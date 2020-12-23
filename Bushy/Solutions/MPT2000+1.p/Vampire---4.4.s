%------------------------------------------------------------------------------
% File       : Vampire---4.4
% Problem    : waybel_7__t49_waybel_7.p : TPTP v0.0.0. Released v0.0.0.
% Transform  : none
% Format     : tptp:raw
% Command    : vampire --mode casc -t %d %s

% Computer   : n007.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 300s
% DateTime   : Fri Oct 11 10:41:07 EDT 2019

% Result     : Theorem 0.18s
% Output     : Refutation 0.18s
% Verified   : 
% Statistics : Number of formulae       :  335 (1157 expanded)
%              Number of leaves         :   88 ( 530 expanded)
%              Depth                    :   11
%              Number of atoms          : 1387 (4522 expanded)
%              Number of equality atoms :   30 (  94 expanded)
%              Maximal formula depth    :   21 (   5 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f1141,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f150,f157,f164,f171,f178,f185,f192,f199,f206,f213,f220,f227,f234,f241,f251,f262,f276,f297,f307,f314,f322,f350,f370,f390,f402,f411,f420,f427,f444,f452,f459,f528,f535,f542,f544,f546,f595,f597,f600,f603,f604,f671,f738,f746,f767,f776,f787,f800,f815,f840,f871,f890,f899,f906,f913,f1053,f1062,f1069,f1080,f1088,f1115,f1122,f1129,f1132])).

fof(f1132,plain,
    ( ~ spl8_0
    | ~ spl8_2
    | ~ spl8_4
    | ~ spl8_6
    | ~ spl8_8
    | ~ spl8_10
    | ~ spl8_12
    | ~ spl8_14
    | ~ spl8_20
    | spl8_23
    | ~ spl8_24
    | ~ spl8_26
    | ~ spl8_92
    | ~ spl8_94
    | spl8_97
    | spl8_99 ),
    inference(avatar_contradiction_clause,[],[f1131])).

fof(f1131,plain,
    ( $false
    | ~ spl8_0
    | ~ spl8_2
    | ~ spl8_4
    | ~ spl8_6
    | ~ spl8_8
    | ~ spl8_10
    | ~ spl8_12
    | ~ spl8_14
    | ~ spl8_20
    | ~ spl8_23
    | ~ spl8_24
    | ~ spl8_26
    | ~ spl8_92
    | ~ spl8_94
    | ~ spl8_97
    | ~ spl8_99 ),
    inference(subsumption_resolution,[],[f1130,f1081])).

fof(f1081,plain,
    ( r1_waybel_3(sK0,k12_lattice3(sK0,sK4(sK0,sK1),sK5(sK0,sK1)),sK1)
    | ~ spl8_0
    | ~ spl8_2
    | ~ spl8_4
    | ~ spl8_6
    | ~ spl8_8
    | ~ spl8_10
    | ~ spl8_12
    | ~ spl8_14
    | ~ spl8_23
    | ~ spl8_24
    | ~ spl8_26 ),
    inference(unit_resulting_resolution,[],[f149,f156,f163,f170,f177,f184,f191,f198,f226,f240,f233,f124])).

fof(f124,plain,(
    ! [X0,X1] :
      ( r1_waybel_3(X0,k12_lattice3(X0,sK4(X0,X1),sK5(X0,X1)),X1)
      | v5_waybel_6(X1,X0)
      | ~ v5_waybel_7(k1_waybel_4(X0),X0)
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | ~ v3_waybel_3(X0)
      | ~ v2_lattice3(X0)
      | ~ v1_lattice3(X0)
      | ~ v1_yellow_0(X0)
      | ~ v5_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v3_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f92])).

fof(f92,plain,(
    ! [X0] :
      ( ! [X1] :
          ( v5_waybel_6(X1,X0)
          | ( ~ r3_orders_2(X0,sK5(X0,X1),X1)
            & ~ r3_orders_2(X0,sK4(X0,X1),X1)
            & r1_waybel_3(X0,k12_lattice3(X0,sK4(X0,X1),sK5(X0,X1)),X1)
            & m1_subset_1(sK5(X0,X1),u1_struct_0(X0))
            & m1_subset_1(sK4(X0,X1),u1_struct_0(X0)) )
          | ~ v5_waybel_7(k1_waybel_4(X0),X0)
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l1_orders_2(X0)
      | ~ v3_waybel_3(X0)
      | ~ v2_lattice3(X0)
      | ~ v1_lattice3(X0)
      | ~ v1_yellow_0(X0)
      | ~ v5_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v3_orders_2(X0) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4,sK5])],[f60,f91,f90])).

fof(f90,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ? [X3] :
              ( ~ r3_orders_2(X0,X3,X1)
              & ~ r3_orders_2(X0,X2,X1)
              & r1_waybel_3(X0,k12_lattice3(X0,X2,X3),X1)
              & m1_subset_1(X3,u1_struct_0(X0)) )
          & m1_subset_1(X2,u1_struct_0(X0)) )
     => ( ? [X3] :
            ( ~ r3_orders_2(X0,X3,X1)
            & ~ r3_orders_2(X0,sK4(X0,X1),X1)
            & r1_waybel_3(X0,k12_lattice3(X0,sK4(X0,X1),X3),X1)
            & m1_subset_1(X3,u1_struct_0(X0)) )
        & m1_subset_1(sK4(X0,X1),u1_struct_0(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f91,plain,(
    ! [X2,X1,X0] :
      ( ? [X3] :
          ( ~ r3_orders_2(X0,X3,X1)
          & ~ r3_orders_2(X0,X2,X1)
          & r1_waybel_3(X0,k12_lattice3(X0,X2,X3),X1)
          & m1_subset_1(X3,u1_struct_0(X0)) )
     => ( ~ r3_orders_2(X0,sK5(X0,X1),X1)
        & ~ r3_orders_2(X0,X2,X1)
        & r1_waybel_3(X0,k12_lattice3(X0,X2,sK5(X0,X1)),X1)
        & m1_subset_1(sK5(X0,X1),u1_struct_0(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f60,plain,(
    ! [X0] :
      ( ! [X1] :
          ( v5_waybel_6(X1,X0)
          | ? [X2] :
              ( ? [X3] :
                  ( ~ r3_orders_2(X0,X3,X1)
                  & ~ r3_orders_2(X0,X2,X1)
                  & r1_waybel_3(X0,k12_lattice3(X0,X2,X3),X1)
                  & m1_subset_1(X3,u1_struct_0(X0)) )
              & m1_subset_1(X2,u1_struct_0(X0)) )
          | ~ v5_waybel_7(k1_waybel_4(X0),X0)
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l1_orders_2(X0)
      | ~ v3_waybel_3(X0)
      | ~ v2_lattice3(X0)
      | ~ v1_lattice3(X0)
      | ~ v1_yellow_0(X0)
      | ~ v5_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v3_orders_2(X0) ) ),
    inference(flattening,[],[f59])).

fof(f59,plain,(
    ! [X0] :
      ( ! [X1] :
          ( v5_waybel_6(X1,X0)
          | ? [X2] :
              ( ? [X3] :
                  ( ~ r3_orders_2(X0,X3,X1)
                  & ~ r3_orders_2(X0,X2,X1)
                  & r1_waybel_3(X0,k12_lattice3(X0,X2,X3),X1)
                  & m1_subset_1(X3,u1_struct_0(X0)) )
              & m1_subset_1(X2,u1_struct_0(X0)) )
          | ~ v5_waybel_7(k1_waybel_4(X0),X0)
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l1_orders_2(X0)
      | ~ v3_waybel_3(X0)
      | ~ v2_lattice3(X0)
      | ~ v1_lattice3(X0)
      | ~ v1_yellow_0(X0)
      | ~ v5_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v3_orders_2(X0) ) ),
    inference(ennf_transformation,[],[f19])).

fof(f19,axiom,(
    ! [X0] :
      ( ( l1_orders_2(X0)
        & v3_waybel_3(X0)
        & v2_lattice3(X0)
        & v1_lattice3(X0)
        & v1_yellow_0(X0)
        & v5_orders_2(X0)
        & v4_orders_2(X0)
        & v3_orders_2(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,u1_struct_0(X0))
         => ~ ( ~ v5_waybel_6(X1,X0)
              & ! [X2] :
                  ( m1_subset_1(X2,u1_struct_0(X0))
                 => ! [X3] :
                      ( m1_subset_1(X3,u1_struct_0(X0))
                     => ~ ( ~ r3_orders_2(X0,X3,X1)
                          & ~ r3_orders_2(X0,X2,X1)
                          & r1_waybel_3(X0,k12_lattice3(X0,X2,X3),X1) ) ) )
              & v5_waybel_7(k1_waybel_4(X0),X0) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/waybel_7__t49_waybel_7.p',l57_waybel_7)).

fof(f233,plain,
    ( v5_waybel_7(k1_waybel_4(sK0),sK0)
    | ~ spl8_24 ),
    inference(avatar_component_clause,[],[f232])).

fof(f232,plain,
    ( spl8_24
  <=> v5_waybel_7(k1_waybel_4(sK0),sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_24])])).

fof(f240,plain,
    ( m1_subset_1(sK1,u1_struct_0(sK0))
    | ~ spl8_26 ),
    inference(avatar_component_clause,[],[f239])).

fof(f239,plain,
    ( spl8_26
  <=> m1_subset_1(sK1,u1_struct_0(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_26])])).

fof(f226,plain,
    ( ~ v5_waybel_6(sK1,sK0)
    | ~ spl8_23 ),
    inference(avatar_component_clause,[],[f225])).

fof(f225,plain,
    ( spl8_23
  <=> ~ v5_waybel_6(sK1,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_23])])).

fof(f198,plain,
    ( l1_orders_2(sK0)
    | ~ spl8_14 ),
    inference(avatar_component_clause,[],[f197])).

fof(f197,plain,
    ( spl8_14
  <=> l1_orders_2(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_14])])).

fof(f191,plain,
    ( v3_waybel_3(sK0)
    | ~ spl8_12 ),
    inference(avatar_component_clause,[],[f190])).

fof(f190,plain,
    ( spl8_12
  <=> v3_waybel_3(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_12])])).

fof(f184,plain,
    ( v2_lattice3(sK0)
    | ~ spl8_10 ),
    inference(avatar_component_clause,[],[f183])).

fof(f183,plain,
    ( spl8_10
  <=> v2_lattice3(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_10])])).

fof(f177,plain,
    ( v1_lattice3(sK0)
    | ~ spl8_8 ),
    inference(avatar_component_clause,[],[f176])).

fof(f176,plain,
    ( spl8_8
  <=> v1_lattice3(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_8])])).

fof(f170,plain,
    ( v1_yellow_0(sK0)
    | ~ spl8_6 ),
    inference(avatar_component_clause,[],[f169])).

fof(f169,plain,
    ( spl8_6
  <=> v1_yellow_0(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_6])])).

fof(f163,plain,
    ( v5_orders_2(sK0)
    | ~ spl8_4 ),
    inference(avatar_component_clause,[],[f162])).

fof(f162,plain,
    ( spl8_4
  <=> v5_orders_2(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_4])])).

fof(f156,plain,
    ( v4_orders_2(sK0)
    | ~ spl8_2 ),
    inference(avatar_component_clause,[],[f155])).

fof(f155,plain,
    ( spl8_2
  <=> v4_orders_2(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_2])])).

fof(f149,plain,
    ( v3_orders_2(sK0)
    | ~ spl8_0 ),
    inference(avatar_component_clause,[],[f148])).

fof(f148,plain,
    ( spl8_0
  <=> v3_orders_2(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_0])])).

fof(f1130,plain,
    ( ~ r1_waybel_3(sK0,k12_lattice3(sK0,sK4(sK0,sK1),sK5(sK0,sK1)),sK1)
    | ~ spl8_0
    | ~ spl8_2
    | ~ spl8_4
    | ~ spl8_6
    | ~ spl8_8
    | ~ spl8_10
    | ~ spl8_12
    | ~ spl8_14
    | ~ spl8_20
    | ~ spl8_24
    | ~ spl8_26
    | ~ spl8_92
    | ~ spl8_94
    | ~ spl8_97
    | ~ spl8_99 ),
    inference(forward_demodulation,[],[f1124,f997])).

fof(f997,plain,
    ( k12_lattice3(sK0,sK4(sK0,sK1),sK5(sK0,sK1)) = k12_lattice3(sK0,sK5(sK0,sK1),sK4(sK0,sK1))
    | ~ spl8_4
    | ~ spl8_10
    | ~ spl8_14
    | ~ spl8_92
    | ~ spl8_94 ),
    inference(unit_resulting_resolution,[],[f163,f184,f198,f898,f905,f137])).

fof(f137,plain,(
    ! [X2,X0,X1] :
      ( ~ v2_lattice3(X0)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | k12_lattice3(X0,X1,X2) = k12_lattice3(X0,X2,X1)
      | ~ v5_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f74])).

fof(f74,plain,(
    ! [X0,X1,X2] :
      ( k12_lattice3(X0,X1,X2) = k12_lattice3(X0,X2,X1)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | ~ v2_lattice3(X0)
      | ~ v5_orders_2(X0) ) ),
    inference(flattening,[],[f73])).

fof(f73,plain,(
    ! [X0,X1,X2] :
      ( k12_lattice3(X0,X1,X2) = k12_lattice3(X0,X2,X1)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | ~ v2_lattice3(X0)
      | ~ v5_orders_2(X0) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,u1_struct_0(X0))
        & m1_subset_1(X1,u1_struct_0(X0))
        & l1_orders_2(X0)
        & v2_lattice3(X0)
        & v5_orders_2(X0) )
     => k12_lattice3(X0,X1,X2) = k12_lattice3(X0,X2,X1) ) ),
    file('/export/starexec/sandbox/benchmark/waybel_7__t49_waybel_7.p',commutativity_k12_lattice3)).

fof(f905,plain,
    ( m1_subset_1(sK5(sK0,sK1),u1_struct_0(sK0))
    | ~ spl8_94 ),
    inference(avatar_component_clause,[],[f904])).

fof(f904,plain,
    ( spl8_94
  <=> m1_subset_1(sK5(sK0,sK1),u1_struct_0(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_94])])).

fof(f898,plain,
    ( m1_subset_1(sK4(sK0,sK1),u1_struct_0(sK0))
    | ~ spl8_92 ),
    inference(avatar_component_clause,[],[f897])).

fof(f897,plain,
    ( spl8_92
  <=> m1_subset_1(sK4(sK0,sK1),u1_struct_0(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_92])])).

fof(f1124,plain,
    ( ~ r1_waybel_3(sK0,k12_lattice3(sK0,sK5(sK0,sK1),sK4(sK0,sK1)),sK1)
    | ~ spl8_0
    | ~ spl8_2
    | ~ spl8_4
    | ~ spl8_6
    | ~ spl8_8
    | ~ spl8_10
    | ~ spl8_12
    | ~ spl8_14
    | ~ spl8_20
    | ~ spl8_24
    | ~ spl8_26
    | ~ spl8_92
    | ~ spl8_94
    | ~ spl8_97
    | ~ spl8_99 ),
    inference(unit_resulting_resolution,[],[f149,f156,f163,f170,f177,f184,f191,f198,f1052,f905,f219,f240,f912,f898,f233,f116])).

fof(f116,plain,(
    ! [X4,X0,X5,X1] :
      ( ~ v5_waybel_7(k1_waybel_4(X0),X0)
      | r3_orders_2(X0,X4,X1)
      | ~ r1_waybel_3(X0,k12_lattice3(X0,X4,X5),X1)
      | ~ m1_subset_1(X5,u1_struct_0(X0))
      | ~ m1_subset_1(X4,u1_struct_0(X0))
      | ~ v4_waybel_7(X1,X0)
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | r3_orders_2(X0,X5,X1)
      | ~ l1_orders_2(X0)
      | ~ v3_waybel_3(X0)
      | ~ v2_lattice3(X0)
      | ~ v1_lattice3(X0)
      | ~ v1_yellow_0(X0)
      | ~ v5_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v3_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f89])).

fof(f89,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ( v4_waybel_7(X1,X0)
              | ( ~ r3_orders_2(X0,sK3(X0,X1),X1)
                & ~ r3_orders_2(X0,sK2(X0,X1),X1)
                & r1_waybel_3(X0,k12_lattice3(X0,sK2(X0,X1),sK3(X0,X1)),X1)
                & m1_subset_1(sK3(X0,X1),u1_struct_0(X0))
                & m1_subset_1(sK2(X0,X1),u1_struct_0(X0)) ) )
            & ( ! [X4] :
                  ( ! [X5] :
                      ( r3_orders_2(X0,X5,X1)
                      | r3_orders_2(X0,X4,X1)
                      | ~ r1_waybel_3(X0,k12_lattice3(X0,X4,X5),X1)
                      | ~ m1_subset_1(X5,u1_struct_0(X0)) )
                  | ~ m1_subset_1(X4,u1_struct_0(X0)) )
              | ~ v4_waybel_7(X1,X0) ) )
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ v5_waybel_7(k1_waybel_4(X0),X0)
      | ~ l1_orders_2(X0)
      | ~ v3_waybel_3(X0)
      | ~ v2_lattice3(X0)
      | ~ v1_lattice3(X0)
      | ~ v1_yellow_0(X0)
      | ~ v5_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v3_orders_2(X0) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2,sK3])],[f86,f88,f87])).

fof(f87,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ? [X3] :
              ( ~ r3_orders_2(X0,X3,X1)
              & ~ r3_orders_2(X0,X2,X1)
              & r1_waybel_3(X0,k12_lattice3(X0,X2,X3),X1)
              & m1_subset_1(X3,u1_struct_0(X0)) )
          & m1_subset_1(X2,u1_struct_0(X0)) )
     => ( ? [X3] :
            ( ~ r3_orders_2(X0,X3,X1)
            & ~ r3_orders_2(X0,sK2(X0,X1),X1)
            & r1_waybel_3(X0,k12_lattice3(X0,sK2(X0,X1),X3),X1)
            & m1_subset_1(X3,u1_struct_0(X0)) )
        & m1_subset_1(sK2(X0,X1),u1_struct_0(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f88,plain,(
    ! [X2,X1,X0] :
      ( ? [X3] :
          ( ~ r3_orders_2(X0,X3,X1)
          & ~ r3_orders_2(X0,X2,X1)
          & r1_waybel_3(X0,k12_lattice3(X0,X2,X3),X1)
          & m1_subset_1(X3,u1_struct_0(X0)) )
     => ( ~ r3_orders_2(X0,sK3(X0,X1),X1)
        & ~ r3_orders_2(X0,X2,X1)
        & r1_waybel_3(X0,k12_lattice3(X0,X2,sK3(X0,X1)),X1)
        & m1_subset_1(sK3(X0,X1),u1_struct_0(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f86,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ( v4_waybel_7(X1,X0)
              | ? [X2] :
                  ( ? [X3] :
                      ( ~ r3_orders_2(X0,X3,X1)
                      & ~ r3_orders_2(X0,X2,X1)
                      & r1_waybel_3(X0,k12_lattice3(X0,X2,X3),X1)
                      & m1_subset_1(X3,u1_struct_0(X0)) )
                  & m1_subset_1(X2,u1_struct_0(X0)) ) )
            & ( ! [X4] :
                  ( ! [X5] :
                      ( r3_orders_2(X0,X5,X1)
                      | r3_orders_2(X0,X4,X1)
                      | ~ r1_waybel_3(X0,k12_lattice3(X0,X4,X5),X1)
                      | ~ m1_subset_1(X5,u1_struct_0(X0)) )
                  | ~ m1_subset_1(X4,u1_struct_0(X0)) )
              | ~ v4_waybel_7(X1,X0) ) )
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ v5_waybel_7(k1_waybel_4(X0),X0)
      | ~ l1_orders_2(X0)
      | ~ v3_waybel_3(X0)
      | ~ v2_lattice3(X0)
      | ~ v1_lattice3(X0)
      | ~ v1_yellow_0(X0)
      | ~ v5_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v3_orders_2(X0) ) ),
    inference(rectify,[],[f85])).

fof(f85,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ( v4_waybel_7(X1,X0)
              | ? [X2] :
                  ( ? [X3] :
                      ( ~ r3_orders_2(X0,X3,X1)
                      & ~ r3_orders_2(X0,X2,X1)
                      & r1_waybel_3(X0,k12_lattice3(X0,X2,X3),X1)
                      & m1_subset_1(X3,u1_struct_0(X0)) )
                  & m1_subset_1(X2,u1_struct_0(X0)) ) )
            & ( ! [X2] :
                  ( ! [X3] :
                      ( r3_orders_2(X0,X3,X1)
                      | r3_orders_2(X0,X2,X1)
                      | ~ r1_waybel_3(X0,k12_lattice3(X0,X2,X3),X1)
                      | ~ m1_subset_1(X3,u1_struct_0(X0)) )
                  | ~ m1_subset_1(X2,u1_struct_0(X0)) )
              | ~ v4_waybel_7(X1,X0) ) )
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ v5_waybel_7(k1_waybel_4(X0),X0)
      | ~ l1_orders_2(X0)
      | ~ v3_waybel_3(X0)
      | ~ v2_lattice3(X0)
      | ~ v1_lattice3(X0)
      | ~ v1_yellow_0(X0)
      | ~ v5_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v3_orders_2(X0) ) ),
    inference(nnf_transformation,[],[f58])).

fof(f58,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( v4_waybel_7(X1,X0)
          <=> ! [X2] :
                ( ! [X3] :
                    ( r3_orders_2(X0,X3,X1)
                    | r3_orders_2(X0,X2,X1)
                    | ~ r1_waybel_3(X0,k12_lattice3(X0,X2,X3),X1)
                    | ~ m1_subset_1(X3,u1_struct_0(X0)) )
                | ~ m1_subset_1(X2,u1_struct_0(X0)) ) )
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ v5_waybel_7(k1_waybel_4(X0),X0)
      | ~ l1_orders_2(X0)
      | ~ v3_waybel_3(X0)
      | ~ v2_lattice3(X0)
      | ~ v1_lattice3(X0)
      | ~ v1_yellow_0(X0)
      | ~ v5_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v3_orders_2(X0) ) ),
    inference(flattening,[],[f57])).

fof(f57,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( v4_waybel_7(X1,X0)
          <=> ! [X2] :
                ( ! [X3] :
                    ( r3_orders_2(X0,X3,X1)
                    | r3_orders_2(X0,X2,X1)
                    | ~ r1_waybel_3(X0,k12_lattice3(X0,X2,X3),X1)
                    | ~ m1_subset_1(X3,u1_struct_0(X0)) )
                | ~ m1_subset_1(X2,u1_struct_0(X0)) ) )
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ v5_waybel_7(k1_waybel_4(X0),X0)
      | ~ l1_orders_2(X0)
      | ~ v3_waybel_3(X0)
      | ~ v2_lattice3(X0)
      | ~ v1_lattice3(X0)
      | ~ v1_yellow_0(X0)
      | ~ v5_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v3_orders_2(X0) ) ),
    inference(ennf_transformation,[],[f26])).

fof(f26,axiom,(
    ! [X0] :
      ( ( l1_orders_2(X0)
        & v3_waybel_3(X0)
        & v2_lattice3(X0)
        & v1_lattice3(X0)
        & v1_yellow_0(X0)
        & v5_orders_2(X0)
        & v4_orders_2(X0)
        & v3_orders_2(X0) )
     => ( v5_waybel_7(k1_waybel_4(X0),X0)
       => ! [X1] :
            ( m1_subset_1(X1,u1_struct_0(X0))
           => ( v4_waybel_7(X1,X0)
            <=> ! [X2] :
                  ( m1_subset_1(X2,u1_struct_0(X0))
                 => ! [X3] :
                      ( m1_subset_1(X3,u1_struct_0(X0))
                     => ~ ( ~ r3_orders_2(X0,X3,X1)
                          & ~ r3_orders_2(X0,X2,X1)
                          & r1_waybel_3(X0,k12_lattice3(X0,X2,X3),X1) ) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/waybel_7__t49_waybel_7.p',t48_waybel_7)).

fof(f912,plain,
    ( ~ r3_orders_2(sK0,sK4(sK0,sK1),sK1)
    | ~ spl8_97 ),
    inference(avatar_component_clause,[],[f911])).

fof(f911,plain,
    ( spl8_97
  <=> ~ r3_orders_2(sK0,sK4(sK0,sK1),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_97])])).

fof(f219,plain,
    ( v4_waybel_7(sK1,sK0)
    | ~ spl8_20 ),
    inference(avatar_component_clause,[],[f218])).

fof(f218,plain,
    ( spl8_20
  <=> v4_waybel_7(sK1,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_20])])).

fof(f1052,plain,
    ( ~ r3_orders_2(sK0,sK5(sK0,sK1),sK1)
    | ~ spl8_99 ),
    inference(avatar_component_clause,[],[f1051])).

fof(f1051,plain,
    ( spl8_99
  <=> ~ r3_orders_2(sK0,sK5(sK0,sK1),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_99])])).

fof(f1129,plain,
    ( ~ spl8_0
    | ~ spl8_2
    | ~ spl8_4
    | ~ spl8_6
    | ~ spl8_8
    | ~ spl8_10
    | ~ spl8_12
    | ~ spl8_14
    | ~ spl8_20
    | spl8_23
    | ~ spl8_24
    | ~ spl8_26
    | ~ spl8_92
    | ~ spl8_94
    | spl8_97
    | spl8_99 ),
    inference(avatar_contradiction_clause,[],[f1128])).

fof(f1128,plain,
    ( $false
    | ~ spl8_0
    | ~ spl8_2
    | ~ spl8_4
    | ~ spl8_6
    | ~ spl8_8
    | ~ spl8_10
    | ~ spl8_12
    | ~ spl8_14
    | ~ spl8_20
    | ~ spl8_23
    | ~ spl8_24
    | ~ spl8_26
    | ~ spl8_92
    | ~ spl8_94
    | ~ spl8_97
    | ~ spl8_99 ),
    inference(subsumption_resolution,[],[f1125,f1081])).

fof(f1125,plain,
    ( ~ r1_waybel_3(sK0,k12_lattice3(sK0,sK4(sK0,sK1),sK5(sK0,sK1)),sK1)
    | ~ spl8_0
    | ~ spl8_2
    | ~ spl8_4
    | ~ spl8_6
    | ~ spl8_8
    | ~ spl8_10
    | ~ spl8_12
    | ~ spl8_14
    | ~ spl8_20
    | ~ spl8_24
    | ~ spl8_26
    | ~ spl8_92
    | ~ spl8_94
    | ~ spl8_97
    | ~ spl8_99 ),
    inference(unit_resulting_resolution,[],[f149,f156,f163,f170,f177,f184,f191,f198,f912,f898,f219,f240,f1052,f905,f233,f116])).

fof(f1122,plain,
    ( ~ spl8_111
    | spl8_47
    | ~ spl8_94 ),
    inference(avatar_split_clause,[],[f978,f904,f368,f1120])).

fof(f1120,plain,
    ( spl8_111
  <=> ~ r2_hidden(u1_struct_0(sK0),sK5(sK0,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_111])])).

fof(f368,plain,
    ( spl8_47
  <=> ~ v1_xboole_0(u1_struct_0(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_47])])).

fof(f978,plain,
    ( ~ r2_hidden(u1_struct_0(sK0),sK5(sK0,sK1))
    | ~ spl8_47
    | ~ spl8_94 ),
    inference(unit_resulting_resolution,[],[f905,f754])).

fof(f754,plain,
    ( ! [X5] :
        ( ~ r2_hidden(u1_struct_0(sK0),X5)
        | ~ m1_subset_1(X5,u1_struct_0(sK0)) )
    | ~ spl8_47 ),
    inference(resolution,[],[f626,f128])).

fof(f128,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X1,X0)
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f61])).

fof(f61,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X1,X0)
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
     => ~ r2_hidden(X1,X0) ) ),
    file('/export/starexec/sandbox/benchmark/waybel_7__t49_waybel_7.p',antisymmetry_r2_hidden)).

fof(f626,plain,
    ( ! [X0] :
        ( r2_hidden(X0,u1_struct_0(sK0))
        | ~ m1_subset_1(X0,u1_struct_0(sK0)) )
    | ~ spl8_47 ),
    inference(resolution,[],[f369,f130])).

fof(f130,plain,(
    ! [X0,X1] :
      ( v1_xboole_0(X1)
      | r2_hidden(X0,X1)
      | ~ m1_subset_1(X0,X1) ) ),
    inference(cnf_transformation,[],[f64])).

fof(f64,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
      | v1_xboole_0(X1)
      | ~ m1_subset_1(X0,X1) ) ),
    inference(flattening,[],[f63])).

fof(f63,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
      | v1_xboole_0(X1)
      | ~ m1_subset_1(X0,X1) ) ),
    inference(ennf_transformation,[],[f24])).

fof(f24,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,X1)
     => ( r2_hidden(X0,X1)
        | v1_xboole_0(X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/waybel_7__t49_waybel_7.p',t2_subset)).

fof(f369,plain,
    ( ~ v1_xboole_0(u1_struct_0(sK0))
    | ~ spl8_47 ),
    inference(avatar_component_clause,[],[f368])).

fof(f1115,plain,
    ( ~ spl8_109
    | spl8_47
    | ~ spl8_92 ),
    inference(avatar_split_clause,[],[f924,f897,f368,f1113])).

fof(f1113,plain,
    ( spl8_109
  <=> ~ r2_hidden(u1_struct_0(sK0),sK4(sK0,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_109])])).

fof(f924,plain,
    ( ~ r2_hidden(u1_struct_0(sK0),sK4(sK0,sK1))
    | ~ spl8_47
    | ~ spl8_92 ),
    inference(unit_resulting_resolution,[],[f898,f754])).

fof(f1088,plain,
    ( spl8_106
    | spl8_47
    | ~ spl8_94 ),
    inference(avatar_split_clause,[],[f1022,f904,f368,f1086])).

fof(f1086,plain,
    ( spl8_106
  <=> r2_hidden(sK5(sK0,sK1),u1_struct_0(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_106])])).

fof(f1022,plain,
    ( r2_hidden(sK5(sK0,sK1),u1_struct_0(sK0))
    | ~ spl8_47
    | ~ spl8_94 ),
    inference(unit_resulting_resolution,[],[f369,f905,f130])).

fof(f1080,plain,
    ( spl8_104
    | spl8_47
    | ~ spl8_92 ),
    inference(avatar_split_clause,[],[f960,f897,f368,f1078])).

fof(f1078,plain,
    ( spl8_104
  <=> r2_hidden(sK4(sK0,sK1),u1_struct_0(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_104])])).

fof(f960,plain,
    ( r2_hidden(sK4(sK0,sK1),u1_struct_0(sK0))
    | ~ spl8_47
    | ~ spl8_92 ),
    inference(unit_resulting_resolution,[],[f369,f898,f130])).

fof(f1069,plain,
    ( ~ spl8_103
    | ~ spl8_0
    | ~ spl8_14
    | ~ spl8_26
    | spl8_31
    | ~ spl8_94
    | spl8_99 ),
    inference(avatar_split_clause,[],[f1054,f1051,f904,f260,f239,f197,f148,f1067])).

fof(f1067,plain,
    ( spl8_103
  <=> ~ r1_orders_2(sK0,sK5(sK0,sK1),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_103])])).

fof(f260,plain,
    ( spl8_31
  <=> ~ v2_struct_0(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_31])])).

fof(f1054,plain,
    ( ~ r1_orders_2(sK0,sK5(sK0,sK1),sK1)
    | ~ spl8_0
    | ~ spl8_14
    | ~ spl8_26
    | ~ spl8_31
    | ~ spl8_94
    | ~ spl8_99 ),
    inference(unit_resulting_resolution,[],[f261,f149,f198,f240,f905,f1052,f135])).

fof(f135,plain,(
    ! [X2,X0,X1] :
      ( r3_orders_2(X0,X1,X2)
      | ~ r1_orders_2(X0,X1,X2)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f95])).

fof(f95,plain,(
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
    inference(nnf_transformation,[],[f70])).

fof(f70,plain,(
    ! [X0,X1,X2] :
      ( ( r3_orders_2(X0,X1,X2)
      <=> r1_orders_2(X0,X1,X2) )
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f69])).

fof(f69,plain,(
    ! [X0,X1,X2] :
      ( ( r3_orders_2(X0,X1,X2)
      <=> r1_orders_2(X0,X1,X2) )
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f21])).

fof(f21,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,u1_struct_0(X0))
        & m1_subset_1(X1,u1_struct_0(X0))
        & l1_orders_2(X0)
        & v3_orders_2(X0)
        & ~ v2_struct_0(X0) )
     => ( r3_orders_2(X0,X1,X2)
      <=> r1_orders_2(X0,X1,X2) ) ) ),
    file('/export/starexec/sandbox/benchmark/waybel_7__t49_waybel_7.p',redefinition_r3_orders_2)).

fof(f261,plain,
    ( ~ v2_struct_0(sK0)
    | ~ spl8_31 ),
    inference(avatar_component_clause,[],[f260])).

fof(f1062,plain,
    ( ~ spl8_101
    | ~ spl8_0
    | ~ spl8_14
    | ~ spl8_26
    | spl8_31
    | ~ spl8_92
    | spl8_97 ),
    inference(avatar_split_clause,[],[f1045,f911,f897,f260,f239,f197,f148,f1060])).

fof(f1060,plain,
    ( spl8_101
  <=> ~ r1_orders_2(sK0,sK4(sK0,sK1),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_101])])).

fof(f1045,plain,
    ( ~ r1_orders_2(sK0,sK4(sK0,sK1),sK1)
    | ~ spl8_0
    | ~ spl8_14
    | ~ spl8_26
    | ~ spl8_31
    | ~ spl8_92
    | ~ spl8_97 ),
    inference(unit_resulting_resolution,[],[f261,f149,f198,f240,f898,f912,f135])).

fof(f1053,plain,
    ( ~ spl8_99
    | ~ spl8_0
    | ~ spl8_2
    | ~ spl8_4
    | ~ spl8_6
    | ~ spl8_8
    | ~ spl8_10
    | ~ spl8_12
    | ~ spl8_14
    | spl8_23
    | ~ spl8_24
    | ~ spl8_26 ),
    inference(avatar_split_clause,[],[f914,f239,f232,f225,f197,f190,f183,f176,f169,f162,f155,f148,f1051])).

fof(f914,plain,
    ( ~ r3_orders_2(sK0,sK5(sK0,sK1),sK1)
    | ~ spl8_0
    | ~ spl8_2
    | ~ spl8_4
    | ~ spl8_6
    | ~ spl8_8
    | ~ spl8_10
    | ~ spl8_12
    | ~ spl8_14
    | ~ spl8_23
    | ~ spl8_24
    | ~ spl8_26 ),
    inference(unit_resulting_resolution,[],[f149,f156,f163,f170,f177,f184,f191,f198,f226,f240,f233,f126])).

fof(f126,plain,(
    ! [X0,X1] :
      ( ~ v5_waybel_7(k1_waybel_4(X0),X0)
      | ~ r3_orders_2(X0,sK5(X0,X1),X1)
      | v5_waybel_6(X1,X0)
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | ~ v3_waybel_3(X0)
      | ~ v2_lattice3(X0)
      | ~ v1_lattice3(X0)
      | ~ v1_yellow_0(X0)
      | ~ v5_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v3_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f92])).

fof(f913,plain,
    ( ~ spl8_97
    | ~ spl8_0
    | ~ spl8_2
    | ~ spl8_4
    | ~ spl8_6
    | ~ spl8_8
    | ~ spl8_10
    | ~ spl8_12
    | ~ spl8_14
    | spl8_23
    | ~ spl8_24
    | ~ spl8_26 ),
    inference(avatar_split_clause,[],[f874,f239,f232,f225,f197,f190,f183,f176,f169,f162,f155,f148,f911])).

fof(f874,plain,
    ( ~ r3_orders_2(sK0,sK4(sK0,sK1),sK1)
    | ~ spl8_0
    | ~ spl8_2
    | ~ spl8_4
    | ~ spl8_6
    | ~ spl8_8
    | ~ spl8_10
    | ~ spl8_12
    | ~ spl8_14
    | ~ spl8_23
    | ~ spl8_24
    | ~ spl8_26 ),
    inference(unit_resulting_resolution,[],[f149,f156,f163,f170,f177,f184,f191,f198,f226,f240,f233,f125])).

fof(f125,plain,(
    ! [X0,X1] :
      ( ~ v5_waybel_7(k1_waybel_4(X0),X0)
      | ~ r3_orders_2(X0,sK4(X0,X1),X1)
      | v5_waybel_6(X1,X0)
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | ~ v3_waybel_3(X0)
      | ~ v2_lattice3(X0)
      | ~ v1_lattice3(X0)
      | ~ v1_yellow_0(X0)
      | ~ v5_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v3_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f92])).

fof(f906,plain,
    ( spl8_94
    | ~ spl8_0
    | ~ spl8_2
    | ~ spl8_4
    | ~ spl8_6
    | ~ spl8_8
    | ~ spl8_10
    | ~ spl8_12
    | ~ spl8_14
    | spl8_23
    | ~ spl8_24
    | ~ spl8_26 ),
    inference(avatar_split_clause,[],[f856,f239,f232,f225,f197,f190,f183,f176,f169,f162,f155,f148,f904])).

fof(f856,plain,
    ( m1_subset_1(sK5(sK0,sK1),u1_struct_0(sK0))
    | ~ spl8_0
    | ~ spl8_2
    | ~ spl8_4
    | ~ spl8_6
    | ~ spl8_8
    | ~ spl8_10
    | ~ spl8_12
    | ~ spl8_14
    | ~ spl8_23
    | ~ spl8_24
    | ~ spl8_26 ),
    inference(unit_resulting_resolution,[],[f149,f156,f163,f170,f177,f184,f191,f198,f226,f240,f233,f123])).

fof(f123,plain,(
    ! [X0,X1] :
      ( m1_subset_1(sK5(X0,X1),u1_struct_0(X0))
      | v5_waybel_6(X1,X0)
      | ~ v5_waybel_7(k1_waybel_4(X0),X0)
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | ~ v3_waybel_3(X0)
      | ~ v2_lattice3(X0)
      | ~ v1_lattice3(X0)
      | ~ v1_yellow_0(X0)
      | ~ v5_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v3_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f92])).

fof(f899,plain,
    ( spl8_92
    | ~ spl8_0
    | ~ spl8_2
    | ~ spl8_4
    | ~ spl8_6
    | ~ spl8_8
    | ~ spl8_10
    | ~ spl8_12
    | ~ spl8_14
    | spl8_23
    | ~ spl8_24
    | ~ spl8_26 ),
    inference(avatar_split_clause,[],[f819,f239,f232,f225,f197,f190,f183,f176,f169,f162,f155,f148,f897])).

fof(f819,plain,
    ( m1_subset_1(sK4(sK0,sK1),u1_struct_0(sK0))
    | ~ spl8_0
    | ~ spl8_2
    | ~ spl8_4
    | ~ spl8_6
    | ~ spl8_8
    | ~ spl8_10
    | ~ spl8_12
    | ~ spl8_14
    | ~ spl8_23
    | ~ spl8_24
    | ~ spl8_26 ),
    inference(unit_resulting_resolution,[],[f149,f156,f163,f170,f177,f184,f191,f198,f226,f240,f233,f122])).

fof(f122,plain,(
    ! [X0,X1] :
      ( m1_subset_1(sK4(X0,X1),u1_struct_0(X0))
      | v5_waybel_6(X1,X0)
      | ~ v5_waybel_7(k1_waybel_4(X0),X0)
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | ~ v3_waybel_3(X0)
      | ~ v2_lattice3(X0)
      | ~ v1_lattice3(X0)
      | ~ v1_yellow_0(X0)
      | ~ v5_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v3_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f92])).

fof(f890,plain,
    ( ~ spl8_91
    | spl8_89 ),
    inference(avatar_split_clause,[],[f873,f869,f888])).

fof(f888,plain,
    ( spl8_91
  <=> ~ r2_hidden(k1_zfmisc_1(o_0_0_xboole_0),k1_zfmisc_1(o_0_0_xboole_0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_91])])).

fof(f869,plain,
    ( spl8_89
  <=> ~ m1_subset_1(k1_zfmisc_1(o_0_0_xboole_0),k1_zfmisc_1(o_0_0_xboole_0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_89])])).

fof(f873,plain,
    ( ~ r2_hidden(k1_zfmisc_1(o_0_0_xboole_0),k1_zfmisc_1(o_0_0_xboole_0))
    | ~ spl8_89 ),
    inference(unit_resulting_resolution,[],[f870,f129])).

fof(f129,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X0,X1)
      | m1_subset_1(X0,X1) ) ),
    inference(cnf_transformation,[],[f62])).

fof(f62,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X0,X1)
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f23])).

fof(f23,axiom,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
     => m1_subset_1(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/waybel_7__t49_waybel_7.p',t1_subset)).

fof(f870,plain,
    ( ~ m1_subset_1(k1_zfmisc_1(o_0_0_xboole_0),k1_zfmisc_1(o_0_0_xboole_0))
    | ~ spl8_89 ),
    inference(avatar_component_clause,[],[f869])).

fof(f871,plain,
    ( ~ spl8_89
    | ~ spl8_16
    | ~ spl8_82 ),
    inference(avatar_split_clause,[],[f846,f798,f204,f869])).

fof(f204,plain,
    ( spl8_16
  <=> v1_xboole_0(o_0_0_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_16])])).

fof(f798,plain,
    ( spl8_82
  <=> r2_hidden(o_0_0_xboole_0,k1_zfmisc_1(o_0_0_xboole_0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_82])])).

fof(f846,plain,
    ( ~ m1_subset_1(k1_zfmisc_1(o_0_0_xboole_0),k1_zfmisc_1(o_0_0_xboole_0))
    | ~ spl8_16
    | ~ spl8_82 ),
    inference(unit_resulting_resolution,[],[f205,f799,f141])).

fof(f141,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(X0,X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ v1_xboole_0(X2) ) ),
    inference(cnf_transformation,[],[f81])).

fof(f81,plain,(
    ! [X0,X1,X2] :
      ( ~ v1_xboole_0(X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f28])).

fof(f28,axiom,(
    ! [X0,X1,X2] :
      ~ ( v1_xboole_0(X2)
        & m1_subset_1(X1,k1_zfmisc_1(X2))
        & r2_hidden(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/waybel_7__t49_waybel_7.p',t5_subset)).

fof(f799,plain,
    ( r2_hidden(o_0_0_xboole_0,k1_zfmisc_1(o_0_0_xboole_0))
    | ~ spl8_82 ),
    inference(avatar_component_clause,[],[f798])).

fof(f205,plain,
    ( v1_xboole_0(o_0_0_xboole_0)
    | ~ spl8_16 ),
    inference(avatar_component_clause,[],[f204])).

fof(f840,plain,
    ( ~ spl8_87
    | ~ spl8_16
    | spl8_81 ),
    inference(avatar_split_clause,[],[f830,f789,f204,f838])).

fof(f838,plain,
    ( spl8_87
  <=> ~ v1_xboole_0(k1_zfmisc_1(o_0_0_xboole_0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_87])])).

fof(f789,plain,
    ( spl8_81
  <=> k1_zfmisc_1(o_0_0_xboole_0) != o_0_0_xboole_0 ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_81])])).

fof(f830,plain,
    ( ~ v1_xboole_0(k1_zfmisc_1(o_0_0_xboole_0))
    | ~ spl8_16
    | ~ spl8_81 ),
    inference(unit_resulting_resolution,[],[f205,f790,f131])).

fof(f131,plain,(
    ! [X0,X1] :
      ( ~ v1_xboole_0(X1)
      | X0 = X1
      | ~ v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f65])).

fof(f65,plain,(
    ! [X0,X1] :
      ( ~ v1_xboole_0(X1)
      | X0 = X1
      | ~ v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f31])).

fof(f31,axiom,(
    ! [X0,X1] :
      ~ ( v1_xboole_0(X1)
        & X0 != X1
        & v1_xboole_0(X0) ) ),
    file('/export/starexec/sandbox/benchmark/waybel_7__t49_waybel_7.p',t8_boole)).

fof(f790,plain,
    ( k1_zfmisc_1(o_0_0_xboole_0) != o_0_0_xboole_0
    | ~ spl8_81 ),
    inference(avatar_component_clause,[],[f789])).

fof(f815,plain,
    ( spl8_84
    | ~ spl8_38
    | ~ spl8_80 ),
    inference(avatar_split_clause,[],[f802,f792,f312,f813])).

fof(f813,plain,
    ( spl8_84
  <=> m1_subset_1(o_0_0_xboole_0,o_0_0_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_84])])).

fof(f312,plain,
    ( spl8_38
  <=> m1_subset_1(o_0_0_xboole_0,k1_zfmisc_1(o_0_0_xboole_0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_38])])).

fof(f792,plain,
    ( spl8_80
  <=> k1_zfmisc_1(o_0_0_xboole_0) = o_0_0_xboole_0 ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_80])])).

fof(f802,plain,
    ( m1_subset_1(o_0_0_xboole_0,o_0_0_xboole_0)
    | ~ spl8_38
    | ~ spl8_80 ),
    inference(backward_demodulation,[],[f793,f313])).

fof(f313,plain,
    ( m1_subset_1(o_0_0_xboole_0,k1_zfmisc_1(o_0_0_xboole_0))
    | ~ spl8_38 ),
    inference(avatar_component_clause,[],[f312])).

fof(f793,plain,
    ( k1_zfmisc_1(o_0_0_xboole_0) = o_0_0_xboole_0
    | ~ spl8_80 ),
    inference(avatar_component_clause,[],[f792])).

fof(f800,plain,
    ( spl8_80
    | spl8_82
    | ~ spl8_16
    | ~ spl8_38 ),
    inference(avatar_split_clause,[],[f326,f312,f204,f798,f792])).

fof(f326,plain,
    ( r2_hidden(o_0_0_xboole_0,k1_zfmisc_1(o_0_0_xboole_0))
    | k1_zfmisc_1(o_0_0_xboole_0) = o_0_0_xboole_0
    | ~ spl8_16
    | ~ spl8_38 ),
    inference(resolution,[],[f267,f313])).

fof(f267,plain,
    ( ! [X4,X3] :
        ( ~ m1_subset_1(X3,X4)
        | r2_hidden(X3,X4)
        | o_0_0_xboole_0 = X4 )
    | ~ spl8_16 ),
    inference(resolution,[],[f130,f244])).

fof(f244,plain,
    ( ! [X0] :
        ( ~ v1_xboole_0(X0)
        | o_0_0_xboole_0 = X0 )
    | ~ spl8_16 ),
    inference(backward_demodulation,[],[f242,f111])).

fof(f111,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(X0)
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f50])).

fof(f50,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | ~ v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f29])).

fof(f29,axiom,(
    ! [X0] :
      ( v1_xboole_0(X0)
     => k1_xboole_0 = X0 ) ),
    file('/export/starexec/sandbox/benchmark/waybel_7__t49_waybel_7.p',t6_boole)).

fof(f242,plain,
    ( o_0_0_xboole_0 = k1_xboole_0
    | ~ spl8_16 ),
    inference(unit_resulting_resolution,[],[f205,f111])).

fof(f787,plain,
    ( ~ spl8_79
    | spl8_75 ),
    inference(avatar_split_clause,[],[f768,f765,f785])).

fof(f785,plain,
    ( spl8_79
  <=> ~ r2_hidden(u1_struct_0(sK0),sK6(k1_zfmisc_1(u1_struct_0(sK0)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_79])])).

fof(f765,plain,
    ( spl8_75
  <=> ~ m1_subset_1(u1_struct_0(sK0),u1_struct_0(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_75])])).

fof(f768,plain,
    ( ~ r2_hidden(u1_struct_0(sK0),sK6(k1_zfmisc_1(u1_struct_0(sK0))))
    | ~ spl8_75 ),
    inference(unit_resulting_resolution,[],[f127,f766,f140])).

fof(f140,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(X0,X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | m1_subset_1(X0,X2) ) ),
    inference(cnf_transformation,[],[f80])).

fof(f80,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X0,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(flattening,[],[f79])).

fof(f79,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X0,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f27])).

fof(f27,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(X2))
        & r2_hidden(X0,X1) )
     => m1_subset_1(X0,X2) ) ),
    file('/export/starexec/sandbox/benchmark/waybel_7__t49_waybel_7.p',t4_subset)).

fof(f766,plain,
    ( ~ m1_subset_1(u1_struct_0(sK0),u1_struct_0(sK0))
    | ~ spl8_75 ),
    inference(avatar_component_clause,[],[f765])).

fof(f127,plain,(
    ! [X0] : m1_subset_1(sK6(X0),X0) ),
    inference(cnf_transformation,[],[f94])).

fof(f94,plain,(
    ! [X0] : m1_subset_1(sK6(X0),X0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK6])],[f18,f93])).

fof(f93,plain,(
    ! [X0] :
      ( ? [X1] : m1_subset_1(X1,X0)
     => m1_subset_1(sK6(X0),X0) ) ),
    introduced(choice_axiom,[])).

fof(f18,axiom,(
    ! [X0] :
    ? [X1] : m1_subset_1(X1,X0) ),
    file('/export/starexec/sandbox/benchmark/waybel_7__t49_waybel_7.p',existence_m1_subset_1)).

fof(f776,plain,
    ( ~ spl8_77
    | spl8_75 ),
    inference(avatar_split_clause,[],[f769,f765,f774])).

fof(f774,plain,
    ( spl8_77
  <=> ~ r2_hidden(u1_struct_0(sK0),u1_struct_0(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_77])])).

fof(f769,plain,
    ( ~ r2_hidden(u1_struct_0(sK0),u1_struct_0(sK0))
    | ~ spl8_75 ),
    inference(unit_resulting_resolution,[],[f766,f129])).

fof(f767,plain,
    ( ~ spl8_75
    | spl8_47 ),
    inference(avatar_split_clause,[],[f760,f368,f765])).

fof(f760,plain,
    ( ~ m1_subset_1(u1_struct_0(sK0),u1_struct_0(sK0))
    | ~ spl8_47 ),
    inference(duplicate_literal_removal,[],[f759])).

fof(f759,plain,
    ( ~ m1_subset_1(u1_struct_0(sK0),u1_struct_0(sK0))
    | ~ m1_subset_1(u1_struct_0(sK0),u1_struct_0(sK0))
    | ~ spl8_47 ),
    inference(resolution,[],[f754,f626])).

fof(f746,plain,
    ( spl8_72
    | ~ spl8_0
    | ~ spl8_14
    | spl8_31
    | ~ spl8_40 ),
    inference(avatar_split_clause,[],[f413,f320,f260,f197,f148,f744])).

fof(f744,plain,
    ( spl8_72
  <=> r1_orders_2(sK0,sK6(u1_struct_0(sK0)),sK6(u1_struct_0(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_72])])).

fof(f320,plain,
    ( spl8_40
  <=> r3_orders_2(sK0,sK6(u1_struct_0(sK0)),sK6(u1_struct_0(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_40])])).

fof(f413,plain,
    ( r1_orders_2(sK0,sK6(u1_struct_0(sK0)),sK6(u1_struct_0(sK0)))
    | ~ spl8_0
    | ~ spl8_14
    | ~ spl8_31
    | ~ spl8_40 ),
    inference(unit_resulting_resolution,[],[f261,f149,f198,f127,f321,f127,f134])).

fof(f134,plain,(
    ! [X2,X0,X1] :
      ( r1_orders_2(X0,X1,X2)
      | ~ r3_orders_2(X0,X1,X2)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f95])).

fof(f321,plain,
    ( r3_orders_2(sK0,sK6(u1_struct_0(sK0)),sK6(u1_struct_0(sK0)))
    | ~ spl8_40 ),
    inference(avatar_component_clause,[],[f320])).

fof(f738,plain,
    ( ~ spl8_71
    | ~ spl8_68 ),
    inference(avatar_split_clause,[],[f725,f540,f736])).

fof(f736,plain,
    ( spl8_71
  <=> ~ r2_hidden(u1_struct_0(sK0),k12_lattice3(sK0,sK1,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_71])])).

fof(f540,plain,
    ( spl8_68
  <=> r2_hidden(k12_lattice3(sK0,sK1,sK1),u1_struct_0(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_68])])).

fof(f725,plain,
    ( ~ r2_hidden(u1_struct_0(sK0),k12_lattice3(sK0,sK1,sK1))
    | ~ spl8_68 ),
    inference(unit_resulting_resolution,[],[f541,f128])).

fof(f541,plain,
    ( r2_hidden(k12_lattice3(sK0,sK1,sK1),u1_struct_0(sK0))
    | ~ spl8_68 ),
    inference(avatar_component_clause,[],[f540])).

fof(f671,plain,
    ( ~ spl8_51
    | ~ spl8_16
    | ~ spl8_56 ),
    inference(avatar_split_clause,[],[f428,f425,f204,f400])).

fof(f400,plain,
    ( spl8_51
  <=> ~ m1_subset_1(u1_struct_0(sK0),k1_zfmisc_1(o_0_0_xboole_0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_51])])).

fof(f425,plain,
    ( spl8_56
  <=> r2_hidden(sK6(u1_struct_0(sK0)),u1_struct_0(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_56])])).

fof(f428,plain,
    ( ~ m1_subset_1(u1_struct_0(sK0),k1_zfmisc_1(o_0_0_xboole_0))
    | ~ spl8_16
    | ~ spl8_56 ),
    inference(unit_resulting_resolution,[],[f205,f426,f141])).

fof(f426,plain,
    ( r2_hidden(sK6(u1_struct_0(sK0)),u1_struct_0(sK0))
    | ~ spl8_56 ),
    inference(avatar_component_clause,[],[f425])).

fof(f604,plain,
    ( ~ spl8_47
    | ~ spl8_56 ),
    inference(avatar_split_clause,[],[f437,f425,f368])).

fof(f437,plain,
    ( ~ v1_xboole_0(u1_struct_0(sK0))
    | ~ spl8_56 ),
    inference(resolution,[],[f426,f132])).

fof(f132,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X0,X1)
      | ~ v1_xboole_0(X1) ) ),
    inference(cnf_transformation,[],[f66])).

fof(f66,plain,(
    ! [X0,X1] :
      ( ~ v1_xboole_0(X1)
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f30])).

fof(f30,axiom,(
    ! [X0,X1] :
      ~ ( v1_xboole_0(X1)
        & r2_hidden(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/waybel_7__t49_waybel_7.p',t7_boole)).

fof(f603,plain,
    ( ~ spl8_16
    | ~ spl8_42
    | ~ spl8_66 ),
    inference(avatar_contradiction_clause,[],[f602])).

fof(f602,plain,
    ( $false
    | ~ spl8_16
    | ~ spl8_42
    | ~ spl8_66 ),
    inference(subsumption_resolution,[],[f592,f252])).

fof(f252,plain,
    ( ! [X0] : ~ r2_hidden(X0,o_0_0_xboole_0)
    | ~ spl8_16 ),
    inference(unit_resulting_resolution,[],[f205,f132])).

fof(f592,plain,
    ( r2_hidden(k11_lattice3(sK0,sK1,sK1),o_0_0_xboole_0)
    | ~ spl8_42
    | ~ spl8_66 ),
    inference(backward_demodulation,[],[f343,f534])).

fof(f534,plain,
    ( r2_hidden(k11_lattice3(sK0,sK1,sK1),u1_struct_0(sK0))
    | ~ spl8_66 ),
    inference(avatar_component_clause,[],[f533])).

fof(f533,plain,
    ( spl8_66
  <=> r2_hidden(k11_lattice3(sK0,sK1,sK1),u1_struct_0(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_66])])).

fof(f343,plain,
    ( u1_struct_0(sK0) = o_0_0_xboole_0
    | ~ spl8_42 ),
    inference(avatar_component_clause,[],[f342])).

fof(f342,plain,
    ( spl8_42
  <=> u1_struct_0(sK0) = o_0_0_xboole_0 ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_42])])).

fof(f600,plain,
    ( ~ spl8_16
    | ~ spl8_42
    | ~ spl8_56 ),
    inference(avatar_contradiction_clause,[],[f599])).

fof(f599,plain,
    ( $false
    | ~ spl8_16
    | ~ spl8_42
    | ~ spl8_56 ),
    inference(subsumption_resolution,[],[f563,f205])).

fof(f563,plain,
    ( ~ v1_xboole_0(o_0_0_xboole_0)
    | ~ spl8_42
    | ~ spl8_56 ),
    inference(backward_demodulation,[],[f343,f437])).

fof(f597,plain,
    ( ~ spl8_16
    | ~ spl8_38
    | ~ spl8_42
    | ~ spl8_56 ),
    inference(avatar_contradiction_clause,[],[f596])).

fof(f596,plain,
    ( $false
    | ~ spl8_16
    | ~ spl8_38
    | ~ spl8_42
    | ~ spl8_56 ),
    inference(subsumption_resolution,[],[f560,f313])).

fof(f560,plain,
    ( ~ m1_subset_1(o_0_0_xboole_0,k1_zfmisc_1(o_0_0_xboole_0))
    | ~ spl8_16
    | ~ spl8_42
    | ~ spl8_56 ),
    inference(backward_demodulation,[],[f343,f428])).

fof(f595,plain,
    ( ~ spl8_16
    | ~ spl8_42
    | ~ spl8_56 ),
    inference(avatar_contradiction_clause,[],[f594])).

fof(f594,plain,
    ( $false
    | ~ spl8_16
    | ~ spl8_42
    | ~ spl8_56 ),
    inference(subsumption_resolution,[],[f559,f252])).

fof(f559,plain,
    ( r2_hidden(sK6(o_0_0_xboole_0),o_0_0_xboole_0)
    | ~ spl8_42
    | ~ spl8_56 ),
    inference(backward_demodulation,[],[f343,f426])).

fof(f546,plain,
    ( ~ spl8_46
    | ~ spl8_56 ),
    inference(avatar_contradiction_clause,[],[f545])).

fof(f545,plain,
    ( $false
    | ~ spl8_46
    | ~ spl8_56 ),
    inference(subsumption_resolution,[],[f366,f437])).

fof(f366,plain,
    ( v1_xboole_0(u1_struct_0(sK0))
    | ~ spl8_46 ),
    inference(avatar_component_clause,[],[f365])).

fof(f365,plain,
    ( spl8_46
  <=> v1_xboole_0(u1_struct_0(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_46])])).

fof(f544,plain,
    ( ~ spl8_16
    | ~ spl8_50
    | ~ spl8_56 ),
    inference(avatar_contradiction_clause,[],[f543])).

fof(f543,plain,
    ( $false
    | ~ spl8_16
    | ~ spl8_50
    | ~ spl8_56 ),
    inference(subsumption_resolution,[],[f398,f428])).

fof(f398,plain,
    ( m1_subset_1(u1_struct_0(sK0),k1_zfmisc_1(o_0_0_xboole_0))
    | ~ spl8_50 ),
    inference(avatar_component_clause,[],[f397])).

fof(f397,plain,
    ( spl8_50
  <=> m1_subset_1(u1_struct_0(sK0),k1_zfmisc_1(o_0_0_xboole_0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_50])])).

fof(f542,plain,
    ( spl8_68
    | spl8_47
    | ~ spl8_62 ),
    inference(avatar_split_clause,[],[f494,f457,f368,f540])).

fof(f457,plain,
    ( spl8_62
  <=> m1_subset_1(k12_lattice3(sK0,sK1,sK1),u1_struct_0(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_62])])).

fof(f494,plain,
    ( r2_hidden(k12_lattice3(sK0,sK1,sK1),u1_struct_0(sK0))
    | ~ spl8_47
    | ~ spl8_62 ),
    inference(unit_resulting_resolution,[],[f369,f458,f130])).

fof(f458,plain,
    ( m1_subset_1(k12_lattice3(sK0,sK1,sK1),u1_struct_0(sK0))
    | ~ spl8_62 ),
    inference(avatar_component_clause,[],[f457])).

fof(f535,plain,
    ( spl8_66
    | spl8_47
    | ~ spl8_60 ),
    inference(avatar_split_clause,[],[f474,f450,f368,f533])).

fof(f450,plain,
    ( spl8_60
  <=> m1_subset_1(k11_lattice3(sK0,sK1,sK1),u1_struct_0(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_60])])).

fof(f474,plain,
    ( r2_hidden(k11_lattice3(sK0,sK1,sK1),u1_struct_0(sK0))
    | ~ spl8_47
    | ~ spl8_60 ),
    inference(unit_resulting_resolution,[],[f369,f451,f130])).

fof(f451,plain,
    ( m1_subset_1(k11_lattice3(sK0,sK1,sK1),u1_struct_0(sK0))
    | ~ spl8_60 ),
    inference(avatar_component_clause,[],[f450])).

fof(f528,plain,
    ( ~ spl8_65
    | spl8_51 ),
    inference(avatar_split_clause,[],[f403,f400,f526])).

fof(f526,plain,
    ( spl8_65
  <=> ~ r2_hidden(u1_struct_0(sK0),sK6(k1_zfmisc_1(k1_zfmisc_1(o_0_0_xboole_0)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_65])])).

fof(f403,plain,
    ( ~ r2_hidden(u1_struct_0(sK0),sK6(k1_zfmisc_1(k1_zfmisc_1(o_0_0_xboole_0))))
    | ~ spl8_51 ),
    inference(unit_resulting_resolution,[],[f127,f401,f140])).

fof(f401,plain,
    ( ~ m1_subset_1(u1_struct_0(sK0),k1_zfmisc_1(o_0_0_xboole_0))
    | ~ spl8_51 ),
    inference(avatar_component_clause,[],[f400])).

fof(f459,plain,
    ( spl8_62
    | ~ spl8_4
    | ~ spl8_10
    | ~ spl8_14
    | ~ spl8_26 ),
    inference(avatar_split_clause,[],[f391,f239,f197,f183,f162,f457])).

fof(f391,plain,
    ( m1_subset_1(k12_lattice3(sK0,sK1,sK1),u1_struct_0(sK0))
    | ~ spl8_4
    | ~ spl8_10
    | ~ spl8_14
    | ~ spl8_26 ),
    inference(unit_resulting_resolution,[],[f163,f184,f198,f240,f240,f136])).

fof(f136,plain,(
    ! [X2,X0,X1] :
      ( m1_subset_1(k12_lattice3(X0,X1,X2),u1_struct_0(X0))
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | ~ v2_lattice3(X0)
      | ~ v5_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f72])).

fof(f72,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(k12_lattice3(X0,X1,X2),u1_struct_0(X0))
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | ~ v2_lattice3(X0)
      | ~ v5_orders_2(X0) ) ),
    inference(flattening,[],[f71])).

fof(f71,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(k12_lattice3(X0,X1,X2),u1_struct_0(X0))
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | ~ v2_lattice3(X0)
      | ~ v5_orders_2(X0) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,u1_struct_0(X0))
        & m1_subset_1(X1,u1_struct_0(X0))
        & l1_orders_2(X0)
        & v2_lattice3(X0)
        & v5_orders_2(X0) )
     => m1_subset_1(k12_lattice3(X0,X1,X2),u1_struct_0(X0)) ) ),
    file('/export/starexec/sandbox/benchmark/waybel_7__t49_waybel_7.p',dt_k12_lattice3)).

fof(f452,plain,
    ( spl8_60
    | ~ spl8_14
    | ~ spl8_26 ),
    inference(avatar_split_clause,[],[f351,f239,f197,f450])).

fof(f351,plain,
    ( m1_subset_1(k11_lattice3(sK0,sK1,sK1),u1_struct_0(sK0))
    | ~ spl8_14
    | ~ spl8_26 ),
    inference(unit_resulting_resolution,[],[f198,f240,f240,f139])).

fof(f139,plain,(
    ! [X2,X0,X1] :
      ( m1_subset_1(k11_lattice3(X0,X1,X2),u1_struct_0(X0))
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f78])).

fof(f78,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(k11_lattice3(X0,X1,X2),u1_struct_0(X0))
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0) ) ),
    inference(flattening,[],[f77])).

fof(f77,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(k11_lattice3(X0,X1,X2),u1_struct_0(X0))
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,u1_struct_0(X0))
        & m1_subset_1(X1,u1_struct_0(X0))
        & l1_orders_2(X0) )
     => m1_subset_1(k11_lattice3(X0,X1,X2),u1_struct_0(X0)) ) ),
    file('/export/starexec/sandbox/benchmark/waybel_7__t49_waybel_7.p',dt_k11_lattice3)).

fof(f444,plain,
    ( ~ spl8_59
    | ~ spl8_16
    | spl8_43 ),
    inference(avatar_split_clause,[],[f358,f339,f204,f442])).

fof(f442,plain,
    ( spl8_59
  <=> ~ r2_hidden(u1_struct_0(sK0),sK6(u1_struct_0(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_59])])).

fof(f339,plain,
    ( spl8_43
  <=> u1_struct_0(sK0) != o_0_0_xboole_0 ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_43])])).

fof(f358,plain,
    ( ~ r2_hidden(u1_struct_0(sK0),sK6(u1_struct_0(sK0)))
    | ~ spl8_16
    | ~ spl8_43 ),
    inference(unit_resulting_resolution,[],[f340,f333])).

fof(f333,plain,
    ( ! [X5] :
        ( ~ r2_hidden(X5,sK6(X5))
        | o_0_0_xboole_0 = X5 )
    | ~ spl8_16 ),
    inference(resolution,[],[f328,f128])).

fof(f328,plain,
    ( ! [X1] :
        ( r2_hidden(sK6(X1),X1)
        | o_0_0_xboole_0 = X1 )
    | ~ spl8_16 ),
    inference(resolution,[],[f267,f127])).

fof(f340,plain,
    ( u1_struct_0(sK0) != o_0_0_xboole_0
    | ~ spl8_43 ),
    inference(avatar_component_clause,[],[f339])).

fof(f427,plain,
    ( spl8_56
    | ~ spl8_16
    | spl8_43 ),
    inference(avatar_split_clause,[],[f361,f339,f204,f425])).

fof(f361,plain,
    ( r2_hidden(sK6(u1_struct_0(sK0)),u1_struct_0(sK0))
    | ~ spl8_16
    | ~ spl8_43 ),
    inference(unit_resulting_resolution,[],[f127,f340,f267])).

fof(f420,plain,
    ( spl8_54
    | ~ spl8_0
    | ~ spl8_14
    | ~ spl8_26
    | spl8_31
    | ~ spl8_36 ),
    inference(avatar_split_clause,[],[f412,f305,f260,f239,f197,f148,f418])).

fof(f418,plain,
    ( spl8_54
  <=> r1_orders_2(sK0,sK1,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_54])])).

fof(f305,plain,
    ( spl8_36
  <=> r3_orders_2(sK0,sK1,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_36])])).

fof(f412,plain,
    ( r1_orders_2(sK0,sK1,sK1)
    | ~ spl8_0
    | ~ spl8_14
    | ~ spl8_26
    | ~ spl8_31
    | ~ spl8_36 ),
    inference(unit_resulting_resolution,[],[f261,f149,f198,f240,f306,f240,f134])).

fof(f306,plain,
    ( r3_orders_2(sK0,sK1,sK1)
    | ~ spl8_36 ),
    inference(avatar_component_clause,[],[f305])).

fof(f411,plain,
    ( ~ spl8_53
    | spl8_51 ),
    inference(avatar_split_clause,[],[f404,f400,f409])).

fof(f409,plain,
    ( spl8_53
  <=> ~ r2_hidden(u1_struct_0(sK0),k1_zfmisc_1(o_0_0_xboole_0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_53])])).

fof(f404,plain,
    ( ~ r2_hidden(u1_struct_0(sK0),k1_zfmisc_1(o_0_0_xboole_0))
    | ~ spl8_51 ),
    inference(unit_resulting_resolution,[],[f401,f129])).

fof(f402,plain,
    ( ~ spl8_51
    | ~ spl8_16
    | ~ spl8_44 ),
    inference(avatar_split_clause,[],[f374,f348,f204,f400])).

fof(f348,plain,
    ( spl8_44
  <=> r2_hidden(sK1,u1_struct_0(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_44])])).

fof(f374,plain,
    ( ~ m1_subset_1(u1_struct_0(sK0),k1_zfmisc_1(o_0_0_xboole_0))
    | ~ spl8_16
    | ~ spl8_44 ),
    inference(unit_resulting_resolution,[],[f205,f349,f141])).

fof(f349,plain,
    ( r2_hidden(sK1,u1_struct_0(sK0))
    | ~ spl8_44 ),
    inference(avatar_component_clause,[],[f348])).

fof(f390,plain,
    ( ~ spl8_49
    | ~ spl8_44 ),
    inference(avatar_split_clause,[],[f377,f348,f388])).

fof(f388,plain,
    ( spl8_49
  <=> ~ r2_hidden(u1_struct_0(sK0),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_49])])).

fof(f377,plain,
    ( ~ r2_hidden(u1_struct_0(sK0),sK1)
    | ~ spl8_44 ),
    inference(unit_resulting_resolution,[],[f349,f128])).

fof(f370,plain,
    ( ~ spl8_47
    | ~ spl8_16
    | spl8_43 ),
    inference(avatar_split_clause,[],[f363,f339,f204,f368])).

fof(f363,plain,
    ( ~ v1_xboole_0(u1_struct_0(sK0))
    | ~ spl8_16
    | ~ spl8_43 ),
    inference(unit_resulting_resolution,[],[f205,f340,f131])).

fof(f350,plain,
    ( spl8_42
    | spl8_44
    | ~ spl8_16
    | ~ spl8_26 ),
    inference(avatar_split_clause,[],[f327,f239,f204,f348,f342])).

fof(f327,plain,
    ( r2_hidden(sK1,u1_struct_0(sK0))
    | u1_struct_0(sK0) = o_0_0_xboole_0
    | ~ spl8_16
    | ~ spl8_26 ),
    inference(resolution,[],[f267,f240])).

fof(f322,plain,
    ( spl8_40
    | ~ spl8_0
    | ~ spl8_14
    | spl8_31 ),
    inference(avatar_split_clause,[],[f300,f260,f197,f148,f320])).

fof(f300,plain,
    ( r3_orders_2(sK0,sK6(u1_struct_0(sK0)),sK6(u1_struct_0(sK0)))
    | ~ spl8_0
    | ~ spl8_14
    | ~ spl8_31 ),
    inference(unit_resulting_resolution,[],[f261,f149,f198,f127,f143])).

fof(f143,plain,(
    ! [X0,X1] :
      ( r3_orders_2(X1,X0,X0)
      | ~ m1_subset_1(X0,u1_struct_0(X1))
      | ~ l1_orders_2(X1)
      | ~ v3_orders_2(X1)
      | v2_struct_0(X1) ) ),
    inference(condensation,[],[f133])).

fof(f133,plain,(
    ! [X2,X0,X1] :
      ( r3_orders_2(X0,X1,X1)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f68])).

fof(f68,plain,(
    ! [X0,X1,X2] :
      ( r3_orders_2(X0,X1,X1)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f67])).

fof(f67,plain,(
    ! [X0,X1,X2] :
      ( r3_orders_2(X0,X1,X1)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f22])).

fof(f22,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,u1_struct_0(X0))
        & m1_subset_1(X1,u1_struct_0(X0))
        & l1_orders_2(X0)
        & v3_orders_2(X0)
        & ~ v2_struct_0(X0) )
     => r3_orders_2(X0,X1,X1) ) ),
    file('/export/starexec/sandbox/benchmark/waybel_7__t49_waybel_7.p',reflexivity_r3_orders_2)).

fof(f314,plain,
    ( spl8_38
    | ~ spl8_34 ),
    inference(avatar_split_clause,[],[f298,f295,f312])).

fof(f295,plain,
    ( spl8_34
  <=> o_0_0_xboole_0 = sK6(k1_zfmisc_1(o_0_0_xboole_0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_34])])).

fof(f298,plain,
    ( m1_subset_1(o_0_0_xboole_0,k1_zfmisc_1(o_0_0_xboole_0))
    | ~ spl8_34 ),
    inference(superposition,[],[f127,f296])).

fof(f296,plain,
    ( o_0_0_xboole_0 = sK6(k1_zfmisc_1(o_0_0_xboole_0))
    | ~ spl8_34 ),
    inference(avatar_component_clause,[],[f295])).

fof(f307,plain,
    ( spl8_36
    | ~ spl8_0
    | ~ spl8_14
    | ~ spl8_26
    | spl8_31 ),
    inference(avatar_split_clause,[],[f299,f260,f239,f197,f148,f305])).

fof(f299,plain,
    ( r3_orders_2(sK0,sK1,sK1)
    | ~ spl8_0
    | ~ spl8_14
    | ~ spl8_26
    | ~ spl8_31 ),
    inference(unit_resulting_resolution,[],[f261,f149,f198,f240,f143])).

fof(f297,plain,
    ( spl8_34
    | ~ spl8_16
    | ~ spl8_32 ),
    inference(avatar_split_clause,[],[f282,f274,f204,f295])).

fof(f274,plain,
    ( spl8_32
  <=> v1_xboole_0(sK6(k1_zfmisc_1(o_0_0_xboole_0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_32])])).

fof(f282,plain,
    ( o_0_0_xboole_0 = sK6(k1_zfmisc_1(o_0_0_xboole_0))
    | ~ spl8_16
    | ~ spl8_32 ),
    inference(unit_resulting_resolution,[],[f275,f244])).

fof(f275,plain,
    ( v1_xboole_0(sK6(k1_zfmisc_1(o_0_0_xboole_0)))
    | ~ spl8_32 ),
    inference(avatar_component_clause,[],[f274])).

fof(f276,plain,
    ( spl8_32
    | ~ spl8_16 ),
    inference(avatar_split_clause,[],[f269,f204,f274])).

fof(f269,plain,
    ( v1_xboole_0(sK6(k1_zfmisc_1(o_0_0_xboole_0)))
    | ~ spl8_16 ),
    inference(unit_resulting_resolution,[],[f127,f268,f130])).

fof(f268,plain,
    ( ! [X0] : ~ r2_hidden(X0,sK6(k1_zfmisc_1(o_0_0_xboole_0)))
    | ~ spl8_16 ),
    inference(unit_resulting_resolution,[],[f205,f127,f141])).

fof(f262,plain,
    ( ~ spl8_31
    | ~ spl8_10
    | ~ spl8_14 ),
    inference(avatar_split_clause,[],[f255,f197,f183,f260])).

fof(f255,plain,
    ( ~ v2_struct_0(sK0)
    | ~ spl8_10
    | ~ spl8_14 ),
    inference(unit_resulting_resolution,[],[f198,f184,f112])).

fof(f112,plain,(
    ! [X0] :
      ( ~ v2_struct_0(X0)
      | ~ v2_lattice3(X0)
      | ~ l1_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f52])).

fof(f52,plain,(
    ! [X0] :
      ( ~ v2_struct_0(X0)
      | ~ v2_lattice3(X0)
      | ~ l1_orders_2(X0) ) ),
    inference(flattening,[],[f51])).

fof(f51,plain,(
    ! [X0] :
      ( ~ v2_struct_0(X0)
      | ~ v2_lattice3(X0)
      | ~ l1_orders_2(X0) ) ),
    inference(ennf_transformation,[],[f32])).

fof(f32,axiom,(
    ! [X0] :
      ( l1_orders_2(X0)
     => ( v2_lattice3(X0)
       => ~ v2_struct_0(X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/waybel_7__t49_waybel_7.p',cc2_lattice3)).

fof(f251,plain,
    ( spl8_28
    | ~ spl8_16 ),
    inference(avatar_split_clause,[],[f242,f204,f249])).

fof(f249,plain,
    ( spl8_28
  <=> o_0_0_xboole_0 = k1_xboole_0 ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_28])])).

fof(f241,plain,(
    spl8_26 ),
    inference(avatar_split_clause,[],[f107,f239])).

fof(f107,plain,(
    m1_subset_1(sK1,u1_struct_0(sK0)) ),
    inference(cnf_transformation,[],[f84])).

fof(f84,plain,
    ( ~ v5_waybel_6(sK1,sK0)
    & v4_waybel_7(sK1,sK0)
    & m1_subset_1(sK1,u1_struct_0(sK0))
    & v5_waybel_7(k1_waybel_4(sK0),sK0)
    & l1_orders_2(sK0)
    & v3_waybel_3(sK0)
    & v2_lattice3(sK0)
    & v1_lattice3(sK0)
    & v1_yellow_0(sK0)
    & v5_orders_2(sK0)
    & v4_orders_2(sK0)
    & v3_orders_2(sK0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f49,f83,f82])).

fof(f82,plain,
    ( ? [X0] :
        ( ? [X1] :
            ( ~ v5_waybel_6(X1,X0)
            & v4_waybel_7(X1,X0)
            & m1_subset_1(X1,u1_struct_0(X0)) )
        & v5_waybel_7(k1_waybel_4(X0),X0)
        & l1_orders_2(X0)
        & v3_waybel_3(X0)
        & v2_lattice3(X0)
        & v1_lattice3(X0)
        & v1_yellow_0(X0)
        & v5_orders_2(X0)
        & v4_orders_2(X0)
        & v3_orders_2(X0) )
   => ( ? [X1] :
          ( ~ v5_waybel_6(X1,sK0)
          & v4_waybel_7(X1,sK0)
          & m1_subset_1(X1,u1_struct_0(sK0)) )
      & v5_waybel_7(k1_waybel_4(sK0),sK0)
      & l1_orders_2(sK0)
      & v3_waybel_3(sK0)
      & v2_lattice3(sK0)
      & v1_lattice3(sK0)
      & v1_yellow_0(sK0)
      & v5_orders_2(sK0)
      & v4_orders_2(sK0)
      & v3_orders_2(sK0) ) ),
    introduced(choice_axiom,[])).

fof(f83,plain,(
    ! [X0] :
      ( ? [X1] :
          ( ~ v5_waybel_6(X1,X0)
          & v4_waybel_7(X1,X0)
          & m1_subset_1(X1,u1_struct_0(X0)) )
     => ( ~ v5_waybel_6(sK1,X0)
        & v4_waybel_7(sK1,X0)
        & m1_subset_1(sK1,u1_struct_0(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f49,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ~ v5_waybel_6(X1,X0)
          & v4_waybel_7(X1,X0)
          & m1_subset_1(X1,u1_struct_0(X0)) )
      & v5_waybel_7(k1_waybel_4(X0),X0)
      & l1_orders_2(X0)
      & v3_waybel_3(X0)
      & v2_lattice3(X0)
      & v1_lattice3(X0)
      & v1_yellow_0(X0)
      & v5_orders_2(X0)
      & v4_orders_2(X0)
      & v3_orders_2(X0) ) ),
    inference(flattening,[],[f48])).

fof(f48,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ~ v5_waybel_6(X1,X0)
          & v4_waybel_7(X1,X0)
          & m1_subset_1(X1,u1_struct_0(X0)) )
      & v5_waybel_7(k1_waybel_4(X0),X0)
      & l1_orders_2(X0)
      & v3_waybel_3(X0)
      & v2_lattice3(X0)
      & v1_lattice3(X0)
      & v1_yellow_0(X0)
      & v5_orders_2(X0)
      & v4_orders_2(X0)
      & v3_orders_2(X0) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,negated_conjecture,(
    ~ ! [X0] :
        ( ( l1_orders_2(X0)
          & v3_waybel_3(X0)
          & v2_lattice3(X0)
          & v1_lattice3(X0)
          & v1_yellow_0(X0)
          & v5_orders_2(X0)
          & v4_orders_2(X0)
          & v3_orders_2(X0) )
       => ( v5_waybel_7(k1_waybel_4(X0),X0)
         => ! [X1] :
              ( m1_subset_1(X1,u1_struct_0(X0))
             => ( v4_waybel_7(X1,X0)
               => v5_waybel_6(X1,X0) ) ) ) ) ),
    inference(negated_conjecture,[],[f1])).

fof(f1,conjecture,(
    ! [X0] :
      ( ( l1_orders_2(X0)
        & v3_waybel_3(X0)
        & v2_lattice3(X0)
        & v1_lattice3(X0)
        & v1_yellow_0(X0)
        & v5_orders_2(X0)
        & v4_orders_2(X0)
        & v3_orders_2(X0) )
     => ( v5_waybel_7(k1_waybel_4(X0),X0)
       => ! [X1] :
            ( m1_subset_1(X1,u1_struct_0(X0))
           => ( v4_waybel_7(X1,X0)
             => v5_waybel_6(X1,X0) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/waybel_7__t49_waybel_7.p',t49_waybel_7)).

fof(f234,plain,(
    spl8_24 ),
    inference(avatar_split_clause,[],[f106,f232])).

fof(f106,plain,(
    v5_waybel_7(k1_waybel_4(sK0),sK0) ),
    inference(cnf_transformation,[],[f84])).

fof(f227,plain,(
    ~ spl8_23 ),
    inference(avatar_split_clause,[],[f109,f225])).

fof(f109,plain,(
    ~ v5_waybel_6(sK1,sK0) ),
    inference(cnf_transformation,[],[f84])).

fof(f220,plain,(
    spl8_20 ),
    inference(avatar_split_clause,[],[f108,f218])).

fof(f108,plain,(
    v4_waybel_7(sK1,sK0) ),
    inference(cnf_transformation,[],[f84])).

fof(f213,plain,(
    spl8_18 ),
    inference(avatar_split_clause,[],[f142,f211])).

fof(f211,plain,
    ( spl8_18
  <=> l1_orders_2(sK7) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_18])])).

fof(f142,plain,(
    l1_orders_2(sK7) ),
    inference(cnf_transformation,[],[f97])).

fof(f97,plain,(
    l1_orders_2(sK7) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK7])],[f16,f96])).

fof(f96,plain,
    ( ? [X0] : l1_orders_2(X0)
   => l1_orders_2(sK7) ),
    introduced(choice_axiom,[])).

fof(f16,axiom,(
    ? [X0] : l1_orders_2(X0) ),
    file('/export/starexec/sandbox/benchmark/waybel_7__t49_waybel_7.p',existence_l1_orders_2)).

fof(f206,plain,(
    spl8_16 ),
    inference(avatar_split_clause,[],[f110,f204])).

fof(f110,plain,(
    v1_xboole_0(o_0_0_xboole_0) ),
    inference(cnf_transformation,[],[f14])).

fof(f14,axiom,(
    v1_xboole_0(o_0_0_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/waybel_7__t49_waybel_7.p',dt_o_0_0_xboole_0)).

fof(f199,plain,(
    spl8_14 ),
    inference(avatar_split_clause,[],[f105,f197])).

fof(f105,plain,(
    l1_orders_2(sK0) ),
    inference(cnf_transformation,[],[f84])).

fof(f192,plain,(
    spl8_12 ),
    inference(avatar_split_clause,[],[f104,f190])).

fof(f104,plain,(
    v3_waybel_3(sK0) ),
    inference(cnf_transformation,[],[f84])).

fof(f185,plain,(
    spl8_10 ),
    inference(avatar_split_clause,[],[f103,f183])).

fof(f103,plain,(
    v2_lattice3(sK0) ),
    inference(cnf_transformation,[],[f84])).

fof(f178,plain,(
    spl8_8 ),
    inference(avatar_split_clause,[],[f102,f176])).

fof(f102,plain,(
    v1_lattice3(sK0) ),
    inference(cnf_transformation,[],[f84])).

fof(f171,plain,(
    spl8_6 ),
    inference(avatar_split_clause,[],[f101,f169])).

fof(f101,plain,(
    v1_yellow_0(sK0) ),
    inference(cnf_transformation,[],[f84])).

fof(f164,plain,(
    spl8_4 ),
    inference(avatar_split_clause,[],[f100,f162])).

fof(f100,plain,(
    v5_orders_2(sK0) ),
    inference(cnf_transformation,[],[f84])).

fof(f157,plain,(
    spl8_2 ),
    inference(avatar_split_clause,[],[f99,f155])).

fof(f99,plain,(
    v4_orders_2(sK0) ),
    inference(cnf_transformation,[],[f84])).

fof(f150,plain,(
    spl8_0 ),
    inference(avatar_split_clause,[],[f98,f148])).

fof(f98,plain,(
    v3_orders_2(sK0) ),
    inference(cnf_transformation,[],[f84])).
%------------------------------------------------------------------------------
