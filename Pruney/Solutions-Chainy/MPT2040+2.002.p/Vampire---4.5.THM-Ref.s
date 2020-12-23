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
% DateTime   : Thu Dec  3 13:23:18 EST 2020

% Result     : Theorem 0.22s
% Output     : Refutation 0.22s
% Verified   : 
% Statistics : Number of formulae       :  279 ( 829 expanded)
%              Number of leaves         :   69 ( 446 expanded)
%              Depth                    :   11
%              Number of atoms          : 2183 (7127 expanded)
%              Number of equality atoms :   62 ( 163 expanded)
%              Maximal formula depth    :   27 (   8 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f435,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f112,f116,f120,f124,f128,f132,f136,f140,f144,f148,f152,f156,f160,f164,f168,f179,f197,f202,f207,f210,f224,f226,f228,f234,f238,f244,f252,f257,f262,f264,f274,f287,f289,f302,f307,f312,f340,f355,f364,f368,f370,f383,f396,f401,f404,f414,f415,f416,f418,f427,f434])).

fof(f434,plain,
    ( ~ spl9_16
    | ~ spl9_15
    | ~ spl9_14
    | ~ spl9_13
    | ~ spl9_12
    | ~ spl9_11
    | ~ spl9_10
    | ~ spl9_9
    | ~ spl9_8
    | spl9_7
    | ~ spl9_6
    | ~ spl9_5
    | ~ spl9_4
    | ~ spl9_27
    | ~ spl9_37
    | ~ spl9_3
    | ~ spl9_26
    | spl9_46 ),
    inference(avatar_split_clause,[],[f432,f334,f232,f114,f292,f236,f118,f122,f126,f130,f134,f138,f142,f146,f150,f154,f158,f162,f166])).

fof(f166,plain,
    ( spl9_16
  <=> v2_pre_topc(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_16])])).

fof(f162,plain,
    ( spl9_15
  <=> v8_pre_topc(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_15])])).

fof(f158,plain,
    ( spl9_14
  <=> v3_orders_2(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_14])])).

fof(f154,plain,
    ( spl9_13
  <=> v4_orders_2(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_13])])).

fof(f150,plain,
    ( spl9_12
  <=> v5_orders_2(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_12])])).

fof(f146,plain,
    ( spl9_11
  <=> v1_lattice3(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_11])])).

fof(f142,plain,
    ( spl9_10
  <=> v2_lattice3(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_10])])).

fof(f138,plain,
    ( spl9_9
  <=> v1_compts_1(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_9])])).

fof(f134,plain,
    ( spl9_8
  <=> l1_waybel_9(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_8])])).

fof(f130,plain,
    ( spl9_7
  <=> v2_struct_0(sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_7])])).

fof(f126,plain,
    ( spl9_6
  <=> v4_orders_2(sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_6])])).

fof(f122,plain,
    ( spl9_5
  <=> v7_waybel_0(sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_5])])).

fof(f118,plain,
    ( spl9_4
  <=> l1_waybel_0(sK1,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_4])])).

fof(f236,plain,
    ( spl9_27
  <=> m1_subset_1(k1_waybel_9(sK0,sK1),u1_struct_0(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_27])])).

fof(f292,plain,
    ( spl9_37
  <=> v5_pre_topc(k4_waybel_1(sK0,sK7(sK0)),sK0,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_37])])).

fof(f114,plain,
    ( spl9_3
  <=> v11_waybel_0(sK1,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_3])])).

fof(f232,plain,
    ( spl9_26
  <=> r3_waybel_9(sK0,sK1,k1_waybel_9(sK0,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_26])])).

fof(f334,plain,
    ( spl9_46
  <=> r1_lattice3(sK0,k2_relset_1(u1_struct_0(sK1),u1_struct_0(sK0),u1_waybel_0(sK0,sK1)),k1_waybel_9(sK0,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_46])])).

fof(f432,plain,
    ( ~ r3_waybel_9(sK0,sK1,k1_waybel_9(sK0,sK1))
    | ~ v11_waybel_0(sK1,sK0)
    | ~ v5_pre_topc(k4_waybel_1(sK0,sK7(sK0)),sK0,sK0)
    | ~ m1_subset_1(k1_waybel_9(sK0,sK1),u1_struct_0(sK0))
    | ~ l1_waybel_0(sK1,sK0)
    | ~ v7_waybel_0(sK1)
    | ~ v4_orders_2(sK1)
    | v2_struct_0(sK1)
    | ~ l1_waybel_9(sK0)
    | ~ v1_compts_1(sK0)
    | ~ v2_lattice3(sK0)
    | ~ v1_lattice3(sK0)
    | ~ v5_orders_2(sK0)
    | ~ v4_orders_2(sK0)
    | ~ v3_orders_2(sK0)
    | ~ v8_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | spl9_46 ),
    inference(resolution,[],[f335,f105])).

fof(f105,plain,(
    ! [X0,X3,X1] :
      ( r1_lattice3(X0,k2_relset_1(u1_struct_0(X1),u1_struct_0(X0),u1_waybel_0(X0,X1)),X3)
      | ~ r3_waybel_9(X0,X1,X3)
      | ~ v11_waybel_0(X1,X0)
      | ~ v5_pre_topc(k4_waybel_1(X0,sK7(X0)),X0,X0)
      | ~ m1_subset_1(X3,u1_struct_0(X0))
      | ~ l1_waybel_0(X1,X0)
      | ~ v7_waybel_0(X1)
      | ~ v4_orders_2(X1)
      | v2_struct_0(X1)
      | ~ l1_waybel_9(X0)
      | ~ v1_compts_1(X0)
      | ~ v2_lattice3(X0)
      | ~ v1_lattice3(X0)
      | ~ v5_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v3_orders_2(X0)
      | ~ v8_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(duplicate_literal_removal,[],[f98])).

fof(f98,plain,(
    ! [X0,X3,X1] :
      ( r1_lattice3(X0,k2_relset_1(u1_struct_0(X1),u1_struct_0(X0),u1_waybel_0(X0,X1)),X3)
      | ~ r3_waybel_9(X0,X1,X3)
      | ~ v11_waybel_0(X1,X0)
      | ~ v5_pre_topc(k4_waybel_1(X0,sK7(X0)),X0,X0)
      | ~ m1_subset_1(X3,u1_struct_0(X0))
      | ~ m1_subset_1(X3,u1_struct_0(X0))
      | ~ l1_waybel_0(X1,X0)
      | ~ v7_waybel_0(X1)
      | ~ v4_orders_2(X1)
      | v2_struct_0(X1)
      | ~ l1_waybel_9(X0)
      | ~ v1_compts_1(X0)
      | ~ v2_lattice3(X0)
      | ~ v1_lattice3(X0)
      | ~ v5_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v3_orders_2(X0)
      | ~ v8_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(equality_resolution,[],[f93])).

fof(f93,plain,(
    ! [X2,X0,X3,X1] :
      ( r1_lattice3(X0,k2_relset_1(u1_struct_0(X1),u1_struct_0(X0),u1_waybel_0(X0,X1)),X3)
      | ~ r3_waybel_9(X0,X1,X2)
      | ~ v11_waybel_0(X1,X0)
      | ~ v5_pre_topc(k4_waybel_1(X0,sK7(X0)),X0,X0)
      | X2 != X3
      | ~ m1_subset_1(X3,u1_struct_0(X0))
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ l1_waybel_0(X1,X0)
      | ~ v7_waybel_0(X1)
      | ~ v4_orders_2(X1)
      | v2_struct_0(X1)
      | ~ l1_waybel_9(X0)
      | ~ v1_compts_1(X0)
      | ~ v2_lattice3(X0)
      | ~ v1_lattice3(X0)
      | ~ v5_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v3_orders_2(X0)
      | ~ v8_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f50])).

fof(f50,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( r1_lattice3(X0,k2_relset_1(u1_struct_0(X1),u1_struct_0(X0),u1_waybel_0(X0,X1)),X3)
                  | ~ r3_waybel_9(X0,X1,X2)
                  | ~ v11_waybel_0(X1,X0)
                  | ( ~ v5_pre_topc(k4_waybel_1(X0,sK7(X0)),X0,X0)
                    & m1_subset_1(sK7(X0),u1_struct_0(X0)) )
                  | X2 != X3
                  | ~ m1_subset_1(X3,u1_struct_0(X0)) )
              | ~ m1_subset_1(X2,u1_struct_0(X0)) )
          | ~ l1_waybel_0(X1,X0)
          | ~ v7_waybel_0(X1)
          | ~ v4_orders_2(X1)
          | v2_struct_0(X1) )
      | ~ l1_waybel_9(X0)
      | ~ v1_compts_1(X0)
      | ~ v2_lattice3(X0)
      | ~ v1_lattice3(X0)
      | ~ v5_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v3_orders_2(X0)
      | ~ v8_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK7])],[f31,f49])).

fof(f49,plain,(
    ! [X0] :
      ( ? [X4] :
          ( ~ v5_pre_topc(k4_waybel_1(X0,X4),X0,X0)
          & m1_subset_1(X4,u1_struct_0(X0)) )
     => ( ~ v5_pre_topc(k4_waybel_1(X0,sK7(X0)),X0,X0)
        & m1_subset_1(sK7(X0),u1_struct_0(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f31,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( r1_lattice3(X0,k2_relset_1(u1_struct_0(X1),u1_struct_0(X0),u1_waybel_0(X0,X1)),X3)
                  | ~ r3_waybel_9(X0,X1,X2)
                  | ~ v11_waybel_0(X1,X0)
                  | ? [X4] :
                      ( ~ v5_pre_topc(k4_waybel_1(X0,X4),X0,X0)
                      & m1_subset_1(X4,u1_struct_0(X0)) )
                  | X2 != X3
                  | ~ m1_subset_1(X3,u1_struct_0(X0)) )
              | ~ m1_subset_1(X2,u1_struct_0(X0)) )
          | ~ l1_waybel_0(X1,X0)
          | ~ v7_waybel_0(X1)
          | ~ v4_orders_2(X1)
          | v2_struct_0(X1) )
      | ~ l1_waybel_9(X0)
      | ~ v1_compts_1(X0)
      | ~ v2_lattice3(X0)
      | ~ v1_lattice3(X0)
      | ~ v5_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v3_orders_2(X0)
      | ~ v8_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(flattening,[],[f30])).

fof(f30,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( r1_lattice3(X0,k2_relset_1(u1_struct_0(X1),u1_struct_0(X0),u1_waybel_0(X0,X1)),X3)
                  | ~ r3_waybel_9(X0,X1,X2)
                  | ~ v11_waybel_0(X1,X0)
                  | ? [X4] :
                      ( ~ v5_pre_topc(k4_waybel_1(X0,X4),X0,X0)
                      & m1_subset_1(X4,u1_struct_0(X0)) )
                  | X2 != X3
                  | ~ m1_subset_1(X3,u1_struct_0(X0)) )
              | ~ m1_subset_1(X2,u1_struct_0(X0)) )
          | ~ l1_waybel_0(X1,X0)
          | ~ v7_waybel_0(X1)
          | ~ v4_orders_2(X1)
          | v2_struct_0(X1) )
      | ~ l1_waybel_9(X0)
      | ~ v1_compts_1(X0)
      | ~ v2_lattice3(X0)
      | ~ v1_lattice3(X0)
      | ~ v5_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v3_orders_2(X0)
      | ~ v8_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0] :
      ( ( l1_waybel_9(X0)
        & v1_compts_1(X0)
        & v2_lattice3(X0)
        & v1_lattice3(X0)
        & v5_orders_2(X0)
        & v4_orders_2(X0)
        & v3_orders_2(X0)
        & v8_pre_topc(X0)
        & v2_pre_topc(X0) )
     => ! [X1] :
          ( ( l1_waybel_0(X1,X0)
            & v7_waybel_0(X1)
            & v4_orders_2(X1)
            & ~ v2_struct_0(X1) )
         => ! [X2] :
              ( m1_subset_1(X2,u1_struct_0(X0))
             => ! [X3] :
                  ( m1_subset_1(X3,u1_struct_0(X0))
                 => ( ( r3_waybel_9(X0,X1,X2)
                      & v11_waybel_0(X1,X0)
                      & ! [X4] :
                          ( m1_subset_1(X4,u1_struct_0(X0))
                         => v5_pre_topc(k4_waybel_1(X0,X4),X0,X0) )
                      & X2 = X3 )
                   => r1_lattice3(X0,k2_relset_1(u1_struct_0(X1),u1_struct_0(X0),u1_waybel_0(X0,X1)),X3) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l51_waybel_9)).

fof(f335,plain,
    ( ~ r1_lattice3(sK0,k2_relset_1(u1_struct_0(sK1),u1_struct_0(sK0),u1_waybel_0(sK0,sK1)),k1_waybel_9(sK0,sK1))
    | spl9_46 ),
    inference(avatar_component_clause,[],[f334])).

fof(f427,plain,
    ( spl9_22
    | ~ spl9_16
    | ~ spl9_15
    | ~ spl9_9
    | ~ spl9_23
    | spl9_7
    | ~ spl9_6
    | ~ spl9_5
    | ~ spl9_4
    | spl9_58
    | ~ spl9_54
    | ~ spl9_57 ),
    inference(avatar_split_clause,[],[f426,f394,f381,f399,f118,f122,f126,f130,f216,f138,f162,f166,f213])).

fof(f213,plain,
    ( spl9_22
  <=> v2_struct_0(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_22])])).

fof(f216,plain,
    ( spl9_23
  <=> l1_pre_topc(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_23])])).

fof(f399,plain,
    ( spl9_58
  <=> ! [X0] :
        ( ~ r3_waybel_9(sK0,sK1,X0)
        | r2_hidden(X0,k10_yellow_6(sK0,sK1))
        | ~ m1_subset_1(X0,u1_struct_0(sK0)) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_58])])).

fof(f381,plain,
    ( spl9_54
  <=> k1_waybel_9(sK0,sK1) = sK3(sK0,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_54])])).

fof(f394,plain,
    ( spl9_57
  <=> k1_waybel_9(sK0,sK1) = sK2(sK0,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_57])])).

fof(f426,plain,
    ( ! [X0] :
        ( ~ r3_waybel_9(sK0,sK1,X0)
        | ~ m1_subset_1(X0,u1_struct_0(sK0))
        | r2_hidden(X0,k10_yellow_6(sK0,sK1))
        | ~ l1_waybel_0(sK1,sK0)
        | ~ v7_waybel_0(sK1)
        | ~ v4_orders_2(sK1)
        | v2_struct_0(sK1)
        | ~ l1_pre_topc(sK0)
        | ~ v1_compts_1(sK0)
        | ~ v8_pre_topc(sK0)
        | ~ v2_pre_topc(sK0)
        | v2_struct_0(sK0) )
    | ~ spl9_54
    | ~ spl9_57 ),
    inference(trivial_inequality_removal,[],[f425])).

fof(f425,plain,
    ( ! [X0] :
        ( k1_waybel_9(sK0,sK1) != k1_waybel_9(sK0,sK1)
        | ~ r3_waybel_9(sK0,sK1,X0)
        | ~ m1_subset_1(X0,u1_struct_0(sK0))
        | r2_hidden(X0,k10_yellow_6(sK0,sK1))
        | ~ l1_waybel_0(sK1,sK0)
        | ~ v7_waybel_0(sK1)
        | ~ v4_orders_2(sK1)
        | v2_struct_0(sK1)
        | ~ l1_pre_topc(sK0)
        | ~ v1_compts_1(sK0)
        | ~ v8_pre_topc(sK0)
        | ~ v2_pre_topc(sK0)
        | v2_struct_0(sK0) )
    | ~ spl9_54
    | ~ spl9_57 ),
    inference(forward_demodulation,[],[f423,f395])).

fof(f395,plain,
    ( k1_waybel_9(sK0,sK1) = sK2(sK0,sK1)
    | ~ spl9_57 ),
    inference(avatar_component_clause,[],[f394])).

fof(f423,plain,
    ( ! [X0] :
        ( k1_waybel_9(sK0,sK1) != sK2(sK0,sK1)
        | ~ r3_waybel_9(sK0,sK1,X0)
        | ~ m1_subset_1(X0,u1_struct_0(sK0))
        | r2_hidden(X0,k10_yellow_6(sK0,sK1))
        | ~ l1_waybel_0(sK1,sK0)
        | ~ v7_waybel_0(sK1)
        | ~ v4_orders_2(sK1)
        | v2_struct_0(sK1)
        | ~ l1_pre_topc(sK0)
        | ~ v1_compts_1(sK0)
        | ~ v8_pre_topc(sK0)
        | ~ v2_pre_topc(sK0)
        | v2_struct_0(sK0) )
    | ~ spl9_54 ),
    inference(superposition,[],[f79,f382])).

fof(f382,plain,
    ( k1_waybel_9(sK0,sK1) = sK3(sK0,sK1)
    | ~ spl9_54 ),
    inference(avatar_component_clause,[],[f381])).

fof(f79,plain,(
    ! [X2,X0,X1] :
      ( sK2(X0,X1) != sK3(X0,X1)
      | ~ r3_waybel_9(X0,X1,X2)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | r2_hidden(X2,k10_yellow_6(X0,X1))
      | ~ l1_waybel_0(X1,X0)
      | ~ v7_waybel_0(X1)
      | ~ v4_orders_2(X1)
      | v2_struct_0(X1)
      | ~ l1_pre_topc(X0)
      | ~ v1_compts_1(X0)
      | ~ v8_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f42])).

fof(f42,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( r2_hidden(X2,k10_yellow_6(X0,X1))
              | ~ r3_waybel_9(X0,X1,X2)
              | ~ m1_subset_1(X2,u1_struct_0(X0)) )
          | ( sK2(X0,X1) != sK3(X0,X1)
            & r3_waybel_9(X0,X1,sK3(X0,X1))
            & r3_waybel_9(X0,X1,sK2(X0,X1))
            & m1_subset_1(sK3(X0,X1),u1_struct_0(X0))
            & m1_subset_1(sK2(X0,X1),u1_struct_0(X0)) )
          | ~ l1_waybel_0(X1,X0)
          | ~ v7_waybel_0(X1)
          | ~ v4_orders_2(X1)
          | v2_struct_0(X1) )
      | ~ l1_pre_topc(X0)
      | ~ v1_compts_1(X0)
      | ~ v8_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2,sK3])],[f39,f41,f40])).

fof(f40,plain,(
    ! [X1,X0] :
      ( ? [X3] :
          ( ? [X4] :
              ( X3 != X4
              & r3_waybel_9(X0,X1,X4)
              & r3_waybel_9(X0,X1,X3)
              & m1_subset_1(X4,u1_struct_0(X0)) )
          & m1_subset_1(X3,u1_struct_0(X0)) )
     => ( ? [X4] :
            ( sK2(X0,X1) != X4
            & r3_waybel_9(X0,X1,X4)
            & r3_waybel_9(X0,X1,sK2(X0,X1))
            & m1_subset_1(X4,u1_struct_0(X0)) )
        & m1_subset_1(sK2(X0,X1),u1_struct_0(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f41,plain,(
    ! [X1,X0] :
      ( ? [X4] :
          ( sK2(X0,X1) != X4
          & r3_waybel_9(X0,X1,X4)
          & r3_waybel_9(X0,X1,sK2(X0,X1))
          & m1_subset_1(X4,u1_struct_0(X0)) )
     => ( sK2(X0,X1) != sK3(X0,X1)
        & r3_waybel_9(X0,X1,sK3(X0,X1))
        & r3_waybel_9(X0,X1,sK2(X0,X1))
        & m1_subset_1(sK3(X0,X1),u1_struct_0(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f39,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( r2_hidden(X2,k10_yellow_6(X0,X1))
              | ~ r3_waybel_9(X0,X1,X2)
              | ~ m1_subset_1(X2,u1_struct_0(X0)) )
          | ? [X3] :
              ( ? [X4] :
                  ( X3 != X4
                  & r3_waybel_9(X0,X1,X4)
                  & r3_waybel_9(X0,X1,X3)
                  & m1_subset_1(X4,u1_struct_0(X0)) )
              & m1_subset_1(X3,u1_struct_0(X0)) )
          | ~ l1_waybel_0(X1,X0)
          | ~ v7_waybel_0(X1)
          | ~ v4_orders_2(X1)
          | v2_struct_0(X1) )
      | ~ l1_pre_topc(X0)
      | ~ v1_compts_1(X0)
      | ~ v8_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(rectify,[],[f23])).

fof(f23,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X4] :
              ( r2_hidden(X4,k10_yellow_6(X0,X1))
              | ~ r3_waybel_9(X0,X1,X4)
              | ~ m1_subset_1(X4,u1_struct_0(X0)) )
          | ? [X2] :
              ( ? [X3] :
                  ( X2 != X3
                  & r3_waybel_9(X0,X1,X3)
                  & r3_waybel_9(X0,X1,X2)
                  & m1_subset_1(X3,u1_struct_0(X0)) )
              & m1_subset_1(X2,u1_struct_0(X0)) )
          | ~ l1_waybel_0(X1,X0)
          | ~ v7_waybel_0(X1)
          | ~ v4_orders_2(X1)
          | v2_struct_0(X1) )
      | ~ l1_pre_topc(X0)
      | ~ v1_compts_1(X0)
      | ~ v8_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f22])).

fof(f22,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X4] :
              ( r2_hidden(X4,k10_yellow_6(X0,X1))
              | ~ r3_waybel_9(X0,X1,X4)
              | ~ m1_subset_1(X4,u1_struct_0(X0)) )
          | ? [X2] :
              ( ? [X3] :
                  ( X2 != X3
                  & r3_waybel_9(X0,X1,X3)
                  & r3_waybel_9(X0,X1,X2)
                  & m1_subset_1(X3,u1_struct_0(X0)) )
              & m1_subset_1(X2,u1_struct_0(X0)) )
          | ~ l1_waybel_0(X1,X0)
          | ~ v7_waybel_0(X1)
          | ~ v4_orders_2(X1)
          | v2_struct_0(X1) )
      | ~ l1_pre_topc(X0)
      | ~ v1_compts_1(X0)
      | ~ v8_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f13,plain,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v1_compts_1(X0)
        & v8_pre_topc(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( ( l1_waybel_0(X1,X0)
            & v7_waybel_0(X1)
            & v4_orders_2(X1)
            & ~ v2_struct_0(X1) )
         => ( ! [X2] :
                ( m1_subset_1(X2,u1_struct_0(X0))
               => ! [X3] :
                    ( m1_subset_1(X3,u1_struct_0(X0))
                   => ( ( r3_waybel_9(X0,X1,X3)
                        & r3_waybel_9(X0,X1,X2) )
                     => X2 = X3 ) ) )
           => ! [X4] :
                ( m1_subset_1(X4,u1_struct_0(X0))
               => ( r3_waybel_9(X0,X1,X4)
                 => r2_hidden(X4,k10_yellow_6(X0,X1)) ) ) ) ) ) ),
    inference(rectify,[],[f8])).

fof(f8,axiom,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v1_compts_1(X0)
        & v8_pre_topc(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( ( l1_waybel_0(X1,X0)
            & v7_waybel_0(X1)
            & v4_orders_2(X1)
            & ~ v2_struct_0(X1) )
         => ( ! [X2] :
                ( m1_subset_1(X2,u1_struct_0(X0))
               => ! [X3] :
                    ( m1_subset_1(X3,u1_struct_0(X0))
                   => ( ( r3_waybel_9(X0,X1,X3)
                        & r3_waybel_9(X0,X1,X2) )
                     => X2 = X3 ) ) )
           => ! [X2] :
                ( m1_subset_1(X2,u1_struct_0(X0))
               => ( r3_waybel_9(X0,X1,X2)
                 => r2_hidden(X2,k10_yellow_6(X0,X1)) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t33_waybel_9)).

fof(f418,plain,
    ( ~ spl9_4
    | spl9_1
    | ~ spl9_8
    | ~ spl9_43 ),
    inference(avatar_split_clause,[],[f356,f318,f134,f107,f118])).

fof(f107,plain,
    ( spl9_1
  <=> r2_waybel_9(sK0,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_1])])).

fof(f318,plain,
    ( spl9_43
  <=> r2_yellow_0(sK0,k2_relset_1(u1_struct_0(sK1),u1_struct_0(sK0),u1_waybel_0(sK0,sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_43])])).

fof(f356,plain,
    ( r2_waybel_9(sK0,sK1)
    | ~ l1_waybel_0(sK1,sK0)
    | ~ spl9_8
    | ~ spl9_43 ),
    inference(resolution,[],[f319,f170])).

fof(f170,plain,
    ( ! [X0] :
        ( ~ r2_yellow_0(sK0,k2_relset_1(u1_struct_0(X0),u1_struct_0(sK0),u1_waybel_0(sK0,X0)))
        | r2_waybel_9(sK0,X0)
        | ~ l1_waybel_0(X0,sK0) )
    | ~ spl9_8 ),
    inference(resolution,[],[f169,f135])).

fof(f135,plain,
    ( l1_waybel_9(sK0)
    | ~ spl9_8 ),
    inference(avatar_component_clause,[],[f134])).

fof(f169,plain,(
    ! [X0,X1] :
      ( ~ l1_waybel_9(X0)
      | ~ l1_waybel_0(X1,X0)
      | r2_waybel_9(X0,X1)
      | ~ r2_yellow_0(X0,k2_relset_1(u1_struct_0(X1),u1_struct_0(X0),u1_waybel_0(X0,X1))) ) ),
    inference(resolution,[],[f72,f74])).

fof(f74,plain,(
    ! [X0] :
      ( l1_orders_2(X0)
      | ~ l1_waybel_9(X0) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f21,plain,(
    ! [X0] :
      ( ( l1_orders_2(X0)
        & l1_pre_topc(X0) )
      | ~ l1_waybel_9(X0) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0] :
      ( l1_waybel_9(X0)
     => ( l1_orders_2(X0)
        & l1_pre_topc(X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_l1_waybel_9)).

fof(f72,plain,(
    ! [X0,X1] :
      ( ~ l1_orders_2(X0)
      | ~ r2_yellow_0(X0,k2_relset_1(u1_struct_0(X1),u1_struct_0(X0),u1_waybel_0(X0,X1)))
      | ~ l1_waybel_0(X1,X0)
      | r2_waybel_9(X0,X1) ) ),
    inference(cnf_transformation,[],[f38])).

fof(f38,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ( r2_waybel_9(X0,X1)
              | ~ r2_yellow_0(X0,k2_relset_1(u1_struct_0(X1),u1_struct_0(X0),u1_waybel_0(X0,X1))) )
            & ( r2_yellow_0(X0,k2_relset_1(u1_struct_0(X1),u1_struct_0(X0),u1_waybel_0(X0,X1)))
              | ~ r2_waybel_9(X0,X1) ) )
          | ~ l1_waybel_0(X1,X0) )
      | ~ l1_orders_2(X0) ) ),
    inference(nnf_transformation,[],[f20])).

fof(f20,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( r2_waybel_9(X0,X1)
          <=> r2_yellow_0(X0,k2_relset_1(u1_struct_0(X1),u1_struct_0(X0),u1_waybel_0(X0,X1))) )
          | ~ l1_waybel_0(X1,X0) )
      | ~ l1_orders_2(X0) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0] :
      ( l1_orders_2(X0)
     => ! [X1] :
          ( l1_waybel_0(X1,X0)
         => ( r2_waybel_9(X0,X1)
          <=> r2_yellow_0(X0,k2_relset_1(u1_struct_0(X1),u1_struct_0(X0),u1_waybel_0(X0,X1))) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d4_waybel_9)).

fof(f319,plain,
    ( r2_yellow_0(sK0,k2_relset_1(u1_struct_0(sK1),u1_struct_0(sK0),u1_waybel_0(sK0,sK1)))
    | ~ spl9_43 ),
    inference(avatar_component_clause,[],[f318])).

fof(f416,plain,
    ( spl9_22
    | ~ spl9_16
    | ~ spl9_15
    | ~ spl9_9
    | ~ spl9_23
    | spl9_7
    | ~ spl9_6
    | ~ spl9_5
    | ~ spl9_4
    | spl9_58
    | spl9_55 ),
    inference(avatar_split_clause,[],[f402,f387,f399,f118,f122,f126,f130,f216,f138,f162,f166,f213])).

fof(f387,plain,
    ( spl9_55
  <=> m1_subset_1(sK2(sK0,sK1),u1_struct_0(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_55])])).

fof(f402,plain,
    ( ! [X0] :
        ( ~ r3_waybel_9(sK0,sK1,X0)
        | ~ m1_subset_1(X0,u1_struct_0(sK0))
        | r2_hidden(X0,k10_yellow_6(sK0,sK1))
        | ~ l1_waybel_0(sK1,sK0)
        | ~ v7_waybel_0(sK1)
        | ~ v4_orders_2(sK1)
        | v2_struct_0(sK1)
        | ~ l1_pre_topc(sK0)
        | ~ v1_compts_1(sK0)
        | ~ v8_pre_topc(sK0)
        | ~ v2_pre_topc(sK0)
        | v2_struct_0(sK0) )
    | spl9_55 ),
    inference(resolution,[],[f388,f75])).

fof(f75,plain,(
    ! [X2,X0,X1] :
      ( m1_subset_1(sK2(X0,X1),u1_struct_0(X0))
      | ~ r3_waybel_9(X0,X1,X2)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | r2_hidden(X2,k10_yellow_6(X0,X1))
      | ~ l1_waybel_0(X1,X0)
      | ~ v7_waybel_0(X1)
      | ~ v4_orders_2(X1)
      | v2_struct_0(X1)
      | ~ l1_pre_topc(X0)
      | ~ v1_compts_1(X0)
      | ~ v8_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f42])).

fof(f388,plain,
    ( ~ m1_subset_1(sK2(sK0,sK1),u1_struct_0(sK0))
    | spl9_55 ),
    inference(avatar_component_clause,[],[f387])).

fof(f415,plain,
    ( ~ spl9_42
    | spl9_43
    | ~ spl9_44
    | ~ spl9_36
    | ~ spl9_46 ),
    inference(avatar_split_clause,[],[f411,f334,f285,f321,f318,f315])).

fof(f315,plain,
    ( spl9_42
  <=> r1_lattice3(sK0,k2_relset_1(u1_struct_0(sK1),u1_struct_0(sK0),u1_waybel_0(sK0,sK1)),sK5(sK0,k1_waybel_9(sK0,sK1),k2_relset_1(u1_struct_0(sK1),u1_struct_0(sK0),u1_waybel_0(sK0,sK1)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_42])])).

fof(f321,plain,
    ( spl9_44
  <=> m1_subset_1(sK5(sK0,k1_waybel_9(sK0,sK1),k2_relset_1(u1_struct_0(sK1),u1_struct_0(sK0),u1_waybel_0(sK0,sK1))),u1_struct_0(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_44])])).

fof(f285,plain,
    ( spl9_36
  <=> ! [X1] :
        ( ~ m1_subset_1(sK5(sK0,k1_waybel_9(sK0,sK1),X1),u1_struct_0(sK0))
        | ~ r1_lattice3(sK0,X1,k1_waybel_9(sK0,sK1))
        | r2_yellow_0(sK0,X1)
        | ~ r1_lattice3(sK0,k2_relset_1(u1_struct_0(sK1),u1_struct_0(sK0),u1_waybel_0(sK0,sK1)),sK5(sK0,k1_waybel_9(sK0,sK1),X1)) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_36])])).

fof(f411,plain,
    ( ~ m1_subset_1(sK5(sK0,k1_waybel_9(sK0,sK1),k2_relset_1(u1_struct_0(sK1),u1_struct_0(sK0),u1_waybel_0(sK0,sK1))),u1_struct_0(sK0))
    | r2_yellow_0(sK0,k2_relset_1(u1_struct_0(sK1),u1_struct_0(sK0),u1_waybel_0(sK0,sK1)))
    | ~ r1_lattice3(sK0,k2_relset_1(u1_struct_0(sK1),u1_struct_0(sK0),u1_waybel_0(sK0,sK1)),sK5(sK0,k1_waybel_9(sK0,sK1),k2_relset_1(u1_struct_0(sK1),u1_struct_0(sK0),u1_waybel_0(sK0,sK1))))
    | ~ spl9_36
    | ~ spl9_46 ),
    inference(resolution,[],[f407,f286])).

fof(f286,plain,
    ( ! [X1] :
        ( ~ r1_lattice3(sK0,X1,k1_waybel_9(sK0,sK1))
        | ~ m1_subset_1(sK5(sK0,k1_waybel_9(sK0,sK1),X1),u1_struct_0(sK0))
        | r2_yellow_0(sK0,X1)
        | ~ r1_lattice3(sK0,k2_relset_1(u1_struct_0(sK1),u1_struct_0(sK0),u1_waybel_0(sK0,sK1)),sK5(sK0,k1_waybel_9(sK0,sK1),X1)) )
    | ~ spl9_36 ),
    inference(avatar_component_clause,[],[f285])).

fof(f407,plain,
    ( r1_lattice3(sK0,k2_relset_1(u1_struct_0(sK1),u1_struct_0(sK0),u1_waybel_0(sK0,sK1)),k1_waybel_9(sK0,sK1))
    | ~ spl9_46 ),
    inference(avatar_component_clause,[],[f334])).

fof(f414,plain,
    ( ~ spl9_12
    | ~ spl9_34
    | ~ spl9_27
    | ~ spl9_46
    | spl9_43
    | spl9_44 ),
    inference(avatar_split_clause,[],[f413,f321,f318,f334,f236,f278,f150])).

fof(f278,plain,
    ( spl9_34
  <=> l1_orders_2(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_34])])).

fof(f413,plain,
    ( r2_yellow_0(sK0,k2_relset_1(u1_struct_0(sK1),u1_struct_0(sK0),u1_waybel_0(sK0,sK1)))
    | ~ r1_lattice3(sK0,k2_relset_1(u1_struct_0(sK1),u1_struct_0(sK0),u1_waybel_0(sK0,sK1)),k1_waybel_9(sK0,sK1))
    | ~ m1_subset_1(k1_waybel_9(sK0,sK1),u1_struct_0(sK0))
    | ~ l1_orders_2(sK0)
    | ~ v5_orders_2(sK0)
    | spl9_44 ),
    inference(resolution,[],[f322,f87])).

fof(f87,plain,(
    ! [X2,X0,X1] :
      ( m1_subset_1(sK5(X0,X1,X2),u1_struct_0(X0))
      | r2_yellow_0(X0,X2)
      | ~ r1_lattice3(X0,X2,X1)
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | ~ v5_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f46])).

fof(f46,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( ( r2_yellow_0(X0,X2)
                  & k2_yellow_0(X0,X2) = X1 )
                | ( ~ r1_orders_2(X0,sK5(X0,X1,X2),X1)
                  & r1_lattice3(X0,X2,sK5(X0,X1,X2))
                  & m1_subset_1(sK5(X0,X1,X2),u1_struct_0(X0)) )
                | ~ r1_lattice3(X0,X2,X1) )
              & ( ( ! [X4] :
                      ( r1_orders_2(X0,X4,X1)
                      | ~ r1_lattice3(X0,X2,X4)
                      | ~ m1_subset_1(X4,u1_struct_0(X0)) )
                  & r1_lattice3(X0,X2,X1) )
                | ~ r2_yellow_0(X0,X2)
                | k2_yellow_0(X0,X2) != X1 ) )
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l1_orders_2(X0)
      | ~ v5_orders_2(X0) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK5])],[f27,f45])).

fof(f45,plain,(
    ! [X2,X1,X0] :
      ( ? [X3] :
          ( ~ r1_orders_2(X0,X3,X1)
          & r1_lattice3(X0,X2,X3)
          & m1_subset_1(X3,u1_struct_0(X0)) )
     => ( ~ r1_orders_2(X0,sK5(X0,X1,X2),X1)
        & r1_lattice3(X0,X2,sK5(X0,X1,X2))
        & m1_subset_1(sK5(X0,X1,X2),u1_struct_0(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f27,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( ( r2_yellow_0(X0,X2)
                  & k2_yellow_0(X0,X2) = X1 )
                | ? [X3] :
                    ( ~ r1_orders_2(X0,X3,X1)
                    & r1_lattice3(X0,X2,X3)
                    & m1_subset_1(X3,u1_struct_0(X0)) )
                | ~ r1_lattice3(X0,X2,X1) )
              & ( ( ! [X4] :
                      ( r1_orders_2(X0,X4,X1)
                      | ~ r1_lattice3(X0,X2,X4)
                      | ~ m1_subset_1(X4,u1_struct_0(X0)) )
                  & r1_lattice3(X0,X2,X1) )
                | ~ r2_yellow_0(X0,X2)
                | k2_yellow_0(X0,X2) != X1 ) )
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l1_orders_2(X0)
      | ~ v5_orders_2(X0) ) ),
    inference(flattening,[],[f26])).

fof(f26,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( ( r2_yellow_0(X0,X2)
                  & k2_yellow_0(X0,X2) = X1 )
                | ? [X3] :
                    ( ~ r1_orders_2(X0,X3,X1)
                    & r1_lattice3(X0,X2,X3)
                    & m1_subset_1(X3,u1_struct_0(X0)) )
                | ~ r1_lattice3(X0,X2,X1) )
              & ( ( ! [X4] :
                      ( r1_orders_2(X0,X4,X1)
                      | ~ r1_lattice3(X0,X2,X4)
                      | ~ m1_subset_1(X4,u1_struct_0(X0)) )
                  & r1_lattice3(X0,X2,X1) )
                | ~ r2_yellow_0(X0,X2)
                | k2_yellow_0(X0,X2) != X1 ) )
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l1_orders_2(X0)
      | ~ v5_orders_2(X0) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f14,plain,(
    ! [X0] :
      ( ( l1_orders_2(X0)
        & v5_orders_2(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,u1_struct_0(X0))
         => ! [X2] :
              ( ( ( ! [X3] :
                      ( m1_subset_1(X3,u1_struct_0(X0))
                     => ( r1_lattice3(X0,X2,X3)
                       => r1_orders_2(X0,X3,X1) ) )
                  & r1_lattice3(X0,X2,X1) )
               => ( r2_yellow_0(X0,X2)
                  & k2_yellow_0(X0,X2) = X1 ) )
              & ( ( r2_yellow_0(X0,X2)
                  & k2_yellow_0(X0,X2) = X1 )
               => ( ! [X4] :
                      ( m1_subset_1(X4,u1_struct_0(X0))
                     => ( r1_lattice3(X0,X2,X4)
                       => r1_orders_2(X0,X4,X1) ) )
                  & r1_lattice3(X0,X2,X1) ) ) ) ) ) ),
    inference(rectify,[],[f2])).

fof(f2,axiom,(
    ! [X0] :
      ( ( l1_orders_2(X0)
        & v5_orders_2(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,u1_struct_0(X0))
         => ! [X2] :
              ( ( ( ! [X3] :
                      ( m1_subset_1(X3,u1_struct_0(X0))
                     => ( r1_lattice3(X0,X2,X3)
                       => r1_orders_2(X0,X3,X1) ) )
                  & r1_lattice3(X0,X2,X1) )
               => ( r2_yellow_0(X0,X2)
                  & k2_yellow_0(X0,X2) = X1 ) )
              & ( ( r2_yellow_0(X0,X2)
                  & k2_yellow_0(X0,X2) = X1 )
               => ( ! [X3] :
                      ( m1_subset_1(X3,u1_struct_0(X0))
                     => ( r1_lattice3(X0,X2,X3)
                       => r1_orders_2(X0,X3,X1) ) )
                  & r1_lattice3(X0,X2,X1) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t31_yellow_0)).

fof(f322,plain,
    ( ~ m1_subset_1(sK5(sK0,k1_waybel_9(sK0,sK1),k2_relset_1(u1_struct_0(sK1),u1_struct_0(sK0),u1_waybel_0(sK0,sK1))),u1_struct_0(sK0))
    | spl9_44 ),
    inference(avatar_component_clause,[],[f321])).

fof(f404,plain,
    ( ~ spl9_27
    | ~ spl9_26
    | spl9_2
    | ~ spl9_58 ),
    inference(avatar_split_clause,[],[f403,f399,f110,f232,f236])).

fof(f110,plain,
    ( spl9_2
  <=> r2_hidden(k1_waybel_9(sK0,sK1),k10_yellow_6(sK0,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_2])])).

fof(f403,plain,
    ( ~ r3_waybel_9(sK0,sK1,k1_waybel_9(sK0,sK1))
    | ~ m1_subset_1(k1_waybel_9(sK0,sK1),u1_struct_0(sK0))
    | spl9_2
    | ~ spl9_58 ),
    inference(resolution,[],[f400,f111])).

fof(f111,plain,
    ( ~ r2_hidden(k1_waybel_9(sK0,sK1),k10_yellow_6(sK0,sK1))
    | spl9_2 ),
    inference(avatar_component_clause,[],[f110])).

fof(f400,plain,
    ( ! [X0] :
        ( r2_hidden(X0,k10_yellow_6(sK0,sK1))
        | ~ r3_waybel_9(sK0,sK1,X0)
        | ~ m1_subset_1(X0,u1_struct_0(sK0)) )
    | ~ spl9_58 ),
    inference(avatar_component_clause,[],[f399])).

fof(f401,plain,
    ( spl9_22
    | ~ spl9_16
    | ~ spl9_15
    | ~ spl9_9
    | ~ spl9_23
    | spl9_7
    | ~ spl9_6
    | ~ spl9_5
    | ~ spl9_4
    | spl9_58
    | spl9_52 ),
    inference(avatar_split_clause,[],[f397,f374,f399,f118,f122,f126,f130,f216,f138,f162,f166,f213])).

fof(f374,plain,
    ( spl9_52
  <=> m1_subset_1(sK3(sK0,sK1),u1_struct_0(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_52])])).

fof(f397,plain,
    ( ! [X0] :
        ( ~ r3_waybel_9(sK0,sK1,X0)
        | ~ m1_subset_1(X0,u1_struct_0(sK0))
        | r2_hidden(X0,k10_yellow_6(sK0,sK1))
        | ~ l1_waybel_0(sK1,sK0)
        | ~ v7_waybel_0(sK1)
        | ~ v4_orders_2(sK1)
        | v2_struct_0(sK1)
        | ~ l1_pre_topc(sK0)
        | ~ v1_compts_1(sK0)
        | ~ v8_pre_topc(sK0)
        | ~ v2_pre_topc(sK0)
        | v2_struct_0(sK0) )
    | spl9_52 ),
    inference(resolution,[],[f375,f76])).

fof(f76,plain,(
    ! [X2,X0,X1] :
      ( m1_subset_1(sK3(X0,X1),u1_struct_0(X0))
      | ~ r3_waybel_9(X0,X1,X2)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | r2_hidden(X2,k10_yellow_6(X0,X1))
      | ~ l1_waybel_0(X1,X0)
      | ~ v7_waybel_0(X1)
      | ~ v4_orders_2(X1)
      | v2_struct_0(X1)
      | ~ l1_pre_topc(X0)
      | ~ v1_compts_1(X0)
      | ~ v8_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f42])).

fof(f375,plain,
    ( ~ m1_subset_1(sK3(sK0,sK1),u1_struct_0(sK0))
    | spl9_52 ),
    inference(avatar_component_clause,[],[f374])).

fof(f396,plain,
    ( spl9_57
    | ~ spl9_55
    | ~ spl9_19
    | ~ spl9_51 ),
    inference(avatar_split_clause,[],[f385,f366,f186,f387,f394])).

fof(f186,plain,
    ( spl9_19
  <=> ! [X0] :
        ( ~ m1_subset_1(X0,u1_struct_0(sK0))
        | ~ r3_waybel_9(sK0,sK1,X0)
        | k1_waybel_9(sK0,sK1) = X0 ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_19])])).

fof(f366,plain,
    ( spl9_51
  <=> r3_waybel_9(sK0,sK1,sK2(sK0,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_51])])).

fof(f385,plain,
    ( ~ m1_subset_1(sK2(sK0,sK1),u1_struct_0(sK0))
    | k1_waybel_9(sK0,sK1) = sK2(sK0,sK1)
    | ~ spl9_19
    | ~ spl9_51 ),
    inference(resolution,[],[f367,f187])).

fof(f187,plain,
    ( ! [X0] :
        ( ~ r3_waybel_9(sK0,sK1,X0)
        | ~ m1_subset_1(X0,u1_struct_0(sK0))
        | k1_waybel_9(sK0,sK1) = X0 )
    | ~ spl9_19 ),
    inference(avatar_component_clause,[],[f186])).

fof(f367,plain,
    ( r3_waybel_9(sK0,sK1,sK2(sK0,sK1))
    | ~ spl9_51 ),
    inference(avatar_component_clause,[],[f366])).

fof(f383,plain,
    ( spl9_54
    | ~ spl9_52
    | ~ spl9_19
    | ~ spl9_50 ),
    inference(avatar_split_clause,[],[f372,f362,f186,f374,f381])).

fof(f362,plain,
    ( spl9_50
  <=> r3_waybel_9(sK0,sK1,sK3(sK0,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_50])])).

fof(f372,plain,
    ( ~ m1_subset_1(sK3(sK0,sK1),u1_struct_0(sK0))
    | k1_waybel_9(sK0,sK1) = sK3(sK0,sK1)
    | ~ spl9_19
    | ~ spl9_50 ),
    inference(resolution,[],[f363,f187])).

fof(f363,plain,
    ( r3_waybel_9(sK0,sK1,sK3(sK0,sK1))
    | ~ spl9_50 ),
    inference(avatar_component_clause,[],[f362])).

fof(f370,plain,
    ( ~ spl9_34
    | ~ spl9_11
    | ~ spl9_22 ),
    inference(avatar_split_clause,[],[f369,f213,f146,f278])).

fof(f369,plain,
    ( ~ v1_lattice3(sK0)
    | ~ l1_orders_2(sK0)
    | ~ spl9_22 ),
    inference(resolution,[],[f214,f70])).

fof(f70,plain,(
    ! [X0] :
      ( ~ v2_struct_0(X0)
      | ~ v1_lattice3(X0)
      | ~ l1_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f19,plain,(
    ! [X0] :
      ( ~ v2_struct_0(X0)
      | ~ v1_lattice3(X0)
      | ~ l1_orders_2(X0) ) ),
    inference(flattening,[],[f18])).

fof(f18,plain,(
    ! [X0] :
      ( ~ v2_struct_0(X0)
      | ~ v1_lattice3(X0)
      | ~ l1_orders_2(X0) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0] :
      ( l1_orders_2(X0)
     => ( v1_lattice3(X0)
       => ~ v2_struct_0(X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_lattice3)).

fof(f214,plain,
    ( v2_struct_0(sK0)
    | ~ spl9_22 ),
    inference(avatar_component_clause,[],[f213])).

fof(f368,plain,
    ( spl9_22
    | ~ spl9_16
    | ~ spl9_15
    | ~ spl9_9
    | ~ spl9_23
    | spl9_7
    | ~ spl9_6
    | ~ spl9_5
    | ~ spl9_4
    | spl9_51
    | ~ spl9_27
    | ~ spl9_26
    | spl9_2 ),
    inference(avatar_split_clause,[],[f360,f110,f232,f236,f366,f118,f122,f126,f130,f216,f138,f162,f166,f213])).

fof(f360,plain,
    ( ~ r3_waybel_9(sK0,sK1,k1_waybel_9(sK0,sK1))
    | ~ m1_subset_1(k1_waybel_9(sK0,sK1),u1_struct_0(sK0))
    | r3_waybel_9(sK0,sK1,sK2(sK0,sK1))
    | ~ l1_waybel_0(sK1,sK0)
    | ~ v7_waybel_0(sK1)
    | ~ v4_orders_2(sK1)
    | v2_struct_0(sK1)
    | ~ l1_pre_topc(sK0)
    | ~ v1_compts_1(sK0)
    | ~ v8_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0)
    | spl9_2 ),
    inference(resolution,[],[f111,f77])).

fof(f77,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(X2,k10_yellow_6(X0,X1))
      | ~ r3_waybel_9(X0,X1,X2)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | r3_waybel_9(X0,X1,sK2(X0,X1))
      | ~ l1_waybel_0(X1,X0)
      | ~ v7_waybel_0(X1)
      | ~ v4_orders_2(X1)
      | v2_struct_0(X1)
      | ~ l1_pre_topc(X0)
      | ~ v1_compts_1(X0)
      | ~ v8_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f42])).

fof(f364,plain,
    ( spl9_22
    | ~ spl9_16
    | ~ spl9_15
    | ~ spl9_9
    | ~ spl9_23
    | spl9_7
    | ~ spl9_6
    | ~ spl9_5
    | ~ spl9_4
    | spl9_50
    | ~ spl9_27
    | ~ spl9_26
    | spl9_2 ),
    inference(avatar_split_clause,[],[f359,f110,f232,f236,f362,f118,f122,f126,f130,f216,f138,f162,f166,f213])).

fof(f359,plain,
    ( ~ r3_waybel_9(sK0,sK1,k1_waybel_9(sK0,sK1))
    | ~ m1_subset_1(k1_waybel_9(sK0,sK1),u1_struct_0(sK0))
    | r3_waybel_9(sK0,sK1,sK3(sK0,sK1))
    | ~ l1_waybel_0(sK1,sK0)
    | ~ v7_waybel_0(sK1)
    | ~ v4_orders_2(sK1)
    | v2_struct_0(sK1)
    | ~ l1_pre_topc(sK0)
    | ~ v1_compts_1(sK0)
    | ~ v8_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0)
    | spl9_2 ),
    inference(resolution,[],[f111,f78])).

fof(f78,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(X2,k10_yellow_6(X0,X1))
      | ~ r3_waybel_9(X0,X1,X2)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | r3_waybel_9(X0,X1,sK3(X0,X1))
      | ~ l1_waybel_0(X1,X0)
      | ~ v7_waybel_0(X1)
      | ~ v4_orders_2(X1)
      | v2_struct_0(X1)
      | ~ l1_pre_topc(X0)
      | ~ v1_compts_1(X0)
      | ~ v8_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f42])).

fof(f355,plain,
    ( ~ spl9_27
    | ~ spl9_26
    | ~ spl9_41
    | spl9_46 ),
    inference(avatar_split_clause,[],[f353,f334,f310,f232,f236])).

fof(f310,plain,
    ( spl9_41
  <=> ! [X0] :
        ( ~ m1_subset_1(X0,u1_struct_0(sK0))
        | ~ r3_waybel_9(sK0,sK1,X0)
        | r1_lattice3(sK0,k2_relset_1(u1_struct_0(sK1),u1_struct_0(sK0),u1_waybel_0(sK0,sK1)),X0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_41])])).

fof(f353,plain,
    ( ~ r3_waybel_9(sK0,sK1,k1_waybel_9(sK0,sK1))
    | ~ m1_subset_1(k1_waybel_9(sK0,sK1),u1_struct_0(sK0))
    | ~ spl9_41
    | spl9_46 ),
    inference(resolution,[],[f335,f311])).

fof(f311,plain,
    ( ! [X0] :
        ( r1_lattice3(sK0,k2_relset_1(u1_struct_0(sK1),u1_struct_0(sK0),u1_waybel_0(sK0,sK1)),X0)
        | ~ r3_waybel_9(sK0,sK1,X0)
        | ~ m1_subset_1(X0,u1_struct_0(sK0)) )
    | ~ spl9_41 ),
    inference(avatar_component_clause,[],[f310])).

fof(f340,plain,
    ( ~ spl9_12
    | ~ spl9_34
    | ~ spl9_27
    | ~ spl9_46
    | spl9_43
    | spl9_42 ),
    inference(avatar_split_clause,[],[f328,f315,f318,f334,f236,f278,f150])).

fof(f328,plain,
    ( r2_yellow_0(sK0,k2_relset_1(u1_struct_0(sK1),u1_struct_0(sK0),u1_waybel_0(sK0,sK1)))
    | ~ r1_lattice3(sK0,k2_relset_1(u1_struct_0(sK1),u1_struct_0(sK0),u1_waybel_0(sK0,sK1)),k1_waybel_9(sK0,sK1))
    | ~ m1_subset_1(k1_waybel_9(sK0,sK1),u1_struct_0(sK0))
    | ~ l1_orders_2(sK0)
    | ~ v5_orders_2(sK0)
    | spl9_42 ),
    inference(resolution,[],[f316,f88])).

fof(f88,plain,(
    ! [X2,X0,X1] :
      ( r1_lattice3(X0,X2,sK5(X0,X1,X2))
      | r2_yellow_0(X0,X2)
      | ~ r1_lattice3(X0,X2,X1)
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | ~ v5_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f46])).

fof(f316,plain,
    ( ~ r1_lattice3(sK0,k2_relset_1(u1_struct_0(sK1),u1_struct_0(sK0),u1_waybel_0(sK0,sK1)),sK5(sK0,k1_waybel_9(sK0,sK1),k2_relset_1(u1_struct_0(sK1),u1_struct_0(sK0),u1_waybel_0(sK0,sK1))))
    | spl9_42 ),
    inference(avatar_component_clause,[],[f315])).

fof(f312,plain,
    ( spl9_41
    | ~ spl9_4
    | ~ spl9_5
    | ~ spl9_6
    | spl9_7
    | ~ spl9_3
    | ~ spl9_40 ),
    inference(avatar_split_clause,[],[f308,f305,f114,f130,f126,f122,f118,f310])).

fof(f305,plain,
    ( spl9_40
  <=> ! [X1,X0] :
        ( ~ r3_waybel_9(sK0,X0,X1)
        | v2_struct_0(X0)
        | ~ v4_orders_2(X0)
        | ~ v7_waybel_0(X0)
        | ~ l1_waybel_0(X0,sK0)
        | ~ m1_subset_1(X1,u1_struct_0(sK0))
        | r1_lattice3(sK0,k2_relset_1(u1_struct_0(X0),u1_struct_0(sK0),u1_waybel_0(sK0,X0)),X1)
        | ~ v11_waybel_0(X0,sK0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_40])])).

fof(f308,plain,
    ( ! [X0] :
        ( v2_struct_0(sK1)
        | ~ v4_orders_2(sK1)
        | ~ v7_waybel_0(sK1)
        | ~ l1_waybel_0(sK1,sK0)
        | ~ m1_subset_1(X0,u1_struct_0(sK0))
        | r1_lattice3(sK0,k2_relset_1(u1_struct_0(sK1),u1_struct_0(sK0),u1_waybel_0(sK0,sK1)),X0)
        | ~ r3_waybel_9(sK0,sK1,X0) )
    | ~ spl9_3
    | ~ spl9_40 ),
    inference(resolution,[],[f306,f115])).

fof(f115,plain,
    ( v11_waybel_0(sK1,sK0)
    | ~ spl9_3 ),
    inference(avatar_component_clause,[],[f114])).

fof(f306,plain,
    ( ! [X0,X1] :
        ( ~ v11_waybel_0(X0,sK0)
        | v2_struct_0(X0)
        | ~ v4_orders_2(X0)
        | ~ v7_waybel_0(X0)
        | ~ l1_waybel_0(X0,sK0)
        | ~ m1_subset_1(X1,u1_struct_0(sK0))
        | r1_lattice3(sK0,k2_relset_1(u1_struct_0(X0),u1_struct_0(sK0),u1_waybel_0(sK0,X0)),X1)
        | ~ r3_waybel_9(sK0,X0,X1) )
    | ~ spl9_40 ),
    inference(avatar_component_clause,[],[f305])).

fof(f307,plain,
    ( ~ spl9_16
    | ~ spl9_15
    | ~ spl9_14
    | ~ spl9_13
    | ~ spl9_12
    | ~ spl9_11
    | ~ spl9_10
    | ~ spl9_9
    | ~ spl9_8
    | spl9_40
    | spl9_39 ),
    inference(avatar_split_clause,[],[f303,f300,f305,f134,f138,f142,f146,f150,f154,f158,f162,f166])).

fof(f300,plain,
    ( spl9_39
  <=> m1_subset_1(sK7(sK0),u1_struct_0(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_39])])).

fof(f303,plain,
    ( ! [X0,X1] :
        ( ~ r3_waybel_9(sK0,X0,X1)
        | ~ v11_waybel_0(X0,sK0)
        | r1_lattice3(sK0,k2_relset_1(u1_struct_0(X0),u1_struct_0(sK0),u1_waybel_0(sK0,X0)),X1)
        | ~ m1_subset_1(X1,u1_struct_0(sK0))
        | ~ l1_waybel_0(X0,sK0)
        | ~ v7_waybel_0(X0)
        | ~ v4_orders_2(X0)
        | v2_struct_0(X0)
        | ~ l1_waybel_9(sK0)
        | ~ v1_compts_1(sK0)
        | ~ v2_lattice3(sK0)
        | ~ v1_lattice3(sK0)
        | ~ v5_orders_2(sK0)
        | ~ v4_orders_2(sK0)
        | ~ v3_orders_2(sK0)
        | ~ v8_pre_topc(sK0)
        | ~ v2_pre_topc(sK0) )
    | spl9_39 ),
    inference(resolution,[],[f301,f104])).

fof(f104,plain,(
    ! [X0,X3,X1] :
      ( m1_subset_1(sK7(X0),u1_struct_0(X0))
      | ~ r3_waybel_9(X0,X1,X3)
      | ~ v11_waybel_0(X1,X0)
      | r1_lattice3(X0,k2_relset_1(u1_struct_0(X1),u1_struct_0(X0),u1_waybel_0(X0,X1)),X3)
      | ~ m1_subset_1(X3,u1_struct_0(X0))
      | ~ l1_waybel_0(X1,X0)
      | ~ v7_waybel_0(X1)
      | ~ v4_orders_2(X1)
      | v2_struct_0(X1)
      | ~ l1_waybel_9(X0)
      | ~ v1_compts_1(X0)
      | ~ v2_lattice3(X0)
      | ~ v1_lattice3(X0)
      | ~ v5_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v3_orders_2(X0)
      | ~ v8_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(duplicate_literal_removal,[],[f99])).

fof(f99,plain,(
    ! [X0,X3,X1] :
      ( r1_lattice3(X0,k2_relset_1(u1_struct_0(X1),u1_struct_0(X0),u1_waybel_0(X0,X1)),X3)
      | ~ r3_waybel_9(X0,X1,X3)
      | ~ v11_waybel_0(X1,X0)
      | m1_subset_1(sK7(X0),u1_struct_0(X0))
      | ~ m1_subset_1(X3,u1_struct_0(X0))
      | ~ m1_subset_1(X3,u1_struct_0(X0))
      | ~ l1_waybel_0(X1,X0)
      | ~ v7_waybel_0(X1)
      | ~ v4_orders_2(X1)
      | v2_struct_0(X1)
      | ~ l1_waybel_9(X0)
      | ~ v1_compts_1(X0)
      | ~ v2_lattice3(X0)
      | ~ v1_lattice3(X0)
      | ~ v5_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v3_orders_2(X0)
      | ~ v8_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(equality_resolution,[],[f92])).

fof(f92,plain,(
    ! [X2,X0,X3,X1] :
      ( r1_lattice3(X0,k2_relset_1(u1_struct_0(X1),u1_struct_0(X0),u1_waybel_0(X0,X1)),X3)
      | ~ r3_waybel_9(X0,X1,X2)
      | ~ v11_waybel_0(X1,X0)
      | m1_subset_1(sK7(X0),u1_struct_0(X0))
      | X2 != X3
      | ~ m1_subset_1(X3,u1_struct_0(X0))
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ l1_waybel_0(X1,X0)
      | ~ v7_waybel_0(X1)
      | ~ v4_orders_2(X1)
      | v2_struct_0(X1)
      | ~ l1_waybel_9(X0)
      | ~ v1_compts_1(X0)
      | ~ v2_lattice3(X0)
      | ~ v1_lattice3(X0)
      | ~ v5_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v3_orders_2(X0)
      | ~ v8_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f50])).

fof(f301,plain,
    ( ~ m1_subset_1(sK7(sK0),u1_struct_0(sK0))
    | spl9_39 ),
    inference(avatar_component_clause,[],[f300])).

fof(f302,plain,
    ( ~ spl9_39
    | spl9_37 ),
    inference(avatar_split_clause,[],[f298,f292,f300])).

fof(f298,plain,
    ( ~ m1_subset_1(sK7(sK0),u1_struct_0(sK0))
    | spl9_37 ),
    inference(resolution,[],[f293,f63])).

fof(f63,plain,(
    ! [X2] :
      ( v5_pre_topc(k4_waybel_1(sK0,X2),sK0,sK0)
      | ~ m1_subset_1(X2,u1_struct_0(sK0)) ) ),
    inference(cnf_transformation,[],[f37])).

fof(f37,plain,
    ( ( ~ r2_hidden(k1_waybel_9(sK0,sK1),k10_yellow_6(sK0,sK1))
      | ~ r2_waybel_9(sK0,sK1) )
    & v11_waybel_0(sK1,sK0)
    & l1_waybel_0(sK1,sK0)
    & v7_waybel_0(sK1)
    & v4_orders_2(sK1)
    & ~ v2_struct_0(sK1)
    & ! [X2] :
        ( v5_pre_topc(k4_waybel_1(sK0,X2),sK0,sK0)
        | ~ m1_subset_1(X2,u1_struct_0(sK0)) )
    & l1_waybel_9(sK0)
    & v1_compts_1(sK0)
    & v2_lattice3(sK0)
    & v1_lattice3(sK0)
    & v5_orders_2(sK0)
    & v4_orders_2(sK0)
    & v3_orders_2(sK0)
    & v8_pre_topc(sK0)
    & v2_pre_topc(sK0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f34,f36,f35])).

fof(f35,plain,
    ( ? [X0] :
        ( ? [X1] :
            ( ( ~ r2_hidden(k1_waybel_9(X0,X1),k10_yellow_6(X0,X1))
              | ~ r2_waybel_9(X0,X1) )
            & v11_waybel_0(X1,X0)
            & l1_waybel_0(X1,X0)
            & v7_waybel_0(X1)
            & v4_orders_2(X1)
            & ~ v2_struct_0(X1) )
        & ! [X2] :
            ( v5_pre_topc(k4_waybel_1(X0,X2),X0,X0)
            | ~ m1_subset_1(X2,u1_struct_0(X0)) )
        & l1_waybel_9(X0)
        & v1_compts_1(X0)
        & v2_lattice3(X0)
        & v1_lattice3(X0)
        & v5_orders_2(X0)
        & v4_orders_2(X0)
        & v3_orders_2(X0)
        & v8_pre_topc(X0)
        & v2_pre_topc(X0) )
   => ( ? [X1] :
          ( ( ~ r2_hidden(k1_waybel_9(sK0,X1),k10_yellow_6(sK0,X1))
            | ~ r2_waybel_9(sK0,X1) )
          & v11_waybel_0(X1,sK0)
          & l1_waybel_0(X1,sK0)
          & v7_waybel_0(X1)
          & v4_orders_2(X1)
          & ~ v2_struct_0(X1) )
      & ! [X2] :
          ( v5_pre_topc(k4_waybel_1(sK0,X2),sK0,sK0)
          | ~ m1_subset_1(X2,u1_struct_0(sK0)) )
      & l1_waybel_9(sK0)
      & v1_compts_1(sK0)
      & v2_lattice3(sK0)
      & v1_lattice3(sK0)
      & v5_orders_2(sK0)
      & v4_orders_2(sK0)
      & v3_orders_2(sK0)
      & v8_pre_topc(sK0)
      & v2_pre_topc(sK0) ) ),
    introduced(choice_axiom,[])).

fof(f36,plain,
    ( ? [X1] :
        ( ( ~ r2_hidden(k1_waybel_9(sK0,X1),k10_yellow_6(sK0,X1))
          | ~ r2_waybel_9(sK0,X1) )
        & v11_waybel_0(X1,sK0)
        & l1_waybel_0(X1,sK0)
        & v7_waybel_0(X1)
        & v4_orders_2(X1)
        & ~ v2_struct_0(X1) )
   => ( ( ~ r2_hidden(k1_waybel_9(sK0,sK1),k10_yellow_6(sK0,sK1))
        | ~ r2_waybel_9(sK0,sK1) )
      & v11_waybel_0(sK1,sK0)
      & l1_waybel_0(sK1,sK0)
      & v7_waybel_0(sK1)
      & v4_orders_2(sK1)
      & ~ v2_struct_0(sK1) ) ),
    introduced(choice_axiom,[])).

fof(f34,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ( ~ r2_hidden(k1_waybel_9(X0,X1),k10_yellow_6(X0,X1))
            | ~ r2_waybel_9(X0,X1) )
          & v11_waybel_0(X1,X0)
          & l1_waybel_0(X1,X0)
          & v7_waybel_0(X1)
          & v4_orders_2(X1)
          & ~ v2_struct_0(X1) )
      & ! [X2] :
          ( v5_pre_topc(k4_waybel_1(X0,X2),X0,X0)
          | ~ m1_subset_1(X2,u1_struct_0(X0)) )
      & l1_waybel_9(X0)
      & v1_compts_1(X0)
      & v2_lattice3(X0)
      & v1_lattice3(X0)
      & v5_orders_2(X0)
      & v4_orders_2(X0)
      & v3_orders_2(X0)
      & v8_pre_topc(X0)
      & v2_pre_topc(X0) ) ),
    inference(rectify,[],[f17])).

fof(f17,plain,(
    ? [X0] :
      ( ? [X2] :
          ( ( ~ r2_hidden(k1_waybel_9(X0,X2),k10_yellow_6(X0,X2))
            | ~ r2_waybel_9(X0,X2) )
          & v11_waybel_0(X2,X0)
          & l1_waybel_0(X2,X0)
          & v7_waybel_0(X2)
          & v4_orders_2(X2)
          & ~ v2_struct_0(X2) )
      & ! [X1] :
          ( v5_pre_topc(k4_waybel_1(X0,X1),X0,X0)
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      & l1_waybel_9(X0)
      & v1_compts_1(X0)
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
      ( ? [X2] :
          ( ( ~ r2_hidden(k1_waybel_9(X0,X2),k10_yellow_6(X0,X2))
            | ~ r2_waybel_9(X0,X2) )
          & v11_waybel_0(X2,X0)
          & l1_waybel_0(X2,X0)
          & v7_waybel_0(X2)
          & v4_orders_2(X2)
          & ~ v2_struct_0(X2) )
      & ! [X1] :
          ( v5_pre_topc(k4_waybel_1(X0,X1),X0,X0)
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      & l1_waybel_9(X0)
      & v1_compts_1(X0)
      & v2_lattice3(X0)
      & v1_lattice3(X0)
      & v5_orders_2(X0)
      & v4_orders_2(X0)
      & v3_orders_2(X0)
      & v8_pre_topc(X0)
      & v2_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f12,plain,(
    ~ ! [X0] :
        ( ( l1_waybel_9(X0)
          & v1_compts_1(X0)
          & v2_lattice3(X0)
          & v1_lattice3(X0)
          & v5_orders_2(X0)
          & v4_orders_2(X0)
          & v3_orders_2(X0)
          & v8_pre_topc(X0)
          & v2_pre_topc(X0) )
       => ( ! [X1] :
              ( m1_subset_1(X1,u1_struct_0(X0))
             => v5_pre_topc(k4_waybel_1(X0,X1),X0,X0) )
         => ! [X2] :
              ( ( l1_waybel_0(X2,X0)
                & v7_waybel_0(X2)
                & v4_orders_2(X2)
                & ~ v2_struct_0(X2) )
             => ( v11_waybel_0(X2,X0)
               => ( r2_hidden(k1_waybel_9(X0,X2),k10_yellow_6(X0,X2))
                  & r2_waybel_9(X0,X2) ) ) ) ) ) ),
    inference(rectify,[],[f11])).

fof(f11,negated_conjecture,(
    ~ ! [X0] :
        ( ( l1_waybel_9(X0)
          & v1_compts_1(X0)
          & v2_lattice3(X0)
          & v1_lattice3(X0)
          & v5_orders_2(X0)
          & v4_orders_2(X0)
          & v3_orders_2(X0)
          & v8_pre_topc(X0)
          & v2_pre_topc(X0) )
       => ( ! [X1] :
              ( m1_subset_1(X1,u1_struct_0(X0))
             => v5_pre_topc(k4_waybel_1(X0,X1),X0,X0) )
         => ! [X1] :
              ( ( l1_waybel_0(X1,X0)
                & v7_waybel_0(X1)
                & v4_orders_2(X1)
                & ~ v2_struct_0(X1) )
             => ( v11_waybel_0(X1,X0)
               => ( r2_hidden(k1_waybel_9(X0,X1),k10_yellow_6(X0,X1))
                  & r2_waybel_9(X0,X1) ) ) ) ) ) ),
    inference(negated_conjecture,[],[f10])).

fof(f10,conjecture,(
    ! [X0] :
      ( ( l1_waybel_9(X0)
        & v1_compts_1(X0)
        & v2_lattice3(X0)
        & v1_lattice3(X0)
        & v5_orders_2(X0)
        & v4_orders_2(X0)
        & v3_orders_2(X0)
        & v8_pre_topc(X0)
        & v2_pre_topc(X0) )
     => ( ! [X1] :
            ( m1_subset_1(X1,u1_struct_0(X0))
           => v5_pre_topc(k4_waybel_1(X0,X1),X0,X0) )
       => ! [X1] :
            ( ( l1_waybel_0(X1,X0)
              & v7_waybel_0(X1)
              & v4_orders_2(X1)
              & ~ v2_struct_0(X1) )
           => ( v11_waybel_0(X1,X0)
             => ( r2_hidden(k1_waybel_9(X0,X1),k10_yellow_6(X0,X1))
                & r2_waybel_9(X0,X1) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t39_waybel_9)).

fof(f293,plain,
    ( ~ v5_pre_topc(k4_waybel_1(sK0,sK7(sK0)),sK0,sK0)
    | spl9_37 ),
    inference(avatar_component_clause,[],[f292])).

fof(f289,plain,
    ( ~ spl9_8
    | spl9_34 ),
    inference(avatar_split_clause,[],[f288,f278,f134])).

fof(f288,plain,
    ( ~ l1_waybel_9(sK0)
    | spl9_34 ),
    inference(resolution,[],[f279,f74])).

fof(f279,plain,
    ( ~ l1_orders_2(sK0)
    | spl9_34 ),
    inference(avatar_component_clause,[],[f278])).

fof(f287,plain,
    ( ~ spl9_12
    | ~ spl9_34
    | ~ spl9_27
    | spl9_36
    | ~ spl9_33 ),
    inference(avatar_split_clause,[],[f276,f269,f285,f236,f278,f150])).

fof(f269,plain,
    ( spl9_33
  <=> ! [X0] :
        ( ~ m1_subset_1(X0,u1_struct_0(sK0))
        | r1_orders_2(sK0,X0,k1_waybel_9(sK0,sK1))
        | ~ r1_lattice3(sK0,k2_relset_1(u1_struct_0(sK1),u1_struct_0(sK0),u1_waybel_0(sK0,sK1)),X0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_33])])).

% (30174)lrs+1011_3:2_aac=none:afp=10000:afq=1.2:amm=off:anc=all:cond=on:fde=none:gs=on:gsem=on:irw=on:lma=on:nm=32:newcnf=on:nwc=3:nicw=on:stl=30:sac=on:sp=reverse_arity:urr=ec_only:updr=off:uhcvi=on_5 on theBenchmark
fof(f276,plain,
    ( ! [X1] :
        ( ~ m1_subset_1(sK5(sK0,k1_waybel_9(sK0,sK1),X1),u1_struct_0(sK0))
        | ~ r1_lattice3(sK0,k2_relset_1(u1_struct_0(sK1),u1_struct_0(sK0),u1_waybel_0(sK0,sK1)),sK5(sK0,k1_waybel_9(sK0,sK1),X1))
        | r2_yellow_0(sK0,X1)
        | ~ r1_lattice3(sK0,X1,k1_waybel_9(sK0,sK1))
        | ~ m1_subset_1(k1_waybel_9(sK0,sK1),u1_struct_0(sK0))
        | ~ l1_orders_2(sK0)
        | ~ v5_orders_2(sK0) )
    | ~ spl9_33 ),
    inference(resolution,[],[f270,f89])).

fof(f89,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_orders_2(X0,sK5(X0,X1,X2),X1)
      | r2_yellow_0(X0,X2)
      | ~ r1_lattice3(X0,X2,X1)
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | ~ v5_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f46])).

fof(f270,plain,
    ( ! [X0] :
        ( r1_orders_2(sK0,X0,k1_waybel_9(sK0,sK1))
        | ~ m1_subset_1(X0,u1_struct_0(sK0))
        | ~ r1_lattice3(sK0,k2_relset_1(u1_struct_0(sK1),u1_struct_0(sK0),u1_waybel_0(sK0,sK1)),X0) )
    | ~ spl9_33 ),
    inference(avatar_component_clause,[],[f269])).

fof(f274,plain,
    ( spl9_22
    | ~ spl9_16
    | ~ spl9_15
    | ~ spl9_9
    | ~ spl9_23
    | spl9_7
    | ~ spl9_6
    | ~ spl9_5
    | ~ spl9_4
    | ~ spl9_27
    | spl9_33
    | ~ spl9_24
    | ~ spl9_30 ),
    inference(avatar_split_clause,[],[f273,f250,f219,f269,f236,f118,f122,f126,f130,f216,f138,f162,f166,f213])).

fof(f219,plain,
    ( spl9_24
  <=> k1_waybel_9(sK0,sK1) = sK4(sK0,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_24])])).

fof(f250,plain,
    ( spl9_30
  <=> ! [X1,X0] :
        ( ~ r1_lattice3(sK0,k2_relset_1(u1_struct_0(sK1),u1_struct_0(sK0),u1_waybel_0(sK0,sK1)),X0)
        | ~ m1_subset_1(X0,u1_struct_0(sK0))
        | ~ r3_waybel_9(sK0,sK1,X1)
        | ~ m1_subset_1(X1,u1_struct_0(sK0))
        | r1_orders_2(sK0,X0,X1) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_30])])).

fof(f273,plain,
    ( ! [X1] :
        ( r1_orders_2(sK0,X1,k1_waybel_9(sK0,sK1))
        | ~ m1_subset_1(k1_waybel_9(sK0,sK1),u1_struct_0(sK0))
        | ~ m1_subset_1(X1,u1_struct_0(sK0))
        | ~ r1_lattice3(sK0,k2_relset_1(u1_struct_0(sK1),u1_struct_0(sK0),u1_waybel_0(sK0,sK1)),X1)
        | ~ l1_waybel_0(sK1,sK0)
        | ~ v7_waybel_0(sK1)
        | ~ v4_orders_2(sK1)
        | v2_struct_0(sK1)
        | ~ l1_pre_topc(sK0)
        | ~ v1_compts_1(sK0)
        | ~ v8_pre_topc(sK0)
        | ~ v2_pre_topc(sK0)
        | v2_struct_0(sK0) )
    | ~ spl9_24
    | ~ spl9_30 ),
    inference(forward_demodulation,[],[f272,f220])).

fof(f220,plain,
    ( k1_waybel_9(sK0,sK1) = sK4(sK0,sK1)
    | ~ spl9_24 ),
    inference(avatar_component_clause,[],[f219])).

fof(f272,plain,
    ( ! [X1] :
        ( ~ m1_subset_1(k1_waybel_9(sK0,sK1),u1_struct_0(sK0))
        | ~ m1_subset_1(X1,u1_struct_0(sK0))
        | ~ r1_lattice3(sK0,k2_relset_1(u1_struct_0(sK1),u1_struct_0(sK0),u1_waybel_0(sK0,sK1)),X1)
        | r1_orders_2(sK0,X1,sK4(sK0,sK1))
        | ~ l1_waybel_0(sK1,sK0)
        | ~ v7_waybel_0(sK1)
        | ~ v4_orders_2(sK1)
        | v2_struct_0(sK1)
        | ~ l1_pre_topc(sK0)
        | ~ v1_compts_1(sK0)
        | ~ v8_pre_topc(sK0)
        | ~ v2_pre_topc(sK0)
        | v2_struct_0(sK0) )
    | ~ spl9_24
    | ~ spl9_30 ),
    inference(forward_demodulation,[],[f266,f220])).

fof(f266,plain,
    ( ! [X1] :
        ( ~ m1_subset_1(X1,u1_struct_0(sK0))
        | ~ r1_lattice3(sK0,k2_relset_1(u1_struct_0(sK1),u1_struct_0(sK0),u1_waybel_0(sK0,sK1)),X1)
        | ~ m1_subset_1(sK4(sK0,sK1),u1_struct_0(sK0))
        | r1_orders_2(sK0,X1,sK4(sK0,sK1))
        | ~ l1_waybel_0(sK1,sK0)
        | ~ v7_waybel_0(sK1)
        | ~ v4_orders_2(sK1)
        | v2_struct_0(sK1)
        | ~ l1_pre_topc(sK0)
        | ~ v1_compts_1(sK0)
        | ~ v8_pre_topc(sK0)
        | ~ v2_pre_topc(sK0)
        | v2_struct_0(sK0) )
    | ~ spl9_30 ),
    inference(resolution,[],[f251,f81])).

fof(f81,plain,(
    ! [X0,X1] :
      ( r3_waybel_9(X0,X1,sK4(X0,X1))
      | ~ l1_waybel_0(X1,X0)
      | ~ v7_waybel_0(X1)
      | ~ v4_orders_2(X1)
      | v2_struct_0(X1)
      | ~ l1_pre_topc(X0)
      | ~ v1_compts_1(X0)
      | ~ v8_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f44])).

fof(f44,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( r3_waybel_9(X0,X1,sK4(X0,X1))
            & m1_subset_1(sK4(X0,X1),u1_struct_0(X0)) )
          | ~ l1_waybel_0(X1,X0)
          | ~ v7_waybel_0(X1)
          | ~ v4_orders_2(X1)
          | v2_struct_0(X1) )
      | ~ l1_pre_topc(X0)
      | ~ v1_compts_1(X0)
      | ~ v8_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4])],[f25,f43])).

fof(f43,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( r3_waybel_9(X0,X1,X2)
          & m1_subset_1(X2,u1_struct_0(X0)) )
     => ( r3_waybel_9(X0,X1,sK4(X0,X1))
        & m1_subset_1(sK4(X0,X1),u1_struct_0(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f25,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ? [X2] :
              ( r3_waybel_9(X0,X1,X2)
              & m1_subset_1(X2,u1_struct_0(X0)) )
          | ~ l1_waybel_0(X1,X0)
          | ~ v7_waybel_0(X1)
          | ~ v4_orders_2(X1)
          | v2_struct_0(X1) )
      | ~ l1_pre_topc(X0)
      | ~ v1_compts_1(X0)
      | ~ v8_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f24])).

fof(f24,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ? [X2] :
              ( r3_waybel_9(X0,X1,X2)
              & m1_subset_1(X2,u1_struct_0(X0)) )
          | ~ l1_waybel_0(X1,X0)
          | ~ v7_waybel_0(X1)
          | ~ v4_orders_2(X1)
          | v2_struct_0(X1) )
      | ~ l1_pre_topc(X0)
      | ~ v1_compts_1(X0)
      | ~ v8_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v1_compts_1(X0)
        & v8_pre_topc(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( ( l1_waybel_0(X1,X0)
            & v7_waybel_0(X1)
            & v4_orders_2(X1)
            & ~ v2_struct_0(X1) )
         => ? [X2] :
              ( r3_waybel_9(X0,X1,X2)
              & m1_subset_1(X2,u1_struct_0(X0)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t30_waybel_9)).

fof(f251,plain,
    ( ! [X0,X1] :
        ( ~ r3_waybel_9(sK0,sK1,X1)
        | ~ m1_subset_1(X0,u1_struct_0(sK0))
        | ~ r1_lattice3(sK0,k2_relset_1(u1_struct_0(sK1),u1_struct_0(sK0),u1_waybel_0(sK0,sK1)),X0)
        | ~ m1_subset_1(X1,u1_struct_0(sK0))
        | r1_orders_2(sK0,X0,X1) )
    | ~ spl9_30 ),
    inference(avatar_component_clause,[],[f250])).

fof(f264,plain,
    ( ~ spl9_4
    | spl9_30
    | ~ spl9_6
    | spl9_7
    | ~ spl9_5
    | ~ spl9_32 ),
    inference(avatar_split_clause,[],[f263,f260,f122,f130,f126,f250,f118])).

fof(f260,plain,
    ( spl9_32
  <=> ! [X1,X0,X2] :
        ( ~ r1_lattice3(sK0,k2_relset_1(u1_struct_0(X0),u1_struct_0(sK0),u1_waybel_0(sK0,X0)),X1)
        | v2_struct_0(X0)
        | ~ v4_orders_2(X0)
        | ~ v7_waybel_0(X0)
        | ~ l1_waybel_0(X0,sK0)
        | ~ m1_subset_1(X2,u1_struct_0(sK0))
        | r1_orders_2(sK0,X1,X2)
        | ~ r3_waybel_9(sK0,X0,X2)
        | ~ m1_subset_1(X1,u1_struct_0(sK0)) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_32])])).

fof(f263,plain,
    ( ! [X0,X1] :
        ( v2_struct_0(sK1)
        | ~ v4_orders_2(sK1)
        | ~ r1_lattice3(sK0,k2_relset_1(u1_struct_0(sK1),u1_struct_0(sK0),u1_waybel_0(sK0,sK1)),X0)
        | ~ l1_waybel_0(sK1,sK0)
        | ~ m1_subset_1(X1,u1_struct_0(sK0))
        | r1_orders_2(sK0,X0,X1)
        | ~ r3_waybel_9(sK0,sK1,X1)
        | ~ m1_subset_1(X0,u1_struct_0(sK0)) )
    | ~ spl9_5
    | ~ spl9_32 ),
    inference(resolution,[],[f261,f123])).

fof(f123,plain,
    ( v7_waybel_0(sK1)
    | ~ spl9_5 ),
    inference(avatar_component_clause,[],[f122])).

fof(f261,plain,
    ( ! [X2,X0,X1] :
        ( ~ v7_waybel_0(X0)
        | v2_struct_0(X0)
        | ~ v4_orders_2(X0)
        | ~ r1_lattice3(sK0,k2_relset_1(u1_struct_0(X0),u1_struct_0(sK0),u1_waybel_0(sK0,X0)),X1)
        | ~ l1_waybel_0(X0,sK0)
        | ~ m1_subset_1(X2,u1_struct_0(sK0))
        | r1_orders_2(sK0,X1,X2)
        | ~ r3_waybel_9(sK0,X0,X2)
        | ~ m1_subset_1(X1,u1_struct_0(sK0)) )
    | ~ spl9_32 ),
    inference(avatar_component_clause,[],[f260])).

fof(f262,plain,
    ( ~ spl9_16
    | ~ spl9_15
    | ~ spl9_14
    | ~ spl9_13
    | ~ spl9_12
    | ~ spl9_11
    | ~ spl9_10
    | ~ spl9_9
    | ~ spl9_8
    | spl9_32
    | spl9_31 ),
    inference(avatar_split_clause,[],[f258,f255,f260,f134,f138,f142,f146,f150,f154,f158,f162,f166])).

fof(f255,plain,
    ( spl9_31
  <=> m1_subset_1(sK8(sK0),u1_struct_0(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_31])])).

fof(f258,plain,
    ( ! [X2,X0,X1] :
        ( ~ r1_lattice3(sK0,k2_relset_1(u1_struct_0(X0),u1_struct_0(sK0),u1_waybel_0(sK0,X0)),X1)
        | ~ m1_subset_1(X1,u1_struct_0(sK0))
        | ~ r3_waybel_9(sK0,X0,X2)
        | r1_orders_2(sK0,X1,X2)
        | ~ m1_subset_1(X2,u1_struct_0(sK0))
        | ~ l1_waybel_0(X0,sK0)
        | ~ v7_waybel_0(X0)
        | ~ v4_orders_2(X0)
        | v2_struct_0(X0)
        | ~ l1_waybel_9(sK0)
        | ~ v1_compts_1(sK0)
        | ~ v2_lattice3(sK0)
        | ~ v1_lattice3(sK0)
        | ~ v5_orders_2(sK0)
        | ~ v4_orders_2(sK0)
        | ~ v3_orders_2(sK0)
        | ~ v8_pre_topc(sK0)
        | ~ v2_pre_topc(sK0) )
    | spl9_31 ),
    inference(resolution,[],[f256,f102])).

fof(f102,plain,(
    ! [X4,X0,X3,X1] :
      ( m1_subset_1(sK8(X0),u1_struct_0(X0))
      | ~ r1_lattice3(X0,k2_relset_1(u1_struct_0(X1),u1_struct_0(X0),u1_waybel_0(X0,X1)),X4)
      | ~ m1_subset_1(X4,u1_struct_0(X0))
      | ~ r3_waybel_9(X0,X1,X3)
      | r1_orders_2(X0,X4,X3)
      | ~ m1_subset_1(X3,u1_struct_0(X0))
      | ~ l1_waybel_0(X1,X0)
      | ~ v7_waybel_0(X1)
      | ~ v4_orders_2(X1)
      | v2_struct_0(X1)
      | ~ l1_waybel_9(X0)
      | ~ v1_compts_1(X0)
      | ~ v2_lattice3(X0)
      | ~ v1_lattice3(X0)
      | ~ v5_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v3_orders_2(X0)
      | ~ v8_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(duplicate_literal_removal,[],[f101])).

fof(f101,plain,(
    ! [X4,X0,X3,X1] :
      ( r1_orders_2(X0,X4,X3)
      | ~ r1_lattice3(X0,k2_relset_1(u1_struct_0(X1),u1_struct_0(X0),u1_waybel_0(X0,X1)),X4)
      | ~ m1_subset_1(X4,u1_struct_0(X0))
      | ~ r3_waybel_9(X0,X1,X3)
      | m1_subset_1(sK8(X0),u1_struct_0(X0))
      | ~ m1_subset_1(X3,u1_struct_0(X0))
      | ~ m1_subset_1(X3,u1_struct_0(X0))
      | ~ l1_waybel_0(X1,X0)
      | ~ v7_waybel_0(X1)
      | ~ v4_orders_2(X1)
      | v2_struct_0(X1)
      | ~ l1_waybel_9(X0)
      | ~ v1_compts_1(X0)
      | ~ v2_lattice3(X0)
      | ~ v1_lattice3(X0)
      | ~ v5_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v3_orders_2(X0)
      | ~ v8_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(equality_resolution,[],[f94])).

fof(f94,plain,(
    ! [X4,X2,X0,X3,X1] :
      ( r1_orders_2(X0,X4,X3)
      | ~ r1_lattice3(X0,k2_relset_1(u1_struct_0(X1),u1_struct_0(X0),u1_waybel_0(X0,X1)),X4)
      | ~ m1_subset_1(X4,u1_struct_0(X0))
      | ~ r3_waybel_9(X0,X1,X2)
      | m1_subset_1(sK8(X0),u1_struct_0(X0))
      | X2 != X3
      | ~ m1_subset_1(X3,u1_struct_0(X0))
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ l1_waybel_0(X1,X0)
      | ~ v7_waybel_0(X1)
      | ~ v4_orders_2(X1)
      | v2_struct_0(X1)
      | ~ l1_waybel_9(X0)
      | ~ v1_compts_1(X0)
      | ~ v2_lattice3(X0)
      | ~ v1_lattice3(X0)
      | ~ v5_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v3_orders_2(X0)
      | ~ v8_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f53])).

fof(f53,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( ! [X4] :
                      ( r1_orders_2(X0,X4,X3)
                      | ~ r1_lattice3(X0,k2_relset_1(u1_struct_0(X1),u1_struct_0(X0),u1_waybel_0(X0,X1)),X4)
                      | ~ m1_subset_1(X4,u1_struct_0(X0)) )
                  | ~ r3_waybel_9(X0,X1,X2)
                  | ( ~ v5_pre_topc(k4_waybel_1(X0,sK8(X0)),X0,X0)
                    & m1_subset_1(sK8(X0),u1_struct_0(X0)) )
                  | X2 != X3
                  | ~ m1_subset_1(X3,u1_struct_0(X0)) )
              | ~ m1_subset_1(X2,u1_struct_0(X0)) )
          | ~ l1_waybel_0(X1,X0)
          | ~ v7_waybel_0(X1)
          | ~ v4_orders_2(X1)
          | v2_struct_0(X1) )
      | ~ l1_waybel_9(X0)
      | ~ v1_compts_1(X0)
      | ~ v2_lattice3(X0)
      | ~ v1_lattice3(X0)
      | ~ v5_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v3_orders_2(X0)
      | ~ v8_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK8])],[f51,f52])).

fof(f52,plain,(
    ! [X0] :
      ( ? [X5] :
          ( ~ v5_pre_topc(k4_waybel_1(X0,X5),X0,X0)
          & m1_subset_1(X5,u1_struct_0(X0)) )
     => ( ~ v5_pre_topc(k4_waybel_1(X0,sK8(X0)),X0,X0)
        & m1_subset_1(sK8(X0),u1_struct_0(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f51,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( ! [X4] :
                      ( r1_orders_2(X0,X4,X3)
                      | ~ r1_lattice3(X0,k2_relset_1(u1_struct_0(X1),u1_struct_0(X0),u1_waybel_0(X0,X1)),X4)
                      | ~ m1_subset_1(X4,u1_struct_0(X0)) )
                  | ~ r3_waybel_9(X0,X1,X2)
                  | ? [X5] :
                      ( ~ v5_pre_topc(k4_waybel_1(X0,X5),X0,X0)
                      & m1_subset_1(X5,u1_struct_0(X0)) )
                  | X2 != X3
                  | ~ m1_subset_1(X3,u1_struct_0(X0)) )
              | ~ m1_subset_1(X2,u1_struct_0(X0)) )
          | ~ l1_waybel_0(X1,X0)
          | ~ v7_waybel_0(X1)
          | ~ v4_orders_2(X1)
          | v2_struct_0(X1) )
      | ~ l1_waybel_9(X0)
      | ~ v1_compts_1(X0)
      | ~ v2_lattice3(X0)
      | ~ v1_lattice3(X0)
      | ~ v5_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v3_orders_2(X0)
      | ~ v8_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(rectify,[],[f33])).

fof(f33,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( ! [X5] :
                      ( r1_orders_2(X0,X5,X3)
                      | ~ r1_lattice3(X0,k2_relset_1(u1_struct_0(X1),u1_struct_0(X0),u1_waybel_0(X0,X1)),X5)
                      | ~ m1_subset_1(X5,u1_struct_0(X0)) )
                  | ~ r3_waybel_9(X0,X1,X2)
                  | ? [X4] :
                      ( ~ v5_pre_topc(k4_waybel_1(X0,X4),X0,X0)
                      & m1_subset_1(X4,u1_struct_0(X0)) )
                  | X2 != X3
                  | ~ m1_subset_1(X3,u1_struct_0(X0)) )
              | ~ m1_subset_1(X2,u1_struct_0(X0)) )
          | ~ l1_waybel_0(X1,X0)
          | ~ v7_waybel_0(X1)
          | ~ v4_orders_2(X1)
          | v2_struct_0(X1) )
      | ~ l1_waybel_9(X0)
      | ~ v1_compts_1(X0)
      | ~ v2_lattice3(X0)
      | ~ v1_lattice3(X0)
      | ~ v5_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v3_orders_2(X0)
      | ~ v8_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(flattening,[],[f32])).

fof(f32,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( ! [X5] :
                      ( r1_orders_2(X0,X5,X3)
                      | ~ r1_lattice3(X0,k2_relset_1(u1_struct_0(X1),u1_struct_0(X0),u1_waybel_0(X0,X1)),X5)
                      | ~ m1_subset_1(X5,u1_struct_0(X0)) )
                  | ~ r3_waybel_9(X0,X1,X2)
                  | ? [X4] :
                      ( ~ v5_pre_topc(k4_waybel_1(X0,X4),X0,X0)
                      & m1_subset_1(X4,u1_struct_0(X0)) )
                  | X2 != X3
                  | ~ m1_subset_1(X3,u1_struct_0(X0)) )
              | ~ m1_subset_1(X2,u1_struct_0(X0)) )
          | ~ l1_waybel_0(X1,X0)
          | ~ v7_waybel_0(X1)
          | ~ v4_orders_2(X1)
          | v2_struct_0(X1) )
      | ~ l1_waybel_9(X0)
      | ~ v1_compts_1(X0)
      | ~ v2_lattice3(X0)
      | ~ v1_lattice3(X0)
      | ~ v5_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v3_orders_2(X0)
      | ~ v8_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f15])).

fof(f15,plain,(
    ! [X0] :
      ( ( l1_waybel_9(X0)
        & v1_compts_1(X0)
        & v2_lattice3(X0)
        & v1_lattice3(X0)
        & v5_orders_2(X0)
        & v4_orders_2(X0)
        & v3_orders_2(X0)
        & v8_pre_topc(X0)
        & v2_pre_topc(X0) )
     => ! [X1] :
          ( ( l1_waybel_0(X1,X0)
            & v7_waybel_0(X1)
            & v4_orders_2(X1)
            & ~ v2_struct_0(X1) )
         => ! [X2] :
              ( m1_subset_1(X2,u1_struct_0(X0))
             => ! [X3] :
                  ( m1_subset_1(X3,u1_struct_0(X0))
                 => ( ( r3_waybel_9(X0,X1,X2)
                      & ! [X4] :
                          ( m1_subset_1(X4,u1_struct_0(X0))
                         => v5_pre_topc(k4_waybel_1(X0,X4),X0,X0) )
                      & X2 = X3 )
                   => ! [X5] :
                        ( m1_subset_1(X5,u1_struct_0(X0))
                       => ( r1_lattice3(X0,k2_relset_1(u1_struct_0(X1),u1_struct_0(X0),u1_waybel_0(X0,X1)),X5)
                         => r1_orders_2(X0,X5,X3) ) ) ) ) ) ) ) ),
    inference(rectify,[],[f6])).

fof(f6,axiom,(
    ! [X0] :
      ( ( l1_waybel_9(X0)
        & v1_compts_1(X0)
        & v2_lattice3(X0)
        & v1_lattice3(X0)
        & v5_orders_2(X0)
        & v4_orders_2(X0)
        & v3_orders_2(X0)
        & v8_pre_topc(X0)
        & v2_pre_topc(X0) )
     => ! [X1] :
          ( ( l1_waybel_0(X1,X0)
            & v7_waybel_0(X1)
            & v4_orders_2(X1)
            & ~ v2_struct_0(X1) )
         => ! [X2] :
              ( m1_subset_1(X2,u1_struct_0(X0))
             => ! [X3] :
                  ( m1_subset_1(X3,u1_struct_0(X0))
                 => ( ( r3_waybel_9(X0,X1,X2)
                      & ! [X4] :
                          ( m1_subset_1(X4,u1_struct_0(X0))
                         => v5_pre_topc(k4_waybel_1(X0,X4),X0,X0) )
                      & X2 = X3 )
                   => ! [X4] :
                        ( m1_subset_1(X4,u1_struct_0(X0))
                       => ( r1_lattice3(X0,k2_relset_1(u1_struct_0(X1),u1_struct_0(X0),u1_waybel_0(X0,X1)),X4)
                         => r1_orders_2(X0,X4,X3) ) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l52_waybel_9)).

fof(f256,plain,
    ( ~ m1_subset_1(sK8(sK0),u1_struct_0(sK0))
    | spl9_31 ),
    inference(avatar_component_clause,[],[f255])).

fof(f257,plain,
    ( ~ spl9_31
    | spl9_29 ),
    inference(avatar_split_clause,[],[f253,f247,f255])).

fof(f247,plain,
    ( spl9_29
  <=> v5_pre_topc(k4_waybel_1(sK0,sK8(sK0)),sK0,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_29])])).

fof(f253,plain,
    ( ~ m1_subset_1(sK8(sK0),u1_struct_0(sK0))
    | spl9_29 ),
    inference(resolution,[],[f248,f63])).

fof(f248,plain,
    ( ~ v5_pre_topc(k4_waybel_1(sK0,sK8(sK0)),sK0,sK0)
    | spl9_29 ),
    inference(avatar_component_clause,[],[f247])).

fof(f252,plain,
    ( ~ spl9_29
    | ~ spl9_4
    | ~ spl9_8
    | spl9_30
    | ~ spl9_10
    | ~ spl9_11
    | ~ spl9_12
    | ~ spl9_13
    | ~ spl9_14
    | ~ spl9_15
    | ~ spl9_16
    | ~ spl9_9
    | ~ spl9_28 ),
    inference(avatar_split_clause,[],[f245,f242,f138,f166,f162,f158,f154,f150,f146,f142,f250,f134,f118,f247])).

fof(f242,plain,
    ( spl9_28
  <=> ! [X1,X0,X2] :
        ( ~ r1_lattice3(X0,k2_relset_1(u1_struct_0(sK1),u1_struct_0(X0),u1_waybel_0(X0,sK1)),X1)
        | ~ v2_pre_topc(X0)
        | ~ v8_pre_topc(X0)
        | ~ v3_orders_2(X0)
        | ~ v4_orders_2(X0)
        | ~ v5_orders_2(X0)
        | ~ v1_lattice3(X0)
        | ~ v2_lattice3(X0)
        | ~ v1_compts_1(X0)
        | ~ l1_waybel_9(X0)
        | r1_orders_2(X0,X1,X2)
        | ~ l1_waybel_0(sK1,X0)
        | ~ m1_subset_1(X2,u1_struct_0(X0))
        | ~ v5_pre_topc(k4_waybel_1(X0,sK8(X0)),X0,X0)
        | ~ r3_waybel_9(X0,sK1,X2)
        | ~ m1_subset_1(X1,u1_struct_0(X0)) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_28])])).

fof(f245,plain,
    ( ! [X0,X1] :
        ( ~ v2_pre_topc(sK0)
        | ~ v8_pre_topc(sK0)
        | ~ v3_orders_2(sK0)
        | ~ v4_orders_2(sK0)
        | ~ v5_orders_2(sK0)
        | ~ v1_lattice3(sK0)
        | ~ v2_lattice3(sK0)
        | ~ r1_lattice3(sK0,k2_relset_1(u1_struct_0(sK1),u1_struct_0(sK0),u1_waybel_0(sK0,sK1)),X0)
        | ~ l1_waybel_9(sK0)
        | r1_orders_2(sK0,X0,X1)
        | ~ l1_waybel_0(sK1,sK0)
        | ~ m1_subset_1(X1,u1_struct_0(sK0))
        | ~ v5_pre_topc(k4_waybel_1(sK0,sK8(sK0)),sK0,sK0)
        | ~ r3_waybel_9(sK0,sK1,X1)
        | ~ m1_subset_1(X0,u1_struct_0(sK0)) )
    | ~ spl9_9
    | ~ spl9_28 ),
    inference(resolution,[],[f243,f139])).

fof(f139,plain,
    ( v1_compts_1(sK0)
    | ~ spl9_9 ),
    inference(avatar_component_clause,[],[f138])).

fof(f243,plain,
    ( ! [X2,X0,X1] :
        ( ~ v1_compts_1(X0)
        | ~ v2_pre_topc(X0)
        | ~ v8_pre_topc(X0)
        | ~ v3_orders_2(X0)
        | ~ v4_orders_2(X0)
        | ~ v5_orders_2(X0)
        | ~ v1_lattice3(X0)
        | ~ v2_lattice3(X0)
        | ~ r1_lattice3(X0,k2_relset_1(u1_struct_0(sK1),u1_struct_0(X0),u1_waybel_0(X0,sK1)),X1)
        | ~ l1_waybel_9(X0)
        | r1_orders_2(X0,X1,X2)
        | ~ l1_waybel_0(sK1,X0)
        | ~ m1_subset_1(X2,u1_struct_0(X0))
        | ~ v5_pre_topc(k4_waybel_1(X0,sK8(X0)),X0,X0)
        | ~ r3_waybel_9(X0,sK1,X2)
        | ~ m1_subset_1(X1,u1_struct_0(X0)) )
    | ~ spl9_28 ),
    inference(avatar_component_clause,[],[f242])).

fof(f244,plain,
    ( spl9_7
    | ~ spl9_6
    | spl9_28
    | ~ spl9_5 ),
    inference(avatar_split_clause,[],[f240,f122,f242,f126,f130])).

fof(f240,plain,
    ( ! [X2,X0,X1] :
        ( ~ r1_lattice3(X0,k2_relset_1(u1_struct_0(sK1),u1_struct_0(X0),u1_waybel_0(X0,sK1)),X1)
        | ~ m1_subset_1(X1,u1_struct_0(X0))
        | ~ r3_waybel_9(X0,sK1,X2)
        | ~ v5_pre_topc(k4_waybel_1(X0,sK8(X0)),X0,X0)
        | ~ m1_subset_1(X2,u1_struct_0(X0))
        | ~ l1_waybel_0(sK1,X0)
        | r1_orders_2(X0,X1,X2)
        | ~ v4_orders_2(sK1)
        | v2_struct_0(sK1)
        | ~ l1_waybel_9(X0)
        | ~ v1_compts_1(X0)
        | ~ v2_lattice3(X0)
        | ~ v1_lattice3(X0)
        | ~ v5_orders_2(X0)
        | ~ v4_orders_2(X0)
        | ~ v3_orders_2(X0)
        | ~ v8_pre_topc(X0)
        | ~ v2_pre_topc(X0) )
    | ~ spl9_5 ),
    inference(resolution,[],[f103,f123])).

fof(f103,plain,(
    ! [X4,X0,X3,X1] :
      ( ~ v7_waybel_0(X1)
      | ~ r1_lattice3(X0,k2_relset_1(u1_struct_0(X1),u1_struct_0(X0),u1_waybel_0(X0,X1)),X4)
      | ~ m1_subset_1(X4,u1_struct_0(X0))
      | ~ r3_waybel_9(X0,X1,X3)
      | ~ v5_pre_topc(k4_waybel_1(X0,sK8(X0)),X0,X0)
      | ~ m1_subset_1(X3,u1_struct_0(X0))
      | ~ l1_waybel_0(X1,X0)
      | r1_orders_2(X0,X4,X3)
      | ~ v4_orders_2(X1)
      | v2_struct_0(X1)
      | ~ l1_waybel_9(X0)
      | ~ v1_compts_1(X0)
      | ~ v2_lattice3(X0)
      | ~ v1_lattice3(X0)
      | ~ v5_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v3_orders_2(X0)
      | ~ v8_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(duplicate_literal_removal,[],[f100])).

fof(f100,plain,(
    ! [X4,X0,X3,X1] :
      ( r1_orders_2(X0,X4,X3)
      | ~ r1_lattice3(X0,k2_relset_1(u1_struct_0(X1),u1_struct_0(X0),u1_waybel_0(X0,X1)),X4)
      | ~ m1_subset_1(X4,u1_struct_0(X0))
      | ~ r3_waybel_9(X0,X1,X3)
      | ~ v5_pre_topc(k4_waybel_1(X0,sK8(X0)),X0,X0)
      | ~ m1_subset_1(X3,u1_struct_0(X0))
      | ~ m1_subset_1(X3,u1_struct_0(X0))
      | ~ l1_waybel_0(X1,X0)
      | ~ v7_waybel_0(X1)
      | ~ v4_orders_2(X1)
      | v2_struct_0(X1)
      | ~ l1_waybel_9(X0)
      | ~ v1_compts_1(X0)
      | ~ v2_lattice3(X0)
      | ~ v1_lattice3(X0)
      | ~ v5_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v3_orders_2(X0)
      | ~ v8_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(equality_resolution,[],[f95])).

fof(f95,plain,(
    ! [X4,X2,X0,X3,X1] :
      ( r1_orders_2(X0,X4,X3)
      | ~ r1_lattice3(X0,k2_relset_1(u1_struct_0(X1),u1_struct_0(X0),u1_waybel_0(X0,X1)),X4)
      | ~ m1_subset_1(X4,u1_struct_0(X0))
      | ~ r3_waybel_9(X0,X1,X2)
      | ~ v5_pre_topc(k4_waybel_1(X0,sK8(X0)),X0,X0)
      | X2 != X3
      | ~ m1_subset_1(X3,u1_struct_0(X0))
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ l1_waybel_0(X1,X0)
      | ~ v7_waybel_0(X1)
      | ~ v4_orders_2(X1)
      | v2_struct_0(X1)
      | ~ l1_waybel_9(X0)
      | ~ v1_compts_1(X0)
      | ~ v2_lattice3(X0)
      | ~ v1_lattice3(X0)
      | ~ v5_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v3_orders_2(X0)
      | ~ v8_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f53])).

fof(f238,plain,
    ( spl9_22
    | ~ spl9_16
    | ~ spl9_15
    | ~ spl9_9
    | ~ spl9_23
    | spl9_7
    | ~ spl9_6
    | ~ spl9_5
    | ~ spl9_4
    | spl9_27
    | ~ spl9_24 ),
    inference(avatar_split_clause,[],[f230,f219,f236,f118,f122,f126,f130,f216,f138,f162,f166,f213])).

fof(f230,plain,
    ( m1_subset_1(k1_waybel_9(sK0,sK1),u1_struct_0(sK0))
    | ~ l1_waybel_0(sK1,sK0)
    | ~ v7_waybel_0(sK1)
    | ~ v4_orders_2(sK1)
    | v2_struct_0(sK1)
    | ~ l1_pre_topc(sK0)
    | ~ v1_compts_1(sK0)
    | ~ v8_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0)
    | ~ spl9_24 ),
    inference(superposition,[],[f80,f220])).

fof(f80,plain,(
    ! [X0,X1] :
      ( m1_subset_1(sK4(X0,X1),u1_struct_0(X0))
      | ~ l1_waybel_0(X1,X0)
      | ~ v7_waybel_0(X1)
      | ~ v4_orders_2(X1)
      | v2_struct_0(X1)
      | ~ l1_pre_topc(X0)
      | ~ v1_compts_1(X0)
      | ~ v8_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f44])).

fof(f234,plain,
    ( spl9_22
    | ~ spl9_16
    | ~ spl9_15
    | ~ spl9_9
    | ~ spl9_23
    | spl9_7
    | ~ spl9_6
    | ~ spl9_5
    | ~ spl9_4
    | spl9_26
    | ~ spl9_24 ),
    inference(avatar_split_clause,[],[f229,f219,f232,f118,f122,f126,f130,f216,f138,f162,f166,f213])).

fof(f229,plain,
    ( r3_waybel_9(sK0,sK1,k1_waybel_9(sK0,sK1))
    | ~ l1_waybel_0(sK1,sK0)
    | ~ v7_waybel_0(sK1)
    | ~ v4_orders_2(sK1)
    | v2_struct_0(sK1)
    | ~ l1_pre_topc(sK0)
    | ~ v1_compts_1(sK0)
    | ~ v8_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0)
    | ~ spl9_24 ),
    inference(superposition,[],[f81,f220])).

fof(f228,plain,
    ( spl9_22
    | ~ spl9_16
    | ~ spl9_15
    | ~ spl9_9
    | ~ spl9_23
    | spl9_7
    | ~ spl9_6
    | ~ spl9_5
    | ~ spl9_4
    | spl9_25 ),
    inference(avatar_split_clause,[],[f227,f222,f118,f122,f126,f130,f216,f138,f162,f166,f213])).

fof(f222,plain,
    ( spl9_25
  <=> m1_subset_1(sK4(sK0,sK1),u1_struct_0(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_25])])).

% (30175)dis+11_2:1_add=large:afp=4000:afq=1.4:amm=sco:anc=none:fsr=off:nm=16:nwc=1:sd=3:ss=axioms:st=1.2:sos=all:urr=ec_only:updr=off_2 on theBenchmark
fof(f227,plain,
    ( ~ l1_waybel_0(sK1,sK0)
    | ~ v7_waybel_0(sK1)
    | ~ v4_orders_2(sK1)
    | v2_struct_0(sK1)
    | ~ l1_pre_topc(sK0)
    | ~ v1_compts_1(sK0)
    | ~ v8_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0)
    | spl9_25 ),
    inference(resolution,[],[f223,f80])).

fof(f223,plain,
    ( ~ m1_subset_1(sK4(sK0,sK1),u1_struct_0(sK0))
    | spl9_25 ),
    inference(avatar_component_clause,[],[f222])).

fof(f226,plain,
    ( ~ spl9_8
    | spl9_23 ),
    inference(avatar_split_clause,[],[f225,f216,f134])).

fof(f225,plain,
    ( ~ l1_waybel_9(sK0)
    | spl9_23 ),
    inference(resolution,[],[f217,f73])).

fof(f73,plain,(
    ! [X0] :
      ( l1_pre_topc(X0)
      | ~ l1_waybel_9(X0) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f217,plain,
    ( ~ l1_pre_topc(sK0)
    | spl9_23 ),
    inference(avatar_component_clause,[],[f216])).

fof(f224,plain,
    ( spl9_22
    | ~ spl9_16
    | ~ spl9_15
    | ~ spl9_9
    | ~ spl9_23
    | spl9_7
    | ~ spl9_6
    | ~ spl9_5
    | ~ spl9_4
    | spl9_24
    | ~ spl9_25
    | ~ spl9_19 ),
    inference(avatar_split_clause,[],[f211,f186,f222,f219,f118,f122,f126,f130,f216,f138,f162,f166,f213])).

fof(f211,plain,
    ( ~ m1_subset_1(sK4(sK0,sK1),u1_struct_0(sK0))
    | k1_waybel_9(sK0,sK1) = sK4(sK0,sK1)
    | ~ l1_waybel_0(sK1,sK0)
    | ~ v7_waybel_0(sK1)
    | ~ v4_orders_2(sK1)
    | v2_struct_0(sK1)
    | ~ l1_pre_topc(sK0)
    | ~ v1_compts_1(sK0)
    | ~ v8_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0)
    | ~ spl9_19 ),
    inference(resolution,[],[f187,f81])).

fof(f210,plain,
    ( ~ spl9_4
    | ~ spl9_5
    | ~ spl9_6
    | spl9_7
    | spl9_19
    | ~ spl9_3
    | ~ spl9_21 ),
    inference(avatar_split_clause,[],[f208,f205,f114,f186,f130,f126,f122,f118])).

fof(f205,plain,
    ( spl9_21
  <=> ! [X1,X0] :
        ( ~ r3_waybel_9(sK0,X0,X1)
        | ~ m1_subset_1(X1,u1_struct_0(sK0))
        | v2_struct_0(X0)
        | ~ v4_orders_2(X0)
        | ~ v7_waybel_0(X0)
        | ~ l1_waybel_0(X0,sK0)
        | k1_waybel_9(sK0,X0) = X1
        | ~ v11_waybel_0(X0,sK0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_21])])).

fof(f208,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(X0,u1_struct_0(sK0))
        | v2_struct_0(sK1)
        | ~ v4_orders_2(sK1)
        | ~ v7_waybel_0(sK1)
        | ~ l1_waybel_0(sK1,sK0)
        | k1_waybel_9(sK0,sK1) = X0
        | ~ r3_waybel_9(sK0,sK1,X0) )
    | ~ spl9_3
    | ~ spl9_21 ),
    inference(resolution,[],[f206,f115])).

fof(f206,plain,
    ( ! [X0,X1] :
        ( ~ v11_waybel_0(X0,sK0)
        | ~ m1_subset_1(X1,u1_struct_0(sK0))
        | v2_struct_0(X0)
        | ~ v4_orders_2(X0)
        | ~ v7_waybel_0(X0)
        | ~ l1_waybel_0(X0,sK0)
        | k1_waybel_9(sK0,X0) = X1
        | ~ r3_waybel_9(sK0,X0,X1) )
    | ~ spl9_21 ),
    inference(avatar_component_clause,[],[f205])).

fof(f207,plain,
    ( ~ spl9_16
    | ~ spl9_15
    | ~ spl9_14
    | ~ spl9_13
    | ~ spl9_12
    | ~ spl9_11
    | ~ spl9_10
    | ~ spl9_9
    | ~ spl9_8
    | spl9_21
    | spl9_20 ),
    inference(avatar_split_clause,[],[f203,f200,f205,f134,f138,f142,f146,f150,f154,f158,f162,f166])).

fof(f200,plain,
    ( spl9_20
  <=> m1_subset_1(sK6(sK0),u1_struct_0(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_20])])).

fof(f203,plain,
    ( ! [X0,X1] :
        ( ~ r3_waybel_9(sK0,X0,X1)
        | ~ v11_waybel_0(X0,sK0)
        | k1_waybel_9(sK0,X0) = X1
        | ~ l1_waybel_0(X0,sK0)
        | ~ v7_waybel_0(X0)
        | ~ v4_orders_2(X0)
        | v2_struct_0(X0)
        | ~ m1_subset_1(X1,u1_struct_0(sK0))
        | ~ l1_waybel_9(sK0)
        | ~ v1_compts_1(sK0)
        | ~ v2_lattice3(sK0)
        | ~ v1_lattice3(sK0)
        | ~ v5_orders_2(sK0)
        | ~ v4_orders_2(sK0)
        | ~ v3_orders_2(sK0)
        | ~ v8_pre_topc(sK0)
        | ~ v2_pre_topc(sK0) )
    | spl9_20 ),
    inference(resolution,[],[f201,f90])).

fof(f90,plain,(
    ! [X2,X0,X1] :
      ( m1_subset_1(sK6(X0),u1_struct_0(X0))
      | ~ r3_waybel_9(X0,X2,X1)
      | ~ v11_waybel_0(X2,X0)
      | k1_waybel_9(X0,X2) = X1
      | ~ l1_waybel_0(X2,X0)
      | ~ v7_waybel_0(X2)
      | ~ v4_orders_2(X2)
      | v2_struct_0(X2)
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_waybel_9(X0)
      | ~ v1_compts_1(X0)
      | ~ v2_lattice3(X0)
      | ~ v1_lattice3(X0)
      | ~ v5_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v3_orders_2(X0)
      | ~ v8_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f48])).

fof(f48,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( k1_waybel_9(X0,X2) = X1
              | ~ r3_waybel_9(X0,X2,X1)
              | ~ v11_waybel_0(X2,X0)
              | ( ~ v5_pre_topc(k4_waybel_1(X0,sK6(X0)),X0,X0)
                & m1_subset_1(sK6(X0),u1_struct_0(X0)) )
              | ~ l1_waybel_0(X2,X0)
              | ~ v7_waybel_0(X2)
              | ~ v4_orders_2(X2)
              | v2_struct_0(X2) )
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l1_waybel_9(X0)
      | ~ v1_compts_1(X0)
      | ~ v2_lattice3(X0)
      | ~ v1_lattice3(X0)
      | ~ v5_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v3_orders_2(X0)
      | ~ v8_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK6])],[f29,f47])).

fof(f47,plain,(
    ! [X0] :
      ( ? [X3] :
          ( ~ v5_pre_topc(k4_waybel_1(X0,X3),X0,X0)
          & m1_subset_1(X3,u1_struct_0(X0)) )
     => ( ~ v5_pre_topc(k4_waybel_1(X0,sK6(X0)),X0,X0)
        & m1_subset_1(sK6(X0),u1_struct_0(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f29,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( k1_waybel_9(X0,X2) = X1
              | ~ r3_waybel_9(X0,X2,X1)
              | ~ v11_waybel_0(X2,X0)
              | ? [X3] :
                  ( ~ v5_pre_topc(k4_waybel_1(X0,X3),X0,X0)
                  & m1_subset_1(X3,u1_struct_0(X0)) )
              | ~ l1_waybel_0(X2,X0)
              | ~ v7_waybel_0(X2)
              | ~ v4_orders_2(X2)
              | v2_struct_0(X2) )
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l1_waybel_9(X0)
      | ~ v1_compts_1(X0)
      | ~ v2_lattice3(X0)
      | ~ v1_lattice3(X0)
      | ~ v5_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v3_orders_2(X0)
      | ~ v8_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(flattening,[],[f28])).

fof(f28,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( k1_waybel_9(X0,X2) = X1
              | ~ r3_waybel_9(X0,X2,X1)
              | ~ v11_waybel_0(X2,X0)
              | ? [X3] :
                  ( ~ v5_pre_topc(k4_waybel_1(X0,X3),X0,X0)
                  & m1_subset_1(X3,u1_struct_0(X0)) )
              | ~ l1_waybel_0(X2,X0)
              | ~ v7_waybel_0(X2)
              | ~ v4_orders_2(X2)
              | v2_struct_0(X2) )
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l1_waybel_9(X0)
      | ~ v1_compts_1(X0)
      | ~ v2_lattice3(X0)
      | ~ v1_lattice3(X0)
      | ~ v5_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v3_orders_2(X0)
      | ~ v8_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0] :
      ( ( l1_waybel_9(X0)
        & v1_compts_1(X0)
        & v2_lattice3(X0)
        & v1_lattice3(X0)
        & v5_orders_2(X0)
        & v4_orders_2(X0)
        & v3_orders_2(X0)
        & v8_pre_topc(X0)
        & v2_pre_topc(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,u1_struct_0(X0))
         => ! [X2] :
              ( ( l1_waybel_0(X2,X0)
                & v7_waybel_0(X2)
                & v4_orders_2(X2)
                & ~ v2_struct_0(X2) )
             => ( ( r3_waybel_9(X0,X2,X1)
                  & v11_waybel_0(X2,X0)
                  & ! [X3] :
                      ( m1_subset_1(X3,u1_struct_0(X0))
                     => v5_pre_topc(k4_waybel_1(X0,X3),X0,X0) ) )
               => k1_waybel_9(X0,X2) = X1 ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t36_waybel_9)).

fof(f201,plain,
    ( ~ m1_subset_1(sK6(sK0),u1_struct_0(sK0))
    | spl9_20 ),
    inference(avatar_component_clause,[],[f200])).

fof(f202,plain,
    ( ~ spl9_20
    | spl9_18 ),
    inference(avatar_split_clause,[],[f198,f182,f200])).

fof(f182,plain,
    ( spl9_18
  <=> v5_pre_topc(k4_waybel_1(sK0,sK6(sK0)),sK0,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_18])])).

fof(f198,plain,
    ( ~ m1_subset_1(sK6(sK0),u1_struct_0(sK0))
    | spl9_18 ),
    inference(resolution,[],[f183,f63])).

fof(f183,plain,
    ( ~ v5_pre_topc(k4_waybel_1(sK0,sK6(sK0)),sK0,sK0)
    | spl9_18 ),
    inference(avatar_component_clause,[],[f182])).

fof(f197,plain,
    ( ~ spl9_18
    | ~ spl9_4
    | spl9_19
    | ~ spl9_8
    | ~ spl9_9
    | ~ spl9_10
    | ~ spl9_11
    | ~ spl9_12
    | ~ spl9_13
    | ~ spl9_14
    | ~ spl9_15
    | ~ spl9_16
    | ~ spl9_3
    | ~ spl9_17 ),
    inference(avatar_split_clause,[],[f180,f177,f114,f166,f162,f158,f154,f150,f146,f142,f138,f134,f186,f118,f182])).

fof(f177,plain,
    ( spl9_17
  <=> ! [X1,X0] :
        ( ~ r3_waybel_9(X0,sK1,X1)
        | ~ v2_pre_topc(X0)
        | ~ v8_pre_topc(X0)
        | ~ v3_orders_2(X0)
        | ~ v4_orders_2(X0)
        | ~ v5_orders_2(X0)
        | ~ v1_lattice3(X0)
        | ~ v2_lattice3(X0)
        | ~ v1_compts_1(X0)
        | ~ l1_waybel_9(X0)
        | ~ m1_subset_1(X1,u1_struct_0(X0))
        | k1_waybel_9(X0,sK1) = X1
        | ~ l1_waybel_0(sK1,X0)
        | ~ v5_pre_topc(k4_waybel_1(X0,sK6(X0)),X0,X0)
        | ~ v11_waybel_0(sK1,X0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_17])])).

fof(f180,plain,
    ( ! [X0] :
        ( ~ v2_pre_topc(sK0)
        | ~ v8_pre_topc(sK0)
        | ~ v3_orders_2(sK0)
        | ~ v4_orders_2(sK0)
        | ~ v5_orders_2(sK0)
        | ~ v1_lattice3(sK0)
        | ~ v2_lattice3(sK0)
        | ~ v1_compts_1(sK0)
        | ~ l1_waybel_9(sK0)
        | ~ m1_subset_1(X0,u1_struct_0(sK0))
        | k1_waybel_9(sK0,sK1) = X0
        | ~ l1_waybel_0(sK1,sK0)
        | ~ v5_pre_topc(k4_waybel_1(sK0,sK6(sK0)),sK0,sK0)
        | ~ r3_waybel_9(sK0,sK1,X0) )
    | ~ spl9_3
    | ~ spl9_17 ),
    inference(resolution,[],[f178,f115])).

fof(f178,plain,
    ( ! [X0,X1] :
        ( ~ v11_waybel_0(sK1,X0)
        | ~ v2_pre_topc(X0)
        | ~ v8_pre_topc(X0)
        | ~ v3_orders_2(X0)
        | ~ v4_orders_2(X0)
        | ~ v5_orders_2(X0)
        | ~ v1_lattice3(X0)
        | ~ v2_lattice3(X0)
        | ~ v1_compts_1(X0)
        | ~ l1_waybel_9(X0)
        | ~ m1_subset_1(X1,u1_struct_0(X0))
        | k1_waybel_9(X0,sK1) = X1
        | ~ l1_waybel_0(sK1,X0)
        | ~ v5_pre_topc(k4_waybel_1(X0,sK6(X0)),X0,X0)
        | ~ r3_waybel_9(X0,sK1,X1) )
    | ~ spl9_17 ),
    inference(avatar_component_clause,[],[f177])).

fof(f179,plain,
    ( spl9_7
    | ~ spl9_6
    | spl9_17
    | ~ spl9_5 ),
    inference(avatar_split_clause,[],[f173,f122,f177,f126,f130])).

fof(f173,plain,
    ( ! [X0,X1] :
        ( ~ r3_waybel_9(X0,sK1,X1)
        | ~ v11_waybel_0(sK1,X0)
        | ~ v5_pre_topc(k4_waybel_1(X0,sK6(X0)),X0,X0)
        | ~ l1_waybel_0(sK1,X0)
        | k1_waybel_9(X0,sK1) = X1
        | ~ v4_orders_2(sK1)
        | v2_struct_0(sK1)
        | ~ m1_subset_1(X1,u1_struct_0(X0))
        | ~ l1_waybel_9(X0)
        | ~ v1_compts_1(X0)
        | ~ v2_lattice3(X0)
        | ~ v1_lattice3(X0)
        | ~ v5_orders_2(X0)
        | ~ v4_orders_2(X0)
        | ~ v3_orders_2(X0)
        | ~ v8_pre_topc(X0)
        | ~ v2_pre_topc(X0) )
    | ~ spl9_5 ),
    inference(resolution,[],[f91,f123])).

fof(f91,plain,(
    ! [X2,X0,X1] :
      ( ~ v7_waybel_0(X2)
      | ~ r3_waybel_9(X0,X2,X1)
      | ~ v11_waybel_0(X2,X0)
      | ~ v5_pre_topc(k4_waybel_1(X0,sK6(X0)),X0,X0)
      | ~ l1_waybel_0(X2,X0)
      | k1_waybel_9(X0,X2) = X1
      | ~ v4_orders_2(X2)
      | v2_struct_0(X2)
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_waybel_9(X0)
      | ~ v1_compts_1(X0)
      | ~ v2_lattice3(X0)
      | ~ v1_lattice3(X0)
      | ~ v5_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v3_orders_2(X0)
      | ~ v8_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f48])).

fof(f168,plain,(
    spl9_16 ),
    inference(avatar_split_clause,[],[f54,f166])).

fof(f54,plain,(
    v2_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f37])).

fof(f164,plain,(
    spl9_15 ),
    inference(avatar_split_clause,[],[f55,f162])).

fof(f55,plain,(
    v8_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f37])).

fof(f160,plain,(
    spl9_14 ),
    inference(avatar_split_clause,[],[f56,f158])).

fof(f56,plain,(
    v3_orders_2(sK0) ),
    inference(cnf_transformation,[],[f37])).

fof(f156,plain,(
    spl9_13 ),
    inference(avatar_split_clause,[],[f57,f154])).

fof(f57,plain,(
    v4_orders_2(sK0) ),
    inference(cnf_transformation,[],[f37])).

fof(f152,plain,(
    spl9_12 ),
    inference(avatar_split_clause,[],[f58,f150])).

fof(f58,plain,(
    v5_orders_2(sK0) ),
    inference(cnf_transformation,[],[f37])).

fof(f148,plain,(
    spl9_11 ),
    inference(avatar_split_clause,[],[f59,f146])).

fof(f59,plain,(
    v1_lattice3(sK0) ),
    inference(cnf_transformation,[],[f37])).

fof(f144,plain,(
    spl9_10 ),
    inference(avatar_split_clause,[],[f60,f142])).

fof(f60,plain,(
    v2_lattice3(sK0) ),
    inference(cnf_transformation,[],[f37])).

fof(f140,plain,(
    spl9_9 ),
    inference(avatar_split_clause,[],[f61,f138])).

fof(f61,plain,(
    v1_compts_1(sK0) ),
    inference(cnf_transformation,[],[f37])).

fof(f136,plain,(
    spl9_8 ),
    inference(avatar_split_clause,[],[f62,f134])).

fof(f62,plain,(
    l1_waybel_9(sK0) ),
    inference(cnf_transformation,[],[f37])).

fof(f132,plain,(
    ~ spl9_7 ),
    inference(avatar_split_clause,[],[f64,f130])).

fof(f64,plain,(
    ~ v2_struct_0(sK1) ),
    inference(cnf_transformation,[],[f37])).

fof(f128,plain,(
    spl9_6 ),
    inference(avatar_split_clause,[],[f65,f126])).

fof(f65,plain,(
    v4_orders_2(sK1) ),
    inference(cnf_transformation,[],[f37])).

fof(f124,plain,(
    spl9_5 ),
    inference(avatar_split_clause,[],[f66,f122])).

fof(f66,plain,(
    v7_waybel_0(sK1) ),
    inference(cnf_transformation,[],[f37])).

fof(f120,plain,(
    spl9_4 ),
    inference(avatar_split_clause,[],[f67,f118])).

fof(f67,plain,(
    l1_waybel_0(sK1,sK0) ),
    inference(cnf_transformation,[],[f37])).

fof(f116,plain,(
    spl9_3 ),
    inference(avatar_split_clause,[],[f68,f114])).

fof(f68,plain,(
    v11_waybel_0(sK1,sK0) ),
    inference(cnf_transformation,[],[f37])).

fof(f112,plain,
    ( ~ spl9_1
    | ~ spl9_2 ),
    inference(avatar_split_clause,[],[f69,f110,f107])).

fof(f69,plain,
    ( ~ r2_hidden(k1_waybel_9(sK0,sK1),k10_yellow_6(sK0,sK1))
    | ~ r2_waybel_9(sK0,sK1) ),
    inference(cnf_transformation,[],[f37])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : run_vampire %s %d
% 0.14/0.35  % Computer   : n005.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % WCLimit    : 600
% 0.14/0.35  % DateTime   : Tue Dec  1 20:46:17 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.22/0.47  % (30180)lrs+11_1024_afr=on:afp=40000:afq=2.0:anc=none:br=off:ep=RSTC:gs=on:nm=16:nwc=1:stl=30:sp=occurrence:urr=on_129 on theBenchmark
% 0.22/0.48  % (30171)lrs+1011_10_aac=none:acc=model:add=large:afp=40000:afq=2.0:anc=none:bd=off:bsr=on:fsr=off:gs=on:gsem=off:irw=on:lcm=reverse:lwlo=on:nm=64:nwc=3:nicw=on:stl=30_38 on theBenchmark
% 0.22/0.48  % (30169)lrs+1011_3:1_av=off:cond=on:irw=on:lma=on:nm=16:nwc=1:stl=30:sos=all:updr=off_11 on theBenchmark
% 0.22/0.48  % (30180)Refutation not found, incomplete strategy% (30180)------------------------------
% 0.22/0.48  % (30180)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.49  % (30180)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.49  
% 0.22/0.49  % (30180)Memory used [KB]: 10746
% 0.22/0.49  % (30180)Time elapsed: 0.014 s
% 0.22/0.49  % (30180)------------------------------
% 0.22/0.49  % (30180)------------------------------
% 0.22/0.49  % (30167)lrs+1010_2:1_aac=none:afr=on:afp=10000:afq=1.4:amm=sco:anc=none:gs=on:gsem=off:irw=on:nm=16:nwc=3:stl=30_7 on theBenchmark
% 0.22/0.49  % (30171)Refutation found. Thanks to Tanya!
% 0.22/0.49  % SZS status Theorem for theBenchmark
% 0.22/0.49  % SZS output start Proof for theBenchmark
% 0.22/0.49  fof(f435,plain,(
% 0.22/0.49    $false),
% 0.22/0.49    inference(avatar_sat_refutation,[],[f112,f116,f120,f124,f128,f132,f136,f140,f144,f148,f152,f156,f160,f164,f168,f179,f197,f202,f207,f210,f224,f226,f228,f234,f238,f244,f252,f257,f262,f264,f274,f287,f289,f302,f307,f312,f340,f355,f364,f368,f370,f383,f396,f401,f404,f414,f415,f416,f418,f427,f434])).
% 0.22/0.49  fof(f434,plain,(
% 0.22/0.49    ~spl9_16 | ~spl9_15 | ~spl9_14 | ~spl9_13 | ~spl9_12 | ~spl9_11 | ~spl9_10 | ~spl9_9 | ~spl9_8 | spl9_7 | ~spl9_6 | ~spl9_5 | ~spl9_4 | ~spl9_27 | ~spl9_37 | ~spl9_3 | ~spl9_26 | spl9_46),
% 0.22/0.49    inference(avatar_split_clause,[],[f432,f334,f232,f114,f292,f236,f118,f122,f126,f130,f134,f138,f142,f146,f150,f154,f158,f162,f166])).
% 0.22/0.49  fof(f166,plain,(
% 0.22/0.49    spl9_16 <=> v2_pre_topc(sK0)),
% 0.22/0.49    introduced(avatar_definition,[new_symbols(naming,[spl9_16])])).
% 0.22/0.49  fof(f162,plain,(
% 0.22/0.49    spl9_15 <=> v8_pre_topc(sK0)),
% 0.22/0.49    introduced(avatar_definition,[new_symbols(naming,[spl9_15])])).
% 0.22/0.49  fof(f158,plain,(
% 0.22/0.49    spl9_14 <=> v3_orders_2(sK0)),
% 0.22/0.49    introduced(avatar_definition,[new_symbols(naming,[spl9_14])])).
% 0.22/0.49  fof(f154,plain,(
% 0.22/0.49    spl9_13 <=> v4_orders_2(sK0)),
% 0.22/0.49    introduced(avatar_definition,[new_symbols(naming,[spl9_13])])).
% 0.22/0.49  fof(f150,plain,(
% 0.22/0.49    spl9_12 <=> v5_orders_2(sK0)),
% 0.22/0.49    introduced(avatar_definition,[new_symbols(naming,[spl9_12])])).
% 0.22/0.49  fof(f146,plain,(
% 0.22/0.49    spl9_11 <=> v1_lattice3(sK0)),
% 0.22/0.49    introduced(avatar_definition,[new_symbols(naming,[spl9_11])])).
% 0.22/0.49  fof(f142,plain,(
% 0.22/0.49    spl9_10 <=> v2_lattice3(sK0)),
% 0.22/0.49    introduced(avatar_definition,[new_symbols(naming,[spl9_10])])).
% 0.22/0.49  fof(f138,plain,(
% 0.22/0.49    spl9_9 <=> v1_compts_1(sK0)),
% 0.22/0.49    introduced(avatar_definition,[new_symbols(naming,[spl9_9])])).
% 0.22/0.49  fof(f134,plain,(
% 0.22/0.49    spl9_8 <=> l1_waybel_9(sK0)),
% 0.22/0.49    introduced(avatar_definition,[new_symbols(naming,[spl9_8])])).
% 0.22/0.49  fof(f130,plain,(
% 0.22/0.49    spl9_7 <=> v2_struct_0(sK1)),
% 0.22/0.49    introduced(avatar_definition,[new_symbols(naming,[spl9_7])])).
% 0.22/0.49  fof(f126,plain,(
% 0.22/0.49    spl9_6 <=> v4_orders_2(sK1)),
% 0.22/0.49    introduced(avatar_definition,[new_symbols(naming,[spl9_6])])).
% 0.22/0.49  fof(f122,plain,(
% 0.22/0.49    spl9_5 <=> v7_waybel_0(sK1)),
% 0.22/0.49    introduced(avatar_definition,[new_symbols(naming,[spl9_5])])).
% 0.22/0.49  fof(f118,plain,(
% 0.22/0.49    spl9_4 <=> l1_waybel_0(sK1,sK0)),
% 0.22/0.49    introduced(avatar_definition,[new_symbols(naming,[spl9_4])])).
% 0.22/0.49  fof(f236,plain,(
% 0.22/0.49    spl9_27 <=> m1_subset_1(k1_waybel_9(sK0,sK1),u1_struct_0(sK0))),
% 0.22/0.49    introduced(avatar_definition,[new_symbols(naming,[spl9_27])])).
% 0.22/0.49  fof(f292,plain,(
% 0.22/0.49    spl9_37 <=> v5_pre_topc(k4_waybel_1(sK0,sK7(sK0)),sK0,sK0)),
% 0.22/0.49    introduced(avatar_definition,[new_symbols(naming,[spl9_37])])).
% 0.22/0.49  fof(f114,plain,(
% 0.22/0.49    spl9_3 <=> v11_waybel_0(sK1,sK0)),
% 0.22/0.49    introduced(avatar_definition,[new_symbols(naming,[spl9_3])])).
% 0.22/0.49  fof(f232,plain,(
% 0.22/0.49    spl9_26 <=> r3_waybel_9(sK0,sK1,k1_waybel_9(sK0,sK1))),
% 0.22/0.49    introduced(avatar_definition,[new_symbols(naming,[spl9_26])])).
% 0.22/0.49  fof(f334,plain,(
% 0.22/0.49    spl9_46 <=> r1_lattice3(sK0,k2_relset_1(u1_struct_0(sK1),u1_struct_0(sK0),u1_waybel_0(sK0,sK1)),k1_waybel_9(sK0,sK1))),
% 0.22/0.49    introduced(avatar_definition,[new_symbols(naming,[spl9_46])])).
% 0.22/0.49  fof(f432,plain,(
% 0.22/0.49    ~r3_waybel_9(sK0,sK1,k1_waybel_9(sK0,sK1)) | ~v11_waybel_0(sK1,sK0) | ~v5_pre_topc(k4_waybel_1(sK0,sK7(sK0)),sK0,sK0) | ~m1_subset_1(k1_waybel_9(sK0,sK1),u1_struct_0(sK0)) | ~l1_waybel_0(sK1,sK0) | ~v7_waybel_0(sK1) | ~v4_orders_2(sK1) | v2_struct_0(sK1) | ~l1_waybel_9(sK0) | ~v1_compts_1(sK0) | ~v2_lattice3(sK0) | ~v1_lattice3(sK0) | ~v5_orders_2(sK0) | ~v4_orders_2(sK0) | ~v3_orders_2(sK0) | ~v8_pre_topc(sK0) | ~v2_pre_topc(sK0) | spl9_46),
% 0.22/0.49    inference(resolution,[],[f335,f105])).
% 0.22/0.49  fof(f105,plain,(
% 0.22/0.49    ( ! [X0,X3,X1] : (r1_lattice3(X0,k2_relset_1(u1_struct_0(X1),u1_struct_0(X0),u1_waybel_0(X0,X1)),X3) | ~r3_waybel_9(X0,X1,X3) | ~v11_waybel_0(X1,X0) | ~v5_pre_topc(k4_waybel_1(X0,sK7(X0)),X0,X0) | ~m1_subset_1(X3,u1_struct_0(X0)) | ~l1_waybel_0(X1,X0) | ~v7_waybel_0(X1) | ~v4_orders_2(X1) | v2_struct_0(X1) | ~l1_waybel_9(X0) | ~v1_compts_1(X0) | ~v2_lattice3(X0) | ~v1_lattice3(X0) | ~v5_orders_2(X0) | ~v4_orders_2(X0) | ~v3_orders_2(X0) | ~v8_pre_topc(X0) | ~v2_pre_topc(X0)) )),
% 0.22/0.49    inference(duplicate_literal_removal,[],[f98])).
% 0.22/0.49  fof(f98,plain,(
% 0.22/0.49    ( ! [X0,X3,X1] : (r1_lattice3(X0,k2_relset_1(u1_struct_0(X1),u1_struct_0(X0),u1_waybel_0(X0,X1)),X3) | ~r3_waybel_9(X0,X1,X3) | ~v11_waybel_0(X1,X0) | ~v5_pre_topc(k4_waybel_1(X0,sK7(X0)),X0,X0) | ~m1_subset_1(X3,u1_struct_0(X0)) | ~m1_subset_1(X3,u1_struct_0(X0)) | ~l1_waybel_0(X1,X0) | ~v7_waybel_0(X1) | ~v4_orders_2(X1) | v2_struct_0(X1) | ~l1_waybel_9(X0) | ~v1_compts_1(X0) | ~v2_lattice3(X0) | ~v1_lattice3(X0) | ~v5_orders_2(X0) | ~v4_orders_2(X0) | ~v3_orders_2(X0) | ~v8_pre_topc(X0) | ~v2_pre_topc(X0)) )),
% 0.22/0.49    inference(equality_resolution,[],[f93])).
% 0.22/0.49  fof(f93,plain,(
% 0.22/0.49    ( ! [X2,X0,X3,X1] : (r1_lattice3(X0,k2_relset_1(u1_struct_0(X1),u1_struct_0(X0),u1_waybel_0(X0,X1)),X3) | ~r3_waybel_9(X0,X1,X2) | ~v11_waybel_0(X1,X0) | ~v5_pre_topc(k4_waybel_1(X0,sK7(X0)),X0,X0) | X2 != X3 | ~m1_subset_1(X3,u1_struct_0(X0)) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~l1_waybel_0(X1,X0) | ~v7_waybel_0(X1) | ~v4_orders_2(X1) | v2_struct_0(X1) | ~l1_waybel_9(X0) | ~v1_compts_1(X0) | ~v2_lattice3(X0) | ~v1_lattice3(X0) | ~v5_orders_2(X0) | ~v4_orders_2(X0) | ~v3_orders_2(X0) | ~v8_pre_topc(X0) | ~v2_pre_topc(X0)) )),
% 0.22/0.49    inference(cnf_transformation,[],[f50])).
% 0.22/0.49  fof(f50,plain,(
% 0.22/0.49    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (r1_lattice3(X0,k2_relset_1(u1_struct_0(X1),u1_struct_0(X0),u1_waybel_0(X0,X1)),X3) | ~r3_waybel_9(X0,X1,X2) | ~v11_waybel_0(X1,X0) | (~v5_pre_topc(k4_waybel_1(X0,sK7(X0)),X0,X0) & m1_subset_1(sK7(X0),u1_struct_0(X0))) | X2 != X3 | ~m1_subset_1(X3,u1_struct_0(X0))) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~l1_waybel_0(X1,X0) | ~v7_waybel_0(X1) | ~v4_orders_2(X1) | v2_struct_0(X1)) | ~l1_waybel_9(X0) | ~v1_compts_1(X0) | ~v2_lattice3(X0) | ~v1_lattice3(X0) | ~v5_orders_2(X0) | ~v4_orders_2(X0) | ~v3_orders_2(X0) | ~v8_pre_topc(X0) | ~v2_pre_topc(X0))),
% 0.22/0.49    inference(skolemisation,[status(esa),new_symbols(skolem,[sK7])],[f31,f49])).
% 0.22/0.49  fof(f49,plain,(
% 0.22/0.49    ! [X0] : (? [X4] : (~v5_pre_topc(k4_waybel_1(X0,X4),X0,X0) & m1_subset_1(X4,u1_struct_0(X0))) => (~v5_pre_topc(k4_waybel_1(X0,sK7(X0)),X0,X0) & m1_subset_1(sK7(X0),u1_struct_0(X0))))),
% 0.22/0.49    introduced(choice_axiom,[])).
% 0.22/0.49  fof(f31,plain,(
% 0.22/0.49    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (r1_lattice3(X0,k2_relset_1(u1_struct_0(X1),u1_struct_0(X0),u1_waybel_0(X0,X1)),X3) | ~r3_waybel_9(X0,X1,X2) | ~v11_waybel_0(X1,X0) | ? [X4] : (~v5_pre_topc(k4_waybel_1(X0,X4),X0,X0) & m1_subset_1(X4,u1_struct_0(X0))) | X2 != X3 | ~m1_subset_1(X3,u1_struct_0(X0))) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~l1_waybel_0(X1,X0) | ~v7_waybel_0(X1) | ~v4_orders_2(X1) | v2_struct_0(X1)) | ~l1_waybel_9(X0) | ~v1_compts_1(X0) | ~v2_lattice3(X0) | ~v1_lattice3(X0) | ~v5_orders_2(X0) | ~v4_orders_2(X0) | ~v3_orders_2(X0) | ~v8_pre_topc(X0) | ~v2_pre_topc(X0))),
% 0.22/0.49    inference(flattening,[],[f30])).
% 0.22/0.49  fof(f30,plain,(
% 0.22/0.49    ! [X0] : (! [X1] : (! [X2] : (! [X3] : ((r1_lattice3(X0,k2_relset_1(u1_struct_0(X1),u1_struct_0(X0),u1_waybel_0(X0,X1)),X3) | (~r3_waybel_9(X0,X1,X2) | ~v11_waybel_0(X1,X0) | ? [X4] : (~v5_pre_topc(k4_waybel_1(X0,X4),X0,X0) & m1_subset_1(X4,u1_struct_0(X0))) | X2 != X3)) | ~m1_subset_1(X3,u1_struct_0(X0))) | ~m1_subset_1(X2,u1_struct_0(X0))) | (~l1_waybel_0(X1,X0) | ~v7_waybel_0(X1) | ~v4_orders_2(X1) | v2_struct_0(X1))) | (~l1_waybel_9(X0) | ~v1_compts_1(X0) | ~v2_lattice3(X0) | ~v1_lattice3(X0) | ~v5_orders_2(X0) | ~v4_orders_2(X0) | ~v3_orders_2(X0) | ~v8_pre_topc(X0) | ~v2_pre_topc(X0)))),
% 0.22/0.49    inference(ennf_transformation,[],[f5])).
% 0.22/0.49  fof(f5,axiom,(
% 0.22/0.49    ! [X0] : ((l1_waybel_9(X0) & v1_compts_1(X0) & v2_lattice3(X0) & v1_lattice3(X0) & v5_orders_2(X0) & v4_orders_2(X0) & v3_orders_2(X0) & v8_pre_topc(X0) & v2_pre_topc(X0)) => ! [X1] : ((l1_waybel_0(X1,X0) & v7_waybel_0(X1) & v4_orders_2(X1) & ~v2_struct_0(X1)) => ! [X2] : (m1_subset_1(X2,u1_struct_0(X0)) => ! [X3] : (m1_subset_1(X3,u1_struct_0(X0)) => ((r3_waybel_9(X0,X1,X2) & v11_waybel_0(X1,X0) & ! [X4] : (m1_subset_1(X4,u1_struct_0(X0)) => v5_pre_topc(k4_waybel_1(X0,X4),X0,X0)) & X2 = X3) => r1_lattice3(X0,k2_relset_1(u1_struct_0(X1),u1_struct_0(X0),u1_waybel_0(X0,X1)),X3))))))),
% 0.22/0.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l51_waybel_9)).
% 0.22/0.49  fof(f335,plain,(
% 0.22/0.49    ~r1_lattice3(sK0,k2_relset_1(u1_struct_0(sK1),u1_struct_0(sK0),u1_waybel_0(sK0,sK1)),k1_waybel_9(sK0,sK1)) | spl9_46),
% 0.22/0.49    inference(avatar_component_clause,[],[f334])).
% 0.22/0.49  fof(f427,plain,(
% 0.22/0.49    spl9_22 | ~spl9_16 | ~spl9_15 | ~spl9_9 | ~spl9_23 | spl9_7 | ~spl9_6 | ~spl9_5 | ~spl9_4 | spl9_58 | ~spl9_54 | ~spl9_57),
% 0.22/0.49    inference(avatar_split_clause,[],[f426,f394,f381,f399,f118,f122,f126,f130,f216,f138,f162,f166,f213])).
% 0.22/0.49  fof(f213,plain,(
% 0.22/0.49    spl9_22 <=> v2_struct_0(sK0)),
% 0.22/0.49    introduced(avatar_definition,[new_symbols(naming,[spl9_22])])).
% 0.22/0.49  fof(f216,plain,(
% 0.22/0.49    spl9_23 <=> l1_pre_topc(sK0)),
% 0.22/0.49    introduced(avatar_definition,[new_symbols(naming,[spl9_23])])).
% 0.22/0.49  fof(f399,plain,(
% 0.22/0.49    spl9_58 <=> ! [X0] : (~r3_waybel_9(sK0,sK1,X0) | r2_hidden(X0,k10_yellow_6(sK0,sK1)) | ~m1_subset_1(X0,u1_struct_0(sK0)))),
% 0.22/0.49    introduced(avatar_definition,[new_symbols(naming,[spl9_58])])).
% 0.22/0.49  fof(f381,plain,(
% 0.22/0.49    spl9_54 <=> k1_waybel_9(sK0,sK1) = sK3(sK0,sK1)),
% 0.22/0.49    introduced(avatar_definition,[new_symbols(naming,[spl9_54])])).
% 0.22/0.49  fof(f394,plain,(
% 0.22/0.49    spl9_57 <=> k1_waybel_9(sK0,sK1) = sK2(sK0,sK1)),
% 0.22/0.49    introduced(avatar_definition,[new_symbols(naming,[spl9_57])])).
% 0.22/0.49  fof(f426,plain,(
% 0.22/0.49    ( ! [X0] : (~r3_waybel_9(sK0,sK1,X0) | ~m1_subset_1(X0,u1_struct_0(sK0)) | r2_hidden(X0,k10_yellow_6(sK0,sK1)) | ~l1_waybel_0(sK1,sK0) | ~v7_waybel_0(sK1) | ~v4_orders_2(sK1) | v2_struct_0(sK1) | ~l1_pre_topc(sK0) | ~v1_compts_1(sK0) | ~v8_pre_topc(sK0) | ~v2_pre_topc(sK0) | v2_struct_0(sK0)) ) | (~spl9_54 | ~spl9_57)),
% 0.22/0.49    inference(trivial_inequality_removal,[],[f425])).
% 0.22/0.49  fof(f425,plain,(
% 0.22/0.49    ( ! [X0] : (k1_waybel_9(sK0,sK1) != k1_waybel_9(sK0,sK1) | ~r3_waybel_9(sK0,sK1,X0) | ~m1_subset_1(X0,u1_struct_0(sK0)) | r2_hidden(X0,k10_yellow_6(sK0,sK1)) | ~l1_waybel_0(sK1,sK0) | ~v7_waybel_0(sK1) | ~v4_orders_2(sK1) | v2_struct_0(sK1) | ~l1_pre_topc(sK0) | ~v1_compts_1(sK0) | ~v8_pre_topc(sK0) | ~v2_pre_topc(sK0) | v2_struct_0(sK0)) ) | (~spl9_54 | ~spl9_57)),
% 0.22/0.49    inference(forward_demodulation,[],[f423,f395])).
% 0.22/0.49  fof(f395,plain,(
% 0.22/0.49    k1_waybel_9(sK0,sK1) = sK2(sK0,sK1) | ~spl9_57),
% 0.22/0.49    inference(avatar_component_clause,[],[f394])).
% 0.22/0.49  fof(f423,plain,(
% 0.22/0.49    ( ! [X0] : (k1_waybel_9(sK0,sK1) != sK2(sK0,sK1) | ~r3_waybel_9(sK0,sK1,X0) | ~m1_subset_1(X0,u1_struct_0(sK0)) | r2_hidden(X0,k10_yellow_6(sK0,sK1)) | ~l1_waybel_0(sK1,sK0) | ~v7_waybel_0(sK1) | ~v4_orders_2(sK1) | v2_struct_0(sK1) | ~l1_pre_topc(sK0) | ~v1_compts_1(sK0) | ~v8_pre_topc(sK0) | ~v2_pre_topc(sK0) | v2_struct_0(sK0)) ) | ~spl9_54),
% 0.22/0.49    inference(superposition,[],[f79,f382])).
% 0.22/0.49  fof(f382,plain,(
% 0.22/0.49    k1_waybel_9(sK0,sK1) = sK3(sK0,sK1) | ~spl9_54),
% 0.22/0.49    inference(avatar_component_clause,[],[f381])).
% 0.22/0.49  fof(f79,plain,(
% 0.22/0.49    ( ! [X2,X0,X1] : (sK2(X0,X1) != sK3(X0,X1) | ~r3_waybel_9(X0,X1,X2) | ~m1_subset_1(X2,u1_struct_0(X0)) | r2_hidden(X2,k10_yellow_6(X0,X1)) | ~l1_waybel_0(X1,X0) | ~v7_waybel_0(X1) | ~v4_orders_2(X1) | v2_struct_0(X1) | ~l1_pre_topc(X0) | ~v1_compts_1(X0) | ~v8_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 0.22/0.49    inference(cnf_transformation,[],[f42])).
% 0.22/0.49  fof(f42,plain,(
% 0.22/0.49    ! [X0] : (! [X1] : (! [X2] : (r2_hidden(X2,k10_yellow_6(X0,X1)) | ~r3_waybel_9(X0,X1,X2) | ~m1_subset_1(X2,u1_struct_0(X0))) | ((sK2(X0,X1) != sK3(X0,X1) & r3_waybel_9(X0,X1,sK3(X0,X1)) & r3_waybel_9(X0,X1,sK2(X0,X1)) & m1_subset_1(sK3(X0,X1),u1_struct_0(X0))) & m1_subset_1(sK2(X0,X1),u1_struct_0(X0))) | ~l1_waybel_0(X1,X0) | ~v7_waybel_0(X1) | ~v4_orders_2(X1) | v2_struct_0(X1)) | ~l1_pre_topc(X0) | ~v1_compts_1(X0) | ~v8_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 0.22/0.49    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2,sK3])],[f39,f41,f40])).
% 0.22/0.49  fof(f40,plain,(
% 0.22/0.49    ! [X1,X0] : (? [X3] : (? [X4] : (X3 != X4 & r3_waybel_9(X0,X1,X4) & r3_waybel_9(X0,X1,X3) & m1_subset_1(X4,u1_struct_0(X0))) & m1_subset_1(X3,u1_struct_0(X0))) => (? [X4] : (sK2(X0,X1) != X4 & r3_waybel_9(X0,X1,X4) & r3_waybel_9(X0,X1,sK2(X0,X1)) & m1_subset_1(X4,u1_struct_0(X0))) & m1_subset_1(sK2(X0,X1),u1_struct_0(X0))))),
% 0.22/0.49    introduced(choice_axiom,[])).
% 0.22/0.49  fof(f41,plain,(
% 0.22/0.49    ! [X1,X0] : (? [X4] : (sK2(X0,X1) != X4 & r3_waybel_9(X0,X1,X4) & r3_waybel_9(X0,X1,sK2(X0,X1)) & m1_subset_1(X4,u1_struct_0(X0))) => (sK2(X0,X1) != sK3(X0,X1) & r3_waybel_9(X0,X1,sK3(X0,X1)) & r3_waybel_9(X0,X1,sK2(X0,X1)) & m1_subset_1(sK3(X0,X1),u1_struct_0(X0))))),
% 0.22/0.49    introduced(choice_axiom,[])).
% 0.22/0.49  fof(f39,plain,(
% 0.22/0.49    ! [X0] : (! [X1] : (! [X2] : (r2_hidden(X2,k10_yellow_6(X0,X1)) | ~r3_waybel_9(X0,X1,X2) | ~m1_subset_1(X2,u1_struct_0(X0))) | ? [X3] : (? [X4] : (X3 != X4 & r3_waybel_9(X0,X1,X4) & r3_waybel_9(X0,X1,X3) & m1_subset_1(X4,u1_struct_0(X0))) & m1_subset_1(X3,u1_struct_0(X0))) | ~l1_waybel_0(X1,X0) | ~v7_waybel_0(X1) | ~v4_orders_2(X1) | v2_struct_0(X1)) | ~l1_pre_topc(X0) | ~v1_compts_1(X0) | ~v8_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 0.22/0.49    inference(rectify,[],[f23])).
% 0.22/0.49  fof(f23,plain,(
% 0.22/0.49    ! [X0] : (! [X1] : (! [X4] : (r2_hidden(X4,k10_yellow_6(X0,X1)) | ~r3_waybel_9(X0,X1,X4) | ~m1_subset_1(X4,u1_struct_0(X0))) | ? [X2] : (? [X3] : (X2 != X3 & r3_waybel_9(X0,X1,X3) & r3_waybel_9(X0,X1,X2) & m1_subset_1(X3,u1_struct_0(X0))) & m1_subset_1(X2,u1_struct_0(X0))) | ~l1_waybel_0(X1,X0) | ~v7_waybel_0(X1) | ~v4_orders_2(X1) | v2_struct_0(X1)) | ~l1_pre_topc(X0) | ~v1_compts_1(X0) | ~v8_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 0.22/0.49    inference(flattening,[],[f22])).
% 0.22/0.49  fof(f22,plain,(
% 0.22/0.49    ! [X0] : (! [X1] : ((! [X4] : ((r2_hidden(X4,k10_yellow_6(X0,X1)) | ~r3_waybel_9(X0,X1,X4)) | ~m1_subset_1(X4,u1_struct_0(X0))) | ? [X2] : (? [X3] : ((X2 != X3 & (r3_waybel_9(X0,X1,X3) & r3_waybel_9(X0,X1,X2))) & m1_subset_1(X3,u1_struct_0(X0))) & m1_subset_1(X2,u1_struct_0(X0)))) | (~l1_waybel_0(X1,X0) | ~v7_waybel_0(X1) | ~v4_orders_2(X1) | v2_struct_0(X1))) | (~l1_pre_topc(X0) | ~v1_compts_1(X0) | ~v8_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 0.22/0.49    inference(ennf_transformation,[],[f13])).
% 0.22/0.49  fof(f13,plain,(
% 0.22/0.49    ! [X0] : ((l1_pre_topc(X0) & v1_compts_1(X0) & v8_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((l1_waybel_0(X1,X0) & v7_waybel_0(X1) & v4_orders_2(X1) & ~v2_struct_0(X1)) => (! [X2] : (m1_subset_1(X2,u1_struct_0(X0)) => ! [X3] : (m1_subset_1(X3,u1_struct_0(X0)) => ((r3_waybel_9(X0,X1,X3) & r3_waybel_9(X0,X1,X2)) => X2 = X3))) => ! [X4] : (m1_subset_1(X4,u1_struct_0(X0)) => (r3_waybel_9(X0,X1,X4) => r2_hidden(X4,k10_yellow_6(X0,X1)))))))),
% 0.22/0.49    inference(rectify,[],[f8])).
% 0.22/0.49  fof(f8,axiom,(
% 0.22/0.49    ! [X0] : ((l1_pre_topc(X0) & v1_compts_1(X0) & v8_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((l1_waybel_0(X1,X0) & v7_waybel_0(X1) & v4_orders_2(X1) & ~v2_struct_0(X1)) => (! [X2] : (m1_subset_1(X2,u1_struct_0(X0)) => ! [X3] : (m1_subset_1(X3,u1_struct_0(X0)) => ((r3_waybel_9(X0,X1,X3) & r3_waybel_9(X0,X1,X2)) => X2 = X3))) => ! [X2] : (m1_subset_1(X2,u1_struct_0(X0)) => (r3_waybel_9(X0,X1,X2) => r2_hidden(X2,k10_yellow_6(X0,X1)))))))),
% 0.22/0.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t33_waybel_9)).
% 0.22/0.49  fof(f418,plain,(
% 0.22/0.49    ~spl9_4 | spl9_1 | ~spl9_8 | ~spl9_43),
% 0.22/0.49    inference(avatar_split_clause,[],[f356,f318,f134,f107,f118])).
% 0.22/0.49  fof(f107,plain,(
% 0.22/0.49    spl9_1 <=> r2_waybel_9(sK0,sK1)),
% 0.22/0.49    introduced(avatar_definition,[new_symbols(naming,[spl9_1])])).
% 0.22/0.49  fof(f318,plain,(
% 0.22/0.49    spl9_43 <=> r2_yellow_0(sK0,k2_relset_1(u1_struct_0(sK1),u1_struct_0(sK0),u1_waybel_0(sK0,sK1)))),
% 0.22/0.49    introduced(avatar_definition,[new_symbols(naming,[spl9_43])])).
% 0.22/0.49  fof(f356,plain,(
% 0.22/0.49    r2_waybel_9(sK0,sK1) | ~l1_waybel_0(sK1,sK0) | (~spl9_8 | ~spl9_43)),
% 0.22/0.49    inference(resolution,[],[f319,f170])).
% 0.22/0.49  fof(f170,plain,(
% 0.22/0.49    ( ! [X0] : (~r2_yellow_0(sK0,k2_relset_1(u1_struct_0(X0),u1_struct_0(sK0),u1_waybel_0(sK0,X0))) | r2_waybel_9(sK0,X0) | ~l1_waybel_0(X0,sK0)) ) | ~spl9_8),
% 0.22/0.49    inference(resolution,[],[f169,f135])).
% 0.22/0.49  fof(f135,plain,(
% 0.22/0.49    l1_waybel_9(sK0) | ~spl9_8),
% 0.22/0.49    inference(avatar_component_clause,[],[f134])).
% 0.22/0.49  fof(f169,plain,(
% 0.22/0.49    ( ! [X0,X1] : (~l1_waybel_9(X0) | ~l1_waybel_0(X1,X0) | r2_waybel_9(X0,X1) | ~r2_yellow_0(X0,k2_relset_1(u1_struct_0(X1),u1_struct_0(X0),u1_waybel_0(X0,X1)))) )),
% 0.22/0.49    inference(resolution,[],[f72,f74])).
% 0.22/0.49  fof(f74,plain,(
% 0.22/0.49    ( ! [X0] : (l1_orders_2(X0) | ~l1_waybel_9(X0)) )),
% 0.22/0.49    inference(cnf_transformation,[],[f21])).
% 0.22/0.49  fof(f21,plain,(
% 0.22/0.49    ! [X0] : ((l1_orders_2(X0) & l1_pre_topc(X0)) | ~l1_waybel_9(X0))),
% 0.22/0.49    inference(ennf_transformation,[],[f4])).
% 0.22/0.49  fof(f4,axiom,(
% 0.22/0.49    ! [X0] : (l1_waybel_9(X0) => (l1_orders_2(X0) & l1_pre_topc(X0)))),
% 0.22/0.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_l1_waybel_9)).
% 0.22/0.49  fof(f72,plain,(
% 0.22/0.49    ( ! [X0,X1] : (~l1_orders_2(X0) | ~r2_yellow_0(X0,k2_relset_1(u1_struct_0(X1),u1_struct_0(X0),u1_waybel_0(X0,X1))) | ~l1_waybel_0(X1,X0) | r2_waybel_9(X0,X1)) )),
% 0.22/0.49    inference(cnf_transformation,[],[f38])).
% 0.22/0.49  fof(f38,plain,(
% 0.22/0.49    ! [X0] : (! [X1] : (((r2_waybel_9(X0,X1) | ~r2_yellow_0(X0,k2_relset_1(u1_struct_0(X1),u1_struct_0(X0),u1_waybel_0(X0,X1)))) & (r2_yellow_0(X0,k2_relset_1(u1_struct_0(X1),u1_struct_0(X0),u1_waybel_0(X0,X1))) | ~r2_waybel_9(X0,X1))) | ~l1_waybel_0(X1,X0)) | ~l1_orders_2(X0))),
% 0.22/0.49    inference(nnf_transformation,[],[f20])).
% 0.22/0.49  fof(f20,plain,(
% 0.22/0.49    ! [X0] : (! [X1] : ((r2_waybel_9(X0,X1) <=> r2_yellow_0(X0,k2_relset_1(u1_struct_0(X1),u1_struct_0(X0),u1_waybel_0(X0,X1)))) | ~l1_waybel_0(X1,X0)) | ~l1_orders_2(X0))),
% 0.22/0.49    inference(ennf_transformation,[],[f3])).
% 0.22/0.49  fof(f3,axiom,(
% 0.22/0.49    ! [X0] : (l1_orders_2(X0) => ! [X1] : (l1_waybel_0(X1,X0) => (r2_waybel_9(X0,X1) <=> r2_yellow_0(X0,k2_relset_1(u1_struct_0(X1),u1_struct_0(X0),u1_waybel_0(X0,X1))))))),
% 0.22/0.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d4_waybel_9)).
% 0.22/0.49  fof(f319,plain,(
% 0.22/0.49    r2_yellow_0(sK0,k2_relset_1(u1_struct_0(sK1),u1_struct_0(sK0),u1_waybel_0(sK0,sK1))) | ~spl9_43),
% 0.22/0.49    inference(avatar_component_clause,[],[f318])).
% 0.22/0.49  fof(f416,plain,(
% 0.22/0.49    spl9_22 | ~spl9_16 | ~spl9_15 | ~spl9_9 | ~spl9_23 | spl9_7 | ~spl9_6 | ~spl9_5 | ~spl9_4 | spl9_58 | spl9_55),
% 0.22/0.49    inference(avatar_split_clause,[],[f402,f387,f399,f118,f122,f126,f130,f216,f138,f162,f166,f213])).
% 0.22/0.49  fof(f387,plain,(
% 0.22/0.49    spl9_55 <=> m1_subset_1(sK2(sK0,sK1),u1_struct_0(sK0))),
% 0.22/0.49    introduced(avatar_definition,[new_symbols(naming,[spl9_55])])).
% 0.22/0.49  fof(f402,plain,(
% 0.22/0.49    ( ! [X0] : (~r3_waybel_9(sK0,sK1,X0) | ~m1_subset_1(X0,u1_struct_0(sK0)) | r2_hidden(X0,k10_yellow_6(sK0,sK1)) | ~l1_waybel_0(sK1,sK0) | ~v7_waybel_0(sK1) | ~v4_orders_2(sK1) | v2_struct_0(sK1) | ~l1_pre_topc(sK0) | ~v1_compts_1(sK0) | ~v8_pre_topc(sK0) | ~v2_pre_topc(sK0) | v2_struct_0(sK0)) ) | spl9_55),
% 0.22/0.49    inference(resolution,[],[f388,f75])).
% 0.22/0.49  fof(f75,plain,(
% 0.22/0.49    ( ! [X2,X0,X1] : (m1_subset_1(sK2(X0,X1),u1_struct_0(X0)) | ~r3_waybel_9(X0,X1,X2) | ~m1_subset_1(X2,u1_struct_0(X0)) | r2_hidden(X2,k10_yellow_6(X0,X1)) | ~l1_waybel_0(X1,X0) | ~v7_waybel_0(X1) | ~v4_orders_2(X1) | v2_struct_0(X1) | ~l1_pre_topc(X0) | ~v1_compts_1(X0) | ~v8_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 0.22/0.49    inference(cnf_transformation,[],[f42])).
% 0.22/0.49  fof(f388,plain,(
% 0.22/0.49    ~m1_subset_1(sK2(sK0,sK1),u1_struct_0(sK0)) | spl9_55),
% 0.22/0.49    inference(avatar_component_clause,[],[f387])).
% 0.22/0.49  fof(f415,plain,(
% 0.22/0.49    ~spl9_42 | spl9_43 | ~spl9_44 | ~spl9_36 | ~spl9_46),
% 0.22/0.49    inference(avatar_split_clause,[],[f411,f334,f285,f321,f318,f315])).
% 0.22/0.49  fof(f315,plain,(
% 0.22/0.49    spl9_42 <=> r1_lattice3(sK0,k2_relset_1(u1_struct_0(sK1),u1_struct_0(sK0),u1_waybel_0(sK0,sK1)),sK5(sK0,k1_waybel_9(sK0,sK1),k2_relset_1(u1_struct_0(sK1),u1_struct_0(sK0),u1_waybel_0(sK0,sK1))))),
% 0.22/0.49    introduced(avatar_definition,[new_symbols(naming,[spl9_42])])).
% 0.22/0.49  fof(f321,plain,(
% 0.22/0.49    spl9_44 <=> m1_subset_1(sK5(sK0,k1_waybel_9(sK0,sK1),k2_relset_1(u1_struct_0(sK1),u1_struct_0(sK0),u1_waybel_0(sK0,sK1))),u1_struct_0(sK0))),
% 0.22/0.49    introduced(avatar_definition,[new_symbols(naming,[spl9_44])])).
% 0.22/0.49  fof(f285,plain,(
% 0.22/0.49    spl9_36 <=> ! [X1] : (~m1_subset_1(sK5(sK0,k1_waybel_9(sK0,sK1),X1),u1_struct_0(sK0)) | ~r1_lattice3(sK0,X1,k1_waybel_9(sK0,sK1)) | r2_yellow_0(sK0,X1) | ~r1_lattice3(sK0,k2_relset_1(u1_struct_0(sK1),u1_struct_0(sK0),u1_waybel_0(sK0,sK1)),sK5(sK0,k1_waybel_9(sK0,sK1),X1)))),
% 0.22/0.49    introduced(avatar_definition,[new_symbols(naming,[spl9_36])])).
% 0.22/0.49  fof(f411,plain,(
% 0.22/0.49    ~m1_subset_1(sK5(sK0,k1_waybel_9(sK0,sK1),k2_relset_1(u1_struct_0(sK1),u1_struct_0(sK0),u1_waybel_0(sK0,sK1))),u1_struct_0(sK0)) | r2_yellow_0(sK0,k2_relset_1(u1_struct_0(sK1),u1_struct_0(sK0),u1_waybel_0(sK0,sK1))) | ~r1_lattice3(sK0,k2_relset_1(u1_struct_0(sK1),u1_struct_0(sK0),u1_waybel_0(sK0,sK1)),sK5(sK0,k1_waybel_9(sK0,sK1),k2_relset_1(u1_struct_0(sK1),u1_struct_0(sK0),u1_waybel_0(sK0,sK1)))) | (~spl9_36 | ~spl9_46)),
% 0.22/0.49    inference(resolution,[],[f407,f286])).
% 0.22/0.49  fof(f286,plain,(
% 0.22/0.49    ( ! [X1] : (~r1_lattice3(sK0,X1,k1_waybel_9(sK0,sK1)) | ~m1_subset_1(sK5(sK0,k1_waybel_9(sK0,sK1),X1),u1_struct_0(sK0)) | r2_yellow_0(sK0,X1) | ~r1_lattice3(sK0,k2_relset_1(u1_struct_0(sK1),u1_struct_0(sK0),u1_waybel_0(sK0,sK1)),sK5(sK0,k1_waybel_9(sK0,sK1),X1))) ) | ~spl9_36),
% 0.22/0.49    inference(avatar_component_clause,[],[f285])).
% 0.22/0.49  fof(f407,plain,(
% 0.22/0.49    r1_lattice3(sK0,k2_relset_1(u1_struct_0(sK1),u1_struct_0(sK0),u1_waybel_0(sK0,sK1)),k1_waybel_9(sK0,sK1)) | ~spl9_46),
% 0.22/0.49    inference(avatar_component_clause,[],[f334])).
% 0.22/0.49  fof(f414,plain,(
% 0.22/0.49    ~spl9_12 | ~spl9_34 | ~spl9_27 | ~spl9_46 | spl9_43 | spl9_44),
% 0.22/0.49    inference(avatar_split_clause,[],[f413,f321,f318,f334,f236,f278,f150])).
% 0.22/0.49  fof(f278,plain,(
% 0.22/0.49    spl9_34 <=> l1_orders_2(sK0)),
% 0.22/0.49    introduced(avatar_definition,[new_symbols(naming,[spl9_34])])).
% 0.22/0.49  fof(f413,plain,(
% 0.22/0.49    r2_yellow_0(sK0,k2_relset_1(u1_struct_0(sK1),u1_struct_0(sK0),u1_waybel_0(sK0,sK1))) | ~r1_lattice3(sK0,k2_relset_1(u1_struct_0(sK1),u1_struct_0(sK0),u1_waybel_0(sK0,sK1)),k1_waybel_9(sK0,sK1)) | ~m1_subset_1(k1_waybel_9(sK0,sK1),u1_struct_0(sK0)) | ~l1_orders_2(sK0) | ~v5_orders_2(sK0) | spl9_44),
% 0.22/0.49    inference(resolution,[],[f322,f87])).
% 0.22/0.49  fof(f87,plain,(
% 0.22/0.49    ( ! [X2,X0,X1] : (m1_subset_1(sK5(X0,X1,X2),u1_struct_0(X0)) | r2_yellow_0(X0,X2) | ~r1_lattice3(X0,X2,X1) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_orders_2(X0) | ~v5_orders_2(X0)) )),
% 0.22/0.49    inference(cnf_transformation,[],[f46])).
% 0.22/0.49  fof(f46,plain,(
% 0.22/0.49    ! [X0] : (! [X1] : (! [X2] : (((r2_yellow_0(X0,X2) & k2_yellow_0(X0,X2) = X1) | (~r1_orders_2(X0,sK5(X0,X1,X2),X1) & r1_lattice3(X0,X2,sK5(X0,X1,X2)) & m1_subset_1(sK5(X0,X1,X2),u1_struct_0(X0))) | ~r1_lattice3(X0,X2,X1)) & ((! [X4] : (r1_orders_2(X0,X4,X1) | ~r1_lattice3(X0,X2,X4) | ~m1_subset_1(X4,u1_struct_0(X0))) & r1_lattice3(X0,X2,X1)) | ~r2_yellow_0(X0,X2) | k2_yellow_0(X0,X2) != X1)) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~l1_orders_2(X0) | ~v5_orders_2(X0))),
% 0.22/0.49    inference(skolemisation,[status(esa),new_symbols(skolem,[sK5])],[f27,f45])).
% 0.22/0.49  fof(f45,plain,(
% 0.22/0.49    ! [X2,X1,X0] : (? [X3] : (~r1_orders_2(X0,X3,X1) & r1_lattice3(X0,X2,X3) & m1_subset_1(X3,u1_struct_0(X0))) => (~r1_orders_2(X0,sK5(X0,X1,X2),X1) & r1_lattice3(X0,X2,sK5(X0,X1,X2)) & m1_subset_1(sK5(X0,X1,X2),u1_struct_0(X0))))),
% 0.22/0.49    introduced(choice_axiom,[])).
% 0.22/0.49  fof(f27,plain,(
% 0.22/0.49    ! [X0] : (! [X1] : (! [X2] : (((r2_yellow_0(X0,X2) & k2_yellow_0(X0,X2) = X1) | ? [X3] : (~r1_orders_2(X0,X3,X1) & r1_lattice3(X0,X2,X3) & m1_subset_1(X3,u1_struct_0(X0))) | ~r1_lattice3(X0,X2,X1)) & ((! [X4] : (r1_orders_2(X0,X4,X1) | ~r1_lattice3(X0,X2,X4) | ~m1_subset_1(X4,u1_struct_0(X0))) & r1_lattice3(X0,X2,X1)) | ~r2_yellow_0(X0,X2) | k2_yellow_0(X0,X2) != X1)) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~l1_orders_2(X0) | ~v5_orders_2(X0))),
% 0.22/0.49    inference(flattening,[],[f26])).
% 0.22/0.49  fof(f26,plain,(
% 0.22/0.49    ! [X0] : (! [X1] : (! [X2] : (((r2_yellow_0(X0,X2) & k2_yellow_0(X0,X2) = X1) | (? [X3] : ((~r1_orders_2(X0,X3,X1) & r1_lattice3(X0,X2,X3)) & m1_subset_1(X3,u1_struct_0(X0))) | ~r1_lattice3(X0,X2,X1))) & ((! [X4] : ((r1_orders_2(X0,X4,X1) | ~r1_lattice3(X0,X2,X4)) | ~m1_subset_1(X4,u1_struct_0(X0))) & r1_lattice3(X0,X2,X1)) | (~r2_yellow_0(X0,X2) | k2_yellow_0(X0,X2) != X1))) | ~m1_subset_1(X1,u1_struct_0(X0))) | (~l1_orders_2(X0) | ~v5_orders_2(X0)))),
% 0.22/0.49    inference(ennf_transformation,[],[f14])).
% 0.22/0.49  fof(f14,plain,(
% 0.22/0.49    ! [X0] : ((l1_orders_2(X0) & v5_orders_2(X0)) => ! [X1] : (m1_subset_1(X1,u1_struct_0(X0)) => ! [X2] : (((! [X3] : (m1_subset_1(X3,u1_struct_0(X0)) => (r1_lattice3(X0,X2,X3) => r1_orders_2(X0,X3,X1))) & r1_lattice3(X0,X2,X1)) => (r2_yellow_0(X0,X2) & k2_yellow_0(X0,X2) = X1)) & ((r2_yellow_0(X0,X2) & k2_yellow_0(X0,X2) = X1) => (! [X4] : (m1_subset_1(X4,u1_struct_0(X0)) => (r1_lattice3(X0,X2,X4) => r1_orders_2(X0,X4,X1))) & r1_lattice3(X0,X2,X1))))))),
% 0.22/0.49    inference(rectify,[],[f2])).
% 0.22/0.49  fof(f2,axiom,(
% 0.22/0.49    ! [X0] : ((l1_orders_2(X0) & v5_orders_2(X0)) => ! [X1] : (m1_subset_1(X1,u1_struct_0(X0)) => ! [X2] : (((! [X3] : (m1_subset_1(X3,u1_struct_0(X0)) => (r1_lattice3(X0,X2,X3) => r1_orders_2(X0,X3,X1))) & r1_lattice3(X0,X2,X1)) => (r2_yellow_0(X0,X2) & k2_yellow_0(X0,X2) = X1)) & ((r2_yellow_0(X0,X2) & k2_yellow_0(X0,X2) = X1) => (! [X3] : (m1_subset_1(X3,u1_struct_0(X0)) => (r1_lattice3(X0,X2,X3) => r1_orders_2(X0,X3,X1))) & r1_lattice3(X0,X2,X1))))))),
% 0.22/0.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t31_yellow_0)).
% 0.22/0.49  fof(f322,plain,(
% 0.22/0.49    ~m1_subset_1(sK5(sK0,k1_waybel_9(sK0,sK1),k2_relset_1(u1_struct_0(sK1),u1_struct_0(sK0),u1_waybel_0(sK0,sK1))),u1_struct_0(sK0)) | spl9_44),
% 0.22/0.49    inference(avatar_component_clause,[],[f321])).
% 0.22/0.49  fof(f404,plain,(
% 0.22/0.49    ~spl9_27 | ~spl9_26 | spl9_2 | ~spl9_58),
% 0.22/0.49    inference(avatar_split_clause,[],[f403,f399,f110,f232,f236])).
% 0.22/0.49  fof(f110,plain,(
% 0.22/0.49    spl9_2 <=> r2_hidden(k1_waybel_9(sK0,sK1),k10_yellow_6(sK0,sK1))),
% 0.22/0.49    introduced(avatar_definition,[new_symbols(naming,[spl9_2])])).
% 0.22/0.49  fof(f403,plain,(
% 0.22/0.49    ~r3_waybel_9(sK0,sK1,k1_waybel_9(sK0,sK1)) | ~m1_subset_1(k1_waybel_9(sK0,sK1),u1_struct_0(sK0)) | (spl9_2 | ~spl9_58)),
% 0.22/0.49    inference(resolution,[],[f400,f111])).
% 0.22/0.49  fof(f111,plain,(
% 0.22/0.49    ~r2_hidden(k1_waybel_9(sK0,sK1),k10_yellow_6(sK0,sK1)) | spl9_2),
% 0.22/0.49    inference(avatar_component_clause,[],[f110])).
% 0.22/0.49  fof(f400,plain,(
% 0.22/0.49    ( ! [X0] : (r2_hidden(X0,k10_yellow_6(sK0,sK1)) | ~r3_waybel_9(sK0,sK1,X0) | ~m1_subset_1(X0,u1_struct_0(sK0))) ) | ~spl9_58),
% 0.22/0.49    inference(avatar_component_clause,[],[f399])).
% 0.22/0.49  fof(f401,plain,(
% 0.22/0.49    spl9_22 | ~spl9_16 | ~spl9_15 | ~spl9_9 | ~spl9_23 | spl9_7 | ~spl9_6 | ~spl9_5 | ~spl9_4 | spl9_58 | spl9_52),
% 0.22/0.49    inference(avatar_split_clause,[],[f397,f374,f399,f118,f122,f126,f130,f216,f138,f162,f166,f213])).
% 0.22/0.49  fof(f374,plain,(
% 0.22/0.49    spl9_52 <=> m1_subset_1(sK3(sK0,sK1),u1_struct_0(sK0))),
% 0.22/0.49    introduced(avatar_definition,[new_symbols(naming,[spl9_52])])).
% 0.22/0.49  fof(f397,plain,(
% 0.22/0.49    ( ! [X0] : (~r3_waybel_9(sK0,sK1,X0) | ~m1_subset_1(X0,u1_struct_0(sK0)) | r2_hidden(X0,k10_yellow_6(sK0,sK1)) | ~l1_waybel_0(sK1,sK0) | ~v7_waybel_0(sK1) | ~v4_orders_2(sK1) | v2_struct_0(sK1) | ~l1_pre_topc(sK0) | ~v1_compts_1(sK0) | ~v8_pre_topc(sK0) | ~v2_pre_topc(sK0) | v2_struct_0(sK0)) ) | spl9_52),
% 0.22/0.49    inference(resolution,[],[f375,f76])).
% 0.22/0.49  fof(f76,plain,(
% 0.22/0.49    ( ! [X2,X0,X1] : (m1_subset_1(sK3(X0,X1),u1_struct_0(X0)) | ~r3_waybel_9(X0,X1,X2) | ~m1_subset_1(X2,u1_struct_0(X0)) | r2_hidden(X2,k10_yellow_6(X0,X1)) | ~l1_waybel_0(X1,X0) | ~v7_waybel_0(X1) | ~v4_orders_2(X1) | v2_struct_0(X1) | ~l1_pre_topc(X0) | ~v1_compts_1(X0) | ~v8_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 0.22/0.49    inference(cnf_transformation,[],[f42])).
% 0.22/0.49  fof(f375,plain,(
% 0.22/0.49    ~m1_subset_1(sK3(sK0,sK1),u1_struct_0(sK0)) | spl9_52),
% 0.22/0.49    inference(avatar_component_clause,[],[f374])).
% 0.22/0.49  fof(f396,plain,(
% 0.22/0.49    spl9_57 | ~spl9_55 | ~spl9_19 | ~spl9_51),
% 0.22/0.49    inference(avatar_split_clause,[],[f385,f366,f186,f387,f394])).
% 0.22/0.49  fof(f186,plain,(
% 0.22/0.49    spl9_19 <=> ! [X0] : (~m1_subset_1(X0,u1_struct_0(sK0)) | ~r3_waybel_9(sK0,sK1,X0) | k1_waybel_9(sK0,sK1) = X0)),
% 0.22/0.49    introduced(avatar_definition,[new_symbols(naming,[spl9_19])])).
% 0.22/0.49  fof(f366,plain,(
% 0.22/0.49    spl9_51 <=> r3_waybel_9(sK0,sK1,sK2(sK0,sK1))),
% 0.22/0.49    introduced(avatar_definition,[new_symbols(naming,[spl9_51])])).
% 0.22/0.49  fof(f385,plain,(
% 0.22/0.49    ~m1_subset_1(sK2(sK0,sK1),u1_struct_0(sK0)) | k1_waybel_9(sK0,sK1) = sK2(sK0,sK1) | (~spl9_19 | ~spl9_51)),
% 0.22/0.49    inference(resolution,[],[f367,f187])).
% 0.22/0.49  fof(f187,plain,(
% 0.22/0.49    ( ! [X0] : (~r3_waybel_9(sK0,sK1,X0) | ~m1_subset_1(X0,u1_struct_0(sK0)) | k1_waybel_9(sK0,sK1) = X0) ) | ~spl9_19),
% 0.22/0.49    inference(avatar_component_clause,[],[f186])).
% 0.22/0.49  fof(f367,plain,(
% 0.22/0.49    r3_waybel_9(sK0,sK1,sK2(sK0,sK1)) | ~spl9_51),
% 0.22/0.49    inference(avatar_component_clause,[],[f366])).
% 0.22/0.49  fof(f383,plain,(
% 0.22/0.49    spl9_54 | ~spl9_52 | ~spl9_19 | ~spl9_50),
% 0.22/0.49    inference(avatar_split_clause,[],[f372,f362,f186,f374,f381])).
% 0.22/0.49  fof(f362,plain,(
% 0.22/0.49    spl9_50 <=> r3_waybel_9(sK0,sK1,sK3(sK0,sK1))),
% 0.22/0.49    introduced(avatar_definition,[new_symbols(naming,[spl9_50])])).
% 0.22/0.49  fof(f372,plain,(
% 0.22/0.49    ~m1_subset_1(sK3(sK0,sK1),u1_struct_0(sK0)) | k1_waybel_9(sK0,sK1) = sK3(sK0,sK1) | (~spl9_19 | ~spl9_50)),
% 0.22/0.49    inference(resolution,[],[f363,f187])).
% 0.22/0.49  fof(f363,plain,(
% 0.22/0.49    r3_waybel_9(sK0,sK1,sK3(sK0,sK1)) | ~spl9_50),
% 0.22/0.49    inference(avatar_component_clause,[],[f362])).
% 0.22/0.49  fof(f370,plain,(
% 0.22/0.49    ~spl9_34 | ~spl9_11 | ~spl9_22),
% 0.22/0.49    inference(avatar_split_clause,[],[f369,f213,f146,f278])).
% 0.22/0.49  fof(f369,plain,(
% 0.22/0.49    ~v1_lattice3(sK0) | ~l1_orders_2(sK0) | ~spl9_22),
% 0.22/0.49    inference(resolution,[],[f214,f70])).
% 0.22/0.49  fof(f70,plain,(
% 0.22/0.49    ( ! [X0] : (~v2_struct_0(X0) | ~v1_lattice3(X0) | ~l1_orders_2(X0)) )),
% 0.22/0.49    inference(cnf_transformation,[],[f19])).
% 0.22/0.49  fof(f19,plain,(
% 0.22/0.49    ! [X0] : (~v2_struct_0(X0) | ~v1_lattice3(X0) | ~l1_orders_2(X0))),
% 0.22/0.49    inference(flattening,[],[f18])).
% 0.22/0.49  fof(f18,plain,(
% 0.22/0.49    ! [X0] : ((~v2_struct_0(X0) | ~v1_lattice3(X0)) | ~l1_orders_2(X0))),
% 0.22/0.49    inference(ennf_transformation,[],[f1])).
% 0.22/0.49  fof(f1,axiom,(
% 0.22/0.49    ! [X0] : (l1_orders_2(X0) => (v1_lattice3(X0) => ~v2_struct_0(X0)))),
% 0.22/0.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_lattice3)).
% 0.22/0.49  fof(f214,plain,(
% 0.22/0.49    v2_struct_0(sK0) | ~spl9_22),
% 0.22/0.49    inference(avatar_component_clause,[],[f213])).
% 0.22/0.49  fof(f368,plain,(
% 0.22/0.49    spl9_22 | ~spl9_16 | ~spl9_15 | ~spl9_9 | ~spl9_23 | spl9_7 | ~spl9_6 | ~spl9_5 | ~spl9_4 | spl9_51 | ~spl9_27 | ~spl9_26 | spl9_2),
% 0.22/0.49    inference(avatar_split_clause,[],[f360,f110,f232,f236,f366,f118,f122,f126,f130,f216,f138,f162,f166,f213])).
% 0.22/0.49  fof(f360,plain,(
% 0.22/0.49    ~r3_waybel_9(sK0,sK1,k1_waybel_9(sK0,sK1)) | ~m1_subset_1(k1_waybel_9(sK0,sK1),u1_struct_0(sK0)) | r3_waybel_9(sK0,sK1,sK2(sK0,sK1)) | ~l1_waybel_0(sK1,sK0) | ~v7_waybel_0(sK1) | ~v4_orders_2(sK1) | v2_struct_0(sK1) | ~l1_pre_topc(sK0) | ~v1_compts_1(sK0) | ~v8_pre_topc(sK0) | ~v2_pre_topc(sK0) | v2_struct_0(sK0) | spl9_2),
% 0.22/0.49    inference(resolution,[],[f111,f77])).
% 0.22/0.49  fof(f77,plain,(
% 0.22/0.49    ( ! [X2,X0,X1] : (r2_hidden(X2,k10_yellow_6(X0,X1)) | ~r3_waybel_9(X0,X1,X2) | ~m1_subset_1(X2,u1_struct_0(X0)) | r3_waybel_9(X0,X1,sK2(X0,X1)) | ~l1_waybel_0(X1,X0) | ~v7_waybel_0(X1) | ~v4_orders_2(X1) | v2_struct_0(X1) | ~l1_pre_topc(X0) | ~v1_compts_1(X0) | ~v8_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 0.22/0.49    inference(cnf_transformation,[],[f42])).
% 0.22/0.49  fof(f364,plain,(
% 0.22/0.49    spl9_22 | ~spl9_16 | ~spl9_15 | ~spl9_9 | ~spl9_23 | spl9_7 | ~spl9_6 | ~spl9_5 | ~spl9_4 | spl9_50 | ~spl9_27 | ~spl9_26 | spl9_2),
% 0.22/0.49    inference(avatar_split_clause,[],[f359,f110,f232,f236,f362,f118,f122,f126,f130,f216,f138,f162,f166,f213])).
% 0.22/0.49  fof(f359,plain,(
% 0.22/0.49    ~r3_waybel_9(sK0,sK1,k1_waybel_9(sK0,sK1)) | ~m1_subset_1(k1_waybel_9(sK0,sK1),u1_struct_0(sK0)) | r3_waybel_9(sK0,sK1,sK3(sK0,sK1)) | ~l1_waybel_0(sK1,sK0) | ~v7_waybel_0(sK1) | ~v4_orders_2(sK1) | v2_struct_0(sK1) | ~l1_pre_topc(sK0) | ~v1_compts_1(sK0) | ~v8_pre_topc(sK0) | ~v2_pre_topc(sK0) | v2_struct_0(sK0) | spl9_2),
% 0.22/0.49    inference(resolution,[],[f111,f78])).
% 0.22/0.49  fof(f78,plain,(
% 0.22/0.49    ( ! [X2,X0,X1] : (r2_hidden(X2,k10_yellow_6(X0,X1)) | ~r3_waybel_9(X0,X1,X2) | ~m1_subset_1(X2,u1_struct_0(X0)) | r3_waybel_9(X0,X1,sK3(X0,X1)) | ~l1_waybel_0(X1,X0) | ~v7_waybel_0(X1) | ~v4_orders_2(X1) | v2_struct_0(X1) | ~l1_pre_topc(X0) | ~v1_compts_1(X0) | ~v8_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 0.22/0.49    inference(cnf_transformation,[],[f42])).
% 0.22/0.49  fof(f355,plain,(
% 0.22/0.49    ~spl9_27 | ~spl9_26 | ~spl9_41 | spl9_46),
% 0.22/0.49    inference(avatar_split_clause,[],[f353,f334,f310,f232,f236])).
% 0.22/0.49  fof(f310,plain,(
% 0.22/0.49    spl9_41 <=> ! [X0] : (~m1_subset_1(X0,u1_struct_0(sK0)) | ~r3_waybel_9(sK0,sK1,X0) | r1_lattice3(sK0,k2_relset_1(u1_struct_0(sK1),u1_struct_0(sK0),u1_waybel_0(sK0,sK1)),X0))),
% 0.22/0.49    introduced(avatar_definition,[new_symbols(naming,[spl9_41])])).
% 0.22/0.49  fof(f353,plain,(
% 0.22/0.49    ~r3_waybel_9(sK0,sK1,k1_waybel_9(sK0,sK1)) | ~m1_subset_1(k1_waybel_9(sK0,sK1),u1_struct_0(sK0)) | (~spl9_41 | spl9_46)),
% 0.22/0.49    inference(resolution,[],[f335,f311])).
% 0.22/0.49  fof(f311,plain,(
% 0.22/0.49    ( ! [X0] : (r1_lattice3(sK0,k2_relset_1(u1_struct_0(sK1),u1_struct_0(sK0),u1_waybel_0(sK0,sK1)),X0) | ~r3_waybel_9(sK0,sK1,X0) | ~m1_subset_1(X0,u1_struct_0(sK0))) ) | ~spl9_41),
% 0.22/0.49    inference(avatar_component_clause,[],[f310])).
% 0.22/0.49  fof(f340,plain,(
% 0.22/0.49    ~spl9_12 | ~spl9_34 | ~spl9_27 | ~spl9_46 | spl9_43 | spl9_42),
% 0.22/0.49    inference(avatar_split_clause,[],[f328,f315,f318,f334,f236,f278,f150])).
% 0.22/0.49  fof(f328,plain,(
% 0.22/0.49    r2_yellow_0(sK0,k2_relset_1(u1_struct_0(sK1),u1_struct_0(sK0),u1_waybel_0(sK0,sK1))) | ~r1_lattice3(sK0,k2_relset_1(u1_struct_0(sK1),u1_struct_0(sK0),u1_waybel_0(sK0,sK1)),k1_waybel_9(sK0,sK1)) | ~m1_subset_1(k1_waybel_9(sK0,sK1),u1_struct_0(sK0)) | ~l1_orders_2(sK0) | ~v5_orders_2(sK0) | spl9_42),
% 0.22/0.49    inference(resolution,[],[f316,f88])).
% 0.22/0.49  fof(f88,plain,(
% 0.22/0.49    ( ! [X2,X0,X1] : (r1_lattice3(X0,X2,sK5(X0,X1,X2)) | r2_yellow_0(X0,X2) | ~r1_lattice3(X0,X2,X1) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_orders_2(X0) | ~v5_orders_2(X0)) )),
% 0.22/0.49    inference(cnf_transformation,[],[f46])).
% 0.22/0.49  fof(f316,plain,(
% 0.22/0.49    ~r1_lattice3(sK0,k2_relset_1(u1_struct_0(sK1),u1_struct_0(sK0),u1_waybel_0(sK0,sK1)),sK5(sK0,k1_waybel_9(sK0,sK1),k2_relset_1(u1_struct_0(sK1),u1_struct_0(sK0),u1_waybel_0(sK0,sK1)))) | spl9_42),
% 0.22/0.49    inference(avatar_component_clause,[],[f315])).
% 0.22/0.49  fof(f312,plain,(
% 0.22/0.49    spl9_41 | ~spl9_4 | ~spl9_5 | ~spl9_6 | spl9_7 | ~spl9_3 | ~spl9_40),
% 0.22/0.49    inference(avatar_split_clause,[],[f308,f305,f114,f130,f126,f122,f118,f310])).
% 0.22/0.49  fof(f305,plain,(
% 0.22/0.49    spl9_40 <=> ! [X1,X0] : (~r3_waybel_9(sK0,X0,X1) | v2_struct_0(X0) | ~v4_orders_2(X0) | ~v7_waybel_0(X0) | ~l1_waybel_0(X0,sK0) | ~m1_subset_1(X1,u1_struct_0(sK0)) | r1_lattice3(sK0,k2_relset_1(u1_struct_0(X0),u1_struct_0(sK0),u1_waybel_0(sK0,X0)),X1) | ~v11_waybel_0(X0,sK0))),
% 0.22/0.49    introduced(avatar_definition,[new_symbols(naming,[spl9_40])])).
% 0.22/0.49  fof(f308,plain,(
% 0.22/0.49    ( ! [X0] : (v2_struct_0(sK1) | ~v4_orders_2(sK1) | ~v7_waybel_0(sK1) | ~l1_waybel_0(sK1,sK0) | ~m1_subset_1(X0,u1_struct_0(sK0)) | r1_lattice3(sK0,k2_relset_1(u1_struct_0(sK1),u1_struct_0(sK0),u1_waybel_0(sK0,sK1)),X0) | ~r3_waybel_9(sK0,sK1,X0)) ) | (~spl9_3 | ~spl9_40)),
% 0.22/0.49    inference(resolution,[],[f306,f115])).
% 0.22/0.49  fof(f115,plain,(
% 0.22/0.49    v11_waybel_0(sK1,sK0) | ~spl9_3),
% 0.22/0.49    inference(avatar_component_clause,[],[f114])).
% 0.22/0.49  fof(f306,plain,(
% 0.22/0.49    ( ! [X0,X1] : (~v11_waybel_0(X0,sK0) | v2_struct_0(X0) | ~v4_orders_2(X0) | ~v7_waybel_0(X0) | ~l1_waybel_0(X0,sK0) | ~m1_subset_1(X1,u1_struct_0(sK0)) | r1_lattice3(sK0,k2_relset_1(u1_struct_0(X0),u1_struct_0(sK0),u1_waybel_0(sK0,X0)),X1) | ~r3_waybel_9(sK0,X0,X1)) ) | ~spl9_40),
% 0.22/0.49    inference(avatar_component_clause,[],[f305])).
% 0.22/0.49  fof(f307,plain,(
% 0.22/0.49    ~spl9_16 | ~spl9_15 | ~spl9_14 | ~spl9_13 | ~spl9_12 | ~spl9_11 | ~spl9_10 | ~spl9_9 | ~spl9_8 | spl9_40 | spl9_39),
% 0.22/0.49    inference(avatar_split_clause,[],[f303,f300,f305,f134,f138,f142,f146,f150,f154,f158,f162,f166])).
% 0.22/0.49  fof(f300,plain,(
% 0.22/0.49    spl9_39 <=> m1_subset_1(sK7(sK0),u1_struct_0(sK0))),
% 0.22/0.49    introduced(avatar_definition,[new_symbols(naming,[spl9_39])])).
% 0.22/0.49  fof(f303,plain,(
% 0.22/0.49    ( ! [X0,X1] : (~r3_waybel_9(sK0,X0,X1) | ~v11_waybel_0(X0,sK0) | r1_lattice3(sK0,k2_relset_1(u1_struct_0(X0),u1_struct_0(sK0),u1_waybel_0(sK0,X0)),X1) | ~m1_subset_1(X1,u1_struct_0(sK0)) | ~l1_waybel_0(X0,sK0) | ~v7_waybel_0(X0) | ~v4_orders_2(X0) | v2_struct_0(X0) | ~l1_waybel_9(sK0) | ~v1_compts_1(sK0) | ~v2_lattice3(sK0) | ~v1_lattice3(sK0) | ~v5_orders_2(sK0) | ~v4_orders_2(sK0) | ~v3_orders_2(sK0) | ~v8_pre_topc(sK0) | ~v2_pre_topc(sK0)) ) | spl9_39),
% 0.22/0.49    inference(resolution,[],[f301,f104])).
% 0.22/0.49  fof(f104,plain,(
% 0.22/0.49    ( ! [X0,X3,X1] : (m1_subset_1(sK7(X0),u1_struct_0(X0)) | ~r3_waybel_9(X0,X1,X3) | ~v11_waybel_0(X1,X0) | r1_lattice3(X0,k2_relset_1(u1_struct_0(X1),u1_struct_0(X0),u1_waybel_0(X0,X1)),X3) | ~m1_subset_1(X3,u1_struct_0(X0)) | ~l1_waybel_0(X1,X0) | ~v7_waybel_0(X1) | ~v4_orders_2(X1) | v2_struct_0(X1) | ~l1_waybel_9(X0) | ~v1_compts_1(X0) | ~v2_lattice3(X0) | ~v1_lattice3(X0) | ~v5_orders_2(X0) | ~v4_orders_2(X0) | ~v3_orders_2(X0) | ~v8_pre_topc(X0) | ~v2_pre_topc(X0)) )),
% 0.22/0.49    inference(duplicate_literal_removal,[],[f99])).
% 0.22/0.49  fof(f99,plain,(
% 0.22/0.49    ( ! [X0,X3,X1] : (r1_lattice3(X0,k2_relset_1(u1_struct_0(X1),u1_struct_0(X0),u1_waybel_0(X0,X1)),X3) | ~r3_waybel_9(X0,X1,X3) | ~v11_waybel_0(X1,X0) | m1_subset_1(sK7(X0),u1_struct_0(X0)) | ~m1_subset_1(X3,u1_struct_0(X0)) | ~m1_subset_1(X3,u1_struct_0(X0)) | ~l1_waybel_0(X1,X0) | ~v7_waybel_0(X1) | ~v4_orders_2(X1) | v2_struct_0(X1) | ~l1_waybel_9(X0) | ~v1_compts_1(X0) | ~v2_lattice3(X0) | ~v1_lattice3(X0) | ~v5_orders_2(X0) | ~v4_orders_2(X0) | ~v3_orders_2(X0) | ~v8_pre_topc(X0) | ~v2_pre_topc(X0)) )),
% 0.22/0.49    inference(equality_resolution,[],[f92])).
% 0.22/0.49  fof(f92,plain,(
% 0.22/0.49    ( ! [X2,X0,X3,X1] : (r1_lattice3(X0,k2_relset_1(u1_struct_0(X1),u1_struct_0(X0),u1_waybel_0(X0,X1)),X3) | ~r3_waybel_9(X0,X1,X2) | ~v11_waybel_0(X1,X0) | m1_subset_1(sK7(X0),u1_struct_0(X0)) | X2 != X3 | ~m1_subset_1(X3,u1_struct_0(X0)) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~l1_waybel_0(X1,X0) | ~v7_waybel_0(X1) | ~v4_orders_2(X1) | v2_struct_0(X1) | ~l1_waybel_9(X0) | ~v1_compts_1(X0) | ~v2_lattice3(X0) | ~v1_lattice3(X0) | ~v5_orders_2(X0) | ~v4_orders_2(X0) | ~v3_orders_2(X0) | ~v8_pre_topc(X0) | ~v2_pre_topc(X0)) )),
% 0.22/0.49    inference(cnf_transformation,[],[f50])).
% 0.22/0.49  fof(f301,plain,(
% 0.22/0.49    ~m1_subset_1(sK7(sK0),u1_struct_0(sK0)) | spl9_39),
% 0.22/0.49    inference(avatar_component_clause,[],[f300])).
% 0.22/0.49  fof(f302,plain,(
% 0.22/0.49    ~spl9_39 | spl9_37),
% 0.22/0.49    inference(avatar_split_clause,[],[f298,f292,f300])).
% 0.22/0.49  fof(f298,plain,(
% 0.22/0.49    ~m1_subset_1(sK7(sK0),u1_struct_0(sK0)) | spl9_37),
% 0.22/0.49    inference(resolution,[],[f293,f63])).
% 0.22/0.49  fof(f63,plain,(
% 0.22/0.49    ( ! [X2] : (v5_pre_topc(k4_waybel_1(sK0,X2),sK0,sK0) | ~m1_subset_1(X2,u1_struct_0(sK0))) )),
% 0.22/0.49    inference(cnf_transformation,[],[f37])).
% 0.22/0.49  fof(f37,plain,(
% 0.22/0.49    ((~r2_hidden(k1_waybel_9(sK0,sK1),k10_yellow_6(sK0,sK1)) | ~r2_waybel_9(sK0,sK1)) & v11_waybel_0(sK1,sK0) & l1_waybel_0(sK1,sK0) & v7_waybel_0(sK1) & v4_orders_2(sK1) & ~v2_struct_0(sK1)) & ! [X2] : (v5_pre_topc(k4_waybel_1(sK0,X2),sK0,sK0) | ~m1_subset_1(X2,u1_struct_0(sK0))) & l1_waybel_9(sK0) & v1_compts_1(sK0) & v2_lattice3(sK0) & v1_lattice3(sK0) & v5_orders_2(sK0) & v4_orders_2(sK0) & v3_orders_2(sK0) & v8_pre_topc(sK0) & v2_pre_topc(sK0)),
% 0.22/0.49    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f34,f36,f35])).
% 0.22/0.50  fof(f35,plain,(
% 0.22/0.50    ? [X0] : (? [X1] : ((~r2_hidden(k1_waybel_9(X0,X1),k10_yellow_6(X0,X1)) | ~r2_waybel_9(X0,X1)) & v11_waybel_0(X1,X0) & l1_waybel_0(X1,X0) & v7_waybel_0(X1) & v4_orders_2(X1) & ~v2_struct_0(X1)) & ! [X2] : (v5_pre_topc(k4_waybel_1(X0,X2),X0,X0) | ~m1_subset_1(X2,u1_struct_0(X0))) & l1_waybel_9(X0) & v1_compts_1(X0) & v2_lattice3(X0) & v1_lattice3(X0) & v5_orders_2(X0) & v4_orders_2(X0) & v3_orders_2(X0) & v8_pre_topc(X0) & v2_pre_topc(X0)) => (? [X1] : ((~r2_hidden(k1_waybel_9(sK0,X1),k10_yellow_6(sK0,X1)) | ~r2_waybel_9(sK0,X1)) & v11_waybel_0(X1,sK0) & l1_waybel_0(X1,sK0) & v7_waybel_0(X1) & v4_orders_2(X1) & ~v2_struct_0(X1)) & ! [X2] : (v5_pre_topc(k4_waybel_1(sK0,X2),sK0,sK0) | ~m1_subset_1(X2,u1_struct_0(sK0))) & l1_waybel_9(sK0) & v1_compts_1(sK0) & v2_lattice3(sK0) & v1_lattice3(sK0) & v5_orders_2(sK0) & v4_orders_2(sK0) & v3_orders_2(sK0) & v8_pre_topc(sK0) & v2_pre_topc(sK0))),
% 0.22/0.50    introduced(choice_axiom,[])).
% 0.22/0.50  fof(f36,plain,(
% 0.22/0.50    ? [X1] : ((~r2_hidden(k1_waybel_9(sK0,X1),k10_yellow_6(sK0,X1)) | ~r2_waybel_9(sK0,X1)) & v11_waybel_0(X1,sK0) & l1_waybel_0(X1,sK0) & v7_waybel_0(X1) & v4_orders_2(X1) & ~v2_struct_0(X1)) => ((~r2_hidden(k1_waybel_9(sK0,sK1),k10_yellow_6(sK0,sK1)) | ~r2_waybel_9(sK0,sK1)) & v11_waybel_0(sK1,sK0) & l1_waybel_0(sK1,sK0) & v7_waybel_0(sK1) & v4_orders_2(sK1) & ~v2_struct_0(sK1))),
% 0.22/0.50    introduced(choice_axiom,[])).
% 0.22/0.50  fof(f34,plain,(
% 0.22/0.50    ? [X0] : (? [X1] : ((~r2_hidden(k1_waybel_9(X0,X1),k10_yellow_6(X0,X1)) | ~r2_waybel_9(X0,X1)) & v11_waybel_0(X1,X0) & l1_waybel_0(X1,X0) & v7_waybel_0(X1) & v4_orders_2(X1) & ~v2_struct_0(X1)) & ! [X2] : (v5_pre_topc(k4_waybel_1(X0,X2),X0,X0) | ~m1_subset_1(X2,u1_struct_0(X0))) & l1_waybel_9(X0) & v1_compts_1(X0) & v2_lattice3(X0) & v1_lattice3(X0) & v5_orders_2(X0) & v4_orders_2(X0) & v3_orders_2(X0) & v8_pre_topc(X0) & v2_pre_topc(X0))),
% 0.22/0.50    inference(rectify,[],[f17])).
% 0.22/0.50  fof(f17,plain,(
% 0.22/0.50    ? [X0] : (? [X2] : ((~r2_hidden(k1_waybel_9(X0,X2),k10_yellow_6(X0,X2)) | ~r2_waybel_9(X0,X2)) & v11_waybel_0(X2,X0) & l1_waybel_0(X2,X0) & v7_waybel_0(X2) & v4_orders_2(X2) & ~v2_struct_0(X2)) & ! [X1] : (v5_pre_topc(k4_waybel_1(X0,X1),X0,X0) | ~m1_subset_1(X1,u1_struct_0(X0))) & l1_waybel_9(X0) & v1_compts_1(X0) & v2_lattice3(X0) & v1_lattice3(X0) & v5_orders_2(X0) & v4_orders_2(X0) & v3_orders_2(X0) & v8_pre_topc(X0) & v2_pre_topc(X0))),
% 0.22/0.50    inference(flattening,[],[f16])).
% 0.22/0.50  fof(f16,plain,(
% 0.22/0.50    ? [X0] : ((? [X2] : (((~r2_hidden(k1_waybel_9(X0,X2),k10_yellow_6(X0,X2)) | ~r2_waybel_9(X0,X2)) & v11_waybel_0(X2,X0)) & (l1_waybel_0(X2,X0) & v7_waybel_0(X2) & v4_orders_2(X2) & ~v2_struct_0(X2))) & ! [X1] : (v5_pre_topc(k4_waybel_1(X0,X1),X0,X0) | ~m1_subset_1(X1,u1_struct_0(X0)))) & (l1_waybel_9(X0) & v1_compts_1(X0) & v2_lattice3(X0) & v1_lattice3(X0) & v5_orders_2(X0) & v4_orders_2(X0) & v3_orders_2(X0) & v8_pre_topc(X0) & v2_pre_topc(X0)))),
% 0.22/0.50    inference(ennf_transformation,[],[f12])).
% 0.22/0.50  fof(f12,plain,(
% 0.22/0.50    ~! [X0] : ((l1_waybel_9(X0) & v1_compts_1(X0) & v2_lattice3(X0) & v1_lattice3(X0) & v5_orders_2(X0) & v4_orders_2(X0) & v3_orders_2(X0) & v8_pre_topc(X0) & v2_pre_topc(X0)) => (! [X1] : (m1_subset_1(X1,u1_struct_0(X0)) => v5_pre_topc(k4_waybel_1(X0,X1),X0,X0)) => ! [X2] : ((l1_waybel_0(X2,X0) & v7_waybel_0(X2) & v4_orders_2(X2) & ~v2_struct_0(X2)) => (v11_waybel_0(X2,X0) => (r2_hidden(k1_waybel_9(X0,X2),k10_yellow_6(X0,X2)) & r2_waybel_9(X0,X2))))))),
% 0.22/0.50    inference(rectify,[],[f11])).
% 0.22/0.50  fof(f11,negated_conjecture,(
% 0.22/0.50    ~! [X0] : ((l1_waybel_9(X0) & v1_compts_1(X0) & v2_lattice3(X0) & v1_lattice3(X0) & v5_orders_2(X0) & v4_orders_2(X0) & v3_orders_2(X0) & v8_pre_topc(X0) & v2_pre_topc(X0)) => (! [X1] : (m1_subset_1(X1,u1_struct_0(X0)) => v5_pre_topc(k4_waybel_1(X0,X1),X0,X0)) => ! [X1] : ((l1_waybel_0(X1,X0) & v7_waybel_0(X1) & v4_orders_2(X1) & ~v2_struct_0(X1)) => (v11_waybel_0(X1,X0) => (r2_hidden(k1_waybel_9(X0,X1),k10_yellow_6(X0,X1)) & r2_waybel_9(X0,X1))))))),
% 0.22/0.50    inference(negated_conjecture,[],[f10])).
% 0.22/0.50  fof(f10,conjecture,(
% 0.22/0.50    ! [X0] : ((l1_waybel_9(X0) & v1_compts_1(X0) & v2_lattice3(X0) & v1_lattice3(X0) & v5_orders_2(X0) & v4_orders_2(X0) & v3_orders_2(X0) & v8_pre_topc(X0) & v2_pre_topc(X0)) => (! [X1] : (m1_subset_1(X1,u1_struct_0(X0)) => v5_pre_topc(k4_waybel_1(X0,X1),X0,X0)) => ! [X1] : ((l1_waybel_0(X1,X0) & v7_waybel_0(X1) & v4_orders_2(X1) & ~v2_struct_0(X1)) => (v11_waybel_0(X1,X0) => (r2_hidden(k1_waybel_9(X0,X1),k10_yellow_6(X0,X1)) & r2_waybel_9(X0,X1))))))),
% 0.22/0.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t39_waybel_9)).
% 0.22/0.50  fof(f293,plain,(
% 0.22/0.50    ~v5_pre_topc(k4_waybel_1(sK0,sK7(sK0)),sK0,sK0) | spl9_37),
% 0.22/0.50    inference(avatar_component_clause,[],[f292])).
% 0.22/0.50  fof(f289,plain,(
% 0.22/0.50    ~spl9_8 | spl9_34),
% 0.22/0.50    inference(avatar_split_clause,[],[f288,f278,f134])).
% 0.22/0.50  fof(f288,plain,(
% 0.22/0.50    ~l1_waybel_9(sK0) | spl9_34),
% 0.22/0.50    inference(resolution,[],[f279,f74])).
% 0.22/0.50  fof(f279,plain,(
% 0.22/0.50    ~l1_orders_2(sK0) | spl9_34),
% 0.22/0.50    inference(avatar_component_clause,[],[f278])).
% 0.22/0.50  fof(f287,plain,(
% 0.22/0.50    ~spl9_12 | ~spl9_34 | ~spl9_27 | spl9_36 | ~spl9_33),
% 0.22/0.50    inference(avatar_split_clause,[],[f276,f269,f285,f236,f278,f150])).
% 0.22/0.50  fof(f269,plain,(
% 0.22/0.50    spl9_33 <=> ! [X0] : (~m1_subset_1(X0,u1_struct_0(sK0)) | r1_orders_2(sK0,X0,k1_waybel_9(sK0,sK1)) | ~r1_lattice3(sK0,k2_relset_1(u1_struct_0(sK1),u1_struct_0(sK0),u1_waybel_0(sK0,sK1)),X0))),
% 0.22/0.50    introduced(avatar_definition,[new_symbols(naming,[spl9_33])])).
% 0.22/0.50  % (30174)lrs+1011_3:2_aac=none:afp=10000:afq=1.2:amm=off:anc=all:cond=on:fde=none:gs=on:gsem=on:irw=on:lma=on:nm=32:newcnf=on:nwc=3:nicw=on:stl=30:sac=on:sp=reverse_arity:urr=ec_only:updr=off:uhcvi=on_5 on theBenchmark
% 0.22/0.50  fof(f276,plain,(
% 0.22/0.50    ( ! [X1] : (~m1_subset_1(sK5(sK0,k1_waybel_9(sK0,sK1),X1),u1_struct_0(sK0)) | ~r1_lattice3(sK0,k2_relset_1(u1_struct_0(sK1),u1_struct_0(sK0),u1_waybel_0(sK0,sK1)),sK5(sK0,k1_waybel_9(sK0,sK1),X1)) | r2_yellow_0(sK0,X1) | ~r1_lattice3(sK0,X1,k1_waybel_9(sK0,sK1)) | ~m1_subset_1(k1_waybel_9(sK0,sK1),u1_struct_0(sK0)) | ~l1_orders_2(sK0) | ~v5_orders_2(sK0)) ) | ~spl9_33),
% 0.22/0.50    inference(resolution,[],[f270,f89])).
% 0.22/0.50  fof(f89,plain,(
% 0.22/0.50    ( ! [X2,X0,X1] : (~r1_orders_2(X0,sK5(X0,X1,X2),X1) | r2_yellow_0(X0,X2) | ~r1_lattice3(X0,X2,X1) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_orders_2(X0) | ~v5_orders_2(X0)) )),
% 0.22/0.50    inference(cnf_transformation,[],[f46])).
% 0.22/0.50  fof(f270,plain,(
% 0.22/0.50    ( ! [X0] : (r1_orders_2(sK0,X0,k1_waybel_9(sK0,sK1)) | ~m1_subset_1(X0,u1_struct_0(sK0)) | ~r1_lattice3(sK0,k2_relset_1(u1_struct_0(sK1),u1_struct_0(sK0),u1_waybel_0(sK0,sK1)),X0)) ) | ~spl9_33),
% 0.22/0.50    inference(avatar_component_clause,[],[f269])).
% 0.22/0.50  fof(f274,plain,(
% 0.22/0.50    spl9_22 | ~spl9_16 | ~spl9_15 | ~spl9_9 | ~spl9_23 | spl9_7 | ~spl9_6 | ~spl9_5 | ~spl9_4 | ~spl9_27 | spl9_33 | ~spl9_24 | ~spl9_30),
% 0.22/0.50    inference(avatar_split_clause,[],[f273,f250,f219,f269,f236,f118,f122,f126,f130,f216,f138,f162,f166,f213])).
% 0.22/0.50  fof(f219,plain,(
% 0.22/0.50    spl9_24 <=> k1_waybel_9(sK0,sK1) = sK4(sK0,sK1)),
% 0.22/0.50    introduced(avatar_definition,[new_symbols(naming,[spl9_24])])).
% 0.22/0.50  fof(f250,plain,(
% 0.22/0.50    spl9_30 <=> ! [X1,X0] : (~r1_lattice3(sK0,k2_relset_1(u1_struct_0(sK1),u1_struct_0(sK0),u1_waybel_0(sK0,sK1)),X0) | ~m1_subset_1(X0,u1_struct_0(sK0)) | ~r3_waybel_9(sK0,sK1,X1) | ~m1_subset_1(X1,u1_struct_0(sK0)) | r1_orders_2(sK0,X0,X1))),
% 0.22/0.50    introduced(avatar_definition,[new_symbols(naming,[spl9_30])])).
% 0.22/0.50  fof(f273,plain,(
% 0.22/0.50    ( ! [X1] : (r1_orders_2(sK0,X1,k1_waybel_9(sK0,sK1)) | ~m1_subset_1(k1_waybel_9(sK0,sK1),u1_struct_0(sK0)) | ~m1_subset_1(X1,u1_struct_0(sK0)) | ~r1_lattice3(sK0,k2_relset_1(u1_struct_0(sK1),u1_struct_0(sK0),u1_waybel_0(sK0,sK1)),X1) | ~l1_waybel_0(sK1,sK0) | ~v7_waybel_0(sK1) | ~v4_orders_2(sK1) | v2_struct_0(sK1) | ~l1_pre_topc(sK0) | ~v1_compts_1(sK0) | ~v8_pre_topc(sK0) | ~v2_pre_topc(sK0) | v2_struct_0(sK0)) ) | (~spl9_24 | ~spl9_30)),
% 0.22/0.50    inference(forward_demodulation,[],[f272,f220])).
% 0.22/0.50  fof(f220,plain,(
% 0.22/0.50    k1_waybel_9(sK0,sK1) = sK4(sK0,sK1) | ~spl9_24),
% 0.22/0.50    inference(avatar_component_clause,[],[f219])).
% 0.22/0.50  fof(f272,plain,(
% 0.22/0.50    ( ! [X1] : (~m1_subset_1(k1_waybel_9(sK0,sK1),u1_struct_0(sK0)) | ~m1_subset_1(X1,u1_struct_0(sK0)) | ~r1_lattice3(sK0,k2_relset_1(u1_struct_0(sK1),u1_struct_0(sK0),u1_waybel_0(sK0,sK1)),X1) | r1_orders_2(sK0,X1,sK4(sK0,sK1)) | ~l1_waybel_0(sK1,sK0) | ~v7_waybel_0(sK1) | ~v4_orders_2(sK1) | v2_struct_0(sK1) | ~l1_pre_topc(sK0) | ~v1_compts_1(sK0) | ~v8_pre_topc(sK0) | ~v2_pre_topc(sK0) | v2_struct_0(sK0)) ) | (~spl9_24 | ~spl9_30)),
% 0.22/0.50    inference(forward_demodulation,[],[f266,f220])).
% 0.22/0.50  fof(f266,plain,(
% 0.22/0.50    ( ! [X1] : (~m1_subset_1(X1,u1_struct_0(sK0)) | ~r1_lattice3(sK0,k2_relset_1(u1_struct_0(sK1),u1_struct_0(sK0),u1_waybel_0(sK0,sK1)),X1) | ~m1_subset_1(sK4(sK0,sK1),u1_struct_0(sK0)) | r1_orders_2(sK0,X1,sK4(sK0,sK1)) | ~l1_waybel_0(sK1,sK0) | ~v7_waybel_0(sK1) | ~v4_orders_2(sK1) | v2_struct_0(sK1) | ~l1_pre_topc(sK0) | ~v1_compts_1(sK0) | ~v8_pre_topc(sK0) | ~v2_pre_topc(sK0) | v2_struct_0(sK0)) ) | ~spl9_30),
% 0.22/0.50    inference(resolution,[],[f251,f81])).
% 0.22/0.50  fof(f81,plain,(
% 0.22/0.50    ( ! [X0,X1] : (r3_waybel_9(X0,X1,sK4(X0,X1)) | ~l1_waybel_0(X1,X0) | ~v7_waybel_0(X1) | ~v4_orders_2(X1) | v2_struct_0(X1) | ~l1_pre_topc(X0) | ~v1_compts_1(X0) | ~v8_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 0.22/0.50    inference(cnf_transformation,[],[f44])).
% 0.22/0.50  fof(f44,plain,(
% 0.22/0.50    ! [X0] : (! [X1] : ((r3_waybel_9(X0,X1,sK4(X0,X1)) & m1_subset_1(sK4(X0,X1),u1_struct_0(X0))) | ~l1_waybel_0(X1,X0) | ~v7_waybel_0(X1) | ~v4_orders_2(X1) | v2_struct_0(X1)) | ~l1_pre_topc(X0) | ~v1_compts_1(X0) | ~v8_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 0.22/0.50    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4])],[f25,f43])).
% 0.22/0.50  fof(f43,plain,(
% 0.22/0.50    ! [X1,X0] : (? [X2] : (r3_waybel_9(X0,X1,X2) & m1_subset_1(X2,u1_struct_0(X0))) => (r3_waybel_9(X0,X1,sK4(X0,X1)) & m1_subset_1(sK4(X0,X1),u1_struct_0(X0))))),
% 0.22/0.50    introduced(choice_axiom,[])).
% 0.22/0.50  fof(f25,plain,(
% 0.22/0.50    ! [X0] : (! [X1] : (? [X2] : (r3_waybel_9(X0,X1,X2) & m1_subset_1(X2,u1_struct_0(X0))) | ~l1_waybel_0(X1,X0) | ~v7_waybel_0(X1) | ~v4_orders_2(X1) | v2_struct_0(X1)) | ~l1_pre_topc(X0) | ~v1_compts_1(X0) | ~v8_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 0.22/0.50    inference(flattening,[],[f24])).
% 0.22/0.50  fof(f24,plain,(
% 0.22/0.50    ! [X0] : (! [X1] : (? [X2] : (r3_waybel_9(X0,X1,X2) & m1_subset_1(X2,u1_struct_0(X0))) | (~l1_waybel_0(X1,X0) | ~v7_waybel_0(X1) | ~v4_orders_2(X1) | v2_struct_0(X1))) | (~l1_pre_topc(X0) | ~v1_compts_1(X0) | ~v8_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 0.22/0.50    inference(ennf_transformation,[],[f7])).
% 0.22/0.50  fof(f7,axiom,(
% 0.22/0.50    ! [X0] : ((l1_pre_topc(X0) & v1_compts_1(X0) & v8_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((l1_waybel_0(X1,X0) & v7_waybel_0(X1) & v4_orders_2(X1) & ~v2_struct_0(X1)) => ? [X2] : (r3_waybel_9(X0,X1,X2) & m1_subset_1(X2,u1_struct_0(X0)))))),
% 0.22/0.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t30_waybel_9)).
% 0.22/0.50  fof(f251,plain,(
% 0.22/0.50    ( ! [X0,X1] : (~r3_waybel_9(sK0,sK1,X1) | ~m1_subset_1(X0,u1_struct_0(sK0)) | ~r1_lattice3(sK0,k2_relset_1(u1_struct_0(sK1),u1_struct_0(sK0),u1_waybel_0(sK0,sK1)),X0) | ~m1_subset_1(X1,u1_struct_0(sK0)) | r1_orders_2(sK0,X0,X1)) ) | ~spl9_30),
% 0.22/0.50    inference(avatar_component_clause,[],[f250])).
% 0.22/0.50  fof(f264,plain,(
% 0.22/0.50    ~spl9_4 | spl9_30 | ~spl9_6 | spl9_7 | ~spl9_5 | ~spl9_32),
% 0.22/0.50    inference(avatar_split_clause,[],[f263,f260,f122,f130,f126,f250,f118])).
% 0.22/0.50  fof(f260,plain,(
% 0.22/0.50    spl9_32 <=> ! [X1,X0,X2] : (~r1_lattice3(sK0,k2_relset_1(u1_struct_0(X0),u1_struct_0(sK0),u1_waybel_0(sK0,X0)),X1) | v2_struct_0(X0) | ~v4_orders_2(X0) | ~v7_waybel_0(X0) | ~l1_waybel_0(X0,sK0) | ~m1_subset_1(X2,u1_struct_0(sK0)) | r1_orders_2(sK0,X1,X2) | ~r3_waybel_9(sK0,X0,X2) | ~m1_subset_1(X1,u1_struct_0(sK0)))),
% 0.22/0.50    introduced(avatar_definition,[new_symbols(naming,[spl9_32])])).
% 0.22/0.50  fof(f263,plain,(
% 0.22/0.50    ( ! [X0,X1] : (v2_struct_0(sK1) | ~v4_orders_2(sK1) | ~r1_lattice3(sK0,k2_relset_1(u1_struct_0(sK1),u1_struct_0(sK0),u1_waybel_0(sK0,sK1)),X0) | ~l1_waybel_0(sK1,sK0) | ~m1_subset_1(X1,u1_struct_0(sK0)) | r1_orders_2(sK0,X0,X1) | ~r3_waybel_9(sK0,sK1,X1) | ~m1_subset_1(X0,u1_struct_0(sK0))) ) | (~spl9_5 | ~spl9_32)),
% 0.22/0.50    inference(resolution,[],[f261,f123])).
% 0.22/0.50  fof(f123,plain,(
% 0.22/0.50    v7_waybel_0(sK1) | ~spl9_5),
% 0.22/0.50    inference(avatar_component_clause,[],[f122])).
% 0.22/0.50  fof(f261,plain,(
% 0.22/0.50    ( ! [X2,X0,X1] : (~v7_waybel_0(X0) | v2_struct_0(X0) | ~v4_orders_2(X0) | ~r1_lattice3(sK0,k2_relset_1(u1_struct_0(X0),u1_struct_0(sK0),u1_waybel_0(sK0,X0)),X1) | ~l1_waybel_0(X0,sK0) | ~m1_subset_1(X2,u1_struct_0(sK0)) | r1_orders_2(sK0,X1,X2) | ~r3_waybel_9(sK0,X0,X2) | ~m1_subset_1(X1,u1_struct_0(sK0))) ) | ~spl9_32),
% 0.22/0.50    inference(avatar_component_clause,[],[f260])).
% 0.22/0.50  fof(f262,plain,(
% 0.22/0.50    ~spl9_16 | ~spl9_15 | ~spl9_14 | ~spl9_13 | ~spl9_12 | ~spl9_11 | ~spl9_10 | ~spl9_9 | ~spl9_8 | spl9_32 | spl9_31),
% 0.22/0.50    inference(avatar_split_clause,[],[f258,f255,f260,f134,f138,f142,f146,f150,f154,f158,f162,f166])).
% 0.22/0.50  fof(f255,plain,(
% 0.22/0.50    spl9_31 <=> m1_subset_1(sK8(sK0),u1_struct_0(sK0))),
% 0.22/0.50    introduced(avatar_definition,[new_symbols(naming,[spl9_31])])).
% 0.22/0.50  fof(f258,plain,(
% 0.22/0.50    ( ! [X2,X0,X1] : (~r1_lattice3(sK0,k2_relset_1(u1_struct_0(X0),u1_struct_0(sK0),u1_waybel_0(sK0,X0)),X1) | ~m1_subset_1(X1,u1_struct_0(sK0)) | ~r3_waybel_9(sK0,X0,X2) | r1_orders_2(sK0,X1,X2) | ~m1_subset_1(X2,u1_struct_0(sK0)) | ~l1_waybel_0(X0,sK0) | ~v7_waybel_0(X0) | ~v4_orders_2(X0) | v2_struct_0(X0) | ~l1_waybel_9(sK0) | ~v1_compts_1(sK0) | ~v2_lattice3(sK0) | ~v1_lattice3(sK0) | ~v5_orders_2(sK0) | ~v4_orders_2(sK0) | ~v3_orders_2(sK0) | ~v8_pre_topc(sK0) | ~v2_pre_topc(sK0)) ) | spl9_31),
% 0.22/0.50    inference(resolution,[],[f256,f102])).
% 0.22/0.50  fof(f102,plain,(
% 0.22/0.50    ( ! [X4,X0,X3,X1] : (m1_subset_1(sK8(X0),u1_struct_0(X0)) | ~r1_lattice3(X0,k2_relset_1(u1_struct_0(X1),u1_struct_0(X0),u1_waybel_0(X0,X1)),X4) | ~m1_subset_1(X4,u1_struct_0(X0)) | ~r3_waybel_9(X0,X1,X3) | r1_orders_2(X0,X4,X3) | ~m1_subset_1(X3,u1_struct_0(X0)) | ~l1_waybel_0(X1,X0) | ~v7_waybel_0(X1) | ~v4_orders_2(X1) | v2_struct_0(X1) | ~l1_waybel_9(X0) | ~v1_compts_1(X0) | ~v2_lattice3(X0) | ~v1_lattice3(X0) | ~v5_orders_2(X0) | ~v4_orders_2(X0) | ~v3_orders_2(X0) | ~v8_pre_topc(X0) | ~v2_pre_topc(X0)) )),
% 0.22/0.50    inference(duplicate_literal_removal,[],[f101])).
% 0.22/0.50  fof(f101,plain,(
% 0.22/0.50    ( ! [X4,X0,X3,X1] : (r1_orders_2(X0,X4,X3) | ~r1_lattice3(X0,k2_relset_1(u1_struct_0(X1),u1_struct_0(X0),u1_waybel_0(X0,X1)),X4) | ~m1_subset_1(X4,u1_struct_0(X0)) | ~r3_waybel_9(X0,X1,X3) | m1_subset_1(sK8(X0),u1_struct_0(X0)) | ~m1_subset_1(X3,u1_struct_0(X0)) | ~m1_subset_1(X3,u1_struct_0(X0)) | ~l1_waybel_0(X1,X0) | ~v7_waybel_0(X1) | ~v4_orders_2(X1) | v2_struct_0(X1) | ~l1_waybel_9(X0) | ~v1_compts_1(X0) | ~v2_lattice3(X0) | ~v1_lattice3(X0) | ~v5_orders_2(X0) | ~v4_orders_2(X0) | ~v3_orders_2(X0) | ~v8_pre_topc(X0) | ~v2_pre_topc(X0)) )),
% 0.22/0.50    inference(equality_resolution,[],[f94])).
% 0.22/0.50  fof(f94,plain,(
% 0.22/0.50    ( ! [X4,X2,X0,X3,X1] : (r1_orders_2(X0,X4,X3) | ~r1_lattice3(X0,k2_relset_1(u1_struct_0(X1),u1_struct_0(X0),u1_waybel_0(X0,X1)),X4) | ~m1_subset_1(X4,u1_struct_0(X0)) | ~r3_waybel_9(X0,X1,X2) | m1_subset_1(sK8(X0),u1_struct_0(X0)) | X2 != X3 | ~m1_subset_1(X3,u1_struct_0(X0)) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~l1_waybel_0(X1,X0) | ~v7_waybel_0(X1) | ~v4_orders_2(X1) | v2_struct_0(X1) | ~l1_waybel_9(X0) | ~v1_compts_1(X0) | ~v2_lattice3(X0) | ~v1_lattice3(X0) | ~v5_orders_2(X0) | ~v4_orders_2(X0) | ~v3_orders_2(X0) | ~v8_pre_topc(X0) | ~v2_pre_topc(X0)) )),
% 0.22/0.50    inference(cnf_transformation,[],[f53])).
% 0.22/0.50  fof(f53,plain,(
% 0.22/0.50    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (! [X4] : (r1_orders_2(X0,X4,X3) | ~r1_lattice3(X0,k2_relset_1(u1_struct_0(X1),u1_struct_0(X0),u1_waybel_0(X0,X1)),X4) | ~m1_subset_1(X4,u1_struct_0(X0))) | ~r3_waybel_9(X0,X1,X2) | (~v5_pre_topc(k4_waybel_1(X0,sK8(X0)),X0,X0) & m1_subset_1(sK8(X0),u1_struct_0(X0))) | X2 != X3 | ~m1_subset_1(X3,u1_struct_0(X0))) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~l1_waybel_0(X1,X0) | ~v7_waybel_0(X1) | ~v4_orders_2(X1) | v2_struct_0(X1)) | ~l1_waybel_9(X0) | ~v1_compts_1(X0) | ~v2_lattice3(X0) | ~v1_lattice3(X0) | ~v5_orders_2(X0) | ~v4_orders_2(X0) | ~v3_orders_2(X0) | ~v8_pre_topc(X0) | ~v2_pre_topc(X0))),
% 0.22/0.50    inference(skolemisation,[status(esa),new_symbols(skolem,[sK8])],[f51,f52])).
% 0.22/0.50  fof(f52,plain,(
% 0.22/0.50    ! [X0] : (? [X5] : (~v5_pre_topc(k4_waybel_1(X0,X5),X0,X0) & m1_subset_1(X5,u1_struct_0(X0))) => (~v5_pre_topc(k4_waybel_1(X0,sK8(X0)),X0,X0) & m1_subset_1(sK8(X0),u1_struct_0(X0))))),
% 0.22/0.50    introduced(choice_axiom,[])).
% 0.22/0.50  fof(f51,plain,(
% 0.22/0.50    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (! [X4] : (r1_orders_2(X0,X4,X3) | ~r1_lattice3(X0,k2_relset_1(u1_struct_0(X1),u1_struct_0(X0),u1_waybel_0(X0,X1)),X4) | ~m1_subset_1(X4,u1_struct_0(X0))) | ~r3_waybel_9(X0,X1,X2) | ? [X5] : (~v5_pre_topc(k4_waybel_1(X0,X5),X0,X0) & m1_subset_1(X5,u1_struct_0(X0))) | X2 != X3 | ~m1_subset_1(X3,u1_struct_0(X0))) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~l1_waybel_0(X1,X0) | ~v7_waybel_0(X1) | ~v4_orders_2(X1) | v2_struct_0(X1)) | ~l1_waybel_9(X0) | ~v1_compts_1(X0) | ~v2_lattice3(X0) | ~v1_lattice3(X0) | ~v5_orders_2(X0) | ~v4_orders_2(X0) | ~v3_orders_2(X0) | ~v8_pre_topc(X0) | ~v2_pre_topc(X0))),
% 0.22/0.50    inference(rectify,[],[f33])).
% 0.22/0.50  fof(f33,plain,(
% 0.22/0.50    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (! [X5] : (r1_orders_2(X0,X5,X3) | ~r1_lattice3(X0,k2_relset_1(u1_struct_0(X1),u1_struct_0(X0),u1_waybel_0(X0,X1)),X5) | ~m1_subset_1(X5,u1_struct_0(X0))) | ~r3_waybel_9(X0,X1,X2) | ? [X4] : (~v5_pre_topc(k4_waybel_1(X0,X4),X0,X0) & m1_subset_1(X4,u1_struct_0(X0))) | X2 != X3 | ~m1_subset_1(X3,u1_struct_0(X0))) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~l1_waybel_0(X1,X0) | ~v7_waybel_0(X1) | ~v4_orders_2(X1) | v2_struct_0(X1)) | ~l1_waybel_9(X0) | ~v1_compts_1(X0) | ~v2_lattice3(X0) | ~v1_lattice3(X0) | ~v5_orders_2(X0) | ~v4_orders_2(X0) | ~v3_orders_2(X0) | ~v8_pre_topc(X0) | ~v2_pre_topc(X0))),
% 0.22/0.50    inference(flattening,[],[f32])).
% 0.22/0.50  fof(f32,plain,(
% 0.22/0.50    ! [X0] : (! [X1] : (! [X2] : (! [X3] : ((! [X5] : ((r1_orders_2(X0,X5,X3) | ~r1_lattice3(X0,k2_relset_1(u1_struct_0(X1),u1_struct_0(X0),u1_waybel_0(X0,X1)),X5)) | ~m1_subset_1(X5,u1_struct_0(X0))) | (~r3_waybel_9(X0,X1,X2) | ? [X4] : (~v5_pre_topc(k4_waybel_1(X0,X4),X0,X0) & m1_subset_1(X4,u1_struct_0(X0))) | X2 != X3)) | ~m1_subset_1(X3,u1_struct_0(X0))) | ~m1_subset_1(X2,u1_struct_0(X0))) | (~l1_waybel_0(X1,X0) | ~v7_waybel_0(X1) | ~v4_orders_2(X1) | v2_struct_0(X1))) | (~l1_waybel_9(X0) | ~v1_compts_1(X0) | ~v2_lattice3(X0) | ~v1_lattice3(X0) | ~v5_orders_2(X0) | ~v4_orders_2(X0) | ~v3_orders_2(X0) | ~v8_pre_topc(X0) | ~v2_pre_topc(X0)))),
% 0.22/0.50    inference(ennf_transformation,[],[f15])).
% 0.22/0.50  fof(f15,plain,(
% 0.22/0.50    ! [X0] : ((l1_waybel_9(X0) & v1_compts_1(X0) & v2_lattice3(X0) & v1_lattice3(X0) & v5_orders_2(X0) & v4_orders_2(X0) & v3_orders_2(X0) & v8_pre_topc(X0) & v2_pre_topc(X0)) => ! [X1] : ((l1_waybel_0(X1,X0) & v7_waybel_0(X1) & v4_orders_2(X1) & ~v2_struct_0(X1)) => ! [X2] : (m1_subset_1(X2,u1_struct_0(X0)) => ! [X3] : (m1_subset_1(X3,u1_struct_0(X0)) => ((r3_waybel_9(X0,X1,X2) & ! [X4] : (m1_subset_1(X4,u1_struct_0(X0)) => v5_pre_topc(k4_waybel_1(X0,X4),X0,X0)) & X2 = X3) => ! [X5] : (m1_subset_1(X5,u1_struct_0(X0)) => (r1_lattice3(X0,k2_relset_1(u1_struct_0(X1),u1_struct_0(X0),u1_waybel_0(X0,X1)),X5) => r1_orders_2(X0,X5,X3))))))))),
% 0.22/0.50    inference(rectify,[],[f6])).
% 0.22/0.50  fof(f6,axiom,(
% 0.22/0.50    ! [X0] : ((l1_waybel_9(X0) & v1_compts_1(X0) & v2_lattice3(X0) & v1_lattice3(X0) & v5_orders_2(X0) & v4_orders_2(X0) & v3_orders_2(X0) & v8_pre_topc(X0) & v2_pre_topc(X0)) => ! [X1] : ((l1_waybel_0(X1,X0) & v7_waybel_0(X1) & v4_orders_2(X1) & ~v2_struct_0(X1)) => ! [X2] : (m1_subset_1(X2,u1_struct_0(X0)) => ! [X3] : (m1_subset_1(X3,u1_struct_0(X0)) => ((r3_waybel_9(X0,X1,X2) & ! [X4] : (m1_subset_1(X4,u1_struct_0(X0)) => v5_pre_topc(k4_waybel_1(X0,X4),X0,X0)) & X2 = X3) => ! [X4] : (m1_subset_1(X4,u1_struct_0(X0)) => (r1_lattice3(X0,k2_relset_1(u1_struct_0(X1),u1_struct_0(X0),u1_waybel_0(X0,X1)),X4) => r1_orders_2(X0,X4,X3))))))))),
% 0.22/0.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l52_waybel_9)).
% 0.22/0.50  fof(f256,plain,(
% 0.22/0.50    ~m1_subset_1(sK8(sK0),u1_struct_0(sK0)) | spl9_31),
% 0.22/0.50    inference(avatar_component_clause,[],[f255])).
% 0.22/0.50  fof(f257,plain,(
% 0.22/0.50    ~spl9_31 | spl9_29),
% 0.22/0.50    inference(avatar_split_clause,[],[f253,f247,f255])).
% 0.22/0.50  fof(f247,plain,(
% 0.22/0.50    spl9_29 <=> v5_pre_topc(k4_waybel_1(sK0,sK8(sK0)),sK0,sK0)),
% 0.22/0.50    introduced(avatar_definition,[new_symbols(naming,[spl9_29])])).
% 0.22/0.50  fof(f253,plain,(
% 0.22/0.50    ~m1_subset_1(sK8(sK0),u1_struct_0(sK0)) | spl9_29),
% 0.22/0.50    inference(resolution,[],[f248,f63])).
% 0.22/0.50  fof(f248,plain,(
% 0.22/0.50    ~v5_pre_topc(k4_waybel_1(sK0,sK8(sK0)),sK0,sK0) | spl9_29),
% 0.22/0.50    inference(avatar_component_clause,[],[f247])).
% 0.22/0.50  fof(f252,plain,(
% 0.22/0.50    ~spl9_29 | ~spl9_4 | ~spl9_8 | spl9_30 | ~spl9_10 | ~spl9_11 | ~spl9_12 | ~spl9_13 | ~spl9_14 | ~spl9_15 | ~spl9_16 | ~spl9_9 | ~spl9_28),
% 0.22/0.50    inference(avatar_split_clause,[],[f245,f242,f138,f166,f162,f158,f154,f150,f146,f142,f250,f134,f118,f247])).
% 0.22/0.50  fof(f242,plain,(
% 0.22/0.50    spl9_28 <=> ! [X1,X0,X2] : (~r1_lattice3(X0,k2_relset_1(u1_struct_0(sK1),u1_struct_0(X0),u1_waybel_0(X0,sK1)),X1) | ~v2_pre_topc(X0) | ~v8_pre_topc(X0) | ~v3_orders_2(X0) | ~v4_orders_2(X0) | ~v5_orders_2(X0) | ~v1_lattice3(X0) | ~v2_lattice3(X0) | ~v1_compts_1(X0) | ~l1_waybel_9(X0) | r1_orders_2(X0,X1,X2) | ~l1_waybel_0(sK1,X0) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~v5_pre_topc(k4_waybel_1(X0,sK8(X0)),X0,X0) | ~r3_waybel_9(X0,sK1,X2) | ~m1_subset_1(X1,u1_struct_0(X0)))),
% 0.22/0.50    introduced(avatar_definition,[new_symbols(naming,[spl9_28])])).
% 0.22/0.50  fof(f245,plain,(
% 0.22/0.50    ( ! [X0,X1] : (~v2_pre_topc(sK0) | ~v8_pre_topc(sK0) | ~v3_orders_2(sK0) | ~v4_orders_2(sK0) | ~v5_orders_2(sK0) | ~v1_lattice3(sK0) | ~v2_lattice3(sK0) | ~r1_lattice3(sK0,k2_relset_1(u1_struct_0(sK1),u1_struct_0(sK0),u1_waybel_0(sK0,sK1)),X0) | ~l1_waybel_9(sK0) | r1_orders_2(sK0,X0,X1) | ~l1_waybel_0(sK1,sK0) | ~m1_subset_1(X1,u1_struct_0(sK0)) | ~v5_pre_topc(k4_waybel_1(sK0,sK8(sK0)),sK0,sK0) | ~r3_waybel_9(sK0,sK1,X1) | ~m1_subset_1(X0,u1_struct_0(sK0))) ) | (~spl9_9 | ~spl9_28)),
% 0.22/0.50    inference(resolution,[],[f243,f139])).
% 0.22/0.50  fof(f139,plain,(
% 0.22/0.50    v1_compts_1(sK0) | ~spl9_9),
% 0.22/0.50    inference(avatar_component_clause,[],[f138])).
% 0.22/0.50  fof(f243,plain,(
% 0.22/0.50    ( ! [X2,X0,X1] : (~v1_compts_1(X0) | ~v2_pre_topc(X0) | ~v8_pre_topc(X0) | ~v3_orders_2(X0) | ~v4_orders_2(X0) | ~v5_orders_2(X0) | ~v1_lattice3(X0) | ~v2_lattice3(X0) | ~r1_lattice3(X0,k2_relset_1(u1_struct_0(sK1),u1_struct_0(X0),u1_waybel_0(X0,sK1)),X1) | ~l1_waybel_9(X0) | r1_orders_2(X0,X1,X2) | ~l1_waybel_0(sK1,X0) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~v5_pre_topc(k4_waybel_1(X0,sK8(X0)),X0,X0) | ~r3_waybel_9(X0,sK1,X2) | ~m1_subset_1(X1,u1_struct_0(X0))) ) | ~spl9_28),
% 0.22/0.50    inference(avatar_component_clause,[],[f242])).
% 0.22/0.50  fof(f244,plain,(
% 0.22/0.50    spl9_7 | ~spl9_6 | spl9_28 | ~spl9_5),
% 0.22/0.50    inference(avatar_split_clause,[],[f240,f122,f242,f126,f130])).
% 0.22/0.50  fof(f240,plain,(
% 0.22/0.50    ( ! [X2,X0,X1] : (~r1_lattice3(X0,k2_relset_1(u1_struct_0(sK1),u1_struct_0(X0),u1_waybel_0(X0,sK1)),X1) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~r3_waybel_9(X0,sK1,X2) | ~v5_pre_topc(k4_waybel_1(X0,sK8(X0)),X0,X0) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~l1_waybel_0(sK1,X0) | r1_orders_2(X0,X1,X2) | ~v4_orders_2(sK1) | v2_struct_0(sK1) | ~l1_waybel_9(X0) | ~v1_compts_1(X0) | ~v2_lattice3(X0) | ~v1_lattice3(X0) | ~v5_orders_2(X0) | ~v4_orders_2(X0) | ~v3_orders_2(X0) | ~v8_pre_topc(X0) | ~v2_pre_topc(X0)) ) | ~spl9_5),
% 0.22/0.50    inference(resolution,[],[f103,f123])).
% 0.22/0.50  fof(f103,plain,(
% 0.22/0.50    ( ! [X4,X0,X3,X1] : (~v7_waybel_0(X1) | ~r1_lattice3(X0,k2_relset_1(u1_struct_0(X1),u1_struct_0(X0),u1_waybel_0(X0,X1)),X4) | ~m1_subset_1(X4,u1_struct_0(X0)) | ~r3_waybel_9(X0,X1,X3) | ~v5_pre_topc(k4_waybel_1(X0,sK8(X0)),X0,X0) | ~m1_subset_1(X3,u1_struct_0(X0)) | ~l1_waybel_0(X1,X0) | r1_orders_2(X0,X4,X3) | ~v4_orders_2(X1) | v2_struct_0(X1) | ~l1_waybel_9(X0) | ~v1_compts_1(X0) | ~v2_lattice3(X0) | ~v1_lattice3(X0) | ~v5_orders_2(X0) | ~v4_orders_2(X0) | ~v3_orders_2(X0) | ~v8_pre_topc(X0) | ~v2_pre_topc(X0)) )),
% 0.22/0.50    inference(duplicate_literal_removal,[],[f100])).
% 0.22/0.50  fof(f100,plain,(
% 0.22/0.50    ( ! [X4,X0,X3,X1] : (r1_orders_2(X0,X4,X3) | ~r1_lattice3(X0,k2_relset_1(u1_struct_0(X1),u1_struct_0(X0),u1_waybel_0(X0,X1)),X4) | ~m1_subset_1(X4,u1_struct_0(X0)) | ~r3_waybel_9(X0,X1,X3) | ~v5_pre_topc(k4_waybel_1(X0,sK8(X0)),X0,X0) | ~m1_subset_1(X3,u1_struct_0(X0)) | ~m1_subset_1(X3,u1_struct_0(X0)) | ~l1_waybel_0(X1,X0) | ~v7_waybel_0(X1) | ~v4_orders_2(X1) | v2_struct_0(X1) | ~l1_waybel_9(X0) | ~v1_compts_1(X0) | ~v2_lattice3(X0) | ~v1_lattice3(X0) | ~v5_orders_2(X0) | ~v4_orders_2(X0) | ~v3_orders_2(X0) | ~v8_pre_topc(X0) | ~v2_pre_topc(X0)) )),
% 0.22/0.50    inference(equality_resolution,[],[f95])).
% 0.22/0.50  fof(f95,plain,(
% 0.22/0.50    ( ! [X4,X2,X0,X3,X1] : (r1_orders_2(X0,X4,X3) | ~r1_lattice3(X0,k2_relset_1(u1_struct_0(X1),u1_struct_0(X0),u1_waybel_0(X0,X1)),X4) | ~m1_subset_1(X4,u1_struct_0(X0)) | ~r3_waybel_9(X0,X1,X2) | ~v5_pre_topc(k4_waybel_1(X0,sK8(X0)),X0,X0) | X2 != X3 | ~m1_subset_1(X3,u1_struct_0(X0)) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~l1_waybel_0(X1,X0) | ~v7_waybel_0(X1) | ~v4_orders_2(X1) | v2_struct_0(X1) | ~l1_waybel_9(X0) | ~v1_compts_1(X0) | ~v2_lattice3(X0) | ~v1_lattice3(X0) | ~v5_orders_2(X0) | ~v4_orders_2(X0) | ~v3_orders_2(X0) | ~v8_pre_topc(X0) | ~v2_pre_topc(X0)) )),
% 0.22/0.50    inference(cnf_transformation,[],[f53])).
% 0.22/0.50  fof(f238,plain,(
% 0.22/0.50    spl9_22 | ~spl9_16 | ~spl9_15 | ~spl9_9 | ~spl9_23 | spl9_7 | ~spl9_6 | ~spl9_5 | ~spl9_4 | spl9_27 | ~spl9_24),
% 0.22/0.50    inference(avatar_split_clause,[],[f230,f219,f236,f118,f122,f126,f130,f216,f138,f162,f166,f213])).
% 0.22/0.50  fof(f230,plain,(
% 0.22/0.50    m1_subset_1(k1_waybel_9(sK0,sK1),u1_struct_0(sK0)) | ~l1_waybel_0(sK1,sK0) | ~v7_waybel_0(sK1) | ~v4_orders_2(sK1) | v2_struct_0(sK1) | ~l1_pre_topc(sK0) | ~v1_compts_1(sK0) | ~v8_pre_topc(sK0) | ~v2_pre_topc(sK0) | v2_struct_0(sK0) | ~spl9_24),
% 0.22/0.50    inference(superposition,[],[f80,f220])).
% 0.22/0.50  fof(f80,plain,(
% 0.22/0.50    ( ! [X0,X1] : (m1_subset_1(sK4(X0,X1),u1_struct_0(X0)) | ~l1_waybel_0(X1,X0) | ~v7_waybel_0(X1) | ~v4_orders_2(X1) | v2_struct_0(X1) | ~l1_pre_topc(X0) | ~v1_compts_1(X0) | ~v8_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 0.22/0.50    inference(cnf_transformation,[],[f44])).
% 0.22/0.50  fof(f234,plain,(
% 0.22/0.50    spl9_22 | ~spl9_16 | ~spl9_15 | ~spl9_9 | ~spl9_23 | spl9_7 | ~spl9_6 | ~spl9_5 | ~spl9_4 | spl9_26 | ~spl9_24),
% 0.22/0.50    inference(avatar_split_clause,[],[f229,f219,f232,f118,f122,f126,f130,f216,f138,f162,f166,f213])).
% 0.22/0.50  fof(f229,plain,(
% 0.22/0.50    r3_waybel_9(sK0,sK1,k1_waybel_9(sK0,sK1)) | ~l1_waybel_0(sK1,sK0) | ~v7_waybel_0(sK1) | ~v4_orders_2(sK1) | v2_struct_0(sK1) | ~l1_pre_topc(sK0) | ~v1_compts_1(sK0) | ~v8_pre_topc(sK0) | ~v2_pre_topc(sK0) | v2_struct_0(sK0) | ~spl9_24),
% 0.22/0.50    inference(superposition,[],[f81,f220])).
% 0.22/0.50  fof(f228,plain,(
% 0.22/0.50    spl9_22 | ~spl9_16 | ~spl9_15 | ~spl9_9 | ~spl9_23 | spl9_7 | ~spl9_6 | ~spl9_5 | ~spl9_4 | spl9_25),
% 0.22/0.50    inference(avatar_split_clause,[],[f227,f222,f118,f122,f126,f130,f216,f138,f162,f166,f213])).
% 0.22/0.50  fof(f222,plain,(
% 0.22/0.50    spl9_25 <=> m1_subset_1(sK4(sK0,sK1),u1_struct_0(sK0))),
% 0.22/0.50    introduced(avatar_definition,[new_symbols(naming,[spl9_25])])).
% 0.22/0.50  % (30175)dis+11_2:1_add=large:afp=4000:afq=1.4:amm=sco:anc=none:fsr=off:nm=16:nwc=1:sd=3:ss=axioms:st=1.2:sos=all:urr=ec_only:updr=off_2 on theBenchmark
% 0.22/0.50  fof(f227,plain,(
% 0.22/0.50    ~l1_waybel_0(sK1,sK0) | ~v7_waybel_0(sK1) | ~v4_orders_2(sK1) | v2_struct_0(sK1) | ~l1_pre_topc(sK0) | ~v1_compts_1(sK0) | ~v8_pre_topc(sK0) | ~v2_pre_topc(sK0) | v2_struct_0(sK0) | spl9_25),
% 0.22/0.50    inference(resolution,[],[f223,f80])).
% 0.22/0.50  fof(f223,plain,(
% 0.22/0.50    ~m1_subset_1(sK4(sK0,sK1),u1_struct_0(sK0)) | spl9_25),
% 0.22/0.50    inference(avatar_component_clause,[],[f222])).
% 0.22/0.50  fof(f226,plain,(
% 0.22/0.50    ~spl9_8 | spl9_23),
% 0.22/0.50    inference(avatar_split_clause,[],[f225,f216,f134])).
% 0.22/0.50  fof(f225,plain,(
% 0.22/0.50    ~l1_waybel_9(sK0) | spl9_23),
% 0.22/0.50    inference(resolution,[],[f217,f73])).
% 0.22/0.50  fof(f73,plain,(
% 0.22/0.50    ( ! [X0] : (l1_pre_topc(X0) | ~l1_waybel_9(X0)) )),
% 0.22/0.50    inference(cnf_transformation,[],[f21])).
% 0.22/0.50  fof(f217,plain,(
% 0.22/0.50    ~l1_pre_topc(sK0) | spl9_23),
% 0.22/0.50    inference(avatar_component_clause,[],[f216])).
% 0.22/0.50  fof(f224,plain,(
% 0.22/0.50    spl9_22 | ~spl9_16 | ~spl9_15 | ~spl9_9 | ~spl9_23 | spl9_7 | ~spl9_6 | ~spl9_5 | ~spl9_4 | spl9_24 | ~spl9_25 | ~spl9_19),
% 0.22/0.50    inference(avatar_split_clause,[],[f211,f186,f222,f219,f118,f122,f126,f130,f216,f138,f162,f166,f213])).
% 0.22/0.50  fof(f211,plain,(
% 0.22/0.50    ~m1_subset_1(sK4(sK0,sK1),u1_struct_0(sK0)) | k1_waybel_9(sK0,sK1) = sK4(sK0,sK1) | ~l1_waybel_0(sK1,sK0) | ~v7_waybel_0(sK1) | ~v4_orders_2(sK1) | v2_struct_0(sK1) | ~l1_pre_topc(sK0) | ~v1_compts_1(sK0) | ~v8_pre_topc(sK0) | ~v2_pre_topc(sK0) | v2_struct_0(sK0) | ~spl9_19),
% 0.22/0.50    inference(resolution,[],[f187,f81])).
% 0.22/0.50  fof(f210,plain,(
% 0.22/0.50    ~spl9_4 | ~spl9_5 | ~spl9_6 | spl9_7 | spl9_19 | ~spl9_3 | ~spl9_21),
% 0.22/0.50    inference(avatar_split_clause,[],[f208,f205,f114,f186,f130,f126,f122,f118])).
% 0.22/0.50  fof(f205,plain,(
% 0.22/0.50    spl9_21 <=> ! [X1,X0] : (~r3_waybel_9(sK0,X0,X1) | ~m1_subset_1(X1,u1_struct_0(sK0)) | v2_struct_0(X0) | ~v4_orders_2(X0) | ~v7_waybel_0(X0) | ~l1_waybel_0(X0,sK0) | k1_waybel_9(sK0,X0) = X1 | ~v11_waybel_0(X0,sK0))),
% 0.22/0.50    introduced(avatar_definition,[new_symbols(naming,[spl9_21])])).
% 0.22/0.50  fof(f208,plain,(
% 0.22/0.50    ( ! [X0] : (~m1_subset_1(X0,u1_struct_0(sK0)) | v2_struct_0(sK1) | ~v4_orders_2(sK1) | ~v7_waybel_0(sK1) | ~l1_waybel_0(sK1,sK0) | k1_waybel_9(sK0,sK1) = X0 | ~r3_waybel_9(sK0,sK1,X0)) ) | (~spl9_3 | ~spl9_21)),
% 0.22/0.50    inference(resolution,[],[f206,f115])).
% 0.22/0.50  fof(f206,plain,(
% 0.22/0.50    ( ! [X0,X1] : (~v11_waybel_0(X0,sK0) | ~m1_subset_1(X1,u1_struct_0(sK0)) | v2_struct_0(X0) | ~v4_orders_2(X0) | ~v7_waybel_0(X0) | ~l1_waybel_0(X0,sK0) | k1_waybel_9(sK0,X0) = X1 | ~r3_waybel_9(sK0,X0,X1)) ) | ~spl9_21),
% 0.22/0.50    inference(avatar_component_clause,[],[f205])).
% 0.22/0.50  fof(f207,plain,(
% 0.22/0.50    ~spl9_16 | ~spl9_15 | ~spl9_14 | ~spl9_13 | ~spl9_12 | ~spl9_11 | ~spl9_10 | ~spl9_9 | ~spl9_8 | spl9_21 | spl9_20),
% 0.22/0.50    inference(avatar_split_clause,[],[f203,f200,f205,f134,f138,f142,f146,f150,f154,f158,f162,f166])).
% 0.22/0.50  fof(f200,plain,(
% 0.22/0.50    spl9_20 <=> m1_subset_1(sK6(sK0),u1_struct_0(sK0))),
% 0.22/0.50    introduced(avatar_definition,[new_symbols(naming,[spl9_20])])).
% 0.22/0.50  fof(f203,plain,(
% 0.22/0.50    ( ! [X0,X1] : (~r3_waybel_9(sK0,X0,X1) | ~v11_waybel_0(X0,sK0) | k1_waybel_9(sK0,X0) = X1 | ~l1_waybel_0(X0,sK0) | ~v7_waybel_0(X0) | ~v4_orders_2(X0) | v2_struct_0(X0) | ~m1_subset_1(X1,u1_struct_0(sK0)) | ~l1_waybel_9(sK0) | ~v1_compts_1(sK0) | ~v2_lattice3(sK0) | ~v1_lattice3(sK0) | ~v5_orders_2(sK0) | ~v4_orders_2(sK0) | ~v3_orders_2(sK0) | ~v8_pre_topc(sK0) | ~v2_pre_topc(sK0)) ) | spl9_20),
% 0.22/0.50    inference(resolution,[],[f201,f90])).
% 0.22/0.50  fof(f90,plain,(
% 0.22/0.50    ( ! [X2,X0,X1] : (m1_subset_1(sK6(X0),u1_struct_0(X0)) | ~r3_waybel_9(X0,X2,X1) | ~v11_waybel_0(X2,X0) | k1_waybel_9(X0,X2) = X1 | ~l1_waybel_0(X2,X0) | ~v7_waybel_0(X2) | ~v4_orders_2(X2) | v2_struct_0(X2) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_waybel_9(X0) | ~v1_compts_1(X0) | ~v2_lattice3(X0) | ~v1_lattice3(X0) | ~v5_orders_2(X0) | ~v4_orders_2(X0) | ~v3_orders_2(X0) | ~v8_pre_topc(X0) | ~v2_pre_topc(X0)) )),
% 0.22/0.50    inference(cnf_transformation,[],[f48])).
% 0.22/0.50  fof(f48,plain,(
% 0.22/0.50    ! [X0] : (! [X1] : (! [X2] : (k1_waybel_9(X0,X2) = X1 | ~r3_waybel_9(X0,X2,X1) | ~v11_waybel_0(X2,X0) | (~v5_pre_topc(k4_waybel_1(X0,sK6(X0)),X0,X0) & m1_subset_1(sK6(X0),u1_struct_0(X0))) | ~l1_waybel_0(X2,X0) | ~v7_waybel_0(X2) | ~v4_orders_2(X2) | v2_struct_0(X2)) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~l1_waybel_9(X0) | ~v1_compts_1(X0) | ~v2_lattice3(X0) | ~v1_lattice3(X0) | ~v5_orders_2(X0) | ~v4_orders_2(X0) | ~v3_orders_2(X0) | ~v8_pre_topc(X0) | ~v2_pre_topc(X0))),
% 0.22/0.50    inference(skolemisation,[status(esa),new_symbols(skolem,[sK6])],[f29,f47])).
% 0.22/0.50  fof(f47,plain,(
% 0.22/0.50    ! [X0] : (? [X3] : (~v5_pre_topc(k4_waybel_1(X0,X3),X0,X0) & m1_subset_1(X3,u1_struct_0(X0))) => (~v5_pre_topc(k4_waybel_1(X0,sK6(X0)),X0,X0) & m1_subset_1(sK6(X0),u1_struct_0(X0))))),
% 0.22/0.50    introduced(choice_axiom,[])).
% 0.22/0.50  fof(f29,plain,(
% 0.22/0.50    ! [X0] : (! [X1] : (! [X2] : (k1_waybel_9(X0,X2) = X1 | ~r3_waybel_9(X0,X2,X1) | ~v11_waybel_0(X2,X0) | ? [X3] : (~v5_pre_topc(k4_waybel_1(X0,X3),X0,X0) & m1_subset_1(X3,u1_struct_0(X0))) | ~l1_waybel_0(X2,X0) | ~v7_waybel_0(X2) | ~v4_orders_2(X2) | v2_struct_0(X2)) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~l1_waybel_9(X0) | ~v1_compts_1(X0) | ~v2_lattice3(X0) | ~v1_lattice3(X0) | ~v5_orders_2(X0) | ~v4_orders_2(X0) | ~v3_orders_2(X0) | ~v8_pre_topc(X0) | ~v2_pre_topc(X0))),
% 0.22/0.50    inference(flattening,[],[f28])).
% 0.22/0.50  fof(f28,plain,(
% 0.22/0.50    ! [X0] : (! [X1] : (! [X2] : ((k1_waybel_9(X0,X2) = X1 | (~r3_waybel_9(X0,X2,X1) | ~v11_waybel_0(X2,X0) | ? [X3] : (~v5_pre_topc(k4_waybel_1(X0,X3),X0,X0) & m1_subset_1(X3,u1_struct_0(X0))))) | (~l1_waybel_0(X2,X0) | ~v7_waybel_0(X2) | ~v4_orders_2(X2) | v2_struct_0(X2))) | ~m1_subset_1(X1,u1_struct_0(X0))) | (~l1_waybel_9(X0) | ~v1_compts_1(X0) | ~v2_lattice3(X0) | ~v1_lattice3(X0) | ~v5_orders_2(X0) | ~v4_orders_2(X0) | ~v3_orders_2(X0) | ~v8_pre_topc(X0) | ~v2_pre_topc(X0)))),
% 0.22/0.50    inference(ennf_transformation,[],[f9])).
% 0.22/0.50  fof(f9,axiom,(
% 0.22/0.50    ! [X0] : ((l1_waybel_9(X0) & v1_compts_1(X0) & v2_lattice3(X0) & v1_lattice3(X0) & v5_orders_2(X0) & v4_orders_2(X0) & v3_orders_2(X0) & v8_pre_topc(X0) & v2_pre_topc(X0)) => ! [X1] : (m1_subset_1(X1,u1_struct_0(X0)) => ! [X2] : ((l1_waybel_0(X2,X0) & v7_waybel_0(X2) & v4_orders_2(X2) & ~v2_struct_0(X2)) => ((r3_waybel_9(X0,X2,X1) & v11_waybel_0(X2,X0) & ! [X3] : (m1_subset_1(X3,u1_struct_0(X0)) => v5_pre_topc(k4_waybel_1(X0,X3),X0,X0))) => k1_waybel_9(X0,X2) = X1))))),
% 0.22/0.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t36_waybel_9)).
% 0.22/0.50  fof(f201,plain,(
% 0.22/0.50    ~m1_subset_1(sK6(sK0),u1_struct_0(sK0)) | spl9_20),
% 0.22/0.50    inference(avatar_component_clause,[],[f200])).
% 0.22/0.50  fof(f202,plain,(
% 0.22/0.50    ~spl9_20 | spl9_18),
% 0.22/0.50    inference(avatar_split_clause,[],[f198,f182,f200])).
% 0.22/0.50  fof(f182,plain,(
% 0.22/0.50    spl9_18 <=> v5_pre_topc(k4_waybel_1(sK0,sK6(sK0)),sK0,sK0)),
% 0.22/0.50    introduced(avatar_definition,[new_symbols(naming,[spl9_18])])).
% 0.22/0.50  fof(f198,plain,(
% 0.22/0.50    ~m1_subset_1(sK6(sK0),u1_struct_0(sK0)) | spl9_18),
% 0.22/0.50    inference(resolution,[],[f183,f63])).
% 0.22/0.50  fof(f183,plain,(
% 0.22/0.50    ~v5_pre_topc(k4_waybel_1(sK0,sK6(sK0)),sK0,sK0) | spl9_18),
% 0.22/0.50    inference(avatar_component_clause,[],[f182])).
% 0.22/0.50  fof(f197,plain,(
% 0.22/0.50    ~spl9_18 | ~spl9_4 | spl9_19 | ~spl9_8 | ~spl9_9 | ~spl9_10 | ~spl9_11 | ~spl9_12 | ~spl9_13 | ~spl9_14 | ~spl9_15 | ~spl9_16 | ~spl9_3 | ~spl9_17),
% 0.22/0.50    inference(avatar_split_clause,[],[f180,f177,f114,f166,f162,f158,f154,f150,f146,f142,f138,f134,f186,f118,f182])).
% 0.22/0.50  fof(f177,plain,(
% 0.22/0.50    spl9_17 <=> ! [X1,X0] : (~r3_waybel_9(X0,sK1,X1) | ~v2_pre_topc(X0) | ~v8_pre_topc(X0) | ~v3_orders_2(X0) | ~v4_orders_2(X0) | ~v5_orders_2(X0) | ~v1_lattice3(X0) | ~v2_lattice3(X0) | ~v1_compts_1(X0) | ~l1_waybel_9(X0) | ~m1_subset_1(X1,u1_struct_0(X0)) | k1_waybel_9(X0,sK1) = X1 | ~l1_waybel_0(sK1,X0) | ~v5_pre_topc(k4_waybel_1(X0,sK6(X0)),X0,X0) | ~v11_waybel_0(sK1,X0))),
% 0.22/0.50    introduced(avatar_definition,[new_symbols(naming,[spl9_17])])).
% 0.22/0.50  fof(f180,plain,(
% 0.22/0.50    ( ! [X0] : (~v2_pre_topc(sK0) | ~v8_pre_topc(sK0) | ~v3_orders_2(sK0) | ~v4_orders_2(sK0) | ~v5_orders_2(sK0) | ~v1_lattice3(sK0) | ~v2_lattice3(sK0) | ~v1_compts_1(sK0) | ~l1_waybel_9(sK0) | ~m1_subset_1(X0,u1_struct_0(sK0)) | k1_waybel_9(sK0,sK1) = X0 | ~l1_waybel_0(sK1,sK0) | ~v5_pre_topc(k4_waybel_1(sK0,sK6(sK0)),sK0,sK0) | ~r3_waybel_9(sK0,sK1,X0)) ) | (~spl9_3 | ~spl9_17)),
% 0.22/0.50    inference(resolution,[],[f178,f115])).
% 0.22/0.50  fof(f178,plain,(
% 0.22/0.50    ( ! [X0,X1] : (~v11_waybel_0(sK1,X0) | ~v2_pre_topc(X0) | ~v8_pre_topc(X0) | ~v3_orders_2(X0) | ~v4_orders_2(X0) | ~v5_orders_2(X0) | ~v1_lattice3(X0) | ~v2_lattice3(X0) | ~v1_compts_1(X0) | ~l1_waybel_9(X0) | ~m1_subset_1(X1,u1_struct_0(X0)) | k1_waybel_9(X0,sK1) = X1 | ~l1_waybel_0(sK1,X0) | ~v5_pre_topc(k4_waybel_1(X0,sK6(X0)),X0,X0) | ~r3_waybel_9(X0,sK1,X1)) ) | ~spl9_17),
% 0.22/0.50    inference(avatar_component_clause,[],[f177])).
% 0.22/0.50  fof(f179,plain,(
% 0.22/0.50    spl9_7 | ~spl9_6 | spl9_17 | ~spl9_5),
% 0.22/0.50    inference(avatar_split_clause,[],[f173,f122,f177,f126,f130])).
% 0.22/0.50  fof(f173,plain,(
% 0.22/0.50    ( ! [X0,X1] : (~r3_waybel_9(X0,sK1,X1) | ~v11_waybel_0(sK1,X0) | ~v5_pre_topc(k4_waybel_1(X0,sK6(X0)),X0,X0) | ~l1_waybel_0(sK1,X0) | k1_waybel_9(X0,sK1) = X1 | ~v4_orders_2(sK1) | v2_struct_0(sK1) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_waybel_9(X0) | ~v1_compts_1(X0) | ~v2_lattice3(X0) | ~v1_lattice3(X0) | ~v5_orders_2(X0) | ~v4_orders_2(X0) | ~v3_orders_2(X0) | ~v8_pre_topc(X0) | ~v2_pre_topc(X0)) ) | ~spl9_5),
% 0.22/0.50    inference(resolution,[],[f91,f123])).
% 0.22/0.50  fof(f91,plain,(
% 0.22/0.50    ( ! [X2,X0,X1] : (~v7_waybel_0(X2) | ~r3_waybel_9(X0,X2,X1) | ~v11_waybel_0(X2,X0) | ~v5_pre_topc(k4_waybel_1(X0,sK6(X0)),X0,X0) | ~l1_waybel_0(X2,X0) | k1_waybel_9(X0,X2) = X1 | ~v4_orders_2(X2) | v2_struct_0(X2) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_waybel_9(X0) | ~v1_compts_1(X0) | ~v2_lattice3(X0) | ~v1_lattice3(X0) | ~v5_orders_2(X0) | ~v4_orders_2(X0) | ~v3_orders_2(X0) | ~v8_pre_topc(X0) | ~v2_pre_topc(X0)) )),
% 0.22/0.50    inference(cnf_transformation,[],[f48])).
% 0.22/0.50  fof(f168,plain,(
% 0.22/0.50    spl9_16),
% 0.22/0.50    inference(avatar_split_clause,[],[f54,f166])).
% 0.22/0.50  fof(f54,plain,(
% 0.22/0.50    v2_pre_topc(sK0)),
% 0.22/0.50    inference(cnf_transformation,[],[f37])).
% 0.22/0.50  fof(f164,plain,(
% 0.22/0.50    spl9_15),
% 0.22/0.50    inference(avatar_split_clause,[],[f55,f162])).
% 0.22/0.50  fof(f55,plain,(
% 0.22/0.50    v8_pre_topc(sK0)),
% 0.22/0.50    inference(cnf_transformation,[],[f37])).
% 0.22/0.50  fof(f160,plain,(
% 0.22/0.50    spl9_14),
% 0.22/0.50    inference(avatar_split_clause,[],[f56,f158])).
% 0.22/0.50  fof(f56,plain,(
% 0.22/0.50    v3_orders_2(sK0)),
% 0.22/0.50    inference(cnf_transformation,[],[f37])).
% 0.22/0.50  fof(f156,plain,(
% 0.22/0.50    spl9_13),
% 0.22/0.50    inference(avatar_split_clause,[],[f57,f154])).
% 0.22/0.50  fof(f57,plain,(
% 0.22/0.50    v4_orders_2(sK0)),
% 0.22/0.50    inference(cnf_transformation,[],[f37])).
% 0.22/0.50  fof(f152,plain,(
% 0.22/0.50    spl9_12),
% 0.22/0.50    inference(avatar_split_clause,[],[f58,f150])).
% 0.22/0.50  fof(f58,plain,(
% 0.22/0.50    v5_orders_2(sK0)),
% 0.22/0.50    inference(cnf_transformation,[],[f37])).
% 0.22/0.50  fof(f148,plain,(
% 0.22/0.50    spl9_11),
% 0.22/0.50    inference(avatar_split_clause,[],[f59,f146])).
% 0.22/0.50  fof(f59,plain,(
% 0.22/0.50    v1_lattice3(sK0)),
% 0.22/0.50    inference(cnf_transformation,[],[f37])).
% 0.22/0.50  fof(f144,plain,(
% 0.22/0.50    spl9_10),
% 0.22/0.50    inference(avatar_split_clause,[],[f60,f142])).
% 0.22/0.50  fof(f60,plain,(
% 0.22/0.50    v2_lattice3(sK0)),
% 0.22/0.50    inference(cnf_transformation,[],[f37])).
% 0.22/0.50  fof(f140,plain,(
% 0.22/0.50    spl9_9),
% 0.22/0.50    inference(avatar_split_clause,[],[f61,f138])).
% 0.22/0.50  fof(f61,plain,(
% 0.22/0.50    v1_compts_1(sK0)),
% 0.22/0.50    inference(cnf_transformation,[],[f37])).
% 0.22/0.50  fof(f136,plain,(
% 0.22/0.50    spl9_8),
% 0.22/0.50    inference(avatar_split_clause,[],[f62,f134])).
% 0.22/0.50  fof(f62,plain,(
% 0.22/0.50    l1_waybel_9(sK0)),
% 0.22/0.50    inference(cnf_transformation,[],[f37])).
% 0.22/0.50  fof(f132,plain,(
% 0.22/0.50    ~spl9_7),
% 0.22/0.50    inference(avatar_split_clause,[],[f64,f130])).
% 0.22/0.50  fof(f64,plain,(
% 0.22/0.50    ~v2_struct_0(sK1)),
% 0.22/0.50    inference(cnf_transformation,[],[f37])).
% 0.22/0.50  fof(f128,plain,(
% 0.22/0.50    spl9_6),
% 0.22/0.50    inference(avatar_split_clause,[],[f65,f126])).
% 0.22/0.50  fof(f65,plain,(
% 0.22/0.50    v4_orders_2(sK1)),
% 0.22/0.50    inference(cnf_transformation,[],[f37])).
% 0.22/0.50  fof(f124,plain,(
% 0.22/0.50    spl9_5),
% 0.22/0.50    inference(avatar_split_clause,[],[f66,f122])).
% 0.22/0.50  fof(f66,plain,(
% 0.22/0.50    v7_waybel_0(sK1)),
% 0.22/0.50    inference(cnf_transformation,[],[f37])).
% 0.22/0.50  fof(f120,plain,(
% 0.22/0.50    spl9_4),
% 0.22/0.50    inference(avatar_split_clause,[],[f67,f118])).
% 0.22/0.50  fof(f67,plain,(
% 0.22/0.50    l1_waybel_0(sK1,sK0)),
% 0.22/0.50    inference(cnf_transformation,[],[f37])).
% 0.22/0.50  fof(f116,plain,(
% 0.22/0.50    spl9_3),
% 0.22/0.50    inference(avatar_split_clause,[],[f68,f114])).
% 0.22/0.50  fof(f68,plain,(
% 0.22/0.50    v11_waybel_0(sK1,sK0)),
% 0.22/0.50    inference(cnf_transformation,[],[f37])).
% 0.22/0.50  fof(f112,plain,(
% 0.22/0.50    ~spl9_1 | ~spl9_2),
% 0.22/0.50    inference(avatar_split_clause,[],[f69,f110,f107])).
% 0.22/0.50  fof(f69,plain,(
% 0.22/0.50    ~r2_hidden(k1_waybel_9(sK0,sK1),k10_yellow_6(sK0,sK1)) | ~r2_waybel_9(sK0,sK1)),
% 0.22/0.50    inference(cnf_transformation,[],[f37])).
% 0.22/0.50  % SZS output end Proof for theBenchmark
% 0.22/0.50  % (30171)------------------------------
% 0.22/0.50  % (30171)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.50  % (30171)Termination reason: Refutation
% 0.22/0.50  
% 0.22/0.50  % (30171)Memory used [KB]: 11129
% 0.22/0.50  % (30171)Time elapsed: 0.020 s
% 0.22/0.50  % (30171)------------------------------
% 0.22/0.50  % (30171)------------------------------
% 0.22/0.50  % (30177)lrs+1011_3:1_add=off:afr=on:afp=10000:afq=1.1:amm=off:bce=on:cond=on:ep=R:fsr=off:nm=16:nwc=1:stl=30:sos=all:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.22/0.50  % (30162)Success in time 0.137 s
%------------------------------------------------------------------------------
