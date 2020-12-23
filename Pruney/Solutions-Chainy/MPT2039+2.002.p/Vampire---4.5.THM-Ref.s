%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n008.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:23:18 EST 2020

% Result     : Theorem 0.22s
% Output     : Refutation 0.22s
% Verified   : 
% Statistics : Number of formulae       :  286 ( 834 expanded)
%              Number of leaves         :   70 ( 445 expanded)
%              Depth                    :   11
%              Number of atoms          : 2262 (7214 expanded)
%              Number of equality atoms :   62 ( 163 expanded)
%              Maximal formula depth    :   27 (   8 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f446,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f118,f122,f126,f130,f134,f138,f142,f146,f150,f154,f158,f162,f166,f170,f174,f185,f203,f208,f213,f216,f230,f232,f234,f240,f244,f250,f258,f263,f268,f270,f279,f281,f291,f293,f316,f321,f326,f337,f368,f381,f389,f390,f391,f397,f401,f414,f427,f432,f436,f437,f445])).

fof(f445,plain,
    ( spl9_22
    | ~ spl9_16
    | ~ spl9_15
    | ~ spl9_9
    | ~ spl9_23
    | spl9_7
    | ~ spl9_6
    | ~ spl9_5
    | ~ spl9_4
    | spl9_59
    | ~ spl9_55
    | ~ spl9_58 ),
    inference(avatar_split_clause,[],[f444,f425,f412,f430,f124,f128,f132,f136,f222,f144,f168,f172,f219])).

fof(f219,plain,
    ( spl9_22
  <=> v2_struct_0(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_22])])).

fof(f172,plain,
    ( spl9_16
  <=> v2_pre_topc(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_16])])).

fof(f168,plain,
    ( spl9_15
  <=> v8_pre_topc(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_15])])).

fof(f144,plain,
    ( spl9_9
  <=> v1_compts_1(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_9])])).

fof(f222,plain,
    ( spl9_23
  <=> l1_pre_topc(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_23])])).

fof(f136,plain,
    ( spl9_7
  <=> v2_struct_0(sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_7])])).

fof(f132,plain,
    ( spl9_6
  <=> v4_orders_2(sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_6])])).

fof(f128,plain,
    ( spl9_5
  <=> v7_waybel_0(sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_5])])).

fof(f124,plain,
    ( spl9_4
  <=> l1_waybel_0(sK1,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_4])])).

fof(f430,plain,
    ( spl9_59
  <=> ! [X0] :
        ( ~ r3_waybel_9(sK0,sK1,X0)
        | r2_hidden(X0,k10_yellow_6(sK0,sK1))
        | ~ m1_subset_1(X0,u1_struct_0(sK0)) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_59])])).

fof(f412,plain,
    ( spl9_55
  <=> k1_waybel_2(sK0,sK1) = sK3(sK0,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_55])])).

fof(f425,plain,
    ( spl9_58
  <=> k1_waybel_2(sK0,sK1) = sK2(sK0,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_58])])).

fof(f444,plain,
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
    | ~ spl9_55
    | ~ spl9_58 ),
    inference(trivial_inequality_removal,[],[f443])).

fof(f443,plain,
    ( ! [X0] :
        ( k1_waybel_2(sK0,sK1) != k1_waybel_2(sK0,sK1)
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
    | ~ spl9_55
    | ~ spl9_58 ),
    inference(forward_demodulation,[],[f441,f426])).

fof(f426,plain,
    ( k1_waybel_2(sK0,sK1) = sK2(sK0,sK1)
    | ~ spl9_58 ),
    inference(avatar_component_clause,[],[f425])).

fof(f441,plain,
    ( ! [X0] :
        ( k1_waybel_2(sK0,sK1) != sK2(sK0,sK1)
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
    | ~ spl9_55 ),
    inference(superposition,[],[f83,f413])).

fof(f413,plain,
    ( k1_waybel_2(sK0,sK1) = sK3(sK0,sK1)
    | ~ spl9_55 ),
    inference(avatar_component_clause,[],[f412])).

fof(f83,plain,(
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
    inference(cnf_transformation,[],[f45])).

fof(f45,plain,(
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
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2,sK3])],[f42,f44,f43])).

fof(f43,plain,(
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

fof(f44,plain,(
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

fof(f42,plain,(
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
    inference(rectify,[],[f24])).

fof(f24,plain,(
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
    inference(flattening,[],[f23])).

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
    inference(ennf_transformation,[],[f14])).

fof(f14,plain,(
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
    inference(rectify,[],[f9])).

fof(f9,axiom,(
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

fof(f437,plain,
    ( spl9_22
    | ~ spl9_16
    | ~ spl9_15
    | ~ spl9_9
    | ~ spl9_23
    | spl9_7
    | ~ spl9_6
    | ~ spl9_5
    | ~ spl9_4
    | spl9_59
    | spl9_56 ),
    inference(avatar_split_clause,[],[f433,f418,f430,f124,f128,f132,f136,f222,f144,f168,f172,f219])).

fof(f418,plain,
    ( spl9_56
  <=> m1_subset_1(sK2(sK0,sK1),u1_struct_0(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_56])])).

fof(f433,plain,
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
    | spl9_56 ),
    inference(resolution,[],[f419,f79])).

fof(f79,plain,(
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
    inference(cnf_transformation,[],[f45])).

fof(f419,plain,
    ( ~ m1_subset_1(sK2(sK0,sK1),u1_struct_0(sK0))
    | spl9_56 ),
    inference(avatar_component_clause,[],[f418])).

fof(f436,plain,
    ( ~ spl9_27
    | ~ spl9_26
    | spl9_2
    | ~ spl9_59 ),
    inference(avatar_split_clause,[],[f435,f430,f116,f238,f242])).

fof(f242,plain,
    ( spl9_27
  <=> m1_subset_1(k1_waybel_2(sK0,sK1),u1_struct_0(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_27])])).

fof(f238,plain,
    ( spl9_26
  <=> r3_waybel_9(sK0,sK1,k1_waybel_2(sK0,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_26])])).

fof(f116,plain,
    ( spl9_2
  <=> r2_hidden(k1_waybel_2(sK0,sK1),k10_yellow_6(sK0,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_2])])).

fof(f435,plain,
    ( ~ r3_waybel_9(sK0,sK1,k1_waybel_2(sK0,sK1))
    | ~ m1_subset_1(k1_waybel_2(sK0,sK1),u1_struct_0(sK0))
    | spl9_2
    | ~ spl9_59 ),
    inference(resolution,[],[f431,f117])).

fof(f117,plain,
    ( ~ r2_hidden(k1_waybel_2(sK0,sK1),k10_yellow_6(sK0,sK1))
    | spl9_2 ),
    inference(avatar_component_clause,[],[f116])).

fof(f431,plain,
    ( ! [X0] :
        ( r2_hidden(X0,k10_yellow_6(sK0,sK1))
        | ~ r3_waybel_9(sK0,sK1,X0)
        | ~ m1_subset_1(X0,u1_struct_0(sK0)) )
    | ~ spl9_59 ),
    inference(avatar_component_clause,[],[f430])).

fof(f432,plain,
    ( spl9_22
    | ~ spl9_16
    | ~ spl9_15
    | ~ spl9_9
    | ~ spl9_23
    | spl9_7
    | ~ spl9_6
    | ~ spl9_5
    | ~ spl9_4
    | spl9_59
    | spl9_53 ),
    inference(avatar_split_clause,[],[f428,f405,f430,f124,f128,f132,f136,f222,f144,f168,f172,f219])).

fof(f405,plain,
    ( spl9_53
  <=> m1_subset_1(sK3(sK0,sK1),u1_struct_0(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_53])])).

fof(f428,plain,
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
    | spl9_53 ),
    inference(resolution,[],[f406,f80])).

fof(f80,plain,(
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
    inference(cnf_transformation,[],[f45])).

fof(f406,plain,
    ( ~ m1_subset_1(sK3(sK0,sK1),u1_struct_0(sK0))
    | spl9_53 ),
    inference(avatar_component_clause,[],[f405])).

fof(f427,plain,
    ( spl9_58
    | ~ spl9_56
    | ~ spl9_19
    | ~ spl9_52 ),
    inference(avatar_split_clause,[],[f416,f399,f192,f418,f425])).

fof(f192,plain,
    ( spl9_19
  <=> ! [X0] :
        ( ~ m1_subset_1(X0,u1_struct_0(sK0))
        | ~ r3_waybel_9(sK0,sK1,X0)
        | k1_waybel_2(sK0,sK1) = X0 ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_19])])).

fof(f399,plain,
    ( spl9_52
  <=> r3_waybel_9(sK0,sK1,sK2(sK0,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_52])])).

fof(f416,plain,
    ( ~ m1_subset_1(sK2(sK0,sK1),u1_struct_0(sK0))
    | k1_waybel_2(sK0,sK1) = sK2(sK0,sK1)
    | ~ spl9_19
    | ~ spl9_52 ),
    inference(resolution,[],[f400,f193])).

fof(f193,plain,
    ( ! [X0] :
        ( ~ r3_waybel_9(sK0,sK1,X0)
        | ~ m1_subset_1(X0,u1_struct_0(sK0))
        | k1_waybel_2(sK0,sK1) = X0 )
    | ~ spl9_19 ),
    inference(avatar_component_clause,[],[f192])).

fof(f400,plain,
    ( r3_waybel_9(sK0,sK1,sK2(sK0,sK1))
    | ~ spl9_52 ),
    inference(avatar_component_clause,[],[f399])).

fof(f414,plain,
    ( spl9_55
    | ~ spl9_53
    | ~ spl9_19
    | ~ spl9_51 ),
    inference(avatar_split_clause,[],[f403,f395,f192,f405,f412])).

fof(f395,plain,
    ( spl9_51
  <=> r3_waybel_9(sK0,sK1,sK3(sK0,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_51])])).

fof(f403,plain,
    ( ~ m1_subset_1(sK3(sK0,sK1),u1_struct_0(sK0))
    | k1_waybel_2(sK0,sK1) = sK3(sK0,sK1)
    | ~ spl9_19
    | ~ spl9_51 ),
    inference(resolution,[],[f396,f193])).

fof(f396,plain,
    ( r3_waybel_9(sK0,sK1,sK3(sK0,sK1))
    | ~ spl9_51 ),
    inference(avatar_component_clause,[],[f395])).

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
    | spl9_52
    | ~ spl9_27
    | ~ spl9_26
    | spl9_2 ),
    inference(avatar_split_clause,[],[f393,f116,f238,f242,f399,f124,f128,f132,f136,f222,f144,f168,f172,f219])).

fof(f393,plain,
    ( ~ r3_waybel_9(sK0,sK1,k1_waybel_2(sK0,sK1))
    | ~ m1_subset_1(k1_waybel_2(sK0,sK1),u1_struct_0(sK0))
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
    inference(resolution,[],[f117,f81])).

fof(f81,plain,(
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
    inference(cnf_transformation,[],[f45])).

fof(f397,plain,
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
    inference(avatar_split_clause,[],[f392,f116,f238,f242,f395,f124,f128,f132,f136,f222,f144,f168,f172,f219])).

fof(f392,plain,
    ( ~ r3_waybel_9(sK0,sK1,k1_waybel_2(sK0,sK1))
    | ~ m1_subset_1(k1_waybel_2(sK0,sK1),u1_struct_0(sK0))
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
    inference(resolution,[],[f117,f82])).

fof(f82,plain,(
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
    inference(cnf_transformation,[],[f45])).

fof(f391,plain,
    ( ~ spl9_4
    | spl9_1
    | ~ spl9_8
    | ~ spl9_39 ),
    inference(avatar_split_clause,[],[f330,f311,f140,f113,f124])).

fof(f113,plain,
    ( spl9_1
  <=> r1_waybel_9(sK0,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_1])])).

fof(f140,plain,
    ( spl9_8
  <=> l1_waybel_9(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_8])])).

fof(f311,plain,
    ( spl9_39
  <=> r1_yellow_0(sK0,k2_relset_1(u1_struct_0(sK1),u1_struct_0(sK0),u1_waybel_0(sK0,sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_39])])).

fof(f330,plain,
    ( r1_waybel_9(sK0,sK1)
    | ~ l1_waybel_0(sK1,sK0)
    | ~ spl9_8
    | ~ spl9_39 ),
    inference(resolution,[],[f312,f176])).

fof(f176,plain,
    ( ! [X0] :
        ( ~ r1_yellow_0(sK0,k2_relset_1(u1_struct_0(X0),u1_struct_0(sK0),u1_waybel_0(sK0,X0)))
        | r1_waybel_9(sK0,X0)
        | ~ l1_waybel_0(X0,sK0) )
    | ~ spl9_8 ),
    inference(resolution,[],[f175,f141])).

fof(f141,plain,
    ( l1_waybel_9(sK0)
    | ~ spl9_8 ),
    inference(avatar_component_clause,[],[f140])).

fof(f175,plain,(
    ! [X0,X1] :
      ( ~ l1_waybel_9(X0)
      | ~ l1_waybel_0(X1,X0)
      | r1_waybel_9(X0,X1)
      | ~ r1_yellow_0(X0,k2_relset_1(u1_struct_0(X1),u1_struct_0(X0),u1_waybel_0(X0,X1))) ) ),
    inference(resolution,[],[f78,f75])).

fof(f75,plain,(
    ! [X0] :
      ( l1_orders_2(X0)
      | ~ l1_waybel_9(X0) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f19,plain,(
    ! [X0] :
      ( ( l1_orders_2(X0)
        & l1_pre_topc(X0) )
      | ~ l1_waybel_9(X0) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0] :
      ( l1_waybel_9(X0)
     => ( l1_orders_2(X0)
        & l1_pre_topc(X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_l1_waybel_9)).

fof(f78,plain,(
    ! [X0,X1] :
      ( ~ l1_orders_2(X0)
      | ~ r1_yellow_0(X0,k2_relset_1(u1_struct_0(X1),u1_struct_0(X0),u1_waybel_0(X0,X1)))
      | ~ l1_waybel_0(X1,X0)
      | r1_waybel_9(X0,X1) ) ),
    inference(cnf_transformation,[],[f41])).

fof(f41,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ( r1_waybel_9(X0,X1)
              | ~ r1_yellow_0(X0,k2_relset_1(u1_struct_0(X1),u1_struct_0(X0),u1_waybel_0(X0,X1))) )
            & ( r1_yellow_0(X0,k2_relset_1(u1_struct_0(X1),u1_struct_0(X0),u1_waybel_0(X0,X1)))
              | ~ r1_waybel_9(X0,X1) ) )
          | ~ l1_waybel_0(X1,X0) )
      | ~ l1_orders_2(X0) ) ),
    inference(nnf_transformation,[],[f22])).

fof(f22,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( r1_waybel_9(X0,X1)
          <=> r1_yellow_0(X0,k2_relset_1(u1_struct_0(X1),u1_struct_0(X0),u1_waybel_0(X0,X1))) )
          | ~ l1_waybel_0(X1,X0) )
      | ~ l1_orders_2(X0) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0] :
      ( l1_orders_2(X0)
     => ! [X1] :
          ( l1_waybel_0(X1,X0)
         => ( r1_waybel_9(X0,X1)
          <=> r1_yellow_0(X0,k2_relset_1(u1_struct_0(X1),u1_struct_0(X0),u1_waybel_0(X0,X1))) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_waybel_9)).

fof(f312,plain,
    ( r1_yellow_0(sK0,k2_relset_1(u1_struct_0(sK1),u1_struct_0(sK0),u1_waybel_0(sK0,sK1)))
    | ~ spl9_39 ),
    inference(avatar_component_clause,[],[f311])).

fof(f390,plain,
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
    | ~ spl9_36
    | ~ spl9_3
    | ~ spl9_26
    | spl9_49 ),
    inference(avatar_split_clause,[],[f387,f378,f238,f120,f299,f242,f124,f128,f132,f136,f140,f144,f148,f152,f156,f160,f164,f168,f172])).

fof(f164,plain,
    ( spl9_14
  <=> v3_orders_2(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_14])])).

fof(f160,plain,
    ( spl9_13
  <=> v4_orders_2(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_13])])).

fof(f156,plain,
    ( spl9_12
  <=> v5_orders_2(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_12])])).

fof(f152,plain,
    ( spl9_11
  <=> v1_lattice3(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_11])])).

fof(f148,plain,
    ( spl9_10
  <=> v2_lattice3(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_10])])).

fof(f299,plain,
    ( spl9_36
  <=> v5_pre_topc(k4_waybel_1(sK0,sK7(sK0)),sK0,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_36])])).

fof(f120,plain,
    ( spl9_3
  <=> v10_waybel_0(sK1,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_3])])).

fof(f378,plain,
    ( spl9_49
  <=> r2_lattice3(sK0,k2_relset_1(u1_struct_0(sK1),u1_struct_0(sK0),u1_waybel_0(sK0,sK1)),k1_waybel_2(sK0,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_49])])).

fof(f387,plain,
    ( ~ r3_waybel_9(sK0,sK1,k1_waybel_2(sK0,sK1))
    | ~ v10_waybel_0(sK1,sK0)
    | ~ v5_pre_topc(k4_waybel_1(sK0,sK7(sK0)),sK0,sK0)
    | ~ m1_subset_1(k1_waybel_2(sK0,sK1),u1_struct_0(sK0))
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
    | spl9_49 ),
    inference(resolution,[],[f379,f111])).

fof(f111,plain,(
    ! [X0,X3,X1] :
      ( r2_lattice3(X0,k2_relset_1(u1_struct_0(X1),u1_struct_0(X0),u1_waybel_0(X0,X1)),X3)
      | ~ r3_waybel_9(X0,X1,X3)
      | ~ v10_waybel_0(X1,X0)
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
    inference(duplicate_literal_removal,[],[f104])).

fof(f104,plain,(
    ! [X0,X3,X1] :
      ( r2_lattice3(X0,k2_relset_1(u1_struct_0(X1),u1_struct_0(X0),u1_waybel_0(X0,X1)),X3)
      | ~ r3_waybel_9(X0,X1,X3)
      | ~ v10_waybel_0(X1,X0)
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
    inference(equality_resolution,[],[f97])).

fof(f97,plain,(
    ! [X2,X0,X3,X1] :
      ( r2_lattice3(X0,k2_relset_1(u1_struct_0(X1),u1_struct_0(X0),u1_waybel_0(X0,X1)),X3)
      | ~ r3_waybel_9(X0,X1,X2)
      | ~ v10_waybel_0(X1,X0)
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
    inference(cnf_transformation,[],[f53])).

fof(f53,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( r2_lattice3(X0,k2_relset_1(u1_struct_0(X1),u1_struct_0(X0),u1_waybel_0(X0,X1)),X3)
                  | ~ r3_waybel_9(X0,X1,X2)
                  | ~ v10_waybel_0(X1,X0)
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
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK7])],[f32,f52])).

fof(f52,plain,(
    ! [X0] :
      ( ? [X4] :
          ( ~ v5_pre_topc(k4_waybel_1(X0,X4),X0,X0)
          & m1_subset_1(X4,u1_struct_0(X0)) )
     => ( ~ v5_pre_topc(k4_waybel_1(X0,sK7(X0)),X0,X0)
        & m1_subset_1(sK7(X0),u1_struct_0(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f32,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( r2_lattice3(X0,k2_relset_1(u1_struct_0(X1),u1_struct_0(X0),u1_waybel_0(X0,X1)),X3)
                  | ~ r3_waybel_9(X0,X1,X2)
                  | ~ v10_waybel_0(X1,X0)
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
    inference(flattening,[],[f31])).

fof(f31,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( r2_lattice3(X0,k2_relset_1(u1_struct_0(X1),u1_struct_0(X0),u1_waybel_0(X0,X1)),X3)
                  | ~ r3_waybel_9(X0,X1,X2)
                  | ~ v10_waybel_0(X1,X0)
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
    inference(ennf_transformation,[],[f6])).

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
                      & v10_waybel_0(X1,X0)
                      & ! [X4] :
                          ( m1_subset_1(X4,u1_struct_0(X0))
                         => v5_pre_topc(k4_waybel_1(X0,X4),X0,X0) )
                      & X2 = X3 )
                   => r2_lattice3(X0,k2_relset_1(u1_struct_0(X1),u1_struct_0(X0),u1_waybel_0(X0,X1)),X3) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l48_waybel_9)).

fof(f379,plain,
    ( ~ r2_lattice3(sK0,k2_relset_1(u1_struct_0(sK1),u1_struct_0(sK0),u1_waybel_0(sK0,sK1)),k1_waybel_2(sK0,sK1))
    | spl9_49 ),
    inference(avatar_component_clause,[],[f378])).

fof(f389,plain,
    ( ~ spl9_27
    | ~ spl9_26
    | ~ spl9_43
    | spl9_49 ),
    inference(avatar_split_clause,[],[f386,f378,f335,f238,f242])).

fof(f335,plain,
    ( spl9_43
  <=> ! [X0] :
        ( ~ m1_subset_1(X0,u1_struct_0(sK0))
        | ~ r3_waybel_9(sK0,sK1,X0)
        | r2_lattice3(sK0,k2_relset_1(u1_struct_0(sK1),u1_struct_0(sK0),u1_waybel_0(sK0,sK1)),X0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_43])])).

fof(f386,plain,
    ( ~ r3_waybel_9(sK0,sK1,k1_waybel_2(sK0,sK1))
    | ~ m1_subset_1(k1_waybel_2(sK0,sK1),u1_struct_0(sK0))
    | ~ spl9_43
    | spl9_49 ),
    inference(resolution,[],[f379,f336])).

fof(f336,plain,
    ( ! [X0] :
        ( r2_lattice3(sK0,k2_relset_1(u1_struct_0(sK1),u1_struct_0(sK0),u1_waybel_0(sK0,sK1)),X0)
        | ~ r3_waybel_9(sK0,sK1,X0)
        | ~ m1_subset_1(X0,u1_struct_0(sK0)) )
    | ~ spl9_43 ),
    inference(avatar_component_clause,[],[f335])).

fof(f381,plain,
    ( ~ spl9_12
    | ~ spl9_33
    | spl9_39
    | ~ spl9_49
    | ~ spl9_27
    | ~ spl9_47 ),
    inference(avatar_split_clause,[],[f372,f366,f242,f378,f311,f274,f156])).

fof(f274,plain,
    ( spl9_33
  <=> l1_orders_2(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_33])])).

fof(f366,plain,
    ( spl9_47
  <=> ! [X1] :
        ( ~ m1_subset_1(X1,u1_struct_0(sK0))
        | r1_orders_2(sK0,k1_waybel_2(sK0,sK1),sK5(sK0,X1,k2_relset_1(u1_struct_0(sK1),u1_struct_0(sK0),u1_waybel_0(sK0,sK1))))
        | ~ r2_lattice3(sK0,k2_relset_1(u1_struct_0(sK1),u1_struct_0(sK0),u1_waybel_0(sK0,sK1)),X1) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_47])])).

fof(f372,plain,
    ( ~ m1_subset_1(k1_waybel_2(sK0,sK1),u1_struct_0(sK0))
    | ~ r2_lattice3(sK0,k2_relset_1(u1_struct_0(sK1),u1_struct_0(sK0),u1_waybel_0(sK0,sK1)),k1_waybel_2(sK0,sK1))
    | r1_yellow_0(sK0,k2_relset_1(u1_struct_0(sK1),u1_struct_0(sK0),u1_waybel_0(sK0,sK1)))
    | ~ l1_orders_2(sK0)
    | ~ v5_orders_2(sK0)
    | ~ spl9_47 ),
    inference(duplicate_literal_removal,[],[f370])).

fof(f370,plain,
    ( ~ m1_subset_1(k1_waybel_2(sK0,sK1),u1_struct_0(sK0))
    | ~ r2_lattice3(sK0,k2_relset_1(u1_struct_0(sK1),u1_struct_0(sK0),u1_waybel_0(sK0,sK1)),k1_waybel_2(sK0,sK1))
    | r1_yellow_0(sK0,k2_relset_1(u1_struct_0(sK1),u1_struct_0(sK0),u1_waybel_0(sK0,sK1)))
    | ~ r2_lattice3(sK0,k2_relset_1(u1_struct_0(sK1),u1_struct_0(sK0),u1_waybel_0(sK0,sK1)),k1_waybel_2(sK0,sK1))
    | ~ m1_subset_1(k1_waybel_2(sK0,sK1),u1_struct_0(sK0))
    | ~ l1_orders_2(sK0)
    | ~ v5_orders_2(sK0)
    | ~ spl9_47 ),
    inference(resolution,[],[f367,f93])).

fof(f93,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_orders_2(X0,X1,sK5(X0,X1,X2))
      | r1_yellow_0(X0,X2)
      | ~ r2_lattice3(X0,X2,X1)
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | ~ v5_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f49])).

fof(f49,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( ( r1_yellow_0(X0,X2)
                  & k1_yellow_0(X0,X2) = X1 )
                | ( ~ r1_orders_2(X0,X1,sK5(X0,X1,X2))
                  & r2_lattice3(X0,X2,sK5(X0,X1,X2))
                  & m1_subset_1(sK5(X0,X1,X2),u1_struct_0(X0)) )
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
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK5])],[f28,f48])).

fof(f48,plain,(
    ! [X2,X1,X0] :
      ( ? [X3] :
          ( ~ r1_orders_2(X0,X1,X3)
          & r2_lattice3(X0,X2,X3)
          & m1_subset_1(X3,u1_struct_0(X0)) )
     => ( ~ r1_orders_2(X0,X1,sK5(X0,X1,X2))
        & r2_lattice3(X0,X2,sK5(X0,X1,X2))
        & m1_subset_1(sK5(X0,X1,X2),u1_struct_0(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f28,plain,(
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
    inference(flattening,[],[f27])).

fof(f27,plain,(
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
    inference(ennf_transformation,[],[f15])).

fof(f15,plain,(
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
    inference(rectify,[],[f3])).

fof(f3,axiom,(
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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t30_yellow_0)).

fof(f367,plain,
    ( ! [X1] :
        ( r1_orders_2(sK0,k1_waybel_2(sK0,sK1),sK5(sK0,X1,k2_relset_1(u1_struct_0(sK1),u1_struct_0(sK0),u1_waybel_0(sK0,sK1))))
        | ~ m1_subset_1(X1,u1_struct_0(sK0))
        | ~ r2_lattice3(sK0,k2_relset_1(u1_struct_0(sK1),u1_struct_0(sK0),u1_waybel_0(sK0,sK1)),X1) )
    | ~ spl9_47 ),
    inference(avatar_component_clause,[],[f366])).

fof(f368,plain,
    ( ~ spl9_12
    | ~ spl9_33
    | spl9_39
    | spl9_47
    | ~ spl9_40 ),
    inference(avatar_split_clause,[],[f359,f314,f366,f311,f274,f156])).

fof(f314,plain,
    ( spl9_40
  <=> ! [X2] :
        ( r1_orders_2(sK0,k1_waybel_2(sK0,sK1),sK5(sK0,X2,k2_relset_1(u1_struct_0(sK1),u1_struct_0(sK0),u1_waybel_0(sK0,sK1))))
        | ~ m1_subset_1(X2,u1_struct_0(sK0))
        | ~ r2_lattice3(sK0,k2_relset_1(u1_struct_0(sK1),u1_struct_0(sK0),u1_waybel_0(sK0,sK1)),X2)
        | ~ m1_subset_1(sK5(sK0,X2,k2_relset_1(u1_struct_0(sK1),u1_struct_0(sK0),u1_waybel_0(sK0,sK1))),u1_struct_0(sK0)) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_40])])).

fof(f359,plain,
    ( ! [X1] :
        ( ~ m1_subset_1(X1,u1_struct_0(sK0))
        | ~ r2_lattice3(sK0,k2_relset_1(u1_struct_0(sK1),u1_struct_0(sK0),u1_waybel_0(sK0,sK1)),X1)
        | r1_orders_2(sK0,k1_waybel_2(sK0,sK1),sK5(sK0,X1,k2_relset_1(u1_struct_0(sK1),u1_struct_0(sK0),u1_waybel_0(sK0,sK1))))
        | r1_yellow_0(sK0,k2_relset_1(u1_struct_0(sK1),u1_struct_0(sK0),u1_waybel_0(sK0,sK1)))
        | ~ l1_orders_2(sK0)
        | ~ v5_orders_2(sK0) )
    | ~ spl9_40 ),
    inference(duplicate_literal_removal,[],[f358])).

fof(f358,plain,
    ( ! [X1] :
        ( ~ m1_subset_1(X1,u1_struct_0(sK0))
        | ~ r2_lattice3(sK0,k2_relset_1(u1_struct_0(sK1),u1_struct_0(sK0),u1_waybel_0(sK0,sK1)),X1)
        | r1_orders_2(sK0,k1_waybel_2(sK0,sK1),sK5(sK0,X1,k2_relset_1(u1_struct_0(sK1),u1_struct_0(sK0),u1_waybel_0(sK0,sK1))))
        | r1_yellow_0(sK0,k2_relset_1(u1_struct_0(sK1),u1_struct_0(sK0),u1_waybel_0(sK0,sK1)))
        | ~ r2_lattice3(sK0,k2_relset_1(u1_struct_0(sK1),u1_struct_0(sK0),u1_waybel_0(sK0,sK1)),X1)
        | ~ m1_subset_1(X1,u1_struct_0(sK0))
        | ~ l1_orders_2(sK0)
        | ~ v5_orders_2(sK0) )
    | ~ spl9_40 ),
    inference(resolution,[],[f315,f91])).

fof(f91,plain,(
    ! [X2,X0,X1] :
      ( m1_subset_1(sK5(X0,X1,X2),u1_struct_0(X0))
      | r1_yellow_0(X0,X2)
      | ~ r2_lattice3(X0,X2,X1)
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | ~ v5_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f49])).

fof(f315,plain,
    ( ! [X2] :
        ( ~ m1_subset_1(sK5(sK0,X2,k2_relset_1(u1_struct_0(sK1),u1_struct_0(sK0),u1_waybel_0(sK0,sK1))),u1_struct_0(sK0))
        | ~ m1_subset_1(X2,u1_struct_0(sK0))
        | ~ r2_lattice3(sK0,k2_relset_1(u1_struct_0(sK1),u1_struct_0(sK0),u1_waybel_0(sK0,sK1)),X2)
        | r1_orders_2(sK0,k1_waybel_2(sK0,sK1),sK5(sK0,X2,k2_relset_1(u1_struct_0(sK1),u1_struct_0(sK0),u1_waybel_0(sK0,sK1)))) )
    | ~ spl9_40 ),
    inference(avatar_component_clause,[],[f314])).

fof(f337,plain,
    ( spl9_43
    | ~ spl9_4
    | ~ spl9_5
    | ~ spl9_6
    | spl9_7
    | ~ spl9_3
    | ~ spl9_42 ),
    inference(avatar_split_clause,[],[f333,f324,f120,f136,f132,f128,f124,f335])).

fof(f324,plain,
    ( spl9_42
  <=> ! [X1,X0] :
        ( ~ r3_waybel_9(sK0,X0,X1)
        | v2_struct_0(X0)
        | ~ v4_orders_2(X0)
        | ~ v7_waybel_0(X0)
        | ~ l1_waybel_0(X0,sK0)
        | ~ m1_subset_1(X1,u1_struct_0(sK0))
        | r2_lattice3(sK0,k2_relset_1(u1_struct_0(X0),u1_struct_0(sK0),u1_waybel_0(sK0,X0)),X1)
        | ~ v10_waybel_0(X0,sK0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_42])])).

fof(f333,plain,
    ( ! [X0] :
        ( v2_struct_0(sK1)
        | ~ v4_orders_2(sK1)
        | ~ v7_waybel_0(sK1)
        | ~ l1_waybel_0(sK1,sK0)
        | ~ m1_subset_1(X0,u1_struct_0(sK0))
        | r2_lattice3(sK0,k2_relset_1(u1_struct_0(sK1),u1_struct_0(sK0),u1_waybel_0(sK0,sK1)),X0)
        | ~ r3_waybel_9(sK0,sK1,X0) )
    | ~ spl9_3
    | ~ spl9_42 ),
    inference(resolution,[],[f325,f121])).

fof(f121,plain,
    ( v10_waybel_0(sK1,sK0)
    | ~ spl9_3 ),
    inference(avatar_component_clause,[],[f120])).

fof(f325,plain,
    ( ! [X0,X1] :
        ( ~ v10_waybel_0(X0,sK0)
        | v2_struct_0(X0)
        | ~ v4_orders_2(X0)
        | ~ v7_waybel_0(X0)
        | ~ l1_waybel_0(X0,sK0)
        | ~ m1_subset_1(X1,u1_struct_0(sK0))
        | r2_lattice3(sK0,k2_relset_1(u1_struct_0(X0),u1_struct_0(sK0),u1_waybel_0(sK0,X0)),X1)
        | ~ r3_waybel_9(sK0,X0,X1) )
    | ~ spl9_42 ),
    inference(avatar_component_clause,[],[f324])).

fof(f326,plain,
    ( ~ spl9_16
    | ~ spl9_15
    | ~ spl9_14
    | ~ spl9_13
    | ~ spl9_12
    | ~ spl9_11
    | ~ spl9_10
    | ~ spl9_9
    | ~ spl9_8
    | spl9_42
    | spl9_41 ),
    inference(avatar_split_clause,[],[f322,f319,f324,f140,f144,f148,f152,f156,f160,f164,f168,f172])).

fof(f319,plain,
    ( spl9_41
  <=> m1_subset_1(sK7(sK0),u1_struct_0(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_41])])).

fof(f322,plain,
    ( ! [X0,X1] :
        ( ~ r3_waybel_9(sK0,X0,X1)
        | ~ v10_waybel_0(X0,sK0)
        | r2_lattice3(sK0,k2_relset_1(u1_struct_0(X0),u1_struct_0(sK0),u1_waybel_0(sK0,X0)),X1)
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
    | spl9_41 ),
    inference(resolution,[],[f320,f110])).

fof(f110,plain,(
    ! [X0,X3,X1] :
      ( m1_subset_1(sK7(X0),u1_struct_0(X0))
      | ~ r3_waybel_9(X0,X1,X3)
      | ~ v10_waybel_0(X1,X0)
      | r2_lattice3(X0,k2_relset_1(u1_struct_0(X1),u1_struct_0(X0),u1_waybel_0(X0,X1)),X3)
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
    inference(duplicate_literal_removal,[],[f105])).

fof(f105,plain,(
    ! [X0,X3,X1] :
      ( r2_lattice3(X0,k2_relset_1(u1_struct_0(X1),u1_struct_0(X0),u1_waybel_0(X0,X1)),X3)
      | ~ r3_waybel_9(X0,X1,X3)
      | ~ v10_waybel_0(X1,X0)
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
    inference(equality_resolution,[],[f96])).

fof(f96,plain,(
    ! [X2,X0,X3,X1] :
      ( r2_lattice3(X0,k2_relset_1(u1_struct_0(X1),u1_struct_0(X0),u1_waybel_0(X0,X1)),X3)
      | ~ r3_waybel_9(X0,X1,X2)
      | ~ v10_waybel_0(X1,X0)
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
    inference(cnf_transformation,[],[f53])).

fof(f320,plain,
    ( ~ m1_subset_1(sK7(sK0),u1_struct_0(sK0))
    | spl9_41 ),
    inference(avatar_component_clause,[],[f319])).

fof(f321,plain,
    ( ~ spl9_41
    | spl9_36 ),
    inference(avatar_split_clause,[],[f317,f299,f319])).

fof(f317,plain,
    ( ~ m1_subset_1(sK7(sK0),u1_struct_0(sK0))
    | spl9_36 ),
    inference(resolution,[],[f300,f67])).

fof(f67,plain,(
    ! [X2] :
      ( v5_pre_topc(k4_waybel_1(sK0,X2),sK0,sK0)
      | ~ m1_subset_1(X2,u1_struct_0(sK0)) ) ),
    inference(cnf_transformation,[],[f40])).

fof(f40,plain,
    ( ( ~ r2_hidden(k1_waybel_2(sK0,sK1),k10_yellow_6(sK0,sK1))
      | ~ r1_waybel_9(sK0,sK1) )
    & v10_waybel_0(sK1,sK0)
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
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f37,f39,f38])).

fof(f38,plain,
    ( ? [X0] :
        ( ? [X1] :
            ( ( ~ r2_hidden(k1_waybel_2(X0,X1),k10_yellow_6(X0,X1))
              | ~ r1_waybel_9(X0,X1) )
            & v10_waybel_0(X1,X0)
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
          ( ( ~ r2_hidden(k1_waybel_2(sK0,X1),k10_yellow_6(sK0,X1))
            | ~ r1_waybel_9(sK0,X1) )
          & v10_waybel_0(X1,sK0)
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

fof(f39,plain,
    ( ? [X1] :
        ( ( ~ r2_hidden(k1_waybel_2(sK0,X1),k10_yellow_6(sK0,X1))
          | ~ r1_waybel_9(sK0,X1) )
        & v10_waybel_0(X1,sK0)
        & l1_waybel_0(X1,sK0)
        & v7_waybel_0(X1)
        & v4_orders_2(X1)
        & ~ v2_struct_0(X1) )
   => ( ( ~ r2_hidden(k1_waybel_2(sK0,sK1),k10_yellow_6(sK0,sK1))
        | ~ r1_waybel_9(sK0,sK1) )
      & v10_waybel_0(sK1,sK0)
      & l1_waybel_0(sK1,sK0)
      & v7_waybel_0(sK1)
      & v4_orders_2(sK1)
      & ~ v2_struct_0(sK1) ) ),
    introduced(choice_axiom,[])).

fof(f37,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ( ~ r2_hidden(k1_waybel_2(X0,X1),k10_yellow_6(X0,X1))
            | ~ r1_waybel_9(X0,X1) )
          & v10_waybel_0(X1,X0)
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
    inference(rectify,[],[f18])).

fof(f18,plain,(
    ? [X0] :
      ( ? [X2] :
          ( ( ~ r2_hidden(k1_waybel_2(X0,X2),k10_yellow_6(X0,X2))
            | ~ r1_waybel_9(X0,X2) )
          & v10_waybel_0(X2,X0)
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
    inference(flattening,[],[f17])).

fof(f17,plain,(
    ? [X0] :
      ( ? [X2] :
          ( ( ~ r2_hidden(k1_waybel_2(X0,X2),k10_yellow_6(X0,X2))
            | ~ r1_waybel_9(X0,X2) )
          & v10_waybel_0(X2,X0)
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
    inference(ennf_transformation,[],[f13])).

fof(f13,plain,(
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
             => ( v10_waybel_0(X2,X0)
               => ( r2_hidden(k1_waybel_2(X0,X2),k10_yellow_6(X0,X2))
                  & r1_waybel_9(X0,X2) ) ) ) ) ) ),
    inference(rectify,[],[f12])).

fof(f12,negated_conjecture,(
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
             => ( v10_waybel_0(X1,X0)
               => ( r2_hidden(k1_waybel_2(X0,X1),k10_yellow_6(X0,X1))
                  & r1_waybel_9(X0,X1) ) ) ) ) ) ),
    inference(negated_conjecture,[],[f11])).

fof(f11,conjecture,(
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
           => ( v10_waybel_0(X1,X0)
             => ( r2_hidden(k1_waybel_2(X0,X1),k10_yellow_6(X0,X1))
                & r1_waybel_9(X0,X1) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t38_waybel_9)).

fof(f300,plain,
    ( ~ v5_pre_topc(k4_waybel_1(sK0,sK7(sK0)),sK0,sK0)
    | spl9_36 ),
    inference(avatar_component_clause,[],[f299])).

fof(f316,plain,
    ( ~ spl9_12
    | ~ spl9_33
    | spl9_39
    | spl9_40
    | ~ spl9_35 ),
    inference(avatar_split_clause,[],[f296,f286,f314,f311,f274,f156])).

fof(f286,plain,
    ( spl9_35
  <=> ! [X0] :
        ( ~ r2_lattice3(sK0,k2_relset_1(u1_struct_0(sK1),u1_struct_0(sK0),u1_waybel_0(sK0,sK1)),X0)
        | r1_orders_2(sK0,k1_waybel_2(sK0,sK1),X0)
        | ~ m1_subset_1(X0,u1_struct_0(sK0)) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_35])])).

fof(f296,plain,
    ( ! [X2] :
        ( r1_orders_2(sK0,k1_waybel_2(sK0,sK1),sK5(sK0,X2,k2_relset_1(u1_struct_0(sK1),u1_struct_0(sK0),u1_waybel_0(sK0,sK1))))
        | ~ m1_subset_1(sK5(sK0,X2,k2_relset_1(u1_struct_0(sK1),u1_struct_0(sK0),u1_waybel_0(sK0,sK1))),u1_struct_0(sK0))
        | r1_yellow_0(sK0,k2_relset_1(u1_struct_0(sK1),u1_struct_0(sK0),u1_waybel_0(sK0,sK1)))
        | ~ r2_lattice3(sK0,k2_relset_1(u1_struct_0(sK1),u1_struct_0(sK0),u1_waybel_0(sK0,sK1)),X2)
        | ~ m1_subset_1(X2,u1_struct_0(sK0))
        | ~ l1_orders_2(sK0)
        | ~ v5_orders_2(sK0) )
    | ~ spl9_35 ),
    inference(resolution,[],[f287,f92])).

fof(f92,plain,(
    ! [X2,X0,X1] :
      ( r2_lattice3(X0,X2,sK5(X0,X1,X2))
      | r1_yellow_0(X0,X2)
      | ~ r2_lattice3(X0,X2,X1)
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | ~ v5_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f49])).

fof(f287,plain,
    ( ! [X0] :
        ( ~ r2_lattice3(sK0,k2_relset_1(u1_struct_0(sK1),u1_struct_0(sK0),u1_waybel_0(sK0,sK1)),X0)
        | r1_orders_2(sK0,k1_waybel_2(sK0,sK1),X0)
        | ~ m1_subset_1(X0,u1_struct_0(sK0)) )
    | ~ spl9_35 ),
    inference(avatar_component_clause,[],[f286])).

fof(f293,plain,
    ( ~ spl9_33
    | ~ spl9_11
    | ~ spl9_22 ),
    inference(avatar_split_clause,[],[f292,f219,f152,f274])).

fof(f292,plain,
    ( ~ v1_lattice3(sK0)
    | ~ l1_orders_2(sK0)
    | ~ spl9_22 ),
    inference(resolution,[],[f220,f76])).

fof(f76,plain,(
    ! [X0] :
      ( ~ v2_struct_0(X0)
      | ~ v1_lattice3(X0)
      | ~ l1_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f21,plain,(
    ! [X0] :
      ( ~ v2_struct_0(X0)
      | ~ v1_lattice3(X0)
      | ~ l1_orders_2(X0) ) ),
    inference(flattening,[],[f20])).

fof(f20,plain,(
    ! [X0] :
      ( ~ v2_struct_0(X0)
      | ~ v1_lattice3(X0)
      | ~ l1_orders_2(X0) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0] :
      ( l1_orders_2(X0)
     => ( v1_lattice3(X0)
       => ~ v2_struct_0(X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_lattice3)).

fof(f220,plain,
    ( v2_struct_0(sK0)
    | ~ spl9_22 ),
    inference(avatar_component_clause,[],[f219])).

fof(f291,plain,
    ( spl9_22
    | ~ spl9_16
    | ~ spl9_15
    | ~ spl9_9
    | ~ spl9_23
    | spl9_7
    | ~ spl9_6
    | ~ spl9_5
    | ~ spl9_4
    | spl9_35
    | ~ spl9_27
    | ~ spl9_24
    | ~ spl9_34 ),
    inference(avatar_split_clause,[],[f290,f277,f225,f242,f286,f124,f128,f132,f136,f222,f144,f168,f172,f219])).

fof(f225,plain,
    ( spl9_24
  <=> k1_waybel_2(sK0,sK1) = sK4(sK0,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_24])])).

fof(f277,plain,
    ( spl9_34
  <=> ! [X1,X0] :
        ( ~ m1_subset_1(X0,u1_struct_0(sK0))
        | ~ r2_lattice3(sK0,k2_relset_1(u1_struct_0(sK1),u1_struct_0(sK0),u1_waybel_0(sK0,sK1)),X0)
        | ~ r3_waybel_9(sK0,sK1,X1)
        | r1_orders_2(sK0,X1,X0)
        | ~ m1_subset_1(X1,u1_struct_0(sK0)) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_34])])).

fof(f290,plain,
    ( ! [X1] :
        ( ~ m1_subset_1(k1_waybel_2(sK0,sK1),u1_struct_0(sK0))
        | r1_orders_2(sK0,k1_waybel_2(sK0,sK1),X1)
        | ~ r2_lattice3(sK0,k2_relset_1(u1_struct_0(sK1),u1_struct_0(sK0),u1_waybel_0(sK0,sK1)),X1)
        | ~ m1_subset_1(X1,u1_struct_0(sK0))
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
    | ~ spl9_34 ),
    inference(forward_demodulation,[],[f289,f226])).

fof(f226,plain,
    ( k1_waybel_2(sK0,sK1) = sK4(sK0,sK1)
    | ~ spl9_24 ),
    inference(avatar_component_clause,[],[f225])).

fof(f289,plain,
    ( ! [X1] :
        ( r1_orders_2(sK0,k1_waybel_2(sK0,sK1),X1)
        | ~ r2_lattice3(sK0,k2_relset_1(u1_struct_0(sK1),u1_struct_0(sK0),u1_waybel_0(sK0,sK1)),X1)
        | ~ m1_subset_1(X1,u1_struct_0(sK0))
        | ~ m1_subset_1(sK4(sK0,sK1),u1_struct_0(sK0))
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
    | ~ spl9_34 ),
    inference(forward_demodulation,[],[f283,f226])).

fof(f283,plain,
    ( ! [X1] :
        ( ~ r2_lattice3(sK0,k2_relset_1(u1_struct_0(sK1),u1_struct_0(sK0),u1_waybel_0(sK0,sK1)),X1)
        | ~ m1_subset_1(X1,u1_struct_0(sK0))
        | r1_orders_2(sK0,sK4(sK0,sK1),X1)
        | ~ m1_subset_1(sK4(sK0,sK1),u1_struct_0(sK0))
        | ~ l1_waybel_0(sK1,sK0)
        | ~ v7_waybel_0(sK1)
        | ~ v4_orders_2(sK1)
        | v2_struct_0(sK1)
        | ~ l1_pre_topc(sK0)
        | ~ v1_compts_1(sK0)
        | ~ v8_pre_topc(sK0)
        | ~ v2_pre_topc(sK0)
        | v2_struct_0(sK0) )
    | ~ spl9_34 ),
    inference(resolution,[],[f278,f85])).

fof(f85,plain,(
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
    inference(cnf_transformation,[],[f47])).

% (3881)Refutation not found, incomplete strategy% (3881)------------------------------
% (3881)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% (3881)Termination reason: Refutation not found, incomplete strategy

% (3881)Memory used [KB]: 7036
% (3881)Time elapsed: 0.121 s
% (3881)------------------------------
% (3881)------------------------------
fof(f47,plain,(
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
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4])],[f26,f46])).

fof(f46,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( r3_waybel_9(X0,X1,X2)
          & m1_subset_1(X2,u1_struct_0(X0)) )
     => ( r3_waybel_9(X0,X1,sK4(X0,X1))
        & m1_subset_1(sK4(X0,X1),u1_struct_0(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f26,plain,(
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
    inference(flattening,[],[f25])).

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
    inference(ennf_transformation,[],[f8])).

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
         => ? [X2] :
              ( r3_waybel_9(X0,X1,X2)
              & m1_subset_1(X2,u1_struct_0(X0)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t30_waybel_9)).

fof(f278,plain,
    ( ! [X0,X1] :
        ( ~ r3_waybel_9(sK0,sK1,X1)
        | ~ r2_lattice3(sK0,k2_relset_1(u1_struct_0(sK1),u1_struct_0(sK0),u1_waybel_0(sK0,sK1)),X0)
        | ~ m1_subset_1(X0,u1_struct_0(sK0))
        | r1_orders_2(sK0,X1,X0)
        | ~ m1_subset_1(X1,u1_struct_0(sK0)) )
    | ~ spl9_34 ),
    inference(avatar_component_clause,[],[f277])).

fof(f281,plain,
    ( ~ spl9_8
    | spl9_33 ),
    inference(avatar_split_clause,[],[f280,f274,f140])).

fof(f280,plain,
    ( ~ l1_waybel_9(sK0)
    | spl9_33 ),
    inference(resolution,[],[f275,f75])).

fof(f275,plain,
    ( ~ l1_orders_2(sK0)
    | spl9_33 ),
    inference(avatar_component_clause,[],[f274])).

fof(f279,plain,
    ( spl9_22
    | ~ spl9_14
    | ~ spl9_33
    | spl9_34
    | ~ spl9_30 ),
    inference(avatar_split_clause,[],[f272,f256,f277,f274,f164,f219])).

fof(f256,plain,
    ( spl9_30
  <=> ! [X1,X0] :
        ( ~ r2_lattice3(sK0,k2_relset_1(u1_struct_0(sK1),u1_struct_0(sK0),u1_waybel_0(sK0,sK1)),X0)
        | ~ m1_subset_1(X0,u1_struct_0(sK0))
        | ~ r3_waybel_9(sK0,sK1,X1)
        | ~ m1_subset_1(X1,u1_struct_0(sK0))
        | r3_orders_2(sK0,X1,X0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_30])])).

fof(f272,plain,
    ( ! [X0,X1] :
        ( ~ m1_subset_1(X0,u1_struct_0(sK0))
        | ~ r3_waybel_9(sK0,sK1,X1)
        | ~ m1_subset_1(X1,u1_struct_0(sK0))
        | ~ r2_lattice3(sK0,k2_relset_1(u1_struct_0(sK1),u1_struct_0(sK0),u1_waybel_0(sK0,sK1)),X0)
        | r1_orders_2(sK0,X1,X0)
        | ~ l1_orders_2(sK0)
        | ~ v3_orders_2(sK0)
        | v2_struct_0(sK0) )
    | ~ spl9_30 ),
    inference(duplicate_literal_removal,[],[f271])).

fof(f271,plain,
    ( ! [X0,X1] :
        ( ~ m1_subset_1(X0,u1_struct_0(sK0))
        | ~ r3_waybel_9(sK0,sK1,X1)
        | ~ m1_subset_1(X1,u1_struct_0(sK0))
        | ~ r2_lattice3(sK0,k2_relset_1(u1_struct_0(sK1),u1_struct_0(sK0),u1_waybel_0(sK0,sK1)),X0)
        | r1_orders_2(sK0,X1,X0)
        | ~ m1_subset_1(X0,u1_struct_0(sK0))
        | ~ m1_subset_1(X1,u1_struct_0(sK0))
        | ~ l1_orders_2(sK0)
        | ~ v3_orders_2(sK0)
        | v2_struct_0(sK0) )
    | ~ spl9_30 ),
    inference(resolution,[],[f257,f100])).

fof(f100,plain,(
    ! [X2,X0,X1] :
      ( ~ r3_orders_2(X0,X1,X2)
      | r1_orders_2(X0,X1,X2)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f57])).

fof(f57,plain,(
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
    inference(nnf_transformation,[],[f36])).

fof(f36,plain,(
    ! [X0,X1,X2] :
      ( ( r3_orders_2(X0,X1,X2)
      <=> r1_orders_2(X0,X1,X2) )
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f35])).

fof(f35,plain,(
    ! [X0,X1,X2] :
      ( ( r3_orders_2(X0,X1,X2)
      <=> r1_orders_2(X0,X1,X2) )
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,u1_struct_0(X0))
        & m1_subset_1(X1,u1_struct_0(X0))
        & l1_orders_2(X0)
        & v3_orders_2(X0)
        & ~ v2_struct_0(X0) )
     => ( r3_orders_2(X0,X1,X2)
      <=> r1_orders_2(X0,X1,X2) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_r3_orders_2)).

fof(f257,plain,
    ( ! [X0,X1] :
        ( r3_orders_2(sK0,X1,X0)
        | ~ m1_subset_1(X0,u1_struct_0(sK0))
        | ~ r3_waybel_9(sK0,sK1,X1)
        | ~ m1_subset_1(X1,u1_struct_0(sK0))
        | ~ r2_lattice3(sK0,k2_relset_1(u1_struct_0(sK1),u1_struct_0(sK0),u1_waybel_0(sK0,sK1)),X0) )
    | ~ spl9_30 ),
    inference(avatar_component_clause,[],[f256])).

fof(f270,plain,
    ( ~ spl9_4
    | spl9_30
    | ~ spl9_6
    | spl9_7
    | ~ spl9_5
    | ~ spl9_32 ),
    inference(avatar_split_clause,[],[f269,f266,f128,f136,f132,f256,f124])).

fof(f266,plain,
    ( spl9_32
  <=> ! [X1,X0,X2] :
        ( ~ r2_lattice3(sK0,k2_relset_1(u1_struct_0(X0),u1_struct_0(sK0),u1_waybel_0(sK0,X0)),X1)
        | v2_struct_0(X0)
        | ~ v4_orders_2(X0)
        | ~ v7_waybel_0(X0)
        | ~ l1_waybel_0(X0,sK0)
        | ~ m1_subset_1(X2,u1_struct_0(sK0))
        | r3_orders_2(sK0,X2,X1)
        | ~ r3_waybel_9(sK0,X0,X2)
        | ~ m1_subset_1(X1,u1_struct_0(sK0)) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_32])])).

fof(f269,plain,
    ( ! [X0,X1] :
        ( v2_struct_0(sK1)
        | ~ v4_orders_2(sK1)
        | ~ r2_lattice3(sK0,k2_relset_1(u1_struct_0(sK1),u1_struct_0(sK0),u1_waybel_0(sK0,sK1)),X0)
        | ~ l1_waybel_0(sK1,sK0)
        | ~ m1_subset_1(X1,u1_struct_0(sK0))
        | r3_orders_2(sK0,X1,X0)
        | ~ r3_waybel_9(sK0,sK1,X1)
        | ~ m1_subset_1(X0,u1_struct_0(sK0)) )
    | ~ spl9_5
    | ~ spl9_32 ),
    inference(resolution,[],[f267,f129])).

fof(f129,plain,
    ( v7_waybel_0(sK1)
    | ~ spl9_5 ),
    inference(avatar_component_clause,[],[f128])).

fof(f267,plain,
    ( ! [X2,X0,X1] :
        ( ~ v7_waybel_0(X0)
        | v2_struct_0(X0)
        | ~ v4_orders_2(X0)
        | ~ r2_lattice3(sK0,k2_relset_1(u1_struct_0(X0),u1_struct_0(sK0),u1_waybel_0(sK0,X0)),X1)
        | ~ l1_waybel_0(X0,sK0)
        | ~ m1_subset_1(X2,u1_struct_0(sK0))
        | r3_orders_2(sK0,X2,X1)
        | ~ r3_waybel_9(sK0,X0,X2)
        | ~ m1_subset_1(X1,u1_struct_0(sK0)) )
    | ~ spl9_32 ),
    inference(avatar_component_clause,[],[f266])).

fof(f268,plain,
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
    inference(avatar_split_clause,[],[f264,f261,f266,f140,f144,f148,f152,f156,f160,f164,f168,f172])).

fof(f261,plain,
    ( spl9_31
  <=> m1_subset_1(sK8(sK0),u1_struct_0(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_31])])).

fof(f264,plain,
    ( ! [X2,X0,X1] :
        ( ~ r2_lattice3(sK0,k2_relset_1(u1_struct_0(X0),u1_struct_0(sK0),u1_waybel_0(sK0,X0)),X1)
        | ~ m1_subset_1(X1,u1_struct_0(sK0))
        | ~ r3_waybel_9(sK0,X0,X2)
        | r3_orders_2(sK0,X2,X1)
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
    inference(resolution,[],[f262,f108])).

fof(f108,plain,(
    ! [X4,X0,X3,X1] :
      ( m1_subset_1(sK8(X0),u1_struct_0(X0))
      | ~ r2_lattice3(X0,k2_relset_1(u1_struct_0(X1),u1_struct_0(X0),u1_waybel_0(X0,X1)),X4)
      | ~ m1_subset_1(X4,u1_struct_0(X0))
      | ~ r3_waybel_9(X0,X1,X3)
      | r3_orders_2(X0,X3,X4)
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
    inference(duplicate_literal_removal,[],[f107])).

fof(f107,plain,(
    ! [X4,X0,X3,X1] :
      ( r3_orders_2(X0,X3,X4)
      | ~ r2_lattice3(X0,k2_relset_1(u1_struct_0(X1),u1_struct_0(X0),u1_waybel_0(X0,X1)),X4)
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
    inference(equality_resolution,[],[f98])).

fof(f98,plain,(
    ! [X4,X2,X0,X3,X1] :
      ( r3_orders_2(X0,X3,X4)
      | ~ r2_lattice3(X0,k2_relset_1(u1_struct_0(X1),u1_struct_0(X0),u1_waybel_0(X0,X1)),X4)
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
    inference(cnf_transformation,[],[f56])).

fof(f56,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( ! [X4] :
                      ( r3_orders_2(X0,X3,X4)
                      | ~ r2_lattice3(X0,k2_relset_1(u1_struct_0(X1),u1_struct_0(X0),u1_waybel_0(X0,X1)),X4)
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
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK8])],[f54,f55])).

fof(f55,plain,(
    ! [X0] :
      ( ? [X5] :
          ( ~ v5_pre_topc(k4_waybel_1(X0,X5),X0,X0)
          & m1_subset_1(X5,u1_struct_0(X0)) )
     => ( ~ v5_pre_topc(k4_waybel_1(X0,sK8(X0)),X0,X0)
        & m1_subset_1(sK8(X0),u1_struct_0(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f54,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( ! [X4] :
                      ( r3_orders_2(X0,X3,X4)
                      | ~ r2_lattice3(X0,k2_relset_1(u1_struct_0(X1),u1_struct_0(X0),u1_waybel_0(X0,X1)),X4)
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
    inference(rectify,[],[f34])).

fof(f34,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( ! [X5] :
                      ( r3_orders_2(X0,X3,X5)
                      | ~ r2_lattice3(X0,k2_relset_1(u1_struct_0(X1),u1_struct_0(X0),u1_waybel_0(X0,X1)),X5)
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
    inference(flattening,[],[f33])).

fof(f33,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( ! [X5] :
                      ( r3_orders_2(X0,X3,X5)
                      | ~ r2_lattice3(X0,k2_relset_1(u1_struct_0(X1),u1_struct_0(X0),u1_waybel_0(X0,X1)),X5)
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
    inference(ennf_transformation,[],[f16])).

fof(f16,plain,(
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
                       => ( r2_lattice3(X0,k2_relset_1(u1_struct_0(X1),u1_struct_0(X0),u1_waybel_0(X0,X1)),X5)
                         => r3_orders_2(X0,X3,X5) ) ) ) ) ) ) ) ),
    inference(rectify,[],[f7])).

fof(f7,axiom,(
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
                       => ( r2_lattice3(X0,k2_relset_1(u1_struct_0(X1),u1_struct_0(X0),u1_waybel_0(X0,X1)),X4)
                         => r3_orders_2(X0,X3,X4) ) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l49_waybel_9)).

fof(f262,plain,
    ( ~ m1_subset_1(sK8(sK0),u1_struct_0(sK0))
    | spl9_31 ),
    inference(avatar_component_clause,[],[f261])).

fof(f263,plain,
    ( ~ spl9_31
    | spl9_29 ),
    inference(avatar_split_clause,[],[f259,f253,f261])).

fof(f253,plain,
    ( spl9_29
  <=> v5_pre_topc(k4_waybel_1(sK0,sK8(sK0)),sK0,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_29])])).

fof(f259,plain,
    ( ~ m1_subset_1(sK8(sK0),u1_struct_0(sK0))
    | spl9_29 ),
    inference(resolution,[],[f254,f67])).

fof(f254,plain,
    ( ~ v5_pre_topc(k4_waybel_1(sK0,sK8(sK0)),sK0,sK0)
    | spl9_29 ),
    inference(avatar_component_clause,[],[f253])).

fof(f258,plain,
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
    inference(avatar_split_clause,[],[f251,f248,f144,f172,f168,f164,f160,f156,f152,f148,f256,f140,f124,f253])).

fof(f248,plain,
    ( spl9_28
  <=> ! [X1,X0,X2] :
        ( ~ r2_lattice3(X0,k2_relset_1(u1_struct_0(sK1),u1_struct_0(X0),u1_waybel_0(X0,sK1)),X1)
        | ~ v2_pre_topc(X0)
        | ~ v8_pre_topc(X0)
        | ~ v3_orders_2(X0)
        | ~ v4_orders_2(X0)
        | ~ v5_orders_2(X0)
        | ~ v1_lattice3(X0)
        | ~ v2_lattice3(X0)
        | ~ v1_compts_1(X0)
        | ~ l1_waybel_9(X0)
        | r3_orders_2(X0,X2,X1)
        | ~ l1_waybel_0(sK1,X0)
        | ~ m1_subset_1(X2,u1_struct_0(X0))
        | ~ v5_pre_topc(k4_waybel_1(X0,sK8(X0)),X0,X0)
        | ~ r3_waybel_9(X0,sK1,X2)
        | ~ m1_subset_1(X1,u1_struct_0(X0)) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_28])])).

fof(f251,plain,
    ( ! [X0,X1] :
        ( ~ v2_pre_topc(sK0)
        | ~ v8_pre_topc(sK0)
        | ~ v3_orders_2(sK0)
        | ~ v4_orders_2(sK0)
        | ~ v5_orders_2(sK0)
        | ~ v1_lattice3(sK0)
        | ~ v2_lattice3(sK0)
        | ~ r2_lattice3(sK0,k2_relset_1(u1_struct_0(sK1),u1_struct_0(sK0),u1_waybel_0(sK0,sK1)),X0)
        | ~ l1_waybel_9(sK0)
        | r3_orders_2(sK0,X1,X0)
        | ~ l1_waybel_0(sK1,sK0)
        | ~ m1_subset_1(X1,u1_struct_0(sK0))
        | ~ v5_pre_topc(k4_waybel_1(sK0,sK8(sK0)),sK0,sK0)
        | ~ r3_waybel_9(sK0,sK1,X1)
        | ~ m1_subset_1(X0,u1_struct_0(sK0)) )
    | ~ spl9_9
    | ~ spl9_28 ),
    inference(resolution,[],[f249,f145])).

fof(f145,plain,
    ( v1_compts_1(sK0)
    | ~ spl9_9 ),
    inference(avatar_component_clause,[],[f144])).

fof(f249,plain,
    ( ! [X2,X0,X1] :
        ( ~ v1_compts_1(X0)
        | ~ v2_pre_topc(X0)
        | ~ v8_pre_topc(X0)
        | ~ v3_orders_2(X0)
        | ~ v4_orders_2(X0)
        | ~ v5_orders_2(X0)
        | ~ v1_lattice3(X0)
        | ~ v2_lattice3(X0)
        | ~ r2_lattice3(X0,k2_relset_1(u1_struct_0(sK1),u1_struct_0(X0),u1_waybel_0(X0,sK1)),X1)
        | ~ l1_waybel_9(X0)
        | r3_orders_2(X0,X2,X1)
        | ~ l1_waybel_0(sK1,X0)
        | ~ m1_subset_1(X2,u1_struct_0(X0))
        | ~ v5_pre_topc(k4_waybel_1(X0,sK8(X0)),X0,X0)
        | ~ r3_waybel_9(X0,sK1,X2)
        | ~ m1_subset_1(X1,u1_struct_0(X0)) )
    | ~ spl9_28 ),
    inference(avatar_component_clause,[],[f248])).

fof(f250,plain,
    ( spl9_7
    | ~ spl9_6
    | spl9_28
    | ~ spl9_5 ),
    inference(avatar_split_clause,[],[f246,f128,f248,f132,f136])).

fof(f246,plain,
    ( ! [X2,X0,X1] :
        ( ~ r2_lattice3(X0,k2_relset_1(u1_struct_0(sK1),u1_struct_0(X0),u1_waybel_0(X0,sK1)),X1)
        | ~ m1_subset_1(X1,u1_struct_0(X0))
        | ~ r3_waybel_9(X0,sK1,X2)
        | ~ v5_pre_topc(k4_waybel_1(X0,sK8(X0)),X0,X0)
        | ~ m1_subset_1(X2,u1_struct_0(X0))
        | ~ l1_waybel_0(sK1,X0)
        | r3_orders_2(X0,X2,X1)
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
    inference(resolution,[],[f109,f129])).

fof(f109,plain,(
    ! [X4,X0,X3,X1] :
      ( ~ v7_waybel_0(X1)
      | ~ r2_lattice3(X0,k2_relset_1(u1_struct_0(X1),u1_struct_0(X0),u1_waybel_0(X0,X1)),X4)
      | ~ m1_subset_1(X4,u1_struct_0(X0))
      | ~ r3_waybel_9(X0,X1,X3)
      | ~ v5_pre_topc(k4_waybel_1(X0,sK8(X0)),X0,X0)
      | ~ m1_subset_1(X3,u1_struct_0(X0))
      | ~ l1_waybel_0(X1,X0)
      | r3_orders_2(X0,X3,X4)
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
    inference(duplicate_literal_removal,[],[f106])).

fof(f106,plain,(
    ! [X4,X0,X3,X1] :
      ( r3_orders_2(X0,X3,X4)
      | ~ r2_lattice3(X0,k2_relset_1(u1_struct_0(X1),u1_struct_0(X0),u1_waybel_0(X0,X1)),X4)
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
    inference(equality_resolution,[],[f99])).

fof(f99,plain,(
    ! [X4,X2,X0,X3,X1] :
      ( r3_orders_2(X0,X3,X4)
      | ~ r2_lattice3(X0,k2_relset_1(u1_struct_0(X1),u1_struct_0(X0),u1_waybel_0(X0,X1)),X4)
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
    inference(cnf_transformation,[],[f56])).

fof(f244,plain,
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
    inference(avatar_split_clause,[],[f236,f225,f242,f124,f128,f132,f136,f222,f144,f168,f172,f219])).

fof(f236,plain,
    ( m1_subset_1(k1_waybel_2(sK0,sK1),u1_struct_0(sK0))
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
    inference(superposition,[],[f84,f226])).

fof(f84,plain,(
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
    inference(cnf_transformation,[],[f47])).

fof(f240,plain,
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
    inference(avatar_split_clause,[],[f235,f225,f238,f124,f128,f132,f136,f222,f144,f168,f172,f219])).

fof(f235,plain,
    ( r3_waybel_9(sK0,sK1,k1_waybel_2(sK0,sK1))
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
    inference(superposition,[],[f85,f226])).

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
    | spl9_25 ),
    inference(avatar_split_clause,[],[f233,f228,f124,f128,f132,f136,f222,f144,f168,f172,f219])).

fof(f228,plain,
    ( spl9_25
  <=> m1_subset_1(sK4(sK0,sK1),u1_struct_0(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_25])])).

fof(f233,plain,
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
    inference(resolution,[],[f229,f84])).

fof(f229,plain,
    ( ~ m1_subset_1(sK4(sK0,sK1),u1_struct_0(sK0))
    | spl9_25 ),
    inference(avatar_component_clause,[],[f228])).

fof(f232,plain,
    ( ~ spl9_8
    | spl9_23 ),
    inference(avatar_split_clause,[],[f231,f222,f140])).

fof(f231,plain,
    ( ~ l1_waybel_9(sK0)
    | spl9_23 ),
    inference(resolution,[],[f223,f74])).

fof(f74,plain,(
    ! [X0] :
      ( l1_pre_topc(X0)
      | ~ l1_waybel_9(X0) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f223,plain,
    ( ~ l1_pre_topc(sK0)
    | spl9_23 ),
    inference(avatar_component_clause,[],[f222])).

fof(f230,plain,
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
    inference(avatar_split_clause,[],[f217,f192,f228,f225,f124,f128,f132,f136,f222,f144,f168,f172,f219])).

fof(f217,plain,
    ( ~ m1_subset_1(sK4(sK0,sK1),u1_struct_0(sK0))
    | k1_waybel_2(sK0,sK1) = sK4(sK0,sK1)
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
    inference(resolution,[],[f193,f85])).

fof(f216,plain,
    ( ~ spl9_4
    | ~ spl9_5
    | ~ spl9_6
    | spl9_7
    | spl9_19
    | ~ spl9_3
    | ~ spl9_21 ),
    inference(avatar_split_clause,[],[f214,f211,f120,f192,f136,f132,f128,f124])).

fof(f211,plain,
    ( spl9_21
  <=> ! [X1,X0] :
        ( ~ r3_waybel_9(sK0,X0,X1)
        | ~ m1_subset_1(X1,u1_struct_0(sK0))
        | v2_struct_0(X0)
        | ~ v4_orders_2(X0)
        | ~ v7_waybel_0(X0)
        | ~ l1_waybel_0(X0,sK0)
        | k1_waybel_2(sK0,X0) = X1
        | ~ v10_waybel_0(X0,sK0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_21])])).

fof(f214,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(X0,u1_struct_0(sK0))
        | v2_struct_0(sK1)
        | ~ v4_orders_2(sK1)
        | ~ v7_waybel_0(sK1)
        | ~ l1_waybel_0(sK1,sK0)
        | k1_waybel_2(sK0,sK1) = X0
        | ~ r3_waybel_9(sK0,sK1,X0) )
    | ~ spl9_3
    | ~ spl9_21 ),
    inference(resolution,[],[f212,f121])).

fof(f212,plain,
    ( ! [X0,X1] :
        ( ~ v10_waybel_0(X0,sK0)
        | ~ m1_subset_1(X1,u1_struct_0(sK0))
        | v2_struct_0(X0)
        | ~ v4_orders_2(X0)
        | ~ v7_waybel_0(X0)
        | ~ l1_waybel_0(X0,sK0)
        | k1_waybel_2(sK0,X0) = X1
        | ~ r3_waybel_9(sK0,X0,X1) )
    | ~ spl9_21 ),
    inference(avatar_component_clause,[],[f211])).

fof(f213,plain,
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
    inference(avatar_split_clause,[],[f209,f206,f211,f140,f144,f148,f152,f156,f160,f164,f168,f172])).

fof(f206,plain,
    ( spl9_20
  <=> m1_subset_1(sK6(sK0),u1_struct_0(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_20])])).

fof(f209,plain,
    ( ! [X0,X1] :
        ( ~ r3_waybel_9(sK0,X0,X1)
        | ~ v10_waybel_0(X0,sK0)
        | k1_waybel_2(sK0,X0) = X1
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
    inference(resolution,[],[f207,f94])).

fof(f94,plain,(
    ! [X2,X0,X1] :
      ( m1_subset_1(sK6(X0),u1_struct_0(X0))
      | ~ r3_waybel_9(X0,X2,X1)
      | ~ v10_waybel_0(X2,X0)
      | k1_waybel_2(X0,X2) = X1
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
    inference(cnf_transformation,[],[f51])).

fof(f51,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( k1_waybel_2(X0,X2) = X1
              | ~ r3_waybel_9(X0,X2,X1)
              | ~ v10_waybel_0(X2,X0)
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
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK6])],[f30,f50])).

fof(f50,plain,(
    ! [X0] :
      ( ? [X3] :
          ( ~ v5_pre_topc(k4_waybel_1(X0,X3),X0,X0)
          & m1_subset_1(X3,u1_struct_0(X0)) )
     => ( ~ v5_pre_topc(k4_waybel_1(X0,sK6(X0)),X0,X0)
        & m1_subset_1(sK6(X0),u1_struct_0(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f30,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( k1_waybel_2(X0,X2) = X1
              | ~ r3_waybel_9(X0,X2,X1)
              | ~ v10_waybel_0(X2,X0)
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
    inference(flattening,[],[f29])).

fof(f29,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( k1_waybel_2(X0,X2) = X1
              | ~ r3_waybel_9(X0,X2,X1)
              | ~ v10_waybel_0(X2,X0)
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
    inference(ennf_transformation,[],[f10])).

fof(f10,axiom,(
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
                  & v10_waybel_0(X2,X0)
                  & ! [X3] :
                      ( m1_subset_1(X3,u1_struct_0(X0))
                     => v5_pre_topc(k4_waybel_1(X0,X3),X0,X0) ) )
               => k1_waybel_2(X0,X2) = X1 ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t35_waybel_9)).

fof(f207,plain,
    ( ~ m1_subset_1(sK6(sK0),u1_struct_0(sK0))
    | spl9_20 ),
    inference(avatar_component_clause,[],[f206])).

fof(f208,plain,
    ( ~ spl9_20
    | spl9_18 ),
    inference(avatar_split_clause,[],[f204,f188,f206])).

fof(f188,plain,
    ( spl9_18
  <=> v5_pre_topc(k4_waybel_1(sK0,sK6(sK0)),sK0,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_18])])).

fof(f204,plain,
    ( ~ m1_subset_1(sK6(sK0),u1_struct_0(sK0))
    | spl9_18 ),
    inference(resolution,[],[f189,f67])).

fof(f189,plain,
    ( ~ v5_pre_topc(k4_waybel_1(sK0,sK6(sK0)),sK0,sK0)
    | spl9_18 ),
    inference(avatar_component_clause,[],[f188])).

fof(f203,plain,
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
    inference(avatar_split_clause,[],[f186,f183,f120,f172,f168,f164,f160,f156,f152,f148,f144,f140,f192,f124,f188])).

fof(f183,plain,
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
        | k1_waybel_2(X0,sK1) = X1
        | ~ l1_waybel_0(sK1,X0)
        | ~ v5_pre_topc(k4_waybel_1(X0,sK6(X0)),X0,X0)
        | ~ v10_waybel_0(sK1,X0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_17])])).

fof(f186,plain,
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
        | k1_waybel_2(sK0,sK1) = X0
        | ~ l1_waybel_0(sK1,sK0)
        | ~ v5_pre_topc(k4_waybel_1(sK0,sK6(sK0)),sK0,sK0)
        | ~ r3_waybel_9(sK0,sK1,X0) )
    | ~ spl9_3
    | ~ spl9_17 ),
    inference(resolution,[],[f184,f121])).

fof(f184,plain,
    ( ! [X0,X1] :
        ( ~ v10_waybel_0(sK1,X0)
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
        | k1_waybel_2(X0,sK1) = X1
        | ~ l1_waybel_0(sK1,X0)
        | ~ v5_pre_topc(k4_waybel_1(X0,sK6(X0)),X0,X0)
        | ~ r3_waybel_9(X0,sK1,X1) )
    | ~ spl9_17 ),
    inference(avatar_component_clause,[],[f183])).

fof(f185,plain,
    ( spl9_7
    | ~ spl9_6
    | spl9_17
    | ~ spl9_5 ),
    inference(avatar_split_clause,[],[f179,f128,f183,f132,f136])).

fof(f179,plain,
    ( ! [X0,X1] :
        ( ~ r3_waybel_9(X0,sK1,X1)
        | ~ v10_waybel_0(sK1,X0)
        | ~ v5_pre_topc(k4_waybel_1(X0,sK6(X0)),X0,X0)
        | ~ l1_waybel_0(sK1,X0)
        | k1_waybel_2(X0,sK1) = X1
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
    inference(resolution,[],[f95,f129])).

fof(f95,plain,(
    ! [X2,X0,X1] :
      ( ~ v7_waybel_0(X2)
      | ~ r3_waybel_9(X0,X2,X1)
      | ~ v10_waybel_0(X2,X0)
      | ~ v5_pre_topc(k4_waybel_1(X0,sK6(X0)),X0,X0)
      | ~ l1_waybel_0(X2,X0)
      | k1_waybel_2(X0,X2) = X1
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
    inference(cnf_transformation,[],[f51])).

fof(f174,plain,(
    spl9_16 ),
    inference(avatar_split_clause,[],[f58,f172])).

fof(f58,plain,(
    v2_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f40])).

fof(f170,plain,(
    spl9_15 ),
    inference(avatar_split_clause,[],[f59,f168])).

fof(f59,plain,(
    v8_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f40])).

fof(f166,plain,(
    spl9_14 ),
    inference(avatar_split_clause,[],[f60,f164])).

fof(f60,plain,(
    v3_orders_2(sK0) ),
    inference(cnf_transformation,[],[f40])).

fof(f162,plain,(
    spl9_13 ),
    inference(avatar_split_clause,[],[f61,f160])).

fof(f61,plain,(
    v4_orders_2(sK0) ),
    inference(cnf_transformation,[],[f40])).

fof(f158,plain,(
    spl9_12 ),
    inference(avatar_split_clause,[],[f62,f156])).

fof(f62,plain,(
    v5_orders_2(sK0) ),
    inference(cnf_transformation,[],[f40])).

fof(f154,plain,(
    spl9_11 ),
    inference(avatar_split_clause,[],[f63,f152])).

fof(f63,plain,(
    v1_lattice3(sK0) ),
    inference(cnf_transformation,[],[f40])).

fof(f150,plain,(
    spl9_10 ),
    inference(avatar_split_clause,[],[f64,f148])).

fof(f64,plain,(
    v2_lattice3(sK0) ),
    inference(cnf_transformation,[],[f40])).

fof(f146,plain,(
    spl9_9 ),
    inference(avatar_split_clause,[],[f65,f144])).

fof(f65,plain,(
    v1_compts_1(sK0) ),
    inference(cnf_transformation,[],[f40])).

fof(f142,plain,(
    spl9_8 ),
    inference(avatar_split_clause,[],[f66,f140])).

fof(f66,plain,(
    l1_waybel_9(sK0) ),
    inference(cnf_transformation,[],[f40])).

fof(f138,plain,(
    ~ spl9_7 ),
    inference(avatar_split_clause,[],[f68,f136])).

fof(f68,plain,(
    ~ v2_struct_0(sK1) ),
    inference(cnf_transformation,[],[f40])).

fof(f134,plain,(
    spl9_6 ),
    inference(avatar_split_clause,[],[f69,f132])).

fof(f69,plain,(
    v4_orders_2(sK1) ),
    inference(cnf_transformation,[],[f40])).

fof(f130,plain,(
    spl9_5 ),
    inference(avatar_split_clause,[],[f70,f128])).

fof(f70,plain,(
    v7_waybel_0(sK1) ),
    inference(cnf_transformation,[],[f40])).

fof(f126,plain,(
    spl9_4 ),
    inference(avatar_split_clause,[],[f71,f124])).

fof(f71,plain,(
    l1_waybel_0(sK1,sK0) ),
    inference(cnf_transformation,[],[f40])).

fof(f122,plain,(
    spl9_3 ),
    inference(avatar_split_clause,[],[f72,f120])).

fof(f72,plain,(
    v10_waybel_0(sK1,sK0) ),
    inference(cnf_transformation,[],[f40])).

fof(f118,plain,
    ( ~ spl9_1
    | ~ spl9_2 ),
    inference(avatar_split_clause,[],[f73,f116,f113])).

fof(f73,plain,
    ( ~ r2_hidden(k1_waybel_2(sK0,sK1),k10_yellow_6(sK0,sK1))
    | ~ r1_waybel_9(sK0,sK1) ),
    inference(cnf_transformation,[],[f40])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : run_vampire %s %d
% 0.14/0.35  % Computer   : n008.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % WCLimit    : 600
% 0.14/0.35  % DateTime   : Tue Dec  1 15:12:30 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.22/0.47  % (3876)dis+1011_3_awrs=decay:awrsf=32:afp=10000:afq=1.1:amm=off:anc=none:cond=fast:ep=RSTC:fde=unused:lma=on:nm=16:nwc=2.5:s2a=on:sac=on:sp=frequency:urr=ec_only_2 on theBenchmark
% 0.22/0.48  % (3872)lrs+1002_8_add=large:afp=40000:afq=1.0:amm=off:anc=none:cond=on:gs=on:irw=on:nm=16:newcnf=on:nwc=1:stl=30:sos=on:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.22/0.48  % (3873)lrs+1010_2:1_aac=none:afr=on:afp=10000:afq=1.4:amm=sco:anc=none:gs=on:gsem=off:irw=on:nm=16:nwc=3:stl=30_7 on theBenchmark
% 0.22/0.48  % (3885)lrs+11_1024_afr=on:afp=40000:afq=2.0:anc=none:br=off:ep=RSTC:gs=on:nm=16:nwc=1:stl=30:sp=occurrence:urr=on_129 on theBenchmark
% 0.22/0.49  % (3872)Refutation not found, incomplete strategy% (3872)------------------------------
% 0.22/0.49  % (3872)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.49  % (3885)Refutation not found, incomplete strategy% (3885)------------------------------
% 0.22/0.49  % (3885)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.49  % (3885)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.49  
% 0.22/0.49  % (3885)Memory used [KB]: 10746
% 0.22/0.49  % (3885)Time elapsed: 0.073 s
% 0.22/0.49  % (3885)------------------------------
% 0.22/0.49  % (3885)------------------------------
% 0.22/0.49  % (3884)lrs+1_7_av=off:irw=on:lcm=predicate:lma=on:nm=4:newcnf=on:nwc=1:stl=30:sos=all:sp=occurrence:updr=off_81 on theBenchmark
% 0.22/0.49  % (3882)lrs+10_50_add=large:afp=40000:afq=1.2:amm=sco:anc=none:br=off:cond=on:fsr=off:gsp=input_only:gs=on:irw=on:lma=on:nm=64:nwc=1:stl=30:sos=all:sp=reverse_arity:urr=on_21 on theBenchmark
% 0.22/0.49  % (3884)Refutation not found, incomplete strategy% (3884)------------------------------
% 0.22/0.49  % (3884)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.49  % (3872)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.49  
% 0.22/0.49  % (3872)Memory used [KB]: 10746
% 0.22/0.49  % (3872)Time elapsed: 0.063 s
% 0.22/0.49  % (3872)------------------------------
% 0.22/0.49  % (3872)------------------------------
% 0.22/0.49  % (3881)dis+11_2:1_add=large:afp=4000:afq=1.4:amm=sco:anc=none:fsr=off:nm=16:nwc=1:sd=3:ss=axioms:st=1.2:sos=all:urr=ec_only:updr=off_2 on theBenchmark
% 0.22/0.49  % (3884)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.49  
% 0.22/0.49  % (3884)Memory used [KB]: 1663
% 0.22/0.49  % (3884)Time elapsed: 0.072 s
% 0.22/0.49  % (3884)------------------------------
% 0.22/0.49  % (3884)------------------------------
% 0.22/0.50  % (3887)ott+1002_7_acc=on:afr=on:afp=100000:afq=1.1:amm=off:anc=none:bs=unit_only:gsp=input_only:gs=on:nm=2:nwc=10:sos=theory:sp=reverse_arity:urr=on:updr=off_45 on theBenchmark
% 0.22/0.50  % (3878)lrs+1011_5_afr=on:afp=100000:afq=1.0:amm=off:anc=none:cond=on:lma=on:nm=6:nwc=1:sas=z3:stl=30:sac=on:urr=on_12 on theBenchmark
% 0.22/0.50  % (3889)lrs+1002_16_av=off:cond=on:nwc=3:stl=30_83 on theBenchmark
% 0.22/0.50  % (3879)lrs+10_4_add=off:afp=100000:afq=2.0:anc=none:bd=off:er=known:gs=on:gsem=off:irw=on:lcm=reverse:nm=4:newcnf=on:nwc=2.5:sas=z3:stl=30:sac=on:urr=ec_only:updr=off_3 on theBenchmark
% 0.22/0.50  % (3891)dis+1010_10_afr=on:afp=100000:afq=2.0:amm=sco:anc=none:ep=RS:fde=unused:gs=on:nwc=1:sos=on:sac=on:sp=occurrence_3 on theBenchmark
% 0.22/0.50  % (3888)ott+1_8:1_av=off:bd=preordered:bsr=on:lma=on:nm=64:newcnf=on:nwc=1.2:uhcvi=on_180 on theBenchmark
% 0.22/0.50  % (3875)lrs+1011_3:1_av=off:cond=on:irw=on:lma=on:nm=16:nwc=1:stl=30:sos=all:updr=off_11 on theBenchmark
% 0.22/0.50  % (3877)lrs+1011_10_aac=none:acc=model:add=large:afp=40000:afq=2.0:anc=none:bd=off:bsr=on:fsr=off:gs=on:gsem=off:irw=on:lcm=reverse:lwlo=on:nm=64:nwc=3:nicw=on:stl=30_38 on theBenchmark
% 0.22/0.50  % (3891)Refutation not found, incomplete strategy% (3891)------------------------------
% 0.22/0.50  % (3891)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.50  % (3891)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.50  
% 0.22/0.50  % (3891)Memory used [KB]: 10618
% 0.22/0.50  % (3891)Time elapsed: 0.087 s
% 0.22/0.50  % (3891)------------------------------
% 0.22/0.50  % (3891)------------------------------
% 0.22/0.51  % (3871)lrs+1_1_aac=none:acc=model:add=large:afp=100000:afq=1.2:anc=none:bd=off:bs=on:bsr=on:ccuc=first:cond=on:fde=unused:irw=on:nm=2:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:uhcvi=on_2 on theBenchmark
% 0.22/0.51  % (3886)lrs+4_2_av=off:gs=on:gsem=on:lma=on:nm=16:nwc=1:sas=z3:stl=30:sos=on:urr=on_159 on theBenchmark
% 0.22/0.51  % (3882)Refutation not found, incomplete strategy% (3882)------------------------------
% 0.22/0.51  % (3882)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.51  % (3882)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.51  
% 0.22/0.51  % (3882)Memory used [KB]: 10746
% 0.22/0.51  % (3882)Time elapsed: 0.078 s
% 0.22/0.51  % (3882)------------------------------
% 0.22/0.51  % (3882)------------------------------
% 0.22/0.51  % (3874)dis+1011_5:4_acc=model:afr=on:afp=10000:afq=1.4:amm=off:anc=none:bd=off:ccuc=small_ones:cond=fast:fde=unused:gs=on:nm=2:newcnf=on:nwc=1:nicw=on:sos=on:sac=on:sp=occurrence:updr=off_9 on theBenchmark
% 0.22/0.51  % (3880)lrs+1011_3:2_aac=none:afp=10000:afq=1.2:amm=off:anc=all:cond=on:fde=none:gs=on:gsem=on:irw=on:lma=on:nm=32:newcnf=on:nwc=3:nicw=on:stl=30:sac=on:sp=reverse_arity:urr=ec_only:updr=off:uhcvi=on_5 on theBenchmark
% 0.22/0.52  % (3890)dis+11_3_add=off:afr=on:afp=40000:afq=2.0:amm=sco:anc=none:cond=on:nm=16:nwc=1:ss=axioms:st=5.0:sos=all:sp=reverse_arity_169 on theBenchmark
% 0.22/0.52  % (3883)lrs+1011_3:1_add=off:afr=on:afp=10000:afq=1.1:amm=off:bce=on:cond=on:ep=R:fsr=off:nm=16:nwc=1:stl=30:sos=all:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.22/0.53  % (3877)Refutation found. Thanks to Tanya!
% 0.22/0.53  % SZS status Theorem for theBenchmark
% 0.22/0.53  % SZS output start Proof for theBenchmark
% 0.22/0.53  fof(f446,plain,(
% 0.22/0.53    $false),
% 0.22/0.53    inference(avatar_sat_refutation,[],[f118,f122,f126,f130,f134,f138,f142,f146,f150,f154,f158,f162,f166,f170,f174,f185,f203,f208,f213,f216,f230,f232,f234,f240,f244,f250,f258,f263,f268,f270,f279,f281,f291,f293,f316,f321,f326,f337,f368,f381,f389,f390,f391,f397,f401,f414,f427,f432,f436,f437,f445])).
% 0.22/0.53  fof(f445,plain,(
% 0.22/0.53    spl9_22 | ~spl9_16 | ~spl9_15 | ~spl9_9 | ~spl9_23 | spl9_7 | ~spl9_6 | ~spl9_5 | ~spl9_4 | spl9_59 | ~spl9_55 | ~spl9_58),
% 0.22/0.53    inference(avatar_split_clause,[],[f444,f425,f412,f430,f124,f128,f132,f136,f222,f144,f168,f172,f219])).
% 0.22/0.53  fof(f219,plain,(
% 0.22/0.53    spl9_22 <=> v2_struct_0(sK0)),
% 0.22/0.53    introduced(avatar_definition,[new_symbols(naming,[spl9_22])])).
% 0.22/0.53  fof(f172,plain,(
% 0.22/0.53    spl9_16 <=> v2_pre_topc(sK0)),
% 0.22/0.53    introduced(avatar_definition,[new_symbols(naming,[spl9_16])])).
% 0.22/0.53  fof(f168,plain,(
% 0.22/0.53    spl9_15 <=> v8_pre_topc(sK0)),
% 0.22/0.53    introduced(avatar_definition,[new_symbols(naming,[spl9_15])])).
% 0.22/0.53  fof(f144,plain,(
% 0.22/0.53    spl9_9 <=> v1_compts_1(sK0)),
% 0.22/0.53    introduced(avatar_definition,[new_symbols(naming,[spl9_9])])).
% 0.22/0.53  fof(f222,plain,(
% 0.22/0.53    spl9_23 <=> l1_pre_topc(sK0)),
% 0.22/0.53    introduced(avatar_definition,[new_symbols(naming,[spl9_23])])).
% 0.22/0.53  fof(f136,plain,(
% 0.22/0.53    spl9_7 <=> v2_struct_0(sK1)),
% 0.22/0.53    introduced(avatar_definition,[new_symbols(naming,[spl9_7])])).
% 0.22/0.53  fof(f132,plain,(
% 0.22/0.53    spl9_6 <=> v4_orders_2(sK1)),
% 0.22/0.53    introduced(avatar_definition,[new_symbols(naming,[spl9_6])])).
% 0.22/0.53  fof(f128,plain,(
% 0.22/0.53    spl9_5 <=> v7_waybel_0(sK1)),
% 0.22/0.53    introduced(avatar_definition,[new_symbols(naming,[spl9_5])])).
% 0.22/0.53  fof(f124,plain,(
% 0.22/0.53    spl9_4 <=> l1_waybel_0(sK1,sK0)),
% 0.22/0.53    introduced(avatar_definition,[new_symbols(naming,[spl9_4])])).
% 0.22/0.53  fof(f430,plain,(
% 0.22/0.53    spl9_59 <=> ! [X0] : (~r3_waybel_9(sK0,sK1,X0) | r2_hidden(X0,k10_yellow_6(sK0,sK1)) | ~m1_subset_1(X0,u1_struct_0(sK0)))),
% 0.22/0.53    introduced(avatar_definition,[new_symbols(naming,[spl9_59])])).
% 0.22/0.53  fof(f412,plain,(
% 0.22/0.53    spl9_55 <=> k1_waybel_2(sK0,sK1) = sK3(sK0,sK1)),
% 0.22/0.53    introduced(avatar_definition,[new_symbols(naming,[spl9_55])])).
% 0.22/0.53  fof(f425,plain,(
% 0.22/0.53    spl9_58 <=> k1_waybel_2(sK0,sK1) = sK2(sK0,sK1)),
% 0.22/0.53    introduced(avatar_definition,[new_symbols(naming,[spl9_58])])).
% 0.22/0.53  fof(f444,plain,(
% 0.22/0.53    ( ! [X0] : (~r3_waybel_9(sK0,sK1,X0) | ~m1_subset_1(X0,u1_struct_0(sK0)) | r2_hidden(X0,k10_yellow_6(sK0,sK1)) | ~l1_waybel_0(sK1,sK0) | ~v7_waybel_0(sK1) | ~v4_orders_2(sK1) | v2_struct_0(sK1) | ~l1_pre_topc(sK0) | ~v1_compts_1(sK0) | ~v8_pre_topc(sK0) | ~v2_pre_topc(sK0) | v2_struct_0(sK0)) ) | (~spl9_55 | ~spl9_58)),
% 0.22/0.53    inference(trivial_inequality_removal,[],[f443])).
% 0.22/0.53  fof(f443,plain,(
% 0.22/0.53    ( ! [X0] : (k1_waybel_2(sK0,sK1) != k1_waybel_2(sK0,sK1) | ~r3_waybel_9(sK0,sK1,X0) | ~m1_subset_1(X0,u1_struct_0(sK0)) | r2_hidden(X0,k10_yellow_6(sK0,sK1)) | ~l1_waybel_0(sK1,sK0) | ~v7_waybel_0(sK1) | ~v4_orders_2(sK1) | v2_struct_0(sK1) | ~l1_pre_topc(sK0) | ~v1_compts_1(sK0) | ~v8_pre_topc(sK0) | ~v2_pre_topc(sK0) | v2_struct_0(sK0)) ) | (~spl9_55 | ~spl9_58)),
% 0.22/0.53    inference(forward_demodulation,[],[f441,f426])).
% 0.22/0.53  fof(f426,plain,(
% 0.22/0.53    k1_waybel_2(sK0,sK1) = sK2(sK0,sK1) | ~spl9_58),
% 0.22/0.53    inference(avatar_component_clause,[],[f425])).
% 0.22/0.53  fof(f441,plain,(
% 0.22/0.53    ( ! [X0] : (k1_waybel_2(sK0,sK1) != sK2(sK0,sK1) | ~r3_waybel_9(sK0,sK1,X0) | ~m1_subset_1(X0,u1_struct_0(sK0)) | r2_hidden(X0,k10_yellow_6(sK0,sK1)) | ~l1_waybel_0(sK1,sK0) | ~v7_waybel_0(sK1) | ~v4_orders_2(sK1) | v2_struct_0(sK1) | ~l1_pre_topc(sK0) | ~v1_compts_1(sK0) | ~v8_pre_topc(sK0) | ~v2_pre_topc(sK0) | v2_struct_0(sK0)) ) | ~spl9_55),
% 0.22/0.53    inference(superposition,[],[f83,f413])).
% 0.22/0.53  fof(f413,plain,(
% 0.22/0.53    k1_waybel_2(sK0,sK1) = sK3(sK0,sK1) | ~spl9_55),
% 0.22/0.53    inference(avatar_component_clause,[],[f412])).
% 0.22/0.53  fof(f83,plain,(
% 0.22/0.53    ( ! [X2,X0,X1] : (sK2(X0,X1) != sK3(X0,X1) | ~r3_waybel_9(X0,X1,X2) | ~m1_subset_1(X2,u1_struct_0(X0)) | r2_hidden(X2,k10_yellow_6(X0,X1)) | ~l1_waybel_0(X1,X0) | ~v7_waybel_0(X1) | ~v4_orders_2(X1) | v2_struct_0(X1) | ~l1_pre_topc(X0) | ~v1_compts_1(X0) | ~v8_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 0.22/0.53    inference(cnf_transformation,[],[f45])).
% 0.22/0.53  fof(f45,plain,(
% 0.22/0.53    ! [X0] : (! [X1] : (! [X2] : (r2_hidden(X2,k10_yellow_6(X0,X1)) | ~r3_waybel_9(X0,X1,X2) | ~m1_subset_1(X2,u1_struct_0(X0))) | ((sK2(X0,X1) != sK3(X0,X1) & r3_waybel_9(X0,X1,sK3(X0,X1)) & r3_waybel_9(X0,X1,sK2(X0,X1)) & m1_subset_1(sK3(X0,X1),u1_struct_0(X0))) & m1_subset_1(sK2(X0,X1),u1_struct_0(X0))) | ~l1_waybel_0(X1,X0) | ~v7_waybel_0(X1) | ~v4_orders_2(X1) | v2_struct_0(X1)) | ~l1_pre_topc(X0) | ~v1_compts_1(X0) | ~v8_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 0.22/0.53    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2,sK3])],[f42,f44,f43])).
% 0.22/0.53  fof(f43,plain,(
% 0.22/0.53    ! [X1,X0] : (? [X3] : (? [X4] : (X3 != X4 & r3_waybel_9(X0,X1,X4) & r3_waybel_9(X0,X1,X3) & m1_subset_1(X4,u1_struct_0(X0))) & m1_subset_1(X3,u1_struct_0(X0))) => (? [X4] : (sK2(X0,X1) != X4 & r3_waybel_9(X0,X1,X4) & r3_waybel_9(X0,X1,sK2(X0,X1)) & m1_subset_1(X4,u1_struct_0(X0))) & m1_subset_1(sK2(X0,X1),u1_struct_0(X0))))),
% 0.22/0.53    introduced(choice_axiom,[])).
% 0.22/0.53  fof(f44,plain,(
% 0.22/0.53    ! [X1,X0] : (? [X4] : (sK2(X0,X1) != X4 & r3_waybel_9(X0,X1,X4) & r3_waybel_9(X0,X1,sK2(X0,X1)) & m1_subset_1(X4,u1_struct_0(X0))) => (sK2(X0,X1) != sK3(X0,X1) & r3_waybel_9(X0,X1,sK3(X0,X1)) & r3_waybel_9(X0,X1,sK2(X0,X1)) & m1_subset_1(sK3(X0,X1),u1_struct_0(X0))))),
% 0.22/0.53    introduced(choice_axiom,[])).
% 0.22/0.53  fof(f42,plain,(
% 0.22/0.53    ! [X0] : (! [X1] : (! [X2] : (r2_hidden(X2,k10_yellow_6(X0,X1)) | ~r3_waybel_9(X0,X1,X2) | ~m1_subset_1(X2,u1_struct_0(X0))) | ? [X3] : (? [X4] : (X3 != X4 & r3_waybel_9(X0,X1,X4) & r3_waybel_9(X0,X1,X3) & m1_subset_1(X4,u1_struct_0(X0))) & m1_subset_1(X3,u1_struct_0(X0))) | ~l1_waybel_0(X1,X0) | ~v7_waybel_0(X1) | ~v4_orders_2(X1) | v2_struct_0(X1)) | ~l1_pre_topc(X0) | ~v1_compts_1(X0) | ~v8_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 0.22/0.53    inference(rectify,[],[f24])).
% 0.22/0.53  fof(f24,plain,(
% 0.22/0.53    ! [X0] : (! [X1] : (! [X4] : (r2_hidden(X4,k10_yellow_6(X0,X1)) | ~r3_waybel_9(X0,X1,X4) | ~m1_subset_1(X4,u1_struct_0(X0))) | ? [X2] : (? [X3] : (X2 != X3 & r3_waybel_9(X0,X1,X3) & r3_waybel_9(X0,X1,X2) & m1_subset_1(X3,u1_struct_0(X0))) & m1_subset_1(X2,u1_struct_0(X0))) | ~l1_waybel_0(X1,X0) | ~v7_waybel_0(X1) | ~v4_orders_2(X1) | v2_struct_0(X1)) | ~l1_pre_topc(X0) | ~v1_compts_1(X0) | ~v8_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 0.22/0.53    inference(flattening,[],[f23])).
% 0.22/0.53  fof(f23,plain,(
% 0.22/0.53    ! [X0] : (! [X1] : ((! [X4] : ((r2_hidden(X4,k10_yellow_6(X0,X1)) | ~r3_waybel_9(X0,X1,X4)) | ~m1_subset_1(X4,u1_struct_0(X0))) | ? [X2] : (? [X3] : ((X2 != X3 & (r3_waybel_9(X0,X1,X3) & r3_waybel_9(X0,X1,X2))) & m1_subset_1(X3,u1_struct_0(X0))) & m1_subset_1(X2,u1_struct_0(X0)))) | (~l1_waybel_0(X1,X0) | ~v7_waybel_0(X1) | ~v4_orders_2(X1) | v2_struct_0(X1))) | (~l1_pre_topc(X0) | ~v1_compts_1(X0) | ~v8_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 0.22/0.53    inference(ennf_transformation,[],[f14])).
% 0.22/0.53  fof(f14,plain,(
% 0.22/0.53    ! [X0] : ((l1_pre_topc(X0) & v1_compts_1(X0) & v8_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((l1_waybel_0(X1,X0) & v7_waybel_0(X1) & v4_orders_2(X1) & ~v2_struct_0(X1)) => (! [X2] : (m1_subset_1(X2,u1_struct_0(X0)) => ! [X3] : (m1_subset_1(X3,u1_struct_0(X0)) => ((r3_waybel_9(X0,X1,X3) & r3_waybel_9(X0,X1,X2)) => X2 = X3))) => ! [X4] : (m1_subset_1(X4,u1_struct_0(X0)) => (r3_waybel_9(X0,X1,X4) => r2_hidden(X4,k10_yellow_6(X0,X1)))))))),
% 0.22/0.53    inference(rectify,[],[f9])).
% 0.22/0.53  fof(f9,axiom,(
% 0.22/0.53    ! [X0] : ((l1_pre_topc(X0) & v1_compts_1(X0) & v8_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((l1_waybel_0(X1,X0) & v7_waybel_0(X1) & v4_orders_2(X1) & ~v2_struct_0(X1)) => (! [X2] : (m1_subset_1(X2,u1_struct_0(X0)) => ! [X3] : (m1_subset_1(X3,u1_struct_0(X0)) => ((r3_waybel_9(X0,X1,X3) & r3_waybel_9(X0,X1,X2)) => X2 = X3))) => ! [X2] : (m1_subset_1(X2,u1_struct_0(X0)) => (r3_waybel_9(X0,X1,X2) => r2_hidden(X2,k10_yellow_6(X0,X1)))))))),
% 0.22/0.53    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t33_waybel_9)).
% 0.22/0.53  fof(f437,plain,(
% 0.22/0.53    spl9_22 | ~spl9_16 | ~spl9_15 | ~spl9_9 | ~spl9_23 | spl9_7 | ~spl9_6 | ~spl9_5 | ~spl9_4 | spl9_59 | spl9_56),
% 0.22/0.53    inference(avatar_split_clause,[],[f433,f418,f430,f124,f128,f132,f136,f222,f144,f168,f172,f219])).
% 0.22/0.53  fof(f418,plain,(
% 0.22/0.53    spl9_56 <=> m1_subset_1(sK2(sK0,sK1),u1_struct_0(sK0))),
% 0.22/0.53    introduced(avatar_definition,[new_symbols(naming,[spl9_56])])).
% 0.22/0.53  fof(f433,plain,(
% 0.22/0.53    ( ! [X0] : (~r3_waybel_9(sK0,sK1,X0) | ~m1_subset_1(X0,u1_struct_0(sK0)) | r2_hidden(X0,k10_yellow_6(sK0,sK1)) | ~l1_waybel_0(sK1,sK0) | ~v7_waybel_0(sK1) | ~v4_orders_2(sK1) | v2_struct_0(sK1) | ~l1_pre_topc(sK0) | ~v1_compts_1(sK0) | ~v8_pre_topc(sK0) | ~v2_pre_topc(sK0) | v2_struct_0(sK0)) ) | spl9_56),
% 0.22/0.53    inference(resolution,[],[f419,f79])).
% 0.22/0.53  fof(f79,plain,(
% 0.22/0.53    ( ! [X2,X0,X1] : (m1_subset_1(sK2(X0,X1),u1_struct_0(X0)) | ~r3_waybel_9(X0,X1,X2) | ~m1_subset_1(X2,u1_struct_0(X0)) | r2_hidden(X2,k10_yellow_6(X0,X1)) | ~l1_waybel_0(X1,X0) | ~v7_waybel_0(X1) | ~v4_orders_2(X1) | v2_struct_0(X1) | ~l1_pre_topc(X0) | ~v1_compts_1(X0) | ~v8_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 0.22/0.53    inference(cnf_transformation,[],[f45])).
% 0.22/0.53  fof(f419,plain,(
% 0.22/0.53    ~m1_subset_1(sK2(sK0,sK1),u1_struct_0(sK0)) | spl9_56),
% 0.22/0.53    inference(avatar_component_clause,[],[f418])).
% 0.22/0.53  fof(f436,plain,(
% 0.22/0.53    ~spl9_27 | ~spl9_26 | spl9_2 | ~spl9_59),
% 0.22/0.53    inference(avatar_split_clause,[],[f435,f430,f116,f238,f242])).
% 0.22/0.53  fof(f242,plain,(
% 0.22/0.53    spl9_27 <=> m1_subset_1(k1_waybel_2(sK0,sK1),u1_struct_0(sK0))),
% 0.22/0.53    introduced(avatar_definition,[new_symbols(naming,[spl9_27])])).
% 0.22/0.53  fof(f238,plain,(
% 0.22/0.53    spl9_26 <=> r3_waybel_9(sK0,sK1,k1_waybel_2(sK0,sK1))),
% 0.22/0.53    introduced(avatar_definition,[new_symbols(naming,[spl9_26])])).
% 0.22/0.53  fof(f116,plain,(
% 0.22/0.53    spl9_2 <=> r2_hidden(k1_waybel_2(sK0,sK1),k10_yellow_6(sK0,sK1))),
% 0.22/0.53    introduced(avatar_definition,[new_symbols(naming,[spl9_2])])).
% 0.22/0.53  fof(f435,plain,(
% 0.22/0.53    ~r3_waybel_9(sK0,sK1,k1_waybel_2(sK0,sK1)) | ~m1_subset_1(k1_waybel_2(sK0,sK1),u1_struct_0(sK0)) | (spl9_2 | ~spl9_59)),
% 0.22/0.53    inference(resolution,[],[f431,f117])).
% 0.22/0.53  fof(f117,plain,(
% 0.22/0.53    ~r2_hidden(k1_waybel_2(sK0,sK1),k10_yellow_6(sK0,sK1)) | spl9_2),
% 0.22/0.53    inference(avatar_component_clause,[],[f116])).
% 0.22/0.53  fof(f431,plain,(
% 0.22/0.53    ( ! [X0] : (r2_hidden(X0,k10_yellow_6(sK0,sK1)) | ~r3_waybel_9(sK0,sK1,X0) | ~m1_subset_1(X0,u1_struct_0(sK0))) ) | ~spl9_59),
% 0.22/0.53    inference(avatar_component_clause,[],[f430])).
% 0.22/0.53  fof(f432,plain,(
% 0.22/0.53    spl9_22 | ~spl9_16 | ~spl9_15 | ~spl9_9 | ~spl9_23 | spl9_7 | ~spl9_6 | ~spl9_5 | ~spl9_4 | spl9_59 | spl9_53),
% 0.22/0.53    inference(avatar_split_clause,[],[f428,f405,f430,f124,f128,f132,f136,f222,f144,f168,f172,f219])).
% 0.22/0.53  fof(f405,plain,(
% 0.22/0.53    spl9_53 <=> m1_subset_1(sK3(sK0,sK1),u1_struct_0(sK0))),
% 0.22/0.53    introduced(avatar_definition,[new_symbols(naming,[spl9_53])])).
% 0.22/0.53  fof(f428,plain,(
% 0.22/0.53    ( ! [X0] : (~r3_waybel_9(sK0,sK1,X0) | ~m1_subset_1(X0,u1_struct_0(sK0)) | r2_hidden(X0,k10_yellow_6(sK0,sK1)) | ~l1_waybel_0(sK1,sK0) | ~v7_waybel_0(sK1) | ~v4_orders_2(sK1) | v2_struct_0(sK1) | ~l1_pre_topc(sK0) | ~v1_compts_1(sK0) | ~v8_pre_topc(sK0) | ~v2_pre_topc(sK0) | v2_struct_0(sK0)) ) | spl9_53),
% 0.22/0.53    inference(resolution,[],[f406,f80])).
% 0.22/0.53  fof(f80,plain,(
% 0.22/0.53    ( ! [X2,X0,X1] : (m1_subset_1(sK3(X0,X1),u1_struct_0(X0)) | ~r3_waybel_9(X0,X1,X2) | ~m1_subset_1(X2,u1_struct_0(X0)) | r2_hidden(X2,k10_yellow_6(X0,X1)) | ~l1_waybel_0(X1,X0) | ~v7_waybel_0(X1) | ~v4_orders_2(X1) | v2_struct_0(X1) | ~l1_pre_topc(X0) | ~v1_compts_1(X0) | ~v8_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 0.22/0.53    inference(cnf_transformation,[],[f45])).
% 0.22/0.53  fof(f406,plain,(
% 0.22/0.53    ~m1_subset_1(sK3(sK0,sK1),u1_struct_0(sK0)) | spl9_53),
% 0.22/0.53    inference(avatar_component_clause,[],[f405])).
% 0.22/0.53  fof(f427,plain,(
% 0.22/0.53    spl9_58 | ~spl9_56 | ~spl9_19 | ~spl9_52),
% 0.22/0.53    inference(avatar_split_clause,[],[f416,f399,f192,f418,f425])).
% 0.22/0.53  fof(f192,plain,(
% 0.22/0.53    spl9_19 <=> ! [X0] : (~m1_subset_1(X0,u1_struct_0(sK0)) | ~r3_waybel_9(sK0,sK1,X0) | k1_waybel_2(sK0,sK1) = X0)),
% 0.22/0.53    introduced(avatar_definition,[new_symbols(naming,[spl9_19])])).
% 0.22/0.53  fof(f399,plain,(
% 0.22/0.53    spl9_52 <=> r3_waybel_9(sK0,sK1,sK2(sK0,sK1))),
% 0.22/0.53    introduced(avatar_definition,[new_symbols(naming,[spl9_52])])).
% 0.22/0.53  fof(f416,plain,(
% 0.22/0.53    ~m1_subset_1(sK2(sK0,sK1),u1_struct_0(sK0)) | k1_waybel_2(sK0,sK1) = sK2(sK0,sK1) | (~spl9_19 | ~spl9_52)),
% 0.22/0.53    inference(resolution,[],[f400,f193])).
% 0.22/0.53  fof(f193,plain,(
% 0.22/0.53    ( ! [X0] : (~r3_waybel_9(sK0,sK1,X0) | ~m1_subset_1(X0,u1_struct_0(sK0)) | k1_waybel_2(sK0,sK1) = X0) ) | ~spl9_19),
% 0.22/0.53    inference(avatar_component_clause,[],[f192])).
% 0.22/0.53  fof(f400,plain,(
% 0.22/0.53    r3_waybel_9(sK0,sK1,sK2(sK0,sK1)) | ~spl9_52),
% 0.22/0.53    inference(avatar_component_clause,[],[f399])).
% 0.22/0.53  fof(f414,plain,(
% 0.22/0.53    spl9_55 | ~spl9_53 | ~spl9_19 | ~spl9_51),
% 0.22/0.53    inference(avatar_split_clause,[],[f403,f395,f192,f405,f412])).
% 0.22/0.53  fof(f395,plain,(
% 0.22/0.53    spl9_51 <=> r3_waybel_9(sK0,sK1,sK3(sK0,sK1))),
% 0.22/0.53    introduced(avatar_definition,[new_symbols(naming,[spl9_51])])).
% 0.22/0.53  fof(f403,plain,(
% 0.22/0.53    ~m1_subset_1(sK3(sK0,sK1),u1_struct_0(sK0)) | k1_waybel_2(sK0,sK1) = sK3(sK0,sK1) | (~spl9_19 | ~spl9_51)),
% 0.22/0.53    inference(resolution,[],[f396,f193])).
% 0.22/0.53  fof(f396,plain,(
% 0.22/0.53    r3_waybel_9(sK0,sK1,sK3(sK0,sK1)) | ~spl9_51),
% 0.22/0.53    inference(avatar_component_clause,[],[f395])).
% 0.22/0.53  fof(f401,plain,(
% 0.22/0.53    spl9_22 | ~spl9_16 | ~spl9_15 | ~spl9_9 | ~spl9_23 | spl9_7 | ~spl9_6 | ~spl9_5 | ~spl9_4 | spl9_52 | ~spl9_27 | ~spl9_26 | spl9_2),
% 0.22/0.53    inference(avatar_split_clause,[],[f393,f116,f238,f242,f399,f124,f128,f132,f136,f222,f144,f168,f172,f219])).
% 0.22/0.53  fof(f393,plain,(
% 0.22/0.53    ~r3_waybel_9(sK0,sK1,k1_waybel_2(sK0,sK1)) | ~m1_subset_1(k1_waybel_2(sK0,sK1),u1_struct_0(sK0)) | r3_waybel_9(sK0,sK1,sK2(sK0,sK1)) | ~l1_waybel_0(sK1,sK0) | ~v7_waybel_0(sK1) | ~v4_orders_2(sK1) | v2_struct_0(sK1) | ~l1_pre_topc(sK0) | ~v1_compts_1(sK0) | ~v8_pre_topc(sK0) | ~v2_pre_topc(sK0) | v2_struct_0(sK0) | spl9_2),
% 0.22/0.53    inference(resolution,[],[f117,f81])).
% 0.22/0.53  fof(f81,plain,(
% 0.22/0.53    ( ! [X2,X0,X1] : (r2_hidden(X2,k10_yellow_6(X0,X1)) | ~r3_waybel_9(X0,X1,X2) | ~m1_subset_1(X2,u1_struct_0(X0)) | r3_waybel_9(X0,X1,sK2(X0,X1)) | ~l1_waybel_0(X1,X0) | ~v7_waybel_0(X1) | ~v4_orders_2(X1) | v2_struct_0(X1) | ~l1_pre_topc(X0) | ~v1_compts_1(X0) | ~v8_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 0.22/0.53    inference(cnf_transformation,[],[f45])).
% 0.22/0.53  fof(f397,plain,(
% 0.22/0.53    spl9_22 | ~spl9_16 | ~spl9_15 | ~spl9_9 | ~spl9_23 | spl9_7 | ~spl9_6 | ~spl9_5 | ~spl9_4 | spl9_51 | ~spl9_27 | ~spl9_26 | spl9_2),
% 0.22/0.53    inference(avatar_split_clause,[],[f392,f116,f238,f242,f395,f124,f128,f132,f136,f222,f144,f168,f172,f219])).
% 0.22/0.53  fof(f392,plain,(
% 0.22/0.53    ~r3_waybel_9(sK0,sK1,k1_waybel_2(sK0,sK1)) | ~m1_subset_1(k1_waybel_2(sK0,sK1),u1_struct_0(sK0)) | r3_waybel_9(sK0,sK1,sK3(sK0,sK1)) | ~l1_waybel_0(sK1,sK0) | ~v7_waybel_0(sK1) | ~v4_orders_2(sK1) | v2_struct_0(sK1) | ~l1_pre_topc(sK0) | ~v1_compts_1(sK0) | ~v8_pre_topc(sK0) | ~v2_pre_topc(sK0) | v2_struct_0(sK0) | spl9_2),
% 0.22/0.53    inference(resolution,[],[f117,f82])).
% 0.22/0.53  fof(f82,plain,(
% 0.22/0.53    ( ! [X2,X0,X1] : (r2_hidden(X2,k10_yellow_6(X0,X1)) | ~r3_waybel_9(X0,X1,X2) | ~m1_subset_1(X2,u1_struct_0(X0)) | r3_waybel_9(X0,X1,sK3(X0,X1)) | ~l1_waybel_0(X1,X0) | ~v7_waybel_0(X1) | ~v4_orders_2(X1) | v2_struct_0(X1) | ~l1_pre_topc(X0) | ~v1_compts_1(X0) | ~v8_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 0.22/0.53    inference(cnf_transformation,[],[f45])).
% 0.22/0.53  fof(f391,plain,(
% 0.22/0.53    ~spl9_4 | spl9_1 | ~spl9_8 | ~spl9_39),
% 0.22/0.53    inference(avatar_split_clause,[],[f330,f311,f140,f113,f124])).
% 0.22/0.53  fof(f113,plain,(
% 0.22/0.53    spl9_1 <=> r1_waybel_9(sK0,sK1)),
% 0.22/0.53    introduced(avatar_definition,[new_symbols(naming,[spl9_1])])).
% 0.22/0.53  fof(f140,plain,(
% 0.22/0.53    spl9_8 <=> l1_waybel_9(sK0)),
% 0.22/0.53    introduced(avatar_definition,[new_symbols(naming,[spl9_8])])).
% 0.22/0.53  fof(f311,plain,(
% 0.22/0.53    spl9_39 <=> r1_yellow_0(sK0,k2_relset_1(u1_struct_0(sK1),u1_struct_0(sK0),u1_waybel_0(sK0,sK1)))),
% 0.22/0.53    introduced(avatar_definition,[new_symbols(naming,[spl9_39])])).
% 0.22/0.53  fof(f330,plain,(
% 0.22/0.53    r1_waybel_9(sK0,sK1) | ~l1_waybel_0(sK1,sK0) | (~spl9_8 | ~spl9_39)),
% 0.22/0.53    inference(resolution,[],[f312,f176])).
% 0.22/0.53  fof(f176,plain,(
% 0.22/0.53    ( ! [X0] : (~r1_yellow_0(sK0,k2_relset_1(u1_struct_0(X0),u1_struct_0(sK0),u1_waybel_0(sK0,X0))) | r1_waybel_9(sK0,X0) | ~l1_waybel_0(X0,sK0)) ) | ~spl9_8),
% 0.22/0.53    inference(resolution,[],[f175,f141])).
% 0.22/0.53  fof(f141,plain,(
% 0.22/0.53    l1_waybel_9(sK0) | ~spl9_8),
% 0.22/0.53    inference(avatar_component_clause,[],[f140])).
% 0.22/0.53  fof(f175,plain,(
% 0.22/0.53    ( ! [X0,X1] : (~l1_waybel_9(X0) | ~l1_waybel_0(X1,X0) | r1_waybel_9(X0,X1) | ~r1_yellow_0(X0,k2_relset_1(u1_struct_0(X1),u1_struct_0(X0),u1_waybel_0(X0,X1)))) )),
% 0.22/0.53    inference(resolution,[],[f78,f75])).
% 0.22/0.53  fof(f75,plain,(
% 0.22/0.53    ( ! [X0] : (l1_orders_2(X0) | ~l1_waybel_9(X0)) )),
% 0.22/0.53    inference(cnf_transformation,[],[f19])).
% 0.22/0.53  fof(f19,plain,(
% 0.22/0.53    ! [X0] : ((l1_orders_2(X0) & l1_pre_topc(X0)) | ~l1_waybel_9(X0))),
% 0.22/0.53    inference(ennf_transformation,[],[f5])).
% 0.22/0.53  fof(f5,axiom,(
% 0.22/0.53    ! [X0] : (l1_waybel_9(X0) => (l1_orders_2(X0) & l1_pre_topc(X0)))),
% 0.22/0.53    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_l1_waybel_9)).
% 0.22/0.53  fof(f78,plain,(
% 0.22/0.53    ( ! [X0,X1] : (~l1_orders_2(X0) | ~r1_yellow_0(X0,k2_relset_1(u1_struct_0(X1),u1_struct_0(X0),u1_waybel_0(X0,X1))) | ~l1_waybel_0(X1,X0) | r1_waybel_9(X0,X1)) )),
% 0.22/0.53    inference(cnf_transformation,[],[f41])).
% 0.22/0.53  fof(f41,plain,(
% 0.22/0.53    ! [X0] : (! [X1] : (((r1_waybel_9(X0,X1) | ~r1_yellow_0(X0,k2_relset_1(u1_struct_0(X1),u1_struct_0(X0),u1_waybel_0(X0,X1)))) & (r1_yellow_0(X0,k2_relset_1(u1_struct_0(X1),u1_struct_0(X0),u1_waybel_0(X0,X1))) | ~r1_waybel_9(X0,X1))) | ~l1_waybel_0(X1,X0)) | ~l1_orders_2(X0))),
% 0.22/0.53    inference(nnf_transformation,[],[f22])).
% 0.22/0.53  fof(f22,plain,(
% 0.22/0.53    ! [X0] : (! [X1] : ((r1_waybel_9(X0,X1) <=> r1_yellow_0(X0,k2_relset_1(u1_struct_0(X1),u1_struct_0(X0),u1_waybel_0(X0,X1)))) | ~l1_waybel_0(X1,X0)) | ~l1_orders_2(X0))),
% 0.22/0.53    inference(ennf_transformation,[],[f4])).
% 0.22/0.53  fof(f4,axiom,(
% 0.22/0.53    ! [X0] : (l1_orders_2(X0) => ! [X1] : (l1_waybel_0(X1,X0) => (r1_waybel_9(X0,X1) <=> r1_yellow_0(X0,k2_relset_1(u1_struct_0(X1),u1_struct_0(X0),u1_waybel_0(X0,X1))))))),
% 0.22/0.53    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_waybel_9)).
% 0.22/0.53  fof(f312,plain,(
% 0.22/0.53    r1_yellow_0(sK0,k2_relset_1(u1_struct_0(sK1),u1_struct_0(sK0),u1_waybel_0(sK0,sK1))) | ~spl9_39),
% 0.22/0.53    inference(avatar_component_clause,[],[f311])).
% 0.22/0.53  fof(f390,plain,(
% 0.22/0.53    ~spl9_16 | ~spl9_15 | ~spl9_14 | ~spl9_13 | ~spl9_12 | ~spl9_11 | ~spl9_10 | ~spl9_9 | ~spl9_8 | spl9_7 | ~spl9_6 | ~spl9_5 | ~spl9_4 | ~spl9_27 | ~spl9_36 | ~spl9_3 | ~spl9_26 | spl9_49),
% 0.22/0.53    inference(avatar_split_clause,[],[f387,f378,f238,f120,f299,f242,f124,f128,f132,f136,f140,f144,f148,f152,f156,f160,f164,f168,f172])).
% 0.22/0.53  fof(f164,plain,(
% 0.22/0.53    spl9_14 <=> v3_orders_2(sK0)),
% 0.22/0.53    introduced(avatar_definition,[new_symbols(naming,[spl9_14])])).
% 0.22/0.53  fof(f160,plain,(
% 0.22/0.53    spl9_13 <=> v4_orders_2(sK0)),
% 0.22/0.53    introduced(avatar_definition,[new_symbols(naming,[spl9_13])])).
% 0.22/0.53  fof(f156,plain,(
% 0.22/0.53    spl9_12 <=> v5_orders_2(sK0)),
% 0.22/0.53    introduced(avatar_definition,[new_symbols(naming,[spl9_12])])).
% 0.22/0.53  fof(f152,plain,(
% 0.22/0.53    spl9_11 <=> v1_lattice3(sK0)),
% 0.22/0.53    introduced(avatar_definition,[new_symbols(naming,[spl9_11])])).
% 0.22/0.53  fof(f148,plain,(
% 0.22/0.53    spl9_10 <=> v2_lattice3(sK0)),
% 0.22/0.53    introduced(avatar_definition,[new_symbols(naming,[spl9_10])])).
% 0.22/0.53  fof(f299,plain,(
% 0.22/0.53    spl9_36 <=> v5_pre_topc(k4_waybel_1(sK0,sK7(sK0)),sK0,sK0)),
% 0.22/0.53    introduced(avatar_definition,[new_symbols(naming,[spl9_36])])).
% 0.22/0.53  fof(f120,plain,(
% 0.22/0.53    spl9_3 <=> v10_waybel_0(sK1,sK0)),
% 0.22/0.53    introduced(avatar_definition,[new_symbols(naming,[spl9_3])])).
% 0.22/0.53  fof(f378,plain,(
% 0.22/0.53    spl9_49 <=> r2_lattice3(sK0,k2_relset_1(u1_struct_0(sK1),u1_struct_0(sK0),u1_waybel_0(sK0,sK1)),k1_waybel_2(sK0,sK1))),
% 0.22/0.53    introduced(avatar_definition,[new_symbols(naming,[spl9_49])])).
% 0.22/0.53  fof(f387,plain,(
% 0.22/0.53    ~r3_waybel_9(sK0,sK1,k1_waybel_2(sK0,sK1)) | ~v10_waybel_0(sK1,sK0) | ~v5_pre_topc(k4_waybel_1(sK0,sK7(sK0)),sK0,sK0) | ~m1_subset_1(k1_waybel_2(sK0,sK1),u1_struct_0(sK0)) | ~l1_waybel_0(sK1,sK0) | ~v7_waybel_0(sK1) | ~v4_orders_2(sK1) | v2_struct_0(sK1) | ~l1_waybel_9(sK0) | ~v1_compts_1(sK0) | ~v2_lattice3(sK0) | ~v1_lattice3(sK0) | ~v5_orders_2(sK0) | ~v4_orders_2(sK0) | ~v3_orders_2(sK0) | ~v8_pre_topc(sK0) | ~v2_pre_topc(sK0) | spl9_49),
% 0.22/0.53    inference(resolution,[],[f379,f111])).
% 0.22/0.53  fof(f111,plain,(
% 0.22/0.53    ( ! [X0,X3,X1] : (r2_lattice3(X0,k2_relset_1(u1_struct_0(X1),u1_struct_0(X0),u1_waybel_0(X0,X1)),X3) | ~r3_waybel_9(X0,X1,X3) | ~v10_waybel_0(X1,X0) | ~v5_pre_topc(k4_waybel_1(X0,sK7(X0)),X0,X0) | ~m1_subset_1(X3,u1_struct_0(X0)) | ~l1_waybel_0(X1,X0) | ~v7_waybel_0(X1) | ~v4_orders_2(X1) | v2_struct_0(X1) | ~l1_waybel_9(X0) | ~v1_compts_1(X0) | ~v2_lattice3(X0) | ~v1_lattice3(X0) | ~v5_orders_2(X0) | ~v4_orders_2(X0) | ~v3_orders_2(X0) | ~v8_pre_topc(X0) | ~v2_pre_topc(X0)) )),
% 0.22/0.53    inference(duplicate_literal_removal,[],[f104])).
% 0.22/0.53  fof(f104,plain,(
% 0.22/0.53    ( ! [X0,X3,X1] : (r2_lattice3(X0,k2_relset_1(u1_struct_0(X1),u1_struct_0(X0),u1_waybel_0(X0,X1)),X3) | ~r3_waybel_9(X0,X1,X3) | ~v10_waybel_0(X1,X0) | ~v5_pre_topc(k4_waybel_1(X0,sK7(X0)),X0,X0) | ~m1_subset_1(X3,u1_struct_0(X0)) | ~m1_subset_1(X3,u1_struct_0(X0)) | ~l1_waybel_0(X1,X0) | ~v7_waybel_0(X1) | ~v4_orders_2(X1) | v2_struct_0(X1) | ~l1_waybel_9(X0) | ~v1_compts_1(X0) | ~v2_lattice3(X0) | ~v1_lattice3(X0) | ~v5_orders_2(X0) | ~v4_orders_2(X0) | ~v3_orders_2(X0) | ~v8_pre_topc(X0) | ~v2_pre_topc(X0)) )),
% 0.22/0.53    inference(equality_resolution,[],[f97])).
% 0.22/0.53  fof(f97,plain,(
% 0.22/0.53    ( ! [X2,X0,X3,X1] : (r2_lattice3(X0,k2_relset_1(u1_struct_0(X1),u1_struct_0(X0),u1_waybel_0(X0,X1)),X3) | ~r3_waybel_9(X0,X1,X2) | ~v10_waybel_0(X1,X0) | ~v5_pre_topc(k4_waybel_1(X0,sK7(X0)),X0,X0) | X2 != X3 | ~m1_subset_1(X3,u1_struct_0(X0)) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~l1_waybel_0(X1,X0) | ~v7_waybel_0(X1) | ~v4_orders_2(X1) | v2_struct_0(X1) | ~l1_waybel_9(X0) | ~v1_compts_1(X0) | ~v2_lattice3(X0) | ~v1_lattice3(X0) | ~v5_orders_2(X0) | ~v4_orders_2(X0) | ~v3_orders_2(X0) | ~v8_pre_topc(X0) | ~v2_pre_topc(X0)) )),
% 0.22/0.53    inference(cnf_transformation,[],[f53])).
% 0.22/0.53  fof(f53,plain,(
% 0.22/0.53    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (r2_lattice3(X0,k2_relset_1(u1_struct_0(X1),u1_struct_0(X0),u1_waybel_0(X0,X1)),X3) | ~r3_waybel_9(X0,X1,X2) | ~v10_waybel_0(X1,X0) | (~v5_pre_topc(k4_waybel_1(X0,sK7(X0)),X0,X0) & m1_subset_1(sK7(X0),u1_struct_0(X0))) | X2 != X3 | ~m1_subset_1(X3,u1_struct_0(X0))) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~l1_waybel_0(X1,X0) | ~v7_waybel_0(X1) | ~v4_orders_2(X1) | v2_struct_0(X1)) | ~l1_waybel_9(X0) | ~v1_compts_1(X0) | ~v2_lattice3(X0) | ~v1_lattice3(X0) | ~v5_orders_2(X0) | ~v4_orders_2(X0) | ~v3_orders_2(X0) | ~v8_pre_topc(X0) | ~v2_pre_topc(X0))),
% 0.22/0.53    inference(skolemisation,[status(esa),new_symbols(skolem,[sK7])],[f32,f52])).
% 0.22/0.53  fof(f52,plain,(
% 0.22/0.53    ! [X0] : (? [X4] : (~v5_pre_topc(k4_waybel_1(X0,X4),X0,X0) & m1_subset_1(X4,u1_struct_0(X0))) => (~v5_pre_topc(k4_waybel_1(X0,sK7(X0)),X0,X0) & m1_subset_1(sK7(X0),u1_struct_0(X0))))),
% 0.22/0.53    introduced(choice_axiom,[])).
% 0.22/0.53  fof(f32,plain,(
% 0.22/0.53    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (r2_lattice3(X0,k2_relset_1(u1_struct_0(X1),u1_struct_0(X0),u1_waybel_0(X0,X1)),X3) | ~r3_waybel_9(X0,X1,X2) | ~v10_waybel_0(X1,X0) | ? [X4] : (~v5_pre_topc(k4_waybel_1(X0,X4),X0,X0) & m1_subset_1(X4,u1_struct_0(X0))) | X2 != X3 | ~m1_subset_1(X3,u1_struct_0(X0))) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~l1_waybel_0(X1,X0) | ~v7_waybel_0(X1) | ~v4_orders_2(X1) | v2_struct_0(X1)) | ~l1_waybel_9(X0) | ~v1_compts_1(X0) | ~v2_lattice3(X0) | ~v1_lattice3(X0) | ~v5_orders_2(X0) | ~v4_orders_2(X0) | ~v3_orders_2(X0) | ~v8_pre_topc(X0) | ~v2_pre_topc(X0))),
% 0.22/0.53    inference(flattening,[],[f31])).
% 0.22/0.53  fof(f31,plain,(
% 0.22/0.53    ! [X0] : (! [X1] : (! [X2] : (! [X3] : ((r2_lattice3(X0,k2_relset_1(u1_struct_0(X1),u1_struct_0(X0),u1_waybel_0(X0,X1)),X3) | (~r3_waybel_9(X0,X1,X2) | ~v10_waybel_0(X1,X0) | ? [X4] : (~v5_pre_topc(k4_waybel_1(X0,X4),X0,X0) & m1_subset_1(X4,u1_struct_0(X0))) | X2 != X3)) | ~m1_subset_1(X3,u1_struct_0(X0))) | ~m1_subset_1(X2,u1_struct_0(X0))) | (~l1_waybel_0(X1,X0) | ~v7_waybel_0(X1) | ~v4_orders_2(X1) | v2_struct_0(X1))) | (~l1_waybel_9(X0) | ~v1_compts_1(X0) | ~v2_lattice3(X0) | ~v1_lattice3(X0) | ~v5_orders_2(X0) | ~v4_orders_2(X0) | ~v3_orders_2(X0) | ~v8_pre_topc(X0) | ~v2_pre_topc(X0)))),
% 0.22/0.53    inference(ennf_transformation,[],[f6])).
% 0.22/0.53  fof(f6,axiom,(
% 0.22/0.53    ! [X0] : ((l1_waybel_9(X0) & v1_compts_1(X0) & v2_lattice3(X0) & v1_lattice3(X0) & v5_orders_2(X0) & v4_orders_2(X0) & v3_orders_2(X0) & v8_pre_topc(X0) & v2_pre_topc(X0)) => ! [X1] : ((l1_waybel_0(X1,X0) & v7_waybel_0(X1) & v4_orders_2(X1) & ~v2_struct_0(X1)) => ! [X2] : (m1_subset_1(X2,u1_struct_0(X0)) => ! [X3] : (m1_subset_1(X3,u1_struct_0(X0)) => ((r3_waybel_9(X0,X1,X2) & v10_waybel_0(X1,X0) & ! [X4] : (m1_subset_1(X4,u1_struct_0(X0)) => v5_pre_topc(k4_waybel_1(X0,X4),X0,X0)) & X2 = X3) => r2_lattice3(X0,k2_relset_1(u1_struct_0(X1),u1_struct_0(X0),u1_waybel_0(X0,X1)),X3))))))),
% 0.22/0.53    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l48_waybel_9)).
% 0.22/0.53  fof(f379,plain,(
% 0.22/0.53    ~r2_lattice3(sK0,k2_relset_1(u1_struct_0(sK1),u1_struct_0(sK0),u1_waybel_0(sK0,sK1)),k1_waybel_2(sK0,sK1)) | spl9_49),
% 0.22/0.53    inference(avatar_component_clause,[],[f378])).
% 0.22/0.53  fof(f389,plain,(
% 0.22/0.53    ~spl9_27 | ~spl9_26 | ~spl9_43 | spl9_49),
% 0.22/0.53    inference(avatar_split_clause,[],[f386,f378,f335,f238,f242])).
% 0.22/0.53  fof(f335,plain,(
% 0.22/0.53    spl9_43 <=> ! [X0] : (~m1_subset_1(X0,u1_struct_0(sK0)) | ~r3_waybel_9(sK0,sK1,X0) | r2_lattice3(sK0,k2_relset_1(u1_struct_0(sK1),u1_struct_0(sK0),u1_waybel_0(sK0,sK1)),X0))),
% 0.22/0.53    introduced(avatar_definition,[new_symbols(naming,[spl9_43])])).
% 0.22/0.53  fof(f386,plain,(
% 0.22/0.53    ~r3_waybel_9(sK0,sK1,k1_waybel_2(sK0,sK1)) | ~m1_subset_1(k1_waybel_2(sK0,sK1),u1_struct_0(sK0)) | (~spl9_43 | spl9_49)),
% 0.22/0.53    inference(resolution,[],[f379,f336])).
% 0.22/0.53  fof(f336,plain,(
% 0.22/0.53    ( ! [X0] : (r2_lattice3(sK0,k2_relset_1(u1_struct_0(sK1),u1_struct_0(sK0),u1_waybel_0(sK0,sK1)),X0) | ~r3_waybel_9(sK0,sK1,X0) | ~m1_subset_1(X0,u1_struct_0(sK0))) ) | ~spl9_43),
% 0.22/0.53    inference(avatar_component_clause,[],[f335])).
% 0.22/0.53  fof(f381,plain,(
% 0.22/0.53    ~spl9_12 | ~spl9_33 | spl9_39 | ~spl9_49 | ~spl9_27 | ~spl9_47),
% 0.22/0.53    inference(avatar_split_clause,[],[f372,f366,f242,f378,f311,f274,f156])).
% 0.22/0.53  fof(f274,plain,(
% 0.22/0.53    spl9_33 <=> l1_orders_2(sK0)),
% 0.22/0.53    introduced(avatar_definition,[new_symbols(naming,[spl9_33])])).
% 0.22/0.53  fof(f366,plain,(
% 0.22/0.53    spl9_47 <=> ! [X1] : (~m1_subset_1(X1,u1_struct_0(sK0)) | r1_orders_2(sK0,k1_waybel_2(sK0,sK1),sK5(sK0,X1,k2_relset_1(u1_struct_0(sK1),u1_struct_0(sK0),u1_waybel_0(sK0,sK1)))) | ~r2_lattice3(sK0,k2_relset_1(u1_struct_0(sK1),u1_struct_0(sK0),u1_waybel_0(sK0,sK1)),X1))),
% 0.22/0.53    introduced(avatar_definition,[new_symbols(naming,[spl9_47])])).
% 0.22/0.53  fof(f372,plain,(
% 0.22/0.53    ~m1_subset_1(k1_waybel_2(sK0,sK1),u1_struct_0(sK0)) | ~r2_lattice3(sK0,k2_relset_1(u1_struct_0(sK1),u1_struct_0(sK0),u1_waybel_0(sK0,sK1)),k1_waybel_2(sK0,sK1)) | r1_yellow_0(sK0,k2_relset_1(u1_struct_0(sK1),u1_struct_0(sK0),u1_waybel_0(sK0,sK1))) | ~l1_orders_2(sK0) | ~v5_orders_2(sK0) | ~spl9_47),
% 0.22/0.53    inference(duplicate_literal_removal,[],[f370])).
% 0.22/0.53  fof(f370,plain,(
% 0.22/0.53    ~m1_subset_1(k1_waybel_2(sK0,sK1),u1_struct_0(sK0)) | ~r2_lattice3(sK0,k2_relset_1(u1_struct_0(sK1),u1_struct_0(sK0),u1_waybel_0(sK0,sK1)),k1_waybel_2(sK0,sK1)) | r1_yellow_0(sK0,k2_relset_1(u1_struct_0(sK1),u1_struct_0(sK0),u1_waybel_0(sK0,sK1))) | ~r2_lattice3(sK0,k2_relset_1(u1_struct_0(sK1),u1_struct_0(sK0),u1_waybel_0(sK0,sK1)),k1_waybel_2(sK0,sK1)) | ~m1_subset_1(k1_waybel_2(sK0,sK1),u1_struct_0(sK0)) | ~l1_orders_2(sK0) | ~v5_orders_2(sK0) | ~spl9_47),
% 0.22/0.53    inference(resolution,[],[f367,f93])).
% 0.22/0.53  fof(f93,plain,(
% 0.22/0.53    ( ! [X2,X0,X1] : (~r1_orders_2(X0,X1,sK5(X0,X1,X2)) | r1_yellow_0(X0,X2) | ~r2_lattice3(X0,X2,X1) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_orders_2(X0) | ~v5_orders_2(X0)) )),
% 0.22/0.53    inference(cnf_transformation,[],[f49])).
% 0.22/0.53  fof(f49,plain,(
% 0.22/0.53    ! [X0] : (! [X1] : (! [X2] : (((r1_yellow_0(X0,X2) & k1_yellow_0(X0,X2) = X1) | (~r1_orders_2(X0,X1,sK5(X0,X1,X2)) & r2_lattice3(X0,X2,sK5(X0,X1,X2)) & m1_subset_1(sK5(X0,X1,X2),u1_struct_0(X0))) | ~r2_lattice3(X0,X2,X1)) & ((! [X4] : (r1_orders_2(X0,X1,X4) | ~r2_lattice3(X0,X2,X4) | ~m1_subset_1(X4,u1_struct_0(X0))) & r2_lattice3(X0,X2,X1)) | ~r1_yellow_0(X0,X2) | k1_yellow_0(X0,X2) != X1)) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~l1_orders_2(X0) | ~v5_orders_2(X0))),
% 0.22/0.53    inference(skolemisation,[status(esa),new_symbols(skolem,[sK5])],[f28,f48])).
% 0.22/0.53  fof(f48,plain,(
% 0.22/0.53    ! [X2,X1,X0] : (? [X3] : (~r1_orders_2(X0,X1,X3) & r2_lattice3(X0,X2,X3) & m1_subset_1(X3,u1_struct_0(X0))) => (~r1_orders_2(X0,X1,sK5(X0,X1,X2)) & r2_lattice3(X0,X2,sK5(X0,X1,X2)) & m1_subset_1(sK5(X0,X1,X2),u1_struct_0(X0))))),
% 0.22/0.53    introduced(choice_axiom,[])).
% 0.22/0.53  fof(f28,plain,(
% 0.22/0.53    ! [X0] : (! [X1] : (! [X2] : (((r1_yellow_0(X0,X2) & k1_yellow_0(X0,X2) = X1) | ? [X3] : (~r1_orders_2(X0,X1,X3) & r2_lattice3(X0,X2,X3) & m1_subset_1(X3,u1_struct_0(X0))) | ~r2_lattice3(X0,X2,X1)) & ((! [X4] : (r1_orders_2(X0,X1,X4) | ~r2_lattice3(X0,X2,X4) | ~m1_subset_1(X4,u1_struct_0(X0))) & r2_lattice3(X0,X2,X1)) | ~r1_yellow_0(X0,X2) | k1_yellow_0(X0,X2) != X1)) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~l1_orders_2(X0) | ~v5_orders_2(X0))),
% 0.22/0.53    inference(flattening,[],[f27])).
% 0.22/0.53  fof(f27,plain,(
% 0.22/0.53    ! [X0] : (! [X1] : (! [X2] : (((r1_yellow_0(X0,X2) & k1_yellow_0(X0,X2) = X1) | (? [X3] : ((~r1_orders_2(X0,X1,X3) & r2_lattice3(X0,X2,X3)) & m1_subset_1(X3,u1_struct_0(X0))) | ~r2_lattice3(X0,X2,X1))) & ((! [X4] : ((r1_orders_2(X0,X1,X4) | ~r2_lattice3(X0,X2,X4)) | ~m1_subset_1(X4,u1_struct_0(X0))) & r2_lattice3(X0,X2,X1)) | (~r1_yellow_0(X0,X2) | k1_yellow_0(X0,X2) != X1))) | ~m1_subset_1(X1,u1_struct_0(X0))) | (~l1_orders_2(X0) | ~v5_orders_2(X0)))),
% 0.22/0.53    inference(ennf_transformation,[],[f15])).
% 0.22/0.53  fof(f15,plain,(
% 0.22/0.53    ! [X0] : ((l1_orders_2(X0) & v5_orders_2(X0)) => ! [X1] : (m1_subset_1(X1,u1_struct_0(X0)) => ! [X2] : (((! [X3] : (m1_subset_1(X3,u1_struct_0(X0)) => (r2_lattice3(X0,X2,X3) => r1_orders_2(X0,X1,X3))) & r2_lattice3(X0,X2,X1)) => (r1_yellow_0(X0,X2) & k1_yellow_0(X0,X2) = X1)) & ((r1_yellow_0(X0,X2) & k1_yellow_0(X0,X2) = X1) => (! [X4] : (m1_subset_1(X4,u1_struct_0(X0)) => (r2_lattice3(X0,X2,X4) => r1_orders_2(X0,X1,X4))) & r2_lattice3(X0,X2,X1))))))),
% 0.22/0.53    inference(rectify,[],[f3])).
% 0.22/0.53  fof(f3,axiom,(
% 0.22/0.53    ! [X0] : ((l1_orders_2(X0) & v5_orders_2(X0)) => ! [X1] : (m1_subset_1(X1,u1_struct_0(X0)) => ! [X2] : (((! [X3] : (m1_subset_1(X3,u1_struct_0(X0)) => (r2_lattice3(X0,X2,X3) => r1_orders_2(X0,X1,X3))) & r2_lattice3(X0,X2,X1)) => (r1_yellow_0(X0,X2) & k1_yellow_0(X0,X2) = X1)) & ((r1_yellow_0(X0,X2) & k1_yellow_0(X0,X2) = X1) => (! [X3] : (m1_subset_1(X3,u1_struct_0(X0)) => (r2_lattice3(X0,X2,X3) => r1_orders_2(X0,X1,X3))) & r2_lattice3(X0,X2,X1))))))),
% 0.22/0.53    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t30_yellow_0)).
% 0.22/0.53  fof(f367,plain,(
% 0.22/0.53    ( ! [X1] : (r1_orders_2(sK0,k1_waybel_2(sK0,sK1),sK5(sK0,X1,k2_relset_1(u1_struct_0(sK1),u1_struct_0(sK0),u1_waybel_0(sK0,sK1)))) | ~m1_subset_1(X1,u1_struct_0(sK0)) | ~r2_lattice3(sK0,k2_relset_1(u1_struct_0(sK1),u1_struct_0(sK0),u1_waybel_0(sK0,sK1)),X1)) ) | ~spl9_47),
% 0.22/0.53    inference(avatar_component_clause,[],[f366])).
% 0.22/0.53  fof(f368,plain,(
% 0.22/0.53    ~spl9_12 | ~spl9_33 | spl9_39 | spl9_47 | ~spl9_40),
% 0.22/0.53    inference(avatar_split_clause,[],[f359,f314,f366,f311,f274,f156])).
% 0.22/0.53  fof(f314,plain,(
% 0.22/0.53    spl9_40 <=> ! [X2] : (r1_orders_2(sK0,k1_waybel_2(sK0,sK1),sK5(sK0,X2,k2_relset_1(u1_struct_0(sK1),u1_struct_0(sK0),u1_waybel_0(sK0,sK1)))) | ~m1_subset_1(X2,u1_struct_0(sK0)) | ~r2_lattice3(sK0,k2_relset_1(u1_struct_0(sK1),u1_struct_0(sK0),u1_waybel_0(sK0,sK1)),X2) | ~m1_subset_1(sK5(sK0,X2,k2_relset_1(u1_struct_0(sK1),u1_struct_0(sK0),u1_waybel_0(sK0,sK1))),u1_struct_0(sK0)))),
% 0.22/0.53    introduced(avatar_definition,[new_symbols(naming,[spl9_40])])).
% 0.22/0.53  fof(f359,plain,(
% 0.22/0.53    ( ! [X1] : (~m1_subset_1(X1,u1_struct_0(sK0)) | ~r2_lattice3(sK0,k2_relset_1(u1_struct_0(sK1),u1_struct_0(sK0),u1_waybel_0(sK0,sK1)),X1) | r1_orders_2(sK0,k1_waybel_2(sK0,sK1),sK5(sK0,X1,k2_relset_1(u1_struct_0(sK1),u1_struct_0(sK0),u1_waybel_0(sK0,sK1)))) | r1_yellow_0(sK0,k2_relset_1(u1_struct_0(sK1),u1_struct_0(sK0),u1_waybel_0(sK0,sK1))) | ~l1_orders_2(sK0) | ~v5_orders_2(sK0)) ) | ~spl9_40),
% 0.22/0.53    inference(duplicate_literal_removal,[],[f358])).
% 0.22/0.53  fof(f358,plain,(
% 0.22/0.53    ( ! [X1] : (~m1_subset_1(X1,u1_struct_0(sK0)) | ~r2_lattice3(sK0,k2_relset_1(u1_struct_0(sK1),u1_struct_0(sK0),u1_waybel_0(sK0,sK1)),X1) | r1_orders_2(sK0,k1_waybel_2(sK0,sK1),sK5(sK0,X1,k2_relset_1(u1_struct_0(sK1),u1_struct_0(sK0),u1_waybel_0(sK0,sK1)))) | r1_yellow_0(sK0,k2_relset_1(u1_struct_0(sK1),u1_struct_0(sK0),u1_waybel_0(sK0,sK1))) | ~r2_lattice3(sK0,k2_relset_1(u1_struct_0(sK1),u1_struct_0(sK0),u1_waybel_0(sK0,sK1)),X1) | ~m1_subset_1(X1,u1_struct_0(sK0)) | ~l1_orders_2(sK0) | ~v5_orders_2(sK0)) ) | ~spl9_40),
% 0.22/0.53    inference(resolution,[],[f315,f91])).
% 0.22/0.53  fof(f91,plain,(
% 0.22/0.53    ( ! [X2,X0,X1] : (m1_subset_1(sK5(X0,X1,X2),u1_struct_0(X0)) | r1_yellow_0(X0,X2) | ~r2_lattice3(X0,X2,X1) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_orders_2(X0) | ~v5_orders_2(X0)) )),
% 0.22/0.53    inference(cnf_transformation,[],[f49])).
% 0.22/0.53  fof(f315,plain,(
% 0.22/0.53    ( ! [X2] : (~m1_subset_1(sK5(sK0,X2,k2_relset_1(u1_struct_0(sK1),u1_struct_0(sK0),u1_waybel_0(sK0,sK1))),u1_struct_0(sK0)) | ~m1_subset_1(X2,u1_struct_0(sK0)) | ~r2_lattice3(sK0,k2_relset_1(u1_struct_0(sK1),u1_struct_0(sK0),u1_waybel_0(sK0,sK1)),X2) | r1_orders_2(sK0,k1_waybel_2(sK0,sK1),sK5(sK0,X2,k2_relset_1(u1_struct_0(sK1),u1_struct_0(sK0),u1_waybel_0(sK0,sK1))))) ) | ~spl9_40),
% 0.22/0.53    inference(avatar_component_clause,[],[f314])).
% 0.22/0.53  fof(f337,plain,(
% 0.22/0.53    spl9_43 | ~spl9_4 | ~spl9_5 | ~spl9_6 | spl9_7 | ~spl9_3 | ~spl9_42),
% 0.22/0.53    inference(avatar_split_clause,[],[f333,f324,f120,f136,f132,f128,f124,f335])).
% 0.22/0.53  fof(f324,plain,(
% 0.22/0.53    spl9_42 <=> ! [X1,X0] : (~r3_waybel_9(sK0,X0,X1) | v2_struct_0(X0) | ~v4_orders_2(X0) | ~v7_waybel_0(X0) | ~l1_waybel_0(X0,sK0) | ~m1_subset_1(X1,u1_struct_0(sK0)) | r2_lattice3(sK0,k2_relset_1(u1_struct_0(X0),u1_struct_0(sK0),u1_waybel_0(sK0,X0)),X1) | ~v10_waybel_0(X0,sK0))),
% 0.22/0.53    introduced(avatar_definition,[new_symbols(naming,[spl9_42])])).
% 0.22/0.53  fof(f333,plain,(
% 0.22/0.53    ( ! [X0] : (v2_struct_0(sK1) | ~v4_orders_2(sK1) | ~v7_waybel_0(sK1) | ~l1_waybel_0(sK1,sK0) | ~m1_subset_1(X0,u1_struct_0(sK0)) | r2_lattice3(sK0,k2_relset_1(u1_struct_0(sK1),u1_struct_0(sK0),u1_waybel_0(sK0,sK1)),X0) | ~r3_waybel_9(sK0,sK1,X0)) ) | (~spl9_3 | ~spl9_42)),
% 0.22/0.53    inference(resolution,[],[f325,f121])).
% 0.22/0.53  fof(f121,plain,(
% 0.22/0.53    v10_waybel_0(sK1,sK0) | ~spl9_3),
% 0.22/0.53    inference(avatar_component_clause,[],[f120])).
% 0.22/0.53  fof(f325,plain,(
% 0.22/0.53    ( ! [X0,X1] : (~v10_waybel_0(X0,sK0) | v2_struct_0(X0) | ~v4_orders_2(X0) | ~v7_waybel_0(X0) | ~l1_waybel_0(X0,sK0) | ~m1_subset_1(X1,u1_struct_0(sK0)) | r2_lattice3(sK0,k2_relset_1(u1_struct_0(X0),u1_struct_0(sK0),u1_waybel_0(sK0,X0)),X1) | ~r3_waybel_9(sK0,X0,X1)) ) | ~spl9_42),
% 0.22/0.53    inference(avatar_component_clause,[],[f324])).
% 0.22/0.53  fof(f326,plain,(
% 0.22/0.53    ~spl9_16 | ~spl9_15 | ~spl9_14 | ~spl9_13 | ~spl9_12 | ~spl9_11 | ~spl9_10 | ~spl9_9 | ~spl9_8 | spl9_42 | spl9_41),
% 0.22/0.53    inference(avatar_split_clause,[],[f322,f319,f324,f140,f144,f148,f152,f156,f160,f164,f168,f172])).
% 0.22/0.53  fof(f319,plain,(
% 0.22/0.53    spl9_41 <=> m1_subset_1(sK7(sK0),u1_struct_0(sK0))),
% 0.22/0.53    introduced(avatar_definition,[new_symbols(naming,[spl9_41])])).
% 0.22/0.53  fof(f322,plain,(
% 0.22/0.53    ( ! [X0,X1] : (~r3_waybel_9(sK0,X0,X1) | ~v10_waybel_0(X0,sK0) | r2_lattice3(sK0,k2_relset_1(u1_struct_0(X0),u1_struct_0(sK0),u1_waybel_0(sK0,X0)),X1) | ~m1_subset_1(X1,u1_struct_0(sK0)) | ~l1_waybel_0(X0,sK0) | ~v7_waybel_0(X0) | ~v4_orders_2(X0) | v2_struct_0(X0) | ~l1_waybel_9(sK0) | ~v1_compts_1(sK0) | ~v2_lattice3(sK0) | ~v1_lattice3(sK0) | ~v5_orders_2(sK0) | ~v4_orders_2(sK0) | ~v3_orders_2(sK0) | ~v8_pre_topc(sK0) | ~v2_pre_topc(sK0)) ) | spl9_41),
% 0.22/0.53    inference(resolution,[],[f320,f110])).
% 0.22/0.53  fof(f110,plain,(
% 0.22/0.53    ( ! [X0,X3,X1] : (m1_subset_1(sK7(X0),u1_struct_0(X0)) | ~r3_waybel_9(X0,X1,X3) | ~v10_waybel_0(X1,X0) | r2_lattice3(X0,k2_relset_1(u1_struct_0(X1),u1_struct_0(X0),u1_waybel_0(X0,X1)),X3) | ~m1_subset_1(X3,u1_struct_0(X0)) | ~l1_waybel_0(X1,X0) | ~v7_waybel_0(X1) | ~v4_orders_2(X1) | v2_struct_0(X1) | ~l1_waybel_9(X0) | ~v1_compts_1(X0) | ~v2_lattice3(X0) | ~v1_lattice3(X0) | ~v5_orders_2(X0) | ~v4_orders_2(X0) | ~v3_orders_2(X0) | ~v8_pre_topc(X0) | ~v2_pre_topc(X0)) )),
% 0.22/0.53    inference(duplicate_literal_removal,[],[f105])).
% 0.22/0.53  fof(f105,plain,(
% 0.22/0.53    ( ! [X0,X3,X1] : (r2_lattice3(X0,k2_relset_1(u1_struct_0(X1),u1_struct_0(X0),u1_waybel_0(X0,X1)),X3) | ~r3_waybel_9(X0,X1,X3) | ~v10_waybel_0(X1,X0) | m1_subset_1(sK7(X0),u1_struct_0(X0)) | ~m1_subset_1(X3,u1_struct_0(X0)) | ~m1_subset_1(X3,u1_struct_0(X0)) | ~l1_waybel_0(X1,X0) | ~v7_waybel_0(X1) | ~v4_orders_2(X1) | v2_struct_0(X1) | ~l1_waybel_9(X0) | ~v1_compts_1(X0) | ~v2_lattice3(X0) | ~v1_lattice3(X0) | ~v5_orders_2(X0) | ~v4_orders_2(X0) | ~v3_orders_2(X0) | ~v8_pre_topc(X0) | ~v2_pre_topc(X0)) )),
% 0.22/0.53    inference(equality_resolution,[],[f96])).
% 0.22/0.53  fof(f96,plain,(
% 0.22/0.53    ( ! [X2,X0,X3,X1] : (r2_lattice3(X0,k2_relset_1(u1_struct_0(X1),u1_struct_0(X0),u1_waybel_0(X0,X1)),X3) | ~r3_waybel_9(X0,X1,X2) | ~v10_waybel_0(X1,X0) | m1_subset_1(sK7(X0),u1_struct_0(X0)) | X2 != X3 | ~m1_subset_1(X3,u1_struct_0(X0)) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~l1_waybel_0(X1,X0) | ~v7_waybel_0(X1) | ~v4_orders_2(X1) | v2_struct_0(X1) | ~l1_waybel_9(X0) | ~v1_compts_1(X0) | ~v2_lattice3(X0) | ~v1_lattice3(X0) | ~v5_orders_2(X0) | ~v4_orders_2(X0) | ~v3_orders_2(X0) | ~v8_pre_topc(X0) | ~v2_pre_topc(X0)) )),
% 0.22/0.53    inference(cnf_transformation,[],[f53])).
% 0.22/0.53  fof(f320,plain,(
% 0.22/0.53    ~m1_subset_1(sK7(sK0),u1_struct_0(sK0)) | spl9_41),
% 0.22/0.53    inference(avatar_component_clause,[],[f319])).
% 0.22/0.53  fof(f321,plain,(
% 0.22/0.53    ~spl9_41 | spl9_36),
% 0.22/0.53    inference(avatar_split_clause,[],[f317,f299,f319])).
% 0.22/0.53  fof(f317,plain,(
% 0.22/0.53    ~m1_subset_1(sK7(sK0),u1_struct_0(sK0)) | spl9_36),
% 0.22/0.53    inference(resolution,[],[f300,f67])).
% 0.22/0.53  fof(f67,plain,(
% 0.22/0.53    ( ! [X2] : (v5_pre_topc(k4_waybel_1(sK0,X2),sK0,sK0) | ~m1_subset_1(X2,u1_struct_0(sK0))) )),
% 0.22/0.53    inference(cnf_transformation,[],[f40])).
% 0.22/0.53  fof(f40,plain,(
% 0.22/0.53    ((~r2_hidden(k1_waybel_2(sK0,sK1),k10_yellow_6(sK0,sK1)) | ~r1_waybel_9(sK0,sK1)) & v10_waybel_0(sK1,sK0) & l1_waybel_0(sK1,sK0) & v7_waybel_0(sK1) & v4_orders_2(sK1) & ~v2_struct_0(sK1)) & ! [X2] : (v5_pre_topc(k4_waybel_1(sK0,X2),sK0,sK0) | ~m1_subset_1(X2,u1_struct_0(sK0))) & l1_waybel_9(sK0) & v1_compts_1(sK0) & v2_lattice3(sK0) & v1_lattice3(sK0) & v5_orders_2(sK0) & v4_orders_2(sK0) & v3_orders_2(sK0) & v8_pre_topc(sK0) & v2_pre_topc(sK0)),
% 0.22/0.53    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f37,f39,f38])).
% 0.22/0.53  fof(f38,plain,(
% 0.22/0.53    ? [X0] : (? [X1] : ((~r2_hidden(k1_waybel_2(X0,X1),k10_yellow_6(X0,X1)) | ~r1_waybel_9(X0,X1)) & v10_waybel_0(X1,X0) & l1_waybel_0(X1,X0) & v7_waybel_0(X1) & v4_orders_2(X1) & ~v2_struct_0(X1)) & ! [X2] : (v5_pre_topc(k4_waybel_1(X0,X2),X0,X0) | ~m1_subset_1(X2,u1_struct_0(X0))) & l1_waybel_9(X0) & v1_compts_1(X0) & v2_lattice3(X0) & v1_lattice3(X0) & v5_orders_2(X0) & v4_orders_2(X0) & v3_orders_2(X0) & v8_pre_topc(X0) & v2_pre_topc(X0)) => (? [X1] : ((~r2_hidden(k1_waybel_2(sK0,X1),k10_yellow_6(sK0,X1)) | ~r1_waybel_9(sK0,X1)) & v10_waybel_0(X1,sK0) & l1_waybel_0(X1,sK0) & v7_waybel_0(X1) & v4_orders_2(X1) & ~v2_struct_0(X1)) & ! [X2] : (v5_pre_topc(k4_waybel_1(sK0,X2),sK0,sK0) | ~m1_subset_1(X2,u1_struct_0(sK0))) & l1_waybel_9(sK0) & v1_compts_1(sK0) & v2_lattice3(sK0) & v1_lattice3(sK0) & v5_orders_2(sK0) & v4_orders_2(sK0) & v3_orders_2(sK0) & v8_pre_topc(sK0) & v2_pre_topc(sK0))),
% 0.22/0.53    introduced(choice_axiom,[])).
% 0.22/0.53  fof(f39,plain,(
% 0.22/0.53    ? [X1] : ((~r2_hidden(k1_waybel_2(sK0,X1),k10_yellow_6(sK0,X1)) | ~r1_waybel_9(sK0,X1)) & v10_waybel_0(X1,sK0) & l1_waybel_0(X1,sK0) & v7_waybel_0(X1) & v4_orders_2(X1) & ~v2_struct_0(X1)) => ((~r2_hidden(k1_waybel_2(sK0,sK1),k10_yellow_6(sK0,sK1)) | ~r1_waybel_9(sK0,sK1)) & v10_waybel_0(sK1,sK0) & l1_waybel_0(sK1,sK0) & v7_waybel_0(sK1) & v4_orders_2(sK1) & ~v2_struct_0(sK1))),
% 0.22/0.53    introduced(choice_axiom,[])).
% 0.22/0.53  fof(f37,plain,(
% 0.22/0.53    ? [X0] : (? [X1] : ((~r2_hidden(k1_waybel_2(X0,X1),k10_yellow_6(X0,X1)) | ~r1_waybel_9(X0,X1)) & v10_waybel_0(X1,X0) & l1_waybel_0(X1,X0) & v7_waybel_0(X1) & v4_orders_2(X1) & ~v2_struct_0(X1)) & ! [X2] : (v5_pre_topc(k4_waybel_1(X0,X2),X0,X0) | ~m1_subset_1(X2,u1_struct_0(X0))) & l1_waybel_9(X0) & v1_compts_1(X0) & v2_lattice3(X0) & v1_lattice3(X0) & v5_orders_2(X0) & v4_orders_2(X0) & v3_orders_2(X0) & v8_pre_topc(X0) & v2_pre_topc(X0))),
% 0.22/0.53    inference(rectify,[],[f18])).
% 0.22/0.53  fof(f18,plain,(
% 0.22/0.53    ? [X0] : (? [X2] : ((~r2_hidden(k1_waybel_2(X0,X2),k10_yellow_6(X0,X2)) | ~r1_waybel_9(X0,X2)) & v10_waybel_0(X2,X0) & l1_waybel_0(X2,X0) & v7_waybel_0(X2) & v4_orders_2(X2) & ~v2_struct_0(X2)) & ! [X1] : (v5_pre_topc(k4_waybel_1(X0,X1),X0,X0) | ~m1_subset_1(X1,u1_struct_0(X0))) & l1_waybel_9(X0) & v1_compts_1(X0) & v2_lattice3(X0) & v1_lattice3(X0) & v5_orders_2(X0) & v4_orders_2(X0) & v3_orders_2(X0) & v8_pre_topc(X0) & v2_pre_topc(X0))),
% 0.22/0.53    inference(flattening,[],[f17])).
% 0.22/0.53  fof(f17,plain,(
% 0.22/0.53    ? [X0] : ((? [X2] : (((~r2_hidden(k1_waybel_2(X0,X2),k10_yellow_6(X0,X2)) | ~r1_waybel_9(X0,X2)) & v10_waybel_0(X2,X0)) & (l1_waybel_0(X2,X0) & v7_waybel_0(X2) & v4_orders_2(X2) & ~v2_struct_0(X2))) & ! [X1] : (v5_pre_topc(k4_waybel_1(X0,X1),X0,X0) | ~m1_subset_1(X1,u1_struct_0(X0)))) & (l1_waybel_9(X0) & v1_compts_1(X0) & v2_lattice3(X0) & v1_lattice3(X0) & v5_orders_2(X0) & v4_orders_2(X0) & v3_orders_2(X0) & v8_pre_topc(X0) & v2_pre_topc(X0)))),
% 0.22/0.53    inference(ennf_transformation,[],[f13])).
% 0.22/0.53  fof(f13,plain,(
% 0.22/0.53    ~! [X0] : ((l1_waybel_9(X0) & v1_compts_1(X0) & v2_lattice3(X0) & v1_lattice3(X0) & v5_orders_2(X0) & v4_orders_2(X0) & v3_orders_2(X0) & v8_pre_topc(X0) & v2_pre_topc(X0)) => (! [X1] : (m1_subset_1(X1,u1_struct_0(X0)) => v5_pre_topc(k4_waybel_1(X0,X1),X0,X0)) => ! [X2] : ((l1_waybel_0(X2,X0) & v7_waybel_0(X2) & v4_orders_2(X2) & ~v2_struct_0(X2)) => (v10_waybel_0(X2,X0) => (r2_hidden(k1_waybel_2(X0,X2),k10_yellow_6(X0,X2)) & r1_waybel_9(X0,X2))))))),
% 0.22/0.53    inference(rectify,[],[f12])).
% 0.22/0.53  fof(f12,negated_conjecture,(
% 0.22/0.53    ~! [X0] : ((l1_waybel_9(X0) & v1_compts_1(X0) & v2_lattice3(X0) & v1_lattice3(X0) & v5_orders_2(X0) & v4_orders_2(X0) & v3_orders_2(X0) & v8_pre_topc(X0) & v2_pre_topc(X0)) => (! [X1] : (m1_subset_1(X1,u1_struct_0(X0)) => v5_pre_topc(k4_waybel_1(X0,X1),X0,X0)) => ! [X1] : ((l1_waybel_0(X1,X0) & v7_waybel_0(X1) & v4_orders_2(X1) & ~v2_struct_0(X1)) => (v10_waybel_0(X1,X0) => (r2_hidden(k1_waybel_2(X0,X1),k10_yellow_6(X0,X1)) & r1_waybel_9(X0,X1))))))),
% 0.22/0.53    inference(negated_conjecture,[],[f11])).
% 0.22/0.53  fof(f11,conjecture,(
% 0.22/0.53    ! [X0] : ((l1_waybel_9(X0) & v1_compts_1(X0) & v2_lattice3(X0) & v1_lattice3(X0) & v5_orders_2(X0) & v4_orders_2(X0) & v3_orders_2(X0) & v8_pre_topc(X0) & v2_pre_topc(X0)) => (! [X1] : (m1_subset_1(X1,u1_struct_0(X0)) => v5_pre_topc(k4_waybel_1(X0,X1),X0,X0)) => ! [X1] : ((l1_waybel_0(X1,X0) & v7_waybel_0(X1) & v4_orders_2(X1) & ~v2_struct_0(X1)) => (v10_waybel_0(X1,X0) => (r2_hidden(k1_waybel_2(X0,X1),k10_yellow_6(X0,X1)) & r1_waybel_9(X0,X1))))))),
% 0.22/0.53    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t38_waybel_9)).
% 0.22/0.53  fof(f300,plain,(
% 0.22/0.53    ~v5_pre_topc(k4_waybel_1(sK0,sK7(sK0)),sK0,sK0) | spl9_36),
% 0.22/0.53    inference(avatar_component_clause,[],[f299])).
% 0.22/0.53  fof(f316,plain,(
% 0.22/0.53    ~spl9_12 | ~spl9_33 | spl9_39 | spl9_40 | ~spl9_35),
% 0.22/0.53    inference(avatar_split_clause,[],[f296,f286,f314,f311,f274,f156])).
% 0.22/0.53  fof(f286,plain,(
% 0.22/0.53    spl9_35 <=> ! [X0] : (~r2_lattice3(sK0,k2_relset_1(u1_struct_0(sK1),u1_struct_0(sK0),u1_waybel_0(sK0,sK1)),X0) | r1_orders_2(sK0,k1_waybel_2(sK0,sK1),X0) | ~m1_subset_1(X0,u1_struct_0(sK0)))),
% 0.22/0.53    introduced(avatar_definition,[new_symbols(naming,[spl9_35])])).
% 0.22/0.53  fof(f296,plain,(
% 0.22/0.53    ( ! [X2] : (r1_orders_2(sK0,k1_waybel_2(sK0,sK1),sK5(sK0,X2,k2_relset_1(u1_struct_0(sK1),u1_struct_0(sK0),u1_waybel_0(sK0,sK1)))) | ~m1_subset_1(sK5(sK0,X2,k2_relset_1(u1_struct_0(sK1),u1_struct_0(sK0),u1_waybel_0(sK0,sK1))),u1_struct_0(sK0)) | r1_yellow_0(sK0,k2_relset_1(u1_struct_0(sK1),u1_struct_0(sK0),u1_waybel_0(sK0,sK1))) | ~r2_lattice3(sK0,k2_relset_1(u1_struct_0(sK1),u1_struct_0(sK0),u1_waybel_0(sK0,sK1)),X2) | ~m1_subset_1(X2,u1_struct_0(sK0)) | ~l1_orders_2(sK0) | ~v5_orders_2(sK0)) ) | ~spl9_35),
% 0.22/0.53    inference(resolution,[],[f287,f92])).
% 0.22/0.53  fof(f92,plain,(
% 0.22/0.53    ( ! [X2,X0,X1] : (r2_lattice3(X0,X2,sK5(X0,X1,X2)) | r1_yellow_0(X0,X2) | ~r2_lattice3(X0,X2,X1) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_orders_2(X0) | ~v5_orders_2(X0)) )),
% 0.22/0.53    inference(cnf_transformation,[],[f49])).
% 0.22/0.53  fof(f287,plain,(
% 0.22/0.53    ( ! [X0] : (~r2_lattice3(sK0,k2_relset_1(u1_struct_0(sK1),u1_struct_0(sK0),u1_waybel_0(sK0,sK1)),X0) | r1_orders_2(sK0,k1_waybel_2(sK0,sK1),X0) | ~m1_subset_1(X0,u1_struct_0(sK0))) ) | ~spl9_35),
% 0.22/0.53    inference(avatar_component_clause,[],[f286])).
% 0.22/0.53  fof(f293,plain,(
% 0.22/0.53    ~spl9_33 | ~spl9_11 | ~spl9_22),
% 0.22/0.53    inference(avatar_split_clause,[],[f292,f219,f152,f274])).
% 0.22/0.53  fof(f292,plain,(
% 0.22/0.53    ~v1_lattice3(sK0) | ~l1_orders_2(sK0) | ~spl9_22),
% 0.22/0.53    inference(resolution,[],[f220,f76])).
% 0.22/0.53  fof(f76,plain,(
% 0.22/0.53    ( ! [X0] : (~v2_struct_0(X0) | ~v1_lattice3(X0) | ~l1_orders_2(X0)) )),
% 0.22/0.53    inference(cnf_transformation,[],[f21])).
% 0.22/0.53  fof(f21,plain,(
% 0.22/0.53    ! [X0] : (~v2_struct_0(X0) | ~v1_lattice3(X0) | ~l1_orders_2(X0))),
% 0.22/0.53    inference(flattening,[],[f20])).
% 0.22/0.53  fof(f20,plain,(
% 0.22/0.53    ! [X0] : ((~v2_struct_0(X0) | ~v1_lattice3(X0)) | ~l1_orders_2(X0))),
% 0.22/0.53    inference(ennf_transformation,[],[f2])).
% 0.22/0.53  fof(f2,axiom,(
% 0.22/0.53    ! [X0] : (l1_orders_2(X0) => (v1_lattice3(X0) => ~v2_struct_0(X0)))),
% 0.22/0.53    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_lattice3)).
% 0.22/0.53  fof(f220,plain,(
% 0.22/0.53    v2_struct_0(sK0) | ~spl9_22),
% 0.22/0.53    inference(avatar_component_clause,[],[f219])).
% 0.22/0.53  fof(f291,plain,(
% 0.22/0.53    spl9_22 | ~spl9_16 | ~spl9_15 | ~spl9_9 | ~spl9_23 | spl9_7 | ~spl9_6 | ~spl9_5 | ~spl9_4 | spl9_35 | ~spl9_27 | ~spl9_24 | ~spl9_34),
% 0.22/0.53    inference(avatar_split_clause,[],[f290,f277,f225,f242,f286,f124,f128,f132,f136,f222,f144,f168,f172,f219])).
% 0.22/0.53  fof(f225,plain,(
% 0.22/0.53    spl9_24 <=> k1_waybel_2(sK0,sK1) = sK4(sK0,sK1)),
% 0.22/0.53    introduced(avatar_definition,[new_symbols(naming,[spl9_24])])).
% 0.22/0.53  fof(f277,plain,(
% 0.22/0.53    spl9_34 <=> ! [X1,X0] : (~m1_subset_1(X0,u1_struct_0(sK0)) | ~r2_lattice3(sK0,k2_relset_1(u1_struct_0(sK1),u1_struct_0(sK0),u1_waybel_0(sK0,sK1)),X0) | ~r3_waybel_9(sK0,sK1,X1) | r1_orders_2(sK0,X1,X0) | ~m1_subset_1(X1,u1_struct_0(sK0)))),
% 0.22/0.53    introduced(avatar_definition,[new_symbols(naming,[spl9_34])])).
% 0.22/0.53  fof(f290,plain,(
% 0.22/0.53    ( ! [X1] : (~m1_subset_1(k1_waybel_2(sK0,sK1),u1_struct_0(sK0)) | r1_orders_2(sK0,k1_waybel_2(sK0,sK1),X1) | ~r2_lattice3(sK0,k2_relset_1(u1_struct_0(sK1),u1_struct_0(sK0),u1_waybel_0(sK0,sK1)),X1) | ~m1_subset_1(X1,u1_struct_0(sK0)) | ~l1_waybel_0(sK1,sK0) | ~v7_waybel_0(sK1) | ~v4_orders_2(sK1) | v2_struct_0(sK1) | ~l1_pre_topc(sK0) | ~v1_compts_1(sK0) | ~v8_pre_topc(sK0) | ~v2_pre_topc(sK0) | v2_struct_0(sK0)) ) | (~spl9_24 | ~spl9_34)),
% 0.22/0.53    inference(forward_demodulation,[],[f289,f226])).
% 0.22/0.53  fof(f226,plain,(
% 0.22/0.53    k1_waybel_2(sK0,sK1) = sK4(sK0,sK1) | ~spl9_24),
% 0.22/0.53    inference(avatar_component_clause,[],[f225])).
% 0.22/0.53  fof(f289,plain,(
% 0.22/0.53    ( ! [X1] : (r1_orders_2(sK0,k1_waybel_2(sK0,sK1),X1) | ~r2_lattice3(sK0,k2_relset_1(u1_struct_0(sK1),u1_struct_0(sK0),u1_waybel_0(sK0,sK1)),X1) | ~m1_subset_1(X1,u1_struct_0(sK0)) | ~m1_subset_1(sK4(sK0,sK1),u1_struct_0(sK0)) | ~l1_waybel_0(sK1,sK0) | ~v7_waybel_0(sK1) | ~v4_orders_2(sK1) | v2_struct_0(sK1) | ~l1_pre_topc(sK0) | ~v1_compts_1(sK0) | ~v8_pre_topc(sK0) | ~v2_pre_topc(sK0) | v2_struct_0(sK0)) ) | (~spl9_24 | ~spl9_34)),
% 0.22/0.53    inference(forward_demodulation,[],[f283,f226])).
% 0.22/0.53  fof(f283,plain,(
% 0.22/0.53    ( ! [X1] : (~r2_lattice3(sK0,k2_relset_1(u1_struct_0(sK1),u1_struct_0(sK0),u1_waybel_0(sK0,sK1)),X1) | ~m1_subset_1(X1,u1_struct_0(sK0)) | r1_orders_2(sK0,sK4(sK0,sK1),X1) | ~m1_subset_1(sK4(sK0,sK1),u1_struct_0(sK0)) | ~l1_waybel_0(sK1,sK0) | ~v7_waybel_0(sK1) | ~v4_orders_2(sK1) | v2_struct_0(sK1) | ~l1_pre_topc(sK0) | ~v1_compts_1(sK0) | ~v8_pre_topc(sK0) | ~v2_pre_topc(sK0) | v2_struct_0(sK0)) ) | ~spl9_34),
% 0.22/0.53    inference(resolution,[],[f278,f85])).
% 0.22/0.53  fof(f85,plain,(
% 0.22/0.53    ( ! [X0,X1] : (r3_waybel_9(X0,X1,sK4(X0,X1)) | ~l1_waybel_0(X1,X0) | ~v7_waybel_0(X1) | ~v4_orders_2(X1) | v2_struct_0(X1) | ~l1_pre_topc(X0) | ~v1_compts_1(X0) | ~v8_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 0.22/0.53    inference(cnf_transformation,[],[f47])).
% 0.22/0.53  % (3881)Refutation not found, incomplete strategy% (3881)------------------------------
% 0.22/0.53  % (3881)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.53  % (3881)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.53  
% 0.22/0.53  % (3881)Memory used [KB]: 7036
% 0.22/0.53  % (3881)Time elapsed: 0.121 s
% 0.22/0.53  % (3881)------------------------------
% 0.22/0.53  % (3881)------------------------------
% 0.22/0.53  fof(f47,plain,(
% 0.22/0.53    ! [X0] : (! [X1] : ((r3_waybel_9(X0,X1,sK4(X0,X1)) & m1_subset_1(sK4(X0,X1),u1_struct_0(X0))) | ~l1_waybel_0(X1,X0) | ~v7_waybel_0(X1) | ~v4_orders_2(X1) | v2_struct_0(X1)) | ~l1_pre_topc(X0) | ~v1_compts_1(X0) | ~v8_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 0.22/0.53    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4])],[f26,f46])).
% 0.22/0.53  fof(f46,plain,(
% 0.22/0.53    ! [X1,X0] : (? [X2] : (r3_waybel_9(X0,X1,X2) & m1_subset_1(X2,u1_struct_0(X0))) => (r3_waybel_9(X0,X1,sK4(X0,X1)) & m1_subset_1(sK4(X0,X1),u1_struct_0(X0))))),
% 0.22/0.53    introduced(choice_axiom,[])).
% 0.22/0.53  fof(f26,plain,(
% 0.22/0.53    ! [X0] : (! [X1] : (? [X2] : (r3_waybel_9(X0,X1,X2) & m1_subset_1(X2,u1_struct_0(X0))) | ~l1_waybel_0(X1,X0) | ~v7_waybel_0(X1) | ~v4_orders_2(X1) | v2_struct_0(X1)) | ~l1_pre_topc(X0) | ~v1_compts_1(X0) | ~v8_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 0.22/0.53    inference(flattening,[],[f25])).
% 0.22/0.53  fof(f25,plain,(
% 0.22/0.53    ! [X0] : (! [X1] : (? [X2] : (r3_waybel_9(X0,X1,X2) & m1_subset_1(X2,u1_struct_0(X0))) | (~l1_waybel_0(X1,X0) | ~v7_waybel_0(X1) | ~v4_orders_2(X1) | v2_struct_0(X1))) | (~l1_pre_topc(X0) | ~v1_compts_1(X0) | ~v8_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 0.22/0.53    inference(ennf_transformation,[],[f8])).
% 0.22/0.53  fof(f8,axiom,(
% 0.22/0.53    ! [X0] : ((l1_pre_topc(X0) & v1_compts_1(X0) & v8_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((l1_waybel_0(X1,X0) & v7_waybel_0(X1) & v4_orders_2(X1) & ~v2_struct_0(X1)) => ? [X2] : (r3_waybel_9(X0,X1,X2) & m1_subset_1(X2,u1_struct_0(X0)))))),
% 0.22/0.53    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t30_waybel_9)).
% 0.22/0.53  fof(f278,plain,(
% 0.22/0.53    ( ! [X0,X1] : (~r3_waybel_9(sK0,sK1,X1) | ~r2_lattice3(sK0,k2_relset_1(u1_struct_0(sK1),u1_struct_0(sK0),u1_waybel_0(sK0,sK1)),X0) | ~m1_subset_1(X0,u1_struct_0(sK0)) | r1_orders_2(sK0,X1,X0) | ~m1_subset_1(X1,u1_struct_0(sK0))) ) | ~spl9_34),
% 0.22/0.53    inference(avatar_component_clause,[],[f277])).
% 0.22/0.53  fof(f281,plain,(
% 0.22/0.53    ~spl9_8 | spl9_33),
% 0.22/0.53    inference(avatar_split_clause,[],[f280,f274,f140])).
% 0.22/0.53  fof(f280,plain,(
% 0.22/0.53    ~l1_waybel_9(sK0) | spl9_33),
% 0.22/0.53    inference(resolution,[],[f275,f75])).
% 0.22/0.53  fof(f275,plain,(
% 0.22/0.53    ~l1_orders_2(sK0) | spl9_33),
% 0.22/0.53    inference(avatar_component_clause,[],[f274])).
% 0.22/0.53  fof(f279,plain,(
% 0.22/0.53    spl9_22 | ~spl9_14 | ~spl9_33 | spl9_34 | ~spl9_30),
% 0.22/0.53    inference(avatar_split_clause,[],[f272,f256,f277,f274,f164,f219])).
% 0.22/0.53  fof(f256,plain,(
% 0.22/0.53    spl9_30 <=> ! [X1,X0] : (~r2_lattice3(sK0,k2_relset_1(u1_struct_0(sK1),u1_struct_0(sK0),u1_waybel_0(sK0,sK1)),X0) | ~m1_subset_1(X0,u1_struct_0(sK0)) | ~r3_waybel_9(sK0,sK1,X1) | ~m1_subset_1(X1,u1_struct_0(sK0)) | r3_orders_2(sK0,X1,X0))),
% 0.22/0.53    introduced(avatar_definition,[new_symbols(naming,[spl9_30])])).
% 0.22/0.53  fof(f272,plain,(
% 0.22/0.53    ( ! [X0,X1] : (~m1_subset_1(X0,u1_struct_0(sK0)) | ~r3_waybel_9(sK0,sK1,X1) | ~m1_subset_1(X1,u1_struct_0(sK0)) | ~r2_lattice3(sK0,k2_relset_1(u1_struct_0(sK1),u1_struct_0(sK0),u1_waybel_0(sK0,sK1)),X0) | r1_orders_2(sK0,X1,X0) | ~l1_orders_2(sK0) | ~v3_orders_2(sK0) | v2_struct_0(sK0)) ) | ~spl9_30),
% 0.22/0.53    inference(duplicate_literal_removal,[],[f271])).
% 0.22/0.53  fof(f271,plain,(
% 0.22/0.53    ( ! [X0,X1] : (~m1_subset_1(X0,u1_struct_0(sK0)) | ~r3_waybel_9(sK0,sK1,X1) | ~m1_subset_1(X1,u1_struct_0(sK0)) | ~r2_lattice3(sK0,k2_relset_1(u1_struct_0(sK1),u1_struct_0(sK0),u1_waybel_0(sK0,sK1)),X0) | r1_orders_2(sK0,X1,X0) | ~m1_subset_1(X0,u1_struct_0(sK0)) | ~m1_subset_1(X1,u1_struct_0(sK0)) | ~l1_orders_2(sK0) | ~v3_orders_2(sK0) | v2_struct_0(sK0)) ) | ~spl9_30),
% 0.22/0.53    inference(resolution,[],[f257,f100])).
% 0.22/0.53  fof(f100,plain,(
% 0.22/0.53    ( ! [X2,X0,X1] : (~r3_orders_2(X0,X1,X2) | r1_orders_2(X0,X1,X2) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_orders_2(X0) | ~v3_orders_2(X0) | v2_struct_0(X0)) )),
% 0.22/0.53    inference(cnf_transformation,[],[f57])).
% 0.22/0.53  fof(f57,plain,(
% 0.22/0.53    ! [X0,X1,X2] : (((r3_orders_2(X0,X1,X2) | ~r1_orders_2(X0,X1,X2)) & (r1_orders_2(X0,X1,X2) | ~r3_orders_2(X0,X1,X2))) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_orders_2(X0) | ~v3_orders_2(X0) | v2_struct_0(X0))),
% 0.22/0.53    inference(nnf_transformation,[],[f36])).
% 0.22/0.53  fof(f36,plain,(
% 0.22/0.53    ! [X0,X1,X2] : ((r3_orders_2(X0,X1,X2) <=> r1_orders_2(X0,X1,X2)) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_orders_2(X0) | ~v3_orders_2(X0) | v2_struct_0(X0))),
% 0.22/0.53    inference(flattening,[],[f35])).
% 0.22/0.53  fof(f35,plain,(
% 0.22/0.53    ! [X0,X1,X2] : ((r3_orders_2(X0,X1,X2) <=> r1_orders_2(X0,X1,X2)) | (~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_orders_2(X0) | ~v3_orders_2(X0) | v2_struct_0(X0)))),
% 0.22/0.53    inference(ennf_transformation,[],[f1])).
% 0.22/0.53  fof(f1,axiom,(
% 0.22/0.53    ! [X0,X1,X2] : ((m1_subset_1(X2,u1_struct_0(X0)) & m1_subset_1(X1,u1_struct_0(X0)) & l1_orders_2(X0) & v3_orders_2(X0) & ~v2_struct_0(X0)) => (r3_orders_2(X0,X1,X2) <=> r1_orders_2(X0,X1,X2)))),
% 0.22/0.53    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_r3_orders_2)).
% 0.22/0.53  fof(f257,plain,(
% 0.22/0.53    ( ! [X0,X1] : (r3_orders_2(sK0,X1,X0) | ~m1_subset_1(X0,u1_struct_0(sK0)) | ~r3_waybel_9(sK0,sK1,X1) | ~m1_subset_1(X1,u1_struct_0(sK0)) | ~r2_lattice3(sK0,k2_relset_1(u1_struct_0(sK1),u1_struct_0(sK0),u1_waybel_0(sK0,sK1)),X0)) ) | ~spl9_30),
% 0.22/0.53    inference(avatar_component_clause,[],[f256])).
% 0.22/0.53  fof(f270,plain,(
% 0.22/0.53    ~spl9_4 | spl9_30 | ~spl9_6 | spl9_7 | ~spl9_5 | ~spl9_32),
% 0.22/0.53    inference(avatar_split_clause,[],[f269,f266,f128,f136,f132,f256,f124])).
% 0.22/0.53  fof(f266,plain,(
% 0.22/0.53    spl9_32 <=> ! [X1,X0,X2] : (~r2_lattice3(sK0,k2_relset_1(u1_struct_0(X0),u1_struct_0(sK0),u1_waybel_0(sK0,X0)),X1) | v2_struct_0(X0) | ~v4_orders_2(X0) | ~v7_waybel_0(X0) | ~l1_waybel_0(X0,sK0) | ~m1_subset_1(X2,u1_struct_0(sK0)) | r3_orders_2(sK0,X2,X1) | ~r3_waybel_9(sK0,X0,X2) | ~m1_subset_1(X1,u1_struct_0(sK0)))),
% 0.22/0.53    introduced(avatar_definition,[new_symbols(naming,[spl9_32])])).
% 0.22/0.53  fof(f269,plain,(
% 0.22/0.53    ( ! [X0,X1] : (v2_struct_0(sK1) | ~v4_orders_2(sK1) | ~r2_lattice3(sK0,k2_relset_1(u1_struct_0(sK1),u1_struct_0(sK0),u1_waybel_0(sK0,sK1)),X0) | ~l1_waybel_0(sK1,sK0) | ~m1_subset_1(X1,u1_struct_0(sK0)) | r3_orders_2(sK0,X1,X0) | ~r3_waybel_9(sK0,sK1,X1) | ~m1_subset_1(X0,u1_struct_0(sK0))) ) | (~spl9_5 | ~spl9_32)),
% 0.22/0.53    inference(resolution,[],[f267,f129])).
% 0.22/0.53  fof(f129,plain,(
% 0.22/0.53    v7_waybel_0(sK1) | ~spl9_5),
% 0.22/0.53    inference(avatar_component_clause,[],[f128])).
% 0.22/0.53  fof(f267,plain,(
% 0.22/0.53    ( ! [X2,X0,X1] : (~v7_waybel_0(X0) | v2_struct_0(X0) | ~v4_orders_2(X0) | ~r2_lattice3(sK0,k2_relset_1(u1_struct_0(X0),u1_struct_0(sK0),u1_waybel_0(sK0,X0)),X1) | ~l1_waybel_0(X0,sK0) | ~m1_subset_1(X2,u1_struct_0(sK0)) | r3_orders_2(sK0,X2,X1) | ~r3_waybel_9(sK0,X0,X2) | ~m1_subset_1(X1,u1_struct_0(sK0))) ) | ~spl9_32),
% 0.22/0.53    inference(avatar_component_clause,[],[f266])).
% 0.22/0.53  fof(f268,plain,(
% 0.22/0.53    ~spl9_16 | ~spl9_15 | ~spl9_14 | ~spl9_13 | ~spl9_12 | ~spl9_11 | ~spl9_10 | ~spl9_9 | ~spl9_8 | spl9_32 | spl9_31),
% 0.22/0.53    inference(avatar_split_clause,[],[f264,f261,f266,f140,f144,f148,f152,f156,f160,f164,f168,f172])).
% 0.22/0.53  fof(f261,plain,(
% 0.22/0.53    spl9_31 <=> m1_subset_1(sK8(sK0),u1_struct_0(sK0))),
% 0.22/0.53    introduced(avatar_definition,[new_symbols(naming,[spl9_31])])).
% 0.22/0.53  fof(f264,plain,(
% 0.22/0.53    ( ! [X2,X0,X1] : (~r2_lattice3(sK0,k2_relset_1(u1_struct_0(X0),u1_struct_0(sK0),u1_waybel_0(sK0,X0)),X1) | ~m1_subset_1(X1,u1_struct_0(sK0)) | ~r3_waybel_9(sK0,X0,X2) | r3_orders_2(sK0,X2,X1) | ~m1_subset_1(X2,u1_struct_0(sK0)) | ~l1_waybel_0(X0,sK0) | ~v7_waybel_0(X0) | ~v4_orders_2(X0) | v2_struct_0(X0) | ~l1_waybel_9(sK0) | ~v1_compts_1(sK0) | ~v2_lattice3(sK0) | ~v1_lattice3(sK0) | ~v5_orders_2(sK0) | ~v4_orders_2(sK0) | ~v3_orders_2(sK0) | ~v8_pre_topc(sK0) | ~v2_pre_topc(sK0)) ) | spl9_31),
% 0.22/0.53    inference(resolution,[],[f262,f108])).
% 0.22/0.53  fof(f108,plain,(
% 0.22/0.53    ( ! [X4,X0,X3,X1] : (m1_subset_1(sK8(X0),u1_struct_0(X0)) | ~r2_lattice3(X0,k2_relset_1(u1_struct_0(X1),u1_struct_0(X0),u1_waybel_0(X0,X1)),X4) | ~m1_subset_1(X4,u1_struct_0(X0)) | ~r3_waybel_9(X0,X1,X3) | r3_orders_2(X0,X3,X4) | ~m1_subset_1(X3,u1_struct_0(X0)) | ~l1_waybel_0(X1,X0) | ~v7_waybel_0(X1) | ~v4_orders_2(X1) | v2_struct_0(X1) | ~l1_waybel_9(X0) | ~v1_compts_1(X0) | ~v2_lattice3(X0) | ~v1_lattice3(X0) | ~v5_orders_2(X0) | ~v4_orders_2(X0) | ~v3_orders_2(X0) | ~v8_pre_topc(X0) | ~v2_pre_topc(X0)) )),
% 0.22/0.53    inference(duplicate_literal_removal,[],[f107])).
% 0.22/0.53  fof(f107,plain,(
% 0.22/0.53    ( ! [X4,X0,X3,X1] : (r3_orders_2(X0,X3,X4) | ~r2_lattice3(X0,k2_relset_1(u1_struct_0(X1),u1_struct_0(X0),u1_waybel_0(X0,X1)),X4) | ~m1_subset_1(X4,u1_struct_0(X0)) | ~r3_waybel_9(X0,X1,X3) | m1_subset_1(sK8(X0),u1_struct_0(X0)) | ~m1_subset_1(X3,u1_struct_0(X0)) | ~m1_subset_1(X3,u1_struct_0(X0)) | ~l1_waybel_0(X1,X0) | ~v7_waybel_0(X1) | ~v4_orders_2(X1) | v2_struct_0(X1) | ~l1_waybel_9(X0) | ~v1_compts_1(X0) | ~v2_lattice3(X0) | ~v1_lattice3(X0) | ~v5_orders_2(X0) | ~v4_orders_2(X0) | ~v3_orders_2(X0) | ~v8_pre_topc(X0) | ~v2_pre_topc(X0)) )),
% 0.22/0.53    inference(equality_resolution,[],[f98])).
% 0.22/0.53  fof(f98,plain,(
% 0.22/0.53    ( ! [X4,X2,X0,X3,X1] : (r3_orders_2(X0,X3,X4) | ~r2_lattice3(X0,k2_relset_1(u1_struct_0(X1),u1_struct_0(X0),u1_waybel_0(X0,X1)),X4) | ~m1_subset_1(X4,u1_struct_0(X0)) | ~r3_waybel_9(X0,X1,X2) | m1_subset_1(sK8(X0),u1_struct_0(X0)) | X2 != X3 | ~m1_subset_1(X3,u1_struct_0(X0)) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~l1_waybel_0(X1,X0) | ~v7_waybel_0(X1) | ~v4_orders_2(X1) | v2_struct_0(X1) | ~l1_waybel_9(X0) | ~v1_compts_1(X0) | ~v2_lattice3(X0) | ~v1_lattice3(X0) | ~v5_orders_2(X0) | ~v4_orders_2(X0) | ~v3_orders_2(X0) | ~v8_pre_topc(X0) | ~v2_pre_topc(X0)) )),
% 0.22/0.53    inference(cnf_transformation,[],[f56])).
% 0.22/0.53  fof(f56,plain,(
% 0.22/0.53    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (! [X4] : (r3_orders_2(X0,X3,X4) | ~r2_lattice3(X0,k2_relset_1(u1_struct_0(X1),u1_struct_0(X0),u1_waybel_0(X0,X1)),X4) | ~m1_subset_1(X4,u1_struct_0(X0))) | ~r3_waybel_9(X0,X1,X2) | (~v5_pre_topc(k4_waybel_1(X0,sK8(X0)),X0,X0) & m1_subset_1(sK8(X0),u1_struct_0(X0))) | X2 != X3 | ~m1_subset_1(X3,u1_struct_0(X0))) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~l1_waybel_0(X1,X0) | ~v7_waybel_0(X1) | ~v4_orders_2(X1) | v2_struct_0(X1)) | ~l1_waybel_9(X0) | ~v1_compts_1(X0) | ~v2_lattice3(X0) | ~v1_lattice3(X0) | ~v5_orders_2(X0) | ~v4_orders_2(X0) | ~v3_orders_2(X0) | ~v8_pre_topc(X0) | ~v2_pre_topc(X0))),
% 0.22/0.53    inference(skolemisation,[status(esa),new_symbols(skolem,[sK8])],[f54,f55])).
% 0.22/0.53  fof(f55,plain,(
% 0.22/0.53    ! [X0] : (? [X5] : (~v5_pre_topc(k4_waybel_1(X0,X5),X0,X0) & m1_subset_1(X5,u1_struct_0(X0))) => (~v5_pre_topc(k4_waybel_1(X0,sK8(X0)),X0,X0) & m1_subset_1(sK8(X0),u1_struct_0(X0))))),
% 0.22/0.53    introduced(choice_axiom,[])).
% 0.22/0.53  fof(f54,plain,(
% 0.22/0.53    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (! [X4] : (r3_orders_2(X0,X3,X4) | ~r2_lattice3(X0,k2_relset_1(u1_struct_0(X1),u1_struct_0(X0),u1_waybel_0(X0,X1)),X4) | ~m1_subset_1(X4,u1_struct_0(X0))) | ~r3_waybel_9(X0,X1,X2) | ? [X5] : (~v5_pre_topc(k4_waybel_1(X0,X5),X0,X0) & m1_subset_1(X5,u1_struct_0(X0))) | X2 != X3 | ~m1_subset_1(X3,u1_struct_0(X0))) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~l1_waybel_0(X1,X0) | ~v7_waybel_0(X1) | ~v4_orders_2(X1) | v2_struct_0(X1)) | ~l1_waybel_9(X0) | ~v1_compts_1(X0) | ~v2_lattice3(X0) | ~v1_lattice3(X0) | ~v5_orders_2(X0) | ~v4_orders_2(X0) | ~v3_orders_2(X0) | ~v8_pre_topc(X0) | ~v2_pre_topc(X0))),
% 0.22/0.53    inference(rectify,[],[f34])).
% 0.22/0.53  fof(f34,plain,(
% 0.22/0.53    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (! [X5] : (r3_orders_2(X0,X3,X5) | ~r2_lattice3(X0,k2_relset_1(u1_struct_0(X1),u1_struct_0(X0),u1_waybel_0(X0,X1)),X5) | ~m1_subset_1(X5,u1_struct_0(X0))) | ~r3_waybel_9(X0,X1,X2) | ? [X4] : (~v5_pre_topc(k4_waybel_1(X0,X4),X0,X0) & m1_subset_1(X4,u1_struct_0(X0))) | X2 != X3 | ~m1_subset_1(X3,u1_struct_0(X0))) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~l1_waybel_0(X1,X0) | ~v7_waybel_0(X1) | ~v4_orders_2(X1) | v2_struct_0(X1)) | ~l1_waybel_9(X0) | ~v1_compts_1(X0) | ~v2_lattice3(X0) | ~v1_lattice3(X0) | ~v5_orders_2(X0) | ~v4_orders_2(X0) | ~v3_orders_2(X0) | ~v8_pre_topc(X0) | ~v2_pre_topc(X0))),
% 0.22/0.53    inference(flattening,[],[f33])).
% 0.22/0.54  fof(f33,plain,(
% 0.22/0.54    ! [X0] : (! [X1] : (! [X2] : (! [X3] : ((! [X5] : ((r3_orders_2(X0,X3,X5) | ~r2_lattice3(X0,k2_relset_1(u1_struct_0(X1),u1_struct_0(X0),u1_waybel_0(X0,X1)),X5)) | ~m1_subset_1(X5,u1_struct_0(X0))) | (~r3_waybel_9(X0,X1,X2) | ? [X4] : (~v5_pre_topc(k4_waybel_1(X0,X4),X0,X0) & m1_subset_1(X4,u1_struct_0(X0))) | X2 != X3)) | ~m1_subset_1(X3,u1_struct_0(X0))) | ~m1_subset_1(X2,u1_struct_0(X0))) | (~l1_waybel_0(X1,X0) | ~v7_waybel_0(X1) | ~v4_orders_2(X1) | v2_struct_0(X1))) | (~l1_waybel_9(X0) | ~v1_compts_1(X0) | ~v2_lattice3(X0) | ~v1_lattice3(X0) | ~v5_orders_2(X0) | ~v4_orders_2(X0) | ~v3_orders_2(X0) | ~v8_pre_topc(X0) | ~v2_pre_topc(X0)))),
% 0.22/0.54    inference(ennf_transformation,[],[f16])).
% 0.22/0.54  fof(f16,plain,(
% 0.22/0.54    ! [X0] : ((l1_waybel_9(X0) & v1_compts_1(X0) & v2_lattice3(X0) & v1_lattice3(X0) & v5_orders_2(X0) & v4_orders_2(X0) & v3_orders_2(X0) & v8_pre_topc(X0) & v2_pre_topc(X0)) => ! [X1] : ((l1_waybel_0(X1,X0) & v7_waybel_0(X1) & v4_orders_2(X1) & ~v2_struct_0(X1)) => ! [X2] : (m1_subset_1(X2,u1_struct_0(X0)) => ! [X3] : (m1_subset_1(X3,u1_struct_0(X0)) => ((r3_waybel_9(X0,X1,X2) & ! [X4] : (m1_subset_1(X4,u1_struct_0(X0)) => v5_pre_topc(k4_waybel_1(X0,X4),X0,X0)) & X2 = X3) => ! [X5] : (m1_subset_1(X5,u1_struct_0(X0)) => (r2_lattice3(X0,k2_relset_1(u1_struct_0(X1),u1_struct_0(X0),u1_waybel_0(X0,X1)),X5) => r3_orders_2(X0,X3,X5))))))))),
% 0.22/0.54    inference(rectify,[],[f7])).
% 0.22/0.54  fof(f7,axiom,(
% 0.22/0.54    ! [X0] : ((l1_waybel_9(X0) & v1_compts_1(X0) & v2_lattice3(X0) & v1_lattice3(X0) & v5_orders_2(X0) & v4_orders_2(X0) & v3_orders_2(X0) & v8_pre_topc(X0) & v2_pre_topc(X0)) => ! [X1] : ((l1_waybel_0(X1,X0) & v7_waybel_0(X1) & v4_orders_2(X1) & ~v2_struct_0(X1)) => ! [X2] : (m1_subset_1(X2,u1_struct_0(X0)) => ! [X3] : (m1_subset_1(X3,u1_struct_0(X0)) => ((r3_waybel_9(X0,X1,X2) & ! [X4] : (m1_subset_1(X4,u1_struct_0(X0)) => v5_pre_topc(k4_waybel_1(X0,X4),X0,X0)) & X2 = X3) => ! [X4] : (m1_subset_1(X4,u1_struct_0(X0)) => (r2_lattice3(X0,k2_relset_1(u1_struct_0(X1),u1_struct_0(X0),u1_waybel_0(X0,X1)),X4) => r3_orders_2(X0,X3,X4))))))))),
% 0.22/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l49_waybel_9)).
% 0.22/0.54  fof(f262,plain,(
% 0.22/0.54    ~m1_subset_1(sK8(sK0),u1_struct_0(sK0)) | spl9_31),
% 0.22/0.54    inference(avatar_component_clause,[],[f261])).
% 0.22/0.54  fof(f263,plain,(
% 0.22/0.54    ~spl9_31 | spl9_29),
% 0.22/0.54    inference(avatar_split_clause,[],[f259,f253,f261])).
% 0.22/0.54  fof(f253,plain,(
% 0.22/0.54    spl9_29 <=> v5_pre_topc(k4_waybel_1(sK0,sK8(sK0)),sK0,sK0)),
% 0.22/0.54    introduced(avatar_definition,[new_symbols(naming,[spl9_29])])).
% 0.22/0.54  fof(f259,plain,(
% 0.22/0.54    ~m1_subset_1(sK8(sK0),u1_struct_0(sK0)) | spl9_29),
% 0.22/0.54    inference(resolution,[],[f254,f67])).
% 0.22/0.54  fof(f254,plain,(
% 0.22/0.54    ~v5_pre_topc(k4_waybel_1(sK0,sK8(sK0)),sK0,sK0) | spl9_29),
% 0.22/0.54    inference(avatar_component_clause,[],[f253])).
% 0.22/0.54  fof(f258,plain,(
% 0.22/0.54    ~spl9_29 | ~spl9_4 | ~spl9_8 | spl9_30 | ~spl9_10 | ~spl9_11 | ~spl9_12 | ~spl9_13 | ~spl9_14 | ~spl9_15 | ~spl9_16 | ~spl9_9 | ~spl9_28),
% 0.22/0.54    inference(avatar_split_clause,[],[f251,f248,f144,f172,f168,f164,f160,f156,f152,f148,f256,f140,f124,f253])).
% 0.22/0.54  fof(f248,plain,(
% 0.22/0.54    spl9_28 <=> ! [X1,X0,X2] : (~r2_lattice3(X0,k2_relset_1(u1_struct_0(sK1),u1_struct_0(X0),u1_waybel_0(X0,sK1)),X1) | ~v2_pre_topc(X0) | ~v8_pre_topc(X0) | ~v3_orders_2(X0) | ~v4_orders_2(X0) | ~v5_orders_2(X0) | ~v1_lattice3(X0) | ~v2_lattice3(X0) | ~v1_compts_1(X0) | ~l1_waybel_9(X0) | r3_orders_2(X0,X2,X1) | ~l1_waybel_0(sK1,X0) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~v5_pre_topc(k4_waybel_1(X0,sK8(X0)),X0,X0) | ~r3_waybel_9(X0,sK1,X2) | ~m1_subset_1(X1,u1_struct_0(X0)))),
% 0.22/0.54    introduced(avatar_definition,[new_symbols(naming,[spl9_28])])).
% 0.22/0.54  fof(f251,plain,(
% 0.22/0.54    ( ! [X0,X1] : (~v2_pre_topc(sK0) | ~v8_pre_topc(sK0) | ~v3_orders_2(sK0) | ~v4_orders_2(sK0) | ~v5_orders_2(sK0) | ~v1_lattice3(sK0) | ~v2_lattice3(sK0) | ~r2_lattice3(sK0,k2_relset_1(u1_struct_0(sK1),u1_struct_0(sK0),u1_waybel_0(sK0,sK1)),X0) | ~l1_waybel_9(sK0) | r3_orders_2(sK0,X1,X0) | ~l1_waybel_0(sK1,sK0) | ~m1_subset_1(X1,u1_struct_0(sK0)) | ~v5_pre_topc(k4_waybel_1(sK0,sK8(sK0)),sK0,sK0) | ~r3_waybel_9(sK0,sK1,X1) | ~m1_subset_1(X0,u1_struct_0(sK0))) ) | (~spl9_9 | ~spl9_28)),
% 0.22/0.54    inference(resolution,[],[f249,f145])).
% 0.22/0.54  fof(f145,plain,(
% 0.22/0.54    v1_compts_1(sK0) | ~spl9_9),
% 0.22/0.54    inference(avatar_component_clause,[],[f144])).
% 0.22/0.54  fof(f249,plain,(
% 0.22/0.54    ( ! [X2,X0,X1] : (~v1_compts_1(X0) | ~v2_pre_topc(X0) | ~v8_pre_topc(X0) | ~v3_orders_2(X0) | ~v4_orders_2(X0) | ~v5_orders_2(X0) | ~v1_lattice3(X0) | ~v2_lattice3(X0) | ~r2_lattice3(X0,k2_relset_1(u1_struct_0(sK1),u1_struct_0(X0),u1_waybel_0(X0,sK1)),X1) | ~l1_waybel_9(X0) | r3_orders_2(X0,X2,X1) | ~l1_waybel_0(sK1,X0) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~v5_pre_topc(k4_waybel_1(X0,sK8(X0)),X0,X0) | ~r3_waybel_9(X0,sK1,X2) | ~m1_subset_1(X1,u1_struct_0(X0))) ) | ~spl9_28),
% 0.22/0.54    inference(avatar_component_clause,[],[f248])).
% 0.22/0.54  fof(f250,plain,(
% 0.22/0.54    spl9_7 | ~spl9_6 | spl9_28 | ~spl9_5),
% 0.22/0.54    inference(avatar_split_clause,[],[f246,f128,f248,f132,f136])).
% 0.22/0.54  fof(f246,plain,(
% 0.22/0.54    ( ! [X2,X0,X1] : (~r2_lattice3(X0,k2_relset_1(u1_struct_0(sK1),u1_struct_0(X0),u1_waybel_0(X0,sK1)),X1) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~r3_waybel_9(X0,sK1,X2) | ~v5_pre_topc(k4_waybel_1(X0,sK8(X0)),X0,X0) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~l1_waybel_0(sK1,X0) | r3_orders_2(X0,X2,X1) | ~v4_orders_2(sK1) | v2_struct_0(sK1) | ~l1_waybel_9(X0) | ~v1_compts_1(X0) | ~v2_lattice3(X0) | ~v1_lattice3(X0) | ~v5_orders_2(X0) | ~v4_orders_2(X0) | ~v3_orders_2(X0) | ~v8_pre_topc(X0) | ~v2_pre_topc(X0)) ) | ~spl9_5),
% 0.22/0.54    inference(resolution,[],[f109,f129])).
% 0.22/0.54  fof(f109,plain,(
% 0.22/0.54    ( ! [X4,X0,X3,X1] : (~v7_waybel_0(X1) | ~r2_lattice3(X0,k2_relset_1(u1_struct_0(X1),u1_struct_0(X0),u1_waybel_0(X0,X1)),X4) | ~m1_subset_1(X4,u1_struct_0(X0)) | ~r3_waybel_9(X0,X1,X3) | ~v5_pre_topc(k4_waybel_1(X0,sK8(X0)),X0,X0) | ~m1_subset_1(X3,u1_struct_0(X0)) | ~l1_waybel_0(X1,X0) | r3_orders_2(X0,X3,X4) | ~v4_orders_2(X1) | v2_struct_0(X1) | ~l1_waybel_9(X0) | ~v1_compts_1(X0) | ~v2_lattice3(X0) | ~v1_lattice3(X0) | ~v5_orders_2(X0) | ~v4_orders_2(X0) | ~v3_orders_2(X0) | ~v8_pre_topc(X0) | ~v2_pre_topc(X0)) )),
% 0.22/0.54    inference(duplicate_literal_removal,[],[f106])).
% 0.22/0.54  fof(f106,plain,(
% 0.22/0.54    ( ! [X4,X0,X3,X1] : (r3_orders_2(X0,X3,X4) | ~r2_lattice3(X0,k2_relset_1(u1_struct_0(X1),u1_struct_0(X0),u1_waybel_0(X0,X1)),X4) | ~m1_subset_1(X4,u1_struct_0(X0)) | ~r3_waybel_9(X0,X1,X3) | ~v5_pre_topc(k4_waybel_1(X0,sK8(X0)),X0,X0) | ~m1_subset_1(X3,u1_struct_0(X0)) | ~m1_subset_1(X3,u1_struct_0(X0)) | ~l1_waybel_0(X1,X0) | ~v7_waybel_0(X1) | ~v4_orders_2(X1) | v2_struct_0(X1) | ~l1_waybel_9(X0) | ~v1_compts_1(X0) | ~v2_lattice3(X0) | ~v1_lattice3(X0) | ~v5_orders_2(X0) | ~v4_orders_2(X0) | ~v3_orders_2(X0) | ~v8_pre_topc(X0) | ~v2_pre_topc(X0)) )),
% 0.22/0.54    inference(equality_resolution,[],[f99])).
% 0.22/0.54  fof(f99,plain,(
% 0.22/0.54    ( ! [X4,X2,X0,X3,X1] : (r3_orders_2(X0,X3,X4) | ~r2_lattice3(X0,k2_relset_1(u1_struct_0(X1),u1_struct_0(X0),u1_waybel_0(X0,X1)),X4) | ~m1_subset_1(X4,u1_struct_0(X0)) | ~r3_waybel_9(X0,X1,X2) | ~v5_pre_topc(k4_waybel_1(X0,sK8(X0)),X0,X0) | X2 != X3 | ~m1_subset_1(X3,u1_struct_0(X0)) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~l1_waybel_0(X1,X0) | ~v7_waybel_0(X1) | ~v4_orders_2(X1) | v2_struct_0(X1) | ~l1_waybel_9(X0) | ~v1_compts_1(X0) | ~v2_lattice3(X0) | ~v1_lattice3(X0) | ~v5_orders_2(X0) | ~v4_orders_2(X0) | ~v3_orders_2(X0) | ~v8_pre_topc(X0) | ~v2_pre_topc(X0)) )),
% 0.22/0.54    inference(cnf_transformation,[],[f56])).
% 0.22/0.54  fof(f244,plain,(
% 0.22/0.54    spl9_22 | ~spl9_16 | ~spl9_15 | ~spl9_9 | ~spl9_23 | spl9_7 | ~spl9_6 | ~spl9_5 | ~spl9_4 | spl9_27 | ~spl9_24),
% 0.22/0.54    inference(avatar_split_clause,[],[f236,f225,f242,f124,f128,f132,f136,f222,f144,f168,f172,f219])).
% 0.22/0.54  fof(f236,plain,(
% 0.22/0.54    m1_subset_1(k1_waybel_2(sK0,sK1),u1_struct_0(sK0)) | ~l1_waybel_0(sK1,sK0) | ~v7_waybel_0(sK1) | ~v4_orders_2(sK1) | v2_struct_0(sK1) | ~l1_pre_topc(sK0) | ~v1_compts_1(sK0) | ~v8_pre_topc(sK0) | ~v2_pre_topc(sK0) | v2_struct_0(sK0) | ~spl9_24),
% 0.22/0.54    inference(superposition,[],[f84,f226])).
% 0.22/0.54  fof(f84,plain,(
% 0.22/0.54    ( ! [X0,X1] : (m1_subset_1(sK4(X0,X1),u1_struct_0(X0)) | ~l1_waybel_0(X1,X0) | ~v7_waybel_0(X1) | ~v4_orders_2(X1) | v2_struct_0(X1) | ~l1_pre_topc(X0) | ~v1_compts_1(X0) | ~v8_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 0.22/0.54    inference(cnf_transformation,[],[f47])).
% 0.22/0.54  fof(f240,plain,(
% 0.22/0.54    spl9_22 | ~spl9_16 | ~spl9_15 | ~spl9_9 | ~spl9_23 | spl9_7 | ~spl9_6 | ~spl9_5 | ~spl9_4 | spl9_26 | ~spl9_24),
% 0.22/0.54    inference(avatar_split_clause,[],[f235,f225,f238,f124,f128,f132,f136,f222,f144,f168,f172,f219])).
% 0.22/0.54  fof(f235,plain,(
% 0.22/0.54    r3_waybel_9(sK0,sK1,k1_waybel_2(sK0,sK1)) | ~l1_waybel_0(sK1,sK0) | ~v7_waybel_0(sK1) | ~v4_orders_2(sK1) | v2_struct_0(sK1) | ~l1_pre_topc(sK0) | ~v1_compts_1(sK0) | ~v8_pre_topc(sK0) | ~v2_pre_topc(sK0) | v2_struct_0(sK0) | ~spl9_24),
% 0.22/0.54    inference(superposition,[],[f85,f226])).
% 0.22/0.54  fof(f234,plain,(
% 0.22/0.54    spl9_22 | ~spl9_16 | ~spl9_15 | ~spl9_9 | ~spl9_23 | spl9_7 | ~spl9_6 | ~spl9_5 | ~spl9_4 | spl9_25),
% 0.22/0.54    inference(avatar_split_clause,[],[f233,f228,f124,f128,f132,f136,f222,f144,f168,f172,f219])).
% 0.22/0.54  fof(f228,plain,(
% 0.22/0.54    spl9_25 <=> m1_subset_1(sK4(sK0,sK1),u1_struct_0(sK0))),
% 0.22/0.54    introduced(avatar_definition,[new_symbols(naming,[spl9_25])])).
% 0.22/0.54  fof(f233,plain,(
% 0.22/0.54    ~l1_waybel_0(sK1,sK0) | ~v7_waybel_0(sK1) | ~v4_orders_2(sK1) | v2_struct_0(sK1) | ~l1_pre_topc(sK0) | ~v1_compts_1(sK0) | ~v8_pre_topc(sK0) | ~v2_pre_topc(sK0) | v2_struct_0(sK0) | spl9_25),
% 0.22/0.54    inference(resolution,[],[f229,f84])).
% 0.22/0.54  fof(f229,plain,(
% 0.22/0.54    ~m1_subset_1(sK4(sK0,sK1),u1_struct_0(sK0)) | spl9_25),
% 0.22/0.54    inference(avatar_component_clause,[],[f228])).
% 0.22/0.54  fof(f232,plain,(
% 0.22/0.54    ~spl9_8 | spl9_23),
% 0.22/0.54    inference(avatar_split_clause,[],[f231,f222,f140])).
% 0.22/0.54  fof(f231,plain,(
% 0.22/0.54    ~l1_waybel_9(sK0) | spl9_23),
% 0.22/0.54    inference(resolution,[],[f223,f74])).
% 0.22/0.54  fof(f74,plain,(
% 0.22/0.54    ( ! [X0] : (l1_pre_topc(X0) | ~l1_waybel_9(X0)) )),
% 0.22/0.54    inference(cnf_transformation,[],[f19])).
% 0.22/0.54  fof(f223,plain,(
% 0.22/0.54    ~l1_pre_topc(sK0) | spl9_23),
% 0.22/0.54    inference(avatar_component_clause,[],[f222])).
% 0.22/0.54  fof(f230,plain,(
% 0.22/0.54    spl9_22 | ~spl9_16 | ~spl9_15 | ~spl9_9 | ~spl9_23 | spl9_7 | ~spl9_6 | ~spl9_5 | ~spl9_4 | spl9_24 | ~spl9_25 | ~spl9_19),
% 0.22/0.54    inference(avatar_split_clause,[],[f217,f192,f228,f225,f124,f128,f132,f136,f222,f144,f168,f172,f219])).
% 0.22/0.54  fof(f217,plain,(
% 0.22/0.54    ~m1_subset_1(sK4(sK0,sK1),u1_struct_0(sK0)) | k1_waybel_2(sK0,sK1) = sK4(sK0,sK1) | ~l1_waybel_0(sK1,sK0) | ~v7_waybel_0(sK1) | ~v4_orders_2(sK1) | v2_struct_0(sK1) | ~l1_pre_topc(sK0) | ~v1_compts_1(sK0) | ~v8_pre_topc(sK0) | ~v2_pre_topc(sK0) | v2_struct_0(sK0) | ~spl9_19),
% 0.22/0.54    inference(resolution,[],[f193,f85])).
% 0.22/0.54  fof(f216,plain,(
% 0.22/0.54    ~spl9_4 | ~spl9_5 | ~spl9_6 | spl9_7 | spl9_19 | ~spl9_3 | ~spl9_21),
% 0.22/0.54    inference(avatar_split_clause,[],[f214,f211,f120,f192,f136,f132,f128,f124])).
% 0.22/0.54  fof(f211,plain,(
% 0.22/0.54    spl9_21 <=> ! [X1,X0] : (~r3_waybel_9(sK0,X0,X1) | ~m1_subset_1(X1,u1_struct_0(sK0)) | v2_struct_0(X0) | ~v4_orders_2(X0) | ~v7_waybel_0(X0) | ~l1_waybel_0(X0,sK0) | k1_waybel_2(sK0,X0) = X1 | ~v10_waybel_0(X0,sK0))),
% 0.22/0.54    introduced(avatar_definition,[new_symbols(naming,[spl9_21])])).
% 0.22/0.54  fof(f214,plain,(
% 0.22/0.54    ( ! [X0] : (~m1_subset_1(X0,u1_struct_0(sK0)) | v2_struct_0(sK1) | ~v4_orders_2(sK1) | ~v7_waybel_0(sK1) | ~l1_waybel_0(sK1,sK0) | k1_waybel_2(sK0,sK1) = X0 | ~r3_waybel_9(sK0,sK1,X0)) ) | (~spl9_3 | ~spl9_21)),
% 0.22/0.54    inference(resolution,[],[f212,f121])).
% 0.22/0.54  fof(f212,plain,(
% 0.22/0.54    ( ! [X0,X1] : (~v10_waybel_0(X0,sK0) | ~m1_subset_1(X1,u1_struct_0(sK0)) | v2_struct_0(X0) | ~v4_orders_2(X0) | ~v7_waybel_0(X0) | ~l1_waybel_0(X0,sK0) | k1_waybel_2(sK0,X0) = X1 | ~r3_waybel_9(sK0,X0,X1)) ) | ~spl9_21),
% 0.22/0.54    inference(avatar_component_clause,[],[f211])).
% 0.22/0.54  fof(f213,plain,(
% 0.22/0.54    ~spl9_16 | ~spl9_15 | ~spl9_14 | ~spl9_13 | ~spl9_12 | ~spl9_11 | ~spl9_10 | ~spl9_9 | ~spl9_8 | spl9_21 | spl9_20),
% 0.22/0.54    inference(avatar_split_clause,[],[f209,f206,f211,f140,f144,f148,f152,f156,f160,f164,f168,f172])).
% 0.22/0.54  fof(f206,plain,(
% 0.22/0.54    spl9_20 <=> m1_subset_1(sK6(sK0),u1_struct_0(sK0))),
% 0.22/0.54    introduced(avatar_definition,[new_symbols(naming,[spl9_20])])).
% 0.22/0.54  fof(f209,plain,(
% 0.22/0.54    ( ! [X0,X1] : (~r3_waybel_9(sK0,X0,X1) | ~v10_waybel_0(X0,sK0) | k1_waybel_2(sK0,X0) = X1 | ~l1_waybel_0(X0,sK0) | ~v7_waybel_0(X0) | ~v4_orders_2(X0) | v2_struct_0(X0) | ~m1_subset_1(X1,u1_struct_0(sK0)) | ~l1_waybel_9(sK0) | ~v1_compts_1(sK0) | ~v2_lattice3(sK0) | ~v1_lattice3(sK0) | ~v5_orders_2(sK0) | ~v4_orders_2(sK0) | ~v3_orders_2(sK0) | ~v8_pre_topc(sK0) | ~v2_pre_topc(sK0)) ) | spl9_20),
% 0.22/0.54    inference(resolution,[],[f207,f94])).
% 0.22/0.54  fof(f94,plain,(
% 0.22/0.54    ( ! [X2,X0,X1] : (m1_subset_1(sK6(X0),u1_struct_0(X0)) | ~r3_waybel_9(X0,X2,X1) | ~v10_waybel_0(X2,X0) | k1_waybel_2(X0,X2) = X1 | ~l1_waybel_0(X2,X0) | ~v7_waybel_0(X2) | ~v4_orders_2(X2) | v2_struct_0(X2) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_waybel_9(X0) | ~v1_compts_1(X0) | ~v2_lattice3(X0) | ~v1_lattice3(X0) | ~v5_orders_2(X0) | ~v4_orders_2(X0) | ~v3_orders_2(X0) | ~v8_pre_topc(X0) | ~v2_pre_topc(X0)) )),
% 0.22/0.54    inference(cnf_transformation,[],[f51])).
% 0.22/0.54  fof(f51,plain,(
% 0.22/0.54    ! [X0] : (! [X1] : (! [X2] : (k1_waybel_2(X0,X2) = X1 | ~r3_waybel_9(X0,X2,X1) | ~v10_waybel_0(X2,X0) | (~v5_pre_topc(k4_waybel_1(X0,sK6(X0)),X0,X0) & m1_subset_1(sK6(X0),u1_struct_0(X0))) | ~l1_waybel_0(X2,X0) | ~v7_waybel_0(X2) | ~v4_orders_2(X2) | v2_struct_0(X2)) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~l1_waybel_9(X0) | ~v1_compts_1(X0) | ~v2_lattice3(X0) | ~v1_lattice3(X0) | ~v5_orders_2(X0) | ~v4_orders_2(X0) | ~v3_orders_2(X0) | ~v8_pre_topc(X0) | ~v2_pre_topc(X0))),
% 0.22/0.54    inference(skolemisation,[status(esa),new_symbols(skolem,[sK6])],[f30,f50])).
% 0.22/0.54  fof(f50,plain,(
% 0.22/0.54    ! [X0] : (? [X3] : (~v5_pre_topc(k4_waybel_1(X0,X3),X0,X0) & m1_subset_1(X3,u1_struct_0(X0))) => (~v5_pre_topc(k4_waybel_1(X0,sK6(X0)),X0,X0) & m1_subset_1(sK6(X0),u1_struct_0(X0))))),
% 0.22/0.54    introduced(choice_axiom,[])).
% 0.22/0.54  fof(f30,plain,(
% 0.22/0.54    ! [X0] : (! [X1] : (! [X2] : (k1_waybel_2(X0,X2) = X1 | ~r3_waybel_9(X0,X2,X1) | ~v10_waybel_0(X2,X0) | ? [X3] : (~v5_pre_topc(k4_waybel_1(X0,X3),X0,X0) & m1_subset_1(X3,u1_struct_0(X0))) | ~l1_waybel_0(X2,X0) | ~v7_waybel_0(X2) | ~v4_orders_2(X2) | v2_struct_0(X2)) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~l1_waybel_9(X0) | ~v1_compts_1(X0) | ~v2_lattice3(X0) | ~v1_lattice3(X0) | ~v5_orders_2(X0) | ~v4_orders_2(X0) | ~v3_orders_2(X0) | ~v8_pre_topc(X0) | ~v2_pre_topc(X0))),
% 0.22/0.54    inference(flattening,[],[f29])).
% 0.22/0.54  fof(f29,plain,(
% 0.22/0.54    ! [X0] : (! [X1] : (! [X2] : ((k1_waybel_2(X0,X2) = X1 | (~r3_waybel_9(X0,X2,X1) | ~v10_waybel_0(X2,X0) | ? [X3] : (~v5_pre_topc(k4_waybel_1(X0,X3),X0,X0) & m1_subset_1(X3,u1_struct_0(X0))))) | (~l1_waybel_0(X2,X0) | ~v7_waybel_0(X2) | ~v4_orders_2(X2) | v2_struct_0(X2))) | ~m1_subset_1(X1,u1_struct_0(X0))) | (~l1_waybel_9(X0) | ~v1_compts_1(X0) | ~v2_lattice3(X0) | ~v1_lattice3(X0) | ~v5_orders_2(X0) | ~v4_orders_2(X0) | ~v3_orders_2(X0) | ~v8_pre_topc(X0) | ~v2_pre_topc(X0)))),
% 0.22/0.54    inference(ennf_transformation,[],[f10])).
% 0.22/0.54  fof(f10,axiom,(
% 0.22/0.54    ! [X0] : ((l1_waybel_9(X0) & v1_compts_1(X0) & v2_lattice3(X0) & v1_lattice3(X0) & v5_orders_2(X0) & v4_orders_2(X0) & v3_orders_2(X0) & v8_pre_topc(X0) & v2_pre_topc(X0)) => ! [X1] : (m1_subset_1(X1,u1_struct_0(X0)) => ! [X2] : ((l1_waybel_0(X2,X0) & v7_waybel_0(X2) & v4_orders_2(X2) & ~v2_struct_0(X2)) => ((r3_waybel_9(X0,X2,X1) & v10_waybel_0(X2,X0) & ! [X3] : (m1_subset_1(X3,u1_struct_0(X0)) => v5_pre_topc(k4_waybel_1(X0,X3),X0,X0))) => k1_waybel_2(X0,X2) = X1))))),
% 0.22/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t35_waybel_9)).
% 0.22/0.54  fof(f207,plain,(
% 0.22/0.54    ~m1_subset_1(sK6(sK0),u1_struct_0(sK0)) | spl9_20),
% 0.22/0.54    inference(avatar_component_clause,[],[f206])).
% 0.22/0.54  fof(f208,plain,(
% 0.22/0.54    ~spl9_20 | spl9_18),
% 0.22/0.54    inference(avatar_split_clause,[],[f204,f188,f206])).
% 0.22/0.54  fof(f188,plain,(
% 0.22/0.54    spl9_18 <=> v5_pre_topc(k4_waybel_1(sK0,sK6(sK0)),sK0,sK0)),
% 0.22/0.54    introduced(avatar_definition,[new_symbols(naming,[spl9_18])])).
% 0.22/0.54  fof(f204,plain,(
% 0.22/0.54    ~m1_subset_1(sK6(sK0),u1_struct_0(sK0)) | spl9_18),
% 0.22/0.54    inference(resolution,[],[f189,f67])).
% 0.22/0.54  fof(f189,plain,(
% 0.22/0.54    ~v5_pre_topc(k4_waybel_1(sK0,sK6(sK0)),sK0,sK0) | spl9_18),
% 0.22/0.54    inference(avatar_component_clause,[],[f188])).
% 0.22/0.54  fof(f203,plain,(
% 0.22/0.54    ~spl9_18 | ~spl9_4 | spl9_19 | ~spl9_8 | ~spl9_9 | ~spl9_10 | ~spl9_11 | ~spl9_12 | ~spl9_13 | ~spl9_14 | ~spl9_15 | ~spl9_16 | ~spl9_3 | ~spl9_17),
% 0.22/0.54    inference(avatar_split_clause,[],[f186,f183,f120,f172,f168,f164,f160,f156,f152,f148,f144,f140,f192,f124,f188])).
% 0.22/0.54  fof(f183,plain,(
% 0.22/0.54    spl9_17 <=> ! [X1,X0] : (~r3_waybel_9(X0,sK1,X1) | ~v2_pre_topc(X0) | ~v8_pre_topc(X0) | ~v3_orders_2(X0) | ~v4_orders_2(X0) | ~v5_orders_2(X0) | ~v1_lattice3(X0) | ~v2_lattice3(X0) | ~v1_compts_1(X0) | ~l1_waybel_9(X0) | ~m1_subset_1(X1,u1_struct_0(X0)) | k1_waybel_2(X0,sK1) = X1 | ~l1_waybel_0(sK1,X0) | ~v5_pre_topc(k4_waybel_1(X0,sK6(X0)),X0,X0) | ~v10_waybel_0(sK1,X0))),
% 0.22/0.54    introduced(avatar_definition,[new_symbols(naming,[spl9_17])])).
% 0.22/0.54  fof(f186,plain,(
% 0.22/0.54    ( ! [X0] : (~v2_pre_topc(sK0) | ~v8_pre_topc(sK0) | ~v3_orders_2(sK0) | ~v4_orders_2(sK0) | ~v5_orders_2(sK0) | ~v1_lattice3(sK0) | ~v2_lattice3(sK0) | ~v1_compts_1(sK0) | ~l1_waybel_9(sK0) | ~m1_subset_1(X0,u1_struct_0(sK0)) | k1_waybel_2(sK0,sK1) = X0 | ~l1_waybel_0(sK1,sK0) | ~v5_pre_topc(k4_waybel_1(sK0,sK6(sK0)),sK0,sK0) | ~r3_waybel_9(sK0,sK1,X0)) ) | (~spl9_3 | ~spl9_17)),
% 0.22/0.54    inference(resolution,[],[f184,f121])).
% 0.22/0.54  fof(f184,plain,(
% 0.22/0.54    ( ! [X0,X1] : (~v10_waybel_0(sK1,X0) | ~v2_pre_topc(X0) | ~v8_pre_topc(X0) | ~v3_orders_2(X0) | ~v4_orders_2(X0) | ~v5_orders_2(X0) | ~v1_lattice3(X0) | ~v2_lattice3(X0) | ~v1_compts_1(X0) | ~l1_waybel_9(X0) | ~m1_subset_1(X1,u1_struct_0(X0)) | k1_waybel_2(X0,sK1) = X1 | ~l1_waybel_0(sK1,X0) | ~v5_pre_topc(k4_waybel_1(X0,sK6(X0)),X0,X0) | ~r3_waybel_9(X0,sK1,X1)) ) | ~spl9_17),
% 0.22/0.54    inference(avatar_component_clause,[],[f183])).
% 0.22/0.54  fof(f185,plain,(
% 0.22/0.54    spl9_7 | ~spl9_6 | spl9_17 | ~spl9_5),
% 0.22/0.54    inference(avatar_split_clause,[],[f179,f128,f183,f132,f136])).
% 0.22/0.54  fof(f179,plain,(
% 0.22/0.54    ( ! [X0,X1] : (~r3_waybel_9(X0,sK1,X1) | ~v10_waybel_0(sK1,X0) | ~v5_pre_topc(k4_waybel_1(X0,sK6(X0)),X0,X0) | ~l1_waybel_0(sK1,X0) | k1_waybel_2(X0,sK1) = X1 | ~v4_orders_2(sK1) | v2_struct_0(sK1) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_waybel_9(X0) | ~v1_compts_1(X0) | ~v2_lattice3(X0) | ~v1_lattice3(X0) | ~v5_orders_2(X0) | ~v4_orders_2(X0) | ~v3_orders_2(X0) | ~v8_pre_topc(X0) | ~v2_pre_topc(X0)) ) | ~spl9_5),
% 0.22/0.54    inference(resolution,[],[f95,f129])).
% 0.22/0.54  fof(f95,plain,(
% 0.22/0.54    ( ! [X2,X0,X1] : (~v7_waybel_0(X2) | ~r3_waybel_9(X0,X2,X1) | ~v10_waybel_0(X2,X0) | ~v5_pre_topc(k4_waybel_1(X0,sK6(X0)),X0,X0) | ~l1_waybel_0(X2,X0) | k1_waybel_2(X0,X2) = X1 | ~v4_orders_2(X2) | v2_struct_0(X2) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_waybel_9(X0) | ~v1_compts_1(X0) | ~v2_lattice3(X0) | ~v1_lattice3(X0) | ~v5_orders_2(X0) | ~v4_orders_2(X0) | ~v3_orders_2(X0) | ~v8_pre_topc(X0) | ~v2_pre_topc(X0)) )),
% 0.22/0.54    inference(cnf_transformation,[],[f51])).
% 0.22/0.54  fof(f174,plain,(
% 0.22/0.54    spl9_16),
% 0.22/0.54    inference(avatar_split_clause,[],[f58,f172])).
% 0.22/0.54  fof(f58,plain,(
% 0.22/0.54    v2_pre_topc(sK0)),
% 0.22/0.54    inference(cnf_transformation,[],[f40])).
% 0.22/0.54  fof(f170,plain,(
% 0.22/0.54    spl9_15),
% 0.22/0.54    inference(avatar_split_clause,[],[f59,f168])).
% 0.22/0.54  fof(f59,plain,(
% 0.22/0.54    v8_pre_topc(sK0)),
% 0.22/0.54    inference(cnf_transformation,[],[f40])).
% 0.22/0.54  fof(f166,plain,(
% 0.22/0.54    spl9_14),
% 0.22/0.54    inference(avatar_split_clause,[],[f60,f164])).
% 0.22/0.54  fof(f60,plain,(
% 0.22/0.54    v3_orders_2(sK0)),
% 0.22/0.54    inference(cnf_transformation,[],[f40])).
% 0.22/0.54  fof(f162,plain,(
% 0.22/0.54    spl9_13),
% 0.22/0.54    inference(avatar_split_clause,[],[f61,f160])).
% 0.22/0.54  fof(f61,plain,(
% 0.22/0.54    v4_orders_2(sK0)),
% 0.22/0.54    inference(cnf_transformation,[],[f40])).
% 0.22/0.54  fof(f158,plain,(
% 0.22/0.54    spl9_12),
% 0.22/0.54    inference(avatar_split_clause,[],[f62,f156])).
% 0.22/0.54  fof(f62,plain,(
% 0.22/0.54    v5_orders_2(sK0)),
% 0.22/0.54    inference(cnf_transformation,[],[f40])).
% 0.22/0.54  fof(f154,plain,(
% 0.22/0.54    spl9_11),
% 0.22/0.54    inference(avatar_split_clause,[],[f63,f152])).
% 0.22/0.54  fof(f63,plain,(
% 0.22/0.54    v1_lattice3(sK0)),
% 0.22/0.54    inference(cnf_transformation,[],[f40])).
% 0.22/0.54  fof(f150,plain,(
% 0.22/0.54    spl9_10),
% 0.22/0.54    inference(avatar_split_clause,[],[f64,f148])).
% 0.22/0.54  fof(f64,plain,(
% 0.22/0.54    v2_lattice3(sK0)),
% 0.22/0.54    inference(cnf_transformation,[],[f40])).
% 0.22/0.54  fof(f146,plain,(
% 0.22/0.54    spl9_9),
% 0.22/0.54    inference(avatar_split_clause,[],[f65,f144])).
% 0.22/0.54  fof(f65,plain,(
% 0.22/0.54    v1_compts_1(sK0)),
% 0.22/0.54    inference(cnf_transformation,[],[f40])).
% 0.22/0.54  fof(f142,plain,(
% 0.22/0.54    spl9_8),
% 0.22/0.54    inference(avatar_split_clause,[],[f66,f140])).
% 0.22/0.54  fof(f66,plain,(
% 0.22/0.54    l1_waybel_9(sK0)),
% 0.22/0.54    inference(cnf_transformation,[],[f40])).
% 0.22/0.54  fof(f138,plain,(
% 0.22/0.54    ~spl9_7),
% 0.22/0.54    inference(avatar_split_clause,[],[f68,f136])).
% 0.22/0.54  fof(f68,plain,(
% 0.22/0.54    ~v2_struct_0(sK1)),
% 0.22/0.54    inference(cnf_transformation,[],[f40])).
% 0.22/0.54  fof(f134,plain,(
% 0.22/0.54    spl9_6),
% 0.22/0.54    inference(avatar_split_clause,[],[f69,f132])).
% 0.22/0.54  fof(f69,plain,(
% 0.22/0.54    v4_orders_2(sK1)),
% 0.22/0.54    inference(cnf_transformation,[],[f40])).
% 0.22/0.54  fof(f130,plain,(
% 0.22/0.54    spl9_5),
% 0.22/0.54    inference(avatar_split_clause,[],[f70,f128])).
% 0.22/0.54  fof(f70,plain,(
% 0.22/0.54    v7_waybel_0(sK1)),
% 0.22/0.54    inference(cnf_transformation,[],[f40])).
% 0.22/0.54  fof(f126,plain,(
% 0.22/0.54    spl9_4),
% 0.22/0.54    inference(avatar_split_clause,[],[f71,f124])).
% 0.22/0.54  fof(f71,plain,(
% 0.22/0.54    l1_waybel_0(sK1,sK0)),
% 0.22/0.54    inference(cnf_transformation,[],[f40])).
% 0.22/0.54  fof(f122,plain,(
% 0.22/0.54    spl9_3),
% 0.22/0.54    inference(avatar_split_clause,[],[f72,f120])).
% 0.22/0.54  fof(f72,plain,(
% 0.22/0.54    v10_waybel_0(sK1,sK0)),
% 0.22/0.54    inference(cnf_transformation,[],[f40])).
% 0.22/0.54  fof(f118,plain,(
% 0.22/0.54    ~spl9_1 | ~spl9_2),
% 0.22/0.54    inference(avatar_split_clause,[],[f73,f116,f113])).
% 0.22/0.54  fof(f73,plain,(
% 0.22/0.54    ~r2_hidden(k1_waybel_2(sK0,sK1),k10_yellow_6(sK0,sK1)) | ~r1_waybel_9(sK0,sK1)),
% 0.22/0.54    inference(cnf_transformation,[],[f40])).
% 0.22/0.54  % SZS output end Proof for theBenchmark
% 0.22/0.54  % (3877)------------------------------
% 0.22/0.54  % (3877)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.54  % (3877)Termination reason: Refutation
% 0.22/0.54  
% 0.22/0.54  % (3877)Memory used [KB]: 11129
% 0.22/0.54  % (3877)Time elapsed: 0.107 s
% 0.22/0.54  % (3877)------------------------------
% 0.22/0.54  % (3877)------------------------------
% 1.45/0.54  % (3870)Success in time 0.17 s
%------------------------------------------------------------------------------
