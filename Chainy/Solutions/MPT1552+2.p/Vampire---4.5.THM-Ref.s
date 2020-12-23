%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT1552+2 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n002.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Wed Dec 16 12:10:24 EST 2020

% Result     : Theorem 1.72s
% Output     : Refutation 1.72s
% Verified   : 
% Statistics : Number of formulae       :  147 ( 402 expanded)
%              Number of leaves         :   29 ( 171 expanded)
%              Depth                    :   17
%              Number of atoms          :  808 (3087 expanded)
%              Number of equality atoms :   53 ( 314 expanded)
%              Maximal formula depth    :   14 (   6 average)
%              Maximal term depth       :    2 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f4105,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f3146,f3150,f3154,f3162,f3164,f3166,f3167,f3171,f3175,f3179,f3208,f3356,f3360,f3378,f3419,f3713,f3776,f3780,f3965,f4006,f4097])).

fof(f4097,plain,
    ( ~ spl16_1
    | spl16_4
    | ~ spl16_8
    | ~ spl16_9
    | ~ spl16_10
    | ~ spl16_38 ),
    inference(avatar_contradiction_clause,[],[f4096])).

fof(f4096,plain,
    ( $false
    | ~ spl16_1
    | spl16_4
    | ~ spl16_8
    | ~ spl16_9
    | ~ spl16_10
    | ~ spl16_38 ),
    inference(subsumption_resolution,[],[f4095,f3145])).

fof(f3145,plain,
    ( ~ r1_yellow_0(sK0,sK2)
    | spl16_4 ),
    inference(avatar_component_clause,[],[f3144])).

fof(f3144,plain,
    ( spl16_4
  <=> r1_yellow_0(sK0,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl16_4])])).

fof(f4095,plain,
    ( r1_yellow_0(sK0,sK2)
    | ~ spl16_1
    | ~ spl16_8
    | ~ spl16_9
    | ~ spl16_10
    | ~ spl16_38 ),
    inference(subsumption_resolution,[],[f4090,f3165])).

fof(f3165,plain,
    ( r2_lattice3(sK0,sK2,sK1)
    | ~ spl16_1 ),
    inference(avatar_component_clause,[],[f3135])).

fof(f3135,plain,
    ( spl16_1
  <=> r2_lattice3(sK0,sK2,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl16_1])])).

fof(f4090,plain,
    ( ~ r2_lattice3(sK0,sK2,sK1)
    | r1_yellow_0(sK0,sK2)
    | ~ spl16_8
    | ~ spl16_9
    | ~ spl16_10
    | ~ spl16_38 ),
    inference(resolution,[],[f3961,f3568])).

fof(f3568,plain,
    ( ! [X2] :
        ( ~ r1_orders_2(sK0,sK1,sK5(sK0,X2,sK1))
        | ~ r2_lattice3(sK0,X2,sK1)
        | r1_yellow_0(sK0,X2) )
    | ~ spl16_8
    | ~ spl16_9
    | ~ spl16_10 ),
    inference(resolution,[],[f3289,f3170])).

fof(f3170,plain,
    ( m1_subset_1(sK1,u1_struct_0(sK0))
    | ~ spl16_8 ),
    inference(avatar_component_clause,[],[f3169])).

fof(f3169,plain,
    ( spl16_8
  <=> m1_subset_1(sK1,u1_struct_0(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl16_8])])).

fof(f3289,plain,
    ( ! [X0,X1] :
        ( ~ m1_subset_1(X0,u1_struct_0(sK0))
        | ~ r2_lattice3(sK0,X1,X0)
        | ~ r1_orders_2(sK0,X0,sK5(sK0,X1,X0))
        | r1_yellow_0(sK0,X1) )
    | ~ spl16_9
    | ~ spl16_10 ),
    inference(subsumption_resolution,[],[f3288,f3174])).

fof(f3174,plain,
    ( l1_orders_2(sK0)
    | ~ spl16_9 ),
    inference(avatar_component_clause,[],[f3173])).

fof(f3173,plain,
    ( spl16_9
  <=> l1_orders_2(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl16_9])])).

fof(f3288,plain,
    ( ! [X0,X1] :
        ( ~ r1_orders_2(sK0,X0,sK5(sK0,X1,X0))
        | ~ r2_lattice3(sK0,X1,X0)
        | ~ m1_subset_1(X0,u1_struct_0(sK0))
        | ~ l1_orders_2(sK0)
        | r1_yellow_0(sK0,X1) )
    | ~ spl16_10 ),
    inference(resolution,[],[f3100,f3178])).

fof(f3178,plain,
    ( v5_orders_2(sK0)
    | ~ spl16_10 ),
    inference(avatar_component_clause,[],[f3177])).

fof(f3177,plain,
    ( spl16_10
  <=> v5_orders_2(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl16_10])])).

fof(f3100,plain,(
    ! [X2,X0,X1] :
      ( ~ v5_orders_2(X0)
      | ~ r1_orders_2(X0,X2,sK5(X0,X1,X2))
      | ~ r2_lattice3(X0,X1,X2)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | r1_yellow_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f3050])).

fof(f3050,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( r1_yellow_0(X0,X1)
            | ! [X2] :
                ( ( ~ r1_orders_2(X0,X2,sK5(X0,X1,X2))
                  & r2_lattice3(X0,X1,sK5(X0,X1,X2))
                  & m1_subset_1(sK5(X0,X1,X2),u1_struct_0(X0)) )
                | ~ r2_lattice3(X0,X1,X2)
                | ~ m1_subset_1(X2,u1_struct_0(X0)) ) )
          & ( ( ! [X5] :
                  ( r1_orders_2(X0,sK6(X0,X1),X5)
                  | ~ r2_lattice3(X0,X1,X5)
                  | ~ m1_subset_1(X5,u1_struct_0(X0)) )
              & r2_lattice3(X0,X1,sK6(X0,X1))
              & m1_subset_1(sK6(X0,X1),u1_struct_0(X0)) )
            | ~ r1_yellow_0(X0,X1) ) )
      | ~ l1_orders_2(X0)
      | ~ v5_orders_2(X0) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK5,sK6])],[f3047,f3049,f3048])).

fof(f3048,plain,(
    ! [X2,X1,X0] :
      ( ? [X3] :
          ( ~ r1_orders_2(X0,X2,X3)
          & r2_lattice3(X0,X1,X3)
          & m1_subset_1(X3,u1_struct_0(X0)) )
     => ( ~ r1_orders_2(X0,X2,sK5(X0,X1,X2))
        & r2_lattice3(X0,X1,sK5(X0,X1,X2))
        & m1_subset_1(sK5(X0,X1,X2),u1_struct_0(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f3049,plain,(
    ! [X1,X0] :
      ( ? [X4] :
          ( ! [X5] :
              ( r1_orders_2(X0,X4,X5)
              | ~ r2_lattice3(X0,X1,X5)
              | ~ m1_subset_1(X5,u1_struct_0(X0)) )
          & r2_lattice3(X0,X1,X4)
          & m1_subset_1(X4,u1_struct_0(X0)) )
     => ( ! [X5] :
            ( r1_orders_2(X0,sK6(X0,X1),X5)
            | ~ r2_lattice3(X0,X1,X5)
            | ~ m1_subset_1(X5,u1_struct_0(X0)) )
        & r2_lattice3(X0,X1,sK6(X0,X1))
        & m1_subset_1(sK6(X0,X1),u1_struct_0(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f3047,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( r1_yellow_0(X0,X1)
            | ! [X2] :
                ( ? [X3] :
                    ( ~ r1_orders_2(X0,X2,X3)
                    & r2_lattice3(X0,X1,X3)
                    & m1_subset_1(X3,u1_struct_0(X0)) )
                | ~ r2_lattice3(X0,X1,X2)
                | ~ m1_subset_1(X2,u1_struct_0(X0)) ) )
          & ( ? [X4] :
                ( ! [X5] :
                    ( r1_orders_2(X0,X4,X5)
                    | ~ r2_lattice3(X0,X1,X5)
                    | ~ m1_subset_1(X5,u1_struct_0(X0)) )
                & r2_lattice3(X0,X1,X4)
                & m1_subset_1(X4,u1_struct_0(X0)) )
            | ~ r1_yellow_0(X0,X1) ) )
      | ~ l1_orders_2(X0)
      | ~ v5_orders_2(X0) ) ),
    inference(rectify,[],[f3046])).

fof(f3046,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( r1_yellow_0(X0,X1)
            | ! [X2] :
                ( ? [X3] :
                    ( ~ r1_orders_2(X0,X2,X3)
                    & r2_lattice3(X0,X1,X3)
                    & m1_subset_1(X3,u1_struct_0(X0)) )
                | ~ r2_lattice3(X0,X1,X2)
                | ~ m1_subset_1(X2,u1_struct_0(X0)) ) )
          & ( ? [X2] :
                ( ! [X3] :
                    ( r1_orders_2(X0,X2,X3)
                    | ~ r2_lattice3(X0,X1,X3)
                    | ~ m1_subset_1(X3,u1_struct_0(X0)) )
                & r2_lattice3(X0,X1,X2)
                & m1_subset_1(X2,u1_struct_0(X0)) )
            | ~ r1_yellow_0(X0,X1) ) )
      | ~ l1_orders_2(X0)
      | ~ v5_orders_2(X0) ) ),
    inference(nnf_transformation,[],[f3027])).

fof(f3027,plain,(
    ! [X0] :
      ( ! [X1] :
          ( r1_yellow_0(X0,X1)
        <=> ? [X2] :
              ( ! [X3] :
                  ( r1_orders_2(X0,X2,X3)
                  | ~ r2_lattice3(X0,X1,X3)
                  | ~ m1_subset_1(X3,u1_struct_0(X0)) )
              & r2_lattice3(X0,X1,X2)
              & m1_subset_1(X2,u1_struct_0(X0)) ) )
      | ~ l1_orders_2(X0)
      | ~ v5_orders_2(X0) ) ),
    inference(flattening,[],[f3026])).

fof(f3026,plain,(
    ! [X0] :
      ( ! [X1] :
          ( r1_yellow_0(X0,X1)
        <=> ? [X2] :
              ( ! [X3] :
                  ( r1_orders_2(X0,X2,X3)
                  | ~ r2_lattice3(X0,X1,X3)
                  | ~ m1_subset_1(X3,u1_struct_0(X0)) )
              & r2_lattice3(X0,X1,X2)
              & m1_subset_1(X2,u1_struct_0(X0)) ) )
      | ~ l1_orders_2(X0)
      | ~ v5_orders_2(X0) ) ),
    inference(ennf_transformation,[],[f2989])).

fof(f2989,axiom,(
    ! [X0] :
      ( ( l1_orders_2(X0)
        & v5_orders_2(X0) )
     => ! [X1] :
          ( r1_yellow_0(X0,X1)
        <=> ? [X2] :
              ( ! [X3] :
                  ( m1_subset_1(X3,u1_struct_0(X0))
                 => ( r2_lattice3(X0,X1,X3)
                   => r1_orders_2(X0,X2,X3) ) )
              & r2_lattice3(X0,X1,X2)
              & m1_subset_1(X2,u1_struct_0(X0)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t15_yellow_0)).

fof(f3961,plain,
    ( r1_orders_2(sK0,sK1,sK5(sK0,sK2,sK1))
    | ~ spl16_38 ),
    inference(avatar_component_clause,[],[f3960])).

fof(f3960,plain,
    ( spl16_38
  <=> r1_orders_2(sK0,sK1,sK5(sK0,sK2,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl16_38])])).

fof(f4006,plain,
    ( ~ spl16_1
    | spl16_4
    | ~ spl16_8
    | ~ spl16_9
    | ~ spl16_10
    | spl16_39 ),
    inference(avatar_contradiction_clause,[],[f4005])).

fof(f4005,plain,
    ( $false
    | ~ spl16_1
    | spl16_4
    | ~ spl16_8
    | ~ spl16_9
    | ~ spl16_10
    | spl16_39 ),
    inference(subsumption_resolution,[],[f4004,f3178])).

fof(f4004,plain,
    ( ~ v5_orders_2(sK0)
    | ~ spl16_1
    | spl16_4
    | ~ spl16_8
    | ~ spl16_9
    | spl16_39 ),
    inference(subsumption_resolution,[],[f4003,f3174])).

fof(f4003,plain,
    ( ~ l1_orders_2(sK0)
    | ~ v5_orders_2(sK0)
    | ~ spl16_1
    | spl16_4
    | ~ spl16_8
    | spl16_39 ),
    inference(subsumption_resolution,[],[f4002,f3170])).

fof(f4002,plain,
    ( ~ m1_subset_1(sK1,u1_struct_0(sK0))
    | ~ l1_orders_2(sK0)
    | ~ v5_orders_2(sK0)
    | ~ spl16_1
    | spl16_4
    | spl16_39 ),
    inference(subsumption_resolution,[],[f4001,f3165])).

fof(f4001,plain,
    ( ~ r2_lattice3(sK0,sK2,sK1)
    | ~ m1_subset_1(sK1,u1_struct_0(sK0))
    | ~ l1_orders_2(sK0)
    | ~ v5_orders_2(sK0)
    | spl16_4
    | spl16_39 ),
    inference(subsumption_resolution,[],[f3999,f3145])).

fof(f3999,plain,
    ( r1_yellow_0(sK0,sK2)
    | ~ r2_lattice3(sK0,sK2,sK1)
    | ~ m1_subset_1(sK1,u1_struct_0(sK0))
    | ~ l1_orders_2(sK0)
    | ~ v5_orders_2(sK0)
    | spl16_39 ),
    inference(resolution,[],[f3964,f3098])).

fof(f3098,plain,(
    ! [X2,X0,X1] :
      ( m1_subset_1(sK5(X0,X1,X2),u1_struct_0(X0))
      | r1_yellow_0(X0,X1)
      | ~ r2_lattice3(X0,X1,X2)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | ~ v5_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f3050])).

fof(f3964,plain,
    ( ~ m1_subset_1(sK5(sK0,sK2,sK1),u1_struct_0(sK0))
    | spl16_39 ),
    inference(avatar_component_clause,[],[f3963])).

fof(f3963,plain,
    ( spl16_39
  <=> m1_subset_1(sK5(sK0,sK2,sK1),u1_struct_0(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl16_39])])).

fof(f3965,plain,
    ( spl16_38
    | ~ spl16_39
    | ~ spl16_7
    | ~ spl16_34 ),
    inference(avatar_split_clause,[],[f3958,f3778,f3156,f3963,f3960])).

fof(f3156,plain,
    ( spl16_7
  <=> ! [X3] :
        ( r1_orders_2(sK0,sK1,X3)
        | ~ m1_subset_1(X3,u1_struct_0(sK0))
        | ~ r2_lattice3(sK0,sK2,X3) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl16_7])])).

fof(f3778,plain,
    ( spl16_34
  <=> r2_lattice3(sK0,sK2,sK5(sK0,sK2,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl16_34])])).

fof(f3958,plain,
    ( ~ m1_subset_1(sK5(sK0,sK2,sK1),u1_struct_0(sK0))
    | r1_orders_2(sK0,sK1,sK5(sK0,sK2,sK1))
    | ~ spl16_7
    | ~ spl16_34 ),
    inference(resolution,[],[f3779,f3157])).

fof(f3157,plain,
    ( ! [X3] :
        ( ~ r2_lattice3(sK0,sK2,X3)
        | ~ m1_subset_1(X3,u1_struct_0(sK0))
        | r1_orders_2(sK0,sK1,X3) )
    | ~ spl16_7 ),
    inference(avatar_component_clause,[],[f3156])).

fof(f3779,plain,
    ( r2_lattice3(sK0,sK2,sK5(sK0,sK2,sK1))
    | ~ spl16_34 ),
    inference(avatar_component_clause,[],[f3778])).

fof(f3780,plain,
    ( spl16_4
    | spl16_34
    | ~ spl16_1
    | ~ spl16_8
    | ~ spl16_9
    | ~ spl16_10 ),
    inference(avatar_split_clause,[],[f3565,f3177,f3173,f3169,f3135,f3778,f3144])).

fof(f3565,plain,
    ( r2_lattice3(sK0,sK2,sK5(sK0,sK2,sK1))
    | r1_yellow_0(sK0,sK2)
    | ~ spl16_1
    | ~ spl16_8
    | ~ spl16_9
    | ~ spl16_10 ),
    inference(resolution,[],[f3534,f3165])).

fof(f3534,plain,
    ( ! [X2] :
        ( ~ r2_lattice3(sK0,X2,sK1)
        | r2_lattice3(sK0,X2,sK5(sK0,X2,sK1))
        | r1_yellow_0(sK0,X2) )
    | ~ spl16_8
    | ~ spl16_9
    | ~ spl16_10 ),
    inference(resolution,[],[f3287,f3170])).

fof(f3287,plain,
    ( ! [X0,X1] :
        ( ~ m1_subset_1(X1,u1_struct_0(sK0))
        | ~ r2_lattice3(sK0,X0,X1)
        | r2_lattice3(sK0,X0,sK5(sK0,X0,X1))
        | r1_yellow_0(sK0,X0) )
    | ~ spl16_9
    | ~ spl16_10 ),
    inference(subsumption_resolution,[],[f3286,f3174])).

fof(f3286,plain,
    ( ! [X0,X1] :
        ( r2_lattice3(sK0,X0,sK5(sK0,X0,X1))
        | ~ r2_lattice3(sK0,X0,X1)
        | ~ m1_subset_1(X1,u1_struct_0(sK0))
        | ~ l1_orders_2(sK0)
        | r1_yellow_0(sK0,X0) )
    | ~ spl16_10 ),
    inference(resolution,[],[f3099,f3178])).

fof(f3099,plain,(
    ! [X2,X0,X1] :
      ( ~ v5_orders_2(X0)
      | r2_lattice3(X0,X1,sK5(X0,X1,X2))
      | ~ r2_lattice3(X0,X1,X2)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | r1_yellow_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f3050])).

fof(f3776,plain,
    ( ~ spl16_4
    | ~ spl16_1
    | ~ spl16_8
    | ~ spl16_9
    | spl16_28 ),
    inference(avatar_split_clause,[],[f3775,f3711,f3173,f3169,f3135,f3144])).

fof(f3711,plain,
    ( spl16_28
  <=> r1_orders_2(sK0,k1_yellow_0(sK0,sK2),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl16_28])])).

fof(f3775,plain,
    ( ~ r1_yellow_0(sK0,sK2)
    | ~ spl16_1
    | ~ spl16_8
    | ~ spl16_9
    | spl16_28 ),
    inference(subsumption_resolution,[],[f3763,f3165])).

fof(f3763,plain,
    ( ~ r1_yellow_0(sK0,sK2)
    | ~ r2_lattice3(sK0,sK2,sK1)
    | ~ spl16_8
    | ~ spl16_9
    | spl16_28 ),
    inference(resolution,[],[f3712,f3318])).

fof(f3318,plain,
    ( ! [X2] :
        ( r1_orders_2(sK0,k1_yellow_0(sK0,X2),sK1)
        | ~ r1_yellow_0(sK0,X2)
        | ~ r2_lattice3(sK0,X2,sK1) )
    | ~ spl16_8
    | ~ spl16_9 ),
    inference(resolution,[],[f3259,f3170])).

fof(f3259,plain,
    ( ! [X0,X1] :
        ( ~ m1_subset_1(X1,u1_struct_0(sK0))
        | ~ r2_lattice3(sK0,X0,X1)
        | ~ r1_yellow_0(sK0,X0)
        | r1_orders_2(sK0,k1_yellow_0(sK0,X0),X1) )
    | ~ spl16_9 ),
    inference(resolution,[],[f3180,f3174])).

fof(f3180,plain,(
    ! [X4,X0,X1] :
      ( ~ l1_orders_2(X0)
      | ~ r2_lattice3(X0,X1,X4)
      | ~ m1_subset_1(X4,u1_struct_0(X0))
      | ~ r1_yellow_0(X0,X1)
      | r1_orders_2(X0,k1_yellow_0(X0,X1),X4) ) ),
    inference(global_subsumption,[],[f3123,f3132])).

fof(f3132,plain,(
    ! [X4,X0,X1] :
      ( r1_orders_2(X0,k1_yellow_0(X0,X1),X4)
      | ~ r2_lattice3(X0,X1,X4)
      | ~ m1_subset_1(X4,u1_struct_0(X0))
      | ~ r1_yellow_0(X0,X1)
      | ~ m1_subset_1(k1_yellow_0(X0,X1),u1_struct_0(X0))
      | ~ l1_orders_2(X0) ) ),
    inference(equality_resolution,[],[f3125])).

fof(f3125,plain,(
    ! [X4,X2,X0,X1] :
      ( r1_orders_2(X0,X2,X4)
      | ~ r2_lattice3(X0,X1,X4)
      | ~ m1_subset_1(X4,u1_struct_0(X0))
      | k1_yellow_0(X0,X1) != X2
      | ~ r1_yellow_0(X0,X1)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ l1_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f3067])).

fof(f3067,plain,(
    ! [X0] :
      ( ! [X1,X2] :
          ( ( ( k1_yellow_0(X0,X1) = X2
              | ( ~ r1_orders_2(X0,X2,sK13(X0,X1,X2))
                & r2_lattice3(X0,X1,sK13(X0,X1,X2))
                & m1_subset_1(sK13(X0,X1,X2),u1_struct_0(X0)) )
              | ~ r2_lattice3(X0,X1,X2) )
            & ( ( ! [X4] :
                    ( r1_orders_2(X0,X2,X4)
                    | ~ r2_lattice3(X0,X1,X4)
                    | ~ m1_subset_1(X4,u1_struct_0(X0)) )
                & r2_lattice3(X0,X1,X2) )
              | k1_yellow_0(X0,X1) != X2 ) )
          | ~ r1_yellow_0(X0,X1)
          | ~ m1_subset_1(X2,u1_struct_0(X0)) )
      | ~ l1_orders_2(X0) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK13])],[f3065,f3066])).

fof(f3066,plain,(
    ! [X2,X1,X0] :
      ( ? [X3] :
          ( ~ r1_orders_2(X0,X2,X3)
          & r2_lattice3(X0,X1,X3)
          & m1_subset_1(X3,u1_struct_0(X0)) )
     => ( ~ r1_orders_2(X0,X2,sK13(X0,X1,X2))
        & r2_lattice3(X0,X1,sK13(X0,X1,X2))
        & m1_subset_1(sK13(X0,X1,X2),u1_struct_0(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f3065,plain,(
    ! [X0] :
      ( ! [X1,X2] :
          ( ( ( k1_yellow_0(X0,X1) = X2
              | ? [X3] :
                  ( ~ r1_orders_2(X0,X2,X3)
                  & r2_lattice3(X0,X1,X3)
                  & m1_subset_1(X3,u1_struct_0(X0)) )
              | ~ r2_lattice3(X0,X1,X2) )
            & ( ( ! [X4] :
                    ( r1_orders_2(X0,X2,X4)
                    | ~ r2_lattice3(X0,X1,X4)
                    | ~ m1_subset_1(X4,u1_struct_0(X0)) )
                & r2_lattice3(X0,X1,X2) )
              | k1_yellow_0(X0,X1) != X2 ) )
          | ~ r1_yellow_0(X0,X1)
          | ~ m1_subset_1(X2,u1_struct_0(X0)) )
      | ~ l1_orders_2(X0) ) ),
    inference(rectify,[],[f3064])).

fof(f3064,plain,(
    ! [X0] :
      ( ! [X1,X2] :
          ( ( ( k1_yellow_0(X0,X1) = X2
              | ? [X3] :
                  ( ~ r1_orders_2(X0,X2,X3)
                  & r2_lattice3(X0,X1,X3)
                  & m1_subset_1(X3,u1_struct_0(X0)) )
              | ~ r2_lattice3(X0,X1,X2) )
            & ( ( ! [X3] :
                    ( r1_orders_2(X0,X2,X3)
                    | ~ r2_lattice3(X0,X1,X3)
                    | ~ m1_subset_1(X3,u1_struct_0(X0)) )
                & r2_lattice3(X0,X1,X2) )
              | k1_yellow_0(X0,X1) != X2 ) )
          | ~ r1_yellow_0(X0,X1)
          | ~ m1_subset_1(X2,u1_struct_0(X0)) )
      | ~ l1_orders_2(X0) ) ),
    inference(flattening,[],[f3063])).

fof(f3063,plain,(
    ! [X0] :
      ( ! [X1,X2] :
          ( ( ( k1_yellow_0(X0,X1) = X2
              | ? [X3] :
                  ( ~ r1_orders_2(X0,X2,X3)
                  & r2_lattice3(X0,X1,X3)
                  & m1_subset_1(X3,u1_struct_0(X0)) )
              | ~ r2_lattice3(X0,X1,X2) )
            & ( ( ! [X3] :
                    ( r1_orders_2(X0,X2,X3)
                    | ~ r2_lattice3(X0,X1,X3)
                    | ~ m1_subset_1(X3,u1_struct_0(X0)) )
                & r2_lattice3(X0,X1,X2) )
              | k1_yellow_0(X0,X1) != X2 ) )
          | ~ r1_yellow_0(X0,X1)
          | ~ m1_subset_1(X2,u1_struct_0(X0)) )
      | ~ l1_orders_2(X0) ) ),
    inference(nnf_transformation,[],[f3034])).

fof(f3034,plain,(
    ! [X0] :
      ( ! [X1,X2] :
          ( ( k1_yellow_0(X0,X1) = X2
          <=> ( ! [X3] :
                  ( r1_orders_2(X0,X2,X3)
                  | ~ r2_lattice3(X0,X1,X3)
                  | ~ m1_subset_1(X3,u1_struct_0(X0)) )
              & r2_lattice3(X0,X1,X2) ) )
          | ~ r1_yellow_0(X0,X1)
          | ~ m1_subset_1(X2,u1_struct_0(X0)) )
      | ~ l1_orders_2(X0) ) ),
    inference(flattening,[],[f3033])).

fof(f3033,plain,(
    ! [X0] :
      ( ! [X1,X2] :
          ( ( k1_yellow_0(X0,X1) = X2
          <=> ( ! [X3] :
                  ( r1_orders_2(X0,X2,X3)
                  | ~ r2_lattice3(X0,X1,X3)
                  | ~ m1_subset_1(X3,u1_struct_0(X0)) )
              & r2_lattice3(X0,X1,X2) ) )
          | ~ r1_yellow_0(X0,X1)
          | ~ m1_subset_1(X2,u1_struct_0(X0)) )
      | ~ l1_orders_2(X0) ) ),
    inference(ennf_transformation,[],[f2974])).

fof(f2974,axiom,(
    ! [X0] :
      ( l1_orders_2(X0)
     => ! [X1,X2] :
          ( m1_subset_1(X2,u1_struct_0(X0))
         => ( r1_yellow_0(X0,X1)
           => ( k1_yellow_0(X0,X1) = X2
            <=> ( ! [X3] :
                    ( m1_subset_1(X3,u1_struct_0(X0))
                   => ( r2_lattice3(X0,X1,X3)
                     => r1_orders_2(X0,X2,X3) ) )
                & r2_lattice3(X0,X1,X2) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d9_yellow_0)).

fof(f3123,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k1_yellow_0(X0,X1),u1_struct_0(X0))
      | ~ l1_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f3032])).

fof(f3032,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k1_yellow_0(X0,X1),u1_struct_0(X0))
      | ~ l1_orders_2(X0) ) ),
    inference(ennf_transformation,[],[f2976])).

fof(f2976,axiom,(
    ! [X0,X1] :
      ( l1_orders_2(X0)
     => m1_subset_1(k1_yellow_0(X0,X1),u1_struct_0(X0)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k1_yellow_0)).

fof(f3712,plain,
    ( ~ r1_orders_2(sK0,k1_yellow_0(sK0,sK2),sK1)
    | spl16_28 ),
    inference(avatar_component_clause,[],[f3711])).

fof(f3713,plain,
    ( ~ spl16_28
    | ~ spl16_20
    | spl16_3
    | ~ spl16_8
    | ~ spl16_9
    | ~ spl16_10
    | ~ spl16_19 ),
    inference(avatar_split_clause,[],[f3709,f3373,f3177,f3173,f3169,f3141,f3376,f3711])).

fof(f3376,plain,
    ( spl16_20
  <=> m1_subset_1(k1_yellow_0(sK0,sK2),u1_struct_0(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl16_20])])).

fof(f3141,plain,
    ( spl16_3
  <=> sK1 = k1_yellow_0(sK0,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl16_3])])).

fof(f3373,plain,
    ( spl16_19
  <=> r1_orders_2(sK0,sK1,k1_yellow_0(sK0,sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl16_19])])).

fof(f3709,plain,
    ( ~ m1_subset_1(k1_yellow_0(sK0,sK2),u1_struct_0(sK0))
    | ~ r1_orders_2(sK0,k1_yellow_0(sK0,sK2),sK1)
    | spl16_3
    | ~ spl16_8
    | ~ spl16_9
    | ~ spl16_10
    | ~ spl16_19 ),
    inference(subsumption_resolution,[],[f3703,f3142])).

fof(f3142,plain,
    ( sK1 != k1_yellow_0(sK0,sK2)
    | spl16_3 ),
    inference(avatar_component_clause,[],[f3141])).

fof(f3703,plain,
    ( ~ m1_subset_1(k1_yellow_0(sK0,sK2),u1_struct_0(sK0))
    | ~ r1_orders_2(sK0,k1_yellow_0(sK0,sK2),sK1)
    | sK1 = k1_yellow_0(sK0,sK2)
    | ~ spl16_8
    | ~ spl16_9
    | ~ spl16_10
    | ~ spl16_19 ),
    inference(resolution,[],[f3639,f3374])).

fof(f3374,plain,
    ( r1_orders_2(sK0,sK1,k1_yellow_0(sK0,sK2))
    | ~ spl16_19 ),
    inference(avatar_component_clause,[],[f3373])).

fof(f3639,plain,
    ( ! [X2] :
        ( ~ r1_orders_2(sK0,sK1,X2)
        | ~ m1_subset_1(X2,u1_struct_0(sK0))
        | ~ r1_orders_2(sK0,X2,sK1)
        | sK1 = X2 )
    | ~ spl16_8
    | ~ spl16_9
    | ~ spl16_10 ),
    inference(resolution,[],[f3308,f3170])).

fof(f3308,plain,
    ( ! [X0,X1] :
        ( ~ m1_subset_1(X1,u1_struct_0(sK0))
        | ~ r1_orders_2(sK0,X1,X0)
        | ~ m1_subset_1(X0,u1_struct_0(sK0))
        | ~ r1_orders_2(sK0,X0,X1)
        | X0 = X1 )
    | ~ spl16_9
    | ~ spl16_10 ),
    inference(subsumption_resolution,[],[f3307,f3174])).

fof(f3307,plain,
    ( ! [X0,X1] :
        ( ~ r1_orders_2(sK0,X0,X1)
        | ~ r1_orders_2(sK0,X1,X0)
        | ~ m1_subset_1(X0,u1_struct_0(sK0))
        | ~ m1_subset_1(X1,u1_struct_0(sK0))
        | ~ l1_orders_2(sK0)
        | X0 = X1 )
    | ~ spl16_10 ),
    inference(resolution,[],[f3090,f3178])).

fof(f3090,plain,(
    ! [X2,X0,X1] :
      ( ~ v5_orders_2(X0)
      | ~ r1_orders_2(X0,X2,X1)
      | ~ r1_orders_2(X0,X1,X2)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | X1 = X2 ) ),
    inference(cnf_transformation,[],[f3023])).

fof(f3023,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( X1 = X2
              | ~ r1_orders_2(X0,X2,X1)
              | ~ r1_orders_2(X0,X1,X2)
              | ~ m1_subset_1(X2,u1_struct_0(X0)) )
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l1_orders_2(X0)
      | ~ v5_orders_2(X0) ) ),
    inference(flattening,[],[f3022])).

fof(f3022,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( X1 = X2
              | ~ r1_orders_2(X0,X2,X1)
              | ~ r1_orders_2(X0,X1,X2)
              | ~ m1_subset_1(X2,u1_struct_0(X0)) )
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l1_orders_2(X0)
      | ~ v5_orders_2(X0) ) ),
    inference(ennf_transformation,[],[f1953])).

fof(f1953,axiom,(
    ! [X0] :
      ( ( l1_orders_2(X0)
        & v5_orders_2(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,u1_struct_0(X0))
         => ! [X2] :
              ( m1_subset_1(X2,u1_struct_0(X0))
             => ( ( r1_orders_2(X0,X2,X1)
                  & r1_orders_2(X0,X1,X2) )
               => X1 = X2 ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t25_orders_2)).

fof(f3419,plain,
    ( ~ spl16_9
    | spl16_20 ),
    inference(avatar_contradiction_clause,[],[f3418])).

fof(f3418,plain,
    ( $false
    | ~ spl16_9
    | spl16_20 ),
    inference(subsumption_resolution,[],[f3416,f3174])).

fof(f3416,plain,
    ( ~ l1_orders_2(sK0)
    | spl16_20 ),
    inference(resolution,[],[f3377,f3123])).

fof(f3377,plain,
    ( ~ m1_subset_1(k1_yellow_0(sK0,sK2),u1_struct_0(sK0))
    | spl16_20 ),
    inference(avatar_component_clause,[],[f3376])).

fof(f3378,plain,
    ( spl16_19
    | ~ spl16_20
    | ~ spl16_7
    | ~ spl16_18 ),
    inference(avatar_split_clause,[],[f3362,f3358,f3156,f3376,f3373])).

fof(f3358,plain,
    ( spl16_18
  <=> r2_lattice3(sK0,sK2,k1_yellow_0(sK0,sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl16_18])])).

fof(f3362,plain,
    ( ~ m1_subset_1(k1_yellow_0(sK0,sK2),u1_struct_0(sK0))
    | r1_orders_2(sK0,sK1,k1_yellow_0(sK0,sK2))
    | ~ spl16_7
    | ~ spl16_18 ),
    inference(resolution,[],[f3157,f3359])).

fof(f3359,plain,
    ( r2_lattice3(sK0,sK2,k1_yellow_0(sK0,sK2))
    | ~ spl16_18 ),
    inference(avatar_component_clause,[],[f3358])).

fof(f3360,plain,
    ( spl16_18
    | ~ spl16_4
    | ~ spl16_9 ),
    inference(avatar_split_clause,[],[f3204,f3173,f3144,f3358])).

fof(f3204,plain,
    ( r2_lattice3(sK0,sK2,k1_yellow_0(sK0,sK2))
    | ~ spl16_4
    | ~ spl16_9 ),
    inference(resolution,[],[f3189,f3161])).

fof(f3161,plain,
    ( r1_yellow_0(sK0,sK2)
    | ~ spl16_4 ),
    inference(avatar_component_clause,[],[f3144])).

fof(f3189,plain,
    ( ! [X0] :
        ( ~ r1_yellow_0(sK0,X0)
        | r2_lattice3(sK0,X0,k1_yellow_0(sK0,X0)) )
    | ~ spl16_9 ),
    inference(resolution,[],[f3181,f3174])).

fof(f3181,plain,(
    ! [X0,X1] :
      ( ~ l1_orders_2(X0)
      | ~ r1_yellow_0(X0,X1)
      | r2_lattice3(X0,X1,k1_yellow_0(X0,X1)) ) ),
    inference(global_subsumption,[],[f3123,f3133])).

fof(f3133,plain,(
    ! [X0,X1] :
      ( r2_lattice3(X0,X1,k1_yellow_0(X0,X1))
      | ~ r1_yellow_0(X0,X1)
      | ~ m1_subset_1(k1_yellow_0(X0,X1),u1_struct_0(X0))
      | ~ l1_orders_2(X0) ) ),
    inference(equality_resolution,[],[f3124])).

fof(f3124,plain,(
    ! [X2,X0,X1] :
      ( r2_lattice3(X0,X1,X2)
      | k1_yellow_0(X0,X1) != X2
      | ~ r1_yellow_0(X0,X1)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ l1_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f3067])).

fof(f3356,plain,
    ( spl16_2
    | ~ spl16_3
    | ~ spl16_4
    | ~ spl16_5
    | ~ spl16_6
    | ~ spl16_9 ),
    inference(avatar_contradiction_clause,[],[f3355])).

fof(f3355,plain,
    ( $false
    | spl16_2
    | ~ spl16_3
    | ~ spl16_4
    | ~ spl16_5
    | ~ spl16_6
    | ~ spl16_9 ),
    inference(subsumption_resolution,[],[f3354,f3149])).

fof(f3149,plain,
    ( r2_lattice3(sK0,sK2,sK3)
    | ~ spl16_5 ),
    inference(avatar_component_clause,[],[f3148])).

fof(f3148,plain,
    ( spl16_5
  <=> r2_lattice3(sK0,sK2,sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl16_5])])).

fof(f3354,plain,
    ( ~ r2_lattice3(sK0,sK2,sK3)
    | spl16_2
    | ~ spl16_3
    | ~ spl16_4
    | ~ spl16_6
    | ~ spl16_9 ),
    inference(subsumption_resolution,[],[f3353,f3161])).

fof(f3353,plain,
    ( ~ r1_yellow_0(sK0,sK2)
    | ~ r2_lattice3(sK0,sK2,sK3)
    | spl16_2
    | ~ spl16_3
    | ~ spl16_6
    | ~ spl16_9 ),
    inference(subsumption_resolution,[],[f3352,f3139])).

fof(f3139,plain,
    ( ~ r1_orders_2(sK0,sK1,sK3)
    | spl16_2 ),
    inference(avatar_component_clause,[],[f3138])).

fof(f3138,plain,
    ( spl16_2
  <=> r1_orders_2(sK0,sK1,sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl16_2])])).

fof(f3352,plain,
    ( r1_orders_2(sK0,sK1,sK3)
    | ~ r1_yellow_0(sK0,sK2)
    | ~ r2_lattice3(sK0,sK2,sK3)
    | ~ spl16_3
    | ~ spl16_6
    | ~ spl16_9 ),
    inference(superposition,[],[f3319,f3163])).

fof(f3163,plain,
    ( sK1 = k1_yellow_0(sK0,sK2)
    | ~ spl16_3 ),
    inference(avatar_component_clause,[],[f3141])).

fof(f3319,plain,
    ( ! [X3] :
        ( r1_orders_2(sK0,k1_yellow_0(sK0,X3),sK3)
        | ~ r1_yellow_0(sK0,X3)
        | ~ r2_lattice3(sK0,X3,sK3) )
    | ~ spl16_6
    | ~ spl16_9 ),
    inference(resolution,[],[f3259,f3153])).

fof(f3153,plain,
    ( m1_subset_1(sK3,u1_struct_0(sK0))
    | ~ spl16_6 ),
    inference(avatar_component_clause,[],[f3152])).

fof(f3152,plain,
    ( spl16_6
  <=> m1_subset_1(sK3,u1_struct_0(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl16_6])])).

fof(f3208,plain,
    ( spl16_1
    | ~ spl16_3
    | ~ spl16_4
    | ~ spl16_9 ),
    inference(avatar_split_clause,[],[f3205,f3173,f3144,f3141,f3135])).

fof(f3205,plain,
    ( r2_lattice3(sK0,sK2,sK1)
    | ~ spl16_3
    | ~ spl16_4
    | ~ spl16_9 ),
    inference(forward_demodulation,[],[f3204,f3163])).

fof(f3179,plain,(
    spl16_10 ),
    inference(avatar_split_clause,[],[f3072,f3177])).

fof(f3072,plain,(
    v5_orders_2(sK0) ),
    inference(cnf_transformation,[],[f3041])).

fof(f3041,plain,
    ( ( ( ( ~ r1_yellow_0(sK0,sK2)
          | sK1 != k1_yellow_0(sK0,sK2) )
        & ! [X3] :
            ( r1_orders_2(sK0,sK1,X3)
            | ~ r2_lattice3(sK0,sK2,X3)
            | ~ m1_subset_1(X3,u1_struct_0(sK0)) )
        & r2_lattice3(sK0,sK2,sK1) )
      | ( ( ( ~ r1_orders_2(sK0,sK1,sK3)
            & r2_lattice3(sK0,sK2,sK3)
            & m1_subset_1(sK3,u1_struct_0(sK0)) )
          | ~ r2_lattice3(sK0,sK2,sK1) )
        & r1_yellow_0(sK0,sK2)
        & sK1 = k1_yellow_0(sK0,sK2) ) )
    & m1_subset_1(sK1,u1_struct_0(sK0))
    & l1_orders_2(sK0)
    & v5_orders_2(sK0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3])],[f3021,f3040,f3039,f3038,f3037])).

fof(f3037,plain,
    ( ? [X0] :
        ( ? [X1] :
            ( ? [X2] :
                ( ( ( ~ r1_yellow_0(X0,X2)
                    | k1_yellow_0(X0,X2) != X1 )
                  & ! [X3] :
                      ( r1_orders_2(X0,X1,X3)
                      | ~ r2_lattice3(X0,X2,X3)
                      | ~ m1_subset_1(X3,u1_struct_0(X0)) )
                  & r2_lattice3(X0,X2,X1) )
                | ( ( ? [X4] :
                        ( ~ r1_orders_2(X0,X1,X4)
                        & r2_lattice3(X0,X2,X4)
                        & m1_subset_1(X4,u1_struct_0(X0)) )
                    | ~ r2_lattice3(X0,X2,X1) )
                  & r1_yellow_0(X0,X2)
                  & k1_yellow_0(X0,X2) = X1 ) )
            & m1_subset_1(X1,u1_struct_0(X0)) )
        & l1_orders_2(X0)
        & v5_orders_2(X0) )
   => ( ? [X1] :
          ( ? [X2] :
              ( ( ( ~ r1_yellow_0(sK0,X2)
                  | k1_yellow_0(sK0,X2) != X1 )
                & ! [X3] :
                    ( r1_orders_2(sK0,X1,X3)
                    | ~ r2_lattice3(sK0,X2,X3)
                    | ~ m1_subset_1(X3,u1_struct_0(sK0)) )
                & r2_lattice3(sK0,X2,X1) )
              | ( ( ? [X4] :
                      ( ~ r1_orders_2(sK0,X1,X4)
                      & r2_lattice3(sK0,X2,X4)
                      & m1_subset_1(X4,u1_struct_0(sK0)) )
                  | ~ r2_lattice3(sK0,X2,X1) )
                & r1_yellow_0(sK0,X2)
                & k1_yellow_0(sK0,X2) = X1 ) )
          & m1_subset_1(X1,u1_struct_0(sK0)) )
      & l1_orders_2(sK0)
      & v5_orders_2(sK0) ) ),
    introduced(choice_axiom,[])).

fof(f3038,plain,
    ( ? [X1] :
        ( ? [X2] :
            ( ( ( ~ r1_yellow_0(sK0,X2)
                | k1_yellow_0(sK0,X2) != X1 )
              & ! [X3] :
                  ( r1_orders_2(sK0,X1,X3)
                  | ~ r2_lattice3(sK0,X2,X3)
                  | ~ m1_subset_1(X3,u1_struct_0(sK0)) )
              & r2_lattice3(sK0,X2,X1) )
            | ( ( ? [X4] :
                    ( ~ r1_orders_2(sK0,X1,X4)
                    & r2_lattice3(sK0,X2,X4)
                    & m1_subset_1(X4,u1_struct_0(sK0)) )
                | ~ r2_lattice3(sK0,X2,X1) )
              & r1_yellow_0(sK0,X2)
              & k1_yellow_0(sK0,X2) = X1 ) )
        & m1_subset_1(X1,u1_struct_0(sK0)) )
   => ( ? [X2] :
          ( ( ( ~ r1_yellow_0(sK0,X2)
              | k1_yellow_0(sK0,X2) != sK1 )
            & ! [X3] :
                ( r1_orders_2(sK0,sK1,X3)
                | ~ r2_lattice3(sK0,X2,X3)
                | ~ m1_subset_1(X3,u1_struct_0(sK0)) )
            & r2_lattice3(sK0,X2,sK1) )
          | ( ( ? [X4] :
                  ( ~ r1_orders_2(sK0,sK1,X4)
                  & r2_lattice3(sK0,X2,X4)
                  & m1_subset_1(X4,u1_struct_0(sK0)) )
              | ~ r2_lattice3(sK0,X2,sK1) )
            & r1_yellow_0(sK0,X2)
            & k1_yellow_0(sK0,X2) = sK1 ) )
      & m1_subset_1(sK1,u1_struct_0(sK0)) ) ),
    introduced(choice_axiom,[])).

fof(f3039,plain,
    ( ? [X2] :
        ( ( ( ~ r1_yellow_0(sK0,X2)
            | k1_yellow_0(sK0,X2) != sK1 )
          & ! [X3] :
              ( r1_orders_2(sK0,sK1,X3)
              | ~ r2_lattice3(sK0,X2,X3)
              | ~ m1_subset_1(X3,u1_struct_0(sK0)) )
          & r2_lattice3(sK0,X2,sK1) )
        | ( ( ? [X4] :
                ( ~ r1_orders_2(sK0,sK1,X4)
                & r2_lattice3(sK0,X2,X4)
                & m1_subset_1(X4,u1_struct_0(sK0)) )
            | ~ r2_lattice3(sK0,X2,sK1) )
          & r1_yellow_0(sK0,X2)
          & k1_yellow_0(sK0,X2) = sK1 ) )
   => ( ( ( ~ r1_yellow_0(sK0,sK2)
          | sK1 != k1_yellow_0(sK0,sK2) )
        & ! [X3] :
            ( r1_orders_2(sK0,sK1,X3)
            | ~ r2_lattice3(sK0,sK2,X3)
            | ~ m1_subset_1(X3,u1_struct_0(sK0)) )
        & r2_lattice3(sK0,sK2,sK1) )
      | ( ( ? [X4] :
              ( ~ r1_orders_2(sK0,sK1,X4)
              & r2_lattice3(sK0,sK2,X4)
              & m1_subset_1(X4,u1_struct_0(sK0)) )
          | ~ r2_lattice3(sK0,sK2,sK1) )
        & r1_yellow_0(sK0,sK2)
        & sK1 = k1_yellow_0(sK0,sK2) ) ) ),
    introduced(choice_axiom,[])).

fof(f3040,plain,
    ( ? [X4] :
        ( ~ r1_orders_2(sK0,sK1,X4)
        & r2_lattice3(sK0,sK2,X4)
        & m1_subset_1(X4,u1_struct_0(sK0)) )
   => ( ~ r1_orders_2(sK0,sK1,sK3)
      & r2_lattice3(sK0,sK2,sK3)
      & m1_subset_1(sK3,u1_struct_0(sK0)) ) ),
    introduced(choice_axiom,[])).

fof(f3021,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ( ( ~ r1_yellow_0(X0,X2)
                  | k1_yellow_0(X0,X2) != X1 )
                & ! [X3] :
                    ( r1_orders_2(X0,X1,X3)
                    | ~ r2_lattice3(X0,X2,X3)
                    | ~ m1_subset_1(X3,u1_struct_0(X0)) )
                & r2_lattice3(X0,X2,X1) )
              | ( ( ? [X4] :
                      ( ~ r1_orders_2(X0,X1,X4)
                      & r2_lattice3(X0,X2,X4)
                      & m1_subset_1(X4,u1_struct_0(X0)) )
                  | ~ r2_lattice3(X0,X2,X1) )
                & r1_yellow_0(X0,X2)
                & k1_yellow_0(X0,X2) = X1 ) )
          & m1_subset_1(X1,u1_struct_0(X0)) )
      & l1_orders_2(X0)
      & v5_orders_2(X0) ) ),
    inference(flattening,[],[f3020])).

fof(f3020,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ( ( ~ r1_yellow_0(X0,X2)
                  | k1_yellow_0(X0,X2) != X1 )
                & ! [X3] :
                    ( r1_orders_2(X0,X1,X3)
                    | ~ r2_lattice3(X0,X2,X3)
                    | ~ m1_subset_1(X3,u1_struct_0(X0)) )
                & r2_lattice3(X0,X2,X1) )
              | ( ( ? [X4] :
                      ( ~ r1_orders_2(X0,X1,X4)
                      & r2_lattice3(X0,X2,X4)
                      & m1_subset_1(X4,u1_struct_0(X0)) )
                  | ~ r2_lattice3(X0,X2,X1) )
                & r1_yellow_0(X0,X2)
                & k1_yellow_0(X0,X2) = X1 ) )
          & m1_subset_1(X1,u1_struct_0(X0)) )
      & l1_orders_2(X0)
      & v5_orders_2(X0) ) ),
    inference(ennf_transformation,[],[f3015])).

fof(f3015,plain,(
    ~ ! [X0] :
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
    inference(rectify,[],[f3007])).

fof(f3007,negated_conjecture,(
    ~ ! [X0] :
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
    inference(negated_conjecture,[],[f3006])).

fof(f3006,conjecture,(
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

fof(f3175,plain,(
    spl16_9 ),
    inference(avatar_split_clause,[],[f3073,f3173])).

fof(f3073,plain,(
    l1_orders_2(sK0) ),
    inference(cnf_transformation,[],[f3041])).

fof(f3171,plain,(
    spl16_8 ),
    inference(avatar_split_clause,[],[f3074,f3169])).

fof(f3074,plain,(
    m1_subset_1(sK1,u1_struct_0(sK0)) ),
    inference(cnf_transformation,[],[f3041])).

fof(f3167,plain,
    ( spl16_3
    | spl16_1 ),
    inference(avatar_split_clause,[],[f3075,f3135,f3141])).

fof(f3075,plain,
    ( r2_lattice3(sK0,sK2,sK1)
    | sK1 = k1_yellow_0(sK0,sK2) ),
    inference(cnf_transformation,[],[f3041])).

fof(f3166,plain,
    ( spl16_4
    | spl16_1 ),
    inference(avatar_split_clause,[],[f3076,f3135,f3144])).

fof(f3076,plain,
    ( r2_lattice3(sK0,sK2,sK1)
    | r1_yellow_0(sK0,sK2) ),
    inference(cnf_transformation,[],[f3041])).

fof(f3164,plain,
    ( spl16_3
    | spl16_7 ),
    inference(avatar_split_clause,[],[f3080,f3156,f3141])).

fof(f3080,plain,(
    ! [X3] :
      ( r1_orders_2(sK0,sK1,X3)
      | ~ r2_lattice3(sK0,sK2,X3)
      | ~ m1_subset_1(X3,u1_struct_0(sK0))
      | sK1 = k1_yellow_0(sK0,sK2) ) ),
    inference(cnf_transformation,[],[f3041])).

fof(f3162,plain,
    ( spl16_4
    | spl16_7 ),
    inference(avatar_split_clause,[],[f3081,f3156,f3144])).

fof(f3081,plain,(
    ! [X3] :
      ( r1_orders_2(sK0,sK1,X3)
      | ~ r2_lattice3(sK0,sK2,X3)
      | ~ m1_subset_1(X3,u1_struct_0(sK0))
      | r1_yellow_0(sK0,sK2) ) ),
    inference(cnf_transformation,[],[f3041])).

fof(f3154,plain,
    ( ~ spl16_1
    | spl16_6
    | ~ spl16_3
    | ~ spl16_4 ),
    inference(avatar_split_clause,[],[f3087,f3144,f3141,f3152,f3135])).

fof(f3087,plain,
    ( ~ r1_yellow_0(sK0,sK2)
    | sK1 != k1_yellow_0(sK0,sK2)
    | m1_subset_1(sK3,u1_struct_0(sK0))
    | ~ r2_lattice3(sK0,sK2,sK1) ),
    inference(cnf_transformation,[],[f3041])).

fof(f3150,plain,
    ( ~ spl16_1
    | spl16_5
    | ~ spl16_3
    | ~ spl16_4 ),
    inference(avatar_split_clause,[],[f3088,f3144,f3141,f3148,f3135])).

fof(f3088,plain,
    ( ~ r1_yellow_0(sK0,sK2)
    | sK1 != k1_yellow_0(sK0,sK2)
    | r2_lattice3(sK0,sK2,sK3)
    | ~ r2_lattice3(sK0,sK2,sK1) ),
    inference(cnf_transformation,[],[f3041])).

fof(f3146,plain,
    ( ~ spl16_1
    | ~ spl16_2
    | ~ spl16_3
    | ~ spl16_4 ),
    inference(avatar_split_clause,[],[f3089,f3144,f3141,f3138,f3135])).

fof(f3089,plain,
    ( ~ r1_yellow_0(sK0,sK2)
    | sK1 != k1_yellow_0(sK0,sK2)
    | ~ r1_orders_2(sK0,sK1,sK3)
    | ~ r2_lattice3(sK0,sK2,sK1) ),
    inference(cnf_transformation,[],[f3041])).
%------------------------------------------------------------------------------
