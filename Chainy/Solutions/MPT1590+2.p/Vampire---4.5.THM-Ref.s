%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT1590+2 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n022.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Wed Dec 16 12:10:26 EST 2020

% Result     : Theorem 1.16s
% Output     : Refutation 1.16s
% Verified   : 
% Statistics : Number of formulae       :   76 ( 171 expanded)
%              Number of leaves         :   17 (  70 expanded)
%              Depth                    :   17
%              Number of atoms          :  387 (1437 expanded)
%              Number of equality atoms :   19 ( 130 expanded)
%              Maximal formula depth    :   14 (   5 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f4121,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f3324,f3328,f3332,f3336,f3340,f3344,f3348,f3352,f3356,f3360,f3368,f4103])).

fof(f4103,plain,
    ( spl20_1
    | ~ spl20_2
    | ~ spl20_3
    | ~ spl20_4
    | ~ spl20_5
    | spl20_6
    | ~ spl20_7
    | ~ spl20_8
    | ~ spl20_9
    | ~ spl20_10
    | spl20_12 ),
    inference(avatar_contradiction_clause,[],[f4102])).

fof(f4102,plain,
    ( $false
    | spl20_1
    | ~ spl20_2
    | ~ spl20_3
    | ~ spl20_4
    | ~ spl20_5
    | spl20_6
    | ~ spl20_7
    | ~ spl20_8
    | ~ spl20_9
    | ~ spl20_10
    | spl20_12 ),
    inference(subsumption_resolution,[],[f4101,f3367])).

fof(f3367,plain,
    ( ~ v2_struct_0(sK0)
    | spl20_12 ),
    inference(avatar_component_clause,[],[f3366])).

fof(f3366,plain,
    ( spl20_12
  <=> v2_struct_0(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl20_12])])).

fof(f4101,plain,
    ( v2_struct_0(sK0)
    | spl20_1
    | ~ spl20_2
    | ~ spl20_3
    | ~ spl20_4
    | ~ spl20_5
    | spl20_6
    | ~ spl20_7
    | ~ spl20_8
    | ~ spl20_9
    | ~ spl20_10
    | spl20_12 ),
    inference(subsumption_resolution,[],[f4100,f3359])).

fof(f3359,plain,
    ( v4_orders_2(sK0)
    | ~ spl20_10 ),
    inference(avatar_component_clause,[],[f3358])).

fof(f3358,plain,
    ( spl20_10
  <=> v4_orders_2(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl20_10])])).

fof(f4100,plain,
    ( ~ v4_orders_2(sK0)
    | v2_struct_0(sK0)
    | spl20_1
    | ~ spl20_2
    | ~ spl20_3
    | ~ spl20_4
    | ~ spl20_5
    | spl20_6
    | ~ spl20_7
    | ~ spl20_8
    | ~ spl20_9
    | spl20_12 ),
    inference(subsumption_resolution,[],[f4099,f3347])).

fof(f3347,plain,
    ( l1_orders_2(sK0)
    | ~ spl20_7 ),
    inference(avatar_component_clause,[],[f3346])).

fof(f3346,plain,
    ( spl20_7
  <=> l1_orders_2(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl20_7])])).

fof(f4099,plain,
    ( ~ l1_orders_2(sK0)
    | ~ v4_orders_2(sK0)
    | v2_struct_0(sK0)
    | spl20_1
    | ~ spl20_2
    | ~ spl20_3
    | ~ spl20_4
    | ~ spl20_5
    | spl20_6
    | ~ spl20_7
    | ~ spl20_8
    | ~ spl20_9
    | spl20_12 ),
    inference(subsumption_resolution,[],[f4098,f3343])).

fof(f3343,plain,
    ( ~ v2_struct_0(sK1)
    | spl20_6 ),
    inference(avatar_component_clause,[],[f3342])).

fof(f3342,plain,
    ( spl20_6
  <=> v2_struct_0(sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl20_6])])).

fof(f4098,plain,
    ( v2_struct_0(sK1)
    | ~ l1_orders_2(sK0)
    | ~ v4_orders_2(sK0)
    | v2_struct_0(sK0)
    | spl20_1
    | ~ spl20_2
    | ~ spl20_3
    | ~ spl20_4
    | ~ spl20_5
    | ~ spl20_7
    | ~ spl20_8
    | ~ spl20_9
    | spl20_12 ),
    inference(subsumption_resolution,[],[f4097,f3339])).

fof(f3339,plain,
    ( v4_yellow_0(sK1,sK0)
    | ~ spl20_5 ),
    inference(avatar_component_clause,[],[f3338])).

fof(f3338,plain,
    ( spl20_5
  <=> v4_yellow_0(sK1,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl20_5])])).

fof(f4097,plain,
    ( ~ v4_yellow_0(sK1,sK0)
    | v2_struct_0(sK1)
    | ~ l1_orders_2(sK0)
    | ~ v4_orders_2(sK0)
    | v2_struct_0(sK0)
    | spl20_1
    | ~ spl20_2
    | ~ spl20_3
    | ~ spl20_4
    | ~ spl20_7
    | ~ spl20_8
    | ~ spl20_9
    | spl20_12 ),
    inference(subsumption_resolution,[],[f4096,f3335])).

fof(f3335,plain,
    ( m1_yellow_0(sK1,sK0)
    | ~ spl20_4 ),
    inference(avatar_component_clause,[],[f3334])).

fof(f3334,plain,
    ( spl20_4
  <=> m1_yellow_0(sK1,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl20_4])])).

fof(f4096,plain,
    ( ~ m1_yellow_0(sK1,sK0)
    | ~ v4_yellow_0(sK1,sK0)
    | v2_struct_0(sK1)
    | ~ l1_orders_2(sK0)
    | ~ v4_orders_2(sK0)
    | v2_struct_0(sK0)
    | spl20_1
    | ~ spl20_2
    | ~ spl20_3
    | ~ spl20_7
    | ~ spl20_8
    | ~ spl20_9
    | spl20_12 ),
    inference(subsumption_resolution,[],[f4095,f3331])).

fof(f3331,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK1)))
    | ~ spl20_3 ),
    inference(avatar_component_clause,[],[f3330])).

fof(f3330,plain,
    ( spl20_3
  <=> m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl20_3])])).

fof(f4095,plain,
    ( ~ m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK1)))
    | ~ m1_yellow_0(sK1,sK0)
    | ~ v4_yellow_0(sK1,sK0)
    | v2_struct_0(sK1)
    | ~ l1_orders_2(sK0)
    | ~ v4_orders_2(sK0)
    | v2_struct_0(sK0)
    | spl20_1
    | ~ spl20_2
    | ~ spl20_7
    | ~ spl20_8
    | ~ spl20_9
    | spl20_12 ),
    inference(subsumption_resolution,[],[f4094,f3451])).

fof(f3451,plain,
    ( ! [X0] : r1_yellow_0(sK0,X0)
    | ~ spl20_7
    | ~ spl20_8
    | ~ spl20_9
    | spl20_12 ),
    inference(subsumption_resolution,[],[f3450,f3367])).

fof(f3450,plain,
    ( ! [X0] :
        ( r1_yellow_0(sK0,X0)
        | v2_struct_0(sK0) )
    | ~ spl20_7
    | ~ spl20_8
    | ~ spl20_9 ),
    inference(subsumption_resolution,[],[f3449,f3355])).

fof(f3355,plain,
    ( v5_orders_2(sK0)
    | ~ spl20_9 ),
    inference(avatar_component_clause,[],[f3354])).

fof(f3354,plain,
    ( spl20_9
  <=> v5_orders_2(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl20_9])])).

fof(f3449,plain,
    ( ! [X0] :
        ( r1_yellow_0(sK0,X0)
        | ~ v5_orders_2(sK0)
        | v2_struct_0(sK0) )
    | ~ spl20_7
    | ~ spl20_8 ),
    inference(subsumption_resolution,[],[f3446,f3347])).

fof(f3446,plain,
    ( ! [X0] :
        ( ~ l1_orders_2(sK0)
        | r1_yellow_0(sK0,X0)
        | ~ v5_orders_2(sK0)
        | v2_struct_0(sK0) )
    | ~ spl20_8 ),
    inference(resolution,[],[f3295,f3351])).

fof(f3351,plain,
    ( v3_lattice3(sK0)
    | ~ spl20_8 ),
    inference(avatar_component_clause,[],[f3350])).

fof(f3350,plain,
    ( spl20_8
  <=> v3_lattice3(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl20_8])])).

fof(f3295,plain,(
    ! [X0,X1] :
      ( ~ v3_lattice3(X0)
      | ~ l1_orders_2(X0)
      | r1_yellow_0(X0,X1)
      | ~ v5_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f3143])).

fof(f3143,plain,(
    ! [X0] :
      ( ! [X1] :
          ( r2_yellow_0(X0,X1)
          & r1_yellow_0(X0,X1) )
      | ~ l1_orders_2(X0)
      | ~ v3_lattice3(X0)
      | ~ v5_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f3142])).

fof(f3142,plain,(
    ! [X0] :
      ( ! [X1] :
          ( r2_yellow_0(X0,X1)
          & r1_yellow_0(X0,X1) )
      | ~ l1_orders_2(X0)
      | ~ v3_lattice3(X0)
      | ~ v5_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f3007])).

fof(f3007,axiom,(
    ! [X0] :
      ( ( l1_orders_2(X0)
        & v3_lattice3(X0)
        & v5_orders_2(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( r2_yellow_0(X0,X1)
          & r1_yellow_0(X0,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t17_yellow_0)).

fof(f4094,plain,
    ( ~ r1_yellow_0(sK0,sK2)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK1)))
    | ~ m1_yellow_0(sK1,sK0)
    | ~ v4_yellow_0(sK1,sK0)
    | v2_struct_0(sK1)
    | ~ l1_orders_2(sK0)
    | ~ v4_orders_2(sK0)
    | v2_struct_0(sK0)
    | spl20_1
    | ~ spl20_2 ),
    inference(subsumption_resolution,[],[f4087,f3323])).

fof(f3323,plain,
    ( k1_yellow_0(sK0,sK2) != k1_yellow_0(sK1,sK2)
    | spl20_1 ),
    inference(avatar_component_clause,[],[f3322])).

fof(f3322,plain,
    ( spl20_1
  <=> k1_yellow_0(sK0,sK2) = k1_yellow_0(sK1,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl20_1])])).

fof(f4087,plain,
    ( k1_yellow_0(sK0,sK2) = k1_yellow_0(sK1,sK2)
    | ~ r1_yellow_0(sK0,sK2)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK1)))
    | ~ m1_yellow_0(sK1,sK0)
    | ~ v4_yellow_0(sK1,sK0)
    | v2_struct_0(sK1)
    | ~ l1_orders_2(sK0)
    | ~ v4_orders_2(sK0)
    | v2_struct_0(sK0)
    | ~ spl20_2 ),
    inference(resolution,[],[f3285,f3327])).

fof(f3327,plain,
    ( r2_hidden(k1_yellow_0(sK0,sK2),u1_struct_0(sK1))
    | ~ spl20_2 ),
    inference(avatar_component_clause,[],[f3326])).

fof(f3326,plain,
    ( spl20_2
  <=> r2_hidden(k1_yellow_0(sK0,sK2),u1_struct_0(sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl20_2])])).

fof(f3285,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(k1_yellow_0(X0,X2),u1_struct_0(X1))
      | k1_yellow_0(X0,X2) = k1_yellow_0(X1,X2)
      | ~ r1_yellow_0(X0,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
      | ~ m1_yellow_0(X1,X0)
      | ~ v4_yellow_0(X1,X0)
      | v2_struct_0(X1)
      | ~ l1_orders_2(X0)
      | ~ v4_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f3132])).

fof(f3132,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( k1_yellow_0(X0,X2) = k1_yellow_0(X1,X2)
                & r1_yellow_0(X1,X2) )
              | ~ r2_hidden(k1_yellow_0(X0,X2),u1_struct_0(X1))
              | ~ r1_yellow_0(X0,X2)
              | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) )
          | ~ m1_yellow_0(X1,X0)
          | ~ v4_yellow_0(X1,X0)
          | v2_struct_0(X1) )
      | ~ l1_orders_2(X0)
      | ~ v4_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f3131])).

fof(f3131,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( k1_yellow_0(X0,X2) = k1_yellow_0(X1,X2)
                & r1_yellow_0(X1,X2) )
              | ~ r2_hidden(k1_yellow_0(X0,X2),u1_struct_0(X1))
              | ~ r1_yellow_0(X0,X2)
              | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) )
          | ~ m1_yellow_0(X1,X0)
          | ~ v4_yellow_0(X1,X0)
          | v2_struct_0(X1) )
      | ~ l1_orders_2(X0)
      | ~ v4_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f3059])).

fof(f3059,axiom,(
    ! [X0] :
      ( ( l1_orders_2(X0)
        & v4_orders_2(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( ( m1_yellow_0(X1,X0)
            & v4_yellow_0(X1,X0)
            & ~ v2_struct_0(X1) )
         => ! [X2] :
              ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
             => ( ( r2_hidden(k1_yellow_0(X0,X2),u1_struct_0(X1))
                  & r1_yellow_0(X0,X2) )
               => ( k1_yellow_0(X0,X2) = k1_yellow_0(X1,X2)
                  & r1_yellow_0(X1,X2) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t65_yellow_0)).

fof(f3368,plain,(
    ~ spl20_12 ),
    inference(avatar_split_clause,[],[f3205,f3366])).

fof(f3205,plain,(
    ~ v2_struct_0(sK0) ),
    inference(cnf_transformation,[],[f3155])).

fof(f3155,plain,
    ( k1_yellow_0(sK0,sK2) != k1_yellow_0(sK1,sK2)
    & r2_hidden(k1_yellow_0(sK0,sK2),u1_struct_0(sK1))
    & m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK1)))
    & m1_yellow_0(sK1,sK0)
    & v4_yellow_0(sK1,sK0)
    & ~ v2_struct_0(sK1)
    & l1_orders_2(sK0)
    & v3_lattice3(sK0)
    & v5_orders_2(sK0)
    & v4_orders_2(sK0)
    & v3_orders_2(sK0)
    & ~ v2_struct_0(sK0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f3077,f3154,f3153,f3152])).

fof(f3152,plain,
    ( ? [X0] :
        ( ? [X1] :
            ( ? [X2] :
                ( k1_yellow_0(X0,X2) != k1_yellow_0(X1,X2)
                & r2_hidden(k1_yellow_0(X0,X2),u1_struct_0(X1))
                & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) )
            & m1_yellow_0(X1,X0)
            & v4_yellow_0(X1,X0)
            & ~ v2_struct_0(X1) )
        & l1_orders_2(X0)
        & v3_lattice3(X0)
        & v5_orders_2(X0)
        & v4_orders_2(X0)
        & v3_orders_2(X0)
        & ~ v2_struct_0(X0) )
   => ( ? [X1] :
          ( ? [X2] :
              ( k1_yellow_0(X1,X2) != k1_yellow_0(sK0,X2)
              & r2_hidden(k1_yellow_0(sK0,X2),u1_struct_0(X1))
              & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) )
          & m1_yellow_0(X1,sK0)
          & v4_yellow_0(X1,sK0)
          & ~ v2_struct_0(X1) )
      & l1_orders_2(sK0)
      & v3_lattice3(sK0)
      & v5_orders_2(sK0)
      & v4_orders_2(sK0)
      & v3_orders_2(sK0)
      & ~ v2_struct_0(sK0) ) ),
    introduced(choice_axiom,[])).

fof(f3153,plain,
    ( ? [X1] :
        ( ? [X2] :
            ( k1_yellow_0(X1,X2) != k1_yellow_0(sK0,X2)
            & r2_hidden(k1_yellow_0(sK0,X2),u1_struct_0(X1))
            & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) )
        & m1_yellow_0(X1,sK0)
        & v4_yellow_0(X1,sK0)
        & ~ v2_struct_0(X1) )
   => ( ? [X2] :
          ( k1_yellow_0(sK0,X2) != k1_yellow_0(sK1,X2)
          & r2_hidden(k1_yellow_0(sK0,X2),u1_struct_0(sK1))
          & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK1))) )
      & m1_yellow_0(sK1,sK0)
      & v4_yellow_0(sK1,sK0)
      & ~ v2_struct_0(sK1) ) ),
    introduced(choice_axiom,[])).

fof(f3154,plain,
    ( ? [X2] :
        ( k1_yellow_0(sK0,X2) != k1_yellow_0(sK1,X2)
        & r2_hidden(k1_yellow_0(sK0,X2),u1_struct_0(sK1))
        & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK1))) )
   => ( k1_yellow_0(sK0,sK2) != k1_yellow_0(sK1,sK2)
      & r2_hidden(k1_yellow_0(sK0,sK2),u1_struct_0(sK1))
      & m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK1))) ) ),
    introduced(choice_axiom,[])).

fof(f3077,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( k1_yellow_0(X0,X2) != k1_yellow_0(X1,X2)
              & r2_hidden(k1_yellow_0(X0,X2),u1_struct_0(X1))
              & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) )
          & m1_yellow_0(X1,X0)
          & v4_yellow_0(X1,X0)
          & ~ v2_struct_0(X1) )
      & l1_orders_2(X0)
      & v3_lattice3(X0)
      & v5_orders_2(X0)
      & v4_orders_2(X0)
      & v3_orders_2(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(flattening,[],[f3076])).

fof(f3076,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( k1_yellow_0(X0,X2) != k1_yellow_0(X1,X2)
              & r2_hidden(k1_yellow_0(X0,X2),u1_struct_0(X1))
              & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) )
          & m1_yellow_0(X1,X0)
          & v4_yellow_0(X1,X0)
          & ~ v2_struct_0(X1) )
      & l1_orders_2(X0)
      & v3_lattice3(X0)
      & v5_orders_2(X0)
      & v4_orders_2(X0)
      & v3_orders_2(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f3064])).

fof(f3064,negated_conjecture,(
    ~ ! [X0] :
        ( ( l1_orders_2(X0)
          & v3_lattice3(X0)
          & v5_orders_2(X0)
          & v4_orders_2(X0)
          & v3_orders_2(X0)
          & ~ v2_struct_0(X0) )
       => ! [X1] :
            ( ( m1_yellow_0(X1,X0)
              & v4_yellow_0(X1,X0)
              & ~ v2_struct_0(X1) )
           => ! [X2] :
                ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
               => ( r2_hidden(k1_yellow_0(X0,X2),u1_struct_0(X1))
                 => k1_yellow_0(X0,X2) = k1_yellow_0(X1,X2) ) ) ) ) ),
    inference(negated_conjecture,[],[f3063])).

fof(f3063,conjecture,(
    ! [X0] :
      ( ( l1_orders_2(X0)
        & v3_lattice3(X0)
        & v5_orders_2(X0)
        & v4_orders_2(X0)
        & v3_orders_2(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( ( m1_yellow_0(X1,X0)
            & v4_yellow_0(X1,X0)
            & ~ v2_struct_0(X1) )
         => ! [X2] :
              ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
             => ( r2_hidden(k1_yellow_0(X0,X2),u1_struct_0(X1))
               => k1_yellow_0(X0,X2) = k1_yellow_0(X1,X2) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t69_yellow_0)).

fof(f3360,plain,(
    spl20_10 ),
    inference(avatar_split_clause,[],[f3207,f3358])).

fof(f3207,plain,(
    v4_orders_2(sK0) ),
    inference(cnf_transformation,[],[f3155])).

fof(f3356,plain,(
    spl20_9 ),
    inference(avatar_split_clause,[],[f3208,f3354])).

fof(f3208,plain,(
    v5_orders_2(sK0) ),
    inference(cnf_transformation,[],[f3155])).

fof(f3352,plain,(
    spl20_8 ),
    inference(avatar_split_clause,[],[f3209,f3350])).

fof(f3209,plain,(
    v3_lattice3(sK0) ),
    inference(cnf_transformation,[],[f3155])).

fof(f3348,plain,(
    spl20_7 ),
    inference(avatar_split_clause,[],[f3210,f3346])).

fof(f3210,plain,(
    l1_orders_2(sK0) ),
    inference(cnf_transformation,[],[f3155])).

fof(f3344,plain,(
    ~ spl20_6 ),
    inference(avatar_split_clause,[],[f3211,f3342])).

fof(f3211,plain,(
    ~ v2_struct_0(sK1) ),
    inference(cnf_transformation,[],[f3155])).

fof(f3340,plain,(
    spl20_5 ),
    inference(avatar_split_clause,[],[f3212,f3338])).

fof(f3212,plain,(
    v4_yellow_0(sK1,sK0) ),
    inference(cnf_transformation,[],[f3155])).

fof(f3336,plain,(
    spl20_4 ),
    inference(avatar_split_clause,[],[f3213,f3334])).

fof(f3213,plain,(
    m1_yellow_0(sK1,sK0) ),
    inference(cnf_transformation,[],[f3155])).

fof(f3332,plain,(
    spl20_3 ),
    inference(avatar_split_clause,[],[f3214,f3330])).

fof(f3214,plain,(
    m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK1))) ),
    inference(cnf_transformation,[],[f3155])).

fof(f3328,plain,(
    spl20_2 ),
    inference(avatar_split_clause,[],[f3215,f3326])).

fof(f3215,plain,(
    r2_hidden(k1_yellow_0(sK0,sK2),u1_struct_0(sK1)) ),
    inference(cnf_transformation,[],[f3155])).

fof(f3324,plain,(
    ~ spl20_1 ),
    inference(avatar_split_clause,[],[f3216,f3322])).

fof(f3216,plain,(
    k1_yellow_0(sK0,sK2) != k1_yellow_0(sK1,sK2) ),
    inference(cnf_transformation,[],[f3155])).
%------------------------------------------------------------------------------
