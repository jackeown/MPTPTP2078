%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT1589+2 : TPTP v7.4.0. Released v7.4.0.
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

% Result     : Theorem 1.69s
% Output     : Refutation 1.69s
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
fof(f4087,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f3315,f3319,f3323,f3327,f3331,f3335,f3339,f3343,f3347,f3351,f3359,f4081])).

fof(f4081,plain,
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
    inference(avatar_contradiction_clause,[],[f4080])).

fof(f4080,plain,
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
    inference(subsumption_resolution,[],[f4079,f3358])).

fof(f3358,plain,
    ( ~ v2_struct_0(sK0)
    | spl20_12 ),
    inference(avatar_component_clause,[],[f3357])).

fof(f3357,plain,
    ( spl20_12
  <=> v2_struct_0(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl20_12])])).

fof(f4079,plain,
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
    inference(subsumption_resolution,[],[f4078,f3350])).

fof(f3350,plain,
    ( v4_orders_2(sK0)
    | ~ spl20_10 ),
    inference(avatar_component_clause,[],[f3349])).

fof(f3349,plain,
    ( spl20_10
  <=> v4_orders_2(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl20_10])])).

fof(f4078,plain,
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
    inference(subsumption_resolution,[],[f4077,f3338])).

fof(f3338,plain,
    ( l1_orders_2(sK0)
    | ~ spl20_7 ),
    inference(avatar_component_clause,[],[f3337])).

fof(f3337,plain,
    ( spl20_7
  <=> l1_orders_2(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl20_7])])).

fof(f4077,plain,
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
    inference(subsumption_resolution,[],[f4076,f3334])).

fof(f3334,plain,
    ( ~ v2_struct_0(sK1)
    | spl20_6 ),
    inference(avatar_component_clause,[],[f3333])).

fof(f3333,plain,
    ( spl20_6
  <=> v2_struct_0(sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl20_6])])).

fof(f4076,plain,
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
    inference(subsumption_resolution,[],[f4075,f3330])).

fof(f3330,plain,
    ( v4_yellow_0(sK1,sK0)
    | ~ spl20_5 ),
    inference(avatar_component_clause,[],[f3329])).

fof(f3329,plain,
    ( spl20_5
  <=> v4_yellow_0(sK1,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl20_5])])).

fof(f4075,plain,
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
    inference(subsumption_resolution,[],[f4074,f3326])).

fof(f3326,plain,
    ( m1_yellow_0(sK1,sK0)
    | ~ spl20_4 ),
    inference(avatar_component_clause,[],[f3325])).

fof(f3325,plain,
    ( spl20_4
  <=> m1_yellow_0(sK1,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl20_4])])).

fof(f4074,plain,
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
    inference(subsumption_resolution,[],[f4073,f3322])).

fof(f3322,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK1)))
    | ~ spl20_3 ),
    inference(avatar_component_clause,[],[f3321])).

fof(f3321,plain,
    ( spl20_3
  <=> m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl20_3])])).

fof(f4073,plain,
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
    inference(subsumption_resolution,[],[f4072,f3448])).

fof(f3448,plain,
    ( ! [X0] : r2_yellow_0(sK0,X0)
    | ~ spl20_7
    | ~ spl20_8
    | ~ spl20_9
    | spl20_12 ),
    inference(subsumption_resolution,[],[f3447,f3358])).

fof(f3447,plain,
    ( ! [X0] :
        ( r2_yellow_0(sK0,X0)
        | v2_struct_0(sK0) )
    | ~ spl20_7
    | ~ spl20_8
    | ~ spl20_9 ),
    inference(subsumption_resolution,[],[f3446,f3346])).

fof(f3346,plain,
    ( v5_orders_2(sK0)
    | ~ spl20_9 ),
    inference(avatar_component_clause,[],[f3345])).

fof(f3345,plain,
    ( spl20_9
  <=> v5_orders_2(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl20_9])])).

fof(f3446,plain,
    ( ! [X0] :
        ( r2_yellow_0(sK0,X0)
        | ~ v5_orders_2(sK0)
        | v2_struct_0(sK0) )
    | ~ spl20_7
    | ~ spl20_8 ),
    inference(subsumption_resolution,[],[f3443,f3338])).

fof(f3443,plain,
    ( ! [X0] :
        ( ~ l1_orders_2(sK0)
        | r2_yellow_0(sK0,X0)
        | ~ v5_orders_2(sK0)
        | v2_struct_0(sK0) )
    | ~ spl20_8 ),
    inference(resolution,[],[f3287,f3342])).

fof(f3342,plain,
    ( v3_lattice3(sK0)
    | ~ spl20_8 ),
    inference(avatar_component_clause,[],[f3341])).

fof(f3341,plain,
    ( spl20_8
  <=> v3_lattice3(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl20_8])])).

fof(f3287,plain,(
    ! [X0,X1] :
      ( ~ v3_lattice3(X0)
      | ~ l1_orders_2(X0)
      | r2_yellow_0(X0,X1)
      | ~ v5_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f3137])).

fof(f3137,plain,(
    ! [X0] :
      ( ! [X1] :
          ( r2_yellow_0(X0,X1)
          & r1_yellow_0(X0,X1) )
      | ~ l1_orders_2(X0)
      | ~ v3_lattice3(X0)
      | ~ v5_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f3136])).

fof(f3136,plain,(
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

fof(f4072,plain,
    ( ~ r2_yellow_0(sK0,sK2)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK1)))
    | ~ m1_yellow_0(sK1,sK0)
    | ~ v4_yellow_0(sK1,sK0)
    | v2_struct_0(sK1)
    | ~ l1_orders_2(sK0)
    | ~ v4_orders_2(sK0)
    | v2_struct_0(sK0)
    | spl20_1
    | ~ spl20_2 ),
    inference(subsumption_resolution,[],[f4068,f3314])).

fof(f3314,plain,
    ( k2_yellow_0(sK0,sK2) != k2_yellow_0(sK1,sK2)
    | spl20_1 ),
    inference(avatar_component_clause,[],[f3313])).

fof(f3313,plain,
    ( spl20_1
  <=> k2_yellow_0(sK0,sK2) = k2_yellow_0(sK1,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl20_1])])).

fof(f4068,plain,
    ( k2_yellow_0(sK0,sK2) = k2_yellow_0(sK1,sK2)
    | ~ r2_yellow_0(sK0,sK2)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK1)))
    | ~ m1_yellow_0(sK1,sK0)
    | ~ v4_yellow_0(sK1,sK0)
    | v2_struct_0(sK1)
    | ~ l1_orders_2(sK0)
    | ~ v4_orders_2(sK0)
    | v2_struct_0(sK0)
    | ~ spl20_2 ),
    inference(resolution,[],[f3278,f3318])).

fof(f3318,plain,
    ( r2_hidden(k2_yellow_0(sK0,sK2),u1_struct_0(sK1))
    | ~ spl20_2 ),
    inference(avatar_component_clause,[],[f3317])).

fof(f3317,plain,
    ( spl20_2
  <=> r2_hidden(k2_yellow_0(sK0,sK2),u1_struct_0(sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl20_2])])).

fof(f3278,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(k2_yellow_0(X0,X2),u1_struct_0(X1))
      | k2_yellow_0(X0,X2) = k2_yellow_0(X1,X2)
      | ~ r2_yellow_0(X0,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
      | ~ m1_yellow_0(X1,X0)
      | ~ v4_yellow_0(X1,X0)
      | v2_struct_0(X1)
      | ~ l1_orders_2(X0)
      | ~ v4_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f3128])).

fof(f3128,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( k2_yellow_0(X0,X2) = k2_yellow_0(X1,X2)
                & r2_yellow_0(X1,X2) )
              | ~ r2_hidden(k2_yellow_0(X0,X2),u1_struct_0(X1))
              | ~ r2_yellow_0(X0,X2)
              | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) )
          | ~ m1_yellow_0(X1,X0)
          | ~ v4_yellow_0(X1,X0)
          | v2_struct_0(X1) )
      | ~ l1_orders_2(X0)
      | ~ v4_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f3127])).

fof(f3127,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( k2_yellow_0(X0,X2) = k2_yellow_0(X1,X2)
                & r2_yellow_0(X1,X2) )
              | ~ r2_hidden(k2_yellow_0(X0,X2),u1_struct_0(X1))
              | ~ r2_yellow_0(X0,X2)
              | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) )
          | ~ m1_yellow_0(X1,X0)
          | ~ v4_yellow_0(X1,X0)
          | v2_struct_0(X1) )
      | ~ l1_orders_2(X0)
      | ~ v4_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f3058])).

fof(f3058,axiom,(
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
             => ( ( r2_hidden(k2_yellow_0(X0,X2),u1_struct_0(X1))
                  & r2_yellow_0(X0,X2) )
               => ( k2_yellow_0(X0,X2) = k2_yellow_0(X1,X2)
                  & r2_yellow_0(X1,X2) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t64_yellow_0)).

fof(f3359,plain,(
    ~ spl20_12 ),
    inference(avatar_split_clause,[],[f3199,f3357])).

fof(f3199,plain,(
    ~ v2_struct_0(sK0) ),
    inference(cnf_transformation,[],[f3149])).

fof(f3149,plain,
    ( k2_yellow_0(sK0,sK2) != k2_yellow_0(sK1,sK2)
    & r2_hidden(k2_yellow_0(sK0,sK2),u1_struct_0(sK1))
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
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f3075,f3148,f3147,f3146])).

fof(f3146,plain,
    ( ? [X0] :
        ( ? [X1] :
            ( ? [X2] :
                ( k2_yellow_0(X0,X2) != k2_yellow_0(X1,X2)
                & r2_hidden(k2_yellow_0(X0,X2),u1_struct_0(X1))
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
              ( k2_yellow_0(X1,X2) != k2_yellow_0(sK0,X2)
              & r2_hidden(k2_yellow_0(sK0,X2),u1_struct_0(X1))
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

fof(f3147,plain,
    ( ? [X1] :
        ( ? [X2] :
            ( k2_yellow_0(X1,X2) != k2_yellow_0(sK0,X2)
            & r2_hidden(k2_yellow_0(sK0,X2),u1_struct_0(X1))
            & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) )
        & m1_yellow_0(X1,sK0)
        & v4_yellow_0(X1,sK0)
        & ~ v2_struct_0(X1) )
   => ( ? [X2] :
          ( k2_yellow_0(sK0,X2) != k2_yellow_0(sK1,X2)
          & r2_hidden(k2_yellow_0(sK0,X2),u1_struct_0(sK1))
          & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK1))) )
      & m1_yellow_0(sK1,sK0)
      & v4_yellow_0(sK1,sK0)
      & ~ v2_struct_0(sK1) ) ),
    introduced(choice_axiom,[])).

fof(f3148,plain,
    ( ? [X2] :
        ( k2_yellow_0(sK0,X2) != k2_yellow_0(sK1,X2)
        & r2_hidden(k2_yellow_0(sK0,X2),u1_struct_0(sK1))
        & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK1))) )
   => ( k2_yellow_0(sK0,sK2) != k2_yellow_0(sK1,sK2)
      & r2_hidden(k2_yellow_0(sK0,sK2),u1_struct_0(sK1))
      & m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK1))) ) ),
    introduced(choice_axiom,[])).

fof(f3075,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( k2_yellow_0(X0,X2) != k2_yellow_0(X1,X2)
              & r2_hidden(k2_yellow_0(X0,X2),u1_struct_0(X1))
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
    inference(flattening,[],[f3074])).

fof(f3074,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( k2_yellow_0(X0,X2) != k2_yellow_0(X1,X2)
              & r2_hidden(k2_yellow_0(X0,X2),u1_struct_0(X1))
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
    inference(ennf_transformation,[],[f3063])).

fof(f3063,negated_conjecture,(
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
               => ( r2_hidden(k2_yellow_0(X0,X2),u1_struct_0(X1))
                 => k2_yellow_0(X0,X2) = k2_yellow_0(X1,X2) ) ) ) ) ),
    inference(negated_conjecture,[],[f3062])).

fof(f3062,conjecture,(
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
             => ( r2_hidden(k2_yellow_0(X0,X2),u1_struct_0(X1))
               => k2_yellow_0(X0,X2) = k2_yellow_0(X1,X2) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t68_yellow_0)).

fof(f3351,plain,(
    spl20_10 ),
    inference(avatar_split_clause,[],[f3201,f3349])).

fof(f3201,plain,(
    v4_orders_2(sK0) ),
    inference(cnf_transformation,[],[f3149])).

fof(f3347,plain,(
    spl20_9 ),
    inference(avatar_split_clause,[],[f3202,f3345])).

fof(f3202,plain,(
    v5_orders_2(sK0) ),
    inference(cnf_transformation,[],[f3149])).

fof(f3343,plain,(
    spl20_8 ),
    inference(avatar_split_clause,[],[f3203,f3341])).

fof(f3203,plain,(
    v3_lattice3(sK0) ),
    inference(cnf_transformation,[],[f3149])).

fof(f3339,plain,(
    spl20_7 ),
    inference(avatar_split_clause,[],[f3204,f3337])).

fof(f3204,plain,(
    l1_orders_2(sK0) ),
    inference(cnf_transformation,[],[f3149])).

fof(f3335,plain,(
    ~ spl20_6 ),
    inference(avatar_split_clause,[],[f3205,f3333])).

fof(f3205,plain,(
    ~ v2_struct_0(sK1) ),
    inference(cnf_transformation,[],[f3149])).

fof(f3331,plain,(
    spl20_5 ),
    inference(avatar_split_clause,[],[f3206,f3329])).

fof(f3206,plain,(
    v4_yellow_0(sK1,sK0) ),
    inference(cnf_transformation,[],[f3149])).

fof(f3327,plain,(
    spl20_4 ),
    inference(avatar_split_clause,[],[f3207,f3325])).

fof(f3207,plain,(
    m1_yellow_0(sK1,sK0) ),
    inference(cnf_transformation,[],[f3149])).

fof(f3323,plain,(
    spl20_3 ),
    inference(avatar_split_clause,[],[f3208,f3321])).

fof(f3208,plain,(
    m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK1))) ),
    inference(cnf_transformation,[],[f3149])).

fof(f3319,plain,(
    spl20_2 ),
    inference(avatar_split_clause,[],[f3209,f3317])).

fof(f3209,plain,(
    r2_hidden(k2_yellow_0(sK0,sK2),u1_struct_0(sK1)) ),
    inference(cnf_transformation,[],[f3149])).

fof(f3315,plain,(
    ~ spl20_1 ),
    inference(avatar_split_clause,[],[f3210,f3313])).

fof(f3210,plain,(
    k2_yellow_0(sK0,sK2) != k2_yellow_0(sK1,sK2) ),
    inference(cnf_transformation,[],[f3149])).
%------------------------------------------------------------------------------
