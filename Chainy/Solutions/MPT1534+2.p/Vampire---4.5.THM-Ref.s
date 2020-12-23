%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT1534+2 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n011.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Wed Dec 16 12:10:23 EST 2020

% Result     : Theorem 0.75s
% Output     : Refutation 0.75s
% Verified   : 
% Statistics : Number of formulae       :   43 (  98 expanded)
%              Number of leaves         :   12 (  43 expanded)
%              Depth                    :    7
%              Number of atoms          :  159 ( 575 expanded)
%              Number of equality atoms :    0 (   0 expanded)
%              Maximal formula depth    :   12 (   4 average)
%              Maximal term depth       :    2 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f3128,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f3050,f3054,f3058,f3062,f3066,f3070,f3074,f3126])).

fof(f3126,plain,
    ( spl7_1
    | ~ spl7_2
    | ~ spl7_3
    | ~ spl7_4
    | ~ spl7_5
    | ~ spl7_6
    | ~ spl7_7 ),
    inference(avatar_contradiction_clause,[],[f3124])).

fof(f3124,plain,
    ( $false
    | spl7_1
    | ~ spl7_2
    | ~ spl7_3
    | ~ spl7_4
    | ~ spl7_5
    | ~ spl7_6
    | ~ spl7_7 ),
    inference(unit_resulting_resolution,[],[f3073,f3069,f3049,f3061,f3053,f3057,f3065,f3021])).

fof(f3021,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ v4_orders_2(X0)
      | ~ r1_lattice3(X0,X3,X2)
      | ~ r1_orders_2(X0,X1,X2)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | r1_lattice3(X0,X3,X1) ) ),
    inference(cnf_transformation,[],[f2987])).

fof(f2987,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( ( r2_lattice3(X0,X3,X2)
                    | ~ r2_lattice3(X0,X3,X1) )
                  & ( r1_lattice3(X0,X3,X1)
                    | ~ r1_lattice3(X0,X3,X2) ) )
              | ~ r1_orders_2(X0,X1,X2)
              | ~ m1_subset_1(X2,u1_struct_0(X0)) )
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l1_orders_2(X0)
      | ~ v4_orders_2(X0) ) ),
    inference(flattening,[],[f2986])).

fof(f2986,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( ( r2_lattice3(X0,X3,X2)
                    | ~ r2_lattice3(X0,X3,X1) )
                  & ( r1_lattice3(X0,X3,X1)
                    | ~ r1_lattice3(X0,X3,X2) ) )
              | ~ r1_orders_2(X0,X1,X2)
              | ~ m1_subset_1(X2,u1_struct_0(X0)) )
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l1_orders_2(X0)
      | ~ v4_orders_2(X0) ) ),
    inference(ennf_transformation,[],[f2970])).

fof(f2970,axiom,(
    ! [X0] :
      ( ( l1_orders_2(X0)
        & v4_orders_2(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,u1_struct_0(X0))
         => ! [X2] :
              ( m1_subset_1(X2,u1_struct_0(X0))
             => ( r1_orders_2(X0,X1,X2)
               => ! [X3] :
                    ( ( r2_lattice3(X0,X3,X1)
                     => r2_lattice3(X0,X3,X2) )
                    & ( r1_lattice3(X0,X3,X2)
                     => r1_lattice3(X0,X3,X1) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_yellow_0)).

fof(f3065,plain,
    ( m1_subset_1(sK2,u1_struct_0(sK0))
    | ~ spl7_5 ),
    inference(avatar_component_clause,[],[f3064])).

fof(f3064,plain,
    ( spl7_5
  <=> m1_subset_1(sK2,u1_struct_0(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_5])])).

fof(f3057,plain,
    ( r1_lattice3(sK0,sK1,sK2)
    | ~ spl7_3 ),
    inference(avatar_component_clause,[],[f3056])).

fof(f3056,plain,
    ( spl7_3
  <=> r1_lattice3(sK0,sK1,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_3])])).

fof(f3053,plain,
    ( r1_orders_2(sK0,sK3,sK2)
    | ~ spl7_2 ),
    inference(avatar_component_clause,[],[f3052])).

fof(f3052,plain,
    ( spl7_2
  <=> r1_orders_2(sK0,sK3,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_2])])).

fof(f3061,plain,
    ( m1_subset_1(sK3,u1_struct_0(sK0))
    | ~ spl7_4 ),
    inference(avatar_component_clause,[],[f3060])).

fof(f3060,plain,
    ( spl7_4
  <=> m1_subset_1(sK3,u1_struct_0(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_4])])).

fof(f3049,plain,
    ( ~ r1_lattice3(sK0,sK1,sK3)
    | spl7_1 ),
    inference(avatar_component_clause,[],[f3048])).

fof(f3048,plain,
    ( spl7_1
  <=> r1_lattice3(sK0,sK1,sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_1])])).

fof(f3069,plain,
    ( l1_orders_2(sK0)
    | ~ spl7_6 ),
    inference(avatar_component_clause,[],[f3068])).

fof(f3068,plain,
    ( spl7_6
  <=> l1_orders_2(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_6])])).

fof(f3073,plain,
    ( v4_orders_2(sK0)
    | ~ spl7_7 ),
    inference(avatar_component_clause,[],[f3072])).

fof(f3072,plain,
    ( spl7_7
  <=> v4_orders_2(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_7])])).

fof(f3074,plain,(
    spl7_7 ),
    inference(avatar_split_clause,[],[f3011,f3072])).

fof(f3011,plain,(
    v4_orders_2(sK0) ),
    inference(cnf_transformation,[],[f3001])).

fof(f3001,plain,
    ( ~ r1_lattice3(sK0,sK1,sK3)
    & r1_orders_2(sK0,sK3,sK2)
    & r1_lattice3(sK0,sK1,sK2)
    & m1_subset_1(sK3,u1_struct_0(sK0))
    & m1_subset_1(sK2,u1_struct_0(sK0))
    & l1_orders_2(sK0)
    & v4_orders_2(sK0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3])],[f2982,f3000,f2999,f2998])).

fof(f2998,plain,
    ( ? [X0] :
        ( ? [X1,X2] :
            ( ? [X3] :
                ( ~ r1_lattice3(X0,X1,X3)
                & r1_orders_2(X0,X3,X2)
                & r1_lattice3(X0,X1,X2)
                & m1_subset_1(X3,u1_struct_0(X0)) )
            & m1_subset_1(X2,u1_struct_0(X0)) )
        & l1_orders_2(X0)
        & v4_orders_2(X0) )
   => ( ? [X2,X1] :
          ( ? [X3] :
              ( ~ r1_lattice3(sK0,X1,X3)
              & r1_orders_2(sK0,X3,X2)
              & r1_lattice3(sK0,X1,X2)
              & m1_subset_1(X3,u1_struct_0(sK0)) )
          & m1_subset_1(X2,u1_struct_0(sK0)) )
      & l1_orders_2(sK0)
      & v4_orders_2(sK0) ) ),
    introduced(choice_axiom,[])).

fof(f2999,plain,
    ( ? [X2,X1] :
        ( ? [X3] :
            ( ~ r1_lattice3(sK0,X1,X3)
            & r1_orders_2(sK0,X3,X2)
            & r1_lattice3(sK0,X1,X2)
            & m1_subset_1(X3,u1_struct_0(sK0)) )
        & m1_subset_1(X2,u1_struct_0(sK0)) )
   => ( ? [X3] :
          ( ~ r1_lattice3(sK0,sK1,X3)
          & r1_orders_2(sK0,X3,sK2)
          & r1_lattice3(sK0,sK1,sK2)
          & m1_subset_1(X3,u1_struct_0(sK0)) )
      & m1_subset_1(sK2,u1_struct_0(sK0)) ) ),
    introduced(choice_axiom,[])).

fof(f3000,plain,
    ( ? [X3] :
        ( ~ r1_lattice3(sK0,sK1,X3)
        & r1_orders_2(sK0,X3,sK2)
        & r1_lattice3(sK0,sK1,sK2)
        & m1_subset_1(X3,u1_struct_0(sK0)) )
   => ( ~ r1_lattice3(sK0,sK1,sK3)
      & r1_orders_2(sK0,sK3,sK2)
      & r1_lattice3(sK0,sK1,sK2)
      & m1_subset_1(sK3,u1_struct_0(sK0)) ) ),
    introduced(choice_axiom,[])).

fof(f2982,plain,(
    ? [X0] :
      ( ? [X1,X2] :
          ( ? [X3] :
              ( ~ r1_lattice3(X0,X1,X3)
              & r1_orders_2(X0,X3,X2)
              & r1_lattice3(X0,X1,X2)
              & m1_subset_1(X3,u1_struct_0(X0)) )
          & m1_subset_1(X2,u1_struct_0(X0)) )
      & l1_orders_2(X0)
      & v4_orders_2(X0) ) ),
    inference(flattening,[],[f2981])).

fof(f2981,plain,(
    ? [X0] :
      ( ? [X1,X2] :
          ( ? [X3] :
              ( ~ r1_lattice3(X0,X1,X3)
              & r1_orders_2(X0,X3,X2)
              & r1_lattice3(X0,X1,X2)
              & m1_subset_1(X3,u1_struct_0(X0)) )
          & m1_subset_1(X2,u1_struct_0(X0)) )
      & l1_orders_2(X0)
      & v4_orders_2(X0) ) ),
    inference(ennf_transformation,[],[f2966])).

fof(f2966,negated_conjecture,(
    ~ ! [X0] :
        ( ( l1_orders_2(X0)
          & v4_orders_2(X0) )
       => ! [X1,X2] :
            ( m1_subset_1(X2,u1_struct_0(X0))
           => ! [X3] :
                ( m1_subset_1(X3,u1_struct_0(X0))
               => ( ( r1_orders_2(X0,X3,X2)
                    & r1_lattice3(X0,X1,X2) )
                 => r1_lattice3(X0,X1,X3) ) ) ) ) ),
    inference(negated_conjecture,[],[f2965])).

fof(f2965,conjecture,(
    ! [X0] :
      ( ( l1_orders_2(X0)
        & v4_orders_2(X0) )
     => ! [X1,X2] :
          ( m1_subset_1(X2,u1_struct_0(X0))
         => ! [X3] :
              ( m1_subset_1(X3,u1_struct_0(X0))
             => ( ( r1_orders_2(X0,X3,X2)
                  & r1_lattice3(X0,X1,X2) )
               => r1_lattice3(X0,X1,X3) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t12_yellow_0)).

fof(f3070,plain,(
    spl7_6 ),
    inference(avatar_split_clause,[],[f3012,f3068])).

fof(f3012,plain,(
    l1_orders_2(sK0) ),
    inference(cnf_transformation,[],[f3001])).

fof(f3066,plain,(
    spl7_5 ),
    inference(avatar_split_clause,[],[f3013,f3064])).

fof(f3013,plain,(
    m1_subset_1(sK2,u1_struct_0(sK0)) ),
    inference(cnf_transformation,[],[f3001])).

fof(f3062,plain,(
    spl7_4 ),
    inference(avatar_split_clause,[],[f3014,f3060])).

fof(f3014,plain,(
    m1_subset_1(sK3,u1_struct_0(sK0)) ),
    inference(cnf_transformation,[],[f3001])).

fof(f3058,plain,(
    spl7_3 ),
    inference(avatar_split_clause,[],[f3015,f3056])).

fof(f3015,plain,(
    r1_lattice3(sK0,sK1,sK2) ),
    inference(cnf_transformation,[],[f3001])).

fof(f3054,plain,(
    spl7_2 ),
    inference(avatar_split_clause,[],[f3016,f3052])).

fof(f3016,plain,(
    r1_orders_2(sK0,sK3,sK2) ),
    inference(cnf_transformation,[],[f3001])).

fof(f3050,plain,(
    ~ spl7_1 ),
    inference(avatar_split_clause,[],[f3017,f3048])).

fof(f3017,plain,(
    ~ r1_lattice3(sK0,sK1,sK3) ),
    inference(cnf_transformation,[],[f3001])).
%------------------------------------------------------------------------------
