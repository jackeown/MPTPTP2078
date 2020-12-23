%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT1533+2 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n018.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Wed Dec 16 12:10:23 EST 2020

% Result     : Theorem 1.09s
% Output     : Refutation 1.09s
% Verified   : 
% Statistics : Number of formulae       :   84 ( 205 expanded)
%              Number of leaves         :   16 (  80 expanded)
%              Depth                    :   19
%              Number of atoms          :  407 (1117 expanded)
%              Number of equality atoms :    0 (   0 expanded)
%              Maximal formula depth    :   14 (   6 average)
%              Maximal term depth       :    2 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f3222,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f3017,f3021,f3025,f3029,f3033,f3037,f3041,f3057,f3190,f3221])).

fof(f3221,plain,
    ( spl7_1
    | ~ spl7_4
    | ~ spl7_6
    | spl7_10 ),
    inference(avatar_contradiction_clause,[],[f3220])).

fof(f3220,plain,
    ( $false
    | spl7_1
    | ~ spl7_4
    | ~ spl7_6
    | spl7_10 ),
    inference(subsumption_resolution,[],[f3219,f3036])).

fof(f3036,plain,
    ( l1_orders_2(sK0)
    | ~ spl7_6 ),
    inference(avatar_component_clause,[],[f3035])).

fof(f3035,plain,
    ( spl7_6
  <=> l1_orders_2(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_6])])).

fof(f3219,plain,
    ( ~ l1_orders_2(sK0)
    | spl7_1
    | ~ spl7_4
    | spl7_10 ),
    inference(subsumption_resolution,[],[f3218,f3028])).

fof(f3028,plain,
    ( m1_subset_1(sK3,u1_struct_0(sK0))
    | ~ spl7_4 ),
    inference(avatar_component_clause,[],[f3027])).

fof(f3027,plain,
    ( spl7_4
  <=> m1_subset_1(sK3,u1_struct_0(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_4])])).

fof(f3218,plain,
    ( ~ m1_subset_1(sK3,u1_struct_0(sK0))
    | ~ l1_orders_2(sK0)
    | spl7_1
    | spl7_10 ),
    inference(subsumption_resolution,[],[f3216,f3016])).

fof(f3016,plain,
    ( ~ r2_lattice3(sK0,sK1,sK3)
    | spl7_1 ),
    inference(avatar_component_clause,[],[f3015])).

fof(f3015,plain,
    ( spl7_1
  <=> r2_lattice3(sK0,sK1,sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_1])])).

fof(f3216,plain,
    ( r2_lattice3(sK0,sK1,sK3)
    | ~ m1_subset_1(sK3,u1_struct_0(sK0))
    | ~ l1_orders_2(sK0)
    | spl7_10 ),
    inference(resolution,[],[f3176,f3009])).

fof(f3009,plain,(
    ! [X2,X0,X1] :
      ( m1_subset_1(sK4(X0,X1,X2),u1_struct_0(X0))
      | r2_lattice3(X0,X1,X2)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ l1_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f2993])).

fof(f2993,plain,(
    ! [X0] :
      ( ! [X1,X2] :
          ( ( ( r2_lattice3(X0,X1,X2)
              | ( ~ r1_orders_2(X0,sK4(X0,X1,X2),X2)
                & r2_hidden(sK4(X0,X1,X2),X1)
                & m1_subset_1(sK4(X0,X1,X2),u1_struct_0(X0)) ) )
            & ( ! [X4] :
                  ( r1_orders_2(X0,X4,X2)
                  | ~ r2_hidden(X4,X1)
                  | ~ m1_subset_1(X4,u1_struct_0(X0)) )
              | ~ r2_lattice3(X0,X1,X2) ) )
          | ~ m1_subset_1(X2,u1_struct_0(X0)) )
      | ~ l1_orders_2(X0) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4])],[f2991,f2992])).

fof(f2992,plain,(
    ! [X2,X1,X0] :
      ( ? [X3] :
          ( ~ r1_orders_2(X0,X3,X2)
          & r2_hidden(X3,X1)
          & m1_subset_1(X3,u1_struct_0(X0)) )
     => ( ~ r1_orders_2(X0,sK4(X0,X1,X2),X2)
        & r2_hidden(sK4(X0,X1,X2),X1)
        & m1_subset_1(sK4(X0,X1,X2),u1_struct_0(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f2991,plain,(
    ! [X0] :
      ( ! [X1,X2] :
          ( ( ( r2_lattice3(X0,X1,X2)
              | ? [X3] :
                  ( ~ r1_orders_2(X0,X3,X2)
                  & r2_hidden(X3,X1)
                  & m1_subset_1(X3,u1_struct_0(X0)) ) )
            & ( ! [X4] :
                  ( r1_orders_2(X0,X4,X2)
                  | ~ r2_hidden(X4,X1)
                  | ~ m1_subset_1(X4,u1_struct_0(X0)) )
              | ~ r2_lattice3(X0,X1,X2) ) )
          | ~ m1_subset_1(X2,u1_struct_0(X0)) )
      | ~ l1_orders_2(X0) ) ),
    inference(rectify,[],[f2990])).

fof(f2990,plain,(
    ! [X0] :
      ( ! [X1,X2] :
          ( ( ( r2_lattice3(X0,X1,X2)
              | ? [X3] :
                  ( ~ r1_orders_2(X0,X3,X2)
                  & r2_hidden(X3,X1)
                  & m1_subset_1(X3,u1_struct_0(X0)) ) )
            & ( ! [X3] :
                  ( r1_orders_2(X0,X3,X2)
                  | ~ r2_hidden(X3,X1)
                  | ~ m1_subset_1(X3,u1_struct_0(X0)) )
              | ~ r2_lattice3(X0,X1,X2) ) )
          | ~ m1_subset_1(X2,u1_struct_0(X0)) )
      | ~ l1_orders_2(X0) ) ),
    inference(nnf_transformation,[],[f2984])).

fof(f2984,plain,(
    ! [X0] :
      ( ! [X1,X2] :
          ( ( r2_lattice3(X0,X1,X2)
          <=> ! [X3] :
                ( r1_orders_2(X0,X3,X2)
                | ~ r2_hidden(X3,X1)
                | ~ m1_subset_1(X3,u1_struct_0(X0)) ) )
          | ~ m1_subset_1(X2,u1_struct_0(X0)) )
      | ~ l1_orders_2(X0) ) ),
    inference(flattening,[],[f2983])).

fof(f2983,plain,(
    ! [X0] :
      ( ! [X1,X2] :
          ( ( r2_lattice3(X0,X1,X2)
          <=> ! [X3] :
                ( r1_orders_2(X0,X3,X2)
                | ~ r2_hidden(X3,X1)
                | ~ m1_subset_1(X3,u1_struct_0(X0)) ) )
          | ~ m1_subset_1(X2,u1_struct_0(X0)) )
      | ~ l1_orders_2(X0) ) ),
    inference(ennf_transformation,[],[f2832])).

fof(f2832,axiom,(
    ! [X0] :
      ( l1_orders_2(X0)
     => ! [X1,X2] :
          ( m1_subset_1(X2,u1_struct_0(X0))
         => ( r2_lattice3(X0,X1,X2)
          <=> ! [X3] :
                ( m1_subset_1(X3,u1_struct_0(X0))
               => ( r2_hidden(X3,X1)
                 => r1_orders_2(X0,X3,X2) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d9_lattice3)).

fof(f3176,plain,
    ( ~ m1_subset_1(sK4(sK0,sK1,sK3),u1_struct_0(sK0))
    | spl7_10 ),
    inference(avatar_component_clause,[],[f3175])).

fof(f3175,plain,
    ( spl7_10
  <=> m1_subset_1(sK4(sK0,sK1,sK3),u1_struct_0(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_10])])).

fof(f3190,plain,
    ( ~ spl7_10
    | spl7_1
    | ~ spl7_2
    | ~ spl7_3
    | ~ spl7_4
    | ~ spl7_5
    | ~ spl7_6
    | ~ spl7_7
    | ~ spl7_9 ),
    inference(avatar_split_clause,[],[f3189,f3055,f3039,f3035,f3031,f3027,f3023,f3019,f3015,f3175])).

fof(f3019,plain,
    ( spl7_2
  <=> r1_orders_2(sK0,sK2,sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_2])])).

fof(f3023,plain,
    ( spl7_3
  <=> r2_lattice3(sK0,sK1,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_3])])).

fof(f3031,plain,
    ( spl7_5
  <=> m1_subset_1(sK2,u1_struct_0(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_5])])).

fof(f3039,plain,
    ( spl7_7
  <=> v4_orders_2(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_7])])).

fof(f3055,plain,
    ( spl7_9
  <=> r2_hidden(sK4(sK0,sK1,sK3),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_9])])).

fof(f3189,plain,
    ( ~ m1_subset_1(sK4(sK0,sK1,sK3),u1_struct_0(sK0))
    | spl7_1
    | ~ spl7_2
    | ~ spl7_3
    | ~ spl7_4
    | ~ spl7_5
    | ~ spl7_6
    | ~ spl7_7
    | ~ spl7_9 ),
    inference(subsumption_resolution,[],[f3188,f3056])).

fof(f3056,plain,
    ( r2_hidden(sK4(sK0,sK1,sK3),sK1)
    | ~ spl7_9 ),
    inference(avatar_component_clause,[],[f3055])).

fof(f3188,plain,
    ( ~ r2_hidden(sK4(sK0,sK1,sK3),sK1)
    | ~ m1_subset_1(sK4(sK0,sK1,sK3),u1_struct_0(sK0))
    | spl7_1
    | ~ spl7_2
    | ~ spl7_3
    | ~ spl7_4
    | ~ spl7_5
    | ~ spl7_6
    | ~ spl7_7 ),
    inference(subsumption_resolution,[],[f3187,f3032])).

fof(f3032,plain,
    ( m1_subset_1(sK2,u1_struct_0(sK0))
    | ~ spl7_5 ),
    inference(avatar_component_clause,[],[f3031])).

fof(f3187,plain,
    ( ~ m1_subset_1(sK2,u1_struct_0(sK0))
    | ~ r2_hidden(sK4(sK0,sK1,sK3),sK1)
    | ~ m1_subset_1(sK4(sK0,sK1,sK3),u1_struct_0(sK0))
    | spl7_1
    | ~ spl7_2
    | ~ spl7_3
    | ~ spl7_4
    | ~ spl7_5
    | ~ spl7_6
    | ~ spl7_7 ),
    inference(subsumption_resolution,[],[f3161,f3020])).

fof(f3020,plain,
    ( r1_orders_2(sK0,sK2,sK3)
    | ~ spl7_2 ),
    inference(avatar_component_clause,[],[f3019])).

fof(f3161,plain,
    ( ~ r1_orders_2(sK0,sK2,sK3)
    | ~ m1_subset_1(sK2,u1_struct_0(sK0))
    | ~ r2_hidden(sK4(sK0,sK1,sK3),sK1)
    | ~ m1_subset_1(sK4(sK0,sK1,sK3),u1_struct_0(sK0))
    | spl7_1
    | ~ spl7_3
    | ~ spl7_4
    | ~ spl7_5
    | ~ spl7_6
    | ~ spl7_7 ),
    inference(resolution,[],[f3152,f3085])).

fof(f3085,plain,
    ( ! [X0] :
        ( r1_orders_2(sK0,X0,sK2)
        | ~ r2_hidden(X0,sK1)
        | ~ m1_subset_1(X0,u1_struct_0(sK0)) )
    | ~ spl7_3
    | ~ spl7_5
    | ~ spl7_6 ),
    inference(resolution,[],[f3072,f3024])).

fof(f3024,plain,
    ( r2_lattice3(sK0,sK1,sK2)
    | ~ spl7_3 ),
    inference(avatar_component_clause,[],[f3023])).

fof(f3072,plain,
    ( ! [X2,X3] :
        ( ~ r2_lattice3(sK0,X3,sK2)
        | ~ m1_subset_1(X2,u1_struct_0(sK0))
        | ~ r2_hidden(X2,X3)
        | r1_orders_2(sK0,X2,sK2) )
    | ~ spl7_5
    | ~ spl7_6 ),
    inference(resolution,[],[f3062,f3032])).

fof(f3062,plain,
    ( ! [X2,X0,X1] :
        ( ~ m1_subset_1(X2,u1_struct_0(sK0))
        | ~ m1_subset_1(X0,u1_struct_0(sK0))
        | ~ r2_lattice3(sK0,X1,X2)
        | ~ r2_hidden(X0,X1)
        | r1_orders_2(sK0,X0,X2) )
    | ~ spl7_6 ),
    inference(resolution,[],[f3008,f3036])).

fof(f3008,plain,(
    ! [X4,X2,X0,X1] :
      ( ~ l1_orders_2(X0)
      | ~ r2_hidden(X4,X1)
      | ~ m1_subset_1(X4,u1_struct_0(X0))
      | ~ r2_lattice3(X0,X1,X2)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | r1_orders_2(X0,X4,X2) ) ),
    inference(cnf_transformation,[],[f2993])).

fof(f3152,plain,
    ( ! [X0] :
        ( ~ r1_orders_2(sK0,sK4(sK0,sK1,sK3),X0)
        | ~ r1_orders_2(sK0,X0,sK3)
        | ~ m1_subset_1(X0,u1_struct_0(sK0)) )
    | spl7_1
    | ~ spl7_4
    | ~ spl7_6
    | ~ spl7_7 ),
    inference(resolution,[],[f3151,f3016])).

fof(f3151,plain,
    ( ! [X0,X1] :
        ( r2_lattice3(sK0,X1,sK3)
        | ~ r1_orders_2(sK0,X0,sK3)
        | ~ r1_orders_2(sK0,sK4(sK0,X1,sK3),X0)
        | ~ m1_subset_1(X0,u1_struct_0(sK0)) )
    | ~ spl7_4
    | ~ spl7_6
    | ~ spl7_7 ),
    inference(subsumption_resolution,[],[f3150,f3028])).

fof(f3150,plain,
    ( ! [X0,X1] :
        ( ~ m1_subset_1(X0,u1_struct_0(sK0))
        | ~ r1_orders_2(sK0,X0,sK3)
        | ~ r1_orders_2(sK0,sK4(sK0,X1,sK3),X0)
        | r2_lattice3(sK0,X1,sK3)
        | ~ m1_subset_1(sK3,u1_struct_0(sK0)) )
    | ~ spl7_4
    | ~ spl7_6
    | ~ spl7_7 ),
    inference(duplicate_literal_removal,[],[f3149])).

fof(f3149,plain,
    ( ! [X0,X1] :
        ( ~ m1_subset_1(X0,u1_struct_0(sK0))
        | ~ r1_orders_2(sK0,X0,sK3)
        | ~ r1_orders_2(sK0,sK4(sK0,X1,sK3),X0)
        | r2_lattice3(sK0,X1,sK3)
        | ~ m1_subset_1(sK3,u1_struct_0(sK0))
        | r2_lattice3(sK0,X1,sK3) )
    | ~ spl7_4
    | ~ spl7_6
    | ~ spl7_7 ),
    inference(resolution,[],[f3115,f3064])).

fof(f3064,plain,
    ( ! [X0] :
        ( ~ r1_orders_2(sK0,sK4(sK0,X0,sK3),sK3)
        | r2_lattice3(sK0,X0,sK3) )
    | ~ spl7_4
    | ~ spl7_6 ),
    inference(resolution,[],[f3058,f3028])).

fof(f3058,plain,
    ( ! [X0,X1] :
        ( ~ m1_subset_1(X1,u1_struct_0(sK0))
        | ~ r1_orders_2(sK0,sK4(sK0,X0,X1),X1)
        | r2_lattice3(sK0,X0,X1) )
    | ~ spl7_6 ),
    inference(resolution,[],[f3011,f3036])).

fof(f3011,plain,(
    ! [X2,X0,X1] :
      ( ~ l1_orders_2(X0)
      | ~ r1_orders_2(X0,sK4(X0,X1,X2),X2)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | r2_lattice3(X0,X1,X2) ) ),
    inference(cnf_transformation,[],[f2993])).

fof(f3115,plain,
    ( ! [X2,X0,X1] :
        ( r1_orders_2(sK0,sK4(sK0,X0,X1),sK3)
        | ~ m1_subset_1(X2,u1_struct_0(sK0))
        | ~ r1_orders_2(sK0,X2,sK3)
        | ~ r1_orders_2(sK0,sK4(sK0,X0,X1),X2)
        | r2_lattice3(sK0,X0,X1)
        | ~ m1_subset_1(X1,u1_struct_0(sK0)) )
    | ~ spl7_4
    | ~ spl7_6
    | ~ spl7_7 ),
    inference(resolution,[],[f3080,f3028])).

fof(f3080,plain,
    ( ! [X6,X4,X7,X5] :
        ( ~ m1_subset_1(X7,u1_struct_0(sK0))
        | ~ r1_orders_2(sK0,sK4(sK0,X4,X5),X6)
        | ~ m1_subset_1(X6,u1_struct_0(sK0))
        | ~ r1_orders_2(sK0,X6,X7)
        | r1_orders_2(sK0,sK4(sK0,X4,X5),X7)
        | r2_lattice3(sK0,X4,X5)
        | ~ m1_subset_1(X5,u1_struct_0(sK0)) )
    | ~ spl7_6
    | ~ spl7_7 ),
    inference(subsumption_resolution,[],[f3078,f3036])).

fof(f3078,plain,
    ( ! [X6,X4,X7,X5] :
        ( ~ r1_orders_2(sK0,sK4(sK0,X4,X5),X6)
        | ~ m1_subset_1(X7,u1_struct_0(sK0))
        | ~ m1_subset_1(X6,u1_struct_0(sK0))
        | ~ r1_orders_2(sK0,X6,X7)
        | r1_orders_2(sK0,sK4(sK0,X4,X5),X7)
        | r2_lattice3(sK0,X4,X5)
        | ~ m1_subset_1(X5,u1_struct_0(sK0))
        | ~ l1_orders_2(sK0) )
    | ~ spl7_6
    | ~ spl7_7 ),
    inference(resolution,[],[f3070,f3009])).

fof(f3070,plain,
    ( ! [X2,X0,X1] :
        ( ~ m1_subset_1(X2,u1_struct_0(sK0))
        | ~ r1_orders_2(sK0,X2,X0)
        | ~ m1_subset_1(X1,u1_struct_0(sK0))
        | ~ m1_subset_1(X0,u1_struct_0(sK0))
        | ~ r1_orders_2(sK0,X0,X1)
        | r1_orders_2(sK0,X2,X1) )
    | ~ spl7_6
    | ~ spl7_7 ),
    inference(subsumption_resolution,[],[f3069,f3036])).

fof(f3069,plain,
    ( ! [X2,X0,X1] :
        ( ~ r1_orders_2(sK0,X0,X1)
        | ~ r1_orders_2(sK0,X2,X0)
        | ~ m1_subset_1(X1,u1_struct_0(sK0))
        | ~ m1_subset_1(X0,u1_struct_0(sK0))
        | ~ m1_subset_1(X2,u1_struct_0(sK0))
        | ~ l1_orders_2(sK0)
        | r1_orders_2(sK0,X2,X1) )
    | ~ spl7_7 ),
    inference(resolution,[],[f3005,f3040])).

fof(f3040,plain,
    ( v4_orders_2(sK0)
    | ~ spl7_7 ),
    inference(avatar_component_clause,[],[f3039])).

fof(f3005,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ v4_orders_2(X0)
      | ~ r1_orders_2(X0,X2,X3)
      | ~ r1_orders_2(X0,X1,X2)
      | ~ m1_subset_1(X3,u1_struct_0(X0))
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | r1_orders_2(X0,X1,X3) ) ),
    inference(cnf_transformation,[],[f2981])).

fof(f2981,plain,(
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
    inference(flattening,[],[f2980])).

fof(f2980,plain,(
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
    inference(ennf_transformation,[],[f1954])).

fof(f1954,axiom,(
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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t26_orders_2)).

fof(f3057,plain,
    ( spl7_9
    | spl7_1
    | ~ spl7_4
    | ~ spl7_6 ),
    inference(avatar_split_clause,[],[f3053,f3035,f3027,f3015,f3055])).

fof(f3053,plain,
    ( r2_hidden(sK4(sK0,sK1,sK3),sK1)
    | spl7_1
    | ~ spl7_4
    | ~ spl7_6 ),
    inference(resolution,[],[f3048,f3016])).

fof(f3048,plain,
    ( ! [X0] :
        ( r2_lattice3(sK0,X0,sK3)
        | r2_hidden(sK4(sK0,X0,sK3),X0) )
    | ~ spl7_4
    | ~ spl7_6 ),
    inference(resolution,[],[f3046,f3028])).

fof(f3046,plain,
    ( ! [X0,X1] :
        ( ~ m1_subset_1(X1,u1_struct_0(sK0))
        | r2_hidden(sK4(sK0,X0,X1),X0)
        | r2_lattice3(sK0,X0,X1) )
    | ~ spl7_6 ),
    inference(resolution,[],[f3010,f3036])).

fof(f3010,plain,(
    ! [X2,X0,X1] :
      ( ~ l1_orders_2(X0)
      | r2_hidden(sK4(X0,X1,X2),X1)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | r2_lattice3(X0,X1,X2) ) ),
    inference(cnf_transformation,[],[f2993])).

fof(f3041,plain,(
    spl7_7 ),
    inference(avatar_split_clause,[],[f2998,f3039])).

fof(f2998,plain,(
    v4_orders_2(sK0) ),
    inference(cnf_transformation,[],[f2988])).

fof(f2988,plain,
    ( ~ r2_lattice3(sK0,sK1,sK3)
    & r1_orders_2(sK0,sK2,sK3)
    & r2_lattice3(sK0,sK1,sK2)
    & m1_subset_1(sK3,u1_struct_0(sK0))
    & m1_subset_1(sK2,u1_struct_0(sK0))
    & l1_orders_2(sK0)
    & v4_orders_2(sK0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3])],[f2979,f2987,f2986,f2985])).

fof(f2985,plain,
    ( ? [X0] :
        ( ? [X1,X2] :
            ( ? [X3] :
                ( ~ r2_lattice3(X0,X1,X3)
                & r1_orders_2(X0,X2,X3)
                & r2_lattice3(X0,X1,X2)
                & m1_subset_1(X3,u1_struct_0(X0)) )
            & m1_subset_1(X2,u1_struct_0(X0)) )
        & l1_orders_2(X0)
        & v4_orders_2(X0) )
   => ( ? [X2,X1] :
          ( ? [X3] :
              ( ~ r2_lattice3(sK0,X1,X3)
              & r1_orders_2(sK0,X2,X3)
              & r2_lattice3(sK0,X1,X2)
              & m1_subset_1(X3,u1_struct_0(sK0)) )
          & m1_subset_1(X2,u1_struct_0(sK0)) )
      & l1_orders_2(sK0)
      & v4_orders_2(sK0) ) ),
    introduced(choice_axiom,[])).

fof(f2986,plain,
    ( ? [X2,X1] :
        ( ? [X3] :
            ( ~ r2_lattice3(sK0,X1,X3)
            & r1_orders_2(sK0,X2,X3)
            & r2_lattice3(sK0,X1,X2)
            & m1_subset_1(X3,u1_struct_0(sK0)) )
        & m1_subset_1(X2,u1_struct_0(sK0)) )
   => ( ? [X3] :
          ( ~ r2_lattice3(sK0,sK1,X3)
          & r1_orders_2(sK0,sK2,X3)
          & r2_lattice3(sK0,sK1,sK2)
          & m1_subset_1(X3,u1_struct_0(sK0)) )
      & m1_subset_1(sK2,u1_struct_0(sK0)) ) ),
    introduced(choice_axiom,[])).

fof(f2987,plain,
    ( ? [X3] :
        ( ~ r2_lattice3(sK0,sK1,X3)
        & r1_orders_2(sK0,sK2,X3)
        & r2_lattice3(sK0,sK1,sK2)
        & m1_subset_1(X3,u1_struct_0(sK0)) )
   => ( ~ r2_lattice3(sK0,sK1,sK3)
      & r1_orders_2(sK0,sK2,sK3)
      & r2_lattice3(sK0,sK1,sK2)
      & m1_subset_1(sK3,u1_struct_0(sK0)) ) ),
    introduced(choice_axiom,[])).

fof(f2979,plain,(
    ? [X0] :
      ( ? [X1,X2] :
          ( ? [X3] :
              ( ~ r2_lattice3(X0,X1,X3)
              & r1_orders_2(X0,X2,X3)
              & r2_lattice3(X0,X1,X2)
              & m1_subset_1(X3,u1_struct_0(X0)) )
          & m1_subset_1(X2,u1_struct_0(X0)) )
      & l1_orders_2(X0)
      & v4_orders_2(X0) ) ),
    inference(flattening,[],[f2978])).

fof(f2978,plain,(
    ? [X0] :
      ( ? [X1,X2] :
          ( ? [X3] :
              ( ~ r2_lattice3(X0,X1,X3)
              & r1_orders_2(X0,X2,X3)
              & r2_lattice3(X0,X1,X2)
              & m1_subset_1(X3,u1_struct_0(X0)) )
          & m1_subset_1(X2,u1_struct_0(X0)) )
      & l1_orders_2(X0)
      & v4_orders_2(X0) ) ),
    inference(ennf_transformation,[],[f2965])).

fof(f2965,negated_conjecture,(
    ~ ! [X0] :
        ( ( l1_orders_2(X0)
          & v4_orders_2(X0) )
       => ! [X1,X2] :
            ( m1_subset_1(X2,u1_struct_0(X0))
           => ! [X3] :
                ( m1_subset_1(X3,u1_struct_0(X0))
               => ( ( r1_orders_2(X0,X2,X3)
                    & r2_lattice3(X0,X1,X2) )
                 => r2_lattice3(X0,X1,X3) ) ) ) ) ),
    inference(negated_conjecture,[],[f2964])).

fof(f2964,conjecture,(
    ! [X0] :
      ( ( l1_orders_2(X0)
        & v4_orders_2(X0) )
     => ! [X1,X2] :
          ( m1_subset_1(X2,u1_struct_0(X0))
         => ! [X3] :
              ( m1_subset_1(X3,u1_struct_0(X0))
             => ( ( r1_orders_2(X0,X2,X3)
                  & r2_lattice3(X0,X1,X2) )
               => r2_lattice3(X0,X1,X3) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t11_yellow_0)).

fof(f3037,plain,(
    spl7_6 ),
    inference(avatar_split_clause,[],[f2999,f3035])).

fof(f2999,plain,(
    l1_orders_2(sK0) ),
    inference(cnf_transformation,[],[f2988])).

fof(f3033,plain,(
    spl7_5 ),
    inference(avatar_split_clause,[],[f3000,f3031])).

fof(f3000,plain,(
    m1_subset_1(sK2,u1_struct_0(sK0)) ),
    inference(cnf_transformation,[],[f2988])).

fof(f3029,plain,(
    spl7_4 ),
    inference(avatar_split_clause,[],[f3001,f3027])).

fof(f3001,plain,(
    m1_subset_1(sK3,u1_struct_0(sK0)) ),
    inference(cnf_transformation,[],[f2988])).

fof(f3025,plain,(
    spl7_3 ),
    inference(avatar_split_clause,[],[f3002,f3023])).

fof(f3002,plain,(
    r2_lattice3(sK0,sK1,sK2) ),
    inference(cnf_transformation,[],[f2988])).

fof(f3021,plain,(
    spl7_2 ),
    inference(avatar_split_clause,[],[f3003,f3019])).

fof(f3003,plain,(
    r1_orders_2(sK0,sK2,sK3) ),
    inference(cnf_transformation,[],[f2988])).

fof(f3017,plain,(
    ~ spl7_1 ),
    inference(avatar_split_clause,[],[f3004,f3015])).

fof(f3004,plain,(
    ~ r2_lattice3(sK0,sK1,sK3) ),
    inference(cnf_transformation,[],[f2988])).
%------------------------------------------------------------------------------
