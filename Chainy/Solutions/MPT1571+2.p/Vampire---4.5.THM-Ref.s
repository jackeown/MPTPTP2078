%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT1571+2 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n025.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Wed Dec 16 12:10:25 EST 2020

% Result     : Theorem 2.96s
% Output     : Refutation 2.96s
% Verified   : 
% Statistics : Number of formulae       :  139 ( 514 expanded)
%              Number of leaves         :   19 ( 155 expanded)
%              Depth                    :   20
%              Number of atoms          :  654 (3711 expanded)
%              Number of equality atoms :   42 ( 393 expanded)
%              Maximal formula depth    :   14 (   6 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f5125,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f3544,f3547,f4552,f4770,f4913,f4973,f5033,f5059,f5124])).

fof(f5124,plain,
    ( ~ spl20_119
    | spl20_120
    | ~ spl20_121 ),
    inference(avatar_contradiction_clause,[],[f5123])).

fof(f5123,plain,
    ( $false
    | ~ spl20_119
    | spl20_120
    | ~ spl20_121 ),
    inference(subsumption_resolution,[],[f5121,f5109])).

fof(f5109,plain,
    ( ~ r1_lattice3(sK2,sK4,sK10(sK2,sK3,sK4))
    | spl20_120
    | ~ spl20_121 ),
    inference(subsumption_resolution,[],[f5100,f4967])).

fof(f4967,plain,
    ( ~ r2_yellow_0(sK2,sK4)
    | spl20_120 ),
    inference(avatar_component_clause,[],[f4966])).

fof(f4966,plain,
    ( spl20_120
  <=> r2_yellow_0(sK2,sK4) ),
    introduced(avatar_definition,[new_symbols(naming,[spl20_120])])).

fof(f5100,plain,
    ( ~ r1_lattice3(sK2,sK4,sK10(sK2,sK3,sK4))
    | r2_yellow_0(sK2,sK4)
    | ~ spl20_121 ),
    inference(resolution,[],[f4972,f3774])).

fof(f3774,plain,(
    ! [X0] :
      ( ~ r1_lattice3(sK2,sK3,sK10(sK2,sK3,X0))
      | ~ r1_lattice3(sK2,X0,sK10(sK2,sK3,X0))
      | r2_yellow_0(sK2,X0) ) ),
    inference(resolution,[],[f3295,f3162])).

fof(f3162,plain,(
    r2_yellow_0(sK2,sK3) ),
    inference(cnf_transformation,[],[f3116])).

fof(f3116,plain,
    ( k2_yellow_0(sK2,sK3) != k2_yellow_0(sK2,sK4)
    & ! [X3] :
        ( ( ( r1_lattice3(sK2,sK3,X3)
            | ~ r1_lattice3(sK2,sK4,X3) )
          & ( r1_lattice3(sK2,sK4,X3)
            | ~ r1_lattice3(sK2,sK3,X3) ) )
        | ~ m1_subset_1(X3,u1_struct_0(sK2)) )
    & r2_yellow_0(sK2,sK3)
    & l1_orders_2(sK2)
    & ~ v2_struct_0(sK2) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2,sK3,sK4])],[f3113,f3115,f3114])).

fof(f3114,plain,
    ( ? [X0] :
        ( ? [X1,X2] :
            ( k2_yellow_0(X0,X1) != k2_yellow_0(X0,X2)
            & ! [X3] :
                ( ( ( r1_lattice3(X0,X1,X3)
                    | ~ r1_lattice3(X0,X2,X3) )
                  & ( r1_lattice3(X0,X2,X3)
                    | ~ r1_lattice3(X0,X1,X3) ) )
                | ~ m1_subset_1(X3,u1_struct_0(X0)) )
            & r2_yellow_0(X0,X1) )
        & l1_orders_2(X0)
        & ~ v2_struct_0(X0) )
   => ( ? [X2,X1] :
          ( k2_yellow_0(sK2,X1) != k2_yellow_0(sK2,X2)
          & ! [X3] :
              ( ( ( r1_lattice3(sK2,X1,X3)
                  | ~ r1_lattice3(sK2,X2,X3) )
                & ( r1_lattice3(sK2,X2,X3)
                  | ~ r1_lattice3(sK2,X1,X3) ) )
              | ~ m1_subset_1(X3,u1_struct_0(sK2)) )
          & r2_yellow_0(sK2,X1) )
      & l1_orders_2(sK2)
      & ~ v2_struct_0(sK2) ) ),
    introduced(choice_axiom,[])).

fof(f3115,plain,
    ( ? [X2,X1] :
        ( k2_yellow_0(sK2,X1) != k2_yellow_0(sK2,X2)
        & ! [X3] :
            ( ( ( r1_lattice3(sK2,X1,X3)
                | ~ r1_lattice3(sK2,X2,X3) )
              & ( r1_lattice3(sK2,X2,X3)
                | ~ r1_lattice3(sK2,X1,X3) ) )
            | ~ m1_subset_1(X3,u1_struct_0(sK2)) )
        & r2_yellow_0(sK2,X1) )
   => ( k2_yellow_0(sK2,sK3) != k2_yellow_0(sK2,sK4)
      & ! [X3] :
          ( ( ( r1_lattice3(sK2,sK3,X3)
              | ~ r1_lattice3(sK2,sK4,X3) )
            & ( r1_lattice3(sK2,sK4,X3)
              | ~ r1_lattice3(sK2,sK3,X3) ) )
          | ~ m1_subset_1(X3,u1_struct_0(sK2)) )
      & r2_yellow_0(sK2,sK3) ) ),
    introduced(choice_axiom,[])).

fof(f3113,plain,(
    ? [X0] :
      ( ? [X1,X2] :
          ( k2_yellow_0(X0,X1) != k2_yellow_0(X0,X2)
          & ! [X3] :
              ( ( ( r1_lattice3(X0,X1,X3)
                  | ~ r1_lattice3(X0,X2,X3) )
                & ( r1_lattice3(X0,X2,X3)
                  | ~ r1_lattice3(X0,X1,X3) ) )
              | ~ m1_subset_1(X3,u1_struct_0(X0)) )
          & r2_yellow_0(X0,X1) )
      & l1_orders_2(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(nnf_transformation,[],[f3059])).

fof(f3059,plain,(
    ? [X0] :
      ( ? [X1,X2] :
          ( k2_yellow_0(X0,X1) != k2_yellow_0(X0,X2)
          & ! [X3] :
              ( ( r1_lattice3(X0,X1,X3)
              <=> r1_lattice3(X0,X2,X3) )
              | ~ m1_subset_1(X3,u1_struct_0(X0)) )
          & r2_yellow_0(X0,X1) )
      & l1_orders_2(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(flattening,[],[f3058])).

fof(f3058,plain,(
    ? [X0] :
      ( ? [X1,X2] :
          ( k2_yellow_0(X0,X1) != k2_yellow_0(X0,X2)
          & ! [X3] :
              ( ( r1_lattice3(X0,X1,X3)
              <=> r1_lattice3(X0,X2,X3) )
              | ~ m1_subset_1(X3,u1_struct_0(X0)) )
          & r2_yellow_0(X0,X1) )
      & l1_orders_2(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f3031])).

fof(f3031,negated_conjecture,(
    ~ ! [X0] :
        ( ( l1_orders_2(X0)
          & ~ v2_struct_0(X0) )
       => ! [X1,X2] :
            ( ( ! [X3] :
                  ( m1_subset_1(X3,u1_struct_0(X0))
                 => ( r1_lattice3(X0,X1,X3)
                  <=> r1_lattice3(X0,X2,X3) ) )
              & r2_yellow_0(X0,X1) )
           => k2_yellow_0(X0,X1) = k2_yellow_0(X0,X2) ) ) ),
    inference(negated_conjecture,[],[f3030])).

fof(f3030,conjecture,(
    ! [X0] :
      ( ( l1_orders_2(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1,X2] :
          ( ( ! [X3] :
                ( m1_subset_1(X3,u1_struct_0(X0))
               => ( r1_lattice3(X0,X1,X3)
                <=> r1_lattice3(X0,X2,X3) ) )
            & r2_yellow_0(X0,X1) )
         => k2_yellow_0(X0,X1) = k2_yellow_0(X0,X2) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t49_yellow_0)).

fof(f3295,plain,(
    ! [X10,X11] :
      ( ~ r2_yellow_0(sK2,X10)
      | ~ r1_lattice3(sK2,X11,sK10(sK2,X10,X11))
      | ~ r1_lattice3(sK2,X10,sK10(sK2,X10,X11))
      | r2_yellow_0(sK2,X11) ) ),
    inference(subsumption_resolution,[],[f3263,f3160])).

fof(f3160,plain,(
    ~ v2_struct_0(sK2) ),
    inference(cnf_transformation,[],[f3116])).

fof(f3263,plain,(
    ! [X10,X11] :
      ( ~ r2_yellow_0(sK2,X10)
      | ~ r1_lattice3(sK2,X11,sK10(sK2,X10,X11))
      | ~ r1_lattice3(sK2,X10,sK10(sK2,X10,X11))
      | r2_yellow_0(sK2,X11)
      | v2_struct_0(sK2) ) ),
    inference(resolution,[],[f3161,f3187])).

fof(f3187,plain,(
    ! [X2,X0,X1] :
      ( ~ l1_orders_2(X0)
      | ~ r2_yellow_0(X0,X1)
      | ~ r1_lattice3(X0,X2,sK10(X0,X1,X2))
      | ~ r1_lattice3(X0,X1,sK10(X0,X1,X2))
      | r2_yellow_0(X0,X2)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f3138])).

fof(f3138,plain,(
    ! [X0] :
      ( ! [X1,X2] :
          ( r2_yellow_0(X0,X2)
          | ~ r2_yellow_0(X0,X1)
          | ( ( ~ r1_lattice3(X0,X2,sK10(X0,X1,X2))
              | ~ r1_lattice3(X0,X1,sK10(X0,X1,X2)) )
            & ( r1_lattice3(X0,X2,sK10(X0,X1,X2))
              | r1_lattice3(X0,X1,sK10(X0,X1,X2)) )
            & m1_subset_1(sK10(X0,X1,X2),u1_struct_0(X0)) ) )
      | ~ l1_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK10])],[f3136,f3137])).

fof(f3137,plain,(
    ! [X2,X1,X0] :
      ( ? [X3] :
          ( ( ~ r1_lattice3(X0,X2,X3)
            | ~ r1_lattice3(X0,X1,X3) )
          & ( r1_lattice3(X0,X2,X3)
            | r1_lattice3(X0,X1,X3) )
          & m1_subset_1(X3,u1_struct_0(X0)) )
     => ( ( ~ r1_lattice3(X0,X2,sK10(X0,X1,X2))
          | ~ r1_lattice3(X0,X1,sK10(X0,X1,X2)) )
        & ( r1_lattice3(X0,X2,sK10(X0,X1,X2))
          | r1_lattice3(X0,X1,sK10(X0,X1,X2)) )
        & m1_subset_1(sK10(X0,X1,X2),u1_struct_0(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f3136,plain,(
    ! [X0] :
      ( ! [X1,X2] :
          ( r2_yellow_0(X0,X2)
          | ~ r2_yellow_0(X0,X1)
          | ? [X3] :
              ( ( ~ r1_lattice3(X0,X2,X3)
                | ~ r1_lattice3(X0,X1,X3) )
              & ( r1_lattice3(X0,X2,X3)
                | r1_lattice3(X0,X1,X3) )
              & m1_subset_1(X3,u1_struct_0(X0)) ) )
      | ~ l1_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f3135])).

fof(f3135,plain,(
    ! [X0] :
      ( ! [X1,X2] :
          ( r2_yellow_0(X0,X2)
          | ~ r2_yellow_0(X0,X1)
          | ? [X3] :
              ( ( ~ r1_lattice3(X0,X2,X3)
                | ~ r1_lattice3(X0,X1,X3) )
              & ( r1_lattice3(X0,X2,X3)
                | r1_lattice3(X0,X1,X3) )
              & m1_subset_1(X3,u1_struct_0(X0)) ) )
      | ~ l1_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(nnf_transformation,[],[f3076])).

fof(f3076,plain,(
    ! [X0] :
      ( ! [X1,X2] :
          ( r2_yellow_0(X0,X2)
          | ~ r2_yellow_0(X0,X1)
          | ? [X3] :
              ( ( r1_lattice3(X0,X1,X3)
              <~> r1_lattice3(X0,X2,X3) )
              & m1_subset_1(X3,u1_struct_0(X0)) ) )
      | ~ l1_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f3075])).

fof(f3075,plain,(
    ! [X0] :
      ( ! [X1,X2] :
          ( r2_yellow_0(X0,X2)
          | ~ r2_yellow_0(X0,X1)
          | ? [X3] :
              ( ( r1_lattice3(X0,X1,X3)
              <~> r1_lattice3(X0,X2,X3) )
              & m1_subset_1(X3,u1_struct_0(X0)) ) )
      | ~ l1_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f3029])).

fof(f3029,axiom,(
    ! [X0] :
      ( ( l1_orders_2(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1,X2] :
          ( ( r2_yellow_0(X0,X1)
            & ! [X3] :
                ( m1_subset_1(X3,u1_struct_0(X0))
               => ( r1_lattice3(X0,X1,X3)
                <=> r1_lattice3(X0,X2,X3) ) ) )
         => r2_yellow_0(X0,X2) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t48_yellow_0)).

fof(f3161,plain,(
    l1_orders_2(sK2) ),
    inference(cnf_transformation,[],[f3116])).

fof(f4972,plain,
    ( r1_lattice3(sK2,sK3,sK10(sK2,sK3,sK4))
    | ~ spl20_121 ),
    inference(avatar_component_clause,[],[f4970])).

fof(f4970,plain,
    ( spl20_121
  <=> r1_lattice3(sK2,sK3,sK10(sK2,sK3,sK4)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl20_121])])).

fof(f5121,plain,
    ( r1_lattice3(sK2,sK4,sK10(sK2,sK3,sK4))
    | ~ spl20_119
    | ~ spl20_121 ),
    inference(subsumption_resolution,[],[f5103,f4963])).

fof(f4963,plain,
    ( m1_subset_1(sK10(sK2,sK3,sK4),u1_struct_0(sK2))
    | ~ spl20_119 ),
    inference(avatar_component_clause,[],[f4962])).

fof(f4962,plain,
    ( spl20_119
  <=> m1_subset_1(sK10(sK2,sK3,sK4),u1_struct_0(sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl20_119])])).

fof(f5103,plain,
    ( r1_lattice3(sK2,sK4,sK10(sK2,sK3,sK4))
    | ~ m1_subset_1(sK10(sK2,sK3,sK4),u1_struct_0(sK2))
    | ~ spl20_121 ),
    inference(resolution,[],[f4972,f3163])).

fof(f3163,plain,(
    ! [X3] :
      ( ~ r1_lattice3(sK2,sK3,X3)
      | r1_lattice3(sK2,sK4,X3)
      | ~ m1_subset_1(X3,u1_struct_0(sK2)) ) ),
    inference(cnf_transformation,[],[f3116])).

fof(f5059,plain,
    ( spl20_3
    | ~ spl20_120 ),
    inference(avatar_contradiction_clause,[],[f5058])).

fof(f5058,plain,
    ( $false
    | spl20_3
    | ~ spl20_120 ),
    inference(subsumption_resolution,[],[f3335,f5038])).

fof(f5038,plain,
    ( sP0(sK2,sK4)
    | ~ spl20_120 ),
    inference(resolution,[],[f4968,f3300])).

fof(f3300,plain,(
    ! [X0] :
      ( ~ r2_yellow_0(sK2,X0)
      | sP0(sK2,X0) ) ),
    inference(resolution,[],[f3275,f3200])).

fof(f3200,plain,(
    ! [X0,X1] :
      ( ~ sP1(X0)
      | ~ r2_yellow_0(X0,X1)
      | sP0(X0,X1) ) ),
    inference(cnf_transformation,[],[f3143])).

fof(f3143,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( r2_yellow_0(X0,X1)
            | ~ sP0(X0,X1) )
          & ( sP0(X0,X1)
            | ~ r2_yellow_0(X0,X1) ) )
      | ~ sP1(X0) ) ),
    inference(nnf_transformation,[],[f3111])).

fof(f3111,plain,(
    ! [X0] :
      ( ! [X1] :
          ( r2_yellow_0(X0,X1)
        <=> sP0(X0,X1) )
      | ~ sP1(X0) ) ),
    introduced(predicate_definition_introduction,[new_symbols(naming,[sP1])])).

fof(f3275,plain,(
    sP1(sK2) ),
    inference(resolution,[],[f3161,f3220])).

fof(f3220,plain,(
    ! [X0] :
      ( ~ l1_orders_2(X0)
      | sP1(X0) ) ),
    inference(cnf_transformation,[],[f3112])).

fof(f3112,plain,(
    ! [X0] :
      ( sP1(X0)
      | ~ l1_orders_2(X0) ) ),
    inference(definition_folding,[],[f3085,f3111,f3110])).

fof(f3110,plain,(
    ! [X0,X1] :
      ( sP0(X0,X1)
    <=> ? [X2] :
          ( ! [X3] :
              ( X2 = X3
              | ? [X4] :
                  ( ~ r1_orders_2(X0,X4,X3)
                  & r1_lattice3(X0,X1,X4)
                  & m1_subset_1(X4,u1_struct_0(X0)) )
              | ~ r1_lattice3(X0,X1,X3)
              | ~ m1_subset_1(X3,u1_struct_0(X0)) )
          & ! [X5] :
              ( r1_orders_2(X0,X5,X2)
              | ~ r1_lattice3(X0,X1,X5)
              | ~ m1_subset_1(X5,u1_struct_0(X0)) )
          & r1_lattice3(X0,X1,X2)
          & m1_subset_1(X2,u1_struct_0(X0)) ) ) ),
    introduced(predicate_definition_introduction,[new_symbols(naming,[sP0])])).

fof(f3085,plain,(
    ! [X0] :
      ( ! [X1] :
          ( r2_yellow_0(X0,X1)
        <=> ? [X2] :
              ( ! [X3] :
                  ( X2 = X3
                  | ? [X4] :
                      ( ~ r1_orders_2(X0,X4,X3)
                      & r1_lattice3(X0,X1,X4)
                      & m1_subset_1(X4,u1_struct_0(X0)) )
                  | ~ r1_lattice3(X0,X1,X3)
                  | ~ m1_subset_1(X3,u1_struct_0(X0)) )
              & ! [X5] :
                  ( r1_orders_2(X0,X5,X2)
                  | ~ r1_lattice3(X0,X1,X5)
                  | ~ m1_subset_1(X5,u1_struct_0(X0)) )
              & r1_lattice3(X0,X1,X2)
              & m1_subset_1(X2,u1_struct_0(X0)) ) )
      | ~ l1_orders_2(X0) ) ),
    inference(flattening,[],[f3084])).

fof(f3084,plain,(
    ! [X0] :
      ( ! [X1] :
          ( r2_yellow_0(X0,X1)
        <=> ? [X2] :
              ( ! [X3] :
                  ( X2 = X3
                  | ? [X4] :
                      ( ~ r1_orders_2(X0,X4,X3)
                      & r1_lattice3(X0,X1,X4)
                      & m1_subset_1(X4,u1_struct_0(X0)) )
                  | ~ r1_lattice3(X0,X1,X3)
                  | ~ m1_subset_1(X3,u1_struct_0(X0)) )
              & ! [X5] :
                  ( r1_orders_2(X0,X5,X2)
                  | ~ r1_lattice3(X0,X1,X5)
                  | ~ m1_subset_1(X5,u1_struct_0(X0)) )
              & r1_lattice3(X0,X1,X2)
              & m1_subset_1(X2,u1_struct_0(X0)) ) )
      | ~ l1_orders_2(X0) ) ),
    inference(ennf_transformation,[],[f3039])).

fof(f3039,plain,(
    ! [X0] :
      ( l1_orders_2(X0)
     => ! [X1] :
          ( r2_yellow_0(X0,X1)
        <=> ? [X2] :
              ( ! [X3] :
                  ( m1_subset_1(X3,u1_struct_0(X0))
                 => ( ( ! [X4] :
                          ( m1_subset_1(X4,u1_struct_0(X0))
                         => ( r1_lattice3(X0,X1,X4)
                           => r1_orders_2(X0,X4,X3) ) )
                      & r1_lattice3(X0,X1,X3) )
                   => X2 = X3 ) )
              & ! [X5] :
                  ( m1_subset_1(X5,u1_struct_0(X0))
                 => ( r1_lattice3(X0,X1,X5)
                   => r1_orders_2(X0,X5,X2) ) )
              & r1_lattice3(X0,X1,X2)
              & m1_subset_1(X2,u1_struct_0(X0)) ) ) ) ),
    inference(rectify,[],[f2975])).

fof(f2975,axiom,(
    ! [X0] :
      ( l1_orders_2(X0)
     => ! [X1] :
          ( r2_yellow_0(X0,X1)
        <=> ? [X2] :
              ( ! [X3] :
                  ( m1_subset_1(X3,u1_struct_0(X0))
                 => ( ( ! [X4] :
                          ( m1_subset_1(X4,u1_struct_0(X0))
                         => ( r1_lattice3(X0,X1,X4)
                           => r1_orders_2(X0,X4,X3) ) )
                      & r1_lattice3(X0,X1,X3) )
                   => X2 = X3 ) )
              & ! [X3] :
                  ( m1_subset_1(X3,u1_struct_0(X0))
                 => ( r1_lattice3(X0,X1,X3)
                   => r1_orders_2(X0,X3,X2) ) )
              & r1_lattice3(X0,X1,X2)
              & m1_subset_1(X2,u1_struct_0(X0)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d8_yellow_0)).

fof(f4968,plain,
    ( r2_yellow_0(sK2,sK4)
    | ~ spl20_120 ),
    inference(avatar_component_clause,[],[f4966])).

fof(f3335,plain,
    ( ~ sP0(sK2,sK4)
    | spl20_3 ),
    inference(avatar_component_clause,[],[f3334])).

fof(f3334,plain,
    ( spl20_3
  <=> sP0(sK2,sK4) ),
    introduced(avatar_definition,[new_symbols(naming,[spl20_3])])).

fof(f5033,plain,
    ( spl20_3
    | spl20_119 ),
    inference(avatar_contradiction_clause,[],[f5032])).

fof(f5032,plain,
    ( $false
    | spl20_3
    | spl20_119 ),
    inference(subsumption_resolution,[],[f3335,f5009])).

fof(f5009,plain,
    ( sP0(sK2,sK4)
    | spl20_119 ),
    inference(resolution,[],[f5004,f3300])).

fof(f5004,plain,
    ( r2_yellow_0(sK2,sK4)
    | spl20_119 ),
    inference(subsumption_resolution,[],[f5003,f3160])).

fof(f5003,plain,
    ( r2_yellow_0(sK2,sK4)
    | v2_struct_0(sK2)
    | spl20_119 ),
    inference(subsumption_resolution,[],[f5002,f3161])).

fof(f5002,plain,
    ( r2_yellow_0(sK2,sK4)
    | ~ l1_orders_2(sK2)
    | v2_struct_0(sK2)
    | spl20_119 ),
    inference(subsumption_resolution,[],[f5001,f3162])).

fof(f5001,plain,
    ( ~ r2_yellow_0(sK2,sK3)
    | r2_yellow_0(sK2,sK4)
    | ~ l1_orders_2(sK2)
    | v2_struct_0(sK2)
    | spl20_119 ),
    inference(resolution,[],[f4964,f3185])).

fof(f3185,plain,(
    ! [X2,X0,X1] :
      ( m1_subset_1(sK10(X0,X1,X2),u1_struct_0(X0))
      | ~ r2_yellow_0(X0,X1)
      | r2_yellow_0(X0,X2)
      | ~ l1_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f3138])).

fof(f4964,plain,
    ( ~ m1_subset_1(sK10(sK2,sK3,sK4),u1_struct_0(sK2))
    | spl20_119 ),
    inference(avatar_component_clause,[],[f4962])).

fof(f4973,plain,
    ( ~ spl20_119
    | spl20_120
    | spl20_121 ),
    inference(avatar_split_clause,[],[f4075,f4970,f4966,f4962])).

fof(f4075,plain,
    ( r1_lattice3(sK2,sK3,sK10(sK2,sK3,sK4))
    | r2_yellow_0(sK2,sK4)
    | ~ m1_subset_1(sK10(sK2,sK3,sK4),u1_struct_0(sK2)) ),
    inference(duplicate_literal_removal,[],[f4056])).

fof(f4056,plain,
    ( r1_lattice3(sK2,sK3,sK10(sK2,sK3,sK4))
    | r2_yellow_0(sK2,sK4)
    | r1_lattice3(sK2,sK3,sK10(sK2,sK3,sK4))
    | ~ m1_subset_1(sK10(sK2,sK3,sK4),u1_struct_0(sK2)) ),
    inference(resolution,[],[f3749,f3164])).

fof(f3164,plain,(
    ! [X3] :
      ( ~ r1_lattice3(sK2,sK4,X3)
      | r1_lattice3(sK2,sK3,X3)
      | ~ m1_subset_1(X3,u1_struct_0(sK2)) ) ),
    inference(cnf_transformation,[],[f3116])).

fof(f3749,plain,(
    ! [X0] :
      ( r1_lattice3(sK2,X0,sK10(sK2,sK3,X0))
      | r1_lattice3(sK2,sK3,sK10(sK2,sK3,X0))
      | r2_yellow_0(sK2,X0) ) ),
    inference(resolution,[],[f3294,f3162])).

fof(f3294,plain,(
    ! [X8,X9] :
      ( ~ r2_yellow_0(sK2,X8)
      | r1_lattice3(sK2,X9,sK10(sK2,X8,X9))
      | r1_lattice3(sK2,X8,sK10(sK2,X8,X9))
      | r2_yellow_0(sK2,X9) ) ),
    inference(subsumption_resolution,[],[f3262,f3160])).

fof(f3262,plain,(
    ! [X8,X9] :
      ( ~ r2_yellow_0(sK2,X8)
      | r1_lattice3(sK2,X9,sK10(sK2,X8,X9))
      | r1_lattice3(sK2,X8,sK10(sK2,X8,X9))
      | r2_yellow_0(sK2,X9)
      | v2_struct_0(sK2) ) ),
    inference(resolution,[],[f3161,f3186])).

fof(f3186,plain,(
    ! [X2,X0,X1] :
      ( ~ l1_orders_2(X0)
      | ~ r2_yellow_0(X0,X1)
      | r1_lattice3(X0,X2,sK10(X0,X1,X2))
      | r1_lattice3(X0,X1,sK10(X0,X1,X2))
      | r2_yellow_0(X0,X2)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f3138])).

fof(f4913,plain,
    ( ~ spl20_3
    | ~ spl20_25
    | ~ spl20_26
    | ~ spl20_102
    | ~ spl20_105 ),
    inference(avatar_contradiction_clause,[],[f4912])).

fof(f4912,plain,
    ( $false
    | ~ spl20_3
    | ~ spl20_25
    | ~ spl20_26
    | ~ spl20_102
    | ~ spl20_105 ),
    inference(subsumption_resolution,[],[f4911,f3165])).

fof(f3165,plain,(
    k2_yellow_0(sK2,sK3) != k2_yellow_0(sK2,sK4) ),
    inference(cnf_transformation,[],[f3116])).

fof(f4911,plain,
    ( k2_yellow_0(sK2,sK3) = k2_yellow_0(sK2,sK4)
    | ~ spl20_3
    | ~ spl20_25
    | ~ spl20_26
    | ~ spl20_102
    | ~ spl20_105 ),
    inference(subsumption_resolution,[],[f4910,f3538])).

fof(f3538,plain,
    ( m1_subset_1(k2_yellow_0(sK2,sK4),u1_struct_0(sK2))
    | ~ spl20_25 ),
    inference(avatar_component_clause,[],[f3537])).

fof(f3537,plain,
    ( spl20_25
  <=> m1_subset_1(k2_yellow_0(sK2,sK4),u1_struct_0(sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl20_25])])).

fof(f4910,plain,
    ( ~ m1_subset_1(k2_yellow_0(sK2,sK4),u1_struct_0(sK2))
    | k2_yellow_0(sK2,sK3) = k2_yellow_0(sK2,sK4)
    | ~ spl20_3
    | ~ spl20_25
    | ~ spl20_26
    | ~ spl20_102
    | ~ spl20_105 ),
    inference(subsumption_resolution,[],[f4909,f3162])).

fof(f4909,plain,
    ( ~ r2_yellow_0(sK2,sK3)
    | ~ m1_subset_1(k2_yellow_0(sK2,sK4),u1_struct_0(sK2))
    | k2_yellow_0(sK2,sK3) = k2_yellow_0(sK2,sK4)
    | ~ spl20_3
    | ~ spl20_25
    | ~ spl20_26
    | ~ spl20_102
    | ~ spl20_105 ),
    inference(subsumption_resolution,[],[f4904,f3543])).

fof(f3543,plain,
    ( r1_lattice3(sK2,sK3,k2_yellow_0(sK2,sK4))
    | ~ spl20_26 ),
    inference(avatar_component_clause,[],[f3541])).

fof(f3541,plain,
    ( spl20_26
  <=> r1_lattice3(sK2,sK3,k2_yellow_0(sK2,sK4)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl20_26])])).

fof(f4904,plain,
    ( ~ r1_lattice3(sK2,sK3,k2_yellow_0(sK2,sK4))
    | ~ r2_yellow_0(sK2,sK3)
    | ~ m1_subset_1(k2_yellow_0(sK2,sK4),u1_struct_0(sK2))
    | k2_yellow_0(sK2,sK3) = k2_yellow_0(sK2,sK4)
    | ~ spl20_3
    | ~ spl20_25
    | ~ spl20_102
    | ~ spl20_105 ),
    inference(resolution,[],[f4871,f3260])).

fof(f3260,plain,(
    ! [X4,X5] :
      ( ~ r1_orders_2(sK2,sK9(sK2,X4,X5),X5)
      | ~ r1_lattice3(sK2,X4,X5)
      | ~ r2_yellow_0(sK2,X4)
      | ~ m1_subset_1(X5,u1_struct_0(sK2))
      | k2_yellow_0(sK2,X4) = X5 ) ),
    inference(resolution,[],[f3161,f3183])).

fof(f3183,plain,(
    ! [X2,X0,X1] :
      ( ~ l1_orders_2(X0)
      | ~ r1_orders_2(X0,sK9(X0,X1,X2),X2)
      | ~ r1_lattice3(X0,X1,X2)
      | ~ r2_yellow_0(X0,X1)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | k2_yellow_0(X0,X1) = X2 ) ),
    inference(cnf_transformation,[],[f3134])).

fof(f3134,plain,(
    ! [X0] :
      ( ! [X1,X2] :
          ( ( ( k2_yellow_0(X0,X1) = X2
              | ( ~ r1_orders_2(X0,sK9(X0,X1,X2),X2)
                & r1_lattice3(X0,X1,sK9(X0,X1,X2))
                & m1_subset_1(sK9(X0,X1,X2),u1_struct_0(X0)) )
              | ~ r1_lattice3(X0,X1,X2) )
            & ( ( ! [X4] :
                    ( r1_orders_2(X0,X4,X2)
                    | ~ r1_lattice3(X0,X1,X4)
                    | ~ m1_subset_1(X4,u1_struct_0(X0)) )
                & r1_lattice3(X0,X1,X2) )
              | k2_yellow_0(X0,X1) != X2 ) )
          | ~ r2_yellow_0(X0,X1)
          | ~ m1_subset_1(X2,u1_struct_0(X0)) )
      | ~ l1_orders_2(X0) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK9])],[f3132,f3133])).

fof(f3133,plain,(
    ! [X2,X1,X0] :
      ( ? [X3] :
          ( ~ r1_orders_2(X0,X3,X2)
          & r1_lattice3(X0,X1,X3)
          & m1_subset_1(X3,u1_struct_0(X0)) )
     => ( ~ r1_orders_2(X0,sK9(X0,X1,X2),X2)
        & r1_lattice3(X0,X1,sK9(X0,X1,X2))
        & m1_subset_1(sK9(X0,X1,X2),u1_struct_0(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f3132,plain,(
    ! [X0] :
      ( ! [X1,X2] :
          ( ( ( k2_yellow_0(X0,X1) = X2
              | ? [X3] :
                  ( ~ r1_orders_2(X0,X3,X2)
                  & r1_lattice3(X0,X1,X3)
                  & m1_subset_1(X3,u1_struct_0(X0)) )
              | ~ r1_lattice3(X0,X1,X2) )
            & ( ( ! [X4] :
                    ( r1_orders_2(X0,X4,X2)
                    | ~ r1_lattice3(X0,X1,X4)
                    | ~ m1_subset_1(X4,u1_struct_0(X0)) )
                & r1_lattice3(X0,X1,X2) )
              | k2_yellow_0(X0,X1) != X2 ) )
          | ~ r2_yellow_0(X0,X1)
          | ~ m1_subset_1(X2,u1_struct_0(X0)) )
      | ~ l1_orders_2(X0) ) ),
    inference(rectify,[],[f3131])).

fof(f3131,plain,(
    ! [X0] :
      ( ! [X1,X2] :
          ( ( ( k2_yellow_0(X0,X1) = X2
              | ? [X3] :
                  ( ~ r1_orders_2(X0,X3,X2)
                  & r1_lattice3(X0,X1,X3)
                  & m1_subset_1(X3,u1_struct_0(X0)) )
              | ~ r1_lattice3(X0,X1,X2) )
            & ( ( ! [X3] :
                    ( r1_orders_2(X0,X3,X2)
                    | ~ r1_lattice3(X0,X1,X3)
                    | ~ m1_subset_1(X3,u1_struct_0(X0)) )
                & r1_lattice3(X0,X1,X2) )
              | k2_yellow_0(X0,X1) != X2 ) )
          | ~ r2_yellow_0(X0,X1)
          | ~ m1_subset_1(X2,u1_struct_0(X0)) )
      | ~ l1_orders_2(X0) ) ),
    inference(flattening,[],[f3130])).

fof(f3130,plain,(
    ! [X0] :
      ( ! [X1,X2] :
          ( ( ( k2_yellow_0(X0,X1) = X2
              | ? [X3] :
                  ( ~ r1_orders_2(X0,X3,X2)
                  & r1_lattice3(X0,X1,X3)
                  & m1_subset_1(X3,u1_struct_0(X0)) )
              | ~ r1_lattice3(X0,X1,X2) )
            & ( ( ! [X3] :
                    ( r1_orders_2(X0,X3,X2)
                    | ~ r1_lattice3(X0,X1,X3)
                    | ~ m1_subset_1(X3,u1_struct_0(X0)) )
                & r1_lattice3(X0,X1,X2) )
              | k2_yellow_0(X0,X1) != X2 ) )
          | ~ r2_yellow_0(X0,X1)
          | ~ m1_subset_1(X2,u1_struct_0(X0)) )
      | ~ l1_orders_2(X0) ) ),
    inference(nnf_transformation,[],[f3072])).

fof(f3072,plain,(
    ! [X0] :
      ( ! [X1,X2] :
          ( ( k2_yellow_0(X0,X1) = X2
          <=> ( ! [X3] :
                  ( r1_orders_2(X0,X3,X2)
                  | ~ r1_lattice3(X0,X1,X3)
                  | ~ m1_subset_1(X3,u1_struct_0(X0)) )
              & r1_lattice3(X0,X1,X2) ) )
          | ~ r2_yellow_0(X0,X1)
          | ~ m1_subset_1(X2,u1_struct_0(X0)) )
      | ~ l1_orders_2(X0) ) ),
    inference(flattening,[],[f3071])).

fof(f3071,plain,(
    ! [X0] :
      ( ! [X1,X2] :
          ( ( k2_yellow_0(X0,X1) = X2
          <=> ( ! [X3] :
                  ( r1_orders_2(X0,X3,X2)
                  | ~ r1_lattice3(X0,X1,X3)
                  | ~ m1_subset_1(X3,u1_struct_0(X0)) )
              & r1_lattice3(X0,X1,X2) ) )
          | ~ r2_yellow_0(X0,X1)
          | ~ m1_subset_1(X2,u1_struct_0(X0)) )
      | ~ l1_orders_2(X0) ) ),
    inference(ennf_transformation,[],[f2968])).

fof(f2968,axiom,(
    ! [X0] :
      ( l1_orders_2(X0)
     => ! [X1,X2] :
          ( m1_subset_1(X2,u1_struct_0(X0))
         => ( r2_yellow_0(X0,X1)
           => ( k2_yellow_0(X0,X1) = X2
            <=> ( ! [X3] :
                    ( m1_subset_1(X3,u1_struct_0(X0))
                   => ( r1_lattice3(X0,X1,X3)
                     => r1_orders_2(X0,X3,X2) ) )
                & r1_lattice3(X0,X1,X2) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_yellow_0)).

fof(f4871,plain,
    ( r1_orders_2(sK2,sK9(sK2,sK3,k2_yellow_0(sK2,sK4)),k2_yellow_0(sK2,sK4))
    | ~ spl20_3
    | ~ spl20_25
    | ~ spl20_102
    | ~ spl20_105 ),
    inference(subsumption_resolution,[],[f4863,f4529])).

fof(f4529,plain,
    ( m1_subset_1(sK9(sK2,sK3,k2_yellow_0(sK2,sK4)),u1_struct_0(sK2))
    | ~ spl20_102 ),
    inference(avatar_component_clause,[],[f4528])).

fof(f4528,plain,
    ( spl20_102
  <=> m1_subset_1(sK9(sK2,sK3,k2_yellow_0(sK2,sK4)),u1_struct_0(sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl20_102])])).

fof(f4863,plain,
    ( ~ m1_subset_1(sK9(sK2,sK3,k2_yellow_0(sK2,sK4)),u1_struct_0(sK2))
    | r1_orders_2(sK2,sK9(sK2,sK3,k2_yellow_0(sK2,sK4)),k2_yellow_0(sK2,sK4))
    | ~ spl20_3
    | ~ spl20_25
    | ~ spl20_105 ),
    inference(resolution,[],[f4544,f3934])).

fof(f3934,plain,
    ( ! [X1] :
        ( ~ r1_lattice3(sK2,sK4,X1)
        | ~ m1_subset_1(X1,u1_struct_0(sK2))
        | r1_orders_2(sK2,X1,k2_yellow_0(sK2,sK4)) )
    | ~ spl20_3
    | ~ spl20_25 ),
    inference(subsumption_resolution,[],[f3931,f3538])).

fof(f3931,plain,
    ( ! [X1] :
        ( ~ m1_subset_1(X1,u1_struct_0(sK2))
        | ~ r1_lattice3(sK2,sK4,X1)
        | ~ m1_subset_1(k2_yellow_0(sK2,sK4),u1_struct_0(sK2))
        | r1_orders_2(sK2,X1,k2_yellow_0(sK2,sK4)) )
    | ~ spl20_3 ),
    inference(resolution,[],[f3290,f3451])).

fof(f3451,plain,
    ( r2_yellow_0(sK2,sK4)
    | ~ spl20_3 ),
    inference(resolution,[],[f3336,f3301])).

fof(f3301,plain,(
    ! [X1] :
      ( ~ sP0(sK2,X1)
      | r2_yellow_0(sK2,X1) ) ),
    inference(resolution,[],[f3275,f3201])).

fof(f3201,plain,(
    ! [X0,X1] :
      ( ~ sP1(X0)
      | ~ sP0(X0,X1)
      | r2_yellow_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f3143])).

fof(f3336,plain,
    ( sP0(sK2,sK4)
    | ~ spl20_3 ),
    inference(avatar_component_clause,[],[f3334])).

fof(f3290,plain,(
    ! [X72,X71] :
      ( ~ r2_yellow_0(sK2,X71)
      | ~ m1_subset_1(X72,u1_struct_0(sK2))
      | ~ r1_lattice3(sK2,X71,X72)
      | ~ m1_subset_1(k2_yellow_0(sK2,X71),u1_struct_0(sK2))
      | r1_orders_2(sK2,X72,k2_yellow_0(sK2,X71)) ) ),
    inference(resolution,[],[f3161,f3254])).

fof(f3254,plain,(
    ! [X4,X0,X1] :
      ( ~ l1_orders_2(X0)
      | ~ r1_lattice3(X0,X1,X4)
      | ~ m1_subset_1(X4,u1_struct_0(X0))
      | ~ r2_yellow_0(X0,X1)
      | ~ m1_subset_1(k2_yellow_0(X0,X1),u1_struct_0(X0))
      | r1_orders_2(X0,X4,k2_yellow_0(X0,X1)) ) ),
    inference(equality_resolution,[],[f3180])).

fof(f3180,plain,(
    ! [X4,X2,X0,X1] :
      ( r1_orders_2(X0,X4,X2)
      | ~ r1_lattice3(X0,X1,X4)
      | ~ m1_subset_1(X4,u1_struct_0(X0))
      | k2_yellow_0(X0,X1) != X2
      | ~ r2_yellow_0(X0,X1)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ l1_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f3134])).

fof(f4544,plain,
    ( r1_lattice3(sK2,sK4,sK9(sK2,sK3,k2_yellow_0(sK2,sK4)))
    | ~ spl20_105 ),
    inference(avatar_component_clause,[],[f4542])).

fof(f4542,plain,
    ( spl20_105
  <=> r1_lattice3(sK2,sK4,sK9(sK2,sK3,k2_yellow_0(sK2,sK4))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl20_105])])).

fof(f4770,plain,
    ( ~ spl20_102
    | spl20_105
    | ~ spl20_25
    | ~ spl20_26 ),
    inference(avatar_split_clause,[],[f4762,f3541,f3537,f4542,f4528])).

fof(f4762,plain,
    ( r1_lattice3(sK2,sK4,sK9(sK2,sK3,k2_yellow_0(sK2,sK4)))
    | ~ m1_subset_1(sK9(sK2,sK3,k2_yellow_0(sK2,sK4)),u1_struct_0(sK2))
    | ~ spl20_25
    | ~ spl20_26 ),
    inference(resolution,[],[f4225,f3163])).

fof(f4225,plain,
    ( r1_lattice3(sK2,sK3,sK9(sK2,sK3,k2_yellow_0(sK2,sK4)))
    | ~ spl20_25
    | ~ spl20_26 ),
    inference(subsumption_resolution,[],[f4224,f3165])).

fof(f4224,plain,
    ( r1_lattice3(sK2,sK3,sK9(sK2,sK3,k2_yellow_0(sK2,sK4)))
    | k2_yellow_0(sK2,sK3) = k2_yellow_0(sK2,sK4)
    | ~ spl20_25
    | ~ spl20_26 ),
    inference(subsumption_resolution,[],[f4219,f3538])).

fof(f4219,plain,
    ( r1_lattice3(sK2,sK3,sK9(sK2,sK3,k2_yellow_0(sK2,sK4)))
    | ~ m1_subset_1(k2_yellow_0(sK2,sK4),u1_struct_0(sK2))
    | k2_yellow_0(sK2,sK3) = k2_yellow_0(sK2,sK4)
    | ~ spl20_26 ),
    inference(resolution,[],[f3840,f3543])).

fof(f3840,plain,(
    ! [X0] :
      ( ~ r1_lattice3(sK2,sK3,X0)
      | r1_lattice3(sK2,sK3,sK9(sK2,sK3,X0))
      | ~ m1_subset_1(X0,u1_struct_0(sK2))
      | k2_yellow_0(sK2,sK3) = X0 ) ),
    inference(resolution,[],[f3259,f3162])).

fof(f3259,plain,(
    ! [X2,X3] :
      ( ~ r2_yellow_0(sK2,X2)
      | ~ r1_lattice3(sK2,X2,X3)
      | r1_lattice3(sK2,X2,sK9(sK2,X2,X3))
      | ~ m1_subset_1(X3,u1_struct_0(sK2))
      | k2_yellow_0(sK2,X2) = X3 ) ),
    inference(resolution,[],[f3161,f3182])).

fof(f3182,plain,(
    ! [X2,X0,X1] :
      ( ~ l1_orders_2(X0)
      | r1_lattice3(X0,X1,sK9(X0,X1,X2))
      | ~ r1_lattice3(X0,X1,X2)
      | ~ r2_yellow_0(X0,X1)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | k2_yellow_0(X0,X1) = X2 ) ),
    inference(cnf_transformation,[],[f3134])).

fof(f4552,plain,
    ( ~ spl20_25
    | ~ spl20_26
    | spl20_102 ),
    inference(avatar_contradiction_clause,[],[f4551])).

fof(f4551,plain,
    ( $false
    | ~ spl20_25
    | ~ spl20_26
    | spl20_102 ),
    inference(subsumption_resolution,[],[f4550,f3161])).

fof(f4550,plain,
    ( ~ l1_orders_2(sK2)
    | ~ spl20_25
    | ~ spl20_26
    | spl20_102 ),
    inference(subsumption_resolution,[],[f4549,f3538])).

fof(f4549,plain,
    ( ~ m1_subset_1(k2_yellow_0(sK2,sK4),u1_struct_0(sK2))
    | ~ l1_orders_2(sK2)
    | ~ spl20_26
    | spl20_102 ),
    inference(subsumption_resolution,[],[f4548,f3162])).

fof(f4548,plain,
    ( ~ r2_yellow_0(sK2,sK3)
    | ~ m1_subset_1(k2_yellow_0(sK2,sK4),u1_struct_0(sK2))
    | ~ l1_orders_2(sK2)
    | ~ spl20_26
    | spl20_102 ),
    inference(subsumption_resolution,[],[f4547,f3543])).

fof(f4547,plain,
    ( ~ r1_lattice3(sK2,sK3,k2_yellow_0(sK2,sK4))
    | ~ r2_yellow_0(sK2,sK3)
    | ~ m1_subset_1(k2_yellow_0(sK2,sK4),u1_struct_0(sK2))
    | ~ l1_orders_2(sK2)
    | spl20_102 ),
    inference(subsumption_resolution,[],[f4546,f3165])).

fof(f4546,plain,
    ( k2_yellow_0(sK2,sK3) = k2_yellow_0(sK2,sK4)
    | ~ r1_lattice3(sK2,sK3,k2_yellow_0(sK2,sK4))
    | ~ r2_yellow_0(sK2,sK3)
    | ~ m1_subset_1(k2_yellow_0(sK2,sK4),u1_struct_0(sK2))
    | ~ l1_orders_2(sK2)
    | spl20_102 ),
    inference(resolution,[],[f4530,f3181])).

fof(f3181,plain,(
    ! [X2,X0,X1] :
      ( m1_subset_1(sK9(X0,X1,X2),u1_struct_0(X0))
      | k2_yellow_0(X0,X1) = X2
      | ~ r1_lattice3(X0,X1,X2)
      | ~ r2_yellow_0(X0,X1)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ l1_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f3134])).

fof(f4530,plain,
    ( ~ m1_subset_1(sK9(sK2,sK3,k2_yellow_0(sK2,sK4)),u1_struct_0(sK2))
    | spl20_102 ),
    inference(avatar_component_clause,[],[f4528])).

fof(f3547,plain,(
    spl20_25 ),
    inference(avatar_contradiction_clause,[],[f3546])).

fof(f3546,plain,
    ( $false
    | spl20_25 ),
    inference(subsumption_resolution,[],[f3545,f3161])).

fof(f3545,plain,
    ( ~ l1_orders_2(sK2)
    | spl20_25 ),
    inference(resolution,[],[f3539,f3177])).

fof(f3177,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k2_yellow_0(X0,X1),u1_struct_0(X0))
      | ~ l1_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f3068])).

fof(f3068,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k2_yellow_0(X0,X1),u1_struct_0(X0))
      | ~ l1_orders_2(X0) ) ),
    inference(ennf_transformation,[],[f2979])).

fof(f2979,axiom,(
    ! [X0,X1] :
      ( l1_orders_2(X0)
     => m1_subset_1(k2_yellow_0(X0,X1),u1_struct_0(X0)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k2_yellow_0)).

fof(f3539,plain,
    ( ~ m1_subset_1(k2_yellow_0(sK2,sK4),u1_struct_0(sK2))
    | spl20_25 ),
    inference(avatar_component_clause,[],[f3537])).

fof(f3544,plain,
    ( ~ spl20_25
    | spl20_26
    | ~ spl20_3 ),
    inference(avatar_split_clause,[],[f3530,f3334,f3541,f3537])).

fof(f3530,plain,
    ( r1_lattice3(sK2,sK3,k2_yellow_0(sK2,sK4))
    | ~ m1_subset_1(k2_yellow_0(sK2,sK4),u1_struct_0(sK2))
    | ~ spl20_3 ),
    inference(resolution,[],[f3485,f3164])).

fof(f3485,plain,
    ( r1_lattice3(sK2,sK4,k2_yellow_0(sK2,sK4))
    | ~ spl20_3 ),
    inference(resolution,[],[f3476,f3451])).

fof(f3476,plain,(
    ! [X0] :
      ( ~ r2_yellow_0(sK2,X0)
      | r1_lattice3(sK2,X0,k2_yellow_0(sK2,X0)) ) ),
    inference(subsumption_resolution,[],[f3475,f3161])).

fof(f3475,plain,(
    ! [X0] :
      ( ~ r2_yellow_0(sK2,X0)
      | r1_lattice3(sK2,X0,k2_yellow_0(sK2,X0))
      | ~ l1_orders_2(sK2) ) ),
    inference(resolution,[],[f3291,f3177])).

fof(f3291,plain,(
    ! [X73] :
      ( ~ m1_subset_1(k2_yellow_0(sK2,X73),u1_struct_0(sK2))
      | ~ r2_yellow_0(sK2,X73)
      | r1_lattice3(sK2,X73,k2_yellow_0(sK2,X73)) ) ),
    inference(resolution,[],[f3161,f3255])).

fof(f3255,plain,(
    ! [X0,X1] :
      ( ~ l1_orders_2(X0)
      | ~ r2_yellow_0(X0,X1)
      | ~ m1_subset_1(k2_yellow_0(X0,X1),u1_struct_0(X0))
      | r1_lattice3(X0,X1,k2_yellow_0(X0,X1)) ) ),
    inference(equality_resolution,[],[f3179])).

fof(f3179,plain,(
    ! [X2,X0,X1] :
      ( r1_lattice3(X0,X1,X2)
      | k2_yellow_0(X0,X1) != X2
      | ~ r2_yellow_0(X0,X1)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ l1_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f3134])).
%------------------------------------------------------------------------------
