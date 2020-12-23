%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT1555+2 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n011.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Wed Dec 16 12:10:24 EST 2020

% Result     : Theorem 2.01s
% Output     : Refutation 2.01s
% Verified   : 
% Statistics : Number of formulae       :  133 ( 687 expanded)
%              Number of leaves         :   22 ( 241 expanded)
%              Depth                    :   28
%              Number of atoms          :  751 (7578 expanded)
%              Number of equality atoms :   70 ( 958 expanded)
%              Maximal formula depth    :   14 (   7 average)
%              Maximal term depth       :    2 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f4148,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f3460,f3465,f3470,f3474,f3475,f3729,f3742,f3762,f3768,f4147])).

fof(f4147,plain,
    ( spl41_1
    | ~ spl41_2
    | ~ spl41_6 ),
    inference(avatar_contradiction_clause,[],[f4146])).

fof(f4146,plain,
    ( $false
    | spl41_1
    | ~ spl41_2
    | ~ spl41_6 ),
    inference(subsumption_resolution,[],[f4145,f3454])).

fof(f3454,plain,
    ( r1_lattice3(sK2,sK4,sK3)
    | ~ spl41_2 ),
    inference(avatar_component_clause,[],[f3453])).

fof(f3453,plain,
    ( spl41_2
  <=> r1_lattice3(sK2,sK4,sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl41_2])])).

fof(f4145,plain,
    ( ~ r1_lattice3(sK2,sK4,sK3)
    | spl41_1
    | ~ spl41_6 ),
    inference(subsumption_resolution,[],[f4144,f3231])).

fof(f3231,plain,(
    m1_subset_1(sK3,u1_struct_0(sK2)) ),
    inference(cnf_transformation,[],[f3136])).

fof(f3136,plain,
    ( ( ( ~ r1_orders_2(sK2,sK5,sK3)
        & r1_lattice3(sK2,sK4,sK5)
        & m1_subset_1(sK5,u1_struct_0(sK2)) )
      | ~ r1_lattice3(sK2,sK4,sK3)
      | sK3 != k2_yellow_0(sK2,sK4) )
    & ( ( ! [X4] :
            ( r1_orders_2(sK2,X4,sK3)
            | ~ r1_lattice3(sK2,sK4,X4)
            | ~ m1_subset_1(X4,u1_struct_0(sK2)) )
        & r1_lattice3(sK2,sK4,sK3) )
      | sK3 = k2_yellow_0(sK2,sK4) )
    & m1_subset_1(sK3,u1_struct_0(sK2))
    & l1_orders_2(sK2)
    & v3_lattice3(sK2)
    & v5_orders_2(sK2)
    & ~ v2_struct_0(sK2) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2,sK3,sK4,sK5])],[f3131,f3135,f3134,f3133,f3132])).

fof(f3132,plain,
    ( ? [X0] :
        ( ? [X1] :
            ( ? [X2] :
                ( ( ? [X3] :
                      ( ~ r1_orders_2(X0,X3,X1)
                      & r1_lattice3(X0,X2,X3)
                      & m1_subset_1(X3,u1_struct_0(X0)) )
                  | ~ r1_lattice3(X0,X2,X1)
                  | k2_yellow_0(X0,X2) != X1 )
                & ( ( ! [X4] :
                        ( r1_orders_2(X0,X4,X1)
                        | ~ r1_lattice3(X0,X2,X4)
                        | ~ m1_subset_1(X4,u1_struct_0(X0)) )
                    & r1_lattice3(X0,X2,X1) )
                  | k2_yellow_0(X0,X2) = X1 ) )
            & m1_subset_1(X1,u1_struct_0(X0)) )
        & l1_orders_2(X0)
        & v3_lattice3(X0)
        & v5_orders_2(X0)
        & ~ v2_struct_0(X0) )
   => ( ? [X1] :
          ( ? [X2] :
              ( ( ? [X3] :
                    ( ~ r1_orders_2(sK2,X3,X1)
                    & r1_lattice3(sK2,X2,X3)
                    & m1_subset_1(X3,u1_struct_0(sK2)) )
                | ~ r1_lattice3(sK2,X2,X1)
                | k2_yellow_0(sK2,X2) != X1 )
              & ( ( ! [X4] :
                      ( r1_orders_2(sK2,X4,X1)
                      | ~ r1_lattice3(sK2,X2,X4)
                      | ~ m1_subset_1(X4,u1_struct_0(sK2)) )
                  & r1_lattice3(sK2,X2,X1) )
                | k2_yellow_0(sK2,X2) = X1 ) )
          & m1_subset_1(X1,u1_struct_0(sK2)) )
      & l1_orders_2(sK2)
      & v3_lattice3(sK2)
      & v5_orders_2(sK2)
      & ~ v2_struct_0(sK2) ) ),
    introduced(choice_axiom,[])).

fof(f3133,plain,
    ( ? [X1] :
        ( ? [X2] :
            ( ( ? [X3] :
                  ( ~ r1_orders_2(sK2,X3,X1)
                  & r1_lattice3(sK2,X2,X3)
                  & m1_subset_1(X3,u1_struct_0(sK2)) )
              | ~ r1_lattice3(sK2,X2,X1)
              | k2_yellow_0(sK2,X2) != X1 )
            & ( ( ! [X4] :
                    ( r1_orders_2(sK2,X4,X1)
                    | ~ r1_lattice3(sK2,X2,X4)
                    | ~ m1_subset_1(X4,u1_struct_0(sK2)) )
                & r1_lattice3(sK2,X2,X1) )
              | k2_yellow_0(sK2,X2) = X1 ) )
        & m1_subset_1(X1,u1_struct_0(sK2)) )
   => ( ? [X2] :
          ( ( ? [X3] :
                ( ~ r1_orders_2(sK2,X3,sK3)
                & r1_lattice3(sK2,X2,X3)
                & m1_subset_1(X3,u1_struct_0(sK2)) )
            | ~ r1_lattice3(sK2,X2,sK3)
            | k2_yellow_0(sK2,X2) != sK3 )
          & ( ( ! [X4] :
                  ( r1_orders_2(sK2,X4,sK3)
                  | ~ r1_lattice3(sK2,X2,X4)
                  | ~ m1_subset_1(X4,u1_struct_0(sK2)) )
              & r1_lattice3(sK2,X2,sK3) )
            | k2_yellow_0(sK2,X2) = sK3 ) )
      & m1_subset_1(sK3,u1_struct_0(sK2)) ) ),
    introduced(choice_axiom,[])).

fof(f3134,plain,
    ( ? [X2] :
        ( ( ? [X3] :
              ( ~ r1_orders_2(sK2,X3,sK3)
              & r1_lattice3(sK2,X2,X3)
              & m1_subset_1(X3,u1_struct_0(sK2)) )
          | ~ r1_lattice3(sK2,X2,sK3)
          | k2_yellow_0(sK2,X2) != sK3 )
        & ( ( ! [X4] :
                ( r1_orders_2(sK2,X4,sK3)
                | ~ r1_lattice3(sK2,X2,X4)
                | ~ m1_subset_1(X4,u1_struct_0(sK2)) )
            & r1_lattice3(sK2,X2,sK3) )
          | k2_yellow_0(sK2,X2) = sK3 ) )
   => ( ( ? [X3] :
            ( ~ r1_orders_2(sK2,X3,sK3)
            & r1_lattice3(sK2,sK4,X3)
            & m1_subset_1(X3,u1_struct_0(sK2)) )
        | ~ r1_lattice3(sK2,sK4,sK3)
        | sK3 != k2_yellow_0(sK2,sK4) )
      & ( ( ! [X4] :
              ( r1_orders_2(sK2,X4,sK3)
              | ~ r1_lattice3(sK2,sK4,X4)
              | ~ m1_subset_1(X4,u1_struct_0(sK2)) )
          & r1_lattice3(sK2,sK4,sK3) )
        | sK3 = k2_yellow_0(sK2,sK4) ) ) ),
    introduced(choice_axiom,[])).

fof(f3135,plain,
    ( ? [X3] :
        ( ~ r1_orders_2(sK2,X3,sK3)
        & r1_lattice3(sK2,sK4,X3)
        & m1_subset_1(X3,u1_struct_0(sK2)) )
   => ( ~ r1_orders_2(sK2,sK5,sK3)
      & r1_lattice3(sK2,sK4,sK5)
      & m1_subset_1(sK5,u1_struct_0(sK2)) ) ),
    introduced(choice_axiom,[])).

fof(f3131,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ( ? [X3] :
                    ( ~ r1_orders_2(X0,X3,X1)
                    & r1_lattice3(X0,X2,X3)
                    & m1_subset_1(X3,u1_struct_0(X0)) )
                | ~ r1_lattice3(X0,X2,X1)
                | k2_yellow_0(X0,X2) != X1 )
              & ( ( ! [X4] :
                      ( r1_orders_2(X0,X4,X1)
                      | ~ r1_lattice3(X0,X2,X4)
                      | ~ m1_subset_1(X4,u1_struct_0(X0)) )
                  & r1_lattice3(X0,X2,X1) )
                | k2_yellow_0(X0,X2) = X1 ) )
          & m1_subset_1(X1,u1_struct_0(X0)) )
      & l1_orders_2(X0)
      & v3_lattice3(X0)
      & v5_orders_2(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(rectify,[],[f3130])).

fof(f3130,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ( ? [X3] :
                    ( ~ r1_orders_2(X0,X3,X1)
                    & r1_lattice3(X0,X2,X3)
                    & m1_subset_1(X3,u1_struct_0(X0)) )
                | ~ r1_lattice3(X0,X2,X1)
                | k2_yellow_0(X0,X2) != X1 )
              & ( ( ! [X3] :
                      ( r1_orders_2(X0,X3,X1)
                      | ~ r1_lattice3(X0,X2,X3)
                      | ~ m1_subset_1(X3,u1_struct_0(X0)) )
                  & r1_lattice3(X0,X2,X1) )
                | k2_yellow_0(X0,X2) = X1 ) )
          & m1_subset_1(X1,u1_struct_0(X0)) )
      & l1_orders_2(X0)
      & v3_lattice3(X0)
      & v5_orders_2(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(flattening,[],[f3129])).

fof(f3129,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ( ? [X3] :
                    ( ~ r1_orders_2(X0,X3,X1)
                    & r1_lattice3(X0,X2,X3)
                    & m1_subset_1(X3,u1_struct_0(X0)) )
                | ~ r1_lattice3(X0,X2,X1)
                | k2_yellow_0(X0,X2) != X1 )
              & ( ( ! [X3] :
                      ( r1_orders_2(X0,X3,X1)
                      | ~ r1_lattice3(X0,X2,X3)
                      | ~ m1_subset_1(X3,u1_struct_0(X0)) )
                  & r1_lattice3(X0,X2,X1) )
                | k2_yellow_0(X0,X2) = X1 ) )
          & m1_subset_1(X1,u1_struct_0(X0)) )
      & l1_orders_2(X0)
      & v3_lattice3(X0)
      & v5_orders_2(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(nnf_transformation,[],[f3031])).

fof(f3031,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( k2_yellow_0(X0,X2) = X1
            <~> ( ! [X3] :
                    ( r1_orders_2(X0,X3,X1)
                    | ~ r1_lattice3(X0,X2,X3)
                    | ~ m1_subset_1(X3,u1_struct_0(X0)) )
                & r1_lattice3(X0,X2,X1) ) )
          & m1_subset_1(X1,u1_struct_0(X0)) )
      & l1_orders_2(X0)
      & v3_lattice3(X0)
      & v5_orders_2(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(flattening,[],[f3030])).

fof(f3030,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( k2_yellow_0(X0,X2) = X1
            <~> ( ! [X3] :
                    ( r1_orders_2(X0,X3,X1)
                    | ~ r1_lattice3(X0,X2,X3)
                    | ~ m1_subset_1(X3,u1_struct_0(X0)) )
                & r1_lattice3(X0,X2,X1) ) )
          & m1_subset_1(X1,u1_struct_0(X0)) )
      & l1_orders_2(X0)
      & v3_lattice3(X0)
      & v5_orders_2(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f3010])).

fof(f3010,negated_conjecture,(
    ~ ! [X0] :
        ( ( l1_orders_2(X0)
          & v3_lattice3(X0)
          & v5_orders_2(X0)
          & ~ v2_struct_0(X0) )
       => ! [X1] :
            ( m1_subset_1(X1,u1_struct_0(X0))
           => ! [X2] :
                ( k2_yellow_0(X0,X2) = X1
              <=> ( ! [X3] :
                      ( m1_subset_1(X3,u1_struct_0(X0))
                     => ( r1_lattice3(X0,X2,X3)
                       => r1_orders_2(X0,X3,X1) ) )
                  & r1_lattice3(X0,X2,X1) ) ) ) ) ),
    inference(negated_conjecture,[],[f3009])).

fof(f3009,conjecture,(
    ! [X0] :
      ( ( l1_orders_2(X0)
        & v3_lattice3(X0)
        & v5_orders_2(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,u1_struct_0(X0))
         => ! [X2] :
              ( k2_yellow_0(X0,X2) = X1
            <=> ( ! [X3] :
                    ( m1_subset_1(X3,u1_struct_0(X0))
                   => ( r1_lattice3(X0,X2,X3)
                     => r1_orders_2(X0,X3,X1) ) )
                & r1_lattice3(X0,X2,X1) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t33_yellow_0)).

fof(f4144,plain,
    ( ~ m1_subset_1(sK3,u1_struct_0(sK2))
    | ~ r1_lattice3(sK2,sK4,sK3)
    | spl41_1
    | ~ spl41_6 ),
    inference(resolution,[],[f4063,f3992])).

fof(f3992,plain,(
    ! [X2,X1] :
      ( r1_orders_2(sK2,X2,k2_yellow_0(sK2,X1))
      | ~ m1_subset_1(X2,u1_struct_0(sK2))
      | ~ r1_lattice3(sK2,X1,X2) ) ),
    inference(subsumption_resolution,[],[f3774,f3790])).

fof(f3790,plain,(
    ! [X1] : r2_yellow_0(sK2,X1) ),
    inference(subsumption_resolution,[],[f3731,f3785])).

fof(f3785,plain,(
    ! [X0] : sP0(sK2,X0) ),
    inference(subsumption_resolution,[],[f3784,f3227])).

fof(f3227,plain,(
    ~ v2_struct_0(sK2) ),
    inference(cnf_transformation,[],[f3136])).

fof(f3784,plain,(
    ! [X0] :
      ( sP0(sK2,X0)
      | v2_struct_0(sK2) ) ),
    inference(subsumption_resolution,[],[f3783,f3228])).

fof(f3228,plain,(
    v5_orders_2(sK2) ),
    inference(cnf_transformation,[],[f3136])).

fof(f3783,plain,(
    ! [X0] :
      ( sP0(sK2,X0)
      | ~ v5_orders_2(sK2)
      | v2_struct_0(sK2) ) ),
    inference(subsumption_resolution,[],[f3782,f3229])).

fof(f3229,plain,(
    v3_lattice3(sK2) ),
    inference(cnf_transformation,[],[f3136])).

fof(f3782,plain,(
    ! [X0] :
      ( sP0(sK2,X0)
      | ~ v3_lattice3(sK2)
      | ~ v5_orders_2(sK2)
      | v2_struct_0(sK2) ) ),
    inference(subsumption_resolution,[],[f3781,f3230])).

fof(f3230,plain,(
    l1_orders_2(sK2) ),
    inference(cnf_transformation,[],[f3136])).

fof(f3781,plain,(
    ! [X0] :
      ( sP0(sK2,X0)
      | ~ l1_orders_2(sK2)
      | ~ v3_lattice3(sK2)
      | ~ v5_orders_2(sK2)
      | v2_struct_0(sK2) ) ),
    inference(resolution,[],[f3730,f3429])).

fof(f3429,plain,(
    ! [X0,X1] :
      ( r2_yellow_0(X0,X1)
      | ~ l1_orders_2(X0)
      | ~ v3_lattice3(X0)
      | ~ v5_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f3121])).

fof(f3121,plain,(
    ! [X0] :
      ( ! [X1] : r2_yellow_0(X0,X1)
      | ~ l1_orders_2(X0)
      | ~ v3_lattice3(X0)
      | ~ v5_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f3120])).

fof(f3120,plain,(
    ! [X0] :
      ( ! [X1] : r2_yellow_0(X0,X1)
      | ~ l1_orders_2(X0)
      | ~ v3_lattice3(X0)
      | ~ v5_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f3021])).

fof(f3021,plain,(
    ! [X0] :
      ( ( l1_orders_2(X0)
        & v3_lattice3(X0)
        & v5_orders_2(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] : r2_yellow_0(X0,X1) ) ),
    inference(pure_predicate_removal,[],[f2991])).

fof(f2991,axiom,(
    ! [X0] :
      ( ( l1_orders_2(X0)
        & v3_lattice3(X0)
        & v5_orders_2(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( r2_yellow_0(X0,X1)
          & r1_yellow_0(X0,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t17_yellow_0)).

fof(f3730,plain,(
    ! [X0] :
      ( ~ r2_yellow_0(sK2,X0)
      | sP0(sK2,X0) ) ),
    inference(resolution,[],[f3638,f3344])).

fof(f3344,plain,(
    ! [X0,X1] :
      ( ~ sP1(X0)
      | ~ r2_yellow_0(X0,X1)
      | sP0(X0,X1) ) ),
    inference(cnf_transformation,[],[f3186])).

fof(f3186,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( r2_yellow_0(X0,X1)
            | ~ sP0(X0,X1) )
          & ( sP0(X0,X1)
            | ~ r2_yellow_0(X0,X1) ) )
      | ~ sP1(X0) ) ),
    inference(nnf_transformation,[],[f3127])).

fof(f3127,plain,(
    ! [X0] :
      ( ! [X1] :
          ( r2_yellow_0(X0,X1)
        <=> sP0(X0,X1) )
      | ~ sP1(X0) ) ),
    introduced(predicate_definition_introduction,[new_symbols(naming,[sP1])])).

fof(f3638,plain,(
    sP1(sK2) ),
    inference(resolution,[],[f3230,f3364])).

fof(f3364,plain,(
    ! [X0] :
      ( ~ l1_orders_2(X0)
      | sP1(X0) ) ),
    inference(cnf_transformation,[],[f3128])).

fof(f3128,plain,(
    ! [X0] :
      ( sP1(X0)
      | ~ l1_orders_2(X0) ) ),
    inference(definition_folding,[],[f3081,f3127,f3126])).

fof(f3126,plain,(
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

fof(f3081,plain,(
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
    inference(flattening,[],[f3080])).

fof(f3080,plain,(
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
    inference(ennf_transformation,[],[f3020])).

fof(f3020,plain,(
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
    inference(rectify,[],[f2973])).

fof(f2973,axiom,(
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

fof(f3731,plain,(
    ! [X1] :
      ( ~ sP0(sK2,X1)
      | r2_yellow_0(sK2,X1) ) ),
    inference(resolution,[],[f3638,f3345])).

fof(f3345,plain,(
    ! [X0,X1] :
      ( ~ sP1(X0)
      | ~ sP0(X0,X1)
      | r2_yellow_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f3186])).

fof(f3774,plain,(
    ! [X2,X1] :
      ( ~ r1_lattice3(sK2,X1,X2)
      | ~ m1_subset_1(X2,u1_struct_0(sK2))
      | ~ r2_yellow_0(sK2,X1)
      | r1_orders_2(sK2,X2,k2_yellow_0(sK2,X1)) ) ),
    inference(subsumption_resolution,[],[f3770,f3230])).

fof(f3770,plain,(
    ! [X2,X1] :
      ( ~ r1_lattice3(sK2,X1,X2)
      | ~ m1_subset_1(X2,u1_struct_0(sK2))
      | ~ r2_yellow_0(sK2,X1)
      | r1_orders_2(sK2,X2,k2_yellow_0(sK2,X1))
      | ~ l1_orders_2(sK2) ) ),
    inference(resolution,[],[f3641,f3441])).

fof(f3441,plain,(
    ! [X4,X0,X1] :
      ( ~ m1_subset_1(k2_yellow_0(X0,X1),u1_struct_0(X0))
      | ~ r1_lattice3(X0,X1,X4)
      | ~ m1_subset_1(X4,u1_struct_0(X0))
      | ~ r2_yellow_0(X0,X1)
      | r1_orders_2(X0,X4,k2_yellow_0(X0,X1))
      | ~ l1_orders_2(X0) ) ),
    inference(equality_resolution,[],[f3338])).

fof(f3338,plain,(
    ! [X4,X2,X0,X1] :
      ( r1_orders_2(X0,X4,X2)
      | ~ r1_lattice3(X0,X1,X4)
      | ~ m1_subset_1(X4,u1_struct_0(X0))
      | k2_yellow_0(X0,X1) != X2
      | ~ r2_yellow_0(X0,X1)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ l1_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f3185])).

fof(f3185,plain,(
    ! [X0] :
      ( ! [X1,X2] :
          ( ( ( k2_yellow_0(X0,X1) = X2
              | ( ~ r1_orders_2(X0,sK24(X0,X1,X2),X2)
                & r1_lattice3(X0,X1,sK24(X0,X1,X2))
                & m1_subset_1(sK24(X0,X1,X2),u1_struct_0(X0)) )
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
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK24])],[f3183,f3184])).

fof(f3184,plain,(
    ! [X2,X1,X0] :
      ( ? [X3] :
          ( ~ r1_orders_2(X0,X3,X2)
          & r1_lattice3(X0,X1,X3)
          & m1_subset_1(X3,u1_struct_0(X0)) )
     => ( ~ r1_orders_2(X0,sK24(X0,X1,X2),X2)
        & r1_lattice3(X0,X1,sK24(X0,X1,X2))
        & m1_subset_1(sK24(X0,X1,X2),u1_struct_0(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f3183,plain,(
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
    inference(rectify,[],[f3182])).

fof(f3182,plain,(
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
    inference(flattening,[],[f3181])).

fof(f3181,plain,(
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
    inference(nnf_transformation,[],[f3078])).

fof(f3078,plain,(
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
    inference(flattening,[],[f3077])).

fof(f3077,plain,(
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

fof(f3641,plain,(
    ! [X80] : m1_subset_1(k2_yellow_0(sK2,X80),u1_struct_0(sK2)) ),
    inference(resolution,[],[f3230,f3380])).

fof(f3380,plain,(
    ! [X0,X1] :
      ( ~ l1_orders_2(X0)
      | m1_subset_1(k2_yellow_0(X0,X1),u1_struct_0(X0)) ) ),
    inference(cnf_transformation,[],[f3093])).

fof(f3093,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k2_yellow_0(X0,X1),u1_struct_0(X0))
      | ~ l1_orders_2(X0) ) ),
    inference(ennf_transformation,[],[f2977])).

fof(f2977,axiom,(
    ! [X0,X1] :
      ( l1_orders_2(X0)
     => m1_subset_1(k2_yellow_0(X0,X1),u1_struct_0(X0)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k2_yellow_0)).

fof(f4063,plain,
    ( ~ r1_orders_2(sK2,sK3,k2_yellow_0(sK2,sK4))
    | spl41_1
    | ~ spl41_6 ),
    inference(subsumption_resolution,[],[f4062,f3451])).

fof(f3451,plain,
    ( sK3 != k2_yellow_0(sK2,sK4)
    | spl41_1 ),
    inference(avatar_component_clause,[],[f3449])).

fof(f3449,plain,
    ( spl41_1
  <=> sK3 = k2_yellow_0(sK2,sK4) ),
    introduced(avatar_definition,[new_symbols(naming,[spl41_1])])).

fof(f4062,plain,
    ( ~ r1_orders_2(sK2,sK3,k2_yellow_0(sK2,sK4))
    | sK3 = k2_yellow_0(sK2,sK4)
    | ~ spl41_6 ),
    inference(subsumption_resolution,[],[f4061,f3231])).

fof(f4061,plain,
    ( ~ r1_orders_2(sK2,sK3,k2_yellow_0(sK2,sK4))
    | ~ m1_subset_1(sK3,u1_struct_0(sK2))
    | sK3 = k2_yellow_0(sK2,sK4)
    | ~ spl41_6 ),
    inference(subsumption_resolution,[],[f4032,f3641])).

fof(f4032,plain,
    ( ~ r1_orders_2(sK2,sK3,k2_yellow_0(sK2,sK4))
    | ~ m1_subset_1(k2_yellow_0(sK2,sK4),u1_struct_0(sK2))
    | ~ m1_subset_1(sK3,u1_struct_0(sK2))
    | sK3 = k2_yellow_0(sK2,sK4)
    | ~ spl41_6 ),
    inference(resolution,[],[f3498,f3865])).

fof(f3865,plain,
    ( r1_orders_2(sK2,k2_yellow_0(sK2,sK4),sK3)
    | ~ spl41_6 ),
    inference(subsumption_resolution,[],[f3859,f3641])).

fof(f3859,plain,
    ( ~ m1_subset_1(k2_yellow_0(sK2,sK4),u1_struct_0(sK2))
    | r1_orders_2(sK2,k2_yellow_0(sK2,sK4),sK3)
    | ~ spl41_6 ),
    inference(resolution,[],[f3855,f3473])).

fof(f3473,plain,
    ( ! [X4] :
        ( ~ r1_lattice3(sK2,sK4,X4)
        | ~ m1_subset_1(X4,u1_struct_0(sK2))
        | r1_orders_2(sK2,X4,sK3) )
    | ~ spl41_6 ),
    inference(avatar_component_clause,[],[f3472])).

fof(f3472,plain,
    ( spl41_6
  <=> ! [X4] :
        ( r1_orders_2(sK2,X4,sK3)
        | ~ m1_subset_1(X4,u1_struct_0(sK2))
        | ~ r1_lattice3(sK2,sK4,X4) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl41_6])])).

fof(f3855,plain,(
    ! [X0] : r1_lattice3(sK2,X0,k2_yellow_0(sK2,X0)) ),
    inference(subsumption_resolution,[],[f3773,f3790])).

fof(f3773,plain,(
    ! [X0] :
      ( ~ r2_yellow_0(sK2,X0)
      | r1_lattice3(sK2,X0,k2_yellow_0(sK2,X0)) ) ),
    inference(subsumption_resolution,[],[f3769,f3230])).

fof(f3769,plain,(
    ! [X0] :
      ( ~ r2_yellow_0(sK2,X0)
      | r1_lattice3(sK2,X0,k2_yellow_0(sK2,X0))
      | ~ l1_orders_2(sK2) ) ),
    inference(resolution,[],[f3641,f3442])).

fof(f3442,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(k2_yellow_0(X0,X1),u1_struct_0(X0))
      | ~ r2_yellow_0(X0,X1)
      | r1_lattice3(X0,X1,k2_yellow_0(X0,X1))
      | ~ l1_orders_2(X0) ) ),
    inference(equality_resolution,[],[f3337])).

fof(f3337,plain,(
    ! [X2,X0,X1] :
      ( r1_lattice3(X0,X1,X2)
      | k2_yellow_0(X0,X1) != X2
      | ~ r2_yellow_0(X0,X1)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ l1_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f3185])).

fof(f3498,plain,(
    ! [X2,X3] :
      ( ~ r1_orders_2(sK2,X2,X3)
      | ~ r1_orders_2(sK2,X3,X2)
      | ~ m1_subset_1(X2,u1_struct_0(sK2))
      | ~ m1_subset_1(X3,u1_struct_0(sK2))
      | X2 = X3 ) ),
    inference(global_subsumption,[],[f3230,f3477])).

fof(f3477,plain,(
    ! [X2,X3] :
      ( ~ r1_orders_2(sK2,X2,X3)
      | ~ r1_orders_2(sK2,X3,X2)
      | ~ m1_subset_1(X2,u1_struct_0(sK2))
      | ~ m1_subset_1(X3,u1_struct_0(sK2))
      | ~ l1_orders_2(sK2)
      | X2 = X3 ) ),
    inference(resolution,[],[f3228,f3238])).

fof(f3238,plain,(
    ! [X2,X0,X1] :
      ( ~ v5_orders_2(X0)
      | ~ r1_orders_2(X0,X2,X1)
      | ~ r1_orders_2(X0,X1,X2)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | X1 = X2 ) ),
    inference(cnf_transformation,[],[f3035])).

fof(f3035,plain,(
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
    inference(flattening,[],[f3034])).

fof(f3034,plain,(
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

fof(f3768,plain,(
    spl41_27 ),
    inference(avatar_contradiction_clause,[],[f3767])).

fof(f3767,plain,
    ( $false
    | spl41_27 ),
    inference(subsumption_resolution,[],[f3766,f3227])).

fof(f3766,plain,
    ( v2_struct_0(sK2)
    | spl41_27 ),
    inference(subsumption_resolution,[],[f3765,f3228])).

fof(f3765,plain,
    ( ~ v5_orders_2(sK2)
    | v2_struct_0(sK2)
    | spl41_27 ),
    inference(subsumption_resolution,[],[f3764,f3229])).

fof(f3764,plain,
    ( ~ v3_lattice3(sK2)
    | ~ v5_orders_2(sK2)
    | v2_struct_0(sK2)
    | spl41_27 ),
    inference(subsumption_resolution,[],[f3763,f3230])).

fof(f3763,plain,
    ( ~ l1_orders_2(sK2)
    | ~ v3_lattice3(sK2)
    | ~ v5_orders_2(sK2)
    | v2_struct_0(sK2)
    | spl41_27 ),
    inference(resolution,[],[f3720,f3429])).

fof(f3720,plain,
    ( ~ r2_yellow_0(sK2,sK4)
    | spl41_27 ),
    inference(avatar_component_clause,[],[f3718])).

fof(f3718,plain,
    ( spl41_27
  <=> r2_yellow_0(sK2,sK4) ),
    introduced(avatar_definition,[new_symbols(naming,[spl41_27])])).

fof(f3762,plain,
    ( spl41_3
    | ~ spl41_4
    | ~ spl41_5
    | ~ spl41_6 ),
    inference(avatar_contradiction_clause,[],[f3761])).

fof(f3761,plain,
    ( $false
    | spl41_3
    | ~ spl41_4
    | ~ spl41_5
    | ~ spl41_6 ),
    inference(subsumption_resolution,[],[f3760,f3469])).

fof(f3469,plain,
    ( m1_subset_1(sK5,u1_struct_0(sK2))
    | ~ spl41_5 ),
    inference(avatar_component_clause,[],[f3467])).

fof(f3467,plain,
    ( spl41_5
  <=> m1_subset_1(sK5,u1_struct_0(sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl41_5])])).

fof(f3760,plain,
    ( ~ m1_subset_1(sK5,u1_struct_0(sK2))
    | spl41_3
    | ~ spl41_4
    | ~ spl41_6 ),
    inference(subsumption_resolution,[],[f3754,f3459])).

fof(f3459,plain,
    ( ~ r1_orders_2(sK2,sK5,sK3)
    | spl41_3 ),
    inference(avatar_component_clause,[],[f3457])).

fof(f3457,plain,
    ( spl41_3
  <=> r1_orders_2(sK2,sK5,sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl41_3])])).

fof(f3754,plain,
    ( ~ m1_subset_1(sK5,u1_struct_0(sK2))
    | r1_orders_2(sK2,sK5,sK3)
    | ~ spl41_4
    | ~ spl41_6 ),
    inference(resolution,[],[f3464,f3473])).

fof(f3464,plain,
    ( r1_lattice3(sK2,sK4,sK5)
    | ~ spl41_4 ),
    inference(avatar_component_clause,[],[f3462])).

fof(f3462,plain,
    ( spl41_4
  <=> r1_lattice3(sK2,sK4,sK5) ),
    introduced(avatar_definition,[new_symbols(naming,[spl41_4])])).

fof(f3742,plain,
    ( spl41_2
    | ~ spl41_27
    | ~ spl41_1 ),
    inference(avatar_split_clause,[],[f3741,f3449,f3718,f3453])).

fof(f3741,plain,
    ( ~ r2_yellow_0(sK2,sK4)
    | r1_lattice3(sK2,sK4,sK3)
    | ~ spl41_1 ),
    inference(subsumption_resolution,[],[f3712,f3230])).

fof(f3712,plain,
    ( ~ r2_yellow_0(sK2,sK4)
    | r1_lattice3(sK2,sK4,sK3)
    | ~ l1_orders_2(sK2)
    | ~ spl41_1 ),
    inference(subsumption_resolution,[],[f3708,f3231])).

fof(f3708,plain,
    ( ~ m1_subset_1(sK3,u1_struct_0(sK2))
    | ~ r2_yellow_0(sK2,sK4)
    | r1_lattice3(sK2,sK4,sK3)
    | ~ l1_orders_2(sK2)
    | ~ spl41_1 ),
    inference(superposition,[],[f3442,f3450])).

fof(f3450,plain,
    ( sK3 = k2_yellow_0(sK2,sK4)
    | ~ spl41_1 ),
    inference(avatar_component_clause,[],[f3449])).

fof(f3729,plain,
    ( ~ spl41_27
    | spl41_6
    | ~ spl41_1 ),
    inference(avatar_split_clause,[],[f3728,f3449,f3472,f3718])).

fof(f3728,plain,
    ( ! [X1] :
        ( ~ r1_lattice3(sK2,sK4,X1)
        | ~ m1_subset_1(X1,u1_struct_0(sK2))
        | ~ r2_yellow_0(sK2,sK4)
        | r1_orders_2(sK2,X1,sK3) )
    | ~ spl41_1 ),
    inference(subsumption_resolution,[],[f3727,f3228])).

fof(f3727,plain,
    ( ! [X1] :
        ( ~ r1_lattice3(sK2,sK4,X1)
        | ~ m1_subset_1(X1,u1_struct_0(sK2))
        | ~ r2_yellow_0(sK2,sK4)
        | r1_orders_2(sK2,X1,sK3)
        | ~ v5_orders_2(sK2) )
    | ~ spl41_1 ),
    inference(subsumption_resolution,[],[f3726,f3230])).

fof(f3726,plain,
    ( ! [X1] :
        ( ~ r1_lattice3(sK2,sK4,X1)
        | ~ m1_subset_1(X1,u1_struct_0(sK2))
        | ~ r2_yellow_0(sK2,sK4)
        | r1_orders_2(sK2,X1,sK3)
        | ~ l1_orders_2(sK2)
        | ~ v5_orders_2(sK2) )
    | ~ spl41_1 ),
    inference(subsumption_resolution,[],[f3711,f3231])).

fof(f3711,plain,
    ( ! [X1] :
        ( ~ m1_subset_1(sK3,u1_struct_0(sK2))
        | ~ r1_lattice3(sK2,sK4,X1)
        | ~ m1_subset_1(X1,u1_struct_0(sK2))
        | ~ r2_yellow_0(sK2,sK4)
        | r1_orders_2(sK2,X1,sK3)
        | ~ l1_orders_2(sK2)
        | ~ v5_orders_2(sK2) )
    | ~ spl41_1 ),
    inference(superposition,[],[f3439,f3450])).

fof(f3439,plain,(
    ! [X4,X2,X0] :
      ( ~ m1_subset_1(k2_yellow_0(X0,X2),u1_struct_0(X0))
      | ~ r1_lattice3(X0,X2,X4)
      | ~ m1_subset_1(X4,u1_struct_0(X0))
      | ~ r2_yellow_0(X0,X2)
      | r1_orders_2(X0,X4,k2_yellow_0(X0,X2))
      | ~ l1_orders_2(X0)
      | ~ v5_orders_2(X0) ) ),
    inference(equality_resolution,[],[f3324])).

fof(f3324,plain,(
    ! [X4,X2,X0,X1] :
      ( r1_orders_2(X0,X4,X1)
      | ~ r1_lattice3(X0,X2,X4)
      | ~ m1_subset_1(X4,u1_struct_0(X0))
      | ~ r2_yellow_0(X0,X2)
      | k2_yellow_0(X0,X2) != X1
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | ~ v5_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f3180])).

fof(f3180,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( ( r2_yellow_0(X0,X2)
                  & k2_yellow_0(X0,X2) = X1 )
                | ( ~ r1_orders_2(X0,sK23(X0,X1,X2),X1)
                  & r1_lattice3(X0,X2,sK23(X0,X1,X2))
                  & m1_subset_1(sK23(X0,X1,X2),u1_struct_0(X0)) )
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
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK23])],[f3072,f3179])).

fof(f3179,plain,(
    ! [X2,X1,X0] :
      ( ? [X3] :
          ( ~ r1_orders_2(X0,X3,X1)
          & r1_lattice3(X0,X2,X3)
          & m1_subset_1(X3,u1_struct_0(X0)) )
     => ( ~ r1_orders_2(X0,sK23(X0,X1,X2),X1)
        & r1_lattice3(X0,X2,sK23(X0,X1,X2))
        & m1_subset_1(sK23(X0,X1,X2),u1_struct_0(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f3072,plain,(
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
    inference(flattening,[],[f3071])).

fof(f3071,plain,(
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
    inference(ennf_transformation,[],[f3019])).

fof(f3019,plain,(
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
    inference(rectify,[],[f3007])).

fof(f3007,axiom,(
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t31_yellow_0)).

fof(f3475,plain,
    ( spl41_1
    | spl41_2 ),
    inference(avatar_split_clause,[],[f3232,f3453,f3449])).

fof(f3232,plain,
    ( r1_lattice3(sK2,sK4,sK3)
    | sK3 = k2_yellow_0(sK2,sK4) ),
    inference(cnf_transformation,[],[f3136])).

fof(f3474,plain,
    ( spl41_1
    | spl41_6 ),
    inference(avatar_split_clause,[],[f3233,f3472,f3449])).

fof(f3233,plain,(
    ! [X4] :
      ( r1_orders_2(sK2,X4,sK3)
      | ~ r1_lattice3(sK2,sK4,X4)
      | ~ m1_subset_1(X4,u1_struct_0(sK2))
      | sK3 = k2_yellow_0(sK2,sK4) ) ),
    inference(cnf_transformation,[],[f3136])).

fof(f3470,plain,
    ( ~ spl41_1
    | ~ spl41_2
    | spl41_5 ),
    inference(avatar_split_clause,[],[f3234,f3467,f3453,f3449])).

fof(f3234,plain,
    ( m1_subset_1(sK5,u1_struct_0(sK2))
    | ~ r1_lattice3(sK2,sK4,sK3)
    | sK3 != k2_yellow_0(sK2,sK4) ),
    inference(cnf_transformation,[],[f3136])).

fof(f3465,plain,
    ( ~ spl41_1
    | ~ spl41_2
    | spl41_4 ),
    inference(avatar_split_clause,[],[f3235,f3462,f3453,f3449])).

fof(f3235,plain,
    ( r1_lattice3(sK2,sK4,sK5)
    | ~ r1_lattice3(sK2,sK4,sK3)
    | sK3 != k2_yellow_0(sK2,sK4) ),
    inference(cnf_transformation,[],[f3136])).

fof(f3460,plain,
    ( ~ spl41_1
    | ~ spl41_2
    | ~ spl41_3 ),
    inference(avatar_split_clause,[],[f3236,f3457,f3453,f3449])).

fof(f3236,plain,
    ( ~ r1_orders_2(sK2,sK5,sK3)
    | ~ r1_lattice3(sK2,sK4,sK3)
    | sK3 != k2_yellow_0(sK2,sK4) ),
    inference(cnf_transformation,[],[f3136])).
%------------------------------------------------------------------------------
