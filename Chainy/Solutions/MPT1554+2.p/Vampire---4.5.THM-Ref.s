%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT1554+2 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n008.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Wed Dec 16 12:10:24 EST 2020

% Result     : Theorem 1.41s
% Output     : Refutation 1.84s
% Verified   : 
% Statistics : Number of formulae       :  141 (5169 expanded)
%              Number of leaves         :   13 (1807 expanded)
%              Depth                    :   29
%              Number of atoms          :  785 (62356 expanded)
%              Number of equality atoms :   95 (7441 expanded)
%              Maximal formula depth    :   14 (   7 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f3925,plain,(
    $false ),
    inference(subsumption_resolution,[],[f3924,f3837])).

fof(f3837,plain,(
    ~ r1_orders_2(sK0,sK1,sK3) ),
    inference(subsumption_resolution,[],[f3824,f3833])).

fof(f3833,plain,(
    r2_lattice3(sK0,sK2,sK1) ),
    inference(superposition,[],[f3605,f3821])).

fof(f3821,plain,(
    sK1 = k1_yellow_0(sK0,sK2) ),
    inference(duplicate_literal_removal,[],[f3814])).

fof(f3814,plain,
    ( sK1 = k1_yellow_0(sK0,sK2)
    | sK1 = k1_yellow_0(sK0,sK2) ),
    inference(superposition,[],[f3668,f3615])).

fof(f3615,plain,
    ( sK1 = sK11(sK0,sK2)
    | sK1 = k1_yellow_0(sK0,sK2) ),
    inference(subsumption_resolution,[],[f3614,f3093])).

fof(f3093,plain,
    ( r2_lattice3(sK0,sK2,sK1)
    | sK1 = k1_yellow_0(sK0,sK2) ),
    inference(cnf_transformation,[],[f3065])).

fof(f3065,plain,
    ( ( ( ~ r1_orders_2(sK0,sK1,sK3)
        & r2_lattice3(sK0,sK2,sK3)
        & m1_subset_1(sK3,u1_struct_0(sK0)) )
      | ~ r2_lattice3(sK0,sK2,sK1)
      | sK1 != k1_yellow_0(sK0,sK2) )
    & ( ( ! [X4] :
            ( r1_orders_2(sK0,sK1,X4)
            | ~ r2_lattice3(sK0,sK2,X4)
            | ~ m1_subset_1(X4,u1_struct_0(sK0)) )
        & r2_lattice3(sK0,sK2,sK1) )
      | sK1 = k1_yellow_0(sK0,sK2) )
    & m1_subset_1(sK1,u1_struct_0(sK0))
    & l1_orders_2(sK0)
    & v3_lattice3(sK0)
    & v5_orders_2(sK0)
    & ~ v2_struct_0(sK0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3])],[f3060,f3064,f3063,f3062,f3061])).

fof(f3061,plain,
    ( ? [X0] :
        ( ? [X1] :
            ( ? [X2] :
                ( ( ? [X3] :
                      ( ~ r1_orders_2(X0,X1,X3)
                      & r2_lattice3(X0,X2,X3)
                      & m1_subset_1(X3,u1_struct_0(X0)) )
                  | ~ r2_lattice3(X0,X2,X1)
                  | k1_yellow_0(X0,X2) != X1 )
                & ( ( ! [X4] :
                        ( r1_orders_2(X0,X1,X4)
                        | ~ r2_lattice3(X0,X2,X4)
                        | ~ m1_subset_1(X4,u1_struct_0(X0)) )
                    & r2_lattice3(X0,X2,X1) )
                  | k1_yellow_0(X0,X2) = X1 ) )
            & m1_subset_1(X1,u1_struct_0(X0)) )
        & l1_orders_2(X0)
        & v3_lattice3(X0)
        & v5_orders_2(X0)
        & ~ v2_struct_0(X0) )
   => ( ? [X1] :
          ( ? [X2] :
              ( ( ? [X3] :
                    ( ~ r1_orders_2(sK0,X1,X3)
                    & r2_lattice3(sK0,X2,X3)
                    & m1_subset_1(X3,u1_struct_0(sK0)) )
                | ~ r2_lattice3(sK0,X2,X1)
                | k1_yellow_0(sK0,X2) != X1 )
              & ( ( ! [X4] :
                      ( r1_orders_2(sK0,X1,X4)
                      | ~ r2_lattice3(sK0,X2,X4)
                      | ~ m1_subset_1(X4,u1_struct_0(sK0)) )
                  & r2_lattice3(sK0,X2,X1) )
                | k1_yellow_0(sK0,X2) = X1 ) )
          & m1_subset_1(X1,u1_struct_0(sK0)) )
      & l1_orders_2(sK0)
      & v3_lattice3(sK0)
      & v5_orders_2(sK0)
      & ~ v2_struct_0(sK0) ) ),
    introduced(choice_axiom,[])).

fof(f3062,plain,
    ( ? [X1] :
        ( ? [X2] :
            ( ( ? [X3] :
                  ( ~ r1_orders_2(sK0,X1,X3)
                  & r2_lattice3(sK0,X2,X3)
                  & m1_subset_1(X3,u1_struct_0(sK0)) )
              | ~ r2_lattice3(sK0,X2,X1)
              | k1_yellow_0(sK0,X2) != X1 )
            & ( ( ! [X4] :
                    ( r1_orders_2(sK0,X1,X4)
                    | ~ r2_lattice3(sK0,X2,X4)
                    | ~ m1_subset_1(X4,u1_struct_0(sK0)) )
                & r2_lattice3(sK0,X2,X1) )
              | k1_yellow_0(sK0,X2) = X1 ) )
        & m1_subset_1(X1,u1_struct_0(sK0)) )
   => ( ? [X2] :
          ( ( ? [X3] :
                ( ~ r1_orders_2(sK0,sK1,X3)
                & r2_lattice3(sK0,X2,X3)
                & m1_subset_1(X3,u1_struct_0(sK0)) )
            | ~ r2_lattice3(sK0,X2,sK1)
            | k1_yellow_0(sK0,X2) != sK1 )
          & ( ( ! [X4] :
                  ( r1_orders_2(sK0,sK1,X4)
                  | ~ r2_lattice3(sK0,X2,X4)
                  | ~ m1_subset_1(X4,u1_struct_0(sK0)) )
              & r2_lattice3(sK0,X2,sK1) )
            | k1_yellow_0(sK0,X2) = sK1 ) )
      & m1_subset_1(sK1,u1_struct_0(sK0)) ) ),
    introduced(choice_axiom,[])).

fof(f3063,plain,
    ( ? [X2] :
        ( ( ? [X3] :
              ( ~ r1_orders_2(sK0,sK1,X3)
              & r2_lattice3(sK0,X2,X3)
              & m1_subset_1(X3,u1_struct_0(sK0)) )
          | ~ r2_lattice3(sK0,X2,sK1)
          | k1_yellow_0(sK0,X2) != sK1 )
        & ( ( ! [X4] :
                ( r1_orders_2(sK0,sK1,X4)
                | ~ r2_lattice3(sK0,X2,X4)
                | ~ m1_subset_1(X4,u1_struct_0(sK0)) )
            & r2_lattice3(sK0,X2,sK1) )
          | k1_yellow_0(sK0,X2) = sK1 ) )
   => ( ( ? [X3] :
            ( ~ r1_orders_2(sK0,sK1,X3)
            & r2_lattice3(sK0,sK2,X3)
            & m1_subset_1(X3,u1_struct_0(sK0)) )
        | ~ r2_lattice3(sK0,sK2,sK1)
        | sK1 != k1_yellow_0(sK0,sK2) )
      & ( ( ! [X4] :
              ( r1_orders_2(sK0,sK1,X4)
              | ~ r2_lattice3(sK0,sK2,X4)
              | ~ m1_subset_1(X4,u1_struct_0(sK0)) )
          & r2_lattice3(sK0,sK2,sK1) )
        | sK1 = k1_yellow_0(sK0,sK2) ) ) ),
    introduced(choice_axiom,[])).

fof(f3064,plain,
    ( ? [X3] :
        ( ~ r1_orders_2(sK0,sK1,X3)
        & r2_lattice3(sK0,sK2,X3)
        & m1_subset_1(X3,u1_struct_0(sK0)) )
   => ( ~ r1_orders_2(sK0,sK1,sK3)
      & r2_lattice3(sK0,sK2,sK3)
      & m1_subset_1(sK3,u1_struct_0(sK0)) ) ),
    introduced(choice_axiom,[])).

fof(f3060,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ( ? [X3] :
                    ( ~ r1_orders_2(X0,X1,X3)
                    & r2_lattice3(X0,X2,X3)
                    & m1_subset_1(X3,u1_struct_0(X0)) )
                | ~ r2_lattice3(X0,X2,X1)
                | k1_yellow_0(X0,X2) != X1 )
              & ( ( ! [X4] :
                      ( r1_orders_2(X0,X1,X4)
                      | ~ r2_lattice3(X0,X2,X4)
                      | ~ m1_subset_1(X4,u1_struct_0(X0)) )
                  & r2_lattice3(X0,X2,X1) )
                | k1_yellow_0(X0,X2) = X1 ) )
          & m1_subset_1(X1,u1_struct_0(X0)) )
      & l1_orders_2(X0)
      & v3_lattice3(X0)
      & v5_orders_2(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(rectify,[],[f3059])).

fof(f3059,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ( ? [X3] :
                    ( ~ r1_orders_2(X0,X1,X3)
                    & r2_lattice3(X0,X2,X3)
                    & m1_subset_1(X3,u1_struct_0(X0)) )
                | ~ r2_lattice3(X0,X2,X1)
                | k1_yellow_0(X0,X2) != X1 )
              & ( ( ! [X3] :
                      ( r1_orders_2(X0,X1,X3)
                      | ~ r2_lattice3(X0,X2,X3)
                      | ~ m1_subset_1(X3,u1_struct_0(X0)) )
                  & r2_lattice3(X0,X2,X1) )
                | k1_yellow_0(X0,X2) = X1 ) )
          & m1_subset_1(X1,u1_struct_0(X0)) )
      & l1_orders_2(X0)
      & v3_lattice3(X0)
      & v5_orders_2(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(flattening,[],[f3058])).

fof(f3058,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ( ? [X3] :
                    ( ~ r1_orders_2(X0,X1,X3)
                    & r2_lattice3(X0,X2,X3)
                    & m1_subset_1(X3,u1_struct_0(X0)) )
                | ~ r2_lattice3(X0,X2,X1)
                | k1_yellow_0(X0,X2) != X1 )
              & ( ( ! [X3] :
                      ( r1_orders_2(X0,X1,X3)
                      | ~ r2_lattice3(X0,X2,X3)
                      | ~ m1_subset_1(X3,u1_struct_0(X0)) )
                  & r2_lattice3(X0,X2,X1) )
                | k1_yellow_0(X0,X2) = X1 ) )
          & m1_subset_1(X1,u1_struct_0(X0)) )
      & l1_orders_2(X0)
      & v3_lattice3(X0)
      & v5_orders_2(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(nnf_transformation,[],[f3029])).

fof(f3029,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( k1_yellow_0(X0,X2) = X1
            <~> ( ! [X3] :
                    ( r1_orders_2(X0,X1,X3)
                    | ~ r2_lattice3(X0,X2,X3)
                    | ~ m1_subset_1(X3,u1_struct_0(X0)) )
                & r2_lattice3(X0,X2,X1) ) )
          & m1_subset_1(X1,u1_struct_0(X0)) )
      & l1_orders_2(X0)
      & v3_lattice3(X0)
      & v5_orders_2(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(flattening,[],[f3028])).

fof(f3028,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( k1_yellow_0(X0,X2) = X1
            <~> ( ! [X3] :
                    ( r1_orders_2(X0,X1,X3)
                    | ~ r2_lattice3(X0,X2,X3)
                    | ~ m1_subset_1(X3,u1_struct_0(X0)) )
                & r2_lattice3(X0,X2,X1) ) )
          & m1_subset_1(X1,u1_struct_0(X0)) )
      & l1_orders_2(X0)
      & v3_lattice3(X0)
      & v5_orders_2(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f3009])).

fof(f3009,negated_conjecture,(
    ~ ! [X0] :
        ( ( l1_orders_2(X0)
          & v3_lattice3(X0)
          & v5_orders_2(X0)
          & ~ v2_struct_0(X0) )
       => ! [X1] :
            ( m1_subset_1(X1,u1_struct_0(X0))
           => ! [X2] :
                ( k1_yellow_0(X0,X2) = X1
              <=> ( ! [X3] :
                      ( m1_subset_1(X3,u1_struct_0(X0))
                     => ( r2_lattice3(X0,X2,X3)
                       => r1_orders_2(X0,X1,X3) ) )
                  & r2_lattice3(X0,X2,X1) ) ) ) ) ),
    inference(negated_conjecture,[],[f3008])).

fof(f3008,conjecture,(
    ! [X0] :
      ( ( l1_orders_2(X0)
        & v3_lattice3(X0)
        & v5_orders_2(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,u1_struct_0(X0))
         => ! [X2] :
              ( k1_yellow_0(X0,X2) = X1
            <=> ( ! [X3] :
                    ( m1_subset_1(X3,u1_struct_0(X0))
                   => ( r2_lattice3(X0,X2,X3)
                     => r1_orders_2(X0,X1,X3) ) )
                & r2_lattice3(X0,X2,X1) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t32_yellow_0)).

fof(f3614,plain,
    ( sK1 = sK11(sK0,sK2)
    | ~ r2_lattice3(sK0,sK2,sK1)
    | sK1 = k1_yellow_0(sK0,sK2) ),
    inference(subsumption_resolution,[],[f3606,f3092])).

fof(f3092,plain,(
    m1_subset_1(sK1,u1_struct_0(sK0)) ),
    inference(cnf_transformation,[],[f3065])).

fof(f3606,plain,
    ( ~ m1_subset_1(sK1,u1_struct_0(sK0))
    | sK1 = sK11(sK0,sK2)
    | ~ r2_lattice3(sK0,sK2,sK1)
    | sK1 = k1_yellow_0(sK0,sK2) ),
    inference(resolution,[],[f3488,f3260])).

fof(f3260,plain,
    ( r1_orders_2(sK0,sK1,sK11(sK0,sK2))
    | sK1 = k1_yellow_0(sK0,sK2) ),
    inference(subsumption_resolution,[],[f3259,f3091])).

fof(f3091,plain,(
    l1_orders_2(sK0) ),
    inference(cnf_transformation,[],[f3065])).

fof(f3259,plain,
    ( r1_orders_2(sK0,sK1,sK11(sK0,sK2))
    | sK1 = k1_yellow_0(sK0,sK2)
    | ~ l1_orders_2(sK0) ),
    inference(subsumption_resolution,[],[f3258,f3090])).

fof(f3090,plain,(
    v3_lattice3(sK0) ),
    inference(cnf_transformation,[],[f3065])).

fof(f3258,plain,
    ( r1_orders_2(sK0,sK1,sK11(sK0,sK2))
    | sK1 = k1_yellow_0(sK0,sK2)
    | ~ v3_lattice3(sK0)
    | ~ l1_orders_2(sK0) ),
    inference(resolution,[],[f3177,f3143])).

fof(f3143,plain,(
    ! [X4,X0] :
      ( m1_subset_1(sK11(X0,X4),u1_struct_0(X0))
      | ~ v3_lattice3(X0)
      | ~ l1_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f3087])).

fof(f3087,plain,(
    ! [X0] :
      ( ( ( v3_lattice3(X0)
          | ! [X2] :
              ( ( ~ r1_orders_2(X0,X2,sK10(X0,X2))
                & r2_lattice3(X0,sK9(X0),sK10(X0,X2))
                & m1_subset_1(sK10(X0,X2),u1_struct_0(X0)) )
              | ~ r2_lattice3(X0,sK9(X0),X2)
              | ~ m1_subset_1(X2,u1_struct_0(X0)) ) )
        & ( ! [X4] :
              ( ! [X6] :
                  ( r1_orders_2(X0,sK11(X0,X4),X6)
                  | ~ r2_lattice3(X0,X4,X6)
                  | ~ m1_subset_1(X6,u1_struct_0(X0)) )
              & r2_lattice3(X0,X4,sK11(X0,X4))
              & m1_subset_1(sK11(X0,X4),u1_struct_0(X0)) )
          | ~ v3_lattice3(X0) ) )
      | ~ l1_orders_2(X0) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK9,sK10,sK11])],[f3083,f3086,f3085,f3084])).

fof(f3084,plain,(
    ! [X0] :
      ( ? [X1] :
        ! [X2] :
          ( ? [X3] :
              ( ~ r1_orders_2(X0,X2,X3)
              & r2_lattice3(X0,X1,X3)
              & m1_subset_1(X3,u1_struct_0(X0)) )
          | ~ r2_lattice3(X0,X1,X2)
          | ~ m1_subset_1(X2,u1_struct_0(X0)) )
     => ! [X2] :
          ( ? [X3] :
              ( ~ r1_orders_2(X0,X2,X3)
              & r2_lattice3(X0,sK9(X0),X3)
              & m1_subset_1(X3,u1_struct_0(X0)) )
          | ~ r2_lattice3(X0,sK9(X0),X2)
          | ~ m1_subset_1(X2,u1_struct_0(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f3085,plain,(
    ! [X2,X0] :
      ( ? [X3] :
          ( ~ r1_orders_2(X0,X2,X3)
          & r2_lattice3(X0,sK9(X0),X3)
          & m1_subset_1(X3,u1_struct_0(X0)) )
     => ( ~ r1_orders_2(X0,X2,sK10(X0,X2))
        & r2_lattice3(X0,sK9(X0),sK10(X0,X2))
        & m1_subset_1(sK10(X0,X2),u1_struct_0(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f3086,plain,(
    ! [X4,X0] :
      ( ? [X5] :
          ( ! [X6] :
              ( r1_orders_2(X0,X5,X6)
              | ~ r2_lattice3(X0,X4,X6)
              | ~ m1_subset_1(X6,u1_struct_0(X0)) )
          & r2_lattice3(X0,X4,X5)
          & m1_subset_1(X5,u1_struct_0(X0)) )
     => ( ! [X6] :
            ( r1_orders_2(X0,sK11(X0,X4),X6)
            | ~ r2_lattice3(X0,X4,X6)
            | ~ m1_subset_1(X6,u1_struct_0(X0)) )
        & r2_lattice3(X0,X4,sK11(X0,X4))
        & m1_subset_1(sK11(X0,X4),u1_struct_0(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f3083,plain,(
    ! [X0] :
      ( ( ( v3_lattice3(X0)
          | ? [X1] :
            ! [X2] :
              ( ? [X3] :
                  ( ~ r1_orders_2(X0,X2,X3)
                  & r2_lattice3(X0,X1,X3)
                  & m1_subset_1(X3,u1_struct_0(X0)) )
              | ~ r2_lattice3(X0,X1,X2)
              | ~ m1_subset_1(X2,u1_struct_0(X0)) ) )
        & ( ! [X4] :
            ? [X5] :
              ( ! [X6] :
                  ( r1_orders_2(X0,X5,X6)
                  | ~ r2_lattice3(X0,X4,X6)
                  | ~ m1_subset_1(X6,u1_struct_0(X0)) )
              & r2_lattice3(X0,X4,X5)
              & m1_subset_1(X5,u1_struct_0(X0)) )
          | ~ v3_lattice3(X0) ) )
      | ~ l1_orders_2(X0) ) ),
    inference(rectify,[],[f3082])).

fof(f3082,plain,(
    ! [X0] :
      ( ( ( v3_lattice3(X0)
          | ? [X1] :
            ! [X2] :
              ( ? [X3] :
                  ( ~ r1_orders_2(X0,X2,X3)
                  & r2_lattice3(X0,X1,X3)
                  & m1_subset_1(X3,u1_struct_0(X0)) )
              | ~ r2_lattice3(X0,X1,X2)
              | ~ m1_subset_1(X2,u1_struct_0(X0)) ) )
        & ( ! [X1] :
            ? [X2] :
              ( ! [X3] :
                  ( r1_orders_2(X0,X2,X3)
                  | ~ r2_lattice3(X0,X1,X3)
                  | ~ m1_subset_1(X3,u1_struct_0(X0)) )
              & r2_lattice3(X0,X1,X2)
              & m1_subset_1(X2,u1_struct_0(X0)) )
          | ~ v3_lattice3(X0) ) )
      | ~ l1_orders_2(X0) ) ),
    inference(nnf_transformation,[],[f3055])).

fof(f3055,plain,(
    ! [X0] :
      ( ( v3_lattice3(X0)
      <=> ! [X1] :
          ? [X2] :
            ( ! [X3] :
                ( r1_orders_2(X0,X2,X3)
                | ~ r2_lattice3(X0,X1,X3)
                | ~ m1_subset_1(X3,u1_struct_0(X0)) )
            & r2_lattice3(X0,X1,X2)
            & m1_subset_1(X2,u1_struct_0(X0)) ) )
      | ~ l1_orders_2(X0) ) ),
    inference(flattening,[],[f3054])).

fof(f3054,plain,(
    ! [X0] :
      ( ( v3_lattice3(X0)
      <=> ! [X1] :
          ? [X2] :
            ( ! [X3] :
                ( r1_orders_2(X0,X2,X3)
                | ~ r2_lattice3(X0,X1,X3)
                | ~ m1_subset_1(X3,u1_struct_0(X0)) )
            & r2_lattice3(X0,X1,X2)
            & m1_subset_1(X2,u1_struct_0(X0)) ) )
      | ~ l1_orders_2(X0) ) ),
    inference(ennf_transformation,[],[f2812])).

fof(f2812,axiom,(
    ! [X0] :
      ( l1_orders_2(X0)
     => ( v3_lattice3(X0)
      <=> ! [X1] :
          ? [X2] :
            ( ! [X3] :
                ( m1_subset_1(X3,u1_struct_0(X0))
               => ( r2_lattice3(X0,X1,X3)
                 => r1_orders_2(X0,X2,X3) ) )
            & r2_lattice3(X0,X1,X2)
            & m1_subset_1(X2,u1_struct_0(X0)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d12_lattice3)).

fof(f3177,plain,
    ( ~ m1_subset_1(sK11(sK0,sK2),u1_struct_0(sK0))
    | r1_orders_2(sK0,sK1,sK11(sK0,sK2))
    | sK1 = k1_yellow_0(sK0,sK2) ),
    inference(subsumption_resolution,[],[f3176,f3091])).

fof(f3176,plain,
    ( r1_orders_2(sK0,sK1,sK11(sK0,sK2))
    | ~ m1_subset_1(sK11(sK0,sK2),u1_struct_0(sK0))
    | sK1 = k1_yellow_0(sK0,sK2)
    | ~ l1_orders_2(sK0) ),
    inference(subsumption_resolution,[],[f3173,f3090])).

fof(f3173,plain,
    ( r1_orders_2(sK0,sK1,sK11(sK0,sK2))
    | ~ m1_subset_1(sK11(sK0,sK2),u1_struct_0(sK0))
    | sK1 = k1_yellow_0(sK0,sK2)
    | ~ v3_lattice3(sK0)
    | ~ l1_orders_2(sK0) ),
    inference(resolution,[],[f3094,f3144])).

fof(f3144,plain,(
    ! [X4,X0] :
      ( r2_lattice3(X0,X4,sK11(X0,X4))
      | ~ v3_lattice3(X0)
      | ~ l1_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f3087])).

fof(f3094,plain,(
    ! [X4] :
      ( ~ r2_lattice3(sK0,sK2,X4)
      | r1_orders_2(sK0,sK1,X4)
      | ~ m1_subset_1(X4,u1_struct_0(sK0))
      | sK1 = k1_yellow_0(sK0,sK2) ) ),
    inference(cnf_transformation,[],[f3065])).

fof(f3488,plain,(
    ! [X0,X1] :
      ( ~ r1_orders_2(sK0,X0,sK11(sK0,X1))
      | ~ m1_subset_1(X0,u1_struct_0(sK0))
      | sK11(sK0,X1) = X0
      | ~ r2_lattice3(sK0,X1,X0) ) ),
    inference(subsumption_resolution,[],[f3487,f3091])).

fof(f3487,plain,(
    ! [X0,X1] :
      ( ~ r1_orders_2(sK0,X0,sK11(sK0,X1))
      | ~ m1_subset_1(X0,u1_struct_0(sK0))
      | sK11(sK0,X1) = X0
      | ~ r2_lattice3(sK0,X1,X0)
      | ~ l1_orders_2(sK0) ) ),
    inference(subsumption_resolution,[],[f3486,f3090])).

fof(f3486,plain,(
    ! [X0,X1] :
      ( ~ r1_orders_2(sK0,X0,sK11(sK0,X1))
      | ~ m1_subset_1(X0,u1_struct_0(sK0))
      | sK11(sK0,X1) = X0
      | ~ r2_lattice3(sK0,X1,X0)
      | ~ v3_lattice3(sK0)
      | ~ l1_orders_2(sK0) ) ),
    inference(resolution,[],[f3306,f3143])).

fof(f3306,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(sK11(sK0,X1),u1_struct_0(sK0))
      | ~ r1_orders_2(sK0,X0,sK11(sK0,X1))
      | ~ m1_subset_1(X0,u1_struct_0(sK0))
      | sK11(sK0,X1) = X0
      | ~ r2_lattice3(sK0,X1,X0) ) ),
    inference(subsumption_resolution,[],[f3305,f3091])).

fof(f3305,plain,(
    ! [X0,X1] :
      ( ~ r1_orders_2(sK0,X0,sK11(sK0,X1))
      | ~ m1_subset_1(sK11(sK0,X1),u1_struct_0(sK0))
      | ~ m1_subset_1(X0,u1_struct_0(sK0))
      | sK11(sK0,X1) = X0
      | ~ r2_lattice3(sK0,X1,X0)
      | ~ l1_orders_2(sK0) ) ),
    inference(subsumption_resolution,[],[f3302,f3090])).

fof(f3302,plain,(
    ! [X0,X1] :
      ( ~ r1_orders_2(sK0,X0,sK11(sK0,X1))
      | ~ m1_subset_1(sK11(sK0,X1),u1_struct_0(sK0))
      | ~ m1_subset_1(X0,u1_struct_0(sK0))
      | sK11(sK0,X1) = X0
      | ~ r2_lattice3(sK0,X1,X0)
      | ~ v3_lattice3(sK0)
      | ~ l1_orders_2(sK0) ) ),
    inference(duplicate_literal_removal,[],[f3299])).

fof(f3299,plain,(
    ! [X0,X1] :
      ( ~ r1_orders_2(sK0,X0,sK11(sK0,X1))
      | ~ m1_subset_1(sK11(sK0,X1),u1_struct_0(sK0))
      | ~ m1_subset_1(X0,u1_struct_0(sK0))
      | sK11(sK0,X1) = X0
      | ~ r2_lattice3(sK0,X1,X0)
      | ~ m1_subset_1(X0,u1_struct_0(sK0))
      | ~ v3_lattice3(sK0)
      | ~ l1_orders_2(sK0) ) ),
    inference(resolution,[],[f3234,f3145])).

fof(f3145,plain,(
    ! [X6,X4,X0] :
      ( r1_orders_2(X0,sK11(X0,X4),X6)
      | ~ r2_lattice3(X0,X4,X6)
      | ~ m1_subset_1(X6,u1_struct_0(X0))
      | ~ v3_lattice3(X0)
      | ~ l1_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f3087])).

fof(f3234,plain,(
    ! [X0,X1] :
      ( ~ r1_orders_2(sK0,X0,X1)
      | ~ r1_orders_2(sK0,X1,X0)
      | ~ m1_subset_1(X0,u1_struct_0(sK0))
      | ~ m1_subset_1(X1,u1_struct_0(sK0))
      | X0 = X1 ) ),
    inference(subsumption_resolution,[],[f3233,f3091])).

fof(f3233,plain,(
    ! [X0,X1] :
      ( ~ r1_orders_2(sK0,X0,X1)
      | ~ r1_orders_2(sK0,X1,X0)
      | ~ m1_subset_1(X0,u1_struct_0(sK0))
      | ~ m1_subset_1(X1,u1_struct_0(sK0))
      | ~ l1_orders_2(sK0)
      | X0 = X1 ) ),
    inference(resolution,[],[f3098,f3089])).

fof(f3089,plain,(
    v5_orders_2(sK0) ),
    inference(cnf_transformation,[],[f3065])).

fof(f3098,plain,(
    ! [X2,X0,X1] :
      ( ~ v5_orders_2(X0)
      | ~ r1_orders_2(X0,X2,X1)
      | ~ r1_orders_2(X0,X1,X2)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | X1 = X2 ) ),
    inference(cnf_transformation,[],[f3031])).

fof(f3031,plain,(
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
    inference(flattening,[],[f3030])).

fof(f3030,plain,(
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

fof(f3668,plain,(
    ! [X5] : k1_yellow_0(sK0,X5) = sK11(sK0,X5) ),
    inference(subsumption_resolution,[],[f3667,f3453])).

fof(f3453,plain,(
    ! [X5] :
      ( r2_lattice3(sK0,X5,sK5(sK0,sK11(sK0,X5),X5))
      | k1_yellow_0(sK0,X5) = sK11(sK0,X5) ) ),
    inference(subsumption_resolution,[],[f3452,f3091])).

fof(f3452,plain,(
    ! [X5] :
      ( r2_lattice3(sK0,X5,sK5(sK0,sK11(sK0,X5),X5))
      | k1_yellow_0(sK0,X5) = sK11(sK0,X5)
      | ~ l1_orders_2(sK0) ) ),
    inference(subsumption_resolution,[],[f3448,f3090])).

fof(f3448,plain,(
    ! [X5] :
      ( r2_lattice3(sK0,X5,sK5(sK0,sK11(sK0,X5),X5))
      | k1_yellow_0(sK0,X5) = sK11(sK0,X5)
      | ~ v3_lattice3(sK0)
      | ~ l1_orders_2(sK0) ) ),
    inference(resolution,[],[f3326,f3144])).

fof(f3326,plain,(
    ! [X14,X13] :
      ( ~ r2_lattice3(sK0,X13,sK11(sK0,X14))
      | r2_lattice3(sK0,X13,sK5(sK0,sK11(sK0,X14),X13))
      | sK11(sK0,X14) = k1_yellow_0(sK0,X13) ) ),
    inference(subsumption_resolution,[],[f3325,f3091])).

fof(f3325,plain,(
    ! [X14,X13] :
      ( ~ r2_lattice3(sK0,X13,sK11(sK0,X14))
      | r2_lattice3(sK0,X13,sK5(sK0,sK11(sK0,X14),X13))
      | sK11(sK0,X14) = k1_yellow_0(sK0,X13)
      | ~ l1_orders_2(sK0) ) ),
    inference(subsumption_resolution,[],[f3322,f3090])).

fof(f3322,plain,(
    ! [X14,X13] :
      ( ~ r2_lattice3(sK0,X13,sK11(sK0,X14))
      | r2_lattice3(sK0,X13,sK5(sK0,sK11(sK0,X14),X13))
      | sK11(sK0,X14) = k1_yellow_0(sK0,X13)
      | ~ v3_lattice3(sK0)
      | ~ l1_orders_2(sK0) ) ),
    inference(resolution,[],[f3249,f3143])).

fof(f3249,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,u1_struct_0(sK0))
      | ~ r2_lattice3(sK0,X0,X1)
      | r2_lattice3(sK0,X0,sK5(sK0,X1,X0))
      | k1_yellow_0(sK0,X0) = X1 ) ),
    inference(subsumption_resolution,[],[f3248,f3091])).

fof(f3248,plain,(
    ! [X0,X1] :
      ( r2_lattice3(sK0,X0,sK5(sK0,X1,X0))
      | ~ r2_lattice3(sK0,X0,X1)
      | ~ m1_subset_1(X1,u1_struct_0(sK0))
      | ~ l1_orders_2(sK0)
      | k1_yellow_0(sK0,X0) = X1 ) ),
    inference(resolution,[],[f3129,f3089])).

fof(f3129,plain,(
    ! [X2,X0,X1] :
      ( ~ v5_orders_2(X0)
      | r2_lattice3(X0,X2,sK5(X0,X1,X2))
      | ~ r2_lattice3(X0,X2,X1)
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | k1_yellow_0(X0,X2) = X1 ) ),
    inference(cnf_transformation,[],[f3072])).

fof(f3072,plain,(
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
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK5])],[f3047,f3071])).

fof(f3071,plain,(
    ! [X2,X1,X0] :
      ( ? [X3] :
          ( ~ r1_orders_2(X0,X1,X3)
          & r2_lattice3(X0,X2,X3)
          & m1_subset_1(X3,u1_struct_0(X0)) )
     => ( ~ r1_orders_2(X0,X1,sK5(X0,X1,X2))
        & r2_lattice3(X0,X2,sK5(X0,X1,X2))
        & m1_subset_1(sK5(X0,X1,X2),u1_struct_0(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f3047,plain,(
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
    inference(flattening,[],[f3046])).

fof(f3046,plain,(
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
    inference(ennf_transformation,[],[f3017])).

fof(f3017,plain,(
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
    inference(rectify,[],[f3006])).

fof(f3006,axiom,(
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

fof(f3667,plain,(
    ! [X5] :
      ( k1_yellow_0(sK0,X5) = sK11(sK0,X5)
      | ~ r2_lattice3(sK0,X5,sK5(sK0,sK11(sK0,X5),X5)) ) ),
    inference(subsumption_resolution,[],[f3666,f3091])).

fof(f3666,plain,(
    ! [X5] :
      ( k1_yellow_0(sK0,X5) = sK11(sK0,X5)
      | ~ r2_lattice3(sK0,X5,sK5(sK0,sK11(sK0,X5),X5))
      | ~ l1_orders_2(sK0) ) ),
    inference(subsumption_resolution,[],[f3661,f3090])).

fof(f3661,plain,(
    ! [X5] :
      ( k1_yellow_0(sK0,X5) = sK11(sK0,X5)
      | ~ r2_lattice3(sK0,X5,sK5(sK0,sK11(sK0,X5),X5))
      | ~ v3_lattice3(sK0)
      | ~ l1_orders_2(sK0) ) ),
    inference(resolution,[],[f3501,f3144])).

fof(f3501,plain,(
    ! [X0,X1] :
      ( ~ r2_lattice3(sK0,X0,sK11(sK0,X1))
      | k1_yellow_0(sK0,X0) = sK11(sK0,X1)
      | ~ r2_lattice3(sK0,X1,sK5(sK0,sK11(sK0,X1),X0)) ) ),
    inference(subsumption_resolution,[],[f3500,f3091])).

fof(f3500,plain,(
    ! [X0,X1] :
      ( ~ r2_lattice3(sK0,X0,sK11(sK0,X1))
      | k1_yellow_0(sK0,X0) = sK11(sK0,X1)
      | ~ r2_lattice3(sK0,X1,sK5(sK0,sK11(sK0,X1),X0))
      | ~ l1_orders_2(sK0) ) ),
    inference(subsumption_resolution,[],[f3499,f3090])).

fof(f3499,plain,(
    ! [X0,X1] :
      ( ~ r2_lattice3(sK0,X0,sK11(sK0,X1))
      | k1_yellow_0(sK0,X0) = sK11(sK0,X1)
      | ~ r2_lattice3(sK0,X1,sK5(sK0,sK11(sK0,X1),X0))
      | ~ v3_lattice3(sK0)
      | ~ l1_orders_2(sK0) ) ),
    inference(resolution,[],[f3343,f3143])).

fof(f3343,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(sK11(sK0,X1),u1_struct_0(sK0))
      | ~ r2_lattice3(sK0,X0,sK11(sK0,X1))
      | k1_yellow_0(sK0,X0) = sK11(sK0,X1)
      | ~ r2_lattice3(sK0,X1,sK5(sK0,sK11(sK0,X1),X0)) ) ),
    inference(subsumption_resolution,[],[f3342,f3247])).

fof(f3247,plain,(
    ! [X0,X1] :
      ( m1_subset_1(sK5(sK0,X0,X1),u1_struct_0(sK0))
      | ~ r2_lattice3(sK0,X1,X0)
      | ~ m1_subset_1(X0,u1_struct_0(sK0))
      | k1_yellow_0(sK0,X1) = X0 ) ),
    inference(subsumption_resolution,[],[f3246,f3091])).

fof(f3246,plain,(
    ! [X0,X1] :
      ( m1_subset_1(sK5(sK0,X0,X1),u1_struct_0(sK0))
      | ~ r2_lattice3(sK0,X1,X0)
      | ~ m1_subset_1(X0,u1_struct_0(sK0))
      | ~ l1_orders_2(sK0)
      | k1_yellow_0(sK0,X1) = X0 ) ),
    inference(resolution,[],[f3128,f3089])).

fof(f3128,plain,(
    ! [X2,X0,X1] :
      ( ~ v5_orders_2(X0)
      | m1_subset_1(sK5(X0,X1,X2),u1_struct_0(X0))
      | ~ r2_lattice3(X0,X2,X1)
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | k1_yellow_0(X0,X2) = X1 ) ),
    inference(cnf_transformation,[],[f3072])).

fof(f3342,plain,(
    ! [X0,X1] :
      ( ~ r2_lattice3(sK0,X0,sK11(sK0,X1))
      | ~ m1_subset_1(sK11(sK0,X1),u1_struct_0(sK0))
      | k1_yellow_0(sK0,X0) = sK11(sK0,X1)
      | ~ r2_lattice3(sK0,X1,sK5(sK0,sK11(sK0,X1),X0))
      | ~ m1_subset_1(sK5(sK0,sK11(sK0,X1),X0),u1_struct_0(sK0)) ) ),
    inference(subsumption_resolution,[],[f3341,f3091])).

fof(f3341,plain,(
    ! [X0,X1] :
      ( ~ r2_lattice3(sK0,X0,sK11(sK0,X1))
      | ~ m1_subset_1(sK11(sK0,X1),u1_struct_0(sK0))
      | k1_yellow_0(sK0,X0) = sK11(sK0,X1)
      | ~ r2_lattice3(sK0,X1,sK5(sK0,sK11(sK0,X1),X0))
      | ~ m1_subset_1(sK5(sK0,sK11(sK0,X1),X0),u1_struct_0(sK0))
      | ~ l1_orders_2(sK0) ) ),
    inference(subsumption_resolution,[],[f3340,f3090])).

fof(f3340,plain,(
    ! [X0,X1] :
      ( ~ r2_lattice3(sK0,X0,sK11(sK0,X1))
      | ~ m1_subset_1(sK11(sK0,X1),u1_struct_0(sK0))
      | k1_yellow_0(sK0,X0) = sK11(sK0,X1)
      | ~ r2_lattice3(sK0,X1,sK5(sK0,sK11(sK0,X1),X0))
      | ~ m1_subset_1(sK5(sK0,sK11(sK0,X1),X0),u1_struct_0(sK0))
      | ~ v3_lattice3(sK0)
      | ~ l1_orders_2(sK0) ) ),
    inference(resolution,[],[f3251,f3145])).

fof(f3251,plain,(
    ! [X0,X1] :
      ( ~ r1_orders_2(sK0,X0,sK5(sK0,X0,X1))
      | ~ r2_lattice3(sK0,X1,X0)
      | ~ m1_subset_1(X0,u1_struct_0(sK0))
      | k1_yellow_0(sK0,X1) = X0 ) ),
    inference(subsumption_resolution,[],[f3250,f3091])).

fof(f3250,plain,(
    ! [X0,X1] :
      ( ~ r1_orders_2(sK0,X0,sK5(sK0,X0,X1))
      | ~ r2_lattice3(sK0,X1,X0)
      | ~ m1_subset_1(X0,u1_struct_0(sK0))
      | ~ l1_orders_2(sK0)
      | k1_yellow_0(sK0,X1) = X0 ) ),
    inference(resolution,[],[f3130,f3089])).

fof(f3130,plain,(
    ! [X2,X0,X1] :
      ( ~ v5_orders_2(X0)
      | ~ r1_orders_2(X0,X1,sK5(X0,X1,X2))
      | ~ r2_lattice3(X0,X2,X1)
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | k1_yellow_0(X0,X2) = X1 ) ),
    inference(cnf_transformation,[],[f3072])).

fof(f3605,plain,(
    ! [X10] : r2_lattice3(sK0,X10,k1_yellow_0(sK0,X10)) ),
    inference(subsumption_resolution,[],[f3604,f3089])).

fof(f3604,plain,(
    ! [X10] :
      ( r2_lattice3(sK0,X10,k1_yellow_0(sK0,X10))
      | ~ v5_orders_2(sK0) ) ),
    inference(subsumption_resolution,[],[f3595,f3091])).

fof(f3595,plain,(
    ! [X10] :
      ( r2_lattice3(sK0,X10,k1_yellow_0(sK0,X10))
      | ~ l1_orders_2(sK0)
      | ~ v5_orders_2(sK0) ) ),
    inference(resolution,[],[f3589,f3157])).

fof(f3157,plain,(
    ! [X2,X0] :
      ( ~ r1_yellow_0(X0,X2)
      | r2_lattice3(X0,X2,k1_yellow_0(X0,X2))
      | ~ l1_orders_2(X0)
      | ~ v5_orders_2(X0) ) ),
    inference(subsumption_resolution,[],[f3153,f3125])).

fof(f3125,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k1_yellow_0(X0,X1),u1_struct_0(X0))
      | ~ l1_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f3045])).

fof(f3045,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k1_yellow_0(X0,X1),u1_struct_0(X0))
      | ~ l1_orders_2(X0) ) ),
    inference(ennf_transformation,[],[f2976])).

fof(f2976,axiom,(
    ! [X0,X1] :
      ( l1_orders_2(X0)
     => m1_subset_1(k1_yellow_0(X0,X1),u1_struct_0(X0)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k1_yellow_0)).

fof(f3153,plain,(
    ! [X2,X0] :
      ( r2_lattice3(X0,X2,k1_yellow_0(X0,X2))
      | ~ r1_yellow_0(X0,X2)
      | ~ m1_subset_1(k1_yellow_0(X0,X2),u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | ~ v5_orders_2(X0) ) ),
    inference(equality_resolution,[],[f3126])).

fof(f3126,plain,(
    ! [X2,X0,X1] :
      ( r2_lattice3(X0,X2,X1)
      | ~ r1_yellow_0(X0,X2)
      | k1_yellow_0(X0,X2) != X1
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | ~ v5_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f3072])).

fof(f3589,plain,(
    ! [X5] : r1_yellow_0(sK0,X5) ),
    inference(subsumption_resolution,[],[f3588,f3418])).

fof(f3418,plain,(
    ! [X5] :
      ( r2_lattice3(sK0,X5,sK5(sK0,sK11(sK0,X5),X5))
      | r1_yellow_0(sK0,X5) ) ),
    inference(subsumption_resolution,[],[f3417,f3091])).

fof(f3417,plain,(
    ! [X5] :
      ( r2_lattice3(sK0,X5,sK5(sK0,sK11(sK0,X5),X5))
      | r1_yellow_0(sK0,X5)
      | ~ l1_orders_2(sK0) ) ),
    inference(subsumption_resolution,[],[f3413,f3090])).

fof(f3413,plain,(
    ! [X5] :
      ( r2_lattice3(sK0,X5,sK5(sK0,sK11(sK0,X5),X5))
      | r1_yellow_0(sK0,X5)
      | ~ v3_lattice3(sK0)
      | ~ l1_orders_2(sK0) ) ),
    inference(resolution,[],[f3278,f3144])).

fof(f3278,plain,(
    ! [X10,X11] :
      ( ~ r2_lattice3(sK0,X10,sK11(sK0,X11))
      | r2_lattice3(sK0,X10,sK5(sK0,sK11(sK0,X11),X10))
      | r1_yellow_0(sK0,X10) ) ),
    inference(subsumption_resolution,[],[f3277,f3091])).

fof(f3277,plain,(
    ! [X10,X11] :
      ( ~ r2_lattice3(sK0,X10,sK11(sK0,X11))
      | r2_lattice3(sK0,X10,sK5(sK0,sK11(sK0,X11),X10))
      | r1_yellow_0(sK0,X10)
      | ~ l1_orders_2(sK0) ) ),
    inference(subsumption_resolution,[],[f3274,f3090])).

fof(f3274,plain,(
    ! [X10,X11] :
      ( ~ r2_lattice3(sK0,X10,sK11(sK0,X11))
      | r2_lattice3(sK0,X10,sK5(sK0,sK11(sK0,X11),X10))
      | r1_yellow_0(sK0,X10)
      | ~ v3_lattice3(sK0)
      | ~ l1_orders_2(sK0) ) ),
    inference(resolution,[],[f3230,f3143])).

fof(f3230,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,u1_struct_0(sK0))
      | ~ r2_lattice3(sK0,X0,X1)
      | r2_lattice3(sK0,X0,sK5(sK0,X1,X0))
      | r1_yellow_0(sK0,X0) ) ),
    inference(subsumption_resolution,[],[f3229,f3091])).

fof(f3229,plain,(
    ! [X0,X1] :
      ( r2_lattice3(sK0,X0,sK5(sK0,X1,X0))
      | ~ r2_lattice3(sK0,X0,X1)
      | ~ m1_subset_1(X1,u1_struct_0(sK0))
      | ~ l1_orders_2(sK0)
      | r1_yellow_0(sK0,X0) ) ),
    inference(resolution,[],[f3132,f3089])).

fof(f3132,plain,(
    ! [X2,X0,X1] :
      ( ~ v5_orders_2(X0)
      | r2_lattice3(X0,X2,sK5(X0,X1,X2))
      | ~ r2_lattice3(X0,X2,X1)
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | r1_yellow_0(X0,X2) ) ),
    inference(cnf_transformation,[],[f3072])).

fof(f3588,plain,(
    ! [X5] :
      ( r1_yellow_0(sK0,X5)
      | ~ r2_lattice3(sK0,X5,sK5(sK0,sK11(sK0,X5),X5)) ) ),
    inference(subsumption_resolution,[],[f3587,f3091])).

fof(f3587,plain,(
    ! [X5] :
      ( r1_yellow_0(sK0,X5)
      | ~ r2_lattice3(sK0,X5,sK5(sK0,sK11(sK0,X5),X5))
      | ~ l1_orders_2(sK0) ) ),
    inference(subsumption_resolution,[],[f3583,f3090])).

fof(f3583,plain,(
    ! [X5] :
      ( r1_yellow_0(sK0,X5)
      | ~ r2_lattice3(sK0,X5,sK5(sK0,sK11(sK0,X5),X5))
      | ~ v3_lattice3(sK0)
      | ~ l1_orders_2(sK0) ) ),
    inference(resolution,[],[f3471,f3144])).

fof(f3471,plain,(
    ! [X0,X1] :
      ( ~ r2_lattice3(sK0,X0,sK11(sK0,X1))
      | r1_yellow_0(sK0,X0)
      | ~ r2_lattice3(sK0,X1,sK5(sK0,sK11(sK0,X1),X0)) ) ),
    inference(subsumption_resolution,[],[f3470,f3091])).

fof(f3470,plain,(
    ! [X0,X1] :
      ( ~ r2_lattice3(sK0,X0,sK11(sK0,X1))
      | r1_yellow_0(sK0,X0)
      | ~ r2_lattice3(sK0,X1,sK5(sK0,sK11(sK0,X1),X0))
      | ~ l1_orders_2(sK0) ) ),
    inference(subsumption_resolution,[],[f3469,f3090])).

fof(f3469,plain,(
    ! [X0,X1] :
      ( ~ r2_lattice3(sK0,X0,sK11(sK0,X1))
      | r1_yellow_0(sK0,X0)
      | ~ r2_lattice3(sK0,X1,sK5(sK0,sK11(sK0,X1),X0))
      | ~ v3_lattice3(sK0)
      | ~ l1_orders_2(sK0) ) ),
    inference(resolution,[],[f3294,f3143])).

fof(f3294,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(sK11(sK0,X1),u1_struct_0(sK0))
      | ~ r2_lattice3(sK0,X0,sK11(sK0,X1))
      | r1_yellow_0(sK0,X0)
      | ~ r2_lattice3(sK0,X1,sK5(sK0,sK11(sK0,X1),X0)) ) ),
    inference(subsumption_resolution,[],[f3293,f3228])).

fof(f3228,plain,(
    ! [X0,X1] :
      ( m1_subset_1(sK5(sK0,X0,X1),u1_struct_0(sK0))
      | ~ r2_lattice3(sK0,X1,X0)
      | ~ m1_subset_1(X0,u1_struct_0(sK0))
      | r1_yellow_0(sK0,X1) ) ),
    inference(subsumption_resolution,[],[f3227,f3091])).

fof(f3227,plain,(
    ! [X0,X1] :
      ( m1_subset_1(sK5(sK0,X0,X1),u1_struct_0(sK0))
      | ~ r2_lattice3(sK0,X1,X0)
      | ~ m1_subset_1(X0,u1_struct_0(sK0))
      | ~ l1_orders_2(sK0)
      | r1_yellow_0(sK0,X1) ) ),
    inference(resolution,[],[f3131,f3089])).

fof(f3131,plain,(
    ! [X2,X0,X1] :
      ( ~ v5_orders_2(X0)
      | m1_subset_1(sK5(X0,X1,X2),u1_struct_0(X0))
      | ~ r2_lattice3(X0,X2,X1)
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | r1_yellow_0(X0,X2) ) ),
    inference(cnf_transformation,[],[f3072])).

fof(f3293,plain,(
    ! [X0,X1] :
      ( ~ r2_lattice3(sK0,X0,sK11(sK0,X1))
      | ~ m1_subset_1(sK11(sK0,X1),u1_struct_0(sK0))
      | r1_yellow_0(sK0,X0)
      | ~ r2_lattice3(sK0,X1,sK5(sK0,sK11(sK0,X1),X0))
      | ~ m1_subset_1(sK5(sK0,sK11(sK0,X1),X0),u1_struct_0(sK0)) ) ),
    inference(subsumption_resolution,[],[f3292,f3091])).

fof(f3292,plain,(
    ! [X0,X1] :
      ( ~ r2_lattice3(sK0,X0,sK11(sK0,X1))
      | ~ m1_subset_1(sK11(sK0,X1),u1_struct_0(sK0))
      | r1_yellow_0(sK0,X0)
      | ~ r2_lattice3(sK0,X1,sK5(sK0,sK11(sK0,X1),X0))
      | ~ m1_subset_1(sK5(sK0,sK11(sK0,X1),X0),u1_struct_0(sK0))
      | ~ l1_orders_2(sK0) ) ),
    inference(subsumption_resolution,[],[f3291,f3090])).

fof(f3291,plain,(
    ! [X0,X1] :
      ( ~ r2_lattice3(sK0,X0,sK11(sK0,X1))
      | ~ m1_subset_1(sK11(sK0,X1),u1_struct_0(sK0))
      | r1_yellow_0(sK0,X0)
      | ~ r2_lattice3(sK0,X1,sK5(sK0,sK11(sK0,X1),X0))
      | ~ m1_subset_1(sK5(sK0,sK11(sK0,X1),X0),u1_struct_0(sK0))
      | ~ v3_lattice3(sK0)
      | ~ l1_orders_2(sK0) ) ),
    inference(resolution,[],[f3232,f3145])).

fof(f3232,plain,(
    ! [X0,X1] :
      ( ~ r1_orders_2(sK0,X0,sK5(sK0,X0,X1))
      | ~ r2_lattice3(sK0,X1,X0)
      | ~ m1_subset_1(X0,u1_struct_0(sK0))
      | r1_yellow_0(sK0,X1) ) ),
    inference(subsumption_resolution,[],[f3231,f3091])).

fof(f3231,plain,(
    ! [X0,X1] :
      ( ~ r1_orders_2(sK0,X0,sK5(sK0,X0,X1))
      | ~ r2_lattice3(sK0,X1,X0)
      | ~ m1_subset_1(X0,u1_struct_0(sK0))
      | ~ l1_orders_2(sK0)
      | r1_yellow_0(sK0,X1) ) ),
    inference(resolution,[],[f3133,f3089])).

fof(f3133,plain,(
    ! [X2,X0,X1] :
      ( ~ v5_orders_2(X0)
      | ~ r1_orders_2(X0,X1,sK5(X0,X1,X2))
      | ~ r2_lattice3(X0,X2,X1)
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | r1_yellow_0(X0,X2) ) ),
    inference(cnf_transformation,[],[f3072])).

fof(f3824,plain,
    ( ~ r1_orders_2(sK0,sK1,sK3)
    | ~ r2_lattice3(sK0,sK2,sK1) ),
    inference(subsumption_resolution,[],[f3097,f3821])).

fof(f3097,plain,
    ( ~ r1_orders_2(sK0,sK1,sK3)
    | ~ r2_lattice3(sK0,sK2,sK1)
    | sK1 != k1_yellow_0(sK0,sK2) ),
    inference(cnf_transformation,[],[f3065])).

fof(f3924,plain,(
    r1_orders_2(sK0,sK1,sK3) ),
    inference(subsumption_resolution,[],[f3918,f3835])).

fof(f3835,plain,(
    m1_subset_1(sK3,u1_struct_0(sK0)) ),
    inference(subsumption_resolution,[],[f3822,f3833])).

fof(f3822,plain,
    ( ~ r2_lattice3(sK0,sK2,sK1)
    | m1_subset_1(sK3,u1_struct_0(sK0)) ),
    inference(subsumption_resolution,[],[f3095,f3821])).

fof(f3095,plain,
    ( sK1 != k1_yellow_0(sK0,sK2)
    | ~ r2_lattice3(sK0,sK2,sK1)
    | m1_subset_1(sK3,u1_struct_0(sK0)) ),
    inference(cnf_transformation,[],[f3065])).

fof(f3918,plain,
    ( ~ m1_subset_1(sK3,u1_struct_0(sK0))
    | r1_orders_2(sK0,sK1,sK3) ),
    inference(resolution,[],[f3889,f3836])).

fof(f3836,plain,(
    r2_lattice3(sK0,sK2,sK3) ),
    inference(subsumption_resolution,[],[f3823,f3833])).

fof(f3823,plain,
    ( r2_lattice3(sK0,sK2,sK3)
    | ~ r2_lattice3(sK0,sK2,sK1) ),
    inference(subsumption_resolution,[],[f3096,f3821])).

fof(f3096,plain,
    ( r2_lattice3(sK0,sK2,sK3)
    | ~ r2_lattice3(sK0,sK2,sK1)
    | sK1 != k1_yellow_0(sK0,sK2) ),
    inference(cnf_transformation,[],[f3065])).

fof(f3889,plain,(
    ! [X0] :
      ( ~ r2_lattice3(sK0,sK2,X0)
      | ~ m1_subset_1(X0,u1_struct_0(sK0))
      | r1_orders_2(sK0,sK1,X0) ) ),
    inference(superposition,[],[f3603,f3821])).

fof(f3603,plain,(
    ! [X8,X9] :
      ( r1_orders_2(sK0,k1_yellow_0(sK0,X8),X9)
      | ~ m1_subset_1(X9,u1_struct_0(sK0))
      | ~ r2_lattice3(sK0,X8,X9) ) ),
    inference(subsumption_resolution,[],[f3602,f3089])).

fof(f3602,plain,(
    ! [X8,X9] :
      ( ~ r2_lattice3(sK0,X8,X9)
      | ~ m1_subset_1(X9,u1_struct_0(sK0))
      | r1_orders_2(sK0,k1_yellow_0(sK0,X8),X9)
      | ~ v5_orders_2(sK0) ) ),
    inference(subsumption_resolution,[],[f3594,f3091])).

fof(f3594,plain,(
    ! [X8,X9] :
      ( ~ r2_lattice3(sK0,X8,X9)
      | ~ m1_subset_1(X9,u1_struct_0(sK0))
      | r1_orders_2(sK0,k1_yellow_0(sK0,X8),X9)
      | ~ l1_orders_2(sK0)
      | ~ v5_orders_2(sK0) ) ),
    inference(resolution,[],[f3589,f3156])).

fof(f3156,plain,(
    ! [X4,X2,X0] :
      ( ~ r1_yellow_0(X0,X2)
      | ~ r2_lattice3(X0,X2,X4)
      | ~ m1_subset_1(X4,u1_struct_0(X0))
      | r1_orders_2(X0,k1_yellow_0(X0,X2),X4)
      | ~ l1_orders_2(X0)
      | ~ v5_orders_2(X0) ) ),
    inference(subsumption_resolution,[],[f3152,f3125])).

fof(f3152,plain,(
    ! [X4,X2,X0] :
      ( r1_orders_2(X0,k1_yellow_0(X0,X2),X4)
      | ~ r2_lattice3(X0,X2,X4)
      | ~ m1_subset_1(X4,u1_struct_0(X0))
      | ~ r1_yellow_0(X0,X2)
      | ~ m1_subset_1(k1_yellow_0(X0,X2),u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | ~ v5_orders_2(X0) ) ),
    inference(equality_resolution,[],[f3127])).

fof(f3127,plain,(
    ! [X4,X2,X0,X1] :
      ( r1_orders_2(X0,X1,X4)
      | ~ r2_lattice3(X0,X2,X4)
      | ~ m1_subset_1(X4,u1_struct_0(X0))
      | ~ r1_yellow_0(X0,X2)
      | k1_yellow_0(X0,X2) != X1
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | ~ v5_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f3072])).
%------------------------------------------------------------------------------
