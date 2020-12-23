%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT1631+2 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n025.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Wed Dec 16 12:10:27 EST 2020

% Result     : Theorem 1.36s
% Output     : Refutation 1.36s
% Verified   : 
% Statistics : Number of formulae       :   99 (1966 expanded)
%              Number of leaves         :   11 ( 752 expanded)
%              Depth                    :   43
%              Number of atoms          :  704 (24617 expanded)
%              Number of equality atoms :    0 (   0 expanded)
%              Maximal formula depth    :   16 (   8 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f3469,plain,(
    $false ),
    inference(subsumption_resolution,[],[f3467,f3456])).

fof(f3456,plain,(
    r1_waybel_0(sK0,sK1,a_3_0_waybel_0(sK0,sK1,sK2)) ),
    inference(unit_resulting_resolution,[],[f3248,f3249,f3250,f3251,f3439,f3444,f3260])).

fof(f3260,plain,(
    ! [X0,X3,X1] :
      ( r1_waybel_0(X0,X1,a_3_0_waybel_0(X0,X1,X3))
      | ~ m1_subset_1(X3,u1_struct_0(X1))
      | ~ v10_waybel_0(X1,X0)
      | ~ l1_waybel_0(X1,X0)
      | v2_struct_0(X1)
      | ~ l1_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f3225])).

fof(f3225,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ( v10_waybel_0(X1,X0)
              | ( ~ r1_waybel_0(X0,X1,a_3_0_waybel_0(X0,X1,sK6(X0,X1)))
                & m1_subset_1(sK6(X0,X1),u1_struct_0(X1)) ) )
            & ( ! [X3] :
                  ( r1_waybel_0(X0,X1,a_3_0_waybel_0(X0,X1,X3))
                  | ~ m1_subset_1(X3,u1_struct_0(X1)) )
              | ~ v10_waybel_0(X1,X0) ) )
          | ~ l1_waybel_0(X1,X0)
          | v2_struct_0(X1) )
      | ~ l1_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK6])],[f3223,f3224])).

fof(f3224,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ~ r1_waybel_0(X0,X1,a_3_0_waybel_0(X0,X1,X2))
          & m1_subset_1(X2,u1_struct_0(X1)) )
     => ( ~ r1_waybel_0(X0,X1,a_3_0_waybel_0(X0,X1,sK6(X0,X1)))
        & m1_subset_1(sK6(X0,X1),u1_struct_0(X1)) ) ) ),
    introduced(choice_axiom,[])).

fof(f3223,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ( v10_waybel_0(X1,X0)
              | ? [X2] :
                  ( ~ r1_waybel_0(X0,X1,a_3_0_waybel_0(X0,X1,X2))
                  & m1_subset_1(X2,u1_struct_0(X1)) ) )
            & ( ! [X3] :
                  ( r1_waybel_0(X0,X1,a_3_0_waybel_0(X0,X1,X3))
                  | ~ m1_subset_1(X3,u1_struct_0(X1)) )
              | ~ v10_waybel_0(X1,X0) ) )
          | ~ l1_waybel_0(X1,X0)
          | v2_struct_0(X1) )
      | ~ l1_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(rectify,[],[f3222])).

fof(f3222,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ( v10_waybel_0(X1,X0)
              | ? [X2] :
                  ( ~ r1_waybel_0(X0,X1,a_3_0_waybel_0(X0,X1,X2))
                  & m1_subset_1(X2,u1_struct_0(X1)) ) )
            & ( ! [X2] :
                  ( r1_waybel_0(X0,X1,a_3_0_waybel_0(X0,X1,X2))
                  | ~ m1_subset_1(X2,u1_struct_0(X1)) )
              | ~ v10_waybel_0(X1,X0) ) )
          | ~ l1_waybel_0(X1,X0)
          | v2_struct_0(X1) )
      | ~ l1_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(nnf_transformation,[],[f3195])).

fof(f3195,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( v10_waybel_0(X1,X0)
          <=> ! [X2] :
                ( r1_waybel_0(X0,X1,a_3_0_waybel_0(X0,X1,X2))
                | ~ m1_subset_1(X2,u1_struct_0(X1)) ) )
          | ~ l1_waybel_0(X1,X0)
          | v2_struct_0(X1) )
      | ~ l1_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f3194])).

fof(f3194,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( v10_waybel_0(X1,X0)
          <=> ! [X2] :
                ( r1_waybel_0(X0,X1,a_3_0_waybel_0(X0,X1,X2))
                | ~ m1_subset_1(X2,u1_struct_0(X1)) ) )
          | ~ l1_waybel_0(X1,X0)
          | v2_struct_0(X1) )
      | ~ l1_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f3156])).

fof(f3156,axiom,(
    ! [X0] :
      ( ( l1_orders_2(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( ( l1_waybel_0(X1,X0)
            & ~ v2_struct_0(X1) )
         => ( v10_waybel_0(X1,X0)
          <=> ! [X2] :
                ( m1_subset_1(X2,u1_struct_0(X1))
               => r1_waybel_0(X0,X1,a_3_0_waybel_0(X0,X1,X2)) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d13_waybel_0)).

fof(f3444,plain,(
    m1_subset_1(sK2,u1_struct_0(sK1)) ),
    inference(unit_resulting_resolution,[],[f3439,f3254])).

fof(f3254,plain,
    ( m1_subset_1(sK2,u1_struct_0(sK1))
    | ~ v10_waybel_0(sK1,sK0) ),
    inference(cnf_transformation,[],[f3219])).

fof(f3219,plain,
    ( ( ( ! [X3] :
            ( ( ~ r1_orders_2(sK0,k2_waybel_0(sK0,sK1,sK2),k2_waybel_0(sK0,sK1,sK3(X3)))
              & r1_orders_2(sK1,X3,sK3(X3))
              & m1_subset_1(sK3(X3),u1_struct_0(sK1)) )
            | ~ m1_subset_1(X3,u1_struct_0(sK1)) )
        & m1_subset_1(sK2,u1_struct_0(sK1)) )
      | ~ v10_waybel_0(sK1,sK0) )
    & ( ! [X5] :
          ( ( ! [X7] :
                ( r1_orders_2(sK0,k2_waybel_0(sK0,sK1,X5),k2_waybel_0(sK0,sK1,X7))
                | ~ r1_orders_2(sK1,sK4(X5),X7)
                | ~ m1_subset_1(X7,u1_struct_0(sK1)) )
            & m1_subset_1(sK4(X5),u1_struct_0(sK1)) )
          | ~ m1_subset_1(X5,u1_struct_0(sK1)) )
      | v10_waybel_0(sK1,sK0) )
    & l1_waybel_0(sK1,sK0)
    & ~ v2_struct_0(sK1)
    & l1_orders_2(sK0)
    & ~ v2_struct_0(sK0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3,sK4])],[f3213,f3218,f3217,f3216,f3215,f3214])).

fof(f3214,plain,
    ( ? [X0] :
        ( ? [X1] :
            ( ( ? [X2] :
                  ( ! [X3] :
                      ( ? [X4] :
                          ( ~ r1_orders_2(X0,k2_waybel_0(X0,X1,X2),k2_waybel_0(X0,X1,X4))
                          & r1_orders_2(X1,X3,X4)
                          & m1_subset_1(X4,u1_struct_0(X1)) )
                      | ~ m1_subset_1(X3,u1_struct_0(X1)) )
                  & m1_subset_1(X2,u1_struct_0(X1)) )
              | ~ v10_waybel_0(X1,X0) )
            & ( ! [X5] :
                  ( ? [X6] :
                      ( ! [X7] :
                          ( r1_orders_2(X0,k2_waybel_0(X0,X1,X5),k2_waybel_0(X0,X1,X7))
                          | ~ r1_orders_2(X1,X6,X7)
                          | ~ m1_subset_1(X7,u1_struct_0(X1)) )
                      & m1_subset_1(X6,u1_struct_0(X1)) )
                  | ~ m1_subset_1(X5,u1_struct_0(X1)) )
              | v10_waybel_0(X1,X0) )
            & l1_waybel_0(X1,X0)
            & ~ v2_struct_0(X1) )
        & l1_orders_2(X0)
        & ~ v2_struct_0(X0) )
   => ( ? [X1] :
          ( ( ? [X2] :
                ( ! [X3] :
                    ( ? [X4] :
                        ( ~ r1_orders_2(sK0,k2_waybel_0(sK0,X1,X2),k2_waybel_0(sK0,X1,X4))
                        & r1_orders_2(X1,X3,X4)
                        & m1_subset_1(X4,u1_struct_0(X1)) )
                    | ~ m1_subset_1(X3,u1_struct_0(X1)) )
                & m1_subset_1(X2,u1_struct_0(X1)) )
            | ~ v10_waybel_0(X1,sK0) )
          & ( ! [X5] :
                ( ? [X6] :
                    ( ! [X7] :
                        ( r1_orders_2(sK0,k2_waybel_0(sK0,X1,X5),k2_waybel_0(sK0,X1,X7))
                        | ~ r1_orders_2(X1,X6,X7)
                        | ~ m1_subset_1(X7,u1_struct_0(X1)) )
                    & m1_subset_1(X6,u1_struct_0(X1)) )
                | ~ m1_subset_1(X5,u1_struct_0(X1)) )
            | v10_waybel_0(X1,sK0) )
          & l1_waybel_0(X1,sK0)
          & ~ v2_struct_0(X1) )
      & l1_orders_2(sK0)
      & ~ v2_struct_0(sK0) ) ),
    introduced(choice_axiom,[])).

fof(f3215,plain,
    ( ? [X1] :
        ( ( ? [X2] :
              ( ! [X3] :
                  ( ? [X4] :
                      ( ~ r1_orders_2(sK0,k2_waybel_0(sK0,X1,X2),k2_waybel_0(sK0,X1,X4))
                      & r1_orders_2(X1,X3,X4)
                      & m1_subset_1(X4,u1_struct_0(X1)) )
                  | ~ m1_subset_1(X3,u1_struct_0(X1)) )
              & m1_subset_1(X2,u1_struct_0(X1)) )
          | ~ v10_waybel_0(X1,sK0) )
        & ( ! [X5] :
              ( ? [X6] :
                  ( ! [X7] :
                      ( r1_orders_2(sK0,k2_waybel_0(sK0,X1,X5),k2_waybel_0(sK0,X1,X7))
                      | ~ r1_orders_2(X1,X6,X7)
                      | ~ m1_subset_1(X7,u1_struct_0(X1)) )
                  & m1_subset_1(X6,u1_struct_0(X1)) )
              | ~ m1_subset_1(X5,u1_struct_0(X1)) )
          | v10_waybel_0(X1,sK0) )
        & l1_waybel_0(X1,sK0)
        & ~ v2_struct_0(X1) )
   => ( ( ? [X2] :
            ( ! [X3] :
                ( ? [X4] :
                    ( ~ r1_orders_2(sK0,k2_waybel_0(sK0,sK1,X2),k2_waybel_0(sK0,sK1,X4))
                    & r1_orders_2(sK1,X3,X4)
                    & m1_subset_1(X4,u1_struct_0(sK1)) )
                | ~ m1_subset_1(X3,u1_struct_0(sK1)) )
            & m1_subset_1(X2,u1_struct_0(sK1)) )
        | ~ v10_waybel_0(sK1,sK0) )
      & ( ! [X5] :
            ( ? [X6] :
                ( ! [X7] :
                    ( r1_orders_2(sK0,k2_waybel_0(sK0,sK1,X5),k2_waybel_0(sK0,sK1,X7))
                    | ~ r1_orders_2(sK1,X6,X7)
                    | ~ m1_subset_1(X7,u1_struct_0(sK1)) )
                & m1_subset_1(X6,u1_struct_0(sK1)) )
            | ~ m1_subset_1(X5,u1_struct_0(sK1)) )
        | v10_waybel_0(sK1,sK0) )
      & l1_waybel_0(sK1,sK0)
      & ~ v2_struct_0(sK1) ) ),
    introduced(choice_axiom,[])).

fof(f3216,plain,
    ( ? [X2] :
        ( ! [X3] :
            ( ? [X4] :
                ( ~ r1_orders_2(sK0,k2_waybel_0(sK0,sK1,X2),k2_waybel_0(sK0,sK1,X4))
                & r1_orders_2(sK1,X3,X4)
                & m1_subset_1(X4,u1_struct_0(sK1)) )
            | ~ m1_subset_1(X3,u1_struct_0(sK1)) )
        & m1_subset_1(X2,u1_struct_0(sK1)) )
   => ( ! [X3] :
          ( ? [X4] :
              ( ~ r1_orders_2(sK0,k2_waybel_0(sK0,sK1,sK2),k2_waybel_0(sK0,sK1,X4))
              & r1_orders_2(sK1,X3,X4)
              & m1_subset_1(X4,u1_struct_0(sK1)) )
          | ~ m1_subset_1(X3,u1_struct_0(sK1)) )
      & m1_subset_1(sK2,u1_struct_0(sK1)) ) ),
    introduced(choice_axiom,[])).

fof(f3217,plain,(
    ! [X3] :
      ( ? [X4] :
          ( ~ r1_orders_2(sK0,k2_waybel_0(sK0,sK1,sK2),k2_waybel_0(sK0,sK1,X4))
          & r1_orders_2(sK1,X3,X4)
          & m1_subset_1(X4,u1_struct_0(sK1)) )
     => ( ~ r1_orders_2(sK0,k2_waybel_0(sK0,sK1,sK2),k2_waybel_0(sK0,sK1,sK3(X3)))
        & r1_orders_2(sK1,X3,sK3(X3))
        & m1_subset_1(sK3(X3),u1_struct_0(sK1)) ) ) ),
    introduced(choice_axiom,[])).

fof(f3218,plain,(
    ! [X5] :
      ( ? [X6] :
          ( ! [X7] :
              ( r1_orders_2(sK0,k2_waybel_0(sK0,sK1,X5),k2_waybel_0(sK0,sK1,X7))
              | ~ r1_orders_2(sK1,X6,X7)
              | ~ m1_subset_1(X7,u1_struct_0(sK1)) )
          & m1_subset_1(X6,u1_struct_0(sK1)) )
     => ( ! [X7] :
            ( r1_orders_2(sK0,k2_waybel_0(sK0,sK1,X5),k2_waybel_0(sK0,sK1,X7))
            | ~ r1_orders_2(sK1,sK4(X5),X7)
            | ~ m1_subset_1(X7,u1_struct_0(sK1)) )
        & m1_subset_1(sK4(X5),u1_struct_0(sK1)) ) ) ),
    introduced(choice_axiom,[])).

fof(f3213,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ( ? [X2] :
                ( ! [X3] :
                    ( ? [X4] :
                        ( ~ r1_orders_2(X0,k2_waybel_0(X0,X1,X2),k2_waybel_0(X0,X1,X4))
                        & r1_orders_2(X1,X3,X4)
                        & m1_subset_1(X4,u1_struct_0(X1)) )
                    | ~ m1_subset_1(X3,u1_struct_0(X1)) )
                & m1_subset_1(X2,u1_struct_0(X1)) )
            | ~ v10_waybel_0(X1,X0) )
          & ( ! [X5] :
                ( ? [X6] :
                    ( ! [X7] :
                        ( r1_orders_2(X0,k2_waybel_0(X0,X1,X5),k2_waybel_0(X0,X1,X7))
                        | ~ r1_orders_2(X1,X6,X7)
                        | ~ m1_subset_1(X7,u1_struct_0(X1)) )
                    & m1_subset_1(X6,u1_struct_0(X1)) )
                | ~ m1_subset_1(X5,u1_struct_0(X1)) )
            | v10_waybel_0(X1,X0) )
          & l1_waybel_0(X1,X0)
          & ~ v2_struct_0(X1) )
      & l1_orders_2(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(rectify,[],[f3212])).

fof(f3212,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ( ? [X2] :
                ( ! [X3] :
                    ( ? [X4] :
                        ( ~ r1_orders_2(X0,k2_waybel_0(X0,X1,X2),k2_waybel_0(X0,X1,X4))
                        & r1_orders_2(X1,X3,X4)
                        & m1_subset_1(X4,u1_struct_0(X1)) )
                    | ~ m1_subset_1(X3,u1_struct_0(X1)) )
                & m1_subset_1(X2,u1_struct_0(X1)) )
            | ~ v10_waybel_0(X1,X0) )
          & ( ! [X2] :
                ( ? [X3] :
                    ( ! [X4] :
                        ( r1_orders_2(X0,k2_waybel_0(X0,X1,X2),k2_waybel_0(X0,X1,X4))
                        | ~ r1_orders_2(X1,X3,X4)
                        | ~ m1_subset_1(X4,u1_struct_0(X1)) )
                    & m1_subset_1(X3,u1_struct_0(X1)) )
                | ~ m1_subset_1(X2,u1_struct_0(X1)) )
            | v10_waybel_0(X1,X0) )
          & l1_waybel_0(X1,X0)
          & ~ v2_struct_0(X1) )
      & l1_orders_2(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(flattening,[],[f3211])).

fof(f3211,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ( ? [X2] :
                ( ! [X3] :
                    ( ? [X4] :
                        ( ~ r1_orders_2(X0,k2_waybel_0(X0,X1,X2),k2_waybel_0(X0,X1,X4))
                        & r1_orders_2(X1,X3,X4)
                        & m1_subset_1(X4,u1_struct_0(X1)) )
                    | ~ m1_subset_1(X3,u1_struct_0(X1)) )
                & m1_subset_1(X2,u1_struct_0(X1)) )
            | ~ v10_waybel_0(X1,X0) )
          & ( ! [X2] :
                ( ? [X3] :
                    ( ! [X4] :
                        ( r1_orders_2(X0,k2_waybel_0(X0,X1,X2),k2_waybel_0(X0,X1,X4))
                        | ~ r1_orders_2(X1,X3,X4)
                        | ~ m1_subset_1(X4,u1_struct_0(X1)) )
                    & m1_subset_1(X3,u1_struct_0(X1)) )
                | ~ m1_subset_1(X2,u1_struct_0(X1)) )
            | v10_waybel_0(X1,X0) )
          & l1_waybel_0(X1,X0)
          & ~ v2_struct_0(X1) )
      & l1_orders_2(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(nnf_transformation,[],[f3191])).

fof(f3191,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ( v10_waybel_0(X1,X0)
          <~> ! [X2] :
                ( ? [X3] :
                    ( ! [X4] :
                        ( r1_orders_2(X0,k2_waybel_0(X0,X1,X2),k2_waybel_0(X0,X1,X4))
                        | ~ r1_orders_2(X1,X3,X4)
                        | ~ m1_subset_1(X4,u1_struct_0(X1)) )
                    & m1_subset_1(X3,u1_struct_0(X1)) )
                | ~ m1_subset_1(X2,u1_struct_0(X1)) ) )
          & l1_waybel_0(X1,X0)
          & ~ v2_struct_0(X1) )
      & l1_orders_2(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(flattening,[],[f3190])).

fof(f3190,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ( v10_waybel_0(X1,X0)
          <~> ! [X2] :
                ( ? [X3] :
                    ( ! [X4] :
                        ( r1_orders_2(X0,k2_waybel_0(X0,X1,X2),k2_waybel_0(X0,X1,X4))
                        | ~ r1_orders_2(X1,X3,X4)
                        | ~ m1_subset_1(X4,u1_struct_0(X1)) )
                    & m1_subset_1(X3,u1_struct_0(X1)) )
                | ~ m1_subset_1(X2,u1_struct_0(X1)) ) )
          & l1_waybel_0(X1,X0)
          & ~ v2_struct_0(X1) )
      & l1_orders_2(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f3174])).

fof(f3174,negated_conjecture,(
    ~ ! [X0] :
        ( ( l1_orders_2(X0)
          & ~ v2_struct_0(X0) )
       => ! [X1] :
            ( ( l1_waybel_0(X1,X0)
              & ~ v2_struct_0(X1) )
           => ( v10_waybel_0(X1,X0)
            <=> ! [X2] :
                  ( m1_subset_1(X2,u1_struct_0(X1))
                 => ? [X3] :
                      ( ! [X4] :
                          ( m1_subset_1(X4,u1_struct_0(X1))
                         => ( r1_orders_2(X1,X3,X4)
                           => r1_orders_2(X0,k2_waybel_0(X0,X1,X2),k2_waybel_0(X0,X1,X4)) ) )
                      & m1_subset_1(X3,u1_struct_0(X1)) ) ) ) ) ) ),
    inference(negated_conjecture,[],[f3173])).

fof(f3173,conjecture,(
    ! [X0] :
      ( ( l1_orders_2(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( ( l1_waybel_0(X1,X0)
            & ~ v2_struct_0(X1) )
         => ( v10_waybel_0(X1,X0)
          <=> ! [X2] :
                ( m1_subset_1(X2,u1_struct_0(X1))
               => ? [X3] :
                    ( ! [X4] :
                        ( m1_subset_1(X4,u1_struct_0(X1))
                       => ( r1_orders_2(X1,X3,X4)
                         => r1_orders_2(X0,k2_waybel_0(X0,X1,X2),k2_waybel_0(X0,X1,X4)) ) )
                    & m1_subset_1(X3,u1_struct_0(X1)) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t11_waybel_0)).

fof(f3439,plain,(
    v10_waybel_0(sK1,sK0) ),
    inference(subsumption_resolution,[],[f3438,f3248])).

fof(f3438,plain,
    ( v10_waybel_0(sK1,sK0)
    | v2_struct_0(sK0) ),
    inference(subsumption_resolution,[],[f3437,f3249])).

fof(f3437,plain,
    ( v10_waybel_0(sK1,sK0)
    | ~ l1_orders_2(sK0)
    | v2_struct_0(sK0) ),
    inference(subsumption_resolution,[],[f3436,f3250])).

fof(f3436,plain,
    ( v10_waybel_0(sK1,sK0)
    | v2_struct_0(sK1)
    | ~ l1_orders_2(sK0)
    | v2_struct_0(sK0) ),
    inference(subsumption_resolution,[],[f3435,f3251])).

fof(f3435,plain,
    ( v10_waybel_0(sK1,sK0)
    | ~ l1_waybel_0(sK1,sK0)
    | v2_struct_0(sK1)
    | ~ l1_orders_2(sK0)
    | v2_struct_0(sK0) ),
    inference(duplicate_literal_removal,[],[f3434])).

fof(f3434,plain,
    ( v10_waybel_0(sK1,sK0)
    | v10_waybel_0(sK1,sK0)
    | ~ l1_waybel_0(sK1,sK0)
    | v2_struct_0(sK1)
    | ~ l1_orders_2(sK0)
    | v2_struct_0(sK0) ),
    inference(resolution,[],[f3414,f3261])).

fof(f3261,plain,(
    ! [X0,X1] :
      ( m1_subset_1(sK6(X0,X1),u1_struct_0(X1))
      | v10_waybel_0(X1,X0)
      | ~ l1_waybel_0(X1,X0)
      | v2_struct_0(X1)
      | ~ l1_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f3225])).

fof(f3414,plain,
    ( ~ m1_subset_1(sK6(sK0,sK1),u1_struct_0(sK1))
    | v10_waybel_0(sK1,sK0) ),
    inference(subsumption_resolution,[],[f3413,f3248])).

fof(f3413,plain,
    ( v10_waybel_0(sK1,sK0)
    | ~ m1_subset_1(sK6(sK0,sK1),u1_struct_0(sK1))
    | v2_struct_0(sK0) ),
    inference(subsumption_resolution,[],[f3412,f3249])).

fof(f3412,plain,
    ( v10_waybel_0(sK1,sK0)
    | ~ m1_subset_1(sK6(sK0,sK1),u1_struct_0(sK1))
    | ~ l1_orders_2(sK0)
    | v2_struct_0(sK0) ),
    inference(subsumption_resolution,[],[f3411,f3250])).

fof(f3411,plain,
    ( v10_waybel_0(sK1,sK0)
    | ~ m1_subset_1(sK6(sK0,sK1),u1_struct_0(sK1))
    | v2_struct_0(sK1)
    | ~ l1_orders_2(sK0)
    | v2_struct_0(sK0) ),
    inference(subsumption_resolution,[],[f3410,f3251])).

fof(f3410,plain,
    ( v10_waybel_0(sK1,sK0)
    | ~ m1_subset_1(sK6(sK0,sK1),u1_struct_0(sK1))
    | ~ l1_waybel_0(sK1,sK0)
    | v2_struct_0(sK1)
    | ~ l1_orders_2(sK0)
    | v2_struct_0(sK0) ),
    inference(duplicate_literal_removal,[],[f3407])).

fof(f3407,plain,
    ( v10_waybel_0(sK1,sK0)
    | ~ m1_subset_1(sK6(sK0,sK1),u1_struct_0(sK1))
    | v10_waybel_0(sK1,sK0)
    | ~ l1_waybel_0(sK1,sK0)
    | v2_struct_0(sK1)
    | ~ l1_orders_2(sK0)
    | v2_struct_0(sK0) ),
    inference(resolution,[],[f3379,f3262])).

fof(f3262,plain,(
    ! [X0,X1] :
      ( ~ r1_waybel_0(X0,X1,a_3_0_waybel_0(X0,X1,sK6(X0,X1)))
      | v10_waybel_0(X1,X0)
      | ~ l1_waybel_0(X1,X0)
      | v2_struct_0(X1)
      | ~ l1_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f3225])).

fof(f3379,plain,(
    ! [X0] :
      ( r1_waybel_0(sK0,sK1,a_3_0_waybel_0(sK0,sK1,X0))
      | v10_waybel_0(sK1,sK0)
      | ~ m1_subset_1(X0,u1_struct_0(sK1)) ) ),
    inference(subsumption_resolution,[],[f3378,f3252])).

fof(f3252,plain,(
    ! [X5] :
      ( m1_subset_1(sK4(X5),u1_struct_0(sK1))
      | ~ m1_subset_1(X5,u1_struct_0(sK1))
      | v10_waybel_0(sK1,sK0) ) ),
    inference(cnf_transformation,[],[f3219])).

fof(f3378,plain,(
    ! [X0] :
      ( ~ m1_subset_1(X0,u1_struct_0(sK1))
      | v10_waybel_0(sK1,sK0)
      | r1_waybel_0(sK0,sK1,a_3_0_waybel_0(sK0,sK1,X0))
      | ~ m1_subset_1(sK4(X0),u1_struct_0(sK1)) ) ),
    inference(subsumption_resolution,[],[f3377,f3248])).

fof(f3377,plain,(
    ! [X0] :
      ( ~ m1_subset_1(X0,u1_struct_0(sK1))
      | v10_waybel_0(sK1,sK0)
      | r1_waybel_0(sK0,sK1,a_3_0_waybel_0(sK0,sK1,X0))
      | ~ m1_subset_1(sK4(X0),u1_struct_0(sK1))
      | v2_struct_0(sK0) ) ),
    inference(subsumption_resolution,[],[f3376,f3249])).

fof(f3376,plain,(
    ! [X0] :
      ( ~ m1_subset_1(X0,u1_struct_0(sK1))
      | v10_waybel_0(sK1,sK0)
      | r1_waybel_0(sK0,sK1,a_3_0_waybel_0(sK0,sK1,X0))
      | ~ m1_subset_1(sK4(X0),u1_struct_0(sK1))
      | ~ l1_orders_2(sK0)
      | v2_struct_0(sK0) ) ),
    inference(subsumption_resolution,[],[f3375,f3250])).

fof(f3375,plain,(
    ! [X0] :
      ( ~ m1_subset_1(X0,u1_struct_0(sK1))
      | v10_waybel_0(sK1,sK0)
      | r1_waybel_0(sK0,sK1,a_3_0_waybel_0(sK0,sK1,X0))
      | ~ m1_subset_1(sK4(X0),u1_struct_0(sK1))
      | v2_struct_0(sK1)
      | ~ l1_orders_2(sK0)
      | v2_struct_0(sK0) ) ),
    inference(subsumption_resolution,[],[f3374,f3251])).

fof(f3374,plain,(
    ! [X0] :
      ( ~ m1_subset_1(X0,u1_struct_0(sK1))
      | v10_waybel_0(sK1,sK0)
      | r1_waybel_0(sK0,sK1,a_3_0_waybel_0(sK0,sK1,X0))
      | ~ m1_subset_1(sK4(X0),u1_struct_0(sK1))
      | ~ l1_waybel_0(sK1,sK0)
      | v2_struct_0(sK1)
      | ~ l1_orders_2(sK0)
      | v2_struct_0(sK0) ) ),
    inference(duplicate_literal_removal,[],[f3373])).

fof(f3373,plain,(
    ! [X0] :
      ( ~ m1_subset_1(X0,u1_struct_0(sK1))
      | v10_waybel_0(sK1,sK0)
      | r1_waybel_0(sK0,sK1,a_3_0_waybel_0(sK0,sK1,X0))
      | r1_waybel_0(sK0,sK1,a_3_0_waybel_0(sK0,sK1,X0))
      | ~ m1_subset_1(sK4(X0),u1_struct_0(sK1))
      | ~ m1_subset_1(X0,u1_struct_0(sK1))
      | ~ l1_waybel_0(sK1,sK0)
      | v2_struct_0(sK1)
      | ~ l1_orders_2(sK0)
      | v2_struct_0(sK0) ) ),
    inference(resolution,[],[f3350,f3283])).

fof(f3283,plain,(
    ! [X2,X0,X3,X1] :
      ( m1_subset_1(sK14(X0,X1,X2,X3),u1_struct_0(X1))
      | r1_waybel_0(X0,X1,a_3_0_waybel_0(X0,X1,X2))
      | ~ m1_subset_1(X3,u1_struct_0(X1))
      | ~ m1_subset_1(X2,u1_struct_0(X1))
      | ~ l1_waybel_0(X1,X0)
      | v2_struct_0(X1)
      | ~ l1_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f3247])).

fof(f3247,plain,(
    ! [X0,X1,X2] :
      ( ( ( r1_waybel_0(X0,X1,a_3_0_waybel_0(X0,X1,X2))
          | ! [X3] :
              ( ( ~ r1_orders_2(X0,k2_waybel_0(X0,X1,X2),k2_waybel_0(X0,X1,sK14(X0,X1,X2,X3)))
                & r1_orders_2(X1,X3,sK14(X0,X1,X2,X3))
                & m1_subset_1(sK14(X0,X1,X2,X3),u1_struct_0(X1)) )
              | ~ m1_subset_1(X3,u1_struct_0(X1)) ) )
        & ( ( ! [X6] :
                ( r1_orders_2(X0,k2_waybel_0(X0,X1,X2),k2_waybel_0(X0,X1,X6))
                | ~ r1_orders_2(X1,sK15(X0,X1,X2),X6)
                | ~ m1_subset_1(X6,u1_struct_0(X1)) )
            & m1_subset_1(sK15(X0,X1,X2),u1_struct_0(X1)) )
          | ~ r1_waybel_0(X0,X1,a_3_0_waybel_0(X0,X1,X2)) ) )
      | ~ m1_subset_1(X2,u1_struct_0(X1))
      | ~ l1_waybel_0(X1,X0)
      | v2_struct_0(X1)
      | ~ l1_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK14,sK15])],[f3244,f3246,f3245])).

fof(f3245,plain,(
    ! [X3,X2,X1,X0] :
      ( ? [X4] :
          ( ~ r1_orders_2(X0,k2_waybel_0(X0,X1,X2),k2_waybel_0(X0,X1,X4))
          & r1_orders_2(X1,X3,X4)
          & m1_subset_1(X4,u1_struct_0(X1)) )
     => ( ~ r1_orders_2(X0,k2_waybel_0(X0,X1,X2),k2_waybel_0(X0,X1,sK14(X0,X1,X2,X3)))
        & r1_orders_2(X1,X3,sK14(X0,X1,X2,X3))
        & m1_subset_1(sK14(X0,X1,X2,X3),u1_struct_0(X1)) ) ) ),
    introduced(choice_axiom,[])).

fof(f3246,plain,(
    ! [X2,X1,X0] :
      ( ? [X5] :
          ( ! [X6] :
              ( r1_orders_2(X0,k2_waybel_0(X0,X1,X2),k2_waybel_0(X0,X1,X6))
              | ~ r1_orders_2(X1,X5,X6)
              | ~ m1_subset_1(X6,u1_struct_0(X1)) )
          & m1_subset_1(X5,u1_struct_0(X1)) )
     => ( ! [X6] :
            ( r1_orders_2(X0,k2_waybel_0(X0,X1,X2),k2_waybel_0(X0,X1,X6))
            | ~ r1_orders_2(X1,sK15(X0,X1,X2),X6)
            | ~ m1_subset_1(X6,u1_struct_0(X1)) )
        & m1_subset_1(sK15(X0,X1,X2),u1_struct_0(X1)) ) ) ),
    introduced(choice_axiom,[])).

fof(f3244,plain,(
    ! [X0,X1,X2] :
      ( ( ( r1_waybel_0(X0,X1,a_3_0_waybel_0(X0,X1,X2))
          | ! [X3] :
              ( ? [X4] :
                  ( ~ r1_orders_2(X0,k2_waybel_0(X0,X1,X2),k2_waybel_0(X0,X1,X4))
                  & r1_orders_2(X1,X3,X4)
                  & m1_subset_1(X4,u1_struct_0(X1)) )
              | ~ m1_subset_1(X3,u1_struct_0(X1)) ) )
        & ( ? [X5] :
              ( ! [X6] :
                  ( r1_orders_2(X0,k2_waybel_0(X0,X1,X2),k2_waybel_0(X0,X1,X6))
                  | ~ r1_orders_2(X1,X5,X6)
                  | ~ m1_subset_1(X6,u1_struct_0(X1)) )
              & m1_subset_1(X5,u1_struct_0(X1)) )
          | ~ r1_waybel_0(X0,X1,a_3_0_waybel_0(X0,X1,X2)) ) )
      | ~ m1_subset_1(X2,u1_struct_0(X1))
      | ~ l1_waybel_0(X1,X0)
      | v2_struct_0(X1)
      | ~ l1_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(rectify,[],[f3243])).

fof(f3243,plain,(
    ! [X0,X1,X2] :
      ( ( ( r1_waybel_0(X0,X1,a_3_0_waybel_0(X0,X1,X2))
          | ! [X3] :
              ( ? [X4] :
                  ( ~ r1_orders_2(X0,k2_waybel_0(X0,X1,X2),k2_waybel_0(X0,X1,X4))
                  & r1_orders_2(X1,X3,X4)
                  & m1_subset_1(X4,u1_struct_0(X1)) )
              | ~ m1_subset_1(X3,u1_struct_0(X1)) ) )
        & ( ? [X3] :
              ( ! [X4] :
                  ( r1_orders_2(X0,k2_waybel_0(X0,X1,X2),k2_waybel_0(X0,X1,X4))
                  | ~ r1_orders_2(X1,X3,X4)
                  | ~ m1_subset_1(X4,u1_struct_0(X1)) )
              & m1_subset_1(X3,u1_struct_0(X1)) )
          | ~ r1_waybel_0(X0,X1,a_3_0_waybel_0(X0,X1,X2)) ) )
      | ~ m1_subset_1(X2,u1_struct_0(X1))
      | ~ l1_waybel_0(X1,X0)
      | v2_struct_0(X1)
      | ~ l1_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(nnf_transformation,[],[f3210])).

fof(f3210,plain,(
    ! [X0,X1,X2] :
      ( ( r1_waybel_0(X0,X1,a_3_0_waybel_0(X0,X1,X2))
      <=> ? [X3] :
            ( ! [X4] :
                ( r1_orders_2(X0,k2_waybel_0(X0,X1,X2),k2_waybel_0(X0,X1,X4))
                | ~ r1_orders_2(X1,X3,X4)
                | ~ m1_subset_1(X4,u1_struct_0(X1)) )
            & m1_subset_1(X3,u1_struct_0(X1)) ) )
      | ~ m1_subset_1(X2,u1_struct_0(X1))
      | ~ l1_waybel_0(X1,X0)
      | v2_struct_0(X1)
      | ~ l1_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f3209])).

fof(f3209,plain,(
    ! [X0,X1,X2] :
      ( ( r1_waybel_0(X0,X1,a_3_0_waybel_0(X0,X1,X2))
      <=> ? [X3] :
            ( ! [X4] :
                ( r1_orders_2(X0,k2_waybel_0(X0,X1,X2),k2_waybel_0(X0,X1,X4))
                | ~ r1_orders_2(X1,X3,X4)
                | ~ m1_subset_1(X4,u1_struct_0(X1)) )
            & m1_subset_1(X3,u1_struct_0(X1)) ) )
      | ~ m1_subset_1(X2,u1_struct_0(X1))
      | ~ l1_waybel_0(X1,X0)
      | v2_struct_0(X1)
      | ~ l1_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f3169])).

fof(f3169,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,u1_struct_0(X1))
        & l1_waybel_0(X1,X0)
        & ~ v2_struct_0(X1)
        & l1_orders_2(X0)
        & ~ v2_struct_0(X0) )
     => ( r1_waybel_0(X0,X1,a_3_0_waybel_0(X0,X1,X2))
      <=> ? [X3] :
            ( ! [X4] :
                ( m1_subset_1(X4,u1_struct_0(X1))
               => ( r1_orders_2(X1,X3,X4)
                 => r1_orders_2(X0,k2_waybel_0(X0,X1,X2),k2_waybel_0(X0,X1,X4)) ) )
            & m1_subset_1(X3,u1_struct_0(X1)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',s1_waybel_0__e1_34_1__waybel_0)).

fof(f3350,plain,(
    ! [X0] :
      ( ~ m1_subset_1(sK14(sK0,sK1,X0,sK4(X0)),u1_struct_0(sK1))
      | ~ m1_subset_1(X0,u1_struct_0(sK1))
      | v10_waybel_0(sK1,sK0)
      | r1_waybel_0(sK0,sK1,a_3_0_waybel_0(sK0,sK1,X0)) ) ),
    inference(subsumption_resolution,[],[f3349,f3252])).

fof(f3349,plain,(
    ! [X0] :
      ( ~ m1_subset_1(sK14(sK0,sK1,X0,sK4(X0)),u1_struct_0(sK1))
      | ~ m1_subset_1(X0,u1_struct_0(sK1))
      | v10_waybel_0(sK1,sK0)
      | r1_waybel_0(sK0,sK1,a_3_0_waybel_0(sK0,sK1,X0))
      | ~ m1_subset_1(sK4(X0),u1_struct_0(sK1)) ) ),
    inference(subsumption_resolution,[],[f3348,f3248])).

fof(f3348,plain,(
    ! [X0] :
      ( ~ m1_subset_1(sK14(sK0,sK1,X0,sK4(X0)),u1_struct_0(sK1))
      | ~ m1_subset_1(X0,u1_struct_0(sK1))
      | v10_waybel_0(sK1,sK0)
      | r1_waybel_0(sK0,sK1,a_3_0_waybel_0(sK0,sK1,X0))
      | ~ m1_subset_1(sK4(X0),u1_struct_0(sK1))
      | v2_struct_0(sK0) ) ),
    inference(subsumption_resolution,[],[f3347,f3249])).

fof(f3347,plain,(
    ! [X0] :
      ( ~ m1_subset_1(sK14(sK0,sK1,X0,sK4(X0)),u1_struct_0(sK1))
      | ~ m1_subset_1(X0,u1_struct_0(sK1))
      | v10_waybel_0(sK1,sK0)
      | r1_waybel_0(sK0,sK1,a_3_0_waybel_0(sK0,sK1,X0))
      | ~ m1_subset_1(sK4(X0),u1_struct_0(sK1))
      | ~ l1_orders_2(sK0)
      | v2_struct_0(sK0) ) ),
    inference(subsumption_resolution,[],[f3346,f3250])).

fof(f3346,plain,(
    ! [X0] :
      ( ~ m1_subset_1(sK14(sK0,sK1,X0,sK4(X0)),u1_struct_0(sK1))
      | ~ m1_subset_1(X0,u1_struct_0(sK1))
      | v10_waybel_0(sK1,sK0)
      | r1_waybel_0(sK0,sK1,a_3_0_waybel_0(sK0,sK1,X0))
      | ~ m1_subset_1(sK4(X0),u1_struct_0(sK1))
      | v2_struct_0(sK1)
      | ~ l1_orders_2(sK0)
      | v2_struct_0(sK0) ) ),
    inference(subsumption_resolution,[],[f3345,f3251])).

fof(f3345,plain,(
    ! [X0] :
      ( ~ m1_subset_1(sK14(sK0,sK1,X0,sK4(X0)),u1_struct_0(sK1))
      | ~ m1_subset_1(X0,u1_struct_0(sK1))
      | v10_waybel_0(sK1,sK0)
      | r1_waybel_0(sK0,sK1,a_3_0_waybel_0(sK0,sK1,X0))
      | ~ m1_subset_1(sK4(X0),u1_struct_0(sK1))
      | ~ l1_waybel_0(sK1,sK0)
      | v2_struct_0(sK1)
      | ~ l1_orders_2(sK0)
      | v2_struct_0(sK0) ) ),
    inference(duplicate_literal_removal,[],[f3344])).

fof(f3344,plain,(
    ! [X0] :
      ( ~ m1_subset_1(sK14(sK0,sK1,X0,sK4(X0)),u1_struct_0(sK1))
      | ~ m1_subset_1(X0,u1_struct_0(sK1))
      | v10_waybel_0(sK1,sK0)
      | r1_waybel_0(sK0,sK1,a_3_0_waybel_0(sK0,sK1,X0))
      | ~ m1_subset_1(sK4(X0),u1_struct_0(sK1))
      | r1_waybel_0(sK0,sK1,a_3_0_waybel_0(sK0,sK1,X0))
      | ~ m1_subset_1(sK4(X0),u1_struct_0(sK1))
      | ~ m1_subset_1(X0,u1_struct_0(sK1))
      | ~ l1_waybel_0(sK1,sK0)
      | v2_struct_0(sK1)
      | ~ l1_orders_2(sK0)
      | v2_struct_0(sK0) ) ),
    inference(resolution,[],[f3315,f3284])).

fof(f3284,plain,(
    ! [X2,X0,X3,X1] :
      ( r1_orders_2(X1,X3,sK14(X0,X1,X2,X3))
      | r1_waybel_0(X0,X1,a_3_0_waybel_0(X0,X1,X2))
      | ~ m1_subset_1(X3,u1_struct_0(X1))
      | ~ m1_subset_1(X2,u1_struct_0(X1))
      | ~ l1_waybel_0(X1,X0)
      | v2_struct_0(X1)
      | ~ l1_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f3247])).

fof(f3315,plain,(
    ! [X4,X3] :
      ( ~ r1_orders_2(sK1,sK4(X3),sK14(sK0,sK1,X3,X4))
      | ~ m1_subset_1(sK14(sK0,sK1,X3,X4),u1_struct_0(sK1))
      | ~ m1_subset_1(X3,u1_struct_0(sK1))
      | v10_waybel_0(sK1,sK0)
      | r1_waybel_0(sK0,sK1,a_3_0_waybel_0(sK0,sK1,X3))
      | ~ m1_subset_1(X4,u1_struct_0(sK1)) ) ),
    inference(subsumption_resolution,[],[f3314,f3248])).

fof(f3314,plain,(
    ! [X4,X3] :
      ( ~ r1_orders_2(sK1,sK4(X3),sK14(sK0,sK1,X3,X4))
      | ~ m1_subset_1(sK14(sK0,sK1,X3,X4),u1_struct_0(sK1))
      | ~ m1_subset_1(X3,u1_struct_0(sK1))
      | v10_waybel_0(sK1,sK0)
      | r1_waybel_0(sK0,sK1,a_3_0_waybel_0(sK0,sK1,X3))
      | ~ m1_subset_1(X4,u1_struct_0(sK1))
      | v2_struct_0(sK0) ) ),
    inference(subsumption_resolution,[],[f3313,f3249])).

% (18974)Refutation not found, incomplete strategy% (18974)------------------------------
% (18974)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% (18974)Termination reason: Refutation not found, incomplete strategy

% (18974)Memory used [KB]: 9338
% (18974)Time elapsed: 0.010 s
% (18974)------------------------------
% (18974)------------------------------
fof(f3313,plain,(
    ! [X4,X3] :
      ( ~ r1_orders_2(sK1,sK4(X3),sK14(sK0,sK1,X3,X4))
      | ~ m1_subset_1(sK14(sK0,sK1,X3,X4),u1_struct_0(sK1))
      | ~ m1_subset_1(X3,u1_struct_0(sK1))
      | v10_waybel_0(sK1,sK0)
      | r1_waybel_0(sK0,sK1,a_3_0_waybel_0(sK0,sK1,X3))
      | ~ m1_subset_1(X4,u1_struct_0(sK1))
      | ~ l1_orders_2(sK0)
      | v2_struct_0(sK0) ) ),
    inference(subsumption_resolution,[],[f3312,f3250])).

fof(f3312,plain,(
    ! [X4,X3] :
      ( ~ r1_orders_2(sK1,sK4(X3),sK14(sK0,sK1,X3,X4))
      | ~ m1_subset_1(sK14(sK0,sK1,X3,X4),u1_struct_0(sK1))
      | ~ m1_subset_1(X3,u1_struct_0(sK1))
      | v10_waybel_0(sK1,sK0)
      | r1_waybel_0(sK0,sK1,a_3_0_waybel_0(sK0,sK1,X3))
      | ~ m1_subset_1(X4,u1_struct_0(sK1))
      | v2_struct_0(sK1)
      | ~ l1_orders_2(sK0)
      | v2_struct_0(sK0) ) ),
    inference(subsumption_resolution,[],[f3306,f3251])).

fof(f3306,plain,(
    ! [X4,X3] :
      ( ~ r1_orders_2(sK1,sK4(X3),sK14(sK0,sK1,X3,X4))
      | ~ m1_subset_1(sK14(sK0,sK1,X3,X4),u1_struct_0(sK1))
      | ~ m1_subset_1(X3,u1_struct_0(sK1))
      | v10_waybel_0(sK1,sK0)
      | r1_waybel_0(sK0,sK1,a_3_0_waybel_0(sK0,sK1,X3))
      | ~ m1_subset_1(X4,u1_struct_0(sK1))
      | ~ l1_waybel_0(sK1,sK0)
      | v2_struct_0(sK1)
      | ~ l1_orders_2(sK0)
      | v2_struct_0(sK0) ) ),
    inference(duplicate_literal_removal,[],[f3303])).

fof(f3303,plain,(
    ! [X4,X3] :
      ( ~ r1_orders_2(sK1,sK4(X3),sK14(sK0,sK1,X3,X4))
      | ~ m1_subset_1(sK14(sK0,sK1,X3,X4),u1_struct_0(sK1))
      | ~ m1_subset_1(X3,u1_struct_0(sK1))
      | v10_waybel_0(sK1,sK0)
      | r1_waybel_0(sK0,sK1,a_3_0_waybel_0(sK0,sK1,X3))
      | ~ m1_subset_1(X4,u1_struct_0(sK1))
      | ~ m1_subset_1(X3,u1_struct_0(sK1))
      | ~ l1_waybel_0(sK1,sK0)
      | v2_struct_0(sK1)
      | ~ l1_orders_2(sK0)
      | v2_struct_0(sK0) ) ),
    inference(resolution,[],[f3253,f3285])).

fof(f3285,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ r1_orders_2(X0,k2_waybel_0(X0,X1,X2),k2_waybel_0(X0,X1,sK14(X0,X1,X2,X3)))
      | r1_waybel_0(X0,X1,a_3_0_waybel_0(X0,X1,X2))
      | ~ m1_subset_1(X3,u1_struct_0(X1))
      | ~ m1_subset_1(X2,u1_struct_0(X1))
      | ~ l1_waybel_0(X1,X0)
      | v2_struct_0(X1)
      | ~ l1_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f3247])).

fof(f3253,plain,(
    ! [X7,X5] :
      ( r1_orders_2(sK0,k2_waybel_0(sK0,sK1,X5),k2_waybel_0(sK0,sK1,X7))
      | ~ r1_orders_2(sK1,sK4(X5),X7)
      | ~ m1_subset_1(X7,u1_struct_0(sK1))
      | ~ m1_subset_1(X5,u1_struct_0(sK1))
      | v10_waybel_0(sK1,sK0) ) ),
    inference(cnf_transformation,[],[f3219])).

fof(f3251,plain,(
    l1_waybel_0(sK1,sK0) ),
    inference(cnf_transformation,[],[f3219])).

fof(f3250,plain,(
    ~ v2_struct_0(sK1) ),
    inference(cnf_transformation,[],[f3219])).

fof(f3249,plain,(
    l1_orders_2(sK0) ),
    inference(cnf_transformation,[],[f3219])).

fof(f3248,plain,(
    ~ v2_struct_0(sK0) ),
    inference(cnf_transformation,[],[f3219])).

fof(f3467,plain,(
    ~ r1_waybel_0(sK0,sK1,a_3_0_waybel_0(sK0,sK1,sK2)) ),
    inference(unit_resulting_resolution,[],[f3248,f3249,f3250,f3251,f3444,f3448,f3281])).

fof(f3281,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_waybel_0(X0,X1,a_3_0_waybel_0(X0,X1,X2))
      | m1_subset_1(sK15(X0,X1,X2),u1_struct_0(X1))
      | ~ m1_subset_1(X2,u1_struct_0(X1))
      | ~ l1_waybel_0(X1,X0)
      | v2_struct_0(X1)
      | ~ l1_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f3247])).

fof(f3448,plain,(
    ~ m1_subset_1(sK15(sK0,sK1,sK2),u1_struct_0(sK1)) ),
    inference(unit_resulting_resolution,[],[f3439,f3372])).

fof(f3372,plain,
    ( ~ m1_subset_1(sK15(sK0,sK1,sK2),u1_struct_0(sK1))
    | ~ v10_waybel_0(sK1,sK0) ),
    inference(subsumption_resolution,[],[f3371,f3254])).

fof(f3371,plain,
    ( ~ m1_subset_1(sK15(sK0,sK1,sK2),u1_struct_0(sK1))
    | ~ v10_waybel_0(sK1,sK0)
    | ~ m1_subset_1(sK2,u1_struct_0(sK1)) ),
    inference(subsumption_resolution,[],[f3370,f3248])).

fof(f3370,plain,
    ( ~ m1_subset_1(sK15(sK0,sK1,sK2),u1_struct_0(sK1))
    | ~ v10_waybel_0(sK1,sK0)
    | ~ m1_subset_1(sK2,u1_struct_0(sK1))
    | v2_struct_0(sK0) ),
    inference(subsumption_resolution,[],[f3369,f3249])).

fof(f3369,plain,
    ( ~ m1_subset_1(sK15(sK0,sK1,sK2),u1_struct_0(sK1))
    | ~ v10_waybel_0(sK1,sK0)
    | ~ m1_subset_1(sK2,u1_struct_0(sK1))
    | ~ l1_orders_2(sK0)
    | v2_struct_0(sK0) ),
    inference(subsumption_resolution,[],[f3368,f3250])).

fof(f3368,plain,
    ( ~ m1_subset_1(sK15(sK0,sK1,sK2),u1_struct_0(sK1))
    | ~ v10_waybel_0(sK1,sK0)
    | ~ m1_subset_1(sK2,u1_struct_0(sK1))
    | v2_struct_0(sK1)
    | ~ l1_orders_2(sK0)
    | v2_struct_0(sK0) ),
    inference(subsumption_resolution,[],[f3367,f3251])).

fof(f3367,plain,
    ( ~ m1_subset_1(sK15(sK0,sK1,sK2),u1_struct_0(sK1))
    | ~ v10_waybel_0(sK1,sK0)
    | ~ m1_subset_1(sK2,u1_struct_0(sK1))
    | ~ l1_waybel_0(sK1,sK0)
    | v2_struct_0(sK1)
    | ~ l1_orders_2(sK0)
    | v2_struct_0(sK0) ),
    inference(duplicate_literal_removal,[],[f3366])).

fof(f3366,plain,
    ( ~ m1_subset_1(sK15(sK0,sK1,sK2),u1_struct_0(sK1))
    | ~ v10_waybel_0(sK1,sK0)
    | ~ m1_subset_1(sK2,u1_struct_0(sK1))
    | ~ v10_waybel_0(sK1,sK0)
    | ~ l1_waybel_0(sK1,sK0)
    | v2_struct_0(sK1)
    | ~ l1_orders_2(sK0)
    | v2_struct_0(sK0) ),
    inference(resolution,[],[f3333,f3260])).

fof(f3333,plain,
    ( ~ r1_waybel_0(sK0,sK1,a_3_0_waybel_0(sK0,sK1,sK2))
    | ~ m1_subset_1(sK15(sK0,sK1,sK2),u1_struct_0(sK1))
    | ~ v10_waybel_0(sK1,sK0) ),
    inference(duplicate_literal_removal,[],[f3332])).

fof(f3332,plain,
    ( ~ v10_waybel_0(sK1,sK0)
    | ~ m1_subset_1(sK15(sK0,sK1,sK2),u1_struct_0(sK1))
    | ~ r1_waybel_0(sK0,sK1,a_3_0_waybel_0(sK0,sK1,sK2))
    | ~ m1_subset_1(sK15(sK0,sK1,sK2),u1_struct_0(sK1))
    | ~ v10_waybel_0(sK1,sK0) ),
    inference(resolution,[],[f3300,f3256])).

fof(f3256,plain,(
    ! [X3] :
      ( r1_orders_2(sK1,X3,sK3(X3))
      | ~ m1_subset_1(X3,u1_struct_0(sK1))
      | ~ v10_waybel_0(sK1,sK0) ) ),
    inference(cnf_transformation,[],[f3219])).

fof(f3300,plain,(
    ! [X0] :
      ( ~ r1_orders_2(sK1,sK15(sK0,sK1,sK2),sK3(X0))
      | ~ v10_waybel_0(sK1,sK0)
      | ~ m1_subset_1(X0,u1_struct_0(sK1))
      | ~ r1_waybel_0(sK0,sK1,a_3_0_waybel_0(sK0,sK1,sK2)) ) ),
    inference(subsumption_resolution,[],[f3299,f3254])).

fof(f3299,plain,(
    ! [X0] :
      ( ~ m1_subset_1(X0,u1_struct_0(sK1))
      | ~ v10_waybel_0(sK1,sK0)
      | ~ r1_orders_2(sK1,sK15(sK0,sK1,sK2),sK3(X0))
      | ~ r1_waybel_0(sK0,sK1,a_3_0_waybel_0(sK0,sK1,sK2))
      | ~ m1_subset_1(sK2,u1_struct_0(sK1)) ) ),
    inference(subsumption_resolution,[],[f3298,f3255])).

fof(f3255,plain,(
    ! [X3] :
      ( m1_subset_1(sK3(X3),u1_struct_0(sK1))
      | ~ m1_subset_1(X3,u1_struct_0(sK1))
      | ~ v10_waybel_0(sK1,sK0) ) ),
    inference(cnf_transformation,[],[f3219])).

fof(f3298,plain,(
    ! [X0] :
      ( ~ m1_subset_1(X0,u1_struct_0(sK1))
      | ~ v10_waybel_0(sK1,sK0)
      | ~ r1_orders_2(sK1,sK15(sK0,sK1,sK2),sK3(X0))
      | ~ m1_subset_1(sK3(X0),u1_struct_0(sK1))
      | ~ r1_waybel_0(sK0,sK1,a_3_0_waybel_0(sK0,sK1,sK2))
      | ~ m1_subset_1(sK2,u1_struct_0(sK1)) ) ),
    inference(subsumption_resolution,[],[f3297,f3248])).

fof(f3297,plain,(
    ! [X0] :
      ( ~ m1_subset_1(X0,u1_struct_0(sK1))
      | ~ v10_waybel_0(sK1,sK0)
      | ~ r1_orders_2(sK1,sK15(sK0,sK1,sK2),sK3(X0))
      | ~ m1_subset_1(sK3(X0),u1_struct_0(sK1))
      | ~ r1_waybel_0(sK0,sK1,a_3_0_waybel_0(sK0,sK1,sK2))
      | ~ m1_subset_1(sK2,u1_struct_0(sK1))
      | v2_struct_0(sK0) ) ),
    inference(subsumption_resolution,[],[f3296,f3249])).

fof(f3296,plain,(
    ! [X0] :
      ( ~ m1_subset_1(X0,u1_struct_0(sK1))
      | ~ v10_waybel_0(sK1,sK0)
      | ~ r1_orders_2(sK1,sK15(sK0,sK1,sK2),sK3(X0))
      | ~ m1_subset_1(sK3(X0),u1_struct_0(sK1))
      | ~ r1_waybel_0(sK0,sK1,a_3_0_waybel_0(sK0,sK1,sK2))
      | ~ m1_subset_1(sK2,u1_struct_0(sK1))
      | ~ l1_orders_2(sK0)
      | v2_struct_0(sK0) ) ),
    inference(subsumption_resolution,[],[f3295,f3250])).

fof(f3295,plain,(
    ! [X0] :
      ( ~ m1_subset_1(X0,u1_struct_0(sK1))
      | ~ v10_waybel_0(sK1,sK0)
      | ~ r1_orders_2(sK1,sK15(sK0,sK1,sK2),sK3(X0))
      | ~ m1_subset_1(sK3(X0),u1_struct_0(sK1))
      | ~ r1_waybel_0(sK0,sK1,a_3_0_waybel_0(sK0,sK1,sK2))
      | ~ m1_subset_1(sK2,u1_struct_0(sK1))
      | v2_struct_0(sK1)
      | ~ l1_orders_2(sK0)
      | v2_struct_0(sK0) ) ),
    inference(subsumption_resolution,[],[f3294,f3251])).

fof(f3294,plain,(
    ! [X0] :
      ( ~ m1_subset_1(X0,u1_struct_0(sK1))
      | ~ v10_waybel_0(sK1,sK0)
      | ~ r1_orders_2(sK1,sK15(sK0,sK1,sK2),sK3(X0))
      | ~ m1_subset_1(sK3(X0),u1_struct_0(sK1))
      | ~ r1_waybel_0(sK0,sK1,a_3_0_waybel_0(sK0,sK1,sK2))
      | ~ m1_subset_1(sK2,u1_struct_0(sK1))
      | ~ l1_waybel_0(sK1,sK0)
      | v2_struct_0(sK1)
      | ~ l1_orders_2(sK0)
      | v2_struct_0(sK0) ) ),
    inference(resolution,[],[f3257,f3282])).

fof(f3282,plain,(
    ! [X6,X2,X0,X1] :
      ( r1_orders_2(X0,k2_waybel_0(X0,X1,X2),k2_waybel_0(X0,X1,X6))
      | ~ r1_orders_2(X1,sK15(X0,X1,X2),X6)
      | ~ m1_subset_1(X6,u1_struct_0(X1))
      | ~ r1_waybel_0(X0,X1,a_3_0_waybel_0(X0,X1,X2))
      | ~ m1_subset_1(X2,u1_struct_0(X1))
      | ~ l1_waybel_0(X1,X0)
      | v2_struct_0(X1)
      | ~ l1_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f3247])).

fof(f3257,plain,(
    ! [X3] :
      ( ~ r1_orders_2(sK0,k2_waybel_0(sK0,sK1,sK2),k2_waybel_0(sK0,sK1,sK3(X3)))
      | ~ m1_subset_1(X3,u1_struct_0(sK1))
      | ~ v10_waybel_0(sK1,sK0) ) ),
    inference(cnf_transformation,[],[f3219])).
%------------------------------------------------------------------------------
