%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT1632+2 : TPTP v7.4.0. Released v7.4.0.
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

% Result     : Theorem 1.77s
% Output     : Refutation 1.77s
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
    r1_waybel_0(sK0,sK1,a_3_1_waybel_0(sK0,sK1,sK2)) ),
    inference(unit_resulting_resolution,[],[f3252,f3253,f3254,f3255,f3439,f3444,f3264])).

fof(f3264,plain,(
    ! [X0,X3,X1] :
      ( r1_waybel_0(X0,X1,a_3_1_waybel_0(X0,X1,X3))
      | ~ m1_subset_1(X3,u1_struct_0(X1))
      | ~ v11_waybel_0(X1,X0)
      | ~ l1_waybel_0(X1,X0)
      | v2_struct_0(X1)
      | ~ l1_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f3229])).

fof(f3229,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ( v11_waybel_0(X1,X0)
              | ( ~ r1_waybel_0(X0,X1,a_3_1_waybel_0(X0,X1,sK6(X0,X1)))
                & m1_subset_1(sK6(X0,X1),u1_struct_0(X1)) ) )
            & ( ! [X3] :
                  ( r1_waybel_0(X0,X1,a_3_1_waybel_0(X0,X1,X3))
                  | ~ m1_subset_1(X3,u1_struct_0(X1)) )
              | ~ v11_waybel_0(X1,X0) ) )
          | ~ l1_waybel_0(X1,X0)
          | v2_struct_0(X1) )
      | ~ l1_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK6])],[f3227,f3228])).

fof(f3228,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ~ r1_waybel_0(X0,X1,a_3_1_waybel_0(X0,X1,X2))
          & m1_subset_1(X2,u1_struct_0(X1)) )
     => ( ~ r1_waybel_0(X0,X1,a_3_1_waybel_0(X0,X1,sK6(X0,X1)))
        & m1_subset_1(sK6(X0,X1),u1_struct_0(X1)) ) ) ),
    introduced(choice_axiom,[])).

fof(f3227,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ( v11_waybel_0(X1,X0)
              | ? [X2] :
                  ( ~ r1_waybel_0(X0,X1,a_3_1_waybel_0(X0,X1,X2))
                  & m1_subset_1(X2,u1_struct_0(X1)) ) )
            & ( ! [X3] :
                  ( r1_waybel_0(X0,X1,a_3_1_waybel_0(X0,X1,X3))
                  | ~ m1_subset_1(X3,u1_struct_0(X1)) )
              | ~ v11_waybel_0(X1,X0) ) )
          | ~ l1_waybel_0(X1,X0)
          | v2_struct_0(X1) )
      | ~ l1_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(rectify,[],[f3226])).

fof(f3226,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ( v11_waybel_0(X1,X0)
              | ? [X2] :
                  ( ~ r1_waybel_0(X0,X1,a_3_1_waybel_0(X0,X1,X2))
                  & m1_subset_1(X2,u1_struct_0(X1)) ) )
            & ( ! [X2] :
                  ( r1_waybel_0(X0,X1,a_3_1_waybel_0(X0,X1,X2))
                  | ~ m1_subset_1(X2,u1_struct_0(X1)) )
              | ~ v11_waybel_0(X1,X0) ) )
          | ~ l1_waybel_0(X1,X0)
          | v2_struct_0(X1) )
      | ~ l1_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(nnf_transformation,[],[f3199])).

fof(f3199,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( v11_waybel_0(X1,X0)
          <=> ! [X2] :
                ( r1_waybel_0(X0,X1,a_3_1_waybel_0(X0,X1,X2))
                | ~ m1_subset_1(X2,u1_struct_0(X1)) ) )
          | ~ l1_waybel_0(X1,X0)
          | v2_struct_0(X1) )
      | ~ l1_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f3198])).

fof(f3198,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( v11_waybel_0(X1,X0)
          <=> ! [X2] :
                ( r1_waybel_0(X0,X1,a_3_1_waybel_0(X0,X1,X2))
                | ~ m1_subset_1(X2,u1_struct_0(X1)) ) )
          | ~ l1_waybel_0(X1,X0)
          | v2_struct_0(X1) )
      | ~ l1_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f3157])).

fof(f3157,axiom,(
    ! [X0] :
      ( ( l1_orders_2(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( ( l1_waybel_0(X1,X0)
            & ~ v2_struct_0(X1) )
         => ( v11_waybel_0(X1,X0)
          <=> ! [X2] :
                ( m1_subset_1(X2,u1_struct_0(X1))
               => r1_waybel_0(X0,X1,a_3_1_waybel_0(X0,X1,X2)) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d14_waybel_0)).

fof(f3444,plain,(
    m1_subset_1(sK2,u1_struct_0(sK1)) ),
    inference(unit_resulting_resolution,[],[f3439,f3258])).

fof(f3258,plain,
    ( m1_subset_1(sK2,u1_struct_0(sK1))
    | ~ v11_waybel_0(sK1,sK0) ),
    inference(cnf_transformation,[],[f3223])).

fof(f3223,plain,
    ( ( ( ! [X3] :
            ( ( ~ r1_orders_2(sK0,k2_waybel_0(sK0,sK1,sK3(X3)),k2_waybel_0(sK0,sK1,sK2))
              & r1_orders_2(sK1,X3,sK3(X3))
              & m1_subset_1(sK3(X3),u1_struct_0(sK1)) )
            | ~ m1_subset_1(X3,u1_struct_0(sK1)) )
        & m1_subset_1(sK2,u1_struct_0(sK1)) )
      | ~ v11_waybel_0(sK1,sK0) )
    & ( ! [X5] :
          ( ( ! [X7] :
                ( r1_orders_2(sK0,k2_waybel_0(sK0,sK1,X7),k2_waybel_0(sK0,sK1,X5))
                | ~ r1_orders_2(sK1,sK4(X5),X7)
                | ~ m1_subset_1(X7,u1_struct_0(sK1)) )
            & m1_subset_1(sK4(X5),u1_struct_0(sK1)) )
          | ~ m1_subset_1(X5,u1_struct_0(sK1)) )
      | v11_waybel_0(sK1,sK0) )
    & l1_waybel_0(sK1,sK0)
    & ~ v2_struct_0(sK1)
    & l1_orders_2(sK0)
    & ~ v2_struct_0(sK0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3,sK4])],[f3217,f3222,f3221,f3220,f3219,f3218])).

fof(f3218,plain,
    ( ? [X0] :
        ( ? [X1] :
            ( ( ? [X2] :
                  ( ! [X3] :
                      ( ? [X4] :
                          ( ~ r1_orders_2(X0,k2_waybel_0(X0,X1,X4),k2_waybel_0(X0,X1,X2))
                          & r1_orders_2(X1,X3,X4)
                          & m1_subset_1(X4,u1_struct_0(X1)) )
                      | ~ m1_subset_1(X3,u1_struct_0(X1)) )
                  & m1_subset_1(X2,u1_struct_0(X1)) )
              | ~ v11_waybel_0(X1,X0) )
            & ( ! [X5] :
                  ( ? [X6] :
                      ( ! [X7] :
                          ( r1_orders_2(X0,k2_waybel_0(X0,X1,X7),k2_waybel_0(X0,X1,X5))
                          | ~ r1_orders_2(X1,X6,X7)
                          | ~ m1_subset_1(X7,u1_struct_0(X1)) )
                      & m1_subset_1(X6,u1_struct_0(X1)) )
                  | ~ m1_subset_1(X5,u1_struct_0(X1)) )
              | v11_waybel_0(X1,X0) )
            & l1_waybel_0(X1,X0)
            & ~ v2_struct_0(X1) )
        & l1_orders_2(X0)
        & ~ v2_struct_0(X0) )
   => ( ? [X1] :
          ( ( ? [X2] :
                ( ! [X3] :
                    ( ? [X4] :
                        ( ~ r1_orders_2(sK0,k2_waybel_0(sK0,X1,X4),k2_waybel_0(sK0,X1,X2))
                        & r1_orders_2(X1,X3,X4)
                        & m1_subset_1(X4,u1_struct_0(X1)) )
                    | ~ m1_subset_1(X3,u1_struct_0(X1)) )
                & m1_subset_1(X2,u1_struct_0(X1)) )
            | ~ v11_waybel_0(X1,sK0) )
          & ( ! [X5] :
                ( ? [X6] :
                    ( ! [X7] :
                        ( r1_orders_2(sK0,k2_waybel_0(sK0,X1,X7),k2_waybel_0(sK0,X1,X5))
                        | ~ r1_orders_2(X1,X6,X7)
                        | ~ m1_subset_1(X7,u1_struct_0(X1)) )
                    & m1_subset_1(X6,u1_struct_0(X1)) )
                | ~ m1_subset_1(X5,u1_struct_0(X1)) )
            | v11_waybel_0(X1,sK0) )
          & l1_waybel_0(X1,sK0)
          & ~ v2_struct_0(X1) )
      & l1_orders_2(sK0)
      & ~ v2_struct_0(sK0) ) ),
    introduced(choice_axiom,[])).

fof(f3219,plain,
    ( ? [X1] :
        ( ( ? [X2] :
              ( ! [X3] :
                  ( ? [X4] :
                      ( ~ r1_orders_2(sK0,k2_waybel_0(sK0,X1,X4),k2_waybel_0(sK0,X1,X2))
                      & r1_orders_2(X1,X3,X4)
                      & m1_subset_1(X4,u1_struct_0(X1)) )
                  | ~ m1_subset_1(X3,u1_struct_0(X1)) )
              & m1_subset_1(X2,u1_struct_0(X1)) )
          | ~ v11_waybel_0(X1,sK0) )
        & ( ! [X5] :
              ( ? [X6] :
                  ( ! [X7] :
                      ( r1_orders_2(sK0,k2_waybel_0(sK0,X1,X7),k2_waybel_0(sK0,X1,X5))
                      | ~ r1_orders_2(X1,X6,X7)
                      | ~ m1_subset_1(X7,u1_struct_0(X1)) )
                  & m1_subset_1(X6,u1_struct_0(X1)) )
              | ~ m1_subset_1(X5,u1_struct_0(X1)) )
          | v11_waybel_0(X1,sK0) )
        & l1_waybel_0(X1,sK0)
        & ~ v2_struct_0(X1) )
   => ( ( ? [X2] :
            ( ! [X3] :
                ( ? [X4] :
                    ( ~ r1_orders_2(sK0,k2_waybel_0(sK0,sK1,X4),k2_waybel_0(sK0,sK1,X2))
                    & r1_orders_2(sK1,X3,X4)
                    & m1_subset_1(X4,u1_struct_0(sK1)) )
                | ~ m1_subset_1(X3,u1_struct_0(sK1)) )
            & m1_subset_1(X2,u1_struct_0(sK1)) )
        | ~ v11_waybel_0(sK1,sK0) )
      & ( ! [X5] :
            ( ? [X6] :
                ( ! [X7] :
                    ( r1_orders_2(sK0,k2_waybel_0(sK0,sK1,X7),k2_waybel_0(sK0,sK1,X5))
                    | ~ r1_orders_2(sK1,X6,X7)
                    | ~ m1_subset_1(X7,u1_struct_0(sK1)) )
                & m1_subset_1(X6,u1_struct_0(sK1)) )
            | ~ m1_subset_1(X5,u1_struct_0(sK1)) )
        | v11_waybel_0(sK1,sK0) )
      & l1_waybel_0(sK1,sK0)
      & ~ v2_struct_0(sK1) ) ),
    introduced(choice_axiom,[])).

fof(f3220,plain,
    ( ? [X2] :
        ( ! [X3] :
            ( ? [X4] :
                ( ~ r1_orders_2(sK0,k2_waybel_0(sK0,sK1,X4),k2_waybel_0(sK0,sK1,X2))
                & r1_orders_2(sK1,X3,X4)
                & m1_subset_1(X4,u1_struct_0(sK1)) )
            | ~ m1_subset_1(X3,u1_struct_0(sK1)) )
        & m1_subset_1(X2,u1_struct_0(sK1)) )
   => ( ! [X3] :
          ( ? [X4] :
              ( ~ r1_orders_2(sK0,k2_waybel_0(sK0,sK1,X4),k2_waybel_0(sK0,sK1,sK2))
              & r1_orders_2(sK1,X3,X4)
              & m1_subset_1(X4,u1_struct_0(sK1)) )
          | ~ m1_subset_1(X3,u1_struct_0(sK1)) )
      & m1_subset_1(sK2,u1_struct_0(sK1)) ) ),
    introduced(choice_axiom,[])).

fof(f3221,plain,(
    ! [X3] :
      ( ? [X4] :
          ( ~ r1_orders_2(sK0,k2_waybel_0(sK0,sK1,X4),k2_waybel_0(sK0,sK1,sK2))
          & r1_orders_2(sK1,X3,X4)
          & m1_subset_1(X4,u1_struct_0(sK1)) )
     => ( ~ r1_orders_2(sK0,k2_waybel_0(sK0,sK1,sK3(X3)),k2_waybel_0(sK0,sK1,sK2))
        & r1_orders_2(sK1,X3,sK3(X3))
        & m1_subset_1(sK3(X3),u1_struct_0(sK1)) ) ) ),
    introduced(choice_axiom,[])).

fof(f3222,plain,(
    ! [X5] :
      ( ? [X6] :
          ( ! [X7] :
              ( r1_orders_2(sK0,k2_waybel_0(sK0,sK1,X7),k2_waybel_0(sK0,sK1,X5))
              | ~ r1_orders_2(sK1,X6,X7)
              | ~ m1_subset_1(X7,u1_struct_0(sK1)) )
          & m1_subset_1(X6,u1_struct_0(sK1)) )
     => ( ! [X7] :
            ( r1_orders_2(sK0,k2_waybel_0(sK0,sK1,X7),k2_waybel_0(sK0,sK1,X5))
            | ~ r1_orders_2(sK1,sK4(X5),X7)
            | ~ m1_subset_1(X7,u1_struct_0(sK1)) )
        & m1_subset_1(sK4(X5),u1_struct_0(sK1)) ) ) ),
    introduced(choice_axiom,[])).

fof(f3217,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ( ? [X2] :
                ( ! [X3] :
                    ( ? [X4] :
                        ( ~ r1_orders_2(X0,k2_waybel_0(X0,X1,X4),k2_waybel_0(X0,X1,X2))
                        & r1_orders_2(X1,X3,X4)
                        & m1_subset_1(X4,u1_struct_0(X1)) )
                    | ~ m1_subset_1(X3,u1_struct_0(X1)) )
                & m1_subset_1(X2,u1_struct_0(X1)) )
            | ~ v11_waybel_0(X1,X0) )
          & ( ! [X5] :
                ( ? [X6] :
                    ( ! [X7] :
                        ( r1_orders_2(X0,k2_waybel_0(X0,X1,X7),k2_waybel_0(X0,X1,X5))
                        | ~ r1_orders_2(X1,X6,X7)
                        | ~ m1_subset_1(X7,u1_struct_0(X1)) )
                    & m1_subset_1(X6,u1_struct_0(X1)) )
                | ~ m1_subset_1(X5,u1_struct_0(X1)) )
            | v11_waybel_0(X1,X0) )
          & l1_waybel_0(X1,X0)
          & ~ v2_struct_0(X1) )
      & l1_orders_2(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(rectify,[],[f3216])).

fof(f3216,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ( ? [X2] :
                ( ! [X3] :
                    ( ? [X4] :
                        ( ~ r1_orders_2(X0,k2_waybel_0(X0,X1,X4),k2_waybel_0(X0,X1,X2))
                        & r1_orders_2(X1,X3,X4)
                        & m1_subset_1(X4,u1_struct_0(X1)) )
                    | ~ m1_subset_1(X3,u1_struct_0(X1)) )
                & m1_subset_1(X2,u1_struct_0(X1)) )
            | ~ v11_waybel_0(X1,X0) )
          & ( ! [X2] :
                ( ? [X3] :
                    ( ! [X4] :
                        ( r1_orders_2(X0,k2_waybel_0(X0,X1,X4),k2_waybel_0(X0,X1,X2))
                        | ~ r1_orders_2(X1,X3,X4)
                        | ~ m1_subset_1(X4,u1_struct_0(X1)) )
                    & m1_subset_1(X3,u1_struct_0(X1)) )
                | ~ m1_subset_1(X2,u1_struct_0(X1)) )
            | v11_waybel_0(X1,X0) )
          & l1_waybel_0(X1,X0)
          & ~ v2_struct_0(X1) )
      & l1_orders_2(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(flattening,[],[f3215])).

fof(f3215,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ( ? [X2] :
                ( ! [X3] :
                    ( ? [X4] :
                        ( ~ r1_orders_2(X0,k2_waybel_0(X0,X1,X4),k2_waybel_0(X0,X1,X2))
                        & r1_orders_2(X1,X3,X4)
                        & m1_subset_1(X4,u1_struct_0(X1)) )
                    | ~ m1_subset_1(X3,u1_struct_0(X1)) )
                & m1_subset_1(X2,u1_struct_0(X1)) )
            | ~ v11_waybel_0(X1,X0) )
          & ( ! [X2] :
                ( ? [X3] :
                    ( ! [X4] :
                        ( r1_orders_2(X0,k2_waybel_0(X0,X1,X4),k2_waybel_0(X0,X1,X2))
                        | ~ r1_orders_2(X1,X3,X4)
                        | ~ m1_subset_1(X4,u1_struct_0(X1)) )
                    & m1_subset_1(X3,u1_struct_0(X1)) )
                | ~ m1_subset_1(X2,u1_struct_0(X1)) )
            | v11_waybel_0(X1,X0) )
          & l1_waybel_0(X1,X0)
          & ~ v2_struct_0(X1) )
      & l1_orders_2(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(nnf_transformation,[],[f3195])).

fof(f3195,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ( v11_waybel_0(X1,X0)
          <~> ! [X2] :
                ( ? [X3] :
                    ( ! [X4] :
                        ( r1_orders_2(X0,k2_waybel_0(X0,X1,X4),k2_waybel_0(X0,X1,X2))
                        | ~ r1_orders_2(X1,X3,X4)
                        | ~ m1_subset_1(X4,u1_struct_0(X1)) )
                    & m1_subset_1(X3,u1_struct_0(X1)) )
                | ~ m1_subset_1(X2,u1_struct_0(X1)) ) )
          & l1_waybel_0(X1,X0)
          & ~ v2_struct_0(X1) )
      & l1_orders_2(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(flattening,[],[f3194])).

fof(f3194,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ( v11_waybel_0(X1,X0)
          <~> ! [X2] :
                ( ? [X3] :
                    ( ! [X4] :
                        ( r1_orders_2(X0,k2_waybel_0(X0,X1,X4),k2_waybel_0(X0,X1,X2))
                        | ~ r1_orders_2(X1,X3,X4)
                        | ~ m1_subset_1(X4,u1_struct_0(X1)) )
                    & m1_subset_1(X3,u1_struct_0(X1)) )
                | ~ m1_subset_1(X2,u1_struct_0(X1)) ) )
          & l1_waybel_0(X1,X0)
          & ~ v2_struct_0(X1) )
      & l1_orders_2(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f3178])).

fof(f3178,negated_conjecture,(
    ~ ! [X0] :
        ( ( l1_orders_2(X0)
          & ~ v2_struct_0(X0) )
       => ! [X1] :
            ( ( l1_waybel_0(X1,X0)
              & ~ v2_struct_0(X1) )
           => ( v11_waybel_0(X1,X0)
            <=> ! [X2] :
                  ( m1_subset_1(X2,u1_struct_0(X1))
                 => ? [X3] :
                      ( ! [X4] :
                          ( m1_subset_1(X4,u1_struct_0(X1))
                         => ( r1_orders_2(X1,X3,X4)
                           => r1_orders_2(X0,k2_waybel_0(X0,X1,X4),k2_waybel_0(X0,X1,X2)) ) )
                      & m1_subset_1(X3,u1_struct_0(X1)) ) ) ) ) ) ),
    inference(negated_conjecture,[],[f3177])).

fof(f3177,conjecture,(
    ! [X0] :
      ( ( l1_orders_2(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( ( l1_waybel_0(X1,X0)
            & ~ v2_struct_0(X1) )
         => ( v11_waybel_0(X1,X0)
          <=> ! [X2] :
                ( m1_subset_1(X2,u1_struct_0(X1))
               => ? [X3] :
                    ( ! [X4] :
                        ( m1_subset_1(X4,u1_struct_0(X1))
                       => ( r1_orders_2(X1,X3,X4)
                         => r1_orders_2(X0,k2_waybel_0(X0,X1,X4),k2_waybel_0(X0,X1,X2)) ) )
                    & m1_subset_1(X3,u1_struct_0(X1)) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t12_waybel_0)).

fof(f3439,plain,(
    v11_waybel_0(sK1,sK0) ),
    inference(subsumption_resolution,[],[f3438,f3252])).

fof(f3438,plain,
    ( v11_waybel_0(sK1,sK0)
    | v2_struct_0(sK0) ),
    inference(subsumption_resolution,[],[f3437,f3253])).

fof(f3437,plain,
    ( v11_waybel_0(sK1,sK0)
    | ~ l1_orders_2(sK0)
    | v2_struct_0(sK0) ),
    inference(subsumption_resolution,[],[f3436,f3254])).

fof(f3436,plain,
    ( v11_waybel_0(sK1,sK0)
    | v2_struct_0(sK1)
    | ~ l1_orders_2(sK0)
    | v2_struct_0(sK0) ),
    inference(subsumption_resolution,[],[f3435,f3255])).

fof(f3435,plain,
    ( v11_waybel_0(sK1,sK0)
    | ~ l1_waybel_0(sK1,sK0)
    | v2_struct_0(sK1)
    | ~ l1_orders_2(sK0)
    | v2_struct_0(sK0) ),
    inference(duplicate_literal_removal,[],[f3434])).

fof(f3434,plain,
    ( v11_waybel_0(sK1,sK0)
    | v11_waybel_0(sK1,sK0)
    | ~ l1_waybel_0(sK1,sK0)
    | v2_struct_0(sK1)
    | ~ l1_orders_2(sK0)
    | v2_struct_0(sK0) ),
    inference(resolution,[],[f3414,f3265])).

fof(f3265,plain,(
    ! [X0,X1] :
      ( m1_subset_1(sK6(X0,X1),u1_struct_0(X1))
      | v11_waybel_0(X1,X0)
      | ~ l1_waybel_0(X1,X0)
      | v2_struct_0(X1)
      | ~ l1_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f3229])).

fof(f3414,plain,
    ( ~ m1_subset_1(sK6(sK0,sK1),u1_struct_0(sK1))
    | v11_waybel_0(sK1,sK0) ),
    inference(subsumption_resolution,[],[f3413,f3252])).

fof(f3413,plain,
    ( v11_waybel_0(sK1,sK0)
    | ~ m1_subset_1(sK6(sK0,sK1),u1_struct_0(sK1))
    | v2_struct_0(sK0) ),
    inference(subsumption_resolution,[],[f3412,f3253])).

fof(f3412,plain,
    ( v11_waybel_0(sK1,sK0)
    | ~ m1_subset_1(sK6(sK0,sK1),u1_struct_0(sK1))
    | ~ l1_orders_2(sK0)
    | v2_struct_0(sK0) ),
    inference(subsumption_resolution,[],[f3411,f3254])).

fof(f3411,plain,
    ( v11_waybel_0(sK1,sK0)
    | ~ m1_subset_1(sK6(sK0,sK1),u1_struct_0(sK1))
    | v2_struct_0(sK1)
    | ~ l1_orders_2(sK0)
    | v2_struct_0(sK0) ),
    inference(subsumption_resolution,[],[f3410,f3255])).

fof(f3410,plain,
    ( v11_waybel_0(sK1,sK0)
    | ~ m1_subset_1(sK6(sK0,sK1),u1_struct_0(sK1))
    | ~ l1_waybel_0(sK1,sK0)
    | v2_struct_0(sK1)
    | ~ l1_orders_2(sK0)
    | v2_struct_0(sK0) ),
    inference(duplicate_literal_removal,[],[f3407])).

fof(f3407,plain,
    ( v11_waybel_0(sK1,sK0)
    | ~ m1_subset_1(sK6(sK0,sK1),u1_struct_0(sK1))
    | v11_waybel_0(sK1,sK0)
    | ~ l1_waybel_0(sK1,sK0)
    | v2_struct_0(sK1)
    | ~ l1_orders_2(sK0)
    | v2_struct_0(sK0) ),
    inference(resolution,[],[f3383,f3266])).

fof(f3266,plain,(
    ! [X0,X1] :
      ( ~ r1_waybel_0(X0,X1,a_3_1_waybel_0(X0,X1,sK6(X0,X1)))
      | v11_waybel_0(X1,X0)
      | ~ l1_waybel_0(X1,X0)
      | v2_struct_0(X1)
      | ~ l1_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f3229])).

fof(f3383,plain,(
    ! [X0] :
      ( r1_waybel_0(sK0,sK1,a_3_1_waybel_0(sK0,sK1,X0))
      | v11_waybel_0(sK1,sK0)
      | ~ m1_subset_1(X0,u1_struct_0(sK1)) ) ),
    inference(subsumption_resolution,[],[f3382,f3256])).

fof(f3256,plain,(
    ! [X5] :
      ( m1_subset_1(sK4(X5),u1_struct_0(sK1))
      | ~ m1_subset_1(X5,u1_struct_0(sK1))
      | v11_waybel_0(sK1,sK0) ) ),
    inference(cnf_transformation,[],[f3223])).

fof(f3382,plain,(
    ! [X0] :
      ( ~ m1_subset_1(X0,u1_struct_0(sK1))
      | v11_waybel_0(sK1,sK0)
      | r1_waybel_0(sK0,sK1,a_3_1_waybel_0(sK0,sK1,X0))
      | ~ m1_subset_1(sK4(X0),u1_struct_0(sK1)) ) ),
    inference(subsumption_resolution,[],[f3381,f3252])).

fof(f3381,plain,(
    ! [X0] :
      ( ~ m1_subset_1(X0,u1_struct_0(sK1))
      | v11_waybel_0(sK1,sK0)
      | r1_waybel_0(sK0,sK1,a_3_1_waybel_0(sK0,sK1,X0))
      | ~ m1_subset_1(sK4(X0),u1_struct_0(sK1))
      | v2_struct_0(sK0) ) ),
    inference(subsumption_resolution,[],[f3380,f3253])).

fof(f3380,plain,(
    ! [X0] :
      ( ~ m1_subset_1(X0,u1_struct_0(sK1))
      | v11_waybel_0(sK1,sK0)
      | r1_waybel_0(sK0,sK1,a_3_1_waybel_0(sK0,sK1,X0))
      | ~ m1_subset_1(sK4(X0),u1_struct_0(sK1))
      | ~ l1_orders_2(sK0)
      | v2_struct_0(sK0) ) ),
    inference(subsumption_resolution,[],[f3379,f3254])).

fof(f3379,plain,(
    ! [X0] :
      ( ~ m1_subset_1(X0,u1_struct_0(sK1))
      | v11_waybel_0(sK1,sK0)
      | r1_waybel_0(sK0,sK1,a_3_1_waybel_0(sK0,sK1,X0))
      | ~ m1_subset_1(sK4(X0),u1_struct_0(sK1))
      | v2_struct_0(sK1)
      | ~ l1_orders_2(sK0)
      | v2_struct_0(sK0) ) ),
    inference(subsumption_resolution,[],[f3378,f3255])).

fof(f3378,plain,(
    ! [X0] :
      ( ~ m1_subset_1(X0,u1_struct_0(sK1))
      | v11_waybel_0(sK1,sK0)
      | r1_waybel_0(sK0,sK1,a_3_1_waybel_0(sK0,sK1,X0))
      | ~ m1_subset_1(sK4(X0),u1_struct_0(sK1))
      | ~ l1_waybel_0(sK1,sK0)
      | v2_struct_0(sK1)
      | ~ l1_orders_2(sK0)
      | v2_struct_0(sK0) ) ),
    inference(duplicate_literal_removal,[],[f3377])).

fof(f3377,plain,(
    ! [X0] :
      ( ~ m1_subset_1(X0,u1_struct_0(sK1))
      | v11_waybel_0(sK1,sK0)
      | r1_waybel_0(sK0,sK1,a_3_1_waybel_0(sK0,sK1,X0))
      | r1_waybel_0(sK0,sK1,a_3_1_waybel_0(sK0,sK1,X0))
      | ~ m1_subset_1(sK4(X0),u1_struct_0(sK1))
      | ~ m1_subset_1(X0,u1_struct_0(sK1))
      | ~ l1_waybel_0(sK1,sK0)
      | v2_struct_0(sK1)
      | ~ l1_orders_2(sK0)
      | v2_struct_0(sK0) ) ),
    inference(resolution,[],[f3354,f3287])).

fof(f3287,plain,(
    ! [X2,X0,X3,X1] :
      ( m1_subset_1(sK14(X0,X1,X2,X3),u1_struct_0(X1))
      | r1_waybel_0(X0,X1,a_3_1_waybel_0(X0,X1,X2))
      | ~ m1_subset_1(X3,u1_struct_0(X1))
      | ~ m1_subset_1(X2,u1_struct_0(X1))
      | ~ l1_waybel_0(X1,X0)
      | v2_struct_0(X1)
      | ~ l1_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f3251])).

fof(f3251,plain,(
    ! [X0,X1,X2] :
      ( ( ( r1_waybel_0(X0,X1,a_3_1_waybel_0(X0,X1,X2))
          | ! [X3] :
              ( ( ~ r1_orders_2(X0,k2_waybel_0(X0,X1,sK14(X0,X1,X2,X3)),k2_waybel_0(X0,X1,X2))
                & r1_orders_2(X1,X3,sK14(X0,X1,X2,X3))
                & m1_subset_1(sK14(X0,X1,X2,X3),u1_struct_0(X1)) )
              | ~ m1_subset_1(X3,u1_struct_0(X1)) ) )
        & ( ( ! [X6] :
                ( r1_orders_2(X0,k2_waybel_0(X0,X1,X6),k2_waybel_0(X0,X1,X2))
                | ~ r1_orders_2(X1,sK15(X0,X1,X2),X6)
                | ~ m1_subset_1(X6,u1_struct_0(X1)) )
            & m1_subset_1(sK15(X0,X1,X2),u1_struct_0(X1)) )
          | ~ r1_waybel_0(X0,X1,a_3_1_waybel_0(X0,X1,X2)) ) )
      | ~ m1_subset_1(X2,u1_struct_0(X1))
      | ~ l1_waybel_0(X1,X0)
      | v2_struct_0(X1)
      | ~ l1_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK14,sK15])],[f3248,f3250,f3249])).

fof(f3249,plain,(
    ! [X3,X2,X1,X0] :
      ( ? [X4] :
          ( ~ r1_orders_2(X0,k2_waybel_0(X0,X1,X4),k2_waybel_0(X0,X1,X2))
          & r1_orders_2(X1,X3,X4)
          & m1_subset_1(X4,u1_struct_0(X1)) )
     => ( ~ r1_orders_2(X0,k2_waybel_0(X0,X1,sK14(X0,X1,X2,X3)),k2_waybel_0(X0,X1,X2))
        & r1_orders_2(X1,X3,sK14(X0,X1,X2,X3))
        & m1_subset_1(sK14(X0,X1,X2,X3),u1_struct_0(X1)) ) ) ),
    introduced(choice_axiom,[])).

fof(f3250,plain,(
    ! [X2,X1,X0] :
      ( ? [X5] :
          ( ! [X6] :
              ( r1_orders_2(X0,k2_waybel_0(X0,X1,X6),k2_waybel_0(X0,X1,X2))
              | ~ r1_orders_2(X1,X5,X6)
              | ~ m1_subset_1(X6,u1_struct_0(X1)) )
          & m1_subset_1(X5,u1_struct_0(X1)) )
     => ( ! [X6] :
            ( r1_orders_2(X0,k2_waybel_0(X0,X1,X6),k2_waybel_0(X0,X1,X2))
            | ~ r1_orders_2(X1,sK15(X0,X1,X2),X6)
            | ~ m1_subset_1(X6,u1_struct_0(X1)) )
        & m1_subset_1(sK15(X0,X1,X2),u1_struct_0(X1)) ) ) ),
    introduced(choice_axiom,[])).

fof(f3248,plain,(
    ! [X0,X1,X2] :
      ( ( ( r1_waybel_0(X0,X1,a_3_1_waybel_0(X0,X1,X2))
          | ! [X3] :
              ( ? [X4] :
                  ( ~ r1_orders_2(X0,k2_waybel_0(X0,X1,X4),k2_waybel_0(X0,X1,X2))
                  & r1_orders_2(X1,X3,X4)
                  & m1_subset_1(X4,u1_struct_0(X1)) )
              | ~ m1_subset_1(X3,u1_struct_0(X1)) ) )
        & ( ? [X5] :
              ( ! [X6] :
                  ( r1_orders_2(X0,k2_waybel_0(X0,X1,X6),k2_waybel_0(X0,X1,X2))
                  | ~ r1_orders_2(X1,X5,X6)
                  | ~ m1_subset_1(X6,u1_struct_0(X1)) )
              & m1_subset_1(X5,u1_struct_0(X1)) )
          | ~ r1_waybel_0(X0,X1,a_3_1_waybel_0(X0,X1,X2)) ) )
      | ~ m1_subset_1(X2,u1_struct_0(X1))
      | ~ l1_waybel_0(X1,X0)
      | v2_struct_0(X1)
      | ~ l1_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(rectify,[],[f3247])).

fof(f3247,plain,(
    ! [X0,X1,X2] :
      ( ( ( r1_waybel_0(X0,X1,a_3_1_waybel_0(X0,X1,X2))
          | ! [X3] :
              ( ? [X4] :
                  ( ~ r1_orders_2(X0,k2_waybel_0(X0,X1,X4),k2_waybel_0(X0,X1,X2))
                  & r1_orders_2(X1,X3,X4)
                  & m1_subset_1(X4,u1_struct_0(X1)) )
              | ~ m1_subset_1(X3,u1_struct_0(X1)) ) )
        & ( ? [X3] :
              ( ! [X4] :
                  ( r1_orders_2(X0,k2_waybel_0(X0,X1,X4),k2_waybel_0(X0,X1,X2))
                  | ~ r1_orders_2(X1,X3,X4)
                  | ~ m1_subset_1(X4,u1_struct_0(X1)) )
              & m1_subset_1(X3,u1_struct_0(X1)) )
          | ~ r1_waybel_0(X0,X1,a_3_1_waybel_0(X0,X1,X2)) ) )
      | ~ m1_subset_1(X2,u1_struct_0(X1))
      | ~ l1_waybel_0(X1,X0)
      | v2_struct_0(X1)
      | ~ l1_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(nnf_transformation,[],[f3214])).

fof(f3214,plain,(
    ! [X0,X1,X2] :
      ( ( r1_waybel_0(X0,X1,a_3_1_waybel_0(X0,X1,X2))
      <=> ? [X3] :
            ( ! [X4] :
                ( r1_orders_2(X0,k2_waybel_0(X0,X1,X4),k2_waybel_0(X0,X1,X2))
                | ~ r1_orders_2(X1,X3,X4)
                | ~ m1_subset_1(X4,u1_struct_0(X1)) )
            & m1_subset_1(X3,u1_struct_0(X1)) ) )
      | ~ m1_subset_1(X2,u1_struct_0(X1))
      | ~ l1_waybel_0(X1,X0)
      | v2_struct_0(X1)
      | ~ l1_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f3213])).

fof(f3213,plain,(
    ! [X0,X1,X2] :
      ( ( r1_waybel_0(X0,X1,a_3_1_waybel_0(X0,X1,X2))
      <=> ? [X3] :
            ( ! [X4] :
                ( r1_orders_2(X0,k2_waybel_0(X0,X1,X4),k2_waybel_0(X0,X1,X2))
                | ~ r1_orders_2(X1,X3,X4)
                | ~ m1_subset_1(X4,u1_struct_0(X1)) )
            & m1_subset_1(X3,u1_struct_0(X1)) ) )
      | ~ m1_subset_1(X2,u1_struct_0(X1))
      | ~ l1_waybel_0(X1,X0)
      | v2_struct_0(X1)
      | ~ l1_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f3172])).

fof(f3172,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,u1_struct_0(X1))
        & l1_waybel_0(X1,X0)
        & ~ v2_struct_0(X1)
        & l1_orders_2(X0)
        & ~ v2_struct_0(X0) )
     => ( r1_waybel_0(X0,X1,a_3_1_waybel_0(X0,X1,X2))
      <=> ? [X3] :
            ( ! [X4] :
                ( m1_subset_1(X4,u1_struct_0(X1))
               => ( r1_orders_2(X1,X3,X4)
                 => r1_orders_2(X0,k2_waybel_0(X0,X1,X4),k2_waybel_0(X0,X1,X2)) ) )
            & m1_subset_1(X3,u1_struct_0(X1)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',s1_waybel_0__e1_35_1__waybel_0)).

fof(f3354,plain,(
    ! [X0] :
      ( ~ m1_subset_1(sK14(sK0,sK1,X0,sK4(X0)),u1_struct_0(sK1))
      | ~ m1_subset_1(X0,u1_struct_0(sK1))
      | v11_waybel_0(sK1,sK0)
      | r1_waybel_0(sK0,sK1,a_3_1_waybel_0(sK0,sK1,X0)) ) ),
    inference(subsumption_resolution,[],[f3353,f3256])).

fof(f3353,plain,(
    ! [X0] :
      ( ~ m1_subset_1(sK14(sK0,sK1,X0,sK4(X0)),u1_struct_0(sK1))
      | ~ m1_subset_1(X0,u1_struct_0(sK1))
      | v11_waybel_0(sK1,sK0)
      | r1_waybel_0(sK0,sK1,a_3_1_waybel_0(sK0,sK1,X0))
      | ~ m1_subset_1(sK4(X0),u1_struct_0(sK1)) ) ),
    inference(subsumption_resolution,[],[f3352,f3252])).

fof(f3352,plain,(
    ! [X0] :
      ( ~ m1_subset_1(sK14(sK0,sK1,X0,sK4(X0)),u1_struct_0(sK1))
      | ~ m1_subset_1(X0,u1_struct_0(sK1))
      | v11_waybel_0(sK1,sK0)
      | r1_waybel_0(sK0,sK1,a_3_1_waybel_0(sK0,sK1,X0))
      | ~ m1_subset_1(sK4(X0),u1_struct_0(sK1))
      | v2_struct_0(sK0) ) ),
    inference(subsumption_resolution,[],[f3351,f3253])).

fof(f3351,plain,(
    ! [X0] :
      ( ~ m1_subset_1(sK14(sK0,sK1,X0,sK4(X0)),u1_struct_0(sK1))
      | ~ m1_subset_1(X0,u1_struct_0(sK1))
      | v11_waybel_0(sK1,sK0)
      | r1_waybel_0(sK0,sK1,a_3_1_waybel_0(sK0,sK1,X0))
      | ~ m1_subset_1(sK4(X0),u1_struct_0(sK1))
      | ~ l1_orders_2(sK0)
      | v2_struct_0(sK0) ) ),
    inference(subsumption_resolution,[],[f3350,f3254])).

fof(f3350,plain,(
    ! [X0] :
      ( ~ m1_subset_1(sK14(sK0,sK1,X0,sK4(X0)),u1_struct_0(sK1))
      | ~ m1_subset_1(X0,u1_struct_0(sK1))
      | v11_waybel_0(sK1,sK0)
      | r1_waybel_0(sK0,sK1,a_3_1_waybel_0(sK0,sK1,X0))
      | ~ m1_subset_1(sK4(X0),u1_struct_0(sK1))
      | v2_struct_0(sK1)
      | ~ l1_orders_2(sK0)
      | v2_struct_0(sK0) ) ),
    inference(subsumption_resolution,[],[f3349,f3255])).

fof(f3349,plain,(
    ! [X0] :
      ( ~ m1_subset_1(sK14(sK0,sK1,X0,sK4(X0)),u1_struct_0(sK1))
      | ~ m1_subset_1(X0,u1_struct_0(sK1))
      | v11_waybel_0(sK1,sK0)
      | r1_waybel_0(sK0,sK1,a_3_1_waybel_0(sK0,sK1,X0))
      | ~ m1_subset_1(sK4(X0),u1_struct_0(sK1))
      | ~ l1_waybel_0(sK1,sK0)
      | v2_struct_0(sK1)
      | ~ l1_orders_2(sK0)
      | v2_struct_0(sK0) ) ),
    inference(duplicate_literal_removal,[],[f3348])).

fof(f3348,plain,(
    ! [X0] :
      ( ~ m1_subset_1(sK14(sK0,sK1,X0,sK4(X0)),u1_struct_0(sK1))
      | ~ m1_subset_1(X0,u1_struct_0(sK1))
      | v11_waybel_0(sK1,sK0)
      | r1_waybel_0(sK0,sK1,a_3_1_waybel_0(sK0,sK1,X0))
      | ~ m1_subset_1(sK4(X0),u1_struct_0(sK1))
      | r1_waybel_0(sK0,sK1,a_3_1_waybel_0(sK0,sK1,X0))
      | ~ m1_subset_1(sK4(X0),u1_struct_0(sK1))
      | ~ m1_subset_1(X0,u1_struct_0(sK1))
      | ~ l1_waybel_0(sK1,sK0)
      | v2_struct_0(sK1)
      | ~ l1_orders_2(sK0)
      | v2_struct_0(sK0) ) ),
    inference(resolution,[],[f3319,f3288])).

fof(f3288,plain,(
    ! [X2,X0,X3,X1] :
      ( r1_orders_2(X1,X3,sK14(X0,X1,X2,X3))
      | r1_waybel_0(X0,X1,a_3_1_waybel_0(X0,X1,X2))
      | ~ m1_subset_1(X3,u1_struct_0(X1))
      | ~ m1_subset_1(X2,u1_struct_0(X1))
      | ~ l1_waybel_0(X1,X0)
      | v2_struct_0(X1)
      | ~ l1_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f3251])).

fof(f3319,plain,(
    ! [X4,X3] :
      ( ~ r1_orders_2(sK1,sK4(X3),sK14(sK0,sK1,X3,X4))
      | ~ m1_subset_1(sK14(sK0,sK1,X3,X4),u1_struct_0(sK1))
      | ~ m1_subset_1(X3,u1_struct_0(sK1))
      | v11_waybel_0(sK1,sK0)
      | r1_waybel_0(sK0,sK1,a_3_1_waybel_0(sK0,sK1,X3))
      | ~ m1_subset_1(X4,u1_struct_0(sK1)) ) ),
    inference(subsumption_resolution,[],[f3318,f3252])).

fof(f3318,plain,(
    ! [X4,X3] :
      ( ~ r1_orders_2(sK1,sK4(X3),sK14(sK0,sK1,X3,X4))
      | ~ m1_subset_1(sK14(sK0,sK1,X3,X4),u1_struct_0(sK1))
      | ~ m1_subset_1(X3,u1_struct_0(sK1))
      | v11_waybel_0(sK1,sK0)
      | r1_waybel_0(sK0,sK1,a_3_1_waybel_0(sK0,sK1,X3))
      | ~ m1_subset_1(X4,u1_struct_0(sK1))
      | v2_struct_0(sK0) ) ),
    inference(subsumption_resolution,[],[f3317,f3253])).

fof(f3317,plain,(
    ! [X4,X3] :
      ( ~ r1_orders_2(sK1,sK4(X3),sK14(sK0,sK1,X3,X4))
      | ~ m1_subset_1(sK14(sK0,sK1,X3,X4),u1_struct_0(sK1))
      | ~ m1_subset_1(X3,u1_struct_0(sK1))
      | v11_waybel_0(sK1,sK0)
      | r1_waybel_0(sK0,sK1,a_3_1_waybel_0(sK0,sK1,X3))
      | ~ m1_subset_1(X4,u1_struct_0(sK1))
      | ~ l1_orders_2(sK0)
      | v2_struct_0(sK0) ) ),
    inference(subsumption_resolution,[],[f3316,f3254])).

fof(f3316,plain,(
    ! [X4,X3] :
      ( ~ r1_orders_2(sK1,sK4(X3),sK14(sK0,sK1,X3,X4))
      | ~ m1_subset_1(sK14(sK0,sK1,X3,X4),u1_struct_0(sK1))
      | ~ m1_subset_1(X3,u1_struct_0(sK1))
      | v11_waybel_0(sK1,sK0)
      | r1_waybel_0(sK0,sK1,a_3_1_waybel_0(sK0,sK1,X3))
      | ~ m1_subset_1(X4,u1_struct_0(sK1))
      | v2_struct_0(sK1)
      | ~ l1_orders_2(sK0)
      | v2_struct_0(sK0) ) ),
    inference(subsumption_resolution,[],[f3310,f3255])).

fof(f3310,plain,(
    ! [X4,X3] :
      ( ~ r1_orders_2(sK1,sK4(X3),sK14(sK0,sK1,X3,X4))
      | ~ m1_subset_1(sK14(sK0,sK1,X3,X4),u1_struct_0(sK1))
      | ~ m1_subset_1(X3,u1_struct_0(sK1))
      | v11_waybel_0(sK1,sK0)
      | r1_waybel_0(sK0,sK1,a_3_1_waybel_0(sK0,sK1,X3))
      | ~ m1_subset_1(X4,u1_struct_0(sK1))
      | ~ l1_waybel_0(sK1,sK0)
      | v2_struct_0(sK1)
      | ~ l1_orders_2(sK0)
      | v2_struct_0(sK0) ) ),
    inference(duplicate_literal_removal,[],[f3307])).

fof(f3307,plain,(
    ! [X4,X3] :
      ( ~ r1_orders_2(sK1,sK4(X3),sK14(sK0,sK1,X3,X4))
      | ~ m1_subset_1(sK14(sK0,sK1,X3,X4),u1_struct_0(sK1))
      | ~ m1_subset_1(X3,u1_struct_0(sK1))
      | v11_waybel_0(sK1,sK0)
      | r1_waybel_0(sK0,sK1,a_3_1_waybel_0(sK0,sK1,X3))
      | ~ m1_subset_1(X4,u1_struct_0(sK1))
      | ~ m1_subset_1(X3,u1_struct_0(sK1))
      | ~ l1_waybel_0(sK1,sK0)
      | v2_struct_0(sK1)
      | ~ l1_orders_2(sK0)
      | v2_struct_0(sK0) ) ),
    inference(resolution,[],[f3257,f3289])).

fof(f3289,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ r1_orders_2(X0,k2_waybel_0(X0,X1,sK14(X0,X1,X2,X3)),k2_waybel_0(X0,X1,X2))
      | r1_waybel_0(X0,X1,a_3_1_waybel_0(X0,X1,X2))
      | ~ m1_subset_1(X3,u1_struct_0(X1))
      | ~ m1_subset_1(X2,u1_struct_0(X1))
      | ~ l1_waybel_0(X1,X0)
      | v2_struct_0(X1)
      | ~ l1_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f3251])).

fof(f3257,plain,(
    ! [X7,X5] :
      ( r1_orders_2(sK0,k2_waybel_0(sK0,sK1,X7),k2_waybel_0(sK0,sK1,X5))
      | ~ r1_orders_2(sK1,sK4(X5),X7)
      | ~ m1_subset_1(X7,u1_struct_0(sK1))
      | ~ m1_subset_1(X5,u1_struct_0(sK1))
      | v11_waybel_0(sK1,sK0) ) ),
    inference(cnf_transformation,[],[f3223])).

fof(f3255,plain,(
    l1_waybel_0(sK1,sK0) ),
    inference(cnf_transformation,[],[f3223])).

fof(f3254,plain,(
    ~ v2_struct_0(sK1) ),
    inference(cnf_transformation,[],[f3223])).

fof(f3253,plain,(
    l1_orders_2(sK0) ),
    inference(cnf_transformation,[],[f3223])).

fof(f3252,plain,(
    ~ v2_struct_0(sK0) ),
    inference(cnf_transformation,[],[f3223])).

fof(f3467,plain,(
    ~ r1_waybel_0(sK0,sK1,a_3_1_waybel_0(sK0,sK1,sK2)) ),
    inference(unit_resulting_resolution,[],[f3252,f3253,f3254,f3255,f3444,f3448,f3285])).

fof(f3285,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_waybel_0(X0,X1,a_3_1_waybel_0(X0,X1,X2))
      | m1_subset_1(sK15(X0,X1,X2),u1_struct_0(X1))
      | ~ m1_subset_1(X2,u1_struct_0(X1))
      | ~ l1_waybel_0(X1,X0)
      | v2_struct_0(X1)
      | ~ l1_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f3251])).

fof(f3448,plain,(
    ~ m1_subset_1(sK15(sK0,sK1,sK2),u1_struct_0(sK1)) ),
    inference(unit_resulting_resolution,[],[f3439,f3376])).

fof(f3376,plain,
    ( ~ m1_subset_1(sK15(sK0,sK1,sK2),u1_struct_0(sK1))
    | ~ v11_waybel_0(sK1,sK0) ),
    inference(subsumption_resolution,[],[f3375,f3258])).

fof(f3375,plain,
    ( ~ m1_subset_1(sK15(sK0,sK1,sK2),u1_struct_0(sK1))
    | ~ v11_waybel_0(sK1,sK0)
    | ~ m1_subset_1(sK2,u1_struct_0(sK1)) ),
    inference(subsumption_resolution,[],[f3374,f3252])).

fof(f3374,plain,
    ( ~ m1_subset_1(sK15(sK0,sK1,sK2),u1_struct_0(sK1))
    | ~ v11_waybel_0(sK1,sK0)
    | ~ m1_subset_1(sK2,u1_struct_0(sK1))
    | v2_struct_0(sK0) ),
    inference(subsumption_resolution,[],[f3373,f3253])).

fof(f3373,plain,
    ( ~ m1_subset_1(sK15(sK0,sK1,sK2),u1_struct_0(sK1))
    | ~ v11_waybel_0(sK1,sK0)
    | ~ m1_subset_1(sK2,u1_struct_0(sK1))
    | ~ l1_orders_2(sK0)
    | v2_struct_0(sK0) ),
    inference(subsumption_resolution,[],[f3372,f3254])).

fof(f3372,plain,
    ( ~ m1_subset_1(sK15(sK0,sK1,sK2),u1_struct_0(sK1))
    | ~ v11_waybel_0(sK1,sK0)
    | ~ m1_subset_1(sK2,u1_struct_0(sK1))
    | v2_struct_0(sK1)
    | ~ l1_orders_2(sK0)
    | v2_struct_0(sK0) ),
    inference(subsumption_resolution,[],[f3371,f3255])).

fof(f3371,plain,
    ( ~ m1_subset_1(sK15(sK0,sK1,sK2),u1_struct_0(sK1))
    | ~ v11_waybel_0(sK1,sK0)
    | ~ m1_subset_1(sK2,u1_struct_0(sK1))
    | ~ l1_waybel_0(sK1,sK0)
    | v2_struct_0(sK1)
    | ~ l1_orders_2(sK0)
    | v2_struct_0(sK0) ),
    inference(duplicate_literal_removal,[],[f3370])).

fof(f3370,plain,
    ( ~ m1_subset_1(sK15(sK0,sK1,sK2),u1_struct_0(sK1))
    | ~ v11_waybel_0(sK1,sK0)
    | ~ m1_subset_1(sK2,u1_struct_0(sK1))
    | ~ v11_waybel_0(sK1,sK0)
    | ~ l1_waybel_0(sK1,sK0)
    | v2_struct_0(sK1)
    | ~ l1_orders_2(sK0)
    | v2_struct_0(sK0) ),
    inference(resolution,[],[f3337,f3264])).

fof(f3337,plain,
    ( ~ r1_waybel_0(sK0,sK1,a_3_1_waybel_0(sK0,sK1,sK2))
    | ~ m1_subset_1(sK15(sK0,sK1,sK2),u1_struct_0(sK1))
    | ~ v11_waybel_0(sK1,sK0) ),
    inference(duplicate_literal_removal,[],[f3336])).

fof(f3336,plain,
    ( ~ v11_waybel_0(sK1,sK0)
    | ~ m1_subset_1(sK15(sK0,sK1,sK2),u1_struct_0(sK1))
    | ~ r1_waybel_0(sK0,sK1,a_3_1_waybel_0(sK0,sK1,sK2))
    | ~ m1_subset_1(sK15(sK0,sK1,sK2),u1_struct_0(sK1))
    | ~ v11_waybel_0(sK1,sK0) ),
    inference(resolution,[],[f3304,f3260])).

fof(f3260,plain,(
    ! [X3] :
      ( r1_orders_2(sK1,X3,sK3(X3))
      | ~ m1_subset_1(X3,u1_struct_0(sK1))
      | ~ v11_waybel_0(sK1,sK0) ) ),
    inference(cnf_transformation,[],[f3223])).

fof(f3304,plain,(
    ! [X0] :
      ( ~ r1_orders_2(sK1,sK15(sK0,sK1,sK2),sK3(X0))
      | ~ v11_waybel_0(sK1,sK0)
      | ~ m1_subset_1(X0,u1_struct_0(sK1))
      | ~ r1_waybel_0(sK0,sK1,a_3_1_waybel_0(sK0,sK1,sK2)) ) ),
    inference(subsumption_resolution,[],[f3303,f3258])).

fof(f3303,plain,(
    ! [X0] :
      ( ~ m1_subset_1(X0,u1_struct_0(sK1))
      | ~ v11_waybel_0(sK1,sK0)
      | ~ r1_orders_2(sK1,sK15(sK0,sK1,sK2),sK3(X0))
      | ~ r1_waybel_0(sK0,sK1,a_3_1_waybel_0(sK0,sK1,sK2))
      | ~ m1_subset_1(sK2,u1_struct_0(sK1)) ) ),
    inference(subsumption_resolution,[],[f3302,f3259])).

fof(f3259,plain,(
    ! [X3] :
      ( m1_subset_1(sK3(X3),u1_struct_0(sK1))
      | ~ m1_subset_1(X3,u1_struct_0(sK1))
      | ~ v11_waybel_0(sK1,sK0) ) ),
    inference(cnf_transformation,[],[f3223])).

fof(f3302,plain,(
    ! [X0] :
      ( ~ m1_subset_1(X0,u1_struct_0(sK1))
      | ~ v11_waybel_0(sK1,sK0)
      | ~ r1_orders_2(sK1,sK15(sK0,sK1,sK2),sK3(X0))
      | ~ m1_subset_1(sK3(X0),u1_struct_0(sK1))
      | ~ r1_waybel_0(sK0,sK1,a_3_1_waybel_0(sK0,sK1,sK2))
      | ~ m1_subset_1(sK2,u1_struct_0(sK1)) ) ),
    inference(subsumption_resolution,[],[f3301,f3252])).

fof(f3301,plain,(
    ! [X0] :
      ( ~ m1_subset_1(X0,u1_struct_0(sK1))
      | ~ v11_waybel_0(sK1,sK0)
      | ~ r1_orders_2(sK1,sK15(sK0,sK1,sK2),sK3(X0))
      | ~ m1_subset_1(sK3(X0),u1_struct_0(sK1))
      | ~ r1_waybel_0(sK0,sK1,a_3_1_waybel_0(sK0,sK1,sK2))
      | ~ m1_subset_1(sK2,u1_struct_0(sK1))
      | v2_struct_0(sK0) ) ),
    inference(subsumption_resolution,[],[f3300,f3253])).

fof(f3300,plain,(
    ! [X0] :
      ( ~ m1_subset_1(X0,u1_struct_0(sK1))
      | ~ v11_waybel_0(sK1,sK0)
      | ~ r1_orders_2(sK1,sK15(sK0,sK1,sK2),sK3(X0))
      | ~ m1_subset_1(sK3(X0),u1_struct_0(sK1))
      | ~ r1_waybel_0(sK0,sK1,a_3_1_waybel_0(sK0,sK1,sK2))
      | ~ m1_subset_1(sK2,u1_struct_0(sK1))
      | ~ l1_orders_2(sK0)
      | v2_struct_0(sK0) ) ),
    inference(subsumption_resolution,[],[f3299,f3254])).

fof(f3299,plain,(
    ! [X0] :
      ( ~ m1_subset_1(X0,u1_struct_0(sK1))
      | ~ v11_waybel_0(sK1,sK0)
      | ~ r1_orders_2(sK1,sK15(sK0,sK1,sK2),sK3(X0))
      | ~ m1_subset_1(sK3(X0),u1_struct_0(sK1))
      | ~ r1_waybel_0(sK0,sK1,a_3_1_waybel_0(sK0,sK1,sK2))
      | ~ m1_subset_1(sK2,u1_struct_0(sK1))
      | v2_struct_0(sK1)
      | ~ l1_orders_2(sK0)
      | v2_struct_0(sK0) ) ),
    inference(subsumption_resolution,[],[f3298,f3255])).

fof(f3298,plain,(
    ! [X0] :
      ( ~ m1_subset_1(X0,u1_struct_0(sK1))
      | ~ v11_waybel_0(sK1,sK0)
      | ~ r1_orders_2(sK1,sK15(sK0,sK1,sK2),sK3(X0))
      | ~ m1_subset_1(sK3(X0),u1_struct_0(sK1))
      | ~ r1_waybel_0(sK0,sK1,a_3_1_waybel_0(sK0,sK1,sK2))
      | ~ m1_subset_1(sK2,u1_struct_0(sK1))
      | ~ l1_waybel_0(sK1,sK0)
      | v2_struct_0(sK1)
      | ~ l1_orders_2(sK0)
      | v2_struct_0(sK0) ) ),
    inference(resolution,[],[f3261,f3286])).

fof(f3286,plain,(
    ! [X6,X2,X0,X1] :
      ( r1_orders_2(X0,k2_waybel_0(X0,X1,X6),k2_waybel_0(X0,X1,X2))
      | ~ r1_orders_2(X1,sK15(X0,X1,X2),X6)
      | ~ m1_subset_1(X6,u1_struct_0(X1))
      | ~ r1_waybel_0(X0,X1,a_3_1_waybel_0(X0,X1,X2))
      | ~ m1_subset_1(X2,u1_struct_0(X1))
      | ~ l1_waybel_0(X1,X0)
      | v2_struct_0(X1)
      | ~ l1_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f3251])).

fof(f3261,plain,(
    ! [X3] :
      ( ~ r1_orders_2(sK0,k2_waybel_0(sK0,sK1,sK3(X3)),k2_waybel_0(sK0,sK1,sK2))
      | ~ m1_subset_1(X3,u1_struct_0(sK1))
      | ~ v11_waybel_0(sK1,sK0) ) ),
    inference(cnf_transformation,[],[f3223])).
%------------------------------------------------------------------------------
