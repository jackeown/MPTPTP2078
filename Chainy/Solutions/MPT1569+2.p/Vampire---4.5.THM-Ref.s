%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT1569+2 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n005.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Wed Dec 16 12:10:25 EST 2020

% Result     : Theorem 1.96s
% Output     : Refutation 1.96s
% Verified   : 
% Statistics : Number of formulae       :  100 (2095 expanded)
%              Number of leaves         :    9 ( 593 expanded)
%              Depth                    :   28
%              Number of atoms          :  493 (16115 expanded)
%              Number of equality atoms :   28 (1884 expanded)
%              Maximal formula depth    :   13 (   7 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f4426,plain,(
    $false ),
    inference(subsumption_resolution,[],[f4425,f4233])).

fof(f4233,plain,(
    m1_subset_1(sK7(sK1,sK2,sK3),u1_struct_0(sK1)) ),
    inference(resolution,[],[f4214,f3180])).

fof(f3180,plain,(
    ! [X0] :
      ( r1_yellow_0(sK1,X0)
      | m1_subset_1(sK7(sK1,sK2,X0),u1_struct_0(sK1)) ) ),
    inference(subsumption_resolution,[],[f3179,f3090])).

fof(f3090,plain,(
    ~ v2_struct_0(sK1) ),
    inference(cnf_transformation,[],[f3062])).

fof(f3062,plain,
    ( k1_yellow_0(sK1,sK2) != k1_yellow_0(sK1,sK3)
    & ! [X3] :
        ( ( ( r2_lattice3(sK1,sK2,X3)
            | ~ r2_lattice3(sK1,sK3,X3) )
          & ( r2_lattice3(sK1,sK3,X3)
            | ~ r2_lattice3(sK1,sK2,X3) ) )
        | ~ m1_subset_1(X3,u1_struct_0(sK1)) )
    & r1_yellow_0(sK1,sK2)
    & l1_orders_2(sK1)
    & ~ v2_struct_0(sK1) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1,sK2,sK3])],[f3059,f3061,f3060])).

fof(f3060,plain,
    ( ? [X0] :
        ( ? [X1,X2] :
            ( k1_yellow_0(X0,X1) != k1_yellow_0(X0,X2)
            & ! [X3] :
                ( ( ( r2_lattice3(X0,X1,X3)
                    | ~ r2_lattice3(X0,X2,X3) )
                  & ( r2_lattice3(X0,X2,X3)
                    | ~ r2_lattice3(X0,X1,X3) ) )
                | ~ m1_subset_1(X3,u1_struct_0(X0)) )
            & r1_yellow_0(X0,X1) )
        & l1_orders_2(X0)
        & ~ v2_struct_0(X0) )
   => ( ? [X2,X1] :
          ( k1_yellow_0(sK1,X1) != k1_yellow_0(sK1,X2)
          & ! [X3] :
              ( ( ( r2_lattice3(sK1,X1,X3)
                  | ~ r2_lattice3(sK1,X2,X3) )
                & ( r2_lattice3(sK1,X2,X3)
                  | ~ r2_lattice3(sK1,X1,X3) ) )
              | ~ m1_subset_1(X3,u1_struct_0(sK1)) )
          & r1_yellow_0(sK1,X1) )
      & l1_orders_2(sK1)
      & ~ v2_struct_0(sK1) ) ),
    introduced(choice_axiom,[])).

fof(f3061,plain,
    ( ? [X2,X1] :
        ( k1_yellow_0(sK1,X1) != k1_yellow_0(sK1,X2)
        & ! [X3] :
            ( ( ( r2_lattice3(sK1,X1,X3)
                | ~ r2_lattice3(sK1,X2,X3) )
              & ( r2_lattice3(sK1,X2,X3)
                | ~ r2_lattice3(sK1,X1,X3) ) )
            | ~ m1_subset_1(X3,u1_struct_0(sK1)) )
        & r1_yellow_0(sK1,X1) )
   => ( k1_yellow_0(sK1,sK2) != k1_yellow_0(sK1,sK3)
      & ! [X3] :
          ( ( ( r2_lattice3(sK1,sK2,X3)
              | ~ r2_lattice3(sK1,sK3,X3) )
            & ( r2_lattice3(sK1,sK3,X3)
              | ~ r2_lattice3(sK1,sK2,X3) ) )
          | ~ m1_subset_1(X3,u1_struct_0(sK1)) )
      & r1_yellow_0(sK1,sK2) ) ),
    introduced(choice_axiom,[])).

fof(f3059,plain,(
    ? [X0] :
      ( ? [X1,X2] :
          ( k1_yellow_0(X0,X1) != k1_yellow_0(X0,X2)
          & ! [X3] :
              ( ( ( r2_lattice3(X0,X1,X3)
                  | ~ r2_lattice3(X0,X2,X3) )
                & ( r2_lattice3(X0,X2,X3)
                  | ~ r2_lattice3(X0,X1,X3) ) )
              | ~ m1_subset_1(X3,u1_struct_0(X0)) )
          & r1_yellow_0(X0,X1) )
      & l1_orders_2(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(nnf_transformation,[],[f3045])).

fof(f3045,plain,(
    ? [X0] :
      ( ? [X1,X2] :
          ( k1_yellow_0(X0,X1) != k1_yellow_0(X0,X2)
          & ! [X3] :
              ( ( r2_lattice3(X0,X1,X3)
              <=> r2_lattice3(X0,X2,X3) )
              | ~ m1_subset_1(X3,u1_struct_0(X0)) )
          & r1_yellow_0(X0,X1) )
      & l1_orders_2(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(flattening,[],[f3044])).

fof(f3044,plain,(
    ? [X0] :
      ( ? [X1,X2] :
          ( k1_yellow_0(X0,X1) != k1_yellow_0(X0,X2)
          & ! [X3] :
              ( ( r2_lattice3(X0,X1,X3)
              <=> r2_lattice3(X0,X2,X3) )
              | ~ m1_subset_1(X3,u1_struct_0(X0)) )
          & r1_yellow_0(X0,X1) )
      & l1_orders_2(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f3029])).

fof(f3029,negated_conjecture,(
    ~ ! [X0] :
        ( ( l1_orders_2(X0)
          & ~ v2_struct_0(X0) )
       => ! [X1,X2] :
            ( ( ! [X3] :
                  ( m1_subset_1(X3,u1_struct_0(X0))
                 => ( r2_lattice3(X0,X1,X3)
                  <=> r2_lattice3(X0,X2,X3) ) )
              & r1_yellow_0(X0,X1) )
           => k1_yellow_0(X0,X1) = k1_yellow_0(X0,X2) ) ) ),
    inference(negated_conjecture,[],[f3028])).

fof(f3028,conjecture,(
    ! [X0] :
      ( ( l1_orders_2(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1,X2] :
          ( ( ! [X3] :
                ( m1_subset_1(X3,u1_struct_0(X0))
               => ( r2_lattice3(X0,X1,X3)
                <=> r2_lattice3(X0,X2,X3) ) )
            & r1_yellow_0(X0,X1) )
         => k1_yellow_0(X0,X1) = k1_yellow_0(X0,X2) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t47_yellow_0)).

fof(f3179,plain,(
    ! [X0] :
      ( r1_yellow_0(sK1,X0)
      | m1_subset_1(sK7(sK1,sK2,X0),u1_struct_0(sK1))
      | v2_struct_0(sK1) ) ),
    inference(subsumption_resolution,[],[f3167,f3091])).

fof(f3091,plain,(
    l1_orders_2(sK1) ),
    inference(cnf_transformation,[],[f3062])).

fof(f3167,plain,(
    ! [X0] :
      ( r1_yellow_0(sK1,X0)
      | m1_subset_1(sK7(sK1,sK2,X0),u1_struct_0(sK1))
      | ~ l1_orders_2(sK1)
      | v2_struct_0(sK1) ) ),
    inference(resolution,[],[f3092,f3108])).

fof(f3108,plain,(
    ! [X2,X0,X1] :
      ( r1_yellow_0(X0,X2)
      | ~ r1_yellow_0(X0,X1)
      | m1_subset_1(sK7(X0,X1,X2),u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f3077])).

fof(f3077,plain,(
    ! [X0] :
      ( ! [X1,X2] :
          ( r1_yellow_0(X0,X2)
          | ~ r1_yellow_0(X0,X1)
          | ( ( ~ r2_lattice3(X0,X2,sK7(X0,X1,X2))
              | ~ r2_lattice3(X0,X1,sK7(X0,X1,X2)) )
            & ( r2_lattice3(X0,X2,sK7(X0,X1,X2))
              | r2_lattice3(X0,X1,sK7(X0,X1,X2)) )
            & m1_subset_1(sK7(X0,X1,X2),u1_struct_0(X0)) ) )
      | ~ l1_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK7])],[f3075,f3076])).

fof(f3076,plain,(
    ! [X2,X1,X0] :
      ( ? [X3] :
          ( ( ~ r2_lattice3(X0,X2,X3)
            | ~ r2_lattice3(X0,X1,X3) )
          & ( r2_lattice3(X0,X2,X3)
            | r2_lattice3(X0,X1,X3) )
          & m1_subset_1(X3,u1_struct_0(X0)) )
     => ( ( ~ r2_lattice3(X0,X2,sK7(X0,X1,X2))
          | ~ r2_lattice3(X0,X1,sK7(X0,X1,X2)) )
        & ( r2_lattice3(X0,X2,sK7(X0,X1,X2))
          | r2_lattice3(X0,X1,sK7(X0,X1,X2)) )
        & m1_subset_1(sK7(X0,X1,X2),u1_struct_0(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f3075,plain,(
    ! [X0] :
      ( ! [X1,X2] :
          ( r1_yellow_0(X0,X2)
          | ~ r1_yellow_0(X0,X1)
          | ? [X3] :
              ( ( ~ r2_lattice3(X0,X2,X3)
                | ~ r2_lattice3(X0,X1,X3) )
              & ( r2_lattice3(X0,X2,X3)
                | r2_lattice3(X0,X1,X3) )
              & m1_subset_1(X3,u1_struct_0(X0)) ) )
      | ~ l1_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f3074])).

fof(f3074,plain,(
    ! [X0] :
      ( ! [X1,X2] :
          ( r1_yellow_0(X0,X2)
          | ~ r1_yellow_0(X0,X1)
          | ? [X3] :
              ( ( ~ r2_lattice3(X0,X2,X3)
                | ~ r2_lattice3(X0,X1,X3) )
              & ( r2_lattice3(X0,X2,X3)
                | r2_lattice3(X0,X1,X3) )
              & m1_subset_1(X3,u1_struct_0(X0)) ) )
      | ~ l1_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(nnf_transformation,[],[f3054])).

fof(f3054,plain,(
    ! [X0] :
      ( ! [X1,X2] :
          ( r1_yellow_0(X0,X2)
          | ~ r1_yellow_0(X0,X1)
          | ? [X3] :
              ( ( r2_lattice3(X0,X1,X3)
              <~> r2_lattice3(X0,X2,X3) )
              & m1_subset_1(X3,u1_struct_0(X0)) ) )
      | ~ l1_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f3053])).

fof(f3053,plain,(
    ! [X0] :
      ( ! [X1,X2] :
          ( r1_yellow_0(X0,X2)
          | ~ r1_yellow_0(X0,X1)
          | ? [X3] :
              ( ( r2_lattice3(X0,X1,X3)
              <~> r2_lattice3(X0,X2,X3) )
              & m1_subset_1(X3,u1_struct_0(X0)) ) )
      | ~ l1_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f3027])).

fof(f3027,axiom,(
    ! [X0] :
      ( ( l1_orders_2(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1,X2] :
          ( ( r1_yellow_0(X0,X1)
            & ! [X3] :
                ( m1_subset_1(X3,u1_struct_0(X0))
               => ( r2_lattice3(X0,X1,X3)
                <=> r2_lattice3(X0,X2,X3) ) ) )
         => r1_yellow_0(X0,X2) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t46_yellow_0)).

fof(f3092,plain,(
    r1_yellow_0(sK1,sK2) ),
    inference(cnf_transformation,[],[f3062])).

fof(f4214,plain,(
    ~ r1_yellow_0(sK1,sK3) ),
    inference(subsumption_resolution,[],[f4213,f3166])).

fof(f3166,plain,(
    ! [X29] :
      ( ~ r1_yellow_0(sK1,X29)
      | r2_lattice3(sK1,X29,k1_yellow_0(sK1,X29)) ) ),
    inference(subsumption_resolution,[],[f3161,f3145])).

fof(f3145,plain,(
    ! [X0] : m1_subset_1(k1_yellow_0(sK1,X0),u1_struct_0(sK1)) ),
    inference(resolution,[],[f3091,f3096])).

fof(f3096,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k1_yellow_0(X0,X1),u1_struct_0(X0))
      | ~ l1_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f3046])).

fof(f3046,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k1_yellow_0(X0,X1),u1_struct_0(X0))
      | ~ l1_orders_2(X0) ) ),
    inference(ennf_transformation,[],[f2978])).

fof(f2978,axiom,(
    ! [X0,X1] :
      ( l1_orders_2(X0)
     => m1_subset_1(k1_yellow_0(X0,X1),u1_struct_0(X0)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k1_yellow_0)).

fof(f3161,plain,(
    ! [X29] :
      ( r2_lattice3(sK1,X29,k1_yellow_0(sK1,X29))
      | ~ r1_yellow_0(sK1,X29)
      | ~ m1_subset_1(k1_yellow_0(sK1,X29),u1_struct_0(sK1)) ) ),
    inference(resolution,[],[f3091,f3127])).

fof(f3127,plain,(
    ! [X0,X1] :
      ( r2_lattice3(X0,X1,k1_yellow_0(X0,X1))
      | ~ r1_yellow_0(X0,X1)
      | ~ m1_subset_1(k1_yellow_0(X0,X1),u1_struct_0(X0))
      | ~ l1_orders_2(X0) ) ),
    inference(equality_resolution,[],[f3097])).

fof(f3097,plain,(
    ! [X2,X0,X1] :
      ( r2_lattice3(X0,X1,X2)
      | k1_yellow_0(X0,X1) != X2
      | ~ r1_yellow_0(X0,X1)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ l1_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f3067])).

fof(f3067,plain,(
    ! [X0] :
      ( ! [X1,X2] :
          ( ( ( k1_yellow_0(X0,X1) = X2
              | ( ~ r1_orders_2(X0,X2,sK4(X0,X1,X2))
                & r2_lattice3(X0,X1,sK4(X0,X1,X2))
                & m1_subset_1(sK4(X0,X1,X2),u1_struct_0(X0)) )
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
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4])],[f3065,f3066])).

fof(f3066,plain,(
    ! [X2,X1,X0] :
      ( ? [X3] :
          ( ~ r1_orders_2(X0,X2,X3)
          & r2_lattice3(X0,X1,X3)
          & m1_subset_1(X3,u1_struct_0(X0)) )
     => ( ~ r1_orders_2(X0,X2,sK4(X0,X1,X2))
        & r2_lattice3(X0,X1,sK4(X0,X1,X2))
        & m1_subset_1(sK4(X0,X1,X2),u1_struct_0(X0)) ) ) ),
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
    inference(nnf_transformation,[],[f3048])).

fof(f3048,plain,(
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
    inference(flattening,[],[f3047])).

fof(f3047,plain,(
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
    inference(ennf_transformation,[],[f2976])).

fof(f2976,axiom,(
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

fof(f4213,plain,
    ( ~ r1_yellow_0(sK1,sK3)
    | ~ r2_lattice3(sK1,sK3,k1_yellow_0(sK1,sK3)) ),
    inference(subsumption_resolution,[],[f4207,f3145])).

fof(f4207,plain,
    ( ~ r1_yellow_0(sK1,sK3)
    | ~ r2_lattice3(sK1,sK3,k1_yellow_0(sK1,sK3))
    | ~ m1_subset_1(k1_yellow_0(sK1,sK3),u1_struct_0(sK1)) ),
    inference(resolution,[],[f4195,f3094])).

fof(f3094,plain,(
    ! [X3] :
      ( r2_lattice3(sK1,sK2,X3)
      | ~ r2_lattice3(sK1,sK3,X3)
      | ~ m1_subset_1(X3,u1_struct_0(sK1)) ) ),
    inference(cnf_transformation,[],[f3062])).

fof(f4195,plain,
    ( ~ r2_lattice3(sK1,sK2,k1_yellow_0(sK1,sK3))
    | ~ r1_yellow_0(sK1,sK3) ),
    inference(subsumption_resolution,[],[f4194,f3243])).

fof(f3243,plain,
    ( ~ r1_orders_2(sK1,k1_yellow_0(sK1,sK3),sK4(sK1,sK2,k1_yellow_0(sK1,sK3)))
    | ~ r2_lattice3(sK1,sK2,k1_yellow_0(sK1,sK3)) ),
    inference(subsumption_resolution,[],[f3242,f3091])).

fof(f3242,plain,
    ( ~ r1_orders_2(sK1,k1_yellow_0(sK1,sK3),sK4(sK1,sK2,k1_yellow_0(sK1,sK3)))
    | ~ r2_lattice3(sK1,sK2,k1_yellow_0(sK1,sK3))
    | ~ l1_orders_2(sK1) ),
    inference(subsumption_resolution,[],[f3241,f3145])).

fof(f3241,plain,
    ( ~ r1_orders_2(sK1,k1_yellow_0(sK1,sK3),sK4(sK1,sK2,k1_yellow_0(sK1,sK3)))
    | ~ r2_lattice3(sK1,sK2,k1_yellow_0(sK1,sK3))
    | ~ m1_subset_1(k1_yellow_0(sK1,sK3),u1_struct_0(sK1))
    | ~ l1_orders_2(sK1) ),
    inference(subsumption_resolution,[],[f3231,f3092])).

fof(f3231,plain,
    ( ~ r1_orders_2(sK1,k1_yellow_0(sK1,sK3),sK4(sK1,sK2,k1_yellow_0(sK1,sK3)))
    | ~ r2_lattice3(sK1,sK2,k1_yellow_0(sK1,sK3))
    | ~ r1_yellow_0(sK1,sK2)
    | ~ m1_subset_1(k1_yellow_0(sK1,sK3),u1_struct_0(sK1))
    | ~ l1_orders_2(sK1) ),
    inference(resolution,[],[f3129,f3130])).

fof(f3130,plain,(
    ! [X2,X0,X1] :
      ( sQ13_eqProxy(k1_yellow_0(X0,X1),X2)
      | ~ r1_orders_2(X0,X2,sK4(X0,X1,X2))
      | ~ r2_lattice3(X0,X1,X2)
      | ~ r1_yellow_0(X0,X1)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ l1_orders_2(X0) ) ),
    inference(equality_proxy_replacement,[],[f3101,f3128])).

fof(f3128,plain,(
    ! [X1,X0] :
      ( sQ13_eqProxy(X0,X1)
    <=> X0 = X1 ) ),
    introduced(equality_proxy_definition,[new_symbols(naming,[sQ13_eqProxy])])).

fof(f3101,plain,(
    ! [X2,X0,X1] :
      ( k1_yellow_0(X0,X1) = X2
      | ~ r1_orders_2(X0,X2,sK4(X0,X1,X2))
      | ~ r2_lattice3(X0,X1,X2)
      | ~ r1_yellow_0(X0,X1)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ l1_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f3067])).

fof(f3129,plain,(
    ~ sQ13_eqProxy(k1_yellow_0(sK1,sK2),k1_yellow_0(sK1,sK3)) ),
    inference(equality_proxy_replacement,[],[f3095,f3128])).

fof(f3095,plain,(
    k1_yellow_0(sK1,sK2) != k1_yellow_0(sK1,sK3) ),
    inference(cnf_transformation,[],[f3062])).

fof(f4194,plain,
    ( r1_orders_2(sK1,k1_yellow_0(sK1,sK3),sK4(sK1,sK2,k1_yellow_0(sK1,sK3)))
    | ~ r1_yellow_0(sK1,sK3)
    | ~ r2_lattice3(sK1,sK2,k1_yellow_0(sK1,sK3)) ),
    inference(subsumption_resolution,[],[f4171,f3237])).

fof(f3237,plain,
    ( ~ r2_lattice3(sK1,sK2,k1_yellow_0(sK1,sK3))
    | m1_subset_1(sK4(sK1,sK2,k1_yellow_0(sK1,sK3)),u1_struct_0(sK1)) ),
    inference(subsumption_resolution,[],[f3236,f3091])).

fof(f3236,plain,
    ( m1_subset_1(sK4(sK1,sK2,k1_yellow_0(sK1,sK3)),u1_struct_0(sK1))
    | ~ r2_lattice3(sK1,sK2,k1_yellow_0(sK1,sK3))
    | ~ l1_orders_2(sK1) ),
    inference(subsumption_resolution,[],[f3235,f3145])).

fof(f3235,plain,
    ( m1_subset_1(sK4(sK1,sK2,k1_yellow_0(sK1,sK3)),u1_struct_0(sK1))
    | ~ r2_lattice3(sK1,sK2,k1_yellow_0(sK1,sK3))
    | ~ m1_subset_1(k1_yellow_0(sK1,sK3),u1_struct_0(sK1))
    | ~ l1_orders_2(sK1) ),
    inference(subsumption_resolution,[],[f3229,f3092])).

fof(f3229,plain,
    ( m1_subset_1(sK4(sK1,sK2,k1_yellow_0(sK1,sK3)),u1_struct_0(sK1))
    | ~ r2_lattice3(sK1,sK2,k1_yellow_0(sK1,sK3))
    | ~ r1_yellow_0(sK1,sK2)
    | ~ m1_subset_1(k1_yellow_0(sK1,sK3),u1_struct_0(sK1))
    | ~ l1_orders_2(sK1) ),
    inference(resolution,[],[f3129,f3132])).

fof(f3132,plain,(
    ! [X2,X0,X1] :
      ( sQ13_eqProxy(k1_yellow_0(X0,X1),X2)
      | m1_subset_1(sK4(X0,X1,X2),u1_struct_0(X0))
      | ~ r2_lattice3(X0,X1,X2)
      | ~ r1_yellow_0(X0,X1)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ l1_orders_2(X0) ) ),
    inference(equality_proxy_replacement,[],[f3099,f3128])).

fof(f3099,plain,(
    ! [X2,X0,X1] :
      ( k1_yellow_0(X0,X1) = X2
      | m1_subset_1(sK4(X0,X1,X2),u1_struct_0(X0))
      | ~ r2_lattice3(X0,X1,X2)
      | ~ r1_yellow_0(X0,X1)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ l1_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f3067])).

fof(f4171,plain,
    ( ~ m1_subset_1(sK4(sK1,sK2,k1_yellow_0(sK1,sK3)),u1_struct_0(sK1))
    | r1_orders_2(sK1,k1_yellow_0(sK1,sK3),sK4(sK1,sK2,k1_yellow_0(sK1,sK3)))
    | ~ r1_yellow_0(sK1,sK3)
    | ~ r2_lattice3(sK1,sK2,k1_yellow_0(sK1,sK3)) ),
    inference(resolution,[],[f3309,f3240])).

fof(f3240,plain,
    ( r2_lattice3(sK1,sK2,sK4(sK1,sK2,k1_yellow_0(sK1,sK3)))
    | ~ r2_lattice3(sK1,sK2,k1_yellow_0(sK1,sK3)) ),
    inference(subsumption_resolution,[],[f3239,f3091])).

fof(f3239,plain,
    ( r2_lattice3(sK1,sK2,sK4(sK1,sK2,k1_yellow_0(sK1,sK3)))
    | ~ r2_lattice3(sK1,sK2,k1_yellow_0(sK1,sK3))
    | ~ l1_orders_2(sK1) ),
    inference(subsumption_resolution,[],[f3238,f3145])).

fof(f3238,plain,
    ( r2_lattice3(sK1,sK2,sK4(sK1,sK2,k1_yellow_0(sK1,sK3)))
    | ~ r2_lattice3(sK1,sK2,k1_yellow_0(sK1,sK3))
    | ~ m1_subset_1(k1_yellow_0(sK1,sK3),u1_struct_0(sK1))
    | ~ l1_orders_2(sK1) ),
    inference(subsumption_resolution,[],[f3230,f3092])).

fof(f3230,plain,
    ( r2_lattice3(sK1,sK2,sK4(sK1,sK2,k1_yellow_0(sK1,sK3)))
    | ~ r2_lattice3(sK1,sK2,k1_yellow_0(sK1,sK3))
    | ~ r1_yellow_0(sK1,sK2)
    | ~ m1_subset_1(k1_yellow_0(sK1,sK3),u1_struct_0(sK1))
    | ~ l1_orders_2(sK1) ),
    inference(resolution,[],[f3129,f3131])).

fof(f3131,plain,(
    ! [X2,X0,X1] :
      ( sQ13_eqProxy(k1_yellow_0(X0,X1),X2)
      | r2_lattice3(X0,X1,sK4(X0,X1,X2))
      | ~ r2_lattice3(X0,X1,X2)
      | ~ r1_yellow_0(X0,X1)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ l1_orders_2(X0) ) ),
    inference(equality_proxy_replacement,[],[f3100,f3128])).

fof(f3100,plain,(
    ! [X2,X0,X1] :
      ( k1_yellow_0(X0,X1) = X2
      | r2_lattice3(X0,X1,sK4(X0,X1,X2))
      | ~ r2_lattice3(X0,X1,X2)
      | ~ r1_yellow_0(X0,X1)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ l1_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f3067])).

fof(f3309,plain,(
    ! [X8] :
      ( ~ r2_lattice3(sK1,sK2,X8)
      | ~ m1_subset_1(X8,u1_struct_0(sK1))
      | r1_orders_2(sK1,k1_yellow_0(sK1,sK3),X8)
      | ~ r1_yellow_0(sK1,sK3) ) ),
    inference(subsumption_resolution,[],[f3308,f3091])).

fof(f3308,plain,(
    ! [X8] :
      ( ~ r2_lattice3(sK1,sK2,X8)
      | ~ m1_subset_1(X8,u1_struct_0(sK1))
      | r1_orders_2(sK1,k1_yellow_0(sK1,sK3),X8)
      | ~ r1_yellow_0(sK1,sK3)
      | ~ l1_orders_2(sK1) ) ),
    inference(subsumption_resolution,[],[f3296,f3145])).

fof(f3296,plain,(
    ! [X8] :
      ( ~ r2_lattice3(sK1,sK2,X8)
      | ~ m1_subset_1(X8,u1_struct_0(sK1))
      | r1_orders_2(sK1,k1_yellow_0(sK1,sK3),X8)
      | ~ r1_yellow_0(sK1,sK3)
      | ~ m1_subset_1(k1_yellow_0(sK1,sK3),u1_struct_0(sK1))
      | ~ l1_orders_2(sK1) ) ),
    inference(duplicate_literal_removal,[],[f3281])).

fof(f3281,plain,(
    ! [X8] :
      ( ~ r2_lattice3(sK1,sK2,X8)
      | ~ m1_subset_1(X8,u1_struct_0(sK1))
      | r1_orders_2(sK1,k1_yellow_0(sK1,sK3),X8)
      | ~ m1_subset_1(X8,u1_struct_0(sK1))
      | ~ r1_yellow_0(sK1,sK3)
      | ~ m1_subset_1(k1_yellow_0(sK1,sK3),u1_struct_0(sK1))
      | ~ l1_orders_2(sK1) ) ),
    inference(resolution,[],[f3093,f3126])).

fof(f3126,plain,(
    ! [X4,X0,X1] :
      ( r1_orders_2(X0,k1_yellow_0(X0,X1),X4)
      | ~ r2_lattice3(X0,X1,X4)
      | ~ m1_subset_1(X4,u1_struct_0(X0))
      | ~ r1_yellow_0(X0,X1)
      | ~ m1_subset_1(k1_yellow_0(X0,X1),u1_struct_0(X0))
      | ~ l1_orders_2(X0) ) ),
    inference(equality_resolution,[],[f3098])).

fof(f3098,plain,(
    ! [X4,X2,X0,X1] :
      ( r1_orders_2(X0,X2,X4)
      | ~ r2_lattice3(X0,X1,X4)
      | ~ m1_subset_1(X4,u1_struct_0(X0))
      | k1_yellow_0(X0,X1) != X2
      | ~ r1_yellow_0(X0,X1)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ l1_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f3067])).

fof(f3093,plain,(
    ! [X3] :
      ( r2_lattice3(sK1,sK3,X3)
      | ~ r2_lattice3(sK1,sK2,X3)
      | ~ m1_subset_1(X3,u1_struct_0(sK1)) ) ),
    inference(cnf_transformation,[],[f3062])).

fof(f4425,plain,(
    ~ m1_subset_1(sK7(sK1,sK2,sK3),u1_struct_0(sK1)) ),
    inference(subsumption_resolution,[],[f4418,f4240])).

fof(f4240,plain,(
    r2_lattice3(sK1,sK2,sK7(sK1,sK2,sK3)) ),
    inference(subsumption_resolution,[],[f4231,f4228])).

fof(f4228,plain,
    ( ~ r2_lattice3(sK1,sK3,sK7(sK1,sK2,sK3))
    | r2_lattice3(sK1,sK2,sK7(sK1,sK2,sK3)) ),
    inference(subsumption_resolution,[],[f4227,f3090])).

fof(f4227,plain,
    ( ~ r2_lattice3(sK1,sK3,sK7(sK1,sK2,sK3))
    | r2_lattice3(sK1,sK2,sK7(sK1,sK2,sK3))
    | v2_struct_0(sK1) ),
    inference(subsumption_resolution,[],[f4226,f3091])).

fof(f4226,plain,
    ( ~ r2_lattice3(sK1,sK3,sK7(sK1,sK2,sK3))
    | r2_lattice3(sK1,sK2,sK7(sK1,sK2,sK3))
    | ~ l1_orders_2(sK1)
    | v2_struct_0(sK1) ),
    inference(subsumption_resolution,[],[f4225,f3092])).

fof(f4225,plain,
    ( ~ r2_lattice3(sK1,sK3,sK7(sK1,sK2,sK3))
    | ~ r1_yellow_0(sK1,sK2)
    | r2_lattice3(sK1,sK2,sK7(sK1,sK2,sK3))
    | ~ l1_orders_2(sK1)
    | v2_struct_0(sK1) ),
    inference(subsumption_resolution,[],[f4222,f4214])).

fof(f4222,plain,
    ( r1_yellow_0(sK1,sK3)
    | ~ r2_lattice3(sK1,sK3,sK7(sK1,sK2,sK3))
    | ~ r1_yellow_0(sK1,sK2)
    | r2_lattice3(sK1,sK2,sK7(sK1,sK2,sK3))
    | ~ l1_orders_2(sK1)
    | v2_struct_0(sK1) ),
    inference(duplicate_literal_removal,[],[f4218])).

fof(f4218,plain,
    ( r1_yellow_0(sK1,sK3)
    | ~ r2_lattice3(sK1,sK3,sK7(sK1,sK2,sK3))
    | r1_yellow_0(sK1,sK3)
    | ~ r1_yellow_0(sK1,sK2)
    | r2_lattice3(sK1,sK2,sK7(sK1,sK2,sK3))
    | ~ l1_orders_2(sK1)
    | v2_struct_0(sK1) ),
    inference(resolution,[],[f3397,f3109])).

fof(f3109,plain,(
    ! [X2,X0,X1] :
      ( r1_yellow_0(X0,X2)
      | ~ r1_yellow_0(X0,X1)
      | r2_lattice3(X0,X2,sK7(X0,X1,X2))
      | r2_lattice3(X0,X1,sK7(X0,X1,X2))
      | ~ l1_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f3077])).

fof(f3397,plain,(
    ! [X19] :
      ( ~ r2_lattice3(sK1,sK3,sK7(sK1,sK2,X19))
      | r1_yellow_0(sK1,X19)
      | ~ r2_lattice3(sK1,X19,sK7(sK1,sK2,X19)) ) ),
    inference(subsumption_resolution,[],[f3396,f3180])).

fof(f3396,plain,(
    ! [X19] :
      ( ~ r2_lattice3(sK1,sK3,sK7(sK1,sK2,X19))
      | ~ m1_subset_1(sK7(sK1,sK2,X19),u1_struct_0(sK1))
      | r1_yellow_0(sK1,X19)
      | ~ r2_lattice3(sK1,X19,sK7(sK1,sK2,X19)) ) ),
    inference(subsumption_resolution,[],[f3395,f3090])).

fof(f3395,plain,(
    ! [X19] :
      ( ~ r2_lattice3(sK1,sK3,sK7(sK1,sK2,X19))
      | ~ m1_subset_1(sK7(sK1,sK2,X19),u1_struct_0(sK1))
      | r1_yellow_0(sK1,X19)
      | ~ r2_lattice3(sK1,X19,sK7(sK1,sK2,X19))
      | v2_struct_0(sK1) ) ),
    inference(subsumption_resolution,[],[f3394,f3091])).

fof(f3394,plain,(
    ! [X19] :
      ( ~ r2_lattice3(sK1,sK3,sK7(sK1,sK2,X19))
      | ~ m1_subset_1(sK7(sK1,sK2,X19),u1_struct_0(sK1))
      | r1_yellow_0(sK1,X19)
      | ~ r2_lattice3(sK1,X19,sK7(sK1,sK2,X19))
      | ~ l1_orders_2(sK1)
      | v2_struct_0(sK1) ) ),
    inference(subsumption_resolution,[],[f3368,f3092])).

fof(f3368,plain,(
    ! [X19] :
      ( ~ r2_lattice3(sK1,sK3,sK7(sK1,sK2,X19))
      | ~ m1_subset_1(sK7(sK1,sK2,X19),u1_struct_0(sK1))
      | r1_yellow_0(sK1,X19)
      | ~ r1_yellow_0(sK1,sK2)
      | ~ r2_lattice3(sK1,X19,sK7(sK1,sK2,X19))
      | ~ l1_orders_2(sK1)
      | v2_struct_0(sK1) ) ),
    inference(resolution,[],[f3094,f3110])).

fof(f3110,plain,(
    ! [X2,X0,X1] :
      ( r1_yellow_0(X0,X2)
      | ~ r1_yellow_0(X0,X1)
      | ~ r2_lattice3(X0,X2,sK7(X0,X1,X2))
      | ~ r2_lattice3(X0,X1,sK7(X0,X1,X2))
      | ~ l1_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f3077])).

fof(f4231,plain,
    ( r2_lattice3(sK1,sK3,sK7(sK1,sK2,sK3))
    | r2_lattice3(sK1,sK2,sK7(sK1,sK2,sK3)) ),
    inference(resolution,[],[f4214,f3182])).

fof(f3182,plain,(
    ! [X1] :
      ( r1_yellow_0(sK1,X1)
      | r2_lattice3(sK1,X1,sK7(sK1,sK2,X1))
      | r2_lattice3(sK1,sK2,sK7(sK1,sK2,X1)) ) ),
    inference(subsumption_resolution,[],[f3181,f3090])).

fof(f3181,plain,(
    ! [X1] :
      ( r1_yellow_0(sK1,X1)
      | r2_lattice3(sK1,X1,sK7(sK1,sK2,X1))
      | r2_lattice3(sK1,sK2,sK7(sK1,sK2,X1))
      | v2_struct_0(sK1) ) ),
    inference(subsumption_resolution,[],[f3168,f3091])).

fof(f3168,plain,(
    ! [X1] :
      ( r1_yellow_0(sK1,X1)
      | r2_lattice3(sK1,X1,sK7(sK1,sK2,X1))
      | r2_lattice3(sK1,sK2,sK7(sK1,sK2,X1))
      | ~ l1_orders_2(sK1)
      | v2_struct_0(sK1) ) ),
    inference(resolution,[],[f3092,f3109])).

fof(f4418,plain,
    ( ~ r2_lattice3(sK1,sK2,sK7(sK1,sK2,sK3))
    | ~ m1_subset_1(sK7(sK1,sK2,sK3),u1_struct_0(sK1)) ),
    inference(resolution,[],[f4394,f3093])).

fof(f4394,plain,(
    ~ r2_lattice3(sK1,sK3,sK7(sK1,sK2,sK3)) ),
    inference(subsumption_resolution,[],[f4371,f4214])).

fof(f4371,plain,
    ( ~ r2_lattice3(sK1,sK3,sK7(sK1,sK2,sK3))
    | r1_yellow_0(sK1,sK3) ),
    inference(resolution,[],[f4240,f3184])).

fof(f3184,plain,(
    ! [X2] :
      ( ~ r2_lattice3(sK1,sK2,sK7(sK1,sK2,X2))
      | ~ r2_lattice3(sK1,X2,sK7(sK1,sK2,X2))
      | r1_yellow_0(sK1,X2) ) ),
    inference(subsumption_resolution,[],[f3183,f3090])).

fof(f3183,plain,(
    ! [X2] :
      ( r1_yellow_0(sK1,X2)
      | ~ r2_lattice3(sK1,X2,sK7(sK1,sK2,X2))
      | ~ r2_lattice3(sK1,sK2,sK7(sK1,sK2,X2))
      | v2_struct_0(sK1) ) ),
    inference(subsumption_resolution,[],[f3169,f3091])).

fof(f3169,plain,(
    ! [X2] :
      ( r1_yellow_0(sK1,X2)
      | ~ r2_lattice3(sK1,X2,sK7(sK1,sK2,X2))
      | ~ r2_lattice3(sK1,sK2,sK7(sK1,sK2,X2))
      | ~ l1_orders_2(sK1)
      | v2_struct_0(sK1) ) ),
    inference(resolution,[],[f3092,f3110])).
%------------------------------------------------------------------------------
