%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT1546+2 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n013.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Wed Dec 16 12:10:23 EST 2020

% Result     : Theorem 1.96s
% Output     : Refutation 1.96s
% Verified   : 
% Statistics : Number of formulae       :   80 ( 552 expanded)
%              Number of leaves         :   10 ( 172 expanded)
%              Depth                    :   31
%              Number of atoms          :  499 (5141 expanded)
%              Number of equality atoms :   66 ( 967 expanded)
%              Maximal formula depth    :   18 (   7 average)
%              Maximal term depth       :    2 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f3493,plain,(
    $false ),
    inference(subsumption_resolution,[],[f3492,f3048])).

fof(f3048,plain,(
    v5_orders_2(sK0) ),
    inference(cnf_transformation,[],[f3029])).

fof(f3029,plain,
    ( ( ~ r1_orders_2(sK0,sK2,sK1)
      | sK1 != k13_lattice3(sK0,sK1,sK2) )
    & ( r1_orders_2(sK0,sK2,sK1)
      | sK1 = k13_lattice3(sK0,sK1,sK2) )
    & m1_subset_1(sK2,u1_struct_0(sK0))
    & m1_subset_1(sK1,u1_struct_0(sK0))
    & l1_orders_2(sK0)
    & v1_lattice3(sK0)
    & v5_orders_2(sK0)
    & v3_orders_2(sK0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f3025,f3028,f3027,f3026])).

fof(f3026,plain,
    ( ? [X0] :
        ( ? [X1] :
            ( ? [X2] :
                ( ( ~ r1_orders_2(X0,X2,X1)
                  | k13_lattice3(X0,X1,X2) != X1 )
                & ( r1_orders_2(X0,X2,X1)
                  | k13_lattice3(X0,X1,X2) = X1 )
                & m1_subset_1(X2,u1_struct_0(X0)) )
            & m1_subset_1(X1,u1_struct_0(X0)) )
        & l1_orders_2(X0)
        & v1_lattice3(X0)
        & v5_orders_2(X0)
        & v3_orders_2(X0) )
   => ( ? [X1] :
          ( ? [X2] :
              ( ( ~ r1_orders_2(sK0,X2,X1)
                | k13_lattice3(sK0,X1,X2) != X1 )
              & ( r1_orders_2(sK0,X2,X1)
                | k13_lattice3(sK0,X1,X2) = X1 )
              & m1_subset_1(X2,u1_struct_0(sK0)) )
          & m1_subset_1(X1,u1_struct_0(sK0)) )
      & l1_orders_2(sK0)
      & v1_lattice3(sK0)
      & v5_orders_2(sK0)
      & v3_orders_2(sK0) ) ),
    introduced(choice_axiom,[])).

fof(f3027,plain,
    ( ? [X1] :
        ( ? [X2] :
            ( ( ~ r1_orders_2(sK0,X2,X1)
              | k13_lattice3(sK0,X1,X2) != X1 )
            & ( r1_orders_2(sK0,X2,X1)
              | k13_lattice3(sK0,X1,X2) = X1 )
            & m1_subset_1(X2,u1_struct_0(sK0)) )
        & m1_subset_1(X1,u1_struct_0(sK0)) )
   => ( ? [X2] :
          ( ( ~ r1_orders_2(sK0,X2,sK1)
            | sK1 != k13_lattice3(sK0,sK1,X2) )
          & ( r1_orders_2(sK0,X2,sK1)
            | sK1 = k13_lattice3(sK0,sK1,X2) )
          & m1_subset_1(X2,u1_struct_0(sK0)) )
      & m1_subset_1(sK1,u1_struct_0(sK0)) ) ),
    introduced(choice_axiom,[])).

fof(f3028,plain,
    ( ? [X2] :
        ( ( ~ r1_orders_2(sK0,X2,sK1)
          | sK1 != k13_lattice3(sK0,sK1,X2) )
        & ( r1_orders_2(sK0,X2,sK1)
          | sK1 = k13_lattice3(sK0,sK1,X2) )
        & m1_subset_1(X2,u1_struct_0(sK0)) )
   => ( ( ~ r1_orders_2(sK0,sK2,sK1)
        | sK1 != k13_lattice3(sK0,sK1,sK2) )
      & ( r1_orders_2(sK0,sK2,sK1)
        | sK1 = k13_lattice3(sK0,sK1,sK2) )
      & m1_subset_1(sK2,u1_struct_0(sK0)) ) ),
    introduced(choice_axiom,[])).

fof(f3025,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ( ~ r1_orders_2(X0,X2,X1)
                | k13_lattice3(X0,X1,X2) != X1 )
              & ( r1_orders_2(X0,X2,X1)
                | k13_lattice3(X0,X1,X2) = X1 )
              & m1_subset_1(X2,u1_struct_0(X0)) )
          & m1_subset_1(X1,u1_struct_0(X0)) )
      & l1_orders_2(X0)
      & v1_lattice3(X0)
      & v5_orders_2(X0)
      & v3_orders_2(X0) ) ),
    inference(flattening,[],[f3024])).

fof(f3024,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ( ~ r1_orders_2(X0,X2,X1)
                | k13_lattice3(X0,X1,X2) != X1 )
              & ( r1_orders_2(X0,X2,X1)
                | k13_lattice3(X0,X1,X2) = X1 )
              & m1_subset_1(X2,u1_struct_0(X0)) )
          & m1_subset_1(X1,u1_struct_0(X0)) )
      & l1_orders_2(X0)
      & v1_lattice3(X0)
      & v5_orders_2(X0)
      & v3_orders_2(X0) ) ),
    inference(nnf_transformation,[],[f3006])).

fof(f3006,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ( k13_lattice3(X0,X1,X2) = X1
              <~> r1_orders_2(X0,X2,X1) )
              & m1_subset_1(X2,u1_struct_0(X0)) )
          & m1_subset_1(X1,u1_struct_0(X0)) )
      & l1_orders_2(X0)
      & v1_lattice3(X0)
      & v5_orders_2(X0)
      & v3_orders_2(X0) ) ),
    inference(flattening,[],[f3005])).

fof(f3005,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ( k13_lattice3(X0,X1,X2) = X1
              <~> r1_orders_2(X0,X2,X1) )
              & m1_subset_1(X2,u1_struct_0(X0)) )
          & m1_subset_1(X1,u1_struct_0(X0)) )
      & l1_orders_2(X0)
      & v1_lattice3(X0)
      & v5_orders_2(X0)
      & v3_orders_2(X0) ) ),
    inference(ennf_transformation,[],[f2990])).

fof(f2990,negated_conjecture,(
    ~ ! [X0] :
        ( ( l1_orders_2(X0)
          & v1_lattice3(X0)
          & v5_orders_2(X0)
          & v3_orders_2(X0) )
       => ! [X1] :
            ( m1_subset_1(X1,u1_struct_0(X0))
           => ! [X2] :
                ( m1_subset_1(X2,u1_struct_0(X0))
               => ( k13_lattice3(X0,X1,X2) = X1
                <=> r1_orders_2(X0,X2,X1) ) ) ) ) ),
    inference(negated_conjecture,[],[f2989])).

fof(f2989,conjecture,(
    ! [X0] :
      ( ( l1_orders_2(X0)
        & v1_lattice3(X0)
        & v5_orders_2(X0)
        & v3_orders_2(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,u1_struct_0(X0))
         => ! [X2] :
              ( m1_subset_1(X2,u1_struct_0(X0))
             => ( k13_lattice3(X0,X1,X2) = X1
              <=> r1_orders_2(X0,X2,X1) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t24_yellow_0)).

fof(f3492,plain,(
    ~ v5_orders_2(sK0) ),
    inference(subsumption_resolution,[],[f3491,f3049])).

fof(f3049,plain,(
    v1_lattice3(sK0) ),
    inference(cnf_transformation,[],[f3029])).

fof(f3491,plain,
    ( ~ v1_lattice3(sK0)
    | ~ v5_orders_2(sK0) ),
    inference(subsumption_resolution,[],[f3490,f3050])).

fof(f3050,plain,(
    l1_orders_2(sK0) ),
    inference(cnf_transformation,[],[f3029])).

fof(f3490,plain,
    ( ~ l1_orders_2(sK0)
    | ~ v1_lattice3(sK0)
    | ~ v5_orders_2(sK0) ),
    inference(subsumption_resolution,[],[f3489,f3052])).

fof(f3052,plain,(
    m1_subset_1(sK2,u1_struct_0(sK0)) ),
    inference(cnf_transformation,[],[f3029])).

fof(f3489,plain,
    ( ~ m1_subset_1(sK2,u1_struct_0(sK0))
    | ~ l1_orders_2(sK0)
    | ~ v1_lattice3(sK0)
    | ~ v5_orders_2(sK0) ),
    inference(subsumption_resolution,[],[f3488,f3051])).

fof(f3051,plain,(
    m1_subset_1(sK1,u1_struct_0(sK0)) ),
    inference(cnf_transformation,[],[f3029])).

fof(f3488,plain,
    ( ~ m1_subset_1(sK1,u1_struct_0(sK0))
    | ~ m1_subset_1(sK2,u1_struct_0(sK0))
    | ~ l1_orders_2(sK0)
    | ~ v1_lattice3(sK0)
    | ~ v5_orders_2(sK0) ),
    inference(subsumption_resolution,[],[f3485,f3434])).

fof(f3434,plain,(
    ~ r1_orders_2(sK0,sK2,sK1) ),
    inference(subsumption_resolution,[],[f3054,f3433])).

fof(f3433,plain,(
    sK1 = k13_lattice3(sK0,sK1,sK2) ),
    inference(subsumption_resolution,[],[f3432,f3050])).

fof(f3432,plain,
    ( sK1 = k13_lattice3(sK0,sK1,sK2)
    | ~ l1_orders_2(sK0) ),
    inference(subsumption_resolution,[],[f3431,f3049])).

fof(f3431,plain,
    ( sK1 = k13_lattice3(sK0,sK1,sK2)
    | ~ v1_lattice3(sK0)
    | ~ l1_orders_2(sK0) ),
    inference(resolution,[],[f3411,f3081])).

fof(f3081,plain,(
    ! [X0] :
      ( ~ v2_struct_0(X0)
      | ~ v1_lattice3(X0)
      | ~ l1_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f3023])).

fof(f3023,plain,(
    ! [X0] :
      ( ~ v2_struct_0(X0)
      | ~ v1_lattice3(X0)
      | ~ l1_orders_2(X0) ) ),
    inference(flattening,[],[f3022])).

fof(f3022,plain,(
    ! [X0] :
      ( ~ v2_struct_0(X0)
      | ~ v1_lattice3(X0)
      | ~ l1_orders_2(X0) ) ),
    inference(ennf_transformation,[],[f2806])).

fof(f2806,axiom,(
    ! [X0] :
      ( l1_orders_2(X0)
     => ( v1_lattice3(X0)
       => ~ v2_struct_0(X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_lattice3)).

fof(f3411,plain,
    ( v2_struct_0(sK0)
    | sK1 = k13_lattice3(sK0,sK1,sK2) ),
    inference(subsumption_resolution,[],[f3410,f3052])).

fof(f3410,plain,
    ( ~ m1_subset_1(sK2,u1_struct_0(sK0))
    | sK1 = k13_lattice3(sK0,sK1,sK2)
    | v2_struct_0(sK0) ),
    inference(duplicate_literal_removal,[],[f3405])).

fof(f3405,plain,
    ( ~ m1_subset_1(sK2,u1_struct_0(sK0))
    | sK1 = k13_lattice3(sK0,sK1,sK2)
    | v2_struct_0(sK0)
    | sK1 = k13_lattice3(sK0,sK1,sK2) ),
    inference(resolution,[],[f3317,f3053])).

fof(f3053,plain,
    ( r1_orders_2(sK0,sK2,sK1)
    | sK1 = k13_lattice3(sK0,sK1,sK2) ),
    inference(cnf_transformation,[],[f3029])).

fof(f3317,plain,(
    ! [X9] :
      ( ~ r1_orders_2(sK0,X9,sK1)
      | ~ m1_subset_1(X9,u1_struct_0(sK0))
      | sK1 = k13_lattice3(sK0,sK1,X9)
      | v2_struct_0(sK0) ) ),
    inference(subsumption_resolution,[],[f3311,f3051])).

fof(f3311,plain,(
    ! [X9] :
      ( ~ r1_orders_2(sK0,X9,sK1)
      | ~ m1_subset_1(sK1,u1_struct_0(sK0))
      | ~ m1_subset_1(X9,u1_struct_0(sK0))
      | sK1 = k13_lattice3(sK0,sK1,X9)
      | v2_struct_0(sK0) ) ),
    inference(resolution,[],[f3232,f3090])).

fof(f3090,plain,
    ( r1_orders_2(sK0,sK1,sK1)
    | v2_struct_0(sK0) ),
    inference(resolution,[],[f3089,f3051])).

fof(f3089,plain,(
    ! [X0] :
      ( ~ m1_subset_1(X0,u1_struct_0(sK0))
      | r1_orders_2(sK0,X0,X0)
      | v2_struct_0(sK0) ) ),
    inference(subsumption_resolution,[],[f3088,f3050])).

fof(f3088,plain,(
    ! [X0] :
      ( ~ m1_subset_1(X0,u1_struct_0(sK0))
      | ~ l1_orders_2(sK0)
      | r1_orders_2(sK0,X0,X0)
      | v2_struct_0(sK0) ) ),
    inference(resolution,[],[f3056,f3047])).

fof(f3047,plain,(
    v3_orders_2(sK0) ),
    inference(cnf_transformation,[],[f3029])).

fof(f3056,plain,(
    ! [X0,X1] :
      ( ~ v3_orders_2(X0)
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | r1_orders_2(X0,X1,X1)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f3010])).

fof(f3010,plain,(
    ! [X0] :
      ( ! [X1] :
          ( r1_orders_2(X0,X1,X1)
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l1_orders_2(X0)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f3009])).

fof(f3009,plain,(
    ! [X0] :
      ( ! [X1] :
          ( r1_orders_2(X0,X1,X1)
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l1_orders_2(X0)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f1952])).

fof(f1952,axiom,(
    ! [X0] :
      ( ( l1_orders_2(X0)
        & v3_orders_2(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,u1_struct_0(X0))
         => r1_orders_2(X0,X1,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t24_orders_2)).

fof(f3232,plain,(
    ! [X8,X9] :
      ( ~ r1_orders_2(sK0,X9,X9)
      | ~ r1_orders_2(sK0,X8,X9)
      | ~ m1_subset_1(X9,u1_struct_0(sK0))
      | ~ m1_subset_1(X8,u1_struct_0(sK0))
      | k13_lattice3(sK0,X9,X8) = X9 ) ),
    inference(subsumption_resolution,[],[f3231,f3048])).

fof(f3231,plain,(
    ! [X8,X9] :
      ( ~ r1_orders_2(sK0,X8,X9)
      | ~ r1_orders_2(sK0,X9,X9)
      | ~ m1_subset_1(X9,u1_struct_0(sK0))
      | ~ m1_subset_1(X8,u1_struct_0(sK0))
      | k13_lattice3(sK0,X9,X8) = X9
      | ~ v5_orders_2(sK0) ) ),
    inference(subsumption_resolution,[],[f3230,f3049])).

fof(f3230,plain,(
    ! [X8,X9] :
      ( ~ r1_orders_2(sK0,X8,X9)
      | ~ r1_orders_2(sK0,X9,X9)
      | ~ m1_subset_1(X9,u1_struct_0(sK0))
      | ~ m1_subset_1(X8,u1_struct_0(sK0))
      | k13_lattice3(sK0,X9,X8) = X9
      | ~ v1_lattice3(sK0)
      | ~ v5_orders_2(sK0) ) ),
    inference(subsumption_resolution,[],[f3227,f3050])).

fof(f3227,plain,(
    ! [X8,X9] :
      ( ~ r1_orders_2(sK0,X8,X9)
      | ~ r1_orders_2(sK0,X9,X9)
      | ~ m1_subset_1(X9,u1_struct_0(sK0))
      | ~ m1_subset_1(X8,u1_struct_0(sK0))
      | k13_lattice3(sK0,X9,X8) = X9
      | ~ l1_orders_2(sK0)
      | ~ v1_lattice3(sK0)
      | ~ v5_orders_2(sK0) ) ),
    inference(duplicate_literal_removal,[],[f3224])).

fof(f3224,plain,(
    ! [X8,X9] :
      ( ~ r1_orders_2(sK0,X8,X9)
      | ~ r1_orders_2(sK0,X9,X9)
      | ~ m1_subset_1(X9,u1_struct_0(sK0))
      | ~ m1_subset_1(X8,u1_struct_0(sK0))
      | ~ m1_subset_1(X9,u1_struct_0(sK0))
      | k13_lattice3(sK0,X9,X8) = X9
      | k13_lattice3(sK0,X9,X8) = X9
      | ~ r1_orders_2(sK0,X8,X9)
      | ~ r1_orders_2(sK0,X9,X9)
      | ~ m1_subset_1(X9,u1_struct_0(sK0))
      | ~ m1_subset_1(X8,u1_struct_0(sK0))
      | ~ m1_subset_1(X9,u1_struct_0(sK0))
      | ~ l1_orders_2(sK0)
      | ~ v1_lattice3(sK0)
      | ~ v5_orders_2(sK0) ) ),
    inference(resolution,[],[f3168,f3066])).

fof(f3066,plain,(
    ! [X2,X0,X3,X1] :
      ( r1_orders_2(X0,X1,sK3(X0,X1,X2,X3))
      | k13_lattice3(X0,X1,X2) = X3
      | ~ r1_orders_2(X0,X2,X3)
      | ~ r1_orders_2(X0,X1,X3)
      | ~ m1_subset_1(X3,u1_struct_0(X0))
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | ~ v1_lattice3(X0)
      | ~ v5_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f3035])).

fof(f3035,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( ( ( k13_lattice3(X0,X1,X2) = X3
                      | ( ~ r1_orders_2(X0,X3,sK3(X0,X1,X2,X3))
                        & r1_orders_2(X0,X2,sK3(X0,X1,X2,X3))
                        & r1_orders_2(X0,X1,sK3(X0,X1,X2,X3))
                        & m1_subset_1(sK3(X0,X1,X2,X3),u1_struct_0(X0)) )
                      | ~ r1_orders_2(X0,X2,X3)
                      | ~ r1_orders_2(X0,X1,X3) )
                    & ( ( ! [X5] :
                            ( r1_orders_2(X0,X3,X5)
                            | ~ r1_orders_2(X0,X2,X5)
                            | ~ r1_orders_2(X0,X1,X5)
                            | ~ m1_subset_1(X5,u1_struct_0(X0)) )
                        & r1_orders_2(X0,X2,X3)
                        & r1_orders_2(X0,X1,X3) )
                      | k13_lattice3(X0,X1,X2) != X3 ) )
                  | ~ m1_subset_1(X3,u1_struct_0(X0)) )
              | ~ m1_subset_1(X2,u1_struct_0(X0)) )
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l1_orders_2(X0)
      | ~ v1_lattice3(X0)
      | ~ v5_orders_2(X0) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3])],[f3033,f3034])).

fof(f3034,plain,(
    ! [X3,X2,X1,X0] :
      ( ? [X4] :
          ( ~ r1_orders_2(X0,X3,X4)
          & r1_orders_2(X0,X2,X4)
          & r1_orders_2(X0,X1,X4)
          & m1_subset_1(X4,u1_struct_0(X0)) )
     => ( ~ r1_orders_2(X0,X3,sK3(X0,X1,X2,X3))
        & r1_orders_2(X0,X2,sK3(X0,X1,X2,X3))
        & r1_orders_2(X0,X1,sK3(X0,X1,X2,X3))
        & m1_subset_1(sK3(X0,X1,X2,X3),u1_struct_0(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f3033,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( ( ( k13_lattice3(X0,X1,X2) = X3
                      | ? [X4] :
                          ( ~ r1_orders_2(X0,X3,X4)
                          & r1_orders_2(X0,X2,X4)
                          & r1_orders_2(X0,X1,X4)
                          & m1_subset_1(X4,u1_struct_0(X0)) )
                      | ~ r1_orders_2(X0,X2,X3)
                      | ~ r1_orders_2(X0,X1,X3) )
                    & ( ( ! [X5] :
                            ( r1_orders_2(X0,X3,X5)
                            | ~ r1_orders_2(X0,X2,X5)
                            | ~ r1_orders_2(X0,X1,X5)
                            | ~ m1_subset_1(X5,u1_struct_0(X0)) )
                        & r1_orders_2(X0,X2,X3)
                        & r1_orders_2(X0,X1,X3) )
                      | k13_lattice3(X0,X1,X2) != X3 ) )
                  | ~ m1_subset_1(X3,u1_struct_0(X0)) )
              | ~ m1_subset_1(X2,u1_struct_0(X0)) )
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l1_orders_2(X0)
      | ~ v1_lattice3(X0)
      | ~ v5_orders_2(X0) ) ),
    inference(rectify,[],[f3032])).

fof(f3032,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( ( ( k13_lattice3(X0,X1,X2) = X3
                      | ? [X4] :
                          ( ~ r1_orders_2(X0,X3,X4)
                          & r1_orders_2(X0,X2,X4)
                          & r1_orders_2(X0,X1,X4)
                          & m1_subset_1(X4,u1_struct_0(X0)) )
                      | ~ r1_orders_2(X0,X2,X3)
                      | ~ r1_orders_2(X0,X1,X3) )
                    & ( ( ! [X4] :
                            ( r1_orders_2(X0,X3,X4)
                            | ~ r1_orders_2(X0,X2,X4)
                            | ~ r1_orders_2(X0,X1,X4)
                            | ~ m1_subset_1(X4,u1_struct_0(X0)) )
                        & r1_orders_2(X0,X2,X3)
                        & r1_orders_2(X0,X1,X3) )
                      | k13_lattice3(X0,X1,X2) != X3 ) )
                  | ~ m1_subset_1(X3,u1_struct_0(X0)) )
              | ~ m1_subset_1(X2,u1_struct_0(X0)) )
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l1_orders_2(X0)
      | ~ v1_lattice3(X0)
      | ~ v5_orders_2(X0) ) ),
    inference(flattening,[],[f3031])).

fof(f3031,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( ( ( k13_lattice3(X0,X1,X2) = X3
                      | ? [X4] :
                          ( ~ r1_orders_2(X0,X3,X4)
                          & r1_orders_2(X0,X2,X4)
                          & r1_orders_2(X0,X1,X4)
                          & m1_subset_1(X4,u1_struct_0(X0)) )
                      | ~ r1_orders_2(X0,X2,X3)
                      | ~ r1_orders_2(X0,X1,X3) )
                    & ( ( ! [X4] :
                            ( r1_orders_2(X0,X3,X4)
                            | ~ r1_orders_2(X0,X2,X4)
                            | ~ r1_orders_2(X0,X1,X4)
                            | ~ m1_subset_1(X4,u1_struct_0(X0)) )
                        & r1_orders_2(X0,X2,X3)
                        & r1_orders_2(X0,X1,X3) )
                      | k13_lattice3(X0,X1,X2) != X3 ) )
                  | ~ m1_subset_1(X3,u1_struct_0(X0)) )
              | ~ m1_subset_1(X2,u1_struct_0(X0)) )
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l1_orders_2(X0)
      | ~ v1_lattice3(X0)
      | ~ v5_orders_2(X0) ) ),
    inference(nnf_transformation,[],[f3019])).

fof(f3019,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( ( k13_lattice3(X0,X1,X2) = X3
                  <=> ( ! [X4] :
                          ( r1_orders_2(X0,X3,X4)
                          | ~ r1_orders_2(X0,X2,X4)
                          | ~ r1_orders_2(X0,X1,X4)
                          | ~ m1_subset_1(X4,u1_struct_0(X0)) )
                      & r1_orders_2(X0,X2,X3)
                      & r1_orders_2(X0,X1,X3) ) )
                  | ~ m1_subset_1(X3,u1_struct_0(X0)) )
              | ~ m1_subset_1(X2,u1_struct_0(X0)) )
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l1_orders_2(X0)
      | ~ v1_lattice3(X0)
      | ~ v5_orders_2(X0) ) ),
    inference(flattening,[],[f3018])).

fof(f3018,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( ( k13_lattice3(X0,X1,X2) = X3
                  <=> ( ! [X4] :
                          ( r1_orders_2(X0,X3,X4)
                          | ~ r1_orders_2(X0,X2,X4)
                          | ~ r1_orders_2(X0,X1,X4)
                          | ~ m1_subset_1(X4,u1_struct_0(X0)) )
                      & r1_orders_2(X0,X2,X3)
                      & r1_orders_2(X0,X1,X3) ) )
                  | ~ m1_subset_1(X3,u1_struct_0(X0)) )
              | ~ m1_subset_1(X2,u1_struct_0(X0)) )
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l1_orders_2(X0)
      | ~ v1_lattice3(X0)
      | ~ v5_orders_2(X0) ) ),
    inference(ennf_transformation,[],[f2987])).

fof(f2987,axiom,(
    ! [X0] :
      ( ( l1_orders_2(X0)
        & v1_lattice3(X0)
        & v5_orders_2(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,u1_struct_0(X0))
         => ! [X2] :
              ( m1_subset_1(X2,u1_struct_0(X0))
             => ! [X3] :
                  ( m1_subset_1(X3,u1_struct_0(X0))
                 => ( k13_lattice3(X0,X1,X2) = X3
                  <=> ( ! [X4] :
                          ( m1_subset_1(X4,u1_struct_0(X0))
                         => ( ( r1_orders_2(X0,X2,X4)
                              & r1_orders_2(X0,X1,X4) )
                           => r1_orders_2(X0,X3,X4) ) )
                      & r1_orders_2(X0,X2,X3)
                      & r1_orders_2(X0,X1,X3) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t22_yellow_0)).

fof(f3168,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_orders_2(sK0,X0,sK3(sK0,X1,X2,X0))
      | ~ r1_orders_2(sK0,X2,X0)
      | ~ r1_orders_2(sK0,X1,X0)
      | ~ m1_subset_1(X0,u1_struct_0(sK0))
      | ~ m1_subset_1(X2,u1_struct_0(sK0))
      | ~ m1_subset_1(X1,u1_struct_0(sK0))
      | k13_lattice3(sK0,X1,X2) = X0 ) ),
    inference(subsumption_resolution,[],[f3167,f3048])).

fof(f3167,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_orders_2(sK0,X0,sK3(sK0,X1,X2,X0))
      | ~ r1_orders_2(sK0,X2,X0)
      | ~ r1_orders_2(sK0,X1,X0)
      | ~ m1_subset_1(X0,u1_struct_0(sK0))
      | ~ m1_subset_1(X2,u1_struct_0(sK0))
      | ~ m1_subset_1(X1,u1_struct_0(sK0))
      | k13_lattice3(sK0,X1,X2) = X0
      | ~ v5_orders_2(sK0) ) ),
    inference(subsumption_resolution,[],[f3166,f3050])).

fof(f3166,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_orders_2(sK0,X0,sK3(sK0,X1,X2,X0))
      | ~ r1_orders_2(sK0,X2,X0)
      | ~ r1_orders_2(sK0,X1,X0)
      | ~ m1_subset_1(X0,u1_struct_0(sK0))
      | ~ m1_subset_1(X2,u1_struct_0(sK0))
      | ~ m1_subset_1(X1,u1_struct_0(sK0))
      | ~ l1_orders_2(sK0)
      | k13_lattice3(sK0,X1,X2) = X0
      | ~ v5_orders_2(sK0) ) ),
    inference(resolution,[],[f3068,f3049])).

fof(f3068,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ v1_lattice3(X0)
      | ~ r1_orders_2(X0,X3,sK3(X0,X1,X2,X3))
      | ~ r1_orders_2(X0,X2,X3)
      | ~ r1_orders_2(X0,X1,X3)
      | ~ m1_subset_1(X3,u1_struct_0(X0))
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | k13_lattice3(X0,X1,X2) = X3
      | ~ v5_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f3035])).

fof(f3054,plain,
    ( sK1 != k13_lattice3(sK0,sK1,sK2)
    | ~ r1_orders_2(sK0,sK2,sK1) ),
    inference(cnf_transformation,[],[f3029])).

fof(f3485,plain,
    ( r1_orders_2(sK0,sK2,sK1)
    | ~ m1_subset_1(sK1,u1_struct_0(sK0))
    | ~ m1_subset_1(sK2,u1_struct_0(sK0))
    | ~ l1_orders_2(sK0)
    | ~ v1_lattice3(sK0)
    | ~ v5_orders_2(sK0) ),
    inference(superposition,[],[f3087,f3436])).

fof(f3436,plain,(
    sK1 = k13_lattice3(sK0,sK2,sK1) ),
    inference(backward_demodulation,[],[f3183,f3433])).

fof(f3183,plain,(
    k13_lattice3(sK0,sK1,sK2) = k13_lattice3(sK0,sK2,sK1) ),
    inference(resolution,[],[f3169,f3052])).

fof(f3169,plain,(
    ! [X0] :
      ( ~ m1_subset_1(X0,u1_struct_0(sK0))
      | k13_lattice3(sK0,sK1,X0) = k13_lattice3(sK0,X0,sK1) ) ),
    inference(resolution,[],[f3123,f3051])).

fof(f3123,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,u1_struct_0(sK0))
      | ~ m1_subset_1(X0,u1_struct_0(sK0))
      | k13_lattice3(sK0,X1,X0) = k13_lattice3(sK0,X0,X1) ) ),
    inference(subsumption_resolution,[],[f3122,f3048])).

fof(f3122,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X0,u1_struct_0(sK0))
      | ~ m1_subset_1(X1,u1_struct_0(sK0))
      | k13_lattice3(sK0,X1,X0) = k13_lattice3(sK0,X0,X1)
      | ~ v5_orders_2(sK0) ) ),
    inference(subsumption_resolution,[],[f3121,f3050])).

fof(f3121,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X0,u1_struct_0(sK0))
      | ~ m1_subset_1(X1,u1_struct_0(sK0))
      | ~ l1_orders_2(sK0)
      | k13_lattice3(sK0,X1,X0) = k13_lattice3(sK0,X0,X1)
      | ~ v5_orders_2(sK0) ) ),
    inference(resolution,[],[f3060,f3049])).

fof(f3060,plain,(
    ! [X2,X0,X1] :
      ( ~ v1_lattice3(X0)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | k13_lattice3(X0,X1,X2) = k13_lattice3(X0,X2,X1)
      | ~ v5_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f3015])).

fof(f3015,plain,(
    ! [X0,X1,X2] :
      ( k13_lattice3(X0,X1,X2) = k13_lattice3(X0,X2,X1)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | ~ v1_lattice3(X0)
      | ~ v5_orders_2(X0) ) ),
    inference(flattening,[],[f3014])).

fof(f3014,plain,(
    ! [X0,X1,X2] :
      ( k13_lattice3(X0,X1,X2) = k13_lattice3(X0,X2,X1)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | ~ v1_lattice3(X0)
      | ~ v5_orders_2(X0) ) ),
    inference(ennf_transformation,[],[f2809])).

fof(f2809,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,u1_struct_0(X0))
        & m1_subset_1(X1,u1_struct_0(X0))
        & l1_orders_2(X0)
        & v1_lattice3(X0)
        & v5_orders_2(X0) )
     => k13_lattice3(X0,X1,X2) = k13_lattice3(X0,X2,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k13_lattice3)).

fof(f3087,plain,(
    ! [X2,X0,X1] :
      ( r1_orders_2(X0,X1,k13_lattice3(X0,X1,X2))
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | ~ v1_lattice3(X0)
      | ~ v5_orders_2(X0) ) ),
    inference(subsumption_resolution,[],[f3084,f3061])).

fof(f3061,plain,(
    ! [X2,X0,X1] :
      ( m1_subset_1(k13_lattice3(X0,X1,X2),u1_struct_0(X0))
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | ~ v1_lattice3(X0)
      | ~ v5_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f3017])).

fof(f3017,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(k13_lattice3(X0,X1,X2),u1_struct_0(X0))
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | ~ v1_lattice3(X0)
      | ~ v5_orders_2(X0) ) ),
    inference(flattening,[],[f3016])).

fof(f3016,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(k13_lattice3(X0,X1,X2),u1_struct_0(X0))
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | ~ v1_lattice3(X0)
      | ~ v5_orders_2(X0) ) ),
    inference(ennf_transformation,[],[f2836])).

fof(f2836,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,u1_struct_0(X0))
        & m1_subset_1(X1,u1_struct_0(X0))
        & l1_orders_2(X0)
        & v1_lattice3(X0)
        & v5_orders_2(X0) )
     => m1_subset_1(k13_lattice3(X0,X1,X2),u1_struct_0(X0)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k13_lattice3)).

fof(f3084,plain,(
    ! [X2,X0,X1] :
      ( r1_orders_2(X0,X1,k13_lattice3(X0,X1,X2))
      | ~ m1_subset_1(k13_lattice3(X0,X1,X2),u1_struct_0(X0))
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | ~ v1_lattice3(X0)
      | ~ v5_orders_2(X0) ) ),
    inference(equality_resolution,[],[f3062])).

fof(f3062,plain,(
    ! [X2,X0,X3,X1] :
      ( r1_orders_2(X0,X1,X3)
      | k13_lattice3(X0,X1,X2) != X3
      | ~ m1_subset_1(X3,u1_struct_0(X0))
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | ~ v1_lattice3(X0)
      | ~ v5_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f3035])).
%------------------------------------------------------------------------------
