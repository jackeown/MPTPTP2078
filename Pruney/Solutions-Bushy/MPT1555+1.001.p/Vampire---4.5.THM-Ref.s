%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT1555+1.001 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n032.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:50:05 EST 2020

% Result     : Theorem 0.12s
% Output     : Refutation 0.12s
% Verified   : 
% Statistics : Number of formulae       :   79 (1945 expanded)
%              Number of leaves         :    8 ( 664 expanded)
%              Depth                    :   29
%              Number of atoms          :  474 (24737 expanded)
%              Number of equality atoms :   70 (3398 expanded)
%              Maximal formula depth    :   14 (   6 average)
%              Maximal term depth       :    2 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f108,plain,(
    $false ),
    inference(unit_resulting_resolution,[],[f98,f99,f96,f95])).

fof(f95,plain,(
    ! [X0] :
      ( r1_orders_2(sK0,X0,sK1)
      | ~ m1_subset_1(X0,u1_struct_0(sK0))
      | ~ r1_lattice3(sK0,sK2,X0) ) ),
    inference(subsumption_resolution,[],[f94,f24])).

fof(f24,plain,(
    v5_orders_2(sK0) ),
    inference(cnf_transformation,[],[f20])).

fof(f20,plain,
    ( ( ( ~ r1_orders_2(sK0,sK3,sK1)
        & r1_lattice3(sK0,sK2,sK3)
        & m1_subset_1(sK3,u1_struct_0(sK0)) )
      | ~ r1_lattice3(sK0,sK2,sK1)
      | sK1 != k2_yellow_0(sK0,sK2) )
    & ( ( ! [X4] :
            ( r1_orders_2(sK0,X4,sK1)
            | ~ r1_lattice3(sK0,sK2,X4)
            | ~ m1_subset_1(X4,u1_struct_0(sK0)) )
        & r1_lattice3(sK0,sK2,sK1) )
      | sK1 = k2_yellow_0(sK0,sK2) )
    & m1_subset_1(sK1,u1_struct_0(sK0))
    & l1_orders_2(sK0)
    & v3_lattice3(sK0)
    & v5_orders_2(sK0)
    & ~ v2_struct_0(sK0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3])],[f15,f19,f18,f17,f16])).

fof(f16,plain,
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
                    ( ~ r1_orders_2(sK0,X3,X1)
                    & r1_lattice3(sK0,X2,X3)
                    & m1_subset_1(X3,u1_struct_0(sK0)) )
                | ~ r1_lattice3(sK0,X2,X1)
                | k2_yellow_0(sK0,X2) != X1 )
              & ( ( ! [X4] :
                      ( r1_orders_2(sK0,X4,X1)
                      | ~ r1_lattice3(sK0,X2,X4)
                      | ~ m1_subset_1(X4,u1_struct_0(sK0)) )
                  & r1_lattice3(sK0,X2,X1) )
                | k2_yellow_0(sK0,X2) = X1 ) )
          & m1_subset_1(X1,u1_struct_0(sK0)) )
      & l1_orders_2(sK0)
      & v3_lattice3(sK0)
      & v5_orders_2(sK0)
      & ~ v2_struct_0(sK0) ) ),
    introduced(choice_axiom,[])).

fof(f17,plain,
    ( ? [X1] :
        ( ? [X2] :
            ( ( ? [X3] :
                  ( ~ r1_orders_2(sK0,X3,X1)
                  & r1_lattice3(sK0,X2,X3)
                  & m1_subset_1(X3,u1_struct_0(sK0)) )
              | ~ r1_lattice3(sK0,X2,X1)
              | k2_yellow_0(sK0,X2) != X1 )
            & ( ( ! [X4] :
                    ( r1_orders_2(sK0,X4,X1)
                    | ~ r1_lattice3(sK0,X2,X4)
                    | ~ m1_subset_1(X4,u1_struct_0(sK0)) )
                & r1_lattice3(sK0,X2,X1) )
              | k2_yellow_0(sK0,X2) = X1 ) )
        & m1_subset_1(X1,u1_struct_0(sK0)) )
   => ( ? [X2] :
          ( ( ? [X3] :
                ( ~ r1_orders_2(sK0,X3,sK1)
                & r1_lattice3(sK0,X2,X3)
                & m1_subset_1(X3,u1_struct_0(sK0)) )
            | ~ r1_lattice3(sK0,X2,sK1)
            | k2_yellow_0(sK0,X2) != sK1 )
          & ( ( ! [X4] :
                  ( r1_orders_2(sK0,X4,sK1)
                  | ~ r1_lattice3(sK0,X2,X4)
                  | ~ m1_subset_1(X4,u1_struct_0(sK0)) )
              & r1_lattice3(sK0,X2,sK1) )
            | k2_yellow_0(sK0,X2) = sK1 ) )
      & m1_subset_1(sK1,u1_struct_0(sK0)) ) ),
    introduced(choice_axiom,[])).

fof(f18,plain,
    ( ? [X2] :
        ( ( ? [X3] :
              ( ~ r1_orders_2(sK0,X3,sK1)
              & r1_lattice3(sK0,X2,X3)
              & m1_subset_1(X3,u1_struct_0(sK0)) )
          | ~ r1_lattice3(sK0,X2,sK1)
          | k2_yellow_0(sK0,X2) != sK1 )
        & ( ( ! [X4] :
                ( r1_orders_2(sK0,X4,sK1)
                | ~ r1_lattice3(sK0,X2,X4)
                | ~ m1_subset_1(X4,u1_struct_0(sK0)) )
            & r1_lattice3(sK0,X2,sK1) )
          | k2_yellow_0(sK0,X2) = sK1 ) )
   => ( ( ? [X3] :
            ( ~ r1_orders_2(sK0,X3,sK1)
            & r1_lattice3(sK0,sK2,X3)
            & m1_subset_1(X3,u1_struct_0(sK0)) )
        | ~ r1_lattice3(sK0,sK2,sK1)
        | sK1 != k2_yellow_0(sK0,sK2) )
      & ( ( ! [X4] :
              ( r1_orders_2(sK0,X4,sK1)
              | ~ r1_lattice3(sK0,sK2,X4)
              | ~ m1_subset_1(X4,u1_struct_0(sK0)) )
          & r1_lattice3(sK0,sK2,sK1) )
        | sK1 = k2_yellow_0(sK0,sK2) ) ) ),
    introduced(choice_axiom,[])).

fof(f19,plain,
    ( ? [X3] :
        ( ~ r1_orders_2(sK0,X3,sK1)
        & r1_lattice3(sK0,sK2,X3)
        & m1_subset_1(X3,u1_struct_0(sK0)) )
   => ( ~ r1_orders_2(sK0,sK3,sK1)
      & r1_lattice3(sK0,sK2,sK3)
      & m1_subset_1(sK3,u1_struct_0(sK0)) ) ),
    introduced(choice_axiom,[])).

fof(f15,plain,(
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
    inference(rectify,[],[f14])).

fof(f14,plain,(
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
    inference(flattening,[],[f13])).

fof(f13,plain,(
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
    inference(nnf_transformation,[],[f8])).

fof(f8,plain,(
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
    inference(flattening,[],[f7])).

fof(f7,plain,(
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
    inference(ennf_transformation,[],[f4])).

fof(f4,negated_conjecture,(
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
    inference(negated_conjecture,[],[f3])).

fof(f3,conjecture,(
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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t33_yellow_0)).

fof(f94,plain,(
    ! [X0] :
      ( ~ r1_lattice3(sK0,sK2,X0)
      | ~ m1_subset_1(X0,u1_struct_0(sK0))
      | r1_orders_2(sK0,X0,sK1)
      | ~ v5_orders_2(sK0) ) ),
    inference(subsumption_resolution,[],[f93,f26])).

fof(f26,plain,(
    l1_orders_2(sK0) ),
    inference(cnf_transformation,[],[f20])).

fof(f93,plain,(
    ! [X0] :
      ( ~ r1_lattice3(sK0,sK2,X0)
      | ~ m1_subset_1(X0,u1_struct_0(sK0))
      | r1_orders_2(sK0,X0,sK1)
      | ~ l1_orders_2(sK0)
      | ~ v5_orders_2(sK0) ) ),
    inference(subsumption_resolution,[],[f92,f44])).

fof(f44,plain,(
    ! [X0] : r2_yellow_0(sK0,X0) ),
    inference(unit_resulting_resolution,[],[f23,f24,f25,f26,f33])).

fof(f33,plain,(
    ! [X0,X1] :
      ( ~ l1_orders_2(X0)
      | r2_yellow_0(X0,X1)
      | ~ v3_lattice3(X0)
      | ~ v5_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f10])).

fof(f10,plain,(
    ! [X0] :
      ( ! [X1] : r2_yellow_0(X0,X1)
      | ~ l1_orders_2(X0)
      | ~ v3_lattice3(X0)
      | ~ v5_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f9])).

fof(f9,plain,(
    ! [X0] :
      ( ! [X1] : r2_yellow_0(X0,X1)
      | ~ l1_orders_2(X0)
      | ~ v3_lattice3(X0)
      | ~ v5_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,plain,(
    ! [X0] :
      ( ( l1_orders_2(X0)
        & v3_lattice3(X0)
        & v5_orders_2(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] : r2_yellow_0(X0,X1) ) ),
    inference(pure_predicate_removal,[],[f1])).

fof(f1,axiom,(
    ! [X0] :
      ( ( l1_orders_2(X0)
        & v3_lattice3(X0)
        & v5_orders_2(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( r2_yellow_0(X0,X1)
          & r1_yellow_0(X0,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t17_yellow_0)).

fof(f25,plain,(
    v3_lattice3(sK0) ),
    inference(cnf_transformation,[],[f20])).

fof(f23,plain,(
    ~ v2_struct_0(sK0) ),
    inference(cnf_transformation,[],[f20])).

fof(f92,plain,(
    ! [X0] :
      ( ~ r1_lattice3(sK0,sK2,X0)
      | ~ m1_subset_1(X0,u1_struct_0(sK0))
      | ~ r2_yellow_0(sK0,sK2)
      | r1_orders_2(sK0,X0,sK1)
      | ~ l1_orders_2(sK0)
      | ~ v5_orders_2(sK0) ) ),
    inference(subsumption_resolution,[],[f87,f27])).

fof(f27,plain,(
    m1_subset_1(sK1,u1_struct_0(sK0)) ),
    inference(cnf_transformation,[],[f20])).

fof(f87,plain,(
    ! [X0] :
      ( ~ m1_subset_1(sK1,u1_struct_0(sK0))
      | ~ r1_lattice3(sK0,sK2,X0)
      | ~ m1_subset_1(X0,u1_struct_0(sK0))
      | ~ r2_yellow_0(sK0,sK2)
      | r1_orders_2(sK0,X0,sK1)
      | ~ l1_orders_2(sK0)
      | ~ v5_orders_2(sK0) ) ),
    inference(superposition,[],[f42,f79])).

fof(f79,plain,(
    sK1 = k2_yellow_0(sK0,sK2) ),
    inference(subsumption_resolution,[],[f78,f28])).

fof(f28,plain,
    ( r1_lattice3(sK0,sK2,sK1)
    | sK1 = k2_yellow_0(sK0,sK2) ),
    inference(cnf_transformation,[],[f20])).

fof(f78,plain,
    ( sK1 = k2_yellow_0(sK0,sK2)
    | ~ r1_lattice3(sK0,sK2,sK1) ),
    inference(subsumption_resolution,[],[f77,f24])).

fof(f77,plain,
    ( sK1 = k2_yellow_0(sK0,sK2)
    | ~ r1_lattice3(sK0,sK2,sK1)
    | ~ v5_orders_2(sK0) ),
    inference(subsumption_resolution,[],[f76,f26])).

fof(f76,plain,
    ( sK1 = k2_yellow_0(sK0,sK2)
    | ~ r1_lattice3(sK0,sK2,sK1)
    | ~ l1_orders_2(sK0)
    | ~ v5_orders_2(sK0) ),
    inference(subsumption_resolution,[],[f75,f27])).

fof(f75,plain,
    ( sK1 = k2_yellow_0(sK0,sK2)
    | ~ r1_lattice3(sK0,sK2,sK1)
    | ~ m1_subset_1(sK1,u1_struct_0(sK0))
    | ~ l1_orders_2(sK0)
    | ~ v5_orders_2(sK0) ),
    inference(duplicate_literal_removal,[],[f73])).

fof(f73,plain,
    ( sK1 = k2_yellow_0(sK0,sK2)
    | sK1 = k2_yellow_0(sK0,sK2)
    | ~ r1_lattice3(sK0,sK2,sK1)
    | ~ m1_subset_1(sK1,u1_struct_0(sK0))
    | ~ l1_orders_2(sK0)
    | ~ v5_orders_2(sK0) ),
    inference(resolution,[],[f72,f36])).

fof(f36,plain,(
    ! [X2,X0,X1] :
      ( m1_subset_1(sK4(X0,X1,X2),u1_struct_0(X0))
      | k2_yellow_0(X0,X2) = X1
      | ~ r1_lattice3(X0,X2,X1)
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | ~ v5_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f22,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( ( r2_yellow_0(X0,X2)
                  & k2_yellow_0(X0,X2) = X1 )
                | ( ~ r1_orders_2(X0,sK4(X0,X1,X2),X1)
                  & r1_lattice3(X0,X2,sK4(X0,X1,X2))
                  & m1_subset_1(sK4(X0,X1,X2),u1_struct_0(X0)) )
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
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4])],[f12,f21])).

fof(f21,plain,(
    ! [X2,X1,X0] :
      ( ? [X3] :
          ( ~ r1_orders_2(X0,X3,X1)
          & r1_lattice3(X0,X2,X3)
          & m1_subset_1(X3,u1_struct_0(X0)) )
     => ( ~ r1_orders_2(X0,sK4(X0,X1,X2),X1)
        & r1_lattice3(X0,X2,sK4(X0,X1,X2))
        & m1_subset_1(sK4(X0,X1,X2),u1_struct_0(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f12,plain,(
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
    inference(flattening,[],[f11])).

fof(f11,plain,(
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
    inference(ennf_transformation,[],[f5])).

fof(f5,plain,(
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
    inference(rectify,[],[f2])).

fof(f2,axiom,(
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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t31_yellow_0)).

fof(f72,plain,
    ( ~ m1_subset_1(sK4(sK0,sK1,sK2),u1_struct_0(sK0))
    | sK1 = k2_yellow_0(sK0,sK2) ),
    inference(subsumption_resolution,[],[f71,f28])).

fof(f71,plain,
    ( sK1 = k2_yellow_0(sK0,sK2)
    | ~ r1_lattice3(sK0,sK2,sK1)
    | ~ m1_subset_1(sK4(sK0,sK1,sK2),u1_struct_0(sK0)) ),
    inference(duplicate_literal_removal,[],[f70])).

fof(f70,plain,
    ( sK1 = k2_yellow_0(sK0,sK2)
    | ~ r1_lattice3(sK0,sK2,sK1)
    | ~ m1_subset_1(sK4(sK0,sK1,sK2),u1_struct_0(sK0))
    | sK1 = k2_yellow_0(sK0,sK2)
    | sK1 = k2_yellow_0(sK0,sK2) ),
    inference(resolution,[],[f64,f58])).

fof(f58,plain,
    ( r1_lattice3(sK0,sK2,sK4(sK0,sK1,sK2))
    | sK1 = k2_yellow_0(sK0,sK2) ),
    inference(duplicate_literal_removal,[],[f57])).

fof(f57,plain,
    ( r1_lattice3(sK0,sK2,sK4(sK0,sK1,sK2))
    | sK1 = k2_yellow_0(sK0,sK2)
    | sK1 = k2_yellow_0(sK0,sK2) ),
    inference(resolution,[],[f54,f28])).

fof(f54,plain,(
    ! [X6] :
      ( ~ r1_lattice3(sK0,X6,sK1)
      | r1_lattice3(sK0,X6,sK4(sK0,sK1,X6))
      | sK1 = k2_yellow_0(sK0,X6) ) ),
    inference(resolution,[],[f50,f27])).

fof(f50,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,u1_struct_0(sK0))
      | ~ r1_lattice3(sK0,X0,X1)
      | r1_lattice3(sK0,X0,sK4(sK0,X1,X0))
      | k2_yellow_0(sK0,X0) = X1 ) ),
    inference(subsumption_resolution,[],[f45,f24])).

fof(f45,plain,(
    ! [X0,X1] :
      ( r1_lattice3(sK0,X0,sK4(sK0,X1,X0))
      | ~ r1_lattice3(sK0,X0,X1)
      | ~ m1_subset_1(X1,u1_struct_0(sK0))
      | k2_yellow_0(sK0,X0) = X1
      | ~ v5_orders_2(sK0) ) ),
    inference(resolution,[],[f26,f37])).

fof(f37,plain,(
    ! [X2,X0,X1] :
      ( ~ l1_orders_2(X0)
      | r1_lattice3(X0,X2,sK4(X0,X1,X2))
      | ~ r1_lattice3(X0,X2,X1)
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | k2_yellow_0(X0,X2) = X1
      | ~ v5_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f64,plain,(
    ! [X0] :
      ( ~ r1_lattice3(sK0,sK2,sK4(sK0,sK1,X0))
      | sK1 = k2_yellow_0(sK0,X0)
      | ~ r1_lattice3(sK0,X0,sK1)
      | ~ m1_subset_1(sK4(sK0,sK1,X0),u1_struct_0(sK0))
      | sK1 = k2_yellow_0(sK0,sK2) ) ),
    inference(resolution,[],[f61,f29])).

fof(f29,plain,(
    ! [X4] :
      ( r1_orders_2(sK0,X4,sK1)
      | ~ r1_lattice3(sK0,sK2,X4)
      | ~ m1_subset_1(X4,u1_struct_0(sK0))
      | sK1 = k2_yellow_0(sK0,sK2) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f61,plain,(
    ! [X6] :
      ( ~ r1_orders_2(sK0,sK4(sK0,sK1,X6),sK1)
      | ~ r1_lattice3(sK0,X6,sK1)
      | sK1 = k2_yellow_0(sK0,X6) ) ),
    inference(resolution,[],[f51,f27])).

fof(f51,plain,(
    ! [X2,X3] :
      ( ~ m1_subset_1(X2,u1_struct_0(sK0))
      | ~ r1_lattice3(sK0,X3,X2)
      | ~ r1_orders_2(sK0,sK4(sK0,X2,X3),X2)
      | k2_yellow_0(sK0,X3) = X2 ) ),
    inference(subsumption_resolution,[],[f46,f24])).

fof(f46,plain,(
    ! [X2,X3] :
      ( ~ r1_orders_2(sK0,sK4(sK0,X2,X3),X2)
      | ~ r1_lattice3(sK0,X3,X2)
      | ~ m1_subset_1(X2,u1_struct_0(sK0))
      | k2_yellow_0(sK0,X3) = X2
      | ~ v5_orders_2(sK0) ) ),
    inference(resolution,[],[f26,f38])).

fof(f38,plain,(
    ! [X2,X0,X1] :
      ( ~ l1_orders_2(X0)
      | ~ r1_orders_2(X0,sK4(X0,X1,X2),X1)
      | ~ r1_lattice3(X0,X2,X1)
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | k2_yellow_0(X0,X2) = X1
      | ~ v5_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f42,plain,(
    ! [X4,X2,X0] :
      ( ~ m1_subset_1(k2_yellow_0(X0,X2),u1_struct_0(X0))
      | ~ r1_lattice3(X0,X2,X4)
      | ~ m1_subset_1(X4,u1_struct_0(X0))
      | ~ r2_yellow_0(X0,X2)
      | r1_orders_2(X0,X4,k2_yellow_0(X0,X2))
      | ~ l1_orders_2(X0)
      | ~ v5_orders_2(X0) ) ),
    inference(equality_resolution,[],[f35])).

fof(f35,plain,(
    ! [X4,X2,X0,X1] :
      ( r1_orders_2(X0,X4,X1)
      | ~ r1_lattice3(X0,X2,X4)
      | ~ m1_subset_1(X4,u1_struct_0(X0))
      | ~ r2_yellow_0(X0,X2)
      | k2_yellow_0(X0,X2) != X1
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | ~ v5_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f96,plain,(
    ~ r1_orders_2(sK0,sK3,sK1) ),
    inference(unit_resulting_resolution,[],[f91,f83])).

fof(f83,plain,
    ( ~ r1_orders_2(sK0,sK3,sK1)
    | ~ r1_lattice3(sK0,sK2,sK1) ),
    inference(trivial_inequality_removal,[],[f82])).

fof(f82,plain,
    ( sK1 != sK1
    | ~ r1_lattice3(sK0,sK2,sK1)
    | ~ r1_orders_2(sK0,sK3,sK1) ),
    inference(backward_demodulation,[],[f32,f79])).

fof(f32,plain,
    ( sK1 != k2_yellow_0(sK0,sK2)
    | ~ r1_lattice3(sK0,sK2,sK1)
    | ~ r1_orders_2(sK0,sK3,sK1) ),
    inference(cnf_transformation,[],[f20])).

fof(f91,plain,(
    r1_lattice3(sK0,sK2,sK1) ),
    inference(subsumption_resolution,[],[f90,f24])).

fof(f90,plain,
    ( r1_lattice3(sK0,sK2,sK1)
    | ~ v5_orders_2(sK0) ),
    inference(subsumption_resolution,[],[f89,f26])).

fof(f89,plain,
    ( r1_lattice3(sK0,sK2,sK1)
    | ~ l1_orders_2(sK0)
    | ~ v5_orders_2(sK0) ),
    inference(subsumption_resolution,[],[f88,f44])).

fof(f88,plain,
    ( ~ r2_yellow_0(sK0,sK2)
    | r1_lattice3(sK0,sK2,sK1)
    | ~ l1_orders_2(sK0)
    | ~ v5_orders_2(sK0) ),
    inference(subsumption_resolution,[],[f86,f27])).

fof(f86,plain,
    ( ~ m1_subset_1(sK1,u1_struct_0(sK0))
    | ~ r2_yellow_0(sK0,sK2)
    | r1_lattice3(sK0,sK2,sK1)
    | ~ l1_orders_2(sK0)
    | ~ v5_orders_2(sK0) ),
    inference(superposition,[],[f43,f79])).

% (995)lrs+11_1024_afr=on:afp=40000:afq=2.0:anc=none:br=off:ep=RSTC:gs=on:nm=16:nwc=1:stl=30:sp=occurrence:urr=on_129 on theBenchmark
% (988)lrs+1011_5_afr=on:afp=100000:afq=1.0:amm=off:anc=none:cond=on:lma=on:nm=6:nwc=1:sas=z3:stl=30:sac=on:urr=on_12 on theBenchmark
fof(f43,plain,(
    ! [X2,X0] :
      ( ~ m1_subset_1(k2_yellow_0(X0,X2),u1_struct_0(X0))
      | ~ r2_yellow_0(X0,X2)
      | r1_lattice3(X0,X2,k2_yellow_0(X0,X2))
      | ~ l1_orders_2(X0)
      | ~ v5_orders_2(X0) ) ),
    inference(equality_resolution,[],[f34])).

fof(f34,plain,(
    ! [X2,X0,X1] :
      ( r1_lattice3(X0,X2,X1)
      | ~ r2_yellow_0(X0,X2)
      | k2_yellow_0(X0,X2) != X1
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | ~ v5_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f99,plain,(
    m1_subset_1(sK3,u1_struct_0(sK0)) ),
    inference(unit_resulting_resolution,[],[f91,f85])).

fof(f85,plain,
    ( ~ r1_lattice3(sK0,sK2,sK1)
    | m1_subset_1(sK3,u1_struct_0(sK0)) ),
    inference(trivial_inequality_removal,[],[f80])).

fof(f80,plain,
    ( sK1 != sK1
    | ~ r1_lattice3(sK0,sK2,sK1)
    | m1_subset_1(sK3,u1_struct_0(sK0)) ),
    inference(backward_demodulation,[],[f30,f79])).

fof(f30,plain,
    ( sK1 != k2_yellow_0(sK0,sK2)
    | ~ r1_lattice3(sK0,sK2,sK1)
    | m1_subset_1(sK3,u1_struct_0(sK0)) ),
    inference(cnf_transformation,[],[f20])).

fof(f98,plain,(
    r1_lattice3(sK0,sK2,sK3) ),
    inference(unit_resulting_resolution,[],[f91,f84])).

fof(f84,plain,
    ( r1_lattice3(sK0,sK2,sK3)
    | ~ r1_lattice3(sK0,sK2,sK1) ),
    inference(trivial_inequality_removal,[],[f81])).

fof(f81,plain,
    ( sK1 != sK1
    | ~ r1_lattice3(sK0,sK2,sK1)
    | r1_lattice3(sK0,sK2,sK3) ),
    inference(backward_demodulation,[],[f31,f79])).

fof(f31,plain,
    ( sK1 != k2_yellow_0(sK0,sK2)
    | ~ r1_lattice3(sK0,sK2,sK1)
    | r1_lattice3(sK0,sK2,sK3) ),
    inference(cnf_transformation,[],[f20])).

%------------------------------------------------------------------------------
