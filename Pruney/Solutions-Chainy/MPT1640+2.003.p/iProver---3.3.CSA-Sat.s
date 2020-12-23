%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n022.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:20:46 EST 2020

% Result     : CounterSatisfiable 1.35s
% Output     : Saturation 1.35s
% Verified   : 
% Statistics : Number of formulae       :  209 (3287 expanded)
%              Number of clauses        :  157 ( 853 expanded)
%              Number of leaves         :   19 ( 999 expanded)
%              Depth                    :   23
%              Number of atoms          :  959 (22172 expanded)
%              Number of equality atoms :  271 (5431 expanded)
%              Maximal formula depth    :   13 (   6 average)
%              Maximal clause size      :   16 (   4 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f2,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,u1_struct_0(X0))
        & m1_subset_1(X1,u1_struct_0(X0))
        & l1_orders_2(X0)
        & v3_orders_2(X0)
        & ~ v2_struct_0(X0) )
     => r3_orders_2(X0,X1,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f10,plain,(
    ! [X0,X1,X2] :
      ( r3_orders_2(X0,X1,X1)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f11,plain,(
    ! [X0,X1,X2] :
      ( r3_orders_2(X0,X1,X1)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f10])).

fof(f31,plain,(
    ! [X2,X0,X1] :
      ( r3_orders_2(X0,X1,X1)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f11])).

fof(f5,conjecture,(
    ! [X0] :
      ( ( l1_orders_2(X0)
        & v5_orders_2(X0)
        & v3_orders_2(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,u1_struct_0(X0))
         => ! [X2] :
              ( m1_subset_1(X2,u1_struct_0(X0))
             => ( k6_waybel_0(X0,X1) = k6_waybel_0(X0,X2)
               => X1 = X2 ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f6,negated_conjecture,(
    ~ ! [X0] :
        ( ( l1_orders_2(X0)
          & v5_orders_2(X0)
          & v3_orders_2(X0)
          & ~ v2_struct_0(X0) )
       => ! [X1] :
            ( m1_subset_1(X1,u1_struct_0(X0))
           => ! [X2] :
                ( m1_subset_1(X2,u1_struct_0(X0))
               => ( k6_waybel_0(X0,X1) = k6_waybel_0(X0,X2)
                 => X1 = X2 ) ) ) ) ),
    inference(negated_conjecture,[],[f5])).

fof(f16,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( X1 != X2
              & k6_waybel_0(X0,X1) = k6_waybel_0(X0,X2)
              & m1_subset_1(X2,u1_struct_0(X0)) )
          & m1_subset_1(X1,u1_struct_0(X0)) )
      & l1_orders_2(X0)
      & v5_orders_2(X0)
      & v3_orders_2(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f17,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( X1 != X2
              & k6_waybel_0(X0,X1) = k6_waybel_0(X0,X2)
              & m1_subset_1(X2,u1_struct_0(X0)) )
          & m1_subset_1(X1,u1_struct_0(X0)) )
      & l1_orders_2(X0)
      & v5_orders_2(X0)
      & v3_orders_2(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(flattening,[],[f16])).

fof(f27,plain,(
    ! [X0,X1] :
      ( ? [X2] :
          ( X1 != X2
          & k6_waybel_0(X0,X1) = k6_waybel_0(X0,X2)
          & m1_subset_1(X2,u1_struct_0(X0)) )
     => ( sK4 != X1
        & k6_waybel_0(X0,sK4) = k6_waybel_0(X0,X1)
        & m1_subset_1(sK4,u1_struct_0(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f26,plain,(
    ! [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( X1 != X2
              & k6_waybel_0(X0,X1) = k6_waybel_0(X0,X2)
              & m1_subset_1(X2,u1_struct_0(X0)) )
          & m1_subset_1(X1,u1_struct_0(X0)) )
     => ( ? [X2] :
            ( sK3 != X2
            & k6_waybel_0(X0,sK3) = k6_waybel_0(X0,X2)
            & m1_subset_1(X2,u1_struct_0(X0)) )
        & m1_subset_1(sK3,u1_struct_0(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f25,plain,
    ( ? [X0] :
        ( ? [X1] :
            ( ? [X2] :
                ( X1 != X2
                & k6_waybel_0(X0,X1) = k6_waybel_0(X0,X2)
                & m1_subset_1(X2,u1_struct_0(X0)) )
            & m1_subset_1(X1,u1_struct_0(X0)) )
        & l1_orders_2(X0)
        & v5_orders_2(X0)
        & v3_orders_2(X0)
        & ~ v2_struct_0(X0) )
   => ( ? [X1] :
          ( ? [X2] :
              ( X1 != X2
              & k6_waybel_0(sK2,X1) = k6_waybel_0(sK2,X2)
              & m1_subset_1(X2,u1_struct_0(sK2)) )
          & m1_subset_1(X1,u1_struct_0(sK2)) )
      & l1_orders_2(sK2)
      & v5_orders_2(sK2)
      & v3_orders_2(sK2)
      & ~ v2_struct_0(sK2) ) ),
    introduced(choice_axiom,[])).

fof(f28,plain,
    ( sK3 != sK4
    & k6_waybel_0(sK2,sK3) = k6_waybel_0(sK2,sK4)
    & m1_subset_1(sK4,u1_struct_0(sK2))
    & m1_subset_1(sK3,u1_struct_0(sK2))
    & l1_orders_2(sK2)
    & v5_orders_2(sK2)
    & v3_orders_2(sK2)
    & ~ v2_struct_0(sK2) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2,sK3,sK4])],[f17,f27,f26,f25])).

fof(f45,plain,(
    v3_orders_2(sK2) ),
    inference(cnf_transformation,[],[f28])).

fof(f44,plain,(
    ~ v2_struct_0(sK2) ),
    inference(cnf_transformation,[],[f28])).

fof(f47,plain,(
    l1_orders_2(sK2) ),
    inference(cnf_transformation,[],[f28])).

fof(f1,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,u1_struct_0(X0))
        & m1_subset_1(X1,u1_struct_0(X0))
        & l1_orders_2(X0)
        & v3_orders_2(X0)
        & ~ v2_struct_0(X0) )
     => ( r3_orders_2(X0,X1,X2)
      <=> r1_orders_2(X0,X1,X2) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f8,plain,(
    ! [X0,X1,X2] :
      ( ( r3_orders_2(X0,X1,X2)
      <=> r1_orders_2(X0,X1,X2) )
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f9,plain,(
    ! [X0,X1,X2] :
      ( ( r3_orders_2(X0,X1,X2)
      <=> r1_orders_2(X0,X1,X2) )
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f8])).

fof(f18,plain,(
    ! [X0,X1,X2] :
      ( ( ( r3_orders_2(X0,X1,X2)
          | ~ r1_orders_2(X0,X1,X2) )
        & ( r1_orders_2(X0,X1,X2)
          | ~ r3_orders_2(X0,X1,X2) ) )
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(nnf_transformation,[],[f9])).

fof(f29,plain,(
    ! [X2,X0,X1] :
      ( r1_orders_2(X0,X1,X2)
      | ~ r3_orders_2(X0,X1,X2)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f48,plain,(
    m1_subset_1(sK3,u1_struct_0(sK2)) ),
    inference(cnf_transformation,[],[f28])).

fof(f50,plain,(
    k6_waybel_0(sK2,sK3) = k6_waybel_0(sK2,sK4) ),
    inference(cnf_transformation,[],[f28])).

fof(f4,axiom,(
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f7,plain,(
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
    inference(rectify,[],[f4])).

fof(f14,plain,(
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
    inference(ennf_transformation,[],[f7])).

fof(f15,plain,(
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
    inference(flattening,[],[f14])).

fof(f23,plain,(
    ! [X2,X1,X0] :
      ( ? [X3] :
          ( ~ r1_orders_2(X0,X3,X1)
          & r1_lattice3(X0,X2,X3)
          & m1_subset_1(X3,u1_struct_0(X0)) )
     => ( ~ r1_orders_2(X0,sK1(X0,X1,X2),X1)
        & r1_lattice3(X0,X2,sK1(X0,X1,X2))
        & m1_subset_1(sK1(X0,X1,X2),u1_struct_0(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f24,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( ( r2_yellow_0(X0,X2)
                  & k2_yellow_0(X0,X2) = X1 )
                | ( ~ r1_orders_2(X0,sK1(X0,X1,X2),X1)
                  & r1_lattice3(X0,X2,sK1(X0,X1,X2))
                  & m1_subset_1(sK1(X0,X1,X2),u1_struct_0(X0)) )
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
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1])],[f15,f23])).

fof(f38,plain,(
    ! [X2,X0,X1] :
      ( k2_yellow_0(X0,X2) = X1
      | m1_subset_1(sK1(X0,X1,X2),u1_struct_0(X0))
      | ~ r1_lattice3(X0,X2,X1)
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | ~ v5_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f46,plain,(
    v5_orders_2(sK2) ),
    inference(cnf_transformation,[],[f28])).

fof(f39,plain,(
    ! [X2,X0,X1] :
      ( k2_yellow_0(X0,X2) = X1
      | r1_lattice3(X0,X2,sK1(X0,X1,X2))
      | ~ r1_lattice3(X0,X2,X1)
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | ~ v5_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f3,axiom,(
    ! [X0] :
      ( l1_orders_2(X0)
     => ! [X1,X2] :
          ( m1_subset_1(X2,u1_struct_0(X0))
         => ( r1_lattice3(X0,X1,X2)
          <=> ! [X3] :
                ( m1_subset_1(X3,u1_struct_0(X0))
               => ( r2_hidden(X3,X1)
                 => r1_orders_2(X0,X2,X3) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f12,plain,(
    ! [X0] :
      ( ! [X1,X2] :
          ( ( r1_lattice3(X0,X1,X2)
          <=> ! [X3] :
                ( r1_orders_2(X0,X2,X3)
                | ~ r2_hidden(X3,X1)
                | ~ m1_subset_1(X3,u1_struct_0(X0)) ) )
          | ~ m1_subset_1(X2,u1_struct_0(X0)) )
      | ~ l1_orders_2(X0) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f13,plain,(
    ! [X0] :
      ( ! [X1,X2] :
          ( ( r1_lattice3(X0,X1,X2)
          <=> ! [X3] :
                ( r1_orders_2(X0,X2,X3)
                | ~ r2_hidden(X3,X1)
                | ~ m1_subset_1(X3,u1_struct_0(X0)) ) )
          | ~ m1_subset_1(X2,u1_struct_0(X0)) )
      | ~ l1_orders_2(X0) ) ),
    inference(flattening,[],[f12])).

fof(f19,plain,(
    ! [X0] :
      ( ! [X1,X2] :
          ( ( ( r1_lattice3(X0,X1,X2)
              | ? [X3] :
                  ( ~ r1_orders_2(X0,X2,X3)
                  & r2_hidden(X3,X1)
                  & m1_subset_1(X3,u1_struct_0(X0)) ) )
            & ( ! [X3] :
                  ( r1_orders_2(X0,X2,X3)
                  | ~ r2_hidden(X3,X1)
                  | ~ m1_subset_1(X3,u1_struct_0(X0)) )
              | ~ r1_lattice3(X0,X1,X2) ) )
          | ~ m1_subset_1(X2,u1_struct_0(X0)) )
      | ~ l1_orders_2(X0) ) ),
    inference(nnf_transformation,[],[f13])).

fof(f20,plain,(
    ! [X0] :
      ( ! [X1,X2] :
          ( ( ( r1_lattice3(X0,X1,X2)
              | ? [X3] :
                  ( ~ r1_orders_2(X0,X2,X3)
                  & r2_hidden(X3,X1)
                  & m1_subset_1(X3,u1_struct_0(X0)) ) )
            & ( ! [X4] :
                  ( r1_orders_2(X0,X2,X4)
                  | ~ r2_hidden(X4,X1)
                  | ~ m1_subset_1(X4,u1_struct_0(X0)) )
              | ~ r1_lattice3(X0,X1,X2) ) )
          | ~ m1_subset_1(X2,u1_struct_0(X0)) )
      | ~ l1_orders_2(X0) ) ),
    inference(rectify,[],[f19])).

fof(f21,plain,(
    ! [X2,X1,X0] :
      ( ? [X3] :
          ( ~ r1_orders_2(X0,X2,X3)
          & r2_hidden(X3,X1)
          & m1_subset_1(X3,u1_struct_0(X0)) )
     => ( ~ r1_orders_2(X0,X2,sK0(X0,X1,X2))
        & r2_hidden(sK0(X0,X1,X2),X1)
        & m1_subset_1(sK0(X0,X1,X2),u1_struct_0(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f22,plain,(
    ! [X0] :
      ( ! [X1,X2] :
          ( ( ( r1_lattice3(X0,X1,X2)
              | ( ~ r1_orders_2(X0,X2,sK0(X0,X1,X2))
                & r2_hidden(sK0(X0,X1,X2),X1)
                & m1_subset_1(sK0(X0,X1,X2),u1_struct_0(X0)) ) )
            & ( ! [X4] :
                  ( r1_orders_2(X0,X2,X4)
                  | ~ r2_hidden(X4,X1)
                  | ~ m1_subset_1(X4,u1_struct_0(X0)) )
              | ~ r1_lattice3(X0,X1,X2) ) )
          | ~ m1_subset_1(X2,u1_struct_0(X0)) )
      | ~ l1_orders_2(X0) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f20,f21])).

fof(f32,plain,(
    ! [X4,X2,X0,X1] :
      ( r1_orders_2(X0,X2,X4)
      | ~ r2_hidden(X4,X1)
      | ~ m1_subset_1(X4,u1_struct_0(X0))
      | ~ r1_lattice3(X0,X1,X2)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ l1_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f34,plain,(
    ! [X2,X0,X1] :
      ( r1_lattice3(X0,X1,X2)
      | r2_hidden(sK0(X0,X1,X2),X1)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ l1_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f33,plain,(
    ! [X2,X0,X1] :
      ( r1_lattice3(X0,X1,X2)
      | m1_subset_1(sK0(X0,X1,X2),u1_struct_0(X0))
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ l1_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f40,plain,(
    ! [X2,X0,X1] :
      ( k2_yellow_0(X0,X2) = X1
      | ~ r1_orders_2(X0,sK1(X0,X1,X2),X1)
      | ~ r1_lattice3(X0,X2,X1)
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | ~ v5_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f41,plain,(
    ! [X2,X0,X1] :
      ( r2_yellow_0(X0,X2)
      | m1_subset_1(sK1(X0,X1,X2),u1_struct_0(X0))
      | ~ r1_lattice3(X0,X2,X1)
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | ~ v5_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f42,plain,(
    ! [X2,X0,X1] :
      ( r2_yellow_0(X0,X2)
      | r1_lattice3(X0,X2,sK1(X0,X1,X2))
      | ~ r1_lattice3(X0,X2,X1)
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | ~ v5_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f43,plain,(
    ! [X2,X0,X1] :
      ( r2_yellow_0(X0,X2)
      | ~ r1_orders_2(X0,sK1(X0,X1,X2),X1)
      | ~ r1_lattice3(X0,X2,X1)
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | ~ v5_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f49,plain,(
    m1_subset_1(sK4,u1_struct_0(sK2)) ),
    inference(cnf_transformation,[],[f28])).

fof(f35,plain,(
    ! [X2,X0,X1] :
      ( r1_lattice3(X0,X1,X2)
      | ~ r1_orders_2(X0,X2,sK0(X0,X1,X2))
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ l1_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f37,plain,(
    ! [X4,X2,X0,X1] :
      ( r1_orders_2(X0,X4,X1)
      | ~ r1_lattice3(X0,X2,X4)
      | ~ m1_subset_1(X4,u1_struct_0(X0))
      | ~ r2_yellow_0(X0,X2)
      | k2_yellow_0(X0,X2) != X1
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | ~ v5_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f52,plain,(
    ! [X4,X2,X0] :
      ( r1_orders_2(X0,X4,k2_yellow_0(X0,X2))
      | ~ r1_lattice3(X0,X2,X4)
      | ~ m1_subset_1(X4,u1_struct_0(X0))
      | ~ r2_yellow_0(X0,X2)
      | ~ m1_subset_1(k2_yellow_0(X0,X2),u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | ~ v5_orders_2(X0) ) ),
    inference(equality_resolution,[],[f37])).

fof(f36,plain,(
    ! [X2,X0,X1] :
      ( r1_lattice3(X0,X2,X1)
      | ~ r2_yellow_0(X0,X2)
      | k2_yellow_0(X0,X2) != X1
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | ~ v5_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f53,plain,(
    ! [X2,X0] :
      ( r1_lattice3(X0,X2,k2_yellow_0(X0,X2))
      | ~ r2_yellow_0(X0,X2)
      | ~ m1_subset_1(k2_yellow_0(X0,X2),u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | ~ v5_orders_2(X0) ) ),
    inference(equality_resolution,[],[f36])).

fof(f51,plain,(
    sK3 != sK4 ),
    inference(cnf_transformation,[],[f28])).

cnf(c_2,plain,
    ( r3_orders_2(X0,X1,X1)
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | ~ m1_subset_1(X1,u1_struct_0(X0))
    | v2_struct_0(X0)
    | ~ v3_orders_2(X0)
    | ~ l1_orders_2(X0) ),
    inference(cnf_transformation,[],[f31])).

cnf(c_21,negated_conjecture,
    ( v3_orders_2(sK2) ),
    inference(cnf_transformation,[],[f45])).

cnf(c_270,plain,
    ( r3_orders_2(X0,X1,X1)
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | ~ m1_subset_1(X1,u1_struct_0(X0))
    | v2_struct_0(X0)
    | ~ l1_orders_2(X0)
    | sK2 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_2,c_21])).

cnf(c_271,plain,
    ( r3_orders_2(sK2,X0,X0)
    | ~ m1_subset_1(X0,u1_struct_0(sK2))
    | ~ m1_subset_1(X1,u1_struct_0(sK2))
    | v2_struct_0(sK2)
    | ~ l1_orders_2(sK2) ),
    inference(unflattening,[status(thm)],[c_270])).

cnf(c_22,negated_conjecture,
    ( ~ v2_struct_0(sK2) ),
    inference(cnf_transformation,[],[f44])).

cnf(c_19,negated_conjecture,
    ( l1_orders_2(sK2) ),
    inference(cnf_transformation,[],[f47])).

cnf(c_275,plain,
    ( r3_orders_2(sK2,X0,X0)
    | ~ m1_subset_1(X0,u1_struct_0(sK2))
    | ~ m1_subset_1(X1,u1_struct_0(sK2)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_271,c_22,c_19])).

cnf(c_276,plain,
    ( r3_orders_2(sK2,X0,X0)
    | ~ m1_subset_1(X1,u1_struct_0(sK2))
    | ~ m1_subset_1(X0,u1_struct_0(sK2)) ),
    inference(renaming,[status(thm)],[c_275])).

cnf(c_1,plain,
    ( r1_orders_2(X0,X1,X2)
    | ~ r3_orders_2(X0,X1,X2)
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | ~ m1_subset_1(X1,u1_struct_0(X0))
    | v2_struct_0(X0)
    | ~ v3_orders_2(X0)
    | ~ l1_orders_2(X0) ),
    inference(cnf_transformation,[],[f29])).

cnf(c_291,plain,
    ( r1_orders_2(X0,X1,X2)
    | ~ r3_orders_2(X0,X1,X2)
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | ~ m1_subset_1(X1,u1_struct_0(X0))
    | v2_struct_0(X0)
    | ~ l1_orders_2(X0)
    | sK2 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_1,c_21])).

cnf(c_292,plain,
    ( r1_orders_2(sK2,X0,X1)
    | ~ r3_orders_2(sK2,X0,X1)
    | ~ m1_subset_1(X0,u1_struct_0(sK2))
    | ~ m1_subset_1(X1,u1_struct_0(sK2))
    | v2_struct_0(sK2)
    | ~ l1_orders_2(sK2) ),
    inference(unflattening,[status(thm)],[c_291])).

cnf(c_296,plain,
    ( r1_orders_2(sK2,X0,X1)
    | ~ r3_orders_2(sK2,X0,X1)
    | ~ m1_subset_1(X0,u1_struct_0(sK2))
    | ~ m1_subset_1(X1,u1_struct_0(sK2)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_292,c_22,c_19])).

cnf(c_297,plain,
    ( r1_orders_2(sK2,X0,X1)
    | ~ r3_orders_2(sK2,X0,X1)
    | ~ m1_subset_1(X1,u1_struct_0(sK2))
    | ~ m1_subset_1(X0,u1_struct_0(sK2)) ),
    inference(renaming,[status(thm)],[c_296])).

cnf(c_354,plain,
    ( r1_orders_2(sK2,X0,X1)
    | ~ m1_subset_1(X2,u1_struct_0(sK2))
    | ~ m1_subset_1(X0,u1_struct_0(sK2))
    | ~ m1_subset_1(X3,u1_struct_0(sK2))
    | ~ m1_subset_1(X1,u1_struct_0(sK2))
    | X0 != X3
    | X1 != X3
    | sK2 != sK2 ),
    inference(resolution_lifted,[status(thm)],[c_276,c_297])).

cnf(c_355,plain,
    ( r1_orders_2(sK2,X0,X0)
    | ~ m1_subset_1(X1,u1_struct_0(sK2))
    | ~ m1_subset_1(X0,u1_struct_0(sK2)) ),
    inference(unflattening,[status(thm)],[c_354])).

cnf(c_1662,plain,
    ( r1_orders_2(sK2,X0_48,X0_48)
    | ~ m1_subset_1(X1_48,u1_struct_0(sK2))
    | ~ m1_subset_1(X0_48,u1_struct_0(sK2)) ),
    inference(subtyping,[status(esa)],[c_355])).

cnf(c_1667,plain,
    ( ~ m1_subset_1(X0_48,u1_struct_0(sK2))
    | ~ sP0_iProver_split ),
    inference(splitting,[splitting(split),new_symbols(definition,[sP0_iProver_split])],[c_1662])).

cnf(c_18,negated_conjecture,
    ( m1_subset_1(sK3,u1_struct_0(sK2)) ),
    inference(cnf_transformation,[],[f48])).

cnf(c_1693,plain,
    ( ~ m1_subset_1(sK3,u1_struct_0(sK2))
    | ~ sP0_iProver_split ),
    inference(instantiation,[status(thm)],[c_1667])).

cnf(c_1763,plain,
    ( ~ sP0_iProver_split ),
    inference(global_propositional_subsumption,[status(thm)],[c_1667,c_18,c_1693])).

cnf(c_1669,plain,
    ( sP1_iProver_split
    | sP0_iProver_split ),
    inference(splitting,[splitting(split),new_symbols(definition,[])],[c_1662])).

cnf(c_1751,plain,
    ( sP1_iProver_split ),
    inference(global_propositional_subsumption,[status(thm)],[c_1669,c_18,c_1693])).

cnf(c_1678,plain,
    ( k6_waybel_0(X0_46,X0_48) = k6_waybel_0(X0_46,X1_48)
    | X0_48 != X1_48 ),
    theory(equality)).

cnf(c_1674,plain,
    ( X0_50 != X1_50
    | X2_50 != X1_50
    | X2_50 = X0_50 ),
    theory(equality)).

cnf(c_1672,plain,
    ( X0_50 = X0_50 ),
    theory(equality)).

cnf(c_16,negated_conjecture,
    ( k6_waybel_0(sK2,sK3) = k6_waybel_0(sK2,sK4) ),
    inference(cnf_transformation,[],[f50])).

cnf(c_1665,negated_conjecture,
    ( k6_waybel_0(sK2,sK3) = k6_waybel_0(sK2,sK4) ),
    inference(subtyping,[status(esa)],[c_16])).

cnf(c_211,plain,
    ( ~ v5_orders_2(X0)
    | v5_orders_2(X1)
    | X1 != X0 ),
    theory(equality)).

cnf(c_210,plain,
    ( ~ r2_hidden(X0,X1)
    | r2_hidden(X2,X1)
    | X2 != X0 ),
    theory(equality)).

cnf(c_208,plain,
    ( ~ v2_struct_0(X0)
    | v2_struct_0(X1)
    | X1 != X0 ),
    theory(equality)).

cnf(c_207,plain,
    ( ~ v3_orders_2(X0)
    | v3_orders_2(X1)
    | X1 != X0 ),
    theory(equality)).

cnf(c_206,plain,
    ( ~ l1_orders_2(X0)
    | l1_orders_2(X1)
    | X1 != X0 ),
    theory(equality)).

cnf(c_200,plain,
    ( X0_2 = X0_2 ),
    theory(equality)).

cnf(c_12,plain,
    ( ~ r1_lattice3(X0,X1,X2)
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | m1_subset_1(sK1(X0,X2,X1),u1_struct_0(X0))
    | ~ v5_orders_2(X0)
    | ~ l1_orders_2(X0)
    | k2_yellow_0(X0,X1) = X2 ),
    inference(cnf_transformation,[],[f38])).

cnf(c_20,negated_conjecture,
    ( v5_orders_2(sK2) ),
    inference(cnf_transformation,[],[f46])).

cnf(c_421,plain,
    ( ~ r1_lattice3(X0,X1,X2)
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | m1_subset_1(sK1(X0,X2,X1),u1_struct_0(X0))
    | ~ l1_orders_2(X0)
    | k2_yellow_0(X0,X1) = X2
    | sK2 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_12,c_20])).

cnf(c_422,plain,
    ( ~ r1_lattice3(sK2,X0,X1)
    | ~ m1_subset_1(X1,u1_struct_0(sK2))
    | m1_subset_1(sK1(sK2,X1,X0),u1_struct_0(sK2))
    | ~ l1_orders_2(sK2)
    | k2_yellow_0(sK2,X0) = X1 ),
    inference(unflattening,[status(thm)],[c_421])).

cnf(c_426,plain,
    ( m1_subset_1(sK1(sK2,X1,X0),u1_struct_0(sK2))
    | ~ m1_subset_1(X1,u1_struct_0(sK2))
    | ~ r1_lattice3(sK2,X0,X1)
    | k2_yellow_0(sK2,X0) = X1 ),
    inference(global_propositional_subsumption,[status(thm)],[c_422,c_19])).

cnf(c_427,plain,
    ( ~ r1_lattice3(sK2,X0,X1)
    | ~ m1_subset_1(X1,u1_struct_0(sK2))
    | m1_subset_1(sK1(sK2,X1,X0),u1_struct_0(sK2))
    | k2_yellow_0(sK2,X0) = X1 ),
    inference(renaming,[status(thm)],[c_426])).

cnf(c_1659,plain,
    ( ~ r1_lattice3(sK2,X0_47,X0_48)
    | ~ m1_subset_1(X0_48,u1_struct_0(sK2))
    | m1_subset_1(sK1(sK2,X0_48,X0_47),u1_struct_0(sK2))
    | k2_yellow_0(sK2,X0_47) = X0_48 ),
    inference(subtyping,[status(esa)],[c_427])).

cnf(c_1980,plain,
    ( k2_yellow_0(sK2,X0_47) = X0_48
    | r1_lattice3(sK2,X0_47,X0_48) != iProver_top
    | m1_subset_1(X0_48,u1_struct_0(sK2)) != iProver_top
    | m1_subset_1(sK1(sK2,X0_48,X0_47),u1_struct_0(sK2)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1659])).

cnf(c_11,plain,
    ( ~ r1_lattice3(X0,X1,X2)
    | r1_lattice3(X0,X1,sK1(X0,X2,X1))
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | ~ v5_orders_2(X0)
    | ~ l1_orders_2(X0)
    | k2_yellow_0(X0,X1) = X2 ),
    inference(cnf_transformation,[],[f39])).

cnf(c_445,plain,
    ( ~ r1_lattice3(X0,X1,X2)
    | r1_lattice3(X0,X1,sK1(X0,X2,X1))
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | ~ l1_orders_2(X0)
    | k2_yellow_0(X0,X1) = X2
    | sK2 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_11,c_20])).

cnf(c_446,plain,
    ( ~ r1_lattice3(sK2,X0,X1)
    | r1_lattice3(sK2,X0,sK1(sK2,X1,X0))
    | ~ m1_subset_1(X1,u1_struct_0(sK2))
    | ~ l1_orders_2(sK2)
    | k2_yellow_0(sK2,X0) = X1 ),
    inference(unflattening,[status(thm)],[c_445])).

cnf(c_450,plain,
    ( ~ m1_subset_1(X1,u1_struct_0(sK2))
    | r1_lattice3(sK2,X0,sK1(sK2,X1,X0))
    | ~ r1_lattice3(sK2,X0,X1)
    | k2_yellow_0(sK2,X0) = X1 ),
    inference(global_propositional_subsumption,[status(thm)],[c_446,c_19])).

cnf(c_451,plain,
    ( ~ r1_lattice3(sK2,X0,X1)
    | r1_lattice3(sK2,X0,sK1(sK2,X1,X0))
    | ~ m1_subset_1(X1,u1_struct_0(sK2))
    | k2_yellow_0(sK2,X0) = X1 ),
    inference(renaming,[status(thm)],[c_450])).

cnf(c_1658,plain,
    ( ~ r1_lattice3(sK2,X0_47,X0_48)
    | r1_lattice3(sK2,X0_47,sK1(sK2,X0_48,X0_47))
    | ~ m1_subset_1(X0_48,u1_struct_0(sK2))
    | k2_yellow_0(sK2,X0_47) = X0_48 ),
    inference(subtyping,[status(esa)],[c_451])).

cnf(c_1981,plain,
    ( k2_yellow_0(sK2,X0_47) = X0_48
    | r1_lattice3(sK2,X0_47,X0_48) != iProver_top
    | r1_lattice3(sK2,X0_47,sK1(sK2,X0_48,X0_47)) = iProver_top
    | m1_subset_1(X0_48,u1_struct_0(sK2)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1658])).

cnf(c_6,plain,
    ( ~ r1_lattice3(X0,X1,X2)
    | r1_orders_2(X0,X2,X3)
    | ~ r2_hidden(X3,X1)
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | ~ m1_subset_1(X3,u1_struct_0(X0))
    | ~ l1_orders_2(X0) ),
    inference(cnf_transformation,[],[f32])).

cnf(c_605,plain,
    ( ~ r1_lattice3(X0,X1,X2)
    | r1_orders_2(X0,X2,X3)
    | ~ r2_hidden(X3,X1)
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | ~ m1_subset_1(X3,u1_struct_0(X0))
    | sK2 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_6,c_19])).

cnf(c_606,plain,
    ( ~ r1_lattice3(sK2,X0,X1)
    | r1_orders_2(sK2,X1,X2)
    | ~ r2_hidden(X2,X0)
    | ~ m1_subset_1(X1,u1_struct_0(sK2))
    | ~ m1_subset_1(X2,u1_struct_0(sK2)) ),
    inference(unflattening,[status(thm)],[c_605])).

cnf(c_4,plain,
    ( r1_lattice3(X0,X1,X2)
    | r2_hidden(sK0(X0,X1,X2),X1)
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | ~ l1_orders_2(X0) ),
    inference(cnf_transformation,[],[f34])).

cnf(c_639,plain,
    ( r1_lattice3(X0,X1,X2)
    | r2_hidden(sK0(X0,X1,X2),X1)
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | sK2 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_4,c_19])).

cnf(c_640,plain,
    ( r1_lattice3(sK2,X0,X1)
    | r2_hidden(sK0(sK2,X0,X1),X0)
    | ~ m1_subset_1(X1,u1_struct_0(sK2)) ),
    inference(unflattening,[status(thm)],[c_639])).

cnf(c_687,plain,
    ( ~ r1_lattice3(sK2,X0,X1)
    | r1_lattice3(sK2,X2,X3)
    | r1_orders_2(sK2,X1,X4)
    | ~ m1_subset_1(X1,u1_struct_0(sK2))
    | ~ m1_subset_1(X4,u1_struct_0(sK2))
    | ~ m1_subset_1(X3,u1_struct_0(sK2))
    | X2 != X0
    | sK0(sK2,X2,X3) != X4 ),
    inference(resolution_lifted,[status(thm)],[c_606,c_640])).

cnf(c_688,plain,
    ( ~ r1_lattice3(sK2,X0,X1)
    | r1_lattice3(sK2,X0,X2)
    | r1_orders_2(sK2,X1,sK0(sK2,X0,X2))
    | ~ m1_subset_1(X1,u1_struct_0(sK2))
    | ~ m1_subset_1(X2,u1_struct_0(sK2))
    | ~ m1_subset_1(sK0(sK2,X0,X2),u1_struct_0(sK2)) ),
    inference(unflattening,[status(thm)],[c_687])).

cnf(c_5,plain,
    ( r1_lattice3(X0,X1,X2)
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | m1_subset_1(sK0(X0,X1,X2),u1_struct_0(X0))
    | ~ l1_orders_2(X0) ),
    inference(cnf_transformation,[],[f33])).

cnf(c_624,plain,
    ( r1_lattice3(X0,X1,X2)
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | m1_subset_1(sK0(X0,X1,X2),u1_struct_0(X0))
    | sK2 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_5,c_19])).

cnf(c_625,plain,
    ( r1_lattice3(sK2,X0,X1)
    | ~ m1_subset_1(X1,u1_struct_0(sK2))
    | m1_subset_1(sK0(sK2,X0,X1),u1_struct_0(sK2)) ),
    inference(unflattening,[status(thm)],[c_624])).

cnf(c_702,plain,
    ( ~ r1_lattice3(sK2,X0,X1)
    | r1_lattice3(sK2,X0,X2)
    | r1_orders_2(sK2,X1,sK0(sK2,X0,X2))
    | ~ m1_subset_1(X1,u1_struct_0(sK2))
    | ~ m1_subset_1(X2,u1_struct_0(sK2)) ),
    inference(forward_subsumption_resolution,[status(thm)],[c_688,c_625])).

cnf(c_1651,plain,
    ( ~ r1_lattice3(sK2,X0_47,X0_48)
    | r1_lattice3(sK2,X0_47,X1_48)
    | r1_orders_2(sK2,X0_48,sK0(sK2,X0_47,X1_48))
    | ~ m1_subset_1(X1_48,u1_struct_0(sK2))
    | ~ m1_subset_1(X0_48,u1_struct_0(sK2)) ),
    inference(subtyping,[status(esa)],[c_702])).

cnf(c_1988,plain,
    ( r1_lattice3(sK2,X0_47,X0_48) != iProver_top
    | r1_lattice3(sK2,X0_47,X1_48) = iProver_top
    | r1_orders_2(sK2,X0_48,sK0(sK2,X0_47,X1_48)) = iProver_top
    | m1_subset_1(X0_48,u1_struct_0(sK2)) != iProver_top
    | m1_subset_1(X1_48,u1_struct_0(sK2)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1651])).

cnf(c_10,plain,
    ( ~ r1_lattice3(X0,X1,X2)
    | ~ r1_orders_2(X0,sK1(X0,X2,X1),X2)
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | ~ v5_orders_2(X0)
    | ~ l1_orders_2(X0)
    | k2_yellow_0(X0,X1) = X2 ),
    inference(cnf_transformation,[],[f40])).

cnf(c_469,plain,
    ( ~ r1_lattice3(X0,X1,X2)
    | ~ r1_orders_2(X0,sK1(X0,X2,X1),X2)
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | ~ l1_orders_2(X0)
    | k2_yellow_0(X0,X1) = X2
    | sK2 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_10,c_20])).

cnf(c_470,plain,
    ( ~ r1_lattice3(sK2,X0,X1)
    | ~ r1_orders_2(sK2,sK1(sK2,X1,X0),X1)
    | ~ m1_subset_1(X1,u1_struct_0(sK2))
    | ~ l1_orders_2(sK2)
    | k2_yellow_0(sK2,X0) = X1 ),
    inference(unflattening,[status(thm)],[c_469])).

cnf(c_474,plain,
    ( ~ m1_subset_1(X1,u1_struct_0(sK2))
    | ~ r1_orders_2(sK2,sK1(sK2,X1,X0),X1)
    | ~ r1_lattice3(sK2,X0,X1)
    | k2_yellow_0(sK2,X0) = X1 ),
    inference(global_propositional_subsumption,[status(thm)],[c_470,c_19])).

cnf(c_475,plain,
    ( ~ r1_lattice3(sK2,X0,X1)
    | ~ r1_orders_2(sK2,sK1(sK2,X1,X0),X1)
    | ~ m1_subset_1(X1,u1_struct_0(sK2))
    | k2_yellow_0(sK2,X0) = X1 ),
    inference(renaming,[status(thm)],[c_474])).

cnf(c_1657,plain,
    ( ~ r1_lattice3(sK2,X0_47,X0_48)
    | ~ r1_orders_2(sK2,sK1(sK2,X0_48,X0_47),X0_48)
    | ~ m1_subset_1(X0_48,u1_struct_0(sK2))
    | k2_yellow_0(sK2,X0_47) = X0_48 ),
    inference(subtyping,[status(esa)],[c_475])).

cnf(c_1982,plain,
    ( k2_yellow_0(sK2,X0_47) = X0_48
    | r1_lattice3(sK2,X0_47,X0_48) != iProver_top
    | r1_orders_2(sK2,sK1(sK2,X0_48,X0_47),X0_48) != iProver_top
    | m1_subset_1(X0_48,u1_struct_0(sK2)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1657])).

cnf(c_2591,plain,
    ( sK0(sK2,X0_47,X0_48) = k2_yellow_0(sK2,X1_47)
    | r1_lattice3(sK2,X0_47,X0_48) = iProver_top
    | r1_lattice3(sK2,X0_47,sK1(sK2,sK0(sK2,X0_47,X0_48),X1_47)) != iProver_top
    | r1_lattice3(sK2,X1_47,sK0(sK2,X0_47,X0_48)) != iProver_top
    | m1_subset_1(X0_48,u1_struct_0(sK2)) != iProver_top
    | m1_subset_1(sK1(sK2,sK0(sK2,X0_47,X0_48),X1_47),u1_struct_0(sK2)) != iProver_top
    | m1_subset_1(sK0(sK2,X0_47,X0_48),u1_struct_0(sK2)) != iProver_top ),
    inference(superposition,[status(thm)],[c_1988,c_1982])).

cnf(c_1653,plain,
    ( r1_lattice3(sK2,X0_47,X0_48)
    | ~ m1_subset_1(X0_48,u1_struct_0(sK2))
    | m1_subset_1(sK0(sK2,X0_47,X0_48),u1_struct_0(sK2)) ),
    inference(subtyping,[status(esa)],[c_625])).

cnf(c_1719,plain,
    ( r1_lattice3(sK2,X0_47,X0_48) = iProver_top
    | m1_subset_1(X0_48,u1_struct_0(sK2)) != iProver_top
    | m1_subset_1(sK0(sK2,X0_47,X0_48),u1_struct_0(sK2)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1653])).

cnf(c_2740,plain,
    ( m1_subset_1(sK1(sK2,sK0(sK2,X0_47,X0_48),X1_47),u1_struct_0(sK2)) != iProver_top
    | m1_subset_1(X0_48,u1_struct_0(sK2)) != iProver_top
    | r1_lattice3(sK2,X1_47,sK0(sK2,X0_47,X0_48)) != iProver_top
    | r1_lattice3(sK2,X0_47,sK1(sK2,sK0(sK2,X0_47,X0_48),X1_47)) != iProver_top
    | r1_lattice3(sK2,X0_47,X0_48) = iProver_top
    | sK0(sK2,X0_47,X0_48) = k2_yellow_0(sK2,X1_47) ),
    inference(global_propositional_subsumption,[status(thm)],[c_2591,c_1719])).

cnf(c_2741,plain,
    ( sK0(sK2,X0_47,X0_48) = k2_yellow_0(sK2,X1_47)
    | r1_lattice3(sK2,X0_47,X0_48) = iProver_top
    | r1_lattice3(sK2,X0_47,sK1(sK2,sK0(sK2,X0_47,X0_48),X1_47)) != iProver_top
    | r1_lattice3(sK2,X1_47,sK0(sK2,X0_47,X0_48)) != iProver_top
    | m1_subset_1(X0_48,u1_struct_0(sK2)) != iProver_top
    | m1_subset_1(sK1(sK2,sK0(sK2,X0_47,X0_48),X1_47),u1_struct_0(sK2)) != iProver_top ),
    inference(renaming,[status(thm)],[c_2740])).

cnf(c_2753,plain,
    ( sK0(sK2,X0_47,X0_48) = k2_yellow_0(sK2,X0_47)
    | r1_lattice3(sK2,X0_47,X0_48) = iProver_top
    | r1_lattice3(sK2,X0_47,sK0(sK2,X0_47,X0_48)) != iProver_top
    | m1_subset_1(X0_48,u1_struct_0(sK2)) != iProver_top
    | m1_subset_1(sK1(sK2,sK0(sK2,X0_47,X0_48),X0_47),u1_struct_0(sK2)) != iProver_top
    | m1_subset_1(sK0(sK2,X0_47,X0_48),u1_struct_0(sK2)) != iProver_top ),
    inference(superposition,[status(thm)],[c_1981,c_2741])).

cnf(c_2926,plain,
    ( m1_subset_1(sK1(sK2,sK0(sK2,X0_47,X0_48),X0_47),u1_struct_0(sK2)) != iProver_top
    | m1_subset_1(X0_48,u1_struct_0(sK2)) != iProver_top
    | r1_lattice3(sK2,X0_47,sK0(sK2,X0_47,X0_48)) != iProver_top
    | r1_lattice3(sK2,X0_47,X0_48) = iProver_top
    | sK0(sK2,X0_47,X0_48) = k2_yellow_0(sK2,X0_47) ),
    inference(global_propositional_subsumption,[status(thm)],[c_2753,c_1719])).

cnf(c_2927,plain,
    ( sK0(sK2,X0_47,X0_48) = k2_yellow_0(sK2,X0_47)
    | r1_lattice3(sK2,X0_47,X0_48) = iProver_top
    | r1_lattice3(sK2,X0_47,sK0(sK2,X0_47,X0_48)) != iProver_top
    | m1_subset_1(X0_48,u1_struct_0(sK2)) != iProver_top
    | m1_subset_1(sK1(sK2,sK0(sK2,X0_47,X0_48),X0_47),u1_struct_0(sK2)) != iProver_top ),
    inference(renaming,[status(thm)],[c_2926])).

cnf(c_2938,plain,
    ( sK0(sK2,X0_47,X0_48) = k2_yellow_0(sK2,X0_47)
    | r1_lattice3(sK2,X0_47,X0_48) = iProver_top
    | r1_lattice3(sK2,X0_47,sK0(sK2,X0_47,X0_48)) != iProver_top
    | m1_subset_1(X0_48,u1_struct_0(sK2)) != iProver_top
    | m1_subset_1(sK0(sK2,X0_47,X0_48),u1_struct_0(sK2)) != iProver_top ),
    inference(superposition,[status(thm)],[c_1980,c_2927])).

cnf(c_3048,plain,
    ( m1_subset_1(X0_48,u1_struct_0(sK2)) != iProver_top
    | r1_lattice3(sK2,X0_47,sK0(sK2,X0_47,X0_48)) != iProver_top
    | r1_lattice3(sK2,X0_47,X0_48) = iProver_top
    | sK0(sK2,X0_47,X0_48) = k2_yellow_0(sK2,X0_47) ),
    inference(global_propositional_subsumption,[status(thm)],[c_2938,c_1719])).

cnf(c_3049,plain,
    ( sK0(sK2,X0_47,X0_48) = k2_yellow_0(sK2,X0_47)
    | r1_lattice3(sK2,X0_47,X0_48) = iProver_top
    | r1_lattice3(sK2,X0_47,sK0(sK2,X0_47,X0_48)) != iProver_top
    | m1_subset_1(X0_48,u1_struct_0(sK2)) != iProver_top ),
    inference(renaming,[status(thm)],[c_3048])).

cnf(c_9,plain,
    ( ~ r1_lattice3(X0,X1,X2)
    | r2_yellow_0(X0,X1)
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | m1_subset_1(sK1(X0,X2,X1),u1_struct_0(X0))
    | ~ v5_orders_2(X0)
    | ~ l1_orders_2(X0) ),
    inference(cnf_transformation,[],[f41])).

cnf(c_493,plain,
    ( ~ r1_lattice3(X0,X1,X2)
    | r2_yellow_0(X0,X1)
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | m1_subset_1(sK1(X0,X2,X1),u1_struct_0(X0))
    | ~ l1_orders_2(X0)
    | sK2 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_9,c_20])).

cnf(c_494,plain,
    ( ~ r1_lattice3(sK2,X0,X1)
    | r2_yellow_0(sK2,X0)
    | ~ m1_subset_1(X1,u1_struct_0(sK2))
    | m1_subset_1(sK1(sK2,X1,X0),u1_struct_0(sK2))
    | ~ l1_orders_2(sK2) ),
    inference(unflattening,[status(thm)],[c_493])).

cnf(c_498,plain,
    ( m1_subset_1(sK1(sK2,X1,X0),u1_struct_0(sK2))
    | ~ m1_subset_1(X1,u1_struct_0(sK2))
    | r2_yellow_0(sK2,X0)
    | ~ r1_lattice3(sK2,X0,X1) ),
    inference(global_propositional_subsumption,[status(thm)],[c_494,c_19])).

cnf(c_499,plain,
    ( ~ r1_lattice3(sK2,X0,X1)
    | r2_yellow_0(sK2,X0)
    | ~ m1_subset_1(X1,u1_struct_0(sK2))
    | m1_subset_1(sK1(sK2,X1,X0),u1_struct_0(sK2)) ),
    inference(renaming,[status(thm)],[c_498])).

cnf(c_1656,plain,
    ( ~ r1_lattice3(sK2,X0_47,X0_48)
    | r2_yellow_0(sK2,X0_47)
    | ~ m1_subset_1(X0_48,u1_struct_0(sK2))
    | m1_subset_1(sK1(sK2,X0_48,X0_47),u1_struct_0(sK2)) ),
    inference(subtyping,[status(esa)],[c_499])).

cnf(c_1983,plain,
    ( r1_lattice3(sK2,X0_47,X0_48) != iProver_top
    | r2_yellow_0(sK2,X0_47) = iProver_top
    | m1_subset_1(X0_48,u1_struct_0(sK2)) != iProver_top
    | m1_subset_1(sK1(sK2,X0_48,X0_47),u1_struct_0(sK2)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1656])).

cnf(c_8,plain,
    ( ~ r1_lattice3(X0,X1,X2)
    | r1_lattice3(X0,X1,sK1(X0,X2,X1))
    | r2_yellow_0(X0,X1)
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | ~ v5_orders_2(X0)
    | ~ l1_orders_2(X0) ),
    inference(cnf_transformation,[],[f42])).

cnf(c_517,plain,
    ( ~ r1_lattice3(X0,X1,X2)
    | r1_lattice3(X0,X1,sK1(X0,X2,X1))
    | r2_yellow_0(X0,X1)
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | ~ l1_orders_2(X0)
    | sK2 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_8,c_20])).

cnf(c_518,plain,
    ( ~ r1_lattice3(sK2,X0,X1)
    | r1_lattice3(sK2,X0,sK1(sK2,X1,X0))
    | r2_yellow_0(sK2,X0)
    | ~ m1_subset_1(X1,u1_struct_0(sK2))
    | ~ l1_orders_2(sK2) ),
    inference(unflattening,[status(thm)],[c_517])).

cnf(c_522,plain,
    ( ~ m1_subset_1(X1,u1_struct_0(sK2))
    | r2_yellow_0(sK2,X0)
    | r1_lattice3(sK2,X0,sK1(sK2,X1,X0))
    | ~ r1_lattice3(sK2,X0,X1) ),
    inference(global_propositional_subsumption,[status(thm)],[c_518,c_19])).

cnf(c_523,plain,
    ( ~ r1_lattice3(sK2,X0,X1)
    | r1_lattice3(sK2,X0,sK1(sK2,X1,X0))
    | r2_yellow_0(sK2,X0)
    | ~ m1_subset_1(X1,u1_struct_0(sK2)) ),
    inference(renaming,[status(thm)],[c_522])).

cnf(c_1655,plain,
    ( ~ r1_lattice3(sK2,X0_47,X0_48)
    | r1_lattice3(sK2,X0_47,sK1(sK2,X0_48,X0_47))
    | r2_yellow_0(sK2,X0_47)
    | ~ m1_subset_1(X0_48,u1_struct_0(sK2)) ),
    inference(subtyping,[status(esa)],[c_523])).

cnf(c_1984,plain,
    ( r1_lattice3(sK2,X0_47,X0_48) != iProver_top
    | r1_lattice3(sK2,X0_47,sK1(sK2,X0_48,X0_47)) = iProver_top
    | r2_yellow_0(sK2,X0_47) = iProver_top
    | m1_subset_1(X0_48,u1_struct_0(sK2)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1655])).

cnf(c_7,plain,
    ( ~ r1_lattice3(X0,X1,X2)
    | ~ r1_orders_2(X0,sK1(X0,X2,X1),X2)
    | r2_yellow_0(X0,X1)
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | ~ v5_orders_2(X0)
    | ~ l1_orders_2(X0) ),
    inference(cnf_transformation,[],[f43])).

cnf(c_541,plain,
    ( ~ r1_lattice3(X0,X1,X2)
    | ~ r1_orders_2(X0,sK1(X0,X2,X1),X2)
    | r2_yellow_0(X0,X1)
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | ~ l1_orders_2(X0)
    | sK2 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_7,c_20])).

cnf(c_542,plain,
    ( ~ r1_lattice3(sK2,X0,X1)
    | ~ r1_orders_2(sK2,sK1(sK2,X1,X0),X1)
    | r2_yellow_0(sK2,X0)
    | ~ m1_subset_1(X1,u1_struct_0(sK2))
    | ~ l1_orders_2(sK2) ),
    inference(unflattening,[status(thm)],[c_541])).

cnf(c_546,plain,
    ( ~ m1_subset_1(X1,u1_struct_0(sK2))
    | r2_yellow_0(sK2,X0)
    | ~ r1_orders_2(sK2,sK1(sK2,X1,X0),X1)
    | ~ r1_lattice3(sK2,X0,X1) ),
    inference(global_propositional_subsumption,[status(thm)],[c_542,c_19])).

cnf(c_547,plain,
    ( ~ r1_lattice3(sK2,X0,X1)
    | ~ r1_orders_2(sK2,sK1(sK2,X1,X0),X1)
    | r2_yellow_0(sK2,X0)
    | ~ m1_subset_1(X1,u1_struct_0(sK2)) ),
    inference(renaming,[status(thm)],[c_546])).

cnf(c_1654,plain,
    ( ~ r1_lattice3(sK2,X0_47,X0_48)
    | ~ r1_orders_2(sK2,sK1(sK2,X0_48,X0_47),X0_48)
    | r2_yellow_0(sK2,X0_47)
    | ~ m1_subset_1(X0_48,u1_struct_0(sK2)) ),
    inference(subtyping,[status(esa)],[c_547])).

cnf(c_1985,plain,
    ( r1_lattice3(sK2,X0_47,X0_48) != iProver_top
    | r1_orders_2(sK2,sK1(sK2,X0_48,X0_47),X0_48) != iProver_top
    | r2_yellow_0(sK2,X0_47) = iProver_top
    | m1_subset_1(X0_48,u1_struct_0(sK2)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1654])).

cnf(c_2590,plain,
    ( r1_lattice3(sK2,X0_47,X0_48) = iProver_top
    | r1_lattice3(sK2,X0_47,sK1(sK2,sK0(sK2,X0_47,X0_48),X1_47)) != iProver_top
    | r1_lattice3(sK2,X1_47,sK0(sK2,X0_47,X0_48)) != iProver_top
    | r2_yellow_0(sK2,X1_47) = iProver_top
    | m1_subset_1(X0_48,u1_struct_0(sK2)) != iProver_top
    | m1_subset_1(sK1(sK2,sK0(sK2,X0_47,X0_48),X1_47),u1_struct_0(sK2)) != iProver_top
    | m1_subset_1(sK0(sK2,X0_47,X0_48),u1_struct_0(sK2)) != iProver_top ),
    inference(superposition,[status(thm)],[c_1988,c_1985])).

cnf(c_2696,plain,
    ( m1_subset_1(sK1(sK2,sK0(sK2,X0_47,X0_48),X1_47),u1_struct_0(sK2)) != iProver_top
    | m1_subset_1(X0_48,u1_struct_0(sK2)) != iProver_top
    | r2_yellow_0(sK2,X1_47) = iProver_top
    | r1_lattice3(sK2,X1_47,sK0(sK2,X0_47,X0_48)) != iProver_top
    | r1_lattice3(sK2,X0_47,sK1(sK2,sK0(sK2,X0_47,X0_48),X1_47)) != iProver_top
    | r1_lattice3(sK2,X0_47,X0_48) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_2590,c_1719])).

cnf(c_2697,plain,
    ( r1_lattice3(sK2,X0_47,X0_48) = iProver_top
    | r1_lattice3(sK2,X0_47,sK1(sK2,sK0(sK2,X0_47,X0_48),X1_47)) != iProver_top
    | r1_lattice3(sK2,X1_47,sK0(sK2,X0_47,X0_48)) != iProver_top
    | r2_yellow_0(sK2,X1_47) = iProver_top
    | m1_subset_1(X0_48,u1_struct_0(sK2)) != iProver_top
    | m1_subset_1(sK1(sK2,sK0(sK2,X0_47,X0_48),X1_47),u1_struct_0(sK2)) != iProver_top ),
    inference(renaming,[status(thm)],[c_2696])).

cnf(c_2708,plain,
    ( r1_lattice3(sK2,X0_47,X0_48) = iProver_top
    | r1_lattice3(sK2,X0_47,sK0(sK2,X0_47,X0_48)) != iProver_top
    | r2_yellow_0(sK2,X0_47) = iProver_top
    | m1_subset_1(X0_48,u1_struct_0(sK2)) != iProver_top
    | m1_subset_1(sK1(sK2,sK0(sK2,X0_47,X0_48),X0_47),u1_struct_0(sK2)) != iProver_top
    | m1_subset_1(sK0(sK2,X0_47,X0_48),u1_struct_0(sK2)) != iProver_top ),
    inference(superposition,[status(thm)],[c_1984,c_2697])).

cnf(c_2833,plain,
    ( m1_subset_1(sK1(sK2,sK0(sK2,X0_47,X0_48),X0_47),u1_struct_0(sK2)) != iProver_top
    | m1_subset_1(X0_48,u1_struct_0(sK2)) != iProver_top
    | r2_yellow_0(sK2,X0_47) = iProver_top
    | r1_lattice3(sK2,X0_47,sK0(sK2,X0_47,X0_48)) != iProver_top
    | r1_lattice3(sK2,X0_47,X0_48) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_2708,c_1719])).

cnf(c_2834,plain,
    ( r1_lattice3(sK2,X0_47,X0_48) = iProver_top
    | r1_lattice3(sK2,X0_47,sK0(sK2,X0_47,X0_48)) != iProver_top
    | r2_yellow_0(sK2,X0_47) = iProver_top
    | m1_subset_1(X0_48,u1_struct_0(sK2)) != iProver_top
    | m1_subset_1(sK1(sK2,sK0(sK2,X0_47,X0_48),X0_47),u1_struct_0(sK2)) != iProver_top ),
    inference(renaming,[status(thm)],[c_2833])).

cnf(c_2844,plain,
    ( r1_lattice3(sK2,X0_47,X0_48) = iProver_top
    | r1_lattice3(sK2,X0_47,sK0(sK2,X0_47,X0_48)) != iProver_top
    | r2_yellow_0(sK2,X0_47) = iProver_top
    | m1_subset_1(X0_48,u1_struct_0(sK2)) != iProver_top
    | m1_subset_1(sK0(sK2,X0_47,X0_48),u1_struct_0(sK2)) != iProver_top ),
    inference(superposition,[status(thm)],[c_1983,c_2834])).

cnf(c_2915,plain,
    ( m1_subset_1(X0_48,u1_struct_0(sK2)) != iProver_top
    | r2_yellow_0(sK2,X0_47) = iProver_top
    | r1_lattice3(sK2,X0_47,sK0(sK2,X0_47,X0_48)) != iProver_top
    | r1_lattice3(sK2,X0_47,X0_48) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_2844,c_1719])).

cnf(c_2916,plain,
    ( r1_lattice3(sK2,X0_47,X0_48) = iProver_top
    | r1_lattice3(sK2,X0_47,sK0(sK2,X0_47,X0_48)) != iProver_top
    | r2_yellow_0(sK2,X0_47) = iProver_top
    | m1_subset_1(X0_48,u1_struct_0(sK2)) != iProver_top ),
    inference(renaming,[status(thm)],[c_2915])).

cnf(c_1668,plain,
    ( r1_orders_2(sK2,X0_48,X0_48)
    | ~ m1_subset_1(X0_48,u1_struct_0(sK2))
    | ~ sP1_iProver_split ),
    inference(splitting,[splitting(split),new_symbols(definition,[sP1_iProver_split])],[c_1662])).

cnf(c_1976,plain,
    ( r1_orders_2(sK2,X0_48,X0_48) = iProver_top
    | m1_subset_1(X0_48,u1_struct_0(sK2)) != iProver_top
    | sP1_iProver_split != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1668])).

cnf(c_1756,plain,
    ( ~ m1_subset_1(X0_48,u1_struct_0(sK2))
    | r1_orders_2(sK2,X0_48,X0_48) ),
    inference(global_propositional_subsumption,[status(thm)],[c_1668,c_18,c_1669,c_1693])).

cnf(c_1757,plain,
    ( r1_orders_2(sK2,X0_48,X0_48)
    | ~ m1_subset_1(X0_48,u1_struct_0(sK2)) ),
    inference(renaming,[status(thm)],[c_1756])).

cnf(c_1758,plain,
    ( r1_orders_2(sK2,X0_48,X0_48) = iProver_top
    | m1_subset_1(X0_48,u1_struct_0(sK2)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1757])).

cnf(c_2255,plain,
    ( m1_subset_1(X0_48,u1_struct_0(sK2)) != iProver_top
    | r1_orders_2(sK2,X0_48,X0_48) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_1976,c_1758])).

cnf(c_2256,plain,
    ( r1_orders_2(sK2,X0_48,X0_48) = iProver_top
    | m1_subset_1(X0_48,u1_struct_0(sK2)) != iProver_top ),
    inference(renaming,[status(thm)],[c_2255])).

cnf(c_2494,plain,
    ( r1_lattice3(sK2,X0_47,X0_48) != iProver_top
    | r1_orders_2(sK2,sK1(sK2,X0_48,X0_47),sK1(sK2,X0_48,X0_47)) = iProver_top
    | r2_yellow_0(sK2,X0_47) = iProver_top
    | m1_subset_1(X0_48,u1_struct_0(sK2)) != iProver_top ),
    inference(superposition,[status(thm)],[c_1983,c_2256])).

cnf(c_2411,plain,
    ( k2_yellow_0(sK2,X0_47) = X0_48
    | r1_lattice3(sK2,X0_47,X0_48) != iProver_top
    | r1_orders_2(sK2,sK1(sK2,X0_48,X0_47),sK1(sK2,X0_48,X0_47)) = iProver_top
    | m1_subset_1(X0_48,u1_struct_0(sK2)) != iProver_top ),
    inference(superposition,[status(thm)],[c_1980,c_2256])).

cnf(c_1986,plain,
    ( r1_lattice3(sK2,X0_47,X0_48) = iProver_top
    | m1_subset_1(X0_48,u1_struct_0(sK2)) != iProver_top
    | m1_subset_1(sK0(sK2,X0_47,X0_48),u1_struct_0(sK2)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1653])).

cnf(c_2311,plain,
    ( r1_lattice3(sK2,X0_47,X0_48) = iProver_top
    | r1_orders_2(sK2,sK0(sK2,X0_47,X0_48),sK0(sK2,X0_47,X0_48)) = iProver_top
    | m1_subset_1(X0_48,u1_struct_0(sK2)) != iProver_top ),
    inference(superposition,[status(thm)],[c_1986,c_2256])).

cnf(c_1663,negated_conjecture,
    ( m1_subset_1(sK3,u1_struct_0(sK2)) ),
    inference(subtyping,[status(esa)],[c_18])).

cnf(c_1974,plain,
    ( m1_subset_1(sK3,u1_struct_0(sK2)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1663])).

cnf(c_2262,plain,
    ( r1_orders_2(sK2,sK3,sK3) = iProver_top ),
    inference(superposition,[status(thm)],[c_1974,c_2256])).

cnf(c_17,negated_conjecture,
    ( m1_subset_1(sK4,u1_struct_0(sK2)) ),
    inference(cnf_transformation,[],[f49])).

cnf(c_1664,negated_conjecture,
    ( m1_subset_1(sK4,u1_struct_0(sK2)) ),
    inference(subtyping,[status(esa)],[c_17])).

cnf(c_1973,plain,
    ( m1_subset_1(sK4,u1_struct_0(sK2)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1664])).

cnf(c_2261,plain,
    ( r1_orders_2(sK2,sK4,sK4) = iProver_top ),
    inference(superposition,[status(thm)],[c_1973,c_2256])).

cnf(c_1977,plain,
    ( m1_subset_1(X0_48,u1_struct_0(sK2)) != iProver_top
    | sP0_iProver_split != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1667])).

cnf(c_27,plain,
    ( m1_subset_1(sK3,u1_struct_0(sK2)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_18])).

cnf(c_1692,plain,
    ( m1_subset_1(X0_48,u1_struct_0(sK2)) != iProver_top
    | sP0_iProver_split != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1667])).

cnf(c_1694,plain,
    ( m1_subset_1(sK3,u1_struct_0(sK2)) != iProver_top
    | sP0_iProver_split != iProver_top ),
    inference(instantiation,[status(thm)],[c_1692])).

cnf(c_2547,plain,
    ( sP0_iProver_split != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_1977,c_27,c_1694])).

cnf(c_1975,plain,
    ( sP1_iProver_split = iProver_top
    | sP0_iProver_split = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1669])).

cnf(c_1688,plain,
    ( sP1_iProver_split = iProver_top
    | sP0_iProver_split = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1669])).

cnf(c_2553,plain,
    ( sP1_iProver_split = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_1975,c_27,c_1688,c_1694])).

cnf(c_3,plain,
    ( r1_lattice3(X0,X1,X2)
    | ~ r1_orders_2(X0,X2,sK0(X0,X1,X2))
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | ~ l1_orders_2(X0) ),
    inference(cnf_transformation,[],[f35])).

cnf(c_654,plain,
    ( r1_lattice3(X0,X1,X2)
    | ~ r1_orders_2(X0,X2,sK0(X0,X1,X2))
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | sK2 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_3,c_19])).

cnf(c_655,plain,
    ( r1_lattice3(sK2,X0,X1)
    | ~ r1_orders_2(sK2,X1,sK0(sK2,X0,X1))
    | ~ m1_subset_1(X1,u1_struct_0(sK2)) ),
    inference(unflattening,[status(thm)],[c_654])).

cnf(c_1652,plain,
    ( r1_lattice3(sK2,X0_47,X0_48)
    | ~ r1_orders_2(sK2,X0_48,sK0(sK2,X0_47,X0_48))
    | ~ m1_subset_1(X0_48,u1_struct_0(sK2)) ),
    inference(subtyping,[status(esa)],[c_655])).

cnf(c_1987,plain,
    ( r1_lattice3(sK2,X0_47,X0_48) = iProver_top
    | r1_orders_2(sK2,X0_48,sK0(sK2,X0_47,X0_48)) != iProver_top
    | m1_subset_1(X0_48,u1_struct_0(sK2)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1652])).

cnf(c_13,plain,
    ( ~ r1_lattice3(X0,X1,X2)
    | r1_orders_2(X0,X2,k2_yellow_0(X0,X1))
    | ~ r2_yellow_0(X0,X1)
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | ~ m1_subset_1(k2_yellow_0(X0,X1),u1_struct_0(X0))
    | ~ v5_orders_2(X0)
    | ~ l1_orders_2(X0) ),
    inference(cnf_transformation,[],[f52])).

cnf(c_394,plain,
    ( ~ r1_lattice3(X0,X1,X2)
    | r1_orders_2(X0,X2,k2_yellow_0(X0,X1))
    | ~ r2_yellow_0(X0,X1)
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | ~ m1_subset_1(k2_yellow_0(X0,X1),u1_struct_0(X0))
    | ~ l1_orders_2(X0)
    | sK2 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_13,c_20])).

cnf(c_395,plain,
    ( ~ r1_lattice3(sK2,X0,X1)
    | r1_orders_2(sK2,X1,k2_yellow_0(sK2,X0))
    | ~ r2_yellow_0(sK2,X0)
    | ~ m1_subset_1(X1,u1_struct_0(sK2))
    | ~ m1_subset_1(k2_yellow_0(sK2,X0),u1_struct_0(sK2))
    | ~ l1_orders_2(sK2) ),
    inference(unflattening,[status(thm)],[c_394])).

cnf(c_399,plain,
    ( ~ m1_subset_1(k2_yellow_0(sK2,X0),u1_struct_0(sK2))
    | ~ m1_subset_1(X1,u1_struct_0(sK2))
    | ~ r2_yellow_0(sK2,X0)
    | r1_orders_2(sK2,X1,k2_yellow_0(sK2,X0))
    | ~ r1_lattice3(sK2,X0,X1) ),
    inference(global_propositional_subsumption,[status(thm)],[c_395,c_19])).

cnf(c_400,plain,
    ( ~ r1_lattice3(sK2,X0,X1)
    | r1_orders_2(sK2,X1,k2_yellow_0(sK2,X0))
    | ~ r2_yellow_0(sK2,X0)
    | ~ m1_subset_1(X1,u1_struct_0(sK2))
    | ~ m1_subset_1(k2_yellow_0(sK2,X0),u1_struct_0(sK2)) ),
    inference(renaming,[status(thm)],[c_399])).

cnf(c_1660,plain,
    ( ~ r1_lattice3(sK2,X0_47,X0_48)
    | r1_orders_2(sK2,X0_48,k2_yellow_0(sK2,X0_47))
    | ~ r2_yellow_0(sK2,X0_47)
    | ~ m1_subset_1(X0_48,u1_struct_0(sK2))
    | ~ m1_subset_1(k2_yellow_0(sK2,X0_47),u1_struct_0(sK2)) ),
    inference(subtyping,[status(esa)],[c_400])).

cnf(c_1979,plain,
    ( r1_lattice3(sK2,X0_47,X0_48) != iProver_top
    | r1_orders_2(sK2,X0_48,k2_yellow_0(sK2,X0_47)) = iProver_top
    | r2_yellow_0(sK2,X0_47) != iProver_top
    | m1_subset_1(X0_48,u1_struct_0(sK2)) != iProver_top
    | m1_subset_1(k2_yellow_0(sK2,X0_47),u1_struct_0(sK2)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1660])).

cnf(c_14,plain,
    ( r1_lattice3(X0,X1,k2_yellow_0(X0,X1))
    | ~ r2_yellow_0(X0,X1)
    | ~ m1_subset_1(k2_yellow_0(X0,X1),u1_struct_0(X0))
    | ~ v5_orders_2(X0)
    | ~ l1_orders_2(X0) ),
    inference(cnf_transformation,[],[f53])).

cnf(c_373,plain,
    ( r1_lattice3(X0,X1,k2_yellow_0(X0,X1))
    | ~ r2_yellow_0(X0,X1)
    | ~ m1_subset_1(k2_yellow_0(X0,X1),u1_struct_0(X0))
    | ~ l1_orders_2(X0)
    | sK2 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_14,c_20])).

cnf(c_374,plain,
    ( r1_lattice3(sK2,X0,k2_yellow_0(sK2,X0))
    | ~ r2_yellow_0(sK2,X0)
    | ~ m1_subset_1(k2_yellow_0(sK2,X0),u1_struct_0(sK2))
    | ~ l1_orders_2(sK2) ),
    inference(unflattening,[status(thm)],[c_373])).

cnf(c_378,plain,
    ( ~ m1_subset_1(k2_yellow_0(sK2,X0),u1_struct_0(sK2))
    | ~ r2_yellow_0(sK2,X0)
    | r1_lattice3(sK2,X0,k2_yellow_0(sK2,X0)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_374,c_19])).

cnf(c_379,plain,
    ( r1_lattice3(sK2,X0,k2_yellow_0(sK2,X0))
    | ~ r2_yellow_0(sK2,X0)
    | ~ m1_subset_1(k2_yellow_0(sK2,X0),u1_struct_0(sK2)) ),
    inference(renaming,[status(thm)],[c_378])).

cnf(c_1661,plain,
    ( r1_lattice3(sK2,X0_47,k2_yellow_0(sK2,X0_47))
    | ~ r2_yellow_0(sK2,X0_47)
    | ~ m1_subset_1(k2_yellow_0(sK2,X0_47),u1_struct_0(sK2)) ),
    inference(subtyping,[status(esa)],[c_379])).

cnf(c_1978,plain,
    ( r1_lattice3(sK2,X0_47,k2_yellow_0(sK2,X0_47)) = iProver_top
    | r2_yellow_0(sK2,X0_47) != iProver_top
    | m1_subset_1(k2_yellow_0(sK2,X0_47),u1_struct_0(sK2)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1661])).

cnf(c_15,negated_conjecture,
    ( sK3 != sK4 ),
    inference(cnf_transformation,[],[f51])).

cnf(c_1666,negated_conjecture,
    ( sK3 != sK4 ),
    inference(subtyping,[status(esa)],[c_15])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.10/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.10/0.12  % Command    : iproveropt_run.sh %d %s
% 0.12/0.33  % Computer   : n022.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.33  % CPULimit   : 60
% 0.12/0.33  % WCLimit    : 600
% 0.12/0.33  % DateTime   : Tue Dec  1 11:42:11 EST 2020
% 0.12/0.33  % CPUTime    : 
% 0.12/0.34  % Running in FOF mode
% 1.35/0.99  % SZS status Started for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.35/0.99  
% 1.35/0.99  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 1.35/0.99  
% 1.35/0.99  ------  iProver source info
% 1.35/0.99  
% 1.35/0.99  git: date: 2020-06-30 10:37:57 +0100
% 1.35/0.99  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 1.35/0.99  git: non_committed_changes: false
% 1.35/0.99  git: last_make_outside_of_git: false
% 1.35/0.99  
% 1.35/0.99  ------ 
% 1.35/0.99  
% 1.35/0.99  ------ Input Options
% 1.35/0.99  
% 1.35/0.99  --out_options                           all
% 1.35/0.99  --tptp_safe_out                         true
% 1.35/0.99  --problem_path                          ""
% 1.35/0.99  --include_path                          ""
% 1.35/0.99  --clausifier                            res/vclausify_rel
% 1.35/0.99  --clausifier_options                    --mode clausify
% 1.35/0.99  --stdin                                 false
% 1.35/0.99  --stats_out                             all
% 1.35/0.99  
% 1.35/0.99  ------ General Options
% 1.35/0.99  
% 1.35/0.99  --fof                                   false
% 1.35/0.99  --time_out_real                         305.
% 1.35/0.99  --time_out_virtual                      -1.
% 1.35/0.99  --symbol_type_check                     false
% 1.35/0.99  --clausify_out                          false
% 1.35/0.99  --sig_cnt_out                           false
% 1.35/0.99  --trig_cnt_out                          false
% 1.35/0.99  --trig_cnt_out_tolerance                1.
% 1.35/0.99  --trig_cnt_out_sk_spl                   false
% 1.35/0.99  --abstr_cl_out                          false
% 1.35/0.99  
% 1.35/0.99  ------ Global Options
% 1.35/0.99  
% 1.35/0.99  --schedule                              default
% 1.35/0.99  --add_important_lit                     false
% 1.35/0.99  --prop_solver_per_cl                    1000
% 1.35/0.99  --min_unsat_core                        false
% 1.35/0.99  --soft_assumptions                      false
% 1.35/0.99  --soft_lemma_size                       3
% 1.35/0.99  --prop_impl_unit_size                   0
% 1.35/0.99  --prop_impl_unit                        []
% 1.35/0.99  --share_sel_clauses                     true
% 1.35/0.99  --reset_solvers                         false
% 1.35/0.99  --bc_imp_inh                            [conj_cone]
% 1.35/0.99  --conj_cone_tolerance                   3.
% 1.35/0.99  --extra_neg_conj                        none
% 1.35/0.99  --large_theory_mode                     true
% 1.35/0.99  --prolific_symb_bound                   200
% 1.35/0.99  --lt_threshold                          2000
% 1.35/0.99  --clause_weak_htbl                      true
% 1.35/0.99  --gc_record_bc_elim                     false
% 1.35/0.99  
% 1.35/0.99  ------ Preprocessing Options
% 1.35/0.99  
% 1.35/0.99  --preprocessing_flag                    true
% 1.35/0.99  --time_out_prep_mult                    0.1
% 1.35/0.99  --splitting_mode                        input
% 1.35/0.99  --splitting_grd                         true
% 1.35/0.99  --splitting_cvd                         false
% 1.35/0.99  --splitting_cvd_svl                     false
% 1.35/0.99  --splitting_nvd                         32
% 1.35/0.99  --sub_typing                            true
% 1.35/0.99  --prep_gs_sim                           true
% 1.35/0.99  --prep_unflatten                        true
% 1.35/0.99  --prep_res_sim                          true
% 1.35/0.99  --prep_upred                            true
% 1.35/0.99  --prep_sem_filter                       exhaustive
% 1.35/0.99  --prep_sem_filter_out                   false
% 1.35/0.99  --pred_elim                             true
% 1.35/0.99  --res_sim_input                         true
% 1.35/0.99  --eq_ax_congr_red                       true
% 1.35/0.99  --pure_diseq_elim                       true
% 1.35/0.99  --brand_transform                       false
% 1.35/0.99  --non_eq_to_eq                          false
% 1.35/0.99  --prep_def_merge                        true
% 1.35/0.99  --prep_def_merge_prop_impl              false
% 1.35/0.99  --prep_def_merge_mbd                    true
% 1.35/0.99  --prep_def_merge_tr_red                 false
% 1.35/0.99  --prep_def_merge_tr_cl                  false
% 1.35/0.99  --smt_preprocessing                     true
% 1.35/0.99  --smt_ac_axioms                         fast
% 1.35/0.99  --preprocessed_out                      false
% 1.35/0.99  --preprocessed_stats                    false
% 1.35/0.99  
% 1.35/0.99  ------ Abstraction refinement Options
% 1.35/0.99  
% 1.35/0.99  --abstr_ref                             []
% 1.35/0.99  --abstr_ref_prep                        false
% 1.35/0.99  --abstr_ref_until_sat                   false
% 1.35/0.99  --abstr_ref_sig_restrict                funpre
% 1.35/0.99  --abstr_ref_af_restrict_to_split_sk     false
% 1.35/0.99  --abstr_ref_under                       []
% 1.35/0.99  
% 1.35/0.99  ------ SAT Options
% 1.35/0.99  
% 1.35/0.99  --sat_mode                              false
% 1.35/0.99  --sat_fm_restart_options                ""
% 1.35/0.99  --sat_gr_def                            false
% 1.35/0.99  --sat_epr_types                         true
% 1.35/0.99  --sat_non_cyclic_types                  false
% 1.35/0.99  --sat_finite_models                     false
% 1.35/0.99  --sat_fm_lemmas                         false
% 1.35/0.99  --sat_fm_prep                           false
% 1.35/0.99  --sat_fm_uc_incr                        true
% 1.35/0.99  --sat_out_model                         small
% 1.35/0.99  --sat_out_clauses                       false
% 1.35/0.99  
% 1.35/0.99  ------ QBF Options
% 1.35/0.99  
% 1.35/0.99  --qbf_mode                              false
% 1.35/0.99  --qbf_elim_univ                         false
% 1.35/0.99  --qbf_dom_inst                          none
% 1.35/0.99  --qbf_dom_pre_inst                      false
% 1.35/0.99  --qbf_sk_in                             false
% 1.35/0.99  --qbf_pred_elim                         true
% 1.35/0.99  --qbf_split                             512
% 1.35/0.99  
% 1.35/0.99  ------ BMC1 Options
% 1.35/0.99  
% 1.35/0.99  --bmc1_incremental                      false
% 1.35/0.99  --bmc1_axioms                           reachable_all
% 1.35/0.99  --bmc1_min_bound                        0
% 1.35/0.99  --bmc1_max_bound                        -1
% 1.35/0.99  --bmc1_max_bound_default                -1
% 1.35/0.99  --bmc1_symbol_reachability              true
% 1.35/0.99  --bmc1_property_lemmas                  false
% 1.35/0.99  --bmc1_k_induction                      false
% 1.35/0.99  --bmc1_non_equiv_states                 false
% 1.35/0.99  --bmc1_deadlock                         false
% 1.35/0.99  --bmc1_ucm                              false
% 1.35/0.99  --bmc1_add_unsat_core                   none
% 1.35/0.99  --bmc1_unsat_core_children              false
% 1.35/0.99  --bmc1_unsat_core_extrapolate_axioms    false
% 1.35/0.99  --bmc1_out_stat                         full
% 1.35/0.99  --bmc1_ground_init                      false
% 1.35/0.99  --bmc1_pre_inst_next_state              false
% 1.35/0.99  --bmc1_pre_inst_state                   false
% 1.35/0.99  --bmc1_pre_inst_reach_state             false
% 1.35/0.99  --bmc1_out_unsat_core                   false
% 1.35/0.99  --bmc1_aig_witness_out                  false
% 1.35/0.99  --bmc1_verbose                          false
% 1.35/0.99  --bmc1_dump_clauses_tptp                false
% 1.35/0.99  --bmc1_dump_unsat_core_tptp             false
% 1.35/0.99  --bmc1_dump_file                        -
% 1.35/0.99  --bmc1_ucm_expand_uc_limit              128
% 1.35/0.99  --bmc1_ucm_n_expand_iterations          6
% 1.35/0.99  --bmc1_ucm_extend_mode                  1
% 1.35/0.99  --bmc1_ucm_init_mode                    2
% 1.35/0.99  --bmc1_ucm_cone_mode                    none
% 1.35/0.99  --bmc1_ucm_reduced_relation_type        0
% 1.35/0.99  --bmc1_ucm_relax_model                  4
% 1.35/0.99  --bmc1_ucm_full_tr_after_sat            true
% 1.35/0.99  --bmc1_ucm_expand_neg_assumptions       false
% 1.35/0.99  --bmc1_ucm_layered_model                none
% 1.35/0.99  --bmc1_ucm_max_lemma_size               10
% 1.35/0.99  
% 1.35/0.99  ------ AIG Options
% 1.35/0.99  
% 1.35/0.99  --aig_mode                              false
% 1.35/0.99  
% 1.35/0.99  ------ Instantiation Options
% 1.35/0.99  
% 1.35/0.99  --instantiation_flag                    true
% 1.35/0.99  --inst_sos_flag                         false
% 1.35/0.99  --inst_sos_phase                        true
% 1.35/0.99  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 1.35/0.99  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 1.35/0.99  --inst_lit_sel_side                     num_symb
% 1.35/0.99  --inst_solver_per_active                1400
% 1.35/0.99  --inst_solver_calls_frac                1.
% 1.35/0.99  --inst_passive_queue_type               priority_queues
% 1.35/0.99  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 1.35/0.99  --inst_passive_queues_freq              [25;2]
% 1.35/0.99  --inst_dismatching                      true
% 1.35/0.99  --inst_eager_unprocessed_to_passive     true
% 1.35/0.99  --inst_prop_sim_given                   true
% 1.35/0.99  --inst_prop_sim_new                     false
% 1.35/0.99  --inst_subs_new                         false
% 1.35/0.99  --inst_eq_res_simp                      false
% 1.35/0.99  --inst_subs_given                       false
% 1.35/0.99  --inst_orphan_elimination               true
% 1.35/0.99  --inst_learning_loop_flag               true
% 1.35/0.99  --inst_learning_start                   3000
% 1.35/0.99  --inst_learning_factor                  2
% 1.35/0.99  --inst_start_prop_sim_after_learn       3
% 1.35/0.99  --inst_sel_renew                        solver
% 1.35/0.99  --inst_lit_activity_flag                true
% 1.35/0.99  --inst_restr_to_given                   false
% 1.35/0.99  --inst_activity_threshold               500
% 1.35/0.99  --inst_out_proof                        true
% 1.35/0.99  
% 1.35/0.99  ------ Resolution Options
% 1.35/0.99  
% 1.35/0.99  --resolution_flag                       true
% 1.35/0.99  --res_lit_sel                           adaptive
% 1.35/0.99  --res_lit_sel_side                      none
% 1.35/0.99  --res_ordering                          kbo
% 1.35/0.99  --res_to_prop_solver                    active
% 1.35/0.99  --res_prop_simpl_new                    false
% 1.35/0.99  --res_prop_simpl_given                  true
% 1.35/0.99  --res_passive_queue_type                priority_queues
% 1.35/0.99  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 1.35/0.99  --res_passive_queues_freq               [15;5]
% 1.35/0.99  --res_forward_subs                      full
% 1.35/0.99  --res_backward_subs                     full
% 1.35/0.99  --res_forward_subs_resolution           true
% 1.35/0.99  --res_backward_subs_resolution          true
% 1.35/0.99  --res_orphan_elimination                true
% 1.35/0.99  --res_time_limit                        2.
% 1.35/0.99  --res_out_proof                         true
% 1.35/0.99  
% 1.35/0.99  ------ Superposition Options
% 1.35/0.99  
% 1.35/0.99  --superposition_flag                    true
% 1.35/0.99  --sup_passive_queue_type                priority_queues
% 1.35/0.99  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 1.35/0.99  --sup_passive_queues_freq               [8;1;4]
% 1.35/0.99  --demod_completeness_check              fast
% 1.35/0.99  --demod_use_ground                      true
% 1.35/0.99  --sup_to_prop_solver                    passive
% 1.35/0.99  --sup_prop_simpl_new                    true
% 1.35/0.99  --sup_prop_simpl_given                  true
% 1.35/0.99  --sup_fun_splitting                     false
% 1.35/0.99  --sup_smt_interval                      50000
% 1.35/0.99  
% 1.35/0.99  ------ Superposition Simplification Setup
% 1.35/0.99  
% 1.35/0.99  --sup_indices_passive                   []
% 1.35/0.99  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 1.35/0.99  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 1.35/0.99  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 1.35/0.99  --sup_full_triv                         [TrivRules;PropSubs]
% 1.35/0.99  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 1.35/0.99  --sup_full_bw                           [BwDemod]
% 1.35/0.99  --sup_immed_triv                        [TrivRules]
% 1.35/0.99  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 1.35/0.99  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 1.35/0.99  --sup_immed_bw_main                     []
% 1.35/0.99  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 1.35/0.99  --sup_input_triv                        [Unflattening;TrivRules]
% 1.35/0.99  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 1.35/0.99  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 1.35/0.99  
% 1.35/0.99  ------ Combination Options
% 1.35/0.99  
% 1.35/0.99  --comb_res_mult                         3
% 1.35/0.99  --comb_sup_mult                         2
% 1.35/0.99  --comb_inst_mult                        10
% 1.35/0.99  
% 1.35/0.99  ------ Debug Options
% 1.35/0.99  
% 1.35/0.99  --dbg_backtrace                         false
% 1.35/0.99  --dbg_dump_prop_clauses                 false
% 1.35/0.99  --dbg_dump_prop_clauses_file            -
% 1.35/0.99  --dbg_out_stat                          false
% 1.35/0.99  ------ Parsing...
% 1.35/0.99  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 1.35/0.99  
% 1.35/0.99  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe:1:0s pe:2:0s pe:4:0s pe_e  sf_s  rm: 6 0s  sf_e  pe_s  pe_e 
% 1.35/0.99  
% 1.35/0.99  ------ Preprocessing... gs_s  sp: 2 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 1.35/0.99  
% 1.35/0.99  ------ Preprocessing... sf_s  rm: 7 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 1.35/0.99  ------ Proving...
% 1.35/0.99  ------ Problem Properties 
% 1.35/0.99  
% 1.35/0.99  
% 1.35/0.99  clauses                                 18
% 1.35/0.99  conjectures                             4
% 1.35/0.99  EPR                                     2
% 1.35/0.99  Horn                                    11
% 1.35/0.99  unary                                   4
% 1.35/0.99  binary                                  2
% 1.35/0.99  lits                                    54
% 1.35/0.99  lits eq                                 5
% 1.35/0.99  fd_pure                                 0
% 1.35/0.99  fd_pseudo                               0
% 1.35/0.99  fd_cond                                 0
% 1.35/0.99  fd_pseudo_cond                          3
% 1.35/0.99  AC symbols                              0
% 1.35/0.99  
% 1.35/0.99  ------ Schedule dynamic 5 is on 
% 1.35/0.99  
% 1.35/0.99  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" Time Limit: 10.
% 1.35/0.99  
% 1.35/0.99  
% 1.35/0.99  ------ 
% 1.35/0.99  Current options:
% 1.35/0.99  ------ 
% 1.35/0.99  
% 1.35/0.99  ------ Input Options
% 1.35/0.99  
% 1.35/0.99  --out_options                           all
% 1.35/0.99  --tptp_safe_out                         true
% 1.35/0.99  --problem_path                          ""
% 1.35/0.99  --include_path                          ""
% 1.35/0.99  --clausifier                            res/vclausify_rel
% 1.35/0.99  --clausifier_options                    --mode clausify
% 1.35/0.99  --stdin                                 false
% 1.35/0.99  --stats_out                             all
% 1.35/0.99  
% 1.35/0.99  ------ General Options
% 1.35/0.99  
% 1.35/0.99  --fof                                   false
% 1.35/0.99  --time_out_real                         305.
% 1.35/0.99  --time_out_virtual                      -1.
% 1.35/0.99  --symbol_type_check                     false
% 1.35/0.99  --clausify_out                          false
% 1.35/0.99  --sig_cnt_out                           false
% 1.35/0.99  --trig_cnt_out                          false
% 1.35/0.99  --trig_cnt_out_tolerance                1.
% 1.35/0.99  --trig_cnt_out_sk_spl                   false
% 1.35/0.99  --abstr_cl_out                          false
% 1.35/0.99  
% 1.35/0.99  ------ Global Options
% 1.35/0.99  
% 1.35/0.99  --schedule                              default
% 1.35/0.99  --add_important_lit                     false
% 1.35/0.99  --prop_solver_per_cl                    1000
% 1.35/0.99  --min_unsat_core                        false
% 1.35/0.99  --soft_assumptions                      false
% 1.35/0.99  --soft_lemma_size                       3
% 1.35/0.99  --prop_impl_unit_size                   0
% 1.35/0.99  --prop_impl_unit                        []
% 1.35/0.99  --share_sel_clauses                     true
% 1.35/0.99  --reset_solvers                         false
% 1.35/0.99  --bc_imp_inh                            [conj_cone]
% 1.35/0.99  --conj_cone_tolerance                   3.
% 1.35/0.99  --extra_neg_conj                        none
% 1.35/0.99  --large_theory_mode                     true
% 1.35/0.99  --prolific_symb_bound                   200
% 1.35/0.99  --lt_threshold                          2000
% 1.35/0.99  --clause_weak_htbl                      true
% 1.35/0.99  --gc_record_bc_elim                     false
% 1.35/0.99  
% 1.35/0.99  ------ Preprocessing Options
% 1.35/0.99  
% 1.35/0.99  --preprocessing_flag                    true
% 1.35/0.99  --time_out_prep_mult                    0.1
% 1.35/0.99  --splitting_mode                        input
% 1.35/0.99  --splitting_grd                         true
% 1.35/0.99  --splitting_cvd                         false
% 1.35/0.99  --splitting_cvd_svl                     false
% 1.35/0.99  --splitting_nvd                         32
% 1.35/0.99  --sub_typing                            true
% 1.35/0.99  --prep_gs_sim                           true
% 1.35/0.99  --prep_unflatten                        true
% 1.35/0.99  --prep_res_sim                          true
% 1.35/0.99  --prep_upred                            true
% 1.35/0.99  --prep_sem_filter                       exhaustive
% 1.35/0.99  --prep_sem_filter_out                   false
% 1.35/0.99  --pred_elim                             true
% 1.35/0.99  --res_sim_input                         true
% 1.35/0.99  --eq_ax_congr_red                       true
% 1.35/0.99  --pure_diseq_elim                       true
% 1.35/0.99  --brand_transform                       false
% 1.35/0.99  --non_eq_to_eq                          false
% 1.35/0.99  --prep_def_merge                        true
% 1.35/0.99  --prep_def_merge_prop_impl              false
% 1.35/0.99  --prep_def_merge_mbd                    true
% 1.35/0.99  --prep_def_merge_tr_red                 false
% 1.35/0.99  --prep_def_merge_tr_cl                  false
% 1.35/0.99  --smt_preprocessing                     true
% 1.35/0.99  --smt_ac_axioms                         fast
% 1.35/0.99  --preprocessed_out                      false
% 1.35/0.99  --preprocessed_stats                    false
% 1.35/0.99  
% 1.35/0.99  ------ Abstraction refinement Options
% 1.35/0.99  
% 1.35/0.99  --abstr_ref                             []
% 1.35/0.99  --abstr_ref_prep                        false
% 1.35/0.99  --abstr_ref_until_sat                   false
% 1.35/0.99  --abstr_ref_sig_restrict                funpre
% 1.35/0.99  --abstr_ref_af_restrict_to_split_sk     false
% 1.35/0.99  --abstr_ref_under                       []
% 1.35/0.99  
% 1.35/0.99  ------ SAT Options
% 1.35/0.99  
% 1.35/0.99  --sat_mode                              false
% 1.35/0.99  --sat_fm_restart_options                ""
% 1.35/0.99  --sat_gr_def                            false
% 1.35/0.99  --sat_epr_types                         true
% 1.35/0.99  --sat_non_cyclic_types                  false
% 1.35/0.99  --sat_finite_models                     false
% 1.35/0.99  --sat_fm_lemmas                         false
% 1.35/0.99  --sat_fm_prep                           false
% 1.35/0.99  --sat_fm_uc_incr                        true
% 1.35/0.99  --sat_out_model                         small
% 1.35/0.99  --sat_out_clauses                       false
% 1.35/0.99  
% 1.35/0.99  ------ QBF Options
% 1.35/0.99  
% 1.35/0.99  --qbf_mode                              false
% 1.35/0.99  --qbf_elim_univ                         false
% 1.35/0.99  --qbf_dom_inst                          none
% 1.35/0.99  --qbf_dom_pre_inst                      false
% 1.35/0.99  --qbf_sk_in                             false
% 1.35/0.99  --qbf_pred_elim                         true
% 1.35/0.99  --qbf_split                             512
% 1.35/0.99  
% 1.35/0.99  ------ BMC1 Options
% 1.35/0.99  
% 1.35/0.99  --bmc1_incremental                      false
% 1.35/0.99  --bmc1_axioms                           reachable_all
% 1.35/0.99  --bmc1_min_bound                        0
% 1.35/0.99  --bmc1_max_bound                        -1
% 1.35/0.99  --bmc1_max_bound_default                -1
% 1.35/0.99  --bmc1_symbol_reachability              true
% 1.35/0.99  --bmc1_property_lemmas                  false
% 1.35/0.99  --bmc1_k_induction                      false
% 1.35/0.99  --bmc1_non_equiv_states                 false
% 1.35/0.99  --bmc1_deadlock                         false
% 1.35/0.99  --bmc1_ucm                              false
% 1.35/0.99  --bmc1_add_unsat_core                   none
% 1.35/0.99  --bmc1_unsat_core_children              false
% 1.35/0.99  --bmc1_unsat_core_extrapolate_axioms    false
% 1.35/0.99  --bmc1_out_stat                         full
% 1.35/0.99  --bmc1_ground_init                      false
% 1.35/0.99  --bmc1_pre_inst_next_state              false
% 1.35/0.99  --bmc1_pre_inst_state                   false
% 1.35/0.99  --bmc1_pre_inst_reach_state             false
% 1.35/0.99  --bmc1_out_unsat_core                   false
% 1.35/0.99  --bmc1_aig_witness_out                  false
% 1.35/0.99  --bmc1_verbose                          false
% 1.35/0.99  --bmc1_dump_clauses_tptp                false
% 1.35/0.99  --bmc1_dump_unsat_core_tptp             false
% 1.35/0.99  --bmc1_dump_file                        -
% 1.35/0.99  --bmc1_ucm_expand_uc_limit              128
% 1.35/0.99  --bmc1_ucm_n_expand_iterations          6
% 1.35/0.99  --bmc1_ucm_extend_mode                  1
% 1.35/0.99  --bmc1_ucm_init_mode                    2
% 1.35/0.99  --bmc1_ucm_cone_mode                    none
% 1.35/0.99  --bmc1_ucm_reduced_relation_type        0
% 1.35/0.99  --bmc1_ucm_relax_model                  4
% 1.35/0.99  --bmc1_ucm_full_tr_after_sat            true
% 1.35/0.99  --bmc1_ucm_expand_neg_assumptions       false
% 1.35/0.99  --bmc1_ucm_layered_model                none
% 1.35/0.99  --bmc1_ucm_max_lemma_size               10
% 1.35/0.99  
% 1.35/0.99  ------ AIG Options
% 1.35/0.99  
% 1.35/0.99  --aig_mode                              false
% 1.35/0.99  
% 1.35/0.99  ------ Instantiation Options
% 1.35/0.99  
% 1.35/0.99  --instantiation_flag                    true
% 1.35/0.99  --inst_sos_flag                         false
% 1.35/0.99  --inst_sos_phase                        true
% 1.35/0.99  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 1.35/0.99  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 1.35/0.99  --inst_lit_sel_side                     none
% 1.35/0.99  --inst_solver_per_active                1400
% 1.35/0.99  --inst_solver_calls_frac                1.
% 1.35/0.99  --inst_passive_queue_type               priority_queues
% 1.35/0.99  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 1.35/0.99  --inst_passive_queues_freq              [25;2]
% 1.35/0.99  --inst_dismatching                      true
% 1.35/0.99  --inst_eager_unprocessed_to_passive     true
% 1.35/0.99  --inst_prop_sim_given                   true
% 1.35/0.99  --inst_prop_sim_new                     false
% 1.35/0.99  --inst_subs_new                         false
% 1.35/0.99  --inst_eq_res_simp                      false
% 1.35/0.99  --inst_subs_given                       false
% 1.35/0.99  --inst_orphan_elimination               true
% 1.35/0.99  --inst_learning_loop_flag               true
% 1.35/0.99  --inst_learning_start                   3000
% 1.35/0.99  --inst_learning_factor                  2
% 1.35/0.99  --inst_start_prop_sim_after_learn       3
% 1.35/0.99  --inst_sel_renew                        solver
% 1.35/0.99  --inst_lit_activity_flag                true
% 1.35/0.99  --inst_restr_to_given                   false
% 1.35/0.99  --inst_activity_threshold               500
% 1.35/0.99  --inst_out_proof                        true
% 1.35/0.99  
% 1.35/0.99  ------ Resolution Options
% 1.35/0.99  
% 1.35/0.99  --resolution_flag                       false
% 1.35/0.99  --res_lit_sel                           adaptive
% 1.35/0.99  --res_lit_sel_side                      none
% 1.35/0.99  --res_ordering                          kbo
% 1.35/0.99  --res_to_prop_solver                    active
% 1.35/0.99  --res_prop_simpl_new                    false
% 1.35/0.99  --res_prop_simpl_given                  true
% 1.35/0.99  --res_passive_queue_type                priority_queues
% 1.35/0.99  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 1.35/0.99  --res_passive_queues_freq               [15;5]
% 1.35/0.99  --res_forward_subs                      full
% 1.35/0.99  --res_backward_subs                     full
% 1.35/0.99  --res_forward_subs_resolution           true
% 1.35/0.99  --res_backward_subs_resolution          true
% 1.35/0.99  --res_orphan_elimination                true
% 1.35/0.99  --res_time_limit                        2.
% 1.35/0.99  --res_out_proof                         true
% 1.35/0.99  
% 1.35/0.99  ------ Superposition Options
% 1.35/0.99  
% 1.35/0.99  --superposition_flag                    true
% 1.35/0.99  --sup_passive_queue_type                priority_queues
% 1.35/0.99  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 1.35/0.99  --sup_passive_queues_freq               [8;1;4]
% 1.35/0.99  --demod_completeness_check              fast
% 1.35/0.99  --demod_use_ground                      true
% 1.35/0.99  --sup_to_prop_solver                    passive
% 1.35/0.99  --sup_prop_simpl_new                    true
% 1.35/0.99  --sup_prop_simpl_given                  true
% 1.35/0.99  --sup_fun_splitting                     false
% 1.35/0.99  --sup_smt_interval                      50000
% 1.35/0.99  
% 1.35/0.99  ------ Superposition Simplification Setup
% 1.35/0.99  
% 1.35/0.99  --sup_indices_passive                   []
% 1.35/0.99  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 1.35/0.99  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 1.35/0.99  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 1.35/0.99  --sup_full_triv                         [TrivRules;PropSubs]
% 1.35/0.99  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 1.35/0.99  --sup_full_bw                           [BwDemod]
% 1.35/0.99  --sup_immed_triv                        [TrivRules]
% 1.35/0.99  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 1.35/0.99  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 1.35/0.99  --sup_immed_bw_main                     []
% 1.35/0.99  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 1.35/0.99  --sup_input_triv                        [Unflattening;TrivRules]
% 1.35/0.99  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 1.35/0.99  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 1.35/0.99  
% 1.35/0.99  ------ Combination Options
% 1.35/0.99  
% 1.35/0.99  --comb_res_mult                         3
% 1.35/0.99  --comb_sup_mult                         2
% 1.35/0.99  --comb_inst_mult                        10
% 1.35/0.99  
% 1.35/0.99  ------ Debug Options
% 1.35/0.99  
% 1.35/0.99  --dbg_backtrace                         false
% 1.35/0.99  --dbg_dump_prop_clauses                 false
% 1.35/0.99  --dbg_dump_prop_clauses_file            -
% 1.35/0.99  --dbg_out_stat                          false
% 1.35/0.99  
% 1.35/0.99  
% 1.35/0.99  
% 1.35/0.99  
% 1.35/0.99  ------ Proving...
% 1.35/0.99  
% 1.35/0.99  
% 1.35/0.99  % SZS status CounterSatisfiable for theBenchmark.p
% 1.35/0.99  
% 1.35/0.99  % SZS output start Saturation for theBenchmark.p
% 1.35/0.99  
% 1.35/0.99  fof(f2,axiom,(
% 1.35/0.99    ! [X0,X1,X2] : ((m1_subset_1(X2,u1_struct_0(X0)) & m1_subset_1(X1,u1_struct_0(X0)) & l1_orders_2(X0) & v3_orders_2(X0) & ~v2_struct_0(X0)) => r3_orders_2(X0,X1,X1))),
% 1.35/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 1.35/0.99  
% 1.35/0.99  fof(f10,plain,(
% 1.35/0.99    ! [X0,X1,X2] : (r3_orders_2(X0,X1,X1) | (~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_orders_2(X0) | ~v3_orders_2(X0) | v2_struct_0(X0)))),
% 1.35/0.99    inference(ennf_transformation,[],[f2])).
% 1.35/0.99  
% 1.35/0.99  fof(f11,plain,(
% 1.35/0.99    ! [X0,X1,X2] : (r3_orders_2(X0,X1,X1) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_orders_2(X0) | ~v3_orders_2(X0) | v2_struct_0(X0))),
% 1.35/0.99    inference(flattening,[],[f10])).
% 1.35/0.99  
% 1.35/0.99  fof(f31,plain,(
% 1.35/0.99    ( ! [X2,X0,X1] : (r3_orders_2(X0,X1,X1) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_orders_2(X0) | ~v3_orders_2(X0) | v2_struct_0(X0)) )),
% 1.35/0.99    inference(cnf_transformation,[],[f11])).
% 1.35/0.99  
% 1.35/0.99  fof(f5,conjecture,(
% 1.35/0.99    ! [X0] : ((l1_orders_2(X0) & v5_orders_2(X0) & v3_orders_2(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,u1_struct_0(X0)) => ! [X2] : (m1_subset_1(X2,u1_struct_0(X0)) => (k6_waybel_0(X0,X1) = k6_waybel_0(X0,X2) => X1 = X2))))),
% 1.35/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 1.35/0.99  
% 1.35/0.99  fof(f6,negated_conjecture,(
% 1.35/0.99    ~! [X0] : ((l1_orders_2(X0) & v5_orders_2(X0) & v3_orders_2(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,u1_struct_0(X0)) => ! [X2] : (m1_subset_1(X2,u1_struct_0(X0)) => (k6_waybel_0(X0,X1) = k6_waybel_0(X0,X2) => X1 = X2))))),
% 1.35/0.99    inference(negated_conjecture,[],[f5])).
% 1.35/0.99  
% 1.35/0.99  fof(f16,plain,(
% 1.35/0.99    ? [X0] : (? [X1] : (? [X2] : ((X1 != X2 & k6_waybel_0(X0,X1) = k6_waybel_0(X0,X2)) & m1_subset_1(X2,u1_struct_0(X0))) & m1_subset_1(X1,u1_struct_0(X0))) & (l1_orders_2(X0) & v5_orders_2(X0) & v3_orders_2(X0) & ~v2_struct_0(X0)))),
% 1.35/0.99    inference(ennf_transformation,[],[f6])).
% 1.35/0.99  
% 1.35/0.99  fof(f17,plain,(
% 1.35/0.99    ? [X0] : (? [X1] : (? [X2] : (X1 != X2 & k6_waybel_0(X0,X1) = k6_waybel_0(X0,X2) & m1_subset_1(X2,u1_struct_0(X0))) & m1_subset_1(X1,u1_struct_0(X0))) & l1_orders_2(X0) & v5_orders_2(X0) & v3_orders_2(X0) & ~v2_struct_0(X0))),
% 1.35/0.99    inference(flattening,[],[f16])).
% 1.35/0.99  
% 1.35/0.99  fof(f27,plain,(
% 1.35/0.99    ( ! [X0,X1] : (? [X2] : (X1 != X2 & k6_waybel_0(X0,X1) = k6_waybel_0(X0,X2) & m1_subset_1(X2,u1_struct_0(X0))) => (sK4 != X1 & k6_waybel_0(X0,sK4) = k6_waybel_0(X0,X1) & m1_subset_1(sK4,u1_struct_0(X0)))) )),
% 1.35/0.99    introduced(choice_axiom,[])).
% 1.35/0.99  
% 1.35/0.99  fof(f26,plain,(
% 1.35/0.99    ( ! [X0] : (? [X1] : (? [X2] : (X1 != X2 & k6_waybel_0(X0,X1) = k6_waybel_0(X0,X2) & m1_subset_1(X2,u1_struct_0(X0))) & m1_subset_1(X1,u1_struct_0(X0))) => (? [X2] : (sK3 != X2 & k6_waybel_0(X0,sK3) = k6_waybel_0(X0,X2) & m1_subset_1(X2,u1_struct_0(X0))) & m1_subset_1(sK3,u1_struct_0(X0)))) )),
% 1.35/0.99    introduced(choice_axiom,[])).
% 1.35/0.99  
% 1.35/0.99  fof(f25,plain,(
% 1.35/0.99    ? [X0] : (? [X1] : (? [X2] : (X1 != X2 & k6_waybel_0(X0,X1) = k6_waybel_0(X0,X2) & m1_subset_1(X2,u1_struct_0(X0))) & m1_subset_1(X1,u1_struct_0(X0))) & l1_orders_2(X0) & v5_orders_2(X0) & v3_orders_2(X0) & ~v2_struct_0(X0)) => (? [X1] : (? [X2] : (X1 != X2 & k6_waybel_0(sK2,X1) = k6_waybel_0(sK2,X2) & m1_subset_1(X2,u1_struct_0(sK2))) & m1_subset_1(X1,u1_struct_0(sK2))) & l1_orders_2(sK2) & v5_orders_2(sK2) & v3_orders_2(sK2) & ~v2_struct_0(sK2))),
% 1.35/0.99    introduced(choice_axiom,[])).
% 1.35/0.99  
% 1.35/0.99  fof(f28,plain,(
% 1.35/0.99    ((sK3 != sK4 & k6_waybel_0(sK2,sK3) = k6_waybel_0(sK2,sK4) & m1_subset_1(sK4,u1_struct_0(sK2))) & m1_subset_1(sK3,u1_struct_0(sK2))) & l1_orders_2(sK2) & v5_orders_2(sK2) & v3_orders_2(sK2) & ~v2_struct_0(sK2)),
% 1.35/0.99    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2,sK3,sK4])],[f17,f27,f26,f25])).
% 1.35/0.99  
% 1.35/0.99  fof(f45,plain,(
% 1.35/0.99    v3_orders_2(sK2)),
% 1.35/0.99    inference(cnf_transformation,[],[f28])).
% 1.35/0.99  
% 1.35/0.99  fof(f44,plain,(
% 1.35/0.99    ~v2_struct_0(sK2)),
% 1.35/0.99    inference(cnf_transformation,[],[f28])).
% 1.35/0.99  
% 1.35/0.99  fof(f47,plain,(
% 1.35/0.99    l1_orders_2(sK2)),
% 1.35/0.99    inference(cnf_transformation,[],[f28])).
% 1.35/0.99  
% 1.35/0.99  fof(f1,axiom,(
% 1.35/0.99    ! [X0,X1,X2] : ((m1_subset_1(X2,u1_struct_0(X0)) & m1_subset_1(X1,u1_struct_0(X0)) & l1_orders_2(X0) & v3_orders_2(X0) & ~v2_struct_0(X0)) => (r3_orders_2(X0,X1,X2) <=> r1_orders_2(X0,X1,X2)))),
% 1.35/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 1.35/0.99  
% 1.35/0.99  fof(f8,plain,(
% 1.35/0.99    ! [X0,X1,X2] : ((r3_orders_2(X0,X1,X2) <=> r1_orders_2(X0,X1,X2)) | (~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_orders_2(X0) | ~v3_orders_2(X0) | v2_struct_0(X0)))),
% 1.35/0.99    inference(ennf_transformation,[],[f1])).
% 1.35/0.99  
% 1.35/0.99  fof(f9,plain,(
% 1.35/0.99    ! [X0,X1,X2] : ((r3_orders_2(X0,X1,X2) <=> r1_orders_2(X0,X1,X2)) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_orders_2(X0) | ~v3_orders_2(X0) | v2_struct_0(X0))),
% 1.35/0.99    inference(flattening,[],[f8])).
% 1.35/0.99  
% 1.35/0.99  fof(f18,plain,(
% 1.35/0.99    ! [X0,X1,X2] : (((r3_orders_2(X0,X1,X2) | ~r1_orders_2(X0,X1,X2)) & (r1_orders_2(X0,X1,X2) | ~r3_orders_2(X0,X1,X2))) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_orders_2(X0) | ~v3_orders_2(X0) | v2_struct_0(X0))),
% 1.35/0.99    inference(nnf_transformation,[],[f9])).
% 1.35/0.99  
% 1.35/0.99  fof(f29,plain,(
% 1.35/0.99    ( ! [X2,X0,X1] : (r1_orders_2(X0,X1,X2) | ~r3_orders_2(X0,X1,X2) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_orders_2(X0) | ~v3_orders_2(X0) | v2_struct_0(X0)) )),
% 1.35/0.99    inference(cnf_transformation,[],[f18])).
% 1.35/0.99  
% 1.35/0.99  fof(f48,plain,(
% 1.35/0.99    m1_subset_1(sK3,u1_struct_0(sK2))),
% 1.35/0.99    inference(cnf_transformation,[],[f28])).
% 1.35/0.99  
% 1.35/0.99  fof(f50,plain,(
% 1.35/0.99    k6_waybel_0(sK2,sK3) = k6_waybel_0(sK2,sK4)),
% 1.35/0.99    inference(cnf_transformation,[],[f28])).
% 1.35/0.99  
% 1.35/0.99  fof(f4,axiom,(
% 1.35/0.99    ! [X0] : ((l1_orders_2(X0) & v5_orders_2(X0)) => ! [X1] : (m1_subset_1(X1,u1_struct_0(X0)) => ! [X2] : (((! [X3] : (m1_subset_1(X3,u1_struct_0(X0)) => (r1_lattice3(X0,X2,X3) => r1_orders_2(X0,X3,X1))) & r1_lattice3(X0,X2,X1)) => (r2_yellow_0(X0,X2) & k2_yellow_0(X0,X2) = X1)) & ((r2_yellow_0(X0,X2) & k2_yellow_0(X0,X2) = X1) => (! [X3] : (m1_subset_1(X3,u1_struct_0(X0)) => (r1_lattice3(X0,X2,X3) => r1_orders_2(X0,X3,X1))) & r1_lattice3(X0,X2,X1))))))),
% 1.35/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 1.35/0.99  
% 1.35/0.99  fof(f7,plain,(
% 1.35/0.99    ! [X0] : ((l1_orders_2(X0) & v5_orders_2(X0)) => ! [X1] : (m1_subset_1(X1,u1_struct_0(X0)) => ! [X2] : (((! [X3] : (m1_subset_1(X3,u1_struct_0(X0)) => (r1_lattice3(X0,X2,X3) => r1_orders_2(X0,X3,X1))) & r1_lattice3(X0,X2,X1)) => (r2_yellow_0(X0,X2) & k2_yellow_0(X0,X2) = X1)) & ((r2_yellow_0(X0,X2) & k2_yellow_0(X0,X2) = X1) => (! [X4] : (m1_subset_1(X4,u1_struct_0(X0)) => (r1_lattice3(X0,X2,X4) => r1_orders_2(X0,X4,X1))) & r1_lattice3(X0,X2,X1))))))),
% 1.35/0.99    inference(rectify,[],[f4])).
% 1.35/0.99  
% 1.35/0.99  fof(f14,plain,(
% 1.35/0.99    ! [X0] : (! [X1] : (! [X2] : (((r2_yellow_0(X0,X2) & k2_yellow_0(X0,X2) = X1) | (? [X3] : ((~r1_orders_2(X0,X3,X1) & r1_lattice3(X0,X2,X3)) & m1_subset_1(X3,u1_struct_0(X0))) | ~r1_lattice3(X0,X2,X1))) & ((! [X4] : ((r1_orders_2(X0,X4,X1) | ~r1_lattice3(X0,X2,X4)) | ~m1_subset_1(X4,u1_struct_0(X0))) & r1_lattice3(X0,X2,X1)) | (~r2_yellow_0(X0,X2) | k2_yellow_0(X0,X2) != X1))) | ~m1_subset_1(X1,u1_struct_0(X0))) | (~l1_orders_2(X0) | ~v5_orders_2(X0)))),
% 1.35/0.99    inference(ennf_transformation,[],[f7])).
% 1.35/0.99  
% 1.35/0.99  fof(f15,plain,(
% 1.35/0.99    ! [X0] : (! [X1] : (! [X2] : (((r2_yellow_0(X0,X2) & k2_yellow_0(X0,X2) = X1) | ? [X3] : (~r1_orders_2(X0,X3,X1) & r1_lattice3(X0,X2,X3) & m1_subset_1(X3,u1_struct_0(X0))) | ~r1_lattice3(X0,X2,X1)) & ((! [X4] : (r1_orders_2(X0,X4,X1) | ~r1_lattice3(X0,X2,X4) | ~m1_subset_1(X4,u1_struct_0(X0))) & r1_lattice3(X0,X2,X1)) | ~r2_yellow_0(X0,X2) | k2_yellow_0(X0,X2) != X1)) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~l1_orders_2(X0) | ~v5_orders_2(X0))),
% 1.35/0.99    inference(flattening,[],[f14])).
% 1.35/0.99  
% 1.35/0.99  fof(f23,plain,(
% 1.35/0.99    ! [X2,X1,X0] : (? [X3] : (~r1_orders_2(X0,X3,X1) & r1_lattice3(X0,X2,X3) & m1_subset_1(X3,u1_struct_0(X0))) => (~r1_orders_2(X0,sK1(X0,X1,X2),X1) & r1_lattice3(X0,X2,sK1(X0,X1,X2)) & m1_subset_1(sK1(X0,X1,X2),u1_struct_0(X0))))),
% 1.35/0.99    introduced(choice_axiom,[])).
% 1.35/0.99  
% 1.35/0.99  fof(f24,plain,(
% 1.35/0.99    ! [X0] : (! [X1] : (! [X2] : (((r2_yellow_0(X0,X2) & k2_yellow_0(X0,X2) = X1) | (~r1_orders_2(X0,sK1(X0,X1,X2),X1) & r1_lattice3(X0,X2,sK1(X0,X1,X2)) & m1_subset_1(sK1(X0,X1,X2),u1_struct_0(X0))) | ~r1_lattice3(X0,X2,X1)) & ((! [X4] : (r1_orders_2(X0,X4,X1) | ~r1_lattice3(X0,X2,X4) | ~m1_subset_1(X4,u1_struct_0(X0))) & r1_lattice3(X0,X2,X1)) | ~r2_yellow_0(X0,X2) | k2_yellow_0(X0,X2) != X1)) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~l1_orders_2(X0) | ~v5_orders_2(X0))),
% 1.35/0.99    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1])],[f15,f23])).
% 1.35/0.99  
% 1.35/0.99  fof(f38,plain,(
% 1.35/0.99    ( ! [X2,X0,X1] : (k2_yellow_0(X0,X2) = X1 | m1_subset_1(sK1(X0,X1,X2),u1_struct_0(X0)) | ~r1_lattice3(X0,X2,X1) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_orders_2(X0) | ~v5_orders_2(X0)) )),
% 1.35/0.99    inference(cnf_transformation,[],[f24])).
% 1.35/0.99  
% 1.35/0.99  fof(f46,plain,(
% 1.35/0.99    v5_orders_2(sK2)),
% 1.35/0.99    inference(cnf_transformation,[],[f28])).
% 1.35/0.99  
% 1.35/0.99  fof(f39,plain,(
% 1.35/0.99    ( ! [X2,X0,X1] : (k2_yellow_0(X0,X2) = X1 | r1_lattice3(X0,X2,sK1(X0,X1,X2)) | ~r1_lattice3(X0,X2,X1) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_orders_2(X0) | ~v5_orders_2(X0)) )),
% 1.35/0.99    inference(cnf_transformation,[],[f24])).
% 1.35/0.99  
% 1.35/0.99  fof(f3,axiom,(
% 1.35/0.99    ! [X0] : (l1_orders_2(X0) => ! [X1,X2] : (m1_subset_1(X2,u1_struct_0(X0)) => (r1_lattice3(X0,X1,X2) <=> ! [X3] : (m1_subset_1(X3,u1_struct_0(X0)) => (r2_hidden(X3,X1) => r1_orders_2(X0,X2,X3))))))),
% 1.35/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 1.35/0.99  
% 1.35/0.99  fof(f12,plain,(
% 1.35/0.99    ! [X0] : (! [X1,X2] : ((r1_lattice3(X0,X1,X2) <=> ! [X3] : ((r1_orders_2(X0,X2,X3) | ~r2_hidden(X3,X1)) | ~m1_subset_1(X3,u1_struct_0(X0)))) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~l1_orders_2(X0))),
% 1.35/0.99    inference(ennf_transformation,[],[f3])).
% 1.35/0.99  
% 1.35/0.99  fof(f13,plain,(
% 1.35/0.99    ! [X0] : (! [X1,X2] : ((r1_lattice3(X0,X1,X2) <=> ! [X3] : (r1_orders_2(X0,X2,X3) | ~r2_hidden(X3,X1) | ~m1_subset_1(X3,u1_struct_0(X0)))) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~l1_orders_2(X0))),
% 1.35/0.99    inference(flattening,[],[f12])).
% 1.35/0.99  
% 1.35/0.99  fof(f19,plain,(
% 1.35/0.99    ! [X0] : (! [X1,X2] : (((r1_lattice3(X0,X1,X2) | ? [X3] : (~r1_orders_2(X0,X2,X3) & r2_hidden(X3,X1) & m1_subset_1(X3,u1_struct_0(X0)))) & (! [X3] : (r1_orders_2(X0,X2,X3) | ~r2_hidden(X3,X1) | ~m1_subset_1(X3,u1_struct_0(X0))) | ~r1_lattice3(X0,X1,X2))) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~l1_orders_2(X0))),
% 1.35/0.99    inference(nnf_transformation,[],[f13])).
% 1.35/0.99  
% 1.35/0.99  fof(f20,plain,(
% 1.35/0.99    ! [X0] : (! [X1,X2] : (((r1_lattice3(X0,X1,X2) | ? [X3] : (~r1_orders_2(X0,X2,X3) & r2_hidden(X3,X1) & m1_subset_1(X3,u1_struct_0(X0)))) & (! [X4] : (r1_orders_2(X0,X2,X4) | ~r2_hidden(X4,X1) | ~m1_subset_1(X4,u1_struct_0(X0))) | ~r1_lattice3(X0,X1,X2))) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~l1_orders_2(X0))),
% 1.35/0.99    inference(rectify,[],[f19])).
% 1.35/0.99  
% 1.35/0.99  fof(f21,plain,(
% 1.35/0.99    ! [X2,X1,X0] : (? [X3] : (~r1_orders_2(X0,X2,X3) & r2_hidden(X3,X1) & m1_subset_1(X3,u1_struct_0(X0))) => (~r1_orders_2(X0,X2,sK0(X0,X1,X2)) & r2_hidden(sK0(X0,X1,X2),X1) & m1_subset_1(sK0(X0,X1,X2),u1_struct_0(X0))))),
% 1.35/0.99    introduced(choice_axiom,[])).
% 1.35/0.99  
% 1.35/0.99  fof(f22,plain,(
% 1.35/0.99    ! [X0] : (! [X1,X2] : (((r1_lattice3(X0,X1,X2) | (~r1_orders_2(X0,X2,sK0(X0,X1,X2)) & r2_hidden(sK0(X0,X1,X2),X1) & m1_subset_1(sK0(X0,X1,X2),u1_struct_0(X0)))) & (! [X4] : (r1_orders_2(X0,X2,X4) | ~r2_hidden(X4,X1) | ~m1_subset_1(X4,u1_struct_0(X0))) | ~r1_lattice3(X0,X1,X2))) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~l1_orders_2(X0))),
% 1.35/0.99    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f20,f21])).
% 1.35/0.99  
% 1.35/0.99  fof(f32,plain,(
% 1.35/0.99    ( ! [X4,X2,X0,X1] : (r1_orders_2(X0,X2,X4) | ~r2_hidden(X4,X1) | ~m1_subset_1(X4,u1_struct_0(X0)) | ~r1_lattice3(X0,X1,X2) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~l1_orders_2(X0)) )),
% 1.35/0.99    inference(cnf_transformation,[],[f22])).
% 1.35/0.99  
% 1.35/0.99  fof(f34,plain,(
% 1.35/0.99    ( ! [X2,X0,X1] : (r1_lattice3(X0,X1,X2) | r2_hidden(sK0(X0,X1,X2),X1) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~l1_orders_2(X0)) )),
% 1.35/0.99    inference(cnf_transformation,[],[f22])).
% 1.35/0.99  
% 1.35/0.99  fof(f33,plain,(
% 1.35/0.99    ( ! [X2,X0,X1] : (r1_lattice3(X0,X1,X2) | m1_subset_1(sK0(X0,X1,X2),u1_struct_0(X0)) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~l1_orders_2(X0)) )),
% 1.35/0.99    inference(cnf_transformation,[],[f22])).
% 1.35/0.99  
% 1.35/0.99  fof(f40,plain,(
% 1.35/0.99    ( ! [X2,X0,X1] : (k2_yellow_0(X0,X2) = X1 | ~r1_orders_2(X0,sK1(X0,X1,X2),X1) | ~r1_lattice3(X0,X2,X1) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_orders_2(X0) | ~v5_orders_2(X0)) )),
% 1.35/0.99    inference(cnf_transformation,[],[f24])).
% 1.35/0.99  
% 1.35/0.99  fof(f41,plain,(
% 1.35/0.99    ( ! [X2,X0,X1] : (r2_yellow_0(X0,X2) | m1_subset_1(sK1(X0,X1,X2),u1_struct_0(X0)) | ~r1_lattice3(X0,X2,X1) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_orders_2(X0) | ~v5_orders_2(X0)) )),
% 1.35/0.99    inference(cnf_transformation,[],[f24])).
% 1.35/0.99  
% 1.35/0.99  fof(f42,plain,(
% 1.35/0.99    ( ! [X2,X0,X1] : (r2_yellow_0(X0,X2) | r1_lattice3(X0,X2,sK1(X0,X1,X2)) | ~r1_lattice3(X0,X2,X1) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_orders_2(X0) | ~v5_orders_2(X0)) )),
% 1.35/0.99    inference(cnf_transformation,[],[f24])).
% 1.35/0.99  
% 1.35/0.99  fof(f43,plain,(
% 1.35/0.99    ( ! [X2,X0,X1] : (r2_yellow_0(X0,X2) | ~r1_orders_2(X0,sK1(X0,X1,X2),X1) | ~r1_lattice3(X0,X2,X1) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_orders_2(X0) | ~v5_orders_2(X0)) )),
% 1.35/0.99    inference(cnf_transformation,[],[f24])).
% 1.35/0.99  
% 1.35/0.99  fof(f49,plain,(
% 1.35/0.99    m1_subset_1(sK4,u1_struct_0(sK2))),
% 1.35/0.99    inference(cnf_transformation,[],[f28])).
% 1.35/0.99  
% 1.35/0.99  fof(f35,plain,(
% 1.35/0.99    ( ! [X2,X0,X1] : (r1_lattice3(X0,X1,X2) | ~r1_orders_2(X0,X2,sK0(X0,X1,X2)) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~l1_orders_2(X0)) )),
% 1.35/0.99    inference(cnf_transformation,[],[f22])).
% 1.35/0.99  
% 1.35/0.99  fof(f37,plain,(
% 1.35/0.99    ( ! [X4,X2,X0,X1] : (r1_orders_2(X0,X4,X1) | ~r1_lattice3(X0,X2,X4) | ~m1_subset_1(X4,u1_struct_0(X0)) | ~r2_yellow_0(X0,X2) | k2_yellow_0(X0,X2) != X1 | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_orders_2(X0) | ~v5_orders_2(X0)) )),
% 1.35/0.99    inference(cnf_transformation,[],[f24])).
% 1.35/0.99  
% 1.35/0.99  fof(f52,plain,(
% 1.35/0.99    ( ! [X4,X2,X0] : (r1_orders_2(X0,X4,k2_yellow_0(X0,X2)) | ~r1_lattice3(X0,X2,X4) | ~m1_subset_1(X4,u1_struct_0(X0)) | ~r2_yellow_0(X0,X2) | ~m1_subset_1(k2_yellow_0(X0,X2),u1_struct_0(X0)) | ~l1_orders_2(X0) | ~v5_orders_2(X0)) )),
% 1.35/0.99    inference(equality_resolution,[],[f37])).
% 1.35/0.99  
% 1.35/0.99  fof(f36,plain,(
% 1.35/0.99    ( ! [X2,X0,X1] : (r1_lattice3(X0,X2,X1) | ~r2_yellow_0(X0,X2) | k2_yellow_0(X0,X2) != X1 | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_orders_2(X0) | ~v5_orders_2(X0)) )),
% 1.35/0.99    inference(cnf_transformation,[],[f24])).
% 1.35/0.99  
% 1.35/0.99  fof(f53,plain,(
% 1.35/0.99    ( ! [X2,X0] : (r1_lattice3(X0,X2,k2_yellow_0(X0,X2)) | ~r2_yellow_0(X0,X2) | ~m1_subset_1(k2_yellow_0(X0,X2),u1_struct_0(X0)) | ~l1_orders_2(X0) | ~v5_orders_2(X0)) )),
% 1.35/0.99    inference(equality_resolution,[],[f36])).
% 1.35/0.99  
% 1.35/0.99  fof(f51,plain,(
% 1.35/0.99    sK3 != sK4),
% 1.35/0.99    inference(cnf_transformation,[],[f28])).
% 1.35/0.99  
% 1.35/0.99  cnf(c_2,plain,
% 1.35/0.99      ( r3_orders_2(X0,X1,X1)
% 1.35/0.99      | ~ m1_subset_1(X2,u1_struct_0(X0))
% 1.35/0.99      | ~ m1_subset_1(X1,u1_struct_0(X0))
% 1.35/0.99      | v2_struct_0(X0)
% 1.35/0.99      | ~ v3_orders_2(X0)
% 1.35/0.99      | ~ l1_orders_2(X0) ),
% 1.35/0.99      inference(cnf_transformation,[],[f31]) ).
% 1.35/0.99  
% 1.35/0.99  cnf(c_21,negated_conjecture,
% 1.35/0.99      ( v3_orders_2(sK2) ),
% 1.35/0.99      inference(cnf_transformation,[],[f45]) ).
% 1.35/0.99  
% 1.35/0.99  cnf(c_270,plain,
% 1.35/0.99      ( r3_orders_2(X0,X1,X1)
% 1.35/0.99      | ~ m1_subset_1(X2,u1_struct_0(X0))
% 1.35/0.99      | ~ m1_subset_1(X1,u1_struct_0(X0))
% 1.35/0.99      | v2_struct_0(X0)
% 1.35/0.99      | ~ l1_orders_2(X0)
% 1.35/0.99      | sK2 != X0 ),
% 1.35/0.99      inference(resolution_lifted,[status(thm)],[c_2,c_21]) ).
% 1.35/0.99  
% 1.35/0.99  cnf(c_271,plain,
% 1.35/0.99      ( r3_orders_2(sK2,X0,X0)
% 1.35/0.99      | ~ m1_subset_1(X0,u1_struct_0(sK2))
% 1.35/0.99      | ~ m1_subset_1(X1,u1_struct_0(sK2))
% 1.35/0.99      | v2_struct_0(sK2)
% 1.35/0.99      | ~ l1_orders_2(sK2) ),
% 1.35/0.99      inference(unflattening,[status(thm)],[c_270]) ).
% 1.35/0.99  
% 1.35/0.99  cnf(c_22,negated_conjecture,
% 1.35/0.99      ( ~ v2_struct_0(sK2) ),
% 1.35/0.99      inference(cnf_transformation,[],[f44]) ).
% 1.35/0.99  
% 1.35/0.99  cnf(c_19,negated_conjecture,
% 1.35/0.99      ( l1_orders_2(sK2) ),
% 1.35/0.99      inference(cnf_transformation,[],[f47]) ).
% 1.35/0.99  
% 1.35/0.99  cnf(c_275,plain,
% 1.35/0.99      ( r3_orders_2(sK2,X0,X0)
% 1.35/0.99      | ~ m1_subset_1(X0,u1_struct_0(sK2))
% 1.35/0.99      | ~ m1_subset_1(X1,u1_struct_0(sK2)) ),
% 1.35/0.99      inference(global_propositional_subsumption,
% 1.35/0.99                [status(thm)],
% 1.35/0.99                [c_271,c_22,c_19]) ).
% 1.35/0.99  
% 1.35/0.99  cnf(c_276,plain,
% 1.35/0.99      ( r3_orders_2(sK2,X0,X0)
% 1.35/0.99      | ~ m1_subset_1(X1,u1_struct_0(sK2))
% 1.35/0.99      | ~ m1_subset_1(X0,u1_struct_0(sK2)) ),
% 1.35/0.99      inference(renaming,[status(thm)],[c_275]) ).
% 1.35/0.99  
% 1.35/0.99  cnf(c_1,plain,
% 1.35/0.99      ( r1_orders_2(X0,X1,X2)
% 1.35/0.99      | ~ r3_orders_2(X0,X1,X2)
% 1.35/0.99      | ~ m1_subset_1(X2,u1_struct_0(X0))
% 1.35/0.99      | ~ m1_subset_1(X1,u1_struct_0(X0))
% 1.35/0.99      | v2_struct_0(X0)
% 1.35/0.99      | ~ v3_orders_2(X0)
% 1.35/0.99      | ~ l1_orders_2(X0) ),
% 1.35/0.99      inference(cnf_transformation,[],[f29]) ).
% 1.35/0.99  
% 1.35/0.99  cnf(c_291,plain,
% 1.35/0.99      ( r1_orders_2(X0,X1,X2)
% 1.35/0.99      | ~ r3_orders_2(X0,X1,X2)
% 1.35/0.99      | ~ m1_subset_1(X2,u1_struct_0(X0))
% 1.35/0.99      | ~ m1_subset_1(X1,u1_struct_0(X0))
% 1.35/0.99      | v2_struct_0(X0)
% 1.35/0.99      | ~ l1_orders_2(X0)
% 1.35/0.99      | sK2 != X0 ),
% 1.35/0.99      inference(resolution_lifted,[status(thm)],[c_1,c_21]) ).
% 1.35/0.99  
% 1.35/0.99  cnf(c_292,plain,
% 1.35/0.99      ( r1_orders_2(sK2,X0,X1)
% 1.35/0.99      | ~ r3_orders_2(sK2,X0,X1)
% 1.35/0.99      | ~ m1_subset_1(X0,u1_struct_0(sK2))
% 1.35/0.99      | ~ m1_subset_1(X1,u1_struct_0(sK2))
% 1.35/0.99      | v2_struct_0(sK2)
% 1.35/0.99      | ~ l1_orders_2(sK2) ),
% 1.35/0.99      inference(unflattening,[status(thm)],[c_291]) ).
% 1.35/0.99  
% 1.35/0.99  cnf(c_296,plain,
% 1.35/0.99      ( r1_orders_2(sK2,X0,X1)
% 1.35/0.99      | ~ r3_orders_2(sK2,X0,X1)
% 1.35/0.99      | ~ m1_subset_1(X0,u1_struct_0(sK2))
% 1.35/0.99      | ~ m1_subset_1(X1,u1_struct_0(sK2)) ),
% 1.35/0.99      inference(global_propositional_subsumption,
% 1.35/0.99                [status(thm)],
% 1.35/0.99                [c_292,c_22,c_19]) ).
% 1.35/0.99  
% 1.35/0.99  cnf(c_297,plain,
% 1.35/0.99      ( r1_orders_2(sK2,X0,X1)
% 1.35/0.99      | ~ r3_orders_2(sK2,X0,X1)
% 1.35/0.99      | ~ m1_subset_1(X1,u1_struct_0(sK2))
% 1.35/0.99      | ~ m1_subset_1(X0,u1_struct_0(sK2)) ),
% 1.35/0.99      inference(renaming,[status(thm)],[c_296]) ).
% 1.35/0.99  
% 1.35/0.99  cnf(c_354,plain,
% 1.35/0.99      ( r1_orders_2(sK2,X0,X1)
% 1.35/0.99      | ~ m1_subset_1(X2,u1_struct_0(sK2))
% 1.35/0.99      | ~ m1_subset_1(X0,u1_struct_0(sK2))
% 1.35/0.99      | ~ m1_subset_1(X3,u1_struct_0(sK2))
% 1.35/0.99      | ~ m1_subset_1(X1,u1_struct_0(sK2))
% 1.35/0.99      | X0 != X3
% 1.35/0.99      | X1 != X3
% 1.35/0.99      | sK2 != sK2 ),
% 1.35/0.99      inference(resolution_lifted,[status(thm)],[c_276,c_297]) ).
% 1.35/0.99  
% 1.35/0.99  cnf(c_355,plain,
% 1.35/0.99      ( r1_orders_2(sK2,X0,X0)
% 1.35/0.99      | ~ m1_subset_1(X1,u1_struct_0(sK2))
% 1.35/0.99      | ~ m1_subset_1(X0,u1_struct_0(sK2)) ),
% 1.35/0.99      inference(unflattening,[status(thm)],[c_354]) ).
% 1.35/0.99  
% 1.35/0.99  cnf(c_1662,plain,
% 1.35/0.99      ( r1_orders_2(sK2,X0_48,X0_48)
% 1.35/0.99      | ~ m1_subset_1(X1_48,u1_struct_0(sK2))
% 1.35/0.99      | ~ m1_subset_1(X0_48,u1_struct_0(sK2)) ),
% 1.35/0.99      inference(subtyping,[status(esa)],[c_355]) ).
% 1.35/0.99  
% 1.35/0.99  cnf(c_1667,plain,
% 1.35/0.99      ( ~ m1_subset_1(X0_48,u1_struct_0(sK2)) | ~ sP0_iProver_split ),
% 1.35/0.99      inference(splitting,
% 1.35/0.99                [splitting(split),new_symbols(definition,[sP0_iProver_split])],
% 1.35/0.99                [c_1662]) ).
% 1.35/0.99  
% 1.35/0.99  cnf(c_18,negated_conjecture,
% 1.35/0.99      ( m1_subset_1(sK3,u1_struct_0(sK2)) ),
% 1.35/0.99      inference(cnf_transformation,[],[f48]) ).
% 1.35/0.99  
% 1.35/0.99  cnf(c_1693,plain,
% 1.35/0.99      ( ~ m1_subset_1(sK3,u1_struct_0(sK2)) | ~ sP0_iProver_split ),
% 1.35/0.99      inference(instantiation,[status(thm)],[c_1667]) ).
% 1.35/0.99  
% 1.35/0.99  cnf(c_1763,plain,
% 1.35/0.99      ( ~ sP0_iProver_split ),
% 1.35/0.99      inference(global_propositional_subsumption,
% 1.35/0.99                [status(thm)],
% 1.35/0.99                [c_1667,c_18,c_1693]) ).
% 1.35/0.99  
% 1.35/0.99  cnf(c_1669,plain,
% 1.35/0.99      ( sP1_iProver_split | sP0_iProver_split ),
% 1.35/0.99      inference(splitting,
% 1.35/0.99                [splitting(split),new_symbols(definition,[])],
% 1.35/0.99                [c_1662]) ).
% 1.35/0.99  
% 1.35/0.99  cnf(c_1751,plain,
% 1.35/0.99      ( sP1_iProver_split ),
% 1.35/0.99      inference(global_propositional_subsumption,
% 1.35/0.99                [status(thm)],
% 1.35/0.99                [c_1669,c_18,c_1693]) ).
% 1.35/0.99  
% 1.35/0.99  cnf(c_1678,plain,
% 1.35/0.99      ( k6_waybel_0(X0_46,X0_48) = k6_waybel_0(X0_46,X1_48) | X0_48 != X1_48 ),
% 1.35/0.99      theory(equality) ).
% 1.35/0.99  
% 1.35/0.99  cnf(c_1674,plain,
% 1.35/0.99      ( X0_50 != X1_50 | X2_50 != X1_50 | X2_50 = X0_50 ),
% 1.35/0.99      theory(equality) ).
% 1.35/0.99  
% 1.35/0.99  cnf(c_1672,plain,( X0_50 = X0_50 ),theory(equality) ).
% 1.35/0.99  
% 1.35/0.99  cnf(c_16,negated_conjecture,
% 1.35/0.99      ( k6_waybel_0(sK2,sK3) = k6_waybel_0(sK2,sK4) ),
% 1.35/0.99      inference(cnf_transformation,[],[f50]) ).
% 1.35/0.99  
% 1.35/0.99  cnf(c_1665,negated_conjecture,
% 1.35/0.99      ( k6_waybel_0(sK2,sK3) = k6_waybel_0(sK2,sK4) ),
% 1.35/0.99      inference(subtyping,[status(esa)],[c_16]) ).
% 1.35/0.99  
% 1.35/0.99  cnf(c_211,plain,
% 1.35/0.99      ( ~ v5_orders_2(X0) | v5_orders_2(X1) | X1 != X0 ),
% 1.35/0.99      theory(equality) ).
% 1.35/0.99  
% 1.35/0.99  cnf(c_210,plain,
% 1.35/0.99      ( ~ r2_hidden(X0,X1) | r2_hidden(X2,X1) | X2 != X0 ),
% 1.35/0.99      theory(equality) ).
% 1.35/0.99  
% 1.35/0.99  cnf(c_208,plain,
% 1.35/0.99      ( ~ v2_struct_0(X0) | v2_struct_0(X1) | X1 != X0 ),
% 1.35/0.99      theory(equality) ).
% 1.35/0.99  
% 1.35/0.99  cnf(c_207,plain,
% 1.35/0.99      ( ~ v3_orders_2(X0) | v3_orders_2(X1) | X1 != X0 ),
% 1.35/0.99      theory(equality) ).
% 1.35/0.99  
% 1.35/0.99  cnf(c_206,plain,
% 1.35/0.99      ( ~ l1_orders_2(X0) | l1_orders_2(X1) | X1 != X0 ),
% 1.35/0.99      theory(equality) ).
% 1.35/0.99  
% 1.35/0.99  cnf(c_200,plain,( X0_2 = X0_2 ),theory(equality) ).
% 1.35/0.99  
% 1.35/0.99  cnf(c_12,plain,
% 1.35/0.99      ( ~ r1_lattice3(X0,X1,X2)
% 1.35/0.99      | ~ m1_subset_1(X2,u1_struct_0(X0))
% 1.35/0.99      | m1_subset_1(sK1(X0,X2,X1),u1_struct_0(X0))
% 1.35/0.99      | ~ v5_orders_2(X0)
% 1.35/0.99      | ~ l1_orders_2(X0)
% 1.35/0.99      | k2_yellow_0(X0,X1) = X2 ),
% 1.35/0.99      inference(cnf_transformation,[],[f38]) ).
% 1.35/0.99  
% 1.35/0.99  cnf(c_20,negated_conjecture,
% 1.35/0.99      ( v5_orders_2(sK2) ),
% 1.35/0.99      inference(cnf_transformation,[],[f46]) ).
% 1.35/0.99  
% 1.35/0.99  cnf(c_421,plain,
% 1.35/0.99      ( ~ r1_lattice3(X0,X1,X2)
% 1.35/0.99      | ~ m1_subset_1(X2,u1_struct_0(X0))
% 1.35/0.99      | m1_subset_1(sK1(X0,X2,X1),u1_struct_0(X0))
% 1.35/0.99      | ~ l1_orders_2(X0)
% 1.35/0.99      | k2_yellow_0(X0,X1) = X2
% 1.35/0.99      | sK2 != X0 ),
% 1.35/0.99      inference(resolution_lifted,[status(thm)],[c_12,c_20]) ).
% 1.35/0.99  
% 1.35/0.99  cnf(c_422,plain,
% 1.35/0.99      ( ~ r1_lattice3(sK2,X0,X1)
% 1.35/0.99      | ~ m1_subset_1(X1,u1_struct_0(sK2))
% 1.35/0.99      | m1_subset_1(sK1(sK2,X1,X0),u1_struct_0(sK2))
% 1.35/0.99      | ~ l1_orders_2(sK2)
% 1.35/0.99      | k2_yellow_0(sK2,X0) = X1 ),
% 1.35/0.99      inference(unflattening,[status(thm)],[c_421]) ).
% 1.35/0.99  
% 1.35/0.99  cnf(c_426,plain,
% 1.35/0.99      ( m1_subset_1(sK1(sK2,X1,X0),u1_struct_0(sK2))
% 1.35/0.99      | ~ m1_subset_1(X1,u1_struct_0(sK2))
% 1.35/0.99      | ~ r1_lattice3(sK2,X0,X1)
% 1.35/0.99      | k2_yellow_0(sK2,X0) = X1 ),
% 1.35/0.99      inference(global_propositional_subsumption,[status(thm)],[c_422,c_19]) ).
% 1.35/0.99  
% 1.35/0.99  cnf(c_427,plain,
% 1.35/0.99      ( ~ r1_lattice3(sK2,X0,X1)
% 1.35/0.99      | ~ m1_subset_1(X1,u1_struct_0(sK2))
% 1.35/0.99      | m1_subset_1(sK1(sK2,X1,X0),u1_struct_0(sK2))
% 1.35/0.99      | k2_yellow_0(sK2,X0) = X1 ),
% 1.35/0.99      inference(renaming,[status(thm)],[c_426]) ).
% 1.35/0.99  
% 1.35/0.99  cnf(c_1659,plain,
% 1.35/0.99      ( ~ r1_lattice3(sK2,X0_47,X0_48)
% 1.35/0.99      | ~ m1_subset_1(X0_48,u1_struct_0(sK2))
% 1.35/0.99      | m1_subset_1(sK1(sK2,X0_48,X0_47),u1_struct_0(sK2))
% 1.35/0.99      | k2_yellow_0(sK2,X0_47) = X0_48 ),
% 1.35/0.99      inference(subtyping,[status(esa)],[c_427]) ).
% 1.35/0.99  
% 1.35/0.99  cnf(c_1980,plain,
% 1.35/0.99      ( k2_yellow_0(sK2,X0_47) = X0_48
% 1.35/0.99      | r1_lattice3(sK2,X0_47,X0_48) != iProver_top
% 1.35/0.99      | m1_subset_1(X0_48,u1_struct_0(sK2)) != iProver_top
% 1.35/0.99      | m1_subset_1(sK1(sK2,X0_48,X0_47),u1_struct_0(sK2)) = iProver_top ),
% 1.35/0.99      inference(predicate_to_equality,[status(thm)],[c_1659]) ).
% 1.35/0.99  
% 1.35/0.99  cnf(c_11,plain,
% 1.35/0.99      ( ~ r1_lattice3(X0,X1,X2)
% 1.35/0.99      | r1_lattice3(X0,X1,sK1(X0,X2,X1))
% 1.35/0.99      | ~ m1_subset_1(X2,u1_struct_0(X0))
% 1.35/0.99      | ~ v5_orders_2(X0)
% 1.35/0.99      | ~ l1_orders_2(X0)
% 1.35/0.99      | k2_yellow_0(X0,X1) = X2 ),
% 1.35/0.99      inference(cnf_transformation,[],[f39]) ).
% 1.35/0.99  
% 1.35/0.99  cnf(c_445,plain,
% 1.35/0.99      ( ~ r1_lattice3(X0,X1,X2)
% 1.35/0.99      | r1_lattice3(X0,X1,sK1(X0,X2,X1))
% 1.35/0.99      | ~ m1_subset_1(X2,u1_struct_0(X0))
% 1.35/0.99      | ~ l1_orders_2(X0)
% 1.35/0.99      | k2_yellow_0(X0,X1) = X2
% 1.35/0.99      | sK2 != X0 ),
% 1.35/0.99      inference(resolution_lifted,[status(thm)],[c_11,c_20]) ).
% 1.35/0.99  
% 1.35/0.99  cnf(c_446,plain,
% 1.35/0.99      ( ~ r1_lattice3(sK2,X0,X1)
% 1.35/0.99      | r1_lattice3(sK2,X0,sK1(sK2,X1,X0))
% 1.35/0.99      | ~ m1_subset_1(X1,u1_struct_0(sK2))
% 1.35/0.99      | ~ l1_orders_2(sK2)
% 1.35/0.99      | k2_yellow_0(sK2,X0) = X1 ),
% 1.35/0.99      inference(unflattening,[status(thm)],[c_445]) ).
% 1.35/0.99  
% 1.35/0.99  cnf(c_450,plain,
% 1.35/0.99      ( ~ m1_subset_1(X1,u1_struct_0(sK2))
% 1.35/0.99      | r1_lattice3(sK2,X0,sK1(sK2,X1,X0))
% 1.35/0.99      | ~ r1_lattice3(sK2,X0,X1)
% 1.35/0.99      | k2_yellow_0(sK2,X0) = X1 ),
% 1.35/0.99      inference(global_propositional_subsumption,[status(thm)],[c_446,c_19]) ).
% 1.35/0.99  
% 1.35/0.99  cnf(c_451,plain,
% 1.35/0.99      ( ~ r1_lattice3(sK2,X0,X1)
% 1.35/0.99      | r1_lattice3(sK2,X0,sK1(sK2,X1,X0))
% 1.35/0.99      | ~ m1_subset_1(X1,u1_struct_0(sK2))
% 1.35/0.99      | k2_yellow_0(sK2,X0) = X1 ),
% 1.35/0.99      inference(renaming,[status(thm)],[c_450]) ).
% 1.35/0.99  
% 1.35/0.99  cnf(c_1658,plain,
% 1.35/0.99      ( ~ r1_lattice3(sK2,X0_47,X0_48)
% 1.35/0.99      | r1_lattice3(sK2,X0_47,sK1(sK2,X0_48,X0_47))
% 1.35/0.99      | ~ m1_subset_1(X0_48,u1_struct_0(sK2))
% 1.35/0.99      | k2_yellow_0(sK2,X0_47) = X0_48 ),
% 1.35/0.99      inference(subtyping,[status(esa)],[c_451]) ).
% 1.35/0.99  
% 1.35/0.99  cnf(c_1981,plain,
% 1.35/0.99      ( k2_yellow_0(sK2,X0_47) = X0_48
% 1.35/0.99      | r1_lattice3(sK2,X0_47,X0_48) != iProver_top
% 1.35/0.99      | r1_lattice3(sK2,X0_47,sK1(sK2,X0_48,X0_47)) = iProver_top
% 1.35/0.99      | m1_subset_1(X0_48,u1_struct_0(sK2)) != iProver_top ),
% 1.35/0.99      inference(predicate_to_equality,[status(thm)],[c_1658]) ).
% 1.35/0.99  
% 1.35/0.99  cnf(c_6,plain,
% 1.35/0.99      ( ~ r1_lattice3(X0,X1,X2)
% 1.35/0.99      | r1_orders_2(X0,X2,X3)
% 1.35/0.99      | ~ r2_hidden(X3,X1)
% 1.35/0.99      | ~ m1_subset_1(X2,u1_struct_0(X0))
% 1.35/0.99      | ~ m1_subset_1(X3,u1_struct_0(X0))
% 1.35/0.99      | ~ l1_orders_2(X0) ),
% 1.35/0.99      inference(cnf_transformation,[],[f32]) ).
% 1.35/0.99  
% 1.35/0.99  cnf(c_605,plain,
% 1.35/0.99      ( ~ r1_lattice3(X0,X1,X2)
% 1.35/0.99      | r1_orders_2(X0,X2,X3)
% 1.35/0.99      | ~ r2_hidden(X3,X1)
% 1.35/0.99      | ~ m1_subset_1(X2,u1_struct_0(X0))
% 1.35/0.99      | ~ m1_subset_1(X3,u1_struct_0(X0))
% 1.35/0.99      | sK2 != X0 ),
% 1.35/0.99      inference(resolution_lifted,[status(thm)],[c_6,c_19]) ).
% 1.35/0.99  
% 1.35/0.99  cnf(c_606,plain,
% 1.35/0.99      ( ~ r1_lattice3(sK2,X0,X1)
% 1.35/0.99      | r1_orders_2(sK2,X1,X2)
% 1.35/0.99      | ~ r2_hidden(X2,X0)
% 1.35/0.99      | ~ m1_subset_1(X1,u1_struct_0(sK2))
% 1.35/0.99      | ~ m1_subset_1(X2,u1_struct_0(sK2)) ),
% 1.35/0.99      inference(unflattening,[status(thm)],[c_605]) ).
% 1.35/0.99  
% 1.35/0.99  cnf(c_4,plain,
% 1.35/0.99      ( r1_lattice3(X0,X1,X2)
% 1.35/0.99      | r2_hidden(sK0(X0,X1,X2),X1)
% 1.35/0.99      | ~ m1_subset_1(X2,u1_struct_0(X0))
% 1.35/0.99      | ~ l1_orders_2(X0) ),
% 1.35/0.99      inference(cnf_transformation,[],[f34]) ).
% 1.35/0.99  
% 1.35/0.99  cnf(c_639,plain,
% 1.35/0.99      ( r1_lattice3(X0,X1,X2)
% 1.35/0.99      | r2_hidden(sK0(X0,X1,X2),X1)
% 1.35/0.99      | ~ m1_subset_1(X2,u1_struct_0(X0))
% 1.35/0.99      | sK2 != X0 ),
% 1.35/0.99      inference(resolution_lifted,[status(thm)],[c_4,c_19]) ).
% 1.35/0.99  
% 1.35/0.99  cnf(c_640,plain,
% 1.35/0.99      ( r1_lattice3(sK2,X0,X1)
% 1.35/0.99      | r2_hidden(sK0(sK2,X0,X1),X0)
% 1.35/0.99      | ~ m1_subset_1(X1,u1_struct_0(sK2)) ),
% 1.35/0.99      inference(unflattening,[status(thm)],[c_639]) ).
% 1.35/0.99  
% 1.35/0.99  cnf(c_687,plain,
% 1.35/0.99      ( ~ r1_lattice3(sK2,X0,X1)
% 1.35/0.99      | r1_lattice3(sK2,X2,X3)
% 1.35/0.99      | r1_orders_2(sK2,X1,X4)
% 1.35/0.99      | ~ m1_subset_1(X1,u1_struct_0(sK2))
% 1.35/0.99      | ~ m1_subset_1(X4,u1_struct_0(sK2))
% 1.35/0.99      | ~ m1_subset_1(X3,u1_struct_0(sK2))
% 1.35/0.99      | X2 != X0
% 1.35/0.99      | sK0(sK2,X2,X3) != X4 ),
% 1.35/0.99      inference(resolution_lifted,[status(thm)],[c_606,c_640]) ).
% 1.35/0.99  
% 1.35/0.99  cnf(c_688,plain,
% 1.35/0.99      ( ~ r1_lattice3(sK2,X0,X1)
% 1.35/0.99      | r1_lattice3(sK2,X0,X2)
% 1.35/0.99      | r1_orders_2(sK2,X1,sK0(sK2,X0,X2))
% 1.35/0.99      | ~ m1_subset_1(X1,u1_struct_0(sK2))
% 1.35/0.99      | ~ m1_subset_1(X2,u1_struct_0(sK2))
% 1.35/0.99      | ~ m1_subset_1(sK0(sK2,X0,X2),u1_struct_0(sK2)) ),
% 1.35/0.99      inference(unflattening,[status(thm)],[c_687]) ).
% 1.35/0.99  
% 1.35/0.99  cnf(c_5,plain,
% 1.35/0.99      ( r1_lattice3(X0,X1,X2)
% 1.35/0.99      | ~ m1_subset_1(X2,u1_struct_0(X0))
% 1.35/0.99      | m1_subset_1(sK0(X0,X1,X2),u1_struct_0(X0))
% 1.35/0.99      | ~ l1_orders_2(X0) ),
% 1.35/0.99      inference(cnf_transformation,[],[f33]) ).
% 1.35/0.99  
% 1.35/0.99  cnf(c_624,plain,
% 1.35/0.99      ( r1_lattice3(X0,X1,X2)
% 1.35/0.99      | ~ m1_subset_1(X2,u1_struct_0(X0))
% 1.35/0.99      | m1_subset_1(sK0(X0,X1,X2),u1_struct_0(X0))
% 1.35/0.99      | sK2 != X0 ),
% 1.35/0.99      inference(resolution_lifted,[status(thm)],[c_5,c_19]) ).
% 1.35/0.99  
% 1.35/0.99  cnf(c_625,plain,
% 1.35/0.99      ( r1_lattice3(sK2,X0,X1)
% 1.35/0.99      | ~ m1_subset_1(X1,u1_struct_0(sK2))
% 1.35/0.99      | m1_subset_1(sK0(sK2,X0,X1),u1_struct_0(sK2)) ),
% 1.35/0.99      inference(unflattening,[status(thm)],[c_624]) ).
% 1.35/0.99  
% 1.35/0.99  cnf(c_702,plain,
% 1.35/0.99      ( ~ r1_lattice3(sK2,X0,X1)
% 1.35/0.99      | r1_lattice3(sK2,X0,X2)
% 1.35/0.99      | r1_orders_2(sK2,X1,sK0(sK2,X0,X2))
% 1.35/0.99      | ~ m1_subset_1(X1,u1_struct_0(sK2))
% 1.35/0.99      | ~ m1_subset_1(X2,u1_struct_0(sK2)) ),
% 1.35/0.99      inference(forward_subsumption_resolution,[status(thm)],[c_688,c_625]) ).
% 1.35/0.99  
% 1.35/0.99  cnf(c_1651,plain,
% 1.35/0.99      ( ~ r1_lattice3(sK2,X0_47,X0_48)
% 1.35/0.99      | r1_lattice3(sK2,X0_47,X1_48)
% 1.35/0.99      | r1_orders_2(sK2,X0_48,sK0(sK2,X0_47,X1_48))
% 1.35/0.99      | ~ m1_subset_1(X1_48,u1_struct_0(sK2))
% 1.35/0.99      | ~ m1_subset_1(X0_48,u1_struct_0(sK2)) ),
% 1.35/0.99      inference(subtyping,[status(esa)],[c_702]) ).
% 1.35/0.99  
% 1.35/0.99  cnf(c_1988,plain,
% 1.35/0.99      ( r1_lattice3(sK2,X0_47,X0_48) != iProver_top
% 1.35/0.99      | r1_lattice3(sK2,X0_47,X1_48) = iProver_top
% 1.35/0.99      | r1_orders_2(sK2,X0_48,sK0(sK2,X0_47,X1_48)) = iProver_top
% 1.35/0.99      | m1_subset_1(X0_48,u1_struct_0(sK2)) != iProver_top
% 1.35/0.99      | m1_subset_1(X1_48,u1_struct_0(sK2)) != iProver_top ),
% 1.35/0.99      inference(predicate_to_equality,[status(thm)],[c_1651]) ).
% 1.35/0.99  
% 1.35/0.99  cnf(c_10,plain,
% 1.35/0.99      ( ~ r1_lattice3(X0,X1,X2)
% 1.35/0.99      | ~ r1_orders_2(X0,sK1(X0,X2,X1),X2)
% 1.35/0.99      | ~ m1_subset_1(X2,u1_struct_0(X0))
% 1.35/0.99      | ~ v5_orders_2(X0)
% 1.35/0.99      | ~ l1_orders_2(X0)
% 1.35/0.99      | k2_yellow_0(X0,X1) = X2 ),
% 1.35/0.99      inference(cnf_transformation,[],[f40]) ).
% 1.35/0.99  
% 1.35/0.99  cnf(c_469,plain,
% 1.35/0.99      ( ~ r1_lattice3(X0,X1,X2)
% 1.35/0.99      | ~ r1_orders_2(X0,sK1(X0,X2,X1),X2)
% 1.35/0.99      | ~ m1_subset_1(X2,u1_struct_0(X0))
% 1.35/0.99      | ~ l1_orders_2(X0)
% 1.35/0.99      | k2_yellow_0(X0,X1) = X2
% 1.35/0.99      | sK2 != X0 ),
% 1.35/0.99      inference(resolution_lifted,[status(thm)],[c_10,c_20]) ).
% 1.35/0.99  
% 1.35/0.99  cnf(c_470,plain,
% 1.35/0.99      ( ~ r1_lattice3(sK2,X0,X1)
% 1.35/0.99      | ~ r1_orders_2(sK2,sK1(sK2,X1,X0),X1)
% 1.35/0.99      | ~ m1_subset_1(X1,u1_struct_0(sK2))
% 1.35/0.99      | ~ l1_orders_2(sK2)
% 1.35/0.99      | k2_yellow_0(sK2,X0) = X1 ),
% 1.35/0.99      inference(unflattening,[status(thm)],[c_469]) ).
% 1.35/0.99  
% 1.35/0.99  cnf(c_474,plain,
% 1.35/0.99      ( ~ m1_subset_1(X1,u1_struct_0(sK2))
% 1.35/0.99      | ~ r1_orders_2(sK2,sK1(sK2,X1,X0),X1)
% 1.35/0.99      | ~ r1_lattice3(sK2,X0,X1)
% 1.35/0.99      | k2_yellow_0(sK2,X0) = X1 ),
% 1.35/0.99      inference(global_propositional_subsumption,[status(thm)],[c_470,c_19]) ).
% 1.35/0.99  
% 1.35/0.99  cnf(c_475,plain,
% 1.35/0.99      ( ~ r1_lattice3(sK2,X0,X1)
% 1.35/0.99      | ~ r1_orders_2(sK2,sK1(sK2,X1,X0),X1)
% 1.35/0.99      | ~ m1_subset_1(X1,u1_struct_0(sK2))
% 1.35/0.99      | k2_yellow_0(sK2,X0) = X1 ),
% 1.35/0.99      inference(renaming,[status(thm)],[c_474]) ).
% 1.35/0.99  
% 1.35/0.99  cnf(c_1657,plain,
% 1.35/0.99      ( ~ r1_lattice3(sK2,X0_47,X0_48)
% 1.35/0.99      | ~ r1_orders_2(sK2,sK1(sK2,X0_48,X0_47),X0_48)
% 1.35/0.99      | ~ m1_subset_1(X0_48,u1_struct_0(sK2))
% 1.35/0.99      | k2_yellow_0(sK2,X0_47) = X0_48 ),
% 1.35/0.99      inference(subtyping,[status(esa)],[c_475]) ).
% 1.35/0.99  
% 1.35/0.99  cnf(c_1982,plain,
% 1.35/0.99      ( k2_yellow_0(sK2,X0_47) = X0_48
% 1.35/0.99      | r1_lattice3(sK2,X0_47,X0_48) != iProver_top
% 1.35/0.99      | r1_orders_2(sK2,sK1(sK2,X0_48,X0_47),X0_48) != iProver_top
% 1.35/0.99      | m1_subset_1(X0_48,u1_struct_0(sK2)) != iProver_top ),
% 1.35/0.99      inference(predicate_to_equality,[status(thm)],[c_1657]) ).
% 1.35/0.99  
% 1.35/0.99  cnf(c_2591,plain,
% 1.35/0.99      ( sK0(sK2,X0_47,X0_48) = k2_yellow_0(sK2,X1_47)
% 1.35/0.99      | r1_lattice3(sK2,X0_47,X0_48) = iProver_top
% 1.35/0.99      | r1_lattice3(sK2,X0_47,sK1(sK2,sK0(sK2,X0_47,X0_48),X1_47)) != iProver_top
% 1.35/0.99      | r1_lattice3(sK2,X1_47,sK0(sK2,X0_47,X0_48)) != iProver_top
% 1.35/0.99      | m1_subset_1(X0_48,u1_struct_0(sK2)) != iProver_top
% 1.35/0.99      | m1_subset_1(sK1(sK2,sK0(sK2,X0_47,X0_48),X1_47),u1_struct_0(sK2)) != iProver_top
% 1.35/0.99      | m1_subset_1(sK0(sK2,X0_47,X0_48),u1_struct_0(sK2)) != iProver_top ),
% 1.35/0.99      inference(superposition,[status(thm)],[c_1988,c_1982]) ).
% 1.35/0.99  
% 1.35/0.99  cnf(c_1653,plain,
% 1.35/0.99      ( r1_lattice3(sK2,X0_47,X0_48)
% 1.35/0.99      | ~ m1_subset_1(X0_48,u1_struct_0(sK2))
% 1.35/0.99      | m1_subset_1(sK0(sK2,X0_47,X0_48),u1_struct_0(sK2)) ),
% 1.35/0.99      inference(subtyping,[status(esa)],[c_625]) ).
% 1.35/0.99  
% 1.35/0.99  cnf(c_1719,plain,
% 1.35/0.99      ( r1_lattice3(sK2,X0_47,X0_48) = iProver_top
% 1.35/0.99      | m1_subset_1(X0_48,u1_struct_0(sK2)) != iProver_top
% 1.35/0.99      | m1_subset_1(sK0(sK2,X0_47,X0_48),u1_struct_0(sK2)) = iProver_top ),
% 1.35/0.99      inference(predicate_to_equality,[status(thm)],[c_1653]) ).
% 1.35/0.99  
% 1.35/0.99  cnf(c_2740,plain,
% 1.35/0.99      ( m1_subset_1(sK1(sK2,sK0(sK2,X0_47,X0_48),X1_47),u1_struct_0(sK2)) != iProver_top
% 1.35/0.99      | m1_subset_1(X0_48,u1_struct_0(sK2)) != iProver_top
% 1.35/0.99      | r1_lattice3(sK2,X1_47,sK0(sK2,X0_47,X0_48)) != iProver_top
% 1.35/0.99      | r1_lattice3(sK2,X0_47,sK1(sK2,sK0(sK2,X0_47,X0_48),X1_47)) != iProver_top
% 1.35/0.99      | r1_lattice3(sK2,X0_47,X0_48) = iProver_top
% 1.35/0.99      | sK0(sK2,X0_47,X0_48) = k2_yellow_0(sK2,X1_47) ),
% 1.35/0.99      inference(global_propositional_subsumption,[status(thm)],[c_2591,c_1719]) ).
% 1.35/0.99  
% 1.35/0.99  cnf(c_2741,plain,
% 1.35/0.99      ( sK0(sK2,X0_47,X0_48) = k2_yellow_0(sK2,X1_47)
% 1.35/0.99      | r1_lattice3(sK2,X0_47,X0_48) = iProver_top
% 1.35/0.99      | r1_lattice3(sK2,X0_47,sK1(sK2,sK0(sK2,X0_47,X0_48),X1_47)) != iProver_top
% 1.35/0.99      | r1_lattice3(sK2,X1_47,sK0(sK2,X0_47,X0_48)) != iProver_top
% 1.35/0.99      | m1_subset_1(X0_48,u1_struct_0(sK2)) != iProver_top
% 1.35/0.99      | m1_subset_1(sK1(sK2,sK0(sK2,X0_47,X0_48),X1_47),u1_struct_0(sK2)) != iProver_top ),
% 1.35/0.99      inference(renaming,[status(thm)],[c_2740]) ).
% 1.35/0.99  
% 1.35/0.99  cnf(c_2753,plain,
% 1.35/0.99      ( sK0(sK2,X0_47,X0_48) = k2_yellow_0(sK2,X0_47)
% 1.35/0.99      | r1_lattice3(sK2,X0_47,X0_48) = iProver_top
% 1.35/0.99      | r1_lattice3(sK2,X0_47,sK0(sK2,X0_47,X0_48)) != iProver_top
% 1.35/0.99      | m1_subset_1(X0_48,u1_struct_0(sK2)) != iProver_top
% 1.35/0.99      | m1_subset_1(sK1(sK2,sK0(sK2,X0_47,X0_48),X0_47),u1_struct_0(sK2)) != iProver_top
% 1.35/0.99      | m1_subset_1(sK0(sK2,X0_47,X0_48),u1_struct_0(sK2)) != iProver_top ),
% 1.35/0.99      inference(superposition,[status(thm)],[c_1981,c_2741]) ).
% 1.35/0.99  
% 1.35/0.99  cnf(c_2926,plain,
% 1.35/0.99      ( m1_subset_1(sK1(sK2,sK0(sK2,X0_47,X0_48),X0_47),u1_struct_0(sK2)) != iProver_top
% 1.35/0.99      | m1_subset_1(X0_48,u1_struct_0(sK2)) != iProver_top
% 1.35/0.99      | r1_lattice3(sK2,X0_47,sK0(sK2,X0_47,X0_48)) != iProver_top
% 1.35/0.99      | r1_lattice3(sK2,X0_47,X0_48) = iProver_top
% 1.35/0.99      | sK0(sK2,X0_47,X0_48) = k2_yellow_0(sK2,X0_47) ),
% 1.35/0.99      inference(global_propositional_subsumption,[status(thm)],[c_2753,c_1719]) ).
% 1.35/0.99  
% 1.35/0.99  cnf(c_2927,plain,
% 1.35/0.99      ( sK0(sK2,X0_47,X0_48) = k2_yellow_0(sK2,X0_47)
% 1.35/0.99      | r1_lattice3(sK2,X0_47,X0_48) = iProver_top
% 1.35/0.99      | r1_lattice3(sK2,X0_47,sK0(sK2,X0_47,X0_48)) != iProver_top
% 1.35/0.99      | m1_subset_1(X0_48,u1_struct_0(sK2)) != iProver_top
% 1.35/0.99      | m1_subset_1(sK1(sK2,sK0(sK2,X0_47,X0_48),X0_47),u1_struct_0(sK2)) != iProver_top ),
% 1.35/0.99      inference(renaming,[status(thm)],[c_2926]) ).
% 1.35/0.99  
% 1.35/0.99  cnf(c_2938,plain,
% 1.35/0.99      ( sK0(sK2,X0_47,X0_48) = k2_yellow_0(sK2,X0_47)
% 1.35/0.99      | r1_lattice3(sK2,X0_47,X0_48) = iProver_top
% 1.35/0.99      | r1_lattice3(sK2,X0_47,sK0(sK2,X0_47,X0_48)) != iProver_top
% 1.35/0.99      | m1_subset_1(X0_48,u1_struct_0(sK2)) != iProver_top
% 1.35/0.99      | m1_subset_1(sK0(sK2,X0_47,X0_48),u1_struct_0(sK2)) != iProver_top ),
% 1.35/0.99      inference(superposition,[status(thm)],[c_1980,c_2927]) ).
% 1.35/0.99  
% 1.35/0.99  cnf(c_3048,plain,
% 1.35/0.99      ( m1_subset_1(X0_48,u1_struct_0(sK2)) != iProver_top
% 1.35/0.99      | r1_lattice3(sK2,X0_47,sK0(sK2,X0_47,X0_48)) != iProver_top
% 1.35/0.99      | r1_lattice3(sK2,X0_47,X0_48) = iProver_top
% 1.35/0.99      | sK0(sK2,X0_47,X0_48) = k2_yellow_0(sK2,X0_47) ),
% 1.35/0.99      inference(global_propositional_subsumption,[status(thm)],[c_2938,c_1719]) ).
% 1.35/0.99  
% 1.35/0.99  cnf(c_3049,plain,
% 1.35/0.99      ( sK0(sK2,X0_47,X0_48) = k2_yellow_0(sK2,X0_47)
% 1.35/0.99      | r1_lattice3(sK2,X0_47,X0_48) = iProver_top
% 1.35/0.99      | r1_lattice3(sK2,X0_47,sK0(sK2,X0_47,X0_48)) != iProver_top
% 1.35/0.99      | m1_subset_1(X0_48,u1_struct_0(sK2)) != iProver_top ),
% 1.35/0.99      inference(renaming,[status(thm)],[c_3048]) ).
% 1.35/0.99  
% 1.35/0.99  cnf(c_9,plain,
% 1.35/0.99      ( ~ r1_lattice3(X0,X1,X2)
% 1.35/0.99      | r2_yellow_0(X0,X1)
% 1.35/0.99      | ~ m1_subset_1(X2,u1_struct_0(X0))
% 1.35/0.99      | m1_subset_1(sK1(X0,X2,X1),u1_struct_0(X0))
% 1.35/0.99      | ~ v5_orders_2(X0)
% 1.35/0.99      | ~ l1_orders_2(X0) ),
% 1.35/0.99      inference(cnf_transformation,[],[f41]) ).
% 1.35/0.99  
% 1.35/0.99  cnf(c_493,plain,
% 1.35/0.99      ( ~ r1_lattice3(X0,X1,X2)
% 1.35/0.99      | r2_yellow_0(X0,X1)
% 1.35/0.99      | ~ m1_subset_1(X2,u1_struct_0(X0))
% 1.35/0.99      | m1_subset_1(sK1(X0,X2,X1),u1_struct_0(X0))
% 1.35/0.99      | ~ l1_orders_2(X0)
% 1.35/0.99      | sK2 != X0 ),
% 1.35/0.99      inference(resolution_lifted,[status(thm)],[c_9,c_20]) ).
% 1.35/0.99  
% 1.35/0.99  cnf(c_494,plain,
% 1.35/0.99      ( ~ r1_lattice3(sK2,X0,X1)
% 1.35/0.99      | r2_yellow_0(sK2,X0)
% 1.35/0.99      | ~ m1_subset_1(X1,u1_struct_0(sK2))
% 1.35/0.99      | m1_subset_1(sK1(sK2,X1,X0),u1_struct_0(sK2))
% 1.35/0.99      | ~ l1_orders_2(sK2) ),
% 1.35/0.99      inference(unflattening,[status(thm)],[c_493]) ).
% 1.35/0.99  
% 1.35/0.99  cnf(c_498,plain,
% 1.35/0.99      ( m1_subset_1(sK1(sK2,X1,X0),u1_struct_0(sK2))
% 1.35/0.99      | ~ m1_subset_1(X1,u1_struct_0(sK2))
% 1.35/0.99      | r2_yellow_0(sK2,X0)
% 1.35/0.99      | ~ r1_lattice3(sK2,X0,X1) ),
% 1.35/0.99      inference(global_propositional_subsumption,[status(thm)],[c_494,c_19]) ).
% 1.35/0.99  
% 1.35/0.99  cnf(c_499,plain,
% 1.35/0.99      ( ~ r1_lattice3(sK2,X0,X1)
% 1.35/0.99      | r2_yellow_0(sK2,X0)
% 1.35/0.99      | ~ m1_subset_1(X1,u1_struct_0(sK2))
% 1.35/0.99      | m1_subset_1(sK1(sK2,X1,X0),u1_struct_0(sK2)) ),
% 1.35/0.99      inference(renaming,[status(thm)],[c_498]) ).
% 1.35/0.99  
% 1.35/0.99  cnf(c_1656,plain,
% 1.35/0.99      ( ~ r1_lattice3(sK2,X0_47,X0_48)
% 1.35/0.99      | r2_yellow_0(sK2,X0_47)
% 1.35/0.99      | ~ m1_subset_1(X0_48,u1_struct_0(sK2))
% 1.35/0.99      | m1_subset_1(sK1(sK2,X0_48,X0_47),u1_struct_0(sK2)) ),
% 1.35/0.99      inference(subtyping,[status(esa)],[c_499]) ).
% 1.35/0.99  
% 1.35/0.99  cnf(c_1983,plain,
% 1.35/0.99      ( r1_lattice3(sK2,X0_47,X0_48) != iProver_top
% 1.35/0.99      | r2_yellow_0(sK2,X0_47) = iProver_top
% 1.35/0.99      | m1_subset_1(X0_48,u1_struct_0(sK2)) != iProver_top
% 1.35/0.99      | m1_subset_1(sK1(sK2,X0_48,X0_47),u1_struct_0(sK2)) = iProver_top ),
% 1.35/0.99      inference(predicate_to_equality,[status(thm)],[c_1656]) ).
% 1.35/0.99  
% 1.35/0.99  cnf(c_8,plain,
% 1.35/0.99      ( ~ r1_lattice3(X0,X1,X2)
% 1.35/0.99      | r1_lattice3(X0,X1,sK1(X0,X2,X1))
% 1.35/0.99      | r2_yellow_0(X0,X1)
% 1.35/0.99      | ~ m1_subset_1(X2,u1_struct_0(X0))
% 1.35/0.99      | ~ v5_orders_2(X0)
% 1.35/0.99      | ~ l1_orders_2(X0) ),
% 1.35/0.99      inference(cnf_transformation,[],[f42]) ).
% 1.35/0.99  
% 1.35/0.99  cnf(c_517,plain,
% 1.35/0.99      ( ~ r1_lattice3(X0,X1,X2)
% 1.35/0.99      | r1_lattice3(X0,X1,sK1(X0,X2,X1))
% 1.35/0.99      | r2_yellow_0(X0,X1)
% 1.35/0.99      | ~ m1_subset_1(X2,u1_struct_0(X0))
% 1.35/0.99      | ~ l1_orders_2(X0)
% 1.35/0.99      | sK2 != X0 ),
% 1.35/0.99      inference(resolution_lifted,[status(thm)],[c_8,c_20]) ).
% 1.35/0.99  
% 1.35/0.99  cnf(c_518,plain,
% 1.35/0.99      ( ~ r1_lattice3(sK2,X0,X1)
% 1.35/0.99      | r1_lattice3(sK2,X0,sK1(sK2,X1,X0))
% 1.35/0.99      | r2_yellow_0(sK2,X0)
% 1.35/0.99      | ~ m1_subset_1(X1,u1_struct_0(sK2))
% 1.35/0.99      | ~ l1_orders_2(sK2) ),
% 1.35/0.99      inference(unflattening,[status(thm)],[c_517]) ).
% 1.35/0.99  
% 1.35/0.99  cnf(c_522,plain,
% 1.35/0.99      ( ~ m1_subset_1(X1,u1_struct_0(sK2))
% 1.35/0.99      | r2_yellow_0(sK2,X0)
% 1.35/0.99      | r1_lattice3(sK2,X0,sK1(sK2,X1,X0))
% 1.35/0.99      | ~ r1_lattice3(sK2,X0,X1) ),
% 1.35/0.99      inference(global_propositional_subsumption,[status(thm)],[c_518,c_19]) ).
% 1.35/0.99  
% 1.35/0.99  cnf(c_523,plain,
% 1.35/0.99      ( ~ r1_lattice3(sK2,X0,X1)
% 1.35/0.99      | r1_lattice3(sK2,X0,sK1(sK2,X1,X0))
% 1.35/0.99      | r2_yellow_0(sK2,X0)
% 1.35/0.99      | ~ m1_subset_1(X1,u1_struct_0(sK2)) ),
% 1.35/0.99      inference(renaming,[status(thm)],[c_522]) ).
% 1.35/0.99  
% 1.35/0.99  cnf(c_1655,plain,
% 1.35/0.99      ( ~ r1_lattice3(sK2,X0_47,X0_48)
% 1.35/0.99      | r1_lattice3(sK2,X0_47,sK1(sK2,X0_48,X0_47))
% 1.35/0.99      | r2_yellow_0(sK2,X0_47)
% 1.35/0.99      | ~ m1_subset_1(X0_48,u1_struct_0(sK2)) ),
% 1.35/0.99      inference(subtyping,[status(esa)],[c_523]) ).
% 1.35/0.99  
% 1.35/0.99  cnf(c_1984,plain,
% 1.35/0.99      ( r1_lattice3(sK2,X0_47,X0_48) != iProver_top
% 1.35/0.99      | r1_lattice3(sK2,X0_47,sK1(sK2,X0_48,X0_47)) = iProver_top
% 1.35/0.99      | r2_yellow_0(sK2,X0_47) = iProver_top
% 1.35/0.99      | m1_subset_1(X0_48,u1_struct_0(sK2)) != iProver_top ),
% 1.35/0.99      inference(predicate_to_equality,[status(thm)],[c_1655]) ).
% 1.35/0.99  
% 1.35/0.99  cnf(c_7,plain,
% 1.35/0.99      ( ~ r1_lattice3(X0,X1,X2)
% 1.35/0.99      | ~ r1_orders_2(X0,sK1(X0,X2,X1),X2)
% 1.35/0.99      | r2_yellow_0(X0,X1)
% 1.35/0.99      | ~ m1_subset_1(X2,u1_struct_0(X0))
% 1.35/0.99      | ~ v5_orders_2(X0)
% 1.35/0.99      | ~ l1_orders_2(X0) ),
% 1.35/0.99      inference(cnf_transformation,[],[f43]) ).
% 1.35/0.99  
% 1.35/0.99  cnf(c_541,plain,
% 1.35/0.99      ( ~ r1_lattice3(X0,X1,X2)
% 1.35/0.99      | ~ r1_orders_2(X0,sK1(X0,X2,X1),X2)
% 1.35/0.99      | r2_yellow_0(X0,X1)
% 1.35/0.99      | ~ m1_subset_1(X2,u1_struct_0(X0))
% 1.35/0.99      | ~ l1_orders_2(X0)
% 1.35/0.99      | sK2 != X0 ),
% 1.35/0.99      inference(resolution_lifted,[status(thm)],[c_7,c_20]) ).
% 1.35/0.99  
% 1.35/0.99  cnf(c_542,plain,
% 1.35/0.99      ( ~ r1_lattice3(sK2,X0,X1)
% 1.35/0.99      | ~ r1_orders_2(sK2,sK1(sK2,X1,X0),X1)
% 1.35/0.99      | r2_yellow_0(sK2,X0)
% 1.35/0.99      | ~ m1_subset_1(X1,u1_struct_0(sK2))
% 1.35/0.99      | ~ l1_orders_2(sK2) ),
% 1.35/0.99      inference(unflattening,[status(thm)],[c_541]) ).
% 1.35/0.99  
% 1.35/0.99  cnf(c_546,plain,
% 1.35/0.99      ( ~ m1_subset_1(X1,u1_struct_0(sK2))
% 1.35/0.99      | r2_yellow_0(sK2,X0)
% 1.35/0.99      | ~ r1_orders_2(sK2,sK1(sK2,X1,X0),X1)
% 1.35/0.99      | ~ r1_lattice3(sK2,X0,X1) ),
% 1.35/0.99      inference(global_propositional_subsumption,[status(thm)],[c_542,c_19]) ).
% 1.35/0.99  
% 1.35/0.99  cnf(c_547,plain,
% 1.35/0.99      ( ~ r1_lattice3(sK2,X0,X1)
% 1.35/0.99      | ~ r1_orders_2(sK2,sK1(sK2,X1,X0),X1)
% 1.35/0.99      | r2_yellow_0(sK2,X0)
% 1.35/0.99      | ~ m1_subset_1(X1,u1_struct_0(sK2)) ),
% 1.35/0.99      inference(renaming,[status(thm)],[c_546]) ).
% 1.35/0.99  
% 1.35/0.99  cnf(c_1654,plain,
% 1.35/0.99      ( ~ r1_lattice3(sK2,X0_47,X0_48)
% 1.35/0.99      | ~ r1_orders_2(sK2,sK1(sK2,X0_48,X0_47),X0_48)
% 1.35/0.99      | r2_yellow_0(sK2,X0_47)
% 1.35/0.99      | ~ m1_subset_1(X0_48,u1_struct_0(sK2)) ),
% 1.35/0.99      inference(subtyping,[status(esa)],[c_547]) ).
% 1.35/0.99  
% 1.35/0.99  cnf(c_1985,plain,
% 1.35/0.99      ( r1_lattice3(sK2,X0_47,X0_48) != iProver_top
% 1.35/0.99      | r1_orders_2(sK2,sK1(sK2,X0_48,X0_47),X0_48) != iProver_top
% 1.35/0.99      | r2_yellow_0(sK2,X0_47) = iProver_top
% 1.35/0.99      | m1_subset_1(X0_48,u1_struct_0(sK2)) != iProver_top ),
% 1.35/0.99      inference(predicate_to_equality,[status(thm)],[c_1654]) ).
% 1.35/0.99  
% 1.35/0.99  cnf(c_2590,plain,
% 1.35/0.99      ( r1_lattice3(sK2,X0_47,X0_48) = iProver_top
% 1.35/0.99      | r1_lattice3(sK2,X0_47,sK1(sK2,sK0(sK2,X0_47,X0_48),X1_47)) != iProver_top
% 1.35/0.99      | r1_lattice3(sK2,X1_47,sK0(sK2,X0_47,X0_48)) != iProver_top
% 1.35/0.99      | r2_yellow_0(sK2,X1_47) = iProver_top
% 1.35/0.99      | m1_subset_1(X0_48,u1_struct_0(sK2)) != iProver_top
% 1.35/0.99      | m1_subset_1(sK1(sK2,sK0(sK2,X0_47,X0_48),X1_47),u1_struct_0(sK2)) != iProver_top
% 1.35/0.99      | m1_subset_1(sK0(sK2,X0_47,X0_48),u1_struct_0(sK2)) != iProver_top ),
% 1.35/0.99      inference(superposition,[status(thm)],[c_1988,c_1985]) ).
% 1.35/0.99  
% 1.35/0.99  cnf(c_2696,plain,
% 1.35/0.99      ( m1_subset_1(sK1(sK2,sK0(sK2,X0_47,X0_48),X1_47),u1_struct_0(sK2)) != iProver_top
% 1.35/0.99      | m1_subset_1(X0_48,u1_struct_0(sK2)) != iProver_top
% 1.35/0.99      | r2_yellow_0(sK2,X1_47) = iProver_top
% 1.35/0.99      | r1_lattice3(sK2,X1_47,sK0(sK2,X0_47,X0_48)) != iProver_top
% 1.35/0.99      | r1_lattice3(sK2,X0_47,sK1(sK2,sK0(sK2,X0_47,X0_48),X1_47)) != iProver_top
% 1.35/0.99      | r1_lattice3(sK2,X0_47,X0_48) = iProver_top ),
% 1.35/0.99      inference(global_propositional_subsumption,[status(thm)],[c_2590,c_1719]) ).
% 1.35/0.99  
% 1.35/0.99  cnf(c_2697,plain,
% 1.35/0.99      ( r1_lattice3(sK2,X0_47,X0_48) = iProver_top
% 1.35/0.99      | r1_lattice3(sK2,X0_47,sK1(sK2,sK0(sK2,X0_47,X0_48),X1_47)) != iProver_top
% 1.35/0.99      | r1_lattice3(sK2,X1_47,sK0(sK2,X0_47,X0_48)) != iProver_top
% 1.35/0.99      | r2_yellow_0(sK2,X1_47) = iProver_top
% 1.35/0.99      | m1_subset_1(X0_48,u1_struct_0(sK2)) != iProver_top
% 1.35/0.99      | m1_subset_1(sK1(sK2,sK0(sK2,X0_47,X0_48),X1_47),u1_struct_0(sK2)) != iProver_top ),
% 1.35/0.99      inference(renaming,[status(thm)],[c_2696]) ).
% 1.35/0.99  
% 1.35/0.99  cnf(c_2708,plain,
% 1.35/0.99      ( r1_lattice3(sK2,X0_47,X0_48) = iProver_top
% 1.35/0.99      | r1_lattice3(sK2,X0_47,sK0(sK2,X0_47,X0_48)) != iProver_top
% 1.35/0.99      | r2_yellow_0(sK2,X0_47) = iProver_top
% 1.35/0.99      | m1_subset_1(X0_48,u1_struct_0(sK2)) != iProver_top
% 1.35/0.99      | m1_subset_1(sK1(sK2,sK0(sK2,X0_47,X0_48),X0_47),u1_struct_0(sK2)) != iProver_top
% 1.35/0.99      | m1_subset_1(sK0(sK2,X0_47,X0_48),u1_struct_0(sK2)) != iProver_top ),
% 1.35/0.99      inference(superposition,[status(thm)],[c_1984,c_2697]) ).
% 1.35/0.99  
% 1.35/0.99  cnf(c_2833,plain,
% 1.35/0.99      ( m1_subset_1(sK1(sK2,sK0(sK2,X0_47,X0_48),X0_47),u1_struct_0(sK2)) != iProver_top
% 1.35/0.99      | m1_subset_1(X0_48,u1_struct_0(sK2)) != iProver_top
% 1.35/0.99      | r2_yellow_0(sK2,X0_47) = iProver_top
% 1.35/0.99      | r1_lattice3(sK2,X0_47,sK0(sK2,X0_47,X0_48)) != iProver_top
% 1.35/0.99      | r1_lattice3(sK2,X0_47,X0_48) = iProver_top ),
% 1.35/0.99      inference(global_propositional_subsumption,[status(thm)],[c_2708,c_1719]) ).
% 1.35/0.99  
% 1.35/0.99  cnf(c_2834,plain,
% 1.35/0.99      ( r1_lattice3(sK2,X0_47,X0_48) = iProver_top
% 1.35/0.99      | r1_lattice3(sK2,X0_47,sK0(sK2,X0_47,X0_48)) != iProver_top
% 1.35/0.99      | r2_yellow_0(sK2,X0_47) = iProver_top
% 1.35/0.99      | m1_subset_1(X0_48,u1_struct_0(sK2)) != iProver_top
% 1.35/0.99      | m1_subset_1(sK1(sK2,sK0(sK2,X0_47,X0_48),X0_47),u1_struct_0(sK2)) != iProver_top ),
% 1.35/0.99      inference(renaming,[status(thm)],[c_2833]) ).
% 1.35/0.99  
% 1.35/0.99  cnf(c_2844,plain,
% 1.35/0.99      ( r1_lattice3(sK2,X0_47,X0_48) = iProver_top
% 1.35/0.99      | r1_lattice3(sK2,X0_47,sK0(sK2,X0_47,X0_48)) != iProver_top
% 1.35/0.99      | r2_yellow_0(sK2,X0_47) = iProver_top
% 1.35/0.99      | m1_subset_1(X0_48,u1_struct_0(sK2)) != iProver_top
% 1.35/0.99      | m1_subset_1(sK0(sK2,X0_47,X0_48),u1_struct_0(sK2)) != iProver_top ),
% 1.35/0.99      inference(superposition,[status(thm)],[c_1983,c_2834]) ).
% 1.35/0.99  
% 1.35/0.99  cnf(c_2915,plain,
% 1.35/0.99      ( m1_subset_1(X0_48,u1_struct_0(sK2)) != iProver_top
% 1.35/0.99      | r2_yellow_0(sK2,X0_47) = iProver_top
% 1.35/0.99      | r1_lattice3(sK2,X0_47,sK0(sK2,X0_47,X0_48)) != iProver_top
% 1.35/0.99      | r1_lattice3(sK2,X0_47,X0_48) = iProver_top ),
% 1.35/0.99      inference(global_propositional_subsumption,[status(thm)],[c_2844,c_1719]) ).
% 1.35/0.99  
% 1.35/0.99  cnf(c_2916,plain,
% 1.35/0.99      ( r1_lattice3(sK2,X0_47,X0_48) = iProver_top
% 1.35/0.99      | r1_lattice3(sK2,X0_47,sK0(sK2,X0_47,X0_48)) != iProver_top
% 1.35/0.99      | r2_yellow_0(sK2,X0_47) = iProver_top
% 1.35/0.99      | m1_subset_1(X0_48,u1_struct_0(sK2)) != iProver_top ),
% 1.35/0.99      inference(renaming,[status(thm)],[c_2915]) ).
% 1.35/0.99  
% 1.35/0.99  cnf(c_1668,plain,
% 1.35/0.99      ( r1_orders_2(sK2,X0_48,X0_48)
% 1.35/0.99      | ~ m1_subset_1(X0_48,u1_struct_0(sK2))
% 1.35/0.99      | ~ sP1_iProver_split ),
% 1.35/0.99      inference(splitting,
% 1.35/0.99                [splitting(split),new_symbols(definition,[sP1_iProver_split])],
% 1.35/0.99                [c_1662]) ).
% 1.35/0.99  
% 1.35/0.99  cnf(c_1976,plain,
% 1.35/0.99      ( r1_orders_2(sK2,X0_48,X0_48) = iProver_top
% 1.35/0.99      | m1_subset_1(X0_48,u1_struct_0(sK2)) != iProver_top
% 1.35/0.99      | sP1_iProver_split != iProver_top ),
% 1.35/0.99      inference(predicate_to_equality,[status(thm)],[c_1668]) ).
% 1.35/0.99  
% 1.35/0.99  cnf(c_1756,plain,
% 1.35/0.99      ( ~ m1_subset_1(X0_48,u1_struct_0(sK2)) | r1_orders_2(sK2,X0_48,X0_48) ),
% 1.35/0.99      inference(global_propositional_subsumption,
% 1.35/0.99                [status(thm)],
% 1.35/0.99                [c_1668,c_18,c_1669,c_1693]) ).
% 1.35/0.99  
% 1.35/0.99  cnf(c_1757,plain,
% 1.35/0.99      ( r1_orders_2(sK2,X0_48,X0_48) | ~ m1_subset_1(X0_48,u1_struct_0(sK2)) ),
% 1.35/0.99      inference(renaming,[status(thm)],[c_1756]) ).
% 1.35/0.99  
% 1.35/0.99  cnf(c_1758,plain,
% 1.35/0.99      ( r1_orders_2(sK2,X0_48,X0_48) = iProver_top
% 1.35/0.99      | m1_subset_1(X0_48,u1_struct_0(sK2)) != iProver_top ),
% 1.35/0.99      inference(predicate_to_equality,[status(thm)],[c_1757]) ).
% 1.35/0.99  
% 1.35/0.99  cnf(c_2255,plain,
% 1.35/0.99      ( m1_subset_1(X0_48,u1_struct_0(sK2)) != iProver_top
% 1.35/0.99      | r1_orders_2(sK2,X0_48,X0_48) = iProver_top ),
% 1.35/0.99      inference(global_propositional_subsumption,[status(thm)],[c_1976,c_1758]) ).
% 1.35/0.99  
% 1.35/0.99  cnf(c_2256,plain,
% 1.35/0.99      ( r1_orders_2(sK2,X0_48,X0_48) = iProver_top
% 1.35/0.99      | m1_subset_1(X0_48,u1_struct_0(sK2)) != iProver_top ),
% 1.35/0.99      inference(renaming,[status(thm)],[c_2255]) ).
% 1.35/0.99  
% 1.35/0.99  cnf(c_2494,plain,
% 1.35/0.99      ( r1_lattice3(sK2,X0_47,X0_48) != iProver_top
% 1.35/0.99      | r1_orders_2(sK2,sK1(sK2,X0_48,X0_47),sK1(sK2,X0_48,X0_47)) = iProver_top
% 1.35/0.99      | r2_yellow_0(sK2,X0_47) = iProver_top
% 1.35/0.99      | m1_subset_1(X0_48,u1_struct_0(sK2)) != iProver_top ),
% 1.35/0.99      inference(superposition,[status(thm)],[c_1983,c_2256]) ).
% 1.35/0.99  
% 1.35/0.99  cnf(c_2411,plain,
% 1.35/0.99      ( k2_yellow_0(sK2,X0_47) = X0_48
% 1.35/0.99      | r1_lattice3(sK2,X0_47,X0_48) != iProver_top
% 1.35/0.99      | r1_orders_2(sK2,sK1(sK2,X0_48,X0_47),sK1(sK2,X0_48,X0_47)) = iProver_top
% 1.35/0.99      | m1_subset_1(X0_48,u1_struct_0(sK2)) != iProver_top ),
% 1.35/0.99      inference(superposition,[status(thm)],[c_1980,c_2256]) ).
% 1.35/0.99  
% 1.35/0.99  cnf(c_1986,plain,
% 1.35/0.99      ( r1_lattice3(sK2,X0_47,X0_48) = iProver_top
% 1.35/0.99      | m1_subset_1(X0_48,u1_struct_0(sK2)) != iProver_top
% 1.35/0.99      | m1_subset_1(sK0(sK2,X0_47,X0_48),u1_struct_0(sK2)) = iProver_top ),
% 1.35/0.99      inference(predicate_to_equality,[status(thm)],[c_1653]) ).
% 1.35/0.99  
% 1.35/0.99  cnf(c_2311,plain,
% 1.35/0.99      ( r1_lattice3(sK2,X0_47,X0_48) = iProver_top
% 1.35/0.99      | r1_orders_2(sK2,sK0(sK2,X0_47,X0_48),sK0(sK2,X0_47,X0_48)) = iProver_top
% 1.35/0.99      | m1_subset_1(X0_48,u1_struct_0(sK2)) != iProver_top ),
% 1.35/0.99      inference(superposition,[status(thm)],[c_1986,c_2256]) ).
% 1.35/0.99  
% 1.35/0.99  cnf(c_1663,negated_conjecture,
% 1.35/0.99      ( m1_subset_1(sK3,u1_struct_0(sK2)) ),
% 1.35/0.99      inference(subtyping,[status(esa)],[c_18]) ).
% 1.35/0.99  
% 1.35/0.99  cnf(c_1974,plain,
% 1.35/0.99      ( m1_subset_1(sK3,u1_struct_0(sK2)) = iProver_top ),
% 1.35/0.99      inference(predicate_to_equality,[status(thm)],[c_1663]) ).
% 1.35/0.99  
% 1.35/0.99  cnf(c_2262,plain,
% 1.35/0.99      ( r1_orders_2(sK2,sK3,sK3) = iProver_top ),
% 1.35/0.99      inference(superposition,[status(thm)],[c_1974,c_2256]) ).
% 1.35/0.99  
% 1.35/0.99  cnf(c_17,negated_conjecture,
% 1.35/0.99      ( m1_subset_1(sK4,u1_struct_0(sK2)) ),
% 1.35/0.99      inference(cnf_transformation,[],[f49]) ).
% 1.35/0.99  
% 1.35/0.99  cnf(c_1664,negated_conjecture,
% 1.35/0.99      ( m1_subset_1(sK4,u1_struct_0(sK2)) ),
% 1.35/0.99      inference(subtyping,[status(esa)],[c_17]) ).
% 1.35/0.99  
% 1.35/0.99  cnf(c_1973,plain,
% 1.35/0.99      ( m1_subset_1(sK4,u1_struct_0(sK2)) = iProver_top ),
% 1.35/0.99      inference(predicate_to_equality,[status(thm)],[c_1664]) ).
% 1.35/0.99  
% 1.35/0.99  cnf(c_2261,plain,
% 1.35/0.99      ( r1_orders_2(sK2,sK4,sK4) = iProver_top ),
% 1.35/0.99      inference(superposition,[status(thm)],[c_1973,c_2256]) ).
% 1.35/0.99  
% 1.35/0.99  cnf(c_1977,plain,
% 1.35/0.99      ( m1_subset_1(X0_48,u1_struct_0(sK2)) != iProver_top
% 1.35/0.99      | sP0_iProver_split != iProver_top ),
% 1.35/0.99      inference(predicate_to_equality,[status(thm)],[c_1667]) ).
% 1.35/0.99  
% 1.35/0.99  cnf(c_27,plain,
% 1.35/0.99      ( m1_subset_1(sK3,u1_struct_0(sK2)) = iProver_top ),
% 1.35/0.99      inference(predicate_to_equality,[status(thm)],[c_18]) ).
% 1.35/0.99  
% 1.35/0.99  cnf(c_1692,plain,
% 1.35/0.99      ( m1_subset_1(X0_48,u1_struct_0(sK2)) != iProver_top
% 1.35/0.99      | sP0_iProver_split != iProver_top ),
% 1.35/0.99      inference(predicate_to_equality,[status(thm)],[c_1667]) ).
% 1.35/0.99  
% 1.35/0.99  cnf(c_1694,plain,
% 1.35/0.99      ( m1_subset_1(sK3,u1_struct_0(sK2)) != iProver_top
% 1.35/0.99      | sP0_iProver_split != iProver_top ),
% 1.35/0.99      inference(instantiation,[status(thm)],[c_1692]) ).
% 1.35/0.99  
% 1.35/0.99  cnf(c_2547,plain,
% 1.35/0.99      ( sP0_iProver_split != iProver_top ),
% 1.35/0.99      inference(global_propositional_subsumption,
% 1.35/0.99                [status(thm)],
% 1.35/0.99                [c_1977,c_27,c_1694]) ).
% 1.35/0.99  
% 1.35/0.99  cnf(c_1975,plain,
% 1.35/0.99      ( sP1_iProver_split = iProver_top | sP0_iProver_split = iProver_top ),
% 1.35/0.99      inference(predicate_to_equality,[status(thm)],[c_1669]) ).
% 1.35/0.99  
% 1.35/0.99  cnf(c_1688,plain,
% 1.35/0.99      ( sP1_iProver_split = iProver_top | sP0_iProver_split = iProver_top ),
% 1.35/0.99      inference(predicate_to_equality,[status(thm)],[c_1669]) ).
% 1.35/0.99  
% 1.35/0.99  cnf(c_2553,plain,
% 1.35/0.99      ( sP1_iProver_split = iProver_top ),
% 1.35/0.99      inference(global_propositional_subsumption,
% 1.35/0.99                [status(thm)],
% 1.35/0.99                [c_1975,c_27,c_1688,c_1694]) ).
% 1.35/0.99  
% 1.35/0.99  cnf(c_3,plain,
% 1.35/0.99      ( r1_lattice3(X0,X1,X2)
% 1.35/0.99      | ~ r1_orders_2(X0,X2,sK0(X0,X1,X2))
% 1.35/0.99      | ~ m1_subset_1(X2,u1_struct_0(X0))
% 1.35/0.99      | ~ l1_orders_2(X0) ),
% 1.35/0.99      inference(cnf_transformation,[],[f35]) ).
% 1.35/0.99  
% 1.35/0.99  cnf(c_654,plain,
% 1.35/0.99      ( r1_lattice3(X0,X1,X2)
% 1.35/0.99      | ~ r1_orders_2(X0,X2,sK0(X0,X1,X2))
% 1.35/0.99      | ~ m1_subset_1(X2,u1_struct_0(X0))
% 1.35/0.99      | sK2 != X0 ),
% 1.35/0.99      inference(resolution_lifted,[status(thm)],[c_3,c_19]) ).
% 1.35/0.99  
% 1.35/0.99  cnf(c_655,plain,
% 1.35/0.99      ( r1_lattice3(sK2,X0,X1)
% 1.35/0.99      | ~ r1_orders_2(sK2,X1,sK0(sK2,X0,X1))
% 1.35/0.99      | ~ m1_subset_1(X1,u1_struct_0(sK2)) ),
% 1.35/0.99      inference(unflattening,[status(thm)],[c_654]) ).
% 1.35/0.99  
% 1.35/0.99  cnf(c_1652,plain,
% 1.35/0.99      ( r1_lattice3(sK2,X0_47,X0_48)
% 1.35/0.99      | ~ r1_orders_2(sK2,X0_48,sK0(sK2,X0_47,X0_48))
% 1.35/0.99      | ~ m1_subset_1(X0_48,u1_struct_0(sK2)) ),
% 1.35/0.99      inference(subtyping,[status(esa)],[c_655]) ).
% 1.35/0.99  
% 1.35/0.99  cnf(c_1987,plain,
% 1.35/0.99      ( r1_lattice3(sK2,X0_47,X0_48) = iProver_top
% 1.35/0.99      | r1_orders_2(sK2,X0_48,sK0(sK2,X0_47,X0_48)) != iProver_top
% 1.35/0.99      | m1_subset_1(X0_48,u1_struct_0(sK2)) != iProver_top ),
% 1.35/0.99      inference(predicate_to_equality,[status(thm)],[c_1652]) ).
% 1.35/0.99  
% 1.35/0.99  cnf(c_13,plain,
% 1.35/0.99      ( ~ r1_lattice3(X0,X1,X2)
% 1.35/0.99      | r1_orders_2(X0,X2,k2_yellow_0(X0,X1))
% 1.35/0.99      | ~ r2_yellow_0(X0,X1)
% 1.35/0.99      | ~ m1_subset_1(X2,u1_struct_0(X0))
% 1.35/0.99      | ~ m1_subset_1(k2_yellow_0(X0,X1),u1_struct_0(X0))
% 1.35/0.99      | ~ v5_orders_2(X0)
% 1.35/0.99      | ~ l1_orders_2(X0) ),
% 1.35/0.99      inference(cnf_transformation,[],[f52]) ).
% 1.35/0.99  
% 1.35/0.99  cnf(c_394,plain,
% 1.35/0.99      ( ~ r1_lattice3(X0,X1,X2)
% 1.35/0.99      | r1_orders_2(X0,X2,k2_yellow_0(X0,X1))
% 1.35/0.99      | ~ r2_yellow_0(X0,X1)
% 1.35/0.99      | ~ m1_subset_1(X2,u1_struct_0(X0))
% 1.35/0.99      | ~ m1_subset_1(k2_yellow_0(X0,X1),u1_struct_0(X0))
% 1.35/0.99      | ~ l1_orders_2(X0)
% 1.35/0.99      | sK2 != X0 ),
% 1.35/0.99      inference(resolution_lifted,[status(thm)],[c_13,c_20]) ).
% 1.35/0.99  
% 1.35/0.99  cnf(c_395,plain,
% 1.35/0.99      ( ~ r1_lattice3(sK2,X0,X1)
% 1.35/0.99      | r1_orders_2(sK2,X1,k2_yellow_0(sK2,X0))
% 1.35/0.99      | ~ r2_yellow_0(sK2,X0)
% 1.35/0.99      | ~ m1_subset_1(X1,u1_struct_0(sK2))
% 1.35/0.99      | ~ m1_subset_1(k2_yellow_0(sK2,X0),u1_struct_0(sK2))
% 1.35/0.99      | ~ l1_orders_2(sK2) ),
% 1.35/0.99      inference(unflattening,[status(thm)],[c_394]) ).
% 1.35/0.99  
% 1.35/0.99  cnf(c_399,plain,
% 1.35/0.99      ( ~ m1_subset_1(k2_yellow_0(sK2,X0),u1_struct_0(sK2))
% 1.35/0.99      | ~ m1_subset_1(X1,u1_struct_0(sK2))
% 1.35/0.99      | ~ r2_yellow_0(sK2,X0)
% 1.35/0.99      | r1_orders_2(sK2,X1,k2_yellow_0(sK2,X0))
% 1.35/0.99      | ~ r1_lattice3(sK2,X0,X1) ),
% 1.35/0.99      inference(global_propositional_subsumption,[status(thm)],[c_395,c_19]) ).
% 1.35/0.99  
% 1.35/0.99  cnf(c_400,plain,
% 1.35/0.99      ( ~ r1_lattice3(sK2,X0,X1)
% 1.35/0.99      | r1_orders_2(sK2,X1,k2_yellow_0(sK2,X0))
% 1.35/0.99      | ~ r2_yellow_0(sK2,X0)
% 1.35/0.99      | ~ m1_subset_1(X1,u1_struct_0(sK2))
% 1.35/0.99      | ~ m1_subset_1(k2_yellow_0(sK2,X0),u1_struct_0(sK2)) ),
% 1.35/0.99      inference(renaming,[status(thm)],[c_399]) ).
% 1.35/0.99  
% 1.35/0.99  cnf(c_1660,plain,
% 1.35/0.99      ( ~ r1_lattice3(sK2,X0_47,X0_48)
% 1.35/0.99      | r1_orders_2(sK2,X0_48,k2_yellow_0(sK2,X0_47))
% 1.35/0.99      | ~ r2_yellow_0(sK2,X0_47)
% 1.35/0.99      | ~ m1_subset_1(X0_48,u1_struct_0(sK2))
% 1.35/0.99      | ~ m1_subset_1(k2_yellow_0(sK2,X0_47),u1_struct_0(sK2)) ),
% 1.35/0.99      inference(subtyping,[status(esa)],[c_400]) ).
% 1.35/0.99  
% 1.35/0.99  cnf(c_1979,plain,
% 1.35/0.99      ( r1_lattice3(sK2,X0_47,X0_48) != iProver_top
% 1.35/0.99      | r1_orders_2(sK2,X0_48,k2_yellow_0(sK2,X0_47)) = iProver_top
% 1.35/0.99      | r2_yellow_0(sK2,X0_47) != iProver_top
% 1.35/0.99      | m1_subset_1(X0_48,u1_struct_0(sK2)) != iProver_top
% 1.35/0.99      | m1_subset_1(k2_yellow_0(sK2,X0_47),u1_struct_0(sK2)) != iProver_top ),
% 1.35/0.99      inference(predicate_to_equality,[status(thm)],[c_1660]) ).
% 1.35/0.99  
% 1.35/0.99  cnf(c_14,plain,
% 1.35/0.99      ( r1_lattice3(X0,X1,k2_yellow_0(X0,X1))
% 1.35/0.99      | ~ r2_yellow_0(X0,X1)
% 1.35/0.99      | ~ m1_subset_1(k2_yellow_0(X0,X1),u1_struct_0(X0))
% 1.35/0.99      | ~ v5_orders_2(X0)
% 1.35/0.99      | ~ l1_orders_2(X0) ),
% 1.35/0.99      inference(cnf_transformation,[],[f53]) ).
% 1.35/0.99  
% 1.35/0.99  cnf(c_373,plain,
% 1.35/0.99      ( r1_lattice3(X0,X1,k2_yellow_0(X0,X1))
% 1.35/0.99      | ~ r2_yellow_0(X0,X1)
% 1.35/0.99      | ~ m1_subset_1(k2_yellow_0(X0,X1),u1_struct_0(X0))
% 1.35/0.99      | ~ l1_orders_2(X0)
% 1.35/0.99      | sK2 != X0 ),
% 1.35/0.99      inference(resolution_lifted,[status(thm)],[c_14,c_20]) ).
% 1.35/0.99  
% 1.35/0.99  cnf(c_374,plain,
% 1.35/0.99      ( r1_lattice3(sK2,X0,k2_yellow_0(sK2,X0))
% 1.35/0.99      | ~ r2_yellow_0(sK2,X0)
% 1.35/0.99      | ~ m1_subset_1(k2_yellow_0(sK2,X0),u1_struct_0(sK2))
% 1.35/0.99      | ~ l1_orders_2(sK2) ),
% 1.35/0.99      inference(unflattening,[status(thm)],[c_373]) ).
% 1.35/0.99  
% 1.35/0.99  cnf(c_378,plain,
% 1.35/0.99      ( ~ m1_subset_1(k2_yellow_0(sK2,X0),u1_struct_0(sK2))
% 1.35/0.99      | ~ r2_yellow_0(sK2,X0)
% 1.35/0.99      | r1_lattice3(sK2,X0,k2_yellow_0(sK2,X0)) ),
% 1.35/0.99      inference(global_propositional_subsumption,[status(thm)],[c_374,c_19]) ).
% 1.35/0.99  
% 1.35/0.99  cnf(c_379,plain,
% 1.35/0.99      ( r1_lattice3(sK2,X0,k2_yellow_0(sK2,X0))
% 1.35/0.99      | ~ r2_yellow_0(sK2,X0)
% 1.35/0.99      | ~ m1_subset_1(k2_yellow_0(sK2,X0),u1_struct_0(sK2)) ),
% 1.35/0.99      inference(renaming,[status(thm)],[c_378]) ).
% 1.35/0.99  
% 1.35/0.99  cnf(c_1661,plain,
% 1.35/0.99      ( r1_lattice3(sK2,X0_47,k2_yellow_0(sK2,X0_47))
% 1.35/0.99      | ~ r2_yellow_0(sK2,X0_47)
% 1.35/0.99      | ~ m1_subset_1(k2_yellow_0(sK2,X0_47),u1_struct_0(sK2)) ),
% 1.35/0.99      inference(subtyping,[status(esa)],[c_379]) ).
% 1.35/0.99  
% 1.35/0.99  cnf(c_1978,plain,
% 1.35/0.99      ( r1_lattice3(sK2,X0_47,k2_yellow_0(sK2,X0_47)) = iProver_top
% 1.35/0.99      | r2_yellow_0(sK2,X0_47) != iProver_top
% 1.35/0.99      | m1_subset_1(k2_yellow_0(sK2,X0_47),u1_struct_0(sK2)) != iProver_top ),
% 1.35/0.99      inference(predicate_to_equality,[status(thm)],[c_1661]) ).
% 1.35/0.99  
% 1.35/0.99  cnf(c_15,negated_conjecture,
% 1.35/0.99      ( sK3 != sK4 ),
% 1.35/0.99      inference(cnf_transformation,[],[f51]) ).
% 1.35/0.99  
% 1.35/0.99  cnf(c_1666,negated_conjecture,
% 1.35/0.99      ( sK3 != sK4 ),
% 1.35/0.99      inference(subtyping,[status(esa)],[c_15]) ).
% 1.35/0.99  
% 1.35/0.99  
% 1.35/0.99  % SZS output end Saturation for theBenchmark.p
% 1.35/0.99  
% 1.35/0.99  ------                               Statistics
% 1.35/0.99  
% 1.35/0.99  ------ General
% 1.35/0.99  
% 1.35/0.99  abstr_ref_over_cycles:                  0
% 1.35/0.99  abstr_ref_under_cycles:                 0
% 1.35/0.99  gc_basic_clause_elim:                   0
% 1.35/0.99  forced_gc_time:                         0
% 1.35/0.99  parsing_time:                           0.012
% 1.35/0.99  unif_index_cands_time:                  0.
% 1.35/0.99  unif_index_add_time:                    0.
% 1.35/0.99  orderings_time:                         0.
% 1.35/0.99  out_proof_time:                         0.
% 1.35/0.99  total_time:                             0.141
% 1.35/0.99  num_of_symbols:                         53
% 1.35/0.99  num_of_terms:                           1896
% 1.35/0.99  
% 1.35/0.99  ------ Preprocessing
% 1.35/0.99  
% 1.35/0.99  num_of_splits:                          2
% 1.35/0.99  num_of_split_atoms:                     2
% 1.35/0.99  num_of_reused_defs:                     0
% 1.35/0.99  num_eq_ax_congr_red:                    40
% 1.35/0.99  num_of_sem_filtered_clauses:            7
% 1.35/0.99  num_of_subtypes:                        5
% 1.35/0.99  monotx_restored_types:                  0
% 1.35/0.99  sat_num_of_epr_types:                   0
% 1.35/0.99  sat_num_of_non_cyclic_types:            0
% 1.35/0.99  sat_guarded_non_collapsed_types:        1
% 1.35/0.99  num_pure_diseq_elim:                    0
% 1.35/0.99  simp_replaced_by:                       0
% 1.35/0.99  res_preprocessed:                       86
% 1.35/0.99  prep_upred:                             0
% 1.35/0.99  prep_unflattend:                        47
% 1.35/0.99  smt_new_axioms:                         0
% 1.35/0.99  pred_elim_cands:                        4
% 1.35/0.99  pred_elim:                              6
% 1.35/0.99  pred_elim_cl:                           7
% 1.35/0.99  pred_elim_cycles:                       11
% 1.35/0.99  merged_defs:                            0
% 1.35/0.99  merged_defs_ncl:                        0
% 1.35/0.99  bin_hyper_res:                          0
% 1.35/0.99  prep_cycles:                            4
% 1.35/0.99  pred_elim_time:                         0.028
% 1.35/0.99  splitting_time:                         0.
% 1.35/0.99  sem_filter_time:                        0.
% 1.35/0.99  monotx_time:                            0.
% 1.35/0.99  subtype_inf_time:                       0.
% 1.35/0.99  
% 1.35/0.99  ------ Problem properties
% 1.35/0.99  
% 1.35/0.99  clauses:                                18
% 1.35/0.99  conjectures:                            4
% 1.35/0.99  epr:                                    2
% 1.35/0.99  horn:                                   11
% 1.35/0.99  ground:                                 5
% 1.35/0.99  unary:                                  4
% 1.35/0.99  binary:                                 2
% 1.35/0.99  lits:                                   54
% 1.35/0.99  lits_eq:                                5
% 1.35/0.99  fd_pure:                                0
% 1.35/0.99  fd_pseudo:                              0
% 1.35/0.99  fd_cond:                                0
% 1.35/0.99  fd_pseudo_cond:                         3
% 1.35/0.99  ac_symbols:                             0
% 1.35/0.99  
% 1.35/0.99  ------ Propositional Solver
% 1.35/0.99  
% 1.35/0.99  prop_solver_calls:                      32
% 1.35/0.99  prop_fast_solver_calls:                 1041
% 1.35/0.99  smt_solver_calls:                       0
% 1.35/0.99  smt_fast_solver_calls:                  0
% 1.35/0.99  prop_num_of_clauses:                    662
% 1.35/0.99  prop_preprocess_simplified:             2917
% 1.35/0.99  prop_fo_subsumed:                       32
% 1.35/0.99  prop_solver_time:                       0.
% 1.35/0.99  smt_solver_time:                        0.
% 1.35/0.99  smt_fast_solver_time:                   0.
% 1.35/0.99  prop_fast_solver_time:                  0.
% 1.35/0.99  prop_unsat_core_time:                   0.
% 1.35/0.99  
% 1.35/0.99  ------ QBF
% 1.35/0.99  
% 1.35/0.99  qbf_q_res:                              0
% 1.35/0.99  qbf_num_tautologies:                    0
% 1.35/0.99  qbf_prep_cycles:                        0
% 1.35/0.99  
% 1.35/0.99  ------ BMC1
% 1.35/0.99  
% 1.35/0.99  bmc1_current_bound:                     -1
% 1.35/0.99  bmc1_last_solved_bound:                 -1
% 1.35/0.99  bmc1_unsat_core_size:                   -1
% 1.35/0.99  bmc1_unsat_core_parents_size:           -1
% 1.35/0.99  bmc1_merge_next_fun:                    0
% 1.35/0.99  bmc1_unsat_core_clauses_time:           0.
% 1.35/0.99  
% 1.35/0.99  ------ Instantiation
% 1.35/0.99  
% 1.35/0.99  inst_num_of_clauses:                    121
% 1.35/0.99  inst_num_in_passive:                    0
% 1.35/0.99  inst_num_in_active:                     104
% 1.35/0.99  inst_num_in_unprocessed:                17
% 1.35/0.99  inst_num_of_loops:                      150
% 1.35/0.99  inst_num_of_learning_restarts:          0
% 1.35/0.99  inst_num_moves_active_passive:          37
% 1.35/0.99  inst_lit_activity:                      0
% 1.35/0.99  inst_lit_activity_moves:                0
% 1.35/0.99  inst_num_tautologies:                   0
% 1.35/0.99  inst_num_prop_implied:                  0
% 1.35/0.99  inst_num_existing_simplified:           0
% 1.35/0.99  inst_num_eq_res_simplified:             0
% 1.35/0.99  inst_num_child_elim:                    0
% 1.35/0.99  inst_num_of_dismatching_blockings:      38
% 1.35/0.99  inst_num_of_non_proper_insts:           183
% 1.35/0.99  inst_num_of_duplicates:                 0
% 1.35/0.99  inst_inst_num_from_inst_to_res:         0
% 1.35/0.99  inst_dismatching_checking_time:         0.
% 1.35/0.99  
% 1.35/0.99  ------ Resolution
% 1.35/0.99  
% 1.35/0.99  res_num_of_clauses:                     0
% 1.35/0.99  res_num_in_passive:                     0
% 1.35/0.99  res_num_in_active:                      0
% 1.35/0.99  res_num_of_loops:                       90
% 1.35/0.99  res_forward_subset_subsumed:            15
% 1.35/0.99  res_backward_subset_subsumed:           0
% 1.35/0.99  res_forward_subsumed:                   0
% 1.35/0.99  res_backward_subsumed:                  0
% 1.35/0.99  res_forward_subsumption_resolution:     3
% 1.35/0.99  res_backward_subsumption_resolution:    0
% 1.35/0.99  res_clause_to_clause_subsumption:       187
% 1.35/0.99  res_orphan_elimination:                 0
% 1.35/0.99  res_tautology_del:                      32
% 1.35/0.99  res_num_eq_res_simplified:              0
% 1.35/0.99  res_num_sel_changes:                    0
% 1.35/0.99  res_moves_from_active_to_pass:          0
% 1.35/0.99  
% 1.35/0.99  ------ Superposition
% 1.35/0.99  
% 1.35/0.99  sup_time_total:                         0.
% 1.35/0.99  sup_time_generating:                    0.
% 1.35/0.99  sup_time_sim_full:                      0.
% 1.35/0.99  sup_time_sim_immed:                     0.
% 1.35/0.99  
% 1.35/0.99  sup_num_of_clauses:                     27
% 1.35/0.99  sup_num_in_active:                      27
% 1.35/0.99  sup_num_in_passive:                     0
% 1.35/0.99  sup_num_of_loops:                       29
% 1.35/0.99  sup_fw_superposition:                   10
% 1.35/0.99  sup_bw_superposition:                   6
% 1.35/0.99  sup_immediate_simplified:               2
% 1.35/0.99  sup_given_eliminated:                   0
% 1.35/0.99  comparisons_done:                       0
% 1.35/0.99  comparisons_avoided:                    0
% 1.35/0.99  
% 1.35/0.99  ------ Simplifications
% 1.35/0.99  
% 1.35/0.99  
% 1.35/0.99  sim_fw_subset_subsumed:                 0
% 1.35/0.99  sim_bw_subset_subsumed:                 2
% 1.35/0.99  sim_fw_subsumed:                        0
% 1.35/0.99  sim_bw_subsumed:                        2
% 1.35/0.99  sim_fw_subsumption_res:                 0
% 1.35/0.99  sim_bw_subsumption_res:                 0
% 1.35/0.99  sim_tautology_del:                      1
% 1.35/0.99  sim_eq_tautology_del:                   0
% 1.35/0.99  sim_eq_res_simp:                        0
% 1.35/0.99  sim_fw_demodulated:                     0
% 1.35/0.99  sim_bw_demodulated:                     0
% 1.35/0.99  sim_light_normalised:                   0
% 1.35/0.99  sim_joinable_taut:                      0
% 1.35/0.99  sim_joinable_simp:                      0
% 1.35/0.99  sim_ac_normalised:                      0
% 1.35/0.99  sim_smt_subsumption:                    0
% 1.35/0.99  
%------------------------------------------------------------------------------
