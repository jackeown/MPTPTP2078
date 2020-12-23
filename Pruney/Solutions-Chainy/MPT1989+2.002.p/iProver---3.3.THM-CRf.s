%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n018.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:28:36 EST 2020

% Result     : Theorem 2.43s
% Output     : CNFRefutation 2.43s
% Verified   : 
% Statistics : Number of formulae       :  229 ( 895 expanded)
%              Number of clauses        :  150 ( 232 expanded)
%              Number of leaves         :   21 ( 234 expanded)
%              Depth                    :   22
%              Number of atoms          : 1188 (6463 expanded)
%              Number of equality atoms :  167 ( 211 expanded)
%              Maximal formula depth    :   18 (   6 average)
%              Maximal clause size      :   21 (   4 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f3,axiom,(
    ! [X0] :
      ( l1_orders_2(X0)
     => ! [X1,X2] :
          ( m1_subset_1(X2,u1_struct_0(X0))
         => ( r2_lattice3(X0,X1,X2)
          <=> ! [X3] :
                ( m1_subset_1(X3,u1_struct_0(X0))
               => ( r2_hidden(X3,X1)
                 => r1_orders_2(X0,X3,X2) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f19,plain,(
    ! [X0] :
      ( ! [X1,X2] :
          ( ( r2_lattice3(X0,X1,X2)
          <=> ! [X3] :
                ( r1_orders_2(X0,X3,X2)
                | ~ r2_hidden(X3,X1)
                | ~ m1_subset_1(X3,u1_struct_0(X0)) ) )
          | ~ m1_subset_1(X2,u1_struct_0(X0)) )
      | ~ l1_orders_2(X0) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f20,plain,(
    ! [X0] :
      ( ! [X1,X2] :
          ( ( r2_lattice3(X0,X1,X2)
          <=> ! [X3] :
                ( r1_orders_2(X0,X3,X2)
                | ~ r2_hidden(X3,X1)
                | ~ m1_subset_1(X3,u1_struct_0(X0)) ) )
          | ~ m1_subset_1(X2,u1_struct_0(X0)) )
      | ~ l1_orders_2(X0) ) ),
    inference(flattening,[],[f19])).

fof(f38,plain,(
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
    inference(nnf_transformation,[],[f20])).

fof(f39,plain,(
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
    inference(rectify,[],[f38])).

fof(f40,plain,(
    ! [X2,X1,X0] :
      ( ? [X3] :
          ( ~ r1_orders_2(X0,X3,X2)
          & r2_hidden(X3,X1)
          & m1_subset_1(X3,u1_struct_0(X0)) )
     => ( ~ r1_orders_2(X0,sK0(X0,X1,X2),X2)
        & r2_hidden(sK0(X0,X1,X2),X1)
        & m1_subset_1(sK0(X0,X1,X2),u1_struct_0(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f41,plain,(
    ! [X0] :
      ( ! [X1,X2] :
          ( ( ( r2_lattice3(X0,X1,X2)
              | ( ~ r1_orders_2(X0,sK0(X0,X1,X2),X2)
                & r2_hidden(sK0(X0,X1,X2),X1)
                & m1_subset_1(sK0(X0,X1,X2),u1_struct_0(X0)) ) )
            & ( ! [X4] :
                  ( r1_orders_2(X0,X4,X2)
                  | ~ r2_hidden(X4,X1)
                  | ~ m1_subset_1(X4,u1_struct_0(X0)) )
              | ~ r2_lattice3(X0,X1,X2) ) )
          | ~ m1_subset_1(X2,u1_struct_0(X0)) )
      | ~ l1_orders_2(X0) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f39,f40])).

fof(f54,plain,(
    ! [X4,X2,X0,X1] :
      ( r1_orders_2(X0,X4,X2)
      | ~ r2_hidden(X4,X1)
      | ~ m1_subset_1(X4,u1_struct_0(X0))
      | ~ r2_lattice3(X0,X1,X2)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ l1_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f41])).

fof(f12,conjecture,(
    ! [X0] :
      ( ( l1_orders_2(X0)
        & v2_lattice3(X0)
        & v1_lattice3(X0)
        & v5_orders_2(X0)
        & v4_orders_2(X0)
        & v3_orders_2(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,u1_struct_0(X0))
         => ( v5_waybel_6(X1,X0)
           => v4_waybel_7(X1,X0) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f13,negated_conjecture,(
    ~ ! [X0] :
        ( ( l1_orders_2(X0)
          & v2_lattice3(X0)
          & v1_lattice3(X0)
          & v5_orders_2(X0)
          & v4_orders_2(X0)
          & v3_orders_2(X0) )
       => ! [X1] :
            ( m1_subset_1(X1,u1_struct_0(X0))
           => ( v5_waybel_6(X1,X0)
             => v4_waybel_7(X1,X0) ) ) ) ),
    inference(negated_conjecture,[],[f12])).

fof(f36,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ~ v4_waybel_7(X1,X0)
          & v5_waybel_6(X1,X0)
          & m1_subset_1(X1,u1_struct_0(X0)) )
      & l1_orders_2(X0)
      & v2_lattice3(X0)
      & v1_lattice3(X0)
      & v5_orders_2(X0)
      & v4_orders_2(X0)
      & v3_orders_2(X0) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f37,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ~ v4_waybel_7(X1,X0)
          & v5_waybel_6(X1,X0)
          & m1_subset_1(X1,u1_struct_0(X0)) )
      & l1_orders_2(X0)
      & v2_lattice3(X0)
      & v1_lattice3(X0)
      & v5_orders_2(X0)
      & v4_orders_2(X0)
      & v3_orders_2(X0) ) ),
    inference(flattening,[],[f36])).

fof(f50,plain,(
    ! [X0] :
      ( ? [X1] :
          ( ~ v4_waybel_7(X1,X0)
          & v5_waybel_6(X1,X0)
          & m1_subset_1(X1,u1_struct_0(X0)) )
     => ( ~ v4_waybel_7(sK4,X0)
        & v5_waybel_6(sK4,X0)
        & m1_subset_1(sK4,u1_struct_0(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f49,plain,
    ( ? [X0] :
        ( ? [X1] :
            ( ~ v4_waybel_7(X1,X0)
            & v5_waybel_6(X1,X0)
            & m1_subset_1(X1,u1_struct_0(X0)) )
        & l1_orders_2(X0)
        & v2_lattice3(X0)
        & v1_lattice3(X0)
        & v5_orders_2(X0)
        & v4_orders_2(X0)
        & v3_orders_2(X0) )
   => ( ? [X1] :
          ( ~ v4_waybel_7(X1,sK3)
          & v5_waybel_6(X1,sK3)
          & m1_subset_1(X1,u1_struct_0(sK3)) )
      & l1_orders_2(sK3)
      & v2_lattice3(sK3)
      & v1_lattice3(sK3)
      & v5_orders_2(sK3)
      & v4_orders_2(sK3)
      & v3_orders_2(sK3) ) ),
    introduced(choice_axiom,[])).

fof(f51,plain,
    ( ~ v4_waybel_7(sK4,sK3)
    & v5_waybel_6(sK4,sK3)
    & m1_subset_1(sK4,u1_struct_0(sK3))
    & l1_orders_2(sK3)
    & v2_lattice3(sK3)
    & v1_lattice3(sK3)
    & v5_orders_2(sK3)
    & v4_orders_2(sK3)
    & v3_orders_2(sK3) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3,sK4])],[f37,f50,f49])).

fof(f86,plain,(
    l1_orders_2(sK3) ),
    inference(cnf_transformation,[],[f51])).

fof(f56,plain,(
    ! [X2,X0,X1] :
      ( r2_lattice3(X0,X1,X2)
      | r2_hidden(sK0(X0,X1,X2),X1)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ l1_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f41])).

fof(f9,axiom,(
    ! [X0] :
      ( ( l1_orders_2(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,u1_struct_0(X0))
         => ! [X2] :
              ( m1_subset_1(X2,u1_struct_0(X0))
             => ( r2_hidden(X2,k5_waybel_0(X0,X1))
              <=> r1_orders_2(X0,X2,X1) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f30,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( r2_hidden(X2,k5_waybel_0(X0,X1))
              <=> r1_orders_2(X0,X2,X1) )
              | ~ m1_subset_1(X2,u1_struct_0(X0)) )
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l1_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f31,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( r2_hidden(X2,k5_waybel_0(X0,X1))
              <=> r1_orders_2(X0,X2,X1) )
              | ~ m1_subset_1(X2,u1_struct_0(X0)) )
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l1_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f30])).

fof(f44,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( ( r2_hidden(X2,k5_waybel_0(X0,X1))
                  | ~ r1_orders_2(X0,X2,X1) )
                & ( r1_orders_2(X0,X2,X1)
                  | ~ r2_hidden(X2,k5_waybel_0(X0,X1)) ) )
              | ~ m1_subset_1(X2,u1_struct_0(X0)) )
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l1_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(nnf_transformation,[],[f31])).

fof(f71,plain,(
    ! [X2,X0,X1] :
      ( r1_orders_2(X0,X2,X1)
      | ~ r2_hidden(X2,k5_waybel_0(X0,X1))
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f44])).

fof(f2,axiom,(
    ! [X0] :
      ( l1_orders_2(X0)
     => ( v1_lattice3(X0)
       => ~ v2_struct_0(X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f17,plain,(
    ! [X0] :
      ( ~ v2_struct_0(X0)
      | ~ v1_lattice3(X0)
      | ~ l1_orders_2(X0) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f18,plain,(
    ! [X0] :
      ( ~ v2_struct_0(X0)
      | ~ v1_lattice3(X0)
      | ~ l1_orders_2(X0) ) ),
    inference(flattening,[],[f17])).

fof(f53,plain,(
    ! [X0] :
      ( ~ v2_struct_0(X0)
      | ~ v1_lattice3(X0)
      | ~ l1_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f84,plain,(
    v1_lattice3(sK3) ),
    inference(cnf_transformation,[],[f51])).

fof(f57,plain,(
    ! [X2,X0,X1] :
      ( r2_lattice3(X0,X1,X2)
      | ~ r1_orders_2(X0,sK0(X0,X1,X2),X2)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ l1_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f41])).

fof(f55,plain,(
    ! [X2,X0,X1] :
      ( r2_lattice3(X0,X1,X2)
      | m1_subset_1(sK0(X0,X1,X2),u1_struct_0(X0))
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ l1_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f41])).

fof(f5,axiom,(
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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f14,plain,(
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
    inference(rectify,[],[f5])).

fof(f22,plain,(
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
    inference(ennf_transformation,[],[f14])).

fof(f23,plain,(
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
    inference(flattening,[],[f22])).

fof(f42,plain,(
    ! [X2,X1,X0] :
      ( ? [X3] :
          ( ~ r1_orders_2(X0,X1,X3)
          & r2_lattice3(X0,X2,X3)
          & m1_subset_1(X3,u1_struct_0(X0)) )
     => ( ~ r1_orders_2(X0,X1,sK1(X0,X1,X2))
        & r2_lattice3(X0,X2,sK1(X0,X1,X2))
        & m1_subset_1(sK1(X0,X1,X2),u1_struct_0(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f43,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( ( r1_yellow_0(X0,X2)
                  & k1_yellow_0(X0,X2) = X1 )
                | ( ~ r1_orders_2(X0,X1,sK1(X0,X1,X2))
                  & r2_lattice3(X0,X2,sK1(X0,X1,X2))
                  & m1_subset_1(sK1(X0,X1,X2),u1_struct_0(X0)) )
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
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1])],[f23,f42])).

fof(f62,plain,(
    ! [X2,X0,X1] :
      ( k1_yellow_0(X0,X2) = X1
      | r2_lattice3(X0,X2,sK1(X0,X1,X2))
      | ~ r2_lattice3(X0,X2,X1)
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | ~ v5_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f43])).

fof(f83,plain,(
    v5_orders_2(sK3) ),
    inference(cnf_transformation,[],[f51])).

fof(f63,plain,(
    ! [X2,X0,X1] :
      ( k1_yellow_0(X0,X2) = X1
      | ~ r1_orders_2(X0,X1,sK1(X0,X1,X2))
      | ~ r2_lattice3(X0,X2,X1)
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | ~ v5_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f43])).

fof(f61,plain,(
    ! [X2,X0,X1] :
      ( k1_yellow_0(X0,X2) = X1
      | m1_subset_1(sK1(X0,X1,X2),u1_struct_0(X0))
      | ~ r2_lattice3(X0,X2,X1)
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | ~ v5_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f43])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( l1_orders_2(X0)
     => m1_subset_1(k1_yellow_0(X0,X1),u1_struct_0(X0)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f21,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k1_yellow_0(X0,X1),u1_struct_0(X0))
      | ~ l1_orders_2(X0) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f58,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k1_yellow_0(X0,X1),u1_struct_0(X0))
      | ~ l1_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f7,axiom,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,u1_struct_0(X0))
        & l1_orders_2(X0)
        & v4_orders_2(X0)
        & ~ v2_struct_0(X0) )
     => v12_waybel_0(k5_waybel_0(X0,X1),X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f26,plain,(
    ! [X0,X1] :
      ( v12_waybel_0(k5_waybel_0(X0,X1),X0)
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | ~ v4_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f27,plain,(
    ! [X0,X1] :
      ( v12_waybel_0(k5_waybel_0(X0,X1),X0)
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | ~ v4_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f26])).

fof(f68,plain,(
    ! [X0,X1] :
      ( v12_waybel_0(k5_waybel_0(X0,X1),X0)
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | ~ v4_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f10,axiom,(
    ! [X0] :
      ( ( l1_orders_2(X0)
        & v2_lattice3(X0)
        & v1_lattice3(X0)
        & v5_orders_2(X0)
        & v4_orders_2(X0)
        & v3_orders_2(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,u1_struct_0(X0))
         => ( v4_waybel_7(X1,X0)
          <=> ? [X2] :
                ( k1_yellow_0(X0,X2) = X1
                & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
                & v1_waybel_7(X2,X0)
                & v12_waybel_0(X2,X0)
                & v1_waybel_0(X2,X0)
                & ~ v1_xboole_0(X2) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f32,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( v4_waybel_7(X1,X0)
          <=> ? [X2] :
                ( k1_yellow_0(X0,X2) = X1
                & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
                & v1_waybel_7(X2,X0)
                & v12_waybel_0(X2,X0)
                & v1_waybel_0(X2,X0)
                & ~ v1_xboole_0(X2) ) )
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l1_orders_2(X0)
      | ~ v2_lattice3(X0)
      | ~ v1_lattice3(X0)
      | ~ v5_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v3_orders_2(X0) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f33,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( v4_waybel_7(X1,X0)
          <=> ? [X2] :
                ( k1_yellow_0(X0,X2) = X1
                & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
                & v1_waybel_7(X2,X0)
                & v12_waybel_0(X2,X0)
                & v1_waybel_0(X2,X0)
                & ~ v1_xboole_0(X2) ) )
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l1_orders_2(X0)
      | ~ v2_lattice3(X0)
      | ~ v1_lattice3(X0)
      | ~ v5_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v3_orders_2(X0) ) ),
    inference(flattening,[],[f32])).

fof(f45,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ( v4_waybel_7(X1,X0)
              | ! [X2] :
                  ( k1_yellow_0(X0,X2) != X1
                  | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
                  | ~ v1_waybel_7(X2,X0)
                  | ~ v12_waybel_0(X2,X0)
                  | ~ v1_waybel_0(X2,X0)
                  | v1_xboole_0(X2) ) )
            & ( ? [X2] :
                  ( k1_yellow_0(X0,X2) = X1
                  & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
                  & v1_waybel_7(X2,X0)
                  & v12_waybel_0(X2,X0)
                  & v1_waybel_0(X2,X0)
                  & ~ v1_xboole_0(X2) )
              | ~ v4_waybel_7(X1,X0) ) )
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l1_orders_2(X0)
      | ~ v2_lattice3(X0)
      | ~ v1_lattice3(X0)
      | ~ v5_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v3_orders_2(X0) ) ),
    inference(nnf_transformation,[],[f33])).

fof(f46,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ( v4_waybel_7(X1,X0)
              | ! [X2] :
                  ( k1_yellow_0(X0,X2) != X1
                  | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
                  | ~ v1_waybel_7(X2,X0)
                  | ~ v12_waybel_0(X2,X0)
                  | ~ v1_waybel_0(X2,X0)
                  | v1_xboole_0(X2) ) )
            & ( ? [X3] :
                  ( k1_yellow_0(X0,X3) = X1
                  & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))
                  & v1_waybel_7(X3,X0)
                  & v12_waybel_0(X3,X0)
                  & v1_waybel_0(X3,X0)
                  & ~ v1_xboole_0(X3) )
              | ~ v4_waybel_7(X1,X0) ) )
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l1_orders_2(X0)
      | ~ v2_lattice3(X0)
      | ~ v1_lattice3(X0)
      | ~ v5_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v3_orders_2(X0) ) ),
    inference(rectify,[],[f45])).

fof(f47,plain,(
    ! [X1,X0] :
      ( ? [X3] :
          ( k1_yellow_0(X0,X3) = X1
          & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))
          & v1_waybel_7(X3,X0)
          & v12_waybel_0(X3,X0)
          & v1_waybel_0(X3,X0)
          & ~ v1_xboole_0(X3) )
     => ( k1_yellow_0(X0,sK2(X0,X1)) = X1
        & m1_subset_1(sK2(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))
        & v1_waybel_7(sK2(X0,X1),X0)
        & v12_waybel_0(sK2(X0,X1),X0)
        & v1_waybel_0(sK2(X0,X1),X0)
        & ~ v1_xboole_0(sK2(X0,X1)) ) ) ),
    introduced(choice_axiom,[])).

fof(f48,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ( v4_waybel_7(X1,X0)
              | ! [X2] :
                  ( k1_yellow_0(X0,X2) != X1
                  | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
                  | ~ v1_waybel_7(X2,X0)
                  | ~ v12_waybel_0(X2,X0)
                  | ~ v1_waybel_0(X2,X0)
                  | v1_xboole_0(X2) ) )
            & ( ( k1_yellow_0(X0,sK2(X0,X1)) = X1
                & m1_subset_1(sK2(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))
                & v1_waybel_7(sK2(X0,X1),X0)
                & v12_waybel_0(sK2(X0,X1),X0)
                & v1_waybel_0(sK2(X0,X1),X0)
                & ~ v1_xboole_0(sK2(X0,X1)) )
              | ~ v4_waybel_7(X1,X0) ) )
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l1_orders_2(X0)
      | ~ v2_lattice3(X0)
      | ~ v1_lattice3(X0)
      | ~ v5_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v3_orders_2(X0) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2])],[f46,f47])).

fof(f79,plain,(
    ! [X2,X0,X1] :
      ( v4_waybel_7(X1,X0)
      | k1_yellow_0(X0,X2) != X1
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ v1_waybel_7(X2,X0)
      | ~ v12_waybel_0(X2,X0)
      | ~ v1_waybel_0(X2,X0)
      | v1_xboole_0(X2)
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | ~ v2_lattice3(X0)
      | ~ v1_lattice3(X0)
      | ~ v5_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v3_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f48])).

fof(f92,plain,(
    ! [X2,X0] :
      ( v4_waybel_7(k1_yellow_0(X0,X2),X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ v1_waybel_7(X2,X0)
      | ~ v12_waybel_0(X2,X0)
      | ~ v1_waybel_0(X2,X0)
      | v1_xboole_0(X2)
      | ~ m1_subset_1(k1_yellow_0(X0,X2),u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | ~ v2_lattice3(X0)
      | ~ v1_lattice3(X0)
      | ~ v5_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v3_orders_2(X0) ) ),
    inference(equality_resolution,[],[f79])).

fof(f11,axiom,(
    ! [X0] :
      ( ( l1_orders_2(X0)
        & v2_lattice3(X0)
        & v1_lattice3(X0)
        & v5_orders_2(X0)
        & v4_orders_2(X0)
        & v3_orders_2(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,u1_struct_0(X0))
         => ( v5_waybel_6(X1,X0)
           => v1_waybel_7(k5_waybel_0(X0,X1),X0) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f34,plain,(
    ! [X0] :
      ( ! [X1] :
          ( v1_waybel_7(k5_waybel_0(X0,X1),X0)
          | ~ v5_waybel_6(X1,X0)
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l1_orders_2(X0)
      | ~ v2_lattice3(X0)
      | ~ v1_lattice3(X0)
      | ~ v5_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v3_orders_2(X0) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f35,plain,(
    ! [X0] :
      ( ! [X1] :
          ( v1_waybel_7(k5_waybel_0(X0,X1),X0)
          | ~ v5_waybel_6(X1,X0)
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l1_orders_2(X0)
      | ~ v2_lattice3(X0)
      | ~ v1_lattice3(X0)
      | ~ v5_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v3_orders_2(X0) ) ),
    inference(flattening,[],[f34])).

fof(f80,plain,(
    ! [X0,X1] :
      ( v1_waybel_7(k5_waybel_0(X0,X1),X0)
      | ~ v5_waybel_6(X1,X0)
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | ~ v2_lattice3(X0)
      | ~ v1_lattice3(X0)
      | ~ v5_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v3_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f35])).

fof(f88,plain,(
    v5_waybel_6(sK4,sK3) ),
    inference(cnf_transformation,[],[f51])).

fof(f81,plain,(
    v3_orders_2(sK3) ),
    inference(cnf_transformation,[],[f51])).

fof(f82,plain,(
    v4_orders_2(sK3) ),
    inference(cnf_transformation,[],[f51])).

fof(f85,plain,(
    v2_lattice3(sK3) ),
    inference(cnf_transformation,[],[f51])).

fof(f87,plain,(
    m1_subset_1(sK4,u1_struct_0(sK3)) ),
    inference(cnf_transformation,[],[f51])).

fof(f6,axiom,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,u1_struct_0(X0))
        & l1_orders_2(X0)
        & ~ v2_struct_0(X0) )
     => m1_subset_1(k5_waybel_0(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f24,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k5_waybel_0(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f25,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k5_waybel_0(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f24])).

fof(f67,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k5_waybel_0(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f72,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(X2,k5_waybel_0(X0,X1))
      | ~ r1_orders_2(X0,X2,X1)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f44])).

fof(f8,axiom,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,u1_struct_0(X0))
        & l1_orders_2(X0)
        & v3_orders_2(X0)
        & ~ v2_struct_0(X0) )
     => ( v1_waybel_0(k5_waybel_0(X0,X1),X0)
        & ~ v1_xboole_0(k5_waybel_0(X0,X1)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f28,plain,(
    ! [X0,X1] :
      ( ( v1_waybel_0(k5_waybel_0(X0,X1),X0)
        & ~ v1_xboole_0(k5_waybel_0(X0,X1)) )
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f29,plain,(
    ! [X0,X1] :
      ( ( v1_waybel_0(k5_waybel_0(X0,X1),X0)
        & ~ v1_xboole_0(k5_waybel_0(X0,X1)) )
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f28])).

fof(f69,plain,(
    ! [X0,X1] :
      ( ~ v1_xboole_0(k5_waybel_0(X0,X1))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f70,plain,(
    ! [X0,X1] :
      ( v1_waybel_0(k5_waybel_0(X0,X1),X0)
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f1,axiom,(
    ! [X0] :
      ( ( l1_orders_2(X0)
        & v3_orders_2(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,u1_struct_0(X0))
         => r1_orders_2(X0,X1,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f15,plain,(
    ! [X0] :
      ( ! [X1] :
          ( r1_orders_2(X0,X1,X1)
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l1_orders_2(X0)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f16,plain,(
    ! [X0] :
      ( ! [X1] :
          ( r1_orders_2(X0,X1,X1)
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l1_orders_2(X0)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f15])).

fof(f52,plain,(
    ! [X0,X1] :
      ( r1_orders_2(X0,X1,X1)
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f16])).

fof(f89,plain,(
    ~ v4_waybel_7(sK4,sK3) ),
    inference(cnf_transformation,[],[f51])).

cnf(c_5,plain,
    ( ~ r2_lattice3(X0,X1,X2)
    | r1_orders_2(X0,X3,X2)
    | ~ r2_hidden(X3,X1)
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | ~ m1_subset_1(X3,u1_struct_0(X0))
    | ~ l1_orders_2(X0) ),
    inference(cnf_transformation,[],[f54])).

cnf(c_32,negated_conjecture,
    ( l1_orders_2(sK3) ),
    inference(cnf_transformation,[],[f86])).

cnf(c_1871,plain,
    ( ~ r2_lattice3(X0,X1,X2)
    | r1_orders_2(X0,X3,X2)
    | ~ r2_hidden(X3,X1)
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | ~ m1_subset_1(X3,u1_struct_0(X0))
    | sK3 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_5,c_32])).

cnf(c_1872,plain,
    ( ~ r2_lattice3(sK3,X0,X1)
    | r1_orders_2(sK3,X2,X1)
    | ~ r2_hidden(X2,X0)
    | ~ m1_subset_1(X1,u1_struct_0(sK3))
    | ~ m1_subset_1(X2,u1_struct_0(sK3)) ),
    inference(unflattening,[status(thm)],[c_1871])).

cnf(c_3800,plain,
    ( ~ r2_lattice3(sK3,X0_55,X1_55)
    | r1_orders_2(sK3,X2_55,X1_55)
    | ~ r2_hidden(X2_55,X0_55)
    | ~ m1_subset_1(X1_55,u1_struct_0(sK3))
    | ~ m1_subset_1(X2_55,u1_struct_0(sK3)) ),
    inference(subtyping,[status(esa)],[c_1872])).

cnf(c_5725,plain,
    ( ~ r2_lattice3(sK3,X0_55,sK1(sK3,X1_55,k5_waybel_0(sK3,sK4)))
    | r1_orders_2(sK3,X1_55,sK1(sK3,X1_55,k5_waybel_0(sK3,sK4)))
    | ~ r2_hidden(X1_55,X0_55)
    | ~ m1_subset_1(X1_55,u1_struct_0(sK3))
    | ~ m1_subset_1(sK1(sK3,X1_55,k5_waybel_0(sK3,sK4)),u1_struct_0(sK3)) ),
    inference(instantiation,[status(thm)],[c_3800])).

cnf(c_7244,plain,
    ( ~ r2_lattice3(sK3,k5_waybel_0(sK3,X0_55),sK1(sK3,X1_55,k5_waybel_0(sK3,sK4)))
    | r1_orders_2(sK3,X1_55,sK1(sK3,X1_55,k5_waybel_0(sK3,sK4)))
    | ~ r2_hidden(X1_55,k5_waybel_0(sK3,X0_55))
    | ~ m1_subset_1(X1_55,u1_struct_0(sK3))
    | ~ m1_subset_1(sK1(sK3,X1_55,k5_waybel_0(sK3,sK4)),u1_struct_0(sK3)) ),
    inference(instantiation,[status(thm)],[c_5725])).

cnf(c_7245,plain,
    ( r2_lattice3(sK3,k5_waybel_0(sK3,X0_55),sK1(sK3,X1_55,k5_waybel_0(sK3,sK4))) != iProver_top
    | r1_orders_2(sK3,X1_55,sK1(sK3,X1_55,k5_waybel_0(sK3,sK4))) = iProver_top
    | r2_hidden(X1_55,k5_waybel_0(sK3,X0_55)) != iProver_top
    | m1_subset_1(X1_55,u1_struct_0(sK3)) != iProver_top
    | m1_subset_1(sK1(sK3,X1_55,k5_waybel_0(sK3,sK4)),u1_struct_0(sK3)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_7244])).

cnf(c_7247,plain,
    ( r2_lattice3(sK3,k5_waybel_0(sK3,sK4),sK1(sK3,sK4,k5_waybel_0(sK3,sK4))) != iProver_top
    | r1_orders_2(sK3,sK4,sK1(sK3,sK4,k5_waybel_0(sK3,sK4))) = iProver_top
    | r2_hidden(sK4,k5_waybel_0(sK3,sK4)) != iProver_top
    | m1_subset_1(sK1(sK3,sK4,k5_waybel_0(sK3,sK4)),u1_struct_0(sK3)) != iProver_top
    | m1_subset_1(sK4,u1_struct_0(sK3)) != iProver_top ),
    inference(instantiation,[status(thm)],[c_7245])).

cnf(c_3,plain,
    ( r2_lattice3(X0,X1,X2)
    | r2_hidden(sK0(X0,X1,X2),X1)
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | ~ l1_orders_2(X0) ),
    inference(cnf_transformation,[],[f56])).

cnf(c_1905,plain,
    ( r2_lattice3(X0,X1,X2)
    | r2_hidden(sK0(X0,X1,X2),X1)
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | sK3 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_3,c_32])).

cnf(c_1906,plain,
    ( r2_lattice3(sK3,X0,X1)
    | r2_hidden(sK0(sK3,X0,X1),X0)
    | ~ m1_subset_1(X1,u1_struct_0(sK3)) ),
    inference(unflattening,[status(thm)],[c_1905])).

cnf(c_3798,plain,
    ( r2_lattice3(sK3,X0_55,X1_55)
    | r2_hidden(sK0(sK3,X0_55,X1_55),X0_55)
    | ~ m1_subset_1(X1_55,u1_struct_0(sK3)) ),
    inference(subtyping,[status(esa)],[c_1906])).

cnf(c_4366,plain,
    ( r2_lattice3(sK3,X0_55,X1_55) = iProver_top
    | r2_hidden(sK0(sK3,X0_55,X1_55),X0_55) = iProver_top
    | m1_subset_1(X1_55,u1_struct_0(sK3)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3798])).

cnf(c_20,plain,
    ( r1_orders_2(X0,X1,X2)
    | ~ r2_hidden(X1,k5_waybel_0(X0,X2))
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | ~ m1_subset_1(X1,u1_struct_0(X0))
    | v2_struct_0(X0)
    | ~ l1_orders_2(X0) ),
    inference(cnf_transformation,[],[f71])).

cnf(c_1,plain,
    ( ~ v1_lattice3(X0)
    | ~ v2_struct_0(X0)
    | ~ l1_orders_2(X0) ),
    inference(cnf_transformation,[],[f53])).

cnf(c_740,plain,
    ( r1_orders_2(X0,X1,X2)
    | ~ r2_hidden(X1,k5_waybel_0(X0,X2))
    | ~ m1_subset_1(X1,u1_struct_0(X0))
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | ~ v1_lattice3(X0)
    | ~ l1_orders_2(X0) ),
    inference(resolution,[status(thm)],[c_20,c_1])).

cnf(c_34,negated_conjecture,
    ( v1_lattice3(sK3) ),
    inference(cnf_transformation,[],[f84])).

cnf(c_1233,plain,
    ( r1_orders_2(X0,X1,X2)
    | ~ r2_hidden(X1,k5_waybel_0(X0,X2))
    | ~ m1_subset_1(X1,u1_struct_0(X0))
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | ~ l1_orders_2(X0)
    | sK3 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_740,c_34])).

cnf(c_1234,plain,
    ( r1_orders_2(sK3,X0,X1)
    | ~ r2_hidden(X0,k5_waybel_0(sK3,X1))
    | ~ m1_subset_1(X0,u1_struct_0(sK3))
    | ~ m1_subset_1(X1,u1_struct_0(sK3))
    | ~ l1_orders_2(sK3) ),
    inference(unflattening,[status(thm)],[c_1233])).

cnf(c_1236,plain,
    ( ~ m1_subset_1(X1,u1_struct_0(sK3))
    | ~ m1_subset_1(X0,u1_struct_0(sK3))
    | ~ r2_hidden(X0,k5_waybel_0(sK3,X1))
    | r1_orders_2(sK3,X0,X1) ),
    inference(global_propositional_subsumption,[status(thm)],[c_1234,c_32])).

cnf(c_1237,plain,
    ( r1_orders_2(sK3,X0,X1)
    | ~ r2_hidden(X0,k5_waybel_0(sK3,X1))
    | ~ m1_subset_1(X1,u1_struct_0(sK3))
    | ~ m1_subset_1(X0,u1_struct_0(sK3)) ),
    inference(renaming,[status(thm)],[c_1236])).

cnf(c_3811,plain,
    ( r1_orders_2(sK3,X0_55,X1_55)
    | ~ r2_hidden(X0_55,k5_waybel_0(sK3,X1_55))
    | ~ m1_subset_1(X0_55,u1_struct_0(sK3))
    | ~ m1_subset_1(X1_55,u1_struct_0(sK3)) ),
    inference(subtyping,[status(esa)],[c_1237])).

cnf(c_4353,plain,
    ( r1_orders_2(sK3,X0_55,X1_55) = iProver_top
    | r2_hidden(X0_55,k5_waybel_0(sK3,X1_55)) != iProver_top
    | m1_subset_1(X0_55,u1_struct_0(sK3)) != iProver_top
    | m1_subset_1(X1_55,u1_struct_0(sK3)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3811])).

cnf(c_5454,plain,
    ( r2_lattice3(sK3,k5_waybel_0(sK3,X0_55),X1_55) = iProver_top
    | r1_orders_2(sK3,sK0(sK3,k5_waybel_0(sK3,X0_55),X1_55),X0_55) = iProver_top
    | m1_subset_1(X0_55,u1_struct_0(sK3)) != iProver_top
    | m1_subset_1(X1_55,u1_struct_0(sK3)) != iProver_top
    | m1_subset_1(sK0(sK3,k5_waybel_0(sK3,X0_55),X1_55),u1_struct_0(sK3)) != iProver_top ),
    inference(superposition,[status(thm)],[c_4366,c_4353])).

cnf(c_5467,plain,
    ( r2_lattice3(sK3,k5_waybel_0(sK3,sK4),sK4) = iProver_top
    | r1_orders_2(sK3,sK0(sK3,k5_waybel_0(sK3,sK4),sK4),sK4) = iProver_top
    | m1_subset_1(sK0(sK3,k5_waybel_0(sK3,sK4),sK4),u1_struct_0(sK3)) != iProver_top
    | m1_subset_1(sK4,u1_struct_0(sK3)) != iProver_top ),
    inference(instantiation,[status(thm)],[c_5454])).

cnf(c_2,plain,
    ( r2_lattice3(X0,X1,X2)
    | ~ r1_orders_2(X0,sK0(X0,X1,X2),X2)
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | ~ l1_orders_2(X0) ),
    inference(cnf_transformation,[],[f57])).

cnf(c_1920,plain,
    ( r2_lattice3(X0,X1,X2)
    | ~ r1_orders_2(X0,sK0(X0,X1,X2),X2)
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | sK3 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_2,c_32])).

cnf(c_1921,plain,
    ( r2_lattice3(sK3,X0,X1)
    | ~ r1_orders_2(sK3,sK0(sK3,X0,X1),X1)
    | ~ m1_subset_1(X1,u1_struct_0(sK3)) ),
    inference(unflattening,[status(thm)],[c_1920])).

cnf(c_3797,plain,
    ( r2_lattice3(sK3,X0_55,X1_55)
    | ~ r1_orders_2(sK3,sK0(sK3,X0_55,X1_55),X1_55)
    | ~ m1_subset_1(X1_55,u1_struct_0(sK3)) ),
    inference(subtyping,[status(esa)],[c_1921])).

cnf(c_5261,plain,
    ( r2_lattice3(sK3,k5_waybel_0(sK3,sK4),X0_55)
    | ~ r1_orders_2(sK3,sK0(sK3,k5_waybel_0(sK3,sK4),X0_55),X0_55)
    | ~ m1_subset_1(X0_55,u1_struct_0(sK3)) ),
    inference(instantiation,[status(thm)],[c_3797])).

cnf(c_5267,plain,
    ( r2_lattice3(sK3,k5_waybel_0(sK3,sK4),X0_55) = iProver_top
    | r1_orders_2(sK3,sK0(sK3,k5_waybel_0(sK3,sK4),X0_55),X0_55) != iProver_top
    | m1_subset_1(X0_55,u1_struct_0(sK3)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_5261])).

cnf(c_5269,plain,
    ( r2_lattice3(sK3,k5_waybel_0(sK3,sK4),sK4) = iProver_top
    | r1_orders_2(sK3,sK0(sK3,k5_waybel_0(sK3,sK4),sK4),sK4) != iProver_top
    | m1_subset_1(sK4,u1_struct_0(sK3)) != iProver_top ),
    inference(instantiation,[status(thm)],[c_5267])).

cnf(c_4,plain,
    ( r2_lattice3(X0,X1,X2)
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | m1_subset_1(sK0(X0,X1,X2),u1_struct_0(X0))
    | ~ l1_orders_2(X0) ),
    inference(cnf_transformation,[],[f55])).

cnf(c_1890,plain,
    ( r2_lattice3(X0,X1,X2)
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | m1_subset_1(sK0(X0,X1,X2),u1_struct_0(X0))
    | sK3 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_4,c_32])).

cnf(c_1891,plain,
    ( r2_lattice3(sK3,X0,X1)
    | ~ m1_subset_1(X1,u1_struct_0(sK3))
    | m1_subset_1(sK0(sK3,X0,X1),u1_struct_0(sK3)) ),
    inference(unflattening,[status(thm)],[c_1890])).

cnf(c_3799,plain,
    ( r2_lattice3(sK3,X0_55,X1_55)
    | ~ m1_subset_1(X1_55,u1_struct_0(sK3))
    | m1_subset_1(sK0(sK3,X0_55,X1_55),u1_struct_0(sK3)) ),
    inference(subtyping,[status(esa)],[c_1891])).

cnf(c_5262,plain,
    ( r2_lattice3(sK3,k5_waybel_0(sK3,sK4),X0_55)
    | ~ m1_subset_1(X0_55,u1_struct_0(sK3))
    | m1_subset_1(sK0(sK3,k5_waybel_0(sK3,sK4),X0_55),u1_struct_0(sK3)) ),
    inference(instantiation,[status(thm)],[c_3799])).

cnf(c_5263,plain,
    ( r2_lattice3(sK3,k5_waybel_0(sK3,sK4),X0_55) = iProver_top
    | m1_subset_1(X0_55,u1_struct_0(sK3)) != iProver_top
    | m1_subset_1(sK0(sK3,k5_waybel_0(sK3,sK4),X0_55),u1_struct_0(sK3)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_5262])).

cnf(c_5265,plain,
    ( r2_lattice3(sK3,k5_waybel_0(sK3,sK4),sK4) = iProver_top
    | m1_subset_1(sK0(sK3,k5_waybel_0(sK3,sK4),sK4),u1_struct_0(sK3)) = iProver_top
    | m1_subset_1(sK4,u1_struct_0(sK3)) != iProver_top ),
    inference(instantiation,[status(thm)],[c_5263])).

cnf(c_11,plain,
    ( ~ r2_lattice3(X0,X1,X2)
    | r2_lattice3(X0,X1,sK1(X0,X2,X1))
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | ~ v5_orders_2(X0)
    | ~ l1_orders_2(X0)
    | k1_yellow_0(X0,X1) = X2 ),
    inference(cnf_transformation,[],[f62])).

cnf(c_35,negated_conjecture,
    ( v5_orders_2(sK3) ),
    inference(cnf_transformation,[],[f83])).

cnf(c_1704,plain,
    ( ~ r2_lattice3(X0,X1,X2)
    | r2_lattice3(X0,X1,sK1(X0,X2,X1))
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | ~ l1_orders_2(X0)
    | k1_yellow_0(X0,X1) = X2
    | sK3 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_11,c_35])).

cnf(c_1705,plain,
    ( ~ r2_lattice3(sK3,X0,X1)
    | r2_lattice3(sK3,X0,sK1(sK3,X1,X0))
    | ~ m1_subset_1(X1,u1_struct_0(sK3))
    | ~ l1_orders_2(sK3)
    | k1_yellow_0(sK3,X0) = X1 ),
    inference(unflattening,[status(thm)],[c_1704])).

cnf(c_1709,plain,
    ( ~ m1_subset_1(X1,u1_struct_0(sK3))
    | r2_lattice3(sK3,X0,sK1(sK3,X1,X0))
    | ~ r2_lattice3(sK3,X0,X1)
    | k1_yellow_0(sK3,X0) = X1 ),
    inference(global_propositional_subsumption,[status(thm)],[c_1705,c_32])).

cnf(c_1710,plain,
    ( ~ r2_lattice3(sK3,X0,X1)
    | r2_lattice3(sK3,X0,sK1(sK3,X1,X0))
    | ~ m1_subset_1(X1,u1_struct_0(sK3))
    | k1_yellow_0(sK3,X0) = X1 ),
    inference(renaming,[status(thm)],[c_1709])).

cnf(c_3806,plain,
    ( ~ r2_lattice3(sK3,X0_55,X1_55)
    | r2_lattice3(sK3,X0_55,sK1(sK3,X1_55,X0_55))
    | ~ m1_subset_1(X1_55,u1_struct_0(sK3))
    | k1_yellow_0(sK3,X0_55) = X1_55 ),
    inference(subtyping,[status(esa)],[c_1710])).

cnf(c_5054,plain,
    ( ~ r2_lattice3(sK3,k5_waybel_0(sK3,sK4),X0_55)
    | r2_lattice3(sK3,k5_waybel_0(sK3,sK4),sK1(sK3,X0_55,k5_waybel_0(sK3,sK4)))
    | ~ m1_subset_1(X0_55,u1_struct_0(sK3))
    | k1_yellow_0(sK3,k5_waybel_0(sK3,sK4)) = X0_55 ),
    inference(instantiation,[status(thm)],[c_3806])).

cnf(c_5065,plain,
    ( k1_yellow_0(sK3,k5_waybel_0(sK3,sK4)) = X0_55
    | r2_lattice3(sK3,k5_waybel_0(sK3,sK4),X0_55) != iProver_top
    | r2_lattice3(sK3,k5_waybel_0(sK3,sK4),sK1(sK3,X0_55,k5_waybel_0(sK3,sK4))) = iProver_top
    | m1_subset_1(X0_55,u1_struct_0(sK3)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_5054])).

cnf(c_5067,plain,
    ( k1_yellow_0(sK3,k5_waybel_0(sK3,sK4)) = sK4
    | r2_lattice3(sK3,k5_waybel_0(sK3,sK4),sK1(sK3,sK4,k5_waybel_0(sK3,sK4))) = iProver_top
    | r2_lattice3(sK3,k5_waybel_0(sK3,sK4),sK4) != iProver_top
    | m1_subset_1(sK4,u1_struct_0(sK3)) != iProver_top ),
    inference(instantiation,[status(thm)],[c_5065])).

cnf(c_10,plain,
    ( ~ r2_lattice3(X0,X1,X2)
    | ~ r1_orders_2(X0,X2,sK1(X0,X2,X1))
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | ~ v5_orders_2(X0)
    | ~ l1_orders_2(X0)
    | k1_yellow_0(X0,X1) = X2 ),
    inference(cnf_transformation,[],[f63])).

cnf(c_1728,plain,
    ( ~ r2_lattice3(X0,X1,X2)
    | ~ r1_orders_2(X0,X2,sK1(X0,X2,X1))
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | ~ l1_orders_2(X0)
    | k1_yellow_0(X0,X1) = X2
    | sK3 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_10,c_35])).

cnf(c_1729,plain,
    ( ~ r2_lattice3(sK3,X0,X1)
    | ~ r1_orders_2(sK3,X1,sK1(sK3,X1,X0))
    | ~ m1_subset_1(X1,u1_struct_0(sK3))
    | ~ l1_orders_2(sK3)
    | k1_yellow_0(sK3,X0) = X1 ),
    inference(unflattening,[status(thm)],[c_1728])).

cnf(c_1733,plain,
    ( ~ m1_subset_1(X1,u1_struct_0(sK3))
    | ~ r1_orders_2(sK3,X1,sK1(sK3,X1,X0))
    | ~ r2_lattice3(sK3,X0,X1)
    | k1_yellow_0(sK3,X0) = X1 ),
    inference(global_propositional_subsumption,[status(thm)],[c_1729,c_32])).

cnf(c_1734,plain,
    ( ~ r2_lattice3(sK3,X0,X1)
    | ~ r1_orders_2(sK3,X1,sK1(sK3,X1,X0))
    | ~ m1_subset_1(X1,u1_struct_0(sK3))
    | k1_yellow_0(sK3,X0) = X1 ),
    inference(renaming,[status(thm)],[c_1733])).

cnf(c_3805,plain,
    ( ~ r2_lattice3(sK3,X0_55,X1_55)
    | ~ r1_orders_2(sK3,X1_55,sK1(sK3,X1_55,X0_55))
    | ~ m1_subset_1(X1_55,u1_struct_0(sK3))
    | k1_yellow_0(sK3,X0_55) = X1_55 ),
    inference(subtyping,[status(esa)],[c_1734])).

cnf(c_5055,plain,
    ( ~ r2_lattice3(sK3,k5_waybel_0(sK3,sK4),X0_55)
    | ~ r1_orders_2(sK3,X0_55,sK1(sK3,X0_55,k5_waybel_0(sK3,sK4)))
    | ~ m1_subset_1(X0_55,u1_struct_0(sK3))
    | k1_yellow_0(sK3,k5_waybel_0(sK3,sK4)) = X0_55 ),
    inference(instantiation,[status(thm)],[c_3805])).

cnf(c_5061,plain,
    ( k1_yellow_0(sK3,k5_waybel_0(sK3,sK4)) = X0_55
    | r2_lattice3(sK3,k5_waybel_0(sK3,sK4),X0_55) != iProver_top
    | r1_orders_2(sK3,X0_55,sK1(sK3,X0_55,k5_waybel_0(sK3,sK4))) != iProver_top
    | m1_subset_1(X0_55,u1_struct_0(sK3)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_5055])).

cnf(c_5063,plain,
    ( k1_yellow_0(sK3,k5_waybel_0(sK3,sK4)) = sK4
    | r2_lattice3(sK3,k5_waybel_0(sK3,sK4),sK4) != iProver_top
    | r1_orders_2(sK3,sK4,sK1(sK3,sK4,k5_waybel_0(sK3,sK4))) != iProver_top
    | m1_subset_1(sK4,u1_struct_0(sK3)) != iProver_top ),
    inference(instantiation,[status(thm)],[c_5061])).

cnf(c_12,plain,
    ( ~ r2_lattice3(X0,X1,X2)
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | m1_subset_1(sK1(X0,X2,X1),u1_struct_0(X0))
    | ~ v5_orders_2(X0)
    | ~ l1_orders_2(X0)
    | k1_yellow_0(X0,X1) = X2 ),
    inference(cnf_transformation,[],[f61])).

cnf(c_1680,plain,
    ( ~ r2_lattice3(X0,X1,X2)
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | m1_subset_1(sK1(X0,X2,X1),u1_struct_0(X0))
    | ~ l1_orders_2(X0)
    | k1_yellow_0(X0,X1) = X2
    | sK3 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_12,c_35])).

cnf(c_1681,plain,
    ( ~ r2_lattice3(sK3,X0,X1)
    | ~ m1_subset_1(X1,u1_struct_0(sK3))
    | m1_subset_1(sK1(sK3,X1,X0),u1_struct_0(sK3))
    | ~ l1_orders_2(sK3)
    | k1_yellow_0(sK3,X0) = X1 ),
    inference(unflattening,[status(thm)],[c_1680])).

cnf(c_1685,plain,
    ( m1_subset_1(sK1(sK3,X1,X0),u1_struct_0(sK3))
    | ~ m1_subset_1(X1,u1_struct_0(sK3))
    | ~ r2_lattice3(sK3,X0,X1)
    | k1_yellow_0(sK3,X0) = X1 ),
    inference(global_propositional_subsumption,[status(thm)],[c_1681,c_32])).

cnf(c_1686,plain,
    ( ~ r2_lattice3(sK3,X0,X1)
    | ~ m1_subset_1(X1,u1_struct_0(sK3))
    | m1_subset_1(sK1(sK3,X1,X0),u1_struct_0(sK3))
    | k1_yellow_0(sK3,X0) = X1 ),
    inference(renaming,[status(thm)],[c_1685])).

cnf(c_3807,plain,
    ( ~ r2_lattice3(sK3,X0_55,X1_55)
    | ~ m1_subset_1(X1_55,u1_struct_0(sK3))
    | m1_subset_1(sK1(sK3,X1_55,X0_55),u1_struct_0(sK3))
    | k1_yellow_0(sK3,X0_55) = X1_55 ),
    inference(subtyping,[status(esa)],[c_1686])).

cnf(c_5056,plain,
    ( ~ r2_lattice3(sK3,k5_waybel_0(sK3,sK4),X0_55)
    | ~ m1_subset_1(X0_55,u1_struct_0(sK3))
    | m1_subset_1(sK1(sK3,X0_55,k5_waybel_0(sK3,sK4)),u1_struct_0(sK3))
    | k1_yellow_0(sK3,k5_waybel_0(sK3,sK4)) = X0_55 ),
    inference(instantiation,[status(thm)],[c_3807])).

cnf(c_5057,plain,
    ( k1_yellow_0(sK3,k5_waybel_0(sK3,sK4)) = X0_55
    | r2_lattice3(sK3,k5_waybel_0(sK3,sK4),X0_55) != iProver_top
    | m1_subset_1(X0_55,u1_struct_0(sK3)) != iProver_top
    | m1_subset_1(sK1(sK3,X0_55,k5_waybel_0(sK3,sK4)),u1_struct_0(sK3)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_5056])).

cnf(c_5059,plain,
    ( k1_yellow_0(sK3,k5_waybel_0(sK3,sK4)) = sK4
    | r2_lattice3(sK3,k5_waybel_0(sK3,sK4),sK4) != iProver_top
    | m1_subset_1(sK1(sK3,sK4,k5_waybel_0(sK3,sK4)),u1_struct_0(sK3)) = iProver_top
    | m1_subset_1(sK4,u1_struct_0(sK3)) != iProver_top ),
    inference(instantiation,[status(thm)],[c_5057])).

cnf(c_3829,plain,
    ( X0_55 != X1_55
    | X2_55 != X1_55
    | X2_55 = X0_55 ),
    theory(equality)).

cnf(c_4767,plain,
    ( X0_55 != X1_55
    | X0_55 = k1_yellow_0(sK3,k5_waybel_0(sK3,sK4))
    | k1_yellow_0(sK3,k5_waybel_0(sK3,sK4)) != X1_55 ),
    inference(instantiation,[status(thm)],[c_3829])).

cnf(c_4768,plain,
    ( k1_yellow_0(sK3,k5_waybel_0(sK3,sK4)) != sK4
    | sK4 = k1_yellow_0(sK3,k5_waybel_0(sK3,sK4))
    | sK4 != sK4 ),
    inference(instantiation,[status(thm)],[c_4767])).

cnf(c_3838,plain,
    ( ~ v4_waybel_7(X0_55,X0_56)
    | v4_waybel_7(X1_55,X0_56)
    | X1_55 != X0_55 ),
    theory(equality)).

cnf(c_4659,plain,
    ( v4_waybel_7(X0_55,sK3)
    | ~ v4_waybel_7(k1_yellow_0(sK3,k5_waybel_0(sK3,sK4)),sK3)
    | X0_55 != k1_yellow_0(sK3,k5_waybel_0(sK3,sK4)) ),
    inference(instantiation,[status(thm)],[c_3838])).

cnf(c_4661,plain,
    ( ~ v4_waybel_7(k1_yellow_0(sK3,k5_waybel_0(sK3,sK4)),sK3)
    | v4_waybel_7(sK4,sK3)
    | sK4 != k1_yellow_0(sK3,k5_waybel_0(sK3,sK4)) ),
    inference(instantiation,[status(thm)],[c_4659])).

cnf(c_6,plain,
    ( m1_subset_1(k1_yellow_0(X0,X1),u1_struct_0(X0))
    | ~ l1_orders_2(X0) ),
    inference(cnf_transformation,[],[f58])).

cnf(c_1862,plain,
    ( m1_subset_1(k1_yellow_0(X0,X1),u1_struct_0(X0))
    | sK3 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_6,c_32])).

cnf(c_1863,plain,
    ( m1_subset_1(k1_yellow_0(sK3,X0),u1_struct_0(sK3)) ),
    inference(unflattening,[status(thm)],[c_1862])).

cnf(c_16,plain,
    ( v12_waybel_0(k5_waybel_0(X0,X1),X0)
    | ~ m1_subset_1(X1,u1_struct_0(X0))
    | ~ v4_orders_2(X0)
    | v2_struct_0(X0)
    | ~ l1_orders_2(X0) ),
    inference(cnf_transformation,[],[f68])).

cnf(c_21,plain,
    ( ~ v1_waybel_7(X0,X1)
    | v4_waybel_7(k1_yellow_0(X1,X0),X1)
    | ~ v1_waybel_0(X0,X1)
    | ~ v12_waybel_0(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ m1_subset_1(k1_yellow_0(X1,X0),u1_struct_0(X1))
    | ~ v2_lattice3(X1)
    | v1_xboole_0(X0)
    | ~ v4_orders_2(X1)
    | ~ v5_orders_2(X1)
    | ~ v1_lattice3(X1)
    | ~ v3_orders_2(X1)
    | ~ l1_orders_2(X1) ),
    inference(cnf_transformation,[],[f92])).

cnf(c_28,plain,
    ( ~ v5_waybel_6(X0,X1)
    | v1_waybel_7(k5_waybel_0(X1,X0),X1)
    | ~ m1_subset_1(X0,u1_struct_0(X1))
    | ~ v2_lattice3(X1)
    | ~ v4_orders_2(X1)
    | ~ v5_orders_2(X1)
    | ~ v1_lattice3(X1)
    | ~ v3_orders_2(X1)
    | ~ l1_orders_2(X1) ),
    inference(cnf_transformation,[],[f80])).

cnf(c_30,negated_conjecture,
    ( v5_waybel_6(sK4,sK3) ),
    inference(cnf_transformation,[],[f88])).

cnf(c_435,plain,
    ( v1_waybel_7(k5_waybel_0(X0,X1),X0)
    | ~ m1_subset_1(X1,u1_struct_0(X0))
    | ~ v2_lattice3(X0)
    | ~ v4_orders_2(X0)
    | ~ v5_orders_2(X0)
    | ~ v1_lattice3(X0)
    | ~ v3_orders_2(X0)
    | ~ l1_orders_2(X0)
    | sK3 != X0
    | sK4 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_28,c_30])).

cnf(c_436,plain,
    ( v1_waybel_7(k5_waybel_0(sK3,sK4),sK3)
    | ~ m1_subset_1(sK4,u1_struct_0(sK3))
    | ~ v2_lattice3(sK3)
    | ~ v4_orders_2(sK3)
    | ~ v5_orders_2(sK3)
    | ~ v1_lattice3(sK3)
    | ~ v3_orders_2(sK3)
    | ~ l1_orders_2(sK3) ),
    inference(unflattening,[status(thm)],[c_435])).

cnf(c_37,negated_conjecture,
    ( v3_orders_2(sK3) ),
    inference(cnf_transformation,[],[f81])).

cnf(c_36,negated_conjecture,
    ( v4_orders_2(sK3) ),
    inference(cnf_transformation,[],[f82])).

cnf(c_33,negated_conjecture,
    ( v2_lattice3(sK3) ),
    inference(cnf_transformation,[],[f85])).

cnf(c_31,negated_conjecture,
    ( m1_subset_1(sK4,u1_struct_0(sK3)) ),
    inference(cnf_transformation,[],[f87])).

cnf(c_438,plain,
    ( v1_waybel_7(k5_waybel_0(sK3,sK4),sK3) ),
    inference(global_propositional_subsumption,[status(thm)],[c_436,c_37,c_36,c_35,c_34,c_33,c_32,c_31])).

cnf(c_492,plain,
    ( v4_waybel_7(k1_yellow_0(X0,X1),X0)
    | ~ v1_waybel_0(X1,X0)
    | ~ v12_waybel_0(X1,X0)
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
    | ~ m1_subset_1(k1_yellow_0(X0,X1),u1_struct_0(X0))
    | ~ v2_lattice3(X0)
    | v1_xboole_0(X1)
    | ~ v4_orders_2(X0)
    | ~ v5_orders_2(X0)
    | ~ v1_lattice3(X0)
    | ~ v3_orders_2(X0)
    | ~ l1_orders_2(X0)
    | k5_waybel_0(sK3,sK4) != X1
    | sK3 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_21,c_438])).

cnf(c_493,plain,
    ( v4_waybel_7(k1_yellow_0(sK3,k5_waybel_0(sK3,sK4)),sK3)
    | ~ v1_waybel_0(k5_waybel_0(sK3,sK4),sK3)
    | ~ v12_waybel_0(k5_waybel_0(sK3,sK4),sK3)
    | ~ m1_subset_1(k5_waybel_0(sK3,sK4),k1_zfmisc_1(u1_struct_0(sK3)))
    | ~ m1_subset_1(k1_yellow_0(sK3,k5_waybel_0(sK3,sK4)),u1_struct_0(sK3))
    | ~ v2_lattice3(sK3)
    | v1_xboole_0(k5_waybel_0(sK3,sK4))
    | ~ v4_orders_2(sK3)
    | ~ v5_orders_2(sK3)
    | ~ v1_lattice3(sK3)
    | ~ v3_orders_2(sK3)
    | ~ l1_orders_2(sK3) ),
    inference(unflattening,[status(thm)],[c_492])).

cnf(c_495,plain,
    ( v1_xboole_0(k5_waybel_0(sK3,sK4))
    | v4_waybel_7(k1_yellow_0(sK3,k5_waybel_0(sK3,sK4)),sK3)
    | ~ v1_waybel_0(k5_waybel_0(sK3,sK4),sK3)
    | ~ v12_waybel_0(k5_waybel_0(sK3,sK4),sK3)
    | ~ m1_subset_1(k5_waybel_0(sK3,sK4),k1_zfmisc_1(u1_struct_0(sK3)))
    | ~ m1_subset_1(k1_yellow_0(sK3,k5_waybel_0(sK3,sK4)),u1_struct_0(sK3)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_493,c_37,c_36,c_35,c_34,c_33,c_32])).

cnf(c_496,plain,
    ( v4_waybel_7(k1_yellow_0(sK3,k5_waybel_0(sK3,sK4)),sK3)
    | ~ v1_waybel_0(k5_waybel_0(sK3,sK4),sK3)
    | ~ v12_waybel_0(k5_waybel_0(sK3,sK4),sK3)
    | ~ m1_subset_1(k5_waybel_0(sK3,sK4),k1_zfmisc_1(u1_struct_0(sK3)))
    | ~ m1_subset_1(k1_yellow_0(sK3,k5_waybel_0(sK3,sK4)),u1_struct_0(sK3))
    | v1_xboole_0(k5_waybel_0(sK3,sK4)) ),
    inference(renaming,[status(thm)],[c_495])).

cnf(c_535,plain,
    ( v4_waybel_7(k1_yellow_0(sK3,k5_waybel_0(sK3,sK4)),sK3)
    | ~ v1_waybel_0(k5_waybel_0(sK3,sK4),sK3)
    | ~ m1_subset_1(X0,u1_struct_0(X1))
    | ~ m1_subset_1(k5_waybel_0(sK3,sK4),k1_zfmisc_1(u1_struct_0(sK3)))
    | ~ m1_subset_1(k1_yellow_0(sK3,k5_waybel_0(sK3,sK4)),u1_struct_0(sK3))
    | v1_xboole_0(k5_waybel_0(sK3,sK4))
    | ~ v4_orders_2(X1)
    | v2_struct_0(X1)
    | ~ l1_orders_2(X1)
    | k5_waybel_0(X1,X0) != k5_waybel_0(sK3,sK4)
    | sK3 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_16,c_496])).

cnf(c_536,plain,
    ( v4_waybel_7(k1_yellow_0(sK3,k5_waybel_0(sK3,sK4)),sK3)
    | ~ v1_waybel_0(k5_waybel_0(sK3,sK4),sK3)
    | ~ m1_subset_1(X0,u1_struct_0(sK3))
    | ~ m1_subset_1(k5_waybel_0(sK3,sK4),k1_zfmisc_1(u1_struct_0(sK3)))
    | ~ m1_subset_1(k1_yellow_0(sK3,k5_waybel_0(sK3,sK4)),u1_struct_0(sK3))
    | v1_xboole_0(k5_waybel_0(sK3,sK4))
    | ~ v4_orders_2(sK3)
    | v2_struct_0(sK3)
    | ~ l1_orders_2(sK3)
    | k5_waybel_0(sK3,X0) != k5_waybel_0(sK3,sK4) ),
    inference(unflattening,[status(thm)],[c_535])).

cnf(c_129,plain,
    ( ~ v1_lattice3(sK3)
    | ~ v2_struct_0(sK3)
    | ~ l1_orders_2(sK3) ),
    inference(instantiation,[status(thm)],[c_1])).

cnf(c_540,plain,
    ( v1_xboole_0(k5_waybel_0(sK3,sK4))
    | ~ m1_subset_1(k1_yellow_0(sK3,k5_waybel_0(sK3,sK4)),u1_struct_0(sK3))
    | ~ m1_subset_1(k5_waybel_0(sK3,sK4),k1_zfmisc_1(u1_struct_0(sK3)))
    | ~ m1_subset_1(X0,u1_struct_0(sK3))
    | ~ v1_waybel_0(k5_waybel_0(sK3,sK4),sK3)
    | v4_waybel_7(k1_yellow_0(sK3,k5_waybel_0(sK3,sK4)),sK3)
    | k5_waybel_0(sK3,X0) != k5_waybel_0(sK3,sK4) ),
    inference(global_propositional_subsumption,[status(thm)],[c_536,c_36,c_34,c_32,c_129])).

cnf(c_541,plain,
    ( v4_waybel_7(k1_yellow_0(sK3,k5_waybel_0(sK3,sK4)),sK3)
    | ~ v1_waybel_0(k5_waybel_0(sK3,sK4),sK3)
    | ~ m1_subset_1(X0,u1_struct_0(sK3))
    | ~ m1_subset_1(k5_waybel_0(sK3,sK4),k1_zfmisc_1(u1_struct_0(sK3)))
    | ~ m1_subset_1(k1_yellow_0(sK3,k5_waybel_0(sK3,sK4)),u1_struct_0(sK3))
    | v1_xboole_0(k5_waybel_0(sK3,sK4))
    | k5_waybel_0(sK3,X0) != k5_waybel_0(sK3,sK4) ),
    inference(renaming,[status(thm)],[c_540])).

cnf(c_1936,plain,
    ( v4_waybel_7(k1_yellow_0(sK3,k5_waybel_0(sK3,sK4)),sK3)
    | ~ v1_waybel_0(k5_waybel_0(sK3,sK4),sK3)
    | ~ m1_subset_1(X0,u1_struct_0(sK3))
    | ~ m1_subset_1(k5_waybel_0(sK3,sK4),k1_zfmisc_1(u1_struct_0(sK3)))
    | v1_xboole_0(k5_waybel_0(sK3,sK4))
    | k5_waybel_0(sK3,X0) != k5_waybel_0(sK3,sK4) ),
    inference(backward_subsumption_resolution,[status(thm)],[c_1863,c_541])).

cnf(c_3796,plain,
    ( v4_waybel_7(k1_yellow_0(sK3,k5_waybel_0(sK3,sK4)),sK3)
    | ~ v1_waybel_0(k5_waybel_0(sK3,sK4),sK3)
    | ~ m1_subset_1(X0_55,u1_struct_0(sK3))
    | ~ m1_subset_1(k5_waybel_0(sK3,sK4),k1_zfmisc_1(u1_struct_0(sK3)))
    | v1_xboole_0(k5_waybel_0(sK3,sK4))
    | k5_waybel_0(sK3,X0_55) != k5_waybel_0(sK3,sK4) ),
    inference(subtyping,[status(esa)],[c_1936])).

cnf(c_3823,plain,
    ( ~ m1_subset_1(X0_55,u1_struct_0(sK3))
    | k5_waybel_0(sK3,X0_55) != k5_waybel_0(sK3,sK4)
    | ~ sP0_iProver_split ),
    inference(splitting,[splitting(split),new_symbols(definition,[sP0_iProver_split])],[c_3796])).

cnf(c_3912,plain,
    ( ~ m1_subset_1(sK4,u1_struct_0(sK3))
    | ~ sP0_iProver_split
    | k5_waybel_0(sK3,sK4) != k5_waybel_0(sK3,sK4) ),
    inference(instantiation,[status(thm)],[c_3823])).

cnf(c_3824,plain,
    ( v4_waybel_7(k1_yellow_0(sK3,k5_waybel_0(sK3,sK4)),sK3)
    | ~ v1_waybel_0(k5_waybel_0(sK3,sK4),sK3)
    | ~ m1_subset_1(k5_waybel_0(sK3,sK4),k1_zfmisc_1(u1_struct_0(sK3)))
    | v1_xboole_0(k5_waybel_0(sK3,sK4))
    | sP0_iProver_split ),
    inference(splitting,[splitting(split),new_symbols(definition,[])],[c_3796])).

cnf(c_15,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(X1))
    | m1_subset_1(k5_waybel_0(X1,X0),k1_zfmisc_1(u1_struct_0(X1)))
    | v2_struct_0(X1)
    | ~ l1_orders_2(X1) ),
    inference(cnf_transformation,[],[f67])).

cnf(c_847,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(X1))
    | m1_subset_1(k5_waybel_0(X1,X0),k1_zfmisc_1(u1_struct_0(X1)))
    | ~ v1_lattice3(X2)
    | ~ l1_orders_2(X2)
    | ~ l1_orders_2(X1)
    | X1 != X2 ),
    inference(resolution_lifted,[status(thm)],[c_1,c_15])).

cnf(c_848,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(X1))
    | m1_subset_1(k5_waybel_0(X1,X0),k1_zfmisc_1(u1_struct_0(X1)))
    | ~ v1_lattice3(X1)
    | ~ l1_orders_2(X1) ),
    inference(unflattening,[status(thm)],[c_847])).

cnf(c_1253,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(X1))
    | m1_subset_1(k5_waybel_0(X1,X0),k1_zfmisc_1(u1_struct_0(X1)))
    | ~ l1_orders_2(X1)
    | sK3 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_848,c_34])).

cnf(c_1254,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(sK3))
    | m1_subset_1(k5_waybel_0(sK3,X0),k1_zfmisc_1(u1_struct_0(sK3)))
    | ~ l1_orders_2(sK3) ),
    inference(unflattening,[status(thm)],[c_1253])).

cnf(c_1258,plain,
    ( m1_subset_1(k5_waybel_0(sK3,X0),k1_zfmisc_1(u1_struct_0(sK3)))
    | ~ m1_subset_1(X0,u1_struct_0(sK3)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_1254,c_32])).

cnf(c_1259,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(sK3))
    | m1_subset_1(k5_waybel_0(sK3,X0),k1_zfmisc_1(u1_struct_0(sK3))) ),
    inference(renaming,[status(thm)],[c_1258])).

cnf(c_3810,plain,
    ( ~ m1_subset_1(X0_55,u1_struct_0(sK3))
    | m1_subset_1(k5_waybel_0(sK3,X0_55),k1_zfmisc_1(u1_struct_0(sK3))) ),
    inference(subtyping,[status(esa)],[c_1259])).

cnf(c_3871,plain,
    ( m1_subset_1(k5_waybel_0(sK3,sK4),k1_zfmisc_1(u1_struct_0(sK3)))
    | ~ m1_subset_1(sK4,u1_struct_0(sK3)) ),
    inference(instantiation,[status(thm)],[c_3810])).

cnf(c_19,plain,
    ( ~ r1_orders_2(X0,X1,X2)
    | r2_hidden(X1,k5_waybel_0(X0,X2))
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | ~ m1_subset_1(X1,u1_struct_0(X0))
    | v2_struct_0(X0)
    | ~ l1_orders_2(X0) ),
    inference(cnf_transformation,[],[f72])).

cnf(c_763,plain,
    ( ~ r1_orders_2(X0,X1,X2)
    | r2_hidden(X1,k5_waybel_0(X0,X2))
    | ~ m1_subset_1(X1,u1_struct_0(X0))
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | ~ v1_lattice3(X0)
    | ~ l1_orders_2(X0) ),
    inference(resolution,[status(thm)],[c_19,c_1])).

cnf(c_1209,plain,
    ( ~ r1_orders_2(X0,X1,X2)
    | r2_hidden(X1,k5_waybel_0(X0,X2))
    | ~ m1_subset_1(X1,u1_struct_0(X0))
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | ~ l1_orders_2(X0)
    | sK3 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_763,c_34])).

cnf(c_1210,plain,
    ( ~ r1_orders_2(sK3,X0,X1)
    | r2_hidden(X0,k5_waybel_0(sK3,X1))
    | ~ m1_subset_1(X0,u1_struct_0(sK3))
    | ~ m1_subset_1(X1,u1_struct_0(sK3))
    | ~ l1_orders_2(sK3) ),
    inference(unflattening,[status(thm)],[c_1209])).

cnf(c_1214,plain,
    ( ~ m1_subset_1(X1,u1_struct_0(sK3))
    | ~ m1_subset_1(X0,u1_struct_0(sK3))
    | r2_hidden(X0,k5_waybel_0(sK3,X1))
    | ~ r1_orders_2(sK3,X0,X1) ),
    inference(global_propositional_subsumption,[status(thm)],[c_1210,c_32])).

cnf(c_1215,plain,
    ( ~ r1_orders_2(sK3,X0,X1)
    | r2_hidden(X0,k5_waybel_0(sK3,X1))
    | ~ m1_subset_1(X1,u1_struct_0(sK3))
    | ~ m1_subset_1(X0,u1_struct_0(sK3)) ),
    inference(renaming,[status(thm)],[c_1214])).

cnf(c_3812,plain,
    ( ~ r1_orders_2(sK3,X0_55,X1_55)
    | r2_hidden(X0_55,k5_waybel_0(sK3,X1_55))
    | ~ m1_subset_1(X0_55,u1_struct_0(sK3))
    | ~ m1_subset_1(X1_55,u1_struct_0(sK3)) ),
    inference(subtyping,[status(esa)],[c_1215])).

cnf(c_3866,plain,
    ( r1_orders_2(sK3,X0_55,X1_55) != iProver_top
    | r2_hidden(X0_55,k5_waybel_0(sK3,X1_55)) = iProver_top
    | m1_subset_1(X0_55,u1_struct_0(sK3)) != iProver_top
    | m1_subset_1(X1_55,u1_struct_0(sK3)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3812])).

cnf(c_3868,plain,
    ( r1_orders_2(sK3,sK4,sK4) != iProver_top
    | r2_hidden(sK4,k5_waybel_0(sK3,sK4)) = iProver_top
    | m1_subset_1(sK4,u1_struct_0(sK3)) != iProver_top ),
    inference(instantiation,[status(thm)],[c_3866])).

cnf(c_18,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(X1))
    | ~ v1_xboole_0(k5_waybel_0(X1,X0))
    | v2_struct_0(X1)
    | ~ v3_orders_2(X1)
    | ~ l1_orders_2(X1) ),
    inference(cnf_transformation,[],[f69])).

cnf(c_826,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(X1))
    | ~ v1_xboole_0(k5_waybel_0(X1,X0))
    | ~ v1_lattice3(X2)
    | ~ v3_orders_2(X1)
    | ~ l1_orders_2(X2)
    | ~ l1_orders_2(X1)
    | X1 != X2 ),
    inference(resolution_lifted,[status(thm)],[c_1,c_18])).

cnf(c_827,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(X1))
    | ~ v1_xboole_0(k5_waybel_0(X1,X0))
    | ~ v1_lattice3(X1)
    | ~ v3_orders_2(X1)
    | ~ l1_orders_2(X1) ),
    inference(unflattening,[status(thm)],[c_826])).

cnf(c_1182,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(X1))
    | ~ v1_xboole_0(k5_waybel_0(X1,X0))
    | ~ v1_lattice3(X1)
    | ~ l1_orders_2(X1)
    | sK3 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_827,c_37])).

cnf(c_1183,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(sK3))
    | ~ v1_xboole_0(k5_waybel_0(sK3,X0))
    | ~ v1_lattice3(sK3)
    | ~ l1_orders_2(sK3) ),
    inference(unflattening,[status(thm)],[c_1182])).

cnf(c_1187,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(sK3))
    | ~ v1_xboole_0(k5_waybel_0(sK3,X0)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_1183,c_34,c_32])).

cnf(c_3813,plain,
    ( ~ m1_subset_1(X0_55,u1_struct_0(sK3))
    | ~ v1_xboole_0(k5_waybel_0(sK3,X0_55)) ),
    inference(subtyping,[status(esa)],[c_1187])).

cnf(c_3864,plain,
    ( ~ m1_subset_1(sK4,u1_struct_0(sK3))
    | ~ v1_xboole_0(k5_waybel_0(sK3,sK4)) ),
    inference(instantiation,[status(thm)],[c_3813])).

cnf(c_17,plain,
    ( v1_waybel_0(k5_waybel_0(X0,X1),X0)
    | ~ m1_subset_1(X1,u1_struct_0(X0))
    | v2_struct_0(X0)
    | ~ v3_orders_2(X0)
    | ~ l1_orders_2(X0) ),
    inference(cnf_transformation,[],[f70])).

cnf(c_786,plain,
    ( v1_waybel_0(k5_waybel_0(X0,X1),X0)
    | ~ m1_subset_1(X1,u1_struct_0(X0))
    | ~ v1_lattice3(X0)
    | ~ v3_orders_2(X0)
    | ~ l1_orders_2(X0) ),
    inference(resolution,[status(thm)],[c_17,c_1])).

cnf(c_1164,plain,
    ( v1_waybel_0(k5_waybel_0(X0,X1),X0)
    | ~ m1_subset_1(X1,u1_struct_0(X0))
    | ~ v1_lattice3(X0)
    | ~ l1_orders_2(X0)
    | sK3 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_786,c_37])).

cnf(c_1165,plain,
    ( v1_waybel_0(k5_waybel_0(sK3,X0),sK3)
    | ~ m1_subset_1(X0,u1_struct_0(sK3))
    | ~ v1_lattice3(sK3)
    | ~ l1_orders_2(sK3) ),
    inference(unflattening,[status(thm)],[c_1164])).

cnf(c_1169,plain,
    ( v1_waybel_0(k5_waybel_0(sK3,X0),sK3)
    | ~ m1_subset_1(X0,u1_struct_0(sK3)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_1165,c_34,c_32])).

cnf(c_3814,plain,
    ( v1_waybel_0(k5_waybel_0(sK3,X0_55),sK3)
    | ~ m1_subset_1(X0_55,u1_struct_0(sK3)) ),
    inference(subtyping,[status(esa)],[c_1169])).

cnf(c_3861,plain,
    ( v1_waybel_0(k5_waybel_0(sK3,sK4),sK3)
    | ~ m1_subset_1(sK4,u1_struct_0(sK3)) ),
    inference(instantiation,[status(thm)],[c_3814])).

cnf(c_0,plain,
    ( r1_orders_2(X0,X1,X1)
    | ~ m1_subset_1(X1,u1_struct_0(X0))
    | v2_struct_0(X0)
    | ~ v3_orders_2(X0)
    | ~ l1_orders_2(X0) ),
    inference(cnf_transformation,[],[f52])).

cnf(c_806,plain,
    ( r1_orders_2(X0,X1,X1)
    | ~ m1_subset_1(X1,u1_struct_0(X0))
    | ~ v1_lattice3(X0)
    | ~ v3_orders_2(X0)
    | ~ l1_orders_2(X0) ),
    inference(resolution,[status(thm)],[c_0,c_1])).

cnf(c_1146,plain,
    ( r1_orders_2(X0,X1,X1)
    | ~ m1_subset_1(X1,u1_struct_0(X0))
    | ~ v1_lattice3(X0)
    | ~ l1_orders_2(X0)
    | sK3 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_806,c_37])).

cnf(c_1147,plain,
    ( r1_orders_2(sK3,X0,X0)
    | ~ m1_subset_1(X0,u1_struct_0(sK3))
    | ~ v1_lattice3(sK3)
    | ~ l1_orders_2(sK3) ),
    inference(unflattening,[status(thm)],[c_1146])).

cnf(c_1151,plain,
    ( r1_orders_2(sK3,X0,X0)
    | ~ m1_subset_1(X0,u1_struct_0(sK3)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_1147,c_34,c_32])).

cnf(c_3815,plain,
    ( r1_orders_2(sK3,X0_55,X0_55)
    | ~ m1_subset_1(X0_55,u1_struct_0(sK3)) ),
    inference(subtyping,[status(esa)],[c_1151])).

cnf(c_3857,plain,
    ( r1_orders_2(sK3,X0_55,X0_55) = iProver_top
    | m1_subset_1(X0_55,u1_struct_0(sK3)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3815])).

cnf(c_3859,plain,
    ( r1_orders_2(sK3,sK4,sK4) = iProver_top
    | m1_subset_1(sK4,u1_struct_0(sK3)) != iProver_top ),
    inference(instantiation,[status(thm)],[c_3857])).

cnf(c_3828,plain,
    ( X0_55 = X0_55 ),
    theory(equality)).

cnf(c_3849,plain,
    ( sK4 = sK4 ),
    inference(instantiation,[status(thm)],[c_3828])).

cnf(c_3835,plain,
    ( X0_55 != X1_55
    | k5_waybel_0(X0_56,X0_55) = k5_waybel_0(X0_56,X1_55) ),
    theory(equality)).

cnf(c_3844,plain,
    ( k5_waybel_0(sK3,sK4) = k5_waybel_0(sK3,sK4)
    | sK4 != sK4 ),
    inference(instantiation,[status(thm)],[c_3835])).

cnf(c_29,negated_conjecture,
    ( ~ v4_waybel_7(sK4,sK3) ),
    inference(cnf_transformation,[],[f89])).

cnf(c_44,plain,
    ( m1_subset_1(sK4,u1_struct_0(sK3)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_31])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_7247,c_5467,c_5269,c_5265,c_5067,c_5063,c_5059,c_4768,c_4661,c_3912,c_3824,c_3871,c_3868,c_3864,c_3861,c_3859,c_3849,c_3844,c_29,c_44,c_31])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.12/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : iproveropt_run.sh %d %s
% 0.14/0.34  % Computer   : n018.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % WCLimit    : 600
% 0.14/0.34  % DateTime   : Tue Dec  1 17:06:42 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.34  % Running in FOF mode
% 2.43/0.98  % SZS status Started for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.43/0.98  
% 2.43/0.98  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 2.43/0.98  
% 2.43/0.98  ------  iProver source info
% 2.43/0.98  
% 2.43/0.98  git: date: 2020-06-30 10:37:57 +0100
% 2.43/0.98  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 2.43/0.98  git: non_committed_changes: false
% 2.43/0.98  git: last_make_outside_of_git: false
% 2.43/0.98  
% 2.43/0.98  ------ 
% 2.43/0.98  
% 2.43/0.98  ------ Input Options
% 2.43/0.98  
% 2.43/0.98  --out_options                           all
% 2.43/0.98  --tptp_safe_out                         true
% 2.43/0.98  --problem_path                          ""
% 2.43/0.98  --include_path                          ""
% 2.43/0.98  --clausifier                            res/vclausify_rel
% 2.43/0.98  --clausifier_options                    --mode clausify
% 2.43/0.98  --stdin                                 false
% 2.43/0.98  --stats_out                             all
% 2.43/0.98  
% 2.43/0.98  ------ General Options
% 2.43/0.98  
% 2.43/0.98  --fof                                   false
% 2.43/0.98  --time_out_real                         305.
% 2.43/0.98  --time_out_virtual                      -1.
% 2.43/0.98  --symbol_type_check                     false
% 2.43/0.98  --clausify_out                          false
% 2.43/0.98  --sig_cnt_out                           false
% 2.43/0.98  --trig_cnt_out                          false
% 2.43/0.98  --trig_cnt_out_tolerance                1.
% 2.43/0.98  --trig_cnt_out_sk_spl                   false
% 2.43/0.98  --abstr_cl_out                          false
% 2.43/0.98  
% 2.43/0.98  ------ Global Options
% 2.43/0.98  
% 2.43/0.98  --schedule                              default
% 2.43/0.98  --add_important_lit                     false
% 2.43/0.98  --prop_solver_per_cl                    1000
% 2.43/0.98  --min_unsat_core                        false
% 2.43/0.98  --soft_assumptions                      false
% 2.43/0.98  --soft_lemma_size                       3
% 2.43/0.98  --prop_impl_unit_size                   0
% 2.43/0.98  --prop_impl_unit                        []
% 2.43/0.98  --share_sel_clauses                     true
% 2.43/0.98  --reset_solvers                         false
% 2.43/0.98  --bc_imp_inh                            [conj_cone]
% 2.43/0.98  --conj_cone_tolerance                   3.
% 2.43/0.98  --extra_neg_conj                        none
% 2.43/0.98  --large_theory_mode                     true
% 2.43/0.98  --prolific_symb_bound                   200
% 2.43/0.98  --lt_threshold                          2000
% 2.43/0.98  --clause_weak_htbl                      true
% 2.43/0.98  --gc_record_bc_elim                     false
% 2.43/0.98  
% 2.43/0.98  ------ Preprocessing Options
% 2.43/0.98  
% 2.43/0.98  --preprocessing_flag                    true
% 2.43/0.98  --time_out_prep_mult                    0.1
% 2.43/0.98  --splitting_mode                        input
% 2.43/0.98  --splitting_grd                         true
% 2.43/0.98  --splitting_cvd                         false
% 2.43/0.98  --splitting_cvd_svl                     false
% 2.43/0.98  --splitting_nvd                         32
% 2.43/0.98  --sub_typing                            true
% 2.43/0.98  --prep_gs_sim                           true
% 2.43/0.98  --prep_unflatten                        true
% 2.43/0.98  --prep_res_sim                          true
% 2.43/0.98  --prep_upred                            true
% 2.43/0.98  --prep_sem_filter                       exhaustive
% 2.43/0.98  --prep_sem_filter_out                   false
% 2.43/0.98  --pred_elim                             true
% 2.43/0.98  --res_sim_input                         true
% 2.43/0.98  --eq_ax_congr_red                       true
% 2.43/0.98  --pure_diseq_elim                       true
% 2.43/0.98  --brand_transform                       false
% 2.43/0.98  --non_eq_to_eq                          false
% 2.43/0.98  --prep_def_merge                        true
% 2.43/0.98  --prep_def_merge_prop_impl              false
% 2.43/0.98  --prep_def_merge_mbd                    true
% 2.43/0.98  --prep_def_merge_tr_red                 false
% 2.43/0.98  --prep_def_merge_tr_cl                  false
% 2.43/0.98  --smt_preprocessing                     true
% 2.43/0.98  --smt_ac_axioms                         fast
% 2.43/0.98  --preprocessed_out                      false
% 2.43/0.98  --preprocessed_stats                    false
% 2.43/0.98  
% 2.43/0.98  ------ Abstraction refinement Options
% 2.43/0.98  
% 2.43/0.98  --abstr_ref                             []
% 2.43/0.98  --abstr_ref_prep                        false
% 2.43/0.98  --abstr_ref_until_sat                   false
% 2.43/0.98  --abstr_ref_sig_restrict                funpre
% 2.43/0.98  --abstr_ref_af_restrict_to_split_sk     false
% 2.43/0.98  --abstr_ref_under                       []
% 2.43/0.98  
% 2.43/0.98  ------ SAT Options
% 2.43/0.98  
% 2.43/0.98  --sat_mode                              false
% 2.43/0.98  --sat_fm_restart_options                ""
% 2.43/0.98  --sat_gr_def                            false
% 2.43/0.98  --sat_epr_types                         true
% 2.43/0.98  --sat_non_cyclic_types                  false
% 2.43/0.98  --sat_finite_models                     false
% 2.43/0.98  --sat_fm_lemmas                         false
% 2.43/0.98  --sat_fm_prep                           false
% 2.43/0.98  --sat_fm_uc_incr                        true
% 2.43/0.98  --sat_out_model                         small
% 2.43/0.98  --sat_out_clauses                       false
% 2.43/0.98  
% 2.43/0.98  ------ QBF Options
% 2.43/0.98  
% 2.43/0.98  --qbf_mode                              false
% 2.43/0.98  --qbf_elim_univ                         false
% 2.43/0.98  --qbf_dom_inst                          none
% 2.43/0.98  --qbf_dom_pre_inst                      false
% 2.43/0.98  --qbf_sk_in                             false
% 2.43/0.98  --qbf_pred_elim                         true
% 2.43/0.98  --qbf_split                             512
% 2.43/0.98  
% 2.43/0.98  ------ BMC1 Options
% 2.43/0.98  
% 2.43/0.98  --bmc1_incremental                      false
% 2.43/0.98  --bmc1_axioms                           reachable_all
% 2.43/0.98  --bmc1_min_bound                        0
% 2.43/0.98  --bmc1_max_bound                        -1
% 2.43/0.98  --bmc1_max_bound_default                -1
% 2.43/0.98  --bmc1_symbol_reachability              true
% 2.43/0.98  --bmc1_property_lemmas                  false
% 2.43/0.98  --bmc1_k_induction                      false
% 2.43/0.98  --bmc1_non_equiv_states                 false
% 2.43/0.98  --bmc1_deadlock                         false
% 2.43/0.98  --bmc1_ucm                              false
% 2.43/0.98  --bmc1_add_unsat_core                   none
% 2.43/0.98  --bmc1_unsat_core_children              false
% 2.43/0.98  --bmc1_unsat_core_extrapolate_axioms    false
% 2.43/0.98  --bmc1_out_stat                         full
% 2.43/0.98  --bmc1_ground_init                      false
% 2.43/0.98  --bmc1_pre_inst_next_state              false
% 2.43/0.98  --bmc1_pre_inst_state                   false
% 2.43/0.98  --bmc1_pre_inst_reach_state             false
% 2.43/0.98  --bmc1_out_unsat_core                   false
% 2.43/0.98  --bmc1_aig_witness_out                  false
% 2.43/0.98  --bmc1_verbose                          false
% 2.43/0.98  --bmc1_dump_clauses_tptp                false
% 2.43/0.98  --bmc1_dump_unsat_core_tptp             false
% 2.43/0.98  --bmc1_dump_file                        -
% 2.43/0.98  --bmc1_ucm_expand_uc_limit              128
% 2.43/0.98  --bmc1_ucm_n_expand_iterations          6
% 2.43/0.98  --bmc1_ucm_extend_mode                  1
% 2.43/0.98  --bmc1_ucm_init_mode                    2
% 2.43/0.98  --bmc1_ucm_cone_mode                    none
% 2.43/0.98  --bmc1_ucm_reduced_relation_type        0
% 2.43/0.98  --bmc1_ucm_relax_model                  4
% 2.43/0.98  --bmc1_ucm_full_tr_after_sat            true
% 2.43/0.98  --bmc1_ucm_expand_neg_assumptions       false
% 2.43/0.98  --bmc1_ucm_layered_model                none
% 2.43/0.98  --bmc1_ucm_max_lemma_size               10
% 2.43/0.98  
% 2.43/0.98  ------ AIG Options
% 2.43/0.98  
% 2.43/0.98  --aig_mode                              false
% 2.43/0.98  
% 2.43/0.98  ------ Instantiation Options
% 2.43/0.98  
% 2.43/0.98  --instantiation_flag                    true
% 2.43/0.98  --inst_sos_flag                         false
% 2.43/0.98  --inst_sos_phase                        true
% 2.43/0.98  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 2.43/0.98  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 2.43/0.98  --inst_lit_sel_side                     num_symb
% 2.43/0.98  --inst_solver_per_active                1400
% 2.43/0.98  --inst_solver_calls_frac                1.
% 2.43/0.98  --inst_passive_queue_type               priority_queues
% 2.43/0.98  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 2.43/0.98  --inst_passive_queues_freq              [25;2]
% 2.43/0.98  --inst_dismatching                      true
% 2.43/0.98  --inst_eager_unprocessed_to_passive     true
% 2.43/0.98  --inst_prop_sim_given                   true
% 2.43/0.98  --inst_prop_sim_new                     false
% 2.43/0.98  --inst_subs_new                         false
% 2.43/0.98  --inst_eq_res_simp                      false
% 2.43/0.98  --inst_subs_given                       false
% 2.43/0.98  --inst_orphan_elimination               true
% 2.43/0.98  --inst_learning_loop_flag               true
% 2.43/0.98  --inst_learning_start                   3000
% 2.43/0.98  --inst_learning_factor                  2
% 2.43/0.98  --inst_start_prop_sim_after_learn       3
% 2.43/0.98  --inst_sel_renew                        solver
% 2.43/0.98  --inst_lit_activity_flag                true
% 2.43/0.98  --inst_restr_to_given                   false
% 2.43/0.98  --inst_activity_threshold               500
% 2.43/0.98  --inst_out_proof                        true
% 2.43/0.98  
% 2.43/0.98  ------ Resolution Options
% 2.43/0.98  
% 2.43/0.98  --resolution_flag                       true
% 2.43/0.98  --res_lit_sel                           adaptive
% 2.43/0.98  --res_lit_sel_side                      none
% 2.43/0.98  --res_ordering                          kbo
% 2.43/0.98  --res_to_prop_solver                    active
% 2.43/0.98  --res_prop_simpl_new                    false
% 2.43/0.98  --res_prop_simpl_given                  true
% 2.43/0.98  --res_passive_queue_type                priority_queues
% 2.43/0.98  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 2.43/0.98  --res_passive_queues_freq               [15;5]
% 2.43/0.98  --res_forward_subs                      full
% 2.43/0.98  --res_backward_subs                     full
% 2.43/0.98  --res_forward_subs_resolution           true
% 2.43/0.98  --res_backward_subs_resolution          true
% 2.43/0.98  --res_orphan_elimination                true
% 2.43/0.98  --res_time_limit                        2.
% 2.43/0.98  --res_out_proof                         true
% 2.43/0.98  
% 2.43/0.98  ------ Superposition Options
% 2.43/0.98  
% 2.43/0.98  --superposition_flag                    true
% 2.43/0.98  --sup_passive_queue_type                priority_queues
% 2.43/0.98  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 2.43/0.98  --sup_passive_queues_freq               [8;1;4]
% 2.43/0.98  --demod_completeness_check              fast
% 2.43/0.98  --demod_use_ground                      true
% 2.43/0.98  --sup_to_prop_solver                    passive
% 2.43/0.98  --sup_prop_simpl_new                    true
% 2.43/0.98  --sup_prop_simpl_given                  true
% 2.43/0.98  --sup_fun_splitting                     false
% 2.43/0.98  --sup_smt_interval                      50000
% 2.43/0.98  
% 2.43/0.98  ------ Superposition Simplification Setup
% 2.43/0.98  
% 2.43/0.98  --sup_indices_passive                   []
% 2.43/0.98  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.43/0.98  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.43/0.98  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.43/0.98  --sup_full_triv                         [TrivRules;PropSubs]
% 2.43/0.98  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.43/0.98  --sup_full_bw                           [BwDemod]
% 2.43/0.98  --sup_immed_triv                        [TrivRules]
% 2.43/0.98  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 2.43/0.98  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.43/0.98  --sup_immed_bw_main                     []
% 2.43/0.98  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.43/0.98  --sup_input_triv                        [Unflattening;TrivRules]
% 2.43/0.98  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.43/0.98  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.43/0.98  
% 2.43/0.98  ------ Combination Options
% 2.43/0.98  
% 2.43/0.98  --comb_res_mult                         3
% 2.43/0.98  --comb_sup_mult                         2
% 2.43/0.98  --comb_inst_mult                        10
% 2.43/0.98  
% 2.43/0.98  ------ Debug Options
% 2.43/0.98  
% 2.43/0.98  --dbg_backtrace                         false
% 2.43/0.98  --dbg_dump_prop_clauses                 false
% 2.43/0.98  --dbg_dump_prop_clauses_file            -
% 2.43/0.98  --dbg_out_stat                          false
% 2.43/0.98  ------ Parsing...
% 2.43/0.98  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 2.43/0.98  
% 2.43/0.98  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe:1:0s pe:2:0s pe:4:0s pe:8:0s pe_e  sf_s  rm: 10 0s  sf_e  pe_s  pe_e 
% 2.43/0.98  
% 2.43/0.98  ------ Preprocessing... gs_s  sp: 2 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 2.43/0.98  
% 2.43/0.98  ------ Preprocessing... sf_s  rm: 9 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 2.43/0.98  ------ Proving...
% 2.43/0.98  ------ Problem Properties 
% 2.43/0.98  
% 2.43/0.98  
% 2.43/0.98  clauses                                 30
% 2.43/0.98  conjectures                             2
% 2.43/0.99  EPR                                     1
% 2.43/0.99  Horn                                    22
% 2.43/0.99  unary                                   3
% 2.43/0.99  binary                                  5
% 2.43/0.99  lits                                    95
% 2.43/0.99  lits eq                                 6
% 2.43/0.99  fd_pure                                 0
% 2.43/0.99  fd_pseudo                               0
% 2.43/0.99  fd_cond                                 0
% 2.43/0.99  fd_pseudo_cond                          3
% 2.43/0.99  AC symbols                              0
% 2.43/0.99  
% 2.43/0.99  ------ Schedule dynamic 5 is on 
% 2.43/0.99  
% 2.43/0.99  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" Time Limit: 10.
% 2.43/0.99  
% 2.43/0.99  
% 2.43/0.99  ------ 
% 2.43/0.99  Current options:
% 2.43/0.99  ------ 
% 2.43/0.99  
% 2.43/0.99  ------ Input Options
% 2.43/0.99  
% 2.43/0.99  --out_options                           all
% 2.43/0.99  --tptp_safe_out                         true
% 2.43/0.99  --problem_path                          ""
% 2.43/0.99  --include_path                          ""
% 2.43/0.99  --clausifier                            res/vclausify_rel
% 2.43/0.99  --clausifier_options                    --mode clausify
% 2.43/0.99  --stdin                                 false
% 2.43/0.99  --stats_out                             all
% 2.43/0.99  
% 2.43/0.99  ------ General Options
% 2.43/0.99  
% 2.43/0.99  --fof                                   false
% 2.43/0.99  --time_out_real                         305.
% 2.43/0.99  --time_out_virtual                      -1.
% 2.43/0.99  --symbol_type_check                     false
% 2.43/0.99  --clausify_out                          false
% 2.43/0.99  --sig_cnt_out                           false
% 2.43/0.99  --trig_cnt_out                          false
% 2.43/0.99  --trig_cnt_out_tolerance                1.
% 2.43/0.99  --trig_cnt_out_sk_spl                   false
% 2.43/0.99  --abstr_cl_out                          false
% 2.43/0.99  
% 2.43/0.99  ------ Global Options
% 2.43/0.99  
% 2.43/0.99  --schedule                              default
% 2.43/0.99  --add_important_lit                     false
% 2.43/0.99  --prop_solver_per_cl                    1000
% 2.43/0.99  --min_unsat_core                        false
% 2.43/0.99  --soft_assumptions                      false
% 2.43/0.99  --soft_lemma_size                       3
% 2.43/0.99  --prop_impl_unit_size                   0
% 2.43/0.99  --prop_impl_unit                        []
% 2.43/0.99  --share_sel_clauses                     true
% 2.43/0.99  --reset_solvers                         false
% 2.43/0.99  --bc_imp_inh                            [conj_cone]
% 2.43/0.99  --conj_cone_tolerance                   3.
% 2.43/0.99  --extra_neg_conj                        none
% 2.43/0.99  --large_theory_mode                     true
% 2.43/0.99  --prolific_symb_bound                   200
% 2.43/0.99  --lt_threshold                          2000
% 2.43/0.99  --clause_weak_htbl                      true
% 2.43/0.99  --gc_record_bc_elim                     false
% 2.43/0.99  
% 2.43/0.99  ------ Preprocessing Options
% 2.43/0.99  
% 2.43/0.99  --preprocessing_flag                    true
% 2.43/0.99  --time_out_prep_mult                    0.1
% 2.43/0.99  --splitting_mode                        input
% 2.43/0.99  --splitting_grd                         true
% 2.43/0.99  --splitting_cvd                         false
% 2.43/0.99  --splitting_cvd_svl                     false
% 2.43/0.99  --splitting_nvd                         32
% 2.43/0.99  --sub_typing                            true
% 2.43/0.99  --prep_gs_sim                           true
% 2.43/0.99  --prep_unflatten                        true
% 2.43/0.99  --prep_res_sim                          true
% 2.43/0.99  --prep_upred                            true
% 2.43/0.99  --prep_sem_filter                       exhaustive
% 2.43/0.99  --prep_sem_filter_out                   false
% 2.43/0.99  --pred_elim                             true
% 2.43/0.99  --res_sim_input                         true
% 2.43/0.99  --eq_ax_congr_red                       true
% 2.43/0.99  --pure_diseq_elim                       true
% 2.43/0.99  --brand_transform                       false
% 2.43/0.99  --non_eq_to_eq                          false
% 2.43/0.99  --prep_def_merge                        true
% 2.43/0.99  --prep_def_merge_prop_impl              false
% 2.43/0.99  --prep_def_merge_mbd                    true
% 2.43/0.99  --prep_def_merge_tr_red                 false
% 2.43/0.99  --prep_def_merge_tr_cl                  false
% 2.43/0.99  --smt_preprocessing                     true
% 2.43/0.99  --smt_ac_axioms                         fast
% 2.43/0.99  --preprocessed_out                      false
% 2.43/0.99  --preprocessed_stats                    false
% 2.43/0.99  
% 2.43/0.99  ------ Abstraction refinement Options
% 2.43/0.99  
% 2.43/0.99  --abstr_ref                             []
% 2.43/0.99  --abstr_ref_prep                        false
% 2.43/0.99  --abstr_ref_until_sat                   false
% 2.43/0.99  --abstr_ref_sig_restrict                funpre
% 2.43/0.99  --abstr_ref_af_restrict_to_split_sk     false
% 2.43/0.99  --abstr_ref_under                       []
% 2.43/0.99  
% 2.43/0.99  ------ SAT Options
% 2.43/0.99  
% 2.43/0.99  --sat_mode                              false
% 2.43/0.99  --sat_fm_restart_options                ""
% 2.43/0.99  --sat_gr_def                            false
% 2.43/0.99  --sat_epr_types                         true
% 2.43/0.99  --sat_non_cyclic_types                  false
% 2.43/0.99  --sat_finite_models                     false
% 2.43/0.99  --sat_fm_lemmas                         false
% 2.43/0.99  --sat_fm_prep                           false
% 2.43/0.99  --sat_fm_uc_incr                        true
% 2.43/0.99  --sat_out_model                         small
% 2.43/0.99  --sat_out_clauses                       false
% 2.43/0.99  
% 2.43/0.99  ------ QBF Options
% 2.43/0.99  
% 2.43/0.99  --qbf_mode                              false
% 2.43/0.99  --qbf_elim_univ                         false
% 2.43/0.99  --qbf_dom_inst                          none
% 2.43/0.99  --qbf_dom_pre_inst                      false
% 2.43/0.99  --qbf_sk_in                             false
% 2.43/0.99  --qbf_pred_elim                         true
% 2.43/0.99  --qbf_split                             512
% 2.43/0.99  
% 2.43/0.99  ------ BMC1 Options
% 2.43/0.99  
% 2.43/0.99  --bmc1_incremental                      false
% 2.43/0.99  --bmc1_axioms                           reachable_all
% 2.43/0.99  --bmc1_min_bound                        0
% 2.43/0.99  --bmc1_max_bound                        -1
% 2.43/0.99  --bmc1_max_bound_default                -1
% 2.43/0.99  --bmc1_symbol_reachability              true
% 2.43/0.99  --bmc1_property_lemmas                  false
% 2.43/0.99  --bmc1_k_induction                      false
% 2.43/0.99  --bmc1_non_equiv_states                 false
% 2.43/0.99  --bmc1_deadlock                         false
% 2.43/0.99  --bmc1_ucm                              false
% 2.43/0.99  --bmc1_add_unsat_core                   none
% 2.43/0.99  --bmc1_unsat_core_children              false
% 2.43/0.99  --bmc1_unsat_core_extrapolate_axioms    false
% 2.43/0.99  --bmc1_out_stat                         full
% 2.43/0.99  --bmc1_ground_init                      false
% 2.43/0.99  --bmc1_pre_inst_next_state              false
% 2.43/0.99  --bmc1_pre_inst_state                   false
% 2.43/0.99  --bmc1_pre_inst_reach_state             false
% 2.43/0.99  --bmc1_out_unsat_core                   false
% 2.43/0.99  --bmc1_aig_witness_out                  false
% 2.43/0.99  --bmc1_verbose                          false
% 2.43/0.99  --bmc1_dump_clauses_tptp                false
% 2.43/0.99  --bmc1_dump_unsat_core_tptp             false
% 2.43/0.99  --bmc1_dump_file                        -
% 2.43/0.99  --bmc1_ucm_expand_uc_limit              128
% 2.43/0.99  --bmc1_ucm_n_expand_iterations          6
% 2.43/0.99  --bmc1_ucm_extend_mode                  1
% 2.43/0.99  --bmc1_ucm_init_mode                    2
% 2.43/0.99  --bmc1_ucm_cone_mode                    none
% 2.43/0.99  --bmc1_ucm_reduced_relation_type        0
% 2.43/0.99  --bmc1_ucm_relax_model                  4
% 2.43/0.99  --bmc1_ucm_full_tr_after_sat            true
% 2.43/0.99  --bmc1_ucm_expand_neg_assumptions       false
% 2.43/0.99  --bmc1_ucm_layered_model                none
% 2.43/0.99  --bmc1_ucm_max_lemma_size               10
% 2.43/0.99  
% 2.43/0.99  ------ AIG Options
% 2.43/0.99  
% 2.43/0.99  --aig_mode                              false
% 2.43/0.99  
% 2.43/0.99  ------ Instantiation Options
% 2.43/0.99  
% 2.43/0.99  --instantiation_flag                    true
% 2.43/0.99  --inst_sos_flag                         false
% 2.43/0.99  --inst_sos_phase                        true
% 2.43/0.99  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 2.43/0.99  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 2.43/0.99  --inst_lit_sel_side                     none
% 2.43/0.99  --inst_solver_per_active                1400
% 2.43/0.99  --inst_solver_calls_frac                1.
% 2.43/0.99  --inst_passive_queue_type               priority_queues
% 2.43/0.99  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 2.43/0.99  --inst_passive_queues_freq              [25;2]
% 2.43/0.99  --inst_dismatching                      true
% 2.43/0.99  --inst_eager_unprocessed_to_passive     true
% 2.43/0.99  --inst_prop_sim_given                   true
% 2.43/0.99  --inst_prop_sim_new                     false
% 2.43/0.99  --inst_subs_new                         false
% 2.43/0.99  --inst_eq_res_simp                      false
% 2.43/0.99  --inst_subs_given                       false
% 2.43/0.99  --inst_orphan_elimination               true
% 2.43/0.99  --inst_learning_loop_flag               true
% 2.43/0.99  --inst_learning_start                   3000
% 2.43/0.99  --inst_learning_factor                  2
% 2.43/0.99  --inst_start_prop_sim_after_learn       3
% 2.43/0.99  --inst_sel_renew                        solver
% 2.43/0.99  --inst_lit_activity_flag                true
% 2.43/0.99  --inst_restr_to_given                   false
% 2.43/0.99  --inst_activity_threshold               500
% 2.43/0.99  --inst_out_proof                        true
% 2.43/0.99  
% 2.43/0.99  ------ Resolution Options
% 2.43/0.99  
% 2.43/0.99  --resolution_flag                       false
% 2.43/0.99  --res_lit_sel                           adaptive
% 2.43/0.99  --res_lit_sel_side                      none
% 2.43/0.99  --res_ordering                          kbo
% 2.43/0.99  --res_to_prop_solver                    active
% 2.43/0.99  --res_prop_simpl_new                    false
% 2.43/0.99  --res_prop_simpl_given                  true
% 2.43/0.99  --res_passive_queue_type                priority_queues
% 2.43/0.99  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 2.43/0.99  --res_passive_queues_freq               [15;5]
% 2.43/0.99  --res_forward_subs                      full
% 2.43/0.99  --res_backward_subs                     full
% 2.43/0.99  --res_forward_subs_resolution           true
% 2.43/0.99  --res_backward_subs_resolution          true
% 2.43/0.99  --res_orphan_elimination                true
% 2.43/0.99  --res_time_limit                        2.
% 2.43/0.99  --res_out_proof                         true
% 2.43/0.99  
% 2.43/0.99  ------ Superposition Options
% 2.43/0.99  
% 2.43/0.99  --superposition_flag                    true
% 2.43/0.99  --sup_passive_queue_type                priority_queues
% 2.43/0.99  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 2.43/0.99  --sup_passive_queues_freq               [8;1;4]
% 2.43/0.99  --demod_completeness_check              fast
% 2.43/0.99  --demod_use_ground                      true
% 2.43/0.99  --sup_to_prop_solver                    passive
% 2.43/0.99  --sup_prop_simpl_new                    true
% 2.43/0.99  --sup_prop_simpl_given                  true
% 2.43/0.99  --sup_fun_splitting                     false
% 2.43/0.99  --sup_smt_interval                      50000
% 2.43/0.99  
% 2.43/0.99  ------ Superposition Simplification Setup
% 2.43/0.99  
% 2.43/0.99  --sup_indices_passive                   []
% 2.43/0.99  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.43/0.99  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.43/0.99  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.43/0.99  --sup_full_triv                         [TrivRules;PropSubs]
% 2.43/0.99  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.43/0.99  --sup_full_bw                           [BwDemod]
% 2.43/0.99  --sup_immed_triv                        [TrivRules]
% 2.43/0.99  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 2.43/0.99  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.43/0.99  --sup_immed_bw_main                     []
% 2.43/0.99  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.43/0.99  --sup_input_triv                        [Unflattening;TrivRules]
% 2.43/0.99  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.43/0.99  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.43/0.99  
% 2.43/0.99  ------ Combination Options
% 2.43/0.99  
% 2.43/0.99  --comb_res_mult                         3
% 2.43/0.99  --comb_sup_mult                         2
% 2.43/0.99  --comb_inst_mult                        10
% 2.43/0.99  
% 2.43/0.99  ------ Debug Options
% 2.43/0.99  
% 2.43/0.99  --dbg_backtrace                         false
% 2.43/0.99  --dbg_dump_prop_clauses                 false
% 2.43/0.99  --dbg_dump_prop_clauses_file            -
% 2.43/0.99  --dbg_out_stat                          false
% 2.43/0.99  
% 2.43/0.99  
% 2.43/0.99  
% 2.43/0.99  
% 2.43/0.99  ------ Proving...
% 2.43/0.99  
% 2.43/0.99  
% 2.43/0.99  % SZS status Theorem for theBenchmark.p
% 2.43/0.99  
% 2.43/0.99  % SZS output start CNFRefutation for theBenchmark.p
% 2.43/0.99  
% 2.43/0.99  fof(f3,axiom,(
% 2.43/0.99    ! [X0] : (l1_orders_2(X0) => ! [X1,X2] : (m1_subset_1(X2,u1_struct_0(X0)) => (r2_lattice3(X0,X1,X2) <=> ! [X3] : (m1_subset_1(X3,u1_struct_0(X0)) => (r2_hidden(X3,X1) => r1_orders_2(X0,X3,X2))))))),
% 2.43/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.43/0.99  
% 2.43/0.99  fof(f19,plain,(
% 2.43/0.99    ! [X0] : (! [X1,X2] : ((r2_lattice3(X0,X1,X2) <=> ! [X3] : ((r1_orders_2(X0,X3,X2) | ~r2_hidden(X3,X1)) | ~m1_subset_1(X3,u1_struct_0(X0)))) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~l1_orders_2(X0))),
% 2.43/0.99    inference(ennf_transformation,[],[f3])).
% 2.43/0.99  
% 2.43/0.99  fof(f20,plain,(
% 2.43/0.99    ! [X0] : (! [X1,X2] : ((r2_lattice3(X0,X1,X2) <=> ! [X3] : (r1_orders_2(X0,X3,X2) | ~r2_hidden(X3,X1) | ~m1_subset_1(X3,u1_struct_0(X0)))) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~l1_orders_2(X0))),
% 2.43/0.99    inference(flattening,[],[f19])).
% 2.43/0.99  
% 2.43/0.99  fof(f38,plain,(
% 2.43/0.99    ! [X0] : (! [X1,X2] : (((r2_lattice3(X0,X1,X2) | ? [X3] : (~r1_orders_2(X0,X3,X2) & r2_hidden(X3,X1) & m1_subset_1(X3,u1_struct_0(X0)))) & (! [X3] : (r1_orders_2(X0,X3,X2) | ~r2_hidden(X3,X1) | ~m1_subset_1(X3,u1_struct_0(X0))) | ~r2_lattice3(X0,X1,X2))) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~l1_orders_2(X0))),
% 2.43/0.99    inference(nnf_transformation,[],[f20])).
% 2.43/0.99  
% 2.43/0.99  fof(f39,plain,(
% 2.43/0.99    ! [X0] : (! [X1,X2] : (((r2_lattice3(X0,X1,X2) | ? [X3] : (~r1_orders_2(X0,X3,X2) & r2_hidden(X3,X1) & m1_subset_1(X3,u1_struct_0(X0)))) & (! [X4] : (r1_orders_2(X0,X4,X2) | ~r2_hidden(X4,X1) | ~m1_subset_1(X4,u1_struct_0(X0))) | ~r2_lattice3(X0,X1,X2))) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~l1_orders_2(X0))),
% 2.43/0.99    inference(rectify,[],[f38])).
% 2.43/0.99  
% 2.43/0.99  fof(f40,plain,(
% 2.43/0.99    ! [X2,X1,X0] : (? [X3] : (~r1_orders_2(X0,X3,X2) & r2_hidden(X3,X1) & m1_subset_1(X3,u1_struct_0(X0))) => (~r1_orders_2(X0,sK0(X0,X1,X2),X2) & r2_hidden(sK0(X0,X1,X2),X1) & m1_subset_1(sK0(X0,X1,X2),u1_struct_0(X0))))),
% 2.43/0.99    introduced(choice_axiom,[])).
% 2.43/0.99  
% 2.43/0.99  fof(f41,plain,(
% 2.43/0.99    ! [X0] : (! [X1,X2] : (((r2_lattice3(X0,X1,X2) | (~r1_orders_2(X0,sK0(X0,X1,X2),X2) & r2_hidden(sK0(X0,X1,X2),X1) & m1_subset_1(sK0(X0,X1,X2),u1_struct_0(X0)))) & (! [X4] : (r1_orders_2(X0,X4,X2) | ~r2_hidden(X4,X1) | ~m1_subset_1(X4,u1_struct_0(X0))) | ~r2_lattice3(X0,X1,X2))) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~l1_orders_2(X0))),
% 2.43/0.99    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f39,f40])).
% 2.43/0.99  
% 2.43/0.99  fof(f54,plain,(
% 2.43/0.99    ( ! [X4,X2,X0,X1] : (r1_orders_2(X0,X4,X2) | ~r2_hidden(X4,X1) | ~m1_subset_1(X4,u1_struct_0(X0)) | ~r2_lattice3(X0,X1,X2) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~l1_orders_2(X0)) )),
% 2.43/0.99    inference(cnf_transformation,[],[f41])).
% 2.43/0.99  
% 2.43/0.99  fof(f12,conjecture,(
% 2.43/0.99    ! [X0] : ((l1_orders_2(X0) & v2_lattice3(X0) & v1_lattice3(X0) & v5_orders_2(X0) & v4_orders_2(X0) & v3_orders_2(X0)) => ! [X1] : (m1_subset_1(X1,u1_struct_0(X0)) => (v5_waybel_6(X1,X0) => v4_waybel_7(X1,X0))))),
% 2.43/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.43/0.99  
% 2.43/0.99  fof(f13,negated_conjecture,(
% 2.43/0.99    ~! [X0] : ((l1_orders_2(X0) & v2_lattice3(X0) & v1_lattice3(X0) & v5_orders_2(X0) & v4_orders_2(X0) & v3_orders_2(X0)) => ! [X1] : (m1_subset_1(X1,u1_struct_0(X0)) => (v5_waybel_6(X1,X0) => v4_waybel_7(X1,X0))))),
% 2.43/0.99    inference(negated_conjecture,[],[f12])).
% 2.43/0.99  
% 2.43/0.99  fof(f36,plain,(
% 2.43/0.99    ? [X0] : (? [X1] : ((~v4_waybel_7(X1,X0) & v5_waybel_6(X1,X0)) & m1_subset_1(X1,u1_struct_0(X0))) & (l1_orders_2(X0) & v2_lattice3(X0) & v1_lattice3(X0) & v5_orders_2(X0) & v4_orders_2(X0) & v3_orders_2(X0)))),
% 2.43/0.99    inference(ennf_transformation,[],[f13])).
% 2.43/0.99  
% 2.43/0.99  fof(f37,plain,(
% 2.43/0.99    ? [X0] : (? [X1] : (~v4_waybel_7(X1,X0) & v5_waybel_6(X1,X0) & m1_subset_1(X1,u1_struct_0(X0))) & l1_orders_2(X0) & v2_lattice3(X0) & v1_lattice3(X0) & v5_orders_2(X0) & v4_orders_2(X0) & v3_orders_2(X0))),
% 2.43/0.99    inference(flattening,[],[f36])).
% 2.43/0.99  
% 2.43/0.99  fof(f50,plain,(
% 2.43/0.99    ( ! [X0] : (? [X1] : (~v4_waybel_7(X1,X0) & v5_waybel_6(X1,X0) & m1_subset_1(X1,u1_struct_0(X0))) => (~v4_waybel_7(sK4,X0) & v5_waybel_6(sK4,X0) & m1_subset_1(sK4,u1_struct_0(X0)))) )),
% 2.43/0.99    introduced(choice_axiom,[])).
% 2.43/0.99  
% 2.43/0.99  fof(f49,plain,(
% 2.43/0.99    ? [X0] : (? [X1] : (~v4_waybel_7(X1,X0) & v5_waybel_6(X1,X0) & m1_subset_1(X1,u1_struct_0(X0))) & l1_orders_2(X0) & v2_lattice3(X0) & v1_lattice3(X0) & v5_orders_2(X0) & v4_orders_2(X0) & v3_orders_2(X0)) => (? [X1] : (~v4_waybel_7(X1,sK3) & v5_waybel_6(X1,sK3) & m1_subset_1(X1,u1_struct_0(sK3))) & l1_orders_2(sK3) & v2_lattice3(sK3) & v1_lattice3(sK3) & v5_orders_2(sK3) & v4_orders_2(sK3) & v3_orders_2(sK3))),
% 2.43/0.99    introduced(choice_axiom,[])).
% 2.43/0.99  
% 2.43/0.99  fof(f51,plain,(
% 2.43/0.99    (~v4_waybel_7(sK4,sK3) & v5_waybel_6(sK4,sK3) & m1_subset_1(sK4,u1_struct_0(sK3))) & l1_orders_2(sK3) & v2_lattice3(sK3) & v1_lattice3(sK3) & v5_orders_2(sK3) & v4_orders_2(sK3) & v3_orders_2(sK3)),
% 2.43/0.99    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3,sK4])],[f37,f50,f49])).
% 2.43/0.99  
% 2.43/0.99  fof(f86,plain,(
% 2.43/0.99    l1_orders_2(sK3)),
% 2.43/0.99    inference(cnf_transformation,[],[f51])).
% 2.43/0.99  
% 2.43/0.99  fof(f56,plain,(
% 2.43/0.99    ( ! [X2,X0,X1] : (r2_lattice3(X0,X1,X2) | r2_hidden(sK0(X0,X1,X2),X1) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~l1_orders_2(X0)) )),
% 2.43/0.99    inference(cnf_transformation,[],[f41])).
% 2.43/0.99  
% 2.43/0.99  fof(f9,axiom,(
% 2.43/0.99    ! [X0] : ((l1_orders_2(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,u1_struct_0(X0)) => ! [X2] : (m1_subset_1(X2,u1_struct_0(X0)) => (r2_hidden(X2,k5_waybel_0(X0,X1)) <=> r1_orders_2(X0,X2,X1)))))),
% 2.43/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.43/0.99  
% 2.43/0.99  fof(f30,plain,(
% 2.43/0.99    ! [X0] : (! [X1] : (! [X2] : ((r2_hidden(X2,k5_waybel_0(X0,X1)) <=> r1_orders_2(X0,X2,X1)) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~m1_subset_1(X1,u1_struct_0(X0))) | (~l1_orders_2(X0) | v2_struct_0(X0)))),
% 2.43/0.99    inference(ennf_transformation,[],[f9])).
% 2.43/0.99  
% 2.43/0.99  fof(f31,plain,(
% 2.43/0.99    ! [X0] : (! [X1] : (! [X2] : ((r2_hidden(X2,k5_waybel_0(X0,X1)) <=> r1_orders_2(X0,X2,X1)) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~l1_orders_2(X0) | v2_struct_0(X0))),
% 2.43/0.99    inference(flattening,[],[f30])).
% 2.43/0.99  
% 2.43/0.99  fof(f44,plain,(
% 2.43/0.99    ! [X0] : (! [X1] : (! [X2] : (((r2_hidden(X2,k5_waybel_0(X0,X1)) | ~r1_orders_2(X0,X2,X1)) & (r1_orders_2(X0,X2,X1) | ~r2_hidden(X2,k5_waybel_0(X0,X1)))) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~l1_orders_2(X0) | v2_struct_0(X0))),
% 2.43/0.99    inference(nnf_transformation,[],[f31])).
% 2.43/0.99  
% 2.43/0.99  fof(f71,plain,(
% 2.43/0.99    ( ! [X2,X0,X1] : (r1_orders_2(X0,X2,X1) | ~r2_hidden(X2,k5_waybel_0(X0,X1)) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_orders_2(X0) | v2_struct_0(X0)) )),
% 2.43/0.99    inference(cnf_transformation,[],[f44])).
% 2.43/0.99  
% 2.43/0.99  fof(f2,axiom,(
% 2.43/0.99    ! [X0] : (l1_orders_2(X0) => (v1_lattice3(X0) => ~v2_struct_0(X0)))),
% 2.43/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.43/0.99  
% 2.43/0.99  fof(f17,plain,(
% 2.43/0.99    ! [X0] : ((~v2_struct_0(X0) | ~v1_lattice3(X0)) | ~l1_orders_2(X0))),
% 2.43/0.99    inference(ennf_transformation,[],[f2])).
% 2.43/0.99  
% 2.43/0.99  fof(f18,plain,(
% 2.43/0.99    ! [X0] : (~v2_struct_0(X0) | ~v1_lattice3(X0) | ~l1_orders_2(X0))),
% 2.43/0.99    inference(flattening,[],[f17])).
% 2.43/0.99  
% 2.43/0.99  fof(f53,plain,(
% 2.43/0.99    ( ! [X0] : (~v2_struct_0(X0) | ~v1_lattice3(X0) | ~l1_orders_2(X0)) )),
% 2.43/0.99    inference(cnf_transformation,[],[f18])).
% 2.43/0.99  
% 2.43/0.99  fof(f84,plain,(
% 2.43/0.99    v1_lattice3(sK3)),
% 2.43/0.99    inference(cnf_transformation,[],[f51])).
% 2.43/0.99  
% 2.43/0.99  fof(f57,plain,(
% 2.43/0.99    ( ! [X2,X0,X1] : (r2_lattice3(X0,X1,X2) | ~r1_orders_2(X0,sK0(X0,X1,X2),X2) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~l1_orders_2(X0)) )),
% 2.43/0.99    inference(cnf_transformation,[],[f41])).
% 2.43/0.99  
% 2.43/0.99  fof(f55,plain,(
% 2.43/0.99    ( ! [X2,X0,X1] : (r2_lattice3(X0,X1,X2) | m1_subset_1(sK0(X0,X1,X2),u1_struct_0(X0)) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~l1_orders_2(X0)) )),
% 2.43/0.99    inference(cnf_transformation,[],[f41])).
% 2.43/0.99  
% 2.43/0.99  fof(f5,axiom,(
% 2.43/0.99    ! [X0] : ((l1_orders_2(X0) & v5_orders_2(X0)) => ! [X1] : (m1_subset_1(X1,u1_struct_0(X0)) => ! [X2] : (((! [X3] : (m1_subset_1(X3,u1_struct_0(X0)) => (r2_lattice3(X0,X2,X3) => r1_orders_2(X0,X1,X3))) & r2_lattice3(X0,X2,X1)) => (r1_yellow_0(X0,X2) & k1_yellow_0(X0,X2) = X1)) & ((r1_yellow_0(X0,X2) & k1_yellow_0(X0,X2) = X1) => (! [X3] : (m1_subset_1(X3,u1_struct_0(X0)) => (r2_lattice3(X0,X2,X3) => r1_orders_2(X0,X1,X3))) & r2_lattice3(X0,X2,X1))))))),
% 2.43/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.43/0.99  
% 2.43/0.99  fof(f14,plain,(
% 2.43/0.99    ! [X0] : ((l1_orders_2(X0) & v5_orders_2(X0)) => ! [X1] : (m1_subset_1(X1,u1_struct_0(X0)) => ! [X2] : (((! [X3] : (m1_subset_1(X3,u1_struct_0(X0)) => (r2_lattice3(X0,X2,X3) => r1_orders_2(X0,X1,X3))) & r2_lattice3(X0,X2,X1)) => (r1_yellow_0(X0,X2) & k1_yellow_0(X0,X2) = X1)) & ((r1_yellow_0(X0,X2) & k1_yellow_0(X0,X2) = X1) => (! [X4] : (m1_subset_1(X4,u1_struct_0(X0)) => (r2_lattice3(X0,X2,X4) => r1_orders_2(X0,X1,X4))) & r2_lattice3(X0,X2,X1))))))),
% 2.43/0.99    inference(rectify,[],[f5])).
% 2.43/0.99  
% 2.43/0.99  fof(f22,plain,(
% 2.43/0.99    ! [X0] : (! [X1] : (! [X2] : (((r1_yellow_0(X0,X2) & k1_yellow_0(X0,X2) = X1) | (? [X3] : ((~r1_orders_2(X0,X1,X3) & r2_lattice3(X0,X2,X3)) & m1_subset_1(X3,u1_struct_0(X0))) | ~r2_lattice3(X0,X2,X1))) & ((! [X4] : ((r1_orders_2(X0,X1,X4) | ~r2_lattice3(X0,X2,X4)) | ~m1_subset_1(X4,u1_struct_0(X0))) & r2_lattice3(X0,X2,X1)) | (~r1_yellow_0(X0,X2) | k1_yellow_0(X0,X2) != X1))) | ~m1_subset_1(X1,u1_struct_0(X0))) | (~l1_orders_2(X0) | ~v5_orders_2(X0)))),
% 2.43/0.99    inference(ennf_transformation,[],[f14])).
% 2.43/0.99  
% 2.43/0.99  fof(f23,plain,(
% 2.43/0.99    ! [X0] : (! [X1] : (! [X2] : (((r1_yellow_0(X0,X2) & k1_yellow_0(X0,X2) = X1) | ? [X3] : (~r1_orders_2(X0,X1,X3) & r2_lattice3(X0,X2,X3) & m1_subset_1(X3,u1_struct_0(X0))) | ~r2_lattice3(X0,X2,X1)) & ((! [X4] : (r1_orders_2(X0,X1,X4) | ~r2_lattice3(X0,X2,X4) | ~m1_subset_1(X4,u1_struct_0(X0))) & r2_lattice3(X0,X2,X1)) | ~r1_yellow_0(X0,X2) | k1_yellow_0(X0,X2) != X1)) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~l1_orders_2(X0) | ~v5_orders_2(X0))),
% 2.43/0.99    inference(flattening,[],[f22])).
% 2.43/0.99  
% 2.43/0.99  fof(f42,plain,(
% 2.43/0.99    ! [X2,X1,X0] : (? [X3] : (~r1_orders_2(X0,X1,X3) & r2_lattice3(X0,X2,X3) & m1_subset_1(X3,u1_struct_0(X0))) => (~r1_orders_2(X0,X1,sK1(X0,X1,X2)) & r2_lattice3(X0,X2,sK1(X0,X1,X2)) & m1_subset_1(sK1(X0,X1,X2),u1_struct_0(X0))))),
% 2.43/0.99    introduced(choice_axiom,[])).
% 2.43/0.99  
% 2.43/0.99  fof(f43,plain,(
% 2.43/0.99    ! [X0] : (! [X1] : (! [X2] : (((r1_yellow_0(X0,X2) & k1_yellow_0(X0,X2) = X1) | (~r1_orders_2(X0,X1,sK1(X0,X1,X2)) & r2_lattice3(X0,X2,sK1(X0,X1,X2)) & m1_subset_1(sK1(X0,X1,X2),u1_struct_0(X0))) | ~r2_lattice3(X0,X2,X1)) & ((! [X4] : (r1_orders_2(X0,X1,X4) | ~r2_lattice3(X0,X2,X4) | ~m1_subset_1(X4,u1_struct_0(X0))) & r2_lattice3(X0,X2,X1)) | ~r1_yellow_0(X0,X2) | k1_yellow_0(X0,X2) != X1)) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~l1_orders_2(X0) | ~v5_orders_2(X0))),
% 2.43/0.99    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1])],[f23,f42])).
% 2.43/0.99  
% 2.43/0.99  fof(f62,plain,(
% 2.43/0.99    ( ! [X2,X0,X1] : (k1_yellow_0(X0,X2) = X1 | r2_lattice3(X0,X2,sK1(X0,X1,X2)) | ~r2_lattice3(X0,X2,X1) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_orders_2(X0) | ~v5_orders_2(X0)) )),
% 2.43/0.99    inference(cnf_transformation,[],[f43])).
% 2.43/0.99  
% 2.43/0.99  fof(f83,plain,(
% 2.43/0.99    v5_orders_2(sK3)),
% 2.43/0.99    inference(cnf_transformation,[],[f51])).
% 2.43/0.99  
% 2.43/0.99  fof(f63,plain,(
% 2.43/0.99    ( ! [X2,X0,X1] : (k1_yellow_0(X0,X2) = X1 | ~r1_orders_2(X0,X1,sK1(X0,X1,X2)) | ~r2_lattice3(X0,X2,X1) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_orders_2(X0) | ~v5_orders_2(X0)) )),
% 2.43/0.99    inference(cnf_transformation,[],[f43])).
% 2.43/0.99  
% 2.43/0.99  fof(f61,plain,(
% 2.43/0.99    ( ! [X2,X0,X1] : (k1_yellow_0(X0,X2) = X1 | m1_subset_1(sK1(X0,X1,X2),u1_struct_0(X0)) | ~r2_lattice3(X0,X2,X1) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_orders_2(X0) | ~v5_orders_2(X0)) )),
% 2.43/0.99    inference(cnf_transformation,[],[f43])).
% 2.43/0.99  
% 2.43/0.99  fof(f4,axiom,(
% 2.43/0.99    ! [X0,X1] : (l1_orders_2(X0) => m1_subset_1(k1_yellow_0(X0,X1),u1_struct_0(X0)))),
% 2.43/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.43/0.99  
% 2.43/0.99  fof(f21,plain,(
% 2.43/0.99    ! [X0,X1] : (m1_subset_1(k1_yellow_0(X0,X1),u1_struct_0(X0)) | ~l1_orders_2(X0))),
% 2.43/0.99    inference(ennf_transformation,[],[f4])).
% 2.43/0.99  
% 2.43/0.99  fof(f58,plain,(
% 2.43/0.99    ( ! [X0,X1] : (m1_subset_1(k1_yellow_0(X0,X1),u1_struct_0(X0)) | ~l1_orders_2(X0)) )),
% 2.43/0.99    inference(cnf_transformation,[],[f21])).
% 2.43/0.99  
% 2.43/0.99  fof(f7,axiom,(
% 2.43/0.99    ! [X0,X1] : ((m1_subset_1(X1,u1_struct_0(X0)) & l1_orders_2(X0) & v4_orders_2(X0) & ~v2_struct_0(X0)) => v12_waybel_0(k5_waybel_0(X0,X1),X0))),
% 2.43/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.43/0.99  
% 2.43/0.99  fof(f26,plain,(
% 2.43/0.99    ! [X0,X1] : (v12_waybel_0(k5_waybel_0(X0,X1),X0) | (~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_orders_2(X0) | ~v4_orders_2(X0) | v2_struct_0(X0)))),
% 2.43/0.99    inference(ennf_transformation,[],[f7])).
% 2.43/0.99  
% 2.43/0.99  fof(f27,plain,(
% 2.43/0.99    ! [X0,X1] : (v12_waybel_0(k5_waybel_0(X0,X1),X0) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_orders_2(X0) | ~v4_orders_2(X0) | v2_struct_0(X0))),
% 2.43/0.99    inference(flattening,[],[f26])).
% 2.43/0.99  
% 2.43/0.99  fof(f68,plain,(
% 2.43/0.99    ( ! [X0,X1] : (v12_waybel_0(k5_waybel_0(X0,X1),X0) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_orders_2(X0) | ~v4_orders_2(X0) | v2_struct_0(X0)) )),
% 2.43/0.99    inference(cnf_transformation,[],[f27])).
% 2.43/0.99  
% 2.43/0.99  fof(f10,axiom,(
% 2.43/0.99    ! [X0] : ((l1_orders_2(X0) & v2_lattice3(X0) & v1_lattice3(X0) & v5_orders_2(X0) & v4_orders_2(X0) & v3_orders_2(X0)) => ! [X1] : (m1_subset_1(X1,u1_struct_0(X0)) => (v4_waybel_7(X1,X0) <=> ? [X2] : (k1_yellow_0(X0,X2) = X1 & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) & v1_waybel_7(X2,X0) & v12_waybel_0(X2,X0) & v1_waybel_0(X2,X0) & ~v1_xboole_0(X2)))))),
% 2.43/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.43/0.99  
% 2.43/0.99  fof(f32,plain,(
% 2.43/0.99    ! [X0] : (! [X1] : ((v4_waybel_7(X1,X0) <=> ? [X2] : (k1_yellow_0(X0,X2) = X1 & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) & v1_waybel_7(X2,X0) & v12_waybel_0(X2,X0) & v1_waybel_0(X2,X0) & ~v1_xboole_0(X2))) | ~m1_subset_1(X1,u1_struct_0(X0))) | (~l1_orders_2(X0) | ~v2_lattice3(X0) | ~v1_lattice3(X0) | ~v5_orders_2(X0) | ~v4_orders_2(X0) | ~v3_orders_2(X0)))),
% 2.43/0.99    inference(ennf_transformation,[],[f10])).
% 2.43/0.99  
% 2.43/0.99  fof(f33,plain,(
% 2.43/0.99    ! [X0] : (! [X1] : ((v4_waybel_7(X1,X0) <=> ? [X2] : (k1_yellow_0(X0,X2) = X1 & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) & v1_waybel_7(X2,X0) & v12_waybel_0(X2,X0) & v1_waybel_0(X2,X0) & ~v1_xboole_0(X2))) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~l1_orders_2(X0) | ~v2_lattice3(X0) | ~v1_lattice3(X0) | ~v5_orders_2(X0) | ~v4_orders_2(X0) | ~v3_orders_2(X0))),
% 2.43/0.99    inference(flattening,[],[f32])).
% 2.43/0.99  
% 2.43/0.99  fof(f45,plain,(
% 2.43/0.99    ! [X0] : (! [X1] : (((v4_waybel_7(X1,X0) | ! [X2] : (k1_yellow_0(X0,X2) != X1 | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) | ~v1_waybel_7(X2,X0) | ~v12_waybel_0(X2,X0) | ~v1_waybel_0(X2,X0) | v1_xboole_0(X2))) & (? [X2] : (k1_yellow_0(X0,X2) = X1 & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) & v1_waybel_7(X2,X0) & v12_waybel_0(X2,X0) & v1_waybel_0(X2,X0) & ~v1_xboole_0(X2)) | ~v4_waybel_7(X1,X0))) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~l1_orders_2(X0) | ~v2_lattice3(X0) | ~v1_lattice3(X0) | ~v5_orders_2(X0) | ~v4_orders_2(X0) | ~v3_orders_2(X0))),
% 2.43/0.99    inference(nnf_transformation,[],[f33])).
% 2.43/0.99  
% 2.43/0.99  fof(f46,plain,(
% 2.43/0.99    ! [X0] : (! [X1] : (((v4_waybel_7(X1,X0) | ! [X2] : (k1_yellow_0(X0,X2) != X1 | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) | ~v1_waybel_7(X2,X0) | ~v12_waybel_0(X2,X0) | ~v1_waybel_0(X2,X0) | v1_xboole_0(X2))) & (? [X3] : (k1_yellow_0(X0,X3) = X1 & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) & v1_waybel_7(X3,X0) & v12_waybel_0(X3,X0) & v1_waybel_0(X3,X0) & ~v1_xboole_0(X3)) | ~v4_waybel_7(X1,X0))) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~l1_orders_2(X0) | ~v2_lattice3(X0) | ~v1_lattice3(X0) | ~v5_orders_2(X0) | ~v4_orders_2(X0) | ~v3_orders_2(X0))),
% 2.43/0.99    inference(rectify,[],[f45])).
% 2.43/0.99  
% 2.43/0.99  fof(f47,plain,(
% 2.43/0.99    ! [X1,X0] : (? [X3] : (k1_yellow_0(X0,X3) = X1 & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) & v1_waybel_7(X3,X0) & v12_waybel_0(X3,X0) & v1_waybel_0(X3,X0) & ~v1_xboole_0(X3)) => (k1_yellow_0(X0,sK2(X0,X1)) = X1 & m1_subset_1(sK2(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) & v1_waybel_7(sK2(X0,X1),X0) & v12_waybel_0(sK2(X0,X1),X0) & v1_waybel_0(sK2(X0,X1),X0) & ~v1_xboole_0(sK2(X0,X1))))),
% 2.43/0.99    introduced(choice_axiom,[])).
% 2.43/0.99  
% 2.43/0.99  fof(f48,plain,(
% 2.43/0.99    ! [X0] : (! [X1] : (((v4_waybel_7(X1,X0) | ! [X2] : (k1_yellow_0(X0,X2) != X1 | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) | ~v1_waybel_7(X2,X0) | ~v12_waybel_0(X2,X0) | ~v1_waybel_0(X2,X0) | v1_xboole_0(X2))) & ((k1_yellow_0(X0,sK2(X0,X1)) = X1 & m1_subset_1(sK2(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) & v1_waybel_7(sK2(X0,X1),X0) & v12_waybel_0(sK2(X0,X1),X0) & v1_waybel_0(sK2(X0,X1),X0) & ~v1_xboole_0(sK2(X0,X1))) | ~v4_waybel_7(X1,X0))) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~l1_orders_2(X0) | ~v2_lattice3(X0) | ~v1_lattice3(X0) | ~v5_orders_2(X0) | ~v4_orders_2(X0) | ~v3_orders_2(X0))),
% 2.43/0.99    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2])],[f46,f47])).
% 2.43/0.99  
% 2.43/0.99  fof(f79,plain,(
% 2.43/0.99    ( ! [X2,X0,X1] : (v4_waybel_7(X1,X0) | k1_yellow_0(X0,X2) != X1 | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) | ~v1_waybel_7(X2,X0) | ~v12_waybel_0(X2,X0) | ~v1_waybel_0(X2,X0) | v1_xboole_0(X2) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_orders_2(X0) | ~v2_lattice3(X0) | ~v1_lattice3(X0) | ~v5_orders_2(X0) | ~v4_orders_2(X0) | ~v3_orders_2(X0)) )),
% 2.43/0.99    inference(cnf_transformation,[],[f48])).
% 2.43/0.99  
% 2.43/0.99  fof(f92,plain,(
% 2.43/0.99    ( ! [X2,X0] : (v4_waybel_7(k1_yellow_0(X0,X2),X0) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) | ~v1_waybel_7(X2,X0) | ~v12_waybel_0(X2,X0) | ~v1_waybel_0(X2,X0) | v1_xboole_0(X2) | ~m1_subset_1(k1_yellow_0(X0,X2),u1_struct_0(X0)) | ~l1_orders_2(X0) | ~v2_lattice3(X0) | ~v1_lattice3(X0) | ~v5_orders_2(X0) | ~v4_orders_2(X0) | ~v3_orders_2(X0)) )),
% 2.43/0.99    inference(equality_resolution,[],[f79])).
% 2.43/0.99  
% 2.43/0.99  fof(f11,axiom,(
% 2.43/0.99    ! [X0] : ((l1_orders_2(X0) & v2_lattice3(X0) & v1_lattice3(X0) & v5_orders_2(X0) & v4_orders_2(X0) & v3_orders_2(X0)) => ! [X1] : (m1_subset_1(X1,u1_struct_0(X0)) => (v5_waybel_6(X1,X0) => v1_waybel_7(k5_waybel_0(X0,X1),X0))))),
% 2.43/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.43/0.99  
% 2.43/0.99  fof(f34,plain,(
% 2.43/0.99    ! [X0] : (! [X1] : ((v1_waybel_7(k5_waybel_0(X0,X1),X0) | ~v5_waybel_6(X1,X0)) | ~m1_subset_1(X1,u1_struct_0(X0))) | (~l1_orders_2(X0) | ~v2_lattice3(X0) | ~v1_lattice3(X0) | ~v5_orders_2(X0) | ~v4_orders_2(X0) | ~v3_orders_2(X0)))),
% 2.43/0.99    inference(ennf_transformation,[],[f11])).
% 2.43/0.99  
% 2.43/0.99  fof(f35,plain,(
% 2.43/0.99    ! [X0] : (! [X1] : (v1_waybel_7(k5_waybel_0(X0,X1),X0) | ~v5_waybel_6(X1,X0) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~l1_orders_2(X0) | ~v2_lattice3(X0) | ~v1_lattice3(X0) | ~v5_orders_2(X0) | ~v4_orders_2(X0) | ~v3_orders_2(X0))),
% 2.43/0.99    inference(flattening,[],[f34])).
% 2.43/0.99  
% 2.43/0.99  fof(f80,plain,(
% 2.43/0.99    ( ! [X0,X1] : (v1_waybel_7(k5_waybel_0(X0,X1),X0) | ~v5_waybel_6(X1,X0) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_orders_2(X0) | ~v2_lattice3(X0) | ~v1_lattice3(X0) | ~v5_orders_2(X0) | ~v4_orders_2(X0) | ~v3_orders_2(X0)) )),
% 2.43/0.99    inference(cnf_transformation,[],[f35])).
% 2.43/0.99  
% 2.43/0.99  fof(f88,plain,(
% 2.43/0.99    v5_waybel_6(sK4,sK3)),
% 2.43/0.99    inference(cnf_transformation,[],[f51])).
% 2.43/0.99  
% 2.43/0.99  fof(f81,plain,(
% 2.43/0.99    v3_orders_2(sK3)),
% 2.43/0.99    inference(cnf_transformation,[],[f51])).
% 2.43/0.99  
% 2.43/0.99  fof(f82,plain,(
% 2.43/0.99    v4_orders_2(sK3)),
% 2.43/0.99    inference(cnf_transformation,[],[f51])).
% 2.43/0.99  
% 2.43/0.99  fof(f85,plain,(
% 2.43/0.99    v2_lattice3(sK3)),
% 2.43/0.99    inference(cnf_transformation,[],[f51])).
% 2.43/0.99  
% 2.43/0.99  fof(f87,plain,(
% 2.43/0.99    m1_subset_1(sK4,u1_struct_0(sK3))),
% 2.43/0.99    inference(cnf_transformation,[],[f51])).
% 2.43/0.99  
% 2.43/0.99  fof(f6,axiom,(
% 2.43/0.99    ! [X0,X1] : ((m1_subset_1(X1,u1_struct_0(X0)) & l1_orders_2(X0) & ~v2_struct_0(X0)) => m1_subset_1(k5_waybel_0(X0,X1),k1_zfmisc_1(u1_struct_0(X0))))),
% 2.43/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.43/0.99  
% 2.43/0.99  fof(f24,plain,(
% 2.43/0.99    ! [X0,X1] : (m1_subset_1(k5_waybel_0(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) | (~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_orders_2(X0) | v2_struct_0(X0)))),
% 2.43/0.99    inference(ennf_transformation,[],[f6])).
% 2.43/0.99  
% 2.43/0.99  fof(f25,plain,(
% 2.43/0.99    ! [X0,X1] : (m1_subset_1(k5_waybel_0(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_orders_2(X0) | v2_struct_0(X0))),
% 2.43/0.99    inference(flattening,[],[f24])).
% 2.43/0.99  
% 2.43/0.99  fof(f67,plain,(
% 2.43/0.99    ( ! [X0,X1] : (m1_subset_1(k5_waybel_0(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_orders_2(X0) | v2_struct_0(X0)) )),
% 2.43/0.99    inference(cnf_transformation,[],[f25])).
% 2.43/0.99  
% 2.43/0.99  fof(f72,plain,(
% 2.43/0.99    ( ! [X2,X0,X1] : (r2_hidden(X2,k5_waybel_0(X0,X1)) | ~r1_orders_2(X0,X2,X1) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_orders_2(X0) | v2_struct_0(X0)) )),
% 2.43/0.99    inference(cnf_transformation,[],[f44])).
% 2.43/0.99  
% 2.43/0.99  fof(f8,axiom,(
% 2.43/0.99    ! [X0,X1] : ((m1_subset_1(X1,u1_struct_0(X0)) & l1_orders_2(X0) & v3_orders_2(X0) & ~v2_struct_0(X0)) => (v1_waybel_0(k5_waybel_0(X0,X1),X0) & ~v1_xboole_0(k5_waybel_0(X0,X1))))),
% 2.43/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.43/0.99  
% 2.43/0.99  fof(f28,plain,(
% 2.43/0.99    ! [X0,X1] : ((v1_waybel_0(k5_waybel_0(X0,X1),X0) & ~v1_xboole_0(k5_waybel_0(X0,X1))) | (~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_orders_2(X0) | ~v3_orders_2(X0) | v2_struct_0(X0)))),
% 2.43/0.99    inference(ennf_transformation,[],[f8])).
% 2.43/0.99  
% 2.43/0.99  fof(f29,plain,(
% 2.43/0.99    ! [X0,X1] : ((v1_waybel_0(k5_waybel_0(X0,X1),X0) & ~v1_xboole_0(k5_waybel_0(X0,X1))) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_orders_2(X0) | ~v3_orders_2(X0) | v2_struct_0(X0))),
% 2.43/0.99    inference(flattening,[],[f28])).
% 2.43/0.99  
% 2.43/0.99  fof(f69,plain,(
% 2.43/0.99    ( ! [X0,X1] : (~v1_xboole_0(k5_waybel_0(X0,X1)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_orders_2(X0) | ~v3_orders_2(X0) | v2_struct_0(X0)) )),
% 2.43/0.99    inference(cnf_transformation,[],[f29])).
% 2.43/0.99  
% 2.43/0.99  fof(f70,plain,(
% 2.43/0.99    ( ! [X0,X1] : (v1_waybel_0(k5_waybel_0(X0,X1),X0) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_orders_2(X0) | ~v3_orders_2(X0) | v2_struct_0(X0)) )),
% 2.43/0.99    inference(cnf_transformation,[],[f29])).
% 2.43/0.99  
% 2.43/0.99  fof(f1,axiom,(
% 2.43/0.99    ! [X0] : ((l1_orders_2(X0) & v3_orders_2(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,u1_struct_0(X0)) => r1_orders_2(X0,X1,X1)))),
% 2.43/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.43/0.99  
% 2.43/0.99  fof(f15,plain,(
% 2.43/0.99    ! [X0] : (! [X1] : (r1_orders_2(X0,X1,X1) | ~m1_subset_1(X1,u1_struct_0(X0))) | (~l1_orders_2(X0) | ~v3_orders_2(X0) | v2_struct_0(X0)))),
% 2.43/0.99    inference(ennf_transformation,[],[f1])).
% 2.43/0.99  
% 2.43/0.99  fof(f16,plain,(
% 2.43/0.99    ! [X0] : (! [X1] : (r1_orders_2(X0,X1,X1) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~l1_orders_2(X0) | ~v3_orders_2(X0) | v2_struct_0(X0))),
% 2.43/0.99    inference(flattening,[],[f15])).
% 2.43/0.99  
% 2.43/0.99  fof(f52,plain,(
% 2.43/0.99    ( ! [X0,X1] : (r1_orders_2(X0,X1,X1) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_orders_2(X0) | ~v3_orders_2(X0) | v2_struct_0(X0)) )),
% 2.43/0.99    inference(cnf_transformation,[],[f16])).
% 2.43/0.99  
% 2.43/0.99  fof(f89,plain,(
% 2.43/0.99    ~v4_waybel_7(sK4,sK3)),
% 2.43/0.99    inference(cnf_transformation,[],[f51])).
% 2.43/0.99  
% 2.43/0.99  cnf(c_5,plain,
% 2.43/0.99      ( ~ r2_lattice3(X0,X1,X2)
% 2.43/0.99      | r1_orders_2(X0,X3,X2)
% 2.43/0.99      | ~ r2_hidden(X3,X1)
% 2.43/0.99      | ~ m1_subset_1(X2,u1_struct_0(X0))
% 2.43/0.99      | ~ m1_subset_1(X3,u1_struct_0(X0))
% 2.43/0.99      | ~ l1_orders_2(X0) ),
% 2.43/0.99      inference(cnf_transformation,[],[f54]) ).
% 2.43/0.99  
% 2.43/0.99  cnf(c_32,negated_conjecture,
% 2.43/0.99      ( l1_orders_2(sK3) ),
% 2.43/0.99      inference(cnf_transformation,[],[f86]) ).
% 2.43/0.99  
% 2.43/0.99  cnf(c_1871,plain,
% 2.43/0.99      ( ~ r2_lattice3(X0,X1,X2)
% 2.43/0.99      | r1_orders_2(X0,X3,X2)
% 2.43/0.99      | ~ r2_hidden(X3,X1)
% 2.43/0.99      | ~ m1_subset_1(X2,u1_struct_0(X0))
% 2.43/0.99      | ~ m1_subset_1(X3,u1_struct_0(X0))
% 2.43/0.99      | sK3 != X0 ),
% 2.43/0.99      inference(resolution_lifted,[status(thm)],[c_5,c_32]) ).
% 2.43/0.99  
% 2.43/0.99  cnf(c_1872,plain,
% 2.43/0.99      ( ~ r2_lattice3(sK3,X0,X1)
% 2.43/0.99      | r1_orders_2(sK3,X2,X1)
% 2.43/0.99      | ~ r2_hidden(X2,X0)
% 2.43/0.99      | ~ m1_subset_1(X1,u1_struct_0(sK3))
% 2.43/0.99      | ~ m1_subset_1(X2,u1_struct_0(sK3)) ),
% 2.43/0.99      inference(unflattening,[status(thm)],[c_1871]) ).
% 2.43/0.99  
% 2.43/0.99  cnf(c_3800,plain,
% 2.43/0.99      ( ~ r2_lattice3(sK3,X0_55,X1_55)
% 2.43/0.99      | r1_orders_2(sK3,X2_55,X1_55)
% 2.43/0.99      | ~ r2_hidden(X2_55,X0_55)
% 2.43/0.99      | ~ m1_subset_1(X1_55,u1_struct_0(sK3))
% 2.43/0.99      | ~ m1_subset_1(X2_55,u1_struct_0(sK3)) ),
% 2.43/0.99      inference(subtyping,[status(esa)],[c_1872]) ).
% 2.43/0.99  
% 2.43/0.99  cnf(c_5725,plain,
% 2.43/0.99      ( ~ r2_lattice3(sK3,X0_55,sK1(sK3,X1_55,k5_waybel_0(sK3,sK4)))
% 2.43/0.99      | r1_orders_2(sK3,X1_55,sK1(sK3,X1_55,k5_waybel_0(sK3,sK4)))
% 2.43/0.99      | ~ r2_hidden(X1_55,X0_55)
% 2.43/0.99      | ~ m1_subset_1(X1_55,u1_struct_0(sK3))
% 2.43/0.99      | ~ m1_subset_1(sK1(sK3,X1_55,k5_waybel_0(sK3,sK4)),u1_struct_0(sK3)) ),
% 2.43/0.99      inference(instantiation,[status(thm)],[c_3800]) ).
% 2.43/0.99  
% 2.43/0.99  cnf(c_7244,plain,
% 2.43/0.99      ( ~ r2_lattice3(sK3,k5_waybel_0(sK3,X0_55),sK1(sK3,X1_55,k5_waybel_0(sK3,sK4)))
% 2.43/0.99      | r1_orders_2(sK3,X1_55,sK1(sK3,X1_55,k5_waybel_0(sK3,sK4)))
% 2.43/0.99      | ~ r2_hidden(X1_55,k5_waybel_0(sK3,X0_55))
% 2.43/0.99      | ~ m1_subset_1(X1_55,u1_struct_0(sK3))
% 2.43/0.99      | ~ m1_subset_1(sK1(sK3,X1_55,k5_waybel_0(sK3,sK4)),u1_struct_0(sK3)) ),
% 2.43/0.99      inference(instantiation,[status(thm)],[c_5725]) ).
% 2.43/0.99  
% 2.43/0.99  cnf(c_7245,plain,
% 2.43/0.99      ( r2_lattice3(sK3,k5_waybel_0(sK3,X0_55),sK1(sK3,X1_55,k5_waybel_0(sK3,sK4))) != iProver_top
% 2.43/0.99      | r1_orders_2(sK3,X1_55,sK1(sK3,X1_55,k5_waybel_0(sK3,sK4))) = iProver_top
% 2.43/0.99      | r2_hidden(X1_55,k5_waybel_0(sK3,X0_55)) != iProver_top
% 2.43/0.99      | m1_subset_1(X1_55,u1_struct_0(sK3)) != iProver_top
% 2.43/0.99      | m1_subset_1(sK1(sK3,X1_55,k5_waybel_0(sK3,sK4)),u1_struct_0(sK3)) != iProver_top ),
% 2.43/0.99      inference(predicate_to_equality,[status(thm)],[c_7244]) ).
% 2.43/0.99  
% 2.43/0.99  cnf(c_7247,plain,
% 2.43/0.99      ( r2_lattice3(sK3,k5_waybel_0(sK3,sK4),sK1(sK3,sK4,k5_waybel_0(sK3,sK4))) != iProver_top
% 2.43/0.99      | r1_orders_2(sK3,sK4,sK1(sK3,sK4,k5_waybel_0(sK3,sK4))) = iProver_top
% 2.43/0.99      | r2_hidden(sK4,k5_waybel_0(sK3,sK4)) != iProver_top
% 2.43/0.99      | m1_subset_1(sK1(sK3,sK4,k5_waybel_0(sK3,sK4)),u1_struct_0(sK3)) != iProver_top
% 2.43/0.99      | m1_subset_1(sK4,u1_struct_0(sK3)) != iProver_top ),
% 2.43/0.99      inference(instantiation,[status(thm)],[c_7245]) ).
% 2.43/0.99  
% 2.43/0.99  cnf(c_3,plain,
% 2.43/0.99      ( r2_lattice3(X0,X1,X2)
% 2.43/0.99      | r2_hidden(sK0(X0,X1,X2),X1)
% 2.43/0.99      | ~ m1_subset_1(X2,u1_struct_0(X0))
% 2.43/0.99      | ~ l1_orders_2(X0) ),
% 2.43/0.99      inference(cnf_transformation,[],[f56]) ).
% 2.43/0.99  
% 2.43/0.99  cnf(c_1905,plain,
% 2.43/0.99      ( r2_lattice3(X0,X1,X2)
% 2.43/0.99      | r2_hidden(sK0(X0,X1,X2),X1)
% 2.43/0.99      | ~ m1_subset_1(X2,u1_struct_0(X0))
% 2.43/0.99      | sK3 != X0 ),
% 2.43/0.99      inference(resolution_lifted,[status(thm)],[c_3,c_32]) ).
% 2.43/0.99  
% 2.43/0.99  cnf(c_1906,plain,
% 2.43/0.99      ( r2_lattice3(sK3,X0,X1)
% 2.43/0.99      | r2_hidden(sK0(sK3,X0,X1),X0)
% 2.43/0.99      | ~ m1_subset_1(X1,u1_struct_0(sK3)) ),
% 2.43/0.99      inference(unflattening,[status(thm)],[c_1905]) ).
% 2.43/0.99  
% 2.43/0.99  cnf(c_3798,plain,
% 2.43/0.99      ( r2_lattice3(sK3,X0_55,X1_55)
% 2.43/0.99      | r2_hidden(sK0(sK3,X0_55,X1_55),X0_55)
% 2.43/0.99      | ~ m1_subset_1(X1_55,u1_struct_0(sK3)) ),
% 2.43/0.99      inference(subtyping,[status(esa)],[c_1906]) ).
% 2.43/0.99  
% 2.43/0.99  cnf(c_4366,plain,
% 2.43/0.99      ( r2_lattice3(sK3,X0_55,X1_55) = iProver_top
% 2.43/0.99      | r2_hidden(sK0(sK3,X0_55,X1_55),X0_55) = iProver_top
% 2.43/0.99      | m1_subset_1(X1_55,u1_struct_0(sK3)) != iProver_top ),
% 2.43/0.99      inference(predicate_to_equality,[status(thm)],[c_3798]) ).
% 2.43/0.99  
% 2.43/0.99  cnf(c_20,plain,
% 2.43/0.99      ( r1_orders_2(X0,X1,X2)
% 2.43/0.99      | ~ r2_hidden(X1,k5_waybel_0(X0,X2))
% 2.43/0.99      | ~ m1_subset_1(X2,u1_struct_0(X0))
% 2.43/0.99      | ~ m1_subset_1(X1,u1_struct_0(X0))
% 2.43/0.99      | v2_struct_0(X0)
% 2.43/0.99      | ~ l1_orders_2(X0) ),
% 2.43/0.99      inference(cnf_transformation,[],[f71]) ).
% 2.43/0.99  
% 2.43/0.99  cnf(c_1,plain,
% 2.43/0.99      ( ~ v1_lattice3(X0) | ~ v2_struct_0(X0) | ~ l1_orders_2(X0) ),
% 2.43/0.99      inference(cnf_transformation,[],[f53]) ).
% 2.43/0.99  
% 2.43/0.99  cnf(c_740,plain,
% 2.43/0.99      ( r1_orders_2(X0,X1,X2)
% 2.43/0.99      | ~ r2_hidden(X1,k5_waybel_0(X0,X2))
% 2.43/0.99      | ~ m1_subset_1(X1,u1_struct_0(X0))
% 2.43/0.99      | ~ m1_subset_1(X2,u1_struct_0(X0))
% 2.43/0.99      | ~ v1_lattice3(X0)
% 2.43/0.99      | ~ l1_orders_2(X0) ),
% 2.43/0.99      inference(resolution,[status(thm)],[c_20,c_1]) ).
% 2.43/0.99  
% 2.43/0.99  cnf(c_34,negated_conjecture,
% 2.43/0.99      ( v1_lattice3(sK3) ),
% 2.43/0.99      inference(cnf_transformation,[],[f84]) ).
% 2.43/0.99  
% 2.43/0.99  cnf(c_1233,plain,
% 2.43/0.99      ( r1_orders_2(X0,X1,X2)
% 2.43/0.99      | ~ r2_hidden(X1,k5_waybel_0(X0,X2))
% 2.43/0.99      | ~ m1_subset_1(X1,u1_struct_0(X0))
% 2.43/0.99      | ~ m1_subset_1(X2,u1_struct_0(X0))
% 2.43/0.99      | ~ l1_orders_2(X0)
% 2.43/0.99      | sK3 != X0 ),
% 2.43/0.99      inference(resolution_lifted,[status(thm)],[c_740,c_34]) ).
% 2.43/0.99  
% 2.43/0.99  cnf(c_1234,plain,
% 2.43/0.99      ( r1_orders_2(sK3,X0,X1)
% 2.43/0.99      | ~ r2_hidden(X0,k5_waybel_0(sK3,X1))
% 2.43/0.99      | ~ m1_subset_1(X0,u1_struct_0(sK3))
% 2.43/0.99      | ~ m1_subset_1(X1,u1_struct_0(sK3))
% 2.43/0.99      | ~ l1_orders_2(sK3) ),
% 2.43/0.99      inference(unflattening,[status(thm)],[c_1233]) ).
% 2.43/0.99  
% 2.43/0.99  cnf(c_1236,plain,
% 2.43/0.99      ( ~ m1_subset_1(X1,u1_struct_0(sK3))
% 2.43/0.99      | ~ m1_subset_1(X0,u1_struct_0(sK3))
% 2.43/0.99      | ~ r2_hidden(X0,k5_waybel_0(sK3,X1))
% 2.43/0.99      | r1_orders_2(sK3,X0,X1) ),
% 2.43/0.99      inference(global_propositional_subsumption,
% 2.43/0.99                [status(thm)],
% 2.43/0.99                [c_1234,c_32]) ).
% 2.43/0.99  
% 2.43/0.99  cnf(c_1237,plain,
% 2.43/0.99      ( r1_orders_2(sK3,X0,X1)
% 2.43/0.99      | ~ r2_hidden(X0,k5_waybel_0(sK3,X1))
% 2.43/0.99      | ~ m1_subset_1(X1,u1_struct_0(sK3))
% 2.43/0.99      | ~ m1_subset_1(X0,u1_struct_0(sK3)) ),
% 2.43/0.99      inference(renaming,[status(thm)],[c_1236]) ).
% 2.43/0.99  
% 2.43/0.99  cnf(c_3811,plain,
% 2.43/0.99      ( r1_orders_2(sK3,X0_55,X1_55)
% 2.43/0.99      | ~ r2_hidden(X0_55,k5_waybel_0(sK3,X1_55))
% 2.43/0.99      | ~ m1_subset_1(X0_55,u1_struct_0(sK3))
% 2.43/0.99      | ~ m1_subset_1(X1_55,u1_struct_0(sK3)) ),
% 2.43/0.99      inference(subtyping,[status(esa)],[c_1237]) ).
% 2.43/0.99  
% 2.43/0.99  cnf(c_4353,plain,
% 2.43/0.99      ( r1_orders_2(sK3,X0_55,X1_55) = iProver_top
% 2.43/0.99      | r2_hidden(X0_55,k5_waybel_0(sK3,X1_55)) != iProver_top
% 2.43/0.99      | m1_subset_1(X0_55,u1_struct_0(sK3)) != iProver_top
% 2.43/0.99      | m1_subset_1(X1_55,u1_struct_0(sK3)) != iProver_top ),
% 2.43/0.99      inference(predicate_to_equality,[status(thm)],[c_3811]) ).
% 2.43/0.99  
% 2.43/0.99  cnf(c_5454,plain,
% 2.43/0.99      ( r2_lattice3(sK3,k5_waybel_0(sK3,X0_55),X1_55) = iProver_top
% 2.43/0.99      | r1_orders_2(sK3,sK0(sK3,k5_waybel_0(sK3,X0_55),X1_55),X0_55) = iProver_top
% 2.43/0.99      | m1_subset_1(X0_55,u1_struct_0(sK3)) != iProver_top
% 2.43/0.99      | m1_subset_1(X1_55,u1_struct_0(sK3)) != iProver_top
% 2.43/0.99      | m1_subset_1(sK0(sK3,k5_waybel_0(sK3,X0_55),X1_55),u1_struct_0(sK3)) != iProver_top ),
% 2.43/0.99      inference(superposition,[status(thm)],[c_4366,c_4353]) ).
% 2.43/0.99  
% 2.43/0.99  cnf(c_5467,plain,
% 2.43/0.99      ( r2_lattice3(sK3,k5_waybel_0(sK3,sK4),sK4) = iProver_top
% 2.43/0.99      | r1_orders_2(sK3,sK0(sK3,k5_waybel_0(sK3,sK4),sK4),sK4) = iProver_top
% 2.43/0.99      | m1_subset_1(sK0(sK3,k5_waybel_0(sK3,sK4),sK4),u1_struct_0(sK3)) != iProver_top
% 2.43/0.99      | m1_subset_1(sK4,u1_struct_0(sK3)) != iProver_top ),
% 2.43/0.99      inference(instantiation,[status(thm)],[c_5454]) ).
% 2.43/0.99  
% 2.43/0.99  cnf(c_2,plain,
% 2.43/0.99      ( r2_lattice3(X0,X1,X2)
% 2.43/0.99      | ~ r1_orders_2(X0,sK0(X0,X1,X2),X2)
% 2.43/0.99      | ~ m1_subset_1(X2,u1_struct_0(X0))
% 2.43/0.99      | ~ l1_orders_2(X0) ),
% 2.43/0.99      inference(cnf_transformation,[],[f57]) ).
% 2.43/0.99  
% 2.43/0.99  cnf(c_1920,plain,
% 2.43/0.99      ( r2_lattice3(X0,X1,X2)
% 2.43/0.99      | ~ r1_orders_2(X0,sK0(X0,X1,X2),X2)
% 2.43/0.99      | ~ m1_subset_1(X2,u1_struct_0(X0))
% 2.43/0.99      | sK3 != X0 ),
% 2.43/0.99      inference(resolution_lifted,[status(thm)],[c_2,c_32]) ).
% 2.43/0.99  
% 2.43/0.99  cnf(c_1921,plain,
% 2.43/0.99      ( r2_lattice3(sK3,X0,X1)
% 2.43/0.99      | ~ r1_orders_2(sK3,sK0(sK3,X0,X1),X1)
% 2.43/0.99      | ~ m1_subset_1(X1,u1_struct_0(sK3)) ),
% 2.43/0.99      inference(unflattening,[status(thm)],[c_1920]) ).
% 2.43/0.99  
% 2.43/0.99  cnf(c_3797,plain,
% 2.43/0.99      ( r2_lattice3(sK3,X0_55,X1_55)
% 2.43/0.99      | ~ r1_orders_2(sK3,sK0(sK3,X0_55,X1_55),X1_55)
% 2.43/0.99      | ~ m1_subset_1(X1_55,u1_struct_0(sK3)) ),
% 2.43/0.99      inference(subtyping,[status(esa)],[c_1921]) ).
% 2.43/0.99  
% 2.43/0.99  cnf(c_5261,plain,
% 2.43/0.99      ( r2_lattice3(sK3,k5_waybel_0(sK3,sK4),X0_55)
% 2.43/0.99      | ~ r1_orders_2(sK3,sK0(sK3,k5_waybel_0(sK3,sK4),X0_55),X0_55)
% 2.43/0.99      | ~ m1_subset_1(X0_55,u1_struct_0(sK3)) ),
% 2.43/0.99      inference(instantiation,[status(thm)],[c_3797]) ).
% 2.43/0.99  
% 2.43/0.99  cnf(c_5267,plain,
% 2.43/0.99      ( r2_lattice3(sK3,k5_waybel_0(sK3,sK4),X0_55) = iProver_top
% 2.43/0.99      | r1_orders_2(sK3,sK0(sK3,k5_waybel_0(sK3,sK4),X0_55),X0_55) != iProver_top
% 2.43/0.99      | m1_subset_1(X0_55,u1_struct_0(sK3)) != iProver_top ),
% 2.43/0.99      inference(predicate_to_equality,[status(thm)],[c_5261]) ).
% 2.43/0.99  
% 2.43/0.99  cnf(c_5269,plain,
% 2.43/0.99      ( r2_lattice3(sK3,k5_waybel_0(sK3,sK4),sK4) = iProver_top
% 2.43/0.99      | r1_orders_2(sK3,sK0(sK3,k5_waybel_0(sK3,sK4),sK4),sK4) != iProver_top
% 2.43/0.99      | m1_subset_1(sK4,u1_struct_0(sK3)) != iProver_top ),
% 2.43/0.99      inference(instantiation,[status(thm)],[c_5267]) ).
% 2.43/0.99  
% 2.43/0.99  cnf(c_4,plain,
% 2.43/0.99      ( r2_lattice3(X0,X1,X2)
% 2.43/0.99      | ~ m1_subset_1(X2,u1_struct_0(X0))
% 2.43/0.99      | m1_subset_1(sK0(X0,X1,X2),u1_struct_0(X0))
% 2.43/0.99      | ~ l1_orders_2(X0) ),
% 2.43/0.99      inference(cnf_transformation,[],[f55]) ).
% 2.43/0.99  
% 2.43/0.99  cnf(c_1890,plain,
% 2.43/0.99      ( r2_lattice3(X0,X1,X2)
% 2.43/0.99      | ~ m1_subset_1(X2,u1_struct_0(X0))
% 2.43/0.99      | m1_subset_1(sK0(X0,X1,X2),u1_struct_0(X0))
% 2.43/0.99      | sK3 != X0 ),
% 2.43/0.99      inference(resolution_lifted,[status(thm)],[c_4,c_32]) ).
% 2.43/0.99  
% 2.43/0.99  cnf(c_1891,plain,
% 2.43/0.99      ( r2_lattice3(sK3,X0,X1)
% 2.43/0.99      | ~ m1_subset_1(X1,u1_struct_0(sK3))
% 2.43/0.99      | m1_subset_1(sK0(sK3,X0,X1),u1_struct_0(sK3)) ),
% 2.43/0.99      inference(unflattening,[status(thm)],[c_1890]) ).
% 2.43/0.99  
% 2.43/0.99  cnf(c_3799,plain,
% 2.43/0.99      ( r2_lattice3(sK3,X0_55,X1_55)
% 2.43/0.99      | ~ m1_subset_1(X1_55,u1_struct_0(sK3))
% 2.43/0.99      | m1_subset_1(sK0(sK3,X0_55,X1_55),u1_struct_0(sK3)) ),
% 2.43/0.99      inference(subtyping,[status(esa)],[c_1891]) ).
% 2.43/0.99  
% 2.43/0.99  cnf(c_5262,plain,
% 2.43/0.99      ( r2_lattice3(sK3,k5_waybel_0(sK3,sK4),X0_55)
% 2.43/0.99      | ~ m1_subset_1(X0_55,u1_struct_0(sK3))
% 2.43/0.99      | m1_subset_1(sK0(sK3,k5_waybel_0(sK3,sK4),X0_55),u1_struct_0(sK3)) ),
% 2.43/0.99      inference(instantiation,[status(thm)],[c_3799]) ).
% 2.43/0.99  
% 2.43/0.99  cnf(c_5263,plain,
% 2.43/0.99      ( r2_lattice3(sK3,k5_waybel_0(sK3,sK4),X0_55) = iProver_top
% 2.43/0.99      | m1_subset_1(X0_55,u1_struct_0(sK3)) != iProver_top
% 2.43/0.99      | m1_subset_1(sK0(sK3,k5_waybel_0(sK3,sK4),X0_55),u1_struct_0(sK3)) = iProver_top ),
% 2.43/0.99      inference(predicate_to_equality,[status(thm)],[c_5262]) ).
% 2.43/0.99  
% 2.43/0.99  cnf(c_5265,plain,
% 2.43/0.99      ( r2_lattice3(sK3,k5_waybel_0(sK3,sK4),sK4) = iProver_top
% 2.43/0.99      | m1_subset_1(sK0(sK3,k5_waybel_0(sK3,sK4),sK4),u1_struct_0(sK3)) = iProver_top
% 2.43/0.99      | m1_subset_1(sK4,u1_struct_0(sK3)) != iProver_top ),
% 2.43/0.99      inference(instantiation,[status(thm)],[c_5263]) ).
% 2.43/0.99  
% 2.43/0.99  cnf(c_11,plain,
% 2.43/0.99      ( ~ r2_lattice3(X0,X1,X2)
% 2.43/0.99      | r2_lattice3(X0,X1,sK1(X0,X2,X1))
% 2.43/0.99      | ~ m1_subset_1(X2,u1_struct_0(X0))
% 2.43/0.99      | ~ v5_orders_2(X0)
% 2.43/0.99      | ~ l1_orders_2(X0)
% 2.43/0.99      | k1_yellow_0(X0,X1) = X2 ),
% 2.43/0.99      inference(cnf_transformation,[],[f62]) ).
% 2.43/0.99  
% 2.43/0.99  cnf(c_35,negated_conjecture,
% 2.43/0.99      ( v5_orders_2(sK3) ),
% 2.43/0.99      inference(cnf_transformation,[],[f83]) ).
% 2.43/0.99  
% 2.43/0.99  cnf(c_1704,plain,
% 2.43/0.99      ( ~ r2_lattice3(X0,X1,X2)
% 2.43/0.99      | r2_lattice3(X0,X1,sK1(X0,X2,X1))
% 2.43/0.99      | ~ m1_subset_1(X2,u1_struct_0(X0))
% 2.43/0.99      | ~ l1_orders_2(X0)
% 2.43/0.99      | k1_yellow_0(X0,X1) = X2
% 2.43/0.99      | sK3 != X0 ),
% 2.43/0.99      inference(resolution_lifted,[status(thm)],[c_11,c_35]) ).
% 2.43/0.99  
% 2.43/0.99  cnf(c_1705,plain,
% 2.43/0.99      ( ~ r2_lattice3(sK3,X0,X1)
% 2.43/0.99      | r2_lattice3(sK3,X0,sK1(sK3,X1,X0))
% 2.43/0.99      | ~ m1_subset_1(X1,u1_struct_0(sK3))
% 2.43/0.99      | ~ l1_orders_2(sK3)
% 2.43/0.99      | k1_yellow_0(sK3,X0) = X1 ),
% 2.43/0.99      inference(unflattening,[status(thm)],[c_1704]) ).
% 2.43/0.99  
% 2.43/0.99  cnf(c_1709,plain,
% 2.43/0.99      ( ~ m1_subset_1(X1,u1_struct_0(sK3))
% 2.43/0.99      | r2_lattice3(sK3,X0,sK1(sK3,X1,X0))
% 2.43/0.99      | ~ r2_lattice3(sK3,X0,X1)
% 2.43/0.99      | k1_yellow_0(sK3,X0) = X1 ),
% 2.43/0.99      inference(global_propositional_subsumption,
% 2.43/0.99                [status(thm)],
% 2.43/0.99                [c_1705,c_32]) ).
% 2.43/0.99  
% 2.43/0.99  cnf(c_1710,plain,
% 2.43/0.99      ( ~ r2_lattice3(sK3,X0,X1)
% 2.43/0.99      | r2_lattice3(sK3,X0,sK1(sK3,X1,X0))
% 2.43/0.99      | ~ m1_subset_1(X1,u1_struct_0(sK3))
% 2.43/0.99      | k1_yellow_0(sK3,X0) = X1 ),
% 2.43/0.99      inference(renaming,[status(thm)],[c_1709]) ).
% 2.43/0.99  
% 2.43/0.99  cnf(c_3806,plain,
% 2.43/0.99      ( ~ r2_lattice3(sK3,X0_55,X1_55)
% 2.43/0.99      | r2_lattice3(sK3,X0_55,sK1(sK3,X1_55,X0_55))
% 2.43/0.99      | ~ m1_subset_1(X1_55,u1_struct_0(sK3))
% 2.43/0.99      | k1_yellow_0(sK3,X0_55) = X1_55 ),
% 2.43/0.99      inference(subtyping,[status(esa)],[c_1710]) ).
% 2.43/0.99  
% 2.43/0.99  cnf(c_5054,plain,
% 2.43/0.99      ( ~ r2_lattice3(sK3,k5_waybel_0(sK3,sK4),X0_55)
% 2.43/0.99      | r2_lattice3(sK3,k5_waybel_0(sK3,sK4),sK1(sK3,X0_55,k5_waybel_0(sK3,sK4)))
% 2.43/0.99      | ~ m1_subset_1(X0_55,u1_struct_0(sK3))
% 2.43/0.99      | k1_yellow_0(sK3,k5_waybel_0(sK3,sK4)) = X0_55 ),
% 2.43/0.99      inference(instantiation,[status(thm)],[c_3806]) ).
% 2.43/0.99  
% 2.43/0.99  cnf(c_5065,plain,
% 2.43/0.99      ( k1_yellow_0(sK3,k5_waybel_0(sK3,sK4)) = X0_55
% 2.43/0.99      | r2_lattice3(sK3,k5_waybel_0(sK3,sK4),X0_55) != iProver_top
% 2.43/0.99      | r2_lattice3(sK3,k5_waybel_0(sK3,sK4),sK1(sK3,X0_55,k5_waybel_0(sK3,sK4))) = iProver_top
% 2.43/0.99      | m1_subset_1(X0_55,u1_struct_0(sK3)) != iProver_top ),
% 2.43/0.99      inference(predicate_to_equality,[status(thm)],[c_5054]) ).
% 2.43/0.99  
% 2.43/0.99  cnf(c_5067,plain,
% 2.43/0.99      ( k1_yellow_0(sK3,k5_waybel_0(sK3,sK4)) = sK4
% 2.43/0.99      | r2_lattice3(sK3,k5_waybel_0(sK3,sK4),sK1(sK3,sK4,k5_waybel_0(sK3,sK4))) = iProver_top
% 2.43/0.99      | r2_lattice3(sK3,k5_waybel_0(sK3,sK4),sK4) != iProver_top
% 2.43/0.99      | m1_subset_1(sK4,u1_struct_0(sK3)) != iProver_top ),
% 2.43/0.99      inference(instantiation,[status(thm)],[c_5065]) ).
% 2.43/0.99  
% 2.43/0.99  cnf(c_10,plain,
% 2.43/0.99      ( ~ r2_lattice3(X0,X1,X2)
% 2.43/0.99      | ~ r1_orders_2(X0,X2,sK1(X0,X2,X1))
% 2.43/0.99      | ~ m1_subset_1(X2,u1_struct_0(X0))
% 2.43/0.99      | ~ v5_orders_2(X0)
% 2.43/0.99      | ~ l1_orders_2(X0)
% 2.43/0.99      | k1_yellow_0(X0,X1) = X2 ),
% 2.43/0.99      inference(cnf_transformation,[],[f63]) ).
% 2.43/0.99  
% 2.43/0.99  cnf(c_1728,plain,
% 2.43/0.99      ( ~ r2_lattice3(X0,X1,X2)
% 2.43/0.99      | ~ r1_orders_2(X0,X2,sK1(X0,X2,X1))
% 2.43/0.99      | ~ m1_subset_1(X2,u1_struct_0(X0))
% 2.43/0.99      | ~ l1_orders_2(X0)
% 2.43/0.99      | k1_yellow_0(X0,X1) = X2
% 2.43/0.99      | sK3 != X0 ),
% 2.43/0.99      inference(resolution_lifted,[status(thm)],[c_10,c_35]) ).
% 2.43/0.99  
% 2.43/0.99  cnf(c_1729,plain,
% 2.43/0.99      ( ~ r2_lattice3(sK3,X0,X1)
% 2.43/0.99      | ~ r1_orders_2(sK3,X1,sK1(sK3,X1,X0))
% 2.43/0.99      | ~ m1_subset_1(X1,u1_struct_0(sK3))
% 2.43/0.99      | ~ l1_orders_2(sK3)
% 2.43/0.99      | k1_yellow_0(sK3,X0) = X1 ),
% 2.43/0.99      inference(unflattening,[status(thm)],[c_1728]) ).
% 2.43/0.99  
% 2.43/0.99  cnf(c_1733,plain,
% 2.43/0.99      ( ~ m1_subset_1(X1,u1_struct_0(sK3))
% 2.43/0.99      | ~ r1_orders_2(sK3,X1,sK1(sK3,X1,X0))
% 2.43/0.99      | ~ r2_lattice3(sK3,X0,X1)
% 2.43/0.99      | k1_yellow_0(sK3,X0) = X1 ),
% 2.43/0.99      inference(global_propositional_subsumption,
% 2.43/0.99                [status(thm)],
% 2.43/0.99                [c_1729,c_32]) ).
% 2.43/0.99  
% 2.43/0.99  cnf(c_1734,plain,
% 2.43/0.99      ( ~ r2_lattice3(sK3,X0,X1)
% 2.43/0.99      | ~ r1_orders_2(sK3,X1,sK1(sK3,X1,X0))
% 2.43/0.99      | ~ m1_subset_1(X1,u1_struct_0(sK3))
% 2.43/0.99      | k1_yellow_0(sK3,X0) = X1 ),
% 2.43/0.99      inference(renaming,[status(thm)],[c_1733]) ).
% 2.43/0.99  
% 2.43/0.99  cnf(c_3805,plain,
% 2.43/0.99      ( ~ r2_lattice3(sK3,X0_55,X1_55)
% 2.43/0.99      | ~ r1_orders_2(sK3,X1_55,sK1(sK3,X1_55,X0_55))
% 2.43/0.99      | ~ m1_subset_1(X1_55,u1_struct_0(sK3))
% 2.43/0.99      | k1_yellow_0(sK3,X0_55) = X1_55 ),
% 2.43/0.99      inference(subtyping,[status(esa)],[c_1734]) ).
% 2.43/0.99  
% 2.43/0.99  cnf(c_5055,plain,
% 2.43/0.99      ( ~ r2_lattice3(sK3,k5_waybel_0(sK3,sK4),X0_55)
% 2.43/0.99      | ~ r1_orders_2(sK3,X0_55,sK1(sK3,X0_55,k5_waybel_0(sK3,sK4)))
% 2.43/0.99      | ~ m1_subset_1(X0_55,u1_struct_0(sK3))
% 2.43/0.99      | k1_yellow_0(sK3,k5_waybel_0(sK3,sK4)) = X0_55 ),
% 2.43/0.99      inference(instantiation,[status(thm)],[c_3805]) ).
% 2.43/0.99  
% 2.43/0.99  cnf(c_5061,plain,
% 2.43/0.99      ( k1_yellow_0(sK3,k5_waybel_0(sK3,sK4)) = X0_55
% 2.43/0.99      | r2_lattice3(sK3,k5_waybel_0(sK3,sK4),X0_55) != iProver_top
% 2.43/0.99      | r1_orders_2(sK3,X0_55,sK1(sK3,X0_55,k5_waybel_0(sK3,sK4))) != iProver_top
% 2.43/0.99      | m1_subset_1(X0_55,u1_struct_0(sK3)) != iProver_top ),
% 2.43/0.99      inference(predicate_to_equality,[status(thm)],[c_5055]) ).
% 2.43/0.99  
% 2.43/0.99  cnf(c_5063,plain,
% 2.43/0.99      ( k1_yellow_0(sK3,k5_waybel_0(sK3,sK4)) = sK4
% 2.43/0.99      | r2_lattice3(sK3,k5_waybel_0(sK3,sK4),sK4) != iProver_top
% 2.43/0.99      | r1_orders_2(sK3,sK4,sK1(sK3,sK4,k5_waybel_0(sK3,sK4))) != iProver_top
% 2.43/0.99      | m1_subset_1(sK4,u1_struct_0(sK3)) != iProver_top ),
% 2.43/0.99      inference(instantiation,[status(thm)],[c_5061]) ).
% 2.43/0.99  
% 2.43/0.99  cnf(c_12,plain,
% 2.43/0.99      ( ~ r2_lattice3(X0,X1,X2)
% 2.43/0.99      | ~ m1_subset_1(X2,u1_struct_0(X0))
% 2.43/0.99      | m1_subset_1(sK1(X0,X2,X1),u1_struct_0(X0))
% 2.43/0.99      | ~ v5_orders_2(X0)
% 2.43/0.99      | ~ l1_orders_2(X0)
% 2.43/0.99      | k1_yellow_0(X0,X1) = X2 ),
% 2.43/0.99      inference(cnf_transformation,[],[f61]) ).
% 2.43/0.99  
% 2.43/0.99  cnf(c_1680,plain,
% 2.43/0.99      ( ~ r2_lattice3(X0,X1,X2)
% 2.43/0.99      | ~ m1_subset_1(X2,u1_struct_0(X0))
% 2.43/0.99      | m1_subset_1(sK1(X0,X2,X1),u1_struct_0(X0))
% 2.43/0.99      | ~ l1_orders_2(X0)
% 2.43/0.99      | k1_yellow_0(X0,X1) = X2
% 2.43/0.99      | sK3 != X0 ),
% 2.43/0.99      inference(resolution_lifted,[status(thm)],[c_12,c_35]) ).
% 2.43/0.99  
% 2.43/0.99  cnf(c_1681,plain,
% 2.43/0.99      ( ~ r2_lattice3(sK3,X0,X1)
% 2.43/0.99      | ~ m1_subset_1(X1,u1_struct_0(sK3))
% 2.43/0.99      | m1_subset_1(sK1(sK3,X1,X0),u1_struct_0(sK3))
% 2.43/0.99      | ~ l1_orders_2(sK3)
% 2.43/0.99      | k1_yellow_0(sK3,X0) = X1 ),
% 2.43/0.99      inference(unflattening,[status(thm)],[c_1680]) ).
% 2.43/0.99  
% 2.43/0.99  cnf(c_1685,plain,
% 2.43/0.99      ( m1_subset_1(sK1(sK3,X1,X0),u1_struct_0(sK3))
% 2.43/0.99      | ~ m1_subset_1(X1,u1_struct_0(sK3))
% 2.43/0.99      | ~ r2_lattice3(sK3,X0,X1)
% 2.43/0.99      | k1_yellow_0(sK3,X0) = X1 ),
% 2.43/0.99      inference(global_propositional_subsumption,
% 2.43/0.99                [status(thm)],
% 2.43/0.99                [c_1681,c_32]) ).
% 2.43/0.99  
% 2.43/0.99  cnf(c_1686,plain,
% 2.43/0.99      ( ~ r2_lattice3(sK3,X0,X1)
% 2.43/0.99      | ~ m1_subset_1(X1,u1_struct_0(sK3))
% 2.43/0.99      | m1_subset_1(sK1(sK3,X1,X0),u1_struct_0(sK3))
% 2.43/0.99      | k1_yellow_0(sK3,X0) = X1 ),
% 2.43/0.99      inference(renaming,[status(thm)],[c_1685]) ).
% 2.43/0.99  
% 2.43/0.99  cnf(c_3807,plain,
% 2.43/0.99      ( ~ r2_lattice3(sK3,X0_55,X1_55)
% 2.43/0.99      | ~ m1_subset_1(X1_55,u1_struct_0(sK3))
% 2.43/0.99      | m1_subset_1(sK1(sK3,X1_55,X0_55),u1_struct_0(sK3))
% 2.43/0.99      | k1_yellow_0(sK3,X0_55) = X1_55 ),
% 2.43/0.99      inference(subtyping,[status(esa)],[c_1686]) ).
% 2.43/0.99  
% 2.43/0.99  cnf(c_5056,plain,
% 2.43/0.99      ( ~ r2_lattice3(sK3,k5_waybel_0(sK3,sK4),X0_55)
% 2.43/0.99      | ~ m1_subset_1(X0_55,u1_struct_0(sK3))
% 2.43/0.99      | m1_subset_1(sK1(sK3,X0_55,k5_waybel_0(sK3,sK4)),u1_struct_0(sK3))
% 2.43/0.99      | k1_yellow_0(sK3,k5_waybel_0(sK3,sK4)) = X0_55 ),
% 2.43/0.99      inference(instantiation,[status(thm)],[c_3807]) ).
% 2.43/0.99  
% 2.43/0.99  cnf(c_5057,plain,
% 2.43/0.99      ( k1_yellow_0(sK3,k5_waybel_0(sK3,sK4)) = X0_55
% 2.43/0.99      | r2_lattice3(sK3,k5_waybel_0(sK3,sK4),X0_55) != iProver_top
% 2.43/0.99      | m1_subset_1(X0_55,u1_struct_0(sK3)) != iProver_top
% 2.43/0.99      | m1_subset_1(sK1(sK3,X0_55,k5_waybel_0(sK3,sK4)),u1_struct_0(sK3)) = iProver_top ),
% 2.43/0.99      inference(predicate_to_equality,[status(thm)],[c_5056]) ).
% 2.43/0.99  
% 2.43/0.99  cnf(c_5059,plain,
% 2.43/0.99      ( k1_yellow_0(sK3,k5_waybel_0(sK3,sK4)) = sK4
% 2.43/0.99      | r2_lattice3(sK3,k5_waybel_0(sK3,sK4),sK4) != iProver_top
% 2.43/0.99      | m1_subset_1(sK1(sK3,sK4,k5_waybel_0(sK3,sK4)),u1_struct_0(sK3)) = iProver_top
% 2.43/0.99      | m1_subset_1(sK4,u1_struct_0(sK3)) != iProver_top ),
% 2.43/0.99      inference(instantiation,[status(thm)],[c_5057]) ).
% 2.43/0.99  
% 2.43/0.99  cnf(c_3829,plain,
% 2.43/0.99      ( X0_55 != X1_55 | X2_55 != X1_55 | X2_55 = X0_55 ),
% 2.43/0.99      theory(equality) ).
% 2.43/0.99  
% 2.43/0.99  cnf(c_4767,plain,
% 2.43/0.99      ( X0_55 != X1_55
% 2.43/0.99      | X0_55 = k1_yellow_0(sK3,k5_waybel_0(sK3,sK4))
% 2.43/0.99      | k1_yellow_0(sK3,k5_waybel_0(sK3,sK4)) != X1_55 ),
% 2.43/0.99      inference(instantiation,[status(thm)],[c_3829]) ).
% 2.43/0.99  
% 2.43/0.99  cnf(c_4768,plain,
% 2.43/0.99      ( k1_yellow_0(sK3,k5_waybel_0(sK3,sK4)) != sK4
% 2.43/0.99      | sK4 = k1_yellow_0(sK3,k5_waybel_0(sK3,sK4))
% 2.43/0.99      | sK4 != sK4 ),
% 2.43/0.99      inference(instantiation,[status(thm)],[c_4767]) ).
% 2.43/0.99  
% 2.43/0.99  cnf(c_3838,plain,
% 2.43/0.99      ( ~ v4_waybel_7(X0_55,X0_56)
% 2.43/0.99      | v4_waybel_7(X1_55,X0_56)
% 2.43/0.99      | X1_55 != X0_55 ),
% 2.43/0.99      theory(equality) ).
% 2.43/0.99  
% 2.43/0.99  cnf(c_4659,plain,
% 2.43/0.99      ( v4_waybel_7(X0_55,sK3)
% 2.43/0.99      | ~ v4_waybel_7(k1_yellow_0(sK3,k5_waybel_0(sK3,sK4)),sK3)
% 2.43/0.99      | X0_55 != k1_yellow_0(sK3,k5_waybel_0(sK3,sK4)) ),
% 2.43/0.99      inference(instantiation,[status(thm)],[c_3838]) ).
% 2.43/0.99  
% 2.43/0.99  cnf(c_4661,plain,
% 2.43/0.99      ( ~ v4_waybel_7(k1_yellow_0(sK3,k5_waybel_0(sK3,sK4)),sK3)
% 2.43/0.99      | v4_waybel_7(sK4,sK3)
% 2.43/0.99      | sK4 != k1_yellow_0(sK3,k5_waybel_0(sK3,sK4)) ),
% 2.43/0.99      inference(instantiation,[status(thm)],[c_4659]) ).
% 2.43/0.99  
% 2.43/0.99  cnf(c_6,plain,
% 2.43/0.99      ( m1_subset_1(k1_yellow_0(X0,X1),u1_struct_0(X0))
% 2.43/0.99      | ~ l1_orders_2(X0) ),
% 2.43/0.99      inference(cnf_transformation,[],[f58]) ).
% 2.43/0.99  
% 2.43/0.99  cnf(c_1862,plain,
% 2.43/0.99      ( m1_subset_1(k1_yellow_0(X0,X1),u1_struct_0(X0)) | sK3 != X0 ),
% 2.43/0.99      inference(resolution_lifted,[status(thm)],[c_6,c_32]) ).
% 2.43/0.99  
% 2.43/0.99  cnf(c_1863,plain,
% 2.43/0.99      ( m1_subset_1(k1_yellow_0(sK3,X0),u1_struct_0(sK3)) ),
% 2.43/0.99      inference(unflattening,[status(thm)],[c_1862]) ).
% 2.43/0.99  
% 2.43/0.99  cnf(c_16,plain,
% 2.43/0.99      ( v12_waybel_0(k5_waybel_0(X0,X1),X0)
% 2.43/0.99      | ~ m1_subset_1(X1,u1_struct_0(X0))
% 2.43/0.99      | ~ v4_orders_2(X0)
% 2.43/0.99      | v2_struct_0(X0)
% 2.43/0.99      | ~ l1_orders_2(X0) ),
% 2.43/0.99      inference(cnf_transformation,[],[f68]) ).
% 2.43/0.99  
% 2.43/0.99  cnf(c_21,plain,
% 2.43/0.99      ( ~ v1_waybel_7(X0,X1)
% 2.43/0.99      | v4_waybel_7(k1_yellow_0(X1,X0),X1)
% 2.43/0.99      | ~ v1_waybel_0(X0,X1)
% 2.43/0.99      | ~ v12_waybel_0(X0,X1)
% 2.43/0.99      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 2.43/0.99      | ~ m1_subset_1(k1_yellow_0(X1,X0),u1_struct_0(X1))
% 2.43/0.99      | ~ v2_lattice3(X1)
% 2.43/0.99      | v1_xboole_0(X0)
% 2.43/0.99      | ~ v4_orders_2(X1)
% 2.43/0.99      | ~ v5_orders_2(X1)
% 2.43/0.99      | ~ v1_lattice3(X1)
% 2.43/0.99      | ~ v3_orders_2(X1)
% 2.43/0.99      | ~ l1_orders_2(X1) ),
% 2.43/0.99      inference(cnf_transformation,[],[f92]) ).
% 2.43/0.99  
% 2.43/0.99  cnf(c_28,plain,
% 2.43/0.99      ( ~ v5_waybel_6(X0,X1)
% 2.43/0.99      | v1_waybel_7(k5_waybel_0(X1,X0),X1)
% 2.43/0.99      | ~ m1_subset_1(X0,u1_struct_0(X1))
% 2.43/0.99      | ~ v2_lattice3(X1)
% 2.43/0.99      | ~ v4_orders_2(X1)
% 2.43/0.99      | ~ v5_orders_2(X1)
% 2.43/0.99      | ~ v1_lattice3(X1)
% 2.43/0.99      | ~ v3_orders_2(X1)
% 2.43/0.99      | ~ l1_orders_2(X1) ),
% 2.43/0.99      inference(cnf_transformation,[],[f80]) ).
% 2.43/0.99  
% 2.43/0.99  cnf(c_30,negated_conjecture,
% 2.43/0.99      ( v5_waybel_6(sK4,sK3) ),
% 2.43/0.99      inference(cnf_transformation,[],[f88]) ).
% 2.43/0.99  
% 2.43/0.99  cnf(c_435,plain,
% 2.43/0.99      ( v1_waybel_7(k5_waybel_0(X0,X1),X0)
% 2.43/0.99      | ~ m1_subset_1(X1,u1_struct_0(X0))
% 2.43/0.99      | ~ v2_lattice3(X0)
% 2.43/0.99      | ~ v4_orders_2(X0)
% 2.43/0.99      | ~ v5_orders_2(X0)
% 2.43/0.99      | ~ v1_lattice3(X0)
% 2.43/0.99      | ~ v3_orders_2(X0)
% 2.43/0.99      | ~ l1_orders_2(X0)
% 2.43/0.99      | sK3 != X0
% 2.43/0.99      | sK4 != X1 ),
% 2.43/0.99      inference(resolution_lifted,[status(thm)],[c_28,c_30]) ).
% 2.43/0.99  
% 2.43/0.99  cnf(c_436,plain,
% 2.43/0.99      ( v1_waybel_7(k5_waybel_0(sK3,sK4),sK3)
% 2.43/0.99      | ~ m1_subset_1(sK4,u1_struct_0(sK3))
% 2.43/0.99      | ~ v2_lattice3(sK3)
% 2.43/0.99      | ~ v4_orders_2(sK3)
% 2.43/0.99      | ~ v5_orders_2(sK3)
% 2.43/0.99      | ~ v1_lattice3(sK3)
% 2.43/0.99      | ~ v3_orders_2(sK3)
% 2.43/0.99      | ~ l1_orders_2(sK3) ),
% 2.43/0.99      inference(unflattening,[status(thm)],[c_435]) ).
% 2.43/0.99  
% 2.43/0.99  cnf(c_37,negated_conjecture,
% 2.43/0.99      ( v3_orders_2(sK3) ),
% 2.43/0.99      inference(cnf_transformation,[],[f81]) ).
% 2.43/0.99  
% 2.43/0.99  cnf(c_36,negated_conjecture,
% 2.43/0.99      ( v4_orders_2(sK3) ),
% 2.43/0.99      inference(cnf_transformation,[],[f82]) ).
% 2.43/0.99  
% 2.43/0.99  cnf(c_33,negated_conjecture,
% 2.43/0.99      ( v2_lattice3(sK3) ),
% 2.43/0.99      inference(cnf_transformation,[],[f85]) ).
% 2.43/0.99  
% 2.43/0.99  cnf(c_31,negated_conjecture,
% 2.43/0.99      ( m1_subset_1(sK4,u1_struct_0(sK3)) ),
% 2.43/0.99      inference(cnf_transformation,[],[f87]) ).
% 2.43/0.99  
% 2.43/0.99  cnf(c_438,plain,
% 2.43/0.99      ( v1_waybel_7(k5_waybel_0(sK3,sK4),sK3) ),
% 2.43/0.99      inference(global_propositional_subsumption,
% 2.43/0.99                [status(thm)],
% 2.43/0.99                [c_436,c_37,c_36,c_35,c_34,c_33,c_32,c_31]) ).
% 2.43/0.99  
% 2.43/0.99  cnf(c_492,plain,
% 2.43/0.99      ( v4_waybel_7(k1_yellow_0(X0,X1),X0)
% 2.43/0.99      | ~ v1_waybel_0(X1,X0)
% 2.43/0.99      | ~ v12_waybel_0(X1,X0)
% 2.43/0.99      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
% 2.43/0.99      | ~ m1_subset_1(k1_yellow_0(X0,X1),u1_struct_0(X0))
% 2.43/0.99      | ~ v2_lattice3(X0)
% 2.43/0.99      | v1_xboole_0(X1)
% 2.43/0.99      | ~ v4_orders_2(X0)
% 2.43/0.99      | ~ v5_orders_2(X0)
% 2.43/0.99      | ~ v1_lattice3(X0)
% 2.43/0.99      | ~ v3_orders_2(X0)
% 2.43/0.99      | ~ l1_orders_2(X0)
% 2.43/0.99      | k5_waybel_0(sK3,sK4) != X1
% 2.43/0.99      | sK3 != X0 ),
% 2.43/0.99      inference(resolution_lifted,[status(thm)],[c_21,c_438]) ).
% 2.43/0.99  
% 2.43/0.99  cnf(c_493,plain,
% 2.43/0.99      ( v4_waybel_7(k1_yellow_0(sK3,k5_waybel_0(sK3,sK4)),sK3)
% 2.43/0.99      | ~ v1_waybel_0(k5_waybel_0(sK3,sK4),sK3)
% 2.43/0.99      | ~ v12_waybel_0(k5_waybel_0(sK3,sK4),sK3)
% 2.43/0.99      | ~ m1_subset_1(k5_waybel_0(sK3,sK4),k1_zfmisc_1(u1_struct_0(sK3)))
% 2.43/0.99      | ~ m1_subset_1(k1_yellow_0(sK3,k5_waybel_0(sK3,sK4)),u1_struct_0(sK3))
% 2.43/0.99      | ~ v2_lattice3(sK3)
% 2.43/0.99      | v1_xboole_0(k5_waybel_0(sK3,sK4))
% 2.43/0.99      | ~ v4_orders_2(sK3)
% 2.43/0.99      | ~ v5_orders_2(sK3)
% 2.43/0.99      | ~ v1_lattice3(sK3)
% 2.43/0.99      | ~ v3_orders_2(sK3)
% 2.43/0.99      | ~ l1_orders_2(sK3) ),
% 2.43/0.99      inference(unflattening,[status(thm)],[c_492]) ).
% 2.43/0.99  
% 2.43/0.99  cnf(c_495,plain,
% 2.43/0.99      ( v1_xboole_0(k5_waybel_0(sK3,sK4))
% 2.43/0.99      | v4_waybel_7(k1_yellow_0(sK3,k5_waybel_0(sK3,sK4)),sK3)
% 2.43/0.99      | ~ v1_waybel_0(k5_waybel_0(sK3,sK4),sK3)
% 2.43/0.99      | ~ v12_waybel_0(k5_waybel_0(sK3,sK4),sK3)
% 2.43/0.99      | ~ m1_subset_1(k5_waybel_0(sK3,sK4),k1_zfmisc_1(u1_struct_0(sK3)))
% 2.43/0.99      | ~ m1_subset_1(k1_yellow_0(sK3,k5_waybel_0(sK3,sK4)),u1_struct_0(sK3)) ),
% 2.43/0.99      inference(global_propositional_subsumption,
% 2.43/0.99                [status(thm)],
% 2.43/0.99                [c_493,c_37,c_36,c_35,c_34,c_33,c_32]) ).
% 2.43/0.99  
% 2.43/0.99  cnf(c_496,plain,
% 2.43/0.99      ( v4_waybel_7(k1_yellow_0(sK3,k5_waybel_0(sK3,sK4)),sK3)
% 2.43/0.99      | ~ v1_waybel_0(k5_waybel_0(sK3,sK4),sK3)
% 2.43/0.99      | ~ v12_waybel_0(k5_waybel_0(sK3,sK4),sK3)
% 2.43/0.99      | ~ m1_subset_1(k5_waybel_0(sK3,sK4),k1_zfmisc_1(u1_struct_0(sK3)))
% 2.43/0.99      | ~ m1_subset_1(k1_yellow_0(sK3,k5_waybel_0(sK3,sK4)),u1_struct_0(sK3))
% 2.43/0.99      | v1_xboole_0(k5_waybel_0(sK3,sK4)) ),
% 2.43/0.99      inference(renaming,[status(thm)],[c_495]) ).
% 2.43/0.99  
% 2.43/0.99  cnf(c_535,plain,
% 2.43/0.99      ( v4_waybel_7(k1_yellow_0(sK3,k5_waybel_0(sK3,sK4)),sK3)
% 2.43/0.99      | ~ v1_waybel_0(k5_waybel_0(sK3,sK4),sK3)
% 2.43/0.99      | ~ m1_subset_1(X0,u1_struct_0(X1))
% 2.43/0.99      | ~ m1_subset_1(k5_waybel_0(sK3,sK4),k1_zfmisc_1(u1_struct_0(sK3)))
% 2.43/0.99      | ~ m1_subset_1(k1_yellow_0(sK3,k5_waybel_0(sK3,sK4)),u1_struct_0(sK3))
% 2.43/0.99      | v1_xboole_0(k5_waybel_0(sK3,sK4))
% 2.43/0.99      | ~ v4_orders_2(X1)
% 2.43/0.99      | v2_struct_0(X1)
% 2.43/0.99      | ~ l1_orders_2(X1)
% 2.43/0.99      | k5_waybel_0(X1,X0) != k5_waybel_0(sK3,sK4)
% 2.43/0.99      | sK3 != X1 ),
% 2.43/0.99      inference(resolution_lifted,[status(thm)],[c_16,c_496]) ).
% 2.43/0.99  
% 2.43/0.99  cnf(c_536,plain,
% 2.43/0.99      ( v4_waybel_7(k1_yellow_0(sK3,k5_waybel_0(sK3,sK4)),sK3)
% 2.43/0.99      | ~ v1_waybel_0(k5_waybel_0(sK3,sK4),sK3)
% 2.43/0.99      | ~ m1_subset_1(X0,u1_struct_0(sK3))
% 2.43/0.99      | ~ m1_subset_1(k5_waybel_0(sK3,sK4),k1_zfmisc_1(u1_struct_0(sK3)))
% 2.43/0.99      | ~ m1_subset_1(k1_yellow_0(sK3,k5_waybel_0(sK3,sK4)),u1_struct_0(sK3))
% 2.43/0.99      | v1_xboole_0(k5_waybel_0(sK3,sK4))
% 2.43/0.99      | ~ v4_orders_2(sK3)
% 2.43/0.99      | v2_struct_0(sK3)
% 2.43/0.99      | ~ l1_orders_2(sK3)
% 2.43/0.99      | k5_waybel_0(sK3,X0) != k5_waybel_0(sK3,sK4) ),
% 2.43/0.99      inference(unflattening,[status(thm)],[c_535]) ).
% 2.43/0.99  
% 2.43/0.99  cnf(c_129,plain,
% 2.43/0.99      ( ~ v1_lattice3(sK3) | ~ v2_struct_0(sK3) | ~ l1_orders_2(sK3) ),
% 2.43/0.99      inference(instantiation,[status(thm)],[c_1]) ).
% 2.43/0.99  
% 2.43/0.99  cnf(c_540,plain,
% 2.43/0.99      ( v1_xboole_0(k5_waybel_0(sK3,sK4))
% 2.43/0.99      | ~ m1_subset_1(k1_yellow_0(sK3,k5_waybel_0(sK3,sK4)),u1_struct_0(sK3))
% 2.43/0.99      | ~ m1_subset_1(k5_waybel_0(sK3,sK4),k1_zfmisc_1(u1_struct_0(sK3)))
% 2.43/0.99      | ~ m1_subset_1(X0,u1_struct_0(sK3))
% 2.43/0.99      | ~ v1_waybel_0(k5_waybel_0(sK3,sK4),sK3)
% 2.43/0.99      | v4_waybel_7(k1_yellow_0(sK3,k5_waybel_0(sK3,sK4)),sK3)
% 2.43/0.99      | k5_waybel_0(sK3,X0) != k5_waybel_0(sK3,sK4) ),
% 2.43/0.99      inference(global_propositional_subsumption,
% 2.43/0.99                [status(thm)],
% 2.43/0.99                [c_536,c_36,c_34,c_32,c_129]) ).
% 2.43/0.99  
% 2.43/0.99  cnf(c_541,plain,
% 2.43/0.99      ( v4_waybel_7(k1_yellow_0(sK3,k5_waybel_0(sK3,sK4)),sK3)
% 2.43/0.99      | ~ v1_waybel_0(k5_waybel_0(sK3,sK4),sK3)
% 2.43/0.99      | ~ m1_subset_1(X0,u1_struct_0(sK3))
% 2.43/0.99      | ~ m1_subset_1(k5_waybel_0(sK3,sK4),k1_zfmisc_1(u1_struct_0(sK3)))
% 2.43/0.99      | ~ m1_subset_1(k1_yellow_0(sK3,k5_waybel_0(sK3,sK4)),u1_struct_0(sK3))
% 2.43/0.99      | v1_xboole_0(k5_waybel_0(sK3,sK4))
% 2.43/0.99      | k5_waybel_0(sK3,X0) != k5_waybel_0(sK3,sK4) ),
% 2.43/0.99      inference(renaming,[status(thm)],[c_540]) ).
% 2.43/0.99  
% 2.43/0.99  cnf(c_1936,plain,
% 2.43/0.99      ( v4_waybel_7(k1_yellow_0(sK3,k5_waybel_0(sK3,sK4)),sK3)
% 2.43/0.99      | ~ v1_waybel_0(k5_waybel_0(sK3,sK4),sK3)
% 2.43/0.99      | ~ m1_subset_1(X0,u1_struct_0(sK3))
% 2.43/0.99      | ~ m1_subset_1(k5_waybel_0(sK3,sK4),k1_zfmisc_1(u1_struct_0(sK3)))
% 2.43/0.99      | v1_xboole_0(k5_waybel_0(sK3,sK4))
% 2.43/0.99      | k5_waybel_0(sK3,X0) != k5_waybel_0(sK3,sK4) ),
% 2.43/0.99      inference(backward_subsumption_resolution,
% 2.43/0.99                [status(thm)],
% 2.43/0.99                [c_1863,c_541]) ).
% 2.43/0.99  
% 2.43/0.99  cnf(c_3796,plain,
% 2.43/0.99      ( v4_waybel_7(k1_yellow_0(sK3,k5_waybel_0(sK3,sK4)),sK3)
% 2.43/0.99      | ~ v1_waybel_0(k5_waybel_0(sK3,sK4),sK3)
% 2.43/0.99      | ~ m1_subset_1(X0_55,u1_struct_0(sK3))
% 2.43/0.99      | ~ m1_subset_1(k5_waybel_0(sK3,sK4),k1_zfmisc_1(u1_struct_0(sK3)))
% 2.43/0.99      | v1_xboole_0(k5_waybel_0(sK3,sK4))
% 2.43/0.99      | k5_waybel_0(sK3,X0_55) != k5_waybel_0(sK3,sK4) ),
% 2.43/0.99      inference(subtyping,[status(esa)],[c_1936]) ).
% 2.43/0.99  
% 2.43/0.99  cnf(c_3823,plain,
% 2.43/0.99      ( ~ m1_subset_1(X0_55,u1_struct_0(sK3))
% 2.43/0.99      | k5_waybel_0(sK3,X0_55) != k5_waybel_0(sK3,sK4)
% 2.43/0.99      | ~ sP0_iProver_split ),
% 2.43/0.99      inference(splitting,
% 2.43/0.99                [splitting(split),new_symbols(definition,[sP0_iProver_split])],
% 2.43/0.99                [c_3796]) ).
% 2.43/0.99  
% 2.43/0.99  cnf(c_3912,plain,
% 2.43/0.99      ( ~ m1_subset_1(sK4,u1_struct_0(sK3))
% 2.43/0.99      | ~ sP0_iProver_split
% 2.43/0.99      | k5_waybel_0(sK3,sK4) != k5_waybel_0(sK3,sK4) ),
% 2.43/0.99      inference(instantiation,[status(thm)],[c_3823]) ).
% 2.43/0.99  
% 2.43/0.99  cnf(c_3824,plain,
% 2.43/0.99      ( v4_waybel_7(k1_yellow_0(sK3,k5_waybel_0(sK3,sK4)),sK3)
% 2.43/0.99      | ~ v1_waybel_0(k5_waybel_0(sK3,sK4),sK3)
% 2.43/0.99      | ~ m1_subset_1(k5_waybel_0(sK3,sK4),k1_zfmisc_1(u1_struct_0(sK3)))
% 2.43/0.99      | v1_xboole_0(k5_waybel_0(sK3,sK4))
% 2.43/0.99      | sP0_iProver_split ),
% 2.43/0.99      inference(splitting,
% 2.43/0.99                [splitting(split),new_symbols(definition,[])],
% 2.43/0.99                [c_3796]) ).
% 2.43/0.99  
% 2.43/0.99  cnf(c_15,plain,
% 2.43/0.99      ( ~ m1_subset_1(X0,u1_struct_0(X1))
% 2.43/0.99      | m1_subset_1(k5_waybel_0(X1,X0),k1_zfmisc_1(u1_struct_0(X1)))
% 2.43/0.99      | v2_struct_0(X1)
% 2.43/0.99      | ~ l1_orders_2(X1) ),
% 2.43/0.99      inference(cnf_transformation,[],[f67]) ).
% 2.43/0.99  
% 2.43/0.99  cnf(c_847,plain,
% 2.43/0.99      ( ~ m1_subset_1(X0,u1_struct_0(X1))
% 2.43/0.99      | m1_subset_1(k5_waybel_0(X1,X0),k1_zfmisc_1(u1_struct_0(X1)))
% 2.43/0.99      | ~ v1_lattice3(X2)
% 2.43/0.99      | ~ l1_orders_2(X2)
% 2.43/0.99      | ~ l1_orders_2(X1)
% 2.43/0.99      | X1 != X2 ),
% 2.43/0.99      inference(resolution_lifted,[status(thm)],[c_1,c_15]) ).
% 2.43/0.99  
% 2.43/0.99  cnf(c_848,plain,
% 2.43/0.99      ( ~ m1_subset_1(X0,u1_struct_0(X1))
% 2.43/0.99      | m1_subset_1(k5_waybel_0(X1,X0),k1_zfmisc_1(u1_struct_0(X1)))
% 2.43/0.99      | ~ v1_lattice3(X1)
% 2.43/0.99      | ~ l1_orders_2(X1) ),
% 2.43/0.99      inference(unflattening,[status(thm)],[c_847]) ).
% 2.43/0.99  
% 2.43/0.99  cnf(c_1253,plain,
% 2.43/0.99      ( ~ m1_subset_1(X0,u1_struct_0(X1))
% 2.43/0.99      | m1_subset_1(k5_waybel_0(X1,X0),k1_zfmisc_1(u1_struct_0(X1)))
% 2.43/0.99      | ~ l1_orders_2(X1)
% 2.43/0.99      | sK3 != X1 ),
% 2.43/0.99      inference(resolution_lifted,[status(thm)],[c_848,c_34]) ).
% 2.43/0.99  
% 2.43/0.99  cnf(c_1254,plain,
% 2.43/0.99      ( ~ m1_subset_1(X0,u1_struct_0(sK3))
% 2.43/0.99      | m1_subset_1(k5_waybel_0(sK3,X0),k1_zfmisc_1(u1_struct_0(sK3)))
% 2.43/0.99      | ~ l1_orders_2(sK3) ),
% 2.43/0.99      inference(unflattening,[status(thm)],[c_1253]) ).
% 2.43/0.99  
% 2.43/0.99  cnf(c_1258,plain,
% 2.43/0.99      ( m1_subset_1(k5_waybel_0(sK3,X0),k1_zfmisc_1(u1_struct_0(sK3)))
% 2.43/0.99      | ~ m1_subset_1(X0,u1_struct_0(sK3)) ),
% 2.43/0.99      inference(global_propositional_subsumption,
% 2.43/0.99                [status(thm)],
% 2.43/0.99                [c_1254,c_32]) ).
% 2.43/0.99  
% 2.43/0.99  cnf(c_1259,plain,
% 2.43/0.99      ( ~ m1_subset_1(X0,u1_struct_0(sK3))
% 2.43/0.99      | m1_subset_1(k5_waybel_0(sK3,X0),k1_zfmisc_1(u1_struct_0(sK3))) ),
% 2.43/0.99      inference(renaming,[status(thm)],[c_1258]) ).
% 2.43/0.99  
% 2.43/0.99  cnf(c_3810,plain,
% 2.43/0.99      ( ~ m1_subset_1(X0_55,u1_struct_0(sK3))
% 2.43/0.99      | m1_subset_1(k5_waybel_0(sK3,X0_55),k1_zfmisc_1(u1_struct_0(sK3))) ),
% 2.43/0.99      inference(subtyping,[status(esa)],[c_1259]) ).
% 2.43/0.99  
% 2.43/0.99  cnf(c_3871,plain,
% 2.43/0.99      ( m1_subset_1(k5_waybel_0(sK3,sK4),k1_zfmisc_1(u1_struct_0(sK3)))
% 2.43/0.99      | ~ m1_subset_1(sK4,u1_struct_0(sK3)) ),
% 2.43/0.99      inference(instantiation,[status(thm)],[c_3810]) ).
% 2.43/0.99  
% 2.43/0.99  cnf(c_19,plain,
% 2.43/0.99      ( ~ r1_orders_2(X0,X1,X2)
% 2.43/0.99      | r2_hidden(X1,k5_waybel_0(X0,X2))
% 2.43/0.99      | ~ m1_subset_1(X2,u1_struct_0(X0))
% 2.43/0.99      | ~ m1_subset_1(X1,u1_struct_0(X0))
% 2.43/0.99      | v2_struct_0(X0)
% 2.43/0.99      | ~ l1_orders_2(X0) ),
% 2.43/0.99      inference(cnf_transformation,[],[f72]) ).
% 2.43/0.99  
% 2.43/0.99  cnf(c_763,plain,
% 2.43/0.99      ( ~ r1_orders_2(X0,X1,X2)
% 2.43/0.99      | r2_hidden(X1,k5_waybel_0(X0,X2))
% 2.43/0.99      | ~ m1_subset_1(X1,u1_struct_0(X0))
% 2.43/0.99      | ~ m1_subset_1(X2,u1_struct_0(X0))
% 2.43/0.99      | ~ v1_lattice3(X0)
% 2.43/0.99      | ~ l1_orders_2(X0) ),
% 2.43/0.99      inference(resolution,[status(thm)],[c_19,c_1]) ).
% 2.43/0.99  
% 2.43/0.99  cnf(c_1209,plain,
% 2.43/0.99      ( ~ r1_orders_2(X0,X1,X2)
% 2.43/0.99      | r2_hidden(X1,k5_waybel_0(X0,X2))
% 2.43/0.99      | ~ m1_subset_1(X1,u1_struct_0(X0))
% 2.43/0.99      | ~ m1_subset_1(X2,u1_struct_0(X0))
% 2.43/0.99      | ~ l1_orders_2(X0)
% 2.43/0.99      | sK3 != X0 ),
% 2.43/0.99      inference(resolution_lifted,[status(thm)],[c_763,c_34]) ).
% 2.43/0.99  
% 2.43/0.99  cnf(c_1210,plain,
% 2.43/0.99      ( ~ r1_orders_2(sK3,X0,X1)
% 2.43/0.99      | r2_hidden(X0,k5_waybel_0(sK3,X1))
% 2.43/0.99      | ~ m1_subset_1(X0,u1_struct_0(sK3))
% 2.43/0.99      | ~ m1_subset_1(X1,u1_struct_0(sK3))
% 2.43/0.99      | ~ l1_orders_2(sK3) ),
% 2.43/0.99      inference(unflattening,[status(thm)],[c_1209]) ).
% 2.43/0.99  
% 2.43/0.99  cnf(c_1214,plain,
% 2.43/0.99      ( ~ m1_subset_1(X1,u1_struct_0(sK3))
% 2.43/0.99      | ~ m1_subset_1(X0,u1_struct_0(sK3))
% 2.43/0.99      | r2_hidden(X0,k5_waybel_0(sK3,X1))
% 2.43/0.99      | ~ r1_orders_2(sK3,X0,X1) ),
% 2.43/0.99      inference(global_propositional_subsumption,
% 2.43/0.99                [status(thm)],
% 2.43/0.99                [c_1210,c_32]) ).
% 2.43/0.99  
% 2.43/0.99  cnf(c_1215,plain,
% 2.43/0.99      ( ~ r1_orders_2(sK3,X0,X1)
% 2.43/0.99      | r2_hidden(X0,k5_waybel_0(sK3,X1))
% 2.43/0.99      | ~ m1_subset_1(X1,u1_struct_0(sK3))
% 2.43/0.99      | ~ m1_subset_1(X0,u1_struct_0(sK3)) ),
% 2.43/0.99      inference(renaming,[status(thm)],[c_1214]) ).
% 2.43/0.99  
% 2.43/0.99  cnf(c_3812,plain,
% 2.43/0.99      ( ~ r1_orders_2(sK3,X0_55,X1_55)
% 2.43/0.99      | r2_hidden(X0_55,k5_waybel_0(sK3,X1_55))
% 2.43/0.99      | ~ m1_subset_1(X0_55,u1_struct_0(sK3))
% 2.43/0.99      | ~ m1_subset_1(X1_55,u1_struct_0(sK3)) ),
% 2.43/0.99      inference(subtyping,[status(esa)],[c_1215]) ).
% 2.43/0.99  
% 2.43/0.99  cnf(c_3866,plain,
% 2.43/0.99      ( r1_orders_2(sK3,X0_55,X1_55) != iProver_top
% 2.43/0.99      | r2_hidden(X0_55,k5_waybel_0(sK3,X1_55)) = iProver_top
% 2.43/0.99      | m1_subset_1(X0_55,u1_struct_0(sK3)) != iProver_top
% 2.43/0.99      | m1_subset_1(X1_55,u1_struct_0(sK3)) != iProver_top ),
% 2.43/0.99      inference(predicate_to_equality,[status(thm)],[c_3812]) ).
% 2.43/0.99  
% 2.43/0.99  cnf(c_3868,plain,
% 2.43/0.99      ( r1_orders_2(sK3,sK4,sK4) != iProver_top
% 2.43/0.99      | r2_hidden(sK4,k5_waybel_0(sK3,sK4)) = iProver_top
% 2.43/0.99      | m1_subset_1(sK4,u1_struct_0(sK3)) != iProver_top ),
% 2.43/0.99      inference(instantiation,[status(thm)],[c_3866]) ).
% 2.43/0.99  
% 2.43/0.99  cnf(c_18,plain,
% 2.43/0.99      ( ~ m1_subset_1(X0,u1_struct_0(X1))
% 2.43/0.99      | ~ v1_xboole_0(k5_waybel_0(X1,X0))
% 2.43/0.99      | v2_struct_0(X1)
% 2.43/0.99      | ~ v3_orders_2(X1)
% 2.43/0.99      | ~ l1_orders_2(X1) ),
% 2.43/0.99      inference(cnf_transformation,[],[f69]) ).
% 2.43/0.99  
% 2.43/0.99  cnf(c_826,plain,
% 2.43/0.99      ( ~ m1_subset_1(X0,u1_struct_0(X1))
% 2.43/0.99      | ~ v1_xboole_0(k5_waybel_0(X1,X0))
% 2.43/0.99      | ~ v1_lattice3(X2)
% 2.43/0.99      | ~ v3_orders_2(X1)
% 2.43/0.99      | ~ l1_orders_2(X2)
% 2.43/0.99      | ~ l1_orders_2(X1)
% 2.43/0.99      | X1 != X2 ),
% 2.43/0.99      inference(resolution_lifted,[status(thm)],[c_1,c_18]) ).
% 2.43/0.99  
% 2.43/0.99  cnf(c_827,plain,
% 2.43/0.99      ( ~ m1_subset_1(X0,u1_struct_0(X1))
% 2.43/0.99      | ~ v1_xboole_0(k5_waybel_0(X1,X0))
% 2.43/0.99      | ~ v1_lattice3(X1)
% 2.43/0.99      | ~ v3_orders_2(X1)
% 2.43/0.99      | ~ l1_orders_2(X1) ),
% 2.43/0.99      inference(unflattening,[status(thm)],[c_826]) ).
% 2.43/0.99  
% 2.43/0.99  cnf(c_1182,plain,
% 2.43/0.99      ( ~ m1_subset_1(X0,u1_struct_0(X1))
% 2.43/0.99      | ~ v1_xboole_0(k5_waybel_0(X1,X0))
% 2.43/0.99      | ~ v1_lattice3(X1)
% 2.43/0.99      | ~ l1_orders_2(X1)
% 2.43/0.99      | sK3 != X1 ),
% 2.43/0.99      inference(resolution_lifted,[status(thm)],[c_827,c_37]) ).
% 2.43/0.99  
% 2.43/0.99  cnf(c_1183,plain,
% 2.43/0.99      ( ~ m1_subset_1(X0,u1_struct_0(sK3))
% 2.43/0.99      | ~ v1_xboole_0(k5_waybel_0(sK3,X0))
% 2.43/0.99      | ~ v1_lattice3(sK3)
% 2.43/0.99      | ~ l1_orders_2(sK3) ),
% 2.43/0.99      inference(unflattening,[status(thm)],[c_1182]) ).
% 2.43/0.99  
% 2.43/0.99  cnf(c_1187,plain,
% 2.43/0.99      ( ~ m1_subset_1(X0,u1_struct_0(sK3))
% 2.43/0.99      | ~ v1_xboole_0(k5_waybel_0(sK3,X0)) ),
% 2.43/0.99      inference(global_propositional_subsumption,
% 2.43/0.99                [status(thm)],
% 2.43/0.99                [c_1183,c_34,c_32]) ).
% 2.43/0.99  
% 2.43/0.99  cnf(c_3813,plain,
% 2.43/0.99      ( ~ m1_subset_1(X0_55,u1_struct_0(sK3))
% 2.43/0.99      | ~ v1_xboole_0(k5_waybel_0(sK3,X0_55)) ),
% 2.43/0.99      inference(subtyping,[status(esa)],[c_1187]) ).
% 2.43/0.99  
% 2.43/0.99  cnf(c_3864,plain,
% 2.43/0.99      ( ~ m1_subset_1(sK4,u1_struct_0(sK3))
% 2.43/0.99      | ~ v1_xboole_0(k5_waybel_0(sK3,sK4)) ),
% 2.43/0.99      inference(instantiation,[status(thm)],[c_3813]) ).
% 2.43/0.99  
% 2.43/0.99  cnf(c_17,plain,
% 2.43/0.99      ( v1_waybel_0(k5_waybel_0(X0,X1),X0)
% 2.43/0.99      | ~ m1_subset_1(X1,u1_struct_0(X0))
% 2.43/0.99      | v2_struct_0(X0)
% 2.43/0.99      | ~ v3_orders_2(X0)
% 2.43/0.99      | ~ l1_orders_2(X0) ),
% 2.43/0.99      inference(cnf_transformation,[],[f70]) ).
% 2.43/0.99  
% 2.43/0.99  cnf(c_786,plain,
% 2.43/0.99      ( v1_waybel_0(k5_waybel_0(X0,X1),X0)
% 2.43/0.99      | ~ m1_subset_1(X1,u1_struct_0(X0))
% 2.43/0.99      | ~ v1_lattice3(X0)
% 2.43/0.99      | ~ v3_orders_2(X0)
% 2.43/0.99      | ~ l1_orders_2(X0) ),
% 2.43/0.99      inference(resolution,[status(thm)],[c_17,c_1]) ).
% 2.43/0.99  
% 2.43/0.99  cnf(c_1164,plain,
% 2.43/0.99      ( v1_waybel_0(k5_waybel_0(X0,X1),X0)
% 2.43/0.99      | ~ m1_subset_1(X1,u1_struct_0(X0))
% 2.43/0.99      | ~ v1_lattice3(X0)
% 2.43/0.99      | ~ l1_orders_2(X0)
% 2.43/0.99      | sK3 != X0 ),
% 2.43/0.99      inference(resolution_lifted,[status(thm)],[c_786,c_37]) ).
% 2.43/0.99  
% 2.43/0.99  cnf(c_1165,plain,
% 2.43/0.99      ( v1_waybel_0(k5_waybel_0(sK3,X0),sK3)
% 2.43/0.99      | ~ m1_subset_1(X0,u1_struct_0(sK3))
% 2.43/0.99      | ~ v1_lattice3(sK3)
% 2.43/0.99      | ~ l1_orders_2(sK3) ),
% 2.43/0.99      inference(unflattening,[status(thm)],[c_1164]) ).
% 2.43/0.99  
% 2.43/0.99  cnf(c_1169,plain,
% 2.43/0.99      ( v1_waybel_0(k5_waybel_0(sK3,X0),sK3)
% 2.43/0.99      | ~ m1_subset_1(X0,u1_struct_0(sK3)) ),
% 2.43/0.99      inference(global_propositional_subsumption,
% 2.43/0.99                [status(thm)],
% 2.43/0.99                [c_1165,c_34,c_32]) ).
% 2.43/0.99  
% 2.43/0.99  cnf(c_3814,plain,
% 2.43/0.99      ( v1_waybel_0(k5_waybel_0(sK3,X0_55),sK3)
% 2.43/0.99      | ~ m1_subset_1(X0_55,u1_struct_0(sK3)) ),
% 2.43/0.99      inference(subtyping,[status(esa)],[c_1169]) ).
% 2.43/0.99  
% 2.43/0.99  cnf(c_3861,plain,
% 2.43/0.99      ( v1_waybel_0(k5_waybel_0(sK3,sK4),sK3)
% 2.43/0.99      | ~ m1_subset_1(sK4,u1_struct_0(sK3)) ),
% 2.43/0.99      inference(instantiation,[status(thm)],[c_3814]) ).
% 2.43/0.99  
% 2.43/0.99  cnf(c_0,plain,
% 2.43/0.99      ( r1_orders_2(X0,X1,X1)
% 2.43/0.99      | ~ m1_subset_1(X1,u1_struct_0(X0))
% 2.43/0.99      | v2_struct_0(X0)
% 2.43/0.99      | ~ v3_orders_2(X0)
% 2.43/0.99      | ~ l1_orders_2(X0) ),
% 2.43/0.99      inference(cnf_transformation,[],[f52]) ).
% 2.43/0.99  
% 2.43/0.99  cnf(c_806,plain,
% 2.43/0.99      ( r1_orders_2(X0,X1,X1)
% 2.43/0.99      | ~ m1_subset_1(X1,u1_struct_0(X0))
% 2.43/0.99      | ~ v1_lattice3(X0)
% 2.43/0.99      | ~ v3_orders_2(X0)
% 2.43/0.99      | ~ l1_orders_2(X0) ),
% 2.43/0.99      inference(resolution,[status(thm)],[c_0,c_1]) ).
% 2.43/0.99  
% 2.43/0.99  cnf(c_1146,plain,
% 2.43/0.99      ( r1_orders_2(X0,X1,X1)
% 2.43/0.99      | ~ m1_subset_1(X1,u1_struct_0(X0))
% 2.43/0.99      | ~ v1_lattice3(X0)
% 2.43/0.99      | ~ l1_orders_2(X0)
% 2.43/0.99      | sK3 != X0 ),
% 2.43/0.99      inference(resolution_lifted,[status(thm)],[c_806,c_37]) ).
% 2.43/0.99  
% 2.43/0.99  cnf(c_1147,plain,
% 2.43/0.99      ( r1_orders_2(sK3,X0,X0)
% 2.43/0.99      | ~ m1_subset_1(X0,u1_struct_0(sK3))
% 2.43/0.99      | ~ v1_lattice3(sK3)
% 2.43/0.99      | ~ l1_orders_2(sK3) ),
% 2.43/0.99      inference(unflattening,[status(thm)],[c_1146]) ).
% 2.43/0.99  
% 2.43/0.99  cnf(c_1151,plain,
% 2.43/0.99      ( r1_orders_2(sK3,X0,X0) | ~ m1_subset_1(X0,u1_struct_0(sK3)) ),
% 2.43/0.99      inference(global_propositional_subsumption,
% 2.43/0.99                [status(thm)],
% 2.43/0.99                [c_1147,c_34,c_32]) ).
% 2.43/0.99  
% 2.43/0.99  cnf(c_3815,plain,
% 2.43/0.99      ( r1_orders_2(sK3,X0_55,X0_55)
% 2.43/0.99      | ~ m1_subset_1(X0_55,u1_struct_0(sK3)) ),
% 2.43/0.99      inference(subtyping,[status(esa)],[c_1151]) ).
% 2.43/0.99  
% 2.43/0.99  cnf(c_3857,plain,
% 2.43/0.99      ( r1_orders_2(sK3,X0_55,X0_55) = iProver_top
% 2.43/0.99      | m1_subset_1(X0_55,u1_struct_0(sK3)) != iProver_top ),
% 2.43/0.99      inference(predicate_to_equality,[status(thm)],[c_3815]) ).
% 2.43/0.99  
% 2.43/0.99  cnf(c_3859,plain,
% 2.43/0.99      ( r1_orders_2(sK3,sK4,sK4) = iProver_top
% 2.43/0.99      | m1_subset_1(sK4,u1_struct_0(sK3)) != iProver_top ),
% 2.43/0.99      inference(instantiation,[status(thm)],[c_3857]) ).
% 2.43/0.99  
% 2.43/0.99  cnf(c_3828,plain,( X0_55 = X0_55 ),theory(equality) ).
% 2.43/0.99  
% 2.43/0.99  cnf(c_3849,plain,
% 2.43/0.99      ( sK4 = sK4 ),
% 2.43/0.99      inference(instantiation,[status(thm)],[c_3828]) ).
% 2.43/0.99  
% 2.43/0.99  cnf(c_3835,plain,
% 2.43/0.99      ( X0_55 != X1_55
% 2.43/0.99      | k5_waybel_0(X0_56,X0_55) = k5_waybel_0(X0_56,X1_55) ),
% 2.43/0.99      theory(equality) ).
% 2.43/0.99  
% 2.43/0.99  cnf(c_3844,plain,
% 2.43/0.99      ( k5_waybel_0(sK3,sK4) = k5_waybel_0(sK3,sK4) | sK4 != sK4 ),
% 2.43/0.99      inference(instantiation,[status(thm)],[c_3835]) ).
% 2.43/0.99  
% 2.43/0.99  cnf(c_29,negated_conjecture,
% 2.43/0.99      ( ~ v4_waybel_7(sK4,sK3) ),
% 2.43/0.99      inference(cnf_transformation,[],[f89]) ).
% 2.43/0.99  
% 2.43/0.99  cnf(c_44,plain,
% 2.43/0.99      ( m1_subset_1(sK4,u1_struct_0(sK3)) = iProver_top ),
% 2.43/0.99      inference(predicate_to_equality,[status(thm)],[c_31]) ).
% 2.43/0.99  
% 2.43/0.99  cnf(contradiction,plain,
% 2.43/0.99      ( $false ),
% 2.43/0.99      inference(minisat,
% 2.43/0.99                [status(thm)],
% 2.43/0.99                [c_7247,c_5467,c_5269,c_5265,c_5067,c_5063,c_5059,c_4768,
% 2.43/0.99                 c_4661,c_3912,c_3824,c_3871,c_3868,c_3864,c_3861,c_3859,
% 2.43/0.99                 c_3849,c_3844,c_29,c_44,c_31]) ).
% 2.43/0.99  
% 2.43/0.99  
% 2.43/0.99  % SZS output end CNFRefutation for theBenchmark.p
% 2.43/0.99  
% 2.43/0.99  ------                               Statistics
% 2.43/0.99  
% 2.43/0.99  ------ General
% 2.43/0.99  
% 2.43/0.99  abstr_ref_over_cycles:                  0
% 2.43/0.99  abstr_ref_under_cycles:                 0
% 2.43/0.99  gc_basic_clause_elim:                   0
% 2.43/0.99  forced_gc_time:                         0
% 2.43/0.99  parsing_time:                           0.012
% 2.43/0.99  unif_index_cands_time:                  0.
% 2.43/0.99  unif_index_add_time:                    0.
% 2.43/0.99  orderings_time:                         0.
% 2.43/0.99  out_proof_time:                         0.014
% 2.43/0.99  total_time:                             0.224
% 2.43/0.99  num_of_symbols:                         60
% 2.43/0.99  num_of_terms:                           4765
% 2.43/0.99  
% 2.43/0.99  ------ Preprocessing
% 2.43/0.99  
% 2.43/0.99  num_of_splits:                          2
% 2.43/0.99  num_of_split_atoms:                     2
% 2.43/0.99  num_of_reused_defs:                     0
% 2.43/0.99  num_eq_ax_congr_red:                    47
% 2.43/0.99  num_of_sem_filtered_clauses:            9
% 2.43/0.99  num_of_subtypes:                        3
% 2.43/0.99  monotx_restored_types:                  0
% 2.43/0.99  sat_num_of_epr_types:                   0
% 2.43/0.99  sat_num_of_non_cyclic_types:            0
% 2.43/0.99  sat_guarded_non_collapsed_types:        1
% 2.43/0.99  num_pure_diseq_elim:                    0
% 2.43/0.99  simp_replaced_by:                       0
% 2.43/0.99  res_preprocessed:                       139
% 2.43/0.99  prep_upred:                             0
% 2.43/0.99  prep_unflattend:                        116
% 2.43/0.99  smt_new_axioms:                         0
% 2.43/0.99  pred_elim_cands:                        8
% 2.43/0.99  pred_elim:                              10
% 2.43/0.99  pred_elim_cl:                           10
% 2.43/0.99  pred_elim_cycles:                       25
% 2.43/0.99  merged_defs:                            0
% 2.43/0.99  merged_defs_ncl:                        0
% 2.43/0.99  bin_hyper_res:                          0
% 2.43/0.99  prep_cycles:                            4
% 2.43/0.99  pred_elim_time:                         0.065
% 2.43/0.99  splitting_time:                         0.
% 2.43/0.99  sem_filter_time:                        0.
% 2.43/0.99  monotx_time:                            0.
% 2.43/0.99  subtype_inf_time:                       0.
% 2.43/0.99  
% 2.43/0.99  ------ Problem properties
% 2.43/0.99  
% 2.43/0.99  clauses:                                30
% 2.43/0.99  conjectures:                            2
% 2.43/0.99  epr:                                    1
% 2.43/0.99  horn:                                   22
% 2.43/0.99  ground:                                 4
% 2.43/0.99  unary:                                  3
% 2.43/0.99  binary:                                 5
% 2.43/0.99  lits:                                   95
% 2.43/0.99  lits_eq:                                6
% 2.43/0.99  fd_pure:                                0
% 2.43/0.99  fd_pseudo:                              0
% 2.43/0.99  fd_cond:                                0
% 2.43/0.99  fd_pseudo_cond:                         3
% 2.43/0.99  ac_symbols:                             0
% 2.43/0.99  
% 2.43/0.99  ------ Propositional Solver
% 2.43/0.99  
% 2.43/0.99  prop_solver_calls:                      29
% 2.43/0.99  prop_fast_solver_calls:                 2132
% 2.43/0.99  smt_solver_calls:                       0
% 2.43/0.99  smt_fast_solver_calls:                  0
% 2.43/0.99  prop_num_of_clauses:                    1864
% 2.43/0.99  prop_preprocess_simplified:             6225
% 2.43/0.99  prop_fo_subsumed:                       105
% 2.43/0.99  prop_solver_time:                       0.
% 2.43/0.99  smt_solver_time:                        0.
% 2.43/0.99  smt_fast_solver_time:                   0.
% 2.43/0.99  prop_fast_solver_time:                  0.
% 2.43/0.99  prop_unsat_core_time:                   0.
% 2.43/0.99  
% 2.43/0.99  ------ QBF
% 2.43/0.99  
% 2.43/0.99  qbf_q_res:                              0
% 2.43/0.99  qbf_num_tautologies:                    0
% 2.43/0.99  qbf_prep_cycles:                        0
% 2.43/0.99  
% 2.43/0.99  ------ BMC1
% 2.43/0.99  
% 2.43/0.99  bmc1_current_bound:                     -1
% 2.43/0.99  bmc1_last_solved_bound:                 -1
% 2.43/0.99  bmc1_unsat_core_size:                   -1
% 2.43/0.99  bmc1_unsat_core_parents_size:           -1
% 2.43/0.99  bmc1_merge_next_fun:                    0
% 2.43/0.99  bmc1_unsat_core_clauses_time:           0.
% 2.43/0.99  
% 2.43/0.99  ------ Instantiation
% 2.43/0.99  
% 2.43/0.99  inst_num_of_clauses:                    367
% 2.43/0.99  inst_num_in_passive:                    28
% 2.43/0.99  inst_num_in_active:                     254
% 2.43/0.99  inst_num_in_unprocessed:                85
% 2.43/0.99  inst_num_of_loops:                      310
% 2.43/0.99  inst_num_of_learning_restarts:          0
% 2.43/0.99  inst_num_moves_active_passive:          52
% 2.43/0.99  inst_lit_activity:                      0
% 2.43/0.99  inst_lit_activity_moves:                0
% 2.43/0.99  inst_num_tautologies:                   0
% 2.43/0.99  inst_num_prop_implied:                  0
% 2.43/0.99  inst_num_existing_simplified:           0
% 2.43/0.99  inst_num_eq_res_simplified:             0
% 2.43/0.99  inst_num_child_elim:                    0
% 2.43/0.99  inst_num_of_dismatching_blockings:      124
% 2.43/0.99  inst_num_of_non_proper_insts:           425
% 2.43/0.99  inst_num_of_duplicates:                 0
% 2.43/0.99  inst_inst_num_from_inst_to_res:         0
% 2.43/0.99  inst_dismatching_checking_time:         0.
% 2.43/0.99  
% 2.43/0.99  ------ Resolution
% 2.43/0.99  
% 2.43/0.99  res_num_of_clauses:                     0
% 2.43/0.99  res_num_in_passive:                     0
% 2.43/0.99  res_num_in_active:                      0
% 2.43/0.99  res_num_of_loops:                       143
% 2.43/0.99  res_forward_subset_subsumed:            26
% 2.43/0.99  res_backward_subset_subsumed:           8
% 2.43/0.99  res_forward_subsumed:                   6
% 2.43/0.99  res_backward_subsumed:                  0
% 2.43/0.99  res_forward_subsumption_resolution:     4
% 2.43/0.99  res_backward_subsumption_resolution:    2
% 2.43/0.99  res_clause_to_clause_subsumption:       702
% 2.43/0.99  res_orphan_elimination:                 0
% 2.43/0.99  res_tautology_del:                      56
% 2.43/0.99  res_num_eq_res_simplified:              0
% 2.43/0.99  res_num_sel_changes:                    0
% 2.43/0.99  res_moves_from_active_to_pass:          0
% 2.43/0.99  
% 2.43/0.99  ------ Superposition
% 2.43/0.99  
% 2.43/0.99  sup_time_total:                         0.
% 2.43/0.99  sup_time_generating:                    0.
% 2.43/0.99  sup_time_sim_full:                      0.
% 2.43/0.99  sup_time_sim_immed:                     0.
% 2.43/0.99  
% 2.43/0.99  sup_num_of_clauses:                     89
% 2.43/0.99  sup_num_in_active:                      62
% 2.43/0.99  sup_num_in_passive:                     27
% 2.43/0.99  sup_num_of_loops:                       61
% 2.43/0.99  sup_fw_superposition:                   51
% 2.43/0.99  sup_bw_superposition:                   17
% 2.43/0.99  sup_immediate_simplified:               7
% 2.43/0.99  sup_given_eliminated:                   0
% 2.43/0.99  comparisons_done:                       0
% 2.43/0.99  comparisons_avoided:                    0
% 2.43/0.99  
% 2.43/0.99  ------ Simplifications
% 2.43/0.99  
% 2.43/0.99  
% 2.43/0.99  sim_fw_subset_subsumed:                 7
% 2.43/0.99  sim_bw_subset_subsumed:                 1
% 2.43/0.99  sim_fw_subsumed:                        0
% 2.43/0.99  sim_bw_subsumed:                        0
% 2.43/0.99  sim_fw_subsumption_res:                 4
% 2.43/0.99  sim_bw_subsumption_res:                 0
% 2.43/0.99  sim_tautology_del:                      2
% 2.43/0.99  sim_eq_tautology_del:                   0
% 2.43/0.99  sim_eq_res_simp:                        0
% 2.43/0.99  sim_fw_demodulated:                     0
% 2.43/0.99  sim_bw_demodulated:                     0
% 2.43/0.99  sim_light_normalised:                   0
% 2.43/0.99  sim_joinable_taut:                      0
% 2.43/0.99  sim_joinable_simp:                      0
% 2.43/0.99  sim_ac_normalised:                      0
% 2.43/0.99  sim_smt_subsumption:                    0
% 2.43/0.99  
%------------------------------------------------------------------------------
