%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n025.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:28:36 EST 2020

% Result     : Theorem 3.12s
% Output     : CNFRefutation 3.12s
% Verified   : 
% Statistics : Number of formulae       :  207 (1100 expanded)
%              Number of clauses        :  128 ( 257 expanded)
%              Number of leaves         :   17 ( 293 expanded)
%              Depth                    :   23
%              Number of atoms          : 1115 (8140 expanded)
%              Number of equality atoms :  178 ( 244 expanded)
%              Maximal formula depth    :   18 (   6 average)
%              Maximal clause size      :   21 (   4 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

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
    inference(ennf_transformation,[],[f13])).

fof(f38,plain,(
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
    inference(flattening,[],[f37])).

fof(f51,plain,(
    ! [X0] :
      ( ? [X1] :
          ( ~ v4_waybel_7(X1,X0)
          & v5_waybel_6(X1,X0)
          & m1_subset_1(X1,u1_struct_0(X0)) )
     => ( ~ v4_waybel_7(sK4,X0)
        & v5_waybel_6(sK4,X0)
        & m1_subset_1(sK4,u1_struct_0(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f50,plain,
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

fof(f52,plain,
    ( ~ v4_waybel_7(sK4,sK3)
    & v5_waybel_6(sK4,sK3)
    & m1_subset_1(sK4,u1_struct_0(sK3))
    & l1_orders_2(sK3)
    & v2_lattice3(sK3)
    & v1_lattice3(sK3)
    & v5_orders_2(sK3)
    & v4_orders_2(sK3)
    & v3_orders_2(sK3) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3,sK4])],[f38,f51,f50])).

fof(f88,plain,(
    m1_subset_1(sK4,u1_struct_0(sK3)) ),
    inference(cnf_transformation,[],[f52])).

fof(f4,axiom,(
    ! [X0] :
      ( l1_orders_2(X0)
     => ! [X1,X2] :
          ( m1_subset_1(X2,u1_struct_0(X0))
         => ( r2_lattice3(X0,X1,X2)
          <=> ! [X3] :
                ( m1_subset_1(X3,u1_struct_0(X0))
               => ( r2_hidden(X3,X1)
                 => r1_orders_2(X0,X3,X2) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f21,plain,(
    ! [X0] :
      ( ! [X1,X2] :
          ( ( r2_lattice3(X0,X1,X2)
          <=> ! [X3] :
                ( r1_orders_2(X0,X3,X2)
                | ~ r2_hidden(X3,X1)
                | ~ m1_subset_1(X3,u1_struct_0(X0)) ) )
          | ~ m1_subset_1(X2,u1_struct_0(X0)) )
      | ~ l1_orders_2(X0) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f22,plain,(
    ! [X0] :
      ( ! [X1,X2] :
          ( ( r2_lattice3(X0,X1,X2)
          <=> ! [X3] :
                ( r1_orders_2(X0,X3,X2)
                | ~ r2_hidden(X3,X1)
                | ~ m1_subset_1(X3,u1_struct_0(X0)) ) )
          | ~ m1_subset_1(X2,u1_struct_0(X0)) )
      | ~ l1_orders_2(X0) ) ),
    inference(flattening,[],[f21])).

fof(f39,plain,(
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
    inference(nnf_transformation,[],[f22])).

fof(f40,plain,(
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
    inference(rectify,[],[f39])).

fof(f41,plain,(
    ! [X2,X1,X0] :
      ( ? [X3] :
          ( ~ r1_orders_2(X0,X3,X2)
          & r2_hidden(X3,X1)
          & m1_subset_1(X3,u1_struct_0(X0)) )
     => ( ~ r1_orders_2(X0,sK0(X0,X1,X2),X2)
        & r2_hidden(sK0(X0,X1,X2),X1)
        & m1_subset_1(sK0(X0,X1,X2),u1_struct_0(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f42,plain,(
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
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f40,f41])).

fof(f58,plain,(
    ! [X2,X0,X1] :
      ( r2_lattice3(X0,X1,X2)
      | r2_hidden(sK0(X0,X1,X2),X1)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ l1_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f42])).

fof(f87,plain,(
    l1_orders_2(sK3) ),
    inference(cnf_transformation,[],[f52])).

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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

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
    inference(ennf_transformation,[],[f9])).

fof(f32,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( r2_hidden(X2,k5_waybel_0(X0,X1))
              <=> r1_orders_2(X0,X2,X1) )
              | ~ m1_subset_1(X2,u1_struct_0(X0)) )
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l1_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f31])).

fof(f45,plain,(
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
    inference(nnf_transformation,[],[f32])).

fof(f72,plain,(
    ! [X2,X0,X1] :
      ( r1_orders_2(X0,X2,X1)
      | ~ r2_hidden(X2,k5_waybel_0(X0,X1))
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f45])).

fof(f3,axiom,(
    ! [X0] :
      ( l1_orders_2(X0)
     => ( v1_lattice3(X0)
       => ~ v2_struct_0(X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f19,plain,(
    ! [X0] :
      ( ~ v2_struct_0(X0)
      | ~ v1_lattice3(X0)
      | ~ l1_orders_2(X0) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f20,plain,(
    ! [X0] :
      ( ~ v2_struct_0(X0)
      | ~ v1_lattice3(X0)
      | ~ l1_orders_2(X0) ) ),
    inference(flattening,[],[f19])).

fof(f55,plain,(
    ! [X0] :
      ( ~ v2_struct_0(X0)
      | ~ v1_lattice3(X0)
      | ~ l1_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f85,plain,(
    v1_lattice3(sK3) ),
    inference(cnf_transformation,[],[f52])).

fof(f6,axiom,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,u1_struct_0(X0))
        & l1_orders_2(X0)
        & ~ v2_struct_0(X0) )
     => m1_subset_1(k5_waybel_0(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f25,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k5_waybel_0(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f26,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k5_waybel_0(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f25])).

fof(f68,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k5_waybel_0(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f1,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(X2))
        & r2_hidden(X0,X1) )
     => m1_subset_1(X0,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f15,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X0,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f16,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X0,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(flattening,[],[f15])).

fof(f53,plain,(
    ! [X2,X0,X1] :
      ( m1_subset_1(X0,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f16])).

fof(f59,plain,(
    ! [X2,X0,X1] :
      ( r2_lattice3(X0,X1,X2)
      | ~ r1_orders_2(X0,sK0(X0,X1,X2),X2)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ l1_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f42])).

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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

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
    inference(ennf_transformation,[],[f14])).

fof(f24,plain,(
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
    inference(flattening,[],[f23])).

fof(f43,plain,(
    ! [X2,X1,X0] :
      ( ? [X3] :
          ( ~ r1_orders_2(X0,X1,X3)
          & r2_lattice3(X0,X2,X3)
          & m1_subset_1(X3,u1_struct_0(X0)) )
     => ( ~ r1_orders_2(X0,X1,sK1(X0,X1,X2))
        & r2_lattice3(X0,X2,sK1(X0,X1,X2))
        & m1_subset_1(sK1(X0,X1,X2),u1_struct_0(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f44,plain,(
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
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1])],[f24,f43])).

fof(f63,plain,(
    ! [X2,X0,X1] :
      ( k1_yellow_0(X0,X2) = X1
      | r2_lattice3(X0,X2,sK1(X0,X1,X2))
      | ~ r2_lattice3(X0,X2,X1)
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | ~ v5_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f44])).

fof(f84,plain,(
    v5_orders_2(sK3) ),
    inference(cnf_transformation,[],[f52])).

fof(f62,plain,(
    ! [X2,X0,X1] :
      ( k1_yellow_0(X0,X2) = X1
      | m1_subset_1(sK1(X0,X1,X2),u1_struct_0(X0))
      | ~ r2_lattice3(X0,X2,X1)
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | ~ v5_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f44])).

fof(f56,plain,(
    ! [X4,X2,X0,X1] :
      ( r1_orders_2(X0,X4,X2)
      | ~ r2_hidden(X4,X1)
      | ~ m1_subset_1(X4,u1_struct_0(X0))
      | ~ r2_lattice3(X0,X1,X2)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ l1_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f42])).

fof(f64,plain,(
    ! [X2,X0,X1] :
      ( k1_yellow_0(X0,X2) = X1
      | ~ r1_orders_2(X0,X1,sK1(X0,X1,X2))
      | ~ r2_lattice3(X0,X2,X1)
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | ~ v5_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f44])).

fof(f2,axiom,(
    ! [X0] :
      ( ( l1_orders_2(X0)
        & v3_orders_2(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,u1_struct_0(X0))
         => r1_orders_2(X0,X1,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f17,plain,(
    ! [X0] :
      ( ! [X1] :
          ( r1_orders_2(X0,X1,X1)
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l1_orders_2(X0)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f18,plain,(
    ! [X0] :
      ( ! [X1] :
          ( r1_orders_2(X0,X1,X1)
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l1_orders_2(X0)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f17])).

fof(f54,plain,(
    ! [X0,X1] :
      ( r1_orders_2(X0,X1,X1)
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f82,plain,(
    v3_orders_2(sK3) ),
    inference(cnf_transformation,[],[f52])).

fof(f73,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(X2,k5_waybel_0(X0,X1))
      | ~ r1_orders_2(X0,X2,X1)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f45])).

fof(f7,axiom,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,u1_struct_0(X0))
        & l1_orders_2(X0)
        & v4_orders_2(X0)
        & ~ v2_struct_0(X0) )
     => v12_waybel_0(k5_waybel_0(X0,X1),X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f27,plain,(
    ! [X0,X1] :
      ( v12_waybel_0(k5_waybel_0(X0,X1),X0)
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | ~ v4_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f28,plain,(
    ! [X0,X1] :
      ( v12_waybel_0(k5_waybel_0(X0,X1),X0)
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | ~ v4_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f27])).

fof(f69,plain,(
    ! [X0,X1] :
      ( v12_waybel_0(k5_waybel_0(X0,X1),X0)
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | ~ v4_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f28])).

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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

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
    inference(ennf_transformation,[],[f10])).

fof(f34,plain,(
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
    inference(flattening,[],[f33])).

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
    inference(nnf_transformation,[],[f34])).

fof(f47,plain,(
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
    inference(rectify,[],[f46])).

fof(f48,plain,(
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

fof(f49,plain,(
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
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2])],[f47,f48])).

fof(f80,plain,(
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
    inference(cnf_transformation,[],[f49])).

fof(f93,plain,(
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
    inference(equality_resolution,[],[f80])).

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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

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
    inference(ennf_transformation,[],[f11])).

fof(f36,plain,(
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
    inference(flattening,[],[f35])).

fof(f81,plain,(
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
    inference(cnf_transformation,[],[f36])).

fof(f89,plain,(
    v5_waybel_6(sK4,sK3) ),
    inference(cnf_transformation,[],[f52])).

fof(f83,plain,(
    v4_orders_2(sK3) ),
    inference(cnf_transformation,[],[f52])).

fof(f86,plain,(
    v2_lattice3(sK3) ),
    inference(cnf_transformation,[],[f52])).

fof(f8,axiom,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,u1_struct_0(X0))
        & l1_orders_2(X0)
        & v3_orders_2(X0)
        & ~ v2_struct_0(X0) )
     => ( v1_waybel_0(k5_waybel_0(X0,X1),X0)
        & ~ v1_xboole_0(k5_waybel_0(X0,X1)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f29,plain,(
    ! [X0,X1] :
      ( ( v1_waybel_0(k5_waybel_0(X0,X1),X0)
        & ~ v1_xboole_0(k5_waybel_0(X0,X1)) )
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f30,plain,(
    ! [X0,X1] :
      ( ( v1_waybel_0(k5_waybel_0(X0,X1),X0)
        & ~ v1_xboole_0(k5_waybel_0(X0,X1)) )
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f29])).

fof(f71,plain,(
    ! [X0,X1] :
      ( v1_waybel_0(k5_waybel_0(X0,X1),X0)
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f70,plain,(
    ! [X0,X1] :
      ( ~ v1_xboole_0(k5_waybel_0(X0,X1))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f90,plain,(
    ~ v4_waybel_7(sK4,sK3) ),
    inference(cnf_transformation,[],[f52])).

cnf(c_31,negated_conjecture,
    ( m1_subset_1(sK4,u1_struct_0(sK3)) ),
    inference(cnf_transformation,[],[f88])).

cnf(c_4106,plain,
    ( m1_subset_1(sK4,u1_struct_0(sK3)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_31])).

cnf(c_4,plain,
    ( r2_lattice3(X0,X1,X2)
    | r2_hidden(sK0(X0,X1,X2),X1)
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | ~ l1_orders_2(X0) ),
    inference(cnf_transformation,[],[f58])).

cnf(c_32,negated_conjecture,
    ( l1_orders_2(sK3) ),
    inference(cnf_transformation,[],[f87])).

cnf(c_1708,plain,
    ( r2_lattice3(X0,X1,X2)
    | r2_hidden(sK0(X0,X1,X2),X1)
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | sK3 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_4,c_32])).

cnf(c_1709,plain,
    ( r2_lattice3(sK3,X0,X1)
    | r2_hidden(sK0(sK3,X0,X1),X0)
    | ~ m1_subset_1(X1,u1_struct_0(sK3)) ),
    inference(unflattening,[status(thm)],[c_1708])).

cnf(c_4080,plain,
    ( r2_lattice3(sK3,X0,X1) = iProver_top
    | r2_hidden(sK0(sK3,X0,X1),X0) = iProver_top
    | m1_subset_1(X1,u1_struct_0(sK3)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1709])).

cnf(c_20,plain,
    ( r1_orders_2(X0,X1,X2)
    | ~ r2_hidden(X1,k5_waybel_0(X0,X2))
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | ~ m1_subset_1(X1,u1_struct_0(X0))
    | v2_struct_0(X0)
    | ~ l1_orders_2(X0) ),
    inference(cnf_transformation,[],[f72])).

cnf(c_2,plain,
    ( ~ v1_lattice3(X0)
    | ~ v2_struct_0(X0)
    | ~ l1_orders_2(X0) ),
    inference(cnf_transformation,[],[f55])).

cnf(c_607,plain,
    ( r1_orders_2(X0,X1,X2)
    | ~ r2_hidden(X1,k5_waybel_0(X0,X2))
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | ~ m1_subset_1(X1,u1_struct_0(X0))
    | ~ v1_lattice3(X0)
    | ~ l1_orders_2(X0) ),
    inference(resolution,[status(thm)],[c_20,c_2])).

cnf(c_34,negated_conjecture,
    ( v1_lattice3(sK3) ),
    inference(cnf_transformation,[],[f85])).

cnf(c_985,plain,
    ( r1_orders_2(X0,X1,X2)
    | ~ r2_hidden(X1,k5_waybel_0(X0,X2))
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | ~ m1_subset_1(X1,u1_struct_0(X0))
    | ~ l1_orders_2(X0)
    | sK3 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_607,c_34])).

cnf(c_986,plain,
    ( r1_orders_2(sK3,X0,X1)
    | ~ r2_hidden(X0,k5_waybel_0(sK3,X1))
    | ~ m1_subset_1(X0,u1_struct_0(sK3))
    | ~ m1_subset_1(X1,u1_struct_0(sK3))
    | ~ l1_orders_2(sK3) ),
    inference(unflattening,[status(thm)],[c_985])).

cnf(c_988,plain,
    ( ~ m1_subset_1(X1,u1_struct_0(sK3))
    | ~ m1_subset_1(X0,u1_struct_0(sK3))
    | ~ r2_hidden(X0,k5_waybel_0(sK3,X1))
    | r1_orders_2(sK3,X0,X1) ),
    inference(global_propositional_subsumption,[status(thm)],[c_986,c_32])).

cnf(c_989,plain,
    ( r1_orders_2(sK3,X0,X1)
    | ~ r2_hidden(X0,k5_waybel_0(sK3,X1))
    | ~ m1_subset_1(X1,u1_struct_0(sK3))
    | ~ m1_subset_1(X0,u1_struct_0(sK3)) ),
    inference(renaming,[status(thm)],[c_988])).

cnf(c_4092,plain,
    ( r1_orders_2(sK3,X0,X1) = iProver_top
    | r2_hidden(X0,k5_waybel_0(sK3,X1)) != iProver_top
    | m1_subset_1(X0,u1_struct_0(sK3)) != iProver_top
    | m1_subset_1(X1,u1_struct_0(sK3)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_989])).

cnf(c_990,plain,
    ( r1_orders_2(sK3,X0,X1) = iProver_top
    | r2_hidden(X0,k5_waybel_0(sK3,X1)) != iProver_top
    | m1_subset_1(X0,u1_struct_0(sK3)) != iProver_top
    | m1_subset_1(X1,u1_struct_0(sK3)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_989])).

cnf(c_15,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(X1))
    | m1_subset_1(k5_waybel_0(X1,X0),k1_zfmisc_1(u1_struct_0(X1)))
    | v2_struct_0(X1)
    | ~ l1_orders_2(X1) ),
    inference(cnf_transformation,[],[f68])).

cnf(c_714,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(X1))
    | m1_subset_1(k5_waybel_0(X1,X0),k1_zfmisc_1(u1_struct_0(X1)))
    | ~ v1_lattice3(X2)
    | ~ l1_orders_2(X2)
    | ~ l1_orders_2(X1)
    | X1 != X2 ),
    inference(resolution_lifted,[status(thm)],[c_2,c_15])).

cnf(c_715,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(X1))
    | m1_subset_1(k5_waybel_0(X1,X0),k1_zfmisc_1(u1_struct_0(X1)))
    | ~ v1_lattice3(X1)
    | ~ l1_orders_2(X1) ),
    inference(unflattening,[status(thm)],[c_714])).

cnf(c_1005,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(X1))
    | m1_subset_1(k5_waybel_0(X1,X0),k1_zfmisc_1(u1_struct_0(X1)))
    | ~ l1_orders_2(X1)
    | sK3 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_715,c_34])).

cnf(c_1006,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(sK3))
    | m1_subset_1(k5_waybel_0(sK3,X0),k1_zfmisc_1(u1_struct_0(sK3)))
    | ~ l1_orders_2(sK3) ),
    inference(unflattening,[status(thm)],[c_1005])).

cnf(c_1010,plain,
    ( m1_subset_1(k5_waybel_0(sK3,X0),k1_zfmisc_1(u1_struct_0(sK3)))
    | ~ m1_subset_1(X0,u1_struct_0(sK3)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_1006,c_32])).

cnf(c_1011,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(sK3))
    | m1_subset_1(k5_waybel_0(sK3,X0),k1_zfmisc_1(u1_struct_0(sK3))) ),
    inference(renaming,[status(thm)],[c_1010])).

cnf(c_4091,plain,
    ( m1_subset_1(X0,u1_struct_0(sK3)) != iProver_top
    | m1_subset_1(k5_waybel_0(sK3,X0),k1_zfmisc_1(u1_struct_0(sK3))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1011])).

cnf(c_0,plain,
    ( ~ r2_hidden(X0,X1)
    | m1_subset_1(X0,X2)
    | ~ m1_subset_1(X1,k1_zfmisc_1(X2)) ),
    inference(cnf_transformation,[],[f53])).

cnf(c_4108,plain,
    ( r2_hidden(X0,X1) != iProver_top
    | m1_subset_1(X0,X2) = iProver_top
    | m1_subset_1(X1,k1_zfmisc_1(X2)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_0])).

cnf(c_4495,plain,
    ( r2_hidden(X0,k5_waybel_0(sK3,X1)) != iProver_top
    | m1_subset_1(X1,u1_struct_0(sK3)) != iProver_top
    | m1_subset_1(X0,u1_struct_0(sK3)) = iProver_top ),
    inference(superposition,[status(thm)],[c_4091,c_4108])).

cnf(c_4811,plain,
    ( r2_hidden(X0,k5_waybel_0(sK3,X1)) != iProver_top
    | r1_orders_2(sK3,X0,X1) = iProver_top
    | m1_subset_1(X1,u1_struct_0(sK3)) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_4092,c_990,c_4495])).

cnf(c_4812,plain,
    ( r1_orders_2(sK3,X0,X1) = iProver_top
    | r2_hidden(X0,k5_waybel_0(sK3,X1)) != iProver_top
    | m1_subset_1(X1,u1_struct_0(sK3)) != iProver_top ),
    inference(renaming,[status(thm)],[c_4811])).

cnf(c_4818,plain,
    ( r2_lattice3(sK3,k5_waybel_0(sK3,X0),X1) = iProver_top
    | r1_orders_2(sK3,sK0(sK3,k5_waybel_0(sK3,X0),X1),X0) = iProver_top
    | m1_subset_1(X0,u1_struct_0(sK3)) != iProver_top
    | m1_subset_1(X1,u1_struct_0(sK3)) != iProver_top ),
    inference(superposition,[status(thm)],[c_4080,c_4812])).

cnf(c_3,plain,
    ( r2_lattice3(X0,X1,X2)
    | ~ r1_orders_2(X0,sK0(X0,X1,X2),X2)
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | ~ l1_orders_2(X0) ),
    inference(cnf_transformation,[],[f59])).

cnf(c_1723,plain,
    ( r2_lattice3(X0,X1,X2)
    | ~ r1_orders_2(X0,sK0(X0,X1,X2),X2)
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | sK3 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_3,c_32])).

cnf(c_1724,plain,
    ( r2_lattice3(sK3,X0,X1)
    | ~ r1_orders_2(sK3,sK0(sK3,X0,X1),X1)
    | ~ m1_subset_1(X1,u1_struct_0(sK3)) ),
    inference(unflattening,[status(thm)],[c_1723])).

cnf(c_4079,plain,
    ( r2_lattice3(sK3,X0,X1) = iProver_top
    | r1_orders_2(sK3,sK0(sK3,X0,X1),X1) != iProver_top
    | m1_subset_1(X1,u1_struct_0(sK3)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1724])).

cnf(c_6223,plain,
    ( r2_lattice3(sK3,k5_waybel_0(sK3,X0),X0) = iProver_top
    | m1_subset_1(X0,u1_struct_0(sK3)) != iProver_top ),
    inference(superposition,[status(thm)],[c_4818,c_4079])).

cnf(c_11,plain,
    ( ~ r2_lattice3(X0,X1,X2)
    | r2_lattice3(X0,X1,sK1(X0,X2,X1))
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | ~ v5_orders_2(X0)
    | ~ l1_orders_2(X0)
    | k1_yellow_0(X0,X1) = X2 ),
    inference(cnf_transformation,[],[f63])).

cnf(c_35,negated_conjecture,
    ( v5_orders_2(sK3) ),
    inference(cnf_transformation,[],[f84])).

cnf(c_1514,plain,
    ( ~ r2_lattice3(X0,X1,X2)
    | r2_lattice3(X0,X1,sK1(X0,X2,X1))
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | ~ l1_orders_2(X0)
    | k1_yellow_0(X0,X1) = X2
    | sK3 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_11,c_35])).

cnf(c_1515,plain,
    ( ~ r2_lattice3(sK3,X0,X1)
    | r2_lattice3(sK3,X0,sK1(sK3,X1,X0))
    | ~ m1_subset_1(X1,u1_struct_0(sK3))
    | ~ l1_orders_2(sK3)
    | k1_yellow_0(sK3,X0) = X1 ),
    inference(unflattening,[status(thm)],[c_1514])).

cnf(c_1519,plain,
    ( ~ m1_subset_1(X1,u1_struct_0(sK3))
    | r2_lattice3(sK3,X0,sK1(sK3,X1,X0))
    | ~ r2_lattice3(sK3,X0,X1)
    | k1_yellow_0(sK3,X0) = X1 ),
    inference(global_propositional_subsumption,[status(thm)],[c_1515,c_32])).

cnf(c_1520,plain,
    ( ~ r2_lattice3(sK3,X0,X1)
    | r2_lattice3(sK3,X0,sK1(sK3,X1,X0))
    | ~ m1_subset_1(X1,u1_struct_0(sK3))
    | k1_yellow_0(sK3,X0) = X1 ),
    inference(renaming,[status(thm)],[c_1519])).

cnf(c_4087,plain,
    ( k1_yellow_0(sK3,X0) = X1
    | r2_lattice3(sK3,X0,X1) != iProver_top
    | r2_lattice3(sK3,X0,sK1(sK3,X1,X0)) = iProver_top
    | m1_subset_1(X1,u1_struct_0(sK3)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1520])).

cnf(c_12,plain,
    ( ~ r2_lattice3(X0,X1,X2)
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | m1_subset_1(sK1(X0,X2,X1),u1_struct_0(X0))
    | ~ v5_orders_2(X0)
    | ~ l1_orders_2(X0)
    | k1_yellow_0(X0,X1) = X2 ),
    inference(cnf_transformation,[],[f62])).

cnf(c_1490,plain,
    ( ~ r2_lattice3(X0,X1,X2)
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | m1_subset_1(sK1(X0,X2,X1),u1_struct_0(X0))
    | ~ l1_orders_2(X0)
    | k1_yellow_0(X0,X1) = X2
    | sK3 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_12,c_35])).

cnf(c_1491,plain,
    ( ~ r2_lattice3(sK3,X0,X1)
    | ~ m1_subset_1(X1,u1_struct_0(sK3))
    | m1_subset_1(sK1(sK3,X1,X0),u1_struct_0(sK3))
    | ~ l1_orders_2(sK3)
    | k1_yellow_0(sK3,X0) = X1 ),
    inference(unflattening,[status(thm)],[c_1490])).

cnf(c_1495,plain,
    ( m1_subset_1(sK1(sK3,X1,X0),u1_struct_0(sK3))
    | ~ m1_subset_1(X1,u1_struct_0(sK3))
    | ~ r2_lattice3(sK3,X0,X1)
    | k1_yellow_0(sK3,X0) = X1 ),
    inference(global_propositional_subsumption,[status(thm)],[c_1491,c_32])).

cnf(c_1496,plain,
    ( ~ r2_lattice3(sK3,X0,X1)
    | ~ m1_subset_1(X1,u1_struct_0(sK3))
    | m1_subset_1(sK1(sK3,X1,X0),u1_struct_0(sK3))
    | k1_yellow_0(sK3,X0) = X1 ),
    inference(renaming,[status(thm)],[c_1495])).

cnf(c_4088,plain,
    ( k1_yellow_0(sK3,X0) = X1
    | r2_lattice3(sK3,X0,X1) != iProver_top
    | m1_subset_1(X1,u1_struct_0(sK3)) != iProver_top
    | m1_subset_1(sK1(sK3,X1,X0),u1_struct_0(sK3)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1496])).

cnf(c_6,plain,
    ( ~ r2_lattice3(X0,X1,X2)
    | r1_orders_2(X0,X3,X2)
    | ~ r2_hidden(X3,X1)
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | ~ m1_subset_1(X3,u1_struct_0(X0))
    | ~ l1_orders_2(X0) ),
    inference(cnf_transformation,[],[f56])).

cnf(c_1674,plain,
    ( ~ r2_lattice3(X0,X1,X2)
    | r1_orders_2(X0,X3,X2)
    | ~ r2_hidden(X3,X1)
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | ~ m1_subset_1(X3,u1_struct_0(X0))
    | sK3 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_6,c_32])).

cnf(c_1675,plain,
    ( ~ r2_lattice3(sK3,X0,X1)
    | r1_orders_2(sK3,X2,X1)
    | ~ r2_hidden(X2,X0)
    | ~ m1_subset_1(X1,u1_struct_0(sK3))
    | ~ m1_subset_1(X2,u1_struct_0(sK3)) ),
    inference(unflattening,[status(thm)],[c_1674])).

cnf(c_4082,plain,
    ( r2_lattice3(sK3,X0,X1) != iProver_top
    | r1_orders_2(sK3,X2,X1) = iProver_top
    | r2_hidden(X2,X0) != iProver_top
    | m1_subset_1(X1,u1_struct_0(sK3)) != iProver_top
    | m1_subset_1(X2,u1_struct_0(sK3)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1675])).

cnf(c_5751,plain,
    ( k1_yellow_0(sK3,X0) = X1
    | r2_lattice3(sK3,X0,X1) != iProver_top
    | r2_lattice3(sK3,X2,sK1(sK3,X1,X0)) != iProver_top
    | r1_orders_2(sK3,X3,sK1(sK3,X1,X0)) = iProver_top
    | r2_hidden(X3,X2) != iProver_top
    | m1_subset_1(X1,u1_struct_0(sK3)) != iProver_top
    | m1_subset_1(X3,u1_struct_0(sK3)) != iProver_top ),
    inference(superposition,[status(thm)],[c_4088,c_4082])).

cnf(c_6754,plain,
    ( k1_yellow_0(sK3,X0) = X1
    | r2_lattice3(sK3,X0,X1) != iProver_top
    | r1_orders_2(sK3,X2,sK1(sK3,X1,X0)) = iProver_top
    | r2_hidden(X2,X0) != iProver_top
    | m1_subset_1(X1,u1_struct_0(sK3)) != iProver_top
    | m1_subset_1(X2,u1_struct_0(sK3)) != iProver_top ),
    inference(superposition,[status(thm)],[c_4087,c_5751])).

cnf(c_10,plain,
    ( ~ r2_lattice3(X0,X1,X2)
    | ~ r1_orders_2(X0,X2,sK1(X0,X2,X1))
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | ~ v5_orders_2(X0)
    | ~ l1_orders_2(X0)
    | k1_yellow_0(X0,X1) = X2 ),
    inference(cnf_transformation,[],[f64])).

cnf(c_1538,plain,
    ( ~ r2_lattice3(X0,X1,X2)
    | ~ r1_orders_2(X0,X2,sK1(X0,X2,X1))
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | ~ l1_orders_2(X0)
    | k1_yellow_0(X0,X1) = X2
    | sK3 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_10,c_35])).

cnf(c_1539,plain,
    ( ~ r2_lattice3(sK3,X0,X1)
    | ~ r1_orders_2(sK3,X1,sK1(sK3,X1,X0))
    | ~ m1_subset_1(X1,u1_struct_0(sK3))
    | ~ l1_orders_2(sK3)
    | k1_yellow_0(sK3,X0) = X1 ),
    inference(unflattening,[status(thm)],[c_1538])).

cnf(c_1543,plain,
    ( ~ m1_subset_1(X1,u1_struct_0(sK3))
    | ~ r1_orders_2(sK3,X1,sK1(sK3,X1,X0))
    | ~ r2_lattice3(sK3,X0,X1)
    | k1_yellow_0(sK3,X0) = X1 ),
    inference(global_propositional_subsumption,[status(thm)],[c_1539,c_32])).

cnf(c_1544,plain,
    ( ~ r2_lattice3(sK3,X0,X1)
    | ~ r1_orders_2(sK3,X1,sK1(sK3,X1,X0))
    | ~ m1_subset_1(X1,u1_struct_0(sK3))
    | k1_yellow_0(sK3,X0) = X1 ),
    inference(renaming,[status(thm)],[c_1543])).

cnf(c_4086,plain,
    ( k1_yellow_0(sK3,X0) = X1
    | r2_lattice3(sK3,X0,X1) != iProver_top
    | r1_orders_2(sK3,X1,sK1(sK3,X1,X0)) != iProver_top
    | m1_subset_1(X1,u1_struct_0(sK3)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1544])).

cnf(c_7026,plain,
    ( k1_yellow_0(sK3,X0) = X1
    | r2_lattice3(sK3,X0,X1) != iProver_top
    | r2_hidden(X1,X0) != iProver_top
    | m1_subset_1(X1,u1_struct_0(sK3)) != iProver_top ),
    inference(superposition,[status(thm)],[c_6754,c_4086])).

cnf(c_7120,plain,
    ( k1_yellow_0(sK3,k5_waybel_0(sK3,X0)) = X0
    | r2_hidden(X0,k5_waybel_0(sK3,X0)) != iProver_top
    | m1_subset_1(X0,u1_struct_0(sK3)) != iProver_top ),
    inference(superposition,[status(thm)],[c_6223,c_7026])).

cnf(c_1,plain,
    ( r1_orders_2(X0,X1,X1)
    | ~ m1_subset_1(X1,u1_struct_0(X0))
    | v2_struct_0(X0)
    | ~ v3_orders_2(X0)
    | ~ l1_orders_2(X0) ),
    inference(cnf_transformation,[],[f54])).

cnf(c_673,plain,
    ( r1_orders_2(X0,X1,X1)
    | ~ m1_subset_1(X1,u1_struct_0(X0))
    | ~ v1_lattice3(X0)
    | ~ v3_orders_2(X0)
    | ~ l1_orders_2(X0) ),
    inference(resolution,[status(thm)],[c_1,c_2])).

cnf(c_37,negated_conjecture,
    ( v3_orders_2(sK3) ),
    inference(cnf_transformation,[],[f82])).

cnf(c_898,plain,
    ( r1_orders_2(X0,X1,X1)
    | ~ m1_subset_1(X1,u1_struct_0(X0))
    | ~ v1_lattice3(X0)
    | ~ l1_orders_2(X0)
    | sK3 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_673,c_37])).

cnf(c_899,plain,
    ( r1_orders_2(sK3,X0,X0)
    | ~ m1_subset_1(X0,u1_struct_0(sK3))
    | ~ v1_lattice3(sK3)
    | ~ l1_orders_2(sK3) ),
    inference(unflattening,[status(thm)],[c_898])).

cnf(c_903,plain,
    ( r1_orders_2(sK3,X0,X0)
    | ~ m1_subset_1(X0,u1_struct_0(sK3)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_899,c_34,c_32])).

cnf(c_19,plain,
    ( ~ r1_orders_2(X0,X1,X2)
    | r2_hidden(X1,k5_waybel_0(X0,X2))
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | ~ m1_subset_1(X1,u1_struct_0(X0))
    | v2_struct_0(X0)
    | ~ l1_orders_2(X0) ),
    inference(cnf_transformation,[],[f73])).

cnf(c_630,plain,
    ( ~ r1_orders_2(X0,X1,X2)
    | r2_hidden(X1,k5_waybel_0(X0,X2))
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | ~ m1_subset_1(X1,u1_struct_0(X0))
    | ~ v1_lattice3(X0)
    | ~ l1_orders_2(X0) ),
    inference(resolution,[status(thm)],[c_19,c_2])).

cnf(c_961,plain,
    ( ~ r1_orders_2(X0,X1,X2)
    | r2_hidden(X1,k5_waybel_0(X0,X2))
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | ~ m1_subset_1(X1,u1_struct_0(X0))
    | ~ l1_orders_2(X0)
    | sK3 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_630,c_34])).

cnf(c_962,plain,
    ( ~ r1_orders_2(sK3,X0,X1)
    | r2_hidden(X0,k5_waybel_0(sK3,X1))
    | ~ m1_subset_1(X0,u1_struct_0(sK3))
    | ~ m1_subset_1(X1,u1_struct_0(sK3))
    | ~ l1_orders_2(sK3) ),
    inference(unflattening,[status(thm)],[c_961])).

cnf(c_966,plain,
    ( ~ m1_subset_1(X1,u1_struct_0(sK3))
    | ~ m1_subset_1(X0,u1_struct_0(sK3))
    | r2_hidden(X0,k5_waybel_0(sK3,X1))
    | ~ r1_orders_2(sK3,X0,X1) ),
    inference(global_propositional_subsumption,[status(thm)],[c_962,c_32])).

cnf(c_967,plain,
    ( ~ r1_orders_2(sK3,X0,X1)
    | r2_hidden(X0,k5_waybel_0(sK3,X1))
    | ~ m1_subset_1(X1,u1_struct_0(sK3))
    | ~ m1_subset_1(X0,u1_struct_0(sK3)) ),
    inference(renaming,[status(thm)],[c_966])).

cnf(c_2060,plain,
    ( r2_hidden(X0,k5_waybel_0(sK3,X1))
    | ~ m1_subset_1(X0,u1_struct_0(sK3))
    | ~ m1_subset_1(X2,u1_struct_0(sK3))
    | ~ m1_subset_1(X1,u1_struct_0(sK3))
    | X1 != X2
    | X0 != X2
    | sK3 != sK3 ),
    inference(resolution_lifted,[status(thm)],[c_903,c_967])).

cnf(c_2061,plain,
    ( r2_hidden(X0,k5_waybel_0(sK3,X0))
    | ~ m1_subset_1(X0,u1_struct_0(sK3)) ),
    inference(unflattening,[status(thm)],[c_2060])).

cnf(c_2062,plain,
    ( r2_hidden(X0,k5_waybel_0(sK3,X0)) = iProver_top
    | m1_subset_1(X0,u1_struct_0(sK3)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2061])).

cnf(c_8274,plain,
    ( k1_yellow_0(sK3,k5_waybel_0(sK3,X0)) = X0
    | m1_subset_1(X0,u1_struct_0(sK3)) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_7120,c_2062])).

cnf(c_8282,plain,
    ( k1_yellow_0(sK3,k5_waybel_0(sK3,sK4)) = sK4 ),
    inference(superposition,[status(thm)],[c_4106,c_8274])).

cnf(c_16,plain,
    ( v12_waybel_0(k5_waybel_0(X0,X1),X0)
    | ~ m1_subset_1(X1,u1_struct_0(X0))
    | ~ v4_orders_2(X0)
    | v2_struct_0(X0)
    | ~ l1_orders_2(X0) ),
    inference(cnf_transformation,[],[f69])).

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
    inference(cnf_transformation,[],[f93])).

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
    inference(cnf_transformation,[],[f81])).

cnf(c_30,negated_conjecture,
    ( v5_waybel_6(sK4,sK3) ),
    inference(cnf_transformation,[],[f89])).

cnf(c_422,plain,
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

cnf(c_423,plain,
    ( v1_waybel_7(k5_waybel_0(sK3,sK4),sK3)
    | ~ m1_subset_1(sK4,u1_struct_0(sK3))
    | ~ v2_lattice3(sK3)
    | ~ v4_orders_2(sK3)
    | ~ v5_orders_2(sK3)
    | ~ v1_lattice3(sK3)
    | ~ v3_orders_2(sK3)
    | ~ l1_orders_2(sK3) ),
    inference(unflattening,[status(thm)],[c_422])).

cnf(c_36,negated_conjecture,
    ( v4_orders_2(sK3) ),
    inference(cnf_transformation,[],[f83])).

cnf(c_33,negated_conjecture,
    ( v2_lattice3(sK3) ),
    inference(cnf_transformation,[],[f86])).

cnf(c_425,plain,
    ( v1_waybel_7(k5_waybel_0(sK3,sK4),sK3) ),
    inference(global_propositional_subsumption,[status(thm)],[c_423,c_37,c_36,c_35,c_34,c_33,c_32,c_31])).

cnf(c_477,plain,
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
    inference(resolution_lifted,[status(thm)],[c_21,c_425])).

cnf(c_478,plain,
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
    inference(unflattening,[status(thm)],[c_477])).

cnf(c_480,plain,
    ( v1_xboole_0(k5_waybel_0(sK3,sK4))
    | v4_waybel_7(k1_yellow_0(sK3,k5_waybel_0(sK3,sK4)),sK3)
    | ~ v1_waybel_0(k5_waybel_0(sK3,sK4),sK3)
    | ~ v12_waybel_0(k5_waybel_0(sK3,sK4),sK3)
    | ~ m1_subset_1(k5_waybel_0(sK3,sK4),k1_zfmisc_1(u1_struct_0(sK3)))
    | ~ m1_subset_1(k1_yellow_0(sK3,k5_waybel_0(sK3,sK4)),u1_struct_0(sK3)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_478,c_37,c_36,c_35,c_34,c_33,c_32])).

cnf(c_481,plain,
    ( v4_waybel_7(k1_yellow_0(sK3,k5_waybel_0(sK3,sK4)),sK3)
    | ~ v1_waybel_0(k5_waybel_0(sK3,sK4),sK3)
    | ~ v12_waybel_0(k5_waybel_0(sK3,sK4),sK3)
    | ~ m1_subset_1(k5_waybel_0(sK3,sK4),k1_zfmisc_1(u1_struct_0(sK3)))
    | ~ m1_subset_1(k1_yellow_0(sK3,k5_waybel_0(sK3,sK4)),u1_struct_0(sK3))
    | v1_xboole_0(k5_waybel_0(sK3,sK4)) ),
    inference(renaming,[status(thm)],[c_480])).

cnf(c_521,plain,
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
    inference(resolution_lifted,[status(thm)],[c_16,c_481])).

cnf(c_522,plain,
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
    inference(unflattening,[status(thm)],[c_521])).

cnf(c_126,plain,
    ( ~ v1_lattice3(sK3)
    | ~ v2_struct_0(sK3)
    | ~ l1_orders_2(sK3) ),
    inference(instantiation,[status(thm)],[c_2])).

cnf(c_526,plain,
    ( v1_xboole_0(k5_waybel_0(sK3,sK4))
    | ~ m1_subset_1(k1_yellow_0(sK3,k5_waybel_0(sK3,sK4)),u1_struct_0(sK3))
    | ~ m1_subset_1(k5_waybel_0(sK3,sK4),k1_zfmisc_1(u1_struct_0(sK3)))
    | ~ m1_subset_1(X0,u1_struct_0(sK3))
    | ~ v1_waybel_0(k5_waybel_0(sK3,sK4),sK3)
    | v4_waybel_7(k1_yellow_0(sK3,k5_waybel_0(sK3,sK4)),sK3)
    | k5_waybel_0(sK3,X0) != k5_waybel_0(sK3,sK4) ),
    inference(global_propositional_subsumption,[status(thm)],[c_522,c_36,c_34,c_32,c_126])).

cnf(c_527,plain,
    ( v4_waybel_7(k1_yellow_0(sK3,k5_waybel_0(sK3,sK4)),sK3)
    | ~ v1_waybel_0(k5_waybel_0(sK3,sK4),sK3)
    | ~ m1_subset_1(X0,u1_struct_0(sK3))
    | ~ m1_subset_1(k5_waybel_0(sK3,sK4),k1_zfmisc_1(u1_struct_0(sK3)))
    | ~ m1_subset_1(k1_yellow_0(sK3,k5_waybel_0(sK3,sK4)),u1_struct_0(sK3))
    | v1_xboole_0(k5_waybel_0(sK3,sK4))
    | k5_waybel_0(sK3,X0) != k5_waybel_0(sK3,sK4) ),
    inference(renaming,[status(thm)],[c_526])).

cnf(c_3507,plain,
    ( v4_waybel_7(k1_yellow_0(sK3,k5_waybel_0(sK3,sK4)),sK3)
    | ~ v1_waybel_0(k5_waybel_0(sK3,sK4),sK3)
    | ~ m1_subset_1(k5_waybel_0(sK3,sK4),k1_zfmisc_1(u1_struct_0(sK3)))
    | ~ m1_subset_1(k1_yellow_0(sK3,k5_waybel_0(sK3,sK4)),u1_struct_0(sK3))
    | v1_xboole_0(k5_waybel_0(sK3,sK4))
    | sP1_iProver_split ),
    inference(splitting,[splitting(split),new_symbols(definition,[])],[c_527])).

cnf(c_4104,plain,
    ( v4_waybel_7(k1_yellow_0(sK3,k5_waybel_0(sK3,sK4)),sK3) = iProver_top
    | v1_waybel_0(k5_waybel_0(sK3,sK4),sK3) != iProver_top
    | m1_subset_1(k5_waybel_0(sK3,sK4),k1_zfmisc_1(u1_struct_0(sK3))) != iProver_top
    | m1_subset_1(k1_yellow_0(sK3,k5_waybel_0(sK3,sK4)),u1_struct_0(sK3)) != iProver_top
    | v1_xboole_0(k5_waybel_0(sK3,sK4)) = iProver_top
    | sP1_iProver_split = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3507])).

cnf(c_44,plain,
    ( m1_subset_1(sK4,u1_struct_0(sK3)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_31])).

cnf(c_3570,plain,
    ( v4_waybel_7(k1_yellow_0(sK3,k5_waybel_0(sK3,sK4)),sK3) = iProver_top
    | v1_waybel_0(k5_waybel_0(sK3,sK4),sK3) != iProver_top
    | m1_subset_1(k5_waybel_0(sK3,sK4),k1_zfmisc_1(u1_struct_0(sK3))) != iProver_top
    | m1_subset_1(k1_yellow_0(sK3,k5_waybel_0(sK3,sK4)),u1_struct_0(sK3)) != iProver_top
    | v1_xboole_0(k5_waybel_0(sK3,sK4)) = iProver_top
    | sP1_iProver_split = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3507])).

cnf(c_17,plain,
    ( v1_waybel_0(k5_waybel_0(X0,X1),X0)
    | ~ m1_subset_1(X1,u1_struct_0(X0))
    | v2_struct_0(X0)
    | ~ v3_orders_2(X0)
    | ~ l1_orders_2(X0) ),
    inference(cnf_transformation,[],[f71])).

cnf(c_653,plain,
    ( v1_waybel_0(k5_waybel_0(X0,X1),X0)
    | ~ m1_subset_1(X1,u1_struct_0(X0))
    | ~ v1_lattice3(X0)
    | ~ v3_orders_2(X0)
    | ~ l1_orders_2(X0) ),
    inference(resolution,[status(thm)],[c_17,c_2])).

cnf(c_916,plain,
    ( v1_waybel_0(k5_waybel_0(X0,X1),X0)
    | ~ m1_subset_1(X1,u1_struct_0(X0))
    | ~ v1_lattice3(X0)
    | ~ l1_orders_2(X0)
    | sK3 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_653,c_37])).

cnf(c_917,plain,
    ( v1_waybel_0(k5_waybel_0(sK3,X0),sK3)
    | ~ m1_subset_1(X0,u1_struct_0(sK3))
    | ~ v1_lattice3(sK3)
    | ~ l1_orders_2(sK3) ),
    inference(unflattening,[status(thm)],[c_916])).

cnf(c_921,plain,
    ( v1_waybel_0(k5_waybel_0(sK3,X0),sK3)
    | ~ m1_subset_1(X0,u1_struct_0(sK3)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_917,c_34,c_32])).

cnf(c_4381,plain,
    ( v1_waybel_0(k5_waybel_0(sK3,sK4),sK3)
    | ~ m1_subset_1(sK4,u1_struct_0(sK3)) ),
    inference(instantiation,[status(thm)],[c_921])).

cnf(c_4382,plain,
    ( v1_waybel_0(k5_waybel_0(sK3,sK4),sK3) = iProver_top
    | m1_subset_1(sK4,u1_struct_0(sK3)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_4381])).

cnf(c_18,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(X1))
    | ~ v1_xboole_0(k5_waybel_0(X1,X0))
    | v2_struct_0(X1)
    | ~ v3_orders_2(X1)
    | ~ l1_orders_2(X1) ),
    inference(cnf_transformation,[],[f70])).

cnf(c_693,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(X1))
    | ~ v1_xboole_0(k5_waybel_0(X1,X0))
    | ~ v1_lattice3(X2)
    | ~ v3_orders_2(X1)
    | ~ l1_orders_2(X2)
    | ~ l1_orders_2(X1)
    | X1 != X2 ),
    inference(resolution_lifted,[status(thm)],[c_2,c_18])).

cnf(c_694,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(X1))
    | ~ v1_xboole_0(k5_waybel_0(X1,X0))
    | ~ v1_lattice3(X1)
    | ~ v3_orders_2(X1)
    | ~ l1_orders_2(X1) ),
    inference(unflattening,[status(thm)],[c_693])).

cnf(c_934,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(X1))
    | ~ v1_xboole_0(k5_waybel_0(X1,X0))
    | ~ v1_lattice3(X1)
    | ~ l1_orders_2(X1)
    | sK3 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_694,c_37])).

cnf(c_935,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(sK3))
    | ~ v1_xboole_0(k5_waybel_0(sK3,X0))
    | ~ v1_lattice3(sK3)
    | ~ l1_orders_2(sK3) ),
    inference(unflattening,[status(thm)],[c_934])).

cnf(c_939,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(sK3))
    | ~ v1_xboole_0(k5_waybel_0(sK3,X0)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_935,c_34,c_32])).

cnf(c_4384,plain,
    ( ~ m1_subset_1(sK4,u1_struct_0(sK3))
    | ~ v1_xboole_0(k5_waybel_0(sK3,sK4)) ),
    inference(instantiation,[status(thm)],[c_939])).

cnf(c_4385,plain,
    ( m1_subset_1(sK4,u1_struct_0(sK3)) != iProver_top
    | v1_xboole_0(k5_waybel_0(sK3,sK4)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_4384])).

cnf(c_4387,plain,
    ( m1_subset_1(k5_waybel_0(sK3,sK4),k1_zfmisc_1(u1_struct_0(sK3)))
    | ~ m1_subset_1(sK4,u1_struct_0(sK3)) ),
    inference(instantiation,[status(thm)],[c_1011])).

cnf(c_4388,plain,
    ( m1_subset_1(k5_waybel_0(sK3,sK4),k1_zfmisc_1(u1_struct_0(sK3))) = iProver_top
    | m1_subset_1(sK4,u1_struct_0(sK3)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_4387])).

cnf(c_6739,plain,
    ( m1_subset_1(k1_yellow_0(sK3,k5_waybel_0(sK3,sK4)),u1_struct_0(sK3)) != iProver_top
    | v4_waybel_7(k1_yellow_0(sK3,k5_waybel_0(sK3,sK4)),sK3) = iProver_top
    | sP1_iProver_split = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_4104,c_44,c_3570,c_4382,c_4385,c_4388])).

cnf(c_6740,plain,
    ( v4_waybel_7(k1_yellow_0(sK3,k5_waybel_0(sK3,sK4)),sK3) = iProver_top
    | m1_subset_1(k1_yellow_0(sK3,k5_waybel_0(sK3,sK4)),u1_struct_0(sK3)) != iProver_top
    | sP1_iProver_split = iProver_top ),
    inference(renaming,[status(thm)],[c_6739])).

cnf(c_8374,plain,
    ( v4_waybel_7(sK4,sK3) = iProver_top
    | m1_subset_1(sK4,u1_struct_0(sK3)) != iProver_top
    | sP1_iProver_split = iProver_top ),
    inference(demodulation,[status(thm)],[c_8282,c_6740])).

cnf(c_3506,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(sK3))
    | k5_waybel_0(sK3,X0) != k5_waybel_0(sK3,sK4)
    | ~ sP1_iProver_split ),
    inference(splitting,[splitting(split),new_symbols(definition,[sP1_iProver_split])],[c_527])).

cnf(c_4105,plain,
    ( k5_waybel_0(sK3,X0) != k5_waybel_0(sK3,sK4)
    | m1_subset_1(X0,u1_struct_0(sK3)) != iProver_top
    | sP1_iProver_split != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3506])).

cnf(c_7716,plain,
    ( m1_subset_1(sK4,u1_struct_0(sK3)) != iProver_top
    | sP1_iProver_split != iProver_top ),
    inference(equality_resolution,[status(thm)],[c_4105])).

cnf(c_29,negated_conjecture,
    ( ~ v4_waybel_7(sK4,sK3) ),
    inference(cnf_transformation,[],[f90])).

cnf(c_46,plain,
    ( v4_waybel_7(sK4,sK3) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_29])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_8374,c_7716,c_46,c_44])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : iproveropt_run.sh %d %s
% 0.13/0.34  % Computer   : n025.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 14:03:20 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running in FOF mode
% 3.12/1.00  % SZS status Started for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.12/1.00  
% 3.12/1.00  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 3.12/1.00  
% 3.12/1.00  ------  iProver source info
% 3.12/1.00  
% 3.12/1.00  git: date: 2020-06-30 10:37:57 +0100
% 3.12/1.00  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 3.12/1.00  git: non_committed_changes: false
% 3.12/1.00  git: last_make_outside_of_git: false
% 3.12/1.00  
% 3.12/1.00  ------ 
% 3.12/1.00  
% 3.12/1.00  ------ Input Options
% 3.12/1.00  
% 3.12/1.00  --out_options                           all
% 3.12/1.00  --tptp_safe_out                         true
% 3.12/1.00  --problem_path                          ""
% 3.12/1.00  --include_path                          ""
% 3.12/1.00  --clausifier                            res/vclausify_rel
% 3.12/1.00  --clausifier_options                    --mode clausify
% 3.12/1.00  --stdin                                 false
% 3.12/1.00  --stats_out                             all
% 3.12/1.00  
% 3.12/1.00  ------ General Options
% 3.12/1.00  
% 3.12/1.00  --fof                                   false
% 3.12/1.00  --time_out_real                         305.
% 3.12/1.00  --time_out_virtual                      -1.
% 3.12/1.00  --symbol_type_check                     false
% 3.12/1.00  --clausify_out                          false
% 3.12/1.00  --sig_cnt_out                           false
% 3.12/1.00  --trig_cnt_out                          false
% 3.12/1.00  --trig_cnt_out_tolerance                1.
% 3.12/1.00  --trig_cnt_out_sk_spl                   false
% 3.12/1.00  --abstr_cl_out                          false
% 3.12/1.00  
% 3.12/1.00  ------ Global Options
% 3.12/1.00  
% 3.12/1.00  --schedule                              default
% 3.12/1.00  --add_important_lit                     false
% 3.12/1.00  --prop_solver_per_cl                    1000
% 3.12/1.00  --min_unsat_core                        false
% 3.12/1.00  --soft_assumptions                      false
% 3.12/1.00  --soft_lemma_size                       3
% 3.12/1.00  --prop_impl_unit_size                   0
% 3.12/1.00  --prop_impl_unit                        []
% 3.12/1.00  --share_sel_clauses                     true
% 3.12/1.00  --reset_solvers                         false
% 3.12/1.00  --bc_imp_inh                            [conj_cone]
% 3.12/1.00  --conj_cone_tolerance                   3.
% 3.12/1.00  --extra_neg_conj                        none
% 3.12/1.00  --large_theory_mode                     true
% 3.12/1.00  --prolific_symb_bound                   200
% 3.12/1.00  --lt_threshold                          2000
% 3.12/1.00  --clause_weak_htbl                      true
% 3.12/1.00  --gc_record_bc_elim                     false
% 3.12/1.00  
% 3.12/1.00  ------ Preprocessing Options
% 3.12/1.00  
% 3.12/1.00  --preprocessing_flag                    true
% 3.12/1.00  --time_out_prep_mult                    0.1
% 3.12/1.00  --splitting_mode                        input
% 3.12/1.00  --splitting_grd                         true
% 3.12/1.00  --splitting_cvd                         false
% 3.12/1.00  --splitting_cvd_svl                     false
% 3.12/1.00  --splitting_nvd                         32
% 3.12/1.00  --sub_typing                            true
% 3.12/1.00  --prep_gs_sim                           true
% 3.12/1.00  --prep_unflatten                        true
% 3.12/1.00  --prep_res_sim                          true
% 3.12/1.00  --prep_upred                            true
% 3.12/1.00  --prep_sem_filter                       exhaustive
% 3.12/1.00  --prep_sem_filter_out                   false
% 3.12/1.00  --pred_elim                             true
% 3.12/1.00  --res_sim_input                         true
% 3.12/1.00  --eq_ax_congr_red                       true
% 3.12/1.00  --pure_diseq_elim                       true
% 3.12/1.00  --brand_transform                       false
% 3.12/1.00  --non_eq_to_eq                          false
% 3.12/1.00  --prep_def_merge                        true
% 3.12/1.00  --prep_def_merge_prop_impl              false
% 3.12/1.00  --prep_def_merge_mbd                    true
% 3.12/1.00  --prep_def_merge_tr_red                 false
% 3.12/1.00  --prep_def_merge_tr_cl                  false
% 3.12/1.00  --smt_preprocessing                     true
% 3.12/1.00  --smt_ac_axioms                         fast
% 3.12/1.00  --preprocessed_out                      false
% 3.12/1.00  --preprocessed_stats                    false
% 3.12/1.00  
% 3.12/1.00  ------ Abstraction refinement Options
% 3.12/1.00  
% 3.12/1.00  --abstr_ref                             []
% 3.12/1.00  --abstr_ref_prep                        false
% 3.12/1.00  --abstr_ref_until_sat                   false
% 3.12/1.00  --abstr_ref_sig_restrict                funpre
% 3.12/1.00  --abstr_ref_af_restrict_to_split_sk     false
% 3.12/1.00  --abstr_ref_under                       []
% 3.12/1.00  
% 3.12/1.00  ------ SAT Options
% 3.12/1.00  
% 3.12/1.00  --sat_mode                              false
% 3.12/1.00  --sat_fm_restart_options                ""
% 3.12/1.00  --sat_gr_def                            false
% 3.12/1.00  --sat_epr_types                         true
% 3.12/1.00  --sat_non_cyclic_types                  false
% 3.12/1.00  --sat_finite_models                     false
% 3.12/1.00  --sat_fm_lemmas                         false
% 3.12/1.00  --sat_fm_prep                           false
% 3.12/1.00  --sat_fm_uc_incr                        true
% 3.12/1.00  --sat_out_model                         small
% 3.12/1.00  --sat_out_clauses                       false
% 3.12/1.00  
% 3.12/1.00  ------ QBF Options
% 3.12/1.00  
% 3.12/1.00  --qbf_mode                              false
% 3.12/1.00  --qbf_elim_univ                         false
% 3.12/1.00  --qbf_dom_inst                          none
% 3.12/1.00  --qbf_dom_pre_inst                      false
% 3.12/1.00  --qbf_sk_in                             false
% 3.12/1.00  --qbf_pred_elim                         true
% 3.12/1.00  --qbf_split                             512
% 3.12/1.00  
% 3.12/1.00  ------ BMC1 Options
% 3.12/1.00  
% 3.12/1.00  --bmc1_incremental                      false
% 3.12/1.00  --bmc1_axioms                           reachable_all
% 3.12/1.00  --bmc1_min_bound                        0
% 3.12/1.00  --bmc1_max_bound                        -1
% 3.12/1.00  --bmc1_max_bound_default                -1
% 3.12/1.00  --bmc1_symbol_reachability              true
% 3.12/1.00  --bmc1_property_lemmas                  false
% 3.12/1.00  --bmc1_k_induction                      false
% 3.12/1.00  --bmc1_non_equiv_states                 false
% 3.12/1.00  --bmc1_deadlock                         false
% 3.12/1.00  --bmc1_ucm                              false
% 3.12/1.00  --bmc1_add_unsat_core                   none
% 3.12/1.00  --bmc1_unsat_core_children              false
% 3.12/1.00  --bmc1_unsat_core_extrapolate_axioms    false
% 3.12/1.00  --bmc1_out_stat                         full
% 3.12/1.00  --bmc1_ground_init                      false
% 3.12/1.00  --bmc1_pre_inst_next_state              false
% 3.12/1.00  --bmc1_pre_inst_state                   false
% 3.12/1.00  --bmc1_pre_inst_reach_state             false
% 3.12/1.00  --bmc1_out_unsat_core                   false
% 3.12/1.00  --bmc1_aig_witness_out                  false
% 3.12/1.00  --bmc1_verbose                          false
% 3.12/1.00  --bmc1_dump_clauses_tptp                false
% 3.12/1.00  --bmc1_dump_unsat_core_tptp             false
% 3.12/1.00  --bmc1_dump_file                        -
% 3.12/1.00  --bmc1_ucm_expand_uc_limit              128
% 3.12/1.00  --bmc1_ucm_n_expand_iterations          6
% 3.12/1.00  --bmc1_ucm_extend_mode                  1
% 3.12/1.00  --bmc1_ucm_init_mode                    2
% 3.12/1.00  --bmc1_ucm_cone_mode                    none
% 3.12/1.00  --bmc1_ucm_reduced_relation_type        0
% 3.12/1.00  --bmc1_ucm_relax_model                  4
% 3.12/1.00  --bmc1_ucm_full_tr_after_sat            true
% 3.12/1.00  --bmc1_ucm_expand_neg_assumptions       false
% 3.12/1.00  --bmc1_ucm_layered_model                none
% 3.12/1.00  --bmc1_ucm_max_lemma_size               10
% 3.12/1.00  
% 3.12/1.00  ------ AIG Options
% 3.12/1.00  
% 3.12/1.00  --aig_mode                              false
% 3.12/1.00  
% 3.12/1.00  ------ Instantiation Options
% 3.12/1.00  
% 3.12/1.00  --instantiation_flag                    true
% 3.12/1.00  --inst_sos_flag                         false
% 3.12/1.00  --inst_sos_phase                        true
% 3.12/1.00  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 3.12/1.00  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 3.12/1.00  --inst_lit_sel_side                     num_symb
% 3.12/1.00  --inst_solver_per_active                1400
% 3.12/1.00  --inst_solver_calls_frac                1.
% 3.12/1.00  --inst_passive_queue_type               priority_queues
% 3.12/1.00  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 3.12/1.00  --inst_passive_queues_freq              [25;2]
% 3.12/1.00  --inst_dismatching                      true
% 3.12/1.00  --inst_eager_unprocessed_to_passive     true
% 3.12/1.00  --inst_prop_sim_given                   true
% 3.12/1.00  --inst_prop_sim_new                     false
% 3.12/1.00  --inst_subs_new                         false
% 3.12/1.00  --inst_eq_res_simp                      false
% 3.12/1.00  --inst_subs_given                       false
% 3.12/1.00  --inst_orphan_elimination               true
% 3.12/1.00  --inst_learning_loop_flag               true
% 3.12/1.00  --inst_learning_start                   3000
% 3.12/1.00  --inst_learning_factor                  2
% 3.12/1.00  --inst_start_prop_sim_after_learn       3
% 3.12/1.00  --inst_sel_renew                        solver
% 3.12/1.00  --inst_lit_activity_flag                true
% 3.12/1.00  --inst_restr_to_given                   false
% 3.12/1.00  --inst_activity_threshold               500
% 3.12/1.00  --inst_out_proof                        true
% 3.12/1.00  
% 3.12/1.00  ------ Resolution Options
% 3.12/1.00  
% 3.12/1.00  --resolution_flag                       true
% 3.12/1.00  --res_lit_sel                           adaptive
% 3.12/1.00  --res_lit_sel_side                      none
% 3.12/1.00  --res_ordering                          kbo
% 3.12/1.00  --res_to_prop_solver                    active
% 3.12/1.00  --res_prop_simpl_new                    false
% 3.12/1.00  --res_prop_simpl_given                  true
% 3.12/1.00  --res_passive_queue_type                priority_queues
% 3.12/1.00  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 3.12/1.00  --res_passive_queues_freq               [15;5]
% 3.12/1.00  --res_forward_subs                      full
% 3.12/1.00  --res_backward_subs                     full
% 3.12/1.00  --res_forward_subs_resolution           true
% 3.12/1.00  --res_backward_subs_resolution          true
% 3.12/1.00  --res_orphan_elimination                true
% 3.12/1.00  --res_time_limit                        2.
% 3.12/1.00  --res_out_proof                         true
% 3.12/1.00  
% 3.12/1.00  ------ Superposition Options
% 3.12/1.00  
% 3.12/1.00  --superposition_flag                    true
% 3.12/1.00  --sup_passive_queue_type                priority_queues
% 3.12/1.00  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 3.12/1.00  --sup_passive_queues_freq               [8;1;4]
% 3.12/1.00  --demod_completeness_check              fast
% 3.12/1.00  --demod_use_ground                      true
% 3.12/1.00  --sup_to_prop_solver                    passive
% 3.12/1.00  --sup_prop_simpl_new                    true
% 3.12/1.00  --sup_prop_simpl_given                  true
% 3.12/1.00  --sup_fun_splitting                     false
% 3.12/1.00  --sup_smt_interval                      50000
% 3.12/1.00  
% 3.12/1.00  ------ Superposition Simplification Setup
% 3.12/1.00  
% 3.12/1.00  --sup_indices_passive                   []
% 3.12/1.00  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.12/1.00  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.12/1.00  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.12/1.00  --sup_full_triv                         [TrivRules;PropSubs]
% 3.12/1.00  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.12/1.00  --sup_full_bw                           [BwDemod]
% 3.12/1.00  --sup_immed_triv                        [TrivRules]
% 3.12/1.00  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 3.12/1.00  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.12/1.00  --sup_immed_bw_main                     []
% 3.12/1.00  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 3.12/1.00  --sup_input_triv                        [Unflattening;TrivRules]
% 3.12/1.00  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.12/1.00  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 3.12/1.00  
% 3.12/1.00  ------ Combination Options
% 3.12/1.00  
% 3.12/1.00  --comb_res_mult                         3
% 3.12/1.00  --comb_sup_mult                         2
% 3.12/1.00  --comb_inst_mult                        10
% 3.12/1.00  
% 3.12/1.00  ------ Debug Options
% 3.12/1.00  
% 3.12/1.00  --dbg_backtrace                         false
% 3.12/1.00  --dbg_dump_prop_clauses                 false
% 3.12/1.00  --dbg_dump_prop_clauses_file            -
% 3.12/1.00  --dbg_out_stat                          false
% 3.12/1.00  ------ Parsing...
% 3.12/1.00  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 3.12/1.00  
% 3.12/1.00  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe:1:0s pe:2:0s pe:4:0s pe:8:0s pe_e  sf_s  rm: 10 0s  sf_e  pe_s  pe_e 
% 3.12/1.00  
% 3.12/1.00  ------ Preprocessing... gs_s  sp: 2 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 3.12/1.00  
% 3.12/1.00  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 3.12/1.00  ------ Proving...
% 3.12/1.00  ------ Problem Properties 
% 3.12/1.00  
% 3.12/1.00  
% 3.12/1.00  clauses                                 30
% 3.12/1.00  conjectures                             2
% 3.12/1.00  EPR                                     1
% 3.12/1.00  Horn                                    22
% 3.12/1.00  unary                                   2
% 3.12/1.00  binary                                  4
% 3.12/1.00  lits                                    102
% 3.12/1.00  lits eq                                 6
% 3.12/1.00  fd_pure                                 0
% 3.12/1.00  fd_pseudo                               0
% 3.12/1.00  fd_cond                                 0
% 3.12/1.00  fd_pseudo_cond                          3
% 3.12/1.00  AC symbols                              0
% 3.12/1.00  
% 3.12/1.00  ------ Schedule dynamic 5 is on 
% 3.12/1.00  
% 3.12/1.00  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" Time Limit: 10.
% 3.12/1.00  
% 3.12/1.00  
% 3.12/1.00  ------ 
% 3.12/1.00  Current options:
% 3.12/1.00  ------ 
% 3.12/1.00  
% 3.12/1.00  ------ Input Options
% 3.12/1.00  
% 3.12/1.00  --out_options                           all
% 3.12/1.00  --tptp_safe_out                         true
% 3.12/1.00  --problem_path                          ""
% 3.12/1.00  --include_path                          ""
% 3.12/1.00  --clausifier                            res/vclausify_rel
% 3.12/1.00  --clausifier_options                    --mode clausify
% 3.12/1.00  --stdin                                 false
% 3.12/1.00  --stats_out                             all
% 3.12/1.00  
% 3.12/1.00  ------ General Options
% 3.12/1.00  
% 3.12/1.00  --fof                                   false
% 3.12/1.00  --time_out_real                         305.
% 3.12/1.00  --time_out_virtual                      -1.
% 3.12/1.00  --symbol_type_check                     false
% 3.12/1.00  --clausify_out                          false
% 3.12/1.00  --sig_cnt_out                           false
% 3.12/1.00  --trig_cnt_out                          false
% 3.12/1.00  --trig_cnt_out_tolerance                1.
% 3.12/1.00  --trig_cnt_out_sk_spl                   false
% 3.12/1.00  --abstr_cl_out                          false
% 3.12/1.00  
% 3.12/1.00  ------ Global Options
% 3.12/1.00  
% 3.12/1.00  --schedule                              default
% 3.12/1.00  --add_important_lit                     false
% 3.12/1.00  --prop_solver_per_cl                    1000
% 3.12/1.00  --min_unsat_core                        false
% 3.12/1.00  --soft_assumptions                      false
% 3.12/1.00  --soft_lemma_size                       3
% 3.12/1.00  --prop_impl_unit_size                   0
% 3.12/1.00  --prop_impl_unit                        []
% 3.12/1.00  --share_sel_clauses                     true
% 3.12/1.00  --reset_solvers                         false
% 3.12/1.00  --bc_imp_inh                            [conj_cone]
% 3.12/1.00  --conj_cone_tolerance                   3.
% 3.12/1.00  --extra_neg_conj                        none
% 3.12/1.00  --large_theory_mode                     true
% 3.12/1.00  --prolific_symb_bound                   200
% 3.12/1.00  --lt_threshold                          2000
% 3.12/1.00  --clause_weak_htbl                      true
% 3.12/1.00  --gc_record_bc_elim                     false
% 3.12/1.00  
% 3.12/1.00  ------ Preprocessing Options
% 3.12/1.00  
% 3.12/1.00  --preprocessing_flag                    true
% 3.12/1.00  --time_out_prep_mult                    0.1
% 3.12/1.00  --splitting_mode                        input
% 3.12/1.00  --splitting_grd                         true
% 3.12/1.00  --splitting_cvd                         false
% 3.12/1.00  --splitting_cvd_svl                     false
% 3.12/1.00  --splitting_nvd                         32
% 3.12/1.00  --sub_typing                            true
% 3.12/1.00  --prep_gs_sim                           true
% 3.12/1.00  --prep_unflatten                        true
% 3.12/1.00  --prep_res_sim                          true
% 3.12/1.00  --prep_upred                            true
% 3.12/1.00  --prep_sem_filter                       exhaustive
% 3.12/1.00  --prep_sem_filter_out                   false
% 3.12/1.00  --pred_elim                             true
% 3.12/1.00  --res_sim_input                         true
% 3.12/1.00  --eq_ax_congr_red                       true
% 3.12/1.00  --pure_diseq_elim                       true
% 3.12/1.00  --brand_transform                       false
% 3.12/1.00  --non_eq_to_eq                          false
% 3.12/1.00  --prep_def_merge                        true
% 3.12/1.00  --prep_def_merge_prop_impl              false
% 3.12/1.00  --prep_def_merge_mbd                    true
% 3.12/1.00  --prep_def_merge_tr_red                 false
% 3.12/1.00  --prep_def_merge_tr_cl                  false
% 3.12/1.00  --smt_preprocessing                     true
% 3.12/1.00  --smt_ac_axioms                         fast
% 3.12/1.00  --preprocessed_out                      false
% 3.12/1.00  --preprocessed_stats                    false
% 3.12/1.00  
% 3.12/1.00  ------ Abstraction refinement Options
% 3.12/1.00  
% 3.12/1.00  --abstr_ref                             []
% 3.12/1.00  --abstr_ref_prep                        false
% 3.12/1.00  --abstr_ref_until_sat                   false
% 3.12/1.00  --abstr_ref_sig_restrict                funpre
% 3.12/1.00  --abstr_ref_af_restrict_to_split_sk     false
% 3.12/1.00  --abstr_ref_under                       []
% 3.12/1.00  
% 3.12/1.00  ------ SAT Options
% 3.12/1.00  
% 3.12/1.00  --sat_mode                              false
% 3.12/1.00  --sat_fm_restart_options                ""
% 3.12/1.00  --sat_gr_def                            false
% 3.12/1.00  --sat_epr_types                         true
% 3.12/1.00  --sat_non_cyclic_types                  false
% 3.12/1.00  --sat_finite_models                     false
% 3.12/1.00  --sat_fm_lemmas                         false
% 3.12/1.00  --sat_fm_prep                           false
% 3.12/1.00  --sat_fm_uc_incr                        true
% 3.12/1.00  --sat_out_model                         small
% 3.12/1.00  --sat_out_clauses                       false
% 3.12/1.00  
% 3.12/1.00  ------ QBF Options
% 3.12/1.00  
% 3.12/1.00  --qbf_mode                              false
% 3.12/1.00  --qbf_elim_univ                         false
% 3.12/1.00  --qbf_dom_inst                          none
% 3.12/1.00  --qbf_dom_pre_inst                      false
% 3.12/1.00  --qbf_sk_in                             false
% 3.12/1.00  --qbf_pred_elim                         true
% 3.12/1.00  --qbf_split                             512
% 3.12/1.00  
% 3.12/1.00  ------ BMC1 Options
% 3.12/1.00  
% 3.12/1.00  --bmc1_incremental                      false
% 3.12/1.00  --bmc1_axioms                           reachable_all
% 3.12/1.00  --bmc1_min_bound                        0
% 3.12/1.00  --bmc1_max_bound                        -1
% 3.12/1.00  --bmc1_max_bound_default                -1
% 3.12/1.00  --bmc1_symbol_reachability              true
% 3.12/1.00  --bmc1_property_lemmas                  false
% 3.12/1.00  --bmc1_k_induction                      false
% 3.12/1.00  --bmc1_non_equiv_states                 false
% 3.12/1.00  --bmc1_deadlock                         false
% 3.12/1.00  --bmc1_ucm                              false
% 3.12/1.00  --bmc1_add_unsat_core                   none
% 3.12/1.00  --bmc1_unsat_core_children              false
% 3.12/1.00  --bmc1_unsat_core_extrapolate_axioms    false
% 3.12/1.00  --bmc1_out_stat                         full
% 3.12/1.00  --bmc1_ground_init                      false
% 3.12/1.00  --bmc1_pre_inst_next_state              false
% 3.12/1.00  --bmc1_pre_inst_state                   false
% 3.12/1.00  --bmc1_pre_inst_reach_state             false
% 3.12/1.00  --bmc1_out_unsat_core                   false
% 3.12/1.00  --bmc1_aig_witness_out                  false
% 3.12/1.00  --bmc1_verbose                          false
% 3.12/1.00  --bmc1_dump_clauses_tptp                false
% 3.12/1.00  --bmc1_dump_unsat_core_tptp             false
% 3.12/1.00  --bmc1_dump_file                        -
% 3.12/1.00  --bmc1_ucm_expand_uc_limit              128
% 3.12/1.00  --bmc1_ucm_n_expand_iterations          6
% 3.12/1.00  --bmc1_ucm_extend_mode                  1
% 3.12/1.00  --bmc1_ucm_init_mode                    2
% 3.12/1.00  --bmc1_ucm_cone_mode                    none
% 3.12/1.00  --bmc1_ucm_reduced_relation_type        0
% 3.12/1.00  --bmc1_ucm_relax_model                  4
% 3.12/1.00  --bmc1_ucm_full_tr_after_sat            true
% 3.12/1.00  --bmc1_ucm_expand_neg_assumptions       false
% 3.12/1.00  --bmc1_ucm_layered_model                none
% 3.12/1.00  --bmc1_ucm_max_lemma_size               10
% 3.12/1.00  
% 3.12/1.00  ------ AIG Options
% 3.12/1.00  
% 3.12/1.00  --aig_mode                              false
% 3.12/1.00  
% 3.12/1.00  ------ Instantiation Options
% 3.12/1.00  
% 3.12/1.00  --instantiation_flag                    true
% 3.12/1.00  --inst_sos_flag                         false
% 3.12/1.00  --inst_sos_phase                        true
% 3.12/1.00  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 3.12/1.00  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 3.12/1.00  --inst_lit_sel_side                     none
% 3.12/1.00  --inst_solver_per_active                1400
% 3.12/1.00  --inst_solver_calls_frac                1.
% 3.12/1.00  --inst_passive_queue_type               priority_queues
% 3.12/1.00  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 3.12/1.00  --inst_passive_queues_freq              [25;2]
% 3.12/1.00  --inst_dismatching                      true
% 3.12/1.00  --inst_eager_unprocessed_to_passive     true
% 3.12/1.00  --inst_prop_sim_given                   true
% 3.12/1.00  --inst_prop_sim_new                     false
% 3.12/1.00  --inst_subs_new                         false
% 3.12/1.00  --inst_eq_res_simp                      false
% 3.12/1.00  --inst_subs_given                       false
% 3.12/1.00  --inst_orphan_elimination               true
% 3.12/1.00  --inst_learning_loop_flag               true
% 3.12/1.00  --inst_learning_start                   3000
% 3.12/1.00  --inst_learning_factor                  2
% 3.12/1.00  --inst_start_prop_sim_after_learn       3
% 3.12/1.00  --inst_sel_renew                        solver
% 3.12/1.00  --inst_lit_activity_flag                true
% 3.12/1.00  --inst_restr_to_given                   false
% 3.12/1.00  --inst_activity_threshold               500
% 3.12/1.00  --inst_out_proof                        true
% 3.12/1.00  
% 3.12/1.00  ------ Resolution Options
% 3.12/1.00  
% 3.12/1.00  --resolution_flag                       false
% 3.12/1.00  --res_lit_sel                           adaptive
% 3.12/1.00  --res_lit_sel_side                      none
% 3.12/1.00  --res_ordering                          kbo
% 3.12/1.00  --res_to_prop_solver                    active
% 3.12/1.00  --res_prop_simpl_new                    false
% 3.12/1.00  --res_prop_simpl_given                  true
% 3.12/1.00  --res_passive_queue_type                priority_queues
% 3.12/1.00  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 3.12/1.00  --res_passive_queues_freq               [15;5]
% 3.12/1.00  --res_forward_subs                      full
% 3.12/1.00  --res_backward_subs                     full
% 3.12/1.00  --res_forward_subs_resolution           true
% 3.12/1.00  --res_backward_subs_resolution          true
% 3.12/1.00  --res_orphan_elimination                true
% 3.12/1.00  --res_time_limit                        2.
% 3.12/1.00  --res_out_proof                         true
% 3.12/1.00  
% 3.12/1.00  ------ Superposition Options
% 3.12/1.00  
% 3.12/1.00  --superposition_flag                    true
% 3.12/1.00  --sup_passive_queue_type                priority_queues
% 3.12/1.00  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 3.12/1.00  --sup_passive_queues_freq               [8;1;4]
% 3.12/1.00  --demod_completeness_check              fast
% 3.12/1.00  --demod_use_ground                      true
% 3.12/1.00  --sup_to_prop_solver                    passive
% 3.12/1.00  --sup_prop_simpl_new                    true
% 3.12/1.00  --sup_prop_simpl_given                  true
% 3.12/1.00  --sup_fun_splitting                     false
% 3.12/1.00  --sup_smt_interval                      50000
% 3.12/1.00  
% 3.12/1.00  ------ Superposition Simplification Setup
% 3.12/1.00  
% 3.12/1.00  --sup_indices_passive                   []
% 3.12/1.00  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.12/1.00  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.12/1.00  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.12/1.00  --sup_full_triv                         [TrivRules;PropSubs]
% 3.12/1.00  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.12/1.00  --sup_full_bw                           [BwDemod]
% 3.12/1.00  --sup_immed_triv                        [TrivRules]
% 3.12/1.00  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 3.12/1.00  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.12/1.00  --sup_immed_bw_main                     []
% 3.12/1.00  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 3.12/1.00  --sup_input_triv                        [Unflattening;TrivRules]
% 3.12/1.00  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.12/1.00  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 3.12/1.00  
% 3.12/1.00  ------ Combination Options
% 3.12/1.00  
% 3.12/1.00  --comb_res_mult                         3
% 3.12/1.00  --comb_sup_mult                         2
% 3.12/1.00  --comb_inst_mult                        10
% 3.12/1.00  
% 3.12/1.00  ------ Debug Options
% 3.12/1.00  
% 3.12/1.00  --dbg_backtrace                         false
% 3.12/1.00  --dbg_dump_prop_clauses                 false
% 3.12/1.00  --dbg_dump_prop_clauses_file            -
% 3.12/1.00  --dbg_out_stat                          false
% 3.12/1.00  
% 3.12/1.00  
% 3.12/1.00  
% 3.12/1.00  
% 3.12/1.00  ------ Proving...
% 3.12/1.00  
% 3.12/1.00  
% 3.12/1.00  % SZS status Theorem for theBenchmark.p
% 3.12/1.00  
% 3.12/1.00  % SZS output start CNFRefutation for theBenchmark.p
% 3.12/1.00  
% 3.12/1.00  fof(f12,conjecture,(
% 3.12/1.00    ! [X0] : ((l1_orders_2(X0) & v2_lattice3(X0) & v1_lattice3(X0) & v5_orders_2(X0) & v4_orders_2(X0) & v3_orders_2(X0)) => ! [X1] : (m1_subset_1(X1,u1_struct_0(X0)) => (v5_waybel_6(X1,X0) => v4_waybel_7(X1,X0))))),
% 3.12/1.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.12/1.00  
% 3.12/1.00  fof(f13,negated_conjecture,(
% 3.12/1.00    ~! [X0] : ((l1_orders_2(X0) & v2_lattice3(X0) & v1_lattice3(X0) & v5_orders_2(X0) & v4_orders_2(X0) & v3_orders_2(X0)) => ! [X1] : (m1_subset_1(X1,u1_struct_0(X0)) => (v5_waybel_6(X1,X0) => v4_waybel_7(X1,X0))))),
% 3.12/1.00    inference(negated_conjecture,[],[f12])).
% 3.12/1.00  
% 3.12/1.00  fof(f37,plain,(
% 3.12/1.00    ? [X0] : (? [X1] : ((~v4_waybel_7(X1,X0) & v5_waybel_6(X1,X0)) & m1_subset_1(X1,u1_struct_0(X0))) & (l1_orders_2(X0) & v2_lattice3(X0) & v1_lattice3(X0) & v5_orders_2(X0) & v4_orders_2(X0) & v3_orders_2(X0)))),
% 3.12/1.00    inference(ennf_transformation,[],[f13])).
% 3.12/1.00  
% 3.12/1.00  fof(f38,plain,(
% 3.12/1.00    ? [X0] : (? [X1] : (~v4_waybel_7(X1,X0) & v5_waybel_6(X1,X0) & m1_subset_1(X1,u1_struct_0(X0))) & l1_orders_2(X0) & v2_lattice3(X0) & v1_lattice3(X0) & v5_orders_2(X0) & v4_orders_2(X0) & v3_orders_2(X0))),
% 3.12/1.00    inference(flattening,[],[f37])).
% 3.12/1.00  
% 3.12/1.00  fof(f51,plain,(
% 3.12/1.00    ( ! [X0] : (? [X1] : (~v4_waybel_7(X1,X0) & v5_waybel_6(X1,X0) & m1_subset_1(X1,u1_struct_0(X0))) => (~v4_waybel_7(sK4,X0) & v5_waybel_6(sK4,X0) & m1_subset_1(sK4,u1_struct_0(X0)))) )),
% 3.12/1.00    introduced(choice_axiom,[])).
% 3.12/1.00  
% 3.12/1.00  fof(f50,plain,(
% 3.12/1.00    ? [X0] : (? [X1] : (~v4_waybel_7(X1,X0) & v5_waybel_6(X1,X0) & m1_subset_1(X1,u1_struct_0(X0))) & l1_orders_2(X0) & v2_lattice3(X0) & v1_lattice3(X0) & v5_orders_2(X0) & v4_orders_2(X0) & v3_orders_2(X0)) => (? [X1] : (~v4_waybel_7(X1,sK3) & v5_waybel_6(X1,sK3) & m1_subset_1(X1,u1_struct_0(sK3))) & l1_orders_2(sK3) & v2_lattice3(sK3) & v1_lattice3(sK3) & v5_orders_2(sK3) & v4_orders_2(sK3) & v3_orders_2(sK3))),
% 3.12/1.00    introduced(choice_axiom,[])).
% 3.12/1.00  
% 3.12/1.00  fof(f52,plain,(
% 3.12/1.00    (~v4_waybel_7(sK4,sK3) & v5_waybel_6(sK4,sK3) & m1_subset_1(sK4,u1_struct_0(sK3))) & l1_orders_2(sK3) & v2_lattice3(sK3) & v1_lattice3(sK3) & v5_orders_2(sK3) & v4_orders_2(sK3) & v3_orders_2(sK3)),
% 3.12/1.00    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3,sK4])],[f38,f51,f50])).
% 3.12/1.00  
% 3.12/1.00  fof(f88,plain,(
% 3.12/1.00    m1_subset_1(sK4,u1_struct_0(sK3))),
% 3.12/1.00    inference(cnf_transformation,[],[f52])).
% 3.12/1.00  
% 3.12/1.00  fof(f4,axiom,(
% 3.12/1.00    ! [X0] : (l1_orders_2(X0) => ! [X1,X2] : (m1_subset_1(X2,u1_struct_0(X0)) => (r2_lattice3(X0,X1,X2) <=> ! [X3] : (m1_subset_1(X3,u1_struct_0(X0)) => (r2_hidden(X3,X1) => r1_orders_2(X0,X3,X2))))))),
% 3.12/1.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.12/1.00  
% 3.12/1.00  fof(f21,plain,(
% 3.12/1.00    ! [X0] : (! [X1,X2] : ((r2_lattice3(X0,X1,X2) <=> ! [X3] : ((r1_orders_2(X0,X3,X2) | ~r2_hidden(X3,X1)) | ~m1_subset_1(X3,u1_struct_0(X0)))) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~l1_orders_2(X0))),
% 3.12/1.00    inference(ennf_transformation,[],[f4])).
% 3.12/1.00  
% 3.12/1.00  fof(f22,plain,(
% 3.12/1.00    ! [X0] : (! [X1,X2] : ((r2_lattice3(X0,X1,X2) <=> ! [X3] : (r1_orders_2(X0,X3,X2) | ~r2_hidden(X3,X1) | ~m1_subset_1(X3,u1_struct_0(X0)))) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~l1_orders_2(X0))),
% 3.12/1.00    inference(flattening,[],[f21])).
% 3.12/1.00  
% 3.12/1.00  fof(f39,plain,(
% 3.12/1.00    ! [X0] : (! [X1,X2] : (((r2_lattice3(X0,X1,X2) | ? [X3] : (~r1_orders_2(X0,X3,X2) & r2_hidden(X3,X1) & m1_subset_1(X3,u1_struct_0(X0)))) & (! [X3] : (r1_orders_2(X0,X3,X2) | ~r2_hidden(X3,X1) | ~m1_subset_1(X3,u1_struct_0(X0))) | ~r2_lattice3(X0,X1,X2))) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~l1_orders_2(X0))),
% 3.12/1.00    inference(nnf_transformation,[],[f22])).
% 3.12/1.00  
% 3.12/1.00  fof(f40,plain,(
% 3.12/1.00    ! [X0] : (! [X1,X2] : (((r2_lattice3(X0,X1,X2) | ? [X3] : (~r1_orders_2(X0,X3,X2) & r2_hidden(X3,X1) & m1_subset_1(X3,u1_struct_0(X0)))) & (! [X4] : (r1_orders_2(X0,X4,X2) | ~r2_hidden(X4,X1) | ~m1_subset_1(X4,u1_struct_0(X0))) | ~r2_lattice3(X0,X1,X2))) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~l1_orders_2(X0))),
% 3.12/1.00    inference(rectify,[],[f39])).
% 3.12/1.00  
% 3.12/1.00  fof(f41,plain,(
% 3.12/1.00    ! [X2,X1,X0] : (? [X3] : (~r1_orders_2(X0,X3,X2) & r2_hidden(X3,X1) & m1_subset_1(X3,u1_struct_0(X0))) => (~r1_orders_2(X0,sK0(X0,X1,X2),X2) & r2_hidden(sK0(X0,X1,X2),X1) & m1_subset_1(sK0(X0,X1,X2),u1_struct_0(X0))))),
% 3.12/1.00    introduced(choice_axiom,[])).
% 3.12/1.00  
% 3.12/1.00  fof(f42,plain,(
% 3.12/1.00    ! [X0] : (! [X1,X2] : (((r2_lattice3(X0,X1,X2) | (~r1_orders_2(X0,sK0(X0,X1,X2),X2) & r2_hidden(sK0(X0,X1,X2),X1) & m1_subset_1(sK0(X0,X1,X2),u1_struct_0(X0)))) & (! [X4] : (r1_orders_2(X0,X4,X2) | ~r2_hidden(X4,X1) | ~m1_subset_1(X4,u1_struct_0(X0))) | ~r2_lattice3(X0,X1,X2))) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~l1_orders_2(X0))),
% 3.12/1.00    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f40,f41])).
% 3.12/1.00  
% 3.12/1.00  fof(f58,plain,(
% 3.12/1.00    ( ! [X2,X0,X1] : (r2_lattice3(X0,X1,X2) | r2_hidden(sK0(X0,X1,X2),X1) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~l1_orders_2(X0)) )),
% 3.12/1.00    inference(cnf_transformation,[],[f42])).
% 3.12/1.00  
% 3.12/1.00  fof(f87,plain,(
% 3.12/1.00    l1_orders_2(sK3)),
% 3.12/1.00    inference(cnf_transformation,[],[f52])).
% 3.12/1.00  
% 3.12/1.00  fof(f9,axiom,(
% 3.12/1.00    ! [X0] : ((l1_orders_2(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,u1_struct_0(X0)) => ! [X2] : (m1_subset_1(X2,u1_struct_0(X0)) => (r2_hidden(X2,k5_waybel_0(X0,X1)) <=> r1_orders_2(X0,X2,X1)))))),
% 3.12/1.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.12/1.00  
% 3.12/1.00  fof(f31,plain,(
% 3.12/1.00    ! [X0] : (! [X1] : (! [X2] : ((r2_hidden(X2,k5_waybel_0(X0,X1)) <=> r1_orders_2(X0,X2,X1)) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~m1_subset_1(X1,u1_struct_0(X0))) | (~l1_orders_2(X0) | v2_struct_0(X0)))),
% 3.12/1.00    inference(ennf_transformation,[],[f9])).
% 3.12/1.00  
% 3.12/1.00  fof(f32,plain,(
% 3.12/1.00    ! [X0] : (! [X1] : (! [X2] : ((r2_hidden(X2,k5_waybel_0(X0,X1)) <=> r1_orders_2(X0,X2,X1)) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~l1_orders_2(X0) | v2_struct_0(X0))),
% 3.12/1.00    inference(flattening,[],[f31])).
% 3.12/1.00  
% 3.12/1.00  fof(f45,plain,(
% 3.12/1.00    ! [X0] : (! [X1] : (! [X2] : (((r2_hidden(X2,k5_waybel_0(X0,X1)) | ~r1_orders_2(X0,X2,X1)) & (r1_orders_2(X0,X2,X1) | ~r2_hidden(X2,k5_waybel_0(X0,X1)))) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~l1_orders_2(X0) | v2_struct_0(X0))),
% 3.12/1.00    inference(nnf_transformation,[],[f32])).
% 3.12/1.00  
% 3.12/1.00  fof(f72,plain,(
% 3.12/1.00    ( ! [X2,X0,X1] : (r1_orders_2(X0,X2,X1) | ~r2_hidden(X2,k5_waybel_0(X0,X1)) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_orders_2(X0) | v2_struct_0(X0)) )),
% 3.12/1.00    inference(cnf_transformation,[],[f45])).
% 3.12/1.00  
% 3.12/1.00  fof(f3,axiom,(
% 3.12/1.00    ! [X0] : (l1_orders_2(X0) => (v1_lattice3(X0) => ~v2_struct_0(X0)))),
% 3.12/1.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.12/1.00  
% 3.12/1.00  fof(f19,plain,(
% 3.12/1.00    ! [X0] : ((~v2_struct_0(X0) | ~v1_lattice3(X0)) | ~l1_orders_2(X0))),
% 3.12/1.00    inference(ennf_transformation,[],[f3])).
% 3.12/1.00  
% 3.12/1.00  fof(f20,plain,(
% 3.12/1.00    ! [X0] : (~v2_struct_0(X0) | ~v1_lattice3(X0) | ~l1_orders_2(X0))),
% 3.12/1.00    inference(flattening,[],[f19])).
% 3.12/1.00  
% 3.12/1.00  fof(f55,plain,(
% 3.12/1.00    ( ! [X0] : (~v2_struct_0(X0) | ~v1_lattice3(X0) | ~l1_orders_2(X0)) )),
% 3.12/1.00    inference(cnf_transformation,[],[f20])).
% 3.12/1.00  
% 3.12/1.00  fof(f85,plain,(
% 3.12/1.00    v1_lattice3(sK3)),
% 3.12/1.00    inference(cnf_transformation,[],[f52])).
% 3.12/1.00  
% 3.12/1.00  fof(f6,axiom,(
% 3.12/1.00    ! [X0,X1] : ((m1_subset_1(X1,u1_struct_0(X0)) & l1_orders_2(X0) & ~v2_struct_0(X0)) => m1_subset_1(k5_waybel_0(X0,X1),k1_zfmisc_1(u1_struct_0(X0))))),
% 3.12/1.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.12/1.00  
% 3.12/1.00  fof(f25,plain,(
% 3.12/1.00    ! [X0,X1] : (m1_subset_1(k5_waybel_0(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) | (~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_orders_2(X0) | v2_struct_0(X0)))),
% 3.12/1.00    inference(ennf_transformation,[],[f6])).
% 3.12/1.00  
% 3.12/1.00  fof(f26,plain,(
% 3.12/1.00    ! [X0,X1] : (m1_subset_1(k5_waybel_0(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_orders_2(X0) | v2_struct_0(X0))),
% 3.12/1.00    inference(flattening,[],[f25])).
% 3.12/1.00  
% 3.12/1.00  fof(f68,plain,(
% 3.12/1.00    ( ! [X0,X1] : (m1_subset_1(k5_waybel_0(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_orders_2(X0) | v2_struct_0(X0)) )),
% 3.12/1.00    inference(cnf_transformation,[],[f26])).
% 3.12/1.00  
% 3.12/1.00  fof(f1,axiom,(
% 3.12/1.00    ! [X0,X1,X2] : ((m1_subset_1(X1,k1_zfmisc_1(X2)) & r2_hidden(X0,X1)) => m1_subset_1(X0,X2))),
% 3.12/1.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.12/1.00  
% 3.12/1.00  fof(f15,plain,(
% 3.12/1.00    ! [X0,X1,X2] : (m1_subset_1(X0,X2) | (~m1_subset_1(X1,k1_zfmisc_1(X2)) | ~r2_hidden(X0,X1)))),
% 3.12/1.00    inference(ennf_transformation,[],[f1])).
% 3.12/1.00  
% 3.12/1.00  fof(f16,plain,(
% 3.12/1.00    ! [X0,X1,X2] : (m1_subset_1(X0,X2) | ~m1_subset_1(X1,k1_zfmisc_1(X2)) | ~r2_hidden(X0,X1))),
% 3.12/1.00    inference(flattening,[],[f15])).
% 3.12/1.00  
% 3.12/1.00  fof(f53,plain,(
% 3.12/1.00    ( ! [X2,X0,X1] : (m1_subset_1(X0,X2) | ~m1_subset_1(X1,k1_zfmisc_1(X2)) | ~r2_hidden(X0,X1)) )),
% 3.12/1.00    inference(cnf_transformation,[],[f16])).
% 3.12/1.00  
% 3.12/1.00  fof(f59,plain,(
% 3.12/1.00    ( ! [X2,X0,X1] : (r2_lattice3(X0,X1,X2) | ~r1_orders_2(X0,sK0(X0,X1,X2),X2) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~l1_orders_2(X0)) )),
% 3.12/1.00    inference(cnf_transformation,[],[f42])).
% 3.12/1.00  
% 3.12/1.00  fof(f5,axiom,(
% 3.12/1.00    ! [X0] : ((l1_orders_2(X0) & v5_orders_2(X0)) => ! [X1] : (m1_subset_1(X1,u1_struct_0(X0)) => ! [X2] : (((! [X3] : (m1_subset_1(X3,u1_struct_0(X0)) => (r2_lattice3(X0,X2,X3) => r1_orders_2(X0,X1,X3))) & r2_lattice3(X0,X2,X1)) => (r1_yellow_0(X0,X2) & k1_yellow_0(X0,X2) = X1)) & ((r1_yellow_0(X0,X2) & k1_yellow_0(X0,X2) = X1) => (! [X3] : (m1_subset_1(X3,u1_struct_0(X0)) => (r2_lattice3(X0,X2,X3) => r1_orders_2(X0,X1,X3))) & r2_lattice3(X0,X2,X1))))))),
% 3.12/1.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.12/1.00  
% 3.12/1.00  fof(f14,plain,(
% 3.12/1.00    ! [X0] : ((l1_orders_2(X0) & v5_orders_2(X0)) => ! [X1] : (m1_subset_1(X1,u1_struct_0(X0)) => ! [X2] : (((! [X3] : (m1_subset_1(X3,u1_struct_0(X0)) => (r2_lattice3(X0,X2,X3) => r1_orders_2(X0,X1,X3))) & r2_lattice3(X0,X2,X1)) => (r1_yellow_0(X0,X2) & k1_yellow_0(X0,X2) = X1)) & ((r1_yellow_0(X0,X2) & k1_yellow_0(X0,X2) = X1) => (! [X4] : (m1_subset_1(X4,u1_struct_0(X0)) => (r2_lattice3(X0,X2,X4) => r1_orders_2(X0,X1,X4))) & r2_lattice3(X0,X2,X1))))))),
% 3.12/1.00    inference(rectify,[],[f5])).
% 3.12/1.00  
% 3.12/1.00  fof(f23,plain,(
% 3.12/1.00    ! [X0] : (! [X1] : (! [X2] : (((r1_yellow_0(X0,X2) & k1_yellow_0(X0,X2) = X1) | (? [X3] : ((~r1_orders_2(X0,X1,X3) & r2_lattice3(X0,X2,X3)) & m1_subset_1(X3,u1_struct_0(X0))) | ~r2_lattice3(X0,X2,X1))) & ((! [X4] : ((r1_orders_2(X0,X1,X4) | ~r2_lattice3(X0,X2,X4)) | ~m1_subset_1(X4,u1_struct_0(X0))) & r2_lattice3(X0,X2,X1)) | (~r1_yellow_0(X0,X2) | k1_yellow_0(X0,X2) != X1))) | ~m1_subset_1(X1,u1_struct_0(X0))) | (~l1_orders_2(X0) | ~v5_orders_2(X0)))),
% 3.12/1.00    inference(ennf_transformation,[],[f14])).
% 3.12/1.00  
% 3.12/1.00  fof(f24,plain,(
% 3.12/1.00    ! [X0] : (! [X1] : (! [X2] : (((r1_yellow_0(X0,X2) & k1_yellow_0(X0,X2) = X1) | ? [X3] : (~r1_orders_2(X0,X1,X3) & r2_lattice3(X0,X2,X3) & m1_subset_1(X3,u1_struct_0(X0))) | ~r2_lattice3(X0,X2,X1)) & ((! [X4] : (r1_orders_2(X0,X1,X4) | ~r2_lattice3(X0,X2,X4) | ~m1_subset_1(X4,u1_struct_0(X0))) & r2_lattice3(X0,X2,X1)) | ~r1_yellow_0(X0,X2) | k1_yellow_0(X0,X2) != X1)) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~l1_orders_2(X0) | ~v5_orders_2(X0))),
% 3.12/1.00    inference(flattening,[],[f23])).
% 3.12/1.00  
% 3.12/1.00  fof(f43,plain,(
% 3.12/1.00    ! [X2,X1,X0] : (? [X3] : (~r1_orders_2(X0,X1,X3) & r2_lattice3(X0,X2,X3) & m1_subset_1(X3,u1_struct_0(X0))) => (~r1_orders_2(X0,X1,sK1(X0,X1,X2)) & r2_lattice3(X0,X2,sK1(X0,X1,X2)) & m1_subset_1(sK1(X0,X1,X2),u1_struct_0(X0))))),
% 3.12/1.00    introduced(choice_axiom,[])).
% 3.12/1.00  
% 3.12/1.00  fof(f44,plain,(
% 3.12/1.00    ! [X0] : (! [X1] : (! [X2] : (((r1_yellow_0(X0,X2) & k1_yellow_0(X0,X2) = X1) | (~r1_orders_2(X0,X1,sK1(X0,X1,X2)) & r2_lattice3(X0,X2,sK1(X0,X1,X2)) & m1_subset_1(sK1(X0,X1,X2),u1_struct_0(X0))) | ~r2_lattice3(X0,X2,X1)) & ((! [X4] : (r1_orders_2(X0,X1,X4) | ~r2_lattice3(X0,X2,X4) | ~m1_subset_1(X4,u1_struct_0(X0))) & r2_lattice3(X0,X2,X1)) | ~r1_yellow_0(X0,X2) | k1_yellow_0(X0,X2) != X1)) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~l1_orders_2(X0) | ~v5_orders_2(X0))),
% 3.12/1.00    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1])],[f24,f43])).
% 3.12/1.00  
% 3.12/1.00  fof(f63,plain,(
% 3.12/1.00    ( ! [X2,X0,X1] : (k1_yellow_0(X0,X2) = X1 | r2_lattice3(X0,X2,sK1(X0,X1,X2)) | ~r2_lattice3(X0,X2,X1) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_orders_2(X0) | ~v5_orders_2(X0)) )),
% 3.12/1.00    inference(cnf_transformation,[],[f44])).
% 3.12/1.00  
% 3.12/1.00  fof(f84,plain,(
% 3.12/1.00    v5_orders_2(sK3)),
% 3.12/1.00    inference(cnf_transformation,[],[f52])).
% 3.12/1.00  
% 3.12/1.00  fof(f62,plain,(
% 3.12/1.00    ( ! [X2,X0,X1] : (k1_yellow_0(X0,X2) = X1 | m1_subset_1(sK1(X0,X1,X2),u1_struct_0(X0)) | ~r2_lattice3(X0,X2,X1) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_orders_2(X0) | ~v5_orders_2(X0)) )),
% 3.12/1.00    inference(cnf_transformation,[],[f44])).
% 3.12/1.00  
% 3.12/1.00  fof(f56,plain,(
% 3.12/1.00    ( ! [X4,X2,X0,X1] : (r1_orders_2(X0,X4,X2) | ~r2_hidden(X4,X1) | ~m1_subset_1(X4,u1_struct_0(X0)) | ~r2_lattice3(X0,X1,X2) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~l1_orders_2(X0)) )),
% 3.12/1.00    inference(cnf_transformation,[],[f42])).
% 3.12/1.00  
% 3.12/1.00  fof(f64,plain,(
% 3.12/1.00    ( ! [X2,X0,X1] : (k1_yellow_0(X0,X2) = X1 | ~r1_orders_2(X0,X1,sK1(X0,X1,X2)) | ~r2_lattice3(X0,X2,X1) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_orders_2(X0) | ~v5_orders_2(X0)) )),
% 3.12/1.00    inference(cnf_transformation,[],[f44])).
% 3.12/1.00  
% 3.12/1.00  fof(f2,axiom,(
% 3.12/1.00    ! [X0] : ((l1_orders_2(X0) & v3_orders_2(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,u1_struct_0(X0)) => r1_orders_2(X0,X1,X1)))),
% 3.12/1.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.12/1.00  
% 3.12/1.00  fof(f17,plain,(
% 3.12/1.00    ! [X0] : (! [X1] : (r1_orders_2(X0,X1,X1) | ~m1_subset_1(X1,u1_struct_0(X0))) | (~l1_orders_2(X0) | ~v3_orders_2(X0) | v2_struct_0(X0)))),
% 3.12/1.00    inference(ennf_transformation,[],[f2])).
% 3.12/1.00  
% 3.12/1.00  fof(f18,plain,(
% 3.12/1.00    ! [X0] : (! [X1] : (r1_orders_2(X0,X1,X1) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~l1_orders_2(X0) | ~v3_orders_2(X0) | v2_struct_0(X0))),
% 3.12/1.00    inference(flattening,[],[f17])).
% 3.12/1.00  
% 3.12/1.00  fof(f54,plain,(
% 3.12/1.00    ( ! [X0,X1] : (r1_orders_2(X0,X1,X1) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_orders_2(X0) | ~v3_orders_2(X0) | v2_struct_0(X0)) )),
% 3.12/1.00    inference(cnf_transformation,[],[f18])).
% 3.12/1.00  
% 3.12/1.00  fof(f82,plain,(
% 3.12/1.00    v3_orders_2(sK3)),
% 3.12/1.00    inference(cnf_transformation,[],[f52])).
% 3.12/1.00  
% 3.12/1.00  fof(f73,plain,(
% 3.12/1.00    ( ! [X2,X0,X1] : (r2_hidden(X2,k5_waybel_0(X0,X1)) | ~r1_orders_2(X0,X2,X1) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_orders_2(X0) | v2_struct_0(X0)) )),
% 3.12/1.00    inference(cnf_transformation,[],[f45])).
% 3.12/1.00  
% 3.12/1.00  fof(f7,axiom,(
% 3.12/1.00    ! [X0,X1] : ((m1_subset_1(X1,u1_struct_0(X0)) & l1_orders_2(X0) & v4_orders_2(X0) & ~v2_struct_0(X0)) => v12_waybel_0(k5_waybel_0(X0,X1),X0))),
% 3.12/1.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.12/1.00  
% 3.12/1.00  fof(f27,plain,(
% 3.12/1.00    ! [X0,X1] : (v12_waybel_0(k5_waybel_0(X0,X1),X0) | (~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_orders_2(X0) | ~v4_orders_2(X0) | v2_struct_0(X0)))),
% 3.12/1.00    inference(ennf_transformation,[],[f7])).
% 3.12/1.00  
% 3.12/1.00  fof(f28,plain,(
% 3.12/1.00    ! [X0,X1] : (v12_waybel_0(k5_waybel_0(X0,X1),X0) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_orders_2(X0) | ~v4_orders_2(X0) | v2_struct_0(X0))),
% 3.12/1.00    inference(flattening,[],[f27])).
% 3.12/1.00  
% 3.12/1.00  fof(f69,plain,(
% 3.12/1.00    ( ! [X0,X1] : (v12_waybel_0(k5_waybel_0(X0,X1),X0) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_orders_2(X0) | ~v4_orders_2(X0) | v2_struct_0(X0)) )),
% 3.12/1.00    inference(cnf_transformation,[],[f28])).
% 3.12/1.00  
% 3.12/1.00  fof(f10,axiom,(
% 3.12/1.00    ! [X0] : ((l1_orders_2(X0) & v2_lattice3(X0) & v1_lattice3(X0) & v5_orders_2(X0) & v4_orders_2(X0) & v3_orders_2(X0)) => ! [X1] : (m1_subset_1(X1,u1_struct_0(X0)) => (v4_waybel_7(X1,X0) <=> ? [X2] : (k1_yellow_0(X0,X2) = X1 & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) & v1_waybel_7(X2,X0) & v12_waybel_0(X2,X0) & v1_waybel_0(X2,X0) & ~v1_xboole_0(X2)))))),
% 3.12/1.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.12/1.00  
% 3.12/1.00  fof(f33,plain,(
% 3.12/1.00    ! [X0] : (! [X1] : ((v4_waybel_7(X1,X0) <=> ? [X2] : (k1_yellow_0(X0,X2) = X1 & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) & v1_waybel_7(X2,X0) & v12_waybel_0(X2,X0) & v1_waybel_0(X2,X0) & ~v1_xboole_0(X2))) | ~m1_subset_1(X1,u1_struct_0(X0))) | (~l1_orders_2(X0) | ~v2_lattice3(X0) | ~v1_lattice3(X0) | ~v5_orders_2(X0) | ~v4_orders_2(X0) | ~v3_orders_2(X0)))),
% 3.12/1.00    inference(ennf_transformation,[],[f10])).
% 3.12/1.00  
% 3.12/1.00  fof(f34,plain,(
% 3.12/1.00    ! [X0] : (! [X1] : ((v4_waybel_7(X1,X0) <=> ? [X2] : (k1_yellow_0(X0,X2) = X1 & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) & v1_waybel_7(X2,X0) & v12_waybel_0(X2,X0) & v1_waybel_0(X2,X0) & ~v1_xboole_0(X2))) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~l1_orders_2(X0) | ~v2_lattice3(X0) | ~v1_lattice3(X0) | ~v5_orders_2(X0) | ~v4_orders_2(X0) | ~v3_orders_2(X0))),
% 3.12/1.00    inference(flattening,[],[f33])).
% 3.12/1.00  
% 3.12/1.00  fof(f46,plain,(
% 3.12/1.00    ! [X0] : (! [X1] : (((v4_waybel_7(X1,X0) | ! [X2] : (k1_yellow_0(X0,X2) != X1 | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) | ~v1_waybel_7(X2,X0) | ~v12_waybel_0(X2,X0) | ~v1_waybel_0(X2,X0) | v1_xboole_0(X2))) & (? [X2] : (k1_yellow_0(X0,X2) = X1 & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) & v1_waybel_7(X2,X0) & v12_waybel_0(X2,X0) & v1_waybel_0(X2,X0) & ~v1_xboole_0(X2)) | ~v4_waybel_7(X1,X0))) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~l1_orders_2(X0) | ~v2_lattice3(X0) | ~v1_lattice3(X0) | ~v5_orders_2(X0) | ~v4_orders_2(X0) | ~v3_orders_2(X0))),
% 3.12/1.00    inference(nnf_transformation,[],[f34])).
% 3.12/1.00  
% 3.12/1.00  fof(f47,plain,(
% 3.12/1.00    ! [X0] : (! [X1] : (((v4_waybel_7(X1,X0) | ! [X2] : (k1_yellow_0(X0,X2) != X1 | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) | ~v1_waybel_7(X2,X0) | ~v12_waybel_0(X2,X0) | ~v1_waybel_0(X2,X0) | v1_xboole_0(X2))) & (? [X3] : (k1_yellow_0(X0,X3) = X1 & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) & v1_waybel_7(X3,X0) & v12_waybel_0(X3,X0) & v1_waybel_0(X3,X0) & ~v1_xboole_0(X3)) | ~v4_waybel_7(X1,X0))) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~l1_orders_2(X0) | ~v2_lattice3(X0) | ~v1_lattice3(X0) | ~v5_orders_2(X0) | ~v4_orders_2(X0) | ~v3_orders_2(X0))),
% 3.12/1.00    inference(rectify,[],[f46])).
% 3.12/1.00  
% 3.12/1.00  fof(f48,plain,(
% 3.12/1.00    ! [X1,X0] : (? [X3] : (k1_yellow_0(X0,X3) = X1 & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) & v1_waybel_7(X3,X0) & v12_waybel_0(X3,X0) & v1_waybel_0(X3,X0) & ~v1_xboole_0(X3)) => (k1_yellow_0(X0,sK2(X0,X1)) = X1 & m1_subset_1(sK2(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) & v1_waybel_7(sK2(X0,X1),X0) & v12_waybel_0(sK2(X0,X1),X0) & v1_waybel_0(sK2(X0,X1),X0) & ~v1_xboole_0(sK2(X0,X1))))),
% 3.12/1.00    introduced(choice_axiom,[])).
% 3.12/1.00  
% 3.12/1.00  fof(f49,plain,(
% 3.12/1.00    ! [X0] : (! [X1] : (((v4_waybel_7(X1,X0) | ! [X2] : (k1_yellow_0(X0,X2) != X1 | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) | ~v1_waybel_7(X2,X0) | ~v12_waybel_0(X2,X0) | ~v1_waybel_0(X2,X0) | v1_xboole_0(X2))) & ((k1_yellow_0(X0,sK2(X0,X1)) = X1 & m1_subset_1(sK2(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) & v1_waybel_7(sK2(X0,X1),X0) & v12_waybel_0(sK2(X0,X1),X0) & v1_waybel_0(sK2(X0,X1),X0) & ~v1_xboole_0(sK2(X0,X1))) | ~v4_waybel_7(X1,X0))) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~l1_orders_2(X0) | ~v2_lattice3(X0) | ~v1_lattice3(X0) | ~v5_orders_2(X0) | ~v4_orders_2(X0) | ~v3_orders_2(X0))),
% 3.12/1.00    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2])],[f47,f48])).
% 3.12/1.00  
% 3.12/1.00  fof(f80,plain,(
% 3.12/1.00    ( ! [X2,X0,X1] : (v4_waybel_7(X1,X0) | k1_yellow_0(X0,X2) != X1 | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) | ~v1_waybel_7(X2,X0) | ~v12_waybel_0(X2,X0) | ~v1_waybel_0(X2,X0) | v1_xboole_0(X2) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_orders_2(X0) | ~v2_lattice3(X0) | ~v1_lattice3(X0) | ~v5_orders_2(X0) | ~v4_orders_2(X0) | ~v3_orders_2(X0)) )),
% 3.12/1.00    inference(cnf_transformation,[],[f49])).
% 3.12/1.00  
% 3.12/1.00  fof(f93,plain,(
% 3.12/1.00    ( ! [X2,X0] : (v4_waybel_7(k1_yellow_0(X0,X2),X0) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) | ~v1_waybel_7(X2,X0) | ~v12_waybel_0(X2,X0) | ~v1_waybel_0(X2,X0) | v1_xboole_0(X2) | ~m1_subset_1(k1_yellow_0(X0,X2),u1_struct_0(X0)) | ~l1_orders_2(X0) | ~v2_lattice3(X0) | ~v1_lattice3(X0) | ~v5_orders_2(X0) | ~v4_orders_2(X0) | ~v3_orders_2(X0)) )),
% 3.12/1.00    inference(equality_resolution,[],[f80])).
% 3.12/1.00  
% 3.12/1.00  fof(f11,axiom,(
% 3.12/1.00    ! [X0] : ((l1_orders_2(X0) & v2_lattice3(X0) & v1_lattice3(X0) & v5_orders_2(X0) & v4_orders_2(X0) & v3_orders_2(X0)) => ! [X1] : (m1_subset_1(X1,u1_struct_0(X0)) => (v5_waybel_6(X1,X0) => v1_waybel_7(k5_waybel_0(X0,X1),X0))))),
% 3.12/1.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.12/1.00  
% 3.12/1.00  fof(f35,plain,(
% 3.12/1.00    ! [X0] : (! [X1] : ((v1_waybel_7(k5_waybel_0(X0,X1),X0) | ~v5_waybel_6(X1,X0)) | ~m1_subset_1(X1,u1_struct_0(X0))) | (~l1_orders_2(X0) | ~v2_lattice3(X0) | ~v1_lattice3(X0) | ~v5_orders_2(X0) | ~v4_orders_2(X0) | ~v3_orders_2(X0)))),
% 3.12/1.00    inference(ennf_transformation,[],[f11])).
% 3.12/1.00  
% 3.12/1.00  fof(f36,plain,(
% 3.12/1.00    ! [X0] : (! [X1] : (v1_waybel_7(k5_waybel_0(X0,X1),X0) | ~v5_waybel_6(X1,X0) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~l1_orders_2(X0) | ~v2_lattice3(X0) | ~v1_lattice3(X0) | ~v5_orders_2(X0) | ~v4_orders_2(X0) | ~v3_orders_2(X0))),
% 3.12/1.00    inference(flattening,[],[f35])).
% 3.12/1.00  
% 3.12/1.00  fof(f81,plain,(
% 3.12/1.00    ( ! [X0,X1] : (v1_waybel_7(k5_waybel_0(X0,X1),X0) | ~v5_waybel_6(X1,X0) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_orders_2(X0) | ~v2_lattice3(X0) | ~v1_lattice3(X0) | ~v5_orders_2(X0) | ~v4_orders_2(X0) | ~v3_orders_2(X0)) )),
% 3.12/1.00    inference(cnf_transformation,[],[f36])).
% 3.12/1.00  
% 3.12/1.00  fof(f89,plain,(
% 3.12/1.00    v5_waybel_6(sK4,sK3)),
% 3.12/1.00    inference(cnf_transformation,[],[f52])).
% 3.12/1.00  
% 3.12/1.00  fof(f83,plain,(
% 3.12/1.00    v4_orders_2(sK3)),
% 3.12/1.00    inference(cnf_transformation,[],[f52])).
% 3.12/1.00  
% 3.12/1.00  fof(f86,plain,(
% 3.12/1.00    v2_lattice3(sK3)),
% 3.12/1.00    inference(cnf_transformation,[],[f52])).
% 3.12/1.00  
% 3.12/1.00  fof(f8,axiom,(
% 3.12/1.00    ! [X0,X1] : ((m1_subset_1(X1,u1_struct_0(X0)) & l1_orders_2(X0) & v3_orders_2(X0) & ~v2_struct_0(X0)) => (v1_waybel_0(k5_waybel_0(X0,X1),X0) & ~v1_xboole_0(k5_waybel_0(X0,X1))))),
% 3.12/1.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.12/1.00  
% 3.12/1.00  fof(f29,plain,(
% 3.12/1.00    ! [X0,X1] : ((v1_waybel_0(k5_waybel_0(X0,X1),X0) & ~v1_xboole_0(k5_waybel_0(X0,X1))) | (~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_orders_2(X0) | ~v3_orders_2(X0) | v2_struct_0(X0)))),
% 3.12/1.00    inference(ennf_transformation,[],[f8])).
% 3.12/1.00  
% 3.12/1.00  fof(f30,plain,(
% 3.12/1.00    ! [X0,X1] : ((v1_waybel_0(k5_waybel_0(X0,X1),X0) & ~v1_xboole_0(k5_waybel_0(X0,X1))) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_orders_2(X0) | ~v3_orders_2(X0) | v2_struct_0(X0))),
% 3.12/1.00    inference(flattening,[],[f29])).
% 3.12/1.00  
% 3.12/1.00  fof(f71,plain,(
% 3.12/1.00    ( ! [X0,X1] : (v1_waybel_0(k5_waybel_0(X0,X1),X0) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_orders_2(X0) | ~v3_orders_2(X0) | v2_struct_0(X0)) )),
% 3.12/1.00    inference(cnf_transformation,[],[f30])).
% 3.12/1.00  
% 3.12/1.00  fof(f70,plain,(
% 3.12/1.00    ( ! [X0,X1] : (~v1_xboole_0(k5_waybel_0(X0,X1)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_orders_2(X0) | ~v3_orders_2(X0) | v2_struct_0(X0)) )),
% 3.12/1.00    inference(cnf_transformation,[],[f30])).
% 3.12/1.00  
% 3.12/1.00  fof(f90,plain,(
% 3.12/1.00    ~v4_waybel_7(sK4,sK3)),
% 3.12/1.00    inference(cnf_transformation,[],[f52])).
% 3.12/1.00  
% 3.12/1.00  cnf(c_31,negated_conjecture,
% 3.12/1.00      ( m1_subset_1(sK4,u1_struct_0(sK3)) ),
% 3.12/1.00      inference(cnf_transformation,[],[f88]) ).
% 3.12/1.00  
% 3.12/1.00  cnf(c_4106,plain,
% 3.12/1.00      ( m1_subset_1(sK4,u1_struct_0(sK3)) = iProver_top ),
% 3.12/1.00      inference(predicate_to_equality,[status(thm)],[c_31]) ).
% 3.12/1.00  
% 3.12/1.00  cnf(c_4,plain,
% 3.12/1.00      ( r2_lattice3(X0,X1,X2)
% 3.12/1.00      | r2_hidden(sK0(X0,X1,X2),X1)
% 3.12/1.00      | ~ m1_subset_1(X2,u1_struct_0(X0))
% 3.12/1.00      | ~ l1_orders_2(X0) ),
% 3.12/1.00      inference(cnf_transformation,[],[f58]) ).
% 3.12/1.00  
% 3.12/1.00  cnf(c_32,negated_conjecture,
% 3.12/1.00      ( l1_orders_2(sK3) ),
% 3.12/1.00      inference(cnf_transformation,[],[f87]) ).
% 3.12/1.00  
% 3.12/1.00  cnf(c_1708,plain,
% 3.12/1.00      ( r2_lattice3(X0,X1,X2)
% 3.12/1.00      | r2_hidden(sK0(X0,X1,X2),X1)
% 3.12/1.00      | ~ m1_subset_1(X2,u1_struct_0(X0))
% 3.12/1.00      | sK3 != X0 ),
% 3.12/1.00      inference(resolution_lifted,[status(thm)],[c_4,c_32]) ).
% 3.12/1.00  
% 3.12/1.00  cnf(c_1709,plain,
% 3.12/1.00      ( r2_lattice3(sK3,X0,X1)
% 3.12/1.00      | r2_hidden(sK0(sK3,X0,X1),X0)
% 3.12/1.00      | ~ m1_subset_1(X1,u1_struct_0(sK3)) ),
% 3.12/1.00      inference(unflattening,[status(thm)],[c_1708]) ).
% 3.12/1.00  
% 3.12/1.00  cnf(c_4080,plain,
% 3.12/1.00      ( r2_lattice3(sK3,X0,X1) = iProver_top
% 3.12/1.00      | r2_hidden(sK0(sK3,X0,X1),X0) = iProver_top
% 3.12/1.00      | m1_subset_1(X1,u1_struct_0(sK3)) != iProver_top ),
% 3.12/1.00      inference(predicate_to_equality,[status(thm)],[c_1709]) ).
% 3.12/1.00  
% 3.12/1.00  cnf(c_20,plain,
% 3.12/1.00      ( r1_orders_2(X0,X1,X2)
% 3.12/1.00      | ~ r2_hidden(X1,k5_waybel_0(X0,X2))
% 3.12/1.00      | ~ m1_subset_1(X2,u1_struct_0(X0))
% 3.12/1.00      | ~ m1_subset_1(X1,u1_struct_0(X0))
% 3.12/1.00      | v2_struct_0(X0)
% 3.12/1.00      | ~ l1_orders_2(X0) ),
% 3.12/1.00      inference(cnf_transformation,[],[f72]) ).
% 3.12/1.00  
% 3.12/1.00  cnf(c_2,plain,
% 3.12/1.00      ( ~ v1_lattice3(X0) | ~ v2_struct_0(X0) | ~ l1_orders_2(X0) ),
% 3.12/1.00      inference(cnf_transformation,[],[f55]) ).
% 3.12/1.00  
% 3.12/1.00  cnf(c_607,plain,
% 3.12/1.00      ( r1_orders_2(X0,X1,X2)
% 3.12/1.00      | ~ r2_hidden(X1,k5_waybel_0(X0,X2))
% 3.12/1.00      | ~ m1_subset_1(X2,u1_struct_0(X0))
% 3.12/1.00      | ~ m1_subset_1(X1,u1_struct_0(X0))
% 3.12/1.00      | ~ v1_lattice3(X0)
% 3.12/1.00      | ~ l1_orders_2(X0) ),
% 3.12/1.00      inference(resolution,[status(thm)],[c_20,c_2]) ).
% 3.12/1.00  
% 3.12/1.00  cnf(c_34,negated_conjecture,
% 3.12/1.00      ( v1_lattice3(sK3) ),
% 3.12/1.00      inference(cnf_transformation,[],[f85]) ).
% 3.12/1.00  
% 3.12/1.00  cnf(c_985,plain,
% 3.12/1.00      ( r1_orders_2(X0,X1,X2)
% 3.12/1.00      | ~ r2_hidden(X1,k5_waybel_0(X0,X2))
% 3.12/1.00      | ~ m1_subset_1(X2,u1_struct_0(X0))
% 3.12/1.00      | ~ m1_subset_1(X1,u1_struct_0(X0))
% 3.12/1.00      | ~ l1_orders_2(X0)
% 3.12/1.00      | sK3 != X0 ),
% 3.12/1.00      inference(resolution_lifted,[status(thm)],[c_607,c_34]) ).
% 3.12/1.00  
% 3.12/1.00  cnf(c_986,plain,
% 3.12/1.00      ( r1_orders_2(sK3,X0,X1)
% 3.12/1.00      | ~ r2_hidden(X0,k5_waybel_0(sK3,X1))
% 3.12/1.00      | ~ m1_subset_1(X0,u1_struct_0(sK3))
% 3.12/1.00      | ~ m1_subset_1(X1,u1_struct_0(sK3))
% 3.12/1.00      | ~ l1_orders_2(sK3) ),
% 3.12/1.00      inference(unflattening,[status(thm)],[c_985]) ).
% 3.12/1.00  
% 3.12/1.00  cnf(c_988,plain,
% 3.12/1.00      ( ~ m1_subset_1(X1,u1_struct_0(sK3))
% 3.12/1.00      | ~ m1_subset_1(X0,u1_struct_0(sK3))
% 3.12/1.00      | ~ r2_hidden(X0,k5_waybel_0(sK3,X1))
% 3.12/1.00      | r1_orders_2(sK3,X0,X1) ),
% 3.12/1.00      inference(global_propositional_subsumption,
% 3.12/1.00                [status(thm)],
% 3.12/1.00                [c_986,c_32]) ).
% 3.12/1.00  
% 3.12/1.00  cnf(c_989,plain,
% 3.12/1.00      ( r1_orders_2(sK3,X0,X1)
% 3.12/1.00      | ~ r2_hidden(X0,k5_waybel_0(sK3,X1))
% 3.12/1.00      | ~ m1_subset_1(X1,u1_struct_0(sK3))
% 3.12/1.00      | ~ m1_subset_1(X0,u1_struct_0(sK3)) ),
% 3.12/1.00      inference(renaming,[status(thm)],[c_988]) ).
% 3.12/1.00  
% 3.12/1.00  cnf(c_4092,plain,
% 3.12/1.00      ( r1_orders_2(sK3,X0,X1) = iProver_top
% 3.12/1.00      | r2_hidden(X0,k5_waybel_0(sK3,X1)) != iProver_top
% 3.12/1.00      | m1_subset_1(X0,u1_struct_0(sK3)) != iProver_top
% 3.12/1.00      | m1_subset_1(X1,u1_struct_0(sK3)) != iProver_top ),
% 3.12/1.00      inference(predicate_to_equality,[status(thm)],[c_989]) ).
% 3.12/1.00  
% 3.12/1.00  cnf(c_990,plain,
% 3.12/1.00      ( r1_orders_2(sK3,X0,X1) = iProver_top
% 3.12/1.00      | r2_hidden(X0,k5_waybel_0(sK3,X1)) != iProver_top
% 3.12/1.00      | m1_subset_1(X0,u1_struct_0(sK3)) != iProver_top
% 3.12/1.00      | m1_subset_1(X1,u1_struct_0(sK3)) != iProver_top ),
% 3.12/1.00      inference(predicate_to_equality,[status(thm)],[c_989]) ).
% 3.12/1.00  
% 3.12/1.00  cnf(c_15,plain,
% 3.12/1.00      ( ~ m1_subset_1(X0,u1_struct_0(X1))
% 3.12/1.00      | m1_subset_1(k5_waybel_0(X1,X0),k1_zfmisc_1(u1_struct_0(X1)))
% 3.12/1.00      | v2_struct_0(X1)
% 3.12/1.00      | ~ l1_orders_2(X1) ),
% 3.12/1.00      inference(cnf_transformation,[],[f68]) ).
% 3.12/1.00  
% 3.12/1.00  cnf(c_714,plain,
% 3.12/1.00      ( ~ m1_subset_1(X0,u1_struct_0(X1))
% 3.12/1.00      | m1_subset_1(k5_waybel_0(X1,X0),k1_zfmisc_1(u1_struct_0(X1)))
% 3.12/1.00      | ~ v1_lattice3(X2)
% 3.12/1.00      | ~ l1_orders_2(X2)
% 3.12/1.00      | ~ l1_orders_2(X1)
% 3.12/1.00      | X1 != X2 ),
% 3.12/1.00      inference(resolution_lifted,[status(thm)],[c_2,c_15]) ).
% 3.12/1.00  
% 3.12/1.00  cnf(c_715,plain,
% 3.12/1.00      ( ~ m1_subset_1(X0,u1_struct_0(X1))
% 3.12/1.00      | m1_subset_1(k5_waybel_0(X1,X0),k1_zfmisc_1(u1_struct_0(X1)))
% 3.12/1.00      | ~ v1_lattice3(X1)
% 3.12/1.00      | ~ l1_orders_2(X1) ),
% 3.12/1.00      inference(unflattening,[status(thm)],[c_714]) ).
% 3.12/1.00  
% 3.12/1.00  cnf(c_1005,plain,
% 3.12/1.00      ( ~ m1_subset_1(X0,u1_struct_0(X1))
% 3.12/1.00      | m1_subset_1(k5_waybel_0(X1,X0),k1_zfmisc_1(u1_struct_0(X1)))
% 3.12/1.00      | ~ l1_orders_2(X1)
% 3.12/1.00      | sK3 != X1 ),
% 3.12/1.00      inference(resolution_lifted,[status(thm)],[c_715,c_34]) ).
% 3.12/1.00  
% 3.12/1.00  cnf(c_1006,plain,
% 3.12/1.00      ( ~ m1_subset_1(X0,u1_struct_0(sK3))
% 3.12/1.00      | m1_subset_1(k5_waybel_0(sK3,X0),k1_zfmisc_1(u1_struct_0(sK3)))
% 3.12/1.00      | ~ l1_orders_2(sK3) ),
% 3.12/1.00      inference(unflattening,[status(thm)],[c_1005]) ).
% 3.12/1.00  
% 3.12/1.00  cnf(c_1010,plain,
% 3.12/1.00      ( m1_subset_1(k5_waybel_0(sK3,X0),k1_zfmisc_1(u1_struct_0(sK3)))
% 3.12/1.00      | ~ m1_subset_1(X0,u1_struct_0(sK3)) ),
% 3.12/1.00      inference(global_propositional_subsumption,
% 3.12/1.00                [status(thm)],
% 3.12/1.00                [c_1006,c_32]) ).
% 3.12/1.00  
% 3.12/1.00  cnf(c_1011,plain,
% 3.12/1.00      ( ~ m1_subset_1(X0,u1_struct_0(sK3))
% 3.12/1.00      | m1_subset_1(k5_waybel_0(sK3,X0),k1_zfmisc_1(u1_struct_0(sK3))) ),
% 3.12/1.00      inference(renaming,[status(thm)],[c_1010]) ).
% 3.12/1.00  
% 3.12/1.00  cnf(c_4091,plain,
% 3.12/1.00      ( m1_subset_1(X0,u1_struct_0(sK3)) != iProver_top
% 3.12/1.00      | m1_subset_1(k5_waybel_0(sK3,X0),k1_zfmisc_1(u1_struct_0(sK3))) = iProver_top ),
% 3.12/1.00      inference(predicate_to_equality,[status(thm)],[c_1011]) ).
% 3.12/1.00  
% 3.12/1.00  cnf(c_0,plain,
% 3.12/1.00      ( ~ r2_hidden(X0,X1)
% 3.12/1.00      | m1_subset_1(X0,X2)
% 3.12/1.00      | ~ m1_subset_1(X1,k1_zfmisc_1(X2)) ),
% 3.12/1.00      inference(cnf_transformation,[],[f53]) ).
% 3.12/1.00  
% 3.12/1.00  cnf(c_4108,plain,
% 3.12/1.00      ( r2_hidden(X0,X1) != iProver_top
% 3.12/1.00      | m1_subset_1(X0,X2) = iProver_top
% 3.12/1.00      | m1_subset_1(X1,k1_zfmisc_1(X2)) != iProver_top ),
% 3.12/1.00      inference(predicate_to_equality,[status(thm)],[c_0]) ).
% 3.12/1.00  
% 3.12/1.00  cnf(c_4495,plain,
% 3.12/1.00      ( r2_hidden(X0,k5_waybel_0(sK3,X1)) != iProver_top
% 3.12/1.00      | m1_subset_1(X1,u1_struct_0(sK3)) != iProver_top
% 3.12/1.00      | m1_subset_1(X0,u1_struct_0(sK3)) = iProver_top ),
% 3.12/1.00      inference(superposition,[status(thm)],[c_4091,c_4108]) ).
% 3.12/1.00  
% 3.12/1.00  cnf(c_4811,plain,
% 3.12/1.00      ( r2_hidden(X0,k5_waybel_0(sK3,X1)) != iProver_top
% 3.12/1.00      | r1_orders_2(sK3,X0,X1) = iProver_top
% 3.12/1.00      | m1_subset_1(X1,u1_struct_0(sK3)) != iProver_top ),
% 3.12/1.00      inference(global_propositional_subsumption,
% 3.12/1.00                [status(thm)],
% 3.12/1.00                [c_4092,c_990,c_4495]) ).
% 3.12/1.00  
% 3.12/1.00  cnf(c_4812,plain,
% 3.12/1.00      ( r1_orders_2(sK3,X0,X1) = iProver_top
% 3.12/1.00      | r2_hidden(X0,k5_waybel_0(sK3,X1)) != iProver_top
% 3.12/1.00      | m1_subset_1(X1,u1_struct_0(sK3)) != iProver_top ),
% 3.12/1.00      inference(renaming,[status(thm)],[c_4811]) ).
% 3.12/1.00  
% 3.12/1.00  cnf(c_4818,plain,
% 3.12/1.00      ( r2_lattice3(sK3,k5_waybel_0(sK3,X0),X1) = iProver_top
% 3.12/1.00      | r1_orders_2(sK3,sK0(sK3,k5_waybel_0(sK3,X0),X1),X0) = iProver_top
% 3.12/1.00      | m1_subset_1(X0,u1_struct_0(sK3)) != iProver_top
% 3.12/1.00      | m1_subset_1(X1,u1_struct_0(sK3)) != iProver_top ),
% 3.12/1.00      inference(superposition,[status(thm)],[c_4080,c_4812]) ).
% 3.12/1.00  
% 3.12/1.00  cnf(c_3,plain,
% 3.12/1.00      ( r2_lattice3(X0,X1,X2)
% 3.12/1.00      | ~ r1_orders_2(X0,sK0(X0,X1,X2),X2)
% 3.12/1.00      | ~ m1_subset_1(X2,u1_struct_0(X0))
% 3.12/1.00      | ~ l1_orders_2(X0) ),
% 3.12/1.00      inference(cnf_transformation,[],[f59]) ).
% 3.12/1.00  
% 3.12/1.00  cnf(c_1723,plain,
% 3.12/1.00      ( r2_lattice3(X0,X1,X2)
% 3.12/1.00      | ~ r1_orders_2(X0,sK0(X0,X1,X2),X2)
% 3.12/1.00      | ~ m1_subset_1(X2,u1_struct_0(X0))
% 3.12/1.00      | sK3 != X0 ),
% 3.12/1.00      inference(resolution_lifted,[status(thm)],[c_3,c_32]) ).
% 3.12/1.00  
% 3.12/1.00  cnf(c_1724,plain,
% 3.12/1.00      ( r2_lattice3(sK3,X0,X1)
% 3.12/1.00      | ~ r1_orders_2(sK3,sK0(sK3,X0,X1),X1)
% 3.12/1.00      | ~ m1_subset_1(X1,u1_struct_0(sK3)) ),
% 3.12/1.00      inference(unflattening,[status(thm)],[c_1723]) ).
% 3.12/1.00  
% 3.12/1.00  cnf(c_4079,plain,
% 3.12/1.00      ( r2_lattice3(sK3,X0,X1) = iProver_top
% 3.12/1.00      | r1_orders_2(sK3,sK0(sK3,X0,X1),X1) != iProver_top
% 3.12/1.00      | m1_subset_1(X1,u1_struct_0(sK3)) != iProver_top ),
% 3.12/1.00      inference(predicate_to_equality,[status(thm)],[c_1724]) ).
% 3.12/1.00  
% 3.12/1.00  cnf(c_6223,plain,
% 3.12/1.00      ( r2_lattice3(sK3,k5_waybel_0(sK3,X0),X0) = iProver_top
% 3.12/1.00      | m1_subset_1(X0,u1_struct_0(sK3)) != iProver_top ),
% 3.12/1.00      inference(superposition,[status(thm)],[c_4818,c_4079]) ).
% 3.12/1.00  
% 3.12/1.00  cnf(c_11,plain,
% 3.12/1.00      ( ~ r2_lattice3(X0,X1,X2)
% 3.12/1.00      | r2_lattice3(X0,X1,sK1(X0,X2,X1))
% 3.12/1.00      | ~ m1_subset_1(X2,u1_struct_0(X0))
% 3.12/1.00      | ~ v5_orders_2(X0)
% 3.12/1.00      | ~ l1_orders_2(X0)
% 3.12/1.00      | k1_yellow_0(X0,X1) = X2 ),
% 3.12/1.00      inference(cnf_transformation,[],[f63]) ).
% 3.12/1.00  
% 3.12/1.00  cnf(c_35,negated_conjecture,
% 3.12/1.00      ( v5_orders_2(sK3) ),
% 3.12/1.00      inference(cnf_transformation,[],[f84]) ).
% 3.12/1.00  
% 3.12/1.00  cnf(c_1514,plain,
% 3.12/1.00      ( ~ r2_lattice3(X0,X1,X2)
% 3.12/1.00      | r2_lattice3(X0,X1,sK1(X0,X2,X1))
% 3.12/1.00      | ~ m1_subset_1(X2,u1_struct_0(X0))
% 3.12/1.00      | ~ l1_orders_2(X0)
% 3.12/1.00      | k1_yellow_0(X0,X1) = X2
% 3.12/1.00      | sK3 != X0 ),
% 3.12/1.00      inference(resolution_lifted,[status(thm)],[c_11,c_35]) ).
% 3.12/1.00  
% 3.12/1.00  cnf(c_1515,plain,
% 3.12/1.00      ( ~ r2_lattice3(sK3,X0,X1)
% 3.12/1.00      | r2_lattice3(sK3,X0,sK1(sK3,X1,X0))
% 3.12/1.00      | ~ m1_subset_1(X1,u1_struct_0(sK3))
% 3.12/1.00      | ~ l1_orders_2(sK3)
% 3.12/1.00      | k1_yellow_0(sK3,X0) = X1 ),
% 3.12/1.00      inference(unflattening,[status(thm)],[c_1514]) ).
% 3.12/1.00  
% 3.12/1.00  cnf(c_1519,plain,
% 3.12/1.00      ( ~ m1_subset_1(X1,u1_struct_0(sK3))
% 3.12/1.00      | r2_lattice3(sK3,X0,sK1(sK3,X1,X0))
% 3.12/1.00      | ~ r2_lattice3(sK3,X0,X1)
% 3.12/1.00      | k1_yellow_0(sK3,X0) = X1 ),
% 3.12/1.00      inference(global_propositional_subsumption,
% 3.12/1.00                [status(thm)],
% 3.12/1.00                [c_1515,c_32]) ).
% 3.12/1.00  
% 3.12/1.00  cnf(c_1520,plain,
% 3.12/1.00      ( ~ r2_lattice3(sK3,X0,X1)
% 3.12/1.00      | r2_lattice3(sK3,X0,sK1(sK3,X1,X0))
% 3.12/1.00      | ~ m1_subset_1(X1,u1_struct_0(sK3))
% 3.12/1.00      | k1_yellow_0(sK3,X0) = X1 ),
% 3.12/1.00      inference(renaming,[status(thm)],[c_1519]) ).
% 3.12/1.00  
% 3.12/1.00  cnf(c_4087,plain,
% 3.12/1.00      ( k1_yellow_0(sK3,X0) = X1
% 3.12/1.00      | r2_lattice3(sK3,X0,X1) != iProver_top
% 3.12/1.00      | r2_lattice3(sK3,X0,sK1(sK3,X1,X0)) = iProver_top
% 3.12/1.00      | m1_subset_1(X1,u1_struct_0(sK3)) != iProver_top ),
% 3.12/1.00      inference(predicate_to_equality,[status(thm)],[c_1520]) ).
% 3.12/1.00  
% 3.12/1.00  cnf(c_12,plain,
% 3.12/1.00      ( ~ r2_lattice3(X0,X1,X2)
% 3.12/1.00      | ~ m1_subset_1(X2,u1_struct_0(X0))
% 3.12/1.00      | m1_subset_1(sK1(X0,X2,X1),u1_struct_0(X0))
% 3.12/1.00      | ~ v5_orders_2(X0)
% 3.12/1.00      | ~ l1_orders_2(X0)
% 3.12/1.00      | k1_yellow_0(X0,X1) = X2 ),
% 3.12/1.00      inference(cnf_transformation,[],[f62]) ).
% 3.12/1.00  
% 3.12/1.00  cnf(c_1490,plain,
% 3.12/1.00      ( ~ r2_lattice3(X0,X1,X2)
% 3.12/1.00      | ~ m1_subset_1(X2,u1_struct_0(X0))
% 3.12/1.00      | m1_subset_1(sK1(X0,X2,X1),u1_struct_0(X0))
% 3.12/1.00      | ~ l1_orders_2(X0)
% 3.12/1.00      | k1_yellow_0(X0,X1) = X2
% 3.12/1.00      | sK3 != X0 ),
% 3.12/1.00      inference(resolution_lifted,[status(thm)],[c_12,c_35]) ).
% 3.12/1.00  
% 3.12/1.00  cnf(c_1491,plain,
% 3.12/1.00      ( ~ r2_lattice3(sK3,X0,X1)
% 3.12/1.00      | ~ m1_subset_1(X1,u1_struct_0(sK3))
% 3.12/1.00      | m1_subset_1(sK1(sK3,X1,X0),u1_struct_0(sK3))
% 3.12/1.00      | ~ l1_orders_2(sK3)
% 3.12/1.00      | k1_yellow_0(sK3,X0) = X1 ),
% 3.12/1.00      inference(unflattening,[status(thm)],[c_1490]) ).
% 3.12/1.00  
% 3.12/1.00  cnf(c_1495,plain,
% 3.12/1.00      ( m1_subset_1(sK1(sK3,X1,X0),u1_struct_0(sK3))
% 3.12/1.00      | ~ m1_subset_1(X1,u1_struct_0(sK3))
% 3.12/1.00      | ~ r2_lattice3(sK3,X0,X1)
% 3.12/1.00      | k1_yellow_0(sK3,X0) = X1 ),
% 3.12/1.00      inference(global_propositional_subsumption,
% 3.12/1.00                [status(thm)],
% 3.12/1.00                [c_1491,c_32]) ).
% 3.12/1.00  
% 3.12/1.00  cnf(c_1496,plain,
% 3.12/1.00      ( ~ r2_lattice3(sK3,X0,X1)
% 3.12/1.00      | ~ m1_subset_1(X1,u1_struct_0(sK3))
% 3.12/1.00      | m1_subset_1(sK1(sK3,X1,X0),u1_struct_0(sK3))
% 3.12/1.00      | k1_yellow_0(sK3,X0) = X1 ),
% 3.12/1.00      inference(renaming,[status(thm)],[c_1495]) ).
% 3.12/1.00  
% 3.12/1.00  cnf(c_4088,plain,
% 3.12/1.00      ( k1_yellow_0(sK3,X0) = X1
% 3.12/1.00      | r2_lattice3(sK3,X0,X1) != iProver_top
% 3.12/1.00      | m1_subset_1(X1,u1_struct_0(sK3)) != iProver_top
% 3.12/1.00      | m1_subset_1(sK1(sK3,X1,X0),u1_struct_0(sK3)) = iProver_top ),
% 3.12/1.00      inference(predicate_to_equality,[status(thm)],[c_1496]) ).
% 3.12/1.00  
% 3.12/1.00  cnf(c_6,plain,
% 3.12/1.00      ( ~ r2_lattice3(X0,X1,X2)
% 3.12/1.00      | r1_orders_2(X0,X3,X2)
% 3.12/1.00      | ~ r2_hidden(X3,X1)
% 3.12/1.00      | ~ m1_subset_1(X2,u1_struct_0(X0))
% 3.12/1.00      | ~ m1_subset_1(X3,u1_struct_0(X0))
% 3.12/1.00      | ~ l1_orders_2(X0) ),
% 3.12/1.00      inference(cnf_transformation,[],[f56]) ).
% 3.12/1.00  
% 3.12/1.00  cnf(c_1674,plain,
% 3.12/1.00      ( ~ r2_lattice3(X0,X1,X2)
% 3.12/1.00      | r1_orders_2(X0,X3,X2)
% 3.12/1.00      | ~ r2_hidden(X3,X1)
% 3.12/1.00      | ~ m1_subset_1(X2,u1_struct_0(X0))
% 3.12/1.00      | ~ m1_subset_1(X3,u1_struct_0(X0))
% 3.12/1.00      | sK3 != X0 ),
% 3.12/1.00      inference(resolution_lifted,[status(thm)],[c_6,c_32]) ).
% 3.12/1.00  
% 3.12/1.00  cnf(c_1675,plain,
% 3.12/1.00      ( ~ r2_lattice3(sK3,X0,X1)
% 3.12/1.00      | r1_orders_2(sK3,X2,X1)
% 3.12/1.00      | ~ r2_hidden(X2,X0)
% 3.12/1.00      | ~ m1_subset_1(X1,u1_struct_0(sK3))
% 3.12/1.00      | ~ m1_subset_1(X2,u1_struct_0(sK3)) ),
% 3.12/1.00      inference(unflattening,[status(thm)],[c_1674]) ).
% 3.12/1.00  
% 3.12/1.00  cnf(c_4082,plain,
% 3.12/1.00      ( r2_lattice3(sK3,X0,X1) != iProver_top
% 3.12/1.00      | r1_orders_2(sK3,X2,X1) = iProver_top
% 3.12/1.00      | r2_hidden(X2,X0) != iProver_top
% 3.12/1.00      | m1_subset_1(X1,u1_struct_0(sK3)) != iProver_top
% 3.12/1.00      | m1_subset_1(X2,u1_struct_0(sK3)) != iProver_top ),
% 3.12/1.00      inference(predicate_to_equality,[status(thm)],[c_1675]) ).
% 3.12/1.00  
% 3.12/1.00  cnf(c_5751,plain,
% 3.12/1.00      ( k1_yellow_0(sK3,X0) = X1
% 3.12/1.00      | r2_lattice3(sK3,X0,X1) != iProver_top
% 3.12/1.00      | r2_lattice3(sK3,X2,sK1(sK3,X1,X0)) != iProver_top
% 3.12/1.00      | r1_orders_2(sK3,X3,sK1(sK3,X1,X0)) = iProver_top
% 3.12/1.00      | r2_hidden(X3,X2) != iProver_top
% 3.12/1.00      | m1_subset_1(X1,u1_struct_0(sK3)) != iProver_top
% 3.12/1.00      | m1_subset_1(X3,u1_struct_0(sK3)) != iProver_top ),
% 3.12/1.00      inference(superposition,[status(thm)],[c_4088,c_4082]) ).
% 3.12/1.00  
% 3.12/1.00  cnf(c_6754,plain,
% 3.12/1.00      ( k1_yellow_0(sK3,X0) = X1
% 3.12/1.00      | r2_lattice3(sK3,X0,X1) != iProver_top
% 3.12/1.00      | r1_orders_2(sK3,X2,sK1(sK3,X1,X0)) = iProver_top
% 3.12/1.00      | r2_hidden(X2,X0) != iProver_top
% 3.12/1.00      | m1_subset_1(X1,u1_struct_0(sK3)) != iProver_top
% 3.12/1.00      | m1_subset_1(X2,u1_struct_0(sK3)) != iProver_top ),
% 3.12/1.00      inference(superposition,[status(thm)],[c_4087,c_5751]) ).
% 3.12/1.00  
% 3.12/1.00  cnf(c_10,plain,
% 3.12/1.00      ( ~ r2_lattice3(X0,X1,X2)
% 3.12/1.00      | ~ r1_orders_2(X0,X2,sK1(X0,X2,X1))
% 3.12/1.00      | ~ m1_subset_1(X2,u1_struct_0(X0))
% 3.12/1.00      | ~ v5_orders_2(X0)
% 3.12/1.00      | ~ l1_orders_2(X0)
% 3.12/1.00      | k1_yellow_0(X0,X1) = X2 ),
% 3.12/1.00      inference(cnf_transformation,[],[f64]) ).
% 3.12/1.00  
% 3.12/1.00  cnf(c_1538,plain,
% 3.12/1.00      ( ~ r2_lattice3(X0,X1,X2)
% 3.12/1.00      | ~ r1_orders_2(X0,X2,sK1(X0,X2,X1))
% 3.12/1.00      | ~ m1_subset_1(X2,u1_struct_0(X0))
% 3.12/1.00      | ~ l1_orders_2(X0)
% 3.12/1.00      | k1_yellow_0(X0,X1) = X2
% 3.12/1.00      | sK3 != X0 ),
% 3.12/1.00      inference(resolution_lifted,[status(thm)],[c_10,c_35]) ).
% 3.12/1.00  
% 3.12/1.00  cnf(c_1539,plain,
% 3.12/1.00      ( ~ r2_lattice3(sK3,X0,X1)
% 3.12/1.00      | ~ r1_orders_2(sK3,X1,sK1(sK3,X1,X0))
% 3.12/1.00      | ~ m1_subset_1(X1,u1_struct_0(sK3))
% 3.12/1.00      | ~ l1_orders_2(sK3)
% 3.12/1.00      | k1_yellow_0(sK3,X0) = X1 ),
% 3.12/1.00      inference(unflattening,[status(thm)],[c_1538]) ).
% 3.12/1.00  
% 3.12/1.00  cnf(c_1543,plain,
% 3.12/1.00      ( ~ m1_subset_1(X1,u1_struct_0(sK3))
% 3.12/1.00      | ~ r1_orders_2(sK3,X1,sK1(sK3,X1,X0))
% 3.12/1.00      | ~ r2_lattice3(sK3,X0,X1)
% 3.12/1.00      | k1_yellow_0(sK3,X0) = X1 ),
% 3.12/1.00      inference(global_propositional_subsumption,
% 3.12/1.00                [status(thm)],
% 3.12/1.00                [c_1539,c_32]) ).
% 3.12/1.00  
% 3.12/1.00  cnf(c_1544,plain,
% 3.12/1.00      ( ~ r2_lattice3(sK3,X0,X1)
% 3.12/1.00      | ~ r1_orders_2(sK3,X1,sK1(sK3,X1,X0))
% 3.12/1.00      | ~ m1_subset_1(X1,u1_struct_0(sK3))
% 3.12/1.00      | k1_yellow_0(sK3,X0) = X1 ),
% 3.12/1.00      inference(renaming,[status(thm)],[c_1543]) ).
% 3.12/1.00  
% 3.12/1.00  cnf(c_4086,plain,
% 3.12/1.00      ( k1_yellow_0(sK3,X0) = X1
% 3.12/1.00      | r2_lattice3(sK3,X0,X1) != iProver_top
% 3.12/1.00      | r1_orders_2(sK3,X1,sK1(sK3,X1,X0)) != iProver_top
% 3.12/1.00      | m1_subset_1(X1,u1_struct_0(sK3)) != iProver_top ),
% 3.12/1.00      inference(predicate_to_equality,[status(thm)],[c_1544]) ).
% 3.12/1.00  
% 3.12/1.00  cnf(c_7026,plain,
% 3.12/1.00      ( k1_yellow_0(sK3,X0) = X1
% 3.12/1.00      | r2_lattice3(sK3,X0,X1) != iProver_top
% 3.12/1.00      | r2_hidden(X1,X0) != iProver_top
% 3.12/1.00      | m1_subset_1(X1,u1_struct_0(sK3)) != iProver_top ),
% 3.12/1.00      inference(superposition,[status(thm)],[c_6754,c_4086]) ).
% 3.12/1.00  
% 3.12/1.00  cnf(c_7120,plain,
% 3.12/1.00      ( k1_yellow_0(sK3,k5_waybel_0(sK3,X0)) = X0
% 3.12/1.00      | r2_hidden(X0,k5_waybel_0(sK3,X0)) != iProver_top
% 3.12/1.00      | m1_subset_1(X0,u1_struct_0(sK3)) != iProver_top ),
% 3.12/1.00      inference(superposition,[status(thm)],[c_6223,c_7026]) ).
% 3.12/1.00  
% 3.12/1.00  cnf(c_1,plain,
% 3.12/1.00      ( r1_orders_2(X0,X1,X1)
% 3.12/1.00      | ~ m1_subset_1(X1,u1_struct_0(X0))
% 3.12/1.00      | v2_struct_0(X0)
% 3.12/1.00      | ~ v3_orders_2(X0)
% 3.12/1.00      | ~ l1_orders_2(X0) ),
% 3.12/1.00      inference(cnf_transformation,[],[f54]) ).
% 3.12/1.00  
% 3.12/1.00  cnf(c_673,plain,
% 3.12/1.00      ( r1_orders_2(X0,X1,X1)
% 3.12/1.00      | ~ m1_subset_1(X1,u1_struct_0(X0))
% 3.12/1.00      | ~ v1_lattice3(X0)
% 3.12/1.00      | ~ v3_orders_2(X0)
% 3.12/1.00      | ~ l1_orders_2(X0) ),
% 3.12/1.00      inference(resolution,[status(thm)],[c_1,c_2]) ).
% 3.12/1.00  
% 3.12/1.00  cnf(c_37,negated_conjecture,
% 3.12/1.00      ( v3_orders_2(sK3) ),
% 3.12/1.00      inference(cnf_transformation,[],[f82]) ).
% 3.12/1.00  
% 3.12/1.00  cnf(c_898,plain,
% 3.12/1.00      ( r1_orders_2(X0,X1,X1)
% 3.12/1.00      | ~ m1_subset_1(X1,u1_struct_0(X0))
% 3.12/1.00      | ~ v1_lattice3(X0)
% 3.12/1.00      | ~ l1_orders_2(X0)
% 3.12/1.00      | sK3 != X0 ),
% 3.12/1.00      inference(resolution_lifted,[status(thm)],[c_673,c_37]) ).
% 3.12/1.00  
% 3.12/1.00  cnf(c_899,plain,
% 3.12/1.00      ( r1_orders_2(sK3,X0,X0)
% 3.12/1.00      | ~ m1_subset_1(X0,u1_struct_0(sK3))
% 3.12/1.00      | ~ v1_lattice3(sK3)
% 3.12/1.00      | ~ l1_orders_2(sK3) ),
% 3.12/1.00      inference(unflattening,[status(thm)],[c_898]) ).
% 3.12/1.00  
% 3.12/1.00  cnf(c_903,plain,
% 3.12/1.00      ( r1_orders_2(sK3,X0,X0) | ~ m1_subset_1(X0,u1_struct_0(sK3)) ),
% 3.12/1.00      inference(global_propositional_subsumption,
% 3.12/1.00                [status(thm)],
% 3.12/1.00                [c_899,c_34,c_32]) ).
% 3.12/1.00  
% 3.12/1.00  cnf(c_19,plain,
% 3.12/1.00      ( ~ r1_orders_2(X0,X1,X2)
% 3.12/1.00      | r2_hidden(X1,k5_waybel_0(X0,X2))
% 3.12/1.00      | ~ m1_subset_1(X2,u1_struct_0(X0))
% 3.12/1.00      | ~ m1_subset_1(X1,u1_struct_0(X0))
% 3.12/1.00      | v2_struct_0(X0)
% 3.12/1.00      | ~ l1_orders_2(X0) ),
% 3.12/1.00      inference(cnf_transformation,[],[f73]) ).
% 3.12/1.00  
% 3.12/1.00  cnf(c_630,plain,
% 3.12/1.00      ( ~ r1_orders_2(X0,X1,X2)
% 3.12/1.00      | r2_hidden(X1,k5_waybel_0(X0,X2))
% 3.12/1.00      | ~ m1_subset_1(X2,u1_struct_0(X0))
% 3.12/1.00      | ~ m1_subset_1(X1,u1_struct_0(X0))
% 3.12/1.00      | ~ v1_lattice3(X0)
% 3.12/1.00      | ~ l1_orders_2(X0) ),
% 3.12/1.00      inference(resolution,[status(thm)],[c_19,c_2]) ).
% 3.12/1.00  
% 3.12/1.00  cnf(c_961,plain,
% 3.12/1.00      ( ~ r1_orders_2(X0,X1,X2)
% 3.12/1.00      | r2_hidden(X1,k5_waybel_0(X0,X2))
% 3.12/1.00      | ~ m1_subset_1(X2,u1_struct_0(X0))
% 3.12/1.00      | ~ m1_subset_1(X1,u1_struct_0(X0))
% 3.12/1.00      | ~ l1_orders_2(X0)
% 3.12/1.00      | sK3 != X0 ),
% 3.12/1.00      inference(resolution_lifted,[status(thm)],[c_630,c_34]) ).
% 3.12/1.00  
% 3.12/1.00  cnf(c_962,plain,
% 3.12/1.00      ( ~ r1_orders_2(sK3,X0,X1)
% 3.12/1.00      | r2_hidden(X0,k5_waybel_0(sK3,X1))
% 3.12/1.00      | ~ m1_subset_1(X0,u1_struct_0(sK3))
% 3.12/1.00      | ~ m1_subset_1(X1,u1_struct_0(sK3))
% 3.12/1.00      | ~ l1_orders_2(sK3) ),
% 3.12/1.00      inference(unflattening,[status(thm)],[c_961]) ).
% 3.12/1.00  
% 3.12/1.00  cnf(c_966,plain,
% 3.12/1.00      ( ~ m1_subset_1(X1,u1_struct_0(sK3))
% 3.12/1.00      | ~ m1_subset_1(X0,u1_struct_0(sK3))
% 3.12/1.00      | r2_hidden(X0,k5_waybel_0(sK3,X1))
% 3.12/1.00      | ~ r1_orders_2(sK3,X0,X1) ),
% 3.12/1.00      inference(global_propositional_subsumption,
% 3.12/1.00                [status(thm)],
% 3.12/1.00                [c_962,c_32]) ).
% 3.12/1.00  
% 3.12/1.00  cnf(c_967,plain,
% 3.12/1.00      ( ~ r1_orders_2(sK3,X0,X1)
% 3.12/1.00      | r2_hidden(X0,k5_waybel_0(sK3,X1))
% 3.12/1.00      | ~ m1_subset_1(X1,u1_struct_0(sK3))
% 3.12/1.00      | ~ m1_subset_1(X0,u1_struct_0(sK3)) ),
% 3.12/1.00      inference(renaming,[status(thm)],[c_966]) ).
% 3.12/1.00  
% 3.12/1.00  cnf(c_2060,plain,
% 3.12/1.00      ( r2_hidden(X0,k5_waybel_0(sK3,X1))
% 3.12/1.00      | ~ m1_subset_1(X0,u1_struct_0(sK3))
% 3.12/1.00      | ~ m1_subset_1(X2,u1_struct_0(sK3))
% 3.12/1.00      | ~ m1_subset_1(X1,u1_struct_0(sK3))
% 3.12/1.00      | X1 != X2
% 3.12/1.00      | X0 != X2
% 3.12/1.00      | sK3 != sK3 ),
% 3.12/1.00      inference(resolution_lifted,[status(thm)],[c_903,c_967]) ).
% 3.12/1.00  
% 3.12/1.00  cnf(c_2061,plain,
% 3.12/1.00      ( r2_hidden(X0,k5_waybel_0(sK3,X0))
% 3.12/1.00      | ~ m1_subset_1(X0,u1_struct_0(sK3)) ),
% 3.12/1.00      inference(unflattening,[status(thm)],[c_2060]) ).
% 3.12/1.00  
% 3.12/1.00  cnf(c_2062,plain,
% 3.12/1.00      ( r2_hidden(X0,k5_waybel_0(sK3,X0)) = iProver_top
% 3.12/1.00      | m1_subset_1(X0,u1_struct_0(sK3)) != iProver_top ),
% 3.12/1.00      inference(predicate_to_equality,[status(thm)],[c_2061]) ).
% 3.12/1.00  
% 3.12/1.00  cnf(c_8274,plain,
% 3.12/1.00      ( k1_yellow_0(sK3,k5_waybel_0(sK3,X0)) = X0
% 3.12/1.00      | m1_subset_1(X0,u1_struct_0(sK3)) != iProver_top ),
% 3.12/1.00      inference(global_propositional_subsumption,
% 3.12/1.00                [status(thm)],
% 3.12/1.00                [c_7120,c_2062]) ).
% 3.12/1.00  
% 3.12/1.00  cnf(c_8282,plain,
% 3.12/1.00      ( k1_yellow_0(sK3,k5_waybel_0(sK3,sK4)) = sK4 ),
% 3.12/1.00      inference(superposition,[status(thm)],[c_4106,c_8274]) ).
% 3.12/1.00  
% 3.12/1.00  cnf(c_16,plain,
% 3.12/1.00      ( v12_waybel_0(k5_waybel_0(X0,X1),X0)
% 3.12/1.00      | ~ m1_subset_1(X1,u1_struct_0(X0))
% 3.12/1.00      | ~ v4_orders_2(X0)
% 3.12/1.00      | v2_struct_0(X0)
% 3.12/1.00      | ~ l1_orders_2(X0) ),
% 3.12/1.00      inference(cnf_transformation,[],[f69]) ).
% 3.12/1.00  
% 3.12/1.00  cnf(c_21,plain,
% 3.12/1.00      ( ~ v1_waybel_7(X0,X1)
% 3.12/1.00      | v4_waybel_7(k1_yellow_0(X1,X0),X1)
% 3.12/1.00      | ~ v1_waybel_0(X0,X1)
% 3.12/1.00      | ~ v12_waybel_0(X0,X1)
% 3.12/1.00      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 3.12/1.00      | ~ m1_subset_1(k1_yellow_0(X1,X0),u1_struct_0(X1))
% 3.12/1.00      | ~ v2_lattice3(X1)
% 3.12/1.00      | v1_xboole_0(X0)
% 3.12/1.00      | ~ v4_orders_2(X1)
% 3.12/1.00      | ~ v5_orders_2(X1)
% 3.12/1.00      | ~ v1_lattice3(X1)
% 3.12/1.00      | ~ v3_orders_2(X1)
% 3.12/1.00      | ~ l1_orders_2(X1) ),
% 3.12/1.00      inference(cnf_transformation,[],[f93]) ).
% 3.12/1.00  
% 3.12/1.00  cnf(c_28,plain,
% 3.12/1.00      ( ~ v5_waybel_6(X0,X1)
% 3.12/1.00      | v1_waybel_7(k5_waybel_0(X1,X0),X1)
% 3.12/1.00      | ~ m1_subset_1(X0,u1_struct_0(X1))
% 3.12/1.00      | ~ v2_lattice3(X1)
% 3.12/1.00      | ~ v4_orders_2(X1)
% 3.12/1.00      | ~ v5_orders_2(X1)
% 3.12/1.00      | ~ v1_lattice3(X1)
% 3.12/1.00      | ~ v3_orders_2(X1)
% 3.12/1.00      | ~ l1_orders_2(X1) ),
% 3.12/1.00      inference(cnf_transformation,[],[f81]) ).
% 3.12/1.00  
% 3.12/1.00  cnf(c_30,negated_conjecture,
% 3.12/1.00      ( v5_waybel_6(sK4,sK3) ),
% 3.12/1.00      inference(cnf_transformation,[],[f89]) ).
% 3.12/1.00  
% 3.12/1.00  cnf(c_422,plain,
% 3.12/1.00      ( v1_waybel_7(k5_waybel_0(X0,X1),X0)
% 3.12/1.00      | ~ m1_subset_1(X1,u1_struct_0(X0))
% 3.12/1.00      | ~ v2_lattice3(X0)
% 3.12/1.00      | ~ v4_orders_2(X0)
% 3.12/1.00      | ~ v5_orders_2(X0)
% 3.12/1.00      | ~ v1_lattice3(X0)
% 3.12/1.00      | ~ v3_orders_2(X0)
% 3.12/1.00      | ~ l1_orders_2(X0)
% 3.12/1.00      | sK3 != X0
% 3.12/1.00      | sK4 != X1 ),
% 3.12/1.00      inference(resolution_lifted,[status(thm)],[c_28,c_30]) ).
% 3.12/1.00  
% 3.12/1.00  cnf(c_423,plain,
% 3.12/1.00      ( v1_waybel_7(k5_waybel_0(sK3,sK4),sK3)
% 3.12/1.00      | ~ m1_subset_1(sK4,u1_struct_0(sK3))
% 3.12/1.00      | ~ v2_lattice3(sK3)
% 3.12/1.00      | ~ v4_orders_2(sK3)
% 3.12/1.00      | ~ v5_orders_2(sK3)
% 3.12/1.00      | ~ v1_lattice3(sK3)
% 3.12/1.00      | ~ v3_orders_2(sK3)
% 3.12/1.00      | ~ l1_orders_2(sK3) ),
% 3.12/1.00      inference(unflattening,[status(thm)],[c_422]) ).
% 3.12/1.00  
% 3.12/1.00  cnf(c_36,negated_conjecture,
% 3.12/1.00      ( v4_orders_2(sK3) ),
% 3.12/1.00      inference(cnf_transformation,[],[f83]) ).
% 3.12/1.00  
% 3.12/1.00  cnf(c_33,negated_conjecture,
% 3.12/1.00      ( v2_lattice3(sK3) ),
% 3.12/1.00      inference(cnf_transformation,[],[f86]) ).
% 3.12/1.00  
% 3.12/1.00  cnf(c_425,plain,
% 3.12/1.00      ( v1_waybel_7(k5_waybel_0(sK3,sK4),sK3) ),
% 3.12/1.00      inference(global_propositional_subsumption,
% 3.12/1.00                [status(thm)],
% 3.12/1.00                [c_423,c_37,c_36,c_35,c_34,c_33,c_32,c_31]) ).
% 3.12/1.00  
% 3.12/1.00  cnf(c_477,plain,
% 3.12/1.00      ( v4_waybel_7(k1_yellow_0(X0,X1),X0)
% 3.12/1.00      | ~ v1_waybel_0(X1,X0)
% 3.12/1.00      | ~ v12_waybel_0(X1,X0)
% 3.12/1.00      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
% 3.12/1.00      | ~ m1_subset_1(k1_yellow_0(X0,X1),u1_struct_0(X0))
% 3.12/1.00      | ~ v2_lattice3(X0)
% 3.12/1.00      | v1_xboole_0(X1)
% 3.12/1.00      | ~ v4_orders_2(X0)
% 3.12/1.00      | ~ v5_orders_2(X0)
% 3.12/1.00      | ~ v1_lattice3(X0)
% 3.12/1.00      | ~ v3_orders_2(X0)
% 3.12/1.00      | ~ l1_orders_2(X0)
% 3.12/1.00      | k5_waybel_0(sK3,sK4) != X1
% 3.12/1.00      | sK3 != X0 ),
% 3.12/1.00      inference(resolution_lifted,[status(thm)],[c_21,c_425]) ).
% 3.12/1.00  
% 3.12/1.00  cnf(c_478,plain,
% 3.12/1.00      ( v4_waybel_7(k1_yellow_0(sK3,k5_waybel_0(sK3,sK4)),sK3)
% 3.12/1.00      | ~ v1_waybel_0(k5_waybel_0(sK3,sK4),sK3)
% 3.12/1.00      | ~ v12_waybel_0(k5_waybel_0(sK3,sK4),sK3)
% 3.12/1.00      | ~ m1_subset_1(k5_waybel_0(sK3,sK4),k1_zfmisc_1(u1_struct_0(sK3)))
% 3.12/1.00      | ~ m1_subset_1(k1_yellow_0(sK3,k5_waybel_0(sK3,sK4)),u1_struct_0(sK3))
% 3.12/1.00      | ~ v2_lattice3(sK3)
% 3.12/1.00      | v1_xboole_0(k5_waybel_0(sK3,sK4))
% 3.12/1.00      | ~ v4_orders_2(sK3)
% 3.12/1.00      | ~ v5_orders_2(sK3)
% 3.12/1.00      | ~ v1_lattice3(sK3)
% 3.12/1.00      | ~ v3_orders_2(sK3)
% 3.12/1.00      | ~ l1_orders_2(sK3) ),
% 3.12/1.00      inference(unflattening,[status(thm)],[c_477]) ).
% 3.12/1.00  
% 3.12/1.00  cnf(c_480,plain,
% 3.12/1.00      ( v1_xboole_0(k5_waybel_0(sK3,sK4))
% 3.12/1.00      | v4_waybel_7(k1_yellow_0(sK3,k5_waybel_0(sK3,sK4)),sK3)
% 3.12/1.00      | ~ v1_waybel_0(k5_waybel_0(sK3,sK4),sK3)
% 3.12/1.00      | ~ v12_waybel_0(k5_waybel_0(sK3,sK4),sK3)
% 3.12/1.00      | ~ m1_subset_1(k5_waybel_0(sK3,sK4),k1_zfmisc_1(u1_struct_0(sK3)))
% 3.12/1.00      | ~ m1_subset_1(k1_yellow_0(sK3,k5_waybel_0(sK3,sK4)),u1_struct_0(sK3)) ),
% 3.12/1.00      inference(global_propositional_subsumption,
% 3.12/1.00                [status(thm)],
% 3.12/1.00                [c_478,c_37,c_36,c_35,c_34,c_33,c_32]) ).
% 3.12/1.00  
% 3.12/1.00  cnf(c_481,plain,
% 3.12/1.00      ( v4_waybel_7(k1_yellow_0(sK3,k5_waybel_0(sK3,sK4)),sK3)
% 3.12/1.00      | ~ v1_waybel_0(k5_waybel_0(sK3,sK4),sK3)
% 3.12/1.00      | ~ v12_waybel_0(k5_waybel_0(sK3,sK4),sK3)
% 3.12/1.00      | ~ m1_subset_1(k5_waybel_0(sK3,sK4),k1_zfmisc_1(u1_struct_0(sK3)))
% 3.12/1.00      | ~ m1_subset_1(k1_yellow_0(sK3,k5_waybel_0(sK3,sK4)),u1_struct_0(sK3))
% 3.12/1.00      | v1_xboole_0(k5_waybel_0(sK3,sK4)) ),
% 3.12/1.00      inference(renaming,[status(thm)],[c_480]) ).
% 3.12/1.00  
% 3.12/1.00  cnf(c_521,plain,
% 3.12/1.00      ( v4_waybel_7(k1_yellow_0(sK3,k5_waybel_0(sK3,sK4)),sK3)
% 3.12/1.00      | ~ v1_waybel_0(k5_waybel_0(sK3,sK4),sK3)
% 3.12/1.00      | ~ m1_subset_1(X0,u1_struct_0(X1))
% 3.12/1.00      | ~ m1_subset_1(k5_waybel_0(sK3,sK4),k1_zfmisc_1(u1_struct_0(sK3)))
% 3.12/1.00      | ~ m1_subset_1(k1_yellow_0(sK3,k5_waybel_0(sK3,sK4)),u1_struct_0(sK3))
% 3.12/1.00      | v1_xboole_0(k5_waybel_0(sK3,sK4))
% 3.12/1.00      | ~ v4_orders_2(X1)
% 3.12/1.00      | v2_struct_0(X1)
% 3.12/1.00      | ~ l1_orders_2(X1)
% 3.12/1.00      | k5_waybel_0(X1,X0) != k5_waybel_0(sK3,sK4)
% 3.12/1.00      | sK3 != X1 ),
% 3.12/1.00      inference(resolution_lifted,[status(thm)],[c_16,c_481]) ).
% 3.12/1.00  
% 3.12/1.00  cnf(c_522,plain,
% 3.12/1.00      ( v4_waybel_7(k1_yellow_0(sK3,k5_waybel_0(sK3,sK4)),sK3)
% 3.12/1.00      | ~ v1_waybel_0(k5_waybel_0(sK3,sK4),sK3)
% 3.12/1.00      | ~ m1_subset_1(X0,u1_struct_0(sK3))
% 3.12/1.00      | ~ m1_subset_1(k5_waybel_0(sK3,sK4),k1_zfmisc_1(u1_struct_0(sK3)))
% 3.12/1.00      | ~ m1_subset_1(k1_yellow_0(sK3,k5_waybel_0(sK3,sK4)),u1_struct_0(sK3))
% 3.12/1.00      | v1_xboole_0(k5_waybel_0(sK3,sK4))
% 3.12/1.00      | ~ v4_orders_2(sK3)
% 3.12/1.00      | v2_struct_0(sK3)
% 3.12/1.00      | ~ l1_orders_2(sK3)
% 3.12/1.00      | k5_waybel_0(sK3,X0) != k5_waybel_0(sK3,sK4) ),
% 3.12/1.00      inference(unflattening,[status(thm)],[c_521]) ).
% 3.12/1.00  
% 3.12/1.00  cnf(c_126,plain,
% 3.12/1.00      ( ~ v1_lattice3(sK3) | ~ v2_struct_0(sK3) | ~ l1_orders_2(sK3) ),
% 3.12/1.00      inference(instantiation,[status(thm)],[c_2]) ).
% 3.12/1.00  
% 3.12/1.00  cnf(c_526,plain,
% 3.12/1.00      ( v1_xboole_0(k5_waybel_0(sK3,sK4))
% 3.12/1.00      | ~ m1_subset_1(k1_yellow_0(sK3,k5_waybel_0(sK3,sK4)),u1_struct_0(sK3))
% 3.12/1.00      | ~ m1_subset_1(k5_waybel_0(sK3,sK4),k1_zfmisc_1(u1_struct_0(sK3)))
% 3.12/1.00      | ~ m1_subset_1(X0,u1_struct_0(sK3))
% 3.12/1.00      | ~ v1_waybel_0(k5_waybel_0(sK3,sK4),sK3)
% 3.12/1.00      | v4_waybel_7(k1_yellow_0(sK3,k5_waybel_0(sK3,sK4)),sK3)
% 3.12/1.00      | k5_waybel_0(sK3,X0) != k5_waybel_0(sK3,sK4) ),
% 3.12/1.00      inference(global_propositional_subsumption,
% 3.12/1.00                [status(thm)],
% 3.12/1.00                [c_522,c_36,c_34,c_32,c_126]) ).
% 3.12/1.00  
% 3.12/1.00  cnf(c_527,plain,
% 3.12/1.00      ( v4_waybel_7(k1_yellow_0(sK3,k5_waybel_0(sK3,sK4)),sK3)
% 3.12/1.00      | ~ v1_waybel_0(k5_waybel_0(sK3,sK4),sK3)
% 3.12/1.00      | ~ m1_subset_1(X0,u1_struct_0(sK3))
% 3.12/1.00      | ~ m1_subset_1(k5_waybel_0(sK3,sK4),k1_zfmisc_1(u1_struct_0(sK3)))
% 3.12/1.00      | ~ m1_subset_1(k1_yellow_0(sK3,k5_waybel_0(sK3,sK4)),u1_struct_0(sK3))
% 3.12/1.00      | v1_xboole_0(k5_waybel_0(sK3,sK4))
% 3.12/1.00      | k5_waybel_0(sK3,X0) != k5_waybel_0(sK3,sK4) ),
% 3.12/1.00      inference(renaming,[status(thm)],[c_526]) ).
% 3.12/1.00  
% 3.12/1.00  cnf(c_3507,plain,
% 3.12/1.00      ( v4_waybel_7(k1_yellow_0(sK3,k5_waybel_0(sK3,sK4)),sK3)
% 3.12/1.00      | ~ v1_waybel_0(k5_waybel_0(sK3,sK4),sK3)
% 3.12/1.00      | ~ m1_subset_1(k5_waybel_0(sK3,sK4),k1_zfmisc_1(u1_struct_0(sK3)))
% 3.12/1.00      | ~ m1_subset_1(k1_yellow_0(sK3,k5_waybel_0(sK3,sK4)),u1_struct_0(sK3))
% 3.12/1.00      | v1_xboole_0(k5_waybel_0(sK3,sK4))
% 3.12/1.00      | sP1_iProver_split ),
% 3.12/1.00      inference(splitting,
% 3.12/1.00                [splitting(split),new_symbols(definition,[])],
% 3.12/1.00                [c_527]) ).
% 3.12/1.00  
% 3.12/1.00  cnf(c_4104,plain,
% 3.12/1.00      ( v4_waybel_7(k1_yellow_0(sK3,k5_waybel_0(sK3,sK4)),sK3) = iProver_top
% 3.12/1.00      | v1_waybel_0(k5_waybel_0(sK3,sK4),sK3) != iProver_top
% 3.12/1.00      | m1_subset_1(k5_waybel_0(sK3,sK4),k1_zfmisc_1(u1_struct_0(sK3))) != iProver_top
% 3.12/1.00      | m1_subset_1(k1_yellow_0(sK3,k5_waybel_0(sK3,sK4)),u1_struct_0(sK3)) != iProver_top
% 3.12/1.00      | v1_xboole_0(k5_waybel_0(sK3,sK4)) = iProver_top
% 3.12/1.00      | sP1_iProver_split = iProver_top ),
% 3.12/1.00      inference(predicate_to_equality,[status(thm)],[c_3507]) ).
% 3.12/1.00  
% 3.12/1.00  cnf(c_44,plain,
% 3.12/1.00      ( m1_subset_1(sK4,u1_struct_0(sK3)) = iProver_top ),
% 3.12/1.00      inference(predicate_to_equality,[status(thm)],[c_31]) ).
% 3.12/1.00  
% 3.12/1.00  cnf(c_3570,plain,
% 3.12/1.00      ( v4_waybel_7(k1_yellow_0(sK3,k5_waybel_0(sK3,sK4)),sK3) = iProver_top
% 3.12/1.00      | v1_waybel_0(k5_waybel_0(sK3,sK4),sK3) != iProver_top
% 3.12/1.00      | m1_subset_1(k5_waybel_0(sK3,sK4),k1_zfmisc_1(u1_struct_0(sK3))) != iProver_top
% 3.12/1.00      | m1_subset_1(k1_yellow_0(sK3,k5_waybel_0(sK3,sK4)),u1_struct_0(sK3)) != iProver_top
% 3.12/1.00      | v1_xboole_0(k5_waybel_0(sK3,sK4)) = iProver_top
% 3.12/1.00      | sP1_iProver_split = iProver_top ),
% 3.12/1.00      inference(predicate_to_equality,[status(thm)],[c_3507]) ).
% 3.12/1.00  
% 3.12/1.00  cnf(c_17,plain,
% 3.12/1.00      ( v1_waybel_0(k5_waybel_0(X0,X1),X0)
% 3.12/1.00      | ~ m1_subset_1(X1,u1_struct_0(X0))
% 3.12/1.00      | v2_struct_0(X0)
% 3.12/1.00      | ~ v3_orders_2(X0)
% 3.12/1.00      | ~ l1_orders_2(X0) ),
% 3.12/1.00      inference(cnf_transformation,[],[f71]) ).
% 3.12/1.00  
% 3.12/1.00  cnf(c_653,plain,
% 3.12/1.00      ( v1_waybel_0(k5_waybel_0(X0,X1),X0)
% 3.12/1.00      | ~ m1_subset_1(X1,u1_struct_0(X0))
% 3.12/1.00      | ~ v1_lattice3(X0)
% 3.12/1.00      | ~ v3_orders_2(X0)
% 3.12/1.00      | ~ l1_orders_2(X0) ),
% 3.12/1.00      inference(resolution,[status(thm)],[c_17,c_2]) ).
% 3.12/1.00  
% 3.12/1.00  cnf(c_916,plain,
% 3.12/1.00      ( v1_waybel_0(k5_waybel_0(X0,X1),X0)
% 3.12/1.00      | ~ m1_subset_1(X1,u1_struct_0(X0))
% 3.12/1.00      | ~ v1_lattice3(X0)
% 3.12/1.00      | ~ l1_orders_2(X0)
% 3.12/1.00      | sK3 != X0 ),
% 3.12/1.00      inference(resolution_lifted,[status(thm)],[c_653,c_37]) ).
% 3.12/1.00  
% 3.12/1.00  cnf(c_917,plain,
% 3.12/1.00      ( v1_waybel_0(k5_waybel_0(sK3,X0),sK3)
% 3.12/1.00      | ~ m1_subset_1(X0,u1_struct_0(sK3))
% 3.12/1.00      | ~ v1_lattice3(sK3)
% 3.12/1.00      | ~ l1_orders_2(sK3) ),
% 3.12/1.00      inference(unflattening,[status(thm)],[c_916]) ).
% 3.12/1.00  
% 3.12/1.00  cnf(c_921,plain,
% 3.12/1.00      ( v1_waybel_0(k5_waybel_0(sK3,X0),sK3)
% 3.12/1.00      | ~ m1_subset_1(X0,u1_struct_0(sK3)) ),
% 3.12/1.00      inference(global_propositional_subsumption,
% 3.12/1.00                [status(thm)],
% 3.12/1.00                [c_917,c_34,c_32]) ).
% 3.12/1.00  
% 3.12/1.00  cnf(c_4381,plain,
% 3.12/1.00      ( v1_waybel_0(k5_waybel_0(sK3,sK4),sK3)
% 3.12/1.00      | ~ m1_subset_1(sK4,u1_struct_0(sK3)) ),
% 3.12/1.00      inference(instantiation,[status(thm)],[c_921]) ).
% 3.12/1.00  
% 3.12/1.00  cnf(c_4382,plain,
% 3.12/1.00      ( v1_waybel_0(k5_waybel_0(sK3,sK4),sK3) = iProver_top
% 3.12/1.00      | m1_subset_1(sK4,u1_struct_0(sK3)) != iProver_top ),
% 3.12/1.00      inference(predicate_to_equality,[status(thm)],[c_4381]) ).
% 3.12/1.00  
% 3.12/1.00  cnf(c_18,plain,
% 3.12/1.00      ( ~ m1_subset_1(X0,u1_struct_0(X1))
% 3.12/1.00      | ~ v1_xboole_0(k5_waybel_0(X1,X0))
% 3.12/1.00      | v2_struct_0(X1)
% 3.12/1.00      | ~ v3_orders_2(X1)
% 3.12/1.00      | ~ l1_orders_2(X1) ),
% 3.12/1.00      inference(cnf_transformation,[],[f70]) ).
% 3.12/1.00  
% 3.12/1.00  cnf(c_693,plain,
% 3.12/1.00      ( ~ m1_subset_1(X0,u1_struct_0(X1))
% 3.12/1.00      | ~ v1_xboole_0(k5_waybel_0(X1,X0))
% 3.12/1.00      | ~ v1_lattice3(X2)
% 3.12/1.00      | ~ v3_orders_2(X1)
% 3.12/1.00      | ~ l1_orders_2(X2)
% 3.12/1.00      | ~ l1_orders_2(X1)
% 3.12/1.00      | X1 != X2 ),
% 3.12/1.00      inference(resolution_lifted,[status(thm)],[c_2,c_18]) ).
% 3.12/1.00  
% 3.12/1.00  cnf(c_694,plain,
% 3.12/1.00      ( ~ m1_subset_1(X0,u1_struct_0(X1))
% 3.12/1.00      | ~ v1_xboole_0(k5_waybel_0(X1,X0))
% 3.12/1.00      | ~ v1_lattice3(X1)
% 3.12/1.00      | ~ v3_orders_2(X1)
% 3.12/1.00      | ~ l1_orders_2(X1) ),
% 3.12/1.00      inference(unflattening,[status(thm)],[c_693]) ).
% 3.12/1.00  
% 3.12/1.00  cnf(c_934,plain,
% 3.12/1.00      ( ~ m1_subset_1(X0,u1_struct_0(X1))
% 3.12/1.00      | ~ v1_xboole_0(k5_waybel_0(X1,X0))
% 3.12/1.00      | ~ v1_lattice3(X1)
% 3.12/1.00      | ~ l1_orders_2(X1)
% 3.12/1.00      | sK3 != X1 ),
% 3.12/1.00      inference(resolution_lifted,[status(thm)],[c_694,c_37]) ).
% 3.12/1.00  
% 3.12/1.00  cnf(c_935,plain,
% 3.12/1.00      ( ~ m1_subset_1(X0,u1_struct_0(sK3))
% 3.12/1.00      | ~ v1_xboole_0(k5_waybel_0(sK3,X0))
% 3.12/1.00      | ~ v1_lattice3(sK3)
% 3.12/1.00      | ~ l1_orders_2(sK3) ),
% 3.12/1.00      inference(unflattening,[status(thm)],[c_934]) ).
% 3.12/1.00  
% 3.12/1.00  cnf(c_939,plain,
% 3.12/1.00      ( ~ m1_subset_1(X0,u1_struct_0(sK3))
% 3.12/1.00      | ~ v1_xboole_0(k5_waybel_0(sK3,X0)) ),
% 3.12/1.00      inference(global_propositional_subsumption,
% 3.12/1.00                [status(thm)],
% 3.12/1.00                [c_935,c_34,c_32]) ).
% 3.12/1.00  
% 3.12/1.00  cnf(c_4384,plain,
% 3.12/1.00      ( ~ m1_subset_1(sK4,u1_struct_0(sK3))
% 3.12/1.00      | ~ v1_xboole_0(k5_waybel_0(sK3,sK4)) ),
% 3.12/1.00      inference(instantiation,[status(thm)],[c_939]) ).
% 3.12/1.00  
% 3.12/1.00  cnf(c_4385,plain,
% 3.12/1.00      ( m1_subset_1(sK4,u1_struct_0(sK3)) != iProver_top
% 3.12/1.00      | v1_xboole_0(k5_waybel_0(sK3,sK4)) != iProver_top ),
% 3.12/1.00      inference(predicate_to_equality,[status(thm)],[c_4384]) ).
% 3.12/1.00  
% 3.12/1.00  cnf(c_4387,plain,
% 3.12/1.00      ( m1_subset_1(k5_waybel_0(sK3,sK4),k1_zfmisc_1(u1_struct_0(sK3)))
% 3.12/1.00      | ~ m1_subset_1(sK4,u1_struct_0(sK3)) ),
% 3.12/1.00      inference(instantiation,[status(thm)],[c_1011]) ).
% 3.12/1.00  
% 3.12/1.00  cnf(c_4388,plain,
% 3.12/1.00      ( m1_subset_1(k5_waybel_0(sK3,sK4),k1_zfmisc_1(u1_struct_0(sK3))) = iProver_top
% 3.12/1.00      | m1_subset_1(sK4,u1_struct_0(sK3)) != iProver_top ),
% 3.12/1.00      inference(predicate_to_equality,[status(thm)],[c_4387]) ).
% 3.12/1.00  
% 3.12/1.00  cnf(c_6739,plain,
% 3.12/1.00      ( m1_subset_1(k1_yellow_0(sK3,k5_waybel_0(sK3,sK4)),u1_struct_0(sK3)) != iProver_top
% 3.12/1.00      | v4_waybel_7(k1_yellow_0(sK3,k5_waybel_0(sK3,sK4)),sK3) = iProver_top
% 3.12/1.00      | sP1_iProver_split = iProver_top ),
% 3.12/1.00      inference(global_propositional_subsumption,
% 3.12/1.00                [status(thm)],
% 3.12/1.00                [c_4104,c_44,c_3570,c_4382,c_4385,c_4388]) ).
% 3.12/1.00  
% 3.12/1.00  cnf(c_6740,plain,
% 3.12/1.00      ( v4_waybel_7(k1_yellow_0(sK3,k5_waybel_0(sK3,sK4)),sK3) = iProver_top
% 3.12/1.00      | m1_subset_1(k1_yellow_0(sK3,k5_waybel_0(sK3,sK4)),u1_struct_0(sK3)) != iProver_top
% 3.12/1.00      | sP1_iProver_split = iProver_top ),
% 3.12/1.00      inference(renaming,[status(thm)],[c_6739]) ).
% 3.12/1.00  
% 3.12/1.00  cnf(c_8374,plain,
% 3.12/1.00      ( v4_waybel_7(sK4,sK3) = iProver_top
% 3.12/1.00      | m1_subset_1(sK4,u1_struct_0(sK3)) != iProver_top
% 3.12/1.00      | sP1_iProver_split = iProver_top ),
% 3.12/1.00      inference(demodulation,[status(thm)],[c_8282,c_6740]) ).
% 3.12/1.00  
% 3.12/1.00  cnf(c_3506,plain,
% 3.12/1.00      ( ~ m1_subset_1(X0,u1_struct_0(sK3))
% 3.12/1.00      | k5_waybel_0(sK3,X0) != k5_waybel_0(sK3,sK4)
% 3.12/1.00      | ~ sP1_iProver_split ),
% 3.12/1.00      inference(splitting,
% 3.12/1.00                [splitting(split),new_symbols(definition,[sP1_iProver_split])],
% 3.12/1.00                [c_527]) ).
% 3.12/1.00  
% 3.12/1.00  cnf(c_4105,plain,
% 3.12/1.00      ( k5_waybel_0(sK3,X0) != k5_waybel_0(sK3,sK4)
% 3.12/1.00      | m1_subset_1(X0,u1_struct_0(sK3)) != iProver_top
% 3.12/1.00      | sP1_iProver_split != iProver_top ),
% 3.12/1.00      inference(predicate_to_equality,[status(thm)],[c_3506]) ).
% 3.12/1.00  
% 3.12/1.00  cnf(c_7716,plain,
% 3.12/1.00      ( m1_subset_1(sK4,u1_struct_0(sK3)) != iProver_top
% 3.12/1.00      | sP1_iProver_split != iProver_top ),
% 3.12/1.00      inference(equality_resolution,[status(thm)],[c_4105]) ).
% 3.12/1.00  
% 3.12/1.00  cnf(c_29,negated_conjecture,
% 3.12/1.00      ( ~ v4_waybel_7(sK4,sK3) ),
% 3.12/1.00      inference(cnf_transformation,[],[f90]) ).
% 3.12/1.00  
% 3.12/1.00  cnf(c_46,plain,
% 3.12/1.00      ( v4_waybel_7(sK4,sK3) != iProver_top ),
% 3.12/1.00      inference(predicate_to_equality,[status(thm)],[c_29]) ).
% 3.12/1.00  
% 3.12/1.00  cnf(contradiction,plain,
% 3.12/1.00      ( $false ),
% 3.12/1.00      inference(minisat,[status(thm)],[c_8374,c_7716,c_46,c_44]) ).
% 3.12/1.00  
% 3.12/1.00  
% 3.12/1.00  % SZS output end CNFRefutation for theBenchmark.p
% 3.12/1.00  
% 3.12/1.00  ------                               Statistics
% 3.12/1.00  
% 3.12/1.00  ------ General
% 3.12/1.00  
% 3.12/1.00  abstr_ref_over_cycles:                  0
% 3.12/1.00  abstr_ref_under_cycles:                 0
% 3.12/1.00  gc_basic_clause_elim:                   0
% 3.12/1.00  forced_gc_time:                         0
% 3.12/1.00  parsing_time:                           0.012
% 3.12/1.00  unif_index_cands_time:                  0.
% 3.12/1.00  unif_index_add_time:                    0.
% 3.12/1.00  orderings_time:                         0.
% 3.12/1.00  out_proof_time:                         0.014
% 3.12/1.00  total_time:                             0.259
% 3.12/1.00  num_of_symbols:                         60
% 3.12/1.00  num_of_terms:                           4860
% 3.12/1.00  
% 3.12/1.00  ------ Preprocessing
% 3.12/1.00  
% 3.12/1.00  num_of_splits:                          2
% 3.12/1.00  num_of_split_atoms:                     2
% 3.12/1.00  num_of_reused_defs:                     0
% 3.12/1.00  num_eq_ax_congr_red:                    34
% 3.12/1.00  num_of_sem_filtered_clauses:            1
% 3.12/1.00  num_of_subtypes:                        0
% 3.12/1.00  monotx_restored_types:                  0
% 3.12/1.00  sat_num_of_epr_types:                   0
% 3.12/1.00  sat_num_of_non_cyclic_types:            0
% 3.12/1.00  sat_guarded_non_collapsed_types:        0
% 3.12/1.00  num_pure_diseq_elim:                    0
% 3.12/1.00  simp_replaced_by:                       0
% 3.12/1.00  res_preprocessed:                       161
% 3.12/1.00  prep_upred:                             0
% 3.12/1.00  prep_unflattend:                        115
% 3.12/1.00  smt_new_axioms:                         0
% 3.12/1.00  pred_elim_cands:                        8
% 3.12/1.00  pred_elim:                              10
% 3.12/1.00  pred_elim_cl:                           10
% 3.12/1.00  pred_elim_cycles:                       21
% 3.12/1.00  merged_defs:                            0
% 3.12/1.00  merged_defs_ncl:                        0
% 3.12/1.00  bin_hyper_res:                          0
% 3.12/1.00  prep_cycles:                            4
% 3.12/1.00  pred_elim_time:                         0.059
% 3.12/1.00  splitting_time:                         0.
% 3.12/1.00  sem_filter_time:                        0.
% 3.12/1.00  monotx_time:                            0.001
% 3.12/1.00  subtype_inf_time:                       0.
% 3.12/1.00  
% 3.12/1.00  ------ Problem properties
% 3.12/1.00  
% 3.12/1.00  clauses:                                30
% 3.12/1.00  conjectures:                            2
% 3.12/1.00  epr:                                    1
% 3.12/1.00  horn:                                   22
% 3.12/1.00  ground:                                 4
% 3.12/1.00  unary:                                  2
% 3.12/1.00  binary:                                 4
% 3.12/1.00  lits:                                   102
% 3.12/1.00  lits_eq:                                6
% 3.12/1.00  fd_pure:                                0
% 3.12/1.00  fd_pseudo:                              0
% 3.12/1.00  fd_cond:                                0
% 3.12/1.00  fd_pseudo_cond:                         3
% 3.12/1.00  ac_symbols:                             0
% 3.12/1.00  
% 3.12/1.00  ------ Propositional Solver
% 3.12/1.00  
% 3.12/1.00  prop_solver_calls:                      29
% 3.12/1.00  prop_fast_solver_calls:                 2460
% 3.12/1.00  smt_solver_calls:                       0
% 3.12/1.00  smt_fast_solver_calls:                  0
% 3.12/1.00  prop_num_of_clauses:                    2195
% 3.12/1.00  prop_preprocess_simplified:             7661
% 3.12/1.00  prop_fo_subsumed:                       102
% 3.12/1.00  prop_solver_time:                       0.
% 3.12/1.00  smt_solver_time:                        0.
% 3.12/1.00  smt_fast_solver_time:                   0.
% 3.12/1.00  prop_fast_solver_time:                  0.
% 3.12/1.00  prop_unsat_core_time:                   0.
% 3.12/1.00  
% 3.12/1.00  ------ QBF
% 3.12/1.00  
% 3.12/1.00  qbf_q_res:                              0
% 3.12/1.00  qbf_num_tautologies:                    0
% 3.12/1.00  qbf_prep_cycles:                        0
% 3.12/1.00  
% 3.12/1.00  ------ BMC1
% 3.12/1.00  
% 3.12/1.00  bmc1_current_bound:                     -1
% 3.12/1.00  bmc1_last_solved_bound:                 -1
% 3.12/1.00  bmc1_unsat_core_size:                   -1
% 3.12/1.00  bmc1_unsat_core_parents_size:           -1
% 3.12/1.00  bmc1_merge_next_fun:                    0
% 3.12/1.00  bmc1_unsat_core_clauses_time:           0.
% 3.12/1.00  
% 3.12/1.00  ------ Instantiation
% 3.12/1.00  
% 3.12/1.00  inst_num_of_clauses:                    451
% 3.12/1.00  inst_num_in_passive:                    101
% 3.12/1.00  inst_num_in_active:                     295
% 3.12/1.00  inst_num_in_unprocessed:                55
% 3.12/1.00  inst_num_of_loops:                      410
% 3.12/1.00  inst_num_of_learning_restarts:          0
% 3.12/1.00  inst_num_moves_active_passive:          111
% 3.12/1.00  inst_lit_activity:                      0
% 3.12/1.00  inst_lit_activity_moves:                0
% 3.12/1.00  inst_num_tautologies:                   0
% 3.12/1.00  inst_num_prop_implied:                  0
% 3.12/1.00  inst_num_existing_simplified:           0
% 3.12/1.00  inst_num_eq_res_simplified:             0
% 3.12/1.00  inst_num_child_elim:                    0
% 3.12/1.00  inst_num_of_dismatching_blockings:      81
% 3.12/1.00  inst_num_of_non_proper_insts:           398
% 3.12/1.00  inst_num_of_duplicates:                 0
% 3.12/1.00  inst_inst_num_from_inst_to_res:         0
% 3.12/1.00  inst_dismatching_checking_time:         0.
% 3.12/1.00  
% 3.12/1.00  ------ Resolution
% 3.12/1.00  
% 3.12/1.00  res_num_of_clauses:                     0
% 3.12/1.00  res_num_in_passive:                     0
% 3.12/1.00  res_num_in_active:                      0
% 3.12/1.00  res_num_of_loops:                       165
% 3.12/1.00  res_forward_subset_subsumed:            29
% 3.12/1.00  res_backward_subset_subsumed:           0
% 3.12/1.00  res_forward_subsumed:                   4
% 3.12/1.00  res_backward_subsumed:                  0
% 3.12/1.00  res_forward_subsumption_resolution:     5
% 3.12/1.00  res_backward_subsumption_resolution:    0
% 3.12/1.00  res_clause_to_clause_subsumption:       1002
% 3.12/1.00  res_orphan_elimination:                 0
% 3.12/1.00  res_tautology_del:                      49
% 3.12/1.00  res_num_eq_res_simplified:              0
% 3.12/1.00  res_num_sel_changes:                    0
% 3.12/1.00  res_moves_from_active_to_pass:          0
% 3.12/1.00  
% 3.12/1.00  ------ Superposition
% 3.12/1.00  
% 3.12/1.00  sup_time_total:                         0.
% 3.12/1.00  sup_time_generating:                    0.
% 3.12/1.00  sup_time_sim_full:                      0.
% 3.12/1.00  sup_time_sim_immed:                     0.
% 3.12/1.00  
% 3.12/1.00  sup_num_of_clauses:                     106
% 3.12/1.00  sup_num_in_active:                      76
% 3.12/1.00  sup_num_in_passive:                     30
% 3.12/1.00  sup_num_of_loops:                       80
% 3.12/1.00  sup_fw_superposition:                   76
% 3.12/1.00  sup_bw_superposition:                   27
% 3.12/1.00  sup_immediate_simplified:               17
% 3.12/1.00  sup_given_eliminated:                   0
% 3.12/1.00  comparisons_done:                       0
% 3.12/1.00  comparisons_avoided:                    2
% 3.12/1.00  
% 3.12/1.00  ------ Simplifications
% 3.12/1.00  
% 3.12/1.00  
% 3.12/1.00  sim_fw_subset_subsumed:                 9
% 3.12/1.00  sim_bw_subset_subsumed:                 2
% 3.12/1.00  sim_fw_subsumed:                        10
% 3.12/1.00  sim_bw_subsumed:                        0
% 3.12/1.00  sim_fw_subsumption_res:                 3
% 3.12/1.00  sim_bw_subsumption_res:                 0
% 3.12/1.00  sim_tautology_del:                      3
% 3.12/1.00  sim_eq_tautology_del:                   0
% 3.12/1.00  sim_eq_res_simp:                        0
% 3.12/1.00  sim_fw_demodulated:                     0
% 3.12/1.00  sim_bw_demodulated:                     2
% 3.12/1.00  sim_light_normalised:                   0
% 3.12/1.00  sim_joinable_taut:                      0
% 3.12/1.00  sim_joinable_simp:                      0
% 3.12/1.00  sim_ac_normalised:                      0
% 3.12/1.00  sim_smt_subsumption:                    0
% 3.12/1.00  
%------------------------------------------------------------------------------
