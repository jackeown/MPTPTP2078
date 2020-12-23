%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n017.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:28:35 EST 2020

% Result     : Theorem 4.01s
% Output     : CNFRefutation 4.01s
% Verified   : 
% Statistics : Number of formulae       :  178 ( 459 expanded)
%              Number of clauses        :   91 ( 135 expanded)
%              Number of leaves         :   19 ( 104 expanded)
%              Depth                    :   18
%              Number of atoms          : 1049 (3145 expanded)
%              Number of equality atoms :  316 ( 378 expanded)
%              Maximal formula depth    :   18 (   7 average)
%              Maximal clause size      :   21 (   5 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f14,conjecture,(
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

fof(f15,negated_conjecture,(
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
    inference(negated_conjecture,[],[f14])).

fof(f42,plain,(
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
    inference(ennf_transformation,[],[f15])).

fof(f43,plain,(
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
    inference(flattening,[],[f42])).

fof(f57,plain,(
    ! [X0] :
      ( ? [X1] :
          ( ~ v4_waybel_7(X1,X0)
          & v5_waybel_6(X1,X0)
          & m1_subset_1(X1,u1_struct_0(X0)) )
     => ( ~ v4_waybel_7(sK4,X0)
        & v5_waybel_6(sK4,X0)
        & m1_subset_1(sK4,u1_struct_0(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f56,plain,
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

fof(f58,plain,
    ( ~ v4_waybel_7(sK4,sK3)
    & v5_waybel_6(sK4,sK3)
    & m1_subset_1(sK4,u1_struct_0(sK3))
    & l1_orders_2(sK3)
    & v2_lattice3(sK3)
    & v1_lattice3(sK3)
    & v5_orders_2(sK3)
    & v4_orders_2(sK3)
    & v3_orders_2(sK3) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3,sK4])],[f43,f57,f56])).

fof(f97,plain,(
    m1_subset_1(sK4,u1_struct_0(sK3)) ),
    inference(cnf_transformation,[],[f58])).

fof(f2,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,u1_struct_0(X0))
        & m1_subset_1(X1,u1_struct_0(X0))
        & l1_orders_2(X0)
        & v3_orders_2(X0)
        & ~ v2_struct_0(X0) )
     => ( r3_orders_2(X0,X1,X2)
      <=> r1_orders_2(X0,X1,X2) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f19,plain,(
    ! [X0,X1,X2] :
      ( ( r3_orders_2(X0,X1,X2)
      <=> r1_orders_2(X0,X1,X2) )
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f20,plain,(
    ! [X0,X1,X2] :
      ( ( r3_orders_2(X0,X1,X2)
      <=> r1_orders_2(X0,X1,X2) )
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f19])).

fof(f44,plain,(
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
    inference(nnf_transformation,[],[f20])).

fof(f60,plain,(
    ! [X2,X0,X1] :
      ( r1_orders_2(X0,X1,X2)
      | ~ r3_orders_2(X0,X1,X2)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f44])).

fof(f91,plain,(
    v3_orders_2(sK3) ),
    inference(cnf_transformation,[],[f58])).

fof(f94,plain,(
    v1_lattice3(sK3) ),
    inference(cnf_transformation,[],[f58])).

fof(f96,plain,(
    l1_orders_2(sK3) ),
    inference(cnf_transformation,[],[f58])).

fof(f4,axiom,(
    ! [X0] :
      ( l1_orders_2(X0)
     => ( v1_lattice3(X0)
       => ~ v2_struct_0(X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f23,plain,(
    ! [X0] :
      ( ~ v2_struct_0(X0)
      | ~ v1_lattice3(X0)
      | ~ l1_orders_2(X0) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f24,plain,(
    ! [X0] :
      ( ~ v2_struct_0(X0)
      | ~ v1_lattice3(X0)
      | ~ l1_orders_2(X0) ) ),
    inference(flattening,[],[f23])).

fof(f63,plain,(
    ! [X0] :
      ( ~ v2_struct_0(X0)
      | ~ v1_lattice3(X0)
      | ~ l1_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f6,axiom,(
    ! [X0,X1] :
      ( l1_orders_2(X0)
     => m1_subset_1(k1_yellow_0(X0,X1),u1_struct_0(X0)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f27,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k1_yellow_0(X0,X1),u1_struct_0(X0))
      | ~ l1_orders_2(X0) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f68,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k1_yellow_0(X0,X1),u1_struct_0(X0))
      | ~ l1_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f3,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,u1_struct_0(X0))
        & m1_subset_1(X1,u1_struct_0(X0))
        & l1_orders_2(X0)
        & v3_orders_2(X0)
        & ~ v2_struct_0(X0) )
     => r3_orders_2(X0,X1,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f21,plain,(
    ! [X0,X1,X2] :
      ( r3_orders_2(X0,X1,X1)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f22,plain,(
    ! [X0,X1,X2] :
      ( r3_orders_2(X0,X1,X1)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f21])).

fof(f62,plain,(
    ! [X2,X0,X1] :
      ( r3_orders_2(X0,X1,X1)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f11,axiom,(
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

fof(f36,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( r2_hidden(X2,k5_waybel_0(X0,X1))
              <=> r1_orders_2(X0,X2,X1) )
              | ~ m1_subset_1(X2,u1_struct_0(X0)) )
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l1_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f37,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( r2_hidden(X2,k5_waybel_0(X0,X1))
              <=> r1_orders_2(X0,X2,X1) )
              | ~ m1_subset_1(X2,u1_struct_0(X0)) )
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l1_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f36])).

fof(f51,plain,(
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
    inference(nnf_transformation,[],[f37])).

fof(f82,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(X2,k5_waybel_0(X0,X1))
      | ~ r1_orders_2(X0,X2,X1)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f51])).

fof(f5,axiom,(
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

fof(f25,plain,(
    ! [X0] :
      ( ! [X1,X2] :
          ( ( r2_lattice3(X0,X1,X2)
          <=> ! [X3] :
                ( r1_orders_2(X0,X3,X2)
                | ~ r2_hidden(X3,X1)
                | ~ m1_subset_1(X3,u1_struct_0(X0)) ) )
          | ~ m1_subset_1(X2,u1_struct_0(X0)) )
      | ~ l1_orders_2(X0) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f26,plain,(
    ! [X0] :
      ( ! [X1,X2] :
          ( ( r2_lattice3(X0,X1,X2)
          <=> ! [X3] :
                ( r1_orders_2(X0,X3,X2)
                | ~ r2_hidden(X3,X1)
                | ~ m1_subset_1(X3,u1_struct_0(X0)) ) )
          | ~ m1_subset_1(X2,u1_struct_0(X0)) )
      | ~ l1_orders_2(X0) ) ),
    inference(flattening,[],[f25])).

fof(f45,plain,(
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
    inference(nnf_transformation,[],[f26])).

fof(f46,plain,(
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
    inference(rectify,[],[f45])).

fof(f47,plain,(
    ! [X2,X1,X0] :
      ( ? [X3] :
          ( ~ r1_orders_2(X0,X3,X2)
          & r2_hidden(X3,X1)
          & m1_subset_1(X3,u1_struct_0(X0)) )
     => ( ~ r1_orders_2(X0,sK0(X0,X1,X2),X2)
        & r2_hidden(sK0(X0,X1,X2),X1)
        & m1_subset_1(sK0(X0,X1,X2),u1_struct_0(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f48,plain,(
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
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f46,f47])).

fof(f66,plain,(
    ! [X2,X0,X1] :
      ( r2_lattice3(X0,X1,X2)
      | r2_hidden(sK0(X0,X1,X2),X1)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ l1_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f48])).

fof(f81,plain,(
    ! [X2,X0,X1] :
      ( r1_orders_2(X0,X2,X1)
      | ~ r2_hidden(X2,k5_waybel_0(X0,X1))
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f51])).

fof(f8,axiom,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,u1_struct_0(X0))
        & l1_orders_2(X0)
        & ~ v2_struct_0(X0) )
     => m1_subset_1(k5_waybel_0(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f30,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k5_waybel_0(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f31,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k5_waybel_0(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f30])).

fof(f77,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k5_waybel_0(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f1,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(X2))
        & r2_hidden(X0,X1) )
     => m1_subset_1(X0,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f17,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X0,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f18,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X0,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(flattening,[],[f17])).

fof(f59,plain,(
    ! [X2,X0,X1] :
      ( m1_subset_1(X0,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f67,plain,(
    ! [X2,X0,X1] :
      ( r2_lattice3(X0,X1,X2)
      | ~ r1_orders_2(X0,sK0(X0,X1,X2),X2)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ l1_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f48])).

fof(f7,axiom,(
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

fof(f16,plain,(
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
    inference(rectify,[],[f7])).

fof(f28,plain,(
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
    inference(ennf_transformation,[],[f16])).

fof(f29,plain,(
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
    inference(flattening,[],[f28])).

fof(f49,plain,(
    ! [X2,X1,X0] :
      ( ? [X3] :
          ( ~ r1_orders_2(X0,X1,X3)
          & r2_lattice3(X0,X2,X3)
          & m1_subset_1(X3,u1_struct_0(X0)) )
     => ( ~ r1_orders_2(X0,X1,sK1(X0,X1,X2))
        & r2_lattice3(X0,X2,sK1(X0,X1,X2))
        & m1_subset_1(sK1(X0,X1,X2),u1_struct_0(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f50,plain,(
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
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1])],[f29,f49])).

fof(f72,plain,(
    ! [X2,X0,X1] :
      ( k1_yellow_0(X0,X2) = X1
      | r2_lattice3(X0,X2,sK1(X0,X1,X2))
      | ~ r2_lattice3(X0,X2,X1)
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | ~ v5_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f50])).

fof(f71,plain,(
    ! [X2,X0,X1] :
      ( k1_yellow_0(X0,X2) = X1
      | m1_subset_1(sK1(X0,X1,X2),u1_struct_0(X0))
      | ~ r2_lattice3(X0,X2,X1)
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | ~ v5_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f50])).

fof(f64,plain,(
    ! [X4,X2,X0,X1] :
      ( r1_orders_2(X0,X4,X2)
      | ~ r2_hidden(X4,X1)
      | ~ m1_subset_1(X4,u1_struct_0(X0))
      | ~ r2_lattice3(X0,X1,X2)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ l1_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f48])).

fof(f73,plain,(
    ! [X2,X0,X1] :
      ( k1_yellow_0(X0,X2) = X1
      | ~ r1_orders_2(X0,X1,sK1(X0,X1,X2))
      | ~ r2_lattice3(X0,X2,X1)
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | ~ v5_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f50])).

fof(f93,plain,(
    v5_orders_2(sK3) ),
    inference(cnf_transformation,[],[f58])).

fof(f12,axiom,(
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

fof(f38,plain,(
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
    inference(ennf_transformation,[],[f12])).

fof(f39,plain,(
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
    inference(flattening,[],[f38])).

fof(f52,plain,(
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
    inference(nnf_transformation,[],[f39])).

fof(f53,plain,(
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
    inference(rectify,[],[f52])).

fof(f54,plain,(
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

fof(f55,plain,(
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
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2])],[f53,f54])).

fof(f89,plain,(
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
    inference(cnf_transformation,[],[f55])).

fof(f102,plain,(
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
    inference(equality_resolution,[],[f89])).

fof(f10,axiom,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,u1_struct_0(X0))
        & l1_orders_2(X0)
        & v3_orders_2(X0)
        & ~ v2_struct_0(X0) )
     => ( v1_waybel_0(k5_waybel_0(X0,X1),X0)
        & ~ v1_xboole_0(k5_waybel_0(X0,X1)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f34,plain,(
    ! [X0,X1] :
      ( ( v1_waybel_0(k5_waybel_0(X0,X1),X0)
        & ~ v1_xboole_0(k5_waybel_0(X0,X1)) )
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f35,plain,(
    ! [X0,X1] :
      ( ( v1_waybel_0(k5_waybel_0(X0,X1),X0)
        & ~ v1_xboole_0(k5_waybel_0(X0,X1)) )
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f34])).

fof(f80,plain,(
    ! [X0,X1] :
      ( v1_waybel_0(k5_waybel_0(X0,X1),X0)
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f35])).

fof(f9,axiom,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,u1_struct_0(X0))
        & l1_orders_2(X0)
        & v4_orders_2(X0)
        & ~ v2_struct_0(X0) )
     => v12_waybel_0(k5_waybel_0(X0,X1),X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f32,plain,(
    ! [X0,X1] :
      ( v12_waybel_0(k5_waybel_0(X0,X1),X0)
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | ~ v4_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f33,plain,(
    ! [X0,X1] :
      ( v12_waybel_0(k5_waybel_0(X0,X1),X0)
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | ~ v4_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f32])).

fof(f78,plain,(
    ! [X0,X1] :
      ( v12_waybel_0(k5_waybel_0(X0,X1),X0)
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | ~ v4_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f33])).

fof(f79,plain,(
    ! [X0,X1] :
      ( ~ v1_xboole_0(k5_waybel_0(X0,X1))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f35])).

fof(f13,axiom,(
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

fof(f40,plain,(
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
    inference(ennf_transformation,[],[f13])).

fof(f41,plain,(
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
    inference(flattening,[],[f40])).

fof(f90,plain,(
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
    inference(cnf_transformation,[],[f41])).

fof(f99,plain,(
    ~ v4_waybel_7(sK4,sK3) ),
    inference(cnf_transformation,[],[f58])).

fof(f98,plain,(
    v5_waybel_6(sK4,sK3) ),
    inference(cnf_transformation,[],[f58])).

fof(f95,plain,(
    v2_lattice3(sK3) ),
    inference(cnf_transformation,[],[f58])).

fof(f92,plain,(
    v4_orders_2(sK3) ),
    inference(cnf_transformation,[],[f58])).

cnf(c_34,negated_conjecture,
    ( m1_subset_1(sK4,u1_struct_0(sK3)) ),
    inference(cnf_transformation,[],[f97])).

cnf(c_1166,plain,
    ( m1_subset_1(sK4,u1_struct_0(sK3)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_34])).

cnf(c_2,plain,
    ( r1_orders_2(X0,X1,X2)
    | ~ r3_orders_2(X0,X1,X2)
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | ~ m1_subset_1(X1,u1_struct_0(X0))
    | v2_struct_0(X0)
    | ~ v3_orders_2(X0)
    | ~ l1_orders_2(X0) ),
    inference(cnf_transformation,[],[f60])).

cnf(c_1196,plain,
    ( r1_orders_2(X0,X1,X2) = iProver_top
    | r3_orders_2(X0,X1,X2) != iProver_top
    | m1_subset_1(X1,u1_struct_0(X0)) != iProver_top
    | m1_subset_1(X2,u1_struct_0(X0)) != iProver_top
    | v2_struct_0(X0) = iProver_top
    | v3_orders_2(X0) != iProver_top
    | l1_orders_2(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2])).

cnf(c_3874,plain,
    ( r1_orders_2(sK3,sK4,X0) = iProver_top
    | r3_orders_2(sK3,sK4,X0) != iProver_top
    | m1_subset_1(X0,u1_struct_0(sK3)) != iProver_top
    | v2_struct_0(sK3) = iProver_top
    | v3_orders_2(sK3) != iProver_top
    | l1_orders_2(sK3) != iProver_top ),
    inference(superposition,[status(thm)],[c_1166,c_1196])).

cnf(c_40,negated_conjecture,
    ( v3_orders_2(sK3) ),
    inference(cnf_transformation,[],[f91])).

cnf(c_41,plain,
    ( v3_orders_2(sK3) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_40])).

cnf(c_37,negated_conjecture,
    ( v1_lattice3(sK3) ),
    inference(cnf_transformation,[],[f94])).

cnf(c_44,plain,
    ( v1_lattice3(sK3) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_37])).

cnf(c_35,negated_conjecture,
    ( l1_orders_2(sK3) ),
    inference(cnf_transformation,[],[f96])).

cnf(c_46,plain,
    ( l1_orders_2(sK3) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_35])).

cnf(c_4,plain,
    ( ~ v1_lattice3(X0)
    | ~ v2_struct_0(X0)
    | ~ l1_orders_2(X0) ),
    inference(cnf_transformation,[],[f63])).

cnf(c_131,plain,
    ( v1_lattice3(X0) != iProver_top
    | v2_struct_0(X0) != iProver_top
    | l1_orders_2(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_4])).

cnf(c_133,plain,
    ( v1_lattice3(sK3) != iProver_top
    | v2_struct_0(sK3) != iProver_top
    | l1_orders_2(sK3) != iProver_top ),
    inference(instantiation,[status(thm)],[c_131])).

cnf(c_5232,plain,
    ( m1_subset_1(X0,u1_struct_0(sK3)) != iProver_top
    | r3_orders_2(sK3,sK4,X0) != iProver_top
    | r1_orders_2(sK3,sK4,X0) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_3874,c_41,c_44,c_46,c_133])).

cnf(c_5233,plain,
    ( r1_orders_2(sK3,sK4,X0) = iProver_top
    | r3_orders_2(sK3,sK4,X0) != iProver_top
    | m1_subset_1(X0,u1_struct_0(sK3)) != iProver_top ),
    inference(renaming,[status(thm)],[c_5232])).

cnf(c_5245,plain,
    ( r1_orders_2(sK3,sK4,sK4) = iProver_top
    | r3_orders_2(sK3,sK4,sK4) != iProver_top ),
    inference(superposition,[status(thm)],[c_1166,c_5233])).

cnf(c_47,plain,
    ( m1_subset_1(sK4,u1_struct_0(sK3)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_34])).

cnf(c_9,plain,
    ( m1_subset_1(k1_yellow_0(X0,X1),u1_struct_0(X0))
    | ~ l1_orders_2(X0) ),
    inference(cnf_transformation,[],[f68])).

cnf(c_116,plain,
    ( m1_subset_1(k1_yellow_0(X0,X1),u1_struct_0(X0)) = iProver_top
    | l1_orders_2(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_9])).

cnf(c_118,plain,
    ( m1_subset_1(k1_yellow_0(sK3,sK3),u1_struct_0(sK3)) = iProver_top
    | l1_orders_2(sK3) != iProver_top ),
    inference(instantiation,[status(thm)],[c_116])).

cnf(c_3,plain,
    ( r3_orders_2(X0,X1,X1)
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | ~ m1_subset_1(X1,u1_struct_0(X0))
    | v2_struct_0(X0)
    | ~ v3_orders_2(X0)
    | ~ l1_orders_2(X0) ),
    inference(cnf_transformation,[],[f62])).

cnf(c_1808,plain,
    ( r3_orders_2(sK3,sK4,sK4)
    | ~ m1_subset_1(X0,u1_struct_0(sK3))
    | ~ m1_subset_1(sK4,u1_struct_0(sK3))
    | v2_struct_0(sK3)
    | ~ v3_orders_2(sK3)
    | ~ l1_orders_2(sK3) ),
    inference(instantiation,[status(thm)],[c_3])).

cnf(c_1970,plain,
    ( r3_orders_2(sK3,sK4,sK4)
    | ~ m1_subset_1(k1_yellow_0(sK3,X0),u1_struct_0(sK3))
    | ~ m1_subset_1(sK4,u1_struct_0(sK3))
    | v2_struct_0(sK3)
    | ~ v3_orders_2(sK3)
    | ~ l1_orders_2(sK3) ),
    inference(instantiation,[status(thm)],[c_1808])).

cnf(c_1972,plain,
    ( r3_orders_2(sK3,sK4,sK4) = iProver_top
    | m1_subset_1(k1_yellow_0(sK3,X0),u1_struct_0(sK3)) != iProver_top
    | m1_subset_1(sK4,u1_struct_0(sK3)) != iProver_top
    | v2_struct_0(sK3) = iProver_top
    | v3_orders_2(sK3) != iProver_top
    | l1_orders_2(sK3) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1970])).

cnf(c_1974,plain,
    ( r3_orders_2(sK3,sK4,sK4) = iProver_top
    | m1_subset_1(k1_yellow_0(sK3,sK3),u1_struct_0(sK3)) != iProver_top
    | m1_subset_1(sK4,u1_struct_0(sK3)) != iProver_top
    | v2_struct_0(sK3) = iProver_top
    | v3_orders_2(sK3) != iProver_top
    | l1_orders_2(sK3) != iProver_top ),
    inference(instantiation,[status(thm)],[c_1972])).

cnf(c_2253,plain,
    ( r1_orders_2(sK3,sK4,sK4)
    | ~ r3_orders_2(sK3,sK4,sK4)
    | ~ m1_subset_1(sK4,u1_struct_0(sK3))
    | v2_struct_0(sK3)
    | ~ v3_orders_2(sK3)
    | ~ l1_orders_2(sK3) ),
    inference(instantiation,[status(thm)],[c_2])).

cnf(c_2254,plain,
    ( r1_orders_2(sK3,sK4,sK4) = iProver_top
    | r3_orders_2(sK3,sK4,sK4) != iProver_top
    | m1_subset_1(sK4,u1_struct_0(sK3)) != iProver_top
    | v2_struct_0(sK3) = iProver_top
    | v3_orders_2(sK3) != iProver_top
    | l1_orders_2(sK3) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2253])).

cnf(c_5418,plain,
    ( r1_orders_2(sK3,sK4,sK4) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_5245,c_41,c_44,c_46,c_47,c_118,c_133,c_1974,c_2254])).

cnf(c_22,plain,
    ( ~ r1_orders_2(X0,X1,X2)
    | r2_hidden(X1,k5_waybel_0(X0,X2))
    | ~ m1_subset_1(X1,u1_struct_0(X0))
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | v2_struct_0(X0)
    | ~ l1_orders_2(X0) ),
    inference(cnf_transformation,[],[f82])).

cnf(c_1178,plain,
    ( r1_orders_2(X0,X1,X2) != iProver_top
    | r2_hidden(X1,k5_waybel_0(X0,X2)) = iProver_top
    | m1_subset_1(X1,u1_struct_0(X0)) != iProver_top
    | m1_subset_1(X2,u1_struct_0(X0)) != iProver_top
    | v2_struct_0(X0) = iProver_top
    | l1_orders_2(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_22])).

cnf(c_6,plain,
    ( r2_lattice3(X0,X1,X2)
    | r2_hidden(sK0(X0,X1,X2),X1)
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | ~ l1_orders_2(X0) ),
    inference(cnf_transformation,[],[f66])).

cnf(c_1192,plain,
    ( r2_lattice3(X0,X1,X2) = iProver_top
    | r2_hidden(sK0(X0,X1,X2),X1) = iProver_top
    | m1_subset_1(X2,u1_struct_0(X0)) != iProver_top
    | l1_orders_2(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_6])).

cnf(c_23,plain,
    ( r1_orders_2(X0,X1,X2)
    | ~ r2_hidden(X1,k5_waybel_0(X0,X2))
    | ~ m1_subset_1(X1,u1_struct_0(X0))
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | v2_struct_0(X0)
    | ~ l1_orders_2(X0) ),
    inference(cnf_transformation,[],[f81])).

cnf(c_1177,plain,
    ( r1_orders_2(X0,X1,X2) = iProver_top
    | r2_hidden(X1,k5_waybel_0(X0,X2)) != iProver_top
    | m1_subset_1(X1,u1_struct_0(X0)) != iProver_top
    | m1_subset_1(X2,u1_struct_0(X0)) != iProver_top
    | v2_struct_0(X0) = iProver_top
    | l1_orders_2(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_23])).

cnf(c_2892,plain,
    ( r2_lattice3(X0,k5_waybel_0(X1,X2),X3) = iProver_top
    | r1_orders_2(X1,sK0(X0,k5_waybel_0(X1,X2),X3),X2) = iProver_top
    | m1_subset_1(X3,u1_struct_0(X0)) != iProver_top
    | m1_subset_1(X2,u1_struct_0(X1)) != iProver_top
    | m1_subset_1(sK0(X0,k5_waybel_0(X1,X2),X3),u1_struct_0(X1)) != iProver_top
    | v2_struct_0(X1) = iProver_top
    | l1_orders_2(X1) != iProver_top
    | l1_orders_2(X0) != iProver_top ),
    inference(superposition,[status(thm)],[c_1192,c_1177])).

cnf(c_18,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(X1))
    | m1_subset_1(k5_waybel_0(X1,X0),k1_zfmisc_1(u1_struct_0(X1)))
    | v2_struct_0(X1)
    | ~ l1_orders_2(X1) ),
    inference(cnf_transformation,[],[f77])).

cnf(c_1182,plain,
    ( m1_subset_1(X0,u1_struct_0(X1)) != iProver_top
    | m1_subset_1(k5_waybel_0(X1,X0),k1_zfmisc_1(u1_struct_0(X1))) = iProver_top
    | v2_struct_0(X1) = iProver_top
    | l1_orders_2(X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_18])).

cnf(c_0,plain,
    ( ~ r2_hidden(X0,X1)
    | m1_subset_1(X0,X2)
    | ~ m1_subset_1(X1,k1_zfmisc_1(X2)) ),
    inference(cnf_transformation,[],[f59])).

cnf(c_1198,plain,
    ( r2_hidden(X0,X1) != iProver_top
    | m1_subset_1(X0,X2) = iProver_top
    | m1_subset_1(X1,k1_zfmisc_1(X2)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_0])).

cnf(c_2261,plain,
    ( r2_hidden(X0,k5_waybel_0(X1,X2)) != iProver_top
    | m1_subset_1(X2,u1_struct_0(X1)) != iProver_top
    | m1_subset_1(X0,u1_struct_0(X1)) = iProver_top
    | v2_struct_0(X1) = iProver_top
    | l1_orders_2(X1) != iProver_top ),
    inference(superposition,[status(thm)],[c_1182,c_1198])).

cnf(c_4804,plain,
    ( r2_lattice3(X0,k5_waybel_0(X1,X2),X3) = iProver_top
    | m1_subset_1(X3,u1_struct_0(X0)) != iProver_top
    | m1_subset_1(X2,u1_struct_0(X1)) != iProver_top
    | m1_subset_1(sK0(X0,k5_waybel_0(X1,X2),X3),u1_struct_0(X1)) = iProver_top
    | v2_struct_0(X1) = iProver_top
    | l1_orders_2(X1) != iProver_top
    | l1_orders_2(X0) != iProver_top ),
    inference(superposition,[status(thm)],[c_1192,c_2261])).

cnf(c_6338,plain,
    ( m1_subset_1(X2,u1_struct_0(X1)) != iProver_top
    | m1_subset_1(X3,u1_struct_0(X0)) != iProver_top
    | r1_orders_2(X1,sK0(X0,k5_waybel_0(X1,X2),X3),X2) = iProver_top
    | r2_lattice3(X0,k5_waybel_0(X1,X2),X3) = iProver_top
    | v2_struct_0(X1) = iProver_top
    | l1_orders_2(X1) != iProver_top
    | l1_orders_2(X0) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_2892,c_4804])).

cnf(c_6339,plain,
    ( r2_lattice3(X0,k5_waybel_0(X1,X2),X3) = iProver_top
    | r1_orders_2(X1,sK0(X0,k5_waybel_0(X1,X2),X3),X2) = iProver_top
    | m1_subset_1(X3,u1_struct_0(X0)) != iProver_top
    | m1_subset_1(X2,u1_struct_0(X1)) != iProver_top
    | v2_struct_0(X1) = iProver_top
    | l1_orders_2(X1) != iProver_top
    | l1_orders_2(X0) != iProver_top ),
    inference(renaming,[status(thm)],[c_6338])).

cnf(c_5,plain,
    ( r2_lattice3(X0,X1,X2)
    | ~ r1_orders_2(X0,sK0(X0,X1,X2),X2)
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | ~ l1_orders_2(X0) ),
    inference(cnf_transformation,[],[f67])).

cnf(c_1193,plain,
    ( r2_lattice3(X0,X1,X2) = iProver_top
    | r1_orders_2(X0,sK0(X0,X1,X2),X2) != iProver_top
    | m1_subset_1(X2,u1_struct_0(X0)) != iProver_top
    | l1_orders_2(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_5])).

cnf(c_6351,plain,
    ( r2_lattice3(X0,k5_waybel_0(X0,X1),X1) = iProver_top
    | m1_subset_1(X1,u1_struct_0(X0)) != iProver_top
    | v2_struct_0(X0) = iProver_top
    | l1_orders_2(X0) != iProver_top ),
    inference(superposition,[status(thm)],[c_6339,c_1193])).

cnf(c_14,plain,
    ( ~ r2_lattice3(X0,X1,X2)
    | r2_lattice3(X0,X1,sK1(X0,X2,X1))
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | ~ v5_orders_2(X0)
    | ~ l1_orders_2(X0)
    | k1_yellow_0(X0,X1) = X2 ),
    inference(cnf_transformation,[],[f72])).

cnf(c_1184,plain,
    ( k1_yellow_0(X0,X1) = X2
    | r2_lattice3(X0,X1,X2) != iProver_top
    | r2_lattice3(X0,X1,sK1(X0,X2,X1)) = iProver_top
    | m1_subset_1(X2,u1_struct_0(X0)) != iProver_top
    | v5_orders_2(X0) != iProver_top
    | l1_orders_2(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_14])).

cnf(c_15,plain,
    ( ~ r2_lattice3(X0,X1,X2)
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | m1_subset_1(sK1(X0,X2,X1),u1_struct_0(X0))
    | ~ v5_orders_2(X0)
    | ~ l1_orders_2(X0)
    | k1_yellow_0(X0,X1) = X2 ),
    inference(cnf_transformation,[],[f71])).

cnf(c_1183,plain,
    ( k1_yellow_0(X0,X1) = X2
    | r2_lattice3(X0,X1,X2) != iProver_top
    | m1_subset_1(X2,u1_struct_0(X0)) != iProver_top
    | m1_subset_1(sK1(X0,X2,X1),u1_struct_0(X0)) = iProver_top
    | v5_orders_2(X0) != iProver_top
    | l1_orders_2(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_15])).

cnf(c_8,plain,
    ( ~ r2_lattice3(X0,X1,X2)
    | r1_orders_2(X0,X3,X2)
    | ~ r2_hidden(X3,X1)
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | ~ m1_subset_1(X3,u1_struct_0(X0))
    | ~ l1_orders_2(X0) ),
    inference(cnf_transformation,[],[f64])).

cnf(c_1190,plain,
    ( r2_lattice3(X0,X1,X2) != iProver_top
    | r1_orders_2(X0,X3,X2) = iProver_top
    | r2_hidden(X3,X1) != iProver_top
    | m1_subset_1(X2,u1_struct_0(X0)) != iProver_top
    | m1_subset_1(X3,u1_struct_0(X0)) != iProver_top
    | l1_orders_2(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_8])).

cnf(c_3479,plain,
    ( k1_yellow_0(X0,X1) = X2
    | r2_lattice3(X0,X1,X2) != iProver_top
    | r2_lattice3(X0,X3,sK1(X0,X2,X1)) != iProver_top
    | r1_orders_2(X0,X4,sK1(X0,X2,X1)) = iProver_top
    | r2_hidden(X4,X3) != iProver_top
    | m1_subset_1(X2,u1_struct_0(X0)) != iProver_top
    | m1_subset_1(X4,u1_struct_0(X0)) != iProver_top
    | v5_orders_2(X0) != iProver_top
    | l1_orders_2(X0) != iProver_top ),
    inference(superposition,[status(thm)],[c_1183,c_1190])).

cnf(c_8406,plain,
    ( k1_yellow_0(X0,X1) = X2
    | r2_lattice3(X0,X1,X2) != iProver_top
    | r1_orders_2(X0,X3,sK1(X0,X2,X1)) = iProver_top
    | r2_hidden(X3,X1) != iProver_top
    | m1_subset_1(X2,u1_struct_0(X0)) != iProver_top
    | m1_subset_1(X3,u1_struct_0(X0)) != iProver_top
    | v5_orders_2(X0) != iProver_top
    | l1_orders_2(X0) != iProver_top ),
    inference(superposition,[status(thm)],[c_1184,c_3479])).

cnf(c_13,plain,
    ( ~ r2_lattice3(X0,X1,X2)
    | ~ r1_orders_2(X0,X2,sK1(X0,X2,X1))
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | ~ v5_orders_2(X0)
    | ~ l1_orders_2(X0)
    | k1_yellow_0(X0,X1) = X2 ),
    inference(cnf_transformation,[],[f73])).

cnf(c_1185,plain,
    ( k1_yellow_0(X0,X1) = X2
    | r2_lattice3(X0,X1,X2) != iProver_top
    | r1_orders_2(X0,X2,sK1(X0,X2,X1)) != iProver_top
    | m1_subset_1(X2,u1_struct_0(X0)) != iProver_top
    | v5_orders_2(X0) != iProver_top
    | l1_orders_2(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_13])).

cnf(c_8714,plain,
    ( k1_yellow_0(X0,X1) = X2
    | r2_lattice3(X0,X1,X2) != iProver_top
    | r2_hidden(X2,X1) != iProver_top
    | m1_subset_1(X2,u1_struct_0(X0)) != iProver_top
    | v5_orders_2(X0) != iProver_top
    | l1_orders_2(X0) != iProver_top ),
    inference(superposition,[status(thm)],[c_8406,c_1185])).

cnf(c_8970,plain,
    ( k1_yellow_0(X0,k5_waybel_0(X0,X1)) = X1
    | r2_hidden(X1,k5_waybel_0(X0,X1)) != iProver_top
    | m1_subset_1(X1,u1_struct_0(X0)) != iProver_top
    | v5_orders_2(X0) != iProver_top
    | v2_struct_0(X0) = iProver_top
    | l1_orders_2(X0) != iProver_top ),
    inference(superposition,[status(thm)],[c_6351,c_8714])).

cnf(c_14203,plain,
    ( k1_yellow_0(X0,k5_waybel_0(X0,X1)) = X1
    | r1_orders_2(X0,X1,X1) != iProver_top
    | m1_subset_1(X1,u1_struct_0(X0)) != iProver_top
    | v5_orders_2(X0) != iProver_top
    | v2_struct_0(X0) = iProver_top
    | l1_orders_2(X0) != iProver_top ),
    inference(superposition,[status(thm)],[c_1178,c_8970])).

cnf(c_14259,plain,
    ( k1_yellow_0(sK3,k5_waybel_0(sK3,sK4)) = sK4
    | m1_subset_1(sK4,u1_struct_0(sK3)) != iProver_top
    | v5_orders_2(sK3) != iProver_top
    | v2_struct_0(sK3) = iProver_top
    | l1_orders_2(sK3) != iProver_top ),
    inference(superposition,[status(thm)],[c_5418,c_14203])).

cnf(c_38,negated_conjecture,
    ( v5_orders_2(sK3) ),
    inference(cnf_transformation,[],[f93])).

cnf(c_43,plain,
    ( v5_orders_2(sK3) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_38])).

cnf(c_14467,plain,
    ( k1_yellow_0(sK3,k5_waybel_0(sK3,sK4)) = sK4 ),
    inference(global_propositional_subsumption,[status(thm)],[c_14259,c_43,c_44,c_46,c_47,c_133])).

cnf(c_24,plain,
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
    inference(cnf_transformation,[],[f102])).

cnf(c_1176,plain,
    ( v1_waybel_7(X0,X1) != iProver_top
    | v4_waybel_7(k1_yellow_0(X1,X0),X1) = iProver_top
    | v1_waybel_0(X0,X1) != iProver_top
    | v12_waybel_0(X0,X1) != iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1))) != iProver_top
    | m1_subset_1(k1_yellow_0(X1,X0),u1_struct_0(X1)) != iProver_top
    | v2_lattice3(X1) != iProver_top
    | v1_xboole_0(X0) = iProver_top
    | v4_orders_2(X1) != iProver_top
    | v5_orders_2(X1) != iProver_top
    | v1_lattice3(X1) != iProver_top
    | v3_orders_2(X1) != iProver_top
    | l1_orders_2(X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_24])).

cnf(c_1189,plain,
    ( m1_subset_1(k1_yellow_0(X0,X1),u1_struct_0(X0)) = iProver_top
    | l1_orders_2(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_9])).

cnf(c_1602,plain,
    ( v1_waybel_7(X0,X1) != iProver_top
    | v4_waybel_7(k1_yellow_0(X1,X0),X1) = iProver_top
    | v1_waybel_0(X0,X1) != iProver_top
    | v12_waybel_0(X0,X1) != iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1))) != iProver_top
    | v2_lattice3(X1) != iProver_top
    | v1_xboole_0(X0) = iProver_top
    | v4_orders_2(X1) != iProver_top
    | v5_orders_2(X1) != iProver_top
    | v1_lattice3(X1) != iProver_top
    | v3_orders_2(X1) != iProver_top
    | l1_orders_2(X1) != iProver_top ),
    inference(forward_subsumption_resolution,[status(thm)],[c_1176,c_1189])).

cnf(c_4575,plain,
    ( v1_waybel_7(k5_waybel_0(X0,X1),X0) != iProver_top
    | v4_waybel_7(k1_yellow_0(X0,k5_waybel_0(X0,X1)),X0) = iProver_top
    | v1_waybel_0(k5_waybel_0(X0,X1),X0) != iProver_top
    | v12_waybel_0(k5_waybel_0(X0,X1),X0) != iProver_top
    | m1_subset_1(X1,u1_struct_0(X0)) != iProver_top
    | v2_lattice3(X0) != iProver_top
    | v1_xboole_0(k5_waybel_0(X0,X1)) = iProver_top
    | v4_orders_2(X0) != iProver_top
    | v5_orders_2(X0) != iProver_top
    | v1_lattice3(X0) != iProver_top
    | v2_struct_0(X0) = iProver_top
    | v3_orders_2(X0) != iProver_top
    | l1_orders_2(X0) != iProver_top ),
    inference(superposition,[status(thm)],[c_1182,c_1602])).

cnf(c_20,plain,
    ( v1_waybel_0(k5_waybel_0(X0,X1),X0)
    | ~ m1_subset_1(X1,u1_struct_0(X0))
    | v2_struct_0(X0)
    | ~ v3_orders_2(X0)
    | ~ l1_orders_2(X0) ),
    inference(cnf_transformation,[],[f80])).

cnf(c_83,plain,
    ( v1_waybel_0(k5_waybel_0(X0,X1),X0) = iProver_top
    | m1_subset_1(X1,u1_struct_0(X0)) != iProver_top
    | v2_struct_0(X0) = iProver_top
    | v3_orders_2(X0) != iProver_top
    | l1_orders_2(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_20])).

cnf(c_19,plain,
    ( v12_waybel_0(k5_waybel_0(X0,X1),X0)
    | ~ m1_subset_1(X1,u1_struct_0(X0))
    | ~ v4_orders_2(X0)
    | v2_struct_0(X0)
    | ~ l1_orders_2(X0) ),
    inference(cnf_transformation,[],[f78])).

cnf(c_86,plain,
    ( v12_waybel_0(k5_waybel_0(X0,X1),X0) = iProver_top
    | m1_subset_1(X1,u1_struct_0(X0)) != iProver_top
    | v4_orders_2(X0) != iProver_top
    | v2_struct_0(X0) = iProver_top
    | l1_orders_2(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_19])).

cnf(c_10681,plain,
    ( v1_lattice3(X0) != iProver_top
    | v5_orders_2(X0) != iProver_top
    | v4_orders_2(X0) != iProver_top
    | v1_xboole_0(k5_waybel_0(X0,X1)) = iProver_top
    | v2_lattice3(X0) != iProver_top
    | m1_subset_1(X1,u1_struct_0(X0)) != iProver_top
    | v4_waybel_7(k1_yellow_0(X0,k5_waybel_0(X0,X1)),X0) = iProver_top
    | v1_waybel_7(k5_waybel_0(X0,X1),X0) != iProver_top
    | v3_orders_2(X0) != iProver_top
    | l1_orders_2(X0) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_4575,c_83,c_86,c_131])).

cnf(c_10682,plain,
    ( v1_waybel_7(k5_waybel_0(X0,X1),X0) != iProver_top
    | v4_waybel_7(k1_yellow_0(X0,k5_waybel_0(X0,X1)),X0) = iProver_top
    | m1_subset_1(X1,u1_struct_0(X0)) != iProver_top
    | v2_lattice3(X0) != iProver_top
    | v1_xboole_0(k5_waybel_0(X0,X1)) = iProver_top
    | v4_orders_2(X0) != iProver_top
    | v5_orders_2(X0) != iProver_top
    | v1_lattice3(X0) != iProver_top
    | v3_orders_2(X0) != iProver_top
    | l1_orders_2(X0) != iProver_top ),
    inference(renaming,[status(thm)],[c_10681])).

cnf(c_14491,plain,
    ( v1_waybel_7(k5_waybel_0(sK3,sK4),sK3) != iProver_top
    | v4_waybel_7(sK4,sK3) = iProver_top
    | m1_subset_1(sK4,u1_struct_0(sK3)) != iProver_top
    | v2_lattice3(sK3) != iProver_top
    | v1_xboole_0(k5_waybel_0(sK3,sK4)) = iProver_top
    | v4_orders_2(sK3) != iProver_top
    | v5_orders_2(sK3) != iProver_top
    | v1_lattice3(sK3) != iProver_top
    | v3_orders_2(sK3) != iProver_top
    | l1_orders_2(sK3) != iProver_top ),
    inference(superposition,[status(thm)],[c_14467,c_10682])).

cnf(c_21,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(X1))
    | ~ v1_xboole_0(k5_waybel_0(X1,X0))
    | v2_struct_0(X1)
    | ~ v3_orders_2(X1)
    | ~ l1_orders_2(X1) ),
    inference(cnf_transformation,[],[f79])).

cnf(c_1179,plain,
    ( m1_subset_1(X0,u1_struct_0(X1)) != iProver_top
    | v1_xboole_0(k5_waybel_0(X1,X0)) != iProver_top
    | v2_struct_0(X1) = iProver_top
    | v3_orders_2(X1) != iProver_top
    | l1_orders_2(X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_21])).

cnf(c_2426,plain,
    ( v1_xboole_0(k5_waybel_0(sK3,sK4)) != iProver_top
    | v2_struct_0(sK3) = iProver_top
    | v3_orders_2(sK3) != iProver_top
    | l1_orders_2(sK3) != iProver_top ),
    inference(superposition,[status(thm)],[c_1166,c_1179])).

cnf(c_31,plain,
    ( ~ v5_waybel_6(X0,X1)
    | v1_waybel_7(k5_waybel_0(X1,X0),X1)
    | ~ m1_subset_1(X0,u1_struct_0(X1))
    | ~ v2_lattice3(X1)
    | ~ v4_orders_2(X1)
    | ~ v5_orders_2(X1)
    | ~ v1_lattice3(X1)
    | ~ v3_orders_2(X1)
    | ~ l1_orders_2(X1) ),
    inference(cnf_transformation,[],[f90])).

cnf(c_1892,plain,
    ( ~ v5_waybel_6(sK4,sK3)
    | v1_waybel_7(k5_waybel_0(sK3,sK4),sK3)
    | ~ m1_subset_1(sK4,u1_struct_0(sK3))
    | ~ v2_lattice3(sK3)
    | ~ v4_orders_2(sK3)
    | ~ v5_orders_2(sK3)
    | ~ v1_lattice3(sK3)
    | ~ v3_orders_2(sK3)
    | ~ l1_orders_2(sK3) ),
    inference(instantiation,[status(thm)],[c_31])).

cnf(c_1893,plain,
    ( v5_waybel_6(sK4,sK3) != iProver_top
    | v1_waybel_7(k5_waybel_0(sK3,sK4),sK3) = iProver_top
    | m1_subset_1(sK4,u1_struct_0(sK3)) != iProver_top
    | v2_lattice3(sK3) != iProver_top
    | v4_orders_2(sK3) != iProver_top
    | v5_orders_2(sK3) != iProver_top
    | v1_lattice3(sK3) != iProver_top
    | v3_orders_2(sK3) != iProver_top
    | l1_orders_2(sK3) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1892])).

cnf(c_32,negated_conjecture,
    ( ~ v4_waybel_7(sK4,sK3) ),
    inference(cnf_transformation,[],[f99])).

cnf(c_49,plain,
    ( v4_waybel_7(sK4,sK3) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_32])).

cnf(c_33,negated_conjecture,
    ( v5_waybel_6(sK4,sK3) ),
    inference(cnf_transformation,[],[f98])).

cnf(c_48,plain,
    ( v5_waybel_6(sK4,sK3) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_33])).

cnf(c_36,negated_conjecture,
    ( v2_lattice3(sK3) ),
    inference(cnf_transformation,[],[f95])).

cnf(c_45,plain,
    ( v2_lattice3(sK3) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_36])).

cnf(c_39,negated_conjecture,
    ( v4_orders_2(sK3) ),
    inference(cnf_transformation,[],[f92])).

cnf(c_42,plain,
    ( v4_orders_2(sK3) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_39])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_14491,c_2426,c_1893,c_133,c_49,c_48,c_47,c_46,c_45,c_44,c_43,c_42,c_41])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.00/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.12  % Command    : iproveropt_run.sh %d %s
% 0.13/0.33  % Computer   : n017.cluster.edu
% 0.13/0.33  % Model      : x86_64 x86_64
% 0.13/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.33  % Memory     : 8042.1875MB
% 0.13/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.33  % CPULimit   : 60
% 0.13/0.33  % WCLimit    : 600
% 0.13/0.33  % DateTime   : Tue Dec  1 13:29:46 EST 2020
% 0.13/0.33  % CPUTime    : 
% 0.19/0.34  % Running in FOF mode
% 4.01/0.98  % SZS status Started for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 4.01/0.98  
% 4.01/0.98  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 4.01/0.98  
% 4.01/0.98  ------  iProver source info
% 4.01/0.98  
% 4.01/0.98  git: date: 2020-06-30 10:37:57 +0100
% 4.01/0.98  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 4.01/0.98  git: non_committed_changes: false
% 4.01/0.98  git: last_make_outside_of_git: false
% 4.01/0.98  
% 4.01/0.98  ------ 
% 4.01/0.98  
% 4.01/0.98  ------ Input Options
% 4.01/0.98  
% 4.01/0.98  --out_options                           all
% 4.01/0.98  --tptp_safe_out                         true
% 4.01/0.98  --problem_path                          ""
% 4.01/0.98  --include_path                          ""
% 4.01/0.98  --clausifier                            res/vclausify_rel
% 4.01/0.98  --clausifier_options                    --mode clausify
% 4.01/0.98  --stdin                                 false
% 4.01/0.98  --stats_out                             sel
% 4.01/0.98  
% 4.01/0.98  ------ General Options
% 4.01/0.98  
% 4.01/0.98  --fof                                   false
% 4.01/0.98  --time_out_real                         604.99
% 4.01/0.98  --time_out_virtual                      -1.
% 4.01/0.98  --symbol_type_check                     false
% 4.01/0.98  --clausify_out                          false
% 4.01/0.98  --sig_cnt_out                           false
% 4.01/0.98  --trig_cnt_out                          false
% 4.01/0.98  --trig_cnt_out_tolerance                1.
% 4.01/0.98  --trig_cnt_out_sk_spl                   false
% 4.01/0.98  --abstr_cl_out                          false
% 4.01/0.98  
% 4.01/0.98  ------ Global Options
% 4.01/0.98  
% 4.01/0.98  --schedule                              none
% 4.01/0.98  --add_important_lit                     false
% 4.01/0.98  --prop_solver_per_cl                    1000
% 4.01/0.98  --min_unsat_core                        false
% 4.01/0.98  --soft_assumptions                      false
% 4.01/0.98  --soft_lemma_size                       3
% 4.01/0.98  --prop_impl_unit_size                   0
% 4.01/0.98  --prop_impl_unit                        []
% 4.01/0.98  --share_sel_clauses                     true
% 4.01/0.98  --reset_solvers                         false
% 4.01/0.98  --bc_imp_inh                            [conj_cone]
% 4.01/0.98  --conj_cone_tolerance                   3.
% 4.01/0.98  --extra_neg_conj                        none
% 4.01/0.98  --large_theory_mode                     true
% 4.01/0.98  --prolific_symb_bound                   200
% 4.01/0.98  --lt_threshold                          2000
% 4.01/0.98  --clause_weak_htbl                      true
% 4.01/0.98  --gc_record_bc_elim                     false
% 4.01/0.98  
% 4.01/0.98  ------ Preprocessing Options
% 4.01/0.98  
% 4.01/0.98  --preprocessing_flag                    true
% 4.01/0.98  --time_out_prep_mult                    0.1
% 4.01/0.98  --splitting_mode                        input
% 4.01/0.98  --splitting_grd                         true
% 4.01/0.98  --splitting_cvd                         false
% 4.01/0.98  --splitting_cvd_svl                     false
% 4.01/0.98  --splitting_nvd                         32
% 4.01/0.98  --sub_typing                            true
% 4.01/0.98  --prep_gs_sim                           false
% 4.01/0.98  --prep_unflatten                        true
% 4.01/0.98  --prep_res_sim                          true
% 4.01/0.98  --prep_upred                            true
% 4.01/0.98  --prep_sem_filter                       exhaustive
% 4.01/0.98  --prep_sem_filter_out                   false
% 4.01/0.98  --pred_elim                             false
% 4.01/0.98  --res_sim_input                         true
% 4.01/0.98  --eq_ax_congr_red                       true
% 4.01/0.98  --pure_diseq_elim                       true
% 4.01/0.98  --brand_transform                       false
% 4.01/0.98  --non_eq_to_eq                          false
% 4.01/0.98  --prep_def_merge                        true
% 4.01/0.98  --prep_def_merge_prop_impl              false
% 4.01/0.98  --prep_def_merge_mbd                    true
% 4.01/0.98  --prep_def_merge_tr_red                 false
% 4.01/0.98  --prep_def_merge_tr_cl                  false
% 4.01/0.98  --smt_preprocessing                     true
% 4.01/0.98  --smt_ac_axioms                         fast
% 4.01/0.98  --preprocessed_out                      false
% 4.01/0.98  --preprocessed_stats                    false
% 4.01/0.98  
% 4.01/0.98  ------ Abstraction refinement Options
% 4.01/0.98  
% 4.01/0.98  --abstr_ref                             []
% 4.01/0.98  --abstr_ref_prep                        false
% 4.01/0.98  --abstr_ref_until_sat                   false
% 4.01/0.98  --abstr_ref_sig_restrict                funpre
% 4.01/0.98  --abstr_ref_af_restrict_to_split_sk     false
% 4.01/0.98  --abstr_ref_under                       []
% 4.01/0.98  
% 4.01/0.98  ------ SAT Options
% 4.01/0.98  
% 4.01/0.98  --sat_mode                              false
% 4.01/0.98  --sat_fm_restart_options                ""
% 4.01/0.98  --sat_gr_def                            false
% 4.01/0.98  --sat_epr_types                         true
% 4.01/0.98  --sat_non_cyclic_types                  false
% 4.01/0.98  --sat_finite_models                     false
% 4.01/0.98  --sat_fm_lemmas                         false
% 4.01/0.98  --sat_fm_prep                           false
% 4.01/0.98  --sat_fm_uc_incr                        true
% 4.01/0.98  --sat_out_model                         small
% 4.01/0.98  --sat_out_clauses                       false
% 4.01/0.98  
% 4.01/0.98  ------ QBF Options
% 4.01/0.98  
% 4.01/0.98  --qbf_mode                              false
% 4.01/0.98  --qbf_elim_univ                         false
% 4.01/0.98  --qbf_dom_inst                          none
% 4.01/0.98  --qbf_dom_pre_inst                      false
% 4.01/0.98  --qbf_sk_in                             false
% 4.01/0.98  --qbf_pred_elim                         true
% 4.01/0.98  --qbf_split                             512
% 4.01/0.98  
% 4.01/0.98  ------ BMC1 Options
% 4.01/0.98  
% 4.01/0.98  --bmc1_incremental                      false
% 4.01/0.98  --bmc1_axioms                           reachable_all
% 4.01/0.98  --bmc1_min_bound                        0
% 4.01/0.98  --bmc1_max_bound                        -1
% 4.01/0.98  --bmc1_max_bound_default                -1
% 4.01/0.98  --bmc1_symbol_reachability              true
% 4.01/0.98  --bmc1_property_lemmas                  false
% 4.01/0.98  --bmc1_k_induction                      false
% 4.01/0.98  --bmc1_non_equiv_states                 false
% 4.01/0.98  --bmc1_deadlock                         false
% 4.01/0.98  --bmc1_ucm                              false
% 4.01/0.98  --bmc1_add_unsat_core                   none
% 4.01/0.98  --bmc1_unsat_core_children              false
% 4.01/0.98  --bmc1_unsat_core_extrapolate_axioms    false
% 4.01/0.98  --bmc1_out_stat                         full
% 4.01/0.98  --bmc1_ground_init                      false
% 4.01/0.98  --bmc1_pre_inst_next_state              false
% 4.01/0.98  --bmc1_pre_inst_state                   false
% 4.01/0.98  --bmc1_pre_inst_reach_state             false
% 4.01/0.98  --bmc1_out_unsat_core                   false
% 4.01/0.98  --bmc1_aig_witness_out                  false
% 4.01/0.98  --bmc1_verbose                          false
% 4.01/0.98  --bmc1_dump_clauses_tptp                false
% 4.01/0.98  --bmc1_dump_unsat_core_tptp             false
% 4.01/0.98  --bmc1_dump_file                        -
% 4.01/0.98  --bmc1_ucm_expand_uc_limit              128
% 4.01/0.98  --bmc1_ucm_n_expand_iterations          6
% 4.01/0.98  --bmc1_ucm_extend_mode                  1
% 4.01/0.98  --bmc1_ucm_init_mode                    2
% 4.01/0.98  --bmc1_ucm_cone_mode                    none
% 4.01/0.98  --bmc1_ucm_reduced_relation_type        0
% 4.01/0.98  --bmc1_ucm_relax_model                  4
% 4.01/0.98  --bmc1_ucm_full_tr_after_sat            true
% 4.01/0.98  --bmc1_ucm_expand_neg_assumptions       false
% 4.01/0.98  --bmc1_ucm_layered_model                none
% 4.01/0.98  --bmc1_ucm_max_lemma_size               10
% 4.01/0.98  
% 4.01/0.98  ------ AIG Options
% 4.01/0.98  
% 4.01/0.98  --aig_mode                              false
% 4.01/0.98  
% 4.01/0.98  ------ Instantiation Options
% 4.01/0.98  
% 4.01/0.98  --instantiation_flag                    true
% 4.01/0.98  --inst_sos_flag                         false
% 4.01/0.98  --inst_sos_phase                        true
% 4.01/0.98  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 4.01/0.98  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 4.01/0.98  --inst_lit_sel_side                     num_symb
% 4.01/0.98  --inst_solver_per_active                1400
% 4.01/0.98  --inst_solver_calls_frac                1.
% 4.01/0.98  --inst_passive_queue_type               priority_queues
% 4.01/0.98  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 4.01/0.98  --inst_passive_queues_freq              [25;2]
% 4.01/0.98  --inst_dismatching                      true
% 4.01/0.98  --inst_eager_unprocessed_to_passive     true
% 4.01/0.98  --inst_prop_sim_given                   true
% 4.01/0.98  --inst_prop_sim_new                     false
% 4.01/0.98  --inst_subs_new                         false
% 4.01/0.98  --inst_eq_res_simp                      false
% 4.01/0.98  --inst_subs_given                       false
% 4.01/0.98  --inst_orphan_elimination               true
% 4.01/0.98  --inst_learning_loop_flag               true
% 4.01/0.98  --inst_learning_start                   3000
% 4.01/0.98  --inst_learning_factor                  2
% 4.01/0.98  --inst_start_prop_sim_after_learn       3
% 4.01/0.98  --inst_sel_renew                        solver
% 4.01/0.98  --inst_lit_activity_flag                true
% 4.01/0.98  --inst_restr_to_given                   false
% 4.01/0.98  --inst_activity_threshold               500
% 4.01/0.98  --inst_out_proof                        true
% 4.01/0.98  
% 4.01/0.98  ------ Resolution Options
% 4.01/0.98  
% 4.01/0.98  --resolution_flag                       true
% 4.01/0.98  --res_lit_sel                           adaptive
% 4.01/0.98  --res_lit_sel_side                      none
% 4.01/0.98  --res_ordering                          kbo
% 4.01/0.98  --res_to_prop_solver                    active
% 4.01/0.98  --res_prop_simpl_new                    false
% 4.01/0.98  --res_prop_simpl_given                  true
% 4.01/0.98  --res_passive_queue_type                priority_queues
% 4.01/0.98  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 4.01/0.98  --res_passive_queues_freq               [15;5]
% 4.01/0.98  --res_forward_subs                      full
% 4.01/0.98  --res_backward_subs                     full
% 4.01/0.98  --res_forward_subs_resolution           true
% 4.01/0.98  --res_backward_subs_resolution          true
% 4.01/0.98  --res_orphan_elimination                true
% 4.01/0.98  --res_time_limit                        2.
% 4.01/0.98  --res_out_proof                         true
% 4.01/0.98  
% 4.01/0.98  ------ Superposition Options
% 4.01/0.98  
% 4.01/0.98  --superposition_flag                    true
% 4.01/0.98  --sup_passive_queue_type                priority_queues
% 4.01/0.98  --sup_passive_queues                    [[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 4.01/0.98  --sup_passive_queues_freq               [1;4]
% 4.01/0.98  --demod_completeness_check              fast
% 4.01/0.98  --demod_use_ground                      true
% 4.01/0.98  --sup_to_prop_solver                    passive
% 4.01/0.98  --sup_prop_simpl_new                    true
% 4.01/0.98  --sup_prop_simpl_given                  true
% 4.01/0.98  --sup_fun_splitting                     false
% 4.01/0.98  --sup_smt_interval                      50000
% 4.01/0.98  
% 4.01/0.98  ------ Superposition Simplification Setup
% 4.01/0.98  
% 4.01/0.98  --sup_indices_passive                   []
% 4.01/0.98  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 4.01/0.98  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 4.01/0.98  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 4.01/0.98  --sup_full_triv                         [TrivRules;PropSubs]
% 4.01/0.98  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 4.01/0.98  --sup_full_bw                           [BwDemod]
% 4.01/0.98  --sup_immed_triv                        [TrivRules]
% 4.01/0.98  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 4.01/0.98  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 4.01/0.98  --sup_immed_bw_main                     []
% 4.01/0.98  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 4.01/0.98  --sup_input_triv                        [Unflattening;TrivRules]
% 4.01/0.98  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 4.01/0.98  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 4.01/0.98  
% 4.01/0.98  ------ Combination Options
% 4.01/0.98  
% 4.01/0.98  --comb_res_mult                         3
% 4.01/0.98  --comb_sup_mult                         2
% 4.01/0.98  --comb_inst_mult                        10
% 4.01/0.98  
% 4.01/0.98  ------ Debug Options
% 4.01/0.98  
% 4.01/0.98  --dbg_backtrace                         false
% 4.01/0.98  --dbg_dump_prop_clauses                 false
% 4.01/0.98  --dbg_dump_prop_clauses_file            -
% 4.01/0.98  --dbg_out_stat                          false
% 4.01/0.98  ------ Parsing...
% 4.01/0.98  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 4.01/0.98  
% 4.01/0.98  ------ Preprocessing... sf_s  rm: 1 0s  sf_e 
% 4.01/0.98  
% 4.01/0.98  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 4.01/0.98  
% 4.01/0.98  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 4.01/0.98  ------ Proving...
% 4.01/0.98  ------ Problem Properties 
% 4.01/0.98  
% 4.01/0.98  
% 4.01/0.98  clauses                                 41
% 4.01/0.98  conjectures                             9
% 4.01/0.98  EPR                                     9
% 4.01/0.98  Horn                                    26
% 4.01/0.98  unary                                   9
% 4.01/0.98  binary                                  1
% 4.01/0.98  lits                                    208
% 4.01/0.98  lits eq                                 4
% 4.01/0.98  fd_pure                                 0
% 4.01/0.98  fd_pseudo                               0
% 4.01/0.98  fd_cond                                 0
% 4.01/0.98  fd_pseudo_cond                          3
% 4.01/0.98  AC symbols                              0
% 4.01/0.98  
% 4.01/0.98  ------ Input Options Time Limit: Unbounded
% 4.01/0.98  
% 4.01/0.98  
% 4.01/0.98  ------ 
% 4.01/0.98  Current options:
% 4.01/0.98  ------ 
% 4.01/0.98  
% 4.01/0.98  ------ Input Options
% 4.01/0.98  
% 4.01/0.98  --out_options                           all
% 4.01/0.98  --tptp_safe_out                         true
% 4.01/0.98  --problem_path                          ""
% 4.01/0.98  --include_path                          ""
% 4.01/0.98  --clausifier                            res/vclausify_rel
% 4.01/0.98  --clausifier_options                    --mode clausify
% 4.01/0.98  --stdin                                 false
% 4.01/0.98  --stats_out                             sel
% 4.01/0.98  
% 4.01/0.98  ------ General Options
% 4.01/0.98  
% 4.01/0.98  --fof                                   false
% 4.01/0.98  --time_out_real                         604.99
% 4.01/0.98  --time_out_virtual                      -1.
% 4.01/0.98  --symbol_type_check                     false
% 4.01/0.98  --clausify_out                          false
% 4.01/0.98  --sig_cnt_out                           false
% 4.01/0.98  --trig_cnt_out                          false
% 4.01/0.98  --trig_cnt_out_tolerance                1.
% 4.01/0.98  --trig_cnt_out_sk_spl                   false
% 4.01/0.98  --abstr_cl_out                          false
% 4.01/0.98  
% 4.01/0.98  ------ Global Options
% 4.01/0.98  
% 4.01/0.98  --schedule                              none
% 4.01/0.98  --add_important_lit                     false
% 4.01/0.98  --prop_solver_per_cl                    1000
% 4.01/0.98  --min_unsat_core                        false
% 4.01/0.98  --soft_assumptions                      false
% 4.01/0.98  --soft_lemma_size                       3
% 4.01/0.98  --prop_impl_unit_size                   0
% 4.01/0.98  --prop_impl_unit                        []
% 4.01/0.98  --share_sel_clauses                     true
% 4.01/0.98  --reset_solvers                         false
% 4.01/0.98  --bc_imp_inh                            [conj_cone]
% 4.01/0.98  --conj_cone_tolerance                   3.
% 4.01/0.98  --extra_neg_conj                        none
% 4.01/0.98  --large_theory_mode                     true
% 4.01/0.98  --prolific_symb_bound                   200
% 4.01/0.98  --lt_threshold                          2000
% 4.01/0.98  --clause_weak_htbl                      true
% 4.01/0.98  --gc_record_bc_elim                     false
% 4.01/0.98  
% 4.01/0.98  ------ Preprocessing Options
% 4.01/0.98  
% 4.01/0.98  --preprocessing_flag                    true
% 4.01/0.98  --time_out_prep_mult                    0.1
% 4.01/0.98  --splitting_mode                        input
% 4.01/0.98  --splitting_grd                         true
% 4.01/0.98  --splitting_cvd                         false
% 4.01/0.98  --splitting_cvd_svl                     false
% 4.01/0.98  --splitting_nvd                         32
% 4.01/0.98  --sub_typing                            true
% 4.01/0.98  --prep_gs_sim                           false
% 4.01/0.98  --prep_unflatten                        true
% 4.01/0.98  --prep_res_sim                          true
% 4.01/0.98  --prep_upred                            true
% 4.01/0.98  --prep_sem_filter                       exhaustive
% 4.01/0.98  --prep_sem_filter_out                   false
% 4.01/0.98  --pred_elim                             false
% 4.01/0.98  --res_sim_input                         true
% 4.01/0.98  --eq_ax_congr_red                       true
% 4.01/0.98  --pure_diseq_elim                       true
% 4.01/0.98  --brand_transform                       false
% 4.01/0.98  --non_eq_to_eq                          false
% 4.01/0.98  --prep_def_merge                        true
% 4.01/0.98  --prep_def_merge_prop_impl              false
% 4.01/0.98  --prep_def_merge_mbd                    true
% 4.01/0.98  --prep_def_merge_tr_red                 false
% 4.01/0.98  --prep_def_merge_tr_cl                  false
% 4.01/0.98  --smt_preprocessing                     true
% 4.01/0.98  --smt_ac_axioms                         fast
% 4.01/0.98  --preprocessed_out                      false
% 4.01/0.98  --preprocessed_stats                    false
% 4.01/0.98  
% 4.01/0.98  ------ Abstraction refinement Options
% 4.01/0.98  
% 4.01/0.98  --abstr_ref                             []
% 4.01/0.98  --abstr_ref_prep                        false
% 4.01/0.98  --abstr_ref_until_sat                   false
% 4.01/0.98  --abstr_ref_sig_restrict                funpre
% 4.01/0.98  --abstr_ref_af_restrict_to_split_sk     false
% 4.01/0.98  --abstr_ref_under                       []
% 4.01/0.98  
% 4.01/0.98  ------ SAT Options
% 4.01/0.98  
% 4.01/0.98  --sat_mode                              false
% 4.01/0.98  --sat_fm_restart_options                ""
% 4.01/0.98  --sat_gr_def                            false
% 4.01/0.98  --sat_epr_types                         true
% 4.01/0.98  --sat_non_cyclic_types                  false
% 4.01/0.98  --sat_finite_models                     false
% 4.01/0.98  --sat_fm_lemmas                         false
% 4.01/0.98  --sat_fm_prep                           false
% 4.01/0.98  --sat_fm_uc_incr                        true
% 4.01/0.98  --sat_out_model                         small
% 4.01/0.98  --sat_out_clauses                       false
% 4.01/0.98  
% 4.01/0.98  ------ QBF Options
% 4.01/0.98  
% 4.01/0.98  --qbf_mode                              false
% 4.01/0.98  --qbf_elim_univ                         false
% 4.01/0.98  --qbf_dom_inst                          none
% 4.01/0.98  --qbf_dom_pre_inst                      false
% 4.01/0.98  --qbf_sk_in                             false
% 4.01/0.98  --qbf_pred_elim                         true
% 4.01/0.98  --qbf_split                             512
% 4.01/0.98  
% 4.01/0.98  ------ BMC1 Options
% 4.01/0.98  
% 4.01/0.98  --bmc1_incremental                      false
% 4.01/0.98  --bmc1_axioms                           reachable_all
% 4.01/0.98  --bmc1_min_bound                        0
% 4.01/0.98  --bmc1_max_bound                        -1
% 4.01/0.98  --bmc1_max_bound_default                -1
% 4.01/0.98  --bmc1_symbol_reachability              true
% 4.01/0.98  --bmc1_property_lemmas                  false
% 4.01/0.98  --bmc1_k_induction                      false
% 4.01/0.98  --bmc1_non_equiv_states                 false
% 4.01/0.98  --bmc1_deadlock                         false
% 4.01/0.98  --bmc1_ucm                              false
% 4.01/0.98  --bmc1_add_unsat_core                   none
% 4.01/0.98  --bmc1_unsat_core_children              false
% 4.01/0.98  --bmc1_unsat_core_extrapolate_axioms    false
% 4.01/0.98  --bmc1_out_stat                         full
% 4.01/0.98  --bmc1_ground_init                      false
% 4.01/0.98  --bmc1_pre_inst_next_state              false
% 4.01/0.98  --bmc1_pre_inst_state                   false
% 4.01/0.98  --bmc1_pre_inst_reach_state             false
% 4.01/0.98  --bmc1_out_unsat_core                   false
% 4.01/0.98  --bmc1_aig_witness_out                  false
% 4.01/0.98  --bmc1_verbose                          false
% 4.01/0.98  --bmc1_dump_clauses_tptp                false
% 4.01/0.98  --bmc1_dump_unsat_core_tptp             false
% 4.01/0.98  --bmc1_dump_file                        -
% 4.01/0.98  --bmc1_ucm_expand_uc_limit              128
% 4.01/0.98  --bmc1_ucm_n_expand_iterations          6
% 4.01/0.98  --bmc1_ucm_extend_mode                  1
% 4.01/0.98  --bmc1_ucm_init_mode                    2
% 4.01/0.98  --bmc1_ucm_cone_mode                    none
% 4.01/0.98  --bmc1_ucm_reduced_relation_type        0
% 4.01/0.98  --bmc1_ucm_relax_model                  4
% 4.01/0.98  --bmc1_ucm_full_tr_after_sat            true
% 4.01/0.98  --bmc1_ucm_expand_neg_assumptions       false
% 4.01/0.98  --bmc1_ucm_layered_model                none
% 4.01/0.98  --bmc1_ucm_max_lemma_size               10
% 4.01/0.98  
% 4.01/0.98  ------ AIG Options
% 4.01/0.98  
% 4.01/0.98  --aig_mode                              false
% 4.01/0.98  
% 4.01/0.98  ------ Instantiation Options
% 4.01/0.98  
% 4.01/0.98  --instantiation_flag                    true
% 4.01/0.98  --inst_sos_flag                         false
% 4.01/0.98  --inst_sos_phase                        true
% 4.01/0.98  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 4.01/0.98  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 4.01/0.98  --inst_lit_sel_side                     num_symb
% 4.01/0.98  --inst_solver_per_active                1400
% 4.01/0.98  --inst_solver_calls_frac                1.
% 4.01/0.98  --inst_passive_queue_type               priority_queues
% 4.01/0.98  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 4.01/0.98  --inst_passive_queues_freq              [25;2]
% 4.01/0.98  --inst_dismatching                      true
% 4.01/0.98  --inst_eager_unprocessed_to_passive     true
% 4.01/0.98  --inst_prop_sim_given                   true
% 4.01/0.98  --inst_prop_sim_new                     false
% 4.01/0.98  --inst_subs_new                         false
% 4.01/0.98  --inst_eq_res_simp                      false
% 4.01/0.98  --inst_subs_given                       false
% 4.01/0.98  --inst_orphan_elimination               true
% 4.01/0.98  --inst_learning_loop_flag               true
% 4.01/0.98  --inst_learning_start                   3000
% 4.01/0.98  --inst_learning_factor                  2
% 4.01/0.98  --inst_start_prop_sim_after_learn       3
% 4.01/0.98  --inst_sel_renew                        solver
% 4.01/0.98  --inst_lit_activity_flag                true
% 4.01/0.98  --inst_restr_to_given                   false
% 4.01/0.98  --inst_activity_threshold               500
% 4.01/0.98  --inst_out_proof                        true
% 4.01/0.98  
% 4.01/0.98  ------ Resolution Options
% 4.01/0.98  
% 4.01/0.98  --resolution_flag                       true
% 4.01/0.98  --res_lit_sel                           adaptive
% 4.01/0.98  --res_lit_sel_side                      none
% 4.01/0.98  --res_ordering                          kbo
% 4.01/0.98  --res_to_prop_solver                    active
% 4.01/0.98  --res_prop_simpl_new                    false
% 4.01/0.98  --res_prop_simpl_given                  true
% 4.01/0.98  --res_passive_queue_type                priority_queues
% 4.01/0.98  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 4.01/0.98  --res_passive_queues_freq               [15;5]
% 4.01/0.98  --res_forward_subs                      full
% 4.01/0.98  --res_backward_subs                     full
% 4.01/0.98  --res_forward_subs_resolution           true
% 4.01/0.98  --res_backward_subs_resolution          true
% 4.01/0.98  --res_orphan_elimination                true
% 4.01/0.98  --res_time_limit                        2.
% 4.01/0.98  --res_out_proof                         true
% 4.01/0.98  
% 4.01/0.98  ------ Superposition Options
% 4.01/0.98  
% 4.01/0.98  --superposition_flag                    true
% 4.01/0.98  --sup_passive_queue_type                priority_queues
% 4.01/0.98  --sup_passive_queues                    [[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 4.01/0.98  --sup_passive_queues_freq               [1;4]
% 4.01/0.98  --demod_completeness_check              fast
% 4.01/0.98  --demod_use_ground                      true
% 4.01/0.98  --sup_to_prop_solver                    passive
% 4.01/0.98  --sup_prop_simpl_new                    true
% 4.01/0.98  --sup_prop_simpl_given                  true
% 4.01/0.98  --sup_fun_splitting                     false
% 4.01/0.98  --sup_smt_interval                      50000
% 4.01/0.98  
% 4.01/0.98  ------ Superposition Simplification Setup
% 4.01/0.98  
% 4.01/0.98  --sup_indices_passive                   []
% 4.01/0.98  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 4.01/0.98  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 4.01/0.98  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 4.01/0.98  --sup_full_triv                         [TrivRules;PropSubs]
% 4.01/0.98  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 4.01/0.98  --sup_full_bw                           [BwDemod]
% 4.01/0.98  --sup_immed_triv                        [TrivRules]
% 4.01/0.98  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 4.01/0.98  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 4.01/0.98  --sup_immed_bw_main                     []
% 4.01/0.98  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 4.01/0.98  --sup_input_triv                        [Unflattening;TrivRules]
% 4.01/0.98  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 4.01/0.98  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 4.01/0.98  
% 4.01/0.98  ------ Combination Options
% 4.01/0.98  
% 4.01/0.98  --comb_res_mult                         3
% 4.01/0.98  --comb_sup_mult                         2
% 4.01/0.98  --comb_inst_mult                        10
% 4.01/0.98  
% 4.01/0.98  ------ Debug Options
% 4.01/0.98  
% 4.01/0.98  --dbg_backtrace                         false
% 4.01/0.98  --dbg_dump_prop_clauses                 false
% 4.01/0.98  --dbg_dump_prop_clauses_file            -
% 4.01/0.98  --dbg_out_stat                          false
% 4.01/0.98  
% 4.01/0.98  
% 4.01/0.98  
% 4.01/0.98  
% 4.01/0.98  ------ Proving...
% 4.01/0.98  
% 4.01/0.98  
% 4.01/0.98  % SZS status Theorem for theBenchmark.p
% 4.01/0.98  
% 4.01/0.98  % SZS output start CNFRefutation for theBenchmark.p
% 4.01/0.98  
% 4.01/0.98  fof(f14,conjecture,(
% 4.01/0.98    ! [X0] : ((l1_orders_2(X0) & v2_lattice3(X0) & v1_lattice3(X0) & v5_orders_2(X0) & v4_orders_2(X0) & v3_orders_2(X0)) => ! [X1] : (m1_subset_1(X1,u1_struct_0(X0)) => (v5_waybel_6(X1,X0) => v4_waybel_7(X1,X0))))),
% 4.01/0.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 4.01/0.98  
% 4.01/0.98  fof(f15,negated_conjecture,(
% 4.01/0.98    ~! [X0] : ((l1_orders_2(X0) & v2_lattice3(X0) & v1_lattice3(X0) & v5_orders_2(X0) & v4_orders_2(X0) & v3_orders_2(X0)) => ! [X1] : (m1_subset_1(X1,u1_struct_0(X0)) => (v5_waybel_6(X1,X0) => v4_waybel_7(X1,X0))))),
% 4.01/0.98    inference(negated_conjecture,[],[f14])).
% 4.01/0.98  
% 4.01/0.98  fof(f42,plain,(
% 4.01/0.98    ? [X0] : (? [X1] : ((~v4_waybel_7(X1,X0) & v5_waybel_6(X1,X0)) & m1_subset_1(X1,u1_struct_0(X0))) & (l1_orders_2(X0) & v2_lattice3(X0) & v1_lattice3(X0) & v5_orders_2(X0) & v4_orders_2(X0) & v3_orders_2(X0)))),
% 4.01/0.98    inference(ennf_transformation,[],[f15])).
% 4.01/0.98  
% 4.01/0.98  fof(f43,plain,(
% 4.01/0.98    ? [X0] : (? [X1] : (~v4_waybel_7(X1,X0) & v5_waybel_6(X1,X0) & m1_subset_1(X1,u1_struct_0(X0))) & l1_orders_2(X0) & v2_lattice3(X0) & v1_lattice3(X0) & v5_orders_2(X0) & v4_orders_2(X0) & v3_orders_2(X0))),
% 4.01/0.98    inference(flattening,[],[f42])).
% 4.01/0.98  
% 4.01/0.98  fof(f57,plain,(
% 4.01/0.98    ( ! [X0] : (? [X1] : (~v4_waybel_7(X1,X0) & v5_waybel_6(X1,X0) & m1_subset_1(X1,u1_struct_0(X0))) => (~v4_waybel_7(sK4,X0) & v5_waybel_6(sK4,X0) & m1_subset_1(sK4,u1_struct_0(X0)))) )),
% 4.01/0.98    introduced(choice_axiom,[])).
% 4.01/0.98  
% 4.01/0.98  fof(f56,plain,(
% 4.01/0.98    ? [X0] : (? [X1] : (~v4_waybel_7(X1,X0) & v5_waybel_6(X1,X0) & m1_subset_1(X1,u1_struct_0(X0))) & l1_orders_2(X0) & v2_lattice3(X0) & v1_lattice3(X0) & v5_orders_2(X0) & v4_orders_2(X0) & v3_orders_2(X0)) => (? [X1] : (~v4_waybel_7(X1,sK3) & v5_waybel_6(X1,sK3) & m1_subset_1(X1,u1_struct_0(sK3))) & l1_orders_2(sK3) & v2_lattice3(sK3) & v1_lattice3(sK3) & v5_orders_2(sK3) & v4_orders_2(sK3) & v3_orders_2(sK3))),
% 4.01/0.98    introduced(choice_axiom,[])).
% 4.01/0.98  
% 4.01/0.98  fof(f58,plain,(
% 4.01/0.98    (~v4_waybel_7(sK4,sK3) & v5_waybel_6(sK4,sK3) & m1_subset_1(sK4,u1_struct_0(sK3))) & l1_orders_2(sK3) & v2_lattice3(sK3) & v1_lattice3(sK3) & v5_orders_2(sK3) & v4_orders_2(sK3) & v3_orders_2(sK3)),
% 4.01/0.98    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3,sK4])],[f43,f57,f56])).
% 4.01/0.98  
% 4.01/0.98  fof(f97,plain,(
% 4.01/0.98    m1_subset_1(sK4,u1_struct_0(sK3))),
% 4.01/0.98    inference(cnf_transformation,[],[f58])).
% 4.01/0.98  
% 4.01/0.98  fof(f2,axiom,(
% 4.01/0.98    ! [X0,X1,X2] : ((m1_subset_1(X2,u1_struct_0(X0)) & m1_subset_1(X1,u1_struct_0(X0)) & l1_orders_2(X0) & v3_orders_2(X0) & ~v2_struct_0(X0)) => (r3_orders_2(X0,X1,X2) <=> r1_orders_2(X0,X1,X2)))),
% 4.01/0.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 4.01/0.98  
% 4.01/0.98  fof(f19,plain,(
% 4.01/0.98    ! [X0,X1,X2] : ((r3_orders_2(X0,X1,X2) <=> r1_orders_2(X0,X1,X2)) | (~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_orders_2(X0) | ~v3_orders_2(X0) | v2_struct_0(X0)))),
% 4.01/0.98    inference(ennf_transformation,[],[f2])).
% 4.01/0.98  
% 4.01/0.98  fof(f20,plain,(
% 4.01/0.98    ! [X0,X1,X2] : ((r3_orders_2(X0,X1,X2) <=> r1_orders_2(X0,X1,X2)) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_orders_2(X0) | ~v3_orders_2(X0) | v2_struct_0(X0))),
% 4.01/0.98    inference(flattening,[],[f19])).
% 4.01/0.98  
% 4.01/0.98  fof(f44,plain,(
% 4.01/0.98    ! [X0,X1,X2] : (((r3_orders_2(X0,X1,X2) | ~r1_orders_2(X0,X1,X2)) & (r1_orders_2(X0,X1,X2) | ~r3_orders_2(X0,X1,X2))) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_orders_2(X0) | ~v3_orders_2(X0) | v2_struct_0(X0))),
% 4.01/0.98    inference(nnf_transformation,[],[f20])).
% 4.01/0.98  
% 4.01/0.98  fof(f60,plain,(
% 4.01/0.98    ( ! [X2,X0,X1] : (r1_orders_2(X0,X1,X2) | ~r3_orders_2(X0,X1,X2) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_orders_2(X0) | ~v3_orders_2(X0) | v2_struct_0(X0)) )),
% 4.01/0.98    inference(cnf_transformation,[],[f44])).
% 4.01/0.98  
% 4.01/0.98  fof(f91,plain,(
% 4.01/0.98    v3_orders_2(sK3)),
% 4.01/0.98    inference(cnf_transformation,[],[f58])).
% 4.01/0.98  
% 4.01/0.98  fof(f94,plain,(
% 4.01/0.98    v1_lattice3(sK3)),
% 4.01/0.98    inference(cnf_transformation,[],[f58])).
% 4.01/0.98  
% 4.01/0.98  fof(f96,plain,(
% 4.01/0.98    l1_orders_2(sK3)),
% 4.01/0.98    inference(cnf_transformation,[],[f58])).
% 4.01/0.98  
% 4.01/0.98  fof(f4,axiom,(
% 4.01/0.98    ! [X0] : (l1_orders_2(X0) => (v1_lattice3(X0) => ~v2_struct_0(X0)))),
% 4.01/0.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 4.01/0.98  
% 4.01/0.98  fof(f23,plain,(
% 4.01/0.98    ! [X0] : ((~v2_struct_0(X0) | ~v1_lattice3(X0)) | ~l1_orders_2(X0))),
% 4.01/0.98    inference(ennf_transformation,[],[f4])).
% 4.01/0.98  
% 4.01/0.98  fof(f24,plain,(
% 4.01/0.98    ! [X0] : (~v2_struct_0(X0) | ~v1_lattice3(X0) | ~l1_orders_2(X0))),
% 4.01/0.98    inference(flattening,[],[f23])).
% 4.01/0.98  
% 4.01/0.98  fof(f63,plain,(
% 4.01/0.98    ( ! [X0] : (~v2_struct_0(X0) | ~v1_lattice3(X0) | ~l1_orders_2(X0)) )),
% 4.01/0.98    inference(cnf_transformation,[],[f24])).
% 4.01/0.98  
% 4.01/0.98  fof(f6,axiom,(
% 4.01/0.98    ! [X0,X1] : (l1_orders_2(X0) => m1_subset_1(k1_yellow_0(X0,X1),u1_struct_0(X0)))),
% 4.01/0.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 4.01/0.98  
% 4.01/0.98  fof(f27,plain,(
% 4.01/0.98    ! [X0,X1] : (m1_subset_1(k1_yellow_0(X0,X1),u1_struct_0(X0)) | ~l1_orders_2(X0))),
% 4.01/0.98    inference(ennf_transformation,[],[f6])).
% 4.01/0.98  
% 4.01/0.98  fof(f68,plain,(
% 4.01/0.98    ( ! [X0,X1] : (m1_subset_1(k1_yellow_0(X0,X1),u1_struct_0(X0)) | ~l1_orders_2(X0)) )),
% 4.01/0.98    inference(cnf_transformation,[],[f27])).
% 4.01/0.98  
% 4.01/0.98  fof(f3,axiom,(
% 4.01/0.98    ! [X0,X1,X2] : ((m1_subset_1(X2,u1_struct_0(X0)) & m1_subset_1(X1,u1_struct_0(X0)) & l1_orders_2(X0) & v3_orders_2(X0) & ~v2_struct_0(X0)) => r3_orders_2(X0,X1,X1))),
% 4.01/0.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 4.01/0.98  
% 4.01/0.98  fof(f21,plain,(
% 4.01/0.98    ! [X0,X1,X2] : (r3_orders_2(X0,X1,X1) | (~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_orders_2(X0) | ~v3_orders_2(X0) | v2_struct_0(X0)))),
% 4.01/0.98    inference(ennf_transformation,[],[f3])).
% 4.01/0.98  
% 4.01/0.98  fof(f22,plain,(
% 4.01/0.98    ! [X0,X1,X2] : (r3_orders_2(X0,X1,X1) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_orders_2(X0) | ~v3_orders_2(X0) | v2_struct_0(X0))),
% 4.01/0.98    inference(flattening,[],[f21])).
% 4.01/0.98  
% 4.01/0.98  fof(f62,plain,(
% 4.01/0.98    ( ! [X2,X0,X1] : (r3_orders_2(X0,X1,X1) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_orders_2(X0) | ~v3_orders_2(X0) | v2_struct_0(X0)) )),
% 4.01/0.98    inference(cnf_transformation,[],[f22])).
% 4.01/0.98  
% 4.01/0.98  fof(f11,axiom,(
% 4.01/0.98    ! [X0] : ((l1_orders_2(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,u1_struct_0(X0)) => ! [X2] : (m1_subset_1(X2,u1_struct_0(X0)) => (r2_hidden(X2,k5_waybel_0(X0,X1)) <=> r1_orders_2(X0,X2,X1)))))),
% 4.01/0.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 4.01/0.98  
% 4.01/0.98  fof(f36,plain,(
% 4.01/0.98    ! [X0] : (! [X1] : (! [X2] : ((r2_hidden(X2,k5_waybel_0(X0,X1)) <=> r1_orders_2(X0,X2,X1)) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~m1_subset_1(X1,u1_struct_0(X0))) | (~l1_orders_2(X0) | v2_struct_0(X0)))),
% 4.01/0.98    inference(ennf_transformation,[],[f11])).
% 4.01/0.98  
% 4.01/0.98  fof(f37,plain,(
% 4.01/0.98    ! [X0] : (! [X1] : (! [X2] : ((r2_hidden(X2,k5_waybel_0(X0,X1)) <=> r1_orders_2(X0,X2,X1)) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~l1_orders_2(X0) | v2_struct_0(X0))),
% 4.01/0.98    inference(flattening,[],[f36])).
% 4.01/0.98  
% 4.01/0.98  fof(f51,plain,(
% 4.01/0.98    ! [X0] : (! [X1] : (! [X2] : (((r2_hidden(X2,k5_waybel_0(X0,X1)) | ~r1_orders_2(X0,X2,X1)) & (r1_orders_2(X0,X2,X1) | ~r2_hidden(X2,k5_waybel_0(X0,X1)))) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~l1_orders_2(X0) | v2_struct_0(X0))),
% 4.01/0.98    inference(nnf_transformation,[],[f37])).
% 4.01/0.98  
% 4.01/0.98  fof(f82,plain,(
% 4.01/0.98    ( ! [X2,X0,X1] : (r2_hidden(X2,k5_waybel_0(X0,X1)) | ~r1_orders_2(X0,X2,X1) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_orders_2(X0) | v2_struct_0(X0)) )),
% 4.01/0.98    inference(cnf_transformation,[],[f51])).
% 4.01/0.98  
% 4.01/0.98  fof(f5,axiom,(
% 4.01/0.98    ! [X0] : (l1_orders_2(X0) => ! [X1,X2] : (m1_subset_1(X2,u1_struct_0(X0)) => (r2_lattice3(X0,X1,X2) <=> ! [X3] : (m1_subset_1(X3,u1_struct_0(X0)) => (r2_hidden(X3,X1) => r1_orders_2(X0,X3,X2))))))),
% 4.01/0.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 4.01/0.98  
% 4.01/0.98  fof(f25,plain,(
% 4.01/0.98    ! [X0] : (! [X1,X2] : ((r2_lattice3(X0,X1,X2) <=> ! [X3] : ((r1_orders_2(X0,X3,X2) | ~r2_hidden(X3,X1)) | ~m1_subset_1(X3,u1_struct_0(X0)))) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~l1_orders_2(X0))),
% 4.01/0.98    inference(ennf_transformation,[],[f5])).
% 4.01/0.98  
% 4.01/0.98  fof(f26,plain,(
% 4.01/0.98    ! [X0] : (! [X1,X2] : ((r2_lattice3(X0,X1,X2) <=> ! [X3] : (r1_orders_2(X0,X3,X2) | ~r2_hidden(X3,X1) | ~m1_subset_1(X3,u1_struct_0(X0)))) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~l1_orders_2(X0))),
% 4.01/0.98    inference(flattening,[],[f25])).
% 4.01/0.98  
% 4.01/0.98  fof(f45,plain,(
% 4.01/0.98    ! [X0] : (! [X1,X2] : (((r2_lattice3(X0,X1,X2) | ? [X3] : (~r1_orders_2(X0,X3,X2) & r2_hidden(X3,X1) & m1_subset_1(X3,u1_struct_0(X0)))) & (! [X3] : (r1_orders_2(X0,X3,X2) | ~r2_hidden(X3,X1) | ~m1_subset_1(X3,u1_struct_0(X0))) | ~r2_lattice3(X0,X1,X2))) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~l1_orders_2(X0))),
% 4.01/0.98    inference(nnf_transformation,[],[f26])).
% 4.01/0.98  
% 4.01/0.98  fof(f46,plain,(
% 4.01/0.98    ! [X0] : (! [X1,X2] : (((r2_lattice3(X0,X1,X2) | ? [X3] : (~r1_orders_2(X0,X3,X2) & r2_hidden(X3,X1) & m1_subset_1(X3,u1_struct_0(X0)))) & (! [X4] : (r1_orders_2(X0,X4,X2) | ~r2_hidden(X4,X1) | ~m1_subset_1(X4,u1_struct_0(X0))) | ~r2_lattice3(X0,X1,X2))) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~l1_orders_2(X0))),
% 4.01/0.98    inference(rectify,[],[f45])).
% 4.01/0.98  
% 4.01/0.98  fof(f47,plain,(
% 4.01/0.98    ! [X2,X1,X0] : (? [X3] : (~r1_orders_2(X0,X3,X2) & r2_hidden(X3,X1) & m1_subset_1(X3,u1_struct_0(X0))) => (~r1_orders_2(X0,sK0(X0,X1,X2),X2) & r2_hidden(sK0(X0,X1,X2),X1) & m1_subset_1(sK0(X0,X1,X2),u1_struct_0(X0))))),
% 4.01/0.98    introduced(choice_axiom,[])).
% 4.01/0.98  
% 4.01/0.98  fof(f48,plain,(
% 4.01/0.98    ! [X0] : (! [X1,X2] : (((r2_lattice3(X0,X1,X2) | (~r1_orders_2(X0,sK0(X0,X1,X2),X2) & r2_hidden(sK0(X0,X1,X2),X1) & m1_subset_1(sK0(X0,X1,X2),u1_struct_0(X0)))) & (! [X4] : (r1_orders_2(X0,X4,X2) | ~r2_hidden(X4,X1) | ~m1_subset_1(X4,u1_struct_0(X0))) | ~r2_lattice3(X0,X1,X2))) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~l1_orders_2(X0))),
% 4.01/0.98    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f46,f47])).
% 4.01/0.98  
% 4.01/0.98  fof(f66,plain,(
% 4.01/0.98    ( ! [X2,X0,X1] : (r2_lattice3(X0,X1,X2) | r2_hidden(sK0(X0,X1,X2),X1) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~l1_orders_2(X0)) )),
% 4.01/0.98    inference(cnf_transformation,[],[f48])).
% 4.01/0.98  
% 4.01/0.98  fof(f81,plain,(
% 4.01/0.98    ( ! [X2,X0,X1] : (r1_orders_2(X0,X2,X1) | ~r2_hidden(X2,k5_waybel_0(X0,X1)) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_orders_2(X0) | v2_struct_0(X0)) )),
% 4.01/0.98    inference(cnf_transformation,[],[f51])).
% 4.01/0.98  
% 4.01/0.98  fof(f8,axiom,(
% 4.01/0.98    ! [X0,X1] : ((m1_subset_1(X1,u1_struct_0(X0)) & l1_orders_2(X0) & ~v2_struct_0(X0)) => m1_subset_1(k5_waybel_0(X0,X1),k1_zfmisc_1(u1_struct_0(X0))))),
% 4.01/0.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 4.01/0.98  
% 4.01/0.98  fof(f30,plain,(
% 4.01/0.98    ! [X0,X1] : (m1_subset_1(k5_waybel_0(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) | (~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_orders_2(X0) | v2_struct_0(X0)))),
% 4.01/0.98    inference(ennf_transformation,[],[f8])).
% 4.01/0.98  
% 4.01/0.98  fof(f31,plain,(
% 4.01/0.98    ! [X0,X1] : (m1_subset_1(k5_waybel_0(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_orders_2(X0) | v2_struct_0(X0))),
% 4.01/0.98    inference(flattening,[],[f30])).
% 4.01/0.98  
% 4.01/0.98  fof(f77,plain,(
% 4.01/0.98    ( ! [X0,X1] : (m1_subset_1(k5_waybel_0(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_orders_2(X0) | v2_struct_0(X0)) )),
% 4.01/0.98    inference(cnf_transformation,[],[f31])).
% 4.01/0.98  
% 4.01/0.98  fof(f1,axiom,(
% 4.01/0.98    ! [X0,X1,X2] : ((m1_subset_1(X1,k1_zfmisc_1(X2)) & r2_hidden(X0,X1)) => m1_subset_1(X0,X2))),
% 4.01/0.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 4.01/0.98  
% 4.01/0.98  fof(f17,plain,(
% 4.01/0.98    ! [X0,X1,X2] : (m1_subset_1(X0,X2) | (~m1_subset_1(X1,k1_zfmisc_1(X2)) | ~r2_hidden(X0,X1)))),
% 4.01/0.98    inference(ennf_transformation,[],[f1])).
% 4.01/0.98  
% 4.01/0.98  fof(f18,plain,(
% 4.01/0.98    ! [X0,X1,X2] : (m1_subset_1(X0,X2) | ~m1_subset_1(X1,k1_zfmisc_1(X2)) | ~r2_hidden(X0,X1))),
% 4.01/0.98    inference(flattening,[],[f17])).
% 4.01/0.98  
% 4.01/0.98  fof(f59,plain,(
% 4.01/0.98    ( ! [X2,X0,X1] : (m1_subset_1(X0,X2) | ~m1_subset_1(X1,k1_zfmisc_1(X2)) | ~r2_hidden(X0,X1)) )),
% 4.01/0.98    inference(cnf_transformation,[],[f18])).
% 4.01/0.98  
% 4.01/0.98  fof(f67,plain,(
% 4.01/0.98    ( ! [X2,X0,X1] : (r2_lattice3(X0,X1,X2) | ~r1_orders_2(X0,sK0(X0,X1,X2),X2) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~l1_orders_2(X0)) )),
% 4.01/0.98    inference(cnf_transformation,[],[f48])).
% 4.01/0.98  
% 4.01/0.98  fof(f7,axiom,(
% 4.01/0.98    ! [X0] : ((l1_orders_2(X0) & v5_orders_2(X0)) => ! [X1] : (m1_subset_1(X1,u1_struct_0(X0)) => ! [X2] : (((! [X3] : (m1_subset_1(X3,u1_struct_0(X0)) => (r2_lattice3(X0,X2,X3) => r1_orders_2(X0,X1,X3))) & r2_lattice3(X0,X2,X1)) => (r1_yellow_0(X0,X2) & k1_yellow_0(X0,X2) = X1)) & ((r1_yellow_0(X0,X2) & k1_yellow_0(X0,X2) = X1) => (! [X3] : (m1_subset_1(X3,u1_struct_0(X0)) => (r2_lattice3(X0,X2,X3) => r1_orders_2(X0,X1,X3))) & r2_lattice3(X0,X2,X1))))))),
% 4.01/0.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 4.01/0.98  
% 4.01/0.98  fof(f16,plain,(
% 4.01/0.98    ! [X0] : ((l1_orders_2(X0) & v5_orders_2(X0)) => ! [X1] : (m1_subset_1(X1,u1_struct_0(X0)) => ! [X2] : (((! [X3] : (m1_subset_1(X3,u1_struct_0(X0)) => (r2_lattice3(X0,X2,X3) => r1_orders_2(X0,X1,X3))) & r2_lattice3(X0,X2,X1)) => (r1_yellow_0(X0,X2) & k1_yellow_0(X0,X2) = X1)) & ((r1_yellow_0(X0,X2) & k1_yellow_0(X0,X2) = X1) => (! [X4] : (m1_subset_1(X4,u1_struct_0(X0)) => (r2_lattice3(X0,X2,X4) => r1_orders_2(X0,X1,X4))) & r2_lattice3(X0,X2,X1))))))),
% 4.01/0.98    inference(rectify,[],[f7])).
% 4.01/0.98  
% 4.01/0.98  fof(f28,plain,(
% 4.01/0.98    ! [X0] : (! [X1] : (! [X2] : (((r1_yellow_0(X0,X2) & k1_yellow_0(X0,X2) = X1) | (? [X3] : ((~r1_orders_2(X0,X1,X3) & r2_lattice3(X0,X2,X3)) & m1_subset_1(X3,u1_struct_0(X0))) | ~r2_lattice3(X0,X2,X1))) & ((! [X4] : ((r1_orders_2(X0,X1,X4) | ~r2_lattice3(X0,X2,X4)) | ~m1_subset_1(X4,u1_struct_0(X0))) & r2_lattice3(X0,X2,X1)) | (~r1_yellow_0(X0,X2) | k1_yellow_0(X0,X2) != X1))) | ~m1_subset_1(X1,u1_struct_0(X0))) | (~l1_orders_2(X0) | ~v5_orders_2(X0)))),
% 4.01/0.98    inference(ennf_transformation,[],[f16])).
% 4.01/0.98  
% 4.01/0.98  fof(f29,plain,(
% 4.01/0.98    ! [X0] : (! [X1] : (! [X2] : (((r1_yellow_0(X0,X2) & k1_yellow_0(X0,X2) = X1) | ? [X3] : (~r1_orders_2(X0,X1,X3) & r2_lattice3(X0,X2,X3) & m1_subset_1(X3,u1_struct_0(X0))) | ~r2_lattice3(X0,X2,X1)) & ((! [X4] : (r1_orders_2(X0,X1,X4) | ~r2_lattice3(X0,X2,X4) | ~m1_subset_1(X4,u1_struct_0(X0))) & r2_lattice3(X0,X2,X1)) | ~r1_yellow_0(X0,X2) | k1_yellow_0(X0,X2) != X1)) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~l1_orders_2(X0) | ~v5_orders_2(X0))),
% 4.01/0.98    inference(flattening,[],[f28])).
% 4.01/0.98  
% 4.01/0.98  fof(f49,plain,(
% 4.01/0.98    ! [X2,X1,X0] : (? [X3] : (~r1_orders_2(X0,X1,X3) & r2_lattice3(X0,X2,X3) & m1_subset_1(X3,u1_struct_0(X0))) => (~r1_orders_2(X0,X1,sK1(X0,X1,X2)) & r2_lattice3(X0,X2,sK1(X0,X1,X2)) & m1_subset_1(sK1(X0,X1,X2),u1_struct_0(X0))))),
% 4.01/0.98    introduced(choice_axiom,[])).
% 4.01/0.98  
% 4.01/0.98  fof(f50,plain,(
% 4.01/0.98    ! [X0] : (! [X1] : (! [X2] : (((r1_yellow_0(X0,X2) & k1_yellow_0(X0,X2) = X1) | (~r1_orders_2(X0,X1,sK1(X0,X1,X2)) & r2_lattice3(X0,X2,sK1(X0,X1,X2)) & m1_subset_1(sK1(X0,X1,X2),u1_struct_0(X0))) | ~r2_lattice3(X0,X2,X1)) & ((! [X4] : (r1_orders_2(X0,X1,X4) | ~r2_lattice3(X0,X2,X4) | ~m1_subset_1(X4,u1_struct_0(X0))) & r2_lattice3(X0,X2,X1)) | ~r1_yellow_0(X0,X2) | k1_yellow_0(X0,X2) != X1)) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~l1_orders_2(X0) | ~v5_orders_2(X0))),
% 4.01/0.98    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1])],[f29,f49])).
% 4.01/0.98  
% 4.01/0.98  fof(f72,plain,(
% 4.01/0.98    ( ! [X2,X0,X1] : (k1_yellow_0(X0,X2) = X1 | r2_lattice3(X0,X2,sK1(X0,X1,X2)) | ~r2_lattice3(X0,X2,X1) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_orders_2(X0) | ~v5_orders_2(X0)) )),
% 4.01/0.98    inference(cnf_transformation,[],[f50])).
% 4.01/0.98  
% 4.01/0.98  fof(f71,plain,(
% 4.01/0.98    ( ! [X2,X0,X1] : (k1_yellow_0(X0,X2) = X1 | m1_subset_1(sK1(X0,X1,X2),u1_struct_0(X0)) | ~r2_lattice3(X0,X2,X1) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_orders_2(X0) | ~v5_orders_2(X0)) )),
% 4.01/0.98    inference(cnf_transformation,[],[f50])).
% 4.01/0.98  
% 4.01/0.98  fof(f64,plain,(
% 4.01/0.98    ( ! [X4,X2,X0,X1] : (r1_orders_2(X0,X4,X2) | ~r2_hidden(X4,X1) | ~m1_subset_1(X4,u1_struct_0(X0)) | ~r2_lattice3(X0,X1,X2) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~l1_orders_2(X0)) )),
% 4.01/0.98    inference(cnf_transformation,[],[f48])).
% 4.01/0.98  
% 4.01/0.98  fof(f73,plain,(
% 4.01/0.98    ( ! [X2,X0,X1] : (k1_yellow_0(X0,X2) = X1 | ~r1_orders_2(X0,X1,sK1(X0,X1,X2)) | ~r2_lattice3(X0,X2,X1) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_orders_2(X0) | ~v5_orders_2(X0)) )),
% 4.01/0.98    inference(cnf_transformation,[],[f50])).
% 4.01/0.98  
% 4.01/0.98  fof(f93,plain,(
% 4.01/0.98    v5_orders_2(sK3)),
% 4.01/0.98    inference(cnf_transformation,[],[f58])).
% 4.01/0.98  
% 4.01/0.98  fof(f12,axiom,(
% 4.01/0.98    ! [X0] : ((l1_orders_2(X0) & v2_lattice3(X0) & v1_lattice3(X0) & v5_orders_2(X0) & v4_orders_2(X0) & v3_orders_2(X0)) => ! [X1] : (m1_subset_1(X1,u1_struct_0(X0)) => (v4_waybel_7(X1,X0) <=> ? [X2] : (k1_yellow_0(X0,X2) = X1 & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) & v1_waybel_7(X2,X0) & v12_waybel_0(X2,X0) & v1_waybel_0(X2,X0) & ~v1_xboole_0(X2)))))),
% 4.01/0.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 4.01/0.98  
% 4.01/0.98  fof(f38,plain,(
% 4.01/0.98    ! [X0] : (! [X1] : ((v4_waybel_7(X1,X0) <=> ? [X2] : (k1_yellow_0(X0,X2) = X1 & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) & v1_waybel_7(X2,X0) & v12_waybel_0(X2,X0) & v1_waybel_0(X2,X0) & ~v1_xboole_0(X2))) | ~m1_subset_1(X1,u1_struct_0(X0))) | (~l1_orders_2(X0) | ~v2_lattice3(X0) | ~v1_lattice3(X0) | ~v5_orders_2(X0) | ~v4_orders_2(X0) | ~v3_orders_2(X0)))),
% 4.01/0.98    inference(ennf_transformation,[],[f12])).
% 4.01/0.98  
% 4.01/0.98  fof(f39,plain,(
% 4.01/0.98    ! [X0] : (! [X1] : ((v4_waybel_7(X1,X0) <=> ? [X2] : (k1_yellow_0(X0,X2) = X1 & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) & v1_waybel_7(X2,X0) & v12_waybel_0(X2,X0) & v1_waybel_0(X2,X0) & ~v1_xboole_0(X2))) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~l1_orders_2(X0) | ~v2_lattice3(X0) | ~v1_lattice3(X0) | ~v5_orders_2(X0) | ~v4_orders_2(X0) | ~v3_orders_2(X0))),
% 4.01/0.98    inference(flattening,[],[f38])).
% 4.01/0.98  
% 4.01/0.98  fof(f52,plain,(
% 4.01/0.98    ! [X0] : (! [X1] : (((v4_waybel_7(X1,X0) | ! [X2] : (k1_yellow_0(X0,X2) != X1 | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) | ~v1_waybel_7(X2,X0) | ~v12_waybel_0(X2,X0) | ~v1_waybel_0(X2,X0) | v1_xboole_0(X2))) & (? [X2] : (k1_yellow_0(X0,X2) = X1 & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) & v1_waybel_7(X2,X0) & v12_waybel_0(X2,X0) & v1_waybel_0(X2,X0) & ~v1_xboole_0(X2)) | ~v4_waybel_7(X1,X0))) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~l1_orders_2(X0) | ~v2_lattice3(X0) | ~v1_lattice3(X0) | ~v5_orders_2(X0) | ~v4_orders_2(X0) | ~v3_orders_2(X0))),
% 4.01/0.98    inference(nnf_transformation,[],[f39])).
% 4.01/0.98  
% 4.01/0.98  fof(f53,plain,(
% 4.01/0.98    ! [X0] : (! [X1] : (((v4_waybel_7(X1,X0) | ! [X2] : (k1_yellow_0(X0,X2) != X1 | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) | ~v1_waybel_7(X2,X0) | ~v12_waybel_0(X2,X0) | ~v1_waybel_0(X2,X0) | v1_xboole_0(X2))) & (? [X3] : (k1_yellow_0(X0,X3) = X1 & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) & v1_waybel_7(X3,X0) & v12_waybel_0(X3,X0) & v1_waybel_0(X3,X0) & ~v1_xboole_0(X3)) | ~v4_waybel_7(X1,X0))) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~l1_orders_2(X0) | ~v2_lattice3(X0) | ~v1_lattice3(X0) | ~v5_orders_2(X0) | ~v4_orders_2(X0) | ~v3_orders_2(X0))),
% 4.01/0.98    inference(rectify,[],[f52])).
% 4.01/0.98  
% 4.01/0.98  fof(f54,plain,(
% 4.01/0.98    ! [X1,X0] : (? [X3] : (k1_yellow_0(X0,X3) = X1 & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) & v1_waybel_7(X3,X0) & v12_waybel_0(X3,X0) & v1_waybel_0(X3,X0) & ~v1_xboole_0(X3)) => (k1_yellow_0(X0,sK2(X0,X1)) = X1 & m1_subset_1(sK2(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) & v1_waybel_7(sK2(X0,X1),X0) & v12_waybel_0(sK2(X0,X1),X0) & v1_waybel_0(sK2(X0,X1),X0) & ~v1_xboole_0(sK2(X0,X1))))),
% 4.01/0.98    introduced(choice_axiom,[])).
% 4.01/0.98  
% 4.01/0.98  fof(f55,plain,(
% 4.01/0.98    ! [X0] : (! [X1] : (((v4_waybel_7(X1,X0) | ! [X2] : (k1_yellow_0(X0,X2) != X1 | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) | ~v1_waybel_7(X2,X0) | ~v12_waybel_0(X2,X0) | ~v1_waybel_0(X2,X0) | v1_xboole_0(X2))) & ((k1_yellow_0(X0,sK2(X0,X1)) = X1 & m1_subset_1(sK2(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) & v1_waybel_7(sK2(X0,X1),X0) & v12_waybel_0(sK2(X0,X1),X0) & v1_waybel_0(sK2(X0,X1),X0) & ~v1_xboole_0(sK2(X0,X1))) | ~v4_waybel_7(X1,X0))) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~l1_orders_2(X0) | ~v2_lattice3(X0) | ~v1_lattice3(X0) | ~v5_orders_2(X0) | ~v4_orders_2(X0) | ~v3_orders_2(X0))),
% 4.01/0.98    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2])],[f53,f54])).
% 4.01/0.98  
% 4.01/0.98  fof(f89,plain,(
% 4.01/0.98    ( ! [X2,X0,X1] : (v4_waybel_7(X1,X0) | k1_yellow_0(X0,X2) != X1 | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) | ~v1_waybel_7(X2,X0) | ~v12_waybel_0(X2,X0) | ~v1_waybel_0(X2,X0) | v1_xboole_0(X2) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_orders_2(X0) | ~v2_lattice3(X0) | ~v1_lattice3(X0) | ~v5_orders_2(X0) | ~v4_orders_2(X0) | ~v3_orders_2(X0)) )),
% 4.01/0.98    inference(cnf_transformation,[],[f55])).
% 4.01/0.98  
% 4.01/0.98  fof(f102,plain,(
% 4.01/0.98    ( ! [X2,X0] : (v4_waybel_7(k1_yellow_0(X0,X2),X0) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) | ~v1_waybel_7(X2,X0) | ~v12_waybel_0(X2,X0) | ~v1_waybel_0(X2,X0) | v1_xboole_0(X2) | ~m1_subset_1(k1_yellow_0(X0,X2),u1_struct_0(X0)) | ~l1_orders_2(X0) | ~v2_lattice3(X0) | ~v1_lattice3(X0) | ~v5_orders_2(X0) | ~v4_orders_2(X0) | ~v3_orders_2(X0)) )),
% 4.01/0.98    inference(equality_resolution,[],[f89])).
% 4.01/0.98  
% 4.01/0.98  fof(f10,axiom,(
% 4.01/0.98    ! [X0,X1] : ((m1_subset_1(X1,u1_struct_0(X0)) & l1_orders_2(X0) & v3_orders_2(X0) & ~v2_struct_0(X0)) => (v1_waybel_0(k5_waybel_0(X0,X1),X0) & ~v1_xboole_0(k5_waybel_0(X0,X1))))),
% 4.01/0.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 4.01/0.98  
% 4.01/0.98  fof(f34,plain,(
% 4.01/0.98    ! [X0,X1] : ((v1_waybel_0(k5_waybel_0(X0,X1),X0) & ~v1_xboole_0(k5_waybel_0(X0,X1))) | (~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_orders_2(X0) | ~v3_orders_2(X0) | v2_struct_0(X0)))),
% 4.01/0.98    inference(ennf_transformation,[],[f10])).
% 4.01/0.98  
% 4.01/0.98  fof(f35,plain,(
% 4.01/0.98    ! [X0,X1] : ((v1_waybel_0(k5_waybel_0(X0,X1),X0) & ~v1_xboole_0(k5_waybel_0(X0,X1))) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_orders_2(X0) | ~v3_orders_2(X0) | v2_struct_0(X0))),
% 4.01/0.98    inference(flattening,[],[f34])).
% 4.01/0.98  
% 4.01/0.98  fof(f80,plain,(
% 4.01/0.98    ( ! [X0,X1] : (v1_waybel_0(k5_waybel_0(X0,X1),X0) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_orders_2(X0) | ~v3_orders_2(X0) | v2_struct_0(X0)) )),
% 4.01/0.98    inference(cnf_transformation,[],[f35])).
% 4.01/0.98  
% 4.01/0.98  fof(f9,axiom,(
% 4.01/0.98    ! [X0,X1] : ((m1_subset_1(X1,u1_struct_0(X0)) & l1_orders_2(X0) & v4_orders_2(X0) & ~v2_struct_0(X0)) => v12_waybel_0(k5_waybel_0(X0,X1),X0))),
% 4.01/0.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 4.01/0.98  
% 4.01/0.98  fof(f32,plain,(
% 4.01/0.98    ! [X0,X1] : (v12_waybel_0(k5_waybel_0(X0,X1),X0) | (~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_orders_2(X0) | ~v4_orders_2(X0) | v2_struct_0(X0)))),
% 4.01/0.98    inference(ennf_transformation,[],[f9])).
% 4.01/0.98  
% 4.01/0.98  fof(f33,plain,(
% 4.01/0.98    ! [X0,X1] : (v12_waybel_0(k5_waybel_0(X0,X1),X0) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_orders_2(X0) | ~v4_orders_2(X0) | v2_struct_0(X0))),
% 4.01/0.98    inference(flattening,[],[f32])).
% 4.01/0.98  
% 4.01/0.98  fof(f78,plain,(
% 4.01/0.98    ( ! [X0,X1] : (v12_waybel_0(k5_waybel_0(X0,X1),X0) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_orders_2(X0) | ~v4_orders_2(X0) | v2_struct_0(X0)) )),
% 4.01/0.98    inference(cnf_transformation,[],[f33])).
% 4.01/0.98  
% 4.01/0.98  fof(f79,plain,(
% 4.01/0.98    ( ! [X0,X1] : (~v1_xboole_0(k5_waybel_0(X0,X1)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_orders_2(X0) | ~v3_orders_2(X0) | v2_struct_0(X0)) )),
% 4.01/0.98    inference(cnf_transformation,[],[f35])).
% 4.01/0.98  
% 4.01/0.98  fof(f13,axiom,(
% 4.01/0.98    ! [X0] : ((l1_orders_2(X0) & v2_lattice3(X0) & v1_lattice3(X0) & v5_orders_2(X0) & v4_orders_2(X0) & v3_orders_2(X0)) => ! [X1] : (m1_subset_1(X1,u1_struct_0(X0)) => (v5_waybel_6(X1,X0) => v1_waybel_7(k5_waybel_0(X0,X1),X0))))),
% 4.01/0.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 4.01/0.98  
% 4.01/0.98  fof(f40,plain,(
% 4.01/0.98    ! [X0] : (! [X1] : ((v1_waybel_7(k5_waybel_0(X0,X1),X0) | ~v5_waybel_6(X1,X0)) | ~m1_subset_1(X1,u1_struct_0(X0))) | (~l1_orders_2(X0) | ~v2_lattice3(X0) | ~v1_lattice3(X0) | ~v5_orders_2(X0) | ~v4_orders_2(X0) | ~v3_orders_2(X0)))),
% 4.01/0.98    inference(ennf_transformation,[],[f13])).
% 4.01/0.98  
% 4.01/0.98  fof(f41,plain,(
% 4.01/0.98    ! [X0] : (! [X1] : (v1_waybel_7(k5_waybel_0(X0,X1),X0) | ~v5_waybel_6(X1,X0) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~l1_orders_2(X0) | ~v2_lattice3(X0) | ~v1_lattice3(X0) | ~v5_orders_2(X0) | ~v4_orders_2(X0) | ~v3_orders_2(X0))),
% 4.01/0.98    inference(flattening,[],[f40])).
% 4.01/0.98  
% 4.01/0.98  fof(f90,plain,(
% 4.01/0.98    ( ! [X0,X1] : (v1_waybel_7(k5_waybel_0(X0,X1),X0) | ~v5_waybel_6(X1,X0) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_orders_2(X0) | ~v2_lattice3(X0) | ~v1_lattice3(X0) | ~v5_orders_2(X0) | ~v4_orders_2(X0) | ~v3_orders_2(X0)) )),
% 4.01/0.98    inference(cnf_transformation,[],[f41])).
% 4.01/0.98  
% 4.01/0.98  fof(f99,plain,(
% 4.01/0.98    ~v4_waybel_7(sK4,sK3)),
% 4.01/0.98    inference(cnf_transformation,[],[f58])).
% 4.01/0.98  
% 4.01/0.98  fof(f98,plain,(
% 4.01/0.98    v5_waybel_6(sK4,sK3)),
% 4.01/0.98    inference(cnf_transformation,[],[f58])).
% 4.01/0.98  
% 4.01/0.98  fof(f95,plain,(
% 4.01/0.98    v2_lattice3(sK3)),
% 4.01/0.98    inference(cnf_transformation,[],[f58])).
% 4.01/0.98  
% 4.01/0.98  fof(f92,plain,(
% 4.01/0.98    v4_orders_2(sK3)),
% 4.01/0.98    inference(cnf_transformation,[],[f58])).
% 4.01/0.98  
% 4.01/0.98  cnf(c_34,negated_conjecture,
% 4.01/0.98      ( m1_subset_1(sK4,u1_struct_0(sK3)) ),
% 4.01/0.98      inference(cnf_transformation,[],[f97]) ).
% 4.01/0.98  
% 4.01/0.98  cnf(c_1166,plain,
% 4.01/0.98      ( m1_subset_1(sK4,u1_struct_0(sK3)) = iProver_top ),
% 4.01/0.98      inference(predicate_to_equality,[status(thm)],[c_34]) ).
% 4.01/0.98  
% 4.01/0.98  cnf(c_2,plain,
% 4.01/0.98      ( r1_orders_2(X0,X1,X2)
% 4.01/0.98      | ~ r3_orders_2(X0,X1,X2)
% 4.01/0.98      | ~ m1_subset_1(X2,u1_struct_0(X0))
% 4.01/0.98      | ~ m1_subset_1(X1,u1_struct_0(X0))
% 4.01/0.98      | v2_struct_0(X0)
% 4.01/0.98      | ~ v3_orders_2(X0)
% 4.01/0.98      | ~ l1_orders_2(X0) ),
% 4.01/0.98      inference(cnf_transformation,[],[f60]) ).
% 4.01/0.98  
% 4.01/0.98  cnf(c_1196,plain,
% 4.01/0.98      ( r1_orders_2(X0,X1,X2) = iProver_top
% 4.01/0.98      | r3_orders_2(X0,X1,X2) != iProver_top
% 4.01/0.98      | m1_subset_1(X1,u1_struct_0(X0)) != iProver_top
% 4.01/0.98      | m1_subset_1(X2,u1_struct_0(X0)) != iProver_top
% 4.01/0.98      | v2_struct_0(X0) = iProver_top
% 4.01/0.98      | v3_orders_2(X0) != iProver_top
% 4.01/0.98      | l1_orders_2(X0) != iProver_top ),
% 4.01/0.98      inference(predicate_to_equality,[status(thm)],[c_2]) ).
% 4.01/0.98  
% 4.01/0.98  cnf(c_3874,plain,
% 4.01/0.98      ( r1_orders_2(sK3,sK4,X0) = iProver_top
% 4.01/0.98      | r3_orders_2(sK3,sK4,X0) != iProver_top
% 4.01/0.98      | m1_subset_1(X0,u1_struct_0(sK3)) != iProver_top
% 4.01/0.98      | v2_struct_0(sK3) = iProver_top
% 4.01/0.98      | v3_orders_2(sK3) != iProver_top
% 4.01/0.98      | l1_orders_2(sK3) != iProver_top ),
% 4.01/0.98      inference(superposition,[status(thm)],[c_1166,c_1196]) ).
% 4.01/0.98  
% 4.01/0.98  cnf(c_40,negated_conjecture,
% 4.01/0.98      ( v3_orders_2(sK3) ),
% 4.01/0.98      inference(cnf_transformation,[],[f91]) ).
% 4.01/0.98  
% 4.01/0.98  cnf(c_41,plain,
% 4.01/0.98      ( v3_orders_2(sK3) = iProver_top ),
% 4.01/0.98      inference(predicate_to_equality,[status(thm)],[c_40]) ).
% 4.01/0.98  
% 4.01/0.98  cnf(c_37,negated_conjecture,
% 4.01/0.98      ( v1_lattice3(sK3) ),
% 4.01/0.98      inference(cnf_transformation,[],[f94]) ).
% 4.01/0.98  
% 4.01/0.98  cnf(c_44,plain,
% 4.01/0.98      ( v1_lattice3(sK3) = iProver_top ),
% 4.01/0.98      inference(predicate_to_equality,[status(thm)],[c_37]) ).
% 4.01/0.98  
% 4.01/0.98  cnf(c_35,negated_conjecture,
% 4.01/0.98      ( l1_orders_2(sK3) ),
% 4.01/0.98      inference(cnf_transformation,[],[f96]) ).
% 4.01/0.98  
% 4.01/0.98  cnf(c_46,plain,
% 4.01/0.98      ( l1_orders_2(sK3) = iProver_top ),
% 4.01/0.98      inference(predicate_to_equality,[status(thm)],[c_35]) ).
% 4.01/0.98  
% 4.01/0.98  cnf(c_4,plain,
% 4.01/0.98      ( ~ v1_lattice3(X0) | ~ v2_struct_0(X0) | ~ l1_orders_2(X0) ),
% 4.01/0.98      inference(cnf_transformation,[],[f63]) ).
% 4.01/0.98  
% 4.01/0.98  cnf(c_131,plain,
% 4.01/0.98      ( v1_lattice3(X0) != iProver_top
% 4.01/0.98      | v2_struct_0(X0) != iProver_top
% 4.01/0.98      | l1_orders_2(X0) != iProver_top ),
% 4.01/0.98      inference(predicate_to_equality,[status(thm)],[c_4]) ).
% 4.01/0.98  
% 4.01/0.98  cnf(c_133,plain,
% 4.01/0.98      ( v1_lattice3(sK3) != iProver_top
% 4.01/0.98      | v2_struct_0(sK3) != iProver_top
% 4.01/0.98      | l1_orders_2(sK3) != iProver_top ),
% 4.01/0.98      inference(instantiation,[status(thm)],[c_131]) ).
% 4.01/0.98  
% 4.01/0.98  cnf(c_5232,plain,
% 4.01/0.98      ( m1_subset_1(X0,u1_struct_0(sK3)) != iProver_top
% 4.01/0.98      | r3_orders_2(sK3,sK4,X0) != iProver_top
% 4.01/0.98      | r1_orders_2(sK3,sK4,X0) = iProver_top ),
% 4.01/0.98      inference(global_propositional_subsumption,
% 4.01/0.98                [status(thm)],
% 4.01/0.98                [c_3874,c_41,c_44,c_46,c_133]) ).
% 4.01/0.98  
% 4.01/0.98  cnf(c_5233,plain,
% 4.01/0.98      ( r1_orders_2(sK3,sK4,X0) = iProver_top
% 4.01/0.98      | r3_orders_2(sK3,sK4,X0) != iProver_top
% 4.01/0.98      | m1_subset_1(X0,u1_struct_0(sK3)) != iProver_top ),
% 4.01/0.98      inference(renaming,[status(thm)],[c_5232]) ).
% 4.01/0.98  
% 4.01/0.98  cnf(c_5245,plain,
% 4.01/0.98      ( r1_orders_2(sK3,sK4,sK4) = iProver_top
% 4.01/0.98      | r3_orders_2(sK3,sK4,sK4) != iProver_top ),
% 4.01/0.98      inference(superposition,[status(thm)],[c_1166,c_5233]) ).
% 4.01/0.98  
% 4.01/0.98  cnf(c_47,plain,
% 4.01/0.98      ( m1_subset_1(sK4,u1_struct_0(sK3)) = iProver_top ),
% 4.01/0.98      inference(predicate_to_equality,[status(thm)],[c_34]) ).
% 4.01/0.98  
% 4.01/0.98  cnf(c_9,plain,
% 4.01/0.98      ( m1_subset_1(k1_yellow_0(X0,X1),u1_struct_0(X0))
% 4.01/0.98      | ~ l1_orders_2(X0) ),
% 4.01/0.98      inference(cnf_transformation,[],[f68]) ).
% 4.01/0.98  
% 4.01/0.98  cnf(c_116,plain,
% 4.01/0.98      ( m1_subset_1(k1_yellow_0(X0,X1),u1_struct_0(X0)) = iProver_top
% 4.01/0.98      | l1_orders_2(X0) != iProver_top ),
% 4.01/0.98      inference(predicate_to_equality,[status(thm)],[c_9]) ).
% 4.01/0.98  
% 4.01/0.98  cnf(c_118,plain,
% 4.01/0.98      ( m1_subset_1(k1_yellow_0(sK3,sK3),u1_struct_0(sK3)) = iProver_top
% 4.01/0.98      | l1_orders_2(sK3) != iProver_top ),
% 4.01/0.98      inference(instantiation,[status(thm)],[c_116]) ).
% 4.01/0.98  
% 4.01/0.98  cnf(c_3,plain,
% 4.01/0.98      ( r3_orders_2(X0,X1,X1)
% 4.01/0.98      | ~ m1_subset_1(X2,u1_struct_0(X0))
% 4.01/0.98      | ~ m1_subset_1(X1,u1_struct_0(X0))
% 4.01/0.98      | v2_struct_0(X0)
% 4.01/0.98      | ~ v3_orders_2(X0)
% 4.01/0.98      | ~ l1_orders_2(X0) ),
% 4.01/0.98      inference(cnf_transformation,[],[f62]) ).
% 4.01/0.98  
% 4.01/0.98  cnf(c_1808,plain,
% 4.01/0.98      ( r3_orders_2(sK3,sK4,sK4)
% 4.01/0.98      | ~ m1_subset_1(X0,u1_struct_0(sK3))
% 4.01/0.98      | ~ m1_subset_1(sK4,u1_struct_0(sK3))
% 4.01/0.98      | v2_struct_0(sK3)
% 4.01/0.98      | ~ v3_orders_2(sK3)
% 4.01/0.98      | ~ l1_orders_2(sK3) ),
% 4.01/0.98      inference(instantiation,[status(thm)],[c_3]) ).
% 4.01/0.98  
% 4.01/0.98  cnf(c_1970,plain,
% 4.01/0.98      ( r3_orders_2(sK3,sK4,sK4)
% 4.01/0.98      | ~ m1_subset_1(k1_yellow_0(sK3,X0),u1_struct_0(sK3))
% 4.01/0.98      | ~ m1_subset_1(sK4,u1_struct_0(sK3))
% 4.01/0.98      | v2_struct_0(sK3)
% 4.01/0.98      | ~ v3_orders_2(sK3)
% 4.01/0.98      | ~ l1_orders_2(sK3) ),
% 4.01/0.98      inference(instantiation,[status(thm)],[c_1808]) ).
% 4.01/0.98  
% 4.01/0.98  cnf(c_1972,plain,
% 4.01/0.98      ( r3_orders_2(sK3,sK4,sK4) = iProver_top
% 4.01/0.98      | m1_subset_1(k1_yellow_0(sK3,X0),u1_struct_0(sK3)) != iProver_top
% 4.01/0.98      | m1_subset_1(sK4,u1_struct_0(sK3)) != iProver_top
% 4.01/0.98      | v2_struct_0(sK3) = iProver_top
% 4.01/0.98      | v3_orders_2(sK3) != iProver_top
% 4.01/0.98      | l1_orders_2(sK3) != iProver_top ),
% 4.01/0.98      inference(predicate_to_equality,[status(thm)],[c_1970]) ).
% 4.01/0.98  
% 4.01/0.98  cnf(c_1974,plain,
% 4.01/0.98      ( r3_orders_2(sK3,sK4,sK4) = iProver_top
% 4.01/0.98      | m1_subset_1(k1_yellow_0(sK3,sK3),u1_struct_0(sK3)) != iProver_top
% 4.01/0.98      | m1_subset_1(sK4,u1_struct_0(sK3)) != iProver_top
% 4.01/0.98      | v2_struct_0(sK3) = iProver_top
% 4.01/0.98      | v3_orders_2(sK3) != iProver_top
% 4.01/0.98      | l1_orders_2(sK3) != iProver_top ),
% 4.01/0.98      inference(instantiation,[status(thm)],[c_1972]) ).
% 4.01/0.98  
% 4.01/0.98  cnf(c_2253,plain,
% 4.01/0.98      ( r1_orders_2(sK3,sK4,sK4)
% 4.01/0.98      | ~ r3_orders_2(sK3,sK4,sK4)
% 4.01/0.98      | ~ m1_subset_1(sK4,u1_struct_0(sK3))
% 4.01/0.98      | v2_struct_0(sK3)
% 4.01/0.98      | ~ v3_orders_2(sK3)
% 4.01/0.98      | ~ l1_orders_2(sK3) ),
% 4.01/0.98      inference(instantiation,[status(thm)],[c_2]) ).
% 4.01/0.98  
% 4.01/0.98  cnf(c_2254,plain,
% 4.01/0.98      ( r1_orders_2(sK3,sK4,sK4) = iProver_top
% 4.01/0.98      | r3_orders_2(sK3,sK4,sK4) != iProver_top
% 4.01/0.98      | m1_subset_1(sK4,u1_struct_0(sK3)) != iProver_top
% 4.01/0.98      | v2_struct_0(sK3) = iProver_top
% 4.01/0.98      | v3_orders_2(sK3) != iProver_top
% 4.01/0.98      | l1_orders_2(sK3) != iProver_top ),
% 4.01/0.98      inference(predicate_to_equality,[status(thm)],[c_2253]) ).
% 4.01/0.98  
% 4.01/0.98  cnf(c_5418,plain,
% 4.01/0.98      ( r1_orders_2(sK3,sK4,sK4) = iProver_top ),
% 4.01/0.98      inference(global_propositional_subsumption,
% 4.01/0.98                [status(thm)],
% 4.01/0.98                [c_5245,c_41,c_44,c_46,c_47,c_118,c_133,c_1974,c_2254]) ).
% 4.01/0.98  
% 4.01/0.98  cnf(c_22,plain,
% 4.01/0.98      ( ~ r1_orders_2(X0,X1,X2)
% 4.01/0.98      | r2_hidden(X1,k5_waybel_0(X0,X2))
% 4.01/0.98      | ~ m1_subset_1(X1,u1_struct_0(X0))
% 4.01/0.98      | ~ m1_subset_1(X2,u1_struct_0(X0))
% 4.01/0.98      | v2_struct_0(X0)
% 4.01/0.98      | ~ l1_orders_2(X0) ),
% 4.01/0.98      inference(cnf_transformation,[],[f82]) ).
% 4.01/0.98  
% 4.01/0.98  cnf(c_1178,plain,
% 4.01/0.98      ( r1_orders_2(X0,X1,X2) != iProver_top
% 4.01/0.98      | r2_hidden(X1,k5_waybel_0(X0,X2)) = iProver_top
% 4.01/0.98      | m1_subset_1(X1,u1_struct_0(X0)) != iProver_top
% 4.01/0.98      | m1_subset_1(X2,u1_struct_0(X0)) != iProver_top
% 4.01/0.98      | v2_struct_0(X0) = iProver_top
% 4.01/0.98      | l1_orders_2(X0) != iProver_top ),
% 4.01/0.98      inference(predicate_to_equality,[status(thm)],[c_22]) ).
% 4.01/0.98  
% 4.01/0.98  cnf(c_6,plain,
% 4.01/0.98      ( r2_lattice3(X0,X1,X2)
% 4.01/0.98      | r2_hidden(sK0(X0,X1,X2),X1)
% 4.01/0.98      | ~ m1_subset_1(X2,u1_struct_0(X0))
% 4.01/0.98      | ~ l1_orders_2(X0) ),
% 4.01/0.98      inference(cnf_transformation,[],[f66]) ).
% 4.01/0.98  
% 4.01/0.98  cnf(c_1192,plain,
% 4.01/0.98      ( r2_lattice3(X0,X1,X2) = iProver_top
% 4.01/0.98      | r2_hidden(sK0(X0,X1,X2),X1) = iProver_top
% 4.01/0.98      | m1_subset_1(X2,u1_struct_0(X0)) != iProver_top
% 4.01/0.98      | l1_orders_2(X0) != iProver_top ),
% 4.01/0.98      inference(predicate_to_equality,[status(thm)],[c_6]) ).
% 4.01/0.98  
% 4.01/0.98  cnf(c_23,plain,
% 4.01/0.98      ( r1_orders_2(X0,X1,X2)
% 4.01/0.98      | ~ r2_hidden(X1,k5_waybel_0(X0,X2))
% 4.01/0.98      | ~ m1_subset_1(X1,u1_struct_0(X0))
% 4.01/0.98      | ~ m1_subset_1(X2,u1_struct_0(X0))
% 4.01/0.98      | v2_struct_0(X0)
% 4.01/0.98      | ~ l1_orders_2(X0) ),
% 4.01/0.98      inference(cnf_transformation,[],[f81]) ).
% 4.01/0.98  
% 4.01/0.98  cnf(c_1177,plain,
% 4.01/0.98      ( r1_orders_2(X0,X1,X2) = iProver_top
% 4.01/0.98      | r2_hidden(X1,k5_waybel_0(X0,X2)) != iProver_top
% 4.01/0.98      | m1_subset_1(X1,u1_struct_0(X0)) != iProver_top
% 4.01/0.98      | m1_subset_1(X2,u1_struct_0(X0)) != iProver_top
% 4.01/0.98      | v2_struct_0(X0) = iProver_top
% 4.01/0.98      | l1_orders_2(X0) != iProver_top ),
% 4.01/0.98      inference(predicate_to_equality,[status(thm)],[c_23]) ).
% 4.01/0.98  
% 4.01/0.98  cnf(c_2892,plain,
% 4.01/0.98      ( r2_lattice3(X0,k5_waybel_0(X1,X2),X3) = iProver_top
% 4.01/0.98      | r1_orders_2(X1,sK0(X0,k5_waybel_0(X1,X2),X3),X2) = iProver_top
% 4.01/0.98      | m1_subset_1(X3,u1_struct_0(X0)) != iProver_top
% 4.01/0.98      | m1_subset_1(X2,u1_struct_0(X1)) != iProver_top
% 4.01/0.98      | m1_subset_1(sK0(X0,k5_waybel_0(X1,X2),X3),u1_struct_0(X1)) != iProver_top
% 4.01/0.98      | v2_struct_0(X1) = iProver_top
% 4.01/0.98      | l1_orders_2(X1) != iProver_top
% 4.01/0.98      | l1_orders_2(X0) != iProver_top ),
% 4.01/0.98      inference(superposition,[status(thm)],[c_1192,c_1177]) ).
% 4.01/0.98  
% 4.01/0.98  cnf(c_18,plain,
% 4.01/0.98      ( ~ m1_subset_1(X0,u1_struct_0(X1))
% 4.01/0.98      | m1_subset_1(k5_waybel_0(X1,X0),k1_zfmisc_1(u1_struct_0(X1)))
% 4.01/0.98      | v2_struct_0(X1)
% 4.01/0.98      | ~ l1_orders_2(X1) ),
% 4.01/0.98      inference(cnf_transformation,[],[f77]) ).
% 4.01/0.98  
% 4.01/0.98  cnf(c_1182,plain,
% 4.01/0.98      ( m1_subset_1(X0,u1_struct_0(X1)) != iProver_top
% 4.01/0.98      | m1_subset_1(k5_waybel_0(X1,X0),k1_zfmisc_1(u1_struct_0(X1))) = iProver_top
% 4.01/0.98      | v2_struct_0(X1) = iProver_top
% 4.01/0.98      | l1_orders_2(X1) != iProver_top ),
% 4.01/0.98      inference(predicate_to_equality,[status(thm)],[c_18]) ).
% 4.01/0.98  
% 4.01/0.98  cnf(c_0,plain,
% 4.01/0.98      ( ~ r2_hidden(X0,X1)
% 4.01/0.98      | m1_subset_1(X0,X2)
% 4.01/0.98      | ~ m1_subset_1(X1,k1_zfmisc_1(X2)) ),
% 4.01/0.98      inference(cnf_transformation,[],[f59]) ).
% 4.01/0.98  
% 4.01/0.98  cnf(c_1198,plain,
% 4.01/0.98      ( r2_hidden(X0,X1) != iProver_top
% 4.01/0.98      | m1_subset_1(X0,X2) = iProver_top
% 4.01/0.98      | m1_subset_1(X1,k1_zfmisc_1(X2)) != iProver_top ),
% 4.01/0.98      inference(predicate_to_equality,[status(thm)],[c_0]) ).
% 4.01/0.98  
% 4.01/0.98  cnf(c_2261,plain,
% 4.01/0.98      ( r2_hidden(X0,k5_waybel_0(X1,X2)) != iProver_top
% 4.01/0.98      | m1_subset_1(X2,u1_struct_0(X1)) != iProver_top
% 4.01/0.98      | m1_subset_1(X0,u1_struct_0(X1)) = iProver_top
% 4.01/0.98      | v2_struct_0(X1) = iProver_top
% 4.01/0.98      | l1_orders_2(X1) != iProver_top ),
% 4.01/0.98      inference(superposition,[status(thm)],[c_1182,c_1198]) ).
% 4.01/0.98  
% 4.01/0.98  cnf(c_4804,plain,
% 4.01/0.98      ( r2_lattice3(X0,k5_waybel_0(X1,X2),X3) = iProver_top
% 4.01/0.98      | m1_subset_1(X3,u1_struct_0(X0)) != iProver_top
% 4.01/0.98      | m1_subset_1(X2,u1_struct_0(X1)) != iProver_top
% 4.01/0.98      | m1_subset_1(sK0(X0,k5_waybel_0(X1,X2),X3),u1_struct_0(X1)) = iProver_top
% 4.01/0.98      | v2_struct_0(X1) = iProver_top
% 4.01/0.98      | l1_orders_2(X1) != iProver_top
% 4.01/0.98      | l1_orders_2(X0) != iProver_top ),
% 4.01/0.98      inference(superposition,[status(thm)],[c_1192,c_2261]) ).
% 4.01/0.98  
% 4.01/0.98  cnf(c_6338,plain,
% 4.01/0.98      ( m1_subset_1(X2,u1_struct_0(X1)) != iProver_top
% 4.01/0.98      | m1_subset_1(X3,u1_struct_0(X0)) != iProver_top
% 4.01/0.98      | r1_orders_2(X1,sK0(X0,k5_waybel_0(X1,X2),X3),X2) = iProver_top
% 4.01/0.98      | r2_lattice3(X0,k5_waybel_0(X1,X2),X3) = iProver_top
% 4.01/0.98      | v2_struct_0(X1) = iProver_top
% 4.01/0.98      | l1_orders_2(X1) != iProver_top
% 4.01/0.98      | l1_orders_2(X0) != iProver_top ),
% 4.01/0.98      inference(global_propositional_subsumption,
% 4.01/0.98                [status(thm)],
% 4.01/0.98                [c_2892,c_4804]) ).
% 4.01/0.98  
% 4.01/0.98  cnf(c_6339,plain,
% 4.01/0.98      ( r2_lattice3(X0,k5_waybel_0(X1,X2),X3) = iProver_top
% 4.01/0.98      | r1_orders_2(X1,sK0(X0,k5_waybel_0(X1,X2),X3),X2) = iProver_top
% 4.01/0.98      | m1_subset_1(X3,u1_struct_0(X0)) != iProver_top
% 4.01/0.98      | m1_subset_1(X2,u1_struct_0(X1)) != iProver_top
% 4.01/0.98      | v2_struct_0(X1) = iProver_top
% 4.01/0.98      | l1_orders_2(X1) != iProver_top
% 4.01/0.98      | l1_orders_2(X0) != iProver_top ),
% 4.01/0.98      inference(renaming,[status(thm)],[c_6338]) ).
% 4.01/0.98  
% 4.01/0.98  cnf(c_5,plain,
% 4.01/0.98      ( r2_lattice3(X0,X1,X2)
% 4.01/0.98      | ~ r1_orders_2(X0,sK0(X0,X1,X2),X2)
% 4.01/0.98      | ~ m1_subset_1(X2,u1_struct_0(X0))
% 4.01/0.98      | ~ l1_orders_2(X0) ),
% 4.01/0.98      inference(cnf_transformation,[],[f67]) ).
% 4.01/0.98  
% 4.01/0.98  cnf(c_1193,plain,
% 4.01/0.98      ( r2_lattice3(X0,X1,X2) = iProver_top
% 4.01/0.98      | r1_orders_2(X0,sK0(X0,X1,X2),X2) != iProver_top
% 4.01/0.98      | m1_subset_1(X2,u1_struct_0(X0)) != iProver_top
% 4.01/0.98      | l1_orders_2(X0) != iProver_top ),
% 4.01/0.98      inference(predicate_to_equality,[status(thm)],[c_5]) ).
% 4.01/0.98  
% 4.01/0.98  cnf(c_6351,plain,
% 4.01/0.98      ( r2_lattice3(X0,k5_waybel_0(X0,X1),X1) = iProver_top
% 4.01/0.98      | m1_subset_1(X1,u1_struct_0(X0)) != iProver_top
% 4.01/0.98      | v2_struct_0(X0) = iProver_top
% 4.01/0.98      | l1_orders_2(X0) != iProver_top ),
% 4.01/0.98      inference(superposition,[status(thm)],[c_6339,c_1193]) ).
% 4.01/0.98  
% 4.01/0.98  cnf(c_14,plain,
% 4.01/0.98      ( ~ r2_lattice3(X0,X1,X2)
% 4.01/0.98      | r2_lattice3(X0,X1,sK1(X0,X2,X1))
% 4.01/0.98      | ~ m1_subset_1(X2,u1_struct_0(X0))
% 4.01/0.98      | ~ v5_orders_2(X0)
% 4.01/0.98      | ~ l1_orders_2(X0)
% 4.01/0.98      | k1_yellow_0(X0,X1) = X2 ),
% 4.01/0.98      inference(cnf_transformation,[],[f72]) ).
% 4.01/0.98  
% 4.01/0.98  cnf(c_1184,plain,
% 4.01/0.98      ( k1_yellow_0(X0,X1) = X2
% 4.01/0.98      | r2_lattice3(X0,X1,X2) != iProver_top
% 4.01/0.98      | r2_lattice3(X0,X1,sK1(X0,X2,X1)) = iProver_top
% 4.01/0.98      | m1_subset_1(X2,u1_struct_0(X0)) != iProver_top
% 4.01/0.98      | v5_orders_2(X0) != iProver_top
% 4.01/0.98      | l1_orders_2(X0) != iProver_top ),
% 4.01/0.98      inference(predicate_to_equality,[status(thm)],[c_14]) ).
% 4.01/0.98  
% 4.01/0.98  cnf(c_15,plain,
% 4.01/0.98      ( ~ r2_lattice3(X0,X1,X2)
% 4.01/0.98      | ~ m1_subset_1(X2,u1_struct_0(X0))
% 4.01/0.98      | m1_subset_1(sK1(X0,X2,X1),u1_struct_0(X0))
% 4.01/0.98      | ~ v5_orders_2(X0)
% 4.01/0.98      | ~ l1_orders_2(X0)
% 4.01/0.98      | k1_yellow_0(X0,X1) = X2 ),
% 4.01/0.98      inference(cnf_transformation,[],[f71]) ).
% 4.01/0.98  
% 4.01/0.98  cnf(c_1183,plain,
% 4.01/0.98      ( k1_yellow_0(X0,X1) = X2
% 4.01/0.98      | r2_lattice3(X0,X1,X2) != iProver_top
% 4.01/0.98      | m1_subset_1(X2,u1_struct_0(X0)) != iProver_top
% 4.01/0.98      | m1_subset_1(sK1(X0,X2,X1),u1_struct_0(X0)) = iProver_top
% 4.01/0.98      | v5_orders_2(X0) != iProver_top
% 4.01/0.98      | l1_orders_2(X0) != iProver_top ),
% 4.01/0.98      inference(predicate_to_equality,[status(thm)],[c_15]) ).
% 4.01/0.98  
% 4.01/0.98  cnf(c_8,plain,
% 4.01/0.98      ( ~ r2_lattice3(X0,X1,X2)
% 4.01/0.98      | r1_orders_2(X0,X3,X2)
% 4.01/0.98      | ~ r2_hidden(X3,X1)
% 4.01/0.98      | ~ m1_subset_1(X2,u1_struct_0(X0))
% 4.01/0.98      | ~ m1_subset_1(X3,u1_struct_0(X0))
% 4.01/0.98      | ~ l1_orders_2(X0) ),
% 4.01/0.98      inference(cnf_transformation,[],[f64]) ).
% 4.01/0.98  
% 4.01/0.98  cnf(c_1190,plain,
% 4.01/0.98      ( r2_lattice3(X0,X1,X2) != iProver_top
% 4.01/0.98      | r1_orders_2(X0,X3,X2) = iProver_top
% 4.01/0.98      | r2_hidden(X3,X1) != iProver_top
% 4.01/0.98      | m1_subset_1(X2,u1_struct_0(X0)) != iProver_top
% 4.01/0.98      | m1_subset_1(X3,u1_struct_0(X0)) != iProver_top
% 4.01/0.98      | l1_orders_2(X0) != iProver_top ),
% 4.01/0.98      inference(predicate_to_equality,[status(thm)],[c_8]) ).
% 4.01/0.98  
% 4.01/0.98  cnf(c_3479,plain,
% 4.01/0.98      ( k1_yellow_0(X0,X1) = X2
% 4.01/0.98      | r2_lattice3(X0,X1,X2) != iProver_top
% 4.01/0.98      | r2_lattice3(X0,X3,sK1(X0,X2,X1)) != iProver_top
% 4.01/0.98      | r1_orders_2(X0,X4,sK1(X0,X2,X1)) = iProver_top
% 4.01/0.98      | r2_hidden(X4,X3) != iProver_top
% 4.01/0.98      | m1_subset_1(X2,u1_struct_0(X0)) != iProver_top
% 4.01/0.98      | m1_subset_1(X4,u1_struct_0(X0)) != iProver_top
% 4.01/0.98      | v5_orders_2(X0) != iProver_top
% 4.01/0.98      | l1_orders_2(X0) != iProver_top ),
% 4.01/0.98      inference(superposition,[status(thm)],[c_1183,c_1190]) ).
% 4.01/0.98  
% 4.01/0.98  cnf(c_8406,plain,
% 4.01/0.98      ( k1_yellow_0(X0,X1) = X2
% 4.01/0.98      | r2_lattice3(X0,X1,X2) != iProver_top
% 4.01/0.98      | r1_orders_2(X0,X3,sK1(X0,X2,X1)) = iProver_top
% 4.01/0.98      | r2_hidden(X3,X1) != iProver_top
% 4.01/0.98      | m1_subset_1(X2,u1_struct_0(X0)) != iProver_top
% 4.01/0.98      | m1_subset_1(X3,u1_struct_0(X0)) != iProver_top
% 4.01/0.98      | v5_orders_2(X0) != iProver_top
% 4.01/0.98      | l1_orders_2(X0) != iProver_top ),
% 4.01/0.98      inference(superposition,[status(thm)],[c_1184,c_3479]) ).
% 4.01/0.98  
% 4.01/0.98  cnf(c_13,plain,
% 4.01/0.98      ( ~ r2_lattice3(X0,X1,X2)
% 4.01/0.98      | ~ r1_orders_2(X0,X2,sK1(X0,X2,X1))
% 4.01/0.98      | ~ m1_subset_1(X2,u1_struct_0(X0))
% 4.01/0.98      | ~ v5_orders_2(X0)
% 4.01/0.98      | ~ l1_orders_2(X0)
% 4.01/0.98      | k1_yellow_0(X0,X1) = X2 ),
% 4.01/0.98      inference(cnf_transformation,[],[f73]) ).
% 4.01/0.98  
% 4.01/0.98  cnf(c_1185,plain,
% 4.01/0.98      ( k1_yellow_0(X0,X1) = X2
% 4.01/0.98      | r2_lattice3(X0,X1,X2) != iProver_top
% 4.01/0.98      | r1_orders_2(X0,X2,sK1(X0,X2,X1)) != iProver_top
% 4.01/0.98      | m1_subset_1(X2,u1_struct_0(X0)) != iProver_top
% 4.01/0.98      | v5_orders_2(X0) != iProver_top
% 4.01/0.98      | l1_orders_2(X0) != iProver_top ),
% 4.01/0.98      inference(predicate_to_equality,[status(thm)],[c_13]) ).
% 4.01/0.98  
% 4.01/0.98  cnf(c_8714,plain,
% 4.01/0.98      ( k1_yellow_0(X0,X1) = X2
% 4.01/0.98      | r2_lattice3(X0,X1,X2) != iProver_top
% 4.01/0.98      | r2_hidden(X2,X1) != iProver_top
% 4.01/0.98      | m1_subset_1(X2,u1_struct_0(X0)) != iProver_top
% 4.01/0.98      | v5_orders_2(X0) != iProver_top
% 4.01/0.98      | l1_orders_2(X0) != iProver_top ),
% 4.01/0.98      inference(superposition,[status(thm)],[c_8406,c_1185]) ).
% 4.01/0.98  
% 4.01/0.98  cnf(c_8970,plain,
% 4.01/0.98      ( k1_yellow_0(X0,k5_waybel_0(X0,X1)) = X1
% 4.01/0.98      | r2_hidden(X1,k5_waybel_0(X0,X1)) != iProver_top
% 4.01/0.98      | m1_subset_1(X1,u1_struct_0(X0)) != iProver_top
% 4.01/0.98      | v5_orders_2(X0) != iProver_top
% 4.01/0.98      | v2_struct_0(X0) = iProver_top
% 4.01/0.98      | l1_orders_2(X0) != iProver_top ),
% 4.01/0.98      inference(superposition,[status(thm)],[c_6351,c_8714]) ).
% 4.01/0.98  
% 4.01/0.98  cnf(c_14203,plain,
% 4.01/0.98      ( k1_yellow_0(X0,k5_waybel_0(X0,X1)) = X1
% 4.01/0.98      | r1_orders_2(X0,X1,X1) != iProver_top
% 4.01/0.98      | m1_subset_1(X1,u1_struct_0(X0)) != iProver_top
% 4.01/0.98      | v5_orders_2(X0) != iProver_top
% 4.01/0.98      | v2_struct_0(X0) = iProver_top
% 4.01/0.98      | l1_orders_2(X0) != iProver_top ),
% 4.01/0.98      inference(superposition,[status(thm)],[c_1178,c_8970]) ).
% 4.01/0.98  
% 4.01/0.98  cnf(c_14259,plain,
% 4.01/0.98      ( k1_yellow_0(sK3,k5_waybel_0(sK3,sK4)) = sK4
% 4.01/0.98      | m1_subset_1(sK4,u1_struct_0(sK3)) != iProver_top
% 4.01/0.98      | v5_orders_2(sK3) != iProver_top
% 4.01/0.98      | v2_struct_0(sK3) = iProver_top
% 4.01/0.98      | l1_orders_2(sK3) != iProver_top ),
% 4.01/0.98      inference(superposition,[status(thm)],[c_5418,c_14203]) ).
% 4.01/0.98  
% 4.01/0.98  cnf(c_38,negated_conjecture,
% 4.01/0.98      ( v5_orders_2(sK3) ),
% 4.01/0.98      inference(cnf_transformation,[],[f93]) ).
% 4.01/0.98  
% 4.01/0.98  cnf(c_43,plain,
% 4.01/0.98      ( v5_orders_2(sK3) = iProver_top ),
% 4.01/0.98      inference(predicate_to_equality,[status(thm)],[c_38]) ).
% 4.01/0.98  
% 4.01/0.98  cnf(c_14467,plain,
% 4.01/0.98      ( k1_yellow_0(sK3,k5_waybel_0(sK3,sK4)) = sK4 ),
% 4.01/0.98      inference(global_propositional_subsumption,
% 4.01/0.98                [status(thm)],
% 4.01/0.98                [c_14259,c_43,c_44,c_46,c_47,c_133]) ).
% 4.01/0.98  
% 4.01/0.98  cnf(c_24,plain,
% 4.01/0.98      ( ~ v1_waybel_7(X0,X1)
% 4.01/0.98      | v4_waybel_7(k1_yellow_0(X1,X0),X1)
% 4.01/0.98      | ~ v1_waybel_0(X0,X1)
% 4.01/0.98      | ~ v12_waybel_0(X0,X1)
% 4.01/0.98      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 4.01/0.98      | ~ m1_subset_1(k1_yellow_0(X1,X0),u1_struct_0(X1))
% 4.01/0.98      | ~ v2_lattice3(X1)
% 4.01/0.98      | v1_xboole_0(X0)
% 4.01/0.98      | ~ v4_orders_2(X1)
% 4.01/0.98      | ~ v5_orders_2(X1)
% 4.01/0.98      | ~ v1_lattice3(X1)
% 4.01/0.98      | ~ v3_orders_2(X1)
% 4.01/0.98      | ~ l1_orders_2(X1) ),
% 4.01/0.98      inference(cnf_transformation,[],[f102]) ).
% 4.01/0.98  
% 4.01/0.98  cnf(c_1176,plain,
% 4.01/0.98      ( v1_waybel_7(X0,X1) != iProver_top
% 4.01/0.98      | v4_waybel_7(k1_yellow_0(X1,X0),X1) = iProver_top
% 4.01/0.98      | v1_waybel_0(X0,X1) != iProver_top
% 4.01/0.98      | v12_waybel_0(X0,X1) != iProver_top
% 4.01/0.98      | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1))) != iProver_top
% 4.01/0.98      | m1_subset_1(k1_yellow_0(X1,X0),u1_struct_0(X1)) != iProver_top
% 4.01/0.98      | v2_lattice3(X1) != iProver_top
% 4.01/0.98      | v1_xboole_0(X0) = iProver_top
% 4.01/0.98      | v4_orders_2(X1) != iProver_top
% 4.01/0.98      | v5_orders_2(X1) != iProver_top
% 4.01/0.98      | v1_lattice3(X1) != iProver_top
% 4.01/0.98      | v3_orders_2(X1) != iProver_top
% 4.01/0.98      | l1_orders_2(X1) != iProver_top ),
% 4.01/0.98      inference(predicate_to_equality,[status(thm)],[c_24]) ).
% 4.01/0.98  
% 4.01/0.98  cnf(c_1189,plain,
% 4.01/0.98      ( m1_subset_1(k1_yellow_0(X0,X1),u1_struct_0(X0)) = iProver_top
% 4.01/0.98      | l1_orders_2(X0) != iProver_top ),
% 4.01/0.98      inference(predicate_to_equality,[status(thm)],[c_9]) ).
% 4.01/0.98  
% 4.01/0.98  cnf(c_1602,plain,
% 4.01/0.98      ( v1_waybel_7(X0,X1) != iProver_top
% 4.01/0.98      | v4_waybel_7(k1_yellow_0(X1,X0),X1) = iProver_top
% 4.01/0.98      | v1_waybel_0(X0,X1) != iProver_top
% 4.01/0.98      | v12_waybel_0(X0,X1) != iProver_top
% 4.01/0.98      | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1))) != iProver_top
% 4.01/0.98      | v2_lattice3(X1) != iProver_top
% 4.01/0.98      | v1_xboole_0(X0) = iProver_top
% 4.01/0.98      | v4_orders_2(X1) != iProver_top
% 4.01/0.98      | v5_orders_2(X1) != iProver_top
% 4.01/0.98      | v1_lattice3(X1) != iProver_top
% 4.01/0.98      | v3_orders_2(X1) != iProver_top
% 4.01/0.98      | l1_orders_2(X1) != iProver_top ),
% 4.01/0.98      inference(forward_subsumption_resolution,
% 4.01/0.98                [status(thm)],
% 4.01/0.98                [c_1176,c_1189]) ).
% 4.01/0.98  
% 4.01/0.98  cnf(c_4575,plain,
% 4.01/0.98      ( v1_waybel_7(k5_waybel_0(X0,X1),X0) != iProver_top
% 4.01/0.98      | v4_waybel_7(k1_yellow_0(X0,k5_waybel_0(X0,X1)),X0) = iProver_top
% 4.01/0.98      | v1_waybel_0(k5_waybel_0(X0,X1),X0) != iProver_top
% 4.01/0.98      | v12_waybel_0(k5_waybel_0(X0,X1),X0) != iProver_top
% 4.01/0.98      | m1_subset_1(X1,u1_struct_0(X0)) != iProver_top
% 4.01/0.98      | v2_lattice3(X0) != iProver_top
% 4.01/0.98      | v1_xboole_0(k5_waybel_0(X0,X1)) = iProver_top
% 4.01/0.98      | v4_orders_2(X0) != iProver_top
% 4.01/0.98      | v5_orders_2(X0) != iProver_top
% 4.01/0.98      | v1_lattice3(X0) != iProver_top
% 4.01/0.98      | v2_struct_0(X0) = iProver_top
% 4.01/0.98      | v3_orders_2(X0) != iProver_top
% 4.01/0.98      | l1_orders_2(X0) != iProver_top ),
% 4.01/0.98      inference(superposition,[status(thm)],[c_1182,c_1602]) ).
% 4.01/0.98  
% 4.01/0.98  cnf(c_20,plain,
% 4.01/0.98      ( v1_waybel_0(k5_waybel_0(X0,X1),X0)
% 4.01/0.98      | ~ m1_subset_1(X1,u1_struct_0(X0))
% 4.01/0.98      | v2_struct_0(X0)
% 4.01/0.98      | ~ v3_orders_2(X0)
% 4.01/0.98      | ~ l1_orders_2(X0) ),
% 4.01/0.98      inference(cnf_transformation,[],[f80]) ).
% 4.01/0.98  
% 4.01/0.98  cnf(c_83,plain,
% 4.01/0.98      ( v1_waybel_0(k5_waybel_0(X0,X1),X0) = iProver_top
% 4.01/0.98      | m1_subset_1(X1,u1_struct_0(X0)) != iProver_top
% 4.01/0.98      | v2_struct_0(X0) = iProver_top
% 4.01/0.98      | v3_orders_2(X0) != iProver_top
% 4.01/0.98      | l1_orders_2(X0) != iProver_top ),
% 4.01/0.98      inference(predicate_to_equality,[status(thm)],[c_20]) ).
% 4.01/0.98  
% 4.01/0.98  cnf(c_19,plain,
% 4.01/0.98      ( v12_waybel_0(k5_waybel_0(X0,X1),X0)
% 4.01/0.98      | ~ m1_subset_1(X1,u1_struct_0(X0))
% 4.01/0.98      | ~ v4_orders_2(X0)
% 4.01/0.98      | v2_struct_0(X0)
% 4.01/0.98      | ~ l1_orders_2(X0) ),
% 4.01/0.98      inference(cnf_transformation,[],[f78]) ).
% 4.01/0.98  
% 4.01/0.98  cnf(c_86,plain,
% 4.01/0.98      ( v12_waybel_0(k5_waybel_0(X0,X1),X0) = iProver_top
% 4.01/0.98      | m1_subset_1(X1,u1_struct_0(X0)) != iProver_top
% 4.01/0.98      | v4_orders_2(X0) != iProver_top
% 4.01/0.98      | v2_struct_0(X0) = iProver_top
% 4.01/0.98      | l1_orders_2(X0) != iProver_top ),
% 4.01/0.98      inference(predicate_to_equality,[status(thm)],[c_19]) ).
% 4.01/0.98  
% 4.01/0.98  cnf(c_10681,plain,
% 4.01/0.98      ( v1_lattice3(X0) != iProver_top
% 4.01/0.98      | v5_orders_2(X0) != iProver_top
% 4.01/0.98      | v4_orders_2(X0) != iProver_top
% 4.01/0.98      | v1_xboole_0(k5_waybel_0(X0,X1)) = iProver_top
% 4.01/0.98      | v2_lattice3(X0) != iProver_top
% 4.01/0.98      | m1_subset_1(X1,u1_struct_0(X0)) != iProver_top
% 4.01/0.98      | v4_waybel_7(k1_yellow_0(X0,k5_waybel_0(X0,X1)),X0) = iProver_top
% 4.01/0.98      | v1_waybel_7(k5_waybel_0(X0,X1),X0) != iProver_top
% 4.01/0.98      | v3_orders_2(X0) != iProver_top
% 4.01/0.98      | l1_orders_2(X0) != iProver_top ),
% 4.01/0.98      inference(global_propositional_subsumption,
% 4.01/0.98                [status(thm)],
% 4.01/0.98                [c_4575,c_83,c_86,c_131]) ).
% 4.01/0.98  
% 4.01/0.98  cnf(c_10682,plain,
% 4.01/0.98      ( v1_waybel_7(k5_waybel_0(X0,X1),X0) != iProver_top
% 4.01/0.98      | v4_waybel_7(k1_yellow_0(X0,k5_waybel_0(X0,X1)),X0) = iProver_top
% 4.01/0.98      | m1_subset_1(X1,u1_struct_0(X0)) != iProver_top
% 4.01/0.98      | v2_lattice3(X0) != iProver_top
% 4.01/0.98      | v1_xboole_0(k5_waybel_0(X0,X1)) = iProver_top
% 4.01/0.98      | v4_orders_2(X0) != iProver_top
% 4.01/0.98      | v5_orders_2(X0) != iProver_top
% 4.01/0.98      | v1_lattice3(X0) != iProver_top
% 4.01/0.98      | v3_orders_2(X0) != iProver_top
% 4.01/0.98      | l1_orders_2(X0) != iProver_top ),
% 4.01/0.98      inference(renaming,[status(thm)],[c_10681]) ).
% 4.01/0.98  
% 4.01/0.98  cnf(c_14491,plain,
% 4.01/0.98      ( v1_waybel_7(k5_waybel_0(sK3,sK4),sK3) != iProver_top
% 4.01/0.98      | v4_waybel_7(sK4,sK3) = iProver_top
% 4.01/0.98      | m1_subset_1(sK4,u1_struct_0(sK3)) != iProver_top
% 4.01/0.98      | v2_lattice3(sK3) != iProver_top
% 4.01/0.98      | v1_xboole_0(k5_waybel_0(sK3,sK4)) = iProver_top
% 4.01/0.98      | v4_orders_2(sK3) != iProver_top
% 4.01/0.98      | v5_orders_2(sK3) != iProver_top
% 4.01/0.98      | v1_lattice3(sK3) != iProver_top
% 4.01/0.98      | v3_orders_2(sK3) != iProver_top
% 4.01/0.98      | l1_orders_2(sK3) != iProver_top ),
% 4.01/0.98      inference(superposition,[status(thm)],[c_14467,c_10682]) ).
% 4.01/0.98  
% 4.01/0.98  cnf(c_21,plain,
% 4.01/0.98      ( ~ m1_subset_1(X0,u1_struct_0(X1))
% 4.01/0.98      | ~ v1_xboole_0(k5_waybel_0(X1,X0))
% 4.01/0.98      | v2_struct_0(X1)
% 4.01/0.98      | ~ v3_orders_2(X1)
% 4.01/0.98      | ~ l1_orders_2(X1) ),
% 4.01/0.98      inference(cnf_transformation,[],[f79]) ).
% 4.01/0.98  
% 4.01/0.98  cnf(c_1179,plain,
% 4.01/0.98      ( m1_subset_1(X0,u1_struct_0(X1)) != iProver_top
% 4.01/0.98      | v1_xboole_0(k5_waybel_0(X1,X0)) != iProver_top
% 4.01/0.98      | v2_struct_0(X1) = iProver_top
% 4.01/0.98      | v3_orders_2(X1) != iProver_top
% 4.01/0.98      | l1_orders_2(X1) != iProver_top ),
% 4.01/0.98      inference(predicate_to_equality,[status(thm)],[c_21]) ).
% 4.01/0.98  
% 4.01/0.98  cnf(c_2426,plain,
% 4.01/0.98      ( v1_xboole_0(k5_waybel_0(sK3,sK4)) != iProver_top
% 4.01/0.98      | v2_struct_0(sK3) = iProver_top
% 4.01/0.98      | v3_orders_2(sK3) != iProver_top
% 4.01/0.98      | l1_orders_2(sK3) != iProver_top ),
% 4.01/0.98      inference(superposition,[status(thm)],[c_1166,c_1179]) ).
% 4.01/0.98  
% 4.01/0.98  cnf(c_31,plain,
% 4.01/0.98      ( ~ v5_waybel_6(X0,X1)
% 4.01/0.98      | v1_waybel_7(k5_waybel_0(X1,X0),X1)
% 4.01/0.98      | ~ m1_subset_1(X0,u1_struct_0(X1))
% 4.01/0.98      | ~ v2_lattice3(X1)
% 4.01/0.98      | ~ v4_orders_2(X1)
% 4.01/0.98      | ~ v5_orders_2(X1)
% 4.01/0.98      | ~ v1_lattice3(X1)
% 4.01/0.98      | ~ v3_orders_2(X1)
% 4.01/0.98      | ~ l1_orders_2(X1) ),
% 4.01/0.98      inference(cnf_transformation,[],[f90]) ).
% 4.01/0.98  
% 4.01/0.98  cnf(c_1892,plain,
% 4.01/0.98      ( ~ v5_waybel_6(sK4,sK3)
% 4.01/0.98      | v1_waybel_7(k5_waybel_0(sK3,sK4),sK3)
% 4.01/0.98      | ~ m1_subset_1(sK4,u1_struct_0(sK3))
% 4.01/0.98      | ~ v2_lattice3(sK3)
% 4.01/0.98      | ~ v4_orders_2(sK3)
% 4.01/0.98      | ~ v5_orders_2(sK3)
% 4.01/0.98      | ~ v1_lattice3(sK3)
% 4.01/0.98      | ~ v3_orders_2(sK3)
% 4.01/0.98      | ~ l1_orders_2(sK3) ),
% 4.01/0.98      inference(instantiation,[status(thm)],[c_31]) ).
% 4.01/0.98  
% 4.01/0.98  cnf(c_1893,plain,
% 4.01/0.98      ( v5_waybel_6(sK4,sK3) != iProver_top
% 4.01/0.98      | v1_waybel_7(k5_waybel_0(sK3,sK4),sK3) = iProver_top
% 4.01/0.98      | m1_subset_1(sK4,u1_struct_0(sK3)) != iProver_top
% 4.01/0.98      | v2_lattice3(sK3) != iProver_top
% 4.01/0.98      | v4_orders_2(sK3) != iProver_top
% 4.01/0.98      | v5_orders_2(sK3) != iProver_top
% 4.01/0.98      | v1_lattice3(sK3) != iProver_top
% 4.01/0.98      | v3_orders_2(sK3) != iProver_top
% 4.01/0.98      | l1_orders_2(sK3) != iProver_top ),
% 4.01/0.98      inference(predicate_to_equality,[status(thm)],[c_1892]) ).
% 4.01/0.98  
% 4.01/0.98  cnf(c_32,negated_conjecture,
% 4.01/0.98      ( ~ v4_waybel_7(sK4,sK3) ),
% 4.01/0.98      inference(cnf_transformation,[],[f99]) ).
% 4.01/0.98  
% 4.01/0.98  cnf(c_49,plain,
% 4.01/0.98      ( v4_waybel_7(sK4,sK3) != iProver_top ),
% 4.01/0.98      inference(predicate_to_equality,[status(thm)],[c_32]) ).
% 4.01/0.98  
% 4.01/0.98  cnf(c_33,negated_conjecture,
% 4.01/0.98      ( v5_waybel_6(sK4,sK3) ),
% 4.01/0.98      inference(cnf_transformation,[],[f98]) ).
% 4.01/0.98  
% 4.01/0.98  cnf(c_48,plain,
% 4.01/0.98      ( v5_waybel_6(sK4,sK3) = iProver_top ),
% 4.01/0.98      inference(predicate_to_equality,[status(thm)],[c_33]) ).
% 4.01/0.98  
% 4.01/0.98  cnf(c_36,negated_conjecture,
% 4.01/0.98      ( v2_lattice3(sK3) ),
% 4.01/0.98      inference(cnf_transformation,[],[f95]) ).
% 4.01/0.98  
% 4.01/0.98  cnf(c_45,plain,
% 4.01/0.98      ( v2_lattice3(sK3) = iProver_top ),
% 4.01/0.98      inference(predicate_to_equality,[status(thm)],[c_36]) ).
% 4.01/0.98  
% 4.01/0.98  cnf(c_39,negated_conjecture,
% 4.01/0.98      ( v4_orders_2(sK3) ),
% 4.01/0.98      inference(cnf_transformation,[],[f92]) ).
% 4.01/0.98  
% 4.01/0.98  cnf(c_42,plain,
% 4.01/0.98      ( v4_orders_2(sK3) = iProver_top ),
% 4.01/0.98      inference(predicate_to_equality,[status(thm)],[c_39]) ).
% 4.01/0.98  
% 4.01/0.98  cnf(contradiction,plain,
% 4.01/0.98      ( $false ),
% 4.01/0.98      inference(minisat,
% 4.01/0.98                [status(thm)],
% 4.01/0.98                [c_14491,c_2426,c_1893,c_133,c_49,c_48,c_47,c_46,c_45,
% 4.01/0.98                 c_44,c_43,c_42,c_41]) ).
% 4.01/0.98  
% 4.01/0.98  
% 4.01/0.98  % SZS output end CNFRefutation for theBenchmark.p
% 4.01/0.98  
% 4.01/0.98  ------                               Statistics
% 4.01/0.98  
% 4.01/0.98  ------ Selected
% 4.01/0.98  
% 4.01/0.98  total_time:                             0.443
% 4.01/0.98  
%------------------------------------------------------------------------------
