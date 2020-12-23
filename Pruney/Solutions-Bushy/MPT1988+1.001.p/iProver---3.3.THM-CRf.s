%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT1988+1.001 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n029.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:46:59 EST 2020

% Result     : Theorem 1.74s
% Output     : CNFRefutation 1.74s
% Verified   : 
% Statistics : Number of formulae       :  198 (1608 expanded)
%              Number of clauses        :  129 ( 373 expanded)
%              Number of leaves         :   17 ( 393 expanded)
%              Depth                    :   18
%              Number of atoms          : 1141 (10647 expanded)
%              Number of equality atoms :   40 (  67 expanded)
%              Maximal formula depth    :   14 (   7 average)
%              Maximal clause size      :   21 (   5 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f8,axiom,(
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

fof(f27,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( r2_hidden(X2,k5_waybel_0(X0,X1))
              <=> r1_orders_2(X0,X2,X1) )
              | ~ m1_subset_1(X2,u1_struct_0(X0)) )
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l1_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f28,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( r2_hidden(X2,k5_waybel_0(X0,X1))
              <=> r1_orders_2(X0,X2,X1) )
              | ~ m1_subset_1(X2,u1_struct_0(X0)) )
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l1_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f27])).

fof(f43,plain,(
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
    inference(nnf_transformation,[],[f28])).

fof(f66,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(X2,k5_waybel_0(X0,X1))
      | ~ r1_orders_2(X0,X2,X1)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f43])).

fof(f1,axiom,(
    ! [X0] :
      ( l1_orders_2(X0)
     => ( v2_lattice3(X0)
       => ~ v2_struct_0(X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f13,plain,(
    ! [X0] :
      ( ~ v2_struct_0(X0)
      | ~ v2_lattice3(X0)
      | ~ l1_orders_2(X0) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f14,plain,(
    ! [X0] :
      ( ~ v2_struct_0(X0)
      | ~ v2_lattice3(X0)
      | ~ l1_orders_2(X0) ) ),
    inference(flattening,[],[f13])).

fof(f47,plain,(
    ! [X0] :
      ( ~ v2_struct_0(X0)
      | ~ v2_lattice3(X0)
      | ~ l1_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f14])).

fof(f10,conjecture,(
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

fof(f11,negated_conjecture,(
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
             => v1_waybel_7(k5_waybel_0(X0,X1),X0) ) ) ) ),
    inference(negated_conjecture,[],[f10])).

fof(f12,plain,(
    ~ ! [X0] :
        ( ( l1_orders_2(X0)
          & v2_lattice3(X0)
          & v5_orders_2(X0)
          & v4_orders_2(X0)
          & v3_orders_2(X0) )
       => ! [X1] :
            ( m1_subset_1(X1,u1_struct_0(X0))
           => ( v5_waybel_6(X1,X0)
             => v1_waybel_7(k5_waybel_0(X0,X1),X0) ) ) ) ),
    inference(pure_predicate_removal,[],[f11])).

fof(f31,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ~ v1_waybel_7(k5_waybel_0(X0,X1),X0)
          & v5_waybel_6(X1,X0)
          & m1_subset_1(X1,u1_struct_0(X0)) )
      & l1_orders_2(X0)
      & v2_lattice3(X0)
      & v5_orders_2(X0)
      & v4_orders_2(X0)
      & v3_orders_2(X0) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f32,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ~ v1_waybel_7(k5_waybel_0(X0,X1),X0)
          & v5_waybel_6(X1,X0)
          & m1_subset_1(X1,u1_struct_0(X0)) )
      & l1_orders_2(X0)
      & v2_lattice3(X0)
      & v5_orders_2(X0)
      & v4_orders_2(X0)
      & v3_orders_2(X0) ) ),
    inference(flattening,[],[f31])).

fof(f45,plain,(
    ! [X0] :
      ( ? [X1] :
          ( ~ v1_waybel_7(k5_waybel_0(X0,X1),X0)
          & v5_waybel_6(X1,X0)
          & m1_subset_1(X1,u1_struct_0(X0)) )
     => ( ~ v1_waybel_7(k5_waybel_0(X0,sK5),X0)
        & v5_waybel_6(sK5,X0)
        & m1_subset_1(sK5,u1_struct_0(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f44,plain,
    ( ? [X0] :
        ( ? [X1] :
            ( ~ v1_waybel_7(k5_waybel_0(X0,X1),X0)
            & v5_waybel_6(X1,X0)
            & m1_subset_1(X1,u1_struct_0(X0)) )
        & l1_orders_2(X0)
        & v2_lattice3(X0)
        & v5_orders_2(X0)
        & v4_orders_2(X0)
        & v3_orders_2(X0) )
   => ( ? [X1] :
          ( ~ v1_waybel_7(k5_waybel_0(sK4,X1),sK4)
          & v5_waybel_6(X1,sK4)
          & m1_subset_1(X1,u1_struct_0(sK4)) )
      & l1_orders_2(sK4)
      & v2_lattice3(sK4)
      & v5_orders_2(sK4)
      & v4_orders_2(sK4)
      & v3_orders_2(sK4) ) ),
    introduced(choice_axiom,[])).

fof(f46,plain,
    ( ~ v1_waybel_7(k5_waybel_0(sK4,sK5),sK4)
    & v5_waybel_6(sK5,sK4)
    & m1_subset_1(sK5,u1_struct_0(sK4))
    & l1_orders_2(sK4)
    & v2_lattice3(sK4)
    & v5_orders_2(sK4)
    & v4_orders_2(sK4)
    & v3_orders_2(sK4) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4,sK5])],[f32,f45,f44])).

fof(f71,plain,(
    v2_lattice3(sK4) ),
    inference(cnf_transformation,[],[f46])).

fof(f72,plain,(
    l1_orders_2(sK4) ),
    inference(cnf_transformation,[],[f46])).

fof(f3,axiom,(
    ! [X0] :
      ( ( l1_orders_2(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,u1_struct_0(X0))
         => ( v5_waybel_6(X1,X0)
          <=> ! [X2] :
                ( m1_subset_1(X2,u1_struct_0(X0))
               => ! [X3] :
                    ( m1_subset_1(X3,u1_struct_0(X0))
                   => ~ ( ~ r1_orders_2(X0,X3,X1)
                        & ~ r1_orders_2(X0,X2,X1)
                        & r1_orders_2(X0,k11_lattice3(X0,X2,X3),X1) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f17,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( v5_waybel_6(X1,X0)
          <=> ! [X2] :
                ( ! [X3] :
                    ( r1_orders_2(X0,X3,X1)
                    | r1_orders_2(X0,X2,X1)
                    | ~ r1_orders_2(X0,k11_lattice3(X0,X2,X3),X1)
                    | ~ m1_subset_1(X3,u1_struct_0(X0)) )
                | ~ m1_subset_1(X2,u1_struct_0(X0)) ) )
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l1_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f18,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( v5_waybel_6(X1,X0)
          <=> ! [X2] :
                ( ! [X3] :
                    ( r1_orders_2(X0,X3,X1)
                    | r1_orders_2(X0,X2,X1)
                    | ~ r1_orders_2(X0,k11_lattice3(X0,X2,X3),X1)
                    | ~ m1_subset_1(X3,u1_struct_0(X0)) )
                | ~ m1_subset_1(X2,u1_struct_0(X0)) ) )
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l1_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f17])).

fof(f38,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ( v5_waybel_6(X1,X0)
              | ? [X2] :
                  ( ? [X3] :
                      ( ~ r1_orders_2(X0,X3,X1)
                      & ~ r1_orders_2(X0,X2,X1)
                      & r1_orders_2(X0,k11_lattice3(X0,X2,X3),X1)
                      & m1_subset_1(X3,u1_struct_0(X0)) )
                  & m1_subset_1(X2,u1_struct_0(X0)) ) )
            & ( ! [X2] :
                  ( ! [X3] :
                      ( r1_orders_2(X0,X3,X1)
                      | r1_orders_2(X0,X2,X1)
                      | ~ r1_orders_2(X0,k11_lattice3(X0,X2,X3),X1)
                      | ~ m1_subset_1(X3,u1_struct_0(X0)) )
                  | ~ m1_subset_1(X2,u1_struct_0(X0)) )
              | ~ v5_waybel_6(X1,X0) ) )
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l1_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(nnf_transformation,[],[f18])).

fof(f39,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ( v5_waybel_6(X1,X0)
              | ? [X2] :
                  ( ? [X3] :
                      ( ~ r1_orders_2(X0,X3,X1)
                      & ~ r1_orders_2(X0,X2,X1)
                      & r1_orders_2(X0,k11_lattice3(X0,X2,X3),X1)
                      & m1_subset_1(X3,u1_struct_0(X0)) )
                  & m1_subset_1(X2,u1_struct_0(X0)) ) )
            & ( ! [X4] :
                  ( ! [X5] :
                      ( r1_orders_2(X0,X5,X1)
                      | r1_orders_2(X0,X4,X1)
                      | ~ r1_orders_2(X0,k11_lattice3(X0,X4,X5),X1)
                      | ~ m1_subset_1(X5,u1_struct_0(X0)) )
                  | ~ m1_subset_1(X4,u1_struct_0(X0)) )
              | ~ v5_waybel_6(X1,X0) ) )
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l1_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(rectify,[],[f38])).

fof(f41,plain,(
    ! [X2,X1,X0] :
      ( ? [X3] :
          ( ~ r1_orders_2(X0,X3,X1)
          & ~ r1_orders_2(X0,X2,X1)
          & r1_orders_2(X0,k11_lattice3(X0,X2,X3),X1)
          & m1_subset_1(X3,u1_struct_0(X0)) )
     => ( ~ r1_orders_2(X0,sK3(X0,X1),X1)
        & ~ r1_orders_2(X0,X2,X1)
        & r1_orders_2(X0,k11_lattice3(X0,X2,sK3(X0,X1)),X1)
        & m1_subset_1(sK3(X0,X1),u1_struct_0(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f40,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ? [X3] :
              ( ~ r1_orders_2(X0,X3,X1)
              & ~ r1_orders_2(X0,X2,X1)
              & r1_orders_2(X0,k11_lattice3(X0,X2,X3),X1)
              & m1_subset_1(X3,u1_struct_0(X0)) )
          & m1_subset_1(X2,u1_struct_0(X0)) )
     => ( ? [X3] :
            ( ~ r1_orders_2(X0,X3,X1)
            & ~ r1_orders_2(X0,sK2(X0,X1),X1)
            & r1_orders_2(X0,k11_lattice3(X0,sK2(X0,X1),X3),X1)
            & m1_subset_1(X3,u1_struct_0(X0)) )
        & m1_subset_1(sK2(X0,X1),u1_struct_0(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f42,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ( v5_waybel_6(X1,X0)
              | ( ~ r1_orders_2(X0,sK3(X0,X1),X1)
                & ~ r1_orders_2(X0,sK2(X0,X1),X1)
                & r1_orders_2(X0,k11_lattice3(X0,sK2(X0,X1),sK3(X0,X1)),X1)
                & m1_subset_1(sK3(X0,X1),u1_struct_0(X0))
                & m1_subset_1(sK2(X0,X1),u1_struct_0(X0)) ) )
            & ( ! [X4] :
                  ( ! [X5] :
                      ( r1_orders_2(X0,X5,X1)
                      | r1_orders_2(X0,X4,X1)
                      | ~ r1_orders_2(X0,k11_lattice3(X0,X4,X5),X1)
                      | ~ m1_subset_1(X5,u1_struct_0(X0)) )
                  | ~ m1_subset_1(X4,u1_struct_0(X0)) )
              | ~ v5_waybel_6(X1,X0) ) )
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l1_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2,sK3])],[f39,f41,f40])).

fof(f54,plain,(
    ! [X4,X0,X5,X1] :
      ( r1_orders_2(X0,X5,X1)
      | r1_orders_2(X0,X4,X1)
      | ~ r1_orders_2(X0,k11_lattice3(X0,X4,X5),X1)
      | ~ m1_subset_1(X5,u1_struct_0(X0))
      | ~ m1_subset_1(X4,u1_struct_0(X0))
      | ~ v5_waybel_6(X1,X0)
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f42])).

fof(f7,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,u1_struct_0(X0))
        & m1_subset_1(X1,u1_struct_0(X0))
        & l1_orders_2(X0)
        & v2_lattice3(X0)
        & v5_orders_2(X0) )
     => k12_lattice3(X0,X1,X2) = k11_lattice3(X0,X1,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f25,plain,(
    ! [X0,X1,X2] :
      ( k12_lattice3(X0,X1,X2) = k11_lattice3(X0,X1,X2)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | ~ v2_lattice3(X0)
      | ~ v5_orders_2(X0) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f26,plain,(
    ! [X0,X1,X2] :
      ( k12_lattice3(X0,X1,X2) = k11_lattice3(X0,X1,X2)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | ~ v2_lattice3(X0)
      | ~ v5_orders_2(X0) ) ),
    inference(flattening,[],[f25])).

fof(f64,plain,(
    ! [X2,X0,X1] :
      ( k12_lattice3(X0,X1,X2) = k11_lattice3(X0,X1,X2)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | ~ v2_lattice3(X0)
      | ~ v5_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f70,plain,(
    v5_orders_2(sK4) ),
    inference(cnf_transformation,[],[f46])).

fof(f9,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(X2))
        & r2_hidden(X0,X1) )
     => m1_subset_1(X0,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f29,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X0,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f30,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X0,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(flattening,[],[f29])).

fof(f67,plain,(
    ! [X2,X0,X1] :
      ( m1_subset_1(X0,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f65,plain,(
    ! [X2,X0,X1] :
      ( r1_orders_2(X0,X2,X1)
      | ~ r2_hidden(X2,k5_waybel_0(X0,X1))
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f43])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,u1_struct_0(X0))
        & l1_orders_2(X0)
        & ~ v2_struct_0(X0) )
     => m1_subset_1(k5_waybel_0(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f19,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k5_waybel_0(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f20,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k5_waybel_0(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f19])).

fof(f60,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k5_waybel_0(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f5,axiom,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,u1_struct_0(X0))
        & l1_orders_2(X0)
        & v4_orders_2(X0)
        & ~ v2_struct_0(X0) )
     => v12_waybel_0(k5_waybel_0(X0,X1),X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f21,plain,(
    ! [X0,X1] :
      ( v12_waybel_0(k5_waybel_0(X0,X1),X0)
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | ~ v4_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f22,plain,(
    ! [X0,X1] :
      ( v12_waybel_0(k5_waybel_0(X0,X1),X0)
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | ~ v4_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f21])).

fof(f61,plain,(
    ! [X0,X1] :
      ( v12_waybel_0(k5_waybel_0(X0,X1),X0)
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | ~ v4_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f69,plain,(
    v4_orders_2(sK4) ),
    inference(cnf_transformation,[],[f46])).

fof(f2,axiom,(
    ! [X0] :
      ( ( l1_orders_2(X0)
        & v2_lattice3(X0)
        & v5_orders_2(X0)
        & v4_orders_2(X0)
        & v3_orders_2(X0) )
     => ! [X1] :
          ( ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
            & v12_waybel_0(X1,X0)
            & v1_waybel_0(X1,X0)
            & ~ v1_xboole_0(X1) )
         => ( v1_waybel_7(X1,X0)
          <=> ! [X2] :
                ( m1_subset_1(X2,u1_struct_0(X0))
               => ! [X3] :
                    ( m1_subset_1(X3,u1_struct_0(X0))
                   => ~ ( ~ r2_hidden(X3,X1)
                        & ~ r2_hidden(X2,X1)
                        & r2_hidden(k12_lattice3(X0,X2,X3),X1) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f15,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( v1_waybel_7(X1,X0)
          <=> ! [X2] :
                ( ! [X3] :
                    ( r2_hidden(X3,X1)
                    | r2_hidden(X2,X1)
                    | ~ r2_hidden(k12_lattice3(X0,X2,X3),X1)
                    | ~ m1_subset_1(X3,u1_struct_0(X0)) )
                | ~ m1_subset_1(X2,u1_struct_0(X0)) ) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
          | ~ v12_waybel_0(X1,X0)
          | ~ v1_waybel_0(X1,X0)
          | v1_xboole_0(X1) )
      | ~ l1_orders_2(X0)
      | ~ v2_lattice3(X0)
      | ~ v5_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v3_orders_2(X0) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f16,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( v1_waybel_7(X1,X0)
          <=> ! [X2] :
                ( ! [X3] :
                    ( r2_hidden(X3,X1)
                    | r2_hidden(X2,X1)
                    | ~ r2_hidden(k12_lattice3(X0,X2,X3),X1)
                    | ~ m1_subset_1(X3,u1_struct_0(X0)) )
                | ~ m1_subset_1(X2,u1_struct_0(X0)) ) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
          | ~ v12_waybel_0(X1,X0)
          | ~ v1_waybel_0(X1,X0)
          | v1_xboole_0(X1) )
      | ~ l1_orders_2(X0)
      | ~ v2_lattice3(X0)
      | ~ v5_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v3_orders_2(X0) ) ),
    inference(flattening,[],[f15])).

fof(f33,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ( v1_waybel_7(X1,X0)
              | ? [X2] :
                  ( ? [X3] :
                      ( ~ r2_hidden(X3,X1)
                      & ~ r2_hidden(X2,X1)
                      & r2_hidden(k12_lattice3(X0,X2,X3),X1)
                      & m1_subset_1(X3,u1_struct_0(X0)) )
                  & m1_subset_1(X2,u1_struct_0(X0)) ) )
            & ( ! [X2] :
                  ( ! [X3] :
                      ( r2_hidden(X3,X1)
                      | r2_hidden(X2,X1)
                      | ~ r2_hidden(k12_lattice3(X0,X2,X3),X1)
                      | ~ m1_subset_1(X3,u1_struct_0(X0)) )
                  | ~ m1_subset_1(X2,u1_struct_0(X0)) )
              | ~ v1_waybel_7(X1,X0) ) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
          | ~ v12_waybel_0(X1,X0)
          | ~ v1_waybel_0(X1,X0)
          | v1_xboole_0(X1) )
      | ~ l1_orders_2(X0)
      | ~ v2_lattice3(X0)
      | ~ v5_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v3_orders_2(X0) ) ),
    inference(nnf_transformation,[],[f16])).

fof(f34,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ( v1_waybel_7(X1,X0)
              | ? [X2] :
                  ( ? [X3] :
                      ( ~ r2_hidden(X3,X1)
                      & ~ r2_hidden(X2,X1)
                      & r2_hidden(k12_lattice3(X0,X2,X3),X1)
                      & m1_subset_1(X3,u1_struct_0(X0)) )
                  & m1_subset_1(X2,u1_struct_0(X0)) ) )
            & ( ! [X4] :
                  ( ! [X5] :
                      ( r2_hidden(X5,X1)
                      | r2_hidden(X4,X1)
                      | ~ r2_hidden(k12_lattice3(X0,X4,X5),X1)
                      | ~ m1_subset_1(X5,u1_struct_0(X0)) )
                  | ~ m1_subset_1(X4,u1_struct_0(X0)) )
              | ~ v1_waybel_7(X1,X0) ) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
          | ~ v12_waybel_0(X1,X0)
          | ~ v1_waybel_0(X1,X0)
          | v1_xboole_0(X1) )
      | ~ l1_orders_2(X0)
      | ~ v2_lattice3(X0)
      | ~ v5_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v3_orders_2(X0) ) ),
    inference(rectify,[],[f33])).

fof(f36,plain,(
    ! [X2,X1,X0] :
      ( ? [X3] :
          ( ~ r2_hidden(X3,X1)
          & ~ r2_hidden(X2,X1)
          & r2_hidden(k12_lattice3(X0,X2,X3),X1)
          & m1_subset_1(X3,u1_struct_0(X0)) )
     => ( ~ r2_hidden(sK1(X0,X1),X1)
        & ~ r2_hidden(X2,X1)
        & r2_hidden(k12_lattice3(X0,X2,sK1(X0,X1)),X1)
        & m1_subset_1(sK1(X0,X1),u1_struct_0(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f35,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ? [X3] :
              ( ~ r2_hidden(X3,X1)
              & ~ r2_hidden(X2,X1)
              & r2_hidden(k12_lattice3(X0,X2,X3),X1)
              & m1_subset_1(X3,u1_struct_0(X0)) )
          & m1_subset_1(X2,u1_struct_0(X0)) )
     => ( ? [X3] :
            ( ~ r2_hidden(X3,X1)
            & ~ r2_hidden(sK0(X0,X1),X1)
            & r2_hidden(k12_lattice3(X0,sK0(X0,X1),X3),X1)
            & m1_subset_1(X3,u1_struct_0(X0)) )
        & m1_subset_1(sK0(X0,X1),u1_struct_0(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f37,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ( v1_waybel_7(X1,X0)
              | ( ~ r2_hidden(sK1(X0,X1),X1)
                & ~ r2_hidden(sK0(X0,X1),X1)
                & r2_hidden(k12_lattice3(X0,sK0(X0,X1),sK1(X0,X1)),X1)
                & m1_subset_1(sK1(X0,X1),u1_struct_0(X0))
                & m1_subset_1(sK0(X0,X1),u1_struct_0(X0)) ) )
            & ( ! [X4] :
                  ( ! [X5] :
                      ( r2_hidden(X5,X1)
                      | r2_hidden(X4,X1)
                      | ~ r2_hidden(k12_lattice3(X0,X4,X5),X1)
                      | ~ m1_subset_1(X5,u1_struct_0(X0)) )
                  | ~ m1_subset_1(X4,u1_struct_0(X0)) )
              | ~ v1_waybel_7(X1,X0) ) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
          | ~ v12_waybel_0(X1,X0)
          | ~ v1_waybel_0(X1,X0)
          | v1_xboole_0(X1) )
      | ~ l1_orders_2(X0)
      | ~ v2_lattice3(X0)
      | ~ v5_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v3_orders_2(X0) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f34,f36,f35])).

fof(f50,plain,(
    ! [X0,X1] :
      ( v1_waybel_7(X1,X0)
      | m1_subset_1(sK1(X0,X1),u1_struct_0(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ v12_waybel_0(X1,X0)
      | ~ v1_waybel_0(X1,X0)
      | v1_xboole_0(X1)
      | ~ l1_orders_2(X0)
      | ~ v2_lattice3(X0)
      | ~ v5_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v3_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f37])).

fof(f68,plain,(
    v3_orders_2(sK4) ),
    inference(cnf_transformation,[],[f46])).

fof(f6,axiom,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,u1_struct_0(X0))
        & l1_orders_2(X0)
        & v3_orders_2(X0)
        & ~ v2_struct_0(X0) )
     => ( v1_waybel_0(k5_waybel_0(X0,X1),X0)
        & ~ v1_xboole_0(k5_waybel_0(X0,X1)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f23,plain,(
    ! [X0,X1] :
      ( ( v1_waybel_0(k5_waybel_0(X0,X1),X0)
        & ~ v1_xboole_0(k5_waybel_0(X0,X1)) )
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f24,plain,(
    ! [X0,X1] :
      ( ( v1_waybel_0(k5_waybel_0(X0,X1),X0)
        & ~ v1_xboole_0(k5_waybel_0(X0,X1)) )
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f23])).

fof(f63,plain,(
    ! [X0,X1] :
      ( v1_waybel_0(k5_waybel_0(X0,X1),X0)
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f62,plain,(
    ! [X0,X1] :
      ( ~ v1_xboole_0(k5_waybel_0(X0,X1))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f49,plain,(
    ! [X0,X1] :
      ( v1_waybel_7(X1,X0)
      | m1_subset_1(sK0(X0,X1),u1_struct_0(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ v12_waybel_0(X1,X0)
      | ~ v1_waybel_0(X1,X0)
      | v1_xboole_0(X1)
      | ~ l1_orders_2(X0)
      | ~ v2_lattice3(X0)
      | ~ v5_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v3_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f37])).

fof(f52,plain,(
    ! [X0,X1] :
      ( v1_waybel_7(X1,X0)
      | ~ r2_hidden(sK0(X0,X1),X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ v12_waybel_0(X1,X0)
      | ~ v1_waybel_0(X1,X0)
      | v1_xboole_0(X1)
      | ~ l1_orders_2(X0)
      | ~ v2_lattice3(X0)
      | ~ v5_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v3_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f37])).

fof(f51,plain,(
    ! [X0,X1] :
      ( v1_waybel_7(X1,X0)
      | r2_hidden(k12_lattice3(X0,sK0(X0,X1),sK1(X0,X1)),X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ v12_waybel_0(X1,X0)
      | ~ v1_waybel_0(X1,X0)
      | v1_xboole_0(X1)
      | ~ l1_orders_2(X0)
      | ~ v2_lattice3(X0)
      | ~ v5_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v3_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f37])).

fof(f53,plain,(
    ! [X0,X1] :
      ( v1_waybel_7(X1,X0)
      | ~ r2_hidden(sK1(X0,X1),X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ v12_waybel_0(X1,X0)
      | ~ v1_waybel_0(X1,X0)
      | v1_xboole_0(X1)
      | ~ l1_orders_2(X0)
      | ~ v2_lattice3(X0)
      | ~ v5_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v3_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f37])).

fof(f75,plain,(
    ~ v1_waybel_7(k5_waybel_0(sK4,sK5),sK4) ),
    inference(cnf_transformation,[],[f46])).

fof(f74,plain,(
    v5_waybel_6(sK5,sK4) ),
    inference(cnf_transformation,[],[f46])).

fof(f73,plain,(
    m1_subset_1(sK5,u1_struct_0(sK4)) ),
    inference(cnf_transformation,[],[f46])).

cnf(c_18,plain,
    ( ~ r1_orders_2(X0,X1,X2)
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | ~ m1_subset_1(X1,u1_struct_0(X0))
    | r2_hidden(X1,k5_waybel_0(X0,X2))
    | ~ l1_orders_2(X0)
    | v2_struct_0(X0) ),
    inference(cnf_transformation,[],[f66])).

cnf(c_0,plain,
    ( ~ l1_orders_2(X0)
    | ~ v2_lattice3(X0)
    | ~ v2_struct_0(X0) ),
    inference(cnf_transformation,[],[f47])).

cnf(c_25,negated_conjecture,
    ( v2_lattice3(sK4) ),
    inference(cnf_transformation,[],[f71])).

cnf(c_608,plain,
    ( ~ l1_orders_2(X0)
    | ~ v2_struct_0(X0)
    | sK4 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_0,c_25])).

cnf(c_609,plain,
    ( ~ l1_orders_2(sK4)
    | ~ v2_struct_0(sK4) ),
    inference(unflattening,[status(thm)],[c_608])).

cnf(c_24,negated_conjecture,
    ( l1_orders_2(sK4) ),
    inference(cnf_transformation,[],[f72])).

cnf(c_98,plain,
    ( ~ l1_orders_2(sK4)
    | ~ v2_lattice3(sK4)
    | ~ v2_struct_0(sK4) ),
    inference(instantiation,[status(thm)],[c_0])).

cnf(c_611,plain,
    ( ~ v2_struct_0(sK4) ),
    inference(global_propositional_subsumption,[status(thm)],[c_609,c_25,c_24,c_98])).

cnf(c_877,plain,
    ( ~ r1_orders_2(X0,X1,X2)
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | ~ m1_subset_1(X1,u1_struct_0(X0))
    | r2_hidden(X1,k5_waybel_0(X0,X2))
    | ~ l1_orders_2(X0)
    | sK4 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_18,c_611])).

cnf(c_878,plain,
    ( ~ r1_orders_2(sK4,X0,X1)
    | ~ m1_subset_1(X0,u1_struct_0(sK4))
    | ~ m1_subset_1(X1,u1_struct_0(sK4))
    | r2_hidden(X0,k5_waybel_0(sK4,X1))
    | ~ l1_orders_2(sK4) ),
    inference(unflattening,[status(thm)],[c_877])).

cnf(c_882,plain,
    ( r2_hidden(X0,k5_waybel_0(sK4,X1))
    | ~ m1_subset_1(X1,u1_struct_0(sK4))
    | ~ m1_subset_1(X0,u1_struct_0(sK4))
    | ~ r1_orders_2(sK4,X0,X1) ),
    inference(global_propositional_subsumption,[status(thm)],[c_878,c_24])).

cnf(c_883,plain,
    ( ~ r1_orders_2(sK4,X0,X1)
    | ~ m1_subset_1(X1,u1_struct_0(sK4))
    | ~ m1_subset_1(X0,u1_struct_0(sK4))
    | r2_hidden(X0,k5_waybel_0(sK4,X1)) ),
    inference(renaming,[status(thm)],[c_882])).

cnf(c_2183,plain,
    ( ~ r1_orders_2(sK4,X0_53,X1_53)
    | ~ m1_subset_1(X0_53,u1_struct_0(sK4))
    | ~ m1_subset_1(X1_53,u1_struct_0(sK4))
    | r2_hidden(X0_53,k5_waybel_0(sK4,X1_53)) ),
    inference(subtyping,[status(esa)],[c_883])).

cnf(c_3520,plain,
    ( ~ r1_orders_2(sK4,sK1(sK4,k5_waybel_0(sK4,X0_53)),X0_53)
    | ~ m1_subset_1(X0_53,u1_struct_0(sK4))
    | ~ m1_subset_1(sK1(sK4,k5_waybel_0(sK4,X0_53)),u1_struct_0(sK4))
    | r2_hidden(sK1(sK4,k5_waybel_0(sK4,X0_53)),k5_waybel_0(sK4,X0_53)) ),
    inference(instantiation,[status(thm)],[c_2183])).

cnf(c_3522,plain,
    ( ~ r1_orders_2(sK4,sK1(sK4,k5_waybel_0(sK4,sK5)),sK5)
    | ~ m1_subset_1(sK1(sK4,k5_waybel_0(sK4,sK5)),u1_struct_0(sK4))
    | ~ m1_subset_1(sK5,u1_struct_0(sK4))
    | r2_hidden(sK1(sK4,k5_waybel_0(sK4,sK5)),k5_waybel_0(sK4,sK5)) ),
    inference(instantiation,[status(thm)],[c_3520])).

cnf(c_3415,plain,
    ( ~ r1_orders_2(sK4,sK0(sK4,k5_waybel_0(sK4,X0_53)),X0_53)
    | ~ m1_subset_1(X0_53,u1_struct_0(sK4))
    | ~ m1_subset_1(sK0(sK4,k5_waybel_0(sK4,X0_53)),u1_struct_0(sK4))
    | r2_hidden(sK0(sK4,k5_waybel_0(sK4,X0_53)),k5_waybel_0(sK4,X0_53)) ),
    inference(instantiation,[status(thm)],[c_2183])).

cnf(c_3417,plain,
    ( ~ r1_orders_2(sK4,sK0(sK4,k5_waybel_0(sK4,sK5)),sK5)
    | ~ m1_subset_1(sK0(sK4,k5_waybel_0(sK4,sK5)),u1_struct_0(sK4))
    | ~ m1_subset_1(sK5,u1_struct_0(sK4))
    | r2_hidden(sK0(sK4,k5_waybel_0(sK4,sK5)),k5_waybel_0(sK4,sK5)) ),
    inference(instantiation,[status(thm)],[c_3415])).

cnf(c_12,plain,
    ( r1_orders_2(X0,X1,X2)
    | r1_orders_2(X0,X3,X2)
    | ~ r1_orders_2(X0,k11_lattice3(X0,X1,X3),X2)
    | ~ v5_waybel_6(X2,X0)
    | ~ m1_subset_1(X3,u1_struct_0(X0))
    | ~ m1_subset_1(X1,u1_struct_0(X0))
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | ~ l1_orders_2(X0)
    | v2_struct_0(X0) ),
    inference(cnf_transformation,[],[f54])).

cnf(c_901,plain,
    ( r1_orders_2(X0,X1,X2)
    | r1_orders_2(X0,X3,X2)
    | ~ r1_orders_2(X0,k11_lattice3(X0,X1,X3),X2)
    | ~ v5_waybel_6(X2,X0)
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | ~ m1_subset_1(X3,u1_struct_0(X0))
    | ~ m1_subset_1(X1,u1_struct_0(X0))
    | ~ l1_orders_2(X0)
    | sK4 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_12,c_611])).

cnf(c_902,plain,
    ( r1_orders_2(sK4,X0,X1)
    | r1_orders_2(sK4,X2,X1)
    | ~ r1_orders_2(sK4,k11_lattice3(sK4,X0,X2),X1)
    | ~ v5_waybel_6(X1,sK4)
    | ~ m1_subset_1(X0,u1_struct_0(sK4))
    | ~ m1_subset_1(X2,u1_struct_0(sK4))
    | ~ m1_subset_1(X1,u1_struct_0(sK4))
    | ~ l1_orders_2(sK4) ),
    inference(unflattening,[status(thm)],[c_901])).

cnf(c_906,plain,
    ( ~ m1_subset_1(X1,u1_struct_0(sK4))
    | ~ m1_subset_1(X2,u1_struct_0(sK4))
    | ~ m1_subset_1(X0,u1_struct_0(sK4))
    | ~ v5_waybel_6(X1,sK4)
    | ~ r1_orders_2(sK4,k11_lattice3(sK4,X0,X2),X1)
    | r1_orders_2(sK4,X2,X1)
    | r1_orders_2(sK4,X0,X1) ),
    inference(global_propositional_subsumption,[status(thm)],[c_902,c_24])).

cnf(c_907,plain,
    ( r1_orders_2(sK4,X0,X1)
    | r1_orders_2(sK4,X2,X1)
    | ~ r1_orders_2(sK4,k11_lattice3(sK4,X0,X2),X1)
    | ~ v5_waybel_6(X1,sK4)
    | ~ m1_subset_1(X1,u1_struct_0(sK4))
    | ~ m1_subset_1(X0,u1_struct_0(sK4))
    | ~ m1_subset_1(X2,u1_struct_0(sK4)) ),
    inference(renaming,[status(thm)],[c_906])).

cnf(c_2182,plain,
    ( r1_orders_2(sK4,X0_53,X1_53)
    | r1_orders_2(sK4,X2_53,X1_53)
    | ~ r1_orders_2(sK4,k11_lattice3(sK4,X0_53,X2_53),X1_53)
    | ~ v5_waybel_6(X1_53,sK4)
    | ~ m1_subset_1(X0_53,u1_struct_0(sK4))
    | ~ m1_subset_1(X1_53,u1_struct_0(sK4))
    | ~ m1_subset_1(X2_53,u1_struct_0(sK4)) ),
    inference(subtyping,[status(esa)],[c_907])).

cnf(c_3124,plain,
    ( ~ r1_orders_2(sK4,k11_lattice3(sK4,sK0(sK4,k5_waybel_0(sK4,X0_53)),sK1(sK4,k5_waybel_0(sK4,X0_53))),X0_53)
    | r1_orders_2(sK4,sK0(sK4,k5_waybel_0(sK4,X0_53)),X0_53)
    | r1_orders_2(sK4,sK1(sK4,k5_waybel_0(sK4,X0_53)),X0_53)
    | ~ v5_waybel_6(X0_53,sK4)
    | ~ m1_subset_1(X0_53,u1_struct_0(sK4))
    | ~ m1_subset_1(sK0(sK4,k5_waybel_0(sK4,X0_53)),u1_struct_0(sK4))
    | ~ m1_subset_1(sK1(sK4,k5_waybel_0(sK4,X0_53)),u1_struct_0(sK4)) ),
    inference(instantiation,[status(thm)],[c_2182])).

cnf(c_3126,plain,
    ( ~ r1_orders_2(sK4,k11_lattice3(sK4,sK0(sK4,k5_waybel_0(sK4,sK5)),sK1(sK4,k5_waybel_0(sK4,sK5))),sK5)
    | r1_orders_2(sK4,sK0(sK4,k5_waybel_0(sK4,sK5)),sK5)
    | r1_orders_2(sK4,sK1(sK4,k5_waybel_0(sK4,sK5)),sK5)
    | ~ v5_waybel_6(sK5,sK4)
    | ~ m1_subset_1(sK0(sK4,k5_waybel_0(sK4,sK5)),u1_struct_0(sK4))
    | ~ m1_subset_1(sK1(sK4,k5_waybel_0(sK4,sK5)),u1_struct_0(sK4))
    | ~ m1_subset_1(sK5,u1_struct_0(sK4)) ),
    inference(instantiation,[status(thm)],[c_3124])).

cnf(c_2200,plain,
    ( ~ r1_orders_2(X0_55,X0_53,X1_53)
    | r1_orders_2(X0_55,X2_53,X1_53)
    | X2_53 != X0_53 ),
    theory(equality)).

cnf(c_2832,plain,
    ( r1_orders_2(sK4,X0_53,X1_53)
    | ~ r1_orders_2(sK4,k12_lattice3(sK4,sK0(sK4,k5_waybel_0(sK4,X1_53)),sK1(sK4,k5_waybel_0(sK4,X1_53))),X1_53)
    | X0_53 != k12_lattice3(sK4,sK0(sK4,k5_waybel_0(sK4,X1_53)),sK1(sK4,k5_waybel_0(sK4,X1_53))) ),
    inference(instantiation,[status(thm)],[c_2200])).

cnf(c_3047,plain,
    ( r1_orders_2(sK4,k11_lattice3(sK4,sK0(sK4,k5_waybel_0(sK4,X0_53)),sK1(sK4,k5_waybel_0(sK4,X0_53))),X0_53)
    | ~ r1_orders_2(sK4,k12_lattice3(sK4,sK0(sK4,k5_waybel_0(sK4,X0_53)),sK1(sK4,k5_waybel_0(sK4,X0_53))),X0_53)
    | k11_lattice3(sK4,sK0(sK4,k5_waybel_0(sK4,X0_53)),sK1(sK4,k5_waybel_0(sK4,X0_53))) != k12_lattice3(sK4,sK0(sK4,k5_waybel_0(sK4,X0_53)),sK1(sK4,k5_waybel_0(sK4,X0_53))) ),
    inference(instantiation,[status(thm)],[c_2832])).

cnf(c_3049,plain,
    ( r1_orders_2(sK4,k11_lattice3(sK4,sK0(sK4,k5_waybel_0(sK4,sK5)),sK1(sK4,k5_waybel_0(sK4,sK5))),sK5)
    | ~ r1_orders_2(sK4,k12_lattice3(sK4,sK0(sK4,k5_waybel_0(sK4,sK5)),sK1(sK4,k5_waybel_0(sK4,sK5))),sK5)
    | k11_lattice3(sK4,sK0(sK4,k5_waybel_0(sK4,sK5)),sK1(sK4,k5_waybel_0(sK4,sK5))) != k12_lattice3(sK4,sK0(sK4,k5_waybel_0(sK4,sK5)),sK1(sK4,k5_waybel_0(sK4,sK5))) ),
    inference(instantiation,[status(thm)],[c_3047])).

cnf(c_17,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(X1))
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ v5_orders_2(X1)
    | ~ l1_orders_2(X1)
    | ~ v2_lattice3(X1)
    | k11_lattice3(X1,X0,X2) = k12_lattice3(X1,X0,X2) ),
    inference(cnf_transformation,[],[f64])).

cnf(c_26,negated_conjecture,
    ( v5_orders_2(sK4) ),
    inference(cnf_transformation,[],[f70])).

cnf(c_583,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(X1))
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ l1_orders_2(X1)
    | ~ v2_lattice3(X1)
    | k11_lattice3(X1,X2,X0) = k12_lattice3(X1,X2,X0)
    | sK4 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_17,c_26])).

cnf(c_584,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(sK4))
    | ~ m1_subset_1(X1,u1_struct_0(sK4))
    | ~ l1_orders_2(sK4)
    | ~ v2_lattice3(sK4)
    | k11_lattice3(sK4,X1,X0) = k12_lattice3(sK4,X1,X0) ),
    inference(unflattening,[status(thm)],[c_583])).

cnf(c_588,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(sK4))
    | ~ m1_subset_1(X1,u1_struct_0(sK4))
    | k11_lattice3(sK4,X1,X0) = k12_lattice3(sK4,X1,X0) ),
    inference(global_propositional_subsumption,[status(thm)],[c_584,c_25,c_24])).

cnf(c_589,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(sK4))
    | ~ m1_subset_1(X1,u1_struct_0(sK4))
    | k11_lattice3(sK4,X0,X1) = k12_lattice3(sK4,X0,X1) ),
    inference(renaming,[status(thm)],[c_588])).

cnf(c_2185,plain,
    ( ~ m1_subset_1(X0_53,u1_struct_0(sK4))
    | ~ m1_subset_1(X1_53,u1_struct_0(sK4))
    | k11_lattice3(sK4,X0_53,X1_53) = k12_lattice3(sK4,X0_53,X1_53) ),
    inference(subtyping,[status(esa)],[c_589])).

cnf(c_2925,plain,
    ( ~ m1_subset_1(sK0(sK4,k5_waybel_0(sK4,X0_53)),u1_struct_0(sK4))
    | ~ m1_subset_1(sK1(sK4,k5_waybel_0(sK4,X0_53)),u1_struct_0(sK4))
    | k11_lattice3(sK4,sK0(sK4,k5_waybel_0(sK4,X0_53)),sK1(sK4,k5_waybel_0(sK4,X0_53))) = k12_lattice3(sK4,sK0(sK4,k5_waybel_0(sK4,X0_53)),sK1(sK4,k5_waybel_0(sK4,X0_53))) ),
    inference(instantiation,[status(thm)],[c_2185])).

cnf(c_2931,plain,
    ( ~ m1_subset_1(sK0(sK4,k5_waybel_0(sK4,sK5)),u1_struct_0(sK4))
    | ~ m1_subset_1(sK1(sK4,k5_waybel_0(sK4,sK5)),u1_struct_0(sK4))
    | k11_lattice3(sK4,sK0(sK4,k5_waybel_0(sK4,sK5)),sK1(sK4,k5_waybel_0(sK4,sK5))) = k12_lattice3(sK4,sK0(sK4,k5_waybel_0(sK4,sK5)),sK1(sK4,k5_waybel_0(sK4,sK5))) ),
    inference(instantiation,[status(thm)],[c_2925])).

cnf(c_20,plain,
    ( m1_subset_1(X0,X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(X1))
    | ~ r2_hidden(X0,X2) ),
    inference(cnf_transformation,[],[f67])).

cnf(c_2189,plain,
    ( m1_subset_1(X0_53,X0_54)
    | ~ m1_subset_1(X1_53,k1_zfmisc_1(X0_54))
    | ~ r2_hidden(X0_53,X1_53) ),
    inference(subtyping,[status(esa)],[c_20])).

cnf(c_2784,plain,
    ( m1_subset_1(k12_lattice3(sK4,sK0(sK4,k5_waybel_0(sK4,X0_53)),sK1(sK4,k5_waybel_0(sK4,X0_53))),X0_54)
    | ~ m1_subset_1(k5_waybel_0(sK4,X0_53),k1_zfmisc_1(X0_54))
    | ~ r2_hidden(k12_lattice3(sK4,sK0(sK4,k5_waybel_0(sK4,X0_53)),sK1(sK4,k5_waybel_0(sK4,X0_53))),k5_waybel_0(sK4,X0_53)) ),
    inference(instantiation,[status(thm)],[c_2189])).

cnf(c_2873,plain,
    ( m1_subset_1(k12_lattice3(sK4,sK0(sK4,k5_waybel_0(sK4,X0_53)),sK1(sK4,k5_waybel_0(sK4,X0_53))),u1_struct_0(sK4))
    | ~ m1_subset_1(k5_waybel_0(sK4,X0_53),k1_zfmisc_1(u1_struct_0(sK4)))
    | ~ r2_hidden(k12_lattice3(sK4,sK0(sK4,k5_waybel_0(sK4,X0_53)),sK1(sK4,k5_waybel_0(sK4,X0_53))),k5_waybel_0(sK4,X0_53)) ),
    inference(instantiation,[status(thm)],[c_2784])).

cnf(c_2875,plain,
    ( m1_subset_1(k12_lattice3(sK4,sK0(sK4,k5_waybel_0(sK4,sK5)),sK1(sK4,k5_waybel_0(sK4,sK5))),u1_struct_0(sK4))
    | ~ m1_subset_1(k5_waybel_0(sK4,sK5),k1_zfmisc_1(u1_struct_0(sK4)))
    | ~ r2_hidden(k12_lattice3(sK4,sK0(sK4,k5_waybel_0(sK4,sK5)),sK1(sK4,k5_waybel_0(sK4,sK5))),k5_waybel_0(sK4,sK5)) ),
    inference(instantiation,[status(thm)],[c_2873])).

cnf(c_19,plain,
    ( r1_orders_2(X0,X1,X2)
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | ~ m1_subset_1(X1,u1_struct_0(X0))
    | ~ r2_hidden(X1,k5_waybel_0(X0,X2))
    | ~ l1_orders_2(X0)
    | v2_struct_0(X0) ),
    inference(cnf_transformation,[],[f65])).

cnf(c_853,plain,
    ( r1_orders_2(X0,X1,X2)
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | ~ m1_subset_1(X1,u1_struct_0(X0))
    | ~ r2_hidden(X1,k5_waybel_0(X0,X2))
    | ~ l1_orders_2(X0)
    | sK4 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_19,c_611])).

cnf(c_854,plain,
    ( r1_orders_2(sK4,X0,X1)
    | ~ m1_subset_1(X0,u1_struct_0(sK4))
    | ~ m1_subset_1(X1,u1_struct_0(sK4))
    | ~ r2_hidden(X0,k5_waybel_0(sK4,X1))
    | ~ l1_orders_2(sK4) ),
    inference(unflattening,[status(thm)],[c_853])).

cnf(c_858,plain,
    ( ~ r2_hidden(X0,k5_waybel_0(sK4,X1))
    | ~ m1_subset_1(X1,u1_struct_0(sK4))
    | ~ m1_subset_1(X0,u1_struct_0(sK4))
    | r1_orders_2(sK4,X0,X1) ),
    inference(global_propositional_subsumption,[status(thm)],[c_854,c_24])).

cnf(c_859,plain,
    ( r1_orders_2(sK4,X0,X1)
    | ~ m1_subset_1(X1,u1_struct_0(sK4))
    | ~ m1_subset_1(X0,u1_struct_0(sK4))
    | ~ r2_hidden(X0,k5_waybel_0(sK4,X1)) ),
    inference(renaming,[status(thm)],[c_858])).

cnf(c_2184,plain,
    ( r1_orders_2(sK4,X0_53,X1_53)
    | ~ m1_subset_1(X0_53,u1_struct_0(sK4))
    | ~ m1_subset_1(X1_53,u1_struct_0(sK4))
    | ~ r2_hidden(X0_53,k5_waybel_0(sK4,X1_53)) ),
    inference(subtyping,[status(esa)],[c_859])).

cnf(c_2779,plain,
    ( r1_orders_2(sK4,k12_lattice3(sK4,sK0(sK4,k5_waybel_0(sK4,X0_53)),sK1(sK4,k5_waybel_0(sK4,X0_53))),X0_53)
    | ~ m1_subset_1(X0_53,u1_struct_0(sK4))
    | ~ m1_subset_1(k12_lattice3(sK4,sK0(sK4,k5_waybel_0(sK4,X0_53)),sK1(sK4,k5_waybel_0(sK4,X0_53))),u1_struct_0(sK4))
    | ~ r2_hidden(k12_lattice3(sK4,sK0(sK4,k5_waybel_0(sK4,X0_53)),sK1(sK4,k5_waybel_0(sK4,X0_53))),k5_waybel_0(sK4,X0_53)) ),
    inference(instantiation,[status(thm)],[c_2184])).

cnf(c_2781,plain,
    ( r1_orders_2(sK4,k12_lattice3(sK4,sK0(sK4,k5_waybel_0(sK4,sK5)),sK1(sK4,k5_waybel_0(sK4,sK5))),sK5)
    | ~ m1_subset_1(k12_lattice3(sK4,sK0(sK4,k5_waybel_0(sK4,sK5)),sK1(sK4,k5_waybel_0(sK4,sK5))),u1_struct_0(sK4))
    | ~ m1_subset_1(sK5,u1_struct_0(sK4))
    | ~ r2_hidden(k12_lattice3(sK4,sK0(sK4,k5_waybel_0(sK4,sK5)),sK1(sK4,k5_waybel_0(sK4,sK5))),k5_waybel_0(sK4,sK5)) ),
    inference(instantiation,[status(thm)],[c_2779])).

cnf(c_13,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(X1))
    | m1_subset_1(k5_waybel_0(X1,X0),k1_zfmisc_1(u1_struct_0(X1)))
    | ~ l1_orders_2(X1)
    | v2_struct_0(X1) ),
    inference(cnf_transformation,[],[f60])).

cnf(c_997,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(X1))
    | m1_subset_1(k5_waybel_0(X1,X0),k1_zfmisc_1(u1_struct_0(X1)))
    | ~ l1_orders_2(X1)
    | sK4 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_13,c_611])).

cnf(c_998,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(sK4))
    | m1_subset_1(k5_waybel_0(sK4,X0),k1_zfmisc_1(u1_struct_0(sK4)))
    | ~ l1_orders_2(sK4) ),
    inference(unflattening,[status(thm)],[c_997])).

cnf(c_1002,plain,
    ( m1_subset_1(k5_waybel_0(sK4,X0),k1_zfmisc_1(u1_struct_0(sK4)))
    | ~ m1_subset_1(X0,u1_struct_0(sK4)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_998,c_24])).

cnf(c_1003,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(sK4))
    | m1_subset_1(k5_waybel_0(sK4,X0),k1_zfmisc_1(u1_struct_0(sK4))) ),
    inference(renaming,[status(thm)],[c_1002])).

cnf(c_14,plain,
    ( v12_waybel_0(k5_waybel_0(X0,X1),X0)
    | ~ m1_subset_1(X1,u1_struct_0(X0))
    | ~ v4_orders_2(X0)
    | ~ l1_orders_2(X0)
    | v2_struct_0(X0) ),
    inference(cnf_transformation,[],[f61])).

cnf(c_27,negated_conjecture,
    ( v4_orders_2(sK4) ),
    inference(cnf_transformation,[],[f69])).

cnf(c_324,plain,
    ( v12_waybel_0(k5_waybel_0(X0,X1),X0)
    | ~ m1_subset_1(X1,u1_struct_0(X0))
    | ~ l1_orders_2(X0)
    | v2_struct_0(X0)
    | sK4 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_14,c_27])).

cnf(c_325,plain,
    ( v12_waybel_0(k5_waybel_0(sK4,X0),sK4)
    | ~ m1_subset_1(X0,u1_struct_0(sK4))
    | ~ l1_orders_2(sK4)
    | v2_struct_0(sK4) ),
    inference(unflattening,[status(thm)],[c_324])).

cnf(c_329,plain,
    ( v12_waybel_0(k5_waybel_0(sK4,X0),sK4)
    | ~ m1_subset_1(X0,u1_struct_0(sK4)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_325,c_25,c_24,c_98])).

cnf(c_4,plain,
    ( ~ v1_waybel_0(X0,X1)
    | ~ v12_waybel_0(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | m1_subset_1(sK1(X1,X0),u1_struct_0(X1))
    | v1_waybel_7(X0,X1)
    | ~ v3_orders_2(X1)
    | ~ v4_orders_2(X1)
    | ~ v5_orders_2(X1)
    | v1_xboole_0(X0)
    | ~ l1_orders_2(X1)
    | ~ v2_lattice3(X1) ),
    inference(cnf_transformation,[],[f50])).

cnf(c_414,plain,
    ( ~ v1_waybel_0(X0,X1)
    | ~ v12_waybel_0(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | m1_subset_1(sK1(X1,X0),u1_struct_0(X1))
    | v1_waybel_7(X0,X1)
    | ~ v3_orders_2(X1)
    | ~ v5_orders_2(X1)
    | v1_xboole_0(X0)
    | ~ l1_orders_2(X1)
    | ~ v2_lattice3(X1)
    | sK4 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_4,c_27])).

cnf(c_415,plain,
    ( ~ v1_waybel_0(X0,sK4)
    | ~ v12_waybel_0(X0,sK4)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK4)))
    | m1_subset_1(sK1(sK4,X0),u1_struct_0(sK4))
    | v1_waybel_7(X0,sK4)
    | ~ v3_orders_2(sK4)
    | ~ v5_orders_2(sK4)
    | v1_xboole_0(X0)
    | ~ l1_orders_2(sK4)
    | ~ v2_lattice3(sK4) ),
    inference(unflattening,[status(thm)],[c_414])).

cnf(c_28,negated_conjecture,
    ( v3_orders_2(sK4) ),
    inference(cnf_transformation,[],[f68])).

cnf(c_419,plain,
    ( ~ v1_waybel_0(X0,sK4)
    | ~ v12_waybel_0(X0,sK4)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK4)))
    | m1_subset_1(sK1(sK4,X0),u1_struct_0(sK4))
    | v1_waybel_7(X0,sK4)
    | v1_xboole_0(X0) ),
    inference(global_propositional_subsumption,[status(thm)],[c_415,c_28,c_26,c_25,c_24])).

cnf(c_735,plain,
    ( ~ v1_waybel_0(X0,sK4)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK4)))
    | ~ m1_subset_1(X1,u1_struct_0(sK4))
    | m1_subset_1(sK1(sK4,X0),u1_struct_0(sK4))
    | v1_waybel_7(X0,sK4)
    | v1_xboole_0(X0)
    | k5_waybel_0(sK4,X1) != X0
    | sK4 != sK4 ),
    inference(resolution_lifted,[status(thm)],[c_329,c_419])).

cnf(c_736,plain,
    ( ~ v1_waybel_0(k5_waybel_0(sK4,X0),sK4)
    | ~ m1_subset_1(X0,u1_struct_0(sK4))
    | ~ m1_subset_1(k5_waybel_0(sK4,X0),k1_zfmisc_1(u1_struct_0(sK4)))
    | m1_subset_1(sK1(sK4,k5_waybel_0(sK4,X0)),u1_struct_0(sK4))
    | v1_waybel_7(k5_waybel_0(sK4,X0),sK4)
    | v1_xboole_0(k5_waybel_0(sK4,X0)) ),
    inference(unflattening,[status(thm)],[c_735])).

cnf(c_15,plain,
    ( v1_waybel_0(k5_waybel_0(X0,X1),X0)
    | ~ m1_subset_1(X1,u1_struct_0(X0))
    | ~ v3_orders_2(X0)
    | ~ l1_orders_2(X0)
    | v2_struct_0(X0) ),
    inference(cnf_transformation,[],[f63])).

cnf(c_621,plain,
    ( v1_waybel_0(k5_waybel_0(X0,X1),X0)
    | ~ m1_subset_1(X1,u1_struct_0(X0))
    | ~ l1_orders_2(X0)
    | v2_struct_0(X0)
    | sK4 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_15,c_28])).

cnf(c_622,plain,
    ( v1_waybel_0(k5_waybel_0(sK4,X0),sK4)
    | ~ m1_subset_1(X0,u1_struct_0(sK4))
    | ~ l1_orders_2(sK4)
    | v2_struct_0(sK4) ),
    inference(unflattening,[status(thm)],[c_621])).

cnf(c_16,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(X1))
    | ~ v3_orders_2(X1)
    | ~ v1_xboole_0(k5_waybel_0(X1,X0))
    | ~ l1_orders_2(X1)
    | v2_struct_0(X1) ),
    inference(cnf_transformation,[],[f62])).

cnf(c_639,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(X1))
    | ~ v1_xboole_0(k5_waybel_0(X1,X0))
    | ~ l1_orders_2(X1)
    | v2_struct_0(X1)
    | sK4 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_16,c_28])).

cnf(c_640,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(sK4))
    | ~ v1_xboole_0(k5_waybel_0(sK4,X0))
    | ~ l1_orders_2(sK4)
    | v2_struct_0(sK4) ),
    inference(unflattening,[status(thm)],[c_639])).

cnf(c_740,plain,
    ( v1_waybel_7(k5_waybel_0(sK4,X0),sK4)
    | m1_subset_1(sK1(sK4,k5_waybel_0(sK4,X0)),u1_struct_0(sK4))
    | ~ m1_subset_1(k5_waybel_0(sK4,X0),k1_zfmisc_1(u1_struct_0(sK4)))
    | ~ m1_subset_1(X0,u1_struct_0(sK4)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_736,c_25,c_24,c_98,c_622,c_640])).

cnf(c_741,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(sK4))
    | ~ m1_subset_1(k5_waybel_0(sK4,X0),k1_zfmisc_1(u1_struct_0(sK4)))
    | m1_subset_1(sK1(sK4,k5_waybel_0(sK4,X0)),u1_struct_0(sK4))
    | v1_waybel_7(k5_waybel_0(sK4,X0),sK4) ),
    inference(renaming,[status(thm)],[c_740])).

cnf(c_1094,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(sK4))
    | m1_subset_1(sK1(sK4,k5_waybel_0(sK4,X0)),u1_struct_0(sK4))
    | v1_waybel_7(k5_waybel_0(sK4,X0),sK4) ),
    inference(backward_subsumption_resolution,[status(thm)],[c_1003,c_741])).

cnf(c_2170,plain,
    ( ~ m1_subset_1(X0_53,u1_struct_0(sK4))
    | m1_subset_1(sK1(sK4,k5_waybel_0(sK4,X0_53)),u1_struct_0(sK4))
    | v1_waybel_7(k5_waybel_0(sK4,X0_53),sK4) ),
    inference(subtyping,[status(esa)],[c_1094])).

cnf(c_2255,plain,
    ( m1_subset_1(sK1(sK4,k5_waybel_0(sK4,sK5)),u1_struct_0(sK4))
    | ~ m1_subset_1(sK5,u1_struct_0(sK4))
    | v1_waybel_7(k5_waybel_0(sK4,sK5),sK4) ),
    inference(instantiation,[status(thm)],[c_2170])).

cnf(c_5,plain,
    ( ~ v1_waybel_0(X0,X1)
    | ~ v12_waybel_0(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | m1_subset_1(sK0(X1,X0),u1_struct_0(X1))
    | v1_waybel_7(X0,X1)
    | ~ v3_orders_2(X1)
    | ~ v4_orders_2(X1)
    | ~ v5_orders_2(X1)
    | v1_xboole_0(X0)
    | ~ l1_orders_2(X1)
    | ~ v2_lattice3(X1) ),
    inference(cnf_transformation,[],[f49])).

cnf(c_384,plain,
    ( ~ v1_waybel_0(X0,X1)
    | ~ v12_waybel_0(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | m1_subset_1(sK0(X1,X0),u1_struct_0(X1))
    | v1_waybel_7(X0,X1)
    | ~ v3_orders_2(X1)
    | ~ v5_orders_2(X1)
    | v1_xboole_0(X0)
    | ~ l1_orders_2(X1)
    | ~ v2_lattice3(X1)
    | sK4 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_5,c_27])).

cnf(c_385,plain,
    ( ~ v1_waybel_0(X0,sK4)
    | ~ v12_waybel_0(X0,sK4)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK4)))
    | m1_subset_1(sK0(sK4,X0),u1_struct_0(sK4))
    | v1_waybel_7(X0,sK4)
    | ~ v3_orders_2(sK4)
    | ~ v5_orders_2(sK4)
    | v1_xboole_0(X0)
    | ~ l1_orders_2(sK4)
    | ~ v2_lattice3(sK4) ),
    inference(unflattening,[status(thm)],[c_384])).

cnf(c_389,plain,
    ( ~ v1_waybel_0(X0,sK4)
    | ~ v12_waybel_0(X0,sK4)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK4)))
    | m1_subset_1(sK0(sK4,X0),u1_struct_0(sK4))
    | v1_waybel_7(X0,sK4)
    | v1_xboole_0(X0) ),
    inference(global_propositional_subsumption,[status(thm)],[c_385,c_28,c_26,c_25,c_24])).

cnf(c_759,plain,
    ( ~ v1_waybel_0(X0,sK4)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK4)))
    | ~ m1_subset_1(X1,u1_struct_0(sK4))
    | m1_subset_1(sK0(sK4,X0),u1_struct_0(sK4))
    | v1_waybel_7(X0,sK4)
    | v1_xboole_0(X0)
    | k5_waybel_0(sK4,X1) != X0
    | sK4 != sK4 ),
    inference(resolution_lifted,[status(thm)],[c_329,c_389])).

cnf(c_760,plain,
    ( ~ v1_waybel_0(k5_waybel_0(sK4,X0),sK4)
    | ~ m1_subset_1(X0,u1_struct_0(sK4))
    | ~ m1_subset_1(k5_waybel_0(sK4,X0),k1_zfmisc_1(u1_struct_0(sK4)))
    | m1_subset_1(sK0(sK4,k5_waybel_0(sK4,X0)),u1_struct_0(sK4))
    | v1_waybel_7(k5_waybel_0(sK4,X0),sK4)
    | v1_xboole_0(k5_waybel_0(sK4,X0)) ),
    inference(unflattening,[status(thm)],[c_759])).

cnf(c_764,plain,
    ( v1_waybel_7(k5_waybel_0(sK4,X0),sK4)
    | m1_subset_1(sK0(sK4,k5_waybel_0(sK4,X0)),u1_struct_0(sK4))
    | ~ m1_subset_1(k5_waybel_0(sK4,X0),k1_zfmisc_1(u1_struct_0(sK4)))
    | ~ m1_subset_1(X0,u1_struct_0(sK4)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_760,c_25,c_24,c_98,c_622,c_640])).

cnf(c_765,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(sK4))
    | ~ m1_subset_1(k5_waybel_0(sK4,X0),k1_zfmisc_1(u1_struct_0(sK4)))
    | m1_subset_1(sK0(sK4,k5_waybel_0(sK4,X0)),u1_struct_0(sK4))
    | v1_waybel_7(k5_waybel_0(sK4,X0),sK4) ),
    inference(renaming,[status(thm)],[c_764])).

cnf(c_1093,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(sK4))
    | m1_subset_1(sK0(sK4,k5_waybel_0(sK4,X0)),u1_struct_0(sK4))
    | v1_waybel_7(k5_waybel_0(sK4,X0),sK4) ),
    inference(backward_subsumption_resolution,[status(thm)],[c_1003,c_765])).

cnf(c_2171,plain,
    ( ~ m1_subset_1(X0_53,u1_struct_0(sK4))
    | m1_subset_1(sK0(sK4,k5_waybel_0(sK4,X0_53)),u1_struct_0(sK4))
    | v1_waybel_7(k5_waybel_0(sK4,X0_53),sK4) ),
    inference(subtyping,[status(esa)],[c_1093])).

cnf(c_2252,plain,
    ( m1_subset_1(sK0(sK4,k5_waybel_0(sK4,sK5)),u1_struct_0(sK4))
    | ~ m1_subset_1(sK5,u1_struct_0(sK4))
    | v1_waybel_7(k5_waybel_0(sK4,sK5),sK4) ),
    inference(instantiation,[status(thm)],[c_2171])).

cnf(c_2,plain,
    ( ~ v1_waybel_0(X0,X1)
    | ~ v12_waybel_0(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ r2_hidden(sK0(X1,X0),X0)
    | v1_waybel_7(X0,X1)
    | ~ v3_orders_2(X1)
    | ~ v4_orders_2(X1)
    | ~ v5_orders_2(X1)
    | v1_xboole_0(X0)
    | ~ l1_orders_2(X1)
    | ~ v2_lattice3(X1) ),
    inference(cnf_transformation,[],[f52])).

cnf(c_474,plain,
    ( ~ v1_waybel_0(X0,X1)
    | ~ v12_waybel_0(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ r2_hidden(sK0(X1,X0),X0)
    | v1_waybel_7(X0,X1)
    | ~ v3_orders_2(X1)
    | ~ v5_orders_2(X1)
    | v1_xboole_0(X0)
    | ~ l1_orders_2(X1)
    | ~ v2_lattice3(X1)
    | sK4 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_2,c_27])).

cnf(c_475,plain,
    ( ~ v1_waybel_0(X0,sK4)
    | ~ v12_waybel_0(X0,sK4)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK4)))
    | ~ r2_hidden(sK0(sK4,X0),X0)
    | v1_waybel_7(X0,sK4)
    | ~ v3_orders_2(sK4)
    | ~ v5_orders_2(sK4)
    | v1_xboole_0(X0)
    | ~ l1_orders_2(sK4)
    | ~ v2_lattice3(sK4) ),
    inference(unflattening,[status(thm)],[c_474])).

cnf(c_479,plain,
    ( ~ v1_waybel_0(X0,sK4)
    | ~ v12_waybel_0(X0,sK4)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK4)))
    | ~ r2_hidden(sK0(sK4,X0),X0)
    | v1_waybel_7(X0,sK4)
    | v1_xboole_0(X0) ),
    inference(global_propositional_subsumption,[status(thm)],[c_475,c_28,c_26,c_25,c_24])).

cnf(c_687,plain,
    ( ~ v1_waybel_0(X0,sK4)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK4)))
    | ~ m1_subset_1(X1,u1_struct_0(sK4))
    | ~ r2_hidden(sK0(sK4,X0),X0)
    | v1_waybel_7(X0,sK4)
    | v1_xboole_0(X0)
    | k5_waybel_0(sK4,X1) != X0
    | sK4 != sK4 ),
    inference(resolution_lifted,[status(thm)],[c_329,c_479])).

cnf(c_688,plain,
    ( ~ v1_waybel_0(k5_waybel_0(sK4,X0),sK4)
    | ~ m1_subset_1(X0,u1_struct_0(sK4))
    | ~ m1_subset_1(k5_waybel_0(sK4,X0),k1_zfmisc_1(u1_struct_0(sK4)))
    | ~ r2_hidden(sK0(sK4,k5_waybel_0(sK4,X0)),k5_waybel_0(sK4,X0))
    | v1_waybel_7(k5_waybel_0(sK4,X0),sK4)
    | v1_xboole_0(k5_waybel_0(sK4,X0)) ),
    inference(unflattening,[status(thm)],[c_687])).

cnf(c_692,plain,
    ( v1_waybel_7(k5_waybel_0(sK4,X0),sK4)
    | ~ r2_hidden(sK0(sK4,k5_waybel_0(sK4,X0)),k5_waybel_0(sK4,X0))
    | ~ m1_subset_1(k5_waybel_0(sK4,X0),k1_zfmisc_1(u1_struct_0(sK4)))
    | ~ m1_subset_1(X0,u1_struct_0(sK4)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_688,c_25,c_24,c_98,c_622,c_640])).

cnf(c_693,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(sK4))
    | ~ m1_subset_1(k5_waybel_0(sK4,X0),k1_zfmisc_1(u1_struct_0(sK4)))
    | ~ r2_hidden(sK0(sK4,k5_waybel_0(sK4,X0)),k5_waybel_0(sK4,X0))
    | v1_waybel_7(k5_waybel_0(sK4,X0),sK4) ),
    inference(renaming,[status(thm)],[c_692])).

cnf(c_1091,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(sK4))
    | ~ r2_hidden(sK0(sK4,k5_waybel_0(sK4,X0)),k5_waybel_0(sK4,X0))
    | v1_waybel_7(k5_waybel_0(sK4,X0),sK4) ),
    inference(backward_subsumption_resolution,[status(thm)],[c_1003,c_693])).

cnf(c_2173,plain,
    ( ~ m1_subset_1(X0_53,u1_struct_0(sK4))
    | ~ r2_hidden(sK0(sK4,k5_waybel_0(sK4,X0_53)),k5_waybel_0(sK4,X0_53))
    | v1_waybel_7(k5_waybel_0(sK4,X0_53),sK4) ),
    inference(subtyping,[status(esa)],[c_1091])).

cnf(c_2248,plain,
    ( ~ m1_subset_1(sK5,u1_struct_0(sK4))
    | ~ r2_hidden(sK0(sK4,k5_waybel_0(sK4,sK5)),k5_waybel_0(sK4,sK5))
    | v1_waybel_7(k5_waybel_0(sK4,sK5),sK4) ),
    inference(instantiation,[status(thm)],[c_2173])).

cnf(c_3,plain,
    ( ~ v1_waybel_0(X0,X1)
    | ~ v12_waybel_0(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | r2_hidden(k12_lattice3(X1,sK0(X1,X0),sK1(X1,X0)),X0)
    | v1_waybel_7(X0,X1)
    | ~ v3_orders_2(X1)
    | ~ v4_orders_2(X1)
    | ~ v5_orders_2(X1)
    | v1_xboole_0(X0)
    | ~ l1_orders_2(X1)
    | ~ v2_lattice3(X1) ),
    inference(cnf_transformation,[],[f51])).

cnf(c_444,plain,
    ( ~ v1_waybel_0(X0,X1)
    | ~ v12_waybel_0(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | r2_hidden(k12_lattice3(X1,sK0(X1,X0),sK1(X1,X0)),X0)
    | v1_waybel_7(X0,X1)
    | ~ v3_orders_2(X1)
    | ~ v5_orders_2(X1)
    | v1_xboole_0(X0)
    | ~ l1_orders_2(X1)
    | ~ v2_lattice3(X1)
    | sK4 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_3,c_27])).

cnf(c_445,plain,
    ( ~ v1_waybel_0(X0,sK4)
    | ~ v12_waybel_0(X0,sK4)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK4)))
    | r2_hidden(k12_lattice3(sK4,sK0(sK4,X0),sK1(sK4,X0)),X0)
    | v1_waybel_7(X0,sK4)
    | ~ v3_orders_2(sK4)
    | ~ v5_orders_2(sK4)
    | v1_xboole_0(X0)
    | ~ l1_orders_2(sK4)
    | ~ v2_lattice3(sK4) ),
    inference(unflattening,[status(thm)],[c_444])).

cnf(c_449,plain,
    ( ~ v1_waybel_0(X0,sK4)
    | ~ v12_waybel_0(X0,sK4)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK4)))
    | r2_hidden(k12_lattice3(sK4,sK0(sK4,X0),sK1(sK4,X0)),X0)
    | v1_waybel_7(X0,sK4)
    | v1_xboole_0(X0) ),
    inference(global_propositional_subsumption,[status(thm)],[c_445,c_28,c_26,c_25,c_24])).

cnf(c_711,plain,
    ( ~ v1_waybel_0(X0,sK4)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK4)))
    | ~ m1_subset_1(X1,u1_struct_0(sK4))
    | r2_hidden(k12_lattice3(sK4,sK0(sK4,X0),sK1(sK4,X0)),X0)
    | v1_waybel_7(X0,sK4)
    | v1_xboole_0(X0)
    | k5_waybel_0(sK4,X1) != X0
    | sK4 != sK4 ),
    inference(resolution_lifted,[status(thm)],[c_329,c_449])).

cnf(c_712,plain,
    ( ~ v1_waybel_0(k5_waybel_0(sK4,X0),sK4)
    | ~ m1_subset_1(X0,u1_struct_0(sK4))
    | ~ m1_subset_1(k5_waybel_0(sK4,X0),k1_zfmisc_1(u1_struct_0(sK4)))
    | r2_hidden(k12_lattice3(sK4,sK0(sK4,k5_waybel_0(sK4,X0)),sK1(sK4,k5_waybel_0(sK4,X0))),k5_waybel_0(sK4,X0))
    | v1_waybel_7(k5_waybel_0(sK4,X0),sK4)
    | v1_xboole_0(k5_waybel_0(sK4,X0)) ),
    inference(unflattening,[status(thm)],[c_711])).

cnf(c_716,plain,
    ( v1_waybel_7(k5_waybel_0(sK4,X0),sK4)
    | r2_hidden(k12_lattice3(sK4,sK0(sK4,k5_waybel_0(sK4,X0)),sK1(sK4,k5_waybel_0(sK4,X0))),k5_waybel_0(sK4,X0))
    | ~ m1_subset_1(k5_waybel_0(sK4,X0),k1_zfmisc_1(u1_struct_0(sK4)))
    | ~ m1_subset_1(X0,u1_struct_0(sK4)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_712,c_25,c_24,c_98,c_622,c_640])).

cnf(c_717,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(sK4))
    | ~ m1_subset_1(k5_waybel_0(sK4,X0),k1_zfmisc_1(u1_struct_0(sK4)))
    | r2_hidden(k12_lattice3(sK4,sK0(sK4,k5_waybel_0(sK4,X0)),sK1(sK4,k5_waybel_0(sK4,X0))),k5_waybel_0(sK4,X0))
    | v1_waybel_7(k5_waybel_0(sK4,X0),sK4) ),
    inference(renaming,[status(thm)],[c_716])).

cnf(c_1090,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(sK4))
    | r2_hidden(k12_lattice3(sK4,sK0(sK4,k5_waybel_0(sK4,X0)),sK1(sK4,k5_waybel_0(sK4,X0))),k5_waybel_0(sK4,X0))
    | v1_waybel_7(k5_waybel_0(sK4,X0),sK4) ),
    inference(backward_subsumption_resolution,[status(thm)],[c_1003,c_717])).

cnf(c_2174,plain,
    ( ~ m1_subset_1(X0_53,u1_struct_0(sK4))
    | r2_hidden(k12_lattice3(sK4,sK0(sK4,k5_waybel_0(sK4,X0_53)),sK1(sK4,k5_waybel_0(sK4,X0_53))),k5_waybel_0(sK4,X0_53))
    | v1_waybel_7(k5_waybel_0(sK4,X0_53),sK4) ),
    inference(subtyping,[status(esa)],[c_1090])).

cnf(c_2245,plain,
    ( ~ m1_subset_1(sK5,u1_struct_0(sK4))
    | r2_hidden(k12_lattice3(sK4,sK0(sK4,k5_waybel_0(sK4,sK5)),sK1(sK4,k5_waybel_0(sK4,sK5))),k5_waybel_0(sK4,sK5))
    | v1_waybel_7(k5_waybel_0(sK4,sK5),sK4) ),
    inference(instantiation,[status(thm)],[c_2174])).

cnf(c_1,plain,
    ( ~ v1_waybel_0(X0,X1)
    | ~ v12_waybel_0(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ r2_hidden(sK1(X1,X0),X0)
    | v1_waybel_7(X0,X1)
    | ~ v3_orders_2(X1)
    | ~ v4_orders_2(X1)
    | ~ v5_orders_2(X1)
    | v1_xboole_0(X0)
    | ~ l1_orders_2(X1)
    | ~ v2_lattice3(X1) ),
    inference(cnf_transformation,[],[f53])).

cnf(c_504,plain,
    ( ~ v1_waybel_0(X0,X1)
    | ~ v12_waybel_0(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ r2_hidden(sK1(X1,X0),X0)
    | v1_waybel_7(X0,X1)
    | ~ v3_orders_2(X1)
    | ~ v5_orders_2(X1)
    | v1_xboole_0(X0)
    | ~ l1_orders_2(X1)
    | ~ v2_lattice3(X1)
    | sK4 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_1,c_27])).

cnf(c_505,plain,
    ( ~ v1_waybel_0(X0,sK4)
    | ~ v12_waybel_0(X0,sK4)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK4)))
    | ~ r2_hidden(sK1(sK4,X0),X0)
    | v1_waybel_7(X0,sK4)
    | ~ v3_orders_2(sK4)
    | ~ v5_orders_2(sK4)
    | v1_xboole_0(X0)
    | ~ l1_orders_2(sK4)
    | ~ v2_lattice3(sK4) ),
    inference(unflattening,[status(thm)],[c_504])).

cnf(c_509,plain,
    ( ~ v1_waybel_0(X0,sK4)
    | ~ v12_waybel_0(X0,sK4)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK4)))
    | ~ r2_hidden(sK1(sK4,X0),X0)
    | v1_waybel_7(X0,sK4)
    | v1_xboole_0(X0) ),
    inference(global_propositional_subsumption,[status(thm)],[c_505,c_28,c_26,c_25,c_24])).

cnf(c_663,plain,
    ( ~ v1_waybel_0(X0,sK4)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK4)))
    | ~ m1_subset_1(X1,u1_struct_0(sK4))
    | ~ r2_hidden(sK1(sK4,X0),X0)
    | v1_waybel_7(X0,sK4)
    | v1_xboole_0(X0)
    | k5_waybel_0(sK4,X1) != X0
    | sK4 != sK4 ),
    inference(resolution_lifted,[status(thm)],[c_329,c_509])).

cnf(c_664,plain,
    ( ~ v1_waybel_0(k5_waybel_0(sK4,X0),sK4)
    | ~ m1_subset_1(X0,u1_struct_0(sK4))
    | ~ m1_subset_1(k5_waybel_0(sK4,X0),k1_zfmisc_1(u1_struct_0(sK4)))
    | ~ r2_hidden(sK1(sK4,k5_waybel_0(sK4,X0)),k5_waybel_0(sK4,X0))
    | v1_waybel_7(k5_waybel_0(sK4,X0),sK4)
    | v1_xboole_0(k5_waybel_0(sK4,X0)) ),
    inference(unflattening,[status(thm)],[c_663])).

cnf(c_668,plain,
    ( v1_waybel_7(k5_waybel_0(sK4,X0),sK4)
    | ~ r2_hidden(sK1(sK4,k5_waybel_0(sK4,X0)),k5_waybel_0(sK4,X0))
    | ~ m1_subset_1(k5_waybel_0(sK4,X0),k1_zfmisc_1(u1_struct_0(sK4)))
    | ~ m1_subset_1(X0,u1_struct_0(sK4)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_664,c_25,c_24,c_98,c_622,c_640])).

cnf(c_669,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(sK4))
    | ~ m1_subset_1(k5_waybel_0(sK4,X0),k1_zfmisc_1(u1_struct_0(sK4)))
    | ~ r2_hidden(sK1(sK4,k5_waybel_0(sK4,X0)),k5_waybel_0(sK4,X0))
    | v1_waybel_7(k5_waybel_0(sK4,X0),sK4) ),
    inference(renaming,[status(thm)],[c_668])).

cnf(c_1089,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(sK4))
    | ~ r2_hidden(sK1(sK4,k5_waybel_0(sK4,X0)),k5_waybel_0(sK4,X0))
    | v1_waybel_7(k5_waybel_0(sK4,X0),sK4) ),
    inference(backward_subsumption_resolution,[status(thm)],[c_1003,c_669])).

cnf(c_2175,plain,
    ( ~ m1_subset_1(X0_53,u1_struct_0(sK4))
    | ~ r2_hidden(sK1(sK4,k5_waybel_0(sK4,X0_53)),k5_waybel_0(sK4,X0_53))
    | v1_waybel_7(k5_waybel_0(sK4,X0_53),sK4) ),
    inference(subtyping,[status(esa)],[c_1089])).

cnf(c_2242,plain,
    ( ~ m1_subset_1(sK5,u1_struct_0(sK4))
    | ~ r2_hidden(sK1(sK4,k5_waybel_0(sK4,sK5)),k5_waybel_0(sK4,sK5))
    | v1_waybel_7(k5_waybel_0(sK4,sK5),sK4) ),
    inference(instantiation,[status(thm)],[c_2175])).

cnf(c_2178,plain,
    ( ~ m1_subset_1(X0_53,u1_struct_0(sK4))
    | m1_subset_1(k5_waybel_0(sK4,X0_53),k1_zfmisc_1(u1_struct_0(sK4))) ),
    inference(subtyping,[status(esa)],[c_1003])).

cnf(c_2237,plain,
    ( m1_subset_1(k5_waybel_0(sK4,sK5),k1_zfmisc_1(u1_struct_0(sK4)))
    | ~ m1_subset_1(sK5,u1_struct_0(sK4)) ),
    inference(instantiation,[status(thm)],[c_2178])).

cnf(c_21,negated_conjecture,
    ( ~ v1_waybel_7(k5_waybel_0(sK4,sK5),sK4) ),
    inference(cnf_transformation,[],[f75])).

cnf(c_22,negated_conjecture,
    ( v5_waybel_6(sK5,sK4) ),
    inference(cnf_transformation,[],[f74])).

cnf(c_23,negated_conjecture,
    ( m1_subset_1(sK5,u1_struct_0(sK4)) ),
    inference(cnf_transformation,[],[f73])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_3522,c_3417,c_3126,c_3049,c_2931,c_2875,c_2781,c_2255,c_2252,c_2248,c_2245,c_2242,c_2237,c_21,c_22,c_23])).


%------------------------------------------------------------------------------
