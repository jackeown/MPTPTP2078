%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT1964+1.001 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n027.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:46:56 EST 2020

% Result     : Theorem 3.85s
% Output     : CNFRefutation 3.85s
% Verified   : 
% Statistics : Number of formulae       :  164 (1321 expanded)
%              Number of clauses        :  104 ( 463 expanded)
%              Number of leaves         :   14 ( 232 expanded)
%              Depth                    :   28
%              Number of atoms          :  797 (8174 expanded)
%              Number of equality atoms :  237 ( 732 expanded)
%              Maximal formula depth    :   16 (   6 average)
%              Maximal clause size      :   20 (   4 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f8,conjecture,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(k3_yellow_1(X0))))
        & v13_waybel_0(X1,k3_yellow_1(X0)) )
     => ( v2_waybel_0(X1,k3_yellow_1(X0))
      <=> ! [X2,X3] :
            ( ( r2_hidden(X3,X1)
              & r2_hidden(X2,X1) )
           => r2_hidden(k3_xboole_0(X2,X3),X1) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f9,negated_conjecture,(
    ~ ! [X0,X1] :
        ( ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(k3_yellow_1(X0))))
          & v13_waybel_0(X1,k3_yellow_1(X0)) )
       => ( v2_waybel_0(X1,k3_yellow_1(X0))
        <=> ! [X2,X3] :
              ( ( r2_hidden(X3,X1)
                & r2_hidden(X2,X1) )
             => r2_hidden(k3_xboole_0(X2,X3),X1) ) ) ) ),
    inference(negated_conjecture,[],[f8])).

fof(f28,plain,(
    ? [X0,X1] :
      ( ( v2_waybel_0(X1,k3_yellow_1(X0))
      <~> ! [X2,X3] :
            ( r2_hidden(k3_xboole_0(X2,X3),X1)
            | ~ r2_hidden(X3,X1)
            | ~ r2_hidden(X2,X1) ) )
      & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(k3_yellow_1(X0))))
      & v13_waybel_0(X1,k3_yellow_1(X0)) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f29,plain,(
    ? [X0,X1] :
      ( ( v2_waybel_0(X1,k3_yellow_1(X0))
      <~> ! [X2,X3] :
            ( r2_hidden(k3_xboole_0(X2,X3),X1)
            | ~ r2_hidden(X3,X1)
            | ~ r2_hidden(X2,X1) ) )
      & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(k3_yellow_1(X0))))
      & v13_waybel_0(X1,k3_yellow_1(X0)) ) ),
    inference(flattening,[],[f28])).

fof(f35,plain,(
    ? [X0,X1] :
      ( ( ? [X2,X3] :
            ( ~ r2_hidden(k3_xboole_0(X2,X3),X1)
            & r2_hidden(X3,X1)
            & r2_hidden(X2,X1) )
        | ~ v2_waybel_0(X1,k3_yellow_1(X0)) )
      & ( ! [X2,X3] :
            ( r2_hidden(k3_xboole_0(X2,X3),X1)
            | ~ r2_hidden(X3,X1)
            | ~ r2_hidden(X2,X1) )
        | v2_waybel_0(X1,k3_yellow_1(X0)) )
      & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(k3_yellow_1(X0))))
      & v13_waybel_0(X1,k3_yellow_1(X0)) ) ),
    inference(nnf_transformation,[],[f29])).

fof(f36,plain,(
    ? [X0,X1] :
      ( ( ? [X2,X3] :
            ( ~ r2_hidden(k3_xboole_0(X2,X3),X1)
            & r2_hidden(X3,X1)
            & r2_hidden(X2,X1) )
        | ~ v2_waybel_0(X1,k3_yellow_1(X0)) )
      & ( ! [X2,X3] :
            ( r2_hidden(k3_xboole_0(X2,X3),X1)
            | ~ r2_hidden(X3,X1)
            | ~ r2_hidden(X2,X1) )
        | v2_waybel_0(X1,k3_yellow_1(X0)) )
      & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(k3_yellow_1(X0))))
      & v13_waybel_0(X1,k3_yellow_1(X0)) ) ),
    inference(flattening,[],[f35])).

fof(f37,plain,(
    ? [X0,X1] :
      ( ( ? [X2,X3] :
            ( ~ r2_hidden(k3_xboole_0(X2,X3),X1)
            & r2_hidden(X3,X1)
            & r2_hidden(X2,X1) )
        | ~ v2_waybel_0(X1,k3_yellow_1(X0)) )
      & ( ! [X4,X5] :
            ( r2_hidden(k3_xboole_0(X4,X5),X1)
            | ~ r2_hidden(X5,X1)
            | ~ r2_hidden(X4,X1) )
        | v2_waybel_0(X1,k3_yellow_1(X0)) )
      & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(k3_yellow_1(X0))))
      & v13_waybel_0(X1,k3_yellow_1(X0)) ) ),
    inference(rectify,[],[f36])).

fof(f39,plain,(
    ! [X1] :
      ( ? [X2,X3] :
          ( ~ r2_hidden(k3_xboole_0(X2,X3),X1)
          & r2_hidden(X3,X1)
          & r2_hidden(X2,X1) )
     => ( ~ r2_hidden(k3_xboole_0(sK4,sK5),X1)
        & r2_hidden(sK5,X1)
        & r2_hidden(sK4,X1) ) ) ),
    introduced(choice_axiom,[])).

fof(f38,plain,
    ( ? [X0,X1] :
        ( ( ? [X2,X3] :
              ( ~ r2_hidden(k3_xboole_0(X2,X3),X1)
              & r2_hidden(X3,X1)
              & r2_hidden(X2,X1) )
          | ~ v2_waybel_0(X1,k3_yellow_1(X0)) )
        & ( ! [X4,X5] :
              ( r2_hidden(k3_xboole_0(X4,X5),X1)
              | ~ r2_hidden(X5,X1)
              | ~ r2_hidden(X4,X1) )
          | v2_waybel_0(X1,k3_yellow_1(X0)) )
        & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(k3_yellow_1(X0))))
        & v13_waybel_0(X1,k3_yellow_1(X0)) )
   => ( ( ? [X3,X2] :
            ( ~ r2_hidden(k3_xboole_0(X2,X3),sK3)
            & r2_hidden(X3,sK3)
            & r2_hidden(X2,sK3) )
        | ~ v2_waybel_0(sK3,k3_yellow_1(sK2)) )
      & ( ! [X5,X4] :
            ( r2_hidden(k3_xboole_0(X4,X5),sK3)
            | ~ r2_hidden(X5,sK3)
            | ~ r2_hidden(X4,sK3) )
        | v2_waybel_0(sK3,k3_yellow_1(sK2)) )
      & m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(k3_yellow_1(sK2))))
      & v13_waybel_0(sK3,k3_yellow_1(sK2)) ) ),
    introduced(choice_axiom,[])).

fof(f40,plain,
    ( ( ( ~ r2_hidden(k3_xboole_0(sK4,sK5),sK3)
        & r2_hidden(sK5,sK3)
        & r2_hidden(sK4,sK3) )
      | ~ v2_waybel_0(sK3,k3_yellow_1(sK2)) )
    & ( ! [X4,X5] :
          ( r2_hidden(k3_xboole_0(X4,X5),sK3)
          | ~ r2_hidden(X5,sK3)
          | ~ r2_hidden(X4,sK3) )
      | v2_waybel_0(sK3,k3_yellow_1(sK2)) )
    & m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(k3_yellow_1(sK2))))
    & v13_waybel_0(sK3,k3_yellow_1(sK2)) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2,sK3,sK4,sK5])],[f37,f39,f38])).

fof(f58,plain,(
    m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(k3_yellow_1(sK2)))) ),
    inference(cnf_transformation,[],[f40])).

fof(f6,axiom,(
    ! [X0] :
      ( ( l1_orders_2(X0)
        & v2_lattice3(X0)
        & v5_orders_2(X0) )
     => ! [X1] :
          ( ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
            & v13_waybel_0(X1,X0) )
         => ( v2_waybel_0(X1,X0)
          <=> ! [X2] :
                ( m1_subset_1(X2,u1_struct_0(X0))
               => ! [X3] :
                    ( m1_subset_1(X3,u1_struct_0(X0))
                   => ( ( r2_hidden(X3,X1)
                        & r2_hidden(X2,X1) )
                     => r2_hidden(k12_lattice3(X0,X2,X3),X1) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f24,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( v2_waybel_0(X1,X0)
          <=> ! [X2] :
                ( ! [X3] :
                    ( r2_hidden(k12_lattice3(X0,X2,X3),X1)
                    | ~ r2_hidden(X3,X1)
                    | ~ r2_hidden(X2,X1)
                    | ~ m1_subset_1(X3,u1_struct_0(X0)) )
                | ~ m1_subset_1(X2,u1_struct_0(X0)) ) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
          | ~ v13_waybel_0(X1,X0) )
      | ~ l1_orders_2(X0)
      | ~ v2_lattice3(X0)
      | ~ v5_orders_2(X0) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f25,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( v2_waybel_0(X1,X0)
          <=> ! [X2] :
                ( ! [X3] :
                    ( r2_hidden(k12_lattice3(X0,X2,X3),X1)
                    | ~ r2_hidden(X3,X1)
                    | ~ r2_hidden(X2,X1)
                    | ~ m1_subset_1(X3,u1_struct_0(X0)) )
                | ~ m1_subset_1(X2,u1_struct_0(X0)) ) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
          | ~ v13_waybel_0(X1,X0) )
      | ~ l1_orders_2(X0)
      | ~ v2_lattice3(X0)
      | ~ v5_orders_2(X0) ) ),
    inference(flattening,[],[f24])).

fof(f30,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ( v2_waybel_0(X1,X0)
              | ? [X2] :
                  ( ? [X3] :
                      ( ~ r2_hidden(k12_lattice3(X0,X2,X3),X1)
                      & r2_hidden(X3,X1)
                      & r2_hidden(X2,X1)
                      & m1_subset_1(X3,u1_struct_0(X0)) )
                  & m1_subset_1(X2,u1_struct_0(X0)) ) )
            & ( ! [X2] :
                  ( ! [X3] :
                      ( r2_hidden(k12_lattice3(X0,X2,X3),X1)
                      | ~ r2_hidden(X3,X1)
                      | ~ r2_hidden(X2,X1)
                      | ~ m1_subset_1(X3,u1_struct_0(X0)) )
                  | ~ m1_subset_1(X2,u1_struct_0(X0)) )
              | ~ v2_waybel_0(X1,X0) ) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
          | ~ v13_waybel_0(X1,X0) )
      | ~ l1_orders_2(X0)
      | ~ v2_lattice3(X0)
      | ~ v5_orders_2(X0) ) ),
    inference(nnf_transformation,[],[f25])).

fof(f31,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ( v2_waybel_0(X1,X0)
              | ? [X2] :
                  ( ? [X3] :
                      ( ~ r2_hidden(k12_lattice3(X0,X2,X3),X1)
                      & r2_hidden(X3,X1)
                      & r2_hidden(X2,X1)
                      & m1_subset_1(X3,u1_struct_0(X0)) )
                  & m1_subset_1(X2,u1_struct_0(X0)) ) )
            & ( ! [X4] :
                  ( ! [X5] :
                      ( r2_hidden(k12_lattice3(X0,X4,X5),X1)
                      | ~ r2_hidden(X5,X1)
                      | ~ r2_hidden(X4,X1)
                      | ~ m1_subset_1(X5,u1_struct_0(X0)) )
                  | ~ m1_subset_1(X4,u1_struct_0(X0)) )
              | ~ v2_waybel_0(X1,X0) ) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
          | ~ v13_waybel_0(X1,X0) )
      | ~ l1_orders_2(X0)
      | ~ v2_lattice3(X0)
      | ~ v5_orders_2(X0) ) ),
    inference(rectify,[],[f30])).

fof(f33,plain,(
    ! [X2,X1,X0] :
      ( ? [X3] :
          ( ~ r2_hidden(k12_lattice3(X0,X2,X3),X1)
          & r2_hidden(X3,X1)
          & r2_hidden(X2,X1)
          & m1_subset_1(X3,u1_struct_0(X0)) )
     => ( ~ r2_hidden(k12_lattice3(X0,X2,sK1(X0,X1)),X1)
        & r2_hidden(sK1(X0,X1),X1)
        & r2_hidden(X2,X1)
        & m1_subset_1(sK1(X0,X1),u1_struct_0(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f32,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ? [X3] :
              ( ~ r2_hidden(k12_lattice3(X0,X2,X3),X1)
              & r2_hidden(X3,X1)
              & r2_hidden(X2,X1)
              & m1_subset_1(X3,u1_struct_0(X0)) )
          & m1_subset_1(X2,u1_struct_0(X0)) )
     => ( ? [X3] :
            ( ~ r2_hidden(k12_lattice3(X0,sK0(X0,X1),X3),X1)
            & r2_hidden(X3,X1)
            & r2_hidden(sK0(X0,X1),X1)
            & m1_subset_1(X3,u1_struct_0(X0)) )
        & m1_subset_1(sK0(X0,X1),u1_struct_0(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f34,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ( v2_waybel_0(X1,X0)
              | ( ~ r2_hidden(k12_lattice3(X0,sK0(X0,X1),sK1(X0,X1)),X1)
                & r2_hidden(sK1(X0,X1),X1)
                & r2_hidden(sK0(X0,X1),X1)
                & m1_subset_1(sK1(X0,X1),u1_struct_0(X0))
                & m1_subset_1(sK0(X0,X1),u1_struct_0(X0)) ) )
            & ( ! [X4] :
                  ( ! [X5] :
                      ( r2_hidden(k12_lattice3(X0,X4,X5),X1)
                      | ~ r2_hidden(X5,X1)
                      | ~ r2_hidden(X4,X1)
                      | ~ m1_subset_1(X5,u1_struct_0(X0)) )
                  | ~ m1_subset_1(X4,u1_struct_0(X0)) )
              | ~ v2_waybel_0(X1,X0) ) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
          | ~ v13_waybel_0(X1,X0) )
      | ~ l1_orders_2(X0)
      | ~ v2_lattice3(X0)
      | ~ v5_orders_2(X0) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f31,f33,f32])).

fof(f52,plain,(
    ! [X0,X1] :
      ( v2_waybel_0(X1,X0)
      | m1_subset_1(sK1(X0,X1),u1_struct_0(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ v13_waybel_0(X1,X0)
      | ~ l1_orders_2(X0)
      | ~ v2_lattice3(X0)
      | ~ v5_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f34])).

fof(f5,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,u1_struct_0(k3_yellow_1(X0)))
     => ! [X2] :
          ( m1_subset_1(X2,u1_struct_0(k3_yellow_1(X0)))
         => ( k12_lattice3(k3_yellow_1(X0),X1,X2) = k3_xboole_0(X1,X2)
            & k13_lattice3(k3_yellow_1(X0),X1,X2) = k2_xboole_0(X1,X2) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f23,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( ( k12_lattice3(k3_yellow_1(X0),X1,X2) = k3_xboole_0(X1,X2)
            & k13_lattice3(k3_yellow_1(X0),X1,X2) = k2_xboole_0(X1,X2) )
          | ~ m1_subset_1(X2,u1_struct_0(k3_yellow_1(X0))) )
      | ~ m1_subset_1(X1,u1_struct_0(k3_yellow_1(X0))) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f48,plain,(
    ! [X2,X0,X1] :
      ( k13_lattice3(k3_yellow_1(X0),X1,X2) = k2_xboole_0(X1,X2)
      | ~ m1_subset_1(X2,u1_struct_0(k3_yellow_1(X0)))
      | ~ m1_subset_1(X1,u1_struct_0(k3_yellow_1(X0))) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f2,axiom,(
    ! [X0] :
      ( l1_orders_2(k3_yellow_1(X0))
      & v1_orders_2(k3_yellow_1(X0)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f11,plain,(
    ! [X0] : l1_orders_2(k3_yellow_1(X0)) ),
    inference(pure_predicate_removal,[],[f2])).

fof(f44,plain,(
    ! [X0] : l1_orders_2(k3_yellow_1(X0)) ),
    inference(cnf_transformation,[],[f11])).

fof(f3,axiom,(
    ! [X0] :
      ( v11_waybel_1(k3_yellow_1(X0))
      & v1_orders_2(k3_yellow_1(X0)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f12,plain,(
    ! [X0] : v11_waybel_1(k3_yellow_1(X0)) ),
    inference(pure_predicate_removal,[],[f3])).

fof(f45,plain,(
    ! [X0] : v11_waybel_1(k3_yellow_1(X0)) ),
    inference(cnf_transformation,[],[f12])).

fof(f4,axiom,(
    ! [X0] :
      ( v5_orders_2(k3_yellow_1(X0))
      & v4_orders_2(k3_yellow_1(X0))
      & v3_orders_2(k3_yellow_1(X0))
      & v1_orders_2(k3_yellow_1(X0))
      & ~ v2_struct_0(k3_yellow_1(X0)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f10,plain,(
    ! [X0] :
      ( v5_orders_2(k3_yellow_1(X0))
      & v4_orders_2(k3_yellow_1(X0))
      & v3_orders_2(k3_yellow_1(X0))
      & ~ v2_struct_0(k3_yellow_1(X0)) ) ),
    inference(pure_predicate_removal,[],[f4])).

fof(f17,plain,(
    ! [X0] :
      ( v5_orders_2(k3_yellow_1(X0))
      & v3_orders_2(k3_yellow_1(X0))
      & ~ v2_struct_0(k3_yellow_1(X0)) ) ),
    inference(pure_predicate_removal,[],[f10])).

fof(f19,plain,(
    ! [X0] :
      ( v5_orders_2(k3_yellow_1(X0))
      & ~ v2_struct_0(k3_yellow_1(X0)) ) ),
    inference(pure_predicate_removal,[],[f17])).

fof(f47,plain,(
    ! [X0] : v5_orders_2(k3_yellow_1(X0)) ),
    inference(cnf_transformation,[],[f19])).

fof(f46,plain,(
    ! [X0] : ~ v2_struct_0(k3_yellow_1(X0)) ),
    inference(cnf_transformation,[],[f19])).

fof(f1,axiom,(
    ! [X0] :
      ( l1_orders_2(X0)
     => ( ( v11_waybel_1(X0)
          & ~ v2_struct_0(X0) )
       => ( v10_waybel_1(X0)
          & v2_waybel_1(X0)
          & v3_yellow_0(X0)
          & v2_lattice3(X0)
          & v1_lattice3(X0)
          & v5_orders_2(X0)
          & v4_orders_2(X0)
          & v3_orders_2(X0)
          & ~ v2_struct_0(X0) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f13,plain,(
    ! [X0] :
      ( l1_orders_2(X0)
     => ( ( v11_waybel_1(X0)
          & ~ v2_struct_0(X0) )
       => ( v2_waybel_1(X0)
          & v3_yellow_0(X0)
          & v2_lattice3(X0)
          & v1_lattice3(X0)
          & v5_orders_2(X0)
          & v4_orders_2(X0)
          & v3_orders_2(X0)
          & ~ v2_struct_0(X0) ) ) ) ),
    inference(pure_predicate_removal,[],[f1])).

fof(f14,plain,(
    ! [X0] :
      ( l1_orders_2(X0)
     => ( ( v11_waybel_1(X0)
          & ~ v2_struct_0(X0) )
       => ( v3_yellow_0(X0)
          & v2_lattice3(X0)
          & v1_lattice3(X0)
          & v5_orders_2(X0)
          & v4_orders_2(X0)
          & v3_orders_2(X0)
          & ~ v2_struct_0(X0) ) ) ) ),
    inference(pure_predicate_removal,[],[f13])).

fof(f15,plain,(
    ! [X0] :
      ( l1_orders_2(X0)
     => ( ( v11_waybel_1(X0)
          & ~ v2_struct_0(X0) )
       => ( v2_lattice3(X0)
          & v1_lattice3(X0)
          & v5_orders_2(X0)
          & v4_orders_2(X0)
          & v3_orders_2(X0)
          & ~ v2_struct_0(X0) ) ) ) ),
    inference(pure_predicate_removal,[],[f14])).

fof(f16,plain,(
    ! [X0] :
      ( l1_orders_2(X0)
     => ( ( v11_waybel_1(X0)
          & ~ v2_struct_0(X0) )
       => ( v2_lattice3(X0)
          & v5_orders_2(X0)
          & v4_orders_2(X0)
          & v3_orders_2(X0)
          & ~ v2_struct_0(X0) ) ) ) ),
    inference(pure_predicate_removal,[],[f15])).

fof(f18,plain,(
    ! [X0] :
      ( l1_orders_2(X0)
     => ( ( v11_waybel_1(X0)
          & ~ v2_struct_0(X0) )
       => ( v2_lattice3(X0)
          & v5_orders_2(X0)
          & v3_orders_2(X0)
          & ~ v2_struct_0(X0) ) ) ) ),
    inference(pure_predicate_removal,[],[f16])).

fof(f20,plain,(
    ! [X0] :
      ( l1_orders_2(X0)
     => ( ( v11_waybel_1(X0)
          & ~ v2_struct_0(X0) )
       => ( v2_lattice3(X0)
          & v5_orders_2(X0)
          & ~ v2_struct_0(X0) ) ) ) ),
    inference(pure_predicate_removal,[],[f18])).

fof(f21,plain,(
    ! [X0] :
      ( ( v2_lattice3(X0)
        & v5_orders_2(X0)
        & ~ v2_struct_0(X0) )
      | ~ v11_waybel_1(X0)
      | v2_struct_0(X0)
      | ~ l1_orders_2(X0) ) ),
    inference(ennf_transformation,[],[f20])).

fof(f22,plain,(
    ! [X0] :
      ( ( v2_lattice3(X0)
        & v5_orders_2(X0)
        & ~ v2_struct_0(X0) )
      | ~ v11_waybel_1(X0)
      | v2_struct_0(X0)
      | ~ l1_orders_2(X0) ) ),
    inference(flattening,[],[f21])).

fof(f43,plain,(
    ! [X0] :
      ( v2_lattice3(X0)
      | ~ v11_waybel_1(X0)
      | v2_struct_0(X0)
      | ~ l1_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f57,plain,(
    v13_waybel_0(sK3,k3_yellow_1(sK2)) ),
    inference(cnf_transformation,[],[f40])).

fof(f51,plain,(
    ! [X0,X1] :
      ( v2_waybel_0(X1,X0)
      | m1_subset_1(sK0(X0,X1),u1_struct_0(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ v13_waybel_0(X1,X0)
      | ~ l1_orders_2(X0)
      | ~ v2_lattice3(X0)
      | ~ v5_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f34])).

fof(f59,plain,(
    ! [X4,X5] :
      ( r2_hidden(k3_xboole_0(X4,X5),sK3)
      | ~ r2_hidden(X5,sK3)
      | ~ r2_hidden(X4,sK3)
      | v2_waybel_0(sK3,k3_yellow_1(sK2)) ) ),
    inference(cnf_transformation,[],[f40])).

fof(f54,plain,(
    ! [X0,X1] :
      ( v2_waybel_0(X1,X0)
      | r2_hidden(sK1(X0,X1),X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ v13_waybel_0(X1,X0)
      | ~ l1_orders_2(X0)
      | ~ v2_lattice3(X0)
      | ~ v5_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f34])).

fof(f53,plain,(
    ! [X0,X1] :
      ( v2_waybel_0(X1,X0)
      | r2_hidden(sK0(X0,X1),X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ v13_waybel_0(X1,X0)
      | ~ l1_orders_2(X0)
      | ~ v2_lattice3(X0)
      | ~ v5_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f34])).

fof(f55,plain,(
    ! [X0,X1] :
      ( v2_waybel_0(X1,X0)
      | ~ r2_hidden(k12_lattice3(X0,sK0(X0,X1),sK1(X0,X1)),X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ v13_waybel_0(X1,X0)
      | ~ l1_orders_2(X0)
      | ~ v2_lattice3(X0)
      | ~ v5_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f34])).

fof(f49,plain,(
    ! [X2,X0,X1] :
      ( k12_lattice3(k3_yellow_1(X0),X1,X2) = k3_xboole_0(X1,X2)
      | ~ m1_subset_1(X2,u1_struct_0(k3_yellow_1(X0)))
      | ~ m1_subset_1(X1,u1_struct_0(k3_yellow_1(X0))) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f61,plain,
    ( r2_hidden(sK5,sK3)
    | ~ v2_waybel_0(sK3,k3_yellow_1(sK2)) ),
    inference(cnf_transformation,[],[f40])).

fof(f60,plain,
    ( r2_hidden(sK4,sK3)
    | ~ v2_waybel_0(sK3,k3_yellow_1(sK2)) ),
    inference(cnf_transformation,[],[f40])).

fof(f7,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(X2))
        & r2_hidden(X0,X1) )
     => m1_subset_1(X0,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f26,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X0,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f27,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X0,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(flattening,[],[f26])).

fof(f56,plain,(
    ! [X2,X0,X1] :
      ( m1_subset_1(X0,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f50,plain,(
    ! [X4,X0,X5,X1] :
      ( r2_hidden(k12_lattice3(X0,X4,X5),X1)
      | ~ r2_hidden(X5,X1)
      | ~ r2_hidden(X4,X1)
      | ~ m1_subset_1(X5,u1_struct_0(X0))
      | ~ m1_subset_1(X4,u1_struct_0(X0))
      | ~ v2_waybel_0(X1,X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ v13_waybel_0(X1,X0)
      | ~ l1_orders_2(X0)
      | ~ v2_lattice3(X0)
      | ~ v5_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f34])).

fof(f62,plain,
    ( ~ r2_hidden(k3_xboole_0(sK4,sK5),sK3)
    | ~ v2_waybel_0(sK3,k3_yellow_1(sK2)) ),
    inference(cnf_transformation,[],[f40])).

cnf(c_20,negated_conjecture,
    ( m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(k3_yellow_1(sK2)))) ),
    inference(cnf_transformation,[],[f58])).

cnf(c_308,negated_conjecture,
    ( m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(k3_yellow_1(sK2)))) ),
    inference(subtyping,[status(esa)],[c_20])).

cnf(c_716,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(k3_yellow_1(sK2)))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_308])).

cnf(c_12,plain,
    ( ~ v13_waybel_0(X0,X1)
    | v2_waybel_0(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | m1_subset_1(sK1(X1,X0),u1_struct_0(X1))
    | ~ v5_orders_2(X1)
    | ~ l1_orders_2(X1)
    | ~ v2_lattice3(X1) ),
    inference(cnf_transformation,[],[f52])).

cnf(c_316,plain,
    ( ~ v13_waybel_0(X0_50,X0_51)
    | v2_waybel_0(X0_50,X0_51)
    | ~ m1_subset_1(X0_50,k1_zfmisc_1(u1_struct_0(X0_51)))
    | m1_subset_1(sK1(X0_51,X0_50),u1_struct_0(X0_51))
    | ~ v5_orders_2(X0_51)
    | ~ l1_orders_2(X0_51)
    | ~ v2_lattice3(X0_51) ),
    inference(subtyping,[status(esa)],[c_12])).

cnf(c_708,plain,
    ( v13_waybel_0(X0_50,X0_51) != iProver_top
    | v2_waybel_0(X0_50,X0_51) = iProver_top
    | m1_subset_1(X0_50,k1_zfmisc_1(u1_struct_0(X0_51))) != iProver_top
    | m1_subset_1(sK1(X0_51,X0_50),u1_struct_0(X0_51)) = iProver_top
    | v5_orders_2(X0_51) != iProver_top
    | l1_orders_2(X0_51) != iProver_top
    | v2_lattice3(X0_51) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_316])).

cnf(c_8,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(k3_yellow_1(X1)))
    | ~ m1_subset_1(X2,u1_struct_0(k3_yellow_1(X1)))
    | k13_lattice3(k3_yellow_1(X1),X2,X0) = k2_xboole_0(X2,X0) ),
    inference(cnf_transformation,[],[f48])).

cnf(c_320,plain,
    ( ~ m1_subset_1(X0_50,u1_struct_0(k3_yellow_1(X0_52)))
    | ~ m1_subset_1(X1_50,u1_struct_0(k3_yellow_1(X0_52)))
    | k13_lattice3(k3_yellow_1(X0_52),X1_50,X0_50) = k2_xboole_0(X1_50,X0_50) ),
    inference(subtyping,[status(esa)],[c_8])).

cnf(c_704,plain,
    ( k13_lattice3(k3_yellow_1(X0_52),X0_50,X1_50) = k2_xboole_0(X0_50,X1_50)
    | m1_subset_1(X0_50,u1_struct_0(k3_yellow_1(X0_52))) != iProver_top
    | m1_subset_1(X1_50,u1_struct_0(k3_yellow_1(X0_52))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_320])).

cnf(c_1610,plain,
    ( k13_lattice3(k3_yellow_1(X0_52),X0_50,sK1(k3_yellow_1(X0_52),X1_50)) = k2_xboole_0(X0_50,sK1(k3_yellow_1(X0_52),X1_50))
    | v13_waybel_0(X1_50,k3_yellow_1(X0_52)) != iProver_top
    | v2_waybel_0(X1_50,k3_yellow_1(X0_52)) = iProver_top
    | m1_subset_1(X1_50,k1_zfmisc_1(u1_struct_0(k3_yellow_1(X0_52)))) != iProver_top
    | m1_subset_1(X0_50,u1_struct_0(k3_yellow_1(X0_52))) != iProver_top
    | v5_orders_2(k3_yellow_1(X0_52)) != iProver_top
    | l1_orders_2(k3_yellow_1(X0_52)) != iProver_top
    | v2_lattice3(k3_yellow_1(X0_52)) != iProver_top ),
    inference(superposition,[status(thm)],[c_708,c_704])).

cnf(c_3,plain,
    ( l1_orders_2(k3_yellow_1(X0)) ),
    inference(cnf_transformation,[],[f44])).

cnf(c_325,plain,
    ( l1_orders_2(k3_yellow_1(X0_52)) ),
    inference(subtyping,[status(esa)],[c_3])).

cnf(c_354,plain,
    ( l1_orders_2(k3_yellow_1(X0_52)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_325])).

cnf(c_4,plain,
    ( v11_waybel_1(k3_yellow_1(X0)) ),
    inference(cnf_transformation,[],[f45])).

cnf(c_324,plain,
    ( v11_waybel_1(k3_yellow_1(X0_52)) ),
    inference(subtyping,[status(esa)],[c_4])).

cnf(c_357,plain,
    ( v11_waybel_1(k3_yellow_1(X0_52)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_324])).

cnf(c_5,plain,
    ( v5_orders_2(k3_yellow_1(X0)) ),
    inference(cnf_transformation,[],[f47])).

cnf(c_323,plain,
    ( v5_orders_2(k3_yellow_1(X0_52)) ),
    inference(subtyping,[status(esa)],[c_5])).

cnf(c_360,plain,
    ( v5_orders_2(k3_yellow_1(X0_52)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_323])).

cnf(c_6,plain,
    ( ~ v2_struct_0(k3_yellow_1(X0)) ),
    inference(cnf_transformation,[],[f46])).

cnf(c_322,plain,
    ( ~ v2_struct_0(k3_yellow_1(X0_52)) ),
    inference(subtyping,[status(esa)],[c_6])).

cnf(c_363,plain,
    ( v2_struct_0(k3_yellow_1(X0_52)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_322])).

cnf(c_0,plain,
    ( ~ l1_orders_2(X0)
    | v2_struct_0(X0)
    | ~ v11_waybel_1(X0)
    | v2_lattice3(X0) ),
    inference(cnf_transformation,[],[f43])).

cnf(c_327,plain,
    ( ~ l1_orders_2(X0_51)
    | v2_struct_0(X0_51)
    | ~ v11_waybel_1(X0_51)
    | v2_lattice3(X0_51) ),
    inference(subtyping,[status(esa)],[c_0])).

cnf(c_985,plain,
    ( ~ l1_orders_2(k3_yellow_1(X0_52))
    | v2_struct_0(k3_yellow_1(X0_52))
    | ~ v11_waybel_1(k3_yellow_1(X0_52))
    | v2_lattice3(k3_yellow_1(X0_52)) ),
    inference(instantiation,[status(thm)],[c_327])).

cnf(c_986,plain,
    ( l1_orders_2(k3_yellow_1(X0_52)) != iProver_top
    | v2_struct_0(k3_yellow_1(X0_52)) = iProver_top
    | v11_waybel_1(k3_yellow_1(X0_52)) != iProver_top
    | v2_lattice3(k3_yellow_1(X0_52)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_985])).

cnf(c_2337,plain,
    ( m1_subset_1(X0_50,u1_struct_0(k3_yellow_1(X0_52))) != iProver_top
    | m1_subset_1(X1_50,k1_zfmisc_1(u1_struct_0(k3_yellow_1(X0_52)))) != iProver_top
    | v2_waybel_0(X1_50,k3_yellow_1(X0_52)) = iProver_top
    | v13_waybel_0(X1_50,k3_yellow_1(X0_52)) != iProver_top
    | k13_lattice3(k3_yellow_1(X0_52),X0_50,sK1(k3_yellow_1(X0_52),X1_50)) = k2_xboole_0(X0_50,sK1(k3_yellow_1(X0_52),X1_50)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_1610,c_354,c_357,c_360,c_363,c_986])).

cnf(c_2338,plain,
    ( k13_lattice3(k3_yellow_1(X0_52),X0_50,sK1(k3_yellow_1(X0_52),X1_50)) = k2_xboole_0(X0_50,sK1(k3_yellow_1(X0_52),X1_50))
    | v13_waybel_0(X1_50,k3_yellow_1(X0_52)) != iProver_top
    | v2_waybel_0(X1_50,k3_yellow_1(X0_52)) = iProver_top
    | m1_subset_1(X1_50,k1_zfmisc_1(u1_struct_0(k3_yellow_1(X0_52)))) != iProver_top
    | m1_subset_1(X0_50,u1_struct_0(k3_yellow_1(X0_52))) != iProver_top ),
    inference(renaming,[status(thm)],[c_2337])).

cnf(c_2348,plain,
    ( k13_lattice3(k3_yellow_1(sK2),X0_50,sK1(k3_yellow_1(sK2),sK3)) = k2_xboole_0(X0_50,sK1(k3_yellow_1(sK2),sK3))
    | v13_waybel_0(sK3,k3_yellow_1(sK2)) != iProver_top
    | v2_waybel_0(sK3,k3_yellow_1(sK2)) = iProver_top
    | m1_subset_1(X0_50,u1_struct_0(k3_yellow_1(sK2))) != iProver_top ),
    inference(superposition,[status(thm)],[c_716,c_2338])).

cnf(c_21,negated_conjecture,
    ( v13_waybel_0(sK3,k3_yellow_1(sK2)) ),
    inference(cnf_transformation,[],[f57])).

cnf(c_22,plain,
    ( v13_waybel_0(sK3,k3_yellow_1(sK2)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_21])).

cnf(c_2454,plain,
    ( k13_lattice3(k3_yellow_1(sK2),X0_50,sK1(k3_yellow_1(sK2),sK3)) = k2_xboole_0(X0_50,sK1(k3_yellow_1(sK2),sK3))
    | v2_waybel_0(sK3,k3_yellow_1(sK2)) = iProver_top
    | m1_subset_1(X0_50,u1_struct_0(k3_yellow_1(sK2))) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_2348,c_22])).

cnf(c_2464,plain,
    ( k13_lattice3(k3_yellow_1(sK2),sK1(k3_yellow_1(sK2),X0_50),sK1(k3_yellow_1(sK2),sK3)) = k2_xboole_0(sK1(k3_yellow_1(sK2),X0_50),sK1(k3_yellow_1(sK2),sK3))
    | v13_waybel_0(X0_50,k3_yellow_1(sK2)) != iProver_top
    | v2_waybel_0(X0_50,k3_yellow_1(sK2)) = iProver_top
    | v2_waybel_0(sK3,k3_yellow_1(sK2)) = iProver_top
    | m1_subset_1(X0_50,k1_zfmisc_1(u1_struct_0(k3_yellow_1(sK2)))) != iProver_top
    | v5_orders_2(k3_yellow_1(sK2)) != iProver_top
    | l1_orders_2(k3_yellow_1(sK2)) != iProver_top
    | v2_lattice3(k3_yellow_1(sK2)) != iProver_top ),
    inference(superposition,[status(thm)],[c_708,c_2454])).

cnf(c_356,plain,
    ( l1_orders_2(k3_yellow_1(sK2)) = iProver_top ),
    inference(instantiation,[status(thm)],[c_354])).

cnf(c_359,plain,
    ( v11_waybel_1(k3_yellow_1(sK2)) = iProver_top ),
    inference(instantiation,[status(thm)],[c_357])).

cnf(c_362,plain,
    ( v5_orders_2(k3_yellow_1(sK2)) = iProver_top ),
    inference(instantiation,[status(thm)],[c_360])).

cnf(c_365,plain,
    ( v2_struct_0(k3_yellow_1(sK2)) != iProver_top ),
    inference(instantiation,[status(thm)],[c_363])).

cnf(c_988,plain,
    ( l1_orders_2(k3_yellow_1(sK2)) != iProver_top
    | v2_struct_0(k3_yellow_1(sK2)) = iProver_top
    | v11_waybel_1(k3_yellow_1(sK2)) != iProver_top
    | v2_lattice3(k3_yellow_1(sK2)) = iProver_top ),
    inference(instantiation,[status(thm)],[c_986])).

cnf(c_10648,plain,
    ( m1_subset_1(X0_50,k1_zfmisc_1(u1_struct_0(k3_yellow_1(sK2)))) != iProver_top
    | v2_waybel_0(sK3,k3_yellow_1(sK2)) = iProver_top
    | v2_waybel_0(X0_50,k3_yellow_1(sK2)) = iProver_top
    | v13_waybel_0(X0_50,k3_yellow_1(sK2)) != iProver_top
    | k13_lattice3(k3_yellow_1(sK2),sK1(k3_yellow_1(sK2),X0_50),sK1(k3_yellow_1(sK2),sK3)) = k2_xboole_0(sK1(k3_yellow_1(sK2),X0_50),sK1(k3_yellow_1(sK2),sK3)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_2464,c_356,c_359,c_362,c_365,c_988])).

cnf(c_10649,plain,
    ( k13_lattice3(k3_yellow_1(sK2),sK1(k3_yellow_1(sK2),X0_50),sK1(k3_yellow_1(sK2),sK3)) = k2_xboole_0(sK1(k3_yellow_1(sK2),X0_50),sK1(k3_yellow_1(sK2),sK3))
    | v13_waybel_0(X0_50,k3_yellow_1(sK2)) != iProver_top
    | v2_waybel_0(X0_50,k3_yellow_1(sK2)) = iProver_top
    | v2_waybel_0(sK3,k3_yellow_1(sK2)) = iProver_top
    | m1_subset_1(X0_50,k1_zfmisc_1(u1_struct_0(k3_yellow_1(sK2)))) != iProver_top ),
    inference(renaming,[status(thm)],[c_10648])).

cnf(c_10658,plain,
    ( k13_lattice3(k3_yellow_1(sK2),sK1(k3_yellow_1(sK2),sK3),sK1(k3_yellow_1(sK2),sK3)) = k2_xboole_0(sK1(k3_yellow_1(sK2),sK3),sK1(k3_yellow_1(sK2),sK3))
    | v13_waybel_0(sK3,k3_yellow_1(sK2)) != iProver_top
    | v2_waybel_0(sK3,k3_yellow_1(sK2)) = iProver_top ),
    inference(superposition,[status(thm)],[c_716,c_10649])).

cnf(c_23,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(k3_yellow_1(sK2)))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_20])).

cnf(c_13,plain,
    ( ~ v13_waybel_0(X0,X1)
    | v2_waybel_0(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | m1_subset_1(sK0(X1,X0),u1_struct_0(X1))
    | ~ v5_orders_2(X1)
    | ~ l1_orders_2(X1)
    | ~ v2_lattice3(X1) ),
    inference(cnf_transformation,[],[f51])).

cnf(c_315,plain,
    ( ~ v13_waybel_0(X0_50,X0_51)
    | v2_waybel_0(X0_50,X0_51)
    | ~ m1_subset_1(X0_50,k1_zfmisc_1(u1_struct_0(X0_51)))
    | m1_subset_1(sK0(X0_51,X0_50),u1_struct_0(X0_51))
    | ~ v5_orders_2(X0_51)
    | ~ l1_orders_2(X0_51)
    | ~ v2_lattice3(X0_51) ),
    inference(subtyping,[status(esa)],[c_13])).

cnf(c_1029,plain,
    ( ~ v13_waybel_0(X0_50,k3_yellow_1(X0_52))
    | v2_waybel_0(X0_50,k3_yellow_1(X0_52))
    | ~ m1_subset_1(X0_50,k1_zfmisc_1(u1_struct_0(k3_yellow_1(X0_52))))
    | m1_subset_1(sK0(k3_yellow_1(X0_52),X0_50),u1_struct_0(k3_yellow_1(X0_52)))
    | ~ v5_orders_2(k3_yellow_1(X0_52))
    | ~ l1_orders_2(k3_yellow_1(X0_52))
    | ~ v2_lattice3(k3_yellow_1(X0_52)) ),
    inference(instantiation,[status(thm)],[c_315])).

cnf(c_1030,plain,
    ( v13_waybel_0(X0_50,k3_yellow_1(X0_52)) != iProver_top
    | v2_waybel_0(X0_50,k3_yellow_1(X0_52)) = iProver_top
    | m1_subset_1(X0_50,k1_zfmisc_1(u1_struct_0(k3_yellow_1(X0_52)))) != iProver_top
    | m1_subset_1(sK0(k3_yellow_1(X0_52),X0_50),u1_struct_0(k3_yellow_1(X0_52))) = iProver_top
    | v5_orders_2(k3_yellow_1(X0_52)) != iProver_top
    | l1_orders_2(k3_yellow_1(X0_52)) != iProver_top
    | v2_lattice3(k3_yellow_1(X0_52)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1029])).

cnf(c_1032,plain,
    ( v13_waybel_0(sK3,k3_yellow_1(sK2)) != iProver_top
    | v2_waybel_0(sK3,k3_yellow_1(sK2)) = iProver_top
    | m1_subset_1(sK0(k3_yellow_1(sK2),sK3),u1_struct_0(k3_yellow_1(sK2))) = iProver_top
    | m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(k3_yellow_1(sK2)))) != iProver_top
    | v5_orders_2(k3_yellow_1(sK2)) != iProver_top
    | l1_orders_2(k3_yellow_1(sK2)) != iProver_top
    | v2_lattice3(k3_yellow_1(sK2)) != iProver_top ),
    inference(instantiation,[status(thm)],[c_1030])).

cnf(c_1028,plain,
    ( ~ v13_waybel_0(X0_50,k3_yellow_1(X0_52))
    | v2_waybel_0(X0_50,k3_yellow_1(X0_52))
    | ~ m1_subset_1(X0_50,k1_zfmisc_1(u1_struct_0(k3_yellow_1(X0_52))))
    | m1_subset_1(sK1(k3_yellow_1(X0_52),X0_50),u1_struct_0(k3_yellow_1(X0_52)))
    | ~ v5_orders_2(k3_yellow_1(X0_52))
    | ~ l1_orders_2(k3_yellow_1(X0_52))
    | ~ v2_lattice3(k3_yellow_1(X0_52)) ),
    inference(instantiation,[status(thm)],[c_316])).

cnf(c_1034,plain,
    ( v13_waybel_0(X0_50,k3_yellow_1(X0_52)) != iProver_top
    | v2_waybel_0(X0_50,k3_yellow_1(X0_52)) = iProver_top
    | m1_subset_1(X0_50,k1_zfmisc_1(u1_struct_0(k3_yellow_1(X0_52)))) != iProver_top
    | m1_subset_1(sK1(k3_yellow_1(X0_52),X0_50),u1_struct_0(k3_yellow_1(X0_52))) = iProver_top
    | v5_orders_2(k3_yellow_1(X0_52)) != iProver_top
    | l1_orders_2(k3_yellow_1(X0_52)) != iProver_top
    | v2_lattice3(k3_yellow_1(X0_52)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1028])).

cnf(c_1036,plain,
    ( v13_waybel_0(sK3,k3_yellow_1(sK2)) != iProver_top
    | v2_waybel_0(sK3,k3_yellow_1(sK2)) = iProver_top
    | m1_subset_1(sK1(k3_yellow_1(sK2),sK3),u1_struct_0(k3_yellow_1(sK2))) = iProver_top
    | m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(k3_yellow_1(sK2)))) != iProver_top
    | v5_orders_2(k3_yellow_1(sK2)) != iProver_top
    | l1_orders_2(k3_yellow_1(sK2)) != iProver_top
    | v2_lattice3(k3_yellow_1(sK2)) != iProver_top ),
    inference(instantiation,[status(thm)],[c_1034])).

cnf(c_19,negated_conjecture,
    ( ~ r2_hidden(X0,sK3)
    | ~ r2_hidden(X1,sK3)
    | r2_hidden(k3_xboole_0(X1,X0),sK3)
    | v2_waybel_0(sK3,k3_yellow_1(sK2)) ),
    inference(cnf_transformation,[],[f59])).

cnf(c_309,negated_conjecture,
    ( ~ r2_hidden(X0_50,sK3)
    | ~ r2_hidden(X1_50,sK3)
    | r2_hidden(k3_xboole_0(X1_50,X0_50),sK3)
    | v2_waybel_0(sK3,k3_yellow_1(sK2)) ),
    inference(subtyping,[status(esa)],[c_19])).

cnf(c_1075,plain,
    ( ~ r2_hidden(X0_50,sK3)
    | ~ r2_hidden(sK0(k3_yellow_1(X0_52),sK3),sK3)
    | r2_hidden(k3_xboole_0(sK0(k3_yellow_1(X0_52),sK3),X0_50),sK3)
    | v2_waybel_0(sK3,k3_yellow_1(sK2)) ),
    inference(instantiation,[status(thm)],[c_309])).

cnf(c_1377,plain,
    ( ~ r2_hidden(sK1(k3_yellow_1(X0_52),sK3),sK3)
    | ~ r2_hidden(sK0(k3_yellow_1(X1_52),sK3),sK3)
    | r2_hidden(k3_xboole_0(sK0(k3_yellow_1(X1_52),sK3),sK1(k3_yellow_1(X0_52),sK3)),sK3)
    | v2_waybel_0(sK3,k3_yellow_1(sK2)) ),
    inference(instantiation,[status(thm)],[c_1075])).

cnf(c_1378,plain,
    ( r2_hidden(sK1(k3_yellow_1(X0_52),sK3),sK3) != iProver_top
    | r2_hidden(sK0(k3_yellow_1(X1_52),sK3),sK3) != iProver_top
    | r2_hidden(k3_xboole_0(sK0(k3_yellow_1(X1_52),sK3),sK1(k3_yellow_1(X0_52),sK3)),sK3) = iProver_top
    | v2_waybel_0(sK3,k3_yellow_1(sK2)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1377])).

cnf(c_1380,plain,
    ( r2_hidden(sK1(k3_yellow_1(sK2),sK3),sK3) != iProver_top
    | r2_hidden(sK0(k3_yellow_1(sK2),sK3),sK3) != iProver_top
    | r2_hidden(k3_xboole_0(sK0(k3_yellow_1(sK2),sK3),sK1(k3_yellow_1(sK2),sK3)),sK3) = iProver_top
    | v2_waybel_0(sK3,k3_yellow_1(sK2)) = iProver_top ),
    inference(instantiation,[status(thm)],[c_1378])).

cnf(c_10,plain,
    ( ~ v13_waybel_0(X0,X1)
    | r2_hidden(sK1(X1,X0),X0)
    | v2_waybel_0(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ v5_orders_2(X1)
    | ~ l1_orders_2(X1)
    | ~ v2_lattice3(X1) ),
    inference(cnf_transformation,[],[f54])).

cnf(c_318,plain,
    ( ~ v13_waybel_0(X0_50,X0_51)
    | r2_hidden(sK1(X0_51,X0_50),X0_50)
    | v2_waybel_0(X0_50,X0_51)
    | ~ m1_subset_1(X0_50,k1_zfmisc_1(u1_struct_0(X0_51)))
    | ~ v5_orders_2(X0_51)
    | ~ l1_orders_2(X0_51)
    | ~ v2_lattice3(X0_51) ),
    inference(subtyping,[status(esa)],[c_10])).

cnf(c_706,plain,
    ( v13_waybel_0(X0_50,X0_51) != iProver_top
    | r2_hidden(sK1(X0_51,X0_50),X0_50) = iProver_top
    | v2_waybel_0(X0_50,X0_51) = iProver_top
    | m1_subset_1(X0_50,k1_zfmisc_1(u1_struct_0(X0_51))) != iProver_top
    | v5_orders_2(X0_51) != iProver_top
    | l1_orders_2(X0_51) != iProver_top
    | v2_lattice3(X0_51) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_318])).

cnf(c_1486,plain,
    ( v13_waybel_0(sK3,k3_yellow_1(sK2)) != iProver_top
    | r2_hidden(sK1(k3_yellow_1(sK2),sK3),sK3) = iProver_top
    | v2_waybel_0(sK3,k3_yellow_1(sK2)) = iProver_top
    | v5_orders_2(k3_yellow_1(sK2)) != iProver_top
    | l1_orders_2(k3_yellow_1(sK2)) != iProver_top
    | v2_lattice3(k3_yellow_1(sK2)) != iProver_top ),
    inference(superposition,[status(thm)],[c_716,c_706])).

cnf(c_11,plain,
    ( ~ v13_waybel_0(X0,X1)
    | r2_hidden(sK0(X1,X0),X0)
    | v2_waybel_0(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ v5_orders_2(X1)
    | ~ l1_orders_2(X1)
    | ~ v2_lattice3(X1) ),
    inference(cnf_transformation,[],[f53])).

cnf(c_317,plain,
    ( ~ v13_waybel_0(X0_50,X0_51)
    | r2_hidden(sK0(X0_51,X0_50),X0_50)
    | v2_waybel_0(X0_50,X0_51)
    | ~ m1_subset_1(X0_50,k1_zfmisc_1(u1_struct_0(X0_51)))
    | ~ v5_orders_2(X0_51)
    | ~ l1_orders_2(X0_51)
    | ~ v2_lattice3(X0_51) ),
    inference(subtyping,[status(esa)],[c_11])).

cnf(c_707,plain,
    ( v13_waybel_0(X0_50,X0_51) != iProver_top
    | r2_hidden(sK0(X0_51,X0_50),X0_50) = iProver_top
    | v2_waybel_0(X0_50,X0_51) = iProver_top
    | m1_subset_1(X0_50,k1_zfmisc_1(u1_struct_0(X0_51))) != iProver_top
    | v5_orders_2(X0_51) != iProver_top
    | l1_orders_2(X0_51) != iProver_top
    | v2_lattice3(X0_51) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_317])).

cnf(c_1496,plain,
    ( v13_waybel_0(sK3,k3_yellow_1(sK2)) != iProver_top
    | r2_hidden(sK0(k3_yellow_1(sK2),sK3),sK3) = iProver_top
    | v2_waybel_0(sK3,k3_yellow_1(sK2)) = iProver_top
    | v5_orders_2(k3_yellow_1(sK2)) != iProver_top
    | l1_orders_2(k3_yellow_1(sK2)) != iProver_top
    | v2_lattice3(k3_yellow_1(sK2)) != iProver_top ),
    inference(superposition,[status(thm)],[c_716,c_707])).

cnf(c_9,plain,
    ( ~ v13_waybel_0(X0,X1)
    | ~ r2_hidden(k12_lattice3(X1,sK0(X1,X0),sK1(X1,X0)),X0)
    | v2_waybel_0(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ v5_orders_2(X1)
    | ~ l1_orders_2(X1)
    | ~ v2_lattice3(X1) ),
    inference(cnf_transformation,[],[f55])).

cnf(c_319,plain,
    ( ~ v13_waybel_0(X0_50,X0_51)
    | ~ r2_hidden(k12_lattice3(X0_51,sK0(X0_51,X0_50),sK1(X0_51,X0_50)),X0_50)
    | v2_waybel_0(X0_50,X0_51)
    | ~ m1_subset_1(X0_50,k1_zfmisc_1(u1_struct_0(X0_51)))
    | ~ v5_orders_2(X0_51)
    | ~ l1_orders_2(X0_51)
    | ~ v2_lattice3(X0_51) ),
    inference(subtyping,[status(esa)],[c_9])).

cnf(c_7,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(k3_yellow_1(X1)))
    | ~ m1_subset_1(X2,u1_struct_0(k3_yellow_1(X1)))
    | k12_lattice3(k3_yellow_1(X1),X2,X0) = k3_xboole_0(X2,X0) ),
    inference(cnf_transformation,[],[f49])).

cnf(c_321,plain,
    ( ~ m1_subset_1(X0_50,u1_struct_0(k3_yellow_1(X0_52)))
    | ~ m1_subset_1(X1_50,u1_struct_0(k3_yellow_1(X0_52)))
    | k12_lattice3(k3_yellow_1(X0_52),X1_50,X0_50) = k3_xboole_0(X1_50,X0_50) ),
    inference(subtyping,[status(esa)],[c_7])).

cnf(c_337,plain,
    ( ~ r2_hidden(X0_50,X1_50)
    | r2_hidden(X2_50,X3_50)
    | X2_50 != X0_50
    | X3_50 != X1_50 ),
    theory(equality)).

cnf(c_329,plain,
    ( X0_50 = X0_50 ),
    theory(equality)).

cnf(c_2727,plain,
    ( ~ r2_hidden(X0_50,X1_50)
    | r2_hidden(X2_50,X1_50)
    | X2_50 != X0_50 ),
    inference(resolution,[status(thm)],[c_337,c_329])).

cnf(c_2933,plain,
    ( r2_hidden(k12_lattice3(k3_yellow_1(X0_52),X0_50,X1_50),X2_50)
    | ~ r2_hidden(k3_xboole_0(X0_50,X1_50),X2_50)
    | ~ m1_subset_1(X0_50,u1_struct_0(k3_yellow_1(X0_52)))
    | ~ m1_subset_1(X1_50,u1_struct_0(k3_yellow_1(X0_52))) ),
    inference(resolution,[status(thm)],[c_321,c_2727])).

cnf(c_10703,plain,
    ( ~ v13_waybel_0(X0_50,k3_yellow_1(X0_52))
    | ~ r2_hidden(k3_xboole_0(sK0(k3_yellow_1(X0_52),X0_50),sK1(k3_yellow_1(X0_52),X0_50)),X0_50)
    | v2_waybel_0(X0_50,k3_yellow_1(X0_52))
    | ~ m1_subset_1(X0_50,k1_zfmisc_1(u1_struct_0(k3_yellow_1(X0_52))))
    | ~ m1_subset_1(sK1(k3_yellow_1(X0_52),X0_50),u1_struct_0(k3_yellow_1(X0_52)))
    | ~ m1_subset_1(sK0(k3_yellow_1(X0_52),X0_50),u1_struct_0(k3_yellow_1(X0_52)))
    | ~ v5_orders_2(k3_yellow_1(X0_52))
    | ~ l1_orders_2(k3_yellow_1(X0_52))
    | ~ v2_lattice3(k3_yellow_1(X0_52)) ),
    inference(resolution,[status(thm)],[c_319,c_2933])).

cnf(c_10704,plain,
    ( v13_waybel_0(X0_50,k3_yellow_1(X0_52)) != iProver_top
    | r2_hidden(k3_xboole_0(sK0(k3_yellow_1(X0_52),X0_50),sK1(k3_yellow_1(X0_52),X0_50)),X0_50) != iProver_top
    | v2_waybel_0(X0_50,k3_yellow_1(X0_52)) = iProver_top
    | m1_subset_1(X0_50,k1_zfmisc_1(u1_struct_0(k3_yellow_1(X0_52)))) != iProver_top
    | m1_subset_1(sK1(k3_yellow_1(X0_52),X0_50),u1_struct_0(k3_yellow_1(X0_52))) != iProver_top
    | m1_subset_1(sK0(k3_yellow_1(X0_52),X0_50),u1_struct_0(k3_yellow_1(X0_52))) != iProver_top
    | v5_orders_2(k3_yellow_1(X0_52)) != iProver_top
    | l1_orders_2(k3_yellow_1(X0_52)) != iProver_top
    | v2_lattice3(k3_yellow_1(X0_52)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_10703])).

cnf(c_10706,plain,
    ( v13_waybel_0(sK3,k3_yellow_1(sK2)) != iProver_top
    | r2_hidden(k3_xboole_0(sK0(k3_yellow_1(sK2),sK3),sK1(k3_yellow_1(sK2),sK3)),sK3) != iProver_top
    | v2_waybel_0(sK3,k3_yellow_1(sK2)) = iProver_top
    | m1_subset_1(sK1(k3_yellow_1(sK2),sK3),u1_struct_0(k3_yellow_1(sK2))) != iProver_top
    | m1_subset_1(sK0(k3_yellow_1(sK2),sK3),u1_struct_0(k3_yellow_1(sK2))) != iProver_top
    | m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(k3_yellow_1(sK2)))) != iProver_top
    | v5_orders_2(k3_yellow_1(sK2)) != iProver_top
    | l1_orders_2(k3_yellow_1(sK2)) != iProver_top
    | v2_lattice3(k3_yellow_1(sK2)) != iProver_top ),
    inference(instantiation,[status(thm)],[c_10704])).

cnf(c_10715,plain,
    ( v2_waybel_0(sK3,k3_yellow_1(sK2)) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_10658,c_22,c_23,c_356,c_359,c_362,c_365,c_988,c_1032,c_1036,c_1380,c_1486,c_1496,c_10706])).

cnf(c_17,negated_conjecture,
    ( r2_hidden(sK5,sK3)
    | ~ v2_waybel_0(sK3,k3_yellow_1(sK2)) ),
    inference(cnf_transformation,[],[f61])).

cnf(c_311,negated_conjecture,
    ( r2_hidden(sK5,sK3)
    | ~ v2_waybel_0(sK3,k3_yellow_1(sK2)) ),
    inference(subtyping,[status(esa)],[c_17])).

cnf(c_713,plain,
    ( r2_hidden(sK5,sK3) = iProver_top
    | v2_waybel_0(sK3,k3_yellow_1(sK2)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_311])).

cnf(c_10721,plain,
    ( r2_hidden(sK5,sK3) = iProver_top ),
    inference(superposition,[status(thm)],[c_10715,c_713])).

cnf(c_18,negated_conjecture,
    ( r2_hidden(sK4,sK3)
    | ~ v2_waybel_0(sK3,k3_yellow_1(sK2)) ),
    inference(cnf_transformation,[],[f60])).

cnf(c_310,negated_conjecture,
    ( r2_hidden(sK4,sK3)
    | ~ v2_waybel_0(sK3,k3_yellow_1(sK2)) ),
    inference(subtyping,[status(esa)],[c_18])).

cnf(c_714,plain,
    ( r2_hidden(sK4,sK3) = iProver_top
    | v2_waybel_0(sK3,k3_yellow_1(sK2)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_310])).

cnf(c_10720,plain,
    ( r2_hidden(sK4,sK3) = iProver_top ),
    inference(superposition,[status(thm)],[c_10715,c_714])).

cnf(c_15,plain,
    ( ~ r2_hidden(X0,X1)
    | m1_subset_1(X0,X2)
    | ~ m1_subset_1(X1,k1_zfmisc_1(X2)) ),
    inference(cnf_transformation,[],[f56])).

cnf(c_313,plain,
    ( ~ r2_hidden(X0_50,X1_50)
    | m1_subset_1(X0_50,X0_53)
    | ~ m1_subset_1(X1_50,k1_zfmisc_1(X0_53)) ),
    inference(subtyping,[status(esa)],[c_15])).

cnf(c_711,plain,
    ( r2_hidden(X0_50,X1_50) != iProver_top
    | m1_subset_1(X0_50,X0_53) = iProver_top
    | m1_subset_1(X1_50,k1_zfmisc_1(X0_53)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_313])).

cnf(c_1267,plain,
    ( r2_hidden(X0_50,sK3) != iProver_top
    | m1_subset_1(X0_50,u1_struct_0(k3_yellow_1(sK2))) = iProver_top ),
    inference(superposition,[status(thm)],[c_716,c_711])).

cnf(c_703,plain,
    ( k12_lattice3(k3_yellow_1(X0_52),X0_50,X1_50) = k3_xboole_0(X0_50,X1_50)
    | m1_subset_1(X0_50,u1_struct_0(k3_yellow_1(X0_52))) != iProver_top
    | m1_subset_1(X1_50,u1_struct_0(k3_yellow_1(X0_52))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_321])).

cnf(c_1925,plain,
    ( k12_lattice3(k3_yellow_1(sK2),X0_50,X1_50) = k3_xboole_0(X0_50,X1_50)
    | r2_hidden(X1_50,sK3) != iProver_top
    | m1_subset_1(X0_50,u1_struct_0(k3_yellow_1(sK2))) != iProver_top ),
    inference(superposition,[status(thm)],[c_1267,c_703])).

cnf(c_2190,plain,
    ( k12_lattice3(k3_yellow_1(sK2),X0_50,X1_50) = k3_xboole_0(X0_50,X1_50)
    | r2_hidden(X0_50,sK3) != iProver_top
    | r2_hidden(X1_50,sK3) != iProver_top ),
    inference(superposition,[status(thm)],[c_1267,c_1925])).

cnf(c_10743,plain,
    ( k12_lattice3(k3_yellow_1(sK2),sK4,X0_50) = k3_xboole_0(sK4,X0_50)
    | r2_hidden(X0_50,sK3) != iProver_top ),
    inference(superposition,[status(thm)],[c_10720,c_2190])).

cnf(c_11035,plain,
    ( k12_lattice3(k3_yellow_1(sK2),sK4,sK5) = k3_xboole_0(sK4,sK5) ),
    inference(superposition,[status(thm)],[c_10721,c_10743])).

cnf(c_14,plain,
    ( ~ v13_waybel_0(X0,X1)
    | ~ r2_hidden(X2,X0)
    | ~ r2_hidden(X3,X0)
    | r2_hidden(k12_lattice3(X1,X3,X2),X0)
    | ~ v2_waybel_0(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ m1_subset_1(X3,u1_struct_0(X1))
    | ~ v5_orders_2(X1)
    | ~ l1_orders_2(X1)
    | ~ v2_lattice3(X1) ),
    inference(cnf_transformation,[],[f50])).

cnf(c_314,plain,
    ( ~ v13_waybel_0(X0_50,X0_51)
    | ~ r2_hidden(X1_50,X0_50)
    | ~ r2_hidden(X2_50,X0_50)
    | r2_hidden(k12_lattice3(X0_51,X1_50,X2_50),X0_50)
    | ~ v2_waybel_0(X0_50,X0_51)
    | ~ m1_subset_1(X0_50,k1_zfmisc_1(u1_struct_0(X0_51)))
    | ~ m1_subset_1(X2_50,u1_struct_0(X0_51))
    | ~ m1_subset_1(X1_50,u1_struct_0(X0_51))
    | ~ v5_orders_2(X0_51)
    | ~ l1_orders_2(X0_51)
    | ~ v2_lattice3(X0_51) ),
    inference(subtyping,[status(esa)],[c_14])).

cnf(c_710,plain,
    ( v13_waybel_0(X0_50,X0_51) != iProver_top
    | r2_hidden(X1_50,X0_50) != iProver_top
    | r2_hidden(X2_50,X0_50) != iProver_top
    | r2_hidden(k12_lattice3(X0_51,X2_50,X1_50),X0_50) = iProver_top
    | v2_waybel_0(X0_50,X0_51) != iProver_top
    | m1_subset_1(X0_50,k1_zfmisc_1(u1_struct_0(X0_51))) != iProver_top
    | m1_subset_1(X1_50,u1_struct_0(X0_51)) != iProver_top
    | m1_subset_1(X2_50,u1_struct_0(X0_51)) != iProver_top
    | v5_orders_2(X0_51) != iProver_top
    | l1_orders_2(X0_51) != iProver_top
    | v2_lattice3(X0_51) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_314])).

cnf(c_865,plain,
    ( v13_waybel_0(X0_50,X0_51) != iProver_top
    | r2_hidden(X1_50,X0_50) != iProver_top
    | r2_hidden(X2_50,X0_50) != iProver_top
    | r2_hidden(k12_lattice3(X0_51,X1_50,X2_50),X0_50) = iProver_top
    | v2_waybel_0(X0_50,X0_51) != iProver_top
    | m1_subset_1(X0_50,k1_zfmisc_1(u1_struct_0(X0_51))) != iProver_top
    | v5_orders_2(X0_51) != iProver_top
    | l1_orders_2(X0_51) != iProver_top
    | v2_lattice3(X0_51) != iProver_top ),
    inference(forward_subsumption_resolution,[status(thm)],[c_710,c_711,c_711])).

cnf(c_11130,plain,
    ( v13_waybel_0(X0_50,k3_yellow_1(sK2)) != iProver_top
    | r2_hidden(k3_xboole_0(sK4,sK5),X0_50) = iProver_top
    | r2_hidden(sK5,X0_50) != iProver_top
    | r2_hidden(sK4,X0_50) != iProver_top
    | v2_waybel_0(X0_50,k3_yellow_1(sK2)) != iProver_top
    | m1_subset_1(X0_50,k1_zfmisc_1(u1_struct_0(k3_yellow_1(sK2)))) != iProver_top
    | v5_orders_2(k3_yellow_1(sK2)) != iProver_top
    | l1_orders_2(k3_yellow_1(sK2)) != iProver_top
    | v2_lattice3(k3_yellow_1(sK2)) != iProver_top ),
    inference(superposition,[status(thm)],[c_11035,c_865])).

cnf(c_11132,plain,
    ( v13_waybel_0(sK3,k3_yellow_1(sK2)) != iProver_top
    | r2_hidden(k3_xboole_0(sK4,sK5),sK3) = iProver_top
    | r2_hidden(sK5,sK3) != iProver_top
    | r2_hidden(sK4,sK3) != iProver_top
    | v2_waybel_0(sK3,k3_yellow_1(sK2)) != iProver_top
    | m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(k3_yellow_1(sK2)))) != iProver_top
    | v5_orders_2(k3_yellow_1(sK2)) != iProver_top
    | l1_orders_2(k3_yellow_1(sK2)) != iProver_top
    | v2_lattice3(k3_yellow_1(sK2)) != iProver_top ),
    inference(instantiation,[status(thm)],[c_11130])).

cnf(c_16,negated_conjecture,
    ( ~ r2_hidden(k3_xboole_0(sK4,sK5),sK3)
    | ~ v2_waybel_0(sK3,k3_yellow_1(sK2)) ),
    inference(cnf_transformation,[],[f62])).

cnf(c_29,plain,
    ( r2_hidden(k3_xboole_0(sK4,sK5),sK3) != iProver_top
    | v2_waybel_0(sK3,k3_yellow_1(sK2)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_16])).

cnf(c_28,plain,
    ( r2_hidden(sK5,sK3) = iProver_top
    | v2_waybel_0(sK3,k3_yellow_1(sK2)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_17])).

cnf(c_27,plain,
    ( r2_hidden(sK4,sK3) = iProver_top
    | v2_waybel_0(sK3,k3_yellow_1(sK2)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_18])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_11132,c_10715,c_988,c_365,c_362,c_359,c_356,c_29,c_28,c_27,c_23,c_22])).


%------------------------------------------------------------------------------
