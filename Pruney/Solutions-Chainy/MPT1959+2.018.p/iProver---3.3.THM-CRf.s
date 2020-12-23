%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n003.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:28:27 EST 2020

% Result     : Theorem 3.78s
% Output     : CNFRefutation 3.78s
% Verified   : 
% Statistics : Number of formulae       :  259 (4417 expanded)
%              Number of clauses        :  159 (1080 expanded)
%              Number of leaves         :   31 ( 870 expanded)
%              Depth                    :   28
%              Number of atoms          : 1058 (33256 expanded)
%              Number of equality atoms :  275 (1356 expanded)
%              Maximal formula depth    :   14 (   5 average)
%              Maximal clause size      :   22 (   3 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f4,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(X0))
         => ( ! [X3] :
                ( m1_subset_1(X3,X0)
               => ( r2_hidden(X3,X1)
                <=> r2_hidden(X3,X2) ) )
           => X1 = X2 ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f22,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( X1 = X2
          | ? [X3] :
              ( ( r2_hidden(X3,X1)
              <~> r2_hidden(X3,X2) )
              & m1_subset_1(X3,X0) )
          | ~ m1_subset_1(X2,k1_zfmisc_1(X0)) )
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f23,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( X1 = X2
          | ? [X3] :
              ( ( r2_hidden(X3,X1)
              <~> r2_hidden(X3,X2) )
              & m1_subset_1(X3,X0) )
          | ~ m1_subset_1(X2,k1_zfmisc_1(X0)) )
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(flattening,[],[f22])).

fof(f45,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( X1 = X2
          | ? [X3] :
              ( ( ~ r2_hidden(X3,X2)
                | ~ r2_hidden(X3,X1) )
              & ( r2_hidden(X3,X2)
                | r2_hidden(X3,X1) )
              & m1_subset_1(X3,X0) )
          | ~ m1_subset_1(X2,k1_zfmisc_1(X0)) )
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(nnf_transformation,[],[f23])).

fof(f46,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( X1 = X2
          | ? [X3] :
              ( ( ~ r2_hidden(X3,X2)
                | ~ r2_hidden(X3,X1) )
              & ( r2_hidden(X3,X2)
                | r2_hidden(X3,X1) )
              & m1_subset_1(X3,X0) )
          | ~ m1_subset_1(X2,k1_zfmisc_1(X0)) )
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(flattening,[],[f45])).

fof(f47,plain,(
    ! [X2,X1,X0] :
      ( ? [X3] :
          ( ( ~ r2_hidden(X3,X2)
            | ~ r2_hidden(X3,X1) )
          & ( r2_hidden(X3,X2)
            | r2_hidden(X3,X1) )
          & m1_subset_1(X3,X0) )
     => ( ( ~ r2_hidden(sK1(X0,X1,X2),X2)
          | ~ r2_hidden(sK1(X0,X1,X2),X1) )
        & ( r2_hidden(sK1(X0,X1,X2),X2)
          | r2_hidden(sK1(X0,X1,X2),X1) )
        & m1_subset_1(sK1(X0,X1,X2),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f48,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( X1 = X2
          | ( ( ~ r2_hidden(sK1(X0,X1,X2),X2)
              | ~ r2_hidden(sK1(X0,X1,X2),X1) )
            & ( r2_hidden(sK1(X0,X1,X2),X2)
              | r2_hidden(sK1(X0,X1,X2),X1) )
            & m1_subset_1(sK1(X0,X1,X2),X0) )
          | ~ m1_subset_1(X2,k1_zfmisc_1(X0)) )
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1])],[f46,f47])).

fof(f75,plain,(
    ! [X2,X0,X1] :
      ( X1 = X2
      | m1_subset_1(sK1(X0,X1,X2),X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f48])).

fof(f15,conjecture,(
    ! [X0] :
      ( ( l1_orders_2(X0)
        & v1_yellow_0(X0)
        & v5_orders_2(X0)
        & v4_orders_2(X0)
        & v3_orders_2(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
            & v13_waybel_0(X1,X0)
            & v2_waybel_0(X1,X0)
            & ~ v1_xboole_0(X1) )
         => ( v1_subset_1(X1,u1_struct_0(X0))
          <=> ~ r2_hidden(k3_yellow_0(X0),X1) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f16,negated_conjecture,(
    ~ ! [X0] :
        ( ( l1_orders_2(X0)
          & v1_yellow_0(X0)
          & v5_orders_2(X0)
          & v4_orders_2(X0)
          & v3_orders_2(X0)
          & ~ v2_struct_0(X0) )
       => ! [X1] :
            ( ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
              & v13_waybel_0(X1,X0)
              & v2_waybel_0(X1,X0)
              & ~ v1_xboole_0(X1) )
           => ( v1_subset_1(X1,u1_struct_0(X0))
            <=> ~ r2_hidden(k3_yellow_0(X0),X1) ) ) ) ),
    inference(negated_conjecture,[],[f15])).

fof(f17,plain,(
    ~ ! [X0] :
        ( ( l1_orders_2(X0)
          & v1_yellow_0(X0)
          & v5_orders_2(X0)
          & v4_orders_2(X0)
          & v3_orders_2(X0)
          & ~ v2_struct_0(X0) )
       => ! [X1] :
            ( ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
              & v13_waybel_0(X1,X0)
              & ~ v1_xboole_0(X1) )
           => ( v1_subset_1(X1,u1_struct_0(X0))
            <=> ~ r2_hidden(k3_yellow_0(X0),X1) ) ) ) ),
    inference(pure_predicate_removal,[],[f16])).

fof(f18,plain,(
    ~ ! [X0] :
        ( ( l1_orders_2(X0)
          & v1_yellow_0(X0)
          & v5_orders_2(X0)
          & v3_orders_2(X0)
          & ~ v2_struct_0(X0) )
       => ! [X1] :
            ( ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
              & v13_waybel_0(X1,X0)
              & ~ v1_xboole_0(X1) )
           => ( v1_subset_1(X1,u1_struct_0(X0))
            <=> ~ r2_hidden(k3_yellow_0(X0),X1) ) ) ) ),
    inference(pure_predicate_removal,[],[f17])).

fof(f19,plain,(
    ~ ! [X0] :
        ( ( l1_orders_2(X0)
          & v1_yellow_0(X0)
          & v5_orders_2(X0)
          & ~ v2_struct_0(X0) )
       => ! [X1] :
            ( ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
              & v13_waybel_0(X1,X0)
              & ~ v1_xboole_0(X1) )
           => ( v1_subset_1(X1,u1_struct_0(X0))
            <=> ~ r2_hidden(k3_yellow_0(X0),X1) ) ) ) ),
    inference(pure_predicate_removal,[],[f18])).

fof(f39,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ( v1_subset_1(X1,u1_struct_0(X0))
          <~> ~ r2_hidden(k3_yellow_0(X0),X1) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
          & v13_waybel_0(X1,X0)
          & ~ v1_xboole_0(X1) )
      & l1_orders_2(X0)
      & v1_yellow_0(X0)
      & v5_orders_2(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f19])).

fof(f40,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ( v1_subset_1(X1,u1_struct_0(X0))
          <~> ~ r2_hidden(k3_yellow_0(X0),X1) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
          & v13_waybel_0(X1,X0)
          & ~ v1_xboole_0(X1) )
      & l1_orders_2(X0)
      & v1_yellow_0(X0)
      & v5_orders_2(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(flattening,[],[f39])).

fof(f66,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ( r2_hidden(k3_yellow_0(X0),X1)
            | ~ v1_subset_1(X1,u1_struct_0(X0)) )
          & ( ~ r2_hidden(k3_yellow_0(X0),X1)
            | v1_subset_1(X1,u1_struct_0(X0)) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
          & v13_waybel_0(X1,X0)
          & ~ v1_xboole_0(X1) )
      & l1_orders_2(X0)
      & v1_yellow_0(X0)
      & v5_orders_2(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(nnf_transformation,[],[f40])).

fof(f67,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ( r2_hidden(k3_yellow_0(X0),X1)
            | ~ v1_subset_1(X1,u1_struct_0(X0)) )
          & ( ~ r2_hidden(k3_yellow_0(X0),X1)
            | v1_subset_1(X1,u1_struct_0(X0)) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
          & v13_waybel_0(X1,X0)
          & ~ v1_xboole_0(X1) )
      & l1_orders_2(X0)
      & v1_yellow_0(X0)
      & v5_orders_2(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(flattening,[],[f66])).

fof(f69,plain,(
    ! [X0] :
      ( ? [X1] :
          ( ( r2_hidden(k3_yellow_0(X0),X1)
            | ~ v1_subset_1(X1,u1_struct_0(X0)) )
          & ( ~ r2_hidden(k3_yellow_0(X0),X1)
            | v1_subset_1(X1,u1_struct_0(X0)) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
          & v13_waybel_0(X1,X0)
          & ~ v1_xboole_0(X1) )
     => ( ( r2_hidden(k3_yellow_0(X0),sK8)
          | ~ v1_subset_1(sK8,u1_struct_0(X0)) )
        & ( ~ r2_hidden(k3_yellow_0(X0),sK8)
          | v1_subset_1(sK8,u1_struct_0(X0)) )
        & m1_subset_1(sK8,k1_zfmisc_1(u1_struct_0(X0)))
        & v13_waybel_0(sK8,X0)
        & ~ v1_xboole_0(sK8) ) ) ),
    introduced(choice_axiom,[])).

fof(f68,plain,
    ( ? [X0] :
        ( ? [X1] :
            ( ( r2_hidden(k3_yellow_0(X0),X1)
              | ~ v1_subset_1(X1,u1_struct_0(X0)) )
            & ( ~ r2_hidden(k3_yellow_0(X0),X1)
              | v1_subset_1(X1,u1_struct_0(X0)) )
            & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
            & v13_waybel_0(X1,X0)
            & ~ v1_xboole_0(X1) )
        & l1_orders_2(X0)
        & v1_yellow_0(X0)
        & v5_orders_2(X0)
        & ~ v2_struct_0(X0) )
   => ( ? [X1] :
          ( ( r2_hidden(k3_yellow_0(sK7),X1)
            | ~ v1_subset_1(X1,u1_struct_0(sK7)) )
          & ( ~ r2_hidden(k3_yellow_0(sK7),X1)
            | v1_subset_1(X1,u1_struct_0(sK7)) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK7)))
          & v13_waybel_0(X1,sK7)
          & ~ v1_xboole_0(X1) )
      & l1_orders_2(sK7)
      & v1_yellow_0(sK7)
      & v5_orders_2(sK7)
      & ~ v2_struct_0(sK7) ) ),
    introduced(choice_axiom,[])).

fof(f70,plain,
    ( ( r2_hidden(k3_yellow_0(sK7),sK8)
      | ~ v1_subset_1(sK8,u1_struct_0(sK7)) )
    & ( ~ r2_hidden(k3_yellow_0(sK7),sK8)
      | v1_subset_1(sK8,u1_struct_0(sK7)) )
    & m1_subset_1(sK8,k1_zfmisc_1(u1_struct_0(sK7)))
    & v13_waybel_0(sK8,sK7)
    & ~ v1_xboole_0(sK8)
    & l1_orders_2(sK7)
    & v1_yellow_0(sK7)
    & v5_orders_2(sK7)
    & ~ v2_struct_0(sK7) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK7,sK8])],[f67,f69,f68])).

fof(f108,plain,(
    m1_subset_1(sK8,k1_zfmisc_1(u1_struct_0(sK7))) ),
    inference(cnf_transformation,[],[f70])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => ! [X2] :
          ( r2_hidden(X2,X1)
         => r2_hidden(X2,X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f21,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( r2_hidden(X2,X0)
          | ~ r2_hidden(X2,X1) )
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f74,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(X2,X0)
      | ~ r2_hidden(X2,X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f1,axiom,(
    ! [X0] :
      ( v1_xboole_0(X0)
    <=> ! [X1] : ~ r2_hidden(X1,X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f41,plain,(
    ! [X0] :
      ( ( v1_xboole_0(X0)
        | ? [X1] : r2_hidden(X1,X0) )
      & ( ! [X1] : ~ r2_hidden(X1,X0)
        | ~ v1_xboole_0(X0) ) ) ),
    inference(nnf_transformation,[],[f1])).

fof(f42,plain,(
    ! [X0] :
      ( ( v1_xboole_0(X0)
        | ? [X1] : r2_hidden(X1,X0) )
      & ( ! [X2] : ~ r2_hidden(X2,X0)
        | ~ v1_xboole_0(X0) ) ) ),
    inference(rectify,[],[f41])).

fof(f43,plain,(
    ! [X0] :
      ( ? [X1] : r2_hidden(X1,X0)
     => r2_hidden(sK0(X0),X0) ) ),
    introduced(choice_axiom,[])).

fof(f44,plain,(
    ! [X0] :
      ( ( v1_xboole_0(X0)
        | r2_hidden(sK0(X0),X0) )
      & ( ! [X2] : ~ r2_hidden(X2,X0)
        | ~ v1_xboole_0(X0) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f42,f43])).

fof(f72,plain,(
    ! [X0] :
      ( v1_xboole_0(X0)
      | r2_hidden(sK0(X0),X0) ) ),
    inference(cnf_transformation,[],[f44])).

fof(f5,axiom,(
    ! [X0] :
    ? [X1] :
      ( ~ v1_subset_1(X1,X0)
      & m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f49,plain,(
    ! [X0] :
      ( ? [X1] :
          ( ~ v1_subset_1(X1,X0)
          & m1_subset_1(X1,k1_zfmisc_1(X0)) )
     => ( ~ v1_subset_1(sK2(X0),X0)
        & m1_subset_1(sK2(X0),k1_zfmisc_1(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f50,plain,(
    ! [X0] :
      ( ~ v1_subset_1(sK2(X0),X0)
      & m1_subset_1(sK2(X0),k1_zfmisc_1(X0)) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2])],[f5,f49])).

fof(f78,plain,(
    ! [X0] : m1_subset_1(sK2(X0),k1_zfmisc_1(X0)) ),
    inference(cnf_transformation,[],[f50])).

fof(f79,plain,(
    ! [X0] : ~ v1_subset_1(sK2(X0),X0) ),
    inference(cnf_transformation,[],[f50])).

fof(f14,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => ( v1_subset_1(X1,X0)
      <=> X0 != X1 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f38,plain,(
    ! [X0,X1] :
      ( ( v1_subset_1(X1,X0)
      <=> X0 != X1 )
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f65,plain,(
    ! [X0,X1] :
      ( ( ( v1_subset_1(X1,X0)
          | X0 = X1 )
        & ( X0 != X1
          | ~ v1_subset_1(X1,X0) ) )
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(nnf_transformation,[],[f38])).

fof(f101,plain,(
    ! [X0,X1] :
      ( v1_subset_1(X1,X0)
      | X0 = X1
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f65])).

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

fof(f81,plain,(
    ! [X2,X0,X1] :
      ( m1_subset_1(X0,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f8,axiom,(
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

fof(f28,plain,(
    ! [X0] :
      ( ! [X1,X2] :
          ( ( r2_lattice3(X0,X1,X2)
          <=> ! [X3] :
                ( r1_orders_2(X0,X3,X2)
                | ~ r2_hidden(X3,X1)
                | ~ m1_subset_1(X3,u1_struct_0(X0)) ) )
          | ~ m1_subset_1(X2,u1_struct_0(X0)) )
      | ~ l1_orders_2(X0) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f29,plain,(
    ! [X0] :
      ( ! [X1,X2] :
          ( ( r2_lattice3(X0,X1,X2)
          <=> ! [X3] :
                ( r1_orders_2(X0,X3,X2)
                | ~ r2_hidden(X3,X1)
                | ~ m1_subset_1(X3,u1_struct_0(X0)) ) )
          | ~ m1_subset_1(X2,u1_struct_0(X0)) )
      | ~ l1_orders_2(X0) ) ),
    inference(flattening,[],[f28])).

fof(f51,plain,(
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
    inference(nnf_transformation,[],[f29])).

fof(f52,plain,(
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
    inference(rectify,[],[f51])).

fof(f53,plain,(
    ! [X2,X1,X0] :
      ( ? [X3] :
          ( ~ r1_orders_2(X0,X3,X2)
          & r2_hidden(X3,X1)
          & m1_subset_1(X3,u1_struct_0(X0)) )
     => ( ~ r1_orders_2(X0,sK3(X0,X1,X2),X2)
        & r2_hidden(sK3(X0,X1,X2),X1)
        & m1_subset_1(sK3(X0,X1,X2),u1_struct_0(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f54,plain,(
    ! [X0] :
      ( ! [X1,X2] :
          ( ( ( r2_lattice3(X0,X1,X2)
              | ( ~ r1_orders_2(X0,sK3(X0,X1,X2),X2)
                & r2_hidden(sK3(X0,X1,X2),X1)
                & m1_subset_1(sK3(X0,X1,X2),u1_struct_0(X0)) ) )
            & ( ! [X4] :
                  ( r1_orders_2(X0,X4,X2)
                  | ~ r2_hidden(X4,X1)
                  | ~ m1_subset_1(X4,u1_struct_0(X0)) )
              | ~ r2_lattice3(X0,X1,X2) ) )
          | ~ m1_subset_1(X2,u1_struct_0(X0)) )
      | ~ l1_orders_2(X0) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3])],[f52,f53])).

fof(f82,plain,(
    ! [X4,X2,X0,X1] :
      ( r1_orders_2(X0,X4,X2)
      | ~ r2_hidden(X4,X1)
      | ~ m1_subset_1(X4,u1_struct_0(X0))
      | ~ r2_lattice3(X0,X1,X2)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ l1_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f54])).

fof(f105,plain,(
    l1_orders_2(sK7) ),
    inference(cnf_transformation,[],[f70])).

fof(f106,plain,(
    ~ v1_xboole_0(sK8) ),
    inference(cnf_transformation,[],[f70])).

fof(f71,plain,(
    ! [X2,X0] :
      ( ~ r2_hidden(X2,X0)
      | ~ v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f44])).

fof(f13,axiom,(
    ! [X0] :
      ( l1_orders_2(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ( v13_waybel_0(X1,X0)
          <=> ! [X2] :
                ( m1_subset_1(X2,u1_struct_0(X0))
               => ! [X3] :
                    ( m1_subset_1(X3,u1_struct_0(X0))
                   => ( ( r1_orders_2(X0,X2,X3)
                        & r2_hidden(X2,X1) )
                     => r2_hidden(X3,X1) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f36,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( v13_waybel_0(X1,X0)
          <=> ! [X2] :
                ( ! [X3] :
                    ( r2_hidden(X3,X1)
                    | ~ r1_orders_2(X0,X2,X3)
                    | ~ r2_hidden(X2,X1)
                    | ~ m1_subset_1(X3,u1_struct_0(X0)) )
                | ~ m1_subset_1(X2,u1_struct_0(X0)) ) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_orders_2(X0) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f37,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( v13_waybel_0(X1,X0)
          <=> ! [X2] :
                ( ! [X3] :
                    ( r2_hidden(X3,X1)
                    | ~ r1_orders_2(X0,X2,X3)
                    | ~ r2_hidden(X2,X1)
                    | ~ m1_subset_1(X3,u1_struct_0(X0)) )
                | ~ m1_subset_1(X2,u1_struct_0(X0)) ) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_orders_2(X0) ) ),
    inference(flattening,[],[f36])).

fof(f60,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ( v13_waybel_0(X1,X0)
              | ? [X2] :
                  ( ? [X3] :
                      ( ~ r2_hidden(X3,X1)
                      & r1_orders_2(X0,X2,X3)
                      & r2_hidden(X2,X1)
                      & m1_subset_1(X3,u1_struct_0(X0)) )
                  & m1_subset_1(X2,u1_struct_0(X0)) ) )
            & ( ! [X2] :
                  ( ! [X3] :
                      ( r2_hidden(X3,X1)
                      | ~ r1_orders_2(X0,X2,X3)
                      | ~ r2_hidden(X2,X1)
                      | ~ m1_subset_1(X3,u1_struct_0(X0)) )
                  | ~ m1_subset_1(X2,u1_struct_0(X0)) )
              | ~ v13_waybel_0(X1,X0) ) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_orders_2(X0) ) ),
    inference(nnf_transformation,[],[f37])).

fof(f61,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ( v13_waybel_0(X1,X0)
              | ? [X2] :
                  ( ? [X3] :
                      ( ~ r2_hidden(X3,X1)
                      & r1_orders_2(X0,X2,X3)
                      & r2_hidden(X2,X1)
                      & m1_subset_1(X3,u1_struct_0(X0)) )
                  & m1_subset_1(X2,u1_struct_0(X0)) ) )
            & ( ! [X4] :
                  ( ! [X5] :
                      ( r2_hidden(X5,X1)
                      | ~ r1_orders_2(X0,X4,X5)
                      | ~ r2_hidden(X4,X1)
                      | ~ m1_subset_1(X5,u1_struct_0(X0)) )
                  | ~ m1_subset_1(X4,u1_struct_0(X0)) )
              | ~ v13_waybel_0(X1,X0) ) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_orders_2(X0) ) ),
    inference(rectify,[],[f60])).

fof(f63,plain,(
    ! [X2,X1,X0] :
      ( ? [X3] :
          ( ~ r2_hidden(X3,X1)
          & r1_orders_2(X0,X2,X3)
          & r2_hidden(X2,X1)
          & m1_subset_1(X3,u1_struct_0(X0)) )
     => ( ~ r2_hidden(sK6(X0,X1),X1)
        & r1_orders_2(X0,X2,sK6(X0,X1))
        & r2_hidden(X2,X1)
        & m1_subset_1(sK6(X0,X1),u1_struct_0(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f62,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ? [X3] :
              ( ~ r2_hidden(X3,X1)
              & r1_orders_2(X0,X2,X3)
              & r2_hidden(X2,X1)
              & m1_subset_1(X3,u1_struct_0(X0)) )
          & m1_subset_1(X2,u1_struct_0(X0)) )
     => ( ? [X3] :
            ( ~ r2_hidden(X3,X1)
            & r1_orders_2(X0,sK5(X0,X1),X3)
            & r2_hidden(sK5(X0,X1),X1)
            & m1_subset_1(X3,u1_struct_0(X0)) )
        & m1_subset_1(sK5(X0,X1),u1_struct_0(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f64,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ( v13_waybel_0(X1,X0)
              | ( ~ r2_hidden(sK6(X0,X1),X1)
                & r1_orders_2(X0,sK5(X0,X1),sK6(X0,X1))
                & r2_hidden(sK5(X0,X1),X1)
                & m1_subset_1(sK6(X0,X1),u1_struct_0(X0))
                & m1_subset_1(sK5(X0,X1),u1_struct_0(X0)) ) )
            & ( ! [X4] :
                  ( ! [X5] :
                      ( r2_hidden(X5,X1)
                      | ~ r1_orders_2(X0,X4,X5)
                      | ~ r2_hidden(X4,X1)
                      | ~ m1_subset_1(X5,u1_struct_0(X0)) )
                  | ~ m1_subset_1(X4,u1_struct_0(X0)) )
              | ~ v13_waybel_0(X1,X0) ) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_orders_2(X0) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK5,sK6])],[f61,f63,f62])).

fof(f94,plain,(
    ! [X4,X0,X5,X1] :
      ( r2_hidden(X5,X1)
      | ~ r1_orders_2(X0,X4,X5)
      | ~ r2_hidden(X4,X1)
      | ~ m1_subset_1(X5,u1_struct_0(X0))
      | ~ m1_subset_1(X4,u1_struct_0(X0))
      | ~ v13_waybel_0(X1,X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f64])).

fof(f107,plain,(
    v13_waybel_0(sK8,sK7) ),
    inference(cnf_transformation,[],[f70])).

fof(f9,axiom,(
    ! [X0] :
      ( l1_orders_2(X0)
     => k3_yellow_0(X0) = k1_yellow_0(X0,k1_xboole_0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f30,plain,(
    ! [X0] :
      ( k3_yellow_0(X0) = k1_yellow_0(X0,k1_xboole_0)
      | ~ l1_orders_2(X0) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f86,plain,(
    ! [X0] :
      ( k3_yellow_0(X0) = k1_yellow_0(X0,k1_xboole_0)
      | ~ l1_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f11,axiom,(
    ! [X0,X1] :
      ( l1_orders_2(X0)
     => m1_subset_1(k1_yellow_0(X0,X1),u1_struct_0(X0)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f33,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k1_yellow_0(X0,X1),u1_struct_0(X0))
      | ~ l1_orders_2(X0) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f92,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k1_yellow_0(X0,X1),u1_struct_0(X0))
      | ~ l1_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f33])).

fof(f6,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,X1)
     => ( r2_hidden(X0,X1)
        | v1_xboole_0(X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f24,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
      | v1_xboole_0(X1)
      | ~ m1_subset_1(X0,X1) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f25,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
      | v1_xboole_0(X1)
      | ~ m1_subset_1(X0,X1) ) ),
    inference(flattening,[],[f24])).

fof(f80,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
      | v1_xboole_0(X1)
      | ~ m1_subset_1(X0,X1) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f10,axiom,(
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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f31,plain,(
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
    inference(ennf_transformation,[],[f10])).

fof(f32,plain,(
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
    inference(flattening,[],[f31])).

fof(f55,plain,(
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
    inference(nnf_transformation,[],[f32])).

fof(f56,plain,(
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
    inference(flattening,[],[f55])).

fof(f57,plain,(
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
    inference(rectify,[],[f56])).

fof(f58,plain,(
    ! [X2,X1,X0] :
      ( ? [X3] :
          ( ~ r1_orders_2(X0,X2,X3)
          & r2_lattice3(X0,X1,X3)
          & m1_subset_1(X3,u1_struct_0(X0)) )
     => ( ~ r1_orders_2(X0,X2,sK4(X0,X1,X2))
        & r2_lattice3(X0,X1,sK4(X0,X1,X2))
        & m1_subset_1(sK4(X0,X1,X2),u1_struct_0(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f59,plain,(
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
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4])],[f57,f58])).

fof(f88,plain,(
    ! [X4,X2,X0,X1] :
      ( r1_orders_2(X0,X2,X4)
      | ~ r2_lattice3(X0,X1,X4)
      | ~ m1_subset_1(X4,u1_struct_0(X0))
      | k1_yellow_0(X0,X1) != X2
      | ~ r1_yellow_0(X0,X1)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ l1_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f59])).

fof(f111,plain,(
    ! [X4,X0,X1] :
      ( r1_orders_2(X0,k1_yellow_0(X0,X1),X4)
      | ~ r2_lattice3(X0,X1,X4)
      | ~ m1_subset_1(X4,u1_struct_0(X0))
      | ~ r1_yellow_0(X0,X1)
      | ~ m1_subset_1(k1_yellow_0(X0,X1),u1_struct_0(X0))
      | ~ l1_orders_2(X0) ) ),
    inference(equality_resolution,[],[f88])).

fof(f12,axiom,(
    ! [X0] :
      ( ( l1_orders_2(X0)
        & v1_yellow_0(X0)
        & v5_orders_2(X0)
        & ~ v2_struct_0(X0) )
     => ( r2_yellow_0(X0,u1_struct_0(X0))
        & r1_yellow_0(X0,k1_xboole_0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f20,plain,(
    ! [X0] :
      ( ( l1_orders_2(X0)
        & v1_yellow_0(X0)
        & v5_orders_2(X0)
        & ~ v2_struct_0(X0) )
     => r1_yellow_0(X0,k1_xboole_0) ) ),
    inference(pure_predicate_removal,[],[f12])).

fof(f34,plain,(
    ! [X0] :
      ( r1_yellow_0(X0,k1_xboole_0)
      | ~ l1_orders_2(X0)
      | ~ v1_yellow_0(X0)
      | ~ v5_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f20])).

fof(f35,plain,(
    ! [X0] :
      ( r1_yellow_0(X0,k1_xboole_0)
      | ~ l1_orders_2(X0)
      | ~ v1_yellow_0(X0)
      | ~ v5_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f34])).

fof(f93,plain,(
    ! [X0] :
      ( r1_yellow_0(X0,k1_xboole_0)
      | ~ l1_orders_2(X0)
      | ~ v1_yellow_0(X0)
      | ~ v5_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f35])).

fof(f104,plain,(
    v1_yellow_0(sK7) ),
    inference(cnf_transformation,[],[f70])).

fof(f102,plain,(
    ~ v2_struct_0(sK7) ),
    inference(cnf_transformation,[],[f70])).

fof(f103,plain,(
    v5_orders_2(sK7) ),
    inference(cnf_transformation,[],[f70])).

fof(f110,plain,
    ( r2_hidden(k3_yellow_0(sK7),sK8)
    | ~ v1_subset_1(sK8,u1_struct_0(sK7)) ),
    inference(cnf_transformation,[],[f70])).

fof(f84,plain,(
    ! [X2,X0,X1] :
      ( r2_lattice3(X0,X1,X2)
      | r2_hidden(sK3(X0,X1,X2),X1)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ l1_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f54])).

fof(f87,plain,(
    ! [X2,X0,X1] :
      ( r2_lattice3(X0,X1,X2)
      | k1_yellow_0(X0,X1) != X2
      | ~ r1_yellow_0(X0,X1)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ l1_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f59])).

fof(f112,plain,(
    ! [X0,X1] :
      ( r2_lattice3(X0,X1,k1_yellow_0(X0,X1))
      | ~ r1_yellow_0(X0,X1)
      | ~ m1_subset_1(k1_yellow_0(X0,X1),u1_struct_0(X0))
      | ~ l1_orders_2(X0) ) ),
    inference(equality_resolution,[],[f87])).

fof(f2,axiom,(
    v1_xboole_0(k1_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f73,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(cnf_transformation,[],[f2])).

fof(f77,plain,(
    ! [X2,X0,X1] :
      ( X1 = X2
      | ~ r2_hidden(sK1(X0,X1,X2),X2)
      | ~ r2_hidden(sK1(X0,X1,X2),X1)
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f48])).

fof(f109,plain,
    ( ~ r2_hidden(k3_yellow_0(sK7),sK8)
    | v1_subset_1(sK8,u1_struct_0(sK7)) ),
    inference(cnf_transformation,[],[f70])).

cnf(c_6,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | ~ m1_subset_1(X2,k1_zfmisc_1(X1))
    | m1_subset_1(sK1(X1,X0,X2),X1)
    | X0 = X2 ),
    inference(cnf_transformation,[],[f75])).

cnf(c_2681,plain,
    ( X0 = X1
    | m1_subset_1(X0,k1_zfmisc_1(X2)) != iProver_top
    | m1_subset_1(X1,k1_zfmisc_1(X2)) != iProver_top
    | m1_subset_1(sK1(X2,X0,X1),X2) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_6])).

cnf(c_33,negated_conjecture,
    ( m1_subset_1(sK8,k1_zfmisc_1(u1_struct_0(sK7))) ),
    inference(cnf_transformation,[],[f108])).

cnf(c_2677,plain,
    ( m1_subset_1(sK8,k1_zfmisc_1(u1_struct_0(sK7))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_33])).

cnf(c_3,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | ~ r2_hidden(X2,X0)
    | r2_hidden(X2,X1) ),
    inference(cnf_transformation,[],[f74])).

cnf(c_2684,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(X1)) != iProver_top
    | r2_hidden(X2,X0) != iProver_top
    | r2_hidden(X2,X1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3])).

cnf(c_4010,plain,
    ( r2_hidden(X0,u1_struct_0(sK7)) = iProver_top
    | r2_hidden(X0,sK8) != iProver_top ),
    inference(superposition,[status(thm)],[c_2677,c_2684])).

cnf(c_0,plain,
    ( r2_hidden(sK0(X0),X0)
    | v1_xboole_0(X0) ),
    inference(cnf_transformation,[],[f72])).

cnf(c_2687,plain,
    ( r2_hidden(sK0(X0),X0) = iProver_top
    | v1_xboole_0(X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_0])).

cnf(c_8,plain,
    ( m1_subset_1(sK2(X0),k1_zfmisc_1(X0)) ),
    inference(cnf_transformation,[],[f78])).

cnf(c_2680,plain,
    ( m1_subset_1(sK2(X0),k1_zfmisc_1(X0)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_8])).

cnf(c_7,plain,
    ( ~ v1_subset_1(sK2(X0),X0) ),
    inference(cnf_transformation,[],[f79])).

cnf(c_29,plain,
    ( v1_subset_1(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | X0 = X1 ),
    inference(cnf_transformation,[],[f101])).

cnf(c_618,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | X1 != X2
    | X1 = X0
    | sK2(X2) != X0 ),
    inference(resolution_lifted,[status(thm)],[c_7,c_29])).

cnf(c_619,plain,
    ( ~ m1_subset_1(sK2(X0),k1_zfmisc_1(X0))
    | X0 = sK2(X0) ),
    inference(unflattening,[status(thm)],[c_618])).

cnf(c_623,plain,
    ( X0 = sK2(X0) ),
    inference(global_propositional_subsumption,[status(thm)],[c_619,c_8])).

cnf(c_2700,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(X0)) = iProver_top ),
    inference(light_normalisation,[status(thm)],[c_2680,c_623])).

cnf(c_10,plain,
    ( m1_subset_1(X0,X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(X1))
    | ~ r2_hidden(X0,X2) ),
    inference(cnf_transformation,[],[f81])).

cnf(c_2678,plain,
    ( m1_subset_1(X0,X1) = iProver_top
    | m1_subset_1(X2,k1_zfmisc_1(X1)) != iProver_top
    | r2_hidden(X0,X2) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_10])).

cnf(c_4876,plain,
    ( m1_subset_1(X0,X1) = iProver_top
    | r2_hidden(X0,X1) != iProver_top ),
    inference(superposition,[status(thm)],[c_2700,c_2678])).

cnf(c_5076,plain,
    ( m1_subset_1(sK0(X0),X0) = iProver_top
    | v1_xboole_0(X0) = iProver_top ),
    inference(superposition,[status(thm)],[c_2687,c_4876])).

cnf(c_14,plain,
    ( r1_orders_2(X0,X1,X2)
    | ~ r2_lattice3(X0,X3,X2)
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | ~ m1_subset_1(X1,u1_struct_0(X0))
    | ~ r2_hidden(X1,X3)
    | ~ l1_orders_2(X0) ),
    inference(cnf_transformation,[],[f82])).

cnf(c_36,negated_conjecture,
    ( l1_orders_2(sK7) ),
    inference(cnf_transformation,[],[f105])).

cnf(c_858,plain,
    ( r1_orders_2(X0,X1,X2)
    | ~ r2_lattice3(X0,X3,X2)
    | ~ m1_subset_1(X1,u1_struct_0(X0))
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | ~ r2_hidden(X1,X3)
    | sK7 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_14,c_36])).

cnf(c_859,plain,
    ( r1_orders_2(sK7,X0,X1)
    | ~ r2_lattice3(sK7,X2,X1)
    | ~ m1_subset_1(X0,u1_struct_0(sK7))
    | ~ m1_subset_1(X1,u1_struct_0(sK7))
    | ~ r2_hidden(X0,X2) ),
    inference(unflattening,[status(thm)],[c_858])).

cnf(c_2663,plain,
    ( r1_orders_2(sK7,X0,X1) = iProver_top
    | r2_lattice3(sK7,X2,X1) != iProver_top
    | m1_subset_1(X0,u1_struct_0(sK7)) != iProver_top
    | m1_subset_1(X1,u1_struct_0(sK7)) != iProver_top
    | r2_hidden(X0,X2) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_859])).

cnf(c_5605,plain,
    ( r1_orders_2(sK7,sK0(u1_struct_0(sK7)),X0) = iProver_top
    | r2_lattice3(sK7,X1,X0) != iProver_top
    | m1_subset_1(X0,u1_struct_0(sK7)) != iProver_top
    | r2_hidden(sK0(u1_struct_0(sK7)),X1) != iProver_top
    | v1_xboole_0(u1_struct_0(sK7)) = iProver_top ),
    inference(superposition,[status(thm)],[c_5076,c_2663])).

cnf(c_46,plain,
    ( m1_subset_1(sK8,k1_zfmisc_1(u1_struct_0(sK7))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_33])).

cnf(c_35,negated_conjecture,
    ( ~ v1_xboole_0(sK8) ),
    inference(cnf_transformation,[],[f106])).

cnf(c_575,plain,
    ( r2_hidden(sK0(X0),X0)
    | sK8 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_0,c_35])).

cnf(c_576,plain,
    ( r2_hidden(sK0(sK8),sK8) ),
    inference(unflattening,[status(thm)],[c_575])).

cnf(c_577,plain,
    ( r2_hidden(sK0(sK8),sK8) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_576])).

cnf(c_3135,plain,
    ( ~ m1_subset_1(sK8,k1_zfmisc_1(X0))
    | r2_hidden(sK0(sK8),X0)
    | ~ r2_hidden(sK0(sK8),sK8) ),
    inference(instantiation,[status(thm)],[c_3])).

cnf(c_3269,plain,
    ( ~ m1_subset_1(sK8,k1_zfmisc_1(u1_struct_0(sK7)))
    | r2_hidden(sK0(sK8),u1_struct_0(sK7))
    | ~ r2_hidden(sK0(sK8),sK8) ),
    inference(instantiation,[status(thm)],[c_3135])).

cnf(c_3270,plain,
    ( m1_subset_1(sK8,k1_zfmisc_1(u1_struct_0(sK7))) != iProver_top
    | r2_hidden(sK0(sK8),u1_struct_0(sK7)) = iProver_top
    | r2_hidden(sK0(sK8),sK8) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3269])).

cnf(c_1,plain,
    ( ~ r2_hidden(X0,X1)
    | ~ v1_xboole_0(X1) ),
    inference(cnf_transformation,[],[f71])).

cnf(c_3733,plain,
    ( ~ r2_hidden(sK0(sK8),u1_struct_0(sK7))
    | ~ v1_xboole_0(u1_struct_0(sK7)) ),
    inference(instantiation,[status(thm)],[c_1])).

cnf(c_3734,plain,
    ( r2_hidden(sK0(sK8),u1_struct_0(sK7)) != iProver_top
    | v1_xboole_0(u1_struct_0(sK7)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3733])).

cnf(c_9351,plain,
    ( r2_hidden(sK0(u1_struct_0(sK7)),X1) != iProver_top
    | m1_subset_1(X0,u1_struct_0(sK7)) != iProver_top
    | r2_lattice3(sK7,X1,X0) != iProver_top
    | r1_orders_2(sK7,sK0(u1_struct_0(sK7)),X0) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_5605,c_46,c_577,c_3270,c_3734])).

cnf(c_9352,plain,
    ( r1_orders_2(sK7,sK0(u1_struct_0(sK7)),X0) = iProver_top
    | r2_lattice3(sK7,X1,X0) != iProver_top
    | m1_subset_1(X0,u1_struct_0(sK7)) != iProver_top
    | r2_hidden(sK0(u1_struct_0(sK7)),X1) != iProver_top ),
    inference(renaming,[status(thm)],[c_9351])).

cnf(c_9362,plain,
    ( r1_orders_2(sK7,sK0(u1_struct_0(sK7)),X0) = iProver_top
    | r2_lattice3(sK7,u1_struct_0(sK7),X0) != iProver_top
    | m1_subset_1(X0,u1_struct_0(sK7)) != iProver_top
    | r2_hidden(sK0(u1_struct_0(sK7)),sK8) != iProver_top ),
    inference(superposition,[status(thm)],[c_4010,c_9352])).

cnf(c_9361,plain,
    ( r1_orders_2(sK7,sK0(u1_struct_0(sK7)),X0) = iProver_top
    | r2_lattice3(sK7,u1_struct_0(sK7),X0) != iProver_top
    | m1_subset_1(X0,u1_struct_0(sK7)) != iProver_top
    | v1_xboole_0(u1_struct_0(sK7)) = iProver_top ),
    inference(superposition,[status(thm)],[c_2687,c_9352])).

cnf(c_9398,plain,
    ( m1_subset_1(X0,u1_struct_0(sK7)) != iProver_top
    | r2_lattice3(sK7,u1_struct_0(sK7),X0) != iProver_top
    | r1_orders_2(sK7,sK0(u1_struct_0(sK7)),X0) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_9362,c_46,c_577,c_3270,c_3734,c_9361])).

cnf(c_9399,plain,
    ( r1_orders_2(sK7,sK0(u1_struct_0(sK7)),X0) = iProver_top
    | r2_lattice3(sK7,u1_struct_0(sK7),X0) != iProver_top
    | m1_subset_1(X0,u1_struct_0(sK7)) != iProver_top ),
    inference(renaming,[status(thm)],[c_9398])).

cnf(c_28,plain,
    ( ~ r1_orders_2(X0,X1,X2)
    | ~ v13_waybel_0(X3,X0)
    | ~ m1_subset_1(X1,u1_struct_0(X0))
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))
    | ~ r2_hidden(X1,X3)
    | r2_hidden(X2,X3)
    | ~ l1_orders_2(X0) ),
    inference(cnf_transformation,[],[f94])).

cnf(c_804,plain,
    ( ~ r1_orders_2(X0,X1,X2)
    | ~ v13_waybel_0(X3,X0)
    | ~ m1_subset_1(X1,u1_struct_0(X0))
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))
    | ~ r2_hidden(X1,X3)
    | r2_hidden(X2,X3)
    | sK7 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_28,c_36])).

cnf(c_805,plain,
    ( ~ r1_orders_2(sK7,X0,X1)
    | ~ v13_waybel_0(X2,sK7)
    | ~ m1_subset_1(X0,u1_struct_0(sK7))
    | ~ m1_subset_1(X1,u1_struct_0(sK7))
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK7)))
    | ~ r2_hidden(X0,X2)
    | r2_hidden(X1,X2) ),
    inference(unflattening,[status(thm)],[c_804])).

cnf(c_821,plain,
    ( ~ r1_orders_2(sK7,X0,X1)
    | ~ v13_waybel_0(X2,sK7)
    | ~ m1_subset_1(X1,u1_struct_0(sK7))
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK7)))
    | ~ r2_hidden(X0,X2)
    | r2_hidden(X1,X2) ),
    inference(forward_subsumption_resolution,[status(thm)],[c_805,c_10])).

cnf(c_2666,plain,
    ( r1_orders_2(sK7,X0,X1) != iProver_top
    | v13_waybel_0(X2,sK7) != iProver_top
    | m1_subset_1(X1,u1_struct_0(sK7)) != iProver_top
    | m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK7))) != iProver_top
    | r2_hidden(X0,X2) != iProver_top
    | r2_hidden(X1,X2) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_821])).

cnf(c_4701,plain,
    ( r1_orders_2(sK7,X0,X1) != iProver_top
    | v13_waybel_0(sK8,sK7) != iProver_top
    | m1_subset_1(X1,u1_struct_0(sK7)) != iProver_top
    | r2_hidden(X0,sK8) != iProver_top
    | r2_hidden(X1,sK8) = iProver_top ),
    inference(superposition,[status(thm)],[c_2677,c_2666])).

cnf(c_34,negated_conjecture,
    ( v13_waybel_0(sK8,sK7) ),
    inference(cnf_transformation,[],[f107])).

cnf(c_1032,plain,
    ( ~ r1_orders_2(sK7,X0,X1)
    | ~ m1_subset_1(X1,u1_struct_0(sK7))
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK7)))
    | ~ r2_hidden(X0,X2)
    | r2_hidden(X1,X2)
    | sK8 != X2
    | sK7 != sK7 ),
    inference(resolution_lifted,[status(thm)],[c_34,c_821])).

cnf(c_1033,plain,
    ( ~ r1_orders_2(sK7,X0,X1)
    | ~ m1_subset_1(X1,u1_struct_0(sK7))
    | ~ m1_subset_1(sK8,k1_zfmisc_1(u1_struct_0(sK7)))
    | ~ r2_hidden(X0,sK8)
    | r2_hidden(X1,sK8) ),
    inference(unflattening,[status(thm)],[c_1032])).

cnf(c_1035,plain,
    ( ~ m1_subset_1(X1,u1_struct_0(sK7))
    | ~ r1_orders_2(sK7,X0,X1)
    | ~ r2_hidden(X0,sK8)
    | r2_hidden(X1,sK8) ),
    inference(global_propositional_subsumption,[status(thm)],[c_1033,c_33])).

cnf(c_1036,plain,
    ( ~ r1_orders_2(sK7,X0,X1)
    | ~ m1_subset_1(X1,u1_struct_0(sK7))
    | ~ r2_hidden(X0,sK8)
    | r2_hidden(X1,sK8) ),
    inference(renaming,[status(thm)],[c_1035])).

cnf(c_1037,plain,
    ( r1_orders_2(sK7,X0,X1) != iProver_top
    | m1_subset_1(X1,u1_struct_0(sK7)) != iProver_top
    | r2_hidden(X0,sK8) != iProver_top
    | r2_hidden(X1,sK8) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1036])).

cnf(c_5121,plain,
    ( r1_orders_2(sK7,X0,X1) != iProver_top
    | m1_subset_1(X1,u1_struct_0(sK7)) != iProver_top
    | r2_hidden(X0,sK8) != iProver_top
    | r2_hidden(X1,sK8) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_4701,c_1037])).

cnf(c_9408,plain,
    ( r2_lattice3(sK7,u1_struct_0(sK7),X0) != iProver_top
    | m1_subset_1(X0,u1_struct_0(sK7)) != iProver_top
    | r2_hidden(X0,sK8) = iProver_top
    | r2_hidden(sK0(u1_struct_0(sK7)),sK8) != iProver_top ),
    inference(superposition,[status(thm)],[c_9399,c_5121])).

cnf(c_2099,plain,
    ( X0 != X1
    | k3_yellow_0(X0) = k3_yellow_0(X1) ),
    theory(equality)).

cnf(c_2114,plain,
    ( k3_yellow_0(sK7) = k3_yellow_0(sK7)
    | sK7 != sK7 ),
    inference(instantiation,[status(thm)],[c_2099])).

cnf(c_2088,plain,
    ( X0 = X0 ),
    theory(equality)).

cnf(c_2121,plain,
    ( sK7 = sK7 ),
    inference(instantiation,[status(thm)],[c_2088])).

cnf(c_3184,plain,
    ( sK8 = sK8 ),
    inference(instantiation,[status(thm)],[c_2088])).

cnf(c_15,plain,
    ( ~ l1_orders_2(X0)
    | k1_yellow_0(X0,k1_xboole_0) = k3_yellow_0(X0) ),
    inference(cnf_transformation,[],[f86])).

cnf(c_853,plain,
    ( k1_yellow_0(X0,k1_xboole_0) = k3_yellow_0(X0)
    | sK7 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_15,c_36])).

cnf(c_854,plain,
    ( k1_yellow_0(sK7,k1_xboole_0) = k3_yellow_0(sK7) ),
    inference(unflattening,[status(thm)],[c_853])).

cnf(c_21,plain,
    ( m1_subset_1(k1_yellow_0(X0,X1),u1_struct_0(X0))
    | ~ l1_orders_2(X0) ),
    inference(cnf_transformation,[],[f92])).

cnf(c_844,plain,
    ( m1_subset_1(k1_yellow_0(X0,X1),u1_struct_0(X0))
    | sK7 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_21,c_36])).

cnf(c_845,plain,
    ( m1_subset_1(k1_yellow_0(sK7,X0),u1_struct_0(sK7)) ),
    inference(unflattening,[status(thm)],[c_844])).

cnf(c_2664,plain,
    ( m1_subset_1(k1_yellow_0(sK7,X0),u1_struct_0(sK7)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_845])).

cnf(c_3036,plain,
    ( m1_subset_1(k3_yellow_0(sK7),u1_struct_0(sK7)) = iProver_top ),
    inference(superposition,[status(thm)],[c_854,c_2664])).

cnf(c_9,plain,
    ( ~ m1_subset_1(X0,X1)
    | r2_hidden(X0,X1)
    | v1_xboole_0(X1) ),
    inference(cnf_transformation,[],[f80])).

cnf(c_2679,plain,
    ( m1_subset_1(X0,X1) != iProver_top
    | r2_hidden(X0,X1) = iProver_top
    | v1_xboole_0(X1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_9])).

cnf(c_3306,plain,
    ( r2_hidden(k3_yellow_0(sK7),u1_struct_0(sK7)) = iProver_top
    | v1_xboole_0(u1_struct_0(sK7)) = iProver_top ),
    inference(superposition,[status(thm)],[c_3036,c_2679])).

cnf(c_2089,plain,
    ( X0 != X1
    | X2 != X1
    | X2 = X0 ),
    theory(equality)).

cnf(c_3115,plain,
    ( u1_struct_0(sK7) != X0
    | sK8 != X0
    | sK8 = u1_struct_0(sK7) ),
    inference(instantiation,[status(thm)],[c_2089])).

cnf(c_3637,plain,
    ( u1_struct_0(sK7) != sK8
    | sK8 = u1_struct_0(sK7)
    | sK8 != sK8 ),
    inference(instantiation,[status(thm)],[c_3115])).

cnf(c_19,plain,
    ( r1_orders_2(X0,k1_yellow_0(X0,X1),X2)
    | ~ r2_lattice3(X0,X1,X2)
    | ~ r1_yellow_0(X0,X1)
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | ~ m1_subset_1(k1_yellow_0(X0,X1),u1_struct_0(X0))
    | ~ l1_orders_2(X0) ),
    inference(cnf_transformation,[],[f111])).

cnf(c_243,plain,
    ( ~ m1_subset_1(X2,u1_struct_0(X0))
    | ~ r1_yellow_0(X0,X1)
    | ~ r2_lattice3(X0,X1,X2)
    | r1_orders_2(X0,k1_yellow_0(X0,X1),X2)
    | ~ l1_orders_2(X0) ),
    inference(global_propositional_subsumption,[status(thm)],[c_19,c_21])).

cnf(c_244,plain,
    ( r1_orders_2(X0,k1_yellow_0(X0,X1),X2)
    | ~ r2_lattice3(X0,X1,X2)
    | ~ r1_yellow_0(X0,X1)
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | ~ l1_orders_2(X0) ),
    inference(renaming,[status(thm)],[c_243])).

cnf(c_22,plain,
    ( r1_yellow_0(X0,k1_xboole_0)
    | v2_struct_0(X0)
    | ~ v5_orders_2(X0)
    | ~ v1_yellow_0(X0)
    | ~ l1_orders_2(X0) ),
    inference(cnf_transformation,[],[f93])).

cnf(c_37,negated_conjecture,
    ( v1_yellow_0(sK7) ),
    inference(cnf_transformation,[],[f104])).

cnf(c_538,plain,
    ( r1_yellow_0(X0,k1_xboole_0)
    | v2_struct_0(X0)
    | ~ v5_orders_2(X0)
    | ~ l1_orders_2(X0)
    | sK7 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_22,c_37])).

cnf(c_539,plain,
    ( r1_yellow_0(sK7,k1_xboole_0)
    | v2_struct_0(sK7)
    | ~ v5_orders_2(sK7)
    | ~ l1_orders_2(sK7) ),
    inference(unflattening,[status(thm)],[c_538])).

cnf(c_39,negated_conjecture,
    ( ~ v2_struct_0(sK7) ),
    inference(cnf_transformation,[],[f102])).

cnf(c_38,negated_conjecture,
    ( v5_orders_2(sK7) ),
    inference(cnf_transformation,[],[f103])).

cnf(c_72,plain,
    ( r1_yellow_0(sK7,k1_xboole_0)
    | v2_struct_0(sK7)
    | ~ v5_orders_2(sK7)
    | ~ v1_yellow_0(sK7)
    | ~ l1_orders_2(sK7) ),
    inference(instantiation,[status(thm)],[c_22])).

cnf(c_541,plain,
    ( r1_yellow_0(sK7,k1_xboole_0) ),
    inference(global_propositional_subsumption,[status(thm)],[c_539,c_39,c_38,c_37,c_36,c_72])).

cnf(c_703,plain,
    ( r1_orders_2(X0,k1_yellow_0(X0,X1),X2)
    | ~ r2_lattice3(X0,X1,X2)
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | ~ l1_orders_2(X0)
    | sK7 != X0
    | k1_xboole_0 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_244,c_541])).

cnf(c_704,plain,
    ( r1_orders_2(sK7,k1_yellow_0(sK7,k1_xboole_0),X0)
    | ~ r2_lattice3(sK7,k1_xboole_0,X0)
    | ~ m1_subset_1(X0,u1_struct_0(sK7))
    | ~ l1_orders_2(sK7) ),
    inference(unflattening,[status(thm)],[c_703])).

cnf(c_708,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(sK7))
    | ~ r2_lattice3(sK7,k1_xboole_0,X0)
    | r1_orders_2(sK7,k1_yellow_0(sK7,k1_xboole_0),X0) ),
    inference(global_propositional_subsumption,[status(thm)],[c_704,c_36])).

cnf(c_709,plain,
    ( r1_orders_2(sK7,k1_yellow_0(sK7,k1_xboole_0),X0)
    | ~ r2_lattice3(sK7,k1_xboole_0,X0)
    | ~ m1_subset_1(X0,u1_struct_0(sK7)) ),
    inference(renaming,[status(thm)],[c_708])).

cnf(c_2670,plain,
    ( r1_orders_2(sK7,k1_yellow_0(sK7,k1_xboole_0),X0) = iProver_top
    | r2_lattice3(sK7,k1_xboole_0,X0) != iProver_top
    | m1_subset_1(X0,u1_struct_0(sK7)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_709])).

cnf(c_2783,plain,
    ( r1_orders_2(sK7,k3_yellow_0(sK7),X0) = iProver_top
    | r2_lattice3(sK7,k1_xboole_0,X0) != iProver_top
    | m1_subset_1(X0,u1_struct_0(sK7)) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_2670,c_854])).

cnf(c_5130,plain,
    ( r2_lattice3(sK7,k1_xboole_0,X0) != iProver_top
    | m1_subset_1(X0,u1_struct_0(sK7)) != iProver_top
    | r2_hidden(X0,sK8) = iProver_top
    | r2_hidden(k3_yellow_0(sK7),sK8) != iProver_top ),
    inference(superposition,[status(thm)],[c_2783,c_5121])).

cnf(c_31,negated_conjecture,
    ( ~ v1_subset_1(sK8,u1_struct_0(sK7))
    | r2_hidden(k3_yellow_0(sK7),sK8) ),
    inference(cnf_transformation,[],[f110])).

cnf(c_317,plain,
    ( ~ v1_subset_1(sK8,u1_struct_0(sK7))
    | r2_hidden(k3_yellow_0(sK7),sK8) ),
    inference(prop_impl,[status(thm)],[c_31])).

cnf(c_641,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | r2_hidden(k3_yellow_0(sK7),sK8)
    | X1 = X0
    | u1_struct_0(sK7) != X1
    | sK8 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_29,c_317])).

cnf(c_642,plain,
    ( ~ m1_subset_1(sK8,k1_zfmisc_1(u1_struct_0(sK7)))
    | r2_hidden(k3_yellow_0(sK7),sK8)
    | u1_struct_0(sK7) = sK8 ),
    inference(unflattening,[status(thm)],[c_641])).

cnf(c_644,plain,
    ( r2_hidden(k3_yellow_0(sK7),sK8)
    | u1_struct_0(sK7) = sK8 ),
    inference(global_propositional_subsumption,[status(thm)],[c_642,c_33])).

cnf(c_2673,plain,
    ( u1_struct_0(sK7) = sK8
    | r2_hidden(k3_yellow_0(sK7),sK8) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_644])).

cnf(c_5497,plain,
    ( u1_struct_0(sK7) = sK8
    | r2_lattice3(sK7,k1_xboole_0,X0) != iProver_top
    | m1_subset_1(X0,u1_struct_0(sK7)) != iProver_top
    | r2_hidden(X0,sK8) = iProver_top ),
    inference(superposition,[status(thm)],[c_2673,c_5130])).

cnf(c_12,plain,
    ( r2_lattice3(X0,X1,X2)
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | r2_hidden(sK3(X0,X1,X2),X1)
    | ~ l1_orders_2(X0) ),
    inference(cnf_transformation,[],[f84])).

cnf(c_894,plain,
    ( r2_lattice3(X0,X1,X2)
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | r2_hidden(sK3(X0,X1,X2),X1)
    | sK7 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_12,c_36])).

cnf(c_895,plain,
    ( r2_lattice3(sK7,X0,X1)
    | ~ m1_subset_1(X1,u1_struct_0(sK7))
    | r2_hidden(sK3(sK7,X0,X1),X0) ),
    inference(unflattening,[status(thm)],[c_894])).

cnf(c_2661,plain,
    ( r2_lattice3(sK7,X0,X1) = iProver_top
    | m1_subset_1(X1,u1_struct_0(sK7)) != iProver_top
    | r2_hidden(sK3(sK7,X0,X1),X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_895])).

cnf(c_20,plain,
    ( r2_lattice3(X0,X1,k1_yellow_0(X0,X1))
    | ~ r1_yellow_0(X0,X1)
    | ~ m1_subset_1(k1_yellow_0(X0,X1),u1_struct_0(X0))
    | ~ l1_orders_2(X0) ),
    inference(cnf_transformation,[],[f112])).

cnf(c_236,plain,
    ( ~ r1_yellow_0(X0,X1)
    | r2_lattice3(X0,X1,k1_yellow_0(X0,X1))
    | ~ l1_orders_2(X0) ),
    inference(global_propositional_subsumption,[status(thm)],[c_20,c_21])).

cnf(c_237,plain,
    ( r2_lattice3(X0,X1,k1_yellow_0(X0,X1))
    | ~ r1_yellow_0(X0,X1)
    | ~ l1_orders_2(X0) ),
    inference(renaming,[status(thm)],[c_236])).

cnf(c_724,plain,
    ( r2_lattice3(X0,X1,k1_yellow_0(X0,X1))
    | ~ l1_orders_2(X0)
    | sK7 != X0
    | k1_xboole_0 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_237,c_541])).

cnf(c_725,plain,
    ( r2_lattice3(sK7,k1_xboole_0,k1_yellow_0(sK7,k1_xboole_0))
    | ~ l1_orders_2(sK7) ),
    inference(unflattening,[status(thm)],[c_724])).

cnf(c_727,plain,
    ( r2_lattice3(sK7,k1_xboole_0,k1_yellow_0(sK7,k1_xboole_0)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_725,c_36])).

cnf(c_2669,plain,
    ( r2_lattice3(sK7,k1_xboole_0,k1_yellow_0(sK7,k1_xboole_0)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_727])).

cnf(c_2705,plain,
    ( r2_lattice3(sK7,k1_xboole_0,k3_yellow_0(sK7)) = iProver_top ),
    inference(light_normalisation,[status(thm)],[c_2669,c_854])).

cnf(c_4002,plain,
    ( m1_subset_1(X0,u1_struct_0(sK7)) = iProver_top
    | r2_hidden(X0,sK8) != iProver_top ),
    inference(superposition,[status(thm)],[c_2677,c_2678])).

cnf(c_4288,plain,
    ( r1_orders_2(sK7,X0,X1) = iProver_top
    | r2_lattice3(sK7,X2,X1) != iProver_top
    | m1_subset_1(X1,u1_struct_0(sK7)) != iProver_top
    | r2_hidden(X0,X2) != iProver_top
    | r2_hidden(X0,sK8) != iProver_top ),
    inference(superposition,[status(thm)],[c_4002,c_2663])).

cnf(c_5980,plain,
    ( r1_orders_2(sK7,X0,k3_yellow_0(sK7)) = iProver_top
    | r2_lattice3(sK7,X1,k3_yellow_0(sK7)) != iProver_top
    | r2_hidden(X0,X1) != iProver_top
    | r2_hidden(X0,sK8) != iProver_top ),
    inference(superposition,[status(thm)],[c_3036,c_4288])).

cnf(c_6113,plain,
    ( r1_orders_2(sK7,X0,k3_yellow_0(sK7)) = iProver_top
    | r2_hidden(X0,sK8) != iProver_top
    | r2_hidden(X0,k1_xboole_0) != iProver_top ),
    inference(superposition,[status(thm)],[c_2705,c_5980])).

cnf(c_2,plain,
    ( v1_xboole_0(k1_xboole_0) ),
    inference(cnf_transformation,[],[f73])).

cnf(c_582,plain,
    ( ~ r2_hidden(X0,X1)
    | k1_xboole_0 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_1,c_2])).

cnf(c_583,plain,
    ( ~ r2_hidden(X0,k1_xboole_0) ),
    inference(unflattening,[status(thm)],[c_582])).

cnf(c_584,plain,
    ( r2_hidden(X0,k1_xboole_0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_583])).

cnf(c_6232,plain,
    ( r2_hidden(X0,k1_xboole_0) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_6113,c_584])).

cnf(c_6240,plain,
    ( r2_lattice3(sK7,k1_xboole_0,X0) = iProver_top
    | m1_subset_1(X0,u1_struct_0(sK7)) != iProver_top ),
    inference(superposition,[status(thm)],[c_2661,c_6232])).

cnf(c_2091,plain,
    ( ~ r2_hidden(X0,X1)
    | r2_hidden(X2,X3)
    | X2 != X0
    | X3 != X1 ),
    theory(equality)).

cnf(c_3853,plain,
    ( r2_hidden(X0,X1)
    | ~ r2_hidden(k3_yellow_0(sK7),u1_struct_0(sK7))
    | X0 != k3_yellow_0(sK7)
    | X1 != u1_struct_0(sK7) ),
    inference(instantiation,[status(thm)],[c_2091])).

cnf(c_4422,plain,
    ( r2_hidden(k3_yellow_0(sK7),X0)
    | ~ r2_hidden(k3_yellow_0(sK7),u1_struct_0(sK7))
    | X0 != u1_struct_0(sK7)
    | k3_yellow_0(sK7) != k3_yellow_0(sK7) ),
    inference(instantiation,[status(thm)],[c_3853])).

cnf(c_7126,plain,
    ( ~ r2_hidden(k3_yellow_0(sK7),u1_struct_0(sK7))
    | r2_hidden(k3_yellow_0(sK7),sK8)
    | k3_yellow_0(sK7) != k3_yellow_0(sK7)
    | sK8 != u1_struct_0(sK7) ),
    inference(instantiation,[status(thm)],[c_4422])).

cnf(c_7127,plain,
    ( k3_yellow_0(sK7) != k3_yellow_0(sK7)
    | sK8 != u1_struct_0(sK7)
    | r2_hidden(k3_yellow_0(sK7),u1_struct_0(sK7)) != iProver_top
    | r2_hidden(k3_yellow_0(sK7),sK8) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_7126])).

cnf(c_9540,plain,
    ( r2_hidden(X0,sK8) = iProver_top
    | m1_subset_1(X0,u1_struct_0(sK7)) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_9408,c_46,c_577,c_2114,c_2121,c_3184,c_3270,c_3306,c_3637,c_3734,c_5130,c_5497,c_6240,c_7127])).

cnf(c_9541,plain,
    ( m1_subset_1(X0,u1_struct_0(sK7)) != iProver_top
    | r2_hidden(X0,sK8) = iProver_top ),
    inference(renaming,[status(thm)],[c_9540])).

cnf(c_9548,plain,
    ( X0 = X1
    | m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK7))) != iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK7))) != iProver_top
    | r2_hidden(sK1(u1_struct_0(sK7),X1,X0),sK8) = iProver_top ),
    inference(superposition,[status(thm)],[c_2681,c_9541])).

cnf(c_4,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | ~ m1_subset_1(X2,k1_zfmisc_1(X1))
    | ~ r2_hidden(sK1(X1,X0,X2),X2)
    | ~ r2_hidden(sK1(X1,X0,X2),X0)
    | X0 = X2 ),
    inference(cnf_transformation,[],[f77])).

cnf(c_2683,plain,
    ( X0 = X1
    | m1_subset_1(X0,k1_zfmisc_1(X2)) != iProver_top
    | m1_subset_1(X1,k1_zfmisc_1(X2)) != iProver_top
    | r2_hidden(sK1(X2,X0,X1),X1) != iProver_top
    | r2_hidden(sK1(X2,X0,X1),X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_4])).

cnf(c_4859,plain,
    ( u1_struct_0(sK7) = X0
    | m1_subset_1(X0,k1_zfmisc_1(X1)) != iProver_top
    | m1_subset_1(u1_struct_0(sK7),k1_zfmisc_1(X1)) != iProver_top
    | r2_hidden(sK1(X1,X0,u1_struct_0(sK7)),X0) != iProver_top
    | r2_hidden(sK1(X1,X0,u1_struct_0(sK7)),sK8) != iProver_top ),
    inference(superposition,[status(thm)],[c_4010,c_2683])).

cnf(c_9878,plain,
    ( u1_struct_0(sK7) = sK8
    | m1_subset_1(u1_struct_0(sK7),k1_zfmisc_1(u1_struct_0(sK7))) != iProver_top
    | m1_subset_1(sK8,k1_zfmisc_1(u1_struct_0(sK7))) != iProver_top
    | r2_hidden(sK1(u1_struct_0(sK7),sK8,u1_struct_0(sK7)),sK8) != iProver_top ),
    inference(superposition,[status(thm)],[c_9548,c_4859])).

cnf(c_9883,plain,
    ( u1_struct_0(sK7) = sK8
    | m1_subset_1(u1_struct_0(sK7),k1_zfmisc_1(u1_struct_0(sK7))) != iProver_top
    | m1_subset_1(sK8,k1_zfmisc_1(u1_struct_0(sK7))) != iProver_top ),
    inference(forward_subsumption_resolution,[status(thm)],[c_9878,c_9548])).

cnf(c_9555,plain,
    ( r2_hidden(k3_yellow_0(sK7),sK8) = iProver_top ),
    inference(superposition,[status(thm)],[c_3036,c_9541])).

cnf(c_2093,plain,
    ( ~ m1_subset_1(X0,X1)
    | m1_subset_1(X2,X3)
    | X2 != X0
    | X3 != X1 ),
    theory(equality)).

cnf(c_3056,plain,
    ( m1_subset_1(X0,X1)
    | ~ m1_subset_1(sK2(X2),k1_zfmisc_1(X2))
    | X0 != sK2(X2)
    | X1 != k1_zfmisc_1(X2) ),
    inference(instantiation,[status(thm)],[c_2093])).

cnf(c_3473,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(X1))
    | ~ m1_subset_1(sK2(X1),k1_zfmisc_1(X1))
    | X0 != sK2(X1)
    | k1_zfmisc_1(X1) != k1_zfmisc_1(X1) ),
    inference(instantiation,[status(thm)],[c_3056])).

cnf(c_4550,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK7)))
    | ~ m1_subset_1(sK2(u1_struct_0(sK7)),k1_zfmisc_1(u1_struct_0(sK7)))
    | X0 != sK2(u1_struct_0(sK7))
    | k1_zfmisc_1(u1_struct_0(sK7)) != k1_zfmisc_1(u1_struct_0(sK7)) ),
    inference(instantiation,[status(thm)],[c_3473])).

cnf(c_6224,plain,
    ( m1_subset_1(u1_struct_0(sK7),k1_zfmisc_1(u1_struct_0(sK7)))
    | ~ m1_subset_1(sK2(u1_struct_0(sK7)),k1_zfmisc_1(u1_struct_0(sK7)))
    | u1_struct_0(sK7) != sK2(u1_struct_0(sK7))
    | k1_zfmisc_1(u1_struct_0(sK7)) != k1_zfmisc_1(u1_struct_0(sK7)) ),
    inference(instantiation,[status(thm)],[c_4550])).

cnf(c_6225,plain,
    ( u1_struct_0(sK7) != sK2(u1_struct_0(sK7))
    | k1_zfmisc_1(u1_struct_0(sK7)) != k1_zfmisc_1(u1_struct_0(sK7))
    | m1_subset_1(u1_struct_0(sK7),k1_zfmisc_1(u1_struct_0(sK7))) = iProver_top
    | m1_subset_1(sK2(u1_struct_0(sK7)),k1_zfmisc_1(u1_struct_0(sK7))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_6224])).

cnf(c_2092,plain,
    ( X0 != X1
    | k1_zfmisc_1(X0) = k1_zfmisc_1(X1) ),
    theory(equality)).

cnf(c_3294,plain,
    ( X0 != u1_struct_0(sK7)
    | k1_zfmisc_1(X0) = k1_zfmisc_1(u1_struct_0(sK7)) ),
    inference(instantiation,[status(thm)],[c_2092])).

cnf(c_4791,plain,
    ( u1_struct_0(sK7) != u1_struct_0(sK7)
    | k1_zfmisc_1(u1_struct_0(sK7)) = k1_zfmisc_1(u1_struct_0(sK7)) ),
    inference(instantiation,[status(thm)],[c_3294])).

cnf(c_3574,plain,
    ( u1_struct_0(sK7) = sK2(u1_struct_0(sK7)) ),
    inference(instantiation,[status(thm)],[c_623])).

cnf(c_3005,plain,
    ( m1_subset_1(sK2(u1_struct_0(sK7)),k1_zfmisc_1(u1_struct_0(sK7))) ),
    inference(instantiation,[status(thm)],[c_8])).

cnf(c_3011,plain,
    ( m1_subset_1(sK2(u1_struct_0(sK7)),k1_zfmisc_1(u1_struct_0(sK7))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3005])).

cnf(c_32,negated_conjecture,
    ( v1_subset_1(sK8,u1_struct_0(sK7))
    | ~ r2_hidden(k3_yellow_0(sK7),sK8) ),
    inference(cnf_transformation,[],[f109])).

cnf(c_315,plain,
    ( v1_subset_1(sK8,u1_struct_0(sK7))
    | ~ r2_hidden(k3_yellow_0(sK7),sK8) ),
    inference(prop_impl,[status(thm)],[c_32])).

cnf(c_629,plain,
    ( ~ r2_hidden(k3_yellow_0(sK7),sK8)
    | u1_struct_0(sK7) != X0
    | sK2(X0) != sK8 ),
    inference(resolution_lifted,[status(thm)],[c_7,c_315])).

cnf(c_630,plain,
    ( ~ r2_hidden(k3_yellow_0(sK7),sK8)
    | sK2(u1_struct_0(sK7)) != sK8 ),
    inference(unflattening,[status(thm)],[c_629])).

cnf(c_2674,plain,
    ( sK2(u1_struct_0(sK7)) != sK8
    | r2_hidden(k3_yellow_0(sK7),sK8) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_630])).

cnf(c_2720,plain,
    ( u1_struct_0(sK7) != sK8
    | r2_hidden(k3_yellow_0(sK7),sK8) != iProver_top ),
    inference(demodulation,[status(thm)],[c_2674,c_623])).

cnf(c_2098,plain,
    ( X0 != X1
    | u1_struct_0(X0) = u1_struct_0(X1) ),
    theory(equality)).

cnf(c_2113,plain,
    ( u1_struct_0(sK7) = u1_struct_0(sK7)
    | sK7 != sK7 ),
    inference(instantiation,[status(thm)],[c_2098])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_9883,c_9555,c_6225,c_4791,c_3574,c_3011,c_2720,c_2121,c_2113,c_46])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.00/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.10/0.11  % Command    : iproveropt_run.sh %d %s
% 0.11/0.32  % Computer   : n003.cluster.edu
% 0.11/0.32  % Model      : x86_64 x86_64
% 0.11/0.32  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.11/0.32  % Memory     : 8042.1875MB
% 0.11/0.32  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.11/0.32  % CPULimit   : 60
% 0.11/0.32  % WCLimit    : 600
% 0.11/0.32  % DateTime   : Tue Dec  1 10:37:27 EST 2020
% 0.11/0.32  % CPUTime    : 
% 0.11/0.33  % Running in FOF mode
% 3.78/0.99  % SZS status Started for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.78/0.99  
% 3.78/0.99  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 3.78/0.99  
% 3.78/0.99  ------  iProver source info
% 3.78/0.99  
% 3.78/0.99  git: date: 2020-06-30 10:37:57 +0100
% 3.78/0.99  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 3.78/0.99  git: non_committed_changes: false
% 3.78/0.99  git: last_make_outside_of_git: false
% 3.78/0.99  
% 3.78/0.99  ------ 
% 3.78/0.99  
% 3.78/0.99  ------ Input Options
% 3.78/0.99  
% 3.78/0.99  --out_options                           all
% 3.78/0.99  --tptp_safe_out                         true
% 3.78/0.99  --problem_path                          ""
% 3.78/0.99  --include_path                          ""
% 3.78/0.99  --clausifier                            res/vclausify_rel
% 3.78/0.99  --clausifier_options                    --mode clausify
% 3.78/0.99  --stdin                                 false
% 3.78/0.99  --stats_out                             all
% 3.78/0.99  
% 3.78/0.99  ------ General Options
% 3.78/0.99  
% 3.78/0.99  --fof                                   false
% 3.78/0.99  --time_out_real                         305.
% 3.78/0.99  --time_out_virtual                      -1.
% 3.78/0.99  --symbol_type_check                     false
% 3.78/0.99  --clausify_out                          false
% 3.78/0.99  --sig_cnt_out                           false
% 3.78/0.99  --trig_cnt_out                          false
% 3.78/0.99  --trig_cnt_out_tolerance                1.
% 3.78/0.99  --trig_cnt_out_sk_spl                   false
% 3.78/0.99  --abstr_cl_out                          false
% 3.78/0.99  
% 3.78/0.99  ------ Global Options
% 3.78/0.99  
% 3.78/0.99  --schedule                              default
% 3.78/0.99  --add_important_lit                     false
% 3.78/0.99  --prop_solver_per_cl                    1000
% 3.78/0.99  --min_unsat_core                        false
% 3.78/0.99  --soft_assumptions                      false
% 3.78/0.99  --soft_lemma_size                       3
% 3.78/0.99  --prop_impl_unit_size                   0
% 3.78/0.99  --prop_impl_unit                        []
% 3.78/0.99  --share_sel_clauses                     true
% 3.78/0.99  --reset_solvers                         false
% 3.78/0.99  --bc_imp_inh                            [conj_cone]
% 3.78/0.99  --conj_cone_tolerance                   3.
% 3.78/0.99  --extra_neg_conj                        none
% 3.78/0.99  --large_theory_mode                     true
% 3.78/0.99  --prolific_symb_bound                   200
% 3.78/0.99  --lt_threshold                          2000
% 3.78/0.99  --clause_weak_htbl                      true
% 3.78/0.99  --gc_record_bc_elim                     false
% 3.78/0.99  
% 3.78/0.99  ------ Preprocessing Options
% 3.78/0.99  
% 3.78/0.99  --preprocessing_flag                    true
% 3.78/0.99  --time_out_prep_mult                    0.1
% 3.78/0.99  --splitting_mode                        input
% 3.78/0.99  --splitting_grd                         true
% 3.78/0.99  --splitting_cvd                         false
% 3.78/0.99  --splitting_cvd_svl                     false
% 3.78/0.99  --splitting_nvd                         32
% 3.78/0.99  --sub_typing                            true
% 3.78/0.99  --prep_gs_sim                           true
% 3.78/0.99  --prep_unflatten                        true
% 3.78/0.99  --prep_res_sim                          true
% 3.78/0.99  --prep_upred                            true
% 3.78/0.99  --prep_sem_filter                       exhaustive
% 3.78/0.99  --prep_sem_filter_out                   false
% 3.78/0.99  --pred_elim                             true
% 3.78/0.99  --res_sim_input                         true
% 3.78/0.99  --eq_ax_congr_red                       true
% 3.78/0.99  --pure_diseq_elim                       true
% 3.78/0.99  --brand_transform                       false
% 3.78/0.99  --non_eq_to_eq                          false
% 3.78/0.99  --prep_def_merge                        true
% 3.78/0.99  --prep_def_merge_prop_impl              false
% 3.78/0.99  --prep_def_merge_mbd                    true
% 3.78/0.99  --prep_def_merge_tr_red                 false
% 3.78/0.99  --prep_def_merge_tr_cl                  false
% 3.78/0.99  --smt_preprocessing                     true
% 3.78/0.99  --smt_ac_axioms                         fast
% 3.78/0.99  --preprocessed_out                      false
% 3.78/0.99  --preprocessed_stats                    false
% 3.78/0.99  
% 3.78/0.99  ------ Abstraction refinement Options
% 3.78/0.99  
% 3.78/0.99  --abstr_ref                             []
% 3.78/0.99  --abstr_ref_prep                        false
% 3.78/0.99  --abstr_ref_until_sat                   false
% 3.78/0.99  --abstr_ref_sig_restrict                funpre
% 3.78/0.99  --abstr_ref_af_restrict_to_split_sk     false
% 3.78/0.99  --abstr_ref_under                       []
% 3.78/0.99  
% 3.78/0.99  ------ SAT Options
% 3.78/0.99  
% 3.78/0.99  --sat_mode                              false
% 3.78/0.99  --sat_fm_restart_options                ""
% 3.78/0.99  --sat_gr_def                            false
% 3.78/0.99  --sat_epr_types                         true
% 3.78/0.99  --sat_non_cyclic_types                  false
% 3.78/0.99  --sat_finite_models                     false
% 3.78/0.99  --sat_fm_lemmas                         false
% 3.78/0.99  --sat_fm_prep                           false
% 3.78/0.99  --sat_fm_uc_incr                        true
% 3.78/0.99  --sat_out_model                         small
% 3.78/0.99  --sat_out_clauses                       false
% 3.78/0.99  
% 3.78/0.99  ------ QBF Options
% 3.78/0.99  
% 3.78/0.99  --qbf_mode                              false
% 3.78/0.99  --qbf_elim_univ                         false
% 3.78/0.99  --qbf_dom_inst                          none
% 3.78/0.99  --qbf_dom_pre_inst                      false
% 3.78/0.99  --qbf_sk_in                             false
% 3.78/0.99  --qbf_pred_elim                         true
% 3.78/0.99  --qbf_split                             512
% 3.78/0.99  
% 3.78/0.99  ------ BMC1 Options
% 3.78/0.99  
% 3.78/0.99  --bmc1_incremental                      false
% 3.78/0.99  --bmc1_axioms                           reachable_all
% 3.78/0.99  --bmc1_min_bound                        0
% 3.78/0.99  --bmc1_max_bound                        -1
% 3.78/0.99  --bmc1_max_bound_default                -1
% 3.78/0.99  --bmc1_symbol_reachability              true
% 3.78/0.99  --bmc1_property_lemmas                  false
% 3.78/0.99  --bmc1_k_induction                      false
% 3.78/0.99  --bmc1_non_equiv_states                 false
% 3.78/0.99  --bmc1_deadlock                         false
% 3.78/0.99  --bmc1_ucm                              false
% 3.78/0.99  --bmc1_add_unsat_core                   none
% 3.78/0.99  --bmc1_unsat_core_children              false
% 3.78/0.99  --bmc1_unsat_core_extrapolate_axioms    false
% 3.78/0.99  --bmc1_out_stat                         full
% 3.78/0.99  --bmc1_ground_init                      false
% 3.78/0.99  --bmc1_pre_inst_next_state              false
% 3.78/0.99  --bmc1_pre_inst_state                   false
% 3.78/0.99  --bmc1_pre_inst_reach_state             false
% 3.78/0.99  --bmc1_out_unsat_core                   false
% 3.78/0.99  --bmc1_aig_witness_out                  false
% 3.78/0.99  --bmc1_verbose                          false
% 3.78/0.99  --bmc1_dump_clauses_tptp                false
% 3.78/0.99  --bmc1_dump_unsat_core_tptp             false
% 3.78/0.99  --bmc1_dump_file                        -
% 3.78/0.99  --bmc1_ucm_expand_uc_limit              128
% 3.78/0.99  --bmc1_ucm_n_expand_iterations          6
% 3.78/0.99  --bmc1_ucm_extend_mode                  1
% 3.78/0.99  --bmc1_ucm_init_mode                    2
% 3.78/0.99  --bmc1_ucm_cone_mode                    none
% 3.78/0.99  --bmc1_ucm_reduced_relation_type        0
% 3.78/0.99  --bmc1_ucm_relax_model                  4
% 3.78/0.99  --bmc1_ucm_full_tr_after_sat            true
% 3.78/0.99  --bmc1_ucm_expand_neg_assumptions       false
% 3.78/0.99  --bmc1_ucm_layered_model                none
% 3.78/0.99  --bmc1_ucm_max_lemma_size               10
% 3.78/0.99  
% 3.78/0.99  ------ AIG Options
% 3.78/0.99  
% 3.78/0.99  --aig_mode                              false
% 3.78/0.99  
% 3.78/0.99  ------ Instantiation Options
% 3.78/0.99  
% 3.78/0.99  --instantiation_flag                    true
% 3.78/0.99  --inst_sos_flag                         false
% 3.78/0.99  --inst_sos_phase                        true
% 3.78/0.99  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 3.78/0.99  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 3.78/0.99  --inst_lit_sel_side                     num_symb
% 3.78/0.99  --inst_solver_per_active                1400
% 3.78/0.99  --inst_solver_calls_frac                1.
% 3.78/0.99  --inst_passive_queue_type               priority_queues
% 3.78/0.99  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 3.78/0.99  --inst_passive_queues_freq              [25;2]
% 3.78/0.99  --inst_dismatching                      true
% 3.78/0.99  --inst_eager_unprocessed_to_passive     true
% 3.78/0.99  --inst_prop_sim_given                   true
% 3.78/0.99  --inst_prop_sim_new                     false
% 3.78/0.99  --inst_subs_new                         false
% 3.78/0.99  --inst_eq_res_simp                      false
% 3.78/0.99  --inst_subs_given                       false
% 3.78/0.99  --inst_orphan_elimination               true
% 3.78/0.99  --inst_learning_loop_flag               true
% 3.78/0.99  --inst_learning_start                   3000
% 3.78/0.99  --inst_learning_factor                  2
% 3.78/0.99  --inst_start_prop_sim_after_learn       3
% 3.78/0.99  --inst_sel_renew                        solver
% 3.78/0.99  --inst_lit_activity_flag                true
% 3.78/0.99  --inst_restr_to_given                   false
% 3.78/0.99  --inst_activity_threshold               500
% 3.78/0.99  --inst_out_proof                        true
% 3.78/0.99  
% 3.78/0.99  ------ Resolution Options
% 3.78/0.99  
% 3.78/0.99  --resolution_flag                       true
% 3.78/0.99  --res_lit_sel                           adaptive
% 3.78/0.99  --res_lit_sel_side                      none
% 3.78/0.99  --res_ordering                          kbo
% 3.78/0.99  --res_to_prop_solver                    active
% 3.78/0.99  --res_prop_simpl_new                    false
% 3.78/0.99  --res_prop_simpl_given                  true
% 3.78/0.99  --res_passive_queue_type                priority_queues
% 3.78/0.99  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 3.78/0.99  --res_passive_queues_freq               [15;5]
% 3.78/0.99  --res_forward_subs                      full
% 3.78/0.99  --res_backward_subs                     full
% 3.78/0.99  --res_forward_subs_resolution           true
% 3.78/0.99  --res_backward_subs_resolution          true
% 3.78/0.99  --res_orphan_elimination                true
% 3.78/0.99  --res_time_limit                        2.
% 3.78/0.99  --res_out_proof                         true
% 3.78/0.99  
% 3.78/0.99  ------ Superposition Options
% 3.78/0.99  
% 3.78/0.99  --superposition_flag                    true
% 3.78/0.99  --sup_passive_queue_type                priority_queues
% 3.78/0.99  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 3.78/0.99  --sup_passive_queues_freq               [8;1;4]
% 3.78/0.99  --demod_completeness_check              fast
% 3.78/0.99  --demod_use_ground                      true
% 3.78/0.99  --sup_to_prop_solver                    passive
% 3.78/0.99  --sup_prop_simpl_new                    true
% 3.78/0.99  --sup_prop_simpl_given                  true
% 3.78/0.99  --sup_fun_splitting                     false
% 3.78/0.99  --sup_smt_interval                      50000
% 3.78/0.99  
% 3.78/0.99  ------ Superposition Simplification Setup
% 3.78/0.99  
% 3.78/0.99  --sup_indices_passive                   []
% 3.78/0.99  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.78/0.99  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.78/0.99  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.78/0.99  --sup_full_triv                         [TrivRules;PropSubs]
% 3.78/0.99  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.78/0.99  --sup_full_bw                           [BwDemod]
% 3.78/0.99  --sup_immed_triv                        [TrivRules]
% 3.78/0.99  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 3.78/0.99  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.78/0.99  --sup_immed_bw_main                     []
% 3.78/0.99  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 3.78/0.99  --sup_input_triv                        [Unflattening;TrivRules]
% 3.78/0.99  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.78/0.99  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 3.78/0.99  
% 3.78/0.99  ------ Combination Options
% 3.78/0.99  
% 3.78/0.99  --comb_res_mult                         3
% 3.78/0.99  --comb_sup_mult                         2
% 3.78/0.99  --comb_inst_mult                        10
% 3.78/0.99  
% 3.78/0.99  ------ Debug Options
% 3.78/0.99  
% 3.78/0.99  --dbg_backtrace                         false
% 3.78/0.99  --dbg_dump_prop_clauses                 false
% 3.78/0.99  --dbg_dump_prop_clauses_file            -
% 3.78/0.99  --dbg_out_stat                          false
% 3.78/0.99  ------ Parsing...
% 3.78/0.99  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 3.78/0.99  
% 3.78/0.99  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe:1:0s pe:2:0s pe:4:0s pe_e  sf_s  rm: 7 0s  sf_e  pe_s  pe_e 
% 3.78/0.99  
% 3.78/0.99  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 3.78/0.99  
% 3.78/0.99  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 3.78/0.99  ------ Proving...
% 3.78/0.99  ------ Problem Properties 
% 3.78/0.99  
% 3.78/0.99  
% 3.78/0.99  clauses                                 34
% 3.78/0.99  conjectures                             3
% 3.78/0.99  EPR                                     5
% 3.78/0.99  Horn                                    21
% 3.78/0.99  unary                                   9
% 3.78/0.99  binary                                  4
% 3.78/0.99  lits                                    93
% 3.78/0.99  lits eq                                 11
% 3.78/0.99  fd_pure                                 0
% 3.78/0.99  fd_pseudo                               0
% 3.78/0.99  fd_cond                                 3
% 3.78/0.99  fd_pseudo_cond                          3
% 3.78/0.99  AC symbols                              0
% 3.78/0.99  
% 3.78/0.99  ------ Schedule dynamic 5 is on 
% 3.78/0.99  
% 3.78/0.99  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" Time Limit: 10.
% 3.78/0.99  
% 3.78/0.99  
% 3.78/0.99  ------ 
% 3.78/0.99  Current options:
% 3.78/0.99  ------ 
% 3.78/0.99  
% 3.78/0.99  ------ Input Options
% 3.78/0.99  
% 3.78/0.99  --out_options                           all
% 3.78/0.99  --tptp_safe_out                         true
% 3.78/0.99  --problem_path                          ""
% 3.78/0.99  --include_path                          ""
% 3.78/0.99  --clausifier                            res/vclausify_rel
% 3.78/0.99  --clausifier_options                    --mode clausify
% 3.78/0.99  --stdin                                 false
% 3.78/0.99  --stats_out                             all
% 3.78/0.99  
% 3.78/0.99  ------ General Options
% 3.78/0.99  
% 3.78/0.99  --fof                                   false
% 3.78/0.99  --time_out_real                         305.
% 3.78/0.99  --time_out_virtual                      -1.
% 3.78/0.99  --symbol_type_check                     false
% 3.78/0.99  --clausify_out                          false
% 3.78/0.99  --sig_cnt_out                           false
% 3.78/0.99  --trig_cnt_out                          false
% 3.78/0.99  --trig_cnt_out_tolerance                1.
% 3.78/0.99  --trig_cnt_out_sk_spl                   false
% 3.78/0.99  --abstr_cl_out                          false
% 3.78/0.99  
% 3.78/0.99  ------ Global Options
% 3.78/0.99  
% 3.78/0.99  --schedule                              default
% 3.78/0.99  --add_important_lit                     false
% 3.78/0.99  --prop_solver_per_cl                    1000
% 3.78/0.99  --min_unsat_core                        false
% 3.78/0.99  --soft_assumptions                      false
% 3.78/0.99  --soft_lemma_size                       3
% 3.78/0.99  --prop_impl_unit_size                   0
% 3.78/0.99  --prop_impl_unit                        []
% 3.78/0.99  --share_sel_clauses                     true
% 3.78/0.99  --reset_solvers                         false
% 3.78/0.99  --bc_imp_inh                            [conj_cone]
% 3.78/0.99  --conj_cone_tolerance                   3.
% 3.78/0.99  --extra_neg_conj                        none
% 3.78/0.99  --large_theory_mode                     true
% 3.78/0.99  --prolific_symb_bound                   200
% 3.78/0.99  --lt_threshold                          2000
% 3.78/0.99  --clause_weak_htbl                      true
% 3.78/0.99  --gc_record_bc_elim                     false
% 3.78/0.99  
% 3.78/0.99  ------ Preprocessing Options
% 3.78/0.99  
% 3.78/0.99  --preprocessing_flag                    true
% 3.78/0.99  --time_out_prep_mult                    0.1
% 3.78/0.99  --splitting_mode                        input
% 3.78/0.99  --splitting_grd                         true
% 3.78/0.99  --splitting_cvd                         false
% 3.78/0.99  --splitting_cvd_svl                     false
% 3.78/0.99  --splitting_nvd                         32
% 3.78/0.99  --sub_typing                            true
% 3.78/0.99  --prep_gs_sim                           true
% 3.78/0.99  --prep_unflatten                        true
% 3.78/0.99  --prep_res_sim                          true
% 3.78/0.99  --prep_upred                            true
% 3.78/0.99  --prep_sem_filter                       exhaustive
% 3.78/0.99  --prep_sem_filter_out                   false
% 3.78/0.99  --pred_elim                             true
% 3.78/0.99  --res_sim_input                         true
% 3.78/0.99  --eq_ax_congr_red                       true
% 3.78/0.99  --pure_diseq_elim                       true
% 3.78/0.99  --brand_transform                       false
% 3.78/0.99  --non_eq_to_eq                          false
% 3.78/0.99  --prep_def_merge                        true
% 3.78/0.99  --prep_def_merge_prop_impl              false
% 3.78/0.99  --prep_def_merge_mbd                    true
% 3.78/0.99  --prep_def_merge_tr_red                 false
% 3.78/0.99  --prep_def_merge_tr_cl                  false
% 3.78/0.99  --smt_preprocessing                     true
% 3.78/0.99  --smt_ac_axioms                         fast
% 3.78/0.99  --preprocessed_out                      false
% 3.78/0.99  --preprocessed_stats                    false
% 3.78/0.99  
% 3.78/0.99  ------ Abstraction refinement Options
% 3.78/0.99  
% 3.78/0.99  --abstr_ref                             []
% 3.78/0.99  --abstr_ref_prep                        false
% 3.78/0.99  --abstr_ref_until_sat                   false
% 3.78/0.99  --abstr_ref_sig_restrict                funpre
% 3.78/0.99  --abstr_ref_af_restrict_to_split_sk     false
% 3.78/0.99  --abstr_ref_under                       []
% 3.78/0.99  
% 3.78/0.99  ------ SAT Options
% 3.78/0.99  
% 3.78/0.99  --sat_mode                              false
% 3.78/0.99  --sat_fm_restart_options                ""
% 3.78/0.99  --sat_gr_def                            false
% 3.78/0.99  --sat_epr_types                         true
% 3.78/0.99  --sat_non_cyclic_types                  false
% 3.78/0.99  --sat_finite_models                     false
% 3.78/0.99  --sat_fm_lemmas                         false
% 3.78/0.99  --sat_fm_prep                           false
% 3.78/0.99  --sat_fm_uc_incr                        true
% 3.78/0.99  --sat_out_model                         small
% 3.78/0.99  --sat_out_clauses                       false
% 3.78/0.99  
% 3.78/0.99  ------ QBF Options
% 3.78/0.99  
% 3.78/0.99  --qbf_mode                              false
% 3.78/0.99  --qbf_elim_univ                         false
% 3.78/0.99  --qbf_dom_inst                          none
% 3.78/0.99  --qbf_dom_pre_inst                      false
% 3.78/0.99  --qbf_sk_in                             false
% 3.78/0.99  --qbf_pred_elim                         true
% 3.78/0.99  --qbf_split                             512
% 3.78/0.99  
% 3.78/0.99  ------ BMC1 Options
% 3.78/0.99  
% 3.78/0.99  --bmc1_incremental                      false
% 3.78/0.99  --bmc1_axioms                           reachable_all
% 3.78/0.99  --bmc1_min_bound                        0
% 3.78/0.99  --bmc1_max_bound                        -1
% 3.78/0.99  --bmc1_max_bound_default                -1
% 3.78/0.99  --bmc1_symbol_reachability              true
% 3.78/0.99  --bmc1_property_lemmas                  false
% 3.78/0.99  --bmc1_k_induction                      false
% 3.78/0.99  --bmc1_non_equiv_states                 false
% 3.78/0.99  --bmc1_deadlock                         false
% 3.78/0.99  --bmc1_ucm                              false
% 3.78/0.99  --bmc1_add_unsat_core                   none
% 3.78/0.99  --bmc1_unsat_core_children              false
% 3.78/0.99  --bmc1_unsat_core_extrapolate_axioms    false
% 3.78/0.99  --bmc1_out_stat                         full
% 3.78/0.99  --bmc1_ground_init                      false
% 3.78/0.99  --bmc1_pre_inst_next_state              false
% 3.78/0.99  --bmc1_pre_inst_state                   false
% 3.78/0.99  --bmc1_pre_inst_reach_state             false
% 3.78/0.99  --bmc1_out_unsat_core                   false
% 3.78/0.99  --bmc1_aig_witness_out                  false
% 3.78/0.99  --bmc1_verbose                          false
% 3.78/0.99  --bmc1_dump_clauses_tptp                false
% 3.78/0.99  --bmc1_dump_unsat_core_tptp             false
% 3.78/0.99  --bmc1_dump_file                        -
% 3.78/0.99  --bmc1_ucm_expand_uc_limit              128
% 3.78/0.99  --bmc1_ucm_n_expand_iterations          6
% 3.78/0.99  --bmc1_ucm_extend_mode                  1
% 3.78/0.99  --bmc1_ucm_init_mode                    2
% 3.78/0.99  --bmc1_ucm_cone_mode                    none
% 3.78/0.99  --bmc1_ucm_reduced_relation_type        0
% 3.78/0.99  --bmc1_ucm_relax_model                  4
% 3.78/0.99  --bmc1_ucm_full_tr_after_sat            true
% 3.78/0.99  --bmc1_ucm_expand_neg_assumptions       false
% 3.78/0.99  --bmc1_ucm_layered_model                none
% 3.78/0.99  --bmc1_ucm_max_lemma_size               10
% 3.78/0.99  
% 3.78/0.99  ------ AIG Options
% 3.78/0.99  
% 3.78/0.99  --aig_mode                              false
% 3.78/0.99  
% 3.78/0.99  ------ Instantiation Options
% 3.78/0.99  
% 3.78/0.99  --instantiation_flag                    true
% 3.78/0.99  --inst_sos_flag                         false
% 3.78/0.99  --inst_sos_phase                        true
% 3.78/0.99  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 3.78/0.99  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 3.78/0.99  --inst_lit_sel_side                     none
% 3.78/0.99  --inst_solver_per_active                1400
% 3.78/0.99  --inst_solver_calls_frac                1.
% 3.78/0.99  --inst_passive_queue_type               priority_queues
% 3.78/0.99  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 3.78/0.99  --inst_passive_queues_freq              [25;2]
% 3.78/0.99  --inst_dismatching                      true
% 3.78/0.99  --inst_eager_unprocessed_to_passive     true
% 3.78/0.99  --inst_prop_sim_given                   true
% 3.78/0.99  --inst_prop_sim_new                     false
% 3.78/0.99  --inst_subs_new                         false
% 3.78/0.99  --inst_eq_res_simp                      false
% 3.78/0.99  --inst_subs_given                       false
% 3.78/0.99  --inst_orphan_elimination               true
% 3.78/0.99  --inst_learning_loop_flag               true
% 3.78/0.99  --inst_learning_start                   3000
% 3.78/0.99  --inst_learning_factor                  2
% 3.78/0.99  --inst_start_prop_sim_after_learn       3
% 3.78/0.99  --inst_sel_renew                        solver
% 3.78/0.99  --inst_lit_activity_flag                true
% 3.78/0.99  --inst_restr_to_given                   false
% 3.78/0.99  --inst_activity_threshold               500
% 3.78/0.99  --inst_out_proof                        true
% 3.78/0.99  
% 3.78/0.99  ------ Resolution Options
% 3.78/0.99  
% 3.78/0.99  --resolution_flag                       false
% 3.78/0.99  --res_lit_sel                           adaptive
% 3.78/0.99  --res_lit_sel_side                      none
% 3.78/0.99  --res_ordering                          kbo
% 3.78/0.99  --res_to_prop_solver                    active
% 3.78/0.99  --res_prop_simpl_new                    false
% 3.78/0.99  --res_prop_simpl_given                  true
% 3.78/0.99  --res_passive_queue_type                priority_queues
% 3.78/0.99  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 3.78/0.99  --res_passive_queues_freq               [15;5]
% 3.78/0.99  --res_forward_subs                      full
% 3.78/0.99  --res_backward_subs                     full
% 3.78/0.99  --res_forward_subs_resolution           true
% 3.78/0.99  --res_backward_subs_resolution          true
% 3.78/0.99  --res_orphan_elimination                true
% 3.78/0.99  --res_time_limit                        2.
% 3.78/0.99  --res_out_proof                         true
% 3.78/0.99  
% 3.78/0.99  ------ Superposition Options
% 3.78/0.99  
% 3.78/0.99  --superposition_flag                    true
% 3.78/0.99  --sup_passive_queue_type                priority_queues
% 3.78/0.99  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 3.78/0.99  --sup_passive_queues_freq               [8;1;4]
% 3.78/0.99  --demod_completeness_check              fast
% 3.78/0.99  --demod_use_ground                      true
% 3.78/0.99  --sup_to_prop_solver                    passive
% 3.78/0.99  --sup_prop_simpl_new                    true
% 3.78/0.99  --sup_prop_simpl_given                  true
% 3.78/0.99  --sup_fun_splitting                     false
% 3.78/0.99  --sup_smt_interval                      50000
% 3.78/0.99  
% 3.78/0.99  ------ Superposition Simplification Setup
% 3.78/0.99  
% 3.78/0.99  --sup_indices_passive                   []
% 3.78/0.99  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.78/0.99  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.78/0.99  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.78/0.99  --sup_full_triv                         [TrivRules;PropSubs]
% 3.78/0.99  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.78/0.99  --sup_full_bw                           [BwDemod]
% 3.78/0.99  --sup_immed_triv                        [TrivRules]
% 3.78/0.99  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 3.78/0.99  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.78/0.99  --sup_immed_bw_main                     []
% 3.78/0.99  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 3.78/0.99  --sup_input_triv                        [Unflattening;TrivRules]
% 3.78/0.99  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.78/0.99  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 3.78/0.99  
% 3.78/0.99  ------ Combination Options
% 3.78/0.99  
% 3.78/0.99  --comb_res_mult                         3
% 3.78/0.99  --comb_sup_mult                         2
% 3.78/0.99  --comb_inst_mult                        10
% 3.78/0.99  
% 3.78/0.99  ------ Debug Options
% 3.78/0.99  
% 3.78/0.99  --dbg_backtrace                         false
% 3.78/0.99  --dbg_dump_prop_clauses                 false
% 3.78/0.99  --dbg_dump_prop_clauses_file            -
% 3.78/0.99  --dbg_out_stat                          false
% 3.78/0.99  
% 3.78/0.99  
% 3.78/0.99  
% 3.78/0.99  
% 3.78/0.99  ------ Proving...
% 3.78/0.99  
% 3.78/0.99  
% 3.78/0.99  % SZS status Theorem for theBenchmark.p
% 3.78/0.99  
% 3.78/0.99  % SZS output start CNFRefutation for theBenchmark.p
% 3.78/0.99  
% 3.78/0.99  fof(f4,axiom,(
% 3.78/0.99    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(X0)) => (! [X3] : (m1_subset_1(X3,X0) => (r2_hidden(X3,X1) <=> r2_hidden(X3,X2))) => X1 = X2)))),
% 3.78/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.78/0.99  
% 3.78/0.99  fof(f22,plain,(
% 3.78/0.99    ! [X0,X1] : (! [X2] : ((X1 = X2 | ? [X3] : ((r2_hidden(X3,X1) <~> r2_hidden(X3,X2)) & m1_subset_1(X3,X0))) | ~m1_subset_1(X2,k1_zfmisc_1(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 3.78/0.99    inference(ennf_transformation,[],[f4])).
% 3.78/0.99  
% 3.78/0.99  fof(f23,plain,(
% 3.78/0.99    ! [X0,X1] : (! [X2] : (X1 = X2 | ? [X3] : ((r2_hidden(X3,X1) <~> r2_hidden(X3,X2)) & m1_subset_1(X3,X0)) | ~m1_subset_1(X2,k1_zfmisc_1(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 3.78/0.99    inference(flattening,[],[f22])).
% 3.78/0.99  
% 3.78/0.99  fof(f45,plain,(
% 3.78/0.99    ! [X0,X1] : (! [X2] : (X1 = X2 | ? [X3] : (((~r2_hidden(X3,X2) | ~r2_hidden(X3,X1)) & (r2_hidden(X3,X2) | r2_hidden(X3,X1))) & m1_subset_1(X3,X0)) | ~m1_subset_1(X2,k1_zfmisc_1(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 3.78/0.99    inference(nnf_transformation,[],[f23])).
% 3.78/0.99  
% 3.78/0.99  fof(f46,plain,(
% 3.78/0.99    ! [X0,X1] : (! [X2] : (X1 = X2 | ? [X3] : ((~r2_hidden(X3,X2) | ~r2_hidden(X3,X1)) & (r2_hidden(X3,X2) | r2_hidden(X3,X1)) & m1_subset_1(X3,X0)) | ~m1_subset_1(X2,k1_zfmisc_1(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 3.78/0.99    inference(flattening,[],[f45])).
% 3.78/0.99  
% 3.78/0.99  fof(f47,plain,(
% 3.78/0.99    ! [X2,X1,X0] : (? [X3] : ((~r2_hidden(X3,X2) | ~r2_hidden(X3,X1)) & (r2_hidden(X3,X2) | r2_hidden(X3,X1)) & m1_subset_1(X3,X0)) => ((~r2_hidden(sK1(X0,X1,X2),X2) | ~r2_hidden(sK1(X0,X1,X2),X1)) & (r2_hidden(sK1(X0,X1,X2),X2) | r2_hidden(sK1(X0,X1,X2),X1)) & m1_subset_1(sK1(X0,X1,X2),X0)))),
% 3.78/0.99    introduced(choice_axiom,[])).
% 3.78/0.99  
% 3.78/0.99  fof(f48,plain,(
% 3.78/0.99    ! [X0,X1] : (! [X2] : (X1 = X2 | ((~r2_hidden(sK1(X0,X1,X2),X2) | ~r2_hidden(sK1(X0,X1,X2),X1)) & (r2_hidden(sK1(X0,X1,X2),X2) | r2_hidden(sK1(X0,X1,X2),X1)) & m1_subset_1(sK1(X0,X1,X2),X0)) | ~m1_subset_1(X2,k1_zfmisc_1(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 3.78/0.99    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1])],[f46,f47])).
% 3.78/0.99  
% 3.78/0.99  fof(f75,plain,(
% 3.78/0.99    ( ! [X2,X0,X1] : (X1 = X2 | m1_subset_1(sK1(X0,X1,X2),X0) | ~m1_subset_1(X2,k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 3.78/0.99    inference(cnf_transformation,[],[f48])).
% 3.78/0.99  
% 3.78/0.99  fof(f15,conjecture,(
% 3.78/0.99    ! [X0] : ((l1_orders_2(X0) & v1_yellow_0(X0) & v5_orders_2(X0) & v4_orders_2(X0) & v3_orders_2(X0) & ~v2_struct_0(X0)) => ! [X1] : ((m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & v13_waybel_0(X1,X0) & v2_waybel_0(X1,X0) & ~v1_xboole_0(X1)) => (v1_subset_1(X1,u1_struct_0(X0)) <=> ~r2_hidden(k3_yellow_0(X0),X1))))),
% 3.78/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.78/0.99  
% 3.78/0.99  fof(f16,negated_conjecture,(
% 3.78/0.99    ~! [X0] : ((l1_orders_2(X0) & v1_yellow_0(X0) & v5_orders_2(X0) & v4_orders_2(X0) & v3_orders_2(X0) & ~v2_struct_0(X0)) => ! [X1] : ((m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & v13_waybel_0(X1,X0) & v2_waybel_0(X1,X0) & ~v1_xboole_0(X1)) => (v1_subset_1(X1,u1_struct_0(X0)) <=> ~r2_hidden(k3_yellow_0(X0),X1))))),
% 3.78/0.99    inference(negated_conjecture,[],[f15])).
% 3.78/0.99  
% 3.78/0.99  fof(f17,plain,(
% 3.78/0.99    ~! [X0] : ((l1_orders_2(X0) & v1_yellow_0(X0) & v5_orders_2(X0) & v4_orders_2(X0) & v3_orders_2(X0) & ~v2_struct_0(X0)) => ! [X1] : ((m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & v13_waybel_0(X1,X0) & ~v1_xboole_0(X1)) => (v1_subset_1(X1,u1_struct_0(X0)) <=> ~r2_hidden(k3_yellow_0(X0),X1))))),
% 3.78/0.99    inference(pure_predicate_removal,[],[f16])).
% 3.78/0.99  
% 3.78/0.99  fof(f18,plain,(
% 3.78/0.99    ~! [X0] : ((l1_orders_2(X0) & v1_yellow_0(X0) & v5_orders_2(X0) & v3_orders_2(X0) & ~v2_struct_0(X0)) => ! [X1] : ((m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & v13_waybel_0(X1,X0) & ~v1_xboole_0(X1)) => (v1_subset_1(X1,u1_struct_0(X0)) <=> ~r2_hidden(k3_yellow_0(X0),X1))))),
% 3.78/0.99    inference(pure_predicate_removal,[],[f17])).
% 3.78/0.99  
% 3.78/0.99  fof(f19,plain,(
% 3.78/0.99    ~! [X0] : ((l1_orders_2(X0) & v1_yellow_0(X0) & v5_orders_2(X0) & ~v2_struct_0(X0)) => ! [X1] : ((m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & v13_waybel_0(X1,X0) & ~v1_xboole_0(X1)) => (v1_subset_1(X1,u1_struct_0(X0)) <=> ~r2_hidden(k3_yellow_0(X0),X1))))),
% 3.78/0.99    inference(pure_predicate_removal,[],[f18])).
% 3.78/0.99  
% 3.78/0.99  fof(f39,plain,(
% 3.78/0.99    ? [X0] : (? [X1] : ((v1_subset_1(X1,u1_struct_0(X0)) <~> ~r2_hidden(k3_yellow_0(X0),X1)) & (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & v13_waybel_0(X1,X0) & ~v1_xboole_0(X1))) & (l1_orders_2(X0) & v1_yellow_0(X0) & v5_orders_2(X0) & ~v2_struct_0(X0)))),
% 3.78/0.99    inference(ennf_transformation,[],[f19])).
% 3.78/0.99  
% 3.78/0.99  fof(f40,plain,(
% 3.78/0.99    ? [X0] : (? [X1] : ((v1_subset_1(X1,u1_struct_0(X0)) <~> ~r2_hidden(k3_yellow_0(X0),X1)) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & v13_waybel_0(X1,X0) & ~v1_xboole_0(X1)) & l1_orders_2(X0) & v1_yellow_0(X0) & v5_orders_2(X0) & ~v2_struct_0(X0))),
% 3.78/0.99    inference(flattening,[],[f39])).
% 3.78/0.99  
% 3.78/0.99  fof(f66,plain,(
% 3.78/0.99    ? [X0] : (? [X1] : (((r2_hidden(k3_yellow_0(X0),X1) | ~v1_subset_1(X1,u1_struct_0(X0))) & (~r2_hidden(k3_yellow_0(X0),X1) | v1_subset_1(X1,u1_struct_0(X0)))) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & v13_waybel_0(X1,X0) & ~v1_xboole_0(X1)) & l1_orders_2(X0) & v1_yellow_0(X0) & v5_orders_2(X0) & ~v2_struct_0(X0))),
% 3.78/0.99    inference(nnf_transformation,[],[f40])).
% 3.78/0.99  
% 3.78/0.99  fof(f67,plain,(
% 3.78/0.99    ? [X0] : (? [X1] : ((r2_hidden(k3_yellow_0(X0),X1) | ~v1_subset_1(X1,u1_struct_0(X0))) & (~r2_hidden(k3_yellow_0(X0),X1) | v1_subset_1(X1,u1_struct_0(X0))) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & v13_waybel_0(X1,X0) & ~v1_xboole_0(X1)) & l1_orders_2(X0) & v1_yellow_0(X0) & v5_orders_2(X0) & ~v2_struct_0(X0))),
% 3.78/0.99    inference(flattening,[],[f66])).
% 3.78/0.99  
% 3.78/0.99  fof(f69,plain,(
% 3.78/0.99    ( ! [X0] : (? [X1] : ((r2_hidden(k3_yellow_0(X0),X1) | ~v1_subset_1(X1,u1_struct_0(X0))) & (~r2_hidden(k3_yellow_0(X0),X1) | v1_subset_1(X1,u1_struct_0(X0))) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & v13_waybel_0(X1,X0) & ~v1_xboole_0(X1)) => ((r2_hidden(k3_yellow_0(X0),sK8) | ~v1_subset_1(sK8,u1_struct_0(X0))) & (~r2_hidden(k3_yellow_0(X0),sK8) | v1_subset_1(sK8,u1_struct_0(X0))) & m1_subset_1(sK8,k1_zfmisc_1(u1_struct_0(X0))) & v13_waybel_0(sK8,X0) & ~v1_xboole_0(sK8))) )),
% 3.78/0.99    introduced(choice_axiom,[])).
% 3.78/0.99  
% 3.78/0.99  fof(f68,plain,(
% 3.78/0.99    ? [X0] : (? [X1] : ((r2_hidden(k3_yellow_0(X0),X1) | ~v1_subset_1(X1,u1_struct_0(X0))) & (~r2_hidden(k3_yellow_0(X0),X1) | v1_subset_1(X1,u1_struct_0(X0))) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & v13_waybel_0(X1,X0) & ~v1_xboole_0(X1)) & l1_orders_2(X0) & v1_yellow_0(X0) & v5_orders_2(X0) & ~v2_struct_0(X0)) => (? [X1] : ((r2_hidden(k3_yellow_0(sK7),X1) | ~v1_subset_1(X1,u1_struct_0(sK7))) & (~r2_hidden(k3_yellow_0(sK7),X1) | v1_subset_1(X1,u1_struct_0(sK7))) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK7))) & v13_waybel_0(X1,sK7) & ~v1_xboole_0(X1)) & l1_orders_2(sK7) & v1_yellow_0(sK7) & v5_orders_2(sK7) & ~v2_struct_0(sK7))),
% 3.78/0.99    introduced(choice_axiom,[])).
% 3.78/0.99  
% 3.78/0.99  fof(f70,plain,(
% 3.78/0.99    ((r2_hidden(k3_yellow_0(sK7),sK8) | ~v1_subset_1(sK8,u1_struct_0(sK7))) & (~r2_hidden(k3_yellow_0(sK7),sK8) | v1_subset_1(sK8,u1_struct_0(sK7))) & m1_subset_1(sK8,k1_zfmisc_1(u1_struct_0(sK7))) & v13_waybel_0(sK8,sK7) & ~v1_xboole_0(sK8)) & l1_orders_2(sK7) & v1_yellow_0(sK7) & v5_orders_2(sK7) & ~v2_struct_0(sK7)),
% 3.78/0.99    inference(skolemisation,[status(esa),new_symbols(skolem,[sK7,sK8])],[f67,f69,f68])).
% 3.78/0.99  
% 3.78/0.99  fof(f108,plain,(
% 3.78/0.99    m1_subset_1(sK8,k1_zfmisc_1(u1_struct_0(sK7)))),
% 3.78/0.99    inference(cnf_transformation,[],[f70])).
% 3.78/0.99  
% 3.78/0.99  fof(f3,axiom,(
% 3.78/0.99    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => ! [X2] : (r2_hidden(X2,X1) => r2_hidden(X2,X0)))),
% 3.78/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.78/0.99  
% 3.78/0.99  fof(f21,plain,(
% 3.78/0.99    ! [X0,X1] : (! [X2] : (r2_hidden(X2,X0) | ~r2_hidden(X2,X1)) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 3.78/0.99    inference(ennf_transformation,[],[f3])).
% 3.78/0.99  
% 3.78/0.99  fof(f74,plain,(
% 3.78/0.99    ( ! [X2,X0,X1] : (r2_hidden(X2,X0) | ~r2_hidden(X2,X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 3.78/0.99    inference(cnf_transformation,[],[f21])).
% 3.78/0.99  
% 3.78/0.99  fof(f1,axiom,(
% 3.78/0.99    ! [X0] : (v1_xboole_0(X0) <=> ! [X1] : ~r2_hidden(X1,X0))),
% 3.78/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.78/0.99  
% 3.78/0.99  fof(f41,plain,(
% 3.78/0.99    ! [X0] : ((v1_xboole_0(X0) | ? [X1] : r2_hidden(X1,X0)) & (! [X1] : ~r2_hidden(X1,X0) | ~v1_xboole_0(X0)))),
% 3.78/0.99    inference(nnf_transformation,[],[f1])).
% 3.78/0.99  
% 3.78/0.99  fof(f42,plain,(
% 3.78/0.99    ! [X0] : ((v1_xboole_0(X0) | ? [X1] : r2_hidden(X1,X0)) & (! [X2] : ~r2_hidden(X2,X0) | ~v1_xboole_0(X0)))),
% 3.78/0.99    inference(rectify,[],[f41])).
% 3.78/0.99  
% 3.78/0.99  fof(f43,plain,(
% 3.78/0.99    ! [X0] : (? [X1] : r2_hidden(X1,X0) => r2_hidden(sK0(X0),X0))),
% 3.78/0.99    introduced(choice_axiom,[])).
% 3.78/0.99  
% 3.78/0.99  fof(f44,plain,(
% 3.78/0.99    ! [X0] : ((v1_xboole_0(X0) | r2_hidden(sK0(X0),X0)) & (! [X2] : ~r2_hidden(X2,X0) | ~v1_xboole_0(X0)))),
% 3.78/0.99    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f42,f43])).
% 3.78/0.99  
% 3.78/0.99  fof(f72,plain,(
% 3.78/0.99    ( ! [X0] : (v1_xboole_0(X0) | r2_hidden(sK0(X0),X0)) )),
% 3.78/0.99    inference(cnf_transformation,[],[f44])).
% 3.78/0.99  
% 3.78/0.99  fof(f5,axiom,(
% 3.78/0.99    ! [X0] : ? [X1] : (~v1_subset_1(X1,X0) & m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 3.78/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.78/0.99  
% 3.78/0.99  fof(f49,plain,(
% 3.78/0.99    ! [X0] : (? [X1] : (~v1_subset_1(X1,X0) & m1_subset_1(X1,k1_zfmisc_1(X0))) => (~v1_subset_1(sK2(X0),X0) & m1_subset_1(sK2(X0),k1_zfmisc_1(X0))))),
% 3.78/0.99    introduced(choice_axiom,[])).
% 3.78/0.99  
% 3.78/0.99  fof(f50,plain,(
% 3.78/0.99    ! [X0] : (~v1_subset_1(sK2(X0),X0) & m1_subset_1(sK2(X0),k1_zfmisc_1(X0)))),
% 3.78/0.99    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2])],[f5,f49])).
% 3.78/0.99  
% 3.78/0.99  fof(f78,plain,(
% 3.78/0.99    ( ! [X0] : (m1_subset_1(sK2(X0),k1_zfmisc_1(X0))) )),
% 3.78/0.99    inference(cnf_transformation,[],[f50])).
% 3.78/0.99  
% 3.78/0.99  fof(f79,plain,(
% 3.78/0.99    ( ! [X0] : (~v1_subset_1(sK2(X0),X0)) )),
% 3.78/0.99    inference(cnf_transformation,[],[f50])).
% 3.78/0.99  
% 3.78/0.99  fof(f14,axiom,(
% 3.78/0.99    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => (v1_subset_1(X1,X0) <=> X0 != X1))),
% 3.78/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.78/0.99  
% 3.78/0.99  fof(f38,plain,(
% 3.78/0.99    ! [X0,X1] : ((v1_subset_1(X1,X0) <=> X0 != X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 3.78/0.99    inference(ennf_transformation,[],[f14])).
% 3.78/0.99  
% 3.78/0.99  fof(f65,plain,(
% 3.78/0.99    ! [X0,X1] : (((v1_subset_1(X1,X0) | X0 = X1) & (X0 != X1 | ~v1_subset_1(X1,X0))) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 3.78/0.99    inference(nnf_transformation,[],[f38])).
% 3.78/0.99  
% 3.78/0.99  fof(f101,plain,(
% 3.78/0.99    ( ! [X0,X1] : (v1_subset_1(X1,X0) | X0 = X1 | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 3.78/0.99    inference(cnf_transformation,[],[f65])).
% 3.78/0.99  
% 3.78/0.99  fof(f7,axiom,(
% 3.78/0.99    ! [X0,X1,X2] : ((m1_subset_1(X1,k1_zfmisc_1(X2)) & r2_hidden(X0,X1)) => m1_subset_1(X0,X2))),
% 3.78/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.78/0.99  
% 3.78/0.99  fof(f26,plain,(
% 3.78/0.99    ! [X0,X1,X2] : (m1_subset_1(X0,X2) | (~m1_subset_1(X1,k1_zfmisc_1(X2)) | ~r2_hidden(X0,X1)))),
% 3.78/0.99    inference(ennf_transformation,[],[f7])).
% 3.78/0.99  
% 3.78/0.99  fof(f27,plain,(
% 3.78/0.99    ! [X0,X1,X2] : (m1_subset_1(X0,X2) | ~m1_subset_1(X1,k1_zfmisc_1(X2)) | ~r2_hidden(X0,X1))),
% 3.78/0.99    inference(flattening,[],[f26])).
% 3.78/0.99  
% 3.78/0.99  fof(f81,plain,(
% 3.78/0.99    ( ! [X2,X0,X1] : (m1_subset_1(X0,X2) | ~m1_subset_1(X1,k1_zfmisc_1(X2)) | ~r2_hidden(X0,X1)) )),
% 3.78/0.99    inference(cnf_transformation,[],[f27])).
% 3.78/0.99  
% 3.78/0.99  fof(f8,axiom,(
% 3.78/0.99    ! [X0] : (l1_orders_2(X0) => ! [X1,X2] : (m1_subset_1(X2,u1_struct_0(X0)) => (r2_lattice3(X0,X1,X2) <=> ! [X3] : (m1_subset_1(X3,u1_struct_0(X0)) => (r2_hidden(X3,X1) => r1_orders_2(X0,X3,X2))))))),
% 3.78/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.78/0.99  
% 3.78/0.99  fof(f28,plain,(
% 3.78/0.99    ! [X0] : (! [X1,X2] : ((r2_lattice3(X0,X1,X2) <=> ! [X3] : ((r1_orders_2(X0,X3,X2) | ~r2_hidden(X3,X1)) | ~m1_subset_1(X3,u1_struct_0(X0)))) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~l1_orders_2(X0))),
% 3.78/0.99    inference(ennf_transformation,[],[f8])).
% 3.78/0.99  
% 3.78/0.99  fof(f29,plain,(
% 3.78/0.99    ! [X0] : (! [X1,X2] : ((r2_lattice3(X0,X1,X2) <=> ! [X3] : (r1_orders_2(X0,X3,X2) | ~r2_hidden(X3,X1) | ~m1_subset_1(X3,u1_struct_0(X0)))) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~l1_orders_2(X0))),
% 3.78/0.99    inference(flattening,[],[f28])).
% 3.78/0.99  
% 3.78/0.99  fof(f51,plain,(
% 3.78/0.99    ! [X0] : (! [X1,X2] : (((r2_lattice3(X0,X1,X2) | ? [X3] : (~r1_orders_2(X0,X3,X2) & r2_hidden(X3,X1) & m1_subset_1(X3,u1_struct_0(X0)))) & (! [X3] : (r1_orders_2(X0,X3,X2) | ~r2_hidden(X3,X1) | ~m1_subset_1(X3,u1_struct_0(X0))) | ~r2_lattice3(X0,X1,X2))) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~l1_orders_2(X0))),
% 3.78/0.99    inference(nnf_transformation,[],[f29])).
% 3.78/0.99  
% 3.78/0.99  fof(f52,plain,(
% 3.78/0.99    ! [X0] : (! [X1,X2] : (((r2_lattice3(X0,X1,X2) | ? [X3] : (~r1_orders_2(X0,X3,X2) & r2_hidden(X3,X1) & m1_subset_1(X3,u1_struct_0(X0)))) & (! [X4] : (r1_orders_2(X0,X4,X2) | ~r2_hidden(X4,X1) | ~m1_subset_1(X4,u1_struct_0(X0))) | ~r2_lattice3(X0,X1,X2))) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~l1_orders_2(X0))),
% 3.78/0.99    inference(rectify,[],[f51])).
% 3.78/0.99  
% 3.78/0.99  fof(f53,plain,(
% 3.78/0.99    ! [X2,X1,X0] : (? [X3] : (~r1_orders_2(X0,X3,X2) & r2_hidden(X3,X1) & m1_subset_1(X3,u1_struct_0(X0))) => (~r1_orders_2(X0,sK3(X0,X1,X2),X2) & r2_hidden(sK3(X0,X1,X2),X1) & m1_subset_1(sK3(X0,X1,X2),u1_struct_0(X0))))),
% 3.78/0.99    introduced(choice_axiom,[])).
% 3.78/0.99  
% 3.78/0.99  fof(f54,plain,(
% 3.78/0.99    ! [X0] : (! [X1,X2] : (((r2_lattice3(X0,X1,X2) | (~r1_orders_2(X0,sK3(X0,X1,X2),X2) & r2_hidden(sK3(X0,X1,X2),X1) & m1_subset_1(sK3(X0,X1,X2),u1_struct_0(X0)))) & (! [X4] : (r1_orders_2(X0,X4,X2) | ~r2_hidden(X4,X1) | ~m1_subset_1(X4,u1_struct_0(X0))) | ~r2_lattice3(X0,X1,X2))) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~l1_orders_2(X0))),
% 3.78/0.99    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3])],[f52,f53])).
% 3.78/0.99  
% 3.78/0.99  fof(f82,plain,(
% 3.78/0.99    ( ! [X4,X2,X0,X1] : (r1_orders_2(X0,X4,X2) | ~r2_hidden(X4,X1) | ~m1_subset_1(X4,u1_struct_0(X0)) | ~r2_lattice3(X0,X1,X2) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~l1_orders_2(X0)) )),
% 3.78/0.99    inference(cnf_transformation,[],[f54])).
% 3.78/0.99  
% 3.78/0.99  fof(f105,plain,(
% 3.78/0.99    l1_orders_2(sK7)),
% 3.78/0.99    inference(cnf_transformation,[],[f70])).
% 3.78/0.99  
% 3.78/0.99  fof(f106,plain,(
% 3.78/0.99    ~v1_xboole_0(sK8)),
% 3.78/0.99    inference(cnf_transformation,[],[f70])).
% 3.78/0.99  
% 3.78/0.99  fof(f71,plain,(
% 3.78/0.99    ( ! [X2,X0] : (~r2_hidden(X2,X0) | ~v1_xboole_0(X0)) )),
% 3.78/0.99    inference(cnf_transformation,[],[f44])).
% 3.78/0.99  
% 3.78/0.99  fof(f13,axiom,(
% 3.78/0.99    ! [X0] : (l1_orders_2(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => (v13_waybel_0(X1,X0) <=> ! [X2] : (m1_subset_1(X2,u1_struct_0(X0)) => ! [X3] : (m1_subset_1(X3,u1_struct_0(X0)) => ((r1_orders_2(X0,X2,X3) & r2_hidden(X2,X1)) => r2_hidden(X3,X1)))))))),
% 3.78/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.78/0.99  
% 3.78/0.99  fof(f36,plain,(
% 3.78/0.99    ! [X0] : (! [X1] : ((v13_waybel_0(X1,X0) <=> ! [X2] : (! [X3] : ((r2_hidden(X3,X1) | (~r1_orders_2(X0,X2,X3) | ~r2_hidden(X2,X1))) | ~m1_subset_1(X3,u1_struct_0(X0))) | ~m1_subset_1(X2,u1_struct_0(X0)))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_orders_2(X0))),
% 3.78/0.99    inference(ennf_transformation,[],[f13])).
% 3.78/0.99  
% 3.78/0.99  fof(f37,plain,(
% 3.78/0.99    ! [X0] : (! [X1] : ((v13_waybel_0(X1,X0) <=> ! [X2] : (! [X3] : (r2_hidden(X3,X1) | ~r1_orders_2(X0,X2,X3) | ~r2_hidden(X2,X1) | ~m1_subset_1(X3,u1_struct_0(X0))) | ~m1_subset_1(X2,u1_struct_0(X0)))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_orders_2(X0))),
% 3.78/0.99    inference(flattening,[],[f36])).
% 3.78/0.99  
% 3.78/0.99  fof(f60,plain,(
% 3.78/0.99    ! [X0] : (! [X1] : (((v13_waybel_0(X1,X0) | ? [X2] : (? [X3] : (~r2_hidden(X3,X1) & r1_orders_2(X0,X2,X3) & r2_hidden(X2,X1) & m1_subset_1(X3,u1_struct_0(X0))) & m1_subset_1(X2,u1_struct_0(X0)))) & (! [X2] : (! [X3] : (r2_hidden(X3,X1) | ~r1_orders_2(X0,X2,X3) | ~r2_hidden(X2,X1) | ~m1_subset_1(X3,u1_struct_0(X0))) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~v13_waybel_0(X1,X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_orders_2(X0))),
% 3.78/0.99    inference(nnf_transformation,[],[f37])).
% 3.78/0.99  
% 3.78/0.99  fof(f61,plain,(
% 3.78/0.99    ! [X0] : (! [X1] : (((v13_waybel_0(X1,X0) | ? [X2] : (? [X3] : (~r2_hidden(X3,X1) & r1_orders_2(X0,X2,X3) & r2_hidden(X2,X1) & m1_subset_1(X3,u1_struct_0(X0))) & m1_subset_1(X2,u1_struct_0(X0)))) & (! [X4] : (! [X5] : (r2_hidden(X5,X1) | ~r1_orders_2(X0,X4,X5) | ~r2_hidden(X4,X1) | ~m1_subset_1(X5,u1_struct_0(X0))) | ~m1_subset_1(X4,u1_struct_0(X0))) | ~v13_waybel_0(X1,X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_orders_2(X0))),
% 3.78/0.99    inference(rectify,[],[f60])).
% 3.78/0.99  
% 3.78/0.99  fof(f63,plain,(
% 3.78/0.99    ( ! [X2] : (! [X1,X0] : (? [X3] : (~r2_hidden(X3,X1) & r1_orders_2(X0,X2,X3) & r2_hidden(X2,X1) & m1_subset_1(X3,u1_struct_0(X0))) => (~r2_hidden(sK6(X0,X1),X1) & r1_orders_2(X0,X2,sK6(X0,X1)) & r2_hidden(X2,X1) & m1_subset_1(sK6(X0,X1),u1_struct_0(X0))))) )),
% 3.78/0.99    introduced(choice_axiom,[])).
% 3.78/0.99  
% 3.78/0.99  fof(f62,plain,(
% 3.78/0.99    ! [X1,X0] : (? [X2] : (? [X3] : (~r2_hidden(X3,X1) & r1_orders_2(X0,X2,X3) & r2_hidden(X2,X1) & m1_subset_1(X3,u1_struct_0(X0))) & m1_subset_1(X2,u1_struct_0(X0))) => (? [X3] : (~r2_hidden(X3,X1) & r1_orders_2(X0,sK5(X0,X1),X3) & r2_hidden(sK5(X0,X1),X1) & m1_subset_1(X3,u1_struct_0(X0))) & m1_subset_1(sK5(X0,X1),u1_struct_0(X0))))),
% 3.78/0.99    introduced(choice_axiom,[])).
% 3.78/0.99  
% 3.78/0.99  fof(f64,plain,(
% 3.78/0.99    ! [X0] : (! [X1] : (((v13_waybel_0(X1,X0) | ((~r2_hidden(sK6(X0,X1),X1) & r1_orders_2(X0,sK5(X0,X1),sK6(X0,X1)) & r2_hidden(sK5(X0,X1),X1) & m1_subset_1(sK6(X0,X1),u1_struct_0(X0))) & m1_subset_1(sK5(X0,X1),u1_struct_0(X0)))) & (! [X4] : (! [X5] : (r2_hidden(X5,X1) | ~r1_orders_2(X0,X4,X5) | ~r2_hidden(X4,X1) | ~m1_subset_1(X5,u1_struct_0(X0))) | ~m1_subset_1(X4,u1_struct_0(X0))) | ~v13_waybel_0(X1,X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_orders_2(X0))),
% 3.78/0.99    inference(skolemisation,[status(esa),new_symbols(skolem,[sK5,sK6])],[f61,f63,f62])).
% 3.78/0.99  
% 3.78/0.99  fof(f94,plain,(
% 3.78/0.99    ( ! [X4,X0,X5,X1] : (r2_hidden(X5,X1) | ~r1_orders_2(X0,X4,X5) | ~r2_hidden(X4,X1) | ~m1_subset_1(X5,u1_struct_0(X0)) | ~m1_subset_1(X4,u1_struct_0(X0)) | ~v13_waybel_0(X1,X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_orders_2(X0)) )),
% 3.78/0.99    inference(cnf_transformation,[],[f64])).
% 3.78/0.99  
% 3.78/0.99  fof(f107,plain,(
% 3.78/0.99    v13_waybel_0(sK8,sK7)),
% 3.78/0.99    inference(cnf_transformation,[],[f70])).
% 3.78/0.99  
% 3.78/0.99  fof(f9,axiom,(
% 3.78/0.99    ! [X0] : (l1_orders_2(X0) => k3_yellow_0(X0) = k1_yellow_0(X0,k1_xboole_0))),
% 3.78/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.78/0.99  
% 3.78/0.99  fof(f30,plain,(
% 3.78/0.99    ! [X0] : (k3_yellow_0(X0) = k1_yellow_0(X0,k1_xboole_0) | ~l1_orders_2(X0))),
% 3.78/0.99    inference(ennf_transformation,[],[f9])).
% 3.78/0.99  
% 3.78/0.99  fof(f86,plain,(
% 3.78/0.99    ( ! [X0] : (k3_yellow_0(X0) = k1_yellow_0(X0,k1_xboole_0) | ~l1_orders_2(X0)) )),
% 3.78/0.99    inference(cnf_transformation,[],[f30])).
% 3.78/0.99  
% 3.78/0.99  fof(f11,axiom,(
% 3.78/0.99    ! [X0,X1] : (l1_orders_2(X0) => m1_subset_1(k1_yellow_0(X0,X1),u1_struct_0(X0)))),
% 3.78/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.78/0.99  
% 3.78/0.99  fof(f33,plain,(
% 3.78/0.99    ! [X0,X1] : (m1_subset_1(k1_yellow_0(X0,X1),u1_struct_0(X0)) | ~l1_orders_2(X0))),
% 3.78/0.99    inference(ennf_transformation,[],[f11])).
% 3.78/0.99  
% 3.78/0.99  fof(f92,plain,(
% 3.78/0.99    ( ! [X0,X1] : (m1_subset_1(k1_yellow_0(X0,X1),u1_struct_0(X0)) | ~l1_orders_2(X0)) )),
% 3.78/0.99    inference(cnf_transformation,[],[f33])).
% 3.78/0.99  
% 3.78/0.99  fof(f6,axiom,(
% 3.78/0.99    ! [X0,X1] : (m1_subset_1(X0,X1) => (r2_hidden(X0,X1) | v1_xboole_0(X1)))),
% 3.78/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.78/0.99  
% 3.78/0.99  fof(f24,plain,(
% 3.78/0.99    ! [X0,X1] : ((r2_hidden(X0,X1) | v1_xboole_0(X1)) | ~m1_subset_1(X0,X1))),
% 3.78/0.99    inference(ennf_transformation,[],[f6])).
% 3.78/0.99  
% 3.78/0.99  fof(f25,plain,(
% 3.78/0.99    ! [X0,X1] : (r2_hidden(X0,X1) | v1_xboole_0(X1) | ~m1_subset_1(X0,X1))),
% 3.78/0.99    inference(flattening,[],[f24])).
% 3.78/0.99  
% 3.78/0.99  fof(f80,plain,(
% 3.78/0.99    ( ! [X0,X1] : (r2_hidden(X0,X1) | v1_xboole_0(X1) | ~m1_subset_1(X0,X1)) )),
% 3.78/0.99    inference(cnf_transformation,[],[f25])).
% 3.78/0.99  
% 3.78/0.99  fof(f10,axiom,(
% 3.78/0.99    ! [X0] : (l1_orders_2(X0) => ! [X1,X2] : (m1_subset_1(X2,u1_struct_0(X0)) => (r1_yellow_0(X0,X1) => (k1_yellow_0(X0,X1) = X2 <=> (! [X3] : (m1_subset_1(X3,u1_struct_0(X0)) => (r2_lattice3(X0,X1,X3) => r1_orders_2(X0,X2,X3))) & r2_lattice3(X0,X1,X2))))))),
% 3.78/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.78/0.99  
% 3.78/0.99  fof(f31,plain,(
% 3.78/0.99    ! [X0] : (! [X1,X2] : (((k1_yellow_0(X0,X1) = X2 <=> (! [X3] : ((r1_orders_2(X0,X2,X3) | ~r2_lattice3(X0,X1,X3)) | ~m1_subset_1(X3,u1_struct_0(X0))) & r2_lattice3(X0,X1,X2))) | ~r1_yellow_0(X0,X1)) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~l1_orders_2(X0))),
% 3.78/0.99    inference(ennf_transformation,[],[f10])).
% 3.78/0.99  
% 3.78/0.99  fof(f32,plain,(
% 3.78/0.99    ! [X0] : (! [X1,X2] : ((k1_yellow_0(X0,X1) = X2 <=> (! [X3] : (r1_orders_2(X0,X2,X3) | ~r2_lattice3(X0,X1,X3) | ~m1_subset_1(X3,u1_struct_0(X0))) & r2_lattice3(X0,X1,X2))) | ~r1_yellow_0(X0,X1) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~l1_orders_2(X0))),
% 3.78/0.99    inference(flattening,[],[f31])).
% 3.78/0.99  
% 3.78/0.99  fof(f55,plain,(
% 3.78/0.99    ! [X0] : (! [X1,X2] : (((k1_yellow_0(X0,X1) = X2 | (? [X3] : (~r1_orders_2(X0,X2,X3) & r2_lattice3(X0,X1,X3) & m1_subset_1(X3,u1_struct_0(X0))) | ~r2_lattice3(X0,X1,X2))) & ((! [X3] : (r1_orders_2(X0,X2,X3) | ~r2_lattice3(X0,X1,X3) | ~m1_subset_1(X3,u1_struct_0(X0))) & r2_lattice3(X0,X1,X2)) | k1_yellow_0(X0,X1) != X2)) | ~r1_yellow_0(X0,X1) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~l1_orders_2(X0))),
% 3.78/0.99    inference(nnf_transformation,[],[f32])).
% 3.78/0.99  
% 3.78/0.99  fof(f56,plain,(
% 3.78/0.99    ! [X0] : (! [X1,X2] : (((k1_yellow_0(X0,X1) = X2 | ? [X3] : (~r1_orders_2(X0,X2,X3) & r2_lattice3(X0,X1,X3) & m1_subset_1(X3,u1_struct_0(X0))) | ~r2_lattice3(X0,X1,X2)) & ((! [X3] : (r1_orders_2(X0,X2,X3) | ~r2_lattice3(X0,X1,X3) | ~m1_subset_1(X3,u1_struct_0(X0))) & r2_lattice3(X0,X1,X2)) | k1_yellow_0(X0,X1) != X2)) | ~r1_yellow_0(X0,X1) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~l1_orders_2(X0))),
% 3.78/0.99    inference(flattening,[],[f55])).
% 3.78/0.99  
% 3.78/0.99  fof(f57,plain,(
% 3.78/0.99    ! [X0] : (! [X1,X2] : (((k1_yellow_0(X0,X1) = X2 | ? [X3] : (~r1_orders_2(X0,X2,X3) & r2_lattice3(X0,X1,X3) & m1_subset_1(X3,u1_struct_0(X0))) | ~r2_lattice3(X0,X1,X2)) & ((! [X4] : (r1_orders_2(X0,X2,X4) | ~r2_lattice3(X0,X1,X4) | ~m1_subset_1(X4,u1_struct_0(X0))) & r2_lattice3(X0,X1,X2)) | k1_yellow_0(X0,X1) != X2)) | ~r1_yellow_0(X0,X1) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~l1_orders_2(X0))),
% 3.78/0.99    inference(rectify,[],[f56])).
% 3.78/0.99  
% 3.78/0.99  fof(f58,plain,(
% 3.78/0.99    ! [X2,X1,X0] : (? [X3] : (~r1_orders_2(X0,X2,X3) & r2_lattice3(X0,X1,X3) & m1_subset_1(X3,u1_struct_0(X0))) => (~r1_orders_2(X0,X2,sK4(X0,X1,X2)) & r2_lattice3(X0,X1,sK4(X0,X1,X2)) & m1_subset_1(sK4(X0,X1,X2),u1_struct_0(X0))))),
% 3.78/0.99    introduced(choice_axiom,[])).
% 3.78/0.99  
% 3.78/0.99  fof(f59,plain,(
% 3.78/0.99    ! [X0] : (! [X1,X2] : (((k1_yellow_0(X0,X1) = X2 | (~r1_orders_2(X0,X2,sK4(X0,X1,X2)) & r2_lattice3(X0,X1,sK4(X0,X1,X2)) & m1_subset_1(sK4(X0,X1,X2),u1_struct_0(X0))) | ~r2_lattice3(X0,X1,X2)) & ((! [X4] : (r1_orders_2(X0,X2,X4) | ~r2_lattice3(X0,X1,X4) | ~m1_subset_1(X4,u1_struct_0(X0))) & r2_lattice3(X0,X1,X2)) | k1_yellow_0(X0,X1) != X2)) | ~r1_yellow_0(X0,X1) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~l1_orders_2(X0))),
% 3.78/0.99    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4])],[f57,f58])).
% 3.78/0.99  
% 3.78/0.99  fof(f88,plain,(
% 3.78/0.99    ( ! [X4,X2,X0,X1] : (r1_orders_2(X0,X2,X4) | ~r2_lattice3(X0,X1,X4) | ~m1_subset_1(X4,u1_struct_0(X0)) | k1_yellow_0(X0,X1) != X2 | ~r1_yellow_0(X0,X1) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~l1_orders_2(X0)) )),
% 3.78/0.99    inference(cnf_transformation,[],[f59])).
% 3.78/0.99  
% 3.78/0.99  fof(f111,plain,(
% 3.78/0.99    ( ! [X4,X0,X1] : (r1_orders_2(X0,k1_yellow_0(X0,X1),X4) | ~r2_lattice3(X0,X1,X4) | ~m1_subset_1(X4,u1_struct_0(X0)) | ~r1_yellow_0(X0,X1) | ~m1_subset_1(k1_yellow_0(X0,X1),u1_struct_0(X0)) | ~l1_orders_2(X0)) )),
% 3.78/0.99    inference(equality_resolution,[],[f88])).
% 3.78/0.99  
% 3.78/0.99  fof(f12,axiom,(
% 3.78/0.99    ! [X0] : ((l1_orders_2(X0) & v1_yellow_0(X0) & v5_orders_2(X0) & ~v2_struct_0(X0)) => (r2_yellow_0(X0,u1_struct_0(X0)) & r1_yellow_0(X0,k1_xboole_0)))),
% 3.78/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.78/0.99  
% 3.78/0.99  fof(f20,plain,(
% 3.78/0.99    ! [X0] : ((l1_orders_2(X0) & v1_yellow_0(X0) & v5_orders_2(X0) & ~v2_struct_0(X0)) => r1_yellow_0(X0,k1_xboole_0))),
% 3.78/0.99    inference(pure_predicate_removal,[],[f12])).
% 3.78/0.99  
% 3.78/0.99  fof(f34,plain,(
% 3.78/0.99    ! [X0] : (r1_yellow_0(X0,k1_xboole_0) | (~l1_orders_2(X0) | ~v1_yellow_0(X0) | ~v5_orders_2(X0) | v2_struct_0(X0)))),
% 3.78/0.99    inference(ennf_transformation,[],[f20])).
% 3.78/0.99  
% 3.78/0.99  fof(f35,plain,(
% 3.78/0.99    ! [X0] : (r1_yellow_0(X0,k1_xboole_0) | ~l1_orders_2(X0) | ~v1_yellow_0(X0) | ~v5_orders_2(X0) | v2_struct_0(X0))),
% 3.78/0.99    inference(flattening,[],[f34])).
% 3.78/0.99  
% 3.78/0.99  fof(f93,plain,(
% 3.78/0.99    ( ! [X0] : (r1_yellow_0(X0,k1_xboole_0) | ~l1_orders_2(X0) | ~v1_yellow_0(X0) | ~v5_orders_2(X0) | v2_struct_0(X0)) )),
% 3.78/0.99    inference(cnf_transformation,[],[f35])).
% 3.78/0.99  
% 3.78/0.99  fof(f104,plain,(
% 3.78/0.99    v1_yellow_0(sK7)),
% 3.78/0.99    inference(cnf_transformation,[],[f70])).
% 3.78/0.99  
% 3.78/0.99  fof(f102,plain,(
% 3.78/0.99    ~v2_struct_0(sK7)),
% 3.78/0.99    inference(cnf_transformation,[],[f70])).
% 3.78/0.99  
% 3.78/0.99  fof(f103,plain,(
% 3.78/0.99    v5_orders_2(sK7)),
% 3.78/0.99    inference(cnf_transformation,[],[f70])).
% 3.78/0.99  
% 3.78/0.99  fof(f110,plain,(
% 3.78/0.99    r2_hidden(k3_yellow_0(sK7),sK8) | ~v1_subset_1(sK8,u1_struct_0(sK7))),
% 3.78/0.99    inference(cnf_transformation,[],[f70])).
% 3.78/0.99  
% 3.78/0.99  fof(f84,plain,(
% 3.78/0.99    ( ! [X2,X0,X1] : (r2_lattice3(X0,X1,X2) | r2_hidden(sK3(X0,X1,X2),X1) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~l1_orders_2(X0)) )),
% 3.78/0.99    inference(cnf_transformation,[],[f54])).
% 3.78/0.99  
% 3.78/0.99  fof(f87,plain,(
% 3.78/0.99    ( ! [X2,X0,X1] : (r2_lattice3(X0,X1,X2) | k1_yellow_0(X0,X1) != X2 | ~r1_yellow_0(X0,X1) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~l1_orders_2(X0)) )),
% 3.78/0.99    inference(cnf_transformation,[],[f59])).
% 3.78/0.99  
% 3.78/0.99  fof(f112,plain,(
% 3.78/0.99    ( ! [X0,X1] : (r2_lattice3(X0,X1,k1_yellow_0(X0,X1)) | ~r1_yellow_0(X0,X1) | ~m1_subset_1(k1_yellow_0(X0,X1),u1_struct_0(X0)) | ~l1_orders_2(X0)) )),
% 3.78/0.99    inference(equality_resolution,[],[f87])).
% 3.78/0.99  
% 3.78/0.99  fof(f2,axiom,(
% 3.78/0.99    v1_xboole_0(k1_xboole_0)),
% 3.78/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.78/0.99  
% 3.78/0.99  fof(f73,plain,(
% 3.78/0.99    v1_xboole_0(k1_xboole_0)),
% 3.78/0.99    inference(cnf_transformation,[],[f2])).
% 3.78/0.99  
% 3.78/0.99  fof(f77,plain,(
% 3.78/0.99    ( ! [X2,X0,X1] : (X1 = X2 | ~r2_hidden(sK1(X0,X1,X2),X2) | ~r2_hidden(sK1(X0,X1,X2),X1) | ~m1_subset_1(X2,k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 3.78/0.99    inference(cnf_transformation,[],[f48])).
% 3.78/0.99  
% 3.78/0.99  fof(f109,plain,(
% 3.78/0.99    ~r2_hidden(k3_yellow_0(sK7),sK8) | v1_subset_1(sK8,u1_struct_0(sK7))),
% 3.78/0.99    inference(cnf_transformation,[],[f70])).
% 3.78/0.99  
% 3.78/0.99  cnf(c_6,plain,
% 3.78/0.99      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
% 3.78/0.99      | ~ m1_subset_1(X2,k1_zfmisc_1(X1))
% 3.78/0.99      | m1_subset_1(sK1(X1,X0,X2),X1)
% 3.78/0.99      | X0 = X2 ),
% 3.78/0.99      inference(cnf_transformation,[],[f75]) ).
% 3.78/0.99  
% 3.78/0.99  cnf(c_2681,plain,
% 3.78/0.99      ( X0 = X1
% 3.78/0.99      | m1_subset_1(X0,k1_zfmisc_1(X2)) != iProver_top
% 3.78/0.99      | m1_subset_1(X1,k1_zfmisc_1(X2)) != iProver_top
% 3.78/0.99      | m1_subset_1(sK1(X2,X0,X1),X2) = iProver_top ),
% 3.78/0.99      inference(predicate_to_equality,[status(thm)],[c_6]) ).
% 3.78/0.99  
% 3.78/0.99  cnf(c_33,negated_conjecture,
% 3.78/0.99      ( m1_subset_1(sK8,k1_zfmisc_1(u1_struct_0(sK7))) ),
% 3.78/0.99      inference(cnf_transformation,[],[f108]) ).
% 3.78/0.99  
% 3.78/0.99  cnf(c_2677,plain,
% 3.78/0.99      ( m1_subset_1(sK8,k1_zfmisc_1(u1_struct_0(sK7))) = iProver_top ),
% 3.78/0.99      inference(predicate_to_equality,[status(thm)],[c_33]) ).
% 3.78/0.99  
% 3.78/0.99  cnf(c_3,plain,
% 3.78/0.99      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
% 3.78/0.99      | ~ r2_hidden(X2,X0)
% 3.78/0.99      | r2_hidden(X2,X1) ),
% 3.78/0.99      inference(cnf_transformation,[],[f74]) ).
% 3.78/0.99  
% 3.78/0.99  cnf(c_2684,plain,
% 3.78/0.99      ( m1_subset_1(X0,k1_zfmisc_1(X1)) != iProver_top
% 3.78/0.99      | r2_hidden(X2,X0) != iProver_top
% 3.78/0.99      | r2_hidden(X2,X1) = iProver_top ),
% 3.78/0.99      inference(predicate_to_equality,[status(thm)],[c_3]) ).
% 3.78/0.99  
% 3.78/0.99  cnf(c_4010,plain,
% 3.78/0.99      ( r2_hidden(X0,u1_struct_0(sK7)) = iProver_top
% 3.78/0.99      | r2_hidden(X0,sK8) != iProver_top ),
% 3.78/0.99      inference(superposition,[status(thm)],[c_2677,c_2684]) ).
% 3.78/0.99  
% 3.78/0.99  cnf(c_0,plain,
% 3.78/0.99      ( r2_hidden(sK0(X0),X0) | v1_xboole_0(X0) ),
% 3.78/0.99      inference(cnf_transformation,[],[f72]) ).
% 3.78/0.99  
% 3.78/0.99  cnf(c_2687,plain,
% 3.78/0.99      ( r2_hidden(sK0(X0),X0) = iProver_top
% 3.78/0.99      | v1_xboole_0(X0) = iProver_top ),
% 3.78/0.99      inference(predicate_to_equality,[status(thm)],[c_0]) ).
% 3.78/0.99  
% 3.78/0.99  cnf(c_8,plain,
% 3.78/0.99      ( m1_subset_1(sK2(X0),k1_zfmisc_1(X0)) ),
% 3.78/0.99      inference(cnf_transformation,[],[f78]) ).
% 3.78/0.99  
% 3.78/0.99  cnf(c_2680,plain,
% 3.78/0.99      ( m1_subset_1(sK2(X0),k1_zfmisc_1(X0)) = iProver_top ),
% 3.78/0.99      inference(predicate_to_equality,[status(thm)],[c_8]) ).
% 3.78/0.99  
% 3.78/0.99  cnf(c_7,plain,
% 3.78/0.99      ( ~ v1_subset_1(sK2(X0),X0) ),
% 3.78/0.99      inference(cnf_transformation,[],[f79]) ).
% 3.78/0.99  
% 3.78/0.99  cnf(c_29,plain,
% 3.78/0.99      ( v1_subset_1(X0,X1)
% 3.78/0.99      | ~ m1_subset_1(X0,k1_zfmisc_1(X1))
% 3.78/0.99      | X0 = X1 ),
% 3.78/0.99      inference(cnf_transformation,[],[f101]) ).
% 3.78/0.99  
% 3.78/0.99  cnf(c_618,plain,
% 3.78/0.99      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
% 3.78/0.99      | X1 != X2
% 3.78/0.99      | X1 = X0
% 3.78/0.99      | sK2(X2) != X0 ),
% 3.78/0.99      inference(resolution_lifted,[status(thm)],[c_7,c_29]) ).
% 3.78/0.99  
% 3.78/0.99  cnf(c_619,plain,
% 3.78/0.99      ( ~ m1_subset_1(sK2(X0),k1_zfmisc_1(X0)) | X0 = sK2(X0) ),
% 3.78/0.99      inference(unflattening,[status(thm)],[c_618]) ).
% 3.78/0.99  
% 3.78/0.99  cnf(c_623,plain,
% 3.78/0.99      ( X0 = sK2(X0) ),
% 3.78/0.99      inference(global_propositional_subsumption,
% 3.78/0.99                [status(thm)],
% 3.78/0.99                [c_619,c_8]) ).
% 3.78/0.99  
% 3.78/0.99  cnf(c_2700,plain,
% 3.78/0.99      ( m1_subset_1(X0,k1_zfmisc_1(X0)) = iProver_top ),
% 3.78/0.99      inference(light_normalisation,[status(thm)],[c_2680,c_623]) ).
% 3.78/0.99  
% 3.78/0.99  cnf(c_10,plain,
% 3.78/0.99      ( m1_subset_1(X0,X1)
% 3.78/0.99      | ~ m1_subset_1(X2,k1_zfmisc_1(X1))
% 3.78/0.99      | ~ r2_hidden(X0,X2) ),
% 3.78/0.99      inference(cnf_transformation,[],[f81]) ).
% 3.78/0.99  
% 3.78/0.99  cnf(c_2678,plain,
% 3.78/0.99      ( m1_subset_1(X0,X1) = iProver_top
% 3.78/0.99      | m1_subset_1(X2,k1_zfmisc_1(X1)) != iProver_top
% 3.78/0.99      | r2_hidden(X0,X2) != iProver_top ),
% 3.78/0.99      inference(predicate_to_equality,[status(thm)],[c_10]) ).
% 3.78/0.99  
% 3.78/0.99  cnf(c_4876,plain,
% 3.78/0.99      ( m1_subset_1(X0,X1) = iProver_top
% 3.78/0.99      | r2_hidden(X0,X1) != iProver_top ),
% 3.78/0.99      inference(superposition,[status(thm)],[c_2700,c_2678]) ).
% 3.78/0.99  
% 3.78/0.99  cnf(c_5076,plain,
% 3.78/0.99      ( m1_subset_1(sK0(X0),X0) = iProver_top
% 3.78/0.99      | v1_xboole_0(X0) = iProver_top ),
% 3.78/0.99      inference(superposition,[status(thm)],[c_2687,c_4876]) ).
% 3.78/0.99  
% 3.78/0.99  cnf(c_14,plain,
% 3.78/0.99      ( r1_orders_2(X0,X1,X2)
% 3.78/0.99      | ~ r2_lattice3(X0,X3,X2)
% 3.78/0.99      | ~ m1_subset_1(X2,u1_struct_0(X0))
% 3.78/0.99      | ~ m1_subset_1(X1,u1_struct_0(X0))
% 3.78/0.99      | ~ r2_hidden(X1,X3)
% 3.78/0.99      | ~ l1_orders_2(X0) ),
% 3.78/0.99      inference(cnf_transformation,[],[f82]) ).
% 3.78/0.99  
% 3.78/0.99  cnf(c_36,negated_conjecture,
% 3.78/0.99      ( l1_orders_2(sK7) ),
% 3.78/0.99      inference(cnf_transformation,[],[f105]) ).
% 3.78/0.99  
% 3.78/0.99  cnf(c_858,plain,
% 3.78/0.99      ( r1_orders_2(X0,X1,X2)
% 3.78/0.99      | ~ r2_lattice3(X0,X3,X2)
% 3.78/0.99      | ~ m1_subset_1(X1,u1_struct_0(X0))
% 3.78/0.99      | ~ m1_subset_1(X2,u1_struct_0(X0))
% 3.78/0.99      | ~ r2_hidden(X1,X3)
% 3.78/0.99      | sK7 != X0 ),
% 3.78/0.99      inference(resolution_lifted,[status(thm)],[c_14,c_36]) ).
% 3.78/0.99  
% 3.78/0.99  cnf(c_859,plain,
% 3.78/0.99      ( r1_orders_2(sK7,X0,X1)
% 3.78/0.99      | ~ r2_lattice3(sK7,X2,X1)
% 3.78/0.99      | ~ m1_subset_1(X0,u1_struct_0(sK7))
% 3.78/0.99      | ~ m1_subset_1(X1,u1_struct_0(sK7))
% 3.78/0.99      | ~ r2_hidden(X0,X2) ),
% 3.78/0.99      inference(unflattening,[status(thm)],[c_858]) ).
% 3.78/0.99  
% 3.78/0.99  cnf(c_2663,plain,
% 3.78/0.99      ( r1_orders_2(sK7,X0,X1) = iProver_top
% 3.78/0.99      | r2_lattice3(sK7,X2,X1) != iProver_top
% 3.78/0.99      | m1_subset_1(X0,u1_struct_0(sK7)) != iProver_top
% 3.78/0.99      | m1_subset_1(X1,u1_struct_0(sK7)) != iProver_top
% 3.78/0.99      | r2_hidden(X0,X2) != iProver_top ),
% 3.78/0.99      inference(predicate_to_equality,[status(thm)],[c_859]) ).
% 3.78/0.99  
% 3.78/0.99  cnf(c_5605,plain,
% 3.78/0.99      ( r1_orders_2(sK7,sK0(u1_struct_0(sK7)),X0) = iProver_top
% 3.78/0.99      | r2_lattice3(sK7,X1,X0) != iProver_top
% 3.78/0.99      | m1_subset_1(X0,u1_struct_0(sK7)) != iProver_top
% 3.78/0.99      | r2_hidden(sK0(u1_struct_0(sK7)),X1) != iProver_top
% 3.78/0.99      | v1_xboole_0(u1_struct_0(sK7)) = iProver_top ),
% 3.78/0.99      inference(superposition,[status(thm)],[c_5076,c_2663]) ).
% 3.78/0.99  
% 3.78/0.99  cnf(c_46,plain,
% 3.78/0.99      ( m1_subset_1(sK8,k1_zfmisc_1(u1_struct_0(sK7))) = iProver_top ),
% 3.78/0.99      inference(predicate_to_equality,[status(thm)],[c_33]) ).
% 3.78/0.99  
% 3.78/0.99  cnf(c_35,negated_conjecture,
% 3.78/0.99      ( ~ v1_xboole_0(sK8) ),
% 3.78/0.99      inference(cnf_transformation,[],[f106]) ).
% 3.78/0.99  
% 3.78/0.99  cnf(c_575,plain,
% 3.78/0.99      ( r2_hidden(sK0(X0),X0) | sK8 != X0 ),
% 3.78/0.99      inference(resolution_lifted,[status(thm)],[c_0,c_35]) ).
% 3.78/0.99  
% 3.78/0.99  cnf(c_576,plain,
% 3.78/0.99      ( r2_hidden(sK0(sK8),sK8) ),
% 3.78/0.99      inference(unflattening,[status(thm)],[c_575]) ).
% 3.78/0.99  
% 3.78/0.99  cnf(c_577,plain,
% 3.78/0.99      ( r2_hidden(sK0(sK8),sK8) = iProver_top ),
% 3.78/0.99      inference(predicate_to_equality,[status(thm)],[c_576]) ).
% 3.78/0.99  
% 3.78/0.99  cnf(c_3135,plain,
% 3.78/0.99      ( ~ m1_subset_1(sK8,k1_zfmisc_1(X0))
% 3.78/0.99      | r2_hidden(sK0(sK8),X0)
% 3.78/0.99      | ~ r2_hidden(sK0(sK8),sK8) ),
% 3.78/0.99      inference(instantiation,[status(thm)],[c_3]) ).
% 3.78/0.99  
% 3.78/0.99  cnf(c_3269,plain,
% 3.78/0.99      ( ~ m1_subset_1(sK8,k1_zfmisc_1(u1_struct_0(sK7)))
% 3.78/0.99      | r2_hidden(sK0(sK8),u1_struct_0(sK7))
% 3.78/0.99      | ~ r2_hidden(sK0(sK8),sK8) ),
% 3.78/0.99      inference(instantiation,[status(thm)],[c_3135]) ).
% 3.78/0.99  
% 3.78/0.99  cnf(c_3270,plain,
% 3.78/0.99      ( m1_subset_1(sK8,k1_zfmisc_1(u1_struct_0(sK7))) != iProver_top
% 3.78/0.99      | r2_hidden(sK0(sK8),u1_struct_0(sK7)) = iProver_top
% 3.78/0.99      | r2_hidden(sK0(sK8),sK8) != iProver_top ),
% 3.78/0.99      inference(predicate_to_equality,[status(thm)],[c_3269]) ).
% 3.78/0.99  
% 3.78/0.99  cnf(c_1,plain,
% 3.78/0.99      ( ~ r2_hidden(X0,X1) | ~ v1_xboole_0(X1) ),
% 3.78/0.99      inference(cnf_transformation,[],[f71]) ).
% 3.78/0.99  
% 3.78/0.99  cnf(c_3733,plain,
% 3.78/0.99      ( ~ r2_hidden(sK0(sK8),u1_struct_0(sK7))
% 3.78/0.99      | ~ v1_xboole_0(u1_struct_0(sK7)) ),
% 3.78/0.99      inference(instantiation,[status(thm)],[c_1]) ).
% 3.78/0.99  
% 3.78/0.99  cnf(c_3734,plain,
% 3.78/0.99      ( r2_hidden(sK0(sK8),u1_struct_0(sK7)) != iProver_top
% 3.78/0.99      | v1_xboole_0(u1_struct_0(sK7)) != iProver_top ),
% 3.78/0.99      inference(predicate_to_equality,[status(thm)],[c_3733]) ).
% 3.78/0.99  
% 3.78/0.99  cnf(c_9351,plain,
% 3.78/0.99      ( r2_hidden(sK0(u1_struct_0(sK7)),X1) != iProver_top
% 3.78/0.99      | m1_subset_1(X0,u1_struct_0(sK7)) != iProver_top
% 3.78/0.99      | r2_lattice3(sK7,X1,X0) != iProver_top
% 3.78/0.99      | r1_orders_2(sK7,sK0(u1_struct_0(sK7)),X0) = iProver_top ),
% 3.78/0.99      inference(global_propositional_subsumption,
% 3.78/0.99                [status(thm)],
% 3.78/0.99                [c_5605,c_46,c_577,c_3270,c_3734]) ).
% 3.78/0.99  
% 3.78/0.99  cnf(c_9352,plain,
% 3.78/0.99      ( r1_orders_2(sK7,sK0(u1_struct_0(sK7)),X0) = iProver_top
% 3.78/0.99      | r2_lattice3(sK7,X1,X0) != iProver_top
% 3.78/0.99      | m1_subset_1(X0,u1_struct_0(sK7)) != iProver_top
% 3.78/0.99      | r2_hidden(sK0(u1_struct_0(sK7)),X1) != iProver_top ),
% 3.78/0.99      inference(renaming,[status(thm)],[c_9351]) ).
% 3.78/0.99  
% 3.78/0.99  cnf(c_9362,plain,
% 3.78/0.99      ( r1_orders_2(sK7,sK0(u1_struct_0(sK7)),X0) = iProver_top
% 3.78/0.99      | r2_lattice3(sK7,u1_struct_0(sK7),X0) != iProver_top
% 3.78/0.99      | m1_subset_1(X0,u1_struct_0(sK7)) != iProver_top
% 3.78/0.99      | r2_hidden(sK0(u1_struct_0(sK7)),sK8) != iProver_top ),
% 3.78/0.99      inference(superposition,[status(thm)],[c_4010,c_9352]) ).
% 3.78/0.99  
% 3.78/0.99  cnf(c_9361,plain,
% 3.78/0.99      ( r1_orders_2(sK7,sK0(u1_struct_0(sK7)),X0) = iProver_top
% 3.78/0.99      | r2_lattice3(sK7,u1_struct_0(sK7),X0) != iProver_top
% 3.78/0.99      | m1_subset_1(X0,u1_struct_0(sK7)) != iProver_top
% 3.78/0.99      | v1_xboole_0(u1_struct_0(sK7)) = iProver_top ),
% 3.78/0.99      inference(superposition,[status(thm)],[c_2687,c_9352]) ).
% 3.78/0.99  
% 3.78/0.99  cnf(c_9398,plain,
% 3.78/0.99      ( m1_subset_1(X0,u1_struct_0(sK7)) != iProver_top
% 3.78/0.99      | r2_lattice3(sK7,u1_struct_0(sK7),X0) != iProver_top
% 3.78/0.99      | r1_orders_2(sK7,sK0(u1_struct_0(sK7)),X0) = iProver_top ),
% 3.78/0.99      inference(global_propositional_subsumption,
% 3.78/0.99                [status(thm)],
% 3.78/0.99                [c_9362,c_46,c_577,c_3270,c_3734,c_9361]) ).
% 3.78/0.99  
% 3.78/0.99  cnf(c_9399,plain,
% 3.78/0.99      ( r1_orders_2(sK7,sK0(u1_struct_0(sK7)),X0) = iProver_top
% 3.78/0.99      | r2_lattice3(sK7,u1_struct_0(sK7),X0) != iProver_top
% 3.78/0.99      | m1_subset_1(X0,u1_struct_0(sK7)) != iProver_top ),
% 3.78/0.99      inference(renaming,[status(thm)],[c_9398]) ).
% 3.78/0.99  
% 3.78/0.99  cnf(c_28,plain,
% 3.78/0.99      ( ~ r1_orders_2(X0,X1,X2)
% 3.78/0.99      | ~ v13_waybel_0(X3,X0)
% 3.78/0.99      | ~ m1_subset_1(X1,u1_struct_0(X0))
% 3.78/0.99      | ~ m1_subset_1(X2,u1_struct_0(X0))
% 3.78/0.99      | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))
% 3.78/0.99      | ~ r2_hidden(X1,X3)
% 3.78/0.99      | r2_hidden(X2,X3)
% 3.78/0.99      | ~ l1_orders_2(X0) ),
% 3.78/0.99      inference(cnf_transformation,[],[f94]) ).
% 3.78/0.99  
% 3.78/0.99  cnf(c_804,plain,
% 3.78/0.99      ( ~ r1_orders_2(X0,X1,X2)
% 3.78/0.99      | ~ v13_waybel_0(X3,X0)
% 3.78/0.99      | ~ m1_subset_1(X1,u1_struct_0(X0))
% 3.78/0.99      | ~ m1_subset_1(X2,u1_struct_0(X0))
% 3.78/0.99      | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))
% 3.78/0.99      | ~ r2_hidden(X1,X3)
% 3.78/0.99      | r2_hidden(X2,X3)
% 3.78/0.99      | sK7 != X0 ),
% 3.78/0.99      inference(resolution_lifted,[status(thm)],[c_28,c_36]) ).
% 3.78/0.99  
% 3.78/0.99  cnf(c_805,plain,
% 3.78/0.99      ( ~ r1_orders_2(sK7,X0,X1)
% 3.78/0.99      | ~ v13_waybel_0(X2,sK7)
% 3.78/0.99      | ~ m1_subset_1(X0,u1_struct_0(sK7))
% 3.78/0.99      | ~ m1_subset_1(X1,u1_struct_0(sK7))
% 3.78/0.99      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK7)))
% 3.78/0.99      | ~ r2_hidden(X0,X2)
% 3.78/0.99      | r2_hidden(X1,X2) ),
% 3.78/0.99      inference(unflattening,[status(thm)],[c_804]) ).
% 3.78/0.99  
% 3.78/0.99  cnf(c_821,plain,
% 3.78/0.99      ( ~ r1_orders_2(sK7,X0,X1)
% 3.78/0.99      | ~ v13_waybel_0(X2,sK7)
% 3.78/0.99      | ~ m1_subset_1(X1,u1_struct_0(sK7))
% 3.78/0.99      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK7)))
% 3.78/0.99      | ~ r2_hidden(X0,X2)
% 3.78/0.99      | r2_hidden(X1,X2) ),
% 3.78/0.99      inference(forward_subsumption_resolution,
% 3.78/0.99                [status(thm)],
% 3.78/0.99                [c_805,c_10]) ).
% 3.78/0.99  
% 3.78/0.99  cnf(c_2666,plain,
% 3.78/0.99      ( r1_orders_2(sK7,X0,X1) != iProver_top
% 3.78/0.99      | v13_waybel_0(X2,sK7) != iProver_top
% 3.78/0.99      | m1_subset_1(X1,u1_struct_0(sK7)) != iProver_top
% 3.78/0.99      | m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK7))) != iProver_top
% 3.78/0.99      | r2_hidden(X0,X2) != iProver_top
% 3.78/0.99      | r2_hidden(X1,X2) = iProver_top ),
% 3.78/0.99      inference(predicate_to_equality,[status(thm)],[c_821]) ).
% 3.78/0.99  
% 3.78/0.99  cnf(c_4701,plain,
% 3.78/0.99      ( r1_orders_2(sK7,X0,X1) != iProver_top
% 3.78/0.99      | v13_waybel_0(sK8,sK7) != iProver_top
% 3.78/0.99      | m1_subset_1(X1,u1_struct_0(sK7)) != iProver_top
% 3.78/0.99      | r2_hidden(X0,sK8) != iProver_top
% 3.78/0.99      | r2_hidden(X1,sK8) = iProver_top ),
% 3.78/0.99      inference(superposition,[status(thm)],[c_2677,c_2666]) ).
% 3.78/0.99  
% 3.78/0.99  cnf(c_34,negated_conjecture,
% 3.78/0.99      ( v13_waybel_0(sK8,sK7) ),
% 3.78/0.99      inference(cnf_transformation,[],[f107]) ).
% 3.78/0.99  
% 3.78/0.99  cnf(c_1032,plain,
% 3.78/0.99      ( ~ r1_orders_2(sK7,X0,X1)
% 3.78/0.99      | ~ m1_subset_1(X1,u1_struct_0(sK7))
% 3.78/0.99      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK7)))
% 3.78/0.99      | ~ r2_hidden(X0,X2)
% 3.78/0.99      | r2_hidden(X1,X2)
% 3.78/0.99      | sK8 != X2
% 3.78/0.99      | sK7 != sK7 ),
% 3.78/0.99      inference(resolution_lifted,[status(thm)],[c_34,c_821]) ).
% 3.78/0.99  
% 3.78/0.99  cnf(c_1033,plain,
% 3.78/0.99      ( ~ r1_orders_2(sK7,X0,X1)
% 3.78/0.99      | ~ m1_subset_1(X1,u1_struct_0(sK7))
% 3.78/0.99      | ~ m1_subset_1(sK8,k1_zfmisc_1(u1_struct_0(sK7)))
% 3.78/0.99      | ~ r2_hidden(X0,sK8)
% 3.78/0.99      | r2_hidden(X1,sK8) ),
% 3.78/0.99      inference(unflattening,[status(thm)],[c_1032]) ).
% 3.78/0.99  
% 3.78/0.99  cnf(c_1035,plain,
% 3.78/0.99      ( ~ m1_subset_1(X1,u1_struct_0(sK7))
% 3.78/0.99      | ~ r1_orders_2(sK7,X0,X1)
% 3.78/0.99      | ~ r2_hidden(X0,sK8)
% 3.78/0.99      | r2_hidden(X1,sK8) ),
% 3.78/0.99      inference(global_propositional_subsumption,
% 3.78/0.99                [status(thm)],
% 3.78/0.99                [c_1033,c_33]) ).
% 3.78/0.99  
% 3.78/0.99  cnf(c_1036,plain,
% 3.78/0.99      ( ~ r1_orders_2(sK7,X0,X1)
% 3.78/0.99      | ~ m1_subset_1(X1,u1_struct_0(sK7))
% 3.78/0.99      | ~ r2_hidden(X0,sK8)
% 3.78/0.99      | r2_hidden(X1,sK8) ),
% 3.78/0.99      inference(renaming,[status(thm)],[c_1035]) ).
% 3.78/0.99  
% 3.78/0.99  cnf(c_1037,plain,
% 3.78/0.99      ( r1_orders_2(sK7,X0,X1) != iProver_top
% 3.78/0.99      | m1_subset_1(X1,u1_struct_0(sK7)) != iProver_top
% 3.78/0.99      | r2_hidden(X0,sK8) != iProver_top
% 3.78/0.99      | r2_hidden(X1,sK8) = iProver_top ),
% 3.78/0.99      inference(predicate_to_equality,[status(thm)],[c_1036]) ).
% 3.78/0.99  
% 3.78/0.99  cnf(c_5121,plain,
% 3.78/0.99      ( r1_orders_2(sK7,X0,X1) != iProver_top
% 3.78/0.99      | m1_subset_1(X1,u1_struct_0(sK7)) != iProver_top
% 3.78/0.99      | r2_hidden(X0,sK8) != iProver_top
% 3.78/0.99      | r2_hidden(X1,sK8) = iProver_top ),
% 3.78/0.99      inference(global_propositional_subsumption,
% 3.78/0.99                [status(thm)],
% 3.78/0.99                [c_4701,c_1037]) ).
% 3.78/0.99  
% 3.78/0.99  cnf(c_9408,plain,
% 3.78/0.99      ( r2_lattice3(sK7,u1_struct_0(sK7),X0) != iProver_top
% 3.78/0.99      | m1_subset_1(X0,u1_struct_0(sK7)) != iProver_top
% 3.78/0.99      | r2_hidden(X0,sK8) = iProver_top
% 3.78/0.99      | r2_hidden(sK0(u1_struct_0(sK7)),sK8) != iProver_top ),
% 3.78/0.99      inference(superposition,[status(thm)],[c_9399,c_5121]) ).
% 3.78/0.99  
% 3.78/0.99  cnf(c_2099,plain,
% 3.78/0.99      ( X0 != X1 | k3_yellow_0(X0) = k3_yellow_0(X1) ),
% 3.78/0.99      theory(equality) ).
% 3.78/0.99  
% 3.78/0.99  cnf(c_2114,plain,
% 3.78/0.99      ( k3_yellow_0(sK7) = k3_yellow_0(sK7) | sK7 != sK7 ),
% 3.78/0.99      inference(instantiation,[status(thm)],[c_2099]) ).
% 3.78/0.99  
% 3.78/0.99  cnf(c_2088,plain,( X0 = X0 ),theory(equality) ).
% 3.78/0.99  
% 3.78/0.99  cnf(c_2121,plain,
% 3.78/0.99      ( sK7 = sK7 ),
% 3.78/0.99      inference(instantiation,[status(thm)],[c_2088]) ).
% 3.78/0.99  
% 3.78/0.99  cnf(c_3184,plain,
% 3.78/0.99      ( sK8 = sK8 ),
% 3.78/0.99      inference(instantiation,[status(thm)],[c_2088]) ).
% 3.78/0.99  
% 3.78/0.99  cnf(c_15,plain,
% 3.78/0.99      ( ~ l1_orders_2(X0)
% 3.78/0.99      | k1_yellow_0(X0,k1_xboole_0) = k3_yellow_0(X0) ),
% 3.78/0.99      inference(cnf_transformation,[],[f86]) ).
% 3.78/0.99  
% 3.78/0.99  cnf(c_853,plain,
% 3.78/0.99      ( k1_yellow_0(X0,k1_xboole_0) = k3_yellow_0(X0) | sK7 != X0 ),
% 3.78/0.99      inference(resolution_lifted,[status(thm)],[c_15,c_36]) ).
% 3.78/0.99  
% 3.78/0.99  cnf(c_854,plain,
% 3.78/0.99      ( k1_yellow_0(sK7,k1_xboole_0) = k3_yellow_0(sK7) ),
% 3.78/0.99      inference(unflattening,[status(thm)],[c_853]) ).
% 3.78/0.99  
% 3.78/0.99  cnf(c_21,plain,
% 3.78/0.99      ( m1_subset_1(k1_yellow_0(X0,X1),u1_struct_0(X0))
% 3.78/0.99      | ~ l1_orders_2(X0) ),
% 3.78/0.99      inference(cnf_transformation,[],[f92]) ).
% 3.78/0.99  
% 3.78/0.99  cnf(c_844,plain,
% 3.78/0.99      ( m1_subset_1(k1_yellow_0(X0,X1),u1_struct_0(X0)) | sK7 != X0 ),
% 3.78/0.99      inference(resolution_lifted,[status(thm)],[c_21,c_36]) ).
% 3.78/0.99  
% 3.78/0.99  cnf(c_845,plain,
% 3.78/0.99      ( m1_subset_1(k1_yellow_0(sK7,X0),u1_struct_0(sK7)) ),
% 3.78/0.99      inference(unflattening,[status(thm)],[c_844]) ).
% 3.78/0.99  
% 3.78/0.99  cnf(c_2664,plain,
% 3.78/0.99      ( m1_subset_1(k1_yellow_0(sK7,X0),u1_struct_0(sK7)) = iProver_top ),
% 3.78/0.99      inference(predicate_to_equality,[status(thm)],[c_845]) ).
% 3.78/0.99  
% 3.78/0.99  cnf(c_3036,plain,
% 3.78/0.99      ( m1_subset_1(k3_yellow_0(sK7),u1_struct_0(sK7)) = iProver_top ),
% 3.78/0.99      inference(superposition,[status(thm)],[c_854,c_2664]) ).
% 3.78/0.99  
% 3.78/0.99  cnf(c_9,plain,
% 3.78/0.99      ( ~ m1_subset_1(X0,X1) | r2_hidden(X0,X1) | v1_xboole_0(X1) ),
% 3.78/0.99      inference(cnf_transformation,[],[f80]) ).
% 3.78/0.99  
% 3.78/0.99  cnf(c_2679,plain,
% 3.78/0.99      ( m1_subset_1(X0,X1) != iProver_top
% 3.78/0.99      | r2_hidden(X0,X1) = iProver_top
% 3.78/0.99      | v1_xboole_0(X1) = iProver_top ),
% 3.78/0.99      inference(predicate_to_equality,[status(thm)],[c_9]) ).
% 3.78/0.99  
% 3.78/0.99  cnf(c_3306,plain,
% 3.78/0.99      ( r2_hidden(k3_yellow_0(sK7),u1_struct_0(sK7)) = iProver_top
% 3.78/0.99      | v1_xboole_0(u1_struct_0(sK7)) = iProver_top ),
% 3.78/0.99      inference(superposition,[status(thm)],[c_3036,c_2679]) ).
% 3.78/0.99  
% 3.78/0.99  cnf(c_2089,plain,( X0 != X1 | X2 != X1 | X2 = X0 ),theory(equality) ).
% 3.78/0.99  
% 3.78/0.99  cnf(c_3115,plain,
% 3.78/0.99      ( u1_struct_0(sK7) != X0 | sK8 != X0 | sK8 = u1_struct_0(sK7) ),
% 3.78/0.99      inference(instantiation,[status(thm)],[c_2089]) ).
% 3.78/0.99  
% 3.78/0.99  cnf(c_3637,plain,
% 3.78/0.99      ( u1_struct_0(sK7) != sK8 | sK8 = u1_struct_0(sK7) | sK8 != sK8 ),
% 3.78/0.99      inference(instantiation,[status(thm)],[c_3115]) ).
% 3.78/0.99  
% 3.78/0.99  cnf(c_19,plain,
% 3.78/0.99      ( r1_orders_2(X0,k1_yellow_0(X0,X1),X2)
% 3.78/0.99      | ~ r2_lattice3(X0,X1,X2)
% 3.78/0.99      | ~ r1_yellow_0(X0,X1)
% 3.78/0.99      | ~ m1_subset_1(X2,u1_struct_0(X0))
% 3.78/0.99      | ~ m1_subset_1(k1_yellow_0(X0,X1),u1_struct_0(X0))
% 3.78/0.99      | ~ l1_orders_2(X0) ),
% 3.78/0.99      inference(cnf_transformation,[],[f111]) ).
% 3.78/0.99  
% 3.78/0.99  cnf(c_243,plain,
% 3.78/0.99      ( ~ m1_subset_1(X2,u1_struct_0(X0))
% 3.78/0.99      | ~ r1_yellow_0(X0,X1)
% 3.78/0.99      | ~ r2_lattice3(X0,X1,X2)
% 3.78/0.99      | r1_orders_2(X0,k1_yellow_0(X0,X1),X2)
% 3.78/0.99      | ~ l1_orders_2(X0) ),
% 3.78/0.99      inference(global_propositional_subsumption,
% 3.78/0.99                [status(thm)],
% 3.78/0.99                [c_19,c_21]) ).
% 3.78/0.99  
% 3.78/0.99  cnf(c_244,plain,
% 3.78/0.99      ( r1_orders_2(X0,k1_yellow_0(X0,X1),X2)
% 3.78/0.99      | ~ r2_lattice3(X0,X1,X2)
% 3.78/0.99      | ~ r1_yellow_0(X0,X1)
% 3.78/0.99      | ~ m1_subset_1(X2,u1_struct_0(X0))
% 3.78/0.99      | ~ l1_orders_2(X0) ),
% 3.78/0.99      inference(renaming,[status(thm)],[c_243]) ).
% 3.78/0.99  
% 3.78/0.99  cnf(c_22,plain,
% 3.78/0.99      ( r1_yellow_0(X0,k1_xboole_0)
% 3.78/0.99      | v2_struct_0(X0)
% 3.78/0.99      | ~ v5_orders_2(X0)
% 3.78/0.99      | ~ v1_yellow_0(X0)
% 3.78/0.99      | ~ l1_orders_2(X0) ),
% 3.78/0.99      inference(cnf_transformation,[],[f93]) ).
% 3.78/0.99  
% 3.78/0.99  cnf(c_37,negated_conjecture,
% 3.78/0.99      ( v1_yellow_0(sK7) ),
% 3.78/0.99      inference(cnf_transformation,[],[f104]) ).
% 3.78/0.99  
% 3.78/0.99  cnf(c_538,plain,
% 3.78/0.99      ( r1_yellow_0(X0,k1_xboole_0)
% 3.78/0.99      | v2_struct_0(X0)
% 3.78/0.99      | ~ v5_orders_2(X0)
% 3.78/0.99      | ~ l1_orders_2(X0)
% 3.78/0.99      | sK7 != X0 ),
% 3.78/0.99      inference(resolution_lifted,[status(thm)],[c_22,c_37]) ).
% 3.78/0.99  
% 3.78/0.99  cnf(c_539,plain,
% 3.78/0.99      ( r1_yellow_0(sK7,k1_xboole_0)
% 3.78/0.99      | v2_struct_0(sK7)
% 3.78/0.99      | ~ v5_orders_2(sK7)
% 3.78/0.99      | ~ l1_orders_2(sK7) ),
% 3.78/0.99      inference(unflattening,[status(thm)],[c_538]) ).
% 3.78/0.99  
% 3.78/0.99  cnf(c_39,negated_conjecture,
% 3.78/0.99      ( ~ v2_struct_0(sK7) ),
% 3.78/0.99      inference(cnf_transformation,[],[f102]) ).
% 3.78/0.99  
% 3.78/0.99  cnf(c_38,negated_conjecture,
% 3.78/0.99      ( v5_orders_2(sK7) ),
% 3.78/0.99      inference(cnf_transformation,[],[f103]) ).
% 3.78/0.99  
% 3.78/0.99  cnf(c_72,plain,
% 3.78/0.99      ( r1_yellow_0(sK7,k1_xboole_0)
% 3.78/0.99      | v2_struct_0(sK7)
% 3.78/0.99      | ~ v5_orders_2(sK7)
% 3.78/0.99      | ~ v1_yellow_0(sK7)
% 3.78/0.99      | ~ l1_orders_2(sK7) ),
% 3.78/0.99      inference(instantiation,[status(thm)],[c_22]) ).
% 3.78/0.99  
% 3.78/0.99  cnf(c_541,plain,
% 3.78/0.99      ( r1_yellow_0(sK7,k1_xboole_0) ),
% 3.78/0.99      inference(global_propositional_subsumption,
% 3.78/0.99                [status(thm)],
% 3.78/0.99                [c_539,c_39,c_38,c_37,c_36,c_72]) ).
% 3.78/0.99  
% 3.78/0.99  cnf(c_703,plain,
% 3.78/0.99      ( r1_orders_2(X0,k1_yellow_0(X0,X1),X2)
% 3.78/0.99      | ~ r2_lattice3(X0,X1,X2)
% 3.78/0.99      | ~ m1_subset_1(X2,u1_struct_0(X0))
% 3.78/0.99      | ~ l1_orders_2(X0)
% 3.78/0.99      | sK7 != X0
% 3.78/0.99      | k1_xboole_0 != X1 ),
% 3.78/0.99      inference(resolution_lifted,[status(thm)],[c_244,c_541]) ).
% 3.78/0.99  
% 3.78/0.99  cnf(c_704,plain,
% 3.78/0.99      ( r1_orders_2(sK7,k1_yellow_0(sK7,k1_xboole_0),X0)
% 3.78/0.99      | ~ r2_lattice3(sK7,k1_xboole_0,X0)
% 3.78/0.99      | ~ m1_subset_1(X0,u1_struct_0(sK7))
% 3.78/0.99      | ~ l1_orders_2(sK7) ),
% 3.78/0.99      inference(unflattening,[status(thm)],[c_703]) ).
% 3.78/0.99  
% 3.78/0.99  cnf(c_708,plain,
% 3.78/0.99      ( ~ m1_subset_1(X0,u1_struct_0(sK7))
% 3.78/0.99      | ~ r2_lattice3(sK7,k1_xboole_0,X0)
% 3.78/0.99      | r1_orders_2(sK7,k1_yellow_0(sK7,k1_xboole_0),X0) ),
% 3.78/0.99      inference(global_propositional_subsumption,
% 3.78/0.99                [status(thm)],
% 3.78/0.99                [c_704,c_36]) ).
% 3.78/0.99  
% 3.78/0.99  cnf(c_709,plain,
% 3.78/0.99      ( r1_orders_2(sK7,k1_yellow_0(sK7,k1_xboole_0),X0)
% 3.78/0.99      | ~ r2_lattice3(sK7,k1_xboole_0,X0)
% 3.78/0.99      | ~ m1_subset_1(X0,u1_struct_0(sK7)) ),
% 3.78/0.99      inference(renaming,[status(thm)],[c_708]) ).
% 3.78/0.99  
% 3.78/0.99  cnf(c_2670,plain,
% 3.78/0.99      ( r1_orders_2(sK7,k1_yellow_0(sK7,k1_xboole_0),X0) = iProver_top
% 3.78/0.99      | r2_lattice3(sK7,k1_xboole_0,X0) != iProver_top
% 3.78/0.99      | m1_subset_1(X0,u1_struct_0(sK7)) != iProver_top ),
% 3.78/0.99      inference(predicate_to_equality,[status(thm)],[c_709]) ).
% 3.78/0.99  
% 3.78/0.99  cnf(c_2783,plain,
% 3.78/0.99      ( r1_orders_2(sK7,k3_yellow_0(sK7),X0) = iProver_top
% 3.78/0.99      | r2_lattice3(sK7,k1_xboole_0,X0) != iProver_top
% 3.78/0.99      | m1_subset_1(X0,u1_struct_0(sK7)) != iProver_top ),
% 3.78/0.99      inference(light_normalisation,[status(thm)],[c_2670,c_854]) ).
% 3.78/0.99  
% 3.78/0.99  cnf(c_5130,plain,
% 3.78/0.99      ( r2_lattice3(sK7,k1_xboole_0,X0) != iProver_top
% 3.78/0.99      | m1_subset_1(X0,u1_struct_0(sK7)) != iProver_top
% 3.78/0.99      | r2_hidden(X0,sK8) = iProver_top
% 3.78/0.99      | r2_hidden(k3_yellow_0(sK7),sK8) != iProver_top ),
% 3.78/0.99      inference(superposition,[status(thm)],[c_2783,c_5121]) ).
% 3.78/0.99  
% 3.78/0.99  cnf(c_31,negated_conjecture,
% 3.78/0.99      ( ~ v1_subset_1(sK8,u1_struct_0(sK7))
% 3.78/0.99      | r2_hidden(k3_yellow_0(sK7),sK8) ),
% 3.78/0.99      inference(cnf_transformation,[],[f110]) ).
% 3.78/0.99  
% 3.78/0.99  cnf(c_317,plain,
% 3.78/0.99      ( ~ v1_subset_1(sK8,u1_struct_0(sK7))
% 3.78/0.99      | r2_hidden(k3_yellow_0(sK7),sK8) ),
% 3.78/0.99      inference(prop_impl,[status(thm)],[c_31]) ).
% 3.78/0.99  
% 3.78/0.99  cnf(c_641,plain,
% 3.78/0.99      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
% 3.78/0.99      | r2_hidden(k3_yellow_0(sK7),sK8)
% 3.78/0.99      | X1 = X0
% 3.78/0.99      | u1_struct_0(sK7) != X1
% 3.78/0.99      | sK8 != X0 ),
% 3.78/0.99      inference(resolution_lifted,[status(thm)],[c_29,c_317]) ).
% 3.78/0.99  
% 3.78/0.99  cnf(c_642,plain,
% 3.78/0.99      ( ~ m1_subset_1(sK8,k1_zfmisc_1(u1_struct_0(sK7)))
% 3.78/0.99      | r2_hidden(k3_yellow_0(sK7),sK8)
% 3.78/0.99      | u1_struct_0(sK7) = sK8 ),
% 3.78/0.99      inference(unflattening,[status(thm)],[c_641]) ).
% 3.78/0.99  
% 3.78/0.99  cnf(c_644,plain,
% 3.78/0.99      ( r2_hidden(k3_yellow_0(sK7),sK8) | u1_struct_0(sK7) = sK8 ),
% 3.78/0.99      inference(global_propositional_subsumption,
% 3.78/0.99                [status(thm)],
% 3.78/0.99                [c_642,c_33]) ).
% 3.78/0.99  
% 3.78/0.99  cnf(c_2673,plain,
% 3.78/0.99      ( u1_struct_0(sK7) = sK8
% 3.78/0.99      | r2_hidden(k3_yellow_0(sK7),sK8) = iProver_top ),
% 3.78/0.99      inference(predicate_to_equality,[status(thm)],[c_644]) ).
% 3.78/0.99  
% 3.78/0.99  cnf(c_5497,plain,
% 3.78/0.99      ( u1_struct_0(sK7) = sK8
% 3.78/0.99      | r2_lattice3(sK7,k1_xboole_0,X0) != iProver_top
% 3.78/0.99      | m1_subset_1(X0,u1_struct_0(sK7)) != iProver_top
% 3.78/0.99      | r2_hidden(X0,sK8) = iProver_top ),
% 3.78/0.99      inference(superposition,[status(thm)],[c_2673,c_5130]) ).
% 3.78/0.99  
% 3.78/0.99  cnf(c_12,plain,
% 3.78/0.99      ( r2_lattice3(X0,X1,X2)
% 3.78/0.99      | ~ m1_subset_1(X2,u1_struct_0(X0))
% 3.78/0.99      | r2_hidden(sK3(X0,X1,X2),X1)
% 3.78/0.99      | ~ l1_orders_2(X0) ),
% 3.78/0.99      inference(cnf_transformation,[],[f84]) ).
% 3.78/0.99  
% 3.78/0.99  cnf(c_894,plain,
% 3.78/0.99      ( r2_lattice3(X0,X1,X2)
% 3.78/0.99      | ~ m1_subset_1(X2,u1_struct_0(X0))
% 3.78/0.99      | r2_hidden(sK3(X0,X1,X2),X1)
% 3.78/0.99      | sK7 != X0 ),
% 3.78/0.99      inference(resolution_lifted,[status(thm)],[c_12,c_36]) ).
% 3.78/0.99  
% 3.78/0.99  cnf(c_895,plain,
% 3.78/0.99      ( r2_lattice3(sK7,X0,X1)
% 3.78/0.99      | ~ m1_subset_1(X1,u1_struct_0(sK7))
% 3.78/0.99      | r2_hidden(sK3(sK7,X0,X1),X0) ),
% 3.78/0.99      inference(unflattening,[status(thm)],[c_894]) ).
% 3.78/0.99  
% 3.78/0.99  cnf(c_2661,plain,
% 3.78/0.99      ( r2_lattice3(sK7,X0,X1) = iProver_top
% 3.78/0.99      | m1_subset_1(X1,u1_struct_0(sK7)) != iProver_top
% 3.78/0.99      | r2_hidden(sK3(sK7,X0,X1),X0) = iProver_top ),
% 3.78/0.99      inference(predicate_to_equality,[status(thm)],[c_895]) ).
% 3.78/0.99  
% 3.78/0.99  cnf(c_20,plain,
% 3.78/0.99      ( r2_lattice3(X0,X1,k1_yellow_0(X0,X1))
% 3.78/0.99      | ~ r1_yellow_0(X0,X1)
% 3.78/0.99      | ~ m1_subset_1(k1_yellow_0(X0,X1),u1_struct_0(X0))
% 3.78/0.99      | ~ l1_orders_2(X0) ),
% 3.78/0.99      inference(cnf_transformation,[],[f112]) ).
% 3.78/0.99  
% 3.78/0.99  cnf(c_236,plain,
% 3.78/0.99      ( ~ r1_yellow_0(X0,X1)
% 3.78/0.99      | r2_lattice3(X0,X1,k1_yellow_0(X0,X1))
% 3.78/0.99      | ~ l1_orders_2(X0) ),
% 3.78/0.99      inference(global_propositional_subsumption,
% 3.78/0.99                [status(thm)],
% 3.78/0.99                [c_20,c_21]) ).
% 3.78/0.99  
% 3.78/0.99  cnf(c_237,plain,
% 3.78/0.99      ( r2_lattice3(X0,X1,k1_yellow_0(X0,X1))
% 3.78/0.99      | ~ r1_yellow_0(X0,X1)
% 3.78/0.99      | ~ l1_orders_2(X0) ),
% 3.78/0.99      inference(renaming,[status(thm)],[c_236]) ).
% 3.78/0.99  
% 3.78/0.99  cnf(c_724,plain,
% 3.78/0.99      ( r2_lattice3(X0,X1,k1_yellow_0(X0,X1))
% 3.78/0.99      | ~ l1_orders_2(X0)
% 3.78/0.99      | sK7 != X0
% 3.78/0.99      | k1_xboole_0 != X1 ),
% 3.78/0.99      inference(resolution_lifted,[status(thm)],[c_237,c_541]) ).
% 3.78/0.99  
% 3.78/0.99  cnf(c_725,plain,
% 3.78/0.99      ( r2_lattice3(sK7,k1_xboole_0,k1_yellow_0(sK7,k1_xboole_0))
% 3.78/0.99      | ~ l1_orders_2(sK7) ),
% 3.78/0.99      inference(unflattening,[status(thm)],[c_724]) ).
% 3.78/0.99  
% 3.78/0.99  cnf(c_727,plain,
% 3.78/0.99      ( r2_lattice3(sK7,k1_xboole_0,k1_yellow_0(sK7,k1_xboole_0)) ),
% 3.78/0.99      inference(global_propositional_subsumption,
% 3.78/0.99                [status(thm)],
% 3.78/0.99                [c_725,c_36]) ).
% 3.78/0.99  
% 3.78/0.99  cnf(c_2669,plain,
% 3.78/0.99      ( r2_lattice3(sK7,k1_xboole_0,k1_yellow_0(sK7,k1_xboole_0)) = iProver_top ),
% 3.78/0.99      inference(predicate_to_equality,[status(thm)],[c_727]) ).
% 3.78/0.99  
% 3.78/0.99  cnf(c_2705,plain,
% 3.78/0.99      ( r2_lattice3(sK7,k1_xboole_0,k3_yellow_0(sK7)) = iProver_top ),
% 3.78/0.99      inference(light_normalisation,[status(thm)],[c_2669,c_854]) ).
% 3.78/0.99  
% 3.78/0.99  cnf(c_4002,plain,
% 3.78/0.99      ( m1_subset_1(X0,u1_struct_0(sK7)) = iProver_top
% 3.78/0.99      | r2_hidden(X0,sK8) != iProver_top ),
% 3.78/0.99      inference(superposition,[status(thm)],[c_2677,c_2678]) ).
% 3.78/0.99  
% 3.78/0.99  cnf(c_4288,plain,
% 3.78/0.99      ( r1_orders_2(sK7,X0,X1) = iProver_top
% 3.78/0.99      | r2_lattice3(sK7,X2,X1) != iProver_top
% 3.78/0.99      | m1_subset_1(X1,u1_struct_0(sK7)) != iProver_top
% 3.78/0.99      | r2_hidden(X0,X2) != iProver_top
% 3.78/0.99      | r2_hidden(X0,sK8) != iProver_top ),
% 3.78/0.99      inference(superposition,[status(thm)],[c_4002,c_2663]) ).
% 3.78/0.99  
% 3.78/0.99  cnf(c_5980,plain,
% 3.78/0.99      ( r1_orders_2(sK7,X0,k3_yellow_0(sK7)) = iProver_top
% 3.78/0.99      | r2_lattice3(sK7,X1,k3_yellow_0(sK7)) != iProver_top
% 3.78/0.99      | r2_hidden(X0,X1) != iProver_top
% 3.78/0.99      | r2_hidden(X0,sK8) != iProver_top ),
% 3.78/0.99      inference(superposition,[status(thm)],[c_3036,c_4288]) ).
% 3.78/0.99  
% 3.78/0.99  cnf(c_6113,plain,
% 3.78/0.99      ( r1_orders_2(sK7,X0,k3_yellow_0(sK7)) = iProver_top
% 3.78/0.99      | r2_hidden(X0,sK8) != iProver_top
% 3.78/0.99      | r2_hidden(X0,k1_xboole_0) != iProver_top ),
% 3.78/0.99      inference(superposition,[status(thm)],[c_2705,c_5980]) ).
% 3.78/0.99  
% 3.78/0.99  cnf(c_2,plain,
% 3.78/0.99      ( v1_xboole_0(k1_xboole_0) ),
% 3.78/0.99      inference(cnf_transformation,[],[f73]) ).
% 3.78/0.99  
% 3.78/0.99  cnf(c_582,plain,
% 3.78/0.99      ( ~ r2_hidden(X0,X1) | k1_xboole_0 != X1 ),
% 3.78/0.99      inference(resolution_lifted,[status(thm)],[c_1,c_2]) ).
% 3.78/0.99  
% 3.78/0.99  cnf(c_583,plain,
% 3.78/0.99      ( ~ r2_hidden(X0,k1_xboole_0) ),
% 3.78/0.99      inference(unflattening,[status(thm)],[c_582]) ).
% 3.78/0.99  
% 3.78/0.99  cnf(c_584,plain,
% 3.78/0.99      ( r2_hidden(X0,k1_xboole_0) != iProver_top ),
% 3.78/0.99      inference(predicate_to_equality,[status(thm)],[c_583]) ).
% 3.78/0.99  
% 3.78/0.99  cnf(c_6232,plain,
% 3.78/0.99      ( r2_hidden(X0,k1_xboole_0) != iProver_top ),
% 3.78/0.99      inference(global_propositional_subsumption,
% 3.78/0.99                [status(thm)],
% 3.78/0.99                [c_6113,c_584]) ).
% 3.78/0.99  
% 3.78/0.99  cnf(c_6240,plain,
% 3.78/0.99      ( r2_lattice3(sK7,k1_xboole_0,X0) = iProver_top
% 3.78/0.99      | m1_subset_1(X0,u1_struct_0(sK7)) != iProver_top ),
% 3.78/0.99      inference(superposition,[status(thm)],[c_2661,c_6232]) ).
% 3.78/0.99  
% 3.78/0.99  cnf(c_2091,plain,
% 3.78/0.99      ( ~ r2_hidden(X0,X1) | r2_hidden(X2,X3) | X2 != X0 | X3 != X1 ),
% 3.78/0.99      theory(equality) ).
% 3.78/0.99  
% 3.78/0.99  cnf(c_3853,plain,
% 3.78/0.99      ( r2_hidden(X0,X1)
% 3.78/0.99      | ~ r2_hidden(k3_yellow_0(sK7),u1_struct_0(sK7))
% 3.78/0.99      | X0 != k3_yellow_0(sK7)
% 3.78/0.99      | X1 != u1_struct_0(sK7) ),
% 3.78/0.99      inference(instantiation,[status(thm)],[c_2091]) ).
% 3.78/0.99  
% 3.78/0.99  cnf(c_4422,plain,
% 3.78/0.99      ( r2_hidden(k3_yellow_0(sK7),X0)
% 3.78/0.99      | ~ r2_hidden(k3_yellow_0(sK7),u1_struct_0(sK7))
% 3.78/0.99      | X0 != u1_struct_0(sK7)
% 3.78/0.99      | k3_yellow_0(sK7) != k3_yellow_0(sK7) ),
% 3.78/0.99      inference(instantiation,[status(thm)],[c_3853]) ).
% 3.78/0.99  
% 3.78/0.99  cnf(c_7126,plain,
% 3.78/0.99      ( ~ r2_hidden(k3_yellow_0(sK7),u1_struct_0(sK7))
% 3.78/0.99      | r2_hidden(k3_yellow_0(sK7),sK8)
% 3.78/0.99      | k3_yellow_0(sK7) != k3_yellow_0(sK7)
% 3.78/0.99      | sK8 != u1_struct_0(sK7) ),
% 3.78/0.99      inference(instantiation,[status(thm)],[c_4422]) ).
% 3.78/0.99  
% 3.78/0.99  cnf(c_7127,plain,
% 3.78/0.99      ( k3_yellow_0(sK7) != k3_yellow_0(sK7)
% 3.78/0.99      | sK8 != u1_struct_0(sK7)
% 3.78/0.99      | r2_hidden(k3_yellow_0(sK7),u1_struct_0(sK7)) != iProver_top
% 3.78/0.99      | r2_hidden(k3_yellow_0(sK7),sK8) = iProver_top ),
% 3.78/0.99      inference(predicate_to_equality,[status(thm)],[c_7126]) ).
% 3.78/0.99  
% 3.78/0.99  cnf(c_9540,plain,
% 3.78/0.99      ( r2_hidden(X0,sK8) = iProver_top
% 3.78/0.99      | m1_subset_1(X0,u1_struct_0(sK7)) != iProver_top ),
% 3.78/0.99      inference(global_propositional_subsumption,
% 3.78/0.99                [status(thm)],
% 3.78/0.99                [c_9408,c_46,c_577,c_2114,c_2121,c_3184,c_3270,c_3306,
% 3.78/0.99                 c_3637,c_3734,c_5130,c_5497,c_6240,c_7127]) ).
% 3.78/0.99  
% 3.78/0.99  cnf(c_9541,plain,
% 3.78/0.99      ( m1_subset_1(X0,u1_struct_0(sK7)) != iProver_top
% 3.78/0.99      | r2_hidden(X0,sK8) = iProver_top ),
% 3.78/0.99      inference(renaming,[status(thm)],[c_9540]) ).
% 3.78/0.99  
% 3.78/0.99  cnf(c_9548,plain,
% 3.78/0.99      ( X0 = X1
% 3.78/0.99      | m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK7))) != iProver_top
% 3.78/0.99      | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK7))) != iProver_top
% 3.78/0.99      | r2_hidden(sK1(u1_struct_0(sK7),X1,X0),sK8) = iProver_top ),
% 3.78/0.99      inference(superposition,[status(thm)],[c_2681,c_9541]) ).
% 3.78/0.99  
% 3.78/0.99  cnf(c_4,plain,
% 3.78/0.99      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
% 3.78/0.99      | ~ m1_subset_1(X2,k1_zfmisc_1(X1))
% 3.78/0.99      | ~ r2_hidden(sK1(X1,X0,X2),X2)
% 3.78/0.99      | ~ r2_hidden(sK1(X1,X0,X2),X0)
% 3.78/0.99      | X0 = X2 ),
% 3.78/0.99      inference(cnf_transformation,[],[f77]) ).
% 3.78/0.99  
% 3.78/0.99  cnf(c_2683,plain,
% 3.78/0.99      ( X0 = X1
% 3.78/0.99      | m1_subset_1(X0,k1_zfmisc_1(X2)) != iProver_top
% 3.78/0.99      | m1_subset_1(X1,k1_zfmisc_1(X2)) != iProver_top
% 3.78/0.99      | r2_hidden(sK1(X2,X0,X1),X1) != iProver_top
% 3.78/0.99      | r2_hidden(sK1(X2,X0,X1),X0) != iProver_top ),
% 3.78/0.99      inference(predicate_to_equality,[status(thm)],[c_4]) ).
% 3.78/0.99  
% 3.78/0.99  cnf(c_4859,plain,
% 3.78/0.99      ( u1_struct_0(sK7) = X0
% 3.78/0.99      | m1_subset_1(X0,k1_zfmisc_1(X1)) != iProver_top
% 3.78/0.99      | m1_subset_1(u1_struct_0(sK7),k1_zfmisc_1(X1)) != iProver_top
% 3.78/0.99      | r2_hidden(sK1(X1,X0,u1_struct_0(sK7)),X0) != iProver_top
% 3.78/0.99      | r2_hidden(sK1(X1,X0,u1_struct_0(sK7)),sK8) != iProver_top ),
% 3.78/0.99      inference(superposition,[status(thm)],[c_4010,c_2683]) ).
% 3.78/0.99  
% 3.78/0.99  cnf(c_9878,plain,
% 3.78/0.99      ( u1_struct_0(sK7) = sK8
% 3.78/0.99      | m1_subset_1(u1_struct_0(sK7),k1_zfmisc_1(u1_struct_0(sK7))) != iProver_top
% 3.78/0.99      | m1_subset_1(sK8,k1_zfmisc_1(u1_struct_0(sK7))) != iProver_top
% 3.78/0.99      | r2_hidden(sK1(u1_struct_0(sK7),sK8,u1_struct_0(sK7)),sK8) != iProver_top ),
% 3.78/0.99      inference(superposition,[status(thm)],[c_9548,c_4859]) ).
% 3.78/0.99  
% 3.78/0.99  cnf(c_9883,plain,
% 3.78/0.99      ( u1_struct_0(sK7) = sK8
% 3.78/0.99      | m1_subset_1(u1_struct_0(sK7),k1_zfmisc_1(u1_struct_0(sK7))) != iProver_top
% 3.78/0.99      | m1_subset_1(sK8,k1_zfmisc_1(u1_struct_0(sK7))) != iProver_top ),
% 3.78/0.99      inference(forward_subsumption_resolution,
% 3.78/0.99                [status(thm)],
% 3.78/0.99                [c_9878,c_9548]) ).
% 3.78/0.99  
% 3.78/0.99  cnf(c_9555,plain,
% 3.78/0.99      ( r2_hidden(k3_yellow_0(sK7),sK8) = iProver_top ),
% 3.78/0.99      inference(superposition,[status(thm)],[c_3036,c_9541]) ).
% 3.78/0.99  
% 3.78/0.99  cnf(c_2093,plain,
% 3.78/0.99      ( ~ m1_subset_1(X0,X1) | m1_subset_1(X2,X3) | X2 != X0 | X3 != X1 ),
% 3.78/0.99      theory(equality) ).
% 3.78/0.99  
% 3.78/0.99  cnf(c_3056,plain,
% 3.78/0.99      ( m1_subset_1(X0,X1)
% 3.78/0.99      | ~ m1_subset_1(sK2(X2),k1_zfmisc_1(X2))
% 3.78/0.99      | X0 != sK2(X2)
% 3.78/0.99      | X1 != k1_zfmisc_1(X2) ),
% 3.78/0.99      inference(instantiation,[status(thm)],[c_2093]) ).
% 3.78/0.99  
% 3.78/0.99  cnf(c_3473,plain,
% 3.78/0.99      ( m1_subset_1(X0,k1_zfmisc_1(X1))
% 3.78/0.99      | ~ m1_subset_1(sK2(X1),k1_zfmisc_1(X1))
% 3.78/0.99      | X0 != sK2(X1)
% 3.78/0.99      | k1_zfmisc_1(X1) != k1_zfmisc_1(X1) ),
% 3.78/0.99      inference(instantiation,[status(thm)],[c_3056]) ).
% 3.78/0.99  
% 3.78/0.99  cnf(c_4550,plain,
% 3.78/0.99      ( m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK7)))
% 3.78/0.99      | ~ m1_subset_1(sK2(u1_struct_0(sK7)),k1_zfmisc_1(u1_struct_0(sK7)))
% 3.78/0.99      | X0 != sK2(u1_struct_0(sK7))
% 3.78/0.99      | k1_zfmisc_1(u1_struct_0(sK7)) != k1_zfmisc_1(u1_struct_0(sK7)) ),
% 3.78/0.99      inference(instantiation,[status(thm)],[c_3473]) ).
% 3.78/0.99  
% 3.78/0.99  cnf(c_6224,plain,
% 3.78/0.99      ( m1_subset_1(u1_struct_0(sK7),k1_zfmisc_1(u1_struct_0(sK7)))
% 3.78/0.99      | ~ m1_subset_1(sK2(u1_struct_0(sK7)),k1_zfmisc_1(u1_struct_0(sK7)))
% 3.78/0.99      | u1_struct_0(sK7) != sK2(u1_struct_0(sK7))
% 3.78/0.99      | k1_zfmisc_1(u1_struct_0(sK7)) != k1_zfmisc_1(u1_struct_0(sK7)) ),
% 3.78/0.99      inference(instantiation,[status(thm)],[c_4550]) ).
% 3.78/0.99  
% 3.78/0.99  cnf(c_6225,plain,
% 3.78/0.99      ( u1_struct_0(sK7) != sK2(u1_struct_0(sK7))
% 3.78/0.99      | k1_zfmisc_1(u1_struct_0(sK7)) != k1_zfmisc_1(u1_struct_0(sK7))
% 3.78/0.99      | m1_subset_1(u1_struct_0(sK7),k1_zfmisc_1(u1_struct_0(sK7))) = iProver_top
% 3.78/0.99      | m1_subset_1(sK2(u1_struct_0(sK7)),k1_zfmisc_1(u1_struct_0(sK7))) != iProver_top ),
% 3.78/0.99      inference(predicate_to_equality,[status(thm)],[c_6224]) ).
% 3.78/0.99  
% 3.78/0.99  cnf(c_2092,plain,
% 3.78/0.99      ( X0 != X1 | k1_zfmisc_1(X0) = k1_zfmisc_1(X1) ),
% 3.78/0.99      theory(equality) ).
% 3.78/0.99  
% 3.78/0.99  cnf(c_3294,plain,
% 3.78/0.99      ( X0 != u1_struct_0(sK7)
% 3.78/0.99      | k1_zfmisc_1(X0) = k1_zfmisc_1(u1_struct_0(sK7)) ),
% 3.78/0.99      inference(instantiation,[status(thm)],[c_2092]) ).
% 3.78/0.99  
% 3.78/0.99  cnf(c_4791,plain,
% 3.78/0.99      ( u1_struct_0(sK7) != u1_struct_0(sK7)
% 3.78/0.99      | k1_zfmisc_1(u1_struct_0(sK7)) = k1_zfmisc_1(u1_struct_0(sK7)) ),
% 3.78/0.99      inference(instantiation,[status(thm)],[c_3294]) ).
% 3.78/0.99  
% 3.78/0.99  cnf(c_3574,plain,
% 3.78/0.99      ( u1_struct_0(sK7) = sK2(u1_struct_0(sK7)) ),
% 3.78/0.99      inference(instantiation,[status(thm)],[c_623]) ).
% 3.78/0.99  
% 3.78/0.99  cnf(c_3005,plain,
% 3.78/0.99      ( m1_subset_1(sK2(u1_struct_0(sK7)),k1_zfmisc_1(u1_struct_0(sK7))) ),
% 3.78/0.99      inference(instantiation,[status(thm)],[c_8]) ).
% 3.78/0.99  
% 3.78/0.99  cnf(c_3011,plain,
% 3.78/0.99      ( m1_subset_1(sK2(u1_struct_0(sK7)),k1_zfmisc_1(u1_struct_0(sK7))) = iProver_top ),
% 3.78/0.99      inference(predicate_to_equality,[status(thm)],[c_3005]) ).
% 3.78/0.99  
% 3.78/0.99  cnf(c_32,negated_conjecture,
% 3.78/0.99      ( v1_subset_1(sK8,u1_struct_0(sK7))
% 3.78/0.99      | ~ r2_hidden(k3_yellow_0(sK7),sK8) ),
% 3.78/0.99      inference(cnf_transformation,[],[f109]) ).
% 3.78/0.99  
% 3.78/0.99  cnf(c_315,plain,
% 3.78/0.99      ( v1_subset_1(sK8,u1_struct_0(sK7))
% 3.78/0.99      | ~ r2_hidden(k3_yellow_0(sK7),sK8) ),
% 3.78/0.99      inference(prop_impl,[status(thm)],[c_32]) ).
% 3.78/0.99  
% 3.78/0.99  cnf(c_629,plain,
% 3.78/0.99      ( ~ r2_hidden(k3_yellow_0(sK7),sK8)
% 3.78/0.99      | u1_struct_0(sK7) != X0
% 3.78/0.99      | sK2(X0) != sK8 ),
% 3.78/0.99      inference(resolution_lifted,[status(thm)],[c_7,c_315]) ).
% 3.78/0.99  
% 3.78/0.99  cnf(c_630,plain,
% 3.78/0.99      ( ~ r2_hidden(k3_yellow_0(sK7),sK8)
% 3.78/0.99      | sK2(u1_struct_0(sK7)) != sK8 ),
% 3.78/0.99      inference(unflattening,[status(thm)],[c_629]) ).
% 3.78/0.99  
% 3.78/0.99  cnf(c_2674,plain,
% 3.78/0.99      ( sK2(u1_struct_0(sK7)) != sK8
% 3.78/0.99      | r2_hidden(k3_yellow_0(sK7),sK8) != iProver_top ),
% 3.78/0.99      inference(predicate_to_equality,[status(thm)],[c_630]) ).
% 3.78/0.99  
% 3.78/0.99  cnf(c_2720,plain,
% 3.78/0.99      ( u1_struct_0(sK7) != sK8
% 3.78/0.99      | r2_hidden(k3_yellow_0(sK7),sK8) != iProver_top ),
% 3.78/0.99      inference(demodulation,[status(thm)],[c_2674,c_623]) ).
% 3.78/0.99  
% 3.78/0.99  cnf(c_2098,plain,
% 3.78/0.99      ( X0 != X1 | u1_struct_0(X0) = u1_struct_0(X1) ),
% 3.78/0.99      theory(equality) ).
% 3.78/0.99  
% 3.78/0.99  cnf(c_2113,plain,
% 3.78/0.99      ( u1_struct_0(sK7) = u1_struct_0(sK7) | sK7 != sK7 ),
% 3.78/0.99      inference(instantiation,[status(thm)],[c_2098]) ).
% 3.78/0.99  
% 3.78/0.99  cnf(contradiction,plain,
% 3.78/0.99      ( $false ),
% 3.78/0.99      inference(minisat,
% 3.78/0.99                [status(thm)],
% 3.78/0.99                [c_9883,c_9555,c_6225,c_4791,c_3574,c_3011,c_2720,c_2121,
% 3.78/0.99                 c_2113,c_46]) ).
% 3.78/0.99  
% 3.78/0.99  
% 3.78/0.99  % SZS output end CNFRefutation for theBenchmark.p
% 3.78/0.99  
% 3.78/0.99  ------                               Statistics
% 3.78/0.99  
% 3.78/0.99  ------ General
% 3.78/0.99  
% 3.78/0.99  abstr_ref_over_cycles:                  0
% 3.78/0.99  abstr_ref_under_cycles:                 0
% 3.78/0.99  gc_basic_clause_elim:                   0
% 3.78/0.99  forced_gc_time:                         0
% 3.78/0.99  parsing_time:                           0.009
% 3.78/0.99  unif_index_cands_time:                  0.
% 3.78/0.99  unif_index_add_time:                    0.
% 3.78/0.99  orderings_time:                         0.
% 3.78/0.99  out_proof_time:                         0.031
% 3.78/0.99  total_time:                             0.395
% 3.78/0.99  num_of_symbols:                         57
% 3.78/0.99  num_of_terms:                           7251
% 3.78/0.99  
% 3.78/0.99  ------ Preprocessing
% 3.78/0.99  
% 3.78/0.99  num_of_splits:                          0
% 3.78/0.99  num_of_split_atoms:                     0
% 3.78/0.99  num_of_reused_defs:                     0
% 3.78/0.99  num_eq_ax_congr_red:                    38
% 3.78/0.99  num_of_sem_filtered_clauses:            1
% 3.78/0.99  num_of_subtypes:                        0
% 3.78/0.99  monotx_restored_types:                  0
% 3.78/0.99  sat_num_of_epr_types:                   0
% 3.78/0.99  sat_num_of_non_cyclic_types:            0
% 3.78/0.99  sat_guarded_non_collapsed_types:        0
% 3.78/0.99  num_pure_diseq_elim:                    0
% 3.78/0.99  simp_replaced_by:                       0
% 3.78/0.99  res_preprocessed:                       177
% 3.78/0.99  prep_upred:                             0
% 3.78/0.99  prep_unflattend:                        77
% 3.78/0.99  smt_new_axioms:                         0
% 3.78/0.99  pred_elim_cands:                        6
% 3.78/0.99  pred_elim:                              6
% 3.78/0.99  pred_elim_cl:                           6
% 3.78/0.99  pred_elim_cycles:                       12
% 3.78/0.99  merged_defs:                            2
% 3.78/0.99  merged_defs_ncl:                        0
% 3.78/0.99  bin_hyper_res:                          2
% 3.78/0.99  prep_cycles:                            4
% 3.78/0.99  pred_elim_time:                         0.026
% 3.78/0.99  splitting_time:                         0.
% 3.78/0.99  sem_filter_time:                        0.
% 3.78/0.99  monotx_time:                            0.001
% 3.78/0.99  subtype_inf_time:                       0.
% 3.78/0.99  
% 3.78/0.99  ------ Problem properties
% 3.78/0.99  
% 3.78/0.99  clauses:                                34
% 3.78/0.99  conjectures:                            3
% 3.78/0.99  epr:                                    5
% 3.78/0.99  horn:                                   21
% 3.78/0.99  ground:                                 9
% 3.78/0.99  unary:                                  9
% 3.78/0.99  binary:                                 4
% 3.78/0.99  lits:                                   93
% 3.78/0.99  lits_eq:                                11
% 3.78/0.99  fd_pure:                                0
% 3.78/0.99  fd_pseudo:                              0
% 3.78/0.99  fd_cond:                                3
% 3.78/0.99  fd_pseudo_cond:                         3
% 3.78/0.99  ac_symbols:                             0
% 3.78/0.99  
% 3.78/0.99  ------ Propositional Solver
% 3.78/0.99  
% 3.78/0.99  prop_solver_calls:                      29
% 3.78/0.99  prop_fast_solver_calls:                 1686
% 3.78/0.99  smt_solver_calls:                       0
% 3.78/0.99  smt_fast_solver_calls:                  0
% 3.78/0.99  prop_num_of_clauses:                    2995
% 3.78/0.99  prop_preprocess_simplified:             7909
% 3.78/0.99  prop_fo_subsumed:                       38
% 3.78/0.99  prop_solver_time:                       0.
% 3.78/0.99  smt_solver_time:                        0.
% 3.78/0.99  smt_fast_solver_time:                   0.
% 3.78/0.99  prop_fast_solver_time:                  0.
% 3.78/0.99  prop_unsat_core_time:                   0.
% 3.78/0.99  
% 3.78/0.99  ------ QBF
% 3.78/0.99  
% 3.78/0.99  qbf_q_res:                              0
% 3.78/0.99  qbf_num_tautologies:                    0
% 3.78/0.99  qbf_prep_cycles:                        0
% 3.78/0.99  
% 3.78/0.99  ------ BMC1
% 3.78/0.99  
% 3.78/0.99  bmc1_current_bound:                     -1
% 3.78/0.99  bmc1_last_solved_bound:                 -1
% 3.78/0.99  bmc1_unsat_core_size:                   -1
% 3.78/0.99  bmc1_unsat_core_parents_size:           -1
% 3.78/0.99  bmc1_merge_next_fun:                    0
% 3.78/0.99  bmc1_unsat_core_clauses_time:           0.
% 3.78/0.99  
% 3.78/0.99  ------ Instantiation
% 3.78/0.99  
% 3.78/0.99  inst_num_of_clauses:                    748
% 3.78/0.99  inst_num_in_passive:                    296
% 3.78/0.99  inst_num_in_active:                     439
% 3.78/0.99  inst_num_in_unprocessed:                13
% 3.78/0.99  inst_num_of_loops:                      490
% 3.78/0.99  inst_num_of_learning_restarts:          0
% 3.78/0.99  inst_num_moves_active_passive:          47
% 3.78/0.99  inst_lit_activity:                      0
% 3.78/0.99  inst_lit_activity_moves:                0
% 3.78/0.99  inst_num_tautologies:                   0
% 3.78/0.99  inst_num_prop_implied:                  0
% 3.78/0.99  inst_num_existing_simplified:           0
% 3.78/0.99  inst_num_eq_res_simplified:             0
% 3.78/0.99  inst_num_child_elim:                    0
% 3.78/0.99  inst_num_of_dismatching_blockings:      176
% 3.78/0.99  inst_num_of_non_proper_insts:           849
% 3.78/0.99  inst_num_of_duplicates:                 0
% 3.78/0.99  inst_inst_num_from_inst_to_res:         0
% 3.78/0.99  inst_dismatching_checking_time:         0.
% 3.78/0.99  
% 3.78/0.99  ------ Resolution
% 3.78/0.99  
% 3.78/0.99  res_num_of_clauses:                     0
% 3.78/0.99  res_num_in_passive:                     0
% 3.78/0.99  res_num_in_active:                      0
% 3.78/0.99  res_num_of_loops:                       181
% 3.78/0.99  res_forward_subset_subsumed:            133
% 3.78/0.99  res_backward_subset_subsumed:           0
% 3.78/0.99  res_forward_subsumed:                   0
% 3.78/0.99  res_backward_subsumed:                  0
% 3.78/0.99  res_forward_subsumption_resolution:     6
% 3.78/0.99  res_backward_subsumption_resolution:    0
% 3.78/0.99  res_clause_to_clause_subsumption:       993
% 3.78/0.99  res_orphan_elimination:                 0
% 3.78/0.99  res_tautology_del:                      73
% 3.78/0.99  res_num_eq_res_simplified:              0
% 3.78/0.99  res_num_sel_changes:                    0
% 3.78/0.99  res_moves_from_active_to_pass:          0
% 3.78/0.99  
% 3.78/0.99  ------ Superposition
% 3.78/0.99  
% 3.78/0.99  sup_time_total:                         0.
% 3.78/0.99  sup_time_generating:                    0.
% 3.78/0.99  sup_time_sim_full:                      0.
% 3.78/0.99  sup_time_sim_immed:                     0.
% 3.78/0.99  
% 3.78/0.99  sup_num_of_clauses:                     222
% 3.78/0.99  sup_num_in_active:                      98
% 3.78/0.99  sup_num_in_passive:                     124
% 3.78/0.99  sup_num_of_loops:                       97
% 3.78/0.99  sup_fw_superposition:                   137
% 3.78/0.99  sup_bw_superposition:                   144
% 3.78/0.99  sup_immediate_simplified:               59
% 3.78/0.99  sup_given_eliminated:                   0
% 3.78/0.99  comparisons_done:                       0
% 3.78/0.99  comparisons_avoided:                    0
% 3.78/0.99  
% 3.78/0.99  ------ Simplifications
% 3.78/0.99  
% 3.78/0.99  
% 3.78/0.99  sim_fw_subset_subsumed:                 20
% 3.78/0.99  sim_bw_subset_subsumed:                 4
% 3.78/0.99  sim_fw_subsumed:                        30
% 3.78/0.99  sim_bw_subsumed:                        3
% 3.78/0.99  sim_fw_subsumption_res:                 2
% 3.78/0.99  sim_bw_subsumption_res:                 0
% 3.78/0.99  sim_tautology_del:                      8
% 3.78/0.99  sim_eq_tautology_del:                   7
% 3.78/0.99  sim_eq_res_simp:                        0
% 3.78/0.99  sim_fw_demodulated:                     4
% 3.78/0.99  sim_bw_demodulated:                     0
% 3.78/0.99  sim_light_normalised:                   5
% 3.78/0.99  sim_joinable_taut:                      0
% 3.78/0.99  sim_joinable_simp:                      0
% 3.78/0.99  sim_ac_normalised:                      0
% 3.78/0.99  sim_smt_subsumption:                    0
% 3.78/0.99  
%------------------------------------------------------------------------------
