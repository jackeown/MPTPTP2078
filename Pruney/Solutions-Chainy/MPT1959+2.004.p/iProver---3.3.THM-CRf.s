%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n014.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:28:24 EST 2020

% Result     : Theorem 3.19s
% Output     : CNFRefutation 3.19s
% Verified   : 
% Statistics : Number of formulae       :  215 (3307 expanded)
%              Number of clauses        :  143 ( 827 expanded)
%              Number of leaves         :   19 ( 683 expanded)
%              Depth                    :   31
%              Number of atoms          :  830 (25008 expanded)
%              Number of equality atoms :  232 (1078 expanded)
%              Maximal formula depth    :   14 (   5 average)
%              Maximal clause size      :   22 (   3 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f1,axiom,(
    ! [X0,X1] :
      ( ! [X2] :
          ( r2_hidden(X2,X0)
        <=> r2_hidden(X2,X1) )
     => X0 = X1 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f16,plain,(
    ! [X0,X1] :
      ( X0 = X1
      | ? [X2] :
          ( r2_hidden(X2,X0)
        <~> r2_hidden(X2,X1) ) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f31,plain,(
    ! [X0,X1] :
      ( X0 = X1
      | ? [X2] :
          ( ( ~ r2_hidden(X2,X1)
            | ~ r2_hidden(X2,X0) )
          & ( r2_hidden(X2,X1)
            | r2_hidden(X2,X0) ) ) ) ),
    inference(nnf_transformation,[],[f16])).

fof(f32,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ( ~ r2_hidden(X2,X1)
            | ~ r2_hidden(X2,X0) )
          & ( r2_hidden(X2,X1)
            | r2_hidden(X2,X0) ) )
     => ( ( ~ r2_hidden(sK0(X0,X1),X1)
          | ~ r2_hidden(sK0(X0,X1),X0) )
        & ( r2_hidden(sK0(X0,X1),X1)
          | r2_hidden(sK0(X0,X1),X0) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f33,plain,(
    ! [X0,X1] :
      ( X0 = X1
      | ( ( ~ r2_hidden(sK0(X0,X1),X1)
          | ~ r2_hidden(sK0(X0,X1),X0) )
        & ( r2_hidden(sK0(X0,X1),X1)
          | r2_hidden(sK0(X0,X1),X0) ) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f31,f32])).

fof(f47,plain,(
    ! [X0,X1] :
      ( X0 = X1
      | r2_hidden(sK0(X0,X1),X1)
      | r2_hidden(sK0(X0,X1),X0) ) ),
    inference(cnf_transformation,[],[f33])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
     => m1_subset_1(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f18,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X0,X1)
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f52,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X0,X1)
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f10,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => ( v1_subset_1(X1,X0)
      <=> X0 != X1 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f28,plain,(
    ! [X0,X1] :
      ( ( v1_subset_1(X1,X0)
      <=> X0 != X1 )
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f41,plain,(
    ! [X0,X1] :
      ( ( ( v1_subset_1(X1,X0)
          | X0 = X1 )
        & ( X0 != X1
          | ~ v1_subset_1(X1,X0) ) )
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(nnf_transformation,[],[f28])).

fof(f64,plain,(
    ! [X0,X1] :
      ( v1_subset_1(X1,X0)
      | X0 = X1
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f41])).

fof(f11,conjecture,(
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

fof(f12,negated_conjecture,(
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
    inference(negated_conjecture,[],[f11])).

fof(f13,plain,(
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
    inference(pure_predicate_removal,[],[f12])).

fof(f14,plain,(
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
    inference(pure_predicate_removal,[],[f13])).

fof(f15,plain,(
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
    inference(pure_predicate_removal,[],[f14])).

fof(f29,plain,(
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
    inference(ennf_transformation,[],[f15])).

fof(f30,plain,(
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
    inference(flattening,[],[f29])).

fof(f42,plain,(
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
    inference(nnf_transformation,[],[f30])).

fof(f43,plain,(
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
    inference(flattening,[],[f42])).

fof(f45,plain,(
    ! [X0] :
      ( ? [X1] :
          ( ( r2_hidden(k3_yellow_0(X0),X1)
            | ~ v1_subset_1(X1,u1_struct_0(X0)) )
          & ( ~ r2_hidden(k3_yellow_0(X0),X1)
            | v1_subset_1(X1,u1_struct_0(X0)) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
          & v13_waybel_0(X1,X0)
          & ~ v1_xboole_0(X1) )
     => ( ( r2_hidden(k3_yellow_0(X0),sK5)
          | ~ v1_subset_1(sK5,u1_struct_0(X0)) )
        & ( ~ r2_hidden(k3_yellow_0(X0),sK5)
          | v1_subset_1(sK5,u1_struct_0(X0)) )
        & m1_subset_1(sK5,k1_zfmisc_1(u1_struct_0(X0)))
        & v13_waybel_0(sK5,X0)
        & ~ v1_xboole_0(sK5) ) ) ),
    introduced(choice_axiom,[])).

fof(f44,plain,
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
          ( ( r2_hidden(k3_yellow_0(sK4),X1)
            | ~ v1_subset_1(X1,u1_struct_0(sK4)) )
          & ( ~ r2_hidden(k3_yellow_0(sK4),X1)
            | v1_subset_1(X1,u1_struct_0(sK4)) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK4)))
          & v13_waybel_0(X1,sK4)
          & ~ v1_xboole_0(X1) )
      & l1_orders_2(sK4)
      & v1_yellow_0(sK4)
      & v5_orders_2(sK4)
      & ~ v2_struct_0(sK4) ) ),
    introduced(choice_axiom,[])).

fof(f46,plain,
    ( ( r2_hidden(k3_yellow_0(sK4),sK5)
      | ~ v1_subset_1(sK5,u1_struct_0(sK4)) )
    & ( ~ r2_hidden(k3_yellow_0(sK4),sK5)
      | v1_subset_1(sK5,u1_struct_0(sK4)) )
    & m1_subset_1(sK5,k1_zfmisc_1(u1_struct_0(sK4)))
    & v13_waybel_0(sK5,sK4)
    & ~ v1_xboole_0(sK5)
    & l1_orders_2(sK4)
    & v1_yellow_0(sK4)
    & v5_orders_2(sK4)
    & ~ v2_struct_0(sK4) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4,sK5])],[f43,f45,f44])).

fof(f73,plain,
    ( r2_hidden(k3_yellow_0(sK4),sK5)
    | ~ v1_subset_1(sK5,u1_struct_0(sK4)) ),
    inference(cnf_transformation,[],[f46])).

fof(f71,plain,(
    m1_subset_1(sK5,k1_zfmisc_1(u1_struct_0(sK4))) ),
    inference(cnf_transformation,[],[f46])).

fof(f9,axiom,(
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

fof(f26,plain,(
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
    inference(ennf_transformation,[],[f9])).

fof(f27,plain,(
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
    inference(flattening,[],[f26])).

fof(f36,plain,(
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
    inference(nnf_transformation,[],[f27])).

fof(f37,plain,(
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
    inference(rectify,[],[f36])).

fof(f39,plain,(
    ! [X2,X1,X0] :
      ( ? [X3] :
          ( ~ r2_hidden(X3,X1)
          & r1_orders_2(X0,X2,X3)
          & r2_hidden(X2,X1)
          & m1_subset_1(X3,u1_struct_0(X0)) )
     => ( ~ r2_hidden(sK3(X0,X1),X1)
        & r1_orders_2(X0,X2,sK3(X0,X1))
        & r2_hidden(X2,X1)
        & m1_subset_1(sK3(X0,X1),u1_struct_0(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f38,plain,(
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
            & r1_orders_2(X0,sK2(X0,X1),X3)
            & r2_hidden(sK2(X0,X1),X1)
            & m1_subset_1(X3,u1_struct_0(X0)) )
        & m1_subset_1(sK2(X0,X1),u1_struct_0(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f40,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ( v13_waybel_0(X1,X0)
              | ( ~ r2_hidden(sK3(X0,X1),X1)
                & r1_orders_2(X0,sK2(X0,X1),sK3(X0,X1))
                & r2_hidden(sK2(X0,X1),X1)
                & m1_subset_1(sK3(X0,X1),u1_struct_0(X0))
                & m1_subset_1(sK2(X0,X1),u1_struct_0(X0)) ) )
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
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2,sK3])],[f37,f39,f38])).

fof(f57,plain,(
    ! [X4,X0,X5,X1] :
      ( r2_hidden(X5,X1)
      | ~ r1_orders_2(X0,X4,X5)
      | ~ r2_hidden(X4,X1)
      | ~ m1_subset_1(X5,u1_struct_0(X0))
      | ~ m1_subset_1(X4,u1_struct_0(X0))
      | ~ v13_waybel_0(X1,X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f40])).

fof(f8,axiom,(
    ! [X0] :
      ( ( l1_orders_2(X0)
        & v1_yellow_0(X0)
        & v5_orders_2(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,u1_struct_0(X0))
         => r1_orders_2(X0,k3_yellow_0(X0),X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f24,plain,(
    ! [X0] :
      ( ! [X1] :
          ( r1_orders_2(X0,k3_yellow_0(X0),X1)
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l1_orders_2(X0)
      | ~ v1_yellow_0(X0)
      | ~ v5_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f25,plain,(
    ! [X0] :
      ( ! [X1] :
          ( r1_orders_2(X0,k3_yellow_0(X0),X1)
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l1_orders_2(X0)
      | ~ v1_yellow_0(X0)
      | ~ v5_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f24])).

fof(f56,plain,(
    ! [X0,X1] :
      ( r1_orders_2(X0,k3_yellow_0(X0),X1)
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | ~ v1_yellow_0(X0)
      | ~ v5_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f67,plain,(
    v1_yellow_0(sK4) ),
    inference(cnf_transformation,[],[f46])).

fof(f65,plain,(
    ~ v2_struct_0(sK4) ),
    inference(cnf_transformation,[],[f46])).

fof(f66,plain,(
    v5_orders_2(sK4) ),
    inference(cnf_transformation,[],[f46])).

fof(f68,plain,(
    l1_orders_2(sK4) ),
    inference(cnf_transformation,[],[f46])).

fof(f7,axiom,(
    ! [X0] :
      ( l1_orders_2(X0)
     => m1_subset_1(k3_yellow_0(X0),u1_struct_0(X0)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f23,plain,(
    ! [X0] :
      ( m1_subset_1(k3_yellow_0(X0),u1_struct_0(X0))
      | ~ l1_orders_2(X0) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f55,plain,(
    ! [X0] :
      ( m1_subset_1(k3_yellow_0(X0),u1_struct_0(X0))
      | ~ l1_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f70,plain,(
    v13_waybel_0(sK5,sK4) ),
    inference(cnf_transformation,[],[f46])).

fof(f61,plain,(
    ! [X0,X1] :
      ( v13_waybel_0(X1,X0)
      | r1_orders_2(X0,sK2(X0,X1),sK3(X0,X1))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f40])).

fof(f59,plain,(
    ! [X0,X1] :
      ( v13_waybel_0(X1,X0)
      | m1_subset_1(sK3(X0,X1),u1_struct_0(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f40])).

fof(f6,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(X2))
        & r2_hidden(X0,X1) )
     => m1_subset_1(X0,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f21,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X0,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f22,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X0,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(flattening,[],[f21])).

fof(f54,plain,(
    ! [X2,X0,X1] :
      ( m1_subset_1(X0,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f69,plain,(
    ~ v1_xboole_0(sK5) ),
    inference(cnf_transformation,[],[f46])).

fof(f3,axiom,(
    ! [X0] :
    ? [X1] :
      ( ~ v1_subset_1(X1,X0)
      & m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f34,plain,(
    ! [X0] :
      ( ? [X1] :
          ( ~ v1_subset_1(X1,X0)
          & m1_subset_1(X1,k1_zfmisc_1(X0)) )
     => ( ~ v1_subset_1(sK1(X0),X0)
        & m1_subset_1(sK1(X0),k1_zfmisc_1(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f35,plain,(
    ! [X0] :
      ( ~ v1_subset_1(sK1(X0),X0)
      & m1_subset_1(sK1(X0),k1_zfmisc_1(X0)) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1])],[f3,f34])).

fof(f50,plain,(
    ! [X0] : m1_subset_1(sK1(X0),k1_zfmisc_1(X0)) ),
    inference(cnf_transformation,[],[f35])).

fof(f5,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,X1)
     => ( r2_hidden(X0,X1)
        | v1_xboole_0(X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f19,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
      | v1_xboole_0(X1)
      | ~ m1_subset_1(X0,X1) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f20,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
      | v1_xboole_0(X1)
      | ~ m1_subset_1(X0,X1) ) ),
    inference(flattening,[],[f19])).

fof(f53,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
      | v1_xboole_0(X1)
      | ~ m1_subset_1(X0,X1) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f2,axiom,(
    ! [X0] :
      ( v1_xboole_0(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(X0))
         => v1_xboole_0(X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f17,plain,(
    ! [X0] :
      ( ! [X1] :
          ( v1_xboole_0(X1)
          | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) )
      | ~ v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f49,plain,(
    ! [X0,X1] :
      ( v1_xboole_0(X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | ~ v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f48,plain,(
    ! [X0,X1] :
      ( X0 = X1
      | ~ r2_hidden(sK0(X0,X1),X1)
      | ~ r2_hidden(sK0(X0,X1),X0) ) ),
    inference(cnf_transformation,[],[f33])).

fof(f51,plain,(
    ! [X0] : ~ v1_subset_1(sK1(X0),X0) ),
    inference(cnf_transformation,[],[f35])).

fof(f60,plain,(
    ! [X0,X1] :
      ( v13_waybel_0(X1,X0)
      | r2_hidden(sK2(X0,X1),X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f40])).

fof(f62,plain,(
    ! [X0,X1] :
      ( v13_waybel_0(X1,X0)
      | ~ r2_hidden(sK3(X0,X1),X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f40])).

fof(f58,plain,(
    ! [X0,X1] :
      ( v13_waybel_0(X1,X0)
      | m1_subset_1(sK2(X0,X1),u1_struct_0(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f40])).

fof(f72,plain,
    ( ~ r2_hidden(k3_yellow_0(sK4),sK5)
    | v1_subset_1(sK5,u1_struct_0(sK4)) ),
    inference(cnf_transformation,[],[f46])).

cnf(c_1,plain,
    ( r2_hidden(sK0(X0,X1),X1)
    | r2_hidden(sK0(X0,X1),X0)
    | X1 = X0 ),
    inference(cnf_transformation,[],[f47])).

cnf(c_1142,plain,
    ( X0 = X1
    | r2_hidden(sK0(X1,X0),X0) = iProver_top
    | r2_hidden(sK0(X1,X0),X1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1])).

cnf(c_5,plain,
    ( m1_subset_1(X0,X1)
    | ~ r2_hidden(X0,X1) ),
    inference(cnf_transformation,[],[f52])).

cnf(c_1139,plain,
    ( m1_subset_1(X0,X1) = iProver_top
    | r2_hidden(X0,X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_5])).

cnf(c_1643,plain,
    ( X0 = X1
    | m1_subset_1(sK0(X0,X1),X1) = iProver_top
    | r2_hidden(sK0(X0,X1),X0) = iProver_top ),
    inference(superposition,[status(thm)],[c_1142,c_1139])).

cnf(c_16,plain,
    ( v1_subset_1(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | X0 = X1 ),
    inference(cnf_transformation,[],[f64])).

cnf(c_18,negated_conjecture,
    ( ~ v1_subset_1(sK5,u1_struct_0(sK4))
    | r2_hidden(k3_yellow_0(sK4),sK5) ),
    inference(cnf_transformation,[],[f73])).

cnf(c_201,plain,
    ( ~ v1_subset_1(sK5,u1_struct_0(sK4))
    | r2_hidden(k3_yellow_0(sK4),sK5) ),
    inference(prop_impl,[status(thm)],[c_18])).

cnf(c_402,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | r2_hidden(k3_yellow_0(sK4),sK5)
    | X1 = X0
    | u1_struct_0(sK4) != X1
    | sK5 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_16,c_201])).

cnf(c_403,plain,
    ( ~ m1_subset_1(sK5,k1_zfmisc_1(u1_struct_0(sK4)))
    | r2_hidden(k3_yellow_0(sK4),sK5)
    | u1_struct_0(sK4) = sK5 ),
    inference(unflattening,[status(thm)],[c_402])).

cnf(c_20,negated_conjecture,
    ( m1_subset_1(sK5,k1_zfmisc_1(u1_struct_0(sK4))) ),
    inference(cnf_transformation,[],[f71])).

cnf(c_405,plain,
    ( r2_hidden(k3_yellow_0(sK4),sK5)
    | u1_struct_0(sK4) = sK5 ),
    inference(global_propositional_subsumption,[status(thm)],[c_403,c_20])).

cnf(c_1132,plain,
    ( u1_struct_0(sK4) = sK5
    | r2_hidden(k3_yellow_0(sK4),sK5) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_405])).

cnf(c_1136,plain,
    ( m1_subset_1(sK5,k1_zfmisc_1(u1_struct_0(sK4))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_20])).

cnf(c_15,plain,
    ( ~ r1_orders_2(X0,X1,X2)
    | ~ v13_waybel_0(X3,X0)
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | ~ m1_subset_1(X1,u1_struct_0(X0))
    | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))
    | ~ r2_hidden(X1,X3)
    | r2_hidden(X2,X3)
    | ~ l1_orders_2(X0) ),
    inference(cnf_transformation,[],[f57])).

cnf(c_9,plain,
    ( r1_orders_2(X0,k3_yellow_0(X0),X1)
    | ~ m1_subset_1(X1,u1_struct_0(X0))
    | v2_struct_0(X0)
    | ~ v5_orders_2(X0)
    | ~ v1_yellow_0(X0)
    | ~ l1_orders_2(X0) ),
    inference(cnf_transformation,[],[f56])).

cnf(c_24,negated_conjecture,
    ( v1_yellow_0(sK4) ),
    inference(cnf_transformation,[],[f67])).

cnf(c_357,plain,
    ( r1_orders_2(X0,k3_yellow_0(X0),X1)
    | ~ m1_subset_1(X1,u1_struct_0(X0))
    | v2_struct_0(X0)
    | ~ v5_orders_2(X0)
    | ~ l1_orders_2(X0)
    | sK4 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_9,c_24])).

cnf(c_358,plain,
    ( r1_orders_2(sK4,k3_yellow_0(sK4),X0)
    | ~ m1_subset_1(X0,u1_struct_0(sK4))
    | v2_struct_0(sK4)
    | ~ v5_orders_2(sK4)
    | ~ l1_orders_2(sK4) ),
    inference(unflattening,[status(thm)],[c_357])).

cnf(c_26,negated_conjecture,
    ( ~ v2_struct_0(sK4) ),
    inference(cnf_transformation,[],[f65])).

cnf(c_25,negated_conjecture,
    ( v5_orders_2(sK4) ),
    inference(cnf_transformation,[],[f66])).

cnf(c_23,negated_conjecture,
    ( l1_orders_2(sK4) ),
    inference(cnf_transformation,[],[f68])).

cnf(c_362,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(sK4))
    | r1_orders_2(sK4,k3_yellow_0(sK4),X0) ),
    inference(global_propositional_subsumption,[status(thm)],[c_358,c_26,c_25,c_23])).

cnf(c_363,plain,
    ( r1_orders_2(sK4,k3_yellow_0(sK4),X0)
    | ~ m1_subset_1(X0,u1_struct_0(sK4)) ),
    inference(renaming,[status(thm)],[c_362])).

cnf(c_470,plain,
    ( ~ v13_waybel_0(X0,X1)
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ m1_subset_1(X3,u1_struct_0(X1))
    | ~ m1_subset_1(X4,u1_struct_0(sK4))
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ r2_hidden(X2,X0)
    | r2_hidden(X3,X0)
    | ~ l1_orders_2(X1)
    | X4 != X3
    | k3_yellow_0(sK4) != X2
    | sK4 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_15,c_363])).

cnf(c_471,plain,
    ( ~ v13_waybel_0(X0,sK4)
    | ~ m1_subset_1(X1,u1_struct_0(sK4))
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK4)))
    | ~ m1_subset_1(k3_yellow_0(sK4),u1_struct_0(sK4))
    | r2_hidden(X1,X0)
    | ~ r2_hidden(k3_yellow_0(sK4),X0)
    | ~ l1_orders_2(sK4) ),
    inference(unflattening,[status(thm)],[c_470])).

cnf(c_8,plain,
    ( m1_subset_1(k3_yellow_0(X0),u1_struct_0(X0))
    | ~ l1_orders_2(X0) ),
    inference(cnf_transformation,[],[f55])).

cnf(c_62,plain,
    ( m1_subset_1(k3_yellow_0(sK4),u1_struct_0(sK4))
    | ~ l1_orders_2(sK4) ),
    inference(instantiation,[status(thm)],[c_8])).

cnf(c_475,plain,
    ( ~ r2_hidden(k3_yellow_0(sK4),X0)
    | r2_hidden(X1,X0)
    | ~ v13_waybel_0(X0,sK4)
    | ~ m1_subset_1(X1,u1_struct_0(sK4))
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK4))) ),
    inference(global_propositional_subsumption,[status(thm)],[c_471,c_23,c_62])).

cnf(c_476,plain,
    ( ~ v13_waybel_0(X0,sK4)
    | ~ m1_subset_1(X1,u1_struct_0(sK4))
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK4)))
    | r2_hidden(X1,X0)
    | ~ r2_hidden(k3_yellow_0(sK4),X0) ),
    inference(renaming,[status(thm)],[c_475])).

cnf(c_1130,plain,
    ( v13_waybel_0(X0,sK4) != iProver_top
    | m1_subset_1(X1,u1_struct_0(sK4)) != iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK4))) != iProver_top
    | r2_hidden(X1,X0) = iProver_top
    | r2_hidden(k3_yellow_0(sK4),X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_476])).

cnf(c_1721,plain,
    ( v13_waybel_0(sK5,sK4) != iProver_top
    | m1_subset_1(X0,u1_struct_0(sK4)) != iProver_top
    | r2_hidden(X0,sK5) = iProver_top
    | r2_hidden(k3_yellow_0(sK4),sK5) != iProver_top ),
    inference(superposition,[status(thm)],[c_1136,c_1130])).

cnf(c_21,negated_conjecture,
    ( v13_waybel_0(sK5,sK4) ),
    inference(cnf_transformation,[],[f70])).

cnf(c_32,plain,
    ( v13_waybel_0(sK5,sK4) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_21])).

cnf(c_1726,plain,
    ( m1_subset_1(X0,u1_struct_0(sK4)) != iProver_top
    | r2_hidden(X0,sK5) = iProver_top
    | r2_hidden(k3_yellow_0(sK4),sK5) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_1721,c_32])).

cnf(c_1868,plain,
    ( u1_struct_0(sK4) = sK5
    | m1_subset_1(X0,u1_struct_0(sK4)) != iProver_top
    | r2_hidden(X0,sK5) = iProver_top ),
    inference(superposition,[status(thm)],[c_1132,c_1726])).

cnf(c_3371,plain,
    ( u1_struct_0(sK4) = X0
    | u1_struct_0(sK4) = sK5
    | r2_hidden(sK0(X0,u1_struct_0(sK4)),X0) = iProver_top
    | r2_hidden(sK0(X0,u1_struct_0(sK4)),sK5) = iProver_top ),
    inference(superposition,[status(thm)],[c_1643,c_1868])).

cnf(c_6640,plain,
    ( u1_struct_0(sK4) = X0
    | u1_struct_0(sK4) = sK5
    | m1_subset_1(sK0(X0,u1_struct_0(sK4)),sK5) = iProver_top
    | r2_hidden(sK0(X0,u1_struct_0(sK4)),X0) = iProver_top ),
    inference(superposition,[status(thm)],[c_3371,c_1139])).

cnf(c_7476,plain,
    ( u1_struct_0(sK4) = X0
    | u1_struct_0(sK4) = sK5
    | m1_subset_1(sK0(X0,u1_struct_0(sK4)),X0) = iProver_top
    | m1_subset_1(sK0(X0,u1_struct_0(sK4)),sK5) = iProver_top ),
    inference(superposition,[status(thm)],[c_6640,c_1139])).

cnf(c_11,plain,
    ( r1_orders_2(X0,sK2(X0,X1),sK3(X0,X1))
    | v13_waybel_0(X1,X0)
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
    | ~ l1_orders_2(X0) ),
    inference(cnf_transformation,[],[f61])).

cnf(c_440,plain,
    ( ~ v13_waybel_0(X0,X1)
    | v13_waybel_0(X2,X3)
    | ~ m1_subset_1(X4,u1_struct_0(X1))
    | ~ m1_subset_1(X5,u1_struct_0(X1))
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X3)))
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ r2_hidden(X5,X0)
    | r2_hidden(X4,X0)
    | ~ l1_orders_2(X3)
    | ~ l1_orders_2(X1)
    | X1 != X3
    | sK2(X3,X2) != X5
    | sK3(X3,X2) != X4 ),
    inference(resolution_lifted,[status(thm)],[c_11,c_15])).

cnf(c_441,plain,
    ( ~ v13_waybel_0(X0,X1)
    | v13_waybel_0(X2,X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ m1_subset_1(sK2(X1,X2),u1_struct_0(X1))
    | ~ m1_subset_1(sK3(X1,X2),u1_struct_0(X1))
    | ~ r2_hidden(sK2(X1,X2),X0)
    | r2_hidden(sK3(X1,X2),X0)
    | ~ l1_orders_2(X1) ),
    inference(unflattening,[status(thm)],[c_440])).

cnf(c_13,plain,
    ( v13_waybel_0(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | m1_subset_1(sK3(X1,X0),u1_struct_0(X1))
    | ~ l1_orders_2(X1) ),
    inference(cnf_transformation,[],[f59])).

cnf(c_7,plain,
    ( m1_subset_1(X0,X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(X1))
    | ~ r2_hidden(X0,X2) ),
    inference(cnf_transformation,[],[f54])).

cnf(c_461,plain,
    ( ~ v13_waybel_0(X0,X1)
    | v13_waybel_0(X2,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ r2_hidden(sK2(X1,X2),X0)
    | r2_hidden(sK3(X1,X2),X0)
    | ~ l1_orders_2(X1) ),
    inference(forward_subsumption_resolution,[status(thm)],[c_441,c_13,c_7])).

cnf(c_518,plain,
    ( ~ v13_waybel_0(X0,X1)
    | v13_waybel_0(X2,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ r2_hidden(sK2(X1,X2),X0)
    | r2_hidden(sK3(X1,X2),X0)
    | sK4 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_461,c_23])).

cnf(c_519,plain,
    ( ~ v13_waybel_0(X0,sK4)
    | v13_waybel_0(X1,sK4)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK4)))
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK4)))
    | ~ r2_hidden(sK2(sK4,X1),X0)
    | r2_hidden(sK3(sK4,X1),X0) ),
    inference(unflattening,[status(thm)],[c_518])).

cnf(c_1128,plain,
    ( v13_waybel_0(X0,sK4) != iProver_top
    | v13_waybel_0(X1,sK4) = iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK4))) != iProver_top
    | m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK4))) != iProver_top
    | r2_hidden(sK2(sK4,X1),X0) != iProver_top
    | r2_hidden(sK3(sK4,X1),X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_519])).

cnf(c_7907,plain,
    ( u1_struct_0(sK4) = sK5
    | k1_zfmisc_1(u1_struct_0(sK4)) = u1_struct_0(sK4)
    | v13_waybel_0(X0,sK4) = iProver_top
    | v13_waybel_0(sK0(k1_zfmisc_1(u1_struct_0(sK4)),u1_struct_0(sK4)),sK4) != iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK4))) != iProver_top
    | m1_subset_1(sK0(k1_zfmisc_1(u1_struct_0(sK4)),u1_struct_0(sK4)),sK5) = iProver_top
    | r2_hidden(sK2(sK4,X0),sK0(k1_zfmisc_1(u1_struct_0(sK4)),u1_struct_0(sK4))) != iProver_top
    | r2_hidden(sK3(sK4,X0),sK0(k1_zfmisc_1(u1_struct_0(sK4)),u1_struct_0(sK4))) = iProver_top ),
    inference(superposition,[status(thm)],[c_7476,c_1128])).

cnf(c_22,negated_conjecture,
    ( ~ v1_xboole_0(sK5) ),
    inference(cnf_transformation,[],[f69])).

cnf(c_31,plain,
    ( v1_xboole_0(sK5) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_22])).

cnf(c_33,plain,
    ( m1_subset_1(sK5,k1_zfmisc_1(u1_struct_0(sK4))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_20])).

cnf(c_4,plain,
    ( m1_subset_1(sK1(X0),k1_zfmisc_1(X0)) ),
    inference(cnf_transformation,[],[f50])).

cnf(c_1313,plain,
    ( m1_subset_1(sK1(u1_struct_0(sK4)),k1_zfmisc_1(u1_struct_0(sK4))) ),
    inference(instantiation,[status(thm)],[c_4])).

cnf(c_1318,plain,
    ( m1_subset_1(sK1(u1_struct_0(sK4)),k1_zfmisc_1(u1_struct_0(sK4))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1313])).

cnf(c_762,plain,
    ( X0 = X0 ),
    theory(equality)).

cnf(c_1515,plain,
    ( k1_zfmisc_1(u1_struct_0(sK4)) = k1_zfmisc_1(u1_struct_0(sK4)) ),
    inference(instantiation,[status(thm)],[c_762])).

cnf(c_511,plain,
    ( m1_subset_1(k3_yellow_0(X0),u1_struct_0(X0))
    | sK4 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_8,c_23])).

cnf(c_512,plain,
    ( m1_subset_1(k3_yellow_0(sK4),u1_struct_0(sK4)) ),
    inference(unflattening,[status(thm)],[c_511])).

cnf(c_1129,plain,
    ( m1_subset_1(k3_yellow_0(sK4),u1_struct_0(sK4)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_512])).

cnf(c_6,plain,
    ( ~ m1_subset_1(X0,X1)
    | r2_hidden(X0,X1)
    | v1_xboole_0(X1) ),
    inference(cnf_transformation,[],[f53])).

cnf(c_1138,plain,
    ( m1_subset_1(X0,X1) != iProver_top
    | r2_hidden(X0,X1) = iProver_top
    | v1_xboole_0(X1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_6])).

cnf(c_1596,plain,
    ( r2_hidden(k3_yellow_0(sK4),u1_struct_0(sK4)) = iProver_top
    | v1_xboole_0(u1_struct_0(sK4)) = iProver_top ),
    inference(superposition,[status(thm)],[c_1129,c_1138])).

cnf(c_2,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | ~ v1_xboole_0(X1)
    | v1_xboole_0(X0) ),
    inference(cnf_transformation,[],[f49])).

cnf(c_1141,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(X1)) != iProver_top
    | v1_xboole_0(X1) != iProver_top
    | v1_xboole_0(X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2])).

cnf(c_1635,plain,
    ( v1_xboole_0(u1_struct_0(sK4)) != iProver_top
    | v1_xboole_0(sK5) = iProver_top ),
    inference(superposition,[status(thm)],[c_1136,c_1141])).

cnf(c_0,plain,
    ( ~ r2_hidden(sK0(X0,X1),X1)
    | ~ r2_hidden(sK0(X0,X1),X0)
    | X1 = X0 ),
    inference(cnf_transformation,[],[f48])).

cnf(c_1431,plain,
    ( ~ r2_hidden(sK0(sK5,X0),X0)
    | ~ r2_hidden(sK0(sK5,X0),sK5)
    | X0 = sK5 ),
    inference(instantiation,[status(thm)],[c_0])).

cnf(c_2162,plain,
    ( ~ r2_hidden(sK0(sK5,u1_struct_0(sK4)),u1_struct_0(sK4))
    | ~ r2_hidden(sK0(sK5,u1_struct_0(sK4)),sK5)
    | u1_struct_0(sK4) = sK5 ),
    inference(instantiation,[status(thm)],[c_1431])).

cnf(c_2166,plain,
    ( u1_struct_0(sK4) = sK5
    | r2_hidden(sK0(sK5,u1_struct_0(sK4)),u1_struct_0(sK4)) != iProver_top
    | r2_hidden(sK0(sK5,u1_struct_0(sK4)),sK5) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2162])).

cnf(c_3,plain,
    ( ~ v1_subset_1(sK1(X0),X0) ),
    inference(cnf_transformation,[],[f51])).

cnf(c_379,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | X1 != X2
    | X1 = X0
    | sK1(X2) != X0 ),
    inference(resolution_lifted,[status(thm)],[c_3,c_16])).

cnf(c_380,plain,
    ( ~ m1_subset_1(sK1(X0),k1_zfmisc_1(X0))
    | X0 = sK1(X0) ),
    inference(unflattening,[status(thm)],[c_379])).

cnf(c_384,plain,
    ( X0 = sK1(X0) ),
    inference(global_propositional_subsumption,[status(thm)],[c_380,c_4])).

cnf(c_2593,plain,
    ( u1_struct_0(sK4) = sK1(u1_struct_0(sK4)) ),
    inference(instantiation,[status(thm)],[c_384])).

cnf(c_1140,plain,
    ( m1_subset_1(sK1(X0),k1_zfmisc_1(X0)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_4])).

cnf(c_1154,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(X0)) = iProver_top ),
    inference(light_normalisation,[status(thm)],[c_1140,c_384])).

cnf(c_12,plain,
    ( v13_waybel_0(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | r2_hidden(sK2(X1,X0),X0)
    | ~ l1_orders_2(X1) ),
    inference(cnf_transformation,[],[f60])).

cnf(c_570,plain,
    ( v13_waybel_0(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | r2_hidden(sK2(X1,X0),X0)
    | sK4 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_12,c_23])).

cnf(c_571,plain,
    ( v13_waybel_0(X0,sK4)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK4)))
    | r2_hidden(sK2(sK4,X0),X0) ),
    inference(unflattening,[status(thm)],[c_570])).

cnf(c_1125,plain,
    ( v13_waybel_0(X0,sK4) = iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK4))) != iProver_top
    | r2_hidden(sK2(sK4,X0),X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_571])).

cnf(c_2075,plain,
    ( v13_waybel_0(u1_struct_0(sK4),sK4) = iProver_top
    | r2_hidden(sK2(sK4,u1_struct_0(sK4)),u1_struct_0(sK4)) = iProver_top ),
    inference(superposition,[status(thm)],[c_1154,c_1125])).

cnf(c_2261,plain,
    ( v13_waybel_0(u1_struct_0(sK4),sK4) = iProver_top
    | m1_subset_1(sK2(sK4,u1_struct_0(sK4)),u1_struct_0(sK4)) = iProver_top ),
    inference(superposition,[status(thm)],[c_2075,c_1139])).

cnf(c_555,plain,
    ( v13_waybel_0(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | m1_subset_1(sK3(X1,X0),u1_struct_0(X1))
    | sK4 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_13,c_23])).

cnf(c_556,plain,
    ( v13_waybel_0(X0,sK4)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK4)))
    | m1_subset_1(sK3(sK4,X0),u1_struct_0(sK4)) ),
    inference(unflattening,[status(thm)],[c_555])).

cnf(c_1126,plain,
    ( v13_waybel_0(X0,sK4) = iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK4))) != iProver_top
    | m1_subset_1(sK3(sK4,X0),u1_struct_0(sK4)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_556])).

cnf(c_1598,plain,
    ( v13_waybel_0(X0,sK4) = iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK4))) != iProver_top
    | r2_hidden(sK3(sK4,X0),u1_struct_0(sK4)) = iProver_top
    | v1_xboole_0(u1_struct_0(sK4)) = iProver_top ),
    inference(superposition,[status(thm)],[c_1126,c_1138])).

cnf(c_1854,plain,
    ( r2_hidden(sK3(sK4,X0),u1_struct_0(sK4)) = iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK4))) != iProver_top
    | v13_waybel_0(X0,sK4) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_1598,c_31,c_1635])).

cnf(c_1855,plain,
    ( v13_waybel_0(X0,sK4) = iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK4))) != iProver_top
    | r2_hidden(sK3(sK4,X0),u1_struct_0(sK4)) = iProver_top ),
    inference(renaming,[status(thm)],[c_1854])).

cnf(c_10,plain,
    ( v13_waybel_0(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ r2_hidden(sK3(X1,X0),X0)
    | ~ l1_orders_2(X1) ),
    inference(cnf_transformation,[],[f62])).

cnf(c_585,plain,
    ( v13_waybel_0(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ r2_hidden(sK3(X1,X0),X0)
    | sK4 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_10,c_23])).

cnf(c_586,plain,
    ( v13_waybel_0(X0,sK4)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK4)))
    | ~ r2_hidden(sK3(sK4,X0),X0) ),
    inference(unflattening,[status(thm)],[c_585])).

cnf(c_1124,plain,
    ( v13_waybel_0(X0,sK4) = iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK4))) != iProver_top
    | r2_hidden(sK3(sK4,X0),X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_586])).

cnf(c_2076,plain,
    ( v13_waybel_0(u1_struct_0(sK4),sK4) = iProver_top
    | r2_hidden(sK3(sK4,u1_struct_0(sK4)),u1_struct_0(sK4)) != iProver_top ),
    inference(superposition,[status(thm)],[c_1154,c_1124])).

cnf(c_2182,plain,
    ( v13_waybel_0(u1_struct_0(sK4),sK4) = iProver_top
    | m1_subset_1(u1_struct_0(sK4),k1_zfmisc_1(u1_struct_0(sK4))) != iProver_top ),
    inference(superposition,[status(thm)],[c_1855,c_2076])).

cnf(c_1534,plain,
    ( v13_waybel_0(X0,sK4) = iProver_top
    | v13_waybel_0(sK5,sK4) != iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK4))) != iProver_top
    | r2_hidden(sK2(sK4,X0),sK5) != iProver_top
    | r2_hidden(sK3(sK4,X0),sK5) = iProver_top ),
    inference(superposition,[status(thm)],[c_1136,c_1128])).

cnf(c_1678,plain,
    ( v13_waybel_0(X0,sK4) = iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK4))) != iProver_top
    | r2_hidden(sK2(sK4,X0),sK5) != iProver_top
    | r2_hidden(sK3(sK4,X0),sK5) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_1534,c_32])).

cnf(c_2073,plain,
    ( v13_waybel_0(u1_struct_0(sK4),sK4) = iProver_top
    | r2_hidden(sK2(sK4,u1_struct_0(sK4)),sK5) != iProver_top
    | r2_hidden(sK3(sK4,u1_struct_0(sK4)),sK5) = iProver_top ),
    inference(superposition,[status(thm)],[c_1154,c_1678])).

cnf(c_1137,plain,
    ( m1_subset_1(X0,X1) = iProver_top
    | m1_subset_1(X2,k1_zfmisc_1(X1)) != iProver_top
    | r2_hidden(X0,X2) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_7])).

cnf(c_1999,plain,
    ( m1_subset_1(X0,u1_struct_0(sK4)) = iProver_top
    | r2_hidden(X0,sK5) != iProver_top ),
    inference(superposition,[status(thm)],[c_1136,c_1137])).

cnf(c_2175,plain,
    ( r2_hidden(X0,u1_struct_0(sK4)) = iProver_top
    | r2_hidden(X0,sK5) != iProver_top
    | v1_xboole_0(u1_struct_0(sK4)) = iProver_top ),
    inference(superposition,[status(thm)],[c_1999,c_1138])).

cnf(c_2341,plain,
    ( r2_hidden(X0,sK5) != iProver_top
    | r2_hidden(X0,u1_struct_0(sK4)) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_2175,c_31,c_1635])).

cnf(c_2342,plain,
    ( r2_hidden(X0,u1_struct_0(sK4)) = iProver_top
    | r2_hidden(X0,sK5) != iProver_top ),
    inference(renaming,[status(thm)],[c_2341])).

cnf(c_2351,plain,
    ( v13_waybel_0(u1_struct_0(sK4),sK4) = iProver_top
    | r2_hidden(sK3(sK4,u1_struct_0(sK4)),sK5) != iProver_top ),
    inference(superposition,[status(thm)],[c_2342,c_2076])).

cnf(c_2367,plain,
    ( r2_hidden(sK2(sK4,u1_struct_0(sK4)),sK5) != iProver_top
    | v13_waybel_0(u1_struct_0(sK4),sK4) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_2073,c_2351])).

cnf(c_2368,plain,
    ( v13_waybel_0(u1_struct_0(sK4),sK4) = iProver_top
    | r2_hidden(sK2(sK4,u1_struct_0(sK4)),sK5) != iProver_top ),
    inference(renaming,[status(thm)],[c_2367])).

cnf(c_767,plain,
    ( ~ m1_subset_1(X0,X1)
    | m1_subset_1(X2,X3)
    | X2 != X0
    | X3 != X1 ),
    theory(equality)).

cnf(c_1373,plain,
    ( m1_subset_1(X0,X1)
    | ~ m1_subset_1(sK5,k1_zfmisc_1(u1_struct_0(sK4)))
    | X1 != k1_zfmisc_1(u1_struct_0(sK4))
    | X0 != sK5 ),
    inference(instantiation,[status(thm)],[c_767])).

cnf(c_1514,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK4)))
    | ~ m1_subset_1(sK5,k1_zfmisc_1(u1_struct_0(sK4)))
    | X0 != sK5
    | k1_zfmisc_1(u1_struct_0(sK4)) != k1_zfmisc_1(u1_struct_0(sK4)) ),
    inference(instantiation,[status(thm)],[c_1373])).

cnf(c_2418,plain,
    ( m1_subset_1(u1_struct_0(sK4),k1_zfmisc_1(u1_struct_0(sK4)))
    | ~ m1_subset_1(sK5,k1_zfmisc_1(u1_struct_0(sK4)))
    | u1_struct_0(sK4) != sK5
    | k1_zfmisc_1(u1_struct_0(sK4)) != k1_zfmisc_1(u1_struct_0(sK4)) ),
    inference(instantiation,[status(thm)],[c_1514])).

cnf(c_2419,plain,
    ( u1_struct_0(sK4) != sK5
    | k1_zfmisc_1(u1_struct_0(sK4)) != k1_zfmisc_1(u1_struct_0(sK4))
    | m1_subset_1(u1_struct_0(sK4),k1_zfmisc_1(u1_struct_0(sK4))) = iProver_top
    | m1_subset_1(sK5,k1_zfmisc_1(u1_struct_0(sK4))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2418])).

cnf(c_14,plain,
    ( v13_waybel_0(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | m1_subset_1(sK2(X1,X0),u1_struct_0(X1))
    | ~ l1_orders_2(X1) ),
    inference(cnf_transformation,[],[f58])).

cnf(c_540,plain,
    ( v13_waybel_0(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | m1_subset_1(sK2(X1,X0),u1_struct_0(X1))
    | sK4 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_14,c_23])).

cnf(c_541,plain,
    ( v13_waybel_0(X0,sK4)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK4)))
    | m1_subset_1(sK2(sK4,X0),u1_struct_0(sK4)) ),
    inference(unflattening,[status(thm)],[c_540])).

cnf(c_1127,plain,
    ( v13_waybel_0(X0,sK4) = iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK4))) != iProver_top
    | m1_subset_1(sK2(sK4,X0),u1_struct_0(sK4)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_541])).

cnf(c_2269,plain,
    ( u1_struct_0(sK4) = sK5
    | v13_waybel_0(X0,sK4) = iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK4))) != iProver_top
    | r2_hidden(sK2(sK4,X0),sK5) = iProver_top ),
    inference(superposition,[status(thm)],[c_1127,c_1868])).

cnf(c_2550,plain,
    ( u1_struct_0(sK4) = sK5
    | v13_waybel_0(u1_struct_0(sK4),sK4) = iProver_top
    | r2_hidden(sK2(sK4,u1_struct_0(sK4)),sK5) = iProver_top ),
    inference(superposition,[status(thm)],[c_1154,c_2269])).

cnf(c_3110,plain,
    ( v13_waybel_0(u1_struct_0(sK4),sK4) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_2261,c_33,c_1515,c_2182,c_2368,c_2419,c_2550])).

cnf(c_1368,plain,
    ( m1_subset_1(X0,X1)
    | ~ m1_subset_1(sK1(X2),k1_zfmisc_1(X2))
    | X0 != sK1(X2)
    | X1 != k1_zfmisc_1(X2) ),
    inference(instantiation,[status(thm)],[c_767])).

cnf(c_1699,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(X1))
    | ~ m1_subset_1(sK1(X1),k1_zfmisc_1(X1))
    | X0 != sK1(X1)
    | k1_zfmisc_1(X1) != k1_zfmisc_1(X1) ),
    inference(instantiation,[status(thm)],[c_1368])).

cnf(c_1985,plain,
    ( m1_subset_1(u1_struct_0(sK4),k1_zfmisc_1(X0))
    | ~ m1_subset_1(sK1(X0),k1_zfmisc_1(X0))
    | u1_struct_0(sK4) != sK1(X0)
    | k1_zfmisc_1(X0) != k1_zfmisc_1(X0) ),
    inference(instantiation,[status(thm)],[c_1699])).

cnf(c_4521,plain,
    ( m1_subset_1(u1_struct_0(sK4),k1_zfmisc_1(u1_struct_0(sK4)))
    | ~ m1_subset_1(sK1(u1_struct_0(sK4)),k1_zfmisc_1(u1_struct_0(sK4)))
    | u1_struct_0(sK4) != sK1(u1_struct_0(sK4))
    | k1_zfmisc_1(u1_struct_0(sK4)) != k1_zfmisc_1(u1_struct_0(sK4)) ),
    inference(instantiation,[status(thm)],[c_1985])).

cnf(c_4522,plain,
    ( u1_struct_0(sK4) != sK1(u1_struct_0(sK4))
    | k1_zfmisc_1(u1_struct_0(sK4)) != k1_zfmisc_1(u1_struct_0(sK4))
    | m1_subset_1(u1_struct_0(sK4),k1_zfmisc_1(u1_struct_0(sK4))) = iProver_top
    | m1_subset_1(sK1(u1_struct_0(sK4)),k1_zfmisc_1(u1_struct_0(sK4))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_4521])).

cnf(c_1422,plain,
    ( m1_subset_1(X0,X1)
    | ~ m1_subset_1(sK5,k1_zfmisc_1(X1))
    | ~ r2_hidden(X0,sK5) ),
    inference(instantiation,[status(thm)],[c_7])).

cnf(c_5353,plain,
    ( m1_subset_1(sK0(sK5,u1_struct_0(sK4)),u1_struct_0(sK4))
    | ~ m1_subset_1(sK5,k1_zfmisc_1(u1_struct_0(sK4)))
    | ~ r2_hidden(sK0(sK5,u1_struct_0(sK4)),sK5) ),
    inference(instantiation,[status(thm)],[c_1422])).

cnf(c_5359,plain,
    ( m1_subset_1(sK0(sK5,u1_struct_0(sK4)),u1_struct_0(sK4)) = iProver_top
    | m1_subset_1(sK5,k1_zfmisc_1(u1_struct_0(sK4))) != iProver_top
    | r2_hidden(sK0(sK5,u1_struct_0(sK4)),sK5) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_5353])).

cnf(c_6649,plain,
    ( u1_struct_0(sK4) = sK5
    | r2_hidden(sK0(sK5,u1_struct_0(sK4)),sK5) = iProver_top
    | iProver_top != iProver_top ),
    inference(equality_factoring,[status(thm)],[c_3371])).

cnf(c_6651,plain,
    ( u1_struct_0(sK4) = sK5
    | r2_hidden(sK0(sK5,u1_struct_0(sK4)),sK5) = iProver_top ),
    inference(equality_resolution_simp,[status(thm)],[c_6649])).

cnf(c_4801,plain,
    ( ~ v13_waybel_0(u1_struct_0(sK4),sK4)
    | ~ m1_subset_1(sK0(X0,u1_struct_0(sK4)),u1_struct_0(sK4))
    | ~ m1_subset_1(u1_struct_0(sK4),k1_zfmisc_1(u1_struct_0(sK4)))
    | r2_hidden(sK0(X0,u1_struct_0(sK4)),u1_struct_0(sK4))
    | ~ r2_hidden(k3_yellow_0(sK4),u1_struct_0(sK4)) ),
    inference(instantiation,[status(thm)],[c_476])).

cnf(c_8540,plain,
    ( ~ v13_waybel_0(u1_struct_0(sK4),sK4)
    | ~ m1_subset_1(sK0(sK5,u1_struct_0(sK4)),u1_struct_0(sK4))
    | ~ m1_subset_1(u1_struct_0(sK4),k1_zfmisc_1(u1_struct_0(sK4)))
    | r2_hidden(sK0(sK5,u1_struct_0(sK4)),u1_struct_0(sK4))
    | ~ r2_hidden(k3_yellow_0(sK4),u1_struct_0(sK4)) ),
    inference(instantiation,[status(thm)],[c_4801])).

cnf(c_8541,plain,
    ( v13_waybel_0(u1_struct_0(sK4),sK4) != iProver_top
    | m1_subset_1(sK0(sK5,u1_struct_0(sK4)),u1_struct_0(sK4)) != iProver_top
    | m1_subset_1(u1_struct_0(sK4),k1_zfmisc_1(u1_struct_0(sK4))) != iProver_top
    | r2_hidden(sK0(sK5,u1_struct_0(sK4)),u1_struct_0(sK4)) = iProver_top
    | r2_hidden(k3_yellow_0(sK4),u1_struct_0(sK4)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_8540])).

cnf(c_8544,plain,
    ( u1_struct_0(sK4) = sK5 ),
    inference(global_propositional_subsumption,[status(thm)],[c_7907,c_31,c_33,c_1318,c_1515,c_1596,c_1635,c_2166,c_2182,c_2368,c_2419,c_2550,c_2593,c_4522,c_5359,c_6651,c_8541])).

cnf(c_19,negated_conjecture,
    ( v1_subset_1(sK5,u1_struct_0(sK4))
    | ~ r2_hidden(k3_yellow_0(sK4),sK5) ),
    inference(cnf_transformation,[],[f72])).

cnf(c_199,plain,
    ( v1_subset_1(sK5,u1_struct_0(sK4))
    | ~ r2_hidden(k3_yellow_0(sK4),sK5) ),
    inference(prop_impl,[status(thm)],[c_19])).

cnf(c_390,plain,
    ( ~ r2_hidden(k3_yellow_0(sK4),sK5)
    | u1_struct_0(sK4) != X0
    | sK1(X0) != sK5 ),
    inference(resolution_lifted,[status(thm)],[c_3,c_199])).

cnf(c_391,plain,
    ( ~ r2_hidden(k3_yellow_0(sK4),sK5)
    | sK1(u1_struct_0(sK4)) != sK5 ),
    inference(unflattening,[status(thm)],[c_390])).

cnf(c_1133,plain,
    ( sK1(u1_struct_0(sK4)) != sK5
    | r2_hidden(k3_yellow_0(sK4),sK5) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_391])).

cnf(c_1165,plain,
    ( u1_struct_0(sK4) != sK5
    | r2_hidden(k3_yellow_0(sK4),sK5) != iProver_top ),
    inference(demodulation,[status(thm)],[c_1133,c_384])).

cnf(c_8581,plain,
    ( sK5 != sK5
    | r2_hidden(k3_yellow_0(sK4),sK5) != iProver_top ),
    inference(demodulation,[status(thm)],[c_8544,c_1165])).

cnf(c_8686,plain,
    ( r2_hidden(k3_yellow_0(sK4),sK5) != iProver_top ),
    inference(equality_resolution_simp,[status(thm)],[c_8581])).

cnf(c_1764,plain,
    ( r2_hidden(k3_yellow_0(sK4),u1_struct_0(sK4)) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_1596,c_31,c_1635])).

cnf(c_8586,plain,
    ( r2_hidden(k3_yellow_0(sK4),sK5) = iProver_top ),
    inference(demodulation,[status(thm)],[c_8544,c_1764])).

cnf(c_8688,plain,
    ( $false ),
    inference(forward_subsumption_resolution,[status(thm)],[c_8686,c_8586])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : iproveropt_run.sh %d %s
% 0.12/0.34  % Computer   : n014.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % WCLimit    : 600
% 0.12/0.34  % DateTime   : Tue Dec  1 13:37:07 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.34  % Running in FOF mode
% 3.19/0.99  % SZS status Started for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.19/0.99  
% 3.19/0.99  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 3.19/0.99  
% 3.19/0.99  ------  iProver source info
% 3.19/0.99  
% 3.19/0.99  git: date: 2020-06-30 10:37:57 +0100
% 3.19/0.99  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 3.19/0.99  git: non_committed_changes: false
% 3.19/0.99  git: last_make_outside_of_git: false
% 3.19/0.99  
% 3.19/0.99  ------ 
% 3.19/0.99  
% 3.19/0.99  ------ Input Options
% 3.19/0.99  
% 3.19/0.99  --out_options                           all
% 3.19/0.99  --tptp_safe_out                         true
% 3.19/0.99  --problem_path                          ""
% 3.19/0.99  --include_path                          ""
% 3.19/0.99  --clausifier                            res/vclausify_rel
% 3.19/0.99  --clausifier_options                    --mode clausify
% 3.19/0.99  --stdin                                 false
% 3.19/0.99  --stats_out                             all
% 3.19/0.99  
% 3.19/0.99  ------ General Options
% 3.19/0.99  
% 3.19/0.99  --fof                                   false
% 3.19/0.99  --time_out_real                         305.
% 3.19/0.99  --time_out_virtual                      -1.
% 3.19/0.99  --symbol_type_check                     false
% 3.19/0.99  --clausify_out                          false
% 3.19/0.99  --sig_cnt_out                           false
% 3.19/0.99  --trig_cnt_out                          false
% 3.19/0.99  --trig_cnt_out_tolerance                1.
% 3.19/0.99  --trig_cnt_out_sk_spl                   false
% 3.19/0.99  --abstr_cl_out                          false
% 3.19/0.99  
% 3.19/0.99  ------ Global Options
% 3.19/0.99  
% 3.19/0.99  --schedule                              default
% 3.19/0.99  --add_important_lit                     false
% 3.19/0.99  --prop_solver_per_cl                    1000
% 3.19/0.99  --min_unsat_core                        false
% 3.19/0.99  --soft_assumptions                      false
% 3.19/0.99  --soft_lemma_size                       3
% 3.19/0.99  --prop_impl_unit_size                   0
% 3.19/0.99  --prop_impl_unit                        []
% 3.19/0.99  --share_sel_clauses                     true
% 3.19/0.99  --reset_solvers                         false
% 3.19/0.99  --bc_imp_inh                            [conj_cone]
% 3.19/0.99  --conj_cone_tolerance                   3.
% 3.19/0.99  --extra_neg_conj                        none
% 3.19/0.99  --large_theory_mode                     true
% 3.19/0.99  --prolific_symb_bound                   200
% 3.19/0.99  --lt_threshold                          2000
% 3.19/0.99  --clause_weak_htbl                      true
% 3.19/0.99  --gc_record_bc_elim                     false
% 3.19/0.99  
% 3.19/0.99  ------ Preprocessing Options
% 3.19/0.99  
% 3.19/0.99  --preprocessing_flag                    true
% 3.19/0.99  --time_out_prep_mult                    0.1
% 3.19/0.99  --splitting_mode                        input
% 3.19/0.99  --splitting_grd                         true
% 3.19/0.99  --splitting_cvd                         false
% 3.19/0.99  --splitting_cvd_svl                     false
% 3.19/0.99  --splitting_nvd                         32
% 3.19/0.99  --sub_typing                            true
% 3.19/0.99  --prep_gs_sim                           true
% 3.19/0.99  --prep_unflatten                        true
% 3.19/0.99  --prep_res_sim                          true
% 3.19/0.99  --prep_upred                            true
% 3.19/0.99  --prep_sem_filter                       exhaustive
% 3.19/0.99  --prep_sem_filter_out                   false
% 3.19/0.99  --pred_elim                             true
% 3.19/0.99  --res_sim_input                         true
% 3.19/0.99  --eq_ax_congr_red                       true
% 3.19/0.99  --pure_diseq_elim                       true
% 3.19/0.99  --brand_transform                       false
% 3.19/0.99  --non_eq_to_eq                          false
% 3.19/0.99  --prep_def_merge                        true
% 3.19/0.99  --prep_def_merge_prop_impl              false
% 3.19/0.99  --prep_def_merge_mbd                    true
% 3.19/0.99  --prep_def_merge_tr_red                 false
% 3.19/0.99  --prep_def_merge_tr_cl                  false
% 3.19/0.99  --smt_preprocessing                     true
% 3.19/0.99  --smt_ac_axioms                         fast
% 3.19/0.99  --preprocessed_out                      false
% 3.19/0.99  --preprocessed_stats                    false
% 3.19/0.99  
% 3.19/0.99  ------ Abstraction refinement Options
% 3.19/0.99  
% 3.19/0.99  --abstr_ref                             []
% 3.19/0.99  --abstr_ref_prep                        false
% 3.19/0.99  --abstr_ref_until_sat                   false
% 3.19/0.99  --abstr_ref_sig_restrict                funpre
% 3.19/0.99  --abstr_ref_af_restrict_to_split_sk     false
% 3.19/0.99  --abstr_ref_under                       []
% 3.19/0.99  
% 3.19/0.99  ------ SAT Options
% 3.19/0.99  
% 3.19/0.99  --sat_mode                              false
% 3.19/0.99  --sat_fm_restart_options                ""
% 3.19/0.99  --sat_gr_def                            false
% 3.19/0.99  --sat_epr_types                         true
% 3.19/0.99  --sat_non_cyclic_types                  false
% 3.19/0.99  --sat_finite_models                     false
% 3.19/0.99  --sat_fm_lemmas                         false
% 3.19/0.99  --sat_fm_prep                           false
% 3.19/0.99  --sat_fm_uc_incr                        true
% 3.19/0.99  --sat_out_model                         small
% 3.19/0.99  --sat_out_clauses                       false
% 3.19/0.99  
% 3.19/0.99  ------ QBF Options
% 3.19/0.99  
% 3.19/0.99  --qbf_mode                              false
% 3.19/0.99  --qbf_elim_univ                         false
% 3.19/0.99  --qbf_dom_inst                          none
% 3.19/0.99  --qbf_dom_pre_inst                      false
% 3.19/0.99  --qbf_sk_in                             false
% 3.19/0.99  --qbf_pred_elim                         true
% 3.19/0.99  --qbf_split                             512
% 3.19/0.99  
% 3.19/0.99  ------ BMC1 Options
% 3.19/0.99  
% 3.19/0.99  --bmc1_incremental                      false
% 3.19/0.99  --bmc1_axioms                           reachable_all
% 3.19/0.99  --bmc1_min_bound                        0
% 3.19/0.99  --bmc1_max_bound                        -1
% 3.19/0.99  --bmc1_max_bound_default                -1
% 3.19/0.99  --bmc1_symbol_reachability              true
% 3.19/0.99  --bmc1_property_lemmas                  false
% 3.19/0.99  --bmc1_k_induction                      false
% 3.19/0.99  --bmc1_non_equiv_states                 false
% 3.19/0.99  --bmc1_deadlock                         false
% 3.19/0.99  --bmc1_ucm                              false
% 3.19/0.99  --bmc1_add_unsat_core                   none
% 3.19/0.99  --bmc1_unsat_core_children              false
% 3.19/0.99  --bmc1_unsat_core_extrapolate_axioms    false
% 3.19/0.99  --bmc1_out_stat                         full
% 3.19/0.99  --bmc1_ground_init                      false
% 3.19/0.99  --bmc1_pre_inst_next_state              false
% 3.19/0.99  --bmc1_pre_inst_state                   false
% 3.19/0.99  --bmc1_pre_inst_reach_state             false
% 3.19/0.99  --bmc1_out_unsat_core                   false
% 3.19/0.99  --bmc1_aig_witness_out                  false
% 3.19/0.99  --bmc1_verbose                          false
% 3.19/0.99  --bmc1_dump_clauses_tptp                false
% 3.19/0.99  --bmc1_dump_unsat_core_tptp             false
% 3.19/0.99  --bmc1_dump_file                        -
% 3.19/0.99  --bmc1_ucm_expand_uc_limit              128
% 3.19/0.99  --bmc1_ucm_n_expand_iterations          6
% 3.19/0.99  --bmc1_ucm_extend_mode                  1
% 3.19/0.99  --bmc1_ucm_init_mode                    2
% 3.19/0.99  --bmc1_ucm_cone_mode                    none
% 3.19/0.99  --bmc1_ucm_reduced_relation_type        0
% 3.19/0.99  --bmc1_ucm_relax_model                  4
% 3.19/0.99  --bmc1_ucm_full_tr_after_sat            true
% 3.19/0.99  --bmc1_ucm_expand_neg_assumptions       false
% 3.19/0.99  --bmc1_ucm_layered_model                none
% 3.19/0.99  --bmc1_ucm_max_lemma_size               10
% 3.19/0.99  
% 3.19/0.99  ------ AIG Options
% 3.19/0.99  
% 3.19/0.99  --aig_mode                              false
% 3.19/0.99  
% 3.19/0.99  ------ Instantiation Options
% 3.19/0.99  
% 3.19/0.99  --instantiation_flag                    true
% 3.19/0.99  --inst_sos_flag                         false
% 3.19/0.99  --inst_sos_phase                        true
% 3.19/0.99  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 3.19/0.99  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 3.19/0.99  --inst_lit_sel_side                     num_symb
% 3.19/0.99  --inst_solver_per_active                1400
% 3.19/0.99  --inst_solver_calls_frac                1.
% 3.19/0.99  --inst_passive_queue_type               priority_queues
% 3.19/0.99  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 3.19/0.99  --inst_passive_queues_freq              [25;2]
% 3.19/0.99  --inst_dismatching                      true
% 3.19/0.99  --inst_eager_unprocessed_to_passive     true
% 3.19/0.99  --inst_prop_sim_given                   true
% 3.19/0.99  --inst_prop_sim_new                     false
% 3.19/0.99  --inst_subs_new                         false
% 3.19/0.99  --inst_eq_res_simp                      false
% 3.19/0.99  --inst_subs_given                       false
% 3.19/0.99  --inst_orphan_elimination               true
% 3.19/0.99  --inst_learning_loop_flag               true
% 3.19/0.99  --inst_learning_start                   3000
% 3.19/0.99  --inst_learning_factor                  2
% 3.19/0.99  --inst_start_prop_sim_after_learn       3
% 3.19/0.99  --inst_sel_renew                        solver
% 3.19/0.99  --inst_lit_activity_flag                true
% 3.19/0.99  --inst_restr_to_given                   false
% 3.19/0.99  --inst_activity_threshold               500
% 3.19/0.99  --inst_out_proof                        true
% 3.19/0.99  
% 3.19/0.99  ------ Resolution Options
% 3.19/0.99  
% 3.19/0.99  --resolution_flag                       true
% 3.19/0.99  --res_lit_sel                           adaptive
% 3.19/0.99  --res_lit_sel_side                      none
% 3.19/0.99  --res_ordering                          kbo
% 3.19/0.99  --res_to_prop_solver                    active
% 3.19/0.99  --res_prop_simpl_new                    false
% 3.19/0.99  --res_prop_simpl_given                  true
% 3.19/0.99  --res_passive_queue_type                priority_queues
% 3.19/0.99  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 3.19/0.99  --res_passive_queues_freq               [15;5]
% 3.19/0.99  --res_forward_subs                      full
% 3.19/0.99  --res_backward_subs                     full
% 3.19/0.99  --res_forward_subs_resolution           true
% 3.19/0.99  --res_backward_subs_resolution          true
% 3.19/0.99  --res_orphan_elimination                true
% 3.19/0.99  --res_time_limit                        2.
% 3.19/0.99  --res_out_proof                         true
% 3.19/0.99  
% 3.19/0.99  ------ Superposition Options
% 3.19/0.99  
% 3.19/0.99  --superposition_flag                    true
% 3.19/0.99  --sup_passive_queue_type                priority_queues
% 3.19/0.99  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 3.19/0.99  --sup_passive_queues_freq               [8;1;4]
% 3.19/0.99  --demod_completeness_check              fast
% 3.19/0.99  --demod_use_ground                      true
% 3.19/0.99  --sup_to_prop_solver                    passive
% 3.19/0.99  --sup_prop_simpl_new                    true
% 3.19/0.99  --sup_prop_simpl_given                  true
% 3.19/0.99  --sup_fun_splitting                     false
% 3.19/0.99  --sup_smt_interval                      50000
% 3.19/0.99  
% 3.19/0.99  ------ Superposition Simplification Setup
% 3.19/0.99  
% 3.19/0.99  --sup_indices_passive                   []
% 3.19/0.99  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.19/0.99  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.19/0.99  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.19/0.99  --sup_full_triv                         [TrivRules;PropSubs]
% 3.19/0.99  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.19/0.99  --sup_full_bw                           [BwDemod]
% 3.19/0.99  --sup_immed_triv                        [TrivRules]
% 3.19/0.99  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 3.19/0.99  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.19/0.99  --sup_immed_bw_main                     []
% 3.19/0.99  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 3.19/0.99  --sup_input_triv                        [Unflattening;TrivRules]
% 3.19/0.99  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.19/0.99  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 3.19/0.99  
% 3.19/0.99  ------ Combination Options
% 3.19/0.99  
% 3.19/0.99  --comb_res_mult                         3
% 3.19/0.99  --comb_sup_mult                         2
% 3.19/0.99  --comb_inst_mult                        10
% 3.19/0.99  
% 3.19/0.99  ------ Debug Options
% 3.19/0.99  
% 3.19/0.99  --dbg_backtrace                         false
% 3.19/0.99  --dbg_dump_prop_clauses                 false
% 3.19/0.99  --dbg_dump_prop_clauses_file            -
% 3.19/0.99  --dbg_out_stat                          false
% 3.19/0.99  ------ Parsing...
% 3.19/0.99  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 3.19/0.99  
% 3.19/0.99  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe:1:0s pe:2:0s pe:4:0s pe_e  sf_s  rm: 7 0s  sf_e  pe_s  pe_e 
% 3.19/0.99  
% 3.19/0.99  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 3.19/0.99  
% 3.19/0.99  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 3.19/0.99  ------ Proving...
% 3.19/0.99  ------ Problem Properties 
% 3.19/0.99  
% 3.19/0.99  
% 3.19/0.99  clauses                                 21
% 3.19/0.99  conjectures                             3
% 3.19/0.99  EPR                                     4
% 3.19/0.99  Horn                                    14
% 3.19/0.99  unary                                   6
% 3.19/0.99  binary                                  3
% 3.19/0.99  lits                                    53
% 3.19/0.99  lits eq                                 6
% 3.19/0.99  fd_pure                                 0
% 3.19/0.99  fd_pseudo                               0
% 3.19/0.99  fd_cond                                 0
% 3.19/0.99  fd_pseudo_cond                          2
% 3.19/0.99  AC symbols                              0
% 3.19/0.99  
% 3.19/0.99  ------ Schedule dynamic 5 is on 
% 3.19/0.99  
% 3.19/0.99  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" Time Limit: 10.
% 3.19/0.99  
% 3.19/0.99  
% 3.19/0.99  ------ 
% 3.19/0.99  Current options:
% 3.19/0.99  ------ 
% 3.19/0.99  
% 3.19/0.99  ------ Input Options
% 3.19/0.99  
% 3.19/0.99  --out_options                           all
% 3.19/0.99  --tptp_safe_out                         true
% 3.19/0.99  --problem_path                          ""
% 3.19/0.99  --include_path                          ""
% 3.19/0.99  --clausifier                            res/vclausify_rel
% 3.19/0.99  --clausifier_options                    --mode clausify
% 3.19/0.99  --stdin                                 false
% 3.19/0.99  --stats_out                             all
% 3.19/0.99  
% 3.19/0.99  ------ General Options
% 3.19/0.99  
% 3.19/0.99  --fof                                   false
% 3.19/0.99  --time_out_real                         305.
% 3.19/0.99  --time_out_virtual                      -1.
% 3.19/0.99  --symbol_type_check                     false
% 3.19/0.99  --clausify_out                          false
% 3.19/0.99  --sig_cnt_out                           false
% 3.19/0.99  --trig_cnt_out                          false
% 3.19/0.99  --trig_cnt_out_tolerance                1.
% 3.19/0.99  --trig_cnt_out_sk_spl                   false
% 3.19/0.99  --abstr_cl_out                          false
% 3.19/0.99  
% 3.19/0.99  ------ Global Options
% 3.19/0.99  
% 3.19/0.99  --schedule                              default
% 3.19/0.99  --add_important_lit                     false
% 3.19/0.99  --prop_solver_per_cl                    1000
% 3.19/0.99  --min_unsat_core                        false
% 3.19/0.99  --soft_assumptions                      false
% 3.19/0.99  --soft_lemma_size                       3
% 3.19/0.99  --prop_impl_unit_size                   0
% 3.19/0.99  --prop_impl_unit                        []
% 3.19/0.99  --share_sel_clauses                     true
% 3.19/0.99  --reset_solvers                         false
% 3.19/0.99  --bc_imp_inh                            [conj_cone]
% 3.19/0.99  --conj_cone_tolerance                   3.
% 3.19/0.99  --extra_neg_conj                        none
% 3.19/0.99  --large_theory_mode                     true
% 3.19/0.99  --prolific_symb_bound                   200
% 3.19/0.99  --lt_threshold                          2000
% 3.19/0.99  --clause_weak_htbl                      true
% 3.19/0.99  --gc_record_bc_elim                     false
% 3.19/0.99  
% 3.19/0.99  ------ Preprocessing Options
% 3.19/0.99  
% 3.19/0.99  --preprocessing_flag                    true
% 3.19/0.99  --time_out_prep_mult                    0.1
% 3.19/0.99  --splitting_mode                        input
% 3.19/0.99  --splitting_grd                         true
% 3.19/0.99  --splitting_cvd                         false
% 3.19/0.99  --splitting_cvd_svl                     false
% 3.19/0.99  --splitting_nvd                         32
% 3.19/0.99  --sub_typing                            true
% 3.19/0.99  --prep_gs_sim                           true
% 3.19/0.99  --prep_unflatten                        true
% 3.19/0.99  --prep_res_sim                          true
% 3.19/0.99  --prep_upred                            true
% 3.19/0.99  --prep_sem_filter                       exhaustive
% 3.19/0.99  --prep_sem_filter_out                   false
% 3.19/0.99  --pred_elim                             true
% 3.19/0.99  --res_sim_input                         true
% 3.19/0.99  --eq_ax_congr_red                       true
% 3.19/0.99  --pure_diseq_elim                       true
% 3.19/0.99  --brand_transform                       false
% 3.19/0.99  --non_eq_to_eq                          false
% 3.19/0.99  --prep_def_merge                        true
% 3.19/0.99  --prep_def_merge_prop_impl              false
% 3.19/0.99  --prep_def_merge_mbd                    true
% 3.19/0.99  --prep_def_merge_tr_red                 false
% 3.19/0.99  --prep_def_merge_tr_cl                  false
% 3.19/0.99  --smt_preprocessing                     true
% 3.19/0.99  --smt_ac_axioms                         fast
% 3.19/0.99  --preprocessed_out                      false
% 3.19/0.99  --preprocessed_stats                    false
% 3.19/0.99  
% 3.19/0.99  ------ Abstraction refinement Options
% 3.19/0.99  
% 3.19/0.99  --abstr_ref                             []
% 3.19/0.99  --abstr_ref_prep                        false
% 3.19/0.99  --abstr_ref_until_sat                   false
% 3.19/0.99  --abstr_ref_sig_restrict                funpre
% 3.19/0.99  --abstr_ref_af_restrict_to_split_sk     false
% 3.19/0.99  --abstr_ref_under                       []
% 3.19/0.99  
% 3.19/0.99  ------ SAT Options
% 3.19/0.99  
% 3.19/0.99  --sat_mode                              false
% 3.19/0.99  --sat_fm_restart_options                ""
% 3.19/0.99  --sat_gr_def                            false
% 3.19/0.99  --sat_epr_types                         true
% 3.19/0.99  --sat_non_cyclic_types                  false
% 3.19/0.99  --sat_finite_models                     false
% 3.19/0.99  --sat_fm_lemmas                         false
% 3.19/0.99  --sat_fm_prep                           false
% 3.19/0.99  --sat_fm_uc_incr                        true
% 3.19/0.99  --sat_out_model                         small
% 3.19/0.99  --sat_out_clauses                       false
% 3.19/0.99  
% 3.19/0.99  ------ QBF Options
% 3.19/0.99  
% 3.19/0.99  --qbf_mode                              false
% 3.19/0.99  --qbf_elim_univ                         false
% 3.19/0.99  --qbf_dom_inst                          none
% 3.19/0.99  --qbf_dom_pre_inst                      false
% 3.19/0.99  --qbf_sk_in                             false
% 3.19/0.99  --qbf_pred_elim                         true
% 3.19/0.99  --qbf_split                             512
% 3.19/0.99  
% 3.19/0.99  ------ BMC1 Options
% 3.19/0.99  
% 3.19/0.99  --bmc1_incremental                      false
% 3.19/0.99  --bmc1_axioms                           reachable_all
% 3.19/0.99  --bmc1_min_bound                        0
% 3.19/0.99  --bmc1_max_bound                        -1
% 3.19/0.99  --bmc1_max_bound_default                -1
% 3.19/0.99  --bmc1_symbol_reachability              true
% 3.19/0.99  --bmc1_property_lemmas                  false
% 3.19/0.99  --bmc1_k_induction                      false
% 3.19/0.99  --bmc1_non_equiv_states                 false
% 3.19/0.99  --bmc1_deadlock                         false
% 3.19/0.99  --bmc1_ucm                              false
% 3.19/0.99  --bmc1_add_unsat_core                   none
% 3.19/0.99  --bmc1_unsat_core_children              false
% 3.19/0.99  --bmc1_unsat_core_extrapolate_axioms    false
% 3.19/0.99  --bmc1_out_stat                         full
% 3.19/0.99  --bmc1_ground_init                      false
% 3.19/0.99  --bmc1_pre_inst_next_state              false
% 3.19/0.99  --bmc1_pre_inst_state                   false
% 3.19/0.99  --bmc1_pre_inst_reach_state             false
% 3.19/0.99  --bmc1_out_unsat_core                   false
% 3.19/0.99  --bmc1_aig_witness_out                  false
% 3.19/0.99  --bmc1_verbose                          false
% 3.19/0.99  --bmc1_dump_clauses_tptp                false
% 3.19/0.99  --bmc1_dump_unsat_core_tptp             false
% 3.19/0.99  --bmc1_dump_file                        -
% 3.19/0.99  --bmc1_ucm_expand_uc_limit              128
% 3.19/0.99  --bmc1_ucm_n_expand_iterations          6
% 3.19/0.99  --bmc1_ucm_extend_mode                  1
% 3.19/0.99  --bmc1_ucm_init_mode                    2
% 3.19/0.99  --bmc1_ucm_cone_mode                    none
% 3.19/0.99  --bmc1_ucm_reduced_relation_type        0
% 3.19/0.99  --bmc1_ucm_relax_model                  4
% 3.19/0.99  --bmc1_ucm_full_tr_after_sat            true
% 3.19/0.99  --bmc1_ucm_expand_neg_assumptions       false
% 3.19/0.99  --bmc1_ucm_layered_model                none
% 3.19/0.99  --bmc1_ucm_max_lemma_size               10
% 3.19/0.99  
% 3.19/0.99  ------ AIG Options
% 3.19/0.99  
% 3.19/0.99  --aig_mode                              false
% 3.19/0.99  
% 3.19/0.99  ------ Instantiation Options
% 3.19/0.99  
% 3.19/0.99  --instantiation_flag                    true
% 3.19/0.99  --inst_sos_flag                         false
% 3.19/0.99  --inst_sos_phase                        true
% 3.19/0.99  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 3.19/0.99  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 3.19/0.99  --inst_lit_sel_side                     none
% 3.19/0.99  --inst_solver_per_active                1400
% 3.19/0.99  --inst_solver_calls_frac                1.
% 3.19/0.99  --inst_passive_queue_type               priority_queues
% 3.19/0.99  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 3.19/0.99  --inst_passive_queues_freq              [25;2]
% 3.19/0.99  --inst_dismatching                      true
% 3.19/0.99  --inst_eager_unprocessed_to_passive     true
% 3.19/0.99  --inst_prop_sim_given                   true
% 3.19/0.99  --inst_prop_sim_new                     false
% 3.19/0.99  --inst_subs_new                         false
% 3.19/0.99  --inst_eq_res_simp                      false
% 3.19/0.99  --inst_subs_given                       false
% 3.19/0.99  --inst_orphan_elimination               true
% 3.19/0.99  --inst_learning_loop_flag               true
% 3.19/0.99  --inst_learning_start                   3000
% 3.19/0.99  --inst_learning_factor                  2
% 3.19/0.99  --inst_start_prop_sim_after_learn       3
% 3.19/0.99  --inst_sel_renew                        solver
% 3.19/0.99  --inst_lit_activity_flag                true
% 3.19/0.99  --inst_restr_to_given                   false
% 3.19/0.99  --inst_activity_threshold               500
% 3.19/0.99  --inst_out_proof                        true
% 3.19/0.99  
% 3.19/0.99  ------ Resolution Options
% 3.19/0.99  
% 3.19/0.99  --resolution_flag                       false
% 3.19/0.99  --res_lit_sel                           adaptive
% 3.19/0.99  --res_lit_sel_side                      none
% 3.19/0.99  --res_ordering                          kbo
% 3.19/0.99  --res_to_prop_solver                    active
% 3.19/0.99  --res_prop_simpl_new                    false
% 3.19/0.99  --res_prop_simpl_given                  true
% 3.19/0.99  --res_passive_queue_type                priority_queues
% 3.19/0.99  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 3.19/0.99  --res_passive_queues_freq               [15;5]
% 3.19/0.99  --res_forward_subs                      full
% 3.19/0.99  --res_backward_subs                     full
% 3.19/0.99  --res_forward_subs_resolution           true
% 3.19/0.99  --res_backward_subs_resolution          true
% 3.19/0.99  --res_orphan_elimination                true
% 3.19/0.99  --res_time_limit                        2.
% 3.19/0.99  --res_out_proof                         true
% 3.19/0.99  
% 3.19/0.99  ------ Superposition Options
% 3.19/0.99  
% 3.19/0.99  --superposition_flag                    true
% 3.19/0.99  --sup_passive_queue_type                priority_queues
% 3.19/0.99  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 3.19/0.99  --sup_passive_queues_freq               [8;1;4]
% 3.19/0.99  --demod_completeness_check              fast
% 3.19/0.99  --demod_use_ground                      true
% 3.19/0.99  --sup_to_prop_solver                    passive
% 3.19/0.99  --sup_prop_simpl_new                    true
% 3.19/0.99  --sup_prop_simpl_given                  true
% 3.19/0.99  --sup_fun_splitting                     false
% 3.19/0.99  --sup_smt_interval                      50000
% 3.19/0.99  
% 3.19/0.99  ------ Superposition Simplification Setup
% 3.19/0.99  
% 3.19/0.99  --sup_indices_passive                   []
% 3.19/0.99  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.19/0.99  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.19/0.99  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.19/0.99  --sup_full_triv                         [TrivRules;PropSubs]
% 3.19/0.99  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.19/0.99  --sup_full_bw                           [BwDemod]
% 3.19/0.99  --sup_immed_triv                        [TrivRules]
% 3.19/0.99  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 3.19/0.99  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.19/0.99  --sup_immed_bw_main                     []
% 3.19/0.99  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 3.19/0.99  --sup_input_triv                        [Unflattening;TrivRules]
% 3.19/0.99  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.19/0.99  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 3.19/0.99  
% 3.19/0.99  ------ Combination Options
% 3.19/0.99  
% 3.19/0.99  --comb_res_mult                         3
% 3.19/0.99  --comb_sup_mult                         2
% 3.19/0.99  --comb_inst_mult                        10
% 3.19/0.99  
% 3.19/0.99  ------ Debug Options
% 3.19/0.99  
% 3.19/0.99  --dbg_backtrace                         false
% 3.19/0.99  --dbg_dump_prop_clauses                 false
% 3.19/0.99  --dbg_dump_prop_clauses_file            -
% 3.19/0.99  --dbg_out_stat                          false
% 3.19/0.99  
% 3.19/0.99  
% 3.19/0.99  
% 3.19/0.99  
% 3.19/0.99  ------ Proving...
% 3.19/0.99  
% 3.19/0.99  
% 3.19/0.99  % SZS status Theorem for theBenchmark.p
% 3.19/0.99  
% 3.19/0.99   Resolution empty clause
% 3.19/0.99  
% 3.19/0.99  % SZS output start CNFRefutation for theBenchmark.p
% 3.19/0.99  
% 3.19/0.99  fof(f1,axiom,(
% 3.19/0.99    ! [X0,X1] : (! [X2] : (r2_hidden(X2,X0) <=> r2_hidden(X2,X1)) => X0 = X1)),
% 3.19/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.19/0.99  
% 3.19/0.99  fof(f16,plain,(
% 3.19/0.99    ! [X0,X1] : (X0 = X1 | ? [X2] : (r2_hidden(X2,X0) <~> r2_hidden(X2,X1)))),
% 3.19/0.99    inference(ennf_transformation,[],[f1])).
% 3.19/0.99  
% 3.19/0.99  fof(f31,plain,(
% 3.19/0.99    ! [X0,X1] : (X0 = X1 | ? [X2] : ((~r2_hidden(X2,X1) | ~r2_hidden(X2,X0)) & (r2_hidden(X2,X1) | r2_hidden(X2,X0))))),
% 3.19/0.99    inference(nnf_transformation,[],[f16])).
% 3.19/0.99  
% 3.19/0.99  fof(f32,plain,(
% 3.19/0.99    ! [X1,X0] : (? [X2] : ((~r2_hidden(X2,X1) | ~r2_hidden(X2,X0)) & (r2_hidden(X2,X1) | r2_hidden(X2,X0))) => ((~r2_hidden(sK0(X0,X1),X1) | ~r2_hidden(sK0(X0,X1),X0)) & (r2_hidden(sK0(X0,X1),X1) | r2_hidden(sK0(X0,X1),X0))))),
% 3.19/0.99    introduced(choice_axiom,[])).
% 3.19/0.99  
% 3.19/0.99  fof(f33,plain,(
% 3.19/0.99    ! [X0,X1] : (X0 = X1 | ((~r2_hidden(sK0(X0,X1),X1) | ~r2_hidden(sK0(X0,X1),X0)) & (r2_hidden(sK0(X0,X1),X1) | r2_hidden(sK0(X0,X1),X0))))),
% 3.19/0.99    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f31,f32])).
% 3.19/0.99  
% 3.19/0.99  fof(f47,plain,(
% 3.19/0.99    ( ! [X0,X1] : (X0 = X1 | r2_hidden(sK0(X0,X1),X1) | r2_hidden(sK0(X0,X1),X0)) )),
% 3.19/0.99    inference(cnf_transformation,[],[f33])).
% 3.19/0.99  
% 3.19/0.99  fof(f4,axiom,(
% 3.19/0.99    ! [X0,X1] : (r2_hidden(X0,X1) => m1_subset_1(X0,X1))),
% 3.19/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.19/0.99  
% 3.19/0.99  fof(f18,plain,(
% 3.19/0.99    ! [X0,X1] : (m1_subset_1(X0,X1) | ~r2_hidden(X0,X1))),
% 3.19/0.99    inference(ennf_transformation,[],[f4])).
% 3.19/0.99  
% 3.19/0.99  fof(f52,plain,(
% 3.19/0.99    ( ! [X0,X1] : (m1_subset_1(X0,X1) | ~r2_hidden(X0,X1)) )),
% 3.19/0.99    inference(cnf_transformation,[],[f18])).
% 3.19/0.99  
% 3.19/0.99  fof(f10,axiom,(
% 3.19/0.99    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => (v1_subset_1(X1,X0) <=> X0 != X1))),
% 3.19/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.19/0.99  
% 3.19/0.99  fof(f28,plain,(
% 3.19/0.99    ! [X0,X1] : ((v1_subset_1(X1,X0) <=> X0 != X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 3.19/0.99    inference(ennf_transformation,[],[f10])).
% 3.19/0.99  
% 3.19/0.99  fof(f41,plain,(
% 3.19/0.99    ! [X0,X1] : (((v1_subset_1(X1,X0) | X0 = X1) & (X0 != X1 | ~v1_subset_1(X1,X0))) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 3.19/0.99    inference(nnf_transformation,[],[f28])).
% 3.19/0.99  
% 3.19/0.99  fof(f64,plain,(
% 3.19/0.99    ( ! [X0,X1] : (v1_subset_1(X1,X0) | X0 = X1 | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 3.19/0.99    inference(cnf_transformation,[],[f41])).
% 3.19/0.99  
% 3.19/0.99  fof(f11,conjecture,(
% 3.19/0.99    ! [X0] : ((l1_orders_2(X0) & v1_yellow_0(X0) & v5_orders_2(X0) & v4_orders_2(X0) & v3_orders_2(X0) & ~v2_struct_0(X0)) => ! [X1] : ((m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & v13_waybel_0(X1,X0) & v2_waybel_0(X1,X0) & ~v1_xboole_0(X1)) => (v1_subset_1(X1,u1_struct_0(X0)) <=> ~r2_hidden(k3_yellow_0(X0),X1))))),
% 3.19/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.19/0.99  
% 3.19/0.99  fof(f12,negated_conjecture,(
% 3.19/0.99    ~! [X0] : ((l1_orders_2(X0) & v1_yellow_0(X0) & v5_orders_2(X0) & v4_orders_2(X0) & v3_orders_2(X0) & ~v2_struct_0(X0)) => ! [X1] : ((m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & v13_waybel_0(X1,X0) & v2_waybel_0(X1,X0) & ~v1_xboole_0(X1)) => (v1_subset_1(X1,u1_struct_0(X0)) <=> ~r2_hidden(k3_yellow_0(X0),X1))))),
% 3.19/0.99    inference(negated_conjecture,[],[f11])).
% 3.19/0.99  
% 3.19/0.99  fof(f13,plain,(
% 3.19/0.99    ~! [X0] : ((l1_orders_2(X0) & v1_yellow_0(X0) & v5_orders_2(X0) & v4_orders_2(X0) & v3_orders_2(X0) & ~v2_struct_0(X0)) => ! [X1] : ((m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & v13_waybel_0(X1,X0) & ~v1_xboole_0(X1)) => (v1_subset_1(X1,u1_struct_0(X0)) <=> ~r2_hidden(k3_yellow_0(X0),X1))))),
% 3.19/0.99    inference(pure_predicate_removal,[],[f12])).
% 3.19/0.99  
% 3.19/0.99  fof(f14,plain,(
% 3.19/0.99    ~! [X0] : ((l1_orders_2(X0) & v1_yellow_0(X0) & v5_orders_2(X0) & v3_orders_2(X0) & ~v2_struct_0(X0)) => ! [X1] : ((m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & v13_waybel_0(X1,X0) & ~v1_xboole_0(X1)) => (v1_subset_1(X1,u1_struct_0(X0)) <=> ~r2_hidden(k3_yellow_0(X0),X1))))),
% 3.19/0.99    inference(pure_predicate_removal,[],[f13])).
% 3.19/0.99  
% 3.19/0.99  fof(f15,plain,(
% 3.19/0.99    ~! [X0] : ((l1_orders_2(X0) & v1_yellow_0(X0) & v5_orders_2(X0) & ~v2_struct_0(X0)) => ! [X1] : ((m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & v13_waybel_0(X1,X0) & ~v1_xboole_0(X1)) => (v1_subset_1(X1,u1_struct_0(X0)) <=> ~r2_hidden(k3_yellow_0(X0),X1))))),
% 3.19/0.99    inference(pure_predicate_removal,[],[f14])).
% 3.19/0.99  
% 3.19/0.99  fof(f29,plain,(
% 3.19/0.99    ? [X0] : (? [X1] : ((v1_subset_1(X1,u1_struct_0(X0)) <~> ~r2_hidden(k3_yellow_0(X0),X1)) & (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & v13_waybel_0(X1,X0) & ~v1_xboole_0(X1))) & (l1_orders_2(X0) & v1_yellow_0(X0) & v5_orders_2(X0) & ~v2_struct_0(X0)))),
% 3.19/0.99    inference(ennf_transformation,[],[f15])).
% 3.19/0.99  
% 3.19/0.99  fof(f30,plain,(
% 3.19/0.99    ? [X0] : (? [X1] : ((v1_subset_1(X1,u1_struct_0(X0)) <~> ~r2_hidden(k3_yellow_0(X0),X1)) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & v13_waybel_0(X1,X0) & ~v1_xboole_0(X1)) & l1_orders_2(X0) & v1_yellow_0(X0) & v5_orders_2(X0) & ~v2_struct_0(X0))),
% 3.19/0.99    inference(flattening,[],[f29])).
% 3.19/0.99  
% 3.19/0.99  fof(f42,plain,(
% 3.19/0.99    ? [X0] : (? [X1] : (((r2_hidden(k3_yellow_0(X0),X1) | ~v1_subset_1(X1,u1_struct_0(X0))) & (~r2_hidden(k3_yellow_0(X0),X1) | v1_subset_1(X1,u1_struct_0(X0)))) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & v13_waybel_0(X1,X0) & ~v1_xboole_0(X1)) & l1_orders_2(X0) & v1_yellow_0(X0) & v5_orders_2(X0) & ~v2_struct_0(X0))),
% 3.19/0.99    inference(nnf_transformation,[],[f30])).
% 3.19/0.99  
% 3.19/0.99  fof(f43,plain,(
% 3.19/0.99    ? [X0] : (? [X1] : ((r2_hidden(k3_yellow_0(X0),X1) | ~v1_subset_1(X1,u1_struct_0(X0))) & (~r2_hidden(k3_yellow_0(X0),X1) | v1_subset_1(X1,u1_struct_0(X0))) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & v13_waybel_0(X1,X0) & ~v1_xboole_0(X1)) & l1_orders_2(X0) & v1_yellow_0(X0) & v5_orders_2(X0) & ~v2_struct_0(X0))),
% 3.19/0.99    inference(flattening,[],[f42])).
% 3.19/0.99  
% 3.19/0.99  fof(f45,plain,(
% 3.19/0.99    ( ! [X0] : (? [X1] : ((r2_hidden(k3_yellow_0(X0),X1) | ~v1_subset_1(X1,u1_struct_0(X0))) & (~r2_hidden(k3_yellow_0(X0),X1) | v1_subset_1(X1,u1_struct_0(X0))) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & v13_waybel_0(X1,X0) & ~v1_xboole_0(X1)) => ((r2_hidden(k3_yellow_0(X0),sK5) | ~v1_subset_1(sK5,u1_struct_0(X0))) & (~r2_hidden(k3_yellow_0(X0),sK5) | v1_subset_1(sK5,u1_struct_0(X0))) & m1_subset_1(sK5,k1_zfmisc_1(u1_struct_0(X0))) & v13_waybel_0(sK5,X0) & ~v1_xboole_0(sK5))) )),
% 3.19/0.99    introduced(choice_axiom,[])).
% 3.19/0.99  
% 3.19/0.99  fof(f44,plain,(
% 3.19/0.99    ? [X0] : (? [X1] : ((r2_hidden(k3_yellow_0(X0),X1) | ~v1_subset_1(X1,u1_struct_0(X0))) & (~r2_hidden(k3_yellow_0(X0),X1) | v1_subset_1(X1,u1_struct_0(X0))) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & v13_waybel_0(X1,X0) & ~v1_xboole_0(X1)) & l1_orders_2(X0) & v1_yellow_0(X0) & v5_orders_2(X0) & ~v2_struct_0(X0)) => (? [X1] : ((r2_hidden(k3_yellow_0(sK4),X1) | ~v1_subset_1(X1,u1_struct_0(sK4))) & (~r2_hidden(k3_yellow_0(sK4),X1) | v1_subset_1(X1,u1_struct_0(sK4))) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK4))) & v13_waybel_0(X1,sK4) & ~v1_xboole_0(X1)) & l1_orders_2(sK4) & v1_yellow_0(sK4) & v5_orders_2(sK4) & ~v2_struct_0(sK4))),
% 3.19/0.99    introduced(choice_axiom,[])).
% 3.19/0.99  
% 3.19/0.99  fof(f46,plain,(
% 3.19/0.99    ((r2_hidden(k3_yellow_0(sK4),sK5) | ~v1_subset_1(sK5,u1_struct_0(sK4))) & (~r2_hidden(k3_yellow_0(sK4),sK5) | v1_subset_1(sK5,u1_struct_0(sK4))) & m1_subset_1(sK5,k1_zfmisc_1(u1_struct_0(sK4))) & v13_waybel_0(sK5,sK4) & ~v1_xboole_0(sK5)) & l1_orders_2(sK4) & v1_yellow_0(sK4) & v5_orders_2(sK4) & ~v2_struct_0(sK4)),
% 3.19/0.99    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4,sK5])],[f43,f45,f44])).
% 3.19/0.99  
% 3.19/0.99  fof(f73,plain,(
% 3.19/0.99    r2_hidden(k3_yellow_0(sK4),sK5) | ~v1_subset_1(sK5,u1_struct_0(sK4))),
% 3.19/0.99    inference(cnf_transformation,[],[f46])).
% 3.19/0.99  
% 3.19/0.99  fof(f71,plain,(
% 3.19/0.99    m1_subset_1(sK5,k1_zfmisc_1(u1_struct_0(sK4)))),
% 3.19/0.99    inference(cnf_transformation,[],[f46])).
% 3.19/0.99  
% 3.19/0.99  fof(f9,axiom,(
% 3.19/0.99    ! [X0] : (l1_orders_2(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => (v13_waybel_0(X1,X0) <=> ! [X2] : (m1_subset_1(X2,u1_struct_0(X0)) => ! [X3] : (m1_subset_1(X3,u1_struct_0(X0)) => ((r1_orders_2(X0,X2,X3) & r2_hidden(X2,X1)) => r2_hidden(X3,X1)))))))),
% 3.19/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.19/0.99  
% 3.19/0.99  fof(f26,plain,(
% 3.19/0.99    ! [X0] : (! [X1] : ((v13_waybel_0(X1,X0) <=> ! [X2] : (! [X3] : ((r2_hidden(X3,X1) | (~r1_orders_2(X0,X2,X3) | ~r2_hidden(X2,X1))) | ~m1_subset_1(X3,u1_struct_0(X0))) | ~m1_subset_1(X2,u1_struct_0(X0)))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_orders_2(X0))),
% 3.19/0.99    inference(ennf_transformation,[],[f9])).
% 3.19/0.99  
% 3.19/0.99  fof(f27,plain,(
% 3.19/0.99    ! [X0] : (! [X1] : ((v13_waybel_0(X1,X0) <=> ! [X2] : (! [X3] : (r2_hidden(X3,X1) | ~r1_orders_2(X0,X2,X3) | ~r2_hidden(X2,X1) | ~m1_subset_1(X3,u1_struct_0(X0))) | ~m1_subset_1(X2,u1_struct_0(X0)))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_orders_2(X0))),
% 3.19/0.99    inference(flattening,[],[f26])).
% 3.19/0.99  
% 3.19/0.99  fof(f36,plain,(
% 3.19/0.99    ! [X0] : (! [X1] : (((v13_waybel_0(X1,X0) | ? [X2] : (? [X3] : (~r2_hidden(X3,X1) & r1_orders_2(X0,X2,X3) & r2_hidden(X2,X1) & m1_subset_1(X3,u1_struct_0(X0))) & m1_subset_1(X2,u1_struct_0(X0)))) & (! [X2] : (! [X3] : (r2_hidden(X3,X1) | ~r1_orders_2(X0,X2,X3) | ~r2_hidden(X2,X1) | ~m1_subset_1(X3,u1_struct_0(X0))) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~v13_waybel_0(X1,X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_orders_2(X0))),
% 3.19/0.99    inference(nnf_transformation,[],[f27])).
% 3.19/0.99  
% 3.19/0.99  fof(f37,plain,(
% 3.19/0.99    ! [X0] : (! [X1] : (((v13_waybel_0(X1,X0) | ? [X2] : (? [X3] : (~r2_hidden(X3,X1) & r1_orders_2(X0,X2,X3) & r2_hidden(X2,X1) & m1_subset_1(X3,u1_struct_0(X0))) & m1_subset_1(X2,u1_struct_0(X0)))) & (! [X4] : (! [X5] : (r2_hidden(X5,X1) | ~r1_orders_2(X0,X4,X5) | ~r2_hidden(X4,X1) | ~m1_subset_1(X5,u1_struct_0(X0))) | ~m1_subset_1(X4,u1_struct_0(X0))) | ~v13_waybel_0(X1,X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_orders_2(X0))),
% 3.19/0.99    inference(rectify,[],[f36])).
% 3.19/0.99  
% 3.19/0.99  fof(f39,plain,(
% 3.19/0.99    ( ! [X2] : (! [X1,X0] : (? [X3] : (~r2_hidden(X3,X1) & r1_orders_2(X0,X2,X3) & r2_hidden(X2,X1) & m1_subset_1(X3,u1_struct_0(X0))) => (~r2_hidden(sK3(X0,X1),X1) & r1_orders_2(X0,X2,sK3(X0,X1)) & r2_hidden(X2,X1) & m1_subset_1(sK3(X0,X1),u1_struct_0(X0))))) )),
% 3.19/0.99    introduced(choice_axiom,[])).
% 3.19/0.99  
% 3.19/0.99  fof(f38,plain,(
% 3.19/0.99    ! [X1,X0] : (? [X2] : (? [X3] : (~r2_hidden(X3,X1) & r1_orders_2(X0,X2,X3) & r2_hidden(X2,X1) & m1_subset_1(X3,u1_struct_0(X0))) & m1_subset_1(X2,u1_struct_0(X0))) => (? [X3] : (~r2_hidden(X3,X1) & r1_orders_2(X0,sK2(X0,X1),X3) & r2_hidden(sK2(X0,X1),X1) & m1_subset_1(X3,u1_struct_0(X0))) & m1_subset_1(sK2(X0,X1),u1_struct_0(X0))))),
% 3.19/0.99    introduced(choice_axiom,[])).
% 3.19/0.99  
% 3.19/0.99  fof(f40,plain,(
% 3.19/0.99    ! [X0] : (! [X1] : (((v13_waybel_0(X1,X0) | ((~r2_hidden(sK3(X0,X1),X1) & r1_orders_2(X0,sK2(X0,X1),sK3(X0,X1)) & r2_hidden(sK2(X0,X1),X1) & m1_subset_1(sK3(X0,X1),u1_struct_0(X0))) & m1_subset_1(sK2(X0,X1),u1_struct_0(X0)))) & (! [X4] : (! [X5] : (r2_hidden(X5,X1) | ~r1_orders_2(X0,X4,X5) | ~r2_hidden(X4,X1) | ~m1_subset_1(X5,u1_struct_0(X0))) | ~m1_subset_1(X4,u1_struct_0(X0))) | ~v13_waybel_0(X1,X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_orders_2(X0))),
% 3.19/0.99    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2,sK3])],[f37,f39,f38])).
% 3.19/0.99  
% 3.19/0.99  fof(f57,plain,(
% 3.19/0.99    ( ! [X4,X0,X5,X1] : (r2_hidden(X5,X1) | ~r1_orders_2(X0,X4,X5) | ~r2_hidden(X4,X1) | ~m1_subset_1(X5,u1_struct_0(X0)) | ~m1_subset_1(X4,u1_struct_0(X0)) | ~v13_waybel_0(X1,X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_orders_2(X0)) )),
% 3.19/0.99    inference(cnf_transformation,[],[f40])).
% 3.19/0.99  
% 3.19/0.99  fof(f8,axiom,(
% 3.19/0.99    ! [X0] : ((l1_orders_2(X0) & v1_yellow_0(X0) & v5_orders_2(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,u1_struct_0(X0)) => r1_orders_2(X0,k3_yellow_0(X0),X1)))),
% 3.19/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.19/0.99  
% 3.19/0.99  fof(f24,plain,(
% 3.19/0.99    ! [X0] : (! [X1] : (r1_orders_2(X0,k3_yellow_0(X0),X1) | ~m1_subset_1(X1,u1_struct_0(X0))) | (~l1_orders_2(X0) | ~v1_yellow_0(X0) | ~v5_orders_2(X0) | v2_struct_0(X0)))),
% 3.19/0.99    inference(ennf_transformation,[],[f8])).
% 3.19/0.99  
% 3.19/0.99  fof(f25,plain,(
% 3.19/0.99    ! [X0] : (! [X1] : (r1_orders_2(X0,k3_yellow_0(X0),X1) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~l1_orders_2(X0) | ~v1_yellow_0(X0) | ~v5_orders_2(X0) | v2_struct_0(X0))),
% 3.19/0.99    inference(flattening,[],[f24])).
% 3.19/0.99  
% 3.19/0.99  fof(f56,plain,(
% 3.19/0.99    ( ! [X0,X1] : (r1_orders_2(X0,k3_yellow_0(X0),X1) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_orders_2(X0) | ~v1_yellow_0(X0) | ~v5_orders_2(X0) | v2_struct_0(X0)) )),
% 3.19/0.99    inference(cnf_transformation,[],[f25])).
% 3.19/0.99  
% 3.19/0.99  fof(f67,plain,(
% 3.19/0.99    v1_yellow_0(sK4)),
% 3.19/0.99    inference(cnf_transformation,[],[f46])).
% 3.19/0.99  
% 3.19/0.99  fof(f65,plain,(
% 3.19/0.99    ~v2_struct_0(sK4)),
% 3.19/0.99    inference(cnf_transformation,[],[f46])).
% 3.19/0.99  
% 3.19/0.99  fof(f66,plain,(
% 3.19/0.99    v5_orders_2(sK4)),
% 3.19/0.99    inference(cnf_transformation,[],[f46])).
% 3.19/0.99  
% 3.19/0.99  fof(f68,plain,(
% 3.19/0.99    l1_orders_2(sK4)),
% 3.19/0.99    inference(cnf_transformation,[],[f46])).
% 3.19/0.99  
% 3.19/0.99  fof(f7,axiom,(
% 3.19/0.99    ! [X0] : (l1_orders_2(X0) => m1_subset_1(k3_yellow_0(X0),u1_struct_0(X0)))),
% 3.19/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.19/0.99  
% 3.19/0.99  fof(f23,plain,(
% 3.19/0.99    ! [X0] : (m1_subset_1(k3_yellow_0(X0),u1_struct_0(X0)) | ~l1_orders_2(X0))),
% 3.19/0.99    inference(ennf_transformation,[],[f7])).
% 3.19/0.99  
% 3.19/0.99  fof(f55,plain,(
% 3.19/0.99    ( ! [X0] : (m1_subset_1(k3_yellow_0(X0),u1_struct_0(X0)) | ~l1_orders_2(X0)) )),
% 3.19/0.99    inference(cnf_transformation,[],[f23])).
% 3.19/0.99  
% 3.19/0.99  fof(f70,plain,(
% 3.19/0.99    v13_waybel_0(sK5,sK4)),
% 3.19/0.99    inference(cnf_transformation,[],[f46])).
% 3.19/0.99  
% 3.19/0.99  fof(f61,plain,(
% 3.19/0.99    ( ! [X0,X1] : (v13_waybel_0(X1,X0) | r1_orders_2(X0,sK2(X0,X1),sK3(X0,X1)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_orders_2(X0)) )),
% 3.19/0.99    inference(cnf_transformation,[],[f40])).
% 3.19/0.99  
% 3.19/0.99  fof(f59,plain,(
% 3.19/0.99    ( ! [X0,X1] : (v13_waybel_0(X1,X0) | m1_subset_1(sK3(X0,X1),u1_struct_0(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_orders_2(X0)) )),
% 3.19/0.99    inference(cnf_transformation,[],[f40])).
% 3.19/0.99  
% 3.19/0.99  fof(f6,axiom,(
% 3.19/0.99    ! [X0,X1,X2] : ((m1_subset_1(X1,k1_zfmisc_1(X2)) & r2_hidden(X0,X1)) => m1_subset_1(X0,X2))),
% 3.19/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.19/0.99  
% 3.19/0.99  fof(f21,plain,(
% 3.19/0.99    ! [X0,X1,X2] : (m1_subset_1(X0,X2) | (~m1_subset_1(X1,k1_zfmisc_1(X2)) | ~r2_hidden(X0,X1)))),
% 3.19/0.99    inference(ennf_transformation,[],[f6])).
% 3.19/0.99  
% 3.19/0.99  fof(f22,plain,(
% 3.19/0.99    ! [X0,X1,X2] : (m1_subset_1(X0,X2) | ~m1_subset_1(X1,k1_zfmisc_1(X2)) | ~r2_hidden(X0,X1))),
% 3.19/0.99    inference(flattening,[],[f21])).
% 3.19/0.99  
% 3.19/0.99  fof(f54,plain,(
% 3.19/0.99    ( ! [X2,X0,X1] : (m1_subset_1(X0,X2) | ~m1_subset_1(X1,k1_zfmisc_1(X2)) | ~r2_hidden(X0,X1)) )),
% 3.19/0.99    inference(cnf_transformation,[],[f22])).
% 3.19/0.99  
% 3.19/0.99  fof(f69,plain,(
% 3.19/0.99    ~v1_xboole_0(sK5)),
% 3.19/0.99    inference(cnf_transformation,[],[f46])).
% 3.19/0.99  
% 3.19/0.99  fof(f3,axiom,(
% 3.19/0.99    ! [X0] : ? [X1] : (~v1_subset_1(X1,X0) & m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 3.19/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.19/0.99  
% 3.19/0.99  fof(f34,plain,(
% 3.19/0.99    ! [X0] : (? [X1] : (~v1_subset_1(X1,X0) & m1_subset_1(X1,k1_zfmisc_1(X0))) => (~v1_subset_1(sK1(X0),X0) & m1_subset_1(sK1(X0),k1_zfmisc_1(X0))))),
% 3.19/0.99    introduced(choice_axiom,[])).
% 3.19/0.99  
% 3.19/0.99  fof(f35,plain,(
% 3.19/0.99    ! [X0] : (~v1_subset_1(sK1(X0),X0) & m1_subset_1(sK1(X0),k1_zfmisc_1(X0)))),
% 3.19/0.99    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1])],[f3,f34])).
% 3.19/0.99  
% 3.19/0.99  fof(f50,plain,(
% 3.19/0.99    ( ! [X0] : (m1_subset_1(sK1(X0),k1_zfmisc_1(X0))) )),
% 3.19/0.99    inference(cnf_transformation,[],[f35])).
% 3.19/0.99  
% 3.19/0.99  fof(f5,axiom,(
% 3.19/0.99    ! [X0,X1] : (m1_subset_1(X0,X1) => (r2_hidden(X0,X1) | v1_xboole_0(X1)))),
% 3.19/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.19/0.99  
% 3.19/0.99  fof(f19,plain,(
% 3.19/0.99    ! [X0,X1] : ((r2_hidden(X0,X1) | v1_xboole_0(X1)) | ~m1_subset_1(X0,X1))),
% 3.19/0.99    inference(ennf_transformation,[],[f5])).
% 3.19/0.99  
% 3.19/0.99  fof(f20,plain,(
% 3.19/0.99    ! [X0,X1] : (r2_hidden(X0,X1) | v1_xboole_0(X1) | ~m1_subset_1(X0,X1))),
% 3.19/0.99    inference(flattening,[],[f19])).
% 3.19/0.99  
% 3.19/0.99  fof(f53,plain,(
% 3.19/0.99    ( ! [X0,X1] : (r2_hidden(X0,X1) | v1_xboole_0(X1) | ~m1_subset_1(X0,X1)) )),
% 3.19/0.99    inference(cnf_transformation,[],[f20])).
% 3.19/0.99  
% 3.19/0.99  fof(f2,axiom,(
% 3.19/0.99    ! [X0] : (v1_xboole_0(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => v1_xboole_0(X1)))),
% 3.19/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.19/0.99  
% 3.19/0.99  fof(f17,plain,(
% 3.19/0.99    ! [X0] : (! [X1] : (v1_xboole_0(X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) | ~v1_xboole_0(X0))),
% 3.19/0.99    inference(ennf_transformation,[],[f2])).
% 3.19/0.99  
% 3.19/0.99  fof(f49,plain,(
% 3.19/0.99    ( ! [X0,X1] : (v1_xboole_0(X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0)) | ~v1_xboole_0(X0)) )),
% 3.19/0.99    inference(cnf_transformation,[],[f17])).
% 3.19/0.99  
% 3.19/0.99  fof(f48,plain,(
% 3.19/0.99    ( ! [X0,X1] : (X0 = X1 | ~r2_hidden(sK0(X0,X1),X1) | ~r2_hidden(sK0(X0,X1),X0)) )),
% 3.19/0.99    inference(cnf_transformation,[],[f33])).
% 3.19/0.99  
% 3.19/0.99  fof(f51,plain,(
% 3.19/0.99    ( ! [X0] : (~v1_subset_1(sK1(X0),X0)) )),
% 3.19/0.99    inference(cnf_transformation,[],[f35])).
% 3.19/0.99  
% 3.19/0.99  fof(f60,plain,(
% 3.19/0.99    ( ! [X0,X1] : (v13_waybel_0(X1,X0) | r2_hidden(sK2(X0,X1),X1) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_orders_2(X0)) )),
% 3.19/0.99    inference(cnf_transformation,[],[f40])).
% 3.19/0.99  
% 3.19/0.99  fof(f62,plain,(
% 3.19/0.99    ( ! [X0,X1] : (v13_waybel_0(X1,X0) | ~r2_hidden(sK3(X0,X1),X1) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_orders_2(X0)) )),
% 3.19/0.99    inference(cnf_transformation,[],[f40])).
% 3.19/0.99  
% 3.19/0.99  fof(f58,plain,(
% 3.19/0.99    ( ! [X0,X1] : (v13_waybel_0(X1,X0) | m1_subset_1(sK2(X0,X1),u1_struct_0(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_orders_2(X0)) )),
% 3.19/0.99    inference(cnf_transformation,[],[f40])).
% 3.19/0.99  
% 3.19/0.99  fof(f72,plain,(
% 3.19/0.99    ~r2_hidden(k3_yellow_0(sK4),sK5) | v1_subset_1(sK5,u1_struct_0(sK4))),
% 3.19/0.99    inference(cnf_transformation,[],[f46])).
% 3.19/0.99  
% 3.19/0.99  cnf(c_1,plain,
% 3.19/0.99      ( r2_hidden(sK0(X0,X1),X1) | r2_hidden(sK0(X0,X1),X0) | X1 = X0 ),
% 3.19/0.99      inference(cnf_transformation,[],[f47]) ).
% 3.19/0.99  
% 3.19/0.99  cnf(c_1142,plain,
% 3.19/0.99      ( X0 = X1
% 3.19/0.99      | r2_hidden(sK0(X1,X0),X0) = iProver_top
% 3.19/0.99      | r2_hidden(sK0(X1,X0),X1) = iProver_top ),
% 3.19/0.99      inference(predicate_to_equality,[status(thm)],[c_1]) ).
% 3.19/0.99  
% 3.19/0.99  cnf(c_5,plain,
% 3.19/0.99      ( m1_subset_1(X0,X1) | ~ r2_hidden(X0,X1) ),
% 3.19/0.99      inference(cnf_transformation,[],[f52]) ).
% 3.19/0.99  
% 3.19/0.99  cnf(c_1139,plain,
% 3.19/0.99      ( m1_subset_1(X0,X1) = iProver_top | r2_hidden(X0,X1) != iProver_top ),
% 3.19/0.99      inference(predicate_to_equality,[status(thm)],[c_5]) ).
% 3.19/0.99  
% 3.19/0.99  cnf(c_1643,plain,
% 3.19/0.99      ( X0 = X1
% 3.19/0.99      | m1_subset_1(sK0(X0,X1),X1) = iProver_top
% 3.19/0.99      | r2_hidden(sK0(X0,X1),X0) = iProver_top ),
% 3.19/0.99      inference(superposition,[status(thm)],[c_1142,c_1139]) ).
% 3.19/0.99  
% 3.19/0.99  cnf(c_16,plain,
% 3.19/0.99      ( v1_subset_1(X0,X1) | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) | X0 = X1 ),
% 3.19/0.99      inference(cnf_transformation,[],[f64]) ).
% 3.19/0.99  
% 3.19/0.99  cnf(c_18,negated_conjecture,
% 3.19/0.99      ( ~ v1_subset_1(sK5,u1_struct_0(sK4)) | r2_hidden(k3_yellow_0(sK4),sK5) ),
% 3.19/0.99      inference(cnf_transformation,[],[f73]) ).
% 3.19/0.99  
% 3.19/0.99  cnf(c_201,plain,
% 3.19/0.99      ( ~ v1_subset_1(sK5,u1_struct_0(sK4)) | r2_hidden(k3_yellow_0(sK4),sK5) ),
% 3.19/0.99      inference(prop_impl,[status(thm)],[c_18]) ).
% 3.19/0.99  
% 3.19/0.99  cnf(c_402,plain,
% 3.19/0.99      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
% 3.19/0.99      | r2_hidden(k3_yellow_0(sK4),sK5)
% 3.19/0.99      | X1 = X0
% 3.19/0.99      | u1_struct_0(sK4) != X1
% 3.19/0.99      | sK5 != X0 ),
% 3.19/0.99      inference(resolution_lifted,[status(thm)],[c_16,c_201]) ).
% 3.19/0.99  
% 3.19/0.99  cnf(c_403,plain,
% 3.19/0.99      ( ~ m1_subset_1(sK5,k1_zfmisc_1(u1_struct_0(sK4)))
% 3.19/0.99      | r2_hidden(k3_yellow_0(sK4),sK5)
% 3.19/0.99      | u1_struct_0(sK4) = sK5 ),
% 3.19/0.99      inference(unflattening,[status(thm)],[c_402]) ).
% 3.19/0.99  
% 3.19/0.99  cnf(c_20,negated_conjecture,
% 3.19/0.99      ( m1_subset_1(sK5,k1_zfmisc_1(u1_struct_0(sK4))) ),
% 3.19/0.99      inference(cnf_transformation,[],[f71]) ).
% 3.19/0.99  
% 3.19/0.99  cnf(c_405,plain,
% 3.19/0.99      ( r2_hidden(k3_yellow_0(sK4),sK5) | u1_struct_0(sK4) = sK5 ),
% 3.19/0.99      inference(global_propositional_subsumption,[status(thm)],[c_403,c_20]) ).
% 3.19/0.99  
% 3.19/0.99  cnf(c_1132,plain,
% 3.19/0.99      ( u1_struct_0(sK4) = sK5
% 3.19/0.99      | r2_hidden(k3_yellow_0(sK4),sK5) = iProver_top ),
% 3.19/0.99      inference(predicate_to_equality,[status(thm)],[c_405]) ).
% 3.19/0.99  
% 3.19/0.99  cnf(c_1136,plain,
% 3.19/0.99      ( m1_subset_1(sK5,k1_zfmisc_1(u1_struct_0(sK4))) = iProver_top ),
% 3.19/0.99      inference(predicate_to_equality,[status(thm)],[c_20]) ).
% 3.19/0.99  
% 3.19/0.99  cnf(c_15,plain,
% 3.19/0.99      ( ~ r1_orders_2(X0,X1,X2)
% 3.19/0.99      | ~ v13_waybel_0(X3,X0)
% 3.19/0.99      | ~ m1_subset_1(X2,u1_struct_0(X0))
% 3.19/0.99      | ~ m1_subset_1(X1,u1_struct_0(X0))
% 3.19/0.99      | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))
% 3.19/0.99      | ~ r2_hidden(X1,X3)
% 3.19/0.99      | r2_hidden(X2,X3)
% 3.19/0.99      | ~ l1_orders_2(X0) ),
% 3.19/0.99      inference(cnf_transformation,[],[f57]) ).
% 3.19/0.99  
% 3.19/0.99  cnf(c_9,plain,
% 3.19/0.99      ( r1_orders_2(X0,k3_yellow_0(X0),X1)
% 3.19/0.99      | ~ m1_subset_1(X1,u1_struct_0(X0))
% 3.19/0.99      | v2_struct_0(X0)
% 3.19/0.99      | ~ v5_orders_2(X0)
% 3.19/0.99      | ~ v1_yellow_0(X0)
% 3.19/0.99      | ~ l1_orders_2(X0) ),
% 3.19/0.99      inference(cnf_transformation,[],[f56]) ).
% 3.19/0.99  
% 3.19/0.99  cnf(c_24,negated_conjecture,
% 3.19/0.99      ( v1_yellow_0(sK4) ),
% 3.19/0.99      inference(cnf_transformation,[],[f67]) ).
% 3.19/0.99  
% 3.19/0.99  cnf(c_357,plain,
% 3.19/0.99      ( r1_orders_2(X0,k3_yellow_0(X0),X1)
% 3.19/0.99      | ~ m1_subset_1(X1,u1_struct_0(X0))
% 3.19/0.99      | v2_struct_0(X0)
% 3.19/0.99      | ~ v5_orders_2(X0)
% 3.19/0.99      | ~ l1_orders_2(X0)
% 3.19/0.99      | sK4 != X0 ),
% 3.19/0.99      inference(resolution_lifted,[status(thm)],[c_9,c_24]) ).
% 3.19/0.99  
% 3.19/0.99  cnf(c_358,plain,
% 3.19/0.99      ( r1_orders_2(sK4,k3_yellow_0(sK4),X0)
% 3.19/0.99      | ~ m1_subset_1(X0,u1_struct_0(sK4))
% 3.19/0.99      | v2_struct_0(sK4)
% 3.19/0.99      | ~ v5_orders_2(sK4)
% 3.19/0.99      | ~ l1_orders_2(sK4) ),
% 3.19/0.99      inference(unflattening,[status(thm)],[c_357]) ).
% 3.19/0.99  
% 3.19/0.99  cnf(c_26,negated_conjecture,
% 3.19/0.99      ( ~ v2_struct_0(sK4) ),
% 3.19/0.99      inference(cnf_transformation,[],[f65]) ).
% 3.19/0.99  
% 3.19/0.99  cnf(c_25,negated_conjecture,
% 3.19/0.99      ( v5_orders_2(sK4) ),
% 3.19/0.99      inference(cnf_transformation,[],[f66]) ).
% 3.19/0.99  
% 3.19/0.99  cnf(c_23,negated_conjecture,
% 3.19/0.99      ( l1_orders_2(sK4) ),
% 3.19/0.99      inference(cnf_transformation,[],[f68]) ).
% 3.19/0.99  
% 3.19/0.99  cnf(c_362,plain,
% 3.19/0.99      ( ~ m1_subset_1(X0,u1_struct_0(sK4))
% 3.19/0.99      | r1_orders_2(sK4,k3_yellow_0(sK4),X0) ),
% 3.19/0.99      inference(global_propositional_subsumption,
% 3.19/0.99                [status(thm)],
% 3.19/0.99                [c_358,c_26,c_25,c_23]) ).
% 3.19/0.99  
% 3.19/0.99  cnf(c_363,plain,
% 3.19/0.99      ( r1_orders_2(sK4,k3_yellow_0(sK4),X0)
% 3.19/0.99      | ~ m1_subset_1(X0,u1_struct_0(sK4)) ),
% 3.19/0.99      inference(renaming,[status(thm)],[c_362]) ).
% 3.19/0.99  
% 3.19/0.99  cnf(c_470,plain,
% 3.19/0.99      ( ~ v13_waybel_0(X0,X1)
% 3.19/0.99      | ~ m1_subset_1(X2,u1_struct_0(X1))
% 3.19/0.99      | ~ m1_subset_1(X3,u1_struct_0(X1))
% 3.19/0.99      | ~ m1_subset_1(X4,u1_struct_0(sK4))
% 3.19/0.99      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 3.19/0.99      | ~ r2_hidden(X2,X0)
% 3.19/0.99      | r2_hidden(X3,X0)
% 3.19/0.99      | ~ l1_orders_2(X1)
% 3.19/0.99      | X4 != X3
% 3.19/0.99      | k3_yellow_0(sK4) != X2
% 3.19/0.99      | sK4 != X1 ),
% 3.19/0.99      inference(resolution_lifted,[status(thm)],[c_15,c_363]) ).
% 3.19/0.99  
% 3.19/0.99  cnf(c_471,plain,
% 3.19/0.99      ( ~ v13_waybel_0(X0,sK4)
% 3.19/0.99      | ~ m1_subset_1(X1,u1_struct_0(sK4))
% 3.19/0.99      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK4)))
% 3.19/0.99      | ~ m1_subset_1(k3_yellow_0(sK4),u1_struct_0(sK4))
% 3.19/0.99      | r2_hidden(X1,X0)
% 3.19/0.99      | ~ r2_hidden(k3_yellow_0(sK4),X0)
% 3.19/0.99      | ~ l1_orders_2(sK4) ),
% 3.19/0.99      inference(unflattening,[status(thm)],[c_470]) ).
% 3.19/0.99  
% 3.19/0.99  cnf(c_8,plain,
% 3.19/0.99      ( m1_subset_1(k3_yellow_0(X0),u1_struct_0(X0)) | ~ l1_orders_2(X0) ),
% 3.19/0.99      inference(cnf_transformation,[],[f55]) ).
% 3.19/0.99  
% 3.19/0.99  cnf(c_62,plain,
% 3.19/0.99      ( m1_subset_1(k3_yellow_0(sK4),u1_struct_0(sK4)) | ~ l1_orders_2(sK4) ),
% 3.19/0.99      inference(instantiation,[status(thm)],[c_8]) ).
% 3.19/0.99  
% 3.19/0.99  cnf(c_475,plain,
% 3.19/0.99      ( ~ r2_hidden(k3_yellow_0(sK4),X0)
% 3.19/0.99      | r2_hidden(X1,X0)
% 3.19/0.99      | ~ v13_waybel_0(X0,sK4)
% 3.19/0.99      | ~ m1_subset_1(X1,u1_struct_0(sK4))
% 3.19/0.99      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK4))) ),
% 3.19/0.99      inference(global_propositional_subsumption,
% 3.19/0.99                [status(thm)],
% 3.19/0.99                [c_471,c_23,c_62]) ).
% 3.19/0.99  
% 3.19/0.99  cnf(c_476,plain,
% 3.19/0.99      ( ~ v13_waybel_0(X0,sK4)
% 3.19/0.99      | ~ m1_subset_1(X1,u1_struct_0(sK4))
% 3.19/0.99      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK4)))
% 3.19/0.99      | r2_hidden(X1,X0)
% 3.19/0.99      | ~ r2_hidden(k3_yellow_0(sK4),X0) ),
% 3.19/0.99      inference(renaming,[status(thm)],[c_475]) ).
% 3.19/0.99  
% 3.19/0.99  cnf(c_1130,plain,
% 3.19/0.99      ( v13_waybel_0(X0,sK4) != iProver_top
% 3.19/0.99      | m1_subset_1(X1,u1_struct_0(sK4)) != iProver_top
% 3.19/0.99      | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK4))) != iProver_top
% 3.19/0.99      | r2_hidden(X1,X0) = iProver_top
% 3.19/0.99      | r2_hidden(k3_yellow_0(sK4),X0) != iProver_top ),
% 3.19/0.99      inference(predicate_to_equality,[status(thm)],[c_476]) ).
% 3.19/0.99  
% 3.19/0.99  cnf(c_1721,plain,
% 3.19/0.99      ( v13_waybel_0(sK5,sK4) != iProver_top
% 3.19/0.99      | m1_subset_1(X0,u1_struct_0(sK4)) != iProver_top
% 3.19/0.99      | r2_hidden(X0,sK5) = iProver_top
% 3.19/0.99      | r2_hidden(k3_yellow_0(sK4),sK5) != iProver_top ),
% 3.19/0.99      inference(superposition,[status(thm)],[c_1136,c_1130]) ).
% 3.19/0.99  
% 3.19/0.99  cnf(c_21,negated_conjecture,
% 3.19/0.99      ( v13_waybel_0(sK5,sK4) ),
% 3.19/0.99      inference(cnf_transformation,[],[f70]) ).
% 3.19/0.99  
% 3.19/0.99  cnf(c_32,plain,
% 3.19/0.99      ( v13_waybel_0(sK5,sK4) = iProver_top ),
% 3.19/0.99      inference(predicate_to_equality,[status(thm)],[c_21]) ).
% 3.19/0.99  
% 3.19/0.99  cnf(c_1726,plain,
% 3.19/0.99      ( m1_subset_1(X0,u1_struct_0(sK4)) != iProver_top
% 3.19/0.99      | r2_hidden(X0,sK5) = iProver_top
% 3.19/0.99      | r2_hidden(k3_yellow_0(sK4),sK5) != iProver_top ),
% 3.19/0.99      inference(global_propositional_subsumption,[status(thm)],[c_1721,c_32]) ).
% 3.19/0.99  
% 3.19/0.99  cnf(c_1868,plain,
% 3.19/0.99      ( u1_struct_0(sK4) = sK5
% 3.19/0.99      | m1_subset_1(X0,u1_struct_0(sK4)) != iProver_top
% 3.19/0.99      | r2_hidden(X0,sK5) = iProver_top ),
% 3.19/0.99      inference(superposition,[status(thm)],[c_1132,c_1726]) ).
% 3.19/0.99  
% 3.19/0.99  cnf(c_3371,plain,
% 3.19/0.99      ( u1_struct_0(sK4) = X0
% 3.19/0.99      | u1_struct_0(sK4) = sK5
% 3.19/0.99      | r2_hidden(sK0(X0,u1_struct_0(sK4)),X0) = iProver_top
% 3.19/0.99      | r2_hidden(sK0(X0,u1_struct_0(sK4)),sK5) = iProver_top ),
% 3.19/0.99      inference(superposition,[status(thm)],[c_1643,c_1868]) ).
% 3.19/0.99  
% 3.19/0.99  cnf(c_6640,plain,
% 3.19/0.99      ( u1_struct_0(sK4) = X0
% 3.19/0.99      | u1_struct_0(sK4) = sK5
% 3.19/0.99      | m1_subset_1(sK0(X0,u1_struct_0(sK4)),sK5) = iProver_top
% 3.19/0.99      | r2_hidden(sK0(X0,u1_struct_0(sK4)),X0) = iProver_top ),
% 3.19/0.99      inference(superposition,[status(thm)],[c_3371,c_1139]) ).
% 3.19/0.99  
% 3.19/0.99  cnf(c_7476,plain,
% 3.19/0.99      ( u1_struct_0(sK4) = X0
% 3.19/0.99      | u1_struct_0(sK4) = sK5
% 3.19/0.99      | m1_subset_1(sK0(X0,u1_struct_0(sK4)),X0) = iProver_top
% 3.19/0.99      | m1_subset_1(sK0(X0,u1_struct_0(sK4)),sK5) = iProver_top ),
% 3.19/0.99      inference(superposition,[status(thm)],[c_6640,c_1139]) ).
% 3.19/0.99  
% 3.19/0.99  cnf(c_11,plain,
% 3.19/0.99      ( r1_orders_2(X0,sK2(X0,X1),sK3(X0,X1))
% 3.19/0.99      | v13_waybel_0(X1,X0)
% 3.19/0.99      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
% 3.19/0.99      | ~ l1_orders_2(X0) ),
% 3.19/0.99      inference(cnf_transformation,[],[f61]) ).
% 3.19/0.99  
% 3.19/0.99  cnf(c_440,plain,
% 3.19/0.99      ( ~ v13_waybel_0(X0,X1)
% 3.19/0.99      | v13_waybel_0(X2,X3)
% 3.19/0.99      | ~ m1_subset_1(X4,u1_struct_0(X1))
% 3.19/0.99      | ~ m1_subset_1(X5,u1_struct_0(X1))
% 3.19/0.99      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X3)))
% 3.19/0.99      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 3.19/0.99      | ~ r2_hidden(X5,X0)
% 3.19/0.99      | r2_hidden(X4,X0)
% 3.19/0.99      | ~ l1_orders_2(X3)
% 3.19/0.99      | ~ l1_orders_2(X1)
% 3.19/0.99      | X1 != X3
% 3.19/0.99      | sK2(X3,X2) != X5
% 3.19/0.99      | sK3(X3,X2) != X4 ),
% 3.19/0.99      inference(resolution_lifted,[status(thm)],[c_11,c_15]) ).
% 3.19/0.99  
% 3.19/0.99  cnf(c_441,plain,
% 3.19/0.99      ( ~ v13_waybel_0(X0,X1)
% 3.19/0.99      | v13_waybel_0(X2,X1)
% 3.19/0.99      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
% 3.19/0.99      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 3.19/0.99      | ~ m1_subset_1(sK2(X1,X2),u1_struct_0(X1))
% 3.19/0.99      | ~ m1_subset_1(sK3(X1,X2),u1_struct_0(X1))
% 3.19/0.99      | ~ r2_hidden(sK2(X1,X2),X0)
% 3.19/0.99      | r2_hidden(sK3(X1,X2),X0)
% 3.19/0.99      | ~ l1_orders_2(X1) ),
% 3.19/0.99      inference(unflattening,[status(thm)],[c_440]) ).
% 3.19/0.99  
% 3.19/0.99  cnf(c_13,plain,
% 3.19/0.99      ( v13_waybel_0(X0,X1)
% 3.19/0.99      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 3.19/0.99      | m1_subset_1(sK3(X1,X0),u1_struct_0(X1))
% 3.19/0.99      | ~ l1_orders_2(X1) ),
% 3.19/0.99      inference(cnf_transformation,[],[f59]) ).
% 3.19/0.99  
% 3.19/0.99  cnf(c_7,plain,
% 3.19/0.99      ( m1_subset_1(X0,X1)
% 3.19/0.99      | ~ m1_subset_1(X2,k1_zfmisc_1(X1))
% 3.19/0.99      | ~ r2_hidden(X0,X2) ),
% 3.19/0.99      inference(cnf_transformation,[],[f54]) ).
% 3.19/0.99  
% 3.19/0.99  cnf(c_461,plain,
% 3.19/0.99      ( ~ v13_waybel_0(X0,X1)
% 3.19/0.99      | v13_waybel_0(X2,X1)
% 3.19/0.99      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 3.19/0.99      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
% 3.19/0.99      | ~ r2_hidden(sK2(X1,X2),X0)
% 3.19/0.99      | r2_hidden(sK3(X1,X2),X0)
% 3.19/0.99      | ~ l1_orders_2(X1) ),
% 3.19/0.99      inference(forward_subsumption_resolution,[status(thm)],[c_441,c_13,c_7]) ).
% 3.19/0.99  
% 3.19/0.99  cnf(c_518,plain,
% 3.19/0.99      ( ~ v13_waybel_0(X0,X1)
% 3.19/0.99      | v13_waybel_0(X2,X1)
% 3.19/0.99      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 3.19/0.99      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
% 3.19/0.99      | ~ r2_hidden(sK2(X1,X2),X0)
% 3.19/0.99      | r2_hidden(sK3(X1,X2),X0)
% 3.19/0.99      | sK4 != X1 ),
% 3.19/0.99      inference(resolution_lifted,[status(thm)],[c_461,c_23]) ).
% 3.19/0.99  
% 3.19/0.99  cnf(c_519,plain,
% 3.19/0.99      ( ~ v13_waybel_0(X0,sK4)
% 3.19/0.99      | v13_waybel_0(X1,sK4)
% 3.19/0.99      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK4)))
% 3.19/0.99      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK4)))
% 3.19/0.99      | ~ r2_hidden(sK2(sK4,X1),X0)
% 3.19/0.99      | r2_hidden(sK3(sK4,X1),X0) ),
% 3.19/0.99      inference(unflattening,[status(thm)],[c_518]) ).
% 3.19/0.99  
% 3.19/0.99  cnf(c_1128,plain,
% 3.19/0.99      ( v13_waybel_0(X0,sK4) != iProver_top
% 3.19/0.99      | v13_waybel_0(X1,sK4) = iProver_top
% 3.19/0.99      | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK4))) != iProver_top
% 3.19/0.99      | m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK4))) != iProver_top
% 3.19/0.99      | r2_hidden(sK2(sK4,X1),X0) != iProver_top
% 3.19/0.99      | r2_hidden(sK3(sK4,X1),X0) = iProver_top ),
% 3.19/0.99      inference(predicate_to_equality,[status(thm)],[c_519]) ).
% 3.19/0.99  
% 3.19/0.99  cnf(c_7907,plain,
% 3.19/0.99      ( u1_struct_0(sK4) = sK5
% 3.19/0.99      | k1_zfmisc_1(u1_struct_0(sK4)) = u1_struct_0(sK4)
% 3.19/0.99      | v13_waybel_0(X0,sK4) = iProver_top
% 3.19/0.99      | v13_waybel_0(sK0(k1_zfmisc_1(u1_struct_0(sK4)),u1_struct_0(sK4)),sK4) != iProver_top
% 3.19/0.99      | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK4))) != iProver_top
% 3.19/0.99      | m1_subset_1(sK0(k1_zfmisc_1(u1_struct_0(sK4)),u1_struct_0(sK4)),sK5) = iProver_top
% 3.19/0.99      | r2_hidden(sK2(sK4,X0),sK0(k1_zfmisc_1(u1_struct_0(sK4)),u1_struct_0(sK4))) != iProver_top
% 3.19/0.99      | r2_hidden(sK3(sK4,X0),sK0(k1_zfmisc_1(u1_struct_0(sK4)),u1_struct_0(sK4))) = iProver_top ),
% 3.19/0.99      inference(superposition,[status(thm)],[c_7476,c_1128]) ).
% 3.19/0.99  
% 3.19/0.99  cnf(c_22,negated_conjecture,
% 3.19/0.99      ( ~ v1_xboole_0(sK5) ),
% 3.19/0.99      inference(cnf_transformation,[],[f69]) ).
% 3.19/0.99  
% 3.19/0.99  cnf(c_31,plain,
% 3.19/0.99      ( v1_xboole_0(sK5) != iProver_top ),
% 3.19/0.99      inference(predicate_to_equality,[status(thm)],[c_22]) ).
% 3.19/0.99  
% 3.19/0.99  cnf(c_33,plain,
% 3.19/0.99      ( m1_subset_1(sK5,k1_zfmisc_1(u1_struct_0(sK4))) = iProver_top ),
% 3.19/0.99      inference(predicate_to_equality,[status(thm)],[c_20]) ).
% 3.19/0.99  
% 3.19/0.99  cnf(c_4,plain,
% 3.19/0.99      ( m1_subset_1(sK1(X0),k1_zfmisc_1(X0)) ),
% 3.19/0.99      inference(cnf_transformation,[],[f50]) ).
% 3.19/0.99  
% 3.19/0.99  cnf(c_1313,plain,
% 3.19/0.99      ( m1_subset_1(sK1(u1_struct_0(sK4)),k1_zfmisc_1(u1_struct_0(sK4))) ),
% 3.19/0.99      inference(instantiation,[status(thm)],[c_4]) ).
% 3.19/0.99  
% 3.19/0.99  cnf(c_1318,plain,
% 3.19/0.99      ( m1_subset_1(sK1(u1_struct_0(sK4)),k1_zfmisc_1(u1_struct_0(sK4))) = iProver_top ),
% 3.19/0.99      inference(predicate_to_equality,[status(thm)],[c_1313]) ).
% 3.19/0.99  
% 3.19/0.99  cnf(c_762,plain,( X0 = X0 ),theory(equality) ).
% 3.19/0.99  
% 3.19/0.99  cnf(c_1515,plain,
% 3.19/0.99      ( k1_zfmisc_1(u1_struct_0(sK4)) = k1_zfmisc_1(u1_struct_0(sK4)) ),
% 3.19/0.99      inference(instantiation,[status(thm)],[c_762]) ).
% 3.19/0.99  
% 3.19/0.99  cnf(c_511,plain,
% 3.19/0.99      ( m1_subset_1(k3_yellow_0(X0),u1_struct_0(X0)) | sK4 != X0 ),
% 3.19/0.99      inference(resolution_lifted,[status(thm)],[c_8,c_23]) ).
% 3.19/0.99  
% 3.19/0.99  cnf(c_512,plain,
% 3.19/0.99      ( m1_subset_1(k3_yellow_0(sK4),u1_struct_0(sK4)) ),
% 3.19/0.99      inference(unflattening,[status(thm)],[c_511]) ).
% 3.19/0.99  
% 3.19/0.99  cnf(c_1129,plain,
% 3.19/0.99      ( m1_subset_1(k3_yellow_0(sK4),u1_struct_0(sK4)) = iProver_top ),
% 3.19/0.99      inference(predicate_to_equality,[status(thm)],[c_512]) ).
% 3.19/0.99  
% 3.19/0.99  cnf(c_6,plain,
% 3.19/0.99      ( ~ m1_subset_1(X0,X1) | r2_hidden(X0,X1) | v1_xboole_0(X1) ),
% 3.19/0.99      inference(cnf_transformation,[],[f53]) ).
% 3.19/0.99  
% 3.19/0.99  cnf(c_1138,plain,
% 3.19/0.99      ( m1_subset_1(X0,X1) != iProver_top
% 3.19/0.99      | r2_hidden(X0,X1) = iProver_top
% 3.19/0.99      | v1_xboole_0(X1) = iProver_top ),
% 3.19/0.99      inference(predicate_to_equality,[status(thm)],[c_6]) ).
% 3.19/0.99  
% 3.19/0.99  cnf(c_1596,plain,
% 3.19/0.99      ( r2_hidden(k3_yellow_0(sK4),u1_struct_0(sK4)) = iProver_top
% 3.19/0.99      | v1_xboole_0(u1_struct_0(sK4)) = iProver_top ),
% 3.19/0.99      inference(superposition,[status(thm)],[c_1129,c_1138]) ).
% 3.19/0.99  
% 3.19/0.99  cnf(c_2,plain,
% 3.19/0.99      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
% 3.19/0.99      | ~ v1_xboole_0(X1)
% 3.19/0.99      | v1_xboole_0(X0) ),
% 3.19/0.99      inference(cnf_transformation,[],[f49]) ).
% 3.19/0.99  
% 3.19/0.99  cnf(c_1141,plain,
% 3.19/0.99      ( m1_subset_1(X0,k1_zfmisc_1(X1)) != iProver_top
% 3.19/0.99      | v1_xboole_0(X1) != iProver_top
% 3.19/0.99      | v1_xboole_0(X0) = iProver_top ),
% 3.19/0.99      inference(predicate_to_equality,[status(thm)],[c_2]) ).
% 3.19/0.99  
% 3.19/0.99  cnf(c_1635,plain,
% 3.19/0.99      ( v1_xboole_0(u1_struct_0(sK4)) != iProver_top
% 3.19/0.99      | v1_xboole_0(sK5) = iProver_top ),
% 3.19/0.99      inference(superposition,[status(thm)],[c_1136,c_1141]) ).
% 3.19/0.99  
% 3.19/0.99  cnf(c_0,plain,
% 3.19/0.99      ( ~ r2_hidden(sK0(X0,X1),X1) | ~ r2_hidden(sK0(X0,X1),X0) | X1 = X0 ),
% 3.19/0.99      inference(cnf_transformation,[],[f48]) ).
% 3.19/0.99  
% 3.19/0.99  cnf(c_1431,plain,
% 3.19/0.99      ( ~ r2_hidden(sK0(sK5,X0),X0) | ~ r2_hidden(sK0(sK5,X0),sK5) | X0 = sK5 ),
% 3.19/0.99      inference(instantiation,[status(thm)],[c_0]) ).
% 3.19/0.99  
% 3.19/0.99  cnf(c_2162,plain,
% 3.19/0.99      ( ~ r2_hidden(sK0(sK5,u1_struct_0(sK4)),u1_struct_0(sK4))
% 3.19/0.99      | ~ r2_hidden(sK0(sK5,u1_struct_0(sK4)),sK5)
% 3.19/0.99      | u1_struct_0(sK4) = sK5 ),
% 3.19/0.99      inference(instantiation,[status(thm)],[c_1431]) ).
% 3.19/0.99  
% 3.19/0.99  cnf(c_2166,plain,
% 3.19/0.99      ( u1_struct_0(sK4) = sK5
% 3.19/0.99      | r2_hidden(sK0(sK5,u1_struct_0(sK4)),u1_struct_0(sK4)) != iProver_top
% 3.19/0.99      | r2_hidden(sK0(sK5,u1_struct_0(sK4)),sK5) != iProver_top ),
% 3.19/0.99      inference(predicate_to_equality,[status(thm)],[c_2162]) ).
% 3.19/0.99  
% 3.19/0.99  cnf(c_3,plain,
% 3.19/0.99      ( ~ v1_subset_1(sK1(X0),X0) ),
% 3.19/0.99      inference(cnf_transformation,[],[f51]) ).
% 3.19/0.99  
% 3.19/0.99  cnf(c_379,plain,
% 3.19/0.99      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
% 3.19/0.99      | X1 != X2
% 3.19/0.99      | X1 = X0
% 3.19/0.99      | sK1(X2) != X0 ),
% 3.19/0.99      inference(resolution_lifted,[status(thm)],[c_3,c_16]) ).
% 3.19/0.99  
% 3.19/0.99  cnf(c_380,plain,
% 3.19/0.99      ( ~ m1_subset_1(sK1(X0),k1_zfmisc_1(X0)) | X0 = sK1(X0) ),
% 3.19/0.99      inference(unflattening,[status(thm)],[c_379]) ).
% 3.19/0.99  
% 3.19/0.99  cnf(c_384,plain,
% 3.19/0.99      ( X0 = sK1(X0) ),
% 3.19/0.99      inference(global_propositional_subsumption,[status(thm)],[c_380,c_4]) ).
% 3.19/0.99  
% 3.19/0.99  cnf(c_2593,plain,
% 3.19/0.99      ( u1_struct_0(sK4) = sK1(u1_struct_0(sK4)) ),
% 3.19/0.99      inference(instantiation,[status(thm)],[c_384]) ).
% 3.19/0.99  
% 3.19/0.99  cnf(c_1140,plain,
% 3.19/0.99      ( m1_subset_1(sK1(X0),k1_zfmisc_1(X0)) = iProver_top ),
% 3.19/0.99      inference(predicate_to_equality,[status(thm)],[c_4]) ).
% 3.19/0.99  
% 3.19/0.99  cnf(c_1154,plain,
% 3.19/0.99      ( m1_subset_1(X0,k1_zfmisc_1(X0)) = iProver_top ),
% 3.19/0.99      inference(light_normalisation,[status(thm)],[c_1140,c_384]) ).
% 3.19/0.99  
% 3.19/0.99  cnf(c_12,plain,
% 3.19/0.99      ( v13_waybel_0(X0,X1)
% 3.19/0.99      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 3.19/0.99      | r2_hidden(sK2(X1,X0),X0)
% 3.19/0.99      | ~ l1_orders_2(X1) ),
% 3.19/0.99      inference(cnf_transformation,[],[f60]) ).
% 3.19/0.99  
% 3.19/0.99  cnf(c_570,plain,
% 3.19/0.99      ( v13_waybel_0(X0,X1)
% 3.19/0.99      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 3.19/0.99      | r2_hidden(sK2(X1,X0),X0)
% 3.19/0.99      | sK4 != X1 ),
% 3.19/0.99      inference(resolution_lifted,[status(thm)],[c_12,c_23]) ).
% 3.19/0.99  
% 3.19/0.99  cnf(c_571,plain,
% 3.19/0.99      ( v13_waybel_0(X0,sK4)
% 3.19/0.99      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK4)))
% 3.19/0.99      | r2_hidden(sK2(sK4,X0),X0) ),
% 3.19/0.99      inference(unflattening,[status(thm)],[c_570]) ).
% 3.19/0.99  
% 3.19/0.99  cnf(c_1125,plain,
% 3.19/0.99      ( v13_waybel_0(X0,sK4) = iProver_top
% 3.19/0.99      | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK4))) != iProver_top
% 3.19/0.99      | r2_hidden(sK2(sK4,X0),X0) = iProver_top ),
% 3.19/0.99      inference(predicate_to_equality,[status(thm)],[c_571]) ).
% 3.19/0.99  
% 3.19/0.99  cnf(c_2075,plain,
% 3.19/0.99      ( v13_waybel_0(u1_struct_0(sK4),sK4) = iProver_top
% 3.19/0.99      | r2_hidden(sK2(sK4,u1_struct_0(sK4)),u1_struct_0(sK4)) = iProver_top ),
% 3.19/0.99      inference(superposition,[status(thm)],[c_1154,c_1125]) ).
% 3.19/0.99  
% 3.19/0.99  cnf(c_2261,plain,
% 3.19/0.99      ( v13_waybel_0(u1_struct_0(sK4),sK4) = iProver_top
% 3.19/0.99      | m1_subset_1(sK2(sK4,u1_struct_0(sK4)),u1_struct_0(sK4)) = iProver_top ),
% 3.19/0.99      inference(superposition,[status(thm)],[c_2075,c_1139]) ).
% 3.19/0.99  
% 3.19/0.99  cnf(c_555,plain,
% 3.19/0.99      ( v13_waybel_0(X0,X1)
% 3.19/0.99      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 3.19/0.99      | m1_subset_1(sK3(X1,X0),u1_struct_0(X1))
% 3.19/0.99      | sK4 != X1 ),
% 3.19/0.99      inference(resolution_lifted,[status(thm)],[c_13,c_23]) ).
% 3.19/0.99  
% 3.19/0.99  cnf(c_556,plain,
% 3.19/0.99      ( v13_waybel_0(X0,sK4)
% 3.19/0.99      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK4)))
% 3.19/0.99      | m1_subset_1(sK3(sK4,X0),u1_struct_0(sK4)) ),
% 3.19/0.99      inference(unflattening,[status(thm)],[c_555]) ).
% 3.19/0.99  
% 3.19/0.99  cnf(c_1126,plain,
% 3.19/0.99      ( v13_waybel_0(X0,sK4) = iProver_top
% 3.19/0.99      | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK4))) != iProver_top
% 3.19/0.99      | m1_subset_1(sK3(sK4,X0),u1_struct_0(sK4)) = iProver_top ),
% 3.19/0.99      inference(predicate_to_equality,[status(thm)],[c_556]) ).
% 3.19/0.99  
% 3.19/0.99  cnf(c_1598,plain,
% 3.19/0.99      ( v13_waybel_0(X0,sK4) = iProver_top
% 3.19/0.99      | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK4))) != iProver_top
% 3.19/0.99      | r2_hidden(sK3(sK4,X0),u1_struct_0(sK4)) = iProver_top
% 3.19/0.99      | v1_xboole_0(u1_struct_0(sK4)) = iProver_top ),
% 3.19/0.99      inference(superposition,[status(thm)],[c_1126,c_1138]) ).
% 3.19/0.99  
% 3.19/0.99  cnf(c_1854,plain,
% 3.19/0.99      ( r2_hidden(sK3(sK4,X0),u1_struct_0(sK4)) = iProver_top
% 3.19/0.99      | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK4))) != iProver_top
% 3.19/0.99      | v13_waybel_0(X0,sK4) = iProver_top ),
% 3.19/0.99      inference(global_propositional_subsumption,
% 3.19/0.99                [status(thm)],
% 3.19/0.99                [c_1598,c_31,c_1635]) ).
% 3.19/0.99  
% 3.19/0.99  cnf(c_1855,plain,
% 3.19/0.99      ( v13_waybel_0(X0,sK4) = iProver_top
% 3.19/0.99      | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK4))) != iProver_top
% 3.19/0.99      | r2_hidden(sK3(sK4,X0),u1_struct_0(sK4)) = iProver_top ),
% 3.19/0.99      inference(renaming,[status(thm)],[c_1854]) ).
% 3.19/0.99  
% 3.19/0.99  cnf(c_10,plain,
% 3.19/0.99      ( v13_waybel_0(X0,X1)
% 3.19/0.99      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 3.19/0.99      | ~ r2_hidden(sK3(X1,X0),X0)
% 3.19/0.99      | ~ l1_orders_2(X1) ),
% 3.19/0.99      inference(cnf_transformation,[],[f62]) ).
% 3.19/0.99  
% 3.19/0.99  cnf(c_585,plain,
% 3.19/0.99      ( v13_waybel_0(X0,X1)
% 3.19/0.99      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 3.19/0.99      | ~ r2_hidden(sK3(X1,X0),X0)
% 3.19/0.99      | sK4 != X1 ),
% 3.19/0.99      inference(resolution_lifted,[status(thm)],[c_10,c_23]) ).
% 3.19/0.99  
% 3.19/0.99  cnf(c_586,plain,
% 3.19/0.99      ( v13_waybel_0(X0,sK4)
% 3.19/0.99      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK4)))
% 3.19/0.99      | ~ r2_hidden(sK3(sK4,X0),X0) ),
% 3.19/0.99      inference(unflattening,[status(thm)],[c_585]) ).
% 3.19/0.99  
% 3.19/0.99  cnf(c_1124,plain,
% 3.19/0.99      ( v13_waybel_0(X0,sK4) = iProver_top
% 3.19/0.99      | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK4))) != iProver_top
% 3.19/0.99      | r2_hidden(sK3(sK4,X0),X0) != iProver_top ),
% 3.19/0.99      inference(predicate_to_equality,[status(thm)],[c_586]) ).
% 3.19/0.99  
% 3.19/0.99  cnf(c_2076,plain,
% 3.19/0.99      ( v13_waybel_0(u1_struct_0(sK4),sK4) = iProver_top
% 3.19/0.99      | r2_hidden(sK3(sK4,u1_struct_0(sK4)),u1_struct_0(sK4)) != iProver_top ),
% 3.19/0.99      inference(superposition,[status(thm)],[c_1154,c_1124]) ).
% 3.19/0.99  
% 3.19/0.99  cnf(c_2182,plain,
% 3.19/0.99      ( v13_waybel_0(u1_struct_0(sK4),sK4) = iProver_top
% 3.19/0.99      | m1_subset_1(u1_struct_0(sK4),k1_zfmisc_1(u1_struct_0(sK4))) != iProver_top ),
% 3.19/0.99      inference(superposition,[status(thm)],[c_1855,c_2076]) ).
% 3.19/0.99  
% 3.19/0.99  cnf(c_1534,plain,
% 3.19/0.99      ( v13_waybel_0(X0,sK4) = iProver_top
% 3.19/0.99      | v13_waybel_0(sK5,sK4) != iProver_top
% 3.19/0.99      | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK4))) != iProver_top
% 3.19/0.99      | r2_hidden(sK2(sK4,X0),sK5) != iProver_top
% 3.19/0.99      | r2_hidden(sK3(sK4,X0),sK5) = iProver_top ),
% 3.19/0.99      inference(superposition,[status(thm)],[c_1136,c_1128]) ).
% 3.19/0.99  
% 3.19/0.99  cnf(c_1678,plain,
% 3.19/0.99      ( v13_waybel_0(X0,sK4) = iProver_top
% 3.19/0.99      | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK4))) != iProver_top
% 3.19/0.99      | r2_hidden(sK2(sK4,X0),sK5) != iProver_top
% 3.19/0.99      | r2_hidden(sK3(sK4,X0),sK5) = iProver_top ),
% 3.19/0.99      inference(global_propositional_subsumption,[status(thm)],[c_1534,c_32]) ).
% 3.19/0.99  
% 3.19/0.99  cnf(c_2073,plain,
% 3.19/0.99      ( v13_waybel_0(u1_struct_0(sK4),sK4) = iProver_top
% 3.19/0.99      | r2_hidden(sK2(sK4,u1_struct_0(sK4)),sK5) != iProver_top
% 3.19/0.99      | r2_hidden(sK3(sK4,u1_struct_0(sK4)),sK5) = iProver_top ),
% 3.19/0.99      inference(superposition,[status(thm)],[c_1154,c_1678]) ).
% 3.19/0.99  
% 3.19/0.99  cnf(c_1137,plain,
% 3.19/0.99      ( m1_subset_1(X0,X1) = iProver_top
% 3.19/0.99      | m1_subset_1(X2,k1_zfmisc_1(X1)) != iProver_top
% 3.19/0.99      | r2_hidden(X0,X2) != iProver_top ),
% 3.19/0.99      inference(predicate_to_equality,[status(thm)],[c_7]) ).
% 3.19/0.99  
% 3.19/0.99  cnf(c_1999,plain,
% 3.19/0.99      ( m1_subset_1(X0,u1_struct_0(sK4)) = iProver_top
% 3.19/0.99      | r2_hidden(X0,sK5) != iProver_top ),
% 3.19/0.99      inference(superposition,[status(thm)],[c_1136,c_1137]) ).
% 3.19/0.99  
% 3.19/0.99  cnf(c_2175,plain,
% 3.19/0.99      ( r2_hidden(X0,u1_struct_0(sK4)) = iProver_top
% 3.19/0.99      | r2_hidden(X0,sK5) != iProver_top
% 3.19/0.99      | v1_xboole_0(u1_struct_0(sK4)) = iProver_top ),
% 3.19/0.99      inference(superposition,[status(thm)],[c_1999,c_1138]) ).
% 3.19/0.99  
% 3.19/0.99  cnf(c_2341,plain,
% 3.19/0.99      ( r2_hidden(X0,sK5) != iProver_top
% 3.19/0.99      | r2_hidden(X0,u1_struct_0(sK4)) = iProver_top ),
% 3.19/0.99      inference(global_propositional_subsumption,
% 3.19/0.99                [status(thm)],
% 3.19/0.99                [c_2175,c_31,c_1635]) ).
% 3.19/0.99  
% 3.19/0.99  cnf(c_2342,plain,
% 3.19/0.99      ( r2_hidden(X0,u1_struct_0(sK4)) = iProver_top
% 3.19/0.99      | r2_hidden(X0,sK5) != iProver_top ),
% 3.19/0.99      inference(renaming,[status(thm)],[c_2341]) ).
% 3.19/0.99  
% 3.19/0.99  cnf(c_2351,plain,
% 3.19/0.99      ( v13_waybel_0(u1_struct_0(sK4),sK4) = iProver_top
% 3.19/0.99      | r2_hidden(sK3(sK4,u1_struct_0(sK4)),sK5) != iProver_top ),
% 3.19/0.99      inference(superposition,[status(thm)],[c_2342,c_2076]) ).
% 3.19/0.99  
% 3.19/0.99  cnf(c_2367,plain,
% 3.19/0.99      ( r2_hidden(sK2(sK4,u1_struct_0(sK4)),sK5) != iProver_top
% 3.19/0.99      | v13_waybel_0(u1_struct_0(sK4),sK4) = iProver_top ),
% 3.19/0.99      inference(global_propositional_subsumption,[status(thm)],[c_2073,c_2351]) ).
% 3.19/0.99  
% 3.19/0.99  cnf(c_2368,plain,
% 3.19/0.99      ( v13_waybel_0(u1_struct_0(sK4),sK4) = iProver_top
% 3.19/0.99      | r2_hidden(sK2(sK4,u1_struct_0(sK4)),sK5) != iProver_top ),
% 3.19/0.99      inference(renaming,[status(thm)],[c_2367]) ).
% 3.19/0.99  
% 3.19/0.99  cnf(c_767,plain,
% 3.19/0.99      ( ~ m1_subset_1(X0,X1) | m1_subset_1(X2,X3) | X2 != X0 | X3 != X1 ),
% 3.19/0.99      theory(equality) ).
% 3.19/0.99  
% 3.19/0.99  cnf(c_1373,plain,
% 3.19/0.99      ( m1_subset_1(X0,X1)
% 3.19/0.99      | ~ m1_subset_1(sK5,k1_zfmisc_1(u1_struct_0(sK4)))
% 3.19/0.99      | X1 != k1_zfmisc_1(u1_struct_0(sK4))
% 3.19/0.99      | X0 != sK5 ),
% 3.19/0.99      inference(instantiation,[status(thm)],[c_767]) ).
% 3.19/0.99  
% 3.19/0.99  cnf(c_1514,plain,
% 3.19/0.99      ( m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK4)))
% 3.19/0.99      | ~ m1_subset_1(sK5,k1_zfmisc_1(u1_struct_0(sK4)))
% 3.19/0.99      | X0 != sK5
% 3.19/0.99      | k1_zfmisc_1(u1_struct_0(sK4)) != k1_zfmisc_1(u1_struct_0(sK4)) ),
% 3.19/0.99      inference(instantiation,[status(thm)],[c_1373]) ).
% 3.19/0.99  
% 3.19/0.99  cnf(c_2418,plain,
% 3.19/0.99      ( m1_subset_1(u1_struct_0(sK4),k1_zfmisc_1(u1_struct_0(sK4)))
% 3.19/0.99      | ~ m1_subset_1(sK5,k1_zfmisc_1(u1_struct_0(sK4)))
% 3.19/0.99      | u1_struct_0(sK4) != sK5
% 3.19/0.99      | k1_zfmisc_1(u1_struct_0(sK4)) != k1_zfmisc_1(u1_struct_0(sK4)) ),
% 3.19/0.99      inference(instantiation,[status(thm)],[c_1514]) ).
% 3.19/0.99  
% 3.19/0.99  cnf(c_2419,plain,
% 3.19/0.99      ( u1_struct_0(sK4) != sK5
% 3.19/0.99      | k1_zfmisc_1(u1_struct_0(sK4)) != k1_zfmisc_1(u1_struct_0(sK4))
% 3.19/0.99      | m1_subset_1(u1_struct_0(sK4),k1_zfmisc_1(u1_struct_0(sK4))) = iProver_top
% 3.19/0.99      | m1_subset_1(sK5,k1_zfmisc_1(u1_struct_0(sK4))) != iProver_top ),
% 3.19/0.99      inference(predicate_to_equality,[status(thm)],[c_2418]) ).
% 3.19/0.99  
% 3.19/0.99  cnf(c_14,plain,
% 3.19/0.99      ( v13_waybel_0(X0,X1)
% 3.19/0.99      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 3.19/0.99      | m1_subset_1(sK2(X1,X0),u1_struct_0(X1))
% 3.19/0.99      | ~ l1_orders_2(X1) ),
% 3.19/0.99      inference(cnf_transformation,[],[f58]) ).
% 3.19/0.99  
% 3.19/0.99  cnf(c_540,plain,
% 3.19/0.99      ( v13_waybel_0(X0,X1)
% 3.19/0.99      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 3.19/0.99      | m1_subset_1(sK2(X1,X0),u1_struct_0(X1))
% 3.19/0.99      | sK4 != X1 ),
% 3.19/0.99      inference(resolution_lifted,[status(thm)],[c_14,c_23]) ).
% 3.19/0.99  
% 3.19/0.99  cnf(c_541,plain,
% 3.19/0.99      ( v13_waybel_0(X0,sK4)
% 3.19/0.99      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK4)))
% 3.19/0.99      | m1_subset_1(sK2(sK4,X0),u1_struct_0(sK4)) ),
% 3.19/0.99      inference(unflattening,[status(thm)],[c_540]) ).
% 3.19/0.99  
% 3.19/0.99  cnf(c_1127,plain,
% 3.19/0.99      ( v13_waybel_0(X0,sK4) = iProver_top
% 3.19/0.99      | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK4))) != iProver_top
% 3.19/0.99      | m1_subset_1(sK2(sK4,X0),u1_struct_0(sK4)) = iProver_top ),
% 3.19/0.99      inference(predicate_to_equality,[status(thm)],[c_541]) ).
% 3.19/0.99  
% 3.19/0.99  cnf(c_2269,plain,
% 3.19/0.99      ( u1_struct_0(sK4) = sK5
% 3.19/0.99      | v13_waybel_0(X0,sK4) = iProver_top
% 3.19/0.99      | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK4))) != iProver_top
% 3.19/0.99      | r2_hidden(sK2(sK4,X0),sK5) = iProver_top ),
% 3.19/0.99      inference(superposition,[status(thm)],[c_1127,c_1868]) ).
% 3.19/0.99  
% 3.19/0.99  cnf(c_2550,plain,
% 3.19/0.99      ( u1_struct_0(sK4) = sK5
% 3.19/0.99      | v13_waybel_0(u1_struct_0(sK4),sK4) = iProver_top
% 3.19/0.99      | r2_hidden(sK2(sK4,u1_struct_0(sK4)),sK5) = iProver_top ),
% 3.19/0.99      inference(superposition,[status(thm)],[c_1154,c_2269]) ).
% 3.19/0.99  
% 3.19/0.99  cnf(c_3110,plain,
% 3.19/0.99      ( v13_waybel_0(u1_struct_0(sK4),sK4) = iProver_top ),
% 3.19/0.99      inference(global_propositional_subsumption,
% 3.19/0.99                [status(thm)],
% 3.19/0.99                [c_2261,c_33,c_1515,c_2182,c_2368,c_2419,c_2550]) ).
% 3.19/0.99  
% 3.19/0.99  cnf(c_1368,plain,
% 3.19/0.99      ( m1_subset_1(X0,X1)
% 3.19/0.99      | ~ m1_subset_1(sK1(X2),k1_zfmisc_1(X2))
% 3.19/0.99      | X0 != sK1(X2)
% 3.19/0.99      | X1 != k1_zfmisc_1(X2) ),
% 3.19/0.99      inference(instantiation,[status(thm)],[c_767]) ).
% 3.19/0.99  
% 3.19/0.99  cnf(c_1699,plain,
% 3.19/0.99      ( m1_subset_1(X0,k1_zfmisc_1(X1))
% 3.19/0.99      | ~ m1_subset_1(sK1(X1),k1_zfmisc_1(X1))
% 3.19/0.99      | X0 != sK1(X1)
% 3.19/0.99      | k1_zfmisc_1(X1) != k1_zfmisc_1(X1) ),
% 3.19/0.99      inference(instantiation,[status(thm)],[c_1368]) ).
% 3.19/0.99  
% 3.19/0.99  cnf(c_1985,plain,
% 3.19/0.99      ( m1_subset_1(u1_struct_0(sK4),k1_zfmisc_1(X0))
% 3.19/0.99      | ~ m1_subset_1(sK1(X0),k1_zfmisc_1(X0))
% 3.19/0.99      | u1_struct_0(sK4) != sK1(X0)
% 3.19/0.99      | k1_zfmisc_1(X0) != k1_zfmisc_1(X0) ),
% 3.19/0.99      inference(instantiation,[status(thm)],[c_1699]) ).
% 3.19/0.99  
% 3.19/0.99  cnf(c_4521,plain,
% 3.19/0.99      ( m1_subset_1(u1_struct_0(sK4),k1_zfmisc_1(u1_struct_0(sK4)))
% 3.19/0.99      | ~ m1_subset_1(sK1(u1_struct_0(sK4)),k1_zfmisc_1(u1_struct_0(sK4)))
% 3.19/0.99      | u1_struct_0(sK4) != sK1(u1_struct_0(sK4))
% 3.19/0.99      | k1_zfmisc_1(u1_struct_0(sK4)) != k1_zfmisc_1(u1_struct_0(sK4)) ),
% 3.19/0.99      inference(instantiation,[status(thm)],[c_1985]) ).
% 3.19/0.99  
% 3.19/0.99  cnf(c_4522,plain,
% 3.19/0.99      ( u1_struct_0(sK4) != sK1(u1_struct_0(sK4))
% 3.19/0.99      | k1_zfmisc_1(u1_struct_0(sK4)) != k1_zfmisc_1(u1_struct_0(sK4))
% 3.19/0.99      | m1_subset_1(u1_struct_0(sK4),k1_zfmisc_1(u1_struct_0(sK4))) = iProver_top
% 3.19/0.99      | m1_subset_1(sK1(u1_struct_0(sK4)),k1_zfmisc_1(u1_struct_0(sK4))) != iProver_top ),
% 3.19/0.99      inference(predicate_to_equality,[status(thm)],[c_4521]) ).
% 3.19/0.99  
% 3.19/0.99  cnf(c_1422,plain,
% 3.19/0.99      ( m1_subset_1(X0,X1)
% 3.19/0.99      | ~ m1_subset_1(sK5,k1_zfmisc_1(X1))
% 3.19/0.99      | ~ r2_hidden(X0,sK5) ),
% 3.19/0.99      inference(instantiation,[status(thm)],[c_7]) ).
% 3.19/0.99  
% 3.19/0.99  cnf(c_5353,plain,
% 3.19/0.99      ( m1_subset_1(sK0(sK5,u1_struct_0(sK4)),u1_struct_0(sK4))
% 3.19/0.99      | ~ m1_subset_1(sK5,k1_zfmisc_1(u1_struct_0(sK4)))
% 3.19/0.99      | ~ r2_hidden(sK0(sK5,u1_struct_0(sK4)),sK5) ),
% 3.19/0.99      inference(instantiation,[status(thm)],[c_1422]) ).
% 3.19/0.99  
% 3.19/0.99  cnf(c_5359,plain,
% 3.19/0.99      ( m1_subset_1(sK0(sK5,u1_struct_0(sK4)),u1_struct_0(sK4)) = iProver_top
% 3.19/0.99      | m1_subset_1(sK5,k1_zfmisc_1(u1_struct_0(sK4))) != iProver_top
% 3.19/0.99      | r2_hidden(sK0(sK5,u1_struct_0(sK4)),sK5) != iProver_top ),
% 3.19/0.99      inference(predicate_to_equality,[status(thm)],[c_5353]) ).
% 3.19/0.99  
% 3.19/0.99  cnf(c_6649,plain,
% 3.19/0.99      ( u1_struct_0(sK4) = sK5
% 3.19/0.99      | r2_hidden(sK0(sK5,u1_struct_0(sK4)),sK5) = iProver_top
% 3.19/0.99      | iProver_top != iProver_top ),
% 3.19/0.99      inference(equality_factoring,[status(thm)],[c_3371]) ).
% 3.19/0.99  
% 3.19/0.99  cnf(c_6651,plain,
% 3.19/0.99      ( u1_struct_0(sK4) = sK5
% 3.19/0.99      | r2_hidden(sK0(sK5,u1_struct_0(sK4)),sK5) = iProver_top ),
% 3.19/0.99      inference(equality_resolution_simp,[status(thm)],[c_6649]) ).
% 3.19/0.99  
% 3.19/0.99  cnf(c_4801,plain,
% 3.19/0.99      ( ~ v13_waybel_0(u1_struct_0(sK4),sK4)
% 3.19/0.99      | ~ m1_subset_1(sK0(X0,u1_struct_0(sK4)),u1_struct_0(sK4))
% 3.19/0.99      | ~ m1_subset_1(u1_struct_0(sK4),k1_zfmisc_1(u1_struct_0(sK4)))
% 3.19/0.99      | r2_hidden(sK0(X0,u1_struct_0(sK4)),u1_struct_0(sK4))
% 3.19/0.99      | ~ r2_hidden(k3_yellow_0(sK4),u1_struct_0(sK4)) ),
% 3.19/0.99      inference(instantiation,[status(thm)],[c_476]) ).
% 3.19/0.99  
% 3.19/0.99  cnf(c_8540,plain,
% 3.19/0.99      ( ~ v13_waybel_0(u1_struct_0(sK4),sK4)
% 3.19/0.99      | ~ m1_subset_1(sK0(sK5,u1_struct_0(sK4)),u1_struct_0(sK4))
% 3.19/0.99      | ~ m1_subset_1(u1_struct_0(sK4),k1_zfmisc_1(u1_struct_0(sK4)))
% 3.19/0.99      | r2_hidden(sK0(sK5,u1_struct_0(sK4)),u1_struct_0(sK4))
% 3.19/0.99      | ~ r2_hidden(k3_yellow_0(sK4),u1_struct_0(sK4)) ),
% 3.19/0.99      inference(instantiation,[status(thm)],[c_4801]) ).
% 3.19/0.99  
% 3.19/0.99  cnf(c_8541,plain,
% 3.19/0.99      ( v13_waybel_0(u1_struct_0(sK4),sK4) != iProver_top
% 3.19/0.99      | m1_subset_1(sK0(sK5,u1_struct_0(sK4)),u1_struct_0(sK4)) != iProver_top
% 3.19/0.99      | m1_subset_1(u1_struct_0(sK4),k1_zfmisc_1(u1_struct_0(sK4))) != iProver_top
% 3.19/0.99      | r2_hidden(sK0(sK5,u1_struct_0(sK4)),u1_struct_0(sK4)) = iProver_top
% 3.19/0.99      | r2_hidden(k3_yellow_0(sK4),u1_struct_0(sK4)) != iProver_top ),
% 3.19/0.99      inference(predicate_to_equality,[status(thm)],[c_8540]) ).
% 3.19/0.99  
% 3.19/0.99  cnf(c_8544,plain,
% 3.19/0.99      ( u1_struct_0(sK4) = sK5 ),
% 3.19/0.99      inference(global_propositional_subsumption,
% 3.19/0.99                [status(thm)],
% 3.19/0.99                [c_7907,c_31,c_33,c_1318,c_1515,c_1596,c_1635,c_2166,c_2182,
% 3.19/0.99                 c_2368,c_2419,c_2550,c_2593,c_4522,c_5359,c_6651,c_8541]) ).
% 3.19/0.99  
% 3.19/0.99  cnf(c_19,negated_conjecture,
% 3.19/0.99      ( v1_subset_1(sK5,u1_struct_0(sK4)) | ~ r2_hidden(k3_yellow_0(sK4),sK5) ),
% 3.19/0.99      inference(cnf_transformation,[],[f72]) ).
% 3.19/0.99  
% 3.19/0.99  cnf(c_199,plain,
% 3.19/0.99      ( v1_subset_1(sK5,u1_struct_0(sK4)) | ~ r2_hidden(k3_yellow_0(sK4),sK5) ),
% 3.19/0.99      inference(prop_impl,[status(thm)],[c_19]) ).
% 3.19/0.99  
% 3.19/0.99  cnf(c_390,plain,
% 3.19/0.99      ( ~ r2_hidden(k3_yellow_0(sK4),sK5)
% 3.19/0.99      | u1_struct_0(sK4) != X0
% 3.19/0.99      | sK1(X0) != sK5 ),
% 3.19/0.99      inference(resolution_lifted,[status(thm)],[c_3,c_199]) ).
% 3.19/0.99  
% 3.19/0.99  cnf(c_391,plain,
% 3.19/0.99      ( ~ r2_hidden(k3_yellow_0(sK4),sK5) | sK1(u1_struct_0(sK4)) != sK5 ),
% 3.19/0.99      inference(unflattening,[status(thm)],[c_390]) ).
% 3.19/0.99  
% 3.19/0.99  cnf(c_1133,plain,
% 3.19/0.99      ( sK1(u1_struct_0(sK4)) != sK5
% 3.19/0.99      | r2_hidden(k3_yellow_0(sK4),sK5) != iProver_top ),
% 3.19/0.99      inference(predicate_to_equality,[status(thm)],[c_391]) ).
% 3.19/0.99  
% 3.19/0.99  cnf(c_1165,plain,
% 3.19/0.99      ( u1_struct_0(sK4) != sK5
% 3.19/0.99      | r2_hidden(k3_yellow_0(sK4),sK5) != iProver_top ),
% 3.19/0.99      inference(demodulation,[status(thm)],[c_1133,c_384]) ).
% 3.19/0.99  
% 3.19/0.99  cnf(c_8581,plain,
% 3.19/0.99      ( sK5 != sK5 | r2_hidden(k3_yellow_0(sK4),sK5) != iProver_top ),
% 3.19/0.99      inference(demodulation,[status(thm)],[c_8544,c_1165]) ).
% 3.19/0.99  
% 3.19/0.99  cnf(c_8686,plain,
% 3.19/0.99      ( r2_hidden(k3_yellow_0(sK4),sK5) != iProver_top ),
% 3.19/0.99      inference(equality_resolution_simp,[status(thm)],[c_8581]) ).
% 3.19/0.99  
% 3.19/0.99  cnf(c_1764,plain,
% 3.19/0.99      ( r2_hidden(k3_yellow_0(sK4),u1_struct_0(sK4)) = iProver_top ),
% 3.19/0.99      inference(global_propositional_subsumption,
% 3.19/0.99                [status(thm)],
% 3.19/0.99                [c_1596,c_31,c_1635]) ).
% 3.19/0.99  
% 3.19/0.99  cnf(c_8586,plain,
% 3.19/0.99      ( r2_hidden(k3_yellow_0(sK4),sK5) = iProver_top ),
% 3.19/0.99      inference(demodulation,[status(thm)],[c_8544,c_1764]) ).
% 3.19/0.99  
% 3.19/0.99  cnf(c_8688,plain,
% 3.19/0.99      ( $false ),
% 3.19/0.99      inference(forward_subsumption_resolution,[status(thm)],[c_8686,c_8586]) ).
% 3.19/0.99  
% 3.19/0.99  
% 3.19/0.99  % SZS output end CNFRefutation for theBenchmark.p
% 3.19/0.99  
% 3.19/0.99  ------                               Statistics
% 3.19/0.99  
% 3.19/0.99  ------ General
% 3.19/0.99  
% 3.19/0.99  abstr_ref_over_cycles:                  0
% 3.19/0.99  abstr_ref_under_cycles:                 0
% 3.19/0.99  gc_basic_clause_elim:                   0
% 3.19/0.99  forced_gc_time:                         0
% 3.19/0.99  parsing_time:                           0.01
% 3.19/0.99  unif_index_cands_time:                  0.
% 3.19/0.99  unif_index_add_time:                    0.
% 3.19/0.99  orderings_time:                         0.
% 3.19/0.99  out_proof_time:                         0.014
% 3.19/0.99  total_time:                             0.259
% 3.19/0.99  num_of_symbols:                         50
% 3.19/0.99  num_of_terms:                           4640
% 3.19/0.99  
% 3.19/0.99  ------ Preprocessing
% 3.19/0.99  
% 3.19/0.99  num_of_splits:                          0
% 3.19/0.99  num_of_split_atoms:                     0
% 3.19/0.99  num_of_reused_defs:                     0
% 3.19/0.99  num_eq_ax_congr_red:                    16
% 3.19/0.99  num_of_sem_filtered_clauses:            1
% 3.19/0.99  num_of_subtypes:                        0
% 3.19/0.99  monotx_restored_types:                  0
% 3.19/0.99  sat_num_of_epr_types:                   0
% 3.19/0.99  sat_num_of_non_cyclic_types:            0
% 3.19/0.99  sat_guarded_non_collapsed_types:        0
% 3.19/0.99  num_pure_diseq_elim:                    0
% 3.19/0.99  simp_replaced_by:                       0
% 3.19/0.99  res_preprocessed:                       115
% 3.19/0.99  prep_upred:                             0
% 3.19/0.99  prep_unflattend:                        21
% 3.19/0.99  smt_new_axioms:                         0
% 3.19/0.99  pred_elim_cands:                        4
% 3.19/0.99  pred_elim:                              6
% 3.19/0.99  pred_elim_cl:                           6
% 3.19/0.99  pred_elim_cycles:                       8
% 3.19/0.99  merged_defs:                            2
% 3.19/0.99  merged_defs_ncl:                        0
% 3.19/0.99  bin_hyper_res:                          2
% 3.19/0.99  prep_cycles:                            4
% 3.19/0.99  pred_elim_time:                         0.006
% 3.19/0.99  splitting_time:                         0.
% 3.19/0.99  sem_filter_time:                        0.
% 3.19/0.99  monotx_time:                            0.001
% 3.19/0.99  subtype_inf_time:                       0.
% 3.19/0.99  
% 3.19/0.99  ------ Problem properties
% 3.19/0.99  
% 3.19/0.99  clauses:                                21
% 3.19/0.99  conjectures:                            3
% 3.19/0.99  epr:                                    4
% 3.19/0.99  horn:                                   14
% 3.19/0.99  ground:                                 7
% 3.19/0.99  unary:                                  6
% 3.19/0.99  binary:                                 3
% 3.19/0.99  lits:                                   53
% 3.19/0.99  lits_eq:                                6
% 3.19/0.99  fd_pure:                                0
% 3.19/0.99  fd_pseudo:                              0
% 3.19/0.99  fd_cond:                                0
% 3.19/0.99  fd_pseudo_cond:                         2
% 3.19/0.99  ac_symbols:                             0
% 3.19/0.99  
% 3.19/0.99  ------ Propositional Solver
% 3.19/0.99  
% 3.19/0.99  prop_solver_calls:                      29
% 3.19/0.99  prop_fast_solver_calls:                 1049
% 3.19/0.99  smt_solver_calls:                       0
% 3.19/0.99  smt_fast_solver_calls:                  0
% 3.19/0.99  prop_num_of_clauses:                    2837
% 3.19/0.99  prop_preprocess_simplified:             6175
% 3.19/0.99  prop_fo_subsumed:                       29
% 3.19/0.99  prop_solver_time:                       0.
% 3.19/0.99  smt_solver_time:                        0.
% 3.19/0.99  smt_fast_solver_time:                   0.
% 3.19/0.99  prop_fast_solver_time:                  0.
% 3.19/0.99  prop_unsat_core_time:                   0.
% 3.19/0.99  
% 3.19/0.99  ------ QBF
% 3.19/0.99  
% 3.19/0.99  qbf_q_res:                              0
% 3.19/0.99  qbf_num_tautologies:                    0
% 3.19/0.99  qbf_prep_cycles:                        0
% 3.19/0.99  
% 3.19/0.99  ------ BMC1
% 3.19/0.99  
% 3.19/0.99  bmc1_current_bound:                     -1
% 3.19/0.99  bmc1_last_solved_bound:                 -1
% 3.19/0.99  bmc1_unsat_core_size:                   -1
% 3.19/0.99  bmc1_unsat_core_parents_size:           -1
% 3.19/0.99  bmc1_merge_next_fun:                    0
% 3.19/0.99  bmc1_unsat_core_clauses_time:           0.
% 3.19/0.99  
% 3.19/0.99  ------ Instantiation
% 3.19/0.99  
% 3.19/0.99  inst_num_of_clauses:                    705
% 3.19/0.99  inst_num_in_passive:                    240
% 3.19/0.99  inst_num_in_active:                     337
% 3.19/0.99  inst_num_in_unprocessed:                128
% 3.19/0.99  inst_num_of_loops:                      470
% 3.19/0.99  inst_num_of_learning_restarts:          0
% 3.19/0.99  inst_num_moves_active_passive:          130
% 3.19/0.99  inst_lit_activity:                      0
% 3.19/0.99  inst_lit_activity_moves:                0
% 3.19/0.99  inst_num_tautologies:                   0
% 3.19/0.99  inst_num_prop_implied:                  0
% 3.19/0.99  inst_num_existing_simplified:           0
% 3.19/0.99  inst_num_eq_res_simplified:             0
% 3.19/0.99  inst_num_child_elim:                    0
% 3.19/0.99  inst_num_of_dismatching_blockings:      293
% 3.19/0.99  inst_num_of_non_proper_insts:           596
% 3.19/0.99  inst_num_of_duplicates:                 0
% 3.19/0.99  inst_inst_num_from_inst_to_res:         0
% 3.19/0.99  inst_dismatching_checking_time:         0.
% 3.19/0.99  
% 3.19/0.99  ------ Resolution
% 3.19/0.99  
% 3.19/0.99  res_num_of_clauses:                     0
% 3.19/0.99  res_num_in_passive:                     0
% 3.19/0.99  res_num_in_active:                      0
% 3.19/0.99  res_num_of_loops:                       119
% 3.19/0.99  res_forward_subset_subsumed:            25
% 3.19/0.99  res_backward_subset_subsumed:           0
% 3.19/0.99  res_forward_subsumed:                   0
% 3.19/0.99  res_backward_subsumed:                  0
% 3.19/0.99  res_forward_subsumption_resolution:     2
% 3.19/0.99  res_backward_subsumption_resolution:    0
% 3.19/0.99  res_clause_to_clause_subsumption:       2190
% 3.19/0.99  res_orphan_elimination:                 0
% 3.19/0.99  res_tautology_del:                      38
% 3.19/0.99  res_num_eq_res_simplified:              0
% 3.19/0.99  res_num_sel_changes:                    0
% 3.19/0.99  res_moves_from_active_to_pass:          0
% 3.19/0.99  
% 3.19/0.99  ------ Superposition
% 3.19/0.99  
% 3.19/0.99  sup_time_total:                         0.
% 3.19/0.99  sup_time_generating:                    0.
% 3.19/0.99  sup_time_sim_full:                      0.
% 3.19/0.99  sup_time_sim_immed:                     0.
% 3.19/0.99  
% 3.19/0.99  sup_num_of_clauses:                     101
% 3.19/0.99  sup_num_in_active:                      23
% 3.19/0.99  sup_num_in_passive:                     78
% 3.19/0.99  sup_num_of_loops:                       92
% 3.19/0.99  sup_fw_superposition:                   108
% 3.19/0.99  sup_bw_superposition:                   213
% 3.19/0.99  sup_immediate_simplified:               44
% 3.19/0.99  sup_given_eliminated:                   0
% 3.19/0.99  comparisons_done:                       0
% 3.19/0.99  comparisons_avoided:                    3
% 3.19/0.99  
% 3.19/0.99  ------ Simplifications
% 3.19/0.99  
% 3.19/0.99  
% 3.19/0.99  sim_fw_subset_subsumed:                 19
% 3.19/0.99  sim_bw_subset_subsumed:                 61
% 3.19/0.99  sim_fw_subsumed:                        21
% 3.19/0.99  sim_bw_subsumed:                        4
% 3.19/0.99  sim_fw_subsumption_res:                 2
% 3.19/0.99  sim_bw_subsumption_res:                 5
% 3.19/0.99  sim_tautology_del:                      57
% 3.19/0.99  sim_eq_tautology_del:                   12
% 3.19/0.99  sim_eq_res_simp:                        5
% 3.19/0.99  sim_fw_demodulated:                     1
% 3.19/0.99  sim_bw_demodulated:                     52
% 3.19/0.99  sim_light_normalised:                   1
% 3.19/0.99  sim_joinable_taut:                      0
% 3.19/0.99  sim_joinable_simp:                      0
% 3.19/0.99  sim_ac_normalised:                      0
% 3.19/0.99  sim_smt_subsumption:                    0
% 3.19/0.99  
%------------------------------------------------------------------------------
