%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n001.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:28:24 EST 2020

% Result     : Theorem 3.69s
% Output     : CNFRefutation 3.69s
% Verified   : 
% Statistics : Number of formulae       :  164 ( 488 expanded)
%              Number of clauses        :   96 ( 150 expanded)
%              Number of leaves         :   22 (  98 expanded)
%              Depth                    :   27
%              Number of atoms          :  622 (3436 expanded)
%              Number of equality atoms :  142 ( 233 expanded)
%              Maximal formula depth    :   14 (   5 average)
%              Maximal clause size      :   22 (   3 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f1,axiom,(
    ! [X0,X1] :
      ( ! [X2] :
          ( r2_hidden(X2,X0)
        <=> r2_hidden(X2,X1) )
     => X0 = X1 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f17,plain,(
    ! [X0,X1] :
      ( X0 = X1
      | ? [X2] :
          ( r2_hidden(X2,X0)
        <~> r2_hidden(X2,X1) ) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f32,plain,(
    ! [X0,X1] :
      ( X0 = X1
      | ? [X2] :
          ( ( ~ r2_hidden(X2,X1)
            | ~ r2_hidden(X2,X0) )
          & ( r2_hidden(X2,X1)
            | r2_hidden(X2,X0) ) ) ) ),
    inference(nnf_transformation,[],[f17])).

fof(f33,plain,(
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

fof(f34,plain,(
    ! [X0,X1] :
      ( X0 = X1
      | ( ( ~ r2_hidden(sK0(X0,X1),X1)
          | ~ r2_hidden(sK0(X0,X1),X0) )
        & ( r2_hidden(sK0(X0,X1),X1)
          | r2_hidden(sK0(X0,X1),X0) ) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f32,f33])).

fof(f46,plain,(
    ! [X0,X1] :
      ( X0 = X1
      | r2_hidden(sK0(X0,X1),X1)
      | r2_hidden(sK0(X0,X1),X0) ) ),
    inference(cnf_transformation,[],[f34])).

fof(f5,axiom,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
     => m1_subset_1(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f19,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X0,X1)
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f51,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X0,X1)
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f11,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => ( v1_subset_1(X1,X0)
      <=> X0 != X1 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f29,plain,(
    ! [X0,X1] :
      ( ( v1_subset_1(X1,X0)
      <=> X0 != X1 )
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f40,plain,(
    ! [X0,X1] :
      ( ( ( v1_subset_1(X1,X0)
          | X0 = X1 )
        & ( X0 != X1
          | ~ v1_subset_1(X1,X0) ) )
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(nnf_transformation,[],[f29])).

fof(f63,plain,(
    ! [X0,X1] :
      ( v1_subset_1(X1,X0)
      | X0 = X1
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f40])).

fof(f12,conjecture,(
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

fof(f13,negated_conjecture,(
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
    inference(negated_conjecture,[],[f12])).

fof(f14,plain,(
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
    inference(pure_predicate_removal,[],[f13])).

fof(f15,plain,(
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
    inference(pure_predicate_removal,[],[f14])).

fof(f16,plain,(
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
    inference(pure_predicate_removal,[],[f15])).

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
    inference(ennf_transformation,[],[f16])).

fof(f31,plain,(
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
    inference(flattening,[],[f30])).

fof(f41,plain,(
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
    inference(nnf_transformation,[],[f31])).

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
    inference(flattening,[],[f41])).

fof(f44,plain,(
    ! [X0] :
      ( ? [X1] :
          ( ( r2_hidden(k3_yellow_0(X0),X1)
            | ~ v1_subset_1(X1,u1_struct_0(X0)) )
          & ( ~ r2_hidden(k3_yellow_0(X0),X1)
            | v1_subset_1(X1,u1_struct_0(X0)) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
          & v13_waybel_0(X1,X0)
          & ~ v1_xboole_0(X1) )
     => ( ( r2_hidden(k3_yellow_0(X0),sK4)
          | ~ v1_subset_1(sK4,u1_struct_0(X0)) )
        & ( ~ r2_hidden(k3_yellow_0(X0),sK4)
          | v1_subset_1(sK4,u1_struct_0(X0)) )
        & m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(X0)))
        & v13_waybel_0(sK4,X0)
        & ~ v1_xboole_0(sK4) ) ) ),
    introduced(choice_axiom,[])).

fof(f43,plain,
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
          ( ( r2_hidden(k3_yellow_0(sK3),X1)
            | ~ v1_subset_1(X1,u1_struct_0(sK3)) )
          & ( ~ r2_hidden(k3_yellow_0(sK3),X1)
            | v1_subset_1(X1,u1_struct_0(sK3)) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK3)))
          & v13_waybel_0(X1,sK3)
          & ~ v1_xboole_0(X1) )
      & l1_orders_2(sK3)
      & v1_yellow_0(sK3)
      & v5_orders_2(sK3)
      & ~ v2_struct_0(sK3) ) ),
    introduced(choice_axiom,[])).

fof(f45,plain,
    ( ( r2_hidden(k3_yellow_0(sK3),sK4)
      | ~ v1_subset_1(sK4,u1_struct_0(sK3)) )
    & ( ~ r2_hidden(k3_yellow_0(sK3),sK4)
      | v1_subset_1(sK4,u1_struct_0(sK3)) )
    & m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(sK3)))
    & v13_waybel_0(sK4,sK3)
    & ~ v1_xboole_0(sK4)
    & l1_orders_2(sK3)
    & v1_yellow_0(sK3)
    & v5_orders_2(sK3)
    & ~ v2_struct_0(sK3) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3,sK4])],[f42,f44,f43])).

fof(f72,plain,
    ( r2_hidden(k3_yellow_0(sK3),sK4)
    | ~ v1_subset_1(sK4,u1_struct_0(sK3)) ),
    inference(cnf_transformation,[],[f45])).

fof(f70,plain,(
    m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(sK3))) ),
    inference(cnf_transformation,[],[f45])).

fof(f67,plain,(
    l1_orders_2(sK3) ),
    inference(cnf_transformation,[],[f45])).

fof(f8,axiom,(
    ! [X0] :
      ( l1_orders_2(X0)
     => m1_subset_1(k3_yellow_0(X0),u1_struct_0(X0)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f24,plain,(
    ! [X0] :
      ( m1_subset_1(k3_yellow_0(X0),u1_struct_0(X0))
      | ~ l1_orders_2(X0) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f54,plain,(
    ! [X0] :
      ( m1_subset_1(k3_yellow_0(X0),u1_struct_0(X0))
      | ~ l1_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f6,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,X1)
     => ( r2_hidden(X0,X1)
        | v1_xboole_0(X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f20,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
      | v1_xboole_0(X1)
      | ~ m1_subset_1(X0,X1) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f21,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
      | v1_xboole_0(X1)
      | ~ m1_subset_1(X0,X1) ) ),
    inference(flattening,[],[f20])).

fof(f52,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
      | v1_xboole_0(X1)
      | ~ m1_subset_1(X0,X1) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f68,plain,(
    ~ v1_xboole_0(sK4) ),
    inference(cnf_transformation,[],[f45])).

fof(f10,axiom,(
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
    inference(ennf_transformation,[],[f10])).

fof(f28,plain,(
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
    inference(flattening,[],[f27])).

fof(f35,plain,(
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
    inference(nnf_transformation,[],[f28])).

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
    inference(rectify,[],[f35])).

fof(f38,plain,(
    ! [X2,X1,X0] :
      ( ? [X3] :
          ( ~ r2_hidden(X3,X1)
          & r1_orders_2(X0,X2,X3)
          & r2_hidden(X2,X1)
          & m1_subset_1(X3,u1_struct_0(X0)) )
     => ( ~ r2_hidden(sK2(X0,X1),X1)
        & r1_orders_2(X0,X2,sK2(X0,X1))
        & r2_hidden(X2,X1)
        & m1_subset_1(sK2(X0,X1),u1_struct_0(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f37,plain,(
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
            & r1_orders_2(X0,sK1(X0,X1),X3)
            & r2_hidden(sK1(X0,X1),X1)
            & m1_subset_1(X3,u1_struct_0(X0)) )
        & m1_subset_1(sK1(X0,X1),u1_struct_0(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f39,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ( v13_waybel_0(X1,X0)
              | ( ~ r2_hidden(sK2(X0,X1),X1)
                & r1_orders_2(X0,sK1(X0,X1),sK2(X0,X1))
                & r2_hidden(sK1(X0,X1),X1)
                & m1_subset_1(sK2(X0,X1),u1_struct_0(X0))
                & m1_subset_1(sK1(X0,X1),u1_struct_0(X0)) ) )
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
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1,sK2])],[f36,f38,f37])).

fof(f56,plain,(
    ! [X4,X0,X5,X1] :
      ( r2_hidden(X5,X1)
      | ~ r1_orders_2(X0,X4,X5)
      | ~ r2_hidden(X4,X1)
      | ~ m1_subset_1(X5,u1_struct_0(X0))
      | ~ m1_subset_1(X4,u1_struct_0(X0))
      | ~ v13_waybel_0(X1,X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f39])).

fof(f9,axiom,(
    ! [X0] :
      ( ( l1_orders_2(X0)
        & v1_yellow_0(X0)
        & v5_orders_2(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,u1_struct_0(X0))
         => r1_orders_2(X0,k3_yellow_0(X0),X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f25,plain,(
    ! [X0] :
      ( ! [X1] :
          ( r1_orders_2(X0,k3_yellow_0(X0),X1)
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l1_orders_2(X0)
      | ~ v1_yellow_0(X0)
      | ~ v5_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f26,plain,(
    ! [X0] :
      ( ! [X1] :
          ( r1_orders_2(X0,k3_yellow_0(X0),X1)
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l1_orders_2(X0)
      | ~ v1_yellow_0(X0)
      | ~ v5_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f25])).

fof(f55,plain,(
    ! [X0,X1] :
      ( r1_orders_2(X0,k3_yellow_0(X0),X1)
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | ~ v1_yellow_0(X0)
      | ~ v5_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f66,plain,(
    v1_yellow_0(sK3) ),
    inference(cnf_transformation,[],[f45])).

fof(f64,plain,(
    ~ v2_struct_0(sK3) ),
    inference(cnf_transformation,[],[f45])).

fof(f65,plain,(
    v5_orders_2(sK3) ),
    inference(cnf_transformation,[],[f45])).

fof(f69,plain,(
    v13_waybel_0(sK4,sK3) ),
    inference(cnf_transformation,[],[f45])).

fof(f47,plain,(
    ! [X0,X1] :
      ( X0 = X1
      | ~ r2_hidden(sK0(X0,X1),X1)
      | ~ r2_hidden(sK0(X0,X1),X0) ) ),
    inference(cnf_transformation,[],[f34])).

fof(f7,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(X2))
        & r2_hidden(X0,X1) )
     => m1_subset_1(X0,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f22,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X0,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f23,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X0,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(flattening,[],[f22])).

fof(f53,plain,(
    ! [X2,X0,X1] :
      ( m1_subset_1(X0,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f4,axiom,(
    ! [X0] :
      ( v1_xboole_0(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(X0))
         => v1_xboole_0(X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f18,plain,(
    ! [X0] :
      ( ! [X1] :
          ( v1_xboole_0(X1)
          | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) )
      | ~ v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f50,plain,(
    ! [X0,X1] :
      ( v1_xboole_0(X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | ~ v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f62,plain,(
    ! [X0,X1] :
      ( X0 != X1
      | ~ v1_subset_1(X1,X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f40])).

fof(f73,plain,(
    ! [X1] :
      ( ~ v1_subset_1(X1,X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X1)) ) ),
    inference(equality_resolution,[],[f62])).

fof(f71,plain,
    ( ~ r2_hidden(k3_yellow_0(sK3),sK4)
    | v1_subset_1(sK4,u1_struct_0(sK3)) ),
    inference(cnf_transformation,[],[f45])).

fof(f3,axiom,(
    ! [X0] : m1_subset_1(k2_subset_1(X0),k1_zfmisc_1(X0)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f49,plain,(
    ! [X0] : m1_subset_1(k2_subset_1(X0),k1_zfmisc_1(X0)) ),
    inference(cnf_transformation,[],[f3])).

fof(f2,axiom,(
    ! [X0] : k2_subset_1(X0) = X0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f48,plain,(
    ! [X0] : k2_subset_1(X0) = X0 ),
    inference(cnf_transformation,[],[f2])).

cnf(c_1,plain,
    ( r2_hidden(sK0(X0,X1),X1)
    | r2_hidden(sK0(X0,X1),X0)
    | X1 = X0 ),
    inference(cnf_transformation,[],[f46])).

cnf(c_1104,plain,
    ( X0 = X1
    | r2_hidden(sK0(X1,X0),X0) = iProver_top
    | r2_hidden(sK0(X1,X0),X1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1])).

cnf(c_5,plain,
    ( m1_subset_1(X0,X1)
    | ~ r2_hidden(X0,X1) ),
    inference(cnf_transformation,[],[f51])).

cnf(c_1101,plain,
    ( m1_subset_1(X0,X1) = iProver_top
    | r2_hidden(X0,X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_5])).

cnf(c_2463,plain,
    ( X0 = X1
    | m1_subset_1(sK0(X0,X1),X0) = iProver_top
    | r2_hidden(sK0(X0,X1),X1) = iProver_top ),
    inference(superposition,[status(thm)],[c_1104,c_1101])).

cnf(c_16,plain,
    ( v1_subset_1(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | X0 = X1 ),
    inference(cnf_transformation,[],[f63])).

cnf(c_18,negated_conjecture,
    ( ~ v1_subset_1(sK4,u1_struct_0(sK3))
    | r2_hidden(k3_yellow_0(sK3),sK4) ),
    inference(cnf_transformation,[],[f72])).

cnf(c_195,plain,
    ( ~ v1_subset_1(sK4,u1_struct_0(sK3))
    | r2_hidden(k3_yellow_0(sK3),sK4) ),
    inference(prop_impl,[status(thm)],[c_18])).

cnf(c_372,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | r2_hidden(k3_yellow_0(sK3),sK4)
    | X1 = X0
    | u1_struct_0(sK3) != X1
    | sK4 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_16,c_195])).

cnf(c_373,plain,
    ( ~ m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(sK3)))
    | r2_hidden(k3_yellow_0(sK3),sK4)
    | u1_struct_0(sK3) = sK4 ),
    inference(unflattening,[status(thm)],[c_372])).

cnf(c_20,negated_conjecture,
    ( m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(sK3))) ),
    inference(cnf_transformation,[],[f70])).

cnf(c_375,plain,
    ( r2_hidden(k3_yellow_0(sK3),sK4)
    | u1_struct_0(sK3) = sK4 ),
    inference(global_propositional_subsumption,[status(thm)],[c_373,c_20])).

cnf(c_1095,plain,
    ( u1_struct_0(sK3) = sK4
    | r2_hidden(k3_yellow_0(sK3),sK4) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_375])).

cnf(c_2402,plain,
    ( u1_struct_0(sK3) = sK4
    | m1_subset_1(k3_yellow_0(sK3),sK4) = iProver_top ),
    inference(superposition,[status(thm)],[c_1095,c_1101])).

cnf(c_23,negated_conjecture,
    ( l1_orders_2(sK3) ),
    inference(cnf_transformation,[],[f67])).

cnf(c_30,plain,
    ( l1_orders_2(sK3) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_23])).

cnf(c_8,plain,
    ( m1_subset_1(k3_yellow_0(X0),u1_struct_0(X0))
    | ~ l1_orders_2(X0) ),
    inference(cnf_transformation,[],[f54])).

cnf(c_61,plain,
    ( m1_subset_1(k3_yellow_0(X0),u1_struct_0(X0)) = iProver_top
    | l1_orders_2(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_8])).

cnf(c_63,plain,
    ( m1_subset_1(k3_yellow_0(sK3),u1_struct_0(sK3)) = iProver_top
    | l1_orders_2(sK3) != iProver_top ),
    inference(instantiation,[status(thm)],[c_61])).

cnf(c_726,plain,
    ( X0 != X1
    | k3_yellow_0(X0) = k3_yellow_0(X1) ),
    theory(equality)).

cnf(c_735,plain,
    ( k3_yellow_0(sK3) = k3_yellow_0(sK3)
    | sK3 != sK3 ),
    inference(instantiation,[status(thm)],[c_726])).

cnf(c_720,plain,
    ( X0 = X0 ),
    theory(equality)).

cnf(c_741,plain,
    ( sK3 = sK3 ),
    inference(instantiation,[status(thm)],[c_720])).

cnf(c_1449,plain,
    ( sK4 = sK4 ),
    inference(instantiation,[status(thm)],[c_720])).

cnf(c_724,plain,
    ( ~ m1_subset_1(X0,X1)
    | m1_subset_1(X2,X3)
    | X2 != X0
    | X3 != X1 ),
    theory(equality)).

cnf(c_1381,plain,
    ( m1_subset_1(X0,X1)
    | ~ m1_subset_1(k3_yellow_0(sK3),u1_struct_0(sK3))
    | X1 != u1_struct_0(sK3)
    | X0 != k3_yellow_0(sK3) ),
    inference(instantiation,[status(thm)],[c_724])).

cnf(c_1549,plain,
    ( m1_subset_1(k3_yellow_0(X0),X1)
    | ~ m1_subset_1(k3_yellow_0(sK3),u1_struct_0(sK3))
    | X1 != u1_struct_0(sK3)
    | k3_yellow_0(X0) != k3_yellow_0(sK3) ),
    inference(instantiation,[status(thm)],[c_1381])).

cnf(c_1852,plain,
    ( m1_subset_1(k3_yellow_0(X0),sK4)
    | ~ m1_subset_1(k3_yellow_0(sK3),u1_struct_0(sK3))
    | k3_yellow_0(X0) != k3_yellow_0(sK3)
    | sK4 != u1_struct_0(sK3) ),
    inference(instantiation,[status(thm)],[c_1549])).

cnf(c_1863,plain,
    ( k3_yellow_0(X0) != k3_yellow_0(sK3)
    | sK4 != u1_struct_0(sK3)
    | m1_subset_1(k3_yellow_0(X0),sK4) = iProver_top
    | m1_subset_1(k3_yellow_0(sK3),u1_struct_0(sK3)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1852])).

cnf(c_1865,plain,
    ( k3_yellow_0(sK3) != k3_yellow_0(sK3)
    | sK4 != u1_struct_0(sK3)
    | m1_subset_1(k3_yellow_0(sK3),u1_struct_0(sK3)) != iProver_top
    | m1_subset_1(k3_yellow_0(sK3),sK4) = iProver_top ),
    inference(instantiation,[status(thm)],[c_1863])).

cnf(c_721,plain,
    ( X0 != X1
    | X2 != X1
    | X2 = X0 ),
    theory(equality)).

cnf(c_1391,plain,
    ( u1_struct_0(sK3) != X0
    | sK4 != X0
    | sK4 = u1_struct_0(sK3) ),
    inference(instantiation,[status(thm)],[c_721])).

cnf(c_3308,plain,
    ( u1_struct_0(sK3) != sK4
    | sK4 = u1_struct_0(sK3)
    | sK4 != sK4 ),
    inference(instantiation,[status(thm)],[c_1391])).

cnf(c_3475,plain,
    ( m1_subset_1(k3_yellow_0(sK3),sK4) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_2402,c_30,c_63,c_735,c_741,c_1449,c_1865,c_3308])).

cnf(c_6,plain,
    ( ~ m1_subset_1(X0,X1)
    | r2_hidden(X0,X1)
    | v1_xboole_0(X1) ),
    inference(cnf_transformation,[],[f52])).

cnf(c_1100,plain,
    ( m1_subset_1(X0,X1) != iProver_top
    | r2_hidden(X0,X1) = iProver_top
    | v1_xboole_0(X1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_6])).

cnf(c_3480,plain,
    ( r2_hidden(k3_yellow_0(sK3),sK4) = iProver_top
    | v1_xboole_0(sK4) = iProver_top ),
    inference(superposition,[status(thm)],[c_3475,c_1100])).

cnf(c_22,negated_conjecture,
    ( ~ v1_xboole_0(sK4) ),
    inference(cnf_transformation,[],[f68])).

cnf(c_31,plain,
    ( v1_xboole_0(sK4) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_22])).

cnf(c_3740,plain,
    ( r2_hidden(k3_yellow_0(sK3),sK4) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_3480,c_31])).

cnf(c_1098,plain,
    ( m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(sK3))) = iProver_top ),
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
    inference(cnf_transformation,[],[f56])).

cnf(c_9,plain,
    ( r1_orders_2(X0,k3_yellow_0(X0),X1)
    | ~ m1_subset_1(X1,u1_struct_0(X0))
    | v2_struct_0(X0)
    | ~ v5_orders_2(X0)
    | ~ v1_yellow_0(X0)
    | ~ l1_orders_2(X0) ),
    inference(cnf_transformation,[],[f55])).

cnf(c_24,negated_conjecture,
    ( v1_yellow_0(sK3) ),
    inference(cnf_transformation,[],[f66])).

cnf(c_348,plain,
    ( r1_orders_2(X0,k3_yellow_0(X0),X1)
    | ~ m1_subset_1(X1,u1_struct_0(X0))
    | v2_struct_0(X0)
    | ~ v5_orders_2(X0)
    | ~ l1_orders_2(X0)
    | sK3 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_9,c_24])).

cnf(c_349,plain,
    ( r1_orders_2(sK3,k3_yellow_0(sK3),X0)
    | ~ m1_subset_1(X0,u1_struct_0(sK3))
    | v2_struct_0(sK3)
    | ~ v5_orders_2(sK3)
    | ~ l1_orders_2(sK3) ),
    inference(unflattening,[status(thm)],[c_348])).

cnf(c_26,negated_conjecture,
    ( ~ v2_struct_0(sK3) ),
    inference(cnf_transformation,[],[f64])).

cnf(c_25,negated_conjecture,
    ( v5_orders_2(sK3) ),
    inference(cnf_transformation,[],[f65])).

cnf(c_353,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(sK3))
    | r1_orders_2(sK3,k3_yellow_0(sK3),X0) ),
    inference(global_propositional_subsumption,[status(thm)],[c_349,c_26,c_25,c_23])).

cnf(c_354,plain,
    ( r1_orders_2(sK3,k3_yellow_0(sK3),X0)
    | ~ m1_subset_1(X0,u1_struct_0(sK3)) ),
    inference(renaming,[status(thm)],[c_353])).

cnf(c_436,plain,
    ( ~ v13_waybel_0(X0,X1)
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ m1_subset_1(X3,u1_struct_0(X1))
    | ~ m1_subset_1(X4,u1_struct_0(sK3))
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ r2_hidden(X2,X0)
    | r2_hidden(X3,X0)
    | ~ l1_orders_2(X1)
    | X4 != X3
    | k3_yellow_0(sK3) != X2
    | sK3 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_15,c_354])).

cnf(c_437,plain,
    ( ~ v13_waybel_0(X0,sK3)
    | ~ m1_subset_1(X1,u1_struct_0(sK3))
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK3)))
    | ~ m1_subset_1(k3_yellow_0(sK3),u1_struct_0(sK3))
    | r2_hidden(X1,X0)
    | ~ r2_hidden(k3_yellow_0(sK3),X0)
    | ~ l1_orders_2(sK3) ),
    inference(unflattening,[status(thm)],[c_436])).

cnf(c_62,plain,
    ( m1_subset_1(k3_yellow_0(sK3),u1_struct_0(sK3))
    | ~ l1_orders_2(sK3) ),
    inference(instantiation,[status(thm)],[c_8])).

cnf(c_441,plain,
    ( ~ r2_hidden(k3_yellow_0(sK3),X0)
    | r2_hidden(X1,X0)
    | ~ v13_waybel_0(X0,sK3)
    | ~ m1_subset_1(X1,u1_struct_0(sK3))
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK3))) ),
    inference(global_propositional_subsumption,[status(thm)],[c_437,c_23,c_62])).

cnf(c_442,plain,
    ( ~ v13_waybel_0(X0,sK3)
    | ~ m1_subset_1(X1,u1_struct_0(sK3))
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK3)))
    | r2_hidden(X1,X0)
    | ~ r2_hidden(k3_yellow_0(sK3),X0) ),
    inference(renaming,[status(thm)],[c_441])).

cnf(c_1093,plain,
    ( v13_waybel_0(X0,sK3) != iProver_top
    | m1_subset_1(X1,u1_struct_0(sK3)) != iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK3))) != iProver_top
    | r2_hidden(X1,X0) = iProver_top
    | r2_hidden(k3_yellow_0(sK3),X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_442])).

cnf(c_2081,plain,
    ( v13_waybel_0(sK4,sK3) != iProver_top
    | m1_subset_1(X0,u1_struct_0(sK3)) != iProver_top
    | r2_hidden(X0,sK4) = iProver_top
    | r2_hidden(k3_yellow_0(sK3),sK4) != iProver_top ),
    inference(superposition,[status(thm)],[c_1098,c_1093])).

cnf(c_21,negated_conjecture,
    ( v13_waybel_0(sK4,sK3) ),
    inference(cnf_transformation,[],[f69])).

cnf(c_32,plain,
    ( v13_waybel_0(sK4,sK3) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_21])).

cnf(c_2105,plain,
    ( m1_subset_1(X0,u1_struct_0(sK3)) != iProver_top
    | r2_hidden(X0,sK4) = iProver_top
    | r2_hidden(k3_yellow_0(sK3),sK4) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_2081,c_32])).

cnf(c_3746,plain,
    ( m1_subset_1(X0,u1_struct_0(sK3)) != iProver_top
    | r2_hidden(X0,sK4) = iProver_top ),
    inference(superposition,[status(thm)],[c_3740,c_2105])).

cnf(c_4351,plain,
    ( u1_struct_0(sK3) = X0
    | r2_hidden(sK0(u1_struct_0(sK3),X0),X0) = iProver_top
    | r2_hidden(sK0(u1_struct_0(sK3),X0),sK4) = iProver_top ),
    inference(superposition,[status(thm)],[c_2463,c_3746])).

cnf(c_9056,plain,
    ( u1_struct_0(sK3) = sK4
    | r2_hidden(sK0(u1_struct_0(sK3),sK4),sK4) = iProver_top
    | iProver_top != iProver_top ),
    inference(equality_factoring,[status(thm)],[c_4351])).

cnf(c_9058,plain,
    ( u1_struct_0(sK3) = sK4
    | r2_hidden(sK0(u1_struct_0(sK3),sK4),sK4) = iProver_top ),
    inference(equality_resolution_simp,[status(thm)],[c_9056])).

cnf(c_1454,plain,
    ( X0 != X1
    | X0 = sK4
    | sK4 != X1 ),
    inference(instantiation,[status(thm)],[c_721])).

cnf(c_2839,plain,
    ( u1_struct_0(sK3) != X0
    | u1_struct_0(sK3) = sK4
    | sK4 != X0 ),
    inference(instantiation,[status(thm)],[c_1454])).

cnf(c_7255,plain,
    ( u1_struct_0(sK3) != u1_struct_0(sK3)
    | u1_struct_0(sK3) = sK4
    | sK4 != u1_struct_0(sK3) ),
    inference(instantiation,[status(thm)],[c_2839])).

cnf(c_0,plain,
    ( ~ r2_hidden(sK0(X0,X1),X1)
    | ~ r2_hidden(sK0(X0,X1),X0)
    | X1 = X0 ),
    inference(cnf_transformation,[],[f47])).

cnf(c_7,plain,
    ( m1_subset_1(X0,X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(X1))
    | ~ r2_hidden(X0,X2) ),
    inference(cnf_transformation,[],[f53])).

cnf(c_2499,plain,
    ( m1_subset_1(X0,u1_struct_0(sK3))
    | ~ r2_hidden(X0,sK4) ),
    inference(resolution,[status(thm)],[c_7,c_20])).

cnf(c_2622,plain,
    ( r2_hidden(X0,u1_struct_0(sK3))
    | ~ r2_hidden(X0,sK4)
    | v1_xboole_0(u1_struct_0(sK3)) ),
    inference(resolution,[status(thm)],[c_2499,c_6])).

cnf(c_4,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | ~ v1_xboole_0(X1)
    | v1_xboole_0(X0) ),
    inference(cnf_transformation,[],[f50])).

cnf(c_1102,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(X1)) != iProver_top
    | v1_xboole_0(X1) != iProver_top
    | v1_xboole_0(X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_4])).

cnf(c_2453,plain,
    ( v1_xboole_0(u1_struct_0(sK3)) != iProver_top
    | v1_xboole_0(sK4) = iProver_top ),
    inference(superposition,[status(thm)],[c_1098,c_1102])).

cnf(c_2458,plain,
    ( ~ v1_xboole_0(u1_struct_0(sK3))
    | v1_xboole_0(sK4) ),
    inference(predicate_to_equality_rev,[status(thm)],[c_2453])).

cnf(c_2627,plain,
    ( ~ r2_hidden(X0,sK4)
    | r2_hidden(X0,u1_struct_0(sK3)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_2622,c_22,c_2458])).

cnf(c_2628,plain,
    ( r2_hidden(X0,u1_struct_0(sK3))
    | ~ r2_hidden(X0,sK4) ),
    inference(renaming,[status(thm)],[c_2627])).

cnf(c_3533,plain,
    ( ~ r2_hidden(sK0(u1_struct_0(sK3),X0),X0)
    | ~ r2_hidden(sK0(u1_struct_0(sK3),X0),sK4)
    | X0 = u1_struct_0(sK3) ),
    inference(resolution,[status(thm)],[c_0,c_2628])).

cnf(c_3792,plain,
    ( r2_hidden(sK0(u1_struct_0(sK3),sK4),u1_struct_0(sK3))
    | ~ r2_hidden(sK0(u1_struct_0(sK3),sK4),sK4)
    | sK4 = u1_struct_0(sK3) ),
    inference(resolution,[status(thm)],[c_3533,c_1])).

cnf(c_3300,plain,
    ( ~ r2_hidden(sK0(u1_struct_0(sK3),sK4),u1_struct_0(sK3))
    | ~ r2_hidden(sK0(u1_struct_0(sK3),sK4),sK4)
    | sK4 = u1_struct_0(sK3) ),
    inference(instantiation,[status(thm)],[c_0])).

cnf(c_4237,plain,
    ( ~ r2_hidden(sK0(u1_struct_0(sK3),sK4),sK4)
    | sK4 = u1_struct_0(sK3) ),
    inference(global_propositional_subsumption,[status(thm)],[c_3792,c_3300])).

cnf(c_4239,plain,
    ( sK4 = u1_struct_0(sK3)
    | r2_hidden(sK0(u1_struct_0(sK3),sK4),sK4) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_4237])).

cnf(c_17,plain,
    ( ~ v1_subset_1(X0,X0)
    | ~ m1_subset_1(X0,k1_zfmisc_1(X0)) ),
    inference(cnf_transformation,[],[f73])).

cnf(c_19,negated_conjecture,
    ( v1_subset_1(sK4,u1_struct_0(sK3))
    | ~ r2_hidden(k3_yellow_0(sK3),sK4) ),
    inference(cnf_transformation,[],[f71])).

cnf(c_193,plain,
    ( v1_subset_1(sK4,u1_struct_0(sK3))
    | ~ r2_hidden(k3_yellow_0(sK3),sK4) ),
    inference(prop_impl,[status(thm)],[c_19])).

cnf(c_386,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X0))
    | ~ r2_hidden(k3_yellow_0(sK3),sK4)
    | u1_struct_0(sK3) != X0
    | sK4 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_17,c_193])).

cnf(c_387,plain,
    ( ~ m1_subset_1(u1_struct_0(sK3),k1_zfmisc_1(u1_struct_0(sK3)))
    | ~ r2_hidden(k3_yellow_0(sK3),sK4)
    | sK4 != u1_struct_0(sK3) ),
    inference(unflattening,[status(thm)],[c_386])).

cnf(c_1094,plain,
    ( sK4 != u1_struct_0(sK3)
    | m1_subset_1(u1_struct_0(sK3),k1_zfmisc_1(u1_struct_0(sK3))) != iProver_top
    | r2_hidden(k3_yellow_0(sK3),sK4) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_387])).

cnf(c_3,plain,
    ( m1_subset_1(k2_subset_1(X0),k1_zfmisc_1(X0)) ),
    inference(cnf_transformation,[],[f49])).

cnf(c_1103,plain,
    ( m1_subset_1(k2_subset_1(X0),k1_zfmisc_1(X0)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3])).

cnf(c_2,plain,
    ( k2_subset_1(X0) = X0 ),
    inference(cnf_transformation,[],[f48])).

cnf(c_1116,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(X0)) = iProver_top ),
    inference(light_normalisation,[status(thm)],[c_1103,c_2])).

cnf(c_1184,plain,
    ( u1_struct_0(sK3) != sK4
    | r2_hidden(k3_yellow_0(sK3),sK4) != iProver_top ),
    inference(forward_subsumption_resolution,[status(thm)],[c_1094,c_1116])).

cnf(c_727,plain,
    ( X0 != X1
    | u1_struct_0(X0) = u1_struct_0(X1) ),
    theory(equality)).

cnf(c_736,plain,
    ( u1_struct_0(sK3) = u1_struct_0(sK3)
    | sK3 != sK3 ),
    inference(instantiation,[status(thm)],[c_727])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_9058,c_7255,c_4239,c_3480,c_1184,c_741,c_736,c_31])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.12  % Command    : iproveropt_run.sh %d %s
% 0.13/0.33  % Computer   : n001.cluster.edu
% 0.13/0.33  % Model      : x86_64 x86_64
% 0.13/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.33  % Memory     : 8042.1875MB
% 0.13/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.33  % CPULimit   : 60
% 0.13/0.33  % WCLimit    : 600
% 0.13/0.33  % DateTime   : Tue Dec  1 09:48:14 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running in FOF mode
% 3.69/0.99  % SZS status Started for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.69/0.99  
% 3.69/0.99  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 3.69/0.99  
% 3.69/0.99  ------  iProver source info
% 3.69/0.99  
% 3.69/0.99  git: date: 2020-06-30 10:37:57 +0100
% 3.69/0.99  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 3.69/0.99  git: non_committed_changes: false
% 3.69/0.99  git: last_make_outside_of_git: false
% 3.69/0.99  
% 3.69/0.99  ------ 
% 3.69/0.99  ------ Parsing...
% 3.69/0.99  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 3.69/0.99  
% 3.69/0.99  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe:1:0s pe:2:0s pe:4:0s pe_e  sf_s  rm: 7 0s  sf_e  pe_s  pe_e 
% 3.69/0.99  
% 3.69/0.99  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 3.69/0.99  
% 3.69/0.99  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 3.69/0.99  ------ Proving...
% 3.69/0.99  ------ Problem Properties 
% 3.69/0.99  
% 3.69/0.99  
% 3.69/0.99  clauses                                 20
% 3.69/0.99  conjectures                             3
% 3.69/0.99  EPR                                     4
% 3.69/0.99  Horn                                    13
% 3.69/0.99  unary                                   6
% 3.69/0.99  binary                                  2
% 3.69/0.99  lits                                    51
% 3.69/0.99  lits eq                                 5
% 3.69/0.99  fd_pure                                 0
% 3.69/0.99  fd_pseudo                               0
% 3.69/0.99  fd_cond                                 0
% 3.69/0.99  fd_pseudo_cond                          2
% 3.69/0.99  AC symbols                              0
% 3.69/0.99  
% 3.69/0.99  ------ Input Options Time Limit: Unbounded
% 3.69/0.99  
% 3.69/0.99  
% 3.69/0.99  ------ 
% 3.69/0.99  Current options:
% 3.69/0.99  ------ 
% 3.69/0.99  
% 3.69/0.99  
% 3.69/0.99  
% 3.69/0.99  
% 3.69/0.99  ------ Proving...
% 3.69/0.99  
% 3.69/0.99  
% 3.69/0.99  % SZS status Theorem for theBenchmark.p
% 3.69/0.99  
% 3.69/0.99  % SZS output start CNFRefutation for theBenchmark.p
% 3.69/0.99  
% 3.69/0.99  fof(f1,axiom,(
% 3.69/0.99    ! [X0,X1] : (! [X2] : (r2_hidden(X2,X0) <=> r2_hidden(X2,X1)) => X0 = X1)),
% 3.69/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.69/0.99  
% 3.69/0.99  fof(f17,plain,(
% 3.69/0.99    ! [X0,X1] : (X0 = X1 | ? [X2] : (r2_hidden(X2,X0) <~> r2_hidden(X2,X1)))),
% 3.69/0.99    inference(ennf_transformation,[],[f1])).
% 3.69/0.99  
% 3.69/0.99  fof(f32,plain,(
% 3.69/0.99    ! [X0,X1] : (X0 = X1 | ? [X2] : ((~r2_hidden(X2,X1) | ~r2_hidden(X2,X0)) & (r2_hidden(X2,X1) | r2_hidden(X2,X0))))),
% 3.69/0.99    inference(nnf_transformation,[],[f17])).
% 3.69/0.99  
% 3.69/0.99  fof(f33,plain,(
% 3.69/0.99    ! [X1,X0] : (? [X2] : ((~r2_hidden(X2,X1) | ~r2_hidden(X2,X0)) & (r2_hidden(X2,X1) | r2_hidden(X2,X0))) => ((~r2_hidden(sK0(X0,X1),X1) | ~r2_hidden(sK0(X0,X1),X0)) & (r2_hidden(sK0(X0,X1),X1) | r2_hidden(sK0(X0,X1),X0))))),
% 3.69/0.99    introduced(choice_axiom,[])).
% 3.69/0.99  
% 3.69/0.99  fof(f34,plain,(
% 3.69/0.99    ! [X0,X1] : (X0 = X1 | ((~r2_hidden(sK0(X0,X1),X1) | ~r2_hidden(sK0(X0,X1),X0)) & (r2_hidden(sK0(X0,X1),X1) | r2_hidden(sK0(X0,X1),X0))))),
% 3.69/0.99    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f32,f33])).
% 3.69/0.99  
% 3.69/0.99  fof(f46,plain,(
% 3.69/0.99    ( ! [X0,X1] : (X0 = X1 | r2_hidden(sK0(X0,X1),X1) | r2_hidden(sK0(X0,X1),X0)) )),
% 3.69/0.99    inference(cnf_transformation,[],[f34])).
% 3.69/0.99  
% 3.69/0.99  fof(f5,axiom,(
% 3.69/0.99    ! [X0,X1] : (r2_hidden(X0,X1) => m1_subset_1(X0,X1))),
% 3.69/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.69/0.99  
% 3.69/0.99  fof(f19,plain,(
% 3.69/0.99    ! [X0,X1] : (m1_subset_1(X0,X1) | ~r2_hidden(X0,X1))),
% 3.69/0.99    inference(ennf_transformation,[],[f5])).
% 3.69/0.99  
% 3.69/0.99  fof(f51,plain,(
% 3.69/0.99    ( ! [X0,X1] : (m1_subset_1(X0,X1) | ~r2_hidden(X0,X1)) )),
% 3.69/0.99    inference(cnf_transformation,[],[f19])).
% 3.69/0.99  
% 3.69/0.99  fof(f11,axiom,(
% 3.69/0.99    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => (v1_subset_1(X1,X0) <=> X0 != X1))),
% 3.69/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.69/0.99  
% 3.69/0.99  fof(f29,plain,(
% 3.69/0.99    ! [X0,X1] : ((v1_subset_1(X1,X0) <=> X0 != X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 3.69/0.99    inference(ennf_transformation,[],[f11])).
% 3.69/0.99  
% 3.69/0.99  fof(f40,plain,(
% 3.69/0.99    ! [X0,X1] : (((v1_subset_1(X1,X0) | X0 = X1) & (X0 != X1 | ~v1_subset_1(X1,X0))) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 3.69/0.99    inference(nnf_transformation,[],[f29])).
% 3.69/0.99  
% 3.69/0.99  fof(f63,plain,(
% 3.69/0.99    ( ! [X0,X1] : (v1_subset_1(X1,X0) | X0 = X1 | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 3.69/0.99    inference(cnf_transformation,[],[f40])).
% 3.69/0.99  
% 3.69/0.99  fof(f12,conjecture,(
% 3.69/0.99    ! [X0] : ((l1_orders_2(X0) & v1_yellow_0(X0) & v5_orders_2(X0) & v4_orders_2(X0) & v3_orders_2(X0) & ~v2_struct_0(X0)) => ! [X1] : ((m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & v13_waybel_0(X1,X0) & v2_waybel_0(X1,X0) & ~v1_xboole_0(X1)) => (v1_subset_1(X1,u1_struct_0(X0)) <=> ~r2_hidden(k3_yellow_0(X0),X1))))),
% 3.69/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.69/0.99  
% 3.69/0.99  fof(f13,negated_conjecture,(
% 3.69/0.99    ~! [X0] : ((l1_orders_2(X0) & v1_yellow_0(X0) & v5_orders_2(X0) & v4_orders_2(X0) & v3_orders_2(X0) & ~v2_struct_0(X0)) => ! [X1] : ((m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & v13_waybel_0(X1,X0) & v2_waybel_0(X1,X0) & ~v1_xboole_0(X1)) => (v1_subset_1(X1,u1_struct_0(X0)) <=> ~r2_hidden(k3_yellow_0(X0),X1))))),
% 3.69/1.00    inference(negated_conjecture,[],[f12])).
% 3.69/1.00  
% 3.69/1.00  fof(f14,plain,(
% 3.69/1.00    ~! [X0] : ((l1_orders_2(X0) & v1_yellow_0(X0) & v5_orders_2(X0) & v4_orders_2(X0) & v3_orders_2(X0) & ~v2_struct_0(X0)) => ! [X1] : ((m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & v13_waybel_0(X1,X0) & ~v1_xboole_0(X1)) => (v1_subset_1(X1,u1_struct_0(X0)) <=> ~r2_hidden(k3_yellow_0(X0),X1))))),
% 3.69/1.00    inference(pure_predicate_removal,[],[f13])).
% 3.69/1.00  
% 3.69/1.00  fof(f15,plain,(
% 3.69/1.00    ~! [X0] : ((l1_orders_2(X0) & v1_yellow_0(X0) & v5_orders_2(X0) & v3_orders_2(X0) & ~v2_struct_0(X0)) => ! [X1] : ((m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & v13_waybel_0(X1,X0) & ~v1_xboole_0(X1)) => (v1_subset_1(X1,u1_struct_0(X0)) <=> ~r2_hidden(k3_yellow_0(X0),X1))))),
% 3.69/1.00    inference(pure_predicate_removal,[],[f14])).
% 3.69/1.00  
% 3.69/1.00  fof(f16,plain,(
% 3.69/1.00    ~! [X0] : ((l1_orders_2(X0) & v1_yellow_0(X0) & v5_orders_2(X0) & ~v2_struct_0(X0)) => ! [X1] : ((m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & v13_waybel_0(X1,X0) & ~v1_xboole_0(X1)) => (v1_subset_1(X1,u1_struct_0(X0)) <=> ~r2_hidden(k3_yellow_0(X0),X1))))),
% 3.69/1.00    inference(pure_predicate_removal,[],[f15])).
% 3.69/1.00  
% 3.69/1.00  fof(f30,plain,(
% 3.69/1.00    ? [X0] : (? [X1] : ((v1_subset_1(X1,u1_struct_0(X0)) <~> ~r2_hidden(k3_yellow_0(X0),X1)) & (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & v13_waybel_0(X1,X0) & ~v1_xboole_0(X1))) & (l1_orders_2(X0) & v1_yellow_0(X0) & v5_orders_2(X0) & ~v2_struct_0(X0)))),
% 3.69/1.00    inference(ennf_transformation,[],[f16])).
% 3.69/1.00  
% 3.69/1.00  fof(f31,plain,(
% 3.69/1.00    ? [X0] : (? [X1] : ((v1_subset_1(X1,u1_struct_0(X0)) <~> ~r2_hidden(k3_yellow_0(X0),X1)) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & v13_waybel_0(X1,X0) & ~v1_xboole_0(X1)) & l1_orders_2(X0) & v1_yellow_0(X0) & v5_orders_2(X0) & ~v2_struct_0(X0))),
% 3.69/1.00    inference(flattening,[],[f30])).
% 3.69/1.00  
% 3.69/1.00  fof(f41,plain,(
% 3.69/1.00    ? [X0] : (? [X1] : (((r2_hidden(k3_yellow_0(X0),X1) | ~v1_subset_1(X1,u1_struct_0(X0))) & (~r2_hidden(k3_yellow_0(X0),X1) | v1_subset_1(X1,u1_struct_0(X0)))) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & v13_waybel_0(X1,X0) & ~v1_xboole_0(X1)) & l1_orders_2(X0) & v1_yellow_0(X0) & v5_orders_2(X0) & ~v2_struct_0(X0))),
% 3.69/1.00    inference(nnf_transformation,[],[f31])).
% 3.69/1.00  
% 3.69/1.00  fof(f42,plain,(
% 3.69/1.00    ? [X0] : (? [X1] : ((r2_hidden(k3_yellow_0(X0),X1) | ~v1_subset_1(X1,u1_struct_0(X0))) & (~r2_hidden(k3_yellow_0(X0),X1) | v1_subset_1(X1,u1_struct_0(X0))) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & v13_waybel_0(X1,X0) & ~v1_xboole_0(X1)) & l1_orders_2(X0) & v1_yellow_0(X0) & v5_orders_2(X0) & ~v2_struct_0(X0))),
% 3.69/1.00    inference(flattening,[],[f41])).
% 3.69/1.00  
% 3.69/1.00  fof(f44,plain,(
% 3.69/1.00    ( ! [X0] : (? [X1] : ((r2_hidden(k3_yellow_0(X0),X1) | ~v1_subset_1(X1,u1_struct_0(X0))) & (~r2_hidden(k3_yellow_0(X0),X1) | v1_subset_1(X1,u1_struct_0(X0))) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & v13_waybel_0(X1,X0) & ~v1_xboole_0(X1)) => ((r2_hidden(k3_yellow_0(X0),sK4) | ~v1_subset_1(sK4,u1_struct_0(X0))) & (~r2_hidden(k3_yellow_0(X0),sK4) | v1_subset_1(sK4,u1_struct_0(X0))) & m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(X0))) & v13_waybel_0(sK4,X0) & ~v1_xboole_0(sK4))) )),
% 3.69/1.00    introduced(choice_axiom,[])).
% 3.69/1.00  
% 3.69/1.00  fof(f43,plain,(
% 3.69/1.00    ? [X0] : (? [X1] : ((r2_hidden(k3_yellow_0(X0),X1) | ~v1_subset_1(X1,u1_struct_0(X0))) & (~r2_hidden(k3_yellow_0(X0),X1) | v1_subset_1(X1,u1_struct_0(X0))) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & v13_waybel_0(X1,X0) & ~v1_xboole_0(X1)) & l1_orders_2(X0) & v1_yellow_0(X0) & v5_orders_2(X0) & ~v2_struct_0(X0)) => (? [X1] : ((r2_hidden(k3_yellow_0(sK3),X1) | ~v1_subset_1(X1,u1_struct_0(sK3))) & (~r2_hidden(k3_yellow_0(sK3),X1) | v1_subset_1(X1,u1_struct_0(sK3))) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK3))) & v13_waybel_0(X1,sK3) & ~v1_xboole_0(X1)) & l1_orders_2(sK3) & v1_yellow_0(sK3) & v5_orders_2(sK3) & ~v2_struct_0(sK3))),
% 3.69/1.00    introduced(choice_axiom,[])).
% 3.69/1.00  
% 3.69/1.00  fof(f45,plain,(
% 3.69/1.00    ((r2_hidden(k3_yellow_0(sK3),sK4) | ~v1_subset_1(sK4,u1_struct_0(sK3))) & (~r2_hidden(k3_yellow_0(sK3),sK4) | v1_subset_1(sK4,u1_struct_0(sK3))) & m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(sK3))) & v13_waybel_0(sK4,sK3) & ~v1_xboole_0(sK4)) & l1_orders_2(sK3) & v1_yellow_0(sK3) & v5_orders_2(sK3) & ~v2_struct_0(sK3)),
% 3.69/1.00    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3,sK4])],[f42,f44,f43])).
% 3.69/1.00  
% 3.69/1.00  fof(f72,plain,(
% 3.69/1.00    r2_hidden(k3_yellow_0(sK3),sK4) | ~v1_subset_1(sK4,u1_struct_0(sK3))),
% 3.69/1.00    inference(cnf_transformation,[],[f45])).
% 3.69/1.00  
% 3.69/1.00  fof(f70,plain,(
% 3.69/1.00    m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(sK3)))),
% 3.69/1.00    inference(cnf_transformation,[],[f45])).
% 3.69/1.00  
% 3.69/1.00  fof(f67,plain,(
% 3.69/1.00    l1_orders_2(sK3)),
% 3.69/1.00    inference(cnf_transformation,[],[f45])).
% 3.69/1.00  
% 3.69/1.00  fof(f8,axiom,(
% 3.69/1.00    ! [X0] : (l1_orders_2(X0) => m1_subset_1(k3_yellow_0(X0),u1_struct_0(X0)))),
% 3.69/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.69/1.00  
% 3.69/1.00  fof(f24,plain,(
% 3.69/1.00    ! [X0] : (m1_subset_1(k3_yellow_0(X0),u1_struct_0(X0)) | ~l1_orders_2(X0))),
% 3.69/1.00    inference(ennf_transformation,[],[f8])).
% 3.69/1.00  
% 3.69/1.00  fof(f54,plain,(
% 3.69/1.00    ( ! [X0] : (m1_subset_1(k3_yellow_0(X0),u1_struct_0(X0)) | ~l1_orders_2(X0)) )),
% 3.69/1.00    inference(cnf_transformation,[],[f24])).
% 3.69/1.00  
% 3.69/1.00  fof(f6,axiom,(
% 3.69/1.00    ! [X0,X1] : (m1_subset_1(X0,X1) => (r2_hidden(X0,X1) | v1_xboole_0(X1)))),
% 3.69/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.69/1.00  
% 3.69/1.00  fof(f20,plain,(
% 3.69/1.00    ! [X0,X1] : ((r2_hidden(X0,X1) | v1_xboole_0(X1)) | ~m1_subset_1(X0,X1))),
% 3.69/1.00    inference(ennf_transformation,[],[f6])).
% 3.69/1.00  
% 3.69/1.00  fof(f21,plain,(
% 3.69/1.00    ! [X0,X1] : (r2_hidden(X0,X1) | v1_xboole_0(X1) | ~m1_subset_1(X0,X1))),
% 3.69/1.00    inference(flattening,[],[f20])).
% 3.69/1.00  
% 3.69/1.00  fof(f52,plain,(
% 3.69/1.00    ( ! [X0,X1] : (r2_hidden(X0,X1) | v1_xboole_0(X1) | ~m1_subset_1(X0,X1)) )),
% 3.69/1.00    inference(cnf_transformation,[],[f21])).
% 3.69/1.00  
% 3.69/1.00  fof(f68,plain,(
% 3.69/1.00    ~v1_xboole_0(sK4)),
% 3.69/1.00    inference(cnf_transformation,[],[f45])).
% 3.69/1.00  
% 3.69/1.00  fof(f10,axiom,(
% 3.69/1.00    ! [X0] : (l1_orders_2(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => (v13_waybel_0(X1,X0) <=> ! [X2] : (m1_subset_1(X2,u1_struct_0(X0)) => ! [X3] : (m1_subset_1(X3,u1_struct_0(X0)) => ((r1_orders_2(X0,X2,X3) & r2_hidden(X2,X1)) => r2_hidden(X3,X1)))))))),
% 3.69/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.69/1.00  
% 3.69/1.00  fof(f27,plain,(
% 3.69/1.00    ! [X0] : (! [X1] : ((v13_waybel_0(X1,X0) <=> ! [X2] : (! [X3] : ((r2_hidden(X3,X1) | (~r1_orders_2(X0,X2,X3) | ~r2_hidden(X2,X1))) | ~m1_subset_1(X3,u1_struct_0(X0))) | ~m1_subset_1(X2,u1_struct_0(X0)))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_orders_2(X0))),
% 3.69/1.00    inference(ennf_transformation,[],[f10])).
% 3.69/1.00  
% 3.69/1.00  fof(f28,plain,(
% 3.69/1.00    ! [X0] : (! [X1] : ((v13_waybel_0(X1,X0) <=> ! [X2] : (! [X3] : (r2_hidden(X3,X1) | ~r1_orders_2(X0,X2,X3) | ~r2_hidden(X2,X1) | ~m1_subset_1(X3,u1_struct_0(X0))) | ~m1_subset_1(X2,u1_struct_0(X0)))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_orders_2(X0))),
% 3.69/1.00    inference(flattening,[],[f27])).
% 3.69/1.00  
% 3.69/1.00  fof(f35,plain,(
% 3.69/1.00    ! [X0] : (! [X1] : (((v13_waybel_0(X1,X0) | ? [X2] : (? [X3] : (~r2_hidden(X3,X1) & r1_orders_2(X0,X2,X3) & r2_hidden(X2,X1) & m1_subset_1(X3,u1_struct_0(X0))) & m1_subset_1(X2,u1_struct_0(X0)))) & (! [X2] : (! [X3] : (r2_hidden(X3,X1) | ~r1_orders_2(X0,X2,X3) | ~r2_hidden(X2,X1) | ~m1_subset_1(X3,u1_struct_0(X0))) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~v13_waybel_0(X1,X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_orders_2(X0))),
% 3.69/1.00    inference(nnf_transformation,[],[f28])).
% 3.69/1.00  
% 3.69/1.00  fof(f36,plain,(
% 3.69/1.00    ! [X0] : (! [X1] : (((v13_waybel_0(X1,X0) | ? [X2] : (? [X3] : (~r2_hidden(X3,X1) & r1_orders_2(X0,X2,X3) & r2_hidden(X2,X1) & m1_subset_1(X3,u1_struct_0(X0))) & m1_subset_1(X2,u1_struct_0(X0)))) & (! [X4] : (! [X5] : (r2_hidden(X5,X1) | ~r1_orders_2(X0,X4,X5) | ~r2_hidden(X4,X1) | ~m1_subset_1(X5,u1_struct_0(X0))) | ~m1_subset_1(X4,u1_struct_0(X0))) | ~v13_waybel_0(X1,X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_orders_2(X0))),
% 3.69/1.00    inference(rectify,[],[f35])).
% 3.69/1.00  
% 3.69/1.00  fof(f38,plain,(
% 3.69/1.00    ( ! [X2] : (! [X1,X0] : (? [X3] : (~r2_hidden(X3,X1) & r1_orders_2(X0,X2,X3) & r2_hidden(X2,X1) & m1_subset_1(X3,u1_struct_0(X0))) => (~r2_hidden(sK2(X0,X1),X1) & r1_orders_2(X0,X2,sK2(X0,X1)) & r2_hidden(X2,X1) & m1_subset_1(sK2(X0,X1),u1_struct_0(X0))))) )),
% 3.69/1.00    introduced(choice_axiom,[])).
% 3.69/1.00  
% 3.69/1.00  fof(f37,plain,(
% 3.69/1.00    ! [X1,X0] : (? [X2] : (? [X3] : (~r2_hidden(X3,X1) & r1_orders_2(X0,X2,X3) & r2_hidden(X2,X1) & m1_subset_1(X3,u1_struct_0(X0))) & m1_subset_1(X2,u1_struct_0(X0))) => (? [X3] : (~r2_hidden(X3,X1) & r1_orders_2(X0,sK1(X0,X1),X3) & r2_hidden(sK1(X0,X1),X1) & m1_subset_1(X3,u1_struct_0(X0))) & m1_subset_1(sK1(X0,X1),u1_struct_0(X0))))),
% 3.69/1.00    introduced(choice_axiom,[])).
% 3.69/1.00  
% 3.69/1.00  fof(f39,plain,(
% 3.69/1.00    ! [X0] : (! [X1] : (((v13_waybel_0(X1,X0) | ((~r2_hidden(sK2(X0,X1),X1) & r1_orders_2(X0,sK1(X0,X1),sK2(X0,X1)) & r2_hidden(sK1(X0,X1),X1) & m1_subset_1(sK2(X0,X1),u1_struct_0(X0))) & m1_subset_1(sK1(X0,X1),u1_struct_0(X0)))) & (! [X4] : (! [X5] : (r2_hidden(X5,X1) | ~r1_orders_2(X0,X4,X5) | ~r2_hidden(X4,X1) | ~m1_subset_1(X5,u1_struct_0(X0))) | ~m1_subset_1(X4,u1_struct_0(X0))) | ~v13_waybel_0(X1,X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_orders_2(X0))),
% 3.69/1.00    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1,sK2])],[f36,f38,f37])).
% 3.69/1.00  
% 3.69/1.00  fof(f56,plain,(
% 3.69/1.00    ( ! [X4,X0,X5,X1] : (r2_hidden(X5,X1) | ~r1_orders_2(X0,X4,X5) | ~r2_hidden(X4,X1) | ~m1_subset_1(X5,u1_struct_0(X0)) | ~m1_subset_1(X4,u1_struct_0(X0)) | ~v13_waybel_0(X1,X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_orders_2(X0)) )),
% 3.69/1.00    inference(cnf_transformation,[],[f39])).
% 3.69/1.00  
% 3.69/1.00  fof(f9,axiom,(
% 3.69/1.00    ! [X0] : ((l1_orders_2(X0) & v1_yellow_0(X0) & v5_orders_2(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,u1_struct_0(X0)) => r1_orders_2(X0,k3_yellow_0(X0),X1)))),
% 3.69/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.69/1.00  
% 3.69/1.00  fof(f25,plain,(
% 3.69/1.00    ! [X0] : (! [X1] : (r1_orders_2(X0,k3_yellow_0(X0),X1) | ~m1_subset_1(X1,u1_struct_0(X0))) | (~l1_orders_2(X0) | ~v1_yellow_0(X0) | ~v5_orders_2(X0) | v2_struct_0(X0)))),
% 3.69/1.00    inference(ennf_transformation,[],[f9])).
% 3.69/1.00  
% 3.69/1.00  fof(f26,plain,(
% 3.69/1.00    ! [X0] : (! [X1] : (r1_orders_2(X0,k3_yellow_0(X0),X1) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~l1_orders_2(X0) | ~v1_yellow_0(X0) | ~v5_orders_2(X0) | v2_struct_0(X0))),
% 3.69/1.00    inference(flattening,[],[f25])).
% 3.69/1.00  
% 3.69/1.00  fof(f55,plain,(
% 3.69/1.00    ( ! [X0,X1] : (r1_orders_2(X0,k3_yellow_0(X0),X1) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_orders_2(X0) | ~v1_yellow_0(X0) | ~v5_orders_2(X0) | v2_struct_0(X0)) )),
% 3.69/1.00    inference(cnf_transformation,[],[f26])).
% 3.69/1.00  
% 3.69/1.00  fof(f66,plain,(
% 3.69/1.00    v1_yellow_0(sK3)),
% 3.69/1.00    inference(cnf_transformation,[],[f45])).
% 3.69/1.00  
% 3.69/1.00  fof(f64,plain,(
% 3.69/1.00    ~v2_struct_0(sK3)),
% 3.69/1.00    inference(cnf_transformation,[],[f45])).
% 3.69/1.00  
% 3.69/1.00  fof(f65,plain,(
% 3.69/1.00    v5_orders_2(sK3)),
% 3.69/1.00    inference(cnf_transformation,[],[f45])).
% 3.69/1.00  
% 3.69/1.00  fof(f69,plain,(
% 3.69/1.00    v13_waybel_0(sK4,sK3)),
% 3.69/1.00    inference(cnf_transformation,[],[f45])).
% 3.69/1.00  
% 3.69/1.00  fof(f47,plain,(
% 3.69/1.00    ( ! [X0,X1] : (X0 = X1 | ~r2_hidden(sK0(X0,X1),X1) | ~r2_hidden(sK0(X0,X1),X0)) )),
% 3.69/1.00    inference(cnf_transformation,[],[f34])).
% 3.69/1.00  
% 3.69/1.00  fof(f7,axiom,(
% 3.69/1.00    ! [X0,X1,X2] : ((m1_subset_1(X1,k1_zfmisc_1(X2)) & r2_hidden(X0,X1)) => m1_subset_1(X0,X2))),
% 3.69/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.69/1.00  
% 3.69/1.00  fof(f22,plain,(
% 3.69/1.00    ! [X0,X1,X2] : (m1_subset_1(X0,X2) | (~m1_subset_1(X1,k1_zfmisc_1(X2)) | ~r2_hidden(X0,X1)))),
% 3.69/1.00    inference(ennf_transformation,[],[f7])).
% 3.69/1.00  
% 3.69/1.00  fof(f23,plain,(
% 3.69/1.00    ! [X0,X1,X2] : (m1_subset_1(X0,X2) | ~m1_subset_1(X1,k1_zfmisc_1(X2)) | ~r2_hidden(X0,X1))),
% 3.69/1.00    inference(flattening,[],[f22])).
% 3.69/1.00  
% 3.69/1.00  fof(f53,plain,(
% 3.69/1.00    ( ! [X2,X0,X1] : (m1_subset_1(X0,X2) | ~m1_subset_1(X1,k1_zfmisc_1(X2)) | ~r2_hidden(X0,X1)) )),
% 3.69/1.00    inference(cnf_transformation,[],[f23])).
% 3.69/1.00  
% 3.69/1.00  fof(f4,axiom,(
% 3.69/1.00    ! [X0] : (v1_xboole_0(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => v1_xboole_0(X1)))),
% 3.69/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.69/1.00  
% 3.69/1.00  fof(f18,plain,(
% 3.69/1.00    ! [X0] : (! [X1] : (v1_xboole_0(X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) | ~v1_xboole_0(X0))),
% 3.69/1.00    inference(ennf_transformation,[],[f4])).
% 3.69/1.00  
% 3.69/1.00  fof(f50,plain,(
% 3.69/1.00    ( ! [X0,X1] : (v1_xboole_0(X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0)) | ~v1_xboole_0(X0)) )),
% 3.69/1.00    inference(cnf_transformation,[],[f18])).
% 3.69/1.00  
% 3.69/1.00  fof(f62,plain,(
% 3.69/1.00    ( ! [X0,X1] : (X0 != X1 | ~v1_subset_1(X1,X0) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 3.69/1.00    inference(cnf_transformation,[],[f40])).
% 3.69/1.00  
% 3.69/1.00  fof(f73,plain,(
% 3.69/1.00    ( ! [X1] : (~v1_subset_1(X1,X1) | ~m1_subset_1(X1,k1_zfmisc_1(X1))) )),
% 3.69/1.00    inference(equality_resolution,[],[f62])).
% 3.69/1.00  
% 3.69/1.00  fof(f71,plain,(
% 3.69/1.00    ~r2_hidden(k3_yellow_0(sK3),sK4) | v1_subset_1(sK4,u1_struct_0(sK3))),
% 3.69/1.00    inference(cnf_transformation,[],[f45])).
% 3.69/1.00  
% 3.69/1.00  fof(f3,axiom,(
% 3.69/1.00    ! [X0] : m1_subset_1(k2_subset_1(X0),k1_zfmisc_1(X0))),
% 3.69/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.69/1.00  
% 3.69/1.00  fof(f49,plain,(
% 3.69/1.00    ( ! [X0] : (m1_subset_1(k2_subset_1(X0),k1_zfmisc_1(X0))) )),
% 3.69/1.00    inference(cnf_transformation,[],[f3])).
% 3.69/1.00  
% 3.69/1.00  fof(f2,axiom,(
% 3.69/1.00    ! [X0] : k2_subset_1(X0) = X0),
% 3.69/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.69/1.00  
% 3.69/1.00  fof(f48,plain,(
% 3.69/1.00    ( ! [X0] : (k2_subset_1(X0) = X0) )),
% 3.69/1.00    inference(cnf_transformation,[],[f2])).
% 3.69/1.00  
% 3.69/1.00  cnf(c_1,plain,
% 3.69/1.00      ( r2_hidden(sK0(X0,X1),X1) | r2_hidden(sK0(X0,X1),X0) | X1 = X0 ),
% 3.69/1.00      inference(cnf_transformation,[],[f46]) ).
% 3.69/1.00  
% 3.69/1.00  cnf(c_1104,plain,
% 3.69/1.00      ( X0 = X1
% 3.69/1.00      | r2_hidden(sK0(X1,X0),X0) = iProver_top
% 3.69/1.00      | r2_hidden(sK0(X1,X0),X1) = iProver_top ),
% 3.69/1.00      inference(predicate_to_equality,[status(thm)],[c_1]) ).
% 3.69/1.00  
% 3.69/1.00  cnf(c_5,plain,
% 3.69/1.00      ( m1_subset_1(X0,X1) | ~ r2_hidden(X0,X1) ),
% 3.69/1.00      inference(cnf_transformation,[],[f51]) ).
% 3.69/1.00  
% 3.69/1.00  cnf(c_1101,plain,
% 3.69/1.00      ( m1_subset_1(X0,X1) = iProver_top
% 3.69/1.00      | r2_hidden(X0,X1) != iProver_top ),
% 3.69/1.00      inference(predicate_to_equality,[status(thm)],[c_5]) ).
% 3.69/1.00  
% 3.69/1.00  cnf(c_2463,plain,
% 3.69/1.00      ( X0 = X1
% 3.69/1.00      | m1_subset_1(sK0(X0,X1),X0) = iProver_top
% 3.69/1.00      | r2_hidden(sK0(X0,X1),X1) = iProver_top ),
% 3.69/1.00      inference(superposition,[status(thm)],[c_1104,c_1101]) ).
% 3.69/1.00  
% 3.69/1.00  cnf(c_16,plain,
% 3.69/1.00      ( v1_subset_1(X0,X1)
% 3.69/1.00      | ~ m1_subset_1(X0,k1_zfmisc_1(X1))
% 3.69/1.00      | X0 = X1 ),
% 3.69/1.00      inference(cnf_transformation,[],[f63]) ).
% 3.69/1.00  
% 3.69/1.00  cnf(c_18,negated_conjecture,
% 3.69/1.00      ( ~ v1_subset_1(sK4,u1_struct_0(sK3))
% 3.69/1.00      | r2_hidden(k3_yellow_0(sK3),sK4) ),
% 3.69/1.00      inference(cnf_transformation,[],[f72]) ).
% 3.69/1.00  
% 3.69/1.00  cnf(c_195,plain,
% 3.69/1.00      ( ~ v1_subset_1(sK4,u1_struct_0(sK3))
% 3.69/1.00      | r2_hidden(k3_yellow_0(sK3),sK4) ),
% 3.69/1.00      inference(prop_impl,[status(thm)],[c_18]) ).
% 3.69/1.00  
% 3.69/1.00  cnf(c_372,plain,
% 3.69/1.00      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
% 3.69/1.00      | r2_hidden(k3_yellow_0(sK3),sK4)
% 3.69/1.00      | X1 = X0
% 3.69/1.00      | u1_struct_0(sK3) != X1
% 3.69/1.00      | sK4 != X0 ),
% 3.69/1.00      inference(resolution_lifted,[status(thm)],[c_16,c_195]) ).
% 3.69/1.00  
% 3.69/1.00  cnf(c_373,plain,
% 3.69/1.00      ( ~ m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(sK3)))
% 3.69/1.00      | r2_hidden(k3_yellow_0(sK3),sK4)
% 3.69/1.00      | u1_struct_0(sK3) = sK4 ),
% 3.69/1.00      inference(unflattening,[status(thm)],[c_372]) ).
% 3.69/1.00  
% 3.69/1.00  cnf(c_20,negated_conjecture,
% 3.69/1.00      ( m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(sK3))) ),
% 3.69/1.00      inference(cnf_transformation,[],[f70]) ).
% 3.69/1.00  
% 3.69/1.00  cnf(c_375,plain,
% 3.69/1.00      ( r2_hidden(k3_yellow_0(sK3),sK4) | u1_struct_0(sK3) = sK4 ),
% 3.69/1.00      inference(global_propositional_subsumption,
% 3.69/1.00                [status(thm)],
% 3.69/1.00                [c_373,c_20]) ).
% 3.69/1.00  
% 3.69/1.00  cnf(c_1095,plain,
% 3.69/1.00      ( u1_struct_0(sK3) = sK4
% 3.69/1.00      | r2_hidden(k3_yellow_0(sK3),sK4) = iProver_top ),
% 3.69/1.00      inference(predicate_to_equality,[status(thm)],[c_375]) ).
% 3.69/1.00  
% 3.69/1.00  cnf(c_2402,plain,
% 3.69/1.00      ( u1_struct_0(sK3) = sK4
% 3.69/1.00      | m1_subset_1(k3_yellow_0(sK3),sK4) = iProver_top ),
% 3.69/1.00      inference(superposition,[status(thm)],[c_1095,c_1101]) ).
% 3.69/1.00  
% 3.69/1.00  cnf(c_23,negated_conjecture,
% 3.69/1.00      ( l1_orders_2(sK3) ),
% 3.69/1.00      inference(cnf_transformation,[],[f67]) ).
% 3.69/1.00  
% 3.69/1.00  cnf(c_30,plain,
% 3.69/1.00      ( l1_orders_2(sK3) = iProver_top ),
% 3.69/1.00      inference(predicate_to_equality,[status(thm)],[c_23]) ).
% 3.69/1.00  
% 3.69/1.00  cnf(c_8,plain,
% 3.69/1.00      ( m1_subset_1(k3_yellow_0(X0),u1_struct_0(X0))
% 3.69/1.00      | ~ l1_orders_2(X0) ),
% 3.69/1.00      inference(cnf_transformation,[],[f54]) ).
% 3.69/1.00  
% 3.69/1.00  cnf(c_61,plain,
% 3.69/1.00      ( m1_subset_1(k3_yellow_0(X0),u1_struct_0(X0)) = iProver_top
% 3.69/1.00      | l1_orders_2(X0) != iProver_top ),
% 3.69/1.00      inference(predicate_to_equality,[status(thm)],[c_8]) ).
% 3.69/1.00  
% 3.69/1.00  cnf(c_63,plain,
% 3.69/1.00      ( m1_subset_1(k3_yellow_0(sK3),u1_struct_0(sK3)) = iProver_top
% 3.69/1.00      | l1_orders_2(sK3) != iProver_top ),
% 3.69/1.00      inference(instantiation,[status(thm)],[c_61]) ).
% 3.69/1.00  
% 3.69/1.00  cnf(c_726,plain,
% 3.69/1.00      ( X0 != X1 | k3_yellow_0(X0) = k3_yellow_0(X1) ),
% 3.69/1.00      theory(equality) ).
% 3.69/1.00  
% 3.69/1.00  cnf(c_735,plain,
% 3.69/1.00      ( k3_yellow_0(sK3) = k3_yellow_0(sK3) | sK3 != sK3 ),
% 3.69/1.00      inference(instantiation,[status(thm)],[c_726]) ).
% 3.69/1.00  
% 3.69/1.00  cnf(c_720,plain,( X0 = X0 ),theory(equality) ).
% 3.69/1.00  
% 3.69/1.00  cnf(c_741,plain,
% 3.69/1.00      ( sK3 = sK3 ),
% 3.69/1.00      inference(instantiation,[status(thm)],[c_720]) ).
% 3.69/1.00  
% 3.69/1.00  cnf(c_1449,plain,
% 3.69/1.00      ( sK4 = sK4 ),
% 3.69/1.00      inference(instantiation,[status(thm)],[c_720]) ).
% 3.69/1.00  
% 3.69/1.00  cnf(c_724,plain,
% 3.69/1.00      ( ~ m1_subset_1(X0,X1) | m1_subset_1(X2,X3) | X2 != X0 | X3 != X1 ),
% 3.69/1.00      theory(equality) ).
% 3.69/1.00  
% 3.69/1.00  cnf(c_1381,plain,
% 3.69/1.00      ( m1_subset_1(X0,X1)
% 3.69/1.00      | ~ m1_subset_1(k3_yellow_0(sK3),u1_struct_0(sK3))
% 3.69/1.00      | X1 != u1_struct_0(sK3)
% 3.69/1.00      | X0 != k3_yellow_0(sK3) ),
% 3.69/1.00      inference(instantiation,[status(thm)],[c_724]) ).
% 3.69/1.00  
% 3.69/1.00  cnf(c_1549,plain,
% 3.69/1.00      ( m1_subset_1(k3_yellow_0(X0),X1)
% 3.69/1.00      | ~ m1_subset_1(k3_yellow_0(sK3),u1_struct_0(sK3))
% 3.69/1.00      | X1 != u1_struct_0(sK3)
% 3.69/1.00      | k3_yellow_0(X0) != k3_yellow_0(sK3) ),
% 3.69/1.00      inference(instantiation,[status(thm)],[c_1381]) ).
% 3.69/1.00  
% 3.69/1.00  cnf(c_1852,plain,
% 3.69/1.00      ( m1_subset_1(k3_yellow_0(X0),sK4)
% 3.69/1.00      | ~ m1_subset_1(k3_yellow_0(sK3),u1_struct_0(sK3))
% 3.69/1.00      | k3_yellow_0(X0) != k3_yellow_0(sK3)
% 3.69/1.00      | sK4 != u1_struct_0(sK3) ),
% 3.69/1.00      inference(instantiation,[status(thm)],[c_1549]) ).
% 3.69/1.00  
% 3.69/1.00  cnf(c_1863,plain,
% 3.69/1.00      ( k3_yellow_0(X0) != k3_yellow_0(sK3)
% 3.69/1.00      | sK4 != u1_struct_0(sK3)
% 3.69/1.00      | m1_subset_1(k3_yellow_0(X0),sK4) = iProver_top
% 3.69/1.00      | m1_subset_1(k3_yellow_0(sK3),u1_struct_0(sK3)) != iProver_top ),
% 3.69/1.00      inference(predicate_to_equality,[status(thm)],[c_1852]) ).
% 3.69/1.00  
% 3.69/1.00  cnf(c_1865,plain,
% 3.69/1.00      ( k3_yellow_0(sK3) != k3_yellow_0(sK3)
% 3.69/1.00      | sK4 != u1_struct_0(sK3)
% 3.69/1.00      | m1_subset_1(k3_yellow_0(sK3),u1_struct_0(sK3)) != iProver_top
% 3.69/1.00      | m1_subset_1(k3_yellow_0(sK3),sK4) = iProver_top ),
% 3.69/1.00      inference(instantiation,[status(thm)],[c_1863]) ).
% 3.69/1.00  
% 3.69/1.00  cnf(c_721,plain,( X0 != X1 | X2 != X1 | X2 = X0 ),theory(equality) ).
% 3.69/1.00  
% 3.69/1.00  cnf(c_1391,plain,
% 3.69/1.00      ( u1_struct_0(sK3) != X0 | sK4 != X0 | sK4 = u1_struct_0(sK3) ),
% 3.69/1.00      inference(instantiation,[status(thm)],[c_721]) ).
% 3.69/1.00  
% 3.69/1.00  cnf(c_3308,plain,
% 3.69/1.00      ( u1_struct_0(sK3) != sK4 | sK4 = u1_struct_0(sK3) | sK4 != sK4 ),
% 3.69/1.00      inference(instantiation,[status(thm)],[c_1391]) ).
% 3.69/1.00  
% 3.69/1.00  cnf(c_3475,plain,
% 3.69/1.00      ( m1_subset_1(k3_yellow_0(sK3),sK4) = iProver_top ),
% 3.69/1.00      inference(global_propositional_subsumption,
% 3.69/1.00                [status(thm)],
% 3.69/1.00                [c_2402,c_30,c_63,c_735,c_741,c_1449,c_1865,c_3308]) ).
% 3.69/1.00  
% 3.69/1.00  cnf(c_6,plain,
% 3.69/1.00      ( ~ m1_subset_1(X0,X1) | r2_hidden(X0,X1) | v1_xboole_0(X1) ),
% 3.69/1.00      inference(cnf_transformation,[],[f52]) ).
% 3.69/1.00  
% 3.69/1.00  cnf(c_1100,plain,
% 3.69/1.00      ( m1_subset_1(X0,X1) != iProver_top
% 3.69/1.00      | r2_hidden(X0,X1) = iProver_top
% 3.69/1.00      | v1_xboole_0(X1) = iProver_top ),
% 3.69/1.00      inference(predicate_to_equality,[status(thm)],[c_6]) ).
% 3.69/1.00  
% 3.69/1.00  cnf(c_3480,plain,
% 3.69/1.00      ( r2_hidden(k3_yellow_0(sK3),sK4) = iProver_top
% 3.69/1.00      | v1_xboole_0(sK4) = iProver_top ),
% 3.69/1.00      inference(superposition,[status(thm)],[c_3475,c_1100]) ).
% 3.69/1.00  
% 3.69/1.00  cnf(c_22,negated_conjecture,
% 3.69/1.00      ( ~ v1_xboole_0(sK4) ),
% 3.69/1.00      inference(cnf_transformation,[],[f68]) ).
% 3.69/1.00  
% 3.69/1.00  cnf(c_31,plain,
% 3.69/1.00      ( v1_xboole_0(sK4) != iProver_top ),
% 3.69/1.00      inference(predicate_to_equality,[status(thm)],[c_22]) ).
% 3.69/1.00  
% 3.69/1.00  cnf(c_3740,plain,
% 3.69/1.00      ( r2_hidden(k3_yellow_0(sK3),sK4) = iProver_top ),
% 3.69/1.00      inference(global_propositional_subsumption,
% 3.69/1.00                [status(thm)],
% 3.69/1.00                [c_3480,c_31]) ).
% 3.69/1.00  
% 3.69/1.00  cnf(c_1098,plain,
% 3.69/1.00      ( m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(sK3))) = iProver_top ),
% 3.69/1.00      inference(predicate_to_equality,[status(thm)],[c_20]) ).
% 3.69/1.00  
% 3.69/1.00  cnf(c_15,plain,
% 3.69/1.00      ( ~ r1_orders_2(X0,X1,X2)
% 3.69/1.00      | ~ v13_waybel_0(X3,X0)
% 3.69/1.00      | ~ m1_subset_1(X2,u1_struct_0(X0))
% 3.69/1.00      | ~ m1_subset_1(X1,u1_struct_0(X0))
% 3.69/1.00      | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))
% 3.69/1.00      | ~ r2_hidden(X1,X3)
% 3.69/1.00      | r2_hidden(X2,X3)
% 3.69/1.00      | ~ l1_orders_2(X0) ),
% 3.69/1.00      inference(cnf_transformation,[],[f56]) ).
% 3.69/1.00  
% 3.69/1.00  cnf(c_9,plain,
% 3.69/1.00      ( r1_orders_2(X0,k3_yellow_0(X0),X1)
% 3.69/1.00      | ~ m1_subset_1(X1,u1_struct_0(X0))
% 3.69/1.00      | v2_struct_0(X0)
% 3.69/1.00      | ~ v5_orders_2(X0)
% 3.69/1.00      | ~ v1_yellow_0(X0)
% 3.69/1.00      | ~ l1_orders_2(X0) ),
% 3.69/1.00      inference(cnf_transformation,[],[f55]) ).
% 3.69/1.00  
% 3.69/1.00  cnf(c_24,negated_conjecture,
% 3.69/1.00      ( v1_yellow_0(sK3) ),
% 3.69/1.00      inference(cnf_transformation,[],[f66]) ).
% 3.69/1.00  
% 3.69/1.00  cnf(c_348,plain,
% 3.69/1.00      ( r1_orders_2(X0,k3_yellow_0(X0),X1)
% 3.69/1.00      | ~ m1_subset_1(X1,u1_struct_0(X0))
% 3.69/1.00      | v2_struct_0(X0)
% 3.69/1.00      | ~ v5_orders_2(X0)
% 3.69/1.00      | ~ l1_orders_2(X0)
% 3.69/1.00      | sK3 != X0 ),
% 3.69/1.00      inference(resolution_lifted,[status(thm)],[c_9,c_24]) ).
% 3.69/1.00  
% 3.69/1.00  cnf(c_349,plain,
% 3.69/1.00      ( r1_orders_2(sK3,k3_yellow_0(sK3),X0)
% 3.69/1.00      | ~ m1_subset_1(X0,u1_struct_0(sK3))
% 3.69/1.00      | v2_struct_0(sK3)
% 3.69/1.00      | ~ v5_orders_2(sK3)
% 3.69/1.00      | ~ l1_orders_2(sK3) ),
% 3.69/1.00      inference(unflattening,[status(thm)],[c_348]) ).
% 3.69/1.00  
% 3.69/1.00  cnf(c_26,negated_conjecture,
% 3.69/1.00      ( ~ v2_struct_0(sK3) ),
% 3.69/1.00      inference(cnf_transformation,[],[f64]) ).
% 3.69/1.00  
% 3.69/1.00  cnf(c_25,negated_conjecture,
% 3.69/1.00      ( v5_orders_2(sK3) ),
% 3.69/1.00      inference(cnf_transformation,[],[f65]) ).
% 3.69/1.00  
% 3.69/1.00  cnf(c_353,plain,
% 3.69/1.00      ( ~ m1_subset_1(X0,u1_struct_0(sK3))
% 3.69/1.00      | r1_orders_2(sK3,k3_yellow_0(sK3),X0) ),
% 3.69/1.00      inference(global_propositional_subsumption,
% 3.69/1.00                [status(thm)],
% 3.69/1.00                [c_349,c_26,c_25,c_23]) ).
% 3.69/1.00  
% 3.69/1.00  cnf(c_354,plain,
% 3.69/1.00      ( r1_orders_2(sK3,k3_yellow_0(sK3),X0)
% 3.69/1.00      | ~ m1_subset_1(X0,u1_struct_0(sK3)) ),
% 3.69/1.00      inference(renaming,[status(thm)],[c_353]) ).
% 3.69/1.00  
% 3.69/1.00  cnf(c_436,plain,
% 3.69/1.00      ( ~ v13_waybel_0(X0,X1)
% 3.69/1.00      | ~ m1_subset_1(X2,u1_struct_0(X1))
% 3.69/1.00      | ~ m1_subset_1(X3,u1_struct_0(X1))
% 3.69/1.00      | ~ m1_subset_1(X4,u1_struct_0(sK3))
% 3.69/1.00      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 3.69/1.00      | ~ r2_hidden(X2,X0)
% 3.69/1.00      | r2_hidden(X3,X0)
% 3.69/1.00      | ~ l1_orders_2(X1)
% 3.69/1.00      | X4 != X3
% 3.69/1.00      | k3_yellow_0(sK3) != X2
% 3.69/1.00      | sK3 != X1 ),
% 3.69/1.00      inference(resolution_lifted,[status(thm)],[c_15,c_354]) ).
% 3.69/1.00  
% 3.69/1.00  cnf(c_437,plain,
% 3.69/1.00      ( ~ v13_waybel_0(X0,sK3)
% 3.69/1.00      | ~ m1_subset_1(X1,u1_struct_0(sK3))
% 3.69/1.00      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK3)))
% 3.69/1.00      | ~ m1_subset_1(k3_yellow_0(sK3),u1_struct_0(sK3))
% 3.69/1.00      | r2_hidden(X1,X0)
% 3.69/1.00      | ~ r2_hidden(k3_yellow_0(sK3),X0)
% 3.69/1.00      | ~ l1_orders_2(sK3) ),
% 3.69/1.00      inference(unflattening,[status(thm)],[c_436]) ).
% 3.69/1.00  
% 3.69/1.00  cnf(c_62,plain,
% 3.69/1.00      ( m1_subset_1(k3_yellow_0(sK3),u1_struct_0(sK3))
% 3.69/1.00      | ~ l1_orders_2(sK3) ),
% 3.69/1.00      inference(instantiation,[status(thm)],[c_8]) ).
% 3.69/1.00  
% 3.69/1.00  cnf(c_441,plain,
% 3.69/1.00      ( ~ r2_hidden(k3_yellow_0(sK3),X0)
% 3.69/1.00      | r2_hidden(X1,X0)
% 3.69/1.00      | ~ v13_waybel_0(X0,sK3)
% 3.69/1.00      | ~ m1_subset_1(X1,u1_struct_0(sK3))
% 3.69/1.00      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK3))) ),
% 3.69/1.00      inference(global_propositional_subsumption,
% 3.69/1.00                [status(thm)],
% 3.69/1.00                [c_437,c_23,c_62]) ).
% 3.69/1.00  
% 3.69/1.00  cnf(c_442,plain,
% 3.69/1.00      ( ~ v13_waybel_0(X0,sK3)
% 3.69/1.00      | ~ m1_subset_1(X1,u1_struct_0(sK3))
% 3.69/1.00      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK3)))
% 3.69/1.00      | r2_hidden(X1,X0)
% 3.69/1.00      | ~ r2_hidden(k3_yellow_0(sK3),X0) ),
% 3.69/1.00      inference(renaming,[status(thm)],[c_441]) ).
% 3.69/1.00  
% 3.69/1.00  cnf(c_1093,plain,
% 3.69/1.00      ( v13_waybel_0(X0,sK3) != iProver_top
% 3.69/1.00      | m1_subset_1(X1,u1_struct_0(sK3)) != iProver_top
% 3.69/1.00      | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK3))) != iProver_top
% 3.69/1.00      | r2_hidden(X1,X0) = iProver_top
% 3.69/1.00      | r2_hidden(k3_yellow_0(sK3),X0) != iProver_top ),
% 3.69/1.00      inference(predicate_to_equality,[status(thm)],[c_442]) ).
% 3.69/1.00  
% 3.69/1.00  cnf(c_2081,plain,
% 3.69/1.00      ( v13_waybel_0(sK4,sK3) != iProver_top
% 3.69/1.00      | m1_subset_1(X0,u1_struct_0(sK3)) != iProver_top
% 3.69/1.00      | r2_hidden(X0,sK4) = iProver_top
% 3.69/1.00      | r2_hidden(k3_yellow_0(sK3),sK4) != iProver_top ),
% 3.69/1.00      inference(superposition,[status(thm)],[c_1098,c_1093]) ).
% 3.69/1.00  
% 3.69/1.00  cnf(c_21,negated_conjecture,
% 3.69/1.00      ( v13_waybel_0(sK4,sK3) ),
% 3.69/1.00      inference(cnf_transformation,[],[f69]) ).
% 3.69/1.00  
% 3.69/1.00  cnf(c_32,plain,
% 3.69/1.00      ( v13_waybel_0(sK4,sK3) = iProver_top ),
% 3.69/1.00      inference(predicate_to_equality,[status(thm)],[c_21]) ).
% 3.69/1.00  
% 3.69/1.00  cnf(c_2105,plain,
% 3.69/1.00      ( m1_subset_1(X0,u1_struct_0(sK3)) != iProver_top
% 3.69/1.00      | r2_hidden(X0,sK4) = iProver_top
% 3.69/1.00      | r2_hidden(k3_yellow_0(sK3),sK4) != iProver_top ),
% 3.69/1.00      inference(global_propositional_subsumption,
% 3.69/1.00                [status(thm)],
% 3.69/1.00                [c_2081,c_32]) ).
% 3.69/1.00  
% 3.69/1.00  cnf(c_3746,plain,
% 3.69/1.00      ( m1_subset_1(X0,u1_struct_0(sK3)) != iProver_top
% 3.69/1.00      | r2_hidden(X0,sK4) = iProver_top ),
% 3.69/1.00      inference(superposition,[status(thm)],[c_3740,c_2105]) ).
% 3.69/1.00  
% 3.69/1.00  cnf(c_4351,plain,
% 3.69/1.00      ( u1_struct_0(sK3) = X0
% 3.69/1.00      | r2_hidden(sK0(u1_struct_0(sK3),X0),X0) = iProver_top
% 3.69/1.00      | r2_hidden(sK0(u1_struct_0(sK3),X0),sK4) = iProver_top ),
% 3.69/1.00      inference(superposition,[status(thm)],[c_2463,c_3746]) ).
% 3.69/1.00  
% 3.69/1.00  cnf(c_9056,plain,
% 3.69/1.00      ( u1_struct_0(sK3) = sK4
% 3.69/1.00      | r2_hidden(sK0(u1_struct_0(sK3),sK4),sK4) = iProver_top
% 3.69/1.00      | iProver_top != iProver_top ),
% 3.69/1.00      inference(equality_factoring,[status(thm)],[c_4351]) ).
% 3.69/1.00  
% 3.69/1.00  cnf(c_9058,plain,
% 3.69/1.00      ( u1_struct_0(sK3) = sK4
% 3.69/1.00      | r2_hidden(sK0(u1_struct_0(sK3),sK4),sK4) = iProver_top ),
% 3.69/1.00      inference(equality_resolution_simp,[status(thm)],[c_9056]) ).
% 3.69/1.00  
% 3.69/1.00  cnf(c_1454,plain,
% 3.69/1.00      ( X0 != X1 | X0 = sK4 | sK4 != X1 ),
% 3.69/1.00      inference(instantiation,[status(thm)],[c_721]) ).
% 3.69/1.00  
% 3.69/1.00  cnf(c_2839,plain,
% 3.69/1.00      ( u1_struct_0(sK3) != X0 | u1_struct_0(sK3) = sK4 | sK4 != X0 ),
% 3.69/1.00      inference(instantiation,[status(thm)],[c_1454]) ).
% 3.69/1.00  
% 3.69/1.00  cnf(c_7255,plain,
% 3.69/1.00      ( u1_struct_0(sK3) != u1_struct_0(sK3)
% 3.69/1.00      | u1_struct_0(sK3) = sK4
% 3.69/1.00      | sK4 != u1_struct_0(sK3) ),
% 3.69/1.00      inference(instantiation,[status(thm)],[c_2839]) ).
% 3.69/1.00  
% 3.69/1.00  cnf(c_0,plain,
% 3.69/1.00      ( ~ r2_hidden(sK0(X0,X1),X1)
% 3.69/1.00      | ~ r2_hidden(sK0(X0,X1),X0)
% 3.69/1.00      | X1 = X0 ),
% 3.69/1.00      inference(cnf_transformation,[],[f47]) ).
% 3.69/1.00  
% 3.69/1.00  cnf(c_7,plain,
% 3.69/1.00      ( m1_subset_1(X0,X1)
% 3.69/1.00      | ~ m1_subset_1(X2,k1_zfmisc_1(X1))
% 3.69/1.00      | ~ r2_hidden(X0,X2) ),
% 3.69/1.00      inference(cnf_transformation,[],[f53]) ).
% 3.69/1.00  
% 3.69/1.00  cnf(c_2499,plain,
% 3.69/1.00      ( m1_subset_1(X0,u1_struct_0(sK3)) | ~ r2_hidden(X0,sK4) ),
% 3.69/1.00      inference(resolution,[status(thm)],[c_7,c_20]) ).
% 3.69/1.00  
% 3.69/1.00  cnf(c_2622,plain,
% 3.69/1.00      ( r2_hidden(X0,u1_struct_0(sK3))
% 3.69/1.00      | ~ r2_hidden(X0,sK4)
% 3.69/1.00      | v1_xboole_0(u1_struct_0(sK3)) ),
% 3.69/1.00      inference(resolution,[status(thm)],[c_2499,c_6]) ).
% 3.69/1.00  
% 3.69/1.00  cnf(c_4,plain,
% 3.69/1.00      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
% 3.69/1.00      | ~ v1_xboole_0(X1)
% 3.69/1.00      | v1_xboole_0(X0) ),
% 3.69/1.00      inference(cnf_transformation,[],[f50]) ).
% 3.69/1.00  
% 3.69/1.00  cnf(c_1102,plain,
% 3.69/1.00      ( m1_subset_1(X0,k1_zfmisc_1(X1)) != iProver_top
% 3.69/1.00      | v1_xboole_0(X1) != iProver_top
% 3.69/1.00      | v1_xboole_0(X0) = iProver_top ),
% 3.69/1.00      inference(predicate_to_equality,[status(thm)],[c_4]) ).
% 3.69/1.00  
% 3.69/1.00  cnf(c_2453,plain,
% 3.69/1.00      ( v1_xboole_0(u1_struct_0(sK3)) != iProver_top
% 3.69/1.00      | v1_xboole_0(sK4) = iProver_top ),
% 3.69/1.00      inference(superposition,[status(thm)],[c_1098,c_1102]) ).
% 3.69/1.00  
% 3.69/1.00  cnf(c_2458,plain,
% 3.69/1.00      ( ~ v1_xboole_0(u1_struct_0(sK3)) | v1_xboole_0(sK4) ),
% 3.69/1.00      inference(predicate_to_equality_rev,[status(thm)],[c_2453]) ).
% 3.69/1.00  
% 3.69/1.00  cnf(c_2627,plain,
% 3.69/1.00      ( ~ r2_hidden(X0,sK4) | r2_hidden(X0,u1_struct_0(sK3)) ),
% 3.69/1.00      inference(global_propositional_subsumption,
% 3.69/1.00                [status(thm)],
% 3.69/1.00                [c_2622,c_22,c_2458]) ).
% 3.69/1.00  
% 3.69/1.00  cnf(c_2628,plain,
% 3.69/1.00      ( r2_hidden(X0,u1_struct_0(sK3)) | ~ r2_hidden(X0,sK4) ),
% 3.69/1.00      inference(renaming,[status(thm)],[c_2627]) ).
% 3.69/1.00  
% 3.69/1.00  cnf(c_3533,plain,
% 3.69/1.00      ( ~ r2_hidden(sK0(u1_struct_0(sK3),X0),X0)
% 3.69/1.00      | ~ r2_hidden(sK0(u1_struct_0(sK3),X0),sK4)
% 3.69/1.00      | X0 = u1_struct_0(sK3) ),
% 3.69/1.00      inference(resolution,[status(thm)],[c_0,c_2628]) ).
% 3.69/1.00  
% 3.69/1.00  cnf(c_3792,plain,
% 3.69/1.00      ( r2_hidden(sK0(u1_struct_0(sK3),sK4),u1_struct_0(sK3))
% 3.69/1.00      | ~ r2_hidden(sK0(u1_struct_0(sK3),sK4),sK4)
% 3.69/1.00      | sK4 = u1_struct_0(sK3) ),
% 3.69/1.00      inference(resolution,[status(thm)],[c_3533,c_1]) ).
% 3.69/1.00  
% 3.69/1.00  cnf(c_3300,plain,
% 3.69/1.00      ( ~ r2_hidden(sK0(u1_struct_0(sK3),sK4),u1_struct_0(sK3))
% 3.69/1.00      | ~ r2_hidden(sK0(u1_struct_0(sK3),sK4),sK4)
% 3.69/1.00      | sK4 = u1_struct_0(sK3) ),
% 3.69/1.00      inference(instantiation,[status(thm)],[c_0]) ).
% 3.69/1.00  
% 3.69/1.00  cnf(c_4237,plain,
% 3.69/1.00      ( ~ r2_hidden(sK0(u1_struct_0(sK3),sK4),sK4)
% 3.69/1.00      | sK4 = u1_struct_0(sK3) ),
% 3.69/1.00      inference(global_propositional_subsumption,
% 3.69/1.00                [status(thm)],
% 3.69/1.00                [c_3792,c_3300]) ).
% 3.69/1.00  
% 3.69/1.00  cnf(c_4239,plain,
% 3.69/1.00      ( sK4 = u1_struct_0(sK3)
% 3.69/1.00      | r2_hidden(sK0(u1_struct_0(sK3),sK4),sK4) != iProver_top ),
% 3.69/1.00      inference(predicate_to_equality,[status(thm)],[c_4237]) ).
% 3.69/1.00  
% 3.69/1.00  cnf(c_17,plain,
% 3.69/1.00      ( ~ v1_subset_1(X0,X0) | ~ m1_subset_1(X0,k1_zfmisc_1(X0)) ),
% 3.69/1.00      inference(cnf_transformation,[],[f73]) ).
% 3.69/1.00  
% 3.69/1.00  cnf(c_19,negated_conjecture,
% 3.69/1.00      ( v1_subset_1(sK4,u1_struct_0(sK3))
% 3.69/1.00      | ~ r2_hidden(k3_yellow_0(sK3),sK4) ),
% 3.69/1.00      inference(cnf_transformation,[],[f71]) ).
% 3.69/1.00  
% 3.69/1.00  cnf(c_193,plain,
% 3.69/1.00      ( v1_subset_1(sK4,u1_struct_0(sK3))
% 3.69/1.00      | ~ r2_hidden(k3_yellow_0(sK3),sK4) ),
% 3.69/1.00      inference(prop_impl,[status(thm)],[c_19]) ).
% 3.69/1.00  
% 3.69/1.00  cnf(c_386,plain,
% 3.69/1.00      ( ~ m1_subset_1(X0,k1_zfmisc_1(X0))
% 3.69/1.00      | ~ r2_hidden(k3_yellow_0(sK3),sK4)
% 3.69/1.00      | u1_struct_0(sK3) != X0
% 3.69/1.00      | sK4 != X0 ),
% 3.69/1.00      inference(resolution_lifted,[status(thm)],[c_17,c_193]) ).
% 3.69/1.00  
% 3.69/1.00  cnf(c_387,plain,
% 3.69/1.00      ( ~ m1_subset_1(u1_struct_0(sK3),k1_zfmisc_1(u1_struct_0(sK3)))
% 3.69/1.00      | ~ r2_hidden(k3_yellow_0(sK3),sK4)
% 3.69/1.00      | sK4 != u1_struct_0(sK3) ),
% 3.69/1.00      inference(unflattening,[status(thm)],[c_386]) ).
% 3.69/1.00  
% 3.69/1.00  cnf(c_1094,plain,
% 3.69/1.00      ( sK4 != u1_struct_0(sK3)
% 3.69/1.00      | m1_subset_1(u1_struct_0(sK3),k1_zfmisc_1(u1_struct_0(sK3))) != iProver_top
% 3.69/1.00      | r2_hidden(k3_yellow_0(sK3),sK4) != iProver_top ),
% 3.69/1.00      inference(predicate_to_equality,[status(thm)],[c_387]) ).
% 3.69/1.00  
% 3.69/1.00  cnf(c_3,plain,
% 3.69/1.00      ( m1_subset_1(k2_subset_1(X0),k1_zfmisc_1(X0)) ),
% 3.69/1.00      inference(cnf_transformation,[],[f49]) ).
% 3.69/1.00  
% 3.69/1.00  cnf(c_1103,plain,
% 3.69/1.00      ( m1_subset_1(k2_subset_1(X0),k1_zfmisc_1(X0)) = iProver_top ),
% 3.69/1.00      inference(predicate_to_equality,[status(thm)],[c_3]) ).
% 3.69/1.00  
% 3.69/1.00  cnf(c_2,plain,
% 3.69/1.00      ( k2_subset_1(X0) = X0 ),
% 3.69/1.00      inference(cnf_transformation,[],[f48]) ).
% 3.69/1.00  
% 3.69/1.00  cnf(c_1116,plain,
% 3.69/1.00      ( m1_subset_1(X0,k1_zfmisc_1(X0)) = iProver_top ),
% 3.69/1.00      inference(light_normalisation,[status(thm)],[c_1103,c_2]) ).
% 3.69/1.00  
% 3.69/1.00  cnf(c_1184,plain,
% 3.69/1.00      ( u1_struct_0(sK3) != sK4
% 3.69/1.00      | r2_hidden(k3_yellow_0(sK3),sK4) != iProver_top ),
% 3.69/1.00      inference(forward_subsumption_resolution,
% 3.69/1.00                [status(thm)],
% 3.69/1.00                [c_1094,c_1116]) ).
% 3.69/1.00  
% 3.69/1.00  cnf(c_727,plain,
% 3.69/1.00      ( X0 != X1 | u1_struct_0(X0) = u1_struct_0(X1) ),
% 3.69/1.00      theory(equality) ).
% 3.69/1.00  
% 3.69/1.00  cnf(c_736,plain,
% 3.69/1.00      ( u1_struct_0(sK3) = u1_struct_0(sK3) | sK3 != sK3 ),
% 3.69/1.00      inference(instantiation,[status(thm)],[c_727]) ).
% 3.69/1.00  
% 3.69/1.00  cnf(contradiction,plain,
% 3.69/1.00      ( $false ),
% 3.69/1.00      inference(minisat,
% 3.69/1.00                [status(thm)],
% 3.69/1.00                [c_9058,c_7255,c_4239,c_3480,c_1184,c_741,c_736,c_31]) ).
% 3.69/1.00  
% 3.69/1.00  
% 3.69/1.00  % SZS output end CNFRefutation for theBenchmark.p
% 3.69/1.00  
% 3.69/1.00  ------                               Statistics
% 3.69/1.00  
% 3.69/1.00  ------ Selected
% 3.69/1.00  
% 3.69/1.00  total_time:                             0.225
% 3.69/1.00  
%------------------------------------------------------------------------------
