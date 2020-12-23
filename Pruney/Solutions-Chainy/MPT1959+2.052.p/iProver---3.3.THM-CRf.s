%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n010.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:28:35 EST 2020

% Result     : Theorem 2.71s
% Output     : CNFRefutation 2.71s
% Verified   : 
% Statistics : Number of formulae       :  159 (1034 expanded)
%              Number of clauses        :   94 ( 307 expanded)
%              Number of leaves         :   20 ( 209 expanded)
%              Depth                    :   29
%              Number of atoms          :  615 (7338 expanded)
%              Number of equality atoms :  140 ( 445 expanded)
%              Maximal formula depth    :   14 (   5 average)
%              Maximal clause size      :   22 (   3 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
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

fof(f71,plain,(
    m1_subset_1(sK5,k1_zfmisc_1(u1_struct_0(sK4))) ),
    inference(cnf_transformation,[],[f46])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => ! [X2] :
          ( r2_hidden(X2,X1)
         => r2_hidden(X2,X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f17,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( r2_hidden(X2,X0)
          | ~ r2_hidden(X2,X1) )
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f49,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(X2,X0)
      | ~ r2_hidden(X2,X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f17])).

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

fof(f69,plain,(
    ~ v1_xboole_0(sK5) ),
    inference(cnf_transformation,[],[f46])).

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

fof(f73,plain,
    ( r2_hidden(k3_yellow_0(sK4),sK5)
    | ~ v1_subset_1(sK5,u1_struct_0(sK4)) ),
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

fof(f63,plain,(
    ! [X0,X1] :
      ( X0 != X1
      | ~ v1_subset_1(X1,X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f41])).

fof(f74,plain,(
    ! [X1] :
      ( ~ v1_subset_1(X1,X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X1)) ) ),
    inference(equality_resolution,[],[f63])).

fof(f72,plain,
    ( ~ r2_hidden(k3_yellow_0(sK4),sK5)
    | v1_subset_1(sK5,u1_struct_0(sK4)) ),
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

fof(f51,plain,(
    ! [X0] : ~ v1_subset_1(sK1(X0),X0) ),
    inference(cnf_transformation,[],[f35])).

fof(f48,plain,(
    ! [X0,X1] :
      ( X0 = X1
      | ~ r2_hidden(sK0(X0,X1),X1)
      | ~ r2_hidden(sK0(X0,X1),X0) ) ),
    inference(cnf_transformation,[],[f33])).

cnf(c_20,negated_conjecture,
    ( m1_subset_1(sK5,k1_zfmisc_1(u1_struct_0(sK4))) ),
    inference(cnf_transformation,[],[f71])).

cnf(c_1118,plain,
    ( m1_subset_1(sK5,k1_zfmisc_1(u1_struct_0(sK4))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_20])).

cnf(c_2,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | ~ r2_hidden(X2,X0)
    | r2_hidden(X2,X1) ),
    inference(cnf_transformation,[],[f49])).

cnf(c_1122,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(X1)) != iProver_top
    | r2_hidden(X2,X0) != iProver_top
    | r2_hidden(X2,X1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2])).

cnf(c_1589,plain,
    ( r2_hidden(X0,u1_struct_0(sK4)) = iProver_top
    | r2_hidden(X0,sK5) != iProver_top ),
    inference(superposition,[status(thm)],[c_1118,c_1122])).

cnf(c_1,plain,
    ( r2_hidden(sK0(X0,X1),X1)
    | r2_hidden(sK0(X0,X1),X0)
    | X1 = X0 ),
    inference(cnf_transformation,[],[f47])).

cnf(c_1123,plain,
    ( X0 = X1
    | r2_hidden(sK0(X1,X0),X0) = iProver_top
    | r2_hidden(sK0(X1,X0),X1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1])).

cnf(c_5,plain,
    ( m1_subset_1(X0,X1)
    | ~ r2_hidden(X0,X1) ),
    inference(cnf_transformation,[],[f52])).

cnf(c_1120,plain,
    ( m1_subset_1(X0,X1) = iProver_top
    | r2_hidden(X0,X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_5])).

cnf(c_1553,plain,
    ( X0 = X1
    | m1_subset_1(sK0(X0,X1),X0) = iProver_top
    | r2_hidden(sK0(X0,X1),X1) = iProver_top ),
    inference(superposition,[status(thm)],[c_1123,c_1120])).

cnf(c_2110,plain,
    ( X0 = X1
    | m1_subset_1(sK0(X1,X0),X1) = iProver_top
    | m1_subset_1(sK0(X1,X0),X0) = iProver_top ),
    inference(superposition,[status(thm)],[c_1553,c_1120])).

cnf(c_6,plain,
    ( ~ m1_subset_1(X0,X1)
    | r2_hidden(X0,X1)
    | v1_xboole_0(X1) ),
    inference(cnf_transformation,[],[f53])).

cnf(c_22,negated_conjecture,
    ( ~ v1_xboole_0(sK5) ),
    inference(cnf_transformation,[],[f69])).

cnf(c_357,plain,
    ( ~ m1_subset_1(X0,X1)
    | r2_hidden(X0,X1)
    | sK5 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_6,c_22])).

cnf(c_358,plain,
    ( ~ m1_subset_1(X0,sK5)
    | r2_hidden(X0,sK5) ),
    inference(unflattening,[status(thm)],[c_357])).

cnf(c_1116,plain,
    ( m1_subset_1(X0,sK5) != iProver_top
    | r2_hidden(X0,sK5) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_358])).

cnf(c_2943,plain,
    ( sK5 = X0
    | m1_subset_1(sK0(X0,sK5),X0) = iProver_top
    | r2_hidden(sK0(X0,sK5),sK5) = iProver_top ),
    inference(superposition,[status(thm)],[c_2110,c_1116])).

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

cnf(c_417,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | r2_hidden(k3_yellow_0(sK4),sK5)
    | X1 = X0
    | u1_struct_0(sK4) != X1
    | sK5 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_16,c_201])).

cnf(c_418,plain,
    ( ~ m1_subset_1(sK5,k1_zfmisc_1(u1_struct_0(sK4)))
    | r2_hidden(k3_yellow_0(sK4),sK5)
    | u1_struct_0(sK4) = sK5 ),
    inference(unflattening,[status(thm)],[c_417])).

cnf(c_420,plain,
    ( r2_hidden(k3_yellow_0(sK4),sK5)
    | u1_struct_0(sK4) = sK5 ),
    inference(global_propositional_subsumption,[status(thm)],[c_418,c_20])).

cnf(c_1114,plain,
    ( u1_struct_0(sK4) = sK5
    | r2_hidden(k3_yellow_0(sK4),sK5) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_420])).

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

cnf(c_372,plain,
    ( r1_orders_2(X0,k3_yellow_0(X0),X1)
    | ~ m1_subset_1(X1,u1_struct_0(X0))
    | v2_struct_0(X0)
    | ~ v5_orders_2(X0)
    | ~ l1_orders_2(X0)
    | sK4 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_9,c_24])).

cnf(c_373,plain,
    ( r1_orders_2(sK4,k3_yellow_0(sK4),X0)
    | ~ m1_subset_1(X0,u1_struct_0(sK4))
    | v2_struct_0(sK4)
    | ~ v5_orders_2(sK4)
    | ~ l1_orders_2(sK4) ),
    inference(unflattening,[status(thm)],[c_372])).

cnf(c_26,negated_conjecture,
    ( ~ v2_struct_0(sK4) ),
    inference(cnf_transformation,[],[f65])).

cnf(c_25,negated_conjecture,
    ( v5_orders_2(sK4) ),
    inference(cnf_transformation,[],[f66])).

cnf(c_23,negated_conjecture,
    ( l1_orders_2(sK4) ),
    inference(cnf_transformation,[],[f68])).

cnf(c_377,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(sK4))
    | r1_orders_2(sK4,k3_yellow_0(sK4),X0) ),
    inference(global_propositional_subsumption,[status(thm)],[c_373,c_26,c_25,c_23])).

cnf(c_378,plain,
    ( r1_orders_2(sK4,k3_yellow_0(sK4),X0)
    | ~ m1_subset_1(X0,u1_struct_0(sK4)) ),
    inference(renaming,[status(thm)],[c_377])).

cnf(c_485,plain,
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
    inference(resolution_lifted,[status(thm)],[c_15,c_378])).

cnf(c_486,plain,
    ( ~ v13_waybel_0(X0,sK4)
    | ~ m1_subset_1(X1,u1_struct_0(sK4))
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK4)))
    | ~ m1_subset_1(k3_yellow_0(sK4),u1_struct_0(sK4))
    | r2_hidden(X1,X0)
    | ~ r2_hidden(k3_yellow_0(sK4),X0)
    | ~ l1_orders_2(sK4) ),
    inference(unflattening,[status(thm)],[c_485])).

cnf(c_8,plain,
    ( m1_subset_1(k3_yellow_0(X0),u1_struct_0(X0))
    | ~ l1_orders_2(X0) ),
    inference(cnf_transformation,[],[f55])).

cnf(c_62,plain,
    ( m1_subset_1(k3_yellow_0(sK4),u1_struct_0(sK4))
    | ~ l1_orders_2(sK4) ),
    inference(instantiation,[status(thm)],[c_8])).

cnf(c_490,plain,
    ( ~ r2_hidden(k3_yellow_0(sK4),X0)
    | r2_hidden(X1,X0)
    | ~ v13_waybel_0(X0,sK4)
    | ~ m1_subset_1(X1,u1_struct_0(sK4))
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK4))) ),
    inference(global_propositional_subsumption,[status(thm)],[c_486,c_23,c_62])).

cnf(c_491,plain,
    ( ~ v13_waybel_0(X0,sK4)
    | ~ m1_subset_1(X1,u1_struct_0(sK4))
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK4)))
    | r2_hidden(X1,X0)
    | ~ r2_hidden(k3_yellow_0(sK4),X0) ),
    inference(renaming,[status(thm)],[c_490])).

cnf(c_1112,plain,
    ( v13_waybel_0(X0,sK4) != iProver_top
    | m1_subset_1(X1,u1_struct_0(sK4)) != iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK4))) != iProver_top
    | r2_hidden(X1,X0) = iProver_top
    | r2_hidden(k3_yellow_0(sK4),X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_491])).

cnf(c_1695,plain,
    ( v13_waybel_0(sK5,sK4) != iProver_top
    | m1_subset_1(X0,u1_struct_0(sK4)) != iProver_top
    | r2_hidden(X0,sK5) = iProver_top
    | r2_hidden(k3_yellow_0(sK4),sK5) != iProver_top ),
    inference(superposition,[status(thm)],[c_1118,c_1112])).

cnf(c_21,negated_conjecture,
    ( v13_waybel_0(sK5,sK4) ),
    inference(cnf_transformation,[],[f70])).

cnf(c_32,plain,
    ( v13_waybel_0(sK5,sK4) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_21])).

cnf(c_1700,plain,
    ( m1_subset_1(X0,u1_struct_0(sK4)) != iProver_top
    | r2_hidden(X0,sK5) = iProver_top
    | r2_hidden(k3_yellow_0(sK4),sK5) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_1695,c_32])).

cnf(c_1837,plain,
    ( u1_struct_0(sK4) = sK5
    | m1_subset_1(X0,u1_struct_0(sK4)) != iProver_top
    | r2_hidden(X0,sK5) = iProver_top ),
    inference(superposition,[status(thm)],[c_1114,c_1700])).

cnf(c_3400,plain,
    ( u1_struct_0(sK4) = sK5
    | r2_hidden(sK0(u1_struct_0(sK4),sK5),sK5) = iProver_top ),
    inference(superposition,[status(thm)],[c_2943,c_1837])).

cnf(c_30,plain,
    ( l1_orders_2(sK4) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_23])).

cnf(c_61,plain,
    ( m1_subset_1(k3_yellow_0(X0),u1_struct_0(X0)) = iProver_top
    | l1_orders_2(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_8])).

cnf(c_63,plain,
    ( m1_subset_1(k3_yellow_0(sK4),u1_struct_0(sK4)) = iProver_top
    | l1_orders_2(sK4) != iProver_top ),
    inference(instantiation,[status(thm)],[c_61])).

cnf(c_17,plain,
    ( ~ v1_subset_1(X0,X0)
    | ~ m1_subset_1(X0,k1_zfmisc_1(X0)) ),
    inference(cnf_transformation,[],[f74])).

cnf(c_19,negated_conjecture,
    ( v1_subset_1(sK5,u1_struct_0(sK4))
    | ~ r2_hidden(k3_yellow_0(sK4),sK5) ),
    inference(cnf_transformation,[],[f72])).

cnf(c_199,plain,
    ( v1_subset_1(sK5,u1_struct_0(sK4))
    | ~ r2_hidden(k3_yellow_0(sK4),sK5) ),
    inference(prop_impl,[status(thm)],[c_19])).

cnf(c_431,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X0))
    | ~ r2_hidden(k3_yellow_0(sK4),sK5)
    | u1_struct_0(sK4) != X0
    | sK5 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_17,c_199])).

cnf(c_432,plain,
    ( ~ m1_subset_1(u1_struct_0(sK4),k1_zfmisc_1(u1_struct_0(sK4)))
    | ~ r2_hidden(k3_yellow_0(sK4),sK5)
    | sK5 != u1_struct_0(sK4) ),
    inference(unflattening,[status(thm)],[c_431])).

cnf(c_433,plain,
    ( sK5 != u1_struct_0(sK4)
    | m1_subset_1(u1_struct_0(sK4),k1_zfmisc_1(u1_struct_0(sK4))) != iProver_top
    | r2_hidden(k3_yellow_0(sK4),sK5) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_432])).

cnf(c_777,plain,
    ( X0 != X1
    | k3_yellow_0(X0) = k3_yellow_0(X1) ),
    theory(equality)).

cnf(c_786,plain,
    ( k3_yellow_0(sK4) = k3_yellow_0(sK4)
    | sK4 != sK4 ),
    inference(instantiation,[status(thm)],[c_777])).

cnf(c_771,plain,
    ( X0 = X0 ),
    theory(equality)).

cnf(c_792,plain,
    ( sK4 = sK4 ),
    inference(instantiation,[status(thm)],[c_771])).

cnf(c_4,plain,
    ( m1_subset_1(sK1(X0),k1_zfmisc_1(X0)) ),
    inference(cnf_transformation,[],[f50])).

cnf(c_1287,plain,
    ( m1_subset_1(sK1(u1_struct_0(sK4)),k1_zfmisc_1(u1_struct_0(sK4))) ),
    inference(instantiation,[status(thm)],[c_4])).

cnf(c_1292,plain,
    ( m1_subset_1(sK1(u1_struct_0(sK4)),k1_zfmisc_1(u1_struct_0(sK4))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1287])).

cnf(c_1403,plain,
    ( sK5 = sK5 ),
    inference(instantiation,[status(thm)],[c_771])).

cnf(c_1464,plain,
    ( k1_zfmisc_1(u1_struct_0(sK4)) = k1_zfmisc_1(u1_struct_0(sK4)) ),
    inference(instantiation,[status(thm)],[c_771])).

cnf(c_775,plain,
    ( ~ m1_subset_1(X0,X1)
    | m1_subset_1(X2,X3)
    | X2 != X0
    | X3 != X1 ),
    theory(equality)).

cnf(c_1347,plain,
    ( m1_subset_1(X0,X1)
    | ~ m1_subset_1(k3_yellow_0(sK4),u1_struct_0(sK4))
    | X1 != u1_struct_0(sK4)
    | X0 != k3_yellow_0(sK4) ),
    inference(instantiation,[status(thm)],[c_775])).

cnf(c_1579,plain,
    ( m1_subset_1(X0,sK5)
    | ~ m1_subset_1(k3_yellow_0(sK4),u1_struct_0(sK4))
    | X0 != k3_yellow_0(sK4)
    | sK5 != u1_struct_0(sK4) ),
    inference(instantiation,[status(thm)],[c_1347])).

cnf(c_1739,plain,
    ( ~ m1_subset_1(k3_yellow_0(sK4),u1_struct_0(sK4))
    | m1_subset_1(k3_yellow_0(sK4),sK5)
    | k3_yellow_0(sK4) != k3_yellow_0(sK4)
    | sK5 != u1_struct_0(sK4) ),
    inference(instantiation,[status(thm)],[c_1579])).

cnf(c_1741,plain,
    ( k3_yellow_0(sK4) != k3_yellow_0(sK4)
    | sK5 != u1_struct_0(sK4)
    | m1_subset_1(k3_yellow_0(sK4),u1_struct_0(sK4)) != iProver_top
    | m1_subset_1(k3_yellow_0(sK4),sK5) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1739])).

cnf(c_3,plain,
    ( ~ v1_subset_1(sK1(X0),X0) ),
    inference(cnf_transformation,[],[f51])).

cnf(c_394,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | X1 != X2
    | X1 = X0
    | sK1(X2) != X0 ),
    inference(resolution_lifted,[status(thm)],[c_3,c_16])).

cnf(c_395,plain,
    ( ~ m1_subset_1(sK1(X0),k1_zfmisc_1(X0))
    | X0 = sK1(X0) ),
    inference(unflattening,[status(thm)],[c_394])).

cnf(c_399,plain,
    ( X0 = sK1(X0) ),
    inference(global_propositional_subsumption,[status(thm)],[c_395,c_4])).

cnf(c_2563,plain,
    ( u1_struct_0(sK4) = sK1(u1_struct_0(sK4)) ),
    inference(instantiation,[status(thm)],[c_399])).

cnf(c_772,plain,
    ( X0 != X1
    | X2 != X1
    | X2 = X0 ),
    theory(equality)).

cnf(c_1359,plain,
    ( u1_struct_0(sK4) != X0
    | sK5 != X0
    | sK5 = u1_struct_0(sK4) ),
    inference(instantiation,[status(thm)],[c_772])).

cnf(c_2735,plain,
    ( u1_struct_0(sK4) != sK5
    | sK5 = u1_struct_0(sK4)
    | sK5 != sK5 ),
    inference(instantiation,[status(thm)],[c_1359])).

cnf(c_4278,plain,
    ( ~ m1_subset_1(k3_yellow_0(sK4),sK5)
    | r2_hidden(k3_yellow_0(sK4),sK5) ),
    inference(instantiation,[status(thm)],[c_358])).

cnf(c_4279,plain,
    ( m1_subset_1(k3_yellow_0(sK4),sK5) != iProver_top
    | r2_hidden(k3_yellow_0(sK4),sK5) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_4278])).

cnf(c_1337,plain,
    ( m1_subset_1(X0,X1)
    | ~ m1_subset_1(sK1(X2),k1_zfmisc_1(X2))
    | X0 != sK1(X2)
    | X1 != k1_zfmisc_1(X2) ),
    inference(instantiation,[status(thm)],[c_775])).

cnf(c_1538,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(X1))
    | ~ m1_subset_1(sK1(X1),k1_zfmisc_1(X1))
    | X0 != sK1(X1)
    | k1_zfmisc_1(X1) != k1_zfmisc_1(X1) ),
    inference(instantiation,[status(thm)],[c_1337])).

cnf(c_1884,plain,
    ( m1_subset_1(u1_struct_0(sK4),k1_zfmisc_1(X0))
    | ~ m1_subset_1(sK1(X0),k1_zfmisc_1(X0))
    | u1_struct_0(sK4) != sK1(X0)
    | k1_zfmisc_1(X0) != k1_zfmisc_1(X0) ),
    inference(instantiation,[status(thm)],[c_1538])).

cnf(c_5802,plain,
    ( m1_subset_1(u1_struct_0(sK4),k1_zfmisc_1(u1_struct_0(sK4)))
    | ~ m1_subset_1(sK1(u1_struct_0(sK4)),k1_zfmisc_1(u1_struct_0(sK4)))
    | u1_struct_0(sK4) != sK1(u1_struct_0(sK4))
    | k1_zfmisc_1(u1_struct_0(sK4)) != k1_zfmisc_1(u1_struct_0(sK4)) ),
    inference(instantiation,[status(thm)],[c_1884])).

cnf(c_5803,plain,
    ( u1_struct_0(sK4) != sK1(u1_struct_0(sK4))
    | k1_zfmisc_1(u1_struct_0(sK4)) != k1_zfmisc_1(u1_struct_0(sK4))
    | m1_subset_1(u1_struct_0(sK4),k1_zfmisc_1(u1_struct_0(sK4))) = iProver_top
    | m1_subset_1(sK1(u1_struct_0(sK4)),k1_zfmisc_1(u1_struct_0(sK4))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_5802])).

cnf(c_7513,plain,
    ( r2_hidden(sK0(u1_struct_0(sK4),sK5),sK5) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_3400,c_30,c_63,c_433,c_786,c_792,c_1292,c_1403,c_1464,c_1741,c_2563,c_2735,c_4279,c_5803])).

cnf(c_0,plain,
    ( ~ r2_hidden(sK0(X0,X1),X1)
    | ~ r2_hidden(sK0(X0,X1),X0)
    | X1 = X0 ),
    inference(cnf_transformation,[],[f48])).

cnf(c_1124,plain,
    ( X0 = X1
    | r2_hidden(sK0(X1,X0),X0) != iProver_top
    | r2_hidden(sK0(X1,X0),X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_0])).

cnf(c_7519,plain,
    ( u1_struct_0(sK4) = sK5
    | r2_hidden(sK0(u1_struct_0(sK4),sK5),u1_struct_0(sK4)) != iProver_top ),
    inference(superposition,[status(thm)],[c_7513,c_1124])).

cnf(c_1323,plain,
    ( ~ r2_hidden(sK0(u1_struct_0(sK4),sK5),u1_struct_0(sK4))
    | ~ r2_hidden(sK0(u1_struct_0(sK4),sK5),sK5)
    | sK5 = u1_struct_0(sK4) ),
    inference(instantiation,[status(thm)],[c_0])).

cnf(c_1324,plain,
    ( sK5 = u1_struct_0(sK4)
    | r2_hidden(sK0(u1_struct_0(sK4),sK5),u1_struct_0(sK4)) != iProver_top
    | r2_hidden(sK0(u1_struct_0(sK4),sK5),sK5) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1323])).

cnf(c_7962,plain,
    ( r2_hidden(sK0(u1_struct_0(sK4),sK5),u1_struct_0(sK4)) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_7519,c_30,c_63,c_433,c_786,c_792,c_1292,c_1324,c_1403,c_1464,c_1741,c_2563,c_2735,c_3400,c_4279,c_5803])).

cnf(c_7970,plain,
    ( r2_hidden(sK0(u1_struct_0(sK4),sK5),sK5) != iProver_top ),
    inference(superposition,[status(thm)],[c_1589,c_7962])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_7970,c_7513])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : iproveropt_run.sh %d %s
% 0.14/0.34  % Computer   : n010.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % WCLimit    : 600
% 0.14/0.35  % DateTime   : Tue Dec  1 10:04:59 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.14/0.35  % Running in FOF mode
% 2.71/1.04  % SZS status Started for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.71/1.04  
% 2.71/1.04  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 2.71/1.04  
% 2.71/1.04  ------  iProver source info
% 2.71/1.04  
% 2.71/1.04  git: date: 2020-06-30 10:37:57 +0100
% 2.71/1.04  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 2.71/1.04  git: non_committed_changes: false
% 2.71/1.04  git: last_make_outside_of_git: false
% 2.71/1.04  
% 2.71/1.04  ------ 
% 2.71/1.04  
% 2.71/1.04  ------ Input Options
% 2.71/1.04  
% 2.71/1.04  --out_options                           all
% 2.71/1.04  --tptp_safe_out                         true
% 2.71/1.04  --problem_path                          ""
% 2.71/1.04  --include_path                          ""
% 2.71/1.04  --clausifier                            res/vclausify_rel
% 2.71/1.04  --clausifier_options                    --mode clausify
% 2.71/1.04  --stdin                                 false
% 2.71/1.04  --stats_out                             all
% 2.71/1.04  
% 2.71/1.04  ------ General Options
% 2.71/1.04  
% 2.71/1.04  --fof                                   false
% 2.71/1.04  --time_out_real                         305.
% 2.71/1.04  --time_out_virtual                      -1.
% 2.71/1.04  --symbol_type_check                     false
% 2.71/1.04  --clausify_out                          false
% 2.71/1.04  --sig_cnt_out                           false
% 2.71/1.04  --trig_cnt_out                          false
% 2.71/1.04  --trig_cnt_out_tolerance                1.
% 2.71/1.04  --trig_cnt_out_sk_spl                   false
% 2.71/1.04  --abstr_cl_out                          false
% 2.71/1.04  
% 2.71/1.04  ------ Global Options
% 2.71/1.04  
% 2.71/1.04  --schedule                              default
% 2.71/1.04  --add_important_lit                     false
% 2.71/1.04  --prop_solver_per_cl                    1000
% 2.71/1.04  --min_unsat_core                        false
% 2.71/1.04  --soft_assumptions                      false
% 2.71/1.04  --soft_lemma_size                       3
% 2.71/1.04  --prop_impl_unit_size                   0
% 2.71/1.04  --prop_impl_unit                        []
% 2.71/1.04  --share_sel_clauses                     true
% 2.71/1.04  --reset_solvers                         false
% 2.71/1.04  --bc_imp_inh                            [conj_cone]
% 2.71/1.04  --conj_cone_tolerance                   3.
% 2.71/1.04  --extra_neg_conj                        none
% 2.71/1.04  --large_theory_mode                     true
% 2.71/1.04  --prolific_symb_bound                   200
% 2.71/1.04  --lt_threshold                          2000
% 2.71/1.04  --clause_weak_htbl                      true
% 2.71/1.04  --gc_record_bc_elim                     false
% 2.71/1.04  
% 2.71/1.04  ------ Preprocessing Options
% 2.71/1.04  
% 2.71/1.04  --preprocessing_flag                    true
% 2.71/1.04  --time_out_prep_mult                    0.1
% 2.71/1.04  --splitting_mode                        input
% 2.71/1.04  --splitting_grd                         true
% 2.71/1.04  --splitting_cvd                         false
% 2.71/1.04  --splitting_cvd_svl                     false
% 2.71/1.04  --splitting_nvd                         32
% 2.71/1.04  --sub_typing                            true
% 2.71/1.04  --prep_gs_sim                           true
% 2.71/1.04  --prep_unflatten                        true
% 2.71/1.04  --prep_res_sim                          true
% 2.71/1.04  --prep_upred                            true
% 2.71/1.04  --prep_sem_filter                       exhaustive
% 2.71/1.04  --prep_sem_filter_out                   false
% 2.71/1.04  --pred_elim                             true
% 2.71/1.04  --res_sim_input                         true
% 2.71/1.04  --eq_ax_congr_red                       true
% 2.71/1.04  --pure_diseq_elim                       true
% 2.71/1.04  --brand_transform                       false
% 2.71/1.04  --non_eq_to_eq                          false
% 2.71/1.04  --prep_def_merge                        true
% 2.71/1.04  --prep_def_merge_prop_impl              false
% 2.71/1.04  --prep_def_merge_mbd                    true
% 2.71/1.04  --prep_def_merge_tr_red                 false
% 2.71/1.04  --prep_def_merge_tr_cl                  false
% 2.71/1.04  --smt_preprocessing                     true
% 2.71/1.04  --smt_ac_axioms                         fast
% 2.71/1.04  --preprocessed_out                      false
% 2.71/1.04  --preprocessed_stats                    false
% 2.71/1.04  
% 2.71/1.04  ------ Abstraction refinement Options
% 2.71/1.04  
% 2.71/1.04  --abstr_ref                             []
% 2.71/1.04  --abstr_ref_prep                        false
% 2.71/1.04  --abstr_ref_until_sat                   false
% 2.71/1.04  --abstr_ref_sig_restrict                funpre
% 2.71/1.04  --abstr_ref_af_restrict_to_split_sk     false
% 2.71/1.04  --abstr_ref_under                       []
% 2.71/1.04  
% 2.71/1.04  ------ SAT Options
% 2.71/1.04  
% 2.71/1.04  --sat_mode                              false
% 2.71/1.04  --sat_fm_restart_options                ""
% 2.71/1.04  --sat_gr_def                            false
% 2.71/1.04  --sat_epr_types                         true
% 2.71/1.04  --sat_non_cyclic_types                  false
% 2.71/1.04  --sat_finite_models                     false
% 2.71/1.04  --sat_fm_lemmas                         false
% 2.71/1.04  --sat_fm_prep                           false
% 2.71/1.04  --sat_fm_uc_incr                        true
% 2.71/1.04  --sat_out_model                         small
% 2.71/1.04  --sat_out_clauses                       false
% 2.71/1.04  
% 2.71/1.04  ------ QBF Options
% 2.71/1.04  
% 2.71/1.04  --qbf_mode                              false
% 2.71/1.04  --qbf_elim_univ                         false
% 2.71/1.04  --qbf_dom_inst                          none
% 2.71/1.04  --qbf_dom_pre_inst                      false
% 2.71/1.04  --qbf_sk_in                             false
% 2.71/1.04  --qbf_pred_elim                         true
% 2.71/1.04  --qbf_split                             512
% 2.71/1.04  
% 2.71/1.04  ------ BMC1 Options
% 2.71/1.04  
% 2.71/1.04  --bmc1_incremental                      false
% 2.71/1.04  --bmc1_axioms                           reachable_all
% 2.71/1.04  --bmc1_min_bound                        0
% 2.71/1.04  --bmc1_max_bound                        -1
% 2.71/1.04  --bmc1_max_bound_default                -1
% 2.71/1.04  --bmc1_symbol_reachability              true
% 2.71/1.04  --bmc1_property_lemmas                  false
% 2.71/1.04  --bmc1_k_induction                      false
% 2.71/1.04  --bmc1_non_equiv_states                 false
% 2.71/1.04  --bmc1_deadlock                         false
% 2.71/1.04  --bmc1_ucm                              false
% 2.71/1.04  --bmc1_add_unsat_core                   none
% 2.71/1.04  --bmc1_unsat_core_children              false
% 2.71/1.04  --bmc1_unsat_core_extrapolate_axioms    false
% 2.71/1.04  --bmc1_out_stat                         full
% 2.71/1.04  --bmc1_ground_init                      false
% 2.71/1.04  --bmc1_pre_inst_next_state              false
% 2.71/1.04  --bmc1_pre_inst_state                   false
% 2.71/1.04  --bmc1_pre_inst_reach_state             false
% 2.71/1.04  --bmc1_out_unsat_core                   false
% 2.71/1.04  --bmc1_aig_witness_out                  false
% 2.71/1.04  --bmc1_verbose                          false
% 2.71/1.04  --bmc1_dump_clauses_tptp                false
% 2.71/1.04  --bmc1_dump_unsat_core_tptp             false
% 2.71/1.04  --bmc1_dump_file                        -
% 2.71/1.04  --bmc1_ucm_expand_uc_limit              128
% 2.71/1.04  --bmc1_ucm_n_expand_iterations          6
% 2.71/1.04  --bmc1_ucm_extend_mode                  1
% 2.71/1.04  --bmc1_ucm_init_mode                    2
% 2.71/1.04  --bmc1_ucm_cone_mode                    none
% 2.71/1.04  --bmc1_ucm_reduced_relation_type        0
% 2.71/1.04  --bmc1_ucm_relax_model                  4
% 2.71/1.04  --bmc1_ucm_full_tr_after_sat            true
% 2.71/1.04  --bmc1_ucm_expand_neg_assumptions       false
% 2.71/1.04  --bmc1_ucm_layered_model                none
% 2.71/1.04  --bmc1_ucm_max_lemma_size               10
% 2.71/1.04  
% 2.71/1.04  ------ AIG Options
% 2.71/1.04  
% 2.71/1.04  --aig_mode                              false
% 2.71/1.04  
% 2.71/1.04  ------ Instantiation Options
% 2.71/1.04  
% 2.71/1.04  --instantiation_flag                    true
% 2.71/1.04  --inst_sos_flag                         false
% 2.71/1.04  --inst_sos_phase                        true
% 2.71/1.04  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 2.71/1.04  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 2.71/1.04  --inst_lit_sel_side                     num_symb
% 2.71/1.04  --inst_solver_per_active                1400
% 2.71/1.04  --inst_solver_calls_frac                1.
% 2.71/1.04  --inst_passive_queue_type               priority_queues
% 2.71/1.04  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 2.71/1.04  --inst_passive_queues_freq              [25;2]
% 2.71/1.04  --inst_dismatching                      true
% 2.71/1.04  --inst_eager_unprocessed_to_passive     true
% 2.71/1.04  --inst_prop_sim_given                   true
% 2.71/1.04  --inst_prop_sim_new                     false
% 2.71/1.04  --inst_subs_new                         false
% 2.71/1.04  --inst_eq_res_simp                      false
% 2.71/1.04  --inst_subs_given                       false
% 2.71/1.04  --inst_orphan_elimination               true
% 2.71/1.04  --inst_learning_loop_flag               true
% 2.71/1.04  --inst_learning_start                   3000
% 2.71/1.04  --inst_learning_factor                  2
% 2.71/1.04  --inst_start_prop_sim_after_learn       3
% 2.71/1.04  --inst_sel_renew                        solver
% 2.71/1.04  --inst_lit_activity_flag                true
% 2.71/1.04  --inst_restr_to_given                   false
% 2.71/1.04  --inst_activity_threshold               500
% 2.71/1.04  --inst_out_proof                        true
% 2.71/1.04  
% 2.71/1.04  ------ Resolution Options
% 2.71/1.04  
% 2.71/1.04  --resolution_flag                       true
% 2.71/1.04  --res_lit_sel                           adaptive
% 2.71/1.04  --res_lit_sel_side                      none
% 2.71/1.04  --res_ordering                          kbo
% 2.71/1.04  --res_to_prop_solver                    active
% 2.71/1.04  --res_prop_simpl_new                    false
% 2.71/1.04  --res_prop_simpl_given                  true
% 2.71/1.04  --res_passive_queue_type                priority_queues
% 2.71/1.04  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 2.71/1.04  --res_passive_queues_freq               [15;5]
% 2.71/1.04  --res_forward_subs                      full
% 2.71/1.04  --res_backward_subs                     full
% 2.71/1.04  --res_forward_subs_resolution           true
% 2.71/1.04  --res_backward_subs_resolution          true
% 2.71/1.04  --res_orphan_elimination                true
% 2.71/1.04  --res_time_limit                        2.
% 2.71/1.04  --res_out_proof                         true
% 2.71/1.04  
% 2.71/1.04  ------ Superposition Options
% 2.71/1.04  
% 2.71/1.04  --superposition_flag                    true
% 2.71/1.04  --sup_passive_queue_type                priority_queues
% 2.71/1.04  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 2.71/1.04  --sup_passive_queues_freq               [8;1;4]
% 2.71/1.04  --demod_completeness_check              fast
% 2.71/1.04  --demod_use_ground                      true
% 2.71/1.04  --sup_to_prop_solver                    passive
% 2.71/1.04  --sup_prop_simpl_new                    true
% 2.71/1.04  --sup_prop_simpl_given                  true
% 2.71/1.04  --sup_fun_splitting                     false
% 2.71/1.04  --sup_smt_interval                      50000
% 2.71/1.04  
% 2.71/1.04  ------ Superposition Simplification Setup
% 2.71/1.04  
% 2.71/1.04  --sup_indices_passive                   []
% 2.71/1.04  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.71/1.04  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.71/1.04  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.71/1.04  --sup_full_triv                         [TrivRules;PropSubs]
% 2.71/1.04  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.71/1.04  --sup_full_bw                           [BwDemod]
% 2.71/1.04  --sup_immed_triv                        [TrivRules]
% 2.71/1.04  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 2.71/1.04  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.71/1.04  --sup_immed_bw_main                     []
% 2.71/1.04  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.71/1.04  --sup_input_triv                        [Unflattening;TrivRules]
% 2.71/1.04  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.71/1.04  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.71/1.04  
% 2.71/1.04  ------ Combination Options
% 2.71/1.04  
% 2.71/1.04  --comb_res_mult                         3
% 2.71/1.04  --comb_sup_mult                         2
% 2.71/1.04  --comb_inst_mult                        10
% 2.71/1.04  
% 2.71/1.04  ------ Debug Options
% 2.71/1.04  
% 2.71/1.04  --dbg_backtrace                         false
% 2.71/1.04  --dbg_dump_prop_clauses                 false
% 2.71/1.04  --dbg_dump_prop_clauses_file            -
% 2.71/1.04  --dbg_out_stat                          false
% 2.71/1.04  ------ Parsing...
% 2.71/1.04  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 2.71/1.04  
% 2.71/1.04  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe:1:0s pe:2:0s pe:4:0s pe_e  sf_s  rm: 8 0s  sf_e  pe_s  pe_e 
% 2.71/1.04  
% 2.71/1.04  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 2.71/1.04  
% 2.71/1.04  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 2.71/1.04  ------ Proving...
% 2.71/1.04  ------ Problem Properties 
% 2.71/1.04  
% 2.71/1.04  
% 2.71/1.04  clauses                                 20
% 2.71/1.04  conjectures                             2
% 2.71/1.04  EPR                                     3
% 2.71/1.04  Horn                                    14
% 2.71/1.04  unary                                   5
% 2.71/1.04  binary                                  4
% 2.71/1.04  lits                                    51
% 2.71/1.04  lits eq                                 6
% 2.71/1.04  fd_pure                                 0
% 2.71/1.04  fd_pseudo                               0
% 2.71/1.04  fd_cond                                 0
% 2.71/1.04  fd_pseudo_cond                          2
% 2.71/1.04  AC symbols                              0
% 2.71/1.04  
% 2.71/1.04  ------ Schedule dynamic 5 is on 
% 2.71/1.04  
% 2.71/1.04  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" Time Limit: 10.
% 2.71/1.04  
% 2.71/1.04  
% 2.71/1.04  ------ 
% 2.71/1.04  Current options:
% 2.71/1.04  ------ 
% 2.71/1.04  
% 2.71/1.04  ------ Input Options
% 2.71/1.04  
% 2.71/1.04  --out_options                           all
% 2.71/1.04  --tptp_safe_out                         true
% 2.71/1.04  --problem_path                          ""
% 2.71/1.04  --include_path                          ""
% 2.71/1.04  --clausifier                            res/vclausify_rel
% 2.71/1.04  --clausifier_options                    --mode clausify
% 2.71/1.04  --stdin                                 false
% 2.71/1.04  --stats_out                             all
% 2.71/1.04  
% 2.71/1.04  ------ General Options
% 2.71/1.04  
% 2.71/1.04  --fof                                   false
% 2.71/1.04  --time_out_real                         305.
% 2.71/1.04  --time_out_virtual                      -1.
% 2.71/1.04  --symbol_type_check                     false
% 2.71/1.04  --clausify_out                          false
% 2.71/1.04  --sig_cnt_out                           false
% 2.71/1.04  --trig_cnt_out                          false
% 2.71/1.04  --trig_cnt_out_tolerance                1.
% 2.71/1.04  --trig_cnt_out_sk_spl                   false
% 2.71/1.04  --abstr_cl_out                          false
% 2.71/1.04  
% 2.71/1.04  ------ Global Options
% 2.71/1.04  
% 2.71/1.04  --schedule                              default
% 2.71/1.04  --add_important_lit                     false
% 2.71/1.04  --prop_solver_per_cl                    1000
% 2.71/1.04  --min_unsat_core                        false
% 2.71/1.04  --soft_assumptions                      false
% 2.71/1.04  --soft_lemma_size                       3
% 2.71/1.04  --prop_impl_unit_size                   0
% 2.71/1.04  --prop_impl_unit                        []
% 2.71/1.04  --share_sel_clauses                     true
% 2.71/1.04  --reset_solvers                         false
% 2.71/1.04  --bc_imp_inh                            [conj_cone]
% 2.71/1.04  --conj_cone_tolerance                   3.
% 2.71/1.04  --extra_neg_conj                        none
% 2.71/1.04  --large_theory_mode                     true
% 2.71/1.04  --prolific_symb_bound                   200
% 2.71/1.04  --lt_threshold                          2000
% 2.71/1.04  --clause_weak_htbl                      true
% 2.71/1.04  --gc_record_bc_elim                     false
% 2.71/1.04  
% 2.71/1.04  ------ Preprocessing Options
% 2.71/1.04  
% 2.71/1.04  --preprocessing_flag                    true
% 2.71/1.04  --time_out_prep_mult                    0.1
% 2.71/1.04  --splitting_mode                        input
% 2.71/1.04  --splitting_grd                         true
% 2.71/1.04  --splitting_cvd                         false
% 2.71/1.04  --splitting_cvd_svl                     false
% 2.71/1.04  --splitting_nvd                         32
% 2.71/1.04  --sub_typing                            true
% 2.71/1.04  --prep_gs_sim                           true
% 2.71/1.04  --prep_unflatten                        true
% 2.71/1.04  --prep_res_sim                          true
% 2.71/1.04  --prep_upred                            true
% 2.71/1.04  --prep_sem_filter                       exhaustive
% 2.71/1.04  --prep_sem_filter_out                   false
% 2.71/1.04  --pred_elim                             true
% 2.71/1.04  --res_sim_input                         true
% 2.71/1.04  --eq_ax_congr_red                       true
% 2.71/1.04  --pure_diseq_elim                       true
% 2.71/1.04  --brand_transform                       false
% 2.71/1.04  --non_eq_to_eq                          false
% 2.71/1.04  --prep_def_merge                        true
% 2.71/1.04  --prep_def_merge_prop_impl              false
% 2.71/1.04  --prep_def_merge_mbd                    true
% 2.71/1.04  --prep_def_merge_tr_red                 false
% 2.71/1.04  --prep_def_merge_tr_cl                  false
% 2.71/1.04  --smt_preprocessing                     true
% 2.71/1.04  --smt_ac_axioms                         fast
% 2.71/1.04  --preprocessed_out                      false
% 2.71/1.04  --preprocessed_stats                    false
% 2.71/1.04  
% 2.71/1.04  ------ Abstraction refinement Options
% 2.71/1.04  
% 2.71/1.04  --abstr_ref                             []
% 2.71/1.04  --abstr_ref_prep                        false
% 2.71/1.04  --abstr_ref_until_sat                   false
% 2.71/1.04  --abstr_ref_sig_restrict                funpre
% 2.71/1.04  --abstr_ref_af_restrict_to_split_sk     false
% 2.71/1.04  --abstr_ref_under                       []
% 2.71/1.04  
% 2.71/1.04  ------ SAT Options
% 2.71/1.04  
% 2.71/1.04  --sat_mode                              false
% 2.71/1.04  --sat_fm_restart_options                ""
% 2.71/1.04  --sat_gr_def                            false
% 2.71/1.04  --sat_epr_types                         true
% 2.71/1.04  --sat_non_cyclic_types                  false
% 2.71/1.04  --sat_finite_models                     false
% 2.71/1.04  --sat_fm_lemmas                         false
% 2.71/1.04  --sat_fm_prep                           false
% 2.71/1.04  --sat_fm_uc_incr                        true
% 2.71/1.04  --sat_out_model                         small
% 2.71/1.04  --sat_out_clauses                       false
% 2.71/1.04  
% 2.71/1.04  ------ QBF Options
% 2.71/1.04  
% 2.71/1.04  --qbf_mode                              false
% 2.71/1.04  --qbf_elim_univ                         false
% 2.71/1.04  --qbf_dom_inst                          none
% 2.71/1.04  --qbf_dom_pre_inst                      false
% 2.71/1.04  --qbf_sk_in                             false
% 2.71/1.04  --qbf_pred_elim                         true
% 2.71/1.04  --qbf_split                             512
% 2.71/1.04  
% 2.71/1.04  ------ BMC1 Options
% 2.71/1.04  
% 2.71/1.04  --bmc1_incremental                      false
% 2.71/1.04  --bmc1_axioms                           reachable_all
% 2.71/1.04  --bmc1_min_bound                        0
% 2.71/1.04  --bmc1_max_bound                        -1
% 2.71/1.04  --bmc1_max_bound_default                -1
% 2.71/1.04  --bmc1_symbol_reachability              true
% 2.71/1.04  --bmc1_property_lemmas                  false
% 2.71/1.04  --bmc1_k_induction                      false
% 2.71/1.04  --bmc1_non_equiv_states                 false
% 2.71/1.04  --bmc1_deadlock                         false
% 2.71/1.04  --bmc1_ucm                              false
% 2.71/1.04  --bmc1_add_unsat_core                   none
% 2.71/1.04  --bmc1_unsat_core_children              false
% 2.71/1.04  --bmc1_unsat_core_extrapolate_axioms    false
% 2.71/1.04  --bmc1_out_stat                         full
% 2.71/1.04  --bmc1_ground_init                      false
% 2.71/1.04  --bmc1_pre_inst_next_state              false
% 2.71/1.04  --bmc1_pre_inst_state                   false
% 2.71/1.04  --bmc1_pre_inst_reach_state             false
% 2.71/1.04  --bmc1_out_unsat_core                   false
% 2.71/1.04  --bmc1_aig_witness_out                  false
% 2.71/1.04  --bmc1_verbose                          false
% 2.71/1.04  --bmc1_dump_clauses_tptp                false
% 2.71/1.04  --bmc1_dump_unsat_core_tptp             false
% 2.71/1.04  --bmc1_dump_file                        -
% 2.71/1.04  --bmc1_ucm_expand_uc_limit              128
% 2.71/1.04  --bmc1_ucm_n_expand_iterations          6
% 2.71/1.04  --bmc1_ucm_extend_mode                  1
% 2.71/1.04  --bmc1_ucm_init_mode                    2
% 2.71/1.04  --bmc1_ucm_cone_mode                    none
% 2.71/1.04  --bmc1_ucm_reduced_relation_type        0
% 2.71/1.04  --bmc1_ucm_relax_model                  4
% 2.71/1.04  --bmc1_ucm_full_tr_after_sat            true
% 2.71/1.04  --bmc1_ucm_expand_neg_assumptions       false
% 2.71/1.04  --bmc1_ucm_layered_model                none
% 2.71/1.04  --bmc1_ucm_max_lemma_size               10
% 2.71/1.04  
% 2.71/1.04  ------ AIG Options
% 2.71/1.04  
% 2.71/1.04  --aig_mode                              false
% 2.71/1.04  
% 2.71/1.04  ------ Instantiation Options
% 2.71/1.04  
% 2.71/1.04  --instantiation_flag                    true
% 2.71/1.04  --inst_sos_flag                         false
% 2.71/1.04  --inst_sos_phase                        true
% 2.71/1.04  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 2.71/1.04  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 2.71/1.04  --inst_lit_sel_side                     none
% 2.71/1.04  --inst_solver_per_active                1400
% 2.71/1.04  --inst_solver_calls_frac                1.
% 2.71/1.04  --inst_passive_queue_type               priority_queues
% 2.71/1.04  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 2.71/1.05  --inst_passive_queues_freq              [25;2]
% 2.71/1.05  --inst_dismatching                      true
% 2.71/1.05  --inst_eager_unprocessed_to_passive     true
% 2.71/1.05  --inst_prop_sim_given                   true
% 2.71/1.05  --inst_prop_sim_new                     false
% 2.71/1.05  --inst_subs_new                         false
% 2.71/1.05  --inst_eq_res_simp                      false
% 2.71/1.05  --inst_subs_given                       false
% 2.71/1.05  --inst_orphan_elimination               true
% 2.71/1.05  --inst_learning_loop_flag               true
% 2.71/1.05  --inst_learning_start                   3000
% 2.71/1.05  --inst_learning_factor                  2
% 2.71/1.05  --inst_start_prop_sim_after_learn       3
% 2.71/1.05  --inst_sel_renew                        solver
% 2.71/1.05  --inst_lit_activity_flag                true
% 2.71/1.05  --inst_restr_to_given                   false
% 2.71/1.05  --inst_activity_threshold               500
% 2.71/1.05  --inst_out_proof                        true
% 2.71/1.05  
% 2.71/1.05  ------ Resolution Options
% 2.71/1.05  
% 2.71/1.05  --resolution_flag                       false
% 2.71/1.05  --res_lit_sel                           adaptive
% 2.71/1.05  --res_lit_sel_side                      none
% 2.71/1.05  --res_ordering                          kbo
% 2.71/1.05  --res_to_prop_solver                    active
% 2.71/1.05  --res_prop_simpl_new                    false
% 2.71/1.05  --res_prop_simpl_given                  true
% 2.71/1.05  --res_passive_queue_type                priority_queues
% 2.71/1.05  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 2.71/1.05  --res_passive_queues_freq               [15;5]
% 2.71/1.05  --res_forward_subs                      full
% 2.71/1.05  --res_backward_subs                     full
% 2.71/1.05  --res_forward_subs_resolution           true
% 2.71/1.05  --res_backward_subs_resolution          true
% 2.71/1.05  --res_orphan_elimination                true
% 2.71/1.05  --res_time_limit                        2.
% 2.71/1.05  --res_out_proof                         true
% 2.71/1.05  
% 2.71/1.05  ------ Superposition Options
% 2.71/1.05  
% 2.71/1.05  --superposition_flag                    true
% 2.71/1.05  --sup_passive_queue_type                priority_queues
% 2.71/1.05  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 2.71/1.05  --sup_passive_queues_freq               [8;1;4]
% 2.71/1.05  --demod_completeness_check              fast
% 2.71/1.05  --demod_use_ground                      true
% 2.71/1.05  --sup_to_prop_solver                    passive
% 2.71/1.05  --sup_prop_simpl_new                    true
% 2.71/1.05  --sup_prop_simpl_given                  true
% 2.71/1.05  --sup_fun_splitting                     false
% 2.71/1.05  --sup_smt_interval                      50000
% 2.71/1.05  
% 2.71/1.05  ------ Superposition Simplification Setup
% 2.71/1.05  
% 2.71/1.05  --sup_indices_passive                   []
% 2.71/1.05  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.71/1.05  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.71/1.05  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.71/1.05  --sup_full_triv                         [TrivRules;PropSubs]
% 2.71/1.05  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.71/1.05  --sup_full_bw                           [BwDemod]
% 2.71/1.05  --sup_immed_triv                        [TrivRules]
% 2.71/1.05  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 2.71/1.05  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.71/1.05  --sup_immed_bw_main                     []
% 2.71/1.05  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.71/1.05  --sup_input_triv                        [Unflattening;TrivRules]
% 2.71/1.05  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.71/1.05  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.71/1.05  
% 2.71/1.05  ------ Combination Options
% 2.71/1.05  
% 2.71/1.05  --comb_res_mult                         3
% 2.71/1.05  --comb_sup_mult                         2
% 2.71/1.05  --comb_inst_mult                        10
% 2.71/1.05  
% 2.71/1.05  ------ Debug Options
% 2.71/1.05  
% 2.71/1.05  --dbg_backtrace                         false
% 2.71/1.05  --dbg_dump_prop_clauses                 false
% 2.71/1.05  --dbg_dump_prop_clauses_file            -
% 2.71/1.05  --dbg_out_stat                          false
% 2.71/1.05  
% 2.71/1.05  
% 2.71/1.05  
% 2.71/1.05  
% 2.71/1.05  ------ Proving...
% 2.71/1.05  
% 2.71/1.05  
% 2.71/1.05  % SZS status Theorem for theBenchmark.p
% 2.71/1.05  
% 2.71/1.05  % SZS output start CNFRefutation for theBenchmark.p
% 2.71/1.05  
% 2.71/1.05  fof(f11,conjecture,(
% 2.71/1.05    ! [X0] : ((l1_orders_2(X0) & v1_yellow_0(X0) & v5_orders_2(X0) & v4_orders_2(X0) & v3_orders_2(X0) & ~v2_struct_0(X0)) => ! [X1] : ((m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & v13_waybel_0(X1,X0) & v2_waybel_0(X1,X0) & ~v1_xboole_0(X1)) => (v1_subset_1(X1,u1_struct_0(X0)) <=> ~r2_hidden(k3_yellow_0(X0),X1))))),
% 2.71/1.05    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.71/1.05  
% 2.71/1.05  fof(f12,negated_conjecture,(
% 2.71/1.05    ~! [X0] : ((l1_orders_2(X0) & v1_yellow_0(X0) & v5_orders_2(X0) & v4_orders_2(X0) & v3_orders_2(X0) & ~v2_struct_0(X0)) => ! [X1] : ((m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & v13_waybel_0(X1,X0) & v2_waybel_0(X1,X0) & ~v1_xboole_0(X1)) => (v1_subset_1(X1,u1_struct_0(X0)) <=> ~r2_hidden(k3_yellow_0(X0),X1))))),
% 2.71/1.05    inference(negated_conjecture,[],[f11])).
% 2.71/1.05  
% 2.71/1.05  fof(f13,plain,(
% 2.71/1.05    ~! [X0] : ((l1_orders_2(X0) & v1_yellow_0(X0) & v5_orders_2(X0) & v4_orders_2(X0) & v3_orders_2(X0) & ~v2_struct_0(X0)) => ! [X1] : ((m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & v13_waybel_0(X1,X0) & ~v1_xboole_0(X1)) => (v1_subset_1(X1,u1_struct_0(X0)) <=> ~r2_hidden(k3_yellow_0(X0),X1))))),
% 2.71/1.05    inference(pure_predicate_removal,[],[f12])).
% 2.71/1.05  
% 2.71/1.05  fof(f14,plain,(
% 2.71/1.05    ~! [X0] : ((l1_orders_2(X0) & v1_yellow_0(X0) & v5_orders_2(X0) & v3_orders_2(X0) & ~v2_struct_0(X0)) => ! [X1] : ((m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & v13_waybel_0(X1,X0) & ~v1_xboole_0(X1)) => (v1_subset_1(X1,u1_struct_0(X0)) <=> ~r2_hidden(k3_yellow_0(X0),X1))))),
% 2.71/1.05    inference(pure_predicate_removal,[],[f13])).
% 2.71/1.05  
% 2.71/1.05  fof(f15,plain,(
% 2.71/1.05    ~! [X0] : ((l1_orders_2(X0) & v1_yellow_0(X0) & v5_orders_2(X0) & ~v2_struct_0(X0)) => ! [X1] : ((m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & v13_waybel_0(X1,X0) & ~v1_xboole_0(X1)) => (v1_subset_1(X1,u1_struct_0(X0)) <=> ~r2_hidden(k3_yellow_0(X0),X1))))),
% 2.71/1.05    inference(pure_predicate_removal,[],[f14])).
% 2.71/1.05  
% 2.71/1.05  fof(f29,plain,(
% 2.71/1.05    ? [X0] : (? [X1] : ((v1_subset_1(X1,u1_struct_0(X0)) <~> ~r2_hidden(k3_yellow_0(X0),X1)) & (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & v13_waybel_0(X1,X0) & ~v1_xboole_0(X1))) & (l1_orders_2(X0) & v1_yellow_0(X0) & v5_orders_2(X0) & ~v2_struct_0(X0)))),
% 2.71/1.05    inference(ennf_transformation,[],[f15])).
% 2.71/1.05  
% 2.71/1.05  fof(f30,plain,(
% 2.71/1.05    ? [X0] : (? [X1] : ((v1_subset_1(X1,u1_struct_0(X0)) <~> ~r2_hidden(k3_yellow_0(X0),X1)) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & v13_waybel_0(X1,X0) & ~v1_xboole_0(X1)) & l1_orders_2(X0) & v1_yellow_0(X0) & v5_orders_2(X0) & ~v2_struct_0(X0))),
% 2.71/1.05    inference(flattening,[],[f29])).
% 2.71/1.05  
% 2.71/1.05  fof(f42,plain,(
% 2.71/1.05    ? [X0] : (? [X1] : (((r2_hidden(k3_yellow_0(X0),X1) | ~v1_subset_1(X1,u1_struct_0(X0))) & (~r2_hidden(k3_yellow_0(X0),X1) | v1_subset_1(X1,u1_struct_0(X0)))) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & v13_waybel_0(X1,X0) & ~v1_xboole_0(X1)) & l1_orders_2(X0) & v1_yellow_0(X0) & v5_orders_2(X0) & ~v2_struct_0(X0))),
% 2.71/1.05    inference(nnf_transformation,[],[f30])).
% 2.71/1.05  
% 2.71/1.05  fof(f43,plain,(
% 2.71/1.05    ? [X0] : (? [X1] : ((r2_hidden(k3_yellow_0(X0),X1) | ~v1_subset_1(X1,u1_struct_0(X0))) & (~r2_hidden(k3_yellow_0(X0),X1) | v1_subset_1(X1,u1_struct_0(X0))) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & v13_waybel_0(X1,X0) & ~v1_xboole_0(X1)) & l1_orders_2(X0) & v1_yellow_0(X0) & v5_orders_2(X0) & ~v2_struct_0(X0))),
% 2.71/1.05    inference(flattening,[],[f42])).
% 2.71/1.05  
% 2.71/1.05  fof(f45,plain,(
% 2.71/1.05    ( ! [X0] : (? [X1] : ((r2_hidden(k3_yellow_0(X0),X1) | ~v1_subset_1(X1,u1_struct_0(X0))) & (~r2_hidden(k3_yellow_0(X0),X1) | v1_subset_1(X1,u1_struct_0(X0))) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & v13_waybel_0(X1,X0) & ~v1_xboole_0(X1)) => ((r2_hidden(k3_yellow_0(X0),sK5) | ~v1_subset_1(sK5,u1_struct_0(X0))) & (~r2_hidden(k3_yellow_0(X0),sK5) | v1_subset_1(sK5,u1_struct_0(X0))) & m1_subset_1(sK5,k1_zfmisc_1(u1_struct_0(X0))) & v13_waybel_0(sK5,X0) & ~v1_xboole_0(sK5))) )),
% 2.71/1.05    introduced(choice_axiom,[])).
% 2.71/1.05  
% 2.71/1.05  fof(f44,plain,(
% 2.71/1.05    ? [X0] : (? [X1] : ((r2_hidden(k3_yellow_0(X0),X1) | ~v1_subset_1(X1,u1_struct_0(X0))) & (~r2_hidden(k3_yellow_0(X0),X1) | v1_subset_1(X1,u1_struct_0(X0))) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & v13_waybel_0(X1,X0) & ~v1_xboole_0(X1)) & l1_orders_2(X0) & v1_yellow_0(X0) & v5_orders_2(X0) & ~v2_struct_0(X0)) => (? [X1] : ((r2_hidden(k3_yellow_0(sK4),X1) | ~v1_subset_1(X1,u1_struct_0(sK4))) & (~r2_hidden(k3_yellow_0(sK4),X1) | v1_subset_1(X1,u1_struct_0(sK4))) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK4))) & v13_waybel_0(X1,sK4) & ~v1_xboole_0(X1)) & l1_orders_2(sK4) & v1_yellow_0(sK4) & v5_orders_2(sK4) & ~v2_struct_0(sK4))),
% 2.71/1.05    introduced(choice_axiom,[])).
% 2.71/1.05  
% 2.71/1.05  fof(f46,plain,(
% 2.71/1.05    ((r2_hidden(k3_yellow_0(sK4),sK5) | ~v1_subset_1(sK5,u1_struct_0(sK4))) & (~r2_hidden(k3_yellow_0(sK4),sK5) | v1_subset_1(sK5,u1_struct_0(sK4))) & m1_subset_1(sK5,k1_zfmisc_1(u1_struct_0(sK4))) & v13_waybel_0(sK5,sK4) & ~v1_xboole_0(sK5)) & l1_orders_2(sK4) & v1_yellow_0(sK4) & v5_orders_2(sK4) & ~v2_struct_0(sK4)),
% 2.71/1.05    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4,sK5])],[f43,f45,f44])).
% 2.71/1.05  
% 2.71/1.05  fof(f71,plain,(
% 2.71/1.05    m1_subset_1(sK5,k1_zfmisc_1(u1_struct_0(sK4)))),
% 2.71/1.05    inference(cnf_transformation,[],[f46])).
% 2.71/1.05  
% 2.71/1.05  fof(f2,axiom,(
% 2.71/1.05    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => ! [X2] : (r2_hidden(X2,X1) => r2_hidden(X2,X0)))),
% 2.71/1.05    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.71/1.05  
% 2.71/1.05  fof(f17,plain,(
% 2.71/1.05    ! [X0,X1] : (! [X2] : (r2_hidden(X2,X0) | ~r2_hidden(X2,X1)) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 2.71/1.05    inference(ennf_transformation,[],[f2])).
% 2.71/1.05  
% 2.71/1.05  fof(f49,plain,(
% 2.71/1.05    ( ! [X2,X0,X1] : (r2_hidden(X2,X0) | ~r2_hidden(X2,X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 2.71/1.05    inference(cnf_transformation,[],[f17])).
% 2.71/1.05  
% 2.71/1.05  fof(f1,axiom,(
% 2.71/1.05    ! [X0,X1] : (! [X2] : (r2_hidden(X2,X0) <=> r2_hidden(X2,X1)) => X0 = X1)),
% 2.71/1.05    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.71/1.05  
% 2.71/1.05  fof(f16,plain,(
% 2.71/1.05    ! [X0,X1] : (X0 = X1 | ? [X2] : (r2_hidden(X2,X0) <~> r2_hidden(X2,X1)))),
% 2.71/1.05    inference(ennf_transformation,[],[f1])).
% 2.71/1.05  
% 2.71/1.05  fof(f31,plain,(
% 2.71/1.05    ! [X0,X1] : (X0 = X1 | ? [X2] : ((~r2_hidden(X2,X1) | ~r2_hidden(X2,X0)) & (r2_hidden(X2,X1) | r2_hidden(X2,X0))))),
% 2.71/1.05    inference(nnf_transformation,[],[f16])).
% 2.71/1.05  
% 2.71/1.05  fof(f32,plain,(
% 2.71/1.05    ! [X1,X0] : (? [X2] : ((~r2_hidden(X2,X1) | ~r2_hidden(X2,X0)) & (r2_hidden(X2,X1) | r2_hidden(X2,X0))) => ((~r2_hidden(sK0(X0,X1),X1) | ~r2_hidden(sK0(X0,X1),X0)) & (r2_hidden(sK0(X0,X1),X1) | r2_hidden(sK0(X0,X1),X0))))),
% 2.71/1.05    introduced(choice_axiom,[])).
% 2.71/1.05  
% 2.71/1.05  fof(f33,plain,(
% 2.71/1.05    ! [X0,X1] : (X0 = X1 | ((~r2_hidden(sK0(X0,X1),X1) | ~r2_hidden(sK0(X0,X1),X0)) & (r2_hidden(sK0(X0,X1),X1) | r2_hidden(sK0(X0,X1),X0))))),
% 2.71/1.05    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f31,f32])).
% 2.71/1.05  
% 2.71/1.05  fof(f47,plain,(
% 2.71/1.05    ( ! [X0,X1] : (X0 = X1 | r2_hidden(sK0(X0,X1),X1) | r2_hidden(sK0(X0,X1),X0)) )),
% 2.71/1.05    inference(cnf_transformation,[],[f33])).
% 2.71/1.05  
% 2.71/1.05  fof(f4,axiom,(
% 2.71/1.05    ! [X0,X1] : (r2_hidden(X0,X1) => m1_subset_1(X0,X1))),
% 2.71/1.05    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.71/1.05  
% 2.71/1.05  fof(f18,plain,(
% 2.71/1.05    ! [X0,X1] : (m1_subset_1(X0,X1) | ~r2_hidden(X0,X1))),
% 2.71/1.05    inference(ennf_transformation,[],[f4])).
% 2.71/1.05  
% 2.71/1.05  fof(f52,plain,(
% 2.71/1.05    ( ! [X0,X1] : (m1_subset_1(X0,X1) | ~r2_hidden(X0,X1)) )),
% 2.71/1.05    inference(cnf_transformation,[],[f18])).
% 2.71/1.05  
% 2.71/1.05  fof(f5,axiom,(
% 2.71/1.05    ! [X0,X1] : (m1_subset_1(X0,X1) => (r2_hidden(X0,X1) | v1_xboole_0(X1)))),
% 2.71/1.05    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.71/1.05  
% 2.71/1.05  fof(f19,plain,(
% 2.71/1.05    ! [X0,X1] : ((r2_hidden(X0,X1) | v1_xboole_0(X1)) | ~m1_subset_1(X0,X1))),
% 2.71/1.05    inference(ennf_transformation,[],[f5])).
% 2.71/1.05  
% 2.71/1.05  fof(f20,plain,(
% 2.71/1.05    ! [X0,X1] : (r2_hidden(X0,X1) | v1_xboole_0(X1) | ~m1_subset_1(X0,X1))),
% 2.71/1.05    inference(flattening,[],[f19])).
% 2.71/1.05  
% 2.71/1.05  fof(f53,plain,(
% 2.71/1.05    ( ! [X0,X1] : (r2_hidden(X0,X1) | v1_xboole_0(X1) | ~m1_subset_1(X0,X1)) )),
% 2.71/1.05    inference(cnf_transformation,[],[f20])).
% 2.71/1.05  
% 2.71/1.05  fof(f69,plain,(
% 2.71/1.05    ~v1_xboole_0(sK5)),
% 2.71/1.05    inference(cnf_transformation,[],[f46])).
% 2.71/1.05  
% 2.71/1.05  fof(f10,axiom,(
% 2.71/1.05    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => (v1_subset_1(X1,X0) <=> X0 != X1))),
% 2.71/1.05    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.71/1.05  
% 2.71/1.05  fof(f28,plain,(
% 2.71/1.05    ! [X0,X1] : ((v1_subset_1(X1,X0) <=> X0 != X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 2.71/1.05    inference(ennf_transformation,[],[f10])).
% 2.71/1.05  
% 2.71/1.05  fof(f41,plain,(
% 2.71/1.05    ! [X0,X1] : (((v1_subset_1(X1,X0) | X0 = X1) & (X0 != X1 | ~v1_subset_1(X1,X0))) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 2.71/1.05    inference(nnf_transformation,[],[f28])).
% 2.71/1.05  
% 2.71/1.05  fof(f64,plain,(
% 2.71/1.05    ( ! [X0,X1] : (v1_subset_1(X1,X0) | X0 = X1 | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 2.71/1.05    inference(cnf_transformation,[],[f41])).
% 2.71/1.05  
% 2.71/1.05  fof(f73,plain,(
% 2.71/1.05    r2_hidden(k3_yellow_0(sK4),sK5) | ~v1_subset_1(sK5,u1_struct_0(sK4))),
% 2.71/1.05    inference(cnf_transformation,[],[f46])).
% 2.71/1.05  
% 2.71/1.05  fof(f9,axiom,(
% 2.71/1.05    ! [X0] : (l1_orders_2(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => (v13_waybel_0(X1,X0) <=> ! [X2] : (m1_subset_1(X2,u1_struct_0(X0)) => ! [X3] : (m1_subset_1(X3,u1_struct_0(X0)) => ((r1_orders_2(X0,X2,X3) & r2_hidden(X2,X1)) => r2_hidden(X3,X1)))))))),
% 2.71/1.05    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.71/1.05  
% 2.71/1.05  fof(f26,plain,(
% 2.71/1.05    ! [X0] : (! [X1] : ((v13_waybel_0(X1,X0) <=> ! [X2] : (! [X3] : ((r2_hidden(X3,X1) | (~r1_orders_2(X0,X2,X3) | ~r2_hidden(X2,X1))) | ~m1_subset_1(X3,u1_struct_0(X0))) | ~m1_subset_1(X2,u1_struct_0(X0)))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_orders_2(X0))),
% 2.71/1.05    inference(ennf_transformation,[],[f9])).
% 2.71/1.05  
% 2.71/1.05  fof(f27,plain,(
% 2.71/1.05    ! [X0] : (! [X1] : ((v13_waybel_0(X1,X0) <=> ! [X2] : (! [X3] : (r2_hidden(X3,X1) | ~r1_orders_2(X0,X2,X3) | ~r2_hidden(X2,X1) | ~m1_subset_1(X3,u1_struct_0(X0))) | ~m1_subset_1(X2,u1_struct_0(X0)))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_orders_2(X0))),
% 2.71/1.05    inference(flattening,[],[f26])).
% 2.71/1.05  
% 2.71/1.05  fof(f36,plain,(
% 2.71/1.05    ! [X0] : (! [X1] : (((v13_waybel_0(X1,X0) | ? [X2] : (? [X3] : (~r2_hidden(X3,X1) & r1_orders_2(X0,X2,X3) & r2_hidden(X2,X1) & m1_subset_1(X3,u1_struct_0(X0))) & m1_subset_1(X2,u1_struct_0(X0)))) & (! [X2] : (! [X3] : (r2_hidden(X3,X1) | ~r1_orders_2(X0,X2,X3) | ~r2_hidden(X2,X1) | ~m1_subset_1(X3,u1_struct_0(X0))) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~v13_waybel_0(X1,X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_orders_2(X0))),
% 2.71/1.05    inference(nnf_transformation,[],[f27])).
% 2.71/1.05  
% 2.71/1.05  fof(f37,plain,(
% 2.71/1.05    ! [X0] : (! [X1] : (((v13_waybel_0(X1,X0) | ? [X2] : (? [X3] : (~r2_hidden(X3,X1) & r1_orders_2(X0,X2,X3) & r2_hidden(X2,X1) & m1_subset_1(X3,u1_struct_0(X0))) & m1_subset_1(X2,u1_struct_0(X0)))) & (! [X4] : (! [X5] : (r2_hidden(X5,X1) | ~r1_orders_2(X0,X4,X5) | ~r2_hidden(X4,X1) | ~m1_subset_1(X5,u1_struct_0(X0))) | ~m1_subset_1(X4,u1_struct_0(X0))) | ~v13_waybel_0(X1,X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_orders_2(X0))),
% 2.71/1.05    inference(rectify,[],[f36])).
% 2.71/1.05  
% 2.71/1.05  fof(f39,plain,(
% 2.71/1.05    ( ! [X2] : (! [X1,X0] : (? [X3] : (~r2_hidden(X3,X1) & r1_orders_2(X0,X2,X3) & r2_hidden(X2,X1) & m1_subset_1(X3,u1_struct_0(X0))) => (~r2_hidden(sK3(X0,X1),X1) & r1_orders_2(X0,X2,sK3(X0,X1)) & r2_hidden(X2,X1) & m1_subset_1(sK3(X0,X1),u1_struct_0(X0))))) )),
% 2.71/1.05    introduced(choice_axiom,[])).
% 2.71/1.05  
% 2.71/1.05  fof(f38,plain,(
% 2.71/1.05    ! [X1,X0] : (? [X2] : (? [X3] : (~r2_hidden(X3,X1) & r1_orders_2(X0,X2,X3) & r2_hidden(X2,X1) & m1_subset_1(X3,u1_struct_0(X0))) & m1_subset_1(X2,u1_struct_0(X0))) => (? [X3] : (~r2_hidden(X3,X1) & r1_orders_2(X0,sK2(X0,X1),X3) & r2_hidden(sK2(X0,X1),X1) & m1_subset_1(X3,u1_struct_0(X0))) & m1_subset_1(sK2(X0,X1),u1_struct_0(X0))))),
% 2.71/1.05    introduced(choice_axiom,[])).
% 2.71/1.05  
% 2.71/1.05  fof(f40,plain,(
% 2.71/1.05    ! [X0] : (! [X1] : (((v13_waybel_0(X1,X0) | ((~r2_hidden(sK3(X0,X1),X1) & r1_orders_2(X0,sK2(X0,X1),sK3(X0,X1)) & r2_hidden(sK2(X0,X1),X1) & m1_subset_1(sK3(X0,X1),u1_struct_0(X0))) & m1_subset_1(sK2(X0,X1),u1_struct_0(X0)))) & (! [X4] : (! [X5] : (r2_hidden(X5,X1) | ~r1_orders_2(X0,X4,X5) | ~r2_hidden(X4,X1) | ~m1_subset_1(X5,u1_struct_0(X0))) | ~m1_subset_1(X4,u1_struct_0(X0))) | ~v13_waybel_0(X1,X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_orders_2(X0))),
% 2.71/1.05    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2,sK3])],[f37,f39,f38])).
% 2.71/1.05  
% 2.71/1.05  fof(f57,plain,(
% 2.71/1.05    ( ! [X4,X0,X5,X1] : (r2_hidden(X5,X1) | ~r1_orders_2(X0,X4,X5) | ~r2_hidden(X4,X1) | ~m1_subset_1(X5,u1_struct_0(X0)) | ~m1_subset_1(X4,u1_struct_0(X0)) | ~v13_waybel_0(X1,X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_orders_2(X0)) )),
% 2.71/1.05    inference(cnf_transformation,[],[f40])).
% 2.71/1.05  
% 2.71/1.05  fof(f8,axiom,(
% 2.71/1.05    ! [X0] : ((l1_orders_2(X0) & v1_yellow_0(X0) & v5_orders_2(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,u1_struct_0(X0)) => r1_orders_2(X0,k3_yellow_0(X0),X1)))),
% 2.71/1.05    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.71/1.05  
% 2.71/1.05  fof(f24,plain,(
% 2.71/1.05    ! [X0] : (! [X1] : (r1_orders_2(X0,k3_yellow_0(X0),X1) | ~m1_subset_1(X1,u1_struct_0(X0))) | (~l1_orders_2(X0) | ~v1_yellow_0(X0) | ~v5_orders_2(X0) | v2_struct_0(X0)))),
% 2.71/1.05    inference(ennf_transformation,[],[f8])).
% 2.71/1.05  
% 2.71/1.05  fof(f25,plain,(
% 2.71/1.05    ! [X0] : (! [X1] : (r1_orders_2(X0,k3_yellow_0(X0),X1) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~l1_orders_2(X0) | ~v1_yellow_0(X0) | ~v5_orders_2(X0) | v2_struct_0(X0))),
% 2.71/1.05    inference(flattening,[],[f24])).
% 2.71/1.05  
% 2.71/1.05  fof(f56,plain,(
% 2.71/1.05    ( ! [X0,X1] : (r1_orders_2(X0,k3_yellow_0(X0),X1) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_orders_2(X0) | ~v1_yellow_0(X0) | ~v5_orders_2(X0) | v2_struct_0(X0)) )),
% 2.71/1.05    inference(cnf_transformation,[],[f25])).
% 2.71/1.05  
% 2.71/1.05  fof(f67,plain,(
% 2.71/1.05    v1_yellow_0(sK4)),
% 2.71/1.05    inference(cnf_transformation,[],[f46])).
% 2.71/1.05  
% 2.71/1.05  fof(f65,plain,(
% 2.71/1.05    ~v2_struct_0(sK4)),
% 2.71/1.05    inference(cnf_transformation,[],[f46])).
% 2.71/1.05  
% 2.71/1.05  fof(f66,plain,(
% 2.71/1.05    v5_orders_2(sK4)),
% 2.71/1.05    inference(cnf_transformation,[],[f46])).
% 2.71/1.05  
% 2.71/1.05  fof(f68,plain,(
% 2.71/1.05    l1_orders_2(sK4)),
% 2.71/1.05    inference(cnf_transformation,[],[f46])).
% 2.71/1.05  
% 2.71/1.05  fof(f7,axiom,(
% 2.71/1.05    ! [X0] : (l1_orders_2(X0) => m1_subset_1(k3_yellow_0(X0),u1_struct_0(X0)))),
% 2.71/1.05    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.71/1.05  
% 2.71/1.05  fof(f23,plain,(
% 2.71/1.05    ! [X0] : (m1_subset_1(k3_yellow_0(X0),u1_struct_0(X0)) | ~l1_orders_2(X0))),
% 2.71/1.05    inference(ennf_transformation,[],[f7])).
% 2.71/1.05  
% 2.71/1.05  fof(f55,plain,(
% 2.71/1.05    ( ! [X0] : (m1_subset_1(k3_yellow_0(X0),u1_struct_0(X0)) | ~l1_orders_2(X0)) )),
% 2.71/1.05    inference(cnf_transformation,[],[f23])).
% 2.71/1.05  
% 2.71/1.05  fof(f70,plain,(
% 2.71/1.05    v13_waybel_0(sK5,sK4)),
% 2.71/1.05    inference(cnf_transformation,[],[f46])).
% 2.71/1.05  
% 2.71/1.05  fof(f63,plain,(
% 2.71/1.05    ( ! [X0,X1] : (X0 != X1 | ~v1_subset_1(X1,X0) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 2.71/1.05    inference(cnf_transformation,[],[f41])).
% 2.71/1.05  
% 2.71/1.05  fof(f74,plain,(
% 2.71/1.05    ( ! [X1] : (~v1_subset_1(X1,X1) | ~m1_subset_1(X1,k1_zfmisc_1(X1))) )),
% 2.71/1.05    inference(equality_resolution,[],[f63])).
% 2.71/1.05  
% 2.71/1.05  fof(f72,plain,(
% 2.71/1.05    ~r2_hidden(k3_yellow_0(sK4),sK5) | v1_subset_1(sK5,u1_struct_0(sK4))),
% 2.71/1.05    inference(cnf_transformation,[],[f46])).
% 2.71/1.05  
% 2.71/1.05  fof(f3,axiom,(
% 2.71/1.05    ! [X0] : ? [X1] : (~v1_subset_1(X1,X0) & m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 2.71/1.05    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.71/1.05  
% 2.71/1.05  fof(f34,plain,(
% 2.71/1.05    ! [X0] : (? [X1] : (~v1_subset_1(X1,X0) & m1_subset_1(X1,k1_zfmisc_1(X0))) => (~v1_subset_1(sK1(X0),X0) & m1_subset_1(sK1(X0),k1_zfmisc_1(X0))))),
% 2.71/1.05    introduced(choice_axiom,[])).
% 2.71/1.05  
% 2.71/1.05  fof(f35,plain,(
% 2.71/1.05    ! [X0] : (~v1_subset_1(sK1(X0),X0) & m1_subset_1(sK1(X0),k1_zfmisc_1(X0)))),
% 2.71/1.05    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1])],[f3,f34])).
% 2.71/1.05  
% 2.71/1.05  fof(f50,plain,(
% 2.71/1.05    ( ! [X0] : (m1_subset_1(sK1(X0),k1_zfmisc_1(X0))) )),
% 2.71/1.05    inference(cnf_transformation,[],[f35])).
% 2.71/1.05  
% 2.71/1.05  fof(f51,plain,(
% 2.71/1.05    ( ! [X0] : (~v1_subset_1(sK1(X0),X0)) )),
% 2.71/1.05    inference(cnf_transformation,[],[f35])).
% 2.71/1.05  
% 2.71/1.05  fof(f48,plain,(
% 2.71/1.05    ( ! [X0,X1] : (X0 = X1 | ~r2_hidden(sK0(X0,X1),X1) | ~r2_hidden(sK0(X0,X1),X0)) )),
% 2.71/1.05    inference(cnf_transformation,[],[f33])).
% 2.71/1.05  
% 2.71/1.05  cnf(c_20,negated_conjecture,
% 2.71/1.05      ( m1_subset_1(sK5,k1_zfmisc_1(u1_struct_0(sK4))) ),
% 2.71/1.05      inference(cnf_transformation,[],[f71]) ).
% 2.71/1.05  
% 2.71/1.05  cnf(c_1118,plain,
% 2.71/1.05      ( m1_subset_1(sK5,k1_zfmisc_1(u1_struct_0(sK4))) = iProver_top ),
% 2.71/1.05      inference(predicate_to_equality,[status(thm)],[c_20]) ).
% 2.71/1.05  
% 2.71/1.05  cnf(c_2,plain,
% 2.71/1.05      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
% 2.71/1.05      | ~ r2_hidden(X2,X0)
% 2.71/1.05      | r2_hidden(X2,X1) ),
% 2.71/1.05      inference(cnf_transformation,[],[f49]) ).
% 2.71/1.05  
% 2.71/1.05  cnf(c_1122,plain,
% 2.71/1.05      ( m1_subset_1(X0,k1_zfmisc_1(X1)) != iProver_top
% 2.71/1.05      | r2_hidden(X2,X0) != iProver_top
% 2.71/1.05      | r2_hidden(X2,X1) = iProver_top ),
% 2.71/1.05      inference(predicate_to_equality,[status(thm)],[c_2]) ).
% 2.71/1.05  
% 2.71/1.05  cnf(c_1589,plain,
% 2.71/1.05      ( r2_hidden(X0,u1_struct_0(sK4)) = iProver_top
% 2.71/1.05      | r2_hidden(X0,sK5) != iProver_top ),
% 2.71/1.05      inference(superposition,[status(thm)],[c_1118,c_1122]) ).
% 2.71/1.05  
% 2.71/1.05  cnf(c_1,plain,
% 2.71/1.05      ( r2_hidden(sK0(X0,X1),X1) | r2_hidden(sK0(X0,X1),X0) | X1 = X0 ),
% 2.71/1.05      inference(cnf_transformation,[],[f47]) ).
% 2.71/1.05  
% 2.71/1.05  cnf(c_1123,plain,
% 2.71/1.05      ( X0 = X1
% 2.71/1.05      | r2_hidden(sK0(X1,X0),X0) = iProver_top
% 2.71/1.05      | r2_hidden(sK0(X1,X0),X1) = iProver_top ),
% 2.71/1.05      inference(predicate_to_equality,[status(thm)],[c_1]) ).
% 2.71/1.05  
% 2.71/1.05  cnf(c_5,plain,
% 2.71/1.05      ( m1_subset_1(X0,X1) | ~ r2_hidden(X0,X1) ),
% 2.71/1.05      inference(cnf_transformation,[],[f52]) ).
% 2.71/1.05  
% 2.71/1.05  cnf(c_1120,plain,
% 2.71/1.05      ( m1_subset_1(X0,X1) = iProver_top
% 2.71/1.05      | r2_hidden(X0,X1) != iProver_top ),
% 2.71/1.05      inference(predicate_to_equality,[status(thm)],[c_5]) ).
% 2.71/1.05  
% 2.71/1.05  cnf(c_1553,plain,
% 2.71/1.05      ( X0 = X1
% 2.71/1.05      | m1_subset_1(sK0(X0,X1),X0) = iProver_top
% 2.71/1.05      | r2_hidden(sK0(X0,X1),X1) = iProver_top ),
% 2.71/1.05      inference(superposition,[status(thm)],[c_1123,c_1120]) ).
% 2.71/1.05  
% 2.71/1.05  cnf(c_2110,plain,
% 2.71/1.05      ( X0 = X1
% 2.71/1.05      | m1_subset_1(sK0(X1,X0),X1) = iProver_top
% 2.71/1.05      | m1_subset_1(sK0(X1,X0),X0) = iProver_top ),
% 2.71/1.05      inference(superposition,[status(thm)],[c_1553,c_1120]) ).
% 2.71/1.05  
% 2.71/1.05  cnf(c_6,plain,
% 2.71/1.05      ( ~ m1_subset_1(X0,X1) | r2_hidden(X0,X1) | v1_xboole_0(X1) ),
% 2.71/1.05      inference(cnf_transformation,[],[f53]) ).
% 2.71/1.05  
% 2.71/1.05  cnf(c_22,negated_conjecture,
% 2.71/1.05      ( ~ v1_xboole_0(sK5) ),
% 2.71/1.05      inference(cnf_transformation,[],[f69]) ).
% 2.71/1.05  
% 2.71/1.05  cnf(c_357,plain,
% 2.71/1.05      ( ~ m1_subset_1(X0,X1) | r2_hidden(X0,X1) | sK5 != X1 ),
% 2.71/1.05      inference(resolution_lifted,[status(thm)],[c_6,c_22]) ).
% 2.71/1.05  
% 2.71/1.05  cnf(c_358,plain,
% 2.71/1.05      ( ~ m1_subset_1(X0,sK5) | r2_hidden(X0,sK5) ),
% 2.71/1.05      inference(unflattening,[status(thm)],[c_357]) ).
% 2.71/1.05  
% 2.71/1.05  cnf(c_1116,plain,
% 2.71/1.05      ( m1_subset_1(X0,sK5) != iProver_top
% 2.71/1.05      | r2_hidden(X0,sK5) = iProver_top ),
% 2.71/1.05      inference(predicate_to_equality,[status(thm)],[c_358]) ).
% 2.71/1.05  
% 2.71/1.05  cnf(c_2943,plain,
% 2.71/1.05      ( sK5 = X0
% 2.71/1.05      | m1_subset_1(sK0(X0,sK5),X0) = iProver_top
% 2.71/1.05      | r2_hidden(sK0(X0,sK5),sK5) = iProver_top ),
% 2.71/1.05      inference(superposition,[status(thm)],[c_2110,c_1116]) ).
% 2.71/1.05  
% 2.71/1.05  cnf(c_16,plain,
% 2.71/1.05      ( v1_subset_1(X0,X1)
% 2.71/1.05      | ~ m1_subset_1(X0,k1_zfmisc_1(X1))
% 2.71/1.05      | X0 = X1 ),
% 2.71/1.05      inference(cnf_transformation,[],[f64]) ).
% 2.71/1.05  
% 2.71/1.05  cnf(c_18,negated_conjecture,
% 2.71/1.05      ( ~ v1_subset_1(sK5,u1_struct_0(sK4))
% 2.71/1.05      | r2_hidden(k3_yellow_0(sK4),sK5) ),
% 2.71/1.05      inference(cnf_transformation,[],[f73]) ).
% 2.71/1.05  
% 2.71/1.05  cnf(c_201,plain,
% 2.71/1.05      ( ~ v1_subset_1(sK5,u1_struct_0(sK4))
% 2.71/1.05      | r2_hidden(k3_yellow_0(sK4),sK5) ),
% 2.71/1.05      inference(prop_impl,[status(thm)],[c_18]) ).
% 2.71/1.05  
% 2.71/1.05  cnf(c_417,plain,
% 2.71/1.05      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
% 2.71/1.05      | r2_hidden(k3_yellow_0(sK4),sK5)
% 2.71/1.05      | X1 = X0
% 2.71/1.05      | u1_struct_0(sK4) != X1
% 2.71/1.05      | sK5 != X0 ),
% 2.71/1.05      inference(resolution_lifted,[status(thm)],[c_16,c_201]) ).
% 2.71/1.05  
% 2.71/1.05  cnf(c_418,plain,
% 2.71/1.05      ( ~ m1_subset_1(sK5,k1_zfmisc_1(u1_struct_0(sK4)))
% 2.71/1.05      | r2_hidden(k3_yellow_0(sK4),sK5)
% 2.71/1.05      | u1_struct_0(sK4) = sK5 ),
% 2.71/1.05      inference(unflattening,[status(thm)],[c_417]) ).
% 2.71/1.05  
% 2.71/1.05  cnf(c_420,plain,
% 2.71/1.05      ( r2_hidden(k3_yellow_0(sK4),sK5) | u1_struct_0(sK4) = sK5 ),
% 2.71/1.05      inference(global_propositional_subsumption,
% 2.71/1.05                [status(thm)],
% 2.71/1.05                [c_418,c_20]) ).
% 2.71/1.05  
% 2.71/1.05  cnf(c_1114,plain,
% 2.71/1.05      ( u1_struct_0(sK4) = sK5
% 2.71/1.05      | r2_hidden(k3_yellow_0(sK4),sK5) = iProver_top ),
% 2.71/1.05      inference(predicate_to_equality,[status(thm)],[c_420]) ).
% 2.71/1.05  
% 2.71/1.05  cnf(c_15,plain,
% 2.71/1.05      ( ~ r1_orders_2(X0,X1,X2)
% 2.71/1.05      | ~ v13_waybel_0(X3,X0)
% 2.71/1.05      | ~ m1_subset_1(X2,u1_struct_0(X0))
% 2.71/1.05      | ~ m1_subset_1(X1,u1_struct_0(X0))
% 2.71/1.05      | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))
% 2.71/1.05      | ~ r2_hidden(X1,X3)
% 2.71/1.05      | r2_hidden(X2,X3)
% 2.71/1.05      | ~ l1_orders_2(X0) ),
% 2.71/1.05      inference(cnf_transformation,[],[f57]) ).
% 2.71/1.05  
% 2.71/1.05  cnf(c_9,plain,
% 2.71/1.05      ( r1_orders_2(X0,k3_yellow_0(X0),X1)
% 2.71/1.05      | ~ m1_subset_1(X1,u1_struct_0(X0))
% 2.71/1.05      | v2_struct_0(X0)
% 2.71/1.05      | ~ v5_orders_2(X0)
% 2.71/1.05      | ~ v1_yellow_0(X0)
% 2.71/1.05      | ~ l1_orders_2(X0) ),
% 2.71/1.05      inference(cnf_transformation,[],[f56]) ).
% 2.71/1.05  
% 2.71/1.05  cnf(c_24,negated_conjecture,
% 2.71/1.05      ( v1_yellow_0(sK4) ),
% 2.71/1.05      inference(cnf_transformation,[],[f67]) ).
% 2.71/1.05  
% 2.71/1.05  cnf(c_372,plain,
% 2.71/1.05      ( r1_orders_2(X0,k3_yellow_0(X0),X1)
% 2.71/1.05      | ~ m1_subset_1(X1,u1_struct_0(X0))
% 2.71/1.05      | v2_struct_0(X0)
% 2.71/1.05      | ~ v5_orders_2(X0)
% 2.71/1.05      | ~ l1_orders_2(X0)
% 2.71/1.05      | sK4 != X0 ),
% 2.71/1.05      inference(resolution_lifted,[status(thm)],[c_9,c_24]) ).
% 2.71/1.05  
% 2.71/1.05  cnf(c_373,plain,
% 2.71/1.05      ( r1_orders_2(sK4,k3_yellow_0(sK4),X0)
% 2.71/1.05      | ~ m1_subset_1(X0,u1_struct_0(sK4))
% 2.71/1.05      | v2_struct_0(sK4)
% 2.71/1.05      | ~ v5_orders_2(sK4)
% 2.71/1.05      | ~ l1_orders_2(sK4) ),
% 2.71/1.05      inference(unflattening,[status(thm)],[c_372]) ).
% 2.71/1.05  
% 2.71/1.05  cnf(c_26,negated_conjecture,
% 2.71/1.05      ( ~ v2_struct_0(sK4) ),
% 2.71/1.05      inference(cnf_transformation,[],[f65]) ).
% 2.71/1.05  
% 2.71/1.05  cnf(c_25,negated_conjecture,
% 2.71/1.05      ( v5_orders_2(sK4) ),
% 2.71/1.05      inference(cnf_transformation,[],[f66]) ).
% 2.71/1.05  
% 2.71/1.05  cnf(c_23,negated_conjecture,
% 2.71/1.05      ( l1_orders_2(sK4) ),
% 2.71/1.05      inference(cnf_transformation,[],[f68]) ).
% 2.71/1.05  
% 2.71/1.05  cnf(c_377,plain,
% 2.71/1.05      ( ~ m1_subset_1(X0,u1_struct_0(sK4))
% 2.71/1.05      | r1_orders_2(sK4,k3_yellow_0(sK4),X0) ),
% 2.71/1.05      inference(global_propositional_subsumption,
% 2.71/1.05                [status(thm)],
% 2.71/1.05                [c_373,c_26,c_25,c_23]) ).
% 2.71/1.05  
% 2.71/1.05  cnf(c_378,plain,
% 2.71/1.05      ( r1_orders_2(sK4,k3_yellow_0(sK4),X0)
% 2.71/1.05      | ~ m1_subset_1(X0,u1_struct_0(sK4)) ),
% 2.71/1.05      inference(renaming,[status(thm)],[c_377]) ).
% 2.71/1.05  
% 2.71/1.05  cnf(c_485,plain,
% 2.71/1.05      ( ~ v13_waybel_0(X0,X1)
% 2.71/1.05      | ~ m1_subset_1(X2,u1_struct_0(X1))
% 2.71/1.05      | ~ m1_subset_1(X3,u1_struct_0(X1))
% 2.71/1.05      | ~ m1_subset_1(X4,u1_struct_0(sK4))
% 2.71/1.05      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 2.71/1.05      | ~ r2_hidden(X2,X0)
% 2.71/1.05      | r2_hidden(X3,X0)
% 2.71/1.05      | ~ l1_orders_2(X1)
% 2.71/1.05      | X4 != X3
% 2.71/1.05      | k3_yellow_0(sK4) != X2
% 2.71/1.05      | sK4 != X1 ),
% 2.71/1.05      inference(resolution_lifted,[status(thm)],[c_15,c_378]) ).
% 2.71/1.05  
% 2.71/1.05  cnf(c_486,plain,
% 2.71/1.05      ( ~ v13_waybel_0(X0,sK4)
% 2.71/1.05      | ~ m1_subset_1(X1,u1_struct_0(sK4))
% 2.71/1.05      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK4)))
% 2.71/1.05      | ~ m1_subset_1(k3_yellow_0(sK4),u1_struct_0(sK4))
% 2.71/1.05      | r2_hidden(X1,X0)
% 2.71/1.05      | ~ r2_hidden(k3_yellow_0(sK4),X0)
% 2.71/1.05      | ~ l1_orders_2(sK4) ),
% 2.71/1.05      inference(unflattening,[status(thm)],[c_485]) ).
% 2.71/1.05  
% 2.71/1.05  cnf(c_8,plain,
% 2.71/1.05      ( m1_subset_1(k3_yellow_0(X0),u1_struct_0(X0))
% 2.71/1.05      | ~ l1_orders_2(X0) ),
% 2.71/1.05      inference(cnf_transformation,[],[f55]) ).
% 2.71/1.05  
% 2.71/1.05  cnf(c_62,plain,
% 2.71/1.05      ( m1_subset_1(k3_yellow_0(sK4),u1_struct_0(sK4))
% 2.71/1.05      | ~ l1_orders_2(sK4) ),
% 2.71/1.05      inference(instantiation,[status(thm)],[c_8]) ).
% 2.71/1.05  
% 2.71/1.05  cnf(c_490,plain,
% 2.71/1.05      ( ~ r2_hidden(k3_yellow_0(sK4),X0)
% 2.71/1.05      | r2_hidden(X1,X0)
% 2.71/1.05      | ~ v13_waybel_0(X0,sK4)
% 2.71/1.05      | ~ m1_subset_1(X1,u1_struct_0(sK4))
% 2.71/1.05      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK4))) ),
% 2.71/1.05      inference(global_propositional_subsumption,
% 2.71/1.05                [status(thm)],
% 2.71/1.05                [c_486,c_23,c_62]) ).
% 2.71/1.05  
% 2.71/1.05  cnf(c_491,plain,
% 2.71/1.05      ( ~ v13_waybel_0(X0,sK4)
% 2.71/1.05      | ~ m1_subset_1(X1,u1_struct_0(sK4))
% 2.71/1.05      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK4)))
% 2.71/1.05      | r2_hidden(X1,X0)
% 2.71/1.05      | ~ r2_hidden(k3_yellow_0(sK4),X0) ),
% 2.71/1.05      inference(renaming,[status(thm)],[c_490]) ).
% 2.71/1.05  
% 2.71/1.05  cnf(c_1112,plain,
% 2.71/1.05      ( v13_waybel_0(X0,sK4) != iProver_top
% 2.71/1.05      | m1_subset_1(X1,u1_struct_0(sK4)) != iProver_top
% 2.71/1.05      | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK4))) != iProver_top
% 2.71/1.05      | r2_hidden(X1,X0) = iProver_top
% 2.71/1.05      | r2_hidden(k3_yellow_0(sK4),X0) != iProver_top ),
% 2.71/1.05      inference(predicate_to_equality,[status(thm)],[c_491]) ).
% 2.71/1.05  
% 2.71/1.05  cnf(c_1695,plain,
% 2.71/1.05      ( v13_waybel_0(sK5,sK4) != iProver_top
% 2.71/1.05      | m1_subset_1(X0,u1_struct_0(sK4)) != iProver_top
% 2.71/1.05      | r2_hidden(X0,sK5) = iProver_top
% 2.71/1.05      | r2_hidden(k3_yellow_0(sK4),sK5) != iProver_top ),
% 2.71/1.05      inference(superposition,[status(thm)],[c_1118,c_1112]) ).
% 2.71/1.05  
% 2.71/1.05  cnf(c_21,negated_conjecture,
% 2.71/1.05      ( v13_waybel_0(sK5,sK4) ),
% 2.71/1.05      inference(cnf_transformation,[],[f70]) ).
% 2.71/1.05  
% 2.71/1.05  cnf(c_32,plain,
% 2.71/1.05      ( v13_waybel_0(sK5,sK4) = iProver_top ),
% 2.71/1.05      inference(predicate_to_equality,[status(thm)],[c_21]) ).
% 2.71/1.05  
% 2.71/1.05  cnf(c_1700,plain,
% 2.71/1.05      ( m1_subset_1(X0,u1_struct_0(sK4)) != iProver_top
% 2.71/1.05      | r2_hidden(X0,sK5) = iProver_top
% 2.71/1.05      | r2_hidden(k3_yellow_0(sK4),sK5) != iProver_top ),
% 2.71/1.05      inference(global_propositional_subsumption,
% 2.71/1.05                [status(thm)],
% 2.71/1.05                [c_1695,c_32]) ).
% 2.71/1.05  
% 2.71/1.05  cnf(c_1837,plain,
% 2.71/1.05      ( u1_struct_0(sK4) = sK5
% 2.71/1.05      | m1_subset_1(X0,u1_struct_0(sK4)) != iProver_top
% 2.71/1.05      | r2_hidden(X0,sK5) = iProver_top ),
% 2.71/1.05      inference(superposition,[status(thm)],[c_1114,c_1700]) ).
% 2.71/1.05  
% 2.71/1.05  cnf(c_3400,plain,
% 2.71/1.05      ( u1_struct_0(sK4) = sK5
% 2.71/1.05      | r2_hidden(sK0(u1_struct_0(sK4),sK5),sK5) = iProver_top ),
% 2.71/1.05      inference(superposition,[status(thm)],[c_2943,c_1837]) ).
% 2.71/1.05  
% 2.71/1.05  cnf(c_30,plain,
% 2.71/1.05      ( l1_orders_2(sK4) = iProver_top ),
% 2.71/1.05      inference(predicate_to_equality,[status(thm)],[c_23]) ).
% 2.71/1.05  
% 2.71/1.05  cnf(c_61,plain,
% 2.71/1.05      ( m1_subset_1(k3_yellow_0(X0),u1_struct_0(X0)) = iProver_top
% 2.71/1.05      | l1_orders_2(X0) != iProver_top ),
% 2.71/1.05      inference(predicate_to_equality,[status(thm)],[c_8]) ).
% 2.71/1.05  
% 2.71/1.05  cnf(c_63,plain,
% 2.71/1.05      ( m1_subset_1(k3_yellow_0(sK4),u1_struct_0(sK4)) = iProver_top
% 2.71/1.05      | l1_orders_2(sK4) != iProver_top ),
% 2.71/1.05      inference(instantiation,[status(thm)],[c_61]) ).
% 2.71/1.05  
% 2.71/1.05  cnf(c_17,plain,
% 2.71/1.05      ( ~ v1_subset_1(X0,X0) | ~ m1_subset_1(X0,k1_zfmisc_1(X0)) ),
% 2.71/1.05      inference(cnf_transformation,[],[f74]) ).
% 2.71/1.05  
% 2.71/1.05  cnf(c_19,negated_conjecture,
% 2.71/1.05      ( v1_subset_1(sK5,u1_struct_0(sK4))
% 2.71/1.05      | ~ r2_hidden(k3_yellow_0(sK4),sK5) ),
% 2.71/1.05      inference(cnf_transformation,[],[f72]) ).
% 2.71/1.05  
% 2.71/1.05  cnf(c_199,plain,
% 2.71/1.05      ( v1_subset_1(sK5,u1_struct_0(sK4))
% 2.71/1.05      | ~ r2_hidden(k3_yellow_0(sK4),sK5) ),
% 2.71/1.05      inference(prop_impl,[status(thm)],[c_19]) ).
% 2.71/1.05  
% 2.71/1.05  cnf(c_431,plain,
% 2.71/1.05      ( ~ m1_subset_1(X0,k1_zfmisc_1(X0))
% 2.71/1.05      | ~ r2_hidden(k3_yellow_0(sK4),sK5)
% 2.71/1.05      | u1_struct_0(sK4) != X0
% 2.71/1.05      | sK5 != X0 ),
% 2.71/1.05      inference(resolution_lifted,[status(thm)],[c_17,c_199]) ).
% 2.71/1.05  
% 2.71/1.05  cnf(c_432,plain,
% 2.71/1.05      ( ~ m1_subset_1(u1_struct_0(sK4),k1_zfmisc_1(u1_struct_0(sK4)))
% 2.71/1.05      | ~ r2_hidden(k3_yellow_0(sK4),sK5)
% 2.71/1.05      | sK5 != u1_struct_0(sK4) ),
% 2.71/1.05      inference(unflattening,[status(thm)],[c_431]) ).
% 2.71/1.05  
% 2.71/1.05  cnf(c_433,plain,
% 2.71/1.05      ( sK5 != u1_struct_0(sK4)
% 2.71/1.05      | m1_subset_1(u1_struct_0(sK4),k1_zfmisc_1(u1_struct_0(sK4))) != iProver_top
% 2.71/1.05      | r2_hidden(k3_yellow_0(sK4),sK5) != iProver_top ),
% 2.71/1.05      inference(predicate_to_equality,[status(thm)],[c_432]) ).
% 2.71/1.05  
% 2.71/1.05  cnf(c_777,plain,
% 2.71/1.05      ( X0 != X1 | k3_yellow_0(X0) = k3_yellow_0(X1) ),
% 2.71/1.05      theory(equality) ).
% 2.71/1.05  
% 2.71/1.05  cnf(c_786,plain,
% 2.71/1.05      ( k3_yellow_0(sK4) = k3_yellow_0(sK4) | sK4 != sK4 ),
% 2.71/1.05      inference(instantiation,[status(thm)],[c_777]) ).
% 2.71/1.05  
% 2.71/1.05  cnf(c_771,plain,( X0 = X0 ),theory(equality) ).
% 2.71/1.05  
% 2.71/1.05  cnf(c_792,plain,
% 2.71/1.05      ( sK4 = sK4 ),
% 2.71/1.05      inference(instantiation,[status(thm)],[c_771]) ).
% 2.71/1.05  
% 2.71/1.05  cnf(c_4,plain,
% 2.71/1.05      ( m1_subset_1(sK1(X0),k1_zfmisc_1(X0)) ),
% 2.71/1.05      inference(cnf_transformation,[],[f50]) ).
% 2.71/1.05  
% 2.71/1.05  cnf(c_1287,plain,
% 2.71/1.05      ( m1_subset_1(sK1(u1_struct_0(sK4)),k1_zfmisc_1(u1_struct_0(sK4))) ),
% 2.71/1.05      inference(instantiation,[status(thm)],[c_4]) ).
% 2.71/1.05  
% 2.71/1.05  cnf(c_1292,plain,
% 2.71/1.05      ( m1_subset_1(sK1(u1_struct_0(sK4)),k1_zfmisc_1(u1_struct_0(sK4))) = iProver_top ),
% 2.71/1.05      inference(predicate_to_equality,[status(thm)],[c_1287]) ).
% 2.71/1.05  
% 2.71/1.05  cnf(c_1403,plain,
% 2.71/1.05      ( sK5 = sK5 ),
% 2.71/1.05      inference(instantiation,[status(thm)],[c_771]) ).
% 2.71/1.05  
% 2.71/1.05  cnf(c_1464,plain,
% 2.71/1.05      ( k1_zfmisc_1(u1_struct_0(sK4)) = k1_zfmisc_1(u1_struct_0(sK4)) ),
% 2.71/1.05      inference(instantiation,[status(thm)],[c_771]) ).
% 2.71/1.05  
% 2.71/1.05  cnf(c_775,plain,
% 2.71/1.05      ( ~ m1_subset_1(X0,X1) | m1_subset_1(X2,X3) | X2 != X0 | X3 != X1 ),
% 2.71/1.05      theory(equality) ).
% 2.71/1.05  
% 2.71/1.05  cnf(c_1347,plain,
% 2.71/1.05      ( m1_subset_1(X0,X1)
% 2.71/1.05      | ~ m1_subset_1(k3_yellow_0(sK4),u1_struct_0(sK4))
% 2.71/1.05      | X1 != u1_struct_0(sK4)
% 2.71/1.05      | X0 != k3_yellow_0(sK4) ),
% 2.71/1.05      inference(instantiation,[status(thm)],[c_775]) ).
% 2.71/1.05  
% 2.71/1.05  cnf(c_1579,plain,
% 2.71/1.05      ( m1_subset_1(X0,sK5)
% 2.71/1.05      | ~ m1_subset_1(k3_yellow_0(sK4),u1_struct_0(sK4))
% 2.71/1.05      | X0 != k3_yellow_0(sK4)
% 2.71/1.05      | sK5 != u1_struct_0(sK4) ),
% 2.71/1.05      inference(instantiation,[status(thm)],[c_1347]) ).
% 2.71/1.05  
% 2.71/1.05  cnf(c_1739,plain,
% 2.71/1.05      ( ~ m1_subset_1(k3_yellow_0(sK4),u1_struct_0(sK4))
% 2.71/1.05      | m1_subset_1(k3_yellow_0(sK4),sK5)
% 2.71/1.05      | k3_yellow_0(sK4) != k3_yellow_0(sK4)
% 2.71/1.05      | sK5 != u1_struct_0(sK4) ),
% 2.71/1.05      inference(instantiation,[status(thm)],[c_1579]) ).
% 2.71/1.05  
% 2.71/1.05  cnf(c_1741,plain,
% 2.71/1.05      ( k3_yellow_0(sK4) != k3_yellow_0(sK4)
% 2.71/1.05      | sK5 != u1_struct_0(sK4)
% 2.71/1.05      | m1_subset_1(k3_yellow_0(sK4),u1_struct_0(sK4)) != iProver_top
% 2.71/1.05      | m1_subset_1(k3_yellow_0(sK4),sK5) = iProver_top ),
% 2.71/1.05      inference(predicate_to_equality,[status(thm)],[c_1739]) ).
% 2.71/1.05  
% 2.71/1.05  cnf(c_3,plain,
% 2.71/1.05      ( ~ v1_subset_1(sK1(X0),X0) ),
% 2.71/1.05      inference(cnf_transformation,[],[f51]) ).
% 2.71/1.05  
% 2.71/1.05  cnf(c_394,plain,
% 2.71/1.05      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
% 2.71/1.05      | X1 != X2
% 2.71/1.05      | X1 = X0
% 2.71/1.05      | sK1(X2) != X0 ),
% 2.71/1.05      inference(resolution_lifted,[status(thm)],[c_3,c_16]) ).
% 2.71/1.05  
% 2.71/1.05  cnf(c_395,plain,
% 2.71/1.05      ( ~ m1_subset_1(sK1(X0),k1_zfmisc_1(X0)) | X0 = sK1(X0) ),
% 2.71/1.05      inference(unflattening,[status(thm)],[c_394]) ).
% 2.71/1.05  
% 2.71/1.05  cnf(c_399,plain,
% 2.71/1.05      ( X0 = sK1(X0) ),
% 2.71/1.05      inference(global_propositional_subsumption,
% 2.71/1.05                [status(thm)],
% 2.71/1.05                [c_395,c_4]) ).
% 2.71/1.05  
% 2.71/1.05  cnf(c_2563,plain,
% 2.71/1.05      ( u1_struct_0(sK4) = sK1(u1_struct_0(sK4)) ),
% 2.71/1.05      inference(instantiation,[status(thm)],[c_399]) ).
% 2.71/1.05  
% 2.71/1.05  cnf(c_772,plain,( X0 != X1 | X2 != X1 | X2 = X0 ),theory(equality) ).
% 2.71/1.05  
% 2.71/1.05  cnf(c_1359,plain,
% 2.71/1.05      ( u1_struct_0(sK4) != X0 | sK5 != X0 | sK5 = u1_struct_0(sK4) ),
% 2.71/1.05      inference(instantiation,[status(thm)],[c_772]) ).
% 2.71/1.05  
% 2.71/1.05  cnf(c_2735,plain,
% 2.71/1.05      ( u1_struct_0(sK4) != sK5 | sK5 = u1_struct_0(sK4) | sK5 != sK5 ),
% 2.71/1.05      inference(instantiation,[status(thm)],[c_1359]) ).
% 2.71/1.05  
% 2.71/1.05  cnf(c_4278,plain,
% 2.71/1.05      ( ~ m1_subset_1(k3_yellow_0(sK4),sK5)
% 2.71/1.05      | r2_hidden(k3_yellow_0(sK4),sK5) ),
% 2.71/1.05      inference(instantiation,[status(thm)],[c_358]) ).
% 2.71/1.05  
% 2.71/1.05  cnf(c_4279,plain,
% 2.71/1.05      ( m1_subset_1(k3_yellow_0(sK4),sK5) != iProver_top
% 2.71/1.05      | r2_hidden(k3_yellow_0(sK4),sK5) = iProver_top ),
% 2.71/1.05      inference(predicate_to_equality,[status(thm)],[c_4278]) ).
% 2.71/1.05  
% 2.71/1.05  cnf(c_1337,plain,
% 2.71/1.05      ( m1_subset_1(X0,X1)
% 2.71/1.05      | ~ m1_subset_1(sK1(X2),k1_zfmisc_1(X2))
% 2.71/1.05      | X0 != sK1(X2)
% 2.71/1.05      | X1 != k1_zfmisc_1(X2) ),
% 2.71/1.05      inference(instantiation,[status(thm)],[c_775]) ).
% 2.71/1.05  
% 2.71/1.05  cnf(c_1538,plain,
% 2.71/1.05      ( m1_subset_1(X0,k1_zfmisc_1(X1))
% 2.71/1.05      | ~ m1_subset_1(sK1(X1),k1_zfmisc_1(X1))
% 2.71/1.05      | X0 != sK1(X1)
% 2.71/1.05      | k1_zfmisc_1(X1) != k1_zfmisc_1(X1) ),
% 2.71/1.05      inference(instantiation,[status(thm)],[c_1337]) ).
% 2.71/1.05  
% 2.71/1.05  cnf(c_1884,plain,
% 2.71/1.05      ( m1_subset_1(u1_struct_0(sK4),k1_zfmisc_1(X0))
% 2.71/1.05      | ~ m1_subset_1(sK1(X0),k1_zfmisc_1(X0))
% 2.71/1.05      | u1_struct_0(sK4) != sK1(X0)
% 2.71/1.05      | k1_zfmisc_1(X0) != k1_zfmisc_1(X0) ),
% 2.71/1.05      inference(instantiation,[status(thm)],[c_1538]) ).
% 2.71/1.05  
% 2.71/1.05  cnf(c_5802,plain,
% 2.71/1.05      ( m1_subset_1(u1_struct_0(sK4),k1_zfmisc_1(u1_struct_0(sK4)))
% 2.71/1.05      | ~ m1_subset_1(sK1(u1_struct_0(sK4)),k1_zfmisc_1(u1_struct_0(sK4)))
% 2.71/1.05      | u1_struct_0(sK4) != sK1(u1_struct_0(sK4))
% 2.71/1.05      | k1_zfmisc_1(u1_struct_0(sK4)) != k1_zfmisc_1(u1_struct_0(sK4)) ),
% 2.71/1.05      inference(instantiation,[status(thm)],[c_1884]) ).
% 2.71/1.05  
% 2.71/1.05  cnf(c_5803,plain,
% 2.71/1.05      ( u1_struct_0(sK4) != sK1(u1_struct_0(sK4))
% 2.71/1.05      | k1_zfmisc_1(u1_struct_0(sK4)) != k1_zfmisc_1(u1_struct_0(sK4))
% 2.71/1.05      | m1_subset_1(u1_struct_0(sK4),k1_zfmisc_1(u1_struct_0(sK4))) = iProver_top
% 2.71/1.05      | m1_subset_1(sK1(u1_struct_0(sK4)),k1_zfmisc_1(u1_struct_0(sK4))) != iProver_top ),
% 2.71/1.05      inference(predicate_to_equality,[status(thm)],[c_5802]) ).
% 2.71/1.05  
% 2.71/1.05  cnf(c_7513,plain,
% 2.71/1.05      ( r2_hidden(sK0(u1_struct_0(sK4),sK5),sK5) = iProver_top ),
% 2.71/1.05      inference(global_propositional_subsumption,
% 2.71/1.05                [status(thm)],
% 2.71/1.05                [c_3400,c_30,c_63,c_433,c_786,c_792,c_1292,c_1403,c_1464,
% 2.71/1.05                 c_1741,c_2563,c_2735,c_4279,c_5803]) ).
% 2.71/1.05  
% 2.71/1.05  cnf(c_0,plain,
% 2.71/1.05      ( ~ r2_hidden(sK0(X0,X1),X1)
% 2.71/1.05      | ~ r2_hidden(sK0(X0,X1),X0)
% 2.71/1.05      | X1 = X0 ),
% 2.71/1.05      inference(cnf_transformation,[],[f48]) ).
% 2.71/1.05  
% 2.71/1.05  cnf(c_1124,plain,
% 2.71/1.05      ( X0 = X1
% 2.71/1.05      | r2_hidden(sK0(X1,X0),X0) != iProver_top
% 2.71/1.05      | r2_hidden(sK0(X1,X0),X1) != iProver_top ),
% 2.71/1.05      inference(predicate_to_equality,[status(thm)],[c_0]) ).
% 2.71/1.05  
% 2.71/1.05  cnf(c_7519,plain,
% 2.71/1.05      ( u1_struct_0(sK4) = sK5
% 2.71/1.05      | r2_hidden(sK0(u1_struct_0(sK4),sK5),u1_struct_0(sK4)) != iProver_top ),
% 2.71/1.05      inference(superposition,[status(thm)],[c_7513,c_1124]) ).
% 2.71/1.05  
% 2.71/1.05  cnf(c_1323,plain,
% 2.71/1.05      ( ~ r2_hidden(sK0(u1_struct_0(sK4),sK5),u1_struct_0(sK4))
% 2.71/1.05      | ~ r2_hidden(sK0(u1_struct_0(sK4),sK5),sK5)
% 2.71/1.05      | sK5 = u1_struct_0(sK4) ),
% 2.71/1.05      inference(instantiation,[status(thm)],[c_0]) ).
% 2.71/1.05  
% 2.71/1.05  cnf(c_1324,plain,
% 2.71/1.05      ( sK5 = u1_struct_0(sK4)
% 2.71/1.05      | r2_hidden(sK0(u1_struct_0(sK4),sK5),u1_struct_0(sK4)) != iProver_top
% 2.71/1.05      | r2_hidden(sK0(u1_struct_0(sK4),sK5),sK5) != iProver_top ),
% 2.71/1.05      inference(predicate_to_equality,[status(thm)],[c_1323]) ).
% 2.71/1.05  
% 2.71/1.05  cnf(c_7962,plain,
% 2.71/1.05      ( r2_hidden(sK0(u1_struct_0(sK4),sK5),u1_struct_0(sK4)) != iProver_top ),
% 2.71/1.05      inference(global_propositional_subsumption,
% 2.71/1.05                [status(thm)],
% 2.71/1.05                [c_7519,c_30,c_63,c_433,c_786,c_792,c_1292,c_1324,c_1403,
% 2.71/1.05                 c_1464,c_1741,c_2563,c_2735,c_3400,c_4279,c_5803]) ).
% 2.71/1.05  
% 2.71/1.05  cnf(c_7970,plain,
% 2.71/1.05      ( r2_hidden(sK0(u1_struct_0(sK4),sK5),sK5) != iProver_top ),
% 2.71/1.05      inference(superposition,[status(thm)],[c_1589,c_7962]) ).
% 2.71/1.05  
% 2.71/1.05  cnf(contradiction,plain,
% 2.71/1.05      ( $false ),
% 2.71/1.05      inference(minisat,[status(thm)],[c_7970,c_7513]) ).
% 2.71/1.05  
% 2.71/1.05  
% 2.71/1.05  % SZS output end CNFRefutation for theBenchmark.p
% 2.71/1.05  
% 2.71/1.05  ------                               Statistics
% 2.71/1.05  
% 2.71/1.05  ------ General
% 2.71/1.05  
% 2.71/1.05  abstr_ref_over_cycles:                  0
% 2.71/1.05  abstr_ref_under_cycles:                 0
% 2.71/1.05  gc_basic_clause_elim:                   0
% 2.71/1.05  forced_gc_time:                         0
% 2.71/1.05  parsing_time:                           0.011
% 2.71/1.05  unif_index_cands_time:                  0.
% 2.71/1.05  unif_index_add_time:                    0.
% 2.71/1.05  orderings_time:                         0.
% 2.71/1.05  out_proof_time:                         0.012
% 2.71/1.05  total_time:                             0.235
% 2.71/1.05  num_of_symbols:                         50
% 2.71/1.05  num_of_terms:                           4122
% 2.71/1.05  
% 2.71/1.05  ------ Preprocessing
% 2.71/1.05  
% 2.71/1.05  num_of_splits:                          0
% 2.71/1.05  num_of_split_atoms:                     0
% 2.71/1.05  num_of_reused_defs:                     0
% 2.71/1.05  num_eq_ax_congr_red:                    16
% 2.71/1.05  num_of_sem_filtered_clauses:            1
% 2.71/1.05  num_of_subtypes:                        0
% 2.71/1.05  monotx_restored_types:                  0
% 2.71/1.05  sat_num_of_epr_types:                   0
% 2.71/1.05  sat_num_of_non_cyclic_types:            0
% 2.71/1.05  sat_guarded_non_collapsed_types:        0
% 2.71/1.05  num_pure_diseq_elim:                    0
% 2.71/1.05  simp_replaced_by:                       0
% 2.71/1.05  res_preprocessed:                       110
% 2.71/1.05  prep_upred:                             0
% 2.71/1.05  prep_unflattend:                        22
% 2.71/1.05  smt_new_axioms:                         0
% 2.71/1.05  pred_elim_cands:                        3
% 2.71/1.05  pred_elim:                              7
% 2.71/1.05  pred_elim_cl:                           7
% 2.71/1.05  pred_elim_cycles:                       9
% 2.71/1.05  merged_defs:                            2
% 2.71/1.05  merged_defs_ncl:                        0
% 2.71/1.05  bin_hyper_res:                          2
% 2.71/1.05  prep_cycles:                            4
% 2.71/1.05  pred_elim_time:                         0.006
% 2.71/1.05  splitting_time:                         0.
% 2.71/1.05  sem_filter_time:                        0.
% 2.71/1.05  monotx_time:                            0.
% 2.71/1.05  subtype_inf_time:                       0.
% 2.71/1.05  
% 2.71/1.05  ------ Problem properties
% 2.71/1.05  
% 2.71/1.05  clauses:                                20
% 2.71/1.05  conjectures:                            2
% 2.71/1.05  epr:                                    3
% 2.71/1.05  horn:                                   14
% 2.71/1.05  ground:                                 6
% 2.71/1.05  unary:                                  5
% 2.71/1.05  binary:                                 4
% 2.71/1.05  lits:                                   51
% 2.71/1.05  lits_eq:                                6
% 2.71/1.05  fd_pure:                                0
% 2.71/1.05  fd_pseudo:                              0
% 2.71/1.05  fd_cond:                                0
% 2.71/1.05  fd_pseudo_cond:                         2
% 2.71/1.05  ac_symbols:                             0
% 2.71/1.05  
% 2.71/1.05  ------ Propositional Solver
% 2.71/1.05  
% 2.71/1.05  prop_solver_calls:                      30
% 2.71/1.05  prop_fast_solver_calls:                 983
% 2.71/1.05  smt_solver_calls:                       0
% 2.71/1.05  smt_fast_solver_calls:                  0
% 2.71/1.05  prop_num_of_clauses:                    2597
% 2.71/1.05  prop_preprocess_simplified:             5238
% 2.71/1.05  prop_fo_subsumed:                       26
% 2.71/1.05  prop_solver_time:                       0.
% 2.71/1.05  smt_solver_time:                        0.
% 2.71/1.05  smt_fast_solver_time:                   0.
% 2.71/1.05  prop_fast_solver_time:                  0.
% 2.71/1.05  prop_unsat_core_time:                   0.
% 2.71/1.05  
% 2.71/1.05  ------ QBF
% 2.71/1.05  
% 2.71/1.05  qbf_q_res:                              0
% 2.71/1.05  qbf_num_tautologies:                    0
% 2.71/1.05  qbf_prep_cycles:                        0
% 2.71/1.05  
% 2.71/1.05  ------ BMC1
% 2.71/1.05  
% 2.71/1.05  bmc1_current_bound:                     -1
% 2.71/1.05  bmc1_last_solved_bound:                 -1
% 2.71/1.05  bmc1_unsat_core_size:                   -1
% 2.71/1.05  bmc1_unsat_core_parents_size:           -1
% 2.71/1.05  bmc1_merge_next_fun:                    0
% 2.71/1.05  bmc1_unsat_core_clauses_time:           0.
% 2.71/1.05  
% 2.71/1.05  ------ Instantiation
% 2.71/1.05  
% 2.71/1.05  inst_num_of_clauses:                    565
% 2.71/1.05  inst_num_in_passive:                    255
% 2.71/1.05  inst_num_in_active:                     292
% 2.71/1.05  inst_num_in_unprocessed:                18
% 2.71/1.05  inst_num_of_loops:                      410
% 2.71/1.05  inst_num_of_learning_restarts:          0
% 2.71/1.05  inst_num_moves_active_passive:          113
% 2.71/1.05  inst_lit_activity:                      0
% 2.71/1.05  inst_lit_activity_moves:                0
% 2.71/1.05  inst_num_tautologies:                   0
% 2.71/1.05  inst_num_prop_implied:                  0
% 2.71/1.05  inst_num_existing_simplified:           0
% 2.71/1.05  inst_num_eq_res_simplified:             0
% 2.71/1.05  inst_num_child_elim:                    0
% 2.71/1.05  inst_num_of_dismatching_blockings:      148
% 2.71/1.05  inst_num_of_non_proper_insts:           596
% 2.71/1.05  inst_num_of_duplicates:                 0
% 2.71/1.05  inst_inst_num_from_inst_to_res:         0
% 2.71/1.05  inst_dismatching_checking_time:         0.
% 2.71/1.05  
% 2.71/1.05  ------ Resolution
% 2.71/1.05  
% 2.71/1.05  res_num_of_clauses:                     0
% 2.71/1.05  res_num_in_passive:                     0
% 2.71/1.05  res_num_in_active:                      0
% 2.71/1.05  res_num_of_loops:                       114
% 2.71/1.05  res_forward_subset_subsumed:            71
% 2.71/1.05  res_backward_subset_subsumed:           0
% 2.71/1.05  res_forward_subsumed:                   0
% 2.71/1.05  res_backward_subsumed:                  0
% 2.71/1.05  res_forward_subsumption_resolution:     2
% 2.71/1.05  res_backward_subsumption_resolution:    0
% 2.71/1.05  res_clause_to_clause_subsumption:       1922
% 2.71/1.05  res_orphan_elimination:                 0
% 2.71/1.05  res_tautology_del:                      69
% 2.71/1.05  res_num_eq_res_simplified:              0
% 2.71/1.05  res_num_sel_changes:                    0
% 2.71/1.05  res_moves_from_active_to_pass:          0
% 2.71/1.05  
% 2.71/1.05  ------ Superposition
% 2.71/1.05  
% 2.71/1.05  sup_time_total:                         0.
% 2.71/1.05  sup_time_generating:                    0.
% 2.71/1.05  sup_time_sim_full:                      0.
% 2.71/1.05  sup_time_sim_immed:                     0.
% 2.71/1.05  
% 2.71/1.05  sup_num_of_clauses:                     209
% 2.71/1.05  sup_num_in_active:                      76
% 2.71/1.05  sup_num_in_passive:                     133
% 2.71/1.05  sup_num_of_loops:                       80
% 2.71/1.05  sup_fw_superposition:                   124
% 2.71/1.05  sup_bw_superposition:                   191
% 2.71/1.05  sup_immediate_simplified:               44
% 2.71/1.05  sup_given_eliminated:                   0
% 2.71/1.05  comparisons_done:                       0
% 2.71/1.05  comparisons_avoided:                    0
% 2.71/1.05  
% 2.71/1.05  ------ Simplifications
% 2.71/1.05  
% 2.71/1.05  
% 2.71/1.05  sim_fw_subset_subsumed:                 10
% 2.71/1.05  sim_bw_subset_subsumed:                 7
% 2.71/1.05  sim_fw_subsumed:                        29
% 2.71/1.05  sim_bw_subsumed:                        9
% 2.71/1.05  sim_fw_subsumption_res:                 1
% 2.71/1.05  sim_bw_subsumption_res:                 0
% 2.71/1.05  sim_tautology_del:                      30
% 2.71/1.05  sim_eq_tautology_del:                   18
% 2.71/1.05  sim_eq_res_simp:                        1
% 2.71/1.05  sim_fw_demodulated:                     1
% 2.71/1.05  sim_bw_demodulated:                     0
% 2.71/1.05  sim_light_normalised:                   1
% 2.71/1.05  sim_joinable_taut:                      0
% 2.71/1.05  sim_joinable_simp:                      0
% 2.71/1.05  sim_ac_normalised:                      0
% 2.71/1.05  sim_smt_subsumption:                    0
% 2.71/1.05  
%------------------------------------------------------------------------------
