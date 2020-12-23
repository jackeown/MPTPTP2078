%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n002.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:28:34 EST 2020

% Result     : Theorem 2.31s
% Output     : CNFRefutation 2.31s
% Verified   : 
% Statistics : Number of formulae       :  158 (2127 expanded)
%              Number of clauses        :   93 ( 508 expanded)
%              Number of leaves         :   19 ( 412 expanded)
%              Depth                    :   30
%              Number of atoms          :  615 (16832 expanded)
%              Number of equality atoms :  143 ( 650 expanded)
%              Maximal formula depth    :   14 (   5 average)
%              Maximal clause size      :   22 (   3 average)
%              Maximal term depth       :    6 (   1 average)

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

fof(f58,plain,(
    ! [X0,X1] :
      ( v13_waybel_0(X1,X0)
      | m1_subset_1(sK2(X0,X1),u1_struct_0(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f39])).

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

fof(f67,plain,(
    l1_orders_2(sK3) ),
    inference(cnf_transformation,[],[f45])).

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

fof(f72,plain,
    ( r2_hidden(k3_yellow_0(sK3),sK4)
    | ~ v1_subset_1(sK4,u1_struct_0(sK3)) ),
    inference(cnf_transformation,[],[f45])).

fof(f70,plain,(
    m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(sK3))) ),
    inference(cnf_transformation,[],[f45])).

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

fof(f69,plain,(
    v13_waybel_0(sK4,sK3) ),
    inference(cnf_transformation,[],[f45])).

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

fof(f47,plain,(
    ! [X0,X1] :
      ( X0 = X1
      | ~ r2_hidden(sK0(X0,X1),X1)
      | ~ r2_hidden(sK0(X0,X1),X0) ) ),
    inference(cnf_transformation,[],[f34])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => ! [X2] :
          ( r2_hidden(X2,X1)
         => r2_hidden(X2,X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f18,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( r2_hidden(X2,X0)
          | ~ r2_hidden(X2,X1) )
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f50,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(X2,X0)
      | ~ r2_hidden(X2,X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f18])).

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

cnf(c_1,plain,
    ( r2_hidden(sK0(X0,X1),X1)
    | r2_hidden(sK0(X0,X1),X0)
    | X1 = X0 ),
    inference(cnf_transformation,[],[f46])).

cnf(c_1062,plain,
    ( X0 = X1
    | r2_hidden(sK0(X1,X0),X0) = iProver_top
    | r2_hidden(sK0(X1,X0),X1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1])).

cnf(c_5,plain,
    ( m1_subset_1(X0,X1)
    | ~ r2_hidden(X0,X1) ),
    inference(cnf_transformation,[],[f51])).

cnf(c_1059,plain,
    ( m1_subset_1(X0,X1) = iProver_top
    | r2_hidden(X0,X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_5])).

cnf(c_1555,plain,
    ( X0 = X1
    | m1_subset_1(sK0(X0,X1),X0) = iProver_top
    | r2_hidden(sK0(X0,X1),X1) = iProver_top ),
    inference(superposition,[status(thm)],[c_1062,c_1059])).

cnf(c_13,plain,
    ( v13_waybel_0(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | m1_subset_1(sK2(X1,X0),u1_struct_0(X1))
    | ~ l1_orders_2(X1) ),
    inference(cnf_transformation,[],[f58])).

cnf(c_23,negated_conjecture,
    ( l1_orders_2(sK3) ),
    inference(cnf_transformation,[],[f67])).

cnf(c_536,plain,
    ( v13_waybel_0(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | m1_subset_1(sK2(X1,X0),u1_struct_0(X1))
    | sK3 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_13,c_23])).

cnf(c_537,plain,
    ( v13_waybel_0(X0,sK3)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK3)))
    | m1_subset_1(sK2(sK3,X0),u1_struct_0(sK3)) ),
    inference(unflattening,[status(thm)],[c_536])).

cnf(c_1048,plain,
    ( v13_waybel_0(X0,sK3) = iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK3))) != iProver_top
    | m1_subset_1(sK2(sK3,X0),u1_struct_0(sK3)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_537])).

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

cnf(c_387,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | r2_hidden(k3_yellow_0(sK3),sK4)
    | X1 = X0
    | u1_struct_0(sK3) != X1
    | sK4 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_16,c_195])).

cnf(c_388,plain,
    ( ~ m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(sK3)))
    | r2_hidden(k3_yellow_0(sK3),sK4)
    | u1_struct_0(sK3) = sK4 ),
    inference(unflattening,[status(thm)],[c_387])).

cnf(c_20,negated_conjecture,
    ( m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(sK3))) ),
    inference(cnf_transformation,[],[f70])).

cnf(c_390,plain,
    ( r2_hidden(k3_yellow_0(sK3),sK4)
    | u1_struct_0(sK3) = sK4 ),
    inference(global_propositional_subsumption,[status(thm)],[c_388,c_20])).

cnf(c_1054,plain,
    ( u1_struct_0(sK3) = sK4
    | r2_hidden(k3_yellow_0(sK3),sK4) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_390])).

cnf(c_1057,plain,
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

cnf(c_363,plain,
    ( r1_orders_2(X0,k3_yellow_0(X0),X1)
    | ~ m1_subset_1(X1,u1_struct_0(X0))
    | v2_struct_0(X0)
    | ~ v5_orders_2(X0)
    | ~ l1_orders_2(X0)
    | sK3 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_9,c_24])).

cnf(c_364,plain,
    ( r1_orders_2(sK3,k3_yellow_0(sK3),X0)
    | ~ m1_subset_1(X0,u1_struct_0(sK3))
    | v2_struct_0(sK3)
    | ~ v5_orders_2(sK3)
    | ~ l1_orders_2(sK3) ),
    inference(unflattening,[status(thm)],[c_363])).

cnf(c_26,negated_conjecture,
    ( ~ v2_struct_0(sK3) ),
    inference(cnf_transformation,[],[f64])).

cnf(c_25,negated_conjecture,
    ( v5_orders_2(sK3) ),
    inference(cnf_transformation,[],[f65])).

cnf(c_368,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(sK3))
    | r1_orders_2(sK3,k3_yellow_0(sK3),X0) ),
    inference(global_propositional_subsumption,[status(thm)],[c_364,c_26,c_25,c_23])).

cnf(c_369,plain,
    ( r1_orders_2(sK3,k3_yellow_0(sK3),X0)
    | ~ m1_subset_1(X0,u1_struct_0(sK3)) ),
    inference(renaming,[status(thm)],[c_368])).

cnf(c_451,plain,
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
    inference(resolution_lifted,[status(thm)],[c_15,c_369])).

cnf(c_452,plain,
    ( ~ v13_waybel_0(X0,sK3)
    | ~ m1_subset_1(X1,u1_struct_0(sK3))
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK3)))
    | ~ m1_subset_1(k3_yellow_0(sK3),u1_struct_0(sK3))
    | r2_hidden(X1,X0)
    | ~ r2_hidden(k3_yellow_0(sK3),X0)
    | ~ l1_orders_2(sK3) ),
    inference(unflattening,[status(thm)],[c_451])).

cnf(c_8,plain,
    ( m1_subset_1(k3_yellow_0(X0),u1_struct_0(X0))
    | ~ l1_orders_2(X0) ),
    inference(cnf_transformation,[],[f54])).

cnf(c_62,plain,
    ( m1_subset_1(k3_yellow_0(sK3),u1_struct_0(sK3))
    | ~ l1_orders_2(sK3) ),
    inference(instantiation,[status(thm)],[c_8])).

cnf(c_456,plain,
    ( ~ r2_hidden(k3_yellow_0(sK3),X0)
    | r2_hidden(X1,X0)
    | ~ v13_waybel_0(X0,sK3)
    | ~ m1_subset_1(X1,u1_struct_0(sK3))
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK3))) ),
    inference(global_propositional_subsumption,[status(thm)],[c_452,c_23,c_62])).

cnf(c_457,plain,
    ( ~ v13_waybel_0(X0,sK3)
    | ~ m1_subset_1(X1,u1_struct_0(sK3))
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK3)))
    | r2_hidden(X1,X0)
    | ~ r2_hidden(k3_yellow_0(sK3),X0) ),
    inference(renaming,[status(thm)],[c_456])).

cnf(c_1052,plain,
    ( v13_waybel_0(X0,sK3) != iProver_top
    | m1_subset_1(X1,u1_struct_0(sK3)) != iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK3))) != iProver_top
    | r2_hidden(X1,X0) = iProver_top
    | r2_hidden(k3_yellow_0(sK3),X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_457])).

cnf(c_1685,plain,
    ( v13_waybel_0(sK4,sK3) != iProver_top
    | m1_subset_1(X0,u1_struct_0(sK3)) != iProver_top
    | r2_hidden(X0,sK4) = iProver_top
    | r2_hidden(k3_yellow_0(sK3),sK4) != iProver_top ),
    inference(superposition,[status(thm)],[c_1057,c_1052])).

cnf(c_21,negated_conjecture,
    ( v13_waybel_0(sK4,sK3) ),
    inference(cnf_transformation,[],[f69])).

cnf(c_32,plain,
    ( v13_waybel_0(sK4,sK3) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_21])).

cnf(c_1833,plain,
    ( m1_subset_1(X0,u1_struct_0(sK3)) != iProver_top
    | r2_hidden(X0,sK4) = iProver_top
    | r2_hidden(k3_yellow_0(sK3),sK4) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_1685,c_32])).

cnf(c_1924,plain,
    ( u1_struct_0(sK3) = sK4
    | m1_subset_1(X0,u1_struct_0(sK3)) != iProver_top
    | r2_hidden(X0,sK4) = iProver_top ),
    inference(superposition,[status(thm)],[c_1054,c_1833])).

cnf(c_2514,plain,
    ( u1_struct_0(sK3) = sK4
    | v13_waybel_0(X0,sK3) = iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK3))) != iProver_top
    | r2_hidden(sK2(sK3,X0),sK4) = iProver_top ),
    inference(superposition,[status(thm)],[c_1048,c_1924])).

cnf(c_3017,plain,
    ( u1_struct_0(sK3) = sK4
    | k1_zfmisc_1(u1_struct_0(sK3)) = X0
    | v13_waybel_0(sK0(k1_zfmisc_1(u1_struct_0(sK3)),X0),sK3) = iProver_top
    | r2_hidden(sK2(sK3,sK0(k1_zfmisc_1(u1_struct_0(sK3)),X0)),sK4) = iProver_top
    | r2_hidden(sK0(k1_zfmisc_1(u1_struct_0(sK3)),X0),X0) = iProver_top ),
    inference(superposition,[status(thm)],[c_1555,c_2514])).

cnf(c_3011,plain,
    ( X0 = X1
    | m1_subset_1(sK0(X1,X0),X1) = iProver_top
    | m1_subset_1(sK0(X1,X0),X0) = iProver_top ),
    inference(superposition,[status(thm)],[c_1555,c_1059])).

cnf(c_6,plain,
    ( ~ m1_subset_1(X0,X1)
    | r2_hidden(X0,X1)
    | v1_xboole_0(X1) ),
    inference(cnf_transformation,[],[f52])).

cnf(c_22,negated_conjecture,
    ( ~ v1_xboole_0(sK4) ),
    inference(cnf_transformation,[],[f68])).

cnf(c_348,plain,
    ( ~ m1_subset_1(X0,X1)
    | r2_hidden(X0,X1)
    | sK4 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_6,c_22])).

cnf(c_349,plain,
    ( ~ m1_subset_1(X0,sK4)
    | r2_hidden(X0,sK4) ),
    inference(unflattening,[status(thm)],[c_348])).

cnf(c_1055,plain,
    ( m1_subset_1(X0,sK4) != iProver_top
    | r2_hidden(X0,sK4) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_349])).

cnf(c_3369,plain,
    ( sK4 = X0
    | m1_subset_1(sK0(X0,sK4),X0) = iProver_top
    | r2_hidden(sK0(X0,sK4),sK4) = iProver_top ),
    inference(superposition,[status(thm)],[c_3011,c_1055])).

cnf(c_3755,plain,
    ( u1_struct_0(sK3) = sK4
    | r2_hidden(sK0(u1_struct_0(sK3),sK4),sK4) = iProver_top ),
    inference(superposition,[status(thm)],[c_3369,c_1924])).

cnf(c_0,plain,
    ( ~ r2_hidden(sK0(X0,X1),X1)
    | ~ r2_hidden(sK0(X0,X1),X0)
    | X1 = X0 ),
    inference(cnf_transformation,[],[f47])).

cnf(c_1063,plain,
    ( X0 = X1
    | r2_hidden(sK0(X1,X0),X0) != iProver_top
    | r2_hidden(sK0(X1,X0),X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_0])).

cnf(c_7504,plain,
    ( u1_struct_0(sK3) = sK4
    | r2_hidden(sK0(u1_struct_0(sK3),sK4),u1_struct_0(sK3)) != iProver_top ),
    inference(superposition,[status(thm)],[c_3755,c_1063])).

cnf(c_4,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | ~ r2_hidden(X2,X0)
    | r2_hidden(X2,X1) ),
    inference(cnf_transformation,[],[f50])).

cnf(c_1060,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(X1)) != iProver_top
    | r2_hidden(X2,X0) != iProver_top
    | r2_hidden(X2,X1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_4])).

cnf(c_2009,plain,
    ( r2_hidden(X0,u1_struct_0(sK3)) = iProver_top
    | r2_hidden(X0,sK4) != iProver_top ),
    inference(superposition,[status(thm)],[c_1057,c_1060])).

cnf(c_3,plain,
    ( m1_subset_1(k2_subset_1(X0),k1_zfmisc_1(X0)) ),
    inference(cnf_transformation,[],[f49])).

cnf(c_1061,plain,
    ( m1_subset_1(k2_subset_1(X0),k1_zfmisc_1(X0)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3])).

cnf(c_2,plain,
    ( k2_subset_1(X0) = X0 ),
    inference(cnf_transformation,[],[f48])).

cnf(c_1072,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(X0)) = iProver_top ),
    inference(light_normalisation,[status(thm)],[c_1061,c_2])).

cnf(c_1684,plain,
    ( v13_waybel_0(u1_struct_0(sK3),sK3) != iProver_top
    | m1_subset_1(X0,u1_struct_0(sK3)) != iProver_top
    | r2_hidden(X0,u1_struct_0(sK3)) = iProver_top
    | r2_hidden(k3_yellow_0(sK3),u1_struct_0(sK3)) != iProver_top ),
    inference(superposition,[status(thm)],[c_1072,c_1052])).

cnf(c_2194,plain,
    ( v13_waybel_0(u1_struct_0(sK3),sK3) != iProver_top
    | m1_subset_1(X0,u1_struct_0(sK3)) != iProver_top
    | r2_hidden(X0,u1_struct_0(sK3)) = iProver_top
    | r2_hidden(k3_yellow_0(sK3),sK4) != iProver_top ),
    inference(superposition,[status(thm)],[c_2009,c_1684])).

cnf(c_2494,plain,
    ( m1_subset_1(X0,u1_struct_0(sK3)) != iProver_top
    | r2_hidden(X0,u1_struct_0(sK3)) = iProver_top
    | r2_hidden(k3_yellow_0(sK3),sK4) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_2194,c_32,c_1685,c_2009])).

cnf(c_2503,plain,
    ( u1_struct_0(sK3) = sK4
    | m1_subset_1(X0,u1_struct_0(sK3)) != iProver_top
    | r2_hidden(X0,u1_struct_0(sK3)) = iProver_top ),
    inference(superposition,[status(thm)],[c_1054,c_2494])).

cnf(c_5082,plain,
    ( u1_struct_0(sK3) = sK4
    | r2_hidden(sK0(u1_struct_0(sK3),sK4),u1_struct_0(sK3)) = iProver_top
    | r2_hidden(sK0(u1_struct_0(sK3),sK4),sK4) = iProver_top ),
    inference(superposition,[status(thm)],[c_3369,c_2503])).

cnf(c_734,plain,
    ( X0 != X1
    | k3_yellow_0(X0) = k3_yellow_0(X1) ),
    theory(equality)).

cnf(c_742,plain,
    ( k3_yellow_0(sK3) = k3_yellow_0(sK3)
    | sK3 != sK3 ),
    inference(instantiation,[status(thm)],[c_734])).

cnf(c_729,plain,
    ( X0 = X0 ),
    theory(equality)).

cnf(c_748,plain,
    ( sK3 = sK3 ),
    inference(instantiation,[status(thm)],[c_729])).

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

cnf(c_401,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X0))
    | ~ r2_hidden(k3_yellow_0(sK3),sK4)
    | u1_struct_0(sK3) != X0
    | sK4 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_17,c_193])).

cnf(c_402,plain,
    ( ~ m1_subset_1(u1_struct_0(sK3),k1_zfmisc_1(u1_struct_0(sK3)))
    | ~ r2_hidden(k3_yellow_0(sK3),sK4)
    | sK4 != u1_struct_0(sK3) ),
    inference(unflattening,[status(thm)],[c_401])).

cnf(c_1053,plain,
    ( sK4 != u1_struct_0(sK3)
    | m1_subset_1(u1_struct_0(sK3),k1_zfmisc_1(u1_struct_0(sK3))) != iProver_top
    | r2_hidden(k3_yellow_0(sK3),sK4) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_402])).

cnf(c_1138,plain,
    ( u1_struct_0(sK3) != sK4
    | r2_hidden(k3_yellow_0(sK3),sK4) != iProver_top ),
    inference(forward_subsumption_resolution,[status(thm)],[c_1053,c_1072])).

cnf(c_1166,plain,
    ( ~ r2_hidden(k3_yellow_0(sK3),sK4)
    | u1_struct_0(sK3) != sK4 ),
    inference(predicate_to_equality_rev,[status(thm)],[c_1138])).

cnf(c_1258,plain,
    ( r2_hidden(sK0(u1_struct_0(sK3),sK4),u1_struct_0(sK3))
    | r2_hidden(sK0(u1_struct_0(sK3),sK4),sK4)
    | sK4 = u1_struct_0(sK3) ),
    inference(instantiation,[status(thm)],[c_1])).

cnf(c_1259,plain,
    ( sK4 = u1_struct_0(sK3)
    | r2_hidden(sK0(u1_struct_0(sK3),sK4),u1_struct_0(sK3)) = iProver_top
    | r2_hidden(sK0(u1_struct_0(sK3),sK4),sK4) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1258])).

cnf(c_2313,plain,
    ( ~ m1_subset_1(k3_yellow_0(sK3),sK4)
    | r2_hidden(k3_yellow_0(sK3),sK4) ),
    inference(instantiation,[status(thm)],[c_349])).

cnf(c_733,plain,
    ( ~ m1_subset_1(X0,X1)
    | m1_subset_1(X2,X3)
    | X2 != X0
    | X3 != X1 ),
    theory(equality)).

cnf(c_1276,plain,
    ( m1_subset_1(X0,X1)
    | ~ m1_subset_1(k3_yellow_0(sK3),u1_struct_0(sK3))
    | X1 != u1_struct_0(sK3)
    | X0 != k3_yellow_0(sK3) ),
    inference(instantiation,[status(thm)],[c_733])).

cnf(c_1544,plain,
    ( m1_subset_1(X0,sK4)
    | ~ m1_subset_1(k3_yellow_0(sK3),u1_struct_0(sK3))
    | X0 != k3_yellow_0(sK3)
    | sK4 != u1_struct_0(sK3) ),
    inference(instantiation,[status(thm)],[c_1276])).

cnf(c_4380,plain,
    ( ~ m1_subset_1(k3_yellow_0(sK3),u1_struct_0(sK3))
    | m1_subset_1(k3_yellow_0(sK3),sK4)
    | k3_yellow_0(sK3) != k3_yellow_0(sK3)
    | sK4 != u1_struct_0(sK3) ),
    inference(instantiation,[status(thm)],[c_1544])).

cnf(c_7525,plain,
    ( r2_hidden(sK0(u1_struct_0(sK3),sK4),u1_struct_0(sK3)) = iProver_top
    | r2_hidden(sK0(u1_struct_0(sK3),sK4),sK4) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_5082,c_23,c_62,c_742,c_748,c_1166,c_1259,c_2313,c_3755,c_4380])).

cnf(c_7531,plain,
    ( r2_hidden(sK0(u1_struct_0(sK3),sK4),u1_struct_0(sK3)) = iProver_top ),
    inference(forward_subsumption_resolution,[status(thm)],[c_7525,c_2009])).

cnf(c_7536,plain,
    ( u1_struct_0(sK3) = sK4 ),
    inference(global_propositional_subsumption,[status(thm)],[c_3017,c_7504,c_7531])).

cnf(c_492,plain,
    ( m1_subset_1(k3_yellow_0(X0),u1_struct_0(X0))
    | sK3 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_8,c_23])).

cnf(c_493,plain,
    ( m1_subset_1(k3_yellow_0(sK3),u1_struct_0(sK3)) ),
    inference(unflattening,[status(thm)],[c_492])).

cnf(c_1051,plain,
    ( m1_subset_1(k3_yellow_0(sK3),u1_struct_0(sK3)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_493])).

cnf(c_7580,plain,
    ( m1_subset_1(k3_yellow_0(sK3),sK4) = iProver_top ),
    inference(demodulation,[status(thm)],[c_7536,c_1051])).

cnf(c_2314,plain,
    ( m1_subset_1(k3_yellow_0(sK3),sK4) != iProver_top
    | r2_hidden(k3_yellow_0(sK3),sK4) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2313])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_7580,c_7531,c_7504,c_2314,c_1138])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.12  % Command    : iproveropt_run.sh %d %s
% 0.12/0.33  % Computer   : n002.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.33  % CPULimit   : 60
% 0.12/0.33  % WCLimit    : 600
% 0.12/0.33  % DateTime   : Tue Dec  1 17:37:06 EST 2020
% 0.12/0.33  % CPUTime    : 
% 0.12/0.33  % Running in FOF mode
% 2.31/0.92  % SZS status Started for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.31/0.92  
% 2.31/0.92  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 2.31/0.92  
% 2.31/0.92  ------  iProver source info
% 2.31/0.92  
% 2.31/0.92  git: date: 2020-06-30 10:37:57 +0100
% 2.31/0.92  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 2.31/0.92  git: non_committed_changes: false
% 2.31/0.92  git: last_make_outside_of_git: false
% 2.31/0.92  
% 2.31/0.92  ------ 
% 2.31/0.92  
% 2.31/0.92  ------ Input Options
% 2.31/0.92  
% 2.31/0.92  --out_options                           all
% 2.31/0.92  --tptp_safe_out                         true
% 2.31/0.92  --problem_path                          ""
% 2.31/0.92  --include_path                          ""
% 2.31/0.92  --clausifier                            res/vclausify_rel
% 2.31/0.92  --clausifier_options                    --mode clausify
% 2.31/0.92  --stdin                                 false
% 2.31/0.92  --stats_out                             all
% 2.31/0.92  
% 2.31/0.92  ------ General Options
% 2.31/0.92  
% 2.31/0.92  --fof                                   false
% 2.31/0.92  --time_out_real                         305.
% 2.31/0.92  --time_out_virtual                      -1.
% 2.31/0.92  --symbol_type_check                     false
% 2.31/0.92  --clausify_out                          false
% 2.31/0.92  --sig_cnt_out                           false
% 2.31/0.92  --trig_cnt_out                          false
% 2.31/0.92  --trig_cnt_out_tolerance                1.
% 2.31/0.92  --trig_cnt_out_sk_spl                   false
% 2.31/0.92  --abstr_cl_out                          false
% 2.31/0.92  
% 2.31/0.92  ------ Global Options
% 2.31/0.92  
% 2.31/0.92  --schedule                              default
% 2.31/0.92  --add_important_lit                     false
% 2.31/0.92  --prop_solver_per_cl                    1000
% 2.31/0.92  --min_unsat_core                        false
% 2.31/0.92  --soft_assumptions                      false
% 2.31/0.92  --soft_lemma_size                       3
% 2.31/0.92  --prop_impl_unit_size                   0
% 2.31/0.92  --prop_impl_unit                        []
% 2.31/0.92  --share_sel_clauses                     true
% 2.31/0.92  --reset_solvers                         false
% 2.31/0.92  --bc_imp_inh                            [conj_cone]
% 2.31/0.92  --conj_cone_tolerance                   3.
% 2.31/0.92  --extra_neg_conj                        none
% 2.31/0.92  --large_theory_mode                     true
% 2.31/0.92  --prolific_symb_bound                   200
% 2.31/0.92  --lt_threshold                          2000
% 2.31/0.92  --clause_weak_htbl                      true
% 2.31/0.92  --gc_record_bc_elim                     false
% 2.31/0.92  
% 2.31/0.92  ------ Preprocessing Options
% 2.31/0.92  
% 2.31/0.92  --preprocessing_flag                    true
% 2.31/0.92  --time_out_prep_mult                    0.1
% 2.31/0.92  --splitting_mode                        input
% 2.31/0.92  --splitting_grd                         true
% 2.31/0.92  --splitting_cvd                         false
% 2.31/0.92  --splitting_cvd_svl                     false
% 2.31/0.92  --splitting_nvd                         32
% 2.31/0.92  --sub_typing                            true
% 2.31/0.92  --prep_gs_sim                           true
% 2.31/0.92  --prep_unflatten                        true
% 2.31/0.92  --prep_res_sim                          true
% 2.31/0.92  --prep_upred                            true
% 2.31/0.92  --prep_sem_filter                       exhaustive
% 2.31/0.92  --prep_sem_filter_out                   false
% 2.31/0.92  --pred_elim                             true
% 2.31/0.92  --res_sim_input                         true
% 2.31/0.92  --eq_ax_congr_red                       true
% 2.31/0.92  --pure_diseq_elim                       true
% 2.31/0.92  --brand_transform                       false
% 2.31/0.92  --non_eq_to_eq                          false
% 2.31/0.92  --prep_def_merge                        true
% 2.31/0.92  --prep_def_merge_prop_impl              false
% 2.31/0.92  --prep_def_merge_mbd                    true
% 2.31/0.92  --prep_def_merge_tr_red                 false
% 2.31/0.92  --prep_def_merge_tr_cl                  false
% 2.31/0.92  --smt_preprocessing                     true
% 2.31/0.92  --smt_ac_axioms                         fast
% 2.31/0.92  --preprocessed_out                      false
% 2.31/0.92  --preprocessed_stats                    false
% 2.31/0.92  
% 2.31/0.92  ------ Abstraction refinement Options
% 2.31/0.92  
% 2.31/0.92  --abstr_ref                             []
% 2.31/0.92  --abstr_ref_prep                        false
% 2.31/0.92  --abstr_ref_until_sat                   false
% 2.31/0.92  --abstr_ref_sig_restrict                funpre
% 2.31/0.92  --abstr_ref_af_restrict_to_split_sk     false
% 2.31/0.92  --abstr_ref_under                       []
% 2.31/0.92  
% 2.31/0.92  ------ SAT Options
% 2.31/0.92  
% 2.31/0.92  --sat_mode                              false
% 2.31/0.92  --sat_fm_restart_options                ""
% 2.31/0.92  --sat_gr_def                            false
% 2.31/0.92  --sat_epr_types                         true
% 2.31/0.92  --sat_non_cyclic_types                  false
% 2.31/0.92  --sat_finite_models                     false
% 2.31/0.92  --sat_fm_lemmas                         false
% 2.31/0.92  --sat_fm_prep                           false
% 2.31/0.92  --sat_fm_uc_incr                        true
% 2.31/0.92  --sat_out_model                         small
% 2.31/0.92  --sat_out_clauses                       false
% 2.31/0.92  
% 2.31/0.92  ------ QBF Options
% 2.31/0.92  
% 2.31/0.92  --qbf_mode                              false
% 2.31/0.92  --qbf_elim_univ                         false
% 2.31/0.92  --qbf_dom_inst                          none
% 2.31/0.92  --qbf_dom_pre_inst                      false
% 2.31/0.92  --qbf_sk_in                             false
% 2.31/0.92  --qbf_pred_elim                         true
% 2.31/0.92  --qbf_split                             512
% 2.31/0.92  
% 2.31/0.92  ------ BMC1 Options
% 2.31/0.92  
% 2.31/0.92  --bmc1_incremental                      false
% 2.31/0.92  --bmc1_axioms                           reachable_all
% 2.31/0.92  --bmc1_min_bound                        0
% 2.31/0.92  --bmc1_max_bound                        -1
% 2.31/0.92  --bmc1_max_bound_default                -1
% 2.31/0.92  --bmc1_symbol_reachability              true
% 2.31/0.92  --bmc1_property_lemmas                  false
% 2.31/0.92  --bmc1_k_induction                      false
% 2.31/0.92  --bmc1_non_equiv_states                 false
% 2.31/0.92  --bmc1_deadlock                         false
% 2.31/0.92  --bmc1_ucm                              false
% 2.31/0.92  --bmc1_add_unsat_core                   none
% 2.31/0.92  --bmc1_unsat_core_children              false
% 2.31/0.92  --bmc1_unsat_core_extrapolate_axioms    false
% 2.31/0.92  --bmc1_out_stat                         full
% 2.31/0.92  --bmc1_ground_init                      false
% 2.31/0.92  --bmc1_pre_inst_next_state              false
% 2.31/0.92  --bmc1_pre_inst_state                   false
% 2.31/0.92  --bmc1_pre_inst_reach_state             false
% 2.31/0.92  --bmc1_out_unsat_core                   false
% 2.31/0.92  --bmc1_aig_witness_out                  false
% 2.31/0.92  --bmc1_verbose                          false
% 2.31/0.92  --bmc1_dump_clauses_tptp                false
% 2.31/0.92  --bmc1_dump_unsat_core_tptp             false
% 2.31/0.92  --bmc1_dump_file                        -
% 2.31/0.92  --bmc1_ucm_expand_uc_limit              128
% 2.31/0.92  --bmc1_ucm_n_expand_iterations          6
% 2.31/0.92  --bmc1_ucm_extend_mode                  1
% 2.31/0.92  --bmc1_ucm_init_mode                    2
% 2.31/0.92  --bmc1_ucm_cone_mode                    none
% 2.31/0.92  --bmc1_ucm_reduced_relation_type        0
% 2.31/0.92  --bmc1_ucm_relax_model                  4
% 2.31/0.92  --bmc1_ucm_full_tr_after_sat            true
% 2.31/0.92  --bmc1_ucm_expand_neg_assumptions       false
% 2.31/0.92  --bmc1_ucm_layered_model                none
% 2.31/0.92  --bmc1_ucm_max_lemma_size               10
% 2.31/0.92  
% 2.31/0.92  ------ AIG Options
% 2.31/0.92  
% 2.31/0.92  --aig_mode                              false
% 2.31/0.92  
% 2.31/0.92  ------ Instantiation Options
% 2.31/0.92  
% 2.31/0.92  --instantiation_flag                    true
% 2.31/0.92  --inst_sos_flag                         false
% 2.31/0.92  --inst_sos_phase                        true
% 2.31/0.92  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 2.31/0.92  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 2.31/0.92  --inst_lit_sel_side                     num_symb
% 2.31/0.92  --inst_solver_per_active                1400
% 2.31/0.92  --inst_solver_calls_frac                1.
% 2.31/0.92  --inst_passive_queue_type               priority_queues
% 2.31/0.92  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 2.31/0.92  --inst_passive_queues_freq              [25;2]
% 2.31/0.92  --inst_dismatching                      true
% 2.31/0.92  --inst_eager_unprocessed_to_passive     true
% 2.31/0.92  --inst_prop_sim_given                   true
% 2.31/0.92  --inst_prop_sim_new                     false
% 2.31/0.92  --inst_subs_new                         false
% 2.31/0.92  --inst_eq_res_simp                      false
% 2.31/0.92  --inst_subs_given                       false
% 2.31/0.92  --inst_orphan_elimination               true
% 2.31/0.92  --inst_learning_loop_flag               true
% 2.31/0.92  --inst_learning_start                   3000
% 2.31/0.92  --inst_learning_factor                  2
% 2.31/0.92  --inst_start_prop_sim_after_learn       3
% 2.31/0.92  --inst_sel_renew                        solver
% 2.31/0.92  --inst_lit_activity_flag                true
% 2.31/0.92  --inst_restr_to_given                   false
% 2.31/0.92  --inst_activity_threshold               500
% 2.31/0.92  --inst_out_proof                        true
% 2.31/0.92  
% 2.31/0.92  ------ Resolution Options
% 2.31/0.92  
% 2.31/0.92  --resolution_flag                       true
% 2.31/0.92  --res_lit_sel                           adaptive
% 2.31/0.92  --res_lit_sel_side                      none
% 2.31/0.92  --res_ordering                          kbo
% 2.31/0.92  --res_to_prop_solver                    active
% 2.31/0.92  --res_prop_simpl_new                    false
% 2.31/0.92  --res_prop_simpl_given                  true
% 2.31/0.92  --res_passive_queue_type                priority_queues
% 2.31/0.92  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 2.31/0.92  --res_passive_queues_freq               [15;5]
% 2.31/0.92  --res_forward_subs                      full
% 2.31/0.92  --res_backward_subs                     full
% 2.31/0.92  --res_forward_subs_resolution           true
% 2.31/0.92  --res_backward_subs_resolution          true
% 2.31/0.92  --res_orphan_elimination                true
% 2.31/0.92  --res_time_limit                        2.
% 2.31/0.92  --res_out_proof                         true
% 2.31/0.92  
% 2.31/0.92  ------ Superposition Options
% 2.31/0.92  
% 2.31/0.92  --superposition_flag                    true
% 2.31/0.92  --sup_passive_queue_type                priority_queues
% 2.31/0.92  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 2.31/0.92  --sup_passive_queues_freq               [8;1;4]
% 2.31/0.92  --demod_completeness_check              fast
% 2.31/0.92  --demod_use_ground                      true
% 2.31/0.92  --sup_to_prop_solver                    passive
% 2.31/0.92  --sup_prop_simpl_new                    true
% 2.31/0.92  --sup_prop_simpl_given                  true
% 2.31/0.92  --sup_fun_splitting                     false
% 2.31/0.92  --sup_smt_interval                      50000
% 2.31/0.92  
% 2.31/0.92  ------ Superposition Simplification Setup
% 2.31/0.92  
% 2.31/0.92  --sup_indices_passive                   []
% 2.31/0.92  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.31/0.92  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.31/0.92  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.31/0.92  --sup_full_triv                         [TrivRules;PropSubs]
% 2.31/0.92  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.31/0.92  --sup_full_bw                           [BwDemod]
% 2.31/0.92  --sup_immed_triv                        [TrivRules]
% 2.31/0.92  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 2.31/0.92  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.31/0.92  --sup_immed_bw_main                     []
% 2.31/0.92  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.31/0.92  --sup_input_triv                        [Unflattening;TrivRules]
% 2.31/0.92  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.31/0.92  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.31/0.92  
% 2.31/0.92  ------ Combination Options
% 2.31/0.92  
% 2.31/0.92  --comb_res_mult                         3
% 2.31/0.92  --comb_sup_mult                         2
% 2.31/0.92  --comb_inst_mult                        10
% 2.31/0.92  
% 2.31/0.92  ------ Debug Options
% 2.31/0.92  
% 2.31/0.92  --dbg_backtrace                         false
% 2.31/0.92  --dbg_dump_prop_clauses                 false
% 2.31/0.92  --dbg_dump_prop_clauses_file            -
% 2.31/0.92  --dbg_out_stat                          false
% 2.31/0.92  ------ Parsing...
% 2.31/0.92  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 2.31/0.92  
% 2.31/0.92  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe:1:0s pe:2:0s pe:4:0s pe_e  sf_s  rm: 8 0s  sf_e  pe_s  pe_e 
% 2.31/0.92  
% 2.31/0.92  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 2.31/0.92  
% 2.31/0.92  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 2.31/0.92  ------ Proving...
% 2.31/0.92  ------ Problem Properties 
% 2.31/0.92  
% 2.31/0.92  
% 2.31/0.92  clauses                                 19
% 2.31/0.92  conjectures                             2
% 2.31/0.92  EPR                                     3
% 2.31/0.92  Horn                                    13
% 2.31/0.92  unary                                   5
% 2.31/0.92  binary                                  3
% 2.31/0.92  lits                                    49
% 2.31/0.92  lits eq                                 5
% 2.31/0.92  fd_pure                                 0
% 2.31/0.92  fd_pseudo                               0
% 2.31/0.92  fd_cond                                 0
% 2.31/0.92  fd_pseudo_cond                          2
% 2.31/0.92  AC symbols                              0
% 2.31/0.92  
% 2.31/0.92  ------ Schedule dynamic 5 is on 
% 2.31/0.92  
% 2.31/0.92  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" Time Limit: 10.
% 2.31/0.92  
% 2.31/0.92  
% 2.31/0.92  ------ 
% 2.31/0.92  Current options:
% 2.31/0.92  ------ 
% 2.31/0.92  
% 2.31/0.92  ------ Input Options
% 2.31/0.92  
% 2.31/0.92  --out_options                           all
% 2.31/0.92  --tptp_safe_out                         true
% 2.31/0.92  --problem_path                          ""
% 2.31/0.92  --include_path                          ""
% 2.31/0.92  --clausifier                            res/vclausify_rel
% 2.31/0.92  --clausifier_options                    --mode clausify
% 2.31/0.92  --stdin                                 false
% 2.31/0.92  --stats_out                             all
% 2.31/0.92  
% 2.31/0.92  ------ General Options
% 2.31/0.92  
% 2.31/0.92  --fof                                   false
% 2.31/0.92  --time_out_real                         305.
% 2.31/0.92  --time_out_virtual                      -1.
% 2.31/0.92  --symbol_type_check                     false
% 2.31/0.92  --clausify_out                          false
% 2.31/0.92  --sig_cnt_out                           false
% 2.31/0.92  --trig_cnt_out                          false
% 2.31/0.92  --trig_cnt_out_tolerance                1.
% 2.31/0.92  --trig_cnt_out_sk_spl                   false
% 2.31/0.92  --abstr_cl_out                          false
% 2.31/0.92  
% 2.31/0.92  ------ Global Options
% 2.31/0.92  
% 2.31/0.92  --schedule                              default
% 2.31/0.92  --add_important_lit                     false
% 2.31/0.92  --prop_solver_per_cl                    1000
% 2.31/0.92  --min_unsat_core                        false
% 2.31/0.92  --soft_assumptions                      false
% 2.31/0.92  --soft_lemma_size                       3
% 2.31/0.92  --prop_impl_unit_size                   0
% 2.31/0.92  --prop_impl_unit                        []
% 2.31/0.92  --share_sel_clauses                     true
% 2.31/0.92  --reset_solvers                         false
% 2.31/0.92  --bc_imp_inh                            [conj_cone]
% 2.31/0.92  --conj_cone_tolerance                   3.
% 2.31/0.92  --extra_neg_conj                        none
% 2.31/0.92  --large_theory_mode                     true
% 2.31/0.92  --prolific_symb_bound                   200
% 2.31/0.92  --lt_threshold                          2000
% 2.31/0.92  --clause_weak_htbl                      true
% 2.31/0.92  --gc_record_bc_elim                     false
% 2.31/0.92  
% 2.31/0.92  ------ Preprocessing Options
% 2.31/0.92  
% 2.31/0.92  --preprocessing_flag                    true
% 2.31/0.92  --time_out_prep_mult                    0.1
% 2.31/0.92  --splitting_mode                        input
% 2.31/0.92  --splitting_grd                         true
% 2.31/0.92  --splitting_cvd                         false
% 2.31/0.92  --splitting_cvd_svl                     false
% 2.31/0.92  --splitting_nvd                         32
% 2.31/0.92  --sub_typing                            true
% 2.31/0.92  --prep_gs_sim                           true
% 2.31/0.92  --prep_unflatten                        true
% 2.31/0.92  --prep_res_sim                          true
% 2.31/0.92  --prep_upred                            true
% 2.31/0.92  --prep_sem_filter                       exhaustive
% 2.31/0.92  --prep_sem_filter_out                   false
% 2.31/0.92  --pred_elim                             true
% 2.31/0.92  --res_sim_input                         true
% 2.31/0.92  --eq_ax_congr_red                       true
% 2.31/0.92  --pure_diseq_elim                       true
% 2.31/0.92  --brand_transform                       false
% 2.31/0.92  --non_eq_to_eq                          false
% 2.31/0.92  --prep_def_merge                        true
% 2.31/0.92  --prep_def_merge_prop_impl              false
% 2.31/0.92  --prep_def_merge_mbd                    true
% 2.31/0.92  --prep_def_merge_tr_red                 false
% 2.31/0.92  --prep_def_merge_tr_cl                  false
% 2.31/0.92  --smt_preprocessing                     true
% 2.31/0.92  --smt_ac_axioms                         fast
% 2.31/0.92  --preprocessed_out                      false
% 2.31/0.92  --preprocessed_stats                    false
% 2.31/0.92  
% 2.31/0.92  ------ Abstraction refinement Options
% 2.31/0.92  
% 2.31/0.92  --abstr_ref                             []
% 2.31/0.92  --abstr_ref_prep                        false
% 2.31/0.92  --abstr_ref_until_sat                   false
% 2.31/0.92  --abstr_ref_sig_restrict                funpre
% 2.31/0.92  --abstr_ref_af_restrict_to_split_sk     false
% 2.31/0.92  --abstr_ref_under                       []
% 2.31/0.92  
% 2.31/0.92  ------ SAT Options
% 2.31/0.92  
% 2.31/0.92  --sat_mode                              false
% 2.31/0.92  --sat_fm_restart_options                ""
% 2.31/0.92  --sat_gr_def                            false
% 2.31/0.92  --sat_epr_types                         true
% 2.31/0.92  --sat_non_cyclic_types                  false
% 2.31/0.92  --sat_finite_models                     false
% 2.31/0.92  --sat_fm_lemmas                         false
% 2.31/0.92  --sat_fm_prep                           false
% 2.31/0.92  --sat_fm_uc_incr                        true
% 2.31/0.92  --sat_out_model                         small
% 2.31/0.92  --sat_out_clauses                       false
% 2.31/0.92  
% 2.31/0.92  ------ QBF Options
% 2.31/0.92  
% 2.31/0.92  --qbf_mode                              false
% 2.31/0.92  --qbf_elim_univ                         false
% 2.31/0.92  --qbf_dom_inst                          none
% 2.31/0.92  --qbf_dom_pre_inst                      false
% 2.31/0.92  --qbf_sk_in                             false
% 2.31/0.92  --qbf_pred_elim                         true
% 2.31/0.92  --qbf_split                             512
% 2.31/0.92  
% 2.31/0.92  ------ BMC1 Options
% 2.31/0.92  
% 2.31/0.92  --bmc1_incremental                      false
% 2.31/0.92  --bmc1_axioms                           reachable_all
% 2.31/0.92  --bmc1_min_bound                        0
% 2.31/0.92  --bmc1_max_bound                        -1
% 2.31/0.92  --bmc1_max_bound_default                -1
% 2.31/0.92  --bmc1_symbol_reachability              true
% 2.31/0.92  --bmc1_property_lemmas                  false
% 2.31/0.92  --bmc1_k_induction                      false
% 2.31/0.92  --bmc1_non_equiv_states                 false
% 2.31/0.92  --bmc1_deadlock                         false
% 2.31/0.92  --bmc1_ucm                              false
% 2.31/0.92  --bmc1_add_unsat_core                   none
% 2.31/0.92  --bmc1_unsat_core_children              false
% 2.31/0.92  --bmc1_unsat_core_extrapolate_axioms    false
% 2.31/0.92  --bmc1_out_stat                         full
% 2.31/0.92  --bmc1_ground_init                      false
% 2.31/0.92  --bmc1_pre_inst_next_state              false
% 2.31/0.92  --bmc1_pre_inst_state                   false
% 2.31/0.92  --bmc1_pre_inst_reach_state             false
% 2.31/0.92  --bmc1_out_unsat_core                   false
% 2.31/0.92  --bmc1_aig_witness_out                  false
% 2.31/0.92  --bmc1_verbose                          false
% 2.31/0.92  --bmc1_dump_clauses_tptp                false
% 2.31/0.92  --bmc1_dump_unsat_core_tptp             false
% 2.31/0.92  --bmc1_dump_file                        -
% 2.31/0.92  --bmc1_ucm_expand_uc_limit              128
% 2.31/0.92  --bmc1_ucm_n_expand_iterations          6
% 2.31/0.92  --bmc1_ucm_extend_mode                  1
% 2.31/0.92  --bmc1_ucm_init_mode                    2
% 2.31/0.92  --bmc1_ucm_cone_mode                    none
% 2.31/0.92  --bmc1_ucm_reduced_relation_type        0
% 2.31/0.92  --bmc1_ucm_relax_model                  4
% 2.31/0.92  --bmc1_ucm_full_tr_after_sat            true
% 2.31/0.92  --bmc1_ucm_expand_neg_assumptions       false
% 2.31/0.92  --bmc1_ucm_layered_model                none
% 2.31/0.92  --bmc1_ucm_max_lemma_size               10
% 2.31/0.92  
% 2.31/0.92  ------ AIG Options
% 2.31/0.92  
% 2.31/0.92  --aig_mode                              false
% 2.31/0.92  
% 2.31/0.92  ------ Instantiation Options
% 2.31/0.92  
% 2.31/0.92  --instantiation_flag                    true
% 2.31/0.92  --inst_sos_flag                         false
% 2.31/0.92  --inst_sos_phase                        true
% 2.31/0.92  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 2.31/0.92  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 2.31/0.92  --inst_lit_sel_side                     none
% 2.31/0.92  --inst_solver_per_active                1400
% 2.31/0.92  --inst_solver_calls_frac                1.
% 2.31/0.92  --inst_passive_queue_type               priority_queues
% 2.31/0.92  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 2.31/0.92  --inst_passive_queues_freq              [25;2]
% 2.31/0.92  --inst_dismatching                      true
% 2.31/0.92  --inst_eager_unprocessed_to_passive     true
% 2.31/0.92  --inst_prop_sim_given                   true
% 2.31/0.92  --inst_prop_sim_new                     false
% 2.31/0.92  --inst_subs_new                         false
% 2.31/0.92  --inst_eq_res_simp                      false
% 2.31/0.92  --inst_subs_given                       false
% 2.31/0.92  --inst_orphan_elimination               true
% 2.31/0.92  --inst_learning_loop_flag               true
% 2.31/0.92  --inst_learning_start                   3000
% 2.31/0.92  --inst_learning_factor                  2
% 2.31/0.92  --inst_start_prop_sim_after_learn       3
% 2.31/0.92  --inst_sel_renew                        solver
% 2.31/0.92  --inst_lit_activity_flag                true
% 2.31/0.92  --inst_restr_to_given                   false
% 2.31/0.92  --inst_activity_threshold               500
% 2.31/0.92  --inst_out_proof                        true
% 2.31/0.92  
% 2.31/0.92  ------ Resolution Options
% 2.31/0.92  
% 2.31/0.92  --resolution_flag                       false
% 2.31/0.92  --res_lit_sel                           adaptive
% 2.31/0.92  --res_lit_sel_side                      none
% 2.31/0.92  --res_ordering                          kbo
% 2.31/0.92  --res_to_prop_solver                    active
% 2.31/0.92  --res_prop_simpl_new                    false
% 2.31/0.92  --res_prop_simpl_given                  true
% 2.31/0.92  --res_passive_queue_type                priority_queues
% 2.31/0.92  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 2.31/0.92  --res_passive_queues_freq               [15;5]
% 2.31/0.92  --res_forward_subs                      full
% 2.31/0.92  --res_backward_subs                     full
% 2.31/0.92  --res_forward_subs_resolution           true
% 2.31/0.92  --res_backward_subs_resolution          true
% 2.31/0.92  --res_orphan_elimination                true
% 2.31/0.92  --res_time_limit                        2.
% 2.31/0.92  --res_out_proof                         true
% 2.31/0.92  
% 2.31/0.92  ------ Superposition Options
% 2.31/0.92  
% 2.31/0.92  --superposition_flag                    true
% 2.31/0.92  --sup_passive_queue_type                priority_queues
% 2.31/0.92  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 2.31/0.92  --sup_passive_queues_freq               [8;1;4]
% 2.31/0.92  --demod_completeness_check              fast
% 2.31/0.92  --demod_use_ground                      true
% 2.31/0.92  --sup_to_prop_solver                    passive
% 2.31/0.92  --sup_prop_simpl_new                    true
% 2.31/0.92  --sup_prop_simpl_given                  true
% 2.31/0.92  --sup_fun_splitting                     false
% 2.31/0.92  --sup_smt_interval                      50000
% 2.31/0.92  
% 2.31/0.92  ------ Superposition Simplification Setup
% 2.31/0.92  
% 2.31/0.92  --sup_indices_passive                   []
% 2.31/0.92  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.31/0.92  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.31/0.92  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.31/0.92  --sup_full_triv                         [TrivRules;PropSubs]
% 2.31/0.92  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.31/0.92  --sup_full_bw                           [BwDemod]
% 2.31/0.92  --sup_immed_triv                        [TrivRules]
% 2.31/0.92  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 2.31/0.92  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.31/0.92  --sup_immed_bw_main                     []
% 2.31/0.92  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.31/0.92  --sup_input_triv                        [Unflattening;TrivRules]
% 2.31/0.92  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.31/0.92  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.31/0.92  
% 2.31/0.92  ------ Combination Options
% 2.31/0.92  
% 2.31/0.92  --comb_res_mult                         3
% 2.31/0.92  --comb_sup_mult                         2
% 2.31/0.92  --comb_inst_mult                        10
% 2.31/0.92  
% 2.31/0.92  ------ Debug Options
% 2.31/0.92  
% 2.31/0.92  --dbg_backtrace                         false
% 2.31/0.92  --dbg_dump_prop_clauses                 false
% 2.31/0.92  --dbg_dump_prop_clauses_file            -
% 2.31/0.92  --dbg_out_stat                          false
% 2.31/0.92  
% 2.31/0.92  
% 2.31/0.92  
% 2.31/0.92  
% 2.31/0.92  ------ Proving...
% 2.31/0.92  
% 2.31/0.92  
% 2.31/0.92  % SZS status Theorem for theBenchmark.p
% 2.31/0.92  
% 2.31/0.92  % SZS output start CNFRefutation for theBenchmark.p
% 2.31/0.92  
% 2.31/0.92  fof(f1,axiom,(
% 2.31/0.92    ! [X0,X1] : (! [X2] : (r2_hidden(X2,X0) <=> r2_hidden(X2,X1)) => X0 = X1)),
% 2.31/0.92    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.31/0.92  
% 2.31/0.92  fof(f17,plain,(
% 2.31/0.92    ! [X0,X1] : (X0 = X1 | ? [X2] : (r2_hidden(X2,X0) <~> r2_hidden(X2,X1)))),
% 2.31/0.92    inference(ennf_transformation,[],[f1])).
% 2.31/0.92  
% 2.31/0.92  fof(f32,plain,(
% 2.31/0.92    ! [X0,X1] : (X0 = X1 | ? [X2] : ((~r2_hidden(X2,X1) | ~r2_hidden(X2,X0)) & (r2_hidden(X2,X1) | r2_hidden(X2,X0))))),
% 2.31/0.92    inference(nnf_transformation,[],[f17])).
% 2.31/0.92  
% 2.31/0.92  fof(f33,plain,(
% 2.31/0.92    ! [X1,X0] : (? [X2] : ((~r2_hidden(X2,X1) | ~r2_hidden(X2,X0)) & (r2_hidden(X2,X1) | r2_hidden(X2,X0))) => ((~r2_hidden(sK0(X0,X1),X1) | ~r2_hidden(sK0(X0,X1),X0)) & (r2_hidden(sK0(X0,X1),X1) | r2_hidden(sK0(X0,X1),X0))))),
% 2.31/0.92    introduced(choice_axiom,[])).
% 2.31/0.92  
% 2.31/0.92  fof(f34,plain,(
% 2.31/0.92    ! [X0,X1] : (X0 = X1 | ((~r2_hidden(sK0(X0,X1),X1) | ~r2_hidden(sK0(X0,X1),X0)) & (r2_hidden(sK0(X0,X1),X1) | r2_hidden(sK0(X0,X1),X0))))),
% 2.31/0.92    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f32,f33])).
% 2.31/0.92  
% 2.31/0.92  fof(f46,plain,(
% 2.31/0.92    ( ! [X0,X1] : (X0 = X1 | r2_hidden(sK0(X0,X1),X1) | r2_hidden(sK0(X0,X1),X0)) )),
% 2.31/0.92    inference(cnf_transformation,[],[f34])).
% 2.31/0.92  
% 2.31/0.92  fof(f5,axiom,(
% 2.31/0.92    ! [X0,X1] : (r2_hidden(X0,X1) => m1_subset_1(X0,X1))),
% 2.31/0.92    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.31/0.92  
% 2.31/0.92  fof(f19,plain,(
% 2.31/0.92    ! [X0,X1] : (m1_subset_1(X0,X1) | ~r2_hidden(X0,X1))),
% 2.31/0.92    inference(ennf_transformation,[],[f5])).
% 2.31/0.92  
% 2.31/0.92  fof(f51,plain,(
% 2.31/0.92    ( ! [X0,X1] : (m1_subset_1(X0,X1) | ~r2_hidden(X0,X1)) )),
% 2.31/0.92    inference(cnf_transformation,[],[f19])).
% 2.31/0.92  
% 2.31/0.92  fof(f10,axiom,(
% 2.31/0.92    ! [X0] : (l1_orders_2(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => (v13_waybel_0(X1,X0) <=> ! [X2] : (m1_subset_1(X2,u1_struct_0(X0)) => ! [X3] : (m1_subset_1(X3,u1_struct_0(X0)) => ((r1_orders_2(X0,X2,X3) & r2_hidden(X2,X1)) => r2_hidden(X3,X1)))))))),
% 2.31/0.92    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.31/0.92  
% 2.31/0.92  fof(f27,plain,(
% 2.31/0.92    ! [X0] : (! [X1] : ((v13_waybel_0(X1,X0) <=> ! [X2] : (! [X3] : ((r2_hidden(X3,X1) | (~r1_orders_2(X0,X2,X3) | ~r2_hidden(X2,X1))) | ~m1_subset_1(X3,u1_struct_0(X0))) | ~m1_subset_1(X2,u1_struct_0(X0)))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_orders_2(X0))),
% 2.31/0.92    inference(ennf_transformation,[],[f10])).
% 2.31/0.92  
% 2.31/0.92  fof(f28,plain,(
% 2.31/0.92    ! [X0] : (! [X1] : ((v13_waybel_0(X1,X0) <=> ! [X2] : (! [X3] : (r2_hidden(X3,X1) | ~r1_orders_2(X0,X2,X3) | ~r2_hidden(X2,X1) | ~m1_subset_1(X3,u1_struct_0(X0))) | ~m1_subset_1(X2,u1_struct_0(X0)))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_orders_2(X0))),
% 2.31/0.92    inference(flattening,[],[f27])).
% 2.31/0.92  
% 2.31/0.92  fof(f35,plain,(
% 2.31/0.92    ! [X0] : (! [X1] : (((v13_waybel_0(X1,X0) | ? [X2] : (? [X3] : (~r2_hidden(X3,X1) & r1_orders_2(X0,X2,X3) & r2_hidden(X2,X1) & m1_subset_1(X3,u1_struct_0(X0))) & m1_subset_1(X2,u1_struct_0(X0)))) & (! [X2] : (! [X3] : (r2_hidden(X3,X1) | ~r1_orders_2(X0,X2,X3) | ~r2_hidden(X2,X1) | ~m1_subset_1(X3,u1_struct_0(X0))) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~v13_waybel_0(X1,X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_orders_2(X0))),
% 2.31/0.92    inference(nnf_transformation,[],[f28])).
% 2.31/0.92  
% 2.31/0.92  fof(f36,plain,(
% 2.31/0.92    ! [X0] : (! [X1] : (((v13_waybel_0(X1,X0) | ? [X2] : (? [X3] : (~r2_hidden(X3,X1) & r1_orders_2(X0,X2,X3) & r2_hidden(X2,X1) & m1_subset_1(X3,u1_struct_0(X0))) & m1_subset_1(X2,u1_struct_0(X0)))) & (! [X4] : (! [X5] : (r2_hidden(X5,X1) | ~r1_orders_2(X0,X4,X5) | ~r2_hidden(X4,X1) | ~m1_subset_1(X5,u1_struct_0(X0))) | ~m1_subset_1(X4,u1_struct_0(X0))) | ~v13_waybel_0(X1,X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_orders_2(X0))),
% 2.31/0.92    inference(rectify,[],[f35])).
% 2.31/0.92  
% 2.31/0.92  fof(f38,plain,(
% 2.31/0.92    ( ! [X2] : (! [X1,X0] : (? [X3] : (~r2_hidden(X3,X1) & r1_orders_2(X0,X2,X3) & r2_hidden(X2,X1) & m1_subset_1(X3,u1_struct_0(X0))) => (~r2_hidden(sK2(X0,X1),X1) & r1_orders_2(X0,X2,sK2(X0,X1)) & r2_hidden(X2,X1) & m1_subset_1(sK2(X0,X1),u1_struct_0(X0))))) )),
% 2.31/0.92    introduced(choice_axiom,[])).
% 2.31/0.92  
% 2.31/0.92  fof(f37,plain,(
% 2.31/0.92    ! [X1,X0] : (? [X2] : (? [X3] : (~r2_hidden(X3,X1) & r1_orders_2(X0,X2,X3) & r2_hidden(X2,X1) & m1_subset_1(X3,u1_struct_0(X0))) & m1_subset_1(X2,u1_struct_0(X0))) => (? [X3] : (~r2_hidden(X3,X1) & r1_orders_2(X0,sK1(X0,X1),X3) & r2_hidden(sK1(X0,X1),X1) & m1_subset_1(X3,u1_struct_0(X0))) & m1_subset_1(sK1(X0,X1),u1_struct_0(X0))))),
% 2.31/0.92    introduced(choice_axiom,[])).
% 2.31/0.92  
% 2.31/0.92  fof(f39,plain,(
% 2.31/0.92    ! [X0] : (! [X1] : (((v13_waybel_0(X1,X0) | ((~r2_hidden(sK2(X0,X1),X1) & r1_orders_2(X0,sK1(X0,X1),sK2(X0,X1)) & r2_hidden(sK1(X0,X1),X1) & m1_subset_1(sK2(X0,X1),u1_struct_0(X0))) & m1_subset_1(sK1(X0,X1),u1_struct_0(X0)))) & (! [X4] : (! [X5] : (r2_hidden(X5,X1) | ~r1_orders_2(X0,X4,X5) | ~r2_hidden(X4,X1) | ~m1_subset_1(X5,u1_struct_0(X0))) | ~m1_subset_1(X4,u1_struct_0(X0))) | ~v13_waybel_0(X1,X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_orders_2(X0))),
% 2.31/0.92    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1,sK2])],[f36,f38,f37])).
% 2.31/0.92  
% 2.31/0.92  fof(f58,plain,(
% 2.31/0.92    ( ! [X0,X1] : (v13_waybel_0(X1,X0) | m1_subset_1(sK2(X0,X1),u1_struct_0(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_orders_2(X0)) )),
% 2.31/0.92    inference(cnf_transformation,[],[f39])).
% 2.31/0.92  
% 2.31/0.92  fof(f12,conjecture,(
% 2.31/0.92    ! [X0] : ((l1_orders_2(X0) & v1_yellow_0(X0) & v5_orders_2(X0) & v4_orders_2(X0) & v3_orders_2(X0) & ~v2_struct_0(X0)) => ! [X1] : ((m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & v13_waybel_0(X1,X0) & v2_waybel_0(X1,X0) & ~v1_xboole_0(X1)) => (v1_subset_1(X1,u1_struct_0(X0)) <=> ~r2_hidden(k3_yellow_0(X0),X1))))),
% 2.31/0.92    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.31/0.92  
% 2.31/0.92  fof(f13,negated_conjecture,(
% 2.31/0.92    ~! [X0] : ((l1_orders_2(X0) & v1_yellow_0(X0) & v5_orders_2(X0) & v4_orders_2(X0) & v3_orders_2(X0) & ~v2_struct_0(X0)) => ! [X1] : ((m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & v13_waybel_0(X1,X0) & v2_waybel_0(X1,X0) & ~v1_xboole_0(X1)) => (v1_subset_1(X1,u1_struct_0(X0)) <=> ~r2_hidden(k3_yellow_0(X0),X1))))),
% 2.31/0.92    inference(negated_conjecture,[],[f12])).
% 2.31/0.92  
% 2.31/0.92  fof(f14,plain,(
% 2.31/0.92    ~! [X0] : ((l1_orders_2(X0) & v1_yellow_0(X0) & v5_orders_2(X0) & v4_orders_2(X0) & v3_orders_2(X0) & ~v2_struct_0(X0)) => ! [X1] : ((m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & v13_waybel_0(X1,X0) & ~v1_xboole_0(X1)) => (v1_subset_1(X1,u1_struct_0(X0)) <=> ~r2_hidden(k3_yellow_0(X0),X1))))),
% 2.31/0.92    inference(pure_predicate_removal,[],[f13])).
% 2.31/0.92  
% 2.31/0.92  fof(f15,plain,(
% 2.31/0.92    ~! [X0] : ((l1_orders_2(X0) & v1_yellow_0(X0) & v5_orders_2(X0) & v3_orders_2(X0) & ~v2_struct_0(X0)) => ! [X1] : ((m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & v13_waybel_0(X1,X0) & ~v1_xboole_0(X1)) => (v1_subset_1(X1,u1_struct_0(X0)) <=> ~r2_hidden(k3_yellow_0(X0),X1))))),
% 2.31/0.92    inference(pure_predicate_removal,[],[f14])).
% 2.31/0.92  
% 2.31/0.92  fof(f16,plain,(
% 2.31/0.92    ~! [X0] : ((l1_orders_2(X0) & v1_yellow_0(X0) & v5_orders_2(X0) & ~v2_struct_0(X0)) => ! [X1] : ((m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & v13_waybel_0(X1,X0) & ~v1_xboole_0(X1)) => (v1_subset_1(X1,u1_struct_0(X0)) <=> ~r2_hidden(k3_yellow_0(X0),X1))))),
% 2.31/0.92    inference(pure_predicate_removal,[],[f15])).
% 2.31/0.92  
% 2.31/0.92  fof(f30,plain,(
% 2.31/0.92    ? [X0] : (? [X1] : ((v1_subset_1(X1,u1_struct_0(X0)) <~> ~r2_hidden(k3_yellow_0(X0),X1)) & (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & v13_waybel_0(X1,X0) & ~v1_xboole_0(X1))) & (l1_orders_2(X0) & v1_yellow_0(X0) & v5_orders_2(X0) & ~v2_struct_0(X0)))),
% 2.31/0.92    inference(ennf_transformation,[],[f16])).
% 2.31/0.92  
% 2.31/0.92  fof(f31,plain,(
% 2.31/0.92    ? [X0] : (? [X1] : ((v1_subset_1(X1,u1_struct_0(X0)) <~> ~r2_hidden(k3_yellow_0(X0),X1)) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & v13_waybel_0(X1,X0) & ~v1_xboole_0(X1)) & l1_orders_2(X0) & v1_yellow_0(X0) & v5_orders_2(X0) & ~v2_struct_0(X0))),
% 2.31/0.92    inference(flattening,[],[f30])).
% 2.31/0.92  
% 2.31/0.92  fof(f41,plain,(
% 2.31/0.92    ? [X0] : (? [X1] : (((r2_hidden(k3_yellow_0(X0),X1) | ~v1_subset_1(X1,u1_struct_0(X0))) & (~r2_hidden(k3_yellow_0(X0),X1) | v1_subset_1(X1,u1_struct_0(X0)))) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & v13_waybel_0(X1,X0) & ~v1_xboole_0(X1)) & l1_orders_2(X0) & v1_yellow_0(X0) & v5_orders_2(X0) & ~v2_struct_0(X0))),
% 2.31/0.92    inference(nnf_transformation,[],[f31])).
% 2.31/0.92  
% 2.31/0.92  fof(f42,plain,(
% 2.31/0.92    ? [X0] : (? [X1] : ((r2_hidden(k3_yellow_0(X0),X1) | ~v1_subset_1(X1,u1_struct_0(X0))) & (~r2_hidden(k3_yellow_0(X0),X1) | v1_subset_1(X1,u1_struct_0(X0))) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & v13_waybel_0(X1,X0) & ~v1_xboole_0(X1)) & l1_orders_2(X0) & v1_yellow_0(X0) & v5_orders_2(X0) & ~v2_struct_0(X0))),
% 2.31/0.92    inference(flattening,[],[f41])).
% 2.31/0.92  
% 2.31/0.92  fof(f44,plain,(
% 2.31/0.92    ( ! [X0] : (? [X1] : ((r2_hidden(k3_yellow_0(X0),X1) | ~v1_subset_1(X1,u1_struct_0(X0))) & (~r2_hidden(k3_yellow_0(X0),X1) | v1_subset_1(X1,u1_struct_0(X0))) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & v13_waybel_0(X1,X0) & ~v1_xboole_0(X1)) => ((r2_hidden(k3_yellow_0(X0),sK4) | ~v1_subset_1(sK4,u1_struct_0(X0))) & (~r2_hidden(k3_yellow_0(X0),sK4) | v1_subset_1(sK4,u1_struct_0(X0))) & m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(X0))) & v13_waybel_0(sK4,X0) & ~v1_xboole_0(sK4))) )),
% 2.31/0.92    introduced(choice_axiom,[])).
% 2.31/0.92  
% 2.31/0.92  fof(f43,plain,(
% 2.31/0.92    ? [X0] : (? [X1] : ((r2_hidden(k3_yellow_0(X0),X1) | ~v1_subset_1(X1,u1_struct_0(X0))) & (~r2_hidden(k3_yellow_0(X0),X1) | v1_subset_1(X1,u1_struct_0(X0))) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & v13_waybel_0(X1,X0) & ~v1_xboole_0(X1)) & l1_orders_2(X0) & v1_yellow_0(X0) & v5_orders_2(X0) & ~v2_struct_0(X0)) => (? [X1] : ((r2_hidden(k3_yellow_0(sK3),X1) | ~v1_subset_1(X1,u1_struct_0(sK3))) & (~r2_hidden(k3_yellow_0(sK3),X1) | v1_subset_1(X1,u1_struct_0(sK3))) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK3))) & v13_waybel_0(X1,sK3) & ~v1_xboole_0(X1)) & l1_orders_2(sK3) & v1_yellow_0(sK3) & v5_orders_2(sK3) & ~v2_struct_0(sK3))),
% 2.31/0.92    introduced(choice_axiom,[])).
% 2.31/0.92  
% 2.31/0.92  fof(f45,plain,(
% 2.31/0.92    ((r2_hidden(k3_yellow_0(sK3),sK4) | ~v1_subset_1(sK4,u1_struct_0(sK3))) & (~r2_hidden(k3_yellow_0(sK3),sK4) | v1_subset_1(sK4,u1_struct_0(sK3))) & m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(sK3))) & v13_waybel_0(sK4,sK3) & ~v1_xboole_0(sK4)) & l1_orders_2(sK3) & v1_yellow_0(sK3) & v5_orders_2(sK3) & ~v2_struct_0(sK3)),
% 2.31/0.92    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3,sK4])],[f42,f44,f43])).
% 2.31/0.92  
% 2.31/0.92  fof(f67,plain,(
% 2.31/0.92    l1_orders_2(sK3)),
% 2.31/0.92    inference(cnf_transformation,[],[f45])).
% 2.31/0.92  
% 2.31/0.92  fof(f11,axiom,(
% 2.31/0.92    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => (v1_subset_1(X1,X0) <=> X0 != X1))),
% 2.31/0.92    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.31/0.92  
% 2.31/0.92  fof(f29,plain,(
% 2.31/0.92    ! [X0,X1] : ((v1_subset_1(X1,X0) <=> X0 != X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 2.31/0.92    inference(ennf_transformation,[],[f11])).
% 2.31/0.92  
% 2.31/0.92  fof(f40,plain,(
% 2.31/0.92    ! [X0,X1] : (((v1_subset_1(X1,X0) | X0 = X1) & (X0 != X1 | ~v1_subset_1(X1,X0))) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 2.31/0.92    inference(nnf_transformation,[],[f29])).
% 2.31/0.92  
% 2.31/0.92  fof(f63,plain,(
% 2.31/0.92    ( ! [X0,X1] : (v1_subset_1(X1,X0) | X0 = X1 | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 2.31/0.92    inference(cnf_transformation,[],[f40])).
% 2.31/0.92  
% 2.31/0.92  fof(f72,plain,(
% 2.31/0.92    r2_hidden(k3_yellow_0(sK3),sK4) | ~v1_subset_1(sK4,u1_struct_0(sK3))),
% 2.31/0.92    inference(cnf_transformation,[],[f45])).
% 2.31/0.92  
% 2.31/0.92  fof(f70,plain,(
% 2.31/0.92    m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(sK3)))),
% 2.31/0.92    inference(cnf_transformation,[],[f45])).
% 2.31/0.92  
% 2.31/0.92  fof(f56,plain,(
% 2.31/0.92    ( ! [X4,X0,X5,X1] : (r2_hidden(X5,X1) | ~r1_orders_2(X0,X4,X5) | ~r2_hidden(X4,X1) | ~m1_subset_1(X5,u1_struct_0(X0)) | ~m1_subset_1(X4,u1_struct_0(X0)) | ~v13_waybel_0(X1,X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_orders_2(X0)) )),
% 2.31/0.92    inference(cnf_transformation,[],[f39])).
% 2.31/0.92  
% 2.31/0.92  fof(f9,axiom,(
% 2.31/0.92    ! [X0] : ((l1_orders_2(X0) & v1_yellow_0(X0) & v5_orders_2(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,u1_struct_0(X0)) => r1_orders_2(X0,k3_yellow_0(X0),X1)))),
% 2.31/0.93    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.31/0.93  
% 2.31/0.93  fof(f25,plain,(
% 2.31/0.93    ! [X0] : (! [X1] : (r1_orders_2(X0,k3_yellow_0(X0),X1) | ~m1_subset_1(X1,u1_struct_0(X0))) | (~l1_orders_2(X0) | ~v1_yellow_0(X0) | ~v5_orders_2(X0) | v2_struct_0(X0)))),
% 2.31/0.93    inference(ennf_transformation,[],[f9])).
% 2.31/0.93  
% 2.31/0.93  fof(f26,plain,(
% 2.31/0.93    ! [X0] : (! [X1] : (r1_orders_2(X0,k3_yellow_0(X0),X1) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~l1_orders_2(X0) | ~v1_yellow_0(X0) | ~v5_orders_2(X0) | v2_struct_0(X0))),
% 2.31/0.93    inference(flattening,[],[f25])).
% 2.31/0.93  
% 2.31/0.93  fof(f55,plain,(
% 2.31/0.93    ( ! [X0,X1] : (r1_orders_2(X0,k3_yellow_0(X0),X1) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_orders_2(X0) | ~v1_yellow_0(X0) | ~v5_orders_2(X0) | v2_struct_0(X0)) )),
% 2.31/0.93    inference(cnf_transformation,[],[f26])).
% 2.31/0.93  
% 2.31/0.93  fof(f66,plain,(
% 2.31/0.93    v1_yellow_0(sK3)),
% 2.31/0.93    inference(cnf_transformation,[],[f45])).
% 2.31/0.93  
% 2.31/0.93  fof(f64,plain,(
% 2.31/0.93    ~v2_struct_0(sK3)),
% 2.31/0.93    inference(cnf_transformation,[],[f45])).
% 2.31/0.93  
% 2.31/0.93  fof(f65,plain,(
% 2.31/0.93    v5_orders_2(sK3)),
% 2.31/0.93    inference(cnf_transformation,[],[f45])).
% 2.31/0.93  
% 2.31/0.93  fof(f8,axiom,(
% 2.31/0.93    ! [X0] : (l1_orders_2(X0) => m1_subset_1(k3_yellow_0(X0),u1_struct_0(X0)))),
% 2.31/0.93    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.31/0.93  
% 2.31/0.93  fof(f24,plain,(
% 2.31/0.93    ! [X0] : (m1_subset_1(k3_yellow_0(X0),u1_struct_0(X0)) | ~l1_orders_2(X0))),
% 2.31/0.93    inference(ennf_transformation,[],[f8])).
% 2.31/0.93  
% 2.31/0.93  fof(f54,plain,(
% 2.31/0.93    ( ! [X0] : (m1_subset_1(k3_yellow_0(X0),u1_struct_0(X0)) | ~l1_orders_2(X0)) )),
% 2.31/0.93    inference(cnf_transformation,[],[f24])).
% 2.31/0.93  
% 2.31/0.93  fof(f69,plain,(
% 2.31/0.93    v13_waybel_0(sK4,sK3)),
% 2.31/0.93    inference(cnf_transformation,[],[f45])).
% 2.31/0.93  
% 2.31/0.93  fof(f6,axiom,(
% 2.31/0.93    ! [X0,X1] : (m1_subset_1(X0,X1) => (r2_hidden(X0,X1) | v1_xboole_0(X1)))),
% 2.31/0.93    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.31/0.93  
% 2.31/0.93  fof(f20,plain,(
% 2.31/0.93    ! [X0,X1] : ((r2_hidden(X0,X1) | v1_xboole_0(X1)) | ~m1_subset_1(X0,X1))),
% 2.31/0.93    inference(ennf_transformation,[],[f6])).
% 2.31/0.93  
% 2.31/0.93  fof(f21,plain,(
% 2.31/0.93    ! [X0,X1] : (r2_hidden(X0,X1) | v1_xboole_0(X1) | ~m1_subset_1(X0,X1))),
% 2.31/0.93    inference(flattening,[],[f20])).
% 2.31/0.93  
% 2.31/0.93  fof(f52,plain,(
% 2.31/0.93    ( ! [X0,X1] : (r2_hidden(X0,X1) | v1_xboole_0(X1) | ~m1_subset_1(X0,X1)) )),
% 2.31/0.93    inference(cnf_transformation,[],[f21])).
% 2.31/0.93  
% 2.31/0.93  fof(f68,plain,(
% 2.31/0.93    ~v1_xboole_0(sK4)),
% 2.31/0.93    inference(cnf_transformation,[],[f45])).
% 2.31/0.93  
% 2.31/0.93  fof(f47,plain,(
% 2.31/0.93    ( ! [X0,X1] : (X0 = X1 | ~r2_hidden(sK0(X0,X1),X1) | ~r2_hidden(sK0(X0,X1),X0)) )),
% 2.31/0.93    inference(cnf_transformation,[],[f34])).
% 2.31/0.93  
% 2.31/0.93  fof(f4,axiom,(
% 2.31/0.93    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => ! [X2] : (r2_hidden(X2,X1) => r2_hidden(X2,X0)))),
% 2.31/0.93    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.31/0.93  
% 2.31/0.93  fof(f18,plain,(
% 2.31/0.93    ! [X0,X1] : (! [X2] : (r2_hidden(X2,X0) | ~r2_hidden(X2,X1)) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 2.31/0.93    inference(ennf_transformation,[],[f4])).
% 2.31/0.93  
% 2.31/0.93  fof(f50,plain,(
% 2.31/0.93    ( ! [X2,X0,X1] : (r2_hidden(X2,X0) | ~r2_hidden(X2,X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 2.31/0.93    inference(cnf_transformation,[],[f18])).
% 2.31/0.93  
% 2.31/0.93  fof(f3,axiom,(
% 2.31/0.93    ! [X0] : m1_subset_1(k2_subset_1(X0),k1_zfmisc_1(X0))),
% 2.31/0.93    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.31/0.93  
% 2.31/0.93  fof(f49,plain,(
% 2.31/0.93    ( ! [X0] : (m1_subset_1(k2_subset_1(X0),k1_zfmisc_1(X0))) )),
% 2.31/0.93    inference(cnf_transformation,[],[f3])).
% 2.31/0.93  
% 2.31/0.93  fof(f2,axiom,(
% 2.31/0.93    ! [X0] : k2_subset_1(X0) = X0),
% 2.31/0.93    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.31/0.93  
% 2.31/0.93  fof(f48,plain,(
% 2.31/0.93    ( ! [X0] : (k2_subset_1(X0) = X0) )),
% 2.31/0.93    inference(cnf_transformation,[],[f2])).
% 2.31/0.93  
% 2.31/0.93  fof(f62,plain,(
% 2.31/0.93    ( ! [X0,X1] : (X0 != X1 | ~v1_subset_1(X1,X0) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 2.31/0.93    inference(cnf_transformation,[],[f40])).
% 2.31/0.93  
% 2.31/0.93  fof(f73,plain,(
% 2.31/0.93    ( ! [X1] : (~v1_subset_1(X1,X1) | ~m1_subset_1(X1,k1_zfmisc_1(X1))) )),
% 2.31/0.93    inference(equality_resolution,[],[f62])).
% 2.31/0.93  
% 2.31/0.93  fof(f71,plain,(
% 2.31/0.93    ~r2_hidden(k3_yellow_0(sK3),sK4) | v1_subset_1(sK4,u1_struct_0(sK3))),
% 2.31/0.93    inference(cnf_transformation,[],[f45])).
% 2.31/0.93  
% 2.31/0.93  cnf(c_1,plain,
% 2.31/0.93      ( r2_hidden(sK0(X0,X1),X1) | r2_hidden(sK0(X0,X1),X0) | X1 = X0 ),
% 2.31/0.93      inference(cnf_transformation,[],[f46]) ).
% 2.31/0.93  
% 2.31/0.93  cnf(c_1062,plain,
% 2.31/0.93      ( X0 = X1
% 2.31/0.93      | r2_hidden(sK0(X1,X0),X0) = iProver_top
% 2.31/0.93      | r2_hidden(sK0(X1,X0),X1) = iProver_top ),
% 2.31/0.93      inference(predicate_to_equality,[status(thm)],[c_1]) ).
% 2.31/0.93  
% 2.31/0.93  cnf(c_5,plain,
% 2.31/0.93      ( m1_subset_1(X0,X1) | ~ r2_hidden(X0,X1) ),
% 2.31/0.93      inference(cnf_transformation,[],[f51]) ).
% 2.31/0.93  
% 2.31/0.93  cnf(c_1059,plain,
% 2.31/0.93      ( m1_subset_1(X0,X1) = iProver_top
% 2.31/0.93      | r2_hidden(X0,X1) != iProver_top ),
% 2.31/0.93      inference(predicate_to_equality,[status(thm)],[c_5]) ).
% 2.31/0.93  
% 2.31/0.93  cnf(c_1555,plain,
% 2.31/0.93      ( X0 = X1
% 2.31/0.93      | m1_subset_1(sK0(X0,X1),X0) = iProver_top
% 2.31/0.93      | r2_hidden(sK0(X0,X1),X1) = iProver_top ),
% 2.31/0.93      inference(superposition,[status(thm)],[c_1062,c_1059]) ).
% 2.31/0.93  
% 2.31/0.93  cnf(c_13,plain,
% 2.31/0.93      ( v13_waybel_0(X0,X1)
% 2.31/0.93      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 2.31/0.93      | m1_subset_1(sK2(X1,X0),u1_struct_0(X1))
% 2.31/0.93      | ~ l1_orders_2(X1) ),
% 2.31/0.93      inference(cnf_transformation,[],[f58]) ).
% 2.31/0.93  
% 2.31/0.93  cnf(c_23,negated_conjecture,
% 2.31/0.93      ( l1_orders_2(sK3) ),
% 2.31/0.93      inference(cnf_transformation,[],[f67]) ).
% 2.31/0.93  
% 2.31/0.93  cnf(c_536,plain,
% 2.31/0.93      ( v13_waybel_0(X0,X1)
% 2.31/0.93      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 2.31/0.93      | m1_subset_1(sK2(X1,X0),u1_struct_0(X1))
% 2.31/0.93      | sK3 != X1 ),
% 2.31/0.93      inference(resolution_lifted,[status(thm)],[c_13,c_23]) ).
% 2.31/0.93  
% 2.31/0.93  cnf(c_537,plain,
% 2.31/0.93      ( v13_waybel_0(X0,sK3)
% 2.31/0.93      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK3)))
% 2.31/0.93      | m1_subset_1(sK2(sK3,X0),u1_struct_0(sK3)) ),
% 2.31/0.93      inference(unflattening,[status(thm)],[c_536]) ).
% 2.31/0.93  
% 2.31/0.93  cnf(c_1048,plain,
% 2.31/0.93      ( v13_waybel_0(X0,sK3) = iProver_top
% 2.31/0.93      | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK3))) != iProver_top
% 2.31/0.93      | m1_subset_1(sK2(sK3,X0),u1_struct_0(sK3)) = iProver_top ),
% 2.31/0.93      inference(predicate_to_equality,[status(thm)],[c_537]) ).
% 2.31/0.93  
% 2.31/0.93  cnf(c_16,plain,
% 2.31/0.93      ( v1_subset_1(X0,X1)
% 2.31/0.93      | ~ m1_subset_1(X0,k1_zfmisc_1(X1))
% 2.31/0.93      | X0 = X1 ),
% 2.31/0.93      inference(cnf_transformation,[],[f63]) ).
% 2.31/0.93  
% 2.31/0.93  cnf(c_18,negated_conjecture,
% 2.31/0.93      ( ~ v1_subset_1(sK4,u1_struct_0(sK3))
% 2.31/0.93      | r2_hidden(k3_yellow_0(sK3),sK4) ),
% 2.31/0.93      inference(cnf_transformation,[],[f72]) ).
% 2.31/0.93  
% 2.31/0.93  cnf(c_195,plain,
% 2.31/0.93      ( ~ v1_subset_1(sK4,u1_struct_0(sK3))
% 2.31/0.93      | r2_hidden(k3_yellow_0(sK3),sK4) ),
% 2.31/0.93      inference(prop_impl,[status(thm)],[c_18]) ).
% 2.31/0.93  
% 2.31/0.93  cnf(c_387,plain,
% 2.31/0.93      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
% 2.31/0.93      | r2_hidden(k3_yellow_0(sK3),sK4)
% 2.31/0.93      | X1 = X0
% 2.31/0.93      | u1_struct_0(sK3) != X1
% 2.31/0.93      | sK4 != X0 ),
% 2.31/0.93      inference(resolution_lifted,[status(thm)],[c_16,c_195]) ).
% 2.31/0.93  
% 2.31/0.93  cnf(c_388,plain,
% 2.31/0.93      ( ~ m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(sK3)))
% 2.31/0.93      | r2_hidden(k3_yellow_0(sK3),sK4)
% 2.31/0.93      | u1_struct_0(sK3) = sK4 ),
% 2.31/0.93      inference(unflattening,[status(thm)],[c_387]) ).
% 2.31/0.93  
% 2.31/0.93  cnf(c_20,negated_conjecture,
% 2.31/0.93      ( m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(sK3))) ),
% 2.31/0.93      inference(cnf_transformation,[],[f70]) ).
% 2.31/0.93  
% 2.31/0.93  cnf(c_390,plain,
% 2.31/0.93      ( r2_hidden(k3_yellow_0(sK3),sK4) | u1_struct_0(sK3) = sK4 ),
% 2.31/0.93      inference(global_propositional_subsumption,
% 2.31/0.93                [status(thm)],
% 2.31/0.93                [c_388,c_20]) ).
% 2.31/0.93  
% 2.31/0.93  cnf(c_1054,plain,
% 2.31/0.93      ( u1_struct_0(sK3) = sK4
% 2.31/0.93      | r2_hidden(k3_yellow_0(sK3),sK4) = iProver_top ),
% 2.31/0.93      inference(predicate_to_equality,[status(thm)],[c_390]) ).
% 2.31/0.93  
% 2.31/0.93  cnf(c_1057,plain,
% 2.31/0.93      ( m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(sK3))) = iProver_top ),
% 2.31/0.93      inference(predicate_to_equality,[status(thm)],[c_20]) ).
% 2.31/0.93  
% 2.31/0.93  cnf(c_15,plain,
% 2.31/0.93      ( ~ r1_orders_2(X0,X1,X2)
% 2.31/0.93      | ~ v13_waybel_0(X3,X0)
% 2.31/0.93      | ~ m1_subset_1(X2,u1_struct_0(X0))
% 2.31/0.93      | ~ m1_subset_1(X1,u1_struct_0(X0))
% 2.31/0.93      | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))
% 2.31/0.93      | ~ r2_hidden(X1,X3)
% 2.31/0.93      | r2_hidden(X2,X3)
% 2.31/0.93      | ~ l1_orders_2(X0) ),
% 2.31/0.93      inference(cnf_transformation,[],[f56]) ).
% 2.31/0.93  
% 2.31/0.93  cnf(c_9,plain,
% 2.31/0.93      ( r1_orders_2(X0,k3_yellow_0(X0),X1)
% 2.31/0.93      | ~ m1_subset_1(X1,u1_struct_0(X0))
% 2.31/0.93      | v2_struct_0(X0)
% 2.31/0.93      | ~ v5_orders_2(X0)
% 2.31/0.93      | ~ v1_yellow_0(X0)
% 2.31/0.93      | ~ l1_orders_2(X0) ),
% 2.31/0.93      inference(cnf_transformation,[],[f55]) ).
% 2.31/0.93  
% 2.31/0.93  cnf(c_24,negated_conjecture,
% 2.31/0.93      ( v1_yellow_0(sK3) ),
% 2.31/0.93      inference(cnf_transformation,[],[f66]) ).
% 2.31/0.93  
% 2.31/0.93  cnf(c_363,plain,
% 2.31/0.93      ( r1_orders_2(X0,k3_yellow_0(X0),X1)
% 2.31/0.93      | ~ m1_subset_1(X1,u1_struct_0(X0))
% 2.31/0.93      | v2_struct_0(X0)
% 2.31/0.93      | ~ v5_orders_2(X0)
% 2.31/0.93      | ~ l1_orders_2(X0)
% 2.31/0.93      | sK3 != X0 ),
% 2.31/0.93      inference(resolution_lifted,[status(thm)],[c_9,c_24]) ).
% 2.31/0.93  
% 2.31/0.93  cnf(c_364,plain,
% 2.31/0.93      ( r1_orders_2(sK3,k3_yellow_0(sK3),X0)
% 2.31/0.93      | ~ m1_subset_1(X0,u1_struct_0(sK3))
% 2.31/0.93      | v2_struct_0(sK3)
% 2.31/0.93      | ~ v5_orders_2(sK3)
% 2.31/0.93      | ~ l1_orders_2(sK3) ),
% 2.31/0.93      inference(unflattening,[status(thm)],[c_363]) ).
% 2.31/0.93  
% 2.31/0.93  cnf(c_26,negated_conjecture,
% 2.31/0.93      ( ~ v2_struct_0(sK3) ),
% 2.31/0.93      inference(cnf_transformation,[],[f64]) ).
% 2.31/0.93  
% 2.31/0.93  cnf(c_25,negated_conjecture,
% 2.31/0.93      ( v5_orders_2(sK3) ),
% 2.31/0.93      inference(cnf_transformation,[],[f65]) ).
% 2.31/0.93  
% 2.31/0.93  cnf(c_368,plain,
% 2.31/0.93      ( ~ m1_subset_1(X0,u1_struct_0(sK3))
% 2.31/0.93      | r1_orders_2(sK3,k3_yellow_0(sK3),X0) ),
% 2.31/0.93      inference(global_propositional_subsumption,
% 2.31/0.93                [status(thm)],
% 2.31/0.93                [c_364,c_26,c_25,c_23]) ).
% 2.31/0.93  
% 2.31/0.93  cnf(c_369,plain,
% 2.31/0.93      ( r1_orders_2(sK3,k3_yellow_0(sK3),X0)
% 2.31/0.93      | ~ m1_subset_1(X0,u1_struct_0(sK3)) ),
% 2.31/0.93      inference(renaming,[status(thm)],[c_368]) ).
% 2.31/0.93  
% 2.31/0.93  cnf(c_451,plain,
% 2.31/0.93      ( ~ v13_waybel_0(X0,X1)
% 2.31/0.93      | ~ m1_subset_1(X2,u1_struct_0(X1))
% 2.31/0.93      | ~ m1_subset_1(X3,u1_struct_0(X1))
% 2.31/0.93      | ~ m1_subset_1(X4,u1_struct_0(sK3))
% 2.31/0.93      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 2.31/0.93      | ~ r2_hidden(X2,X0)
% 2.31/0.93      | r2_hidden(X3,X0)
% 2.31/0.93      | ~ l1_orders_2(X1)
% 2.31/0.93      | X4 != X3
% 2.31/0.93      | k3_yellow_0(sK3) != X2
% 2.31/0.93      | sK3 != X1 ),
% 2.31/0.93      inference(resolution_lifted,[status(thm)],[c_15,c_369]) ).
% 2.31/0.93  
% 2.31/0.93  cnf(c_452,plain,
% 2.31/0.93      ( ~ v13_waybel_0(X0,sK3)
% 2.31/0.93      | ~ m1_subset_1(X1,u1_struct_0(sK3))
% 2.31/0.93      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK3)))
% 2.31/0.93      | ~ m1_subset_1(k3_yellow_0(sK3),u1_struct_0(sK3))
% 2.31/0.93      | r2_hidden(X1,X0)
% 2.31/0.93      | ~ r2_hidden(k3_yellow_0(sK3),X0)
% 2.31/0.93      | ~ l1_orders_2(sK3) ),
% 2.31/0.93      inference(unflattening,[status(thm)],[c_451]) ).
% 2.31/0.93  
% 2.31/0.93  cnf(c_8,plain,
% 2.31/0.93      ( m1_subset_1(k3_yellow_0(X0),u1_struct_0(X0))
% 2.31/0.93      | ~ l1_orders_2(X0) ),
% 2.31/0.93      inference(cnf_transformation,[],[f54]) ).
% 2.31/0.93  
% 2.31/0.93  cnf(c_62,plain,
% 2.31/0.93      ( m1_subset_1(k3_yellow_0(sK3),u1_struct_0(sK3))
% 2.31/0.93      | ~ l1_orders_2(sK3) ),
% 2.31/0.93      inference(instantiation,[status(thm)],[c_8]) ).
% 2.31/0.93  
% 2.31/0.93  cnf(c_456,plain,
% 2.31/0.93      ( ~ r2_hidden(k3_yellow_0(sK3),X0)
% 2.31/0.93      | r2_hidden(X1,X0)
% 2.31/0.93      | ~ v13_waybel_0(X0,sK3)
% 2.31/0.93      | ~ m1_subset_1(X1,u1_struct_0(sK3))
% 2.31/0.93      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK3))) ),
% 2.31/0.93      inference(global_propositional_subsumption,
% 2.31/0.93                [status(thm)],
% 2.31/0.93                [c_452,c_23,c_62]) ).
% 2.31/0.93  
% 2.31/0.93  cnf(c_457,plain,
% 2.31/0.93      ( ~ v13_waybel_0(X0,sK3)
% 2.31/0.93      | ~ m1_subset_1(X1,u1_struct_0(sK3))
% 2.31/0.93      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK3)))
% 2.31/0.93      | r2_hidden(X1,X0)
% 2.31/0.93      | ~ r2_hidden(k3_yellow_0(sK3),X0) ),
% 2.31/0.93      inference(renaming,[status(thm)],[c_456]) ).
% 2.31/0.93  
% 2.31/0.93  cnf(c_1052,plain,
% 2.31/0.93      ( v13_waybel_0(X0,sK3) != iProver_top
% 2.31/0.93      | m1_subset_1(X1,u1_struct_0(sK3)) != iProver_top
% 2.31/0.93      | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK3))) != iProver_top
% 2.31/0.93      | r2_hidden(X1,X0) = iProver_top
% 2.31/0.93      | r2_hidden(k3_yellow_0(sK3),X0) != iProver_top ),
% 2.31/0.93      inference(predicate_to_equality,[status(thm)],[c_457]) ).
% 2.31/0.93  
% 2.31/0.93  cnf(c_1685,plain,
% 2.31/0.93      ( v13_waybel_0(sK4,sK3) != iProver_top
% 2.31/0.93      | m1_subset_1(X0,u1_struct_0(sK3)) != iProver_top
% 2.31/0.93      | r2_hidden(X0,sK4) = iProver_top
% 2.31/0.93      | r2_hidden(k3_yellow_0(sK3),sK4) != iProver_top ),
% 2.31/0.93      inference(superposition,[status(thm)],[c_1057,c_1052]) ).
% 2.31/0.93  
% 2.31/0.93  cnf(c_21,negated_conjecture,
% 2.31/0.93      ( v13_waybel_0(sK4,sK3) ),
% 2.31/0.93      inference(cnf_transformation,[],[f69]) ).
% 2.31/0.93  
% 2.31/0.93  cnf(c_32,plain,
% 2.31/0.93      ( v13_waybel_0(sK4,sK3) = iProver_top ),
% 2.31/0.93      inference(predicate_to_equality,[status(thm)],[c_21]) ).
% 2.31/0.93  
% 2.31/0.93  cnf(c_1833,plain,
% 2.31/0.93      ( m1_subset_1(X0,u1_struct_0(sK3)) != iProver_top
% 2.31/0.93      | r2_hidden(X0,sK4) = iProver_top
% 2.31/0.93      | r2_hidden(k3_yellow_0(sK3),sK4) != iProver_top ),
% 2.31/0.93      inference(global_propositional_subsumption,
% 2.31/0.93                [status(thm)],
% 2.31/0.93                [c_1685,c_32]) ).
% 2.31/0.93  
% 2.31/0.93  cnf(c_1924,plain,
% 2.31/0.93      ( u1_struct_0(sK3) = sK4
% 2.31/0.93      | m1_subset_1(X0,u1_struct_0(sK3)) != iProver_top
% 2.31/0.93      | r2_hidden(X0,sK4) = iProver_top ),
% 2.31/0.93      inference(superposition,[status(thm)],[c_1054,c_1833]) ).
% 2.31/0.93  
% 2.31/0.93  cnf(c_2514,plain,
% 2.31/0.93      ( u1_struct_0(sK3) = sK4
% 2.31/0.93      | v13_waybel_0(X0,sK3) = iProver_top
% 2.31/0.93      | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK3))) != iProver_top
% 2.31/0.93      | r2_hidden(sK2(sK3,X0),sK4) = iProver_top ),
% 2.31/0.93      inference(superposition,[status(thm)],[c_1048,c_1924]) ).
% 2.31/0.93  
% 2.31/0.93  cnf(c_3017,plain,
% 2.31/0.93      ( u1_struct_0(sK3) = sK4
% 2.31/0.93      | k1_zfmisc_1(u1_struct_0(sK3)) = X0
% 2.31/0.93      | v13_waybel_0(sK0(k1_zfmisc_1(u1_struct_0(sK3)),X0),sK3) = iProver_top
% 2.31/0.93      | r2_hidden(sK2(sK3,sK0(k1_zfmisc_1(u1_struct_0(sK3)),X0)),sK4) = iProver_top
% 2.31/0.93      | r2_hidden(sK0(k1_zfmisc_1(u1_struct_0(sK3)),X0),X0) = iProver_top ),
% 2.31/0.93      inference(superposition,[status(thm)],[c_1555,c_2514]) ).
% 2.31/0.93  
% 2.31/0.93  cnf(c_3011,plain,
% 2.31/0.93      ( X0 = X1
% 2.31/0.93      | m1_subset_1(sK0(X1,X0),X1) = iProver_top
% 2.31/0.93      | m1_subset_1(sK0(X1,X0),X0) = iProver_top ),
% 2.31/0.93      inference(superposition,[status(thm)],[c_1555,c_1059]) ).
% 2.31/0.93  
% 2.31/0.93  cnf(c_6,plain,
% 2.31/0.93      ( ~ m1_subset_1(X0,X1) | r2_hidden(X0,X1) | v1_xboole_0(X1) ),
% 2.31/0.93      inference(cnf_transformation,[],[f52]) ).
% 2.31/0.93  
% 2.31/0.93  cnf(c_22,negated_conjecture,
% 2.31/0.93      ( ~ v1_xboole_0(sK4) ),
% 2.31/0.93      inference(cnf_transformation,[],[f68]) ).
% 2.31/0.93  
% 2.31/0.93  cnf(c_348,plain,
% 2.31/0.93      ( ~ m1_subset_1(X0,X1) | r2_hidden(X0,X1) | sK4 != X1 ),
% 2.31/0.93      inference(resolution_lifted,[status(thm)],[c_6,c_22]) ).
% 2.31/0.93  
% 2.31/0.93  cnf(c_349,plain,
% 2.31/0.93      ( ~ m1_subset_1(X0,sK4) | r2_hidden(X0,sK4) ),
% 2.31/0.93      inference(unflattening,[status(thm)],[c_348]) ).
% 2.31/0.93  
% 2.31/0.93  cnf(c_1055,plain,
% 2.31/0.93      ( m1_subset_1(X0,sK4) != iProver_top
% 2.31/0.93      | r2_hidden(X0,sK4) = iProver_top ),
% 2.31/0.93      inference(predicate_to_equality,[status(thm)],[c_349]) ).
% 2.31/0.93  
% 2.31/0.93  cnf(c_3369,plain,
% 2.31/0.93      ( sK4 = X0
% 2.31/0.93      | m1_subset_1(sK0(X0,sK4),X0) = iProver_top
% 2.31/0.93      | r2_hidden(sK0(X0,sK4),sK4) = iProver_top ),
% 2.31/0.93      inference(superposition,[status(thm)],[c_3011,c_1055]) ).
% 2.31/0.93  
% 2.31/0.93  cnf(c_3755,plain,
% 2.31/0.93      ( u1_struct_0(sK3) = sK4
% 2.31/0.93      | r2_hidden(sK0(u1_struct_0(sK3),sK4),sK4) = iProver_top ),
% 2.31/0.93      inference(superposition,[status(thm)],[c_3369,c_1924]) ).
% 2.31/0.93  
% 2.31/0.93  cnf(c_0,plain,
% 2.31/0.93      ( ~ r2_hidden(sK0(X0,X1),X1)
% 2.31/0.93      | ~ r2_hidden(sK0(X0,X1),X0)
% 2.31/0.93      | X1 = X0 ),
% 2.31/0.93      inference(cnf_transformation,[],[f47]) ).
% 2.31/0.93  
% 2.31/0.93  cnf(c_1063,plain,
% 2.31/0.93      ( X0 = X1
% 2.31/0.93      | r2_hidden(sK0(X1,X0),X0) != iProver_top
% 2.31/0.93      | r2_hidden(sK0(X1,X0),X1) != iProver_top ),
% 2.31/0.93      inference(predicate_to_equality,[status(thm)],[c_0]) ).
% 2.31/0.93  
% 2.31/0.93  cnf(c_7504,plain,
% 2.31/0.93      ( u1_struct_0(sK3) = sK4
% 2.31/0.93      | r2_hidden(sK0(u1_struct_0(sK3),sK4),u1_struct_0(sK3)) != iProver_top ),
% 2.31/0.93      inference(superposition,[status(thm)],[c_3755,c_1063]) ).
% 2.31/0.93  
% 2.31/0.93  cnf(c_4,plain,
% 2.31/0.93      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
% 2.31/0.93      | ~ r2_hidden(X2,X0)
% 2.31/0.93      | r2_hidden(X2,X1) ),
% 2.31/0.93      inference(cnf_transformation,[],[f50]) ).
% 2.31/0.93  
% 2.31/0.93  cnf(c_1060,plain,
% 2.31/0.93      ( m1_subset_1(X0,k1_zfmisc_1(X1)) != iProver_top
% 2.31/0.93      | r2_hidden(X2,X0) != iProver_top
% 2.31/0.93      | r2_hidden(X2,X1) = iProver_top ),
% 2.31/0.93      inference(predicate_to_equality,[status(thm)],[c_4]) ).
% 2.31/0.93  
% 2.31/0.93  cnf(c_2009,plain,
% 2.31/0.93      ( r2_hidden(X0,u1_struct_0(sK3)) = iProver_top
% 2.31/0.93      | r2_hidden(X0,sK4) != iProver_top ),
% 2.31/0.93      inference(superposition,[status(thm)],[c_1057,c_1060]) ).
% 2.31/0.93  
% 2.31/0.93  cnf(c_3,plain,
% 2.31/0.93      ( m1_subset_1(k2_subset_1(X0),k1_zfmisc_1(X0)) ),
% 2.31/0.93      inference(cnf_transformation,[],[f49]) ).
% 2.31/0.93  
% 2.31/0.93  cnf(c_1061,plain,
% 2.31/0.93      ( m1_subset_1(k2_subset_1(X0),k1_zfmisc_1(X0)) = iProver_top ),
% 2.31/0.93      inference(predicate_to_equality,[status(thm)],[c_3]) ).
% 2.31/0.93  
% 2.31/0.93  cnf(c_2,plain,
% 2.31/0.93      ( k2_subset_1(X0) = X0 ),
% 2.31/0.93      inference(cnf_transformation,[],[f48]) ).
% 2.31/0.93  
% 2.31/0.93  cnf(c_1072,plain,
% 2.31/0.93      ( m1_subset_1(X0,k1_zfmisc_1(X0)) = iProver_top ),
% 2.31/0.93      inference(light_normalisation,[status(thm)],[c_1061,c_2]) ).
% 2.31/0.93  
% 2.31/0.93  cnf(c_1684,plain,
% 2.31/0.93      ( v13_waybel_0(u1_struct_0(sK3),sK3) != iProver_top
% 2.31/0.93      | m1_subset_1(X0,u1_struct_0(sK3)) != iProver_top
% 2.31/0.93      | r2_hidden(X0,u1_struct_0(sK3)) = iProver_top
% 2.31/0.93      | r2_hidden(k3_yellow_0(sK3),u1_struct_0(sK3)) != iProver_top ),
% 2.31/0.93      inference(superposition,[status(thm)],[c_1072,c_1052]) ).
% 2.31/0.93  
% 2.31/0.93  cnf(c_2194,plain,
% 2.31/0.93      ( v13_waybel_0(u1_struct_0(sK3),sK3) != iProver_top
% 2.31/0.93      | m1_subset_1(X0,u1_struct_0(sK3)) != iProver_top
% 2.31/0.93      | r2_hidden(X0,u1_struct_0(sK3)) = iProver_top
% 2.31/0.93      | r2_hidden(k3_yellow_0(sK3),sK4) != iProver_top ),
% 2.31/0.93      inference(superposition,[status(thm)],[c_2009,c_1684]) ).
% 2.31/0.93  
% 2.31/0.93  cnf(c_2494,plain,
% 2.31/0.93      ( m1_subset_1(X0,u1_struct_0(sK3)) != iProver_top
% 2.31/0.93      | r2_hidden(X0,u1_struct_0(sK3)) = iProver_top
% 2.31/0.93      | r2_hidden(k3_yellow_0(sK3),sK4) != iProver_top ),
% 2.31/0.93      inference(global_propositional_subsumption,
% 2.31/0.93                [status(thm)],
% 2.31/0.93                [c_2194,c_32,c_1685,c_2009]) ).
% 2.31/0.93  
% 2.31/0.93  cnf(c_2503,plain,
% 2.31/0.93      ( u1_struct_0(sK3) = sK4
% 2.31/0.93      | m1_subset_1(X0,u1_struct_0(sK3)) != iProver_top
% 2.31/0.93      | r2_hidden(X0,u1_struct_0(sK3)) = iProver_top ),
% 2.31/0.93      inference(superposition,[status(thm)],[c_1054,c_2494]) ).
% 2.31/0.93  
% 2.31/0.93  cnf(c_5082,plain,
% 2.31/0.93      ( u1_struct_0(sK3) = sK4
% 2.31/0.93      | r2_hidden(sK0(u1_struct_0(sK3),sK4),u1_struct_0(sK3)) = iProver_top
% 2.31/0.93      | r2_hidden(sK0(u1_struct_0(sK3),sK4),sK4) = iProver_top ),
% 2.31/0.93      inference(superposition,[status(thm)],[c_3369,c_2503]) ).
% 2.31/0.93  
% 2.31/0.93  cnf(c_734,plain,
% 2.31/0.93      ( X0 != X1 | k3_yellow_0(X0) = k3_yellow_0(X1) ),
% 2.31/0.93      theory(equality) ).
% 2.31/0.93  
% 2.31/0.93  cnf(c_742,plain,
% 2.31/0.93      ( k3_yellow_0(sK3) = k3_yellow_0(sK3) | sK3 != sK3 ),
% 2.31/0.93      inference(instantiation,[status(thm)],[c_734]) ).
% 2.31/0.93  
% 2.31/0.93  cnf(c_729,plain,( X0 = X0 ),theory(equality) ).
% 2.31/0.93  
% 2.31/0.93  cnf(c_748,plain,
% 2.31/0.93      ( sK3 = sK3 ),
% 2.31/0.93      inference(instantiation,[status(thm)],[c_729]) ).
% 2.31/0.93  
% 2.31/0.93  cnf(c_17,plain,
% 2.31/0.93      ( ~ v1_subset_1(X0,X0) | ~ m1_subset_1(X0,k1_zfmisc_1(X0)) ),
% 2.31/0.93      inference(cnf_transformation,[],[f73]) ).
% 2.31/0.93  
% 2.31/0.93  cnf(c_19,negated_conjecture,
% 2.31/0.93      ( v1_subset_1(sK4,u1_struct_0(sK3))
% 2.31/0.93      | ~ r2_hidden(k3_yellow_0(sK3),sK4) ),
% 2.31/0.93      inference(cnf_transformation,[],[f71]) ).
% 2.31/0.93  
% 2.31/0.93  cnf(c_193,plain,
% 2.31/0.93      ( v1_subset_1(sK4,u1_struct_0(sK3))
% 2.31/0.93      | ~ r2_hidden(k3_yellow_0(sK3),sK4) ),
% 2.31/0.93      inference(prop_impl,[status(thm)],[c_19]) ).
% 2.31/0.93  
% 2.31/0.93  cnf(c_401,plain,
% 2.31/0.93      ( ~ m1_subset_1(X0,k1_zfmisc_1(X0))
% 2.31/0.93      | ~ r2_hidden(k3_yellow_0(sK3),sK4)
% 2.31/0.93      | u1_struct_0(sK3) != X0
% 2.31/0.93      | sK4 != X0 ),
% 2.31/0.93      inference(resolution_lifted,[status(thm)],[c_17,c_193]) ).
% 2.31/0.93  
% 2.31/0.93  cnf(c_402,plain,
% 2.31/0.93      ( ~ m1_subset_1(u1_struct_0(sK3),k1_zfmisc_1(u1_struct_0(sK3)))
% 2.31/0.93      | ~ r2_hidden(k3_yellow_0(sK3),sK4)
% 2.31/0.93      | sK4 != u1_struct_0(sK3) ),
% 2.31/0.93      inference(unflattening,[status(thm)],[c_401]) ).
% 2.31/0.93  
% 2.31/0.93  cnf(c_1053,plain,
% 2.31/0.93      ( sK4 != u1_struct_0(sK3)
% 2.31/0.93      | m1_subset_1(u1_struct_0(sK3),k1_zfmisc_1(u1_struct_0(sK3))) != iProver_top
% 2.31/0.93      | r2_hidden(k3_yellow_0(sK3),sK4) != iProver_top ),
% 2.31/0.93      inference(predicate_to_equality,[status(thm)],[c_402]) ).
% 2.31/0.93  
% 2.31/0.93  cnf(c_1138,plain,
% 2.31/0.93      ( u1_struct_0(sK3) != sK4
% 2.31/0.93      | r2_hidden(k3_yellow_0(sK3),sK4) != iProver_top ),
% 2.31/0.93      inference(forward_subsumption_resolution,
% 2.31/0.93                [status(thm)],
% 2.31/0.93                [c_1053,c_1072]) ).
% 2.31/0.93  
% 2.31/0.93  cnf(c_1166,plain,
% 2.31/0.93      ( ~ r2_hidden(k3_yellow_0(sK3),sK4) | u1_struct_0(sK3) != sK4 ),
% 2.31/0.93      inference(predicate_to_equality_rev,[status(thm)],[c_1138]) ).
% 2.31/0.93  
% 2.31/0.93  cnf(c_1258,plain,
% 2.31/0.93      ( r2_hidden(sK0(u1_struct_0(sK3),sK4),u1_struct_0(sK3))
% 2.31/0.93      | r2_hidden(sK0(u1_struct_0(sK3),sK4),sK4)
% 2.31/0.93      | sK4 = u1_struct_0(sK3) ),
% 2.31/0.93      inference(instantiation,[status(thm)],[c_1]) ).
% 2.31/0.93  
% 2.31/0.93  cnf(c_1259,plain,
% 2.31/0.93      ( sK4 = u1_struct_0(sK3)
% 2.31/0.93      | r2_hidden(sK0(u1_struct_0(sK3),sK4),u1_struct_0(sK3)) = iProver_top
% 2.31/0.93      | r2_hidden(sK0(u1_struct_0(sK3),sK4),sK4) = iProver_top ),
% 2.31/0.93      inference(predicate_to_equality,[status(thm)],[c_1258]) ).
% 2.31/0.93  
% 2.31/0.93  cnf(c_2313,plain,
% 2.31/0.93      ( ~ m1_subset_1(k3_yellow_0(sK3),sK4)
% 2.31/0.93      | r2_hidden(k3_yellow_0(sK3),sK4) ),
% 2.31/0.93      inference(instantiation,[status(thm)],[c_349]) ).
% 2.31/0.93  
% 2.31/0.93  cnf(c_733,plain,
% 2.31/0.93      ( ~ m1_subset_1(X0,X1) | m1_subset_1(X2,X3) | X2 != X0 | X3 != X1 ),
% 2.31/0.93      theory(equality) ).
% 2.31/0.93  
% 2.31/0.93  cnf(c_1276,plain,
% 2.31/0.93      ( m1_subset_1(X0,X1)
% 2.31/0.93      | ~ m1_subset_1(k3_yellow_0(sK3),u1_struct_0(sK3))
% 2.31/0.93      | X1 != u1_struct_0(sK3)
% 2.31/0.93      | X0 != k3_yellow_0(sK3) ),
% 2.31/0.93      inference(instantiation,[status(thm)],[c_733]) ).
% 2.31/0.93  
% 2.31/0.93  cnf(c_1544,plain,
% 2.31/0.93      ( m1_subset_1(X0,sK4)
% 2.31/0.93      | ~ m1_subset_1(k3_yellow_0(sK3),u1_struct_0(sK3))
% 2.31/0.93      | X0 != k3_yellow_0(sK3)
% 2.31/0.93      | sK4 != u1_struct_0(sK3) ),
% 2.31/0.93      inference(instantiation,[status(thm)],[c_1276]) ).
% 2.31/0.93  
% 2.31/0.93  cnf(c_4380,plain,
% 2.31/0.93      ( ~ m1_subset_1(k3_yellow_0(sK3),u1_struct_0(sK3))
% 2.31/0.93      | m1_subset_1(k3_yellow_0(sK3),sK4)
% 2.31/0.93      | k3_yellow_0(sK3) != k3_yellow_0(sK3)
% 2.31/0.93      | sK4 != u1_struct_0(sK3) ),
% 2.31/0.93      inference(instantiation,[status(thm)],[c_1544]) ).
% 2.31/0.93  
% 2.31/0.93  cnf(c_7525,plain,
% 2.31/0.93      ( r2_hidden(sK0(u1_struct_0(sK3),sK4),u1_struct_0(sK3)) = iProver_top
% 2.31/0.93      | r2_hidden(sK0(u1_struct_0(sK3),sK4),sK4) = iProver_top ),
% 2.31/0.93      inference(global_propositional_subsumption,
% 2.31/0.93                [status(thm)],
% 2.31/0.93                [c_5082,c_23,c_62,c_742,c_748,c_1166,c_1259,c_2313,
% 2.31/0.93                 c_3755,c_4380]) ).
% 2.31/0.93  
% 2.31/0.93  cnf(c_7531,plain,
% 2.31/0.93      ( r2_hidden(sK0(u1_struct_0(sK3),sK4),u1_struct_0(sK3)) = iProver_top ),
% 2.31/0.93      inference(forward_subsumption_resolution,
% 2.31/0.93                [status(thm)],
% 2.31/0.93                [c_7525,c_2009]) ).
% 2.31/0.93  
% 2.31/0.93  cnf(c_7536,plain,
% 2.31/0.93      ( u1_struct_0(sK3) = sK4 ),
% 2.31/0.93      inference(global_propositional_subsumption,
% 2.31/0.93                [status(thm)],
% 2.31/0.93                [c_3017,c_7504,c_7531]) ).
% 2.31/0.93  
% 2.31/0.93  cnf(c_492,plain,
% 2.31/0.93      ( m1_subset_1(k3_yellow_0(X0),u1_struct_0(X0)) | sK3 != X0 ),
% 2.31/0.93      inference(resolution_lifted,[status(thm)],[c_8,c_23]) ).
% 2.31/0.93  
% 2.31/0.93  cnf(c_493,plain,
% 2.31/0.93      ( m1_subset_1(k3_yellow_0(sK3),u1_struct_0(sK3)) ),
% 2.31/0.93      inference(unflattening,[status(thm)],[c_492]) ).
% 2.31/0.93  
% 2.31/0.93  cnf(c_1051,plain,
% 2.31/0.93      ( m1_subset_1(k3_yellow_0(sK3),u1_struct_0(sK3)) = iProver_top ),
% 2.31/0.93      inference(predicate_to_equality,[status(thm)],[c_493]) ).
% 2.31/0.93  
% 2.31/0.93  cnf(c_7580,plain,
% 2.31/0.93      ( m1_subset_1(k3_yellow_0(sK3),sK4) = iProver_top ),
% 2.31/0.93      inference(demodulation,[status(thm)],[c_7536,c_1051]) ).
% 2.31/0.93  
% 2.31/0.93  cnf(c_2314,plain,
% 2.31/0.93      ( m1_subset_1(k3_yellow_0(sK3),sK4) != iProver_top
% 2.31/0.93      | r2_hidden(k3_yellow_0(sK3),sK4) = iProver_top ),
% 2.31/0.93      inference(predicate_to_equality,[status(thm)],[c_2313]) ).
% 2.31/0.93  
% 2.31/0.93  cnf(contradiction,plain,
% 2.31/0.93      ( $false ),
% 2.31/0.93      inference(minisat,
% 2.31/0.93                [status(thm)],
% 2.31/0.93                [c_7580,c_7531,c_7504,c_2314,c_1138]) ).
% 2.31/0.93  
% 2.31/0.93  
% 2.31/0.93  % SZS output end CNFRefutation for theBenchmark.p
% 2.31/0.93  
% 2.31/0.93  ------                               Statistics
% 2.31/0.93  
% 2.31/0.93  ------ General
% 2.31/0.93  
% 2.31/0.93  abstr_ref_over_cycles:                  0
% 2.31/0.93  abstr_ref_under_cycles:                 0
% 2.31/0.93  gc_basic_clause_elim:                   0
% 2.31/0.93  forced_gc_time:                         0
% 2.31/0.93  parsing_time:                           0.01
% 2.31/0.93  unif_index_cands_time:                  0.
% 2.31/0.93  unif_index_add_time:                    0.
% 2.31/0.93  orderings_time:                         0.
% 2.31/0.93  out_proof_time:                         0.009
% 2.31/0.93  total_time:                             0.236
% 2.31/0.93  num_of_symbols:                         50
% 2.31/0.93  num_of_terms:                           4674
% 2.31/0.93  
% 2.31/0.93  ------ Preprocessing
% 2.31/0.93  
% 2.31/0.93  num_of_splits:                          0
% 2.31/0.93  num_of_split_atoms:                     0
% 2.31/0.93  num_of_reused_defs:                     0
% 2.31/0.93  num_eq_ax_congr_red:                    18
% 2.31/0.93  num_of_sem_filtered_clauses:            1
% 2.31/0.93  num_of_subtypes:                        0
% 2.31/0.93  monotx_restored_types:                  0
% 2.31/0.93  sat_num_of_epr_types:                   0
% 2.31/0.93  sat_num_of_non_cyclic_types:            0
% 2.31/0.93  sat_guarded_non_collapsed_types:        0
% 2.31/0.93  num_pure_diseq_elim:                    0
% 2.31/0.93  simp_replaced_by:                       0
% 2.31/0.93  res_preprocessed:                       105
% 2.31/0.93  prep_upred:                             0
% 2.31/0.93  prep_unflattend:                        19
% 2.31/0.93  smt_new_axioms:                         0
% 2.31/0.93  pred_elim_cands:                        3
% 2.31/0.93  pred_elim:                              7
% 2.31/0.93  pred_elim_cl:                           8
% 2.31/0.93  pred_elim_cycles:                       9
% 2.31/0.93  merged_defs:                            2
% 2.31/0.93  merged_defs_ncl:                        0
% 2.31/0.93  bin_hyper_res:                          2
% 2.31/0.93  prep_cycles:                            4
% 2.31/0.93  pred_elim_time:                         0.006
% 2.31/0.93  splitting_time:                         0.
% 2.31/0.93  sem_filter_time:                        0.
% 2.31/0.93  monotx_time:                            0.
% 2.31/0.93  subtype_inf_time:                       0.
% 2.31/0.93  
% 2.31/0.93  ------ Problem properties
% 2.31/0.93  
% 2.31/0.93  clauses:                                19
% 2.31/0.93  conjectures:                            2
% 2.31/0.93  epr:                                    3
% 2.31/0.93  horn:                                   13
% 2.31/0.93  ground:                                 5
% 2.31/0.93  unary:                                  5
% 2.31/0.93  binary:                                 3
% 2.31/0.93  lits:                                   49
% 2.31/0.93  lits_eq:                                5
% 2.31/0.93  fd_pure:                                0
% 2.31/0.93  fd_pseudo:                              0
% 2.31/0.93  fd_cond:                                0
% 2.31/0.93  fd_pseudo_cond:                         2
% 2.31/0.93  ac_symbols:                             0
% 2.31/0.93  
% 2.31/0.93  ------ Propositional Solver
% 2.31/0.93  
% 2.31/0.93  prop_solver_calls:                      29
% 2.31/0.93  prop_fast_solver_calls:                 934
% 2.31/0.93  smt_solver_calls:                       0
% 2.31/0.93  smt_fast_solver_calls:                  0
% 2.31/0.93  prop_num_of_clauses:                    2537
% 2.31/0.93  prop_preprocess_simplified:             5832
% 2.31/0.93  prop_fo_subsumed:                       18
% 2.31/0.93  prop_solver_time:                       0.
% 2.31/0.93  smt_solver_time:                        0.
% 2.31/0.93  smt_fast_solver_time:                   0.
% 2.31/0.93  prop_fast_solver_time:                  0.
% 2.31/0.93  prop_unsat_core_time:                   0.
% 2.31/0.93  
% 2.31/0.93  ------ QBF
% 2.31/0.93  
% 2.31/0.93  qbf_q_res:                              0
% 2.31/0.93  qbf_num_tautologies:                    0
% 2.31/0.93  qbf_prep_cycles:                        0
% 2.31/0.93  
% 2.31/0.93  ------ BMC1
% 2.31/0.93  
% 2.31/0.93  bmc1_current_bound:                     -1
% 2.31/0.93  bmc1_last_solved_bound:                 -1
% 2.31/0.93  bmc1_unsat_core_size:                   -1
% 2.31/0.93  bmc1_unsat_core_parents_size:           -1
% 2.31/0.93  bmc1_merge_next_fun:                    0
% 2.31/0.93  bmc1_unsat_core_clauses_time:           0.
% 2.31/0.93  
% 2.31/0.93  ------ Instantiation
% 2.31/0.93  
% 2.31/0.93  inst_num_of_clauses:                    580
% 2.31/0.93  inst_num_in_passive:                    297
% 2.31/0.93  inst_num_in_active:                     243
% 2.31/0.93  inst_num_in_unprocessed:                41
% 2.31/0.93  inst_num_of_loops:                      400
% 2.31/0.93  inst_num_of_learning_restarts:          0
% 2.31/0.93  inst_num_moves_active_passive:          154
% 2.31/0.93  inst_lit_activity:                      0
% 2.31/0.93  inst_lit_activity_moves:                0
% 2.31/0.93  inst_num_tautologies:                   0
% 2.31/0.93  inst_num_prop_implied:                  0
% 2.31/0.93  inst_num_existing_simplified:           0
% 2.31/0.93  inst_num_eq_res_simplified:             0
% 2.31/0.93  inst_num_child_elim:                    0
% 2.31/0.93  inst_num_of_dismatching_blockings:      295
% 2.31/0.93  inst_num_of_non_proper_insts:           568
% 2.31/0.93  inst_num_of_duplicates:                 0
% 2.31/0.93  inst_inst_num_from_inst_to_res:         0
% 2.31/0.93  inst_dismatching_checking_time:         0.
% 2.31/0.93  
% 2.31/0.93  ------ Resolution
% 2.31/0.93  
% 2.31/0.93  res_num_of_clauses:                     0
% 2.31/0.93  res_num_in_passive:                     0
% 2.31/0.93  res_num_in_active:                      0
% 2.31/0.93  res_num_of_loops:                       109
% 2.31/0.93  res_forward_subset_subsumed:            34
% 2.31/0.93  res_backward_subset_subsumed:           2
% 2.31/0.93  res_forward_subsumed:                   0
% 2.31/0.93  res_backward_subsumed:                  0
% 2.31/0.93  res_forward_subsumption_resolution:     2
% 2.31/0.93  res_backward_subsumption_resolution:    0
% 2.31/0.93  res_clause_to_clause_subsumption:       1714
% 2.31/0.93  res_orphan_elimination:                 0
% 2.31/0.93  res_tautology_del:                      82
% 2.31/0.93  res_num_eq_res_simplified:              0
% 2.31/0.93  res_num_sel_changes:                    0
% 2.31/0.93  res_moves_from_active_to_pass:          0
% 2.31/0.93  
% 2.31/0.93  ------ Superposition
% 2.31/0.93  
% 2.31/0.93  sup_time_total:                         0.
% 2.31/0.93  sup_time_generating:                    0.
% 2.31/0.93  sup_time_sim_full:                      0.
% 2.31/0.93  sup_time_sim_immed:                     0.
% 2.31/0.93  
% 2.31/0.93  sup_num_of_clauses:                     128
% 2.31/0.93  sup_num_in_active:                      21
% 2.31/0.93  sup_num_in_passive:                     107
% 2.31/0.93  sup_num_of_loops:                       79
% 2.31/0.93  sup_fw_superposition:                   118
% 2.31/0.93  sup_bw_superposition:                   135
% 2.31/0.93  sup_immediate_simplified:               49
% 2.31/0.93  sup_given_eliminated:                   0
% 2.31/0.93  comparisons_done:                       0
% 2.31/0.93  comparisons_avoided:                    0
% 2.31/0.93  
% 2.31/0.93  ------ Simplifications
% 2.31/0.93  
% 2.31/0.93  
% 2.31/0.93  sim_fw_subset_subsumed:                 18
% 2.31/0.93  sim_bw_subset_subsumed:                 38
% 2.31/0.93  sim_fw_subsumed:                        28
% 2.31/0.93  sim_bw_subsumed:                        7
% 2.31/0.93  sim_fw_subsumption_res:                 2
% 2.31/0.93  sim_bw_subsumption_res:                 1
% 2.31/0.93  sim_tautology_del:                      30
% 2.31/0.93  sim_eq_tautology_del:                   10
% 2.31/0.93  sim_eq_res_simp:                        3
% 2.31/0.93  sim_fw_demodulated:                     0
% 2.31/0.93  sim_bw_demodulated:                     43
% 2.31/0.93  sim_light_normalised:                   1
% 2.31/0.93  sim_joinable_taut:                      0
% 2.31/0.93  sim_joinable_simp:                      0
% 2.31/0.93  sim_ac_normalised:                      0
% 2.31/0.93  sim_smt_subsumption:                    0
% 2.31/0.93  
%------------------------------------------------------------------------------
