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
% DateTime   : Thu Dec  3 12:28:26 EST 2020

% Result     : Theorem 3.59s
% Output     : CNFRefutation 3.59s
% Verified   : 
% Statistics : Number of formulae       :  174 (1582 expanded)
%              Number of clauses        :  105 ( 498 expanded)
%              Number of leaves         :   20 ( 290 expanded)
%              Depth                    :   29
%              Number of atoms          :  650 (10231 expanded)
%              Number of equality atoms :  147 ( 739 expanded)
%              Maximal formula depth    :   14 (   5 average)
%              Maximal clause size      :   22 (   3 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
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

fof(f44,plain,(
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

fof(f45,plain,(
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
    inference(flattening,[],[f44])).

fof(f47,plain,(
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

fof(f46,plain,
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

fof(f48,plain,
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
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3,sK4])],[f45,f47,f46])).

fof(f76,plain,(
    m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(sK3))) ),
    inference(cnf_transformation,[],[f48])).

fof(f6,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f37,plain,(
    ! [X0,X1] :
      ( ( m1_subset_1(X0,k1_zfmisc_1(X1))
        | ~ r1_tarski(X0,X1) )
      & ( r1_tarski(X0,X1)
        | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ) ) ),
    inference(nnf_transformation,[],[f6])).

fof(f57,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ) ),
    inference(cnf_transformation,[],[f37])).

fof(f3,axiom,(
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
    inference(ennf_transformation,[],[f3])).

fof(f54,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(X2,X0)
      | ~ r2_hidden(X2,X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f58,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f37])).

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

fof(f49,plain,(
    ! [X0,X1] :
      ( X0 = X1
      | r2_hidden(sK0(X0,X1),X1)
      | r2_hidden(sK0(X0,X1),X0) ) ),
    inference(cnf_transformation,[],[f34])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
     => m1_subset_1(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f19,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X0,X1)
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f55,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X0,X1)
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f5,axiom,(
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
    inference(ennf_transformation,[],[f5])).

fof(f21,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
      | v1_xboole_0(X1)
      | ~ m1_subset_1(X0,X1) ) ),
    inference(flattening,[],[f20])).

fof(f56,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
      | v1_xboole_0(X1)
      | ~ m1_subset_1(X0,X1) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f74,plain,(
    ~ v1_xboole_0(sK4) ),
    inference(cnf_transformation,[],[f48])).

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

fof(f43,plain,(
    ! [X0,X1] :
      ( ( ( v1_subset_1(X1,X0)
          | X0 = X1 )
        & ( X0 != X1
          | ~ v1_subset_1(X1,X0) ) )
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(nnf_transformation,[],[f29])).

fof(f69,plain,(
    ! [X0,X1] :
      ( v1_subset_1(X1,X0)
      | X0 = X1
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f43])).

fof(f78,plain,
    ( r2_hidden(k3_yellow_0(sK3),sK4)
    | ~ v1_subset_1(sK4,u1_struct_0(sK3)) ),
    inference(cnf_transformation,[],[f48])).

fof(f68,plain,(
    ! [X0,X1] :
      ( X0 != X1
      | ~ v1_subset_1(X1,X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f43])).

fof(f81,plain,(
    ! [X1] :
      ( ~ v1_subset_1(X1,X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X1)) ) ),
    inference(equality_resolution,[],[f68])).

fof(f77,plain,
    ( ~ r2_hidden(k3_yellow_0(sK3),sK4)
    | v1_subset_1(sK4,u1_struct_0(sK3)) ),
    inference(cnf_transformation,[],[f48])).

fof(f73,plain,(
    l1_orders_2(sK3) ),
    inference(cnf_transformation,[],[f48])).

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

fof(f60,plain,(
    ! [X0] :
      ( m1_subset_1(k3_yellow_0(X0),u1_struct_0(X0))
      | ~ l1_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( X0 = X1
    <=> ( r1_tarski(X1,X0)
        & r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f35,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(nnf_transformation,[],[f2])).

fof(f36,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(flattening,[],[f35])).

fof(f51,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | X0 != X1 ) ),
    inference(cnf_transformation,[],[f36])).

fof(f80,plain,(
    ! [X1] : r1_tarski(X1,X1) ),
    inference(equality_resolution,[],[f51])).

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

fof(f38,plain,(
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

fof(f39,plain,(
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
    inference(rectify,[],[f38])).

fof(f41,plain,(
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

fof(f40,plain,(
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

fof(f42,plain,(
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
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1,sK2])],[f39,f41,f40])).

fof(f62,plain,(
    ! [X4,X0,X5,X1] :
      ( r2_hidden(X5,X1)
      | ~ r1_orders_2(X0,X4,X5)
      | ~ r2_hidden(X4,X1)
      | ~ m1_subset_1(X5,u1_struct_0(X0))
      | ~ m1_subset_1(X4,u1_struct_0(X0))
      | ~ v13_waybel_0(X1,X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f42])).

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

fof(f61,plain,(
    ! [X0,X1] :
      ( r1_orders_2(X0,k3_yellow_0(X0),X1)
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | ~ v1_yellow_0(X0)
      | ~ v5_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f72,plain,(
    v1_yellow_0(sK3) ),
    inference(cnf_transformation,[],[f48])).

fof(f70,plain,(
    ~ v2_struct_0(sK3) ),
    inference(cnf_transformation,[],[f48])).

fof(f71,plain,(
    v5_orders_2(sK3) ),
    inference(cnf_transformation,[],[f48])).

fof(f75,plain,(
    v13_waybel_0(sK4,sK3) ),
    inference(cnf_transformation,[],[f48])).

fof(f50,plain,(
    ! [X0,X1] :
      ( X0 = X1
      | ~ r2_hidden(sK0(X0,X1),X1)
      | ~ r2_hidden(sK0(X0,X1),X0) ) ),
    inference(cnf_transformation,[],[f34])).

cnf(c_23,negated_conjecture,
    ( m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(sK3))) ),
    inference(cnf_transformation,[],[f76])).

cnf(c_1368,plain,
    ( m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(sK3))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_23])).

cnf(c_9,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | r1_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f57])).

cnf(c_1370,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(X1)) != iProver_top
    | r1_tarski(X0,X1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_9])).

cnf(c_1814,plain,
    ( r1_tarski(sK4,u1_struct_0(sK3)) = iProver_top ),
    inference(superposition,[status(thm)],[c_1368,c_1370])).

cnf(c_5,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | ~ r2_hidden(X2,X0)
    | r2_hidden(X2,X1) ),
    inference(cnf_transformation,[],[f54])).

cnf(c_8,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(X1))
    | ~ r1_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f58])).

cnf(c_224,plain,
    ( ~ r1_tarski(X0,X1)
    | m1_subset_1(X0,k1_zfmisc_1(X1)) ),
    inference(prop_impl,[status(thm)],[c_8])).

cnf(c_225,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(X1))
    | ~ r1_tarski(X0,X1) ),
    inference(renaming,[status(thm)],[c_224])).

cnf(c_288,plain,
    ( ~ r1_tarski(X0,X1)
    | ~ r2_hidden(X2,X0)
    | r2_hidden(X2,X1) ),
    inference(bin_hyper_res,[status(thm)],[c_5,c_225])).

cnf(c_1366,plain,
    ( r1_tarski(X0,X1) != iProver_top
    | r2_hidden(X2,X0) != iProver_top
    | r2_hidden(X2,X1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_288])).

cnf(c_3102,plain,
    ( r2_hidden(X0,u1_struct_0(sK3)) = iProver_top
    | r2_hidden(X0,sK4) != iProver_top ),
    inference(superposition,[status(thm)],[c_1814,c_1366])).

cnf(c_1,plain,
    ( r2_hidden(sK0(X0,X1),X1)
    | r2_hidden(sK0(X0,X1),X0)
    | X1 = X0 ),
    inference(cnf_transformation,[],[f49])).

cnf(c_1375,plain,
    ( X0 = X1
    | r2_hidden(sK0(X1,X0),X0) = iProver_top
    | r2_hidden(sK0(X1,X0),X1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1])).

cnf(c_6,plain,
    ( m1_subset_1(X0,X1)
    | ~ r2_hidden(X0,X1) ),
    inference(cnf_transformation,[],[f55])).

cnf(c_1372,plain,
    ( m1_subset_1(X0,X1) = iProver_top
    | r2_hidden(X0,X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_6])).

cnf(c_2205,plain,
    ( X0 = X1
    | m1_subset_1(sK0(X0,X1),X0) = iProver_top
    | r2_hidden(sK0(X0,X1),X1) = iProver_top ),
    inference(superposition,[status(thm)],[c_1375,c_1372])).

cnf(c_3114,plain,
    ( X0 = X1
    | m1_subset_1(sK0(X1,X0),X1) = iProver_top
    | m1_subset_1(sK0(X1,X0),X0) = iProver_top ),
    inference(superposition,[status(thm)],[c_2205,c_1372])).

cnf(c_7,plain,
    ( ~ m1_subset_1(X0,X1)
    | r2_hidden(X0,X1)
    | v1_xboole_0(X1) ),
    inference(cnf_transformation,[],[f56])).

cnf(c_25,negated_conjecture,
    ( ~ v1_xboole_0(sK4) ),
    inference(cnf_transformation,[],[f74])).

cnf(c_397,plain,
    ( ~ m1_subset_1(X0,X1)
    | r2_hidden(X0,X1)
    | sK4 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_7,c_25])).

cnf(c_398,plain,
    ( ~ m1_subset_1(X0,sK4)
    | r2_hidden(X0,sK4) ),
    inference(unflattening,[status(thm)],[c_397])).

cnf(c_1365,plain,
    ( m1_subset_1(X0,sK4) != iProver_top
    | r2_hidden(X0,sK4) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_398])).

cnf(c_4516,plain,
    ( sK4 = X0
    | m1_subset_1(sK0(X0,sK4),X0) = iProver_top
    | r2_hidden(sK0(X0,sK4),sK4) = iProver_top ),
    inference(superposition,[status(thm)],[c_3114,c_1365])).

cnf(c_19,plain,
    ( v1_subset_1(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | X0 = X1 ),
    inference(cnf_transformation,[],[f69])).

cnf(c_291,plain,
    ( v1_subset_1(X0,X1)
    | ~ r1_tarski(X0,X1)
    | X0 = X1 ),
    inference(bin_hyper_res,[status(thm)],[c_19,c_225])).

cnf(c_21,negated_conjecture,
    ( ~ v1_subset_1(sK4,u1_struct_0(sK3))
    | r2_hidden(k3_yellow_0(sK3),sK4) ),
    inference(cnf_transformation,[],[f78])).

cnf(c_228,plain,
    ( ~ v1_subset_1(sK4,u1_struct_0(sK3))
    | r2_hidden(k3_yellow_0(sK3),sK4) ),
    inference(prop_impl,[status(thm)],[c_21])).

cnf(c_436,plain,
    ( ~ r1_tarski(X0,X1)
    | r2_hidden(k3_yellow_0(sK3),sK4)
    | X1 = X0
    | u1_struct_0(sK3) != X1
    | sK4 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_291,c_228])).

cnf(c_437,plain,
    ( ~ r1_tarski(sK4,u1_struct_0(sK3))
    | r2_hidden(k3_yellow_0(sK3),sK4)
    | u1_struct_0(sK3) = sK4 ),
    inference(unflattening,[status(thm)],[c_436])).

cnf(c_1364,plain,
    ( u1_struct_0(sK3) = sK4
    | r1_tarski(sK4,u1_struct_0(sK3)) != iProver_top
    | r2_hidden(k3_yellow_0(sK3),sK4) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_437])).

cnf(c_36,plain,
    ( m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(sK3))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_23])).

cnf(c_438,plain,
    ( u1_struct_0(sK3) = sK4
    | r1_tarski(sK4,u1_struct_0(sK3)) != iProver_top
    | r2_hidden(k3_yellow_0(sK3),sK4) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_437])).

cnf(c_1558,plain,
    ( ~ m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(sK3)))
    | r1_tarski(sK4,u1_struct_0(sK3)) ),
    inference(instantiation,[status(thm)],[c_9])).

cnf(c_1559,plain,
    ( m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(sK3))) != iProver_top
    | r1_tarski(sK4,u1_struct_0(sK3)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1558])).

cnf(c_847,plain,
    ( X0 = X0 ),
    theory(equality)).

cnf(c_1633,plain,
    ( sK4 = sK4 ),
    inference(instantiation,[status(thm)],[c_847])).

cnf(c_20,plain,
    ( ~ v1_subset_1(X0,X0)
    | ~ m1_subset_1(X0,k1_zfmisc_1(X0)) ),
    inference(cnf_transformation,[],[f81])).

cnf(c_22,negated_conjecture,
    ( v1_subset_1(sK4,u1_struct_0(sK3))
    | ~ r2_hidden(k3_yellow_0(sK3),sK4) ),
    inference(cnf_transformation,[],[f77])).

cnf(c_226,plain,
    ( v1_subset_1(sK4,u1_struct_0(sK3))
    | ~ r2_hidden(k3_yellow_0(sK3),sK4) ),
    inference(prop_impl,[status(thm)],[c_22])).

cnf(c_449,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X0))
    | ~ r2_hidden(k3_yellow_0(sK3),sK4)
    | u1_struct_0(sK3) != X0
    | sK4 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_20,c_226])).

cnf(c_450,plain,
    ( ~ m1_subset_1(u1_struct_0(sK3),k1_zfmisc_1(u1_struct_0(sK3)))
    | ~ r2_hidden(k3_yellow_0(sK3),sK4)
    | sK4 != u1_struct_0(sK3) ),
    inference(unflattening,[status(thm)],[c_449])).

cnf(c_1363,plain,
    ( sK4 != u1_struct_0(sK3)
    | m1_subset_1(u1_struct_0(sK3),k1_zfmisc_1(u1_struct_0(sK3))) != iProver_top
    | r2_hidden(k3_yellow_0(sK3),sK4) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_450])).

cnf(c_26,negated_conjecture,
    ( l1_orders_2(sK3) ),
    inference(cnf_transformation,[],[f73])).

cnf(c_33,plain,
    ( l1_orders_2(sK3) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_26])).

cnf(c_40,plain,
    ( ~ v1_subset_1(sK3,sK3)
    | ~ m1_subset_1(sK3,k1_zfmisc_1(sK3)) ),
    inference(instantiation,[status(thm)],[c_20])).

cnf(c_43,plain,
    ( v1_subset_1(sK3,sK3)
    | ~ m1_subset_1(sK3,k1_zfmisc_1(sK3))
    | sK3 = sK3 ),
    inference(instantiation,[status(thm)],[c_19])).

cnf(c_11,plain,
    ( m1_subset_1(k3_yellow_0(X0),u1_struct_0(X0))
    | ~ l1_orders_2(X0) ),
    inference(cnf_transformation,[],[f60])).

cnf(c_64,plain,
    ( m1_subset_1(k3_yellow_0(X0),u1_struct_0(X0)) = iProver_top
    | l1_orders_2(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_11])).

cnf(c_66,plain,
    ( m1_subset_1(k3_yellow_0(sK3),u1_struct_0(sK3)) = iProver_top
    | l1_orders_2(sK3) != iProver_top ),
    inference(instantiation,[status(thm)],[c_64])).

cnf(c_74,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(sK3))
    | ~ r1_tarski(sK3,sK3) ),
    inference(instantiation,[status(thm)],[c_8])).

cnf(c_4,plain,
    ( r1_tarski(X0,X0) ),
    inference(cnf_transformation,[],[f80])).

cnf(c_84,plain,
    ( r1_tarski(sK3,sK3) ),
    inference(instantiation,[status(thm)],[c_4])).

cnf(c_451,plain,
    ( sK4 != u1_struct_0(sK3)
    | m1_subset_1(u1_struct_0(sK3),k1_zfmisc_1(u1_struct_0(sK3))) != iProver_top
    | r2_hidden(k3_yellow_0(sK3),sK4) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_450])).

cnf(c_853,plain,
    ( X0 != X1
    | k3_yellow_0(X0) = k3_yellow_0(X1) ),
    theory(equality)).

cnf(c_862,plain,
    ( k3_yellow_0(sK3) = k3_yellow_0(sK3)
    | sK3 != sK3 ),
    inference(instantiation,[status(thm)],[c_853])).

cnf(c_1553,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK3)))
    | ~ r1_tarski(X0,u1_struct_0(sK3)) ),
    inference(instantiation,[status(thm)],[c_8])).

cnf(c_1643,plain,
    ( m1_subset_1(u1_struct_0(sK3),k1_zfmisc_1(u1_struct_0(sK3)))
    | ~ r1_tarski(u1_struct_0(sK3),u1_struct_0(sK3)) ),
    inference(instantiation,[status(thm)],[c_1553])).

cnf(c_1645,plain,
    ( m1_subset_1(u1_struct_0(sK3),k1_zfmisc_1(u1_struct_0(sK3))) = iProver_top
    | r1_tarski(u1_struct_0(sK3),u1_struct_0(sK3)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1643])).

cnf(c_1644,plain,
    ( r1_tarski(u1_struct_0(sK3),u1_struct_0(sK3)) ),
    inference(instantiation,[status(thm)],[c_4])).

cnf(c_1647,plain,
    ( r1_tarski(u1_struct_0(sK3),u1_struct_0(sK3)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1644])).

cnf(c_852,plain,
    ( ~ m1_subset_1(X0,X1)
    | m1_subset_1(X2,X3)
    | X2 != X0
    | X3 != X1 ),
    theory(equality)).

cnf(c_1572,plain,
    ( m1_subset_1(X0,X1)
    | ~ m1_subset_1(k3_yellow_0(sK3),u1_struct_0(sK3))
    | X1 != u1_struct_0(sK3)
    | X0 != k3_yellow_0(sK3) ),
    inference(instantiation,[status(thm)],[c_852])).

cnf(c_1831,plain,
    ( m1_subset_1(k3_yellow_0(sK3),X0)
    | ~ m1_subset_1(k3_yellow_0(sK3),u1_struct_0(sK3))
    | X0 != u1_struct_0(sK3)
    | k3_yellow_0(sK3) != k3_yellow_0(sK3) ),
    inference(instantiation,[status(thm)],[c_1572])).

cnf(c_2060,plain,
    ( ~ m1_subset_1(k3_yellow_0(sK3),u1_struct_0(sK3))
    | m1_subset_1(k3_yellow_0(sK3),sK4)
    | k3_yellow_0(sK3) != k3_yellow_0(sK3)
    | sK4 != u1_struct_0(sK3) ),
    inference(instantiation,[status(thm)],[c_1831])).

cnf(c_2062,plain,
    ( k3_yellow_0(sK3) != k3_yellow_0(sK3)
    | sK4 != u1_struct_0(sK3)
    | m1_subset_1(k3_yellow_0(sK3),u1_struct_0(sK3)) != iProver_top
    | m1_subset_1(k3_yellow_0(sK3),sK4) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2060])).

cnf(c_2061,plain,
    ( ~ m1_subset_1(k3_yellow_0(sK3),sK4)
    | r2_hidden(k3_yellow_0(sK3),sK4) ),
    inference(instantiation,[status(thm)],[c_398])).

cnf(c_2064,plain,
    ( m1_subset_1(k3_yellow_0(sK3),sK4) != iProver_top
    | r2_hidden(k3_yellow_0(sK3),sK4) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2061])).

cnf(c_2111,plain,
    ( sK4 != u1_struct_0(sK3) ),
    inference(global_propositional_subsumption,[status(thm)],[c_1363,c_33,c_40,c_43,c_66,c_74,c_84,c_451,c_862,c_1645,c_1647,c_2062,c_2064])).

cnf(c_848,plain,
    ( X0 != X1
    | X2 != X1
    | X2 = X0 ),
    theory(equality)).

cnf(c_1675,plain,
    ( X0 != X1
    | X0 = u1_struct_0(sK3)
    | u1_struct_0(sK3) != X1 ),
    inference(instantiation,[status(thm)],[c_848])).

cnf(c_2148,plain,
    ( u1_struct_0(sK3) != X0
    | sK4 != X0
    | sK4 = u1_struct_0(sK3) ),
    inference(instantiation,[status(thm)],[c_1675])).

cnf(c_2693,plain,
    ( u1_struct_0(sK3) != sK4
    | sK4 = u1_struct_0(sK3)
    | sK4 != sK4 ),
    inference(instantiation,[status(thm)],[c_2148])).

cnf(c_3056,plain,
    ( r2_hidden(k3_yellow_0(sK3),sK4) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_1364,c_33,c_36,c_40,c_43,c_66,c_74,c_84,c_438,c_451,c_862,c_1559,c_1633,c_1645,c_1647,c_2062,c_2064,c_2693])).

cnf(c_18,plain,
    ( ~ r1_orders_2(X0,X1,X2)
    | ~ v13_waybel_0(X3,X0)
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | ~ m1_subset_1(X1,u1_struct_0(X0))
    | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))
    | ~ r2_hidden(X1,X3)
    | r2_hidden(X2,X3)
    | ~ l1_orders_2(X0) ),
    inference(cnf_transformation,[],[f62])).

cnf(c_12,plain,
    ( r1_orders_2(X0,k3_yellow_0(X0),X1)
    | ~ m1_subset_1(X1,u1_struct_0(X0))
    | v2_struct_0(X0)
    | ~ v5_orders_2(X0)
    | ~ v1_yellow_0(X0)
    | ~ l1_orders_2(X0) ),
    inference(cnf_transformation,[],[f61])).

cnf(c_27,negated_conjecture,
    ( v1_yellow_0(sK3) ),
    inference(cnf_transformation,[],[f72])).

cnf(c_412,plain,
    ( r1_orders_2(X0,k3_yellow_0(X0),X1)
    | ~ m1_subset_1(X1,u1_struct_0(X0))
    | v2_struct_0(X0)
    | ~ v5_orders_2(X0)
    | ~ l1_orders_2(X0)
    | sK3 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_12,c_27])).

cnf(c_413,plain,
    ( r1_orders_2(sK3,k3_yellow_0(sK3),X0)
    | ~ m1_subset_1(X0,u1_struct_0(sK3))
    | v2_struct_0(sK3)
    | ~ v5_orders_2(sK3)
    | ~ l1_orders_2(sK3) ),
    inference(unflattening,[status(thm)],[c_412])).

cnf(c_29,negated_conjecture,
    ( ~ v2_struct_0(sK3) ),
    inference(cnf_transformation,[],[f70])).

cnf(c_28,negated_conjecture,
    ( v5_orders_2(sK3) ),
    inference(cnf_transformation,[],[f71])).

cnf(c_417,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(sK3))
    | r1_orders_2(sK3,k3_yellow_0(sK3),X0) ),
    inference(global_propositional_subsumption,[status(thm)],[c_413,c_29,c_28,c_26])).

cnf(c_418,plain,
    ( r1_orders_2(sK3,k3_yellow_0(sK3),X0)
    | ~ m1_subset_1(X0,u1_struct_0(sK3)) ),
    inference(renaming,[status(thm)],[c_417])).

cnf(c_500,plain,
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
    inference(resolution_lifted,[status(thm)],[c_18,c_418])).

cnf(c_501,plain,
    ( ~ v13_waybel_0(X0,sK3)
    | ~ m1_subset_1(X1,u1_struct_0(sK3))
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK3)))
    | ~ m1_subset_1(k3_yellow_0(sK3),u1_struct_0(sK3))
    | r2_hidden(X1,X0)
    | ~ r2_hidden(k3_yellow_0(sK3),X0)
    | ~ l1_orders_2(sK3) ),
    inference(unflattening,[status(thm)],[c_500])).

cnf(c_65,plain,
    ( m1_subset_1(k3_yellow_0(sK3),u1_struct_0(sK3))
    | ~ l1_orders_2(sK3) ),
    inference(instantiation,[status(thm)],[c_11])).

cnf(c_505,plain,
    ( ~ r2_hidden(k3_yellow_0(sK3),X0)
    | r2_hidden(X1,X0)
    | ~ v13_waybel_0(X0,sK3)
    | ~ m1_subset_1(X1,u1_struct_0(sK3))
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK3))) ),
    inference(global_propositional_subsumption,[status(thm)],[c_501,c_26,c_65])).

cnf(c_506,plain,
    ( ~ v13_waybel_0(X0,sK3)
    | ~ m1_subset_1(X1,u1_struct_0(sK3))
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK3)))
    | r2_hidden(X1,X0)
    | ~ r2_hidden(k3_yellow_0(sK3),X0) ),
    inference(renaming,[status(thm)],[c_505])).

cnf(c_1362,plain,
    ( v13_waybel_0(X0,sK3) != iProver_top
    | m1_subset_1(X1,u1_struct_0(sK3)) != iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK3))) != iProver_top
    | r2_hidden(X1,X0) = iProver_top
    | r2_hidden(k3_yellow_0(sK3),X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_506])).

cnf(c_1991,plain,
    ( v13_waybel_0(sK4,sK3) != iProver_top
    | m1_subset_1(X0,u1_struct_0(sK3)) != iProver_top
    | r2_hidden(X0,sK4) = iProver_top
    | r2_hidden(k3_yellow_0(sK3),sK4) != iProver_top ),
    inference(superposition,[status(thm)],[c_1368,c_1362])).

cnf(c_24,negated_conjecture,
    ( v13_waybel_0(sK4,sK3) ),
    inference(cnf_transformation,[],[f75])).

cnf(c_35,plain,
    ( v13_waybel_0(sK4,sK3) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_24])).

cnf(c_2017,plain,
    ( m1_subset_1(X0,u1_struct_0(sK3)) != iProver_top
    | r2_hidden(X0,sK4) = iProver_top
    | r2_hidden(k3_yellow_0(sK3),sK4) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_1991,c_35])).

cnf(c_3062,plain,
    ( m1_subset_1(X0,u1_struct_0(sK3)) != iProver_top
    | r2_hidden(X0,sK4) = iProver_top ),
    inference(superposition,[status(thm)],[c_3056,c_2017])).

cnf(c_5223,plain,
    ( u1_struct_0(sK3) = sK4
    | r2_hidden(sK0(u1_struct_0(sK3),sK4),sK4) = iProver_top ),
    inference(superposition,[status(thm)],[c_4516,c_3062])).

cnf(c_9347,plain,
    ( r2_hidden(sK0(u1_struct_0(sK3),sK4),sK4) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_5223,c_33,c_40,c_43,c_66,c_74,c_84,c_451,c_862,c_1633,c_1645,c_1647,c_2062,c_2064,c_2693])).

cnf(c_0,plain,
    ( ~ r2_hidden(sK0(X0,X1),X1)
    | ~ r2_hidden(sK0(X0,X1),X0)
    | X1 = X0 ),
    inference(cnf_transformation,[],[f50])).

cnf(c_1376,plain,
    ( X0 = X1
    | r2_hidden(sK0(X1,X0),X0) != iProver_top
    | r2_hidden(sK0(X1,X0),X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_0])).

cnf(c_9354,plain,
    ( u1_struct_0(sK3) = sK4
    | r2_hidden(sK0(u1_struct_0(sK3),sK4),u1_struct_0(sK3)) != iProver_top ),
    inference(superposition,[status(thm)],[c_9347,c_1376])).

cnf(c_1660,plain,
    ( ~ r2_hidden(sK0(u1_struct_0(sK3),X0),X0)
    | ~ r2_hidden(sK0(u1_struct_0(sK3),X0),u1_struct_0(sK3))
    | X0 = u1_struct_0(sK3) ),
    inference(instantiation,[status(thm)],[c_0])).

cnf(c_2149,plain,
    ( ~ r2_hidden(sK0(u1_struct_0(sK3),sK4),u1_struct_0(sK3))
    | ~ r2_hidden(sK0(u1_struct_0(sK3),sK4),sK4)
    | sK4 = u1_struct_0(sK3) ),
    inference(instantiation,[status(thm)],[c_1660])).

cnf(c_2158,plain,
    ( sK4 = u1_struct_0(sK3)
    | r2_hidden(sK0(u1_struct_0(sK3),sK4),u1_struct_0(sK3)) != iProver_top
    | r2_hidden(sK0(u1_struct_0(sK3),sK4),sK4) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2149])).

cnf(c_9900,plain,
    ( r2_hidden(sK0(u1_struct_0(sK3),sK4),u1_struct_0(sK3)) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_9354,c_33,c_40,c_43,c_66,c_74,c_84,c_451,c_862,c_1633,c_1645,c_1647,c_2062,c_2064,c_2158,c_2693,c_5223])).

cnf(c_9909,plain,
    ( r2_hidden(sK0(u1_struct_0(sK3),sK4),sK4) != iProver_top ),
    inference(superposition,[status(thm)],[c_3102,c_9900])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_9909,c_5223,c_2693,c_2111,c_1633])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.13/0.13  % Command    : iproveropt_run.sh %d %s
% 0.13/0.34  % Computer   : n017.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 14:16:16 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.35  % Running in FOF mode
% 3.59/1.00  % SZS status Started for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.59/1.00  
% 3.59/1.00  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 3.59/1.00  
% 3.59/1.00  ------  iProver source info
% 3.59/1.00  
% 3.59/1.00  git: date: 2020-06-30 10:37:57 +0100
% 3.59/1.00  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 3.59/1.00  git: non_committed_changes: false
% 3.59/1.00  git: last_make_outside_of_git: false
% 3.59/1.00  
% 3.59/1.00  ------ 
% 3.59/1.00  
% 3.59/1.00  ------ Input Options
% 3.59/1.00  
% 3.59/1.00  --out_options                           all
% 3.59/1.00  --tptp_safe_out                         true
% 3.59/1.00  --problem_path                          ""
% 3.59/1.00  --include_path                          ""
% 3.59/1.00  --clausifier                            res/vclausify_rel
% 3.59/1.00  --clausifier_options                    --mode clausify
% 3.59/1.00  --stdin                                 false
% 3.59/1.00  --stats_out                             all
% 3.59/1.00  
% 3.59/1.00  ------ General Options
% 3.59/1.00  
% 3.59/1.00  --fof                                   false
% 3.59/1.00  --time_out_real                         305.
% 3.59/1.00  --time_out_virtual                      -1.
% 3.59/1.00  --symbol_type_check                     false
% 3.59/1.00  --clausify_out                          false
% 3.59/1.00  --sig_cnt_out                           false
% 3.59/1.00  --trig_cnt_out                          false
% 3.59/1.00  --trig_cnt_out_tolerance                1.
% 3.59/1.00  --trig_cnt_out_sk_spl                   false
% 3.59/1.00  --abstr_cl_out                          false
% 3.59/1.00  
% 3.59/1.00  ------ Global Options
% 3.59/1.00  
% 3.59/1.00  --schedule                              default
% 3.59/1.00  --add_important_lit                     false
% 3.59/1.00  --prop_solver_per_cl                    1000
% 3.59/1.00  --min_unsat_core                        false
% 3.59/1.00  --soft_assumptions                      false
% 3.59/1.00  --soft_lemma_size                       3
% 3.59/1.00  --prop_impl_unit_size                   0
% 3.59/1.00  --prop_impl_unit                        []
% 3.59/1.00  --share_sel_clauses                     true
% 3.59/1.00  --reset_solvers                         false
% 3.59/1.00  --bc_imp_inh                            [conj_cone]
% 3.59/1.00  --conj_cone_tolerance                   3.
% 3.59/1.00  --extra_neg_conj                        none
% 3.59/1.00  --large_theory_mode                     true
% 3.59/1.00  --prolific_symb_bound                   200
% 3.59/1.00  --lt_threshold                          2000
% 3.59/1.00  --clause_weak_htbl                      true
% 3.59/1.00  --gc_record_bc_elim                     false
% 3.59/1.00  
% 3.59/1.00  ------ Preprocessing Options
% 3.59/1.00  
% 3.59/1.00  --preprocessing_flag                    true
% 3.59/1.00  --time_out_prep_mult                    0.1
% 3.59/1.00  --splitting_mode                        input
% 3.59/1.00  --splitting_grd                         true
% 3.59/1.00  --splitting_cvd                         false
% 3.59/1.00  --splitting_cvd_svl                     false
% 3.59/1.00  --splitting_nvd                         32
% 3.59/1.00  --sub_typing                            true
% 3.59/1.00  --prep_gs_sim                           true
% 3.59/1.00  --prep_unflatten                        true
% 3.59/1.00  --prep_res_sim                          true
% 3.59/1.00  --prep_upred                            true
% 3.59/1.00  --prep_sem_filter                       exhaustive
% 3.59/1.00  --prep_sem_filter_out                   false
% 3.59/1.00  --pred_elim                             true
% 3.59/1.00  --res_sim_input                         true
% 3.59/1.00  --eq_ax_congr_red                       true
% 3.59/1.00  --pure_diseq_elim                       true
% 3.59/1.00  --brand_transform                       false
% 3.59/1.00  --non_eq_to_eq                          false
% 3.59/1.00  --prep_def_merge                        true
% 3.59/1.00  --prep_def_merge_prop_impl              false
% 3.59/1.00  --prep_def_merge_mbd                    true
% 3.59/1.00  --prep_def_merge_tr_red                 false
% 3.59/1.00  --prep_def_merge_tr_cl                  false
% 3.59/1.00  --smt_preprocessing                     true
% 3.59/1.00  --smt_ac_axioms                         fast
% 3.59/1.00  --preprocessed_out                      false
% 3.59/1.00  --preprocessed_stats                    false
% 3.59/1.00  
% 3.59/1.00  ------ Abstraction refinement Options
% 3.59/1.00  
% 3.59/1.00  --abstr_ref                             []
% 3.59/1.00  --abstr_ref_prep                        false
% 3.59/1.00  --abstr_ref_until_sat                   false
% 3.59/1.00  --abstr_ref_sig_restrict                funpre
% 3.59/1.00  --abstr_ref_af_restrict_to_split_sk     false
% 3.59/1.00  --abstr_ref_under                       []
% 3.59/1.00  
% 3.59/1.00  ------ SAT Options
% 3.59/1.00  
% 3.59/1.00  --sat_mode                              false
% 3.59/1.00  --sat_fm_restart_options                ""
% 3.59/1.00  --sat_gr_def                            false
% 3.59/1.00  --sat_epr_types                         true
% 3.59/1.00  --sat_non_cyclic_types                  false
% 3.59/1.00  --sat_finite_models                     false
% 3.59/1.00  --sat_fm_lemmas                         false
% 3.59/1.00  --sat_fm_prep                           false
% 3.59/1.00  --sat_fm_uc_incr                        true
% 3.59/1.00  --sat_out_model                         small
% 3.59/1.00  --sat_out_clauses                       false
% 3.59/1.00  
% 3.59/1.00  ------ QBF Options
% 3.59/1.00  
% 3.59/1.00  --qbf_mode                              false
% 3.59/1.00  --qbf_elim_univ                         false
% 3.59/1.00  --qbf_dom_inst                          none
% 3.59/1.00  --qbf_dom_pre_inst                      false
% 3.59/1.00  --qbf_sk_in                             false
% 3.59/1.00  --qbf_pred_elim                         true
% 3.59/1.00  --qbf_split                             512
% 3.59/1.00  
% 3.59/1.00  ------ BMC1 Options
% 3.59/1.00  
% 3.59/1.00  --bmc1_incremental                      false
% 3.59/1.00  --bmc1_axioms                           reachable_all
% 3.59/1.00  --bmc1_min_bound                        0
% 3.59/1.00  --bmc1_max_bound                        -1
% 3.59/1.00  --bmc1_max_bound_default                -1
% 3.59/1.00  --bmc1_symbol_reachability              true
% 3.59/1.00  --bmc1_property_lemmas                  false
% 3.59/1.00  --bmc1_k_induction                      false
% 3.59/1.00  --bmc1_non_equiv_states                 false
% 3.59/1.00  --bmc1_deadlock                         false
% 3.59/1.00  --bmc1_ucm                              false
% 3.59/1.00  --bmc1_add_unsat_core                   none
% 3.59/1.00  --bmc1_unsat_core_children              false
% 3.59/1.00  --bmc1_unsat_core_extrapolate_axioms    false
% 3.59/1.00  --bmc1_out_stat                         full
% 3.59/1.00  --bmc1_ground_init                      false
% 3.59/1.00  --bmc1_pre_inst_next_state              false
% 3.59/1.00  --bmc1_pre_inst_state                   false
% 3.59/1.00  --bmc1_pre_inst_reach_state             false
% 3.59/1.00  --bmc1_out_unsat_core                   false
% 3.59/1.00  --bmc1_aig_witness_out                  false
% 3.59/1.00  --bmc1_verbose                          false
% 3.59/1.00  --bmc1_dump_clauses_tptp                false
% 3.59/1.00  --bmc1_dump_unsat_core_tptp             false
% 3.59/1.00  --bmc1_dump_file                        -
% 3.59/1.00  --bmc1_ucm_expand_uc_limit              128
% 3.59/1.00  --bmc1_ucm_n_expand_iterations          6
% 3.59/1.00  --bmc1_ucm_extend_mode                  1
% 3.59/1.00  --bmc1_ucm_init_mode                    2
% 3.59/1.00  --bmc1_ucm_cone_mode                    none
% 3.59/1.00  --bmc1_ucm_reduced_relation_type        0
% 3.59/1.00  --bmc1_ucm_relax_model                  4
% 3.59/1.00  --bmc1_ucm_full_tr_after_sat            true
% 3.59/1.00  --bmc1_ucm_expand_neg_assumptions       false
% 3.59/1.00  --bmc1_ucm_layered_model                none
% 3.59/1.00  --bmc1_ucm_max_lemma_size               10
% 3.59/1.00  
% 3.59/1.00  ------ AIG Options
% 3.59/1.00  
% 3.59/1.00  --aig_mode                              false
% 3.59/1.00  
% 3.59/1.00  ------ Instantiation Options
% 3.59/1.00  
% 3.59/1.00  --instantiation_flag                    true
% 3.59/1.00  --inst_sos_flag                         false
% 3.59/1.00  --inst_sos_phase                        true
% 3.59/1.00  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 3.59/1.00  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 3.59/1.00  --inst_lit_sel_side                     num_symb
% 3.59/1.00  --inst_solver_per_active                1400
% 3.59/1.00  --inst_solver_calls_frac                1.
% 3.59/1.00  --inst_passive_queue_type               priority_queues
% 3.59/1.00  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 3.59/1.00  --inst_passive_queues_freq              [25;2]
% 3.59/1.00  --inst_dismatching                      true
% 3.59/1.00  --inst_eager_unprocessed_to_passive     true
% 3.59/1.00  --inst_prop_sim_given                   true
% 3.59/1.00  --inst_prop_sim_new                     false
% 3.59/1.00  --inst_subs_new                         false
% 3.59/1.00  --inst_eq_res_simp                      false
% 3.59/1.00  --inst_subs_given                       false
% 3.59/1.00  --inst_orphan_elimination               true
% 3.59/1.00  --inst_learning_loop_flag               true
% 3.59/1.00  --inst_learning_start                   3000
% 3.59/1.00  --inst_learning_factor                  2
% 3.59/1.00  --inst_start_prop_sim_after_learn       3
% 3.59/1.00  --inst_sel_renew                        solver
% 3.59/1.00  --inst_lit_activity_flag                true
% 3.59/1.00  --inst_restr_to_given                   false
% 3.59/1.00  --inst_activity_threshold               500
% 3.59/1.00  --inst_out_proof                        true
% 3.59/1.00  
% 3.59/1.00  ------ Resolution Options
% 3.59/1.00  
% 3.59/1.00  --resolution_flag                       true
% 3.59/1.00  --res_lit_sel                           adaptive
% 3.59/1.00  --res_lit_sel_side                      none
% 3.59/1.00  --res_ordering                          kbo
% 3.59/1.00  --res_to_prop_solver                    active
% 3.59/1.00  --res_prop_simpl_new                    false
% 3.59/1.00  --res_prop_simpl_given                  true
% 3.59/1.00  --res_passive_queue_type                priority_queues
% 3.59/1.00  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 3.59/1.00  --res_passive_queues_freq               [15;5]
% 3.59/1.00  --res_forward_subs                      full
% 3.59/1.00  --res_backward_subs                     full
% 3.59/1.00  --res_forward_subs_resolution           true
% 3.59/1.00  --res_backward_subs_resolution          true
% 3.59/1.00  --res_orphan_elimination                true
% 3.59/1.00  --res_time_limit                        2.
% 3.59/1.00  --res_out_proof                         true
% 3.59/1.00  
% 3.59/1.00  ------ Superposition Options
% 3.59/1.00  
% 3.59/1.00  --superposition_flag                    true
% 3.59/1.00  --sup_passive_queue_type                priority_queues
% 3.59/1.00  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 3.59/1.00  --sup_passive_queues_freq               [8;1;4]
% 3.59/1.00  --demod_completeness_check              fast
% 3.59/1.00  --demod_use_ground                      true
% 3.59/1.00  --sup_to_prop_solver                    passive
% 3.59/1.00  --sup_prop_simpl_new                    true
% 3.59/1.00  --sup_prop_simpl_given                  true
% 3.59/1.00  --sup_fun_splitting                     false
% 3.59/1.00  --sup_smt_interval                      50000
% 3.59/1.00  
% 3.59/1.00  ------ Superposition Simplification Setup
% 3.59/1.00  
% 3.59/1.00  --sup_indices_passive                   []
% 3.59/1.00  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.59/1.00  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.59/1.00  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.59/1.00  --sup_full_triv                         [TrivRules;PropSubs]
% 3.59/1.00  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.59/1.00  --sup_full_bw                           [BwDemod]
% 3.59/1.00  --sup_immed_triv                        [TrivRules]
% 3.59/1.00  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 3.59/1.00  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.59/1.00  --sup_immed_bw_main                     []
% 3.59/1.00  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 3.59/1.00  --sup_input_triv                        [Unflattening;TrivRules]
% 3.59/1.00  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.59/1.00  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 3.59/1.00  
% 3.59/1.00  ------ Combination Options
% 3.59/1.00  
% 3.59/1.00  --comb_res_mult                         3
% 3.59/1.00  --comb_sup_mult                         2
% 3.59/1.00  --comb_inst_mult                        10
% 3.59/1.00  
% 3.59/1.00  ------ Debug Options
% 3.59/1.00  
% 3.59/1.00  --dbg_backtrace                         false
% 3.59/1.00  --dbg_dump_prop_clauses                 false
% 3.59/1.00  --dbg_dump_prop_clauses_file            -
% 3.59/1.00  --dbg_out_stat                          false
% 3.59/1.00  ------ Parsing...
% 3.59/1.00  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 3.59/1.00  
% 3.59/1.00  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe:1:0s pe:2:0s pe:4:0s pe_e  sf_s  rm: 8 0s  sf_e  pe_s  pe_e 
% 3.59/1.00  
% 3.59/1.00  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 3.59/1.00  
% 3.59/1.00  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 3.59/1.00  ------ Proving...
% 3.59/1.00  ------ Problem Properties 
% 3.59/1.00  
% 3.59/1.00  
% 3.59/1.00  clauses                                 21
% 3.59/1.00  conjectures                             2
% 3.59/1.00  EPR                                     6
% 3.59/1.00  Horn                                    15
% 3.59/1.00  unary                                   4
% 3.59/1.00  binary                                  4
% 3.59/1.00  lits                                    56
% 3.59/1.00  lits eq                                 5
% 3.59/1.00  fd_pure                                 0
% 3.59/1.00  fd_pseudo                               0
% 3.59/1.00  fd_cond                                 0
% 3.59/1.00  fd_pseudo_cond                          3
% 3.59/1.00  AC symbols                              0
% 3.59/1.00  
% 3.59/1.00  ------ Schedule dynamic 5 is on 
% 3.59/1.00  
% 3.59/1.00  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" Time Limit: 10.
% 3.59/1.00  
% 3.59/1.00  
% 3.59/1.00  ------ 
% 3.59/1.00  Current options:
% 3.59/1.00  ------ 
% 3.59/1.00  
% 3.59/1.00  ------ Input Options
% 3.59/1.00  
% 3.59/1.00  --out_options                           all
% 3.59/1.00  --tptp_safe_out                         true
% 3.59/1.00  --problem_path                          ""
% 3.59/1.00  --include_path                          ""
% 3.59/1.00  --clausifier                            res/vclausify_rel
% 3.59/1.00  --clausifier_options                    --mode clausify
% 3.59/1.00  --stdin                                 false
% 3.59/1.00  --stats_out                             all
% 3.59/1.00  
% 3.59/1.00  ------ General Options
% 3.59/1.00  
% 3.59/1.00  --fof                                   false
% 3.59/1.00  --time_out_real                         305.
% 3.59/1.00  --time_out_virtual                      -1.
% 3.59/1.00  --symbol_type_check                     false
% 3.59/1.00  --clausify_out                          false
% 3.59/1.00  --sig_cnt_out                           false
% 3.59/1.00  --trig_cnt_out                          false
% 3.59/1.00  --trig_cnt_out_tolerance                1.
% 3.59/1.00  --trig_cnt_out_sk_spl                   false
% 3.59/1.00  --abstr_cl_out                          false
% 3.59/1.00  
% 3.59/1.00  ------ Global Options
% 3.59/1.00  
% 3.59/1.00  --schedule                              default
% 3.59/1.00  --add_important_lit                     false
% 3.59/1.00  --prop_solver_per_cl                    1000
% 3.59/1.00  --min_unsat_core                        false
% 3.59/1.00  --soft_assumptions                      false
% 3.59/1.00  --soft_lemma_size                       3
% 3.59/1.00  --prop_impl_unit_size                   0
% 3.59/1.00  --prop_impl_unit                        []
% 3.59/1.00  --share_sel_clauses                     true
% 3.59/1.00  --reset_solvers                         false
% 3.59/1.00  --bc_imp_inh                            [conj_cone]
% 3.59/1.00  --conj_cone_tolerance                   3.
% 3.59/1.00  --extra_neg_conj                        none
% 3.59/1.00  --large_theory_mode                     true
% 3.59/1.00  --prolific_symb_bound                   200
% 3.59/1.00  --lt_threshold                          2000
% 3.59/1.00  --clause_weak_htbl                      true
% 3.59/1.00  --gc_record_bc_elim                     false
% 3.59/1.00  
% 3.59/1.00  ------ Preprocessing Options
% 3.59/1.00  
% 3.59/1.00  --preprocessing_flag                    true
% 3.59/1.00  --time_out_prep_mult                    0.1
% 3.59/1.00  --splitting_mode                        input
% 3.59/1.00  --splitting_grd                         true
% 3.59/1.00  --splitting_cvd                         false
% 3.59/1.00  --splitting_cvd_svl                     false
% 3.59/1.00  --splitting_nvd                         32
% 3.59/1.00  --sub_typing                            true
% 3.59/1.00  --prep_gs_sim                           true
% 3.59/1.00  --prep_unflatten                        true
% 3.59/1.00  --prep_res_sim                          true
% 3.59/1.00  --prep_upred                            true
% 3.59/1.00  --prep_sem_filter                       exhaustive
% 3.59/1.00  --prep_sem_filter_out                   false
% 3.59/1.00  --pred_elim                             true
% 3.59/1.00  --res_sim_input                         true
% 3.59/1.00  --eq_ax_congr_red                       true
% 3.59/1.00  --pure_diseq_elim                       true
% 3.59/1.00  --brand_transform                       false
% 3.59/1.00  --non_eq_to_eq                          false
% 3.59/1.00  --prep_def_merge                        true
% 3.59/1.00  --prep_def_merge_prop_impl              false
% 3.59/1.00  --prep_def_merge_mbd                    true
% 3.59/1.00  --prep_def_merge_tr_red                 false
% 3.59/1.00  --prep_def_merge_tr_cl                  false
% 3.59/1.00  --smt_preprocessing                     true
% 3.59/1.00  --smt_ac_axioms                         fast
% 3.59/1.00  --preprocessed_out                      false
% 3.59/1.00  --preprocessed_stats                    false
% 3.59/1.00  
% 3.59/1.00  ------ Abstraction refinement Options
% 3.59/1.00  
% 3.59/1.00  --abstr_ref                             []
% 3.59/1.00  --abstr_ref_prep                        false
% 3.59/1.00  --abstr_ref_until_sat                   false
% 3.59/1.00  --abstr_ref_sig_restrict                funpre
% 3.59/1.00  --abstr_ref_af_restrict_to_split_sk     false
% 3.59/1.00  --abstr_ref_under                       []
% 3.59/1.00  
% 3.59/1.00  ------ SAT Options
% 3.59/1.00  
% 3.59/1.00  --sat_mode                              false
% 3.59/1.00  --sat_fm_restart_options                ""
% 3.59/1.00  --sat_gr_def                            false
% 3.59/1.00  --sat_epr_types                         true
% 3.59/1.00  --sat_non_cyclic_types                  false
% 3.59/1.00  --sat_finite_models                     false
% 3.59/1.00  --sat_fm_lemmas                         false
% 3.59/1.00  --sat_fm_prep                           false
% 3.59/1.00  --sat_fm_uc_incr                        true
% 3.59/1.00  --sat_out_model                         small
% 3.59/1.00  --sat_out_clauses                       false
% 3.59/1.00  
% 3.59/1.00  ------ QBF Options
% 3.59/1.00  
% 3.59/1.00  --qbf_mode                              false
% 3.59/1.00  --qbf_elim_univ                         false
% 3.59/1.00  --qbf_dom_inst                          none
% 3.59/1.00  --qbf_dom_pre_inst                      false
% 3.59/1.00  --qbf_sk_in                             false
% 3.59/1.00  --qbf_pred_elim                         true
% 3.59/1.00  --qbf_split                             512
% 3.59/1.00  
% 3.59/1.00  ------ BMC1 Options
% 3.59/1.00  
% 3.59/1.00  --bmc1_incremental                      false
% 3.59/1.00  --bmc1_axioms                           reachable_all
% 3.59/1.00  --bmc1_min_bound                        0
% 3.59/1.00  --bmc1_max_bound                        -1
% 3.59/1.00  --bmc1_max_bound_default                -1
% 3.59/1.00  --bmc1_symbol_reachability              true
% 3.59/1.00  --bmc1_property_lemmas                  false
% 3.59/1.00  --bmc1_k_induction                      false
% 3.59/1.00  --bmc1_non_equiv_states                 false
% 3.59/1.00  --bmc1_deadlock                         false
% 3.59/1.00  --bmc1_ucm                              false
% 3.59/1.00  --bmc1_add_unsat_core                   none
% 3.59/1.00  --bmc1_unsat_core_children              false
% 3.59/1.00  --bmc1_unsat_core_extrapolate_axioms    false
% 3.59/1.00  --bmc1_out_stat                         full
% 3.59/1.00  --bmc1_ground_init                      false
% 3.59/1.00  --bmc1_pre_inst_next_state              false
% 3.59/1.00  --bmc1_pre_inst_state                   false
% 3.59/1.00  --bmc1_pre_inst_reach_state             false
% 3.59/1.00  --bmc1_out_unsat_core                   false
% 3.59/1.00  --bmc1_aig_witness_out                  false
% 3.59/1.00  --bmc1_verbose                          false
% 3.59/1.00  --bmc1_dump_clauses_tptp                false
% 3.59/1.00  --bmc1_dump_unsat_core_tptp             false
% 3.59/1.00  --bmc1_dump_file                        -
% 3.59/1.00  --bmc1_ucm_expand_uc_limit              128
% 3.59/1.00  --bmc1_ucm_n_expand_iterations          6
% 3.59/1.00  --bmc1_ucm_extend_mode                  1
% 3.59/1.00  --bmc1_ucm_init_mode                    2
% 3.59/1.00  --bmc1_ucm_cone_mode                    none
% 3.59/1.00  --bmc1_ucm_reduced_relation_type        0
% 3.59/1.00  --bmc1_ucm_relax_model                  4
% 3.59/1.00  --bmc1_ucm_full_tr_after_sat            true
% 3.59/1.00  --bmc1_ucm_expand_neg_assumptions       false
% 3.59/1.00  --bmc1_ucm_layered_model                none
% 3.59/1.00  --bmc1_ucm_max_lemma_size               10
% 3.59/1.00  
% 3.59/1.00  ------ AIG Options
% 3.59/1.00  
% 3.59/1.00  --aig_mode                              false
% 3.59/1.00  
% 3.59/1.00  ------ Instantiation Options
% 3.59/1.00  
% 3.59/1.00  --instantiation_flag                    true
% 3.59/1.00  --inst_sos_flag                         false
% 3.59/1.00  --inst_sos_phase                        true
% 3.59/1.00  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 3.59/1.00  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 3.59/1.00  --inst_lit_sel_side                     none
% 3.59/1.00  --inst_solver_per_active                1400
% 3.59/1.00  --inst_solver_calls_frac                1.
% 3.59/1.00  --inst_passive_queue_type               priority_queues
% 3.59/1.00  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 3.59/1.00  --inst_passive_queues_freq              [25;2]
% 3.59/1.00  --inst_dismatching                      true
% 3.59/1.00  --inst_eager_unprocessed_to_passive     true
% 3.59/1.00  --inst_prop_sim_given                   true
% 3.59/1.00  --inst_prop_sim_new                     false
% 3.59/1.00  --inst_subs_new                         false
% 3.59/1.00  --inst_eq_res_simp                      false
% 3.59/1.00  --inst_subs_given                       false
% 3.59/1.00  --inst_orphan_elimination               true
% 3.59/1.00  --inst_learning_loop_flag               true
% 3.59/1.00  --inst_learning_start                   3000
% 3.59/1.00  --inst_learning_factor                  2
% 3.59/1.00  --inst_start_prop_sim_after_learn       3
% 3.59/1.00  --inst_sel_renew                        solver
% 3.59/1.00  --inst_lit_activity_flag                true
% 3.59/1.00  --inst_restr_to_given                   false
% 3.59/1.00  --inst_activity_threshold               500
% 3.59/1.00  --inst_out_proof                        true
% 3.59/1.00  
% 3.59/1.00  ------ Resolution Options
% 3.59/1.00  
% 3.59/1.00  --resolution_flag                       false
% 3.59/1.00  --res_lit_sel                           adaptive
% 3.59/1.00  --res_lit_sel_side                      none
% 3.59/1.00  --res_ordering                          kbo
% 3.59/1.00  --res_to_prop_solver                    active
% 3.59/1.00  --res_prop_simpl_new                    false
% 3.59/1.00  --res_prop_simpl_given                  true
% 3.59/1.00  --res_passive_queue_type                priority_queues
% 3.59/1.00  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 3.59/1.00  --res_passive_queues_freq               [15;5]
% 3.59/1.00  --res_forward_subs                      full
% 3.59/1.00  --res_backward_subs                     full
% 3.59/1.00  --res_forward_subs_resolution           true
% 3.59/1.00  --res_backward_subs_resolution          true
% 3.59/1.00  --res_orphan_elimination                true
% 3.59/1.00  --res_time_limit                        2.
% 3.59/1.00  --res_out_proof                         true
% 3.59/1.00  
% 3.59/1.00  ------ Superposition Options
% 3.59/1.00  
% 3.59/1.00  --superposition_flag                    true
% 3.59/1.00  --sup_passive_queue_type                priority_queues
% 3.59/1.00  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 3.59/1.00  --sup_passive_queues_freq               [8;1;4]
% 3.59/1.00  --demod_completeness_check              fast
% 3.59/1.00  --demod_use_ground                      true
% 3.59/1.00  --sup_to_prop_solver                    passive
% 3.59/1.00  --sup_prop_simpl_new                    true
% 3.59/1.00  --sup_prop_simpl_given                  true
% 3.59/1.00  --sup_fun_splitting                     false
% 3.59/1.00  --sup_smt_interval                      50000
% 3.59/1.00  
% 3.59/1.00  ------ Superposition Simplification Setup
% 3.59/1.00  
% 3.59/1.00  --sup_indices_passive                   []
% 3.59/1.00  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.59/1.00  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.59/1.00  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.59/1.00  --sup_full_triv                         [TrivRules;PropSubs]
% 3.59/1.00  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.59/1.00  --sup_full_bw                           [BwDemod]
% 3.59/1.00  --sup_immed_triv                        [TrivRules]
% 3.59/1.00  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 3.59/1.00  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.59/1.00  --sup_immed_bw_main                     []
% 3.59/1.00  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 3.59/1.00  --sup_input_triv                        [Unflattening;TrivRules]
% 3.59/1.00  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.59/1.00  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 3.59/1.00  
% 3.59/1.00  ------ Combination Options
% 3.59/1.00  
% 3.59/1.00  --comb_res_mult                         3
% 3.59/1.00  --comb_sup_mult                         2
% 3.59/1.00  --comb_inst_mult                        10
% 3.59/1.00  
% 3.59/1.00  ------ Debug Options
% 3.59/1.00  
% 3.59/1.00  --dbg_backtrace                         false
% 3.59/1.00  --dbg_dump_prop_clauses                 false
% 3.59/1.00  --dbg_dump_prop_clauses_file            -
% 3.59/1.00  --dbg_out_stat                          false
% 3.59/1.00  
% 3.59/1.00  
% 3.59/1.00  
% 3.59/1.00  
% 3.59/1.00  ------ Proving...
% 3.59/1.00  
% 3.59/1.00  
% 3.59/1.00  % SZS status Theorem for theBenchmark.p
% 3.59/1.00  
% 3.59/1.00  % SZS output start CNFRefutation for theBenchmark.p
% 3.59/1.00  
% 3.59/1.00  fof(f12,conjecture,(
% 3.59/1.00    ! [X0] : ((l1_orders_2(X0) & v1_yellow_0(X0) & v5_orders_2(X0) & v4_orders_2(X0) & v3_orders_2(X0) & ~v2_struct_0(X0)) => ! [X1] : ((m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & v13_waybel_0(X1,X0) & v2_waybel_0(X1,X0) & ~v1_xboole_0(X1)) => (v1_subset_1(X1,u1_struct_0(X0)) <=> ~r2_hidden(k3_yellow_0(X0),X1))))),
% 3.59/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.59/1.00  
% 3.59/1.00  fof(f13,negated_conjecture,(
% 3.59/1.00    ~! [X0] : ((l1_orders_2(X0) & v1_yellow_0(X0) & v5_orders_2(X0) & v4_orders_2(X0) & v3_orders_2(X0) & ~v2_struct_0(X0)) => ! [X1] : ((m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & v13_waybel_0(X1,X0) & v2_waybel_0(X1,X0) & ~v1_xboole_0(X1)) => (v1_subset_1(X1,u1_struct_0(X0)) <=> ~r2_hidden(k3_yellow_0(X0),X1))))),
% 3.59/1.00    inference(negated_conjecture,[],[f12])).
% 3.59/1.00  
% 3.59/1.00  fof(f14,plain,(
% 3.59/1.00    ~! [X0] : ((l1_orders_2(X0) & v1_yellow_0(X0) & v5_orders_2(X0) & v4_orders_2(X0) & v3_orders_2(X0) & ~v2_struct_0(X0)) => ! [X1] : ((m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & v13_waybel_0(X1,X0) & ~v1_xboole_0(X1)) => (v1_subset_1(X1,u1_struct_0(X0)) <=> ~r2_hidden(k3_yellow_0(X0),X1))))),
% 3.59/1.00    inference(pure_predicate_removal,[],[f13])).
% 3.59/1.00  
% 3.59/1.00  fof(f15,plain,(
% 3.59/1.00    ~! [X0] : ((l1_orders_2(X0) & v1_yellow_0(X0) & v5_orders_2(X0) & v3_orders_2(X0) & ~v2_struct_0(X0)) => ! [X1] : ((m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & v13_waybel_0(X1,X0) & ~v1_xboole_0(X1)) => (v1_subset_1(X1,u1_struct_0(X0)) <=> ~r2_hidden(k3_yellow_0(X0),X1))))),
% 3.59/1.00    inference(pure_predicate_removal,[],[f14])).
% 3.59/1.00  
% 3.59/1.00  fof(f16,plain,(
% 3.59/1.00    ~! [X0] : ((l1_orders_2(X0) & v1_yellow_0(X0) & v5_orders_2(X0) & ~v2_struct_0(X0)) => ! [X1] : ((m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & v13_waybel_0(X1,X0) & ~v1_xboole_0(X1)) => (v1_subset_1(X1,u1_struct_0(X0)) <=> ~r2_hidden(k3_yellow_0(X0),X1))))),
% 3.59/1.00    inference(pure_predicate_removal,[],[f15])).
% 3.59/1.00  
% 3.59/1.00  fof(f30,plain,(
% 3.59/1.00    ? [X0] : (? [X1] : ((v1_subset_1(X1,u1_struct_0(X0)) <~> ~r2_hidden(k3_yellow_0(X0),X1)) & (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & v13_waybel_0(X1,X0) & ~v1_xboole_0(X1))) & (l1_orders_2(X0) & v1_yellow_0(X0) & v5_orders_2(X0) & ~v2_struct_0(X0)))),
% 3.59/1.00    inference(ennf_transformation,[],[f16])).
% 3.59/1.00  
% 3.59/1.00  fof(f31,plain,(
% 3.59/1.00    ? [X0] : (? [X1] : ((v1_subset_1(X1,u1_struct_0(X0)) <~> ~r2_hidden(k3_yellow_0(X0),X1)) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & v13_waybel_0(X1,X0) & ~v1_xboole_0(X1)) & l1_orders_2(X0) & v1_yellow_0(X0) & v5_orders_2(X0) & ~v2_struct_0(X0))),
% 3.59/1.00    inference(flattening,[],[f30])).
% 3.59/1.00  
% 3.59/1.00  fof(f44,plain,(
% 3.59/1.00    ? [X0] : (? [X1] : (((r2_hidden(k3_yellow_0(X0),X1) | ~v1_subset_1(X1,u1_struct_0(X0))) & (~r2_hidden(k3_yellow_0(X0),X1) | v1_subset_1(X1,u1_struct_0(X0)))) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & v13_waybel_0(X1,X0) & ~v1_xboole_0(X1)) & l1_orders_2(X0) & v1_yellow_0(X0) & v5_orders_2(X0) & ~v2_struct_0(X0))),
% 3.59/1.00    inference(nnf_transformation,[],[f31])).
% 3.59/1.00  
% 3.59/1.00  fof(f45,plain,(
% 3.59/1.00    ? [X0] : (? [X1] : ((r2_hidden(k3_yellow_0(X0),X1) | ~v1_subset_1(X1,u1_struct_0(X0))) & (~r2_hidden(k3_yellow_0(X0),X1) | v1_subset_1(X1,u1_struct_0(X0))) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & v13_waybel_0(X1,X0) & ~v1_xboole_0(X1)) & l1_orders_2(X0) & v1_yellow_0(X0) & v5_orders_2(X0) & ~v2_struct_0(X0))),
% 3.59/1.00    inference(flattening,[],[f44])).
% 3.59/1.00  
% 3.59/1.00  fof(f47,plain,(
% 3.59/1.00    ( ! [X0] : (? [X1] : ((r2_hidden(k3_yellow_0(X0),X1) | ~v1_subset_1(X1,u1_struct_0(X0))) & (~r2_hidden(k3_yellow_0(X0),X1) | v1_subset_1(X1,u1_struct_0(X0))) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & v13_waybel_0(X1,X0) & ~v1_xboole_0(X1)) => ((r2_hidden(k3_yellow_0(X0),sK4) | ~v1_subset_1(sK4,u1_struct_0(X0))) & (~r2_hidden(k3_yellow_0(X0),sK4) | v1_subset_1(sK4,u1_struct_0(X0))) & m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(X0))) & v13_waybel_0(sK4,X0) & ~v1_xboole_0(sK4))) )),
% 3.59/1.00    introduced(choice_axiom,[])).
% 3.59/1.00  
% 3.59/1.00  fof(f46,plain,(
% 3.59/1.00    ? [X0] : (? [X1] : ((r2_hidden(k3_yellow_0(X0),X1) | ~v1_subset_1(X1,u1_struct_0(X0))) & (~r2_hidden(k3_yellow_0(X0),X1) | v1_subset_1(X1,u1_struct_0(X0))) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & v13_waybel_0(X1,X0) & ~v1_xboole_0(X1)) & l1_orders_2(X0) & v1_yellow_0(X0) & v5_orders_2(X0) & ~v2_struct_0(X0)) => (? [X1] : ((r2_hidden(k3_yellow_0(sK3),X1) | ~v1_subset_1(X1,u1_struct_0(sK3))) & (~r2_hidden(k3_yellow_0(sK3),X1) | v1_subset_1(X1,u1_struct_0(sK3))) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK3))) & v13_waybel_0(X1,sK3) & ~v1_xboole_0(X1)) & l1_orders_2(sK3) & v1_yellow_0(sK3) & v5_orders_2(sK3) & ~v2_struct_0(sK3))),
% 3.59/1.00    introduced(choice_axiom,[])).
% 3.59/1.00  
% 3.59/1.00  fof(f48,plain,(
% 3.59/1.00    ((r2_hidden(k3_yellow_0(sK3),sK4) | ~v1_subset_1(sK4,u1_struct_0(sK3))) & (~r2_hidden(k3_yellow_0(sK3),sK4) | v1_subset_1(sK4,u1_struct_0(sK3))) & m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(sK3))) & v13_waybel_0(sK4,sK3) & ~v1_xboole_0(sK4)) & l1_orders_2(sK3) & v1_yellow_0(sK3) & v5_orders_2(sK3) & ~v2_struct_0(sK3)),
% 3.59/1.00    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3,sK4])],[f45,f47,f46])).
% 3.59/1.00  
% 3.59/1.00  fof(f76,plain,(
% 3.59/1.00    m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(sK3)))),
% 3.59/1.00    inference(cnf_transformation,[],[f48])).
% 3.59/1.00  
% 3.59/1.00  fof(f6,axiom,(
% 3.59/1.00    ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) <=> r1_tarski(X0,X1))),
% 3.59/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.59/1.00  
% 3.59/1.00  fof(f37,plain,(
% 3.59/1.00    ! [X0,X1] : ((m1_subset_1(X0,k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1)) & (r1_tarski(X0,X1) | ~m1_subset_1(X0,k1_zfmisc_1(X1))))),
% 3.59/1.00    inference(nnf_transformation,[],[f6])).
% 3.59/1.00  
% 3.59/1.00  fof(f57,plain,(
% 3.59/1.00    ( ! [X0,X1] : (r1_tarski(X0,X1) | ~m1_subset_1(X0,k1_zfmisc_1(X1))) )),
% 3.59/1.00    inference(cnf_transformation,[],[f37])).
% 3.59/1.00  
% 3.59/1.00  fof(f3,axiom,(
% 3.59/1.00    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => ! [X2] : (r2_hidden(X2,X1) => r2_hidden(X2,X0)))),
% 3.59/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.59/1.00  
% 3.59/1.00  fof(f18,plain,(
% 3.59/1.00    ! [X0,X1] : (! [X2] : (r2_hidden(X2,X0) | ~r2_hidden(X2,X1)) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 3.59/1.00    inference(ennf_transformation,[],[f3])).
% 3.59/1.00  
% 3.59/1.00  fof(f54,plain,(
% 3.59/1.00    ( ! [X2,X0,X1] : (r2_hidden(X2,X0) | ~r2_hidden(X2,X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 3.59/1.00    inference(cnf_transformation,[],[f18])).
% 3.59/1.00  
% 3.59/1.00  fof(f58,plain,(
% 3.59/1.00    ( ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1)) )),
% 3.59/1.00    inference(cnf_transformation,[],[f37])).
% 3.59/1.00  
% 3.59/1.00  fof(f1,axiom,(
% 3.59/1.00    ! [X0,X1] : (! [X2] : (r2_hidden(X2,X0) <=> r2_hidden(X2,X1)) => X0 = X1)),
% 3.59/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.59/1.00  
% 3.59/1.00  fof(f17,plain,(
% 3.59/1.00    ! [X0,X1] : (X0 = X1 | ? [X2] : (r2_hidden(X2,X0) <~> r2_hidden(X2,X1)))),
% 3.59/1.00    inference(ennf_transformation,[],[f1])).
% 3.59/1.00  
% 3.59/1.00  fof(f32,plain,(
% 3.59/1.00    ! [X0,X1] : (X0 = X1 | ? [X2] : ((~r2_hidden(X2,X1) | ~r2_hidden(X2,X0)) & (r2_hidden(X2,X1) | r2_hidden(X2,X0))))),
% 3.59/1.00    inference(nnf_transformation,[],[f17])).
% 3.59/1.00  
% 3.59/1.00  fof(f33,plain,(
% 3.59/1.00    ! [X1,X0] : (? [X2] : ((~r2_hidden(X2,X1) | ~r2_hidden(X2,X0)) & (r2_hidden(X2,X1) | r2_hidden(X2,X0))) => ((~r2_hidden(sK0(X0,X1),X1) | ~r2_hidden(sK0(X0,X1),X0)) & (r2_hidden(sK0(X0,X1),X1) | r2_hidden(sK0(X0,X1),X0))))),
% 3.59/1.00    introduced(choice_axiom,[])).
% 3.59/1.00  
% 3.59/1.00  fof(f34,plain,(
% 3.59/1.00    ! [X0,X1] : (X0 = X1 | ((~r2_hidden(sK0(X0,X1),X1) | ~r2_hidden(sK0(X0,X1),X0)) & (r2_hidden(sK0(X0,X1),X1) | r2_hidden(sK0(X0,X1),X0))))),
% 3.59/1.00    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f32,f33])).
% 3.59/1.00  
% 3.59/1.00  fof(f49,plain,(
% 3.59/1.00    ( ! [X0,X1] : (X0 = X1 | r2_hidden(sK0(X0,X1),X1) | r2_hidden(sK0(X0,X1),X0)) )),
% 3.59/1.00    inference(cnf_transformation,[],[f34])).
% 3.59/1.00  
% 3.59/1.00  fof(f4,axiom,(
% 3.59/1.00    ! [X0,X1] : (r2_hidden(X0,X1) => m1_subset_1(X0,X1))),
% 3.59/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.59/1.00  
% 3.59/1.00  fof(f19,plain,(
% 3.59/1.00    ! [X0,X1] : (m1_subset_1(X0,X1) | ~r2_hidden(X0,X1))),
% 3.59/1.00    inference(ennf_transformation,[],[f4])).
% 3.59/1.00  
% 3.59/1.00  fof(f55,plain,(
% 3.59/1.00    ( ! [X0,X1] : (m1_subset_1(X0,X1) | ~r2_hidden(X0,X1)) )),
% 3.59/1.00    inference(cnf_transformation,[],[f19])).
% 3.59/1.00  
% 3.59/1.00  fof(f5,axiom,(
% 3.59/1.00    ! [X0,X1] : (m1_subset_1(X0,X1) => (r2_hidden(X0,X1) | v1_xboole_0(X1)))),
% 3.59/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.59/1.00  
% 3.59/1.00  fof(f20,plain,(
% 3.59/1.00    ! [X0,X1] : ((r2_hidden(X0,X1) | v1_xboole_0(X1)) | ~m1_subset_1(X0,X1))),
% 3.59/1.00    inference(ennf_transformation,[],[f5])).
% 3.59/1.00  
% 3.59/1.00  fof(f21,plain,(
% 3.59/1.00    ! [X0,X1] : (r2_hidden(X0,X1) | v1_xboole_0(X1) | ~m1_subset_1(X0,X1))),
% 3.59/1.00    inference(flattening,[],[f20])).
% 3.59/1.00  
% 3.59/1.00  fof(f56,plain,(
% 3.59/1.00    ( ! [X0,X1] : (r2_hidden(X0,X1) | v1_xboole_0(X1) | ~m1_subset_1(X0,X1)) )),
% 3.59/1.00    inference(cnf_transformation,[],[f21])).
% 3.59/1.00  
% 3.59/1.00  fof(f74,plain,(
% 3.59/1.00    ~v1_xboole_0(sK4)),
% 3.59/1.00    inference(cnf_transformation,[],[f48])).
% 3.59/1.00  
% 3.59/1.00  fof(f11,axiom,(
% 3.59/1.00    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => (v1_subset_1(X1,X0) <=> X0 != X1))),
% 3.59/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.59/1.00  
% 3.59/1.00  fof(f29,plain,(
% 3.59/1.00    ! [X0,X1] : ((v1_subset_1(X1,X0) <=> X0 != X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 3.59/1.00    inference(ennf_transformation,[],[f11])).
% 3.59/1.00  
% 3.59/1.00  fof(f43,plain,(
% 3.59/1.00    ! [X0,X1] : (((v1_subset_1(X1,X0) | X0 = X1) & (X0 != X1 | ~v1_subset_1(X1,X0))) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 3.59/1.00    inference(nnf_transformation,[],[f29])).
% 3.59/1.00  
% 3.59/1.00  fof(f69,plain,(
% 3.59/1.00    ( ! [X0,X1] : (v1_subset_1(X1,X0) | X0 = X1 | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 3.59/1.00    inference(cnf_transformation,[],[f43])).
% 3.59/1.00  
% 3.59/1.00  fof(f78,plain,(
% 3.59/1.00    r2_hidden(k3_yellow_0(sK3),sK4) | ~v1_subset_1(sK4,u1_struct_0(sK3))),
% 3.59/1.00    inference(cnf_transformation,[],[f48])).
% 3.59/1.00  
% 3.59/1.00  fof(f68,plain,(
% 3.59/1.00    ( ! [X0,X1] : (X0 != X1 | ~v1_subset_1(X1,X0) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 3.59/1.00    inference(cnf_transformation,[],[f43])).
% 3.59/1.00  
% 3.59/1.00  fof(f81,plain,(
% 3.59/1.00    ( ! [X1] : (~v1_subset_1(X1,X1) | ~m1_subset_1(X1,k1_zfmisc_1(X1))) )),
% 3.59/1.00    inference(equality_resolution,[],[f68])).
% 3.59/1.00  
% 3.59/1.00  fof(f77,plain,(
% 3.59/1.00    ~r2_hidden(k3_yellow_0(sK3),sK4) | v1_subset_1(sK4,u1_struct_0(sK3))),
% 3.59/1.00    inference(cnf_transformation,[],[f48])).
% 3.59/1.00  
% 3.59/1.00  fof(f73,plain,(
% 3.59/1.00    l1_orders_2(sK3)),
% 3.59/1.00    inference(cnf_transformation,[],[f48])).
% 3.59/1.00  
% 3.59/1.00  fof(f8,axiom,(
% 3.59/1.00    ! [X0] : (l1_orders_2(X0) => m1_subset_1(k3_yellow_0(X0),u1_struct_0(X0)))),
% 3.59/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.59/1.00  
% 3.59/1.00  fof(f24,plain,(
% 3.59/1.00    ! [X0] : (m1_subset_1(k3_yellow_0(X0),u1_struct_0(X0)) | ~l1_orders_2(X0))),
% 3.59/1.00    inference(ennf_transformation,[],[f8])).
% 3.59/1.00  
% 3.59/1.00  fof(f60,plain,(
% 3.59/1.00    ( ! [X0] : (m1_subset_1(k3_yellow_0(X0),u1_struct_0(X0)) | ~l1_orders_2(X0)) )),
% 3.59/1.00    inference(cnf_transformation,[],[f24])).
% 3.59/1.00  
% 3.59/1.00  fof(f2,axiom,(
% 3.59/1.00    ! [X0,X1] : (X0 = X1 <=> (r1_tarski(X1,X0) & r1_tarski(X0,X1)))),
% 3.59/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.59/1.00  
% 3.59/1.00  fof(f35,plain,(
% 3.59/1.00    ! [X0,X1] : ((X0 = X1 | (~r1_tarski(X1,X0) | ~r1_tarski(X0,X1))) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 3.59/1.00    inference(nnf_transformation,[],[f2])).
% 3.59/1.00  
% 3.59/1.00  fof(f36,plain,(
% 3.59/1.00    ! [X0,X1] : ((X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 3.59/1.00    inference(flattening,[],[f35])).
% 3.59/1.00  
% 3.59/1.00  fof(f51,plain,(
% 3.59/1.00    ( ! [X0,X1] : (r1_tarski(X0,X1) | X0 != X1) )),
% 3.59/1.00    inference(cnf_transformation,[],[f36])).
% 3.59/1.00  
% 3.59/1.00  fof(f80,plain,(
% 3.59/1.00    ( ! [X1] : (r1_tarski(X1,X1)) )),
% 3.59/1.00    inference(equality_resolution,[],[f51])).
% 3.59/1.00  
% 3.59/1.00  fof(f10,axiom,(
% 3.59/1.00    ! [X0] : (l1_orders_2(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => (v13_waybel_0(X1,X0) <=> ! [X2] : (m1_subset_1(X2,u1_struct_0(X0)) => ! [X3] : (m1_subset_1(X3,u1_struct_0(X0)) => ((r1_orders_2(X0,X2,X3) & r2_hidden(X2,X1)) => r2_hidden(X3,X1)))))))),
% 3.59/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.59/1.00  
% 3.59/1.00  fof(f27,plain,(
% 3.59/1.00    ! [X0] : (! [X1] : ((v13_waybel_0(X1,X0) <=> ! [X2] : (! [X3] : ((r2_hidden(X3,X1) | (~r1_orders_2(X0,X2,X3) | ~r2_hidden(X2,X1))) | ~m1_subset_1(X3,u1_struct_0(X0))) | ~m1_subset_1(X2,u1_struct_0(X0)))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_orders_2(X0))),
% 3.59/1.00    inference(ennf_transformation,[],[f10])).
% 3.59/1.00  
% 3.59/1.00  fof(f28,plain,(
% 3.59/1.00    ! [X0] : (! [X1] : ((v13_waybel_0(X1,X0) <=> ! [X2] : (! [X3] : (r2_hidden(X3,X1) | ~r1_orders_2(X0,X2,X3) | ~r2_hidden(X2,X1) | ~m1_subset_1(X3,u1_struct_0(X0))) | ~m1_subset_1(X2,u1_struct_0(X0)))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_orders_2(X0))),
% 3.59/1.00    inference(flattening,[],[f27])).
% 3.59/1.00  
% 3.59/1.00  fof(f38,plain,(
% 3.59/1.00    ! [X0] : (! [X1] : (((v13_waybel_0(X1,X0) | ? [X2] : (? [X3] : (~r2_hidden(X3,X1) & r1_orders_2(X0,X2,X3) & r2_hidden(X2,X1) & m1_subset_1(X3,u1_struct_0(X0))) & m1_subset_1(X2,u1_struct_0(X0)))) & (! [X2] : (! [X3] : (r2_hidden(X3,X1) | ~r1_orders_2(X0,X2,X3) | ~r2_hidden(X2,X1) | ~m1_subset_1(X3,u1_struct_0(X0))) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~v13_waybel_0(X1,X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_orders_2(X0))),
% 3.59/1.00    inference(nnf_transformation,[],[f28])).
% 3.59/1.00  
% 3.59/1.00  fof(f39,plain,(
% 3.59/1.00    ! [X0] : (! [X1] : (((v13_waybel_0(X1,X0) | ? [X2] : (? [X3] : (~r2_hidden(X3,X1) & r1_orders_2(X0,X2,X3) & r2_hidden(X2,X1) & m1_subset_1(X3,u1_struct_0(X0))) & m1_subset_1(X2,u1_struct_0(X0)))) & (! [X4] : (! [X5] : (r2_hidden(X5,X1) | ~r1_orders_2(X0,X4,X5) | ~r2_hidden(X4,X1) | ~m1_subset_1(X5,u1_struct_0(X0))) | ~m1_subset_1(X4,u1_struct_0(X0))) | ~v13_waybel_0(X1,X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_orders_2(X0))),
% 3.59/1.00    inference(rectify,[],[f38])).
% 3.59/1.00  
% 3.59/1.00  fof(f41,plain,(
% 3.59/1.00    ( ! [X2] : (! [X1,X0] : (? [X3] : (~r2_hidden(X3,X1) & r1_orders_2(X0,X2,X3) & r2_hidden(X2,X1) & m1_subset_1(X3,u1_struct_0(X0))) => (~r2_hidden(sK2(X0,X1),X1) & r1_orders_2(X0,X2,sK2(X0,X1)) & r2_hidden(X2,X1) & m1_subset_1(sK2(X0,X1),u1_struct_0(X0))))) )),
% 3.59/1.00    introduced(choice_axiom,[])).
% 3.59/1.00  
% 3.59/1.00  fof(f40,plain,(
% 3.59/1.00    ! [X1,X0] : (? [X2] : (? [X3] : (~r2_hidden(X3,X1) & r1_orders_2(X0,X2,X3) & r2_hidden(X2,X1) & m1_subset_1(X3,u1_struct_0(X0))) & m1_subset_1(X2,u1_struct_0(X0))) => (? [X3] : (~r2_hidden(X3,X1) & r1_orders_2(X0,sK1(X0,X1),X3) & r2_hidden(sK1(X0,X1),X1) & m1_subset_1(X3,u1_struct_0(X0))) & m1_subset_1(sK1(X0,X1),u1_struct_0(X0))))),
% 3.59/1.00    introduced(choice_axiom,[])).
% 3.59/1.00  
% 3.59/1.00  fof(f42,plain,(
% 3.59/1.00    ! [X0] : (! [X1] : (((v13_waybel_0(X1,X0) | ((~r2_hidden(sK2(X0,X1),X1) & r1_orders_2(X0,sK1(X0,X1),sK2(X0,X1)) & r2_hidden(sK1(X0,X1),X1) & m1_subset_1(sK2(X0,X1),u1_struct_0(X0))) & m1_subset_1(sK1(X0,X1),u1_struct_0(X0)))) & (! [X4] : (! [X5] : (r2_hidden(X5,X1) | ~r1_orders_2(X0,X4,X5) | ~r2_hidden(X4,X1) | ~m1_subset_1(X5,u1_struct_0(X0))) | ~m1_subset_1(X4,u1_struct_0(X0))) | ~v13_waybel_0(X1,X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_orders_2(X0))),
% 3.59/1.00    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1,sK2])],[f39,f41,f40])).
% 3.59/1.00  
% 3.59/1.00  fof(f62,plain,(
% 3.59/1.00    ( ! [X4,X0,X5,X1] : (r2_hidden(X5,X1) | ~r1_orders_2(X0,X4,X5) | ~r2_hidden(X4,X1) | ~m1_subset_1(X5,u1_struct_0(X0)) | ~m1_subset_1(X4,u1_struct_0(X0)) | ~v13_waybel_0(X1,X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_orders_2(X0)) )),
% 3.59/1.00    inference(cnf_transformation,[],[f42])).
% 3.59/1.00  
% 3.59/1.00  fof(f9,axiom,(
% 3.59/1.00    ! [X0] : ((l1_orders_2(X0) & v1_yellow_0(X0) & v5_orders_2(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,u1_struct_0(X0)) => r1_orders_2(X0,k3_yellow_0(X0),X1)))),
% 3.59/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.59/1.00  
% 3.59/1.00  fof(f25,plain,(
% 3.59/1.00    ! [X0] : (! [X1] : (r1_orders_2(X0,k3_yellow_0(X0),X1) | ~m1_subset_1(X1,u1_struct_0(X0))) | (~l1_orders_2(X0) | ~v1_yellow_0(X0) | ~v5_orders_2(X0) | v2_struct_0(X0)))),
% 3.59/1.00    inference(ennf_transformation,[],[f9])).
% 3.59/1.00  
% 3.59/1.00  fof(f26,plain,(
% 3.59/1.00    ! [X0] : (! [X1] : (r1_orders_2(X0,k3_yellow_0(X0),X1) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~l1_orders_2(X0) | ~v1_yellow_0(X0) | ~v5_orders_2(X0) | v2_struct_0(X0))),
% 3.59/1.00    inference(flattening,[],[f25])).
% 3.59/1.00  
% 3.59/1.00  fof(f61,plain,(
% 3.59/1.00    ( ! [X0,X1] : (r1_orders_2(X0,k3_yellow_0(X0),X1) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_orders_2(X0) | ~v1_yellow_0(X0) | ~v5_orders_2(X0) | v2_struct_0(X0)) )),
% 3.59/1.00    inference(cnf_transformation,[],[f26])).
% 3.59/1.00  
% 3.59/1.00  fof(f72,plain,(
% 3.59/1.00    v1_yellow_0(sK3)),
% 3.59/1.00    inference(cnf_transformation,[],[f48])).
% 3.59/1.00  
% 3.59/1.00  fof(f70,plain,(
% 3.59/1.00    ~v2_struct_0(sK3)),
% 3.59/1.00    inference(cnf_transformation,[],[f48])).
% 3.59/1.00  
% 3.59/1.00  fof(f71,plain,(
% 3.59/1.00    v5_orders_2(sK3)),
% 3.59/1.00    inference(cnf_transformation,[],[f48])).
% 3.59/1.00  
% 3.59/1.00  fof(f75,plain,(
% 3.59/1.00    v13_waybel_0(sK4,sK3)),
% 3.59/1.00    inference(cnf_transformation,[],[f48])).
% 3.59/1.00  
% 3.59/1.00  fof(f50,plain,(
% 3.59/1.00    ( ! [X0,X1] : (X0 = X1 | ~r2_hidden(sK0(X0,X1),X1) | ~r2_hidden(sK0(X0,X1),X0)) )),
% 3.59/1.00    inference(cnf_transformation,[],[f34])).
% 3.59/1.00  
% 3.59/1.00  cnf(c_23,negated_conjecture,
% 3.59/1.00      ( m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(sK3))) ),
% 3.59/1.00      inference(cnf_transformation,[],[f76]) ).
% 3.59/1.00  
% 3.59/1.00  cnf(c_1368,plain,
% 3.59/1.00      ( m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(sK3))) = iProver_top ),
% 3.59/1.00      inference(predicate_to_equality,[status(thm)],[c_23]) ).
% 3.59/1.00  
% 3.59/1.00  cnf(c_9,plain,
% 3.59/1.00      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1)) | r1_tarski(X0,X1) ),
% 3.59/1.00      inference(cnf_transformation,[],[f57]) ).
% 3.59/1.00  
% 3.59/1.00  cnf(c_1370,plain,
% 3.59/1.00      ( m1_subset_1(X0,k1_zfmisc_1(X1)) != iProver_top
% 3.59/1.00      | r1_tarski(X0,X1) = iProver_top ),
% 3.59/1.00      inference(predicate_to_equality,[status(thm)],[c_9]) ).
% 3.59/1.00  
% 3.59/1.00  cnf(c_1814,plain,
% 3.59/1.00      ( r1_tarski(sK4,u1_struct_0(sK3)) = iProver_top ),
% 3.59/1.00      inference(superposition,[status(thm)],[c_1368,c_1370]) ).
% 3.59/1.00  
% 3.59/1.00  cnf(c_5,plain,
% 3.59/1.00      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
% 3.59/1.00      | ~ r2_hidden(X2,X0)
% 3.59/1.00      | r2_hidden(X2,X1) ),
% 3.59/1.00      inference(cnf_transformation,[],[f54]) ).
% 3.59/1.00  
% 3.59/1.00  cnf(c_8,plain,
% 3.59/1.00      ( m1_subset_1(X0,k1_zfmisc_1(X1)) | ~ r1_tarski(X0,X1) ),
% 3.59/1.00      inference(cnf_transformation,[],[f58]) ).
% 3.59/1.00  
% 3.59/1.00  cnf(c_224,plain,
% 3.59/1.00      ( ~ r1_tarski(X0,X1) | m1_subset_1(X0,k1_zfmisc_1(X1)) ),
% 3.59/1.00      inference(prop_impl,[status(thm)],[c_8]) ).
% 3.59/1.00  
% 3.59/1.00  cnf(c_225,plain,
% 3.59/1.00      ( m1_subset_1(X0,k1_zfmisc_1(X1)) | ~ r1_tarski(X0,X1) ),
% 3.59/1.00      inference(renaming,[status(thm)],[c_224]) ).
% 3.59/1.00  
% 3.59/1.00  cnf(c_288,plain,
% 3.59/1.00      ( ~ r1_tarski(X0,X1) | ~ r2_hidden(X2,X0) | r2_hidden(X2,X1) ),
% 3.59/1.00      inference(bin_hyper_res,[status(thm)],[c_5,c_225]) ).
% 3.59/1.00  
% 3.59/1.00  cnf(c_1366,plain,
% 3.59/1.00      ( r1_tarski(X0,X1) != iProver_top
% 3.59/1.00      | r2_hidden(X2,X0) != iProver_top
% 3.59/1.00      | r2_hidden(X2,X1) = iProver_top ),
% 3.59/1.00      inference(predicate_to_equality,[status(thm)],[c_288]) ).
% 3.59/1.00  
% 3.59/1.00  cnf(c_3102,plain,
% 3.59/1.00      ( r2_hidden(X0,u1_struct_0(sK3)) = iProver_top
% 3.59/1.00      | r2_hidden(X0,sK4) != iProver_top ),
% 3.59/1.00      inference(superposition,[status(thm)],[c_1814,c_1366]) ).
% 3.59/1.00  
% 3.59/1.00  cnf(c_1,plain,
% 3.59/1.00      ( r2_hidden(sK0(X0,X1),X1) | r2_hidden(sK0(X0,X1),X0) | X1 = X0 ),
% 3.59/1.00      inference(cnf_transformation,[],[f49]) ).
% 3.59/1.00  
% 3.59/1.00  cnf(c_1375,plain,
% 3.59/1.00      ( X0 = X1
% 3.59/1.00      | r2_hidden(sK0(X1,X0),X0) = iProver_top
% 3.59/1.00      | r2_hidden(sK0(X1,X0),X1) = iProver_top ),
% 3.59/1.00      inference(predicate_to_equality,[status(thm)],[c_1]) ).
% 3.59/1.00  
% 3.59/1.00  cnf(c_6,plain,
% 3.59/1.00      ( m1_subset_1(X0,X1) | ~ r2_hidden(X0,X1) ),
% 3.59/1.00      inference(cnf_transformation,[],[f55]) ).
% 3.59/1.00  
% 3.59/1.00  cnf(c_1372,plain,
% 3.59/1.00      ( m1_subset_1(X0,X1) = iProver_top
% 3.59/1.00      | r2_hidden(X0,X1) != iProver_top ),
% 3.59/1.00      inference(predicate_to_equality,[status(thm)],[c_6]) ).
% 3.59/1.00  
% 3.59/1.00  cnf(c_2205,plain,
% 3.59/1.00      ( X0 = X1
% 3.59/1.00      | m1_subset_1(sK0(X0,X1),X0) = iProver_top
% 3.59/1.00      | r2_hidden(sK0(X0,X1),X1) = iProver_top ),
% 3.59/1.00      inference(superposition,[status(thm)],[c_1375,c_1372]) ).
% 3.59/1.00  
% 3.59/1.00  cnf(c_3114,plain,
% 3.59/1.00      ( X0 = X1
% 3.59/1.00      | m1_subset_1(sK0(X1,X0),X1) = iProver_top
% 3.59/1.00      | m1_subset_1(sK0(X1,X0),X0) = iProver_top ),
% 3.59/1.00      inference(superposition,[status(thm)],[c_2205,c_1372]) ).
% 3.59/1.00  
% 3.59/1.00  cnf(c_7,plain,
% 3.59/1.00      ( ~ m1_subset_1(X0,X1) | r2_hidden(X0,X1) | v1_xboole_0(X1) ),
% 3.59/1.00      inference(cnf_transformation,[],[f56]) ).
% 3.59/1.00  
% 3.59/1.00  cnf(c_25,negated_conjecture,
% 3.59/1.00      ( ~ v1_xboole_0(sK4) ),
% 3.59/1.00      inference(cnf_transformation,[],[f74]) ).
% 3.59/1.00  
% 3.59/1.00  cnf(c_397,plain,
% 3.59/1.00      ( ~ m1_subset_1(X0,X1) | r2_hidden(X0,X1) | sK4 != X1 ),
% 3.59/1.00      inference(resolution_lifted,[status(thm)],[c_7,c_25]) ).
% 3.59/1.00  
% 3.59/1.00  cnf(c_398,plain,
% 3.59/1.00      ( ~ m1_subset_1(X0,sK4) | r2_hidden(X0,sK4) ),
% 3.59/1.00      inference(unflattening,[status(thm)],[c_397]) ).
% 3.59/1.00  
% 3.59/1.00  cnf(c_1365,plain,
% 3.59/1.00      ( m1_subset_1(X0,sK4) != iProver_top
% 3.59/1.00      | r2_hidden(X0,sK4) = iProver_top ),
% 3.59/1.00      inference(predicate_to_equality,[status(thm)],[c_398]) ).
% 3.59/1.00  
% 3.59/1.00  cnf(c_4516,plain,
% 3.59/1.00      ( sK4 = X0
% 3.59/1.00      | m1_subset_1(sK0(X0,sK4),X0) = iProver_top
% 3.59/1.00      | r2_hidden(sK0(X0,sK4),sK4) = iProver_top ),
% 3.59/1.00      inference(superposition,[status(thm)],[c_3114,c_1365]) ).
% 3.59/1.00  
% 3.59/1.00  cnf(c_19,plain,
% 3.59/1.00      ( v1_subset_1(X0,X1)
% 3.59/1.00      | ~ m1_subset_1(X0,k1_zfmisc_1(X1))
% 3.59/1.00      | X0 = X1 ),
% 3.59/1.00      inference(cnf_transformation,[],[f69]) ).
% 3.59/1.00  
% 3.59/1.00  cnf(c_291,plain,
% 3.59/1.00      ( v1_subset_1(X0,X1) | ~ r1_tarski(X0,X1) | X0 = X1 ),
% 3.59/1.00      inference(bin_hyper_res,[status(thm)],[c_19,c_225]) ).
% 3.59/1.00  
% 3.59/1.00  cnf(c_21,negated_conjecture,
% 3.59/1.00      ( ~ v1_subset_1(sK4,u1_struct_0(sK3))
% 3.59/1.00      | r2_hidden(k3_yellow_0(sK3),sK4) ),
% 3.59/1.00      inference(cnf_transformation,[],[f78]) ).
% 3.59/1.00  
% 3.59/1.00  cnf(c_228,plain,
% 3.59/1.00      ( ~ v1_subset_1(sK4,u1_struct_0(sK3))
% 3.59/1.00      | r2_hidden(k3_yellow_0(sK3),sK4) ),
% 3.59/1.00      inference(prop_impl,[status(thm)],[c_21]) ).
% 3.59/1.00  
% 3.59/1.00  cnf(c_436,plain,
% 3.59/1.00      ( ~ r1_tarski(X0,X1)
% 3.59/1.00      | r2_hidden(k3_yellow_0(sK3),sK4)
% 3.59/1.00      | X1 = X0
% 3.59/1.00      | u1_struct_0(sK3) != X1
% 3.59/1.00      | sK4 != X0 ),
% 3.59/1.00      inference(resolution_lifted,[status(thm)],[c_291,c_228]) ).
% 3.59/1.00  
% 3.59/1.00  cnf(c_437,plain,
% 3.59/1.00      ( ~ r1_tarski(sK4,u1_struct_0(sK3))
% 3.59/1.00      | r2_hidden(k3_yellow_0(sK3),sK4)
% 3.59/1.00      | u1_struct_0(sK3) = sK4 ),
% 3.59/1.00      inference(unflattening,[status(thm)],[c_436]) ).
% 3.59/1.00  
% 3.59/1.00  cnf(c_1364,plain,
% 3.59/1.00      ( u1_struct_0(sK3) = sK4
% 3.59/1.00      | r1_tarski(sK4,u1_struct_0(sK3)) != iProver_top
% 3.59/1.00      | r2_hidden(k3_yellow_0(sK3),sK4) = iProver_top ),
% 3.59/1.00      inference(predicate_to_equality,[status(thm)],[c_437]) ).
% 3.59/1.00  
% 3.59/1.00  cnf(c_36,plain,
% 3.59/1.00      ( m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(sK3))) = iProver_top ),
% 3.59/1.00      inference(predicate_to_equality,[status(thm)],[c_23]) ).
% 3.59/1.00  
% 3.59/1.00  cnf(c_438,plain,
% 3.59/1.00      ( u1_struct_0(sK3) = sK4
% 3.59/1.00      | r1_tarski(sK4,u1_struct_0(sK3)) != iProver_top
% 3.59/1.00      | r2_hidden(k3_yellow_0(sK3),sK4) = iProver_top ),
% 3.59/1.00      inference(predicate_to_equality,[status(thm)],[c_437]) ).
% 3.59/1.00  
% 3.59/1.00  cnf(c_1558,plain,
% 3.59/1.00      ( ~ m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(sK3)))
% 3.59/1.00      | r1_tarski(sK4,u1_struct_0(sK3)) ),
% 3.59/1.00      inference(instantiation,[status(thm)],[c_9]) ).
% 3.59/1.00  
% 3.59/1.00  cnf(c_1559,plain,
% 3.59/1.00      ( m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(sK3))) != iProver_top
% 3.59/1.00      | r1_tarski(sK4,u1_struct_0(sK3)) = iProver_top ),
% 3.59/1.00      inference(predicate_to_equality,[status(thm)],[c_1558]) ).
% 3.59/1.00  
% 3.59/1.00  cnf(c_847,plain,( X0 = X0 ),theory(equality) ).
% 3.59/1.00  
% 3.59/1.00  cnf(c_1633,plain,
% 3.59/1.00      ( sK4 = sK4 ),
% 3.59/1.00      inference(instantiation,[status(thm)],[c_847]) ).
% 3.59/1.00  
% 3.59/1.00  cnf(c_20,plain,
% 3.59/1.00      ( ~ v1_subset_1(X0,X0) | ~ m1_subset_1(X0,k1_zfmisc_1(X0)) ),
% 3.59/1.00      inference(cnf_transformation,[],[f81]) ).
% 3.59/1.00  
% 3.59/1.00  cnf(c_22,negated_conjecture,
% 3.59/1.00      ( v1_subset_1(sK4,u1_struct_0(sK3))
% 3.59/1.00      | ~ r2_hidden(k3_yellow_0(sK3),sK4) ),
% 3.59/1.00      inference(cnf_transformation,[],[f77]) ).
% 3.59/1.00  
% 3.59/1.00  cnf(c_226,plain,
% 3.59/1.00      ( v1_subset_1(sK4,u1_struct_0(sK3))
% 3.59/1.00      | ~ r2_hidden(k3_yellow_0(sK3),sK4) ),
% 3.59/1.00      inference(prop_impl,[status(thm)],[c_22]) ).
% 3.59/1.00  
% 3.59/1.00  cnf(c_449,plain,
% 3.59/1.00      ( ~ m1_subset_1(X0,k1_zfmisc_1(X0))
% 3.59/1.00      | ~ r2_hidden(k3_yellow_0(sK3),sK4)
% 3.59/1.00      | u1_struct_0(sK3) != X0
% 3.59/1.00      | sK4 != X0 ),
% 3.59/1.00      inference(resolution_lifted,[status(thm)],[c_20,c_226]) ).
% 3.59/1.00  
% 3.59/1.00  cnf(c_450,plain,
% 3.59/1.00      ( ~ m1_subset_1(u1_struct_0(sK3),k1_zfmisc_1(u1_struct_0(sK3)))
% 3.59/1.00      | ~ r2_hidden(k3_yellow_0(sK3),sK4)
% 3.59/1.00      | sK4 != u1_struct_0(sK3) ),
% 3.59/1.00      inference(unflattening,[status(thm)],[c_449]) ).
% 3.59/1.00  
% 3.59/1.00  cnf(c_1363,plain,
% 3.59/1.00      ( sK4 != u1_struct_0(sK3)
% 3.59/1.00      | m1_subset_1(u1_struct_0(sK3),k1_zfmisc_1(u1_struct_0(sK3))) != iProver_top
% 3.59/1.00      | r2_hidden(k3_yellow_0(sK3),sK4) != iProver_top ),
% 3.59/1.00      inference(predicate_to_equality,[status(thm)],[c_450]) ).
% 3.59/1.00  
% 3.59/1.00  cnf(c_26,negated_conjecture,
% 3.59/1.00      ( l1_orders_2(sK3) ),
% 3.59/1.00      inference(cnf_transformation,[],[f73]) ).
% 3.59/1.00  
% 3.59/1.00  cnf(c_33,plain,
% 3.59/1.00      ( l1_orders_2(sK3) = iProver_top ),
% 3.59/1.00      inference(predicate_to_equality,[status(thm)],[c_26]) ).
% 3.59/1.00  
% 3.59/1.00  cnf(c_40,plain,
% 3.59/1.00      ( ~ v1_subset_1(sK3,sK3) | ~ m1_subset_1(sK3,k1_zfmisc_1(sK3)) ),
% 3.59/1.00      inference(instantiation,[status(thm)],[c_20]) ).
% 3.59/1.00  
% 3.59/1.00  cnf(c_43,plain,
% 3.59/1.00      ( v1_subset_1(sK3,sK3)
% 3.59/1.00      | ~ m1_subset_1(sK3,k1_zfmisc_1(sK3))
% 3.59/1.00      | sK3 = sK3 ),
% 3.59/1.00      inference(instantiation,[status(thm)],[c_19]) ).
% 3.59/1.00  
% 3.59/1.00  cnf(c_11,plain,
% 3.59/1.00      ( m1_subset_1(k3_yellow_0(X0),u1_struct_0(X0))
% 3.59/1.00      | ~ l1_orders_2(X0) ),
% 3.59/1.00      inference(cnf_transformation,[],[f60]) ).
% 3.59/1.00  
% 3.59/1.00  cnf(c_64,plain,
% 3.59/1.00      ( m1_subset_1(k3_yellow_0(X0),u1_struct_0(X0)) = iProver_top
% 3.59/1.00      | l1_orders_2(X0) != iProver_top ),
% 3.59/1.00      inference(predicate_to_equality,[status(thm)],[c_11]) ).
% 3.59/1.00  
% 3.59/1.00  cnf(c_66,plain,
% 3.59/1.00      ( m1_subset_1(k3_yellow_0(sK3),u1_struct_0(sK3)) = iProver_top
% 3.59/1.00      | l1_orders_2(sK3) != iProver_top ),
% 3.59/1.00      inference(instantiation,[status(thm)],[c_64]) ).
% 3.59/1.00  
% 3.59/1.00  cnf(c_74,plain,
% 3.59/1.00      ( m1_subset_1(sK3,k1_zfmisc_1(sK3)) | ~ r1_tarski(sK3,sK3) ),
% 3.59/1.00      inference(instantiation,[status(thm)],[c_8]) ).
% 3.59/1.00  
% 3.59/1.00  cnf(c_4,plain,
% 3.59/1.00      ( r1_tarski(X0,X0) ),
% 3.59/1.00      inference(cnf_transformation,[],[f80]) ).
% 3.59/1.00  
% 3.59/1.00  cnf(c_84,plain,
% 3.59/1.00      ( r1_tarski(sK3,sK3) ),
% 3.59/1.00      inference(instantiation,[status(thm)],[c_4]) ).
% 3.59/1.00  
% 3.59/1.00  cnf(c_451,plain,
% 3.59/1.00      ( sK4 != u1_struct_0(sK3)
% 3.59/1.00      | m1_subset_1(u1_struct_0(sK3),k1_zfmisc_1(u1_struct_0(sK3))) != iProver_top
% 3.59/1.00      | r2_hidden(k3_yellow_0(sK3),sK4) != iProver_top ),
% 3.59/1.00      inference(predicate_to_equality,[status(thm)],[c_450]) ).
% 3.59/1.00  
% 3.59/1.00  cnf(c_853,plain,
% 3.59/1.00      ( X0 != X1 | k3_yellow_0(X0) = k3_yellow_0(X1) ),
% 3.59/1.00      theory(equality) ).
% 3.59/1.00  
% 3.59/1.00  cnf(c_862,plain,
% 3.59/1.00      ( k3_yellow_0(sK3) = k3_yellow_0(sK3) | sK3 != sK3 ),
% 3.59/1.00      inference(instantiation,[status(thm)],[c_853]) ).
% 3.59/1.00  
% 3.59/1.00  cnf(c_1553,plain,
% 3.59/1.00      ( m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK3)))
% 3.59/1.00      | ~ r1_tarski(X0,u1_struct_0(sK3)) ),
% 3.59/1.00      inference(instantiation,[status(thm)],[c_8]) ).
% 3.59/1.00  
% 3.59/1.00  cnf(c_1643,plain,
% 3.59/1.00      ( m1_subset_1(u1_struct_0(sK3),k1_zfmisc_1(u1_struct_0(sK3)))
% 3.59/1.00      | ~ r1_tarski(u1_struct_0(sK3),u1_struct_0(sK3)) ),
% 3.59/1.00      inference(instantiation,[status(thm)],[c_1553]) ).
% 3.59/1.00  
% 3.59/1.00  cnf(c_1645,plain,
% 3.59/1.00      ( m1_subset_1(u1_struct_0(sK3),k1_zfmisc_1(u1_struct_0(sK3))) = iProver_top
% 3.59/1.00      | r1_tarski(u1_struct_0(sK3),u1_struct_0(sK3)) != iProver_top ),
% 3.59/1.00      inference(predicate_to_equality,[status(thm)],[c_1643]) ).
% 3.59/1.00  
% 3.59/1.00  cnf(c_1644,plain,
% 3.59/1.00      ( r1_tarski(u1_struct_0(sK3),u1_struct_0(sK3)) ),
% 3.59/1.00      inference(instantiation,[status(thm)],[c_4]) ).
% 3.59/1.00  
% 3.59/1.00  cnf(c_1647,plain,
% 3.59/1.00      ( r1_tarski(u1_struct_0(sK3),u1_struct_0(sK3)) = iProver_top ),
% 3.59/1.00      inference(predicate_to_equality,[status(thm)],[c_1644]) ).
% 3.59/1.00  
% 3.59/1.00  cnf(c_852,plain,
% 3.59/1.00      ( ~ m1_subset_1(X0,X1) | m1_subset_1(X2,X3) | X2 != X0 | X3 != X1 ),
% 3.59/1.00      theory(equality) ).
% 3.59/1.00  
% 3.59/1.00  cnf(c_1572,plain,
% 3.59/1.00      ( m1_subset_1(X0,X1)
% 3.59/1.00      | ~ m1_subset_1(k3_yellow_0(sK3),u1_struct_0(sK3))
% 3.59/1.00      | X1 != u1_struct_0(sK3)
% 3.59/1.00      | X0 != k3_yellow_0(sK3) ),
% 3.59/1.00      inference(instantiation,[status(thm)],[c_852]) ).
% 3.59/1.00  
% 3.59/1.00  cnf(c_1831,plain,
% 3.59/1.00      ( m1_subset_1(k3_yellow_0(sK3),X0)
% 3.59/1.00      | ~ m1_subset_1(k3_yellow_0(sK3),u1_struct_0(sK3))
% 3.59/1.00      | X0 != u1_struct_0(sK3)
% 3.59/1.00      | k3_yellow_0(sK3) != k3_yellow_0(sK3) ),
% 3.59/1.00      inference(instantiation,[status(thm)],[c_1572]) ).
% 3.59/1.00  
% 3.59/1.00  cnf(c_2060,plain,
% 3.59/1.00      ( ~ m1_subset_1(k3_yellow_0(sK3),u1_struct_0(sK3))
% 3.59/1.00      | m1_subset_1(k3_yellow_0(sK3),sK4)
% 3.59/1.00      | k3_yellow_0(sK3) != k3_yellow_0(sK3)
% 3.59/1.00      | sK4 != u1_struct_0(sK3) ),
% 3.59/1.00      inference(instantiation,[status(thm)],[c_1831]) ).
% 3.59/1.00  
% 3.59/1.00  cnf(c_2062,plain,
% 3.59/1.00      ( k3_yellow_0(sK3) != k3_yellow_0(sK3)
% 3.59/1.00      | sK4 != u1_struct_0(sK3)
% 3.59/1.00      | m1_subset_1(k3_yellow_0(sK3),u1_struct_0(sK3)) != iProver_top
% 3.59/1.00      | m1_subset_1(k3_yellow_0(sK3),sK4) = iProver_top ),
% 3.59/1.00      inference(predicate_to_equality,[status(thm)],[c_2060]) ).
% 3.59/1.00  
% 3.59/1.00  cnf(c_2061,plain,
% 3.59/1.00      ( ~ m1_subset_1(k3_yellow_0(sK3),sK4)
% 3.59/1.00      | r2_hidden(k3_yellow_0(sK3),sK4) ),
% 3.59/1.00      inference(instantiation,[status(thm)],[c_398]) ).
% 3.59/1.00  
% 3.59/1.00  cnf(c_2064,plain,
% 3.59/1.00      ( m1_subset_1(k3_yellow_0(sK3),sK4) != iProver_top
% 3.59/1.00      | r2_hidden(k3_yellow_0(sK3),sK4) = iProver_top ),
% 3.59/1.00      inference(predicate_to_equality,[status(thm)],[c_2061]) ).
% 3.59/1.00  
% 3.59/1.00  cnf(c_2111,plain,
% 3.59/1.00      ( sK4 != u1_struct_0(sK3) ),
% 3.59/1.00      inference(global_propositional_subsumption,
% 3.59/1.00                [status(thm)],
% 3.59/1.00                [c_1363,c_33,c_40,c_43,c_66,c_74,c_84,c_451,c_862,c_1645,
% 3.59/1.00                 c_1647,c_2062,c_2064]) ).
% 3.59/1.00  
% 3.59/1.00  cnf(c_848,plain,( X0 != X1 | X2 != X1 | X2 = X0 ),theory(equality) ).
% 3.59/1.00  
% 3.59/1.00  cnf(c_1675,plain,
% 3.59/1.00      ( X0 != X1 | X0 = u1_struct_0(sK3) | u1_struct_0(sK3) != X1 ),
% 3.59/1.00      inference(instantiation,[status(thm)],[c_848]) ).
% 3.59/1.00  
% 3.59/1.00  cnf(c_2148,plain,
% 3.59/1.00      ( u1_struct_0(sK3) != X0 | sK4 != X0 | sK4 = u1_struct_0(sK3) ),
% 3.59/1.00      inference(instantiation,[status(thm)],[c_1675]) ).
% 3.59/1.00  
% 3.59/1.00  cnf(c_2693,plain,
% 3.59/1.00      ( u1_struct_0(sK3) != sK4 | sK4 = u1_struct_0(sK3) | sK4 != sK4 ),
% 3.59/1.00      inference(instantiation,[status(thm)],[c_2148]) ).
% 3.59/1.00  
% 3.59/1.00  cnf(c_3056,plain,
% 3.59/1.00      ( r2_hidden(k3_yellow_0(sK3),sK4) = iProver_top ),
% 3.59/1.00      inference(global_propositional_subsumption,
% 3.59/1.00                [status(thm)],
% 3.59/1.00                [c_1364,c_33,c_36,c_40,c_43,c_66,c_74,c_84,c_438,c_451,
% 3.59/1.00                 c_862,c_1559,c_1633,c_1645,c_1647,c_2062,c_2064,c_2693]) ).
% 3.59/1.00  
% 3.59/1.00  cnf(c_18,plain,
% 3.59/1.00      ( ~ r1_orders_2(X0,X1,X2)
% 3.59/1.00      | ~ v13_waybel_0(X3,X0)
% 3.59/1.00      | ~ m1_subset_1(X2,u1_struct_0(X0))
% 3.59/1.00      | ~ m1_subset_1(X1,u1_struct_0(X0))
% 3.59/1.00      | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))
% 3.59/1.00      | ~ r2_hidden(X1,X3)
% 3.59/1.00      | r2_hidden(X2,X3)
% 3.59/1.00      | ~ l1_orders_2(X0) ),
% 3.59/1.00      inference(cnf_transformation,[],[f62]) ).
% 3.59/1.00  
% 3.59/1.00  cnf(c_12,plain,
% 3.59/1.00      ( r1_orders_2(X0,k3_yellow_0(X0),X1)
% 3.59/1.00      | ~ m1_subset_1(X1,u1_struct_0(X0))
% 3.59/1.00      | v2_struct_0(X0)
% 3.59/1.00      | ~ v5_orders_2(X0)
% 3.59/1.00      | ~ v1_yellow_0(X0)
% 3.59/1.00      | ~ l1_orders_2(X0) ),
% 3.59/1.00      inference(cnf_transformation,[],[f61]) ).
% 3.59/1.00  
% 3.59/1.00  cnf(c_27,negated_conjecture,
% 3.59/1.00      ( v1_yellow_0(sK3) ),
% 3.59/1.00      inference(cnf_transformation,[],[f72]) ).
% 3.59/1.00  
% 3.59/1.00  cnf(c_412,plain,
% 3.59/1.00      ( r1_orders_2(X0,k3_yellow_0(X0),X1)
% 3.59/1.00      | ~ m1_subset_1(X1,u1_struct_0(X0))
% 3.59/1.00      | v2_struct_0(X0)
% 3.59/1.00      | ~ v5_orders_2(X0)
% 3.59/1.00      | ~ l1_orders_2(X0)
% 3.59/1.00      | sK3 != X0 ),
% 3.59/1.00      inference(resolution_lifted,[status(thm)],[c_12,c_27]) ).
% 3.59/1.00  
% 3.59/1.00  cnf(c_413,plain,
% 3.59/1.00      ( r1_orders_2(sK3,k3_yellow_0(sK3),X0)
% 3.59/1.00      | ~ m1_subset_1(X0,u1_struct_0(sK3))
% 3.59/1.00      | v2_struct_0(sK3)
% 3.59/1.00      | ~ v5_orders_2(sK3)
% 3.59/1.00      | ~ l1_orders_2(sK3) ),
% 3.59/1.00      inference(unflattening,[status(thm)],[c_412]) ).
% 3.59/1.00  
% 3.59/1.00  cnf(c_29,negated_conjecture,
% 3.59/1.00      ( ~ v2_struct_0(sK3) ),
% 3.59/1.00      inference(cnf_transformation,[],[f70]) ).
% 3.59/1.00  
% 3.59/1.00  cnf(c_28,negated_conjecture,
% 3.59/1.00      ( v5_orders_2(sK3) ),
% 3.59/1.00      inference(cnf_transformation,[],[f71]) ).
% 3.59/1.00  
% 3.59/1.00  cnf(c_417,plain,
% 3.59/1.00      ( ~ m1_subset_1(X0,u1_struct_0(sK3))
% 3.59/1.00      | r1_orders_2(sK3,k3_yellow_0(sK3),X0) ),
% 3.59/1.00      inference(global_propositional_subsumption,
% 3.59/1.00                [status(thm)],
% 3.59/1.00                [c_413,c_29,c_28,c_26]) ).
% 3.59/1.00  
% 3.59/1.00  cnf(c_418,plain,
% 3.59/1.00      ( r1_orders_2(sK3,k3_yellow_0(sK3),X0)
% 3.59/1.00      | ~ m1_subset_1(X0,u1_struct_0(sK3)) ),
% 3.59/1.00      inference(renaming,[status(thm)],[c_417]) ).
% 3.59/1.00  
% 3.59/1.00  cnf(c_500,plain,
% 3.59/1.00      ( ~ v13_waybel_0(X0,X1)
% 3.59/1.00      | ~ m1_subset_1(X2,u1_struct_0(X1))
% 3.59/1.00      | ~ m1_subset_1(X3,u1_struct_0(X1))
% 3.59/1.00      | ~ m1_subset_1(X4,u1_struct_0(sK3))
% 3.59/1.00      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 3.59/1.00      | ~ r2_hidden(X2,X0)
% 3.59/1.00      | r2_hidden(X3,X0)
% 3.59/1.00      | ~ l1_orders_2(X1)
% 3.59/1.00      | X4 != X3
% 3.59/1.00      | k3_yellow_0(sK3) != X2
% 3.59/1.00      | sK3 != X1 ),
% 3.59/1.00      inference(resolution_lifted,[status(thm)],[c_18,c_418]) ).
% 3.59/1.00  
% 3.59/1.00  cnf(c_501,plain,
% 3.59/1.00      ( ~ v13_waybel_0(X0,sK3)
% 3.59/1.00      | ~ m1_subset_1(X1,u1_struct_0(sK3))
% 3.59/1.00      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK3)))
% 3.59/1.00      | ~ m1_subset_1(k3_yellow_0(sK3),u1_struct_0(sK3))
% 3.59/1.00      | r2_hidden(X1,X0)
% 3.59/1.00      | ~ r2_hidden(k3_yellow_0(sK3),X0)
% 3.59/1.00      | ~ l1_orders_2(sK3) ),
% 3.59/1.00      inference(unflattening,[status(thm)],[c_500]) ).
% 3.59/1.00  
% 3.59/1.00  cnf(c_65,plain,
% 3.59/1.00      ( m1_subset_1(k3_yellow_0(sK3),u1_struct_0(sK3))
% 3.59/1.00      | ~ l1_orders_2(sK3) ),
% 3.59/1.00      inference(instantiation,[status(thm)],[c_11]) ).
% 3.59/1.00  
% 3.59/1.00  cnf(c_505,plain,
% 3.59/1.00      ( ~ r2_hidden(k3_yellow_0(sK3),X0)
% 3.59/1.00      | r2_hidden(X1,X0)
% 3.59/1.00      | ~ v13_waybel_0(X0,sK3)
% 3.59/1.00      | ~ m1_subset_1(X1,u1_struct_0(sK3))
% 3.59/1.00      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK3))) ),
% 3.59/1.00      inference(global_propositional_subsumption,
% 3.59/1.00                [status(thm)],
% 3.59/1.00                [c_501,c_26,c_65]) ).
% 3.59/1.00  
% 3.59/1.00  cnf(c_506,plain,
% 3.59/1.00      ( ~ v13_waybel_0(X0,sK3)
% 3.59/1.00      | ~ m1_subset_1(X1,u1_struct_0(sK3))
% 3.59/1.00      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK3)))
% 3.59/1.00      | r2_hidden(X1,X0)
% 3.59/1.00      | ~ r2_hidden(k3_yellow_0(sK3),X0) ),
% 3.59/1.00      inference(renaming,[status(thm)],[c_505]) ).
% 3.59/1.00  
% 3.59/1.00  cnf(c_1362,plain,
% 3.59/1.00      ( v13_waybel_0(X0,sK3) != iProver_top
% 3.59/1.00      | m1_subset_1(X1,u1_struct_0(sK3)) != iProver_top
% 3.59/1.00      | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK3))) != iProver_top
% 3.59/1.00      | r2_hidden(X1,X0) = iProver_top
% 3.59/1.00      | r2_hidden(k3_yellow_0(sK3),X0) != iProver_top ),
% 3.59/1.00      inference(predicate_to_equality,[status(thm)],[c_506]) ).
% 3.59/1.00  
% 3.59/1.00  cnf(c_1991,plain,
% 3.59/1.00      ( v13_waybel_0(sK4,sK3) != iProver_top
% 3.59/1.00      | m1_subset_1(X0,u1_struct_0(sK3)) != iProver_top
% 3.59/1.00      | r2_hidden(X0,sK4) = iProver_top
% 3.59/1.00      | r2_hidden(k3_yellow_0(sK3),sK4) != iProver_top ),
% 3.59/1.00      inference(superposition,[status(thm)],[c_1368,c_1362]) ).
% 3.59/1.00  
% 3.59/1.00  cnf(c_24,negated_conjecture,
% 3.59/1.00      ( v13_waybel_0(sK4,sK3) ),
% 3.59/1.00      inference(cnf_transformation,[],[f75]) ).
% 3.59/1.00  
% 3.59/1.00  cnf(c_35,plain,
% 3.59/1.00      ( v13_waybel_0(sK4,sK3) = iProver_top ),
% 3.59/1.00      inference(predicate_to_equality,[status(thm)],[c_24]) ).
% 3.59/1.00  
% 3.59/1.00  cnf(c_2017,plain,
% 3.59/1.00      ( m1_subset_1(X0,u1_struct_0(sK3)) != iProver_top
% 3.59/1.00      | r2_hidden(X0,sK4) = iProver_top
% 3.59/1.00      | r2_hidden(k3_yellow_0(sK3),sK4) != iProver_top ),
% 3.59/1.00      inference(global_propositional_subsumption,
% 3.59/1.00                [status(thm)],
% 3.59/1.00                [c_1991,c_35]) ).
% 3.59/1.00  
% 3.59/1.00  cnf(c_3062,plain,
% 3.59/1.00      ( m1_subset_1(X0,u1_struct_0(sK3)) != iProver_top
% 3.59/1.00      | r2_hidden(X0,sK4) = iProver_top ),
% 3.59/1.00      inference(superposition,[status(thm)],[c_3056,c_2017]) ).
% 3.59/1.00  
% 3.59/1.00  cnf(c_5223,plain,
% 3.59/1.00      ( u1_struct_0(sK3) = sK4
% 3.59/1.00      | r2_hidden(sK0(u1_struct_0(sK3),sK4),sK4) = iProver_top ),
% 3.59/1.00      inference(superposition,[status(thm)],[c_4516,c_3062]) ).
% 3.59/1.00  
% 3.59/1.00  cnf(c_9347,plain,
% 3.59/1.00      ( r2_hidden(sK0(u1_struct_0(sK3),sK4),sK4) = iProver_top ),
% 3.59/1.00      inference(global_propositional_subsumption,
% 3.59/1.00                [status(thm)],
% 3.59/1.00                [c_5223,c_33,c_40,c_43,c_66,c_74,c_84,c_451,c_862,c_1633,
% 3.59/1.00                 c_1645,c_1647,c_2062,c_2064,c_2693]) ).
% 3.59/1.00  
% 3.59/1.00  cnf(c_0,plain,
% 3.59/1.00      ( ~ r2_hidden(sK0(X0,X1),X1)
% 3.59/1.00      | ~ r2_hidden(sK0(X0,X1),X0)
% 3.59/1.00      | X1 = X0 ),
% 3.59/1.00      inference(cnf_transformation,[],[f50]) ).
% 3.59/1.00  
% 3.59/1.00  cnf(c_1376,plain,
% 3.59/1.00      ( X0 = X1
% 3.59/1.00      | r2_hidden(sK0(X1,X0),X0) != iProver_top
% 3.59/1.00      | r2_hidden(sK0(X1,X0),X1) != iProver_top ),
% 3.59/1.00      inference(predicate_to_equality,[status(thm)],[c_0]) ).
% 3.59/1.00  
% 3.59/1.00  cnf(c_9354,plain,
% 3.59/1.00      ( u1_struct_0(sK3) = sK4
% 3.59/1.00      | r2_hidden(sK0(u1_struct_0(sK3),sK4),u1_struct_0(sK3)) != iProver_top ),
% 3.59/1.00      inference(superposition,[status(thm)],[c_9347,c_1376]) ).
% 3.59/1.00  
% 3.59/1.00  cnf(c_1660,plain,
% 3.59/1.00      ( ~ r2_hidden(sK0(u1_struct_0(sK3),X0),X0)
% 3.59/1.00      | ~ r2_hidden(sK0(u1_struct_0(sK3),X0),u1_struct_0(sK3))
% 3.59/1.00      | X0 = u1_struct_0(sK3) ),
% 3.59/1.00      inference(instantiation,[status(thm)],[c_0]) ).
% 3.59/1.00  
% 3.59/1.00  cnf(c_2149,plain,
% 3.59/1.00      ( ~ r2_hidden(sK0(u1_struct_0(sK3),sK4),u1_struct_0(sK3))
% 3.59/1.00      | ~ r2_hidden(sK0(u1_struct_0(sK3),sK4),sK4)
% 3.59/1.00      | sK4 = u1_struct_0(sK3) ),
% 3.59/1.00      inference(instantiation,[status(thm)],[c_1660]) ).
% 3.59/1.00  
% 3.59/1.00  cnf(c_2158,plain,
% 3.59/1.00      ( sK4 = u1_struct_0(sK3)
% 3.59/1.00      | r2_hidden(sK0(u1_struct_0(sK3),sK4),u1_struct_0(sK3)) != iProver_top
% 3.59/1.00      | r2_hidden(sK0(u1_struct_0(sK3),sK4),sK4) != iProver_top ),
% 3.59/1.00      inference(predicate_to_equality,[status(thm)],[c_2149]) ).
% 3.59/1.00  
% 3.59/1.00  cnf(c_9900,plain,
% 3.59/1.00      ( r2_hidden(sK0(u1_struct_0(sK3),sK4),u1_struct_0(sK3)) != iProver_top ),
% 3.59/1.00      inference(global_propositional_subsumption,
% 3.59/1.00                [status(thm)],
% 3.59/1.00                [c_9354,c_33,c_40,c_43,c_66,c_74,c_84,c_451,c_862,c_1633,
% 3.59/1.00                 c_1645,c_1647,c_2062,c_2064,c_2158,c_2693,c_5223]) ).
% 3.59/1.00  
% 3.59/1.00  cnf(c_9909,plain,
% 3.59/1.00      ( r2_hidden(sK0(u1_struct_0(sK3),sK4),sK4) != iProver_top ),
% 3.59/1.00      inference(superposition,[status(thm)],[c_3102,c_9900]) ).
% 3.59/1.00  
% 3.59/1.00  cnf(contradiction,plain,
% 3.59/1.00      ( $false ),
% 3.59/1.00      inference(minisat,
% 3.59/1.00                [status(thm)],
% 3.59/1.00                [c_9909,c_5223,c_2693,c_2111,c_1633]) ).
% 3.59/1.00  
% 3.59/1.00  
% 3.59/1.00  % SZS output end CNFRefutation for theBenchmark.p
% 3.59/1.00  
% 3.59/1.00  ------                               Statistics
% 3.59/1.00  
% 3.59/1.00  ------ General
% 3.59/1.00  
% 3.59/1.00  abstr_ref_over_cycles:                  0
% 3.59/1.00  abstr_ref_under_cycles:                 0
% 3.59/1.00  gc_basic_clause_elim:                   0
% 3.59/1.00  forced_gc_time:                         0
% 3.59/1.00  parsing_time:                           0.013
% 3.59/1.00  unif_index_cands_time:                  0.
% 3.59/1.00  unif_index_add_time:                    0.
% 3.59/1.00  orderings_time:                         0.
% 3.59/1.00  out_proof_time:                         0.027
% 3.59/1.00  total_time:                             0.38
% 3.59/1.00  num_of_symbols:                         50
% 3.59/1.00  num_of_terms:                           5865
% 3.59/1.00  
% 3.59/1.00  ------ Preprocessing
% 3.59/1.00  
% 3.59/1.00  num_of_splits:                          0
% 3.59/1.00  num_of_split_atoms:                     0
% 3.59/1.00  num_of_reused_defs:                     0
% 3.59/1.00  num_eq_ax_congr_red:                    17
% 3.59/1.00  num_of_sem_filtered_clauses:            1
% 3.59/1.00  num_of_subtypes:                        0
% 3.59/1.00  monotx_restored_types:                  0
% 3.59/1.00  sat_num_of_epr_types:                   0
% 3.59/1.00  sat_num_of_non_cyclic_types:            0
% 3.59/1.00  sat_guarded_non_collapsed_types:        0
% 3.59/1.00  num_pure_diseq_elim:                    0
% 3.59/1.00  simp_replaced_by:                       0
% 3.59/1.00  res_preprocessed:                       115
% 3.59/1.00  prep_upred:                             0
% 3.59/1.00  prep_unflattend:                        19
% 3.59/1.00  smt_new_axioms:                         0
% 3.59/1.00  pred_elim_cands:                        4
% 3.59/1.00  pred_elim:                              7
% 3.59/1.00  pred_elim_cl:                           8
% 3.59/1.00  pred_elim_cycles:                       9
% 3.59/1.00  merged_defs:                            10
% 3.59/1.00  merged_defs_ncl:                        0
% 3.59/1.00  bin_hyper_res:                          12
% 3.59/1.00  prep_cycles:                            4
% 3.59/1.00  pred_elim_time:                         0.006
% 3.59/1.00  splitting_time:                         0.
% 3.59/1.00  sem_filter_time:                        0.
% 3.59/1.00  monotx_time:                            0.001
% 3.59/1.00  subtype_inf_time:                       0.
% 3.59/1.00  
% 3.59/1.00  ------ Problem properties
% 3.59/1.00  
% 3.59/1.00  clauses:                                21
% 3.59/1.00  conjectures:                            2
% 3.59/1.00  epr:                                    6
% 3.59/1.00  horn:                                   15
% 3.59/1.00  ground:                                 5
% 3.59/1.00  unary:                                  4
% 3.59/1.00  binary:                                 4
% 3.59/1.00  lits:                                   56
% 3.59/1.00  lits_eq:                                5
% 3.59/1.00  fd_pure:                                0
% 3.59/1.00  fd_pseudo:                              0
% 3.59/1.00  fd_cond:                                0
% 3.59/1.00  fd_pseudo_cond:                         3
% 3.59/1.00  ac_symbols:                             0
% 3.59/1.00  
% 3.59/1.00  ------ Propositional Solver
% 3.59/1.00  
% 3.59/1.00  prop_solver_calls:                      29
% 3.59/1.00  prop_fast_solver_calls:                 1075
% 3.59/1.00  smt_solver_calls:                       0
% 3.59/1.00  smt_fast_solver_calls:                  0
% 3.59/1.00  prop_num_of_clauses:                    2951
% 3.59/1.00  prop_preprocess_simplified:             7193
% 3.59/1.00  prop_fo_subsumed:                       23
% 3.59/1.00  prop_solver_time:                       0.
% 3.59/1.00  smt_solver_time:                        0.
% 3.59/1.00  smt_fast_solver_time:                   0.
% 3.59/1.00  prop_fast_solver_time:                  0.
% 3.59/1.00  prop_unsat_core_time:                   0.
% 3.59/1.00  
% 3.59/1.00  ------ QBF
% 3.59/1.00  
% 3.59/1.00  qbf_q_res:                              0
% 3.59/1.00  qbf_num_tautologies:                    0
% 3.59/1.00  qbf_prep_cycles:                        0
% 3.59/1.00  
% 3.59/1.00  ------ BMC1
% 3.59/1.00  
% 3.59/1.00  bmc1_current_bound:                     -1
% 3.59/1.00  bmc1_last_solved_bound:                 -1
% 3.59/1.00  bmc1_unsat_core_size:                   -1
% 3.59/1.00  bmc1_unsat_core_parents_size:           -1
% 3.59/1.00  bmc1_merge_next_fun:                    0
% 3.59/1.00  bmc1_unsat_core_clauses_time:           0.
% 3.59/1.00  
% 3.59/1.00  ------ Instantiation
% 3.59/1.00  
% 3.59/1.00  inst_num_of_clauses:                    705
% 3.59/1.00  inst_num_in_passive:                    268
% 3.59/1.00  inst_num_in_active:                     283
% 3.59/1.00  inst_num_in_unprocessed:                156
% 3.59/1.00  inst_num_of_loops:                      490
% 3.59/1.00  inst_num_of_learning_restarts:          0
% 3.59/1.00  inst_num_moves_active_passive:          204
% 3.59/1.00  inst_lit_activity:                      0
% 3.59/1.00  inst_lit_activity_moves:                0
% 3.59/1.00  inst_num_tautologies:                   0
% 3.59/1.00  inst_num_prop_implied:                  0
% 3.59/1.00  inst_num_existing_simplified:           0
% 3.59/1.00  inst_num_eq_res_simplified:             0
% 3.59/1.00  inst_num_child_elim:                    0
% 3.59/1.00  inst_num_of_dismatching_blockings:      230
% 3.59/1.00  inst_num_of_non_proper_insts:           847
% 3.59/1.00  inst_num_of_duplicates:                 0
% 3.59/1.00  inst_inst_num_from_inst_to_res:         0
% 3.59/1.00  inst_dismatching_checking_time:         0.
% 3.59/1.00  
% 3.59/1.00  ------ Resolution
% 3.59/1.00  
% 3.59/1.00  res_num_of_clauses:                     0
% 3.59/1.00  res_num_in_passive:                     0
% 3.59/1.00  res_num_in_active:                      0
% 3.59/1.00  res_num_of_loops:                       119
% 3.59/1.00  res_forward_subset_subsumed:            130
% 3.59/1.00  res_backward_subset_subsumed:           4
% 3.59/1.00  res_forward_subsumed:                   0
% 3.59/1.00  res_backward_subsumed:                  0
% 3.59/1.00  res_forward_subsumption_resolution:     2
% 3.59/1.00  res_backward_subsumption_resolution:    0
% 3.59/1.00  res_clause_to_clause_subsumption:       1648
% 3.59/1.00  res_orphan_elimination:                 0
% 3.59/1.00  res_tautology_del:                      89
% 3.59/1.00  res_num_eq_res_simplified:              0
% 3.59/1.00  res_num_sel_changes:                    0
% 3.59/1.00  res_moves_from_active_to_pass:          0
% 3.59/1.00  
% 3.59/1.00  ------ Superposition
% 3.59/1.00  
% 3.59/1.00  sup_time_total:                         0.
% 3.59/1.00  sup_time_generating:                    0.
% 3.59/1.00  sup_time_sim_full:                      0.
% 3.59/1.00  sup_time_sim_immed:                     0.
% 3.59/1.00  
% 3.59/1.00  sup_num_of_clauses:                     256
% 3.59/1.00  sup_num_in_active:                      95
% 3.59/1.00  sup_num_in_passive:                     161
% 3.59/1.00  sup_num_of_loops:                       96
% 3.59/1.00  sup_fw_superposition:                   147
% 3.59/1.00  sup_bw_superposition:                   263
% 3.59/1.00  sup_immediate_simplified:               48
% 3.59/1.00  sup_given_eliminated:                   0
% 3.59/1.00  comparisons_done:                       0
% 3.59/1.00  comparisons_avoided:                    0
% 3.59/1.00  
% 3.59/1.00  ------ Simplifications
% 3.59/1.00  
% 3.59/1.00  
% 3.59/1.00  sim_fw_subset_subsumed:                 17
% 3.59/1.00  sim_bw_subset_subsumed:                 4
% 3.59/1.00  sim_fw_subsumed:                        24
% 3.59/1.00  sim_bw_subsumed:                        3
% 3.59/1.00  sim_fw_subsumption_res:                 0
% 3.59/1.00  sim_bw_subsumption_res:                 6
% 3.59/1.00  sim_tautology_del:                      88
% 3.59/1.00  sim_eq_tautology_del:                   18
% 3.59/1.00  sim_eq_res_simp:                        3
% 3.59/1.00  sim_fw_demodulated:                     0
% 3.59/1.00  sim_bw_demodulated:                     0
% 3.59/1.00  sim_light_normalised:                   0
% 3.59/1.00  sim_joinable_taut:                      0
% 3.59/1.00  sim_joinable_simp:                      0
% 3.59/1.00  sim_ac_normalised:                      0
% 3.59/1.00  sim_smt_subsumption:                    0
% 3.59/1.00  
%------------------------------------------------------------------------------
