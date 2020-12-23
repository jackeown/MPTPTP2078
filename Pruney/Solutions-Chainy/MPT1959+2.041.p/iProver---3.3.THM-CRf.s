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
% DateTime   : Thu Dec  3 12:28:32 EST 2020

% Result     : Theorem 3.73s
% Output     : CNFRefutation 3.73s
% Verified   : 
% Statistics : Number of formulae       :  166 ( 514 expanded)
%              Number of clauses        :   95 ( 156 expanded)
%              Number of leaves         :   22 ( 103 expanded)
%              Depth                    :   28
%              Number of atoms          :  645 (3571 expanded)
%              Number of equality atoms :  124 ( 201 expanded)
%              Maximal formula depth    :   14 (   5 average)
%              Maximal clause size      :   22 (   3 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f7,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(X2))
        & r2_hidden(X0,X1) )
     => m1_subset_1(X0,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f20,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X0,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f21,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X0,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(flattening,[],[f20])).

fof(f60,plain,(
    ! [X2,X0,X1] :
      ( m1_subset_1(X0,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( ( v1_xboole_0(X0)
       => ( m1_subset_1(X1,X0)
        <=> v1_xboole_0(X1) ) )
      & ( ~ v1_xboole_0(X0)
       => ( m1_subset_1(X1,X0)
        <=> r2_hidden(X1,X0) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f18,plain,(
    ! [X0,X1] :
      ( ( ( m1_subset_1(X1,X0)
        <=> v1_xboole_0(X1) )
        | ~ v1_xboole_0(X0) )
      & ( ( m1_subset_1(X1,X0)
        <=> r2_hidden(X1,X0) )
        | v1_xboole_0(X0) ) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f37,plain,(
    ! [X0,X1] :
      ( ( ( ( m1_subset_1(X1,X0)
            | ~ v1_xboole_0(X1) )
          & ( v1_xboole_0(X1)
            | ~ m1_subset_1(X1,X0) ) )
        | ~ v1_xboole_0(X0) )
      & ( ( ( m1_subset_1(X1,X0)
            | ~ r2_hidden(X1,X0) )
          & ( r2_hidden(X1,X0)
            | ~ m1_subset_1(X1,X0) ) )
        | v1_xboole_0(X0) ) ) ),
    inference(nnf_transformation,[],[f18])).

fof(f53,plain,(
    ! [X0,X1] :
      ( r2_hidden(X1,X0)
      | ~ m1_subset_1(X1,X0)
      | v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f37])).

fof(f2,axiom,(
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
    inference(ennf_transformation,[],[f2])).

fof(f34,plain,(
    ! [X0,X1] :
      ( X0 = X1
      | ? [X2] :
          ( ( ~ r2_hidden(X2,X1)
            | ~ r2_hidden(X2,X0) )
          & ( r2_hidden(X2,X1)
            | r2_hidden(X2,X0) ) ) ) ),
    inference(nnf_transformation,[],[f17])).

fof(f35,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ( ~ r2_hidden(X2,X1)
            | ~ r2_hidden(X2,X0) )
          & ( r2_hidden(X2,X1)
            | r2_hidden(X2,X0) ) )
     => ( ( ~ r2_hidden(sK1(X0,X1),X1)
          | ~ r2_hidden(sK1(X0,X1),X0) )
        & ( r2_hidden(sK1(X0,X1),X1)
          | r2_hidden(sK1(X0,X1),X0) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f36,plain,(
    ! [X0,X1] :
      ( X0 = X1
      | ( ( ~ r2_hidden(sK1(X0,X1),X1)
          | ~ r2_hidden(sK1(X0,X1),X0) )
        & ( r2_hidden(sK1(X0,X1),X1)
          | r2_hidden(sK1(X0,X1),X0) ) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1])],[f34,f35])).

fof(f51,plain,(
    ! [X0,X1] :
      ( X0 = X1
      | r2_hidden(sK1(X0,X1),X1)
      | r2_hidden(sK1(X0,X1),X0) ) ),
    inference(cnf_transformation,[],[f36])).

fof(f54,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X1,X0)
      | ~ r2_hidden(X1,X0)
      | v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f37])).

fof(f1,axiom,(
    ! [X0] :
      ( v1_xboole_0(X0)
    <=> ! [X1] : ~ r2_hidden(X1,X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f30,plain,(
    ! [X0] :
      ( ( v1_xboole_0(X0)
        | ? [X1] : r2_hidden(X1,X0) )
      & ( ! [X1] : ~ r2_hidden(X1,X0)
        | ~ v1_xboole_0(X0) ) ) ),
    inference(nnf_transformation,[],[f1])).

fof(f31,plain,(
    ! [X0] :
      ( ( v1_xboole_0(X0)
        | ? [X1] : r2_hidden(X1,X0) )
      & ( ! [X2] : ~ r2_hidden(X2,X0)
        | ~ v1_xboole_0(X0) ) ) ),
    inference(rectify,[],[f30])).

fof(f32,plain,(
    ! [X0] :
      ( ? [X1] : r2_hidden(X1,X0)
     => r2_hidden(sK0(X0),X0) ) ),
    introduced(choice_axiom,[])).

fof(f33,plain,(
    ! [X0] :
      ( ( v1_xboole_0(X0)
        | r2_hidden(sK0(X0),X0) )
      & ( ! [X2] : ~ r2_hidden(X2,X0)
        | ~ v1_xboole_0(X0) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f31,f32])).

fof(f49,plain,(
    ! [X2,X0] :
      ( ~ r2_hidden(X2,X0)
      | ~ v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f33])).

fof(f11,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => ( v1_subset_1(X1,X0)
      <=> X0 != X1 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f27,plain,(
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
    inference(nnf_transformation,[],[f27])).

fof(f70,plain,(
    ! [X0,X1] :
      ( v1_subset_1(X1,X0)
      | X0 = X1
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f43])).

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

fof(f28,plain,(
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
    inference(flattening,[],[f28])).

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
    inference(nnf_transformation,[],[f29])).

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
     => ( ( r2_hidden(k3_yellow_0(X0),sK5)
          | ~ v1_subset_1(sK5,u1_struct_0(X0)) )
        & ( ~ r2_hidden(k3_yellow_0(X0),sK5)
          | v1_subset_1(sK5,u1_struct_0(X0)) )
        & m1_subset_1(sK5,k1_zfmisc_1(u1_struct_0(X0)))
        & v13_waybel_0(sK5,X0)
        & ~ v1_xboole_0(sK5) ) ) ),
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

fof(f48,plain,
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
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4,sK5])],[f45,f47,f46])).

fof(f79,plain,
    ( r2_hidden(k3_yellow_0(sK4),sK5)
    | ~ v1_subset_1(sK5,u1_struct_0(sK4)) ),
    inference(cnf_transformation,[],[f48])).

fof(f77,plain,(
    m1_subset_1(sK5,k1_zfmisc_1(u1_struct_0(sK4))) ),
    inference(cnf_transformation,[],[f48])).

fof(f74,plain,(
    l1_orders_2(sK4) ),
    inference(cnf_transformation,[],[f48])).

fof(f8,axiom,(
    ! [X0] :
      ( l1_orders_2(X0)
     => m1_subset_1(k3_yellow_0(X0),u1_struct_0(X0)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f22,plain,(
    ! [X0] :
      ( m1_subset_1(k3_yellow_0(X0),u1_struct_0(X0))
      | ~ l1_orders_2(X0) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f61,plain,(
    ! [X0] :
      ( m1_subset_1(k3_yellow_0(X0),u1_struct_0(X0))
      | ~ l1_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f75,plain,(
    ~ v1_xboole_0(sK5) ),
    inference(cnf_transformation,[],[f48])).

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

fof(f25,plain,(
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
    inference(flattening,[],[f25])).

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
    inference(nnf_transformation,[],[f26])).

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
     => ( ~ r2_hidden(sK3(X0,X1),X1)
        & r1_orders_2(X0,X2,sK3(X0,X1))
        & r2_hidden(X2,X1)
        & m1_subset_1(sK3(X0,X1),u1_struct_0(X0)) ) ) ),
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
            & r1_orders_2(X0,sK2(X0,X1),X3)
            & r2_hidden(sK2(X0,X1),X1)
            & m1_subset_1(X3,u1_struct_0(X0)) )
        & m1_subset_1(sK2(X0,X1),u1_struct_0(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f42,plain,(
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
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2,sK3])],[f39,f41,f40])).

fof(f63,plain,(
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

fof(f23,plain,(
    ! [X0] :
      ( ! [X1] :
          ( r1_orders_2(X0,k3_yellow_0(X0),X1)
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l1_orders_2(X0)
      | ~ v1_yellow_0(X0)
      | ~ v5_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f24,plain,(
    ! [X0] :
      ( ! [X1] :
          ( r1_orders_2(X0,k3_yellow_0(X0),X1)
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l1_orders_2(X0)
      | ~ v1_yellow_0(X0)
      | ~ v5_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f23])).

fof(f62,plain,(
    ! [X0,X1] :
      ( r1_orders_2(X0,k3_yellow_0(X0),X1)
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | ~ v1_yellow_0(X0)
      | ~ v5_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f73,plain,(
    v1_yellow_0(sK4) ),
    inference(cnf_transformation,[],[f48])).

fof(f71,plain,(
    ~ v2_struct_0(sK4) ),
    inference(cnf_transformation,[],[f48])).

fof(f72,plain,(
    v5_orders_2(sK4) ),
    inference(cnf_transformation,[],[f48])).

fof(f76,plain,(
    v13_waybel_0(sK5,sK4) ),
    inference(cnf_transformation,[],[f48])).

fof(f4,axiom,(
    ! [X0] : k2_subset_1(X0) = X0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f57,plain,(
    ! [X0] : k2_subset_1(X0) = X0 ),
    inference(cnf_transformation,[],[f4])).

fof(f5,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => ! [X2] :
          ( r2_hidden(X2,X1)
         => r2_hidden(X2,X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f19,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( r2_hidden(X2,X0)
          | ~ r2_hidden(X2,X1) )
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f58,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(X2,X0)
      | ~ r2_hidden(X2,X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f52,plain,(
    ! [X0,X1] :
      ( X0 = X1
      | ~ r2_hidden(sK1(X0,X1),X1)
      | ~ r2_hidden(sK1(X0,X1),X0) ) ),
    inference(cnf_transformation,[],[f36])).

fof(f50,plain,(
    ! [X0] :
      ( v1_xboole_0(X0)
      | r2_hidden(sK0(X0),X0) ) ),
    inference(cnf_transformation,[],[f33])).

fof(f6,axiom,(
    ! [X0] : ~ v1_subset_1(k2_subset_1(X0),X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f59,plain,(
    ! [X0] : ~ v1_subset_1(k2_subset_1(X0),X0) ),
    inference(cnf_transformation,[],[f6])).

fof(f78,plain,
    ( ~ r2_hidden(k3_yellow_0(sK4),sK5)
    | v1_subset_1(sK5,u1_struct_0(sK4)) ),
    inference(cnf_transformation,[],[f48])).

cnf(c_11,plain,
    ( m1_subset_1(X0,X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(X1))
    | ~ r2_hidden(X0,X2) ),
    inference(cnf_transformation,[],[f60])).

cnf(c_2480,plain,
    ( m1_subset_1(sK1(X0,sK5),X1)
    | ~ m1_subset_1(sK5,k1_zfmisc_1(X1))
    | ~ r2_hidden(sK1(X0,sK5),sK5) ),
    inference(instantiation,[status(thm)],[c_11])).

cnf(c_5956,plain,
    ( m1_subset_1(sK1(X0,sK5),u1_struct_0(sK4))
    | ~ m1_subset_1(sK5,k1_zfmisc_1(u1_struct_0(sK4)))
    | ~ r2_hidden(sK1(X0,sK5),sK5) ),
    inference(instantiation,[status(thm)],[c_2480])).

cnf(c_18071,plain,
    ( m1_subset_1(sK1(u1_struct_0(sK4),sK5),u1_struct_0(sK4))
    | ~ m1_subset_1(sK5,k1_zfmisc_1(u1_struct_0(sK4)))
    | ~ r2_hidden(sK1(u1_struct_0(sK4),sK5),sK5) ),
    inference(instantiation,[status(thm)],[c_5956])).

cnf(c_7,plain,
    ( ~ m1_subset_1(X0,X1)
    | r2_hidden(X0,X1)
    | v1_xboole_0(X1) ),
    inference(cnf_transformation,[],[f53])).

cnf(c_3963,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(sK4))
    | r2_hidden(X0,u1_struct_0(sK4))
    | v1_xboole_0(u1_struct_0(sK4)) ),
    inference(instantiation,[status(thm)],[c_7])).

cnf(c_10784,plain,
    ( ~ m1_subset_1(sK1(u1_struct_0(sK4),sK5),u1_struct_0(sK4))
    | r2_hidden(sK1(u1_struct_0(sK4),sK5),u1_struct_0(sK4))
    | v1_xboole_0(u1_struct_0(sK4)) ),
    inference(instantiation,[status(thm)],[c_3963])).

cnf(c_3,plain,
    ( r2_hidden(sK1(X0,X1),X1)
    | r2_hidden(sK1(X0,X1),X0)
    | X1 = X0 ),
    inference(cnf_transformation,[],[f51])).

cnf(c_1281,plain,
    ( X0 = X1
    | r2_hidden(sK1(X1,X0),X0) = iProver_top
    | r2_hidden(sK1(X1,X0),X1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3])).

cnf(c_6,plain,
    ( m1_subset_1(X0,X1)
    | ~ r2_hidden(X0,X1)
    | v1_xboole_0(X1) ),
    inference(cnf_transformation,[],[f54])).

cnf(c_1,plain,
    ( ~ r2_hidden(X0,X1)
    | ~ v1_xboole_0(X1) ),
    inference(cnf_transformation,[],[f49])).

cnf(c_182,plain,
    ( ~ r2_hidden(X0,X1)
    | m1_subset_1(X0,X1) ),
    inference(global_propositional_subsumption,[status(thm)],[c_6,c_1])).

cnf(c_183,plain,
    ( m1_subset_1(X0,X1)
    | ~ r2_hidden(X0,X1) ),
    inference(renaming,[status(thm)],[c_182])).

cnf(c_1272,plain,
    ( m1_subset_1(X0,X1) = iProver_top
    | r2_hidden(X0,X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_183])).

cnf(c_2256,plain,
    ( X0 = X1
    | m1_subset_1(sK1(X0,X1),X0) = iProver_top
    | r2_hidden(sK1(X0,X1),X1) = iProver_top ),
    inference(superposition,[status(thm)],[c_1281,c_1272])).

cnf(c_20,plain,
    ( v1_subset_1(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | X0 = X1 ),
    inference(cnf_transformation,[],[f70])).

cnf(c_22,negated_conjecture,
    ( ~ v1_subset_1(sK5,u1_struct_0(sK4))
    | r2_hidden(k3_yellow_0(sK4),sK5) ),
    inference(cnf_transformation,[],[f79])).

cnf(c_233,plain,
    ( ~ v1_subset_1(sK5,u1_struct_0(sK4))
    | r2_hidden(k3_yellow_0(sK4),sK5) ),
    inference(prop_impl,[status(thm)],[c_22])).

cnf(c_448,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | r2_hidden(k3_yellow_0(sK4),sK5)
    | X1 = X0
    | u1_struct_0(sK4) != X1
    | sK5 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_20,c_233])).

cnf(c_449,plain,
    ( ~ m1_subset_1(sK5,k1_zfmisc_1(u1_struct_0(sK4)))
    | r2_hidden(k3_yellow_0(sK4),sK5)
    | u1_struct_0(sK4) = sK5 ),
    inference(unflattening,[status(thm)],[c_448])).

cnf(c_24,negated_conjecture,
    ( m1_subset_1(sK5,k1_zfmisc_1(u1_struct_0(sK4))) ),
    inference(cnf_transformation,[],[f77])).

cnf(c_451,plain,
    ( r2_hidden(k3_yellow_0(sK4),sK5)
    | u1_struct_0(sK4) = sK5 ),
    inference(global_propositional_subsumption,[status(thm)],[c_449,c_24])).

cnf(c_1269,plain,
    ( u1_struct_0(sK4) = sK5
    | r2_hidden(k3_yellow_0(sK4),sK5) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_451])).

cnf(c_2730,plain,
    ( u1_struct_0(sK4) = sK5
    | m1_subset_1(k3_yellow_0(sK4),sK5) = iProver_top ),
    inference(superposition,[status(thm)],[c_1269,c_1272])).

cnf(c_27,negated_conjecture,
    ( l1_orders_2(sK4) ),
    inference(cnf_transformation,[],[f74])).

cnf(c_34,plain,
    ( l1_orders_2(sK4) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_27])).

cnf(c_12,plain,
    ( m1_subset_1(k3_yellow_0(X0),u1_struct_0(X0))
    | ~ l1_orders_2(X0) ),
    inference(cnf_transformation,[],[f61])).

cnf(c_65,plain,
    ( m1_subset_1(k3_yellow_0(X0),u1_struct_0(X0)) = iProver_top
    | l1_orders_2(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_12])).

cnf(c_67,plain,
    ( m1_subset_1(k3_yellow_0(sK4),u1_struct_0(sK4)) = iProver_top
    | l1_orders_2(sK4) != iProver_top ),
    inference(instantiation,[status(thm)],[c_65])).

cnf(c_844,plain,
    ( X0 != X1
    | k3_yellow_0(X0) = k3_yellow_0(X1) ),
    theory(equality)).

cnf(c_854,plain,
    ( k3_yellow_0(sK4) = k3_yellow_0(sK4)
    | sK4 != sK4 ),
    inference(instantiation,[status(thm)],[c_844])).

cnf(c_837,plain,
    ( X0 = X0 ),
    theory(equality)).

cnf(c_860,plain,
    ( sK4 = sK4 ),
    inference(instantiation,[status(thm)],[c_837])).

cnf(c_1684,plain,
    ( sK5 = sK5 ),
    inference(instantiation,[status(thm)],[c_837])).

cnf(c_841,plain,
    ( ~ m1_subset_1(X0,X1)
    | m1_subset_1(X2,X3)
    | X2 != X0
    | X3 != X1 ),
    theory(equality)).

cnf(c_1655,plain,
    ( ~ m1_subset_1(X0,X1)
    | m1_subset_1(X2,sK5)
    | X2 != X0
    | sK5 != X1 ),
    inference(instantiation,[status(thm)],[c_841])).

cnf(c_1856,plain,
    ( m1_subset_1(X0,sK5)
    | ~ m1_subset_1(k3_yellow_0(sK4),u1_struct_0(sK4))
    | X0 != k3_yellow_0(sK4)
    | sK5 != u1_struct_0(sK4) ),
    inference(instantiation,[status(thm)],[c_1655])).

cnf(c_2194,plain,
    ( ~ m1_subset_1(k3_yellow_0(sK4),u1_struct_0(sK4))
    | m1_subset_1(k3_yellow_0(sK4),sK5)
    | k3_yellow_0(sK4) != k3_yellow_0(sK4)
    | sK5 != u1_struct_0(sK4) ),
    inference(instantiation,[status(thm)],[c_1856])).

cnf(c_2196,plain,
    ( k3_yellow_0(sK4) != k3_yellow_0(sK4)
    | sK5 != u1_struct_0(sK4)
    | m1_subset_1(k3_yellow_0(sK4),u1_struct_0(sK4)) != iProver_top
    | m1_subset_1(k3_yellow_0(sK4),sK5) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2194])).

cnf(c_838,plain,
    ( X0 != X1
    | X2 != X1
    | X2 = X0 ),
    theory(equality)).

cnf(c_1632,plain,
    ( X0 != X1
    | sK5 != X1
    | sK5 = X0 ),
    inference(instantiation,[status(thm)],[c_838])).

cnf(c_2209,plain,
    ( X0 != sK5
    | sK5 = X0
    | sK5 != sK5 ),
    inference(instantiation,[status(thm)],[c_1632])).

cnf(c_3122,plain,
    ( u1_struct_0(sK4) != sK5
    | sK5 = u1_struct_0(sK4)
    | sK5 != sK5 ),
    inference(instantiation,[status(thm)],[c_2209])).

cnf(c_5925,plain,
    ( m1_subset_1(k3_yellow_0(sK4),sK5) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_2730,c_34,c_67,c_854,c_860,c_1684,c_2196,c_3122])).

cnf(c_1278,plain,
    ( m1_subset_1(X0,X1) != iProver_top
    | r2_hidden(X0,X1) = iProver_top
    | v1_xboole_0(X1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_7])).

cnf(c_5930,plain,
    ( r2_hidden(k3_yellow_0(sK4),sK5) = iProver_top
    | v1_xboole_0(sK5) = iProver_top ),
    inference(superposition,[status(thm)],[c_5925,c_1278])).

cnf(c_26,negated_conjecture,
    ( ~ v1_xboole_0(sK5) ),
    inference(cnf_transformation,[],[f75])).

cnf(c_35,plain,
    ( v1_xboole_0(sK5) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_26])).

cnf(c_5938,plain,
    ( r2_hidden(k3_yellow_0(sK4),sK5) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_5930,c_35])).

cnf(c_1275,plain,
    ( m1_subset_1(sK5,k1_zfmisc_1(u1_struct_0(sK4))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_24])).

cnf(c_19,plain,
    ( ~ r1_orders_2(X0,X1,X2)
    | ~ v13_waybel_0(X3,X0)
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | ~ m1_subset_1(X1,u1_struct_0(X0))
    | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))
    | ~ r2_hidden(X1,X3)
    | r2_hidden(X2,X3)
    | ~ l1_orders_2(X0) ),
    inference(cnf_transformation,[],[f63])).

cnf(c_13,plain,
    ( r1_orders_2(X0,k3_yellow_0(X0),X1)
    | ~ m1_subset_1(X1,u1_struct_0(X0))
    | v2_struct_0(X0)
    | ~ v5_orders_2(X0)
    | ~ v1_yellow_0(X0)
    | ~ l1_orders_2(X0) ),
    inference(cnf_transformation,[],[f62])).

cnf(c_28,negated_conjecture,
    ( v1_yellow_0(sK4) ),
    inference(cnf_transformation,[],[f73])).

cnf(c_402,plain,
    ( r1_orders_2(X0,k3_yellow_0(X0),X1)
    | ~ m1_subset_1(X1,u1_struct_0(X0))
    | v2_struct_0(X0)
    | ~ v5_orders_2(X0)
    | ~ l1_orders_2(X0)
    | sK4 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_13,c_28])).

cnf(c_403,plain,
    ( r1_orders_2(sK4,k3_yellow_0(sK4),X0)
    | ~ m1_subset_1(X0,u1_struct_0(sK4))
    | v2_struct_0(sK4)
    | ~ v5_orders_2(sK4)
    | ~ l1_orders_2(sK4) ),
    inference(unflattening,[status(thm)],[c_402])).

cnf(c_30,negated_conjecture,
    ( ~ v2_struct_0(sK4) ),
    inference(cnf_transformation,[],[f71])).

cnf(c_29,negated_conjecture,
    ( v5_orders_2(sK4) ),
    inference(cnf_transformation,[],[f72])).

cnf(c_407,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(sK4))
    | r1_orders_2(sK4,k3_yellow_0(sK4),X0) ),
    inference(global_propositional_subsumption,[status(thm)],[c_403,c_30,c_29,c_27])).

cnf(c_408,plain,
    ( r1_orders_2(sK4,k3_yellow_0(sK4),X0)
    | ~ m1_subset_1(X0,u1_struct_0(sK4)) ),
    inference(renaming,[status(thm)],[c_407])).

cnf(c_518,plain,
    ( ~ v13_waybel_0(X0,X1)
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ m1_subset_1(X3,u1_struct_0(X1))
    | ~ m1_subset_1(X4,u1_struct_0(sK4))
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ r2_hidden(X3,X0)
    | r2_hidden(X2,X0)
    | ~ l1_orders_2(X1)
    | X4 != X2
    | k3_yellow_0(sK4) != X3
    | sK4 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_19,c_408])).

cnf(c_519,plain,
    ( ~ v13_waybel_0(X0,sK4)
    | ~ m1_subset_1(X1,u1_struct_0(sK4))
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK4)))
    | ~ m1_subset_1(k3_yellow_0(sK4),u1_struct_0(sK4))
    | r2_hidden(X1,X0)
    | ~ r2_hidden(k3_yellow_0(sK4),X0)
    | ~ l1_orders_2(sK4) ),
    inference(unflattening,[status(thm)],[c_518])).

cnf(c_66,plain,
    ( m1_subset_1(k3_yellow_0(sK4),u1_struct_0(sK4))
    | ~ l1_orders_2(sK4) ),
    inference(instantiation,[status(thm)],[c_12])).

cnf(c_523,plain,
    ( ~ r2_hidden(k3_yellow_0(sK4),X0)
    | r2_hidden(X1,X0)
    | ~ v13_waybel_0(X0,sK4)
    | ~ m1_subset_1(X1,u1_struct_0(sK4))
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK4))) ),
    inference(global_propositional_subsumption,[status(thm)],[c_519,c_27,c_66])).

cnf(c_524,plain,
    ( ~ v13_waybel_0(X0,sK4)
    | ~ m1_subset_1(X1,u1_struct_0(sK4))
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK4)))
    | r2_hidden(X1,X0)
    | ~ r2_hidden(k3_yellow_0(sK4),X0) ),
    inference(renaming,[status(thm)],[c_523])).

cnf(c_1267,plain,
    ( v13_waybel_0(X0,sK4) != iProver_top
    | m1_subset_1(X1,u1_struct_0(sK4)) != iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK4))) != iProver_top
    | r2_hidden(X1,X0) = iProver_top
    | r2_hidden(k3_yellow_0(sK4),X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_524])).

cnf(c_1867,plain,
    ( v13_waybel_0(sK5,sK4) != iProver_top
    | m1_subset_1(X0,u1_struct_0(sK4)) != iProver_top
    | r2_hidden(X0,sK5) = iProver_top
    | r2_hidden(k3_yellow_0(sK4),sK5) != iProver_top ),
    inference(superposition,[status(thm)],[c_1275,c_1267])).

cnf(c_25,negated_conjecture,
    ( v13_waybel_0(sK5,sK4) ),
    inference(cnf_transformation,[],[f76])).

cnf(c_36,plain,
    ( v13_waybel_0(sK5,sK4) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_25])).

cnf(c_1872,plain,
    ( m1_subset_1(X0,u1_struct_0(sK4)) != iProver_top
    | r2_hidden(X0,sK5) = iProver_top
    | r2_hidden(k3_yellow_0(sK4),sK5) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_1867,c_36])).

cnf(c_5945,plain,
    ( m1_subset_1(X0,u1_struct_0(sK4)) != iProver_top
    | r2_hidden(X0,sK5) = iProver_top ),
    inference(superposition,[status(thm)],[c_5938,c_1872])).

cnf(c_6516,plain,
    ( u1_struct_0(sK4) = X0
    | r2_hidden(sK1(u1_struct_0(sK4),X0),X0) = iProver_top
    | r2_hidden(sK1(u1_struct_0(sK4),X0),sK5) = iProver_top ),
    inference(superposition,[status(thm)],[c_2256,c_5945])).

cnf(c_8314,plain,
    ( u1_struct_0(sK4) = sK5
    | r2_hidden(sK1(u1_struct_0(sK4),sK5),sK5) = iProver_top
    | iProver_top != iProver_top ),
    inference(equality_factoring,[status(thm)],[c_6516])).

cnf(c_8316,plain,
    ( u1_struct_0(sK4) = sK5
    | r2_hidden(sK1(u1_struct_0(sK4),sK5),sK5) = iProver_top ),
    inference(equality_resolution_simp,[status(thm)],[c_8314])).

cnf(c_8396,plain,
    ( r2_hidden(sK1(u1_struct_0(sK4),sK5),sK5)
    | u1_struct_0(sK4) = sK5 ),
    inference(predicate_to_equality_rev,[status(thm)],[c_8316])).

cnf(c_1581,plain,
    ( k2_subset_1(u1_struct_0(sK4)) != X0
    | k2_subset_1(u1_struct_0(sK4)) = sK5
    | sK5 != X0 ),
    inference(instantiation,[status(thm)],[c_838])).

cnf(c_6870,plain,
    ( k2_subset_1(u1_struct_0(sK4)) != u1_struct_0(sK4)
    | k2_subset_1(u1_struct_0(sK4)) = sK5
    | sK5 != u1_struct_0(sK4) ),
    inference(instantiation,[status(thm)],[c_1581])).

cnf(c_8,plain,
    ( k2_subset_1(X0) = X0 ),
    inference(cnf_transformation,[],[f57])).

cnf(c_2445,plain,
    ( k2_subset_1(u1_struct_0(sK4)) = u1_struct_0(sK4) ),
    inference(instantiation,[status(thm)],[c_8])).

cnf(c_1975,plain,
    ( ~ r2_hidden(sK0(sK5),u1_struct_0(sK4))
    | ~ v1_xboole_0(u1_struct_0(sK4)) ),
    inference(instantiation,[status(thm)],[c_1])).

cnf(c_9,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | ~ r2_hidden(X2,X0)
    | r2_hidden(X2,X1) ),
    inference(cnf_transformation,[],[f58])).

cnf(c_1591,plain,
    ( ~ m1_subset_1(sK5,k1_zfmisc_1(X0))
    | r2_hidden(sK0(sK5),X0)
    | ~ r2_hidden(sK0(sK5),sK5) ),
    inference(instantiation,[status(thm)],[c_9])).

cnf(c_1735,plain,
    ( ~ m1_subset_1(sK5,k1_zfmisc_1(u1_struct_0(sK4)))
    | r2_hidden(sK0(sK5),u1_struct_0(sK4))
    | ~ r2_hidden(sK0(sK5),sK5) ),
    inference(instantiation,[status(thm)],[c_1591])).

cnf(c_2,plain,
    ( ~ r2_hidden(sK1(X0,X1),X1)
    | ~ r2_hidden(sK1(X0,X1),X0)
    | X1 = X0 ),
    inference(cnf_transformation,[],[f52])).

cnf(c_1542,plain,
    ( ~ r2_hidden(sK1(u1_struct_0(sK4),sK5),u1_struct_0(sK4))
    | ~ r2_hidden(sK1(u1_struct_0(sK4),sK5),sK5)
    | sK5 = u1_struct_0(sK4) ),
    inference(instantiation,[status(thm)],[c_2])).

cnf(c_0,plain,
    ( r2_hidden(sK0(X0),X0)
    | v1_xboole_0(X0) ),
    inference(cnf_transformation,[],[f50])).

cnf(c_1481,plain,
    ( r2_hidden(sK0(sK5),sK5)
    | v1_xboole_0(sK5) ),
    inference(instantiation,[status(thm)],[c_0])).

cnf(c_10,plain,
    ( ~ v1_subset_1(k2_subset_1(X0),X0) ),
    inference(cnf_transformation,[],[f59])).

cnf(c_23,negated_conjecture,
    ( v1_subset_1(sK5,u1_struct_0(sK4))
    | ~ r2_hidden(k3_yellow_0(sK4),sK5) ),
    inference(cnf_transformation,[],[f78])).

cnf(c_231,plain,
    ( v1_subset_1(sK5,u1_struct_0(sK4))
    | ~ r2_hidden(k3_yellow_0(sK4),sK5) ),
    inference(prop_impl,[status(thm)],[c_23])).

cnf(c_436,plain,
    ( ~ r2_hidden(k3_yellow_0(sK4),sK5)
    | u1_struct_0(sK4) != X0
    | k2_subset_1(X0) != sK5 ),
    inference(resolution_lifted,[status(thm)],[c_10,c_231])).

cnf(c_437,plain,
    ( ~ r2_hidden(k3_yellow_0(sK4),sK5)
    | k2_subset_1(u1_struct_0(sK4)) != sK5 ),
    inference(unflattening,[status(thm)],[c_436])).

cnf(c_1270,plain,
    ( k2_subset_1(u1_struct_0(sK4)) != sK5
    | r2_hidden(k3_yellow_0(sK4),sK5) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_437])).

cnf(c_1313,plain,
    ( u1_struct_0(sK4) != sK5
    | r2_hidden(k3_yellow_0(sK4),sK5) != iProver_top ),
    inference(demodulation,[status(thm)],[c_1270,c_8])).

cnf(c_438,plain,
    ( k2_subset_1(u1_struct_0(sK4)) != sK5
    | r2_hidden(k3_yellow_0(sK4),sK5) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_437])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_18071,c_10784,c_8396,c_6870,c_5930,c_2445,c_1975,c_1735,c_1542,c_1481,c_1313,c_438,c_24,c_35,c_26])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.12  % Command    : iproveropt_run.sh %d %s
% 0.12/0.33  % Computer   : n001.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.33  % CPULimit   : 60
% 0.12/0.33  % WCLimit    : 600
% 0.12/0.33  % DateTime   : Tue Dec  1 14:52:59 EST 2020
% 0.12/0.33  % CPUTime    : 
% 0.12/0.33  % Running in FOF mode
% 3.73/0.98  % SZS status Started for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.73/0.98  
% 3.73/0.98  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 3.73/0.98  
% 3.73/0.98  ------  iProver source info
% 3.73/0.98  
% 3.73/0.98  git: date: 2020-06-30 10:37:57 +0100
% 3.73/0.98  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 3.73/0.98  git: non_committed_changes: false
% 3.73/0.98  git: last_make_outside_of_git: false
% 3.73/0.98  
% 3.73/0.98  ------ 
% 3.73/0.98  
% 3.73/0.98  ------ Input Options
% 3.73/0.98  
% 3.73/0.98  --out_options                           all
% 3.73/0.98  --tptp_safe_out                         true
% 3.73/0.98  --problem_path                          ""
% 3.73/0.98  --include_path                          ""
% 3.73/0.98  --clausifier                            res/vclausify_rel
% 3.73/0.98  --clausifier_options                    --mode clausify
% 3.73/0.98  --stdin                                 false
% 3.73/0.98  --stats_out                             all
% 3.73/0.98  
% 3.73/0.98  ------ General Options
% 3.73/0.98  
% 3.73/0.98  --fof                                   false
% 3.73/0.98  --time_out_real                         305.
% 3.73/0.98  --time_out_virtual                      -1.
% 3.73/0.98  --symbol_type_check                     false
% 3.73/0.98  --clausify_out                          false
% 3.73/0.98  --sig_cnt_out                           false
% 3.73/0.98  --trig_cnt_out                          false
% 3.73/0.98  --trig_cnt_out_tolerance                1.
% 3.73/0.98  --trig_cnt_out_sk_spl                   false
% 3.73/0.98  --abstr_cl_out                          false
% 3.73/0.98  
% 3.73/0.98  ------ Global Options
% 3.73/0.98  
% 3.73/0.98  --schedule                              default
% 3.73/0.98  --add_important_lit                     false
% 3.73/0.98  --prop_solver_per_cl                    1000
% 3.73/0.98  --min_unsat_core                        false
% 3.73/0.98  --soft_assumptions                      false
% 3.73/0.98  --soft_lemma_size                       3
% 3.73/0.98  --prop_impl_unit_size                   0
% 3.73/0.98  --prop_impl_unit                        []
% 3.73/0.98  --share_sel_clauses                     true
% 3.73/0.98  --reset_solvers                         false
% 3.73/0.98  --bc_imp_inh                            [conj_cone]
% 3.73/0.98  --conj_cone_tolerance                   3.
% 3.73/0.98  --extra_neg_conj                        none
% 3.73/0.98  --large_theory_mode                     true
% 3.73/0.98  --prolific_symb_bound                   200
% 3.73/0.98  --lt_threshold                          2000
% 3.73/0.98  --clause_weak_htbl                      true
% 3.73/0.98  --gc_record_bc_elim                     false
% 3.73/0.98  
% 3.73/0.98  ------ Preprocessing Options
% 3.73/0.98  
% 3.73/0.98  --preprocessing_flag                    true
% 3.73/0.98  --time_out_prep_mult                    0.1
% 3.73/0.98  --splitting_mode                        input
% 3.73/0.98  --splitting_grd                         true
% 3.73/0.98  --splitting_cvd                         false
% 3.73/0.98  --splitting_cvd_svl                     false
% 3.73/0.98  --splitting_nvd                         32
% 3.73/0.98  --sub_typing                            true
% 3.73/0.98  --prep_gs_sim                           true
% 3.73/0.98  --prep_unflatten                        true
% 3.73/0.98  --prep_res_sim                          true
% 3.73/0.98  --prep_upred                            true
% 3.73/0.98  --prep_sem_filter                       exhaustive
% 3.73/0.98  --prep_sem_filter_out                   false
% 3.73/0.98  --pred_elim                             true
% 3.73/0.98  --res_sim_input                         true
% 3.73/0.98  --eq_ax_congr_red                       true
% 3.73/0.98  --pure_diseq_elim                       true
% 3.73/0.98  --brand_transform                       false
% 3.73/0.98  --non_eq_to_eq                          false
% 3.73/0.98  --prep_def_merge                        true
% 3.73/0.98  --prep_def_merge_prop_impl              false
% 3.73/0.98  --prep_def_merge_mbd                    true
% 3.73/0.98  --prep_def_merge_tr_red                 false
% 3.73/0.98  --prep_def_merge_tr_cl                  false
% 3.73/0.98  --smt_preprocessing                     true
% 3.73/0.98  --smt_ac_axioms                         fast
% 3.73/0.98  --preprocessed_out                      false
% 3.73/0.98  --preprocessed_stats                    false
% 3.73/0.98  
% 3.73/0.98  ------ Abstraction refinement Options
% 3.73/0.98  
% 3.73/0.98  --abstr_ref                             []
% 3.73/0.98  --abstr_ref_prep                        false
% 3.73/0.98  --abstr_ref_until_sat                   false
% 3.73/0.98  --abstr_ref_sig_restrict                funpre
% 3.73/0.98  --abstr_ref_af_restrict_to_split_sk     false
% 3.73/0.98  --abstr_ref_under                       []
% 3.73/0.98  
% 3.73/0.98  ------ SAT Options
% 3.73/0.98  
% 3.73/0.98  --sat_mode                              false
% 3.73/0.98  --sat_fm_restart_options                ""
% 3.73/0.98  --sat_gr_def                            false
% 3.73/0.98  --sat_epr_types                         true
% 3.73/0.98  --sat_non_cyclic_types                  false
% 3.73/0.98  --sat_finite_models                     false
% 3.73/0.98  --sat_fm_lemmas                         false
% 3.73/0.98  --sat_fm_prep                           false
% 3.73/0.98  --sat_fm_uc_incr                        true
% 3.73/0.98  --sat_out_model                         small
% 3.73/0.98  --sat_out_clauses                       false
% 3.73/0.98  
% 3.73/0.98  ------ QBF Options
% 3.73/0.98  
% 3.73/0.98  --qbf_mode                              false
% 3.73/0.98  --qbf_elim_univ                         false
% 3.73/0.98  --qbf_dom_inst                          none
% 3.73/0.98  --qbf_dom_pre_inst                      false
% 3.73/0.98  --qbf_sk_in                             false
% 3.73/0.98  --qbf_pred_elim                         true
% 3.73/0.98  --qbf_split                             512
% 3.73/0.98  
% 3.73/0.98  ------ BMC1 Options
% 3.73/0.98  
% 3.73/0.98  --bmc1_incremental                      false
% 3.73/0.98  --bmc1_axioms                           reachable_all
% 3.73/0.98  --bmc1_min_bound                        0
% 3.73/0.98  --bmc1_max_bound                        -1
% 3.73/0.98  --bmc1_max_bound_default                -1
% 3.73/0.98  --bmc1_symbol_reachability              true
% 3.73/0.98  --bmc1_property_lemmas                  false
% 3.73/0.98  --bmc1_k_induction                      false
% 3.73/0.98  --bmc1_non_equiv_states                 false
% 3.73/0.98  --bmc1_deadlock                         false
% 3.73/0.98  --bmc1_ucm                              false
% 3.73/0.98  --bmc1_add_unsat_core                   none
% 3.73/0.98  --bmc1_unsat_core_children              false
% 3.73/0.98  --bmc1_unsat_core_extrapolate_axioms    false
% 3.73/0.98  --bmc1_out_stat                         full
% 3.73/0.98  --bmc1_ground_init                      false
% 3.73/0.98  --bmc1_pre_inst_next_state              false
% 3.73/0.98  --bmc1_pre_inst_state                   false
% 3.73/0.98  --bmc1_pre_inst_reach_state             false
% 3.73/0.98  --bmc1_out_unsat_core                   false
% 3.73/0.98  --bmc1_aig_witness_out                  false
% 3.73/0.98  --bmc1_verbose                          false
% 3.73/0.98  --bmc1_dump_clauses_tptp                false
% 3.73/0.98  --bmc1_dump_unsat_core_tptp             false
% 3.73/0.98  --bmc1_dump_file                        -
% 3.73/0.98  --bmc1_ucm_expand_uc_limit              128
% 3.73/0.98  --bmc1_ucm_n_expand_iterations          6
% 3.73/0.98  --bmc1_ucm_extend_mode                  1
% 3.73/0.98  --bmc1_ucm_init_mode                    2
% 3.73/0.98  --bmc1_ucm_cone_mode                    none
% 3.73/0.98  --bmc1_ucm_reduced_relation_type        0
% 3.73/0.98  --bmc1_ucm_relax_model                  4
% 3.73/0.98  --bmc1_ucm_full_tr_after_sat            true
% 3.73/0.98  --bmc1_ucm_expand_neg_assumptions       false
% 3.73/0.98  --bmc1_ucm_layered_model                none
% 3.73/0.98  --bmc1_ucm_max_lemma_size               10
% 3.73/0.98  
% 3.73/0.98  ------ AIG Options
% 3.73/0.98  
% 3.73/0.98  --aig_mode                              false
% 3.73/0.98  
% 3.73/0.98  ------ Instantiation Options
% 3.73/0.98  
% 3.73/0.98  --instantiation_flag                    true
% 3.73/0.98  --inst_sos_flag                         false
% 3.73/0.98  --inst_sos_phase                        true
% 3.73/0.98  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 3.73/0.98  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 3.73/0.98  --inst_lit_sel_side                     num_symb
% 3.73/0.98  --inst_solver_per_active                1400
% 3.73/0.98  --inst_solver_calls_frac                1.
% 3.73/0.98  --inst_passive_queue_type               priority_queues
% 3.73/0.98  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 3.73/0.98  --inst_passive_queues_freq              [25;2]
% 3.73/0.98  --inst_dismatching                      true
% 3.73/0.98  --inst_eager_unprocessed_to_passive     true
% 3.73/0.98  --inst_prop_sim_given                   true
% 3.73/0.98  --inst_prop_sim_new                     false
% 3.73/0.98  --inst_subs_new                         false
% 3.73/0.98  --inst_eq_res_simp                      false
% 3.73/0.98  --inst_subs_given                       false
% 3.73/0.98  --inst_orphan_elimination               true
% 3.73/0.98  --inst_learning_loop_flag               true
% 3.73/0.98  --inst_learning_start                   3000
% 3.73/0.98  --inst_learning_factor                  2
% 3.73/0.98  --inst_start_prop_sim_after_learn       3
% 3.73/0.98  --inst_sel_renew                        solver
% 3.73/0.98  --inst_lit_activity_flag                true
% 3.73/0.98  --inst_restr_to_given                   false
% 3.73/0.98  --inst_activity_threshold               500
% 3.73/0.98  --inst_out_proof                        true
% 3.73/0.98  
% 3.73/0.98  ------ Resolution Options
% 3.73/0.98  
% 3.73/0.98  --resolution_flag                       true
% 3.73/0.98  --res_lit_sel                           adaptive
% 3.73/0.98  --res_lit_sel_side                      none
% 3.73/0.98  --res_ordering                          kbo
% 3.73/0.98  --res_to_prop_solver                    active
% 3.73/0.98  --res_prop_simpl_new                    false
% 3.73/0.98  --res_prop_simpl_given                  true
% 3.73/0.98  --res_passive_queue_type                priority_queues
% 3.73/0.98  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 3.73/0.98  --res_passive_queues_freq               [15;5]
% 3.73/0.98  --res_forward_subs                      full
% 3.73/0.98  --res_backward_subs                     full
% 3.73/0.98  --res_forward_subs_resolution           true
% 3.73/0.98  --res_backward_subs_resolution          true
% 3.73/0.98  --res_orphan_elimination                true
% 3.73/0.98  --res_time_limit                        2.
% 3.73/0.98  --res_out_proof                         true
% 3.73/0.98  
% 3.73/0.98  ------ Superposition Options
% 3.73/0.98  
% 3.73/0.98  --superposition_flag                    true
% 3.73/0.98  --sup_passive_queue_type                priority_queues
% 3.73/0.98  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 3.73/0.98  --sup_passive_queues_freq               [8;1;4]
% 3.73/0.98  --demod_completeness_check              fast
% 3.73/0.98  --demod_use_ground                      true
% 3.73/0.98  --sup_to_prop_solver                    passive
% 3.73/0.98  --sup_prop_simpl_new                    true
% 3.73/0.98  --sup_prop_simpl_given                  true
% 3.73/0.98  --sup_fun_splitting                     false
% 3.73/0.98  --sup_smt_interval                      50000
% 3.73/0.98  
% 3.73/0.98  ------ Superposition Simplification Setup
% 3.73/0.98  
% 3.73/0.98  --sup_indices_passive                   []
% 3.73/0.98  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.73/0.98  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.73/0.98  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.73/0.98  --sup_full_triv                         [TrivRules;PropSubs]
% 3.73/0.98  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.73/0.98  --sup_full_bw                           [BwDemod]
% 3.73/0.98  --sup_immed_triv                        [TrivRules]
% 3.73/0.98  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 3.73/0.98  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.73/0.98  --sup_immed_bw_main                     []
% 3.73/0.98  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 3.73/0.98  --sup_input_triv                        [Unflattening;TrivRules]
% 3.73/0.98  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.73/0.98  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 3.73/0.98  
% 3.73/0.98  ------ Combination Options
% 3.73/0.98  
% 3.73/0.98  --comb_res_mult                         3
% 3.73/0.98  --comb_sup_mult                         2
% 3.73/0.98  --comb_inst_mult                        10
% 3.73/0.98  
% 3.73/0.98  ------ Debug Options
% 3.73/0.98  
% 3.73/0.98  --dbg_backtrace                         false
% 3.73/0.98  --dbg_dump_prop_clauses                 false
% 3.73/0.98  --dbg_dump_prop_clauses_file            -
% 3.73/0.98  --dbg_out_stat                          false
% 3.73/0.98  ------ Parsing...
% 3.73/0.98  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 3.73/0.98  
% 3.73/0.98  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe:1:0s pe:2:0s pe:4:0s pe_e  sf_s  rm: 7 0s  sf_e  pe_s  pe_e 
% 3.73/0.98  
% 3.73/0.98  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 3.73/0.98  
% 3.73/0.98  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 3.73/0.98  ------ Proving...
% 3.73/0.98  ------ Problem Properties 
% 3.73/0.98  
% 3.73/0.98  
% 3.73/0.98  clauses                                 25
% 3.73/0.98  conjectures                             3
% 3.73/0.98  EPR                                     7
% 3.73/0.98  Horn                                    17
% 3.73/0.98  unary                                   5
% 3.73/0.98  binary                                  6
% 3.73/0.98  lits                                    64
% 3.73/0.98  lits eq                                 7
% 3.73/0.98  fd_pure                                 0
% 3.73/0.98  fd_pseudo                               0
% 3.73/0.98  fd_cond                                 0
% 3.73/0.98  fd_pseudo_cond                          2
% 3.73/0.98  AC symbols                              0
% 3.73/0.98  
% 3.73/0.98  ------ Schedule dynamic 5 is on 
% 3.73/0.98  
% 3.73/0.98  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" Time Limit: 10.
% 3.73/0.98  
% 3.73/0.98  
% 3.73/0.98  ------ 
% 3.73/0.98  Current options:
% 3.73/0.98  ------ 
% 3.73/0.98  
% 3.73/0.98  ------ Input Options
% 3.73/0.98  
% 3.73/0.98  --out_options                           all
% 3.73/0.98  --tptp_safe_out                         true
% 3.73/0.98  --problem_path                          ""
% 3.73/0.98  --include_path                          ""
% 3.73/0.98  --clausifier                            res/vclausify_rel
% 3.73/0.98  --clausifier_options                    --mode clausify
% 3.73/0.98  --stdin                                 false
% 3.73/0.98  --stats_out                             all
% 3.73/0.98  
% 3.73/0.98  ------ General Options
% 3.73/0.98  
% 3.73/0.98  --fof                                   false
% 3.73/0.98  --time_out_real                         305.
% 3.73/0.98  --time_out_virtual                      -1.
% 3.73/0.98  --symbol_type_check                     false
% 3.73/0.98  --clausify_out                          false
% 3.73/0.98  --sig_cnt_out                           false
% 3.73/0.98  --trig_cnt_out                          false
% 3.73/0.98  --trig_cnt_out_tolerance                1.
% 3.73/0.98  --trig_cnt_out_sk_spl                   false
% 3.73/0.98  --abstr_cl_out                          false
% 3.73/0.98  
% 3.73/0.98  ------ Global Options
% 3.73/0.98  
% 3.73/0.98  --schedule                              default
% 3.73/0.98  --add_important_lit                     false
% 3.73/0.98  --prop_solver_per_cl                    1000
% 3.73/0.98  --min_unsat_core                        false
% 3.73/0.98  --soft_assumptions                      false
% 3.73/0.98  --soft_lemma_size                       3
% 3.73/0.98  --prop_impl_unit_size                   0
% 3.73/0.98  --prop_impl_unit                        []
% 3.73/0.98  --share_sel_clauses                     true
% 3.73/0.98  --reset_solvers                         false
% 3.73/0.98  --bc_imp_inh                            [conj_cone]
% 3.73/0.98  --conj_cone_tolerance                   3.
% 3.73/0.98  --extra_neg_conj                        none
% 3.73/0.98  --large_theory_mode                     true
% 3.73/0.98  --prolific_symb_bound                   200
% 3.73/0.98  --lt_threshold                          2000
% 3.73/0.98  --clause_weak_htbl                      true
% 3.73/0.98  --gc_record_bc_elim                     false
% 3.73/0.98  
% 3.73/0.98  ------ Preprocessing Options
% 3.73/0.98  
% 3.73/0.98  --preprocessing_flag                    true
% 3.73/0.98  --time_out_prep_mult                    0.1
% 3.73/0.98  --splitting_mode                        input
% 3.73/0.98  --splitting_grd                         true
% 3.73/0.98  --splitting_cvd                         false
% 3.73/0.98  --splitting_cvd_svl                     false
% 3.73/0.98  --splitting_nvd                         32
% 3.73/0.98  --sub_typing                            true
% 3.73/0.98  --prep_gs_sim                           true
% 3.73/0.98  --prep_unflatten                        true
% 3.73/0.98  --prep_res_sim                          true
% 3.73/0.98  --prep_upred                            true
% 3.73/0.98  --prep_sem_filter                       exhaustive
% 3.73/0.98  --prep_sem_filter_out                   false
% 3.73/0.98  --pred_elim                             true
% 3.73/0.98  --res_sim_input                         true
% 3.73/0.98  --eq_ax_congr_red                       true
% 3.73/0.98  --pure_diseq_elim                       true
% 3.73/0.98  --brand_transform                       false
% 3.73/0.98  --non_eq_to_eq                          false
% 3.73/0.98  --prep_def_merge                        true
% 3.73/0.98  --prep_def_merge_prop_impl              false
% 3.73/0.98  --prep_def_merge_mbd                    true
% 3.73/0.98  --prep_def_merge_tr_red                 false
% 3.73/0.98  --prep_def_merge_tr_cl                  false
% 3.73/0.98  --smt_preprocessing                     true
% 3.73/0.98  --smt_ac_axioms                         fast
% 3.73/0.98  --preprocessed_out                      false
% 3.73/0.98  --preprocessed_stats                    false
% 3.73/0.98  
% 3.73/0.98  ------ Abstraction refinement Options
% 3.73/0.98  
% 3.73/0.98  --abstr_ref                             []
% 3.73/0.98  --abstr_ref_prep                        false
% 3.73/0.98  --abstr_ref_until_sat                   false
% 3.73/0.98  --abstr_ref_sig_restrict                funpre
% 3.73/0.98  --abstr_ref_af_restrict_to_split_sk     false
% 3.73/0.98  --abstr_ref_under                       []
% 3.73/0.98  
% 3.73/0.98  ------ SAT Options
% 3.73/0.98  
% 3.73/0.98  --sat_mode                              false
% 3.73/0.98  --sat_fm_restart_options                ""
% 3.73/0.98  --sat_gr_def                            false
% 3.73/0.98  --sat_epr_types                         true
% 3.73/0.98  --sat_non_cyclic_types                  false
% 3.73/0.98  --sat_finite_models                     false
% 3.73/0.98  --sat_fm_lemmas                         false
% 3.73/0.98  --sat_fm_prep                           false
% 3.73/0.98  --sat_fm_uc_incr                        true
% 3.73/0.98  --sat_out_model                         small
% 3.73/0.98  --sat_out_clauses                       false
% 3.73/0.98  
% 3.73/0.98  ------ QBF Options
% 3.73/0.98  
% 3.73/0.98  --qbf_mode                              false
% 3.73/0.98  --qbf_elim_univ                         false
% 3.73/0.98  --qbf_dom_inst                          none
% 3.73/0.98  --qbf_dom_pre_inst                      false
% 3.73/0.98  --qbf_sk_in                             false
% 3.73/0.98  --qbf_pred_elim                         true
% 3.73/0.98  --qbf_split                             512
% 3.73/0.98  
% 3.73/0.98  ------ BMC1 Options
% 3.73/0.98  
% 3.73/0.98  --bmc1_incremental                      false
% 3.73/0.98  --bmc1_axioms                           reachable_all
% 3.73/0.98  --bmc1_min_bound                        0
% 3.73/0.98  --bmc1_max_bound                        -1
% 3.73/0.98  --bmc1_max_bound_default                -1
% 3.73/0.98  --bmc1_symbol_reachability              true
% 3.73/0.98  --bmc1_property_lemmas                  false
% 3.73/0.98  --bmc1_k_induction                      false
% 3.73/0.98  --bmc1_non_equiv_states                 false
% 3.73/0.98  --bmc1_deadlock                         false
% 3.73/0.98  --bmc1_ucm                              false
% 3.73/0.98  --bmc1_add_unsat_core                   none
% 3.73/0.98  --bmc1_unsat_core_children              false
% 3.73/0.98  --bmc1_unsat_core_extrapolate_axioms    false
% 3.73/0.98  --bmc1_out_stat                         full
% 3.73/0.98  --bmc1_ground_init                      false
% 3.73/0.98  --bmc1_pre_inst_next_state              false
% 3.73/0.98  --bmc1_pre_inst_state                   false
% 3.73/0.98  --bmc1_pre_inst_reach_state             false
% 3.73/0.98  --bmc1_out_unsat_core                   false
% 3.73/0.98  --bmc1_aig_witness_out                  false
% 3.73/0.98  --bmc1_verbose                          false
% 3.73/0.98  --bmc1_dump_clauses_tptp                false
% 3.73/0.98  --bmc1_dump_unsat_core_tptp             false
% 3.73/0.98  --bmc1_dump_file                        -
% 3.73/0.98  --bmc1_ucm_expand_uc_limit              128
% 3.73/0.98  --bmc1_ucm_n_expand_iterations          6
% 3.73/0.98  --bmc1_ucm_extend_mode                  1
% 3.73/0.98  --bmc1_ucm_init_mode                    2
% 3.73/0.98  --bmc1_ucm_cone_mode                    none
% 3.73/0.98  --bmc1_ucm_reduced_relation_type        0
% 3.73/0.98  --bmc1_ucm_relax_model                  4
% 3.73/0.98  --bmc1_ucm_full_tr_after_sat            true
% 3.73/0.98  --bmc1_ucm_expand_neg_assumptions       false
% 3.73/0.98  --bmc1_ucm_layered_model                none
% 3.73/0.98  --bmc1_ucm_max_lemma_size               10
% 3.73/0.98  
% 3.73/0.98  ------ AIG Options
% 3.73/0.98  
% 3.73/0.98  --aig_mode                              false
% 3.73/0.98  
% 3.73/0.98  ------ Instantiation Options
% 3.73/0.98  
% 3.73/0.98  --instantiation_flag                    true
% 3.73/0.98  --inst_sos_flag                         false
% 3.73/0.98  --inst_sos_phase                        true
% 3.73/0.98  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 3.73/0.98  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 3.73/0.98  --inst_lit_sel_side                     none
% 3.73/0.98  --inst_solver_per_active                1400
% 3.73/0.98  --inst_solver_calls_frac                1.
% 3.73/0.98  --inst_passive_queue_type               priority_queues
% 3.73/0.98  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 3.73/0.98  --inst_passive_queues_freq              [25;2]
% 3.73/0.98  --inst_dismatching                      true
% 3.73/0.98  --inst_eager_unprocessed_to_passive     true
% 3.73/0.98  --inst_prop_sim_given                   true
% 3.73/0.98  --inst_prop_sim_new                     false
% 3.73/0.98  --inst_subs_new                         false
% 3.73/0.98  --inst_eq_res_simp                      false
% 3.73/0.98  --inst_subs_given                       false
% 3.73/0.98  --inst_orphan_elimination               true
% 3.73/0.98  --inst_learning_loop_flag               true
% 3.73/0.98  --inst_learning_start                   3000
% 3.73/0.98  --inst_learning_factor                  2
% 3.73/0.98  --inst_start_prop_sim_after_learn       3
% 3.73/0.98  --inst_sel_renew                        solver
% 3.73/0.98  --inst_lit_activity_flag                true
% 3.73/0.98  --inst_restr_to_given                   false
% 3.73/0.98  --inst_activity_threshold               500
% 3.73/0.98  --inst_out_proof                        true
% 3.73/0.98  
% 3.73/0.98  ------ Resolution Options
% 3.73/0.98  
% 3.73/0.98  --resolution_flag                       false
% 3.73/0.98  --res_lit_sel                           adaptive
% 3.73/0.98  --res_lit_sel_side                      none
% 3.73/0.98  --res_ordering                          kbo
% 3.73/0.98  --res_to_prop_solver                    active
% 3.73/0.98  --res_prop_simpl_new                    false
% 3.73/0.98  --res_prop_simpl_given                  true
% 3.73/0.98  --res_passive_queue_type                priority_queues
% 3.73/0.98  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 3.73/0.98  --res_passive_queues_freq               [15;5]
% 3.73/0.98  --res_forward_subs                      full
% 3.73/0.98  --res_backward_subs                     full
% 3.73/0.98  --res_forward_subs_resolution           true
% 3.73/0.98  --res_backward_subs_resolution          true
% 3.73/0.98  --res_orphan_elimination                true
% 3.73/0.98  --res_time_limit                        2.
% 3.73/0.98  --res_out_proof                         true
% 3.73/0.98  
% 3.73/0.98  ------ Superposition Options
% 3.73/0.98  
% 3.73/0.98  --superposition_flag                    true
% 3.73/0.98  --sup_passive_queue_type                priority_queues
% 3.73/0.98  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 3.73/0.98  --sup_passive_queues_freq               [8;1;4]
% 3.73/0.98  --demod_completeness_check              fast
% 3.73/0.98  --demod_use_ground                      true
% 3.73/0.98  --sup_to_prop_solver                    passive
% 3.73/0.98  --sup_prop_simpl_new                    true
% 3.73/0.98  --sup_prop_simpl_given                  true
% 3.73/0.98  --sup_fun_splitting                     false
% 3.73/0.98  --sup_smt_interval                      50000
% 3.73/0.98  
% 3.73/0.98  ------ Superposition Simplification Setup
% 3.73/0.98  
% 3.73/0.98  --sup_indices_passive                   []
% 3.73/0.98  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.73/0.98  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.73/0.98  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.73/0.98  --sup_full_triv                         [TrivRules;PropSubs]
% 3.73/0.98  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.73/0.98  --sup_full_bw                           [BwDemod]
% 3.73/0.98  --sup_immed_triv                        [TrivRules]
% 3.73/0.98  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 3.73/0.98  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.73/0.98  --sup_immed_bw_main                     []
% 3.73/0.98  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 3.73/0.98  --sup_input_triv                        [Unflattening;TrivRules]
% 3.73/0.98  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.73/0.98  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 3.73/0.98  
% 3.73/0.98  ------ Combination Options
% 3.73/0.98  
% 3.73/0.98  --comb_res_mult                         3
% 3.73/0.98  --comb_sup_mult                         2
% 3.73/0.98  --comb_inst_mult                        10
% 3.73/0.98  
% 3.73/0.98  ------ Debug Options
% 3.73/0.98  
% 3.73/0.98  --dbg_backtrace                         false
% 3.73/0.98  --dbg_dump_prop_clauses                 false
% 3.73/0.98  --dbg_dump_prop_clauses_file            -
% 3.73/0.98  --dbg_out_stat                          false
% 3.73/0.98  
% 3.73/0.98  
% 3.73/0.98  
% 3.73/0.98  
% 3.73/0.98  ------ Proving...
% 3.73/0.98  
% 3.73/0.98  
% 3.73/0.98  % SZS status Theorem for theBenchmark.p
% 3.73/0.98  
% 3.73/0.98  % SZS output start CNFRefutation for theBenchmark.p
% 3.73/0.98  
% 3.73/0.98  fof(f7,axiom,(
% 3.73/0.98    ! [X0,X1,X2] : ((m1_subset_1(X1,k1_zfmisc_1(X2)) & r2_hidden(X0,X1)) => m1_subset_1(X0,X2))),
% 3.73/0.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.73/0.98  
% 3.73/0.98  fof(f20,plain,(
% 3.73/0.98    ! [X0,X1,X2] : (m1_subset_1(X0,X2) | (~m1_subset_1(X1,k1_zfmisc_1(X2)) | ~r2_hidden(X0,X1)))),
% 3.73/0.98    inference(ennf_transformation,[],[f7])).
% 3.73/0.98  
% 3.73/0.98  fof(f21,plain,(
% 3.73/0.98    ! [X0,X1,X2] : (m1_subset_1(X0,X2) | ~m1_subset_1(X1,k1_zfmisc_1(X2)) | ~r2_hidden(X0,X1))),
% 3.73/0.98    inference(flattening,[],[f20])).
% 3.73/0.98  
% 3.73/0.98  fof(f60,plain,(
% 3.73/0.98    ( ! [X2,X0,X1] : (m1_subset_1(X0,X2) | ~m1_subset_1(X1,k1_zfmisc_1(X2)) | ~r2_hidden(X0,X1)) )),
% 3.73/0.98    inference(cnf_transformation,[],[f21])).
% 3.73/0.98  
% 3.73/0.98  fof(f3,axiom,(
% 3.73/0.98    ! [X0,X1] : ((v1_xboole_0(X0) => (m1_subset_1(X1,X0) <=> v1_xboole_0(X1))) & (~v1_xboole_0(X0) => (m1_subset_1(X1,X0) <=> r2_hidden(X1,X0))))),
% 3.73/0.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.73/0.98  
% 3.73/0.98  fof(f18,plain,(
% 3.73/0.98    ! [X0,X1] : (((m1_subset_1(X1,X0) <=> v1_xboole_0(X1)) | ~v1_xboole_0(X0)) & ((m1_subset_1(X1,X0) <=> r2_hidden(X1,X0)) | v1_xboole_0(X0)))),
% 3.73/0.98    inference(ennf_transformation,[],[f3])).
% 3.73/0.98  
% 3.73/0.98  fof(f37,plain,(
% 3.73/0.98    ! [X0,X1] : ((((m1_subset_1(X1,X0) | ~v1_xboole_0(X1)) & (v1_xboole_0(X1) | ~m1_subset_1(X1,X0))) | ~v1_xboole_0(X0)) & (((m1_subset_1(X1,X0) | ~r2_hidden(X1,X0)) & (r2_hidden(X1,X0) | ~m1_subset_1(X1,X0))) | v1_xboole_0(X0)))),
% 3.73/0.98    inference(nnf_transformation,[],[f18])).
% 3.73/0.98  
% 3.73/0.98  fof(f53,plain,(
% 3.73/0.98    ( ! [X0,X1] : (r2_hidden(X1,X0) | ~m1_subset_1(X1,X0) | v1_xboole_0(X0)) )),
% 3.73/0.98    inference(cnf_transformation,[],[f37])).
% 3.73/0.98  
% 3.73/0.98  fof(f2,axiom,(
% 3.73/0.98    ! [X0,X1] : (! [X2] : (r2_hidden(X2,X0) <=> r2_hidden(X2,X1)) => X0 = X1)),
% 3.73/0.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.73/0.98  
% 3.73/0.98  fof(f17,plain,(
% 3.73/0.98    ! [X0,X1] : (X0 = X1 | ? [X2] : (r2_hidden(X2,X0) <~> r2_hidden(X2,X1)))),
% 3.73/0.98    inference(ennf_transformation,[],[f2])).
% 3.73/0.98  
% 3.73/0.98  fof(f34,plain,(
% 3.73/0.98    ! [X0,X1] : (X0 = X1 | ? [X2] : ((~r2_hidden(X2,X1) | ~r2_hidden(X2,X0)) & (r2_hidden(X2,X1) | r2_hidden(X2,X0))))),
% 3.73/0.98    inference(nnf_transformation,[],[f17])).
% 3.73/0.98  
% 3.73/0.98  fof(f35,plain,(
% 3.73/0.98    ! [X1,X0] : (? [X2] : ((~r2_hidden(X2,X1) | ~r2_hidden(X2,X0)) & (r2_hidden(X2,X1) | r2_hidden(X2,X0))) => ((~r2_hidden(sK1(X0,X1),X1) | ~r2_hidden(sK1(X0,X1),X0)) & (r2_hidden(sK1(X0,X1),X1) | r2_hidden(sK1(X0,X1),X0))))),
% 3.73/0.98    introduced(choice_axiom,[])).
% 3.73/0.98  
% 3.73/0.98  fof(f36,plain,(
% 3.73/0.98    ! [X0,X1] : (X0 = X1 | ((~r2_hidden(sK1(X0,X1),X1) | ~r2_hidden(sK1(X0,X1),X0)) & (r2_hidden(sK1(X0,X1),X1) | r2_hidden(sK1(X0,X1),X0))))),
% 3.73/0.98    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1])],[f34,f35])).
% 3.73/0.98  
% 3.73/0.98  fof(f51,plain,(
% 3.73/0.98    ( ! [X0,X1] : (X0 = X1 | r2_hidden(sK1(X0,X1),X1) | r2_hidden(sK1(X0,X1),X0)) )),
% 3.73/0.98    inference(cnf_transformation,[],[f36])).
% 3.73/0.98  
% 3.73/0.98  fof(f54,plain,(
% 3.73/0.98    ( ! [X0,X1] : (m1_subset_1(X1,X0) | ~r2_hidden(X1,X0) | v1_xboole_0(X0)) )),
% 3.73/0.98    inference(cnf_transformation,[],[f37])).
% 3.73/0.98  
% 3.73/0.98  fof(f1,axiom,(
% 3.73/0.98    ! [X0] : (v1_xboole_0(X0) <=> ! [X1] : ~r2_hidden(X1,X0))),
% 3.73/0.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.73/0.98  
% 3.73/0.98  fof(f30,plain,(
% 3.73/0.98    ! [X0] : ((v1_xboole_0(X0) | ? [X1] : r2_hidden(X1,X0)) & (! [X1] : ~r2_hidden(X1,X0) | ~v1_xboole_0(X0)))),
% 3.73/0.98    inference(nnf_transformation,[],[f1])).
% 3.73/0.98  
% 3.73/0.98  fof(f31,plain,(
% 3.73/0.98    ! [X0] : ((v1_xboole_0(X0) | ? [X1] : r2_hidden(X1,X0)) & (! [X2] : ~r2_hidden(X2,X0) | ~v1_xboole_0(X0)))),
% 3.73/0.98    inference(rectify,[],[f30])).
% 3.73/0.98  
% 3.73/0.98  fof(f32,plain,(
% 3.73/0.98    ! [X0] : (? [X1] : r2_hidden(X1,X0) => r2_hidden(sK0(X0),X0))),
% 3.73/0.98    introduced(choice_axiom,[])).
% 3.73/0.98  
% 3.73/0.98  fof(f33,plain,(
% 3.73/0.98    ! [X0] : ((v1_xboole_0(X0) | r2_hidden(sK0(X0),X0)) & (! [X2] : ~r2_hidden(X2,X0) | ~v1_xboole_0(X0)))),
% 3.73/0.98    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f31,f32])).
% 3.73/0.98  
% 3.73/0.98  fof(f49,plain,(
% 3.73/0.98    ( ! [X2,X0] : (~r2_hidden(X2,X0) | ~v1_xboole_0(X0)) )),
% 3.73/0.98    inference(cnf_transformation,[],[f33])).
% 3.73/0.98  
% 3.73/0.98  fof(f11,axiom,(
% 3.73/0.98    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => (v1_subset_1(X1,X0) <=> X0 != X1))),
% 3.73/0.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.73/0.98  
% 3.73/0.98  fof(f27,plain,(
% 3.73/0.98    ! [X0,X1] : ((v1_subset_1(X1,X0) <=> X0 != X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 3.73/0.98    inference(ennf_transformation,[],[f11])).
% 3.73/0.98  
% 3.73/0.98  fof(f43,plain,(
% 3.73/0.98    ! [X0,X1] : (((v1_subset_1(X1,X0) | X0 = X1) & (X0 != X1 | ~v1_subset_1(X1,X0))) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 3.73/0.98    inference(nnf_transformation,[],[f27])).
% 3.73/0.98  
% 3.73/0.98  fof(f70,plain,(
% 3.73/0.98    ( ! [X0,X1] : (v1_subset_1(X1,X0) | X0 = X1 | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 3.73/0.98    inference(cnf_transformation,[],[f43])).
% 3.73/0.98  
% 3.73/0.98  fof(f12,conjecture,(
% 3.73/0.98    ! [X0] : ((l1_orders_2(X0) & v1_yellow_0(X0) & v5_orders_2(X0) & v4_orders_2(X0) & v3_orders_2(X0) & ~v2_struct_0(X0)) => ! [X1] : ((m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & v13_waybel_0(X1,X0) & v2_waybel_0(X1,X0) & ~v1_xboole_0(X1)) => (v1_subset_1(X1,u1_struct_0(X0)) <=> ~r2_hidden(k3_yellow_0(X0),X1))))),
% 3.73/0.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.73/0.98  
% 3.73/0.98  fof(f13,negated_conjecture,(
% 3.73/0.98    ~! [X0] : ((l1_orders_2(X0) & v1_yellow_0(X0) & v5_orders_2(X0) & v4_orders_2(X0) & v3_orders_2(X0) & ~v2_struct_0(X0)) => ! [X1] : ((m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & v13_waybel_0(X1,X0) & v2_waybel_0(X1,X0) & ~v1_xboole_0(X1)) => (v1_subset_1(X1,u1_struct_0(X0)) <=> ~r2_hidden(k3_yellow_0(X0),X1))))),
% 3.73/0.98    inference(negated_conjecture,[],[f12])).
% 3.73/0.98  
% 3.73/0.98  fof(f14,plain,(
% 3.73/0.98    ~! [X0] : ((l1_orders_2(X0) & v1_yellow_0(X0) & v5_orders_2(X0) & v4_orders_2(X0) & v3_orders_2(X0) & ~v2_struct_0(X0)) => ! [X1] : ((m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & v13_waybel_0(X1,X0) & ~v1_xboole_0(X1)) => (v1_subset_1(X1,u1_struct_0(X0)) <=> ~r2_hidden(k3_yellow_0(X0),X1))))),
% 3.73/0.98    inference(pure_predicate_removal,[],[f13])).
% 3.73/0.98  
% 3.73/0.98  fof(f15,plain,(
% 3.73/0.98    ~! [X0] : ((l1_orders_2(X0) & v1_yellow_0(X0) & v5_orders_2(X0) & v3_orders_2(X0) & ~v2_struct_0(X0)) => ! [X1] : ((m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & v13_waybel_0(X1,X0) & ~v1_xboole_0(X1)) => (v1_subset_1(X1,u1_struct_0(X0)) <=> ~r2_hidden(k3_yellow_0(X0),X1))))),
% 3.73/0.98    inference(pure_predicate_removal,[],[f14])).
% 3.73/0.98  
% 3.73/0.98  fof(f16,plain,(
% 3.73/0.98    ~! [X0] : ((l1_orders_2(X0) & v1_yellow_0(X0) & v5_orders_2(X0) & ~v2_struct_0(X0)) => ! [X1] : ((m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & v13_waybel_0(X1,X0) & ~v1_xboole_0(X1)) => (v1_subset_1(X1,u1_struct_0(X0)) <=> ~r2_hidden(k3_yellow_0(X0),X1))))),
% 3.73/0.98    inference(pure_predicate_removal,[],[f15])).
% 3.73/0.98  
% 3.73/0.98  fof(f28,plain,(
% 3.73/0.98    ? [X0] : (? [X1] : ((v1_subset_1(X1,u1_struct_0(X0)) <~> ~r2_hidden(k3_yellow_0(X0),X1)) & (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & v13_waybel_0(X1,X0) & ~v1_xboole_0(X1))) & (l1_orders_2(X0) & v1_yellow_0(X0) & v5_orders_2(X0) & ~v2_struct_0(X0)))),
% 3.73/0.98    inference(ennf_transformation,[],[f16])).
% 3.73/0.98  
% 3.73/0.98  fof(f29,plain,(
% 3.73/0.98    ? [X0] : (? [X1] : ((v1_subset_1(X1,u1_struct_0(X0)) <~> ~r2_hidden(k3_yellow_0(X0),X1)) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & v13_waybel_0(X1,X0) & ~v1_xboole_0(X1)) & l1_orders_2(X0) & v1_yellow_0(X0) & v5_orders_2(X0) & ~v2_struct_0(X0))),
% 3.73/0.98    inference(flattening,[],[f28])).
% 3.73/0.98  
% 3.73/0.98  fof(f44,plain,(
% 3.73/0.98    ? [X0] : (? [X1] : (((r2_hidden(k3_yellow_0(X0),X1) | ~v1_subset_1(X1,u1_struct_0(X0))) & (~r2_hidden(k3_yellow_0(X0),X1) | v1_subset_1(X1,u1_struct_0(X0)))) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & v13_waybel_0(X1,X0) & ~v1_xboole_0(X1)) & l1_orders_2(X0) & v1_yellow_0(X0) & v5_orders_2(X0) & ~v2_struct_0(X0))),
% 3.73/0.98    inference(nnf_transformation,[],[f29])).
% 3.73/0.98  
% 3.73/0.98  fof(f45,plain,(
% 3.73/0.98    ? [X0] : (? [X1] : ((r2_hidden(k3_yellow_0(X0),X1) | ~v1_subset_1(X1,u1_struct_0(X0))) & (~r2_hidden(k3_yellow_0(X0),X1) | v1_subset_1(X1,u1_struct_0(X0))) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & v13_waybel_0(X1,X0) & ~v1_xboole_0(X1)) & l1_orders_2(X0) & v1_yellow_0(X0) & v5_orders_2(X0) & ~v2_struct_0(X0))),
% 3.73/0.98    inference(flattening,[],[f44])).
% 3.73/0.98  
% 3.73/0.98  fof(f47,plain,(
% 3.73/0.98    ( ! [X0] : (? [X1] : ((r2_hidden(k3_yellow_0(X0),X1) | ~v1_subset_1(X1,u1_struct_0(X0))) & (~r2_hidden(k3_yellow_0(X0),X1) | v1_subset_1(X1,u1_struct_0(X0))) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & v13_waybel_0(X1,X0) & ~v1_xboole_0(X1)) => ((r2_hidden(k3_yellow_0(X0),sK5) | ~v1_subset_1(sK5,u1_struct_0(X0))) & (~r2_hidden(k3_yellow_0(X0),sK5) | v1_subset_1(sK5,u1_struct_0(X0))) & m1_subset_1(sK5,k1_zfmisc_1(u1_struct_0(X0))) & v13_waybel_0(sK5,X0) & ~v1_xboole_0(sK5))) )),
% 3.73/0.98    introduced(choice_axiom,[])).
% 3.73/0.98  
% 3.73/0.98  fof(f46,plain,(
% 3.73/0.98    ? [X0] : (? [X1] : ((r2_hidden(k3_yellow_0(X0),X1) | ~v1_subset_1(X1,u1_struct_0(X0))) & (~r2_hidden(k3_yellow_0(X0),X1) | v1_subset_1(X1,u1_struct_0(X0))) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & v13_waybel_0(X1,X0) & ~v1_xboole_0(X1)) & l1_orders_2(X0) & v1_yellow_0(X0) & v5_orders_2(X0) & ~v2_struct_0(X0)) => (? [X1] : ((r2_hidden(k3_yellow_0(sK4),X1) | ~v1_subset_1(X1,u1_struct_0(sK4))) & (~r2_hidden(k3_yellow_0(sK4),X1) | v1_subset_1(X1,u1_struct_0(sK4))) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK4))) & v13_waybel_0(X1,sK4) & ~v1_xboole_0(X1)) & l1_orders_2(sK4) & v1_yellow_0(sK4) & v5_orders_2(sK4) & ~v2_struct_0(sK4))),
% 3.73/0.98    introduced(choice_axiom,[])).
% 3.73/0.98  
% 3.73/0.98  fof(f48,plain,(
% 3.73/0.98    ((r2_hidden(k3_yellow_0(sK4),sK5) | ~v1_subset_1(sK5,u1_struct_0(sK4))) & (~r2_hidden(k3_yellow_0(sK4),sK5) | v1_subset_1(sK5,u1_struct_0(sK4))) & m1_subset_1(sK5,k1_zfmisc_1(u1_struct_0(sK4))) & v13_waybel_0(sK5,sK4) & ~v1_xboole_0(sK5)) & l1_orders_2(sK4) & v1_yellow_0(sK4) & v5_orders_2(sK4) & ~v2_struct_0(sK4)),
% 3.73/0.98    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4,sK5])],[f45,f47,f46])).
% 3.73/0.98  
% 3.73/0.98  fof(f79,plain,(
% 3.73/0.98    r2_hidden(k3_yellow_0(sK4),sK5) | ~v1_subset_1(sK5,u1_struct_0(sK4))),
% 3.73/0.98    inference(cnf_transformation,[],[f48])).
% 3.73/0.98  
% 3.73/0.98  fof(f77,plain,(
% 3.73/0.98    m1_subset_1(sK5,k1_zfmisc_1(u1_struct_0(sK4)))),
% 3.73/0.98    inference(cnf_transformation,[],[f48])).
% 3.73/0.98  
% 3.73/0.98  fof(f74,plain,(
% 3.73/0.98    l1_orders_2(sK4)),
% 3.73/0.98    inference(cnf_transformation,[],[f48])).
% 3.73/0.98  
% 3.73/0.98  fof(f8,axiom,(
% 3.73/0.98    ! [X0] : (l1_orders_2(X0) => m1_subset_1(k3_yellow_0(X0),u1_struct_0(X0)))),
% 3.73/0.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.73/0.98  
% 3.73/0.98  fof(f22,plain,(
% 3.73/0.98    ! [X0] : (m1_subset_1(k3_yellow_0(X0),u1_struct_0(X0)) | ~l1_orders_2(X0))),
% 3.73/0.98    inference(ennf_transformation,[],[f8])).
% 3.73/0.98  
% 3.73/0.98  fof(f61,plain,(
% 3.73/0.98    ( ! [X0] : (m1_subset_1(k3_yellow_0(X0),u1_struct_0(X0)) | ~l1_orders_2(X0)) )),
% 3.73/0.98    inference(cnf_transformation,[],[f22])).
% 3.73/0.98  
% 3.73/0.98  fof(f75,plain,(
% 3.73/0.98    ~v1_xboole_0(sK5)),
% 3.73/0.98    inference(cnf_transformation,[],[f48])).
% 3.73/0.98  
% 3.73/0.98  fof(f10,axiom,(
% 3.73/0.98    ! [X0] : (l1_orders_2(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => (v13_waybel_0(X1,X0) <=> ! [X2] : (m1_subset_1(X2,u1_struct_0(X0)) => ! [X3] : (m1_subset_1(X3,u1_struct_0(X0)) => ((r1_orders_2(X0,X2,X3) & r2_hidden(X2,X1)) => r2_hidden(X3,X1)))))))),
% 3.73/0.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.73/0.98  
% 3.73/0.98  fof(f25,plain,(
% 3.73/0.98    ! [X0] : (! [X1] : ((v13_waybel_0(X1,X0) <=> ! [X2] : (! [X3] : ((r2_hidden(X3,X1) | (~r1_orders_2(X0,X2,X3) | ~r2_hidden(X2,X1))) | ~m1_subset_1(X3,u1_struct_0(X0))) | ~m1_subset_1(X2,u1_struct_0(X0)))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_orders_2(X0))),
% 3.73/0.98    inference(ennf_transformation,[],[f10])).
% 3.73/0.98  
% 3.73/0.98  fof(f26,plain,(
% 3.73/0.98    ! [X0] : (! [X1] : ((v13_waybel_0(X1,X0) <=> ! [X2] : (! [X3] : (r2_hidden(X3,X1) | ~r1_orders_2(X0,X2,X3) | ~r2_hidden(X2,X1) | ~m1_subset_1(X3,u1_struct_0(X0))) | ~m1_subset_1(X2,u1_struct_0(X0)))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_orders_2(X0))),
% 3.73/0.98    inference(flattening,[],[f25])).
% 3.73/0.98  
% 3.73/0.98  fof(f38,plain,(
% 3.73/0.98    ! [X0] : (! [X1] : (((v13_waybel_0(X1,X0) | ? [X2] : (? [X3] : (~r2_hidden(X3,X1) & r1_orders_2(X0,X2,X3) & r2_hidden(X2,X1) & m1_subset_1(X3,u1_struct_0(X0))) & m1_subset_1(X2,u1_struct_0(X0)))) & (! [X2] : (! [X3] : (r2_hidden(X3,X1) | ~r1_orders_2(X0,X2,X3) | ~r2_hidden(X2,X1) | ~m1_subset_1(X3,u1_struct_0(X0))) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~v13_waybel_0(X1,X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_orders_2(X0))),
% 3.73/0.98    inference(nnf_transformation,[],[f26])).
% 3.73/0.98  
% 3.73/0.98  fof(f39,plain,(
% 3.73/0.98    ! [X0] : (! [X1] : (((v13_waybel_0(X1,X0) | ? [X2] : (? [X3] : (~r2_hidden(X3,X1) & r1_orders_2(X0,X2,X3) & r2_hidden(X2,X1) & m1_subset_1(X3,u1_struct_0(X0))) & m1_subset_1(X2,u1_struct_0(X0)))) & (! [X4] : (! [X5] : (r2_hidden(X5,X1) | ~r1_orders_2(X0,X4,X5) | ~r2_hidden(X4,X1) | ~m1_subset_1(X5,u1_struct_0(X0))) | ~m1_subset_1(X4,u1_struct_0(X0))) | ~v13_waybel_0(X1,X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_orders_2(X0))),
% 3.73/0.98    inference(rectify,[],[f38])).
% 3.73/0.98  
% 3.73/0.98  fof(f41,plain,(
% 3.73/0.98    ( ! [X2] : (! [X1,X0] : (? [X3] : (~r2_hidden(X3,X1) & r1_orders_2(X0,X2,X3) & r2_hidden(X2,X1) & m1_subset_1(X3,u1_struct_0(X0))) => (~r2_hidden(sK3(X0,X1),X1) & r1_orders_2(X0,X2,sK3(X0,X1)) & r2_hidden(X2,X1) & m1_subset_1(sK3(X0,X1),u1_struct_0(X0))))) )),
% 3.73/0.98    introduced(choice_axiom,[])).
% 3.73/0.98  
% 3.73/0.98  fof(f40,plain,(
% 3.73/0.98    ! [X1,X0] : (? [X2] : (? [X3] : (~r2_hidden(X3,X1) & r1_orders_2(X0,X2,X3) & r2_hidden(X2,X1) & m1_subset_1(X3,u1_struct_0(X0))) & m1_subset_1(X2,u1_struct_0(X0))) => (? [X3] : (~r2_hidden(X3,X1) & r1_orders_2(X0,sK2(X0,X1),X3) & r2_hidden(sK2(X0,X1),X1) & m1_subset_1(X3,u1_struct_0(X0))) & m1_subset_1(sK2(X0,X1),u1_struct_0(X0))))),
% 3.73/0.98    introduced(choice_axiom,[])).
% 3.73/0.98  
% 3.73/0.98  fof(f42,plain,(
% 3.73/0.98    ! [X0] : (! [X1] : (((v13_waybel_0(X1,X0) | ((~r2_hidden(sK3(X0,X1),X1) & r1_orders_2(X0,sK2(X0,X1),sK3(X0,X1)) & r2_hidden(sK2(X0,X1),X1) & m1_subset_1(sK3(X0,X1),u1_struct_0(X0))) & m1_subset_1(sK2(X0,X1),u1_struct_0(X0)))) & (! [X4] : (! [X5] : (r2_hidden(X5,X1) | ~r1_orders_2(X0,X4,X5) | ~r2_hidden(X4,X1) | ~m1_subset_1(X5,u1_struct_0(X0))) | ~m1_subset_1(X4,u1_struct_0(X0))) | ~v13_waybel_0(X1,X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_orders_2(X0))),
% 3.73/0.98    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2,sK3])],[f39,f41,f40])).
% 3.73/0.98  
% 3.73/0.98  fof(f63,plain,(
% 3.73/0.98    ( ! [X4,X0,X5,X1] : (r2_hidden(X5,X1) | ~r1_orders_2(X0,X4,X5) | ~r2_hidden(X4,X1) | ~m1_subset_1(X5,u1_struct_0(X0)) | ~m1_subset_1(X4,u1_struct_0(X0)) | ~v13_waybel_0(X1,X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_orders_2(X0)) )),
% 3.73/0.98    inference(cnf_transformation,[],[f42])).
% 3.73/0.98  
% 3.73/0.98  fof(f9,axiom,(
% 3.73/0.98    ! [X0] : ((l1_orders_2(X0) & v1_yellow_0(X0) & v5_orders_2(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,u1_struct_0(X0)) => r1_orders_2(X0,k3_yellow_0(X0),X1)))),
% 3.73/0.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.73/0.98  
% 3.73/0.98  fof(f23,plain,(
% 3.73/0.98    ! [X0] : (! [X1] : (r1_orders_2(X0,k3_yellow_0(X0),X1) | ~m1_subset_1(X1,u1_struct_0(X0))) | (~l1_orders_2(X0) | ~v1_yellow_0(X0) | ~v5_orders_2(X0) | v2_struct_0(X0)))),
% 3.73/0.98    inference(ennf_transformation,[],[f9])).
% 3.73/0.98  
% 3.73/0.98  fof(f24,plain,(
% 3.73/0.98    ! [X0] : (! [X1] : (r1_orders_2(X0,k3_yellow_0(X0),X1) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~l1_orders_2(X0) | ~v1_yellow_0(X0) | ~v5_orders_2(X0) | v2_struct_0(X0))),
% 3.73/0.98    inference(flattening,[],[f23])).
% 3.73/0.98  
% 3.73/0.98  fof(f62,plain,(
% 3.73/0.98    ( ! [X0,X1] : (r1_orders_2(X0,k3_yellow_0(X0),X1) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_orders_2(X0) | ~v1_yellow_0(X0) | ~v5_orders_2(X0) | v2_struct_0(X0)) )),
% 3.73/0.98    inference(cnf_transformation,[],[f24])).
% 3.73/0.98  
% 3.73/0.98  fof(f73,plain,(
% 3.73/0.98    v1_yellow_0(sK4)),
% 3.73/0.98    inference(cnf_transformation,[],[f48])).
% 3.73/0.98  
% 3.73/0.98  fof(f71,plain,(
% 3.73/0.98    ~v2_struct_0(sK4)),
% 3.73/0.98    inference(cnf_transformation,[],[f48])).
% 3.73/0.98  
% 3.73/0.98  fof(f72,plain,(
% 3.73/0.98    v5_orders_2(sK4)),
% 3.73/0.98    inference(cnf_transformation,[],[f48])).
% 3.73/0.98  
% 3.73/0.98  fof(f76,plain,(
% 3.73/0.98    v13_waybel_0(sK5,sK4)),
% 3.73/0.98    inference(cnf_transformation,[],[f48])).
% 3.73/0.98  
% 3.73/0.98  fof(f4,axiom,(
% 3.73/0.98    ! [X0] : k2_subset_1(X0) = X0),
% 3.73/0.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.73/0.98  
% 3.73/0.98  fof(f57,plain,(
% 3.73/0.98    ( ! [X0] : (k2_subset_1(X0) = X0) )),
% 3.73/0.98    inference(cnf_transformation,[],[f4])).
% 3.73/0.98  
% 3.73/0.98  fof(f5,axiom,(
% 3.73/0.98    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => ! [X2] : (r2_hidden(X2,X1) => r2_hidden(X2,X0)))),
% 3.73/0.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.73/0.98  
% 3.73/0.98  fof(f19,plain,(
% 3.73/0.98    ! [X0,X1] : (! [X2] : (r2_hidden(X2,X0) | ~r2_hidden(X2,X1)) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 3.73/0.98    inference(ennf_transformation,[],[f5])).
% 3.73/0.98  
% 3.73/0.98  fof(f58,plain,(
% 3.73/0.98    ( ! [X2,X0,X1] : (r2_hidden(X2,X0) | ~r2_hidden(X2,X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 3.73/0.98    inference(cnf_transformation,[],[f19])).
% 3.73/0.98  
% 3.73/0.98  fof(f52,plain,(
% 3.73/0.98    ( ! [X0,X1] : (X0 = X1 | ~r2_hidden(sK1(X0,X1),X1) | ~r2_hidden(sK1(X0,X1),X0)) )),
% 3.73/0.98    inference(cnf_transformation,[],[f36])).
% 3.73/0.98  
% 3.73/0.98  fof(f50,plain,(
% 3.73/0.98    ( ! [X0] : (v1_xboole_0(X0) | r2_hidden(sK0(X0),X0)) )),
% 3.73/0.98    inference(cnf_transformation,[],[f33])).
% 3.73/0.98  
% 3.73/0.98  fof(f6,axiom,(
% 3.73/0.98    ! [X0] : ~v1_subset_1(k2_subset_1(X0),X0)),
% 3.73/0.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.73/0.98  
% 3.73/0.98  fof(f59,plain,(
% 3.73/0.98    ( ! [X0] : (~v1_subset_1(k2_subset_1(X0),X0)) )),
% 3.73/0.98    inference(cnf_transformation,[],[f6])).
% 3.73/0.98  
% 3.73/0.98  fof(f78,plain,(
% 3.73/0.98    ~r2_hidden(k3_yellow_0(sK4),sK5) | v1_subset_1(sK5,u1_struct_0(sK4))),
% 3.73/0.98    inference(cnf_transformation,[],[f48])).
% 3.73/0.98  
% 3.73/0.98  cnf(c_11,plain,
% 3.73/0.98      ( m1_subset_1(X0,X1)
% 3.73/0.98      | ~ m1_subset_1(X2,k1_zfmisc_1(X1))
% 3.73/0.98      | ~ r2_hidden(X0,X2) ),
% 3.73/0.98      inference(cnf_transformation,[],[f60]) ).
% 3.73/0.98  
% 3.73/0.98  cnf(c_2480,plain,
% 3.73/0.98      ( m1_subset_1(sK1(X0,sK5),X1)
% 3.73/0.98      | ~ m1_subset_1(sK5,k1_zfmisc_1(X1))
% 3.73/0.98      | ~ r2_hidden(sK1(X0,sK5),sK5) ),
% 3.73/0.98      inference(instantiation,[status(thm)],[c_11]) ).
% 3.73/0.98  
% 3.73/0.98  cnf(c_5956,plain,
% 3.73/0.98      ( m1_subset_1(sK1(X0,sK5),u1_struct_0(sK4))
% 3.73/0.98      | ~ m1_subset_1(sK5,k1_zfmisc_1(u1_struct_0(sK4)))
% 3.73/0.98      | ~ r2_hidden(sK1(X0,sK5),sK5) ),
% 3.73/0.98      inference(instantiation,[status(thm)],[c_2480]) ).
% 3.73/0.98  
% 3.73/0.98  cnf(c_18071,plain,
% 3.73/0.98      ( m1_subset_1(sK1(u1_struct_0(sK4),sK5),u1_struct_0(sK4))
% 3.73/0.98      | ~ m1_subset_1(sK5,k1_zfmisc_1(u1_struct_0(sK4)))
% 3.73/0.98      | ~ r2_hidden(sK1(u1_struct_0(sK4),sK5),sK5) ),
% 3.73/0.98      inference(instantiation,[status(thm)],[c_5956]) ).
% 3.73/0.98  
% 3.73/0.98  cnf(c_7,plain,
% 3.73/0.98      ( ~ m1_subset_1(X0,X1) | r2_hidden(X0,X1) | v1_xboole_0(X1) ),
% 3.73/0.98      inference(cnf_transformation,[],[f53]) ).
% 3.73/0.98  
% 3.73/0.98  cnf(c_3963,plain,
% 3.73/0.98      ( ~ m1_subset_1(X0,u1_struct_0(sK4))
% 3.73/0.98      | r2_hidden(X0,u1_struct_0(sK4))
% 3.73/0.98      | v1_xboole_0(u1_struct_0(sK4)) ),
% 3.73/0.98      inference(instantiation,[status(thm)],[c_7]) ).
% 3.73/0.98  
% 3.73/0.98  cnf(c_10784,plain,
% 3.73/0.98      ( ~ m1_subset_1(sK1(u1_struct_0(sK4),sK5),u1_struct_0(sK4))
% 3.73/0.98      | r2_hidden(sK1(u1_struct_0(sK4),sK5),u1_struct_0(sK4))
% 3.73/0.98      | v1_xboole_0(u1_struct_0(sK4)) ),
% 3.73/0.98      inference(instantiation,[status(thm)],[c_3963]) ).
% 3.73/0.98  
% 3.73/0.98  cnf(c_3,plain,
% 3.73/0.98      ( r2_hidden(sK1(X0,X1),X1) | r2_hidden(sK1(X0,X1),X0) | X1 = X0 ),
% 3.73/0.98      inference(cnf_transformation,[],[f51]) ).
% 3.73/0.98  
% 3.73/0.98  cnf(c_1281,plain,
% 3.73/0.98      ( X0 = X1
% 3.73/0.98      | r2_hidden(sK1(X1,X0),X0) = iProver_top
% 3.73/0.98      | r2_hidden(sK1(X1,X0),X1) = iProver_top ),
% 3.73/0.98      inference(predicate_to_equality,[status(thm)],[c_3]) ).
% 3.73/0.98  
% 3.73/0.98  cnf(c_6,plain,
% 3.73/0.98      ( m1_subset_1(X0,X1) | ~ r2_hidden(X0,X1) | v1_xboole_0(X1) ),
% 3.73/0.98      inference(cnf_transformation,[],[f54]) ).
% 3.73/0.98  
% 3.73/0.98  cnf(c_1,plain,
% 3.73/0.98      ( ~ r2_hidden(X0,X1) | ~ v1_xboole_0(X1) ),
% 3.73/0.98      inference(cnf_transformation,[],[f49]) ).
% 3.73/0.98  
% 3.73/0.98  cnf(c_182,plain,
% 3.73/0.98      ( ~ r2_hidden(X0,X1) | m1_subset_1(X0,X1) ),
% 3.73/0.98      inference(global_propositional_subsumption,[status(thm)],[c_6,c_1]) ).
% 3.73/0.98  
% 3.73/0.98  cnf(c_183,plain,
% 3.73/0.98      ( m1_subset_1(X0,X1) | ~ r2_hidden(X0,X1) ),
% 3.73/0.98      inference(renaming,[status(thm)],[c_182]) ).
% 3.73/0.98  
% 3.73/0.98  cnf(c_1272,plain,
% 3.73/0.98      ( m1_subset_1(X0,X1) = iProver_top
% 3.73/0.98      | r2_hidden(X0,X1) != iProver_top ),
% 3.73/0.98      inference(predicate_to_equality,[status(thm)],[c_183]) ).
% 3.73/0.98  
% 3.73/0.98  cnf(c_2256,plain,
% 3.73/0.98      ( X0 = X1
% 3.73/0.98      | m1_subset_1(sK1(X0,X1),X0) = iProver_top
% 3.73/0.98      | r2_hidden(sK1(X0,X1),X1) = iProver_top ),
% 3.73/0.98      inference(superposition,[status(thm)],[c_1281,c_1272]) ).
% 3.73/0.98  
% 3.73/0.98  cnf(c_20,plain,
% 3.73/0.98      ( v1_subset_1(X0,X1)
% 3.73/0.98      | ~ m1_subset_1(X0,k1_zfmisc_1(X1))
% 3.73/0.98      | X0 = X1 ),
% 3.73/0.98      inference(cnf_transformation,[],[f70]) ).
% 3.73/0.98  
% 3.73/0.98  cnf(c_22,negated_conjecture,
% 3.73/0.98      ( ~ v1_subset_1(sK5,u1_struct_0(sK4))
% 3.73/0.98      | r2_hidden(k3_yellow_0(sK4),sK5) ),
% 3.73/0.98      inference(cnf_transformation,[],[f79]) ).
% 3.73/0.98  
% 3.73/0.98  cnf(c_233,plain,
% 3.73/0.98      ( ~ v1_subset_1(sK5,u1_struct_0(sK4))
% 3.73/0.98      | r2_hidden(k3_yellow_0(sK4),sK5) ),
% 3.73/0.98      inference(prop_impl,[status(thm)],[c_22]) ).
% 3.73/0.98  
% 3.73/0.98  cnf(c_448,plain,
% 3.73/0.98      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
% 3.73/0.98      | r2_hidden(k3_yellow_0(sK4),sK5)
% 3.73/0.98      | X1 = X0
% 3.73/0.98      | u1_struct_0(sK4) != X1
% 3.73/0.98      | sK5 != X0 ),
% 3.73/0.98      inference(resolution_lifted,[status(thm)],[c_20,c_233]) ).
% 3.73/0.98  
% 3.73/0.98  cnf(c_449,plain,
% 3.73/0.98      ( ~ m1_subset_1(sK5,k1_zfmisc_1(u1_struct_0(sK4)))
% 3.73/0.98      | r2_hidden(k3_yellow_0(sK4),sK5)
% 3.73/0.98      | u1_struct_0(sK4) = sK5 ),
% 3.73/0.98      inference(unflattening,[status(thm)],[c_448]) ).
% 3.73/0.98  
% 3.73/0.98  cnf(c_24,negated_conjecture,
% 3.73/0.98      ( m1_subset_1(sK5,k1_zfmisc_1(u1_struct_0(sK4))) ),
% 3.73/0.98      inference(cnf_transformation,[],[f77]) ).
% 3.73/0.98  
% 3.73/0.98  cnf(c_451,plain,
% 3.73/0.98      ( r2_hidden(k3_yellow_0(sK4),sK5) | u1_struct_0(sK4) = sK5 ),
% 3.73/0.98      inference(global_propositional_subsumption,
% 3.73/0.98                [status(thm)],
% 3.73/0.98                [c_449,c_24]) ).
% 3.73/0.98  
% 3.73/0.98  cnf(c_1269,plain,
% 3.73/0.98      ( u1_struct_0(sK4) = sK5
% 3.73/0.98      | r2_hidden(k3_yellow_0(sK4),sK5) = iProver_top ),
% 3.73/0.98      inference(predicate_to_equality,[status(thm)],[c_451]) ).
% 3.73/0.98  
% 3.73/0.98  cnf(c_2730,plain,
% 3.73/0.98      ( u1_struct_0(sK4) = sK5
% 3.73/0.98      | m1_subset_1(k3_yellow_0(sK4),sK5) = iProver_top ),
% 3.73/0.98      inference(superposition,[status(thm)],[c_1269,c_1272]) ).
% 3.73/0.98  
% 3.73/0.98  cnf(c_27,negated_conjecture,
% 3.73/0.98      ( l1_orders_2(sK4) ),
% 3.73/0.98      inference(cnf_transformation,[],[f74]) ).
% 3.73/0.98  
% 3.73/0.98  cnf(c_34,plain,
% 3.73/0.98      ( l1_orders_2(sK4) = iProver_top ),
% 3.73/0.98      inference(predicate_to_equality,[status(thm)],[c_27]) ).
% 3.73/0.98  
% 3.73/0.98  cnf(c_12,plain,
% 3.73/0.98      ( m1_subset_1(k3_yellow_0(X0),u1_struct_0(X0))
% 3.73/0.98      | ~ l1_orders_2(X0) ),
% 3.73/0.98      inference(cnf_transformation,[],[f61]) ).
% 3.73/0.98  
% 3.73/0.98  cnf(c_65,plain,
% 3.73/0.98      ( m1_subset_1(k3_yellow_0(X0),u1_struct_0(X0)) = iProver_top
% 3.73/0.98      | l1_orders_2(X0) != iProver_top ),
% 3.73/0.98      inference(predicate_to_equality,[status(thm)],[c_12]) ).
% 3.73/0.98  
% 3.73/0.98  cnf(c_67,plain,
% 3.73/0.98      ( m1_subset_1(k3_yellow_0(sK4),u1_struct_0(sK4)) = iProver_top
% 3.73/0.98      | l1_orders_2(sK4) != iProver_top ),
% 3.73/0.98      inference(instantiation,[status(thm)],[c_65]) ).
% 3.73/0.98  
% 3.73/0.98  cnf(c_844,plain,
% 3.73/0.98      ( X0 != X1 | k3_yellow_0(X0) = k3_yellow_0(X1) ),
% 3.73/0.98      theory(equality) ).
% 3.73/0.98  
% 3.73/0.98  cnf(c_854,plain,
% 3.73/0.98      ( k3_yellow_0(sK4) = k3_yellow_0(sK4) | sK4 != sK4 ),
% 3.73/0.98      inference(instantiation,[status(thm)],[c_844]) ).
% 3.73/0.98  
% 3.73/0.98  cnf(c_837,plain,( X0 = X0 ),theory(equality) ).
% 3.73/0.98  
% 3.73/0.98  cnf(c_860,plain,
% 3.73/0.98      ( sK4 = sK4 ),
% 3.73/0.98      inference(instantiation,[status(thm)],[c_837]) ).
% 3.73/0.98  
% 3.73/0.98  cnf(c_1684,plain,
% 3.73/0.98      ( sK5 = sK5 ),
% 3.73/0.98      inference(instantiation,[status(thm)],[c_837]) ).
% 3.73/0.98  
% 3.73/0.98  cnf(c_841,plain,
% 3.73/0.98      ( ~ m1_subset_1(X0,X1) | m1_subset_1(X2,X3) | X2 != X0 | X3 != X1 ),
% 3.73/0.98      theory(equality) ).
% 3.73/0.98  
% 3.73/0.98  cnf(c_1655,plain,
% 3.73/0.98      ( ~ m1_subset_1(X0,X1)
% 3.73/0.98      | m1_subset_1(X2,sK5)
% 3.73/0.98      | X2 != X0
% 3.73/0.98      | sK5 != X1 ),
% 3.73/0.98      inference(instantiation,[status(thm)],[c_841]) ).
% 3.73/0.98  
% 3.73/0.98  cnf(c_1856,plain,
% 3.73/0.98      ( m1_subset_1(X0,sK5)
% 3.73/0.98      | ~ m1_subset_1(k3_yellow_0(sK4),u1_struct_0(sK4))
% 3.73/0.98      | X0 != k3_yellow_0(sK4)
% 3.73/0.98      | sK5 != u1_struct_0(sK4) ),
% 3.73/0.98      inference(instantiation,[status(thm)],[c_1655]) ).
% 3.73/0.98  
% 3.73/0.98  cnf(c_2194,plain,
% 3.73/0.98      ( ~ m1_subset_1(k3_yellow_0(sK4),u1_struct_0(sK4))
% 3.73/0.98      | m1_subset_1(k3_yellow_0(sK4),sK5)
% 3.73/0.98      | k3_yellow_0(sK4) != k3_yellow_0(sK4)
% 3.73/0.98      | sK5 != u1_struct_0(sK4) ),
% 3.73/0.98      inference(instantiation,[status(thm)],[c_1856]) ).
% 3.73/0.98  
% 3.73/0.98  cnf(c_2196,plain,
% 3.73/0.98      ( k3_yellow_0(sK4) != k3_yellow_0(sK4)
% 3.73/0.98      | sK5 != u1_struct_0(sK4)
% 3.73/0.98      | m1_subset_1(k3_yellow_0(sK4),u1_struct_0(sK4)) != iProver_top
% 3.73/0.98      | m1_subset_1(k3_yellow_0(sK4),sK5) = iProver_top ),
% 3.73/0.98      inference(predicate_to_equality,[status(thm)],[c_2194]) ).
% 3.73/0.98  
% 3.73/0.98  cnf(c_838,plain,( X0 != X1 | X2 != X1 | X2 = X0 ),theory(equality) ).
% 3.73/0.98  
% 3.73/0.98  cnf(c_1632,plain,
% 3.73/0.98      ( X0 != X1 | sK5 != X1 | sK5 = X0 ),
% 3.73/0.98      inference(instantiation,[status(thm)],[c_838]) ).
% 3.73/0.98  
% 3.73/0.98  cnf(c_2209,plain,
% 3.73/0.98      ( X0 != sK5 | sK5 = X0 | sK5 != sK5 ),
% 3.73/0.98      inference(instantiation,[status(thm)],[c_1632]) ).
% 3.73/0.98  
% 3.73/0.98  cnf(c_3122,plain,
% 3.73/0.98      ( u1_struct_0(sK4) != sK5 | sK5 = u1_struct_0(sK4) | sK5 != sK5 ),
% 3.73/0.98      inference(instantiation,[status(thm)],[c_2209]) ).
% 3.73/0.98  
% 3.73/0.98  cnf(c_5925,plain,
% 3.73/0.98      ( m1_subset_1(k3_yellow_0(sK4),sK5) = iProver_top ),
% 3.73/0.98      inference(global_propositional_subsumption,
% 3.73/0.98                [status(thm)],
% 3.73/0.98                [c_2730,c_34,c_67,c_854,c_860,c_1684,c_2196,c_3122]) ).
% 3.73/0.98  
% 3.73/0.98  cnf(c_1278,plain,
% 3.73/0.98      ( m1_subset_1(X0,X1) != iProver_top
% 3.73/0.98      | r2_hidden(X0,X1) = iProver_top
% 3.73/0.98      | v1_xboole_0(X1) = iProver_top ),
% 3.73/0.98      inference(predicate_to_equality,[status(thm)],[c_7]) ).
% 3.73/0.98  
% 3.73/0.98  cnf(c_5930,plain,
% 3.73/0.98      ( r2_hidden(k3_yellow_0(sK4),sK5) = iProver_top
% 3.73/0.98      | v1_xboole_0(sK5) = iProver_top ),
% 3.73/0.98      inference(superposition,[status(thm)],[c_5925,c_1278]) ).
% 3.73/0.98  
% 3.73/0.98  cnf(c_26,negated_conjecture,
% 3.73/0.98      ( ~ v1_xboole_0(sK5) ),
% 3.73/0.98      inference(cnf_transformation,[],[f75]) ).
% 3.73/0.98  
% 3.73/0.98  cnf(c_35,plain,
% 3.73/0.98      ( v1_xboole_0(sK5) != iProver_top ),
% 3.73/0.98      inference(predicate_to_equality,[status(thm)],[c_26]) ).
% 3.73/0.98  
% 3.73/0.98  cnf(c_5938,plain,
% 3.73/0.98      ( r2_hidden(k3_yellow_0(sK4),sK5) = iProver_top ),
% 3.73/0.98      inference(global_propositional_subsumption,
% 3.73/0.98                [status(thm)],
% 3.73/0.98                [c_5930,c_35]) ).
% 3.73/0.98  
% 3.73/0.98  cnf(c_1275,plain,
% 3.73/0.98      ( m1_subset_1(sK5,k1_zfmisc_1(u1_struct_0(sK4))) = iProver_top ),
% 3.73/0.98      inference(predicate_to_equality,[status(thm)],[c_24]) ).
% 3.73/0.98  
% 3.73/0.98  cnf(c_19,plain,
% 3.73/0.98      ( ~ r1_orders_2(X0,X1,X2)
% 3.73/0.98      | ~ v13_waybel_0(X3,X0)
% 3.73/0.98      | ~ m1_subset_1(X2,u1_struct_0(X0))
% 3.73/0.98      | ~ m1_subset_1(X1,u1_struct_0(X0))
% 3.73/0.98      | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))
% 3.73/0.98      | ~ r2_hidden(X1,X3)
% 3.73/0.98      | r2_hidden(X2,X3)
% 3.73/0.98      | ~ l1_orders_2(X0) ),
% 3.73/0.98      inference(cnf_transformation,[],[f63]) ).
% 3.73/0.98  
% 3.73/0.98  cnf(c_13,plain,
% 3.73/0.98      ( r1_orders_2(X0,k3_yellow_0(X0),X1)
% 3.73/0.98      | ~ m1_subset_1(X1,u1_struct_0(X0))
% 3.73/0.98      | v2_struct_0(X0)
% 3.73/0.98      | ~ v5_orders_2(X0)
% 3.73/0.98      | ~ v1_yellow_0(X0)
% 3.73/0.98      | ~ l1_orders_2(X0) ),
% 3.73/0.98      inference(cnf_transformation,[],[f62]) ).
% 3.73/0.98  
% 3.73/0.98  cnf(c_28,negated_conjecture,
% 3.73/0.98      ( v1_yellow_0(sK4) ),
% 3.73/0.98      inference(cnf_transformation,[],[f73]) ).
% 3.73/0.98  
% 3.73/0.98  cnf(c_402,plain,
% 3.73/0.98      ( r1_orders_2(X0,k3_yellow_0(X0),X1)
% 3.73/0.98      | ~ m1_subset_1(X1,u1_struct_0(X0))
% 3.73/0.98      | v2_struct_0(X0)
% 3.73/0.98      | ~ v5_orders_2(X0)
% 3.73/0.98      | ~ l1_orders_2(X0)
% 3.73/0.98      | sK4 != X0 ),
% 3.73/0.98      inference(resolution_lifted,[status(thm)],[c_13,c_28]) ).
% 3.73/0.98  
% 3.73/0.98  cnf(c_403,plain,
% 3.73/0.98      ( r1_orders_2(sK4,k3_yellow_0(sK4),X0)
% 3.73/0.98      | ~ m1_subset_1(X0,u1_struct_0(sK4))
% 3.73/0.98      | v2_struct_0(sK4)
% 3.73/0.98      | ~ v5_orders_2(sK4)
% 3.73/0.98      | ~ l1_orders_2(sK4) ),
% 3.73/0.98      inference(unflattening,[status(thm)],[c_402]) ).
% 3.73/0.98  
% 3.73/0.98  cnf(c_30,negated_conjecture,
% 3.73/0.98      ( ~ v2_struct_0(sK4) ),
% 3.73/0.98      inference(cnf_transformation,[],[f71]) ).
% 3.73/0.98  
% 3.73/0.98  cnf(c_29,negated_conjecture,
% 3.73/0.98      ( v5_orders_2(sK4) ),
% 3.73/0.98      inference(cnf_transformation,[],[f72]) ).
% 3.73/0.98  
% 3.73/0.98  cnf(c_407,plain,
% 3.73/0.98      ( ~ m1_subset_1(X0,u1_struct_0(sK4))
% 3.73/0.98      | r1_orders_2(sK4,k3_yellow_0(sK4),X0) ),
% 3.73/0.98      inference(global_propositional_subsumption,
% 3.73/0.98                [status(thm)],
% 3.73/0.98                [c_403,c_30,c_29,c_27]) ).
% 3.73/0.98  
% 3.73/0.98  cnf(c_408,plain,
% 3.73/0.98      ( r1_orders_2(sK4,k3_yellow_0(sK4),X0)
% 3.73/0.98      | ~ m1_subset_1(X0,u1_struct_0(sK4)) ),
% 3.73/0.98      inference(renaming,[status(thm)],[c_407]) ).
% 3.73/0.98  
% 3.73/0.98  cnf(c_518,plain,
% 3.73/0.98      ( ~ v13_waybel_0(X0,X1)
% 3.73/0.98      | ~ m1_subset_1(X2,u1_struct_0(X1))
% 3.73/0.98      | ~ m1_subset_1(X3,u1_struct_0(X1))
% 3.73/0.98      | ~ m1_subset_1(X4,u1_struct_0(sK4))
% 3.73/0.98      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 3.73/0.98      | ~ r2_hidden(X3,X0)
% 3.73/0.98      | r2_hidden(X2,X0)
% 3.73/0.98      | ~ l1_orders_2(X1)
% 3.73/0.98      | X4 != X2
% 3.73/0.98      | k3_yellow_0(sK4) != X3
% 3.73/0.98      | sK4 != X1 ),
% 3.73/0.98      inference(resolution_lifted,[status(thm)],[c_19,c_408]) ).
% 3.73/0.98  
% 3.73/0.98  cnf(c_519,plain,
% 3.73/0.98      ( ~ v13_waybel_0(X0,sK4)
% 3.73/0.98      | ~ m1_subset_1(X1,u1_struct_0(sK4))
% 3.73/0.98      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK4)))
% 3.73/0.98      | ~ m1_subset_1(k3_yellow_0(sK4),u1_struct_0(sK4))
% 3.73/0.98      | r2_hidden(X1,X0)
% 3.73/0.98      | ~ r2_hidden(k3_yellow_0(sK4),X0)
% 3.73/0.98      | ~ l1_orders_2(sK4) ),
% 3.73/0.98      inference(unflattening,[status(thm)],[c_518]) ).
% 3.73/0.98  
% 3.73/0.98  cnf(c_66,plain,
% 3.73/0.98      ( m1_subset_1(k3_yellow_0(sK4),u1_struct_0(sK4))
% 3.73/0.98      | ~ l1_orders_2(sK4) ),
% 3.73/0.98      inference(instantiation,[status(thm)],[c_12]) ).
% 3.73/0.98  
% 3.73/0.98  cnf(c_523,plain,
% 3.73/0.98      ( ~ r2_hidden(k3_yellow_0(sK4),X0)
% 3.73/0.98      | r2_hidden(X1,X0)
% 3.73/0.98      | ~ v13_waybel_0(X0,sK4)
% 3.73/0.98      | ~ m1_subset_1(X1,u1_struct_0(sK4))
% 3.73/0.98      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK4))) ),
% 3.73/0.98      inference(global_propositional_subsumption,
% 3.73/0.98                [status(thm)],
% 3.73/0.98                [c_519,c_27,c_66]) ).
% 3.73/0.98  
% 3.73/0.98  cnf(c_524,plain,
% 3.73/0.98      ( ~ v13_waybel_0(X0,sK4)
% 3.73/0.98      | ~ m1_subset_1(X1,u1_struct_0(sK4))
% 3.73/0.98      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK4)))
% 3.73/0.98      | r2_hidden(X1,X0)
% 3.73/0.98      | ~ r2_hidden(k3_yellow_0(sK4),X0) ),
% 3.73/0.98      inference(renaming,[status(thm)],[c_523]) ).
% 3.73/0.98  
% 3.73/0.98  cnf(c_1267,plain,
% 3.73/0.98      ( v13_waybel_0(X0,sK4) != iProver_top
% 3.73/0.98      | m1_subset_1(X1,u1_struct_0(sK4)) != iProver_top
% 3.73/0.98      | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK4))) != iProver_top
% 3.73/0.98      | r2_hidden(X1,X0) = iProver_top
% 3.73/0.98      | r2_hidden(k3_yellow_0(sK4),X0) != iProver_top ),
% 3.73/0.98      inference(predicate_to_equality,[status(thm)],[c_524]) ).
% 3.73/0.98  
% 3.73/0.98  cnf(c_1867,plain,
% 3.73/0.98      ( v13_waybel_0(sK5,sK4) != iProver_top
% 3.73/0.98      | m1_subset_1(X0,u1_struct_0(sK4)) != iProver_top
% 3.73/0.98      | r2_hidden(X0,sK5) = iProver_top
% 3.73/0.98      | r2_hidden(k3_yellow_0(sK4),sK5) != iProver_top ),
% 3.73/0.98      inference(superposition,[status(thm)],[c_1275,c_1267]) ).
% 3.73/0.98  
% 3.73/0.98  cnf(c_25,negated_conjecture,
% 3.73/0.98      ( v13_waybel_0(sK5,sK4) ),
% 3.73/0.98      inference(cnf_transformation,[],[f76]) ).
% 3.73/0.98  
% 3.73/0.98  cnf(c_36,plain,
% 3.73/0.98      ( v13_waybel_0(sK5,sK4) = iProver_top ),
% 3.73/0.98      inference(predicate_to_equality,[status(thm)],[c_25]) ).
% 3.73/0.98  
% 3.73/0.98  cnf(c_1872,plain,
% 3.73/0.98      ( m1_subset_1(X0,u1_struct_0(sK4)) != iProver_top
% 3.73/0.98      | r2_hidden(X0,sK5) = iProver_top
% 3.73/0.98      | r2_hidden(k3_yellow_0(sK4),sK5) != iProver_top ),
% 3.73/0.98      inference(global_propositional_subsumption,
% 3.73/0.98                [status(thm)],
% 3.73/0.98                [c_1867,c_36]) ).
% 3.73/0.98  
% 3.73/0.98  cnf(c_5945,plain,
% 3.73/0.98      ( m1_subset_1(X0,u1_struct_0(sK4)) != iProver_top
% 3.73/0.98      | r2_hidden(X0,sK5) = iProver_top ),
% 3.73/0.98      inference(superposition,[status(thm)],[c_5938,c_1872]) ).
% 3.73/0.98  
% 3.73/0.98  cnf(c_6516,plain,
% 3.73/0.98      ( u1_struct_0(sK4) = X0
% 3.73/0.98      | r2_hidden(sK1(u1_struct_0(sK4),X0),X0) = iProver_top
% 3.73/0.98      | r2_hidden(sK1(u1_struct_0(sK4),X0),sK5) = iProver_top ),
% 3.73/0.98      inference(superposition,[status(thm)],[c_2256,c_5945]) ).
% 3.73/0.98  
% 3.73/0.98  cnf(c_8314,plain,
% 3.73/0.98      ( u1_struct_0(sK4) = sK5
% 3.73/0.98      | r2_hidden(sK1(u1_struct_0(sK4),sK5),sK5) = iProver_top
% 3.73/0.98      | iProver_top != iProver_top ),
% 3.73/0.98      inference(equality_factoring,[status(thm)],[c_6516]) ).
% 3.73/0.98  
% 3.73/0.98  cnf(c_8316,plain,
% 3.73/0.98      ( u1_struct_0(sK4) = sK5
% 3.73/0.98      | r2_hidden(sK1(u1_struct_0(sK4),sK5),sK5) = iProver_top ),
% 3.73/0.98      inference(equality_resolution_simp,[status(thm)],[c_8314]) ).
% 3.73/0.98  
% 3.73/0.98  cnf(c_8396,plain,
% 3.73/0.98      ( r2_hidden(sK1(u1_struct_0(sK4),sK5),sK5)
% 3.73/0.98      | u1_struct_0(sK4) = sK5 ),
% 3.73/0.98      inference(predicate_to_equality_rev,[status(thm)],[c_8316]) ).
% 3.73/0.98  
% 3.73/0.98  cnf(c_1581,plain,
% 3.73/0.98      ( k2_subset_1(u1_struct_0(sK4)) != X0
% 3.73/0.98      | k2_subset_1(u1_struct_0(sK4)) = sK5
% 3.73/0.98      | sK5 != X0 ),
% 3.73/0.98      inference(instantiation,[status(thm)],[c_838]) ).
% 3.73/0.98  
% 3.73/0.98  cnf(c_6870,plain,
% 3.73/0.98      ( k2_subset_1(u1_struct_0(sK4)) != u1_struct_0(sK4)
% 3.73/0.98      | k2_subset_1(u1_struct_0(sK4)) = sK5
% 3.73/0.98      | sK5 != u1_struct_0(sK4) ),
% 3.73/0.98      inference(instantiation,[status(thm)],[c_1581]) ).
% 3.73/0.98  
% 3.73/0.98  cnf(c_8,plain,
% 3.73/0.98      ( k2_subset_1(X0) = X0 ),
% 3.73/0.98      inference(cnf_transformation,[],[f57]) ).
% 3.73/0.98  
% 3.73/0.98  cnf(c_2445,plain,
% 3.73/0.98      ( k2_subset_1(u1_struct_0(sK4)) = u1_struct_0(sK4) ),
% 3.73/0.98      inference(instantiation,[status(thm)],[c_8]) ).
% 3.73/0.98  
% 3.73/0.98  cnf(c_1975,plain,
% 3.73/0.98      ( ~ r2_hidden(sK0(sK5),u1_struct_0(sK4))
% 3.73/0.98      | ~ v1_xboole_0(u1_struct_0(sK4)) ),
% 3.73/0.98      inference(instantiation,[status(thm)],[c_1]) ).
% 3.73/0.98  
% 3.73/0.98  cnf(c_9,plain,
% 3.73/0.98      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
% 3.73/0.98      | ~ r2_hidden(X2,X0)
% 3.73/0.98      | r2_hidden(X2,X1) ),
% 3.73/0.98      inference(cnf_transformation,[],[f58]) ).
% 3.73/0.98  
% 3.73/0.98  cnf(c_1591,plain,
% 3.73/0.98      ( ~ m1_subset_1(sK5,k1_zfmisc_1(X0))
% 3.73/0.98      | r2_hidden(sK0(sK5),X0)
% 3.73/0.98      | ~ r2_hidden(sK0(sK5),sK5) ),
% 3.73/0.98      inference(instantiation,[status(thm)],[c_9]) ).
% 3.73/0.98  
% 3.73/0.98  cnf(c_1735,plain,
% 3.73/0.98      ( ~ m1_subset_1(sK5,k1_zfmisc_1(u1_struct_0(sK4)))
% 3.73/0.98      | r2_hidden(sK0(sK5),u1_struct_0(sK4))
% 3.73/0.98      | ~ r2_hidden(sK0(sK5),sK5) ),
% 3.73/0.98      inference(instantiation,[status(thm)],[c_1591]) ).
% 3.73/0.98  
% 3.73/0.98  cnf(c_2,plain,
% 3.73/0.98      ( ~ r2_hidden(sK1(X0,X1),X1)
% 3.73/0.98      | ~ r2_hidden(sK1(X0,X1),X0)
% 3.73/0.98      | X1 = X0 ),
% 3.73/0.98      inference(cnf_transformation,[],[f52]) ).
% 3.73/0.98  
% 3.73/0.98  cnf(c_1542,plain,
% 3.73/0.98      ( ~ r2_hidden(sK1(u1_struct_0(sK4),sK5),u1_struct_0(sK4))
% 3.73/0.98      | ~ r2_hidden(sK1(u1_struct_0(sK4),sK5),sK5)
% 3.73/0.98      | sK5 = u1_struct_0(sK4) ),
% 3.73/0.98      inference(instantiation,[status(thm)],[c_2]) ).
% 3.73/0.98  
% 3.73/0.98  cnf(c_0,plain,
% 3.73/0.98      ( r2_hidden(sK0(X0),X0) | v1_xboole_0(X0) ),
% 3.73/0.98      inference(cnf_transformation,[],[f50]) ).
% 3.73/0.98  
% 3.73/0.98  cnf(c_1481,plain,
% 3.73/0.98      ( r2_hidden(sK0(sK5),sK5) | v1_xboole_0(sK5) ),
% 3.73/0.98      inference(instantiation,[status(thm)],[c_0]) ).
% 3.73/0.98  
% 3.73/0.98  cnf(c_10,plain,
% 3.73/0.98      ( ~ v1_subset_1(k2_subset_1(X0),X0) ),
% 3.73/0.98      inference(cnf_transformation,[],[f59]) ).
% 3.73/0.98  
% 3.73/0.98  cnf(c_23,negated_conjecture,
% 3.73/0.98      ( v1_subset_1(sK5,u1_struct_0(sK4))
% 3.73/0.98      | ~ r2_hidden(k3_yellow_0(sK4),sK5) ),
% 3.73/0.98      inference(cnf_transformation,[],[f78]) ).
% 3.73/0.98  
% 3.73/0.98  cnf(c_231,plain,
% 3.73/0.98      ( v1_subset_1(sK5,u1_struct_0(sK4))
% 3.73/0.98      | ~ r2_hidden(k3_yellow_0(sK4),sK5) ),
% 3.73/0.98      inference(prop_impl,[status(thm)],[c_23]) ).
% 3.73/0.98  
% 3.73/0.98  cnf(c_436,plain,
% 3.73/0.98      ( ~ r2_hidden(k3_yellow_0(sK4),sK5)
% 3.73/0.98      | u1_struct_0(sK4) != X0
% 3.73/0.98      | k2_subset_1(X0) != sK5 ),
% 3.73/0.98      inference(resolution_lifted,[status(thm)],[c_10,c_231]) ).
% 3.73/0.98  
% 3.73/0.98  cnf(c_437,plain,
% 3.73/0.98      ( ~ r2_hidden(k3_yellow_0(sK4),sK5)
% 3.73/0.98      | k2_subset_1(u1_struct_0(sK4)) != sK5 ),
% 3.73/0.98      inference(unflattening,[status(thm)],[c_436]) ).
% 3.73/0.98  
% 3.73/0.98  cnf(c_1270,plain,
% 3.73/0.98      ( k2_subset_1(u1_struct_0(sK4)) != sK5
% 3.73/0.98      | r2_hidden(k3_yellow_0(sK4),sK5) != iProver_top ),
% 3.73/0.98      inference(predicate_to_equality,[status(thm)],[c_437]) ).
% 3.73/0.98  
% 3.73/0.98  cnf(c_1313,plain,
% 3.73/0.98      ( u1_struct_0(sK4) != sK5
% 3.73/0.98      | r2_hidden(k3_yellow_0(sK4),sK5) != iProver_top ),
% 3.73/0.98      inference(demodulation,[status(thm)],[c_1270,c_8]) ).
% 3.73/0.98  
% 3.73/0.98  cnf(c_438,plain,
% 3.73/0.98      ( k2_subset_1(u1_struct_0(sK4)) != sK5
% 3.73/0.98      | r2_hidden(k3_yellow_0(sK4),sK5) != iProver_top ),
% 3.73/0.98      inference(predicate_to_equality,[status(thm)],[c_437]) ).
% 3.73/0.98  
% 3.73/0.98  cnf(contradiction,plain,
% 3.73/0.98      ( $false ),
% 3.73/0.98      inference(minisat,
% 3.73/0.98                [status(thm)],
% 3.73/0.98                [c_18071,c_10784,c_8396,c_6870,c_5930,c_2445,c_1975,
% 3.73/0.98                 c_1735,c_1542,c_1481,c_1313,c_438,c_24,c_35,c_26]) ).
% 3.73/0.98  
% 3.73/0.98  
% 3.73/0.98  % SZS output end CNFRefutation for theBenchmark.p
% 3.73/0.98  
% 3.73/0.98  ------                               Statistics
% 3.73/0.98  
% 3.73/0.98  ------ General
% 3.73/0.98  
% 3.73/0.98  abstr_ref_over_cycles:                  0
% 3.73/0.98  abstr_ref_under_cycles:                 0
% 3.73/0.98  gc_basic_clause_elim:                   0
% 3.73/0.98  forced_gc_time:                         0
% 3.73/0.98  parsing_time:                           0.009
% 3.73/0.98  unif_index_cands_time:                  0.
% 3.73/0.98  unif_index_add_time:                    0.
% 3.73/0.98  orderings_time:                         0.
% 3.73/0.98  out_proof_time:                         0.01
% 3.73/0.98  total_time:                             0.425
% 3.73/0.98  num_of_symbols:                         51
% 3.73/0.98  num_of_terms:                           8451
% 3.73/0.98  
% 3.73/0.98  ------ Preprocessing
% 3.73/0.98  
% 3.73/0.98  num_of_splits:                          0
% 3.73/0.98  num_of_split_atoms:                     0
% 3.73/0.98  num_of_reused_defs:                     0
% 3.73/0.98  num_eq_ax_congr_red:                    19
% 3.73/0.98  num_of_sem_filtered_clauses:            1
% 3.73/0.98  num_of_subtypes:                        0
% 3.73/0.98  monotx_restored_types:                  0
% 3.73/0.98  sat_num_of_epr_types:                   0
% 3.73/0.98  sat_num_of_non_cyclic_types:            0
% 3.73/0.98  sat_guarded_non_collapsed_types:        0
% 3.73/0.98  num_pure_diseq_elim:                    0
% 3.73/0.98  simp_replaced_by:                       0
% 3.73/0.98  res_preprocessed:                       131
% 3.73/0.98  prep_upred:                             0
% 3.73/0.98  prep_unflattend:                        21
% 3.73/0.98  smt_new_axioms:                         0
% 3.73/0.98  pred_elim_cands:                        4
% 3.73/0.98  pred_elim:                              6
% 3.73/0.98  pred_elim_cl:                           6
% 3.73/0.98  pred_elim_cycles:                       8
% 3.73/0.98  merged_defs:                            2
% 3.73/0.98  merged_defs_ncl:                        0
% 3.73/0.98  bin_hyper_res:                          2
% 3.73/0.98  prep_cycles:                            4
% 3.73/0.98  pred_elim_time:                         0.006
% 3.73/0.98  splitting_time:                         0.
% 3.73/0.98  sem_filter_time:                        0.
% 3.73/0.98  monotx_time:                            0.
% 3.73/0.98  subtype_inf_time:                       0.
% 3.73/0.98  
% 3.73/0.98  ------ Problem properties
% 3.73/0.98  
% 3.73/0.98  clauses:                                25
% 3.73/0.98  conjectures:                            3
% 3.73/0.98  epr:                                    7
% 3.73/0.98  horn:                                   17
% 3.73/0.98  ground:                                 7
% 3.73/0.98  unary:                                  5
% 3.73/0.98  binary:                                 6
% 3.73/0.98  lits:                                   64
% 3.73/0.98  lits_eq:                                7
% 3.73/0.98  fd_pure:                                0
% 3.73/0.98  fd_pseudo:                              0
% 3.73/0.98  fd_cond:                                0
% 3.73/0.98  fd_pseudo_cond:                         2
% 3.73/0.98  ac_symbols:                             0
% 3.73/0.98  
% 3.73/0.98  ------ Propositional Solver
% 3.73/0.98  
% 3.73/0.98  prop_solver_calls:                      28
% 3.73/0.98  prop_fast_solver_calls:                 1454
% 3.73/0.98  smt_solver_calls:                       0
% 3.73/0.98  smt_fast_solver_calls:                  0
% 3.73/0.98  prop_num_of_clauses:                    5598
% 3.73/0.98  prop_preprocess_simplified:             9492
% 3.73/0.98  prop_fo_subsumed:                       67
% 3.73/0.98  prop_solver_time:                       0.
% 3.73/0.98  smt_solver_time:                        0.
% 3.73/0.98  smt_fast_solver_time:                   0.
% 3.73/0.98  prop_fast_solver_time:                  0.
% 3.73/0.98  prop_unsat_core_time:                   0.
% 3.73/0.98  
% 3.73/0.98  ------ QBF
% 3.73/0.98  
% 3.73/0.98  qbf_q_res:                              0
% 3.73/0.98  qbf_num_tautologies:                    0
% 3.73/0.98  qbf_prep_cycles:                        0
% 3.73/0.98  
% 3.73/0.98  ------ BMC1
% 3.73/0.98  
% 3.73/0.98  bmc1_current_bound:                     -1
% 3.73/0.98  bmc1_last_solved_bound:                 -1
% 3.73/0.98  bmc1_unsat_core_size:                   -1
% 3.73/0.98  bmc1_unsat_core_parents_size:           -1
% 3.73/0.98  bmc1_merge_next_fun:                    0
% 3.73/0.98  bmc1_unsat_core_clauses_time:           0.
% 3.73/0.98  
% 3.73/0.98  ------ Instantiation
% 3.73/0.98  
% 3.73/0.98  inst_num_of_clauses:                    1213
% 3.73/0.98  inst_num_in_passive:                    174
% 3.73/0.98  inst_num_in_active:                     516
% 3.73/0.98  inst_num_in_unprocessed:                522
% 3.73/0.98  inst_num_of_loops:                      732
% 3.73/0.98  inst_num_of_learning_restarts:          0
% 3.73/0.98  inst_num_moves_active_passive:          212
% 3.73/0.98  inst_lit_activity:                      0
% 3.73/0.98  inst_lit_activity_moves:                0
% 3.73/0.98  inst_num_tautologies:                   0
% 3.73/0.98  inst_num_prop_implied:                  0
% 3.73/0.98  inst_num_existing_simplified:           0
% 3.73/0.98  inst_num_eq_res_simplified:             0
% 3.73/0.98  inst_num_child_elim:                    0
% 3.73/0.98  inst_num_of_dismatching_blockings:      594
% 3.73/0.98  inst_num_of_non_proper_insts:           1480
% 3.73/0.98  inst_num_of_duplicates:                 0
% 3.73/0.98  inst_inst_num_from_inst_to_res:         0
% 3.73/0.98  inst_dismatching_checking_time:         0.
% 3.73/0.98  
% 3.73/0.98  ------ Resolution
% 3.73/0.98  
% 3.73/0.98  res_num_of_clauses:                     0
% 3.73/0.98  res_num_in_passive:                     0
% 3.73/0.98  res_num_in_active:                      0
% 3.73/0.98  res_num_of_loops:                       135
% 3.73/0.98  res_forward_subset_subsumed:            226
% 3.73/0.98  res_backward_subset_subsumed:           0
% 3.73/0.98  res_forward_subsumed:                   0
% 3.73/0.98  res_backward_subsumed:                  0
% 3.73/0.98  res_forward_subsumption_resolution:     2
% 3.73/0.98  res_backward_subsumption_resolution:    0
% 3.73/0.98  res_clause_to_clause_subsumption:       4898
% 3.73/0.98  res_orphan_elimination:                 0
% 3.73/0.98  res_tautology_del:                      94
% 3.73/0.98  res_num_eq_res_simplified:              0
% 3.73/0.98  res_num_sel_changes:                    0
% 3.73/0.98  res_moves_from_active_to_pass:          0
% 3.73/0.98  
% 3.73/0.98  ------ Superposition
% 3.73/0.98  
% 3.73/0.98  sup_time_total:                         0.
% 3.73/0.98  sup_time_generating:                    0.
% 3.73/0.98  sup_time_sim_full:                      0.
% 3.73/0.98  sup_time_sim_immed:                     0.
% 3.73/0.98  
% 3.73/0.98  sup_num_of_clauses:                     527
% 3.73/0.98  sup_num_in_active:                      144
% 3.73/0.98  sup_num_in_passive:                     383
% 3.73/0.98  sup_num_of_loops:                       146
% 3.73/0.98  sup_fw_superposition:                   319
% 3.73/0.98  sup_bw_superposition:                   499
% 3.73/0.98  sup_immediate_simplified:               143
% 3.73/0.98  sup_given_eliminated:                   0
% 3.73/0.98  comparisons_done:                       0
% 3.73/0.98  comparisons_avoided:                    0
% 3.73/0.98  
% 3.73/0.98  ------ Simplifications
% 3.73/0.98  
% 3.73/0.98  
% 3.73/0.98  sim_fw_subset_subsumed:                 68
% 3.73/0.98  sim_bw_subset_subsumed:                 35
% 3.73/0.98  sim_fw_subsumed:                        34
% 3.73/0.98  sim_bw_subsumed:                        16
% 3.73/0.98  sim_fw_subsumption_res:                 0
% 3.73/0.98  sim_bw_subsumption_res:                 5
% 3.73/0.98  sim_tautology_del:                      56
% 3.73/0.98  sim_eq_tautology_del:                   27
% 3.73/0.98  sim_eq_res_simp:                        4
% 3.73/0.98  sim_fw_demodulated:                     2
% 3.73/0.98  sim_bw_demodulated:                     0
% 3.73/0.98  sim_light_normalised:                   1
% 3.73/0.98  sim_joinable_taut:                      0
% 3.73/0.98  sim_joinable_simp:                      0
% 3.73/0.98  sim_ac_normalised:                      0
% 3.73/0.98  sim_smt_subsumption:                    0
% 3.73/0.98  
%------------------------------------------------------------------------------
