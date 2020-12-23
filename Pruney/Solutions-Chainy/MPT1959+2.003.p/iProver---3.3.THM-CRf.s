%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n021.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:28:24 EST 2020

% Result     : Theorem 3.23s
% Output     : CNFRefutation 3.23s
% Verified   : 
% Statistics : Number of formulae       :  159 ( 917 expanded)
%              Number of clauses        :   93 ( 243 expanded)
%              Number of leaves         :   22 ( 186 expanded)
%              Depth                    :   27
%              Number of atoms          :  610 (6961 expanded)
%              Number of equality atoms :  107 ( 306 expanded)
%              Maximal formula depth    :   14 (   5 average)
%              Maximal clause size      :   22 (   3 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
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

fof(f4,axiom,(
    ! [X0] : ~ v1_subset_1(k2_subset_1(X0),X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f50,plain,(
    ! [X0] : ~ v1_subset_1(k2_subset_1(X0),X0) ),
    inference(cnf_transformation,[],[f4])).

fof(f71,plain,
    ( ~ r2_hidden(k3_yellow_0(sK3),sK4)
    | v1_subset_1(sK4,u1_struct_0(sK3)) ),
    inference(cnf_transformation,[],[f45])).

fof(f2,axiom,(
    ! [X0] : k2_subset_1(X0) = X0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f48,plain,(
    ! [X0] : k2_subset_1(X0) = X0 ),
    inference(cnf_transformation,[],[f2])).

fof(f67,plain,(
    l1_orders_2(sK3) ),
    inference(cnf_transformation,[],[f45])).

fof(f68,plain,(
    ~ v1_xboole_0(sK4) ),
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

fof(f3,axiom,(
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
    inference(ennf_transformation,[],[f3])).

fof(f49,plain,(
    ! [X0,X1] :
      ( v1_xboole_0(X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | ~ v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f46,plain,(
    ! [X0,X1] :
      ( X0 = X1
      | r2_hidden(sK0(X0,X1),X1)
      | r2_hidden(sK0(X0,X1),X0) ) ),
    inference(cnf_transformation,[],[f34])).

cnf(c_759,plain,
    ( ~ r2_hidden(X0,X1)
    | r2_hidden(X2,X3)
    | X2 != X0
    | X3 != X1 ),
    theory(equality)).

cnf(c_757,plain,
    ( X0 = X0 ),
    theory(equality)).

cnf(c_3586,plain,
    ( ~ r2_hidden(X0,X1)
    | r2_hidden(X2,X1)
    | X2 != X0 ),
    inference(resolution,[status(thm)],[c_759,c_757])).

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

cnf(c_394,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | r2_hidden(k3_yellow_0(sK3),sK4)
    | X1 = X0
    | u1_struct_0(sK3) != X1
    | sK4 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_16,c_195])).

cnf(c_395,plain,
    ( ~ m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(sK3)))
    | r2_hidden(k3_yellow_0(sK3),sK4)
    | u1_struct_0(sK3) = sK4 ),
    inference(unflattening,[status(thm)],[c_394])).

cnf(c_20,negated_conjecture,
    ( m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(sK3))) ),
    inference(cnf_transformation,[],[f70])).

cnf(c_397,plain,
    ( r2_hidden(k3_yellow_0(sK3),sK4)
    | u1_struct_0(sK3) = sK4 ),
    inference(global_propositional_subsumption,[status(thm)],[c_395,c_20])).

cnf(c_4221,plain,
    ( r2_hidden(u1_struct_0(sK3),X0)
    | r2_hidden(k3_yellow_0(sK3),sK4)
    | ~ r2_hidden(sK4,X0) ),
    inference(resolution,[status(thm)],[c_3586,c_397])).

cnf(c_4,plain,
    ( ~ v1_subset_1(k2_subset_1(X0),X0) ),
    inference(cnf_transformation,[],[f50])).

cnf(c_19,negated_conjecture,
    ( v1_subset_1(sK4,u1_struct_0(sK3))
    | ~ r2_hidden(k3_yellow_0(sK3),sK4) ),
    inference(cnf_transformation,[],[f71])).

cnf(c_193,plain,
    ( v1_subset_1(sK4,u1_struct_0(sK3))
    | ~ r2_hidden(k3_yellow_0(sK3),sK4) ),
    inference(prop_impl,[status(thm)],[c_19])).

cnf(c_382,plain,
    ( ~ r2_hidden(k3_yellow_0(sK3),sK4)
    | u1_struct_0(sK3) != X0
    | k2_subset_1(X0) != sK4 ),
    inference(resolution_lifted,[status(thm)],[c_4,c_193])).

cnf(c_383,plain,
    ( ~ r2_hidden(k3_yellow_0(sK3),sK4)
    | k2_subset_1(u1_struct_0(sK3)) != sK4 ),
    inference(unflattening,[status(thm)],[c_382])).

cnf(c_1154,plain,
    ( k2_subset_1(u1_struct_0(sK3)) != sK4
    | r2_hidden(k3_yellow_0(sK3),sK4) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_383])).

cnf(c_2,plain,
    ( k2_subset_1(X0) = X0 ),
    inference(cnf_transformation,[],[f48])).

cnf(c_1185,plain,
    ( u1_struct_0(sK3) != sK4
    | r2_hidden(k3_yellow_0(sK3),sK4) != iProver_top ),
    inference(demodulation,[status(thm)],[c_1154,c_2])).

cnf(c_1153,plain,
    ( u1_struct_0(sK3) = sK4
    | r2_hidden(k3_yellow_0(sK3),sK4) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_397])).

cnf(c_23,negated_conjecture,
    ( l1_orders_2(sK3) ),
    inference(cnf_transformation,[],[f67])).

cnf(c_30,plain,
    ( l1_orders_2(sK3) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_23])).

cnf(c_22,negated_conjecture,
    ( ~ v1_xboole_0(sK4) ),
    inference(cnf_transformation,[],[f68])).

cnf(c_31,plain,
    ( v1_xboole_0(sK4) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_22])).

cnf(c_33,plain,
    ( m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(sK3))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_20])).

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

cnf(c_396,plain,
    ( u1_struct_0(sK3) = sK4
    | m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(sK3))) != iProver_top
    | r2_hidden(k3_yellow_0(sK3),sK4) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_395])).

cnf(c_764,plain,
    ( X0 != X1
    | k3_yellow_0(X0) = k3_yellow_0(X1) ),
    theory(equality)).

cnf(c_774,plain,
    ( k3_yellow_0(sK3) = k3_yellow_0(sK3)
    | sK3 != sK3 ),
    inference(instantiation,[status(thm)],[c_764])).

cnf(c_780,plain,
    ( sK3 = sK3 ),
    inference(instantiation,[status(thm)],[c_757])).

cnf(c_1508,plain,
    ( sK4 = sK4 ),
    inference(instantiation,[status(thm)],[c_757])).

cnf(c_763,plain,
    ( ~ m1_subset_1(X0,X1)
    | m1_subset_1(X2,X3)
    | X2 != X0
    | X3 != X1 ),
    theory(equality)).

cnf(c_1424,plain,
    ( m1_subset_1(X0,X1)
    | ~ m1_subset_1(k3_yellow_0(sK3),u1_struct_0(sK3))
    | X1 != u1_struct_0(sK3)
    | X0 != k3_yellow_0(sK3) ),
    inference(instantiation,[status(thm)],[c_763])).

cnf(c_1543,plain,
    ( m1_subset_1(k3_yellow_0(sK3),X0)
    | ~ m1_subset_1(k3_yellow_0(sK3),u1_struct_0(sK3))
    | X0 != u1_struct_0(sK3)
    | k3_yellow_0(sK3) != k3_yellow_0(sK3) ),
    inference(instantiation,[status(thm)],[c_1424])).

cnf(c_1920,plain,
    ( ~ m1_subset_1(k3_yellow_0(sK3),u1_struct_0(sK3))
    | m1_subset_1(k3_yellow_0(sK3),sK4)
    | k3_yellow_0(sK3) != k3_yellow_0(sK3)
    | sK4 != u1_struct_0(sK3) ),
    inference(instantiation,[status(thm)],[c_1543])).

cnf(c_1924,plain,
    ( k3_yellow_0(sK3) != k3_yellow_0(sK3)
    | sK4 != u1_struct_0(sK3)
    | m1_subset_1(k3_yellow_0(sK3),u1_struct_0(sK3)) != iProver_top
    | m1_subset_1(k3_yellow_0(sK3),sK4) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1920])).

cnf(c_6,plain,
    ( ~ m1_subset_1(X0,X1)
    | r2_hidden(X0,X1)
    | v1_xboole_0(X1) ),
    inference(cnf_transformation,[],[f52])).

cnf(c_1714,plain,
    ( ~ m1_subset_1(X0,sK4)
    | r2_hidden(X0,sK4)
    | v1_xboole_0(sK4) ),
    inference(instantiation,[status(thm)],[c_6])).

cnf(c_2209,plain,
    ( ~ m1_subset_1(k3_yellow_0(sK3),sK4)
    | r2_hidden(k3_yellow_0(sK3),sK4)
    | v1_xboole_0(sK4) ),
    inference(instantiation,[status(thm)],[c_1714])).

cnf(c_2210,plain,
    ( m1_subset_1(k3_yellow_0(sK3),sK4) != iProver_top
    | r2_hidden(k3_yellow_0(sK3),sK4) = iProver_top
    | v1_xboole_0(sK4) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2209])).

cnf(c_758,plain,
    ( X0 != X1
    | X2 != X1
    | X2 = X0 ),
    theory(equality)).

cnf(c_1484,plain,
    ( u1_struct_0(sK3) != X0
    | sK4 != X0
    | sK4 = u1_struct_0(sK3) ),
    inference(instantiation,[status(thm)],[c_758])).

cnf(c_2462,plain,
    ( u1_struct_0(sK3) != sK4
    | sK4 = u1_struct_0(sK3)
    | sK4 != sK4 ),
    inference(instantiation,[status(thm)],[c_1484])).

cnf(c_2973,plain,
    ( r2_hidden(k3_yellow_0(sK3),sK4) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_1153,c_30,c_31,c_33,c_63,c_396,c_774,c_780,c_1508,c_1924,c_2210,c_2462])).

cnf(c_4601,plain,
    ( r2_hidden(k3_yellow_0(sK3),sK4) ),
    inference(global_propositional_subsumption,[status(thm)],[c_4221,c_30,c_31,c_33,c_63,c_396,c_397,c_774,c_780,c_1185,c_1508,c_1924,c_2210,c_2462])).

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

cnf(c_464,plain,
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

cnf(c_465,plain,
    ( ~ v13_waybel_0(X0,sK3)
    | ~ m1_subset_1(X1,u1_struct_0(sK3))
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK3)))
    | ~ m1_subset_1(k3_yellow_0(sK3),u1_struct_0(sK3))
    | r2_hidden(X1,X0)
    | ~ r2_hidden(k3_yellow_0(sK3),X0)
    | ~ l1_orders_2(sK3) ),
    inference(unflattening,[status(thm)],[c_464])).

cnf(c_62,plain,
    ( m1_subset_1(k3_yellow_0(sK3),u1_struct_0(sK3))
    | ~ l1_orders_2(sK3) ),
    inference(instantiation,[status(thm)],[c_8])).

cnf(c_469,plain,
    ( ~ r2_hidden(k3_yellow_0(sK3),X0)
    | r2_hidden(X1,X0)
    | ~ v13_waybel_0(X0,sK3)
    | ~ m1_subset_1(X1,u1_struct_0(sK3))
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK3))) ),
    inference(global_propositional_subsumption,[status(thm)],[c_465,c_23,c_62])).

cnf(c_470,plain,
    ( ~ v13_waybel_0(X0,sK3)
    | ~ m1_subset_1(X1,u1_struct_0(sK3))
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK3)))
    | r2_hidden(X1,X0)
    | ~ r2_hidden(k3_yellow_0(sK3),X0) ),
    inference(renaming,[status(thm)],[c_469])).

cnf(c_2010,plain,
    ( ~ v13_waybel_0(sK4,sK3)
    | ~ m1_subset_1(X0,u1_struct_0(sK3))
    | r2_hidden(X0,sK4)
    | ~ r2_hidden(k3_yellow_0(sK3),sK4) ),
    inference(resolution,[status(thm)],[c_470,c_20])).

cnf(c_21,negated_conjecture,
    ( v13_waybel_0(sK4,sK3) ),
    inference(cnf_transformation,[],[f69])).

cnf(c_1158,plain,
    ( m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(sK3))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_20])).

cnf(c_1151,plain,
    ( v13_waybel_0(X0,sK3) != iProver_top
    | m1_subset_1(X1,u1_struct_0(sK3)) != iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK3))) != iProver_top
    | r2_hidden(X1,X0) = iProver_top
    | r2_hidden(k3_yellow_0(sK3),X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_470])).

cnf(c_1981,plain,
    ( v13_waybel_0(sK4,sK3) != iProver_top
    | m1_subset_1(X0,u1_struct_0(sK3)) != iProver_top
    | r2_hidden(X0,sK4) = iProver_top
    | r2_hidden(k3_yellow_0(sK3),sK4) != iProver_top ),
    inference(superposition,[status(thm)],[c_1158,c_1151])).

cnf(c_1982,plain,
    ( ~ v13_waybel_0(sK4,sK3)
    | ~ m1_subset_1(X0,u1_struct_0(sK3))
    | r2_hidden(X0,sK4)
    | ~ r2_hidden(k3_yellow_0(sK3),sK4) ),
    inference(predicate_to_equality_rev,[status(thm)],[c_1981])).

cnf(c_2013,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(sK3))
    | r2_hidden(X0,sK4)
    | ~ r2_hidden(k3_yellow_0(sK3),sK4) ),
    inference(global_propositional_subsumption,[status(thm)],[c_2010,c_21,c_1982])).

cnf(c_4861,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(sK3))
    | r2_hidden(X0,sK4) ),
    inference(backward_subsumption_resolution,[status(thm)],[c_4601,c_2013])).

cnf(c_5,plain,
    ( m1_subset_1(X0,X1)
    | ~ r2_hidden(X0,X1) ),
    inference(cnf_transformation,[],[f51])).

cnf(c_5457,plain,
    ( ~ r2_hidden(X0,u1_struct_0(sK3))
    | r2_hidden(X0,sK4) ),
    inference(resolution,[status(thm)],[c_4861,c_5])).

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

cnf(c_2572,plain,
    ( m1_subset_1(X0,u1_struct_0(sK3))
    | ~ r2_hidden(X0,sK4) ),
    inference(resolution,[status(thm)],[c_7,c_20])).

cnf(c_2665,plain,
    ( r2_hidden(X0,u1_struct_0(sK3))
    | ~ r2_hidden(X0,sK4)
    | v1_xboole_0(u1_struct_0(sK3)) ),
    inference(resolution,[status(thm)],[c_2572,c_6])).

cnf(c_3,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | ~ v1_xboole_0(X1)
    | v1_xboole_0(X0) ),
    inference(cnf_transformation,[],[f49])).

cnf(c_1162,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(X1)) != iProver_top
    | v1_xboole_0(X1) != iProver_top
    | v1_xboole_0(X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3])).

cnf(c_2441,plain,
    ( v1_xboole_0(u1_struct_0(sK3)) != iProver_top
    | v1_xboole_0(sK4) = iProver_top ),
    inference(superposition,[status(thm)],[c_1158,c_1162])).

cnf(c_2442,plain,
    ( ~ v1_xboole_0(u1_struct_0(sK3))
    | v1_xboole_0(sK4) ),
    inference(predicate_to_equality_rev,[status(thm)],[c_2441])).

cnf(c_2670,plain,
    ( ~ r2_hidden(X0,sK4)
    | r2_hidden(X0,u1_struct_0(sK3)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_2665,c_22,c_2442])).

cnf(c_2671,plain,
    ( r2_hidden(X0,u1_struct_0(sK3))
    | ~ r2_hidden(X0,sK4) ),
    inference(renaming,[status(thm)],[c_2670])).

cnf(c_3568,plain,
    ( ~ r2_hidden(sK0(u1_struct_0(sK3),X0),X0)
    | ~ r2_hidden(sK0(u1_struct_0(sK3),X0),sK4)
    | X0 = u1_struct_0(sK3) ),
    inference(resolution,[status(thm)],[c_0,c_2671])).

cnf(c_1,plain,
    ( r2_hidden(sK0(X0,X1),X1)
    | r2_hidden(sK0(X0,X1),X0)
    | X1 = X0 ),
    inference(cnf_transformation,[],[f46])).

cnf(c_3951,plain,
    ( r2_hidden(sK0(u1_struct_0(sK3),sK4),u1_struct_0(sK3))
    | ~ r2_hidden(sK0(u1_struct_0(sK3),sK4),sK4)
    | sK4 = u1_struct_0(sK3) ),
    inference(resolution,[status(thm)],[c_3568,c_1])).

cnf(c_1411,plain,
    ( r2_hidden(sK0(u1_struct_0(sK3),sK4),u1_struct_0(sK3))
    | r2_hidden(sK0(u1_struct_0(sK3),sK4),sK4)
    | sK4 = u1_struct_0(sK3) ),
    inference(instantiation,[status(thm)],[c_1])).

cnf(c_3954,plain,
    ( r2_hidden(sK0(u1_struct_0(sK3),sK4),u1_struct_0(sK3))
    | sK4 = u1_struct_0(sK3) ),
    inference(global_propositional_subsumption,[status(thm)],[c_3951,c_1411])).

cnf(c_5688,plain,
    ( r2_hidden(sK0(u1_struct_0(sK3),sK4),sK4)
    | sK4 = u1_struct_0(sK3) ),
    inference(resolution,[status(thm)],[c_5457,c_3954])).

cnf(c_3541,plain,
    ( X0 != X1
    | k2_subset_1(X1) = X0 ),
    inference(resolution,[status(thm)],[c_758,c_2])).

cnf(c_384,plain,
    ( k2_subset_1(u1_struct_0(sK3)) != sK4
    | r2_hidden(k3_yellow_0(sK3),sK4) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_383])).

cnf(c_3015,plain,
    ( k2_subset_1(u1_struct_0(sK3)) != sK4 ),
    inference(global_propositional_subsumption,[status(thm)],[c_383,c_30,c_31,c_33,c_63,c_384,c_396,c_774,c_780,c_1508,c_1924,c_2210,c_2462])).

cnf(c_5101,plain,
    ( sK4 != u1_struct_0(sK3) ),
    inference(resolution,[status(thm)],[c_3541,c_3015])).

cnf(c_4010,plain,
    ( ~ r2_hidden(sK0(u1_struct_0(sK3),sK4),sK4)
    | sK4 = u1_struct_0(sK3) ),
    inference(resolution,[status(thm)],[c_3954,c_0])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_5688,c_5101,c_4010])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.12  % Command    : iproveropt_run.sh %d %s
% 0.12/0.33  % Computer   : n021.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.33  % CPULimit   : 60
% 0.12/0.33  % WCLimit    : 600
% 0.12/0.33  % DateTime   : Tue Dec  1 10:35:34 EST 2020
% 0.12/0.33  % CPUTime    : 
% 0.12/0.34  % Running in FOF mode
% 3.23/0.98  % SZS status Started for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.23/0.98  
% 3.23/0.98  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 3.23/0.98  
% 3.23/0.98  ------  iProver source info
% 3.23/0.98  
% 3.23/0.98  git: date: 2020-06-30 10:37:57 +0100
% 3.23/0.98  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 3.23/0.98  git: non_committed_changes: false
% 3.23/0.98  git: last_make_outside_of_git: false
% 3.23/0.98  
% 3.23/0.98  ------ 
% 3.23/0.98  ------ Parsing...
% 3.23/0.98  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 3.23/0.98  
% 3.23/0.98  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe:1:0s pe:2:0s pe:4:0s pe_e  sf_s  rm: 7 0s  sf_e  pe_s  pe_e 
% 3.23/0.98  
% 3.23/0.98  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 3.23/0.98  
% 3.23/0.98  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 3.23/0.98  ------ Proving...
% 3.23/0.98  ------ Problem Properties 
% 3.23/0.98  
% 3.23/0.98  
% 3.23/0.98  clauses                                 21
% 3.23/0.98  conjectures                             3
% 3.23/0.98  EPR                                     4
% 3.23/0.98  Horn                                    14
% 3.23/0.98  unary                                   5
% 3.23/0.98  binary                                  4
% 3.23/0.98  lits                                    54
% 3.23/0.98  lits eq                                 7
% 3.23/0.98  fd_pure                                 0
% 3.23/0.98  fd_pseudo                               0
% 3.23/0.98  fd_cond                                 0
% 3.23/0.98  fd_pseudo_cond                          2
% 3.23/0.98  AC symbols                              0
% 3.23/0.98  
% 3.23/0.98  ------ Input Options Time Limit: Unbounded
% 3.23/0.98  
% 3.23/0.98  
% 3.23/0.98  ------ 
% 3.23/0.98  Current options:
% 3.23/0.98  ------ 
% 3.23/0.98  
% 3.23/0.98  
% 3.23/0.98  
% 3.23/0.98  
% 3.23/0.98  ------ Proving...
% 3.23/0.98  
% 3.23/0.98  
% 3.23/0.98  % SZS status Theorem for theBenchmark.p
% 3.23/0.98  
% 3.23/0.98  % SZS output start CNFRefutation for theBenchmark.p
% 3.23/0.98  
% 3.23/0.98  fof(f11,axiom,(
% 3.23/0.98    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => (v1_subset_1(X1,X0) <=> X0 != X1))),
% 3.23/0.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.23/0.98  
% 3.23/0.98  fof(f29,plain,(
% 3.23/0.98    ! [X0,X1] : ((v1_subset_1(X1,X0) <=> X0 != X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 3.23/0.98    inference(ennf_transformation,[],[f11])).
% 3.23/0.98  
% 3.23/0.98  fof(f40,plain,(
% 3.23/0.98    ! [X0,X1] : (((v1_subset_1(X1,X0) | X0 = X1) & (X0 != X1 | ~v1_subset_1(X1,X0))) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 3.23/0.98    inference(nnf_transformation,[],[f29])).
% 3.23/0.98  
% 3.23/0.98  fof(f63,plain,(
% 3.23/0.98    ( ! [X0,X1] : (v1_subset_1(X1,X0) | X0 = X1 | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 3.23/0.98    inference(cnf_transformation,[],[f40])).
% 3.23/0.98  
% 3.23/0.98  fof(f12,conjecture,(
% 3.23/0.98    ! [X0] : ((l1_orders_2(X0) & v1_yellow_0(X0) & v5_orders_2(X0) & v4_orders_2(X0) & v3_orders_2(X0) & ~v2_struct_0(X0)) => ! [X1] : ((m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & v13_waybel_0(X1,X0) & v2_waybel_0(X1,X0) & ~v1_xboole_0(X1)) => (v1_subset_1(X1,u1_struct_0(X0)) <=> ~r2_hidden(k3_yellow_0(X0),X1))))),
% 3.23/0.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.23/0.98  
% 3.23/0.98  fof(f13,negated_conjecture,(
% 3.23/0.98    ~! [X0] : ((l1_orders_2(X0) & v1_yellow_0(X0) & v5_orders_2(X0) & v4_orders_2(X0) & v3_orders_2(X0) & ~v2_struct_0(X0)) => ! [X1] : ((m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & v13_waybel_0(X1,X0) & v2_waybel_0(X1,X0) & ~v1_xboole_0(X1)) => (v1_subset_1(X1,u1_struct_0(X0)) <=> ~r2_hidden(k3_yellow_0(X0),X1))))),
% 3.23/0.98    inference(negated_conjecture,[],[f12])).
% 3.23/0.98  
% 3.23/0.98  fof(f14,plain,(
% 3.23/0.98    ~! [X0] : ((l1_orders_2(X0) & v1_yellow_0(X0) & v5_orders_2(X0) & v4_orders_2(X0) & v3_orders_2(X0) & ~v2_struct_0(X0)) => ! [X1] : ((m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & v13_waybel_0(X1,X0) & ~v1_xboole_0(X1)) => (v1_subset_1(X1,u1_struct_0(X0)) <=> ~r2_hidden(k3_yellow_0(X0),X1))))),
% 3.23/0.98    inference(pure_predicate_removal,[],[f13])).
% 3.23/0.98  
% 3.23/0.98  fof(f15,plain,(
% 3.23/0.98    ~! [X0] : ((l1_orders_2(X0) & v1_yellow_0(X0) & v5_orders_2(X0) & v3_orders_2(X0) & ~v2_struct_0(X0)) => ! [X1] : ((m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & v13_waybel_0(X1,X0) & ~v1_xboole_0(X1)) => (v1_subset_1(X1,u1_struct_0(X0)) <=> ~r2_hidden(k3_yellow_0(X0),X1))))),
% 3.23/0.98    inference(pure_predicate_removal,[],[f14])).
% 3.23/0.98  
% 3.23/0.98  fof(f16,plain,(
% 3.23/0.98    ~! [X0] : ((l1_orders_2(X0) & v1_yellow_0(X0) & v5_orders_2(X0) & ~v2_struct_0(X0)) => ! [X1] : ((m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & v13_waybel_0(X1,X0) & ~v1_xboole_0(X1)) => (v1_subset_1(X1,u1_struct_0(X0)) <=> ~r2_hidden(k3_yellow_0(X0),X1))))),
% 3.23/0.98    inference(pure_predicate_removal,[],[f15])).
% 3.23/0.98  
% 3.23/0.98  fof(f30,plain,(
% 3.23/0.98    ? [X0] : (? [X1] : ((v1_subset_1(X1,u1_struct_0(X0)) <~> ~r2_hidden(k3_yellow_0(X0),X1)) & (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & v13_waybel_0(X1,X0) & ~v1_xboole_0(X1))) & (l1_orders_2(X0) & v1_yellow_0(X0) & v5_orders_2(X0) & ~v2_struct_0(X0)))),
% 3.23/0.98    inference(ennf_transformation,[],[f16])).
% 3.23/0.98  
% 3.23/0.98  fof(f31,plain,(
% 3.23/0.98    ? [X0] : (? [X1] : ((v1_subset_1(X1,u1_struct_0(X0)) <~> ~r2_hidden(k3_yellow_0(X0),X1)) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & v13_waybel_0(X1,X0) & ~v1_xboole_0(X1)) & l1_orders_2(X0) & v1_yellow_0(X0) & v5_orders_2(X0) & ~v2_struct_0(X0))),
% 3.23/0.98    inference(flattening,[],[f30])).
% 3.23/0.98  
% 3.23/0.98  fof(f41,plain,(
% 3.23/0.98    ? [X0] : (? [X1] : (((r2_hidden(k3_yellow_0(X0),X1) | ~v1_subset_1(X1,u1_struct_0(X0))) & (~r2_hidden(k3_yellow_0(X0),X1) | v1_subset_1(X1,u1_struct_0(X0)))) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & v13_waybel_0(X1,X0) & ~v1_xboole_0(X1)) & l1_orders_2(X0) & v1_yellow_0(X0) & v5_orders_2(X0) & ~v2_struct_0(X0))),
% 3.23/0.98    inference(nnf_transformation,[],[f31])).
% 3.23/0.98  
% 3.23/0.98  fof(f42,plain,(
% 3.23/0.98    ? [X0] : (? [X1] : ((r2_hidden(k3_yellow_0(X0),X1) | ~v1_subset_1(X1,u1_struct_0(X0))) & (~r2_hidden(k3_yellow_0(X0),X1) | v1_subset_1(X1,u1_struct_0(X0))) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & v13_waybel_0(X1,X0) & ~v1_xboole_0(X1)) & l1_orders_2(X0) & v1_yellow_0(X0) & v5_orders_2(X0) & ~v2_struct_0(X0))),
% 3.23/0.98    inference(flattening,[],[f41])).
% 3.23/0.98  
% 3.23/0.98  fof(f44,plain,(
% 3.23/0.98    ( ! [X0] : (? [X1] : ((r2_hidden(k3_yellow_0(X0),X1) | ~v1_subset_1(X1,u1_struct_0(X0))) & (~r2_hidden(k3_yellow_0(X0),X1) | v1_subset_1(X1,u1_struct_0(X0))) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & v13_waybel_0(X1,X0) & ~v1_xboole_0(X1)) => ((r2_hidden(k3_yellow_0(X0),sK4) | ~v1_subset_1(sK4,u1_struct_0(X0))) & (~r2_hidden(k3_yellow_0(X0),sK4) | v1_subset_1(sK4,u1_struct_0(X0))) & m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(X0))) & v13_waybel_0(sK4,X0) & ~v1_xboole_0(sK4))) )),
% 3.23/0.98    introduced(choice_axiom,[])).
% 3.23/0.98  
% 3.23/0.98  fof(f43,plain,(
% 3.23/0.98    ? [X0] : (? [X1] : ((r2_hidden(k3_yellow_0(X0),X1) | ~v1_subset_1(X1,u1_struct_0(X0))) & (~r2_hidden(k3_yellow_0(X0),X1) | v1_subset_1(X1,u1_struct_0(X0))) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & v13_waybel_0(X1,X0) & ~v1_xboole_0(X1)) & l1_orders_2(X0) & v1_yellow_0(X0) & v5_orders_2(X0) & ~v2_struct_0(X0)) => (? [X1] : ((r2_hidden(k3_yellow_0(sK3),X1) | ~v1_subset_1(X1,u1_struct_0(sK3))) & (~r2_hidden(k3_yellow_0(sK3),X1) | v1_subset_1(X1,u1_struct_0(sK3))) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK3))) & v13_waybel_0(X1,sK3) & ~v1_xboole_0(X1)) & l1_orders_2(sK3) & v1_yellow_0(sK3) & v5_orders_2(sK3) & ~v2_struct_0(sK3))),
% 3.23/0.98    introduced(choice_axiom,[])).
% 3.23/0.98  
% 3.23/0.98  fof(f45,plain,(
% 3.23/0.98    ((r2_hidden(k3_yellow_0(sK3),sK4) | ~v1_subset_1(sK4,u1_struct_0(sK3))) & (~r2_hidden(k3_yellow_0(sK3),sK4) | v1_subset_1(sK4,u1_struct_0(sK3))) & m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(sK3))) & v13_waybel_0(sK4,sK3) & ~v1_xboole_0(sK4)) & l1_orders_2(sK3) & v1_yellow_0(sK3) & v5_orders_2(sK3) & ~v2_struct_0(sK3)),
% 3.23/0.98    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3,sK4])],[f42,f44,f43])).
% 3.23/0.98  
% 3.23/0.98  fof(f72,plain,(
% 3.23/0.98    r2_hidden(k3_yellow_0(sK3),sK4) | ~v1_subset_1(sK4,u1_struct_0(sK3))),
% 3.23/0.98    inference(cnf_transformation,[],[f45])).
% 3.23/0.98  
% 3.23/0.98  fof(f70,plain,(
% 3.23/0.98    m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(sK3)))),
% 3.23/0.98    inference(cnf_transformation,[],[f45])).
% 3.23/0.98  
% 3.23/0.98  fof(f4,axiom,(
% 3.23/0.98    ! [X0] : ~v1_subset_1(k2_subset_1(X0),X0)),
% 3.23/0.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.23/0.98  
% 3.23/0.98  fof(f50,plain,(
% 3.23/0.98    ( ! [X0] : (~v1_subset_1(k2_subset_1(X0),X0)) )),
% 3.23/0.98    inference(cnf_transformation,[],[f4])).
% 3.23/0.98  
% 3.23/0.98  fof(f71,plain,(
% 3.23/0.98    ~r2_hidden(k3_yellow_0(sK3),sK4) | v1_subset_1(sK4,u1_struct_0(sK3))),
% 3.23/0.98    inference(cnf_transformation,[],[f45])).
% 3.23/0.98  
% 3.23/0.98  fof(f2,axiom,(
% 3.23/0.98    ! [X0] : k2_subset_1(X0) = X0),
% 3.23/0.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.23/0.98  
% 3.23/0.98  fof(f48,plain,(
% 3.23/0.98    ( ! [X0] : (k2_subset_1(X0) = X0) )),
% 3.23/0.98    inference(cnf_transformation,[],[f2])).
% 3.23/0.98  
% 3.23/0.98  fof(f67,plain,(
% 3.23/0.98    l1_orders_2(sK3)),
% 3.23/0.98    inference(cnf_transformation,[],[f45])).
% 3.23/0.98  
% 3.23/0.98  fof(f68,plain,(
% 3.23/0.98    ~v1_xboole_0(sK4)),
% 3.23/0.98    inference(cnf_transformation,[],[f45])).
% 3.23/0.98  
% 3.23/0.98  fof(f8,axiom,(
% 3.23/0.98    ! [X0] : (l1_orders_2(X0) => m1_subset_1(k3_yellow_0(X0),u1_struct_0(X0)))),
% 3.23/0.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.23/0.98  
% 3.23/0.98  fof(f24,plain,(
% 3.23/0.98    ! [X0] : (m1_subset_1(k3_yellow_0(X0),u1_struct_0(X0)) | ~l1_orders_2(X0))),
% 3.23/0.98    inference(ennf_transformation,[],[f8])).
% 3.23/0.98  
% 3.23/0.98  fof(f54,plain,(
% 3.23/0.98    ( ! [X0] : (m1_subset_1(k3_yellow_0(X0),u1_struct_0(X0)) | ~l1_orders_2(X0)) )),
% 3.23/0.98    inference(cnf_transformation,[],[f24])).
% 3.23/0.98  
% 3.23/0.98  fof(f6,axiom,(
% 3.23/0.98    ! [X0,X1] : (m1_subset_1(X0,X1) => (r2_hidden(X0,X1) | v1_xboole_0(X1)))),
% 3.23/0.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.23/0.98  
% 3.23/0.98  fof(f20,plain,(
% 3.23/0.98    ! [X0,X1] : ((r2_hidden(X0,X1) | v1_xboole_0(X1)) | ~m1_subset_1(X0,X1))),
% 3.23/0.98    inference(ennf_transformation,[],[f6])).
% 3.23/0.98  
% 3.23/0.98  fof(f21,plain,(
% 3.23/0.98    ! [X0,X1] : (r2_hidden(X0,X1) | v1_xboole_0(X1) | ~m1_subset_1(X0,X1))),
% 3.23/0.98    inference(flattening,[],[f20])).
% 3.23/0.98  
% 3.23/0.98  fof(f52,plain,(
% 3.23/0.98    ( ! [X0,X1] : (r2_hidden(X0,X1) | v1_xboole_0(X1) | ~m1_subset_1(X0,X1)) )),
% 3.23/0.98    inference(cnf_transformation,[],[f21])).
% 3.23/0.98  
% 3.23/0.98  fof(f10,axiom,(
% 3.23/0.98    ! [X0] : (l1_orders_2(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => (v13_waybel_0(X1,X0) <=> ! [X2] : (m1_subset_1(X2,u1_struct_0(X0)) => ! [X3] : (m1_subset_1(X3,u1_struct_0(X0)) => ((r1_orders_2(X0,X2,X3) & r2_hidden(X2,X1)) => r2_hidden(X3,X1)))))))),
% 3.23/0.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.23/0.98  
% 3.23/0.98  fof(f27,plain,(
% 3.23/0.98    ! [X0] : (! [X1] : ((v13_waybel_0(X1,X0) <=> ! [X2] : (! [X3] : ((r2_hidden(X3,X1) | (~r1_orders_2(X0,X2,X3) | ~r2_hidden(X2,X1))) | ~m1_subset_1(X3,u1_struct_0(X0))) | ~m1_subset_1(X2,u1_struct_0(X0)))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_orders_2(X0))),
% 3.23/0.98    inference(ennf_transformation,[],[f10])).
% 3.23/0.98  
% 3.23/0.98  fof(f28,plain,(
% 3.23/0.98    ! [X0] : (! [X1] : ((v13_waybel_0(X1,X0) <=> ! [X2] : (! [X3] : (r2_hidden(X3,X1) | ~r1_orders_2(X0,X2,X3) | ~r2_hidden(X2,X1) | ~m1_subset_1(X3,u1_struct_0(X0))) | ~m1_subset_1(X2,u1_struct_0(X0)))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_orders_2(X0))),
% 3.23/0.98    inference(flattening,[],[f27])).
% 3.23/0.98  
% 3.23/0.98  fof(f35,plain,(
% 3.23/0.98    ! [X0] : (! [X1] : (((v13_waybel_0(X1,X0) | ? [X2] : (? [X3] : (~r2_hidden(X3,X1) & r1_orders_2(X0,X2,X3) & r2_hidden(X2,X1) & m1_subset_1(X3,u1_struct_0(X0))) & m1_subset_1(X2,u1_struct_0(X0)))) & (! [X2] : (! [X3] : (r2_hidden(X3,X1) | ~r1_orders_2(X0,X2,X3) | ~r2_hidden(X2,X1) | ~m1_subset_1(X3,u1_struct_0(X0))) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~v13_waybel_0(X1,X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_orders_2(X0))),
% 3.23/0.98    inference(nnf_transformation,[],[f28])).
% 3.23/0.98  
% 3.23/0.98  fof(f36,plain,(
% 3.23/0.98    ! [X0] : (! [X1] : (((v13_waybel_0(X1,X0) | ? [X2] : (? [X3] : (~r2_hidden(X3,X1) & r1_orders_2(X0,X2,X3) & r2_hidden(X2,X1) & m1_subset_1(X3,u1_struct_0(X0))) & m1_subset_1(X2,u1_struct_0(X0)))) & (! [X4] : (! [X5] : (r2_hidden(X5,X1) | ~r1_orders_2(X0,X4,X5) | ~r2_hidden(X4,X1) | ~m1_subset_1(X5,u1_struct_0(X0))) | ~m1_subset_1(X4,u1_struct_0(X0))) | ~v13_waybel_0(X1,X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_orders_2(X0))),
% 3.23/0.98    inference(rectify,[],[f35])).
% 3.23/0.98  
% 3.23/0.98  fof(f38,plain,(
% 3.23/0.98    ( ! [X2] : (! [X1,X0] : (? [X3] : (~r2_hidden(X3,X1) & r1_orders_2(X0,X2,X3) & r2_hidden(X2,X1) & m1_subset_1(X3,u1_struct_0(X0))) => (~r2_hidden(sK2(X0,X1),X1) & r1_orders_2(X0,X2,sK2(X0,X1)) & r2_hidden(X2,X1) & m1_subset_1(sK2(X0,X1),u1_struct_0(X0))))) )),
% 3.23/0.98    introduced(choice_axiom,[])).
% 3.23/0.98  
% 3.23/0.98  fof(f37,plain,(
% 3.23/0.98    ! [X1,X0] : (? [X2] : (? [X3] : (~r2_hidden(X3,X1) & r1_orders_2(X0,X2,X3) & r2_hidden(X2,X1) & m1_subset_1(X3,u1_struct_0(X0))) & m1_subset_1(X2,u1_struct_0(X0))) => (? [X3] : (~r2_hidden(X3,X1) & r1_orders_2(X0,sK1(X0,X1),X3) & r2_hidden(sK1(X0,X1),X1) & m1_subset_1(X3,u1_struct_0(X0))) & m1_subset_1(sK1(X0,X1),u1_struct_0(X0))))),
% 3.23/0.98    introduced(choice_axiom,[])).
% 3.23/0.98  
% 3.23/0.98  fof(f39,plain,(
% 3.23/0.98    ! [X0] : (! [X1] : (((v13_waybel_0(X1,X0) | ((~r2_hidden(sK2(X0,X1),X1) & r1_orders_2(X0,sK1(X0,X1),sK2(X0,X1)) & r2_hidden(sK1(X0,X1),X1) & m1_subset_1(sK2(X0,X1),u1_struct_0(X0))) & m1_subset_1(sK1(X0,X1),u1_struct_0(X0)))) & (! [X4] : (! [X5] : (r2_hidden(X5,X1) | ~r1_orders_2(X0,X4,X5) | ~r2_hidden(X4,X1) | ~m1_subset_1(X5,u1_struct_0(X0))) | ~m1_subset_1(X4,u1_struct_0(X0))) | ~v13_waybel_0(X1,X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_orders_2(X0))),
% 3.23/0.98    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1,sK2])],[f36,f38,f37])).
% 3.23/0.98  
% 3.23/0.98  fof(f56,plain,(
% 3.23/0.98    ( ! [X4,X0,X5,X1] : (r2_hidden(X5,X1) | ~r1_orders_2(X0,X4,X5) | ~r2_hidden(X4,X1) | ~m1_subset_1(X5,u1_struct_0(X0)) | ~m1_subset_1(X4,u1_struct_0(X0)) | ~v13_waybel_0(X1,X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_orders_2(X0)) )),
% 3.23/0.98    inference(cnf_transformation,[],[f39])).
% 3.23/0.98  
% 3.23/0.98  fof(f9,axiom,(
% 3.23/0.98    ! [X0] : ((l1_orders_2(X0) & v1_yellow_0(X0) & v5_orders_2(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,u1_struct_0(X0)) => r1_orders_2(X0,k3_yellow_0(X0),X1)))),
% 3.23/0.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.23/0.98  
% 3.23/0.98  fof(f25,plain,(
% 3.23/0.98    ! [X0] : (! [X1] : (r1_orders_2(X0,k3_yellow_0(X0),X1) | ~m1_subset_1(X1,u1_struct_0(X0))) | (~l1_orders_2(X0) | ~v1_yellow_0(X0) | ~v5_orders_2(X0) | v2_struct_0(X0)))),
% 3.23/0.98    inference(ennf_transformation,[],[f9])).
% 3.23/0.98  
% 3.23/0.98  fof(f26,plain,(
% 3.23/0.98    ! [X0] : (! [X1] : (r1_orders_2(X0,k3_yellow_0(X0),X1) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~l1_orders_2(X0) | ~v1_yellow_0(X0) | ~v5_orders_2(X0) | v2_struct_0(X0))),
% 3.23/0.98    inference(flattening,[],[f25])).
% 3.23/0.98  
% 3.23/0.98  fof(f55,plain,(
% 3.23/0.98    ( ! [X0,X1] : (r1_orders_2(X0,k3_yellow_0(X0),X1) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_orders_2(X0) | ~v1_yellow_0(X0) | ~v5_orders_2(X0) | v2_struct_0(X0)) )),
% 3.23/0.98    inference(cnf_transformation,[],[f26])).
% 3.23/0.98  
% 3.23/0.98  fof(f66,plain,(
% 3.23/0.98    v1_yellow_0(sK3)),
% 3.23/0.98    inference(cnf_transformation,[],[f45])).
% 3.23/0.98  
% 3.23/0.98  fof(f64,plain,(
% 3.23/0.98    ~v2_struct_0(sK3)),
% 3.23/0.98    inference(cnf_transformation,[],[f45])).
% 3.23/0.98  
% 3.23/0.98  fof(f65,plain,(
% 3.23/0.98    v5_orders_2(sK3)),
% 3.23/0.98    inference(cnf_transformation,[],[f45])).
% 3.23/0.98  
% 3.23/0.98  fof(f69,plain,(
% 3.23/0.98    v13_waybel_0(sK4,sK3)),
% 3.23/0.98    inference(cnf_transformation,[],[f45])).
% 3.23/0.98  
% 3.23/0.98  fof(f5,axiom,(
% 3.23/0.98    ! [X0,X1] : (r2_hidden(X0,X1) => m1_subset_1(X0,X1))),
% 3.23/0.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.23/0.98  
% 3.23/0.98  fof(f19,plain,(
% 3.23/0.98    ! [X0,X1] : (m1_subset_1(X0,X1) | ~r2_hidden(X0,X1))),
% 3.23/0.98    inference(ennf_transformation,[],[f5])).
% 3.23/0.98  
% 3.23/0.98  fof(f51,plain,(
% 3.23/0.98    ( ! [X0,X1] : (m1_subset_1(X0,X1) | ~r2_hidden(X0,X1)) )),
% 3.23/0.98    inference(cnf_transformation,[],[f19])).
% 3.23/0.98  
% 3.23/0.98  fof(f1,axiom,(
% 3.23/0.98    ! [X0,X1] : (! [X2] : (r2_hidden(X2,X0) <=> r2_hidden(X2,X1)) => X0 = X1)),
% 3.23/0.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.23/0.98  
% 3.23/0.98  fof(f17,plain,(
% 3.23/0.98    ! [X0,X1] : (X0 = X1 | ? [X2] : (r2_hidden(X2,X0) <~> r2_hidden(X2,X1)))),
% 3.23/0.98    inference(ennf_transformation,[],[f1])).
% 3.23/0.98  
% 3.23/0.98  fof(f32,plain,(
% 3.23/0.98    ! [X0,X1] : (X0 = X1 | ? [X2] : ((~r2_hidden(X2,X1) | ~r2_hidden(X2,X0)) & (r2_hidden(X2,X1) | r2_hidden(X2,X0))))),
% 3.23/0.98    inference(nnf_transformation,[],[f17])).
% 3.23/0.98  
% 3.23/0.98  fof(f33,plain,(
% 3.23/0.98    ! [X1,X0] : (? [X2] : ((~r2_hidden(X2,X1) | ~r2_hidden(X2,X0)) & (r2_hidden(X2,X1) | r2_hidden(X2,X0))) => ((~r2_hidden(sK0(X0,X1),X1) | ~r2_hidden(sK0(X0,X1),X0)) & (r2_hidden(sK0(X0,X1),X1) | r2_hidden(sK0(X0,X1),X0))))),
% 3.23/0.98    introduced(choice_axiom,[])).
% 3.23/0.98  
% 3.23/0.98  fof(f34,plain,(
% 3.23/0.98    ! [X0,X1] : (X0 = X1 | ((~r2_hidden(sK0(X0,X1),X1) | ~r2_hidden(sK0(X0,X1),X0)) & (r2_hidden(sK0(X0,X1),X1) | r2_hidden(sK0(X0,X1),X0))))),
% 3.23/0.98    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f32,f33])).
% 3.23/0.98  
% 3.23/0.98  fof(f47,plain,(
% 3.23/0.98    ( ! [X0,X1] : (X0 = X1 | ~r2_hidden(sK0(X0,X1),X1) | ~r2_hidden(sK0(X0,X1),X0)) )),
% 3.23/0.99    inference(cnf_transformation,[],[f34])).
% 3.23/0.99  
% 3.23/0.99  fof(f7,axiom,(
% 3.23/0.99    ! [X0,X1,X2] : ((m1_subset_1(X1,k1_zfmisc_1(X2)) & r2_hidden(X0,X1)) => m1_subset_1(X0,X2))),
% 3.23/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.23/0.99  
% 3.23/0.99  fof(f22,plain,(
% 3.23/0.99    ! [X0,X1,X2] : (m1_subset_1(X0,X2) | (~m1_subset_1(X1,k1_zfmisc_1(X2)) | ~r2_hidden(X0,X1)))),
% 3.23/0.99    inference(ennf_transformation,[],[f7])).
% 3.23/0.99  
% 3.23/0.99  fof(f23,plain,(
% 3.23/0.99    ! [X0,X1,X2] : (m1_subset_1(X0,X2) | ~m1_subset_1(X1,k1_zfmisc_1(X2)) | ~r2_hidden(X0,X1))),
% 3.23/0.99    inference(flattening,[],[f22])).
% 3.23/0.99  
% 3.23/0.99  fof(f53,plain,(
% 3.23/0.99    ( ! [X2,X0,X1] : (m1_subset_1(X0,X2) | ~m1_subset_1(X1,k1_zfmisc_1(X2)) | ~r2_hidden(X0,X1)) )),
% 3.23/0.99    inference(cnf_transformation,[],[f23])).
% 3.23/0.99  
% 3.23/0.99  fof(f3,axiom,(
% 3.23/0.99    ! [X0] : (v1_xboole_0(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => v1_xboole_0(X1)))),
% 3.23/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.23/0.99  
% 3.23/0.99  fof(f18,plain,(
% 3.23/0.99    ! [X0] : (! [X1] : (v1_xboole_0(X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) | ~v1_xboole_0(X0))),
% 3.23/0.99    inference(ennf_transformation,[],[f3])).
% 3.23/0.99  
% 3.23/0.99  fof(f49,plain,(
% 3.23/0.99    ( ! [X0,X1] : (v1_xboole_0(X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0)) | ~v1_xboole_0(X0)) )),
% 3.23/0.99    inference(cnf_transformation,[],[f18])).
% 3.23/0.99  
% 3.23/0.99  fof(f46,plain,(
% 3.23/0.99    ( ! [X0,X1] : (X0 = X1 | r2_hidden(sK0(X0,X1),X1) | r2_hidden(sK0(X0,X1),X0)) )),
% 3.23/0.99    inference(cnf_transformation,[],[f34])).
% 3.23/0.99  
% 3.23/0.99  cnf(c_759,plain,
% 3.23/0.99      ( ~ r2_hidden(X0,X1) | r2_hidden(X2,X3) | X2 != X0 | X3 != X1 ),
% 3.23/0.99      theory(equality) ).
% 3.23/0.99  
% 3.23/0.99  cnf(c_757,plain,( X0 = X0 ),theory(equality) ).
% 3.23/0.99  
% 3.23/0.99  cnf(c_3586,plain,
% 3.23/0.99      ( ~ r2_hidden(X0,X1) | r2_hidden(X2,X1) | X2 != X0 ),
% 3.23/0.99      inference(resolution,[status(thm)],[c_759,c_757]) ).
% 3.23/0.99  
% 3.23/0.99  cnf(c_16,plain,
% 3.23/0.99      ( v1_subset_1(X0,X1)
% 3.23/0.99      | ~ m1_subset_1(X0,k1_zfmisc_1(X1))
% 3.23/0.99      | X0 = X1 ),
% 3.23/0.99      inference(cnf_transformation,[],[f63]) ).
% 3.23/0.99  
% 3.23/0.99  cnf(c_18,negated_conjecture,
% 3.23/0.99      ( ~ v1_subset_1(sK4,u1_struct_0(sK3))
% 3.23/0.99      | r2_hidden(k3_yellow_0(sK3),sK4) ),
% 3.23/0.99      inference(cnf_transformation,[],[f72]) ).
% 3.23/0.99  
% 3.23/0.99  cnf(c_195,plain,
% 3.23/0.99      ( ~ v1_subset_1(sK4,u1_struct_0(sK3))
% 3.23/0.99      | r2_hidden(k3_yellow_0(sK3),sK4) ),
% 3.23/0.99      inference(prop_impl,[status(thm)],[c_18]) ).
% 3.23/0.99  
% 3.23/0.99  cnf(c_394,plain,
% 3.23/0.99      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
% 3.23/0.99      | r2_hidden(k3_yellow_0(sK3),sK4)
% 3.23/0.99      | X1 = X0
% 3.23/0.99      | u1_struct_0(sK3) != X1
% 3.23/0.99      | sK4 != X0 ),
% 3.23/0.99      inference(resolution_lifted,[status(thm)],[c_16,c_195]) ).
% 3.23/0.99  
% 3.23/0.99  cnf(c_395,plain,
% 3.23/0.99      ( ~ m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(sK3)))
% 3.23/0.99      | r2_hidden(k3_yellow_0(sK3),sK4)
% 3.23/0.99      | u1_struct_0(sK3) = sK4 ),
% 3.23/0.99      inference(unflattening,[status(thm)],[c_394]) ).
% 3.23/0.99  
% 3.23/0.99  cnf(c_20,negated_conjecture,
% 3.23/0.99      ( m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(sK3))) ),
% 3.23/0.99      inference(cnf_transformation,[],[f70]) ).
% 3.23/0.99  
% 3.23/0.99  cnf(c_397,plain,
% 3.23/0.99      ( r2_hidden(k3_yellow_0(sK3),sK4) | u1_struct_0(sK3) = sK4 ),
% 3.23/0.99      inference(global_propositional_subsumption,
% 3.23/0.99                [status(thm)],
% 3.23/0.99                [c_395,c_20]) ).
% 3.23/0.99  
% 3.23/0.99  cnf(c_4221,plain,
% 3.23/0.99      ( r2_hidden(u1_struct_0(sK3),X0)
% 3.23/0.99      | r2_hidden(k3_yellow_0(sK3),sK4)
% 3.23/0.99      | ~ r2_hidden(sK4,X0) ),
% 3.23/0.99      inference(resolution,[status(thm)],[c_3586,c_397]) ).
% 3.23/0.99  
% 3.23/0.99  cnf(c_4,plain,
% 3.23/0.99      ( ~ v1_subset_1(k2_subset_1(X0),X0) ),
% 3.23/0.99      inference(cnf_transformation,[],[f50]) ).
% 3.23/0.99  
% 3.23/0.99  cnf(c_19,negated_conjecture,
% 3.23/0.99      ( v1_subset_1(sK4,u1_struct_0(sK3))
% 3.23/0.99      | ~ r2_hidden(k3_yellow_0(sK3),sK4) ),
% 3.23/0.99      inference(cnf_transformation,[],[f71]) ).
% 3.23/0.99  
% 3.23/0.99  cnf(c_193,plain,
% 3.23/0.99      ( v1_subset_1(sK4,u1_struct_0(sK3))
% 3.23/0.99      | ~ r2_hidden(k3_yellow_0(sK3),sK4) ),
% 3.23/0.99      inference(prop_impl,[status(thm)],[c_19]) ).
% 3.23/0.99  
% 3.23/0.99  cnf(c_382,plain,
% 3.23/0.99      ( ~ r2_hidden(k3_yellow_0(sK3),sK4)
% 3.23/0.99      | u1_struct_0(sK3) != X0
% 3.23/0.99      | k2_subset_1(X0) != sK4 ),
% 3.23/0.99      inference(resolution_lifted,[status(thm)],[c_4,c_193]) ).
% 3.23/0.99  
% 3.23/0.99  cnf(c_383,plain,
% 3.23/0.99      ( ~ r2_hidden(k3_yellow_0(sK3),sK4)
% 3.23/0.99      | k2_subset_1(u1_struct_0(sK3)) != sK4 ),
% 3.23/0.99      inference(unflattening,[status(thm)],[c_382]) ).
% 3.23/0.99  
% 3.23/0.99  cnf(c_1154,plain,
% 3.23/0.99      ( k2_subset_1(u1_struct_0(sK3)) != sK4
% 3.23/0.99      | r2_hidden(k3_yellow_0(sK3),sK4) != iProver_top ),
% 3.23/0.99      inference(predicate_to_equality,[status(thm)],[c_383]) ).
% 3.23/0.99  
% 3.23/0.99  cnf(c_2,plain,
% 3.23/0.99      ( k2_subset_1(X0) = X0 ),
% 3.23/0.99      inference(cnf_transformation,[],[f48]) ).
% 3.23/0.99  
% 3.23/0.99  cnf(c_1185,plain,
% 3.23/0.99      ( u1_struct_0(sK3) != sK4
% 3.23/0.99      | r2_hidden(k3_yellow_0(sK3),sK4) != iProver_top ),
% 3.23/0.99      inference(demodulation,[status(thm)],[c_1154,c_2]) ).
% 3.23/0.99  
% 3.23/0.99  cnf(c_1153,plain,
% 3.23/0.99      ( u1_struct_0(sK3) = sK4
% 3.23/0.99      | r2_hidden(k3_yellow_0(sK3),sK4) = iProver_top ),
% 3.23/0.99      inference(predicate_to_equality,[status(thm)],[c_397]) ).
% 3.23/0.99  
% 3.23/0.99  cnf(c_23,negated_conjecture,
% 3.23/0.99      ( l1_orders_2(sK3) ),
% 3.23/0.99      inference(cnf_transformation,[],[f67]) ).
% 3.23/0.99  
% 3.23/0.99  cnf(c_30,plain,
% 3.23/0.99      ( l1_orders_2(sK3) = iProver_top ),
% 3.23/0.99      inference(predicate_to_equality,[status(thm)],[c_23]) ).
% 3.23/0.99  
% 3.23/0.99  cnf(c_22,negated_conjecture,
% 3.23/0.99      ( ~ v1_xboole_0(sK4) ),
% 3.23/0.99      inference(cnf_transformation,[],[f68]) ).
% 3.23/0.99  
% 3.23/0.99  cnf(c_31,plain,
% 3.23/0.99      ( v1_xboole_0(sK4) != iProver_top ),
% 3.23/0.99      inference(predicate_to_equality,[status(thm)],[c_22]) ).
% 3.23/0.99  
% 3.23/0.99  cnf(c_33,plain,
% 3.23/0.99      ( m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(sK3))) = iProver_top ),
% 3.23/0.99      inference(predicate_to_equality,[status(thm)],[c_20]) ).
% 3.23/0.99  
% 3.23/0.99  cnf(c_8,plain,
% 3.23/0.99      ( m1_subset_1(k3_yellow_0(X0),u1_struct_0(X0))
% 3.23/0.99      | ~ l1_orders_2(X0) ),
% 3.23/0.99      inference(cnf_transformation,[],[f54]) ).
% 3.23/0.99  
% 3.23/0.99  cnf(c_61,plain,
% 3.23/0.99      ( m1_subset_1(k3_yellow_0(X0),u1_struct_0(X0)) = iProver_top
% 3.23/0.99      | l1_orders_2(X0) != iProver_top ),
% 3.23/0.99      inference(predicate_to_equality,[status(thm)],[c_8]) ).
% 3.23/0.99  
% 3.23/0.99  cnf(c_63,plain,
% 3.23/0.99      ( m1_subset_1(k3_yellow_0(sK3),u1_struct_0(sK3)) = iProver_top
% 3.23/0.99      | l1_orders_2(sK3) != iProver_top ),
% 3.23/0.99      inference(instantiation,[status(thm)],[c_61]) ).
% 3.23/0.99  
% 3.23/0.99  cnf(c_396,plain,
% 3.23/0.99      ( u1_struct_0(sK3) = sK4
% 3.23/0.99      | m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(sK3))) != iProver_top
% 3.23/0.99      | r2_hidden(k3_yellow_0(sK3),sK4) = iProver_top ),
% 3.23/0.99      inference(predicate_to_equality,[status(thm)],[c_395]) ).
% 3.23/0.99  
% 3.23/0.99  cnf(c_764,plain,
% 3.23/0.99      ( X0 != X1 | k3_yellow_0(X0) = k3_yellow_0(X1) ),
% 3.23/0.99      theory(equality) ).
% 3.23/0.99  
% 3.23/0.99  cnf(c_774,plain,
% 3.23/0.99      ( k3_yellow_0(sK3) = k3_yellow_0(sK3) | sK3 != sK3 ),
% 3.23/0.99      inference(instantiation,[status(thm)],[c_764]) ).
% 3.23/0.99  
% 3.23/0.99  cnf(c_780,plain,
% 3.23/0.99      ( sK3 = sK3 ),
% 3.23/0.99      inference(instantiation,[status(thm)],[c_757]) ).
% 3.23/0.99  
% 3.23/0.99  cnf(c_1508,plain,
% 3.23/0.99      ( sK4 = sK4 ),
% 3.23/0.99      inference(instantiation,[status(thm)],[c_757]) ).
% 3.23/0.99  
% 3.23/0.99  cnf(c_763,plain,
% 3.23/0.99      ( ~ m1_subset_1(X0,X1) | m1_subset_1(X2,X3) | X2 != X0 | X3 != X1 ),
% 3.23/0.99      theory(equality) ).
% 3.23/0.99  
% 3.23/0.99  cnf(c_1424,plain,
% 3.23/0.99      ( m1_subset_1(X0,X1)
% 3.23/0.99      | ~ m1_subset_1(k3_yellow_0(sK3),u1_struct_0(sK3))
% 3.23/0.99      | X1 != u1_struct_0(sK3)
% 3.23/0.99      | X0 != k3_yellow_0(sK3) ),
% 3.23/0.99      inference(instantiation,[status(thm)],[c_763]) ).
% 3.23/0.99  
% 3.23/0.99  cnf(c_1543,plain,
% 3.23/0.99      ( m1_subset_1(k3_yellow_0(sK3),X0)
% 3.23/0.99      | ~ m1_subset_1(k3_yellow_0(sK3),u1_struct_0(sK3))
% 3.23/0.99      | X0 != u1_struct_0(sK3)
% 3.23/0.99      | k3_yellow_0(sK3) != k3_yellow_0(sK3) ),
% 3.23/0.99      inference(instantiation,[status(thm)],[c_1424]) ).
% 3.23/0.99  
% 3.23/0.99  cnf(c_1920,plain,
% 3.23/0.99      ( ~ m1_subset_1(k3_yellow_0(sK3),u1_struct_0(sK3))
% 3.23/0.99      | m1_subset_1(k3_yellow_0(sK3),sK4)
% 3.23/0.99      | k3_yellow_0(sK3) != k3_yellow_0(sK3)
% 3.23/0.99      | sK4 != u1_struct_0(sK3) ),
% 3.23/0.99      inference(instantiation,[status(thm)],[c_1543]) ).
% 3.23/0.99  
% 3.23/0.99  cnf(c_1924,plain,
% 3.23/0.99      ( k3_yellow_0(sK3) != k3_yellow_0(sK3)
% 3.23/0.99      | sK4 != u1_struct_0(sK3)
% 3.23/0.99      | m1_subset_1(k3_yellow_0(sK3),u1_struct_0(sK3)) != iProver_top
% 3.23/0.99      | m1_subset_1(k3_yellow_0(sK3),sK4) = iProver_top ),
% 3.23/0.99      inference(predicate_to_equality,[status(thm)],[c_1920]) ).
% 3.23/0.99  
% 3.23/0.99  cnf(c_6,plain,
% 3.23/0.99      ( ~ m1_subset_1(X0,X1) | r2_hidden(X0,X1) | v1_xboole_0(X1) ),
% 3.23/0.99      inference(cnf_transformation,[],[f52]) ).
% 3.23/0.99  
% 3.23/0.99  cnf(c_1714,plain,
% 3.23/0.99      ( ~ m1_subset_1(X0,sK4) | r2_hidden(X0,sK4) | v1_xboole_0(sK4) ),
% 3.23/0.99      inference(instantiation,[status(thm)],[c_6]) ).
% 3.23/0.99  
% 3.23/0.99  cnf(c_2209,plain,
% 3.23/0.99      ( ~ m1_subset_1(k3_yellow_0(sK3),sK4)
% 3.23/0.99      | r2_hidden(k3_yellow_0(sK3),sK4)
% 3.23/0.99      | v1_xboole_0(sK4) ),
% 3.23/0.99      inference(instantiation,[status(thm)],[c_1714]) ).
% 3.23/0.99  
% 3.23/0.99  cnf(c_2210,plain,
% 3.23/0.99      ( m1_subset_1(k3_yellow_0(sK3),sK4) != iProver_top
% 3.23/0.99      | r2_hidden(k3_yellow_0(sK3),sK4) = iProver_top
% 3.23/0.99      | v1_xboole_0(sK4) = iProver_top ),
% 3.23/0.99      inference(predicate_to_equality,[status(thm)],[c_2209]) ).
% 3.23/0.99  
% 3.23/0.99  cnf(c_758,plain,( X0 != X1 | X2 != X1 | X2 = X0 ),theory(equality) ).
% 3.23/0.99  
% 3.23/0.99  cnf(c_1484,plain,
% 3.23/0.99      ( u1_struct_0(sK3) != X0 | sK4 != X0 | sK4 = u1_struct_0(sK3) ),
% 3.23/0.99      inference(instantiation,[status(thm)],[c_758]) ).
% 3.23/0.99  
% 3.23/0.99  cnf(c_2462,plain,
% 3.23/0.99      ( u1_struct_0(sK3) != sK4 | sK4 = u1_struct_0(sK3) | sK4 != sK4 ),
% 3.23/0.99      inference(instantiation,[status(thm)],[c_1484]) ).
% 3.23/0.99  
% 3.23/0.99  cnf(c_2973,plain,
% 3.23/0.99      ( r2_hidden(k3_yellow_0(sK3),sK4) = iProver_top ),
% 3.23/0.99      inference(global_propositional_subsumption,
% 3.23/0.99                [status(thm)],
% 3.23/0.99                [c_1153,c_30,c_31,c_33,c_63,c_396,c_774,c_780,c_1508,
% 3.23/0.99                 c_1924,c_2210,c_2462]) ).
% 3.23/0.99  
% 3.23/0.99  cnf(c_4601,plain,
% 3.23/0.99      ( r2_hidden(k3_yellow_0(sK3),sK4) ),
% 3.23/0.99      inference(global_propositional_subsumption,
% 3.23/0.99                [status(thm)],
% 3.23/0.99                [c_4221,c_30,c_31,c_33,c_63,c_396,c_397,c_774,c_780,
% 3.23/0.99                 c_1185,c_1508,c_1924,c_2210,c_2462]) ).
% 3.23/0.99  
% 3.23/0.99  cnf(c_15,plain,
% 3.23/0.99      ( ~ r1_orders_2(X0,X1,X2)
% 3.23/0.99      | ~ v13_waybel_0(X3,X0)
% 3.23/0.99      | ~ m1_subset_1(X2,u1_struct_0(X0))
% 3.23/0.99      | ~ m1_subset_1(X1,u1_struct_0(X0))
% 3.23/0.99      | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))
% 3.23/0.99      | ~ r2_hidden(X1,X3)
% 3.23/0.99      | r2_hidden(X2,X3)
% 3.23/0.99      | ~ l1_orders_2(X0) ),
% 3.23/0.99      inference(cnf_transformation,[],[f56]) ).
% 3.23/0.99  
% 3.23/0.99  cnf(c_9,plain,
% 3.23/0.99      ( r1_orders_2(X0,k3_yellow_0(X0),X1)
% 3.23/0.99      | ~ m1_subset_1(X1,u1_struct_0(X0))
% 3.23/0.99      | v2_struct_0(X0)
% 3.23/0.99      | ~ v5_orders_2(X0)
% 3.23/0.99      | ~ v1_yellow_0(X0)
% 3.23/0.99      | ~ l1_orders_2(X0) ),
% 3.23/0.99      inference(cnf_transformation,[],[f55]) ).
% 3.23/0.99  
% 3.23/0.99  cnf(c_24,negated_conjecture,
% 3.23/0.99      ( v1_yellow_0(sK3) ),
% 3.23/0.99      inference(cnf_transformation,[],[f66]) ).
% 3.23/0.99  
% 3.23/0.99  cnf(c_348,plain,
% 3.23/0.99      ( r1_orders_2(X0,k3_yellow_0(X0),X1)
% 3.23/0.99      | ~ m1_subset_1(X1,u1_struct_0(X0))
% 3.23/0.99      | v2_struct_0(X0)
% 3.23/0.99      | ~ v5_orders_2(X0)
% 3.23/0.99      | ~ l1_orders_2(X0)
% 3.23/0.99      | sK3 != X0 ),
% 3.23/0.99      inference(resolution_lifted,[status(thm)],[c_9,c_24]) ).
% 3.23/0.99  
% 3.23/0.99  cnf(c_349,plain,
% 3.23/0.99      ( r1_orders_2(sK3,k3_yellow_0(sK3),X0)
% 3.23/0.99      | ~ m1_subset_1(X0,u1_struct_0(sK3))
% 3.23/0.99      | v2_struct_0(sK3)
% 3.23/0.99      | ~ v5_orders_2(sK3)
% 3.23/0.99      | ~ l1_orders_2(sK3) ),
% 3.23/0.99      inference(unflattening,[status(thm)],[c_348]) ).
% 3.23/0.99  
% 3.23/0.99  cnf(c_26,negated_conjecture,
% 3.23/0.99      ( ~ v2_struct_0(sK3) ),
% 3.23/0.99      inference(cnf_transformation,[],[f64]) ).
% 3.23/0.99  
% 3.23/0.99  cnf(c_25,negated_conjecture,
% 3.23/0.99      ( v5_orders_2(sK3) ),
% 3.23/0.99      inference(cnf_transformation,[],[f65]) ).
% 3.23/0.99  
% 3.23/0.99  cnf(c_353,plain,
% 3.23/0.99      ( ~ m1_subset_1(X0,u1_struct_0(sK3))
% 3.23/0.99      | r1_orders_2(sK3,k3_yellow_0(sK3),X0) ),
% 3.23/0.99      inference(global_propositional_subsumption,
% 3.23/0.99                [status(thm)],
% 3.23/0.99                [c_349,c_26,c_25,c_23]) ).
% 3.23/0.99  
% 3.23/0.99  cnf(c_354,plain,
% 3.23/0.99      ( r1_orders_2(sK3,k3_yellow_0(sK3),X0)
% 3.23/0.99      | ~ m1_subset_1(X0,u1_struct_0(sK3)) ),
% 3.23/0.99      inference(renaming,[status(thm)],[c_353]) ).
% 3.23/0.99  
% 3.23/0.99  cnf(c_464,plain,
% 3.23/0.99      ( ~ v13_waybel_0(X0,X1)
% 3.23/0.99      | ~ m1_subset_1(X2,u1_struct_0(X1))
% 3.23/0.99      | ~ m1_subset_1(X3,u1_struct_0(X1))
% 3.23/0.99      | ~ m1_subset_1(X4,u1_struct_0(sK3))
% 3.23/0.99      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 3.23/0.99      | ~ r2_hidden(X2,X0)
% 3.23/0.99      | r2_hidden(X3,X0)
% 3.23/0.99      | ~ l1_orders_2(X1)
% 3.23/0.99      | X4 != X3
% 3.23/0.99      | k3_yellow_0(sK3) != X2
% 3.23/0.99      | sK3 != X1 ),
% 3.23/0.99      inference(resolution_lifted,[status(thm)],[c_15,c_354]) ).
% 3.23/0.99  
% 3.23/0.99  cnf(c_465,plain,
% 3.23/0.99      ( ~ v13_waybel_0(X0,sK3)
% 3.23/0.99      | ~ m1_subset_1(X1,u1_struct_0(sK3))
% 3.23/0.99      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK3)))
% 3.23/0.99      | ~ m1_subset_1(k3_yellow_0(sK3),u1_struct_0(sK3))
% 3.23/0.99      | r2_hidden(X1,X0)
% 3.23/0.99      | ~ r2_hidden(k3_yellow_0(sK3),X0)
% 3.23/0.99      | ~ l1_orders_2(sK3) ),
% 3.23/0.99      inference(unflattening,[status(thm)],[c_464]) ).
% 3.23/0.99  
% 3.23/0.99  cnf(c_62,plain,
% 3.23/0.99      ( m1_subset_1(k3_yellow_0(sK3),u1_struct_0(sK3))
% 3.23/0.99      | ~ l1_orders_2(sK3) ),
% 3.23/0.99      inference(instantiation,[status(thm)],[c_8]) ).
% 3.23/0.99  
% 3.23/0.99  cnf(c_469,plain,
% 3.23/0.99      ( ~ r2_hidden(k3_yellow_0(sK3),X0)
% 3.23/0.99      | r2_hidden(X1,X0)
% 3.23/0.99      | ~ v13_waybel_0(X0,sK3)
% 3.23/0.99      | ~ m1_subset_1(X1,u1_struct_0(sK3))
% 3.23/0.99      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK3))) ),
% 3.23/0.99      inference(global_propositional_subsumption,
% 3.23/0.99                [status(thm)],
% 3.23/0.99                [c_465,c_23,c_62]) ).
% 3.23/0.99  
% 3.23/0.99  cnf(c_470,plain,
% 3.23/0.99      ( ~ v13_waybel_0(X0,sK3)
% 3.23/0.99      | ~ m1_subset_1(X1,u1_struct_0(sK3))
% 3.23/0.99      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK3)))
% 3.23/0.99      | r2_hidden(X1,X0)
% 3.23/0.99      | ~ r2_hidden(k3_yellow_0(sK3),X0) ),
% 3.23/0.99      inference(renaming,[status(thm)],[c_469]) ).
% 3.23/0.99  
% 3.23/0.99  cnf(c_2010,plain,
% 3.23/0.99      ( ~ v13_waybel_0(sK4,sK3)
% 3.23/0.99      | ~ m1_subset_1(X0,u1_struct_0(sK3))
% 3.23/0.99      | r2_hidden(X0,sK4)
% 3.23/0.99      | ~ r2_hidden(k3_yellow_0(sK3),sK4) ),
% 3.23/0.99      inference(resolution,[status(thm)],[c_470,c_20]) ).
% 3.23/0.99  
% 3.23/0.99  cnf(c_21,negated_conjecture,
% 3.23/0.99      ( v13_waybel_0(sK4,sK3) ),
% 3.23/0.99      inference(cnf_transformation,[],[f69]) ).
% 3.23/0.99  
% 3.23/0.99  cnf(c_1158,plain,
% 3.23/0.99      ( m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(sK3))) = iProver_top ),
% 3.23/0.99      inference(predicate_to_equality,[status(thm)],[c_20]) ).
% 3.23/0.99  
% 3.23/0.99  cnf(c_1151,plain,
% 3.23/0.99      ( v13_waybel_0(X0,sK3) != iProver_top
% 3.23/0.99      | m1_subset_1(X1,u1_struct_0(sK3)) != iProver_top
% 3.23/0.99      | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK3))) != iProver_top
% 3.23/0.99      | r2_hidden(X1,X0) = iProver_top
% 3.23/0.99      | r2_hidden(k3_yellow_0(sK3),X0) != iProver_top ),
% 3.23/0.99      inference(predicate_to_equality,[status(thm)],[c_470]) ).
% 3.23/0.99  
% 3.23/0.99  cnf(c_1981,plain,
% 3.23/0.99      ( v13_waybel_0(sK4,sK3) != iProver_top
% 3.23/0.99      | m1_subset_1(X0,u1_struct_0(sK3)) != iProver_top
% 3.23/0.99      | r2_hidden(X0,sK4) = iProver_top
% 3.23/0.99      | r2_hidden(k3_yellow_0(sK3),sK4) != iProver_top ),
% 3.23/0.99      inference(superposition,[status(thm)],[c_1158,c_1151]) ).
% 3.23/0.99  
% 3.23/0.99  cnf(c_1982,plain,
% 3.23/0.99      ( ~ v13_waybel_0(sK4,sK3)
% 3.23/0.99      | ~ m1_subset_1(X0,u1_struct_0(sK3))
% 3.23/0.99      | r2_hidden(X0,sK4)
% 3.23/0.99      | ~ r2_hidden(k3_yellow_0(sK3),sK4) ),
% 3.23/0.99      inference(predicate_to_equality_rev,[status(thm)],[c_1981]) ).
% 3.23/0.99  
% 3.23/0.99  cnf(c_2013,plain,
% 3.23/0.99      ( ~ m1_subset_1(X0,u1_struct_0(sK3))
% 3.23/0.99      | r2_hidden(X0,sK4)
% 3.23/0.99      | ~ r2_hidden(k3_yellow_0(sK3),sK4) ),
% 3.23/0.99      inference(global_propositional_subsumption,
% 3.23/0.99                [status(thm)],
% 3.23/0.99                [c_2010,c_21,c_1982]) ).
% 3.23/0.99  
% 3.23/0.99  cnf(c_4861,plain,
% 3.23/0.99      ( ~ m1_subset_1(X0,u1_struct_0(sK3)) | r2_hidden(X0,sK4) ),
% 3.23/0.99      inference(backward_subsumption_resolution,
% 3.23/0.99                [status(thm)],
% 3.23/0.99                [c_4601,c_2013]) ).
% 3.23/0.99  
% 3.23/0.99  cnf(c_5,plain,
% 3.23/0.99      ( m1_subset_1(X0,X1) | ~ r2_hidden(X0,X1) ),
% 3.23/0.99      inference(cnf_transformation,[],[f51]) ).
% 3.23/0.99  
% 3.23/0.99  cnf(c_5457,plain,
% 3.23/0.99      ( ~ r2_hidden(X0,u1_struct_0(sK3)) | r2_hidden(X0,sK4) ),
% 3.23/0.99      inference(resolution,[status(thm)],[c_4861,c_5]) ).
% 3.23/0.99  
% 3.23/0.99  cnf(c_0,plain,
% 3.23/0.99      ( ~ r2_hidden(sK0(X0,X1),X1)
% 3.23/0.99      | ~ r2_hidden(sK0(X0,X1),X0)
% 3.23/0.99      | X1 = X0 ),
% 3.23/0.99      inference(cnf_transformation,[],[f47]) ).
% 3.23/0.99  
% 3.23/0.99  cnf(c_7,plain,
% 3.23/0.99      ( m1_subset_1(X0,X1)
% 3.23/0.99      | ~ m1_subset_1(X2,k1_zfmisc_1(X1))
% 3.23/0.99      | ~ r2_hidden(X0,X2) ),
% 3.23/0.99      inference(cnf_transformation,[],[f53]) ).
% 3.23/0.99  
% 3.23/0.99  cnf(c_2572,plain,
% 3.23/0.99      ( m1_subset_1(X0,u1_struct_0(sK3)) | ~ r2_hidden(X0,sK4) ),
% 3.23/0.99      inference(resolution,[status(thm)],[c_7,c_20]) ).
% 3.23/0.99  
% 3.23/0.99  cnf(c_2665,plain,
% 3.23/0.99      ( r2_hidden(X0,u1_struct_0(sK3))
% 3.23/0.99      | ~ r2_hidden(X0,sK4)
% 3.23/0.99      | v1_xboole_0(u1_struct_0(sK3)) ),
% 3.23/0.99      inference(resolution,[status(thm)],[c_2572,c_6]) ).
% 3.23/0.99  
% 3.23/0.99  cnf(c_3,plain,
% 3.23/0.99      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
% 3.23/0.99      | ~ v1_xboole_0(X1)
% 3.23/0.99      | v1_xboole_0(X0) ),
% 3.23/0.99      inference(cnf_transformation,[],[f49]) ).
% 3.23/0.99  
% 3.23/0.99  cnf(c_1162,plain,
% 3.23/0.99      ( m1_subset_1(X0,k1_zfmisc_1(X1)) != iProver_top
% 3.23/0.99      | v1_xboole_0(X1) != iProver_top
% 3.23/0.99      | v1_xboole_0(X0) = iProver_top ),
% 3.23/0.99      inference(predicate_to_equality,[status(thm)],[c_3]) ).
% 3.23/0.99  
% 3.23/0.99  cnf(c_2441,plain,
% 3.23/0.99      ( v1_xboole_0(u1_struct_0(sK3)) != iProver_top
% 3.23/0.99      | v1_xboole_0(sK4) = iProver_top ),
% 3.23/0.99      inference(superposition,[status(thm)],[c_1158,c_1162]) ).
% 3.23/0.99  
% 3.23/0.99  cnf(c_2442,plain,
% 3.23/0.99      ( ~ v1_xboole_0(u1_struct_0(sK3)) | v1_xboole_0(sK4) ),
% 3.23/0.99      inference(predicate_to_equality_rev,[status(thm)],[c_2441]) ).
% 3.23/0.99  
% 3.23/0.99  cnf(c_2670,plain,
% 3.23/0.99      ( ~ r2_hidden(X0,sK4) | r2_hidden(X0,u1_struct_0(sK3)) ),
% 3.23/0.99      inference(global_propositional_subsumption,
% 3.23/0.99                [status(thm)],
% 3.23/0.99                [c_2665,c_22,c_2442]) ).
% 3.23/0.99  
% 3.23/0.99  cnf(c_2671,plain,
% 3.23/0.99      ( r2_hidden(X0,u1_struct_0(sK3)) | ~ r2_hidden(X0,sK4) ),
% 3.23/0.99      inference(renaming,[status(thm)],[c_2670]) ).
% 3.23/0.99  
% 3.23/0.99  cnf(c_3568,plain,
% 3.23/0.99      ( ~ r2_hidden(sK0(u1_struct_0(sK3),X0),X0)
% 3.23/0.99      | ~ r2_hidden(sK0(u1_struct_0(sK3),X0),sK4)
% 3.23/0.99      | X0 = u1_struct_0(sK3) ),
% 3.23/0.99      inference(resolution,[status(thm)],[c_0,c_2671]) ).
% 3.23/0.99  
% 3.23/0.99  cnf(c_1,plain,
% 3.23/0.99      ( r2_hidden(sK0(X0,X1),X1) | r2_hidden(sK0(X0,X1),X0) | X1 = X0 ),
% 3.23/0.99      inference(cnf_transformation,[],[f46]) ).
% 3.23/0.99  
% 3.23/0.99  cnf(c_3951,plain,
% 3.23/0.99      ( r2_hidden(sK0(u1_struct_0(sK3),sK4),u1_struct_0(sK3))
% 3.23/0.99      | ~ r2_hidden(sK0(u1_struct_0(sK3),sK4),sK4)
% 3.23/0.99      | sK4 = u1_struct_0(sK3) ),
% 3.23/0.99      inference(resolution,[status(thm)],[c_3568,c_1]) ).
% 3.23/0.99  
% 3.23/0.99  cnf(c_1411,plain,
% 3.23/0.99      ( r2_hidden(sK0(u1_struct_0(sK3),sK4),u1_struct_0(sK3))
% 3.23/0.99      | r2_hidden(sK0(u1_struct_0(sK3),sK4),sK4)
% 3.23/0.99      | sK4 = u1_struct_0(sK3) ),
% 3.23/0.99      inference(instantiation,[status(thm)],[c_1]) ).
% 3.23/0.99  
% 3.23/0.99  cnf(c_3954,plain,
% 3.23/0.99      ( r2_hidden(sK0(u1_struct_0(sK3),sK4),u1_struct_0(sK3))
% 3.23/0.99      | sK4 = u1_struct_0(sK3) ),
% 3.23/0.99      inference(global_propositional_subsumption,
% 3.23/0.99                [status(thm)],
% 3.23/0.99                [c_3951,c_1411]) ).
% 3.23/0.99  
% 3.23/0.99  cnf(c_5688,plain,
% 3.23/0.99      ( r2_hidden(sK0(u1_struct_0(sK3),sK4),sK4)
% 3.23/0.99      | sK4 = u1_struct_0(sK3) ),
% 3.23/0.99      inference(resolution,[status(thm)],[c_5457,c_3954]) ).
% 3.23/0.99  
% 3.23/0.99  cnf(c_3541,plain,
% 3.23/0.99      ( X0 != X1 | k2_subset_1(X1) = X0 ),
% 3.23/0.99      inference(resolution,[status(thm)],[c_758,c_2]) ).
% 3.23/0.99  
% 3.23/0.99  cnf(c_384,plain,
% 3.23/0.99      ( k2_subset_1(u1_struct_0(sK3)) != sK4
% 3.23/0.99      | r2_hidden(k3_yellow_0(sK3),sK4) != iProver_top ),
% 3.23/0.99      inference(predicate_to_equality,[status(thm)],[c_383]) ).
% 3.23/0.99  
% 3.23/0.99  cnf(c_3015,plain,
% 3.23/0.99      ( k2_subset_1(u1_struct_0(sK3)) != sK4 ),
% 3.23/0.99      inference(global_propositional_subsumption,
% 3.23/0.99                [status(thm)],
% 3.23/0.99                [c_383,c_30,c_31,c_33,c_63,c_384,c_396,c_774,c_780,
% 3.23/0.99                 c_1508,c_1924,c_2210,c_2462]) ).
% 3.23/0.99  
% 3.23/0.99  cnf(c_5101,plain,
% 3.23/0.99      ( sK4 != u1_struct_0(sK3) ),
% 3.23/0.99      inference(resolution,[status(thm)],[c_3541,c_3015]) ).
% 3.23/0.99  
% 3.23/0.99  cnf(c_4010,plain,
% 3.23/0.99      ( ~ r2_hidden(sK0(u1_struct_0(sK3),sK4),sK4)
% 3.23/0.99      | sK4 = u1_struct_0(sK3) ),
% 3.23/0.99      inference(resolution,[status(thm)],[c_3954,c_0]) ).
% 3.23/0.99  
% 3.23/0.99  cnf(contradiction,plain,
% 3.23/0.99      ( $false ),
% 3.23/0.99      inference(minisat,[status(thm)],[c_5688,c_5101,c_4010]) ).
% 3.23/0.99  
% 3.23/0.99  
% 3.23/0.99  % SZS output end CNFRefutation for theBenchmark.p
% 3.23/0.99  
% 3.23/0.99  ------                               Statistics
% 3.23/0.99  
% 3.23/0.99  ------ Selected
% 3.23/0.99  
% 3.23/0.99  total_time:                             0.189
% 3.23/0.99  
%------------------------------------------------------------------------------
