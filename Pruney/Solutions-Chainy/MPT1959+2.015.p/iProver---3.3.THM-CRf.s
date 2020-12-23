%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n013.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:28:26 EST 2020

% Result     : Theorem 2.97s
% Output     : CNFRefutation 2.97s
% Verified   : 
% Statistics : Number of formulae       :  180 ( 721 expanded)
%              Number of clauses        :  110 ( 205 expanded)
%              Number of leaves         :   19 ( 136 expanded)
%              Depth                    :   23
%              Number of atoms          :  751 (5247 expanded)
%              Number of equality atoms :  102 ( 179 expanded)
%              Maximal formula depth    :   14 (   5 average)
%              Maximal clause size      :   22 (   3 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f2,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => ! [X2] :
          ( r2_hidden(X2,X1)
         => r2_hidden(X2,X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f16,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( r2_hidden(X2,X0)
          | ~ r2_hidden(X2,X1) )
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f52,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(X2,X0)
      | ~ r2_hidden(X2,X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f16])).

fof(f5,axiom,(
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
    inference(nnf_transformation,[],[f5])).

fof(f58,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f37])).

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
    inference(nnf_transformation,[],[f27])).

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

fof(f61,plain,(
    ! [X0,X1] :
      ( r1_orders_2(X0,k3_yellow_0(X0),X1)
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | ~ v1_yellow_0(X0)
      | ~ v5_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f25])).

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
    inference(nnf_transformation,[],[f30])).

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

fof(f72,plain,(
    v1_yellow_0(sK3) ),
    inference(cnf_transformation,[],[f48])).

fof(f70,plain,(
    ~ v2_struct_0(sK3) ),
    inference(cnf_transformation,[],[f48])).

fof(f71,plain,(
    v5_orders_2(sK3) ),
    inference(cnf_transformation,[],[f48])).

fof(f73,plain,(
    l1_orders_2(sK3) ),
    inference(cnf_transformation,[],[f48])).

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

fof(f60,plain,(
    ! [X0] :
      ( m1_subset_1(k3_yellow_0(X0),u1_struct_0(X0))
      | ~ l1_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f23])).

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

fof(f43,plain,(
    ! [X0,X1] :
      ( ( ( v1_subset_1(X1,X0)
          | X0 = X1 )
        & ( X0 != X1
          | ~ v1_subset_1(X1,X0) ) )
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(nnf_transformation,[],[f28])).

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

fof(f76,plain,(
    m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(sK3))) ),
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

fof(f1,axiom,(
    ! [X0,X1] :
      ( X0 = X1
    <=> ( r1_tarski(X1,X0)
        & r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f31,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(nnf_transformation,[],[f1])).

fof(f32,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(flattening,[],[f31])).

fof(f49,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | X0 != X1 ) ),
    inference(cnf_transformation,[],[f32])).

fof(f80,plain,(
    ! [X1] : r1_tarski(X1,X1) ),
    inference(equality_resolution,[],[f49])).

fof(f57,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ) ),
    inference(cnf_transformation,[],[f37])).

fof(f4,axiom,(
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
    inference(ennf_transformation,[],[f4])).

fof(f20,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
      | v1_xboole_0(X1)
      | ~ m1_subset_1(X0,X1) ) ),
    inference(flattening,[],[f19])).

fof(f56,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
      | v1_xboole_0(X1)
      | ~ m1_subset_1(X0,X1) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f74,plain,(
    ~ v1_xboole_0(sK4) ),
    inference(cnf_transformation,[],[f48])).

fof(f3,axiom,(
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

fof(f17,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( X1 = X2
          | ? [X3] :
              ( ( r2_hidden(X3,X1)
              <~> r2_hidden(X3,X2) )
              & m1_subset_1(X3,X0) )
          | ~ m1_subset_1(X2,k1_zfmisc_1(X0)) )
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f18,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( X1 = X2
          | ? [X3] :
              ( ( r2_hidden(X3,X1)
              <~> r2_hidden(X3,X2) )
              & m1_subset_1(X3,X0) )
          | ~ m1_subset_1(X2,k1_zfmisc_1(X0)) )
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(flattening,[],[f17])).

fof(f33,plain,(
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
    inference(nnf_transformation,[],[f18])).

fof(f34,plain,(
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
    inference(flattening,[],[f33])).

fof(f35,plain,(
    ! [X2,X1,X0] :
      ( ? [X3] :
          ( ( ~ r2_hidden(X3,X2)
            | ~ r2_hidden(X3,X1) )
          & ( r2_hidden(X3,X2)
            | r2_hidden(X3,X1) )
          & m1_subset_1(X3,X0) )
     => ( ( ~ r2_hidden(sK0(X0,X1,X2),X2)
          | ~ r2_hidden(sK0(X0,X1,X2),X1) )
        & ( r2_hidden(sK0(X0,X1,X2),X2)
          | r2_hidden(sK0(X0,X1,X2),X1) )
        & m1_subset_1(sK0(X0,X1,X2),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f36,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( X1 = X2
          | ( ( ~ r2_hidden(sK0(X0,X1,X2),X2)
              | ~ r2_hidden(sK0(X0,X1,X2),X1) )
            & ( r2_hidden(sK0(X0,X1,X2),X2)
              | r2_hidden(sK0(X0,X1,X2),X1) )
            & m1_subset_1(sK0(X0,X1,X2),X0) )
          | ~ m1_subset_1(X2,k1_zfmisc_1(X0)) )
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f34,f35])).

fof(f55,plain,(
    ! [X2,X0,X1] :
      ( X1 = X2
      | ~ r2_hidden(sK0(X0,X1,X2),X2)
      | ~ r2_hidden(sK0(X0,X1,X2),X1)
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f36])).

fof(f53,plain,(
    ! [X2,X0,X1] :
      ( X1 = X2
      | m1_subset_1(sK0(X0,X1,X2),X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f36])).

fof(f67,plain,(
    ! [X0,X1] :
      ( v13_waybel_0(X1,X0)
      | ~ r2_hidden(sK2(X0,X1),X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f42])).

fof(f64,plain,(
    ! [X0,X1] :
      ( v13_waybel_0(X1,X0)
      | m1_subset_1(sK2(X0,X1),u1_struct_0(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f42])).

fof(f77,plain,
    ( ~ r2_hidden(k3_yellow_0(sK3),sK4)
    | v1_subset_1(sK4,u1_struct_0(sK3)) ),
    inference(cnf_transformation,[],[f48])).

fof(f75,plain,(
    v13_waybel_0(sK4,sK3) ),
    inference(cnf_transformation,[],[f48])).

cnf(c_3,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | ~ r2_hidden(X2,X0)
    | r2_hidden(X2,X1) ),
    inference(cnf_transformation,[],[f52])).

cnf(c_8,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(X1))
    | ~ r1_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f58])).

cnf(c_223,plain,
    ( ~ r1_tarski(X0,X1)
    | m1_subset_1(X0,k1_zfmisc_1(X1)) ),
    inference(prop_impl,[status(thm)],[c_8])).

cnf(c_224,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(X1))
    | ~ r1_tarski(X0,X1) ),
    inference(renaming,[status(thm)],[c_223])).

cnf(c_287,plain,
    ( ~ r2_hidden(X0,X1)
    | r2_hidden(X0,X2)
    | ~ r1_tarski(X1,X2) ),
    inference(bin_hyper_res,[status(thm)],[c_3,c_224])).

cnf(c_1618,plain,
    ( r2_hidden(sK2(sK3,X0),X1)
    | ~ r2_hidden(sK2(sK3,X0),sK4)
    | ~ r1_tarski(sK4,X1) ),
    inference(instantiation,[status(thm)],[c_287])).

cnf(c_1774,plain,
    ( r2_hidden(sK2(sK3,X0),u1_struct_0(sK3))
    | ~ r2_hidden(sK2(sK3,X0),sK4)
    | ~ r1_tarski(sK4,u1_struct_0(sK3)) ),
    inference(instantiation,[status(thm)],[c_1618])).

cnf(c_14037,plain,
    ( r2_hidden(sK2(sK3,u1_struct_0(X0)),u1_struct_0(sK3))
    | ~ r2_hidden(sK2(sK3,u1_struct_0(X0)),sK4)
    | ~ r1_tarski(sK4,u1_struct_0(sK3)) ),
    inference(instantiation,[status(thm)],[c_1774])).

cnf(c_14044,plain,
    ( r2_hidden(sK2(sK3,u1_struct_0(sK3)),u1_struct_0(sK3))
    | ~ r2_hidden(sK2(sK3,u1_struct_0(sK3)),sK4)
    | ~ r1_tarski(sK4,u1_struct_0(sK3)) ),
    inference(instantiation,[status(thm)],[c_14037])).

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

cnf(c_414,plain,
    ( r1_orders_2(X0,k3_yellow_0(X0),X1)
    | ~ m1_subset_1(X1,u1_struct_0(X0))
    | v2_struct_0(X0)
    | ~ v5_orders_2(X0)
    | ~ l1_orders_2(X0)
    | sK3 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_12,c_27])).

cnf(c_415,plain,
    ( r1_orders_2(sK3,k3_yellow_0(sK3),X0)
    | ~ m1_subset_1(X0,u1_struct_0(sK3))
    | v2_struct_0(sK3)
    | ~ v5_orders_2(sK3)
    | ~ l1_orders_2(sK3) ),
    inference(unflattening,[status(thm)],[c_414])).

cnf(c_29,negated_conjecture,
    ( ~ v2_struct_0(sK3) ),
    inference(cnf_transformation,[],[f70])).

cnf(c_28,negated_conjecture,
    ( v5_orders_2(sK3) ),
    inference(cnf_transformation,[],[f71])).

cnf(c_26,negated_conjecture,
    ( l1_orders_2(sK3) ),
    inference(cnf_transformation,[],[f73])).

cnf(c_419,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(sK3))
    | r1_orders_2(sK3,k3_yellow_0(sK3),X0) ),
    inference(global_propositional_subsumption,[status(thm)],[c_415,c_29,c_28,c_26])).

cnf(c_420,plain,
    ( r1_orders_2(sK3,k3_yellow_0(sK3),X0)
    | ~ m1_subset_1(X0,u1_struct_0(sK3)) ),
    inference(renaming,[status(thm)],[c_419])).

cnf(c_502,plain,
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
    inference(resolution_lifted,[status(thm)],[c_18,c_420])).

cnf(c_503,plain,
    ( ~ v13_waybel_0(X0,sK3)
    | ~ m1_subset_1(X1,u1_struct_0(sK3))
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK3)))
    | ~ m1_subset_1(k3_yellow_0(sK3),u1_struct_0(sK3))
    | r2_hidden(X1,X0)
    | ~ r2_hidden(k3_yellow_0(sK3),X0)
    | ~ l1_orders_2(sK3) ),
    inference(unflattening,[status(thm)],[c_502])).

cnf(c_11,plain,
    ( m1_subset_1(k3_yellow_0(X0),u1_struct_0(X0))
    | ~ l1_orders_2(X0) ),
    inference(cnf_transformation,[],[f60])).

cnf(c_65,plain,
    ( m1_subset_1(k3_yellow_0(sK3),u1_struct_0(sK3))
    | ~ l1_orders_2(sK3) ),
    inference(instantiation,[status(thm)],[c_11])).

cnf(c_507,plain,
    ( ~ r2_hidden(k3_yellow_0(sK3),X0)
    | r2_hidden(X1,X0)
    | ~ v13_waybel_0(X0,sK3)
    | ~ m1_subset_1(X1,u1_struct_0(sK3))
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK3))) ),
    inference(global_propositional_subsumption,[status(thm)],[c_503,c_26,c_65])).

cnf(c_508,plain,
    ( ~ v13_waybel_0(X0,sK3)
    | ~ m1_subset_1(X1,u1_struct_0(sK3))
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK3)))
    | r2_hidden(X1,X0)
    | ~ r2_hidden(k3_yellow_0(sK3),X0) ),
    inference(renaming,[status(thm)],[c_507])).

cnf(c_1564,plain,
    ( ~ v13_waybel_0(sK4,sK3)
    | ~ m1_subset_1(X0,u1_struct_0(sK3))
    | ~ m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(sK3)))
    | r2_hidden(X0,sK4)
    | ~ r2_hidden(k3_yellow_0(sK3),sK4) ),
    inference(instantiation,[status(thm)],[c_508])).

cnf(c_8975,plain,
    ( ~ v13_waybel_0(sK4,sK3)
    | ~ m1_subset_1(sK2(sK3,u1_struct_0(X0)),u1_struct_0(sK3))
    | ~ m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(sK3)))
    | r2_hidden(sK2(sK3,u1_struct_0(X0)),sK4)
    | ~ r2_hidden(k3_yellow_0(sK3),sK4) ),
    inference(instantiation,[status(thm)],[c_1564])).

cnf(c_8977,plain,
    ( ~ v13_waybel_0(sK4,sK3)
    | ~ m1_subset_1(sK2(sK3,u1_struct_0(sK3)),u1_struct_0(sK3))
    | ~ m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(sK3)))
    | r2_hidden(sK2(sK3,u1_struct_0(sK3)),sK4)
    | ~ r2_hidden(k3_yellow_0(sK3),sK4) ),
    inference(instantiation,[status(thm)],[c_8975])).

cnf(c_19,plain,
    ( v1_subset_1(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | X0 = X1 ),
    inference(cnf_transformation,[],[f69])).

cnf(c_293,plain,
    ( v1_subset_1(X0,X1)
    | ~ r1_tarski(X0,X1)
    | X0 = X1 ),
    inference(bin_hyper_res,[status(thm)],[c_19,c_224])).

cnf(c_21,negated_conjecture,
    ( ~ v1_subset_1(sK4,u1_struct_0(sK3))
    | r2_hidden(k3_yellow_0(sK3),sK4) ),
    inference(cnf_transformation,[],[f78])).

cnf(c_227,plain,
    ( ~ v1_subset_1(sK4,u1_struct_0(sK3))
    | r2_hidden(k3_yellow_0(sK3),sK4) ),
    inference(prop_impl,[status(thm)],[c_21])).

cnf(c_438,plain,
    ( r2_hidden(k3_yellow_0(sK3),sK4)
    | ~ r1_tarski(X0,X1)
    | X1 = X0
    | u1_struct_0(sK3) != X1
    | sK4 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_293,c_227])).

cnf(c_439,plain,
    ( r2_hidden(k3_yellow_0(sK3),sK4)
    | ~ r1_tarski(sK4,u1_struct_0(sK3))
    | u1_struct_0(sK3) = sK4 ),
    inference(unflattening,[status(thm)],[c_438])).

cnf(c_1375,plain,
    ( u1_struct_0(sK3) = sK4
    | r2_hidden(k3_yellow_0(sK3),sK4) = iProver_top
    | r1_tarski(sK4,u1_struct_0(sK3)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_439])).

cnf(c_33,plain,
    ( l1_orders_2(sK3) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_26])).

cnf(c_23,negated_conjecture,
    ( m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(sK3))) ),
    inference(cnf_transformation,[],[f76])).

cnf(c_36,plain,
    ( m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(sK3))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_23])).

cnf(c_20,plain,
    ( ~ v1_subset_1(X0,X0)
    | ~ m1_subset_1(X0,k1_zfmisc_1(X0)) ),
    inference(cnf_transformation,[],[f81])).

cnf(c_40,plain,
    ( ~ v1_subset_1(sK3,sK3)
    | ~ m1_subset_1(sK3,k1_zfmisc_1(sK3)) ),
    inference(instantiation,[status(thm)],[c_20])).

cnf(c_43,plain,
    ( v1_subset_1(sK3,sK3)
    | ~ m1_subset_1(sK3,k1_zfmisc_1(sK3))
    | sK3 = sK3 ),
    inference(instantiation,[status(thm)],[c_19])).

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

cnf(c_2,plain,
    ( r1_tarski(X0,X0) ),
    inference(cnf_transformation,[],[f80])).

cnf(c_90,plain,
    ( r1_tarski(sK3,sK3) ),
    inference(instantiation,[status(thm)],[c_2])).

cnf(c_440,plain,
    ( u1_struct_0(sK3) = sK4
    | r2_hidden(k3_yellow_0(sK3),sK4) = iProver_top
    | r1_tarski(sK4,u1_struct_0(sK3)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_439])).

cnf(c_859,plain,
    ( X0 != X1
    | k3_yellow_0(X0) = k3_yellow_0(X1) ),
    theory(equality)).

cnf(c_868,plain,
    ( k3_yellow_0(sK3) = k3_yellow_0(sK3)
    | sK3 != sK3 ),
    inference(instantiation,[status(thm)],[c_859])).

cnf(c_9,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | r1_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f57])).

cnf(c_1578,plain,
    ( ~ m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(sK3)))
    | r1_tarski(sK4,u1_struct_0(sK3)) ),
    inference(instantiation,[status(thm)],[c_9])).

cnf(c_1579,plain,
    ( m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(sK3))) != iProver_top
    | r1_tarski(sK4,u1_struct_0(sK3)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1578])).

cnf(c_853,plain,
    ( X0 = X0 ),
    theory(equality)).

cnf(c_1655,plain,
    ( sK4 = sK4 ),
    inference(instantiation,[status(thm)],[c_853])).

cnf(c_854,plain,
    ( X0 != X1
    | X2 != X1
    | X2 = X0 ),
    theory(equality)).

cnf(c_1814,plain,
    ( X0 != X1
    | sK4 != X1
    | sK4 = X0 ),
    inference(instantiation,[status(thm)],[c_854])).

cnf(c_2338,plain,
    ( X0 != sK4
    | sK4 = X0
    | sK4 != sK4 ),
    inference(instantiation,[status(thm)],[c_1814])).

cnf(c_2566,plain,
    ( u1_struct_0(sK3) != sK4
    | sK4 = u1_struct_0(sK3)
    | sK4 != sK4 ),
    inference(instantiation,[status(thm)],[c_2338])).

cnf(c_858,plain,
    ( ~ m1_subset_1(X0,X1)
    | m1_subset_1(X2,X3)
    | X2 != X0
    | X3 != X1 ),
    theory(equality)).

cnf(c_1592,plain,
    ( m1_subset_1(X0,X1)
    | ~ m1_subset_1(k3_yellow_0(sK3),u1_struct_0(sK3))
    | X1 != u1_struct_0(sK3)
    | X0 != k3_yellow_0(sK3) ),
    inference(instantiation,[status(thm)],[c_858])).

cnf(c_3175,plain,
    ( m1_subset_1(X0,sK4)
    | ~ m1_subset_1(k3_yellow_0(sK3),u1_struct_0(sK3))
    | X0 != k3_yellow_0(sK3)
    | sK4 != u1_struct_0(sK3) ),
    inference(instantiation,[status(thm)],[c_1592])).

cnf(c_3915,plain,
    ( ~ m1_subset_1(k3_yellow_0(sK3),u1_struct_0(sK3))
    | m1_subset_1(k3_yellow_0(sK3),sK4)
    | k3_yellow_0(sK3) != k3_yellow_0(sK3)
    | sK4 != u1_struct_0(sK3) ),
    inference(instantiation,[status(thm)],[c_3175])).

cnf(c_3916,plain,
    ( k3_yellow_0(sK3) != k3_yellow_0(sK3)
    | sK4 != u1_struct_0(sK3)
    | m1_subset_1(k3_yellow_0(sK3),u1_struct_0(sK3)) != iProver_top
    | m1_subset_1(k3_yellow_0(sK3),sK4) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3915])).

cnf(c_7,plain,
    ( ~ m1_subset_1(X0,X1)
    | r2_hidden(X0,X1)
    | v1_xboole_0(X1) ),
    inference(cnf_transformation,[],[f56])).

cnf(c_25,negated_conjecture,
    ( ~ v1_xboole_0(sK4) ),
    inference(cnf_transformation,[],[f74])).

cnf(c_399,plain,
    ( ~ m1_subset_1(X0,X1)
    | r2_hidden(X0,X1)
    | sK4 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_7,c_25])).

cnf(c_400,plain,
    ( ~ m1_subset_1(X0,sK4)
    | r2_hidden(X0,sK4) ),
    inference(unflattening,[status(thm)],[c_399])).

cnf(c_6078,plain,
    ( ~ m1_subset_1(k3_yellow_0(sK3),sK4)
    | r2_hidden(k3_yellow_0(sK3),sK4) ),
    inference(instantiation,[status(thm)],[c_400])).

cnf(c_6079,plain,
    ( m1_subset_1(k3_yellow_0(sK3),sK4) != iProver_top
    | r2_hidden(k3_yellow_0(sK3),sK4) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_6078])).

cnf(c_6141,plain,
    ( r2_hidden(k3_yellow_0(sK3),sK4) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_1375,c_33,c_36,c_40,c_43,c_66,c_74,c_90,c_440,c_868,c_1579,c_1655,c_2566,c_3916,c_6079])).

cnf(c_6045,plain,
    ( ~ v13_waybel_0(sK4,sK3)
    | ~ m1_subset_1(sK0(u1_struct_0(sK3),sK4,u1_struct_0(sK3)),u1_struct_0(sK3))
    | ~ m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(sK3)))
    | r2_hidden(sK0(u1_struct_0(sK3),sK4,u1_struct_0(sK3)),sK4)
    | ~ r2_hidden(k3_yellow_0(sK3),sK4) ),
    inference(instantiation,[status(thm)],[c_1564])).

cnf(c_3274,plain,
    ( ~ v13_waybel_0(u1_struct_0(X0),sK3)
    | ~ m1_subset_1(X1,u1_struct_0(sK3))
    | ~ m1_subset_1(u1_struct_0(X0),k1_zfmisc_1(u1_struct_0(sK3)))
    | r2_hidden(X1,u1_struct_0(X0))
    | ~ r2_hidden(k3_yellow_0(sK3),u1_struct_0(X0)) ),
    inference(instantiation,[status(thm)],[c_508])).

cnf(c_6040,plain,
    ( ~ v13_waybel_0(u1_struct_0(X0),sK3)
    | ~ m1_subset_1(sK0(u1_struct_0(sK3),sK4,u1_struct_0(sK3)),u1_struct_0(sK3))
    | ~ m1_subset_1(u1_struct_0(X0),k1_zfmisc_1(u1_struct_0(sK3)))
    | r2_hidden(sK0(u1_struct_0(sK3),sK4,u1_struct_0(sK3)),u1_struct_0(X0))
    | ~ r2_hidden(k3_yellow_0(sK3),u1_struct_0(X0)) ),
    inference(instantiation,[status(thm)],[c_3274])).

cnf(c_6042,plain,
    ( ~ v13_waybel_0(u1_struct_0(sK3),sK3)
    | ~ m1_subset_1(sK0(u1_struct_0(sK3),sK4,u1_struct_0(sK3)),u1_struct_0(sK3))
    | ~ m1_subset_1(u1_struct_0(sK3),k1_zfmisc_1(u1_struct_0(sK3)))
    | r2_hidden(sK0(u1_struct_0(sK3),sK4,u1_struct_0(sK3)),u1_struct_0(sK3))
    | ~ r2_hidden(k3_yellow_0(sK3),u1_struct_0(sK3)) ),
    inference(instantiation,[status(thm)],[c_6040])).

cnf(c_4,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | ~ m1_subset_1(X2,k1_zfmisc_1(X1))
    | ~ r2_hidden(sK0(X1,X0,X2),X2)
    | ~ r2_hidden(sK0(X1,X0,X2),X0)
    | X2 = X0 ),
    inference(cnf_transformation,[],[f55])).

cnf(c_288,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | ~ r2_hidden(sK0(X1,X2,X0),X0)
    | ~ r2_hidden(sK0(X1,X2,X0),X2)
    | ~ r1_tarski(X2,X1)
    | X0 = X2 ),
    inference(bin_hyper_res,[status(thm)],[c_4,c_224])).

cnf(c_725,plain,
    ( ~ r1_tarski(X0,X1)
    | m1_subset_1(X0,k1_zfmisc_1(X1)) ),
    inference(prop_impl,[status(thm)],[c_8])).

cnf(c_726,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(X1))
    | ~ r1_tarski(X0,X1) ),
    inference(renaming,[status(thm)],[c_725])).

cnf(c_774,plain,
    ( ~ r2_hidden(sK0(X0,X1,X2),X2)
    | ~ r2_hidden(sK0(X0,X1,X2),X1)
    | ~ r1_tarski(X2,X0)
    | ~ r1_tarski(X1,X0)
    | X2 = X1 ),
    inference(bin_hyper_res,[status(thm)],[c_288,c_726])).

cnf(c_1638,plain,
    ( ~ r2_hidden(sK0(X0,sK4,X1),X1)
    | ~ r2_hidden(sK0(X0,sK4,X1),sK4)
    | ~ r1_tarski(X1,X0)
    | ~ r1_tarski(sK4,X0)
    | X1 = sK4 ),
    inference(instantiation,[status(thm)],[c_774])).

cnf(c_1897,plain,
    ( ~ r2_hidden(sK0(u1_struct_0(sK3),sK4,X0),X0)
    | ~ r2_hidden(sK0(u1_struct_0(sK3),sK4,X0),sK4)
    | ~ r1_tarski(X0,u1_struct_0(sK3))
    | ~ r1_tarski(sK4,u1_struct_0(sK3))
    | X0 = sK4 ),
    inference(instantiation,[status(thm)],[c_1638])).

cnf(c_2398,plain,
    ( ~ r2_hidden(sK0(u1_struct_0(sK3),sK4,u1_struct_0(sK3)),u1_struct_0(sK3))
    | ~ r2_hidden(sK0(u1_struct_0(sK3),sK4,u1_struct_0(sK3)),sK4)
    | ~ r1_tarski(u1_struct_0(sK3),u1_struct_0(sK3))
    | ~ r1_tarski(sK4,u1_struct_0(sK3))
    | u1_struct_0(sK3) = sK4 ),
    inference(instantiation,[status(thm)],[c_1897])).

cnf(c_6,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | ~ m1_subset_1(X2,k1_zfmisc_1(X1))
    | m1_subset_1(sK0(X1,X0,X2),X1)
    | X2 = X0 ),
    inference(cnf_transformation,[],[f53])).

cnf(c_290,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | m1_subset_1(sK0(X1,X2,X0),X1)
    | ~ r1_tarski(X2,X1)
    | X0 = X2 ),
    inference(bin_hyper_res,[status(thm)],[c_6,c_224])).

cnf(c_776,plain,
    ( m1_subset_1(sK0(X0,X1,X2),X0)
    | ~ r1_tarski(X2,X0)
    | ~ r1_tarski(X1,X0)
    | X2 = X1 ),
    inference(bin_hyper_res,[status(thm)],[c_290,c_726])).

cnf(c_1639,plain,
    ( m1_subset_1(sK0(X0,sK4,X1),X0)
    | ~ r1_tarski(X1,X0)
    | ~ r1_tarski(sK4,X0)
    | X1 = sK4 ),
    inference(instantiation,[status(thm)],[c_776])).

cnf(c_1838,plain,
    ( m1_subset_1(sK0(u1_struct_0(sK3),sK4,X0),u1_struct_0(sK3))
    | ~ r1_tarski(X0,u1_struct_0(sK3))
    | ~ r1_tarski(sK4,u1_struct_0(sK3))
    | X0 = sK4 ),
    inference(instantiation,[status(thm)],[c_1639])).

cnf(c_2327,plain,
    ( m1_subset_1(sK0(u1_struct_0(sK3),sK4,u1_struct_0(sK3)),u1_struct_0(sK3))
    | ~ r1_tarski(u1_struct_0(sK3),u1_struct_0(sK3))
    | ~ r1_tarski(sK4,u1_struct_0(sK3))
    | u1_struct_0(sK3) = sK4 ),
    inference(instantiation,[status(thm)],[c_1838])).

cnf(c_1708,plain,
    ( r2_hidden(k3_yellow_0(sK3),X0)
    | ~ r2_hidden(k3_yellow_0(sK3),sK4)
    | ~ r1_tarski(sK4,X0) ),
    inference(instantiation,[status(thm)],[c_287])).

cnf(c_2119,plain,
    ( r2_hidden(k3_yellow_0(sK3),u1_struct_0(sK3))
    | ~ r2_hidden(k3_yellow_0(sK3),sK4)
    | ~ r1_tarski(sK4,u1_struct_0(sK3)) ),
    inference(instantiation,[status(thm)],[c_1708])).

cnf(c_13,plain,
    ( v13_waybel_0(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ r2_hidden(sK2(X1,X0),X0)
    | ~ l1_orders_2(X1) ),
    inference(cnf_transformation,[],[f67])).

cnf(c_617,plain,
    ( v13_waybel_0(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ r2_hidden(sK2(X1,X0),X0)
    | sK3 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_13,c_26])).

cnf(c_618,plain,
    ( v13_waybel_0(X0,sK3)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK3)))
    | ~ r2_hidden(sK2(sK3,X0),X0) ),
    inference(unflattening,[status(thm)],[c_617])).

cnf(c_1904,plain,
    ( v13_waybel_0(u1_struct_0(sK3),sK3)
    | ~ m1_subset_1(u1_struct_0(sK3),k1_zfmisc_1(u1_struct_0(sK3)))
    | ~ r2_hidden(sK2(sK3,u1_struct_0(sK3)),u1_struct_0(sK3)) ),
    inference(instantiation,[status(thm)],[c_618])).

cnf(c_16,plain,
    ( v13_waybel_0(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | m1_subset_1(sK2(X1,X0),u1_struct_0(X1))
    | ~ l1_orders_2(X1) ),
    inference(cnf_transformation,[],[f64])).

cnf(c_587,plain,
    ( v13_waybel_0(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | m1_subset_1(sK2(X1,X0),u1_struct_0(X1))
    | sK3 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_16,c_26])).

cnf(c_588,plain,
    ( v13_waybel_0(X0,sK3)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK3)))
    | m1_subset_1(sK2(sK3,X0),u1_struct_0(sK3)) ),
    inference(unflattening,[status(thm)],[c_587])).

cnf(c_1906,plain,
    ( v13_waybel_0(u1_struct_0(sK3),sK3)
    | m1_subset_1(sK2(sK3,u1_struct_0(sK3)),u1_struct_0(sK3))
    | ~ m1_subset_1(u1_struct_0(sK3),k1_zfmisc_1(u1_struct_0(sK3))) ),
    inference(instantiation,[status(thm)],[c_588])).

cnf(c_1664,plain,
    ( r1_tarski(u1_struct_0(sK3),u1_struct_0(sK3)) ),
    inference(instantiation,[status(thm)],[c_2])).

cnf(c_1667,plain,
    ( r1_tarski(u1_struct_0(sK3),u1_struct_0(sK3)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1664])).

cnf(c_1573,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK3)))
    | ~ r1_tarski(X0,u1_struct_0(sK3)) ),
    inference(instantiation,[status(thm)],[c_8])).

cnf(c_1663,plain,
    ( m1_subset_1(u1_struct_0(sK3),k1_zfmisc_1(u1_struct_0(sK3)))
    | ~ r1_tarski(u1_struct_0(sK3),u1_struct_0(sK3)) ),
    inference(instantiation,[status(thm)],[c_1573])).

cnf(c_1665,plain,
    ( m1_subset_1(u1_struct_0(sK3),k1_zfmisc_1(u1_struct_0(sK3))) = iProver_top
    | r1_tarski(u1_struct_0(sK3),u1_struct_0(sK3)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1663])).

cnf(c_22,negated_conjecture,
    ( v1_subset_1(sK4,u1_struct_0(sK3))
    | ~ r2_hidden(k3_yellow_0(sK3),sK4) ),
    inference(cnf_transformation,[],[f77])).

cnf(c_225,plain,
    ( v1_subset_1(sK4,u1_struct_0(sK3))
    | ~ r2_hidden(k3_yellow_0(sK3),sK4) ),
    inference(prop_impl,[status(thm)],[c_22])).

cnf(c_451,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X0))
    | ~ r2_hidden(k3_yellow_0(sK3),sK4)
    | u1_struct_0(sK3) != X0
    | sK4 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_20,c_225])).

cnf(c_452,plain,
    ( ~ m1_subset_1(u1_struct_0(sK3),k1_zfmisc_1(u1_struct_0(sK3)))
    | ~ r2_hidden(k3_yellow_0(sK3),sK4)
    | sK4 != u1_struct_0(sK3) ),
    inference(unflattening,[status(thm)],[c_451])).

cnf(c_453,plain,
    ( sK4 != u1_struct_0(sK3)
    | m1_subset_1(u1_struct_0(sK3),k1_zfmisc_1(u1_struct_0(sK3))) != iProver_top
    | r2_hidden(k3_yellow_0(sK3),sK4) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_452])).

cnf(c_24,negated_conjecture,
    ( v13_waybel_0(sK4,sK3) ),
    inference(cnf_transformation,[],[f75])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_14044,c_8977,c_6141,c_6045,c_6042,c_2566,c_2398,c_2327,c_2119,c_1904,c_1906,c_1667,c_1664,c_1665,c_1663,c_1655,c_1578,c_453,c_439,c_23,c_24])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : iproveropt_run.sh %d %s
% 0.14/0.34  % Computer   : n013.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % WCLimit    : 600
% 0.14/0.34  % DateTime   : Tue Dec  1 18:02:39 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.35  % Running in FOF mode
% 2.97/0.99  % SZS status Started for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.97/0.99  
% 2.97/0.99  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 2.97/0.99  
% 2.97/0.99  ------  iProver source info
% 2.97/0.99  
% 2.97/0.99  git: date: 2020-06-30 10:37:57 +0100
% 2.97/0.99  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 2.97/0.99  git: non_committed_changes: false
% 2.97/0.99  git: last_make_outside_of_git: false
% 2.97/0.99  
% 2.97/0.99  ------ 
% 2.97/0.99  
% 2.97/0.99  ------ Input Options
% 2.97/0.99  
% 2.97/0.99  --out_options                           all
% 2.97/0.99  --tptp_safe_out                         true
% 2.97/0.99  --problem_path                          ""
% 2.97/0.99  --include_path                          ""
% 2.97/0.99  --clausifier                            res/vclausify_rel
% 2.97/0.99  --clausifier_options                    --mode clausify
% 2.97/0.99  --stdin                                 false
% 2.97/0.99  --stats_out                             all
% 2.97/0.99  
% 2.97/0.99  ------ General Options
% 2.97/0.99  
% 2.97/0.99  --fof                                   false
% 2.97/0.99  --time_out_real                         305.
% 2.97/0.99  --time_out_virtual                      -1.
% 2.97/0.99  --symbol_type_check                     false
% 2.97/0.99  --clausify_out                          false
% 2.97/0.99  --sig_cnt_out                           false
% 2.97/0.99  --trig_cnt_out                          false
% 2.97/0.99  --trig_cnt_out_tolerance                1.
% 2.97/0.99  --trig_cnt_out_sk_spl                   false
% 2.97/0.99  --abstr_cl_out                          false
% 2.97/0.99  
% 2.97/0.99  ------ Global Options
% 2.97/0.99  
% 2.97/0.99  --schedule                              default
% 2.97/0.99  --add_important_lit                     false
% 2.97/0.99  --prop_solver_per_cl                    1000
% 2.97/0.99  --min_unsat_core                        false
% 2.97/0.99  --soft_assumptions                      false
% 2.97/0.99  --soft_lemma_size                       3
% 2.97/0.99  --prop_impl_unit_size                   0
% 2.97/0.99  --prop_impl_unit                        []
% 2.97/0.99  --share_sel_clauses                     true
% 2.97/0.99  --reset_solvers                         false
% 2.97/0.99  --bc_imp_inh                            [conj_cone]
% 2.97/0.99  --conj_cone_tolerance                   3.
% 2.97/0.99  --extra_neg_conj                        none
% 2.97/0.99  --large_theory_mode                     true
% 2.97/0.99  --prolific_symb_bound                   200
% 2.97/0.99  --lt_threshold                          2000
% 2.97/0.99  --clause_weak_htbl                      true
% 2.97/0.99  --gc_record_bc_elim                     false
% 2.97/0.99  
% 2.97/0.99  ------ Preprocessing Options
% 2.97/0.99  
% 2.97/0.99  --preprocessing_flag                    true
% 2.97/0.99  --time_out_prep_mult                    0.1
% 2.97/0.99  --splitting_mode                        input
% 2.97/0.99  --splitting_grd                         true
% 2.97/0.99  --splitting_cvd                         false
% 2.97/0.99  --splitting_cvd_svl                     false
% 2.97/0.99  --splitting_nvd                         32
% 2.97/0.99  --sub_typing                            true
% 2.97/0.99  --prep_gs_sim                           true
% 2.97/0.99  --prep_unflatten                        true
% 2.97/0.99  --prep_res_sim                          true
% 2.97/0.99  --prep_upred                            true
% 2.97/0.99  --prep_sem_filter                       exhaustive
% 2.97/0.99  --prep_sem_filter_out                   false
% 2.97/0.99  --pred_elim                             true
% 2.97/0.99  --res_sim_input                         true
% 2.97/0.99  --eq_ax_congr_red                       true
% 2.97/0.99  --pure_diseq_elim                       true
% 2.97/0.99  --brand_transform                       false
% 2.97/0.99  --non_eq_to_eq                          false
% 2.97/0.99  --prep_def_merge                        true
% 2.97/0.99  --prep_def_merge_prop_impl              false
% 2.97/0.99  --prep_def_merge_mbd                    true
% 2.97/0.99  --prep_def_merge_tr_red                 false
% 2.97/0.99  --prep_def_merge_tr_cl                  false
% 2.97/0.99  --smt_preprocessing                     true
% 2.97/0.99  --smt_ac_axioms                         fast
% 2.97/0.99  --preprocessed_out                      false
% 2.97/0.99  --preprocessed_stats                    false
% 2.97/0.99  
% 2.97/0.99  ------ Abstraction refinement Options
% 2.97/0.99  
% 2.97/0.99  --abstr_ref                             []
% 2.97/0.99  --abstr_ref_prep                        false
% 2.97/0.99  --abstr_ref_until_sat                   false
% 2.97/0.99  --abstr_ref_sig_restrict                funpre
% 2.97/0.99  --abstr_ref_af_restrict_to_split_sk     false
% 2.97/0.99  --abstr_ref_under                       []
% 2.97/0.99  
% 2.97/0.99  ------ SAT Options
% 2.97/0.99  
% 2.97/0.99  --sat_mode                              false
% 2.97/0.99  --sat_fm_restart_options                ""
% 2.97/0.99  --sat_gr_def                            false
% 2.97/0.99  --sat_epr_types                         true
% 2.97/0.99  --sat_non_cyclic_types                  false
% 2.97/0.99  --sat_finite_models                     false
% 2.97/0.99  --sat_fm_lemmas                         false
% 2.97/0.99  --sat_fm_prep                           false
% 2.97/0.99  --sat_fm_uc_incr                        true
% 2.97/0.99  --sat_out_model                         small
% 2.97/0.99  --sat_out_clauses                       false
% 2.97/0.99  
% 2.97/0.99  ------ QBF Options
% 2.97/0.99  
% 2.97/0.99  --qbf_mode                              false
% 2.97/0.99  --qbf_elim_univ                         false
% 2.97/0.99  --qbf_dom_inst                          none
% 2.97/0.99  --qbf_dom_pre_inst                      false
% 2.97/0.99  --qbf_sk_in                             false
% 2.97/0.99  --qbf_pred_elim                         true
% 2.97/0.99  --qbf_split                             512
% 2.97/0.99  
% 2.97/0.99  ------ BMC1 Options
% 2.97/0.99  
% 2.97/0.99  --bmc1_incremental                      false
% 2.97/0.99  --bmc1_axioms                           reachable_all
% 2.97/0.99  --bmc1_min_bound                        0
% 2.97/0.99  --bmc1_max_bound                        -1
% 2.97/0.99  --bmc1_max_bound_default                -1
% 2.97/0.99  --bmc1_symbol_reachability              true
% 2.97/0.99  --bmc1_property_lemmas                  false
% 2.97/0.99  --bmc1_k_induction                      false
% 2.97/0.99  --bmc1_non_equiv_states                 false
% 2.97/0.99  --bmc1_deadlock                         false
% 2.97/0.99  --bmc1_ucm                              false
% 2.97/0.99  --bmc1_add_unsat_core                   none
% 2.97/0.99  --bmc1_unsat_core_children              false
% 2.97/0.99  --bmc1_unsat_core_extrapolate_axioms    false
% 2.97/0.99  --bmc1_out_stat                         full
% 2.97/0.99  --bmc1_ground_init                      false
% 2.97/0.99  --bmc1_pre_inst_next_state              false
% 2.97/0.99  --bmc1_pre_inst_state                   false
% 2.97/0.99  --bmc1_pre_inst_reach_state             false
% 2.97/0.99  --bmc1_out_unsat_core                   false
% 2.97/0.99  --bmc1_aig_witness_out                  false
% 2.97/0.99  --bmc1_verbose                          false
% 2.97/0.99  --bmc1_dump_clauses_tptp                false
% 2.97/0.99  --bmc1_dump_unsat_core_tptp             false
% 2.97/0.99  --bmc1_dump_file                        -
% 2.97/0.99  --bmc1_ucm_expand_uc_limit              128
% 2.97/0.99  --bmc1_ucm_n_expand_iterations          6
% 2.97/0.99  --bmc1_ucm_extend_mode                  1
% 2.97/0.99  --bmc1_ucm_init_mode                    2
% 2.97/0.99  --bmc1_ucm_cone_mode                    none
% 2.97/0.99  --bmc1_ucm_reduced_relation_type        0
% 2.97/0.99  --bmc1_ucm_relax_model                  4
% 2.97/0.99  --bmc1_ucm_full_tr_after_sat            true
% 2.97/0.99  --bmc1_ucm_expand_neg_assumptions       false
% 2.97/0.99  --bmc1_ucm_layered_model                none
% 2.97/0.99  --bmc1_ucm_max_lemma_size               10
% 2.97/0.99  
% 2.97/0.99  ------ AIG Options
% 2.97/0.99  
% 2.97/0.99  --aig_mode                              false
% 2.97/0.99  
% 2.97/0.99  ------ Instantiation Options
% 2.97/0.99  
% 2.97/0.99  --instantiation_flag                    true
% 2.97/0.99  --inst_sos_flag                         false
% 2.97/0.99  --inst_sos_phase                        true
% 2.97/0.99  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 2.97/0.99  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 2.97/0.99  --inst_lit_sel_side                     num_symb
% 2.97/0.99  --inst_solver_per_active                1400
% 2.97/0.99  --inst_solver_calls_frac                1.
% 2.97/0.99  --inst_passive_queue_type               priority_queues
% 2.97/0.99  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 2.97/0.99  --inst_passive_queues_freq              [25;2]
% 2.97/0.99  --inst_dismatching                      true
% 2.97/0.99  --inst_eager_unprocessed_to_passive     true
% 2.97/0.99  --inst_prop_sim_given                   true
% 2.97/0.99  --inst_prop_sim_new                     false
% 2.97/0.99  --inst_subs_new                         false
% 2.97/0.99  --inst_eq_res_simp                      false
% 2.97/0.99  --inst_subs_given                       false
% 2.97/0.99  --inst_orphan_elimination               true
% 2.97/0.99  --inst_learning_loop_flag               true
% 2.97/0.99  --inst_learning_start                   3000
% 2.97/0.99  --inst_learning_factor                  2
% 2.97/0.99  --inst_start_prop_sim_after_learn       3
% 2.97/0.99  --inst_sel_renew                        solver
% 2.97/0.99  --inst_lit_activity_flag                true
% 2.97/0.99  --inst_restr_to_given                   false
% 2.97/0.99  --inst_activity_threshold               500
% 2.97/0.99  --inst_out_proof                        true
% 2.97/0.99  
% 2.97/0.99  ------ Resolution Options
% 2.97/0.99  
% 2.97/0.99  --resolution_flag                       true
% 2.97/0.99  --res_lit_sel                           adaptive
% 2.97/0.99  --res_lit_sel_side                      none
% 2.97/0.99  --res_ordering                          kbo
% 2.97/0.99  --res_to_prop_solver                    active
% 2.97/0.99  --res_prop_simpl_new                    false
% 2.97/0.99  --res_prop_simpl_given                  true
% 2.97/0.99  --res_passive_queue_type                priority_queues
% 2.97/0.99  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 2.97/0.99  --res_passive_queues_freq               [15;5]
% 2.97/0.99  --res_forward_subs                      full
% 2.97/0.99  --res_backward_subs                     full
% 2.97/0.99  --res_forward_subs_resolution           true
% 2.97/0.99  --res_backward_subs_resolution          true
% 2.97/0.99  --res_orphan_elimination                true
% 2.97/0.99  --res_time_limit                        2.
% 2.97/0.99  --res_out_proof                         true
% 2.97/0.99  
% 2.97/0.99  ------ Superposition Options
% 2.97/0.99  
% 2.97/0.99  --superposition_flag                    true
% 2.97/0.99  --sup_passive_queue_type                priority_queues
% 2.97/0.99  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 2.97/0.99  --sup_passive_queues_freq               [8;1;4]
% 2.97/0.99  --demod_completeness_check              fast
% 2.97/0.99  --demod_use_ground                      true
% 2.97/0.99  --sup_to_prop_solver                    passive
% 2.97/0.99  --sup_prop_simpl_new                    true
% 2.97/0.99  --sup_prop_simpl_given                  true
% 2.97/0.99  --sup_fun_splitting                     false
% 2.97/0.99  --sup_smt_interval                      50000
% 2.97/0.99  
% 2.97/0.99  ------ Superposition Simplification Setup
% 2.97/0.99  
% 2.97/0.99  --sup_indices_passive                   []
% 2.97/0.99  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.97/0.99  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.97/0.99  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.97/0.99  --sup_full_triv                         [TrivRules;PropSubs]
% 2.97/0.99  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.97/0.99  --sup_full_bw                           [BwDemod]
% 2.97/0.99  --sup_immed_triv                        [TrivRules]
% 2.97/0.99  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 2.97/0.99  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.97/0.99  --sup_immed_bw_main                     []
% 2.97/0.99  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.97/0.99  --sup_input_triv                        [Unflattening;TrivRules]
% 2.97/0.99  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.97/0.99  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.97/0.99  
% 2.97/0.99  ------ Combination Options
% 2.97/0.99  
% 2.97/0.99  --comb_res_mult                         3
% 2.97/0.99  --comb_sup_mult                         2
% 2.97/0.99  --comb_inst_mult                        10
% 2.97/0.99  
% 2.97/0.99  ------ Debug Options
% 2.97/0.99  
% 2.97/0.99  --dbg_backtrace                         false
% 2.97/0.99  --dbg_dump_prop_clauses                 false
% 2.97/0.99  --dbg_dump_prop_clauses_file            -
% 2.97/0.99  --dbg_out_stat                          false
% 2.97/0.99  ------ Parsing...
% 2.97/0.99  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 2.97/0.99  
% 2.97/0.99  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe:1:0s pe:2:0s pe:4:0s pe_e  sf_s  rm: 8 0s  sf_e  pe_s  pe_e 
% 2.97/0.99  
% 2.97/0.99  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 2.97/0.99  
% 2.97/0.99  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 2.97/0.99  ------ Proving...
% 2.97/0.99  ------ Problem Properties 
% 2.97/0.99  
% 2.97/0.99  
% 2.97/0.99  clauses                                 21
% 2.97/0.99  conjectures                             2
% 2.97/0.99  EPR                                     5
% 2.97/0.99  Horn                                    14
% 2.97/0.99  unary                                   4
% 2.97/0.99  binary                                  3
% 2.97/0.99  lits                                    62
% 2.97/0.99  lits eq                                 6
% 2.97/0.99  fd_pure                                 0
% 2.97/0.99  fd_pseudo                               0
% 2.97/0.99  fd_cond                                 0
% 2.97/0.99  fd_pseudo_cond                          4
% 2.97/0.99  AC symbols                              0
% 2.97/0.99  
% 2.97/0.99  ------ Schedule dynamic 5 is on 
% 2.97/0.99  
% 2.97/0.99  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" Time Limit: 10.
% 2.97/0.99  
% 2.97/0.99  
% 2.97/0.99  ------ 
% 2.97/0.99  Current options:
% 2.97/0.99  ------ 
% 2.97/0.99  
% 2.97/0.99  ------ Input Options
% 2.97/0.99  
% 2.97/0.99  --out_options                           all
% 2.97/0.99  --tptp_safe_out                         true
% 2.97/0.99  --problem_path                          ""
% 2.97/0.99  --include_path                          ""
% 2.97/0.99  --clausifier                            res/vclausify_rel
% 2.97/0.99  --clausifier_options                    --mode clausify
% 2.97/0.99  --stdin                                 false
% 2.97/0.99  --stats_out                             all
% 2.97/0.99  
% 2.97/0.99  ------ General Options
% 2.97/0.99  
% 2.97/0.99  --fof                                   false
% 2.97/0.99  --time_out_real                         305.
% 2.97/0.99  --time_out_virtual                      -1.
% 2.97/0.99  --symbol_type_check                     false
% 2.97/0.99  --clausify_out                          false
% 2.97/0.99  --sig_cnt_out                           false
% 2.97/0.99  --trig_cnt_out                          false
% 2.97/0.99  --trig_cnt_out_tolerance                1.
% 2.97/0.99  --trig_cnt_out_sk_spl                   false
% 2.97/0.99  --abstr_cl_out                          false
% 2.97/0.99  
% 2.97/0.99  ------ Global Options
% 2.97/0.99  
% 2.97/0.99  --schedule                              default
% 2.97/0.99  --add_important_lit                     false
% 2.97/0.99  --prop_solver_per_cl                    1000
% 2.97/0.99  --min_unsat_core                        false
% 2.97/0.99  --soft_assumptions                      false
% 2.97/0.99  --soft_lemma_size                       3
% 2.97/0.99  --prop_impl_unit_size                   0
% 2.97/0.99  --prop_impl_unit                        []
% 2.97/0.99  --share_sel_clauses                     true
% 2.97/0.99  --reset_solvers                         false
% 2.97/0.99  --bc_imp_inh                            [conj_cone]
% 2.97/0.99  --conj_cone_tolerance                   3.
% 2.97/0.99  --extra_neg_conj                        none
% 2.97/0.99  --large_theory_mode                     true
% 2.97/0.99  --prolific_symb_bound                   200
% 2.97/0.99  --lt_threshold                          2000
% 2.97/0.99  --clause_weak_htbl                      true
% 2.97/0.99  --gc_record_bc_elim                     false
% 2.97/0.99  
% 2.97/0.99  ------ Preprocessing Options
% 2.97/0.99  
% 2.97/0.99  --preprocessing_flag                    true
% 2.97/0.99  --time_out_prep_mult                    0.1
% 2.97/0.99  --splitting_mode                        input
% 2.97/0.99  --splitting_grd                         true
% 2.97/0.99  --splitting_cvd                         false
% 2.97/0.99  --splitting_cvd_svl                     false
% 2.97/0.99  --splitting_nvd                         32
% 2.97/0.99  --sub_typing                            true
% 2.97/0.99  --prep_gs_sim                           true
% 2.97/0.99  --prep_unflatten                        true
% 2.97/0.99  --prep_res_sim                          true
% 2.97/0.99  --prep_upred                            true
% 2.97/0.99  --prep_sem_filter                       exhaustive
% 2.97/0.99  --prep_sem_filter_out                   false
% 2.97/0.99  --pred_elim                             true
% 2.97/0.99  --res_sim_input                         true
% 2.97/0.99  --eq_ax_congr_red                       true
% 2.97/0.99  --pure_diseq_elim                       true
% 2.97/0.99  --brand_transform                       false
% 2.97/0.99  --non_eq_to_eq                          false
% 2.97/0.99  --prep_def_merge                        true
% 2.97/0.99  --prep_def_merge_prop_impl              false
% 2.97/0.99  --prep_def_merge_mbd                    true
% 2.97/0.99  --prep_def_merge_tr_red                 false
% 2.97/0.99  --prep_def_merge_tr_cl                  false
% 2.97/0.99  --smt_preprocessing                     true
% 2.97/0.99  --smt_ac_axioms                         fast
% 2.97/0.99  --preprocessed_out                      false
% 2.97/0.99  --preprocessed_stats                    false
% 2.97/0.99  
% 2.97/0.99  ------ Abstraction refinement Options
% 2.97/0.99  
% 2.97/0.99  --abstr_ref                             []
% 2.97/0.99  --abstr_ref_prep                        false
% 2.97/0.99  --abstr_ref_until_sat                   false
% 2.97/0.99  --abstr_ref_sig_restrict                funpre
% 2.97/0.99  --abstr_ref_af_restrict_to_split_sk     false
% 2.97/0.99  --abstr_ref_under                       []
% 2.97/0.99  
% 2.97/0.99  ------ SAT Options
% 2.97/0.99  
% 2.97/0.99  --sat_mode                              false
% 2.97/0.99  --sat_fm_restart_options                ""
% 2.97/0.99  --sat_gr_def                            false
% 2.97/0.99  --sat_epr_types                         true
% 2.97/0.99  --sat_non_cyclic_types                  false
% 2.97/0.99  --sat_finite_models                     false
% 2.97/0.99  --sat_fm_lemmas                         false
% 2.97/0.99  --sat_fm_prep                           false
% 2.97/0.99  --sat_fm_uc_incr                        true
% 2.97/0.99  --sat_out_model                         small
% 2.97/0.99  --sat_out_clauses                       false
% 2.97/0.99  
% 2.97/0.99  ------ QBF Options
% 2.97/0.99  
% 2.97/0.99  --qbf_mode                              false
% 2.97/0.99  --qbf_elim_univ                         false
% 2.97/0.99  --qbf_dom_inst                          none
% 2.97/0.99  --qbf_dom_pre_inst                      false
% 2.97/0.99  --qbf_sk_in                             false
% 2.97/0.99  --qbf_pred_elim                         true
% 2.97/0.99  --qbf_split                             512
% 2.97/0.99  
% 2.97/0.99  ------ BMC1 Options
% 2.97/0.99  
% 2.97/0.99  --bmc1_incremental                      false
% 2.97/0.99  --bmc1_axioms                           reachable_all
% 2.97/0.99  --bmc1_min_bound                        0
% 2.97/0.99  --bmc1_max_bound                        -1
% 2.97/0.99  --bmc1_max_bound_default                -1
% 2.97/0.99  --bmc1_symbol_reachability              true
% 2.97/0.99  --bmc1_property_lemmas                  false
% 2.97/0.99  --bmc1_k_induction                      false
% 2.97/0.99  --bmc1_non_equiv_states                 false
% 2.97/0.99  --bmc1_deadlock                         false
% 2.97/0.99  --bmc1_ucm                              false
% 2.97/0.99  --bmc1_add_unsat_core                   none
% 2.97/0.99  --bmc1_unsat_core_children              false
% 2.97/0.99  --bmc1_unsat_core_extrapolate_axioms    false
% 2.97/0.99  --bmc1_out_stat                         full
% 2.97/0.99  --bmc1_ground_init                      false
% 2.97/0.99  --bmc1_pre_inst_next_state              false
% 2.97/0.99  --bmc1_pre_inst_state                   false
% 2.97/0.99  --bmc1_pre_inst_reach_state             false
% 2.97/0.99  --bmc1_out_unsat_core                   false
% 2.97/0.99  --bmc1_aig_witness_out                  false
% 2.97/0.99  --bmc1_verbose                          false
% 2.97/0.99  --bmc1_dump_clauses_tptp                false
% 2.97/0.99  --bmc1_dump_unsat_core_tptp             false
% 2.97/0.99  --bmc1_dump_file                        -
% 2.97/0.99  --bmc1_ucm_expand_uc_limit              128
% 2.97/0.99  --bmc1_ucm_n_expand_iterations          6
% 2.97/0.99  --bmc1_ucm_extend_mode                  1
% 2.97/0.99  --bmc1_ucm_init_mode                    2
% 2.97/0.99  --bmc1_ucm_cone_mode                    none
% 2.97/0.99  --bmc1_ucm_reduced_relation_type        0
% 2.97/0.99  --bmc1_ucm_relax_model                  4
% 2.97/0.99  --bmc1_ucm_full_tr_after_sat            true
% 2.97/0.99  --bmc1_ucm_expand_neg_assumptions       false
% 2.97/0.99  --bmc1_ucm_layered_model                none
% 2.97/0.99  --bmc1_ucm_max_lemma_size               10
% 2.97/0.99  
% 2.97/0.99  ------ AIG Options
% 2.97/0.99  
% 2.97/0.99  --aig_mode                              false
% 2.97/0.99  
% 2.97/0.99  ------ Instantiation Options
% 2.97/0.99  
% 2.97/0.99  --instantiation_flag                    true
% 2.97/0.99  --inst_sos_flag                         false
% 2.97/0.99  --inst_sos_phase                        true
% 2.97/0.99  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 2.97/0.99  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 2.97/0.99  --inst_lit_sel_side                     none
% 2.97/0.99  --inst_solver_per_active                1400
% 2.97/0.99  --inst_solver_calls_frac                1.
% 2.97/0.99  --inst_passive_queue_type               priority_queues
% 2.97/0.99  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 2.97/0.99  --inst_passive_queues_freq              [25;2]
% 2.97/0.99  --inst_dismatching                      true
% 2.97/0.99  --inst_eager_unprocessed_to_passive     true
% 2.97/0.99  --inst_prop_sim_given                   true
% 2.97/0.99  --inst_prop_sim_new                     false
% 2.97/0.99  --inst_subs_new                         false
% 2.97/0.99  --inst_eq_res_simp                      false
% 2.97/0.99  --inst_subs_given                       false
% 2.97/0.99  --inst_orphan_elimination               true
% 2.97/0.99  --inst_learning_loop_flag               true
% 2.97/0.99  --inst_learning_start                   3000
% 2.97/0.99  --inst_learning_factor                  2
% 2.97/0.99  --inst_start_prop_sim_after_learn       3
% 2.97/0.99  --inst_sel_renew                        solver
% 2.97/0.99  --inst_lit_activity_flag                true
% 2.97/0.99  --inst_restr_to_given                   false
% 2.97/0.99  --inst_activity_threshold               500
% 2.97/0.99  --inst_out_proof                        true
% 2.97/0.99  
% 2.97/0.99  ------ Resolution Options
% 2.97/0.99  
% 2.97/0.99  --resolution_flag                       false
% 2.97/0.99  --res_lit_sel                           adaptive
% 2.97/0.99  --res_lit_sel_side                      none
% 2.97/0.99  --res_ordering                          kbo
% 2.97/0.99  --res_to_prop_solver                    active
% 2.97/0.99  --res_prop_simpl_new                    false
% 2.97/0.99  --res_prop_simpl_given                  true
% 2.97/0.99  --res_passive_queue_type                priority_queues
% 2.97/0.99  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 2.97/0.99  --res_passive_queues_freq               [15;5]
% 2.97/0.99  --res_forward_subs                      full
% 2.97/0.99  --res_backward_subs                     full
% 2.97/0.99  --res_forward_subs_resolution           true
% 2.97/0.99  --res_backward_subs_resolution          true
% 2.97/0.99  --res_orphan_elimination                true
% 2.97/0.99  --res_time_limit                        2.
% 2.97/0.99  --res_out_proof                         true
% 2.97/0.99  
% 2.97/0.99  ------ Superposition Options
% 2.97/0.99  
% 2.97/0.99  --superposition_flag                    true
% 2.97/0.99  --sup_passive_queue_type                priority_queues
% 2.97/0.99  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 2.97/0.99  --sup_passive_queues_freq               [8;1;4]
% 2.97/0.99  --demod_completeness_check              fast
% 2.97/0.99  --demod_use_ground                      true
% 2.97/0.99  --sup_to_prop_solver                    passive
% 2.97/0.99  --sup_prop_simpl_new                    true
% 2.97/0.99  --sup_prop_simpl_given                  true
% 2.97/0.99  --sup_fun_splitting                     false
% 2.97/0.99  --sup_smt_interval                      50000
% 2.97/0.99  
% 2.97/0.99  ------ Superposition Simplification Setup
% 2.97/0.99  
% 2.97/0.99  --sup_indices_passive                   []
% 2.97/0.99  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.97/0.99  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.97/0.99  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.97/0.99  --sup_full_triv                         [TrivRules;PropSubs]
% 2.97/0.99  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.97/0.99  --sup_full_bw                           [BwDemod]
% 2.97/0.99  --sup_immed_triv                        [TrivRules]
% 2.97/0.99  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 2.97/0.99  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.97/0.99  --sup_immed_bw_main                     []
% 2.97/0.99  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.97/0.99  --sup_input_triv                        [Unflattening;TrivRules]
% 2.97/0.99  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.97/0.99  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.97/0.99  
% 2.97/0.99  ------ Combination Options
% 2.97/0.99  
% 2.97/0.99  --comb_res_mult                         3
% 2.97/0.99  --comb_sup_mult                         2
% 2.97/0.99  --comb_inst_mult                        10
% 2.97/0.99  
% 2.97/0.99  ------ Debug Options
% 2.97/0.99  
% 2.97/0.99  --dbg_backtrace                         false
% 2.97/0.99  --dbg_dump_prop_clauses                 false
% 2.97/0.99  --dbg_dump_prop_clauses_file            -
% 2.97/0.99  --dbg_out_stat                          false
% 2.97/0.99  
% 2.97/0.99  
% 2.97/0.99  
% 2.97/0.99  
% 2.97/0.99  ------ Proving...
% 2.97/0.99  
% 2.97/0.99  
% 2.97/0.99  % SZS status Theorem for theBenchmark.p
% 2.97/0.99  
% 2.97/0.99  % SZS output start CNFRefutation for theBenchmark.p
% 2.97/0.99  
% 2.97/0.99  fof(f2,axiom,(
% 2.97/0.99    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => ! [X2] : (r2_hidden(X2,X1) => r2_hidden(X2,X0)))),
% 2.97/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.97/0.99  
% 2.97/0.99  fof(f16,plain,(
% 2.97/0.99    ! [X0,X1] : (! [X2] : (r2_hidden(X2,X0) | ~r2_hidden(X2,X1)) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 2.97/0.99    inference(ennf_transformation,[],[f2])).
% 2.97/0.99  
% 2.97/0.99  fof(f52,plain,(
% 2.97/0.99    ( ! [X2,X0,X1] : (r2_hidden(X2,X0) | ~r2_hidden(X2,X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 2.97/0.99    inference(cnf_transformation,[],[f16])).
% 2.97/0.99  
% 2.97/0.99  fof(f5,axiom,(
% 2.97/0.99    ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) <=> r1_tarski(X0,X1))),
% 2.97/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.97/0.99  
% 2.97/0.99  fof(f37,plain,(
% 2.97/0.99    ! [X0,X1] : ((m1_subset_1(X0,k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1)) & (r1_tarski(X0,X1) | ~m1_subset_1(X0,k1_zfmisc_1(X1))))),
% 2.97/0.99    inference(nnf_transformation,[],[f5])).
% 2.97/0.99  
% 2.97/0.99  fof(f58,plain,(
% 2.97/0.99    ( ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1)) )),
% 2.97/0.99    inference(cnf_transformation,[],[f37])).
% 2.97/0.99  
% 2.97/0.99  fof(f9,axiom,(
% 2.97/0.99    ! [X0] : (l1_orders_2(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => (v13_waybel_0(X1,X0) <=> ! [X2] : (m1_subset_1(X2,u1_struct_0(X0)) => ! [X3] : (m1_subset_1(X3,u1_struct_0(X0)) => ((r1_orders_2(X0,X2,X3) & r2_hidden(X2,X1)) => r2_hidden(X3,X1)))))))),
% 2.97/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.97/0.99  
% 2.97/0.99  fof(f26,plain,(
% 2.97/0.99    ! [X0] : (! [X1] : ((v13_waybel_0(X1,X0) <=> ! [X2] : (! [X3] : ((r2_hidden(X3,X1) | (~r1_orders_2(X0,X2,X3) | ~r2_hidden(X2,X1))) | ~m1_subset_1(X3,u1_struct_0(X0))) | ~m1_subset_1(X2,u1_struct_0(X0)))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_orders_2(X0))),
% 2.97/0.99    inference(ennf_transformation,[],[f9])).
% 2.97/0.99  
% 2.97/0.99  fof(f27,plain,(
% 2.97/0.99    ! [X0] : (! [X1] : ((v13_waybel_0(X1,X0) <=> ! [X2] : (! [X3] : (r2_hidden(X3,X1) | ~r1_orders_2(X0,X2,X3) | ~r2_hidden(X2,X1) | ~m1_subset_1(X3,u1_struct_0(X0))) | ~m1_subset_1(X2,u1_struct_0(X0)))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_orders_2(X0))),
% 2.97/0.99    inference(flattening,[],[f26])).
% 2.97/0.99  
% 2.97/0.99  fof(f38,plain,(
% 2.97/0.99    ! [X0] : (! [X1] : (((v13_waybel_0(X1,X0) | ? [X2] : (? [X3] : (~r2_hidden(X3,X1) & r1_orders_2(X0,X2,X3) & r2_hidden(X2,X1) & m1_subset_1(X3,u1_struct_0(X0))) & m1_subset_1(X2,u1_struct_0(X0)))) & (! [X2] : (! [X3] : (r2_hidden(X3,X1) | ~r1_orders_2(X0,X2,X3) | ~r2_hidden(X2,X1) | ~m1_subset_1(X3,u1_struct_0(X0))) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~v13_waybel_0(X1,X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_orders_2(X0))),
% 2.97/0.99    inference(nnf_transformation,[],[f27])).
% 2.97/0.99  
% 2.97/0.99  fof(f39,plain,(
% 2.97/0.99    ! [X0] : (! [X1] : (((v13_waybel_0(X1,X0) | ? [X2] : (? [X3] : (~r2_hidden(X3,X1) & r1_orders_2(X0,X2,X3) & r2_hidden(X2,X1) & m1_subset_1(X3,u1_struct_0(X0))) & m1_subset_1(X2,u1_struct_0(X0)))) & (! [X4] : (! [X5] : (r2_hidden(X5,X1) | ~r1_orders_2(X0,X4,X5) | ~r2_hidden(X4,X1) | ~m1_subset_1(X5,u1_struct_0(X0))) | ~m1_subset_1(X4,u1_struct_0(X0))) | ~v13_waybel_0(X1,X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_orders_2(X0))),
% 2.97/0.99    inference(rectify,[],[f38])).
% 2.97/0.99  
% 2.97/0.99  fof(f41,plain,(
% 2.97/0.99    ( ! [X2] : (! [X1,X0] : (? [X3] : (~r2_hidden(X3,X1) & r1_orders_2(X0,X2,X3) & r2_hidden(X2,X1) & m1_subset_1(X3,u1_struct_0(X0))) => (~r2_hidden(sK2(X0,X1),X1) & r1_orders_2(X0,X2,sK2(X0,X1)) & r2_hidden(X2,X1) & m1_subset_1(sK2(X0,X1),u1_struct_0(X0))))) )),
% 2.97/0.99    introduced(choice_axiom,[])).
% 2.97/0.99  
% 2.97/0.99  fof(f40,plain,(
% 2.97/0.99    ! [X1,X0] : (? [X2] : (? [X3] : (~r2_hidden(X3,X1) & r1_orders_2(X0,X2,X3) & r2_hidden(X2,X1) & m1_subset_1(X3,u1_struct_0(X0))) & m1_subset_1(X2,u1_struct_0(X0))) => (? [X3] : (~r2_hidden(X3,X1) & r1_orders_2(X0,sK1(X0,X1),X3) & r2_hidden(sK1(X0,X1),X1) & m1_subset_1(X3,u1_struct_0(X0))) & m1_subset_1(sK1(X0,X1),u1_struct_0(X0))))),
% 2.97/0.99    introduced(choice_axiom,[])).
% 2.97/0.99  
% 2.97/0.99  fof(f42,plain,(
% 2.97/0.99    ! [X0] : (! [X1] : (((v13_waybel_0(X1,X0) | ((~r2_hidden(sK2(X0,X1),X1) & r1_orders_2(X0,sK1(X0,X1),sK2(X0,X1)) & r2_hidden(sK1(X0,X1),X1) & m1_subset_1(sK2(X0,X1),u1_struct_0(X0))) & m1_subset_1(sK1(X0,X1),u1_struct_0(X0)))) & (! [X4] : (! [X5] : (r2_hidden(X5,X1) | ~r1_orders_2(X0,X4,X5) | ~r2_hidden(X4,X1) | ~m1_subset_1(X5,u1_struct_0(X0))) | ~m1_subset_1(X4,u1_struct_0(X0))) | ~v13_waybel_0(X1,X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_orders_2(X0))),
% 2.97/0.99    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1,sK2])],[f39,f41,f40])).
% 2.97/0.99  
% 2.97/0.99  fof(f62,plain,(
% 2.97/0.99    ( ! [X4,X0,X5,X1] : (r2_hidden(X5,X1) | ~r1_orders_2(X0,X4,X5) | ~r2_hidden(X4,X1) | ~m1_subset_1(X5,u1_struct_0(X0)) | ~m1_subset_1(X4,u1_struct_0(X0)) | ~v13_waybel_0(X1,X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_orders_2(X0)) )),
% 2.97/0.99    inference(cnf_transformation,[],[f42])).
% 2.97/0.99  
% 2.97/0.99  fof(f8,axiom,(
% 2.97/0.99    ! [X0] : ((l1_orders_2(X0) & v1_yellow_0(X0) & v5_orders_2(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,u1_struct_0(X0)) => r1_orders_2(X0,k3_yellow_0(X0),X1)))),
% 2.97/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.97/0.99  
% 2.97/0.99  fof(f24,plain,(
% 2.97/0.99    ! [X0] : (! [X1] : (r1_orders_2(X0,k3_yellow_0(X0),X1) | ~m1_subset_1(X1,u1_struct_0(X0))) | (~l1_orders_2(X0) | ~v1_yellow_0(X0) | ~v5_orders_2(X0) | v2_struct_0(X0)))),
% 2.97/0.99    inference(ennf_transformation,[],[f8])).
% 2.97/0.99  
% 2.97/0.99  fof(f25,plain,(
% 2.97/0.99    ! [X0] : (! [X1] : (r1_orders_2(X0,k3_yellow_0(X0),X1) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~l1_orders_2(X0) | ~v1_yellow_0(X0) | ~v5_orders_2(X0) | v2_struct_0(X0))),
% 2.97/0.99    inference(flattening,[],[f24])).
% 2.97/0.99  
% 2.97/0.99  fof(f61,plain,(
% 2.97/0.99    ( ! [X0,X1] : (r1_orders_2(X0,k3_yellow_0(X0),X1) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_orders_2(X0) | ~v1_yellow_0(X0) | ~v5_orders_2(X0) | v2_struct_0(X0)) )),
% 2.97/0.99    inference(cnf_transformation,[],[f25])).
% 2.97/0.99  
% 2.97/0.99  fof(f11,conjecture,(
% 2.97/0.99    ! [X0] : ((l1_orders_2(X0) & v1_yellow_0(X0) & v5_orders_2(X0) & v4_orders_2(X0) & v3_orders_2(X0) & ~v2_struct_0(X0)) => ! [X1] : ((m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & v13_waybel_0(X1,X0) & v2_waybel_0(X1,X0) & ~v1_xboole_0(X1)) => (v1_subset_1(X1,u1_struct_0(X0)) <=> ~r2_hidden(k3_yellow_0(X0),X1))))),
% 2.97/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.97/0.99  
% 2.97/0.99  fof(f12,negated_conjecture,(
% 2.97/0.99    ~! [X0] : ((l1_orders_2(X0) & v1_yellow_0(X0) & v5_orders_2(X0) & v4_orders_2(X0) & v3_orders_2(X0) & ~v2_struct_0(X0)) => ! [X1] : ((m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & v13_waybel_0(X1,X0) & v2_waybel_0(X1,X0) & ~v1_xboole_0(X1)) => (v1_subset_1(X1,u1_struct_0(X0)) <=> ~r2_hidden(k3_yellow_0(X0),X1))))),
% 2.97/0.99    inference(negated_conjecture,[],[f11])).
% 2.97/0.99  
% 2.97/0.99  fof(f13,plain,(
% 2.97/0.99    ~! [X0] : ((l1_orders_2(X0) & v1_yellow_0(X0) & v5_orders_2(X0) & v4_orders_2(X0) & v3_orders_2(X0) & ~v2_struct_0(X0)) => ! [X1] : ((m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & v13_waybel_0(X1,X0) & ~v1_xboole_0(X1)) => (v1_subset_1(X1,u1_struct_0(X0)) <=> ~r2_hidden(k3_yellow_0(X0),X1))))),
% 2.97/0.99    inference(pure_predicate_removal,[],[f12])).
% 2.97/0.99  
% 2.97/0.99  fof(f14,plain,(
% 2.97/0.99    ~! [X0] : ((l1_orders_2(X0) & v1_yellow_0(X0) & v5_orders_2(X0) & v3_orders_2(X0) & ~v2_struct_0(X0)) => ! [X1] : ((m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & v13_waybel_0(X1,X0) & ~v1_xboole_0(X1)) => (v1_subset_1(X1,u1_struct_0(X0)) <=> ~r2_hidden(k3_yellow_0(X0),X1))))),
% 2.97/0.99    inference(pure_predicate_removal,[],[f13])).
% 2.97/0.99  
% 2.97/0.99  fof(f15,plain,(
% 2.97/0.99    ~! [X0] : ((l1_orders_2(X0) & v1_yellow_0(X0) & v5_orders_2(X0) & ~v2_struct_0(X0)) => ! [X1] : ((m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & v13_waybel_0(X1,X0) & ~v1_xboole_0(X1)) => (v1_subset_1(X1,u1_struct_0(X0)) <=> ~r2_hidden(k3_yellow_0(X0),X1))))),
% 2.97/0.99    inference(pure_predicate_removal,[],[f14])).
% 2.97/0.99  
% 2.97/0.99  fof(f29,plain,(
% 2.97/0.99    ? [X0] : (? [X1] : ((v1_subset_1(X1,u1_struct_0(X0)) <~> ~r2_hidden(k3_yellow_0(X0),X1)) & (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & v13_waybel_0(X1,X0) & ~v1_xboole_0(X1))) & (l1_orders_2(X0) & v1_yellow_0(X0) & v5_orders_2(X0) & ~v2_struct_0(X0)))),
% 2.97/0.99    inference(ennf_transformation,[],[f15])).
% 2.97/0.99  
% 2.97/0.99  fof(f30,plain,(
% 2.97/0.99    ? [X0] : (? [X1] : ((v1_subset_1(X1,u1_struct_0(X0)) <~> ~r2_hidden(k3_yellow_0(X0),X1)) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & v13_waybel_0(X1,X0) & ~v1_xboole_0(X1)) & l1_orders_2(X0) & v1_yellow_0(X0) & v5_orders_2(X0) & ~v2_struct_0(X0))),
% 2.97/0.99    inference(flattening,[],[f29])).
% 2.97/0.99  
% 2.97/0.99  fof(f44,plain,(
% 2.97/0.99    ? [X0] : (? [X1] : (((r2_hidden(k3_yellow_0(X0),X1) | ~v1_subset_1(X1,u1_struct_0(X0))) & (~r2_hidden(k3_yellow_0(X0),X1) | v1_subset_1(X1,u1_struct_0(X0)))) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & v13_waybel_0(X1,X0) & ~v1_xboole_0(X1)) & l1_orders_2(X0) & v1_yellow_0(X0) & v5_orders_2(X0) & ~v2_struct_0(X0))),
% 2.97/0.99    inference(nnf_transformation,[],[f30])).
% 2.97/0.99  
% 2.97/0.99  fof(f45,plain,(
% 2.97/0.99    ? [X0] : (? [X1] : ((r2_hidden(k3_yellow_0(X0),X1) | ~v1_subset_1(X1,u1_struct_0(X0))) & (~r2_hidden(k3_yellow_0(X0),X1) | v1_subset_1(X1,u1_struct_0(X0))) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & v13_waybel_0(X1,X0) & ~v1_xboole_0(X1)) & l1_orders_2(X0) & v1_yellow_0(X0) & v5_orders_2(X0) & ~v2_struct_0(X0))),
% 2.97/0.99    inference(flattening,[],[f44])).
% 2.97/0.99  
% 2.97/0.99  fof(f47,plain,(
% 2.97/0.99    ( ! [X0] : (? [X1] : ((r2_hidden(k3_yellow_0(X0),X1) | ~v1_subset_1(X1,u1_struct_0(X0))) & (~r2_hidden(k3_yellow_0(X0),X1) | v1_subset_1(X1,u1_struct_0(X0))) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & v13_waybel_0(X1,X0) & ~v1_xboole_0(X1)) => ((r2_hidden(k3_yellow_0(X0),sK4) | ~v1_subset_1(sK4,u1_struct_0(X0))) & (~r2_hidden(k3_yellow_0(X0),sK4) | v1_subset_1(sK4,u1_struct_0(X0))) & m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(X0))) & v13_waybel_0(sK4,X0) & ~v1_xboole_0(sK4))) )),
% 2.97/0.99    introduced(choice_axiom,[])).
% 2.97/0.99  
% 2.97/0.99  fof(f46,plain,(
% 2.97/0.99    ? [X0] : (? [X1] : ((r2_hidden(k3_yellow_0(X0),X1) | ~v1_subset_1(X1,u1_struct_0(X0))) & (~r2_hidden(k3_yellow_0(X0),X1) | v1_subset_1(X1,u1_struct_0(X0))) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & v13_waybel_0(X1,X0) & ~v1_xboole_0(X1)) & l1_orders_2(X0) & v1_yellow_0(X0) & v5_orders_2(X0) & ~v2_struct_0(X0)) => (? [X1] : ((r2_hidden(k3_yellow_0(sK3),X1) | ~v1_subset_1(X1,u1_struct_0(sK3))) & (~r2_hidden(k3_yellow_0(sK3),X1) | v1_subset_1(X1,u1_struct_0(sK3))) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK3))) & v13_waybel_0(X1,sK3) & ~v1_xboole_0(X1)) & l1_orders_2(sK3) & v1_yellow_0(sK3) & v5_orders_2(sK3) & ~v2_struct_0(sK3))),
% 2.97/0.99    introduced(choice_axiom,[])).
% 2.97/0.99  
% 2.97/0.99  fof(f48,plain,(
% 2.97/0.99    ((r2_hidden(k3_yellow_0(sK3),sK4) | ~v1_subset_1(sK4,u1_struct_0(sK3))) & (~r2_hidden(k3_yellow_0(sK3),sK4) | v1_subset_1(sK4,u1_struct_0(sK3))) & m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(sK3))) & v13_waybel_0(sK4,sK3) & ~v1_xboole_0(sK4)) & l1_orders_2(sK3) & v1_yellow_0(sK3) & v5_orders_2(sK3) & ~v2_struct_0(sK3)),
% 2.97/0.99    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3,sK4])],[f45,f47,f46])).
% 2.97/0.99  
% 2.97/0.99  fof(f72,plain,(
% 2.97/0.99    v1_yellow_0(sK3)),
% 2.97/0.99    inference(cnf_transformation,[],[f48])).
% 2.97/0.99  
% 2.97/0.99  fof(f70,plain,(
% 2.97/0.99    ~v2_struct_0(sK3)),
% 2.97/0.99    inference(cnf_transformation,[],[f48])).
% 2.97/0.99  
% 2.97/0.99  fof(f71,plain,(
% 2.97/0.99    v5_orders_2(sK3)),
% 2.97/0.99    inference(cnf_transformation,[],[f48])).
% 2.97/0.99  
% 2.97/0.99  fof(f73,plain,(
% 2.97/0.99    l1_orders_2(sK3)),
% 2.97/0.99    inference(cnf_transformation,[],[f48])).
% 2.97/0.99  
% 2.97/0.99  fof(f7,axiom,(
% 2.97/0.99    ! [X0] : (l1_orders_2(X0) => m1_subset_1(k3_yellow_0(X0),u1_struct_0(X0)))),
% 2.97/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.97/0.99  
% 2.97/0.99  fof(f23,plain,(
% 2.97/0.99    ! [X0] : (m1_subset_1(k3_yellow_0(X0),u1_struct_0(X0)) | ~l1_orders_2(X0))),
% 2.97/0.99    inference(ennf_transformation,[],[f7])).
% 2.97/0.99  
% 2.97/0.99  fof(f60,plain,(
% 2.97/0.99    ( ! [X0] : (m1_subset_1(k3_yellow_0(X0),u1_struct_0(X0)) | ~l1_orders_2(X0)) )),
% 2.97/0.99    inference(cnf_transformation,[],[f23])).
% 2.97/0.99  
% 2.97/0.99  fof(f10,axiom,(
% 2.97/0.99    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => (v1_subset_1(X1,X0) <=> X0 != X1))),
% 2.97/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.97/0.99  
% 2.97/0.99  fof(f28,plain,(
% 2.97/0.99    ! [X0,X1] : ((v1_subset_1(X1,X0) <=> X0 != X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 2.97/0.99    inference(ennf_transformation,[],[f10])).
% 2.97/0.99  
% 2.97/0.99  fof(f43,plain,(
% 2.97/0.99    ! [X0,X1] : (((v1_subset_1(X1,X0) | X0 = X1) & (X0 != X1 | ~v1_subset_1(X1,X0))) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 2.97/0.99    inference(nnf_transformation,[],[f28])).
% 2.97/0.99  
% 2.97/0.99  fof(f69,plain,(
% 2.97/0.99    ( ! [X0,X1] : (v1_subset_1(X1,X0) | X0 = X1 | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 2.97/0.99    inference(cnf_transformation,[],[f43])).
% 2.97/0.99  
% 2.97/0.99  fof(f78,plain,(
% 2.97/0.99    r2_hidden(k3_yellow_0(sK3),sK4) | ~v1_subset_1(sK4,u1_struct_0(sK3))),
% 2.97/0.99    inference(cnf_transformation,[],[f48])).
% 2.97/0.99  
% 2.97/0.99  fof(f76,plain,(
% 2.97/0.99    m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(sK3)))),
% 2.97/0.99    inference(cnf_transformation,[],[f48])).
% 2.97/0.99  
% 2.97/0.99  fof(f68,plain,(
% 2.97/0.99    ( ! [X0,X1] : (X0 != X1 | ~v1_subset_1(X1,X0) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 2.97/0.99    inference(cnf_transformation,[],[f43])).
% 2.97/0.99  
% 2.97/0.99  fof(f81,plain,(
% 2.97/0.99    ( ! [X1] : (~v1_subset_1(X1,X1) | ~m1_subset_1(X1,k1_zfmisc_1(X1))) )),
% 2.97/0.99    inference(equality_resolution,[],[f68])).
% 2.97/0.99  
% 2.97/0.99  fof(f1,axiom,(
% 2.97/0.99    ! [X0,X1] : (X0 = X1 <=> (r1_tarski(X1,X0) & r1_tarski(X0,X1)))),
% 2.97/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.97/0.99  
% 2.97/0.99  fof(f31,plain,(
% 2.97/0.99    ! [X0,X1] : ((X0 = X1 | (~r1_tarski(X1,X0) | ~r1_tarski(X0,X1))) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 2.97/0.99    inference(nnf_transformation,[],[f1])).
% 2.97/0.99  
% 2.97/0.99  fof(f32,plain,(
% 2.97/0.99    ! [X0,X1] : ((X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 2.97/0.99    inference(flattening,[],[f31])).
% 2.97/0.99  
% 2.97/0.99  fof(f49,plain,(
% 2.97/0.99    ( ! [X0,X1] : (r1_tarski(X0,X1) | X0 != X1) )),
% 2.97/0.99    inference(cnf_transformation,[],[f32])).
% 2.97/0.99  
% 2.97/0.99  fof(f80,plain,(
% 2.97/0.99    ( ! [X1] : (r1_tarski(X1,X1)) )),
% 2.97/0.99    inference(equality_resolution,[],[f49])).
% 2.97/0.99  
% 2.97/0.99  fof(f57,plain,(
% 2.97/0.99    ( ! [X0,X1] : (r1_tarski(X0,X1) | ~m1_subset_1(X0,k1_zfmisc_1(X1))) )),
% 2.97/0.99    inference(cnf_transformation,[],[f37])).
% 2.97/0.99  
% 2.97/0.99  fof(f4,axiom,(
% 2.97/0.99    ! [X0,X1] : (m1_subset_1(X0,X1) => (r2_hidden(X0,X1) | v1_xboole_0(X1)))),
% 2.97/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.97/0.99  
% 2.97/0.99  fof(f19,plain,(
% 2.97/0.99    ! [X0,X1] : ((r2_hidden(X0,X1) | v1_xboole_0(X1)) | ~m1_subset_1(X0,X1))),
% 2.97/0.99    inference(ennf_transformation,[],[f4])).
% 2.97/0.99  
% 2.97/0.99  fof(f20,plain,(
% 2.97/0.99    ! [X0,X1] : (r2_hidden(X0,X1) | v1_xboole_0(X1) | ~m1_subset_1(X0,X1))),
% 2.97/0.99    inference(flattening,[],[f19])).
% 2.97/0.99  
% 2.97/0.99  fof(f56,plain,(
% 2.97/0.99    ( ! [X0,X1] : (r2_hidden(X0,X1) | v1_xboole_0(X1) | ~m1_subset_1(X0,X1)) )),
% 2.97/0.99    inference(cnf_transformation,[],[f20])).
% 2.97/0.99  
% 2.97/0.99  fof(f74,plain,(
% 2.97/0.99    ~v1_xboole_0(sK4)),
% 2.97/0.99    inference(cnf_transformation,[],[f48])).
% 2.97/0.99  
% 2.97/0.99  fof(f3,axiom,(
% 2.97/0.99    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(X0)) => (! [X3] : (m1_subset_1(X3,X0) => (r2_hidden(X3,X1) <=> r2_hidden(X3,X2))) => X1 = X2)))),
% 2.97/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.97/0.99  
% 2.97/0.99  fof(f17,plain,(
% 2.97/0.99    ! [X0,X1] : (! [X2] : ((X1 = X2 | ? [X3] : ((r2_hidden(X3,X1) <~> r2_hidden(X3,X2)) & m1_subset_1(X3,X0))) | ~m1_subset_1(X2,k1_zfmisc_1(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 2.97/0.99    inference(ennf_transformation,[],[f3])).
% 2.97/0.99  
% 2.97/0.99  fof(f18,plain,(
% 2.97/0.99    ! [X0,X1] : (! [X2] : (X1 = X2 | ? [X3] : ((r2_hidden(X3,X1) <~> r2_hidden(X3,X2)) & m1_subset_1(X3,X0)) | ~m1_subset_1(X2,k1_zfmisc_1(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 2.97/0.99    inference(flattening,[],[f17])).
% 2.97/0.99  
% 2.97/0.99  fof(f33,plain,(
% 2.97/0.99    ! [X0,X1] : (! [X2] : (X1 = X2 | ? [X3] : (((~r2_hidden(X3,X2) | ~r2_hidden(X3,X1)) & (r2_hidden(X3,X2) | r2_hidden(X3,X1))) & m1_subset_1(X3,X0)) | ~m1_subset_1(X2,k1_zfmisc_1(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 2.97/0.99    inference(nnf_transformation,[],[f18])).
% 2.97/0.99  
% 2.97/0.99  fof(f34,plain,(
% 2.97/0.99    ! [X0,X1] : (! [X2] : (X1 = X2 | ? [X3] : ((~r2_hidden(X3,X2) | ~r2_hidden(X3,X1)) & (r2_hidden(X3,X2) | r2_hidden(X3,X1)) & m1_subset_1(X3,X0)) | ~m1_subset_1(X2,k1_zfmisc_1(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 2.97/0.99    inference(flattening,[],[f33])).
% 2.97/0.99  
% 2.97/0.99  fof(f35,plain,(
% 2.97/0.99    ! [X2,X1,X0] : (? [X3] : ((~r2_hidden(X3,X2) | ~r2_hidden(X3,X1)) & (r2_hidden(X3,X2) | r2_hidden(X3,X1)) & m1_subset_1(X3,X0)) => ((~r2_hidden(sK0(X0,X1,X2),X2) | ~r2_hidden(sK0(X0,X1,X2),X1)) & (r2_hidden(sK0(X0,X1,X2),X2) | r2_hidden(sK0(X0,X1,X2),X1)) & m1_subset_1(sK0(X0,X1,X2),X0)))),
% 2.97/0.99    introduced(choice_axiom,[])).
% 2.97/0.99  
% 2.97/0.99  fof(f36,plain,(
% 2.97/0.99    ! [X0,X1] : (! [X2] : (X1 = X2 | ((~r2_hidden(sK0(X0,X1,X2),X2) | ~r2_hidden(sK0(X0,X1,X2),X1)) & (r2_hidden(sK0(X0,X1,X2),X2) | r2_hidden(sK0(X0,X1,X2),X1)) & m1_subset_1(sK0(X0,X1,X2),X0)) | ~m1_subset_1(X2,k1_zfmisc_1(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 2.97/0.99    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f34,f35])).
% 2.97/0.99  
% 2.97/0.99  fof(f55,plain,(
% 2.97/0.99    ( ! [X2,X0,X1] : (X1 = X2 | ~r2_hidden(sK0(X0,X1,X2),X2) | ~r2_hidden(sK0(X0,X1,X2),X1) | ~m1_subset_1(X2,k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 2.97/0.99    inference(cnf_transformation,[],[f36])).
% 2.97/0.99  
% 2.97/0.99  fof(f53,plain,(
% 2.97/0.99    ( ! [X2,X0,X1] : (X1 = X2 | m1_subset_1(sK0(X0,X1,X2),X0) | ~m1_subset_1(X2,k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 2.97/0.99    inference(cnf_transformation,[],[f36])).
% 2.97/0.99  
% 2.97/0.99  fof(f67,plain,(
% 2.97/0.99    ( ! [X0,X1] : (v13_waybel_0(X1,X0) | ~r2_hidden(sK2(X0,X1),X1) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_orders_2(X0)) )),
% 2.97/0.99    inference(cnf_transformation,[],[f42])).
% 2.97/0.99  
% 2.97/0.99  fof(f64,plain,(
% 2.97/0.99    ( ! [X0,X1] : (v13_waybel_0(X1,X0) | m1_subset_1(sK2(X0,X1),u1_struct_0(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_orders_2(X0)) )),
% 2.97/0.99    inference(cnf_transformation,[],[f42])).
% 2.97/0.99  
% 2.97/0.99  fof(f77,plain,(
% 2.97/0.99    ~r2_hidden(k3_yellow_0(sK3),sK4) | v1_subset_1(sK4,u1_struct_0(sK3))),
% 2.97/0.99    inference(cnf_transformation,[],[f48])).
% 2.97/0.99  
% 2.97/0.99  fof(f75,plain,(
% 2.97/0.99    v13_waybel_0(sK4,sK3)),
% 2.97/0.99    inference(cnf_transformation,[],[f48])).
% 2.97/0.99  
% 2.97/0.99  cnf(c_3,plain,
% 2.97/0.99      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
% 2.97/0.99      | ~ r2_hidden(X2,X0)
% 2.97/0.99      | r2_hidden(X2,X1) ),
% 2.97/0.99      inference(cnf_transformation,[],[f52]) ).
% 2.97/0.99  
% 2.97/0.99  cnf(c_8,plain,
% 2.97/0.99      ( m1_subset_1(X0,k1_zfmisc_1(X1)) | ~ r1_tarski(X0,X1) ),
% 2.97/0.99      inference(cnf_transformation,[],[f58]) ).
% 2.97/0.99  
% 2.97/0.99  cnf(c_223,plain,
% 2.97/0.99      ( ~ r1_tarski(X0,X1) | m1_subset_1(X0,k1_zfmisc_1(X1)) ),
% 2.97/0.99      inference(prop_impl,[status(thm)],[c_8]) ).
% 2.97/0.99  
% 2.97/0.99  cnf(c_224,plain,
% 2.97/0.99      ( m1_subset_1(X0,k1_zfmisc_1(X1)) | ~ r1_tarski(X0,X1) ),
% 2.97/0.99      inference(renaming,[status(thm)],[c_223]) ).
% 2.97/0.99  
% 2.97/0.99  cnf(c_287,plain,
% 2.97/0.99      ( ~ r2_hidden(X0,X1) | r2_hidden(X0,X2) | ~ r1_tarski(X1,X2) ),
% 2.97/0.99      inference(bin_hyper_res,[status(thm)],[c_3,c_224]) ).
% 2.97/0.99  
% 2.97/0.99  cnf(c_1618,plain,
% 2.97/0.99      ( r2_hidden(sK2(sK3,X0),X1)
% 2.97/0.99      | ~ r2_hidden(sK2(sK3,X0),sK4)
% 2.97/0.99      | ~ r1_tarski(sK4,X1) ),
% 2.97/0.99      inference(instantiation,[status(thm)],[c_287]) ).
% 2.97/0.99  
% 2.97/0.99  cnf(c_1774,plain,
% 2.97/0.99      ( r2_hidden(sK2(sK3,X0),u1_struct_0(sK3))
% 2.97/0.99      | ~ r2_hidden(sK2(sK3,X0),sK4)
% 2.97/0.99      | ~ r1_tarski(sK4,u1_struct_0(sK3)) ),
% 2.97/0.99      inference(instantiation,[status(thm)],[c_1618]) ).
% 2.97/0.99  
% 2.97/0.99  cnf(c_14037,plain,
% 2.97/0.99      ( r2_hidden(sK2(sK3,u1_struct_0(X0)),u1_struct_0(sK3))
% 2.97/0.99      | ~ r2_hidden(sK2(sK3,u1_struct_0(X0)),sK4)
% 2.97/0.99      | ~ r1_tarski(sK4,u1_struct_0(sK3)) ),
% 2.97/0.99      inference(instantiation,[status(thm)],[c_1774]) ).
% 2.97/0.99  
% 2.97/0.99  cnf(c_14044,plain,
% 2.97/0.99      ( r2_hidden(sK2(sK3,u1_struct_0(sK3)),u1_struct_0(sK3))
% 2.97/0.99      | ~ r2_hidden(sK2(sK3,u1_struct_0(sK3)),sK4)
% 2.97/0.99      | ~ r1_tarski(sK4,u1_struct_0(sK3)) ),
% 2.97/0.99      inference(instantiation,[status(thm)],[c_14037]) ).
% 2.97/0.99  
% 2.97/0.99  cnf(c_18,plain,
% 2.97/0.99      ( ~ r1_orders_2(X0,X1,X2)
% 2.97/0.99      | ~ v13_waybel_0(X3,X0)
% 2.97/0.99      | ~ m1_subset_1(X2,u1_struct_0(X0))
% 2.97/0.99      | ~ m1_subset_1(X1,u1_struct_0(X0))
% 2.97/0.99      | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))
% 2.97/0.99      | ~ r2_hidden(X1,X3)
% 2.97/0.99      | r2_hidden(X2,X3)
% 2.97/0.99      | ~ l1_orders_2(X0) ),
% 2.97/0.99      inference(cnf_transformation,[],[f62]) ).
% 2.97/0.99  
% 2.97/0.99  cnf(c_12,plain,
% 2.97/0.99      ( r1_orders_2(X0,k3_yellow_0(X0),X1)
% 2.97/0.99      | ~ m1_subset_1(X1,u1_struct_0(X0))
% 2.97/0.99      | v2_struct_0(X0)
% 2.97/0.99      | ~ v5_orders_2(X0)
% 2.97/0.99      | ~ v1_yellow_0(X0)
% 2.97/0.99      | ~ l1_orders_2(X0) ),
% 2.97/0.99      inference(cnf_transformation,[],[f61]) ).
% 2.97/0.99  
% 2.97/0.99  cnf(c_27,negated_conjecture,
% 2.97/0.99      ( v1_yellow_0(sK3) ),
% 2.97/0.99      inference(cnf_transformation,[],[f72]) ).
% 2.97/0.99  
% 2.97/0.99  cnf(c_414,plain,
% 2.97/0.99      ( r1_orders_2(X0,k3_yellow_0(X0),X1)
% 2.97/0.99      | ~ m1_subset_1(X1,u1_struct_0(X0))
% 2.97/0.99      | v2_struct_0(X0)
% 2.97/0.99      | ~ v5_orders_2(X0)
% 2.97/0.99      | ~ l1_orders_2(X0)
% 2.97/0.99      | sK3 != X0 ),
% 2.97/0.99      inference(resolution_lifted,[status(thm)],[c_12,c_27]) ).
% 2.97/0.99  
% 2.97/0.99  cnf(c_415,plain,
% 2.97/0.99      ( r1_orders_2(sK3,k3_yellow_0(sK3),X0)
% 2.97/0.99      | ~ m1_subset_1(X0,u1_struct_0(sK3))
% 2.97/0.99      | v2_struct_0(sK3)
% 2.97/0.99      | ~ v5_orders_2(sK3)
% 2.97/0.99      | ~ l1_orders_2(sK3) ),
% 2.97/0.99      inference(unflattening,[status(thm)],[c_414]) ).
% 2.97/0.99  
% 2.97/0.99  cnf(c_29,negated_conjecture,
% 2.97/0.99      ( ~ v2_struct_0(sK3) ),
% 2.97/0.99      inference(cnf_transformation,[],[f70]) ).
% 2.97/0.99  
% 2.97/0.99  cnf(c_28,negated_conjecture,
% 2.97/0.99      ( v5_orders_2(sK3) ),
% 2.97/0.99      inference(cnf_transformation,[],[f71]) ).
% 2.97/0.99  
% 2.97/0.99  cnf(c_26,negated_conjecture,
% 2.97/0.99      ( l1_orders_2(sK3) ),
% 2.97/0.99      inference(cnf_transformation,[],[f73]) ).
% 2.97/0.99  
% 2.97/0.99  cnf(c_419,plain,
% 2.97/0.99      ( ~ m1_subset_1(X0,u1_struct_0(sK3))
% 2.97/0.99      | r1_orders_2(sK3,k3_yellow_0(sK3),X0) ),
% 2.97/0.99      inference(global_propositional_subsumption,
% 2.97/0.99                [status(thm)],
% 2.97/0.99                [c_415,c_29,c_28,c_26]) ).
% 2.97/0.99  
% 2.97/0.99  cnf(c_420,plain,
% 2.97/0.99      ( r1_orders_2(sK3,k3_yellow_0(sK3),X0)
% 2.97/0.99      | ~ m1_subset_1(X0,u1_struct_0(sK3)) ),
% 2.97/0.99      inference(renaming,[status(thm)],[c_419]) ).
% 2.97/0.99  
% 2.97/0.99  cnf(c_502,plain,
% 2.97/0.99      ( ~ v13_waybel_0(X0,X1)
% 2.97/0.99      | ~ m1_subset_1(X2,u1_struct_0(X1))
% 2.97/0.99      | ~ m1_subset_1(X3,u1_struct_0(X1))
% 2.97/0.99      | ~ m1_subset_1(X4,u1_struct_0(sK3))
% 2.97/0.99      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 2.97/0.99      | ~ r2_hidden(X2,X0)
% 2.97/0.99      | r2_hidden(X3,X0)
% 2.97/0.99      | ~ l1_orders_2(X1)
% 2.97/0.99      | X4 != X3
% 2.97/0.99      | k3_yellow_0(sK3) != X2
% 2.97/0.99      | sK3 != X1 ),
% 2.97/0.99      inference(resolution_lifted,[status(thm)],[c_18,c_420]) ).
% 2.97/0.99  
% 2.97/0.99  cnf(c_503,plain,
% 2.97/0.99      ( ~ v13_waybel_0(X0,sK3)
% 2.97/0.99      | ~ m1_subset_1(X1,u1_struct_0(sK3))
% 2.97/0.99      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK3)))
% 2.97/0.99      | ~ m1_subset_1(k3_yellow_0(sK3),u1_struct_0(sK3))
% 2.97/0.99      | r2_hidden(X1,X0)
% 2.97/0.99      | ~ r2_hidden(k3_yellow_0(sK3),X0)
% 2.97/0.99      | ~ l1_orders_2(sK3) ),
% 2.97/0.99      inference(unflattening,[status(thm)],[c_502]) ).
% 2.97/0.99  
% 2.97/0.99  cnf(c_11,plain,
% 2.97/0.99      ( m1_subset_1(k3_yellow_0(X0),u1_struct_0(X0))
% 2.97/0.99      | ~ l1_orders_2(X0) ),
% 2.97/0.99      inference(cnf_transformation,[],[f60]) ).
% 2.97/0.99  
% 2.97/0.99  cnf(c_65,plain,
% 2.97/0.99      ( m1_subset_1(k3_yellow_0(sK3),u1_struct_0(sK3))
% 2.97/0.99      | ~ l1_orders_2(sK3) ),
% 2.97/0.99      inference(instantiation,[status(thm)],[c_11]) ).
% 2.97/0.99  
% 2.97/0.99  cnf(c_507,plain,
% 2.97/0.99      ( ~ r2_hidden(k3_yellow_0(sK3),X0)
% 2.97/0.99      | r2_hidden(X1,X0)
% 2.97/0.99      | ~ v13_waybel_0(X0,sK3)
% 2.97/0.99      | ~ m1_subset_1(X1,u1_struct_0(sK3))
% 2.97/0.99      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK3))) ),
% 2.97/0.99      inference(global_propositional_subsumption,
% 2.97/0.99                [status(thm)],
% 2.97/0.99                [c_503,c_26,c_65]) ).
% 2.97/0.99  
% 2.97/0.99  cnf(c_508,plain,
% 2.97/0.99      ( ~ v13_waybel_0(X0,sK3)
% 2.97/0.99      | ~ m1_subset_1(X1,u1_struct_0(sK3))
% 2.97/0.99      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK3)))
% 2.97/0.99      | r2_hidden(X1,X0)
% 2.97/0.99      | ~ r2_hidden(k3_yellow_0(sK3),X0) ),
% 2.97/0.99      inference(renaming,[status(thm)],[c_507]) ).
% 2.97/0.99  
% 2.97/0.99  cnf(c_1564,plain,
% 2.97/0.99      ( ~ v13_waybel_0(sK4,sK3)
% 2.97/0.99      | ~ m1_subset_1(X0,u1_struct_0(sK3))
% 2.97/0.99      | ~ m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(sK3)))
% 2.97/0.99      | r2_hidden(X0,sK4)
% 2.97/0.99      | ~ r2_hidden(k3_yellow_0(sK3),sK4) ),
% 2.97/0.99      inference(instantiation,[status(thm)],[c_508]) ).
% 2.97/0.99  
% 2.97/0.99  cnf(c_8975,plain,
% 2.97/0.99      ( ~ v13_waybel_0(sK4,sK3)
% 2.97/0.99      | ~ m1_subset_1(sK2(sK3,u1_struct_0(X0)),u1_struct_0(sK3))
% 2.97/0.99      | ~ m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(sK3)))
% 2.97/0.99      | r2_hidden(sK2(sK3,u1_struct_0(X0)),sK4)
% 2.97/0.99      | ~ r2_hidden(k3_yellow_0(sK3),sK4) ),
% 2.97/0.99      inference(instantiation,[status(thm)],[c_1564]) ).
% 2.97/0.99  
% 2.97/0.99  cnf(c_8977,plain,
% 2.97/0.99      ( ~ v13_waybel_0(sK4,sK3)
% 2.97/0.99      | ~ m1_subset_1(sK2(sK3,u1_struct_0(sK3)),u1_struct_0(sK3))
% 2.97/0.99      | ~ m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(sK3)))
% 2.97/0.99      | r2_hidden(sK2(sK3,u1_struct_0(sK3)),sK4)
% 2.97/0.99      | ~ r2_hidden(k3_yellow_0(sK3),sK4) ),
% 2.97/0.99      inference(instantiation,[status(thm)],[c_8975]) ).
% 2.97/0.99  
% 2.97/0.99  cnf(c_19,plain,
% 2.97/0.99      ( v1_subset_1(X0,X1)
% 2.97/0.99      | ~ m1_subset_1(X0,k1_zfmisc_1(X1))
% 2.97/0.99      | X0 = X1 ),
% 2.97/0.99      inference(cnf_transformation,[],[f69]) ).
% 2.97/0.99  
% 2.97/0.99  cnf(c_293,plain,
% 2.97/0.99      ( v1_subset_1(X0,X1) | ~ r1_tarski(X0,X1) | X0 = X1 ),
% 2.97/0.99      inference(bin_hyper_res,[status(thm)],[c_19,c_224]) ).
% 2.97/0.99  
% 2.97/0.99  cnf(c_21,negated_conjecture,
% 2.97/0.99      ( ~ v1_subset_1(sK4,u1_struct_0(sK3))
% 2.97/0.99      | r2_hidden(k3_yellow_0(sK3),sK4) ),
% 2.97/0.99      inference(cnf_transformation,[],[f78]) ).
% 2.97/0.99  
% 2.97/0.99  cnf(c_227,plain,
% 2.97/0.99      ( ~ v1_subset_1(sK4,u1_struct_0(sK3))
% 2.97/0.99      | r2_hidden(k3_yellow_0(sK3),sK4) ),
% 2.97/0.99      inference(prop_impl,[status(thm)],[c_21]) ).
% 2.97/0.99  
% 2.97/0.99  cnf(c_438,plain,
% 2.97/0.99      ( r2_hidden(k3_yellow_0(sK3),sK4)
% 2.97/0.99      | ~ r1_tarski(X0,X1)
% 2.97/0.99      | X1 = X0
% 2.97/0.99      | u1_struct_0(sK3) != X1
% 2.97/0.99      | sK4 != X0 ),
% 2.97/0.99      inference(resolution_lifted,[status(thm)],[c_293,c_227]) ).
% 2.97/0.99  
% 2.97/0.99  cnf(c_439,plain,
% 2.97/0.99      ( r2_hidden(k3_yellow_0(sK3),sK4)
% 2.97/0.99      | ~ r1_tarski(sK4,u1_struct_0(sK3))
% 2.97/0.99      | u1_struct_0(sK3) = sK4 ),
% 2.97/0.99      inference(unflattening,[status(thm)],[c_438]) ).
% 2.97/0.99  
% 2.97/0.99  cnf(c_1375,plain,
% 2.97/0.99      ( u1_struct_0(sK3) = sK4
% 2.97/0.99      | r2_hidden(k3_yellow_0(sK3),sK4) = iProver_top
% 2.97/0.99      | r1_tarski(sK4,u1_struct_0(sK3)) != iProver_top ),
% 2.97/0.99      inference(predicate_to_equality,[status(thm)],[c_439]) ).
% 2.97/0.99  
% 2.97/0.99  cnf(c_33,plain,
% 2.97/0.99      ( l1_orders_2(sK3) = iProver_top ),
% 2.97/0.99      inference(predicate_to_equality,[status(thm)],[c_26]) ).
% 2.97/0.99  
% 2.97/0.99  cnf(c_23,negated_conjecture,
% 2.97/0.99      ( m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(sK3))) ),
% 2.97/0.99      inference(cnf_transformation,[],[f76]) ).
% 2.97/0.99  
% 2.97/0.99  cnf(c_36,plain,
% 2.97/0.99      ( m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(sK3))) = iProver_top ),
% 2.97/0.99      inference(predicate_to_equality,[status(thm)],[c_23]) ).
% 2.97/0.99  
% 2.97/0.99  cnf(c_20,plain,
% 2.97/0.99      ( ~ v1_subset_1(X0,X0) | ~ m1_subset_1(X0,k1_zfmisc_1(X0)) ),
% 2.97/0.99      inference(cnf_transformation,[],[f81]) ).
% 2.97/0.99  
% 2.97/0.99  cnf(c_40,plain,
% 2.97/0.99      ( ~ v1_subset_1(sK3,sK3) | ~ m1_subset_1(sK3,k1_zfmisc_1(sK3)) ),
% 2.97/0.99      inference(instantiation,[status(thm)],[c_20]) ).
% 2.97/0.99  
% 2.97/0.99  cnf(c_43,plain,
% 2.97/0.99      ( v1_subset_1(sK3,sK3)
% 2.97/0.99      | ~ m1_subset_1(sK3,k1_zfmisc_1(sK3))
% 2.97/0.99      | sK3 = sK3 ),
% 2.97/0.99      inference(instantiation,[status(thm)],[c_19]) ).
% 2.97/0.99  
% 2.97/0.99  cnf(c_64,plain,
% 2.97/0.99      ( m1_subset_1(k3_yellow_0(X0),u1_struct_0(X0)) = iProver_top
% 2.97/0.99      | l1_orders_2(X0) != iProver_top ),
% 2.97/0.99      inference(predicate_to_equality,[status(thm)],[c_11]) ).
% 2.97/0.99  
% 2.97/0.99  cnf(c_66,plain,
% 2.97/0.99      ( m1_subset_1(k3_yellow_0(sK3),u1_struct_0(sK3)) = iProver_top
% 2.97/0.99      | l1_orders_2(sK3) != iProver_top ),
% 2.97/0.99      inference(instantiation,[status(thm)],[c_64]) ).
% 2.97/0.99  
% 2.97/0.99  cnf(c_74,plain,
% 2.97/0.99      ( m1_subset_1(sK3,k1_zfmisc_1(sK3)) | ~ r1_tarski(sK3,sK3) ),
% 2.97/0.99      inference(instantiation,[status(thm)],[c_8]) ).
% 2.97/0.99  
% 2.97/0.99  cnf(c_2,plain,
% 2.97/0.99      ( r1_tarski(X0,X0) ),
% 2.97/0.99      inference(cnf_transformation,[],[f80]) ).
% 2.97/0.99  
% 2.97/0.99  cnf(c_90,plain,
% 2.97/0.99      ( r1_tarski(sK3,sK3) ),
% 2.97/0.99      inference(instantiation,[status(thm)],[c_2]) ).
% 2.97/0.99  
% 2.97/0.99  cnf(c_440,plain,
% 2.97/0.99      ( u1_struct_0(sK3) = sK4
% 2.97/0.99      | r2_hidden(k3_yellow_0(sK3),sK4) = iProver_top
% 2.97/0.99      | r1_tarski(sK4,u1_struct_0(sK3)) != iProver_top ),
% 2.97/0.99      inference(predicate_to_equality,[status(thm)],[c_439]) ).
% 2.97/0.99  
% 2.97/0.99  cnf(c_859,plain,
% 2.97/0.99      ( X0 != X1 | k3_yellow_0(X0) = k3_yellow_0(X1) ),
% 2.97/0.99      theory(equality) ).
% 2.97/0.99  
% 2.97/0.99  cnf(c_868,plain,
% 2.97/0.99      ( k3_yellow_0(sK3) = k3_yellow_0(sK3) | sK3 != sK3 ),
% 2.97/0.99      inference(instantiation,[status(thm)],[c_859]) ).
% 2.97/0.99  
% 2.97/0.99  cnf(c_9,plain,
% 2.97/0.99      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1)) | r1_tarski(X0,X1) ),
% 2.97/0.99      inference(cnf_transformation,[],[f57]) ).
% 2.97/0.99  
% 2.97/0.99  cnf(c_1578,plain,
% 2.97/0.99      ( ~ m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(sK3)))
% 2.97/0.99      | r1_tarski(sK4,u1_struct_0(sK3)) ),
% 2.97/0.99      inference(instantiation,[status(thm)],[c_9]) ).
% 2.97/0.99  
% 2.97/0.99  cnf(c_1579,plain,
% 2.97/0.99      ( m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(sK3))) != iProver_top
% 2.97/0.99      | r1_tarski(sK4,u1_struct_0(sK3)) = iProver_top ),
% 2.97/0.99      inference(predicate_to_equality,[status(thm)],[c_1578]) ).
% 2.97/0.99  
% 2.97/0.99  cnf(c_853,plain,( X0 = X0 ),theory(equality) ).
% 2.97/0.99  
% 2.97/0.99  cnf(c_1655,plain,
% 2.97/0.99      ( sK4 = sK4 ),
% 2.97/0.99      inference(instantiation,[status(thm)],[c_853]) ).
% 2.97/0.99  
% 2.97/0.99  cnf(c_854,plain,( X0 != X1 | X2 != X1 | X2 = X0 ),theory(equality) ).
% 2.97/0.99  
% 2.97/0.99  cnf(c_1814,plain,
% 2.97/0.99      ( X0 != X1 | sK4 != X1 | sK4 = X0 ),
% 2.97/0.99      inference(instantiation,[status(thm)],[c_854]) ).
% 2.97/0.99  
% 2.97/0.99  cnf(c_2338,plain,
% 2.97/0.99      ( X0 != sK4 | sK4 = X0 | sK4 != sK4 ),
% 2.97/0.99      inference(instantiation,[status(thm)],[c_1814]) ).
% 2.97/0.99  
% 2.97/0.99  cnf(c_2566,plain,
% 2.97/0.99      ( u1_struct_0(sK3) != sK4 | sK4 = u1_struct_0(sK3) | sK4 != sK4 ),
% 2.97/0.99      inference(instantiation,[status(thm)],[c_2338]) ).
% 2.97/0.99  
% 2.97/0.99  cnf(c_858,plain,
% 2.97/0.99      ( ~ m1_subset_1(X0,X1) | m1_subset_1(X2,X3) | X2 != X0 | X3 != X1 ),
% 2.97/0.99      theory(equality) ).
% 2.97/0.99  
% 2.97/0.99  cnf(c_1592,plain,
% 2.97/0.99      ( m1_subset_1(X0,X1)
% 2.97/0.99      | ~ m1_subset_1(k3_yellow_0(sK3),u1_struct_0(sK3))
% 2.97/0.99      | X1 != u1_struct_0(sK3)
% 2.97/0.99      | X0 != k3_yellow_0(sK3) ),
% 2.97/0.99      inference(instantiation,[status(thm)],[c_858]) ).
% 2.97/0.99  
% 2.97/0.99  cnf(c_3175,plain,
% 2.97/0.99      ( m1_subset_1(X0,sK4)
% 2.97/0.99      | ~ m1_subset_1(k3_yellow_0(sK3),u1_struct_0(sK3))
% 2.97/0.99      | X0 != k3_yellow_0(sK3)
% 2.97/0.99      | sK4 != u1_struct_0(sK3) ),
% 2.97/0.99      inference(instantiation,[status(thm)],[c_1592]) ).
% 2.97/0.99  
% 2.97/0.99  cnf(c_3915,plain,
% 2.97/0.99      ( ~ m1_subset_1(k3_yellow_0(sK3),u1_struct_0(sK3))
% 2.97/0.99      | m1_subset_1(k3_yellow_0(sK3),sK4)
% 2.97/0.99      | k3_yellow_0(sK3) != k3_yellow_0(sK3)
% 2.97/0.99      | sK4 != u1_struct_0(sK3) ),
% 2.97/0.99      inference(instantiation,[status(thm)],[c_3175]) ).
% 2.97/0.99  
% 2.97/0.99  cnf(c_3916,plain,
% 2.97/0.99      ( k3_yellow_0(sK3) != k3_yellow_0(sK3)
% 2.97/0.99      | sK4 != u1_struct_0(sK3)
% 2.97/0.99      | m1_subset_1(k3_yellow_0(sK3),u1_struct_0(sK3)) != iProver_top
% 2.97/0.99      | m1_subset_1(k3_yellow_0(sK3),sK4) = iProver_top ),
% 2.97/0.99      inference(predicate_to_equality,[status(thm)],[c_3915]) ).
% 2.97/0.99  
% 2.97/0.99  cnf(c_7,plain,
% 2.97/0.99      ( ~ m1_subset_1(X0,X1) | r2_hidden(X0,X1) | v1_xboole_0(X1) ),
% 2.97/0.99      inference(cnf_transformation,[],[f56]) ).
% 2.97/0.99  
% 2.97/0.99  cnf(c_25,negated_conjecture,
% 2.97/0.99      ( ~ v1_xboole_0(sK4) ),
% 2.97/0.99      inference(cnf_transformation,[],[f74]) ).
% 2.97/0.99  
% 2.97/0.99  cnf(c_399,plain,
% 2.97/0.99      ( ~ m1_subset_1(X0,X1) | r2_hidden(X0,X1) | sK4 != X1 ),
% 2.97/0.99      inference(resolution_lifted,[status(thm)],[c_7,c_25]) ).
% 2.97/0.99  
% 2.97/0.99  cnf(c_400,plain,
% 2.97/0.99      ( ~ m1_subset_1(X0,sK4) | r2_hidden(X0,sK4) ),
% 2.97/0.99      inference(unflattening,[status(thm)],[c_399]) ).
% 2.97/0.99  
% 2.97/0.99  cnf(c_6078,plain,
% 2.97/0.99      ( ~ m1_subset_1(k3_yellow_0(sK3),sK4)
% 2.97/0.99      | r2_hidden(k3_yellow_0(sK3),sK4) ),
% 2.97/0.99      inference(instantiation,[status(thm)],[c_400]) ).
% 2.97/0.99  
% 2.97/0.99  cnf(c_6079,plain,
% 2.97/0.99      ( m1_subset_1(k3_yellow_0(sK3),sK4) != iProver_top
% 2.97/0.99      | r2_hidden(k3_yellow_0(sK3),sK4) = iProver_top ),
% 2.97/0.99      inference(predicate_to_equality,[status(thm)],[c_6078]) ).
% 2.97/0.99  
% 2.97/0.99  cnf(c_6141,plain,
% 2.97/0.99      ( r2_hidden(k3_yellow_0(sK3),sK4) = iProver_top ),
% 2.97/0.99      inference(global_propositional_subsumption,
% 2.97/0.99                [status(thm)],
% 2.97/0.99                [c_1375,c_33,c_36,c_40,c_43,c_66,c_74,c_90,c_440,c_868,
% 2.97/0.99                 c_1579,c_1655,c_2566,c_3916,c_6079]) ).
% 2.97/0.99  
% 2.97/0.99  cnf(c_6045,plain,
% 2.97/0.99      ( ~ v13_waybel_0(sK4,sK3)
% 2.97/0.99      | ~ m1_subset_1(sK0(u1_struct_0(sK3),sK4,u1_struct_0(sK3)),u1_struct_0(sK3))
% 2.97/0.99      | ~ m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(sK3)))
% 2.97/0.99      | r2_hidden(sK0(u1_struct_0(sK3),sK4,u1_struct_0(sK3)),sK4)
% 2.97/0.99      | ~ r2_hidden(k3_yellow_0(sK3),sK4) ),
% 2.97/0.99      inference(instantiation,[status(thm)],[c_1564]) ).
% 2.97/0.99  
% 2.97/0.99  cnf(c_3274,plain,
% 2.97/0.99      ( ~ v13_waybel_0(u1_struct_0(X0),sK3)
% 2.97/0.99      | ~ m1_subset_1(X1,u1_struct_0(sK3))
% 2.97/0.99      | ~ m1_subset_1(u1_struct_0(X0),k1_zfmisc_1(u1_struct_0(sK3)))
% 2.97/0.99      | r2_hidden(X1,u1_struct_0(X0))
% 2.97/0.99      | ~ r2_hidden(k3_yellow_0(sK3),u1_struct_0(X0)) ),
% 2.97/0.99      inference(instantiation,[status(thm)],[c_508]) ).
% 2.97/0.99  
% 2.97/0.99  cnf(c_6040,plain,
% 2.97/0.99      ( ~ v13_waybel_0(u1_struct_0(X0),sK3)
% 2.97/0.99      | ~ m1_subset_1(sK0(u1_struct_0(sK3),sK4,u1_struct_0(sK3)),u1_struct_0(sK3))
% 2.97/0.99      | ~ m1_subset_1(u1_struct_0(X0),k1_zfmisc_1(u1_struct_0(sK3)))
% 2.97/0.99      | r2_hidden(sK0(u1_struct_0(sK3),sK4,u1_struct_0(sK3)),u1_struct_0(X0))
% 2.97/0.99      | ~ r2_hidden(k3_yellow_0(sK3),u1_struct_0(X0)) ),
% 2.97/0.99      inference(instantiation,[status(thm)],[c_3274]) ).
% 2.97/0.99  
% 2.97/0.99  cnf(c_6042,plain,
% 2.97/0.99      ( ~ v13_waybel_0(u1_struct_0(sK3),sK3)
% 2.97/0.99      | ~ m1_subset_1(sK0(u1_struct_0(sK3),sK4,u1_struct_0(sK3)),u1_struct_0(sK3))
% 2.97/0.99      | ~ m1_subset_1(u1_struct_0(sK3),k1_zfmisc_1(u1_struct_0(sK3)))
% 2.97/0.99      | r2_hidden(sK0(u1_struct_0(sK3),sK4,u1_struct_0(sK3)),u1_struct_0(sK3))
% 2.97/0.99      | ~ r2_hidden(k3_yellow_0(sK3),u1_struct_0(sK3)) ),
% 2.97/0.99      inference(instantiation,[status(thm)],[c_6040]) ).
% 2.97/0.99  
% 2.97/0.99  cnf(c_4,plain,
% 2.97/0.99      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
% 2.97/0.99      | ~ m1_subset_1(X2,k1_zfmisc_1(X1))
% 2.97/0.99      | ~ r2_hidden(sK0(X1,X0,X2),X2)
% 2.97/1.00      | ~ r2_hidden(sK0(X1,X0,X2),X0)
% 2.97/1.00      | X2 = X0 ),
% 2.97/1.00      inference(cnf_transformation,[],[f55]) ).
% 2.97/1.00  
% 2.97/1.00  cnf(c_288,plain,
% 2.97/1.00      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
% 2.97/1.00      | ~ r2_hidden(sK0(X1,X2,X0),X0)
% 2.97/1.00      | ~ r2_hidden(sK0(X1,X2,X0),X2)
% 2.97/1.00      | ~ r1_tarski(X2,X1)
% 2.97/1.00      | X0 = X2 ),
% 2.97/1.00      inference(bin_hyper_res,[status(thm)],[c_4,c_224]) ).
% 2.97/1.00  
% 2.97/1.00  cnf(c_725,plain,
% 2.97/1.00      ( ~ r1_tarski(X0,X1) | m1_subset_1(X0,k1_zfmisc_1(X1)) ),
% 2.97/1.00      inference(prop_impl,[status(thm)],[c_8]) ).
% 2.97/1.00  
% 2.97/1.00  cnf(c_726,plain,
% 2.97/1.00      ( m1_subset_1(X0,k1_zfmisc_1(X1)) | ~ r1_tarski(X0,X1) ),
% 2.97/1.00      inference(renaming,[status(thm)],[c_725]) ).
% 2.97/1.00  
% 2.97/1.00  cnf(c_774,plain,
% 2.97/1.00      ( ~ r2_hidden(sK0(X0,X1,X2),X2)
% 2.97/1.00      | ~ r2_hidden(sK0(X0,X1,X2),X1)
% 2.97/1.00      | ~ r1_tarski(X2,X0)
% 2.97/1.00      | ~ r1_tarski(X1,X0)
% 2.97/1.00      | X2 = X1 ),
% 2.97/1.00      inference(bin_hyper_res,[status(thm)],[c_288,c_726]) ).
% 2.97/1.00  
% 2.97/1.00  cnf(c_1638,plain,
% 2.97/1.00      ( ~ r2_hidden(sK0(X0,sK4,X1),X1)
% 2.97/1.00      | ~ r2_hidden(sK0(X0,sK4,X1),sK4)
% 2.97/1.00      | ~ r1_tarski(X1,X0)
% 2.97/1.00      | ~ r1_tarski(sK4,X0)
% 2.97/1.00      | X1 = sK4 ),
% 2.97/1.00      inference(instantiation,[status(thm)],[c_774]) ).
% 2.97/1.00  
% 2.97/1.00  cnf(c_1897,plain,
% 2.97/1.00      ( ~ r2_hidden(sK0(u1_struct_0(sK3),sK4,X0),X0)
% 2.97/1.00      | ~ r2_hidden(sK0(u1_struct_0(sK3),sK4,X0),sK4)
% 2.97/1.00      | ~ r1_tarski(X0,u1_struct_0(sK3))
% 2.97/1.00      | ~ r1_tarski(sK4,u1_struct_0(sK3))
% 2.97/1.00      | X0 = sK4 ),
% 2.97/1.00      inference(instantiation,[status(thm)],[c_1638]) ).
% 2.97/1.00  
% 2.97/1.00  cnf(c_2398,plain,
% 2.97/1.00      ( ~ r2_hidden(sK0(u1_struct_0(sK3),sK4,u1_struct_0(sK3)),u1_struct_0(sK3))
% 2.97/1.00      | ~ r2_hidden(sK0(u1_struct_0(sK3),sK4,u1_struct_0(sK3)),sK4)
% 2.97/1.00      | ~ r1_tarski(u1_struct_0(sK3),u1_struct_0(sK3))
% 2.97/1.00      | ~ r1_tarski(sK4,u1_struct_0(sK3))
% 2.97/1.00      | u1_struct_0(sK3) = sK4 ),
% 2.97/1.00      inference(instantiation,[status(thm)],[c_1897]) ).
% 2.97/1.00  
% 2.97/1.00  cnf(c_6,plain,
% 2.97/1.00      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
% 2.97/1.00      | ~ m1_subset_1(X2,k1_zfmisc_1(X1))
% 2.97/1.00      | m1_subset_1(sK0(X1,X0,X2),X1)
% 2.97/1.00      | X2 = X0 ),
% 2.97/1.00      inference(cnf_transformation,[],[f53]) ).
% 2.97/1.00  
% 2.97/1.00  cnf(c_290,plain,
% 2.97/1.00      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
% 2.97/1.00      | m1_subset_1(sK0(X1,X2,X0),X1)
% 2.97/1.00      | ~ r1_tarski(X2,X1)
% 2.97/1.00      | X0 = X2 ),
% 2.97/1.00      inference(bin_hyper_res,[status(thm)],[c_6,c_224]) ).
% 2.97/1.00  
% 2.97/1.00  cnf(c_776,plain,
% 2.97/1.00      ( m1_subset_1(sK0(X0,X1,X2),X0)
% 2.97/1.00      | ~ r1_tarski(X2,X0)
% 2.97/1.00      | ~ r1_tarski(X1,X0)
% 2.97/1.00      | X2 = X1 ),
% 2.97/1.00      inference(bin_hyper_res,[status(thm)],[c_290,c_726]) ).
% 2.97/1.00  
% 2.97/1.00  cnf(c_1639,plain,
% 2.97/1.00      ( m1_subset_1(sK0(X0,sK4,X1),X0)
% 2.97/1.00      | ~ r1_tarski(X1,X0)
% 2.97/1.00      | ~ r1_tarski(sK4,X0)
% 2.97/1.00      | X1 = sK4 ),
% 2.97/1.00      inference(instantiation,[status(thm)],[c_776]) ).
% 2.97/1.00  
% 2.97/1.00  cnf(c_1838,plain,
% 2.97/1.00      ( m1_subset_1(sK0(u1_struct_0(sK3),sK4,X0),u1_struct_0(sK3))
% 2.97/1.00      | ~ r1_tarski(X0,u1_struct_0(sK3))
% 2.97/1.00      | ~ r1_tarski(sK4,u1_struct_0(sK3))
% 2.97/1.00      | X0 = sK4 ),
% 2.97/1.00      inference(instantiation,[status(thm)],[c_1639]) ).
% 2.97/1.00  
% 2.97/1.00  cnf(c_2327,plain,
% 2.97/1.00      ( m1_subset_1(sK0(u1_struct_0(sK3),sK4,u1_struct_0(sK3)),u1_struct_0(sK3))
% 2.97/1.00      | ~ r1_tarski(u1_struct_0(sK3),u1_struct_0(sK3))
% 2.97/1.00      | ~ r1_tarski(sK4,u1_struct_0(sK3))
% 2.97/1.00      | u1_struct_0(sK3) = sK4 ),
% 2.97/1.00      inference(instantiation,[status(thm)],[c_1838]) ).
% 2.97/1.00  
% 2.97/1.00  cnf(c_1708,plain,
% 2.97/1.00      ( r2_hidden(k3_yellow_0(sK3),X0)
% 2.97/1.00      | ~ r2_hidden(k3_yellow_0(sK3),sK4)
% 2.97/1.00      | ~ r1_tarski(sK4,X0) ),
% 2.97/1.00      inference(instantiation,[status(thm)],[c_287]) ).
% 2.97/1.00  
% 2.97/1.00  cnf(c_2119,plain,
% 2.97/1.00      ( r2_hidden(k3_yellow_0(sK3),u1_struct_0(sK3))
% 2.97/1.00      | ~ r2_hidden(k3_yellow_0(sK3),sK4)
% 2.97/1.00      | ~ r1_tarski(sK4,u1_struct_0(sK3)) ),
% 2.97/1.00      inference(instantiation,[status(thm)],[c_1708]) ).
% 2.97/1.00  
% 2.97/1.00  cnf(c_13,plain,
% 2.97/1.00      ( v13_waybel_0(X0,X1)
% 2.97/1.00      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 2.97/1.00      | ~ r2_hidden(sK2(X1,X0),X0)
% 2.97/1.00      | ~ l1_orders_2(X1) ),
% 2.97/1.00      inference(cnf_transformation,[],[f67]) ).
% 2.97/1.00  
% 2.97/1.00  cnf(c_617,plain,
% 2.97/1.00      ( v13_waybel_0(X0,X1)
% 2.97/1.00      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 2.97/1.00      | ~ r2_hidden(sK2(X1,X0),X0)
% 2.97/1.00      | sK3 != X1 ),
% 2.97/1.00      inference(resolution_lifted,[status(thm)],[c_13,c_26]) ).
% 2.97/1.00  
% 2.97/1.00  cnf(c_618,plain,
% 2.97/1.00      ( v13_waybel_0(X0,sK3)
% 2.97/1.00      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK3)))
% 2.97/1.00      | ~ r2_hidden(sK2(sK3,X0),X0) ),
% 2.97/1.00      inference(unflattening,[status(thm)],[c_617]) ).
% 2.97/1.00  
% 2.97/1.00  cnf(c_1904,plain,
% 2.97/1.00      ( v13_waybel_0(u1_struct_0(sK3),sK3)
% 2.97/1.00      | ~ m1_subset_1(u1_struct_0(sK3),k1_zfmisc_1(u1_struct_0(sK3)))
% 2.97/1.00      | ~ r2_hidden(sK2(sK3,u1_struct_0(sK3)),u1_struct_0(sK3)) ),
% 2.97/1.00      inference(instantiation,[status(thm)],[c_618]) ).
% 2.97/1.00  
% 2.97/1.00  cnf(c_16,plain,
% 2.97/1.00      ( v13_waybel_0(X0,X1)
% 2.97/1.00      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 2.97/1.00      | m1_subset_1(sK2(X1,X0),u1_struct_0(X1))
% 2.97/1.00      | ~ l1_orders_2(X1) ),
% 2.97/1.00      inference(cnf_transformation,[],[f64]) ).
% 2.97/1.00  
% 2.97/1.00  cnf(c_587,plain,
% 2.97/1.00      ( v13_waybel_0(X0,X1)
% 2.97/1.00      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 2.97/1.00      | m1_subset_1(sK2(X1,X0),u1_struct_0(X1))
% 2.97/1.00      | sK3 != X1 ),
% 2.97/1.00      inference(resolution_lifted,[status(thm)],[c_16,c_26]) ).
% 2.97/1.00  
% 2.97/1.00  cnf(c_588,plain,
% 2.97/1.00      ( v13_waybel_0(X0,sK3)
% 2.97/1.00      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK3)))
% 2.97/1.00      | m1_subset_1(sK2(sK3,X0),u1_struct_0(sK3)) ),
% 2.97/1.00      inference(unflattening,[status(thm)],[c_587]) ).
% 2.97/1.00  
% 2.97/1.00  cnf(c_1906,plain,
% 2.97/1.00      ( v13_waybel_0(u1_struct_0(sK3),sK3)
% 2.97/1.00      | m1_subset_1(sK2(sK3,u1_struct_0(sK3)),u1_struct_0(sK3))
% 2.97/1.00      | ~ m1_subset_1(u1_struct_0(sK3),k1_zfmisc_1(u1_struct_0(sK3))) ),
% 2.97/1.00      inference(instantiation,[status(thm)],[c_588]) ).
% 2.97/1.00  
% 2.97/1.00  cnf(c_1664,plain,
% 2.97/1.00      ( r1_tarski(u1_struct_0(sK3),u1_struct_0(sK3)) ),
% 2.97/1.00      inference(instantiation,[status(thm)],[c_2]) ).
% 2.97/1.00  
% 2.97/1.00  cnf(c_1667,plain,
% 2.97/1.00      ( r1_tarski(u1_struct_0(sK3),u1_struct_0(sK3)) = iProver_top ),
% 2.97/1.00      inference(predicate_to_equality,[status(thm)],[c_1664]) ).
% 2.97/1.00  
% 2.97/1.00  cnf(c_1573,plain,
% 2.97/1.00      ( m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK3)))
% 2.97/1.00      | ~ r1_tarski(X0,u1_struct_0(sK3)) ),
% 2.97/1.00      inference(instantiation,[status(thm)],[c_8]) ).
% 2.97/1.00  
% 2.97/1.00  cnf(c_1663,plain,
% 2.97/1.00      ( m1_subset_1(u1_struct_0(sK3),k1_zfmisc_1(u1_struct_0(sK3)))
% 2.97/1.00      | ~ r1_tarski(u1_struct_0(sK3),u1_struct_0(sK3)) ),
% 2.97/1.00      inference(instantiation,[status(thm)],[c_1573]) ).
% 2.97/1.00  
% 2.97/1.00  cnf(c_1665,plain,
% 2.97/1.00      ( m1_subset_1(u1_struct_0(sK3),k1_zfmisc_1(u1_struct_0(sK3))) = iProver_top
% 2.97/1.00      | r1_tarski(u1_struct_0(sK3),u1_struct_0(sK3)) != iProver_top ),
% 2.97/1.00      inference(predicate_to_equality,[status(thm)],[c_1663]) ).
% 2.97/1.00  
% 2.97/1.00  cnf(c_22,negated_conjecture,
% 2.97/1.00      ( v1_subset_1(sK4,u1_struct_0(sK3))
% 2.97/1.00      | ~ r2_hidden(k3_yellow_0(sK3),sK4) ),
% 2.97/1.00      inference(cnf_transformation,[],[f77]) ).
% 2.97/1.00  
% 2.97/1.00  cnf(c_225,plain,
% 2.97/1.00      ( v1_subset_1(sK4,u1_struct_0(sK3))
% 2.97/1.00      | ~ r2_hidden(k3_yellow_0(sK3),sK4) ),
% 2.97/1.00      inference(prop_impl,[status(thm)],[c_22]) ).
% 2.97/1.00  
% 2.97/1.00  cnf(c_451,plain,
% 2.97/1.00      ( ~ m1_subset_1(X0,k1_zfmisc_1(X0))
% 2.97/1.00      | ~ r2_hidden(k3_yellow_0(sK3),sK4)
% 2.97/1.00      | u1_struct_0(sK3) != X0
% 2.97/1.00      | sK4 != X0 ),
% 2.97/1.00      inference(resolution_lifted,[status(thm)],[c_20,c_225]) ).
% 2.97/1.00  
% 2.97/1.00  cnf(c_452,plain,
% 2.97/1.00      ( ~ m1_subset_1(u1_struct_0(sK3),k1_zfmisc_1(u1_struct_0(sK3)))
% 2.97/1.00      | ~ r2_hidden(k3_yellow_0(sK3),sK4)
% 2.97/1.00      | sK4 != u1_struct_0(sK3) ),
% 2.97/1.00      inference(unflattening,[status(thm)],[c_451]) ).
% 2.97/1.00  
% 2.97/1.00  cnf(c_453,plain,
% 2.97/1.00      ( sK4 != u1_struct_0(sK3)
% 2.97/1.00      | m1_subset_1(u1_struct_0(sK3),k1_zfmisc_1(u1_struct_0(sK3))) != iProver_top
% 2.97/1.00      | r2_hidden(k3_yellow_0(sK3),sK4) != iProver_top ),
% 2.97/1.00      inference(predicate_to_equality,[status(thm)],[c_452]) ).
% 2.97/1.00  
% 2.97/1.00  cnf(c_24,negated_conjecture,
% 2.97/1.00      ( v13_waybel_0(sK4,sK3) ),
% 2.97/1.00      inference(cnf_transformation,[],[f75]) ).
% 2.97/1.00  
% 2.97/1.00  cnf(contradiction,plain,
% 2.97/1.00      ( $false ),
% 2.97/1.00      inference(minisat,
% 2.97/1.00                [status(thm)],
% 2.97/1.00                [c_14044,c_8977,c_6141,c_6045,c_6042,c_2566,c_2398,
% 2.97/1.00                 c_2327,c_2119,c_1904,c_1906,c_1667,c_1664,c_1665,c_1663,
% 2.97/1.00                 c_1655,c_1578,c_453,c_439,c_23,c_24]) ).
% 2.97/1.00  
% 2.97/1.00  
% 2.97/1.00  % SZS output end CNFRefutation for theBenchmark.p
% 2.97/1.00  
% 2.97/1.00  ------                               Statistics
% 2.97/1.00  
% 2.97/1.00  ------ General
% 2.97/1.00  
% 2.97/1.00  abstr_ref_over_cycles:                  0
% 2.97/1.00  abstr_ref_under_cycles:                 0
% 2.97/1.00  gc_basic_clause_elim:                   0
% 2.97/1.00  forced_gc_time:                         0
% 2.97/1.00  parsing_time:                           0.022
% 2.97/1.00  unif_index_cands_time:                  0.
% 2.97/1.00  unif_index_add_time:                    0.
% 2.97/1.00  orderings_time:                         0.
% 2.97/1.00  out_proof_time:                         0.009
% 2.97/1.00  total_time:                             0.391
% 2.97/1.00  num_of_symbols:                         50
% 2.97/1.00  num_of_terms:                           6241
% 2.97/1.00  
% 2.97/1.00  ------ Preprocessing
% 2.97/1.00  
% 2.97/1.00  num_of_splits:                          0
% 2.97/1.00  num_of_split_atoms:                     0
% 2.97/1.00  num_of_reused_defs:                     0
% 2.97/1.00  num_eq_ax_congr_red:                    20
% 2.97/1.00  num_of_sem_filtered_clauses:            1
% 2.97/1.00  num_of_subtypes:                        0
% 2.97/1.00  monotx_restored_types:                  0
% 2.97/1.00  sat_num_of_epr_types:                   0
% 2.97/1.00  sat_num_of_non_cyclic_types:            0
% 2.97/1.00  sat_guarded_non_collapsed_types:        0
% 2.97/1.00  num_pure_diseq_elim:                    0
% 2.97/1.00  simp_replaced_by:                       0
% 2.97/1.00  res_preprocessed:                       115
% 2.97/1.00  prep_upred:                             0
% 2.97/1.00  prep_unflattend:                        19
% 2.97/1.00  smt_new_axioms:                         0
% 2.97/1.00  pred_elim_cands:                        4
% 2.97/1.00  pred_elim:                              7
% 2.97/1.00  pred_elim_cl:                           8
% 2.97/1.00  pred_elim_cycles:                       9
% 2.97/1.00  merged_defs:                            10
% 2.97/1.00  merged_defs_ncl:                        0
% 2.97/1.00  bin_hyper_res:                          18
% 2.97/1.00  prep_cycles:                            4
% 2.97/1.00  pred_elim_time:                         0.009
% 2.97/1.00  splitting_time:                         0.
% 2.97/1.00  sem_filter_time:                        0.
% 2.97/1.00  monotx_time:                            0.001
% 2.97/1.00  subtype_inf_time:                       0.
% 2.97/1.00  
% 2.97/1.00  ------ Problem properties
% 2.97/1.00  
% 2.97/1.00  clauses:                                21
% 2.97/1.00  conjectures:                            2
% 2.97/1.00  epr:                                    5
% 2.97/1.00  horn:                                   14
% 2.97/1.00  ground:                                 5
% 2.97/1.00  unary:                                  4
% 2.97/1.00  binary:                                 3
% 2.97/1.00  lits:                                   62
% 2.97/1.00  lits_eq:                                6
% 2.97/1.00  fd_pure:                                0
% 2.97/1.00  fd_pseudo:                              0
% 2.97/1.00  fd_cond:                                0
% 2.97/1.00  fd_pseudo_cond:                         4
% 2.97/1.00  ac_symbols:                             0
% 2.97/1.00  
% 2.97/1.00  ------ Propositional Solver
% 2.97/1.00  
% 2.97/1.00  prop_solver_calls:                      31
% 2.97/1.00  prop_fast_solver_calls:                 1260
% 2.97/1.00  smt_solver_calls:                       0
% 2.97/1.00  smt_fast_solver_calls:                  0
% 2.97/1.00  prop_num_of_clauses:                    2841
% 2.97/1.00  prop_preprocess_simplified:             7703
% 2.97/1.00  prop_fo_subsumed:                       18
% 2.97/1.00  prop_solver_time:                       0.
% 2.97/1.00  smt_solver_time:                        0.
% 2.97/1.00  smt_fast_solver_time:                   0.
% 2.97/1.00  prop_fast_solver_time:                  0.
% 2.97/1.00  prop_unsat_core_time:                   0.
% 2.97/1.00  
% 2.97/1.00  ------ QBF
% 2.97/1.00  
% 2.97/1.00  qbf_q_res:                              0
% 2.97/1.00  qbf_num_tautologies:                    0
% 2.97/1.00  qbf_prep_cycles:                        0
% 2.97/1.00  
% 2.97/1.00  ------ BMC1
% 2.97/1.00  
% 2.97/1.00  bmc1_current_bound:                     -1
% 2.97/1.00  bmc1_last_solved_bound:                 -1
% 2.97/1.00  bmc1_unsat_core_size:                   -1
% 2.97/1.00  bmc1_unsat_core_parents_size:           -1
% 2.97/1.00  bmc1_merge_next_fun:                    0
% 2.97/1.00  bmc1_unsat_core_clauses_time:           0.
% 2.97/1.00  
% 2.97/1.00  ------ Instantiation
% 2.97/1.00  
% 2.97/1.00  inst_num_of_clauses:                    692
% 2.97/1.00  inst_num_in_passive:                    140
% 2.97/1.00  inst_num_in_active:                     550
% 2.97/1.00  inst_num_in_unprocessed:                1
% 2.97/1.00  inst_num_of_loops:                      605
% 2.97/1.00  inst_num_of_learning_restarts:          0
% 2.97/1.00  inst_num_moves_active_passive:          49
% 2.97/1.00  inst_lit_activity:                      0
% 2.97/1.00  inst_lit_activity_moves:                0
% 2.97/1.00  inst_num_tautologies:                   0
% 2.97/1.00  inst_num_prop_implied:                  0
% 2.97/1.00  inst_num_existing_simplified:           0
% 2.97/1.00  inst_num_eq_res_simplified:             0
% 2.97/1.00  inst_num_child_elim:                    0
% 2.97/1.00  inst_num_of_dismatching_blockings:      454
% 2.97/1.00  inst_num_of_non_proper_insts:           1800
% 2.97/1.00  inst_num_of_duplicates:                 0
% 2.97/1.00  inst_inst_num_from_inst_to_res:         0
% 2.97/1.00  inst_dismatching_checking_time:         0.
% 2.97/1.00  
% 2.97/1.00  ------ Resolution
% 2.97/1.00  
% 2.97/1.00  res_num_of_clauses:                     0
% 2.97/1.00  res_num_in_passive:                     0
% 2.97/1.00  res_num_in_active:                      0
% 2.97/1.00  res_num_of_loops:                       119
% 2.97/1.00  res_forward_subset_subsumed:            419
% 2.97/1.00  res_backward_subset_subsumed:           2
% 2.97/1.00  res_forward_subsumed:                   0
% 2.97/1.00  res_backward_subsumed:                  0
% 2.97/1.00  res_forward_subsumption_resolution:     2
% 2.97/1.00  res_backward_subsumption_resolution:    0
% 2.97/1.00  res_clause_to_clause_subsumption:       3626
% 2.97/1.00  res_orphan_elimination:                 0
% 2.97/1.00  res_tautology_del:                      189
% 2.97/1.00  res_num_eq_res_simplified:              0
% 2.97/1.00  res_num_sel_changes:                    0
% 2.97/1.00  res_moves_from_active_to_pass:          0
% 2.97/1.00  
% 2.97/1.00  ------ Superposition
% 2.97/1.00  
% 2.97/1.00  sup_time_total:                         0.
% 2.97/1.00  sup_time_generating:                    0.
% 2.97/1.00  sup_time_sim_full:                      0.
% 2.97/1.00  sup_time_sim_immed:                     0.
% 2.97/1.00  
% 2.97/1.00  sup_num_of_clauses:                     369
% 2.97/1.00  sup_num_in_active:                      118
% 2.97/1.00  sup_num_in_passive:                     251
% 2.97/1.00  sup_num_of_loops:                       120
% 2.97/1.00  sup_fw_superposition:                   213
% 2.97/1.00  sup_bw_superposition:                   283
% 2.97/1.00  sup_immediate_simplified:               59
% 2.97/1.00  sup_given_eliminated:                   0
% 2.97/1.00  comparisons_done:                       0
% 2.97/1.00  comparisons_avoided:                    0
% 2.97/1.00  
% 2.97/1.00  ------ Simplifications
% 2.97/1.00  
% 2.97/1.00  
% 2.97/1.00  sim_fw_subset_subsumed:                 16
% 2.97/1.00  sim_bw_subset_subsumed:                 4
% 2.97/1.00  sim_fw_subsumed:                        35
% 2.97/1.00  sim_bw_subsumed:                        4
% 2.97/1.00  sim_fw_subsumption_res:                 0
% 2.97/1.00  sim_bw_subsumption_res:                 4
% 2.97/1.00  sim_tautology_del:                      48
% 2.97/1.00  sim_eq_tautology_del:                   16
% 2.97/1.00  sim_eq_res_simp:                        2
% 2.97/1.00  sim_fw_demodulated:                     0
% 2.97/1.00  sim_bw_demodulated:                     0
% 2.97/1.00  sim_light_normalised:                   0
% 2.97/1.00  sim_joinable_taut:                      0
% 2.97/1.00  sim_joinable_simp:                      0
% 2.97/1.00  sim_ac_normalised:                      0
% 2.97/1.00  sim_smt_subsumption:                    0
% 2.97/1.00  
%------------------------------------------------------------------------------
