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
% DateTime   : Thu Dec  3 12:28:23 EST 2020

% Result     : Theorem 2.80s
% Output     : CNFRefutation 2.80s
% Verified   : 
% Statistics : Number of formulae       :  174 ( 437 expanded)
%              Number of clauses        :  101 ( 133 expanded)
%              Number of leaves         :   21 (  80 expanded)
%              Depth                    :   23
%              Number of atoms          :  659 (2884 expanded)
%              Number of equality atoms :  117 ( 159 expanded)
%              Maximal formula depth    :   14 (   5 average)
%              Maximal clause size      :   22 (   3 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
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

fof(f59,plain,(
    ! [X2,X0,X1] :
      ( m1_subset_1(X0,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f23])).

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

fof(f54,plain,(
    ! [X0,X1] :
      ( v1_xboole_0(X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | ~ v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f58,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f37])).

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

fof(f50,plain,(
    ! [X0,X1] :
      ( X0 = X1
      | ~ r2_hidden(sK0(X0,X1),X1)
      | ~ r2_hidden(sK0(X0,X1),X0) ) ),
    inference(cnf_transformation,[],[f34])).

fof(f49,plain,(
    ! [X0,X1] :
      ( X0 = X1
      | r2_hidden(sK0(X0,X1),X1)
      | r2_hidden(sK0(X0,X1),X0) ) ),
    inference(cnf_transformation,[],[f34])).

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

fof(f75,plain,(
    v13_waybel_0(sK4,sK3) ),
    inference(cnf_transformation,[],[f48])).

fof(f74,plain,(
    ~ v1_xboole_0(sK4) ),
    inference(cnf_transformation,[],[f48])).

cnf(c_7,plain,
    ( ~ m1_subset_1(X0,X1)
    | r2_hidden(X0,X1)
    | v1_xboole_0(X1) ),
    inference(cnf_transformation,[],[f56])).

cnf(c_6980,plain,
    ( ~ m1_subset_1(sK0(sK4,u1_struct_0(sK3)),u1_struct_0(sK3))
    | r2_hidden(sK0(sK4,u1_struct_0(sK3)),u1_struct_0(sK3))
    | v1_xboole_0(u1_struct_0(sK3)) ),
    inference(instantiation,[status(thm)],[c_7])).

cnf(c_6981,plain,
    ( m1_subset_1(sK0(sK4,u1_struct_0(sK3)),u1_struct_0(sK3)) != iProver_top
    | r2_hidden(sK0(sK4,u1_struct_0(sK3)),u1_struct_0(sK3)) = iProver_top
    | v1_xboole_0(u1_struct_0(sK3)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_6980])).

cnf(c_841,plain,
    ( X0 != X1
    | X2 != X1
    | X2 = X0 ),
    theory(equality)).

cnf(c_1735,plain,
    ( X0 != X1
    | X0 = u1_struct_0(sK3)
    | u1_struct_0(sK3) != X1 ),
    inference(instantiation,[status(thm)],[c_841])).

cnf(c_1962,plain,
    ( u1_struct_0(sK3) != X0
    | sK4 != X0
    | sK4 = u1_struct_0(sK3) ),
    inference(instantiation,[status(thm)],[c_1735])).

cnf(c_5579,plain,
    ( u1_struct_0(sK3) != sK4
    | sK4 = u1_struct_0(sK3)
    | sK4 != sK4 ),
    inference(instantiation,[status(thm)],[c_1962])).

cnf(c_10,plain,
    ( m1_subset_1(X0,X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(X1))
    | ~ r2_hidden(X0,X2) ),
    inference(cnf_transformation,[],[f59])).

cnf(c_1649,plain,
    ( m1_subset_1(X0,X1)
    | ~ m1_subset_1(sK4,k1_zfmisc_1(X1))
    | ~ r2_hidden(X0,sK4) ),
    inference(instantiation,[status(thm)],[c_10])).

cnf(c_4051,plain,
    ( m1_subset_1(sK0(sK4,u1_struct_0(sK3)),u1_struct_0(sK3))
    | ~ m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(sK3)))
    | ~ r2_hidden(sK0(sK4,u1_struct_0(sK3)),sK4) ),
    inference(instantiation,[status(thm)],[c_1649])).

cnf(c_4067,plain,
    ( m1_subset_1(sK0(sK4,u1_struct_0(sK3)),u1_struct_0(sK3)) = iProver_top
    | m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(sK3))) != iProver_top
    | r2_hidden(sK0(sK4,u1_struct_0(sK3)),sK4) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_4051])).

cnf(c_6,plain,
    ( m1_subset_1(X0,X1)
    | ~ r2_hidden(X0,X1) ),
    inference(cnf_transformation,[],[f55])).

cnf(c_4055,plain,
    ( m1_subset_1(sK0(sK4,u1_struct_0(sK3)),u1_struct_0(sK3))
    | ~ r2_hidden(sK0(sK4,u1_struct_0(sK3)),u1_struct_0(sK3)) ),
    inference(instantiation,[status(thm)],[c_6])).

cnf(c_4057,plain,
    ( m1_subset_1(sK0(sK4,u1_struct_0(sK3)),u1_struct_0(sK3)) = iProver_top
    | r2_hidden(sK0(sK4,u1_struct_0(sK3)),u1_struct_0(sK3)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_4055])).

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

cnf(c_397,plain,
    ( r1_orders_2(X0,k3_yellow_0(X0),X1)
    | ~ m1_subset_1(X1,u1_struct_0(X0))
    | v2_struct_0(X0)
    | ~ v5_orders_2(X0)
    | ~ l1_orders_2(X0)
    | sK3 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_12,c_27])).

cnf(c_398,plain,
    ( r1_orders_2(sK3,k3_yellow_0(sK3),X0)
    | ~ m1_subset_1(X0,u1_struct_0(sK3))
    | v2_struct_0(sK3)
    | ~ v5_orders_2(sK3)
    | ~ l1_orders_2(sK3) ),
    inference(unflattening,[status(thm)],[c_397])).

cnf(c_29,negated_conjecture,
    ( ~ v2_struct_0(sK3) ),
    inference(cnf_transformation,[],[f70])).

cnf(c_28,negated_conjecture,
    ( v5_orders_2(sK3) ),
    inference(cnf_transformation,[],[f71])).

cnf(c_26,negated_conjecture,
    ( l1_orders_2(sK3) ),
    inference(cnf_transformation,[],[f73])).

cnf(c_402,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(sK3))
    | r1_orders_2(sK3,k3_yellow_0(sK3),X0) ),
    inference(global_propositional_subsumption,[status(thm)],[c_398,c_29,c_28,c_26])).

cnf(c_403,plain,
    ( r1_orders_2(sK3,k3_yellow_0(sK3),X0)
    | ~ m1_subset_1(X0,u1_struct_0(sK3)) ),
    inference(renaming,[status(thm)],[c_402])).

cnf(c_485,plain,
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
    inference(resolution_lifted,[status(thm)],[c_18,c_403])).

cnf(c_486,plain,
    ( ~ v13_waybel_0(X0,sK3)
    | ~ m1_subset_1(X1,u1_struct_0(sK3))
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK3)))
    | ~ m1_subset_1(k3_yellow_0(sK3),u1_struct_0(sK3))
    | r2_hidden(X1,X0)
    | ~ r2_hidden(k3_yellow_0(sK3),X0)
    | ~ l1_orders_2(sK3) ),
    inference(unflattening,[status(thm)],[c_485])).

cnf(c_11,plain,
    ( m1_subset_1(k3_yellow_0(X0),u1_struct_0(X0))
    | ~ l1_orders_2(X0) ),
    inference(cnf_transformation,[],[f60])).

cnf(c_65,plain,
    ( m1_subset_1(k3_yellow_0(sK3),u1_struct_0(sK3))
    | ~ l1_orders_2(sK3) ),
    inference(instantiation,[status(thm)],[c_11])).

cnf(c_490,plain,
    ( ~ r2_hidden(k3_yellow_0(sK3),X0)
    | r2_hidden(X1,X0)
    | ~ v13_waybel_0(X0,sK3)
    | ~ m1_subset_1(X1,u1_struct_0(sK3))
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK3))) ),
    inference(global_propositional_subsumption,[status(thm)],[c_486,c_26,c_65])).

cnf(c_491,plain,
    ( ~ v13_waybel_0(X0,sK3)
    | ~ m1_subset_1(X1,u1_struct_0(sK3))
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK3)))
    | r2_hidden(X1,X0)
    | ~ r2_hidden(k3_yellow_0(sK3),X0) ),
    inference(renaming,[status(thm)],[c_490])).

cnf(c_1578,plain,
    ( ~ v13_waybel_0(sK4,sK3)
    | ~ m1_subset_1(X0,u1_struct_0(sK3))
    | ~ m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(sK3)))
    | r2_hidden(X0,sK4)
    | ~ r2_hidden(k3_yellow_0(sK3),sK4) ),
    inference(instantiation,[status(thm)],[c_491])).

cnf(c_3343,plain,
    ( ~ v13_waybel_0(sK4,sK3)
    | ~ m1_subset_1(sK0(sK4,u1_struct_0(sK3)),u1_struct_0(sK3))
    | ~ m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(sK3)))
    | r2_hidden(sK0(sK4,u1_struct_0(sK3)),sK4)
    | ~ r2_hidden(k3_yellow_0(sK3),sK4) ),
    inference(instantiation,[status(thm)],[c_1578])).

cnf(c_3344,plain,
    ( v13_waybel_0(sK4,sK3) != iProver_top
    | m1_subset_1(sK0(sK4,u1_struct_0(sK3)),u1_struct_0(sK3)) != iProver_top
    | m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(sK3))) != iProver_top
    | r2_hidden(sK0(sK4,u1_struct_0(sK3)),sK4) = iProver_top
    | r2_hidden(k3_yellow_0(sK3),sK4) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3343])).

cnf(c_23,negated_conjecture,
    ( m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(sK3))) ),
    inference(cnf_transformation,[],[f76])).

cnf(c_1394,plain,
    ( m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(sK3))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_23])).

cnf(c_9,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | r1_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f57])).

cnf(c_1396,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(X1)) != iProver_top
    | r1_tarski(X0,X1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_9])).

cnf(c_1839,plain,
    ( r1_tarski(sK4,u1_struct_0(sK3)) = iProver_top ),
    inference(superposition,[status(thm)],[c_1394,c_1396])).

cnf(c_5,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | ~ v1_xboole_0(X1)
    | v1_xboole_0(X0) ),
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
    | ~ v1_xboole_0(X1)
    | v1_xboole_0(X0) ),
    inference(bin_hyper_res,[status(thm)],[c_5,c_225])).

cnf(c_1391,plain,
    ( r1_tarski(X0,X1) != iProver_top
    | v1_xboole_0(X1) != iProver_top
    | v1_xboole_0(X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_288])).

cnf(c_3253,plain,
    ( v1_xboole_0(u1_struct_0(sK3)) != iProver_top
    | v1_xboole_0(sK4) = iProver_top ),
    inference(superposition,[status(thm)],[c_1839,c_1391])).

cnf(c_3258,plain,
    ( ~ v1_xboole_0(u1_struct_0(sK3))
    | v1_xboole_0(sK4) ),
    inference(predicate_to_equality_rev,[status(thm)],[c_3253])).

cnf(c_526,plain,
    ( m1_subset_1(k3_yellow_0(X0),u1_struct_0(X0))
    | sK3 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_11,c_26])).

cnf(c_527,plain,
    ( m1_subset_1(k3_yellow_0(sK3),u1_struct_0(sK3)) ),
    inference(unflattening,[status(thm)],[c_526])).

cnf(c_1387,plain,
    ( m1_subset_1(k3_yellow_0(sK3),u1_struct_0(sK3)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_527])).

cnf(c_1398,plain,
    ( m1_subset_1(X0,X1) != iProver_top
    | r2_hidden(X0,X1) = iProver_top
    | v1_xboole_0(X1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_7])).

cnf(c_2220,plain,
    ( r2_hidden(k3_yellow_0(sK3),u1_struct_0(sK3)) = iProver_top
    | v1_xboole_0(u1_struct_0(sK3)) = iProver_top ),
    inference(superposition,[status(thm)],[c_1387,c_1398])).

cnf(c_2257,plain,
    ( r2_hidden(k3_yellow_0(sK3),u1_struct_0(sK3))
    | v1_xboole_0(u1_struct_0(sK3)) ),
    inference(predicate_to_equality_rev,[status(thm)],[c_2220])).

cnf(c_842,plain,
    ( ~ r2_hidden(X0,X1)
    | r2_hidden(X2,X3)
    | X2 != X0
    | X3 != X1 ),
    theory(equality)).

cnf(c_1679,plain,
    ( r2_hidden(X0,X1)
    | ~ r2_hidden(k3_yellow_0(sK3),u1_struct_0(sK3))
    | X1 != u1_struct_0(sK3)
    | X0 != k3_yellow_0(sK3) ),
    inference(instantiation,[status(thm)],[c_842])).

cnf(c_2198,plain,
    ( ~ r2_hidden(k3_yellow_0(sK3),u1_struct_0(sK3))
    | r2_hidden(k3_yellow_0(sK3),sK4)
    | k3_yellow_0(sK3) != k3_yellow_0(sK3)
    | sK4 != u1_struct_0(sK3) ),
    inference(instantiation,[status(thm)],[c_1679])).

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

cnf(c_434,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X0))
    | ~ r2_hidden(k3_yellow_0(sK3),sK4)
    | u1_struct_0(sK3) != X0
    | sK4 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_20,c_226])).

cnf(c_435,plain,
    ( ~ m1_subset_1(u1_struct_0(sK3),k1_zfmisc_1(u1_struct_0(sK3)))
    | ~ r2_hidden(k3_yellow_0(sK3),sK4)
    | sK4 != u1_struct_0(sK3) ),
    inference(unflattening,[status(thm)],[c_434])).

cnf(c_1389,plain,
    ( sK4 != u1_struct_0(sK3)
    | m1_subset_1(u1_struct_0(sK3),k1_zfmisc_1(u1_struct_0(sK3))) != iProver_top
    | r2_hidden(k3_yellow_0(sK3),sK4) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_435])).

cnf(c_436,plain,
    ( sK4 != u1_struct_0(sK3)
    | m1_subset_1(u1_struct_0(sK3),k1_zfmisc_1(u1_struct_0(sK3))) != iProver_top
    | r2_hidden(k3_yellow_0(sK3),sK4) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_435])).

cnf(c_1587,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK3)))
    | ~ r1_tarski(X0,u1_struct_0(sK3)) ),
    inference(instantiation,[status(thm)],[c_8])).

cnf(c_1695,plain,
    ( m1_subset_1(u1_struct_0(sK3),k1_zfmisc_1(u1_struct_0(sK3)))
    | ~ r1_tarski(u1_struct_0(sK3),u1_struct_0(sK3)) ),
    inference(instantiation,[status(thm)],[c_1587])).

cnf(c_1697,plain,
    ( m1_subset_1(u1_struct_0(sK3),k1_zfmisc_1(u1_struct_0(sK3))) = iProver_top
    | r1_tarski(u1_struct_0(sK3),u1_struct_0(sK3)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1695])).

cnf(c_4,plain,
    ( r1_tarski(X0,X0) ),
    inference(cnf_transformation,[],[f80])).

cnf(c_1696,plain,
    ( r1_tarski(u1_struct_0(sK3),u1_struct_0(sK3)) ),
    inference(instantiation,[status(thm)],[c_4])).

cnf(c_1699,plain,
    ( r1_tarski(u1_struct_0(sK3),u1_struct_0(sK3)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1696])).

cnf(c_2192,plain,
    ( sK4 != u1_struct_0(sK3)
    | r2_hidden(k3_yellow_0(sK3),sK4) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_1389,c_436,c_1697,c_1699])).

cnf(c_2194,plain,
    ( ~ r2_hidden(k3_yellow_0(sK3),sK4)
    | sK4 != u1_struct_0(sK3) ),
    inference(predicate_to_equality_rev,[status(thm)],[c_2192])).

cnf(c_0,plain,
    ( ~ r2_hidden(sK0(X0,X1),X1)
    | ~ r2_hidden(sK0(X0,X1),X0)
    | X1 = X0 ),
    inference(cnf_transformation,[],[f50])).

cnf(c_1664,plain,
    ( ~ r2_hidden(sK0(sK4,X0),X0)
    | ~ r2_hidden(sK0(sK4,X0),sK4)
    | X0 = sK4 ),
    inference(instantiation,[status(thm)],[c_0])).

cnf(c_1996,plain,
    ( ~ r2_hidden(sK0(sK4,u1_struct_0(sK3)),u1_struct_0(sK3))
    | ~ r2_hidden(sK0(sK4,u1_struct_0(sK3)),sK4)
    | u1_struct_0(sK3) = sK4 ),
    inference(instantiation,[status(thm)],[c_1664])).

cnf(c_2007,plain,
    ( u1_struct_0(sK3) = sK4
    | r2_hidden(sK0(sK4,u1_struct_0(sK3)),u1_struct_0(sK3)) != iProver_top
    | r2_hidden(sK0(sK4,u1_struct_0(sK3)),sK4) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1996])).

cnf(c_1,plain,
    ( r2_hidden(sK0(X0,X1),X1)
    | r2_hidden(sK0(X0,X1),X0)
    | X1 = X0 ),
    inference(cnf_transformation,[],[f49])).

cnf(c_1663,plain,
    ( r2_hidden(sK0(sK4,X0),X0)
    | r2_hidden(sK0(sK4,X0),sK4)
    | X0 = sK4 ),
    inference(instantiation,[status(thm)],[c_1])).

cnf(c_1997,plain,
    ( r2_hidden(sK0(sK4,u1_struct_0(sK3)),u1_struct_0(sK3))
    | r2_hidden(sK0(sK4,u1_struct_0(sK3)),sK4)
    | u1_struct_0(sK3) = sK4 ),
    inference(instantiation,[status(thm)],[c_1663])).

cnf(c_2005,plain,
    ( u1_struct_0(sK3) = sK4
    | r2_hidden(sK0(sK4,u1_struct_0(sK3)),u1_struct_0(sK3)) = iProver_top
    | r2_hidden(sK0(sK4,u1_struct_0(sK3)),sK4) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1997])).

cnf(c_840,plain,
    ( X0 = X0 ),
    theory(equality)).

cnf(c_1674,plain,
    ( sK4 = sK4 ),
    inference(instantiation,[status(thm)],[c_840])).

cnf(c_1592,plain,
    ( ~ m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(sK3)))
    | r1_tarski(sK4,u1_struct_0(sK3)) ),
    inference(instantiation,[status(thm)],[c_9])).

cnf(c_1593,plain,
    ( m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(sK3))) != iProver_top
    | r1_tarski(sK4,u1_struct_0(sK3)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1592])).

cnf(c_847,plain,
    ( X0 != X1
    | k3_yellow_0(X0) = k3_yellow_0(X1) ),
    theory(equality)).

cnf(c_857,plain,
    ( k3_yellow_0(sK3) = k3_yellow_0(sK3)
    | sK3 != sK3 ),
    inference(instantiation,[status(thm)],[c_847])).

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

cnf(c_421,plain,
    ( ~ r1_tarski(X0,X1)
    | r2_hidden(k3_yellow_0(sK3),sK4)
    | X1 = X0
    | u1_struct_0(sK3) != X1
    | sK4 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_291,c_228])).

cnf(c_422,plain,
    ( ~ r1_tarski(sK4,u1_struct_0(sK3))
    | r2_hidden(k3_yellow_0(sK3),sK4)
    | u1_struct_0(sK3) = sK4 ),
    inference(unflattening,[status(thm)],[c_421])).

cnf(c_423,plain,
    ( u1_struct_0(sK3) = sK4
    | r1_tarski(sK4,u1_struct_0(sK3)) != iProver_top
    | r2_hidden(k3_yellow_0(sK3),sK4) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_422])).

cnf(c_84,plain,
    ( r1_tarski(sK3,sK3) ),
    inference(instantiation,[status(thm)],[c_4])).

cnf(c_74,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(sK3))
    | ~ r1_tarski(sK3,sK3) ),
    inference(instantiation,[status(thm)],[c_8])).

cnf(c_43,plain,
    ( v1_subset_1(sK3,sK3)
    | ~ m1_subset_1(sK3,k1_zfmisc_1(sK3))
    | sK3 = sK3 ),
    inference(instantiation,[status(thm)],[c_19])).

cnf(c_40,plain,
    ( ~ v1_subset_1(sK3,sK3)
    | ~ m1_subset_1(sK3,k1_zfmisc_1(sK3)) ),
    inference(instantiation,[status(thm)],[c_20])).

cnf(c_36,plain,
    ( m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(sK3))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_23])).

cnf(c_24,negated_conjecture,
    ( v13_waybel_0(sK4,sK3) ),
    inference(cnf_transformation,[],[f75])).

cnf(c_35,plain,
    ( v13_waybel_0(sK4,sK3) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_24])).

cnf(c_25,negated_conjecture,
    ( ~ v1_xboole_0(sK4) ),
    inference(cnf_transformation,[],[f74])).

cnf(c_34,plain,
    ( v1_xboole_0(sK4) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_25])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_6981,c_5579,c_4067,c_4057,c_3344,c_3258,c_3253,c_2257,c_2198,c_2194,c_2007,c_2005,c_1674,c_1593,c_857,c_423,c_84,c_74,c_43,c_40,c_36,c_35,c_34,c_25])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.10/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.10/0.12  % Command    : iproveropt_run.sh %d %s
% 0.13/0.33  % Computer   : n014.cluster.edu
% 0.13/0.33  % Model      : x86_64 x86_64
% 0.13/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.33  % Memory     : 8042.1875MB
% 0.13/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.33  % CPULimit   : 60
% 0.13/0.33  % WCLimit    : 600
% 0.13/0.33  % DateTime   : Tue Dec  1 17:39:22 EST 2020
% 0.13/0.33  % CPUTime    : 
% 0.13/0.34  % Running in FOF mode
% 2.80/1.02  % SZS status Started for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.80/1.02  
% 2.80/1.02  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 2.80/1.02  
% 2.80/1.02  ------  iProver source info
% 2.80/1.02  
% 2.80/1.02  git: date: 2020-06-30 10:37:57 +0100
% 2.80/1.02  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 2.80/1.02  git: non_committed_changes: false
% 2.80/1.02  git: last_make_outside_of_git: false
% 2.80/1.02  
% 2.80/1.02  ------ 
% 2.80/1.02  
% 2.80/1.02  ------ Input Options
% 2.80/1.02  
% 2.80/1.02  --out_options                           all
% 2.80/1.02  --tptp_safe_out                         true
% 2.80/1.02  --problem_path                          ""
% 2.80/1.02  --include_path                          ""
% 2.80/1.02  --clausifier                            res/vclausify_rel
% 2.80/1.02  --clausifier_options                    --mode clausify
% 2.80/1.02  --stdin                                 false
% 2.80/1.02  --stats_out                             all
% 2.80/1.02  
% 2.80/1.02  ------ General Options
% 2.80/1.02  
% 2.80/1.02  --fof                                   false
% 2.80/1.02  --time_out_real                         305.
% 2.80/1.02  --time_out_virtual                      -1.
% 2.80/1.02  --symbol_type_check                     false
% 2.80/1.02  --clausify_out                          false
% 2.80/1.02  --sig_cnt_out                           false
% 2.80/1.02  --trig_cnt_out                          false
% 2.80/1.02  --trig_cnt_out_tolerance                1.
% 2.80/1.02  --trig_cnt_out_sk_spl                   false
% 2.80/1.02  --abstr_cl_out                          false
% 2.80/1.02  
% 2.80/1.02  ------ Global Options
% 2.80/1.02  
% 2.80/1.02  --schedule                              default
% 2.80/1.02  --add_important_lit                     false
% 2.80/1.02  --prop_solver_per_cl                    1000
% 2.80/1.02  --min_unsat_core                        false
% 2.80/1.02  --soft_assumptions                      false
% 2.80/1.02  --soft_lemma_size                       3
% 2.80/1.02  --prop_impl_unit_size                   0
% 2.80/1.02  --prop_impl_unit                        []
% 2.80/1.02  --share_sel_clauses                     true
% 2.80/1.02  --reset_solvers                         false
% 2.80/1.02  --bc_imp_inh                            [conj_cone]
% 2.80/1.02  --conj_cone_tolerance                   3.
% 2.80/1.02  --extra_neg_conj                        none
% 2.80/1.02  --large_theory_mode                     true
% 2.80/1.02  --prolific_symb_bound                   200
% 2.80/1.02  --lt_threshold                          2000
% 2.80/1.02  --clause_weak_htbl                      true
% 2.80/1.02  --gc_record_bc_elim                     false
% 2.80/1.02  
% 2.80/1.02  ------ Preprocessing Options
% 2.80/1.02  
% 2.80/1.02  --preprocessing_flag                    true
% 2.80/1.02  --time_out_prep_mult                    0.1
% 2.80/1.02  --splitting_mode                        input
% 2.80/1.02  --splitting_grd                         true
% 2.80/1.02  --splitting_cvd                         false
% 2.80/1.02  --splitting_cvd_svl                     false
% 2.80/1.02  --splitting_nvd                         32
% 2.80/1.02  --sub_typing                            true
% 2.80/1.02  --prep_gs_sim                           true
% 2.80/1.02  --prep_unflatten                        true
% 2.80/1.02  --prep_res_sim                          true
% 2.80/1.02  --prep_upred                            true
% 2.80/1.02  --prep_sem_filter                       exhaustive
% 2.80/1.02  --prep_sem_filter_out                   false
% 2.80/1.02  --pred_elim                             true
% 2.80/1.02  --res_sim_input                         true
% 2.80/1.02  --eq_ax_congr_red                       true
% 2.80/1.02  --pure_diseq_elim                       true
% 2.80/1.02  --brand_transform                       false
% 2.80/1.02  --non_eq_to_eq                          false
% 2.80/1.02  --prep_def_merge                        true
% 2.80/1.02  --prep_def_merge_prop_impl              false
% 2.80/1.02  --prep_def_merge_mbd                    true
% 2.80/1.02  --prep_def_merge_tr_red                 false
% 2.80/1.02  --prep_def_merge_tr_cl                  false
% 2.80/1.02  --smt_preprocessing                     true
% 2.80/1.02  --smt_ac_axioms                         fast
% 2.80/1.02  --preprocessed_out                      false
% 2.80/1.02  --preprocessed_stats                    false
% 2.80/1.02  
% 2.80/1.02  ------ Abstraction refinement Options
% 2.80/1.02  
% 2.80/1.02  --abstr_ref                             []
% 2.80/1.02  --abstr_ref_prep                        false
% 2.80/1.02  --abstr_ref_until_sat                   false
% 2.80/1.02  --abstr_ref_sig_restrict                funpre
% 2.80/1.02  --abstr_ref_af_restrict_to_split_sk     false
% 2.80/1.02  --abstr_ref_under                       []
% 2.80/1.02  
% 2.80/1.02  ------ SAT Options
% 2.80/1.02  
% 2.80/1.02  --sat_mode                              false
% 2.80/1.02  --sat_fm_restart_options                ""
% 2.80/1.02  --sat_gr_def                            false
% 2.80/1.02  --sat_epr_types                         true
% 2.80/1.02  --sat_non_cyclic_types                  false
% 2.80/1.02  --sat_finite_models                     false
% 2.80/1.02  --sat_fm_lemmas                         false
% 2.80/1.02  --sat_fm_prep                           false
% 2.80/1.02  --sat_fm_uc_incr                        true
% 2.80/1.02  --sat_out_model                         small
% 2.80/1.02  --sat_out_clauses                       false
% 2.80/1.02  
% 2.80/1.02  ------ QBF Options
% 2.80/1.02  
% 2.80/1.02  --qbf_mode                              false
% 2.80/1.02  --qbf_elim_univ                         false
% 2.80/1.02  --qbf_dom_inst                          none
% 2.80/1.02  --qbf_dom_pre_inst                      false
% 2.80/1.02  --qbf_sk_in                             false
% 2.80/1.02  --qbf_pred_elim                         true
% 2.80/1.02  --qbf_split                             512
% 2.80/1.02  
% 2.80/1.02  ------ BMC1 Options
% 2.80/1.02  
% 2.80/1.02  --bmc1_incremental                      false
% 2.80/1.02  --bmc1_axioms                           reachable_all
% 2.80/1.02  --bmc1_min_bound                        0
% 2.80/1.02  --bmc1_max_bound                        -1
% 2.80/1.02  --bmc1_max_bound_default                -1
% 2.80/1.02  --bmc1_symbol_reachability              true
% 2.80/1.02  --bmc1_property_lemmas                  false
% 2.80/1.02  --bmc1_k_induction                      false
% 2.80/1.02  --bmc1_non_equiv_states                 false
% 2.80/1.02  --bmc1_deadlock                         false
% 2.80/1.02  --bmc1_ucm                              false
% 2.80/1.02  --bmc1_add_unsat_core                   none
% 2.80/1.02  --bmc1_unsat_core_children              false
% 2.80/1.02  --bmc1_unsat_core_extrapolate_axioms    false
% 2.80/1.02  --bmc1_out_stat                         full
% 2.80/1.02  --bmc1_ground_init                      false
% 2.80/1.02  --bmc1_pre_inst_next_state              false
% 2.80/1.02  --bmc1_pre_inst_state                   false
% 2.80/1.02  --bmc1_pre_inst_reach_state             false
% 2.80/1.02  --bmc1_out_unsat_core                   false
% 2.80/1.02  --bmc1_aig_witness_out                  false
% 2.80/1.02  --bmc1_verbose                          false
% 2.80/1.02  --bmc1_dump_clauses_tptp                false
% 2.80/1.02  --bmc1_dump_unsat_core_tptp             false
% 2.80/1.02  --bmc1_dump_file                        -
% 2.80/1.02  --bmc1_ucm_expand_uc_limit              128
% 2.80/1.02  --bmc1_ucm_n_expand_iterations          6
% 2.80/1.02  --bmc1_ucm_extend_mode                  1
% 2.80/1.02  --bmc1_ucm_init_mode                    2
% 2.80/1.02  --bmc1_ucm_cone_mode                    none
% 2.80/1.02  --bmc1_ucm_reduced_relation_type        0
% 2.80/1.02  --bmc1_ucm_relax_model                  4
% 2.80/1.02  --bmc1_ucm_full_tr_after_sat            true
% 2.80/1.02  --bmc1_ucm_expand_neg_assumptions       false
% 2.80/1.02  --bmc1_ucm_layered_model                none
% 2.80/1.02  --bmc1_ucm_max_lemma_size               10
% 2.80/1.02  
% 2.80/1.02  ------ AIG Options
% 2.80/1.02  
% 2.80/1.02  --aig_mode                              false
% 2.80/1.02  
% 2.80/1.02  ------ Instantiation Options
% 2.80/1.02  
% 2.80/1.02  --instantiation_flag                    true
% 2.80/1.02  --inst_sos_flag                         false
% 2.80/1.02  --inst_sos_phase                        true
% 2.80/1.02  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 2.80/1.02  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 2.80/1.02  --inst_lit_sel_side                     num_symb
% 2.80/1.02  --inst_solver_per_active                1400
% 2.80/1.02  --inst_solver_calls_frac                1.
% 2.80/1.02  --inst_passive_queue_type               priority_queues
% 2.80/1.02  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 2.80/1.02  --inst_passive_queues_freq              [25;2]
% 2.80/1.02  --inst_dismatching                      true
% 2.80/1.02  --inst_eager_unprocessed_to_passive     true
% 2.80/1.02  --inst_prop_sim_given                   true
% 2.80/1.02  --inst_prop_sim_new                     false
% 2.80/1.02  --inst_subs_new                         false
% 2.80/1.02  --inst_eq_res_simp                      false
% 2.80/1.02  --inst_subs_given                       false
% 2.80/1.02  --inst_orphan_elimination               true
% 2.80/1.02  --inst_learning_loop_flag               true
% 2.80/1.02  --inst_learning_start                   3000
% 2.80/1.02  --inst_learning_factor                  2
% 2.80/1.02  --inst_start_prop_sim_after_learn       3
% 2.80/1.02  --inst_sel_renew                        solver
% 2.80/1.02  --inst_lit_activity_flag                true
% 2.80/1.02  --inst_restr_to_given                   false
% 2.80/1.02  --inst_activity_threshold               500
% 2.80/1.02  --inst_out_proof                        true
% 2.80/1.02  
% 2.80/1.02  ------ Resolution Options
% 2.80/1.02  
% 2.80/1.02  --resolution_flag                       true
% 2.80/1.02  --res_lit_sel                           adaptive
% 2.80/1.02  --res_lit_sel_side                      none
% 2.80/1.02  --res_ordering                          kbo
% 2.80/1.02  --res_to_prop_solver                    active
% 2.80/1.02  --res_prop_simpl_new                    false
% 2.80/1.02  --res_prop_simpl_given                  true
% 2.80/1.02  --res_passive_queue_type                priority_queues
% 2.80/1.02  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 2.80/1.02  --res_passive_queues_freq               [15;5]
% 2.80/1.02  --res_forward_subs                      full
% 2.80/1.02  --res_backward_subs                     full
% 2.80/1.02  --res_forward_subs_resolution           true
% 2.80/1.02  --res_backward_subs_resolution          true
% 2.80/1.02  --res_orphan_elimination                true
% 2.80/1.02  --res_time_limit                        2.
% 2.80/1.02  --res_out_proof                         true
% 2.80/1.02  
% 2.80/1.02  ------ Superposition Options
% 2.80/1.02  
% 2.80/1.02  --superposition_flag                    true
% 2.80/1.02  --sup_passive_queue_type                priority_queues
% 2.80/1.02  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 2.80/1.02  --sup_passive_queues_freq               [8;1;4]
% 2.80/1.02  --demod_completeness_check              fast
% 2.80/1.02  --demod_use_ground                      true
% 2.80/1.02  --sup_to_prop_solver                    passive
% 2.80/1.02  --sup_prop_simpl_new                    true
% 2.80/1.02  --sup_prop_simpl_given                  true
% 2.80/1.02  --sup_fun_splitting                     false
% 2.80/1.02  --sup_smt_interval                      50000
% 2.80/1.02  
% 2.80/1.02  ------ Superposition Simplification Setup
% 2.80/1.02  
% 2.80/1.02  --sup_indices_passive                   []
% 2.80/1.02  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.80/1.02  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.80/1.02  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.80/1.02  --sup_full_triv                         [TrivRules;PropSubs]
% 2.80/1.02  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.80/1.02  --sup_full_bw                           [BwDemod]
% 2.80/1.02  --sup_immed_triv                        [TrivRules]
% 2.80/1.02  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 2.80/1.02  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.80/1.02  --sup_immed_bw_main                     []
% 2.80/1.02  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.80/1.02  --sup_input_triv                        [Unflattening;TrivRules]
% 2.80/1.02  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.80/1.02  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.80/1.02  
% 2.80/1.02  ------ Combination Options
% 2.80/1.02  
% 2.80/1.02  --comb_res_mult                         3
% 2.80/1.02  --comb_sup_mult                         2
% 2.80/1.02  --comb_inst_mult                        10
% 2.80/1.02  
% 2.80/1.02  ------ Debug Options
% 2.80/1.02  
% 2.80/1.02  --dbg_backtrace                         false
% 2.80/1.02  --dbg_dump_prop_clauses                 false
% 2.80/1.02  --dbg_dump_prop_clauses_file            -
% 2.80/1.02  --dbg_out_stat                          false
% 2.80/1.02  ------ Parsing...
% 2.80/1.02  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 2.80/1.02  
% 2.80/1.02  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe:1:0s pe:2:0s pe:4:0s pe_e  sf_s  rm: 7 0s  sf_e  pe_s  pe_e 
% 2.80/1.02  
% 2.80/1.02  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 2.80/1.02  
% 2.80/1.02  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 2.80/1.02  ------ Proving...
% 2.80/1.02  ------ Problem Properties 
% 2.80/1.02  
% 2.80/1.02  
% 2.80/1.02  clauses                                 22
% 2.80/1.02  conjectures                             3
% 2.80/1.02  EPR                                     7
% 2.80/1.02  Horn                                    15
% 2.80/1.02  unary                                   5
% 2.80/1.02  binary                                  3
% 2.80/1.02  lits                                    58
% 2.80/1.02  lits eq                                 5
% 2.80/1.02  fd_pure                                 0
% 2.80/1.02  fd_pseudo                               0
% 2.80/1.02  fd_cond                                 0
% 2.80/1.02  fd_pseudo_cond                          3
% 2.80/1.02  AC symbols                              0
% 2.80/1.02  
% 2.80/1.02  ------ Schedule dynamic 5 is on 
% 2.80/1.02  
% 2.80/1.02  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" Time Limit: 10.
% 2.80/1.02  
% 2.80/1.02  
% 2.80/1.02  ------ 
% 2.80/1.02  Current options:
% 2.80/1.02  ------ 
% 2.80/1.02  
% 2.80/1.02  ------ Input Options
% 2.80/1.02  
% 2.80/1.02  --out_options                           all
% 2.80/1.02  --tptp_safe_out                         true
% 2.80/1.02  --problem_path                          ""
% 2.80/1.02  --include_path                          ""
% 2.80/1.02  --clausifier                            res/vclausify_rel
% 2.80/1.02  --clausifier_options                    --mode clausify
% 2.80/1.02  --stdin                                 false
% 2.80/1.02  --stats_out                             all
% 2.80/1.02  
% 2.80/1.02  ------ General Options
% 2.80/1.02  
% 2.80/1.02  --fof                                   false
% 2.80/1.02  --time_out_real                         305.
% 2.80/1.02  --time_out_virtual                      -1.
% 2.80/1.02  --symbol_type_check                     false
% 2.80/1.02  --clausify_out                          false
% 2.80/1.02  --sig_cnt_out                           false
% 2.80/1.02  --trig_cnt_out                          false
% 2.80/1.02  --trig_cnt_out_tolerance                1.
% 2.80/1.02  --trig_cnt_out_sk_spl                   false
% 2.80/1.02  --abstr_cl_out                          false
% 2.80/1.02  
% 2.80/1.02  ------ Global Options
% 2.80/1.02  
% 2.80/1.02  --schedule                              default
% 2.80/1.02  --add_important_lit                     false
% 2.80/1.02  --prop_solver_per_cl                    1000
% 2.80/1.02  --min_unsat_core                        false
% 2.80/1.02  --soft_assumptions                      false
% 2.80/1.02  --soft_lemma_size                       3
% 2.80/1.02  --prop_impl_unit_size                   0
% 2.80/1.02  --prop_impl_unit                        []
% 2.80/1.02  --share_sel_clauses                     true
% 2.80/1.02  --reset_solvers                         false
% 2.80/1.02  --bc_imp_inh                            [conj_cone]
% 2.80/1.02  --conj_cone_tolerance                   3.
% 2.80/1.02  --extra_neg_conj                        none
% 2.80/1.02  --large_theory_mode                     true
% 2.80/1.02  --prolific_symb_bound                   200
% 2.80/1.02  --lt_threshold                          2000
% 2.80/1.02  --clause_weak_htbl                      true
% 2.80/1.02  --gc_record_bc_elim                     false
% 2.80/1.02  
% 2.80/1.02  ------ Preprocessing Options
% 2.80/1.02  
% 2.80/1.02  --preprocessing_flag                    true
% 2.80/1.02  --time_out_prep_mult                    0.1
% 2.80/1.02  --splitting_mode                        input
% 2.80/1.02  --splitting_grd                         true
% 2.80/1.02  --splitting_cvd                         false
% 2.80/1.02  --splitting_cvd_svl                     false
% 2.80/1.02  --splitting_nvd                         32
% 2.80/1.02  --sub_typing                            true
% 2.80/1.02  --prep_gs_sim                           true
% 2.80/1.02  --prep_unflatten                        true
% 2.80/1.02  --prep_res_sim                          true
% 2.80/1.02  --prep_upred                            true
% 2.80/1.02  --prep_sem_filter                       exhaustive
% 2.80/1.02  --prep_sem_filter_out                   false
% 2.80/1.02  --pred_elim                             true
% 2.80/1.02  --res_sim_input                         true
% 2.80/1.02  --eq_ax_congr_red                       true
% 2.80/1.02  --pure_diseq_elim                       true
% 2.80/1.02  --brand_transform                       false
% 2.80/1.02  --non_eq_to_eq                          false
% 2.80/1.02  --prep_def_merge                        true
% 2.80/1.02  --prep_def_merge_prop_impl              false
% 2.80/1.02  --prep_def_merge_mbd                    true
% 2.80/1.02  --prep_def_merge_tr_red                 false
% 2.80/1.02  --prep_def_merge_tr_cl                  false
% 2.80/1.02  --smt_preprocessing                     true
% 2.80/1.02  --smt_ac_axioms                         fast
% 2.80/1.02  --preprocessed_out                      false
% 2.80/1.02  --preprocessed_stats                    false
% 2.80/1.02  
% 2.80/1.02  ------ Abstraction refinement Options
% 2.80/1.02  
% 2.80/1.02  --abstr_ref                             []
% 2.80/1.02  --abstr_ref_prep                        false
% 2.80/1.02  --abstr_ref_until_sat                   false
% 2.80/1.02  --abstr_ref_sig_restrict                funpre
% 2.80/1.02  --abstr_ref_af_restrict_to_split_sk     false
% 2.80/1.02  --abstr_ref_under                       []
% 2.80/1.02  
% 2.80/1.02  ------ SAT Options
% 2.80/1.02  
% 2.80/1.02  --sat_mode                              false
% 2.80/1.02  --sat_fm_restart_options                ""
% 2.80/1.02  --sat_gr_def                            false
% 2.80/1.02  --sat_epr_types                         true
% 2.80/1.02  --sat_non_cyclic_types                  false
% 2.80/1.02  --sat_finite_models                     false
% 2.80/1.02  --sat_fm_lemmas                         false
% 2.80/1.02  --sat_fm_prep                           false
% 2.80/1.02  --sat_fm_uc_incr                        true
% 2.80/1.02  --sat_out_model                         small
% 2.80/1.02  --sat_out_clauses                       false
% 2.80/1.02  
% 2.80/1.02  ------ QBF Options
% 2.80/1.02  
% 2.80/1.02  --qbf_mode                              false
% 2.80/1.02  --qbf_elim_univ                         false
% 2.80/1.02  --qbf_dom_inst                          none
% 2.80/1.02  --qbf_dom_pre_inst                      false
% 2.80/1.02  --qbf_sk_in                             false
% 2.80/1.02  --qbf_pred_elim                         true
% 2.80/1.02  --qbf_split                             512
% 2.80/1.02  
% 2.80/1.02  ------ BMC1 Options
% 2.80/1.02  
% 2.80/1.02  --bmc1_incremental                      false
% 2.80/1.02  --bmc1_axioms                           reachable_all
% 2.80/1.02  --bmc1_min_bound                        0
% 2.80/1.02  --bmc1_max_bound                        -1
% 2.80/1.02  --bmc1_max_bound_default                -1
% 2.80/1.02  --bmc1_symbol_reachability              true
% 2.80/1.02  --bmc1_property_lemmas                  false
% 2.80/1.02  --bmc1_k_induction                      false
% 2.80/1.02  --bmc1_non_equiv_states                 false
% 2.80/1.02  --bmc1_deadlock                         false
% 2.80/1.02  --bmc1_ucm                              false
% 2.80/1.02  --bmc1_add_unsat_core                   none
% 2.80/1.02  --bmc1_unsat_core_children              false
% 2.80/1.02  --bmc1_unsat_core_extrapolate_axioms    false
% 2.80/1.02  --bmc1_out_stat                         full
% 2.80/1.02  --bmc1_ground_init                      false
% 2.80/1.02  --bmc1_pre_inst_next_state              false
% 2.80/1.02  --bmc1_pre_inst_state                   false
% 2.80/1.02  --bmc1_pre_inst_reach_state             false
% 2.80/1.02  --bmc1_out_unsat_core                   false
% 2.80/1.02  --bmc1_aig_witness_out                  false
% 2.80/1.02  --bmc1_verbose                          false
% 2.80/1.02  --bmc1_dump_clauses_tptp                false
% 2.80/1.02  --bmc1_dump_unsat_core_tptp             false
% 2.80/1.02  --bmc1_dump_file                        -
% 2.80/1.02  --bmc1_ucm_expand_uc_limit              128
% 2.80/1.02  --bmc1_ucm_n_expand_iterations          6
% 2.80/1.02  --bmc1_ucm_extend_mode                  1
% 2.80/1.02  --bmc1_ucm_init_mode                    2
% 2.80/1.02  --bmc1_ucm_cone_mode                    none
% 2.80/1.02  --bmc1_ucm_reduced_relation_type        0
% 2.80/1.02  --bmc1_ucm_relax_model                  4
% 2.80/1.02  --bmc1_ucm_full_tr_after_sat            true
% 2.80/1.02  --bmc1_ucm_expand_neg_assumptions       false
% 2.80/1.02  --bmc1_ucm_layered_model                none
% 2.80/1.02  --bmc1_ucm_max_lemma_size               10
% 2.80/1.02  
% 2.80/1.02  ------ AIG Options
% 2.80/1.02  
% 2.80/1.02  --aig_mode                              false
% 2.80/1.02  
% 2.80/1.02  ------ Instantiation Options
% 2.80/1.02  
% 2.80/1.02  --instantiation_flag                    true
% 2.80/1.02  --inst_sos_flag                         false
% 2.80/1.02  --inst_sos_phase                        true
% 2.80/1.02  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 2.80/1.02  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 2.80/1.02  --inst_lit_sel_side                     none
% 2.80/1.02  --inst_solver_per_active                1400
% 2.80/1.02  --inst_solver_calls_frac                1.
% 2.80/1.02  --inst_passive_queue_type               priority_queues
% 2.80/1.02  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 2.80/1.02  --inst_passive_queues_freq              [25;2]
% 2.80/1.02  --inst_dismatching                      true
% 2.80/1.02  --inst_eager_unprocessed_to_passive     true
% 2.80/1.02  --inst_prop_sim_given                   true
% 2.80/1.02  --inst_prop_sim_new                     false
% 2.80/1.02  --inst_subs_new                         false
% 2.80/1.02  --inst_eq_res_simp                      false
% 2.80/1.02  --inst_subs_given                       false
% 2.80/1.02  --inst_orphan_elimination               true
% 2.80/1.02  --inst_learning_loop_flag               true
% 2.80/1.02  --inst_learning_start                   3000
% 2.80/1.02  --inst_learning_factor                  2
% 2.80/1.02  --inst_start_prop_sim_after_learn       3
% 2.80/1.02  --inst_sel_renew                        solver
% 2.80/1.02  --inst_lit_activity_flag                true
% 2.80/1.02  --inst_restr_to_given                   false
% 2.80/1.02  --inst_activity_threshold               500
% 2.80/1.02  --inst_out_proof                        true
% 2.80/1.02  
% 2.80/1.02  ------ Resolution Options
% 2.80/1.02  
% 2.80/1.02  --resolution_flag                       false
% 2.80/1.02  --res_lit_sel                           adaptive
% 2.80/1.02  --res_lit_sel_side                      none
% 2.80/1.02  --res_ordering                          kbo
% 2.80/1.02  --res_to_prop_solver                    active
% 2.80/1.02  --res_prop_simpl_new                    false
% 2.80/1.02  --res_prop_simpl_given                  true
% 2.80/1.02  --res_passive_queue_type                priority_queues
% 2.80/1.02  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 2.80/1.02  --res_passive_queues_freq               [15;5]
% 2.80/1.02  --res_forward_subs                      full
% 2.80/1.02  --res_backward_subs                     full
% 2.80/1.02  --res_forward_subs_resolution           true
% 2.80/1.02  --res_backward_subs_resolution          true
% 2.80/1.02  --res_orphan_elimination                true
% 2.80/1.02  --res_time_limit                        2.
% 2.80/1.02  --res_out_proof                         true
% 2.80/1.02  
% 2.80/1.02  ------ Superposition Options
% 2.80/1.02  
% 2.80/1.02  --superposition_flag                    true
% 2.80/1.02  --sup_passive_queue_type                priority_queues
% 2.80/1.02  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 2.80/1.02  --sup_passive_queues_freq               [8;1;4]
% 2.80/1.02  --demod_completeness_check              fast
% 2.80/1.02  --demod_use_ground                      true
% 2.80/1.02  --sup_to_prop_solver                    passive
% 2.80/1.02  --sup_prop_simpl_new                    true
% 2.80/1.02  --sup_prop_simpl_given                  true
% 2.80/1.02  --sup_fun_splitting                     false
% 2.80/1.02  --sup_smt_interval                      50000
% 2.80/1.02  
% 2.80/1.02  ------ Superposition Simplification Setup
% 2.80/1.02  
% 2.80/1.02  --sup_indices_passive                   []
% 2.80/1.02  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.80/1.02  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.80/1.02  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.80/1.02  --sup_full_triv                         [TrivRules;PropSubs]
% 2.80/1.02  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.80/1.02  --sup_full_bw                           [BwDemod]
% 2.80/1.02  --sup_immed_triv                        [TrivRules]
% 2.80/1.02  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 2.80/1.02  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.80/1.02  --sup_immed_bw_main                     []
% 2.80/1.02  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.80/1.02  --sup_input_triv                        [Unflattening;TrivRules]
% 2.80/1.02  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.80/1.02  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.80/1.02  
% 2.80/1.02  ------ Combination Options
% 2.80/1.02  
% 2.80/1.02  --comb_res_mult                         3
% 2.80/1.02  --comb_sup_mult                         2
% 2.80/1.02  --comb_inst_mult                        10
% 2.80/1.02  
% 2.80/1.02  ------ Debug Options
% 2.80/1.02  
% 2.80/1.02  --dbg_backtrace                         false
% 2.80/1.02  --dbg_dump_prop_clauses                 false
% 2.80/1.02  --dbg_dump_prop_clauses_file            -
% 2.80/1.02  --dbg_out_stat                          false
% 2.80/1.02  
% 2.80/1.02  
% 2.80/1.02  
% 2.80/1.02  
% 2.80/1.02  ------ Proving...
% 2.80/1.02  
% 2.80/1.02  
% 2.80/1.02  % SZS status Theorem for theBenchmark.p
% 2.80/1.02  
% 2.80/1.02  % SZS output start CNFRefutation for theBenchmark.p
% 2.80/1.02  
% 2.80/1.02  fof(f5,axiom,(
% 2.80/1.02    ! [X0,X1] : (m1_subset_1(X0,X1) => (r2_hidden(X0,X1) | v1_xboole_0(X1)))),
% 2.80/1.02    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.80/1.02  
% 2.80/1.02  fof(f20,plain,(
% 2.80/1.02    ! [X0,X1] : ((r2_hidden(X0,X1) | v1_xboole_0(X1)) | ~m1_subset_1(X0,X1))),
% 2.80/1.02    inference(ennf_transformation,[],[f5])).
% 2.80/1.02  
% 2.80/1.02  fof(f21,plain,(
% 2.80/1.02    ! [X0,X1] : (r2_hidden(X0,X1) | v1_xboole_0(X1) | ~m1_subset_1(X0,X1))),
% 2.80/1.02    inference(flattening,[],[f20])).
% 2.80/1.02  
% 2.80/1.02  fof(f56,plain,(
% 2.80/1.02    ( ! [X0,X1] : (r2_hidden(X0,X1) | v1_xboole_0(X1) | ~m1_subset_1(X0,X1)) )),
% 2.80/1.02    inference(cnf_transformation,[],[f21])).
% 2.80/1.02  
% 2.80/1.02  fof(f7,axiom,(
% 2.80/1.02    ! [X0,X1,X2] : ((m1_subset_1(X1,k1_zfmisc_1(X2)) & r2_hidden(X0,X1)) => m1_subset_1(X0,X2))),
% 2.80/1.02    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.80/1.02  
% 2.80/1.02  fof(f22,plain,(
% 2.80/1.02    ! [X0,X1,X2] : (m1_subset_1(X0,X2) | (~m1_subset_1(X1,k1_zfmisc_1(X2)) | ~r2_hidden(X0,X1)))),
% 2.80/1.02    inference(ennf_transformation,[],[f7])).
% 2.80/1.02  
% 2.80/1.02  fof(f23,plain,(
% 2.80/1.02    ! [X0,X1,X2] : (m1_subset_1(X0,X2) | ~m1_subset_1(X1,k1_zfmisc_1(X2)) | ~r2_hidden(X0,X1))),
% 2.80/1.02    inference(flattening,[],[f22])).
% 2.80/1.02  
% 2.80/1.02  fof(f59,plain,(
% 2.80/1.02    ( ! [X2,X0,X1] : (m1_subset_1(X0,X2) | ~m1_subset_1(X1,k1_zfmisc_1(X2)) | ~r2_hidden(X0,X1)) )),
% 2.80/1.03    inference(cnf_transformation,[],[f23])).
% 2.80/1.03  
% 2.80/1.03  fof(f4,axiom,(
% 2.80/1.03    ! [X0,X1] : (r2_hidden(X0,X1) => m1_subset_1(X0,X1))),
% 2.80/1.03    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.80/1.03  
% 2.80/1.03  fof(f19,plain,(
% 2.80/1.03    ! [X0,X1] : (m1_subset_1(X0,X1) | ~r2_hidden(X0,X1))),
% 2.80/1.03    inference(ennf_transformation,[],[f4])).
% 2.80/1.03  
% 2.80/1.03  fof(f55,plain,(
% 2.80/1.03    ( ! [X0,X1] : (m1_subset_1(X0,X1) | ~r2_hidden(X0,X1)) )),
% 2.80/1.03    inference(cnf_transformation,[],[f19])).
% 2.80/1.03  
% 2.80/1.03  fof(f10,axiom,(
% 2.80/1.03    ! [X0] : (l1_orders_2(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => (v13_waybel_0(X1,X0) <=> ! [X2] : (m1_subset_1(X2,u1_struct_0(X0)) => ! [X3] : (m1_subset_1(X3,u1_struct_0(X0)) => ((r1_orders_2(X0,X2,X3) & r2_hidden(X2,X1)) => r2_hidden(X3,X1)))))))),
% 2.80/1.03    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.80/1.03  
% 2.80/1.03  fof(f27,plain,(
% 2.80/1.03    ! [X0] : (! [X1] : ((v13_waybel_0(X1,X0) <=> ! [X2] : (! [X3] : ((r2_hidden(X3,X1) | (~r1_orders_2(X0,X2,X3) | ~r2_hidden(X2,X1))) | ~m1_subset_1(X3,u1_struct_0(X0))) | ~m1_subset_1(X2,u1_struct_0(X0)))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_orders_2(X0))),
% 2.80/1.03    inference(ennf_transformation,[],[f10])).
% 2.80/1.03  
% 2.80/1.03  fof(f28,plain,(
% 2.80/1.03    ! [X0] : (! [X1] : ((v13_waybel_0(X1,X0) <=> ! [X2] : (! [X3] : (r2_hidden(X3,X1) | ~r1_orders_2(X0,X2,X3) | ~r2_hidden(X2,X1) | ~m1_subset_1(X3,u1_struct_0(X0))) | ~m1_subset_1(X2,u1_struct_0(X0)))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_orders_2(X0))),
% 2.80/1.03    inference(flattening,[],[f27])).
% 2.80/1.03  
% 2.80/1.03  fof(f38,plain,(
% 2.80/1.03    ! [X0] : (! [X1] : (((v13_waybel_0(X1,X0) | ? [X2] : (? [X3] : (~r2_hidden(X3,X1) & r1_orders_2(X0,X2,X3) & r2_hidden(X2,X1) & m1_subset_1(X3,u1_struct_0(X0))) & m1_subset_1(X2,u1_struct_0(X0)))) & (! [X2] : (! [X3] : (r2_hidden(X3,X1) | ~r1_orders_2(X0,X2,X3) | ~r2_hidden(X2,X1) | ~m1_subset_1(X3,u1_struct_0(X0))) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~v13_waybel_0(X1,X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_orders_2(X0))),
% 2.80/1.03    inference(nnf_transformation,[],[f28])).
% 2.80/1.03  
% 2.80/1.03  fof(f39,plain,(
% 2.80/1.03    ! [X0] : (! [X1] : (((v13_waybel_0(X1,X0) | ? [X2] : (? [X3] : (~r2_hidden(X3,X1) & r1_orders_2(X0,X2,X3) & r2_hidden(X2,X1) & m1_subset_1(X3,u1_struct_0(X0))) & m1_subset_1(X2,u1_struct_0(X0)))) & (! [X4] : (! [X5] : (r2_hidden(X5,X1) | ~r1_orders_2(X0,X4,X5) | ~r2_hidden(X4,X1) | ~m1_subset_1(X5,u1_struct_0(X0))) | ~m1_subset_1(X4,u1_struct_0(X0))) | ~v13_waybel_0(X1,X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_orders_2(X0))),
% 2.80/1.03    inference(rectify,[],[f38])).
% 2.80/1.03  
% 2.80/1.03  fof(f41,plain,(
% 2.80/1.03    ( ! [X2] : (! [X1,X0] : (? [X3] : (~r2_hidden(X3,X1) & r1_orders_2(X0,X2,X3) & r2_hidden(X2,X1) & m1_subset_1(X3,u1_struct_0(X0))) => (~r2_hidden(sK2(X0,X1),X1) & r1_orders_2(X0,X2,sK2(X0,X1)) & r2_hidden(X2,X1) & m1_subset_1(sK2(X0,X1),u1_struct_0(X0))))) )),
% 2.80/1.03    introduced(choice_axiom,[])).
% 2.80/1.03  
% 2.80/1.03  fof(f40,plain,(
% 2.80/1.03    ! [X1,X0] : (? [X2] : (? [X3] : (~r2_hidden(X3,X1) & r1_orders_2(X0,X2,X3) & r2_hidden(X2,X1) & m1_subset_1(X3,u1_struct_0(X0))) & m1_subset_1(X2,u1_struct_0(X0))) => (? [X3] : (~r2_hidden(X3,X1) & r1_orders_2(X0,sK1(X0,X1),X3) & r2_hidden(sK1(X0,X1),X1) & m1_subset_1(X3,u1_struct_0(X0))) & m1_subset_1(sK1(X0,X1),u1_struct_0(X0))))),
% 2.80/1.03    introduced(choice_axiom,[])).
% 2.80/1.03  
% 2.80/1.03  fof(f42,plain,(
% 2.80/1.03    ! [X0] : (! [X1] : (((v13_waybel_0(X1,X0) | ((~r2_hidden(sK2(X0,X1),X1) & r1_orders_2(X0,sK1(X0,X1),sK2(X0,X1)) & r2_hidden(sK1(X0,X1),X1) & m1_subset_1(sK2(X0,X1),u1_struct_0(X0))) & m1_subset_1(sK1(X0,X1),u1_struct_0(X0)))) & (! [X4] : (! [X5] : (r2_hidden(X5,X1) | ~r1_orders_2(X0,X4,X5) | ~r2_hidden(X4,X1) | ~m1_subset_1(X5,u1_struct_0(X0))) | ~m1_subset_1(X4,u1_struct_0(X0))) | ~v13_waybel_0(X1,X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_orders_2(X0))),
% 2.80/1.03    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1,sK2])],[f39,f41,f40])).
% 2.80/1.03  
% 2.80/1.03  fof(f62,plain,(
% 2.80/1.03    ( ! [X4,X0,X5,X1] : (r2_hidden(X5,X1) | ~r1_orders_2(X0,X4,X5) | ~r2_hidden(X4,X1) | ~m1_subset_1(X5,u1_struct_0(X0)) | ~m1_subset_1(X4,u1_struct_0(X0)) | ~v13_waybel_0(X1,X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_orders_2(X0)) )),
% 2.80/1.03    inference(cnf_transformation,[],[f42])).
% 2.80/1.03  
% 2.80/1.03  fof(f9,axiom,(
% 2.80/1.03    ! [X0] : ((l1_orders_2(X0) & v1_yellow_0(X0) & v5_orders_2(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,u1_struct_0(X0)) => r1_orders_2(X0,k3_yellow_0(X0),X1)))),
% 2.80/1.03    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.80/1.03  
% 2.80/1.03  fof(f25,plain,(
% 2.80/1.03    ! [X0] : (! [X1] : (r1_orders_2(X0,k3_yellow_0(X0),X1) | ~m1_subset_1(X1,u1_struct_0(X0))) | (~l1_orders_2(X0) | ~v1_yellow_0(X0) | ~v5_orders_2(X0) | v2_struct_0(X0)))),
% 2.80/1.03    inference(ennf_transformation,[],[f9])).
% 2.80/1.03  
% 2.80/1.03  fof(f26,plain,(
% 2.80/1.03    ! [X0] : (! [X1] : (r1_orders_2(X0,k3_yellow_0(X0),X1) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~l1_orders_2(X0) | ~v1_yellow_0(X0) | ~v5_orders_2(X0) | v2_struct_0(X0))),
% 2.80/1.03    inference(flattening,[],[f25])).
% 2.80/1.03  
% 2.80/1.03  fof(f61,plain,(
% 2.80/1.03    ( ! [X0,X1] : (r1_orders_2(X0,k3_yellow_0(X0),X1) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_orders_2(X0) | ~v1_yellow_0(X0) | ~v5_orders_2(X0) | v2_struct_0(X0)) )),
% 2.80/1.03    inference(cnf_transformation,[],[f26])).
% 2.80/1.03  
% 2.80/1.03  fof(f12,conjecture,(
% 2.80/1.03    ! [X0] : ((l1_orders_2(X0) & v1_yellow_0(X0) & v5_orders_2(X0) & v4_orders_2(X0) & v3_orders_2(X0) & ~v2_struct_0(X0)) => ! [X1] : ((m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & v13_waybel_0(X1,X0) & v2_waybel_0(X1,X0) & ~v1_xboole_0(X1)) => (v1_subset_1(X1,u1_struct_0(X0)) <=> ~r2_hidden(k3_yellow_0(X0),X1))))),
% 2.80/1.03    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.80/1.03  
% 2.80/1.03  fof(f13,negated_conjecture,(
% 2.80/1.03    ~! [X0] : ((l1_orders_2(X0) & v1_yellow_0(X0) & v5_orders_2(X0) & v4_orders_2(X0) & v3_orders_2(X0) & ~v2_struct_0(X0)) => ! [X1] : ((m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & v13_waybel_0(X1,X0) & v2_waybel_0(X1,X0) & ~v1_xboole_0(X1)) => (v1_subset_1(X1,u1_struct_0(X0)) <=> ~r2_hidden(k3_yellow_0(X0),X1))))),
% 2.80/1.03    inference(negated_conjecture,[],[f12])).
% 2.80/1.03  
% 2.80/1.03  fof(f14,plain,(
% 2.80/1.03    ~! [X0] : ((l1_orders_2(X0) & v1_yellow_0(X0) & v5_orders_2(X0) & v4_orders_2(X0) & v3_orders_2(X0) & ~v2_struct_0(X0)) => ! [X1] : ((m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & v13_waybel_0(X1,X0) & ~v1_xboole_0(X1)) => (v1_subset_1(X1,u1_struct_0(X0)) <=> ~r2_hidden(k3_yellow_0(X0),X1))))),
% 2.80/1.03    inference(pure_predicate_removal,[],[f13])).
% 2.80/1.03  
% 2.80/1.03  fof(f15,plain,(
% 2.80/1.03    ~! [X0] : ((l1_orders_2(X0) & v1_yellow_0(X0) & v5_orders_2(X0) & v3_orders_2(X0) & ~v2_struct_0(X0)) => ! [X1] : ((m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & v13_waybel_0(X1,X0) & ~v1_xboole_0(X1)) => (v1_subset_1(X1,u1_struct_0(X0)) <=> ~r2_hidden(k3_yellow_0(X0),X1))))),
% 2.80/1.03    inference(pure_predicate_removal,[],[f14])).
% 2.80/1.03  
% 2.80/1.03  fof(f16,plain,(
% 2.80/1.03    ~! [X0] : ((l1_orders_2(X0) & v1_yellow_0(X0) & v5_orders_2(X0) & ~v2_struct_0(X0)) => ! [X1] : ((m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & v13_waybel_0(X1,X0) & ~v1_xboole_0(X1)) => (v1_subset_1(X1,u1_struct_0(X0)) <=> ~r2_hidden(k3_yellow_0(X0),X1))))),
% 2.80/1.03    inference(pure_predicate_removal,[],[f15])).
% 2.80/1.03  
% 2.80/1.03  fof(f30,plain,(
% 2.80/1.03    ? [X0] : (? [X1] : ((v1_subset_1(X1,u1_struct_0(X0)) <~> ~r2_hidden(k3_yellow_0(X0),X1)) & (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & v13_waybel_0(X1,X0) & ~v1_xboole_0(X1))) & (l1_orders_2(X0) & v1_yellow_0(X0) & v5_orders_2(X0) & ~v2_struct_0(X0)))),
% 2.80/1.03    inference(ennf_transformation,[],[f16])).
% 2.80/1.03  
% 2.80/1.03  fof(f31,plain,(
% 2.80/1.03    ? [X0] : (? [X1] : ((v1_subset_1(X1,u1_struct_0(X0)) <~> ~r2_hidden(k3_yellow_0(X0),X1)) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & v13_waybel_0(X1,X0) & ~v1_xboole_0(X1)) & l1_orders_2(X0) & v1_yellow_0(X0) & v5_orders_2(X0) & ~v2_struct_0(X0))),
% 2.80/1.03    inference(flattening,[],[f30])).
% 2.80/1.03  
% 2.80/1.03  fof(f44,plain,(
% 2.80/1.03    ? [X0] : (? [X1] : (((r2_hidden(k3_yellow_0(X0),X1) | ~v1_subset_1(X1,u1_struct_0(X0))) & (~r2_hidden(k3_yellow_0(X0),X1) | v1_subset_1(X1,u1_struct_0(X0)))) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & v13_waybel_0(X1,X0) & ~v1_xboole_0(X1)) & l1_orders_2(X0) & v1_yellow_0(X0) & v5_orders_2(X0) & ~v2_struct_0(X0))),
% 2.80/1.03    inference(nnf_transformation,[],[f31])).
% 2.80/1.03  
% 2.80/1.03  fof(f45,plain,(
% 2.80/1.03    ? [X0] : (? [X1] : ((r2_hidden(k3_yellow_0(X0),X1) | ~v1_subset_1(X1,u1_struct_0(X0))) & (~r2_hidden(k3_yellow_0(X0),X1) | v1_subset_1(X1,u1_struct_0(X0))) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & v13_waybel_0(X1,X0) & ~v1_xboole_0(X1)) & l1_orders_2(X0) & v1_yellow_0(X0) & v5_orders_2(X0) & ~v2_struct_0(X0))),
% 2.80/1.03    inference(flattening,[],[f44])).
% 2.80/1.03  
% 2.80/1.03  fof(f47,plain,(
% 2.80/1.03    ( ! [X0] : (? [X1] : ((r2_hidden(k3_yellow_0(X0),X1) | ~v1_subset_1(X1,u1_struct_0(X0))) & (~r2_hidden(k3_yellow_0(X0),X1) | v1_subset_1(X1,u1_struct_0(X0))) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & v13_waybel_0(X1,X0) & ~v1_xboole_0(X1)) => ((r2_hidden(k3_yellow_0(X0),sK4) | ~v1_subset_1(sK4,u1_struct_0(X0))) & (~r2_hidden(k3_yellow_0(X0),sK4) | v1_subset_1(sK4,u1_struct_0(X0))) & m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(X0))) & v13_waybel_0(sK4,X0) & ~v1_xboole_0(sK4))) )),
% 2.80/1.03    introduced(choice_axiom,[])).
% 2.80/1.03  
% 2.80/1.03  fof(f46,plain,(
% 2.80/1.03    ? [X0] : (? [X1] : ((r2_hidden(k3_yellow_0(X0),X1) | ~v1_subset_1(X1,u1_struct_0(X0))) & (~r2_hidden(k3_yellow_0(X0),X1) | v1_subset_1(X1,u1_struct_0(X0))) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & v13_waybel_0(X1,X0) & ~v1_xboole_0(X1)) & l1_orders_2(X0) & v1_yellow_0(X0) & v5_orders_2(X0) & ~v2_struct_0(X0)) => (? [X1] : ((r2_hidden(k3_yellow_0(sK3),X1) | ~v1_subset_1(X1,u1_struct_0(sK3))) & (~r2_hidden(k3_yellow_0(sK3),X1) | v1_subset_1(X1,u1_struct_0(sK3))) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK3))) & v13_waybel_0(X1,sK3) & ~v1_xboole_0(X1)) & l1_orders_2(sK3) & v1_yellow_0(sK3) & v5_orders_2(sK3) & ~v2_struct_0(sK3))),
% 2.80/1.03    introduced(choice_axiom,[])).
% 2.80/1.03  
% 2.80/1.03  fof(f48,plain,(
% 2.80/1.03    ((r2_hidden(k3_yellow_0(sK3),sK4) | ~v1_subset_1(sK4,u1_struct_0(sK3))) & (~r2_hidden(k3_yellow_0(sK3),sK4) | v1_subset_1(sK4,u1_struct_0(sK3))) & m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(sK3))) & v13_waybel_0(sK4,sK3) & ~v1_xboole_0(sK4)) & l1_orders_2(sK3) & v1_yellow_0(sK3) & v5_orders_2(sK3) & ~v2_struct_0(sK3)),
% 2.80/1.03    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3,sK4])],[f45,f47,f46])).
% 2.80/1.03  
% 2.80/1.03  fof(f72,plain,(
% 2.80/1.03    v1_yellow_0(sK3)),
% 2.80/1.03    inference(cnf_transformation,[],[f48])).
% 2.80/1.03  
% 2.80/1.03  fof(f70,plain,(
% 2.80/1.03    ~v2_struct_0(sK3)),
% 2.80/1.03    inference(cnf_transformation,[],[f48])).
% 2.80/1.03  
% 2.80/1.03  fof(f71,plain,(
% 2.80/1.03    v5_orders_2(sK3)),
% 2.80/1.03    inference(cnf_transformation,[],[f48])).
% 2.80/1.03  
% 2.80/1.03  fof(f73,plain,(
% 2.80/1.03    l1_orders_2(sK3)),
% 2.80/1.03    inference(cnf_transformation,[],[f48])).
% 2.80/1.03  
% 2.80/1.03  fof(f8,axiom,(
% 2.80/1.03    ! [X0] : (l1_orders_2(X0) => m1_subset_1(k3_yellow_0(X0),u1_struct_0(X0)))),
% 2.80/1.03    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.80/1.03  
% 2.80/1.03  fof(f24,plain,(
% 2.80/1.03    ! [X0] : (m1_subset_1(k3_yellow_0(X0),u1_struct_0(X0)) | ~l1_orders_2(X0))),
% 2.80/1.03    inference(ennf_transformation,[],[f8])).
% 2.80/1.03  
% 2.80/1.03  fof(f60,plain,(
% 2.80/1.03    ( ! [X0] : (m1_subset_1(k3_yellow_0(X0),u1_struct_0(X0)) | ~l1_orders_2(X0)) )),
% 2.80/1.03    inference(cnf_transformation,[],[f24])).
% 2.80/1.03  
% 2.80/1.03  fof(f76,plain,(
% 2.80/1.03    m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(sK3)))),
% 2.80/1.03    inference(cnf_transformation,[],[f48])).
% 2.80/1.03  
% 2.80/1.03  fof(f6,axiom,(
% 2.80/1.03    ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) <=> r1_tarski(X0,X1))),
% 2.80/1.03    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.80/1.03  
% 2.80/1.03  fof(f37,plain,(
% 2.80/1.03    ! [X0,X1] : ((m1_subset_1(X0,k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1)) & (r1_tarski(X0,X1) | ~m1_subset_1(X0,k1_zfmisc_1(X1))))),
% 2.80/1.03    inference(nnf_transformation,[],[f6])).
% 2.80/1.03  
% 2.80/1.03  fof(f57,plain,(
% 2.80/1.03    ( ! [X0,X1] : (r1_tarski(X0,X1) | ~m1_subset_1(X0,k1_zfmisc_1(X1))) )),
% 2.80/1.03    inference(cnf_transformation,[],[f37])).
% 2.80/1.03  
% 2.80/1.03  fof(f3,axiom,(
% 2.80/1.03    ! [X0] : (v1_xboole_0(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => v1_xboole_0(X1)))),
% 2.80/1.03    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.80/1.03  
% 2.80/1.03  fof(f18,plain,(
% 2.80/1.03    ! [X0] : (! [X1] : (v1_xboole_0(X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) | ~v1_xboole_0(X0))),
% 2.80/1.03    inference(ennf_transformation,[],[f3])).
% 2.80/1.03  
% 2.80/1.03  fof(f54,plain,(
% 2.80/1.03    ( ! [X0,X1] : (v1_xboole_0(X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0)) | ~v1_xboole_0(X0)) )),
% 2.80/1.03    inference(cnf_transformation,[],[f18])).
% 2.80/1.03  
% 2.80/1.03  fof(f58,plain,(
% 2.80/1.03    ( ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1)) )),
% 2.80/1.03    inference(cnf_transformation,[],[f37])).
% 2.80/1.03  
% 2.80/1.03  fof(f11,axiom,(
% 2.80/1.03    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => (v1_subset_1(X1,X0) <=> X0 != X1))),
% 2.80/1.03    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.80/1.03  
% 2.80/1.03  fof(f29,plain,(
% 2.80/1.03    ! [X0,X1] : ((v1_subset_1(X1,X0) <=> X0 != X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 2.80/1.03    inference(ennf_transformation,[],[f11])).
% 2.80/1.03  
% 2.80/1.03  fof(f43,plain,(
% 2.80/1.03    ! [X0,X1] : (((v1_subset_1(X1,X0) | X0 = X1) & (X0 != X1 | ~v1_subset_1(X1,X0))) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 2.80/1.03    inference(nnf_transformation,[],[f29])).
% 2.80/1.03  
% 2.80/1.03  fof(f68,plain,(
% 2.80/1.03    ( ! [X0,X1] : (X0 != X1 | ~v1_subset_1(X1,X0) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 2.80/1.03    inference(cnf_transformation,[],[f43])).
% 2.80/1.03  
% 2.80/1.03  fof(f81,plain,(
% 2.80/1.03    ( ! [X1] : (~v1_subset_1(X1,X1) | ~m1_subset_1(X1,k1_zfmisc_1(X1))) )),
% 2.80/1.03    inference(equality_resolution,[],[f68])).
% 2.80/1.03  
% 2.80/1.03  fof(f77,plain,(
% 2.80/1.03    ~r2_hidden(k3_yellow_0(sK3),sK4) | v1_subset_1(sK4,u1_struct_0(sK3))),
% 2.80/1.03    inference(cnf_transformation,[],[f48])).
% 2.80/1.03  
% 2.80/1.03  fof(f2,axiom,(
% 2.80/1.03    ! [X0,X1] : (X0 = X1 <=> (r1_tarski(X1,X0) & r1_tarski(X0,X1)))),
% 2.80/1.03    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.80/1.03  
% 2.80/1.03  fof(f35,plain,(
% 2.80/1.03    ! [X0,X1] : ((X0 = X1 | (~r1_tarski(X1,X0) | ~r1_tarski(X0,X1))) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 2.80/1.03    inference(nnf_transformation,[],[f2])).
% 2.80/1.03  
% 2.80/1.03  fof(f36,plain,(
% 2.80/1.03    ! [X0,X1] : ((X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 2.80/1.03    inference(flattening,[],[f35])).
% 2.80/1.03  
% 2.80/1.03  fof(f51,plain,(
% 2.80/1.03    ( ! [X0,X1] : (r1_tarski(X0,X1) | X0 != X1) )),
% 2.80/1.03    inference(cnf_transformation,[],[f36])).
% 2.80/1.03  
% 2.80/1.03  fof(f80,plain,(
% 2.80/1.03    ( ! [X1] : (r1_tarski(X1,X1)) )),
% 2.80/1.03    inference(equality_resolution,[],[f51])).
% 2.80/1.03  
% 2.80/1.03  fof(f1,axiom,(
% 2.80/1.03    ! [X0,X1] : (! [X2] : (r2_hidden(X2,X0) <=> r2_hidden(X2,X1)) => X0 = X1)),
% 2.80/1.03    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.80/1.03  
% 2.80/1.03  fof(f17,plain,(
% 2.80/1.03    ! [X0,X1] : (X0 = X1 | ? [X2] : (r2_hidden(X2,X0) <~> r2_hidden(X2,X1)))),
% 2.80/1.03    inference(ennf_transformation,[],[f1])).
% 2.80/1.03  
% 2.80/1.03  fof(f32,plain,(
% 2.80/1.03    ! [X0,X1] : (X0 = X1 | ? [X2] : ((~r2_hidden(X2,X1) | ~r2_hidden(X2,X0)) & (r2_hidden(X2,X1) | r2_hidden(X2,X0))))),
% 2.80/1.03    inference(nnf_transformation,[],[f17])).
% 2.80/1.03  
% 2.80/1.03  fof(f33,plain,(
% 2.80/1.03    ! [X1,X0] : (? [X2] : ((~r2_hidden(X2,X1) | ~r2_hidden(X2,X0)) & (r2_hidden(X2,X1) | r2_hidden(X2,X0))) => ((~r2_hidden(sK0(X0,X1),X1) | ~r2_hidden(sK0(X0,X1),X0)) & (r2_hidden(sK0(X0,X1),X1) | r2_hidden(sK0(X0,X1),X0))))),
% 2.80/1.03    introduced(choice_axiom,[])).
% 2.80/1.03  
% 2.80/1.03  fof(f34,plain,(
% 2.80/1.03    ! [X0,X1] : (X0 = X1 | ((~r2_hidden(sK0(X0,X1),X1) | ~r2_hidden(sK0(X0,X1),X0)) & (r2_hidden(sK0(X0,X1),X1) | r2_hidden(sK0(X0,X1),X0))))),
% 2.80/1.03    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f32,f33])).
% 2.80/1.03  
% 2.80/1.03  fof(f50,plain,(
% 2.80/1.03    ( ! [X0,X1] : (X0 = X1 | ~r2_hidden(sK0(X0,X1),X1) | ~r2_hidden(sK0(X0,X1),X0)) )),
% 2.80/1.03    inference(cnf_transformation,[],[f34])).
% 2.80/1.03  
% 2.80/1.03  fof(f49,plain,(
% 2.80/1.03    ( ! [X0,X1] : (X0 = X1 | r2_hidden(sK0(X0,X1),X1) | r2_hidden(sK0(X0,X1),X0)) )),
% 2.80/1.03    inference(cnf_transformation,[],[f34])).
% 2.80/1.03  
% 2.80/1.03  fof(f69,plain,(
% 2.80/1.03    ( ! [X0,X1] : (v1_subset_1(X1,X0) | X0 = X1 | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 2.80/1.03    inference(cnf_transformation,[],[f43])).
% 2.80/1.03  
% 2.80/1.03  fof(f78,plain,(
% 2.80/1.03    r2_hidden(k3_yellow_0(sK3),sK4) | ~v1_subset_1(sK4,u1_struct_0(sK3))),
% 2.80/1.03    inference(cnf_transformation,[],[f48])).
% 2.80/1.03  
% 2.80/1.03  fof(f75,plain,(
% 2.80/1.03    v13_waybel_0(sK4,sK3)),
% 2.80/1.03    inference(cnf_transformation,[],[f48])).
% 2.80/1.03  
% 2.80/1.03  fof(f74,plain,(
% 2.80/1.03    ~v1_xboole_0(sK4)),
% 2.80/1.03    inference(cnf_transformation,[],[f48])).
% 2.80/1.03  
% 2.80/1.03  cnf(c_7,plain,
% 2.80/1.03      ( ~ m1_subset_1(X0,X1) | r2_hidden(X0,X1) | v1_xboole_0(X1) ),
% 2.80/1.03      inference(cnf_transformation,[],[f56]) ).
% 2.80/1.03  
% 2.80/1.03  cnf(c_6980,plain,
% 2.80/1.03      ( ~ m1_subset_1(sK0(sK4,u1_struct_0(sK3)),u1_struct_0(sK3))
% 2.80/1.03      | r2_hidden(sK0(sK4,u1_struct_0(sK3)),u1_struct_0(sK3))
% 2.80/1.03      | v1_xboole_0(u1_struct_0(sK3)) ),
% 2.80/1.03      inference(instantiation,[status(thm)],[c_7]) ).
% 2.80/1.03  
% 2.80/1.03  cnf(c_6981,plain,
% 2.80/1.03      ( m1_subset_1(sK0(sK4,u1_struct_0(sK3)),u1_struct_0(sK3)) != iProver_top
% 2.80/1.03      | r2_hidden(sK0(sK4,u1_struct_0(sK3)),u1_struct_0(sK3)) = iProver_top
% 2.80/1.03      | v1_xboole_0(u1_struct_0(sK3)) = iProver_top ),
% 2.80/1.03      inference(predicate_to_equality,[status(thm)],[c_6980]) ).
% 2.80/1.03  
% 2.80/1.03  cnf(c_841,plain,( X0 != X1 | X2 != X1 | X2 = X0 ),theory(equality) ).
% 2.80/1.03  
% 2.80/1.03  cnf(c_1735,plain,
% 2.80/1.03      ( X0 != X1 | X0 = u1_struct_0(sK3) | u1_struct_0(sK3) != X1 ),
% 2.80/1.03      inference(instantiation,[status(thm)],[c_841]) ).
% 2.80/1.03  
% 2.80/1.03  cnf(c_1962,plain,
% 2.80/1.03      ( u1_struct_0(sK3) != X0 | sK4 != X0 | sK4 = u1_struct_0(sK3) ),
% 2.80/1.03      inference(instantiation,[status(thm)],[c_1735]) ).
% 2.80/1.03  
% 2.80/1.03  cnf(c_5579,plain,
% 2.80/1.03      ( u1_struct_0(sK3) != sK4 | sK4 = u1_struct_0(sK3) | sK4 != sK4 ),
% 2.80/1.03      inference(instantiation,[status(thm)],[c_1962]) ).
% 2.80/1.03  
% 2.80/1.03  cnf(c_10,plain,
% 2.80/1.03      ( m1_subset_1(X0,X1)
% 2.80/1.03      | ~ m1_subset_1(X2,k1_zfmisc_1(X1))
% 2.80/1.03      | ~ r2_hidden(X0,X2) ),
% 2.80/1.03      inference(cnf_transformation,[],[f59]) ).
% 2.80/1.03  
% 2.80/1.03  cnf(c_1649,plain,
% 2.80/1.03      ( m1_subset_1(X0,X1)
% 2.80/1.03      | ~ m1_subset_1(sK4,k1_zfmisc_1(X1))
% 2.80/1.03      | ~ r2_hidden(X0,sK4) ),
% 2.80/1.03      inference(instantiation,[status(thm)],[c_10]) ).
% 2.80/1.03  
% 2.80/1.03  cnf(c_4051,plain,
% 2.80/1.03      ( m1_subset_1(sK0(sK4,u1_struct_0(sK3)),u1_struct_0(sK3))
% 2.80/1.03      | ~ m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(sK3)))
% 2.80/1.03      | ~ r2_hidden(sK0(sK4,u1_struct_0(sK3)),sK4) ),
% 2.80/1.03      inference(instantiation,[status(thm)],[c_1649]) ).
% 2.80/1.03  
% 2.80/1.03  cnf(c_4067,plain,
% 2.80/1.03      ( m1_subset_1(sK0(sK4,u1_struct_0(sK3)),u1_struct_0(sK3)) = iProver_top
% 2.80/1.03      | m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(sK3))) != iProver_top
% 2.80/1.03      | r2_hidden(sK0(sK4,u1_struct_0(sK3)),sK4) != iProver_top ),
% 2.80/1.03      inference(predicate_to_equality,[status(thm)],[c_4051]) ).
% 2.80/1.03  
% 2.80/1.03  cnf(c_6,plain,
% 2.80/1.03      ( m1_subset_1(X0,X1) | ~ r2_hidden(X0,X1) ),
% 2.80/1.03      inference(cnf_transformation,[],[f55]) ).
% 2.80/1.03  
% 2.80/1.03  cnf(c_4055,plain,
% 2.80/1.03      ( m1_subset_1(sK0(sK4,u1_struct_0(sK3)),u1_struct_0(sK3))
% 2.80/1.03      | ~ r2_hidden(sK0(sK4,u1_struct_0(sK3)),u1_struct_0(sK3)) ),
% 2.80/1.03      inference(instantiation,[status(thm)],[c_6]) ).
% 2.80/1.03  
% 2.80/1.03  cnf(c_4057,plain,
% 2.80/1.03      ( m1_subset_1(sK0(sK4,u1_struct_0(sK3)),u1_struct_0(sK3)) = iProver_top
% 2.80/1.03      | r2_hidden(sK0(sK4,u1_struct_0(sK3)),u1_struct_0(sK3)) != iProver_top ),
% 2.80/1.03      inference(predicate_to_equality,[status(thm)],[c_4055]) ).
% 2.80/1.03  
% 2.80/1.03  cnf(c_18,plain,
% 2.80/1.03      ( ~ r1_orders_2(X0,X1,X2)
% 2.80/1.03      | ~ v13_waybel_0(X3,X0)
% 2.80/1.03      | ~ m1_subset_1(X2,u1_struct_0(X0))
% 2.80/1.03      | ~ m1_subset_1(X1,u1_struct_0(X0))
% 2.80/1.03      | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))
% 2.80/1.03      | ~ r2_hidden(X1,X3)
% 2.80/1.03      | r2_hidden(X2,X3)
% 2.80/1.03      | ~ l1_orders_2(X0) ),
% 2.80/1.03      inference(cnf_transformation,[],[f62]) ).
% 2.80/1.03  
% 2.80/1.03  cnf(c_12,plain,
% 2.80/1.03      ( r1_orders_2(X0,k3_yellow_0(X0),X1)
% 2.80/1.03      | ~ m1_subset_1(X1,u1_struct_0(X0))
% 2.80/1.03      | v2_struct_0(X0)
% 2.80/1.03      | ~ v5_orders_2(X0)
% 2.80/1.03      | ~ v1_yellow_0(X0)
% 2.80/1.03      | ~ l1_orders_2(X0) ),
% 2.80/1.03      inference(cnf_transformation,[],[f61]) ).
% 2.80/1.03  
% 2.80/1.03  cnf(c_27,negated_conjecture,
% 2.80/1.03      ( v1_yellow_0(sK3) ),
% 2.80/1.03      inference(cnf_transformation,[],[f72]) ).
% 2.80/1.03  
% 2.80/1.03  cnf(c_397,plain,
% 2.80/1.03      ( r1_orders_2(X0,k3_yellow_0(X0),X1)
% 2.80/1.03      | ~ m1_subset_1(X1,u1_struct_0(X0))
% 2.80/1.03      | v2_struct_0(X0)
% 2.80/1.03      | ~ v5_orders_2(X0)
% 2.80/1.03      | ~ l1_orders_2(X0)
% 2.80/1.03      | sK3 != X0 ),
% 2.80/1.03      inference(resolution_lifted,[status(thm)],[c_12,c_27]) ).
% 2.80/1.03  
% 2.80/1.03  cnf(c_398,plain,
% 2.80/1.03      ( r1_orders_2(sK3,k3_yellow_0(sK3),X0)
% 2.80/1.03      | ~ m1_subset_1(X0,u1_struct_0(sK3))
% 2.80/1.03      | v2_struct_0(sK3)
% 2.80/1.03      | ~ v5_orders_2(sK3)
% 2.80/1.03      | ~ l1_orders_2(sK3) ),
% 2.80/1.03      inference(unflattening,[status(thm)],[c_397]) ).
% 2.80/1.03  
% 2.80/1.03  cnf(c_29,negated_conjecture,
% 2.80/1.03      ( ~ v2_struct_0(sK3) ),
% 2.80/1.03      inference(cnf_transformation,[],[f70]) ).
% 2.80/1.03  
% 2.80/1.03  cnf(c_28,negated_conjecture,
% 2.80/1.03      ( v5_orders_2(sK3) ),
% 2.80/1.03      inference(cnf_transformation,[],[f71]) ).
% 2.80/1.03  
% 2.80/1.03  cnf(c_26,negated_conjecture,
% 2.80/1.03      ( l1_orders_2(sK3) ),
% 2.80/1.03      inference(cnf_transformation,[],[f73]) ).
% 2.80/1.03  
% 2.80/1.03  cnf(c_402,plain,
% 2.80/1.03      ( ~ m1_subset_1(X0,u1_struct_0(sK3))
% 2.80/1.03      | r1_orders_2(sK3,k3_yellow_0(sK3),X0) ),
% 2.80/1.03      inference(global_propositional_subsumption,
% 2.80/1.03                [status(thm)],
% 2.80/1.03                [c_398,c_29,c_28,c_26]) ).
% 2.80/1.03  
% 2.80/1.03  cnf(c_403,plain,
% 2.80/1.03      ( r1_orders_2(sK3,k3_yellow_0(sK3),X0)
% 2.80/1.03      | ~ m1_subset_1(X0,u1_struct_0(sK3)) ),
% 2.80/1.03      inference(renaming,[status(thm)],[c_402]) ).
% 2.80/1.03  
% 2.80/1.03  cnf(c_485,plain,
% 2.80/1.03      ( ~ v13_waybel_0(X0,X1)
% 2.80/1.03      | ~ m1_subset_1(X2,u1_struct_0(X1))
% 2.80/1.03      | ~ m1_subset_1(X3,u1_struct_0(X1))
% 2.80/1.03      | ~ m1_subset_1(X4,u1_struct_0(sK3))
% 2.80/1.03      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 2.80/1.03      | ~ r2_hidden(X2,X0)
% 2.80/1.03      | r2_hidden(X3,X0)
% 2.80/1.03      | ~ l1_orders_2(X1)
% 2.80/1.03      | X4 != X3
% 2.80/1.03      | k3_yellow_0(sK3) != X2
% 2.80/1.03      | sK3 != X1 ),
% 2.80/1.03      inference(resolution_lifted,[status(thm)],[c_18,c_403]) ).
% 2.80/1.03  
% 2.80/1.03  cnf(c_486,plain,
% 2.80/1.03      ( ~ v13_waybel_0(X0,sK3)
% 2.80/1.03      | ~ m1_subset_1(X1,u1_struct_0(sK3))
% 2.80/1.03      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK3)))
% 2.80/1.03      | ~ m1_subset_1(k3_yellow_0(sK3),u1_struct_0(sK3))
% 2.80/1.03      | r2_hidden(X1,X0)
% 2.80/1.03      | ~ r2_hidden(k3_yellow_0(sK3),X0)
% 2.80/1.03      | ~ l1_orders_2(sK3) ),
% 2.80/1.03      inference(unflattening,[status(thm)],[c_485]) ).
% 2.80/1.03  
% 2.80/1.03  cnf(c_11,plain,
% 2.80/1.03      ( m1_subset_1(k3_yellow_0(X0),u1_struct_0(X0))
% 2.80/1.03      | ~ l1_orders_2(X0) ),
% 2.80/1.03      inference(cnf_transformation,[],[f60]) ).
% 2.80/1.03  
% 2.80/1.03  cnf(c_65,plain,
% 2.80/1.03      ( m1_subset_1(k3_yellow_0(sK3),u1_struct_0(sK3))
% 2.80/1.03      | ~ l1_orders_2(sK3) ),
% 2.80/1.03      inference(instantiation,[status(thm)],[c_11]) ).
% 2.80/1.03  
% 2.80/1.03  cnf(c_490,plain,
% 2.80/1.03      ( ~ r2_hidden(k3_yellow_0(sK3),X0)
% 2.80/1.03      | r2_hidden(X1,X0)
% 2.80/1.03      | ~ v13_waybel_0(X0,sK3)
% 2.80/1.03      | ~ m1_subset_1(X1,u1_struct_0(sK3))
% 2.80/1.03      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK3))) ),
% 2.80/1.03      inference(global_propositional_subsumption,
% 2.80/1.03                [status(thm)],
% 2.80/1.03                [c_486,c_26,c_65]) ).
% 2.80/1.03  
% 2.80/1.03  cnf(c_491,plain,
% 2.80/1.03      ( ~ v13_waybel_0(X0,sK3)
% 2.80/1.03      | ~ m1_subset_1(X1,u1_struct_0(sK3))
% 2.80/1.03      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK3)))
% 2.80/1.03      | r2_hidden(X1,X0)
% 2.80/1.03      | ~ r2_hidden(k3_yellow_0(sK3),X0) ),
% 2.80/1.03      inference(renaming,[status(thm)],[c_490]) ).
% 2.80/1.03  
% 2.80/1.03  cnf(c_1578,plain,
% 2.80/1.03      ( ~ v13_waybel_0(sK4,sK3)
% 2.80/1.03      | ~ m1_subset_1(X0,u1_struct_0(sK3))
% 2.80/1.03      | ~ m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(sK3)))
% 2.80/1.03      | r2_hidden(X0,sK4)
% 2.80/1.03      | ~ r2_hidden(k3_yellow_0(sK3),sK4) ),
% 2.80/1.03      inference(instantiation,[status(thm)],[c_491]) ).
% 2.80/1.03  
% 2.80/1.03  cnf(c_3343,plain,
% 2.80/1.03      ( ~ v13_waybel_0(sK4,sK3)
% 2.80/1.03      | ~ m1_subset_1(sK0(sK4,u1_struct_0(sK3)),u1_struct_0(sK3))
% 2.80/1.03      | ~ m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(sK3)))
% 2.80/1.03      | r2_hidden(sK0(sK4,u1_struct_0(sK3)),sK4)
% 2.80/1.03      | ~ r2_hidden(k3_yellow_0(sK3),sK4) ),
% 2.80/1.03      inference(instantiation,[status(thm)],[c_1578]) ).
% 2.80/1.03  
% 2.80/1.03  cnf(c_3344,plain,
% 2.80/1.03      ( v13_waybel_0(sK4,sK3) != iProver_top
% 2.80/1.03      | m1_subset_1(sK0(sK4,u1_struct_0(sK3)),u1_struct_0(sK3)) != iProver_top
% 2.80/1.03      | m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(sK3))) != iProver_top
% 2.80/1.03      | r2_hidden(sK0(sK4,u1_struct_0(sK3)),sK4) = iProver_top
% 2.80/1.03      | r2_hidden(k3_yellow_0(sK3),sK4) != iProver_top ),
% 2.80/1.03      inference(predicate_to_equality,[status(thm)],[c_3343]) ).
% 2.80/1.03  
% 2.80/1.03  cnf(c_23,negated_conjecture,
% 2.80/1.03      ( m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(sK3))) ),
% 2.80/1.03      inference(cnf_transformation,[],[f76]) ).
% 2.80/1.03  
% 2.80/1.03  cnf(c_1394,plain,
% 2.80/1.03      ( m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(sK3))) = iProver_top ),
% 2.80/1.03      inference(predicate_to_equality,[status(thm)],[c_23]) ).
% 2.80/1.03  
% 2.80/1.03  cnf(c_9,plain,
% 2.80/1.03      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1)) | r1_tarski(X0,X1) ),
% 2.80/1.03      inference(cnf_transformation,[],[f57]) ).
% 2.80/1.03  
% 2.80/1.03  cnf(c_1396,plain,
% 2.80/1.03      ( m1_subset_1(X0,k1_zfmisc_1(X1)) != iProver_top
% 2.80/1.03      | r1_tarski(X0,X1) = iProver_top ),
% 2.80/1.03      inference(predicate_to_equality,[status(thm)],[c_9]) ).
% 2.80/1.03  
% 2.80/1.03  cnf(c_1839,plain,
% 2.80/1.03      ( r1_tarski(sK4,u1_struct_0(sK3)) = iProver_top ),
% 2.80/1.03      inference(superposition,[status(thm)],[c_1394,c_1396]) ).
% 2.80/1.03  
% 2.80/1.03  cnf(c_5,plain,
% 2.80/1.03      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
% 2.80/1.03      | ~ v1_xboole_0(X1)
% 2.80/1.03      | v1_xboole_0(X0) ),
% 2.80/1.03      inference(cnf_transformation,[],[f54]) ).
% 2.80/1.03  
% 2.80/1.03  cnf(c_8,plain,
% 2.80/1.03      ( m1_subset_1(X0,k1_zfmisc_1(X1)) | ~ r1_tarski(X0,X1) ),
% 2.80/1.03      inference(cnf_transformation,[],[f58]) ).
% 2.80/1.03  
% 2.80/1.03  cnf(c_224,plain,
% 2.80/1.03      ( ~ r1_tarski(X0,X1) | m1_subset_1(X0,k1_zfmisc_1(X1)) ),
% 2.80/1.03      inference(prop_impl,[status(thm)],[c_8]) ).
% 2.80/1.03  
% 2.80/1.03  cnf(c_225,plain,
% 2.80/1.03      ( m1_subset_1(X0,k1_zfmisc_1(X1)) | ~ r1_tarski(X0,X1) ),
% 2.80/1.03      inference(renaming,[status(thm)],[c_224]) ).
% 2.80/1.03  
% 2.80/1.03  cnf(c_288,plain,
% 2.80/1.03      ( ~ r1_tarski(X0,X1) | ~ v1_xboole_0(X1) | v1_xboole_0(X0) ),
% 2.80/1.03      inference(bin_hyper_res,[status(thm)],[c_5,c_225]) ).
% 2.80/1.03  
% 2.80/1.03  cnf(c_1391,plain,
% 2.80/1.03      ( r1_tarski(X0,X1) != iProver_top
% 2.80/1.03      | v1_xboole_0(X1) != iProver_top
% 2.80/1.03      | v1_xboole_0(X0) = iProver_top ),
% 2.80/1.03      inference(predicate_to_equality,[status(thm)],[c_288]) ).
% 2.80/1.03  
% 2.80/1.03  cnf(c_3253,plain,
% 2.80/1.03      ( v1_xboole_0(u1_struct_0(sK3)) != iProver_top
% 2.80/1.03      | v1_xboole_0(sK4) = iProver_top ),
% 2.80/1.03      inference(superposition,[status(thm)],[c_1839,c_1391]) ).
% 2.80/1.03  
% 2.80/1.03  cnf(c_3258,plain,
% 2.80/1.03      ( ~ v1_xboole_0(u1_struct_0(sK3)) | v1_xboole_0(sK4) ),
% 2.80/1.03      inference(predicate_to_equality_rev,[status(thm)],[c_3253]) ).
% 2.80/1.03  
% 2.80/1.03  cnf(c_526,plain,
% 2.80/1.03      ( m1_subset_1(k3_yellow_0(X0),u1_struct_0(X0)) | sK3 != X0 ),
% 2.80/1.03      inference(resolution_lifted,[status(thm)],[c_11,c_26]) ).
% 2.80/1.03  
% 2.80/1.03  cnf(c_527,plain,
% 2.80/1.03      ( m1_subset_1(k3_yellow_0(sK3),u1_struct_0(sK3)) ),
% 2.80/1.03      inference(unflattening,[status(thm)],[c_526]) ).
% 2.80/1.03  
% 2.80/1.03  cnf(c_1387,plain,
% 2.80/1.03      ( m1_subset_1(k3_yellow_0(sK3),u1_struct_0(sK3)) = iProver_top ),
% 2.80/1.03      inference(predicate_to_equality,[status(thm)],[c_527]) ).
% 2.80/1.03  
% 2.80/1.03  cnf(c_1398,plain,
% 2.80/1.03      ( m1_subset_1(X0,X1) != iProver_top
% 2.80/1.03      | r2_hidden(X0,X1) = iProver_top
% 2.80/1.03      | v1_xboole_0(X1) = iProver_top ),
% 2.80/1.03      inference(predicate_to_equality,[status(thm)],[c_7]) ).
% 2.80/1.03  
% 2.80/1.03  cnf(c_2220,plain,
% 2.80/1.03      ( r2_hidden(k3_yellow_0(sK3),u1_struct_0(sK3)) = iProver_top
% 2.80/1.03      | v1_xboole_0(u1_struct_0(sK3)) = iProver_top ),
% 2.80/1.03      inference(superposition,[status(thm)],[c_1387,c_1398]) ).
% 2.80/1.03  
% 2.80/1.03  cnf(c_2257,plain,
% 2.80/1.03      ( r2_hidden(k3_yellow_0(sK3),u1_struct_0(sK3))
% 2.80/1.03      | v1_xboole_0(u1_struct_0(sK3)) ),
% 2.80/1.03      inference(predicate_to_equality_rev,[status(thm)],[c_2220]) ).
% 2.80/1.03  
% 2.80/1.03  cnf(c_842,plain,
% 2.80/1.03      ( ~ r2_hidden(X0,X1) | r2_hidden(X2,X3) | X2 != X0 | X3 != X1 ),
% 2.80/1.03      theory(equality) ).
% 2.80/1.03  
% 2.80/1.03  cnf(c_1679,plain,
% 2.80/1.03      ( r2_hidden(X0,X1)
% 2.80/1.03      | ~ r2_hidden(k3_yellow_0(sK3),u1_struct_0(sK3))
% 2.80/1.03      | X1 != u1_struct_0(sK3)
% 2.80/1.03      | X0 != k3_yellow_0(sK3) ),
% 2.80/1.03      inference(instantiation,[status(thm)],[c_842]) ).
% 2.80/1.03  
% 2.80/1.03  cnf(c_2198,plain,
% 2.80/1.03      ( ~ r2_hidden(k3_yellow_0(sK3),u1_struct_0(sK3))
% 2.80/1.03      | r2_hidden(k3_yellow_0(sK3),sK4)
% 2.80/1.03      | k3_yellow_0(sK3) != k3_yellow_0(sK3)
% 2.80/1.03      | sK4 != u1_struct_0(sK3) ),
% 2.80/1.03      inference(instantiation,[status(thm)],[c_1679]) ).
% 2.80/1.03  
% 2.80/1.03  cnf(c_20,plain,
% 2.80/1.03      ( ~ v1_subset_1(X0,X0) | ~ m1_subset_1(X0,k1_zfmisc_1(X0)) ),
% 2.80/1.03      inference(cnf_transformation,[],[f81]) ).
% 2.80/1.03  
% 2.80/1.03  cnf(c_22,negated_conjecture,
% 2.80/1.03      ( v1_subset_1(sK4,u1_struct_0(sK3))
% 2.80/1.03      | ~ r2_hidden(k3_yellow_0(sK3),sK4) ),
% 2.80/1.03      inference(cnf_transformation,[],[f77]) ).
% 2.80/1.03  
% 2.80/1.03  cnf(c_226,plain,
% 2.80/1.03      ( v1_subset_1(sK4,u1_struct_0(sK3))
% 2.80/1.03      | ~ r2_hidden(k3_yellow_0(sK3),sK4) ),
% 2.80/1.03      inference(prop_impl,[status(thm)],[c_22]) ).
% 2.80/1.03  
% 2.80/1.03  cnf(c_434,plain,
% 2.80/1.03      ( ~ m1_subset_1(X0,k1_zfmisc_1(X0))
% 2.80/1.03      | ~ r2_hidden(k3_yellow_0(sK3),sK4)
% 2.80/1.03      | u1_struct_0(sK3) != X0
% 2.80/1.03      | sK4 != X0 ),
% 2.80/1.03      inference(resolution_lifted,[status(thm)],[c_20,c_226]) ).
% 2.80/1.03  
% 2.80/1.03  cnf(c_435,plain,
% 2.80/1.03      ( ~ m1_subset_1(u1_struct_0(sK3),k1_zfmisc_1(u1_struct_0(sK3)))
% 2.80/1.03      | ~ r2_hidden(k3_yellow_0(sK3),sK4)
% 2.80/1.03      | sK4 != u1_struct_0(sK3) ),
% 2.80/1.03      inference(unflattening,[status(thm)],[c_434]) ).
% 2.80/1.03  
% 2.80/1.03  cnf(c_1389,plain,
% 2.80/1.03      ( sK4 != u1_struct_0(sK3)
% 2.80/1.03      | m1_subset_1(u1_struct_0(sK3),k1_zfmisc_1(u1_struct_0(sK3))) != iProver_top
% 2.80/1.03      | r2_hidden(k3_yellow_0(sK3),sK4) != iProver_top ),
% 2.80/1.03      inference(predicate_to_equality,[status(thm)],[c_435]) ).
% 2.80/1.03  
% 2.80/1.03  cnf(c_436,plain,
% 2.80/1.03      ( sK4 != u1_struct_0(sK3)
% 2.80/1.03      | m1_subset_1(u1_struct_0(sK3),k1_zfmisc_1(u1_struct_0(sK3))) != iProver_top
% 2.80/1.03      | r2_hidden(k3_yellow_0(sK3),sK4) != iProver_top ),
% 2.80/1.03      inference(predicate_to_equality,[status(thm)],[c_435]) ).
% 2.80/1.03  
% 2.80/1.03  cnf(c_1587,plain,
% 2.80/1.03      ( m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK3)))
% 2.80/1.03      | ~ r1_tarski(X0,u1_struct_0(sK3)) ),
% 2.80/1.03      inference(instantiation,[status(thm)],[c_8]) ).
% 2.80/1.03  
% 2.80/1.03  cnf(c_1695,plain,
% 2.80/1.03      ( m1_subset_1(u1_struct_0(sK3),k1_zfmisc_1(u1_struct_0(sK3)))
% 2.80/1.03      | ~ r1_tarski(u1_struct_0(sK3),u1_struct_0(sK3)) ),
% 2.80/1.03      inference(instantiation,[status(thm)],[c_1587]) ).
% 2.80/1.03  
% 2.80/1.03  cnf(c_1697,plain,
% 2.80/1.03      ( m1_subset_1(u1_struct_0(sK3),k1_zfmisc_1(u1_struct_0(sK3))) = iProver_top
% 2.80/1.03      | r1_tarski(u1_struct_0(sK3),u1_struct_0(sK3)) != iProver_top ),
% 2.80/1.03      inference(predicate_to_equality,[status(thm)],[c_1695]) ).
% 2.80/1.03  
% 2.80/1.03  cnf(c_4,plain,
% 2.80/1.03      ( r1_tarski(X0,X0) ),
% 2.80/1.03      inference(cnf_transformation,[],[f80]) ).
% 2.80/1.03  
% 2.80/1.03  cnf(c_1696,plain,
% 2.80/1.03      ( r1_tarski(u1_struct_0(sK3),u1_struct_0(sK3)) ),
% 2.80/1.03      inference(instantiation,[status(thm)],[c_4]) ).
% 2.80/1.03  
% 2.80/1.03  cnf(c_1699,plain,
% 2.80/1.03      ( r1_tarski(u1_struct_0(sK3),u1_struct_0(sK3)) = iProver_top ),
% 2.80/1.03      inference(predicate_to_equality,[status(thm)],[c_1696]) ).
% 2.80/1.03  
% 2.80/1.03  cnf(c_2192,plain,
% 2.80/1.03      ( sK4 != u1_struct_0(sK3)
% 2.80/1.03      | r2_hidden(k3_yellow_0(sK3),sK4) != iProver_top ),
% 2.80/1.03      inference(global_propositional_subsumption,
% 2.80/1.03                [status(thm)],
% 2.80/1.03                [c_1389,c_436,c_1697,c_1699]) ).
% 2.80/1.03  
% 2.80/1.03  cnf(c_2194,plain,
% 2.80/1.03      ( ~ r2_hidden(k3_yellow_0(sK3),sK4) | sK4 != u1_struct_0(sK3) ),
% 2.80/1.03      inference(predicate_to_equality_rev,[status(thm)],[c_2192]) ).
% 2.80/1.03  
% 2.80/1.03  cnf(c_0,plain,
% 2.80/1.03      ( ~ r2_hidden(sK0(X0,X1),X1)
% 2.80/1.03      | ~ r2_hidden(sK0(X0,X1),X0)
% 2.80/1.03      | X1 = X0 ),
% 2.80/1.03      inference(cnf_transformation,[],[f50]) ).
% 2.80/1.03  
% 2.80/1.03  cnf(c_1664,plain,
% 2.80/1.03      ( ~ r2_hidden(sK0(sK4,X0),X0)
% 2.80/1.03      | ~ r2_hidden(sK0(sK4,X0),sK4)
% 2.80/1.03      | X0 = sK4 ),
% 2.80/1.03      inference(instantiation,[status(thm)],[c_0]) ).
% 2.80/1.03  
% 2.80/1.03  cnf(c_1996,plain,
% 2.80/1.03      ( ~ r2_hidden(sK0(sK4,u1_struct_0(sK3)),u1_struct_0(sK3))
% 2.80/1.03      | ~ r2_hidden(sK0(sK4,u1_struct_0(sK3)),sK4)
% 2.80/1.03      | u1_struct_0(sK3) = sK4 ),
% 2.80/1.03      inference(instantiation,[status(thm)],[c_1664]) ).
% 2.80/1.03  
% 2.80/1.03  cnf(c_2007,plain,
% 2.80/1.03      ( u1_struct_0(sK3) = sK4
% 2.80/1.03      | r2_hidden(sK0(sK4,u1_struct_0(sK3)),u1_struct_0(sK3)) != iProver_top
% 2.80/1.03      | r2_hidden(sK0(sK4,u1_struct_0(sK3)),sK4) != iProver_top ),
% 2.80/1.03      inference(predicate_to_equality,[status(thm)],[c_1996]) ).
% 2.80/1.03  
% 2.80/1.03  cnf(c_1,plain,
% 2.80/1.03      ( r2_hidden(sK0(X0,X1),X1) | r2_hidden(sK0(X0,X1),X0) | X1 = X0 ),
% 2.80/1.03      inference(cnf_transformation,[],[f49]) ).
% 2.80/1.03  
% 2.80/1.03  cnf(c_1663,plain,
% 2.80/1.03      ( r2_hidden(sK0(sK4,X0),X0)
% 2.80/1.03      | r2_hidden(sK0(sK4,X0),sK4)
% 2.80/1.03      | X0 = sK4 ),
% 2.80/1.03      inference(instantiation,[status(thm)],[c_1]) ).
% 2.80/1.03  
% 2.80/1.03  cnf(c_1997,plain,
% 2.80/1.03      ( r2_hidden(sK0(sK4,u1_struct_0(sK3)),u1_struct_0(sK3))
% 2.80/1.03      | r2_hidden(sK0(sK4,u1_struct_0(sK3)),sK4)
% 2.80/1.03      | u1_struct_0(sK3) = sK4 ),
% 2.80/1.03      inference(instantiation,[status(thm)],[c_1663]) ).
% 2.80/1.03  
% 2.80/1.03  cnf(c_2005,plain,
% 2.80/1.03      ( u1_struct_0(sK3) = sK4
% 2.80/1.03      | r2_hidden(sK0(sK4,u1_struct_0(sK3)),u1_struct_0(sK3)) = iProver_top
% 2.80/1.03      | r2_hidden(sK0(sK4,u1_struct_0(sK3)),sK4) = iProver_top ),
% 2.80/1.03      inference(predicate_to_equality,[status(thm)],[c_1997]) ).
% 2.80/1.03  
% 2.80/1.03  cnf(c_840,plain,( X0 = X0 ),theory(equality) ).
% 2.80/1.03  
% 2.80/1.03  cnf(c_1674,plain,
% 2.80/1.03      ( sK4 = sK4 ),
% 2.80/1.03      inference(instantiation,[status(thm)],[c_840]) ).
% 2.80/1.03  
% 2.80/1.03  cnf(c_1592,plain,
% 2.80/1.03      ( ~ m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(sK3)))
% 2.80/1.03      | r1_tarski(sK4,u1_struct_0(sK3)) ),
% 2.80/1.03      inference(instantiation,[status(thm)],[c_9]) ).
% 2.80/1.03  
% 2.80/1.03  cnf(c_1593,plain,
% 2.80/1.03      ( m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(sK3))) != iProver_top
% 2.80/1.03      | r1_tarski(sK4,u1_struct_0(sK3)) = iProver_top ),
% 2.80/1.03      inference(predicate_to_equality,[status(thm)],[c_1592]) ).
% 2.80/1.03  
% 2.80/1.03  cnf(c_847,plain,
% 2.80/1.03      ( X0 != X1 | k3_yellow_0(X0) = k3_yellow_0(X1) ),
% 2.80/1.03      theory(equality) ).
% 2.80/1.03  
% 2.80/1.03  cnf(c_857,plain,
% 2.80/1.03      ( k3_yellow_0(sK3) = k3_yellow_0(sK3) | sK3 != sK3 ),
% 2.80/1.03      inference(instantiation,[status(thm)],[c_847]) ).
% 2.80/1.03  
% 2.80/1.03  cnf(c_19,plain,
% 2.80/1.03      ( v1_subset_1(X0,X1)
% 2.80/1.03      | ~ m1_subset_1(X0,k1_zfmisc_1(X1))
% 2.80/1.03      | X0 = X1 ),
% 2.80/1.03      inference(cnf_transformation,[],[f69]) ).
% 2.80/1.03  
% 2.80/1.03  cnf(c_291,plain,
% 2.80/1.03      ( v1_subset_1(X0,X1) | ~ r1_tarski(X0,X1) | X0 = X1 ),
% 2.80/1.03      inference(bin_hyper_res,[status(thm)],[c_19,c_225]) ).
% 2.80/1.03  
% 2.80/1.03  cnf(c_21,negated_conjecture,
% 2.80/1.03      ( ~ v1_subset_1(sK4,u1_struct_0(sK3))
% 2.80/1.03      | r2_hidden(k3_yellow_0(sK3),sK4) ),
% 2.80/1.03      inference(cnf_transformation,[],[f78]) ).
% 2.80/1.03  
% 2.80/1.03  cnf(c_228,plain,
% 2.80/1.03      ( ~ v1_subset_1(sK4,u1_struct_0(sK3))
% 2.80/1.03      | r2_hidden(k3_yellow_0(sK3),sK4) ),
% 2.80/1.03      inference(prop_impl,[status(thm)],[c_21]) ).
% 2.80/1.03  
% 2.80/1.03  cnf(c_421,plain,
% 2.80/1.03      ( ~ r1_tarski(X0,X1)
% 2.80/1.03      | r2_hidden(k3_yellow_0(sK3),sK4)
% 2.80/1.03      | X1 = X0
% 2.80/1.03      | u1_struct_0(sK3) != X1
% 2.80/1.03      | sK4 != X0 ),
% 2.80/1.03      inference(resolution_lifted,[status(thm)],[c_291,c_228]) ).
% 2.80/1.03  
% 2.80/1.03  cnf(c_422,plain,
% 2.80/1.03      ( ~ r1_tarski(sK4,u1_struct_0(sK3))
% 2.80/1.03      | r2_hidden(k3_yellow_0(sK3),sK4)
% 2.80/1.03      | u1_struct_0(sK3) = sK4 ),
% 2.80/1.03      inference(unflattening,[status(thm)],[c_421]) ).
% 2.80/1.03  
% 2.80/1.03  cnf(c_423,plain,
% 2.80/1.03      ( u1_struct_0(sK3) = sK4
% 2.80/1.03      | r1_tarski(sK4,u1_struct_0(sK3)) != iProver_top
% 2.80/1.03      | r2_hidden(k3_yellow_0(sK3),sK4) = iProver_top ),
% 2.80/1.03      inference(predicate_to_equality,[status(thm)],[c_422]) ).
% 2.80/1.03  
% 2.80/1.03  cnf(c_84,plain,
% 2.80/1.03      ( r1_tarski(sK3,sK3) ),
% 2.80/1.03      inference(instantiation,[status(thm)],[c_4]) ).
% 2.80/1.03  
% 2.80/1.03  cnf(c_74,plain,
% 2.80/1.03      ( m1_subset_1(sK3,k1_zfmisc_1(sK3)) | ~ r1_tarski(sK3,sK3) ),
% 2.80/1.03      inference(instantiation,[status(thm)],[c_8]) ).
% 2.80/1.03  
% 2.80/1.03  cnf(c_43,plain,
% 2.80/1.03      ( v1_subset_1(sK3,sK3)
% 2.80/1.03      | ~ m1_subset_1(sK3,k1_zfmisc_1(sK3))
% 2.80/1.03      | sK3 = sK3 ),
% 2.80/1.03      inference(instantiation,[status(thm)],[c_19]) ).
% 2.80/1.03  
% 2.80/1.03  cnf(c_40,plain,
% 2.80/1.03      ( ~ v1_subset_1(sK3,sK3) | ~ m1_subset_1(sK3,k1_zfmisc_1(sK3)) ),
% 2.80/1.03      inference(instantiation,[status(thm)],[c_20]) ).
% 2.80/1.03  
% 2.80/1.03  cnf(c_36,plain,
% 2.80/1.03      ( m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(sK3))) = iProver_top ),
% 2.80/1.03      inference(predicate_to_equality,[status(thm)],[c_23]) ).
% 2.80/1.03  
% 2.80/1.03  cnf(c_24,negated_conjecture,
% 2.80/1.03      ( v13_waybel_0(sK4,sK3) ),
% 2.80/1.03      inference(cnf_transformation,[],[f75]) ).
% 2.80/1.03  
% 2.80/1.03  cnf(c_35,plain,
% 2.80/1.03      ( v13_waybel_0(sK4,sK3) = iProver_top ),
% 2.80/1.03      inference(predicate_to_equality,[status(thm)],[c_24]) ).
% 2.80/1.03  
% 2.80/1.03  cnf(c_25,negated_conjecture,
% 2.80/1.03      ( ~ v1_xboole_0(sK4) ),
% 2.80/1.03      inference(cnf_transformation,[],[f74]) ).
% 2.80/1.03  
% 2.80/1.03  cnf(c_34,plain,
% 2.80/1.03      ( v1_xboole_0(sK4) != iProver_top ),
% 2.80/1.03      inference(predicate_to_equality,[status(thm)],[c_25]) ).
% 2.80/1.03  
% 2.80/1.03  cnf(contradiction,plain,
% 2.80/1.03      ( $false ),
% 2.80/1.03      inference(minisat,
% 2.80/1.03                [status(thm)],
% 2.80/1.03                [c_6981,c_5579,c_4067,c_4057,c_3344,c_3258,c_3253,c_2257,
% 2.80/1.03                 c_2198,c_2194,c_2007,c_2005,c_1674,c_1593,c_857,c_423,
% 2.80/1.03                 c_84,c_74,c_43,c_40,c_36,c_35,c_34,c_25]) ).
% 2.80/1.03  
% 2.80/1.03  
% 2.80/1.03  % SZS output end CNFRefutation for theBenchmark.p
% 2.80/1.03  
% 2.80/1.03  ------                               Statistics
% 2.80/1.03  
% 2.80/1.03  ------ General
% 2.80/1.03  
% 2.80/1.03  abstr_ref_over_cycles:                  0
% 2.80/1.03  abstr_ref_under_cycles:                 0
% 2.80/1.03  gc_basic_clause_elim:                   0
% 2.80/1.03  forced_gc_time:                         0
% 2.80/1.03  parsing_time:                           0.011
% 2.80/1.03  unif_index_cands_time:                  0.
% 2.80/1.03  unif_index_add_time:                    0.
% 2.80/1.03  orderings_time:                         0.
% 2.80/1.03  out_proof_time:                         0.009
% 2.80/1.03  total_time:                             0.293
% 2.80/1.03  num_of_symbols:                         50
% 2.80/1.03  num_of_terms:                           4982
% 2.80/1.03  
% 2.80/1.03  ------ Preprocessing
% 2.80/1.03  
% 2.80/1.03  num_of_splits:                          0
% 2.80/1.03  num_of_split_atoms:                     0
% 2.80/1.03  num_of_reused_defs:                     0
% 2.80/1.03  num_eq_ax_congr_red:                    17
% 2.80/1.03  num_of_sem_filtered_clauses:            1
% 2.80/1.03  num_of_subtypes:                        0
% 2.80/1.03  monotx_restored_types:                  0
% 2.80/1.03  sat_num_of_epr_types:                   0
% 2.80/1.03  sat_num_of_non_cyclic_types:            0
% 2.80/1.03  sat_guarded_non_collapsed_types:        0
% 2.80/1.03  num_pure_diseq_elim:                    0
% 2.80/1.03  simp_replaced_by:                       0
% 2.80/1.03  res_preprocessed:                       120
% 2.80/1.03  prep_upred:                             0
% 2.80/1.03  prep_unflattend:                        18
% 2.80/1.03  smt_new_axioms:                         0
% 2.80/1.03  pred_elim_cands:                        5
% 2.80/1.03  pred_elim:                              6
% 2.80/1.03  pred_elim_cl:                           7
% 2.80/1.03  pred_elim_cycles:                       8
% 2.80/1.03  merged_defs:                            10
% 2.80/1.03  merged_defs_ncl:                        0
% 2.80/1.03  bin_hyper_res:                          12
% 2.80/1.03  prep_cycles:                            4
% 2.80/1.03  pred_elim_time:                         0.022
% 2.80/1.03  splitting_time:                         0.
% 2.80/1.03  sem_filter_time:                        0.
% 2.80/1.03  monotx_time:                            0.001
% 2.80/1.03  subtype_inf_time:                       0.
% 2.80/1.03  
% 2.80/1.03  ------ Problem properties
% 2.80/1.03  
% 2.80/1.03  clauses:                                22
% 2.80/1.03  conjectures:                            3
% 2.80/1.03  epr:                                    7
% 2.80/1.03  horn:                                   15
% 2.80/1.03  ground:                                 6
% 2.80/1.03  unary:                                  5
% 2.80/1.03  binary:                                 3
% 2.80/1.03  lits:                                   58
% 2.80/1.03  lits_eq:                                5
% 2.80/1.03  fd_pure:                                0
% 2.80/1.03  fd_pseudo:                              0
% 2.80/1.03  fd_cond:                                0
% 2.80/1.03  fd_pseudo_cond:                         3
% 2.80/1.03  ac_symbols:                             0
% 2.80/1.03  
% 2.80/1.03  ------ Propositional Solver
% 2.80/1.03  
% 2.80/1.03  prop_solver_calls:                      30
% 2.80/1.03  prop_fast_solver_calls:                 1159
% 2.80/1.03  smt_solver_calls:                       0
% 2.80/1.03  smt_fast_solver_calls:                  0
% 2.80/1.03  prop_num_of_clauses:                    2915
% 2.80/1.03  prop_preprocess_simplified:             6765
% 2.80/1.03  prop_fo_subsumed:                       27
% 2.80/1.03  prop_solver_time:                       0.
% 2.80/1.03  smt_solver_time:                        0.
% 2.80/1.03  smt_fast_solver_time:                   0.
% 2.80/1.03  prop_fast_solver_time:                  0.
% 2.80/1.03  prop_unsat_core_time:                   0.
% 2.80/1.03  
% 2.80/1.03  ------ QBF
% 2.80/1.03  
% 2.80/1.03  qbf_q_res:                              0
% 2.80/1.03  qbf_num_tautologies:                    0
% 2.80/1.03  qbf_prep_cycles:                        0
% 2.80/1.03  
% 2.80/1.03  ------ BMC1
% 2.80/1.03  
% 2.80/1.03  bmc1_current_bound:                     -1
% 2.80/1.03  bmc1_last_solved_bound:                 -1
% 2.80/1.03  bmc1_unsat_core_size:                   -1
% 2.80/1.03  bmc1_unsat_core_parents_size:           -1
% 2.80/1.03  bmc1_merge_next_fun:                    0
% 2.80/1.03  bmc1_unsat_core_clauses_time:           0.
% 2.80/1.03  
% 2.80/1.03  ------ Instantiation
% 2.80/1.03  
% 2.80/1.03  inst_num_of_clauses:                    599
% 2.80/1.03  inst_num_in_passive:                    21
% 2.80/1.03  inst_num_in_active:                     384
% 2.80/1.03  inst_num_in_unprocessed:                194
% 2.80/1.03  inst_num_of_loops:                      528
% 2.80/1.03  inst_num_of_learning_restarts:          0
% 2.80/1.03  inst_num_moves_active_passive:          139
% 2.80/1.03  inst_lit_activity:                      0
% 2.80/1.03  inst_lit_activity_moves:                0
% 2.80/1.03  inst_num_tautologies:                   0
% 2.80/1.03  inst_num_prop_implied:                  0
% 2.80/1.03  inst_num_existing_simplified:           0
% 2.80/1.03  inst_num_eq_res_simplified:             0
% 2.80/1.03  inst_num_child_elim:                    0
% 2.80/1.03  inst_num_of_dismatching_blockings:      244
% 2.80/1.03  inst_num_of_non_proper_insts:           670
% 2.80/1.03  inst_num_of_duplicates:                 0
% 2.80/1.03  inst_inst_num_from_inst_to_res:         0
% 2.80/1.03  inst_dismatching_checking_time:         0.
% 2.80/1.03  
% 2.80/1.03  ------ Resolution
% 2.80/1.03  
% 2.80/1.03  res_num_of_clauses:                     0
% 2.80/1.03  res_num_in_passive:                     0
% 2.80/1.03  res_num_in_active:                      0
% 2.80/1.03  res_num_of_loops:                       124
% 2.80/1.03  res_forward_subset_subsumed:            67
% 2.80/1.03  res_backward_subset_subsumed:           0
% 2.80/1.03  res_forward_subsumed:                   0
% 2.80/1.03  res_backward_subsumed:                  0
% 2.80/1.03  res_forward_subsumption_resolution:     2
% 2.80/1.03  res_backward_subsumption_resolution:    0
% 2.80/1.03  res_clause_to_clause_subsumption:       1621
% 2.80/1.03  res_orphan_elimination:                 0
% 2.80/1.03  res_tautology_del:                      61
% 2.80/1.03  res_num_eq_res_simplified:              0
% 2.80/1.03  res_num_sel_changes:                    0
% 2.80/1.03  res_moves_from_active_to_pass:          0
% 2.80/1.03  
% 2.80/1.03  ------ Superposition
% 2.80/1.03  
% 2.80/1.03  sup_time_total:                         0.
% 2.80/1.03  sup_time_generating:                    0.
% 2.80/1.03  sup_time_sim_full:                      0.
% 2.80/1.03  sup_time_sim_immed:                     0.
% 2.80/1.03  
% 2.80/1.03  sup_num_of_clauses:                     281
% 2.80/1.03  sup_num_in_active:                      104
% 2.80/1.03  sup_num_in_passive:                     177
% 2.80/1.03  sup_num_of_loops:                       104
% 2.80/1.03  sup_fw_superposition:                   132
% 2.80/1.03  sup_bw_superposition:                   281
% 2.80/1.03  sup_immediate_simplified:               36
% 2.80/1.03  sup_given_eliminated:                   0
% 2.80/1.03  comparisons_done:                       0
% 2.80/1.03  comparisons_avoided:                    0
% 2.80/1.03  
% 2.80/1.03  ------ Simplifications
% 2.80/1.03  
% 2.80/1.03  
% 2.80/1.03  sim_fw_subset_subsumed:                 27
% 2.80/1.03  sim_bw_subset_subsumed:                 1
% 2.80/1.03  sim_fw_subsumed:                        9
% 2.80/1.03  sim_bw_subsumed:                        0
% 2.80/1.03  sim_fw_subsumption_res:                 0
% 2.80/1.03  sim_bw_subsumption_res:                 0
% 2.80/1.03  sim_tautology_del:                      76
% 2.80/1.03  sim_eq_tautology_del:                   25
% 2.80/1.03  sim_eq_res_simp:                        0
% 2.80/1.03  sim_fw_demodulated:                     0
% 2.80/1.03  sim_bw_demodulated:                     0
% 2.80/1.03  sim_light_normalised:                   0
% 2.80/1.03  sim_joinable_taut:                      0
% 2.80/1.03  sim_joinable_simp:                      0
% 2.80/1.03  sim_ac_normalised:                      0
% 2.80/1.03  sim_smt_subsumption:                    0
% 2.80/1.03  
%------------------------------------------------------------------------------
