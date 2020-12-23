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
% DateTime   : Thu Dec  3 12:28:34 EST 2020

% Result     : Theorem 1.90s
% Output     : CNFRefutation 1.90s
% Verified   : 
% Statistics : Number of formulae       :  153 (1061 expanded)
%              Number of clauses        :   87 ( 242 expanded)
%              Number of leaves         :   18 ( 224 expanded)
%              Depth                    :   26
%              Number of atoms          :  610 (8965 expanded)
%              Number of equality atoms :  108 ( 273 expanded)
%              Maximal formula depth    :   14 (   5 average)
%              Maximal clause size      :   24 (   3 average)
%              Maximal term depth       :    5 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f9,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => ( v1_subset_1(X1,X0)
      <=> X0 != X1 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f26,plain,(
    ! [X0,X1] :
      ( ( v1_subset_1(X1,X0)
      <=> X0 != X1 )
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f38,plain,(
    ! [X0,X1] :
      ( ( ( v1_subset_1(X1,X0)
          | X0 = X1 )
        & ( X0 != X1
          | ~ v1_subset_1(X1,X0) ) )
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(nnf_transformation,[],[f26])).

fof(f61,plain,(
    ! [X0,X1] :
      ( v1_subset_1(X1,X0)
      | X0 = X1
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f38])).

fof(f10,conjecture,(
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

fof(f11,negated_conjecture,(
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
    inference(negated_conjecture,[],[f10])).

fof(f12,plain,(
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
    inference(pure_predicate_removal,[],[f11])).

fof(f13,plain,(
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
    inference(pure_predicate_removal,[],[f12])).

fof(f27,plain,(
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
      & v3_orders_2(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f13])).

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
      & v3_orders_2(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(flattening,[],[f27])).

fof(f39,plain,(
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
      & v3_orders_2(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(nnf_transformation,[],[f28])).

fof(f40,plain,(
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
      & v3_orders_2(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(flattening,[],[f39])).

fof(f42,plain,(
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

fof(f41,plain,
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
        & v3_orders_2(X0)
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
      & v3_orders_2(sK4)
      & ~ v2_struct_0(sK4) ) ),
    introduced(choice_axiom,[])).

fof(f43,plain,
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
    & v3_orders_2(sK4)
    & ~ v2_struct_0(sK4) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4,sK5])],[f40,f42,f41])).

fof(f71,plain,
    ( r2_hidden(k3_yellow_0(sK4),sK5)
    | ~ v1_subset_1(sK5,u1_struct_0(sK4)) ),
    inference(cnf_transformation,[],[f43])).

fof(f69,plain,(
    m1_subset_1(sK5,k1_zfmisc_1(u1_struct_0(sK4))) ),
    inference(cnf_transformation,[],[f43])).

fof(f8,axiom,(
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

fof(f24,plain,(
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
    inference(ennf_transformation,[],[f8])).

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
    inference(flattening,[],[f24])).

fof(f33,plain,(
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
    inference(nnf_transformation,[],[f25])).

fof(f34,plain,(
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
    inference(rectify,[],[f33])).

fof(f36,plain,(
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

fof(f35,plain,(
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

fof(f37,plain,(
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
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2,sK3])],[f34,f36,f35])).

fof(f54,plain,(
    ! [X4,X0,X5,X1] :
      ( r2_hidden(X5,X1)
      | ~ r1_orders_2(X0,X4,X5)
      | ~ r2_hidden(X4,X1)
      | ~ m1_subset_1(X5,u1_struct_0(X0))
      | ~ m1_subset_1(X4,u1_struct_0(X0))
      | ~ v13_waybel_0(X1,X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f37])).

fof(f7,axiom,(
    ! [X0] :
      ( ( l1_orders_2(X0)
        & v1_yellow_0(X0)
        & v5_orders_2(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,u1_struct_0(X0))
         => r1_orders_2(X0,k3_yellow_0(X0),X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f22,plain,(
    ! [X0] :
      ( ! [X1] :
          ( r1_orders_2(X0,k3_yellow_0(X0),X1)
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l1_orders_2(X0)
      | ~ v1_yellow_0(X0)
      | ~ v5_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f23,plain,(
    ! [X0] :
      ( ! [X1] :
          ( r1_orders_2(X0,k3_yellow_0(X0),X1)
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l1_orders_2(X0)
      | ~ v1_yellow_0(X0)
      | ~ v5_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f22])).

fof(f53,plain,(
    ! [X0,X1] :
      ( r1_orders_2(X0,k3_yellow_0(X0),X1)
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | ~ v1_yellow_0(X0)
      | ~ v5_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f65,plain,(
    v1_yellow_0(sK4) ),
    inference(cnf_transformation,[],[f43])).

fof(f62,plain,(
    ~ v2_struct_0(sK4) ),
    inference(cnf_transformation,[],[f43])).

fof(f64,plain,(
    v5_orders_2(sK4) ),
    inference(cnf_transformation,[],[f43])).

fof(f66,plain,(
    l1_orders_2(sK4) ),
    inference(cnf_transformation,[],[f43])).

fof(f5,axiom,(
    ! [X0] :
      ( l1_orders_2(X0)
     => m1_subset_1(k3_yellow_0(X0),u1_struct_0(X0)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f19,plain,(
    ! [X0] :
      ( m1_subset_1(k3_yellow_0(X0),u1_struct_0(X0))
      | ~ l1_orders_2(X0) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f50,plain,(
    ! [X0] :
      ( m1_subset_1(k3_yellow_0(X0),u1_struct_0(X0))
      | ~ l1_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f68,plain,(
    v13_waybel_0(sK5,sK4) ),
    inference(cnf_transformation,[],[f43])).

fof(f60,plain,(
    ! [X0,X1] :
      ( X0 != X1
      | ~ v1_subset_1(X1,X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f38])).

fof(f72,plain,(
    ! [X1] :
      ( ~ v1_subset_1(X1,X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X1)) ) ),
    inference(equality_resolution,[],[f60])).

fof(f70,plain,
    ( ~ r2_hidden(k3_yellow_0(sK4),sK5)
    | v1_subset_1(sK5,u1_struct_0(sK4)) ),
    inference(cnf_transformation,[],[f43])).

fof(f2,axiom,(
    ! [X0] :
    ? [X1] :
      ( ~ v1_subset_1(X1,X0)
      & m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f31,plain,(
    ! [X0] :
      ( ? [X1] :
          ( ~ v1_subset_1(X1,X0)
          & m1_subset_1(X1,k1_zfmisc_1(X0)) )
     => ( ~ v1_subset_1(sK1(X0),X0)
        & m1_subset_1(sK1(X0),k1_zfmisc_1(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f32,plain,(
    ! [X0] :
      ( ~ v1_subset_1(sK1(X0),X0)
      & m1_subset_1(sK1(X0),k1_zfmisc_1(X0)) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1])],[f2,f31])).

fof(f46,plain,(
    ! [X0] : m1_subset_1(sK1(X0),k1_zfmisc_1(X0)) ),
    inference(cnf_transformation,[],[f32])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => ( ! [X2] :
            ( m1_subset_1(X2,X0)
           => r2_hidden(X2,X1) )
       => X0 = X1 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f14,plain,(
    ! [X0,X1] :
      ( X0 = X1
      | ? [X2] :
          ( ~ r2_hidden(X2,X1)
          & m1_subset_1(X2,X0) )
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f15,plain,(
    ! [X0,X1] :
      ( X0 = X1
      | ? [X2] :
          ( ~ r2_hidden(X2,X1)
          & m1_subset_1(X2,X0) )
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(flattening,[],[f14])).

fof(f29,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ~ r2_hidden(X2,X1)
          & m1_subset_1(X2,X0) )
     => ( ~ r2_hidden(sK0(X0,X1),X1)
        & m1_subset_1(sK0(X0,X1),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f30,plain,(
    ! [X0,X1] :
      ( X0 = X1
      | ( ~ r2_hidden(sK0(X0,X1),X1)
        & m1_subset_1(sK0(X0,X1),X0) )
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f15,f29])).

fof(f45,plain,(
    ! [X0,X1] :
      ( X0 = X1
      | ~ r2_hidden(sK0(X0,X1),X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f47,plain,(
    ! [X0] : ~ v1_subset_1(sK1(X0),X0) ),
    inference(cnf_transformation,[],[f32])).

fof(f44,plain,(
    ! [X0,X1] :
      ( X0 = X1
      | m1_subset_1(sK0(X0,X1),X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f6,axiom,(
    ! [X0] :
      ( ( l1_orders_2(X0)
        & v5_orders_2(X0)
        & v3_orders_2(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,u1_struct_0(X0))
         => ( k2_yellow_0(X0,k6_domain_1(u1_struct_0(X0),X1)) = X1
            & k1_yellow_0(X0,k6_domain_1(u1_struct_0(X0),X1)) = X1 ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f20,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( k2_yellow_0(X0,k6_domain_1(u1_struct_0(X0),X1)) = X1
            & k1_yellow_0(X0,k6_domain_1(u1_struct_0(X0),X1)) = X1 )
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l1_orders_2(X0)
      | ~ v5_orders_2(X0)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f21,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( k2_yellow_0(X0,k6_domain_1(u1_struct_0(X0),X1)) = X1
            & k1_yellow_0(X0,k6_domain_1(u1_struct_0(X0),X1)) = X1 )
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l1_orders_2(X0)
      | ~ v5_orders_2(X0)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f20])).

fof(f51,plain,(
    ! [X0,X1] :
      ( k1_yellow_0(X0,k6_domain_1(u1_struct_0(X0),X1)) = X1
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | ~ v5_orders_2(X0)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f63,plain,(
    v3_orders_2(sK4) ),
    inference(cnf_transformation,[],[f43])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( l1_orders_2(X0)
     => m1_subset_1(k1_yellow_0(X0,X1),u1_struct_0(X0)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f18,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k1_yellow_0(X0,X1),u1_struct_0(X0))
      | ~ l1_orders_2(X0) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f49,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k1_yellow_0(X0,X1),u1_struct_0(X0))
      | ~ l1_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,X1)
     => ( r2_hidden(X0,X1)
        | v1_xboole_0(X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f16,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
      | v1_xboole_0(X1)
      | ~ m1_subset_1(X0,X1) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f17,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
      | v1_xboole_0(X1)
      | ~ m1_subset_1(X0,X1) ) ),
    inference(flattening,[],[f16])).

fof(f48,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
      | v1_xboole_0(X1)
      | ~ m1_subset_1(X0,X1) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f67,plain,(
    ~ v1_xboole_0(sK5) ),
    inference(cnf_transformation,[],[f43])).

cnf(c_16,plain,
    ( v1_subset_1(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | X0 = X1 ),
    inference(cnf_transformation,[],[f61])).

cnf(c_18,negated_conjecture,
    ( ~ v1_subset_1(sK5,u1_struct_0(sK4))
    | r2_hidden(k3_yellow_0(sK4),sK5) ),
    inference(cnf_transformation,[],[f71])).

cnf(c_209,plain,
    ( ~ v1_subset_1(sK5,u1_struct_0(sK4))
    | r2_hidden(k3_yellow_0(sK4),sK5) ),
    inference(prop_impl,[status(thm)],[c_18])).

cnf(c_473,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | r2_hidden(k3_yellow_0(sK4),sK5)
    | X1 = X0
    | u1_struct_0(sK4) != X1
    | sK5 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_16,c_209])).

cnf(c_474,plain,
    ( ~ m1_subset_1(sK5,k1_zfmisc_1(u1_struct_0(sK4)))
    | r2_hidden(k3_yellow_0(sK4),sK5)
    | u1_struct_0(sK4) = sK5 ),
    inference(unflattening,[status(thm)],[c_473])).

cnf(c_20,negated_conjecture,
    ( m1_subset_1(sK5,k1_zfmisc_1(u1_struct_0(sK4))) ),
    inference(cnf_transformation,[],[f69])).

cnf(c_476,plain,
    ( r2_hidden(k3_yellow_0(sK4),sK5)
    | u1_struct_0(sK4) = sK5 ),
    inference(global_propositional_subsumption,[status(thm)],[c_474,c_20])).

cnf(c_1194,plain,
    ( u1_struct_0(sK4) = sK5
    | r2_hidden(k3_yellow_0(sK4),sK5) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_476])).

cnf(c_1200,plain,
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
    inference(cnf_transformation,[],[f54])).

cnf(c_9,plain,
    ( r1_orders_2(X0,k3_yellow_0(X0),X1)
    | ~ m1_subset_1(X1,u1_struct_0(X0))
    | ~ v1_yellow_0(X0)
    | v2_struct_0(X0)
    | ~ v5_orders_2(X0)
    | ~ l1_orders_2(X0) ),
    inference(cnf_transformation,[],[f53])).

cnf(c_24,negated_conjecture,
    ( v1_yellow_0(sK4) ),
    inference(cnf_transformation,[],[f65])).

cnf(c_386,plain,
    ( r1_orders_2(X0,k3_yellow_0(X0),X1)
    | ~ m1_subset_1(X1,u1_struct_0(X0))
    | v2_struct_0(X0)
    | ~ v5_orders_2(X0)
    | ~ l1_orders_2(X0)
    | sK4 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_9,c_24])).

cnf(c_387,plain,
    ( r1_orders_2(sK4,k3_yellow_0(sK4),X0)
    | ~ m1_subset_1(X0,u1_struct_0(sK4))
    | v2_struct_0(sK4)
    | ~ v5_orders_2(sK4)
    | ~ l1_orders_2(sK4) ),
    inference(unflattening,[status(thm)],[c_386])).

cnf(c_27,negated_conjecture,
    ( ~ v2_struct_0(sK4) ),
    inference(cnf_transformation,[],[f62])).

cnf(c_25,negated_conjecture,
    ( v5_orders_2(sK4) ),
    inference(cnf_transformation,[],[f64])).

cnf(c_23,negated_conjecture,
    ( l1_orders_2(sK4) ),
    inference(cnf_transformation,[],[f66])).

cnf(c_391,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(sK4))
    | r1_orders_2(sK4,k3_yellow_0(sK4),X0) ),
    inference(global_propositional_subsumption,[status(thm)],[c_387,c_27,c_25,c_23])).

cnf(c_392,plain,
    ( r1_orders_2(sK4,k3_yellow_0(sK4),X0)
    | ~ m1_subset_1(X0,u1_struct_0(sK4)) ),
    inference(renaming,[status(thm)],[c_391])).

cnf(c_541,plain,
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
    inference(resolution_lifted,[status(thm)],[c_15,c_392])).

cnf(c_542,plain,
    ( ~ v13_waybel_0(X0,sK4)
    | ~ m1_subset_1(X1,u1_struct_0(sK4))
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK4)))
    | ~ m1_subset_1(k3_yellow_0(sK4),u1_struct_0(sK4))
    | r2_hidden(X1,X0)
    | ~ r2_hidden(k3_yellow_0(sK4),X0)
    | ~ l1_orders_2(sK4) ),
    inference(unflattening,[status(thm)],[c_541])).

cnf(c_6,plain,
    ( m1_subset_1(k3_yellow_0(X0),u1_struct_0(X0))
    | ~ l1_orders_2(X0) ),
    inference(cnf_transformation,[],[f50])).

cnf(c_70,plain,
    ( m1_subset_1(k3_yellow_0(sK4),u1_struct_0(sK4))
    | ~ l1_orders_2(sK4) ),
    inference(instantiation,[status(thm)],[c_6])).

cnf(c_546,plain,
    ( ~ r2_hidden(k3_yellow_0(sK4),X0)
    | r2_hidden(X1,X0)
    | ~ v13_waybel_0(X0,sK4)
    | ~ m1_subset_1(X1,u1_struct_0(sK4))
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK4))) ),
    inference(global_propositional_subsumption,[status(thm)],[c_542,c_23,c_70])).

cnf(c_547,plain,
    ( ~ v13_waybel_0(X0,sK4)
    | ~ m1_subset_1(X1,u1_struct_0(sK4))
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK4)))
    | r2_hidden(X1,X0)
    | ~ r2_hidden(k3_yellow_0(sK4),X0) ),
    inference(renaming,[status(thm)],[c_546])).

cnf(c_1192,plain,
    ( v13_waybel_0(X0,sK4) != iProver_top
    | m1_subset_1(X1,u1_struct_0(sK4)) != iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK4))) != iProver_top
    | r2_hidden(X1,X0) = iProver_top
    | r2_hidden(k3_yellow_0(sK4),X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_547])).

cnf(c_2325,plain,
    ( v13_waybel_0(sK5,sK4) != iProver_top
    | m1_subset_1(X0,u1_struct_0(sK4)) != iProver_top
    | r2_hidden(X0,sK5) = iProver_top
    | r2_hidden(k3_yellow_0(sK4),sK5) != iProver_top ),
    inference(superposition,[status(thm)],[c_1200,c_1192])).

cnf(c_21,negated_conjecture,
    ( v13_waybel_0(sK5,sK4) ),
    inference(cnf_transformation,[],[f68])).

cnf(c_34,plain,
    ( v13_waybel_0(sK5,sK4) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_21])).

cnf(c_2563,plain,
    ( m1_subset_1(X0,u1_struct_0(sK4)) != iProver_top
    | r2_hidden(X0,sK5) = iProver_top
    | r2_hidden(k3_yellow_0(sK4),sK5) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_2325,c_34])).

cnf(c_3002,plain,
    ( u1_struct_0(sK4) = sK5
    | m1_subset_1(X0,u1_struct_0(sK4)) != iProver_top
    | r2_hidden(X0,sK5) = iProver_top ),
    inference(superposition,[status(thm)],[c_1194,c_2563])).

cnf(c_17,plain,
    ( ~ v1_subset_1(X0,X0)
    | ~ m1_subset_1(X0,k1_zfmisc_1(X0)) ),
    inference(cnf_transformation,[],[f72])).

cnf(c_19,negated_conjecture,
    ( v1_subset_1(sK5,u1_struct_0(sK4))
    | ~ r2_hidden(k3_yellow_0(sK4),sK5) ),
    inference(cnf_transformation,[],[f70])).

cnf(c_207,plain,
    ( v1_subset_1(sK5,u1_struct_0(sK4))
    | ~ r2_hidden(k3_yellow_0(sK4),sK5) ),
    inference(prop_impl,[status(thm)],[c_19])).

cnf(c_487,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X0))
    | ~ r2_hidden(k3_yellow_0(sK4),sK5)
    | u1_struct_0(sK4) != X0
    | sK5 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_17,c_207])).

cnf(c_488,plain,
    ( ~ m1_subset_1(u1_struct_0(sK4),k1_zfmisc_1(u1_struct_0(sK4)))
    | ~ r2_hidden(k3_yellow_0(sK4),sK5)
    | sK5 != u1_struct_0(sK4) ),
    inference(unflattening,[status(thm)],[c_487])).

cnf(c_3,plain,
    ( m1_subset_1(sK1(X0),k1_zfmisc_1(X0)) ),
    inference(cnf_transformation,[],[f46])).

cnf(c_1376,plain,
    ( m1_subset_1(sK1(u1_struct_0(sK4)),k1_zfmisc_1(u1_struct_0(sK4))) ),
    inference(instantiation,[status(thm)],[c_3])).

cnf(c_0,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | ~ r2_hidden(sK0(X1,X0),X0)
    | X0 = X1 ),
    inference(cnf_transformation,[],[f45])).

cnf(c_1398,plain,
    ( ~ m1_subset_1(sK5,k1_zfmisc_1(u1_struct_0(sK4)))
    | ~ r2_hidden(sK0(u1_struct_0(sK4),sK5),sK5)
    | sK5 = u1_struct_0(sK4) ),
    inference(instantiation,[status(thm)],[c_0])).

cnf(c_2,plain,
    ( ~ v1_subset_1(sK1(X0),X0) ),
    inference(cnf_transformation,[],[f47])).

cnf(c_450,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | X1 != X2
    | X1 = X0
    | sK1(X2) != X0 ),
    inference(resolution_lifted,[status(thm)],[c_2,c_16])).

cnf(c_451,plain,
    ( ~ m1_subset_1(sK1(X0),k1_zfmisc_1(X0))
    | X0 = sK1(X0) ),
    inference(unflattening,[status(thm)],[c_450])).

cnf(c_455,plain,
    ( X0 = sK1(X0) ),
    inference(global_propositional_subsumption,[status(thm)],[c_451,c_3])).

cnf(c_1807,plain,
    ( u1_struct_0(sK4) = sK1(u1_struct_0(sK4)) ),
    inference(instantiation,[status(thm)],[c_455])).

cnf(c_842,plain,
    ( X0 = X0 ),
    theory(equality)).

cnf(c_1682,plain,
    ( k1_zfmisc_1(X0) = k1_zfmisc_1(X0) ),
    inference(instantiation,[status(thm)],[c_842])).

cnf(c_2060,plain,
    ( k1_zfmisc_1(u1_struct_0(sK4)) = k1_zfmisc_1(u1_struct_0(sK4)) ),
    inference(instantiation,[status(thm)],[c_1682])).

cnf(c_1,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | m1_subset_1(sK0(X1,X0),X1)
    | X0 = X1 ),
    inference(cnf_transformation,[],[f44])).

cnf(c_1202,plain,
    ( X0 = X1
    | m1_subset_1(X0,k1_zfmisc_1(X1)) != iProver_top
    | m1_subset_1(sK0(X1,X0),X1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1])).

cnf(c_8,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(X1))
    | v2_struct_0(X1)
    | ~ v3_orders_2(X1)
    | ~ v5_orders_2(X1)
    | ~ l1_orders_2(X1)
    | k1_yellow_0(X1,k6_domain_1(u1_struct_0(X1),X0)) = X0 ),
    inference(cnf_transformation,[],[f51])).

cnf(c_407,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(X1))
    | v2_struct_0(X1)
    | ~ v3_orders_2(X1)
    | ~ l1_orders_2(X1)
    | k1_yellow_0(X1,k6_domain_1(u1_struct_0(X1),X0)) = X0
    | sK4 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_8,c_25])).

cnf(c_408,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(sK4))
    | v2_struct_0(sK4)
    | ~ v3_orders_2(sK4)
    | ~ l1_orders_2(sK4)
    | k1_yellow_0(sK4,k6_domain_1(u1_struct_0(sK4),X0)) = X0 ),
    inference(unflattening,[status(thm)],[c_407])).

cnf(c_26,negated_conjecture,
    ( v3_orders_2(sK4) ),
    inference(cnf_transformation,[],[f63])).

cnf(c_412,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(sK4))
    | k1_yellow_0(sK4,k6_domain_1(u1_struct_0(sK4),X0)) = X0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_408,c_27,c_26,c_23])).

cnf(c_1197,plain,
    ( k1_yellow_0(sK4,k6_domain_1(u1_struct_0(sK4),X0)) = X0
    | m1_subset_1(X0,u1_struct_0(sK4)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_412])).

cnf(c_1592,plain,
    ( k1_yellow_0(sK4,k6_domain_1(u1_struct_0(sK4),sK0(u1_struct_0(sK4),X0))) = sK0(u1_struct_0(sK4),X0)
    | u1_struct_0(sK4) = X0
    | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK4))) != iProver_top ),
    inference(superposition,[status(thm)],[c_1202,c_1197])).

cnf(c_2460,plain,
    ( k1_yellow_0(sK4,k6_domain_1(u1_struct_0(sK4),sK0(u1_struct_0(sK4),sK5))) = sK0(u1_struct_0(sK4),sK5)
    | u1_struct_0(sK4) = sK5 ),
    inference(superposition,[status(thm)],[c_1200,c_1592])).

cnf(c_5,plain,
    ( m1_subset_1(k1_yellow_0(X0,X1),u1_struct_0(X0))
    | ~ l1_orders_2(X0) ),
    inference(cnf_transformation,[],[f49])).

cnf(c_589,plain,
    ( m1_subset_1(k1_yellow_0(X0,X1),u1_struct_0(X0))
    | sK4 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_5,c_23])).

cnf(c_590,plain,
    ( m1_subset_1(k1_yellow_0(sK4,X0),u1_struct_0(sK4)) ),
    inference(unflattening,[status(thm)],[c_589])).

cnf(c_1190,plain,
    ( m1_subset_1(k1_yellow_0(sK4,X0),u1_struct_0(sK4)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_590])).

cnf(c_2479,plain,
    ( u1_struct_0(sK4) = sK5
    | m1_subset_1(sK0(u1_struct_0(sK4),sK5),u1_struct_0(sK4)) = iProver_top ),
    inference(superposition,[status(thm)],[c_2460,c_1190])).

cnf(c_2488,plain,
    ( m1_subset_1(sK0(u1_struct_0(sK4),sK5),u1_struct_0(sK4))
    | u1_struct_0(sK4) = sK5 ),
    inference(predicate_to_equality_rev,[status(thm)],[c_2479])).

cnf(c_1371,plain,
    ( ~ v13_waybel_0(sK5,sK4)
    | ~ m1_subset_1(X0,u1_struct_0(sK4))
    | ~ m1_subset_1(sK5,k1_zfmisc_1(u1_struct_0(sK4)))
    | r2_hidden(X0,sK5)
    | ~ r2_hidden(k3_yellow_0(sK4),sK5) ),
    inference(instantiation,[status(thm)],[c_547])).

cnf(c_2884,plain,
    ( ~ v13_waybel_0(sK5,sK4)
    | ~ m1_subset_1(sK0(u1_struct_0(sK4),sK5),u1_struct_0(sK4))
    | ~ m1_subset_1(sK5,k1_zfmisc_1(u1_struct_0(sK4)))
    | r2_hidden(sK0(u1_struct_0(sK4),sK5),sK5)
    | ~ r2_hidden(k3_yellow_0(sK4),sK5) ),
    inference(instantiation,[status(thm)],[c_1371])).

cnf(c_846,plain,
    ( ~ m1_subset_1(X0,X1)
    | m1_subset_1(X2,X3)
    | X2 != X0
    | X3 != X1 ),
    theory(equality)).

cnf(c_1412,plain,
    ( m1_subset_1(X0,X1)
    | ~ m1_subset_1(sK1(X2),k1_zfmisc_1(X2))
    | X0 != sK1(X2)
    | X1 != k1_zfmisc_1(X2) ),
    inference(instantiation,[status(thm)],[c_846])).

cnf(c_1681,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(X1))
    | ~ m1_subset_1(sK1(X1),k1_zfmisc_1(X1))
    | X0 != sK1(X1)
    | k1_zfmisc_1(X1) != k1_zfmisc_1(X1) ),
    inference(instantiation,[status(thm)],[c_1412])).

cnf(c_2604,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK4)))
    | ~ m1_subset_1(sK1(u1_struct_0(sK4)),k1_zfmisc_1(u1_struct_0(sK4)))
    | X0 != sK1(u1_struct_0(sK4))
    | k1_zfmisc_1(u1_struct_0(sK4)) != k1_zfmisc_1(u1_struct_0(sK4)) ),
    inference(instantiation,[status(thm)],[c_1681])).

cnf(c_3045,plain,
    ( m1_subset_1(u1_struct_0(sK4),k1_zfmisc_1(u1_struct_0(sK4)))
    | ~ m1_subset_1(sK1(u1_struct_0(sK4)),k1_zfmisc_1(u1_struct_0(sK4)))
    | u1_struct_0(sK4) != sK1(u1_struct_0(sK4))
    | k1_zfmisc_1(u1_struct_0(sK4)) != k1_zfmisc_1(u1_struct_0(sK4)) ),
    inference(instantiation,[status(thm)],[c_2604])).

cnf(c_3218,plain,
    ( u1_struct_0(sK4) = sK5 ),
    inference(global_propositional_subsumption,[status(thm)],[c_3002,c_21,c_20,c_476,c_488,c_1376,c_1398,c_1807,c_2060,c_2488,c_2884,c_3045])).

cnf(c_582,plain,
    ( m1_subset_1(k3_yellow_0(X0),u1_struct_0(X0))
    | sK4 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_6,c_23])).

cnf(c_583,plain,
    ( m1_subset_1(k3_yellow_0(sK4),u1_struct_0(sK4)) ),
    inference(unflattening,[status(thm)],[c_582])).

cnf(c_1191,plain,
    ( m1_subset_1(k3_yellow_0(sK4),u1_struct_0(sK4)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_583])).

cnf(c_3249,plain,
    ( m1_subset_1(k3_yellow_0(sK4),sK5) = iProver_top ),
    inference(demodulation,[status(thm)],[c_3218,c_1191])).

cnf(c_4,plain,
    ( ~ m1_subset_1(X0,X1)
    | r2_hidden(X0,X1)
    | v1_xboole_0(X1) ),
    inference(cnf_transformation,[],[f48])).

cnf(c_22,negated_conjecture,
    ( ~ v1_xboole_0(sK5) ),
    inference(cnf_transformation,[],[f67])).

cnf(c_371,plain,
    ( ~ m1_subset_1(X0,X1)
    | r2_hidden(X0,X1)
    | sK5 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_4,c_22])).

cnf(c_372,plain,
    ( ~ m1_subset_1(X0,sK5)
    | r2_hidden(X0,sK5) ),
    inference(unflattening,[status(thm)],[c_371])).

cnf(c_1198,plain,
    ( m1_subset_1(X0,sK5) != iProver_top
    | r2_hidden(X0,sK5) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_372])).

cnf(c_3430,plain,
    ( r2_hidden(k3_yellow_0(sK4),sK5) = iProver_top ),
    inference(superposition,[status(thm)],[c_3249,c_1198])).

cnf(c_461,plain,
    ( ~ r2_hidden(k3_yellow_0(sK4),sK5)
    | u1_struct_0(sK4) != X0
    | sK1(X0) != sK5 ),
    inference(resolution_lifted,[status(thm)],[c_2,c_207])).

cnf(c_462,plain,
    ( ~ r2_hidden(k3_yellow_0(sK4),sK5)
    | sK1(u1_struct_0(sK4)) != sK5 ),
    inference(unflattening,[status(thm)],[c_461])).

cnf(c_1195,plain,
    ( sK1(u1_struct_0(sK4)) != sK5
    | r2_hidden(k3_yellow_0(sK4),sK5) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_462])).

cnf(c_1225,plain,
    ( u1_struct_0(sK4) != sK5
    | r2_hidden(k3_yellow_0(sK4),sK5) != iProver_top ),
    inference(demodulation,[status(thm)],[c_1195,c_455])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_3430,c_3218,c_1225])).

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
% 0.14/0.34  % DateTime   : Tue Dec  1 19:42:09 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.35  % Running in FOF mode
% 1.03/1.04  % SZS status Started for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.03/1.04  
% 1.03/1.04  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 1.03/1.04  
% 1.03/1.04  ------  iProver source info
% 1.03/1.04  
% 1.03/1.04  git: date: 2020-06-30 10:37:57 +0100
% 1.03/1.04  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 1.03/1.04  git: non_committed_changes: false
% 1.03/1.04  git: last_make_outside_of_git: false
% 1.03/1.04  
% 1.03/1.04  ------ 
% 1.03/1.04  
% 1.03/1.04  ------ Input Options
% 1.03/1.04  
% 1.03/1.04  --out_options                           all
% 1.03/1.04  --tptp_safe_out                         true
% 1.03/1.04  --problem_path                          ""
% 1.03/1.04  --include_path                          ""
% 1.03/1.04  --clausifier                            res/vclausify_rel
% 1.03/1.04  --clausifier_options                    --mode clausify
% 1.03/1.04  --stdin                                 false
% 1.03/1.04  --stats_out                             all
% 1.03/1.04  
% 1.03/1.04  ------ General Options
% 1.03/1.04  
% 1.03/1.04  --fof                                   false
% 1.03/1.04  --time_out_real                         305.
% 1.03/1.04  --time_out_virtual                      -1.
% 1.03/1.04  --symbol_type_check                     false
% 1.03/1.04  --clausify_out                          false
% 1.03/1.04  --sig_cnt_out                           false
% 1.03/1.04  --trig_cnt_out                          false
% 1.03/1.04  --trig_cnt_out_tolerance                1.
% 1.03/1.04  --trig_cnt_out_sk_spl                   false
% 1.03/1.04  --abstr_cl_out                          false
% 1.03/1.04  
% 1.03/1.04  ------ Global Options
% 1.03/1.04  
% 1.03/1.04  --schedule                              default
% 1.03/1.04  --add_important_lit                     false
% 1.03/1.04  --prop_solver_per_cl                    1000
% 1.03/1.04  --min_unsat_core                        false
% 1.03/1.04  --soft_assumptions                      false
% 1.03/1.04  --soft_lemma_size                       3
% 1.03/1.04  --prop_impl_unit_size                   0
% 1.03/1.04  --prop_impl_unit                        []
% 1.03/1.04  --share_sel_clauses                     true
% 1.03/1.04  --reset_solvers                         false
% 1.03/1.04  --bc_imp_inh                            [conj_cone]
% 1.03/1.04  --conj_cone_tolerance                   3.
% 1.03/1.04  --extra_neg_conj                        none
% 1.03/1.04  --large_theory_mode                     true
% 1.03/1.04  --prolific_symb_bound                   200
% 1.03/1.04  --lt_threshold                          2000
% 1.03/1.04  --clause_weak_htbl                      true
% 1.03/1.04  --gc_record_bc_elim                     false
% 1.03/1.04  
% 1.03/1.04  ------ Preprocessing Options
% 1.03/1.04  
% 1.03/1.04  --preprocessing_flag                    true
% 1.03/1.04  --time_out_prep_mult                    0.1
% 1.03/1.04  --splitting_mode                        input
% 1.03/1.04  --splitting_grd                         true
% 1.03/1.04  --splitting_cvd                         false
% 1.03/1.04  --splitting_cvd_svl                     false
% 1.03/1.04  --splitting_nvd                         32
% 1.03/1.04  --sub_typing                            true
% 1.03/1.04  --prep_gs_sim                           true
% 1.03/1.04  --prep_unflatten                        true
% 1.03/1.04  --prep_res_sim                          true
% 1.03/1.04  --prep_upred                            true
% 1.03/1.04  --prep_sem_filter                       exhaustive
% 1.03/1.04  --prep_sem_filter_out                   false
% 1.03/1.04  --pred_elim                             true
% 1.03/1.04  --res_sim_input                         true
% 1.03/1.04  --eq_ax_congr_red                       true
% 1.03/1.04  --pure_diseq_elim                       true
% 1.03/1.04  --brand_transform                       false
% 1.03/1.04  --non_eq_to_eq                          false
% 1.03/1.04  --prep_def_merge                        true
% 1.03/1.04  --prep_def_merge_prop_impl              false
% 1.03/1.04  --prep_def_merge_mbd                    true
% 1.03/1.04  --prep_def_merge_tr_red                 false
% 1.03/1.04  --prep_def_merge_tr_cl                  false
% 1.03/1.04  --smt_preprocessing                     true
% 1.03/1.04  --smt_ac_axioms                         fast
% 1.03/1.04  --preprocessed_out                      false
% 1.03/1.04  --preprocessed_stats                    false
% 1.03/1.04  
% 1.03/1.04  ------ Abstraction refinement Options
% 1.03/1.04  
% 1.03/1.04  --abstr_ref                             []
% 1.03/1.04  --abstr_ref_prep                        false
% 1.03/1.04  --abstr_ref_until_sat                   false
% 1.03/1.04  --abstr_ref_sig_restrict                funpre
% 1.03/1.04  --abstr_ref_af_restrict_to_split_sk     false
% 1.03/1.04  --abstr_ref_under                       []
% 1.03/1.04  
% 1.03/1.04  ------ SAT Options
% 1.03/1.04  
% 1.03/1.04  --sat_mode                              false
% 1.03/1.04  --sat_fm_restart_options                ""
% 1.03/1.04  --sat_gr_def                            false
% 1.03/1.04  --sat_epr_types                         true
% 1.03/1.04  --sat_non_cyclic_types                  false
% 1.03/1.04  --sat_finite_models                     false
% 1.03/1.04  --sat_fm_lemmas                         false
% 1.03/1.04  --sat_fm_prep                           false
% 1.03/1.04  --sat_fm_uc_incr                        true
% 1.03/1.04  --sat_out_model                         small
% 1.03/1.04  --sat_out_clauses                       false
% 1.03/1.04  
% 1.03/1.04  ------ QBF Options
% 1.03/1.04  
% 1.03/1.04  --qbf_mode                              false
% 1.03/1.04  --qbf_elim_univ                         false
% 1.03/1.04  --qbf_dom_inst                          none
% 1.03/1.04  --qbf_dom_pre_inst                      false
% 1.03/1.04  --qbf_sk_in                             false
% 1.03/1.04  --qbf_pred_elim                         true
% 1.03/1.04  --qbf_split                             512
% 1.03/1.04  
% 1.03/1.04  ------ BMC1 Options
% 1.03/1.04  
% 1.03/1.04  --bmc1_incremental                      false
% 1.03/1.04  --bmc1_axioms                           reachable_all
% 1.03/1.04  --bmc1_min_bound                        0
% 1.03/1.04  --bmc1_max_bound                        -1
% 1.03/1.04  --bmc1_max_bound_default                -1
% 1.03/1.04  --bmc1_symbol_reachability              true
% 1.03/1.04  --bmc1_property_lemmas                  false
% 1.03/1.04  --bmc1_k_induction                      false
% 1.03/1.04  --bmc1_non_equiv_states                 false
% 1.03/1.04  --bmc1_deadlock                         false
% 1.03/1.04  --bmc1_ucm                              false
% 1.03/1.04  --bmc1_add_unsat_core                   none
% 1.90/1.04  --bmc1_unsat_core_children              false
% 1.90/1.04  --bmc1_unsat_core_extrapolate_axioms    false
% 1.90/1.04  --bmc1_out_stat                         full
% 1.90/1.04  --bmc1_ground_init                      false
% 1.90/1.04  --bmc1_pre_inst_next_state              false
% 1.90/1.04  --bmc1_pre_inst_state                   false
% 1.90/1.04  --bmc1_pre_inst_reach_state             false
% 1.90/1.04  --bmc1_out_unsat_core                   false
% 1.90/1.04  --bmc1_aig_witness_out                  false
% 1.90/1.04  --bmc1_verbose                          false
% 1.90/1.04  --bmc1_dump_clauses_tptp                false
% 1.90/1.04  --bmc1_dump_unsat_core_tptp             false
% 1.90/1.04  --bmc1_dump_file                        -
% 1.90/1.04  --bmc1_ucm_expand_uc_limit              128
% 1.90/1.04  --bmc1_ucm_n_expand_iterations          6
% 1.90/1.04  --bmc1_ucm_extend_mode                  1
% 1.90/1.04  --bmc1_ucm_init_mode                    2
% 1.90/1.04  --bmc1_ucm_cone_mode                    none
% 1.90/1.04  --bmc1_ucm_reduced_relation_type        0
% 1.90/1.04  --bmc1_ucm_relax_model                  4
% 1.90/1.04  --bmc1_ucm_full_tr_after_sat            true
% 1.90/1.04  --bmc1_ucm_expand_neg_assumptions       false
% 1.90/1.04  --bmc1_ucm_layered_model                none
% 1.90/1.04  --bmc1_ucm_max_lemma_size               10
% 1.90/1.04  
% 1.90/1.04  ------ AIG Options
% 1.90/1.04  
% 1.90/1.04  --aig_mode                              false
% 1.90/1.04  
% 1.90/1.04  ------ Instantiation Options
% 1.90/1.04  
% 1.90/1.04  --instantiation_flag                    true
% 1.90/1.04  --inst_sos_flag                         false
% 1.90/1.04  --inst_sos_phase                        true
% 1.90/1.04  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 1.90/1.04  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 1.90/1.04  --inst_lit_sel_side                     num_symb
% 1.90/1.04  --inst_solver_per_active                1400
% 1.90/1.04  --inst_solver_calls_frac                1.
% 1.90/1.04  --inst_passive_queue_type               priority_queues
% 1.90/1.04  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 1.90/1.04  --inst_passive_queues_freq              [25;2]
% 1.90/1.04  --inst_dismatching                      true
% 1.90/1.04  --inst_eager_unprocessed_to_passive     true
% 1.90/1.04  --inst_prop_sim_given                   true
% 1.90/1.04  --inst_prop_sim_new                     false
% 1.90/1.04  --inst_subs_new                         false
% 1.90/1.04  --inst_eq_res_simp                      false
% 1.90/1.04  --inst_subs_given                       false
% 1.90/1.04  --inst_orphan_elimination               true
% 1.90/1.04  --inst_learning_loop_flag               true
% 1.90/1.04  --inst_learning_start                   3000
% 1.90/1.04  --inst_learning_factor                  2
% 1.90/1.04  --inst_start_prop_sim_after_learn       3
% 1.90/1.04  --inst_sel_renew                        solver
% 1.90/1.04  --inst_lit_activity_flag                true
% 1.90/1.04  --inst_restr_to_given                   false
% 1.90/1.04  --inst_activity_threshold               500
% 1.90/1.04  --inst_out_proof                        true
% 1.90/1.04  
% 1.90/1.04  ------ Resolution Options
% 1.90/1.04  
% 1.90/1.04  --resolution_flag                       true
% 1.90/1.04  --res_lit_sel                           adaptive
% 1.90/1.04  --res_lit_sel_side                      none
% 1.90/1.04  --res_ordering                          kbo
% 1.90/1.04  --res_to_prop_solver                    active
% 1.90/1.04  --res_prop_simpl_new                    false
% 1.90/1.04  --res_prop_simpl_given                  true
% 1.90/1.04  --res_passive_queue_type                priority_queues
% 1.90/1.04  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 1.90/1.04  --res_passive_queues_freq               [15;5]
% 1.90/1.04  --res_forward_subs                      full
% 1.90/1.04  --res_backward_subs                     full
% 1.90/1.04  --res_forward_subs_resolution           true
% 1.90/1.04  --res_backward_subs_resolution          true
% 1.90/1.04  --res_orphan_elimination                true
% 1.90/1.04  --res_time_limit                        2.
% 1.90/1.04  --res_out_proof                         true
% 1.90/1.04  
% 1.90/1.04  ------ Superposition Options
% 1.90/1.04  
% 1.90/1.04  --superposition_flag                    true
% 1.90/1.04  --sup_passive_queue_type                priority_queues
% 1.90/1.04  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 1.90/1.04  --sup_passive_queues_freq               [8;1;4]
% 1.90/1.04  --demod_completeness_check              fast
% 1.90/1.04  --demod_use_ground                      true
% 1.90/1.04  --sup_to_prop_solver                    passive
% 1.90/1.04  --sup_prop_simpl_new                    true
% 1.90/1.04  --sup_prop_simpl_given                  true
% 1.90/1.04  --sup_fun_splitting                     false
% 1.90/1.04  --sup_smt_interval                      50000
% 1.90/1.04  
% 1.90/1.04  ------ Superposition Simplification Setup
% 1.90/1.04  
% 1.90/1.04  --sup_indices_passive                   []
% 1.90/1.04  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 1.90/1.04  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 1.90/1.04  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 1.90/1.04  --sup_full_triv                         [TrivRules;PropSubs]
% 1.90/1.04  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 1.90/1.04  --sup_full_bw                           [BwDemod]
% 1.90/1.04  --sup_immed_triv                        [TrivRules]
% 1.90/1.04  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 1.90/1.04  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 1.90/1.04  --sup_immed_bw_main                     []
% 1.90/1.04  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 1.90/1.04  --sup_input_triv                        [Unflattening;TrivRules]
% 1.90/1.04  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 1.90/1.04  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 1.90/1.04  
% 1.90/1.04  ------ Combination Options
% 1.90/1.04  
% 1.90/1.04  --comb_res_mult                         3
% 1.90/1.04  --comb_sup_mult                         2
% 1.90/1.04  --comb_inst_mult                        10
% 1.90/1.04  
% 1.90/1.04  ------ Debug Options
% 1.90/1.04  
% 1.90/1.04  --dbg_backtrace                         false
% 1.90/1.04  --dbg_dump_prop_clauses                 false
% 1.90/1.04  --dbg_dump_prop_clauses_file            -
% 1.90/1.04  --dbg_out_stat                          false
% 1.90/1.04  ------ Parsing...
% 1.90/1.04  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 1.90/1.04  
% 1.90/1.04  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe:1:0s pe:2:0s pe:4:0s pe:8:0s pe_e  sf_s  rm: 9 0s  sf_e  pe_s  pe_e 
% 1.90/1.04  
% 1.90/1.04  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 1.90/1.04  
% 1.90/1.04  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 1.90/1.04  ------ Proving...
% 1.90/1.04  ------ Problem Properties 
% 1.90/1.04  
% 1.90/1.04  
% 1.90/1.04  clauses                                 20
% 1.90/1.04  conjectures                             2
% 1.90/1.04  EPR                                     2
% 1.90/1.04  Horn                                    14
% 1.90/1.04  unary                                   6
% 1.90/1.04  binary                                  5
% 1.90/1.04  lits                                    48
% 1.90/1.04  lits eq                                 8
% 1.90/1.04  fd_pure                                 0
% 1.90/1.04  fd_pseudo                               0
% 1.90/1.04  fd_cond                                 0
% 1.90/1.04  fd_pseudo_cond                          2
% 1.90/1.04  AC symbols                              0
% 1.90/1.04  
% 1.90/1.04  ------ Schedule dynamic 5 is on 
% 1.90/1.04  
% 1.90/1.04  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" Time Limit: 10.
% 1.90/1.04  
% 1.90/1.04  
% 1.90/1.04  ------ 
% 1.90/1.04  Current options:
% 1.90/1.04  ------ 
% 1.90/1.04  
% 1.90/1.04  ------ Input Options
% 1.90/1.04  
% 1.90/1.04  --out_options                           all
% 1.90/1.04  --tptp_safe_out                         true
% 1.90/1.04  --problem_path                          ""
% 1.90/1.04  --include_path                          ""
% 1.90/1.04  --clausifier                            res/vclausify_rel
% 1.90/1.04  --clausifier_options                    --mode clausify
% 1.90/1.04  --stdin                                 false
% 1.90/1.04  --stats_out                             all
% 1.90/1.04  
% 1.90/1.04  ------ General Options
% 1.90/1.04  
% 1.90/1.04  --fof                                   false
% 1.90/1.04  --time_out_real                         305.
% 1.90/1.04  --time_out_virtual                      -1.
% 1.90/1.04  --symbol_type_check                     false
% 1.90/1.04  --clausify_out                          false
% 1.90/1.04  --sig_cnt_out                           false
% 1.90/1.04  --trig_cnt_out                          false
% 1.90/1.04  --trig_cnt_out_tolerance                1.
% 1.90/1.04  --trig_cnt_out_sk_spl                   false
% 1.90/1.04  --abstr_cl_out                          false
% 1.90/1.04  
% 1.90/1.04  ------ Global Options
% 1.90/1.04  
% 1.90/1.04  --schedule                              default
% 1.90/1.04  --add_important_lit                     false
% 1.90/1.04  --prop_solver_per_cl                    1000
% 1.90/1.04  --min_unsat_core                        false
% 1.90/1.04  --soft_assumptions                      false
% 1.90/1.04  --soft_lemma_size                       3
% 1.90/1.04  --prop_impl_unit_size                   0
% 1.90/1.04  --prop_impl_unit                        []
% 1.90/1.04  --share_sel_clauses                     true
% 1.90/1.04  --reset_solvers                         false
% 1.90/1.04  --bc_imp_inh                            [conj_cone]
% 1.90/1.04  --conj_cone_tolerance                   3.
% 1.90/1.04  --extra_neg_conj                        none
% 1.90/1.04  --large_theory_mode                     true
% 1.90/1.04  --prolific_symb_bound                   200
% 1.90/1.04  --lt_threshold                          2000
% 1.90/1.04  --clause_weak_htbl                      true
% 1.90/1.04  --gc_record_bc_elim                     false
% 1.90/1.04  
% 1.90/1.04  ------ Preprocessing Options
% 1.90/1.04  
% 1.90/1.04  --preprocessing_flag                    true
% 1.90/1.04  --time_out_prep_mult                    0.1
% 1.90/1.04  --splitting_mode                        input
% 1.90/1.04  --splitting_grd                         true
% 1.90/1.04  --splitting_cvd                         false
% 1.90/1.04  --splitting_cvd_svl                     false
% 1.90/1.04  --splitting_nvd                         32
% 1.90/1.04  --sub_typing                            true
% 1.90/1.04  --prep_gs_sim                           true
% 1.90/1.04  --prep_unflatten                        true
% 1.90/1.04  --prep_res_sim                          true
% 1.90/1.04  --prep_upred                            true
% 1.90/1.04  --prep_sem_filter                       exhaustive
% 1.90/1.04  --prep_sem_filter_out                   false
% 1.90/1.04  --pred_elim                             true
% 1.90/1.04  --res_sim_input                         true
% 1.90/1.04  --eq_ax_congr_red                       true
% 1.90/1.04  --pure_diseq_elim                       true
% 1.90/1.04  --brand_transform                       false
% 1.90/1.04  --non_eq_to_eq                          false
% 1.90/1.04  --prep_def_merge                        true
% 1.90/1.04  --prep_def_merge_prop_impl              false
% 1.90/1.04  --prep_def_merge_mbd                    true
% 1.90/1.04  --prep_def_merge_tr_red                 false
% 1.90/1.04  --prep_def_merge_tr_cl                  false
% 1.90/1.04  --smt_preprocessing                     true
% 1.90/1.04  --smt_ac_axioms                         fast
% 1.90/1.04  --preprocessed_out                      false
% 1.90/1.04  --preprocessed_stats                    false
% 1.90/1.04  
% 1.90/1.04  ------ Abstraction refinement Options
% 1.90/1.04  
% 1.90/1.04  --abstr_ref                             []
% 1.90/1.04  --abstr_ref_prep                        false
% 1.90/1.04  --abstr_ref_until_sat                   false
% 1.90/1.04  --abstr_ref_sig_restrict                funpre
% 1.90/1.04  --abstr_ref_af_restrict_to_split_sk     false
% 1.90/1.04  --abstr_ref_under                       []
% 1.90/1.04  
% 1.90/1.04  ------ SAT Options
% 1.90/1.04  
% 1.90/1.04  --sat_mode                              false
% 1.90/1.04  --sat_fm_restart_options                ""
% 1.90/1.04  --sat_gr_def                            false
% 1.90/1.04  --sat_epr_types                         true
% 1.90/1.04  --sat_non_cyclic_types                  false
% 1.90/1.04  --sat_finite_models                     false
% 1.90/1.04  --sat_fm_lemmas                         false
% 1.90/1.04  --sat_fm_prep                           false
% 1.90/1.04  --sat_fm_uc_incr                        true
% 1.90/1.04  --sat_out_model                         small
% 1.90/1.04  --sat_out_clauses                       false
% 1.90/1.04  
% 1.90/1.04  ------ QBF Options
% 1.90/1.04  
% 1.90/1.04  --qbf_mode                              false
% 1.90/1.04  --qbf_elim_univ                         false
% 1.90/1.04  --qbf_dom_inst                          none
% 1.90/1.04  --qbf_dom_pre_inst                      false
% 1.90/1.04  --qbf_sk_in                             false
% 1.90/1.04  --qbf_pred_elim                         true
% 1.90/1.04  --qbf_split                             512
% 1.90/1.04  
% 1.90/1.04  ------ BMC1 Options
% 1.90/1.04  
% 1.90/1.04  --bmc1_incremental                      false
% 1.90/1.04  --bmc1_axioms                           reachable_all
% 1.90/1.04  --bmc1_min_bound                        0
% 1.90/1.04  --bmc1_max_bound                        -1
% 1.90/1.04  --bmc1_max_bound_default                -1
% 1.90/1.04  --bmc1_symbol_reachability              true
% 1.90/1.04  --bmc1_property_lemmas                  false
% 1.90/1.04  --bmc1_k_induction                      false
% 1.90/1.04  --bmc1_non_equiv_states                 false
% 1.90/1.04  --bmc1_deadlock                         false
% 1.90/1.04  --bmc1_ucm                              false
% 1.90/1.04  --bmc1_add_unsat_core                   none
% 1.90/1.04  --bmc1_unsat_core_children              false
% 1.90/1.04  --bmc1_unsat_core_extrapolate_axioms    false
% 1.90/1.04  --bmc1_out_stat                         full
% 1.90/1.04  --bmc1_ground_init                      false
% 1.90/1.04  --bmc1_pre_inst_next_state              false
% 1.90/1.04  --bmc1_pre_inst_state                   false
% 1.90/1.04  --bmc1_pre_inst_reach_state             false
% 1.90/1.04  --bmc1_out_unsat_core                   false
% 1.90/1.04  --bmc1_aig_witness_out                  false
% 1.90/1.04  --bmc1_verbose                          false
% 1.90/1.04  --bmc1_dump_clauses_tptp                false
% 1.90/1.04  --bmc1_dump_unsat_core_tptp             false
% 1.90/1.04  --bmc1_dump_file                        -
% 1.90/1.04  --bmc1_ucm_expand_uc_limit              128
% 1.90/1.04  --bmc1_ucm_n_expand_iterations          6
% 1.90/1.04  --bmc1_ucm_extend_mode                  1
% 1.90/1.04  --bmc1_ucm_init_mode                    2
% 1.90/1.04  --bmc1_ucm_cone_mode                    none
% 1.90/1.04  --bmc1_ucm_reduced_relation_type        0
% 1.90/1.04  --bmc1_ucm_relax_model                  4
% 1.90/1.04  --bmc1_ucm_full_tr_after_sat            true
% 1.90/1.04  --bmc1_ucm_expand_neg_assumptions       false
% 1.90/1.04  --bmc1_ucm_layered_model                none
% 1.90/1.04  --bmc1_ucm_max_lemma_size               10
% 1.90/1.04  
% 1.90/1.04  ------ AIG Options
% 1.90/1.04  
% 1.90/1.04  --aig_mode                              false
% 1.90/1.04  
% 1.90/1.04  ------ Instantiation Options
% 1.90/1.04  
% 1.90/1.04  --instantiation_flag                    true
% 1.90/1.04  --inst_sos_flag                         false
% 1.90/1.04  --inst_sos_phase                        true
% 1.90/1.04  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 1.90/1.04  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 1.90/1.04  --inst_lit_sel_side                     none
% 1.90/1.04  --inst_solver_per_active                1400
% 1.90/1.04  --inst_solver_calls_frac                1.
% 1.90/1.04  --inst_passive_queue_type               priority_queues
% 1.90/1.04  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 1.90/1.04  --inst_passive_queues_freq              [25;2]
% 1.90/1.04  --inst_dismatching                      true
% 1.90/1.04  --inst_eager_unprocessed_to_passive     true
% 1.90/1.04  --inst_prop_sim_given                   true
% 1.90/1.04  --inst_prop_sim_new                     false
% 1.90/1.04  --inst_subs_new                         false
% 1.90/1.04  --inst_eq_res_simp                      false
% 1.90/1.04  --inst_subs_given                       false
% 1.90/1.04  --inst_orphan_elimination               true
% 1.90/1.04  --inst_learning_loop_flag               true
% 1.90/1.04  --inst_learning_start                   3000
% 1.90/1.04  --inst_learning_factor                  2
% 1.90/1.04  --inst_start_prop_sim_after_learn       3
% 1.90/1.04  --inst_sel_renew                        solver
% 1.90/1.04  --inst_lit_activity_flag                true
% 1.90/1.04  --inst_restr_to_given                   false
% 1.90/1.04  --inst_activity_threshold               500
% 1.90/1.04  --inst_out_proof                        true
% 1.90/1.04  
% 1.90/1.04  ------ Resolution Options
% 1.90/1.04  
% 1.90/1.04  --resolution_flag                       false
% 1.90/1.04  --res_lit_sel                           adaptive
% 1.90/1.04  --res_lit_sel_side                      none
% 1.90/1.04  --res_ordering                          kbo
% 1.90/1.04  --res_to_prop_solver                    active
% 1.90/1.04  --res_prop_simpl_new                    false
% 1.90/1.04  --res_prop_simpl_given                  true
% 1.90/1.04  --res_passive_queue_type                priority_queues
% 1.90/1.04  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 1.90/1.04  --res_passive_queues_freq               [15;5]
% 1.90/1.04  --res_forward_subs                      full
% 1.90/1.04  --res_backward_subs                     full
% 1.90/1.04  --res_forward_subs_resolution           true
% 1.90/1.04  --res_backward_subs_resolution          true
% 1.90/1.04  --res_orphan_elimination                true
% 1.90/1.04  --res_time_limit                        2.
% 1.90/1.04  --res_out_proof                         true
% 1.90/1.04  
% 1.90/1.04  ------ Superposition Options
% 1.90/1.04  
% 1.90/1.04  --superposition_flag                    true
% 1.90/1.04  --sup_passive_queue_type                priority_queues
% 1.90/1.04  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 1.90/1.04  --sup_passive_queues_freq               [8;1;4]
% 1.90/1.04  --demod_completeness_check              fast
% 1.90/1.04  --demod_use_ground                      true
% 1.90/1.04  --sup_to_prop_solver                    passive
% 1.90/1.04  --sup_prop_simpl_new                    true
% 1.90/1.04  --sup_prop_simpl_given                  true
% 1.90/1.04  --sup_fun_splitting                     false
% 1.90/1.04  --sup_smt_interval                      50000
% 1.90/1.04  
% 1.90/1.04  ------ Superposition Simplification Setup
% 1.90/1.04  
% 1.90/1.04  --sup_indices_passive                   []
% 1.90/1.04  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 1.90/1.04  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 1.90/1.04  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 1.90/1.04  --sup_full_triv                         [TrivRules;PropSubs]
% 1.90/1.04  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 1.90/1.04  --sup_full_bw                           [BwDemod]
% 1.90/1.04  --sup_immed_triv                        [TrivRules]
% 1.90/1.04  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 1.90/1.04  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 1.90/1.04  --sup_immed_bw_main                     []
% 1.90/1.04  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 1.90/1.04  --sup_input_triv                        [Unflattening;TrivRules]
% 1.90/1.04  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 1.90/1.04  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 1.90/1.04  
% 1.90/1.04  ------ Combination Options
% 1.90/1.04  
% 1.90/1.04  --comb_res_mult                         3
% 1.90/1.04  --comb_sup_mult                         2
% 1.90/1.04  --comb_inst_mult                        10
% 1.90/1.04  
% 1.90/1.04  ------ Debug Options
% 1.90/1.04  
% 1.90/1.04  --dbg_backtrace                         false
% 1.90/1.04  --dbg_dump_prop_clauses                 false
% 1.90/1.04  --dbg_dump_prop_clauses_file            -
% 1.90/1.04  --dbg_out_stat                          false
% 1.90/1.04  
% 1.90/1.04  
% 1.90/1.04  
% 1.90/1.04  
% 1.90/1.04  ------ Proving...
% 1.90/1.04  
% 1.90/1.04  
% 1.90/1.04  % SZS status Theorem for theBenchmark.p
% 1.90/1.04  
% 1.90/1.04  % SZS output start CNFRefutation for theBenchmark.p
% 1.90/1.04  
% 1.90/1.04  fof(f9,axiom,(
% 1.90/1.04    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => (v1_subset_1(X1,X0) <=> X0 != X1))),
% 1.90/1.04    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 1.90/1.04  
% 1.90/1.04  fof(f26,plain,(
% 1.90/1.04    ! [X0,X1] : ((v1_subset_1(X1,X0) <=> X0 != X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 1.90/1.04    inference(ennf_transformation,[],[f9])).
% 1.90/1.04  
% 1.90/1.04  fof(f38,plain,(
% 1.90/1.04    ! [X0,X1] : (((v1_subset_1(X1,X0) | X0 = X1) & (X0 != X1 | ~v1_subset_1(X1,X0))) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 1.90/1.04    inference(nnf_transformation,[],[f26])).
% 1.90/1.04  
% 1.90/1.04  fof(f61,plain,(
% 1.90/1.04    ( ! [X0,X1] : (v1_subset_1(X1,X0) | X0 = X1 | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 1.90/1.04    inference(cnf_transformation,[],[f38])).
% 1.90/1.04  
% 1.90/1.04  fof(f10,conjecture,(
% 1.90/1.04    ! [X0] : ((l1_orders_2(X0) & v1_yellow_0(X0) & v5_orders_2(X0) & v4_orders_2(X0) & v3_orders_2(X0) & ~v2_struct_0(X0)) => ! [X1] : ((m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & v13_waybel_0(X1,X0) & v2_waybel_0(X1,X0) & ~v1_xboole_0(X1)) => (v1_subset_1(X1,u1_struct_0(X0)) <=> ~r2_hidden(k3_yellow_0(X0),X1))))),
% 1.90/1.04    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 1.90/1.04  
% 1.90/1.04  fof(f11,negated_conjecture,(
% 1.90/1.04    ~! [X0] : ((l1_orders_2(X0) & v1_yellow_0(X0) & v5_orders_2(X0) & v4_orders_2(X0) & v3_orders_2(X0) & ~v2_struct_0(X0)) => ! [X1] : ((m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & v13_waybel_0(X1,X0) & v2_waybel_0(X1,X0) & ~v1_xboole_0(X1)) => (v1_subset_1(X1,u1_struct_0(X0)) <=> ~r2_hidden(k3_yellow_0(X0),X1))))),
% 1.90/1.04    inference(negated_conjecture,[],[f10])).
% 1.90/1.04  
% 1.90/1.04  fof(f12,plain,(
% 1.90/1.04    ~! [X0] : ((l1_orders_2(X0) & v1_yellow_0(X0) & v5_orders_2(X0) & v4_orders_2(X0) & v3_orders_2(X0) & ~v2_struct_0(X0)) => ! [X1] : ((m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & v13_waybel_0(X1,X0) & ~v1_xboole_0(X1)) => (v1_subset_1(X1,u1_struct_0(X0)) <=> ~r2_hidden(k3_yellow_0(X0),X1))))),
% 1.90/1.04    inference(pure_predicate_removal,[],[f11])).
% 1.90/1.04  
% 1.90/1.04  fof(f13,plain,(
% 1.90/1.04    ~! [X0] : ((l1_orders_2(X0) & v1_yellow_0(X0) & v5_orders_2(X0) & v3_orders_2(X0) & ~v2_struct_0(X0)) => ! [X1] : ((m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & v13_waybel_0(X1,X0) & ~v1_xboole_0(X1)) => (v1_subset_1(X1,u1_struct_0(X0)) <=> ~r2_hidden(k3_yellow_0(X0),X1))))),
% 1.90/1.04    inference(pure_predicate_removal,[],[f12])).
% 1.90/1.04  
% 1.90/1.04  fof(f27,plain,(
% 1.90/1.04    ? [X0] : (? [X1] : ((v1_subset_1(X1,u1_struct_0(X0)) <~> ~r2_hidden(k3_yellow_0(X0),X1)) & (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & v13_waybel_0(X1,X0) & ~v1_xboole_0(X1))) & (l1_orders_2(X0) & v1_yellow_0(X0) & v5_orders_2(X0) & v3_orders_2(X0) & ~v2_struct_0(X0)))),
% 1.90/1.04    inference(ennf_transformation,[],[f13])).
% 1.90/1.04  
% 1.90/1.04  fof(f28,plain,(
% 1.90/1.04    ? [X0] : (? [X1] : ((v1_subset_1(X1,u1_struct_0(X0)) <~> ~r2_hidden(k3_yellow_0(X0),X1)) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & v13_waybel_0(X1,X0) & ~v1_xboole_0(X1)) & l1_orders_2(X0) & v1_yellow_0(X0) & v5_orders_2(X0) & v3_orders_2(X0) & ~v2_struct_0(X0))),
% 1.90/1.04    inference(flattening,[],[f27])).
% 1.90/1.04  
% 1.90/1.04  fof(f39,plain,(
% 1.90/1.04    ? [X0] : (? [X1] : (((r2_hidden(k3_yellow_0(X0),X1) | ~v1_subset_1(X1,u1_struct_0(X0))) & (~r2_hidden(k3_yellow_0(X0),X1) | v1_subset_1(X1,u1_struct_0(X0)))) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & v13_waybel_0(X1,X0) & ~v1_xboole_0(X1)) & l1_orders_2(X0) & v1_yellow_0(X0) & v5_orders_2(X0) & v3_orders_2(X0) & ~v2_struct_0(X0))),
% 1.90/1.04    inference(nnf_transformation,[],[f28])).
% 1.90/1.04  
% 1.90/1.04  fof(f40,plain,(
% 1.90/1.04    ? [X0] : (? [X1] : ((r2_hidden(k3_yellow_0(X0),X1) | ~v1_subset_1(X1,u1_struct_0(X0))) & (~r2_hidden(k3_yellow_0(X0),X1) | v1_subset_1(X1,u1_struct_0(X0))) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & v13_waybel_0(X1,X0) & ~v1_xboole_0(X1)) & l1_orders_2(X0) & v1_yellow_0(X0) & v5_orders_2(X0) & v3_orders_2(X0) & ~v2_struct_0(X0))),
% 1.90/1.04    inference(flattening,[],[f39])).
% 1.90/1.04  
% 1.90/1.04  fof(f42,plain,(
% 1.90/1.04    ( ! [X0] : (? [X1] : ((r2_hidden(k3_yellow_0(X0),X1) | ~v1_subset_1(X1,u1_struct_0(X0))) & (~r2_hidden(k3_yellow_0(X0),X1) | v1_subset_1(X1,u1_struct_0(X0))) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & v13_waybel_0(X1,X0) & ~v1_xboole_0(X1)) => ((r2_hidden(k3_yellow_0(X0),sK5) | ~v1_subset_1(sK5,u1_struct_0(X0))) & (~r2_hidden(k3_yellow_0(X0),sK5) | v1_subset_1(sK5,u1_struct_0(X0))) & m1_subset_1(sK5,k1_zfmisc_1(u1_struct_0(X0))) & v13_waybel_0(sK5,X0) & ~v1_xboole_0(sK5))) )),
% 1.90/1.04    introduced(choice_axiom,[])).
% 1.90/1.04  
% 1.90/1.04  fof(f41,plain,(
% 1.90/1.04    ? [X0] : (? [X1] : ((r2_hidden(k3_yellow_0(X0),X1) | ~v1_subset_1(X1,u1_struct_0(X0))) & (~r2_hidden(k3_yellow_0(X0),X1) | v1_subset_1(X1,u1_struct_0(X0))) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & v13_waybel_0(X1,X0) & ~v1_xboole_0(X1)) & l1_orders_2(X0) & v1_yellow_0(X0) & v5_orders_2(X0) & v3_orders_2(X0) & ~v2_struct_0(X0)) => (? [X1] : ((r2_hidden(k3_yellow_0(sK4),X1) | ~v1_subset_1(X1,u1_struct_0(sK4))) & (~r2_hidden(k3_yellow_0(sK4),X1) | v1_subset_1(X1,u1_struct_0(sK4))) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK4))) & v13_waybel_0(X1,sK4) & ~v1_xboole_0(X1)) & l1_orders_2(sK4) & v1_yellow_0(sK4) & v5_orders_2(sK4) & v3_orders_2(sK4) & ~v2_struct_0(sK4))),
% 1.90/1.04    introduced(choice_axiom,[])).
% 1.90/1.04  
% 1.90/1.04  fof(f43,plain,(
% 1.90/1.04    ((r2_hidden(k3_yellow_0(sK4),sK5) | ~v1_subset_1(sK5,u1_struct_0(sK4))) & (~r2_hidden(k3_yellow_0(sK4),sK5) | v1_subset_1(sK5,u1_struct_0(sK4))) & m1_subset_1(sK5,k1_zfmisc_1(u1_struct_0(sK4))) & v13_waybel_0(sK5,sK4) & ~v1_xboole_0(sK5)) & l1_orders_2(sK4) & v1_yellow_0(sK4) & v5_orders_2(sK4) & v3_orders_2(sK4) & ~v2_struct_0(sK4)),
% 1.90/1.04    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4,sK5])],[f40,f42,f41])).
% 1.90/1.04  
% 1.90/1.04  fof(f71,plain,(
% 1.90/1.04    r2_hidden(k3_yellow_0(sK4),sK5) | ~v1_subset_1(sK5,u1_struct_0(sK4))),
% 1.90/1.04    inference(cnf_transformation,[],[f43])).
% 1.90/1.04  
% 1.90/1.04  fof(f69,plain,(
% 1.90/1.04    m1_subset_1(sK5,k1_zfmisc_1(u1_struct_0(sK4)))),
% 1.90/1.04    inference(cnf_transformation,[],[f43])).
% 1.90/1.04  
% 1.90/1.04  fof(f8,axiom,(
% 1.90/1.04    ! [X0] : (l1_orders_2(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => (v13_waybel_0(X1,X0) <=> ! [X2] : (m1_subset_1(X2,u1_struct_0(X0)) => ! [X3] : (m1_subset_1(X3,u1_struct_0(X0)) => ((r1_orders_2(X0,X2,X3) & r2_hidden(X2,X1)) => r2_hidden(X3,X1)))))))),
% 1.90/1.04    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 1.90/1.04  
% 1.90/1.04  fof(f24,plain,(
% 1.90/1.04    ! [X0] : (! [X1] : ((v13_waybel_0(X1,X0) <=> ! [X2] : (! [X3] : ((r2_hidden(X3,X1) | (~r1_orders_2(X0,X2,X3) | ~r2_hidden(X2,X1))) | ~m1_subset_1(X3,u1_struct_0(X0))) | ~m1_subset_1(X2,u1_struct_0(X0)))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_orders_2(X0))),
% 1.90/1.04    inference(ennf_transformation,[],[f8])).
% 1.90/1.04  
% 1.90/1.04  fof(f25,plain,(
% 1.90/1.04    ! [X0] : (! [X1] : ((v13_waybel_0(X1,X0) <=> ! [X2] : (! [X3] : (r2_hidden(X3,X1) | ~r1_orders_2(X0,X2,X3) | ~r2_hidden(X2,X1) | ~m1_subset_1(X3,u1_struct_0(X0))) | ~m1_subset_1(X2,u1_struct_0(X0)))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_orders_2(X0))),
% 1.90/1.04    inference(flattening,[],[f24])).
% 1.90/1.04  
% 1.90/1.04  fof(f33,plain,(
% 1.90/1.04    ! [X0] : (! [X1] : (((v13_waybel_0(X1,X0) | ? [X2] : (? [X3] : (~r2_hidden(X3,X1) & r1_orders_2(X0,X2,X3) & r2_hidden(X2,X1) & m1_subset_1(X3,u1_struct_0(X0))) & m1_subset_1(X2,u1_struct_0(X0)))) & (! [X2] : (! [X3] : (r2_hidden(X3,X1) | ~r1_orders_2(X0,X2,X3) | ~r2_hidden(X2,X1) | ~m1_subset_1(X3,u1_struct_0(X0))) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~v13_waybel_0(X1,X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_orders_2(X0))),
% 1.90/1.04    inference(nnf_transformation,[],[f25])).
% 1.90/1.04  
% 1.90/1.04  fof(f34,plain,(
% 1.90/1.04    ! [X0] : (! [X1] : (((v13_waybel_0(X1,X0) | ? [X2] : (? [X3] : (~r2_hidden(X3,X1) & r1_orders_2(X0,X2,X3) & r2_hidden(X2,X1) & m1_subset_1(X3,u1_struct_0(X0))) & m1_subset_1(X2,u1_struct_0(X0)))) & (! [X4] : (! [X5] : (r2_hidden(X5,X1) | ~r1_orders_2(X0,X4,X5) | ~r2_hidden(X4,X1) | ~m1_subset_1(X5,u1_struct_0(X0))) | ~m1_subset_1(X4,u1_struct_0(X0))) | ~v13_waybel_0(X1,X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_orders_2(X0))),
% 1.90/1.04    inference(rectify,[],[f33])).
% 1.90/1.04  
% 1.90/1.04  fof(f36,plain,(
% 1.90/1.04    ( ! [X2] : (! [X1,X0] : (? [X3] : (~r2_hidden(X3,X1) & r1_orders_2(X0,X2,X3) & r2_hidden(X2,X1) & m1_subset_1(X3,u1_struct_0(X0))) => (~r2_hidden(sK3(X0,X1),X1) & r1_orders_2(X0,X2,sK3(X0,X1)) & r2_hidden(X2,X1) & m1_subset_1(sK3(X0,X1),u1_struct_0(X0))))) )),
% 1.90/1.04    introduced(choice_axiom,[])).
% 1.90/1.04  
% 1.90/1.04  fof(f35,plain,(
% 1.90/1.04    ! [X1,X0] : (? [X2] : (? [X3] : (~r2_hidden(X3,X1) & r1_orders_2(X0,X2,X3) & r2_hidden(X2,X1) & m1_subset_1(X3,u1_struct_0(X0))) & m1_subset_1(X2,u1_struct_0(X0))) => (? [X3] : (~r2_hidden(X3,X1) & r1_orders_2(X0,sK2(X0,X1),X3) & r2_hidden(sK2(X0,X1),X1) & m1_subset_1(X3,u1_struct_0(X0))) & m1_subset_1(sK2(X0,X1),u1_struct_0(X0))))),
% 1.90/1.04    introduced(choice_axiom,[])).
% 1.90/1.04  
% 1.90/1.04  fof(f37,plain,(
% 1.90/1.04    ! [X0] : (! [X1] : (((v13_waybel_0(X1,X0) | ((~r2_hidden(sK3(X0,X1),X1) & r1_orders_2(X0,sK2(X0,X1),sK3(X0,X1)) & r2_hidden(sK2(X0,X1),X1) & m1_subset_1(sK3(X0,X1),u1_struct_0(X0))) & m1_subset_1(sK2(X0,X1),u1_struct_0(X0)))) & (! [X4] : (! [X5] : (r2_hidden(X5,X1) | ~r1_orders_2(X0,X4,X5) | ~r2_hidden(X4,X1) | ~m1_subset_1(X5,u1_struct_0(X0))) | ~m1_subset_1(X4,u1_struct_0(X0))) | ~v13_waybel_0(X1,X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_orders_2(X0))),
% 1.90/1.04    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2,sK3])],[f34,f36,f35])).
% 1.90/1.04  
% 1.90/1.04  fof(f54,plain,(
% 1.90/1.04    ( ! [X4,X0,X5,X1] : (r2_hidden(X5,X1) | ~r1_orders_2(X0,X4,X5) | ~r2_hidden(X4,X1) | ~m1_subset_1(X5,u1_struct_0(X0)) | ~m1_subset_1(X4,u1_struct_0(X0)) | ~v13_waybel_0(X1,X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_orders_2(X0)) )),
% 1.90/1.04    inference(cnf_transformation,[],[f37])).
% 1.90/1.04  
% 1.90/1.04  fof(f7,axiom,(
% 1.90/1.04    ! [X0] : ((l1_orders_2(X0) & v1_yellow_0(X0) & v5_orders_2(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,u1_struct_0(X0)) => r1_orders_2(X0,k3_yellow_0(X0),X1)))),
% 1.90/1.04    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 1.90/1.04  
% 1.90/1.04  fof(f22,plain,(
% 1.90/1.04    ! [X0] : (! [X1] : (r1_orders_2(X0,k3_yellow_0(X0),X1) | ~m1_subset_1(X1,u1_struct_0(X0))) | (~l1_orders_2(X0) | ~v1_yellow_0(X0) | ~v5_orders_2(X0) | v2_struct_0(X0)))),
% 1.90/1.04    inference(ennf_transformation,[],[f7])).
% 1.90/1.04  
% 1.90/1.04  fof(f23,plain,(
% 1.90/1.04    ! [X0] : (! [X1] : (r1_orders_2(X0,k3_yellow_0(X0),X1) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~l1_orders_2(X0) | ~v1_yellow_0(X0) | ~v5_orders_2(X0) | v2_struct_0(X0))),
% 1.90/1.04    inference(flattening,[],[f22])).
% 1.90/1.04  
% 1.90/1.04  fof(f53,plain,(
% 1.90/1.04    ( ! [X0,X1] : (r1_orders_2(X0,k3_yellow_0(X0),X1) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_orders_2(X0) | ~v1_yellow_0(X0) | ~v5_orders_2(X0) | v2_struct_0(X0)) )),
% 1.90/1.04    inference(cnf_transformation,[],[f23])).
% 1.90/1.04  
% 1.90/1.04  fof(f65,plain,(
% 1.90/1.04    v1_yellow_0(sK4)),
% 1.90/1.04    inference(cnf_transformation,[],[f43])).
% 1.90/1.04  
% 1.90/1.04  fof(f62,plain,(
% 1.90/1.04    ~v2_struct_0(sK4)),
% 1.90/1.04    inference(cnf_transformation,[],[f43])).
% 1.90/1.04  
% 1.90/1.04  fof(f64,plain,(
% 1.90/1.04    v5_orders_2(sK4)),
% 1.90/1.04    inference(cnf_transformation,[],[f43])).
% 1.90/1.04  
% 1.90/1.04  fof(f66,plain,(
% 1.90/1.04    l1_orders_2(sK4)),
% 1.90/1.04    inference(cnf_transformation,[],[f43])).
% 1.90/1.04  
% 1.90/1.04  fof(f5,axiom,(
% 1.90/1.04    ! [X0] : (l1_orders_2(X0) => m1_subset_1(k3_yellow_0(X0),u1_struct_0(X0)))),
% 1.90/1.04    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 1.90/1.04  
% 1.90/1.04  fof(f19,plain,(
% 1.90/1.04    ! [X0] : (m1_subset_1(k3_yellow_0(X0),u1_struct_0(X0)) | ~l1_orders_2(X0))),
% 1.90/1.04    inference(ennf_transformation,[],[f5])).
% 1.90/1.04  
% 1.90/1.04  fof(f50,plain,(
% 1.90/1.04    ( ! [X0] : (m1_subset_1(k3_yellow_0(X0),u1_struct_0(X0)) | ~l1_orders_2(X0)) )),
% 1.90/1.04    inference(cnf_transformation,[],[f19])).
% 1.90/1.04  
% 1.90/1.04  fof(f68,plain,(
% 1.90/1.04    v13_waybel_0(sK5,sK4)),
% 1.90/1.04    inference(cnf_transformation,[],[f43])).
% 1.90/1.04  
% 1.90/1.04  fof(f60,plain,(
% 1.90/1.04    ( ! [X0,X1] : (X0 != X1 | ~v1_subset_1(X1,X0) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 1.90/1.04    inference(cnf_transformation,[],[f38])).
% 1.90/1.04  
% 1.90/1.04  fof(f72,plain,(
% 1.90/1.04    ( ! [X1] : (~v1_subset_1(X1,X1) | ~m1_subset_1(X1,k1_zfmisc_1(X1))) )),
% 1.90/1.04    inference(equality_resolution,[],[f60])).
% 1.90/1.04  
% 1.90/1.04  fof(f70,plain,(
% 1.90/1.04    ~r2_hidden(k3_yellow_0(sK4),sK5) | v1_subset_1(sK5,u1_struct_0(sK4))),
% 1.90/1.04    inference(cnf_transformation,[],[f43])).
% 1.90/1.04  
% 1.90/1.04  fof(f2,axiom,(
% 1.90/1.04    ! [X0] : ? [X1] : (~v1_subset_1(X1,X0) & m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 1.90/1.04    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 1.90/1.04  
% 1.90/1.04  fof(f31,plain,(
% 1.90/1.04    ! [X0] : (? [X1] : (~v1_subset_1(X1,X0) & m1_subset_1(X1,k1_zfmisc_1(X0))) => (~v1_subset_1(sK1(X0),X0) & m1_subset_1(sK1(X0),k1_zfmisc_1(X0))))),
% 1.90/1.04    introduced(choice_axiom,[])).
% 1.90/1.04  
% 1.90/1.04  fof(f32,plain,(
% 1.90/1.04    ! [X0] : (~v1_subset_1(sK1(X0),X0) & m1_subset_1(sK1(X0),k1_zfmisc_1(X0)))),
% 1.90/1.04    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1])],[f2,f31])).
% 1.90/1.04  
% 1.90/1.04  fof(f46,plain,(
% 1.90/1.04    ( ! [X0] : (m1_subset_1(sK1(X0),k1_zfmisc_1(X0))) )),
% 1.90/1.04    inference(cnf_transformation,[],[f32])).
% 1.90/1.04  
% 1.90/1.04  fof(f1,axiom,(
% 1.90/1.04    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => (! [X2] : (m1_subset_1(X2,X0) => r2_hidden(X2,X1)) => X0 = X1))),
% 1.90/1.04    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 1.90/1.04  
% 1.90/1.04  fof(f14,plain,(
% 1.90/1.04    ! [X0,X1] : ((X0 = X1 | ? [X2] : (~r2_hidden(X2,X1) & m1_subset_1(X2,X0))) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 1.90/1.04    inference(ennf_transformation,[],[f1])).
% 1.90/1.04  
% 1.90/1.04  fof(f15,plain,(
% 1.90/1.04    ! [X0,X1] : (X0 = X1 | ? [X2] : (~r2_hidden(X2,X1) & m1_subset_1(X2,X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 1.90/1.04    inference(flattening,[],[f14])).
% 1.90/1.04  
% 1.90/1.04  fof(f29,plain,(
% 1.90/1.04    ! [X1,X0] : (? [X2] : (~r2_hidden(X2,X1) & m1_subset_1(X2,X0)) => (~r2_hidden(sK0(X0,X1),X1) & m1_subset_1(sK0(X0,X1),X0)))),
% 1.90/1.04    introduced(choice_axiom,[])).
% 1.90/1.04  
% 1.90/1.04  fof(f30,plain,(
% 1.90/1.04    ! [X0,X1] : (X0 = X1 | (~r2_hidden(sK0(X0,X1),X1) & m1_subset_1(sK0(X0,X1),X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 1.90/1.04    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f15,f29])).
% 1.90/1.04  
% 1.90/1.04  fof(f45,plain,(
% 1.90/1.04    ( ! [X0,X1] : (X0 = X1 | ~r2_hidden(sK0(X0,X1),X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 1.90/1.04    inference(cnf_transformation,[],[f30])).
% 1.90/1.04  
% 1.90/1.04  fof(f47,plain,(
% 1.90/1.04    ( ! [X0] : (~v1_subset_1(sK1(X0),X0)) )),
% 1.90/1.04    inference(cnf_transformation,[],[f32])).
% 1.90/1.04  
% 1.90/1.04  fof(f44,plain,(
% 1.90/1.04    ( ! [X0,X1] : (X0 = X1 | m1_subset_1(sK0(X0,X1),X0) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 1.90/1.04    inference(cnf_transformation,[],[f30])).
% 1.90/1.04  
% 1.90/1.04  fof(f6,axiom,(
% 1.90/1.04    ! [X0] : ((l1_orders_2(X0) & v5_orders_2(X0) & v3_orders_2(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,u1_struct_0(X0)) => (k2_yellow_0(X0,k6_domain_1(u1_struct_0(X0),X1)) = X1 & k1_yellow_0(X0,k6_domain_1(u1_struct_0(X0),X1)) = X1)))),
% 1.90/1.04    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 1.90/1.04  
% 1.90/1.04  fof(f20,plain,(
% 1.90/1.04    ! [X0] : (! [X1] : ((k2_yellow_0(X0,k6_domain_1(u1_struct_0(X0),X1)) = X1 & k1_yellow_0(X0,k6_domain_1(u1_struct_0(X0),X1)) = X1) | ~m1_subset_1(X1,u1_struct_0(X0))) | (~l1_orders_2(X0) | ~v5_orders_2(X0) | ~v3_orders_2(X0) | v2_struct_0(X0)))),
% 1.90/1.04    inference(ennf_transformation,[],[f6])).
% 1.90/1.04  
% 1.90/1.04  fof(f21,plain,(
% 1.90/1.04    ! [X0] : (! [X1] : ((k2_yellow_0(X0,k6_domain_1(u1_struct_0(X0),X1)) = X1 & k1_yellow_0(X0,k6_domain_1(u1_struct_0(X0),X1)) = X1) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~l1_orders_2(X0) | ~v5_orders_2(X0) | ~v3_orders_2(X0) | v2_struct_0(X0))),
% 1.90/1.04    inference(flattening,[],[f20])).
% 1.90/1.04  
% 1.90/1.04  fof(f51,plain,(
% 1.90/1.04    ( ! [X0,X1] : (k1_yellow_0(X0,k6_domain_1(u1_struct_0(X0),X1)) = X1 | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_orders_2(X0) | ~v5_orders_2(X0) | ~v3_orders_2(X0) | v2_struct_0(X0)) )),
% 1.90/1.04    inference(cnf_transformation,[],[f21])).
% 1.90/1.04  
% 1.90/1.04  fof(f63,plain,(
% 1.90/1.04    v3_orders_2(sK4)),
% 1.90/1.04    inference(cnf_transformation,[],[f43])).
% 1.90/1.04  
% 1.90/1.04  fof(f4,axiom,(
% 1.90/1.04    ! [X0,X1] : (l1_orders_2(X0) => m1_subset_1(k1_yellow_0(X0,X1),u1_struct_0(X0)))),
% 1.90/1.04    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 1.90/1.04  
% 1.90/1.04  fof(f18,plain,(
% 1.90/1.04    ! [X0,X1] : (m1_subset_1(k1_yellow_0(X0,X1),u1_struct_0(X0)) | ~l1_orders_2(X0))),
% 1.90/1.04    inference(ennf_transformation,[],[f4])).
% 1.90/1.04  
% 1.90/1.04  fof(f49,plain,(
% 1.90/1.04    ( ! [X0,X1] : (m1_subset_1(k1_yellow_0(X0,X1),u1_struct_0(X0)) | ~l1_orders_2(X0)) )),
% 1.90/1.04    inference(cnf_transformation,[],[f18])).
% 1.90/1.04  
% 1.90/1.04  fof(f3,axiom,(
% 1.90/1.04    ! [X0,X1] : (m1_subset_1(X0,X1) => (r2_hidden(X0,X1) | v1_xboole_0(X1)))),
% 1.90/1.04    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 1.90/1.04  
% 1.90/1.04  fof(f16,plain,(
% 1.90/1.04    ! [X0,X1] : ((r2_hidden(X0,X1) | v1_xboole_0(X1)) | ~m1_subset_1(X0,X1))),
% 1.90/1.04    inference(ennf_transformation,[],[f3])).
% 1.90/1.04  
% 1.90/1.04  fof(f17,plain,(
% 1.90/1.04    ! [X0,X1] : (r2_hidden(X0,X1) | v1_xboole_0(X1) | ~m1_subset_1(X0,X1))),
% 1.90/1.04    inference(flattening,[],[f16])).
% 1.90/1.04  
% 1.90/1.04  fof(f48,plain,(
% 1.90/1.04    ( ! [X0,X1] : (r2_hidden(X0,X1) | v1_xboole_0(X1) | ~m1_subset_1(X0,X1)) )),
% 1.90/1.04    inference(cnf_transformation,[],[f17])).
% 1.90/1.04  
% 1.90/1.04  fof(f67,plain,(
% 1.90/1.04    ~v1_xboole_0(sK5)),
% 1.90/1.04    inference(cnf_transformation,[],[f43])).
% 1.90/1.04  
% 1.90/1.04  cnf(c_16,plain,
% 1.90/1.04      ( v1_subset_1(X0,X1)
% 1.90/1.04      | ~ m1_subset_1(X0,k1_zfmisc_1(X1))
% 1.90/1.04      | X0 = X1 ),
% 1.90/1.04      inference(cnf_transformation,[],[f61]) ).
% 1.90/1.04  
% 1.90/1.04  cnf(c_18,negated_conjecture,
% 1.90/1.04      ( ~ v1_subset_1(sK5,u1_struct_0(sK4))
% 1.90/1.04      | r2_hidden(k3_yellow_0(sK4),sK5) ),
% 1.90/1.04      inference(cnf_transformation,[],[f71]) ).
% 1.90/1.04  
% 1.90/1.04  cnf(c_209,plain,
% 1.90/1.04      ( ~ v1_subset_1(sK5,u1_struct_0(sK4))
% 1.90/1.04      | r2_hidden(k3_yellow_0(sK4),sK5) ),
% 1.90/1.04      inference(prop_impl,[status(thm)],[c_18]) ).
% 1.90/1.04  
% 1.90/1.04  cnf(c_473,plain,
% 1.90/1.04      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
% 1.90/1.04      | r2_hidden(k3_yellow_0(sK4),sK5)
% 1.90/1.04      | X1 = X0
% 1.90/1.04      | u1_struct_0(sK4) != X1
% 1.90/1.04      | sK5 != X0 ),
% 1.90/1.04      inference(resolution_lifted,[status(thm)],[c_16,c_209]) ).
% 1.90/1.04  
% 1.90/1.04  cnf(c_474,plain,
% 1.90/1.04      ( ~ m1_subset_1(sK5,k1_zfmisc_1(u1_struct_0(sK4)))
% 1.90/1.04      | r2_hidden(k3_yellow_0(sK4),sK5)
% 1.90/1.04      | u1_struct_0(sK4) = sK5 ),
% 1.90/1.04      inference(unflattening,[status(thm)],[c_473]) ).
% 1.90/1.04  
% 1.90/1.04  cnf(c_20,negated_conjecture,
% 1.90/1.04      ( m1_subset_1(sK5,k1_zfmisc_1(u1_struct_0(sK4))) ),
% 1.90/1.04      inference(cnf_transformation,[],[f69]) ).
% 1.90/1.04  
% 1.90/1.04  cnf(c_476,plain,
% 1.90/1.04      ( r2_hidden(k3_yellow_0(sK4),sK5) | u1_struct_0(sK4) = sK5 ),
% 1.90/1.04      inference(global_propositional_subsumption,
% 1.90/1.04                [status(thm)],
% 1.90/1.04                [c_474,c_20]) ).
% 1.90/1.04  
% 1.90/1.04  cnf(c_1194,plain,
% 1.90/1.04      ( u1_struct_0(sK4) = sK5
% 1.90/1.04      | r2_hidden(k3_yellow_0(sK4),sK5) = iProver_top ),
% 1.90/1.04      inference(predicate_to_equality,[status(thm)],[c_476]) ).
% 1.90/1.04  
% 1.90/1.04  cnf(c_1200,plain,
% 1.90/1.04      ( m1_subset_1(sK5,k1_zfmisc_1(u1_struct_0(sK4))) = iProver_top ),
% 1.90/1.04      inference(predicate_to_equality,[status(thm)],[c_20]) ).
% 1.90/1.04  
% 1.90/1.04  cnf(c_15,plain,
% 1.90/1.04      ( ~ r1_orders_2(X0,X1,X2)
% 1.90/1.04      | ~ v13_waybel_0(X3,X0)
% 1.90/1.04      | ~ m1_subset_1(X2,u1_struct_0(X0))
% 1.90/1.04      | ~ m1_subset_1(X1,u1_struct_0(X0))
% 1.90/1.04      | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))
% 1.90/1.04      | ~ r2_hidden(X1,X3)
% 1.90/1.04      | r2_hidden(X2,X3)
% 1.90/1.04      | ~ l1_orders_2(X0) ),
% 1.90/1.04      inference(cnf_transformation,[],[f54]) ).
% 1.90/1.04  
% 1.90/1.04  cnf(c_9,plain,
% 1.90/1.04      ( r1_orders_2(X0,k3_yellow_0(X0),X1)
% 1.90/1.04      | ~ m1_subset_1(X1,u1_struct_0(X0))
% 1.90/1.04      | ~ v1_yellow_0(X0)
% 1.90/1.04      | v2_struct_0(X0)
% 1.90/1.04      | ~ v5_orders_2(X0)
% 1.90/1.04      | ~ l1_orders_2(X0) ),
% 1.90/1.04      inference(cnf_transformation,[],[f53]) ).
% 1.90/1.04  
% 1.90/1.04  cnf(c_24,negated_conjecture,
% 1.90/1.04      ( v1_yellow_0(sK4) ),
% 1.90/1.04      inference(cnf_transformation,[],[f65]) ).
% 1.90/1.04  
% 1.90/1.04  cnf(c_386,plain,
% 1.90/1.04      ( r1_orders_2(X0,k3_yellow_0(X0),X1)
% 1.90/1.04      | ~ m1_subset_1(X1,u1_struct_0(X0))
% 1.90/1.04      | v2_struct_0(X0)
% 1.90/1.04      | ~ v5_orders_2(X0)
% 1.90/1.04      | ~ l1_orders_2(X0)
% 1.90/1.04      | sK4 != X0 ),
% 1.90/1.04      inference(resolution_lifted,[status(thm)],[c_9,c_24]) ).
% 1.90/1.04  
% 1.90/1.04  cnf(c_387,plain,
% 1.90/1.04      ( r1_orders_2(sK4,k3_yellow_0(sK4),X0)
% 1.90/1.04      | ~ m1_subset_1(X0,u1_struct_0(sK4))
% 1.90/1.04      | v2_struct_0(sK4)
% 1.90/1.04      | ~ v5_orders_2(sK4)
% 1.90/1.04      | ~ l1_orders_2(sK4) ),
% 1.90/1.04      inference(unflattening,[status(thm)],[c_386]) ).
% 1.90/1.04  
% 1.90/1.04  cnf(c_27,negated_conjecture,
% 1.90/1.04      ( ~ v2_struct_0(sK4) ),
% 1.90/1.04      inference(cnf_transformation,[],[f62]) ).
% 1.90/1.04  
% 1.90/1.04  cnf(c_25,negated_conjecture,
% 1.90/1.04      ( v5_orders_2(sK4) ),
% 1.90/1.04      inference(cnf_transformation,[],[f64]) ).
% 1.90/1.04  
% 1.90/1.04  cnf(c_23,negated_conjecture,
% 1.90/1.04      ( l1_orders_2(sK4) ),
% 1.90/1.04      inference(cnf_transformation,[],[f66]) ).
% 1.90/1.04  
% 1.90/1.04  cnf(c_391,plain,
% 1.90/1.04      ( ~ m1_subset_1(X0,u1_struct_0(sK4))
% 1.90/1.04      | r1_orders_2(sK4,k3_yellow_0(sK4),X0) ),
% 1.90/1.04      inference(global_propositional_subsumption,
% 1.90/1.04                [status(thm)],
% 1.90/1.04                [c_387,c_27,c_25,c_23]) ).
% 1.90/1.04  
% 1.90/1.04  cnf(c_392,plain,
% 1.90/1.04      ( r1_orders_2(sK4,k3_yellow_0(sK4),X0)
% 1.90/1.04      | ~ m1_subset_1(X0,u1_struct_0(sK4)) ),
% 1.90/1.04      inference(renaming,[status(thm)],[c_391]) ).
% 1.90/1.04  
% 1.90/1.04  cnf(c_541,plain,
% 1.90/1.04      ( ~ v13_waybel_0(X0,X1)
% 1.90/1.04      | ~ m1_subset_1(X2,u1_struct_0(X1))
% 1.90/1.04      | ~ m1_subset_1(X3,u1_struct_0(X1))
% 1.90/1.04      | ~ m1_subset_1(X4,u1_struct_0(sK4))
% 1.90/1.04      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 1.90/1.04      | ~ r2_hidden(X2,X0)
% 1.90/1.04      | r2_hidden(X3,X0)
% 1.90/1.04      | ~ l1_orders_2(X1)
% 1.90/1.04      | X4 != X3
% 1.90/1.04      | k3_yellow_0(sK4) != X2
% 1.90/1.04      | sK4 != X1 ),
% 1.90/1.04      inference(resolution_lifted,[status(thm)],[c_15,c_392]) ).
% 1.90/1.04  
% 1.90/1.04  cnf(c_542,plain,
% 1.90/1.04      ( ~ v13_waybel_0(X0,sK4)
% 1.90/1.04      | ~ m1_subset_1(X1,u1_struct_0(sK4))
% 1.90/1.04      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK4)))
% 1.90/1.04      | ~ m1_subset_1(k3_yellow_0(sK4),u1_struct_0(sK4))
% 1.90/1.04      | r2_hidden(X1,X0)
% 1.90/1.04      | ~ r2_hidden(k3_yellow_0(sK4),X0)
% 1.90/1.04      | ~ l1_orders_2(sK4) ),
% 1.90/1.04      inference(unflattening,[status(thm)],[c_541]) ).
% 1.90/1.04  
% 1.90/1.04  cnf(c_6,plain,
% 1.90/1.04      ( m1_subset_1(k3_yellow_0(X0),u1_struct_0(X0))
% 1.90/1.04      | ~ l1_orders_2(X0) ),
% 1.90/1.04      inference(cnf_transformation,[],[f50]) ).
% 1.90/1.04  
% 1.90/1.04  cnf(c_70,plain,
% 1.90/1.04      ( m1_subset_1(k3_yellow_0(sK4),u1_struct_0(sK4))
% 1.90/1.04      | ~ l1_orders_2(sK4) ),
% 1.90/1.04      inference(instantiation,[status(thm)],[c_6]) ).
% 1.90/1.04  
% 1.90/1.04  cnf(c_546,plain,
% 1.90/1.04      ( ~ r2_hidden(k3_yellow_0(sK4),X0)
% 1.90/1.04      | r2_hidden(X1,X0)
% 1.90/1.04      | ~ v13_waybel_0(X0,sK4)
% 1.90/1.04      | ~ m1_subset_1(X1,u1_struct_0(sK4))
% 1.90/1.04      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK4))) ),
% 1.90/1.04      inference(global_propositional_subsumption,
% 1.90/1.04                [status(thm)],
% 1.90/1.04                [c_542,c_23,c_70]) ).
% 1.90/1.04  
% 1.90/1.04  cnf(c_547,plain,
% 1.90/1.04      ( ~ v13_waybel_0(X0,sK4)
% 1.90/1.04      | ~ m1_subset_1(X1,u1_struct_0(sK4))
% 1.90/1.04      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK4)))
% 1.90/1.04      | r2_hidden(X1,X0)
% 1.90/1.04      | ~ r2_hidden(k3_yellow_0(sK4),X0) ),
% 1.90/1.04      inference(renaming,[status(thm)],[c_546]) ).
% 1.90/1.04  
% 1.90/1.04  cnf(c_1192,plain,
% 1.90/1.04      ( v13_waybel_0(X0,sK4) != iProver_top
% 1.90/1.04      | m1_subset_1(X1,u1_struct_0(sK4)) != iProver_top
% 1.90/1.04      | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK4))) != iProver_top
% 1.90/1.04      | r2_hidden(X1,X0) = iProver_top
% 1.90/1.04      | r2_hidden(k3_yellow_0(sK4),X0) != iProver_top ),
% 1.90/1.04      inference(predicate_to_equality,[status(thm)],[c_547]) ).
% 1.90/1.04  
% 1.90/1.04  cnf(c_2325,plain,
% 1.90/1.04      ( v13_waybel_0(sK5,sK4) != iProver_top
% 1.90/1.04      | m1_subset_1(X0,u1_struct_0(sK4)) != iProver_top
% 1.90/1.04      | r2_hidden(X0,sK5) = iProver_top
% 1.90/1.04      | r2_hidden(k3_yellow_0(sK4),sK5) != iProver_top ),
% 1.90/1.04      inference(superposition,[status(thm)],[c_1200,c_1192]) ).
% 1.90/1.04  
% 1.90/1.04  cnf(c_21,negated_conjecture,
% 1.90/1.04      ( v13_waybel_0(sK5,sK4) ),
% 1.90/1.04      inference(cnf_transformation,[],[f68]) ).
% 1.90/1.04  
% 1.90/1.04  cnf(c_34,plain,
% 1.90/1.04      ( v13_waybel_0(sK5,sK4) = iProver_top ),
% 1.90/1.04      inference(predicate_to_equality,[status(thm)],[c_21]) ).
% 1.90/1.04  
% 1.90/1.04  cnf(c_2563,plain,
% 1.90/1.04      ( m1_subset_1(X0,u1_struct_0(sK4)) != iProver_top
% 1.90/1.04      | r2_hidden(X0,sK5) = iProver_top
% 1.90/1.04      | r2_hidden(k3_yellow_0(sK4),sK5) != iProver_top ),
% 1.90/1.04      inference(global_propositional_subsumption,
% 1.90/1.04                [status(thm)],
% 1.90/1.04                [c_2325,c_34]) ).
% 1.90/1.04  
% 1.90/1.04  cnf(c_3002,plain,
% 1.90/1.04      ( u1_struct_0(sK4) = sK5
% 1.90/1.04      | m1_subset_1(X0,u1_struct_0(sK4)) != iProver_top
% 1.90/1.04      | r2_hidden(X0,sK5) = iProver_top ),
% 1.90/1.04      inference(superposition,[status(thm)],[c_1194,c_2563]) ).
% 1.90/1.04  
% 1.90/1.04  cnf(c_17,plain,
% 1.90/1.04      ( ~ v1_subset_1(X0,X0) | ~ m1_subset_1(X0,k1_zfmisc_1(X0)) ),
% 1.90/1.04      inference(cnf_transformation,[],[f72]) ).
% 1.90/1.04  
% 1.90/1.04  cnf(c_19,negated_conjecture,
% 1.90/1.04      ( v1_subset_1(sK5,u1_struct_0(sK4))
% 1.90/1.04      | ~ r2_hidden(k3_yellow_0(sK4),sK5) ),
% 1.90/1.04      inference(cnf_transformation,[],[f70]) ).
% 1.90/1.04  
% 1.90/1.04  cnf(c_207,plain,
% 1.90/1.04      ( v1_subset_1(sK5,u1_struct_0(sK4))
% 1.90/1.04      | ~ r2_hidden(k3_yellow_0(sK4),sK5) ),
% 1.90/1.04      inference(prop_impl,[status(thm)],[c_19]) ).
% 1.90/1.04  
% 1.90/1.04  cnf(c_487,plain,
% 1.90/1.04      ( ~ m1_subset_1(X0,k1_zfmisc_1(X0))
% 1.90/1.04      | ~ r2_hidden(k3_yellow_0(sK4),sK5)
% 1.90/1.04      | u1_struct_0(sK4) != X0
% 1.90/1.04      | sK5 != X0 ),
% 1.90/1.04      inference(resolution_lifted,[status(thm)],[c_17,c_207]) ).
% 1.90/1.04  
% 1.90/1.04  cnf(c_488,plain,
% 1.90/1.04      ( ~ m1_subset_1(u1_struct_0(sK4),k1_zfmisc_1(u1_struct_0(sK4)))
% 1.90/1.04      | ~ r2_hidden(k3_yellow_0(sK4),sK5)
% 1.90/1.04      | sK5 != u1_struct_0(sK4) ),
% 1.90/1.04      inference(unflattening,[status(thm)],[c_487]) ).
% 1.90/1.04  
% 1.90/1.04  cnf(c_3,plain,
% 1.90/1.04      ( m1_subset_1(sK1(X0),k1_zfmisc_1(X0)) ),
% 1.90/1.04      inference(cnf_transformation,[],[f46]) ).
% 1.90/1.04  
% 1.90/1.04  cnf(c_1376,plain,
% 1.90/1.04      ( m1_subset_1(sK1(u1_struct_0(sK4)),k1_zfmisc_1(u1_struct_0(sK4))) ),
% 1.90/1.04      inference(instantiation,[status(thm)],[c_3]) ).
% 1.90/1.04  
% 1.90/1.04  cnf(c_0,plain,
% 1.90/1.04      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
% 1.90/1.04      | ~ r2_hidden(sK0(X1,X0),X0)
% 1.90/1.04      | X0 = X1 ),
% 1.90/1.04      inference(cnf_transformation,[],[f45]) ).
% 1.90/1.04  
% 1.90/1.04  cnf(c_1398,plain,
% 1.90/1.04      ( ~ m1_subset_1(sK5,k1_zfmisc_1(u1_struct_0(sK4)))
% 1.90/1.04      | ~ r2_hidden(sK0(u1_struct_0(sK4),sK5),sK5)
% 1.90/1.04      | sK5 = u1_struct_0(sK4) ),
% 1.90/1.04      inference(instantiation,[status(thm)],[c_0]) ).
% 1.90/1.04  
% 1.90/1.04  cnf(c_2,plain,
% 1.90/1.04      ( ~ v1_subset_1(sK1(X0),X0) ),
% 1.90/1.04      inference(cnf_transformation,[],[f47]) ).
% 1.90/1.04  
% 1.90/1.04  cnf(c_450,plain,
% 1.90/1.04      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
% 1.90/1.04      | X1 != X2
% 1.90/1.04      | X1 = X0
% 1.90/1.04      | sK1(X2) != X0 ),
% 1.90/1.04      inference(resolution_lifted,[status(thm)],[c_2,c_16]) ).
% 1.90/1.04  
% 1.90/1.04  cnf(c_451,plain,
% 1.90/1.04      ( ~ m1_subset_1(sK1(X0),k1_zfmisc_1(X0)) | X0 = sK1(X0) ),
% 1.90/1.04      inference(unflattening,[status(thm)],[c_450]) ).
% 1.90/1.04  
% 1.90/1.04  cnf(c_455,plain,
% 1.90/1.04      ( X0 = sK1(X0) ),
% 1.90/1.04      inference(global_propositional_subsumption,
% 1.90/1.04                [status(thm)],
% 1.90/1.04                [c_451,c_3]) ).
% 1.90/1.04  
% 1.90/1.04  cnf(c_1807,plain,
% 1.90/1.04      ( u1_struct_0(sK4) = sK1(u1_struct_0(sK4)) ),
% 1.90/1.04      inference(instantiation,[status(thm)],[c_455]) ).
% 1.90/1.04  
% 1.90/1.04  cnf(c_842,plain,( X0 = X0 ),theory(equality) ).
% 1.90/1.04  
% 1.90/1.04  cnf(c_1682,plain,
% 1.90/1.04      ( k1_zfmisc_1(X0) = k1_zfmisc_1(X0) ),
% 1.90/1.04      inference(instantiation,[status(thm)],[c_842]) ).
% 1.90/1.04  
% 1.90/1.04  cnf(c_2060,plain,
% 1.90/1.04      ( k1_zfmisc_1(u1_struct_0(sK4)) = k1_zfmisc_1(u1_struct_0(sK4)) ),
% 1.90/1.04      inference(instantiation,[status(thm)],[c_1682]) ).
% 1.90/1.04  
% 1.90/1.04  cnf(c_1,plain,
% 1.90/1.04      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
% 1.90/1.04      | m1_subset_1(sK0(X1,X0),X1)
% 1.90/1.04      | X0 = X1 ),
% 1.90/1.04      inference(cnf_transformation,[],[f44]) ).
% 1.90/1.04  
% 1.90/1.04  cnf(c_1202,plain,
% 1.90/1.04      ( X0 = X1
% 1.90/1.04      | m1_subset_1(X0,k1_zfmisc_1(X1)) != iProver_top
% 1.90/1.04      | m1_subset_1(sK0(X1,X0),X1) = iProver_top ),
% 1.90/1.04      inference(predicate_to_equality,[status(thm)],[c_1]) ).
% 1.90/1.04  
% 1.90/1.04  cnf(c_8,plain,
% 1.90/1.04      ( ~ m1_subset_1(X0,u1_struct_0(X1))
% 1.90/1.04      | v2_struct_0(X1)
% 1.90/1.04      | ~ v3_orders_2(X1)
% 1.90/1.04      | ~ v5_orders_2(X1)
% 1.90/1.04      | ~ l1_orders_2(X1)
% 1.90/1.04      | k1_yellow_0(X1,k6_domain_1(u1_struct_0(X1),X0)) = X0 ),
% 1.90/1.04      inference(cnf_transformation,[],[f51]) ).
% 1.90/1.04  
% 1.90/1.04  cnf(c_407,plain,
% 1.90/1.04      ( ~ m1_subset_1(X0,u1_struct_0(X1))
% 1.90/1.04      | v2_struct_0(X1)
% 1.90/1.04      | ~ v3_orders_2(X1)
% 1.90/1.04      | ~ l1_orders_2(X1)
% 1.90/1.04      | k1_yellow_0(X1,k6_domain_1(u1_struct_0(X1),X0)) = X0
% 1.90/1.04      | sK4 != X1 ),
% 1.90/1.04      inference(resolution_lifted,[status(thm)],[c_8,c_25]) ).
% 1.90/1.04  
% 1.90/1.04  cnf(c_408,plain,
% 1.90/1.04      ( ~ m1_subset_1(X0,u1_struct_0(sK4))
% 1.90/1.04      | v2_struct_0(sK4)
% 1.90/1.04      | ~ v3_orders_2(sK4)
% 1.90/1.04      | ~ l1_orders_2(sK4)
% 1.90/1.04      | k1_yellow_0(sK4,k6_domain_1(u1_struct_0(sK4),X0)) = X0 ),
% 1.90/1.04      inference(unflattening,[status(thm)],[c_407]) ).
% 1.90/1.04  
% 1.90/1.04  cnf(c_26,negated_conjecture,
% 1.90/1.04      ( v3_orders_2(sK4) ),
% 1.90/1.04      inference(cnf_transformation,[],[f63]) ).
% 1.90/1.04  
% 1.90/1.04  cnf(c_412,plain,
% 1.90/1.04      ( ~ m1_subset_1(X0,u1_struct_0(sK4))
% 1.90/1.04      | k1_yellow_0(sK4,k6_domain_1(u1_struct_0(sK4),X0)) = X0 ),
% 1.90/1.04      inference(global_propositional_subsumption,
% 1.90/1.04                [status(thm)],
% 1.90/1.04                [c_408,c_27,c_26,c_23]) ).
% 1.90/1.04  
% 1.90/1.04  cnf(c_1197,plain,
% 1.90/1.04      ( k1_yellow_0(sK4,k6_domain_1(u1_struct_0(sK4),X0)) = X0
% 1.90/1.04      | m1_subset_1(X0,u1_struct_0(sK4)) != iProver_top ),
% 1.90/1.04      inference(predicate_to_equality,[status(thm)],[c_412]) ).
% 1.90/1.04  
% 1.90/1.04  cnf(c_1592,plain,
% 1.90/1.04      ( k1_yellow_0(sK4,k6_domain_1(u1_struct_0(sK4),sK0(u1_struct_0(sK4),X0))) = sK0(u1_struct_0(sK4),X0)
% 1.90/1.04      | u1_struct_0(sK4) = X0
% 1.90/1.04      | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK4))) != iProver_top ),
% 1.90/1.04      inference(superposition,[status(thm)],[c_1202,c_1197]) ).
% 1.90/1.04  
% 1.90/1.04  cnf(c_2460,plain,
% 1.90/1.04      ( k1_yellow_0(sK4,k6_domain_1(u1_struct_0(sK4),sK0(u1_struct_0(sK4),sK5))) = sK0(u1_struct_0(sK4),sK5)
% 1.90/1.04      | u1_struct_0(sK4) = sK5 ),
% 1.90/1.04      inference(superposition,[status(thm)],[c_1200,c_1592]) ).
% 1.90/1.04  
% 1.90/1.04  cnf(c_5,plain,
% 1.90/1.04      ( m1_subset_1(k1_yellow_0(X0,X1),u1_struct_0(X0))
% 1.90/1.04      | ~ l1_orders_2(X0) ),
% 1.90/1.04      inference(cnf_transformation,[],[f49]) ).
% 1.90/1.04  
% 1.90/1.04  cnf(c_589,plain,
% 1.90/1.04      ( m1_subset_1(k1_yellow_0(X0,X1),u1_struct_0(X0)) | sK4 != X0 ),
% 1.90/1.04      inference(resolution_lifted,[status(thm)],[c_5,c_23]) ).
% 1.90/1.04  
% 1.90/1.04  cnf(c_590,plain,
% 1.90/1.04      ( m1_subset_1(k1_yellow_0(sK4,X0),u1_struct_0(sK4)) ),
% 1.90/1.04      inference(unflattening,[status(thm)],[c_589]) ).
% 1.90/1.04  
% 1.90/1.04  cnf(c_1190,plain,
% 1.90/1.04      ( m1_subset_1(k1_yellow_0(sK4,X0),u1_struct_0(sK4)) = iProver_top ),
% 1.90/1.04      inference(predicate_to_equality,[status(thm)],[c_590]) ).
% 1.90/1.04  
% 1.90/1.04  cnf(c_2479,plain,
% 1.90/1.04      ( u1_struct_0(sK4) = sK5
% 1.90/1.04      | m1_subset_1(sK0(u1_struct_0(sK4),sK5),u1_struct_0(sK4)) = iProver_top ),
% 1.90/1.04      inference(superposition,[status(thm)],[c_2460,c_1190]) ).
% 1.90/1.04  
% 1.90/1.04  cnf(c_2488,plain,
% 1.90/1.04      ( m1_subset_1(sK0(u1_struct_0(sK4),sK5),u1_struct_0(sK4))
% 1.90/1.04      | u1_struct_0(sK4) = sK5 ),
% 1.90/1.04      inference(predicate_to_equality_rev,[status(thm)],[c_2479]) ).
% 1.90/1.04  
% 1.90/1.04  cnf(c_1371,plain,
% 1.90/1.04      ( ~ v13_waybel_0(sK5,sK4)
% 1.90/1.04      | ~ m1_subset_1(X0,u1_struct_0(sK4))
% 1.90/1.04      | ~ m1_subset_1(sK5,k1_zfmisc_1(u1_struct_0(sK4)))
% 1.90/1.04      | r2_hidden(X0,sK5)
% 1.90/1.04      | ~ r2_hidden(k3_yellow_0(sK4),sK5) ),
% 1.90/1.04      inference(instantiation,[status(thm)],[c_547]) ).
% 1.90/1.04  
% 1.90/1.04  cnf(c_2884,plain,
% 1.90/1.04      ( ~ v13_waybel_0(sK5,sK4)
% 1.90/1.04      | ~ m1_subset_1(sK0(u1_struct_0(sK4),sK5),u1_struct_0(sK4))
% 1.90/1.04      | ~ m1_subset_1(sK5,k1_zfmisc_1(u1_struct_0(sK4)))
% 1.90/1.04      | r2_hidden(sK0(u1_struct_0(sK4),sK5),sK5)
% 1.90/1.04      | ~ r2_hidden(k3_yellow_0(sK4),sK5) ),
% 1.90/1.04      inference(instantiation,[status(thm)],[c_1371]) ).
% 1.90/1.04  
% 1.90/1.04  cnf(c_846,plain,
% 1.90/1.04      ( ~ m1_subset_1(X0,X1) | m1_subset_1(X2,X3) | X2 != X0 | X3 != X1 ),
% 1.90/1.04      theory(equality) ).
% 1.90/1.04  
% 1.90/1.04  cnf(c_1412,plain,
% 1.90/1.04      ( m1_subset_1(X0,X1)
% 1.90/1.04      | ~ m1_subset_1(sK1(X2),k1_zfmisc_1(X2))
% 1.90/1.04      | X0 != sK1(X2)
% 1.90/1.04      | X1 != k1_zfmisc_1(X2) ),
% 1.90/1.04      inference(instantiation,[status(thm)],[c_846]) ).
% 1.90/1.04  
% 1.90/1.04  cnf(c_1681,plain,
% 1.90/1.04      ( m1_subset_1(X0,k1_zfmisc_1(X1))
% 1.90/1.04      | ~ m1_subset_1(sK1(X1),k1_zfmisc_1(X1))
% 1.90/1.04      | X0 != sK1(X1)
% 1.90/1.04      | k1_zfmisc_1(X1) != k1_zfmisc_1(X1) ),
% 1.90/1.04      inference(instantiation,[status(thm)],[c_1412]) ).
% 1.90/1.04  
% 1.90/1.04  cnf(c_2604,plain,
% 1.90/1.04      ( m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK4)))
% 1.90/1.04      | ~ m1_subset_1(sK1(u1_struct_0(sK4)),k1_zfmisc_1(u1_struct_0(sK4)))
% 1.90/1.04      | X0 != sK1(u1_struct_0(sK4))
% 1.90/1.04      | k1_zfmisc_1(u1_struct_0(sK4)) != k1_zfmisc_1(u1_struct_0(sK4)) ),
% 1.90/1.04      inference(instantiation,[status(thm)],[c_1681]) ).
% 1.90/1.04  
% 1.90/1.04  cnf(c_3045,plain,
% 1.90/1.04      ( m1_subset_1(u1_struct_0(sK4),k1_zfmisc_1(u1_struct_0(sK4)))
% 1.90/1.04      | ~ m1_subset_1(sK1(u1_struct_0(sK4)),k1_zfmisc_1(u1_struct_0(sK4)))
% 1.90/1.04      | u1_struct_0(sK4) != sK1(u1_struct_0(sK4))
% 1.90/1.04      | k1_zfmisc_1(u1_struct_0(sK4)) != k1_zfmisc_1(u1_struct_0(sK4)) ),
% 1.90/1.04      inference(instantiation,[status(thm)],[c_2604]) ).
% 1.90/1.04  
% 1.90/1.04  cnf(c_3218,plain,
% 1.90/1.04      ( u1_struct_0(sK4) = sK5 ),
% 1.90/1.04      inference(global_propositional_subsumption,
% 1.90/1.04                [status(thm)],
% 1.90/1.04                [c_3002,c_21,c_20,c_476,c_488,c_1376,c_1398,c_1807,
% 1.90/1.04                 c_2060,c_2488,c_2884,c_3045]) ).
% 1.90/1.04  
% 1.90/1.04  cnf(c_582,plain,
% 1.90/1.04      ( m1_subset_1(k3_yellow_0(X0),u1_struct_0(X0)) | sK4 != X0 ),
% 1.90/1.04      inference(resolution_lifted,[status(thm)],[c_6,c_23]) ).
% 1.90/1.04  
% 1.90/1.04  cnf(c_583,plain,
% 1.90/1.04      ( m1_subset_1(k3_yellow_0(sK4),u1_struct_0(sK4)) ),
% 1.90/1.04      inference(unflattening,[status(thm)],[c_582]) ).
% 1.90/1.04  
% 1.90/1.04  cnf(c_1191,plain,
% 1.90/1.04      ( m1_subset_1(k3_yellow_0(sK4),u1_struct_0(sK4)) = iProver_top ),
% 1.90/1.04      inference(predicate_to_equality,[status(thm)],[c_583]) ).
% 1.90/1.04  
% 1.90/1.04  cnf(c_3249,plain,
% 1.90/1.04      ( m1_subset_1(k3_yellow_0(sK4),sK5) = iProver_top ),
% 1.90/1.04      inference(demodulation,[status(thm)],[c_3218,c_1191]) ).
% 1.90/1.04  
% 1.90/1.04  cnf(c_4,plain,
% 1.90/1.04      ( ~ m1_subset_1(X0,X1) | r2_hidden(X0,X1) | v1_xboole_0(X1) ),
% 1.90/1.04      inference(cnf_transformation,[],[f48]) ).
% 1.90/1.04  
% 1.90/1.04  cnf(c_22,negated_conjecture,
% 1.90/1.04      ( ~ v1_xboole_0(sK5) ),
% 1.90/1.04      inference(cnf_transformation,[],[f67]) ).
% 1.90/1.04  
% 1.90/1.04  cnf(c_371,plain,
% 1.90/1.04      ( ~ m1_subset_1(X0,X1) | r2_hidden(X0,X1) | sK5 != X1 ),
% 1.90/1.04      inference(resolution_lifted,[status(thm)],[c_4,c_22]) ).
% 1.90/1.04  
% 1.90/1.04  cnf(c_372,plain,
% 1.90/1.04      ( ~ m1_subset_1(X0,sK5) | r2_hidden(X0,sK5) ),
% 1.90/1.04      inference(unflattening,[status(thm)],[c_371]) ).
% 1.90/1.04  
% 1.90/1.04  cnf(c_1198,plain,
% 1.90/1.04      ( m1_subset_1(X0,sK5) != iProver_top
% 1.90/1.04      | r2_hidden(X0,sK5) = iProver_top ),
% 1.90/1.04      inference(predicate_to_equality,[status(thm)],[c_372]) ).
% 1.90/1.04  
% 1.90/1.04  cnf(c_3430,plain,
% 1.90/1.04      ( r2_hidden(k3_yellow_0(sK4),sK5) = iProver_top ),
% 1.90/1.04      inference(superposition,[status(thm)],[c_3249,c_1198]) ).
% 1.90/1.04  
% 1.90/1.04  cnf(c_461,plain,
% 1.90/1.04      ( ~ r2_hidden(k3_yellow_0(sK4),sK5)
% 1.90/1.04      | u1_struct_0(sK4) != X0
% 1.90/1.04      | sK1(X0) != sK5 ),
% 1.90/1.04      inference(resolution_lifted,[status(thm)],[c_2,c_207]) ).
% 1.90/1.04  
% 1.90/1.04  cnf(c_462,plain,
% 1.90/1.04      ( ~ r2_hidden(k3_yellow_0(sK4),sK5)
% 1.90/1.04      | sK1(u1_struct_0(sK4)) != sK5 ),
% 1.90/1.04      inference(unflattening,[status(thm)],[c_461]) ).
% 1.90/1.04  
% 1.90/1.04  cnf(c_1195,plain,
% 1.90/1.04      ( sK1(u1_struct_0(sK4)) != sK5
% 1.90/1.04      | r2_hidden(k3_yellow_0(sK4),sK5) != iProver_top ),
% 1.90/1.04      inference(predicate_to_equality,[status(thm)],[c_462]) ).
% 1.90/1.04  
% 1.90/1.04  cnf(c_1225,plain,
% 1.90/1.04      ( u1_struct_0(sK4) != sK5
% 1.90/1.04      | r2_hidden(k3_yellow_0(sK4),sK5) != iProver_top ),
% 1.90/1.04      inference(demodulation,[status(thm)],[c_1195,c_455]) ).
% 1.90/1.04  
% 1.90/1.04  cnf(contradiction,plain,
% 1.90/1.04      ( $false ),
% 1.90/1.04      inference(minisat,[status(thm)],[c_3430,c_3218,c_1225]) ).
% 1.90/1.04  
% 1.90/1.04  
% 1.90/1.04  % SZS output end CNFRefutation for theBenchmark.p
% 1.90/1.04  
% 1.90/1.04  ------                               Statistics
% 1.90/1.04  
% 1.90/1.04  ------ General
% 1.90/1.04  
% 1.90/1.04  abstr_ref_over_cycles:                  0
% 1.90/1.04  abstr_ref_under_cycles:                 0
% 1.90/1.04  gc_basic_clause_elim:                   0
% 1.90/1.04  forced_gc_time:                         0
% 1.90/1.04  parsing_time:                           0.01
% 1.90/1.04  unif_index_cands_time:                  0.
% 1.90/1.04  unif_index_add_time:                    0.
% 1.90/1.04  orderings_time:                         0.
% 1.90/1.04  out_proof_time:                         0.031
% 1.90/1.04  total_time:                             0.178
% 1.90/1.04  num_of_symbols:                         54
% 1.90/1.04  num_of_terms:                           2875
% 1.90/1.04  
% 1.90/1.04  ------ Preprocessing
% 1.90/1.04  
% 1.90/1.04  num_of_splits:                          0
% 1.90/1.04  num_of_split_atoms:                     0
% 1.90/1.04  num_of_reused_defs:                     0
% 1.90/1.04  num_eq_ax_congr_red:                    21
% 1.90/1.04  num_of_sem_filtered_clauses:            1
% 1.90/1.04  num_of_subtypes:                        0
% 1.90/1.04  monotx_restored_types:                  0
% 1.90/1.04  sat_num_of_epr_types:                   0
% 1.90/1.04  sat_num_of_non_cyclic_types:            0
% 1.90/1.04  sat_guarded_non_collapsed_types:        0
% 1.90/1.04  num_pure_diseq_elim:                    0
% 1.90/1.04  simp_replaced_by:                       0
% 1.90/1.04  res_preprocessed:                       117
% 1.90/1.04  prep_upred:                             0
% 1.90/1.04  prep_unflattend:                        25
% 1.90/1.04  smt_new_axioms:                         0
% 1.90/1.04  pred_elim_cands:                        3
% 1.90/1.04  pred_elim:                              8
% 1.90/1.04  pred_elim_cl:                           8
% 1.90/1.04  pred_elim_cycles:                       10
% 1.90/1.04  merged_defs:                            2
% 1.90/1.04  merged_defs_ncl:                        0
% 1.90/1.04  bin_hyper_res:                          2
% 1.90/1.04  prep_cycles:                            4
% 1.90/1.04  pred_elim_time:                         0.01
% 1.90/1.04  splitting_time:                         0.
% 1.90/1.04  sem_filter_time:                        0.
% 1.90/1.04  monotx_time:                            0.001
% 1.90/1.04  subtype_inf_time:                       0.
% 1.90/1.04  
% 1.90/1.04  ------ Problem properties
% 1.90/1.04  
% 1.90/1.04  clauses:                                20
% 1.90/1.04  conjectures:                            2
% 1.90/1.04  epr:                                    2
% 1.90/1.04  horn:                                   14
% 1.90/1.04  ground:                                 6
% 1.90/1.04  unary:                                  6
% 1.90/1.04  binary:                                 5
% 1.90/1.04  lits:                                   48
% 1.90/1.04  lits_eq:                                8
% 1.90/1.04  fd_pure:                                0
% 1.90/1.04  fd_pseudo:                              0
% 1.90/1.04  fd_cond:                                0
% 1.90/1.04  fd_pseudo_cond:                         2
% 1.90/1.04  ac_symbols:                             0
% 1.90/1.04  
% 1.90/1.04  ------ Propositional Solver
% 1.90/1.04  
% 1.90/1.04  prop_solver_calls:                      28
% 1.90/1.04  prop_fast_solver_calls:                 777
% 1.90/1.04  smt_solver_calls:                       0
% 1.90/1.04  smt_fast_solver_calls:                  0
% 1.90/1.04  prop_num_of_clauses:                    1121
% 1.90/1.04  prop_preprocess_simplified:             4089
% 1.90/1.04  prop_fo_subsumed:                       17
% 1.90/1.04  prop_solver_time:                       0.
% 1.90/1.04  smt_solver_time:                        0.
% 1.90/1.04  smt_fast_solver_time:                   0.
% 1.90/1.04  prop_fast_solver_time:                  0.
% 1.90/1.04  prop_unsat_core_time:                   0.
% 1.90/1.04  
% 1.90/1.04  ------ QBF
% 1.90/1.04  
% 1.90/1.04  qbf_q_res:                              0
% 1.90/1.04  qbf_num_tautologies:                    0
% 1.90/1.04  qbf_prep_cycles:                        0
% 1.90/1.04  
% 1.90/1.04  ------ BMC1
% 1.90/1.04  
% 1.90/1.04  bmc1_current_bound:                     -1
% 1.90/1.04  bmc1_last_solved_bound:                 -1
% 1.90/1.04  bmc1_unsat_core_size:                   -1
% 1.90/1.04  bmc1_unsat_core_parents_size:           -1
% 1.90/1.04  bmc1_merge_next_fun:                    0
% 1.90/1.04  bmc1_unsat_core_clauses_time:           0.
% 1.90/1.04  
% 1.90/1.04  ------ Instantiation
% 1.90/1.04  
% 1.90/1.04  inst_num_of_clauses:                    329
% 1.90/1.04  inst_num_in_passive:                    141
% 1.90/1.04  inst_num_in_active:                     184
% 1.90/1.04  inst_num_in_unprocessed:                4
% 1.90/1.04  inst_num_of_loops:                      200
% 1.90/1.04  inst_num_of_learning_restarts:          0
% 1.90/1.04  inst_num_moves_active_passive:          13
% 1.90/1.04  inst_lit_activity:                      0
% 1.90/1.04  inst_lit_activity_moves:                0
% 1.90/1.04  inst_num_tautologies:                   0
% 1.90/1.04  inst_num_prop_implied:                  0
% 1.90/1.04  inst_num_existing_simplified:           0
% 1.90/1.04  inst_num_eq_res_simplified:             0
% 1.90/1.04  inst_num_child_elim:                    0
% 1.90/1.04  inst_num_of_dismatching_blockings:      51
% 1.90/1.04  inst_num_of_non_proper_insts:           304
% 1.90/1.04  inst_num_of_duplicates:                 0
% 1.90/1.04  inst_inst_num_from_inst_to_res:         0
% 1.90/1.04  inst_dismatching_checking_time:         0.
% 1.90/1.04  
% 1.90/1.04  ------ Resolution
% 1.90/1.04  
% 1.90/1.04  res_num_of_clauses:                     0
% 1.90/1.04  res_num_in_passive:                     0
% 1.90/1.04  res_num_in_active:                      0
% 1.90/1.04  res_num_of_loops:                       121
% 1.90/1.04  res_forward_subset_subsumed:            36
% 1.90/1.04  res_backward_subset_subsumed:           0
% 1.90/1.04  res_forward_subsumed:                   0
% 1.90/1.04  res_backward_subsumed:                  0
% 1.90/1.04  res_forward_subsumption_resolution:     2
% 1.90/1.04  res_backward_subsumption_resolution:    0
% 1.90/1.04  res_clause_to_clause_subsumption:       162
% 1.90/1.04  res_orphan_elimination:                 0
% 1.90/1.04  res_tautology_del:                      36
% 1.90/1.04  res_num_eq_res_simplified:              0
% 1.90/1.04  res_num_sel_changes:                    0
% 1.90/1.04  res_moves_from_active_to_pass:          0
% 1.90/1.04  
% 1.90/1.04  ------ Superposition
% 1.90/1.04  
% 1.90/1.04  sup_time_total:                         0.
% 1.90/1.04  sup_time_generating:                    0.
% 1.90/1.04  sup_time_sim_full:                      0.
% 1.90/1.04  sup_time_sim_immed:                     0.
% 1.90/1.04  
% 1.90/1.04  sup_num_of_clauses:                     44
% 1.90/1.04  sup_num_in_active:                      8
% 1.90/1.04  sup_num_in_passive:                     36
% 1.90/1.04  sup_num_of_loops:                       39
% 1.90/1.04  sup_fw_superposition:                   28
% 1.90/1.04  sup_bw_superposition:                   22
% 1.90/1.04  sup_immediate_simplified:               9
% 1.90/1.04  sup_given_eliminated:                   0
% 1.90/1.04  comparisons_done:                       0
% 1.90/1.04  comparisons_avoided:                    20
% 1.90/1.04  
% 1.90/1.04  ------ Simplifications
% 1.90/1.04  
% 1.90/1.04  
% 1.90/1.04  sim_fw_subset_subsumed:                 5
% 1.90/1.04  sim_bw_subset_subsumed:                 2
% 1.90/1.04  sim_fw_subsumed:                        2
% 1.90/1.04  sim_bw_subsumed:                        0
% 1.90/1.04  sim_fw_subsumption_res:                 1
% 1.90/1.04  sim_bw_subsumption_res:                 0
% 1.90/1.04  sim_tautology_del:                      0
% 1.90/1.04  sim_eq_tautology_del:                   8
% 1.90/1.04  sim_eq_res_simp:                        0
% 1.90/1.04  sim_fw_demodulated:                     1
% 1.90/1.04  sim_bw_demodulated:                     30
% 1.90/1.04  sim_light_normalised:                   3
% 1.90/1.04  sim_joinable_taut:                      0
% 1.90/1.04  sim_joinable_simp:                      0
% 1.90/1.04  sim_ac_normalised:                      0
% 1.90/1.04  sim_smt_subsumption:                    0
% 1.90/1.04  
%------------------------------------------------------------------------------
