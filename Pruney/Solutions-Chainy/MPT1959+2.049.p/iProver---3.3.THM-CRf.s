%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n018.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:28:34 EST 2020

% Result     : Theorem 2.44s
% Output     : CNFRefutation 2.44s
% Verified   : 
% Statistics : Number of formulae       :  145 ( 940 expanded)
%              Number of clauses        :   83 ( 270 expanded)
%              Number of leaves         :   20 ( 185 expanded)
%              Depth                    :   27
%              Number of atoms          :  572 (7068 expanded)
%              Number of equality atoms :  121 ( 384 expanded)
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

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

fof(f6,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,X1)
     => ( r2_hidden(X0,X1)
        | v1_xboole_0(X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

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

fof(f68,plain,(
    ~ v1_xboole_0(sK4) ),
    inference(cnf_transformation,[],[f45])).

fof(f11,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => ( v1_subset_1(X1,X0)
      <=> X0 != X1 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

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

fof(f67,plain,(
    l1_orders_2(sK3) ),
    inference(cnf_transformation,[],[f45])).

fof(f8,axiom,(
    ! [X0] :
      ( l1_orders_2(X0)
     => m1_subset_1(k3_yellow_0(X0),u1_struct_0(X0)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

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

fof(f4,axiom,(
    ! [X0] : ~ v1_subset_1(k2_subset_1(X0),X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f50,plain,(
    ! [X0] : ~ v1_subset_1(k2_subset_1(X0),X0) ),
    inference(cnf_transformation,[],[f4])).

fof(f71,plain,
    ( ~ r2_hidden(k3_yellow_0(sK3),sK4)
    | v1_subset_1(sK4,u1_struct_0(sK3)) ),
    inference(cnf_transformation,[],[f45])).

fof(f2,axiom,(
    ! [X0] : k2_subset_1(X0) = X0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f48,plain,(
    ! [X0] : k2_subset_1(X0) = X0 ),
    inference(cnf_transformation,[],[f2])).

fof(f47,plain,(
    ! [X0,X1] :
      ( X0 = X1
      | ~ r2_hidden(sK0(X0,X1),X1)
      | ~ r2_hidden(sK0(X0,X1),X0) ) ),
    inference(cnf_transformation,[],[f34])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => ! [X2] :
          ( r2_hidden(X2,X1)
         => r2_hidden(X2,X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f18,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( r2_hidden(X2,X0)
          | ~ r2_hidden(X2,X1) )
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f49,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(X2,X0)
      | ~ r2_hidden(X2,X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f18])).

cnf(c_1,plain,
    ( r2_hidden(sK0(X0,X1),X1)
    | r2_hidden(sK0(X0,X1),X0)
    | X1 = X0 ),
    inference(cnf_transformation,[],[f46])).

cnf(c_1120,plain,
    ( X0 = X1
    | r2_hidden(sK0(X1,X0),X0) = iProver_top
    | r2_hidden(sK0(X1,X0),X1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1])).

cnf(c_5,plain,
    ( m1_subset_1(X0,X1)
    | ~ r2_hidden(X0,X1) ),
    inference(cnf_transformation,[],[f51])).

cnf(c_1118,plain,
    ( m1_subset_1(X0,X1) = iProver_top
    | r2_hidden(X0,X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_5])).

cnf(c_1583,plain,
    ( X0 = X1
    | m1_subset_1(sK0(X0,X1),X0) = iProver_top
    | r2_hidden(sK0(X0,X1),X1) = iProver_top ),
    inference(superposition,[status(thm)],[c_1120,c_1118])).

cnf(c_2022,plain,
    ( X0 = X1
    | m1_subset_1(sK0(X1,X0),X1) = iProver_top
    | m1_subset_1(sK0(X1,X0),X0) = iProver_top ),
    inference(superposition,[status(thm)],[c_1583,c_1118])).

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

cnf(c_1114,plain,
    ( m1_subset_1(X0,sK4) != iProver_top
    | r2_hidden(X0,sK4) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_349])).

cnf(c_2292,plain,
    ( sK4 = X0
    | m1_subset_1(sK0(X0,sK4),X0) = iProver_top
    | r2_hidden(sK0(X0,sK4),sK4) = iProver_top ),
    inference(superposition,[status(thm)],[c_2022,c_1114])).

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

cnf(c_409,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | r2_hidden(k3_yellow_0(sK3),sK4)
    | X1 = X0
    | u1_struct_0(sK3) != X1
    | sK4 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_16,c_195])).

cnf(c_410,plain,
    ( ~ m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(sK3)))
    | r2_hidden(k3_yellow_0(sK3),sK4)
    | u1_struct_0(sK3) = sK4 ),
    inference(unflattening,[status(thm)],[c_409])).

cnf(c_20,negated_conjecture,
    ( m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(sK3))) ),
    inference(cnf_transformation,[],[f70])).

cnf(c_412,plain,
    ( r2_hidden(k3_yellow_0(sK3),sK4)
    | u1_struct_0(sK3) = sK4 ),
    inference(global_propositional_subsumption,[status(thm)],[c_410,c_20])).

cnf(c_1111,plain,
    ( u1_struct_0(sK3) = sK4
    | r2_hidden(k3_yellow_0(sK3),sK4) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_412])).

cnf(c_23,negated_conjecture,
    ( l1_orders_2(sK3) ),
    inference(cnf_transformation,[],[f67])).

cnf(c_30,plain,
    ( l1_orders_2(sK3) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_23])).

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

cnf(c_411,plain,
    ( u1_struct_0(sK3) = sK4
    | m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(sK3))) != iProver_top
    | r2_hidden(k3_yellow_0(sK3),sK4) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_410])).

cnf(c_772,plain,
    ( X0 != X1
    | k3_yellow_0(X0) = k3_yellow_0(X1) ),
    theory(equality)).

cnf(c_781,plain,
    ( k3_yellow_0(sK3) = k3_yellow_0(sK3)
    | sK3 != sK3 ),
    inference(instantiation,[status(thm)],[c_772])).

cnf(c_766,plain,
    ( X0 = X0 ),
    theory(equality)).

cnf(c_787,plain,
    ( sK3 = sK3 ),
    inference(instantiation,[status(thm)],[c_766])).

cnf(c_1385,plain,
    ( sK4 = sK4 ),
    inference(instantiation,[status(thm)],[c_766])).

cnf(c_771,plain,
    ( ~ m1_subset_1(X0,X1)
    | m1_subset_1(X2,X3)
    | X2 != X0
    | X3 != X1 ),
    theory(equality)).

cnf(c_1323,plain,
    ( m1_subset_1(X0,X1)
    | ~ m1_subset_1(k3_yellow_0(sK3),u1_struct_0(sK3))
    | X1 != u1_struct_0(sK3)
    | X0 != k3_yellow_0(sK3) ),
    inference(instantiation,[status(thm)],[c_771])).

cnf(c_1535,plain,
    ( m1_subset_1(k3_yellow_0(sK3),X0)
    | ~ m1_subset_1(k3_yellow_0(sK3),u1_struct_0(sK3))
    | X0 != u1_struct_0(sK3)
    | k3_yellow_0(sK3) != k3_yellow_0(sK3) ),
    inference(instantiation,[status(thm)],[c_1323])).

cnf(c_1872,plain,
    ( ~ m1_subset_1(k3_yellow_0(sK3),u1_struct_0(sK3))
    | m1_subset_1(k3_yellow_0(sK3),sK4)
    | k3_yellow_0(sK3) != k3_yellow_0(sK3)
    | sK4 != u1_struct_0(sK3) ),
    inference(instantiation,[status(thm)],[c_1535])).

cnf(c_1873,plain,
    ( k3_yellow_0(sK3) != k3_yellow_0(sK3)
    | sK4 != u1_struct_0(sK3)
    | m1_subset_1(k3_yellow_0(sK3),u1_struct_0(sK3)) != iProver_top
    | m1_subset_1(k3_yellow_0(sK3),sK4) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1872])).

cnf(c_2836,plain,
    ( ~ m1_subset_1(k3_yellow_0(X0),sK4)
    | r2_hidden(k3_yellow_0(X0),sK4) ),
    inference(instantiation,[status(thm)],[c_349])).

cnf(c_2839,plain,
    ( m1_subset_1(k3_yellow_0(X0),sK4) != iProver_top
    | r2_hidden(k3_yellow_0(X0),sK4) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2836])).

cnf(c_2841,plain,
    ( m1_subset_1(k3_yellow_0(sK3),sK4) != iProver_top
    | r2_hidden(k3_yellow_0(sK3),sK4) = iProver_top ),
    inference(instantiation,[status(thm)],[c_2839])).

cnf(c_767,plain,
    ( X0 != X1
    | X2 != X1
    | X2 = X0 ),
    theory(equality)).

cnf(c_1335,plain,
    ( u1_struct_0(sK3) != X0
    | sK4 != X0
    | sK4 = u1_struct_0(sK3) ),
    inference(instantiation,[status(thm)],[c_767])).

cnf(c_3047,plain,
    ( u1_struct_0(sK3) != sK4
    | sK4 = u1_struct_0(sK3)
    | sK4 != sK4 ),
    inference(instantiation,[status(thm)],[c_1335])).

cnf(c_3143,plain,
    ( r2_hidden(k3_yellow_0(sK3),sK4) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_1111,c_30,c_33,c_63,c_411,c_781,c_787,c_1385,c_1873,c_2841,c_3047])).

cnf(c_1116,plain,
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

cnf(c_479,plain,
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

cnf(c_480,plain,
    ( ~ v13_waybel_0(X0,sK3)
    | ~ m1_subset_1(X1,u1_struct_0(sK3))
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK3)))
    | ~ m1_subset_1(k3_yellow_0(sK3),u1_struct_0(sK3))
    | r2_hidden(X1,X0)
    | ~ r2_hidden(k3_yellow_0(sK3),X0)
    | ~ l1_orders_2(sK3) ),
    inference(unflattening,[status(thm)],[c_479])).

cnf(c_62,plain,
    ( m1_subset_1(k3_yellow_0(sK3),u1_struct_0(sK3))
    | ~ l1_orders_2(sK3) ),
    inference(instantiation,[status(thm)],[c_8])).

cnf(c_484,plain,
    ( ~ r2_hidden(k3_yellow_0(sK3),X0)
    | r2_hidden(X1,X0)
    | ~ v13_waybel_0(X0,sK3)
    | ~ m1_subset_1(X1,u1_struct_0(sK3))
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK3))) ),
    inference(global_propositional_subsumption,[status(thm)],[c_480,c_23,c_62])).

cnf(c_485,plain,
    ( ~ v13_waybel_0(X0,sK3)
    | ~ m1_subset_1(X1,u1_struct_0(sK3))
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK3)))
    | r2_hidden(X1,X0)
    | ~ r2_hidden(k3_yellow_0(sK3),X0) ),
    inference(renaming,[status(thm)],[c_484])).

cnf(c_1109,plain,
    ( v13_waybel_0(X0,sK3) != iProver_top
    | m1_subset_1(X1,u1_struct_0(sK3)) != iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK3))) != iProver_top
    | r2_hidden(X1,X0) = iProver_top
    | r2_hidden(k3_yellow_0(sK3),X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_485])).

cnf(c_1639,plain,
    ( v13_waybel_0(sK4,sK3) != iProver_top
    | m1_subset_1(X0,u1_struct_0(sK3)) != iProver_top
    | r2_hidden(X0,sK4) = iProver_top
    | r2_hidden(k3_yellow_0(sK3),sK4) != iProver_top ),
    inference(superposition,[status(thm)],[c_1116,c_1109])).

cnf(c_21,negated_conjecture,
    ( v13_waybel_0(sK4,sK3) ),
    inference(cnf_transformation,[],[f69])).

cnf(c_32,plain,
    ( v13_waybel_0(sK4,sK3) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_21])).

cnf(c_1644,plain,
    ( m1_subset_1(X0,u1_struct_0(sK3)) != iProver_top
    | r2_hidden(X0,sK4) = iProver_top
    | r2_hidden(k3_yellow_0(sK3),sK4) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_1639,c_32])).

cnf(c_3149,plain,
    ( m1_subset_1(X0,u1_struct_0(sK3)) != iProver_top
    | r2_hidden(X0,sK4) = iProver_top ),
    inference(superposition,[status(thm)],[c_3143,c_1644])).

cnf(c_3860,plain,
    ( u1_struct_0(sK3) = sK4
    | r2_hidden(sK0(u1_struct_0(sK3),sK4),sK4) = iProver_top ),
    inference(superposition,[status(thm)],[c_2292,c_3149])).

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

cnf(c_397,plain,
    ( ~ r2_hidden(k3_yellow_0(sK3),sK4)
    | u1_struct_0(sK3) != X0
    | k2_subset_1(X0) != sK4 ),
    inference(resolution_lifted,[status(thm)],[c_4,c_193])).

cnf(c_398,plain,
    ( ~ r2_hidden(k3_yellow_0(sK3),sK4)
    | k2_subset_1(u1_struct_0(sK3)) != sK4 ),
    inference(unflattening,[status(thm)],[c_397])).

cnf(c_1112,plain,
    ( k2_subset_1(u1_struct_0(sK3)) != sK4
    | r2_hidden(k3_yellow_0(sK3),sK4) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_398])).

cnf(c_2,plain,
    ( k2_subset_1(X0) = X0 ),
    inference(cnf_transformation,[],[f48])).

cnf(c_1144,plain,
    ( u1_struct_0(sK3) != sK4
    | r2_hidden(k3_yellow_0(sK3),sK4) != iProver_top ),
    inference(demodulation,[status(thm)],[c_1112,c_2])).

cnf(c_5281,plain,
    ( r2_hidden(sK0(u1_struct_0(sK3),sK4),sK4) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_3860,c_30,c_33,c_63,c_411,c_781,c_787,c_1144,c_1385,c_1873,c_2841,c_3047])).

cnf(c_0,plain,
    ( ~ r2_hidden(sK0(X0,X1),X1)
    | ~ r2_hidden(sK0(X0,X1),X0)
    | X1 = X0 ),
    inference(cnf_transformation,[],[f47])).

cnf(c_1121,plain,
    ( X0 = X1
    | r2_hidden(sK0(X1,X0),X0) != iProver_top
    | r2_hidden(sK0(X1,X0),X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_0])).

cnf(c_5287,plain,
    ( u1_struct_0(sK3) = sK4
    | r2_hidden(sK0(u1_struct_0(sK3),sK4),u1_struct_0(sK3)) != iProver_top ),
    inference(superposition,[status(thm)],[c_5281,c_1121])).

cnf(c_3,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | ~ r2_hidden(X2,X0)
    | r2_hidden(X2,X1) ),
    inference(cnf_transformation,[],[f49])).

cnf(c_1882,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | ~ r2_hidden(sK0(u1_struct_0(sK3),X0),X0)
    | r2_hidden(sK0(u1_struct_0(sK3),X0),X1) ),
    inference(instantiation,[status(thm)],[c_3])).

cnf(c_3416,plain,
    ( ~ m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(sK3)))
    | r2_hidden(sK0(u1_struct_0(sK3),sK4),u1_struct_0(sK3))
    | ~ r2_hidden(sK0(u1_struct_0(sK3),sK4),sK4) ),
    inference(instantiation,[status(thm)],[c_1882])).

cnf(c_3417,plain,
    ( m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(sK3))) != iProver_top
    | r2_hidden(sK0(u1_struct_0(sK3),sK4),u1_struct_0(sK3)) = iProver_top
    | r2_hidden(sK0(u1_struct_0(sK3),sK4),sK4) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3416])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_5287,c_3860,c_3417,c_3143,c_1144,c_33])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : iproveropt_run.sh %d %s
% 0.13/0.34  % Computer   : n018.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 13:52:12 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running in FOF mode
% 2.44/1.00  % SZS status Started for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.44/1.00  
% 2.44/1.00  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 2.44/1.00  
% 2.44/1.00  ------  iProver source info
% 2.44/1.00  
% 2.44/1.00  git: date: 2020-06-30 10:37:57 +0100
% 2.44/1.00  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 2.44/1.00  git: non_committed_changes: false
% 2.44/1.00  git: last_make_outside_of_git: false
% 2.44/1.00  
% 2.44/1.00  ------ 
% 2.44/1.00  
% 2.44/1.00  ------ Input Options
% 2.44/1.00  
% 2.44/1.00  --out_options                           all
% 2.44/1.00  --tptp_safe_out                         true
% 2.44/1.00  --problem_path                          ""
% 2.44/1.00  --include_path                          ""
% 2.44/1.00  --clausifier                            res/vclausify_rel
% 2.44/1.00  --clausifier_options                    --mode clausify
% 2.44/1.00  --stdin                                 false
% 2.44/1.00  --stats_out                             all
% 2.44/1.00  
% 2.44/1.00  ------ General Options
% 2.44/1.00  
% 2.44/1.00  --fof                                   false
% 2.44/1.00  --time_out_real                         305.
% 2.44/1.00  --time_out_virtual                      -1.
% 2.44/1.00  --symbol_type_check                     false
% 2.44/1.00  --clausify_out                          false
% 2.44/1.00  --sig_cnt_out                           false
% 2.44/1.00  --trig_cnt_out                          false
% 2.44/1.00  --trig_cnt_out_tolerance                1.
% 2.44/1.00  --trig_cnt_out_sk_spl                   false
% 2.44/1.00  --abstr_cl_out                          false
% 2.44/1.00  
% 2.44/1.00  ------ Global Options
% 2.44/1.00  
% 2.44/1.00  --schedule                              default
% 2.44/1.00  --add_important_lit                     false
% 2.44/1.00  --prop_solver_per_cl                    1000
% 2.44/1.00  --min_unsat_core                        false
% 2.44/1.00  --soft_assumptions                      false
% 2.44/1.00  --soft_lemma_size                       3
% 2.44/1.00  --prop_impl_unit_size                   0
% 2.44/1.00  --prop_impl_unit                        []
% 2.44/1.00  --share_sel_clauses                     true
% 2.44/1.00  --reset_solvers                         false
% 2.44/1.00  --bc_imp_inh                            [conj_cone]
% 2.44/1.00  --conj_cone_tolerance                   3.
% 2.44/1.00  --extra_neg_conj                        none
% 2.44/1.00  --large_theory_mode                     true
% 2.44/1.00  --prolific_symb_bound                   200
% 2.44/1.00  --lt_threshold                          2000
% 2.44/1.00  --clause_weak_htbl                      true
% 2.44/1.00  --gc_record_bc_elim                     false
% 2.44/1.00  
% 2.44/1.00  ------ Preprocessing Options
% 2.44/1.00  
% 2.44/1.00  --preprocessing_flag                    true
% 2.44/1.00  --time_out_prep_mult                    0.1
% 2.44/1.00  --splitting_mode                        input
% 2.44/1.00  --splitting_grd                         true
% 2.44/1.00  --splitting_cvd                         false
% 2.44/1.00  --splitting_cvd_svl                     false
% 2.44/1.00  --splitting_nvd                         32
% 2.44/1.00  --sub_typing                            true
% 2.44/1.00  --prep_gs_sim                           true
% 2.44/1.00  --prep_unflatten                        true
% 2.44/1.00  --prep_res_sim                          true
% 2.44/1.00  --prep_upred                            true
% 2.44/1.00  --prep_sem_filter                       exhaustive
% 2.44/1.00  --prep_sem_filter_out                   false
% 2.44/1.00  --pred_elim                             true
% 2.44/1.00  --res_sim_input                         true
% 2.44/1.00  --eq_ax_congr_red                       true
% 2.44/1.00  --pure_diseq_elim                       true
% 2.44/1.00  --brand_transform                       false
% 2.44/1.00  --non_eq_to_eq                          false
% 2.44/1.00  --prep_def_merge                        true
% 2.44/1.00  --prep_def_merge_prop_impl              false
% 2.44/1.00  --prep_def_merge_mbd                    true
% 2.44/1.00  --prep_def_merge_tr_red                 false
% 2.44/1.00  --prep_def_merge_tr_cl                  false
% 2.44/1.00  --smt_preprocessing                     true
% 2.44/1.00  --smt_ac_axioms                         fast
% 2.44/1.00  --preprocessed_out                      false
% 2.44/1.00  --preprocessed_stats                    false
% 2.44/1.00  
% 2.44/1.00  ------ Abstraction refinement Options
% 2.44/1.00  
% 2.44/1.00  --abstr_ref                             []
% 2.44/1.00  --abstr_ref_prep                        false
% 2.44/1.00  --abstr_ref_until_sat                   false
% 2.44/1.00  --abstr_ref_sig_restrict                funpre
% 2.44/1.00  --abstr_ref_af_restrict_to_split_sk     false
% 2.44/1.00  --abstr_ref_under                       []
% 2.44/1.00  
% 2.44/1.00  ------ SAT Options
% 2.44/1.00  
% 2.44/1.00  --sat_mode                              false
% 2.44/1.00  --sat_fm_restart_options                ""
% 2.44/1.00  --sat_gr_def                            false
% 2.44/1.00  --sat_epr_types                         true
% 2.44/1.00  --sat_non_cyclic_types                  false
% 2.44/1.00  --sat_finite_models                     false
% 2.44/1.00  --sat_fm_lemmas                         false
% 2.44/1.00  --sat_fm_prep                           false
% 2.44/1.00  --sat_fm_uc_incr                        true
% 2.44/1.00  --sat_out_model                         small
% 2.44/1.00  --sat_out_clauses                       false
% 2.44/1.00  
% 2.44/1.00  ------ QBF Options
% 2.44/1.00  
% 2.44/1.00  --qbf_mode                              false
% 2.44/1.00  --qbf_elim_univ                         false
% 2.44/1.00  --qbf_dom_inst                          none
% 2.44/1.00  --qbf_dom_pre_inst                      false
% 2.44/1.00  --qbf_sk_in                             false
% 2.44/1.00  --qbf_pred_elim                         true
% 2.44/1.00  --qbf_split                             512
% 2.44/1.00  
% 2.44/1.00  ------ BMC1 Options
% 2.44/1.00  
% 2.44/1.00  --bmc1_incremental                      false
% 2.44/1.00  --bmc1_axioms                           reachable_all
% 2.44/1.00  --bmc1_min_bound                        0
% 2.44/1.00  --bmc1_max_bound                        -1
% 2.44/1.00  --bmc1_max_bound_default                -1
% 2.44/1.00  --bmc1_symbol_reachability              true
% 2.44/1.00  --bmc1_property_lemmas                  false
% 2.44/1.00  --bmc1_k_induction                      false
% 2.44/1.00  --bmc1_non_equiv_states                 false
% 2.44/1.00  --bmc1_deadlock                         false
% 2.44/1.00  --bmc1_ucm                              false
% 2.44/1.00  --bmc1_add_unsat_core                   none
% 2.44/1.01  --bmc1_unsat_core_children              false
% 2.44/1.01  --bmc1_unsat_core_extrapolate_axioms    false
% 2.44/1.01  --bmc1_out_stat                         full
% 2.44/1.01  --bmc1_ground_init                      false
% 2.44/1.01  --bmc1_pre_inst_next_state              false
% 2.44/1.01  --bmc1_pre_inst_state                   false
% 2.44/1.01  --bmc1_pre_inst_reach_state             false
% 2.44/1.01  --bmc1_out_unsat_core                   false
% 2.44/1.01  --bmc1_aig_witness_out                  false
% 2.44/1.01  --bmc1_verbose                          false
% 2.44/1.01  --bmc1_dump_clauses_tptp                false
% 2.44/1.01  --bmc1_dump_unsat_core_tptp             false
% 2.44/1.01  --bmc1_dump_file                        -
% 2.44/1.01  --bmc1_ucm_expand_uc_limit              128
% 2.44/1.01  --bmc1_ucm_n_expand_iterations          6
% 2.44/1.01  --bmc1_ucm_extend_mode                  1
% 2.44/1.01  --bmc1_ucm_init_mode                    2
% 2.44/1.01  --bmc1_ucm_cone_mode                    none
% 2.44/1.01  --bmc1_ucm_reduced_relation_type        0
% 2.44/1.01  --bmc1_ucm_relax_model                  4
% 2.44/1.01  --bmc1_ucm_full_tr_after_sat            true
% 2.44/1.01  --bmc1_ucm_expand_neg_assumptions       false
% 2.44/1.01  --bmc1_ucm_layered_model                none
% 2.44/1.01  --bmc1_ucm_max_lemma_size               10
% 2.44/1.01  
% 2.44/1.01  ------ AIG Options
% 2.44/1.01  
% 2.44/1.01  --aig_mode                              false
% 2.44/1.01  
% 2.44/1.01  ------ Instantiation Options
% 2.44/1.01  
% 2.44/1.01  --instantiation_flag                    true
% 2.44/1.01  --inst_sos_flag                         false
% 2.44/1.01  --inst_sos_phase                        true
% 2.44/1.01  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 2.44/1.01  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 2.44/1.01  --inst_lit_sel_side                     num_symb
% 2.44/1.01  --inst_solver_per_active                1400
% 2.44/1.01  --inst_solver_calls_frac                1.
% 2.44/1.01  --inst_passive_queue_type               priority_queues
% 2.44/1.01  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 2.44/1.01  --inst_passive_queues_freq              [25;2]
% 2.44/1.01  --inst_dismatching                      true
% 2.44/1.01  --inst_eager_unprocessed_to_passive     true
% 2.44/1.01  --inst_prop_sim_given                   true
% 2.44/1.01  --inst_prop_sim_new                     false
% 2.44/1.01  --inst_subs_new                         false
% 2.44/1.01  --inst_eq_res_simp                      false
% 2.44/1.01  --inst_subs_given                       false
% 2.44/1.01  --inst_orphan_elimination               true
% 2.44/1.01  --inst_learning_loop_flag               true
% 2.44/1.01  --inst_learning_start                   3000
% 2.44/1.01  --inst_learning_factor                  2
% 2.44/1.01  --inst_start_prop_sim_after_learn       3
% 2.44/1.01  --inst_sel_renew                        solver
% 2.44/1.01  --inst_lit_activity_flag                true
% 2.44/1.01  --inst_restr_to_given                   false
% 2.44/1.01  --inst_activity_threshold               500
% 2.44/1.01  --inst_out_proof                        true
% 2.44/1.01  
% 2.44/1.01  ------ Resolution Options
% 2.44/1.01  
% 2.44/1.01  --resolution_flag                       true
% 2.44/1.01  --res_lit_sel                           adaptive
% 2.44/1.01  --res_lit_sel_side                      none
% 2.44/1.01  --res_ordering                          kbo
% 2.44/1.01  --res_to_prop_solver                    active
% 2.44/1.01  --res_prop_simpl_new                    false
% 2.44/1.01  --res_prop_simpl_given                  true
% 2.44/1.01  --res_passive_queue_type                priority_queues
% 2.44/1.01  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 2.44/1.01  --res_passive_queues_freq               [15;5]
% 2.44/1.01  --res_forward_subs                      full
% 2.44/1.01  --res_backward_subs                     full
% 2.44/1.01  --res_forward_subs_resolution           true
% 2.44/1.01  --res_backward_subs_resolution          true
% 2.44/1.01  --res_orphan_elimination                true
% 2.44/1.01  --res_time_limit                        2.
% 2.44/1.01  --res_out_proof                         true
% 2.44/1.01  
% 2.44/1.01  ------ Superposition Options
% 2.44/1.01  
% 2.44/1.01  --superposition_flag                    true
% 2.44/1.01  --sup_passive_queue_type                priority_queues
% 2.44/1.01  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 2.44/1.01  --sup_passive_queues_freq               [8;1;4]
% 2.44/1.01  --demod_completeness_check              fast
% 2.44/1.01  --demod_use_ground                      true
% 2.44/1.01  --sup_to_prop_solver                    passive
% 2.44/1.01  --sup_prop_simpl_new                    true
% 2.44/1.01  --sup_prop_simpl_given                  true
% 2.44/1.01  --sup_fun_splitting                     false
% 2.44/1.01  --sup_smt_interval                      50000
% 2.44/1.01  
% 2.44/1.01  ------ Superposition Simplification Setup
% 2.44/1.01  
% 2.44/1.01  --sup_indices_passive                   []
% 2.44/1.01  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.44/1.01  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.44/1.01  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.44/1.01  --sup_full_triv                         [TrivRules;PropSubs]
% 2.44/1.01  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.44/1.01  --sup_full_bw                           [BwDemod]
% 2.44/1.01  --sup_immed_triv                        [TrivRules]
% 2.44/1.01  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 2.44/1.01  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.44/1.01  --sup_immed_bw_main                     []
% 2.44/1.01  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.44/1.01  --sup_input_triv                        [Unflattening;TrivRules]
% 2.44/1.01  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.44/1.01  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.44/1.01  
% 2.44/1.01  ------ Combination Options
% 2.44/1.01  
% 2.44/1.01  --comb_res_mult                         3
% 2.44/1.01  --comb_sup_mult                         2
% 2.44/1.01  --comb_inst_mult                        10
% 2.44/1.01  
% 2.44/1.01  ------ Debug Options
% 2.44/1.01  
% 2.44/1.01  --dbg_backtrace                         false
% 2.44/1.01  --dbg_dump_prop_clauses                 false
% 2.44/1.01  --dbg_dump_prop_clauses_file            -
% 2.44/1.01  --dbg_out_stat                          false
% 2.44/1.01  ------ Parsing...
% 2.44/1.01  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 2.44/1.01  
% 2.44/1.01  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe:1:0s pe:2:0s pe:4:0s pe_e  sf_s  rm: 8 0s  sf_e  pe_s  pe_e 
% 2.44/1.01  
% 2.44/1.01  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 2.44/1.01  
% 2.44/1.01  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 2.44/1.01  ------ Proving...
% 2.44/1.01  ------ Problem Properties 
% 2.44/1.01  
% 2.44/1.01  
% 2.44/1.01  clauses                                 20
% 2.44/1.01  conjectures                             2
% 2.44/1.01  EPR                                     3
% 2.44/1.01  Horn                                    14
% 2.44/1.01  unary                                   4
% 2.44/1.01  binary                                  5
% 2.44/1.01  lits                                    52
% 2.44/1.01  lits eq                                 7
% 2.44/1.01  fd_pure                                 0
% 2.44/1.01  fd_pseudo                               0
% 2.44/1.01  fd_cond                                 0
% 2.44/1.01  fd_pseudo_cond                          2
% 2.44/1.01  AC symbols                              0
% 2.44/1.01  
% 2.44/1.01  ------ Schedule dynamic 5 is on 
% 2.44/1.01  
% 2.44/1.01  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" Time Limit: 10.
% 2.44/1.01  
% 2.44/1.01  
% 2.44/1.01  ------ 
% 2.44/1.01  Current options:
% 2.44/1.01  ------ 
% 2.44/1.01  
% 2.44/1.01  ------ Input Options
% 2.44/1.01  
% 2.44/1.01  --out_options                           all
% 2.44/1.01  --tptp_safe_out                         true
% 2.44/1.01  --problem_path                          ""
% 2.44/1.01  --include_path                          ""
% 2.44/1.01  --clausifier                            res/vclausify_rel
% 2.44/1.01  --clausifier_options                    --mode clausify
% 2.44/1.01  --stdin                                 false
% 2.44/1.01  --stats_out                             all
% 2.44/1.01  
% 2.44/1.01  ------ General Options
% 2.44/1.01  
% 2.44/1.01  --fof                                   false
% 2.44/1.01  --time_out_real                         305.
% 2.44/1.01  --time_out_virtual                      -1.
% 2.44/1.01  --symbol_type_check                     false
% 2.44/1.01  --clausify_out                          false
% 2.44/1.01  --sig_cnt_out                           false
% 2.44/1.01  --trig_cnt_out                          false
% 2.44/1.01  --trig_cnt_out_tolerance                1.
% 2.44/1.01  --trig_cnt_out_sk_spl                   false
% 2.44/1.01  --abstr_cl_out                          false
% 2.44/1.01  
% 2.44/1.01  ------ Global Options
% 2.44/1.01  
% 2.44/1.01  --schedule                              default
% 2.44/1.01  --add_important_lit                     false
% 2.44/1.01  --prop_solver_per_cl                    1000
% 2.44/1.01  --min_unsat_core                        false
% 2.44/1.01  --soft_assumptions                      false
% 2.44/1.01  --soft_lemma_size                       3
% 2.44/1.01  --prop_impl_unit_size                   0
% 2.44/1.01  --prop_impl_unit                        []
% 2.44/1.01  --share_sel_clauses                     true
% 2.44/1.01  --reset_solvers                         false
% 2.44/1.01  --bc_imp_inh                            [conj_cone]
% 2.44/1.01  --conj_cone_tolerance                   3.
% 2.44/1.01  --extra_neg_conj                        none
% 2.44/1.01  --large_theory_mode                     true
% 2.44/1.01  --prolific_symb_bound                   200
% 2.44/1.01  --lt_threshold                          2000
% 2.44/1.01  --clause_weak_htbl                      true
% 2.44/1.01  --gc_record_bc_elim                     false
% 2.44/1.01  
% 2.44/1.01  ------ Preprocessing Options
% 2.44/1.01  
% 2.44/1.01  --preprocessing_flag                    true
% 2.44/1.01  --time_out_prep_mult                    0.1
% 2.44/1.01  --splitting_mode                        input
% 2.44/1.01  --splitting_grd                         true
% 2.44/1.01  --splitting_cvd                         false
% 2.44/1.01  --splitting_cvd_svl                     false
% 2.44/1.01  --splitting_nvd                         32
% 2.44/1.01  --sub_typing                            true
% 2.44/1.01  --prep_gs_sim                           true
% 2.44/1.01  --prep_unflatten                        true
% 2.44/1.01  --prep_res_sim                          true
% 2.44/1.01  --prep_upred                            true
% 2.44/1.01  --prep_sem_filter                       exhaustive
% 2.44/1.01  --prep_sem_filter_out                   false
% 2.44/1.01  --pred_elim                             true
% 2.44/1.01  --res_sim_input                         true
% 2.44/1.01  --eq_ax_congr_red                       true
% 2.44/1.01  --pure_diseq_elim                       true
% 2.44/1.01  --brand_transform                       false
% 2.44/1.01  --non_eq_to_eq                          false
% 2.44/1.01  --prep_def_merge                        true
% 2.44/1.01  --prep_def_merge_prop_impl              false
% 2.44/1.01  --prep_def_merge_mbd                    true
% 2.44/1.01  --prep_def_merge_tr_red                 false
% 2.44/1.01  --prep_def_merge_tr_cl                  false
% 2.44/1.01  --smt_preprocessing                     true
% 2.44/1.01  --smt_ac_axioms                         fast
% 2.44/1.01  --preprocessed_out                      false
% 2.44/1.01  --preprocessed_stats                    false
% 2.44/1.01  
% 2.44/1.01  ------ Abstraction refinement Options
% 2.44/1.01  
% 2.44/1.01  --abstr_ref                             []
% 2.44/1.01  --abstr_ref_prep                        false
% 2.44/1.01  --abstr_ref_until_sat                   false
% 2.44/1.01  --abstr_ref_sig_restrict                funpre
% 2.44/1.01  --abstr_ref_af_restrict_to_split_sk     false
% 2.44/1.01  --abstr_ref_under                       []
% 2.44/1.01  
% 2.44/1.01  ------ SAT Options
% 2.44/1.01  
% 2.44/1.01  --sat_mode                              false
% 2.44/1.01  --sat_fm_restart_options                ""
% 2.44/1.01  --sat_gr_def                            false
% 2.44/1.01  --sat_epr_types                         true
% 2.44/1.01  --sat_non_cyclic_types                  false
% 2.44/1.01  --sat_finite_models                     false
% 2.44/1.01  --sat_fm_lemmas                         false
% 2.44/1.01  --sat_fm_prep                           false
% 2.44/1.01  --sat_fm_uc_incr                        true
% 2.44/1.01  --sat_out_model                         small
% 2.44/1.01  --sat_out_clauses                       false
% 2.44/1.01  
% 2.44/1.01  ------ QBF Options
% 2.44/1.01  
% 2.44/1.01  --qbf_mode                              false
% 2.44/1.01  --qbf_elim_univ                         false
% 2.44/1.01  --qbf_dom_inst                          none
% 2.44/1.01  --qbf_dom_pre_inst                      false
% 2.44/1.01  --qbf_sk_in                             false
% 2.44/1.01  --qbf_pred_elim                         true
% 2.44/1.01  --qbf_split                             512
% 2.44/1.01  
% 2.44/1.01  ------ BMC1 Options
% 2.44/1.01  
% 2.44/1.01  --bmc1_incremental                      false
% 2.44/1.01  --bmc1_axioms                           reachable_all
% 2.44/1.01  --bmc1_min_bound                        0
% 2.44/1.01  --bmc1_max_bound                        -1
% 2.44/1.01  --bmc1_max_bound_default                -1
% 2.44/1.01  --bmc1_symbol_reachability              true
% 2.44/1.01  --bmc1_property_lemmas                  false
% 2.44/1.01  --bmc1_k_induction                      false
% 2.44/1.01  --bmc1_non_equiv_states                 false
% 2.44/1.01  --bmc1_deadlock                         false
% 2.44/1.01  --bmc1_ucm                              false
% 2.44/1.01  --bmc1_add_unsat_core                   none
% 2.44/1.01  --bmc1_unsat_core_children              false
% 2.44/1.01  --bmc1_unsat_core_extrapolate_axioms    false
% 2.44/1.01  --bmc1_out_stat                         full
% 2.44/1.01  --bmc1_ground_init                      false
% 2.44/1.01  --bmc1_pre_inst_next_state              false
% 2.44/1.01  --bmc1_pre_inst_state                   false
% 2.44/1.01  --bmc1_pre_inst_reach_state             false
% 2.44/1.01  --bmc1_out_unsat_core                   false
% 2.44/1.01  --bmc1_aig_witness_out                  false
% 2.44/1.01  --bmc1_verbose                          false
% 2.44/1.01  --bmc1_dump_clauses_tptp                false
% 2.44/1.01  --bmc1_dump_unsat_core_tptp             false
% 2.44/1.01  --bmc1_dump_file                        -
% 2.44/1.01  --bmc1_ucm_expand_uc_limit              128
% 2.44/1.01  --bmc1_ucm_n_expand_iterations          6
% 2.44/1.01  --bmc1_ucm_extend_mode                  1
% 2.44/1.01  --bmc1_ucm_init_mode                    2
% 2.44/1.01  --bmc1_ucm_cone_mode                    none
% 2.44/1.01  --bmc1_ucm_reduced_relation_type        0
% 2.44/1.01  --bmc1_ucm_relax_model                  4
% 2.44/1.01  --bmc1_ucm_full_tr_after_sat            true
% 2.44/1.01  --bmc1_ucm_expand_neg_assumptions       false
% 2.44/1.01  --bmc1_ucm_layered_model                none
% 2.44/1.01  --bmc1_ucm_max_lemma_size               10
% 2.44/1.01  
% 2.44/1.01  ------ AIG Options
% 2.44/1.01  
% 2.44/1.01  --aig_mode                              false
% 2.44/1.01  
% 2.44/1.01  ------ Instantiation Options
% 2.44/1.01  
% 2.44/1.01  --instantiation_flag                    true
% 2.44/1.01  --inst_sos_flag                         false
% 2.44/1.01  --inst_sos_phase                        true
% 2.44/1.01  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 2.44/1.01  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 2.44/1.01  --inst_lit_sel_side                     none
% 2.44/1.01  --inst_solver_per_active                1400
% 2.44/1.01  --inst_solver_calls_frac                1.
% 2.44/1.01  --inst_passive_queue_type               priority_queues
% 2.44/1.01  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 2.44/1.01  --inst_passive_queues_freq              [25;2]
% 2.44/1.01  --inst_dismatching                      true
% 2.44/1.01  --inst_eager_unprocessed_to_passive     true
% 2.44/1.01  --inst_prop_sim_given                   true
% 2.44/1.01  --inst_prop_sim_new                     false
% 2.44/1.01  --inst_subs_new                         false
% 2.44/1.01  --inst_eq_res_simp                      false
% 2.44/1.01  --inst_subs_given                       false
% 2.44/1.01  --inst_orphan_elimination               true
% 2.44/1.01  --inst_learning_loop_flag               true
% 2.44/1.01  --inst_learning_start                   3000
% 2.44/1.01  --inst_learning_factor                  2
% 2.44/1.01  --inst_start_prop_sim_after_learn       3
% 2.44/1.01  --inst_sel_renew                        solver
% 2.44/1.01  --inst_lit_activity_flag                true
% 2.44/1.01  --inst_restr_to_given                   false
% 2.44/1.01  --inst_activity_threshold               500
% 2.44/1.01  --inst_out_proof                        true
% 2.44/1.01  
% 2.44/1.01  ------ Resolution Options
% 2.44/1.01  
% 2.44/1.01  --resolution_flag                       false
% 2.44/1.01  --res_lit_sel                           adaptive
% 2.44/1.01  --res_lit_sel_side                      none
% 2.44/1.01  --res_ordering                          kbo
% 2.44/1.01  --res_to_prop_solver                    active
% 2.44/1.01  --res_prop_simpl_new                    false
% 2.44/1.01  --res_prop_simpl_given                  true
% 2.44/1.01  --res_passive_queue_type                priority_queues
% 2.44/1.01  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 2.44/1.01  --res_passive_queues_freq               [15;5]
% 2.44/1.01  --res_forward_subs                      full
% 2.44/1.01  --res_backward_subs                     full
% 2.44/1.01  --res_forward_subs_resolution           true
% 2.44/1.01  --res_backward_subs_resolution          true
% 2.44/1.01  --res_orphan_elimination                true
% 2.44/1.01  --res_time_limit                        2.
% 2.44/1.01  --res_out_proof                         true
% 2.44/1.01  
% 2.44/1.01  ------ Superposition Options
% 2.44/1.01  
% 2.44/1.01  --superposition_flag                    true
% 2.44/1.01  --sup_passive_queue_type                priority_queues
% 2.44/1.01  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 2.44/1.01  --sup_passive_queues_freq               [8;1;4]
% 2.44/1.01  --demod_completeness_check              fast
% 2.44/1.01  --demod_use_ground                      true
% 2.44/1.01  --sup_to_prop_solver                    passive
% 2.44/1.01  --sup_prop_simpl_new                    true
% 2.44/1.01  --sup_prop_simpl_given                  true
% 2.44/1.01  --sup_fun_splitting                     false
% 2.44/1.01  --sup_smt_interval                      50000
% 2.44/1.01  
% 2.44/1.01  ------ Superposition Simplification Setup
% 2.44/1.01  
% 2.44/1.01  --sup_indices_passive                   []
% 2.44/1.01  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.44/1.01  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.44/1.01  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.44/1.01  --sup_full_triv                         [TrivRules;PropSubs]
% 2.44/1.01  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.44/1.01  --sup_full_bw                           [BwDemod]
% 2.44/1.01  --sup_immed_triv                        [TrivRules]
% 2.44/1.01  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 2.44/1.01  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.44/1.01  --sup_immed_bw_main                     []
% 2.44/1.01  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.44/1.01  --sup_input_triv                        [Unflattening;TrivRules]
% 2.44/1.01  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.44/1.01  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.44/1.01  
% 2.44/1.01  ------ Combination Options
% 2.44/1.01  
% 2.44/1.01  --comb_res_mult                         3
% 2.44/1.01  --comb_sup_mult                         2
% 2.44/1.01  --comb_inst_mult                        10
% 2.44/1.01  
% 2.44/1.01  ------ Debug Options
% 2.44/1.01  
% 2.44/1.01  --dbg_backtrace                         false
% 2.44/1.01  --dbg_dump_prop_clauses                 false
% 2.44/1.01  --dbg_dump_prop_clauses_file            -
% 2.44/1.01  --dbg_out_stat                          false
% 2.44/1.01  
% 2.44/1.01  
% 2.44/1.01  
% 2.44/1.01  
% 2.44/1.01  ------ Proving...
% 2.44/1.01  
% 2.44/1.01  
% 2.44/1.01  % SZS status Theorem for theBenchmark.p
% 2.44/1.01  
% 2.44/1.01  % SZS output start CNFRefutation for theBenchmark.p
% 2.44/1.01  
% 2.44/1.01  fof(f1,axiom,(
% 2.44/1.01    ! [X0,X1] : (! [X2] : (r2_hidden(X2,X0) <=> r2_hidden(X2,X1)) => X0 = X1)),
% 2.44/1.01    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.44/1.01  
% 2.44/1.01  fof(f17,plain,(
% 2.44/1.01    ! [X0,X1] : (X0 = X1 | ? [X2] : (r2_hidden(X2,X0) <~> r2_hidden(X2,X1)))),
% 2.44/1.01    inference(ennf_transformation,[],[f1])).
% 2.44/1.01  
% 2.44/1.01  fof(f32,plain,(
% 2.44/1.01    ! [X0,X1] : (X0 = X1 | ? [X2] : ((~r2_hidden(X2,X1) | ~r2_hidden(X2,X0)) & (r2_hidden(X2,X1) | r2_hidden(X2,X0))))),
% 2.44/1.01    inference(nnf_transformation,[],[f17])).
% 2.44/1.01  
% 2.44/1.01  fof(f33,plain,(
% 2.44/1.01    ! [X1,X0] : (? [X2] : ((~r2_hidden(X2,X1) | ~r2_hidden(X2,X0)) & (r2_hidden(X2,X1) | r2_hidden(X2,X0))) => ((~r2_hidden(sK0(X0,X1),X1) | ~r2_hidden(sK0(X0,X1),X0)) & (r2_hidden(sK0(X0,X1),X1) | r2_hidden(sK0(X0,X1),X0))))),
% 2.44/1.01    introduced(choice_axiom,[])).
% 2.44/1.01  
% 2.44/1.01  fof(f34,plain,(
% 2.44/1.01    ! [X0,X1] : (X0 = X1 | ((~r2_hidden(sK0(X0,X1),X1) | ~r2_hidden(sK0(X0,X1),X0)) & (r2_hidden(sK0(X0,X1),X1) | r2_hidden(sK0(X0,X1),X0))))),
% 2.44/1.01    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f32,f33])).
% 2.44/1.01  
% 2.44/1.01  fof(f46,plain,(
% 2.44/1.01    ( ! [X0,X1] : (X0 = X1 | r2_hidden(sK0(X0,X1),X1) | r2_hidden(sK0(X0,X1),X0)) )),
% 2.44/1.01    inference(cnf_transformation,[],[f34])).
% 2.44/1.01  
% 2.44/1.01  fof(f5,axiom,(
% 2.44/1.01    ! [X0,X1] : (r2_hidden(X0,X1) => m1_subset_1(X0,X1))),
% 2.44/1.01    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.44/1.01  
% 2.44/1.01  fof(f19,plain,(
% 2.44/1.01    ! [X0,X1] : (m1_subset_1(X0,X1) | ~r2_hidden(X0,X1))),
% 2.44/1.01    inference(ennf_transformation,[],[f5])).
% 2.44/1.01  
% 2.44/1.01  fof(f51,plain,(
% 2.44/1.01    ( ! [X0,X1] : (m1_subset_1(X0,X1) | ~r2_hidden(X0,X1)) )),
% 2.44/1.01    inference(cnf_transformation,[],[f19])).
% 2.44/1.01  
% 2.44/1.01  fof(f6,axiom,(
% 2.44/1.01    ! [X0,X1] : (m1_subset_1(X0,X1) => (r2_hidden(X0,X1) | v1_xboole_0(X1)))),
% 2.44/1.01    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.44/1.01  
% 2.44/1.01  fof(f20,plain,(
% 2.44/1.01    ! [X0,X1] : ((r2_hidden(X0,X1) | v1_xboole_0(X1)) | ~m1_subset_1(X0,X1))),
% 2.44/1.01    inference(ennf_transformation,[],[f6])).
% 2.44/1.01  
% 2.44/1.01  fof(f21,plain,(
% 2.44/1.01    ! [X0,X1] : (r2_hidden(X0,X1) | v1_xboole_0(X1) | ~m1_subset_1(X0,X1))),
% 2.44/1.01    inference(flattening,[],[f20])).
% 2.44/1.01  
% 2.44/1.01  fof(f52,plain,(
% 2.44/1.01    ( ! [X0,X1] : (r2_hidden(X0,X1) | v1_xboole_0(X1) | ~m1_subset_1(X0,X1)) )),
% 2.44/1.01    inference(cnf_transformation,[],[f21])).
% 2.44/1.01  
% 2.44/1.01  fof(f12,conjecture,(
% 2.44/1.01    ! [X0] : ((l1_orders_2(X0) & v1_yellow_0(X0) & v5_orders_2(X0) & v4_orders_2(X0) & v3_orders_2(X0) & ~v2_struct_0(X0)) => ! [X1] : ((m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & v13_waybel_0(X1,X0) & v2_waybel_0(X1,X0) & ~v1_xboole_0(X1)) => (v1_subset_1(X1,u1_struct_0(X0)) <=> ~r2_hidden(k3_yellow_0(X0),X1))))),
% 2.44/1.01    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.44/1.01  
% 2.44/1.01  fof(f13,negated_conjecture,(
% 2.44/1.01    ~! [X0] : ((l1_orders_2(X0) & v1_yellow_0(X0) & v5_orders_2(X0) & v4_orders_2(X0) & v3_orders_2(X0) & ~v2_struct_0(X0)) => ! [X1] : ((m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & v13_waybel_0(X1,X0) & v2_waybel_0(X1,X0) & ~v1_xboole_0(X1)) => (v1_subset_1(X1,u1_struct_0(X0)) <=> ~r2_hidden(k3_yellow_0(X0),X1))))),
% 2.44/1.01    inference(negated_conjecture,[],[f12])).
% 2.44/1.01  
% 2.44/1.01  fof(f14,plain,(
% 2.44/1.01    ~! [X0] : ((l1_orders_2(X0) & v1_yellow_0(X0) & v5_orders_2(X0) & v4_orders_2(X0) & v3_orders_2(X0) & ~v2_struct_0(X0)) => ! [X1] : ((m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & v13_waybel_0(X1,X0) & ~v1_xboole_0(X1)) => (v1_subset_1(X1,u1_struct_0(X0)) <=> ~r2_hidden(k3_yellow_0(X0),X1))))),
% 2.44/1.01    inference(pure_predicate_removal,[],[f13])).
% 2.44/1.01  
% 2.44/1.01  fof(f15,plain,(
% 2.44/1.01    ~! [X0] : ((l1_orders_2(X0) & v1_yellow_0(X0) & v5_orders_2(X0) & v3_orders_2(X0) & ~v2_struct_0(X0)) => ! [X1] : ((m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & v13_waybel_0(X1,X0) & ~v1_xboole_0(X1)) => (v1_subset_1(X1,u1_struct_0(X0)) <=> ~r2_hidden(k3_yellow_0(X0),X1))))),
% 2.44/1.01    inference(pure_predicate_removal,[],[f14])).
% 2.44/1.01  
% 2.44/1.01  fof(f16,plain,(
% 2.44/1.01    ~! [X0] : ((l1_orders_2(X0) & v1_yellow_0(X0) & v5_orders_2(X0) & ~v2_struct_0(X0)) => ! [X1] : ((m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & v13_waybel_0(X1,X0) & ~v1_xboole_0(X1)) => (v1_subset_1(X1,u1_struct_0(X0)) <=> ~r2_hidden(k3_yellow_0(X0),X1))))),
% 2.44/1.01    inference(pure_predicate_removal,[],[f15])).
% 2.44/1.01  
% 2.44/1.01  fof(f30,plain,(
% 2.44/1.01    ? [X0] : (? [X1] : ((v1_subset_1(X1,u1_struct_0(X0)) <~> ~r2_hidden(k3_yellow_0(X0),X1)) & (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & v13_waybel_0(X1,X0) & ~v1_xboole_0(X1))) & (l1_orders_2(X0) & v1_yellow_0(X0) & v5_orders_2(X0) & ~v2_struct_0(X0)))),
% 2.44/1.01    inference(ennf_transformation,[],[f16])).
% 2.44/1.01  
% 2.44/1.01  fof(f31,plain,(
% 2.44/1.01    ? [X0] : (? [X1] : ((v1_subset_1(X1,u1_struct_0(X0)) <~> ~r2_hidden(k3_yellow_0(X0),X1)) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & v13_waybel_0(X1,X0) & ~v1_xboole_0(X1)) & l1_orders_2(X0) & v1_yellow_0(X0) & v5_orders_2(X0) & ~v2_struct_0(X0))),
% 2.44/1.01    inference(flattening,[],[f30])).
% 2.44/1.01  
% 2.44/1.01  fof(f41,plain,(
% 2.44/1.01    ? [X0] : (? [X1] : (((r2_hidden(k3_yellow_0(X0),X1) | ~v1_subset_1(X1,u1_struct_0(X0))) & (~r2_hidden(k3_yellow_0(X0),X1) | v1_subset_1(X1,u1_struct_0(X0)))) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & v13_waybel_0(X1,X0) & ~v1_xboole_0(X1)) & l1_orders_2(X0) & v1_yellow_0(X0) & v5_orders_2(X0) & ~v2_struct_0(X0))),
% 2.44/1.01    inference(nnf_transformation,[],[f31])).
% 2.44/1.01  
% 2.44/1.01  fof(f42,plain,(
% 2.44/1.01    ? [X0] : (? [X1] : ((r2_hidden(k3_yellow_0(X0),X1) | ~v1_subset_1(X1,u1_struct_0(X0))) & (~r2_hidden(k3_yellow_0(X0),X1) | v1_subset_1(X1,u1_struct_0(X0))) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & v13_waybel_0(X1,X0) & ~v1_xboole_0(X1)) & l1_orders_2(X0) & v1_yellow_0(X0) & v5_orders_2(X0) & ~v2_struct_0(X0))),
% 2.44/1.01    inference(flattening,[],[f41])).
% 2.44/1.01  
% 2.44/1.01  fof(f44,plain,(
% 2.44/1.01    ( ! [X0] : (? [X1] : ((r2_hidden(k3_yellow_0(X0),X1) | ~v1_subset_1(X1,u1_struct_0(X0))) & (~r2_hidden(k3_yellow_0(X0),X1) | v1_subset_1(X1,u1_struct_0(X0))) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & v13_waybel_0(X1,X0) & ~v1_xboole_0(X1)) => ((r2_hidden(k3_yellow_0(X0),sK4) | ~v1_subset_1(sK4,u1_struct_0(X0))) & (~r2_hidden(k3_yellow_0(X0),sK4) | v1_subset_1(sK4,u1_struct_0(X0))) & m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(X0))) & v13_waybel_0(sK4,X0) & ~v1_xboole_0(sK4))) )),
% 2.44/1.01    introduced(choice_axiom,[])).
% 2.44/1.01  
% 2.44/1.01  fof(f43,plain,(
% 2.44/1.01    ? [X0] : (? [X1] : ((r2_hidden(k3_yellow_0(X0),X1) | ~v1_subset_1(X1,u1_struct_0(X0))) & (~r2_hidden(k3_yellow_0(X0),X1) | v1_subset_1(X1,u1_struct_0(X0))) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & v13_waybel_0(X1,X0) & ~v1_xboole_0(X1)) & l1_orders_2(X0) & v1_yellow_0(X0) & v5_orders_2(X0) & ~v2_struct_0(X0)) => (? [X1] : ((r2_hidden(k3_yellow_0(sK3),X1) | ~v1_subset_1(X1,u1_struct_0(sK3))) & (~r2_hidden(k3_yellow_0(sK3),X1) | v1_subset_1(X1,u1_struct_0(sK3))) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK3))) & v13_waybel_0(X1,sK3) & ~v1_xboole_0(X1)) & l1_orders_2(sK3) & v1_yellow_0(sK3) & v5_orders_2(sK3) & ~v2_struct_0(sK3))),
% 2.44/1.01    introduced(choice_axiom,[])).
% 2.44/1.01  
% 2.44/1.01  fof(f45,plain,(
% 2.44/1.01    ((r2_hidden(k3_yellow_0(sK3),sK4) | ~v1_subset_1(sK4,u1_struct_0(sK3))) & (~r2_hidden(k3_yellow_0(sK3),sK4) | v1_subset_1(sK4,u1_struct_0(sK3))) & m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(sK3))) & v13_waybel_0(sK4,sK3) & ~v1_xboole_0(sK4)) & l1_orders_2(sK3) & v1_yellow_0(sK3) & v5_orders_2(sK3) & ~v2_struct_0(sK3)),
% 2.44/1.01    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3,sK4])],[f42,f44,f43])).
% 2.44/1.01  
% 2.44/1.01  fof(f68,plain,(
% 2.44/1.01    ~v1_xboole_0(sK4)),
% 2.44/1.01    inference(cnf_transformation,[],[f45])).
% 2.44/1.01  
% 2.44/1.01  fof(f11,axiom,(
% 2.44/1.01    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => (v1_subset_1(X1,X0) <=> X0 != X1))),
% 2.44/1.01    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.44/1.01  
% 2.44/1.01  fof(f29,plain,(
% 2.44/1.01    ! [X0,X1] : ((v1_subset_1(X1,X0) <=> X0 != X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 2.44/1.01    inference(ennf_transformation,[],[f11])).
% 2.44/1.01  
% 2.44/1.01  fof(f40,plain,(
% 2.44/1.01    ! [X0,X1] : (((v1_subset_1(X1,X0) | X0 = X1) & (X0 != X1 | ~v1_subset_1(X1,X0))) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 2.44/1.01    inference(nnf_transformation,[],[f29])).
% 2.44/1.01  
% 2.44/1.01  fof(f63,plain,(
% 2.44/1.01    ( ! [X0,X1] : (v1_subset_1(X1,X0) | X0 = X1 | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 2.44/1.01    inference(cnf_transformation,[],[f40])).
% 2.44/1.01  
% 2.44/1.01  fof(f72,plain,(
% 2.44/1.01    r2_hidden(k3_yellow_0(sK3),sK4) | ~v1_subset_1(sK4,u1_struct_0(sK3))),
% 2.44/1.01    inference(cnf_transformation,[],[f45])).
% 2.44/1.01  
% 2.44/1.01  fof(f70,plain,(
% 2.44/1.01    m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(sK3)))),
% 2.44/1.01    inference(cnf_transformation,[],[f45])).
% 2.44/1.01  
% 2.44/1.01  fof(f67,plain,(
% 2.44/1.01    l1_orders_2(sK3)),
% 2.44/1.01    inference(cnf_transformation,[],[f45])).
% 2.44/1.01  
% 2.44/1.01  fof(f8,axiom,(
% 2.44/1.01    ! [X0] : (l1_orders_2(X0) => m1_subset_1(k3_yellow_0(X0),u1_struct_0(X0)))),
% 2.44/1.01    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.44/1.01  
% 2.44/1.01  fof(f24,plain,(
% 2.44/1.01    ! [X0] : (m1_subset_1(k3_yellow_0(X0),u1_struct_0(X0)) | ~l1_orders_2(X0))),
% 2.44/1.01    inference(ennf_transformation,[],[f8])).
% 2.44/1.01  
% 2.44/1.01  fof(f54,plain,(
% 2.44/1.01    ( ! [X0] : (m1_subset_1(k3_yellow_0(X0),u1_struct_0(X0)) | ~l1_orders_2(X0)) )),
% 2.44/1.01    inference(cnf_transformation,[],[f24])).
% 2.44/1.01  
% 2.44/1.01  fof(f10,axiom,(
% 2.44/1.01    ! [X0] : (l1_orders_2(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => (v13_waybel_0(X1,X0) <=> ! [X2] : (m1_subset_1(X2,u1_struct_0(X0)) => ! [X3] : (m1_subset_1(X3,u1_struct_0(X0)) => ((r1_orders_2(X0,X2,X3) & r2_hidden(X2,X1)) => r2_hidden(X3,X1)))))))),
% 2.44/1.01    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.44/1.01  
% 2.44/1.01  fof(f27,plain,(
% 2.44/1.01    ! [X0] : (! [X1] : ((v13_waybel_0(X1,X0) <=> ! [X2] : (! [X3] : ((r2_hidden(X3,X1) | (~r1_orders_2(X0,X2,X3) | ~r2_hidden(X2,X1))) | ~m1_subset_1(X3,u1_struct_0(X0))) | ~m1_subset_1(X2,u1_struct_0(X0)))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_orders_2(X0))),
% 2.44/1.01    inference(ennf_transformation,[],[f10])).
% 2.44/1.01  
% 2.44/1.01  fof(f28,plain,(
% 2.44/1.01    ! [X0] : (! [X1] : ((v13_waybel_0(X1,X0) <=> ! [X2] : (! [X3] : (r2_hidden(X3,X1) | ~r1_orders_2(X0,X2,X3) | ~r2_hidden(X2,X1) | ~m1_subset_1(X3,u1_struct_0(X0))) | ~m1_subset_1(X2,u1_struct_0(X0)))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_orders_2(X0))),
% 2.44/1.01    inference(flattening,[],[f27])).
% 2.44/1.01  
% 2.44/1.01  fof(f35,plain,(
% 2.44/1.01    ! [X0] : (! [X1] : (((v13_waybel_0(X1,X0) | ? [X2] : (? [X3] : (~r2_hidden(X3,X1) & r1_orders_2(X0,X2,X3) & r2_hidden(X2,X1) & m1_subset_1(X3,u1_struct_0(X0))) & m1_subset_1(X2,u1_struct_0(X0)))) & (! [X2] : (! [X3] : (r2_hidden(X3,X1) | ~r1_orders_2(X0,X2,X3) | ~r2_hidden(X2,X1) | ~m1_subset_1(X3,u1_struct_0(X0))) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~v13_waybel_0(X1,X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_orders_2(X0))),
% 2.44/1.01    inference(nnf_transformation,[],[f28])).
% 2.44/1.01  
% 2.44/1.01  fof(f36,plain,(
% 2.44/1.01    ! [X0] : (! [X1] : (((v13_waybel_0(X1,X0) | ? [X2] : (? [X3] : (~r2_hidden(X3,X1) & r1_orders_2(X0,X2,X3) & r2_hidden(X2,X1) & m1_subset_1(X3,u1_struct_0(X0))) & m1_subset_1(X2,u1_struct_0(X0)))) & (! [X4] : (! [X5] : (r2_hidden(X5,X1) | ~r1_orders_2(X0,X4,X5) | ~r2_hidden(X4,X1) | ~m1_subset_1(X5,u1_struct_0(X0))) | ~m1_subset_1(X4,u1_struct_0(X0))) | ~v13_waybel_0(X1,X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_orders_2(X0))),
% 2.44/1.01    inference(rectify,[],[f35])).
% 2.44/1.01  
% 2.44/1.01  fof(f38,plain,(
% 2.44/1.01    ( ! [X2] : (! [X1,X0] : (? [X3] : (~r2_hidden(X3,X1) & r1_orders_2(X0,X2,X3) & r2_hidden(X2,X1) & m1_subset_1(X3,u1_struct_0(X0))) => (~r2_hidden(sK2(X0,X1),X1) & r1_orders_2(X0,X2,sK2(X0,X1)) & r2_hidden(X2,X1) & m1_subset_1(sK2(X0,X1),u1_struct_0(X0))))) )),
% 2.44/1.01    introduced(choice_axiom,[])).
% 2.44/1.01  
% 2.44/1.01  fof(f37,plain,(
% 2.44/1.01    ! [X1,X0] : (? [X2] : (? [X3] : (~r2_hidden(X3,X1) & r1_orders_2(X0,X2,X3) & r2_hidden(X2,X1) & m1_subset_1(X3,u1_struct_0(X0))) & m1_subset_1(X2,u1_struct_0(X0))) => (? [X3] : (~r2_hidden(X3,X1) & r1_orders_2(X0,sK1(X0,X1),X3) & r2_hidden(sK1(X0,X1),X1) & m1_subset_1(X3,u1_struct_0(X0))) & m1_subset_1(sK1(X0,X1),u1_struct_0(X0))))),
% 2.44/1.01    introduced(choice_axiom,[])).
% 2.44/1.01  
% 2.44/1.01  fof(f39,plain,(
% 2.44/1.01    ! [X0] : (! [X1] : (((v13_waybel_0(X1,X0) | ((~r2_hidden(sK2(X0,X1),X1) & r1_orders_2(X0,sK1(X0,X1),sK2(X0,X1)) & r2_hidden(sK1(X0,X1),X1) & m1_subset_1(sK2(X0,X1),u1_struct_0(X0))) & m1_subset_1(sK1(X0,X1),u1_struct_0(X0)))) & (! [X4] : (! [X5] : (r2_hidden(X5,X1) | ~r1_orders_2(X0,X4,X5) | ~r2_hidden(X4,X1) | ~m1_subset_1(X5,u1_struct_0(X0))) | ~m1_subset_1(X4,u1_struct_0(X0))) | ~v13_waybel_0(X1,X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_orders_2(X0))),
% 2.44/1.01    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1,sK2])],[f36,f38,f37])).
% 2.44/1.01  
% 2.44/1.01  fof(f56,plain,(
% 2.44/1.01    ( ! [X4,X0,X5,X1] : (r2_hidden(X5,X1) | ~r1_orders_2(X0,X4,X5) | ~r2_hidden(X4,X1) | ~m1_subset_1(X5,u1_struct_0(X0)) | ~m1_subset_1(X4,u1_struct_0(X0)) | ~v13_waybel_0(X1,X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_orders_2(X0)) )),
% 2.44/1.01    inference(cnf_transformation,[],[f39])).
% 2.44/1.01  
% 2.44/1.01  fof(f9,axiom,(
% 2.44/1.01    ! [X0] : ((l1_orders_2(X0) & v1_yellow_0(X0) & v5_orders_2(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,u1_struct_0(X0)) => r1_orders_2(X0,k3_yellow_0(X0),X1)))),
% 2.44/1.01    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.44/1.01  
% 2.44/1.01  fof(f25,plain,(
% 2.44/1.01    ! [X0] : (! [X1] : (r1_orders_2(X0,k3_yellow_0(X0),X1) | ~m1_subset_1(X1,u1_struct_0(X0))) | (~l1_orders_2(X0) | ~v1_yellow_0(X0) | ~v5_orders_2(X0) | v2_struct_0(X0)))),
% 2.44/1.01    inference(ennf_transformation,[],[f9])).
% 2.44/1.01  
% 2.44/1.01  fof(f26,plain,(
% 2.44/1.01    ! [X0] : (! [X1] : (r1_orders_2(X0,k3_yellow_0(X0),X1) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~l1_orders_2(X0) | ~v1_yellow_0(X0) | ~v5_orders_2(X0) | v2_struct_0(X0))),
% 2.44/1.01    inference(flattening,[],[f25])).
% 2.44/1.01  
% 2.44/1.01  fof(f55,plain,(
% 2.44/1.01    ( ! [X0,X1] : (r1_orders_2(X0,k3_yellow_0(X0),X1) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_orders_2(X0) | ~v1_yellow_0(X0) | ~v5_orders_2(X0) | v2_struct_0(X0)) )),
% 2.44/1.01    inference(cnf_transformation,[],[f26])).
% 2.44/1.01  
% 2.44/1.01  fof(f66,plain,(
% 2.44/1.01    v1_yellow_0(sK3)),
% 2.44/1.01    inference(cnf_transformation,[],[f45])).
% 2.44/1.01  
% 2.44/1.01  fof(f64,plain,(
% 2.44/1.01    ~v2_struct_0(sK3)),
% 2.44/1.01    inference(cnf_transformation,[],[f45])).
% 2.44/1.01  
% 2.44/1.01  fof(f65,plain,(
% 2.44/1.01    v5_orders_2(sK3)),
% 2.44/1.01    inference(cnf_transformation,[],[f45])).
% 2.44/1.01  
% 2.44/1.01  fof(f69,plain,(
% 2.44/1.01    v13_waybel_0(sK4,sK3)),
% 2.44/1.01    inference(cnf_transformation,[],[f45])).
% 2.44/1.01  
% 2.44/1.01  fof(f4,axiom,(
% 2.44/1.01    ! [X0] : ~v1_subset_1(k2_subset_1(X0),X0)),
% 2.44/1.01    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.44/1.01  
% 2.44/1.01  fof(f50,plain,(
% 2.44/1.01    ( ! [X0] : (~v1_subset_1(k2_subset_1(X0),X0)) )),
% 2.44/1.01    inference(cnf_transformation,[],[f4])).
% 2.44/1.01  
% 2.44/1.01  fof(f71,plain,(
% 2.44/1.01    ~r2_hidden(k3_yellow_0(sK3),sK4) | v1_subset_1(sK4,u1_struct_0(sK3))),
% 2.44/1.01    inference(cnf_transformation,[],[f45])).
% 2.44/1.01  
% 2.44/1.01  fof(f2,axiom,(
% 2.44/1.01    ! [X0] : k2_subset_1(X0) = X0),
% 2.44/1.01    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.44/1.01  
% 2.44/1.01  fof(f48,plain,(
% 2.44/1.01    ( ! [X0] : (k2_subset_1(X0) = X0) )),
% 2.44/1.01    inference(cnf_transformation,[],[f2])).
% 2.44/1.01  
% 2.44/1.01  fof(f47,plain,(
% 2.44/1.01    ( ! [X0,X1] : (X0 = X1 | ~r2_hidden(sK0(X0,X1),X1) | ~r2_hidden(sK0(X0,X1),X0)) )),
% 2.44/1.01    inference(cnf_transformation,[],[f34])).
% 2.44/1.01  
% 2.44/1.01  fof(f3,axiom,(
% 2.44/1.01    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => ! [X2] : (r2_hidden(X2,X1) => r2_hidden(X2,X0)))),
% 2.44/1.01    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.44/1.01  
% 2.44/1.01  fof(f18,plain,(
% 2.44/1.01    ! [X0,X1] : (! [X2] : (r2_hidden(X2,X0) | ~r2_hidden(X2,X1)) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 2.44/1.01    inference(ennf_transformation,[],[f3])).
% 2.44/1.01  
% 2.44/1.01  fof(f49,plain,(
% 2.44/1.01    ( ! [X2,X0,X1] : (r2_hidden(X2,X0) | ~r2_hidden(X2,X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 2.44/1.01    inference(cnf_transformation,[],[f18])).
% 2.44/1.01  
% 2.44/1.01  cnf(c_1,plain,
% 2.44/1.01      ( r2_hidden(sK0(X0,X1),X1) | r2_hidden(sK0(X0,X1),X0) | X1 = X0 ),
% 2.44/1.01      inference(cnf_transformation,[],[f46]) ).
% 2.44/1.01  
% 2.44/1.01  cnf(c_1120,plain,
% 2.44/1.01      ( X0 = X1
% 2.44/1.01      | r2_hidden(sK0(X1,X0),X0) = iProver_top
% 2.44/1.01      | r2_hidden(sK0(X1,X0),X1) = iProver_top ),
% 2.44/1.01      inference(predicate_to_equality,[status(thm)],[c_1]) ).
% 2.44/1.01  
% 2.44/1.01  cnf(c_5,plain,
% 2.44/1.01      ( m1_subset_1(X0,X1) | ~ r2_hidden(X0,X1) ),
% 2.44/1.01      inference(cnf_transformation,[],[f51]) ).
% 2.44/1.01  
% 2.44/1.01  cnf(c_1118,plain,
% 2.44/1.01      ( m1_subset_1(X0,X1) = iProver_top
% 2.44/1.01      | r2_hidden(X0,X1) != iProver_top ),
% 2.44/1.01      inference(predicate_to_equality,[status(thm)],[c_5]) ).
% 2.44/1.01  
% 2.44/1.01  cnf(c_1583,plain,
% 2.44/1.01      ( X0 = X1
% 2.44/1.01      | m1_subset_1(sK0(X0,X1),X0) = iProver_top
% 2.44/1.01      | r2_hidden(sK0(X0,X1),X1) = iProver_top ),
% 2.44/1.01      inference(superposition,[status(thm)],[c_1120,c_1118]) ).
% 2.44/1.01  
% 2.44/1.01  cnf(c_2022,plain,
% 2.44/1.01      ( X0 = X1
% 2.44/1.01      | m1_subset_1(sK0(X1,X0),X1) = iProver_top
% 2.44/1.01      | m1_subset_1(sK0(X1,X0),X0) = iProver_top ),
% 2.44/1.01      inference(superposition,[status(thm)],[c_1583,c_1118]) ).
% 2.44/1.01  
% 2.44/1.01  cnf(c_6,plain,
% 2.44/1.01      ( ~ m1_subset_1(X0,X1) | r2_hidden(X0,X1) | v1_xboole_0(X1) ),
% 2.44/1.01      inference(cnf_transformation,[],[f52]) ).
% 2.44/1.01  
% 2.44/1.01  cnf(c_22,negated_conjecture,
% 2.44/1.01      ( ~ v1_xboole_0(sK4) ),
% 2.44/1.01      inference(cnf_transformation,[],[f68]) ).
% 2.44/1.01  
% 2.44/1.01  cnf(c_348,plain,
% 2.44/1.01      ( ~ m1_subset_1(X0,X1) | r2_hidden(X0,X1) | sK4 != X1 ),
% 2.44/1.01      inference(resolution_lifted,[status(thm)],[c_6,c_22]) ).
% 2.44/1.01  
% 2.44/1.01  cnf(c_349,plain,
% 2.44/1.01      ( ~ m1_subset_1(X0,sK4) | r2_hidden(X0,sK4) ),
% 2.44/1.01      inference(unflattening,[status(thm)],[c_348]) ).
% 2.44/1.01  
% 2.44/1.01  cnf(c_1114,plain,
% 2.44/1.01      ( m1_subset_1(X0,sK4) != iProver_top
% 2.44/1.01      | r2_hidden(X0,sK4) = iProver_top ),
% 2.44/1.01      inference(predicate_to_equality,[status(thm)],[c_349]) ).
% 2.44/1.01  
% 2.44/1.01  cnf(c_2292,plain,
% 2.44/1.01      ( sK4 = X0
% 2.44/1.01      | m1_subset_1(sK0(X0,sK4),X0) = iProver_top
% 2.44/1.01      | r2_hidden(sK0(X0,sK4),sK4) = iProver_top ),
% 2.44/1.01      inference(superposition,[status(thm)],[c_2022,c_1114]) ).
% 2.44/1.01  
% 2.44/1.01  cnf(c_16,plain,
% 2.44/1.01      ( v1_subset_1(X0,X1)
% 2.44/1.01      | ~ m1_subset_1(X0,k1_zfmisc_1(X1))
% 2.44/1.01      | X0 = X1 ),
% 2.44/1.01      inference(cnf_transformation,[],[f63]) ).
% 2.44/1.01  
% 2.44/1.01  cnf(c_18,negated_conjecture,
% 2.44/1.01      ( ~ v1_subset_1(sK4,u1_struct_0(sK3))
% 2.44/1.01      | r2_hidden(k3_yellow_0(sK3),sK4) ),
% 2.44/1.01      inference(cnf_transformation,[],[f72]) ).
% 2.44/1.01  
% 2.44/1.01  cnf(c_195,plain,
% 2.44/1.01      ( ~ v1_subset_1(sK4,u1_struct_0(sK3))
% 2.44/1.01      | r2_hidden(k3_yellow_0(sK3),sK4) ),
% 2.44/1.01      inference(prop_impl,[status(thm)],[c_18]) ).
% 2.44/1.01  
% 2.44/1.01  cnf(c_409,plain,
% 2.44/1.01      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
% 2.44/1.01      | r2_hidden(k3_yellow_0(sK3),sK4)
% 2.44/1.01      | X1 = X0
% 2.44/1.01      | u1_struct_0(sK3) != X1
% 2.44/1.01      | sK4 != X0 ),
% 2.44/1.01      inference(resolution_lifted,[status(thm)],[c_16,c_195]) ).
% 2.44/1.01  
% 2.44/1.01  cnf(c_410,plain,
% 2.44/1.01      ( ~ m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(sK3)))
% 2.44/1.01      | r2_hidden(k3_yellow_0(sK3),sK4)
% 2.44/1.01      | u1_struct_0(sK3) = sK4 ),
% 2.44/1.01      inference(unflattening,[status(thm)],[c_409]) ).
% 2.44/1.01  
% 2.44/1.01  cnf(c_20,negated_conjecture,
% 2.44/1.01      ( m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(sK3))) ),
% 2.44/1.01      inference(cnf_transformation,[],[f70]) ).
% 2.44/1.01  
% 2.44/1.01  cnf(c_412,plain,
% 2.44/1.01      ( r2_hidden(k3_yellow_0(sK3),sK4) | u1_struct_0(sK3) = sK4 ),
% 2.44/1.01      inference(global_propositional_subsumption,
% 2.44/1.01                [status(thm)],
% 2.44/1.01                [c_410,c_20]) ).
% 2.44/1.01  
% 2.44/1.01  cnf(c_1111,plain,
% 2.44/1.01      ( u1_struct_0(sK3) = sK4
% 2.44/1.01      | r2_hidden(k3_yellow_0(sK3),sK4) = iProver_top ),
% 2.44/1.01      inference(predicate_to_equality,[status(thm)],[c_412]) ).
% 2.44/1.01  
% 2.44/1.01  cnf(c_23,negated_conjecture,
% 2.44/1.01      ( l1_orders_2(sK3) ),
% 2.44/1.01      inference(cnf_transformation,[],[f67]) ).
% 2.44/1.01  
% 2.44/1.01  cnf(c_30,plain,
% 2.44/1.01      ( l1_orders_2(sK3) = iProver_top ),
% 2.44/1.01      inference(predicate_to_equality,[status(thm)],[c_23]) ).
% 2.44/1.01  
% 2.44/1.01  cnf(c_33,plain,
% 2.44/1.01      ( m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(sK3))) = iProver_top ),
% 2.44/1.01      inference(predicate_to_equality,[status(thm)],[c_20]) ).
% 2.44/1.01  
% 2.44/1.01  cnf(c_8,plain,
% 2.44/1.01      ( m1_subset_1(k3_yellow_0(X0),u1_struct_0(X0))
% 2.44/1.01      | ~ l1_orders_2(X0) ),
% 2.44/1.01      inference(cnf_transformation,[],[f54]) ).
% 2.44/1.01  
% 2.44/1.01  cnf(c_61,plain,
% 2.44/1.01      ( m1_subset_1(k3_yellow_0(X0),u1_struct_0(X0)) = iProver_top
% 2.44/1.01      | l1_orders_2(X0) != iProver_top ),
% 2.44/1.01      inference(predicate_to_equality,[status(thm)],[c_8]) ).
% 2.44/1.01  
% 2.44/1.01  cnf(c_63,plain,
% 2.44/1.01      ( m1_subset_1(k3_yellow_0(sK3),u1_struct_0(sK3)) = iProver_top
% 2.44/1.01      | l1_orders_2(sK3) != iProver_top ),
% 2.44/1.01      inference(instantiation,[status(thm)],[c_61]) ).
% 2.44/1.01  
% 2.44/1.01  cnf(c_411,plain,
% 2.44/1.01      ( u1_struct_0(sK3) = sK4
% 2.44/1.01      | m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(sK3))) != iProver_top
% 2.44/1.01      | r2_hidden(k3_yellow_0(sK3),sK4) = iProver_top ),
% 2.44/1.01      inference(predicate_to_equality,[status(thm)],[c_410]) ).
% 2.44/1.01  
% 2.44/1.01  cnf(c_772,plain,
% 2.44/1.01      ( X0 != X1 | k3_yellow_0(X0) = k3_yellow_0(X1) ),
% 2.44/1.01      theory(equality) ).
% 2.44/1.01  
% 2.44/1.01  cnf(c_781,plain,
% 2.44/1.01      ( k3_yellow_0(sK3) = k3_yellow_0(sK3) | sK3 != sK3 ),
% 2.44/1.01      inference(instantiation,[status(thm)],[c_772]) ).
% 2.44/1.01  
% 2.44/1.01  cnf(c_766,plain,( X0 = X0 ),theory(equality) ).
% 2.44/1.01  
% 2.44/1.01  cnf(c_787,plain,
% 2.44/1.01      ( sK3 = sK3 ),
% 2.44/1.01      inference(instantiation,[status(thm)],[c_766]) ).
% 2.44/1.01  
% 2.44/1.01  cnf(c_1385,plain,
% 2.44/1.01      ( sK4 = sK4 ),
% 2.44/1.01      inference(instantiation,[status(thm)],[c_766]) ).
% 2.44/1.01  
% 2.44/1.01  cnf(c_771,plain,
% 2.44/1.01      ( ~ m1_subset_1(X0,X1) | m1_subset_1(X2,X3) | X2 != X0 | X3 != X1 ),
% 2.44/1.01      theory(equality) ).
% 2.44/1.01  
% 2.44/1.01  cnf(c_1323,plain,
% 2.44/1.01      ( m1_subset_1(X0,X1)
% 2.44/1.01      | ~ m1_subset_1(k3_yellow_0(sK3),u1_struct_0(sK3))
% 2.44/1.01      | X1 != u1_struct_0(sK3)
% 2.44/1.01      | X0 != k3_yellow_0(sK3) ),
% 2.44/1.01      inference(instantiation,[status(thm)],[c_771]) ).
% 2.44/1.01  
% 2.44/1.01  cnf(c_1535,plain,
% 2.44/1.01      ( m1_subset_1(k3_yellow_0(sK3),X0)
% 2.44/1.01      | ~ m1_subset_1(k3_yellow_0(sK3),u1_struct_0(sK3))
% 2.44/1.01      | X0 != u1_struct_0(sK3)
% 2.44/1.01      | k3_yellow_0(sK3) != k3_yellow_0(sK3) ),
% 2.44/1.01      inference(instantiation,[status(thm)],[c_1323]) ).
% 2.44/1.01  
% 2.44/1.01  cnf(c_1872,plain,
% 2.44/1.01      ( ~ m1_subset_1(k3_yellow_0(sK3),u1_struct_0(sK3))
% 2.44/1.01      | m1_subset_1(k3_yellow_0(sK3),sK4)
% 2.44/1.01      | k3_yellow_0(sK3) != k3_yellow_0(sK3)
% 2.44/1.01      | sK4 != u1_struct_0(sK3) ),
% 2.44/1.01      inference(instantiation,[status(thm)],[c_1535]) ).
% 2.44/1.01  
% 2.44/1.01  cnf(c_1873,plain,
% 2.44/1.01      ( k3_yellow_0(sK3) != k3_yellow_0(sK3)
% 2.44/1.01      | sK4 != u1_struct_0(sK3)
% 2.44/1.01      | m1_subset_1(k3_yellow_0(sK3),u1_struct_0(sK3)) != iProver_top
% 2.44/1.01      | m1_subset_1(k3_yellow_0(sK3),sK4) = iProver_top ),
% 2.44/1.01      inference(predicate_to_equality,[status(thm)],[c_1872]) ).
% 2.44/1.01  
% 2.44/1.01  cnf(c_2836,plain,
% 2.44/1.01      ( ~ m1_subset_1(k3_yellow_0(X0),sK4)
% 2.44/1.01      | r2_hidden(k3_yellow_0(X0),sK4) ),
% 2.44/1.01      inference(instantiation,[status(thm)],[c_349]) ).
% 2.44/1.01  
% 2.44/1.01  cnf(c_2839,plain,
% 2.44/1.01      ( m1_subset_1(k3_yellow_0(X0),sK4) != iProver_top
% 2.44/1.01      | r2_hidden(k3_yellow_0(X0),sK4) = iProver_top ),
% 2.44/1.01      inference(predicate_to_equality,[status(thm)],[c_2836]) ).
% 2.44/1.01  
% 2.44/1.01  cnf(c_2841,plain,
% 2.44/1.01      ( m1_subset_1(k3_yellow_0(sK3),sK4) != iProver_top
% 2.44/1.01      | r2_hidden(k3_yellow_0(sK3),sK4) = iProver_top ),
% 2.44/1.01      inference(instantiation,[status(thm)],[c_2839]) ).
% 2.44/1.01  
% 2.44/1.01  cnf(c_767,plain,( X0 != X1 | X2 != X1 | X2 = X0 ),theory(equality) ).
% 2.44/1.01  
% 2.44/1.01  cnf(c_1335,plain,
% 2.44/1.01      ( u1_struct_0(sK3) != X0 | sK4 != X0 | sK4 = u1_struct_0(sK3) ),
% 2.44/1.01      inference(instantiation,[status(thm)],[c_767]) ).
% 2.44/1.01  
% 2.44/1.01  cnf(c_3047,plain,
% 2.44/1.01      ( u1_struct_0(sK3) != sK4 | sK4 = u1_struct_0(sK3) | sK4 != sK4 ),
% 2.44/1.01      inference(instantiation,[status(thm)],[c_1335]) ).
% 2.44/1.01  
% 2.44/1.01  cnf(c_3143,plain,
% 2.44/1.01      ( r2_hidden(k3_yellow_0(sK3),sK4) = iProver_top ),
% 2.44/1.01      inference(global_propositional_subsumption,
% 2.44/1.01                [status(thm)],
% 2.44/1.01                [c_1111,c_30,c_33,c_63,c_411,c_781,c_787,c_1385,c_1873,
% 2.44/1.01                 c_2841,c_3047]) ).
% 2.44/1.01  
% 2.44/1.01  cnf(c_1116,plain,
% 2.44/1.01      ( m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(sK3))) = iProver_top ),
% 2.44/1.01      inference(predicate_to_equality,[status(thm)],[c_20]) ).
% 2.44/1.01  
% 2.44/1.01  cnf(c_15,plain,
% 2.44/1.01      ( ~ r1_orders_2(X0,X1,X2)
% 2.44/1.01      | ~ v13_waybel_0(X3,X0)
% 2.44/1.01      | ~ m1_subset_1(X2,u1_struct_0(X0))
% 2.44/1.01      | ~ m1_subset_1(X1,u1_struct_0(X0))
% 2.44/1.01      | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))
% 2.44/1.01      | ~ r2_hidden(X1,X3)
% 2.44/1.01      | r2_hidden(X2,X3)
% 2.44/1.01      | ~ l1_orders_2(X0) ),
% 2.44/1.01      inference(cnf_transformation,[],[f56]) ).
% 2.44/1.01  
% 2.44/1.01  cnf(c_9,plain,
% 2.44/1.01      ( r1_orders_2(X0,k3_yellow_0(X0),X1)
% 2.44/1.01      | ~ m1_subset_1(X1,u1_struct_0(X0))
% 2.44/1.01      | v2_struct_0(X0)
% 2.44/1.01      | ~ v5_orders_2(X0)
% 2.44/1.01      | ~ v1_yellow_0(X0)
% 2.44/1.01      | ~ l1_orders_2(X0) ),
% 2.44/1.01      inference(cnf_transformation,[],[f55]) ).
% 2.44/1.01  
% 2.44/1.01  cnf(c_24,negated_conjecture,
% 2.44/1.01      ( v1_yellow_0(sK3) ),
% 2.44/1.01      inference(cnf_transformation,[],[f66]) ).
% 2.44/1.01  
% 2.44/1.01  cnf(c_363,plain,
% 2.44/1.01      ( r1_orders_2(X0,k3_yellow_0(X0),X1)
% 2.44/1.01      | ~ m1_subset_1(X1,u1_struct_0(X0))
% 2.44/1.01      | v2_struct_0(X0)
% 2.44/1.01      | ~ v5_orders_2(X0)
% 2.44/1.01      | ~ l1_orders_2(X0)
% 2.44/1.01      | sK3 != X0 ),
% 2.44/1.01      inference(resolution_lifted,[status(thm)],[c_9,c_24]) ).
% 2.44/1.01  
% 2.44/1.01  cnf(c_364,plain,
% 2.44/1.01      ( r1_orders_2(sK3,k3_yellow_0(sK3),X0)
% 2.44/1.01      | ~ m1_subset_1(X0,u1_struct_0(sK3))
% 2.44/1.01      | v2_struct_0(sK3)
% 2.44/1.01      | ~ v5_orders_2(sK3)
% 2.44/1.01      | ~ l1_orders_2(sK3) ),
% 2.44/1.01      inference(unflattening,[status(thm)],[c_363]) ).
% 2.44/1.01  
% 2.44/1.01  cnf(c_26,negated_conjecture,
% 2.44/1.01      ( ~ v2_struct_0(sK3) ),
% 2.44/1.01      inference(cnf_transformation,[],[f64]) ).
% 2.44/1.01  
% 2.44/1.01  cnf(c_25,negated_conjecture,
% 2.44/1.01      ( v5_orders_2(sK3) ),
% 2.44/1.01      inference(cnf_transformation,[],[f65]) ).
% 2.44/1.01  
% 2.44/1.01  cnf(c_368,plain,
% 2.44/1.01      ( ~ m1_subset_1(X0,u1_struct_0(sK3))
% 2.44/1.01      | r1_orders_2(sK3,k3_yellow_0(sK3),X0) ),
% 2.44/1.01      inference(global_propositional_subsumption,
% 2.44/1.01                [status(thm)],
% 2.44/1.01                [c_364,c_26,c_25,c_23]) ).
% 2.44/1.01  
% 2.44/1.01  cnf(c_369,plain,
% 2.44/1.01      ( r1_orders_2(sK3,k3_yellow_0(sK3),X0)
% 2.44/1.01      | ~ m1_subset_1(X0,u1_struct_0(sK3)) ),
% 2.44/1.01      inference(renaming,[status(thm)],[c_368]) ).
% 2.44/1.01  
% 2.44/1.01  cnf(c_479,plain,
% 2.44/1.01      ( ~ v13_waybel_0(X0,X1)
% 2.44/1.01      | ~ m1_subset_1(X2,u1_struct_0(X1))
% 2.44/1.01      | ~ m1_subset_1(X3,u1_struct_0(X1))
% 2.44/1.01      | ~ m1_subset_1(X4,u1_struct_0(sK3))
% 2.44/1.01      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 2.44/1.01      | ~ r2_hidden(X2,X0)
% 2.44/1.01      | r2_hidden(X3,X0)
% 2.44/1.01      | ~ l1_orders_2(X1)
% 2.44/1.01      | X4 != X3
% 2.44/1.01      | k3_yellow_0(sK3) != X2
% 2.44/1.01      | sK3 != X1 ),
% 2.44/1.01      inference(resolution_lifted,[status(thm)],[c_15,c_369]) ).
% 2.44/1.01  
% 2.44/1.01  cnf(c_480,plain,
% 2.44/1.01      ( ~ v13_waybel_0(X0,sK3)
% 2.44/1.01      | ~ m1_subset_1(X1,u1_struct_0(sK3))
% 2.44/1.01      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK3)))
% 2.44/1.01      | ~ m1_subset_1(k3_yellow_0(sK3),u1_struct_0(sK3))
% 2.44/1.01      | r2_hidden(X1,X0)
% 2.44/1.01      | ~ r2_hidden(k3_yellow_0(sK3),X0)
% 2.44/1.01      | ~ l1_orders_2(sK3) ),
% 2.44/1.01      inference(unflattening,[status(thm)],[c_479]) ).
% 2.44/1.01  
% 2.44/1.01  cnf(c_62,plain,
% 2.44/1.01      ( m1_subset_1(k3_yellow_0(sK3),u1_struct_0(sK3))
% 2.44/1.01      | ~ l1_orders_2(sK3) ),
% 2.44/1.01      inference(instantiation,[status(thm)],[c_8]) ).
% 2.44/1.01  
% 2.44/1.01  cnf(c_484,plain,
% 2.44/1.01      ( ~ r2_hidden(k3_yellow_0(sK3),X0)
% 2.44/1.01      | r2_hidden(X1,X0)
% 2.44/1.01      | ~ v13_waybel_0(X0,sK3)
% 2.44/1.01      | ~ m1_subset_1(X1,u1_struct_0(sK3))
% 2.44/1.01      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK3))) ),
% 2.44/1.01      inference(global_propositional_subsumption,
% 2.44/1.01                [status(thm)],
% 2.44/1.01                [c_480,c_23,c_62]) ).
% 2.44/1.01  
% 2.44/1.01  cnf(c_485,plain,
% 2.44/1.01      ( ~ v13_waybel_0(X0,sK3)
% 2.44/1.01      | ~ m1_subset_1(X1,u1_struct_0(sK3))
% 2.44/1.01      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK3)))
% 2.44/1.01      | r2_hidden(X1,X0)
% 2.44/1.01      | ~ r2_hidden(k3_yellow_0(sK3),X0) ),
% 2.44/1.01      inference(renaming,[status(thm)],[c_484]) ).
% 2.44/1.01  
% 2.44/1.01  cnf(c_1109,plain,
% 2.44/1.01      ( v13_waybel_0(X0,sK3) != iProver_top
% 2.44/1.01      | m1_subset_1(X1,u1_struct_0(sK3)) != iProver_top
% 2.44/1.01      | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK3))) != iProver_top
% 2.44/1.01      | r2_hidden(X1,X0) = iProver_top
% 2.44/1.01      | r2_hidden(k3_yellow_0(sK3),X0) != iProver_top ),
% 2.44/1.01      inference(predicate_to_equality,[status(thm)],[c_485]) ).
% 2.44/1.01  
% 2.44/1.01  cnf(c_1639,plain,
% 2.44/1.01      ( v13_waybel_0(sK4,sK3) != iProver_top
% 2.44/1.01      | m1_subset_1(X0,u1_struct_0(sK3)) != iProver_top
% 2.44/1.01      | r2_hidden(X0,sK4) = iProver_top
% 2.44/1.01      | r2_hidden(k3_yellow_0(sK3),sK4) != iProver_top ),
% 2.44/1.01      inference(superposition,[status(thm)],[c_1116,c_1109]) ).
% 2.44/1.01  
% 2.44/1.01  cnf(c_21,negated_conjecture,
% 2.44/1.01      ( v13_waybel_0(sK4,sK3) ),
% 2.44/1.01      inference(cnf_transformation,[],[f69]) ).
% 2.44/1.01  
% 2.44/1.01  cnf(c_32,plain,
% 2.44/1.01      ( v13_waybel_0(sK4,sK3) = iProver_top ),
% 2.44/1.01      inference(predicate_to_equality,[status(thm)],[c_21]) ).
% 2.44/1.01  
% 2.44/1.01  cnf(c_1644,plain,
% 2.44/1.01      ( m1_subset_1(X0,u1_struct_0(sK3)) != iProver_top
% 2.44/1.01      | r2_hidden(X0,sK4) = iProver_top
% 2.44/1.01      | r2_hidden(k3_yellow_0(sK3),sK4) != iProver_top ),
% 2.44/1.01      inference(global_propositional_subsumption,
% 2.44/1.01                [status(thm)],
% 2.44/1.01                [c_1639,c_32]) ).
% 2.44/1.01  
% 2.44/1.01  cnf(c_3149,plain,
% 2.44/1.01      ( m1_subset_1(X0,u1_struct_0(sK3)) != iProver_top
% 2.44/1.01      | r2_hidden(X0,sK4) = iProver_top ),
% 2.44/1.01      inference(superposition,[status(thm)],[c_3143,c_1644]) ).
% 2.44/1.01  
% 2.44/1.01  cnf(c_3860,plain,
% 2.44/1.01      ( u1_struct_0(sK3) = sK4
% 2.44/1.01      | r2_hidden(sK0(u1_struct_0(sK3),sK4),sK4) = iProver_top ),
% 2.44/1.01      inference(superposition,[status(thm)],[c_2292,c_3149]) ).
% 2.44/1.01  
% 2.44/1.01  cnf(c_4,plain,
% 2.44/1.01      ( ~ v1_subset_1(k2_subset_1(X0),X0) ),
% 2.44/1.01      inference(cnf_transformation,[],[f50]) ).
% 2.44/1.01  
% 2.44/1.01  cnf(c_19,negated_conjecture,
% 2.44/1.01      ( v1_subset_1(sK4,u1_struct_0(sK3))
% 2.44/1.01      | ~ r2_hidden(k3_yellow_0(sK3),sK4) ),
% 2.44/1.01      inference(cnf_transformation,[],[f71]) ).
% 2.44/1.01  
% 2.44/1.01  cnf(c_193,plain,
% 2.44/1.01      ( v1_subset_1(sK4,u1_struct_0(sK3))
% 2.44/1.01      | ~ r2_hidden(k3_yellow_0(sK3),sK4) ),
% 2.44/1.01      inference(prop_impl,[status(thm)],[c_19]) ).
% 2.44/1.01  
% 2.44/1.01  cnf(c_397,plain,
% 2.44/1.01      ( ~ r2_hidden(k3_yellow_0(sK3),sK4)
% 2.44/1.01      | u1_struct_0(sK3) != X0
% 2.44/1.01      | k2_subset_1(X0) != sK4 ),
% 2.44/1.01      inference(resolution_lifted,[status(thm)],[c_4,c_193]) ).
% 2.44/1.01  
% 2.44/1.01  cnf(c_398,plain,
% 2.44/1.01      ( ~ r2_hidden(k3_yellow_0(sK3),sK4)
% 2.44/1.01      | k2_subset_1(u1_struct_0(sK3)) != sK4 ),
% 2.44/1.01      inference(unflattening,[status(thm)],[c_397]) ).
% 2.44/1.01  
% 2.44/1.01  cnf(c_1112,plain,
% 2.44/1.01      ( k2_subset_1(u1_struct_0(sK3)) != sK4
% 2.44/1.01      | r2_hidden(k3_yellow_0(sK3),sK4) != iProver_top ),
% 2.44/1.01      inference(predicate_to_equality,[status(thm)],[c_398]) ).
% 2.44/1.01  
% 2.44/1.01  cnf(c_2,plain,
% 2.44/1.01      ( k2_subset_1(X0) = X0 ),
% 2.44/1.01      inference(cnf_transformation,[],[f48]) ).
% 2.44/1.01  
% 2.44/1.01  cnf(c_1144,plain,
% 2.44/1.01      ( u1_struct_0(sK3) != sK4
% 2.44/1.01      | r2_hidden(k3_yellow_0(sK3),sK4) != iProver_top ),
% 2.44/1.01      inference(demodulation,[status(thm)],[c_1112,c_2]) ).
% 2.44/1.01  
% 2.44/1.01  cnf(c_5281,plain,
% 2.44/1.01      ( r2_hidden(sK0(u1_struct_0(sK3),sK4),sK4) = iProver_top ),
% 2.44/1.01      inference(global_propositional_subsumption,
% 2.44/1.01                [status(thm)],
% 2.44/1.01                [c_3860,c_30,c_33,c_63,c_411,c_781,c_787,c_1144,c_1385,
% 2.44/1.01                 c_1873,c_2841,c_3047]) ).
% 2.44/1.01  
% 2.44/1.01  cnf(c_0,plain,
% 2.44/1.01      ( ~ r2_hidden(sK0(X0,X1),X1)
% 2.44/1.01      | ~ r2_hidden(sK0(X0,X1),X0)
% 2.44/1.01      | X1 = X0 ),
% 2.44/1.01      inference(cnf_transformation,[],[f47]) ).
% 2.44/1.01  
% 2.44/1.01  cnf(c_1121,plain,
% 2.44/1.01      ( X0 = X1
% 2.44/1.01      | r2_hidden(sK0(X1,X0),X0) != iProver_top
% 2.44/1.01      | r2_hidden(sK0(X1,X0),X1) != iProver_top ),
% 2.44/1.01      inference(predicate_to_equality,[status(thm)],[c_0]) ).
% 2.44/1.01  
% 2.44/1.01  cnf(c_5287,plain,
% 2.44/1.01      ( u1_struct_0(sK3) = sK4
% 2.44/1.01      | r2_hidden(sK0(u1_struct_0(sK3),sK4),u1_struct_0(sK3)) != iProver_top ),
% 2.44/1.01      inference(superposition,[status(thm)],[c_5281,c_1121]) ).
% 2.44/1.01  
% 2.44/1.01  cnf(c_3,plain,
% 2.44/1.01      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
% 2.44/1.01      | ~ r2_hidden(X2,X0)
% 2.44/1.01      | r2_hidden(X2,X1) ),
% 2.44/1.01      inference(cnf_transformation,[],[f49]) ).
% 2.44/1.01  
% 2.44/1.01  cnf(c_1882,plain,
% 2.44/1.01      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
% 2.44/1.01      | ~ r2_hidden(sK0(u1_struct_0(sK3),X0),X0)
% 2.44/1.01      | r2_hidden(sK0(u1_struct_0(sK3),X0),X1) ),
% 2.44/1.01      inference(instantiation,[status(thm)],[c_3]) ).
% 2.44/1.01  
% 2.44/1.01  cnf(c_3416,plain,
% 2.44/1.01      ( ~ m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(sK3)))
% 2.44/1.01      | r2_hidden(sK0(u1_struct_0(sK3),sK4),u1_struct_0(sK3))
% 2.44/1.01      | ~ r2_hidden(sK0(u1_struct_0(sK3),sK4),sK4) ),
% 2.44/1.01      inference(instantiation,[status(thm)],[c_1882]) ).
% 2.44/1.01  
% 2.44/1.01  cnf(c_3417,plain,
% 2.44/1.01      ( m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(sK3))) != iProver_top
% 2.44/1.01      | r2_hidden(sK0(u1_struct_0(sK3),sK4),u1_struct_0(sK3)) = iProver_top
% 2.44/1.01      | r2_hidden(sK0(u1_struct_0(sK3),sK4),sK4) != iProver_top ),
% 2.44/1.01      inference(predicate_to_equality,[status(thm)],[c_3416]) ).
% 2.44/1.01  
% 2.44/1.01  cnf(contradiction,plain,
% 2.44/1.01      ( $false ),
% 2.44/1.01      inference(minisat,
% 2.44/1.01                [status(thm)],
% 2.44/1.01                [c_5287,c_3860,c_3417,c_3143,c_1144,c_33]) ).
% 2.44/1.01  
% 2.44/1.01  
% 2.44/1.01  % SZS output end CNFRefutation for theBenchmark.p
% 2.44/1.01  
% 2.44/1.01  ------                               Statistics
% 2.44/1.01  
% 2.44/1.01  ------ General
% 2.44/1.01  
% 2.44/1.01  abstr_ref_over_cycles:                  0
% 2.44/1.01  abstr_ref_under_cycles:                 0
% 2.44/1.01  gc_basic_clause_elim:                   0
% 2.44/1.01  forced_gc_time:                         0
% 2.44/1.01  parsing_time:                           0.009
% 2.44/1.01  unif_index_cands_time:                  0.
% 2.44/1.01  unif_index_add_time:                    0.
% 2.44/1.01  orderings_time:                         0.
% 2.44/1.01  out_proof_time:                         0.008
% 2.44/1.01  total_time:                             0.184
% 2.44/1.01  num_of_symbols:                         50
% 2.44/1.01  num_of_terms:                           3515
% 2.44/1.01  
% 2.44/1.01  ------ Preprocessing
% 2.44/1.01  
% 2.44/1.01  num_of_splits:                          0
% 2.44/1.01  num_of_split_atoms:                     0
% 2.44/1.01  num_of_reused_defs:                     0
% 2.44/1.01  num_eq_ax_congr_red:                    16
% 2.44/1.01  num_of_sem_filtered_clauses:            1
% 2.44/1.01  num_of_subtypes:                        0
% 2.44/1.01  monotx_restored_types:                  0
% 2.44/1.01  sat_num_of_epr_types:                   0
% 2.44/1.01  sat_num_of_non_cyclic_types:            0
% 2.44/1.01  sat_guarded_non_collapsed_types:        0
% 2.44/1.01  num_pure_diseq_elim:                    0
% 2.44/1.01  simp_replaced_by:                       0
% 2.44/1.01  res_preprocessed:                       110
% 2.44/1.01  prep_upred:                             0
% 2.44/1.01  prep_unflattend:                        22
% 2.44/1.01  smt_new_axioms:                         0
% 2.44/1.01  pred_elim_cands:                        3
% 2.44/1.01  pred_elim:                              7
% 2.44/1.01  pred_elim_cl:                           7
% 2.44/1.01  pred_elim_cycles:                       9
% 2.44/1.01  merged_defs:                            2
% 2.44/1.01  merged_defs_ncl:                        0
% 2.44/1.01  bin_hyper_res:                          2
% 2.44/1.01  prep_cycles:                            4
% 2.44/1.01  pred_elim_time:                         0.016
% 2.44/1.01  splitting_time:                         0.
% 2.44/1.01  sem_filter_time:                        0.
% 2.44/1.01  monotx_time:                            0.001
% 2.44/1.01  subtype_inf_time:                       0.
% 2.44/1.01  
% 2.44/1.01  ------ Problem properties
% 2.44/1.01  
% 2.44/1.01  clauses:                                20
% 2.44/1.01  conjectures:                            2
% 2.44/1.01  epr:                                    3
% 2.44/1.01  horn:                                   14
% 2.44/1.01  ground:                                 6
% 2.44/1.01  unary:                                  4
% 2.44/1.01  binary:                                 5
% 2.44/1.01  lits:                                   52
% 2.44/1.01  lits_eq:                                7
% 2.44/1.01  fd_pure:                                0
% 2.44/1.01  fd_pseudo:                              0
% 2.44/1.01  fd_cond:                                0
% 2.44/1.01  fd_pseudo_cond:                         2
% 2.44/1.01  ac_symbols:                             0
% 2.44/1.01  
% 2.44/1.01  ------ Propositional Solver
% 2.44/1.01  
% 2.44/1.01  prop_solver_calls:                      27
% 2.44/1.01  prop_fast_solver_calls:                 902
% 2.44/1.01  smt_solver_calls:                       0
% 2.44/1.01  smt_fast_solver_calls:                  0
% 2.44/1.01  prop_num_of_clauses:                    1583
% 2.44/1.01  prop_preprocess_simplified:             4836
% 2.44/1.01  prop_fo_subsumed:                       14
% 2.44/1.01  prop_solver_time:                       0.
% 2.44/1.01  smt_solver_time:                        0.
% 2.44/1.01  smt_fast_solver_time:                   0.
% 2.44/1.01  prop_fast_solver_time:                  0.
% 2.44/1.01  prop_unsat_core_time:                   0.
% 2.44/1.01  
% 2.44/1.01  ------ QBF
% 2.44/1.01  
% 2.44/1.01  qbf_q_res:                              0
% 2.44/1.01  qbf_num_tautologies:                    0
% 2.44/1.01  qbf_prep_cycles:                        0
% 2.44/1.01  
% 2.44/1.01  ------ BMC1
% 2.44/1.01  
% 2.44/1.01  bmc1_current_bound:                     -1
% 2.44/1.01  bmc1_last_solved_bound:                 -1
% 2.44/1.01  bmc1_unsat_core_size:                   -1
% 2.44/1.01  bmc1_unsat_core_parents_size:           -1
% 2.44/1.01  bmc1_merge_next_fun:                    0
% 2.44/1.01  bmc1_unsat_core_clauses_time:           0.
% 2.44/1.01  
% 2.44/1.01  ------ Instantiation
% 2.44/1.01  
% 2.44/1.01  inst_num_of_clauses:                    387
% 2.44/1.01  inst_num_in_passive:                    81
% 2.44/1.01  inst_num_in_active:                     206
% 2.44/1.01  inst_num_in_unprocessed:                100
% 2.44/1.01  inst_num_of_loops:                      290
% 2.44/1.01  inst_num_of_learning_restarts:          0
% 2.44/1.01  inst_num_moves_active_passive:          82
% 2.44/1.01  inst_lit_activity:                      0
% 2.44/1.01  inst_lit_activity_moves:                0
% 2.44/1.01  inst_num_tautologies:                   0
% 2.44/1.01  inst_num_prop_implied:                  0
% 2.44/1.01  inst_num_existing_simplified:           0
% 2.44/1.01  inst_num_eq_res_simplified:             0
% 2.44/1.01  inst_num_child_elim:                    0
% 2.44/1.01  inst_num_of_dismatching_blockings:      91
% 2.44/1.01  inst_num_of_non_proper_insts:           388
% 2.44/1.01  inst_num_of_duplicates:                 0
% 2.44/1.01  inst_inst_num_from_inst_to_res:         0
% 2.44/1.01  inst_dismatching_checking_time:         0.
% 2.44/1.01  
% 2.44/1.01  ------ Resolution
% 2.44/1.01  
% 2.44/1.01  res_num_of_clauses:                     0
% 2.44/1.01  res_num_in_passive:                     0
% 2.44/1.01  res_num_in_active:                      0
% 2.44/1.01  res_num_of_loops:                       114
% 2.44/1.01  res_forward_subset_subsumed:            48
% 2.44/1.01  res_backward_subset_subsumed:           0
% 2.44/1.01  res_forward_subsumed:                   0
% 2.44/1.01  res_backward_subsumed:                  0
% 2.44/1.01  res_forward_subsumption_resolution:     2
% 2.44/1.01  res_backward_subsumption_resolution:    0
% 2.44/1.01  res_clause_to_clause_subsumption:       1041
% 2.44/1.01  res_orphan_elimination:                 0
% 2.44/1.01  res_tautology_del:                      33
% 2.44/1.01  res_num_eq_res_simplified:              0
% 2.44/1.01  res_num_sel_changes:                    0
% 2.44/1.01  res_moves_from_active_to_pass:          0
% 2.44/1.01  
% 2.44/1.01  ------ Superposition
% 2.44/1.01  
% 2.44/1.01  sup_time_total:                         0.
% 2.44/1.01  sup_time_generating:                    0.
% 2.44/1.01  sup_time_sim_full:                      0.
% 2.44/1.01  sup_time_sim_immed:                     0.
% 2.44/1.01  
% 2.44/1.01  sup_num_of_clauses:                     130
% 2.44/1.01  sup_num_in_active:                      57
% 2.44/1.01  sup_num_in_passive:                     73
% 2.44/1.01  sup_num_of_loops:                       57
% 2.44/1.01  sup_fw_superposition:                   124
% 2.44/1.01  sup_bw_superposition:                   61
% 2.44/1.01  sup_immediate_simplified:               33
% 2.44/1.01  sup_given_eliminated:                   0
% 2.44/1.01  comparisons_done:                       0
% 2.44/1.01  comparisons_avoided:                    0
% 2.44/1.01  
% 2.44/1.01  ------ Simplifications
% 2.44/1.01  
% 2.44/1.01  
% 2.44/1.01  sim_fw_subset_subsumed:                 4
% 2.44/1.01  sim_bw_subset_subsumed:                 1
% 2.44/1.01  sim_fw_subsumed:                        24
% 2.44/1.01  sim_bw_subsumed:                        10
% 2.44/1.01  sim_fw_subsumption_res:                 0
% 2.44/1.01  sim_bw_subsumption_res:                 0
% 2.44/1.01  sim_tautology_del:                      21
% 2.44/1.01  sim_eq_tautology_del:                   9
% 2.44/1.01  sim_eq_res_simp:                        0
% 2.44/1.01  sim_fw_demodulated:                     2
% 2.44/1.01  sim_bw_demodulated:                     0
% 2.44/1.01  sim_light_normalised:                   1
% 2.44/1.01  sim_joinable_taut:                      0
% 2.44/1.01  sim_joinable_simp:                      0
% 2.44/1.01  sim_ac_normalised:                      0
% 2.44/1.01  sim_smt_subsumption:                    0
% 2.44/1.01  
%------------------------------------------------------------------------------
