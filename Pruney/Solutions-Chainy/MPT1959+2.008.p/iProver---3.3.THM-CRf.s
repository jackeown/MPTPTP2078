%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n007.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:28:25 EST 2020

% Result     : Theorem 19.32s
% Output     : CNFRefutation 19.32s
% Verified   : 
% Statistics : Number of formulae       :  284 (3198 expanded)
%              Number of clauses        :  179 ( 837 expanded)
%              Number of leaves         :   28 ( 604 expanded)
%              Depth                    :   28
%              Number of atoms          : 1102 (24149 expanded)
%              Number of equality atoms :  275 (1079 expanded)
%              Maximal formula depth    :   14 (   5 average)
%              Maximal clause size      :   22 (   3 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f1,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
    <=> ! [X2] :
          ( r2_hidden(X2,X0)
         => r2_hidden(X2,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f22,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
          | ~ r2_hidden(X2,X0) ) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f42,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ? [X2] :
            ( ~ r2_hidden(X2,X1)
            & r2_hidden(X2,X0) ) )
      & ( ! [X2] :
            ( r2_hidden(X2,X1)
            | ~ r2_hidden(X2,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(nnf_transformation,[],[f22])).

fof(f43,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ? [X2] :
            ( ~ r2_hidden(X2,X1)
            & r2_hidden(X2,X0) ) )
      & ( ! [X3] :
            ( r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(rectify,[],[f42])).

fof(f44,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ~ r2_hidden(X2,X1)
          & r2_hidden(X2,X0) )
     => ( ~ r2_hidden(sK0(X0,X1),X1)
        & r2_hidden(sK0(X0,X1),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f45,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ( ~ r2_hidden(sK0(X0,X1),X1)
          & r2_hidden(sK0(X0,X1),X0) ) )
      & ( ! [X3] :
            ( r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f43,f44])).

fof(f70,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | r2_hidden(sK0(X0,X1),X0) ) ),
    inference(cnf_transformation,[],[f45])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
     => m1_subset_1(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f23,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X0,X1)
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f76,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X0,X1)
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f10,axiom,(
    ! [X0] :
      ( l1_orders_2(X0)
     => k3_yellow_0(X0) = k1_yellow_0(X0,k1_xboole_0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f31,plain,(
    ! [X0] :
      ( k3_yellow_0(X0) = k1_yellow_0(X0,k1_xboole_0)
      | ~ l1_orders_2(X0) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f86,plain,(
    ! [X0] :
      ( k3_yellow_0(X0) = k1_yellow_0(X0,k1_xboole_0)
      | ~ l1_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f16,conjecture,(
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

fof(f17,negated_conjecture,(
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
    inference(negated_conjecture,[],[f16])).

fof(f18,plain,(
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
    inference(pure_predicate_removal,[],[f17])).

fof(f19,plain,(
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
    inference(pure_predicate_removal,[],[f18])).

fof(f20,plain,(
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
    inference(pure_predicate_removal,[],[f19])).

fof(f40,plain,(
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
    inference(ennf_transformation,[],[f20])).

fof(f41,plain,(
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
    inference(flattening,[],[f40])).

fof(f64,plain,(
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
    inference(nnf_transformation,[],[f41])).

fof(f65,plain,(
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
    inference(flattening,[],[f64])).

fof(f67,plain,(
    ! [X0] :
      ( ? [X1] :
          ( ( r2_hidden(k3_yellow_0(X0),X1)
            | ~ v1_subset_1(X1,u1_struct_0(X0)) )
          & ( ~ r2_hidden(k3_yellow_0(X0),X1)
            | v1_subset_1(X1,u1_struct_0(X0)) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
          & v13_waybel_0(X1,X0)
          & ~ v1_xboole_0(X1) )
     => ( ( r2_hidden(k3_yellow_0(X0),sK6)
          | ~ v1_subset_1(sK6,u1_struct_0(X0)) )
        & ( ~ r2_hidden(k3_yellow_0(X0),sK6)
          | v1_subset_1(sK6,u1_struct_0(X0)) )
        & m1_subset_1(sK6,k1_zfmisc_1(u1_struct_0(X0)))
        & v13_waybel_0(sK6,X0)
        & ~ v1_xboole_0(sK6) ) ) ),
    introduced(choice_axiom,[])).

fof(f66,plain,
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
          ( ( r2_hidden(k3_yellow_0(sK5),X1)
            | ~ v1_subset_1(X1,u1_struct_0(sK5)) )
          & ( ~ r2_hidden(k3_yellow_0(sK5),X1)
            | v1_subset_1(X1,u1_struct_0(sK5)) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK5)))
          & v13_waybel_0(X1,sK5)
          & ~ v1_xboole_0(X1) )
      & l1_orders_2(sK5)
      & v1_yellow_0(sK5)
      & v5_orders_2(sK5)
      & ~ v2_struct_0(sK5) ) ),
    introduced(choice_axiom,[])).

fof(f68,plain,
    ( ( r2_hidden(k3_yellow_0(sK5),sK6)
      | ~ v1_subset_1(sK6,u1_struct_0(sK5)) )
    & ( ~ r2_hidden(k3_yellow_0(sK5),sK6)
      | v1_subset_1(sK6,u1_struct_0(sK5)) )
    & m1_subset_1(sK6,k1_zfmisc_1(u1_struct_0(sK5)))
    & v13_waybel_0(sK6,sK5)
    & ~ v1_xboole_0(sK6)
    & l1_orders_2(sK5)
    & v1_yellow_0(sK5)
    & v5_orders_2(sK5)
    & ~ v2_struct_0(sK5) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK5,sK6])],[f65,f67,f66])).

fof(f105,plain,(
    l1_orders_2(sK5) ),
    inference(cnf_transformation,[],[f68])).

fof(f12,axiom,(
    ! [X0,X1] :
      ( l1_orders_2(X0)
     => m1_subset_1(k1_yellow_0(X0,X1),u1_struct_0(X0)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f34,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k1_yellow_0(X0,X1),u1_struct_0(X0))
      | ~ l1_orders_2(X0) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f92,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k1_yellow_0(X0,X1),u1_struct_0(X0))
      | ~ l1_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f34])).

fof(f5,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,X1)
     => ( r2_hidden(X0,X1)
        | v1_xboole_0(X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f24,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
      | v1_xboole_0(X1)
      | ~ m1_subset_1(X0,X1) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f25,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
      | v1_xboole_0(X1)
      | ~ m1_subset_1(X0,X1) ) ),
    inference(flattening,[],[f24])).

fof(f77,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
      | v1_xboole_0(X1)
      | ~ m1_subset_1(X0,X1) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f106,plain,(
    ~ v1_xboole_0(sK6) ),
    inference(cnf_transformation,[],[f68])).

fof(f108,plain,(
    m1_subset_1(sK6,k1_zfmisc_1(u1_struct_0(sK5))) ),
    inference(cnf_transformation,[],[f68])).

fof(f15,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => ( v1_subset_1(X1,X0)
      <=> X0 != X1 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f39,plain,(
    ! [X0,X1] :
      ( ( v1_subset_1(X1,X0)
      <=> X0 != X1 )
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f15])).

fof(f63,plain,(
    ! [X0,X1] :
      ( ( ( v1_subset_1(X1,X0)
          | X0 = X1 )
        & ( X0 != X1
          | ~ v1_subset_1(X1,X0) ) )
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(nnf_transformation,[],[f39])).

fof(f101,plain,(
    ! [X0,X1] :
      ( v1_subset_1(X1,X0)
      | X0 = X1
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f63])).

fof(f6,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f48,plain,(
    ! [X0,X1] :
      ( ( m1_subset_1(X0,k1_zfmisc_1(X1))
        | ~ r1_tarski(X0,X1) )
      & ( r1_tarski(X0,X1)
        | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ) ) ),
    inference(nnf_transformation,[],[f6])).

fof(f79,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f48])).

fof(f110,plain,
    ( r2_hidden(k3_yellow_0(sK5),sK6)
    | ~ v1_subset_1(sK6,u1_struct_0(sK5)) ),
    inference(cnf_transformation,[],[f68])).

fof(f78,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ) ),
    inference(cnf_transformation,[],[f48])).

fof(f8,axiom,(
    ! [X0,X1,X2] :
      ~ ( v1_xboole_0(X2)
        & m1_subset_1(X1,k1_zfmisc_1(X2))
        & r2_hidden(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f28,plain,(
    ! [X0,X1,X2] :
      ( ~ v1_xboole_0(X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f81,plain,(
    ! [X2,X0,X1] :
      ( ~ v1_xboole_0(X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f69,plain,(
    ! [X0,X3,X1] :
      ( r2_hidden(X3,X1)
      | ~ r2_hidden(X3,X0)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f45])).

fof(f14,axiom,(
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

fof(f37,plain,(
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
    inference(ennf_transformation,[],[f14])).

fof(f38,plain,(
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
    inference(flattening,[],[f37])).

fof(f58,plain,(
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
    inference(nnf_transformation,[],[f38])).

fof(f59,plain,(
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
    inference(rectify,[],[f58])).

fof(f61,plain,(
    ! [X2,X1,X0] :
      ( ? [X3] :
          ( ~ r2_hidden(X3,X1)
          & r1_orders_2(X0,X2,X3)
          & r2_hidden(X2,X1)
          & m1_subset_1(X3,u1_struct_0(X0)) )
     => ( ~ r2_hidden(sK4(X0,X1),X1)
        & r1_orders_2(X0,X2,sK4(X0,X1))
        & r2_hidden(X2,X1)
        & m1_subset_1(sK4(X0,X1),u1_struct_0(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f60,plain,(
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
            & r1_orders_2(X0,sK3(X0,X1),X3)
            & r2_hidden(sK3(X0,X1),X1)
            & m1_subset_1(X3,u1_struct_0(X0)) )
        & m1_subset_1(sK3(X0,X1),u1_struct_0(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f62,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ( v13_waybel_0(X1,X0)
              | ( ~ r2_hidden(sK4(X0,X1),X1)
                & r1_orders_2(X0,sK3(X0,X1),sK4(X0,X1))
                & r2_hidden(sK3(X0,X1),X1)
                & m1_subset_1(sK4(X0,X1),u1_struct_0(X0))
                & m1_subset_1(sK3(X0,X1),u1_struct_0(X0)) ) )
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
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3,sK4])],[f59,f61,f60])).

fof(f97,plain,(
    ! [X0,X1] :
      ( v13_waybel_0(X1,X0)
      | r2_hidden(sK3(X0,X1),X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f62])).

fof(f95,plain,(
    ! [X0,X1] :
      ( v13_waybel_0(X1,X0)
      | m1_subset_1(sK3(X0,X1),u1_struct_0(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f62])).

fof(f9,axiom,(
    ! [X0] :
      ( l1_orders_2(X0)
     => ! [X1,X2] :
          ( m1_subset_1(X2,u1_struct_0(X0))
         => ( r2_lattice3(X0,X1,X2)
          <=> ! [X3] :
                ( m1_subset_1(X3,u1_struct_0(X0))
               => ( r2_hidden(X3,X1)
                 => r1_orders_2(X0,X3,X2) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f29,plain,(
    ! [X0] :
      ( ! [X1,X2] :
          ( ( r2_lattice3(X0,X1,X2)
          <=> ! [X3] :
                ( r1_orders_2(X0,X3,X2)
                | ~ r2_hidden(X3,X1)
                | ~ m1_subset_1(X3,u1_struct_0(X0)) ) )
          | ~ m1_subset_1(X2,u1_struct_0(X0)) )
      | ~ l1_orders_2(X0) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f30,plain,(
    ! [X0] :
      ( ! [X1,X2] :
          ( ( r2_lattice3(X0,X1,X2)
          <=> ! [X3] :
                ( r1_orders_2(X0,X3,X2)
                | ~ r2_hidden(X3,X1)
                | ~ m1_subset_1(X3,u1_struct_0(X0)) ) )
          | ~ m1_subset_1(X2,u1_struct_0(X0)) )
      | ~ l1_orders_2(X0) ) ),
    inference(flattening,[],[f29])).

fof(f49,plain,(
    ! [X0] :
      ( ! [X1,X2] :
          ( ( ( r2_lattice3(X0,X1,X2)
              | ? [X3] :
                  ( ~ r1_orders_2(X0,X3,X2)
                  & r2_hidden(X3,X1)
                  & m1_subset_1(X3,u1_struct_0(X0)) ) )
            & ( ! [X3] :
                  ( r1_orders_2(X0,X3,X2)
                  | ~ r2_hidden(X3,X1)
                  | ~ m1_subset_1(X3,u1_struct_0(X0)) )
              | ~ r2_lattice3(X0,X1,X2) ) )
          | ~ m1_subset_1(X2,u1_struct_0(X0)) )
      | ~ l1_orders_2(X0) ) ),
    inference(nnf_transformation,[],[f30])).

fof(f50,plain,(
    ! [X0] :
      ( ! [X1,X2] :
          ( ( ( r2_lattice3(X0,X1,X2)
              | ? [X3] :
                  ( ~ r1_orders_2(X0,X3,X2)
                  & r2_hidden(X3,X1)
                  & m1_subset_1(X3,u1_struct_0(X0)) ) )
            & ( ! [X4] :
                  ( r1_orders_2(X0,X4,X2)
                  | ~ r2_hidden(X4,X1)
                  | ~ m1_subset_1(X4,u1_struct_0(X0)) )
              | ~ r2_lattice3(X0,X1,X2) ) )
          | ~ m1_subset_1(X2,u1_struct_0(X0)) )
      | ~ l1_orders_2(X0) ) ),
    inference(rectify,[],[f49])).

fof(f51,plain,(
    ! [X2,X1,X0] :
      ( ? [X3] :
          ( ~ r1_orders_2(X0,X3,X2)
          & r2_hidden(X3,X1)
          & m1_subset_1(X3,u1_struct_0(X0)) )
     => ( ~ r1_orders_2(X0,sK1(X0,X1,X2),X2)
        & r2_hidden(sK1(X0,X1,X2),X1)
        & m1_subset_1(sK1(X0,X1,X2),u1_struct_0(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f52,plain,(
    ! [X0] :
      ( ! [X1,X2] :
          ( ( ( r2_lattice3(X0,X1,X2)
              | ( ~ r1_orders_2(X0,sK1(X0,X1,X2),X2)
                & r2_hidden(sK1(X0,X1,X2),X1)
                & m1_subset_1(sK1(X0,X1,X2),u1_struct_0(X0)) ) )
            & ( ! [X4] :
                  ( r1_orders_2(X0,X4,X2)
                  | ~ r2_hidden(X4,X1)
                  | ~ m1_subset_1(X4,u1_struct_0(X0)) )
              | ~ r2_lattice3(X0,X1,X2) ) )
          | ~ m1_subset_1(X2,u1_struct_0(X0)) )
      | ~ l1_orders_2(X0) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1])],[f50,f51])).

fof(f82,plain,(
    ! [X4,X2,X0,X1] :
      ( r1_orders_2(X0,X4,X2)
      | ~ r2_hidden(X4,X1)
      | ~ m1_subset_1(X4,u1_struct_0(X0))
      | ~ r2_lattice3(X0,X1,X2)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ l1_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f52])).

fof(f94,plain,(
    ! [X4,X0,X5,X1] :
      ( r2_hidden(X5,X1)
      | ~ r1_orders_2(X0,X4,X5)
      | ~ r2_hidden(X4,X1)
      | ~ m1_subset_1(X5,u1_struct_0(X0))
      | ~ m1_subset_1(X4,u1_struct_0(X0))
      | ~ v13_waybel_0(X1,X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f62])).

fof(f7,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(X2))
        & r2_hidden(X0,X1) )
     => m1_subset_1(X0,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f26,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X0,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f27,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X0,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(flattening,[],[f26])).

fof(f80,plain,(
    ! [X2,X0,X1] :
      ( m1_subset_1(X0,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f107,plain,(
    v13_waybel_0(sK6,sK5) ),
    inference(cnf_transformation,[],[f68])).

fof(f100,plain,(
    ! [X0,X1] :
      ( X0 != X1
      | ~ v1_subset_1(X1,X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f63])).

fof(f115,plain,(
    ! [X1] :
      ( ~ v1_subset_1(X1,X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X1)) ) ),
    inference(equality_resolution,[],[f100])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( X0 = X1
    <=> ( r1_tarski(X1,X0)
        & r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f46,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(nnf_transformation,[],[f3])).

fof(f47,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(flattening,[],[f46])).

fof(f73,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | X0 != X1 ) ),
    inference(cnf_transformation,[],[f47])).

fof(f112,plain,(
    ! [X1] : r1_tarski(X1,X1) ),
    inference(equality_resolution,[],[f73])).

fof(f11,axiom,(
    ! [X0] :
      ( l1_orders_2(X0)
     => ! [X1,X2] :
          ( m1_subset_1(X2,u1_struct_0(X0))
         => ( r1_yellow_0(X0,X1)
           => ( k1_yellow_0(X0,X1) = X2
            <=> ( ! [X3] :
                    ( m1_subset_1(X3,u1_struct_0(X0))
                   => ( r2_lattice3(X0,X1,X3)
                     => r1_orders_2(X0,X2,X3) ) )
                & r2_lattice3(X0,X1,X2) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f32,plain,(
    ! [X0] :
      ( ! [X1,X2] :
          ( ( k1_yellow_0(X0,X1) = X2
          <=> ( ! [X3] :
                  ( r1_orders_2(X0,X2,X3)
                  | ~ r2_lattice3(X0,X1,X3)
                  | ~ m1_subset_1(X3,u1_struct_0(X0)) )
              & r2_lattice3(X0,X1,X2) ) )
          | ~ r1_yellow_0(X0,X1)
          | ~ m1_subset_1(X2,u1_struct_0(X0)) )
      | ~ l1_orders_2(X0) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f33,plain,(
    ! [X0] :
      ( ! [X1,X2] :
          ( ( k1_yellow_0(X0,X1) = X2
          <=> ( ! [X3] :
                  ( r1_orders_2(X0,X2,X3)
                  | ~ r2_lattice3(X0,X1,X3)
                  | ~ m1_subset_1(X3,u1_struct_0(X0)) )
              & r2_lattice3(X0,X1,X2) ) )
          | ~ r1_yellow_0(X0,X1)
          | ~ m1_subset_1(X2,u1_struct_0(X0)) )
      | ~ l1_orders_2(X0) ) ),
    inference(flattening,[],[f32])).

fof(f53,plain,(
    ! [X0] :
      ( ! [X1,X2] :
          ( ( ( k1_yellow_0(X0,X1) = X2
              | ? [X3] :
                  ( ~ r1_orders_2(X0,X2,X3)
                  & r2_lattice3(X0,X1,X3)
                  & m1_subset_1(X3,u1_struct_0(X0)) )
              | ~ r2_lattice3(X0,X1,X2) )
            & ( ( ! [X3] :
                    ( r1_orders_2(X0,X2,X3)
                    | ~ r2_lattice3(X0,X1,X3)
                    | ~ m1_subset_1(X3,u1_struct_0(X0)) )
                & r2_lattice3(X0,X1,X2) )
              | k1_yellow_0(X0,X1) != X2 ) )
          | ~ r1_yellow_0(X0,X1)
          | ~ m1_subset_1(X2,u1_struct_0(X0)) )
      | ~ l1_orders_2(X0) ) ),
    inference(nnf_transformation,[],[f33])).

fof(f54,plain,(
    ! [X0] :
      ( ! [X1,X2] :
          ( ( ( k1_yellow_0(X0,X1) = X2
              | ? [X3] :
                  ( ~ r1_orders_2(X0,X2,X3)
                  & r2_lattice3(X0,X1,X3)
                  & m1_subset_1(X3,u1_struct_0(X0)) )
              | ~ r2_lattice3(X0,X1,X2) )
            & ( ( ! [X3] :
                    ( r1_orders_2(X0,X2,X3)
                    | ~ r2_lattice3(X0,X1,X3)
                    | ~ m1_subset_1(X3,u1_struct_0(X0)) )
                & r2_lattice3(X0,X1,X2) )
              | k1_yellow_0(X0,X1) != X2 ) )
          | ~ r1_yellow_0(X0,X1)
          | ~ m1_subset_1(X2,u1_struct_0(X0)) )
      | ~ l1_orders_2(X0) ) ),
    inference(flattening,[],[f53])).

fof(f55,plain,(
    ! [X0] :
      ( ! [X1,X2] :
          ( ( ( k1_yellow_0(X0,X1) = X2
              | ? [X3] :
                  ( ~ r1_orders_2(X0,X2,X3)
                  & r2_lattice3(X0,X1,X3)
                  & m1_subset_1(X3,u1_struct_0(X0)) )
              | ~ r2_lattice3(X0,X1,X2) )
            & ( ( ! [X4] :
                    ( r1_orders_2(X0,X2,X4)
                    | ~ r2_lattice3(X0,X1,X4)
                    | ~ m1_subset_1(X4,u1_struct_0(X0)) )
                & r2_lattice3(X0,X1,X2) )
              | k1_yellow_0(X0,X1) != X2 ) )
          | ~ r1_yellow_0(X0,X1)
          | ~ m1_subset_1(X2,u1_struct_0(X0)) )
      | ~ l1_orders_2(X0) ) ),
    inference(rectify,[],[f54])).

fof(f56,plain,(
    ! [X2,X1,X0] :
      ( ? [X3] :
          ( ~ r1_orders_2(X0,X2,X3)
          & r2_lattice3(X0,X1,X3)
          & m1_subset_1(X3,u1_struct_0(X0)) )
     => ( ~ r1_orders_2(X0,X2,sK2(X0,X1,X2))
        & r2_lattice3(X0,X1,sK2(X0,X1,X2))
        & m1_subset_1(sK2(X0,X1,X2),u1_struct_0(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f57,plain,(
    ! [X0] :
      ( ! [X1,X2] :
          ( ( ( k1_yellow_0(X0,X1) = X2
              | ( ~ r1_orders_2(X0,X2,sK2(X0,X1,X2))
                & r2_lattice3(X0,X1,sK2(X0,X1,X2))
                & m1_subset_1(sK2(X0,X1,X2),u1_struct_0(X0)) )
              | ~ r2_lattice3(X0,X1,X2) )
            & ( ( ! [X4] :
                    ( r1_orders_2(X0,X2,X4)
                    | ~ r2_lattice3(X0,X1,X4)
                    | ~ m1_subset_1(X4,u1_struct_0(X0)) )
                & r2_lattice3(X0,X1,X2) )
              | k1_yellow_0(X0,X1) != X2 ) )
          | ~ r1_yellow_0(X0,X1)
          | ~ m1_subset_1(X2,u1_struct_0(X0)) )
      | ~ l1_orders_2(X0) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2])],[f55,f56])).

fof(f88,plain,(
    ! [X4,X2,X0,X1] :
      ( r1_orders_2(X0,X2,X4)
      | ~ r2_lattice3(X0,X1,X4)
      | ~ m1_subset_1(X4,u1_struct_0(X0))
      | k1_yellow_0(X0,X1) != X2
      | ~ r1_yellow_0(X0,X1)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ l1_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f57])).

fof(f113,plain,(
    ! [X4,X0,X1] :
      ( r1_orders_2(X0,k1_yellow_0(X0,X1),X4)
      | ~ r2_lattice3(X0,X1,X4)
      | ~ m1_subset_1(X4,u1_struct_0(X0))
      | ~ r1_yellow_0(X0,X1)
      | ~ m1_subset_1(k1_yellow_0(X0,X1),u1_struct_0(X0))
      | ~ l1_orders_2(X0) ) ),
    inference(equality_resolution,[],[f88])).

fof(f13,axiom,(
    ! [X0] :
      ( ( l1_orders_2(X0)
        & v1_yellow_0(X0)
        & v5_orders_2(X0)
        & ~ v2_struct_0(X0) )
     => ( r2_yellow_0(X0,u1_struct_0(X0))
        & r1_yellow_0(X0,k1_xboole_0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f21,plain,(
    ! [X0] :
      ( ( l1_orders_2(X0)
        & v1_yellow_0(X0)
        & v5_orders_2(X0)
        & ~ v2_struct_0(X0) )
     => r1_yellow_0(X0,k1_xboole_0) ) ),
    inference(pure_predicate_removal,[],[f13])).

fof(f35,plain,(
    ! [X0] :
      ( r1_yellow_0(X0,k1_xboole_0)
      | ~ l1_orders_2(X0)
      | ~ v1_yellow_0(X0)
      | ~ v5_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f21])).

fof(f36,plain,(
    ! [X0] :
      ( r1_yellow_0(X0,k1_xboole_0)
      | ~ l1_orders_2(X0)
      | ~ v1_yellow_0(X0)
      | ~ v5_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f35])).

fof(f93,plain,(
    ! [X0] :
      ( r1_yellow_0(X0,k1_xboole_0)
      | ~ l1_orders_2(X0)
      | ~ v1_yellow_0(X0)
      | ~ v5_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f36])).

fof(f104,plain,(
    v1_yellow_0(sK5) ),
    inference(cnf_transformation,[],[f68])).

fof(f102,plain,(
    ~ v2_struct_0(sK5) ),
    inference(cnf_transformation,[],[f68])).

fof(f103,plain,(
    v5_orders_2(sK5) ),
    inference(cnf_transformation,[],[f68])).

fof(f84,plain,(
    ! [X2,X0,X1] :
      ( r2_lattice3(X0,X1,X2)
      | r2_hidden(sK1(X0,X1,X2),X1)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ l1_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f52])).

fof(f87,plain,(
    ! [X2,X0,X1] :
      ( r2_lattice3(X0,X1,X2)
      | k1_yellow_0(X0,X1) != X2
      | ~ r1_yellow_0(X0,X1)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ l1_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f57])).

fof(f114,plain,(
    ! [X0,X1] :
      ( r2_lattice3(X0,X1,k1_yellow_0(X0,X1))
      | ~ r1_yellow_0(X0,X1)
      | ~ m1_subset_1(k1_yellow_0(X0,X1),u1_struct_0(X0))
      | ~ l1_orders_2(X0) ) ),
    inference(equality_resolution,[],[f87])).

fof(f2,axiom,(
    v1_xboole_0(k1_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f72,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(cnf_transformation,[],[f2])).

fof(f71,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | ~ r2_hidden(sK0(X0,X1),X1) ) ),
    inference(cnf_transformation,[],[f45])).

fof(f75,plain,(
    ! [X0,X1] :
      ( X0 = X1
      | ~ r1_tarski(X1,X0)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f47])).

fof(f109,plain,
    ( ~ r2_hidden(k3_yellow_0(sK5),sK6)
    | v1_subset_1(sK6,u1_struct_0(sK5)) ),
    inference(cnf_transformation,[],[f68])).

cnf(c_1,plain,
    ( r2_hidden(sK0(X0,X1),X0)
    | r1_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f70])).

cnf(c_2946,plain,
    ( r2_hidden(sK0(X0,X1),X0) = iProver_top
    | r1_tarski(X0,X1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1])).

cnf(c_7,plain,
    ( m1_subset_1(X0,X1)
    | ~ r2_hidden(X0,X1) ),
    inference(cnf_transformation,[],[f76])).

cnf(c_2941,plain,
    ( m1_subset_1(X0,X1) = iProver_top
    | r2_hidden(X0,X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_7])).

cnf(c_3965,plain,
    ( m1_subset_1(sK0(X0,X1),X0) = iProver_top
    | r1_tarski(X0,X1) = iProver_top ),
    inference(superposition,[status(thm)],[c_2946,c_2941])).

cnf(c_17,plain,
    ( ~ l1_orders_2(X0)
    | k1_yellow_0(X0,k1_xboole_0) = k3_yellow_0(X0) ),
    inference(cnf_transformation,[],[f86])).

cnf(c_38,negated_conjecture,
    ( l1_orders_2(sK5) ),
    inference(cnf_transformation,[],[f105])).

cnf(c_839,plain,
    ( k1_yellow_0(X0,k1_xboole_0) = k3_yellow_0(X0)
    | sK5 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_17,c_38])).

cnf(c_840,plain,
    ( k1_yellow_0(sK5,k1_xboole_0) = k3_yellow_0(sK5) ),
    inference(unflattening,[status(thm)],[c_839])).

cnf(c_23,plain,
    ( m1_subset_1(k1_yellow_0(X0,X1),u1_struct_0(X0))
    | ~ l1_orders_2(X0) ),
    inference(cnf_transformation,[],[f92])).

cnf(c_830,plain,
    ( m1_subset_1(k1_yellow_0(X0,X1),u1_struct_0(X0))
    | sK5 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_23,c_38])).

cnf(c_831,plain,
    ( m1_subset_1(k1_yellow_0(sK5,X0),u1_struct_0(sK5)) ),
    inference(unflattening,[status(thm)],[c_830])).

cnf(c_2923,plain,
    ( m1_subset_1(k1_yellow_0(sK5,X0),u1_struct_0(sK5)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_831])).

cnf(c_8,plain,
    ( ~ m1_subset_1(X0,X1)
    | r2_hidden(X0,X1)
    | v1_xboole_0(X1) ),
    inference(cnf_transformation,[],[f77])).

cnf(c_2940,plain,
    ( m1_subset_1(X0,X1) != iProver_top
    | r2_hidden(X0,X1) = iProver_top
    | v1_xboole_0(X1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_8])).

cnf(c_4030,plain,
    ( r2_hidden(k1_yellow_0(sK5,X0),u1_struct_0(sK5)) = iProver_top
    | v1_xboole_0(u1_struct_0(sK5)) = iProver_top ),
    inference(superposition,[status(thm)],[c_2923,c_2940])).

cnf(c_37,negated_conjecture,
    ( ~ v1_xboole_0(sK6) ),
    inference(cnf_transformation,[],[f106])).

cnf(c_46,plain,
    ( v1_xboole_0(sK6) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_37])).

cnf(c_35,negated_conjecture,
    ( m1_subset_1(sK6,k1_zfmisc_1(u1_struct_0(sK5))) ),
    inference(cnf_transformation,[],[f108])).

cnf(c_48,plain,
    ( m1_subset_1(sK6,k1_zfmisc_1(u1_struct_0(sK5))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_35])).

cnf(c_31,plain,
    ( v1_subset_1(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | X0 = X1 ),
    inference(cnf_transformation,[],[f101])).

cnf(c_9,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(X1))
    | ~ r1_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f79])).

cnf(c_329,plain,
    ( ~ r1_tarski(X0,X1)
    | m1_subset_1(X0,k1_zfmisc_1(X1)) ),
    inference(prop_impl,[status(thm)],[c_9])).

cnf(c_330,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(X1))
    | ~ r1_tarski(X0,X1) ),
    inference(renaming,[status(thm)],[c_329])).

cnf(c_415,plain,
    ( v1_subset_1(X0,X1)
    | ~ r1_tarski(X0,X1)
    | X0 = X1 ),
    inference(bin_hyper_res,[status(thm)],[c_31,c_330])).

cnf(c_33,negated_conjecture,
    ( ~ v1_subset_1(sK6,u1_struct_0(sK5))
    | r2_hidden(k3_yellow_0(sK5),sK6) ),
    inference(cnf_transformation,[],[f110])).

cnf(c_333,plain,
    ( ~ v1_subset_1(sK6,u1_struct_0(sK5))
    | r2_hidden(k3_yellow_0(sK5),sK6) ),
    inference(prop_impl,[status(thm)],[c_33])).

cnf(c_631,plain,
    ( r2_hidden(k3_yellow_0(sK5),sK6)
    | ~ r1_tarski(X0,X1)
    | X1 = X0
    | u1_struct_0(sK5) != X1
    | sK6 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_415,c_333])).

cnf(c_632,plain,
    ( r2_hidden(k3_yellow_0(sK5),sK6)
    | ~ r1_tarski(sK6,u1_struct_0(sK5))
    | u1_struct_0(sK5) = sK6 ),
    inference(unflattening,[status(thm)],[c_631])).

cnf(c_633,plain,
    ( u1_struct_0(sK5) = sK6
    | r2_hidden(k3_yellow_0(sK5),sK6) = iProver_top
    | r1_tarski(sK6,u1_struct_0(sK5)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_632])).

cnf(c_10,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | r1_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f78])).

cnf(c_3264,plain,
    ( ~ m1_subset_1(sK6,k1_zfmisc_1(u1_struct_0(sK5)))
    | r1_tarski(sK6,u1_struct_0(sK5)) ),
    inference(instantiation,[status(thm)],[c_10])).

cnf(c_3265,plain,
    ( m1_subset_1(sK6,k1_zfmisc_1(u1_struct_0(sK5))) != iProver_top
    | r1_tarski(sK6,u1_struct_0(sK5)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3264])).

cnf(c_2133,plain,
    ( X0 = X0 ),
    theory(equality)).

cnf(c_3345,plain,
    ( sK6 = sK6 ),
    inference(instantiation,[status(thm)],[c_2133])).

cnf(c_2137,plain,
    ( ~ v1_xboole_0(X0)
    | v1_xboole_0(X1)
    | X1 != X0 ),
    theory(equality)).

cnf(c_3409,plain,
    ( v1_xboole_0(X0)
    | ~ v1_xboole_0(u1_struct_0(sK5))
    | X0 != u1_struct_0(sK5) ),
    inference(instantiation,[status(thm)],[c_2137])).

cnf(c_4125,plain,
    ( ~ v1_xboole_0(u1_struct_0(sK5))
    | v1_xboole_0(sK6)
    | sK6 != u1_struct_0(sK5) ),
    inference(instantiation,[status(thm)],[c_3409])).

cnf(c_4126,plain,
    ( sK6 != u1_struct_0(sK5)
    | v1_xboole_0(u1_struct_0(sK5)) != iProver_top
    | v1_xboole_0(sK6) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_4125])).

cnf(c_2134,plain,
    ( X0 != X1
    | X2 != X1
    | X2 = X0 ),
    theory(equality)).

cnf(c_3536,plain,
    ( X0 != X1
    | sK6 != X1
    | sK6 = X0 ),
    inference(instantiation,[status(thm)],[c_2134])).

cnf(c_4188,plain,
    ( X0 != sK6
    | sK6 = X0
    | sK6 != sK6 ),
    inference(instantiation,[status(thm)],[c_3536])).

cnf(c_4571,plain,
    ( u1_struct_0(sK5) != sK6
    | sK6 = u1_struct_0(sK5)
    | sK6 != sK6 ),
    inference(instantiation,[status(thm)],[c_4188])).

cnf(c_12,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | ~ r2_hidden(X2,X0)
    | ~ v1_xboole_0(X1) ),
    inference(cnf_transformation,[],[f81])).

cnf(c_414,plain,
    ( ~ r2_hidden(X0,X1)
    | ~ r1_tarski(X1,X2)
    | ~ v1_xboole_0(X2) ),
    inference(bin_hyper_res,[status(thm)],[c_12,c_330])).

cnf(c_3404,plain,
    ( ~ r2_hidden(X0,X1)
    | ~ r1_tarski(X1,u1_struct_0(sK5))
    | ~ v1_xboole_0(u1_struct_0(sK5)) ),
    inference(instantiation,[status(thm)],[c_414])).

cnf(c_5653,plain,
    ( ~ r2_hidden(k3_yellow_0(sK5),sK6)
    | ~ r1_tarski(sK6,u1_struct_0(sK5))
    | ~ v1_xboole_0(u1_struct_0(sK5)) ),
    inference(instantiation,[status(thm)],[c_3404])).

cnf(c_5667,plain,
    ( r2_hidden(k3_yellow_0(sK5),sK6) != iProver_top
    | r1_tarski(sK6,u1_struct_0(sK5)) != iProver_top
    | v1_xboole_0(u1_struct_0(sK5)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_5653])).

cnf(c_6071,plain,
    ( r2_hidden(k1_yellow_0(sK5,X0),u1_struct_0(sK5)) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_4030,c_46,c_48,c_633,c_3265,c_3345,c_4126,c_4571,c_5667])).

cnf(c_2,plain,
    ( ~ r2_hidden(X0,X1)
    | r2_hidden(X0,X2)
    | ~ r1_tarski(X1,X2) ),
    inference(cnf_transformation,[],[f69])).

cnf(c_2945,plain,
    ( r2_hidden(X0,X1) != iProver_top
    | r2_hidden(X0,X2) = iProver_top
    | r1_tarski(X1,X2) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2])).

cnf(c_6079,plain,
    ( r2_hidden(k1_yellow_0(sK5,X0),X1) = iProver_top
    | r1_tarski(u1_struct_0(sK5),X1) != iProver_top ),
    inference(superposition,[status(thm)],[c_6071,c_2945])).

cnf(c_6476,plain,
    ( m1_subset_1(k1_yellow_0(sK5,X0),X1) = iProver_top
    | r1_tarski(u1_struct_0(sK5),X1) != iProver_top ),
    inference(superposition,[status(thm)],[c_6079,c_2941])).

cnf(c_27,plain,
    ( v13_waybel_0(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | r2_hidden(sK3(X1,X0),X0)
    | ~ l1_orders_2(X1) ),
    inference(cnf_transformation,[],[f97])).

cnf(c_940,plain,
    ( v13_waybel_0(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | r2_hidden(sK3(X1,X0),X0)
    | sK5 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_27,c_38])).

cnf(c_941,plain,
    ( v13_waybel_0(X0,sK5)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK5)))
    | r2_hidden(sK3(sK5,X0),X0) ),
    inference(unflattening,[status(thm)],[c_940])).

cnf(c_2916,plain,
    ( v13_waybel_0(X0,sK5) = iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK5))) != iProver_top
    | r2_hidden(sK3(sK5,X0),X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_941])).

cnf(c_7221,plain,
    ( v13_waybel_0(k1_yellow_0(sK5,X0),sK5) = iProver_top
    | r2_hidden(sK3(sK5,k1_yellow_0(sK5,X0)),k1_yellow_0(sK5,X0)) = iProver_top
    | r1_tarski(u1_struct_0(sK5),k1_zfmisc_1(u1_struct_0(sK5))) != iProver_top ),
    inference(superposition,[status(thm)],[c_6476,c_2916])).

cnf(c_8288,plain,
    ( v13_waybel_0(k1_yellow_0(sK5,k1_xboole_0),sK5) = iProver_top
    | r2_hidden(sK3(sK5,k3_yellow_0(sK5)),k3_yellow_0(sK5)) = iProver_top
    | r1_tarski(u1_struct_0(sK5),k1_zfmisc_1(u1_struct_0(sK5))) != iProver_top ),
    inference(superposition,[status(thm)],[c_840,c_7221])).

cnf(c_8318,plain,
    ( v13_waybel_0(k3_yellow_0(sK5),sK5) = iProver_top
    | r2_hidden(sK3(sK5,k3_yellow_0(sK5)),k3_yellow_0(sK5)) = iProver_top
    | r1_tarski(u1_struct_0(sK5),k1_zfmisc_1(u1_struct_0(sK5))) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_8288,c_840])).

cnf(c_29,plain,
    ( v13_waybel_0(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | m1_subset_1(sK3(X1,X0),u1_struct_0(X1))
    | ~ l1_orders_2(X1) ),
    inference(cnf_transformation,[],[f95])).

cnf(c_910,plain,
    ( v13_waybel_0(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | m1_subset_1(sK3(X1,X0),u1_struct_0(X1))
    | sK5 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_29,c_38])).

cnf(c_911,plain,
    ( v13_waybel_0(X0,sK5)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK5)))
    | m1_subset_1(sK3(sK5,X0),u1_struct_0(sK5)) ),
    inference(unflattening,[status(thm)],[c_910])).

cnf(c_2918,plain,
    ( v13_waybel_0(X0,sK5) = iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK5))) != iProver_top
    | m1_subset_1(sK3(sK5,X0),u1_struct_0(sK5)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_911])).

cnf(c_16,plain,
    ( r1_orders_2(X0,X1,X2)
    | ~ r2_lattice3(X0,X3,X2)
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | ~ m1_subset_1(X1,u1_struct_0(X0))
    | ~ r2_hidden(X1,X3)
    | ~ l1_orders_2(X0) ),
    inference(cnf_transformation,[],[f82])).

cnf(c_844,plain,
    ( r1_orders_2(X0,X1,X2)
    | ~ r2_lattice3(X0,X3,X2)
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | ~ m1_subset_1(X1,u1_struct_0(X0))
    | ~ r2_hidden(X1,X3)
    | sK5 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_16,c_38])).

cnf(c_845,plain,
    ( r1_orders_2(sK5,X0,X1)
    | ~ r2_lattice3(sK5,X2,X1)
    | ~ m1_subset_1(X1,u1_struct_0(sK5))
    | ~ m1_subset_1(X0,u1_struct_0(sK5))
    | ~ r2_hidden(X0,X2) ),
    inference(unflattening,[status(thm)],[c_844])).

cnf(c_2922,plain,
    ( r1_orders_2(sK5,X0,X1) = iProver_top
    | r2_lattice3(sK5,X2,X1) != iProver_top
    | m1_subset_1(X0,u1_struct_0(sK5)) != iProver_top
    | m1_subset_1(X1,u1_struct_0(sK5)) != iProver_top
    | r2_hidden(X0,X2) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_845])).

cnf(c_3777,plain,
    ( r1_orders_2(sK5,sK3(sK5,X0),X1) = iProver_top
    | r2_lattice3(sK5,X2,X1) != iProver_top
    | v13_waybel_0(X0,sK5) = iProver_top
    | m1_subset_1(X1,u1_struct_0(sK5)) != iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK5))) != iProver_top
    | r2_hidden(sK3(sK5,X0),X2) != iProver_top ),
    inference(superposition,[status(thm)],[c_2918,c_2922])).

cnf(c_9067,plain,
    ( r1_orders_2(sK5,sK3(sK5,k3_yellow_0(sK5)),X0) = iProver_top
    | r2_lattice3(sK5,k3_yellow_0(sK5),X0) != iProver_top
    | v13_waybel_0(k3_yellow_0(sK5),sK5) = iProver_top
    | m1_subset_1(X0,u1_struct_0(sK5)) != iProver_top
    | m1_subset_1(k3_yellow_0(sK5),k1_zfmisc_1(u1_struct_0(sK5))) != iProver_top
    | r1_tarski(u1_struct_0(sK5),k1_zfmisc_1(u1_struct_0(sK5))) != iProver_top ),
    inference(superposition,[status(thm)],[c_8318,c_3777])).

cnf(c_7213,plain,
    ( m1_subset_1(k3_yellow_0(sK5),X0) = iProver_top
    | r1_tarski(u1_struct_0(sK5),X0) != iProver_top ),
    inference(superposition,[status(thm)],[c_840,c_6476])).

cnf(c_17201,plain,
    ( r1_orders_2(sK5,sK3(sK5,k3_yellow_0(sK5)),X0) = iProver_top
    | r2_lattice3(sK5,k3_yellow_0(sK5),X0) != iProver_top
    | v13_waybel_0(k3_yellow_0(sK5),sK5) = iProver_top
    | m1_subset_1(X0,u1_struct_0(sK5)) != iProver_top
    | r1_tarski(u1_struct_0(sK5),k1_zfmisc_1(u1_struct_0(sK5))) != iProver_top ),
    inference(forward_subsumption_resolution,[status(thm)],[c_9067,c_7213])).

cnf(c_2936,plain,
    ( m1_subset_1(sK6,k1_zfmisc_1(u1_struct_0(sK5))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_35])).

cnf(c_30,plain,
    ( ~ r1_orders_2(X0,X1,X2)
    | ~ v13_waybel_0(X3,X0)
    | ~ m1_subset_1(X1,u1_struct_0(X0))
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))
    | ~ r2_hidden(X1,X3)
    | r2_hidden(X2,X3)
    | ~ l1_orders_2(X0) ),
    inference(cnf_transformation,[],[f94])).

cnf(c_790,plain,
    ( ~ r1_orders_2(X0,X1,X2)
    | ~ v13_waybel_0(X3,X0)
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | ~ m1_subset_1(X1,u1_struct_0(X0))
    | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))
    | ~ r2_hidden(X1,X3)
    | r2_hidden(X2,X3)
    | sK5 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_30,c_38])).

cnf(c_791,plain,
    ( ~ r1_orders_2(sK5,X0,X1)
    | ~ v13_waybel_0(X2,sK5)
    | ~ m1_subset_1(X1,u1_struct_0(sK5))
    | ~ m1_subset_1(X0,u1_struct_0(sK5))
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK5)))
    | ~ r2_hidden(X0,X2)
    | r2_hidden(X1,X2) ),
    inference(unflattening,[status(thm)],[c_790])).

cnf(c_11,plain,
    ( m1_subset_1(X0,X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(X1))
    | ~ r2_hidden(X0,X2) ),
    inference(cnf_transformation,[],[f80])).

cnf(c_807,plain,
    ( ~ r1_orders_2(sK5,X0,X1)
    | ~ v13_waybel_0(X2,sK5)
    | ~ m1_subset_1(X1,u1_struct_0(sK5))
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK5)))
    | ~ r2_hidden(X0,X2)
    | r2_hidden(X1,X2) ),
    inference(forward_subsumption_resolution,[status(thm)],[c_791,c_11])).

cnf(c_2925,plain,
    ( r1_orders_2(sK5,X0,X1) != iProver_top
    | v13_waybel_0(X2,sK5) != iProver_top
    | m1_subset_1(X1,u1_struct_0(sK5)) != iProver_top
    | m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK5))) != iProver_top
    | r2_hidden(X0,X2) != iProver_top
    | r2_hidden(X1,X2) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_807])).

cnf(c_4513,plain,
    ( r1_orders_2(sK5,X0,X1) != iProver_top
    | v13_waybel_0(sK6,sK5) != iProver_top
    | m1_subset_1(X1,u1_struct_0(sK5)) != iProver_top
    | r2_hidden(X0,sK6) != iProver_top
    | r2_hidden(X1,sK6) = iProver_top ),
    inference(superposition,[status(thm)],[c_2936,c_2925])).

cnf(c_36,negated_conjecture,
    ( v13_waybel_0(sK6,sK5) ),
    inference(cnf_transformation,[],[f107])).

cnf(c_1018,plain,
    ( ~ r1_orders_2(sK5,X0,X1)
    | ~ m1_subset_1(X1,u1_struct_0(sK5))
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK5)))
    | ~ r2_hidden(X0,X2)
    | r2_hidden(X1,X2)
    | sK6 != X2
    | sK5 != sK5 ),
    inference(resolution_lifted,[status(thm)],[c_36,c_807])).

cnf(c_1019,plain,
    ( ~ r1_orders_2(sK5,X0,X1)
    | ~ m1_subset_1(X1,u1_struct_0(sK5))
    | ~ m1_subset_1(sK6,k1_zfmisc_1(u1_struct_0(sK5)))
    | ~ r2_hidden(X0,sK6)
    | r2_hidden(X1,sK6) ),
    inference(unflattening,[status(thm)],[c_1018])).

cnf(c_1021,plain,
    ( ~ m1_subset_1(X1,u1_struct_0(sK5))
    | ~ r1_orders_2(sK5,X0,X1)
    | ~ r2_hidden(X0,sK6)
    | r2_hidden(X1,sK6) ),
    inference(global_propositional_subsumption,[status(thm)],[c_1019,c_35])).

cnf(c_1022,plain,
    ( ~ r1_orders_2(sK5,X0,X1)
    | ~ m1_subset_1(X1,u1_struct_0(sK5))
    | ~ r2_hidden(X0,sK6)
    | r2_hidden(X1,sK6) ),
    inference(renaming,[status(thm)],[c_1021])).

cnf(c_1023,plain,
    ( r1_orders_2(sK5,X0,X1) != iProver_top
    | m1_subset_1(X1,u1_struct_0(sK5)) != iProver_top
    | r2_hidden(X0,sK6) != iProver_top
    | r2_hidden(X1,sK6) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1022])).

cnf(c_4924,plain,
    ( r1_orders_2(sK5,X0,X1) != iProver_top
    | m1_subset_1(X1,u1_struct_0(sK5)) != iProver_top
    | r2_hidden(X0,sK6) != iProver_top
    | r2_hidden(X1,sK6) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_4513,c_1023])).

cnf(c_17207,plain,
    ( r2_lattice3(sK5,k3_yellow_0(sK5),X0) != iProver_top
    | v13_waybel_0(k3_yellow_0(sK5),sK5) = iProver_top
    | m1_subset_1(X0,u1_struct_0(sK5)) != iProver_top
    | r2_hidden(X0,sK6) = iProver_top
    | r2_hidden(sK3(sK5,k3_yellow_0(sK5)),sK6) != iProver_top
    | r1_tarski(u1_struct_0(sK5),k1_zfmisc_1(u1_struct_0(sK5))) != iProver_top ),
    inference(superposition,[status(thm)],[c_17201,c_4924])).

cnf(c_32,plain,
    ( ~ v1_subset_1(X0,X0)
    | ~ m1_subset_1(X0,k1_zfmisc_1(X0)) ),
    inference(cnf_transformation,[],[f115])).

cnf(c_52,plain,
    ( ~ v1_subset_1(sK5,sK5)
    | ~ m1_subset_1(sK5,k1_zfmisc_1(sK5)) ),
    inference(instantiation,[status(thm)],[c_32])).

cnf(c_55,plain,
    ( v1_subset_1(sK5,sK5)
    | ~ m1_subset_1(sK5,k1_zfmisc_1(sK5))
    | sK5 = sK5 ),
    inference(instantiation,[status(thm)],[c_31])).

cnf(c_95,plain,
    ( ~ l1_orders_2(sK5)
    | k1_yellow_0(sK5,k1_xboole_0) = k3_yellow_0(sK5) ),
    inference(instantiation,[status(thm)],[c_17])).

cnf(c_119,plain,
    ( m1_subset_1(sK5,k1_zfmisc_1(sK5))
    | ~ r1_tarski(sK5,sK5) ),
    inference(instantiation,[status(thm)],[c_9])).

cnf(c_6,plain,
    ( r1_tarski(X0,X0) ),
    inference(cnf_transformation,[],[f112])).

cnf(c_128,plain,
    ( r1_tarski(sK5,sK5) ),
    inference(instantiation,[status(thm)],[c_6])).

cnf(c_2144,plain,
    ( X0 != X1
    | k3_yellow_0(X0) = k3_yellow_0(X1) ),
    theory(equality)).

cnf(c_2159,plain,
    ( k3_yellow_0(sK5) = k3_yellow_0(sK5)
    | sK5 != sK5 ),
    inference(instantiation,[status(thm)],[c_2144])).

cnf(c_3553,plain,
    ( m1_subset_1(k1_yellow_0(sK5,k1_xboole_0),u1_struct_0(sK5)) ),
    inference(instantiation,[status(thm)],[c_831])).

cnf(c_3554,plain,
    ( m1_subset_1(k1_yellow_0(sK5,k1_xboole_0),u1_struct_0(sK5)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3553])).

cnf(c_21,plain,
    ( r1_orders_2(X0,k1_yellow_0(X0,X1),X2)
    | ~ r2_lattice3(X0,X1,X2)
    | ~ r1_yellow_0(X0,X1)
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | ~ m1_subset_1(k1_yellow_0(X0,X1),u1_struct_0(X0))
    | ~ l1_orders_2(X0) ),
    inference(cnf_transformation,[],[f113])).

cnf(c_249,plain,
    ( ~ m1_subset_1(X2,u1_struct_0(X0))
    | ~ r1_yellow_0(X0,X1)
    | ~ r2_lattice3(X0,X1,X2)
    | r1_orders_2(X0,k1_yellow_0(X0,X1),X2)
    | ~ l1_orders_2(X0) ),
    inference(global_propositional_subsumption,[status(thm)],[c_21,c_23])).

cnf(c_250,plain,
    ( r1_orders_2(X0,k1_yellow_0(X0,X1),X2)
    | ~ r2_lattice3(X0,X1,X2)
    | ~ r1_yellow_0(X0,X1)
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | ~ l1_orders_2(X0) ),
    inference(renaming,[status(thm)],[c_249])).

cnf(c_24,plain,
    ( r1_yellow_0(X0,k1_xboole_0)
    | v2_struct_0(X0)
    | ~ v5_orders_2(X0)
    | ~ v1_yellow_0(X0)
    | ~ l1_orders_2(X0) ),
    inference(cnf_transformation,[],[f93])).

cnf(c_39,negated_conjecture,
    ( v1_yellow_0(sK5) ),
    inference(cnf_transformation,[],[f104])).

cnf(c_562,plain,
    ( r1_yellow_0(X0,k1_xboole_0)
    | v2_struct_0(X0)
    | ~ v5_orders_2(X0)
    | ~ l1_orders_2(X0)
    | sK5 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_24,c_39])).

cnf(c_563,plain,
    ( r1_yellow_0(sK5,k1_xboole_0)
    | v2_struct_0(sK5)
    | ~ v5_orders_2(sK5)
    | ~ l1_orders_2(sK5) ),
    inference(unflattening,[status(thm)],[c_562])).

cnf(c_41,negated_conjecture,
    ( ~ v2_struct_0(sK5) ),
    inference(cnf_transformation,[],[f102])).

cnf(c_40,negated_conjecture,
    ( v5_orders_2(sK5) ),
    inference(cnf_transformation,[],[f103])).

cnf(c_74,plain,
    ( r1_yellow_0(sK5,k1_xboole_0)
    | v2_struct_0(sK5)
    | ~ v5_orders_2(sK5)
    | ~ v1_yellow_0(sK5)
    | ~ l1_orders_2(sK5) ),
    inference(instantiation,[status(thm)],[c_24])).

cnf(c_565,plain,
    ( r1_yellow_0(sK5,k1_xboole_0) ),
    inference(global_propositional_subsumption,[status(thm)],[c_563,c_41,c_40,c_39,c_38,c_74])).

cnf(c_665,plain,
    ( r1_orders_2(X0,k1_yellow_0(X0,X1),X2)
    | ~ r2_lattice3(X0,X1,X2)
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | ~ l1_orders_2(X0)
    | sK5 != X0
    | k1_xboole_0 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_250,c_565])).

cnf(c_666,plain,
    ( r1_orders_2(sK5,k1_yellow_0(sK5,k1_xboole_0),X0)
    | ~ r2_lattice3(sK5,k1_xboole_0,X0)
    | ~ m1_subset_1(X0,u1_struct_0(sK5))
    | ~ l1_orders_2(sK5) ),
    inference(unflattening,[status(thm)],[c_665])).

cnf(c_670,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(sK5))
    | ~ r2_lattice3(sK5,k1_xboole_0,X0)
    | r1_orders_2(sK5,k1_yellow_0(sK5,k1_xboole_0),X0) ),
    inference(global_propositional_subsumption,[status(thm)],[c_666,c_38])).

cnf(c_671,plain,
    ( r1_orders_2(sK5,k1_yellow_0(sK5,k1_xboole_0),X0)
    | ~ r2_lattice3(sK5,k1_xboole_0,X0)
    | ~ m1_subset_1(X0,u1_struct_0(sK5)) ),
    inference(renaming,[status(thm)],[c_670])).

cnf(c_2930,plain,
    ( r1_orders_2(sK5,k1_yellow_0(sK5,k1_xboole_0),X0) = iProver_top
    | r2_lattice3(sK5,k1_xboole_0,X0) != iProver_top
    | m1_subset_1(X0,u1_struct_0(sK5)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_671])).

cnf(c_3063,plain,
    ( r1_orders_2(sK5,k3_yellow_0(sK5),X0) = iProver_top
    | r2_lattice3(sK5,k1_xboole_0,X0) != iProver_top
    | m1_subset_1(X0,u1_struct_0(sK5)) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_2930,c_840])).

cnf(c_4933,plain,
    ( r2_lattice3(sK5,k1_xboole_0,X0) != iProver_top
    | m1_subset_1(X0,u1_struct_0(sK5)) != iProver_top
    | r2_hidden(X0,sK6) = iProver_top
    | r2_hidden(k3_yellow_0(sK5),sK6) != iProver_top ),
    inference(superposition,[status(thm)],[c_3063,c_4924])).

cnf(c_14,plain,
    ( r2_lattice3(X0,X1,X2)
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | r2_hidden(sK1(X0,X1,X2),X1)
    | ~ l1_orders_2(X0) ),
    inference(cnf_transformation,[],[f84])).

cnf(c_880,plain,
    ( r2_lattice3(X0,X1,X2)
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | r2_hidden(sK1(X0,X1,X2),X1)
    | sK5 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_14,c_38])).

cnf(c_881,plain,
    ( r2_lattice3(sK5,X0,X1)
    | ~ m1_subset_1(X1,u1_struct_0(sK5))
    | r2_hidden(sK1(sK5,X0,X1),X0) ),
    inference(unflattening,[status(thm)],[c_880])).

cnf(c_2920,plain,
    ( r2_lattice3(sK5,X0,X1) = iProver_top
    | m1_subset_1(X1,u1_struct_0(sK5)) != iProver_top
    | r2_hidden(sK1(sK5,X0,X1),X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_881])).

cnf(c_22,plain,
    ( r2_lattice3(X0,X1,k1_yellow_0(X0,X1))
    | ~ r1_yellow_0(X0,X1)
    | ~ m1_subset_1(k1_yellow_0(X0,X1),u1_struct_0(X0))
    | ~ l1_orders_2(X0) ),
    inference(cnf_transformation,[],[f114])).

cnf(c_242,plain,
    ( ~ r1_yellow_0(X0,X1)
    | r2_lattice3(X0,X1,k1_yellow_0(X0,X1))
    | ~ l1_orders_2(X0) ),
    inference(global_propositional_subsumption,[status(thm)],[c_22,c_23])).

cnf(c_243,plain,
    ( r2_lattice3(X0,X1,k1_yellow_0(X0,X1))
    | ~ r1_yellow_0(X0,X1)
    | ~ l1_orders_2(X0) ),
    inference(renaming,[status(thm)],[c_242])).

cnf(c_686,plain,
    ( r2_lattice3(X0,X1,k1_yellow_0(X0,X1))
    | ~ l1_orders_2(X0)
    | sK5 != X0
    | k1_xboole_0 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_243,c_565])).

cnf(c_687,plain,
    ( r2_lattice3(sK5,k1_xboole_0,k1_yellow_0(sK5,k1_xboole_0))
    | ~ l1_orders_2(sK5) ),
    inference(unflattening,[status(thm)],[c_686])).

cnf(c_689,plain,
    ( r2_lattice3(sK5,k1_xboole_0,k1_yellow_0(sK5,k1_xboole_0)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_687,c_38])).

cnf(c_2929,plain,
    ( r2_lattice3(sK5,k1_xboole_0,k1_yellow_0(sK5,k1_xboole_0)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_689])).

cnf(c_2962,plain,
    ( r2_lattice3(sK5,k1_xboole_0,k3_yellow_0(sK5)) = iProver_top ),
    inference(light_normalisation,[status(thm)],[c_2929,c_840])).

cnf(c_3276,plain,
    ( m1_subset_1(k3_yellow_0(sK5),u1_struct_0(sK5)) = iProver_top ),
    inference(superposition,[status(thm)],[c_840,c_2923])).

cnf(c_2937,plain,
    ( m1_subset_1(X0,X1) = iProver_top
    | m1_subset_1(X2,k1_zfmisc_1(X1)) != iProver_top
    | r2_hidden(X0,X2) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_11])).

cnf(c_4665,plain,
    ( m1_subset_1(X0,u1_struct_0(sK5)) = iProver_top
    | r2_hidden(X0,sK6) != iProver_top ),
    inference(superposition,[status(thm)],[c_2936,c_2937])).

cnf(c_4796,plain,
    ( r1_orders_2(sK5,X0,X1) = iProver_top
    | r2_lattice3(sK5,X2,X1) != iProver_top
    | m1_subset_1(X1,u1_struct_0(sK5)) != iProver_top
    | r2_hidden(X0,X2) != iProver_top
    | r2_hidden(X0,sK6) != iProver_top ),
    inference(superposition,[status(thm)],[c_4665,c_2922])).

cnf(c_5099,plain,
    ( r1_orders_2(sK5,X0,k3_yellow_0(sK5)) = iProver_top
    | r2_lattice3(sK5,X1,k3_yellow_0(sK5)) != iProver_top
    | r2_hidden(X0,X1) != iProver_top
    | r2_hidden(X0,sK6) != iProver_top ),
    inference(superposition,[status(thm)],[c_3276,c_4796])).

cnf(c_5202,plain,
    ( r1_orders_2(sK5,X0,k3_yellow_0(sK5)) = iProver_top
    | r2_hidden(X0,sK6) != iProver_top
    | r2_hidden(X0,k1_xboole_0) != iProver_top ),
    inference(superposition,[status(thm)],[c_2962,c_5099])).

cnf(c_3,plain,
    ( v1_xboole_0(k1_xboole_0) ),
    inference(cnf_transformation,[],[f72])).

cnf(c_134,plain,
    ( v1_xboole_0(k1_xboole_0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3])).

cnf(c_3295,plain,
    ( ~ r2_hidden(X0,X1)
    | ~ r1_tarski(X1,k1_xboole_0)
    | ~ v1_xboole_0(k1_xboole_0) ),
    inference(instantiation,[status(thm)],[c_414])).

cnf(c_3818,plain,
    ( ~ r2_hidden(X0,k1_xboole_0)
    | ~ r1_tarski(k1_xboole_0,k1_xboole_0)
    | ~ v1_xboole_0(k1_xboole_0) ),
    inference(instantiation,[status(thm)],[c_3295])).

cnf(c_3820,plain,
    ( r2_hidden(X0,k1_xboole_0) != iProver_top
    | r1_tarski(k1_xboole_0,k1_xboole_0) != iProver_top
    | v1_xboole_0(k1_xboole_0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3818])).

cnf(c_3819,plain,
    ( r1_tarski(k1_xboole_0,k1_xboole_0) ),
    inference(instantiation,[status(thm)],[c_6])).

cnf(c_3824,plain,
    ( r1_tarski(k1_xboole_0,k1_xboole_0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3819])).

cnf(c_5354,plain,
    ( r2_hidden(X0,k1_xboole_0) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_5202,c_134,c_3820,c_3824])).

cnf(c_5362,plain,
    ( r2_lattice3(sK5,k1_xboole_0,X0) = iProver_top
    | m1_subset_1(X0,u1_struct_0(sK5)) != iProver_top ),
    inference(superposition,[status(thm)],[c_2920,c_5354])).

cnf(c_3735,plain,
    ( X0 != X1
    | X0 = k1_yellow_0(sK5,X2)
    | k1_yellow_0(sK5,X2) != X1 ),
    inference(instantiation,[status(thm)],[c_2134])).

cnf(c_5252,plain,
    ( X0 = k1_yellow_0(sK5,k1_xboole_0)
    | X0 != k3_yellow_0(sK5)
    | k1_yellow_0(sK5,k1_xboole_0) != k3_yellow_0(sK5) ),
    inference(instantiation,[status(thm)],[c_3735])).

cnf(c_6041,plain,
    ( k1_yellow_0(sK5,k1_xboole_0) != k3_yellow_0(sK5)
    | k3_yellow_0(sK5) = k1_yellow_0(sK5,k1_xboole_0)
    | k3_yellow_0(sK5) != k3_yellow_0(sK5) ),
    inference(instantiation,[status(thm)],[c_5252])).

cnf(c_2932,plain,
    ( u1_struct_0(sK5) = sK6
    | r2_hidden(k3_yellow_0(sK5),sK6) = iProver_top
    | r1_tarski(sK6,u1_struct_0(sK5)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_632])).

cnf(c_6280,plain,
    ( r2_hidden(k3_yellow_0(sK5),sK6) = iProver_top
    | u1_struct_0(sK5) = sK6 ),
    inference(global_propositional_subsumption,[status(thm)],[c_2932,c_48,c_633,c_3265])).

cnf(c_6281,plain,
    ( u1_struct_0(sK5) = sK6
    | r2_hidden(k3_yellow_0(sK5),sK6) = iProver_top ),
    inference(renaming,[status(thm)],[c_6280])).

cnf(c_6288,plain,
    ( u1_struct_0(sK5) = sK6
    | r2_lattice3(sK5,k1_xboole_0,X0) != iProver_top
    | m1_subset_1(X0,u1_struct_0(sK5)) != iProver_top
    | r2_hidden(X0,sK6) = iProver_top ),
    inference(superposition,[status(thm)],[c_6281,c_4933])).

cnf(c_6892,plain,
    ( ~ m1_subset_1(k3_yellow_0(sK5),sK6)
    | r2_hidden(k3_yellow_0(sK5),sK6)
    | v1_xboole_0(sK6) ),
    inference(instantiation,[status(thm)],[c_8])).

cnf(c_6893,plain,
    ( m1_subset_1(k3_yellow_0(sK5),sK6) != iProver_top
    | r2_hidden(k3_yellow_0(sK5),sK6) = iProver_top
    | v1_xboole_0(sK6) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_6892])).

cnf(c_2138,plain,
    ( ~ m1_subset_1(X0,X1)
    | m1_subset_1(X2,X3)
    | X2 != X0
    | X3 != X1 ),
    theory(equality)).

cnf(c_5075,plain,
    ( m1_subset_1(X0,X1)
    | ~ m1_subset_1(k1_yellow_0(sK5,k1_xboole_0),u1_struct_0(X2))
    | X0 != k1_yellow_0(sK5,k1_xboole_0)
    | X1 != u1_struct_0(X2) ),
    inference(instantiation,[status(thm)],[c_2138])).

cnf(c_14182,plain,
    ( ~ m1_subset_1(k1_yellow_0(sK5,k1_xboole_0),u1_struct_0(X0))
    | m1_subset_1(k3_yellow_0(sK5),sK6)
    | k3_yellow_0(sK5) != k1_yellow_0(sK5,k1_xboole_0)
    | sK6 != u1_struct_0(X0) ),
    inference(instantiation,[status(thm)],[c_5075])).

cnf(c_14200,plain,
    ( k3_yellow_0(sK5) != k1_yellow_0(sK5,k1_xboole_0)
    | sK6 != u1_struct_0(X0)
    | m1_subset_1(k1_yellow_0(sK5,k1_xboole_0),u1_struct_0(X0)) != iProver_top
    | m1_subset_1(k3_yellow_0(sK5),sK6) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_14182])).

cnf(c_14202,plain,
    ( k3_yellow_0(sK5) != k1_yellow_0(sK5,k1_xboole_0)
    | sK6 != u1_struct_0(sK5)
    | m1_subset_1(k1_yellow_0(sK5,k1_xboole_0),u1_struct_0(sK5)) != iProver_top
    | m1_subset_1(k3_yellow_0(sK5),sK6) = iProver_top ),
    inference(instantiation,[status(thm)],[c_14200])).

cnf(c_17898,plain,
    ( m1_subset_1(X0,u1_struct_0(sK5)) != iProver_top
    | r2_hidden(X0,sK6) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_17207,c_38,c_46,c_52,c_55,c_95,c_119,c_128,c_2159,c_3345,c_3554,c_4571,c_4933,c_5362,c_6041,c_6288,c_6893,c_14202])).

cnf(c_17915,plain,
    ( r2_hidden(sK0(u1_struct_0(sK5),X0),sK6) = iProver_top
    | r1_tarski(u1_struct_0(sK5),X0) = iProver_top ),
    inference(superposition,[status(thm)],[c_3965,c_17898])).

cnf(c_0,plain,
    ( ~ r2_hidden(sK0(X0,X1),X1)
    | r1_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f71])).

cnf(c_2947,plain,
    ( r2_hidden(sK0(X0,X1),X1) != iProver_top
    | r1_tarski(X0,X1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_0])).

cnf(c_98008,plain,
    ( r1_tarski(u1_struct_0(sK5),sK6) = iProver_top ),
    inference(superposition,[status(thm)],[c_17915,c_2947])).

cnf(c_17913,plain,
    ( r2_hidden(k3_yellow_0(sK5),sK6) = iProver_top ),
    inference(superposition,[status(thm)],[c_3276,c_17898])).

cnf(c_4,plain,
    ( ~ r1_tarski(X0,X1)
    | ~ r1_tarski(X1,X0)
    | X1 = X0 ),
    inference(cnf_transformation,[],[f75])).

cnf(c_3461,plain,
    ( ~ r1_tarski(X0,u1_struct_0(sK5))
    | ~ r1_tarski(u1_struct_0(sK5),X0)
    | X0 = u1_struct_0(sK5) ),
    inference(instantiation,[status(thm)],[c_4])).

cnf(c_4104,plain,
    ( ~ r1_tarski(u1_struct_0(sK5),sK6)
    | ~ r1_tarski(sK6,u1_struct_0(sK5))
    | sK6 = u1_struct_0(sK5) ),
    inference(instantiation,[status(thm)],[c_3461])).

cnf(c_4106,plain,
    ( sK6 = u1_struct_0(sK5)
    | r1_tarski(u1_struct_0(sK5),sK6) != iProver_top
    | r1_tarski(sK6,u1_struct_0(sK5)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_4104])).

cnf(c_3394,plain,
    ( r1_tarski(u1_struct_0(sK5),u1_struct_0(sK5)) ),
    inference(instantiation,[status(thm)],[c_6])).

cnf(c_3397,plain,
    ( r1_tarski(u1_struct_0(sK5),u1_struct_0(sK5)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3394])).

cnf(c_3259,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK5)))
    | ~ r1_tarski(X0,u1_struct_0(sK5)) ),
    inference(instantiation,[status(thm)],[c_9])).

cnf(c_3393,plain,
    ( m1_subset_1(u1_struct_0(sK5),k1_zfmisc_1(u1_struct_0(sK5)))
    | ~ r1_tarski(u1_struct_0(sK5),u1_struct_0(sK5)) ),
    inference(instantiation,[status(thm)],[c_3259])).

cnf(c_3395,plain,
    ( m1_subset_1(u1_struct_0(sK5),k1_zfmisc_1(u1_struct_0(sK5))) = iProver_top
    | r1_tarski(u1_struct_0(sK5),u1_struct_0(sK5)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3393])).

cnf(c_34,negated_conjecture,
    ( v1_subset_1(sK6,u1_struct_0(sK5))
    | ~ r2_hidden(k3_yellow_0(sK5),sK6) ),
    inference(cnf_transformation,[],[f109])).

cnf(c_331,plain,
    ( v1_subset_1(sK6,u1_struct_0(sK5))
    | ~ r2_hidden(k3_yellow_0(sK5),sK6) ),
    inference(prop_impl,[status(thm)],[c_34])).

cnf(c_644,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X0))
    | ~ r2_hidden(k3_yellow_0(sK5),sK6)
    | u1_struct_0(sK5) != X0
    | sK6 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_32,c_331])).

cnf(c_645,plain,
    ( ~ m1_subset_1(u1_struct_0(sK5),k1_zfmisc_1(u1_struct_0(sK5)))
    | ~ r2_hidden(k3_yellow_0(sK5),sK6)
    | sK6 != u1_struct_0(sK5) ),
    inference(unflattening,[status(thm)],[c_644])).

cnf(c_646,plain,
    ( sK6 != u1_struct_0(sK5)
    | m1_subset_1(u1_struct_0(sK5),k1_zfmisc_1(u1_struct_0(sK5))) != iProver_top
    | r2_hidden(k3_yellow_0(sK5),sK6) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_645])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_98008,c_17913,c_4106,c_3397,c_3395,c_3265,c_646,c_48])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.08/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.08/0.13  % Command    : iproveropt_run.sh %d %s
% 0.12/0.34  % Computer   : n007.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % WCLimit    : 600
% 0.12/0.34  % DateTime   : Tue Dec  1 11:48:51 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.34  % Running in FOF mode
% 19.32/3.01  % SZS status Started for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 19.32/3.01  
% 19.32/3.01  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 19.32/3.01  
% 19.32/3.01  ------  iProver source info
% 19.32/3.01  
% 19.32/3.01  git: date: 2020-06-30 10:37:57 +0100
% 19.32/3.01  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 19.32/3.01  git: non_committed_changes: false
% 19.32/3.01  git: last_make_outside_of_git: false
% 19.32/3.01  
% 19.32/3.01  ------ 
% 19.32/3.01  
% 19.32/3.01  ------ Input Options
% 19.32/3.01  
% 19.32/3.01  --out_options                           all
% 19.32/3.01  --tptp_safe_out                         true
% 19.32/3.01  --problem_path                          ""
% 19.32/3.01  --include_path                          ""
% 19.32/3.01  --clausifier                            res/vclausify_rel
% 19.32/3.01  --clausifier_options                    --mode clausify
% 19.32/3.01  --stdin                                 false
% 19.32/3.01  --stats_out                             all
% 19.32/3.01  
% 19.32/3.01  ------ General Options
% 19.32/3.01  
% 19.32/3.01  --fof                                   false
% 19.32/3.01  --time_out_real                         305.
% 19.32/3.01  --time_out_virtual                      -1.
% 19.32/3.01  --symbol_type_check                     false
% 19.32/3.01  --clausify_out                          false
% 19.32/3.01  --sig_cnt_out                           false
% 19.32/3.01  --trig_cnt_out                          false
% 19.32/3.01  --trig_cnt_out_tolerance                1.
% 19.32/3.01  --trig_cnt_out_sk_spl                   false
% 19.32/3.01  --abstr_cl_out                          false
% 19.32/3.01  
% 19.32/3.01  ------ Global Options
% 19.32/3.01  
% 19.32/3.01  --schedule                              default
% 19.32/3.01  --add_important_lit                     false
% 19.32/3.01  --prop_solver_per_cl                    1000
% 19.32/3.01  --min_unsat_core                        false
% 19.32/3.01  --soft_assumptions                      false
% 19.32/3.01  --soft_lemma_size                       3
% 19.32/3.01  --prop_impl_unit_size                   0
% 19.32/3.01  --prop_impl_unit                        []
% 19.32/3.01  --share_sel_clauses                     true
% 19.32/3.01  --reset_solvers                         false
% 19.32/3.01  --bc_imp_inh                            [conj_cone]
% 19.32/3.01  --conj_cone_tolerance                   3.
% 19.32/3.01  --extra_neg_conj                        none
% 19.32/3.01  --large_theory_mode                     true
% 19.32/3.01  --prolific_symb_bound                   200
% 19.32/3.01  --lt_threshold                          2000
% 19.32/3.01  --clause_weak_htbl                      true
% 19.32/3.01  --gc_record_bc_elim                     false
% 19.32/3.01  
% 19.32/3.01  ------ Preprocessing Options
% 19.32/3.01  
% 19.32/3.01  --preprocessing_flag                    true
% 19.32/3.01  --time_out_prep_mult                    0.1
% 19.32/3.01  --splitting_mode                        input
% 19.32/3.01  --splitting_grd                         true
% 19.32/3.01  --splitting_cvd                         false
% 19.32/3.01  --splitting_cvd_svl                     false
% 19.32/3.01  --splitting_nvd                         32
% 19.32/3.01  --sub_typing                            true
% 19.32/3.01  --prep_gs_sim                           true
% 19.32/3.01  --prep_unflatten                        true
% 19.32/3.01  --prep_res_sim                          true
% 19.32/3.01  --prep_upred                            true
% 19.32/3.01  --prep_sem_filter                       exhaustive
% 19.32/3.01  --prep_sem_filter_out                   false
% 19.32/3.01  --pred_elim                             true
% 19.32/3.01  --res_sim_input                         true
% 19.32/3.01  --eq_ax_congr_red                       true
% 19.32/3.01  --pure_diseq_elim                       true
% 19.32/3.01  --brand_transform                       false
% 19.32/3.01  --non_eq_to_eq                          false
% 19.32/3.01  --prep_def_merge                        true
% 19.32/3.01  --prep_def_merge_prop_impl              false
% 19.32/3.01  --prep_def_merge_mbd                    true
% 19.32/3.01  --prep_def_merge_tr_red                 false
% 19.32/3.01  --prep_def_merge_tr_cl                  false
% 19.32/3.01  --smt_preprocessing                     true
% 19.32/3.01  --smt_ac_axioms                         fast
% 19.32/3.01  --preprocessed_out                      false
% 19.32/3.01  --preprocessed_stats                    false
% 19.32/3.01  
% 19.32/3.01  ------ Abstraction refinement Options
% 19.32/3.01  
% 19.32/3.01  --abstr_ref                             []
% 19.32/3.01  --abstr_ref_prep                        false
% 19.32/3.01  --abstr_ref_until_sat                   false
% 19.32/3.01  --abstr_ref_sig_restrict                funpre
% 19.32/3.01  --abstr_ref_af_restrict_to_split_sk     false
% 19.32/3.01  --abstr_ref_under                       []
% 19.32/3.01  
% 19.32/3.01  ------ SAT Options
% 19.32/3.01  
% 19.32/3.01  --sat_mode                              false
% 19.32/3.01  --sat_fm_restart_options                ""
% 19.32/3.01  --sat_gr_def                            false
% 19.32/3.01  --sat_epr_types                         true
% 19.32/3.01  --sat_non_cyclic_types                  false
% 19.32/3.01  --sat_finite_models                     false
% 19.32/3.01  --sat_fm_lemmas                         false
% 19.32/3.01  --sat_fm_prep                           false
% 19.32/3.01  --sat_fm_uc_incr                        true
% 19.32/3.01  --sat_out_model                         small
% 19.32/3.01  --sat_out_clauses                       false
% 19.32/3.01  
% 19.32/3.01  ------ QBF Options
% 19.32/3.01  
% 19.32/3.01  --qbf_mode                              false
% 19.32/3.01  --qbf_elim_univ                         false
% 19.32/3.01  --qbf_dom_inst                          none
% 19.32/3.01  --qbf_dom_pre_inst                      false
% 19.32/3.01  --qbf_sk_in                             false
% 19.32/3.01  --qbf_pred_elim                         true
% 19.32/3.01  --qbf_split                             512
% 19.32/3.01  
% 19.32/3.01  ------ BMC1 Options
% 19.32/3.01  
% 19.32/3.01  --bmc1_incremental                      false
% 19.32/3.01  --bmc1_axioms                           reachable_all
% 19.32/3.01  --bmc1_min_bound                        0
% 19.32/3.01  --bmc1_max_bound                        -1
% 19.32/3.01  --bmc1_max_bound_default                -1
% 19.32/3.01  --bmc1_symbol_reachability              true
% 19.32/3.01  --bmc1_property_lemmas                  false
% 19.32/3.01  --bmc1_k_induction                      false
% 19.32/3.01  --bmc1_non_equiv_states                 false
% 19.32/3.01  --bmc1_deadlock                         false
% 19.32/3.01  --bmc1_ucm                              false
% 19.32/3.01  --bmc1_add_unsat_core                   none
% 19.32/3.01  --bmc1_unsat_core_children              false
% 19.32/3.01  --bmc1_unsat_core_extrapolate_axioms    false
% 19.32/3.01  --bmc1_out_stat                         full
% 19.32/3.01  --bmc1_ground_init                      false
% 19.32/3.01  --bmc1_pre_inst_next_state              false
% 19.32/3.01  --bmc1_pre_inst_state                   false
% 19.32/3.01  --bmc1_pre_inst_reach_state             false
% 19.32/3.01  --bmc1_out_unsat_core                   false
% 19.32/3.01  --bmc1_aig_witness_out                  false
% 19.32/3.01  --bmc1_verbose                          false
% 19.32/3.01  --bmc1_dump_clauses_tptp                false
% 19.32/3.01  --bmc1_dump_unsat_core_tptp             false
% 19.32/3.01  --bmc1_dump_file                        -
% 19.32/3.01  --bmc1_ucm_expand_uc_limit              128
% 19.32/3.01  --bmc1_ucm_n_expand_iterations          6
% 19.32/3.01  --bmc1_ucm_extend_mode                  1
% 19.32/3.01  --bmc1_ucm_init_mode                    2
% 19.32/3.01  --bmc1_ucm_cone_mode                    none
% 19.32/3.01  --bmc1_ucm_reduced_relation_type        0
% 19.32/3.01  --bmc1_ucm_relax_model                  4
% 19.32/3.01  --bmc1_ucm_full_tr_after_sat            true
% 19.32/3.01  --bmc1_ucm_expand_neg_assumptions       false
% 19.32/3.01  --bmc1_ucm_layered_model                none
% 19.32/3.01  --bmc1_ucm_max_lemma_size               10
% 19.32/3.01  
% 19.32/3.01  ------ AIG Options
% 19.32/3.01  
% 19.32/3.01  --aig_mode                              false
% 19.32/3.01  
% 19.32/3.01  ------ Instantiation Options
% 19.32/3.01  
% 19.32/3.01  --instantiation_flag                    true
% 19.32/3.01  --inst_sos_flag                         false
% 19.32/3.01  --inst_sos_phase                        true
% 19.32/3.01  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 19.32/3.01  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 19.32/3.01  --inst_lit_sel_side                     num_symb
% 19.32/3.01  --inst_solver_per_active                1400
% 19.32/3.01  --inst_solver_calls_frac                1.
% 19.32/3.01  --inst_passive_queue_type               priority_queues
% 19.32/3.01  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 19.32/3.01  --inst_passive_queues_freq              [25;2]
% 19.32/3.01  --inst_dismatching                      true
% 19.32/3.01  --inst_eager_unprocessed_to_passive     true
% 19.32/3.01  --inst_prop_sim_given                   true
% 19.32/3.01  --inst_prop_sim_new                     false
% 19.32/3.01  --inst_subs_new                         false
% 19.32/3.01  --inst_eq_res_simp                      false
% 19.32/3.01  --inst_subs_given                       false
% 19.32/3.01  --inst_orphan_elimination               true
% 19.32/3.01  --inst_learning_loop_flag               true
% 19.32/3.01  --inst_learning_start                   3000
% 19.32/3.01  --inst_learning_factor                  2
% 19.32/3.01  --inst_start_prop_sim_after_learn       3
% 19.32/3.01  --inst_sel_renew                        solver
% 19.32/3.01  --inst_lit_activity_flag                true
% 19.32/3.01  --inst_restr_to_given                   false
% 19.32/3.01  --inst_activity_threshold               500
% 19.32/3.01  --inst_out_proof                        true
% 19.32/3.01  
% 19.32/3.01  ------ Resolution Options
% 19.32/3.01  
% 19.32/3.01  --resolution_flag                       true
% 19.32/3.01  --res_lit_sel                           adaptive
% 19.32/3.01  --res_lit_sel_side                      none
% 19.32/3.01  --res_ordering                          kbo
% 19.32/3.01  --res_to_prop_solver                    active
% 19.32/3.01  --res_prop_simpl_new                    false
% 19.32/3.01  --res_prop_simpl_given                  true
% 19.32/3.01  --res_passive_queue_type                priority_queues
% 19.32/3.01  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 19.32/3.01  --res_passive_queues_freq               [15;5]
% 19.32/3.01  --res_forward_subs                      full
% 19.32/3.01  --res_backward_subs                     full
% 19.32/3.01  --res_forward_subs_resolution           true
% 19.32/3.01  --res_backward_subs_resolution          true
% 19.32/3.01  --res_orphan_elimination                true
% 19.32/3.01  --res_time_limit                        2.
% 19.32/3.01  --res_out_proof                         true
% 19.32/3.01  
% 19.32/3.01  ------ Superposition Options
% 19.32/3.01  
% 19.32/3.01  --superposition_flag                    true
% 19.32/3.01  --sup_passive_queue_type                priority_queues
% 19.32/3.01  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 19.32/3.01  --sup_passive_queues_freq               [8;1;4]
% 19.32/3.01  --demod_completeness_check              fast
% 19.32/3.01  --demod_use_ground                      true
% 19.32/3.01  --sup_to_prop_solver                    passive
% 19.32/3.01  --sup_prop_simpl_new                    true
% 19.32/3.01  --sup_prop_simpl_given                  true
% 19.32/3.01  --sup_fun_splitting                     false
% 19.32/3.01  --sup_smt_interval                      50000
% 19.32/3.01  
% 19.32/3.01  ------ Superposition Simplification Setup
% 19.32/3.01  
% 19.32/3.01  --sup_indices_passive                   []
% 19.32/3.01  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 19.32/3.01  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 19.32/3.01  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 19.32/3.01  --sup_full_triv                         [TrivRules;PropSubs]
% 19.32/3.01  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 19.32/3.01  --sup_full_bw                           [BwDemod]
% 19.32/3.01  --sup_immed_triv                        [TrivRules]
% 19.32/3.01  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 19.32/3.01  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 19.32/3.01  --sup_immed_bw_main                     []
% 19.32/3.01  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 19.32/3.01  --sup_input_triv                        [Unflattening;TrivRules]
% 19.32/3.01  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 19.32/3.01  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 19.32/3.01  
% 19.32/3.01  ------ Combination Options
% 19.32/3.01  
% 19.32/3.01  --comb_res_mult                         3
% 19.32/3.01  --comb_sup_mult                         2
% 19.32/3.01  --comb_inst_mult                        10
% 19.32/3.01  
% 19.32/3.01  ------ Debug Options
% 19.32/3.01  
% 19.32/3.01  --dbg_backtrace                         false
% 19.32/3.01  --dbg_dump_prop_clauses                 false
% 19.32/3.01  --dbg_dump_prop_clauses_file            -
% 19.32/3.01  --dbg_out_stat                          false
% 19.32/3.01  ------ Parsing...
% 19.32/3.01  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 19.32/3.01  
% 19.32/3.01  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe:1:0s pe:2:0s pe:4:0s pe_e  sf_s  rm: 7 0s  sf_e  pe_s  pe_e 
% 19.32/3.01  
% 19.32/3.01  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 19.32/3.01  
% 19.32/3.01  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 19.32/3.01  ------ Proving...
% 19.32/3.01  ------ Problem Properties 
% 19.32/3.01  
% 19.32/3.01  
% 19.32/3.01  clauses                                 34
% 19.32/3.01  conjectures                             3
% 19.32/3.01  EPR                                     9
% 19.32/3.01  Horn                                    23
% 19.32/3.01  unary                                   8
% 19.32/3.01  binary                                  5
% 19.32/3.01  lits                                    89
% 19.32/3.01  lits eq                                 7
% 19.32/3.01  fd_pure                                 0
% 19.32/3.01  fd_pseudo                               0
% 19.32/3.01  fd_cond                                 3
% 19.32/3.01  fd_pseudo_cond                          1
% 19.32/3.01  AC symbols                              0
% 19.32/3.01  
% 19.32/3.01  ------ Schedule dynamic 5 is on 
% 19.32/3.01  
% 19.32/3.01  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" Time Limit: 10.
% 19.32/3.01  
% 19.32/3.01  
% 19.32/3.01  ------ 
% 19.32/3.01  Current options:
% 19.32/3.01  ------ 
% 19.32/3.01  
% 19.32/3.01  ------ Input Options
% 19.32/3.01  
% 19.32/3.01  --out_options                           all
% 19.32/3.01  --tptp_safe_out                         true
% 19.32/3.01  --problem_path                          ""
% 19.32/3.01  --include_path                          ""
% 19.32/3.01  --clausifier                            res/vclausify_rel
% 19.32/3.01  --clausifier_options                    --mode clausify
% 19.32/3.01  --stdin                                 false
% 19.32/3.01  --stats_out                             all
% 19.32/3.02  
% 19.32/3.02  ------ General Options
% 19.32/3.02  
% 19.32/3.02  --fof                                   false
% 19.32/3.02  --time_out_real                         305.
% 19.32/3.02  --time_out_virtual                      -1.
% 19.32/3.02  --symbol_type_check                     false
% 19.32/3.02  --clausify_out                          false
% 19.32/3.02  --sig_cnt_out                           false
% 19.32/3.02  --trig_cnt_out                          false
% 19.32/3.02  --trig_cnt_out_tolerance                1.
% 19.32/3.02  --trig_cnt_out_sk_spl                   false
% 19.32/3.02  --abstr_cl_out                          false
% 19.32/3.02  
% 19.32/3.02  ------ Global Options
% 19.32/3.02  
% 19.32/3.02  --schedule                              default
% 19.32/3.02  --add_important_lit                     false
% 19.32/3.02  --prop_solver_per_cl                    1000
% 19.32/3.02  --min_unsat_core                        false
% 19.32/3.02  --soft_assumptions                      false
% 19.32/3.02  --soft_lemma_size                       3
% 19.32/3.02  --prop_impl_unit_size                   0
% 19.32/3.02  --prop_impl_unit                        []
% 19.32/3.02  --share_sel_clauses                     true
% 19.32/3.02  --reset_solvers                         false
% 19.32/3.02  --bc_imp_inh                            [conj_cone]
% 19.32/3.02  --conj_cone_tolerance                   3.
% 19.32/3.02  --extra_neg_conj                        none
% 19.32/3.02  --large_theory_mode                     true
% 19.32/3.02  --prolific_symb_bound                   200
% 19.32/3.02  --lt_threshold                          2000
% 19.32/3.02  --clause_weak_htbl                      true
% 19.32/3.02  --gc_record_bc_elim                     false
% 19.32/3.02  
% 19.32/3.02  ------ Preprocessing Options
% 19.32/3.02  
% 19.32/3.02  --preprocessing_flag                    true
% 19.32/3.02  --time_out_prep_mult                    0.1
% 19.32/3.02  --splitting_mode                        input
% 19.32/3.02  --splitting_grd                         true
% 19.32/3.02  --splitting_cvd                         false
% 19.32/3.02  --splitting_cvd_svl                     false
% 19.32/3.02  --splitting_nvd                         32
% 19.32/3.02  --sub_typing                            true
% 19.32/3.02  --prep_gs_sim                           true
% 19.32/3.02  --prep_unflatten                        true
% 19.32/3.02  --prep_res_sim                          true
% 19.32/3.02  --prep_upred                            true
% 19.32/3.02  --prep_sem_filter                       exhaustive
% 19.32/3.02  --prep_sem_filter_out                   false
% 19.32/3.02  --pred_elim                             true
% 19.32/3.02  --res_sim_input                         true
% 19.32/3.02  --eq_ax_congr_red                       true
% 19.32/3.02  --pure_diseq_elim                       true
% 19.32/3.02  --brand_transform                       false
% 19.32/3.02  --non_eq_to_eq                          false
% 19.32/3.02  --prep_def_merge                        true
% 19.32/3.02  --prep_def_merge_prop_impl              false
% 19.32/3.02  --prep_def_merge_mbd                    true
% 19.32/3.02  --prep_def_merge_tr_red                 false
% 19.32/3.02  --prep_def_merge_tr_cl                  false
% 19.32/3.02  --smt_preprocessing                     true
% 19.32/3.02  --smt_ac_axioms                         fast
% 19.32/3.02  --preprocessed_out                      false
% 19.32/3.02  --preprocessed_stats                    false
% 19.32/3.02  
% 19.32/3.02  ------ Abstraction refinement Options
% 19.32/3.02  
% 19.32/3.02  --abstr_ref                             []
% 19.32/3.02  --abstr_ref_prep                        false
% 19.32/3.02  --abstr_ref_until_sat                   false
% 19.32/3.02  --abstr_ref_sig_restrict                funpre
% 19.32/3.02  --abstr_ref_af_restrict_to_split_sk     false
% 19.32/3.02  --abstr_ref_under                       []
% 19.32/3.02  
% 19.32/3.02  ------ SAT Options
% 19.32/3.02  
% 19.32/3.02  --sat_mode                              false
% 19.32/3.02  --sat_fm_restart_options                ""
% 19.32/3.02  --sat_gr_def                            false
% 19.32/3.02  --sat_epr_types                         true
% 19.32/3.02  --sat_non_cyclic_types                  false
% 19.32/3.02  --sat_finite_models                     false
% 19.32/3.02  --sat_fm_lemmas                         false
% 19.32/3.02  --sat_fm_prep                           false
% 19.32/3.02  --sat_fm_uc_incr                        true
% 19.32/3.02  --sat_out_model                         small
% 19.32/3.02  --sat_out_clauses                       false
% 19.32/3.02  
% 19.32/3.02  ------ QBF Options
% 19.32/3.02  
% 19.32/3.02  --qbf_mode                              false
% 19.32/3.02  --qbf_elim_univ                         false
% 19.32/3.02  --qbf_dom_inst                          none
% 19.32/3.02  --qbf_dom_pre_inst                      false
% 19.32/3.02  --qbf_sk_in                             false
% 19.32/3.02  --qbf_pred_elim                         true
% 19.32/3.02  --qbf_split                             512
% 19.32/3.02  
% 19.32/3.02  ------ BMC1 Options
% 19.32/3.02  
% 19.32/3.02  --bmc1_incremental                      false
% 19.32/3.02  --bmc1_axioms                           reachable_all
% 19.32/3.02  --bmc1_min_bound                        0
% 19.32/3.02  --bmc1_max_bound                        -1
% 19.32/3.02  --bmc1_max_bound_default                -1
% 19.32/3.02  --bmc1_symbol_reachability              true
% 19.32/3.02  --bmc1_property_lemmas                  false
% 19.32/3.02  --bmc1_k_induction                      false
% 19.32/3.02  --bmc1_non_equiv_states                 false
% 19.32/3.02  --bmc1_deadlock                         false
% 19.32/3.02  --bmc1_ucm                              false
% 19.32/3.02  --bmc1_add_unsat_core                   none
% 19.32/3.02  --bmc1_unsat_core_children              false
% 19.32/3.02  --bmc1_unsat_core_extrapolate_axioms    false
% 19.32/3.02  --bmc1_out_stat                         full
% 19.32/3.02  --bmc1_ground_init                      false
% 19.32/3.02  --bmc1_pre_inst_next_state              false
% 19.32/3.02  --bmc1_pre_inst_state                   false
% 19.32/3.02  --bmc1_pre_inst_reach_state             false
% 19.32/3.02  --bmc1_out_unsat_core                   false
% 19.32/3.02  --bmc1_aig_witness_out                  false
% 19.32/3.02  --bmc1_verbose                          false
% 19.32/3.02  --bmc1_dump_clauses_tptp                false
% 19.32/3.02  --bmc1_dump_unsat_core_tptp             false
% 19.32/3.02  --bmc1_dump_file                        -
% 19.32/3.02  --bmc1_ucm_expand_uc_limit              128
% 19.32/3.02  --bmc1_ucm_n_expand_iterations          6
% 19.32/3.02  --bmc1_ucm_extend_mode                  1
% 19.32/3.02  --bmc1_ucm_init_mode                    2
% 19.32/3.02  --bmc1_ucm_cone_mode                    none
% 19.32/3.02  --bmc1_ucm_reduced_relation_type        0
% 19.32/3.02  --bmc1_ucm_relax_model                  4
% 19.32/3.02  --bmc1_ucm_full_tr_after_sat            true
% 19.32/3.02  --bmc1_ucm_expand_neg_assumptions       false
% 19.32/3.02  --bmc1_ucm_layered_model                none
% 19.32/3.02  --bmc1_ucm_max_lemma_size               10
% 19.32/3.02  
% 19.32/3.02  ------ AIG Options
% 19.32/3.02  
% 19.32/3.02  --aig_mode                              false
% 19.32/3.02  
% 19.32/3.02  ------ Instantiation Options
% 19.32/3.02  
% 19.32/3.02  --instantiation_flag                    true
% 19.32/3.02  --inst_sos_flag                         false
% 19.32/3.02  --inst_sos_phase                        true
% 19.32/3.02  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 19.32/3.02  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 19.32/3.02  --inst_lit_sel_side                     none
% 19.32/3.02  --inst_solver_per_active                1400
% 19.32/3.02  --inst_solver_calls_frac                1.
% 19.32/3.02  --inst_passive_queue_type               priority_queues
% 19.32/3.02  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 19.32/3.02  --inst_passive_queues_freq              [25;2]
% 19.32/3.02  --inst_dismatching                      true
% 19.32/3.02  --inst_eager_unprocessed_to_passive     true
% 19.32/3.02  --inst_prop_sim_given                   true
% 19.32/3.02  --inst_prop_sim_new                     false
% 19.32/3.02  --inst_subs_new                         false
% 19.32/3.02  --inst_eq_res_simp                      false
% 19.32/3.02  --inst_subs_given                       false
% 19.32/3.02  --inst_orphan_elimination               true
% 19.32/3.02  --inst_learning_loop_flag               true
% 19.32/3.02  --inst_learning_start                   3000
% 19.32/3.02  --inst_learning_factor                  2
% 19.32/3.02  --inst_start_prop_sim_after_learn       3
% 19.32/3.02  --inst_sel_renew                        solver
% 19.32/3.02  --inst_lit_activity_flag                true
% 19.32/3.02  --inst_restr_to_given                   false
% 19.32/3.02  --inst_activity_threshold               500
% 19.32/3.02  --inst_out_proof                        true
% 19.32/3.02  
% 19.32/3.02  ------ Resolution Options
% 19.32/3.02  
% 19.32/3.02  --resolution_flag                       false
% 19.32/3.02  --res_lit_sel                           adaptive
% 19.32/3.02  --res_lit_sel_side                      none
% 19.32/3.02  --res_ordering                          kbo
% 19.32/3.02  --res_to_prop_solver                    active
% 19.32/3.02  --res_prop_simpl_new                    false
% 19.32/3.02  --res_prop_simpl_given                  true
% 19.32/3.02  --res_passive_queue_type                priority_queues
% 19.32/3.02  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 19.32/3.02  --res_passive_queues_freq               [15;5]
% 19.32/3.02  --res_forward_subs                      full
% 19.32/3.02  --res_backward_subs                     full
% 19.32/3.02  --res_forward_subs_resolution           true
% 19.32/3.02  --res_backward_subs_resolution          true
% 19.32/3.02  --res_orphan_elimination                true
% 19.32/3.02  --res_time_limit                        2.
% 19.32/3.02  --res_out_proof                         true
% 19.32/3.02  
% 19.32/3.02  ------ Superposition Options
% 19.32/3.02  
% 19.32/3.02  --superposition_flag                    true
% 19.32/3.02  --sup_passive_queue_type                priority_queues
% 19.32/3.02  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 19.32/3.02  --sup_passive_queues_freq               [8;1;4]
% 19.32/3.02  --demod_completeness_check              fast
% 19.32/3.02  --demod_use_ground                      true
% 19.32/3.02  --sup_to_prop_solver                    passive
% 19.32/3.02  --sup_prop_simpl_new                    true
% 19.32/3.02  --sup_prop_simpl_given                  true
% 19.32/3.02  --sup_fun_splitting                     false
% 19.32/3.02  --sup_smt_interval                      50000
% 19.32/3.02  
% 19.32/3.02  ------ Superposition Simplification Setup
% 19.32/3.02  
% 19.32/3.02  --sup_indices_passive                   []
% 19.32/3.02  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 19.32/3.02  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 19.32/3.02  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 19.32/3.02  --sup_full_triv                         [TrivRules;PropSubs]
% 19.32/3.02  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 19.32/3.02  --sup_full_bw                           [BwDemod]
% 19.32/3.02  --sup_immed_triv                        [TrivRules]
% 19.32/3.02  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 19.32/3.02  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 19.32/3.02  --sup_immed_bw_main                     []
% 19.32/3.02  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 19.32/3.02  --sup_input_triv                        [Unflattening;TrivRules]
% 19.32/3.02  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 19.32/3.02  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 19.32/3.02  
% 19.32/3.02  ------ Combination Options
% 19.32/3.02  
% 19.32/3.02  --comb_res_mult                         3
% 19.32/3.02  --comb_sup_mult                         2
% 19.32/3.02  --comb_inst_mult                        10
% 19.32/3.02  
% 19.32/3.02  ------ Debug Options
% 19.32/3.02  
% 19.32/3.02  --dbg_backtrace                         false
% 19.32/3.02  --dbg_dump_prop_clauses                 false
% 19.32/3.02  --dbg_dump_prop_clauses_file            -
% 19.32/3.02  --dbg_out_stat                          false
% 19.32/3.02  
% 19.32/3.02  
% 19.32/3.02  
% 19.32/3.02  
% 19.32/3.02  ------ Proving...
% 19.32/3.02  
% 19.32/3.02  
% 19.32/3.02  % SZS status Theorem for theBenchmark.p
% 19.32/3.02  
% 19.32/3.02  % SZS output start CNFRefutation for theBenchmark.p
% 19.32/3.02  
% 19.32/3.02  fof(f1,axiom,(
% 19.32/3.02    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X0) => r2_hidden(X2,X1)))),
% 19.32/3.02    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 19.32/3.02  
% 19.32/3.02  fof(f22,plain,(
% 19.32/3.02    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X1) | ~r2_hidden(X2,X0)))),
% 19.32/3.02    inference(ennf_transformation,[],[f1])).
% 19.32/3.02  
% 19.32/3.02  fof(f42,plain,(
% 19.32/3.02    ! [X0,X1] : ((r1_tarski(X0,X1) | ? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0))) & (! [X2] : (r2_hidden(X2,X1) | ~r2_hidden(X2,X0)) | ~r1_tarski(X0,X1)))),
% 19.32/3.02    inference(nnf_transformation,[],[f22])).
% 19.32/3.02  
% 19.32/3.02  fof(f43,plain,(
% 19.32/3.02    ! [X0,X1] : ((r1_tarski(X0,X1) | ? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0))) & (! [X3] : (r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) | ~r1_tarski(X0,X1)))),
% 19.32/3.02    inference(rectify,[],[f42])).
% 19.32/3.02  
% 19.32/3.02  fof(f44,plain,(
% 19.32/3.02    ! [X1,X0] : (? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0)) => (~r2_hidden(sK0(X0,X1),X1) & r2_hidden(sK0(X0,X1),X0)))),
% 19.32/3.02    introduced(choice_axiom,[])).
% 19.32/3.02  
% 19.32/3.02  fof(f45,plain,(
% 19.32/3.02    ! [X0,X1] : ((r1_tarski(X0,X1) | (~r2_hidden(sK0(X0,X1),X1) & r2_hidden(sK0(X0,X1),X0))) & (! [X3] : (r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) | ~r1_tarski(X0,X1)))),
% 19.32/3.02    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f43,f44])).
% 19.32/3.02  
% 19.32/3.02  fof(f70,plain,(
% 19.32/3.02    ( ! [X0,X1] : (r1_tarski(X0,X1) | r2_hidden(sK0(X0,X1),X0)) )),
% 19.32/3.02    inference(cnf_transformation,[],[f45])).
% 19.32/3.02  
% 19.32/3.02  fof(f4,axiom,(
% 19.32/3.02    ! [X0,X1] : (r2_hidden(X0,X1) => m1_subset_1(X0,X1))),
% 19.32/3.02    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 19.32/3.02  
% 19.32/3.02  fof(f23,plain,(
% 19.32/3.02    ! [X0,X1] : (m1_subset_1(X0,X1) | ~r2_hidden(X0,X1))),
% 19.32/3.02    inference(ennf_transformation,[],[f4])).
% 19.32/3.02  
% 19.32/3.02  fof(f76,plain,(
% 19.32/3.02    ( ! [X0,X1] : (m1_subset_1(X0,X1) | ~r2_hidden(X0,X1)) )),
% 19.32/3.02    inference(cnf_transformation,[],[f23])).
% 19.32/3.02  
% 19.32/3.02  fof(f10,axiom,(
% 19.32/3.02    ! [X0] : (l1_orders_2(X0) => k3_yellow_0(X0) = k1_yellow_0(X0,k1_xboole_0))),
% 19.32/3.02    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 19.32/3.02  
% 19.32/3.02  fof(f31,plain,(
% 19.32/3.02    ! [X0] : (k3_yellow_0(X0) = k1_yellow_0(X0,k1_xboole_0) | ~l1_orders_2(X0))),
% 19.32/3.02    inference(ennf_transformation,[],[f10])).
% 19.32/3.02  
% 19.32/3.02  fof(f86,plain,(
% 19.32/3.02    ( ! [X0] : (k3_yellow_0(X0) = k1_yellow_0(X0,k1_xboole_0) | ~l1_orders_2(X0)) )),
% 19.32/3.02    inference(cnf_transformation,[],[f31])).
% 19.32/3.02  
% 19.32/3.02  fof(f16,conjecture,(
% 19.32/3.02    ! [X0] : ((l1_orders_2(X0) & v1_yellow_0(X0) & v5_orders_2(X0) & v4_orders_2(X0) & v3_orders_2(X0) & ~v2_struct_0(X0)) => ! [X1] : ((m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & v13_waybel_0(X1,X0) & v2_waybel_0(X1,X0) & ~v1_xboole_0(X1)) => (v1_subset_1(X1,u1_struct_0(X0)) <=> ~r2_hidden(k3_yellow_0(X0),X1))))),
% 19.32/3.02    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 19.32/3.02  
% 19.32/3.02  fof(f17,negated_conjecture,(
% 19.32/3.02    ~! [X0] : ((l1_orders_2(X0) & v1_yellow_0(X0) & v5_orders_2(X0) & v4_orders_2(X0) & v3_orders_2(X0) & ~v2_struct_0(X0)) => ! [X1] : ((m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & v13_waybel_0(X1,X0) & v2_waybel_0(X1,X0) & ~v1_xboole_0(X1)) => (v1_subset_1(X1,u1_struct_0(X0)) <=> ~r2_hidden(k3_yellow_0(X0),X1))))),
% 19.32/3.02    inference(negated_conjecture,[],[f16])).
% 19.32/3.02  
% 19.32/3.02  fof(f18,plain,(
% 19.32/3.02    ~! [X0] : ((l1_orders_2(X0) & v1_yellow_0(X0) & v5_orders_2(X0) & v4_orders_2(X0) & v3_orders_2(X0) & ~v2_struct_0(X0)) => ! [X1] : ((m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & v13_waybel_0(X1,X0) & ~v1_xboole_0(X1)) => (v1_subset_1(X1,u1_struct_0(X0)) <=> ~r2_hidden(k3_yellow_0(X0),X1))))),
% 19.32/3.02    inference(pure_predicate_removal,[],[f17])).
% 19.32/3.02  
% 19.32/3.02  fof(f19,plain,(
% 19.32/3.02    ~! [X0] : ((l1_orders_2(X0) & v1_yellow_0(X0) & v5_orders_2(X0) & v3_orders_2(X0) & ~v2_struct_0(X0)) => ! [X1] : ((m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & v13_waybel_0(X1,X0) & ~v1_xboole_0(X1)) => (v1_subset_1(X1,u1_struct_0(X0)) <=> ~r2_hidden(k3_yellow_0(X0),X1))))),
% 19.32/3.02    inference(pure_predicate_removal,[],[f18])).
% 19.32/3.02  
% 19.32/3.02  fof(f20,plain,(
% 19.32/3.02    ~! [X0] : ((l1_orders_2(X0) & v1_yellow_0(X0) & v5_orders_2(X0) & ~v2_struct_0(X0)) => ! [X1] : ((m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & v13_waybel_0(X1,X0) & ~v1_xboole_0(X1)) => (v1_subset_1(X1,u1_struct_0(X0)) <=> ~r2_hidden(k3_yellow_0(X0),X1))))),
% 19.32/3.02    inference(pure_predicate_removal,[],[f19])).
% 19.32/3.02  
% 19.32/3.02  fof(f40,plain,(
% 19.32/3.02    ? [X0] : (? [X1] : ((v1_subset_1(X1,u1_struct_0(X0)) <~> ~r2_hidden(k3_yellow_0(X0),X1)) & (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & v13_waybel_0(X1,X0) & ~v1_xboole_0(X1))) & (l1_orders_2(X0) & v1_yellow_0(X0) & v5_orders_2(X0) & ~v2_struct_0(X0)))),
% 19.32/3.02    inference(ennf_transformation,[],[f20])).
% 19.32/3.02  
% 19.32/3.02  fof(f41,plain,(
% 19.32/3.02    ? [X0] : (? [X1] : ((v1_subset_1(X1,u1_struct_0(X0)) <~> ~r2_hidden(k3_yellow_0(X0),X1)) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & v13_waybel_0(X1,X0) & ~v1_xboole_0(X1)) & l1_orders_2(X0) & v1_yellow_0(X0) & v5_orders_2(X0) & ~v2_struct_0(X0))),
% 19.32/3.02    inference(flattening,[],[f40])).
% 19.32/3.02  
% 19.32/3.02  fof(f64,plain,(
% 19.32/3.02    ? [X0] : (? [X1] : (((r2_hidden(k3_yellow_0(X0),X1) | ~v1_subset_1(X1,u1_struct_0(X0))) & (~r2_hidden(k3_yellow_0(X0),X1) | v1_subset_1(X1,u1_struct_0(X0)))) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & v13_waybel_0(X1,X0) & ~v1_xboole_0(X1)) & l1_orders_2(X0) & v1_yellow_0(X0) & v5_orders_2(X0) & ~v2_struct_0(X0))),
% 19.32/3.02    inference(nnf_transformation,[],[f41])).
% 19.32/3.02  
% 19.32/3.02  fof(f65,plain,(
% 19.32/3.02    ? [X0] : (? [X1] : ((r2_hidden(k3_yellow_0(X0),X1) | ~v1_subset_1(X1,u1_struct_0(X0))) & (~r2_hidden(k3_yellow_0(X0),X1) | v1_subset_1(X1,u1_struct_0(X0))) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & v13_waybel_0(X1,X0) & ~v1_xboole_0(X1)) & l1_orders_2(X0) & v1_yellow_0(X0) & v5_orders_2(X0) & ~v2_struct_0(X0))),
% 19.32/3.02    inference(flattening,[],[f64])).
% 19.32/3.02  
% 19.32/3.02  fof(f67,plain,(
% 19.32/3.02    ( ! [X0] : (? [X1] : ((r2_hidden(k3_yellow_0(X0),X1) | ~v1_subset_1(X1,u1_struct_0(X0))) & (~r2_hidden(k3_yellow_0(X0),X1) | v1_subset_1(X1,u1_struct_0(X0))) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & v13_waybel_0(X1,X0) & ~v1_xboole_0(X1)) => ((r2_hidden(k3_yellow_0(X0),sK6) | ~v1_subset_1(sK6,u1_struct_0(X0))) & (~r2_hidden(k3_yellow_0(X0),sK6) | v1_subset_1(sK6,u1_struct_0(X0))) & m1_subset_1(sK6,k1_zfmisc_1(u1_struct_0(X0))) & v13_waybel_0(sK6,X0) & ~v1_xboole_0(sK6))) )),
% 19.32/3.02    introduced(choice_axiom,[])).
% 19.32/3.02  
% 19.32/3.02  fof(f66,plain,(
% 19.32/3.02    ? [X0] : (? [X1] : ((r2_hidden(k3_yellow_0(X0),X1) | ~v1_subset_1(X1,u1_struct_0(X0))) & (~r2_hidden(k3_yellow_0(X0),X1) | v1_subset_1(X1,u1_struct_0(X0))) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & v13_waybel_0(X1,X0) & ~v1_xboole_0(X1)) & l1_orders_2(X0) & v1_yellow_0(X0) & v5_orders_2(X0) & ~v2_struct_0(X0)) => (? [X1] : ((r2_hidden(k3_yellow_0(sK5),X1) | ~v1_subset_1(X1,u1_struct_0(sK5))) & (~r2_hidden(k3_yellow_0(sK5),X1) | v1_subset_1(X1,u1_struct_0(sK5))) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK5))) & v13_waybel_0(X1,sK5) & ~v1_xboole_0(X1)) & l1_orders_2(sK5) & v1_yellow_0(sK5) & v5_orders_2(sK5) & ~v2_struct_0(sK5))),
% 19.32/3.02    introduced(choice_axiom,[])).
% 19.32/3.02  
% 19.32/3.02  fof(f68,plain,(
% 19.32/3.02    ((r2_hidden(k3_yellow_0(sK5),sK6) | ~v1_subset_1(sK6,u1_struct_0(sK5))) & (~r2_hidden(k3_yellow_0(sK5),sK6) | v1_subset_1(sK6,u1_struct_0(sK5))) & m1_subset_1(sK6,k1_zfmisc_1(u1_struct_0(sK5))) & v13_waybel_0(sK6,sK5) & ~v1_xboole_0(sK6)) & l1_orders_2(sK5) & v1_yellow_0(sK5) & v5_orders_2(sK5) & ~v2_struct_0(sK5)),
% 19.32/3.02    inference(skolemisation,[status(esa),new_symbols(skolem,[sK5,sK6])],[f65,f67,f66])).
% 19.32/3.02  
% 19.32/3.02  fof(f105,plain,(
% 19.32/3.02    l1_orders_2(sK5)),
% 19.32/3.02    inference(cnf_transformation,[],[f68])).
% 19.32/3.02  
% 19.32/3.02  fof(f12,axiom,(
% 19.32/3.02    ! [X0,X1] : (l1_orders_2(X0) => m1_subset_1(k1_yellow_0(X0,X1),u1_struct_0(X0)))),
% 19.32/3.02    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 19.32/3.02  
% 19.32/3.02  fof(f34,plain,(
% 19.32/3.02    ! [X0,X1] : (m1_subset_1(k1_yellow_0(X0,X1),u1_struct_0(X0)) | ~l1_orders_2(X0))),
% 19.32/3.02    inference(ennf_transformation,[],[f12])).
% 19.32/3.02  
% 19.32/3.02  fof(f92,plain,(
% 19.32/3.02    ( ! [X0,X1] : (m1_subset_1(k1_yellow_0(X0,X1),u1_struct_0(X0)) | ~l1_orders_2(X0)) )),
% 19.32/3.02    inference(cnf_transformation,[],[f34])).
% 19.32/3.02  
% 19.32/3.02  fof(f5,axiom,(
% 19.32/3.02    ! [X0,X1] : (m1_subset_1(X0,X1) => (r2_hidden(X0,X1) | v1_xboole_0(X1)))),
% 19.32/3.02    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 19.32/3.02  
% 19.32/3.02  fof(f24,plain,(
% 19.32/3.02    ! [X0,X1] : ((r2_hidden(X0,X1) | v1_xboole_0(X1)) | ~m1_subset_1(X0,X1))),
% 19.32/3.02    inference(ennf_transformation,[],[f5])).
% 19.32/3.02  
% 19.32/3.02  fof(f25,plain,(
% 19.32/3.02    ! [X0,X1] : (r2_hidden(X0,X1) | v1_xboole_0(X1) | ~m1_subset_1(X0,X1))),
% 19.32/3.02    inference(flattening,[],[f24])).
% 19.32/3.02  
% 19.32/3.02  fof(f77,plain,(
% 19.32/3.02    ( ! [X0,X1] : (r2_hidden(X0,X1) | v1_xboole_0(X1) | ~m1_subset_1(X0,X1)) )),
% 19.32/3.02    inference(cnf_transformation,[],[f25])).
% 19.32/3.02  
% 19.32/3.02  fof(f106,plain,(
% 19.32/3.02    ~v1_xboole_0(sK6)),
% 19.32/3.02    inference(cnf_transformation,[],[f68])).
% 19.32/3.02  
% 19.32/3.02  fof(f108,plain,(
% 19.32/3.02    m1_subset_1(sK6,k1_zfmisc_1(u1_struct_0(sK5)))),
% 19.32/3.02    inference(cnf_transformation,[],[f68])).
% 19.32/3.02  
% 19.32/3.02  fof(f15,axiom,(
% 19.32/3.02    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => (v1_subset_1(X1,X0) <=> X0 != X1))),
% 19.32/3.02    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 19.32/3.02  
% 19.32/3.02  fof(f39,plain,(
% 19.32/3.02    ! [X0,X1] : ((v1_subset_1(X1,X0) <=> X0 != X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 19.32/3.02    inference(ennf_transformation,[],[f15])).
% 19.32/3.02  
% 19.32/3.02  fof(f63,plain,(
% 19.32/3.02    ! [X0,X1] : (((v1_subset_1(X1,X0) | X0 = X1) & (X0 != X1 | ~v1_subset_1(X1,X0))) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 19.32/3.02    inference(nnf_transformation,[],[f39])).
% 19.32/3.02  
% 19.32/3.02  fof(f101,plain,(
% 19.32/3.02    ( ! [X0,X1] : (v1_subset_1(X1,X0) | X0 = X1 | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 19.32/3.02    inference(cnf_transformation,[],[f63])).
% 19.32/3.02  
% 19.32/3.02  fof(f6,axiom,(
% 19.32/3.02    ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) <=> r1_tarski(X0,X1))),
% 19.32/3.02    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 19.32/3.02  
% 19.32/3.02  fof(f48,plain,(
% 19.32/3.02    ! [X0,X1] : ((m1_subset_1(X0,k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1)) & (r1_tarski(X0,X1) | ~m1_subset_1(X0,k1_zfmisc_1(X1))))),
% 19.32/3.02    inference(nnf_transformation,[],[f6])).
% 19.32/3.02  
% 19.32/3.02  fof(f79,plain,(
% 19.32/3.02    ( ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1)) )),
% 19.32/3.02    inference(cnf_transformation,[],[f48])).
% 19.32/3.02  
% 19.32/3.02  fof(f110,plain,(
% 19.32/3.02    r2_hidden(k3_yellow_0(sK5),sK6) | ~v1_subset_1(sK6,u1_struct_0(sK5))),
% 19.32/3.02    inference(cnf_transformation,[],[f68])).
% 19.32/3.02  
% 19.32/3.02  fof(f78,plain,(
% 19.32/3.02    ( ! [X0,X1] : (r1_tarski(X0,X1) | ~m1_subset_1(X0,k1_zfmisc_1(X1))) )),
% 19.32/3.02    inference(cnf_transformation,[],[f48])).
% 19.32/3.02  
% 19.32/3.02  fof(f8,axiom,(
% 19.32/3.02    ! [X0,X1,X2] : ~(v1_xboole_0(X2) & m1_subset_1(X1,k1_zfmisc_1(X2)) & r2_hidden(X0,X1))),
% 19.32/3.02    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 19.32/3.02  
% 19.32/3.02  fof(f28,plain,(
% 19.32/3.02    ! [X0,X1,X2] : (~v1_xboole_0(X2) | ~m1_subset_1(X1,k1_zfmisc_1(X2)) | ~r2_hidden(X0,X1))),
% 19.32/3.02    inference(ennf_transformation,[],[f8])).
% 19.32/3.02  
% 19.32/3.02  fof(f81,plain,(
% 19.32/3.02    ( ! [X2,X0,X1] : (~v1_xboole_0(X2) | ~m1_subset_1(X1,k1_zfmisc_1(X2)) | ~r2_hidden(X0,X1)) )),
% 19.32/3.02    inference(cnf_transformation,[],[f28])).
% 19.32/3.02  
% 19.32/3.02  fof(f69,plain,(
% 19.32/3.02    ( ! [X0,X3,X1] : (r2_hidden(X3,X1) | ~r2_hidden(X3,X0) | ~r1_tarski(X0,X1)) )),
% 19.32/3.02    inference(cnf_transformation,[],[f45])).
% 19.32/3.02  
% 19.32/3.02  fof(f14,axiom,(
% 19.32/3.02    ! [X0] : (l1_orders_2(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => (v13_waybel_0(X1,X0) <=> ! [X2] : (m1_subset_1(X2,u1_struct_0(X0)) => ! [X3] : (m1_subset_1(X3,u1_struct_0(X0)) => ((r1_orders_2(X0,X2,X3) & r2_hidden(X2,X1)) => r2_hidden(X3,X1)))))))),
% 19.32/3.02    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 19.32/3.02  
% 19.32/3.02  fof(f37,plain,(
% 19.32/3.02    ! [X0] : (! [X1] : ((v13_waybel_0(X1,X0) <=> ! [X2] : (! [X3] : ((r2_hidden(X3,X1) | (~r1_orders_2(X0,X2,X3) | ~r2_hidden(X2,X1))) | ~m1_subset_1(X3,u1_struct_0(X0))) | ~m1_subset_1(X2,u1_struct_0(X0)))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_orders_2(X0))),
% 19.32/3.02    inference(ennf_transformation,[],[f14])).
% 19.32/3.02  
% 19.32/3.02  fof(f38,plain,(
% 19.32/3.02    ! [X0] : (! [X1] : ((v13_waybel_0(X1,X0) <=> ! [X2] : (! [X3] : (r2_hidden(X3,X1) | ~r1_orders_2(X0,X2,X3) | ~r2_hidden(X2,X1) | ~m1_subset_1(X3,u1_struct_0(X0))) | ~m1_subset_1(X2,u1_struct_0(X0)))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_orders_2(X0))),
% 19.32/3.02    inference(flattening,[],[f37])).
% 19.32/3.02  
% 19.32/3.02  fof(f58,plain,(
% 19.32/3.02    ! [X0] : (! [X1] : (((v13_waybel_0(X1,X0) | ? [X2] : (? [X3] : (~r2_hidden(X3,X1) & r1_orders_2(X0,X2,X3) & r2_hidden(X2,X1) & m1_subset_1(X3,u1_struct_0(X0))) & m1_subset_1(X2,u1_struct_0(X0)))) & (! [X2] : (! [X3] : (r2_hidden(X3,X1) | ~r1_orders_2(X0,X2,X3) | ~r2_hidden(X2,X1) | ~m1_subset_1(X3,u1_struct_0(X0))) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~v13_waybel_0(X1,X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_orders_2(X0))),
% 19.32/3.02    inference(nnf_transformation,[],[f38])).
% 19.32/3.02  
% 19.32/3.02  fof(f59,plain,(
% 19.32/3.02    ! [X0] : (! [X1] : (((v13_waybel_0(X1,X0) | ? [X2] : (? [X3] : (~r2_hidden(X3,X1) & r1_orders_2(X0,X2,X3) & r2_hidden(X2,X1) & m1_subset_1(X3,u1_struct_0(X0))) & m1_subset_1(X2,u1_struct_0(X0)))) & (! [X4] : (! [X5] : (r2_hidden(X5,X1) | ~r1_orders_2(X0,X4,X5) | ~r2_hidden(X4,X1) | ~m1_subset_1(X5,u1_struct_0(X0))) | ~m1_subset_1(X4,u1_struct_0(X0))) | ~v13_waybel_0(X1,X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_orders_2(X0))),
% 19.32/3.02    inference(rectify,[],[f58])).
% 19.32/3.02  
% 19.32/3.02  fof(f61,plain,(
% 19.32/3.02    ( ! [X2] : (! [X1,X0] : (? [X3] : (~r2_hidden(X3,X1) & r1_orders_2(X0,X2,X3) & r2_hidden(X2,X1) & m1_subset_1(X3,u1_struct_0(X0))) => (~r2_hidden(sK4(X0,X1),X1) & r1_orders_2(X0,X2,sK4(X0,X1)) & r2_hidden(X2,X1) & m1_subset_1(sK4(X0,X1),u1_struct_0(X0))))) )),
% 19.32/3.02    introduced(choice_axiom,[])).
% 19.32/3.02  
% 19.32/3.02  fof(f60,plain,(
% 19.32/3.02    ! [X1,X0] : (? [X2] : (? [X3] : (~r2_hidden(X3,X1) & r1_orders_2(X0,X2,X3) & r2_hidden(X2,X1) & m1_subset_1(X3,u1_struct_0(X0))) & m1_subset_1(X2,u1_struct_0(X0))) => (? [X3] : (~r2_hidden(X3,X1) & r1_orders_2(X0,sK3(X0,X1),X3) & r2_hidden(sK3(X0,X1),X1) & m1_subset_1(X3,u1_struct_0(X0))) & m1_subset_1(sK3(X0,X1),u1_struct_0(X0))))),
% 19.32/3.02    introduced(choice_axiom,[])).
% 19.32/3.02  
% 19.32/3.02  fof(f62,plain,(
% 19.32/3.02    ! [X0] : (! [X1] : (((v13_waybel_0(X1,X0) | ((~r2_hidden(sK4(X0,X1),X1) & r1_orders_2(X0,sK3(X0,X1),sK4(X0,X1)) & r2_hidden(sK3(X0,X1),X1) & m1_subset_1(sK4(X0,X1),u1_struct_0(X0))) & m1_subset_1(sK3(X0,X1),u1_struct_0(X0)))) & (! [X4] : (! [X5] : (r2_hidden(X5,X1) | ~r1_orders_2(X0,X4,X5) | ~r2_hidden(X4,X1) | ~m1_subset_1(X5,u1_struct_0(X0))) | ~m1_subset_1(X4,u1_struct_0(X0))) | ~v13_waybel_0(X1,X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_orders_2(X0))),
% 19.32/3.02    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3,sK4])],[f59,f61,f60])).
% 19.32/3.02  
% 19.32/3.02  fof(f97,plain,(
% 19.32/3.02    ( ! [X0,X1] : (v13_waybel_0(X1,X0) | r2_hidden(sK3(X0,X1),X1) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_orders_2(X0)) )),
% 19.32/3.02    inference(cnf_transformation,[],[f62])).
% 19.32/3.02  
% 19.32/3.02  fof(f95,plain,(
% 19.32/3.02    ( ! [X0,X1] : (v13_waybel_0(X1,X0) | m1_subset_1(sK3(X0,X1),u1_struct_0(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_orders_2(X0)) )),
% 19.32/3.02    inference(cnf_transformation,[],[f62])).
% 19.32/3.02  
% 19.32/3.02  fof(f9,axiom,(
% 19.32/3.02    ! [X0] : (l1_orders_2(X0) => ! [X1,X2] : (m1_subset_1(X2,u1_struct_0(X0)) => (r2_lattice3(X0,X1,X2) <=> ! [X3] : (m1_subset_1(X3,u1_struct_0(X0)) => (r2_hidden(X3,X1) => r1_orders_2(X0,X3,X2))))))),
% 19.32/3.02    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 19.32/3.02  
% 19.32/3.02  fof(f29,plain,(
% 19.32/3.02    ! [X0] : (! [X1,X2] : ((r2_lattice3(X0,X1,X2) <=> ! [X3] : ((r1_orders_2(X0,X3,X2) | ~r2_hidden(X3,X1)) | ~m1_subset_1(X3,u1_struct_0(X0)))) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~l1_orders_2(X0))),
% 19.32/3.02    inference(ennf_transformation,[],[f9])).
% 19.32/3.02  
% 19.32/3.02  fof(f30,plain,(
% 19.32/3.02    ! [X0] : (! [X1,X2] : ((r2_lattice3(X0,X1,X2) <=> ! [X3] : (r1_orders_2(X0,X3,X2) | ~r2_hidden(X3,X1) | ~m1_subset_1(X3,u1_struct_0(X0)))) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~l1_orders_2(X0))),
% 19.32/3.02    inference(flattening,[],[f29])).
% 19.32/3.02  
% 19.32/3.02  fof(f49,plain,(
% 19.32/3.02    ! [X0] : (! [X1,X2] : (((r2_lattice3(X0,X1,X2) | ? [X3] : (~r1_orders_2(X0,X3,X2) & r2_hidden(X3,X1) & m1_subset_1(X3,u1_struct_0(X0)))) & (! [X3] : (r1_orders_2(X0,X3,X2) | ~r2_hidden(X3,X1) | ~m1_subset_1(X3,u1_struct_0(X0))) | ~r2_lattice3(X0,X1,X2))) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~l1_orders_2(X0))),
% 19.32/3.02    inference(nnf_transformation,[],[f30])).
% 19.32/3.02  
% 19.32/3.02  fof(f50,plain,(
% 19.32/3.02    ! [X0] : (! [X1,X2] : (((r2_lattice3(X0,X1,X2) | ? [X3] : (~r1_orders_2(X0,X3,X2) & r2_hidden(X3,X1) & m1_subset_1(X3,u1_struct_0(X0)))) & (! [X4] : (r1_orders_2(X0,X4,X2) | ~r2_hidden(X4,X1) | ~m1_subset_1(X4,u1_struct_0(X0))) | ~r2_lattice3(X0,X1,X2))) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~l1_orders_2(X0))),
% 19.32/3.02    inference(rectify,[],[f49])).
% 19.32/3.02  
% 19.32/3.02  fof(f51,plain,(
% 19.32/3.02    ! [X2,X1,X0] : (? [X3] : (~r1_orders_2(X0,X3,X2) & r2_hidden(X3,X1) & m1_subset_1(X3,u1_struct_0(X0))) => (~r1_orders_2(X0,sK1(X0,X1,X2),X2) & r2_hidden(sK1(X0,X1,X2),X1) & m1_subset_1(sK1(X0,X1,X2),u1_struct_0(X0))))),
% 19.32/3.02    introduced(choice_axiom,[])).
% 19.32/3.02  
% 19.32/3.02  fof(f52,plain,(
% 19.32/3.02    ! [X0] : (! [X1,X2] : (((r2_lattice3(X0,X1,X2) | (~r1_orders_2(X0,sK1(X0,X1,X2),X2) & r2_hidden(sK1(X0,X1,X2),X1) & m1_subset_1(sK1(X0,X1,X2),u1_struct_0(X0)))) & (! [X4] : (r1_orders_2(X0,X4,X2) | ~r2_hidden(X4,X1) | ~m1_subset_1(X4,u1_struct_0(X0))) | ~r2_lattice3(X0,X1,X2))) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~l1_orders_2(X0))),
% 19.32/3.02    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1])],[f50,f51])).
% 19.32/3.02  
% 19.32/3.02  fof(f82,plain,(
% 19.32/3.02    ( ! [X4,X2,X0,X1] : (r1_orders_2(X0,X4,X2) | ~r2_hidden(X4,X1) | ~m1_subset_1(X4,u1_struct_0(X0)) | ~r2_lattice3(X0,X1,X2) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~l1_orders_2(X0)) )),
% 19.32/3.02    inference(cnf_transformation,[],[f52])).
% 19.32/3.02  
% 19.32/3.02  fof(f94,plain,(
% 19.32/3.02    ( ! [X4,X0,X5,X1] : (r2_hidden(X5,X1) | ~r1_orders_2(X0,X4,X5) | ~r2_hidden(X4,X1) | ~m1_subset_1(X5,u1_struct_0(X0)) | ~m1_subset_1(X4,u1_struct_0(X0)) | ~v13_waybel_0(X1,X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_orders_2(X0)) )),
% 19.32/3.02    inference(cnf_transformation,[],[f62])).
% 19.32/3.02  
% 19.32/3.02  fof(f7,axiom,(
% 19.32/3.02    ! [X0,X1,X2] : ((m1_subset_1(X1,k1_zfmisc_1(X2)) & r2_hidden(X0,X1)) => m1_subset_1(X0,X2))),
% 19.32/3.02    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 19.32/3.02  
% 19.32/3.02  fof(f26,plain,(
% 19.32/3.02    ! [X0,X1,X2] : (m1_subset_1(X0,X2) | (~m1_subset_1(X1,k1_zfmisc_1(X2)) | ~r2_hidden(X0,X1)))),
% 19.32/3.02    inference(ennf_transformation,[],[f7])).
% 19.32/3.02  
% 19.32/3.02  fof(f27,plain,(
% 19.32/3.02    ! [X0,X1,X2] : (m1_subset_1(X0,X2) | ~m1_subset_1(X1,k1_zfmisc_1(X2)) | ~r2_hidden(X0,X1))),
% 19.32/3.02    inference(flattening,[],[f26])).
% 19.32/3.02  
% 19.32/3.02  fof(f80,plain,(
% 19.32/3.02    ( ! [X2,X0,X1] : (m1_subset_1(X0,X2) | ~m1_subset_1(X1,k1_zfmisc_1(X2)) | ~r2_hidden(X0,X1)) )),
% 19.32/3.02    inference(cnf_transformation,[],[f27])).
% 19.32/3.02  
% 19.32/3.02  fof(f107,plain,(
% 19.32/3.02    v13_waybel_0(sK6,sK5)),
% 19.32/3.02    inference(cnf_transformation,[],[f68])).
% 19.32/3.02  
% 19.32/3.02  fof(f100,plain,(
% 19.32/3.02    ( ! [X0,X1] : (X0 != X1 | ~v1_subset_1(X1,X0) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 19.32/3.02    inference(cnf_transformation,[],[f63])).
% 19.32/3.02  
% 19.32/3.02  fof(f115,plain,(
% 19.32/3.02    ( ! [X1] : (~v1_subset_1(X1,X1) | ~m1_subset_1(X1,k1_zfmisc_1(X1))) )),
% 19.32/3.02    inference(equality_resolution,[],[f100])).
% 19.32/3.02  
% 19.32/3.02  fof(f3,axiom,(
% 19.32/3.02    ! [X0,X1] : (X0 = X1 <=> (r1_tarski(X1,X0) & r1_tarski(X0,X1)))),
% 19.32/3.02    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 19.32/3.02  
% 19.32/3.02  fof(f46,plain,(
% 19.32/3.02    ! [X0,X1] : ((X0 = X1 | (~r1_tarski(X1,X0) | ~r1_tarski(X0,X1))) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 19.32/3.02    inference(nnf_transformation,[],[f3])).
% 19.32/3.02  
% 19.32/3.02  fof(f47,plain,(
% 19.32/3.02    ! [X0,X1] : ((X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 19.32/3.02    inference(flattening,[],[f46])).
% 19.32/3.02  
% 19.32/3.02  fof(f73,plain,(
% 19.32/3.02    ( ! [X0,X1] : (r1_tarski(X0,X1) | X0 != X1) )),
% 19.32/3.02    inference(cnf_transformation,[],[f47])).
% 19.32/3.02  
% 19.32/3.02  fof(f112,plain,(
% 19.32/3.02    ( ! [X1] : (r1_tarski(X1,X1)) )),
% 19.32/3.02    inference(equality_resolution,[],[f73])).
% 19.32/3.02  
% 19.32/3.02  fof(f11,axiom,(
% 19.32/3.02    ! [X0] : (l1_orders_2(X0) => ! [X1,X2] : (m1_subset_1(X2,u1_struct_0(X0)) => (r1_yellow_0(X0,X1) => (k1_yellow_0(X0,X1) = X2 <=> (! [X3] : (m1_subset_1(X3,u1_struct_0(X0)) => (r2_lattice3(X0,X1,X3) => r1_orders_2(X0,X2,X3))) & r2_lattice3(X0,X1,X2))))))),
% 19.32/3.02    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 19.32/3.02  
% 19.32/3.02  fof(f32,plain,(
% 19.32/3.02    ! [X0] : (! [X1,X2] : (((k1_yellow_0(X0,X1) = X2 <=> (! [X3] : ((r1_orders_2(X0,X2,X3) | ~r2_lattice3(X0,X1,X3)) | ~m1_subset_1(X3,u1_struct_0(X0))) & r2_lattice3(X0,X1,X2))) | ~r1_yellow_0(X0,X1)) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~l1_orders_2(X0))),
% 19.32/3.02    inference(ennf_transformation,[],[f11])).
% 19.32/3.02  
% 19.32/3.02  fof(f33,plain,(
% 19.32/3.02    ! [X0] : (! [X1,X2] : ((k1_yellow_0(X0,X1) = X2 <=> (! [X3] : (r1_orders_2(X0,X2,X3) | ~r2_lattice3(X0,X1,X3) | ~m1_subset_1(X3,u1_struct_0(X0))) & r2_lattice3(X0,X1,X2))) | ~r1_yellow_0(X0,X1) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~l1_orders_2(X0))),
% 19.32/3.02    inference(flattening,[],[f32])).
% 19.32/3.02  
% 19.32/3.02  fof(f53,plain,(
% 19.32/3.02    ! [X0] : (! [X1,X2] : (((k1_yellow_0(X0,X1) = X2 | (? [X3] : (~r1_orders_2(X0,X2,X3) & r2_lattice3(X0,X1,X3) & m1_subset_1(X3,u1_struct_0(X0))) | ~r2_lattice3(X0,X1,X2))) & ((! [X3] : (r1_orders_2(X0,X2,X3) | ~r2_lattice3(X0,X1,X3) | ~m1_subset_1(X3,u1_struct_0(X0))) & r2_lattice3(X0,X1,X2)) | k1_yellow_0(X0,X1) != X2)) | ~r1_yellow_0(X0,X1) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~l1_orders_2(X0))),
% 19.32/3.02    inference(nnf_transformation,[],[f33])).
% 19.32/3.02  
% 19.32/3.02  fof(f54,plain,(
% 19.32/3.02    ! [X0] : (! [X1,X2] : (((k1_yellow_0(X0,X1) = X2 | ? [X3] : (~r1_orders_2(X0,X2,X3) & r2_lattice3(X0,X1,X3) & m1_subset_1(X3,u1_struct_0(X0))) | ~r2_lattice3(X0,X1,X2)) & ((! [X3] : (r1_orders_2(X0,X2,X3) | ~r2_lattice3(X0,X1,X3) | ~m1_subset_1(X3,u1_struct_0(X0))) & r2_lattice3(X0,X1,X2)) | k1_yellow_0(X0,X1) != X2)) | ~r1_yellow_0(X0,X1) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~l1_orders_2(X0))),
% 19.32/3.02    inference(flattening,[],[f53])).
% 19.32/3.02  
% 19.32/3.02  fof(f55,plain,(
% 19.32/3.02    ! [X0] : (! [X1,X2] : (((k1_yellow_0(X0,X1) = X2 | ? [X3] : (~r1_orders_2(X0,X2,X3) & r2_lattice3(X0,X1,X3) & m1_subset_1(X3,u1_struct_0(X0))) | ~r2_lattice3(X0,X1,X2)) & ((! [X4] : (r1_orders_2(X0,X2,X4) | ~r2_lattice3(X0,X1,X4) | ~m1_subset_1(X4,u1_struct_0(X0))) & r2_lattice3(X0,X1,X2)) | k1_yellow_0(X0,X1) != X2)) | ~r1_yellow_0(X0,X1) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~l1_orders_2(X0))),
% 19.32/3.02    inference(rectify,[],[f54])).
% 19.32/3.02  
% 19.32/3.02  fof(f56,plain,(
% 19.32/3.02    ! [X2,X1,X0] : (? [X3] : (~r1_orders_2(X0,X2,X3) & r2_lattice3(X0,X1,X3) & m1_subset_1(X3,u1_struct_0(X0))) => (~r1_orders_2(X0,X2,sK2(X0,X1,X2)) & r2_lattice3(X0,X1,sK2(X0,X1,X2)) & m1_subset_1(sK2(X0,X1,X2),u1_struct_0(X0))))),
% 19.32/3.02    introduced(choice_axiom,[])).
% 19.32/3.02  
% 19.32/3.02  fof(f57,plain,(
% 19.32/3.02    ! [X0] : (! [X1,X2] : (((k1_yellow_0(X0,X1) = X2 | (~r1_orders_2(X0,X2,sK2(X0,X1,X2)) & r2_lattice3(X0,X1,sK2(X0,X1,X2)) & m1_subset_1(sK2(X0,X1,X2),u1_struct_0(X0))) | ~r2_lattice3(X0,X1,X2)) & ((! [X4] : (r1_orders_2(X0,X2,X4) | ~r2_lattice3(X0,X1,X4) | ~m1_subset_1(X4,u1_struct_0(X0))) & r2_lattice3(X0,X1,X2)) | k1_yellow_0(X0,X1) != X2)) | ~r1_yellow_0(X0,X1) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~l1_orders_2(X0))),
% 19.32/3.02    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2])],[f55,f56])).
% 19.32/3.02  
% 19.32/3.02  fof(f88,plain,(
% 19.32/3.02    ( ! [X4,X2,X0,X1] : (r1_orders_2(X0,X2,X4) | ~r2_lattice3(X0,X1,X4) | ~m1_subset_1(X4,u1_struct_0(X0)) | k1_yellow_0(X0,X1) != X2 | ~r1_yellow_0(X0,X1) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~l1_orders_2(X0)) )),
% 19.32/3.02    inference(cnf_transformation,[],[f57])).
% 19.32/3.02  
% 19.32/3.02  fof(f113,plain,(
% 19.32/3.02    ( ! [X4,X0,X1] : (r1_orders_2(X0,k1_yellow_0(X0,X1),X4) | ~r2_lattice3(X0,X1,X4) | ~m1_subset_1(X4,u1_struct_0(X0)) | ~r1_yellow_0(X0,X1) | ~m1_subset_1(k1_yellow_0(X0,X1),u1_struct_0(X0)) | ~l1_orders_2(X0)) )),
% 19.32/3.02    inference(equality_resolution,[],[f88])).
% 19.32/3.02  
% 19.32/3.02  fof(f13,axiom,(
% 19.32/3.02    ! [X0] : ((l1_orders_2(X0) & v1_yellow_0(X0) & v5_orders_2(X0) & ~v2_struct_0(X0)) => (r2_yellow_0(X0,u1_struct_0(X0)) & r1_yellow_0(X0,k1_xboole_0)))),
% 19.32/3.02    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 19.32/3.02  
% 19.32/3.02  fof(f21,plain,(
% 19.32/3.02    ! [X0] : ((l1_orders_2(X0) & v1_yellow_0(X0) & v5_orders_2(X0) & ~v2_struct_0(X0)) => r1_yellow_0(X0,k1_xboole_0))),
% 19.32/3.02    inference(pure_predicate_removal,[],[f13])).
% 19.32/3.02  
% 19.32/3.02  fof(f35,plain,(
% 19.32/3.02    ! [X0] : (r1_yellow_0(X0,k1_xboole_0) | (~l1_orders_2(X0) | ~v1_yellow_0(X0) | ~v5_orders_2(X0) | v2_struct_0(X0)))),
% 19.32/3.02    inference(ennf_transformation,[],[f21])).
% 19.32/3.02  
% 19.32/3.02  fof(f36,plain,(
% 19.32/3.02    ! [X0] : (r1_yellow_0(X0,k1_xboole_0) | ~l1_orders_2(X0) | ~v1_yellow_0(X0) | ~v5_orders_2(X0) | v2_struct_0(X0))),
% 19.32/3.02    inference(flattening,[],[f35])).
% 19.32/3.02  
% 19.32/3.02  fof(f93,plain,(
% 19.32/3.02    ( ! [X0] : (r1_yellow_0(X0,k1_xboole_0) | ~l1_orders_2(X0) | ~v1_yellow_0(X0) | ~v5_orders_2(X0) | v2_struct_0(X0)) )),
% 19.32/3.02    inference(cnf_transformation,[],[f36])).
% 19.32/3.02  
% 19.32/3.02  fof(f104,plain,(
% 19.32/3.02    v1_yellow_0(sK5)),
% 19.32/3.02    inference(cnf_transformation,[],[f68])).
% 19.32/3.02  
% 19.32/3.02  fof(f102,plain,(
% 19.32/3.02    ~v2_struct_0(sK5)),
% 19.32/3.02    inference(cnf_transformation,[],[f68])).
% 19.32/3.02  
% 19.32/3.02  fof(f103,plain,(
% 19.32/3.02    v5_orders_2(sK5)),
% 19.32/3.02    inference(cnf_transformation,[],[f68])).
% 19.32/3.02  
% 19.32/3.02  fof(f84,plain,(
% 19.32/3.02    ( ! [X2,X0,X1] : (r2_lattice3(X0,X1,X2) | r2_hidden(sK1(X0,X1,X2),X1) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~l1_orders_2(X0)) )),
% 19.32/3.02    inference(cnf_transformation,[],[f52])).
% 19.32/3.02  
% 19.32/3.02  fof(f87,plain,(
% 19.32/3.02    ( ! [X2,X0,X1] : (r2_lattice3(X0,X1,X2) | k1_yellow_0(X0,X1) != X2 | ~r1_yellow_0(X0,X1) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~l1_orders_2(X0)) )),
% 19.32/3.02    inference(cnf_transformation,[],[f57])).
% 19.32/3.02  
% 19.32/3.02  fof(f114,plain,(
% 19.32/3.02    ( ! [X0,X1] : (r2_lattice3(X0,X1,k1_yellow_0(X0,X1)) | ~r1_yellow_0(X0,X1) | ~m1_subset_1(k1_yellow_0(X0,X1),u1_struct_0(X0)) | ~l1_orders_2(X0)) )),
% 19.32/3.02    inference(equality_resolution,[],[f87])).
% 19.32/3.02  
% 19.32/3.02  fof(f2,axiom,(
% 19.32/3.02    v1_xboole_0(k1_xboole_0)),
% 19.32/3.02    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 19.32/3.02  
% 19.32/3.02  fof(f72,plain,(
% 19.32/3.02    v1_xboole_0(k1_xboole_0)),
% 19.32/3.02    inference(cnf_transformation,[],[f2])).
% 19.32/3.02  
% 19.32/3.02  fof(f71,plain,(
% 19.32/3.02    ( ! [X0,X1] : (r1_tarski(X0,X1) | ~r2_hidden(sK0(X0,X1),X1)) )),
% 19.32/3.02    inference(cnf_transformation,[],[f45])).
% 19.32/3.02  
% 19.32/3.02  fof(f75,plain,(
% 19.32/3.02    ( ! [X0,X1] : (X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) )),
% 19.32/3.02    inference(cnf_transformation,[],[f47])).
% 19.32/3.02  
% 19.32/3.02  fof(f109,plain,(
% 19.32/3.02    ~r2_hidden(k3_yellow_0(sK5),sK6) | v1_subset_1(sK6,u1_struct_0(sK5))),
% 19.32/3.02    inference(cnf_transformation,[],[f68])).
% 19.32/3.02  
% 19.32/3.02  cnf(c_1,plain,
% 19.32/3.02      ( r2_hidden(sK0(X0,X1),X0) | r1_tarski(X0,X1) ),
% 19.32/3.02      inference(cnf_transformation,[],[f70]) ).
% 19.32/3.02  
% 19.32/3.02  cnf(c_2946,plain,
% 19.32/3.02      ( r2_hidden(sK0(X0,X1),X0) = iProver_top
% 19.32/3.02      | r1_tarski(X0,X1) = iProver_top ),
% 19.32/3.02      inference(predicate_to_equality,[status(thm)],[c_1]) ).
% 19.32/3.02  
% 19.32/3.02  cnf(c_7,plain,
% 19.32/3.02      ( m1_subset_1(X0,X1) | ~ r2_hidden(X0,X1) ),
% 19.32/3.02      inference(cnf_transformation,[],[f76]) ).
% 19.32/3.02  
% 19.32/3.02  cnf(c_2941,plain,
% 19.32/3.02      ( m1_subset_1(X0,X1) = iProver_top
% 19.32/3.02      | r2_hidden(X0,X1) != iProver_top ),
% 19.32/3.02      inference(predicate_to_equality,[status(thm)],[c_7]) ).
% 19.32/3.02  
% 19.32/3.02  cnf(c_3965,plain,
% 19.32/3.02      ( m1_subset_1(sK0(X0,X1),X0) = iProver_top
% 19.32/3.02      | r1_tarski(X0,X1) = iProver_top ),
% 19.32/3.02      inference(superposition,[status(thm)],[c_2946,c_2941]) ).
% 19.32/3.02  
% 19.32/3.02  cnf(c_17,plain,
% 19.32/3.02      ( ~ l1_orders_2(X0)
% 19.32/3.02      | k1_yellow_0(X0,k1_xboole_0) = k3_yellow_0(X0) ),
% 19.32/3.02      inference(cnf_transformation,[],[f86]) ).
% 19.32/3.02  
% 19.32/3.02  cnf(c_38,negated_conjecture,
% 19.32/3.02      ( l1_orders_2(sK5) ),
% 19.32/3.02      inference(cnf_transformation,[],[f105]) ).
% 19.32/3.02  
% 19.32/3.02  cnf(c_839,plain,
% 19.32/3.02      ( k1_yellow_0(X0,k1_xboole_0) = k3_yellow_0(X0) | sK5 != X0 ),
% 19.32/3.02      inference(resolution_lifted,[status(thm)],[c_17,c_38]) ).
% 19.32/3.02  
% 19.32/3.02  cnf(c_840,plain,
% 19.32/3.02      ( k1_yellow_0(sK5,k1_xboole_0) = k3_yellow_0(sK5) ),
% 19.32/3.02      inference(unflattening,[status(thm)],[c_839]) ).
% 19.32/3.02  
% 19.32/3.02  cnf(c_23,plain,
% 19.32/3.02      ( m1_subset_1(k1_yellow_0(X0,X1),u1_struct_0(X0))
% 19.32/3.02      | ~ l1_orders_2(X0) ),
% 19.32/3.02      inference(cnf_transformation,[],[f92]) ).
% 19.32/3.02  
% 19.32/3.02  cnf(c_830,plain,
% 19.32/3.02      ( m1_subset_1(k1_yellow_0(X0,X1),u1_struct_0(X0)) | sK5 != X0 ),
% 19.32/3.02      inference(resolution_lifted,[status(thm)],[c_23,c_38]) ).
% 19.32/3.02  
% 19.32/3.02  cnf(c_831,plain,
% 19.32/3.02      ( m1_subset_1(k1_yellow_0(sK5,X0),u1_struct_0(sK5)) ),
% 19.32/3.02      inference(unflattening,[status(thm)],[c_830]) ).
% 19.32/3.02  
% 19.32/3.02  cnf(c_2923,plain,
% 19.32/3.02      ( m1_subset_1(k1_yellow_0(sK5,X0),u1_struct_0(sK5)) = iProver_top ),
% 19.32/3.02      inference(predicate_to_equality,[status(thm)],[c_831]) ).
% 19.32/3.02  
% 19.32/3.02  cnf(c_8,plain,
% 19.32/3.02      ( ~ m1_subset_1(X0,X1) | r2_hidden(X0,X1) | v1_xboole_0(X1) ),
% 19.32/3.02      inference(cnf_transformation,[],[f77]) ).
% 19.32/3.02  
% 19.32/3.02  cnf(c_2940,plain,
% 19.32/3.02      ( m1_subset_1(X0,X1) != iProver_top
% 19.32/3.02      | r2_hidden(X0,X1) = iProver_top
% 19.32/3.02      | v1_xboole_0(X1) = iProver_top ),
% 19.32/3.02      inference(predicate_to_equality,[status(thm)],[c_8]) ).
% 19.32/3.02  
% 19.32/3.02  cnf(c_4030,plain,
% 19.32/3.02      ( r2_hidden(k1_yellow_0(sK5,X0),u1_struct_0(sK5)) = iProver_top
% 19.32/3.02      | v1_xboole_0(u1_struct_0(sK5)) = iProver_top ),
% 19.32/3.02      inference(superposition,[status(thm)],[c_2923,c_2940]) ).
% 19.32/3.02  
% 19.32/3.02  cnf(c_37,negated_conjecture,
% 19.32/3.02      ( ~ v1_xboole_0(sK6) ),
% 19.32/3.02      inference(cnf_transformation,[],[f106]) ).
% 19.32/3.02  
% 19.32/3.02  cnf(c_46,plain,
% 19.32/3.02      ( v1_xboole_0(sK6) != iProver_top ),
% 19.32/3.02      inference(predicate_to_equality,[status(thm)],[c_37]) ).
% 19.32/3.02  
% 19.32/3.02  cnf(c_35,negated_conjecture,
% 19.32/3.02      ( m1_subset_1(sK6,k1_zfmisc_1(u1_struct_0(sK5))) ),
% 19.32/3.02      inference(cnf_transformation,[],[f108]) ).
% 19.32/3.02  
% 19.32/3.02  cnf(c_48,plain,
% 19.32/3.02      ( m1_subset_1(sK6,k1_zfmisc_1(u1_struct_0(sK5))) = iProver_top ),
% 19.32/3.02      inference(predicate_to_equality,[status(thm)],[c_35]) ).
% 19.32/3.02  
% 19.32/3.02  cnf(c_31,plain,
% 19.32/3.02      ( v1_subset_1(X0,X1)
% 19.32/3.02      | ~ m1_subset_1(X0,k1_zfmisc_1(X1))
% 19.32/3.02      | X0 = X1 ),
% 19.32/3.02      inference(cnf_transformation,[],[f101]) ).
% 19.32/3.02  
% 19.32/3.02  cnf(c_9,plain,
% 19.32/3.02      ( m1_subset_1(X0,k1_zfmisc_1(X1)) | ~ r1_tarski(X0,X1) ),
% 19.32/3.02      inference(cnf_transformation,[],[f79]) ).
% 19.32/3.02  
% 19.32/3.02  cnf(c_329,plain,
% 19.32/3.02      ( ~ r1_tarski(X0,X1) | m1_subset_1(X0,k1_zfmisc_1(X1)) ),
% 19.32/3.02      inference(prop_impl,[status(thm)],[c_9]) ).
% 19.32/3.02  
% 19.32/3.02  cnf(c_330,plain,
% 19.32/3.02      ( m1_subset_1(X0,k1_zfmisc_1(X1)) | ~ r1_tarski(X0,X1) ),
% 19.32/3.02      inference(renaming,[status(thm)],[c_329]) ).
% 19.32/3.02  
% 19.32/3.02  cnf(c_415,plain,
% 19.32/3.02      ( v1_subset_1(X0,X1) | ~ r1_tarski(X0,X1) | X0 = X1 ),
% 19.32/3.02      inference(bin_hyper_res,[status(thm)],[c_31,c_330]) ).
% 19.32/3.02  
% 19.32/3.02  cnf(c_33,negated_conjecture,
% 19.32/3.02      ( ~ v1_subset_1(sK6,u1_struct_0(sK5))
% 19.32/3.02      | r2_hidden(k3_yellow_0(sK5),sK6) ),
% 19.32/3.02      inference(cnf_transformation,[],[f110]) ).
% 19.32/3.02  
% 19.32/3.02  cnf(c_333,plain,
% 19.32/3.02      ( ~ v1_subset_1(sK6,u1_struct_0(sK5))
% 19.32/3.02      | r2_hidden(k3_yellow_0(sK5),sK6) ),
% 19.32/3.02      inference(prop_impl,[status(thm)],[c_33]) ).
% 19.32/3.02  
% 19.32/3.02  cnf(c_631,plain,
% 19.32/3.02      ( r2_hidden(k3_yellow_0(sK5),sK6)
% 19.32/3.02      | ~ r1_tarski(X0,X1)
% 19.32/3.02      | X1 = X0
% 19.32/3.02      | u1_struct_0(sK5) != X1
% 19.32/3.02      | sK6 != X0 ),
% 19.32/3.02      inference(resolution_lifted,[status(thm)],[c_415,c_333]) ).
% 19.32/3.02  
% 19.32/3.02  cnf(c_632,plain,
% 19.32/3.02      ( r2_hidden(k3_yellow_0(sK5),sK6)
% 19.32/3.02      | ~ r1_tarski(sK6,u1_struct_0(sK5))
% 19.32/3.02      | u1_struct_0(sK5) = sK6 ),
% 19.32/3.02      inference(unflattening,[status(thm)],[c_631]) ).
% 19.32/3.02  
% 19.32/3.02  cnf(c_633,plain,
% 19.32/3.02      ( u1_struct_0(sK5) = sK6
% 19.32/3.02      | r2_hidden(k3_yellow_0(sK5),sK6) = iProver_top
% 19.32/3.02      | r1_tarski(sK6,u1_struct_0(sK5)) != iProver_top ),
% 19.32/3.02      inference(predicate_to_equality,[status(thm)],[c_632]) ).
% 19.32/3.02  
% 19.32/3.02  cnf(c_10,plain,
% 19.32/3.02      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1)) | r1_tarski(X0,X1) ),
% 19.32/3.02      inference(cnf_transformation,[],[f78]) ).
% 19.32/3.02  
% 19.32/3.02  cnf(c_3264,plain,
% 19.32/3.02      ( ~ m1_subset_1(sK6,k1_zfmisc_1(u1_struct_0(sK5)))
% 19.32/3.02      | r1_tarski(sK6,u1_struct_0(sK5)) ),
% 19.32/3.02      inference(instantiation,[status(thm)],[c_10]) ).
% 19.32/3.02  
% 19.32/3.02  cnf(c_3265,plain,
% 19.32/3.02      ( m1_subset_1(sK6,k1_zfmisc_1(u1_struct_0(sK5))) != iProver_top
% 19.32/3.02      | r1_tarski(sK6,u1_struct_0(sK5)) = iProver_top ),
% 19.32/3.02      inference(predicate_to_equality,[status(thm)],[c_3264]) ).
% 19.32/3.02  
% 19.32/3.02  cnf(c_2133,plain,( X0 = X0 ),theory(equality) ).
% 19.32/3.02  
% 19.32/3.02  cnf(c_3345,plain,
% 19.32/3.02      ( sK6 = sK6 ),
% 19.32/3.02      inference(instantiation,[status(thm)],[c_2133]) ).
% 19.32/3.02  
% 19.32/3.02  cnf(c_2137,plain,
% 19.32/3.02      ( ~ v1_xboole_0(X0) | v1_xboole_0(X1) | X1 != X0 ),
% 19.32/3.02      theory(equality) ).
% 19.32/3.02  
% 19.32/3.02  cnf(c_3409,plain,
% 19.32/3.02      ( v1_xboole_0(X0)
% 19.32/3.02      | ~ v1_xboole_0(u1_struct_0(sK5))
% 19.32/3.02      | X0 != u1_struct_0(sK5) ),
% 19.32/3.02      inference(instantiation,[status(thm)],[c_2137]) ).
% 19.32/3.02  
% 19.32/3.02  cnf(c_4125,plain,
% 19.32/3.02      ( ~ v1_xboole_0(u1_struct_0(sK5))
% 19.32/3.02      | v1_xboole_0(sK6)
% 19.32/3.02      | sK6 != u1_struct_0(sK5) ),
% 19.32/3.02      inference(instantiation,[status(thm)],[c_3409]) ).
% 19.32/3.02  
% 19.32/3.02  cnf(c_4126,plain,
% 19.32/3.02      ( sK6 != u1_struct_0(sK5)
% 19.32/3.02      | v1_xboole_0(u1_struct_0(sK5)) != iProver_top
% 19.32/3.02      | v1_xboole_0(sK6) = iProver_top ),
% 19.32/3.02      inference(predicate_to_equality,[status(thm)],[c_4125]) ).
% 19.32/3.02  
% 19.32/3.02  cnf(c_2134,plain,( X0 != X1 | X2 != X1 | X2 = X0 ),theory(equality) ).
% 19.32/3.02  
% 19.32/3.02  cnf(c_3536,plain,
% 19.32/3.02      ( X0 != X1 | sK6 != X1 | sK6 = X0 ),
% 19.32/3.02      inference(instantiation,[status(thm)],[c_2134]) ).
% 19.32/3.02  
% 19.32/3.02  cnf(c_4188,plain,
% 19.32/3.02      ( X0 != sK6 | sK6 = X0 | sK6 != sK6 ),
% 19.32/3.02      inference(instantiation,[status(thm)],[c_3536]) ).
% 19.32/3.02  
% 19.32/3.02  cnf(c_4571,plain,
% 19.32/3.02      ( u1_struct_0(sK5) != sK6 | sK6 = u1_struct_0(sK5) | sK6 != sK6 ),
% 19.32/3.02      inference(instantiation,[status(thm)],[c_4188]) ).
% 19.32/3.02  
% 19.32/3.02  cnf(c_12,plain,
% 19.32/3.02      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
% 19.32/3.02      | ~ r2_hidden(X2,X0)
% 19.32/3.02      | ~ v1_xboole_0(X1) ),
% 19.32/3.02      inference(cnf_transformation,[],[f81]) ).
% 19.32/3.02  
% 19.32/3.02  cnf(c_414,plain,
% 19.32/3.02      ( ~ r2_hidden(X0,X1) | ~ r1_tarski(X1,X2) | ~ v1_xboole_0(X2) ),
% 19.32/3.02      inference(bin_hyper_res,[status(thm)],[c_12,c_330]) ).
% 19.32/3.02  
% 19.32/3.02  cnf(c_3404,plain,
% 19.32/3.02      ( ~ r2_hidden(X0,X1)
% 19.32/3.02      | ~ r1_tarski(X1,u1_struct_0(sK5))
% 19.32/3.02      | ~ v1_xboole_0(u1_struct_0(sK5)) ),
% 19.32/3.02      inference(instantiation,[status(thm)],[c_414]) ).
% 19.32/3.02  
% 19.32/3.02  cnf(c_5653,plain,
% 19.32/3.02      ( ~ r2_hidden(k3_yellow_0(sK5),sK6)
% 19.32/3.02      | ~ r1_tarski(sK6,u1_struct_0(sK5))
% 19.32/3.02      | ~ v1_xboole_0(u1_struct_0(sK5)) ),
% 19.32/3.02      inference(instantiation,[status(thm)],[c_3404]) ).
% 19.32/3.02  
% 19.32/3.02  cnf(c_5667,plain,
% 19.32/3.02      ( r2_hidden(k3_yellow_0(sK5),sK6) != iProver_top
% 19.32/3.02      | r1_tarski(sK6,u1_struct_0(sK5)) != iProver_top
% 19.32/3.02      | v1_xboole_0(u1_struct_0(sK5)) != iProver_top ),
% 19.32/3.02      inference(predicate_to_equality,[status(thm)],[c_5653]) ).
% 19.32/3.02  
% 19.32/3.02  cnf(c_6071,plain,
% 19.32/3.02      ( r2_hidden(k1_yellow_0(sK5,X0),u1_struct_0(sK5)) = iProver_top ),
% 19.32/3.02      inference(global_propositional_subsumption,
% 19.32/3.02                [status(thm)],
% 19.32/3.02                [c_4030,c_46,c_48,c_633,c_3265,c_3345,c_4126,c_4571,
% 19.32/3.02                 c_5667]) ).
% 19.32/3.02  
% 19.32/3.02  cnf(c_2,plain,
% 19.32/3.02      ( ~ r2_hidden(X0,X1) | r2_hidden(X0,X2) | ~ r1_tarski(X1,X2) ),
% 19.32/3.02      inference(cnf_transformation,[],[f69]) ).
% 19.32/3.02  
% 19.32/3.02  cnf(c_2945,plain,
% 19.32/3.02      ( r2_hidden(X0,X1) != iProver_top
% 19.32/3.02      | r2_hidden(X0,X2) = iProver_top
% 19.32/3.02      | r1_tarski(X1,X2) != iProver_top ),
% 19.32/3.02      inference(predicate_to_equality,[status(thm)],[c_2]) ).
% 19.32/3.02  
% 19.32/3.02  cnf(c_6079,plain,
% 19.32/3.02      ( r2_hidden(k1_yellow_0(sK5,X0),X1) = iProver_top
% 19.32/3.02      | r1_tarski(u1_struct_0(sK5),X1) != iProver_top ),
% 19.32/3.02      inference(superposition,[status(thm)],[c_6071,c_2945]) ).
% 19.32/3.02  
% 19.32/3.02  cnf(c_6476,plain,
% 19.32/3.02      ( m1_subset_1(k1_yellow_0(sK5,X0),X1) = iProver_top
% 19.32/3.02      | r1_tarski(u1_struct_0(sK5),X1) != iProver_top ),
% 19.32/3.02      inference(superposition,[status(thm)],[c_6079,c_2941]) ).
% 19.32/3.02  
% 19.32/3.02  cnf(c_27,plain,
% 19.32/3.02      ( v13_waybel_0(X0,X1)
% 19.32/3.02      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 19.32/3.02      | r2_hidden(sK3(X1,X0),X0)
% 19.32/3.02      | ~ l1_orders_2(X1) ),
% 19.32/3.02      inference(cnf_transformation,[],[f97]) ).
% 19.32/3.02  
% 19.32/3.02  cnf(c_940,plain,
% 19.32/3.02      ( v13_waybel_0(X0,X1)
% 19.32/3.02      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 19.32/3.02      | r2_hidden(sK3(X1,X0),X0)
% 19.32/3.02      | sK5 != X1 ),
% 19.32/3.02      inference(resolution_lifted,[status(thm)],[c_27,c_38]) ).
% 19.32/3.02  
% 19.32/3.02  cnf(c_941,plain,
% 19.32/3.02      ( v13_waybel_0(X0,sK5)
% 19.32/3.02      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK5)))
% 19.32/3.02      | r2_hidden(sK3(sK5,X0),X0) ),
% 19.32/3.02      inference(unflattening,[status(thm)],[c_940]) ).
% 19.32/3.02  
% 19.32/3.02  cnf(c_2916,plain,
% 19.32/3.02      ( v13_waybel_0(X0,sK5) = iProver_top
% 19.32/3.02      | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK5))) != iProver_top
% 19.32/3.02      | r2_hidden(sK3(sK5,X0),X0) = iProver_top ),
% 19.32/3.02      inference(predicate_to_equality,[status(thm)],[c_941]) ).
% 19.32/3.02  
% 19.32/3.02  cnf(c_7221,plain,
% 19.32/3.02      ( v13_waybel_0(k1_yellow_0(sK5,X0),sK5) = iProver_top
% 19.32/3.02      | r2_hidden(sK3(sK5,k1_yellow_0(sK5,X0)),k1_yellow_0(sK5,X0)) = iProver_top
% 19.32/3.02      | r1_tarski(u1_struct_0(sK5),k1_zfmisc_1(u1_struct_0(sK5))) != iProver_top ),
% 19.32/3.02      inference(superposition,[status(thm)],[c_6476,c_2916]) ).
% 19.32/3.02  
% 19.32/3.02  cnf(c_8288,plain,
% 19.32/3.02      ( v13_waybel_0(k1_yellow_0(sK5,k1_xboole_0),sK5) = iProver_top
% 19.32/3.02      | r2_hidden(sK3(sK5,k3_yellow_0(sK5)),k3_yellow_0(sK5)) = iProver_top
% 19.32/3.02      | r1_tarski(u1_struct_0(sK5),k1_zfmisc_1(u1_struct_0(sK5))) != iProver_top ),
% 19.32/3.02      inference(superposition,[status(thm)],[c_840,c_7221]) ).
% 19.32/3.02  
% 19.32/3.02  cnf(c_8318,plain,
% 19.32/3.02      ( v13_waybel_0(k3_yellow_0(sK5),sK5) = iProver_top
% 19.32/3.02      | r2_hidden(sK3(sK5,k3_yellow_0(sK5)),k3_yellow_0(sK5)) = iProver_top
% 19.32/3.02      | r1_tarski(u1_struct_0(sK5),k1_zfmisc_1(u1_struct_0(sK5))) != iProver_top ),
% 19.32/3.02      inference(light_normalisation,[status(thm)],[c_8288,c_840]) ).
% 19.32/3.02  
% 19.32/3.02  cnf(c_29,plain,
% 19.32/3.02      ( v13_waybel_0(X0,X1)
% 19.32/3.02      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 19.32/3.02      | m1_subset_1(sK3(X1,X0),u1_struct_0(X1))
% 19.32/3.02      | ~ l1_orders_2(X1) ),
% 19.32/3.02      inference(cnf_transformation,[],[f95]) ).
% 19.32/3.02  
% 19.32/3.02  cnf(c_910,plain,
% 19.32/3.02      ( v13_waybel_0(X0,X1)
% 19.32/3.02      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 19.32/3.02      | m1_subset_1(sK3(X1,X0),u1_struct_0(X1))
% 19.32/3.02      | sK5 != X1 ),
% 19.32/3.02      inference(resolution_lifted,[status(thm)],[c_29,c_38]) ).
% 19.32/3.02  
% 19.32/3.02  cnf(c_911,plain,
% 19.32/3.02      ( v13_waybel_0(X0,sK5)
% 19.32/3.02      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK5)))
% 19.32/3.02      | m1_subset_1(sK3(sK5,X0),u1_struct_0(sK5)) ),
% 19.32/3.02      inference(unflattening,[status(thm)],[c_910]) ).
% 19.32/3.02  
% 19.32/3.02  cnf(c_2918,plain,
% 19.32/3.02      ( v13_waybel_0(X0,sK5) = iProver_top
% 19.32/3.02      | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK5))) != iProver_top
% 19.32/3.02      | m1_subset_1(sK3(sK5,X0),u1_struct_0(sK5)) = iProver_top ),
% 19.32/3.02      inference(predicate_to_equality,[status(thm)],[c_911]) ).
% 19.32/3.02  
% 19.32/3.02  cnf(c_16,plain,
% 19.32/3.02      ( r1_orders_2(X0,X1,X2)
% 19.32/3.02      | ~ r2_lattice3(X0,X3,X2)
% 19.32/3.02      | ~ m1_subset_1(X2,u1_struct_0(X0))
% 19.32/3.02      | ~ m1_subset_1(X1,u1_struct_0(X0))
% 19.32/3.02      | ~ r2_hidden(X1,X3)
% 19.32/3.02      | ~ l1_orders_2(X0) ),
% 19.32/3.02      inference(cnf_transformation,[],[f82]) ).
% 19.32/3.02  
% 19.32/3.02  cnf(c_844,plain,
% 19.32/3.02      ( r1_orders_2(X0,X1,X2)
% 19.32/3.02      | ~ r2_lattice3(X0,X3,X2)
% 19.32/3.02      | ~ m1_subset_1(X2,u1_struct_0(X0))
% 19.32/3.02      | ~ m1_subset_1(X1,u1_struct_0(X0))
% 19.32/3.02      | ~ r2_hidden(X1,X3)
% 19.32/3.02      | sK5 != X0 ),
% 19.32/3.02      inference(resolution_lifted,[status(thm)],[c_16,c_38]) ).
% 19.32/3.02  
% 19.32/3.02  cnf(c_845,plain,
% 19.32/3.02      ( r1_orders_2(sK5,X0,X1)
% 19.32/3.02      | ~ r2_lattice3(sK5,X2,X1)
% 19.32/3.02      | ~ m1_subset_1(X1,u1_struct_0(sK5))
% 19.32/3.02      | ~ m1_subset_1(X0,u1_struct_0(sK5))
% 19.32/3.02      | ~ r2_hidden(X0,X2) ),
% 19.32/3.02      inference(unflattening,[status(thm)],[c_844]) ).
% 19.32/3.02  
% 19.32/3.02  cnf(c_2922,plain,
% 19.32/3.02      ( r1_orders_2(sK5,X0,X1) = iProver_top
% 19.32/3.02      | r2_lattice3(sK5,X2,X1) != iProver_top
% 19.32/3.02      | m1_subset_1(X0,u1_struct_0(sK5)) != iProver_top
% 19.32/3.02      | m1_subset_1(X1,u1_struct_0(sK5)) != iProver_top
% 19.32/3.02      | r2_hidden(X0,X2) != iProver_top ),
% 19.32/3.02      inference(predicate_to_equality,[status(thm)],[c_845]) ).
% 19.32/3.02  
% 19.32/3.02  cnf(c_3777,plain,
% 19.32/3.02      ( r1_orders_2(sK5,sK3(sK5,X0),X1) = iProver_top
% 19.32/3.02      | r2_lattice3(sK5,X2,X1) != iProver_top
% 19.32/3.02      | v13_waybel_0(X0,sK5) = iProver_top
% 19.32/3.02      | m1_subset_1(X1,u1_struct_0(sK5)) != iProver_top
% 19.32/3.02      | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK5))) != iProver_top
% 19.32/3.02      | r2_hidden(sK3(sK5,X0),X2) != iProver_top ),
% 19.32/3.02      inference(superposition,[status(thm)],[c_2918,c_2922]) ).
% 19.32/3.02  
% 19.32/3.02  cnf(c_9067,plain,
% 19.32/3.02      ( r1_orders_2(sK5,sK3(sK5,k3_yellow_0(sK5)),X0) = iProver_top
% 19.32/3.02      | r2_lattice3(sK5,k3_yellow_0(sK5),X0) != iProver_top
% 19.32/3.02      | v13_waybel_0(k3_yellow_0(sK5),sK5) = iProver_top
% 19.32/3.02      | m1_subset_1(X0,u1_struct_0(sK5)) != iProver_top
% 19.32/3.02      | m1_subset_1(k3_yellow_0(sK5),k1_zfmisc_1(u1_struct_0(sK5))) != iProver_top
% 19.32/3.02      | r1_tarski(u1_struct_0(sK5),k1_zfmisc_1(u1_struct_0(sK5))) != iProver_top ),
% 19.32/3.02      inference(superposition,[status(thm)],[c_8318,c_3777]) ).
% 19.32/3.02  
% 19.32/3.02  cnf(c_7213,plain,
% 19.32/3.02      ( m1_subset_1(k3_yellow_0(sK5),X0) = iProver_top
% 19.32/3.02      | r1_tarski(u1_struct_0(sK5),X0) != iProver_top ),
% 19.32/3.02      inference(superposition,[status(thm)],[c_840,c_6476]) ).
% 19.32/3.02  
% 19.32/3.02  cnf(c_17201,plain,
% 19.32/3.02      ( r1_orders_2(sK5,sK3(sK5,k3_yellow_0(sK5)),X0) = iProver_top
% 19.32/3.02      | r2_lattice3(sK5,k3_yellow_0(sK5),X0) != iProver_top
% 19.32/3.02      | v13_waybel_0(k3_yellow_0(sK5),sK5) = iProver_top
% 19.32/3.02      | m1_subset_1(X0,u1_struct_0(sK5)) != iProver_top
% 19.32/3.02      | r1_tarski(u1_struct_0(sK5),k1_zfmisc_1(u1_struct_0(sK5))) != iProver_top ),
% 19.32/3.02      inference(forward_subsumption_resolution,
% 19.32/3.02                [status(thm)],
% 19.32/3.02                [c_9067,c_7213]) ).
% 19.32/3.02  
% 19.32/3.02  cnf(c_2936,plain,
% 19.32/3.02      ( m1_subset_1(sK6,k1_zfmisc_1(u1_struct_0(sK5))) = iProver_top ),
% 19.32/3.02      inference(predicate_to_equality,[status(thm)],[c_35]) ).
% 19.32/3.02  
% 19.32/3.02  cnf(c_30,plain,
% 19.32/3.02      ( ~ r1_orders_2(X0,X1,X2)
% 19.32/3.02      | ~ v13_waybel_0(X3,X0)
% 19.32/3.02      | ~ m1_subset_1(X1,u1_struct_0(X0))
% 19.32/3.02      | ~ m1_subset_1(X2,u1_struct_0(X0))
% 19.32/3.02      | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))
% 19.32/3.02      | ~ r2_hidden(X1,X3)
% 19.32/3.02      | r2_hidden(X2,X3)
% 19.32/3.02      | ~ l1_orders_2(X0) ),
% 19.32/3.02      inference(cnf_transformation,[],[f94]) ).
% 19.32/3.02  
% 19.32/3.02  cnf(c_790,plain,
% 19.32/3.02      ( ~ r1_orders_2(X0,X1,X2)
% 19.32/3.02      | ~ v13_waybel_0(X3,X0)
% 19.32/3.02      | ~ m1_subset_1(X2,u1_struct_0(X0))
% 19.32/3.02      | ~ m1_subset_1(X1,u1_struct_0(X0))
% 19.32/3.02      | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))
% 19.32/3.02      | ~ r2_hidden(X1,X3)
% 19.32/3.02      | r2_hidden(X2,X3)
% 19.32/3.02      | sK5 != X0 ),
% 19.32/3.02      inference(resolution_lifted,[status(thm)],[c_30,c_38]) ).
% 19.32/3.02  
% 19.32/3.02  cnf(c_791,plain,
% 19.32/3.02      ( ~ r1_orders_2(sK5,X0,X1)
% 19.32/3.02      | ~ v13_waybel_0(X2,sK5)
% 19.32/3.02      | ~ m1_subset_1(X1,u1_struct_0(sK5))
% 19.32/3.02      | ~ m1_subset_1(X0,u1_struct_0(sK5))
% 19.32/3.02      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK5)))
% 19.32/3.02      | ~ r2_hidden(X0,X2)
% 19.32/3.02      | r2_hidden(X1,X2) ),
% 19.32/3.02      inference(unflattening,[status(thm)],[c_790]) ).
% 19.32/3.02  
% 19.32/3.02  cnf(c_11,plain,
% 19.32/3.02      ( m1_subset_1(X0,X1)
% 19.32/3.02      | ~ m1_subset_1(X2,k1_zfmisc_1(X1))
% 19.32/3.02      | ~ r2_hidden(X0,X2) ),
% 19.32/3.02      inference(cnf_transformation,[],[f80]) ).
% 19.32/3.02  
% 19.32/3.02  cnf(c_807,plain,
% 19.32/3.02      ( ~ r1_orders_2(sK5,X0,X1)
% 19.32/3.02      | ~ v13_waybel_0(X2,sK5)
% 19.32/3.02      | ~ m1_subset_1(X1,u1_struct_0(sK5))
% 19.32/3.02      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK5)))
% 19.32/3.02      | ~ r2_hidden(X0,X2)
% 19.32/3.02      | r2_hidden(X1,X2) ),
% 19.32/3.02      inference(forward_subsumption_resolution,
% 19.32/3.02                [status(thm)],
% 19.32/3.02                [c_791,c_11]) ).
% 19.32/3.02  
% 19.32/3.02  cnf(c_2925,plain,
% 19.32/3.02      ( r1_orders_2(sK5,X0,X1) != iProver_top
% 19.32/3.02      | v13_waybel_0(X2,sK5) != iProver_top
% 19.32/3.02      | m1_subset_1(X1,u1_struct_0(sK5)) != iProver_top
% 19.32/3.02      | m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK5))) != iProver_top
% 19.32/3.02      | r2_hidden(X0,X2) != iProver_top
% 19.32/3.02      | r2_hidden(X1,X2) = iProver_top ),
% 19.32/3.02      inference(predicate_to_equality,[status(thm)],[c_807]) ).
% 19.32/3.02  
% 19.32/3.02  cnf(c_4513,plain,
% 19.32/3.02      ( r1_orders_2(sK5,X0,X1) != iProver_top
% 19.32/3.02      | v13_waybel_0(sK6,sK5) != iProver_top
% 19.32/3.02      | m1_subset_1(X1,u1_struct_0(sK5)) != iProver_top
% 19.32/3.02      | r2_hidden(X0,sK6) != iProver_top
% 19.32/3.02      | r2_hidden(X1,sK6) = iProver_top ),
% 19.32/3.02      inference(superposition,[status(thm)],[c_2936,c_2925]) ).
% 19.32/3.02  
% 19.32/3.02  cnf(c_36,negated_conjecture,
% 19.32/3.02      ( v13_waybel_0(sK6,sK5) ),
% 19.32/3.02      inference(cnf_transformation,[],[f107]) ).
% 19.32/3.02  
% 19.32/3.02  cnf(c_1018,plain,
% 19.32/3.02      ( ~ r1_orders_2(sK5,X0,X1)
% 19.32/3.02      | ~ m1_subset_1(X1,u1_struct_0(sK5))
% 19.32/3.02      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK5)))
% 19.32/3.02      | ~ r2_hidden(X0,X2)
% 19.32/3.02      | r2_hidden(X1,X2)
% 19.32/3.02      | sK6 != X2
% 19.32/3.02      | sK5 != sK5 ),
% 19.32/3.02      inference(resolution_lifted,[status(thm)],[c_36,c_807]) ).
% 19.32/3.02  
% 19.32/3.02  cnf(c_1019,plain,
% 19.32/3.02      ( ~ r1_orders_2(sK5,X0,X1)
% 19.32/3.02      | ~ m1_subset_1(X1,u1_struct_0(sK5))
% 19.32/3.02      | ~ m1_subset_1(sK6,k1_zfmisc_1(u1_struct_0(sK5)))
% 19.32/3.02      | ~ r2_hidden(X0,sK6)
% 19.32/3.02      | r2_hidden(X1,sK6) ),
% 19.32/3.02      inference(unflattening,[status(thm)],[c_1018]) ).
% 19.32/3.02  
% 19.32/3.02  cnf(c_1021,plain,
% 19.32/3.02      ( ~ m1_subset_1(X1,u1_struct_0(sK5))
% 19.32/3.02      | ~ r1_orders_2(sK5,X0,X1)
% 19.32/3.02      | ~ r2_hidden(X0,sK6)
% 19.32/3.02      | r2_hidden(X1,sK6) ),
% 19.32/3.02      inference(global_propositional_subsumption,
% 19.32/3.02                [status(thm)],
% 19.32/3.02                [c_1019,c_35]) ).
% 19.32/3.02  
% 19.32/3.02  cnf(c_1022,plain,
% 19.32/3.02      ( ~ r1_orders_2(sK5,X0,X1)
% 19.32/3.02      | ~ m1_subset_1(X1,u1_struct_0(sK5))
% 19.32/3.02      | ~ r2_hidden(X0,sK6)
% 19.32/3.02      | r2_hidden(X1,sK6) ),
% 19.32/3.02      inference(renaming,[status(thm)],[c_1021]) ).
% 19.32/3.02  
% 19.32/3.02  cnf(c_1023,plain,
% 19.32/3.02      ( r1_orders_2(sK5,X0,X1) != iProver_top
% 19.32/3.02      | m1_subset_1(X1,u1_struct_0(sK5)) != iProver_top
% 19.32/3.02      | r2_hidden(X0,sK6) != iProver_top
% 19.32/3.02      | r2_hidden(X1,sK6) = iProver_top ),
% 19.32/3.02      inference(predicate_to_equality,[status(thm)],[c_1022]) ).
% 19.32/3.02  
% 19.32/3.02  cnf(c_4924,plain,
% 19.32/3.02      ( r1_orders_2(sK5,X0,X1) != iProver_top
% 19.32/3.02      | m1_subset_1(X1,u1_struct_0(sK5)) != iProver_top
% 19.32/3.02      | r2_hidden(X0,sK6) != iProver_top
% 19.32/3.02      | r2_hidden(X1,sK6) = iProver_top ),
% 19.32/3.02      inference(global_propositional_subsumption,
% 19.32/3.02                [status(thm)],
% 19.32/3.02                [c_4513,c_1023]) ).
% 19.32/3.02  
% 19.32/3.02  cnf(c_17207,plain,
% 19.32/3.02      ( r2_lattice3(sK5,k3_yellow_0(sK5),X0) != iProver_top
% 19.32/3.02      | v13_waybel_0(k3_yellow_0(sK5),sK5) = iProver_top
% 19.32/3.02      | m1_subset_1(X0,u1_struct_0(sK5)) != iProver_top
% 19.32/3.02      | r2_hidden(X0,sK6) = iProver_top
% 19.32/3.02      | r2_hidden(sK3(sK5,k3_yellow_0(sK5)),sK6) != iProver_top
% 19.32/3.02      | r1_tarski(u1_struct_0(sK5),k1_zfmisc_1(u1_struct_0(sK5))) != iProver_top ),
% 19.32/3.02      inference(superposition,[status(thm)],[c_17201,c_4924]) ).
% 19.32/3.02  
% 19.32/3.02  cnf(c_32,plain,
% 19.32/3.02      ( ~ v1_subset_1(X0,X0) | ~ m1_subset_1(X0,k1_zfmisc_1(X0)) ),
% 19.32/3.02      inference(cnf_transformation,[],[f115]) ).
% 19.32/3.02  
% 19.32/3.02  cnf(c_52,plain,
% 19.32/3.02      ( ~ v1_subset_1(sK5,sK5) | ~ m1_subset_1(sK5,k1_zfmisc_1(sK5)) ),
% 19.32/3.02      inference(instantiation,[status(thm)],[c_32]) ).
% 19.32/3.02  
% 19.32/3.02  cnf(c_55,plain,
% 19.32/3.02      ( v1_subset_1(sK5,sK5)
% 19.32/3.02      | ~ m1_subset_1(sK5,k1_zfmisc_1(sK5))
% 19.32/3.02      | sK5 = sK5 ),
% 19.32/3.02      inference(instantiation,[status(thm)],[c_31]) ).
% 19.32/3.02  
% 19.32/3.02  cnf(c_95,plain,
% 19.32/3.02      ( ~ l1_orders_2(sK5)
% 19.32/3.02      | k1_yellow_0(sK5,k1_xboole_0) = k3_yellow_0(sK5) ),
% 19.32/3.02      inference(instantiation,[status(thm)],[c_17]) ).
% 19.32/3.02  
% 19.32/3.02  cnf(c_119,plain,
% 19.32/3.02      ( m1_subset_1(sK5,k1_zfmisc_1(sK5)) | ~ r1_tarski(sK5,sK5) ),
% 19.32/3.02      inference(instantiation,[status(thm)],[c_9]) ).
% 19.32/3.02  
% 19.32/3.02  cnf(c_6,plain,
% 19.32/3.02      ( r1_tarski(X0,X0) ),
% 19.32/3.02      inference(cnf_transformation,[],[f112]) ).
% 19.32/3.02  
% 19.32/3.02  cnf(c_128,plain,
% 19.32/3.02      ( r1_tarski(sK5,sK5) ),
% 19.32/3.02      inference(instantiation,[status(thm)],[c_6]) ).
% 19.32/3.02  
% 19.32/3.02  cnf(c_2144,plain,
% 19.32/3.02      ( X0 != X1 | k3_yellow_0(X0) = k3_yellow_0(X1) ),
% 19.32/3.02      theory(equality) ).
% 19.32/3.02  
% 19.32/3.02  cnf(c_2159,plain,
% 19.32/3.02      ( k3_yellow_0(sK5) = k3_yellow_0(sK5) | sK5 != sK5 ),
% 19.32/3.02      inference(instantiation,[status(thm)],[c_2144]) ).
% 19.32/3.02  
% 19.32/3.02  cnf(c_3553,plain,
% 19.32/3.02      ( m1_subset_1(k1_yellow_0(sK5,k1_xboole_0),u1_struct_0(sK5)) ),
% 19.32/3.02      inference(instantiation,[status(thm)],[c_831]) ).
% 19.32/3.02  
% 19.32/3.02  cnf(c_3554,plain,
% 19.32/3.02      ( m1_subset_1(k1_yellow_0(sK5,k1_xboole_0),u1_struct_0(sK5)) = iProver_top ),
% 19.32/3.02      inference(predicate_to_equality,[status(thm)],[c_3553]) ).
% 19.32/3.02  
% 19.32/3.02  cnf(c_21,plain,
% 19.32/3.02      ( r1_orders_2(X0,k1_yellow_0(X0,X1),X2)
% 19.32/3.02      | ~ r2_lattice3(X0,X1,X2)
% 19.32/3.02      | ~ r1_yellow_0(X0,X1)
% 19.32/3.02      | ~ m1_subset_1(X2,u1_struct_0(X0))
% 19.32/3.02      | ~ m1_subset_1(k1_yellow_0(X0,X1),u1_struct_0(X0))
% 19.32/3.02      | ~ l1_orders_2(X0) ),
% 19.32/3.02      inference(cnf_transformation,[],[f113]) ).
% 19.32/3.02  
% 19.32/3.02  cnf(c_249,plain,
% 19.32/3.02      ( ~ m1_subset_1(X2,u1_struct_0(X0))
% 19.32/3.02      | ~ r1_yellow_0(X0,X1)
% 19.32/3.02      | ~ r2_lattice3(X0,X1,X2)
% 19.32/3.02      | r1_orders_2(X0,k1_yellow_0(X0,X1),X2)
% 19.32/3.02      | ~ l1_orders_2(X0) ),
% 19.32/3.02      inference(global_propositional_subsumption,
% 19.32/3.02                [status(thm)],
% 19.32/3.02                [c_21,c_23]) ).
% 19.32/3.02  
% 19.32/3.02  cnf(c_250,plain,
% 19.32/3.02      ( r1_orders_2(X0,k1_yellow_0(X0,X1),X2)
% 19.32/3.02      | ~ r2_lattice3(X0,X1,X2)
% 19.32/3.02      | ~ r1_yellow_0(X0,X1)
% 19.32/3.02      | ~ m1_subset_1(X2,u1_struct_0(X0))
% 19.32/3.02      | ~ l1_orders_2(X0) ),
% 19.32/3.02      inference(renaming,[status(thm)],[c_249]) ).
% 19.32/3.02  
% 19.32/3.02  cnf(c_24,plain,
% 19.32/3.02      ( r1_yellow_0(X0,k1_xboole_0)
% 19.32/3.02      | v2_struct_0(X0)
% 19.32/3.02      | ~ v5_orders_2(X0)
% 19.32/3.02      | ~ v1_yellow_0(X0)
% 19.32/3.02      | ~ l1_orders_2(X0) ),
% 19.32/3.02      inference(cnf_transformation,[],[f93]) ).
% 19.32/3.02  
% 19.32/3.02  cnf(c_39,negated_conjecture,
% 19.32/3.02      ( v1_yellow_0(sK5) ),
% 19.32/3.02      inference(cnf_transformation,[],[f104]) ).
% 19.32/3.02  
% 19.32/3.02  cnf(c_562,plain,
% 19.32/3.02      ( r1_yellow_0(X0,k1_xboole_0)
% 19.32/3.02      | v2_struct_0(X0)
% 19.32/3.02      | ~ v5_orders_2(X0)
% 19.32/3.02      | ~ l1_orders_2(X0)
% 19.32/3.02      | sK5 != X0 ),
% 19.32/3.02      inference(resolution_lifted,[status(thm)],[c_24,c_39]) ).
% 19.32/3.02  
% 19.32/3.02  cnf(c_563,plain,
% 19.32/3.02      ( r1_yellow_0(sK5,k1_xboole_0)
% 19.32/3.02      | v2_struct_0(sK5)
% 19.32/3.02      | ~ v5_orders_2(sK5)
% 19.32/3.02      | ~ l1_orders_2(sK5) ),
% 19.32/3.02      inference(unflattening,[status(thm)],[c_562]) ).
% 19.32/3.02  
% 19.32/3.02  cnf(c_41,negated_conjecture,
% 19.32/3.02      ( ~ v2_struct_0(sK5) ),
% 19.32/3.02      inference(cnf_transformation,[],[f102]) ).
% 19.32/3.02  
% 19.32/3.02  cnf(c_40,negated_conjecture,
% 19.32/3.02      ( v5_orders_2(sK5) ),
% 19.32/3.02      inference(cnf_transformation,[],[f103]) ).
% 19.32/3.02  
% 19.32/3.02  cnf(c_74,plain,
% 19.32/3.02      ( r1_yellow_0(sK5,k1_xboole_0)
% 19.32/3.02      | v2_struct_0(sK5)
% 19.32/3.02      | ~ v5_orders_2(sK5)
% 19.32/3.02      | ~ v1_yellow_0(sK5)
% 19.32/3.02      | ~ l1_orders_2(sK5) ),
% 19.32/3.02      inference(instantiation,[status(thm)],[c_24]) ).
% 19.32/3.02  
% 19.32/3.02  cnf(c_565,plain,
% 19.32/3.02      ( r1_yellow_0(sK5,k1_xboole_0) ),
% 19.32/3.02      inference(global_propositional_subsumption,
% 19.32/3.02                [status(thm)],
% 19.32/3.02                [c_563,c_41,c_40,c_39,c_38,c_74]) ).
% 19.32/3.02  
% 19.32/3.02  cnf(c_665,plain,
% 19.32/3.02      ( r1_orders_2(X0,k1_yellow_0(X0,X1),X2)
% 19.32/3.02      | ~ r2_lattice3(X0,X1,X2)
% 19.32/3.02      | ~ m1_subset_1(X2,u1_struct_0(X0))
% 19.32/3.02      | ~ l1_orders_2(X0)
% 19.32/3.02      | sK5 != X0
% 19.32/3.02      | k1_xboole_0 != X1 ),
% 19.32/3.02      inference(resolution_lifted,[status(thm)],[c_250,c_565]) ).
% 19.32/3.02  
% 19.32/3.02  cnf(c_666,plain,
% 19.32/3.02      ( r1_orders_2(sK5,k1_yellow_0(sK5,k1_xboole_0),X0)
% 19.32/3.02      | ~ r2_lattice3(sK5,k1_xboole_0,X0)
% 19.32/3.02      | ~ m1_subset_1(X0,u1_struct_0(sK5))
% 19.32/3.02      | ~ l1_orders_2(sK5) ),
% 19.32/3.02      inference(unflattening,[status(thm)],[c_665]) ).
% 19.32/3.02  
% 19.32/3.02  cnf(c_670,plain,
% 19.32/3.02      ( ~ m1_subset_1(X0,u1_struct_0(sK5))
% 19.32/3.02      | ~ r2_lattice3(sK5,k1_xboole_0,X0)
% 19.32/3.02      | r1_orders_2(sK5,k1_yellow_0(sK5,k1_xboole_0),X0) ),
% 19.32/3.02      inference(global_propositional_subsumption,
% 19.32/3.02                [status(thm)],
% 19.32/3.02                [c_666,c_38]) ).
% 19.32/3.02  
% 19.32/3.02  cnf(c_671,plain,
% 19.32/3.02      ( r1_orders_2(sK5,k1_yellow_0(sK5,k1_xboole_0),X0)
% 19.32/3.02      | ~ r2_lattice3(sK5,k1_xboole_0,X0)
% 19.32/3.02      | ~ m1_subset_1(X0,u1_struct_0(sK5)) ),
% 19.32/3.02      inference(renaming,[status(thm)],[c_670]) ).
% 19.32/3.02  
% 19.32/3.02  cnf(c_2930,plain,
% 19.32/3.02      ( r1_orders_2(sK5,k1_yellow_0(sK5,k1_xboole_0),X0) = iProver_top
% 19.32/3.02      | r2_lattice3(sK5,k1_xboole_0,X0) != iProver_top
% 19.32/3.02      | m1_subset_1(X0,u1_struct_0(sK5)) != iProver_top ),
% 19.32/3.02      inference(predicate_to_equality,[status(thm)],[c_671]) ).
% 19.32/3.02  
% 19.32/3.02  cnf(c_3063,plain,
% 19.32/3.02      ( r1_orders_2(sK5,k3_yellow_0(sK5),X0) = iProver_top
% 19.32/3.02      | r2_lattice3(sK5,k1_xboole_0,X0) != iProver_top
% 19.32/3.02      | m1_subset_1(X0,u1_struct_0(sK5)) != iProver_top ),
% 19.32/3.02      inference(light_normalisation,[status(thm)],[c_2930,c_840]) ).
% 19.32/3.02  
% 19.32/3.02  cnf(c_4933,plain,
% 19.32/3.02      ( r2_lattice3(sK5,k1_xboole_0,X0) != iProver_top
% 19.32/3.02      | m1_subset_1(X0,u1_struct_0(sK5)) != iProver_top
% 19.32/3.02      | r2_hidden(X0,sK6) = iProver_top
% 19.32/3.02      | r2_hidden(k3_yellow_0(sK5),sK6) != iProver_top ),
% 19.32/3.02      inference(superposition,[status(thm)],[c_3063,c_4924]) ).
% 19.32/3.02  
% 19.32/3.02  cnf(c_14,plain,
% 19.32/3.02      ( r2_lattice3(X0,X1,X2)
% 19.32/3.02      | ~ m1_subset_1(X2,u1_struct_0(X0))
% 19.32/3.02      | r2_hidden(sK1(X0,X1,X2),X1)
% 19.32/3.02      | ~ l1_orders_2(X0) ),
% 19.32/3.02      inference(cnf_transformation,[],[f84]) ).
% 19.32/3.02  
% 19.32/3.02  cnf(c_880,plain,
% 19.32/3.02      ( r2_lattice3(X0,X1,X2)
% 19.32/3.02      | ~ m1_subset_1(X2,u1_struct_0(X0))
% 19.32/3.02      | r2_hidden(sK1(X0,X1,X2),X1)
% 19.32/3.02      | sK5 != X0 ),
% 19.32/3.02      inference(resolution_lifted,[status(thm)],[c_14,c_38]) ).
% 19.32/3.02  
% 19.32/3.02  cnf(c_881,plain,
% 19.32/3.02      ( r2_lattice3(sK5,X0,X1)
% 19.32/3.02      | ~ m1_subset_1(X1,u1_struct_0(sK5))
% 19.32/3.02      | r2_hidden(sK1(sK5,X0,X1),X0) ),
% 19.32/3.02      inference(unflattening,[status(thm)],[c_880]) ).
% 19.32/3.02  
% 19.32/3.02  cnf(c_2920,plain,
% 19.32/3.02      ( r2_lattice3(sK5,X0,X1) = iProver_top
% 19.32/3.02      | m1_subset_1(X1,u1_struct_0(sK5)) != iProver_top
% 19.32/3.02      | r2_hidden(sK1(sK5,X0,X1),X0) = iProver_top ),
% 19.32/3.02      inference(predicate_to_equality,[status(thm)],[c_881]) ).
% 19.32/3.02  
% 19.32/3.02  cnf(c_22,plain,
% 19.32/3.02      ( r2_lattice3(X0,X1,k1_yellow_0(X0,X1))
% 19.32/3.02      | ~ r1_yellow_0(X0,X1)
% 19.32/3.02      | ~ m1_subset_1(k1_yellow_0(X0,X1),u1_struct_0(X0))
% 19.32/3.02      | ~ l1_orders_2(X0) ),
% 19.32/3.02      inference(cnf_transformation,[],[f114]) ).
% 19.32/3.02  
% 19.32/3.02  cnf(c_242,plain,
% 19.32/3.02      ( ~ r1_yellow_0(X0,X1)
% 19.32/3.02      | r2_lattice3(X0,X1,k1_yellow_0(X0,X1))
% 19.32/3.02      | ~ l1_orders_2(X0) ),
% 19.32/3.02      inference(global_propositional_subsumption,
% 19.32/3.02                [status(thm)],
% 19.32/3.02                [c_22,c_23]) ).
% 19.32/3.02  
% 19.32/3.02  cnf(c_243,plain,
% 19.32/3.02      ( r2_lattice3(X0,X1,k1_yellow_0(X0,X1))
% 19.32/3.02      | ~ r1_yellow_0(X0,X1)
% 19.32/3.02      | ~ l1_orders_2(X0) ),
% 19.32/3.02      inference(renaming,[status(thm)],[c_242]) ).
% 19.32/3.02  
% 19.32/3.02  cnf(c_686,plain,
% 19.32/3.02      ( r2_lattice3(X0,X1,k1_yellow_0(X0,X1))
% 19.32/3.02      | ~ l1_orders_2(X0)
% 19.32/3.02      | sK5 != X0
% 19.32/3.02      | k1_xboole_0 != X1 ),
% 19.32/3.02      inference(resolution_lifted,[status(thm)],[c_243,c_565]) ).
% 19.32/3.02  
% 19.32/3.02  cnf(c_687,plain,
% 19.32/3.02      ( r2_lattice3(sK5,k1_xboole_0,k1_yellow_0(sK5,k1_xboole_0))
% 19.32/3.02      | ~ l1_orders_2(sK5) ),
% 19.32/3.02      inference(unflattening,[status(thm)],[c_686]) ).
% 19.32/3.02  
% 19.32/3.02  cnf(c_689,plain,
% 19.32/3.02      ( r2_lattice3(sK5,k1_xboole_0,k1_yellow_0(sK5,k1_xboole_0)) ),
% 19.32/3.02      inference(global_propositional_subsumption,
% 19.32/3.02                [status(thm)],
% 19.32/3.02                [c_687,c_38]) ).
% 19.32/3.02  
% 19.32/3.02  cnf(c_2929,plain,
% 19.32/3.02      ( r2_lattice3(sK5,k1_xboole_0,k1_yellow_0(sK5,k1_xboole_0)) = iProver_top ),
% 19.32/3.02      inference(predicate_to_equality,[status(thm)],[c_689]) ).
% 19.32/3.02  
% 19.32/3.02  cnf(c_2962,plain,
% 19.32/3.02      ( r2_lattice3(sK5,k1_xboole_0,k3_yellow_0(sK5)) = iProver_top ),
% 19.32/3.02      inference(light_normalisation,[status(thm)],[c_2929,c_840]) ).
% 19.32/3.02  
% 19.32/3.02  cnf(c_3276,plain,
% 19.32/3.02      ( m1_subset_1(k3_yellow_0(sK5),u1_struct_0(sK5)) = iProver_top ),
% 19.32/3.02      inference(superposition,[status(thm)],[c_840,c_2923]) ).
% 19.32/3.02  
% 19.32/3.02  cnf(c_2937,plain,
% 19.32/3.02      ( m1_subset_1(X0,X1) = iProver_top
% 19.32/3.02      | m1_subset_1(X2,k1_zfmisc_1(X1)) != iProver_top
% 19.32/3.02      | r2_hidden(X0,X2) != iProver_top ),
% 19.32/3.02      inference(predicate_to_equality,[status(thm)],[c_11]) ).
% 19.32/3.02  
% 19.32/3.02  cnf(c_4665,plain,
% 19.32/3.02      ( m1_subset_1(X0,u1_struct_0(sK5)) = iProver_top
% 19.32/3.02      | r2_hidden(X0,sK6) != iProver_top ),
% 19.32/3.02      inference(superposition,[status(thm)],[c_2936,c_2937]) ).
% 19.32/3.02  
% 19.32/3.02  cnf(c_4796,plain,
% 19.32/3.02      ( r1_orders_2(sK5,X0,X1) = iProver_top
% 19.32/3.02      | r2_lattice3(sK5,X2,X1) != iProver_top
% 19.32/3.02      | m1_subset_1(X1,u1_struct_0(sK5)) != iProver_top
% 19.32/3.02      | r2_hidden(X0,X2) != iProver_top
% 19.32/3.02      | r2_hidden(X0,sK6) != iProver_top ),
% 19.32/3.02      inference(superposition,[status(thm)],[c_4665,c_2922]) ).
% 19.32/3.02  
% 19.32/3.02  cnf(c_5099,plain,
% 19.32/3.02      ( r1_orders_2(sK5,X0,k3_yellow_0(sK5)) = iProver_top
% 19.32/3.02      | r2_lattice3(sK5,X1,k3_yellow_0(sK5)) != iProver_top
% 19.32/3.02      | r2_hidden(X0,X1) != iProver_top
% 19.32/3.02      | r2_hidden(X0,sK6) != iProver_top ),
% 19.32/3.02      inference(superposition,[status(thm)],[c_3276,c_4796]) ).
% 19.32/3.02  
% 19.32/3.02  cnf(c_5202,plain,
% 19.32/3.02      ( r1_orders_2(sK5,X0,k3_yellow_0(sK5)) = iProver_top
% 19.32/3.02      | r2_hidden(X0,sK6) != iProver_top
% 19.32/3.02      | r2_hidden(X0,k1_xboole_0) != iProver_top ),
% 19.32/3.02      inference(superposition,[status(thm)],[c_2962,c_5099]) ).
% 19.32/3.02  
% 19.32/3.02  cnf(c_3,plain,
% 19.32/3.02      ( v1_xboole_0(k1_xboole_0) ),
% 19.32/3.02      inference(cnf_transformation,[],[f72]) ).
% 19.32/3.02  
% 19.32/3.02  cnf(c_134,plain,
% 19.32/3.02      ( v1_xboole_0(k1_xboole_0) = iProver_top ),
% 19.32/3.02      inference(predicate_to_equality,[status(thm)],[c_3]) ).
% 19.32/3.02  
% 19.32/3.02  cnf(c_3295,plain,
% 19.32/3.02      ( ~ r2_hidden(X0,X1)
% 19.32/3.02      | ~ r1_tarski(X1,k1_xboole_0)
% 19.32/3.02      | ~ v1_xboole_0(k1_xboole_0) ),
% 19.32/3.02      inference(instantiation,[status(thm)],[c_414]) ).
% 19.32/3.02  
% 19.32/3.02  cnf(c_3818,plain,
% 19.32/3.02      ( ~ r2_hidden(X0,k1_xboole_0)
% 19.32/3.02      | ~ r1_tarski(k1_xboole_0,k1_xboole_0)
% 19.32/3.02      | ~ v1_xboole_0(k1_xboole_0) ),
% 19.32/3.02      inference(instantiation,[status(thm)],[c_3295]) ).
% 19.32/3.02  
% 19.32/3.02  cnf(c_3820,plain,
% 19.32/3.02      ( r2_hidden(X0,k1_xboole_0) != iProver_top
% 19.32/3.02      | r1_tarski(k1_xboole_0,k1_xboole_0) != iProver_top
% 19.32/3.02      | v1_xboole_0(k1_xboole_0) != iProver_top ),
% 19.32/3.02      inference(predicate_to_equality,[status(thm)],[c_3818]) ).
% 19.32/3.02  
% 19.32/3.02  cnf(c_3819,plain,
% 19.32/3.02      ( r1_tarski(k1_xboole_0,k1_xboole_0) ),
% 19.32/3.02      inference(instantiation,[status(thm)],[c_6]) ).
% 19.32/3.02  
% 19.32/3.02  cnf(c_3824,plain,
% 19.32/3.02      ( r1_tarski(k1_xboole_0,k1_xboole_0) = iProver_top ),
% 19.32/3.02      inference(predicate_to_equality,[status(thm)],[c_3819]) ).
% 19.32/3.02  
% 19.32/3.02  cnf(c_5354,plain,
% 19.32/3.02      ( r2_hidden(X0,k1_xboole_0) != iProver_top ),
% 19.32/3.02      inference(global_propositional_subsumption,
% 19.32/3.02                [status(thm)],
% 19.32/3.02                [c_5202,c_134,c_3820,c_3824]) ).
% 19.32/3.02  
% 19.32/3.02  cnf(c_5362,plain,
% 19.32/3.02      ( r2_lattice3(sK5,k1_xboole_0,X0) = iProver_top
% 19.32/3.02      | m1_subset_1(X0,u1_struct_0(sK5)) != iProver_top ),
% 19.32/3.02      inference(superposition,[status(thm)],[c_2920,c_5354]) ).
% 19.32/3.02  
% 19.32/3.02  cnf(c_3735,plain,
% 19.32/3.02      ( X0 != X1 | X0 = k1_yellow_0(sK5,X2) | k1_yellow_0(sK5,X2) != X1 ),
% 19.32/3.02      inference(instantiation,[status(thm)],[c_2134]) ).
% 19.32/3.02  
% 19.32/3.02  cnf(c_5252,plain,
% 19.32/3.02      ( X0 = k1_yellow_0(sK5,k1_xboole_0)
% 19.32/3.02      | X0 != k3_yellow_0(sK5)
% 19.32/3.02      | k1_yellow_0(sK5,k1_xboole_0) != k3_yellow_0(sK5) ),
% 19.32/3.02      inference(instantiation,[status(thm)],[c_3735]) ).
% 19.32/3.02  
% 19.32/3.02  cnf(c_6041,plain,
% 19.32/3.02      ( k1_yellow_0(sK5,k1_xboole_0) != k3_yellow_0(sK5)
% 19.32/3.02      | k3_yellow_0(sK5) = k1_yellow_0(sK5,k1_xboole_0)
% 19.32/3.02      | k3_yellow_0(sK5) != k3_yellow_0(sK5) ),
% 19.32/3.02      inference(instantiation,[status(thm)],[c_5252]) ).
% 19.32/3.02  
% 19.32/3.02  cnf(c_2932,plain,
% 19.32/3.02      ( u1_struct_0(sK5) = sK6
% 19.32/3.02      | r2_hidden(k3_yellow_0(sK5),sK6) = iProver_top
% 19.32/3.02      | r1_tarski(sK6,u1_struct_0(sK5)) != iProver_top ),
% 19.32/3.02      inference(predicate_to_equality,[status(thm)],[c_632]) ).
% 19.32/3.02  
% 19.32/3.02  cnf(c_6280,plain,
% 19.32/3.02      ( r2_hidden(k3_yellow_0(sK5),sK6) = iProver_top
% 19.32/3.02      | u1_struct_0(sK5) = sK6 ),
% 19.32/3.02      inference(global_propositional_subsumption,
% 19.32/3.02                [status(thm)],
% 19.32/3.02                [c_2932,c_48,c_633,c_3265]) ).
% 19.32/3.02  
% 19.32/3.02  cnf(c_6281,plain,
% 19.32/3.02      ( u1_struct_0(sK5) = sK6
% 19.32/3.02      | r2_hidden(k3_yellow_0(sK5),sK6) = iProver_top ),
% 19.32/3.02      inference(renaming,[status(thm)],[c_6280]) ).
% 19.32/3.02  
% 19.32/3.02  cnf(c_6288,plain,
% 19.32/3.02      ( u1_struct_0(sK5) = sK6
% 19.32/3.02      | r2_lattice3(sK5,k1_xboole_0,X0) != iProver_top
% 19.32/3.02      | m1_subset_1(X0,u1_struct_0(sK5)) != iProver_top
% 19.32/3.02      | r2_hidden(X0,sK6) = iProver_top ),
% 19.32/3.02      inference(superposition,[status(thm)],[c_6281,c_4933]) ).
% 19.32/3.02  
% 19.32/3.02  cnf(c_6892,plain,
% 19.32/3.02      ( ~ m1_subset_1(k3_yellow_0(sK5),sK6)
% 19.32/3.02      | r2_hidden(k3_yellow_0(sK5),sK6)
% 19.32/3.02      | v1_xboole_0(sK6) ),
% 19.32/3.02      inference(instantiation,[status(thm)],[c_8]) ).
% 19.32/3.02  
% 19.32/3.02  cnf(c_6893,plain,
% 19.32/3.02      ( m1_subset_1(k3_yellow_0(sK5),sK6) != iProver_top
% 19.32/3.02      | r2_hidden(k3_yellow_0(sK5),sK6) = iProver_top
% 19.32/3.02      | v1_xboole_0(sK6) = iProver_top ),
% 19.32/3.02      inference(predicate_to_equality,[status(thm)],[c_6892]) ).
% 19.32/3.02  
% 19.32/3.02  cnf(c_2138,plain,
% 19.32/3.02      ( ~ m1_subset_1(X0,X1) | m1_subset_1(X2,X3) | X2 != X0 | X3 != X1 ),
% 19.32/3.02      theory(equality) ).
% 19.32/3.02  
% 19.32/3.02  cnf(c_5075,plain,
% 19.32/3.02      ( m1_subset_1(X0,X1)
% 19.32/3.02      | ~ m1_subset_1(k1_yellow_0(sK5,k1_xboole_0),u1_struct_0(X2))
% 19.32/3.02      | X0 != k1_yellow_0(sK5,k1_xboole_0)
% 19.32/3.02      | X1 != u1_struct_0(X2) ),
% 19.32/3.02      inference(instantiation,[status(thm)],[c_2138]) ).
% 19.32/3.02  
% 19.32/3.02  cnf(c_14182,plain,
% 19.32/3.02      ( ~ m1_subset_1(k1_yellow_0(sK5,k1_xboole_0),u1_struct_0(X0))
% 19.32/3.02      | m1_subset_1(k3_yellow_0(sK5),sK6)
% 19.32/3.02      | k3_yellow_0(sK5) != k1_yellow_0(sK5,k1_xboole_0)
% 19.32/3.02      | sK6 != u1_struct_0(X0) ),
% 19.32/3.02      inference(instantiation,[status(thm)],[c_5075]) ).
% 19.32/3.02  
% 19.32/3.02  cnf(c_14200,plain,
% 19.32/3.02      ( k3_yellow_0(sK5) != k1_yellow_0(sK5,k1_xboole_0)
% 19.32/3.02      | sK6 != u1_struct_0(X0)
% 19.32/3.02      | m1_subset_1(k1_yellow_0(sK5,k1_xboole_0),u1_struct_0(X0)) != iProver_top
% 19.32/3.02      | m1_subset_1(k3_yellow_0(sK5),sK6) = iProver_top ),
% 19.32/3.02      inference(predicate_to_equality,[status(thm)],[c_14182]) ).
% 19.32/3.02  
% 19.32/3.02  cnf(c_14202,plain,
% 19.32/3.02      ( k3_yellow_0(sK5) != k1_yellow_0(sK5,k1_xboole_0)
% 19.32/3.02      | sK6 != u1_struct_0(sK5)
% 19.32/3.02      | m1_subset_1(k1_yellow_0(sK5,k1_xboole_0),u1_struct_0(sK5)) != iProver_top
% 19.32/3.02      | m1_subset_1(k3_yellow_0(sK5),sK6) = iProver_top ),
% 19.32/3.02      inference(instantiation,[status(thm)],[c_14200]) ).
% 19.32/3.02  
% 19.32/3.02  cnf(c_17898,plain,
% 19.32/3.02      ( m1_subset_1(X0,u1_struct_0(sK5)) != iProver_top
% 19.32/3.02      | r2_hidden(X0,sK6) = iProver_top ),
% 19.32/3.02      inference(global_propositional_subsumption,
% 19.32/3.02                [status(thm)],
% 19.32/3.02                [c_17207,c_38,c_46,c_52,c_55,c_95,c_119,c_128,c_2159,
% 19.32/3.02                 c_3345,c_3554,c_4571,c_4933,c_5362,c_6041,c_6288,c_6893,
% 19.32/3.02                 c_14202]) ).
% 19.32/3.02  
% 19.32/3.02  cnf(c_17915,plain,
% 19.32/3.02      ( r2_hidden(sK0(u1_struct_0(sK5),X0),sK6) = iProver_top
% 19.32/3.02      | r1_tarski(u1_struct_0(sK5),X0) = iProver_top ),
% 19.32/3.02      inference(superposition,[status(thm)],[c_3965,c_17898]) ).
% 19.32/3.02  
% 19.32/3.02  cnf(c_0,plain,
% 19.32/3.02      ( ~ r2_hidden(sK0(X0,X1),X1) | r1_tarski(X0,X1) ),
% 19.32/3.02      inference(cnf_transformation,[],[f71]) ).
% 19.32/3.02  
% 19.32/3.02  cnf(c_2947,plain,
% 19.32/3.02      ( r2_hidden(sK0(X0,X1),X1) != iProver_top
% 19.32/3.02      | r1_tarski(X0,X1) = iProver_top ),
% 19.32/3.02      inference(predicate_to_equality,[status(thm)],[c_0]) ).
% 19.32/3.02  
% 19.32/3.02  cnf(c_98008,plain,
% 19.32/3.02      ( r1_tarski(u1_struct_0(sK5),sK6) = iProver_top ),
% 19.32/3.02      inference(superposition,[status(thm)],[c_17915,c_2947]) ).
% 19.32/3.02  
% 19.32/3.02  cnf(c_17913,plain,
% 19.32/3.02      ( r2_hidden(k3_yellow_0(sK5),sK6) = iProver_top ),
% 19.32/3.02      inference(superposition,[status(thm)],[c_3276,c_17898]) ).
% 19.32/3.02  
% 19.32/3.02  cnf(c_4,plain,
% 19.32/3.02      ( ~ r1_tarski(X0,X1) | ~ r1_tarski(X1,X0) | X1 = X0 ),
% 19.32/3.02      inference(cnf_transformation,[],[f75]) ).
% 19.32/3.02  
% 19.32/3.02  cnf(c_3461,plain,
% 19.32/3.02      ( ~ r1_tarski(X0,u1_struct_0(sK5))
% 19.32/3.02      | ~ r1_tarski(u1_struct_0(sK5),X0)
% 19.32/3.02      | X0 = u1_struct_0(sK5) ),
% 19.32/3.02      inference(instantiation,[status(thm)],[c_4]) ).
% 19.32/3.02  
% 19.32/3.02  cnf(c_4104,plain,
% 19.32/3.02      ( ~ r1_tarski(u1_struct_0(sK5),sK6)
% 19.32/3.02      | ~ r1_tarski(sK6,u1_struct_0(sK5))
% 19.32/3.02      | sK6 = u1_struct_0(sK5) ),
% 19.32/3.02      inference(instantiation,[status(thm)],[c_3461]) ).
% 19.32/3.02  
% 19.32/3.02  cnf(c_4106,plain,
% 19.32/3.02      ( sK6 = u1_struct_0(sK5)
% 19.32/3.02      | r1_tarski(u1_struct_0(sK5),sK6) != iProver_top
% 19.32/3.02      | r1_tarski(sK6,u1_struct_0(sK5)) != iProver_top ),
% 19.32/3.02      inference(predicate_to_equality,[status(thm)],[c_4104]) ).
% 19.32/3.02  
% 19.32/3.02  cnf(c_3394,plain,
% 19.32/3.02      ( r1_tarski(u1_struct_0(sK5),u1_struct_0(sK5)) ),
% 19.32/3.02      inference(instantiation,[status(thm)],[c_6]) ).
% 19.32/3.02  
% 19.32/3.02  cnf(c_3397,plain,
% 19.32/3.02      ( r1_tarski(u1_struct_0(sK5),u1_struct_0(sK5)) = iProver_top ),
% 19.32/3.02      inference(predicate_to_equality,[status(thm)],[c_3394]) ).
% 19.32/3.02  
% 19.32/3.02  cnf(c_3259,plain,
% 19.32/3.02      ( m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK5)))
% 19.32/3.02      | ~ r1_tarski(X0,u1_struct_0(sK5)) ),
% 19.32/3.02      inference(instantiation,[status(thm)],[c_9]) ).
% 19.32/3.02  
% 19.32/3.02  cnf(c_3393,plain,
% 19.32/3.02      ( m1_subset_1(u1_struct_0(sK5),k1_zfmisc_1(u1_struct_0(sK5)))
% 19.32/3.02      | ~ r1_tarski(u1_struct_0(sK5),u1_struct_0(sK5)) ),
% 19.32/3.02      inference(instantiation,[status(thm)],[c_3259]) ).
% 19.32/3.02  
% 19.32/3.02  cnf(c_3395,plain,
% 19.32/3.02      ( m1_subset_1(u1_struct_0(sK5),k1_zfmisc_1(u1_struct_0(sK5))) = iProver_top
% 19.32/3.02      | r1_tarski(u1_struct_0(sK5),u1_struct_0(sK5)) != iProver_top ),
% 19.32/3.02      inference(predicate_to_equality,[status(thm)],[c_3393]) ).
% 19.32/3.02  
% 19.32/3.02  cnf(c_34,negated_conjecture,
% 19.32/3.02      ( v1_subset_1(sK6,u1_struct_0(sK5))
% 19.32/3.02      | ~ r2_hidden(k3_yellow_0(sK5),sK6) ),
% 19.32/3.02      inference(cnf_transformation,[],[f109]) ).
% 19.32/3.02  
% 19.32/3.02  cnf(c_331,plain,
% 19.32/3.02      ( v1_subset_1(sK6,u1_struct_0(sK5))
% 19.32/3.02      | ~ r2_hidden(k3_yellow_0(sK5),sK6) ),
% 19.32/3.02      inference(prop_impl,[status(thm)],[c_34]) ).
% 19.32/3.02  
% 19.32/3.02  cnf(c_644,plain,
% 19.32/3.02      ( ~ m1_subset_1(X0,k1_zfmisc_1(X0))
% 19.32/3.02      | ~ r2_hidden(k3_yellow_0(sK5),sK6)
% 19.32/3.02      | u1_struct_0(sK5) != X0
% 19.32/3.02      | sK6 != X0 ),
% 19.32/3.02      inference(resolution_lifted,[status(thm)],[c_32,c_331]) ).
% 19.32/3.02  
% 19.32/3.02  cnf(c_645,plain,
% 19.32/3.02      ( ~ m1_subset_1(u1_struct_0(sK5),k1_zfmisc_1(u1_struct_0(sK5)))
% 19.32/3.02      | ~ r2_hidden(k3_yellow_0(sK5),sK6)
% 19.32/3.02      | sK6 != u1_struct_0(sK5) ),
% 19.32/3.02      inference(unflattening,[status(thm)],[c_644]) ).
% 19.32/3.02  
% 19.32/3.02  cnf(c_646,plain,
% 19.32/3.02      ( sK6 != u1_struct_0(sK5)
% 19.32/3.02      | m1_subset_1(u1_struct_0(sK5),k1_zfmisc_1(u1_struct_0(sK5))) != iProver_top
% 19.32/3.02      | r2_hidden(k3_yellow_0(sK5),sK6) != iProver_top ),
% 19.32/3.02      inference(predicate_to_equality,[status(thm)],[c_645]) ).
% 19.32/3.02  
% 19.32/3.02  cnf(contradiction,plain,
% 19.32/3.02      ( $false ),
% 19.32/3.02      inference(minisat,
% 19.32/3.02                [status(thm)],
% 19.32/3.02                [c_98008,c_17913,c_4106,c_3397,c_3395,c_3265,c_646,c_48]) ).
% 19.32/3.02  
% 19.32/3.02  
% 19.32/3.02  % SZS output end CNFRefutation for theBenchmark.p
% 19.32/3.02  
% 19.32/3.02  ------                               Statistics
% 19.32/3.02  
% 19.32/3.02  ------ General
% 19.32/3.02  
% 19.32/3.02  abstr_ref_over_cycles:                  0
% 19.32/3.02  abstr_ref_under_cycles:                 0
% 19.32/3.02  gc_basic_clause_elim:                   0
% 19.32/3.02  forced_gc_time:                         0
% 19.32/3.02  parsing_time:                           0.011
% 19.32/3.02  unif_index_cands_time:                  0.
% 19.32/3.02  unif_index_add_time:                    0.
% 19.32/3.02  orderings_time:                         0.
% 19.32/3.02  out_proof_time:                         0.019
% 19.32/3.02  total_time:                             2.347
% 19.32/3.02  num_of_symbols:                         56
% 19.32/3.02  num_of_terms:                           43289
% 19.32/3.02  
% 19.32/3.02  ------ Preprocessing
% 19.32/3.02  
% 19.32/3.02  num_of_splits:                          0
% 19.32/3.02  num_of_split_atoms:                     0
% 19.32/3.02  num_of_reused_defs:                     0
% 19.32/3.02  num_eq_ax_congr_red:                    33
% 19.32/3.02  num_of_sem_filtered_clauses:            1
% 19.32/3.02  num_of_subtypes:                        0
% 19.32/3.02  monotx_restored_types:                  0
% 19.32/3.02  sat_num_of_epr_types:                   0
% 19.32/3.02  sat_num_of_non_cyclic_types:            0
% 19.32/3.02  sat_guarded_non_collapsed_types:        0
% 19.32/3.02  num_pure_diseq_elim:                    0
% 19.32/3.02  simp_replaced_by:                       0
% 19.32/3.02  res_preprocessed:                       178
% 19.32/3.02  prep_upred:                             0
% 19.32/3.02  prep_unflattend:                        72
% 19.32/3.02  smt_new_axioms:                         0
% 19.32/3.02  pred_elim_cands:                        7
% 19.32/3.02  pred_elim:                              6
% 19.32/3.02  pred_elim_cl:                           7
% 19.32/3.02  pred_elim_cycles:                       12
% 19.32/3.02  merged_defs:                            10
% 19.32/3.02  merged_defs_ncl:                        0
% 19.32/3.02  bin_hyper_res:                          12
% 19.32/3.02  prep_cycles:                            4
% 19.32/3.02  pred_elim_time:                         0.024
% 19.32/3.02  splitting_time:                         0.
% 19.32/3.02  sem_filter_time:                        0.
% 19.32/3.02  monotx_time:                            0.001
% 19.32/3.02  subtype_inf_time:                       0.
% 19.32/3.02  
% 19.32/3.02  ------ Problem properties
% 19.32/3.02  
% 19.32/3.02  clauses:                                34
% 19.32/3.02  conjectures:                            3
% 19.32/3.02  epr:                                    9
% 19.32/3.02  horn:                                   23
% 19.32/3.02  ground:                                 8
% 19.32/3.02  unary:                                  8
% 19.32/3.02  binary:                                 5
% 19.32/3.02  lits:                                   89
% 19.32/3.02  lits_eq:                                7
% 19.32/3.02  fd_pure:                                0
% 19.32/3.02  fd_pseudo:                              0
% 19.32/3.02  fd_cond:                                3
% 19.32/3.02  fd_pseudo_cond:                         1
% 19.32/3.02  ac_symbols:                             0
% 19.32/3.02  
% 19.32/3.02  ------ Propositional Solver
% 19.32/3.02  
% 19.32/3.02  prop_solver_calls:                      33
% 19.32/3.02  prop_fast_solver_calls:                 4026
% 19.32/3.02  smt_solver_calls:                       0
% 19.32/3.02  smt_fast_solver_calls:                  0
% 19.32/3.02  prop_num_of_clauses:                    23739
% 19.32/3.02  prop_preprocess_simplified:             30469
% 19.32/3.02  prop_fo_subsumed:                       120
% 19.32/3.02  prop_solver_time:                       0.
% 19.32/3.02  smt_solver_time:                        0.
% 19.32/3.02  smt_fast_solver_time:                   0.
% 19.32/3.02  prop_fast_solver_time:                  0.
% 19.32/3.02  prop_unsat_core_time:                   0.001
% 19.32/3.02  
% 19.32/3.02  ------ QBF
% 19.32/3.02  
% 19.32/3.02  qbf_q_res:                              0
% 19.32/3.02  qbf_num_tautologies:                    0
% 19.32/3.02  qbf_prep_cycles:                        0
% 19.32/3.02  
% 19.32/3.02  ------ BMC1
% 19.32/3.02  
% 19.32/3.02  bmc1_current_bound:                     -1
% 19.32/3.02  bmc1_last_solved_bound:                 -1
% 19.32/3.02  bmc1_unsat_core_size:                   -1
% 19.32/3.02  bmc1_unsat_core_parents_size:           -1
% 19.32/3.02  bmc1_merge_next_fun:                    0
% 19.32/3.02  bmc1_unsat_core_clauses_time:           0.
% 19.32/3.02  
% 19.32/3.02  ------ Instantiation
% 19.32/3.02  
% 19.32/3.02  inst_num_of_clauses:                    4648
% 19.32/3.02  inst_num_in_passive:                    1404
% 19.32/3.02  inst_num_in_active:                     2031
% 19.32/3.02  inst_num_in_unprocessed:                1213
% 19.32/3.02  inst_num_of_loops:                      2660
% 19.32/3.02  inst_num_of_learning_restarts:          0
% 19.32/3.02  inst_num_moves_active_passive:          624
% 19.32/3.02  inst_lit_activity:                      0
% 19.32/3.02  inst_lit_activity_moves:                0
% 19.32/3.02  inst_num_tautologies:                   0
% 19.32/3.02  inst_num_prop_implied:                  0
% 19.32/3.02  inst_num_existing_simplified:           0
% 19.32/3.02  inst_num_eq_res_simplified:             0
% 19.32/3.02  inst_num_child_elim:                    0
% 19.32/3.02  inst_num_of_dismatching_blockings:      6904
% 19.32/3.02  inst_num_of_non_proper_insts:           8350
% 19.32/3.02  inst_num_of_duplicates:                 0
% 19.32/3.02  inst_inst_num_from_inst_to_res:         0
% 19.32/3.02  inst_dismatching_checking_time:         0.
% 19.32/3.02  
% 19.32/3.02  ------ Resolution
% 19.32/3.02  
% 19.32/3.02  res_num_of_clauses:                     0
% 19.32/3.02  res_num_in_passive:                     0
% 19.32/3.02  res_num_in_active:                      0
% 19.32/3.02  res_num_of_loops:                       182
% 19.32/3.02  res_forward_subset_subsumed:            613
% 19.32/3.02  res_backward_subset_subsumed:           6
% 19.32/3.02  res_forward_subsumed:                   0
% 19.32/3.02  res_backward_subsumed:                  0
% 19.32/3.02  res_forward_subsumption_resolution:     6
% 19.32/3.02  res_backward_subsumption_resolution:    0
% 19.32/3.02  res_clause_to_clause_subsumption:       33858
% 19.32/3.02  res_orphan_elimination:                 0
% 19.32/3.02  res_tautology_del:                      553
% 19.32/3.02  res_num_eq_res_simplified:              0
% 19.32/3.02  res_num_sel_changes:                    0
% 19.32/3.02  res_moves_from_active_to_pass:          0
% 19.32/3.02  
% 19.32/3.02  ------ Superposition
% 19.32/3.02  
% 19.32/3.02  sup_time_total:                         0.
% 19.32/3.02  sup_time_generating:                    0.
% 19.32/3.02  sup_time_sim_full:                      0.
% 19.32/3.02  sup_time_sim_immed:                     0.
% 19.32/3.02  
% 19.32/3.02  sup_num_of_clauses:                     2841
% 19.32/3.02  sup_num_in_active:                      528
% 19.32/3.02  sup_num_in_passive:                     2313
% 19.32/3.02  sup_num_of_loops:                       530
% 19.32/3.02  sup_fw_superposition:                   1997
% 19.32/3.02  sup_bw_superposition:                   2340
% 19.32/3.02  sup_immediate_simplified:               1132
% 19.32/3.02  sup_given_eliminated:                   0
% 19.32/3.02  comparisons_done:                       0
% 19.32/3.02  comparisons_avoided:                    1
% 19.32/3.02  
% 19.32/3.02  ------ Simplifications
% 19.32/3.02  
% 19.32/3.02  
% 19.32/3.02  sim_fw_subset_subsumed:                 443
% 19.32/3.02  sim_bw_subset_subsumed:                 41
% 19.32/3.02  sim_fw_subsumed:                        489
% 19.32/3.02  sim_bw_subsumed:                        138
% 19.32/3.02  sim_fw_subsumption_res:                 21
% 19.32/3.02  sim_bw_subsumption_res:                 28
% 19.32/3.02  sim_tautology_del:                      61
% 19.32/3.02  sim_eq_tautology_del:                   13
% 19.32/3.02  sim_eq_res_simp:                        0
% 19.32/3.02  sim_fw_demodulated:                     4
% 19.32/3.02  sim_bw_demodulated:                     0
% 19.32/3.02  sim_light_normalised:                   41
% 19.32/3.02  sim_joinable_taut:                      0
% 19.32/3.02  sim_joinable_simp:                      0
% 19.32/3.02  sim_ac_normalised:                      0
% 19.32/3.02  sim_smt_subsumption:                    0
% 19.32/3.02  
%------------------------------------------------------------------------------
