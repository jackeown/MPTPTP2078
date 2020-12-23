%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n011.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:28:32 EST 2020

% Result     : Theorem 4.04s
% Output     : CNFRefutation 4.04s
% Verified   : 
% Statistics : Number of formulae       :  224 (5859 expanded)
%              Number of clauses        :  136 (1426 expanded)
%              Number of leaves         :   22 (1129 expanded)
%              Depth                    :   33
%              Number of atoms          :  894 (41051 expanded)
%              Number of equality atoms :  243 (2324 expanded)
%              Maximal formula depth    :   14 (   5 average)
%              Maximal clause size      :   22 (   3 average)
%              Maximal term depth       :    5 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f3,axiom,(
    ! [X0,X1] :
      ( k1_zfmisc_1(X0) = X1
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
        <=> r1_tarski(X2,X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f38,plain,(
    ! [X0,X1] :
      ( ( k1_zfmisc_1(X0) = X1
        | ? [X2] :
            ( ( ~ r1_tarski(X2,X0)
              | ~ r2_hidden(X2,X1) )
            & ( r1_tarski(X2,X0)
              | r2_hidden(X2,X1) ) ) )
      & ( ! [X2] :
            ( ( r2_hidden(X2,X1)
              | ~ r1_tarski(X2,X0) )
            & ( r1_tarski(X2,X0)
              | ~ r2_hidden(X2,X1) ) )
        | k1_zfmisc_1(X0) != X1 ) ) ),
    inference(nnf_transformation,[],[f3])).

fof(f39,plain,(
    ! [X0,X1] :
      ( ( k1_zfmisc_1(X0) = X1
        | ? [X2] :
            ( ( ~ r1_tarski(X2,X0)
              | ~ r2_hidden(X2,X1) )
            & ( r1_tarski(X2,X0)
              | r2_hidden(X2,X1) ) ) )
      & ( ! [X3] :
            ( ( r2_hidden(X3,X1)
              | ~ r1_tarski(X3,X0) )
            & ( r1_tarski(X3,X0)
              | ~ r2_hidden(X3,X1) ) )
        | k1_zfmisc_1(X0) != X1 ) ) ),
    inference(rectify,[],[f38])).

fof(f40,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ( ~ r1_tarski(X2,X0)
            | ~ r2_hidden(X2,X1) )
          & ( r1_tarski(X2,X0)
            | r2_hidden(X2,X1) ) )
     => ( ( ~ r1_tarski(sK2(X0,X1),X0)
          | ~ r2_hidden(sK2(X0,X1),X1) )
        & ( r1_tarski(sK2(X0,X1),X0)
          | r2_hidden(sK2(X0,X1),X1) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f41,plain,(
    ! [X0,X1] :
      ( ( k1_zfmisc_1(X0) = X1
        | ( ( ~ r1_tarski(sK2(X0,X1),X0)
            | ~ r2_hidden(sK2(X0,X1),X1) )
          & ( r1_tarski(sK2(X0,X1),X0)
            | r2_hidden(sK2(X0,X1),X1) ) ) )
      & ( ! [X3] :
            ( ( r2_hidden(X3,X1)
              | ~ r1_tarski(X3,X0) )
            & ( r1_tarski(X3,X0)
              | ~ r2_hidden(X3,X1) ) )
        | k1_zfmisc_1(X0) != X1 ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2])],[f39,f40])).

fof(f65,plain,(
    ! [X0,X1] :
      ( k1_zfmisc_1(X0) = X1
      | r1_tarski(sK2(X0,X1),X0)
      | r2_hidden(sK2(X0,X1),X1) ) ),
    inference(cnf_transformation,[],[f41])).

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
    inference(ennf_transformation,[],[f15])).

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

fof(f53,plain,(
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

fof(f54,plain,(
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
    inference(flattening,[],[f53])).

fof(f56,plain,(
    ! [X0] :
      ( ? [X1] :
          ( ( r2_hidden(k3_yellow_0(X0),X1)
            | ~ v1_subset_1(X1,u1_struct_0(X0)) )
          & ( ~ r2_hidden(k3_yellow_0(X0),X1)
            | v1_subset_1(X1,u1_struct_0(X0)) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
          & v13_waybel_0(X1,X0)
          & ~ v1_xboole_0(X1) )
     => ( ( r2_hidden(k3_yellow_0(X0),sK7)
          | ~ v1_subset_1(sK7,u1_struct_0(X0)) )
        & ( ~ r2_hidden(k3_yellow_0(X0),sK7)
          | v1_subset_1(sK7,u1_struct_0(X0)) )
        & m1_subset_1(sK7,k1_zfmisc_1(u1_struct_0(X0)))
        & v13_waybel_0(sK7,X0)
        & ~ v1_xboole_0(sK7) ) ) ),
    introduced(choice_axiom,[])).

fof(f55,plain,
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
          ( ( r2_hidden(k3_yellow_0(sK6),X1)
            | ~ v1_subset_1(X1,u1_struct_0(sK6)) )
          & ( ~ r2_hidden(k3_yellow_0(sK6),X1)
            | v1_subset_1(X1,u1_struct_0(sK6)) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK6)))
          & v13_waybel_0(X1,sK6)
          & ~ v1_xboole_0(X1) )
      & l1_orders_2(sK6)
      & v1_yellow_0(sK6)
      & v5_orders_2(sK6)
      & ~ v2_struct_0(sK6) ) ),
    introduced(choice_axiom,[])).

fof(f57,plain,
    ( ( r2_hidden(k3_yellow_0(sK6),sK7)
      | ~ v1_subset_1(sK7,u1_struct_0(sK6)) )
    & ( ~ r2_hidden(k3_yellow_0(sK6),sK7)
      | v1_subset_1(sK7,u1_struct_0(sK6)) )
    & m1_subset_1(sK7,k1_zfmisc_1(u1_struct_0(sK6)))
    & v13_waybel_0(sK7,sK6)
    & ~ v1_xboole_0(sK7)
    & l1_orders_2(sK6)
    & v1_yellow_0(sK6)
    & v5_orders_2(sK6)
    & ~ v2_struct_0(sK6) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK6,sK7])],[f54,f56,f55])).

fof(f91,plain,(
    m1_subset_1(sK7,k1_zfmisc_1(u1_struct_0(sK6))) ),
    inference(cnf_transformation,[],[f57])).

fof(f10,axiom,(
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
    inference(ennf_transformation,[],[f10])).

fof(f52,plain,(
    ! [X0,X1] :
      ( ( ( v1_subset_1(X1,X0)
          | X0 = X1 )
        & ( X0 != X1
          | ~ v1_subset_1(X1,X0) ) )
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(nnf_transformation,[],[f27])).

fof(f84,plain,(
    ! [X0,X1] :
      ( v1_subset_1(X1,X0)
      | X0 = X1
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f52])).

fof(f93,plain,
    ( r2_hidden(k3_yellow_0(sK6),sK7)
    | ~ v1_subset_1(sK7,u1_struct_0(sK6)) ),
    inference(cnf_transformation,[],[f57])).

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

fof(f23,plain,(
    ! [X0] :
      ( ! [X1] :
          ( r1_orders_2(X0,k3_yellow_0(X0),X1)
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l1_orders_2(X0)
      | ~ v1_yellow_0(X0)
      | ~ v5_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f8])).

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

fof(f76,plain,(
    ! [X0,X1] :
      ( r1_orders_2(X0,k3_yellow_0(X0),X1)
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | ~ v1_yellow_0(X0)
      | ~ v5_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f24])).

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

fof(f59,plain,(
    ! [X0] :
      ( v1_xboole_0(X0)
      | r2_hidden(sK0(X0),X0) ) ),
    inference(cnf_transformation,[],[f33])).

fof(f64,plain,(
    ! [X0,X3,X1] :
      ( r2_hidden(X3,X1)
      | ~ r1_tarski(X3,X0)
      | k1_zfmisc_1(X0) != X1 ) ),
    inference(cnf_transformation,[],[f41])).

fof(f94,plain,(
    ! [X0,X3] :
      ( r2_hidden(X3,k1_zfmisc_1(X0))
      | ~ r1_tarski(X3,X0) ) ),
    inference(equality_resolution,[],[f64])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( ( v1_xboole_0(X0)
       => ( m1_subset_1(X1,X0)
        <=> v1_xboole_0(X1) ) )
      & ( ~ v1_xboole_0(X0)
       => ( m1_subset_1(X1,X0)
        <=> r2_hidden(X1,X0) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f17,plain,(
    ! [X0,X1] :
      ( ( ( m1_subset_1(X1,X0)
        <=> v1_xboole_0(X1) )
        | ~ v1_xboole_0(X0) )
      & ( ( m1_subset_1(X1,X0)
        <=> r2_hidden(X1,X0) )
        | v1_xboole_0(X0) ) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f42,plain,(
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
    inference(nnf_transformation,[],[f17])).

fof(f68,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X1,X0)
      | ~ r2_hidden(X1,X0)
      | v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f42])).

fof(f58,plain,(
    ! [X2,X0] :
      ( ~ r2_hidden(X2,X0)
      | ~ v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f33])).

fof(f6,axiom,(
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
    inference(ennf_transformation,[],[f6])).

fof(f21,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X0,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(flattening,[],[f20])).

fof(f74,plain,(
    ! [X2,X0,X1] :
      ( m1_subset_1(X0,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f21])).

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
    inference(ennf_transformation,[],[f9])).

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

fof(f47,plain,(
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

fof(f48,plain,(
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
    inference(rectify,[],[f47])).

fof(f50,plain,(
    ! [X2,X1,X0] :
      ( ? [X3] :
          ( ~ r2_hidden(X3,X1)
          & r1_orders_2(X0,X2,X3)
          & r2_hidden(X2,X1)
          & m1_subset_1(X3,u1_struct_0(X0)) )
     => ( ~ r2_hidden(sK5(X0,X1),X1)
        & r1_orders_2(X0,X2,sK5(X0,X1))
        & r2_hidden(X2,X1)
        & m1_subset_1(sK5(X0,X1),u1_struct_0(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f49,plain,(
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
            & r1_orders_2(X0,sK4(X0,X1),X3)
            & r2_hidden(sK4(X0,X1),X1)
            & m1_subset_1(X3,u1_struct_0(X0)) )
        & m1_subset_1(sK4(X0,X1),u1_struct_0(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f51,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ( v13_waybel_0(X1,X0)
              | ( ~ r2_hidden(sK5(X0,X1),X1)
                & r1_orders_2(X0,sK4(X0,X1),sK5(X0,X1))
                & r2_hidden(sK4(X0,X1),X1)
                & m1_subset_1(sK5(X0,X1),u1_struct_0(X0))
                & m1_subset_1(sK4(X0,X1),u1_struct_0(X0)) ) )
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
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4,sK5])],[f48,f50,f49])).

fof(f77,plain,(
    ! [X4,X0,X5,X1] :
      ( r2_hidden(X5,X1)
      | ~ r1_orders_2(X0,X4,X5)
      | ~ r2_hidden(X4,X1)
      | ~ m1_subset_1(X5,u1_struct_0(X0))
      | ~ m1_subset_1(X4,u1_struct_0(X0))
      | ~ v13_waybel_0(X1,X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f51])).

fof(f88,plain,(
    l1_orders_2(sK6) ),
    inference(cnf_transformation,[],[f57])).

fof(f90,plain,(
    v13_waybel_0(sK7,sK6) ),
    inference(cnf_transformation,[],[f57])).

fof(f85,plain,(
    ~ v2_struct_0(sK6) ),
    inference(cnf_transformation,[],[f57])).

fof(f86,plain,(
    v5_orders_2(sK6) ),
    inference(cnf_transformation,[],[f57])).

fof(f87,plain,(
    v1_yellow_0(sK6) ),
    inference(cnf_transformation,[],[f57])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
    <=> ! [X2] :
          ( r2_hidden(X2,X0)
         => r2_hidden(X2,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f16,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
          | ~ r2_hidden(X2,X0) ) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f34,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ? [X2] :
            ( ~ r2_hidden(X2,X1)
            & r2_hidden(X2,X0) ) )
      & ( ! [X2] :
            ( r2_hidden(X2,X1)
            | ~ r2_hidden(X2,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(nnf_transformation,[],[f16])).

fof(f35,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ? [X2] :
            ( ~ r2_hidden(X2,X1)
            & r2_hidden(X2,X0) ) )
      & ( ! [X3] :
            ( r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(rectify,[],[f34])).

fof(f36,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ~ r2_hidden(X2,X1)
          & r2_hidden(X2,X0) )
     => ( ~ r2_hidden(sK1(X0,X1),X1)
        & r2_hidden(sK1(X0,X1),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f37,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ( ~ r2_hidden(sK1(X0,X1),X1)
          & r2_hidden(sK1(X0,X1),X0) ) )
      & ( ! [X3] :
            ( r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1])],[f35,f36])).

fof(f61,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | r2_hidden(sK1(X0,X1),X0) ) ),
    inference(cnf_transformation,[],[f37])).

fof(f62,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | ~ r2_hidden(sK1(X0,X1),X1) ) ),
    inference(cnf_transformation,[],[f37])).

fof(f5,axiom,(
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
    inference(ennf_transformation,[],[f5])).

fof(f19,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( X1 = X2
          | ? [X3] :
              ( ( r2_hidden(X3,X1)
              <~> r2_hidden(X3,X2) )
              & m1_subset_1(X3,X0) )
          | ~ m1_subset_1(X2,k1_zfmisc_1(X0)) )
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(flattening,[],[f18])).

fof(f43,plain,(
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
    inference(nnf_transformation,[],[f19])).

fof(f44,plain,(
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
    inference(flattening,[],[f43])).

fof(f45,plain,(
    ! [X2,X1,X0] :
      ( ? [X3] :
          ( ( ~ r2_hidden(X3,X2)
            | ~ r2_hidden(X3,X1) )
          & ( r2_hidden(X3,X2)
            | r2_hidden(X3,X1) )
          & m1_subset_1(X3,X0) )
     => ( ( ~ r2_hidden(sK3(X0,X1,X2),X2)
          | ~ r2_hidden(sK3(X0,X1,X2),X1) )
        & ( r2_hidden(sK3(X0,X1,X2),X2)
          | r2_hidden(sK3(X0,X1,X2),X1) )
        & m1_subset_1(sK3(X0,X1,X2),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f46,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( X1 = X2
          | ( ( ~ r2_hidden(sK3(X0,X1,X2),X2)
              | ~ r2_hidden(sK3(X0,X1,X2),X1) )
            & ( r2_hidden(sK3(X0,X1,X2),X2)
              | r2_hidden(sK3(X0,X1,X2),X1) )
            & m1_subset_1(sK3(X0,X1,X2),X0) )
          | ~ m1_subset_1(X2,k1_zfmisc_1(X0)) )
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3])],[f44,f45])).

fof(f73,plain,(
    ! [X2,X0,X1] :
      ( X1 = X2
      | ~ r2_hidden(sK3(X0,X1,X2),X2)
      | ~ r2_hidden(sK3(X0,X1,X2),X1)
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f46])).

fof(f67,plain,(
    ! [X0,X1] :
      ( r2_hidden(X1,X0)
      | ~ m1_subset_1(X1,X0)
      | v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f42])).

fof(f89,plain,(
    ~ v1_xboole_0(sK7) ),
    inference(cnf_transformation,[],[f57])).

fof(f69,plain,(
    ! [X0,X1] :
      ( v1_xboole_0(X1)
      | ~ m1_subset_1(X1,X0)
      | ~ v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f42])).

fof(f63,plain,(
    ! [X0,X3,X1] :
      ( r1_tarski(X3,X0)
      | ~ r2_hidden(X3,X1)
      | k1_zfmisc_1(X0) != X1 ) ),
    inference(cnf_transformation,[],[f41])).

fof(f95,plain,(
    ! [X0,X3] :
      ( r1_tarski(X3,X0)
      | ~ r2_hidden(X3,k1_zfmisc_1(X0)) ) ),
    inference(equality_resolution,[],[f63])).

fof(f60,plain,(
    ! [X0,X3,X1] :
      ( r2_hidden(X3,X1)
      | ~ r2_hidden(X3,X0)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f37])).

fof(f72,plain,(
    ! [X2,X0,X1] :
      ( X1 = X2
      | r2_hidden(sK3(X0,X1,X2),X2)
      | r2_hidden(sK3(X0,X1,X2),X1)
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f46])).

fof(f7,axiom,(
    ! [X0] :
      ( l1_orders_2(X0)
     => m1_subset_1(k3_yellow_0(X0),u1_struct_0(X0)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f22,plain,(
    ! [X0] :
      ( m1_subset_1(k3_yellow_0(X0),u1_struct_0(X0))
      | ~ l1_orders_2(X0) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f75,plain,(
    ! [X0] :
      ( m1_subset_1(k3_yellow_0(X0),u1_struct_0(X0))
      | ~ l1_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f83,plain,(
    ! [X0,X1] :
      ( X0 != X1
      | ~ v1_subset_1(X1,X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f52])).

fof(f96,plain,(
    ! [X1] :
      ( ~ v1_subset_1(X1,X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X1)) ) ),
    inference(equality_resolution,[],[f83])).

fof(f92,plain,
    ( ~ r2_hidden(k3_yellow_0(sK6),sK7)
    | v1_subset_1(sK7,u1_struct_0(sK6)) ),
    inference(cnf_transformation,[],[f57])).

cnf(c_6,plain,
    ( r1_tarski(sK2(X0,X1),X0)
    | r2_hidden(sK2(X0,X1),X1)
    | k1_zfmisc_1(X0) = X1 ),
    inference(cnf_transformation,[],[f65])).

cnf(c_1306,plain,
    ( k1_zfmisc_1(X0) = X1
    | r1_tarski(sK2(X0,X1),X0) = iProver_top
    | r2_hidden(sK2(X0,X1),X1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_6])).

cnf(c_29,negated_conjecture,
    ( m1_subset_1(sK7,k1_zfmisc_1(u1_struct_0(sK6))) ),
    inference(cnf_transformation,[],[f91])).

cnf(c_1284,plain,
    ( m1_subset_1(sK7,k1_zfmisc_1(u1_struct_0(sK6))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_29])).

cnf(c_25,plain,
    ( v1_subset_1(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | X0 = X1 ),
    inference(cnf_transformation,[],[f84])).

cnf(c_1288,plain,
    ( X0 = X1
    | v1_subset_1(X0,X1) = iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(X1)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_25])).

cnf(c_2649,plain,
    ( u1_struct_0(sK6) = sK7
    | v1_subset_1(sK7,u1_struct_0(sK6)) = iProver_top ),
    inference(superposition,[status(thm)],[c_1284,c_1288])).

cnf(c_27,negated_conjecture,
    ( ~ v1_subset_1(sK7,u1_struct_0(sK6))
    | r2_hidden(k3_yellow_0(sK6),sK7) ),
    inference(cnf_transformation,[],[f93])).

cnf(c_1286,plain,
    ( v1_subset_1(sK7,u1_struct_0(sK6)) != iProver_top
    | r2_hidden(k3_yellow_0(sK6),sK7) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_27])).

cnf(c_3091,plain,
    ( u1_struct_0(sK6) = sK7
    | r2_hidden(k3_yellow_0(sK6),sK7) = iProver_top ),
    inference(superposition,[status(thm)],[c_2649,c_1286])).

cnf(c_18,plain,
    ( r1_orders_2(X0,k3_yellow_0(X0),X1)
    | ~ m1_subset_1(X1,u1_struct_0(X0))
    | v2_struct_0(X0)
    | ~ v5_orders_2(X0)
    | ~ v1_yellow_0(X0)
    | ~ l1_orders_2(X0) ),
    inference(cnf_transformation,[],[f76])).

cnf(c_1295,plain,
    ( r1_orders_2(X0,k3_yellow_0(X0),X1) = iProver_top
    | m1_subset_1(X1,u1_struct_0(X0)) != iProver_top
    | v2_struct_0(X0) = iProver_top
    | v5_orders_2(X0) != iProver_top
    | v1_yellow_0(X0) != iProver_top
    | l1_orders_2(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_18])).

cnf(c_0,plain,
    ( r2_hidden(sK0(X0),X0)
    | v1_xboole_0(X0) ),
    inference(cnf_transformation,[],[f59])).

cnf(c_1312,plain,
    ( r2_hidden(sK0(X0),X0) = iProver_top
    | v1_xboole_0(X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_0])).

cnf(c_7,plain,
    ( ~ r1_tarski(X0,X1)
    | r2_hidden(X0,k1_zfmisc_1(X1)) ),
    inference(cnf_transformation,[],[f94])).

cnf(c_1305,plain,
    ( r1_tarski(X0,X1) != iProver_top
    | r2_hidden(X0,k1_zfmisc_1(X1)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_7])).

cnf(c_11,plain,
    ( m1_subset_1(X0,X1)
    | ~ r2_hidden(X0,X1)
    | v1_xboole_0(X1) ),
    inference(cnf_transformation,[],[f68])).

cnf(c_1,plain,
    ( ~ r2_hidden(X0,X1)
    | ~ v1_xboole_0(X1) ),
    inference(cnf_transformation,[],[f58])).

cnf(c_354,plain,
    ( ~ r2_hidden(X0,X1)
    | m1_subset_1(X0,X1) ),
    inference(global_propositional_subsumption,[status(thm)],[c_11,c_1])).

cnf(c_355,plain,
    ( m1_subset_1(X0,X1)
    | ~ r2_hidden(X0,X1) ),
    inference(renaming,[status(thm)],[c_354])).

cnf(c_1277,plain,
    ( m1_subset_1(X0,X1) = iProver_top
    | r2_hidden(X0,X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_355])).

cnf(c_2243,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(X1)) = iProver_top
    | r1_tarski(X0,X1) != iProver_top ),
    inference(superposition,[status(thm)],[c_1305,c_1277])).

cnf(c_16,plain,
    ( m1_subset_1(X0,X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(X1))
    | ~ r2_hidden(X0,X2) ),
    inference(cnf_transformation,[],[f74])).

cnf(c_1297,plain,
    ( m1_subset_1(X0,X1) = iProver_top
    | m1_subset_1(X2,k1_zfmisc_1(X1)) != iProver_top
    | r2_hidden(X0,X2) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_16])).

cnf(c_3509,plain,
    ( m1_subset_1(X0,X1) = iProver_top
    | r1_tarski(X2,X1) != iProver_top
    | r2_hidden(X0,X2) != iProver_top ),
    inference(superposition,[status(thm)],[c_2243,c_1297])).

cnf(c_6689,plain,
    ( m1_subset_1(sK0(X0),X1) = iProver_top
    | r1_tarski(X0,X1) != iProver_top
    | v1_xboole_0(X0) = iProver_top ),
    inference(superposition,[status(thm)],[c_1312,c_3509])).

cnf(c_24,plain,
    ( ~ r1_orders_2(X0,X1,X2)
    | ~ v13_waybel_0(X3,X0)
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | ~ m1_subset_1(X1,u1_struct_0(X0))
    | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))
    | ~ r2_hidden(X1,X3)
    | r2_hidden(X2,X3)
    | ~ l1_orders_2(X0) ),
    inference(cnf_transformation,[],[f77])).

cnf(c_1289,plain,
    ( r1_orders_2(X0,X1,X2) != iProver_top
    | v13_waybel_0(X3,X0) != iProver_top
    | m1_subset_1(X2,u1_struct_0(X0)) != iProver_top
    | m1_subset_1(X1,u1_struct_0(X0)) != iProver_top
    | m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) != iProver_top
    | r2_hidden(X1,X3) != iProver_top
    | r2_hidden(X2,X3) = iProver_top
    | l1_orders_2(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_24])).

cnf(c_1507,plain,
    ( r1_orders_2(X0,X1,X2) != iProver_top
    | v13_waybel_0(X3,X0) != iProver_top
    | m1_subset_1(X2,u1_struct_0(X0)) != iProver_top
    | m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) != iProver_top
    | r2_hidden(X1,X3) != iProver_top
    | r2_hidden(X2,X3) = iProver_top
    | l1_orders_2(X0) != iProver_top ),
    inference(forward_subsumption_resolution,[status(thm)],[c_1289,c_1297])).

cnf(c_6961,plain,
    ( r1_orders_2(sK6,X0,X1) != iProver_top
    | v13_waybel_0(sK7,sK6) != iProver_top
    | m1_subset_1(X1,u1_struct_0(sK6)) != iProver_top
    | r2_hidden(X0,sK7) != iProver_top
    | r2_hidden(X1,sK7) = iProver_top
    | l1_orders_2(sK6) != iProver_top ),
    inference(superposition,[status(thm)],[c_1284,c_1507])).

cnf(c_32,negated_conjecture,
    ( l1_orders_2(sK6) ),
    inference(cnf_transformation,[],[f88])).

cnf(c_39,plain,
    ( l1_orders_2(sK6) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_32])).

cnf(c_30,negated_conjecture,
    ( v13_waybel_0(sK7,sK6) ),
    inference(cnf_transformation,[],[f90])).

cnf(c_41,plain,
    ( v13_waybel_0(sK7,sK6) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_30])).

cnf(c_7523,plain,
    ( r2_hidden(X1,sK7) = iProver_top
    | r2_hidden(X0,sK7) != iProver_top
    | m1_subset_1(X1,u1_struct_0(sK6)) != iProver_top
    | r1_orders_2(sK6,X0,X1) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_6961,c_39,c_41])).

cnf(c_7524,plain,
    ( r1_orders_2(sK6,X0,X1) != iProver_top
    | m1_subset_1(X1,u1_struct_0(sK6)) != iProver_top
    | r2_hidden(X0,sK7) != iProver_top
    | r2_hidden(X1,sK7) = iProver_top ),
    inference(renaming,[status(thm)],[c_7523])).

cnf(c_11109,plain,
    ( r1_orders_2(sK6,X0,sK0(X1)) != iProver_top
    | r1_tarski(X1,u1_struct_0(sK6)) != iProver_top
    | r2_hidden(X0,sK7) != iProver_top
    | r2_hidden(sK0(X1),sK7) = iProver_top
    | v1_xboole_0(X1) = iProver_top ),
    inference(superposition,[status(thm)],[c_6689,c_7524])).

cnf(c_11495,plain,
    ( m1_subset_1(sK0(X0),u1_struct_0(sK6)) != iProver_top
    | r1_tarski(X0,u1_struct_0(sK6)) != iProver_top
    | r2_hidden(k3_yellow_0(sK6),sK7) != iProver_top
    | r2_hidden(sK0(X0),sK7) = iProver_top
    | v2_struct_0(sK6) = iProver_top
    | v5_orders_2(sK6) != iProver_top
    | v1_yellow_0(sK6) != iProver_top
    | l1_orders_2(sK6) != iProver_top
    | v1_xboole_0(X0) = iProver_top ),
    inference(superposition,[status(thm)],[c_1295,c_11109])).

cnf(c_35,negated_conjecture,
    ( ~ v2_struct_0(sK6) ),
    inference(cnf_transformation,[],[f85])).

cnf(c_36,plain,
    ( v2_struct_0(sK6) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_35])).

cnf(c_34,negated_conjecture,
    ( v5_orders_2(sK6) ),
    inference(cnf_transformation,[],[f86])).

cnf(c_37,plain,
    ( v5_orders_2(sK6) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_34])).

cnf(c_33,negated_conjecture,
    ( v1_yellow_0(sK6) ),
    inference(cnf_transformation,[],[f87])).

cnf(c_38,plain,
    ( v1_yellow_0(sK6) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_33])).

cnf(c_11872,plain,
    ( m1_subset_1(sK0(X0),u1_struct_0(sK6)) != iProver_top
    | r1_tarski(X0,u1_struct_0(sK6)) != iProver_top
    | r2_hidden(k3_yellow_0(sK6),sK7) != iProver_top
    | r2_hidden(sK0(X0),sK7) = iProver_top
    | v1_xboole_0(X0) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_11495,c_36,c_37,c_38,c_39])).

cnf(c_11883,plain,
    ( r1_tarski(X0,u1_struct_0(sK6)) != iProver_top
    | r2_hidden(k3_yellow_0(sK6),sK7) != iProver_top
    | r2_hidden(sK0(X0),sK7) = iProver_top
    | v1_xboole_0(X0) = iProver_top ),
    inference(forward_subsumption_resolution,[status(thm)],[c_11872,c_6689])).

cnf(c_11887,plain,
    ( u1_struct_0(sK6) = sK7
    | r1_tarski(X0,u1_struct_0(sK6)) != iProver_top
    | r2_hidden(sK0(X0),sK7) = iProver_top
    | v1_xboole_0(X0) = iProver_top ),
    inference(superposition,[status(thm)],[c_3091,c_11883])).

cnf(c_11917,plain,
    ( u1_struct_0(sK6) = sK7
    | k1_zfmisc_1(u1_struct_0(sK6)) = X0
    | r2_hidden(sK2(u1_struct_0(sK6),X0),X0) = iProver_top
    | r2_hidden(sK0(sK2(u1_struct_0(sK6),X0)),sK7) = iProver_top
    | v1_xboole_0(sK2(u1_struct_0(sK6),X0)) = iProver_top ),
    inference(superposition,[status(thm)],[c_1306,c_11887])).

cnf(c_3,plain,
    ( r1_tarski(X0,X1)
    | r2_hidden(sK1(X0,X1),X0) ),
    inference(cnf_transformation,[],[f61])).

cnf(c_1309,plain,
    ( r1_tarski(X0,X1) = iProver_top
    | r2_hidden(sK1(X0,X1),X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3])).

cnf(c_2666,plain,
    ( m1_subset_1(sK1(X0,X1),X0) = iProver_top
    | r1_tarski(X0,X1) = iProver_top ),
    inference(superposition,[status(thm)],[c_1309,c_1277])).

cnf(c_7537,plain,
    ( r1_orders_2(sK6,X0,sK1(u1_struct_0(sK6),X1)) != iProver_top
    | r1_tarski(u1_struct_0(sK6),X1) = iProver_top
    | r2_hidden(X0,sK7) != iProver_top
    | r2_hidden(sK1(u1_struct_0(sK6),X1),sK7) = iProver_top ),
    inference(superposition,[status(thm)],[c_2666,c_7524])).

cnf(c_8022,plain,
    ( m1_subset_1(sK1(u1_struct_0(sK6),X0),u1_struct_0(sK6)) != iProver_top
    | r1_tarski(u1_struct_0(sK6),X0) = iProver_top
    | r2_hidden(sK1(u1_struct_0(sK6),X0),sK7) = iProver_top
    | r2_hidden(k3_yellow_0(sK6),sK7) != iProver_top
    | v2_struct_0(sK6) = iProver_top
    | v5_orders_2(sK6) != iProver_top
    | v1_yellow_0(sK6) != iProver_top
    | l1_orders_2(sK6) != iProver_top ),
    inference(superposition,[status(thm)],[c_1295,c_7537])).

cnf(c_11638,plain,
    ( m1_subset_1(sK1(u1_struct_0(sK6),X0),u1_struct_0(sK6)) != iProver_top
    | r1_tarski(u1_struct_0(sK6),X0) = iProver_top
    | r2_hidden(sK1(u1_struct_0(sK6),X0),sK7) = iProver_top
    | r2_hidden(k3_yellow_0(sK6),sK7) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_8022,c_36,c_37,c_38,c_39])).

cnf(c_11648,plain,
    ( r1_tarski(u1_struct_0(sK6),X0) = iProver_top
    | r2_hidden(sK1(u1_struct_0(sK6),X0),sK7) = iProver_top
    | r2_hidden(k3_yellow_0(sK6),sK7) != iProver_top ),
    inference(forward_subsumption_resolution,[status(thm)],[c_11638,c_2666])).

cnf(c_2,plain,
    ( r1_tarski(X0,X1)
    | ~ r2_hidden(sK1(X0,X1),X1) ),
    inference(cnf_transformation,[],[f62])).

cnf(c_1310,plain,
    ( r1_tarski(X0,X1) = iProver_top
    | r2_hidden(sK1(X0,X1),X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2])).

cnf(c_11654,plain,
    ( r1_tarski(u1_struct_0(sK6),sK7) = iProver_top
    | r2_hidden(k3_yellow_0(sK6),sK7) != iProver_top ),
    inference(superposition,[status(thm)],[c_11648,c_1310])).

cnf(c_12242,plain,
    ( u1_struct_0(sK6) = sK7
    | r1_tarski(u1_struct_0(sK6),sK7) = iProver_top ),
    inference(superposition,[status(thm)],[c_3091,c_11654])).

cnf(c_12254,plain,
    ( r1_tarski(u1_struct_0(sK6),sK7)
    | u1_struct_0(sK6) = sK7 ),
    inference(predicate_to_equality_rev,[status(thm)],[c_12242])).

cnf(c_13,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | ~ m1_subset_1(X2,k1_zfmisc_1(X1))
    | ~ r2_hidden(sK3(X1,X2,X0),X0)
    | ~ r2_hidden(sK3(X1,X2,X0),X2)
    | X2 = X0 ),
    inference(cnf_transformation,[],[f73])).

cnf(c_2974,plain,
    ( m1_subset_1(X0,u1_struct_0(sK6))
    | ~ r2_hidden(X0,sK7) ),
    inference(resolution,[status(thm)],[c_16,c_29])).

cnf(c_12,plain,
    ( ~ m1_subset_1(X0,X1)
    | r2_hidden(X0,X1)
    | v1_xboole_0(X1) ),
    inference(cnf_transformation,[],[f67])).

cnf(c_3038,plain,
    ( r2_hidden(X0,u1_struct_0(sK6))
    | ~ r2_hidden(X0,sK7)
    | v1_xboole_0(u1_struct_0(sK6)) ),
    inference(resolution,[status(thm)],[c_2974,c_12])).

cnf(c_8079,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | ~ m1_subset_1(u1_struct_0(sK6),k1_zfmisc_1(X1))
    | ~ r2_hidden(sK3(X1,u1_struct_0(sK6),X0),X0)
    | ~ r2_hidden(sK3(X1,u1_struct_0(sK6),X0),sK7)
    | v1_xboole_0(u1_struct_0(sK6))
    | u1_struct_0(sK6) = X0 ),
    inference(resolution,[status(thm)],[c_13,c_3038])).

cnf(c_31,negated_conjecture,
    ( ~ v1_xboole_0(sK7) ),
    inference(cnf_transformation,[],[f89])).

cnf(c_1301,plain,
    ( m1_subset_1(X0,X1) != iProver_top
    | r2_hidden(X0,X1) = iProver_top
    | v1_xboole_0(X1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_12])).

cnf(c_2905,plain,
    ( r2_hidden(sK7,k1_zfmisc_1(u1_struct_0(sK6))) = iProver_top
    | v1_xboole_0(k1_zfmisc_1(u1_struct_0(sK6))) = iProver_top ),
    inference(superposition,[status(thm)],[c_1284,c_1301])).

cnf(c_40,plain,
    ( v1_xboole_0(sK7) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_31])).

cnf(c_42,plain,
    ( m1_subset_1(sK7,k1_zfmisc_1(u1_struct_0(sK6))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_29])).

cnf(c_10,plain,
    ( ~ m1_subset_1(X0,X1)
    | ~ v1_xboole_0(X1)
    | v1_xboole_0(X0) ),
    inference(cnf_transformation,[],[f69])).

cnf(c_1634,plain,
    ( ~ m1_subset_1(sK7,X0)
    | ~ v1_xboole_0(X0)
    | v1_xboole_0(sK7) ),
    inference(instantiation,[status(thm)],[c_10])).

cnf(c_1874,plain,
    ( ~ m1_subset_1(sK7,k1_zfmisc_1(u1_struct_0(sK6)))
    | ~ v1_xboole_0(k1_zfmisc_1(u1_struct_0(sK6)))
    | v1_xboole_0(sK7) ),
    inference(instantiation,[status(thm)],[c_1634])).

cnf(c_1875,plain,
    ( m1_subset_1(sK7,k1_zfmisc_1(u1_struct_0(sK6))) != iProver_top
    | v1_xboole_0(k1_zfmisc_1(u1_struct_0(sK6))) != iProver_top
    | v1_xboole_0(sK7) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1874])).

cnf(c_2143,plain,
    ( r2_hidden(sK7,k1_zfmisc_1(u1_struct_0(sK6)))
    | v1_xboole_0(k1_zfmisc_1(u1_struct_0(sK6))) ),
    inference(resolution,[status(thm)],[c_12,c_29])).

cnf(c_2144,plain,
    ( r2_hidden(sK7,k1_zfmisc_1(u1_struct_0(sK6))) = iProver_top
    | v1_xboole_0(k1_zfmisc_1(u1_struct_0(sK6))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2143])).

cnf(c_3168,plain,
    ( r2_hidden(sK7,k1_zfmisc_1(u1_struct_0(sK6))) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_2905,c_40,c_42,c_1875,c_2144])).

cnf(c_8,plain,
    ( r1_tarski(X0,X1)
    | ~ r2_hidden(X0,k1_zfmisc_1(X1)) ),
    inference(cnf_transformation,[],[f95])).

cnf(c_1304,plain,
    ( r1_tarski(X0,X1) = iProver_top
    | r2_hidden(X0,k1_zfmisc_1(X1)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_8])).

cnf(c_3175,plain,
    ( r1_tarski(sK7,u1_struct_0(sK6)) = iProver_top ),
    inference(superposition,[status(thm)],[c_3168,c_1304])).

cnf(c_4,plain,
    ( ~ r1_tarski(X0,X1)
    | ~ r2_hidden(X2,X0)
    | r2_hidden(X2,X1) ),
    inference(cnf_transformation,[],[f60])).

cnf(c_1308,plain,
    ( r1_tarski(X0,X1) != iProver_top
    | r2_hidden(X2,X0) != iProver_top
    | r2_hidden(X2,X1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_4])).

cnf(c_3496,plain,
    ( r2_hidden(X0,u1_struct_0(sK6)) = iProver_top
    | r2_hidden(X0,sK7) != iProver_top ),
    inference(superposition,[status(thm)],[c_3175,c_1308])).

cnf(c_1311,plain,
    ( r2_hidden(X0,X1) != iProver_top
    | v1_xboole_0(X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1])).

cnf(c_3937,plain,
    ( r2_hidden(X0,sK7) != iProver_top
    | v1_xboole_0(u1_struct_0(sK6)) != iProver_top ),
    inference(superposition,[status(thm)],[c_3496,c_1311])).

cnf(c_4298,plain,
    ( v1_xboole_0(u1_struct_0(sK6)) != iProver_top
    | v1_xboole_0(sK7) = iProver_top ),
    inference(superposition,[status(thm)],[c_1312,c_3937])).

cnf(c_4320,plain,
    ( ~ v1_xboole_0(u1_struct_0(sK6))
    | v1_xboole_0(sK7) ),
    inference(predicate_to_equality_rev,[status(thm)],[c_4298])).

cnf(c_8088,plain,
    ( ~ r2_hidden(sK3(X1,u1_struct_0(sK6),X0),sK7)
    | ~ r2_hidden(sK3(X1,u1_struct_0(sK6),X0),X0)
    | ~ m1_subset_1(u1_struct_0(sK6),k1_zfmisc_1(X1))
    | ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | u1_struct_0(sK6) = X0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_8079,c_31,c_4320])).

cnf(c_8089,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | ~ m1_subset_1(u1_struct_0(sK6),k1_zfmisc_1(X1))
    | ~ r2_hidden(sK3(X1,u1_struct_0(sK6),X0),X0)
    | ~ r2_hidden(sK3(X1,u1_struct_0(sK6),X0),sK7)
    | u1_struct_0(sK6) = X0 ),
    inference(renaming,[status(thm)],[c_8088])).

cnf(c_14,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | ~ m1_subset_1(X2,k1_zfmisc_1(X1))
    | r2_hidden(sK3(X1,X2,X0),X0)
    | r2_hidden(sK3(X1,X2,X0),X2)
    | X2 = X0 ),
    inference(cnf_transformation,[],[f72])).

cnf(c_8364,plain,
    ( ~ m1_subset_1(u1_struct_0(sK6),k1_zfmisc_1(X0))
    | ~ m1_subset_1(sK7,k1_zfmisc_1(X0))
    | r2_hidden(sK3(X0,u1_struct_0(sK6),sK7),u1_struct_0(sK6))
    | ~ r2_hidden(sK3(X0,u1_struct_0(sK6),sK7),sK7)
    | u1_struct_0(sK6) = sK7 ),
    inference(resolution,[status(thm)],[c_8089,c_14])).

cnf(c_8374,plain,
    ( ~ m1_subset_1(u1_struct_0(sK6),k1_zfmisc_1(X0))
    | ~ m1_subset_1(sK7,k1_zfmisc_1(X0))
    | ~ r2_hidden(sK3(X0,u1_struct_0(sK6),sK7),sK7)
    | u1_struct_0(sK6) = sK7 ),
    inference(forward_subsumption_resolution,[status(thm)],[c_8364,c_13])).

cnf(c_8393,plain,
    ( ~ m1_subset_1(u1_struct_0(sK6),k1_zfmisc_1(X0))
    | ~ m1_subset_1(sK7,k1_zfmisc_1(X0))
    | r2_hidden(sK3(X0,u1_struct_0(sK6),sK7),u1_struct_0(sK6))
    | u1_struct_0(sK6) = sK7 ),
    inference(resolution,[status(thm)],[c_8374,c_14])).

cnf(c_8634,plain,
    ( ~ m1_subset_1(u1_struct_0(sK6),k1_zfmisc_1(X0))
    | ~ m1_subset_1(sK7,k1_zfmisc_1(X0))
    | ~ r1_tarski(u1_struct_0(sK6),X1)
    | r2_hidden(sK3(X0,u1_struct_0(sK6),sK7),X1)
    | u1_struct_0(sK6) = sK7 ),
    inference(resolution,[status(thm)],[c_8393,c_4])).

cnf(c_8854,plain,
    ( ~ m1_subset_1(u1_struct_0(sK6),k1_zfmisc_1(X0))
    | ~ m1_subset_1(sK7,k1_zfmisc_1(X0))
    | ~ r1_tarski(u1_struct_0(sK6),sK7)
    | u1_struct_0(sK6) = sK7 ),
    inference(resolution,[status(thm)],[c_8634,c_8374])).

cnf(c_11279,plain,
    ( ~ m1_subset_1(sK7,k1_zfmisc_1(X0))
    | ~ r1_tarski(u1_struct_0(sK6),sK7)
    | ~ r2_hidden(u1_struct_0(sK6),k1_zfmisc_1(X0))
    | u1_struct_0(sK6) = sK7 ),
    inference(resolution,[status(thm)],[c_8854,c_355])).

cnf(c_14263,plain,
    ( ~ m1_subset_1(sK7,k1_zfmisc_1(X0))
    | ~ r2_hidden(u1_struct_0(sK6),k1_zfmisc_1(X0))
    | u1_struct_0(sK6) = sK7 ),
    inference(global_propositional_subsumption,[status(thm)],[c_11279,c_12254])).

cnf(c_2701,plain,
    ( ~ r1_tarski(X0,X1)
    | ~ r1_tarski(k1_zfmisc_1(X1),X2)
    | r2_hidden(X0,X2) ),
    inference(resolution,[status(thm)],[c_4,c_7])).

cnf(c_2699,plain,
    ( ~ r1_tarski(X0,X1)
    | r1_tarski(X0,X2)
    | r2_hidden(sK1(X0,X2),X1) ),
    inference(resolution,[status(thm)],[c_4,c_3])).

cnf(c_3050,plain,
    ( r1_tarski(X0,u1_struct_0(sK6))
    | ~ r2_hidden(sK1(X0,u1_struct_0(sK6)),sK7)
    | v1_xboole_0(u1_struct_0(sK6)) ),
    inference(resolution,[status(thm)],[c_3038,c_2])).

cnf(c_3251,plain,
    ( r1_tarski(X0,u1_struct_0(sK6))
    | ~ r1_tarski(X0,sK7)
    | v1_xboole_0(u1_struct_0(sK6)) ),
    inference(resolution,[status(thm)],[c_2699,c_3050])).

cnf(c_2125,plain,
    ( r1_tarski(X0,k1_zfmisc_1(X1))
    | ~ r1_tarski(sK1(X0,k1_zfmisc_1(X1)),X1) ),
    inference(resolution,[status(thm)],[c_7,c_2])).

cnf(c_3263,plain,
    ( r1_tarski(X0,k1_zfmisc_1(u1_struct_0(sK6)))
    | ~ r1_tarski(sK1(X0,k1_zfmisc_1(u1_struct_0(sK6))),sK7)
    | v1_xboole_0(u1_struct_0(sK6)) ),
    inference(resolution,[status(thm)],[c_3251,c_2125])).

cnf(c_1762,plain,
    ( r1_tarski(sK1(k1_zfmisc_1(X0),X1),X0)
    | r1_tarski(k1_zfmisc_1(X0),X1) ),
    inference(resolution,[status(thm)],[c_8,c_3])).

cnf(c_3535,plain,
    ( r1_tarski(k1_zfmisc_1(sK7),k1_zfmisc_1(u1_struct_0(sK6)))
    | v1_xboole_0(u1_struct_0(sK6)) ),
    inference(resolution,[status(thm)],[c_3263,c_1762])).

cnf(c_4340,plain,
    ( ~ r1_tarski(X0,sK7)
    | r2_hidden(X0,k1_zfmisc_1(u1_struct_0(sK6)))
    | v1_xboole_0(u1_struct_0(sK6)) ),
    inference(resolution,[status(thm)],[c_2701,c_3535])).

cnf(c_4587,plain,
    ( r2_hidden(X0,k1_zfmisc_1(u1_struct_0(sK6)))
    | ~ r1_tarski(X0,sK7) ),
    inference(global_propositional_subsumption,[status(thm)],[c_4340,c_31,c_4320])).

cnf(c_4588,plain,
    ( ~ r1_tarski(X0,sK7)
    | r2_hidden(X0,k1_zfmisc_1(u1_struct_0(sK6))) ),
    inference(renaming,[status(thm)],[c_4587])).

cnf(c_14609,plain,
    ( ~ m1_subset_1(sK7,k1_zfmisc_1(u1_struct_0(sK6)))
    | ~ r1_tarski(u1_struct_0(sK6),sK7)
    | u1_struct_0(sK6) = sK7 ),
    inference(resolution,[status(thm)],[c_14263,c_4588])).

cnf(c_14841,plain,
    ( u1_struct_0(sK6) = sK7 ),
    inference(global_propositional_subsumption,[status(thm)],[c_11917,c_29,c_12254,c_14609])).

cnf(c_17,plain,
    ( m1_subset_1(k3_yellow_0(X0),u1_struct_0(X0))
    | ~ l1_orders_2(X0) ),
    inference(cnf_transformation,[],[f75])).

cnf(c_1296,plain,
    ( m1_subset_1(k3_yellow_0(X0),u1_struct_0(X0)) = iProver_top
    | l1_orders_2(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_17])).

cnf(c_2904,plain,
    ( r2_hidden(k3_yellow_0(X0),u1_struct_0(X0)) = iProver_top
    | l1_orders_2(X0) != iProver_top
    | v1_xboole_0(u1_struct_0(X0)) = iProver_top ),
    inference(superposition,[status(thm)],[c_1296,c_1301])).

cnf(c_15065,plain,
    ( r2_hidden(k3_yellow_0(sK6),sK7) = iProver_top
    | l1_orders_2(sK6) != iProver_top
    | v1_xboole_0(u1_struct_0(sK6)) = iProver_top ),
    inference(superposition,[status(thm)],[c_14841,c_2904])).

cnf(c_15136,plain,
    ( r2_hidden(k3_yellow_0(sK6),sK7) = iProver_top
    | l1_orders_2(sK6) != iProver_top
    | v1_xboole_0(sK7) = iProver_top ),
    inference(light_normalisation,[status(thm)],[c_15065,c_14841])).

cnf(c_14871,plain,
    ( r2_hidden(sK7,k1_zfmisc_1(sK7)) = iProver_top ),
    inference(demodulation,[status(thm)],[c_14841,c_3168])).

cnf(c_26,plain,
    ( ~ v1_subset_1(X0,X0)
    | ~ m1_subset_1(X0,k1_zfmisc_1(X0)) ),
    inference(cnf_transformation,[],[f96])).

cnf(c_11745,plain,
    ( ~ v1_subset_1(sK7,sK7)
    | ~ m1_subset_1(sK7,k1_zfmisc_1(sK7)) ),
    inference(instantiation,[status(thm)],[c_26])).

cnf(c_11748,plain,
    ( v1_subset_1(sK7,sK7) != iProver_top
    | m1_subset_1(sK7,k1_zfmisc_1(sK7)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_11745])).

cnf(c_431,plain,
    ( ~ v1_subset_1(X0,X1)
    | v1_subset_1(X2,X3)
    | X2 != X0
    | X3 != X1 ),
    theory(equality)).

cnf(c_2981,plain,
    ( v1_subset_1(X0,X1)
    | ~ v1_subset_1(sK7,u1_struct_0(sK6))
    | X1 != u1_struct_0(sK6)
    | X0 != sK7 ),
    inference(instantiation,[status(thm)],[c_431])).

cnf(c_5276,plain,
    ( v1_subset_1(X0,sK7)
    | ~ v1_subset_1(sK7,u1_struct_0(sK6))
    | X0 != sK7
    | sK7 != u1_struct_0(sK6) ),
    inference(instantiation,[status(thm)],[c_2981])).

cnf(c_11744,plain,
    ( ~ v1_subset_1(sK7,u1_struct_0(sK6))
    | v1_subset_1(sK7,sK7)
    | sK7 != u1_struct_0(sK6)
    | sK7 != sK7 ),
    inference(instantiation,[status(thm)],[c_5276])).

cnf(c_11746,plain,
    ( sK7 != u1_struct_0(sK6)
    | sK7 != sK7
    | v1_subset_1(sK7,u1_struct_0(sK6)) != iProver_top
    | v1_subset_1(sK7,sK7) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_11744])).

cnf(c_417,plain,
    ( X0 != X1
    | X2 != X1
    | X2 = X0 ),
    theory(equality)).

cnf(c_1882,plain,
    ( X0 != X1
    | sK7 != X1
    | sK7 = X0 ),
    inference(instantiation,[status(thm)],[c_417])).

cnf(c_2219,plain,
    ( X0 != sK7
    | sK7 = X0
    | sK7 != sK7 ),
    inference(instantiation,[status(thm)],[c_1882])).

cnf(c_5277,plain,
    ( u1_struct_0(sK6) != sK7
    | sK7 = u1_struct_0(sK6)
    | sK7 != sK7 ),
    inference(instantiation,[status(thm)],[c_2219])).

cnf(c_2162,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(sK7))
    | ~ r2_hidden(X0,k1_zfmisc_1(sK7)) ),
    inference(instantiation,[status(thm)],[c_355])).

cnf(c_3317,plain,
    ( m1_subset_1(sK7,k1_zfmisc_1(sK7))
    | ~ r2_hidden(sK7,k1_zfmisc_1(sK7)) ),
    inference(instantiation,[status(thm)],[c_2162])).

cnf(c_3319,plain,
    ( m1_subset_1(sK7,k1_zfmisc_1(sK7)) = iProver_top
    | r2_hidden(sK7,k1_zfmisc_1(sK7)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3317])).

cnf(c_416,plain,
    ( X0 = X0 ),
    theory(equality)).

cnf(c_1958,plain,
    ( sK7 = sK7 ),
    inference(instantiation,[status(thm)],[c_416])).

cnf(c_28,negated_conjecture,
    ( v1_subset_1(sK7,u1_struct_0(sK6))
    | ~ r2_hidden(k3_yellow_0(sK6),sK7) ),
    inference(cnf_transformation,[],[f92])).

cnf(c_43,plain,
    ( v1_subset_1(sK7,u1_struct_0(sK6)) = iProver_top
    | r2_hidden(k3_yellow_0(sK6),sK7) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_28])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_15136,c_14871,c_14841,c_11748,c_11746,c_5277,c_3319,c_1958,c_43,c_40,c_39])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.12  % Command    : iproveropt_run.sh %d %s
% 0.13/0.33  % Computer   : n011.cluster.edu
% 0.13/0.33  % Model      : x86_64 x86_64
% 0.13/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.33  % Memory     : 8042.1875MB
% 0.13/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.33  % CPULimit   : 60
% 0.13/0.33  % WCLimit    : 600
% 0.13/0.33  % DateTime   : Tue Dec  1 16:37:42 EST 2020
% 0.13/0.33  % CPUTime    : 
% 0.13/0.33  % Running in FOF mode
% 4.04/0.93  % SZS status Started for /export/starexec/sandbox/benchmark/theBenchmark.p
% 4.04/0.93  
% 4.04/0.93  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 4.04/0.93  
% 4.04/0.93  ------  iProver source info
% 4.04/0.93  
% 4.04/0.93  git: date: 2020-06-30 10:37:57 +0100
% 4.04/0.93  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 4.04/0.93  git: non_committed_changes: false
% 4.04/0.93  git: last_make_outside_of_git: false
% 4.04/0.93  
% 4.04/0.93  ------ 
% 4.04/0.93  ------ Parsing...
% 4.04/0.93  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 4.04/0.93  
% 4.04/0.93  ------ Preprocessing... sf_s  rm: 1 0s  sf_e 
% 4.04/0.93  
% 4.04/0.93  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 4.04/0.93  
% 4.04/0.93  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 4.04/0.93  ------ Proving...
% 4.04/0.93  ------ Problem Properties 
% 4.04/0.93  
% 4.04/0.93  
% 4.04/0.93  clauses                                 36
% 4.04/0.93  conjectures                             9
% 4.04/0.93  EPR                                     12
% 4.04/0.93  Horn                                    24
% 4.04/0.93  unary                                   7
% 4.04/0.93  binary                                  11
% 4.04/0.93  lits                                    101
% 4.04/0.93  lits eq                                 6
% 4.04/0.93  fd_pure                                 0
% 4.04/0.93  fd_pseudo                               0
% 4.04/0.93  fd_cond                                 0
% 4.04/0.93  fd_pseudo_cond                          6
% 4.04/0.93  AC symbols                              0
% 4.04/0.93  
% 4.04/0.93  ------ Input Options Time Limit: Unbounded
% 4.04/0.93  
% 4.04/0.93  
% 4.04/0.93  ------ 
% 4.04/0.93  Current options:
% 4.04/0.93  ------ 
% 4.04/0.93  
% 4.04/0.93  
% 4.04/0.93  
% 4.04/0.93  
% 4.04/0.93  ------ Proving...
% 4.04/0.93  
% 4.04/0.93  
% 4.04/0.93  % SZS status Theorem for theBenchmark.p
% 4.04/0.93  
% 4.04/0.93  % SZS output start CNFRefutation for theBenchmark.p
% 4.04/0.93  
% 4.04/0.93  fof(f3,axiom,(
% 4.04/0.93    ! [X0,X1] : (k1_zfmisc_1(X0) = X1 <=> ! [X2] : (r2_hidden(X2,X1) <=> r1_tarski(X2,X0)))),
% 4.04/0.93    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 4.04/0.93  
% 4.04/0.93  fof(f38,plain,(
% 4.04/0.93    ! [X0,X1] : ((k1_zfmisc_1(X0) = X1 | ? [X2] : ((~r1_tarski(X2,X0) | ~r2_hidden(X2,X1)) & (r1_tarski(X2,X0) | r2_hidden(X2,X1)))) & (! [X2] : ((r2_hidden(X2,X1) | ~r1_tarski(X2,X0)) & (r1_tarski(X2,X0) | ~r2_hidden(X2,X1))) | k1_zfmisc_1(X0) != X1))),
% 4.04/0.93    inference(nnf_transformation,[],[f3])).
% 4.04/0.93  
% 4.04/0.93  fof(f39,plain,(
% 4.04/0.93    ! [X0,X1] : ((k1_zfmisc_1(X0) = X1 | ? [X2] : ((~r1_tarski(X2,X0) | ~r2_hidden(X2,X1)) & (r1_tarski(X2,X0) | r2_hidden(X2,X1)))) & (! [X3] : ((r2_hidden(X3,X1) | ~r1_tarski(X3,X0)) & (r1_tarski(X3,X0) | ~r2_hidden(X3,X1))) | k1_zfmisc_1(X0) != X1))),
% 4.04/0.93    inference(rectify,[],[f38])).
% 4.04/0.93  
% 4.04/0.93  fof(f40,plain,(
% 4.04/0.93    ! [X1,X0] : (? [X2] : ((~r1_tarski(X2,X0) | ~r2_hidden(X2,X1)) & (r1_tarski(X2,X0) | r2_hidden(X2,X1))) => ((~r1_tarski(sK2(X0,X1),X0) | ~r2_hidden(sK2(X0,X1),X1)) & (r1_tarski(sK2(X0,X1),X0) | r2_hidden(sK2(X0,X1),X1))))),
% 4.04/0.93    introduced(choice_axiom,[])).
% 4.04/0.93  
% 4.04/0.93  fof(f41,plain,(
% 4.04/0.93    ! [X0,X1] : ((k1_zfmisc_1(X0) = X1 | ((~r1_tarski(sK2(X0,X1),X0) | ~r2_hidden(sK2(X0,X1),X1)) & (r1_tarski(sK2(X0,X1),X0) | r2_hidden(sK2(X0,X1),X1)))) & (! [X3] : ((r2_hidden(X3,X1) | ~r1_tarski(X3,X0)) & (r1_tarski(X3,X0) | ~r2_hidden(X3,X1))) | k1_zfmisc_1(X0) != X1))),
% 4.04/0.93    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2])],[f39,f40])).
% 4.04/0.93  
% 4.04/0.93  fof(f65,plain,(
% 4.04/0.93    ( ! [X0,X1] : (k1_zfmisc_1(X0) = X1 | r1_tarski(sK2(X0,X1),X0) | r2_hidden(sK2(X0,X1),X1)) )),
% 4.04/0.93    inference(cnf_transformation,[],[f41])).
% 4.04/0.93  
% 4.04/0.93  fof(f11,conjecture,(
% 4.04/0.93    ! [X0] : ((l1_orders_2(X0) & v1_yellow_0(X0) & v5_orders_2(X0) & v4_orders_2(X0) & v3_orders_2(X0) & ~v2_struct_0(X0)) => ! [X1] : ((m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & v13_waybel_0(X1,X0) & v2_waybel_0(X1,X0) & ~v1_xboole_0(X1)) => (v1_subset_1(X1,u1_struct_0(X0)) <=> ~r2_hidden(k3_yellow_0(X0),X1))))),
% 4.04/0.93    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 4.04/0.93  
% 4.04/0.93  fof(f12,negated_conjecture,(
% 4.04/0.93    ~! [X0] : ((l1_orders_2(X0) & v1_yellow_0(X0) & v5_orders_2(X0) & v4_orders_2(X0) & v3_orders_2(X0) & ~v2_struct_0(X0)) => ! [X1] : ((m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & v13_waybel_0(X1,X0) & v2_waybel_0(X1,X0) & ~v1_xboole_0(X1)) => (v1_subset_1(X1,u1_struct_0(X0)) <=> ~r2_hidden(k3_yellow_0(X0),X1))))),
% 4.04/0.93    inference(negated_conjecture,[],[f11])).
% 4.04/0.93  
% 4.04/0.93  fof(f13,plain,(
% 4.04/0.93    ~! [X0] : ((l1_orders_2(X0) & v1_yellow_0(X0) & v5_orders_2(X0) & v4_orders_2(X0) & v3_orders_2(X0) & ~v2_struct_0(X0)) => ! [X1] : ((m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & v13_waybel_0(X1,X0) & ~v1_xboole_0(X1)) => (v1_subset_1(X1,u1_struct_0(X0)) <=> ~r2_hidden(k3_yellow_0(X0),X1))))),
% 4.04/0.93    inference(pure_predicate_removal,[],[f12])).
% 4.04/0.93  
% 4.04/0.93  fof(f14,plain,(
% 4.04/0.93    ~! [X0] : ((l1_orders_2(X0) & v1_yellow_0(X0) & v5_orders_2(X0) & v3_orders_2(X0) & ~v2_struct_0(X0)) => ! [X1] : ((m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & v13_waybel_0(X1,X0) & ~v1_xboole_0(X1)) => (v1_subset_1(X1,u1_struct_0(X0)) <=> ~r2_hidden(k3_yellow_0(X0),X1))))),
% 4.04/0.93    inference(pure_predicate_removal,[],[f13])).
% 4.04/0.93  
% 4.04/0.93  fof(f15,plain,(
% 4.04/0.93    ~! [X0] : ((l1_orders_2(X0) & v1_yellow_0(X0) & v5_orders_2(X0) & ~v2_struct_0(X0)) => ! [X1] : ((m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & v13_waybel_0(X1,X0) & ~v1_xboole_0(X1)) => (v1_subset_1(X1,u1_struct_0(X0)) <=> ~r2_hidden(k3_yellow_0(X0),X1))))),
% 4.04/0.93    inference(pure_predicate_removal,[],[f14])).
% 4.04/0.93  
% 4.04/0.93  fof(f28,plain,(
% 4.04/0.93    ? [X0] : (? [X1] : ((v1_subset_1(X1,u1_struct_0(X0)) <~> ~r2_hidden(k3_yellow_0(X0),X1)) & (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & v13_waybel_0(X1,X0) & ~v1_xboole_0(X1))) & (l1_orders_2(X0) & v1_yellow_0(X0) & v5_orders_2(X0) & ~v2_struct_0(X0)))),
% 4.04/0.93    inference(ennf_transformation,[],[f15])).
% 4.04/0.93  
% 4.04/0.93  fof(f29,plain,(
% 4.04/0.93    ? [X0] : (? [X1] : ((v1_subset_1(X1,u1_struct_0(X0)) <~> ~r2_hidden(k3_yellow_0(X0),X1)) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & v13_waybel_0(X1,X0) & ~v1_xboole_0(X1)) & l1_orders_2(X0) & v1_yellow_0(X0) & v5_orders_2(X0) & ~v2_struct_0(X0))),
% 4.04/0.93    inference(flattening,[],[f28])).
% 4.04/0.93  
% 4.04/0.93  fof(f53,plain,(
% 4.04/0.93    ? [X0] : (? [X1] : (((r2_hidden(k3_yellow_0(X0),X1) | ~v1_subset_1(X1,u1_struct_0(X0))) & (~r2_hidden(k3_yellow_0(X0),X1) | v1_subset_1(X1,u1_struct_0(X0)))) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & v13_waybel_0(X1,X0) & ~v1_xboole_0(X1)) & l1_orders_2(X0) & v1_yellow_0(X0) & v5_orders_2(X0) & ~v2_struct_0(X0))),
% 4.04/0.93    inference(nnf_transformation,[],[f29])).
% 4.04/0.93  
% 4.04/0.93  fof(f54,plain,(
% 4.04/0.93    ? [X0] : (? [X1] : ((r2_hidden(k3_yellow_0(X0),X1) | ~v1_subset_1(X1,u1_struct_0(X0))) & (~r2_hidden(k3_yellow_0(X0),X1) | v1_subset_1(X1,u1_struct_0(X0))) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & v13_waybel_0(X1,X0) & ~v1_xboole_0(X1)) & l1_orders_2(X0) & v1_yellow_0(X0) & v5_orders_2(X0) & ~v2_struct_0(X0))),
% 4.04/0.93    inference(flattening,[],[f53])).
% 4.04/0.93  
% 4.04/0.93  fof(f56,plain,(
% 4.04/0.93    ( ! [X0] : (? [X1] : ((r2_hidden(k3_yellow_0(X0),X1) | ~v1_subset_1(X1,u1_struct_0(X0))) & (~r2_hidden(k3_yellow_0(X0),X1) | v1_subset_1(X1,u1_struct_0(X0))) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & v13_waybel_0(X1,X0) & ~v1_xboole_0(X1)) => ((r2_hidden(k3_yellow_0(X0),sK7) | ~v1_subset_1(sK7,u1_struct_0(X0))) & (~r2_hidden(k3_yellow_0(X0),sK7) | v1_subset_1(sK7,u1_struct_0(X0))) & m1_subset_1(sK7,k1_zfmisc_1(u1_struct_0(X0))) & v13_waybel_0(sK7,X0) & ~v1_xboole_0(sK7))) )),
% 4.04/0.93    introduced(choice_axiom,[])).
% 4.04/0.93  
% 4.04/0.93  fof(f55,plain,(
% 4.04/0.93    ? [X0] : (? [X1] : ((r2_hidden(k3_yellow_0(X0),X1) | ~v1_subset_1(X1,u1_struct_0(X0))) & (~r2_hidden(k3_yellow_0(X0),X1) | v1_subset_1(X1,u1_struct_0(X0))) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & v13_waybel_0(X1,X0) & ~v1_xboole_0(X1)) & l1_orders_2(X0) & v1_yellow_0(X0) & v5_orders_2(X0) & ~v2_struct_0(X0)) => (? [X1] : ((r2_hidden(k3_yellow_0(sK6),X1) | ~v1_subset_1(X1,u1_struct_0(sK6))) & (~r2_hidden(k3_yellow_0(sK6),X1) | v1_subset_1(X1,u1_struct_0(sK6))) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK6))) & v13_waybel_0(X1,sK6) & ~v1_xboole_0(X1)) & l1_orders_2(sK6) & v1_yellow_0(sK6) & v5_orders_2(sK6) & ~v2_struct_0(sK6))),
% 4.04/0.93    introduced(choice_axiom,[])).
% 4.04/0.93  
% 4.04/0.93  fof(f57,plain,(
% 4.04/0.93    ((r2_hidden(k3_yellow_0(sK6),sK7) | ~v1_subset_1(sK7,u1_struct_0(sK6))) & (~r2_hidden(k3_yellow_0(sK6),sK7) | v1_subset_1(sK7,u1_struct_0(sK6))) & m1_subset_1(sK7,k1_zfmisc_1(u1_struct_0(sK6))) & v13_waybel_0(sK7,sK6) & ~v1_xboole_0(sK7)) & l1_orders_2(sK6) & v1_yellow_0(sK6) & v5_orders_2(sK6) & ~v2_struct_0(sK6)),
% 4.04/0.93    inference(skolemisation,[status(esa),new_symbols(skolem,[sK6,sK7])],[f54,f56,f55])).
% 4.04/0.93  
% 4.04/0.93  fof(f91,plain,(
% 4.04/0.93    m1_subset_1(sK7,k1_zfmisc_1(u1_struct_0(sK6)))),
% 4.04/0.93    inference(cnf_transformation,[],[f57])).
% 4.04/0.93  
% 4.04/0.93  fof(f10,axiom,(
% 4.04/0.93    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => (v1_subset_1(X1,X0) <=> X0 != X1))),
% 4.04/0.93    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 4.04/0.93  
% 4.04/0.93  fof(f27,plain,(
% 4.04/0.93    ! [X0,X1] : ((v1_subset_1(X1,X0) <=> X0 != X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 4.04/0.93    inference(ennf_transformation,[],[f10])).
% 4.04/0.93  
% 4.04/0.93  fof(f52,plain,(
% 4.04/0.93    ! [X0,X1] : (((v1_subset_1(X1,X0) | X0 = X1) & (X0 != X1 | ~v1_subset_1(X1,X0))) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 4.04/0.93    inference(nnf_transformation,[],[f27])).
% 4.04/0.93  
% 4.04/0.93  fof(f84,plain,(
% 4.04/0.93    ( ! [X0,X1] : (v1_subset_1(X1,X0) | X0 = X1 | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 4.04/0.93    inference(cnf_transformation,[],[f52])).
% 4.04/0.93  
% 4.04/0.93  fof(f93,plain,(
% 4.04/0.93    r2_hidden(k3_yellow_0(sK6),sK7) | ~v1_subset_1(sK7,u1_struct_0(sK6))),
% 4.04/0.93    inference(cnf_transformation,[],[f57])).
% 4.04/0.93  
% 4.04/0.93  fof(f8,axiom,(
% 4.04/0.93    ! [X0] : ((l1_orders_2(X0) & v1_yellow_0(X0) & v5_orders_2(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,u1_struct_0(X0)) => r1_orders_2(X0,k3_yellow_0(X0),X1)))),
% 4.04/0.93    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 4.04/0.93  
% 4.04/0.93  fof(f23,plain,(
% 4.04/0.93    ! [X0] : (! [X1] : (r1_orders_2(X0,k3_yellow_0(X0),X1) | ~m1_subset_1(X1,u1_struct_0(X0))) | (~l1_orders_2(X0) | ~v1_yellow_0(X0) | ~v5_orders_2(X0) | v2_struct_0(X0)))),
% 4.04/0.93    inference(ennf_transformation,[],[f8])).
% 4.04/0.93  
% 4.04/0.93  fof(f24,plain,(
% 4.04/0.93    ! [X0] : (! [X1] : (r1_orders_2(X0,k3_yellow_0(X0),X1) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~l1_orders_2(X0) | ~v1_yellow_0(X0) | ~v5_orders_2(X0) | v2_struct_0(X0))),
% 4.04/0.93    inference(flattening,[],[f23])).
% 4.04/0.93  
% 4.04/0.93  fof(f76,plain,(
% 4.04/0.93    ( ! [X0,X1] : (r1_orders_2(X0,k3_yellow_0(X0),X1) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_orders_2(X0) | ~v1_yellow_0(X0) | ~v5_orders_2(X0) | v2_struct_0(X0)) )),
% 4.04/0.93    inference(cnf_transformation,[],[f24])).
% 4.04/0.93  
% 4.04/0.93  fof(f1,axiom,(
% 4.04/0.93    ! [X0] : (v1_xboole_0(X0) <=> ! [X1] : ~r2_hidden(X1,X0))),
% 4.04/0.93    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 4.04/0.93  
% 4.04/0.93  fof(f30,plain,(
% 4.04/0.93    ! [X0] : ((v1_xboole_0(X0) | ? [X1] : r2_hidden(X1,X0)) & (! [X1] : ~r2_hidden(X1,X0) | ~v1_xboole_0(X0)))),
% 4.04/0.93    inference(nnf_transformation,[],[f1])).
% 4.04/0.93  
% 4.04/0.93  fof(f31,plain,(
% 4.04/0.93    ! [X0] : ((v1_xboole_0(X0) | ? [X1] : r2_hidden(X1,X0)) & (! [X2] : ~r2_hidden(X2,X0) | ~v1_xboole_0(X0)))),
% 4.04/0.93    inference(rectify,[],[f30])).
% 4.04/0.93  
% 4.04/0.93  fof(f32,plain,(
% 4.04/0.93    ! [X0] : (? [X1] : r2_hidden(X1,X0) => r2_hidden(sK0(X0),X0))),
% 4.04/0.93    introduced(choice_axiom,[])).
% 4.04/0.93  
% 4.04/0.93  fof(f33,plain,(
% 4.04/0.93    ! [X0] : ((v1_xboole_0(X0) | r2_hidden(sK0(X0),X0)) & (! [X2] : ~r2_hidden(X2,X0) | ~v1_xboole_0(X0)))),
% 4.04/0.93    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f31,f32])).
% 4.04/0.93  
% 4.04/0.93  fof(f59,plain,(
% 4.04/0.93    ( ! [X0] : (v1_xboole_0(X0) | r2_hidden(sK0(X0),X0)) )),
% 4.04/0.93    inference(cnf_transformation,[],[f33])).
% 4.04/0.93  
% 4.04/0.93  fof(f64,plain,(
% 4.04/0.93    ( ! [X0,X3,X1] : (r2_hidden(X3,X1) | ~r1_tarski(X3,X0) | k1_zfmisc_1(X0) != X1) )),
% 4.04/0.93    inference(cnf_transformation,[],[f41])).
% 4.04/0.93  
% 4.04/0.93  fof(f94,plain,(
% 4.04/0.93    ( ! [X0,X3] : (r2_hidden(X3,k1_zfmisc_1(X0)) | ~r1_tarski(X3,X0)) )),
% 4.04/0.93    inference(equality_resolution,[],[f64])).
% 4.04/0.93  
% 4.04/0.93  fof(f4,axiom,(
% 4.04/0.93    ! [X0,X1] : ((v1_xboole_0(X0) => (m1_subset_1(X1,X0) <=> v1_xboole_0(X1))) & (~v1_xboole_0(X0) => (m1_subset_1(X1,X0) <=> r2_hidden(X1,X0))))),
% 4.04/0.93    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 4.04/0.93  
% 4.04/0.93  fof(f17,plain,(
% 4.04/0.93    ! [X0,X1] : (((m1_subset_1(X1,X0) <=> v1_xboole_0(X1)) | ~v1_xboole_0(X0)) & ((m1_subset_1(X1,X0) <=> r2_hidden(X1,X0)) | v1_xboole_0(X0)))),
% 4.04/0.93    inference(ennf_transformation,[],[f4])).
% 4.04/0.93  
% 4.04/0.93  fof(f42,plain,(
% 4.04/0.93    ! [X0,X1] : ((((m1_subset_1(X1,X0) | ~v1_xboole_0(X1)) & (v1_xboole_0(X1) | ~m1_subset_1(X1,X0))) | ~v1_xboole_0(X0)) & (((m1_subset_1(X1,X0) | ~r2_hidden(X1,X0)) & (r2_hidden(X1,X0) | ~m1_subset_1(X1,X0))) | v1_xboole_0(X0)))),
% 4.04/0.93    inference(nnf_transformation,[],[f17])).
% 4.04/0.93  
% 4.04/0.93  fof(f68,plain,(
% 4.04/0.93    ( ! [X0,X1] : (m1_subset_1(X1,X0) | ~r2_hidden(X1,X0) | v1_xboole_0(X0)) )),
% 4.04/0.93    inference(cnf_transformation,[],[f42])).
% 4.04/0.93  
% 4.04/0.93  fof(f58,plain,(
% 4.04/0.93    ( ! [X2,X0] : (~r2_hidden(X2,X0) | ~v1_xboole_0(X0)) )),
% 4.04/0.93    inference(cnf_transformation,[],[f33])).
% 4.04/0.93  
% 4.04/0.93  fof(f6,axiom,(
% 4.04/0.93    ! [X0,X1,X2] : ((m1_subset_1(X1,k1_zfmisc_1(X2)) & r2_hidden(X0,X1)) => m1_subset_1(X0,X2))),
% 4.04/0.93    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 4.04/0.93  
% 4.04/0.93  fof(f20,plain,(
% 4.04/0.93    ! [X0,X1,X2] : (m1_subset_1(X0,X2) | (~m1_subset_1(X1,k1_zfmisc_1(X2)) | ~r2_hidden(X0,X1)))),
% 4.04/0.93    inference(ennf_transformation,[],[f6])).
% 4.04/0.93  
% 4.04/0.93  fof(f21,plain,(
% 4.04/0.93    ! [X0,X1,X2] : (m1_subset_1(X0,X2) | ~m1_subset_1(X1,k1_zfmisc_1(X2)) | ~r2_hidden(X0,X1))),
% 4.04/0.93    inference(flattening,[],[f20])).
% 4.04/0.93  
% 4.04/0.93  fof(f74,plain,(
% 4.04/0.93    ( ! [X2,X0,X1] : (m1_subset_1(X0,X2) | ~m1_subset_1(X1,k1_zfmisc_1(X2)) | ~r2_hidden(X0,X1)) )),
% 4.04/0.93    inference(cnf_transformation,[],[f21])).
% 4.04/0.93  
% 4.04/0.93  fof(f9,axiom,(
% 4.04/0.93    ! [X0] : (l1_orders_2(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => (v13_waybel_0(X1,X0) <=> ! [X2] : (m1_subset_1(X2,u1_struct_0(X0)) => ! [X3] : (m1_subset_1(X3,u1_struct_0(X0)) => ((r1_orders_2(X0,X2,X3) & r2_hidden(X2,X1)) => r2_hidden(X3,X1)))))))),
% 4.04/0.93    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 4.04/0.93  
% 4.04/0.93  fof(f25,plain,(
% 4.04/0.93    ! [X0] : (! [X1] : ((v13_waybel_0(X1,X0) <=> ! [X2] : (! [X3] : ((r2_hidden(X3,X1) | (~r1_orders_2(X0,X2,X3) | ~r2_hidden(X2,X1))) | ~m1_subset_1(X3,u1_struct_0(X0))) | ~m1_subset_1(X2,u1_struct_0(X0)))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_orders_2(X0))),
% 4.04/0.93    inference(ennf_transformation,[],[f9])).
% 4.04/0.93  
% 4.04/0.93  fof(f26,plain,(
% 4.04/0.93    ! [X0] : (! [X1] : ((v13_waybel_0(X1,X0) <=> ! [X2] : (! [X3] : (r2_hidden(X3,X1) | ~r1_orders_2(X0,X2,X3) | ~r2_hidden(X2,X1) | ~m1_subset_1(X3,u1_struct_0(X0))) | ~m1_subset_1(X2,u1_struct_0(X0)))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_orders_2(X0))),
% 4.04/0.93    inference(flattening,[],[f25])).
% 4.04/0.93  
% 4.04/0.93  fof(f47,plain,(
% 4.04/0.93    ! [X0] : (! [X1] : (((v13_waybel_0(X1,X0) | ? [X2] : (? [X3] : (~r2_hidden(X3,X1) & r1_orders_2(X0,X2,X3) & r2_hidden(X2,X1) & m1_subset_1(X3,u1_struct_0(X0))) & m1_subset_1(X2,u1_struct_0(X0)))) & (! [X2] : (! [X3] : (r2_hidden(X3,X1) | ~r1_orders_2(X0,X2,X3) | ~r2_hidden(X2,X1) | ~m1_subset_1(X3,u1_struct_0(X0))) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~v13_waybel_0(X1,X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_orders_2(X0))),
% 4.04/0.93    inference(nnf_transformation,[],[f26])).
% 4.04/0.93  
% 4.04/0.93  fof(f48,plain,(
% 4.04/0.93    ! [X0] : (! [X1] : (((v13_waybel_0(X1,X0) | ? [X2] : (? [X3] : (~r2_hidden(X3,X1) & r1_orders_2(X0,X2,X3) & r2_hidden(X2,X1) & m1_subset_1(X3,u1_struct_0(X0))) & m1_subset_1(X2,u1_struct_0(X0)))) & (! [X4] : (! [X5] : (r2_hidden(X5,X1) | ~r1_orders_2(X0,X4,X5) | ~r2_hidden(X4,X1) | ~m1_subset_1(X5,u1_struct_0(X0))) | ~m1_subset_1(X4,u1_struct_0(X0))) | ~v13_waybel_0(X1,X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_orders_2(X0))),
% 4.04/0.93    inference(rectify,[],[f47])).
% 4.04/0.93  
% 4.04/0.93  fof(f50,plain,(
% 4.04/0.93    ( ! [X2] : (! [X1,X0] : (? [X3] : (~r2_hidden(X3,X1) & r1_orders_2(X0,X2,X3) & r2_hidden(X2,X1) & m1_subset_1(X3,u1_struct_0(X0))) => (~r2_hidden(sK5(X0,X1),X1) & r1_orders_2(X0,X2,sK5(X0,X1)) & r2_hidden(X2,X1) & m1_subset_1(sK5(X0,X1),u1_struct_0(X0))))) )),
% 4.04/0.93    introduced(choice_axiom,[])).
% 4.04/0.93  
% 4.04/0.93  fof(f49,plain,(
% 4.04/0.93    ! [X1,X0] : (? [X2] : (? [X3] : (~r2_hidden(X3,X1) & r1_orders_2(X0,X2,X3) & r2_hidden(X2,X1) & m1_subset_1(X3,u1_struct_0(X0))) & m1_subset_1(X2,u1_struct_0(X0))) => (? [X3] : (~r2_hidden(X3,X1) & r1_orders_2(X0,sK4(X0,X1),X3) & r2_hidden(sK4(X0,X1),X1) & m1_subset_1(X3,u1_struct_0(X0))) & m1_subset_1(sK4(X0,X1),u1_struct_0(X0))))),
% 4.04/0.93    introduced(choice_axiom,[])).
% 4.04/0.93  
% 4.04/0.93  fof(f51,plain,(
% 4.04/0.93    ! [X0] : (! [X1] : (((v13_waybel_0(X1,X0) | ((~r2_hidden(sK5(X0,X1),X1) & r1_orders_2(X0,sK4(X0,X1),sK5(X0,X1)) & r2_hidden(sK4(X0,X1),X1) & m1_subset_1(sK5(X0,X1),u1_struct_0(X0))) & m1_subset_1(sK4(X0,X1),u1_struct_0(X0)))) & (! [X4] : (! [X5] : (r2_hidden(X5,X1) | ~r1_orders_2(X0,X4,X5) | ~r2_hidden(X4,X1) | ~m1_subset_1(X5,u1_struct_0(X0))) | ~m1_subset_1(X4,u1_struct_0(X0))) | ~v13_waybel_0(X1,X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_orders_2(X0))),
% 4.04/0.93    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4,sK5])],[f48,f50,f49])).
% 4.04/0.93  
% 4.04/0.93  fof(f77,plain,(
% 4.04/0.93    ( ! [X4,X0,X5,X1] : (r2_hidden(X5,X1) | ~r1_orders_2(X0,X4,X5) | ~r2_hidden(X4,X1) | ~m1_subset_1(X5,u1_struct_0(X0)) | ~m1_subset_1(X4,u1_struct_0(X0)) | ~v13_waybel_0(X1,X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_orders_2(X0)) )),
% 4.04/0.93    inference(cnf_transformation,[],[f51])).
% 4.04/0.93  
% 4.04/0.93  fof(f88,plain,(
% 4.04/0.93    l1_orders_2(sK6)),
% 4.04/0.93    inference(cnf_transformation,[],[f57])).
% 4.04/0.93  
% 4.04/0.93  fof(f90,plain,(
% 4.04/0.93    v13_waybel_0(sK7,sK6)),
% 4.04/0.93    inference(cnf_transformation,[],[f57])).
% 4.04/0.93  
% 4.04/0.93  fof(f85,plain,(
% 4.04/0.93    ~v2_struct_0(sK6)),
% 4.04/0.93    inference(cnf_transformation,[],[f57])).
% 4.04/0.93  
% 4.04/0.93  fof(f86,plain,(
% 4.04/0.93    v5_orders_2(sK6)),
% 4.04/0.93    inference(cnf_transformation,[],[f57])).
% 4.04/0.93  
% 4.04/0.93  fof(f87,plain,(
% 4.04/0.93    v1_yellow_0(sK6)),
% 4.04/0.93    inference(cnf_transformation,[],[f57])).
% 4.04/0.93  
% 4.04/0.93  fof(f2,axiom,(
% 4.04/0.93    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X0) => r2_hidden(X2,X1)))),
% 4.04/0.93    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 4.04/0.93  
% 4.04/0.93  fof(f16,plain,(
% 4.04/0.93    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X1) | ~r2_hidden(X2,X0)))),
% 4.04/0.93    inference(ennf_transformation,[],[f2])).
% 4.04/0.93  
% 4.04/0.93  fof(f34,plain,(
% 4.04/0.93    ! [X0,X1] : ((r1_tarski(X0,X1) | ? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0))) & (! [X2] : (r2_hidden(X2,X1) | ~r2_hidden(X2,X0)) | ~r1_tarski(X0,X1)))),
% 4.04/0.93    inference(nnf_transformation,[],[f16])).
% 4.04/0.93  
% 4.04/0.93  fof(f35,plain,(
% 4.04/0.93    ! [X0,X1] : ((r1_tarski(X0,X1) | ? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0))) & (! [X3] : (r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) | ~r1_tarski(X0,X1)))),
% 4.04/0.93    inference(rectify,[],[f34])).
% 4.04/0.93  
% 4.04/0.93  fof(f36,plain,(
% 4.04/0.93    ! [X1,X0] : (? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0)) => (~r2_hidden(sK1(X0,X1),X1) & r2_hidden(sK1(X0,X1),X0)))),
% 4.04/0.93    introduced(choice_axiom,[])).
% 4.04/0.93  
% 4.04/0.93  fof(f37,plain,(
% 4.04/0.93    ! [X0,X1] : ((r1_tarski(X0,X1) | (~r2_hidden(sK1(X0,X1),X1) & r2_hidden(sK1(X0,X1),X0))) & (! [X3] : (r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) | ~r1_tarski(X0,X1)))),
% 4.04/0.93    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1])],[f35,f36])).
% 4.04/0.93  
% 4.04/0.93  fof(f61,plain,(
% 4.04/0.93    ( ! [X0,X1] : (r1_tarski(X0,X1) | r2_hidden(sK1(X0,X1),X0)) )),
% 4.04/0.93    inference(cnf_transformation,[],[f37])).
% 4.04/0.93  
% 4.04/0.93  fof(f62,plain,(
% 4.04/0.93    ( ! [X0,X1] : (r1_tarski(X0,X1) | ~r2_hidden(sK1(X0,X1),X1)) )),
% 4.04/0.93    inference(cnf_transformation,[],[f37])).
% 4.04/0.93  
% 4.04/0.93  fof(f5,axiom,(
% 4.04/0.93    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(X0)) => (! [X3] : (m1_subset_1(X3,X0) => (r2_hidden(X3,X1) <=> r2_hidden(X3,X2))) => X1 = X2)))),
% 4.04/0.93    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 4.04/0.93  
% 4.04/0.93  fof(f18,plain,(
% 4.04/0.93    ! [X0,X1] : (! [X2] : ((X1 = X2 | ? [X3] : ((r2_hidden(X3,X1) <~> r2_hidden(X3,X2)) & m1_subset_1(X3,X0))) | ~m1_subset_1(X2,k1_zfmisc_1(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 4.04/0.93    inference(ennf_transformation,[],[f5])).
% 4.04/0.93  
% 4.04/0.93  fof(f19,plain,(
% 4.04/0.93    ! [X0,X1] : (! [X2] : (X1 = X2 | ? [X3] : ((r2_hidden(X3,X1) <~> r2_hidden(X3,X2)) & m1_subset_1(X3,X0)) | ~m1_subset_1(X2,k1_zfmisc_1(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 4.04/0.93    inference(flattening,[],[f18])).
% 4.04/0.93  
% 4.04/0.93  fof(f43,plain,(
% 4.04/0.93    ! [X0,X1] : (! [X2] : (X1 = X2 | ? [X3] : (((~r2_hidden(X3,X2) | ~r2_hidden(X3,X1)) & (r2_hidden(X3,X2) | r2_hidden(X3,X1))) & m1_subset_1(X3,X0)) | ~m1_subset_1(X2,k1_zfmisc_1(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 4.04/0.93    inference(nnf_transformation,[],[f19])).
% 4.04/0.93  
% 4.04/0.93  fof(f44,plain,(
% 4.04/0.93    ! [X0,X1] : (! [X2] : (X1 = X2 | ? [X3] : ((~r2_hidden(X3,X2) | ~r2_hidden(X3,X1)) & (r2_hidden(X3,X2) | r2_hidden(X3,X1)) & m1_subset_1(X3,X0)) | ~m1_subset_1(X2,k1_zfmisc_1(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 4.04/0.93    inference(flattening,[],[f43])).
% 4.04/0.93  
% 4.04/0.93  fof(f45,plain,(
% 4.04/0.93    ! [X2,X1,X0] : (? [X3] : ((~r2_hidden(X3,X2) | ~r2_hidden(X3,X1)) & (r2_hidden(X3,X2) | r2_hidden(X3,X1)) & m1_subset_1(X3,X0)) => ((~r2_hidden(sK3(X0,X1,X2),X2) | ~r2_hidden(sK3(X0,X1,X2),X1)) & (r2_hidden(sK3(X0,X1,X2),X2) | r2_hidden(sK3(X0,X1,X2),X1)) & m1_subset_1(sK3(X0,X1,X2),X0)))),
% 4.04/0.93    introduced(choice_axiom,[])).
% 4.04/0.93  
% 4.04/0.93  fof(f46,plain,(
% 4.04/0.93    ! [X0,X1] : (! [X2] : (X1 = X2 | ((~r2_hidden(sK3(X0,X1,X2),X2) | ~r2_hidden(sK3(X0,X1,X2),X1)) & (r2_hidden(sK3(X0,X1,X2),X2) | r2_hidden(sK3(X0,X1,X2),X1)) & m1_subset_1(sK3(X0,X1,X2),X0)) | ~m1_subset_1(X2,k1_zfmisc_1(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 4.04/0.93    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3])],[f44,f45])).
% 4.04/0.93  
% 4.04/0.93  fof(f73,plain,(
% 4.04/0.93    ( ! [X2,X0,X1] : (X1 = X2 | ~r2_hidden(sK3(X0,X1,X2),X2) | ~r2_hidden(sK3(X0,X1,X2),X1) | ~m1_subset_1(X2,k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 4.04/0.93    inference(cnf_transformation,[],[f46])).
% 4.04/0.93  
% 4.04/0.93  fof(f67,plain,(
% 4.04/0.93    ( ! [X0,X1] : (r2_hidden(X1,X0) | ~m1_subset_1(X1,X0) | v1_xboole_0(X0)) )),
% 4.04/0.93    inference(cnf_transformation,[],[f42])).
% 4.04/0.93  
% 4.04/0.93  fof(f89,plain,(
% 4.04/0.93    ~v1_xboole_0(sK7)),
% 4.04/0.93    inference(cnf_transformation,[],[f57])).
% 4.04/0.93  
% 4.04/0.93  fof(f69,plain,(
% 4.04/0.93    ( ! [X0,X1] : (v1_xboole_0(X1) | ~m1_subset_1(X1,X0) | ~v1_xboole_0(X0)) )),
% 4.04/0.93    inference(cnf_transformation,[],[f42])).
% 4.04/0.93  
% 4.04/0.93  fof(f63,plain,(
% 4.04/0.93    ( ! [X0,X3,X1] : (r1_tarski(X3,X0) | ~r2_hidden(X3,X1) | k1_zfmisc_1(X0) != X1) )),
% 4.04/0.93    inference(cnf_transformation,[],[f41])).
% 4.04/0.93  
% 4.04/0.93  fof(f95,plain,(
% 4.04/0.93    ( ! [X0,X3] : (r1_tarski(X3,X0) | ~r2_hidden(X3,k1_zfmisc_1(X0))) )),
% 4.04/0.93    inference(equality_resolution,[],[f63])).
% 4.04/0.93  
% 4.04/0.93  fof(f60,plain,(
% 4.04/0.93    ( ! [X0,X3,X1] : (r2_hidden(X3,X1) | ~r2_hidden(X3,X0) | ~r1_tarski(X0,X1)) )),
% 4.04/0.93    inference(cnf_transformation,[],[f37])).
% 4.04/0.93  
% 4.04/0.93  fof(f72,plain,(
% 4.04/0.93    ( ! [X2,X0,X1] : (X1 = X2 | r2_hidden(sK3(X0,X1,X2),X2) | r2_hidden(sK3(X0,X1,X2),X1) | ~m1_subset_1(X2,k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 4.04/0.93    inference(cnf_transformation,[],[f46])).
% 4.04/0.93  
% 4.04/0.93  fof(f7,axiom,(
% 4.04/0.93    ! [X0] : (l1_orders_2(X0) => m1_subset_1(k3_yellow_0(X0),u1_struct_0(X0)))),
% 4.04/0.93    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 4.04/0.93  
% 4.04/0.93  fof(f22,plain,(
% 4.04/0.93    ! [X0] : (m1_subset_1(k3_yellow_0(X0),u1_struct_0(X0)) | ~l1_orders_2(X0))),
% 4.04/0.93    inference(ennf_transformation,[],[f7])).
% 4.04/0.93  
% 4.04/0.93  fof(f75,plain,(
% 4.04/0.93    ( ! [X0] : (m1_subset_1(k3_yellow_0(X0),u1_struct_0(X0)) | ~l1_orders_2(X0)) )),
% 4.04/0.93    inference(cnf_transformation,[],[f22])).
% 4.04/0.93  
% 4.04/0.93  fof(f83,plain,(
% 4.04/0.93    ( ! [X0,X1] : (X0 != X1 | ~v1_subset_1(X1,X0) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 4.04/0.93    inference(cnf_transformation,[],[f52])).
% 4.04/0.93  
% 4.04/0.93  fof(f96,plain,(
% 4.04/0.93    ( ! [X1] : (~v1_subset_1(X1,X1) | ~m1_subset_1(X1,k1_zfmisc_1(X1))) )),
% 4.04/0.93    inference(equality_resolution,[],[f83])).
% 4.04/0.93  
% 4.04/0.93  fof(f92,plain,(
% 4.04/0.93    ~r2_hidden(k3_yellow_0(sK6),sK7) | v1_subset_1(sK7,u1_struct_0(sK6))),
% 4.04/0.93    inference(cnf_transformation,[],[f57])).
% 4.04/0.93  
% 4.04/0.93  cnf(c_6,plain,
% 4.04/0.93      ( r1_tarski(sK2(X0,X1),X0)
% 4.04/0.93      | r2_hidden(sK2(X0,X1),X1)
% 4.04/0.93      | k1_zfmisc_1(X0) = X1 ),
% 4.04/0.93      inference(cnf_transformation,[],[f65]) ).
% 4.04/0.93  
% 4.04/0.93  cnf(c_1306,plain,
% 4.04/0.93      ( k1_zfmisc_1(X0) = X1
% 4.04/0.93      | r1_tarski(sK2(X0,X1),X0) = iProver_top
% 4.04/0.93      | r2_hidden(sK2(X0,X1),X1) = iProver_top ),
% 4.04/0.93      inference(predicate_to_equality,[status(thm)],[c_6]) ).
% 4.04/0.93  
% 4.04/0.93  cnf(c_29,negated_conjecture,
% 4.04/0.93      ( m1_subset_1(sK7,k1_zfmisc_1(u1_struct_0(sK6))) ),
% 4.04/0.93      inference(cnf_transformation,[],[f91]) ).
% 4.04/0.93  
% 4.04/0.93  cnf(c_1284,plain,
% 4.04/0.93      ( m1_subset_1(sK7,k1_zfmisc_1(u1_struct_0(sK6))) = iProver_top ),
% 4.04/0.93      inference(predicate_to_equality,[status(thm)],[c_29]) ).
% 4.04/0.93  
% 4.04/0.93  cnf(c_25,plain,
% 4.04/0.93      ( v1_subset_1(X0,X1)
% 4.04/0.93      | ~ m1_subset_1(X0,k1_zfmisc_1(X1))
% 4.04/0.93      | X0 = X1 ),
% 4.04/0.93      inference(cnf_transformation,[],[f84]) ).
% 4.04/0.93  
% 4.04/0.93  cnf(c_1288,plain,
% 4.04/0.93      ( X0 = X1
% 4.04/0.93      | v1_subset_1(X0,X1) = iProver_top
% 4.04/0.93      | m1_subset_1(X0,k1_zfmisc_1(X1)) != iProver_top ),
% 4.04/0.93      inference(predicate_to_equality,[status(thm)],[c_25]) ).
% 4.04/0.93  
% 4.04/0.93  cnf(c_2649,plain,
% 4.04/0.93      ( u1_struct_0(sK6) = sK7
% 4.04/0.93      | v1_subset_1(sK7,u1_struct_0(sK6)) = iProver_top ),
% 4.04/0.93      inference(superposition,[status(thm)],[c_1284,c_1288]) ).
% 4.04/0.93  
% 4.04/0.93  cnf(c_27,negated_conjecture,
% 4.04/0.93      ( ~ v1_subset_1(sK7,u1_struct_0(sK6))
% 4.04/0.93      | r2_hidden(k3_yellow_0(sK6),sK7) ),
% 4.04/0.93      inference(cnf_transformation,[],[f93]) ).
% 4.04/0.93  
% 4.04/0.93  cnf(c_1286,plain,
% 4.04/0.93      ( v1_subset_1(sK7,u1_struct_0(sK6)) != iProver_top
% 4.04/0.93      | r2_hidden(k3_yellow_0(sK6),sK7) = iProver_top ),
% 4.04/0.93      inference(predicate_to_equality,[status(thm)],[c_27]) ).
% 4.04/0.93  
% 4.04/0.93  cnf(c_3091,plain,
% 4.04/0.93      ( u1_struct_0(sK6) = sK7
% 4.04/0.93      | r2_hidden(k3_yellow_0(sK6),sK7) = iProver_top ),
% 4.04/0.93      inference(superposition,[status(thm)],[c_2649,c_1286]) ).
% 4.04/0.93  
% 4.04/0.93  cnf(c_18,plain,
% 4.04/0.93      ( r1_orders_2(X0,k3_yellow_0(X0),X1)
% 4.04/0.93      | ~ m1_subset_1(X1,u1_struct_0(X0))
% 4.04/0.93      | v2_struct_0(X0)
% 4.04/0.93      | ~ v5_orders_2(X0)
% 4.04/0.93      | ~ v1_yellow_0(X0)
% 4.04/0.93      | ~ l1_orders_2(X0) ),
% 4.04/0.93      inference(cnf_transformation,[],[f76]) ).
% 4.04/0.93  
% 4.04/0.93  cnf(c_1295,plain,
% 4.04/0.93      ( r1_orders_2(X0,k3_yellow_0(X0),X1) = iProver_top
% 4.04/0.93      | m1_subset_1(X1,u1_struct_0(X0)) != iProver_top
% 4.04/0.93      | v2_struct_0(X0) = iProver_top
% 4.04/0.93      | v5_orders_2(X0) != iProver_top
% 4.04/0.93      | v1_yellow_0(X0) != iProver_top
% 4.04/0.93      | l1_orders_2(X0) != iProver_top ),
% 4.04/0.93      inference(predicate_to_equality,[status(thm)],[c_18]) ).
% 4.04/0.93  
% 4.04/0.93  cnf(c_0,plain,
% 4.04/0.93      ( r2_hidden(sK0(X0),X0) | v1_xboole_0(X0) ),
% 4.04/0.93      inference(cnf_transformation,[],[f59]) ).
% 4.04/0.93  
% 4.04/0.93  cnf(c_1312,plain,
% 4.04/0.93      ( r2_hidden(sK0(X0),X0) = iProver_top
% 4.04/0.93      | v1_xboole_0(X0) = iProver_top ),
% 4.04/0.93      inference(predicate_to_equality,[status(thm)],[c_0]) ).
% 4.04/0.93  
% 4.04/0.93  cnf(c_7,plain,
% 4.04/0.93      ( ~ r1_tarski(X0,X1) | r2_hidden(X0,k1_zfmisc_1(X1)) ),
% 4.04/0.93      inference(cnf_transformation,[],[f94]) ).
% 4.04/0.93  
% 4.04/0.93  cnf(c_1305,plain,
% 4.04/0.93      ( r1_tarski(X0,X1) != iProver_top
% 4.04/0.93      | r2_hidden(X0,k1_zfmisc_1(X1)) = iProver_top ),
% 4.04/0.93      inference(predicate_to_equality,[status(thm)],[c_7]) ).
% 4.04/0.93  
% 4.04/0.93  cnf(c_11,plain,
% 4.04/0.93      ( m1_subset_1(X0,X1) | ~ r2_hidden(X0,X1) | v1_xboole_0(X1) ),
% 4.04/0.93      inference(cnf_transformation,[],[f68]) ).
% 4.04/0.93  
% 4.04/0.93  cnf(c_1,plain,
% 4.04/0.93      ( ~ r2_hidden(X0,X1) | ~ v1_xboole_0(X1) ),
% 4.04/0.93      inference(cnf_transformation,[],[f58]) ).
% 4.04/0.93  
% 4.04/0.93  cnf(c_354,plain,
% 4.04/0.93      ( ~ r2_hidden(X0,X1) | m1_subset_1(X0,X1) ),
% 4.04/0.93      inference(global_propositional_subsumption,
% 4.04/0.93                [status(thm)],
% 4.04/0.93                [c_11,c_1]) ).
% 4.04/0.93  
% 4.04/0.93  cnf(c_355,plain,
% 4.04/0.93      ( m1_subset_1(X0,X1) | ~ r2_hidden(X0,X1) ),
% 4.04/0.93      inference(renaming,[status(thm)],[c_354]) ).
% 4.04/0.93  
% 4.04/0.93  cnf(c_1277,plain,
% 4.04/0.93      ( m1_subset_1(X0,X1) = iProver_top
% 4.04/0.93      | r2_hidden(X0,X1) != iProver_top ),
% 4.04/0.93      inference(predicate_to_equality,[status(thm)],[c_355]) ).
% 4.04/0.93  
% 4.04/0.93  cnf(c_2243,plain,
% 4.04/0.93      ( m1_subset_1(X0,k1_zfmisc_1(X1)) = iProver_top
% 4.04/0.93      | r1_tarski(X0,X1) != iProver_top ),
% 4.04/0.93      inference(superposition,[status(thm)],[c_1305,c_1277]) ).
% 4.04/0.93  
% 4.04/0.93  cnf(c_16,plain,
% 4.04/0.93      ( m1_subset_1(X0,X1)
% 4.04/0.93      | ~ m1_subset_1(X2,k1_zfmisc_1(X1))
% 4.04/0.93      | ~ r2_hidden(X0,X2) ),
% 4.04/0.93      inference(cnf_transformation,[],[f74]) ).
% 4.04/0.93  
% 4.04/0.93  cnf(c_1297,plain,
% 4.04/0.93      ( m1_subset_1(X0,X1) = iProver_top
% 4.04/0.93      | m1_subset_1(X2,k1_zfmisc_1(X1)) != iProver_top
% 4.04/0.93      | r2_hidden(X0,X2) != iProver_top ),
% 4.04/0.93      inference(predicate_to_equality,[status(thm)],[c_16]) ).
% 4.04/0.93  
% 4.04/0.93  cnf(c_3509,plain,
% 4.04/0.93      ( m1_subset_1(X0,X1) = iProver_top
% 4.04/0.93      | r1_tarski(X2,X1) != iProver_top
% 4.04/0.93      | r2_hidden(X0,X2) != iProver_top ),
% 4.04/0.93      inference(superposition,[status(thm)],[c_2243,c_1297]) ).
% 4.04/0.93  
% 4.04/0.93  cnf(c_6689,plain,
% 4.04/0.93      ( m1_subset_1(sK0(X0),X1) = iProver_top
% 4.04/0.93      | r1_tarski(X0,X1) != iProver_top
% 4.04/0.93      | v1_xboole_0(X0) = iProver_top ),
% 4.04/0.93      inference(superposition,[status(thm)],[c_1312,c_3509]) ).
% 4.04/0.93  
% 4.04/0.93  cnf(c_24,plain,
% 4.04/0.93      ( ~ r1_orders_2(X0,X1,X2)
% 4.04/0.93      | ~ v13_waybel_0(X3,X0)
% 4.04/0.93      | ~ m1_subset_1(X2,u1_struct_0(X0))
% 4.04/0.93      | ~ m1_subset_1(X1,u1_struct_0(X0))
% 4.04/0.93      | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))
% 4.04/0.93      | ~ r2_hidden(X1,X3)
% 4.04/0.93      | r2_hidden(X2,X3)
% 4.04/0.93      | ~ l1_orders_2(X0) ),
% 4.04/0.93      inference(cnf_transformation,[],[f77]) ).
% 4.04/0.93  
% 4.04/0.93  cnf(c_1289,plain,
% 4.04/0.93      ( r1_orders_2(X0,X1,X2) != iProver_top
% 4.04/0.93      | v13_waybel_0(X3,X0) != iProver_top
% 4.04/0.93      | m1_subset_1(X2,u1_struct_0(X0)) != iProver_top
% 4.04/0.93      | m1_subset_1(X1,u1_struct_0(X0)) != iProver_top
% 4.04/0.93      | m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) != iProver_top
% 4.04/0.93      | r2_hidden(X1,X3) != iProver_top
% 4.04/0.93      | r2_hidden(X2,X3) = iProver_top
% 4.04/0.93      | l1_orders_2(X0) != iProver_top ),
% 4.04/0.93      inference(predicate_to_equality,[status(thm)],[c_24]) ).
% 4.04/0.93  
% 4.04/0.93  cnf(c_1507,plain,
% 4.04/0.93      ( r1_orders_2(X0,X1,X2) != iProver_top
% 4.04/0.93      | v13_waybel_0(X3,X0) != iProver_top
% 4.04/0.93      | m1_subset_1(X2,u1_struct_0(X0)) != iProver_top
% 4.04/0.93      | m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) != iProver_top
% 4.04/0.93      | r2_hidden(X1,X3) != iProver_top
% 4.04/0.93      | r2_hidden(X2,X3) = iProver_top
% 4.04/0.93      | l1_orders_2(X0) != iProver_top ),
% 4.04/0.93      inference(forward_subsumption_resolution,
% 4.04/0.93                [status(thm)],
% 4.04/0.93                [c_1289,c_1297]) ).
% 4.04/0.93  
% 4.04/0.93  cnf(c_6961,plain,
% 4.04/0.93      ( r1_orders_2(sK6,X0,X1) != iProver_top
% 4.04/0.93      | v13_waybel_0(sK7,sK6) != iProver_top
% 4.04/0.93      | m1_subset_1(X1,u1_struct_0(sK6)) != iProver_top
% 4.04/0.93      | r2_hidden(X0,sK7) != iProver_top
% 4.04/0.93      | r2_hidden(X1,sK7) = iProver_top
% 4.04/0.93      | l1_orders_2(sK6) != iProver_top ),
% 4.04/0.93      inference(superposition,[status(thm)],[c_1284,c_1507]) ).
% 4.04/0.93  
% 4.04/0.93  cnf(c_32,negated_conjecture,
% 4.04/0.93      ( l1_orders_2(sK6) ),
% 4.04/0.93      inference(cnf_transformation,[],[f88]) ).
% 4.04/0.93  
% 4.04/0.93  cnf(c_39,plain,
% 4.04/0.93      ( l1_orders_2(sK6) = iProver_top ),
% 4.04/0.93      inference(predicate_to_equality,[status(thm)],[c_32]) ).
% 4.04/0.93  
% 4.04/0.93  cnf(c_30,negated_conjecture,
% 4.04/0.93      ( v13_waybel_0(sK7,sK6) ),
% 4.04/0.93      inference(cnf_transformation,[],[f90]) ).
% 4.04/0.93  
% 4.04/0.93  cnf(c_41,plain,
% 4.04/0.93      ( v13_waybel_0(sK7,sK6) = iProver_top ),
% 4.04/0.93      inference(predicate_to_equality,[status(thm)],[c_30]) ).
% 4.04/0.93  
% 4.04/0.93  cnf(c_7523,plain,
% 4.04/0.93      ( r2_hidden(X1,sK7) = iProver_top
% 4.04/0.93      | r2_hidden(X0,sK7) != iProver_top
% 4.04/0.93      | m1_subset_1(X1,u1_struct_0(sK6)) != iProver_top
% 4.04/0.93      | r1_orders_2(sK6,X0,X1) != iProver_top ),
% 4.04/0.93      inference(global_propositional_subsumption,
% 4.04/0.93                [status(thm)],
% 4.04/0.93                [c_6961,c_39,c_41]) ).
% 4.04/0.93  
% 4.04/0.93  cnf(c_7524,plain,
% 4.04/0.93      ( r1_orders_2(sK6,X0,X1) != iProver_top
% 4.04/0.93      | m1_subset_1(X1,u1_struct_0(sK6)) != iProver_top
% 4.04/0.93      | r2_hidden(X0,sK7) != iProver_top
% 4.04/0.93      | r2_hidden(X1,sK7) = iProver_top ),
% 4.04/0.93      inference(renaming,[status(thm)],[c_7523]) ).
% 4.04/0.93  
% 4.04/0.93  cnf(c_11109,plain,
% 4.04/0.93      ( r1_orders_2(sK6,X0,sK0(X1)) != iProver_top
% 4.04/0.93      | r1_tarski(X1,u1_struct_0(sK6)) != iProver_top
% 4.04/0.93      | r2_hidden(X0,sK7) != iProver_top
% 4.04/0.93      | r2_hidden(sK0(X1),sK7) = iProver_top
% 4.04/0.93      | v1_xboole_0(X1) = iProver_top ),
% 4.04/0.93      inference(superposition,[status(thm)],[c_6689,c_7524]) ).
% 4.04/0.93  
% 4.04/0.93  cnf(c_11495,plain,
% 4.04/0.93      ( m1_subset_1(sK0(X0),u1_struct_0(sK6)) != iProver_top
% 4.04/0.93      | r1_tarski(X0,u1_struct_0(sK6)) != iProver_top
% 4.04/0.93      | r2_hidden(k3_yellow_0(sK6),sK7) != iProver_top
% 4.04/0.93      | r2_hidden(sK0(X0),sK7) = iProver_top
% 4.04/0.93      | v2_struct_0(sK6) = iProver_top
% 4.04/0.93      | v5_orders_2(sK6) != iProver_top
% 4.04/0.93      | v1_yellow_0(sK6) != iProver_top
% 4.04/0.93      | l1_orders_2(sK6) != iProver_top
% 4.04/0.93      | v1_xboole_0(X0) = iProver_top ),
% 4.04/0.93      inference(superposition,[status(thm)],[c_1295,c_11109]) ).
% 4.04/0.93  
% 4.04/0.93  cnf(c_35,negated_conjecture,
% 4.04/0.93      ( ~ v2_struct_0(sK6) ),
% 4.04/0.93      inference(cnf_transformation,[],[f85]) ).
% 4.04/0.93  
% 4.04/0.93  cnf(c_36,plain,
% 4.04/0.93      ( v2_struct_0(sK6) != iProver_top ),
% 4.04/0.93      inference(predicate_to_equality,[status(thm)],[c_35]) ).
% 4.04/0.93  
% 4.04/0.93  cnf(c_34,negated_conjecture,
% 4.04/0.93      ( v5_orders_2(sK6) ),
% 4.04/0.93      inference(cnf_transformation,[],[f86]) ).
% 4.04/0.93  
% 4.04/0.93  cnf(c_37,plain,
% 4.04/0.93      ( v5_orders_2(sK6) = iProver_top ),
% 4.04/0.93      inference(predicate_to_equality,[status(thm)],[c_34]) ).
% 4.04/0.93  
% 4.04/0.93  cnf(c_33,negated_conjecture,
% 4.04/0.93      ( v1_yellow_0(sK6) ),
% 4.04/0.93      inference(cnf_transformation,[],[f87]) ).
% 4.04/0.93  
% 4.04/0.93  cnf(c_38,plain,
% 4.04/0.93      ( v1_yellow_0(sK6) = iProver_top ),
% 4.04/0.93      inference(predicate_to_equality,[status(thm)],[c_33]) ).
% 4.04/0.93  
% 4.04/0.93  cnf(c_11872,plain,
% 4.04/0.93      ( m1_subset_1(sK0(X0),u1_struct_0(sK6)) != iProver_top
% 4.04/0.93      | r1_tarski(X0,u1_struct_0(sK6)) != iProver_top
% 4.04/0.93      | r2_hidden(k3_yellow_0(sK6),sK7) != iProver_top
% 4.04/0.93      | r2_hidden(sK0(X0),sK7) = iProver_top
% 4.04/0.93      | v1_xboole_0(X0) = iProver_top ),
% 4.04/0.93      inference(global_propositional_subsumption,
% 4.04/0.93                [status(thm)],
% 4.04/0.93                [c_11495,c_36,c_37,c_38,c_39]) ).
% 4.04/0.93  
% 4.04/0.93  cnf(c_11883,plain,
% 4.04/0.93      ( r1_tarski(X0,u1_struct_0(sK6)) != iProver_top
% 4.04/0.93      | r2_hidden(k3_yellow_0(sK6),sK7) != iProver_top
% 4.04/0.93      | r2_hidden(sK0(X0),sK7) = iProver_top
% 4.04/0.93      | v1_xboole_0(X0) = iProver_top ),
% 4.04/0.93      inference(forward_subsumption_resolution,
% 4.04/0.93                [status(thm)],
% 4.04/0.93                [c_11872,c_6689]) ).
% 4.04/0.93  
% 4.04/0.93  cnf(c_11887,plain,
% 4.04/0.93      ( u1_struct_0(sK6) = sK7
% 4.04/0.93      | r1_tarski(X0,u1_struct_0(sK6)) != iProver_top
% 4.04/0.93      | r2_hidden(sK0(X0),sK7) = iProver_top
% 4.04/0.93      | v1_xboole_0(X0) = iProver_top ),
% 4.04/0.93      inference(superposition,[status(thm)],[c_3091,c_11883]) ).
% 4.04/0.93  
% 4.04/0.93  cnf(c_11917,plain,
% 4.04/0.93      ( u1_struct_0(sK6) = sK7
% 4.04/0.93      | k1_zfmisc_1(u1_struct_0(sK6)) = X0
% 4.04/0.93      | r2_hidden(sK2(u1_struct_0(sK6),X0),X0) = iProver_top
% 4.04/0.93      | r2_hidden(sK0(sK2(u1_struct_0(sK6),X0)),sK7) = iProver_top
% 4.04/0.93      | v1_xboole_0(sK2(u1_struct_0(sK6),X0)) = iProver_top ),
% 4.04/0.93      inference(superposition,[status(thm)],[c_1306,c_11887]) ).
% 4.04/0.93  
% 4.04/0.93  cnf(c_3,plain,
% 4.04/0.93      ( r1_tarski(X0,X1) | r2_hidden(sK1(X0,X1),X0) ),
% 4.04/0.93      inference(cnf_transformation,[],[f61]) ).
% 4.04/0.93  
% 4.04/0.93  cnf(c_1309,plain,
% 4.04/0.93      ( r1_tarski(X0,X1) = iProver_top
% 4.04/0.93      | r2_hidden(sK1(X0,X1),X0) = iProver_top ),
% 4.04/0.93      inference(predicate_to_equality,[status(thm)],[c_3]) ).
% 4.04/0.93  
% 4.04/0.93  cnf(c_2666,plain,
% 4.04/0.93      ( m1_subset_1(sK1(X0,X1),X0) = iProver_top
% 4.04/0.93      | r1_tarski(X0,X1) = iProver_top ),
% 4.04/0.93      inference(superposition,[status(thm)],[c_1309,c_1277]) ).
% 4.04/0.93  
% 4.04/0.93  cnf(c_7537,plain,
% 4.04/0.93      ( r1_orders_2(sK6,X0,sK1(u1_struct_0(sK6),X1)) != iProver_top
% 4.04/0.93      | r1_tarski(u1_struct_0(sK6),X1) = iProver_top
% 4.04/0.93      | r2_hidden(X0,sK7) != iProver_top
% 4.04/0.93      | r2_hidden(sK1(u1_struct_0(sK6),X1),sK7) = iProver_top ),
% 4.04/0.93      inference(superposition,[status(thm)],[c_2666,c_7524]) ).
% 4.04/0.93  
% 4.04/0.93  cnf(c_8022,plain,
% 4.04/0.93      ( m1_subset_1(sK1(u1_struct_0(sK6),X0),u1_struct_0(sK6)) != iProver_top
% 4.04/0.93      | r1_tarski(u1_struct_0(sK6),X0) = iProver_top
% 4.04/0.93      | r2_hidden(sK1(u1_struct_0(sK6),X0),sK7) = iProver_top
% 4.04/0.93      | r2_hidden(k3_yellow_0(sK6),sK7) != iProver_top
% 4.04/0.93      | v2_struct_0(sK6) = iProver_top
% 4.04/0.93      | v5_orders_2(sK6) != iProver_top
% 4.04/0.93      | v1_yellow_0(sK6) != iProver_top
% 4.04/0.93      | l1_orders_2(sK6) != iProver_top ),
% 4.04/0.93      inference(superposition,[status(thm)],[c_1295,c_7537]) ).
% 4.04/0.93  
% 4.04/0.93  cnf(c_11638,plain,
% 4.04/0.93      ( m1_subset_1(sK1(u1_struct_0(sK6),X0),u1_struct_0(sK6)) != iProver_top
% 4.04/0.93      | r1_tarski(u1_struct_0(sK6),X0) = iProver_top
% 4.04/0.93      | r2_hidden(sK1(u1_struct_0(sK6),X0),sK7) = iProver_top
% 4.04/0.93      | r2_hidden(k3_yellow_0(sK6),sK7) != iProver_top ),
% 4.04/0.93      inference(global_propositional_subsumption,
% 4.04/0.93                [status(thm)],
% 4.04/0.93                [c_8022,c_36,c_37,c_38,c_39]) ).
% 4.04/0.93  
% 4.04/0.93  cnf(c_11648,plain,
% 4.04/0.93      ( r1_tarski(u1_struct_0(sK6),X0) = iProver_top
% 4.04/0.93      | r2_hidden(sK1(u1_struct_0(sK6),X0),sK7) = iProver_top
% 4.04/0.93      | r2_hidden(k3_yellow_0(sK6),sK7) != iProver_top ),
% 4.04/0.93      inference(forward_subsumption_resolution,
% 4.04/0.93                [status(thm)],
% 4.04/0.93                [c_11638,c_2666]) ).
% 4.04/0.93  
% 4.04/0.93  cnf(c_2,plain,
% 4.04/0.93      ( r1_tarski(X0,X1) | ~ r2_hidden(sK1(X0,X1),X1) ),
% 4.04/0.93      inference(cnf_transformation,[],[f62]) ).
% 4.04/0.93  
% 4.04/0.93  cnf(c_1310,plain,
% 4.04/0.93      ( r1_tarski(X0,X1) = iProver_top
% 4.04/0.93      | r2_hidden(sK1(X0,X1),X1) != iProver_top ),
% 4.04/0.93      inference(predicate_to_equality,[status(thm)],[c_2]) ).
% 4.04/0.93  
% 4.04/0.93  cnf(c_11654,plain,
% 4.04/0.93      ( r1_tarski(u1_struct_0(sK6),sK7) = iProver_top
% 4.04/0.93      | r2_hidden(k3_yellow_0(sK6),sK7) != iProver_top ),
% 4.04/0.93      inference(superposition,[status(thm)],[c_11648,c_1310]) ).
% 4.04/0.93  
% 4.04/0.93  cnf(c_12242,plain,
% 4.04/0.93      ( u1_struct_0(sK6) = sK7
% 4.04/0.93      | r1_tarski(u1_struct_0(sK6),sK7) = iProver_top ),
% 4.04/0.93      inference(superposition,[status(thm)],[c_3091,c_11654]) ).
% 4.04/0.93  
% 4.04/0.93  cnf(c_12254,plain,
% 4.04/0.93      ( r1_tarski(u1_struct_0(sK6),sK7) | u1_struct_0(sK6) = sK7 ),
% 4.04/0.93      inference(predicate_to_equality_rev,[status(thm)],[c_12242]) ).
% 4.04/0.93  
% 4.04/0.93  cnf(c_13,plain,
% 4.04/0.93      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
% 4.04/0.93      | ~ m1_subset_1(X2,k1_zfmisc_1(X1))
% 4.04/0.93      | ~ r2_hidden(sK3(X1,X2,X0),X0)
% 4.04/0.93      | ~ r2_hidden(sK3(X1,X2,X0),X2)
% 4.04/0.93      | X2 = X0 ),
% 4.04/0.93      inference(cnf_transformation,[],[f73]) ).
% 4.04/0.93  
% 4.04/0.93  cnf(c_2974,plain,
% 4.04/0.93      ( m1_subset_1(X0,u1_struct_0(sK6)) | ~ r2_hidden(X0,sK7) ),
% 4.04/0.93      inference(resolution,[status(thm)],[c_16,c_29]) ).
% 4.04/0.93  
% 4.04/0.93  cnf(c_12,plain,
% 4.04/0.93      ( ~ m1_subset_1(X0,X1) | r2_hidden(X0,X1) | v1_xboole_0(X1) ),
% 4.04/0.93      inference(cnf_transformation,[],[f67]) ).
% 4.04/0.93  
% 4.04/0.93  cnf(c_3038,plain,
% 4.04/0.93      ( r2_hidden(X0,u1_struct_0(sK6))
% 4.04/0.93      | ~ r2_hidden(X0,sK7)
% 4.04/0.93      | v1_xboole_0(u1_struct_0(sK6)) ),
% 4.04/0.93      inference(resolution,[status(thm)],[c_2974,c_12]) ).
% 4.04/0.93  
% 4.04/0.93  cnf(c_8079,plain,
% 4.04/0.93      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
% 4.04/0.93      | ~ m1_subset_1(u1_struct_0(sK6),k1_zfmisc_1(X1))
% 4.04/0.93      | ~ r2_hidden(sK3(X1,u1_struct_0(sK6),X0),X0)
% 4.04/0.93      | ~ r2_hidden(sK3(X1,u1_struct_0(sK6),X0),sK7)
% 4.04/0.93      | v1_xboole_0(u1_struct_0(sK6))
% 4.04/0.93      | u1_struct_0(sK6) = X0 ),
% 4.04/0.93      inference(resolution,[status(thm)],[c_13,c_3038]) ).
% 4.04/0.93  
% 4.04/0.93  cnf(c_31,negated_conjecture,
% 4.04/0.93      ( ~ v1_xboole_0(sK7) ),
% 4.04/0.93      inference(cnf_transformation,[],[f89]) ).
% 4.04/0.93  
% 4.04/0.93  cnf(c_1301,plain,
% 4.04/0.93      ( m1_subset_1(X0,X1) != iProver_top
% 4.04/0.93      | r2_hidden(X0,X1) = iProver_top
% 4.04/0.93      | v1_xboole_0(X1) = iProver_top ),
% 4.04/0.93      inference(predicate_to_equality,[status(thm)],[c_12]) ).
% 4.04/0.93  
% 4.04/0.93  cnf(c_2905,plain,
% 4.04/0.93      ( r2_hidden(sK7,k1_zfmisc_1(u1_struct_0(sK6))) = iProver_top
% 4.04/0.93      | v1_xboole_0(k1_zfmisc_1(u1_struct_0(sK6))) = iProver_top ),
% 4.04/0.93      inference(superposition,[status(thm)],[c_1284,c_1301]) ).
% 4.04/0.93  
% 4.04/0.93  cnf(c_40,plain,
% 4.04/0.93      ( v1_xboole_0(sK7) != iProver_top ),
% 4.04/0.93      inference(predicate_to_equality,[status(thm)],[c_31]) ).
% 4.04/0.93  
% 4.04/0.93  cnf(c_42,plain,
% 4.04/0.93      ( m1_subset_1(sK7,k1_zfmisc_1(u1_struct_0(sK6))) = iProver_top ),
% 4.04/0.93      inference(predicate_to_equality,[status(thm)],[c_29]) ).
% 4.04/0.93  
% 4.04/0.93  cnf(c_10,plain,
% 4.04/0.93      ( ~ m1_subset_1(X0,X1) | ~ v1_xboole_0(X1) | v1_xboole_0(X0) ),
% 4.04/0.93      inference(cnf_transformation,[],[f69]) ).
% 4.04/0.93  
% 4.04/0.93  cnf(c_1634,plain,
% 4.04/0.93      ( ~ m1_subset_1(sK7,X0) | ~ v1_xboole_0(X0) | v1_xboole_0(sK7) ),
% 4.04/0.93      inference(instantiation,[status(thm)],[c_10]) ).
% 4.04/0.93  
% 4.04/0.93  cnf(c_1874,plain,
% 4.04/0.93      ( ~ m1_subset_1(sK7,k1_zfmisc_1(u1_struct_0(sK6)))
% 4.04/0.93      | ~ v1_xboole_0(k1_zfmisc_1(u1_struct_0(sK6)))
% 4.04/0.93      | v1_xboole_0(sK7) ),
% 4.04/0.93      inference(instantiation,[status(thm)],[c_1634]) ).
% 4.04/0.93  
% 4.04/0.93  cnf(c_1875,plain,
% 4.04/0.93      ( m1_subset_1(sK7,k1_zfmisc_1(u1_struct_0(sK6))) != iProver_top
% 4.04/0.93      | v1_xboole_0(k1_zfmisc_1(u1_struct_0(sK6))) != iProver_top
% 4.04/0.93      | v1_xboole_0(sK7) = iProver_top ),
% 4.04/0.93      inference(predicate_to_equality,[status(thm)],[c_1874]) ).
% 4.04/0.93  
% 4.04/0.93  cnf(c_2143,plain,
% 4.04/0.93      ( r2_hidden(sK7,k1_zfmisc_1(u1_struct_0(sK6)))
% 4.04/0.93      | v1_xboole_0(k1_zfmisc_1(u1_struct_0(sK6))) ),
% 4.04/0.93      inference(resolution,[status(thm)],[c_12,c_29]) ).
% 4.04/0.93  
% 4.04/0.93  cnf(c_2144,plain,
% 4.04/0.93      ( r2_hidden(sK7,k1_zfmisc_1(u1_struct_0(sK6))) = iProver_top
% 4.04/0.93      | v1_xboole_0(k1_zfmisc_1(u1_struct_0(sK6))) = iProver_top ),
% 4.04/0.93      inference(predicate_to_equality,[status(thm)],[c_2143]) ).
% 4.04/0.93  
% 4.04/0.93  cnf(c_3168,plain,
% 4.04/0.93      ( r2_hidden(sK7,k1_zfmisc_1(u1_struct_0(sK6))) = iProver_top ),
% 4.04/0.93      inference(global_propositional_subsumption,
% 4.04/0.93                [status(thm)],
% 4.04/0.93                [c_2905,c_40,c_42,c_1875,c_2144]) ).
% 4.04/0.93  
% 4.04/0.93  cnf(c_8,plain,
% 4.04/0.93      ( r1_tarski(X0,X1) | ~ r2_hidden(X0,k1_zfmisc_1(X1)) ),
% 4.04/0.93      inference(cnf_transformation,[],[f95]) ).
% 4.04/0.93  
% 4.04/0.93  cnf(c_1304,plain,
% 4.04/0.93      ( r1_tarski(X0,X1) = iProver_top
% 4.04/0.93      | r2_hidden(X0,k1_zfmisc_1(X1)) != iProver_top ),
% 4.04/0.93      inference(predicate_to_equality,[status(thm)],[c_8]) ).
% 4.04/0.93  
% 4.04/0.93  cnf(c_3175,plain,
% 4.04/0.93      ( r1_tarski(sK7,u1_struct_0(sK6)) = iProver_top ),
% 4.04/0.93      inference(superposition,[status(thm)],[c_3168,c_1304]) ).
% 4.04/0.93  
% 4.04/0.93  cnf(c_4,plain,
% 4.04/0.93      ( ~ r1_tarski(X0,X1) | ~ r2_hidden(X2,X0) | r2_hidden(X2,X1) ),
% 4.04/0.93      inference(cnf_transformation,[],[f60]) ).
% 4.04/0.93  
% 4.04/0.93  cnf(c_1308,plain,
% 4.04/0.93      ( r1_tarski(X0,X1) != iProver_top
% 4.04/0.93      | r2_hidden(X2,X0) != iProver_top
% 4.04/0.93      | r2_hidden(X2,X1) = iProver_top ),
% 4.04/0.93      inference(predicate_to_equality,[status(thm)],[c_4]) ).
% 4.04/0.93  
% 4.04/0.93  cnf(c_3496,plain,
% 4.04/0.93      ( r2_hidden(X0,u1_struct_0(sK6)) = iProver_top
% 4.04/0.93      | r2_hidden(X0,sK7) != iProver_top ),
% 4.04/0.93      inference(superposition,[status(thm)],[c_3175,c_1308]) ).
% 4.04/0.93  
% 4.04/0.93  cnf(c_1311,plain,
% 4.04/0.93      ( r2_hidden(X0,X1) != iProver_top
% 4.04/0.93      | v1_xboole_0(X1) != iProver_top ),
% 4.04/0.93      inference(predicate_to_equality,[status(thm)],[c_1]) ).
% 4.04/0.93  
% 4.04/0.93  cnf(c_3937,plain,
% 4.04/0.93      ( r2_hidden(X0,sK7) != iProver_top
% 4.04/0.93      | v1_xboole_0(u1_struct_0(sK6)) != iProver_top ),
% 4.04/0.93      inference(superposition,[status(thm)],[c_3496,c_1311]) ).
% 4.04/0.93  
% 4.04/0.93  cnf(c_4298,plain,
% 4.04/0.93      ( v1_xboole_0(u1_struct_0(sK6)) != iProver_top
% 4.04/0.93      | v1_xboole_0(sK7) = iProver_top ),
% 4.04/0.93      inference(superposition,[status(thm)],[c_1312,c_3937]) ).
% 4.04/0.93  
% 4.04/0.93  cnf(c_4320,plain,
% 4.04/0.93      ( ~ v1_xboole_0(u1_struct_0(sK6)) | v1_xboole_0(sK7) ),
% 4.04/0.93      inference(predicate_to_equality_rev,[status(thm)],[c_4298]) ).
% 4.04/0.93  
% 4.04/0.93  cnf(c_8088,plain,
% 4.04/0.93      ( ~ r2_hidden(sK3(X1,u1_struct_0(sK6),X0),sK7)
% 4.04/0.93      | ~ r2_hidden(sK3(X1,u1_struct_0(sK6),X0),X0)
% 4.04/0.93      | ~ m1_subset_1(u1_struct_0(sK6),k1_zfmisc_1(X1))
% 4.04/0.93      | ~ m1_subset_1(X0,k1_zfmisc_1(X1))
% 4.04/0.93      | u1_struct_0(sK6) = X0 ),
% 4.04/0.93      inference(global_propositional_subsumption,
% 4.04/0.93                [status(thm)],
% 4.04/0.93                [c_8079,c_31,c_4320]) ).
% 4.04/0.93  
% 4.04/0.93  cnf(c_8089,plain,
% 4.04/0.93      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
% 4.04/0.93      | ~ m1_subset_1(u1_struct_0(sK6),k1_zfmisc_1(X1))
% 4.04/0.93      | ~ r2_hidden(sK3(X1,u1_struct_0(sK6),X0),X0)
% 4.04/0.93      | ~ r2_hidden(sK3(X1,u1_struct_0(sK6),X0),sK7)
% 4.04/0.93      | u1_struct_0(sK6) = X0 ),
% 4.04/0.93      inference(renaming,[status(thm)],[c_8088]) ).
% 4.04/0.93  
% 4.04/0.93  cnf(c_14,plain,
% 4.04/0.93      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
% 4.04/0.93      | ~ m1_subset_1(X2,k1_zfmisc_1(X1))
% 4.04/0.93      | r2_hidden(sK3(X1,X2,X0),X0)
% 4.04/0.93      | r2_hidden(sK3(X1,X2,X0),X2)
% 4.04/0.93      | X2 = X0 ),
% 4.04/0.93      inference(cnf_transformation,[],[f72]) ).
% 4.04/0.93  
% 4.04/0.93  cnf(c_8364,plain,
% 4.04/0.93      ( ~ m1_subset_1(u1_struct_0(sK6),k1_zfmisc_1(X0))
% 4.04/0.93      | ~ m1_subset_1(sK7,k1_zfmisc_1(X0))
% 4.04/0.93      | r2_hidden(sK3(X0,u1_struct_0(sK6),sK7),u1_struct_0(sK6))
% 4.04/0.93      | ~ r2_hidden(sK3(X0,u1_struct_0(sK6),sK7),sK7)
% 4.04/0.93      | u1_struct_0(sK6) = sK7 ),
% 4.04/0.93      inference(resolution,[status(thm)],[c_8089,c_14]) ).
% 4.04/0.93  
% 4.04/0.93  cnf(c_8374,plain,
% 4.04/0.93      ( ~ m1_subset_1(u1_struct_0(sK6),k1_zfmisc_1(X0))
% 4.04/0.93      | ~ m1_subset_1(sK7,k1_zfmisc_1(X0))
% 4.04/0.93      | ~ r2_hidden(sK3(X0,u1_struct_0(sK6),sK7),sK7)
% 4.04/0.93      | u1_struct_0(sK6) = sK7 ),
% 4.04/0.93      inference(forward_subsumption_resolution,
% 4.04/0.93                [status(thm)],
% 4.04/0.93                [c_8364,c_13]) ).
% 4.04/0.93  
% 4.04/0.93  cnf(c_8393,plain,
% 4.04/0.93      ( ~ m1_subset_1(u1_struct_0(sK6),k1_zfmisc_1(X0))
% 4.04/0.93      | ~ m1_subset_1(sK7,k1_zfmisc_1(X0))
% 4.04/0.93      | r2_hidden(sK3(X0,u1_struct_0(sK6),sK7),u1_struct_0(sK6))
% 4.04/0.93      | u1_struct_0(sK6) = sK7 ),
% 4.04/0.93      inference(resolution,[status(thm)],[c_8374,c_14]) ).
% 4.04/0.93  
% 4.04/0.93  cnf(c_8634,plain,
% 4.04/0.93      ( ~ m1_subset_1(u1_struct_0(sK6),k1_zfmisc_1(X0))
% 4.04/0.93      | ~ m1_subset_1(sK7,k1_zfmisc_1(X0))
% 4.04/0.93      | ~ r1_tarski(u1_struct_0(sK6),X1)
% 4.04/0.93      | r2_hidden(sK3(X0,u1_struct_0(sK6),sK7),X1)
% 4.04/0.93      | u1_struct_0(sK6) = sK7 ),
% 4.04/0.93      inference(resolution,[status(thm)],[c_8393,c_4]) ).
% 4.04/0.93  
% 4.04/0.93  cnf(c_8854,plain,
% 4.04/0.93      ( ~ m1_subset_1(u1_struct_0(sK6),k1_zfmisc_1(X0))
% 4.04/0.93      | ~ m1_subset_1(sK7,k1_zfmisc_1(X0))
% 4.04/0.93      | ~ r1_tarski(u1_struct_0(sK6),sK7)
% 4.04/0.93      | u1_struct_0(sK6) = sK7 ),
% 4.04/0.93      inference(resolution,[status(thm)],[c_8634,c_8374]) ).
% 4.04/0.93  
% 4.04/0.93  cnf(c_11279,plain,
% 4.04/0.93      ( ~ m1_subset_1(sK7,k1_zfmisc_1(X0))
% 4.04/0.93      | ~ r1_tarski(u1_struct_0(sK6),sK7)
% 4.04/0.93      | ~ r2_hidden(u1_struct_0(sK6),k1_zfmisc_1(X0))
% 4.04/0.93      | u1_struct_0(sK6) = sK7 ),
% 4.04/0.93      inference(resolution,[status(thm)],[c_8854,c_355]) ).
% 4.04/0.93  
% 4.04/0.93  cnf(c_14263,plain,
% 4.04/0.93      ( ~ m1_subset_1(sK7,k1_zfmisc_1(X0))
% 4.04/0.93      | ~ r2_hidden(u1_struct_0(sK6),k1_zfmisc_1(X0))
% 4.04/0.93      | u1_struct_0(sK6) = sK7 ),
% 4.04/0.93      inference(global_propositional_subsumption,
% 4.04/0.93                [status(thm)],
% 4.04/0.93                [c_11279,c_12254]) ).
% 4.04/0.93  
% 4.04/0.93  cnf(c_2701,plain,
% 4.04/0.93      ( ~ r1_tarski(X0,X1)
% 4.04/0.93      | ~ r1_tarski(k1_zfmisc_1(X1),X2)
% 4.04/0.93      | r2_hidden(X0,X2) ),
% 4.04/0.93      inference(resolution,[status(thm)],[c_4,c_7]) ).
% 4.04/0.93  
% 4.04/0.93  cnf(c_2699,plain,
% 4.04/0.93      ( ~ r1_tarski(X0,X1)
% 4.04/0.93      | r1_tarski(X0,X2)
% 4.04/0.93      | r2_hidden(sK1(X0,X2),X1) ),
% 4.04/0.93      inference(resolution,[status(thm)],[c_4,c_3]) ).
% 4.04/0.93  
% 4.04/0.93  cnf(c_3050,plain,
% 4.04/0.93      ( r1_tarski(X0,u1_struct_0(sK6))
% 4.04/0.93      | ~ r2_hidden(sK1(X0,u1_struct_0(sK6)),sK7)
% 4.04/0.93      | v1_xboole_0(u1_struct_0(sK6)) ),
% 4.04/0.93      inference(resolution,[status(thm)],[c_3038,c_2]) ).
% 4.04/0.93  
% 4.04/0.93  cnf(c_3251,plain,
% 4.04/0.93      ( r1_tarski(X0,u1_struct_0(sK6))
% 4.04/0.93      | ~ r1_tarski(X0,sK7)
% 4.04/0.93      | v1_xboole_0(u1_struct_0(sK6)) ),
% 4.04/0.93      inference(resolution,[status(thm)],[c_2699,c_3050]) ).
% 4.04/0.93  
% 4.04/0.93  cnf(c_2125,plain,
% 4.04/0.93      ( r1_tarski(X0,k1_zfmisc_1(X1))
% 4.04/0.93      | ~ r1_tarski(sK1(X0,k1_zfmisc_1(X1)),X1) ),
% 4.04/0.93      inference(resolution,[status(thm)],[c_7,c_2]) ).
% 4.04/0.93  
% 4.04/0.93  cnf(c_3263,plain,
% 4.04/0.93      ( r1_tarski(X0,k1_zfmisc_1(u1_struct_0(sK6)))
% 4.04/0.93      | ~ r1_tarski(sK1(X0,k1_zfmisc_1(u1_struct_0(sK6))),sK7)
% 4.04/0.93      | v1_xboole_0(u1_struct_0(sK6)) ),
% 4.04/0.93      inference(resolution,[status(thm)],[c_3251,c_2125]) ).
% 4.04/0.93  
% 4.04/0.93  cnf(c_1762,plain,
% 4.04/0.93      ( r1_tarski(sK1(k1_zfmisc_1(X0),X1),X0)
% 4.04/0.93      | r1_tarski(k1_zfmisc_1(X0),X1) ),
% 4.04/0.93      inference(resolution,[status(thm)],[c_8,c_3]) ).
% 4.04/0.93  
% 4.04/0.93  cnf(c_3535,plain,
% 4.04/0.93      ( r1_tarski(k1_zfmisc_1(sK7),k1_zfmisc_1(u1_struct_0(sK6)))
% 4.04/0.93      | v1_xboole_0(u1_struct_0(sK6)) ),
% 4.04/0.93      inference(resolution,[status(thm)],[c_3263,c_1762]) ).
% 4.04/0.93  
% 4.04/0.93  cnf(c_4340,plain,
% 4.04/0.93      ( ~ r1_tarski(X0,sK7)
% 4.04/0.93      | r2_hidden(X0,k1_zfmisc_1(u1_struct_0(sK6)))
% 4.04/0.93      | v1_xboole_0(u1_struct_0(sK6)) ),
% 4.04/0.93      inference(resolution,[status(thm)],[c_2701,c_3535]) ).
% 4.04/0.93  
% 4.04/0.93  cnf(c_4587,plain,
% 4.04/0.93      ( r2_hidden(X0,k1_zfmisc_1(u1_struct_0(sK6)))
% 4.04/0.93      | ~ r1_tarski(X0,sK7) ),
% 4.04/0.93      inference(global_propositional_subsumption,
% 4.04/0.93                [status(thm)],
% 4.04/0.93                [c_4340,c_31,c_4320]) ).
% 4.04/0.93  
% 4.04/0.93  cnf(c_4588,plain,
% 4.04/0.93      ( ~ r1_tarski(X0,sK7)
% 4.04/0.93      | r2_hidden(X0,k1_zfmisc_1(u1_struct_0(sK6))) ),
% 4.04/0.93      inference(renaming,[status(thm)],[c_4587]) ).
% 4.04/0.93  
% 4.04/0.93  cnf(c_14609,plain,
% 4.04/0.93      ( ~ m1_subset_1(sK7,k1_zfmisc_1(u1_struct_0(sK6)))
% 4.04/0.93      | ~ r1_tarski(u1_struct_0(sK6),sK7)
% 4.04/0.93      | u1_struct_0(sK6) = sK7 ),
% 4.04/0.93      inference(resolution,[status(thm)],[c_14263,c_4588]) ).
% 4.04/0.93  
% 4.04/0.93  cnf(c_14841,plain,
% 4.04/0.93      ( u1_struct_0(sK6) = sK7 ),
% 4.04/0.93      inference(global_propositional_subsumption,
% 4.04/0.93                [status(thm)],
% 4.04/0.93                [c_11917,c_29,c_12254,c_14609]) ).
% 4.04/0.93  
% 4.04/0.93  cnf(c_17,plain,
% 4.04/0.93      ( m1_subset_1(k3_yellow_0(X0),u1_struct_0(X0))
% 4.04/0.93      | ~ l1_orders_2(X0) ),
% 4.04/0.93      inference(cnf_transformation,[],[f75]) ).
% 4.04/0.93  
% 4.04/0.93  cnf(c_1296,plain,
% 4.04/0.93      ( m1_subset_1(k3_yellow_0(X0),u1_struct_0(X0)) = iProver_top
% 4.04/0.93      | l1_orders_2(X0) != iProver_top ),
% 4.04/0.93      inference(predicate_to_equality,[status(thm)],[c_17]) ).
% 4.04/0.93  
% 4.04/0.93  cnf(c_2904,plain,
% 4.04/0.93      ( r2_hidden(k3_yellow_0(X0),u1_struct_0(X0)) = iProver_top
% 4.04/0.93      | l1_orders_2(X0) != iProver_top
% 4.04/0.93      | v1_xboole_0(u1_struct_0(X0)) = iProver_top ),
% 4.04/0.93      inference(superposition,[status(thm)],[c_1296,c_1301]) ).
% 4.04/0.93  
% 4.04/0.93  cnf(c_15065,plain,
% 4.04/0.93      ( r2_hidden(k3_yellow_0(sK6),sK7) = iProver_top
% 4.04/0.93      | l1_orders_2(sK6) != iProver_top
% 4.04/0.93      | v1_xboole_0(u1_struct_0(sK6)) = iProver_top ),
% 4.04/0.93      inference(superposition,[status(thm)],[c_14841,c_2904]) ).
% 4.04/0.93  
% 4.04/0.93  cnf(c_15136,plain,
% 4.04/0.93      ( r2_hidden(k3_yellow_0(sK6),sK7) = iProver_top
% 4.04/0.93      | l1_orders_2(sK6) != iProver_top
% 4.04/0.93      | v1_xboole_0(sK7) = iProver_top ),
% 4.04/0.93      inference(light_normalisation,[status(thm)],[c_15065,c_14841]) ).
% 4.04/0.93  
% 4.04/0.93  cnf(c_14871,plain,
% 4.04/0.93      ( r2_hidden(sK7,k1_zfmisc_1(sK7)) = iProver_top ),
% 4.04/0.93      inference(demodulation,[status(thm)],[c_14841,c_3168]) ).
% 4.04/0.93  
% 4.04/0.93  cnf(c_26,plain,
% 4.04/0.93      ( ~ v1_subset_1(X0,X0) | ~ m1_subset_1(X0,k1_zfmisc_1(X0)) ),
% 4.04/0.93      inference(cnf_transformation,[],[f96]) ).
% 4.04/0.93  
% 4.04/0.93  cnf(c_11745,plain,
% 4.04/0.93      ( ~ v1_subset_1(sK7,sK7) | ~ m1_subset_1(sK7,k1_zfmisc_1(sK7)) ),
% 4.04/0.93      inference(instantiation,[status(thm)],[c_26]) ).
% 4.04/0.93  
% 4.04/0.93  cnf(c_11748,plain,
% 4.04/0.93      ( v1_subset_1(sK7,sK7) != iProver_top
% 4.04/0.93      | m1_subset_1(sK7,k1_zfmisc_1(sK7)) != iProver_top ),
% 4.04/0.93      inference(predicate_to_equality,[status(thm)],[c_11745]) ).
% 4.04/0.93  
% 4.04/0.93  cnf(c_431,plain,
% 4.04/0.93      ( ~ v1_subset_1(X0,X1) | v1_subset_1(X2,X3) | X2 != X0 | X3 != X1 ),
% 4.04/0.93      theory(equality) ).
% 4.04/0.93  
% 4.04/0.93  cnf(c_2981,plain,
% 4.04/0.93      ( v1_subset_1(X0,X1)
% 4.04/0.93      | ~ v1_subset_1(sK7,u1_struct_0(sK6))
% 4.04/0.93      | X1 != u1_struct_0(sK6)
% 4.04/0.93      | X0 != sK7 ),
% 4.04/0.93      inference(instantiation,[status(thm)],[c_431]) ).
% 4.04/0.93  
% 4.04/0.93  cnf(c_5276,plain,
% 4.04/0.93      ( v1_subset_1(X0,sK7)
% 4.04/0.93      | ~ v1_subset_1(sK7,u1_struct_0(sK6))
% 4.04/0.93      | X0 != sK7
% 4.04/0.93      | sK7 != u1_struct_0(sK6) ),
% 4.04/0.93      inference(instantiation,[status(thm)],[c_2981]) ).
% 4.04/0.93  
% 4.04/0.93  cnf(c_11744,plain,
% 4.04/0.93      ( ~ v1_subset_1(sK7,u1_struct_0(sK6))
% 4.04/0.93      | v1_subset_1(sK7,sK7)
% 4.04/0.93      | sK7 != u1_struct_0(sK6)
% 4.04/0.93      | sK7 != sK7 ),
% 4.04/0.93      inference(instantiation,[status(thm)],[c_5276]) ).
% 4.04/0.93  
% 4.04/0.93  cnf(c_11746,plain,
% 4.04/0.93      ( sK7 != u1_struct_0(sK6)
% 4.04/0.93      | sK7 != sK7
% 4.04/0.93      | v1_subset_1(sK7,u1_struct_0(sK6)) != iProver_top
% 4.04/0.93      | v1_subset_1(sK7,sK7) = iProver_top ),
% 4.04/0.93      inference(predicate_to_equality,[status(thm)],[c_11744]) ).
% 4.04/0.93  
% 4.04/0.93  cnf(c_417,plain,( X0 != X1 | X2 != X1 | X2 = X0 ),theory(equality) ).
% 4.04/0.93  
% 4.04/0.93  cnf(c_1882,plain,
% 4.04/0.93      ( X0 != X1 | sK7 != X1 | sK7 = X0 ),
% 4.04/0.93      inference(instantiation,[status(thm)],[c_417]) ).
% 4.04/0.93  
% 4.04/0.93  cnf(c_2219,plain,
% 4.04/0.93      ( X0 != sK7 | sK7 = X0 | sK7 != sK7 ),
% 4.04/0.93      inference(instantiation,[status(thm)],[c_1882]) ).
% 4.04/0.93  
% 4.04/0.93  cnf(c_5277,plain,
% 4.04/0.93      ( u1_struct_0(sK6) != sK7 | sK7 = u1_struct_0(sK6) | sK7 != sK7 ),
% 4.04/0.93      inference(instantiation,[status(thm)],[c_2219]) ).
% 4.04/0.93  
% 4.04/0.93  cnf(c_2162,plain,
% 4.04/0.93      ( m1_subset_1(X0,k1_zfmisc_1(sK7))
% 4.04/0.93      | ~ r2_hidden(X0,k1_zfmisc_1(sK7)) ),
% 4.04/0.93      inference(instantiation,[status(thm)],[c_355]) ).
% 4.04/0.93  
% 4.04/0.93  cnf(c_3317,plain,
% 4.04/0.93      ( m1_subset_1(sK7,k1_zfmisc_1(sK7))
% 4.04/0.93      | ~ r2_hidden(sK7,k1_zfmisc_1(sK7)) ),
% 4.04/0.93      inference(instantiation,[status(thm)],[c_2162]) ).
% 4.04/0.93  
% 4.04/0.93  cnf(c_3319,plain,
% 4.04/0.93      ( m1_subset_1(sK7,k1_zfmisc_1(sK7)) = iProver_top
% 4.04/0.93      | r2_hidden(sK7,k1_zfmisc_1(sK7)) != iProver_top ),
% 4.04/0.93      inference(predicate_to_equality,[status(thm)],[c_3317]) ).
% 4.04/0.93  
% 4.04/0.93  cnf(c_416,plain,( X0 = X0 ),theory(equality) ).
% 4.04/0.93  
% 4.04/0.93  cnf(c_1958,plain,
% 4.04/0.93      ( sK7 = sK7 ),
% 4.04/0.93      inference(instantiation,[status(thm)],[c_416]) ).
% 4.04/0.93  
% 4.04/0.93  cnf(c_28,negated_conjecture,
% 4.04/0.93      ( v1_subset_1(sK7,u1_struct_0(sK6))
% 4.04/0.93      | ~ r2_hidden(k3_yellow_0(sK6),sK7) ),
% 4.04/0.93      inference(cnf_transformation,[],[f92]) ).
% 4.04/0.93  
% 4.04/0.93  cnf(c_43,plain,
% 4.04/0.93      ( v1_subset_1(sK7,u1_struct_0(sK6)) = iProver_top
% 4.04/0.93      | r2_hidden(k3_yellow_0(sK6),sK7) != iProver_top ),
% 4.04/0.93      inference(predicate_to_equality,[status(thm)],[c_28]) ).
% 4.04/0.93  
% 4.04/0.93  cnf(contradiction,plain,
% 4.04/0.93      ( $false ),
% 4.04/0.93      inference(minisat,
% 4.04/0.93                [status(thm)],
% 4.04/0.93                [c_15136,c_14871,c_14841,c_11748,c_11746,c_5277,c_3319,
% 4.04/0.93                 c_1958,c_43,c_40,c_39]) ).
% 4.04/0.93  
% 4.04/0.93  
% 4.04/0.93  % SZS output end CNFRefutation for theBenchmark.p
% 4.04/0.93  
% 4.04/0.93  ------                               Statistics
% 4.04/0.93  
% 4.04/0.93  ------ Selected
% 4.04/0.93  
% 4.04/0.93  total_time:                             0.41
% 4.04/0.93  
%------------------------------------------------------------------------------
