%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n003.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:28:26 EST 2020

% Result     : Theorem 3.22s
% Output     : CNFRefutation 3.22s
% Verified   : 
% Statistics : Number of formulae       :  205 (1778 expanded)
%              Number of clauses        :  120 ( 453 expanded)
%              Number of leaves         :   20 ( 368 expanded)
%              Depth                    :   24
%              Number of atoms          :  765 (15121 expanded)
%              Number of equality atoms :  169 ( 527 expanded)
%              Maximal formula depth    :   14 (   5 average)
%              Maximal clause size      :   26 (   3 average)
%              Maximal term depth       :    5 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f15,conjecture,(
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

fof(f16,negated_conjecture,(
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
    inference(negated_conjecture,[],[f15])).

fof(f17,plain,(
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
    inference(pure_predicate_removal,[],[f16])).

fof(f37,plain,(
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
      & v4_orders_2(X0)
      & v3_orders_2(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f17])).

fof(f38,plain,(
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
      & v4_orders_2(X0)
      & v3_orders_2(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(flattening,[],[f37])).

fof(f50,plain,(
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
      & v4_orders_2(X0)
      & v3_orders_2(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(nnf_transformation,[],[f38])).

fof(f51,plain,(
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
      & v4_orders_2(X0)
      & v3_orders_2(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(flattening,[],[f50])).

fof(f53,plain,(
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

fof(f52,plain,
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
        & v4_orders_2(X0)
        & v3_orders_2(X0)
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
      & v4_orders_2(sK3)
      & v3_orders_2(sK3)
      & ~ v2_struct_0(sK3) ) ),
    introduced(choice_axiom,[])).

fof(f54,plain,
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
    & v4_orders_2(sK3)
    & v3_orders_2(sK3)
    & ~ v2_struct_0(sK3) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3,sK4])],[f51,f53,f52])).

fof(f88,plain,(
    m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(sK3))) ),
    inference(cnf_transformation,[],[f54])).

fof(f5,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f43,plain,(
    ! [X0,X1] :
      ( ( m1_subset_1(X0,k1_zfmisc_1(X1))
        | ~ r1_tarski(X0,X1) )
      & ( r1_tarski(X0,X1)
        | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ) ) ),
    inference(nnf_transformation,[],[f5])).

fof(f62,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ) ),
    inference(cnf_transformation,[],[f43])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => ( ! [X2] :
            ( m1_subset_1(X2,X0)
           => r2_hidden(X2,X1) )
       => X0 = X1 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f19,plain,(
    ! [X0,X1] :
      ( X0 = X1
      | ? [X2] :
          ( ~ r2_hidden(X2,X1)
          & m1_subset_1(X2,X0) )
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f20,plain,(
    ! [X0,X1] :
      ( X0 = X1
      | ? [X2] :
          ( ~ r2_hidden(X2,X1)
          & m1_subset_1(X2,X0) )
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(flattening,[],[f19])).

fof(f41,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ~ r2_hidden(X2,X1)
          & m1_subset_1(X2,X0) )
     => ( ~ r2_hidden(sK0(X0,X1),X1)
        & m1_subset_1(sK0(X0,X1),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f42,plain,(
    ! [X0,X1] :
      ( X0 = X1
      | ( ~ r2_hidden(sK0(X0,X1),X1)
        & m1_subset_1(sK0(X0,X1),X0) )
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f20,f41])).

fof(f59,plain,(
    ! [X0,X1] :
      ( X0 = X1
      | m1_subset_1(sK0(X0,X1),X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f42])).

fof(f63,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f43])).

fof(f13,axiom,(
    ! [X0] :
      ( ( l1_orders_2(X0)
        & v5_orders_2(X0)
        & v4_orders_2(X0)
        & v3_orders_2(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,u1_struct_0(X0))
         => ( k1_yellow_0(X0,k5_waybel_0(X0,X1)) = X1
            & r1_yellow_0(X0,k5_waybel_0(X0,X1)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f34,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( k1_yellow_0(X0,k5_waybel_0(X0,X1)) = X1
            & r1_yellow_0(X0,k5_waybel_0(X0,X1)) )
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l1_orders_2(X0)
      | ~ v5_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f35,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( k1_yellow_0(X0,k5_waybel_0(X0,X1)) = X1
            & r1_yellow_0(X0,k5_waybel_0(X0,X1)) )
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l1_orders_2(X0)
      | ~ v5_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f34])).

fof(f77,plain,(
    ! [X0,X1] :
      ( k1_yellow_0(X0,k5_waybel_0(X0,X1)) = X1
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | ~ v5_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f35])).

fof(f83,plain,(
    v5_orders_2(sK3) ),
    inference(cnf_transformation,[],[f54])).

fof(f80,plain,(
    ~ v2_struct_0(sK3) ),
    inference(cnf_transformation,[],[f54])).

fof(f81,plain,(
    v3_orders_2(sK3) ),
    inference(cnf_transformation,[],[f54])).

fof(f82,plain,(
    v4_orders_2(sK3) ),
    inference(cnf_transformation,[],[f54])).

fof(f85,plain,(
    l1_orders_2(sK3) ),
    inference(cnf_transformation,[],[f54])).

fof(f8,axiom,(
    ! [X0,X1] :
      ( l1_orders_2(X0)
     => m1_subset_1(k1_yellow_0(X0,X1),u1_struct_0(X0)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f26,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k1_yellow_0(X0,X1),u1_struct_0(X0))
      | ~ l1_orders_2(X0) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f66,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k1_yellow_0(X0,X1),u1_struct_0(X0))
      | ~ l1_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f14,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => ( v1_subset_1(X1,X0)
      <=> X0 != X1 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f36,plain,(
    ! [X0,X1] :
      ( ( v1_subset_1(X1,X0)
      <=> X0 != X1 )
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f49,plain,(
    ! [X0,X1] :
      ( ( ( v1_subset_1(X1,X0)
          | X0 = X1 )
        & ( X0 != X1
          | ~ v1_subset_1(X1,X0) ) )
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(nnf_transformation,[],[f36])).

fof(f79,plain,(
    ! [X0,X1] :
      ( v1_subset_1(X1,X0)
      | X0 = X1
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f49])).

fof(f90,plain,
    ( r2_hidden(k3_yellow_0(sK3),sK4)
    | ~ v1_subset_1(sK4,u1_struct_0(sK3)) ),
    inference(cnf_transformation,[],[f54])).

fof(f78,plain,(
    ! [X0,X1] :
      ( X0 != X1
      | ~ v1_subset_1(X1,X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f49])).

fof(f93,plain,(
    ! [X1] :
      ( ~ v1_subset_1(X1,X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X1)) ) ),
    inference(equality_resolution,[],[f78])).

fof(f89,plain,
    ( ~ r2_hidden(k3_yellow_0(sK3),sK4)
    | v1_subset_1(sK4,u1_struct_0(sK3)) ),
    inference(cnf_transformation,[],[f54])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( X0 = X1
    <=> ( r1_tarski(X1,X0)
        & r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f39,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(nnf_transformation,[],[f1])).

fof(f40,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(flattening,[],[f39])).

fof(f56,plain,(
    ! [X0,X1] :
      ( r1_tarski(X1,X0)
      | X0 != X1 ) ),
    inference(cnf_transformation,[],[f40])).

fof(f91,plain,(
    ! [X1] : r1_tarski(X1,X1) ),
    inference(equality_resolution,[],[f56])).

fof(f60,plain,(
    ! [X0,X1] :
      ( X0 = X1
      | ~ r2_hidden(sK0(X0,X1),X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f42])).

fof(f7,axiom,(
    ! [X0] :
      ( l1_orders_2(X0)
     => k3_yellow_0(X0) = k1_yellow_0(X0,k1_xboole_0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f25,plain,(
    ! [X0] :
      ( k3_yellow_0(X0) = k1_yellow_0(X0,k1_xboole_0)
      | ~ l1_orders_2(X0) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f65,plain,(
    ! [X0] :
      ( k3_yellow_0(X0) = k1_yellow_0(X0,k1_xboole_0)
      | ~ l1_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f10,axiom,(
    ! [X0] :
      ( l1_orders_2(X0)
     => ! [X1,X2] :
          ( ( r1_yellow_0(X0,X2)
            & r1_yellow_0(X0,X1)
            & r1_tarski(X1,X2) )
         => r1_orders_2(X0,k1_yellow_0(X0,X1),k1_yellow_0(X0,X2)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f28,plain,(
    ! [X0] :
      ( ! [X1,X2] :
          ( r1_orders_2(X0,k1_yellow_0(X0,X1),k1_yellow_0(X0,X2))
          | ~ r1_yellow_0(X0,X2)
          | ~ r1_yellow_0(X0,X1)
          | ~ r1_tarski(X1,X2) )
      | ~ l1_orders_2(X0) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f29,plain,(
    ! [X0] :
      ( ! [X1,X2] :
          ( r1_orders_2(X0,k1_yellow_0(X0,X1),k1_yellow_0(X0,X2))
          | ~ r1_yellow_0(X0,X2)
          | ~ r1_yellow_0(X0,X1)
          | ~ r1_tarski(X1,X2) )
      | ~ l1_orders_2(X0) ) ),
    inference(flattening,[],[f28])).

fof(f68,plain,(
    ! [X2,X0,X1] :
      ( r1_orders_2(X0,k1_yellow_0(X0,X1),k1_yellow_0(X0,X2))
      | ~ r1_yellow_0(X0,X2)
      | ~ r1_yellow_0(X0,X1)
      | ~ r1_tarski(X1,X2)
      | ~ l1_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f84,plain,(
    v1_yellow_0(sK3) ),
    inference(cnf_transformation,[],[f54])).

fof(f11,axiom,(
    ! [X0] :
      ( ( l1_orders_2(X0)
        & v1_yellow_0(X0)
        & v5_orders_2(X0)
        & ~ v2_struct_0(X0) )
     => ( r2_yellow_0(X0,u1_struct_0(X0))
        & r1_yellow_0(X0,k1_xboole_0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f18,plain,(
    ! [X0] :
      ( ( l1_orders_2(X0)
        & v1_yellow_0(X0)
        & v5_orders_2(X0)
        & ~ v2_struct_0(X0) )
     => r1_yellow_0(X0,k1_xboole_0) ) ),
    inference(pure_predicate_removal,[],[f11])).

fof(f30,plain,(
    ! [X0] :
      ( r1_yellow_0(X0,k1_xboole_0)
      | ~ l1_orders_2(X0)
      | ~ v1_yellow_0(X0)
      | ~ v5_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f18])).

fof(f31,plain,(
    ! [X0] :
      ( r1_yellow_0(X0,k1_xboole_0)
      | ~ l1_orders_2(X0)
      | ~ v1_yellow_0(X0)
      | ~ v5_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f30])).

fof(f69,plain,(
    ! [X0] :
      ( r1_yellow_0(X0,k1_xboole_0)
      | ~ l1_orders_2(X0)
      | ~ v1_yellow_0(X0)
      | ~ v5_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f2,axiom,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f58,plain,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    inference(cnf_transformation,[],[f2])).

fof(f76,plain,(
    ! [X0,X1] :
      ( r1_yellow_0(X0,k5_waybel_0(X0,X1))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | ~ v5_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f35])).

fof(f12,axiom,(
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

fof(f32,plain,(
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
    inference(ennf_transformation,[],[f12])).

fof(f33,plain,(
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
    inference(flattening,[],[f32])).

fof(f44,plain,(
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
    inference(nnf_transformation,[],[f33])).

fof(f45,plain,(
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
    inference(rectify,[],[f44])).

fof(f47,plain,(
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

fof(f46,plain,(
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

fof(f48,plain,(
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
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1,sK2])],[f45,f47,f46])).

fof(f70,plain,(
    ! [X4,X0,X5,X1] :
      ( r2_hidden(X5,X1)
      | ~ r1_orders_2(X0,X4,X5)
      | ~ r2_hidden(X4,X1)
      | ~ m1_subset_1(X5,u1_struct_0(X0))
      | ~ m1_subset_1(X4,u1_struct_0(X0))
      | ~ v13_waybel_0(X1,X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f48])).

fof(f6,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(X2))
        & r2_hidden(X0,X1) )
     => m1_subset_1(X0,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f23,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X0,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f24,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X0,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(flattening,[],[f23])).

fof(f64,plain,(
    ! [X2,X0,X1] :
      ( m1_subset_1(X0,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f87,plain,(
    v13_waybel_0(sK4,sK3) ),
    inference(cnf_transformation,[],[f54])).

fof(f9,axiom,(
    ! [X0] :
      ( l1_orders_2(X0)
     => m1_subset_1(k3_yellow_0(X0),u1_struct_0(X0)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f27,plain,(
    ! [X0] :
      ( m1_subset_1(k3_yellow_0(X0),u1_struct_0(X0))
      | ~ l1_orders_2(X0) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f67,plain,(
    ! [X0] :
      ( m1_subset_1(k3_yellow_0(X0),u1_struct_0(X0))
      | ~ l1_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,X1)
     => ( r2_hidden(X0,X1)
        | v1_xboole_0(X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f21,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
      | v1_xboole_0(X1)
      | ~ m1_subset_1(X0,X1) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f22,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
      | v1_xboole_0(X1)
      | ~ m1_subset_1(X0,X1) ) ),
    inference(flattening,[],[f21])).

fof(f61,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
      | v1_xboole_0(X1)
      | ~ m1_subset_1(X0,X1) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f86,plain,(
    ~ v1_xboole_0(sK4) ),
    inference(cnf_transformation,[],[f54])).

cnf(c_27,negated_conjecture,
    ( m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(sK3))) ),
    inference(cnf_transformation,[],[f88])).

cnf(c_2174,plain,
    ( m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(sK3))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_27])).

cnf(c_8,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | r1_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f62])).

cnf(c_2176,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(X1)) != iProver_top
    | r1_tarski(X0,X1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_8])).

cnf(c_2688,plain,
    ( r1_tarski(sK4,u1_struct_0(sK3)) = iProver_top ),
    inference(superposition,[status(thm)],[c_2174,c_2176])).

cnf(c_5,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | m1_subset_1(sK0(X1,X0),X1)
    | X0 = X1 ),
    inference(cnf_transformation,[],[f59])).

cnf(c_7,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(X1))
    | ~ r1_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f63])).

cnf(c_271,plain,
    ( ~ r1_tarski(X0,X1)
    | m1_subset_1(X0,k1_zfmisc_1(X1)) ),
    inference(prop_impl,[status(thm)],[c_7])).

cnf(c_272,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(X1))
    | ~ r1_tarski(X0,X1) ),
    inference(renaming,[status(thm)],[c_271])).

cnf(c_348,plain,
    ( m1_subset_1(sK0(X0,X1),X0)
    | ~ r1_tarski(X1,X0)
    | X1 = X0 ),
    inference(bin_hyper_res,[status(thm)],[c_5,c_272])).

cnf(c_2171,plain,
    ( X0 = X1
    | m1_subset_1(sK0(X1,X0),X1) = iProver_top
    | r1_tarski(X0,X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_348])).

cnf(c_21,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(X1))
    | ~ v3_orders_2(X1)
    | ~ v4_orders_2(X1)
    | v2_struct_0(X1)
    | ~ v5_orders_2(X1)
    | ~ l1_orders_2(X1)
    | k1_yellow_0(X1,k5_waybel_0(X1,X0)) = X0 ),
    inference(cnf_transformation,[],[f77])).

cnf(c_32,negated_conjecture,
    ( v5_orders_2(sK3) ),
    inference(cnf_transformation,[],[f83])).

cnf(c_563,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(X1))
    | ~ v3_orders_2(X1)
    | ~ v4_orders_2(X1)
    | v2_struct_0(X1)
    | ~ l1_orders_2(X1)
    | k1_yellow_0(X1,k5_waybel_0(X1,X0)) = X0
    | sK3 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_21,c_32])).

cnf(c_564,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(sK3))
    | ~ v3_orders_2(sK3)
    | ~ v4_orders_2(sK3)
    | v2_struct_0(sK3)
    | ~ l1_orders_2(sK3)
    | k1_yellow_0(sK3,k5_waybel_0(sK3,X0)) = X0 ),
    inference(unflattening,[status(thm)],[c_563])).

cnf(c_35,negated_conjecture,
    ( ~ v2_struct_0(sK3) ),
    inference(cnf_transformation,[],[f80])).

cnf(c_34,negated_conjecture,
    ( v3_orders_2(sK3) ),
    inference(cnf_transformation,[],[f81])).

cnf(c_33,negated_conjecture,
    ( v4_orders_2(sK3) ),
    inference(cnf_transformation,[],[f82])).

cnf(c_30,negated_conjecture,
    ( l1_orders_2(sK3) ),
    inference(cnf_transformation,[],[f85])).

cnf(c_568,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(sK3))
    | k1_yellow_0(sK3,k5_waybel_0(sK3,X0)) = X0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_564,c_35,c_34,c_33,c_30])).

cnf(c_2165,plain,
    ( k1_yellow_0(sK3,k5_waybel_0(sK3,X0)) = X0
    | m1_subset_1(X0,u1_struct_0(sK3)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_568])).

cnf(c_4102,plain,
    ( k1_yellow_0(sK3,k5_waybel_0(sK3,sK0(u1_struct_0(sK3),X0))) = sK0(u1_struct_0(sK3),X0)
    | u1_struct_0(sK3) = X0
    | r1_tarski(X0,u1_struct_0(sK3)) != iProver_top ),
    inference(superposition,[status(thm)],[c_2171,c_2165])).

cnf(c_6958,plain,
    ( k1_yellow_0(sK3,k5_waybel_0(sK3,sK0(u1_struct_0(sK3),sK4))) = sK0(u1_struct_0(sK3),sK4)
    | u1_struct_0(sK3) = sK4 ),
    inference(superposition,[status(thm)],[c_2688,c_4102])).

cnf(c_11,plain,
    ( m1_subset_1(k1_yellow_0(X0,X1),u1_struct_0(X0))
    | ~ l1_orders_2(X0) ),
    inference(cnf_transformation,[],[f66])).

cnf(c_730,plain,
    ( m1_subset_1(k1_yellow_0(X0,X1),u1_struct_0(X0))
    | sK3 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_11,c_30])).

cnf(c_731,plain,
    ( m1_subset_1(k1_yellow_0(sK3,X0),u1_struct_0(sK3)) ),
    inference(unflattening,[status(thm)],[c_730])).

cnf(c_2160,plain,
    ( m1_subset_1(k1_yellow_0(sK3,X0),u1_struct_0(sK3)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_731])).

cnf(c_7115,plain,
    ( u1_struct_0(sK3) = sK4
    | m1_subset_1(sK0(u1_struct_0(sK3),sK4),u1_struct_0(sK3)) = iProver_top ),
    inference(superposition,[status(thm)],[c_6958,c_2160])).

cnf(c_44,plain,
    ( m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(sK3))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_27])).

cnf(c_23,plain,
    ( v1_subset_1(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | X0 = X1 ),
    inference(cnf_transformation,[],[f79])).

cnf(c_351,plain,
    ( v1_subset_1(X0,X1)
    | ~ r1_tarski(X0,X1)
    | X0 = X1 ),
    inference(bin_hyper_res,[status(thm)],[c_23,c_272])).

cnf(c_25,negated_conjecture,
    ( ~ v1_subset_1(sK4,u1_struct_0(sK3))
    | r2_hidden(k3_yellow_0(sK3),sK4) ),
    inference(cnf_transformation,[],[f90])).

cnf(c_275,plain,
    ( ~ v1_subset_1(sK4,u1_struct_0(sK3))
    | r2_hidden(k3_yellow_0(sK3),sK4) ),
    inference(prop_impl,[status(thm)],[c_25])).

cnf(c_511,plain,
    ( r2_hidden(k3_yellow_0(sK3),sK4)
    | ~ r1_tarski(X0,X1)
    | X1 = X0
    | u1_struct_0(sK3) != X1
    | sK4 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_351,c_275])).

cnf(c_512,plain,
    ( r2_hidden(k3_yellow_0(sK3),sK4)
    | ~ r1_tarski(sK4,u1_struct_0(sK3))
    | u1_struct_0(sK3) = sK4 ),
    inference(unflattening,[status(thm)],[c_511])).

cnf(c_513,plain,
    ( u1_struct_0(sK3) = sK4
    | r2_hidden(k3_yellow_0(sK3),sK4) = iProver_top
    | r1_tarski(sK4,u1_struct_0(sK3)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_512])).

cnf(c_24,plain,
    ( ~ v1_subset_1(X0,X0)
    | ~ m1_subset_1(X0,k1_zfmisc_1(X0)) ),
    inference(cnf_transformation,[],[f93])).

cnf(c_26,negated_conjecture,
    ( v1_subset_1(sK4,u1_struct_0(sK3))
    | ~ r2_hidden(k3_yellow_0(sK3),sK4) ),
    inference(cnf_transformation,[],[f89])).

cnf(c_273,plain,
    ( v1_subset_1(sK4,u1_struct_0(sK3))
    | ~ r2_hidden(k3_yellow_0(sK3),sK4) ),
    inference(prop_impl,[status(thm)],[c_26])).

cnf(c_524,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X0))
    | ~ r2_hidden(k3_yellow_0(sK3),sK4)
    | u1_struct_0(sK3) != X0
    | sK4 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_24,c_273])).

cnf(c_525,plain,
    ( ~ m1_subset_1(u1_struct_0(sK3),k1_zfmisc_1(u1_struct_0(sK3)))
    | ~ r2_hidden(k3_yellow_0(sK3),sK4)
    | sK4 != u1_struct_0(sK3) ),
    inference(unflattening,[status(thm)],[c_524])).

cnf(c_526,plain,
    ( sK4 != u1_struct_0(sK3)
    | m1_subset_1(u1_struct_0(sK3),k1_zfmisc_1(u1_struct_0(sK3))) != iProver_top
    | r2_hidden(k3_yellow_0(sK3),sK4) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_525])).

cnf(c_2396,plain,
    ( ~ m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(sK3)))
    | r1_tarski(sK4,u1_struct_0(sK3)) ),
    inference(instantiation,[status(thm)],[c_8])).

cnf(c_2397,plain,
    ( m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(sK3))) != iProver_top
    | r1_tarski(sK4,u1_struct_0(sK3)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2396])).

cnf(c_2391,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK3)))
    | ~ r1_tarski(X0,u1_struct_0(sK3)) ),
    inference(instantiation,[status(thm)],[c_7])).

cnf(c_2498,plain,
    ( m1_subset_1(u1_struct_0(sK3),k1_zfmisc_1(u1_struct_0(sK3)))
    | ~ r1_tarski(u1_struct_0(sK3),u1_struct_0(sK3)) ),
    inference(instantiation,[status(thm)],[c_2391])).

cnf(c_2500,plain,
    ( m1_subset_1(u1_struct_0(sK3),k1_zfmisc_1(u1_struct_0(sK3))) = iProver_top
    | r1_tarski(u1_struct_0(sK3),u1_struct_0(sK3)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2498])).

cnf(c_1,plain,
    ( r1_tarski(X0,X0) ),
    inference(cnf_transformation,[],[f91])).

cnf(c_2499,plain,
    ( r1_tarski(u1_struct_0(sK3),u1_struct_0(sK3)) ),
    inference(instantiation,[status(thm)],[c_1])).

cnf(c_2502,plain,
    ( r1_tarski(u1_struct_0(sK3),u1_struct_0(sK3)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2499])).

cnf(c_4,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | ~ r2_hidden(sK0(X1,X0),X0)
    | X0 = X1 ),
    inference(cnf_transformation,[],[f60])).

cnf(c_347,plain,
    ( ~ r2_hidden(sK0(X0,X1),X1)
    | ~ r1_tarski(X1,X0)
    | X1 = X0 ),
    inference(bin_hyper_res,[status(thm)],[c_4,c_272])).

cnf(c_2539,plain,
    ( ~ r2_hidden(sK0(u1_struct_0(sK3),X0),X0)
    | ~ r1_tarski(X0,u1_struct_0(sK3))
    | X0 = u1_struct_0(sK3) ),
    inference(instantiation,[status(thm)],[c_347])).

cnf(c_2965,plain,
    ( ~ r2_hidden(sK0(u1_struct_0(sK3),sK4),sK4)
    | ~ r1_tarski(sK4,u1_struct_0(sK3))
    | sK4 = u1_struct_0(sK3) ),
    inference(instantiation,[status(thm)],[c_2539])).

cnf(c_2168,plain,
    ( u1_struct_0(sK3) = sK4
    | r2_hidden(k3_yellow_0(sK3),sK4) = iProver_top
    | r1_tarski(sK4,u1_struct_0(sK3)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_512])).

cnf(c_6265,plain,
    ( r2_hidden(k3_yellow_0(sK3),sK4) = iProver_top
    | u1_struct_0(sK3) = sK4 ),
    inference(global_propositional_subsumption,[status(thm)],[c_2168,c_44,c_513,c_2397])).

cnf(c_6266,plain,
    ( u1_struct_0(sK3) = sK4
    | r2_hidden(k3_yellow_0(sK3),sK4) = iProver_top ),
    inference(renaming,[status(thm)],[c_6265])).

cnf(c_6267,plain,
    ( r2_hidden(k3_yellow_0(sK3),sK4)
    | u1_struct_0(sK3) = sK4 ),
    inference(predicate_to_equality_rev,[status(thm)],[c_6266])).

cnf(c_2446,plain,
    ( k1_yellow_0(sK3,k5_waybel_0(sK3,k1_yellow_0(sK3,X0))) = k1_yellow_0(sK3,X0) ),
    inference(superposition,[status(thm)],[c_2160,c_2165])).

cnf(c_10,plain,
    ( ~ l1_orders_2(X0)
    | k1_yellow_0(X0,k1_xboole_0) = k3_yellow_0(X0) ),
    inference(cnf_transformation,[],[f65])).

cnf(c_739,plain,
    ( k1_yellow_0(X0,k1_xboole_0) = k3_yellow_0(X0)
    | sK3 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_10,c_30])).

cnf(c_740,plain,
    ( k1_yellow_0(sK3,k1_xboole_0) = k3_yellow_0(sK3) ),
    inference(unflattening,[status(thm)],[c_739])).

cnf(c_13,plain,
    ( r1_orders_2(X0,k1_yellow_0(X0,X1),k1_yellow_0(X0,X2))
    | ~ r1_yellow_0(X0,X2)
    | ~ r1_yellow_0(X0,X1)
    | ~ r1_tarski(X1,X2)
    | ~ l1_orders_2(X0) ),
    inference(cnf_transformation,[],[f68])).

cnf(c_705,plain,
    ( r1_orders_2(X0,k1_yellow_0(X0,X1),k1_yellow_0(X0,X2))
    | ~ r1_yellow_0(X0,X2)
    | ~ r1_yellow_0(X0,X1)
    | ~ r1_tarski(X1,X2)
    | sK3 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_13,c_30])).

cnf(c_706,plain,
    ( r1_orders_2(sK3,k1_yellow_0(sK3,X0),k1_yellow_0(sK3,X1))
    | ~ r1_yellow_0(sK3,X0)
    | ~ r1_yellow_0(sK3,X1)
    | ~ r1_tarski(X0,X1) ),
    inference(unflattening,[status(thm)],[c_705])).

cnf(c_2162,plain,
    ( r1_orders_2(sK3,k1_yellow_0(sK3,X0),k1_yellow_0(sK3,X1)) = iProver_top
    | r1_yellow_0(sK3,X0) != iProver_top
    | r1_yellow_0(sK3,X1) != iProver_top
    | r1_tarski(X0,X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_706])).

cnf(c_2941,plain,
    ( r1_orders_2(sK3,k3_yellow_0(sK3),k1_yellow_0(sK3,X0)) = iProver_top
    | r1_yellow_0(sK3,X0) != iProver_top
    | r1_yellow_0(sK3,k1_xboole_0) != iProver_top
    | r1_tarski(k1_xboole_0,X0) != iProver_top ),
    inference(superposition,[status(thm)],[c_740,c_2162])).

cnf(c_36,plain,
    ( v2_struct_0(sK3) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_35])).

cnf(c_39,plain,
    ( v5_orders_2(sK3) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_32])).

cnf(c_31,negated_conjecture,
    ( v1_yellow_0(sK3) ),
    inference(cnf_transformation,[],[f84])).

cnf(c_40,plain,
    ( v1_yellow_0(sK3) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_31])).

cnf(c_41,plain,
    ( l1_orders_2(sK3) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_30])).

cnf(c_14,plain,
    ( r1_yellow_0(X0,k1_xboole_0)
    | v2_struct_0(X0)
    | ~ v5_orders_2(X0)
    | ~ v1_yellow_0(X0)
    | ~ l1_orders_2(X0) ),
    inference(cnf_transformation,[],[f69])).

cnf(c_75,plain,
    ( r1_yellow_0(X0,k1_xboole_0) = iProver_top
    | v2_struct_0(X0) = iProver_top
    | v5_orders_2(X0) != iProver_top
    | v1_yellow_0(X0) != iProver_top
    | l1_orders_2(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_14])).

cnf(c_77,plain,
    ( r1_yellow_0(sK3,k1_xboole_0) = iProver_top
    | v2_struct_0(sK3) = iProver_top
    | v5_orders_2(sK3) != iProver_top
    | v1_yellow_0(sK3) != iProver_top
    | l1_orders_2(sK3) != iProver_top ),
    inference(instantiation,[status(thm)],[c_75])).

cnf(c_3,plain,
    ( r1_tarski(k1_xboole_0,X0) ),
    inference(cnf_transformation,[],[f58])).

cnf(c_108,plain,
    ( r1_tarski(k1_xboole_0,X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3])).

cnf(c_3150,plain,
    ( r1_orders_2(sK3,k3_yellow_0(sK3),k1_yellow_0(sK3,X0)) = iProver_top
    | r1_yellow_0(sK3,X0) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_2941,c_36,c_39,c_40,c_41,c_77,c_108])).

cnf(c_3622,plain,
    ( r1_orders_2(sK3,k3_yellow_0(sK3),k1_yellow_0(sK3,X0)) = iProver_top
    | r1_yellow_0(sK3,k5_waybel_0(sK3,k1_yellow_0(sK3,X0))) != iProver_top ),
    inference(superposition,[status(thm)],[c_2446,c_3150])).

cnf(c_732,plain,
    ( m1_subset_1(k1_yellow_0(sK3,X0),u1_struct_0(sK3)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_731])).

cnf(c_22,plain,
    ( r1_yellow_0(X0,k5_waybel_0(X0,X1))
    | ~ m1_subset_1(X1,u1_struct_0(X0))
    | ~ v3_orders_2(X0)
    | ~ v4_orders_2(X0)
    | v2_struct_0(X0)
    | ~ v5_orders_2(X0)
    | ~ l1_orders_2(X0) ),
    inference(cnf_transformation,[],[f76])).

cnf(c_545,plain,
    ( r1_yellow_0(X0,k5_waybel_0(X0,X1))
    | ~ m1_subset_1(X1,u1_struct_0(X0))
    | ~ v3_orders_2(X0)
    | ~ v4_orders_2(X0)
    | v2_struct_0(X0)
    | ~ l1_orders_2(X0)
    | sK3 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_22,c_32])).

cnf(c_546,plain,
    ( r1_yellow_0(sK3,k5_waybel_0(sK3,X0))
    | ~ m1_subset_1(X0,u1_struct_0(sK3))
    | ~ v3_orders_2(sK3)
    | ~ v4_orders_2(sK3)
    | v2_struct_0(sK3)
    | ~ l1_orders_2(sK3) ),
    inference(unflattening,[status(thm)],[c_545])).

cnf(c_550,plain,
    ( r1_yellow_0(sK3,k5_waybel_0(sK3,X0))
    | ~ m1_subset_1(X0,u1_struct_0(sK3)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_546,c_35,c_34,c_33,c_30])).

cnf(c_2362,plain,
    ( r1_yellow_0(sK3,k5_waybel_0(sK3,k1_yellow_0(sK3,X0)))
    | ~ m1_subset_1(k1_yellow_0(sK3,X0),u1_struct_0(sK3)) ),
    inference(instantiation,[status(thm)],[c_550])).

cnf(c_2363,plain,
    ( r1_yellow_0(sK3,k5_waybel_0(sK3,k1_yellow_0(sK3,X0))) = iProver_top
    | m1_subset_1(k1_yellow_0(sK3,X0),u1_struct_0(sK3)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2362])).

cnf(c_3731,plain,
    ( r1_orders_2(sK3,k3_yellow_0(sK3),k1_yellow_0(sK3,X0)) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_3622,c_732,c_2363])).

cnf(c_20,plain,
    ( ~ r1_orders_2(X0,X1,X2)
    | ~ v13_waybel_0(X3,X0)
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | ~ m1_subset_1(X1,u1_struct_0(X0))
    | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))
    | ~ r2_hidden(X1,X3)
    | r2_hidden(X2,X3)
    | ~ l1_orders_2(X0) ),
    inference(cnf_transformation,[],[f70])).

cnf(c_665,plain,
    ( ~ r1_orders_2(X0,X1,X2)
    | ~ v13_waybel_0(X3,X0)
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | ~ m1_subset_1(X1,u1_struct_0(X0))
    | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))
    | ~ r2_hidden(X1,X3)
    | r2_hidden(X2,X3)
    | sK3 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_20,c_30])).

cnf(c_666,plain,
    ( ~ r1_orders_2(sK3,X0,X1)
    | ~ v13_waybel_0(X2,sK3)
    | ~ m1_subset_1(X0,u1_struct_0(sK3))
    | ~ m1_subset_1(X1,u1_struct_0(sK3))
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK3)))
    | ~ r2_hidden(X0,X2)
    | r2_hidden(X1,X2) ),
    inference(unflattening,[status(thm)],[c_665])).

cnf(c_9,plain,
    ( m1_subset_1(X0,X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(X1))
    | ~ r2_hidden(X0,X2) ),
    inference(cnf_transformation,[],[f64])).

cnf(c_682,plain,
    ( ~ r1_orders_2(sK3,X0,X1)
    | ~ v13_waybel_0(X2,sK3)
    | ~ m1_subset_1(X1,u1_struct_0(sK3))
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK3)))
    | ~ r2_hidden(X0,X2)
    | r2_hidden(X1,X2) ),
    inference(forward_subsumption_resolution,[status(thm)],[c_666,c_9])).

cnf(c_2164,plain,
    ( r1_orders_2(sK3,X0,X1) != iProver_top
    | v13_waybel_0(X2,sK3) != iProver_top
    | m1_subset_1(X1,u1_struct_0(sK3)) != iProver_top
    | m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK3))) != iProver_top
    | r2_hidden(X0,X2) != iProver_top
    | r2_hidden(X1,X2) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_682])).

cnf(c_3939,plain,
    ( r1_orders_2(sK3,X0,X1) != iProver_top
    | v13_waybel_0(sK4,sK3) != iProver_top
    | m1_subset_1(X1,u1_struct_0(sK3)) != iProver_top
    | r2_hidden(X0,sK4) != iProver_top
    | r2_hidden(X1,sK4) = iProver_top ),
    inference(superposition,[status(thm)],[c_2174,c_2164])).

cnf(c_28,negated_conjecture,
    ( v13_waybel_0(sK4,sK3) ),
    inference(cnf_transformation,[],[f87])).

cnf(c_907,plain,
    ( ~ r1_orders_2(sK3,X0,X1)
    | ~ m1_subset_1(X1,u1_struct_0(sK3))
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK3)))
    | ~ r2_hidden(X0,X2)
    | r2_hidden(X1,X2)
    | sK4 != X2
    | sK3 != sK3 ),
    inference(resolution_lifted,[status(thm)],[c_28,c_682])).

cnf(c_908,plain,
    ( ~ r1_orders_2(sK3,X0,X1)
    | ~ m1_subset_1(X1,u1_struct_0(sK3))
    | ~ m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(sK3)))
    | ~ r2_hidden(X0,sK4)
    | r2_hidden(X1,sK4) ),
    inference(unflattening,[status(thm)],[c_907])).

cnf(c_909,plain,
    ( r1_orders_2(sK3,X0,X1) != iProver_top
    | m1_subset_1(X1,u1_struct_0(sK3)) != iProver_top
    | m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(sK3))) != iProver_top
    | r2_hidden(X0,sK4) != iProver_top
    | r2_hidden(X1,sK4) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_908])).

cnf(c_4383,plain,
    ( r1_orders_2(sK3,X0,X1) != iProver_top
    | m1_subset_1(X1,u1_struct_0(sK3)) != iProver_top
    | r2_hidden(X0,sK4) != iProver_top
    | r2_hidden(X1,sK4) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_3939,c_44,c_909])).

cnf(c_4393,plain,
    ( m1_subset_1(k1_yellow_0(sK3,X0),u1_struct_0(sK3)) != iProver_top
    | r2_hidden(k1_yellow_0(sK3,X0),sK4) = iProver_top
    | r2_hidden(k3_yellow_0(sK3),sK4) != iProver_top ),
    inference(superposition,[status(thm)],[c_3731,c_4383])).

cnf(c_4445,plain,
    ( r2_hidden(k1_yellow_0(sK3,X0),sK4) = iProver_top
    | r2_hidden(k3_yellow_0(sK3),sK4) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_4393,c_732])).

cnf(c_7111,plain,
    ( u1_struct_0(sK3) = sK4
    | r2_hidden(sK0(u1_struct_0(sK3),sK4),sK4) = iProver_top
    | r2_hidden(k3_yellow_0(sK3),sK4) != iProver_top ),
    inference(superposition,[status(thm)],[c_6958,c_4445])).

cnf(c_7322,plain,
    ( r2_hidden(sK0(u1_struct_0(sK3),sK4),sK4)
    | ~ r2_hidden(k3_yellow_0(sK3),sK4)
    | u1_struct_0(sK3) = sK4 ),
    inference(predicate_to_equality_rev,[status(thm)],[c_7111])).

cnf(c_7330,plain,
    ( u1_struct_0(sK3) = sK4 ),
    inference(global_propositional_subsumption,[status(thm)],[c_7115,c_27,c_44,c_513,c_526,c_2396,c_2397,c_2500,c_2502,c_2965,c_6267,c_7322])).

cnf(c_12,plain,
    ( m1_subset_1(k3_yellow_0(X0),u1_struct_0(X0))
    | ~ l1_orders_2(X0) ),
    inference(cnf_transformation,[],[f67])).

cnf(c_723,plain,
    ( m1_subset_1(k3_yellow_0(X0),u1_struct_0(X0))
    | sK3 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_12,c_30])).

cnf(c_724,plain,
    ( m1_subset_1(k3_yellow_0(sK3),u1_struct_0(sK3)) ),
    inference(unflattening,[status(thm)],[c_723])).

cnf(c_2161,plain,
    ( m1_subset_1(k3_yellow_0(sK3),u1_struct_0(sK3)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_724])).

cnf(c_7358,plain,
    ( m1_subset_1(k3_yellow_0(sK3),sK4) = iProver_top ),
    inference(demodulation,[status(thm)],[c_7330,c_2161])).

cnf(c_6,plain,
    ( ~ m1_subset_1(X0,X1)
    | r2_hidden(X0,X1)
    | v1_xboole_0(X1) ),
    inference(cnf_transformation,[],[f61])).

cnf(c_29,negated_conjecture,
    ( ~ v1_xboole_0(sK4) ),
    inference(cnf_transformation,[],[f86])).

cnf(c_480,plain,
    ( ~ m1_subset_1(X0,X1)
    | r2_hidden(X0,X1)
    | sK4 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_6,c_29])).

cnf(c_481,plain,
    ( ~ m1_subset_1(X0,sK4)
    | r2_hidden(X0,sK4) ),
    inference(unflattening,[status(thm)],[c_480])).

cnf(c_2170,plain,
    ( m1_subset_1(X0,sK4) != iProver_top
    | r2_hidden(X0,sK4) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_481])).

cnf(c_7665,plain,
    ( r2_hidden(k3_yellow_0(sK3),sK4) = iProver_top ),
    inference(superposition,[status(thm)],[c_7358,c_2170])).

cnf(c_2167,plain,
    ( sK4 != u1_struct_0(sK3)
    | m1_subset_1(u1_struct_0(sK3),k1_zfmisc_1(u1_struct_0(sK3))) != iProver_top
    | r2_hidden(k3_yellow_0(sK3),sK4) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_525])).

cnf(c_5012,plain,
    ( sK4 != u1_struct_0(sK3)
    | r2_hidden(k3_yellow_0(sK3),sK4) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_2167,c_526,c_2500,c_2502])).

cnf(c_7343,plain,
    ( sK4 != sK4
    | r2_hidden(k3_yellow_0(sK3),sK4) != iProver_top ),
    inference(demodulation,[status(thm)],[c_7330,c_5012])).

cnf(c_7437,plain,
    ( r2_hidden(k3_yellow_0(sK3),sK4) != iProver_top ),
    inference(equality_resolution_simp,[status(thm)],[c_7343])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_7665,c_7437])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.00/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.12  % Command    : iproveropt_run.sh %d %s
% 0.12/0.33  % Computer   : n003.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.33  % CPULimit   : 60
% 0.12/0.33  % WCLimit    : 600
% 0.12/0.33  % DateTime   : Tue Dec  1 18:40:42 EST 2020
% 0.12/0.33  % CPUTime    : 
% 0.12/0.33  % Running in FOF mode
% 3.22/0.98  % SZS status Started for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.22/0.98  
% 3.22/0.98  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 3.22/0.98  
% 3.22/0.98  ------  iProver source info
% 3.22/0.98  
% 3.22/0.98  git: date: 2020-06-30 10:37:57 +0100
% 3.22/0.98  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 3.22/0.98  git: non_committed_changes: false
% 3.22/0.98  git: last_make_outside_of_git: false
% 3.22/0.98  
% 3.22/0.98  ------ 
% 3.22/0.98  
% 3.22/0.98  ------ Input Options
% 3.22/0.98  
% 3.22/0.98  --out_options                           all
% 3.22/0.98  --tptp_safe_out                         true
% 3.22/0.98  --problem_path                          ""
% 3.22/0.98  --include_path                          ""
% 3.22/0.98  --clausifier                            res/vclausify_rel
% 3.22/0.98  --clausifier_options                    --mode clausify
% 3.22/0.98  --stdin                                 false
% 3.22/0.98  --stats_out                             all
% 3.22/0.98  
% 3.22/0.98  ------ General Options
% 3.22/0.98  
% 3.22/0.98  --fof                                   false
% 3.22/0.98  --time_out_real                         305.
% 3.22/0.98  --time_out_virtual                      -1.
% 3.22/0.98  --symbol_type_check                     false
% 3.22/0.98  --clausify_out                          false
% 3.22/0.98  --sig_cnt_out                           false
% 3.22/0.98  --trig_cnt_out                          false
% 3.22/0.98  --trig_cnt_out_tolerance                1.
% 3.22/0.98  --trig_cnt_out_sk_spl                   false
% 3.22/0.98  --abstr_cl_out                          false
% 3.22/0.98  
% 3.22/0.98  ------ Global Options
% 3.22/0.98  
% 3.22/0.98  --schedule                              default
% 3.22/0.98  --add_important_lit                     false
% 3.22/0.98  --prop_solver_per_cl                    1000
% 3.22/0.98  --min_unsat_core                        false
% 3.22/0.98  --soft_assumptions                      false
% 3.22/0.98  --soft_lemma_size                       3
% 3.22/0.98  --prop_impl_unit_size                   0
% 3.22/0.98  --prop_impl_unit                        []
% 3.22/0.98  --share_sel_clauses                     true
% 3.22/0.98  --reset_solvers                         false
% 3.22/0.98  --bc_imp_inh                            [conj_cone]
% 3.22/0.98  --conj_cone_tolerance                   3.
% 3.22/0.98  --extra_neg_conj                        none
% 3.22/0.98  --large_theory_mode                     true
% 3.22/0.98  --prolific_symb_bound                   200
% 3.22/0.98  --lt_threshold                          2000
% 3.22/0.98  --clause_weak_htbl                      true
% 3.22/0.98  --gc_record_bc_elim                     false
% 3.22/0.98  
% 3.22/0.98  ------ Preprocessing Options
% 3.22/0.98  
% 3.22/0.98  --preprocessing_flag                    true
% 3.22/0.98  --time_out_prep_mult                    0.1
% 3.22/0.98  --splitting_mode                        input
% 3.22/0.98  --splitting_grd                         true
% 3.22/0.98  --splitting_cvd                         false
% 3.22/0.98  --splitting_cvd_svl                     false
% 3.22/0.98  --splitting_nvd                         32
% 3.22/0.98  --sub_typing                            true
% 3.22/0.98  --prep_gs_sim                           true
% 3.22/0.98  --prep_unflatten                        true
% 3.22/0.98  --prep_res_sim                          true
% 3.22/0.98  --prep_upred                            true
% 3.22/0.98  --prep_sem_filter                       exhaustive
% 3.22/0.98  --prep_sem_filter_out                   false
% 3.22/0.98  --pred_elim                             true
% 3.22/0.98  --res_sim_input                         true
% 3.22/0.98  --eq_ax_congr_red                       true
% 3.22/0.98  --pure_diseq_elim                       true
% 3.22/0.98  --brand_transform                       false
% 3.22/0.98  --non_eq_to_eq                          false
% 3.22/0.98  --prep_def_merge                        true
% 3.22/0.98  --prep_def_merge_prop_impl              false
% 3.22/0.98  --prep_def_merge_mbd                    true
% 3.22/0.98  --prep_def_merge_tr_red                 false
% 3.22/0.98  --prep_def_merge_tr_cl                  false
% 3.22/0.98  --smt_preprocessing                     true
% 3.22/0.98  --smt_ac_axioms                         fast
% 3.22/0.98  --preprocessed_out                      false
% 3.22/0.98  --preprocessed_stats                    false
% 3.22/0.98  
% 3.22/0.98  ------ Abstraction refinement Options
% 3.22/0.98  
% 3.22/0.98  --abstr_ref                             []
% 3.22/0.98  --abstr_ref_prep                        false
% 3.22/0.98  --abstr_ref_until_sat                   false
% 3.22/0.98  --abstr_ref_sig_restrict                funpre
% 3.22/0.98  --abstr_ref_af_restrict_to_split_sk     false
% 3.22/0.98  --abstr_ref_under                       []
% 3.22/0.98  
% 3.22/0.98  ------ SAT Options
% 3.22/0.98  
% 3.22/0.98  --sat_mode                              false
% 3.22/0.98  --sat_fm_restart_options                ""
% 3.22/0.98  --sat_gr_def                            false
% 3.22/0.98  --sat_epr_types                         true
% 3.22/0.98  --sat_non_cyclic_types                  false
% 3.22/0.98  --sat_finite_models                     false
% 3.22/0.98  --sat_fm_lemmas                         false
% 3.22/0.98  --sat_fm_prep                           false
% 3.22/0.98  --sat_fm_uc_incr                        true
% 3.22/0.98  --sat_out_model                         small
% 3.22/0.98  --sat_out_clauses                       false
% 3.22/0.98  
% 3.22/0.98  ------ QBF Options
% 3.22/0.98  
% 3.22/0.98  --qbf_mode                              false
% 3.22/0.98  --qbf_elim_univ                         false
% 3.22/0.98  --qbf_dom_inst                          none
% 3.22/0.98  --qbf_dom_pre_inst                      false
% 3.22/0.98  --qbf_sk_in                             false
% 3.22/0.98  --qbf_pred_elim                         true
% 3.22/0.98  --qbf_split                             512
% 3.22/0.98  
% 3.22/0.98  ------ BMC1 Options
% 3.22/0.98  
% 3.22/0.98  --bmc1_incremental                      false
% 3.22/0.98  --bmc1_axioms                           reachable_all
% 3.22/0.98  --bmc1_min_bound                        0
% 3.22/0.98  --bmc1_max_bound                        -1
% 3.22/0.98  --bmc1_max_bound_default                -1
% 3.22/0.98  --bmc1_symbol_reachability              true
% 3.22/0.98  --bmc1_property_lemmas                  false
% 3.22/0.98  --bmc1_k_induction                      false
% 3.22/0.98  --bmc1_non_equiv_states                 false
% 3.22/0.98  --bmc1_deadlock                         false
% 3.22/0.98  --bmc1_ucm                              false
% 3.22/0.98  --bmc1_add_unsat_core                   none
% 3.22/0.98  --bmc1_unsat_core_children              false
% 3.22/0.98  --bmc1_unsat_core_extrapolate_axioms    false
% 3.22/0.98  --bmc1_out_stat                         full
% 3.22/0.98  --bmc1_ground_init                      false
% 3.22/0.98  --bmc1_pre_inst_next_state              false
% 3.22/0.98  --bmc1_pre_inst_state                   false
% 3.22/0.98  --bmc1_pre_inst_reach_state             false
% 3.22/0.98  --bmc1_out_unsat_core                   false
% 3.22/0.98  --bmc1_aig_witness_out                  false
% 3.22/0.98  --bmc1_verbose                          false
% 3.22/0.98  --bmc1_dump_clauses_tptp                false
% 3.22/0.98  --bmc1_dump_unsat_core_tptp             false
% 3.22/0.98  --bmc1_dump_file                        -
% 3.22/0.98  --bmc1_ucm_expand_uc_limit              128
% 3.22/0.98  --bmc1_ucm_n_expand_iterations          6
% 3.22/0.98  --bmc1_ucm_extend_mode                  1
% 3.22/0.98  --bmc1_ucm_init_mode                    2
% 3.22/0.98  --bmc1_ucm_cone_mode                    none
% 3.22/0.98  --bmc1_ucm_reduced_relation_type        0
% 3.22/0.98  --bmc1_ucm_relax_model                  4
% 3.22/0.98  --bmc1_ucm_full_tr_after_sat            true
% 3.22/0.98  --bmc1_ucm_expand_neg_assumptions       false
% 3.22/0.98  --bmc1_ucm_layered_model                none
% 3.22/0.98  --bmc1_ucm_max_lemma_size               10
% 3.22/0.98  
% 3.22/0.98  ------ AIG Options
% 3.22/0.98  
% 3.22/0.98  --aig_mode                              false
% 3.22/0.98  
% 3.22/0.98  ------ Instantiation Options
% 3.22/0.98  
% 3.22/0.98  --instantiation_flag                    true
% 3.22/0.98  --inst_sos_flag                         false
% 3.22/0.98  --inst_sos_phase                        true
% 3.22/0.98  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 3.22/0.98  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 3.22/0.98  --inst_lit_sel_side                     num_symb
% 3.22/0.98  --inst_solver_per_active                1400
% 3.22/0.98  --inst_solver_calls_frac                1.
% 3.22/0.98  --inst_passive_queue_type               priority_queues
% 3.22/0.98  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 3.22/0.98  --inst_passive_queues_freq              [25;2]
% 3.22/0.98  --inst_dismatching                      true
% 3.22/0.98  --inst_eager_unprocessed_to_passive     true
% 3.22/0.98  --inst_prop_sim_given                   true
% 3.22/0.98  --inst_prop_sim_new                     false
% 3.22/0.98  --inst_subs_new                         false
% 3.22/0.98  --inst_eq_res_simp                      false
% 3.22/0.98  --inst_subs_given                       false
% 3.22/0.98  --inst_orphan_elimination               true
% 3.22/0.98  --inst_learning_loop_flag               true
% 3.22/0.98  --inst_learning_start                   3000
% 3.22/0.98  --inst_learning_factor                  2
% 3.22/0.98  --inst_start_prop_sim_after_learn       3
% 3.22/0.98  --inst_sel_renew                        solver
% 3.22/0.98  --inst_lit_activity_flag                true
% 3.22/0.98  --inst_restr_to_given                   false
% 3.22/0.98  --inst_activity_threshold               500
% 3.22/0.98  --inst_out_proof                        true
% 3.22/0.98  
% 3.22/0.98  ------ Resolution Options
% 3.22/0.98  
% 3.22/0.98  --resolution_flag                       true
% 3.22/0.98  --res_lit_sel                           adaptive
% 3.22/0.98  --res_lit_sel_side                      none
% 3.22/0.98  --res_ordering                          kbo
% 3.22/0.98  --res_to_prop_solver                    active
% 3.22/0.98  --res_prop_simpl_new                    false
% 3.22/0.98  --res_prop_simpl_given                  true
% 3.22/0.98  --res_passive_queue_type                priority_queues
% 3.22/0.98  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 3.22/0.98  --res_passive_queues_freq               [15;5]
% 3.22/0.98  --res_forward_subs                      full
% 3.22/0.98  --res_backward_subs                     full
% 3.22/0.98  --res_forward_subs_resolution           true
% 3.22/0.98  --res_backward_subs_resolution          true
% 3.22/0.98  --res_orphan_elimination                true
% 3.22/0.98  --res_time_limit                        2.
% 3.22/0.98  --res_out_proof                         true
% 3.22/0.98  
% 3.22/0.98  ------ Superposition Options
% 3.22/0.98  
% 3.22/0.98  --superposition_flag                    true
% 3.22/0.98  --sup_passive_queue_type                priority_queues
% 3.22/0.98  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 3.22/0.98  --sup_passive_queues_freq               [8;1;4]
% 3.22/0.98  --demod_completeness_check              fast
% 3.22/0.98  --demod_use_ground                      true
% 3.22/0.98  --sup_to_prop_solver                    passive
% 3.22/0.98  --sup_prop_simpl_new                    true
% 3.22/0.98  --sup_prop_simpl_given                  true
% 3.22/0.98  --sup_fun_splitting                     false
% 3.22/0.98  --sup_smt_interval                      50000
% 3.22/0.98  
% 3.22/0.98  ------ Superposition Simplification Setup
% 3.22/0.98  
% 3.22/0.98  --sup_indices_passive                   []
% 3.22/0.98  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.22/0.98  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.22/0.98  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.22/0.98  --sup_full_triv                         [TrivRules;PropSubs]
% 3.22/0.98  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.22/0.98  --sup_full_bw                           [BwDemod]
% 3.22/0.98  --sup_immed_triv                        [TrivRules]
% 3.22/0.98  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 3.22/0.98  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.22/0.98  --sup_immed_bw_main                     []
% 3.22/0.98  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 3.22/0.98  --sup_input_triv                        [Unflattening;TrivRules]
% 3.22/0.98  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.22/0.98  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 3.22/0.98  
% 3.22/0.98  ------ Combination Options
% 3.22/0.98  
% 3.22/0.98  --comb_res_mult                         3
% 3.22/0.98  --comb_sup_mult                         2
% 3.22/0.98  --comb_inst_mult                        10
% 3.22/0.98  
% 3.22/0.98  ------ Debug Options
% 3.22/0.98  
% 3.22/0.98  --dbg_backtrace                         false
% 3.22/0.98  --dbg_dump_prop_clauses                 false
% 3.22/0.98  --dbg_dump_prop_clauses_file            -
% 3.22/0.98  --dbg_out_stat                          false
% 3.22/0.98  ------ Parsing...
% 3.22/0.98  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 3.22/0.98  
% 3.22/0.98  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe:1:0s pe:2:0s pe:4:0s pe:8:0s pe_e  sf_s  rm: 9 0s  sf_e  pe_s  pe_e 
% 3.22/0.98  
% 3.22/0.98  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 3.22/0.98  
% 3.22/0.98  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 3.22/0.98  ------ Proving...
% 3.22/0.98  ------ Problem Properties 
% 3.22/0.98  
% 3.22/0.98  
% 3.22/0.98  clauses                                 26
% 3.22/0.98  conjectures                             2
% 3.22/0.98  EPR                                     6
% 3.22/0.98  Horn                                    20
% 3.22/0.98  unary                                   8
% 3.22/0.98  binary                                  5
% 3.22/0.98  lits                                    61
% 3.22/0.98  lits eq                                 7
% 3.22/0.98  fd_pure                                 0
% 3.22/0.98  fd_pseudo                               0
% 3.22/0.98  fd_cond                                 0
% 3.22/0.98  fd_pseudo_cond                          3
% 3.22/0.98  AC symbols                              0
% 3.22/0.98  
% 3.22/0.98  ------ Schedule dynamic 5 is on 
% 3.22/0.98  
% 3.22/0.98  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" Time Limit: 10.
% 3.22/0.98  
% 3.22/0.98  
% 3.22/0.98  ------ 
% 3.22/0.98  Current options:
% 3.22/0.98  ------ 
% 3.22/0.98  
% 3.22/0.98  ------ Input Options
% 3.22/0.98  
% 3.22/0.98  --out_options                           all
% 3.22/0.98  --tptp_safe_out                         true
% 3.22/0.98  --problem_path                          ""
% 3.22/0.98  --include_path                          ""
% 3.22/0.98  --clausifier                            res/vclausify_rel
% 3.22/0.98  --clausifier_options                    --mode clausify
% 3.22/0.98  --stdin                                 false
% 3.22/0.98  --stats_out                             all
% 3.22/0.98  
% 3.22/0.98  ------ General Options
% 3.22/0.98  
% 3.22/0.98  --fof                                   false
% 3.22/0.98  --time_out_real                         305.
% 3.22/0.98  --time_out_virtual                      -1.
% 3.22/0.98  --symbol_type_check                     false
% 3.22/0.98  --clausify_out                          false
% 3.22/0.98  --sig_cnt_out                           false
% 3.22/0.98  --trig_cnt_out                          false
% 3.22/0.98  --trig_cnt_out_tolerance                1.
% 3.22/0.98  --trig_cnt_out_sk_spl                   false
% 3.22/0.98  --abstr_cl_out                          false
% 3.22/0.98  
% 3.22/0.98  ------ Global Options
% 3.22/0.98  
% 3.22/0.98  --schedule                              default
% 3.22/0.98  --add_important_lit                     false
% 3.22/0.98  --prop_solver_per_cl                    1000
% 3.22/0.98  --min_unsat_core                        false
% 3.22/0.98  --soft_assumptions                      false
% 3.22/0.98  --soft_lemma_size                       3
% 3.22/0.98  --prop_impl_unit_size                   0
% 3.22/0.98  --prop_impl_unit                        []
% 3.22/0.98  --share_sel_clauses                     true
% 3.22/0.98  --reset_solvers                         false
% 3.22/0.98  --bc_imp_inh                            [conj_cone]
% 3.22/0.98  --conj_cone_tolerance                   3.
% 3.22/0.98  --extra_neg_conj                        none
% 3.22/0.98  --large_theory_mode                     true
% 3.22/0.98  --prolific_symb_bound                   200
% 3.22/0.98  --lt_threshold                          2000
% 3.22/0.98  --clause_weak_htbl                      true
% 3.22/0.98  --gc_record_bc_elim                     false
% 3.22/0.98  
% 3.22/0.98  ------ Preprocessing Options
% 3.22/0.98  
% 3.22/0.98  --preprocessing_flag                    true
% 3.22/0.98  --time_out_prep_mult                    0.1
% 3.22/0.98  --splitting_mode                        input
% 3.22/0.98  --splitting_grd                         true
% 3.22/0.98  --splitting_cvd                         false
% 3.22/0.98  --splitting_cvd_svl                     false
% 3.22/0.98  --splitting_nvd                         32
% 3.22/0.98  --sub_typing                            true
% 3.22/0.98  --prep_gs_sim                           true
% 3.22/0.98  --prep_unflatten                        true
% 3.22/0.98  --prep_res_sim                          true
% 3.22/0.98  --prep_upred                            true
% 3.22/0.98  --prep_sem_filter                       exhaustive
% 3.22/0.98  --prep_sem_filter_out                   false
% 3.22/0.98  --pred_elim                             true
% 3.22/0.98  --res_sim_input                         true
% 3.22/0.98  --eq_ax_congr_red                       true
% 3.22/0.98  --pure_diseq_elim                       true
% 3.22/0.98  --brand_transform                       false
% 3.22/0.98  --non_eq_to_eq                          false
% 3.22/0.98  --prep_def_merge                        true
% 3.22/0.98  --prep_def_merge_prop_impl              false
% 3.22/0.98  --prep_def_merge_mbd                    true
% 3.22/0.98  --prep_def_merge_tr_red                 false
% 3.22/0.98  --prep_def_merge_tr_cl                  false
% 3.22/0.98  --smt_preprocessing                     true
% 3.22/0.98  --smt_ac_axioms                         fast
% 3.22/0.98  --preprocessed_out                      false
% 3.22/0.98  --preprocessed_stats                    false
% 3.22/0.98  
% 3.22/0.98  ------ Abstraction refinement Options
% 3.22/0.98  
% 3.22/0.98  --abstr_ref                             []
% 3.22/0.98  --abstr_ref_prep                        false
% 3.22/0.98  --abstr_ref_until_sat                   false
% 3.22/0.98  --abstr_ref_sig_restrict                funpre
% 3.22/0.98  --abstr_ref_af_restrict_to_split_sk     false
% 3.22/0.98  --abstr_ref_under                       []
% 3.22/0.98  
% 3.22/0.98  ------ SAT Options
% 3.22/0.98  
% 3.22/0.98  --sat_mode                              false
% 3.22/0.98  --sat_fm_restart_options                ""
% 3.22/0.98  --sat_gr_def                            false
% 3.22/0.98  --sat_epr_types                         true
% 3.22/0.98  --sat_non_cyclic_types                  false
% 3.22/0.98  --sat_finite_models                     false
% 3.22/0.98  --sat_fm_lemmas                         false
% 3.22/0.98  --sat_fm_prep                           false
% 3.22/0.98  --sat_fm_uc_incr                        true
% 3.22/0.98  --sat_out_model                         small
% 3.22/0.98  --sat_out_clauses                       false
% 3.22/0.98  
% 3.22/0.98  ------ QBF Options
% 3.22/0.98  
% 3.22/0.98  --qbf_mode                              false
% 3.22/0.98  --qbf_elim_univ                         false
% 3.22/0.98  --qbf_dom_inst                          none
% 3.22/0.98  --qbf_dom_pre_inst                      false
% 3.22/0.98  --qbf_sk_in                             false
% 3.22/0.98  --qbf_pred_elim                         true
% 3.22/0.98  --qbf_split                             512
% 3.22/0.98  
% 3.22/0.98  ------ BMC1 Options
% 3.22/0.98  
% 3.22/0.98  --bmc1_incremental                      false
% 3.22/0.98  --bmc1_axioms                           reachable_all
% 3.22/0.98  --bmc1_min_bound                        0
% 3.22/0.98  --bmc1_max_bound                        -1
% 3.22/0.98  --bmc1_max_bound_default                -1
% 3.22/0.98  --bmc1_symbol_reachability              true
% 3.22/0.98  --bmc1_property_lemmas                  false
% 3.22/0.98  --bmc1_k_induction                      false
% 3.22/0.98  --bmc1_non_equiv_states                 false
% 3.22/0.98  --bmc1_deadlock                         false
% 3.22/0.98  --bmc1_ucm                              false
% 3.22/0.98  --bmc1_add_unsat_core                   none
% 3.22/0.98  --bmc1_unsat_core_children              false
% 3.22/0.98  --bmc1_unsat_core_extrapolate_axioms    false
% 3.22/0.98  --bmc1_out_stat                         full
% 3.22/0.98  --bmc1_ground_init                      false
% 3.22/0.98  --bmc1_pre_inst_next_state              false
% 3.22/0.98  --bmc1_pre_inst_state                   false
% 3.22/0.98  --bmc1_pre_inst_reach_state             false
% 3.22/0.98  --bmc1_out_unsat_core                   false
% 3.22/0.98  --bmc1_aig_witness_out                  false
% 3.22/0.98  --bmc1_verbose                          false
% 3.22/0.98  --bmc1_dump_clauses_tptp                false
% 3.22/0.98  --bmc1_dump_unsat_core_tptp             false
% 3.22/0.98  --bmc1_dump_file                        -
% 3.22/0.98  --bmc1_ucm_expand_uc_limit              128
% 3.22/0.98  --bmc1_ucm_n_expand_iterations          6
% 3.22/0.98  --bmc1_ucm_extend_mode                  1
% 3.22/0.98  --bmc1_ucm_init_mode                    2
% 3.22/0.98  --bmc1_ucm_cone_mode                    none
% 3.22/0.98  --bmc1_ucm_reduced_relation_type        0
% 3.22/0.98  --bmc1_ucm_relax_model                  4
% 3.22/0.98  --bmc1_ucm_full_tr_after_sat            true
% 3.22/0.98  --bmc1_ucm_expand_neg_assumptions       false
% 3.22/0.98  --bmc1_ucm_layered_model                none
% 3.22/0.98  --bmc1_ucm_max_lemma_size               10
% 3.22/0.98  
% 3.22/0.98  ------ AIG Options
% 3.22/0.98  
% 3.22/0.98  --aig_mode                              false
% 3.22/0.98  
% 3.22/0.98  ------ Instantiation Options
% 3.22/0.98  
% 3.22/0.98  --instantiation_flag                    true
% 3.22/0.98  --inst_sos_flag                         false
% 3.22/0.98  --inst_sos_phase                        true
% 3.22/0.98  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 3.22/0.98  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 3.22/0.98  --inst_lit_sel_side                     none
% 3.22/0.98  --inst_solver_per_active                1400
% 3.22/0.98  --inst_solver_calls_frac                1.
% 3.22/0.98  --inst_passive_queue_type               priority_queues
% 3.22/0.98  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 3.22/0.98  --inst_passive_queues_freq              [25;2]
% 3.22/0.98  --inst_dismatching                      true
% 3.22/0.98  --inst_eager_unprocessed_to_passive     true
% 3.22/0.98  --inst_prop_sim_given                   true
% 3.22/0.98  --inst_prop_sim_new                     false
% 3.22/0.98  --inst_subs_new                         false
% 3.22/0.98  --inst_eq_res_simp                      false
% 3.22/0.98  --inst_subs_given                       false
% 3.22/0.98  --inst_orphan_elimination               true
% 3.22/0.98  --inst_learning_loop_flag               true
% 3.22/0.98  --inst_learning_start                   3000
% 3.22/0.98  --inst_learning_factor                  2
% 3.22/0.98  --inst_start_prop_sim_after_learn       3
% 3.22/0.98  --inst_sel_renew                        solver
% 3.22/0.98  --inst_lit_activity_flag                true
% 3.22/0.98  --inst_restr_to_given                   false
% 3.22/0.98  --inst_activity_threshold               500
% 3.22/0.98  --inst_out_proof                        true
% 3.22/0.98  
% 3.22/0.98  ------ Resolution Options
% 3.22/0.98  
% 3.22/0.98  --resolution_flag                       false
% 3.22/0.98  --res_lit_sel                           adaptive
% 3.22/0.98  --res_lit_sel_side                      none
% 3.22/0.98  --res_ordering                          kbo
% 3.22/0.98  --res_to_prop_solver                    active
% 3.22/0.98  --res_prop_simpl_new                    false
% 3.22/0.98  --res_prop_simpl_given                  true
% 3.22/0.98  --res_passive_queue_type                priority_queues
% 3.22/0.98  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 3.22/0.98  --res_passive_queues_freq               [15;5]
% 3.22/0.98  --res_forward_subs                      full
% 3.22/0.98  --res_backward_subs                     full
% 3.22/0.98  --res_forward_subs_resolution           true
% 3.22/0.98  --res_backward_subs_resolution          true
% 3.22/0.98  --res_orphan_elimination                true
% 3.22/0.98  --res_time_limit                        2.
% 3.22/0.98  --res_out_proof                         true
% 3.22/0.98  
% 3.22/0.98  ------ Superposition Options
% 3.22/0.98  
% 3.22/0.98  --superposition_flag                    true
% 3.22/0.98  --sup_passive_queue_type                priority_queues
% 3.22/0.98  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 3.22/0.98  --sup_passive_queues_freq               [8;1;4]
% 3.22/0.98  --demod_completeness_check              fast
% 3.22/0.98  --demod_use_ground                      true
% 3.22/0.98  --sup_to_prop_solver                    passive
% 3.22/0.98  --sup_prop_simpl_new                    true
% 3.22/0.98  --sup_prop_simpl_given                  true
% 3.22/0.98  --sup_fun_splitting                     false
% 3.22/0.98  --sup_smt_interval                      50000
% 3.22/0.98  
% 3.22/0.98  ------ Superposition Simplification Setup
% 3.22/0.98  
% 3.22/0.98  --sup_indices_passive                   []
% 3.22/0.98  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.22/0.98  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.22/0.98  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.22/0.98  --sup_full_triv                         [TrivRules;PropSubs]
% 3.22/0.98  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.22/0.98  --sup_full_bw                           [BwDemod]
% 3.22/0.98  --sup_immed_triv                        [TrivRules]
% 3.22/0.98  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 3.22/0.98  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.22/0.98  --sup_immed_bw_main                     []
% 3.22/0.98  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 3.22/0.98  --sup_input_triv                        [Unflattening;TrivRules]
% 3.22/0.98  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.22/0.98  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 3.22/0.98  
% 3.22/0.98  ------ Combination Options
% 3.22/0.98  
% 3.22/0.98  --comb_res_mult                         3
% 3.22/0.98  --comb_sup_mult                         2
% 3.22/0.98  --comb_inst_mult                        10
% 3.22/0.98  
% 3.22/0.98  ------ Debug Options
% 3.22/0.98  
% 3.22/0.98  --dbg_backtrace                         false
% 3.22/0.98  --dbg_dump_prop_clauses                 false
% 3.22/0.98  --dbg_dump_prop_clauses_file            -
% 3.22/0.98  --dbg_out_stat                          false
% 3.22/0.98  
% 3.22/0.98  
% 3.22/0.98  
% 3.22/0.98  
% 3.22/0.98  ------ Proving...
% 3.22/0.98  
% 3.22/0.98  
% 3.22/0.98  % SZS status Theorem for theBenchmark.p
% 3.22/0.98  
% 3.22/0.98  % SZS output start CNFRefutation for theBenchmark.p
% 3.22/0.98  
% 3.22/0.98  fof(f15,conjecture,(
% 3.22/0.98    ! [X0] : ((l1_orders_2(X0) & v1_yellow_0(X0) & v5_orders_2(X0) & v4_orders_2(X0) & v3_orders_2(X0) & ~v2_struct_0(X0)) => ! [X1] : ((m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & v13_waybel_0(X1,X0) & v2_waybel_0(X1,X0) & ~v1_xboole_0(X1)) => (v1_subset_1(X1,u1_struct_0(X0)) <=> ~r2_hidden(k3_yellow_0(X0),X1))))),
% 3.22/0.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.22/0.98  
% 3.22/0.98  fof(f16,negated_conjecture,(
% 3.22/0.98    ~! [X0] : ((l1_orders_2(X0) & v1_yellow_0(X0) & v5_orders_2(X0) & v4_orders_2(X0) & v3_orders_2(X0) & ~v2_struct_0(X0)) => ! [X1] : ((m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & v13_waybel_0(X1,X0) & v2_waybel_0(X1,X0) & ~v1_xboole_0(X1)) => (v1_subset_1(X1,u1_struct_0(X0)) <=> ~r2_hidden(k3_yellow_0(X0),X1))))),
% 3.22/0.98    inference(negated_conjecture,[],[f15])).
% 3.22/0.98  
% 3.22/0.98  fof(f17,plain,(
% 3.22/0.98    ~! [X0] : ((l1_orders_2(X0) & v1_yellow_0(X0) & v5_orders_2(X0) & v4_orders_2(X0) & v3_orders_2(X0) & ~v2_struct_0(X0)) => ! [X1] : ((m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & v13_waybel_0(X1,X0) & ~v1_xboole_0(X1)) => (v1_subset_1(X1,u1_struct_0(X0)) <=> ~r2_hidden(k3_yellow_0(X0),X1))))),
% 3.22/0.98    inference(pure_predicate_removal,[],[f16])).
% 3.22/0.98  
% 3.22/0.98  fof(f37,plain,(
% 3.22/0.98    ? [X0] : (? [X1] : ((v1_subset_1(X1,u1_struct_0(X0)) <~> ~r2_hidden(k3_yellow_0(X0),X1)) & (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & v13_waybel_0(X1,X0) & ~v1_xboole_0(X1))) & (l1_orders_2(X0) & v1_yellow_0(X0) & v5_orders_2(X0) & v4_orders_2(X0) & v3_orders_2(X0) & ~v2_struct_0(X0)))),
% 3.22/0.98    inference(ennf_transformation,[],[f17])).
% 3.22/0.98  
% 3.22/0.98  fof(f38,plain,(
% 3.22/0.98    ? [X0] : (? [X1] : ((v1_subset_1(X1,u1_struct_0(X0)) <~> ~r2_hidden(k3_yellow_0(X0),X1)) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & v13_waybel_0(X1,X0) & ~v1_xboole_0(X1)) & l1_orders_2(X0) & v1_yellow_0(X0) & v5_orders_2(X0) & v4_orders_2(X0) & v3_orders_2(X0) & ~v2_struct_0(X0))),
% 3.22/0.98    inference(flattening,[],[f37])).
% 3.22/0.98  
% 3.22/0.98  fof(f50,plain,(
% 3.22/0.98    ? [X0] : (? [X1] : (((r2_hidden(k3_yellow_0(X0),X1) | ~v1_subset_1(X1,u1_struct_0(X0))) & (~r2_hidden(k3_yellow_0(X0),X1) | v1_subset_1(X1,u1_struct_0(X0)))) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & v13_waybel_0(X1,X0) & ~v1_xboole_0(X1)) & l1_orders_2(X0) & v1_yellow_0(X0) & v5_orders_2(X0) & v4_orders_2(X0) & v3_orders_2(X0) & ~v2_struct_0(X0))),
% 3.22/0.98    inference(nnf_transformation,[],[f38])).
% 3.22/0.98  
% 3.22/0.98  fof(f51,plain,(
% 3.22/0.98    ? [X0] : (? [X1] : ((r2_hidden(k3_yellow_0(X0),X1) | ~v1_subset_1(X1,u1_struct_0(X0))) & (~r2_hidden(k3_yellow_0(X0),X1) | v1_subset_1(X1,u1_struct_0(X0))) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & v13_waybel_0(X1,X0) & ~v1_xboole_0(X1)) & l1_orders_2(X0) & v1_yellow_0(X0) & v5_orders_2(X0) & v4_orders_2(X0) & v3_orders_2(X0) & ~v2_struct_0(X0))),
% 3.22/0.98    inference(flattening,[],[f50])).
% 3.22/0.98  
% 3.22/0.98  fof(f53,plain,(
% 3.22/0.98    ( ! [X0] : (? [X1] : ((r2_hidden(k3_yellow_0(X0),X1) | ~v1_subset_1(X1,u1_struct_0(X0))) & (~r2_hidden(k3_yellow_0(X0),X1) | v1_subset_1(X1,u1_struct_0(X0))) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & v13_waybel_0(X1,X0) & ~v1_xboole_0(X1)) => ((r2_hidden(k3_yellow_0(X0),sK4) | ~v1_subset_1(sK4,u1_struct_0(X0))) & (~r2_hidden(k3_yellow_0(X0),sK4) | v1_subset_1(sK4,u1_struct_0(X0))) & m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(X0))) & v13_waybel_0(sK4,X0) & ~v1_xboole_0(sK4))) )),
% 3.22/0.98    introduced(choice_axiom,[])).
% 3.22/0.98  
% 3.22/0.98  fof(f52,plain,(
% 3.22/0.98    ? [X0] : (? [X1] : ((r2_hidden(k3_yellow_0(X0),X1) | ~v1_subset_1(X1,u1_struct_0(X0))) & (~r2_hidden(k3_yellow_0(X0),X1) | v1_subset_1(X1,u1_struct_0(X0))) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & v13_waybel_0(X1,X0) & ~v1_xboole_0(X1)) & l1_orders_2(X0) & v1_yellow_0(X0) & v5_orders_2(X0) & v4_orders_2(X0) & v3_orders_2(X0) & ~v2_struct_0(X0)) => (? [X1] : ((r2_hidden(k3_yellow_0(sK3),X1) | ~v1_subset_1(X1,u1_struct_0(sK3))) & (~r2_hidden(k3_yellow_0(sK3),X1) | v1_subset_1(X1,u1_struct_0(sK3))) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK3))) & v13_waybel_0(X1,sK3) & ~v1_xboole_0(X1)) & l1_orders_2(sK3) & v1_yellow_0(sK3) & v5_orders_2(sK3) & v4_orders_2(sK3) & v3_orders_2(sK3) & ~v2_struct_0(sK3))),
% 3.22/0.98    introduced(choice_axiom,[])).
% 3.22/0.98  
% 3.22/0.98  fof(f54,plain,(
% 3.22/0.98    ((r2_hidden(k3_yellow_0(sK3),sK4) | ~v1_subset_1(sK4,u1_struct_0(sK3))) & (~r2_hidden(k3_yellow_0(sK3),sK4) | v1_subset_1(sK4,u1_struct_0(sK3))) & m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(sK3))) & v13_waybel_0(sK4,sK3) & ~v1_xboole_0(sK4)) & l1_orders_2(sK3) & v1_yellow_0(sK3) & v5_orders_2(sK3) & v4_orders_2(sK3) & v3_orders_2(sK3) & ~v2_struct_0(sK3)),
% 3.22/0.98    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3,sK4])],[f51,f53,f52])).
% 3.22/0.98  
% 3.22/0.98  fof(f88,plain,(
% 3.22/0.98    m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(sK3)))),
% 3.22/0.98    inference(cnf_transformation,[],[f54])).
% 3.22/0.98  
% 3.22/0.98  fof(f5,axiom,(
% 3.22/0.98    ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) <=> r1_tarski(X0,X1))),
% 3.22/0.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.22/0.98  
% 3.22/0.98  fof(f43,plain,(
% 3.22/0.98    ! [X0,X1] : ((m1_subset_1(X0,k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1)) & (r1_tarski(X0,X1) | ~m1_subset_1(X0,k1_zfmisc_1(X1))))),
% 3.22/0.98    inference(nnf_transformation,[],[f5])).
% 3.22/0.98  
% 3.22/0.98  fof(f62,plain,(
% 3.22/0.98    ( ! [X0,X1] : (r1_tarski(X0,X1) | ~m1_subset_1(X0,k1_zfmisc_1(X1))) )),
% 3.22/0.98    inference(cnf_transformation,[],[f43])).
% 3.22/0.98  
% 3.22/0.98  fof(f3,axiom,(
% 3.22/0.98    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => (! [X2] : (m1_subset_1(X2,X0) => r2_hidden(X2,X1)) => X0 = X1))),
% 3.22/0.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.22/0.98  
% 3.22/0.98  fof(f19,plain,(
% 3.22/0.98    ! [X0,X1] : ((X0 = X1 | ? [X2] : (~r2_hidden(X2,X1) & m1_subset_1(X2,X0))) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 3.22/0.98    inference(ennf_transformation,[],[f3])).
% 3.22/0.98  
% 3.22/0.98  fof(f20,plain,(
% 3.22/0.98    ! [X0,X1] : (X0 = X1 | ? [X2] : (~r2_hidden(X2,X1) & m1_subset_1(X2,X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 3.22/0.98    inference(flattening,[],[f19])).
% 3.22/0.98  
% 3.22/0.98  fof(f41,plain,(
% 3.22/0.98    ! [X1,X0] : (? [X2] : (~r2_hidden(X2,X1) & m1_subset_1(X2,X0)) => (~r2_hidden(sK0(X0,X1),X1) & m1_subset_1(sK0(X0,X1),X0)))),
% 3.22/0.98    introduced(choice_axiom,[])).
% 3.22/0.98  
% 3.22/0.98  fof(f42,plain,(
% 3.22/0.98    ! [X0,X1] : (X0 = X1 | (~r2_hidden(sK0(X0,X1),X1) & m1_subset_1(sK0(X0,X1),X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 3.22/0.98    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f20,f41])).
% 3.22/0.98  
% 3.22/0.98  fof(f59,plain,(
% 3.22/0.98    ( ! [X0,X1] : (X0 = X1 | m1_subset_1(sK0(X0,X1),X0) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 3.22/0.98    inference(cnf_transformation,[],[f42])).
% 3.22/0.98  
% 3.22/0.98  fof(f63,plain,(
% 3.22/0.98    ( ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1)) )),
% 3.22/0.98    inference(cnf_transformation,[],[f43])).
% 3.22/0.98  
% 3.22/0.98  fof(f13,axiom,(
% 3.22/0.98    ! [X0] : ((l1_orders_2(X0) & v5_orders_2(X0) & v4_orders_2(X0) & v3_orders_2(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,u1_struct_0(X0)) => (k1_yellow_0(X0,k5_waybel_0(X0,X1)) = X1 & r1_yellow_0(X0,k5_waybel_0(X0,X1)))))),
% 3.22/0.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.22/0.98  
% 3.22/0.98  fof(f34,plain,(
% 3.22/0.98    ! [X0] : (! [X1] : ((k1_yellow_0(X0,k5_waybel_0(X0,X1)) = X1 & r1_yellow_0(X0,k5_waybel_0(X0,X1))) | ~m1_subset_1(X1,u1_struct_0(X0))) | (~l1_orders_2(X0) | ~v5_orders_2(X0) | ~v4_orders_2(X0) | ~v3_orders_2(X0) | v2_struct_0(X0)))),
% 3.22/0.98    inference(ennf_transformation,[],[f13])).
% 3.22/0.98  
% 3.22/0.98  fof(f35,plain,(
% 3.22/0.98    ! [X0] : (! [X1] : ((k1_yellow_0(X0,k5_waybel_0(X0,X1)) = X1 & r1_yellow_0(X0,k5_waybel_0(X0,X1))) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~l1_orders_2(X0) | ~v5_orders_2(X0) | ~v4_orders_2(X0) | ~v3_orders_2(X0) | v2_struct_0(X0))),
% 3.22/0.98    inference(flattening,[],[f34])).
% 3.22/0.98  
% 3.22/0.98  fof(f77,plain,(
% 3.22/0.98    ( ! [X0,X1] : (k1_yellow_0(X0,k5_waybel_0(X0,X1)) = X1 | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_orders_2(X0) | ~v5_orders_2(X0) | ~v4_orders_2(X0) | ~v3_orders_2(X0) | v2_struct_0(X0)) )),
% 3.22/0.98    inference(cnf_transformation,[],[f35])).
% 3.22/0.98  
% 3.22/0.98  fof(f83,plain,(
% 3.22/0.98    v5_orders_2(sK3)),
% 3.22/0.98    inference(cnf_transformation,[],[f54])).
% 3.22/0.98  
% 3.22/0.98  fof(f80,plain,(
% 3.22/0.98    ~v2_struct_0(sK3)),
% 3.22/0.98    inference(cnf_transformation,[],[f54])).
% 3.22/0.98  
% 3.22/0.98  fof(f81,plain,(
% 3.22/0.98    v3_orders_2(sK3)),
% 3.22/0.98    inference(cnf_transformation,[],[f54])).
% 3.22/0.98  
% 3.22/0.98  fof(f82,plain,(
% 3.22/0.98    v4_orders_2(sK3)),
% 3.22/0.98    inference(cnf_transformation,[],[f54])).
% 3.22/0.98  
% 3.22/0.98  fof(f85,plain,(
% 3.22/0.98    l1_orders_2(sK3)),
% 3.22/0.98    inference(cnf_transformation,[],[f54])).
% 3.22/0.98  
% 3.22/0.98  fof(f8,axiom,(
% 3.22/0.98    ! [X0,X1] : (l1_orders_2(X0) => m1_subset_1(k1_yellow_0(X0,X1),u1_struct_0(X0)))),
% 3.22/0.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.22/0.98  
% 3.22/0.98  fof(f26,plain,(
% 3.22/0.98    ! [X0,X1] : (m1_subset_1(k1_yellow_0(X0,X1),u1_struct_0(X0)) | ~l1_orders_2(X0))),
% 3.22/0.98    inference(ennf_transformation,[],[f8])).
% 3.22/0.98  
% 3.22/0.98  fof(f66,plain,(
% 3.22/0.98    ( ! [X0,X1] : (m1_subset_1(k1_yellow_0(X0,X1),u1_struct_0(X0)) | ~l1_orders_2(X0)) )),
% 3.22/0.98    inference(cnf_transformation,[],[f26])).
% 3.22/0.98  
% 3.22/0.98  fof(f14,axiom,(
% 3.22/0.98    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => (v1_subset_1(X1,X0) <=> X0 != X1))),
% 3.22/0.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.22/0.98  
% 3.22/0.98  fof(f36,plain,(
% 3.22/0.98    ! [X0,X1] : ((v1_subset_1(X1,X0) <=> X0 != X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 3.22/0.98    inference(ennf_transformation,[],[f14])).
% 3.22/0.98  
% 3.22/0.98  fof(f49,plain,(
% 3.22/0.98    ! [X0,X1] : (((v1_subset_1(X1,X0) | X0 = X1) & (X0 != X1 | ~v1_subset_1(X1,X0))) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 3.22/0.98    inference(nnf_transformation,[],[f36])).
% 3.22/0.98  
% 3.22/0.98  fof(f79,plain,(
% 3.22/0.98    ( ! [X0,X1] : (v1_subset_1(X1,X0) | X0 = X1 | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 3.22/0.98    inference(cnf_transformation,[],[f49])).
% 3.22/0.98  
% 3.22/0.98  fof(f90,plain,(
% 3.22/0.98    r2_hidden(k3_yellow_0(sK3),sK4) | ~v1_subset_1(sK4,u1_struct_0(sK3))),
% 3.22/0.98    inference(cnf_transformation,[],[f54])).
% 3.22/0.98  
% 3.22/0.98  fof(f78,plain,(
% 3.22/0.98    ( ! [X0,X1] : (X0 != X1 | ~v1_subset_1(X1,X0) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 3.22/0.98    inference(cnf_transformation,[],[f49])).
% 3.22/0.98  
% 3.22/0.98  fof(f93,plain,(
% 3.22/0.98    ( ! [X1] : (~v1_subset_1(X1,X1) | ~m1_subset_1(X1,k1_zfmisc_1(X1))) )),
% 3.22/0.98    inference(equality_resolution,[],[f78])).
% 3.22/0.98  
% 3.22/0.98  fof(f89,plain,(
% 3.22/0.98    ~r2_hidden(k3_yellow_0(sK3),sK4) | v1_subset_1(sK4,u1_struct_0(sK3))),
% 3.22/0.98    inference(cnf_transformation,[],[f54])).
% 3.22/0.98  
% 3.22/0.98  fof(f1,axiom,(
% 3.22/0.98    ! [X0,X1] : (X0 = X1 <=> (r1_tarski(X1,X0) & r1_tarski(X0,X1)))),
% 3.22/0.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.22/0.98  
% 3.22/0.98  fof(f39,plain,(
% 3.22/0.98    ! [X0,X1] : ((X0 = X1 | (~r1_tarski(X1,X0) | ~r1_tarski(X0,X1))) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 3.22/0.98    inference(nnf_transformation,[],[f1])).
% 3.22/0.98  
% 3.22/0.98  fof(f40,plain,(
% 3.22/0.98    ! [X0,X1] : ((X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 3.22/0.98    inference(flattening,[],[f39])).
% 3.22/0.98  
% 3.22/0.98  fof(f56,plain,(
% 3.22/0.98    ( ! [X0,X1] : (r1_tarski(X1,X0) | X0 != X1) )),
% 3.22/0.98    inference(cnf_transformation,[],[f40])).
% 3.22/0.98  
% 3.22/0.98  fof(f91,plain,(
% 3.22/0.98    ( ! [X1] : (r1_tarski(X1,X1)) )),
% 3.22/0.98    inference(equality_resolution,[],[f56])).
% 3.22/0.98  
% 3.22/0.98  fof(f60,plain,(
% 3.22/0.98    ( ! [X0,X1] : (X0 = X1 | ~r2_hidden(sK0(X0,X1),X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 3.22/0.98    inference(cnf_transformation,[],[f42])).
% 3.22/0.98  
% 3.22/0.98  fof(f7,axiom,(
% 3.22/0.98    ! [X0] : (l1_orders_2(X0) => k3_yellow_0(X0) = k1_yellow_0(X0,k1_xboole_0))),
% 3.22/0.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.22/0.98  
% 3.22/0.98  fof(f25,plain,(
% 3.22/0.98    ! [X0] : (k3_yellow_0(X0) = k1_yellow_0(X0,k1_xboole_0) | ~l1_orders_2(X0))),
% 3.22/0.98    inference(ennf_transformation,[],[f7])).
% 3.22/0.98  
% 3.22/0.98  fof(f65,plain,(
% 3.22/0.98    ( ! [X0] : (k3_yellow_0(X0) = k1_yellow_0(X0,k1_xboole_0) | ~l1_orders_2(X0)) )),
% 3.22/0.98    inference(cnf_transformation,[],[f25])).
% 3.22/0.98  
% 3.22/0.98  fof(f10,axiom,(
% 3.22/0.98    ! [X0] : (l1_orders_2(X0) => ! [X1,X2] : ((r1_yellow_0(X0,X2) & r1_yellow_0(X0,X1) & r1_tarski(X1,X2)) => r1_orders_2(X0,k1_yellow_0(X0,X1),k1_yellow_0(X0,X2))))),
% 3.22/0.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.22/0.98  
% 3.22/0.98  fof(f28,plain,(
% 3.22/0.98    ! [X0] : (! [X1,X2] : (r1_orders_2(X0,k1_yellow_0(X0,X1),k1_yellow_0(X0,X2)) | (~r1_yellow_0(X0,X2) | ~r1_yellow_0(X0,X1) | ~r1_tarski(X1,X2))) | ~l1_orders_2(X0))),
% 3.22/0.98    inference(ennf_transformation,[],[f10])).
% 3.22/0.98  
% 3.22/0.98  fof(f29,plain,(
% 3.22/0.98    ! [X0] : (! [X1,X2] : (r1_orders_2(X0,k1_yellow_0(X0,X1),k1_yellow_0(X0,X2)) | ~r1_yellow_0(X0,X2) | ~r1_yellow_0(X0,X1) | ~r1_tarski(X1,X2)) | ~l1_orders_2(X0))),
% 3.22/0.98    inference(flattening,[],[f28])).
% 3.22/0.98  
% 3.22/0.98  fof(f68,plain,(
% 3.22/0.98    ( ! [X2,X0,X1] : (r1_orders_2(X0,k1_yellow_0(X0,X1),k1_yellow_0(X0,X2)) | ~r1_yellow_0(X0,X2) | ~r1_yellow_0(X0,X1) | ~r1_tarski(X1,X2) | ~l1_orders_2(X0)) )),
% 3.22/0.98    inference(cnf_transformation,[],[f29])).
% 3.22/0.98  
% 3.22/0.98  fof(f84,plain,(
% 3.22/0.98    v1_yellow_0(sK3)),
% 3.22/0.98    inference(cnf_transformation,[],[f54])).
% 3.22/0.98  
% 3.22/0.98  fof(f11,axiom,(
% 3.22/0.98    ! [X0] : ((l1_orders_2(X0) & v1_yellow_0(X0) & v5_orders_2(X0) & ~v2_struct_0(X0)) => (r2_yellow_0(X0,u1_struct_0(X0)) & r1_yellow_0(X0,k1_xboole_0)))),
% 3.22/0.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.22/0.98  
% 3.22/0.98  fof(f18,plain,(
% 3.22/0.98    ! [X0] : ((l1_orders_2(X0) & v1_yellow_0(X0) & v5_orders_2(X0) & ~v2_struct_0(X0)) => r1_yellow_0(X0,k1_xboole_0))),
% 3.22/0.98    inference(pure_predicate_removal,[],[f11])).
% 3.22/0.98  
% 3.22/0.98  fof(f30,plain,(
% 3.22/0.98    ! [X0] : (r1_yellow_0(X0,k1_xboole_0) | (~l1_orders_2(X0) | ~v1_yellow_0(X0) | ~v5_orders_2(X0) | v2_struct_0(X0)))),
% 3.22/0.98    inference(ennf_transformation,[],[f18])).
% 3.22/0.98  
% 3.22/0.98  fof(f31,plain,(
% 3.22/0.98    ! [X0] : (r1_yellow_0(X0,k1_xboole_0) | ~l1_orders_2(X0) | ~v1_yellow_0(X0) | ~v5_orders_2(X0) | v2_struct_0(X0))),
% 3.22/0.98    inference(flattening,[],[f30])).
% 3.22/0.98  
% 3.22/0.98  fof(f69,plain,(
% 3.22/0.98    ( ! [X0] : (r1_yellow_0(X0,k1_xboole_0) | ~l1_orders_2(X0) | ~v1_yellow_0(X0) | ~v5_orders_2(X0) | v2_struct_0(X0)) )),
% 3.22/0.98    inference(cnf_transformation,[],[f31])).
% 3.22/0.98  
% 3.22/0.98  fof(f2,axiom,(
% 3.22/0.98    ! [X0] : r1_tarski(k1_xboole_0,X0)),
% 3.22/0.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.22/0.98  
% 3.22/0.98  fof(f58,plain,(
% 3.22/0.98    ( ! [X0] : (r1_tarski(k1_xboole_0,X0)) )),
% 3.22/0.98    inference(cnf_transformation,[],[f2])).
% 3.22/0.98  
% 3.22/0.98  fof(f76,plain,(
% 3.22/0.98    ( ! [X0,X1] : (r1_yellow_0(X0,k5_waybel_0(X0,X1)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_orders_2(X0) | ~v5_orders_2(X0) | ~v4_orders_2(X0) | ~v3_orders_2(X0) | v2_struct_0(X0)) )),
% 3.22/0.98    inference(cnf_transformation,[],[f35])).
% 3.22/0.98  
% 3.22/0.98  fof(f12,axiom,(
% 3.22/0.98    ! [X0] : (l1_orders_2(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => (v13_waybel_0(X1,X0) <=> ! [X2] : (m1_subset_1(X2,u1_struct_0(X0)) => ! [X3] : (m1_subset_1(X3,u1_struct_0(X0)) => ((r1_orders_2(X0,X2,X3) & r2_hidden(X2,X1)) => r2_hidden(X3,X1)))))))),
% 3.22/0.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.22/0.98  
% 3.22/0.98  fof(f32,plain,(
% 3.22/0.98    ! [X0] : (! [X1] : ((v13_waybel_0(X1,X0) <=> ! [X2] : (! [X3] : ((r2_hidden(X3,X1) | (~r1_orders_2(X0,X2,X3) | ~r2_hidden(X2,X1))) | ~m1_subset_1(X3,u1_struct_0(X0))) | ~m1_subset_1(X2,u1_struct_0(X0)))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_orders_2(X0))),
% 3.22/0.98    inference(ennf_transformation,[],[f12])).
% 3.22/0.98  
% 3.22/0.98  fof(f33,plain,(
% 3.22/0.98    ! [X0] : (! [X1] : ((v13_waybel_0(X1,X0) <=> ! [X2] : (! [X3] : (r2_hidden(X3,X1) | ~r1_orders_2(X0,X2,X3) | ~r2_hidden(X2,X1) | ~m1_subset_1(X3,u1_struct_0(X0))) | ~m1_subset_1(X2,u1_struct_0(X0)))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_orders_2(X0))),
% 3.22/0.98    inference(flattening,[],[f32])).
% 3.22/0.98  
% 3.22/0.98  fof(f44,plain,(
% 3.22/0.98    ! [X0] : (! [X1] : (((v13_waybel_0(X1,X0) | ? [X2] : (? [X3] : (~r2_hidden(X3,X1) & r1_orders_2(X0,X2,X3) & r2_hidden(X2,X1) & m1_subset_1(X3,u1_struct_0(X0))) & m1_subset_1(X2,u1_struct_0(X0)))) & (! [X2] : (! [X3] : (r2_hidden(X3,X1) | ~r1_orders_2(X0,X2,X3) | ~r2_hidden(X2,X1) | ~m1_subset_1(X3,u1_struct_0(X0))) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~v13_waybel_0(X1,X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_orders_2(X0))),
% 3.22/0.98    inference(nnf_transformation,[],[f33])).
% 3.22/0.98  
% 3.22/0.98  fof(f45,plain,(
% 3.22/0.98    ! [X0] : (! [X1] : (((v13_waybel_0(X1,X0) | ? [X2] : (? [X3] : (~r2_hidden(X3,X1) & r1_orders_2(X0,X2,X3) & r2_hidden(X2,X1) & m1_subset_1(X3,u1_struct_0(X0))) & m1_subset_1(X2,u1_struct_0(X0)))) & (! [X4] : (! [X5] : (r2_hidden(X5,X1) | ~r1_orders_2(X0,X4,X5) | ~r2_hidden(X4,X1) | ~m1_subset_1(X5,u1_struct_0(X0))) | ~m1_subset_1(X4,u1_struct_0(X0))) | ~v13_waybel_0(X1,X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_orders_2(X0))),
% 3.22/0.98    inference(rectify,[],[f44])).
% 3.22/0.98  
% 3.22/0.98  fof(f47,plain,(
% 3.22/0.98    ( ! [X2] : (! [X1,X0] : (? [X3] : (~r2_hidden(X3,X1) & r1_orders_2(X0,X2,X3) & r2_hidden(X2,X1) & m1_subset_1(X3,u1_struct_0(X0))) => (~r2_hidden(sK2(X0,X1),X1) & r1_orders_2(X0,X2,sK2(X0,X1)) & r2_hidden(X2,X1) & m1_subset_1(sK2(X0,X1),u1_struct_0(X0))))) )),
% 3.22/0.98    introduced(choice_axiom,[])).
% 3.22/0.98  
% 3.22/0.98  fof(f46,plain,(
% 3.22/0.98    ! [X1,X0] : (? [X2] : (? [X3] : (~r2_hidden(X3,X1) & r1_orders_2(X0,X2,X3) & r2_hidden(X2,X1) & m1_subset_1(X3,u1_struct_0(X0))) & m1_subset_1(X2,u1_struct_0(X0))) => (? [X3] : (~r2_hidden(X3,X1) & r1_orders_2(X0,sK1(X0,X1),X3) & r2_hidden(sK1(X0,X1),X1) & m1_subset_1(X3,u1_struct_0(X0))) & m1_subset_1(sK1(X0,X1),u1_struct_0(X0))))),
% 3.22/0.98    introduced(choice_axiom,[])).
% 3.22/0.98  
% 3.22/0.98  fof(f48,plain,(
% 3.22/0.98    ! [X0] : (! [X1] : (((v13_waybel_0(X1,X0) | ((~r2_hidden(sK2(X0,X1),X1) & r1_orders_2(X0,sK1(X0,X1),sK2(X0,X1)) & r2_hidden(sK1(X0,X1),X1) & m1_subset_1(sK2(X0,X1),u1_struct_0(X0))) & m1_subset_1(sK1(X0,X1),u1_struct_0(X0)))) & (! [X4] : (! [X5] : (r2_hidden(X5,X1) | ~r1_orders_2(X0,X4,X5) | ~r2_hidden(X4,X1) | ~m1_subset_1(X5,u1_struct_0(X0))) | ~m1_subset_1(X4,u1_struct_0(X0))) | ~v13_waybel_0(X1,X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_orders_2(X0))),
% 3.22/0.98    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1,sK2])],[f45,f47,f46])).
% 3.22/0.98  
% 3.22/0.98  fof(f70,plain,(
% 3.22/0.98    ( ! [X4,X0,X5,X1] : (r2_hidden(X5,X1) | ~r1_orders_2(X0,X4,X5) | ~r2_hidden(X4,X1) | ~m1_subset_1(X5,u1_struct_0(X0)) | ~m1_subset_1(X4,u1_struct_0(X0)) | ~v13_waybel_0(X1,X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_orders_2(X0)) )),
% 3.22/0.98    inference(cnf_transformation,[],[f48])).
% 3.22/0.98  
% 3.22/0.98  fof(f6,axiom,(
% 3.22/0.98    ! [X0,X1,X2] : ((m1_subset_1(X1,k1_zfmisc_1(X2)) & r2_hidden(X0,X1)) => m1_subset_1(X0,X2))),
% 3.22/0.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.22/0.98  
% 3.22/0.98  fof(f23,plain,(
% 3.22/0.98    ! [X0,X1,X2] : (m1_subset_1(X0,X2) | (~m1_subset_1(X1,k1_zfmisc_1(X2)) | ~r2_hidden(X0,X1)))),
% 3.22/0.98    inference(ennf_transformation,[],[f6])).
% 3.22/0.98  
% 3.22/0.98  fof(f24,plain,(
% 3.22/0.98    ! [X0,X1,X2] : (m1_subset_1(X0,X2) | ~m1_subset_1(X1,k1_zfmisc_1(X2)) | ~r2_hidden(X0,X1))),
% 3.22/0.98    inference(flattening,[],[f23])).
% 3.22/0.98  
% 3.22/0.98  fof(f64,plain,(
% 3.22/0.98    ( ! [X2,X0,X1] : (m1_subset_1(X0,X2) | ~m1_subset_1(X1,k1_zfmisc_1(X2)) | ~r2_hidden(X0,X1)) )),
% 3.22/0.98    inference(cnf_transformation,[],[f24])).
% 3.22/0.98  
% 3.22/0.98  fof(f87,plain,(
% 3.22/0.98    v13_waybel_0(sK4,sK3)),
% 3.22/0.98    inference(cnf_transformation,[],[f54])).
% 3.22/0.98  
% 3.22/0.98  fof(f9,axiom,(
% 3.22/0.98    ! [X0] : (l1_orders_2(X0) => m1_subset_1(k3_yellow_0(X0),u1_struct_0(X0)))),
% 3.22/0.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.22/0.98  
% 3.22/0.98  fof(f27,plain,(
% 3.22/0.98    ! [X0] : (m1_subset_1(k3_yellow_0(X0),u1_struct_0(X0)) | ~l1_orders_2(X0))),
% 3.22/0.98    inference(ennf_transformation,[],[f9])).
% 3.22/0.98  
% 3.22/0.98  fof(f67,plain,(
% 3.22/0.98    ( ! [X0] : (m1_subset_1(k3_yellow_0(X0),u1_struct_0(X0)) | ~l1_orders_2(X0)) )),
% 3.22/0.98    inference(cnf_transformation,[],[f27])).
% 3.22/0.98  
% 3.22/0.98  fof(f4,axiom,(
% 3.22/0.98    ! [X0,X1] : (m1_subset_1(X0,X1) => (r2_hidden(X0,X1) | v1_xboole_0(X1)))),
% 3.22/0.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.22/0.98  
% 3.22/0.98  fof(f21,plain,(
% 3.22/0.98    ! [X0,X1] : ((r2_hidden(X0,X1) | v1_xboole_0(X1)) | ~m1_subset_1(X0,X1))),
% 3.22/0.98    inference(ennf_transformation,[],[f4])).
% 3.22/0.98  
% 3.22/0.98  fof(f22,plain,(
% 3.22/0.98    ! [X0,X1] : (r2_hidden(X0,X1) | v1_xboole_0(X1) | ~m1_subset_1(X0,X1))),
% 3.22/0.98    inference(flattening,[],[f21])).
% 3.22/0.98  
% 3.22/0.98  fof(f61,plain,(
% 3.22/0.98    ( ! [X0,X1] : (r2_hidden(X0,X1) | v1_xboole_0(X1) | ~m1_subset_1(X0,X1)) )),
% 3.22/0.98    inference(cnf_transformation,[],[f22])).
% 3.22/0.98  
% 3.22/0.98  fof(f86,plain,(
% 3.22/0.98    ~v1_xboole_0(sK4)),
% 3.22/0.98    inference(cnf_transformation,[],[f54])).
% 3.22/0.98  
% 3.22/0.98  cnf(c_27,negated_conjecture,
% 3.22/0.98      ( m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(sK3))) ),
% 3.22/0.98      inference(cnf_transformation,[],[f88]) ).
% 3.22/0.98  
% 3.22/0.98  cnf(c_2174,plain,
% 3.22/0.98      ( m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(sK3))) = iProver_top ),
% 3.22/0.98      inference(predicate_to_equality,[status(thm)],[c_27]) ).
% 3.22/0.98  
% 3.22/0.98  cnf(c_8,plain,
% 3.22/0.98      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1)) | r1_tarski(X0,X1) ),
% 3.22/0.98      inference(cnf_transformation,[],[f62]) ).
% 3.22/0.98  
% 3.22/0.98  cnf(c_2176,plain,
% 3.22/0.98      ( m1_subset_1(X0,k1_zfmisc_1(X1)) != iProver_top
% 3.22/0.98      | r1_tarski(X0,X1) = iProver_top ),
% 3.22/0.98      inference(predicate_to_equality,[status(thm)],[c_8]) ).
% 3.22/0.98  
% 3.22/0.98  cnf(c_2688,plain,
% 3.22/0.98      ( r1_tarski(sK4,u1_struct_0(sK3)) = iProver_top ),
% 3.22/0.98      inference(superposition,[status(thm)],[c_2174,c_2176]) ).
% 3.22/0.98  
% 3.22/0.98  cnf(c_5,plain,
% 3.22/0.98      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
% 3.22/0.98      | m1_subset_1(sK0(X1,X0),X1)
% 3.22/0.98      | X0 = X1 ),
% 3.22/0.98      inference(cnf_transformation,[],[f59]) ).
% 3.22/0.98  
% 3.22/0.98  cnf(c_7,plain,
% 3.22/0.98      ( m1_subset_1(X0,k1_zfmisc_1(X1)) | ~ r1_tarski(X0,X1) ),
% 3.22/0.98      inference(cnf_transformation,[],[f63]) ).
% 3.22/0.98  
% 3.22/0.98  cnf(c_271,plain,
% 3.22/0.98      ( ~ r1_tarski(X0,X1) | m1_subset_1(X0,k1_zfmisc_1(X1)) ),
% 3.22/0.98      inference(prop_impl,[status(thm)],[c_7]) ).
% 3.22/0.98  
% 3.22/0.98  cnf(c_272,plain,
% 3.22/0.98      ( m1_subset_1(X0,k1_zfmisc_1(X1)) | ~ r1_tarski(X0,X1) ),
% 3.22/0.98      inference(renaming,[status(thm)],[c_271]) ).
% 3.22/0.98  
% 3.22/0.98  cnf(c_348,plain,
% 3.22/0.98      ( m1_subset_1(sK0(X0,X1),X0) | ~ r1_tarski(X1,X0) | X1 = X0 ),
% 3.22/0.98      inference(bin_hyper_res,[status(thm)],[c_5,c_272]) ).
% 3.22/0.98  
% 3.22/0.98  cnf(c_2171,plain,
% 3.22/0.98      ( X0 = X1
% 3.22/0.98      | m1_subset_1(sK0(X1,X0),X1) = iProver_top
% 3.22/0.98      | r1_tarski(X0,X1) != iProver_top ),
% 3.22/0.98      inference(predicate_to_equality,[status(thm)],[c_348]) ).
% 3.22/0.98  
% 3.22/0.98  cnf(c_21,plain,
% 3.22/0.98      ( ~ m1_subset_1(X0,u1_struct_0(X1))
% 3.22/0.98      | ~ v3_orders_2(X1)
% 3.22/0.98      | ~ v4_orders_2(X1)
% 3.22/0.98      | v2_struct_0(X1)
% 3.22/0.98      | ~ v5_orders_2(X1)
% 3.22/0.98      | ~ l1_orders_2(X1)
% 3.22/0.98      | k1_yellow_0(X1,k5_waybel_0(X1,X0)) = X0 ),
% 3.22/0.98      inference(cnf_transformation,[],[f77]) ).
% 3.22/0.98  
% 3.22/0.98  cnf(c_32,negated_conjecture,
% 3.22/0.98      ( v5_orders_2(sK3) ),
% 3.22/0.98      inference(cnf_transformation,[],[f83]) ).
% 3.22/0.98  
% 3.22/0.98  cnf(c_563,plain,
% 3.22/0.98      ( ~ m1_subset_1(X0,u1_struct_0(X1))
% 3.22/0.98      | ~ v3_orders_2(X1)
% 3.22/0.98      | ~ v4_orders_2(X1)
% 3.22/0.98      | v2_struct_0(X1)
% 3.22/0.98      | ~ l1_orders_2(X1)
% 3.22/0.98      | k1_yellow_0(X1,k5_waybel_0(X1,X0)) = X0
% 3.22/0.98      | sK3 != X1 ),
% 3.22/0.98      inference(resolution_lifted,[status(thm)],[c_21,c_32]) ).
% 3.22/0.98  
% 3.22/0.98  cnf(c_564,plain,
% 3.22/0.98      ( ~ m1_subset_1(X0,u1_struct_0(sK3))
% 3.22/0.98      | ~ v3_orders_2(sK3)
% 3.22/0.98      | ~ v4_orders_2(sK3)
% 3.22/0.98      | v2_struct_0(sK3)
% 3.22/0.98      | ~ l1_orders_2(sK3)
% 3.22/0.98      | k1_yellow_0(sK3,k5_waybel_0(sK3,X0)) = X0 ),
% 3.22/0.98      inference(unflattening,[status(thm)],[c_563]) ).
% 3.22/0.98  
% 3.22/0.98  cnf(c_35,negated_conjecture,
% 3.22/0.98      ( ~ v2_struct_0(sK3) ),
% 3.22/0.98      inference(cnf_transformation,[],[f80]) ).
% 3.22/0.98  
% 3.22/0.98  cnf(c_34,negated_conjecture,
% 3.22/0.98      ( v3_orders_2(sK3) ),
% 3.22/0.98      inference(cnf_transformation,[],[f81]) ).
% 3.22/0.98  
% 3.22/0.98  cnf(c_33,negated_conjecture,
% 3.22/0.98      ( v4_orders_2(sK3) ),
% 3.22/0.98      inference(cnf_transformation,[],[f82]) ).
% 3.22/0.98  
% 3.22/0.98  cnf(c_30,negated_conjecture,
% 3.22/0.98      ( l1_orders_2(sK3) ),
% 3.22/0.98      inference(cnf_transformation,[],[f85]) ).
% 3.22/0.98  
% 3.22/0.98  cnf(c_568,plain,
% 3.22/0.98      ( ~ m1_subset_1(X0,u1_struct_0(sK3))
% 3.22/0.98      | k1_yellow_0(sK3,k5_waybel_0(sK3,X0)) = X0 ),
% 3.22/0.98      inference(global_propositional_subsumption,
% 3.22/0.98                [status(thm)],
% 3.22/0.98                [c_564,c_35,c_34,c_33,c_30]) ).
% 3.22/0.98  
% 3.22/0.98  cnf(c_2165,plain,
% 3.22/0.98      ( k1_yellow_0(sK3,k5_waybel_0(sK3,X0)) = X0
% 3.22/0.98      | m1_subset_1(X0,u1_struct_0(sK3)) != iProver_top ),
% 3.22/0.98      inference(predicate_to_equality,[status(thm)],[c_568]) ).
% 3.22/0.98  
% 3.22/0.98  cnf(c_4102,plain,
% 3.22/0.98      ( k1_yellow_0(sK3,k5_waybel_0(sK3,sK0(u1_struct_0(sK3),X0))) = sK0(u1_struct_0(sK3),X0)
% 3.22/0.98      | u1_struct_0(sK3) = X0
% 3.22/0.98      | r1_tarski(X0,u1_struct_0(sK3)) != iProver_top ),
% 3.22/0.98      inference(superposition,[status(thm)],[c_2171,c_2165]) ).
% 3.22/0.98  
% 3.22/0.98  cnf(c_6958,plain,
% 3.22/0.98      ( k1_yellow_0(sK3,k5_waybel_0(sK3,sK0(u1_struct_0(sK3),sK4))) = sK0(u1_struct_0(sK3),sK4)
% 3.22/0.98      | u1_struct_0(sK3) = sK4 ),
% 3.22/0.98      inference(superposition,[status(thm)],[c_2688,c_4102]) ).
% 3.22/0.98  
% 3.22/0.98  cnf(c_11,plain,
% 3.22/0.98      ( m1_subset_1(k1_yellow_0(X0,X1),u1_struct_0(X0))
% 3.22/0.98      | ~ l1_orders_2(X0) ),
% 3.22/0.98      inference(cnf_transformation,[],[f66]) ).
% 3.22/0.98  
% 3.22/0.98  cnf(c_730,plain,
% 3.22/0.98      ( m1_subset_1(k1_yellow_0(X0,X1),u1_struct_0(X0)) | sK3 != X0 ),
% 3.22/0.98      inference(resolution_lifted,[status(thm)],[c_11,c_30]) ).
% 3.22/0.98  
% 3.22/0.98  cnf(c_731,plain,
% 3.22/0.98      ( m1_subset_1(k1_yellow_0(sK3,X0),u1_struct_0(sK3)) ),
% 3.22/0.98      inference(unflattening,[status(thm)],[c_730]) ).
% 3.22/0.98  
% 3.22/0.98  cnf(c_2160,plain,
% 3.22/0.98      ( m1_subset_1(k1_yellow_0(sK3,X0),u1_struct_0(sK3)) = iProver_top ),
% 3.22/0.98      inference(predicate_to_equality,[status(thm)],[c_731]) ).
% 3.22/0.98  
% 3.22/0.98  cnf(c_7115,plain,
% 3.22/0.98      ( u1_struct_0(sK3) = sK4
% 3.22/0.98      | m1_subset_1(sK0(u1_struct_0(sK3),sK4),u1_struct_0(sK3)) = iProver_top ),
% 3.22/0.98      inference(superposition,[status(thm)],[c_6958,c_2160]) ).
% 3.22/0.98  
% 3.22/0.98  cnf(c_44,plain,
% 3.22/0.98      ( m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(sK3))) = iProver_top ),
% 3.22/0.98      inference(predicate_to_equality,[status(thm)],[c_27]) ).
% 3.22/0.98  
% 3.22/0.98  cnf(c_23,plain,
% 3.22/0.98      ( v1_subset_1(X0,X1)
% 3.22/0.98      | ~ m1_subset_1(X0,k1_zfmisc_1(X1))
% 3.22/0.98      | X0 = X1 ),
% 3.22/0.98      inference(cnf_transformation,[],[f79]) ).
% 3.22/0.98  
% 3.22/0.98  cnf(c_351,plain,
% 3.22/0.98      ( v1_subset_1(X0,X1) | ~ r1_tarski(X0,X1) | X0 = X1 ),
% 3.22/0.98      inference(bin_hyper_res,[status(thm)],[c_23,c_272]) ).
% 3.22/0.98  
% 3.22/0.98  cnf(c_25,negated_conjecture,
% 3.22/0.98      ( ~ v1_subset_1(sK4,u1_struct_0(sK3))
% 3.22/0.98      | r2_hidden(k3_yellow_0(sK3),sK4) ),
% 3.22/0.98      inference(cnf_transformation,[],[f90]) ).
% 3.22/0.98  
% 3.22/0.98  cnf(c_275,plain,
% 3.22/0.98      ( ~ v1_subset_1(sK4,u1_struct_0(sK3))
% 3.22/0.98      | r2_hidden(k3_yellow_0(sK3),sK4) ),
% 3.22/0.98      inference(prop_impl,[status(thm)],[c_25]) ).
% 3.22/0.98  
% 3.22/0.98  cnf(c_511,plain,
% 3.22/0.98      ( r2_hidden(k3_yellow_0(sK3),sK4)
% 3.22/0.98      | ~ r1_tarski(X0,X1)
% 3.22/0.98      | X1 = X0
% 3.22/0.98      | u1_struct_0(sK3) != X1
% 3.22/0.98      | sK4 != X0 ),
% 3.22/0.98      inference(resolution_lifted,[status(thm)],[c_351,c_275]) ).
% 3.22/0.98  
% 3.22/0.98  cnf(c_512,plain,
% 3.22/0.98      ( r2_hidden(k3_yellow_0(sK3),sK4)
% 3.22/0.98      | ~ r1_tarski(sK4,u1_struct_0(sK3))
% 3.22/0.98      | u1_struct_0(sK3) = sK4 ),
% 3.22/0.98      inference(unflattening,[status(thm)],[c_511]) ).
% 3.22/0.98  
% 3.22/0.98  cnf(c_513,plain,
% 3.22/0.98      ( u1_struct_0(sK3) = sK4
% 3.22/0.98      | r2_hidden(k3_yellow_0(sK3),sK4) = iProver_top
% 3.22/0.98      | r1_tarski(sK4,u1_struct_0(sK3)) != iProver_top ),
% 3.22/0.98      inference(predicate_to_equality,[status(thm)],[c_512]) ).
% 3.22/0.98  
% 3.22/0.98  cnf(c_24,plain,
% 3.22/0.98      ( ~ v1_subset_1(X0,X0) | ~ m1_subset_1(X0,k1_zfmisc_1(X0)) ),
% 3.22/0.98      inference(cnf_transformation,[],[f93]) ).
% 3.22/0.98  
% 3.22/0.98  cnf(c_26,negated_conjecture,
% 3.22/0.98      ( v1_subset_1(sK4,u1_struct_0(sK3))
% 3.22/0.98      | ~ r2_hidden(k3_yellow_0(sK3),sK4) ),
% 3.22/0.98      inference(cnf_transformation,[],[f89]) ).
% 3.22/0.98  
% 3.22/0.98  cnf(c_273,plain,
% 3.22/0.98      ( v1_subset_1(sK4,u1_struct_0(sK3))
% 3.22/0.98      | ~ r2_hidden(k3_yellow_0(sK3),sK4) ),
% 3.22/0.98      inference(prop_impl,[status(thm)],[c_26]) ).
% 3.22/0.98  
% 3.22/0.98  cnf(c_524,plain,
% 3.22/0.98      ( ~ m1_subset_1(X0,k1_zfmisc_1(X0))
% 3.22/0.98      | ~ r2_hidden(k3_yellow_0(sK3),sK4)
% 3.22/0.98      | u1_struct_0(sK3) != X0
% 3.22/0.98      | sK4 != X0 ),
% 3.22/0.98      inference(resolution_lifted,[status(thm)],[c_24,c_273]) ).
% 3.22/0.98  
% 3.22/0.98  cnf(c_525,plain,
% 3.22/0.98      ( ~ m1_subset_1(u1_struct_0(sK3),k1_zfmisc_1(u1_struct_0(sK3)))
% 3.22/0.98      | ~ r2_hidden(k3_yellow_0(sK3),sK4)
% 3.22/0.98      | sK4 != u1_struct_0(sK3) ),
% 3.22/0.98      inference(unflattening,[status(thm)],[c_524]) ).
% 3.22/0.98  
% 3.22/0.98  cnf(c_526,plain,
% 3.22/0.98      ( sK4 != u1_struct_0(sK3)
% 3.22/0.98      | m1_subset_1(u1_struct_0(sK3),k1_zfmisc_1(u1_struct_0(sK3))) != iProver_top
% 3.22/0.98      | r2_hidden(k3_yellow_0(sK3),sK4) != iProver_top ),
% 3.22/0.98      inference(predicate_to_equality,[status(thm)],[c_525]) ).
% 3.22/0.98  
% 3.22/0.98  cnf(c_2396,plain,
% 3.22/0.98      ( ~ m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(sK3)))
% 3.22/0.98      | r1_tarski(sK4,u1_struct_0(sK3)) ),
% 3.22/0.98      inference(instantiation,[status(thm)],[c_8]) ).
% 3.22/0.98  
% 3.22/0.98  cnf(c_2397,plain,
% 3.22/0.98      ( m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(sK3))) != iProver_top
% 3.22/0.98      | r1_tarski(sK4,u1_struct_0(sK3)) = iProver_top ),
% 3.22/0.98      inference(predicate_to_equality,[status(thm)],[c_2396]) ).
% 3.22/0.98  
% 3.22/0.98  cnf(c_2391,plain,
% 3.22/0.98      ( m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK3)))
% 3.22/0.98      | ~ r1_tarski(X0,u1_struct_0(sK3)) ),
% 3.22/0.98      inference(instantiation,[status(thm)],[c_7]) ).
% 3.22/0.98  
% 3.22/0.98  cnf(c_2498,plain,
% 3.22/0.98      ( m1_subset_1(u1_struct_0(sK3),k1_zfmisc_1(u1_struct_0(sK3)))
% 3.22/0.98      | ~ r1_tarski(u1_struct_0(sK3),u1_struct_0(sK3)) ),
% 3.22/0.98      inference(instantiation,[status(thm)],[c_2391]) ).
% 3.22/0.98  
% 3.22/0.98  cnf(c_2500,plain,
% 3.22/0.98      ( m1_subset_1(u1_struct_0(sK3),k1_zfmisc_1(u1_struct_0(sK3))) = iProver_top
% 3.22/0.98      | r1_tarski(u1_struct_0(sK3),u1_struct_0(sK3)) != iProver_top ),
% 3.22/0.98      inference(predicate_to_equality,[status(thm)],[c_2498]) ).
% 3.22/0.98  
% 3.22/0.98  cnf(c_1,plain,
% 3.22/0.98      ( r1_tarski(X0,X0) ),
% 3.22/0.98      inference(cnf_transformation,[],[f91]) ).
% 3.22/0.98  
% 3.22/0.98  cnf(c_2499,plain,
% 3.22/0.98      ( r1_tarski(u1_struct_0(sK3),u1_struct_0(sK3)) ),
% 3.22/0.98      inference(instantiation,[status(thm)],[c_1]) ).
% 3.22/0.98  
% 3.22/0.98  cnf(c_2502,plain,
% 3.22/0.98      ( r1_tarski(u1_struct_0(sK3),u1_struct_0(sK3)) = iProver_top ),
% 3.22/0.98      inference(predicate_to_equality,[status(thm)],[c_2499]) ).
% 3.22/0.98  
% 3.22/0.98  cnf(c_4,plain,
% 3.22/0.98      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
% 3.22/0.98      | ~ r2_hidden(sK0(X1,X0),X0)
% 3.22/0.98      | X0 = X1 ),
% 3.22/0.98      inference(cnf_transformation,[],[f60]) ).
% 3.22/0.98  
% 3.22/0.98  cnf(c_347,plain,
% 3.22/0.98      ( ~ r2_hidden(sK0(X0,X1),X1) | ~ r1_tarski(X1,X0) | X1 = X0 ),
% 3.22/0.98      inference(bin_hyper_res,[status(thm)],[c_4,c_272]) ).
% 3.22/0.98  
% 3.22/0.98  cnf(c_2539,plain,
% 3.22/0.98      ( ~ r2_hidden(sK0(u1_struct_0(sK3),X0),X0)
% 3.22/0.98      | ~ r1_tarski(X0,u1_struct_0(sK3))
% 3.22/0.98      | X0 = u1_struct_0(sK3) ),
% 3.22/0.98      inference(instantiation,[status(thm)],[c_347]) ).
% 3.22/0.98  
% 3.22/0.98  cnf(c_2965,plain,
% 3.22/0.98      ( ~ r2_hidden(sK0(u1_struct_0(sK3),sK4),sK4)
% 3.22/0.98      | ~ r1_tarski(sK4,u1_struct_0(sK3))
% 3.22/0.98      | sK4 = u1_struct_0(sK3) ),
% 3.22/0.98      inference(instantiation,[status(thm)],[c_2539]) ).
% 3.22/0.98  
% 3.22/0.98  cnf(c_2168,plain,
% 3.22/0.98      ( u1_struct_0(sK3) = sK4
% 3.22/0.98      | r2_hidden(k3_yellow_0(sK3),sK4) = iProver_top
% 3.22/0.98      | r1_tarski(sK4,u1_struct_0(sK3)) != iProver_top ),
% 3.22/0.98      inference(predicate_to_equality,[status(thm)],[c_512]) ).
% 3.22/0.98  
% 3.22/0.98  cnf(c_6265,plain,
% 3.22/0.98      ( r2_hidden(k3_yellow_0(sK3),sK4) = iProver_top
% 3.22/0.98      | u1_struct_0(sK3) = sK4 ),
% 3.22/0.98      inference(global_propositional_subsumption,
% 3.22/0.98                [status(thm)],
% 3.22/0.98                [c_2168,c_44,c_513,c_2397]) ).
% 3.22/0.98  
% 3.22/0.98  cnf(c_6266,plain,
% 3.22/0.98      ( u1_struct_0(sK3) = sK4
% 3.22/0.98      | r2_hidden(k3_yellow_0(sK3),sK4) = iProver_top ),
% 3.22/0.98      inference(renaming,[status(thm)],[c_6265]) ).
% 3.22/0.98  
% 3.22/0.98  cnf(c_6267,plain,
% 3.22/0.98      ( r2_hidden(k3_yellow_0(sK3),sK4) | u1_struct_0(sK3) = sK4 ),
% 3.22/0.98      inference(predicate_to_equality_rev,[status(thm)],[c_6266]) ).
% 3.22/0.98  
% 3.22/0.98  cnf(c_2446,plain,
% 3.22/0.98      ( k1_yellow_0(sK3,k5_waybel_0(sK3,k1_yellow_0(sK3,X0))) = k1_yellow_0(sK3,X0) ),
% 3.22/0.98      inference(superposition,[status(thm)],[c_2160,c_2165]) ).
% 3.22/0.98  
% 3.22/0.98  cnf(c_10,plain,
% 3.22/0.98      ( ~ l1_orders_2(X0)
% 3.22/0.98      | k1_yellow_0(X0,k1_xboole_0) = k3_yellow_0(X0) ),
% 3.22/0.98      inference(cnf_transformation,[],[f65]) ).
% 3.22/0.98  
% 3.22/0.98  cnf(c_739,plain,
% 3.22/0.98      ( k1_yellow_0(X0,k1_xboole_0) = k3_yellow_0(X0) | sK3 != X0 ),
% 3.22/0.98      inference(resolution_lifted,[status(thm)],[c_10,c_30]) ).
% 3.22/0.98  
% 3.22/0.98  cnf(c_740,plain,
% 3.22/0.98      ( k1_yellow_0(sK3,k1_xboole_0) = k3_yellow_0(sK3) ),
% 3.22/0.98      inference(unflattening,[status(thm)],[c_739]) ).
% 3.22/0.98  
% 3.22/0.98  cnf(c_13,plain,
% 3.22/0.98      ( r1_orders_2(X0,k1_yellow_0(X0,X1),k1_yellow_0(X0,X2))
% 3.22/0.98      | ~ r1_yellow_0(X0,X2)
% 3.22/0.98      | ~ r1_yellow_0(X0,X1)
% 3.22/0.98      | ~ r1_tarski(X1,X2)
% 3.22/0.98      | ~ l1_orders_2(X0) ),
% 3.22/0.98      inference(cnf_transformation,[],[f68]) ).
% 3.22/0.98  
% 3.22/0.98  cnf(c_705,plain,
% 3.22/0.98      ( r1_orders_2(X0,k1_yellow_0(X0,X1),k1_yellow_0(X0,X2))
% 3.22/0.98      | ~ r1_yellow_0(X0,X2)
% 3.22/0.98      | ~ r1_yellow_0(X0,X1)
% 3.22/0.98      | ~ r1_tarski(X1,X2)
% 3.22/0.98      | sK3 != X0 ),
% 3.22/0.98      inference(resolution_lifted,[status(thm)],[c_13,c_30]) ).
% 3.22/0.98  
% 3.22/0.98  cnf(c_706,plain,
% 3.22/0.98      ( r1_orders_2(sK3,k1_yellow_0(sK3,X0),k1_yellow_0(sK3,X1))
% 3.22/0.98      | ~ r1_yellow_0(sK3,X0)
% 3.22/0.98      | ~ r1_yellow_0(sK3,X1)
% 3.22/0.98      | ~ r1_tarski(X0,X1) ),
% 3.22/0.98      inference(unflattening,[status(thm)],[c_705]) ).
% 3.22/0.98  
% 3.22/0.98  cnf(c_2162,plain,
% 3.22/0.98      ( r1_orders_2(sK3,k1_yellow_0(sK3,X0),k1_yellow_0(sK3,X1)) = iProver_top
% 3.22/0.98      | r1_yellow_0(sK3,X0) != iProver_top
% 3.22/0.98      | r1_yellow_0(sK3,X1) != iProver_top
% 3.22/0.98      | r1_tarski(X0,X1) != iProver_top ),
% 3.22/0.98      inference(predicate_to_equality,[status(thm)],[c_706]) ).
% 3.22/0.98  
% 3.22/0.98  cnf(c_2941,plain,
% 3.22/0.98      ( r1_orders_2(sK3,k3_yellow_0(sK3),k1_yellow_0(sK3,X0)) = iProver_top
% 3.22/0.98      | r1_yellow_0(sK3,X0) != iProver_top
% 3.22/0.98      | r1_yellow_0(sK3,k1_xboole_0) != iProver_top
% 3.22/0.98      | r1_tarski(k1_xboole_0,X0) != iProver_top ),
% 3.22/0.98      inference(superposition,[status(thm)],[c_740,c_2162]) ).
% 3.22/0.98  
% 3.22/0.98  cnf(c_36,plain,
% 3.22/0.98      ( v2_struct_0(sK3) != iProver_top ),
% 3.22/0.98      inference(predicate_to_equality,[status(thm)],[c_35]) ).
% 3.22/0.98  
% 3.22/0.98  cnf(c_39,plain,
% 3.22/0.98      ( v5_orders_2(sK3) = iProver_top ),
% 3.22/0.98      inference(predicate_to_equality,[status(thm)],[c_32]) ).
% 3.22/0.98  
% 3.22/0.98  cnf(c_31,negated_conjecture,
% 3.22/0.98      ( v1_yellow_0(sK3) ),
% 3.22/0.98      inference(cnf_transformation,[],[f84]) ).
% 3.22/0.98  
% 3.22/0.98  cnf(c_40,plain,
% 3.22/0.98      ( v1_yellow_0(sK3) = iProver_top ),
% 3.22/0.98      inference(predicate_to_equality,[status(thm)],[c_31]) ).
% 3.22/0.98  
% 3.22/0.98  cnf(c_41,plain,
% 3.22/0.98      ( l1_orders_2(sK3) = iProver_top ),
% 3.22/0.98      inference(predicate_to_equality,[status(thm)],[c_30]) ).
% 3.22/0.98  
% 3.22/0.98  cnf(c_14,plain,
% 3.22/0.98      ( r1_yellow_0(X0,k1_xboole_0)
% 3.22/0.98      | v2_struct_0(X0)
% 3.22/0.98      | ~ v5_orders_2(X0)
% 3.22/0.98      | ~ v1_yellow_0(X0)
% 3.22/0.98      | ~ l1_orders_2(X0) ),
% 3.22/0.98      inference(cnf_transformation,[],[f69]) ).
% 3.22/0.98  
% 3.22/0.98  cnf(c_75,plain,
% 3.22/0.98      ( r1_yellow_0(X0,k1_xboole_0) = iProver_top
% 3.22/0.98      | v2_struct_0(X0) = iProver_top
% 3.22/0.98      | v5_orders_2(X0) != iProver_top
% 3.22/0.98      | v1_yellow_0(X0) != iProver_top
% 3.22/0.98      | l1_orders_2(X0) != iProver_top ),
% 3.22/0.98      inference(predicate_to_equality,[status(thm)],[c_14]) ).
% 3.22/0.98  
% 3.22/0.98  cnf(c_77,plain,
% 3.22/0.98      ( r1_yellow_0(sK3,k1_xboole_0) = iProver_top
% 3.22/0.98      | v2_struct_0(sK3) = iProver_top
% 3.22/0.98      | v5_orders_2(sK3) != iProver_top
% 3.22/0.98      | v1_yellow_0(sK3) != iProver_top
% 3.22/0.98      | l1_orders_2(sK3) != iProver_top ),
% 3.22/0.98      inference(instantiation,[status(thm)],[c_75]) ).
% 3.22/0.98  
% 3.22/0.98  cnf(c_3,plain,
% 3.22/0.98      ( r1_tarski(k1_xboole_0,X0) ),
% 3.22/0.98      inference(cnf_transformation,[],[f58]) ).
% 3.22/0.98  
% 3.22/0.98  cnf(c_108,plain,
% 3.22/0.98      ( r1_tarski(k1_xboole_0,X0) = iProver_top ),
% 3.22/0.98      inference(predicate_to_equality,[status(thm)],[c_3]) ).
% 3.22/0.98  
% 3.22/0.98  cnf(c_3150,plain,
% 3.22/0.98      ( r1_orders_2(sK3,k3_yellow_0(sK3),k1_yellow_0(sK3,X0)) = iProver_top
% 3.22/0.98      | r1_yellow_0(sK3,X0) != iProver_top ),
% 3.22/0.98      inference(global_propositional_subsumption,
% 3.22/0.98                [status(thm)],
% 3.22/0.98                [c_2941,c_36,c_39,c_40,c_41,c_77,c_108]) ).
% 3.22/0.98  
% 3.22/0.98  cnf(c_3622,plain,
% 3.22/0.98      ( r1_orders_2(sK3,k3_yellow_0(sK3),k1_yellow_0(sK3,X0)) = iProver_top
% 3.22/0.98      | r1_yellow_0(sK3,k5_waybel_0(sK3,k1_yellow_0(sK3,X0))) != iProver_top ),
% 3.22/0.98      inference(superposition,[status(thm)],[c_2446,c_3150]) ).
% 3.22/0.98  
% 3.22/0.98  cnf(c_732,plain,
% 3.22/0.98      ( m1_subset_1(k1_yellow_0(sK3,X0),u1_struct_0(sK3)) = iProver_top ),
% 3.22/0.98      inference(predicate_to_equality,[status(thm)],[c_731]) ).
% 3.22/0.98  
% 3.22/0.98  cnf(c_22,plain,
% 3.22/0.98      ( r1_yellow_0(X0,k5_waybel_0(X0,X1))
% 3.22/0.98      | ~ m1_subset_1(X1,u1_struct_0(X0))
% 3.22/0.98      | ~ v3_orders_2(X0)
% 3.22/0.98      | ~ v4_orders_2(X0)
% 3.22/0.98      | v2_struct_0(X0)
% 3.22/0.98      | ~ v5_orders_2(X0)
% 3.22/0.98      | ~ l1_orders_2(X0) ),
% 3.22/0.98      inference(cnf_transformation,[],[f76]) ).
% 3.22/0.98  
% 3.22/0.98  cnf(c_545,plain,
% 3.22/0.98      ( r1_yellow_0(X0,k5_waybel_0(X0,X1))
% 3.22/0.98      | ~ m1_subset_1(X1,u1_struct_0(X0))
% 3.22/0.98      | ~ v3_orders_2(X0)
% 3.22/0.98      | ~ v4_orders_2(X0)
% 3.22/0.98      | v2_struct_0(X0)
% 3.22/0.98      | ~ l1_orders_2(X0)
% 3.22/0.98      | sK3 != X0 ),
% 3.22/0.98      inference(resolution_lifted,[status(thm)],[c_22,c_32]) ).
% 3.22/0.98  
% 3.22/0.98  cnf(c_546,plain,
% 3.22/0.98      ( r1_yellow_0(sK3,k5_waybel_0(sK3,X0))
% 3.22/0.98      | ~ m1_subset_1(X0,u1_struct_0(sK3))
% 3.22/0.98      | ~ v3_orders_2(sK3)
% 3.22/0.98      | ~ v4_orders_2(sK3)
% 3.22/0.98      | v2_struct_0(sK3)
% 3.22/0.98      | ~ l1_orders_2(sK3) ),
% 3.22/0.98      inference(unflattening,[status(thm)],[c_545]) ).
% 3.22/0.98  
% 3.22/0.98  cnf(c_550,plain,
% 3.22/0.98      ( r1_yellow_0(sK3,k5_waybel_0(sK3,X0))
% 3.22/0.98      | ~ m1_subset_1(X0,u1_struct_0(sK3)) ),
% 3.22/0.98      inference(global_propositional_subsumption,
% 3.22/0.98                [status(thm)],
% 3.22/0.98                [c_546,c_35,c_34,c_33,c_30]) ).
% 3.22/0.98  
% 3.22/0.98  cnf(c_2362,plain,
% 3.22/0.98      ( r1_yellow_0(sK3,k5_waybel_0(sK3,k1_yellow_0(sK3,X0)))
% 3.22/0.98      | ~ m1_subset_1(k1_yellow_0(sK3,X0),u1_struct_0(sK3)) ),
% 3.22/0.98      inference(instantiation,[status(thm)],[c_550]) ).
% 3.22/0.98  
% 3.22/0.98  cnf(c_2363,plain,
% 3.22/0.98      ( r1_yellow_0(sK3,k5_waybel_0(sK3,k1_yellow_0(sK3,X0))) = iProver_top
% 3.22/0.98      | m1_subset_1(k1_yellow_0(sK3,X0),u1_struct_0(sK3)) != iProver_top ),
% 3.22/0.98      inference(predicate_to_equality,[status(thm)],[c_2362]) ).
% 3.22/0.98  
% 3.22/0.98  cnf(c_3731,plain,
% 3.22/0.98      ( r1_orders_2(sK3,k3_yellow_0(sK3),k1_yellow_0(sK3,X0)) = iProver_top ),
% 3.22/0.98      inference(global_propositional_subsumption,
% 3.22/0.98                [status(thm)],
% 3.22/0.98                [c_3622,c_732,c_2363]) ).
% 3.22/0.98  
% 3.22/0.98  cnf(c_20,plain,
% 3.22/0.98      ( ~ r1_orders_2(X0,X1,X2)
% 3.22/0.98      | ~ v13_waybel_0(X3,X0)
% 3.22/0.98      | ~ m1_subset_1(X2,u1_struct_0(X0))
% 3.22/0.98      | ~ m1_subset_1(X1,u1_struct_0(X0))
% 3.22/0.98      | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))
% 3.22/0.98      | ~ r2_hidden(X1,X3)
% 3.22/0.98      | r2_hidden(X2,X3)
% 3.22/0.98      | ~ l1_orders_2(X0) ),
% 3.22/0.98      inference(cnf_transformation,[],[f70]) ).
% 3.22/0.98  
% 3.22/0.98  cnf(c_665,plain,
% 3.22/0.98      ( ~ r1_orders_2(X0,X1,X2)
% 3.22/0.98      | ~ v13_waybel_0(X3,X0)
% 3.22/0.98      | ~ m1_subset_1(X2,u1_struct_0(X0))
% 3.22/0.98      | ~ m1_subset_1(X1,u1_struct_0(X0))
% 3.22/0.98      | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))
% 3.22/0.98      | ~ r2_hidden(X1,X3)
% 3.22/0.98      | r2_hidden(X2,X3)
% 3.22/0.98      | sK3 != X0 ),
% 3.22/0.98      inference(resolution_lifted,[status(thm)],[c_20,c_30]) ).
% 3.22/0.98  
% 3.22/0.98  cnf(c_666,plain,
% 3.22/0.98      ( ~ r1_orders_2(sK3,X0,X1)
% 3.22/0.98      | ~ v13_waybel_0(X2,sK3)
% 3.22/0.98      | ~ m1_subset_1(X0,u1_struct_0(sK3))
% 3.22/0.98      | ~ m1_subset_1(X1,u1_struct_0(sK3))
% 3.22/0.98      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK3)))
% 3.22/0.98      | ~ r2_hidden(X0,X2)
% 3.22/0.98      | r2_hidden(X1,X2) ),
% 3.22/0.98      inference(unflattening,[status(thm)],[c_665]) ).
% 3.22/0.98  
% 3.22/0.98  cnf(c_9,plain,
% 3.22/0.98      ( m1_subset_1(X0,X1)
% 3.22/0.98      | ~ m1_subset_1(X2,k1_zfmisc_1(X1))
% 3.22/0.98      | ~ r2_hidden(X0,X2) ),
% 3.22/0.98      inference(cnf_transformation,[],[f64]) ).
% 3.22/0.98  
% 3.22/0.98  cnf(c_682,plain,
% 3.22/0.98      ( ~ r1_orders_2(sK3,X0,X1)
% 3.22/0.98      | ~ v13_waybel_0(X2,sK3)
% 3.22/0.98      | ~ m1_subset_1(X1,u1_struct_0(sK3))
% 3.22/0.98      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK3)))
% 3.22/0.98      | ~ r2_hidden(X0,X2)
% 3.22/0.98      | r2_hidden(X1,X2) ),
% 3.22/0.98      inference(forward_subsumption_resolution,[status(thm)],[c_666,c_9]) ).
% 3.22/0.98  
% 3.22/0.98  cnf(c_2164,plain,
% 3.22/0.98      ( r1_orders_2(sK3,X0,X1) != iProver_top
% 3.22/0.98      | v13_waybel_0(X2,sK3) != iProver_top
% 3.22/0.98      | m1_subset_1(X1,u1_struct_0(sK3)) != iProver_top
% 3.22/0.98      | m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK3))) != iProver_top
% 3.22/0.98      | r2_hidden(X0,X2) != iProver_top
% 3.22/0.98      | r2_hidden(X1,X2) = iProver_top ),
% 3.22/0.98      inference(predicate_to_equality,[status(thm)],[c_682]) ).
% 3.22/0.98  
% 3.22/0.98  cnf(c_3939,plain,
% 3.22/0.98      ( r1_orders_2(sK3,X0,X1) != iProver_top
% 3.22/0.98      | v13_waybel_0(sK4,sK3) != iProver_top
% 3.22/0.98      | m1_subset_1(X1,u1_struct_0(sK3)) != iProver_top
% 3.22/0.98      | r2_hidden(X0,sK4) != iProver_top
% 3.22/0.98      | r2_hidden(X1,sK4) = iProver_top ),
% 3.22/0.98      inference(superposition,[status(thm)],[c_2174,c_2164]) ).
% 3.22/0.98  
% 3.22/0.98  cnf(c_28,negated_conjecture,
% 3.22/0.98      ( v13_waybel_0(sK4,sK3) ),
% 3.22/0.98      inference(cnf_transformation,[],[f87]) ).
% 3.22/0.98  
% 3.22/0.98  cnf(c_907,plain,
% 3.22/0.98      ( ~ r1_orders_2(sK3,X0,X1)
% 3.22/0.98      | ~ m1_subset_1(X1,u1_struct_0(sK3))
% 3.22/0.98      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK3)))
% 3.22/0.98      | ~ r2_hidden(X0,X2)
% 3.22/0.98      | r2_hidden(X1,X2)
% 3.22/0.98      | sK4 != X2
% 3.22/0.98      | sK3 != sK3 ),
% 3.22/0.98      inference(resolution_lifted,[status(thm)],[c_28,c_682]) ).
% 3.22/0.98  
% 3.22/0.98  cnf(c_908,plain,
% 3.22/0.98      ( ~ r1_orders_2(sK3,X0,X1)
% 3.22/0.98      | ~ m1_subset_1(X1,u1_struct_0(sK3))
% 3.22/0.98      | ~ m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(sK3)))
% 3.22/0.98      | ~ r2_hidden(X0,sK4)
% 3.22/0.98      | r2_hidden(X1,sK4) ),
% 3.22/0.98      inference(unflattening,[status(thm)],[c_907]) ).
% 3.22/0.98  
% 3.22/0.98  cnf(c_909,plain,
% 3.22/0.98      ( r1_orders_2(sK3,X0,X1) != iProver_top
% 3.22/0.98      | m1_subset_1(X1,u1_struct_0(sK3)) != iProver_top
% 3.22/0.98      | m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(sK3))) != iProver_top
% 3.22/0.98      | r2_hidden(X0,sK4) != iProver_top
% 3.22/0.98      | r2_hidden(X1,sK4) = iProver_top ),
% 3.22/0.98      inference(predicate_to_equality,[status(thm)],[c_908]) ).
% 3.22/0.98  
% 3.22/0.98  cnf(c_4383,plain,
% 3.22/0.98      ( r1_orders_2(sK3,X0,X1) != iProver_top
% 3.22/0.98      | m1_subset_1(X1,u1_struct_0(sK3)) != iProver_top
% 3.22/0.98      | r2_hidden(X0,sK4) != iProver_top
% 3.22/0.98      | r2_hidden(X1,sK4) = iProver_top ),
% 3.22/0.98      inference(global_propositional_subsumption,
% 3.22/0.98                [status(thm)],
% 3.22/0.98                [c_3939,c_44,c_909]) ).
% 3.22/0.98  
% 3.22/0.98  cnf(c_4393,plain,
% 3.22/0.98      ( m1_subset_1(k1_yellow_0(sK3,X0),u1_struct_0(sK3)) != iProver_top
% 3.22/0.98      | r2_hidden(k1_yellow_0(sK3,X0),sK4) = iProver_top
% 3.22/0.98      | r2_hidden(k3_yellow_0(sK3),sK4) != iProver_top ),
% 3.22/0.98      inference(superposition,[status(thm)],[c_3731,c_4383]) ).
% 3.22/0.98  
% 3.22/0.98  cnf(c_4445,plain,
% 3.22/0.98      ( r2_hidden(k1_yellow_0(sK3,X0),sK4) = iProver_top
% 3.22/0.98      | r2_hidden(k3_yellow_0(sK3),sK4) != iProver_top ),
% 3.22/0.98      inference(global_propositional_subsumption,
% 3.22/0.98                [status(thm)],
% 3.22/0.98                [c_4393,c_732]) ).
% 3.22/0.98  
% 3.22/0.98  cnf(c_7111,plain,
% 3.22/0.98      ( u1_struct_0(sK3) = sK4
% 3.22/0.98      | r2_hidden(sK0(u1_struct_0(sK3),sK4),sK4) = iProver_top
% 3.22/0.98      | r2_hidden(k3_yellow_0(sK3),sK4) != iProver_top ),
% 3.22/0.98      inference(superposition,[status(thm)],[c_6958,c_4445]) ).
% 3.22/0.98  
% 3.22/0.98  cnf(c_7322,plain,
% 3.22/0.98      ( r2_hidden(sK0(u1_struct_0(sK3),sK4),sK4)
% 3.22/0.98      | ~ r2_hidden(k3_yellow_0(sK3),sK4)
% 3.22/0.98      | u1_struct_0(sK3) = sK4 ),
% 3.22/0.98      inference(predicate_to_equality_rev,[status(thm)],[c_7111]) ).
% 3.22/0.98  
% 3.22/0.98  cnf(c_7330,plain,
% 3.22/0.98      ( u1_struct_0(sK3) = sK4 ),
% 3.22/0.98      inference(global_propositional_subsumption,
% 3.22/0.98                [status(thm)],
% 3.22/0.98                [c_7115,c_27,c_44,c_513,c_526,c_2396,c_2397,c_2500,
% 3.22/0.98                 c_2502,c_2965,c_6267,c_7322]) ).
% 3.22/0.98  
% 3.22/0.98  cnf(c_12,plain,
% 3.22/0.98      ( m1_subset_1(k3_yellow_0(X0),u1_struct_0(X0))
% 3.22/0.98      | ~ l1_orders_2(X0) ),
% 3.22/0.98      inference(cnf_transformation,[],[f67]) ).
% 3.22/0.98  
% 3.22/0.98  cnf(c_723,plain,
% 3.22/0.98      ( m1_subset_1(k3_yellow_0(X0),u1_struct_0(X0)) | sK3 != X0 ),
% 3.22/0.98      inference(resolution_lifted,[status(thm)],[c_12,c_30]) ).
% 3.22/0.98  
% 3.22/0.98  cnf(c_724,plain,
% 3.22/0.98      ( m1_subset_1(k3_yellow_0(sK3),u1_struct_0(sK3)) ),
% 3.22/0.98      inference(unflattening,[status(thm)],[c_723]) ).
% 3.22/0.98  
% 3.22/0.98  cnf(c_2161,plain,
% 3.22/0.98      ( m1_subset_1(k3_yellow_0(sK3),u1_struct_0(sK3)) = iProver_top ),
% 3.22/0.98      inference(predicate_to_equality,[status(thm)],[c_724]) ).
% 3.22/0.98  
% 3.22/0.98  cnf(c_7358,plain,
% 3.22/0.98      ( m1_subset_1(k3_yellow_0(sK3),sK4) = iProver_top ),
% 3.22/0.98      inference(demodulation,[status(thm)],[c_7330,c_2161]) ).
% 3.22/0.98  
% 3.22/0.98  cnf(c_6,plain,
% 3.22/0.98      ( ~ m1_subset_1(X0,X1) | r2_hidden(X0,X1) | v1_xboole_0(X1) ),
% 3.22/0.98      inference(cnf_transformation,[],[f61]) ).
% 3.22/0.98  
% 3.22/0.98  cnf(c_29,negated_conjecture,
% 3.22/0.98      ( ~ v1_xboole_0(sK4) ),
% 3.22/0.98      inference(cnf_transformation,[],[f86]) ).
% 3.22/0.98  
% 3.22/0.98  cnf(c_480,plain,
% 3.22/0.98      ( ~ m1_subset_1(X0,X1) | r2_hidden(X0,X1) | sK4 != X1 ),
% 3.22/0.98      inference(resolution_lifted,[status(thm)],[c_6,c_29]) ).
% 3.22/0.98  
% 3.22/0.98  cnf(c_481,plain,
% 3.22/0.98      ( ~ m1_subset_1(X0,sK4) | r2_hidden(X0,sK4) ),
% 3.22/0.98      inference(unflattening,[status(thm)],[c_480]) ).
% 3.22/0.98  
% 3.22/0.98  cnf(c_2170,plain,
% 3.22/0.98      ( m1_subset_1(X0,sK4) != iProver_top
% 3.22/0.98      | r2_hidden(X0,sK4) = iProver_top ),
% 3.22/0.98      inference(predicate_to_equality,[status(thm)],[c_481]) ).
% 3.22/0.98  
% 3.22/0.98  cnf(c_7665,plain,
% 3.22/0.98      ( r2_hidden(k3_yellow_0(sK3),sK4) = iProver_top ),
% 3.22/0.98      inference(superposition,[status(thm)],[c_7358,c_2170]) ).
% 3.22/0.98  
% 3.22/0.98  cnf(c_2167,plain,
% 3.22/0.98      ( sK4 != u1_struct_0(sK3)
% 3.22/0.98      | m1_subset_1(u1_struct_0(sK3),k1_zfmisc_1(u1_struct_0(sK3))) != iProver_top
% 3.22/0.98      | r2_hidden(k3_yellow_0(sK3),sK4) != iProver_top ),
% 3.22/0.98      inference(predicate_to_equality,[status(thm)],[c_525]) ).
% 3.22/0.98  
% 3.22/0.98  cnf(c_5012,plain,
% 3.22/0.98      ( sK4 != u1_struct_0(sK3)
% 3.22/0.98      | r2_hidden(k3_yellow_0(sK3),sK4) != iProver_top ),
% 3.22/0.98      inference(global_propositional_subsumption,
% 3.22/0.98                [status(thm)],
% 3.22/0.98                [c_2167,c_526,c_2500,c_2502]) ).
% 3.22/0.98  
% 3.22/0.98  cnf(c_7343,plain,
% 3.22/0.98      ( sK4 != sK4 | r2_hidden(k3_yellow_0(sK3),sK4) != iProver_top ),
% 3.22/0.98      inference(demodulation,[status(thm)],[c_7330,c_5012]) ).
% 3.22/0.98  
% 3.22/0.98  cnf(c_7437,plain,
% 3.22/0.98      ( r2_hidden(k3_yellow_0(sK3),sK4) != iProver_top ),
% 3.22/0.98      inference(equality_resolution_simp,[status(thm)],[c_7343]) ).
% 3.22/0.98  
% 3.22/0.98  cnf(contradiction,plain,
% 3.22/0.98      ( $false ),
% 3.22/0.98      inference(minisat,[status(thm)],[c_7665,c_7437]) ).
% 3.22/0.98  
% 3.22/0.98  
% 3.22/0.98  % SZS output end CNFRefutation for theBenchmark.p
% 3.22/0.98  
% 3.22/0.98  ------                               Statistics
% 3.22/0.98  
% 3.22/0.98  ------ General
% 3.22/0.98  
% 3.22/0.98  abstr_ref_over_cycles:                  0
% 3.22/0.98  abstr_ref_under_cycles:                 0
% 3.22/0.98  gc_basic_clause_elim:                   0
% 3.22/0.98  forced_gc_time:                         0
% 3.22/0.98  parsing_time:                           0.008
% 3.22/0.98  unif_index_cands_time:                  0.
% 3.22/0.98  unif_index_add_time:                    0.
% 3.22/0.98  orderings_time:                         0.
% 3.22/0.98  out_proof_time:                         0.012
% 3.22/0.98  total_time:                             0.234
% 3.22/0.98  num_of_symbols:                         56
% 3.22/0.98  num_of_terms:                           4732
% 3.22/0.98  
% 3.22/0.98  ------ Preprocessing
% 3.22/0.98  
% 3.22/0.98  num_of_splits:                          0
% 3.22/0.98  num_of_split_atoms:                     0
% 3.22/0.98  num_of_reused_defs:                     0
% 3.22/0.98  num_eq_ax_congr_red:                    22
% 3.22/0.98  num_of_sem_filtered_clauses:            1
% 3.22/0.98  num_of_subtypes:                        0
% 3.22/0.98  monotx_restored_types:                  0
% 3.22/0.98  sat_num_of_epr_types:                   0
% 3.22/0.98  sat_num_of_non_cyclic_types:            0
% 3.22/0.98  sat_guarded_non_collapsed_types:        0
% 3.22/0.98  num_pure_diseq_elim:                    0
% 3.22/0.98  simp_replaced_by:                       0
% 3.22/0.98  res_preprocessed:                       144
% 3.22/0.98  prep_upred:                             0
% 3.22/0.98  prep_unflattend:                        45
% 3.22/0.98  smt_new_axioms:                         0
% 3.22/0.98  pred_elim_cands:                        6
% 3.22/0.98  pred_elim:                              8
% 3.22/0.98  pred_elim_cl:                           9
% 3.22/0.98  pred_elim_cycles:                       13
% 3.22/0.98  merged_defs:                            10
% 3.22/0.98  merged_defs_ncl:                        0
% 3.22/0.98  bin_hyper_res:                          13
% 3.22/0.98  prep_cycles:                            4
% 3.22/0.98  pred_elim_time:                         0.01
% 3.22/0.98  splitting_time:                         0.
% 3.22/0.98  sem_filter_time:                        0.
% 3.22/0.98  monotx_time:                            0.
% 3.22/0.98  subtype_inf_time:                       0.
% 3.22/0.98  
% 3.22/0.98  ------ Problem properties
% 3.22/0.98  
% 3.22/0.98  clauses:                                26
% 3.22/0.98  conjectures:                            2
% 3.22/0.98  epr:                                    6
% 3.22/0.98  horn:                                   20
% 3.22/0.98  ground:                                 7
% 3.22/0.98  unary:                                  8
% 3.22/0.98  binary:                                 5
% 3.22/0.98  lits:                                   61
% 3.22/0.98  lits_eq:                                7
% 3.22/0.98  fd_pure:                                0
% 3.22/0.98  fd_pseudo:                              0
% 3.22/0.98  fd_cond:                                0
% 3.22/0.98  fd_pseudo_cond:                         3
% 3.22/0.98  ac_symbols:                             0
% 3.22/0.98  
% 3.22/0.98  ------ Propositional Solver
% 3.22/0.98  
% 3.22/0.98  prop_solver_calls:                      27
% 3.22/0.98  prop_fast_solver_calls:                 1218
% 3.22/0.98  smt_solver_calls:                       0
% 3.22/0.98  smt_fast_solver_calls:                  0
% 3.22/0.98  prop_num_of_clauses:                    2300
% 3.22/0.98  prop_preprocess_simplified:             6490
% 3.22/0.98  prop_fo_subsumed:                       34
% 3.22/0.98  prop_solver_time:                       0.
% 3.22/0.98  smt_solver_time:                        0.
% 3.22/0.98  smt_fast_solver_time:                   0.
% 3.22/0.98  prop_fast_solver_time:                  0.
% 3.22/0.98  prop_unsat_core_time:                   0.
% 3.22/0.98  
% 3.22/0.98  ------ QBF
% 3.22/0.98  
% 3.22/0.98  qbf_q_res:                              0
% 3.22/0.98  qbf_num_tautologies:                    0
% 3.22/0.98  qbf_prep_cycles:                        0
% 3.22/0.98  
% 3.22/0.98  ------ BMC1
% 3.22/0.98  
% 3.22/0.98  bmc1_current_bound:                     -1
% 3.22/0.98  bmc1_last_solved_bound:                 -1
% 3.22/0.98  bmc1_unsat_core_size:                   -1
% 3.22/0.98  bmc1_unsat_core_parents_size:           -1
% 3.22/0.98  bmc1_merge_next_fun:                    0
% 3.22/0.98  bmc1_unsat_core_clauses_time:           0.
% 3.22/0.98  
% 3.22/0.98  ------ Instantiation
% 3.22/0.98  
% 3.22/0.98  inst_num_of_clauses:                    608
% 3.22/0.98  inst_num_in_passive:                    77
% 3.22/0.98  inst_num_in_active:                     288
% 3.22/0.98  inst_num_in_unprocessed:                244
% 3.22/0.98  inst_num_of_loops:                      350
% 3.22/0.98  inst_num_of_learning_restarts:          0
% 3.22/0.98  inst_num_moves_active_passive:          60
% 3.22/0.98  inst_lit_activity:                      0
% 3.22/0.98  inst_lit_activity_moves:                0
% 3.22/0.98  inst_num_tautologies:                   0
% 3.22/0.98  inst_num_prop_implied:                  0
% 3.22/0.98  inst_num_existing_simplified:           0
% 3.22/0.98  inst_num_eq_res_simplified:             0
% 3.22/0.98  inst_num_child_elim:                    0
% 3.22/0.98  inst_num_of_dismatching_blockings:      105
% 3.22/0.98  inst_num_of_non_proper_insts:           562
% 3.22/0.98  inst_num_of_duplicates:                 0
% 3.22/0.98  inst_inst_num_from_inst_to_res:         0
% 3.22/0.98  inst_dismatching_checking_time:         0.
% 3.22/0.98  
% 3.22/0.98  ------ Resolution
% 3.22/0.98  
% 3.22/0.98  res_num_of_clauses:                     0
% 3.22/0.98  res_num_in_passive:                     0
% 3.22/0.98  res_num_in_active:                      0
% 3.22/0.98  res_num_of_loops:                       148
% 3.22/0.98  res_forward_subset_subsumed:            79
% 3.22/0.98  res_backward_subset_subsumed:           2
% 3.22/0.98  res_forward_subsumed:                   0
% 3.22/0.98  res_backward_subsumed:                  0
% 3.22/0.98  res_forward_subsumption_resolution:     7
% 3.22/0.98  res_backward_subsumption_resolution:    0
% 3.22/0.98  res_clause_to_clause_subsumption:       454
% 3.22/0.98  res_orphan_elimination:                 0
% 3.22/0.98  res_tautology_del:                      60
% 3.22/0.98  res_num_eq_res_simplified:              0
% 3.22/0.98  res_num_sel_changes:                    0
% 3.22/0.98  res_moves_from_active_to_pass:          0
% 3.22/0.98  
% 3.22/0.98  ------ Superposition
% 3.22/0.98  
% 3.22/0.98  sup_time_total:                         0.
% 3.22/0.98  sup_time_generating:                    0.
% 3.22/0.98  sup_time_sim_full:                      0.
% 3.22/0.98  sup_time_sim_immed:                     0.
% 3.22/0.98  
% 3.22/0.98  sup_num_of_clauses:                     96
% 3.22/0.98  sup_num_in_active:                      39
% 3.22/0.98  sup_num_in_passive:                     57
% 3.22/0.98  sup_num_of_loops:                       69
% 3.22/0.98  sup_fw_superposition:                   106
% 3.22/0.98  sup_bw_superposition:                   74
% 3.22/0.98  sup_immediate_simplified:               49
% 3.22/0.98  sup_given_eliminated:                   0
% 3.22/0.98  comparisons_done:                       0
% 3.22/0.98  comparisons_avoided:                    5
% 3.22/0.98  
% 3.22/0.98  ------ Simplifications
% 3.22/0.98  
% 3.22/0.98  
% 3.22/0.98  sim_fw_subset_subsumed:                 22
% 3.22/0.98  sim_bw_subset_subsumed:                 26
% 3.22/0.98  sim_fw_subsumed:                        13
% 3.22/0.98  sim_bw_subsumed:                        0
% 3.22/0.98  sim_fw_subsumption_res:                 4
% 3.22/0.98  sim_bw_subsumption_res:                 0
% 3.22/0.98  sim_tautology_del:                      18
% 3.22/0.98  sim_eq_tautology_del:                   6
% 3.22/0.98  sim_eq_res_simp:                        1
% 3.22/0.98  sim_fw_demodulated:                     3
% 3.22/0.98  sim_bw_demodulated:                     27
% 3.22/0.98  sim_light_normalised:                   16
% 3.22/0.98  sim_joinable_taut:                      0
% 3.22/0.98  sim_joinable_simp:                      0
% 3.22/0.98  sim_ac_normalised:                      0
% 3.22/0.98  sim_smt_subsumption:                    0
% 3.22/0.98  
%------------------------------------------------------------------------------
