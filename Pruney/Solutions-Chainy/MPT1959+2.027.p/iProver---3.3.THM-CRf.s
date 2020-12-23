%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n025.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:28:29 EST 2020

% Result     : Theorem 3.51s
% Output     : CNFRefutation 3.51s
% Verified   : 
% Statistics : Number of formulae       :  191 (1662 expanded)
%              Number of clauses        :  112 ( 461 expanded)
%              Number of leaves         :   23 ( 377 expanded)
%              Depth                    :   27
%              Number of atoms          :  764 (14241 expanded)
%              Number of equality atoms :  156 ( 609 expanded)
%              Maximal formula depth    :   14 (   5 average)
%              Maximal clause size      :   26 (   3 average)
%              Maximal term depth       :    5 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f5,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => ! [X2] :
          ( r2_hidden(X2,X1)
         => r2_hidden(X2,X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f21,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( r2_hidden(X2,X0)
          | ~ r2_hidden(X2,X1) )
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f59,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(X2,X0)
      | ~ r2_hidden(X2,X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( ! [X2] :
          ( r2_hidden(X2,X0)
        <=> r2_hidden(X2,X1) )
     => X0 = X1 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f20,plain,(
    ! [X0,X1] :
      ( X0 = X1
      | ? [X2] :
          ( r2_hidden(X2,X0)
        <~> r2_hidden(X2,X1) ) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f40,plain,(
    ! [X0,X1] :
      ( X0 = X1
      | ? [X2] :
          ( ( ~ r2_hidden(X2,X1)
            | ~ r2_hidden(X2,X0) )
          & ( r2_hidden(X2,X1)
            | r2_hidden(X2,X0) ) ) ) ),
    inference(nnf_transformation,[],[f20])).

fof(f41,plain,(
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

fof(f42,plain,(
    ! [X0,X1] :
      ( X0 = X1
      | ( ( ~ r2_hidden(sK0(X0,X1),X1)
          | ~ r2_hidden(sK0(X0,X1),X0) )
        & ( r2_hidden(sK0(X0,X1),X1)
          | r2_hidden(sK0(X0,X1),X0) ) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f40,f41])).

fof(f54,plain,(
    ! [X0,X1] :
      ( X0 = X1
      | r2_hidden(sK0(X0,X1),X1)
      | r2_hidden(sK0(X0,X1),X0) ) ),
    inference(cnf_transformation,[],[f42])).

fof(f6,axiom,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
     => m1_subset_1(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f22,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X0,X1)
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f60,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X0,X1)
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f14,axiom,(
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

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
    inference(ennf_transformation,[],[f14])).

fof(f36,plain,(
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
    inference(flattening,[],[f35])).

fof(f74,plain,(
    ! [X0,X1] :
      ( k1_yellow_0(X0,k5_waybel_0(X0,X1)) = X1
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | ~ v5_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f36])).

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
    inference(ennf_transformation,[],[f18])).

fof(f39,plain,(
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
    inference(flattening,[],[f38])).

fof(f49,plain,(
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
    inference(nnf_transformation,[],[f39])).

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
    inference(flattening,[],[f49])).

fof(f52,plain,(
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

fof(f51,plain,
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

fof(f53,plain,
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
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3,sK4])],[f50,f52,f51])).

fof(f80,plain,(
    v5_orders_2(sK3) ),
    inference(cnf_transformation,[],[f53])).

fof(f77,plain,(
    ~ v2_struct_0(sK3) ),
    inference(cnf_transformation,[],[f53])).

fof(f78,plain,(
    v3_orders_2(sK3) ),
    inference(cnf_transformation,[],[f53])).

fof(f79,plain,(
    v4_orders_2(sK3) ),
    inference(cnf_transformation,[],[f53])).

fof(f82,plain,(
    l1_orders_2(sK3) ),
    inference(cnf_transformation,[],[f53])).

fof(f85,plain,(
    m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(sK3))) ),
    inference(cnf_transformation,[],[f53])).

fof(f8,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(X2))
        & r2_hidden(X0,X1) )
     => m1_subset_1(X0,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f25,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X0,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f26,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X0,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(flattening,[],[f25])).

fof(f62,plain,(
    ! [X2,X0,X1] :
      ( m1_subset_1(X0,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f73,plain,(
    ! [X0,X1] :
      ( r1_yellow_0(X0,k5_waybel_0(X0,X1))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | ~ v5_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f36])).

fof(f2,axiom,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f56,plain,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    inference(cnf_transformation,[],[f2])).

fof(f11,axiom,(
    ! [X0] :
      ( l1_orders_2(X0)
     => ! [X1,X2] :
          ( ( r1_yellow_0(X0,X2)
            & r1_yellow_0(X0,X1)
            & r1_tarski(X1,X2) )
         => r1_orders_2(X0,k1_yellow_0(X0,X1),k1_yellow_0(X0,X2)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f29,plain,(
    ! [X0] :
      ( ! [X1,X2] :
          ( r1_orders_2(X0,k1_yellow_0(X0,X1),k1_yellow_0(X0,X2))
          | ~ r1_yellow_0(X0,X2)
          | ~ r1_yellow_0(X0,X1)
          | ~ r1_tarski(X1,X2) )
      | ~ l1_orders_2(X0) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f30,plain,(
    ! [X0] :
      ( ! [X1,X2] :
          ( r1_orders_2(X0,k1_yellow_0(X0,X1),k1_yellow_0(X0,X2))
          | ~ r1_yellow_0(X0,X2)
          | ~ r1_yellow_0(X0,X1)
          | ~ r1_tarski(X1,X2) )
      | ~ l1_orders_2(X0) ) ),
    inference(flattening,[],[f29])).

fof(f65,plain,(
    ! [X2,X0,X1] :
      ( r1_orders_2(X0,k1_yellow_0(X0,X1),k1_yellow_0(X0,X2))
      | ~ r1_yellow_0(X0,X2)
      | ~ r1_yellow_0(X0,X1)
      | ~ r1_tarski(X1,X2)
      | ~ l1_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f81,plain,(
    v1_yellow_0(sK3) ),
    inference(cnf_transformation,[],[f53])).

fof(f12,axiom,(
    ! [X0] :
      ( ( l1_orders_2(X0)
        & v1_yellow_0(X0)
        & v5_orders_2(X0)
        & ~ v2_struct_0(X0) )
     => ( r2_yellow_0(X0,u1_struct_0(X0))
        & r1_yellow_0(X0,k1_xboole_0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f19,plain,(
    ! [X0] :
      ( ( l1_orders_2(X0)
        & v1_yellow_0(X0)
        & v5_orders_2(X0)
        & ~ v2_struct_0(X0) )
     => r1_yellow_0(X0,k1_xboole_0) ) ),
    inference(pure_predicate_removal,[],[f12])).

fof(f31,plain,(
    ! [X0] :
      ( r1_yellow_0(X0,k1_xboole_0)
      | ~ l1_orders_2(X0)
      | ~ v1_yellow_0(X0)
      | ~ v5_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f19])).

fof(f32,plain,(
    ! [X0] :
      ( r1_yellow_0(X0,k1_xboole_0)
      | ~ l1_orders_2(X0)
      | ~ v1_yellow_0(X0)
      | ~ v5_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f31])).

fof(f66,plain,(
    ! [X0] :
      ( r1_yellow_0(X0,k1_xboole_0)
      | ~ l1_orders_2(X0)
      | ~ v1_yellow_0(X0)
      | ~ v5_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f32])).

fof(f9,axiom,(
    ! [X0] :
      ( l1_orders_2(X0)
     => k3_yellow_0(X0) = k1_yellow_0(X0,k1_xboole_0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f27,plain,(
    ! [X0] :
      ( k3_yellow_0(X0) = k1_yellow_0(X0,k1_xboole_0)
      | ~ l1_orders_2(X0) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f63,plain,(
    ! [X0] :
      ( k3_yellow_0(X0) = k1_yellow_0(X0,k1_xboole_0)
      | ~ l1_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f10,axiom,(
    ! [X0] :
      ( l1_orders_2(X0)
     => m1_subset_1(k3_yellow_0(X0),u1_struct_0(X0)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f28,plain,(
    ! [X0] :
      ( m1_subset_1(k3_yellow_0(X0),u1_struct_0(X0))
      | ~ l1_orders_2(X0) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f64,plain,(
    ! [X0] :
      ( m1_subset_1(k3_yellow_0(X0),u1_struct_0(X0))
      | ~ l1_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f15,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => ( v1_subset_1(X1,X0)
      <=> X0 != X1 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f37,plain,(
    ! [X0,X1] :
      ( ( v1_subset_1(X1,X0)
      <=> X0 != X1 )
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f15])).

fof(f48,plain,(
    ! [X0,X1] :
      ( ( ( v1_subset_1(X1,X0)
          | X0 = X1 )
        & ( X0 != X1
          | ~ v1_subset_1(X1,X0) ) )
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(nnf_transformation,[],[f37])).

fof(f75,plain,(
    ! [X0,X1] :
      ( X0 != X1
      | ~ v1_subset_1(X1,X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f48])).

fof(f88,plain,(
    ! [X1] :
      ( ~ v1_subset_1(X1,X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X1)) ) ),
    inference(equality_resolution,[],[f75])).

fof(f86,plain,
    ( ~ r2_hidden(k3_yellow_0(sK3),sK4)
    | v1_subset_1(sK4,u1_struct_0(sK3)) ),
    inference(cnf_transformation,[],[f53])).

fof(f7,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,X1)
     => ( r2_hidden(X0,X1)
        | v1_xboole_0(X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f23,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
      | v1_xboole_0(X1)
      | ~ m1_subset_1(X0,X1) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f24,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
      | v1_xboole_0(X1)
      | ~ m1_subset_1(X0,X1) ) ),
    inference(flattening,[],[f23])).

fof(f61,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
      | v1_xboole_0(X1)
      | ~ m1_subset_1(X0,X1) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f83,plain,(
    ~ v1_xboole_0(sK4) ),
    inference(cnf_transformation,[],[f53])).

fof(f13,axiom,(
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
    inference(ennf_transformation,[],[f13])).

fof(f34,plain,(
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
    inference(flattening,[],[f33])).

fof(f43,plain,(
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
    inference(nnf_transformation,[],[f34])).

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
    inference(rectify,[],[f43])).

fof(f46,plain,(
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

fof(f45,plain,(
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

fof(f47,plain,(
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
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1,sK2])],[f44,f46,f45])).

fof(f67,plain,(
    ! [X4,X0,X5,X1] :
      ( r2_hidden(X5,X1)
      | ~ r1_orders_2(X0,X4,X5)
      | ~ r2_hidden(X4,X1)
      | ~ m1_subset_1(X5,u1_struct_0(X0))
      | ~ m1_subset_1(X4,u1_struct_0(X0))
      | ~ v13_waybel_0(X1,X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f47])).

fof(f84,plain,(
    v13_waybel_0(sK4,sK3) ),
    inference(cnf_transformation,[],[f53])).

fof(f76,plain,(
    ! [X0,X1] :
      ( v1_subset_1(X1,X0)
      | X0 = X1
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f48])).

fof(f87,plain,
    ( r2_hidden(k3_yellow_0(sK3),sK4)
    | ~ v1_subset_1(sK4,u1_struct_0(sK3)) ),
    inference(cnf_transformation,[],[f53])).

fof(f55,plain,(
    ! [X0,X1] :
      ( X0 = X1
      | ~ r2_hidden(sK0(X0,X1),X1)
      | ~ r2_hidden(sK0(X0,X1),X0) ) ),
    inference(cnf_transformation,[],[f42])).

cnf(c_5,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | ~ r2_hidden(X2,X0)
    | r2_hidden(X2,X1) ),
    inference(cnf_transformation,[],[f59])).

cnf(c_2012,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK3)))
    | ~ r2_hidden(X1,X0)
    | r2_hidden(X1,u1_struct_0(sK3)) ),
    inference(instantiation,[status(thm)],[c_5])).

cnf(c_2254,plain,
    ( ~ m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(sK3)))
    | r2_hidden(X0,u1_struct_0(sK3))
    | ~ r2_hidden(X0,sK4) ),
    inference(instantiation,[status(thm)],[c_2012])).

cnf(c_6992,plain,
    ( ~ m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(sK3)))
    | r2_hidden(sK0(u1_struct_0(sK3),sK4),u1_struct_0(sK3))
    | ~ r2_hidden(sK0(u1_struct_0(sK3),sK4),sK4) ),
    inference(instantiation,[status(thm)],[c_2254])).

cnf(c_1,plain,
    ( r2_hidden(sK0(X0,X1),X1)
    | r2_hidden(sK0(X0,X1),X0)
    | X1 = X0 ),
    inference(cnf_transformation,[],[f54])).

cnf(c_1829,plain,
    ( X0 = X1
    | r2_hidden(sK0(X1,X0),X0) = iProver_top
    | r2_hidden(sK0(X1,X0),X1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1])).

cnf(c_6,plain,
    ( m1_subset_1(X0,X1)
    | ~ r2_hidden(X0,X1) ),
    inference(cnf_transformation,[],[f60])).

cnf(c_1826,plain,
    ( m1_subset_1(X0,X1) = iProver_top
    | r2_hidden(X0,X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_6])).

cnf(c_2463,plain,
    ( X0 = X1
    | m1_subset_1(sK0(X0,X1),X0) = iProver_top
    | r2_hidden(sK0(X0,X1),X1) = iProver_top ),
    inference(superposition,[status(thm)],[c_1829,c_1826])).

cnf(c_19,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(X1))
    | ~ v3_orders_2(X1)
    | ~ v4_orders_2(X1)
    | v2_struct_0(X1)
    | ~ v5_orders_2(X1)
    | ~ l1_orders_2(X1)
    | k1_yellow_0(X1,k5_waybel_0(X1,X0)) = X0 ),
    inference(cnf_transformation,[],[f74])).

cnf(c_30,negated_conjecture,
    ( v5_orders_2(sK3) ),
    inference(cnf_transformation,[],[f80])).

cnf(c_550,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(X1))
    | ~ v3_orders_2(X1)
    | ~ v4_orders_2(X1)
    | v2_struct_0(X1)
    | ~ l1_orders_2(X1)
    | k1_yellow_0(X1,k5_waybel_0(X1,X0)) = X0
    | sK3 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_19,c_30])).

cnf(c_551,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(sK3))
    | ~ v3_orders_2(sK3)
    | ~ v4_orders_2(sK3)
    | v2_struct_0(sK3)
    | ~ l1_orders_2(sK3)
    | k1_yellow_0(sK3,k5_waybel_0(sK3,X0)) = X0 ),
    inference(unflattening,[status(thm)],[c_550])).

cnf(c_33,negated_conjecture,
    ( ~ v2_struct_0(sK3) ),
    inference(cnf_transformation,[],[f77])).

cnf(c_32,negated_conjecture,
    ( v3_orders_2(sK3) ),
    inference(cnf_transformation,[],[f78])).

cnf(c_31,negated_conjecture,
    ( v4_orders_2(sK3) ),
    inference(cnf_transformation,[],[f79])).

cnf(c_28,negated_conjecture,
    ( l1_orders_2(sK3) ),
    inference(cnf_transformation,[],[f82])).

cnf(c_555,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(sK3))
    | k1_yellow_0(sK3,k5_waybel_0(sK3,X0)) = X0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_551,c_33,c_32,c_31,c_28])).

cnf(c_1819,plain,
    ( k1_yellow_0(sK3,k5_waybel_0(sK3,X0)) = X0
    | m1_subset_1(X0,u1_struct_0(sK3)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_555])).

cnf(c_3443,plain,
    ( k1_yellow_0(sK3,k5_waybel_0(sK3,sK0(u1_struct_0(sK3),X0))) = sK0(u1_struct_0(sK3),X0)
    | u1_struct_0(sK3) = X0
    | r2_hidden(sK0(u1_struct_0(sK3),X0),X0) = iProver_top ),
    inference(superposition,[status(thm)],[c_2463,c_1819])).

cnf(c_25,negated_conjecture,
    ( m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(sK3))) ),
    inference(cnf_transformation,[],[f85])).

cnf(c_1824,plain,
    ( m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(sK3))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_25])).

cnf(c_8,plain,
    ( m1_subset_1(X0,X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(X1))
    | ~ r2_hidden(X0,X2) ),
    inference(cnf_transformation,[],[f62])).

cnf(c_1825,plain,
    ( m1_subset_1(X0,X1) = iProver_top
    | m1_subset_1(X2,k1_zfmisc_1(X1)) != iProver_top
    | r2_hidden(X0,X2) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_8])).

cnf(c_2822,plain,
    ( m1_subset_1(X0,u1_struct_0(sK3)) = iProver_top
    | r2_hidden(X0,sK4) != iProver_top ),
    inference(superposition,[status(thm)],[c_1824,c_1825])).

cnf(c_2852,plain,
    ( k1_yellow_0(sK3,k5_waybel_0(sK3,X0)) = X0
    | r2_hidden(X0,sK4) != iProver_top ),
    inference(superposition,[status(thm)],[c_2822,c_1819])).

cnf(c_3791,plain,
    ( k1_yellow_0(sK3,k5_waybel_0(sK3,sK0(u1_struct_0(sK3),sK4))) = sK0(u1_struct_0(sK3),sK4)
    | u1_struct_0(sK3) = sK4 ),
    inference(superposition,[status(thm)],[c_3443,c_2852])).

cnf(c_20,plain,
    ( r1_yellow_0(X0,k5_waybel_0(X0,X1))
    | ~ m1_subset_1(X1,u1_struct_0(X0))
    | ~ v3_orders_2(X0)
    | ~ v4_orders_2(X0)
    | v2_struct_0(X0)
    | ~ v5_orders_2(X0)
    | ~ l1_orders_2(X0) ),
    inference(cnf_transformation,[],[f73])).

cnf(c_532,plain,
    ( r1_yellow_0(X0,k5_waybel_0(X0,X1))
    | ~ m1_subset_1(X1,u1_struct_0(X0))
    | ~ v3_orders_2(X0)
    | ~ v4_orders_2(X0)
    | v2_struct_0(X0)
    | ~ l1_orders_2(X0)
    | sK3 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_20,c_30])).

cnf(c_533,plain,
    ( r1_yellow_0(sK3,k5_waybel_0(sK3,X0))
    | ~ m1_subset_1(X0,u1_struct_0(sK3))
    | ~ v3_orders_2(sK3)
    | ~ v4_orders_2(sK3)
    | v2_struct_0(sK3)
    | ~ l1_orders_2(sK3) ),
    inference(unflattening,[status(thm)],[c_532])).

cnf(c_537,plain,
    ( r1_yellow_0(sK3,k5_waybel_0(sK3,X0))
    | ~ m1_subset_1(X0,u1_struct_0(sK3)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_533,c_33,c_32,c_31,c_28])).

cnf(c_2,plain,
    ( r1_tarski(k1_xboole_0,X0) ),
    inference(cnf_transformation,[],[f56])).

cnf(c_11,plain,
    ( r1_orders_2(X0,k1_yellow_0(X0,X1),k1_yellow_0(X0,X2))
    | ~ r1_yellow_0(X0,X2)
    | ~ r1_yellow_0(X0,X1)
    | ~ r1_tarski(X1,X2)
    | ~ l1_orders_2(X0) ),
    inference(cnf_transformation,[],[f65])).

cnf(c_459,plain,
    ( r1_orders_2(X0,k1_yellow_0(X0,X1),k1_yellow_0(X0,X2))
    | ~ r1_yellow_0(X0,X2)
    | ~ r1_yellow_0(X0,X1)
    | ~ l1_orders_2(X0)
    | X2 != X3
    | k1_xboole_0 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_2,c_11])).

cnf(c_460,plain,
    ( r1_orders_2(X0,k1_yellow_0(X0,k1_xboole_0),k1_yellow_0(X0,X1))
    | ~ r1_yellow_0(X0,X1)
    | ~ r1_yellow_0(X0,k1_xboole_0)
    | ~ l1_orders_2(X0) ),
    inference(unflattening,[status(thm)],[c_459])).

cnf(c_654,plain,
    ( r1_orders_2(X0,k1_yellow_0(X0,k1_xboole_0),k1_yellow_0(X0,X1))
    | ~ r1_yellow_0(X0,X1)
    | ~ r1_yellow_0(X0,k1_xboole_0)
    | sK3 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_460,c_28])).

cnf(c_655,plain,
    ( r1_orders_2(sK3,k1_yellow_0(sK3,k1_xboole_0),k1_yellow_0(sK3,X0))
    | ~ r1_yellow_0(sK3,X0)
    | ~ r1_yellow_0(sK3,k1_xboole_0) ),
    inference(unflattening,[status(thm)],[c_654])).

cnf(c_29,negated_conjecture,
    ( v1_yellow_0(sK3) ),
    inference(cnf_transformation,[],[f81])).

cnf(c_12,plain,
    ( r1_yellow_0(X0,k1_xboole_0)
    | v2_struct_0(X0)
    | ~ v5_orders_2(X0)
    | ~ v1_yellow_0(X0)
    | ~ l1_orders_2(X0) ),
    inference(cnf_transformation,[],[f66])).

cnf(c_74,plain,
    ( r1_yellow_0(sK3,k1_xboole_0)
    | v2_struct_0(sK3)
    | ~ v5_orders_2(sK3)
    | ~ v1_yellow_0(sK3)
    | ~ l1_orders_2(sK3) ),
    inference(instantiation,[status(thm)],[c_12])).

cnf(c_659,plain,
    ( ~ r1_yellow_0(sK3,X0)
    | r1_orders_2(sK3,k1_yellow_0(sK3,k1_xboole_0),k1_yellow_0(sK3,X0)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_655,c_33,c_30,c_29,c_28,c_74])).

cnf(c_660,plain,
    ( r1_orders_2(sK3,k1_yellow_0(sK3,k1_xboole_0),k1_yellow_0(sK3,X0))
    | ~ r1_yellow_0(sK3,X0) ),
    inference(renaming,[status(thm)],[c_659])).

cnf(c_824,plain,
    ( r1_orders_2(sK3,k1_yellow_0(sK3,k1_xboole_0),k1_yellow_0(sK3,X0))
    | ~ m1_subset_1(X1,u1_struct_0(sK3))
    | k5_waybel_0(sK3,X1) != X0
    | sK3 != sK3 ),
    inference(resolution_lifted,[status(thm)],[c_537,c_660])).

cnf(c_825,plain,
    ( r1_orders_2(sK3,k1_yellow_0(sK3,k1_xboole_0),k1_yellow_0(sK3,k5_waybel_0(sK3,X0)))
    | ~ m1_subset_1(X0,u1_struct_0(sK3)) ),
    inference(unflattening,[status(thm)],[c_824])).

cnf(c_1810,plain,
    ( r1_orders_2(sK3,k1_yellow_0(sK3,k1_xboole_0),k1_yellow_0(sK3,k5_waybel_0(sK3,X0))) = iProver_top
    | m1_subset_1(X0,u1_struct_0(sK3)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_825])).

cnf(c_9,plain,
    ( ~ l1_orders_2(X0)
    | k1_yellow_0(X0,k1_xboole_0) = k3_yellow_0(X0) ),
    inference(cnf_transformation,[],[f63])).

cnf(c_719,plain,
    ( k1_yellow_0(X0,k1_xboole_0) = k3_yellow_0(X0)
    | sK3 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_9,c_28])).

cnf(c_720,plain,
    ( k1_yellow_0(sK3,k1_xboole_0) = k3_yellow_0(sK3) ),
    inference(unflattening,[status(thm)],[c_719])).

cnf(c_1833,plain,
    ( r1_orders_2(sK3,k3_yellow_0(sK3),k1_yellow_0(sK3,k5_waybel_0(sK3,X0))) = iProver_top
    | m1_subset_1(X0,u1_struct_0(sK3)) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_1810,c_720])).

cnf(c_5652,plain,
    ( u1_struct_0(sK3) = sK4
    | r1_orders_2(sK3,k3_yellow_0(sK3),sK0(u1_struct_0(sK3),sK4)) = iProver_top
    | m1_subset_1(sK0(u1_struct_0(sK3),sK4),u1_struct_0(sK3)) != iProver_top ),
    inference(superposition,[status(thm)],[c_3791,c_1833])).

cnf(c_10,plain,
    ( m1_subset_1(k3_yellow_0(X0),u1_struct_0(X0))
    | ~ l1_orders_2(X0) ),
    inference(cnf_transformation,[],[f64])).

cnf(c_80,plain,
    ( m1_subset_1(k3_yellow_0(sK3),u1_struct_0(sK3))
    | ~ l1_orders_2(sK3) ),
    inference(instantiation,[status(thm)],[c_10])).

cnf(c_22,plain,
    ( ~ v1_subset_1(X0,X0)
    | ~ m1_subset_1(X0,k1_zfmisc_1(X0)) ),
    inference(cnf_transformation,[],[f88])).

cnf(c_24,negated_conjecture,
    ( v1_subset_1(sK4,u1_struct_0(sK3))
    | ~ r2_hidden(k3_yellow_0(sK3),sK4) ),
    inference(cnf_transformation,[],[f86])).

cnf(c_246,plain,
    ( v1_subset_1(sK4,u1_struct_0(sK3))
    | ~ r2_hidden(k3_yellow_0(sK3),sK4) ),
    inference(prop_impl,[status(thm)],[c_24])).

cnf(c_512,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X0))
    | ~ r2_hidden(k3_yellow_0(sK3),sK4)
    | u1_struct_0(sK3) != X0
    | sK4 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_22,c_246])).

cnf(c_513,plain,
    ( ~ m1_subset_1(u1_struct_0(sK3),k1_zfmisc_1(u1_struct_0(sK3)))
    | ~ r2_hidden(k3_yellow_0(sK3),sK4)
    | sK4 != u1_struct_0(sK3) ),
    inference(unflattening,[status(thm)],[c_512])).

cnf(c_1445,plain,
    ( X0 != X1
    | k3_yellow_0(X0) = k3_yellow_0(X1) ),
    theory(equality)).

cnf(c_1456,plain,
    ( k3_yellow_0(sK3) = k3_yellow_0(sK3)
    | sK3 != sK3 ),
    inference(instantiation,[status(thm)],[c_1445])).

cnf(c_1440,plain,
    ( X0 = X0 ),
    theory(equality)).

cnf(c_1465,plain,
    ( sK3 = sK3 ),
    inference(instantiation,[status(thm)],[c_1440])).

cnf(c_2358,plain,
    ( sK4 = sK4 ),
    inference(instantiation,[status(thm)],[c_1440])).

cnf(c_2404,plain,
    ( k1_zfmisc_1(u1_struct_0(sK3)) = k1_zfmisc_1(u1_struct_0(sK3)) ),
    inference(instantiation,[status(thm)],[c_1440])).

cnf(c_1444,plain,
    ( ~ m1_subset_1(X0,X1)
    | m1_subset_1(X2,X3)
    | X2 != X0
    | X3 != X1 ),
    theory(equality)).

cnf(c_1882,plain,
    ( ~ m1_subset_1(X0,X1)
    | m1_subset_1(X2,sK4)
    | X2 != X0
    | sK4 != X1 ),
    inference(instantiation,[status(thm)],[c_1444])).

cnf(c_2326,plain,
    ( m1_subset_1(X0,sK4)
    | ~ m1_subset_1(k3_yellow_0(sK3),u1_struct_0(sK3))
    | X0 != k3_yellow_0(sK3)
    | sK4 != u1_struct_0(sK3) ),
    inference(instantiation,[status(thm)],[c_1882])).

cnf(c_2622,plain,
    ( ~ m1_subset_1(k3_yellow_0(sK3),u1_struct_0(sK3))
    | m1_subset_1(k3_yellow_0(sK3),sK4)
    | k3_yellow_0(sK3) != k3_yellow_0(sK3)
    | sK4 != u1_struct_0(sK3) ),
    inference(instantiation,[status(thm)],[c_2326])).

cnf(c_2892,plain,
    ( m1_subset_1(X0,X1)
    | ~ m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(sK3)))
    | X1 != k1_zfmisc_1(u1_struct_0(sK3))
    | X0 != sK4 ),
    inference(instantiation,[status(thm)],[c_1444])).

cnf(c_3148,plain,
    ( m1_subset_1(u1_struct_0(sK3),X0)
    | ~ m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(sK3)))
    | X0 != k1_zfmisc_1(u1_struct_0(sK3))
    | u1_struct_0(sK3) != sK4 ),
    inference(instantiation,[status(thm)],[c_2892])).

cnf(c_3572,plain,
    ( m1_subset_1(u1_struct_0(sK3),k1_zfmisc_1(u1_struct_0(sK3)))
    | ~ m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(sK3)))
    | u1_struct_0(sK3) != sK4
    | k1_zfmisc_1(u1_struct_0(sK3)) != k1_zfmisc_1(u1_struct_0(sK3)) ),
    inference(instantiation,[status(thm)],[c_3148])).

cnf(c_1441,plain,
    ( X0 != X1
    | X2 != X1
    | X2 = X0 ),
    theory(equality)).

cnf(c_2104,plain,
    ( X0 != X1
    | sK4 != X1
    | sK4 = X0 ),
    inference(instantiation,[status(thm)],[c_1441])).

cnf(c_2366,plain,
    ( u1_struct_0(sK3) != X0
    | sK4 != X0
    | sK4 = u1_struct_0(sK3) ),
    inference(instantiation,[status(thm)],[c_2104])).

cnf(c_4510,plain,
    ( u1_struct_0(sK3) != sK4
    | sK4 = u1_struct_0(sK3)
    | sK4 != sK4 ),
    inference(instantiation,[status(thm)],[c_2366])).

cnf(c_7,plain,
    ( ~ m1_subset_1(X0,X1)
    | r2_hidden(X0,X1)
    | v1_xboole_0(X1) ),
    inference(cnf_transformation,[],[f61])).

cnf(c_27,negated_conjecture,
    ( ~ v1_xboole_0(sK4) ),
    inference(cnf_transformation,[],[f83])).

cnf(c_444,plain,
    ( ~ m1_subset_1(X0,X1)
    | r2_hidden(X0,X1)
    | sK4 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_7,c_27])).

cnf(c_445,plain,
    ( ~ m1_subset_1(X0,sK4)
    | r2_hidden(X0,sK4) ),
    inference(unflattening,[status(thm)],[c_444])).

cnf(c_5720,plain,
    ( ~ m1_subset_1(k3_yellow_0(sK3),sK4)
    | r2_hidden(k3_yellow_0(sK3),sK4) ),
    inference(instantiation,[status(thm)],[c_445])).

cnf(c_5861,plain,
    ( r1_orders_2(sK3,k3_yellow_0(sK3),sK0(u1_struct_0(sK3),sK4)) = iProver_top
    | m1_subset_1(sK0(u1_struct_0(sK3),sK4),u1_struct_0(sK3)) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_5652,c_28,c_25,c_80,c_513,c_1456,c_1465,c_2358,c_2404,c_2622,c_3572,c_4510,c_5720])).

cnf(c_18,plain,
    ( ~ r1_orders_2(X0,X1,X2)
    | ~ v13_waybel_0(X3,X0)
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | ~ m1_subset_1(X1,u1_struct_0(X0))
    | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))
    | ~ r2_hidden(X1,X3)
    | r2_hidden(X2,X3)
    | ~ l1_orders_2(X0) ),
    inference(cnf_transformation,[],[f67])).

cnf(c_672,plain,
    ( ~ r1_orders_2(X0,X1,X2)
    | ~ v13_waybel_0(X3,X0)
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | ~ m1_subset_1(X1,u1_struct_0(X0))
    | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))
    | ~ r2_hidden(X1,X3)
    | r2_hidden(X2,X3)
    | sK3 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_18,c_28])).

cnf(c_673,plain,
    ( ~ r1_orders_2(sK3,X0,X1)
    | ~ v13_waybel_0(X2,sK3)
    | ~ m1_subset_1(X0,u1_struct_0(sK3))
    | ~ m1_subset_1(X1,u1_struct_0(sK3))
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK3)))
    | ~ r2_hidden(X0,X2)
    | r2_hidden(X1,X2) ),
    inference(unflattening,[status(thm)],[c_672])).

cnf(c_689,plain,
    ( ~ r1_orders_2(sK3,X0,X1)
    | ~ v13_waybel_0(X2,sK3)
    | ~ m1_subset_1(X1,u1_struct_0(sK3))
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK3)))
    | ~ r2_hidden(X0,X2)
    | r2_hidden(X1,X2) ),
    inference(forward_subsumption_resolution,[status(thm)],[c_673,c_8])).

cnf(c_1818,plain,
    ( r1_orders_2(sK3,X0,X1) != iProver_top
    | v13_waybel_0(X2,sK3) != iProver_top
    | m1_subset_1(X1,u1_struct_0(sK3)) != iProver_top
    | m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK3))) != iProver_top
    | r2_hidden(X0,X2) != iProver_top
    | r2_hidden(X1,X2) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_689])).

cnf(c_2744,plain,
    ( r1_orders_2(sK3,X0,X1) != iProver_top
    | v13_waybel_0(sK4,sK3) != iProver_top
    | m1_subset_1(X1,u1_struct_0(sK3)) != iProver_top
    | r2_hidden(X0,sK4) != iProver_top
    | r2_hidden(X1,sK4) = iProver_top ),
    inference(superposition,[status(thm)],[c_1824,c_1818])).

cnf(c_42,plain,
    ( m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(sK3))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_25])).

cnf(c_26,negated_conjecture,
    ( v13_waybel_0(sK4,sK3) ),
    inference(cnf_transformation,[],[f84])).

cnf(c_904,plain,
    ( ~ r1_orders_2(sK3,X0,X1)
    | ~ m1_subset_1(X1,u1_struct_0(sK3))
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK3)))
    | ~ r2_hidden(X0,X2)
    | r2_hidden(X1,X2)
    | sK4 != X2
    | sK3 != sK3 ),
    inference(resolution_lifted,[status(thm)],[c_26,c_689])).

cnf(c_905,plain,
    ( ~ r1_orders_2(sK3,X0,X1)
    | ~ m1_subset_1(X1,u1_struct_0(sK3))
    | ~ m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(sK3)))
    | ~ r2_hidden(X0,sK4)
    | r2_hidden(X1,sK4) ),
    inference(unflattening,[status(thm)],[c_904])).

cnf(c_906,plain,
    ( r1_orders_2(sK3,X0,X1) != iProver_top
    | m1_subset_1(X1,u1_struct_0(sK3)) != iProver_top
    | m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(sK3))) != iProver_top
    | r2_hidden(X0,sK4) != iProver_top
    | r2_hidden(X1,sK4) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_905])).

cnf(c_2797,plain,
    ( r1_orders_2(sK3,X0,X1) != iProver_top
    | m1_subset_1(X1,u1_struct_0(sK3)) != iProver_top
    | r2_hidden(X0,sK4) != iProver_top
    | r2_hidden(X1,sK4) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_2744,c_42,c_906])).

cnf(c_5866,plain,
    ( m1_subset_1(sK0(u1_struct_0(sK3),sK4),u1_struct_0(sK3)) != iProver_top
    | r2_hidden(sK0(u1_struct_0(sK3),sK4),sK4) = iProver_top
    | r2_hidden(k3_yellow_0(sK3),sK4) != iProver_top ),
    inference(superposition,[status(thm)],[c_5861,c_2797])).

cnf(c_21,plain,
    ( v1_subset_1(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | X0 = X1 ),
    inference(cnf_transformation,[],[f76])).

cnf(c_23,negated_conjecture,
    ( ~ v1_subset_1(sK4,u1_struct_0(sK3))
    | r2_hidden(k3_yellow_0(sK3),sK4) ),
    inference(cnf_transformation,[],[f87])).

cnf(c_248,plain,
    ( ~ v1_subset_1(sK4,u1_struct_0(sK3))
    | r2_hidden(k3_yellow_0(sK3),sK4) ),
    inference(prop_impl,[status(thm)],[c_23])).

cnf(c_498,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | r2_hidden(k3_yellow_0(sK3),sK4)
    | X1 = X0
    | u1_struct_0(sK3) != X1
    | sK4 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_21,c_248])).

cnf(c_499,plain,
    ( ~ m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(sK3)))
    | r2_hidden(k3_yellow_0(sK3),sK4)
    | u1_struct_0(sK3) = sK4 ),
    inference(unflattening,[status(thm)],[c_498])).

cnf(c_501,plain,
    ( r2_hidden(k3_yellow_0(sK3),sK4)
    | u1_struct_0(sK3) = sK4 ),
    inference(global_propositional_subsumption,[status(thm)],[c_499,c_25])).

cnf(c_503,plain,
    ( u1_struct_0(sK3) = sK4
    | r2_hidden(k3_yellow_0(sK3),sK4) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_501])).

cnf(c_5870,plain,
    ( r2_hidden(sK0(u1_struct_0(sK3),sK4),sK4) = iProver_top
    | m1_subset_1(sK0(u1_struct_0(sK3),sK4),u1_struct_0(sK3)) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_5866,c_28,c_25,c_80,c_503,c_513,c_1456,c_1465,c_2358,c_2404,c_2622,c_3572,c_4510,c_5720])).

cnf(c_5871,plain,
    ( m1_subset_1(sK0(u1_struct_0(sK3),sK4),u1_struct_0(sK3)) != iProver_top
    | r2_hidden(sK0(u1_struct_0(sK3),sK4),sK4) = iProver_top ),
    inference(renaming,[status(thm)],[c_5870])).

cnf(c_5876,plain,
    ( u1_struct_0(sK3) = sK4
    | r2_hidden(sK0(u1_struct_0(sK3),sK4),sK4) = iProver_top ),
    inference(superposition,[status(thm)],[c_2463,c_5871])).

cnf(c_6811,plain,
    ( r2_hidden(sK0(u1_struct_0(sK3),sK4),sK4) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_5876,c_28,c_25,c_80,c_513,c_1456,c_1465,c_2358,c_2404,c_2622,c_3572,c_4510,c_5720])).

cnf(c_0,plain,
    ( ~ r2_hidden(sK0(X0,X1),X1)
    | ~ r2_hidden(sK0(X0,X1),X0)
    | X1 = X0 ),
    inference(cnf_transformation,[],[f55])).

cnf(c_1830,plain,
    ( X0 = X1
    | r2_hidden(sK0(X1,X0),X0) != iProver_top
    | r2_hidden(sK0(X1,X0),X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_0])).

cnf(c_6816,plain,
    ( u1_struct_0(sK3) = sK4
    | r2_hidden(sK0(u1_struct_0(sK3),sK4),u1_struct_0(sK3)) != iProver_top ),
    inference(superposition,[status(thm)],[c_6811,c_1830])).

cnf(c_6819,plain,
    ( ~ r2_hidden(sK0(u1_struct_0(sK3),sK4),u1_struct_0(sK3))
    | u1_struct_0(sK3) = sK4 ),
    inference(predicate_to_equality_rev,[status(thm)],[c_6816])).

cnf(c_6813,plain,
    ( r2_hidden(sK0(u1_struct_0(sK3),sK4),sK4) ),
    inference(predicate_to_equality_rev,[status(thm)],[c_6811])).

cnf(c_2091,plain,
    ( ~ r2_hidden(sK0(X0,sK4),X0)
    | ~ r2_hidden(sK0(X0,sK4),sK4)
    | sK4 = X0 ),
    inference(instantiation,[status(thm)],[c_0])).

cnf(c_2316,plain,
    ( ~ r2_hidden(sK0(u1_struct_0(sK3),sK4),u1_struct_0(sK3))
    | ~ r2_hidden(sK0(u1_struct_0(sK3),sK4),sK4)
    | sK4 = u1_struct_0(sK3) ),
    inference(instantiation,[status(thm)],[c_2091])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_6992,c_6819,c_6813,c_5720,c_3572,c_2622,c_2404,c_2316,c_1465,c_1456,c_513,c_80,c_25,c_28])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : iproveropt_run.sh %d %s
% 0.14/0.34  % Computer   : n025.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % WCLimit    : 600
% 0.14/0.34  % DateTime   : Tue Dec  1 16:31:51 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.34  % Running in FOF mode
% 3.51/0.98  % SZS status Started for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.51/0.98  
% 3.51/0.98  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 3.51/0.98  
% 3.51/0.98  ------  iProver source info
% 3.51/0.98  
% 3.51/0.98  git: date: 2020-06-30 10:37:57 +0100
% 3.51/0.98  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 3.51/0.98  git: non_committed_changes: false
% 3.51/0.98  git: last_make_outside_of_git: false
% 3.51/0.98  
% 3.51/0.98  ------ 
% 3.51/0.98  
% 3.51/0.98  ------ Input Options
% 3.51/0.98  
% 3.51/0.98  --out_options                           all
% 3.51/0.98  --tptp_safe_out                         true
% 3.51/0.98  --problem_path                          ""
% 3.51/0.98  --include_path                          ""
% 3.51/0.98  --clausifier                            res/vclausify_rel
% 3.51/0.98  --clausifier_options                    ""
% 3.51/0.98  --stdin                                 false
% 3.51/0.98  --stats_out                             all
% 3.51/0.98  
% 3.51/0.98  ------ General Options
% 3.51/0.98  
% 3.51/0.98  --fof                                   false
% 3.51/0.98  --time_out_real                         305.
% 3.51/0.98  --time_out_virtual                      -1.
% 3.51/0.98  --symbol_type_check                     false
% 3.51/0.98  --clausify_out                          false
% 3.51/0.98  --sig_cnt_out                           false
% 3.51/0.98  --trig_cnt_out                          false
% 3.51/0.98  --trig_cnt_out_tolerance                1.
% 3.51/0.98  --trig_cnt_out_sk_spl                   false
% 3.51/0.98  --abstr_cl_out                          false
% 3.51/0.98  
% 3.51/0.98  ------ Global Options
% 3.51/0.98  
% 3.51/0.98  --schedule                              default
% 3.51/0.98  --add_important_lit                     false
% 3.51/0.98  --prop_solver_per_cl                    1000
% 3.51/0.98  --min_unsat_core                        false
% 3.51/0.98  --soft_assumptions                      false
% 3.51/0.98  --soft_lemma_size                       3
% 3.51/0.98  --prop_impl_unit_size                   0
% 3.51/0.98  --prop_impl_unit                        []
% 3.51/0.98  --share_sel_clauses                     true
% 3.51/0.98  --reset_solvers                         false
% 3.51/0.98  --bc_imp_inh                            [conj_cone]
% 3.51/0.98  --conj_cone_tolerance                   3.
% 3.51/0.98  --extra_neg_conj                        none
% 3.51/0.98  --large_theory_mode                     true
% 3.51/0.98  --prolific_symb_bound                   200
% 3.51/0.98  --lt_threshold                          2000
% 3.51/0.98  --clause_weak_htbl                      true
% 3.51/0.98  --gc_record_bc_elim                     false
% 3.51/0.98  
% 3.51/0.98  ------ Preprocessing Options
% 3.51/0.98  
% 3.51/0.98  --preprocessing_flag                    true
% 3.51/0.98  --time_out_prep_mult                    0.1
% 3.51/0.98  --splitting_mode                        input
% 3.51/0.98  --splitting_grd                         true
% 3.51/0.98  --splitting_cvd                         false
% 3.51/0.98  --splitting_cvd_svl                     false
% 3.51/0.98  --splitting_nvd                         32
% 3.51/0.98  --sub_typing                            true
% 3.51/0.98  --prep_gs_sim                           true
% 3.51/0.98  --prep_unflatten                        true
% 3.51/0.98  --prep_res_sim                          true
% 3.51/0.98  --prep_upred                            true
% 3.51/0.98  --prep_sem_filter                       exhaustive
% 3.51/0.98  --prep_sem_filter_out                   false
% 3.51/0.98  --pred_elim                             true
% 3.51/0.98  --res_sim_input                         true
% 3.51/0.98  --eq_ax_congr_red                       true
% 3.51/0.98  --pure_diseq_elim                       true
% 3.51/0.98  --brand_transform                       false
% 3.51/0.98  --non_eq_to_eq                          false
% 3.51/0.98  --prep_def_merge                        true
% 3.51/0.98  --prep_def_merge_prop_impl              false
% 3.51/0.98  --prep_def_merge_mbd                    true
% 3.51/0.98  --prep_def_merge_tr_red                 false
% 3.51/0.98  --prep_def_merge_tr_cl                  false
% 3.51/0.98  --smt_preprocessing                     true
% 3.51/0.98  --smt_ac_axioms                         fast
% 3.51/0.98  --preprocessed_out                      false
% 3.51/0.98  --preprocessed_stats                    false
% 3.51/0.98  
% 3.51/0.98  ------ Abstraction refinement Options
% 3.51/0.98  
% 3.51/0.98  --abstr_ref                             []
% 3.51/0.98  --abstr_ref_prep                        false
% 3.51/0.98  --abstr_ref_until_sat                   false
% 3.51/0.98  --abstr_ref_sig_restrict                funpre
% 3.51/0.98  --abstr_ref_af_restrict_to_split_sk     false
% 3.51/0.98  --abstr_ref_under                       []
% 3.51/0.98  
% 3.51/0.98  ------ SAT Options
% 3.51/0.98  
% 3.51/0.98  --sat_mode                              false
% 3.51/0.98  --sat_fm_restart_options                ""
% 3.51/0.98  --sat_gr_def                            false
% 3.51/0.98  --sat_epr_types                         true
% 3.51/0.98  --sat_non_cyclic_types                  false
% 3.51/0.98  --sat_finite_models                     false
% 3.51/0.98  --sat_fm_lemmas                         false
% 3.51/0.98  --sat_fm_prep                           false
% 3.51/0.98  --sat_fm_uc_incr                        true
% 3.51/0.98  --sat_out_model                         small
% 3.51/0.98  --sat_out_clauses                       false
% 3.51/0.98  
% 3.51/0.98  ------ QBF Options
% 3.51/0.98  
% 3.51/0.98  --qbf_mode                              false
% 3.51/0.98  --qbf_elim_univ                         false
% 3.51/0.98  --qbf_dom_inst                          none
% 3.51/0.98  --qbf_dom_pre_inst                      false
% 3.51/0.98  --qbf_sk_in                             false
% 3.51/0.98  --qbf_pred_elim                         true
% 3.51/0.98  --qbf_split                             512
% 3.51/0.98  
% 3.51/0.98  ------ BMC1 Options
% 3.51/0.98  
% 3.51/0.98  --bmc1_incremental                      false
% 3.51/0.98  --bmc1_axioms                           reachable_all
% 3.51/0.98  --bmc1_min_bound                        0
% 3.51/0.98  --bmc1_max_bound                        -1
% 3.51/0.98  --bmc1_max_bound_default                -1
% 3.51/0.98  --bmc1_symbol_reachability              true
% 3.51/0.98  --bmc1_property_lemmas                  false
% 3.51/0.98  --bmc1_k_induction                      false
% 3.51/0.98  --bmc1_non_equiv_states                 false
% 3.51/0.98  --bmc1_deadlock                         false
% 3.51/0.98  --bmc1_ucm                              false
% 3.51/0.98  --bmc1_add_unsat_core                   none
% 3.51/0.98  --bmc1_unsat_core_children              false
% 3.51/0.98  --bmc1_unsat_core_extrapolate_axioms    false
% 3.51/0.98  --bmc1_out_stat                         full
% 3.51/0.98  --bmc1_ground_init                      false
% 3.51/0.98  --bmc1_pre_inst_next_state              false
% 3.51/0.98  --bmc1_pre_inst_state                   false
% 3.51/0.98  --bmc1_pre_inst_reach_state             false
% 3.51/0.98  --bmc1_out_unsat_core                   false
% 3.51/0.98  --bmc1_aig_witness_out                  false
% 3.51/0.98  --bmc1_verbose                          false
% 3.51/0.98  --bmc1_dump_clauses_tptp                false
% 3.51/0.98  --bmc1_dump_unsat_core_tptp             false
% 3.51/0.98  --bmc1_dump_file                        -
% 3.51/0.98  --bmc1_ucm_expand_uc_limit              128
% 3.51/0.98  --bmc1_ucm_n_expand_iterations          6
% 3.51/0.98  --bmc1_ucm_extend_mode                  1
% 3.51/0.98  --bmc1_ucm_init_mode                    2
% 3.51/0.98  --bmc1_ucm_cone_mode                    none
% 3.51/0.98  --bmc1_ucm_reduced_relation_type        0
% 3.51/0.98  --bmc1_ucm_relax_model                  4
% 3.51/0.98  --bmc1_ucm_full_tr_after_sat            true
% 3.51/0.98  --bmc1_ucm_expand_neg_assumptions       false
% 3.51/0.98  --bmc1_ucm_layered_model                none
% 3.51/0.98  --bmc1_ucm_max_lemma_size               10
% 3.51/0.98  
% 3.51/0.98  ------ AIG Options
% 3.51/0.98  
% 3.51/0.98  --aig_mode                              false
% 3.51/0.98  
% 3.51/0.98  ------ Instantiation Options
% 3.51/0.98  
% 3.51/0.98  --instantiation_flag                    true
% 3.51/0.98  --inst_sos_flag                         true
% 3.51/0.98  --inst_sos_phase                        true
% 3.51/0.98  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 3.51/0.98  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 3.51/0.98  --inst_lit_sel_side                     num_symb
% 3.51/0.98  --inst_solver_per_active                1400
% 3.51/0.98  --inst_solver_calls_frac                1.
% 3.51/0.98  --inst_passive_queue_type               priority_queues
% 3.51/0.98  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 3.51/0.98  --inst_passive_queues_freq              [25;2]
% 3.51/0.98  --inst_dismatching                      true
% 3.51/0.98  --inst_eager_unprocessed_to_passive     true
% 3.51/0.98  --inst_prop_sim_given                   true
% 3.51/0.98  --inst_prop_sim_new                     false
% 3.51/0.98  --inst_subs_new                         false
% 3.51/0.98  --inst_eq_res_simp                      false
% 3.51/0.98  --inst_subs_given                       false
% 3.51/0.98  --inst_orphan_elimination               true
% 3.51/0.98  --inst_learning_loop_flag               true
% 3.51/0.98  --inst_learning_start                   3000
% 3.51/0.98  --inst_learning_factor                  2
% 3.51/0.98  --inst_start_prop_sim_after_learn       3
% 3.51/0.98  --inst_sel_renew                        solver
% 3.51/0.98  --inst_lit_activity_flag                true
% 3.51/0.98  --inst_restr_to_given                   false
% 3.51/0.98  --inst_activity_threshold               500
% 3.51/0.98  --inst_out_proof                        true
% 3.51/0.98  
% 3.51/0.98  ------ Resolution Options
% 3.51/0.98  
% 3.51/0.98  --resolution_flag                       true
% 3.51/0.98  --res_lit_sel                           adaptive
% 3.51/0.98  --res_lit_sel_side                      none
% 3.51/0.98  --res_ordering                          kbo
% 3.51/0.98  --res_to_prop_solver                    active
% 3.51/0.98  --res_prop_simpl_new                    false
% 3.51/0.98  --res_prop_simpl_given                  true
% 3.51/0.98  --res_passive_queue_type                priority_queues
% 3.51/0.98  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 3.51/0.98  --res_passive_queues_freq               [15;5]
% 3.51/0.98  --res_forward_subs                      full
% 3.51/0.98  --res_backward_subs                     full
% 3.51/0.98  --res_forward_subs_resolution           true
% 3.51/0.98  --res_backward_subs_resolution          true
% 3.51/0.98  --res_orphan_elimination                true
% 3.51/0.98  --res_time_limit                        2.
% 3.51/0.98  --res_out_proof                         true
% 3.51/0.98  
% 3.51/0.98  ------ Superposition Options
% 3.51/0.98  
% 3.51/0.98  --superposition_flag                    true
% 3.51/0.98  --sup_passive_queue_type                priority_queues
% 3.51/0.98  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 3.51/0.98  --sup_passive_queues_freq               [8;1;4]
% 3.51/0.98  --demod_completeness_check              fast
% 3.51/0.98  --demod_use_ground                      true
% 3.51/0.98  --sup_to_prop_solver                    passive
% 3.51/0.98  --sup_prop_simpl_new                    true
% 3.51/0.98  --sup_prop_simpl_given                  true
% 3.51/0.98  --sup_fun_splitting                     true
% 3.51/0.98  --sup_smt_interval                      50000
% 3.51/0.98  
% 3.51/0.98  ------ Superposition Simplification Setup
% 3.51/0.98  
% 3.51/0.98  --sup_indices_passive                   [LightNormIndex;FwDemodIndex]
% 3.51/0.98  --sup_indices_active                    [SubsumptionIndex;BwDemodIndex]
% 3.51/0.98  --sup_indices_immed                     [SubsumptionIndex;FwDemodIndex;BwDemodIndex]
% 3.51/0.98  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex]
% 3.51/0.98  --sup_full_triv                         [TrivRules;PropSubs]
% 3.51/0.98  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;Joinability]
% 3.51/0.98  --sup_full_bw                           [BwDemod;BwSubsumption]
% 3.51/0.98  --sup_immed_triv                        [TrivRules]
% 3.51/0.98  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 3.51/0.98  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption]
% 3.51/0.98  --sup_immed_bw_main                     []
% 3.51/0.98  --sup_immed_bw_immed                    [BwDemod;BwSubsumption]
% 3.51/0.98  --sup_input_triv                        [Unflattening;TrivRules]
% 3.51/0.98  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption]
% 3.51/0.98  --sup_input_bw                          []
% 3.51/0.98  
% 3.51/0.98  ------ Combination Options
% 3.51/0.98  
% 3.51/0.98  --comb_res_mult                         3
% 3.51/0.98  --comb_sup_mult                         2
% 3.51/0.98  --comb_inst_mult                        10
% 3.51/0.98  
% 3.51/0.98  ------ Debug Options
% 3.51/0.98  
% 3.51/0.98  --dbg_backtrace                         false
% 3.51/0.98  --dbg_dump_prop_clauses                 false
% 3.51/0.98  --dbg_dump_prop_clauses_file            -
% 3.51/0.98  --dbg_out_stat                          false
% 3.51/0.98  ------ Parsing...
% 3.51/0.98  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 3.51/0.98  
% 3.51/0.98  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe:1:0s pe:2:0s pe:4:0s pe:8:0s pe_e  sf_s  rm: 11 0s  sf_e  pe_s  pe_e 
% 3.51/0.98  
% 3.51/0.98  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 3.51/0.98  
% 3.51/0.98  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 3.51/0.98  ------ Proving...
% 3.51/0.98  ------ Problem Properties 
% 3.51/0.98  
% 3.51/0.98  
% 3.51/0.98  clauses                                 23
% 3.51/0.98  conjectures                             2
% 3.51/0.98  EPR                                     3
% 3.51/0.98  Horn                                    17
% 3.51/0.98  unary                                   7
% 3.51/0.98  binary                                  5
% 3.51/0.98  lits                                    53
% 3.51/0.98  lits eq                                 7
% 3.51/0.98  fd_pure                                 0
% 3.51/0.98  fd_pseudo                               0
% 3.51/0.98  fd_cond                                 0
% 3.51/0.98  fd_pseudo_cond                          2
% 3.51/0.98  AC symbols                              0
% 3.51/0.98  
% 3.51/0.98  ------ Schedule dynamic 5 is on 
% 3.51/0.98  
% 3.51/0.98  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" Time Limit: 10.
% 3.51/0.98  
% 3.51/0.98  
% 3.51/0.98  ------ 
% 3.51/0.98  Current options:
% 3.51/0.98  ------ 
% 3.51/0.98  
% 3.51/0.98  ------ Input Options
% 3.51/0.98  
% 3.51/0.98  --out_options                           all
% 3.51/0.98  --tptp_safe_out                         true
% 3.51/0.98  --problem_path                          ""
% 3.51/0.98  --include_path                          ""
% 3.51/0.98  --clausifier                            res/vclausify_rel
% 3.51/0.98  --clausifier_options                    ""
% 3.51/0.98  --stdin                                 false
% 3.51/0.98  --stats_out                             all
% 3.51/0.98  
% 3.51/0.98  ------ General Options
% 3.51/0.98  
% 3.51/0.98  --fof                                   false
% 3.51/0.98  --time_out_real                         305.
% 3.51/0.98  --time_out_virtual                      -1.
% 3.51/0.98  --symbol_type_check                     false
% 3.51/0.98  --clausify_out                          false
% 3.51/0.98  --sig_cnt_out                           false
% 3.51/0.98  --trig_cnt_out                          false
% 3.51/0.98  --trig_cnt_out_tolerance                1.
% 3.51/0.98  --trig_cnt_out_sk_spl                   false
% 3.51/0.98  --abstr_cl_out                          false
% 3.51/0.98  
% 3.51/0.98  ------ Global Options
% 3.51/0.98  
% 3.51/0.98  --schedule                              default
% 3.51/0.98  --add_important_lit                     false
% 3.51/0.98  --prop_solver_per_cl                    1000
% 3.51/0.98  --min_unsat_core                        false
% 3.51/0.98  --soft_assumptions                      false
% 3.51/0.98  --soft_lemma_size                       3
% 3.51/0.98  --prop_impl_unit_size                   0
% 3.51/0.98  --prop_impl_unit                        []
% 3.51/0.98  --share_sel_clauses                     true
% 3.51/0.98  --reset_solvers                         false
% 3.51/0.98  --bc_imp_inh                            [conj_cone]
% 3.51/0.98  --conj_cone_tolerance                   3.
% 3.51/0.98  --extra_neg_conj                        none
% 3.51/0.98  --large_theory_mode                     true
% 3.51/0.98  --prolific_symb_bound                   200
% 3.51/0.98  --lt_threshold                          2000
% 3.51/0.98  --clause_weak_htbl                      true
% 3.51/0.98  --gc_record_bc_elim                     false
% 3.51/0.98  
% 3.51/0.98  ------ Preprocessing Options
% 3.51/0.98  
% 3.51/0.98  --preprocessing_flag                    true
% 3.51/0.98  --time_out_prep_mult                    0.1
% 3.51/0.98  --splitting_mode                        input
% 3.51/0.98  --splitting_grd                         true
% 3.51/0.98  --splitting_cvd                         false
% 3.51/0.98  --splitting_cvd_svl                     false
% 3.51/0.98  --splitting_nvd                         32
% 3.51/0.98  --sub_typing                            true
% 3.51/0.98  --prep_gs_sim                           true
% 3.51/0.98  --prep_unflatten                        true
% 3.51/0.98  --prep_res_sim                          true
% 3.51/0.98  --prep_upred                            true
% 3.51/0.98  --prep_sem_filter                       exhaustive
% 3.51/0.98  --prep_sem_filter_out                   false
% 3.51/0.98  --pred_elim                             true
% 3.51/0.98  --res_sim_input                         true
% 3.51/0.98  --eq_ax_congr_red                       true
% 3.51/0.98  --pure_diseq_elim                       true
% 3.51/0.98  --brand_transform                       false
% 3.51/0.98  --non_eq_to_eq                          false
% 3.51/0.98  --prep_def_merge                        true
% 3.51/0.98  --prep_def_merge_prop_impl              false
% 3.51/0.98  --prep_def_merge_mbd                    true
% 3.51/0.98  --prep_def_merge_tr_red                 false
% 3.51/0.98  --prep_def_merge_tr_cl                  false
% 3.51/0.98  --smt_preprocessing                     true
% 3.51/0.98  --smt_ac_axioms                         fast
% 3.51/0.98  --preprocessed_out                      false
% 3.51/0.98  --preprocessed_stats                    false
% 3.51/0.98  
% 3.51/0.98  ------ Abstraction refinement Options
% 3.51/0.98  
% 3.51/0.98  --abstr_ref                             []
% 3.51/0.98  --abstr_ref_prep                        false
% 3.51/0.98  --abstr_ref_until_sat                   false
% 3.51/0.98  --abstr_ref_sig_restrict                funpre
% 3.51/0.98  --abstr_ref_af_restrict_to_split_sk     false
% 3.51/0.98  --abstr_ref_under                       []
% 3.51/0.98  
% 3.51/0.98  ------ SAT Options
% 3.51/0.98  
% 3.51/0.98  --sat_mode                              false
% 3.51/0.98  --sat_fm_restart_options                ""
% 3.51/0.98  --sat_gr_def                            false
% 3.51/0.98  --sat_epr_types                         true
% 3.51/0.98  --sat_non_cyclic_types                  false
% 3.51/0.98  --sat_finite_models                     false
% 3.51/0.98  --sat_fm_lemmas                         false
% 3.51/0.98  --sat_fm_prep                           false
% 3.51/0.98  --sat_fm_uc_incr                        true
% 3.51/0.98  --sat_out_model                         small
% 3.51/0.98  --sat_out_clauses                       false
% 3.51/0.98  
% 3.51/0.98  ------ QBF Options
% 3.51/0.98  
% 3.51/0.98  --qbf_mode                              false
% 3.51/0.98  --qbf_elim_univ                         false
% 3.51/0.98  --qbf_dom_inst                          none
% 3.51/0.98  --qbf_dom_pre_inst                      false
% 3.51/0.98  --qbf_sk_in                             false
% 3.51/0.98  --qbf_pred_elim                         true
% 3.51/0.98  --qbf_split                             512
% 3.51/0.98  
% 3.51/0.98  ------ BMC1 Options
% 3.51/0.98  
% 3.51/0.98  --bmc1_incremental                      false
% 3.51/0.98  --bmc1_axioms                           reachable_all
% 3.51/0.98  --bmc1_min_bound                        0
% 3.51/0.98  --bmc1_max_bound                        -1
% 3.51/0.98  --bmc1_max_bound_default                -1
% 3.51/0.98  --bmc1_symbol_reachability              true
% 3.51/0.98  --bmc1_property_lemmas                  false
% 3.51/0.98  --bmc1_k_induction                      false
% 3.51/0.98  --bmc1_non_equiv_states                 false
% 3.51/0.98  --bmc1_deadlock                         false
% 3.51/0.98  --bmc1_ucm                              false
% 3.51/0.98  --bmc1_add_unsat_core                   none
% 3.51/0.98  --bmc1_unsat_core_children              false
% 3.51/0.98  --bmc1_unsat_core_extrapolate_axioms    false
% 3.51/0.98  --bmc1_out_stat                         full
% 3.51/0.98  --bmc1_ground_init                      false
% 3.51/0.98  --bmc1_pre_inst_next_state              false
% 3.51/0.98  --bmc1_pre_inst_state                   false
% 3.51/0.98  --bmc1_pre_inst_reach_state             false
% 3.51/0.98  --bmc1_out_unsat_core                   false
% 3.51/0.98  --bmc1_aig_witness_out                  false
% 3.51/0.98  --bmc1_verbose                          false
% 3.51/0.98  --bmc1_dump_clauses_tptp                false
% 3.51/0.98  --bmc1_dump_unsat_core_tptp             false
% 3.51/0.98  --bmc1_dump_file                        -
% 3.51/0.98  --bmc1_ucm_expand_uc_limit              128
% 3.51/0.98  --bmc1_ucm_n_expand_iterations          6
% 3.51/0.98  --bmc1_ucm_extend_mode                  1
% 3.51/0.98  --bmc1_ucm_init_mode                    2
% 3.51/0.98  --bmc1_ucm_cone_mode                    none
% 3.51/0.98  --bmc1_ucm_reduced_relation_type        0
% 3.51/0.98  --bmc1_ucm_relax_model                  4
% 3.51/0.98  --bmc1_ucm_full_tr_after_sat            true
% 3.51/0.98  --bmc1_ucm_expand_neg_assumptions       false
% 3.51/0.98  --bmc1_ucm_layered_model                none
% 3.51/0.98  --bmc1_ucm_max_lemma_size               10
% 3.51/0.98  
% 3.51/0.98  ------ AIG Options
% 3.51/0.98  
% 3.51/0.98  --aig_mode                              false
% 3.51/0.98  
% 3.51/0.98  ------ Instantiation Options
% 3.51/0.98  
% 3.51/0.98  --instantiation_flag                    true
% 3.51/0.98  --inst_sos_flag                         true
% 3.51/0.98  --inst_sos_phase                        true
% 3.51/0.98  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 3.51/0.98  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 3.51/0.98  --inst_lit_sel_side                     none
% 3.51/0.98  --inst_solver_per_active                1400
% 3.51/0.98  --inst_solver_calls_frac                1.
% 3.51/0.98  --inst_passive_queue_type               priority_queues
% 3.51/0.98  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 3.51/0.98  --inst_passive_queues_freq              [25;2]
% 3.51/0.98  --inst_dismatching                      true
% 3.51/0.98  --inst_eager_unprocessed_to_passive     true
% 3.51/0.98  --inst_prop_sim_given                   true
% 3.51/0.98  --inst_prop_sim_new                     false
% 3.51/0.98  --inst_subs_new                         false
% 3.51/0.98  --inst_eq_res_simp                      false
% 3.51/0.98  --inst_subs_given                       false
% 3.51/0.98  --inst_orphan_elimination               true
% 3.51/0.98  --inst_learning_loop_flag               true
% 3.51/0.98  --inst_learning_start                   3000
% 3.51/0.98  --inst_learning_factor                  2
% 3.51/0.98  --inst_start_prop_sim_after_learn       3
% 3.51/0.98  --inst_sel_renew                        solver
% 3.51/0.98  --inst_lit_activity_flag                true
% 3.51/0.98  --inst_restr_to_given                   false
% 3.51/0.98  --inst_activity_threshold               500
% 3.51/0.98  --inst_out_proof                        true
% 3.51/0.98  
% 3.51/0.98  ------ Resolution Options
% 3.51/0.98  
% 3.51/0.98  --resolution_flag                       false
% 3.51/0.98  --res_lit_sel                           adaptive
% 3.51/0.98  --res_lit_sel_side                      none
% 3.51/0.98  --res_ordering                          kbo
% 3.51/0.98  --res_to_prop_solver                    active
% 3.51/0.98  --res_prop_simpl_new                    false
% 3.51/0.98  --res_prop_simpl_given                  true
% 3.51/0.98  --res_passive_queue_type                priority_queues
% 3.51/0.98  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 3.51/0.98  --res_passive_queues_freq               [15;5]
% 3.51/0.98  --res_forward_subs                      full
% 3.51/0.98  --res_backward_subs                     full
% 3.51/0.98  --res_forward_subs_resolution           true
% 3.51/0.98  --res_backward_subs_resolution          true
% 3.51/0.98  --res_orphan_elimination                true
% 3.51/0.98  --res_time_limit                        2.
% 3.51/0.98  --res_out_proof                         true
% 3.51/0.98  
% 3.51/0.98  ------ Superposition Options
% 3.51/0.98  
% 3.51/0.98  --superposition_flag                    true
% 3.51/0.98  --sup_passive_queue_type                priority_queues
% 3.51/0.98  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 3.51/0.98  --sup_passive_queues_freq               [8;1;4]
% 3.51/0.98  --demod_completeness_check              fast
% 3.51/0.98  --demod_use_ground                      true
% 3.51/0.98  --sup_to_prop_solver                    passive
% 3.51/0.98  --sup_prop_simpl_new                    true
% 3.51/0.98  --sup_prop_simpl_given                  true
% 3.51/0.98  --sup_fun_splitting                     true
% 3.51/0.98  --sup_smt_interval                      50000
% 3.51/0.98  
% 3.51/0.98  ------ Superposition Simplification Setup
% 3.51/0.98  
% 3.51/0.98  --sup_indices_passive                   [LightNormIndex;FwDemodIndex]
% 3.51/0.98  --sup_indices_active                    [SubsumptionIndex;BwDemodIndex]
% 3.51/0.98  --sup_indices_immed                     [SubsumptionIndex;FwDemodIndex;BwDemodIndex]
% 3.51/0.98  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex]
% 3.51/0.98  --sup_full_triv                         [TrivRules;PropSubs]
% 3.51/0.98  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;Joinability]
% 3.51/0.98  --sup_full_bw                           [BwDemod;BwSubsumption]
% 3.51/0.98  --sup_immed_triv                        [TrivRules]
% 3.51/0.98  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 3.51/0.98  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption]
% 3.51/0.98  --sup_immed_bw_main                     []
% 3.51/0.98  --sup_immed_bw_immed                    [BwDemod;BwSubsumption]
% 3.51/0.98  --sup_input_triv                        [Unflattening;TrivRules]
% 3.51/0.98  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption]
% 3.51/0.98  --sup_input_bw                          []
% 3.51/0.98  
% 3.51/0.98  ------ Combination Options
% 3.51/0.98  
% 3.51/0.98  --comb_res_mult                         3
% 3.51/0.98  --comb_sup_mult                         2
% 3.51/0.98  --comb_inst_mult                        10
% 3.51/0.98  
% 3.51/0.98  ------ Debug Options
% 3.51/0.98  
% 3.51/0.98  --dbg_backtrace                         false
% 3.51/0.98  --dbg_dump_prop_clauses                 false
% 3.51/0.98  --dbg_dump_prop_clauses_file            -
% 3.51/0.98  --dbg_out_stat                          false
% 3.51/0.98  
% 3.51/0.98  
% 3.51/0.98  
% 3.51/0.98  
% 3.51/0.98  ------ Proving...
% 3.51/0.98  
% 3.51/0.98  
% 3.51/0.98  % SZS status Theorem for theBenchmark.p
% 3.51/0.98  
% 3.51/0.98  % SZS output start CNFRefutation for theBenchmark.p
% 3.51/0.98  
% 3.51/0.98  fof(f5,axiom,(
% 3.51/0.98    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => ! [X2] : (r2_hidden(X2,X1) => r2_hidden(X2,X0)))),
% 3.51/0.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.51/0.98  
% 3.51/0.98  fof(f21,plain,(
% 3.51/0.98    ! [X0,X1] : (! [X2] : (r2_hidden(X2,X0) | ~r2_hidden(X2,X1)) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 3.51/0.98    inference(ennf_transformation,[],[f5])).
% 3.51/0.98  
% 3.51/0.98  fof(f59,plain,(
% 3.51/0.98    ( ! [X2,X0,X1] : (r2_hidden(X2,X0) | ~r2_hidden(X2,X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 3.51/0.98    inference(cnf_transformation,[],[f21])).
% 3.51/0.98  
% 3.51/0.98  fof(f1,axiom,(
% 3.51/0.98    ! [X0,X1] : (! [X2] : (r2_hidden(X2,X0) <=> r2_hidden(X2,X1)) => X0 = X1)),
% 3.51/0.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.51/0.98  
% 3.51/0.98  fof(f20,plain,(
% 3.51/0.98    ! [X0,X1] : (X0 = X1 | ? [X2] : (r2_hidden(X2,X0) <~> r2_hidden(X2,X1)))),
% 3.51/0.98    inference(ennf_transformation,[],[f1])).
% 3.51/0.98  
% 3.51/0.98  fof(f40,plain,(
% 3.51/0.98    ! [X0,X1] : (X0 = X1 | ? [X2] : ((~r2_hidden(X2,X1) | ~r2_hidden(X2,X0)) & (r2_hidden(X2,X1) | r2_hidden(X2,X0))))),
% 3.51/0.98    inference(nnf_transformation,[],[f20])).
% 3.51/0.98  
% 3.51/0.98  fof(f41,plain,(
% 3.51/0.98    ! [X1,X0] : (? [X2] : ((~r2_hidden(X2,X1) | ~r2_hidden(X2,X0)) & (r2_hidden(X2,X1) | r2_hidden(X2,X0))) => ((~r2_hidden(sK0(X0,X1),X1) | ~r2_hidden(sK0(X0,X1),X0)) & (r2_hidden(sK0(X0,X1),X1) | r2_hidden(sK0(X0,X1),X0))))),
% 3.51/0.98    introduced(choice_axiom,[])).
% 3.51/0.98  
% 3.51/0.98  fof(f42,plain,(
% 3.51/0.98    ! [X0,X1] : (X0 = X1 | ((~r2_hidden(sK0(X0,X1),X1) | ~r2_hidden(sK0(X0,X1),X0)) & (r2_hidden(sK0(X0,X1),X1) | r2_hidden(sK0(X0,X1),X0))))),
% 3.51/0.98    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f40,f41])).
% 3.51/0.98  
% 3.51/0.98  fof(f54,plain,(
% 3.51/0.98    ( ! [X0,X1] : (X0 = X1 | r2_hidden(sK0(X0,X1),X1) | r2_hidden(sK0(X0,X1),X0)) )),
% 3.51/0.98    inference(cnf_transformation,[],[f42])).
% 3.51/0.98  
% 3.51/0.98  fof(f6,axiom,(
% 3.51/0.98    ! [X0,X1] : (r2_hidden(X0,X1) => m1_subset_1(X0,X1))),
% 3.51/0.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.51/0.98  
% 3.51/0.98  fof(f22,plain,(
% 3.51/0.98    ! [X0,X1] : (m1_subset_1(X0,X1) | ~r2_hidden(X0,X1))),
% 3.51/0.98    inference(ennf_transformation,[],[f6])).
% 3.51/0.98  
% 3.51/0.98  fof(f60,plain,(
% 3.51/0.98    ( ! [X0,X1] : (m1_subset_1(X0,X1) | ~r2_hidden(X0,X1)) )),
% 3.51/0.98    inference(cnf_transformation,[],[f22])).
% 3.51/0.98  
% 3.51/0.98  fof(f14,axiom,(
% 3.51/0.98    ! [X0] : ((l1_orders_2(X0) & v5_orders_2(X0) & v4_orders_2(X0) & v3_orders_2(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,u1_struct_0(X0)) => (k1_yellow_0(X0,k5_waybel_0(X0,X1)) = X1 & r1_yellow_0(X0,k5_waybel_0(X0,X1)))))),
% 3.51/0.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.51/0.98  
% 3.51/0.98  fof(f35,plain,(
% 3.51/0.98    ! [X0] : (! [X1] : ((k1_yellow_0(X0,k5_waybel_0(X0,X1)) = X1 & r1_yellow_0(X0,k5_waybel_0(X0,X1))) | ~m1_subset_1(X1,u1_struct_0(X0))) | (~l1_orders_2(X0) | ~v5_orders_2(X0) | ~v4_orders_2(X0) | ~v3_orders_2(X0) | v2_struct_0(X0)))),
% 3.51/0.98    inference(ennf_transformation,[],[f14])).
% 3.51/0.98  
% 3.51/0.98  fof(f36,plain,(
% 3.51/0.98    ! [X0] : (! [X1] : ((k1_yellow_0(X0,k5_waybel_0(X0,X1)) = X1 & r1_yellow_0(X0,k5_waybel_0(X0,X1))) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~l1_orders_2(X0) | ~v5_orders_2(X0) | ~v4_orders_2(X0) | ~v3_orders_2(X0) | v2_struct_0(X0))),
% 3.51/0.98    inference(flattening,[],[f35])).
% 3.51/0.98  
% 3.51/0.98  fof(f74,plain,(
% 3.51/0.98    ( ! [X0,X1] : (k1_yellow_0(X0,k5_waybel_0(X0,X1)) = X1 | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_orders_2(X0) | ~v5_orders_2(X0) | ~v4_orders_2(X0) | ~v3_orders_2(X0) | v2_struct_0(X0)) )),
% 3.51/0.98    inference(cnf_transformation,[],[f36])).
% 3.51/0.98  
% 3.51/0.98  fof(f16,conjecture,(
% 3.51/0.98    ! [X0] : ((l1_orders_2(X0) & v1_yellow_0(X0) & v5_orders_2(X0) & v4_orders_2(X0) & v3_orders_2(X0) & ~v2_struct_0(X0)) => ! [X1] : ((m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & v13_waybel_0(X1,X0) & v2_waybel_0(X1,X0) & ~v1_xboole_0(X1)) => (v1_subset_1(X1,u1_struct_0(X0)) <=> ~r2_hidden(k3_yellow_0(X0),X1))))),
% 3.51/0.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.51/0.98  
% 3.51/0.98  fof(f17,negated_conjecture,(
% 3.51/0.98    ~! [X0] : ((l1_orders_2(X0) & v1_yellow_0(X0) & v5_orders_2(X0) & v4_orders_2(X0) & v3_orders_2(X0) & ~v2_struct_0(X0)) => ! [X1] : ((m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & v13_waybel_0(X1,X0) & v2_waybel_0(X1,X0) & ~v1_xboole_0(X1)) => (v1_subset_1(X1,u1_struct_0(X0)) <=> ~r2_hidden(k3_yellow_0(X0),X1))))),
% 3.51/0.98    inference(negated_conjecture,[],[f16])).
% 3.51/0.98  
% 3.51/0.98  fof(f18,plain,(
% 3.51/0.98    ~! [X0] : ((l1_orders_2(X0) & v1_yellow_0(X0) & v5_orders_2(X0) & v4_orders_2(X0) & v3_orders_2(X0) & ~v2_struct_0(X0)) => ! [X1] : ((m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & v13_waybel_0(X1,X0) & ~v1_xboole_0(X1)) => (v1_subset_1(X1,u1_struct_0(X0)) <=> ~r2_hidden(k3_yellow_0(X0),X1))))),
% 3.51/0.98    inference(pure_predicate_removal,[],[f17])).
% 3.51/0.98  
% 3.51/0.98  fof(f38,plain,(
% 3.51/0.98    ? [X0] : (? [X1] : ((v1_subset_1(X1,u1_struct_0(X0)) <~> ~r2_hidden(k3_yellow_0(X0),X1)) & (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & v13_waybel_0(X1,X0) & ~v1_xboole_0(X1))) & (l1_orders_2(X0) & v1_yellow_0(X0) & v5_orders_2(X0) & v4_orders_2(X0) & v3_orders_2(X0) & ~v2_struct_0(X0)))),
% 3.51/0.98    inference(ennf_transformation,[],[f18])).
% 3.51/0.98  
% 3.51/0.98  fof(f39,plain,(
% 3.51/0.98    ? [X0] : (? [X1] : ((v1_subset_1(X1,u1_struct_0(X0)) <~> ~r2_hidden(k3_yellow_0(X0),X1)) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & v13_waybel_0(X1,X0) & ~v1_xboole_0(X1)) & l1_orders_2(X0) & v1_yellow_0(X0) & v5_orders_2(X0) & v4_orders_2(X0) & v3_orders_2(X0) & ~v2_struct_0(X0))),
% 3.51/0.98    inference(flattening,[],[f38])).
% 3.51/0.98  
% 3.51/0.98  fof(f49,plain,(
% 3.51/0.98    ? [X0] : (? [X1] : (((r2_hidden(k3_yellow_0(X0),X1) | ~v1_subset_1(X1,u1_struct_0(X0))) & (~r2_hidden(k3_yellow_0(X0),X1) | v1_subset_1(X1,u1_struct_0(X0)))) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & v13_waybel_0(X1,X0) & ~v1_xboole_0(X1)) & l1_orders_2(X0) & v1_yellow_0(X0) & v5_orders_2(X0) & v4_orders_2(X0) & v3_orders_2(X0) & ~v2_struct_0(X0))),
% 3.51/0.98    inference(nnf_transformation,[],[f39])).
% 3.51/0.98  
% 3.51/0.98  fof(f50,plain,(
% 3.51/0.98    ? [X0] : (? [X1] : ((r2_hidden(k3_yellow_0(X0),X1) | ~v1_subset_1(X1,u1_struct_0(X0))) & (~r2_hidden(k3_yellow_0(X0),X1) | v1_subset_1(X1,u1_struct_0(X0))) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & v13_waybel_0(X1,X0) & ~v1_xboole_0(X1)) & l1_orders_2(X0) & v1_yellow_0(X0) & v5_orders_2(X0) & v4_orders_2(X0) & v3_orders_2(X0) & ~v2_struct_0(X0))),
% 3.51/0.98    inference(flattening,[],[f49])).
% 3.51/0.98  
% 3.51/0.98  fof(f52,plain,(
% 3.51/0.98    ( ! [X0] : (? [X1] : ((r2_hidden(k3_yellow_0(X0),X1) | ~v1_subset_1(X1,u1_struct_0(X0))) & (~r2_hidden(k3_yellow_0(X0),X1) | v1_subset_1(X1,u1_struct_0(X0))) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & v13_waybel_0(X1,X0) & ~v1_xboole_0(X1)) => ((r2_hidden(k3_yellow_0(X0),sK4) | ~v1_subset_1(sK4,u1_struct_0(X0))) & (~r2_hidden(k3_yellow_0(X0),sK4) | v1_subset_1(sK4,u1_struct_0(X0))) & m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(X0))) & v13_waybel_0(sK4,X0) & ~v1_xboole_0(sK4))) )),
% 3.51/0.98    introduced(choice_axiom,[])).
% 3.51/0.98  
% 3.51/0.98  fof(f51,plain,(
% 3.51/0.98    ? [X0] : (? [X1] : ((r2_hidden(k3_yellow_0(X0),X1) | ~v1_subset_1(X1,u1_struct_0(X0))) & (~r2_hidden(k3_yellow_0(X0),X1) | v1_subset_1(X1,u1_struct_0(X0))) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & v13_waybel_0(X1,X0) & ~v1_xboole_0(X1)) & l1_orders_2(X0) & v1_yellow_0(X0) & v5_orders_2(X0) & v4_orders_2(X0) & v3_orders_2(X0) & ~v2_struct_0(X0)) => (? [X1] : ((r2_hidden(k3_yellow_0(sK3),X1) | ~v1_subset_1(X1,u1_struct_0(sK3))) & (~r2_hidden(k3_yellow_0(sK3),X1) | v1_subset_1(X1,u1_struct_0(sK3))) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK3))) & v13_waybel_0(X1,sK3) & ~v1_xboole_0(X1)) & l1_orders_2(sK3) & v1_yellow_0(sK3) & v5_orders_2(sK3) & v4_orders_2(sK3) & v3_orders_2(sK3) & ~v2_struct_0(sK3))),
% 3.51/0.98    introduced(choice_axiom,[])).
% 3.51/0.98  
% 3.51/0.98  fof(f53,plain,(
% 3.51/0.98    ((r2_hidden(k3_yellow_0(sK3),sK4) | ~v1_subset_1(sK4,u1_struct_0(sK3))) & (~r2_hidden(k3_yellow_0(sK3),sK4) | v1_subset_1(sK4,u1_struct_0(sK3))) & m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(sK3))) & v13_waybel_0(sK4,sK3) & ~v1_xboole_0(sK4)) & l1_orders_2(sK3) & v1_yellow_0(sK3) & v5_orders_2(sK3) & v4_orders_2(sK3) & v3_orders_2(sK3) & ~v2_struct_0(sK3)),
% 3.51/0.98    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3,sK4])],[f50,f52,f51])).
% 3.51/0.98  
% 3.51/0.98  fof(f80,plain,(
% 3.51/0.98    v5_orders_2(sK3)),
% 3.51/0.98    inference(cnf_transformation,[],[f53])).
% 3.51/0.98  
% 3.51/0.98  fof(f77,plain,(
% 3.51/0.98    ~v2_struct_0(sK3)),
% 3.51/0.98    inference(cnf_transformation,[],[f53])).
% 3.51/0.98  
% 3.51/0.98  fof(f78,plain,(
% 3.51/0.98    v3_orders_2(sK3)),
% 3.51/0.98    inference(cnf_transformation,[],[f53])).
% 3.51/0.98  
% 3.51/0.98  fof(f79,plain,(
% 3.51/0.98    v4_orders_2(sK3)),
% 3.51/0.98    inference(cnf_transformation,[],[f53])).
% 3.51/0.98  
% 3.51/0.98  fof(f82,plain,(
% 3.51/0.98    l1_orders_2(sK3)),
% 3.51/0.98    inference(cnf_transformation,[],[f53])).
% 3.51/0.98  
% 3.51/0.98  fof(f85,plain,(
% 3.51/0.98    m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(sK3)))),
% 3.51/0.98    inference(cnf_transformation,[],[f53])).
% 3.51/0.98  
% 3.51/0.98  fof(f8,axiom,(
% 3.51/0.98    ! [X0,X1,X2] : ((m1_subset_1(X1,k1_zfmisc_1(X2)) & r2_hidden(X0,X1)) => m1_subset_1(X0,X2))),
% 3.51/0.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.51/0.98  
% 3.51/0.98  fof(f25,plain,(
% 3.51/0.98    ! [X0,X1,X2] : (m1_subset_1(X0,X2) | (~m1_subset_1(X1,k1_zfmisc_1(X2)) | ~r2_hidden(X0,X1)))),
% 3.51/0.98    inference(ennf_transformation,[],[f8])).
% 3.51/0.98  
% 3.51/0.98  fof(f26,plain,(
% 3.51/0.98    ! [X0,X1,X2] : (m1_subset_1(X0,X2) | ~m1_subset_1(X1,k1_zfmisc_1(X2)) | ~r2_hidden(X0,X1))),
% 3.51/0.98    inference(flattening,[],[f25])).
% 3.51/0.98  
% 3.51/0.98  fof(f62,plain,(
% 3.51/0.98    ( ! [X2,X0,X1] : (m1_subset_1(X0,X2) | ~m1_subset_1(X1,k1_zfmisc_1(X2)) | ~r2_hidden(X0,X1)) )),
% 3.51/0.98    inference(cnf_transformation,[],[f26])).
% 3.51/0.98  
% 3.51/0.98  fof(f73,plain,(
% 3.51/0.98    ( ! [X0,X1] : (r1_yellow_0(X0,k5_waybel_0(X0,X1)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_orders_2(X0) | ~v5_orders_2(X0) | ~v4_orders_2(X0) | ~v3_orders_2(X0) | v2_struct_0(X0)) )),
% 3.51/0.98    inference(cnf_transformation,[],[f36])).
% 3.51/0.98  
% 3.51/0.98  fof(f2,axiom,(
% 3.51/0.98    ! [X0] : r1_tarski(k1_xboole_0,X0)),
% 3.51/0.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.51/0.98  
% 3.51/0.98  fof(f56,plain,(
% 3.51/0.98    ( ! [X0] : (r1_tarski(k1_xboole_0,X0)) )),
% 3.51/0.98    inference(cnf_transformation,[],[f2])).
% 3.51/0.98  
% 3.51/0.98  fof(f11,axiom,(
% 3.51/0.98    ! [X0] : (l1_orders_2(X0) => ! [X1,X2] : ((r1_yellow_0(X0,X2) & r1_yellow_0(X0,X1) & r1_tarski(X1,X2)) => r1_orders_2(X0,k1_yellow_0(X0,X1),k1_yellow_0(X0,X2))))),
% 3.51/0.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.51/0.98  
% 3.51/0.98  fof(f29,plain,(
% 3.51/0.98    ! [X0] : (! [X1,X2] : (r1_orders_2(X0,k1_yellow_0(X0,X1),k1_yellow_0(X0,X2)) | (~r1_yellow_0(X0,X2) | ~r1_yellow_0(X0,X1) | ~r1_tarski(X1,X2))) | ~l1_orders_2(X0))),
% 3.51/0.98    inference(ennf_transformation,[],[f11])).
% 3.51/0.98  
% 3.51/0.98  fof(f30,plain,(
% 3.51/0.98    ! [X0] : (! [X1,X2] : (r1_orders_2(X0,k1_yellow_0(X0,X1),k1_yellow_0(X0,X2)) | ~r1_yellow_0(X0,X2) | ~r1_yellow_0(X0,X1) | ~r1_tarski(X1,X2)) | ~l1_orders_2(X0))),
% 3.51/0.98    inference(flattening,[],[f29])).
% 3.51/0.98  
% 3.51/0.98  fof(f65,plain,(
% 3.51/0.98    ( ! [X2,X0,X1] : (r1_orders_2(X0,k1_yellow_0(X0,X1),k1_yellow_0(X0,X2)) | ~r1_yellow_0(X0,X2) | ~r1_yellow_0(X0,X1) | ~r1_tarski(X1,X2) | ~l1_orders_2(X0)) )),
% 3.51/0.98    inference(cnf_transformation,[],[f30])).
% 3.51/0.98  
% 3.51/0.98  fof(f81,plain,(
% 3.51/0.98    v1_yellow_0(sK3)),
% 3.51/0.98    inference(cnf_transformation,[],[f53])).
% 3.51/0.98  
% 3.51/0.98  fof(f12,axiom,(
% 3.51/0.98    ! [X0] : ((l1_orders_2(X0) & v1_yellow_0(X0) & v5_orders_2(X0) & ~v2_struct_0(X0)) => (r2_yellow_0(X0,u1_struct_0(X0)) & r1_yellow_0(X0,k1_xboole_0)))),
% 3.51/0.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.51/0.98  
% 3.51/0.98  fof(f19,plain,(
% 3.51/0.98    ! [X0] : ((l1_orders_2(X0) & v1_yellow_0(X0) & v5_orders_2(X0) & ~v2_struct_0(X0)) => r1_yellow_0(X0,k1_xboole_0))),
% 3.51/0.98    inference(pure_predicate_removal,[],[f12])).
% 3.51/0.98  
% 3.51/0.98  fof(f31,plain,(
% 3.51/0.98    ! [X0] : (r1_yellow_0(X0,k1_xboole_0) | (~l1_orders_2(X0) | ~v1_yellow_0(X0) | ~v5_orders_2(X0) | v2_struct_0(X0)))),
% 3.51/0.98    inference(ennf_transformation,[],[f19])).
% 3.51/0.98  
% 3.51/0.98  fof(f32,plain,(
% 3.51/0.98    ! [X0] : (r1_yellow_0(X0,k1_xboole_0) | ~l1_orders_2(X0) | ~v1_yellow_0(X0) | ~v5_orders_2(X0) | v2_struct_0(X0))),
% 3.51/0.98    inference(flattening,[],[f31])).
% 3.51/0.98  
% 3.51/0.98  fof(f66,plain,(
% 3.51/0.98    ( ! [X0] : (r1_yellow_0(X0,k1_xboole_0) | ~l1_orders_2(X0) | ~v1_yellow_0(X0) | ~v5_orders_2(X0) | v2_struct_0(X0)) )),
% 3.51/0.98    inference(cnf_transformation,[],[f32])).
% 3.51/0.98  
% 3.51/0.98  fof(f9,axiom,(
% 3.51/0.98    ! [X0] : (l1_orders_2(X0) => k3_yellow_0(X0) = k1_yellow_0(X0,k1_xboole_0))),
% 3.51/0.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.51/0.98  
% 3.51/0.98  fof(f27,plain,(
% 3.51/0.98    ! [X0] : (k3_yellow_0(X0) = k1_yellow_0(X0,k1_xboole_0) | ~l1_orders_2(X0))),
% 3.51/0.98    inference(ennf_transformation,[],[f9])).
% 3.51/0.98  
% 3.51/0.98  fof(f63,plain,(
% 3.51/0.98    ( ! [X0] : (k3_yellow_0(X0) = k1_yellow_0(X0,k1_xboole_0) | ~l1_orders_2(X0)) )),
% 3.51/0.98    inference(cnf_transformation,[],[f27])).
% 3.51/0.98  
% 3.51/0.98  fof(f10,axiom,(
% 3.51/0.98    ! [X0] : (l1_orders_2(X0) => m1_subset_1(k3_yellow_0(X0),u1_struct_0(X0)))),
% 3.51/0.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.51/0.98  
% 3.51/0.98  fof(f28,plain,(
% 3.51/0.98    ! [X0] : (m1_subset_1(k3_yellow_0(X0),u1_struct_0(X0)) | ~l1_orders_2(X0))),
% 3.51/0.98    inference(ennf_transformation,[],[f10])).
% 3.51/0.98  
% 3.51/0.98  fof(f64,plain,(
% 3.51/0.98    ( ! [X0] : (m1_subset_1(k3_yellow_0(X0),u1_struct_0(X0)) | ~l1_orders_2(X0)) )),
% 3.51/0.98    inference(cnf_transformation,[],[f28])).
% 3.51/0.98  
% 3.51/0.98  fof(f15,axiom,(
% 3.51/0.98    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => (v1_subset_1(X1,X0) <=> X0 != X1))),
% 3.51/0.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.51/0.98  
% 3.51/0.98  fof(f37,plain,(
% 3.51/0.98    ! [X0,X1] : ((v1_subset_1(X1,X0) <=> X0 != X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 3.51/0.98    inference(ennf_transformation,[],[f15])).
% 3.51/0.98  
% 3.51/0.98  fof(f48,plain,(
% 3.51/0.98    ! [X0,X1] : (((v1_subset_1(X1,X0) | X0 = X1) & (X0 != X1 | ~v1_subset_1(X1,X0))) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 3.51/0.98    inference(nnf_transformation,[],[f37])).
% 3.51/0.98  
% 3.51/0.98  fof(f75,plain,(
% 3.51/0.98    ( ! [X0,X1] : (X0 != X1 | ~v1_subset_1(X1,X0) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 3.51/0.98    inference(cnf_transformation,[],[f48])).
% 3.51/0.98  
% 3.51/0.98  fof(f88,plain,(
% 3.51/0.98    ( ! [X1] : (~v1_subset_1(X1,X1) | ~m1_subset_1(X1,k1_zfmisc_1(X1))) )),
% 3.51/0.98    inference(equality_resolution,[],[f75])).
% 3.51/0.98  
% 3.51/0.98  fof(f86,plain,(
% 3.51/0.98    ~r2_hidden(k3_yellow_0(sK3),sK4) | v1_subset_1(sK4,u1_struct_0(sK3))),
% 3.51/0.98    inference(cnf_transformation,[],[f53])).
% 3.51/0.98  
% 3.51/0.98  fof(f7,axiom,(
% 3.51/0.98    ! [X0,X1] : (m1_subset_1(X0,X1) => (r2_hidden(X0,X1) | v1_xboole_0(X1)))),
% 3.51/0.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.51/0.98  
% 3.51/0.98  fof(f23,plain,(
% 3.51/0.98    ! [X0,X1] : ((r2_hidden(X0,X1) | v1_xboole_0(X1)) | ~m1_subset_1(X0,X1))),
% 3.51/0.98    inference(ennf_transformation,[],[f7])).
% 3.51/0.98  
% 3.51/0.98  fof(f24,plain,(
% 3.51/0.98    ! [X0,X1] : (r2_hidden(X0,X1) | v1_xboole_0(X1) | ~m1_subset_1(X0,X1))),
% 3.51/0.98    inference(flattening,[],[f23])).
% 3.51/0.98  
% 3.51/0.98  fof(f61,plain,(
% 3.51/0.98    ( ! [X0,X1] : (r2_hidden(X0,X1) | v1_xboole_0(X1) | ~m1_subset_1(X0,X1)) )),
% 3.51/0.98    inference(cnf_transformation,[],[f24])).
% 3.51/0.98  
% 3.51/0.98  fof(f83,plain,(
% 3.51/0.98    ~v1_xboole_0(sK4)),
% 3.51/0.98    inference(cnf_transformation,[],[f53])).
% 3.51/0.98  
% 3.51/0.98  fof(f13,axiom,(
% 3.51/0.98    ! [X0] : (l1_orders_2(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => (v13_waybel_0(X1,X0) <=> ! [X2] : (m1_subset_1(X2,u1_struct_0(X0)) => ! [X3] : (m1_subset_1(X3,u1_struct_0(X0)) => ((r1_orders_2(X0,X2,X3) & r2_hidden(X2,X1)) => r2_hidden(X3,X1)))))))),
% 3.51/0.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.51/0.98  
% 3.51/0.98  fof(f33,plain,(
% 3.51/0.98    ! [X0] : (! [X1] : ((v13_waybel_0(X1,X0) <=> ! [X2] : (! [X3] : ((r2_hidden(X3,X1) | (~r1_orders_2(X0,X2,X3) | ~r2_hidden(X2,X1))) | ~m1_subset_1(X3,u1_struct_0(X0))) | ~m1_subset_1(X2,u1_struct_0(X0)))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_orders_2(X0))),
% 3.51/0.98    inference(ennf_transformation,[],[f13])).
% 3.51/0.98  
% 3.51/0.98  fof(f34,plain,(
% 3.51/0.98    ! [X0] : (! [X1] : ((v13_waybel_0(X1,X0) <=> ! [X2] : (! [X3] : (r2_hidden(X3,X1) | ~r1_orders_2(X0,X2,X3) | ~r2_hidden(X2,X1) | ~m1_subset_1(X3,u1_struct_0(X0))) | ~m1_subset_1(X2,u1_struct_0(X0)))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_orders_2(X0))),
% 3.51/0.98    inference(flattening,[],[f33])).
% 3.51/0.98  
% 3.51/0.98  fof(f43,plain,(
% 3.51/0.98    ! [X0] : (! [X1] : (((v13_waybel_0(X1,X0) | ? [X2] : (? [X3] : (~r2_hidden(X3,X1) & r1_orders_2(X0,X2,X3) & r2_hidden(X2,X1) & m1_subset_1(X3,u1_struct_0(X0))) & m1_subset_1(X2,u1_struct_0(X0)))) & (! [X2] : (! [X3] : (r2_hidden(X3,X1) | ~r1_orders_2(X0,X2,X3) | ~r2_hidden(X2,X1) | ~m1_subset_1(X3,u1_struct_0(X0))) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~v13_waybel_0(X1,X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_orders_2(X0))),
% 3.51/0.98    inference(nnf_transformation,[],[f34])).
% 3.51/0.98  
% 3.51/0.98  fof(f44,plain,(
% 3.51/0.98    ! [X0] : (! [X1] : (((v13_waybel_0(X1,X0) | ? [X2] : (? [X3] : (~r2_hidden(X3,X1) & r1_orders_2(X0,X2,X3) & r2_hidden(X2,X1) & m1_subset_1(X3,u1_struct_0(X0))) & m1_subset_1(X2,u1_struct_0(X0)))) & (! [X4] : (! [X5] : (r2_hidden(X5,X1) | ~r1_orders_2(X0,X4,X5) | ~r2_hidden(X4,X1) | ~m1_subset_1(X5,u1_struct_0(X0))) | ~m1_subset_1(X4,u1_struct_0(X0))) | ~v13_waybel_0(X1,X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_orders_2(X0))),
% 3.51/0.98    inference(rectify,[],[f43])).
% 3.51/0.98  
% 3.51/0.98  fof(f46,plain,(
% 3.51/0.98    ( ! [X2] : (! [X1,X0] : (? [X3] : (~r2_hidden(X3,X1) & r1_orders_2(X0,X2,X3) & r2_hidden(X2,X1) & m1_subset_1(X3,u1_struct_0(X0))) => (~r2_hidden(sK2(X0,X1),X1) & r1_orders_2(X0,X2,sK2(X0,X1)) & r2_hidden(X2,X1) & m1_subset_1(sK2(X0,X1),u1_struct_0(X0))))) )),
% 3.51/0.98    introduced(choice_axiom,[])).
% 3.51/0.98  
% 3.51/0.98  fof(f45,plain,(
% 3.51/0.98    ! [X1,X0] : (? [X2] : (? [X3] : (~r2_hidden(X3,X1) & r1_orders_2(X0,X2,X3) & r2_hidden(X2,X1) & m1_subset_1(X3,u1_struct_0(X0))) & m1_subset_1(X2,u1_struct_0(X0))) => (? [X3] : (~r2_hidden(X3,X1) & r1_orders_2(X0,sK1(X0,X1),X3) & r2_hidden(sK1(X0,X1),X1) & m1_subset_1(X3,u1_struct_0(X0))) & m1_subset_1(sK1(X0,X1),u1_struct_0(X0))))),
% 3.51/0.98    introduced(choice_axiom,[])).
% 3.51/0.98  
% 3.51/0.98  fof(f47,plain,(
% 3.51/0.98    ! [X0] : (! [X1] : (((v13_waybel_0(X1,X0) | ((~r2_hidden(sK2(X0,X1),X1) & r1_orders_2(X0,sK1(X0,X1),sK2(X0,X1)) & r2_hidden(sK1(X0,X1),X1) & m1_subset_1(sK2(X0,X1),u1_struct_0(X0))) & m1_subset_1(sK1(X0,X1),u1_struct_0(X0)))) & (! [X4] : (! [X5] : (r2_hidden(X5,X1) | ~r1_orders_2(X0,X4,X5) | ~r2_hidden(X4,X1) | ~m1_subset_1(X5,u1_struct_0(X0))) | ~m1_subset_1(X4,u1_struct_0(X0))) | ~v13_waybel_0(X1,X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_orders_2(X0))),
% 3.51/0.98    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1,sK2])],[f44,f46,f45])).
% 3.51/0.98  
% 3.51/0.98  fof(f67,plain,(
% 3.51/0.98    ( ! [X4,X0,X5,X1] : (r2_hidden(X5,X1) | ~r1_orders_2(X0,X4,X5) | ~r2_hidden(X4,X1) | ~m1_subset_1(X5,u1_struct_0(X0)) | ~m1_subset_1(X4,u1_struct_0(X0)) | ~v13_waybel_0(X1,X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_orders_2(X0)) )),
% 3.51/0.98    inference(cnf_transformation,[],[f47])).
% 3.51/0.98  
% 3.51/0.98  fof(f84,plain,(
% 3.51/0.98    v13_waybel_0(sK4,sK3)),
% 3.51/0.98    inference(cnf_transformation,[],[f53])).
% 3.51/0.98  
% 3.51/0.98  fof(f76,plain,(
% 3.51/0.98    ( ! [X0,X1] : (v1_subset_1(X1,X0) | X0 = X1 | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 3.51/0.98    inference(cnf_transformation,[],[f48])).
% 3.51/0.98  
% 3.51/0.98  fof(f87,plain,(
% 3.51/0.98    r2_hidden(k3_yellow_0(sK3),sK4) | ~v1_subset_1(sK4,u1_struct_0(sK3))),
% 3.51/0.98    inference(cnf_transformation,[],[f53])).
% 3.51/0.98  
% 3.51/0.98  fof(f55,plain,(
% 3.51/0.98    ( ! [X0,X1] : (X0 = X1 | ~r2_hidden(sK0(X0,X1),X1) | ~r2_hidden(sK0(X0,X1),X0)) )),
% 3.51/0.98    inference(cnf_transformation,[],[f42])).
% 3.51/0.98  
% 3.51/0.98  cnf(c_5,plain,
% 3.51/0.98      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
% 3.51/0.98      | ~ r2_hidden(X2,X0)
% 3.51/0.98      | r2_hidden(X2,X1) ),
% 3.51/0.98      inference(cnf_transformation,[],[f59]) ).
% 3.51/0.98  
% 3.51/0.98  cnf(c_2012,plain,
% 3.51/0.98      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK3)))
% 3.51/0.98      | ~ r2_hidden(X1,X0)
% 3.51/0.98      | r2_hidden(X1,u1_struct_0(sK3)) ),
% 3.51/0.98      inference(instantiation,[status(thm)],[c_5]) ).
% 3.51/0.98  
% 3.51/0.98  cnf(c_2254,plain,
% 3.51/0.98      ( ~ m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(sK3)))
% 3.51/0.98      | r2_hidden(X0,u1_struct_0(sK3))
% 3.51/0.98      | ~ r2_hidden(X0,sK4) ),
% 3.51/0.98      inference(instantiation,[status(thm)],[c_2012]) ).
% 3.51/0.98  
% 3.51/0.98  cnf(c_6992,plain,
% 3.51/0.98      ( ~ m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(sK3)))
% 3.51/0.98      | r2_hidden(sK0(u1_struct_0(sK3),sK4),u1_struct_0(sK3))
% 3.51/0.98      | ~ r2_hidden(sK0(u1_struct_0(sK3),sK4),sK4) ),
% 3.51/0.98      inference(instantiation,[status(thm)],[c_2254]) ).
% 3.51/0.98  
% 3.51/0.98  cnf(c_1,plain,
% 3.51/0.98      ( r2_hidden(sK0(X0,X1),X1) | r2_hidden(sK0(X0,X1),X0) | X1 = X0 ),
% 3.51/0.98      inference(cnf_transformation,[],[f54]) ).
% 3.51/0.98  
% 3.51/0.98  cnf(c_1829,plain,
% 3.51/0.98      ( X0 = X1
% 3.51/0.98      | r2_hidden(sK0(X1,X0),X0) = iProver_top
% 3.51/0.98      | r2_hidden(sK0(X1,X0),X1) = iProver_top ),
% 3.51/0.98      inference(predicate_to_equality,[status(thm)],[c_1]) ).
% 3.51/0.98  
% 3.51/0.98  cnf(c_6,plain,
% 3.51/0.98      ( m1_subset_1(X0,X1) | ~ r2_hidden(X0,X1) ),
% 3.51/0.98      inference(cnf_transformation,[],[f60]) ).
% 3.51/0.98  
% 3.51/0.98  cnf(c_1826,plain,
% 3.51/0.98      ( m1_subset_1(X0,X1) = iProver_top
% 3.51/0.98      | r2_hidden(X0,X1) != iProver_top ),
% 3.51/0.98      inference(predicate_to_equality,[status(thm)],[c_6]) ).
% 3.51/0.98  
% 3.51/0.98  cnf(c_2463,plain,
% 3.51/0.98      ( X0 = X1
% 3.51/0.98      | m1_subset_1(sK0(X0,X1),X0) = iProver_top
% 3.51/0.98      | r2_hidden(sK0(X0,X1),X1) = iProver_top ),
% 3.51/0.98      inference(superposition,[status(thm)],[c_1829,c_1826]) ).
% 3.51/0.98  
% 3.51/0.98  cnf(c_19,plain,
% 3.51/0.98      ( ~ m1_subset_1(X0,u1_struct_0(X1))
% 3.51/0.98      | ~ v3_orders_2(X1)
% 3.51/0.98      | ~ v4_orders_2(X1)
% 3.51/0.98      | v2_struct_0(X1)
% 3.51/0.98      | ~ v5_orders_2(X1)
% 3.51/0.98      | ~ l1_orders_2(X1)
% 3.51/0.98      | k1_yellow_0(X1,k5_waybel_0(X1,X0)) = X0 ),
% 3.51/0.98      inference(cnf_transformation,[],[f74]) ).
% 3.51/0.98  
% 3.51/0.98  cnf(c_30,negated_conjecture,
% 3.51/0.98      ( v5_orders_2(sK3) ),
% 3.51/0.98      inference(cnf_transformation,[],[f80]) ).
% 3.51/0.98  
% 3.51/0.98  cnf(c_550,plain,
% 3.51/0.98      ( ~ m1_subset_1(X0,u1_struct_0(X1))
% 3.51/0.98      | ~ v3_orders_2(X1)
% 3.51/0.98      | ~ v4_orders_2(X1)
% 3.51/0.98      | v2_struct_0(X1)
% 3.51/0.98      | ~ l1_orders_2(X1)
% 3.51/0.98      | k1_yellow_0(X1,k5_waybel_0(X1,X0)) = X0
% 3.51/0.98      | sK3 != X1 ),
% 3.51/0.98      inference(resolution_lifted,[status(thm)],[c_19,c_30]) ).
% 3.51/0.98  
% 3.51/0.98  cnf(c_551,plain,
% 3.51/0.98      ( ~ m1_subset_1(X0,u1_struct_0(sK3))
% 3.51/0.98      | ~ v3_orders_2(sK3)
% 3.51/0.98      | ~ v4_orders_2(sK3)
% 3.51/0.98      | v2_struct_0(sK3)
% 3.51/0.98      | ~ l1_orders_2(sK3)
% 3.51/0.98      | k1_yellow_0(sK3,k5_waybel_0(sK3,X0)) = X0 ),
% 3.51/0.98      inference(unflattening,[status(thm)],[c_550]) ).
% 3.51/0.98  
% 3.51/0.98  cnf(c_33,negated_conjecture,
% 3.51/0.98      ( ~ v2_struct_0(sK3) ),
% 3.51/0.98      inference(cnf_transformation,[],[f77]) ).
% 3.51/0.98  
% 3.51/0.98  cnf(c_32,negated_conjecture,
% 3.51/0.98      ( v3_orders_2(sK3) ),
% 3.51/0.98      inference(cnf_transformation,[],[f78]) ).
% 3.51/0.98  
% 3.51/0.98  cnf(c_31,negated_conjecture,
% 3.51/0.98      ( v4_orders_2(sK3) ),
% 3.51/0.98      inference(cnf_transformation,[],[f79]) ).
% 3.51/0.98  
% 3.51/0.98  cnf(c_28,negated_conjecture,
% 3.51/0.98      ( l1_orders_2(sK3) ),
% 3.51/0.98      inference(cnf_transformation,[],[f82]) ).
% 3.51/0.98  
% 3.51/0.98  cnf(c_555,plain,
% 3.51/0.98      ( ~ m1_subset_1(X0,u1_struct_0(sK3))
% 3.51/0.98      | k1_yellow_0(sK3,k5_waybel_0(sK3,X0)) = X0 ),
% 3.51/0.98      inference(global_propositional_subsumption,
% 3.51/0.98                [status(thm)],
% 3.51/0.98                [c_551,c_33,c_32,c_31,c_28]) ).
% 3.51/0.98  
% 3.51/0.98  cnf(c_1819,plain,
% 3.51/0.98      ( k1_yellow_0(sK3,k5_waybel_0(sK3,X0)) = X0
% 3.51/0.98      | m1_subset_1(X0,u1_struct_0(sK3)) != iProver_top ),
% 3.51/0.98      inference(predicate_to_equality,[status(thm)],[c_555]) ).
% 3.51/0.98  
% 3.51/0.98  cnf(c_3443,plain,
% 3.51/0.98      ( k1_yellow_0(sK3,k5_waybel_0(sK3,sK0(u1_struct_0(sK3),X0))) = sK0(u1_struct_0(sK3),X0)
% 3.51/0.98      | u1_struct_0(sK3) = X0
% 3.51/0.98      | r2_hidden(sK0(u1_struct_0(sK3),X0),X0) = iProver_top ),
% 3.51/0.98      inference(superposition,[status(thm)],[c_2463,c_1819]) ).
% 3.51/0.98  
% 3.51/0.98  cnf(c_25,negated_conjecture,
% 3.51/0.98      ( m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(sK3))) ),
% 3.51/0.98      inference(cnf_transformation,[],[f85]) ).
% 3.51/0.98  
% 3.51/0.98  cnf(c_1824,plain,
% 3.51/0.98      ( m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(sK3))) = iProver_top ),
% 3.51/0.98      inference(predicate_to_equality,[status(thm)],[c_25]) ).
% 3.51/0.98  
% 3.51/0.98  cnf(c_8,plain,
% 3.51/0.98      ( m1_subset_1(X0,X1)
% 3.51/0.98      | ~ m1_subset_1(X2,k1_zfmisc_1(X1))
% 3.51/0.98      | ~ r2_hidden(X0,X2) ),
% 3.51/0.98      inference(cnf_transformation,[],[f62]) ).
% 3.51/0.98  
% 3.51/0.98  cnf(c_1825,plain,
% 3.51/0.98      ( m1_subset_1(X0,X1) = iProver_top
% 3.51/0.98      | m1_subset_1(X2,k1_zfmisc_1(X1)) != iProver_top
% 3.51/0.98      | r2_hidden(X0,X2) != iProver_top ),
% 3.51/0.98      inference(predicate_to_equality,[status(thm)],[c_8]) ).
% 3.51/0.98  
% 3.51/0.98  cnf(c_2822,plain,
% 3.51/0.98      ( m1_subset_1(X0,u1_struct_0(sK3)) = iProver_top
% 3.51/0.98      | r2_hidden(X0,sK4) != iProver_top ),
% 3.51/0.98      inference(superposition,[status(thm)],[c_1824,c_1825]) ).
% 3.51/0.98  
% 3.51/0.98  cnf(c_2852,plain,
% 3.51/0.98      ( k1_yellow_0(sK3,k5_waybel_0(sK3,X0)) = X0
% 3.51/0.98      | r2_hidden(X0,sK4) != iProver_top ),
% 3.51/0.98      inference(superposition,[status(thm)],[c_2822,c_1819]) ).
% 3.51/0.98  
% 3.51/0.98  cnf(c_3791,plain,
% 3.51/0.98      ( k1_yellow_0(sK3,k5_waybel_0(sK3,sK0(u1_struct_0(sK3),sK4))) = sK0(u1_struct_0(sK3),sK4)
% 3.51/0.98      | u1_struct_0(sK3) = sK4 ),
% 3.51/0.98      inference(superposition,[status(thm)],[c_3443,c_2852]) ).
% 3.51/0.98  
% 3.51/0.98  cnf(c_20,plain,
% 3.51/0.98      ( r1_yellow_0(X0,k5_waybel_0(X0,X1))
% 3.51/0.98      | ~ m1_subset_1(X1,u1_struct_0(X0))
% 3.51/0.98      | ~ v3_orders_2(X0)
% 3.51/0.98      | ~ v4_orders_2(X0)
% 3.51/0.98      | v2_struct_0(X0)
% 3.51/0.98      | ~ v5_orders_2(X0)
% 3.51/0.98      | ~ l1_orders_2(X0) ),
% 3.51/0.98      inference(cnf_transformation,[],[f73]) ).
% 3.51/0.98  
% 3.51/0.98  cnf(c_532,plain,
% 3.51/0.98      ( r1_yellow_0(X0,k5_waybel_0(X0,X1))
% 3.51/0.98      | ~ m1_subset_1(X1,u1_struct_0(X0))
% 3.51/0.98      | ~ v3_orders_2(X0)
% 3.51/0.98      | ~ v4_orders_2(X0)
% 3.51/0.98      | v2_struct_0(X0)
% 3.51/0.98      | ~ l1_orders_2(X0)
% 3.51/0.98      | sK3 != X0 ),
% 3.51/0.98      inference(resolution_lifted,[status(thm)],[c_20,c_30]) ).
% 3.51/0.98  
% 3.51/0.98  cnf(c_533,plain,
% 3.51/0.98      ( r1_yellow_0(sK3,k5_waybel_0(sK3,X0))
% 3.51/0.98      | ~ m1_subset_1(X0,u1_struct_0(sK3))
% 3.51/0.98      | ~ v3_orders_2(sK3)
% 3.51/0.98      | ~ v4_orders_2(sK3)
% 3.51/0.98      | v2_struct_0(sK3)
% 3.51/0.98      | ~ l1_orders_2(sK3) ),
% 3.51/0.98      inference(unflattening,[status(thm)],[c_532]) ).
% 3.51/0.98  
% 3.51/0.98  cnf(c_537,plain,
% 3.51/0.98      ( r1_yellow_0(sK3,k5_waybel_0(sK3,X0))
% 3.51/0.98      | ~ m1_subset_1(X0,u1_struct_0(sK3)) ),
% 3.51/0.98      inference(global_propositional_subsumption,
% 3.51/0.98                [status(thm)],
% 3.51/0.98                [c_533,c_33,c_32,c_31,c_28]) ).
% 3.51/0.98  
% 3.51/0.98  cnf(c_2,plain,
% 3.51/0.98      ( r1_tarski(k1_xboole_0,X0) ),
% 3.51/0.98      inference(cnf_transformation,[],[f56]) ).
% 3.51/0.98  
% 3.51/0.98  cnf(c_11,plain,
% 3.51/0.98      ( r1_orders_2(X0,k1_yellow_0(X0,X1),k1_yellow_0(X0,X2))
% 3.51/0.98      | ~ r1_yellow_0(X0,X2)
% 3.51/0.98      | ~ r1_yellow_0(X0,X1)
% 3.51/0.98      | ~ r1_tarski(X1,X2)
% 3.51/0.98      | ~ l1_orders_2(X0) ),
% 3.51/0.98      inference(cnf_transformation,[],[f65]) ).
% 3.51/0.98  
% 3.51/0.98  cnf(c_459,plain,
% 3.51/0.98      ( r1_orders_2(X0,k1_yellow_0(X0,X1),k1_yellow_0(X0,X2))
% 3.51/0.98      | ~ r1_yellow_0(X0,X2)
% 3.51/0.98      | ~ r1_yellow_0(X0,X1)
% 3.51/0.98      | ~ l1_orders_2(X0)
% 3.51/0.98      | X2 != X3
% 3.51/0.98      | k1_xboole_0 != X1 ),
% 3.51/0.98      inference(resolution_lifted,[status(thm)],[c_2,c_11]) ).
% 3.51/0.98  
% 3.51/0.98  cnf(c_460,plain,
% 3.51/0.98      ( r1_orders_2(X0,k1_yellow_0(X0,k1_xboole_0),k1_yellow_0(X0,X1))
% 3.51/0.98      | ~ r1_yellow_0(X0,X1)
% 3.51/0.98      | ~ r1_yellow_0(X0,k1_xboole_0)
% 3.51/0.98      | ~ l1_orders_2(X0) ),
% 3.51/0.98      inference(unflattening,[status(thm)],[c_459]) ).
% 3.51/0.98  
% 3.51/0.98  cnf(c_654,plain,
% 3.51/0.98      ( r1_orders_2(X0,k1_yellow_0(X0,k1_xboole_0),k1_yellow_0(X0,X1))
% 3.51/0.98      | ~ r1_yellow_0(X0,X1)
% 3.51/0.98      | ~ r1_yellow_0(X0,k1_xboole_0)
% 3.51/0.98      | sK3 != X0 ),
% 3.51/0.98      inference(resolution_lifted,[status(thm)],[c_460,c_28]) ).
% 3.51/0.98  
% 3.51/0.98  cnf(c_655,plain,
% 3.51/0.98      ( r1_orders_2(sK3,k1_yellow_0(sK3,k1_xboole_0),k1_yellow_0(sK3,X0))
% 3.51/0.98      | ~ r1_yellow_0(sK3,X0)
% 3.51/0.98      | ~ r1_yellow_0(sK3,k1_xboole_0) ),
% 3.51/0.98      inference(unflattening,[status(thm)],[c_654]) ).
% 3.51/0.98  
% 3.51/0.98  cnf(c_29,negated_conjecture,
% 3.51/0.98      ( v1_yellow_0(sK3) ),
% 3.51/0.98      inference(cnf_transformation,[],[f81]) ).
% 3.51/0.98  
% 3.51/0.98  cnf(c_12,plain,
% 3.51/0.98      ( r1_yellow_0(X0,k1_xboole_0)
% 3.51/0.98      | v2_struct_0(X0)
% 3.51/0.98      | ~ v5_orders_2(X0)
% 3.51/0.98      | ~ v1_yellow_0(X0)
% 3.51/0.98      | ~ l1_orders_2(X0) ),
% 3.51/0.98      inference(cnf_transformation,[],[f66]) ).
% 3.51/0.98  
% 3.51/0.98  cnf(c_74,plain,
% 3.51/0.98      ( r1_yellow_0(sK3,k1_xboole_0)
% 3.51/0.98      | v2_struct_0(sK3)
% 3.51/0.98      | ~ v5_orders_2(sK3)
% 3.51/0.98      | ~ v1_yellow_0(sK3)
% 3.51/0.98      | ~ l1_orders_2(sK3) ),
% 3.51/0.98      inference(instantiation,[status(thm)],[c_12]) ).
% 3.51/0.98  
% 3.51/0.98  cnf(c_659,plain,
% 3.51/0.98      ( ~ r1_yellow_0(sK3,X0)
% 3.51/0.98      | r1_orders_2(sK3,k1_yellow_0(sK3,k1_xboole_0),k1_yellow_0(sK3,X0)) ),
% 3.51/0.98      inference(global_propositional_subsumption,
% 3.51/0.98                [status(thm)],
% 3.51/0.98                [c_655,c_33,c_30,c_29,c_28,c_74]) ).
% 3.51/0.98  
% 3.51/0.98  cnf(c_660,plain,
% 3.51/0.98      ( r1_orders_2(sK3,k1_yellow_0(sK3,k1_xboole_0),k1_yellow_0(sK3,X0))
% 3.51/0.98      | ~ r1_yellow_0(sK3,X0) ),
% 3.51/0.98      inference(renaming,[status(thm)],[c_659]) ).
% 3.51/0.98  
% 3.51/0.98  cnf(c_824,plain,
% 3.51/0.98      ( r1_orders_2(sK3,k1_yellow_0(sK3,k1_xboole_0),k1_yellow_0(sK3,X0))
% 3.51/0.98      | ~ m1_subset_1(X1,u1_struct_0(sK3))
% 3.51/0.98      | k5_waybel_0(sK3,X1) != X0
% 3.51/0.98      | sK3 != sK3 ),
% 3.51/0.98      inference(resolution_lifted,[status(thm)],[c_537,c_660]) ).
% 3.51/0.98  
% 3.51/0.98  cnf(c_825,plain,
% 3.51/0.98      ( r1_orders_2(sK3,k1_yellow_0(sK3,k1_xboole_0),k1_yellow_0(sK3,k5_waybel_0(sK3,X0)))
% 3.51/0.98      | ~ m1_subset_1(X0,u1_struct_0(sK3)) ),
% 3.51/0.98      inference(unflattening,[status(thm)],[c_824]) ).
% 3.51/0.98  
% 3.51/0.98  cnf(c_1810,plain,
% 3.51/0.98      ( r1_orders_2(sK3,k1_yellow_0(sK3,k1_xboole_0),k1_yellow_0(sK3,k5_waybel_0(sK3,X0))) = iProver_top
% 3.51/0.98      | m1_subset_1(X0,u1_struct_0(sK3)) != iProver_top ),
% 3.51/0.98      inference(predicate_to_equality,[status(thm)],[c_825]) ).
% 3.51/0.98  
% 3.51/0.98  cnf(c_9,plain,
% 3.51/0.98      ( ~ l1_orders_2(X0)
% 3.51/0.98      | k1_yellow_0(X0,k1_xboole_0) = k3_yellow_0(X0) ),
% 3.51/0.98      inference(cnf_transformation,[],[f63]) ).
% 3.51/0.98  
% 3.51/0.98  cnf(c_719,plain,
% 3.51/0.98      ( k1_yellow_0(X0,k1_xboole_0) = k3_yellow_0(X0) | sK3 != X0 ),
% 3.51/0.98      inference(resolution_lifted,[status(thm)],[c_9,c_28]) ).
% 3.51/0.98  
% 3.51/0.98  cnf(c_720,plain,
% 3.51/0.98      ( k1_yellow_0(sK3,k1_xboole_0) = k3_yellow_0(sK3) ),
% 3.51/0.98      inference(unflattening,[status(thm)],[c_719]) ).
% 3.51/0.98  
% 3.51/0.98  cnf(c_1833,plain,
% 3.51/0.98      ( r1_orders_2(sK3,k3_yellow_0(sK3),k1_yellow_0(sK3,k5_waybel_0(sK3,X0))) = iProver_top
% 3.51/0.98      | m1_subset_1(X0,u1_struct_0(sK3)) != iProver_top ),
% 3.51/0.98      inference(light_normalisation,[status(thm)],[c_1810,c_720]) ).
% 3.51/0.98  
% 3.51/0.98  cnf(c_5652,plain,
% 3.51/0.98      ( u1_struct_0(sK3) = sK4
% 3.51/0.98      | r1_orders_2(sK3,k3_yellow_0(sK3),sK0(u1_struct_0(sK3),sK4)) = iProver_top
% 3.51/0.98      | m1_subset_1(sK0(u1_struct_0(sK3),sK4),u1_struct_0(sK3)) != iProver_top ),
% 3.51/0.98      inference(superposition,[status(thm)],[c_3791,c_1833]) ).
% 3.51/0.98  
% 3.51/0.98  cnf(c_10,plain,
% 3.51/0.98      ( m1_subset_1(k3_yellow_0(X0),u1_struct_0(X0))
% 3.51/0.98      | ~ l1_orders_2(X0) ),
% 3.51/0.98      inference(cnf_transformation,[],[f64]) ).
% 3.51/0.98  
% 3.51/0.98  cnf(c_80,plain,
% 3.51/0.98      ( m1_subset_1(k3_yellow_0(sK3),u1_struct_0(sK3))
% 3.51/0.98      | ~ l1_orders_2(sK3) ),
% 3.51/0.98      inference(instantiation,[status(thm)],[c_10]) ).
% 3.51/0.98  
% 3.51/0.98  cnf(c_22,plain,
% 3.51/0.98      ( ~ v1_subset_1(X0,X0) | ~ m1_subset_1(X0,k1_zfmisc_1(X0)) ),
% 3.51/0.98      inference(cnf_transformation,[],[f88]) ).
% 3.51/0.98  
% 3.51/0.98  cnf(c_24,negated_conjecture,
% 3.51/0.98      ( v1_subset_1(sK4,u1_struct_0(sK3))
% 3.51/0.98      | ~ r2_hidden(k3_yellow_0(sK3),sK4) ),
% 3.51/0.98      inference(cnf_transformation,[],[f86]) ).
% 3.51/0.98  
% 3.51/0.98  cnf(c_246,plain,
% 3.51/0.98      ( v1_subset_1(sK4,u1_struct_0(sK3))
% 3.51/0.98      | ~ r2_hidden(k3_yellow_0(sK3),sK4) ),
% 3.51/0.98      inference(prop_impl,[status(thm)],[c_24]) ).
% 3.51/0.98  
% 3.51/0.98  cnf(c_512,plain,
% 3.51/0.98      ( ~ m1_subset_1(X0,k1_zfmisc_1(X0))
% 3.51/0.98      | ~ r2_hidden(k3_yellow_0(sK3),sK4)
% 3.51/0.98      | u1_struct_0(sK3) != X0
% 3.51/0.98      | sK4 != X0 ),
% 3.51/0.98      inference(resolution_lifted,[status(thm)],[c_22,c_246]) ).
% 3.51/0.98  
% 3.51/0.98  cnf(c_513,plain,
% 3.51/0.98      ( ~ m1_subset_1(u1_struct_0(sK3),k1_zfmisc_1(u1_struct_0(sK3)))
% 3.51/0.98      | ~ r2_hidden(k3_yellow_0(sK3),sK4)
% 3.51/0.98      | sK4 != u1_struct_0(sK3) ),
% 3.51/0.98      inference(unflattening,[status(thm)],[c_512]) ).
% 3.51/0.98  
% 3.51/0.98  cnf(c_1445,plain,
% 3.51/0.98      ( X0 != X1 | k3_yellow_0(X0) = k3_yellow_0(X1) ),
% 3.51/0.98      theory(equality) ).
% 3.51/0.98  
% 3.51/0.98  cnf(c_1456,plain,
% 3.51/0.98      ( k3_yellow_0(sK3) = k3_yellow_0(sK3) | sK3 != sK3 ),
% 3.51/0.98      inference(instantiation,[status(thm)],[c_1445]) ).
% 3.51/0.98  
% 3.51/0.98  cnf(c_1440,plain,( X0 = X0 ),theory(equality) ).
% 3.51/0.98  
% 3.51/0.98  cnf(c_1465,plain,
% 3.51/0.98      ( sK3 = sK3 ),
% 3.51/0.98      inference(instantiation,[status(thm)],[c_1440]) ).
% 3.51/0.98  
% 3.51/0.98  cnf(c_2358,plain,
% 3.51/0.98      ( sK4 = sK4 ),
% 3.51/0.98      inference(instantiation,[status(thm)],[c_1440]) ).
% 3.51/0.98  
% 3.51/0.98  cnf(c_2404,plain,
% 3.51/0.98      ( k1_zfmisc_1(u1_struct_0(sK3)) = k1_zfmisc_1(u1_struct_0(sK3)) ),
% 3.51/0.98      inference(instantiation,[status(thm)],[c_1440]) ).
% 3.51/0.98  
% 3.51/0.98  cnf(c_1444,plain,
% 3.51/0.98      ( ~ m1_subset_1(X0,X1) | m1_subset_1(X2,X3) | X2 != X0 | X3 != X1 ),
% 3.51/0.98      theory(equality) ).
% 3.51/0.98  
% 3.51/0.98  cnf(c_1882,plain,
% 3.51/0.98      ( ~ m1_subset_1(X0,X1)
% 3.51/0.98      | m1_subset_1(X2,sK4)
% 3.51/0.98      | X2 != X0
% 3.51/0.98      | sK4 != X1 ),
% 3.51/0.98      inference(instantiation,[status(thm)],[c_1444]) ).
% 3.51/0.98  
% 3.51/0.98  cnf(c_2326,plain,
% 3.51/0.98      ( m1_subset_1(X0,sK4)
% 3.51/0.98      | ~ m1_subset_1(k3_yellow_0(sK3),u1_struct_0(sK3))
% 3.51/0.98      | X0 != k3_yellow_0(sK3)
% 3.51/0.98      | sK4 != u1_struct_0(sK3) ),
% 3.51/0.98      inference(instantiation,[status(thm)],[c_1882]) ).
% 3.51/0.98  
% 3.51/0.98  cnf(c_2622,plain,
% 3.51/0.98      ( ~ m1_subset_1(k3_yellow_0(sK3),u1_struct_0(sK3))
% 3.51/0.98      | m1_subset_1(k3_yellow_0(sK3),sK4)
% 3.51/0.98      | k3_yellow_0(sK3) != k3_yellow_0(sK3)
% 3.51/0.98      | sK4 != u1_struct_0(sK3) ),
% 3.51/0.98      inference(instantiation,[status(thm)],[c_2326]) ).
% 3.51/0.98  
% 3.51/0.98  cnf(c_2892,plain,
% 3.51/0.98      ( m1_subset_1(X0,X1)
% 3.51/0.98      | ~ m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(sK3)))
% 3.51/0.98      | X1 != k1_zfmisc_1(u1_struct_0(sK3))
% 3.51/0.98      | X0 != sK4 ),
% 3.51/0.98      inference(instantiation,[status(thm)],[c_1444]) ).
% 3.51/0.98  
% 3.51/0.98  cnf(c_3148,plain,
% 3.51/0.98      ( m1_subset_1(u1_struct_0(sK3),X0)
% 3.51/0.98      | ~ m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(sK3)))
% 3.51/0.98      | X0 != k1_zfmisc_1(u1_struct_0(sK3))
% 3.51/0.98      | u1_struct_0(sK3) != sK4 ),
% 3.51/0.98      inference(instantiation,[status(thm)],[c_2892]) ).
% 3.51/0.98  
% 3.51/0.98  cnf(c_3572,plain,
% 3.51/0.98      ( m1_subset_1(u1_struct_0(sK3),k1_zfmisc_1(u1_struct_0(sK3)))
% 3.51/0.98      | ~ m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(sK3)))
% 3.51/0.98      | u1_struct_0(sK3) != sK4
% 3.51/0.98      | k1_zfmisc_1(u1_struct_0(sK3)) != k1_zfmisc_1(u1_struct_0(sK3)) ),
% 3.51/0.98      inference(instantiation,[status(thm)],[c_3148]) ).
% 3.51/0.98  
% 3.51/0.98  cnf(c_1441,plain,( X0 != X1 | X2 != X1 | X2 = X0 ),theory(equality) ).
% 3.51/0.98  
% 3.51/0.98  cnf(c_2104,plain,
% 3.51/0.98      ( X0 != X1 | sK4 != X1 | sK4 = X0 ),
% 3.51/0.98      inference(instantiation,[status(thm)],[c_1441]) ).
% 3.51/0.98  
% 3.51/0.98  cnf(c_2366,plain,
% 3.51/0.98      ( u1_struct_0(sK3) != X0 | sK4 != X0 | sK4 = u1_struct_0(sK3) ),
% 3.51/0.98      inference(instantiation,[status(thm)],[c_2104]) ).
% 3.51/0.98  
% 3.51/0.98  cnf(c_4510,plain,
% 3.51/0.98      ( u1_struct_0(sK3) != sK4 | sK4 = u1_struct_0(sK3) | sK4 != sK4 ),
% 3.51/0.98      inference(instantiation,[status(thm)],[c_2366]) ).
% 3.51/0.98  
% 3.51/0.98  cnf(c_7,plain,
% 3.51/0.98      ( ~ m1_subset_1(X0,X1) | r2_hidden(X0,X1) | v1_xboole_0(X1) ),
% 3.51/0.98      inference(cnf_transformation,[],[f61]) ).
% 3.51/0.98  
% 3.51/0.98  cnf(c_27,negated_conjecture,
% 3.51/0.98      ( ~ v1_xboole_0(sK4) ),
% 3.51/0.98      inference(cnf_transformation,[],[f83]) ).
% 3.51/0.98  
% 3.51/0.98  cnf(c_444,plain,
% 3.51/0.98      ( ~ m1_subset_1(X0,X1) | r2_hidden(X0,X1) | sK4 != X1 ),
% 3.51/0.98      inference(resolution_lifted,[status(thm)],[c_7,c_27]) ).
% 3.51/0.98  
% 3.51/0.98  cnf(c_445,plain,
% 3.51/0.98      ( ~ m1_subset_1(X0,sK4) | r2_hidden(X0,sK4) ),
% 3.51/0.98      inference(unflattening,[status(thm)],[c_444]) ).
% 3.51/0.98  
% 3.51/0.98  cnf(c_5720,plain,
% 3.51/0.98      ( ~ m1_subset_1(k3_yellow_0(sK3),sK4)
% 3.51/0.98      | r2_hidden(k3_yellow_0(sK3),sK4) ),
% 3.51/0.98      inference(instantiation,[status(thm)],[c_445]) ).
% 3.51/0.98  
% 3.51/0.98  cnf(c_5861,plain,
% 3.51/0.98      ( r1_orders_2(sK3,k3_yellow_0(sK3),sK0(u1_struct_0(sK3),sK4)) = iProver_top
% 3.51/0.98      | m1_subset_1(sK0(u1_struct_0(sK3),sK4),u1_struct_0(sK3)) != iProver_top ),
% 3.51/0.98      inference(global_propositional_subsumption,
% 3.51/0.98                [status(thm)],
% 3.51/0.98                [c_5652,c_28,c_25,c_80,c_513,c_1456,c_1465,c_2358,c_2404,
% 3.51/0.98                 c_2622,c_3572,c_4510,c_5720]) ).
% 3.51/0.98  
% 3.51/0.98  cnf(c_18,plain,
% 3.51/0.98      ( ~ r1_orders_2(X0,X1,X2)
% 3.51/0.98      | ~ v13_waybel_0(X3,X0)
% 3.51/0.98      | ~ m1_subset_1(X2,u1_struct_0(X0))
% 3.51/0.98      | ~ m1_subset_1(X1,u1_struct_0(X0))
% 3.51/0.98      | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))
% 3.51/0.98      | ~ r2_hidden(X1,X3)
% 3.51/0.98      | r2_hidden(X2,X3)
% 3.51/0.98      | ~ l1_orders_2(X0) ),
% 3.51/0.98      inference(cnf_transformation,[],[f67]) ).
% 3.51/0.98  
% 3.51/0.98  cnf(c_672,plain,
% 3.51/0.98      ( ~ r1_orders_2(X0,X1,X2)
% 3.51/0.98      | ~ v13_waybel_0(X3,X0)
% 3.51/0.98      | ~ m1_subset_1(X2,u1_struct_0(X0))
% 3.51/0.98      | ~ m1_subset_1(X1,u1_struct_0(X0))
% 3.51/0.98      | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))
% 3.51/0.98      | ~ r2_hidden(X1,X3)
% 3.51/0.98      | r2_hidden(X2,X3)
% 3.51/0.98      | sK3 != X0 ),
% 3.51/0.98      inference(resolution_lifted,[status(thm)],[c_18,c_28]) ).
% 3.51/0.98  
% 3.51/0.98  cnf(c_673,plain,
% 3.51/0.98      ( ~ r1_orders_2(sK3,X0,X1)
% 3.51/0.98      | ~ v13_waybel_0(X2,sK3)
% 3.51/0.98      | ~ m1_subset_1(X0,u1_struct_0(sK3))
% 3.51/0.98      | ~ m1_subset_1(X1,u1_struct_0(sK3))
% 3.51/0.98      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK3)))
% 3.51/0.98      | ~ r2_hidden(X0,X2)
% 3.51/0.98      | r2_hidden(X1,X2) ),
% 3.51/0.98      inference(unflattening,[status(thm)],[c_672]) ).
% 3.51/0.98  
% 3.51/0.98  cnf(c_689,plain,
% 3.51/0.98      ( ~ r1_orders_2(sK3,X0,X1)
% 3.51/0.98      | ~ v13_waybel_0(X2,sK3)
% 3.51/0.98      | ~ m1_subset_1(X1,u1_struct_0(sK3))
% 3.51/0.98      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK3)))
% 3.51/0.98      | ~ r2_hidden(X0,X2)
% 3.51/0.98      | r2_hidden(X1,X2) ),
% 3.51/0.98      inference(forward_subsumption_resolution,[status(thm)],[c_673,c_8]) ).
% 3.51/0.98  
% 3.51/0.98  cnf(c_1818,plain,
% 3.51/0.98      ( r1_orders_2(sK3,X0,X1) != iProver_top
% 3.51/0.98      | v13_waybel_0(X2,sK3) != iProver_top
% 3.51/0.98      | m1_subset_1(X1,u1_struct_0(sK3)) != iProver_top
% 3.51/0.98      | m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK3))) != iProver_top
% 3.51/0.98      | r2_hidden(X0,X2) != iProver_top
% 3.51/0.98      | r2_hidden(X1,X2) = iProver_top ),
% 3.51/0.98      inference(predicate_to_equality,[status(thm)],[c_689]) ).
% 3.51/0.98  
% 3.51/0.98  cnf(c_2744,plain,
% 3.51/0.98      ( r1_orders_2(sK3,X0,X1) != iProver_top
% 3.51/0.98      | v13_waybel_0(sK4,sK3) != iProver_top
% 3.51/0.98      | m1_subset_1(X1,u1_struct_0(sK3)) != iProver_top
% 3.51/0.98      | r2_hidden(X0,sK4) != iProver_top
% 3.51/0.98      | r2_hidden(X1,sK4) = iProver_top ),
% 3.51/0.98      inference(superposition,[status(thm)],[c_1824,c_1818]) ).
% 3.51/0.98  
% 3.51/0.98  cnf(c_42,plain,
% 3.51/0.98      ( m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(sK3))) = iProver_top ),
% 3.51/0.98      inference(predicate_to_equality,[status(thm)],[c_25]) ).
% 3.51/0.98  
% 3.51/0.98  cnf(c_26,negated_conjecture,
% 3.51/0.98      ( v13_waybel_0(sK4,sK3) ),
% 3.51/0.98      inference(cnf_transformation,[],[f84]) ).
% 3.51/0.98  
% 3.51/0.98  cnf(c_904,plain,
% 3.51/0.98      ( ~ r1_orders_2(sK3,X0,X1)
% 3.51/0.98      | ~ m1_subset_1(X1,u1_struct_0(sK3))
% 3.51/0.98      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK3)))
% 3.51/0.98      | ~ r2_hidden(X0,X2)
% 3.51/0.98      | r2_hidden(X1,X2)
% 3.51/0.98      | sK4 != X2
% 3.51/0.98      | sK3 != sK3 ),
% 3.51/0.98      inference(resolution_lifted,[status(thm)],[c_26,c_689]) ).
% 3.51/0.98  
% 3.51/0.98  cnf(c_905,plain,
% 3.51/0.98      ( ~ r1_orders_2(sK3,X0,X1)
% 3.51/0.98      | ~ m1_subset_1(X1,u1_struct_0(sK3))
% 3.51/0.98      | ~ m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(sK3)))
% 3.51/0.98      | ~ r2_hidden(X0,sK4)
% 3.51/0.98      | r2_hidden(X1,sK4) ),
% 3.51/0.98      inference(unflattening,[status(thm)],[c_904]) ).
% 3.51/0.98  
% 3.51/0.98  cnf(c_906,plain,
% 3.51/0.98      ( r1_orders_2(sK3,X0,X1) != iProver_top
% 3.51/0.98      | m1_subset_1(X1,u1_struct_0(sK3)) != iProver_top
% 3.51/0.98      | m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(sK3))) != iProver_top
% 3.51/0.98      | r2_hidden(X0,sK4) != iProver_top
% 3.51/0.98      | r2_hidden(X1,sK4) = iProver_top ),
% 3.51/0.98      inference(predicate_to_equality,[status(thm)],[c_905]) ).
% 3.51/0.98  
% 3.51/0.98  cnf(c_2797,plain,
% 3.51/0.98      ( r1_orders_2(sK3,X0,X1) != iProver_top
% 3.51/0.98      | m1_subset_1(X1,u1_struct_0(sK3)) != iProver_top
% 3.51/0.98      | r2_hidden(X0,sK4) != iProver_top
% 3.51/0.98      | r2_hidden(X1,sK4) = iProver_top ),
% 3.51/0.98      inference(global_propositional_subsumption,
% 3.51/0.98                [status(thm)],
% 3.51/0.98                [c_2744,c_42,c_906]) ).
% 3.51/0.98  
% 3.51/0.98  cnf(c_5866,plain,
% 3.51/0.98      ( m1_subset_1(sK0(u1_struct_0(sK3),sK4),u1_struct_0(sK3)) != iProver_top
% 3.51/0.98      | r2_hidden(sK0(u1_struct_0(sK3),sK4),sK4) = iProver_top
% 3.51/0.98      | r2_hidden(k3_yellow_0(sK3),sK4) != iProver_top ),
% 3.51/0.98      inference(superposition,[status(thm)],[c_5861,c_2797]) ).
% 3.51/0.98  
% 3.51/0.98  cnf(c_21,plain,
% 3.51/0.98      ( v1_subset_1(X0,X1)
% 3.51/0.98      | ~ m1_subset_1(X0,k1_zfmisc_1(X1))
% 3.51/0.98      | X0 = X1 ),
% 3.51/0.98      inference(cnf_transformation,[],[f76]) ).
% 3.51/0.98  
% 3.51/0.98  cnf(c_23,negated_conjecture,
% 3.51/0.98      ( ~ v1_subset_1(sK4,u1_struct_0(sK3))
% 3.51/0.98      | r2_hidden(k3_yellow_0(sK3),sK4) ),
% 3.51/0.98      inference(cnf_transformation,[],[f87]) ).
% 3.51/0.98  
% 3.51/0.98  cnf(c_248,plain,
% 3.51/0.98      ( ~ v1_subset_1(sK4,u1_struct_0(sK3))
% 3.51/0.98      | r2_hidden(k3_yellow_0(sK3),sK4) ),
% 3.51/0.98      inference(prop_impl,[status(thm)],[c_23]) ).
% 3.51/0.98  
% 3.51/0.98  cnf(c_498,plain,
% 3.51/0.98      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
% 3.51/0.98      | r2_hidden(k3_yellow_0(sK3),sK4)
% 3.51/0.98      | X1 = X0
% 3.51/0.98      | u1_struct_0(sK3) != X1
% 3.51/0.98      | sK4 != X0 ),
% 3.51/0.98      inference(resolution_lifted,[status(thm)],[c_21,c_248]) ).
% 3.51/0.98  
% 3.51/0.98  cnf(c_499,plain,
% 3.51/0.98      ( ~ m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(sK3)))
% 3.51/0.98      | r2_hidden(k3_yellow_0(sK3),sK4)
% 3.51/0.98      | u1_struct_0(sK3) = sK4 ),
% 3.51/0.98      inference(unflattening,[status(thm)],[c_498]) ).
% 3.51/0.98  
% 3.51/0.98  cnf(c_501,plain,
% 3.51/0.98      ( r2_hidden(k3_yellow_0(sK3),sK4) | u1_struct_0(sK3) = sK4 ),
% 3.51/0.98      inference(global_propositional_subsumption,
% 3.51/0.98                [status(thm)],
% 3.51/0.98                [c_499,c_25]) ).
% 3.51/0.98  
% 3.51/0.98  cnf(c_503,plain,
% 3.51/0.98      ( u1_struct_0(sK3) = sK4
% 3.51/0.98      | r2_hidden(k3_yellow_0(sK3),sK4) = iProver_top ),
% 3.51/0.98      inference(predicate_to_equality,[status(thm)],[c_501]) ).
% 3.51/0.98  
% 3.51/0.98  cnf(c_5870,plain,
% 3.51/0.98      ( r2_hidden(sK0(u1_struct_0(sK3),sK4),sK4) = iProver_top
% 3.51/0.98      | m1_subset_1(sK0(u1_struct_0(sK3),sK4),u1_struct_0(sK3)) != iProver_top ),
% 3.51/0.98      inference(global_propositional_subsumption,
% 3.51/0.98                [status(thm)],
% 3.51/0.98                [c_5866,c_28,c_25,c_80,c_503,c_513,c_1456,c_1465,c_2358,
% 3.51/0.98                 c_2404,c_2622,c_3572,c_4510,c_5720]) ).
% 3.51/0.98  
% 3.51/0.98  cnf(c_5871,plain,
% 3.51/0.98      ( m1_subset_1(sK0(u1_struct_0(sK3),sK4),u1_struct_0(sK3)) != iProver_top
% 3.51/0.98      | r2_hidden(sK0(u1_struct_0(sK3),sK4),sK4) = iProver_top ),
% 3.51/0.98      inference(renaming,[status(thm)],[c_5870]) ).
% 3.51/0.98  
% 3.51/0.98  cnf(c_5876,plain,
% 3.51/0.98      ( u1_struct_0(sK3) = sK4
% 3.51/0.98      | r2_hidden(sK0(u1_struct_0(sK3),sK4),sK4) = iProver_top ),
% 3.51/0.98      inference(superposition,[status(thm)],[c_2463,c_5871]) ).
% 3.51/0.98  
% 3.51/0.98  cnf(c_6811,plain,
% 3.51/0.98      ( r2_hidden(sK0(u1_struct_0(sK3),sK4),sK4) = iProver_top ),
% 3.51/0.98      inference(global_propositional_subsumption,
% 3.51/0.98                [status(thm)],
% 3.51/0.98                [c_5876,c_28,c_25,c_80,c_513,c_1456,c_1465,c_2358,c_2404,
% 3.51/0.98                 c_2622,c_3572,c_4510,c_5720]) ).
% 3.51/0.98  
% 3.51/0.98  cnf(c_0,plain,
% 3.51/0.98      ( ~ r2_hidden(sK0(X0,X1),X1)
% 3.51/0.98      | ~ r2_hidden(sK0(X0,X1),X0)
% 3.51/0.98      | X1 = X0 ),
% 3.51/0.98      inference(cnf_transformation,[],[f55]) ).
% 3.51/0.98  
% 3.51/0.98  cnf(c_1830,plain,
% 3.51/0.98      ( X0 = X1
% 3.51/0.98      | r2_hidden(sK0(X1,X0),X0) != iProver_top
% 3.51/0.98      | r2_hidden(sK0(X1,X0),X1) != iProver_top ),
% 3.51/0.98      inference(predicate_to_equality,[status(thm)],[c_0]) ).
% 3.51/0.98  
% 3.51/0.98  cnf(c_6816,plain,
% 3.51/0.98      ( u1_struct_0(sK3) = sK4
% 3.51/0.98      | r2_hidden(sK0(u1_struct_0(sK3),sK4),u1_struct_0(sK3)) != iProver_top ),
% 3.51/0.98      inference(superposition,[status(thm)],[c_6811,c_1830]) ).
% 3.51/0.98  
% 3.51/0.98  cnf(c_6819,plain,
% 3.51/0.98      ( ~ r2_hidden(sK0(u1_struct_0(sK3),sK4),u1_struct_0(sK3))
% 3.51/0.98      | u1_struct_0(sK3) = sK4 ),
% 3.51/0.98      inference(predicate_to_equality_rev,[status(thm)],[c_6816]) ).
% 3.51/0.98  
% 3.51/0.98  cnf(c_6813,plain,
% 3.51/0.98      ( r2_hidden(sK0(u1_struct_0(sK3),sK4),sK4) ),
% 3.51/0.98      inference(predicate_to_equality_rev,[status(thm)],[c_6811]) ).
% 3.51/0.98  
% 3.51/0.98  cnf(c_2091,plain,
% 3.51/0.98      ( ~ r2_hidden(sK0(X0,sK4),X0)
% 3.51/0.98      | ~ r2_hidden(sK0(X0,sK4),sK4)
% 3.51/0.98      | sK4 = X0 ),
% 3.51/0.98      inference(instantiation,[status(thm)],[c_0]) ).
% 3.51/0.98  
% 3.51/0.98  cnf(c_2316,plain,
% 3.51/0.98      ( ~ r2_hidden(sK0(u1_struct_0(sK3),sK4),u1_struct_0(sK3))
% 3.51/0.98      | ~ r2_hidden(sK0(u1_struct_0(sK3),sK4),sK4)
% 3.51/0.98      | sK4 = u1_struct_0(sK3) ),
% 3.51/0.98      inference(instantiation,[status(thm)],[c_2091]) ).
% 3.51/0.98  
% 3.51/0.98  cnf(contradiction,plain,
% 3.51/0.98      ( $false ),
% 3.51/0.98      inference(minisat,
% 3.51/0.98                [status(thm)],
% 3.51/0.98                [c_6992,c_6819,c_6813,c_5720,c_3572,c_2622,c_2404,c_2316,
% 3.51/0.98                 c_1465,c_1456,c_513,c_80,c_25,c_28]) ).
% 3.51/0.98  
% 3.51/0.98  
% 3.51/0.98  % SZS output end CNFRefutation for theBenchmark.p
% 3.51/0.98  
% 3.51/0.98  ------                               Statistics
% 3.51/0.98  
% 3.51/0.98  ------ General
% 3.51/0.98  
% 3.51/0.98  abstr_ref_over_cycles:                  0
% 3.51/0.98  abstr_ref_under_cycles:                 0
% 3.51/0.98  gc_basic_clause_elim:                   0
% 3.51/0.98  forced_gc_time:                         0
% 3.51/0.98  parsing_time:                           0.01
% 3.51/0.98  unif_index_cands_time:                  0.
% 3.51/0.98  unif_index_add_time:                    0.
% 3.51/0.98  orderings_time:                         0.
% 3.51/0.98  out_proof_time:                         0.011
% 3.51/0.98  total_time:                             0.235
% 3.51/0.98  num_of_symbols:                         57
% 3.51/0.98  num_of_terms:                           5654
% 3.51/0.98  
% 3.51/0.98  ------ Preprocessing
% 3.51/0.98  
% 3.51/0.98  num_of_splits:                          0
% 3.51/0.98  num_of_split_atoms:                     0
% 3.51/0.98  num_of_reused_defs:                     0
% 3.51/0.98  num_eq_ax_congr_red:                    25
% 3.51/0.98  num_of_sem_filtered_clauses:            1
% 3.51/0.98  num_of_subtypes:                        0
% 3.51/0.98  monotx_restored_types:                  0
% 3.51/0.98  sat_num_of_epr_types:                   0
% 3.51/0.98  sat_num_of_non_cyclic_types:            0
% 3.51/0.98  sat_guarded_non_collapsed_types:        0
% 3.51/0.98  num_pure_diseq_elim:                    0
% 3.51/0.98  simp_replaced_by:                       0
% 3.51/0.98  res_preprocessed:                       130
% 3.51/0.98  prep_upred:                             0
% 3.51/0.98  prep_unflattend:                        52
% 3.51/0.98  smt_new_axioms:                         0
% 3.51/0.98  pred_elim_cands:                        4
% 3.51/0.98  pred_elim:                              10
% 3.51/0.98  pred_elim_cl:                           11
% 3.51/0.98  pred_elim_cycles:                       15
% 3.51/0.98  merged_defs:                            2
% 3.51/0.98  merged_defs_ncl:                        0
% 3.51/0.98  bin_hyper_res:                          2
% 3.51/0.98  prep_cycles:                            4
% 3.51/0.98  pred_elim_time:                         0.027
% 3.51/0.98  splitting_time:                         0.
% 3.51/0.98  sem_filter_time:                        0.
% 3.51/0.98  monotx_time:                            0.
% 3.51/0.98  subtype_inf_time:                       0.
% 3.51/0.98  
% 3.51/0.98  ------ Problem properties
% 3.51/0.98  
% 3.51/0.98  clauses:                                23
% 3.51/0.98  conjectures:                            2
% 3.51/0.98  epr:                                    3
% 3.51/0.98  horn:                                   17
% 3.51/0.98  ground:                                 7
% 3.51/0.98  unary:                                  7
% 3.51/0.98  binary:                                 5
% 3.51/0.98  lits:                                   53
% 3.51/0.98  lits_eq:                                7
% 3.51/0.98  fd_pure:                                0
% 3.51/0.98  fd_pseudo:                              0
% 3.51/0.98  fd_cond:                                0
% 3.51/0.98  fd_pseudo_cond:                         2
% 3.51/0.98  ac_symbols:                             0
% 3.51/0.98  
% 3.51/0.98  ------ Propositional Solver
% 3.51/0.98  
% 3.51/0.98  prop_solver_calls:                      28
% 3.51/0.98  prop_fast_solver_calls:                 1119
% 3.51/0.98  smt_solver_calls:                       0
% 3.51/0.98  smt_fast_solver_calls:                  0
% 3.51/0.98  prop_num_of_clauses:                    2967
% 3.51/0.98  prop_preprocess_simplified:             6155
% 3.51/0.98  prop_fo_subsumed:                       24
% 3.51/0.98  prop_solver_time:                       0.
% 3.51/0.98  smt_solver_time:                        0.
% 3.51/0.98  smt_fast_solver_time:                   0.
% 3.51/0.98  prop_fast_solver_time:                  0.
% 3.51/0.98  prop_unsat_core_time:                   0.
% 3.51/0.98  
% 3.51/0.98  ------ QBF
% 3.51/0.98  
% 3.51/0.98  qbf_q_res:                              0
% 3.51/0.98  qbf_num_tautologies:                    0
% 3.51/0.98  qbf_prep_cycles:                        0
% 3.51/0.98  
% 3.51/0.98  ------ BMC1
% 3.51/0.98  
% 3.51/0.98  bmc1_current_bound:                     -1
% 3.51/0.98  bmc1_last_solved_bound:                 -1
% 3.51/0.98  bmc1_unsat_core_size:                   -1
% 3.51/0.98  bmc1_unsat_core_parents_size:           -1
% 3.51/0.98  bmc1_merge_next_fun:                    0
% 3.51/0.98  bmc1_unsat_core_clauses_time:           0.
% 3.51/0.98  
% 3.51/0.98  ------ Instantiation
% 3.51/0.98  
% 3.51/0.98  inst_num_of_clauses:                    761
% 3.51/0.98  inst_num_in_passive:                    256
% 3.51/0.98  inst_num_in_active:                     280
% 3.51/0.98  inst_num_in_unprocessed:                224
% 3.51/0.98  inst_num_of_loops:                      430
% 3.51/0.98  inst_num_of_learning_restarts:          0
% 3.51/0.98  inst_num_moves_active_passive:          146
% 3.51/0.98  inst_lit_activity:                      0
% 3.51/0.98  inst_lit_activity_moves:                0
% 3.51/0.98  inst_num_tautologies:                   0
% 3.51/0.98  inst_num_prop_implied:                  0
% 3.51/0.98  inst_num_existing_simplified:           0
% 3.51/0.98  inst_num_eq_res_simplified:             0
% 3.51/0.98  inst_num_child_elim:                    0
% 3.51/0.98  inst_num_of_dismatching_blockings:      404
% 3.51/0.98  inst_num_of_non_proper_insts:           694
% 3.51/0.98  inst_num_of_duplicates:                 0
% 3.51/0.98  inst_inst_num_from_inst_to_res:         0
% 3.51/0.98  inst_dismatching_checking_time:         0.
% 3.51/0.98  
% 3.51/0.98  ------ Resolution
% 3.51/0.98  
% 3.51/0.98  res_num_of_clauses:                     0
% 3.51/0.98  res_num_in_passive:                     0
% 3.51/0.98  res_num_in_active:                      0
% 3.51/0.98  res_num_of_loops:                       134
% 3.51/0.98  res_forward_subset_subsumed:            90
% 3.51/0.98  res_backward_subset_subsumed:           0
% 3.51/0.98  res_forward_subsumed:                   0
% 3.51/0.98  res_backward_subsumed:                  0
% 3.51/0.98  res_forward_subsumption_resolution:     5
% 3.51/0.98  res_backward_subsumption_resolution:    0
% 3.51/0.98  res_clause_to_clause_subsumption:       1003
% 3.51/0.98  res_orphan_elimination:                 0
% 3.51/0.98  res_tautology_del:                      27
% 3.51/0.98  res_num_eq_res_simplified:              0
% 3.51/0.98  res_num_sel_changes:                    0
% 3.51/0.98  res_moves_from_active_to_pass:          0
% 3.51/0.98  
% 3.51/0.98  ------ Superposition
% 3.51/0.98  
% 3.51/0.98  sup_time_total:                         0.
% 3.51/0.98  sup_time_generating:                    0.
% 3.51/0.98  sup_time_sim_full:                      0.
% 3.51/0.98  sup_time_sim_immed:                     0.
% 3.51/0.98  
% 3.51/0.98  sup_num_of_clauses:                     184
% 3.51/0.98  sup_num_in_active:                      82
% 3.51/0.98  sup_num_in_passive:                     102
% 3.51/0.98  sup_num_of_loops:                       84
% 3.51/0.98  sup_fw_superposition:                   108
% 3.51/0.98  sup_bw_superposition:                   152
% 3.51/0.98  sup_immediate_simplified:               48
% 3.51/0.98  sup_given_eliminated:                   0
% 3.51/0.98  comparisons_done:                       0
% 3.51/0.98  comparisons_avoided:                    37
% 3.51/0.98  
% 3.51/0.98  ------ Simplifications
% 3.51/0.98  
% 3.51/0.98  
% 3.51/0.98  sim_fw_subset_subsumed:                 10
% 3.51/0.98  sim_bw_subset_subsumed:                 1
% 3.51/0.98  sim_fw_subsumed:                        25
% 3.51/0.98  sim_bw_subsumed:                        8
% 3.51/0.98  sim_fw_subsumption_res:                 0
% 3.51/0.98  sim_bw_subsumption_res:                 0
% 3.51/0.98  sim_tautology_del:                      13
% 3.51/0.98  sim_eq_tautology_del:                   20
% 3.51/0.98  sim_eq_res_simp:                        0
% 3.51/0.98  sim_fw_demodulated:                     0
% 3.51/0.98  sim_bw_demodulated:                     0
% 3.51/0.98  sim_light_normalised:                   9
% 3.51/0.98  sim_joinable_taut:                      0
% 3.51/0.98  sim_joinable_simp:                      0
% 3.51/0.98  sim_ac_normalised:                      0
% 3.51/0.98  sim_smt_subsumption:                    0
% 3.51/0.98  
%------------------------------------------------------------------------------
