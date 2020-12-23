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
% DateTime   : Thu Dec  3 12:28:26 EST 2020

% Result     : Theorem 7.63s
% Output     : CNFRefutation 7.63s
% Verified   : 
% Statistics : Number of formulae       :  245 (3180 expanded)
%              Number of clauses        :  156 ( 786 expanded)
%              Number of leaves         :   25 ( 680 expanded)
%              Depth                    :   25
%              Number of atoms          :  896 (28168 expanded)
%              Number of equality atoms :  263 ( 972 expanded)
%              Maximal formula depth    :   14 (   5 average)
%              Maximal clause size      :   26 (   3 average)
%              Maximal term depth       :    5 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f2,axiom,(
    ! [X0,X1] :
      ( X0 = X1
    <=> ( r1_tarski(X1,X0)
        & r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f43,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(nnf_transformation,[],[f2])).

fof(f44,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(flattening,[],[f43])).

fof(f59,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | X0 != X1 ) ),
    inference(cnf_transformation,[],[f44])).

fof(f95,plain,(
    ! [X1] : r1_tarski(X1,X1) ),
    inference(equality_resolution,[],[f59])).

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

fof(f57,plain,(
    ! [X0,X1] :
      ( X0 = X1
      | r2_hidden(sK0(X0,X1),X1)
      | r2_hidden(sK0(X0,X1),X0) ) ),
    inference(cnf_transformation,[],[f42])).

fof(f7,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f45,plain,(
    ! [X0,X1] :
      ( ( m1_subset_1(X0,k1_zfmisc_1(X1))
        | ~ r1_tarski(X0,X1) )
      & ( r1_tarski(X0,X1)
        | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ) ) ),
    inference(nnf_transformation,[],[f7])).

fof(f67,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f45])).

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

fof(f68,plain,(
    ! [X2,X0,X1] :
      ( m1_subset_1(X0,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f6,axiom,(
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
    inference(ennf_transformation,[],[f6])).

fof(f24,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
      | v1_xboole_0(X1)
      | ~ m1_subset_1(X0,X1) ) ),
    inference(flattening,[],[f23])).

fof(f65,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
      | v1_xboole_0(X1)
      | ~ m1_subset_1(X0,X1) ) ),
    inference(cnf_transformation,[],[f24])).

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

fof(f52,plain,(
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
      & v4_orders_2(X0)
      & v3_orders_2(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(flattening,[],[f52])).

fof(f55,plain,(
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

fof(f54,plain,
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

fof(f56,plain,
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
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3,sK4])],[f53,f55,f54])).

fof(f89,plain,(
    ~ v1_xboole_0(sK4) ),
    inference(cnf_transformation,[],[f56])).

fof(f5,axiom,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
     => m1_subset_1(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f22,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X0,X1)
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f64,plain,(
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

fof(f80,plain,(
    ! [X0,X1] :
      ( k1_yellow_0(X0,k5_waybel_0(X0,X1)) = X1
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | ~ v5_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f36])).

fof(f86,plain,(
    v5_orders_2(sK3) ),
    inference(cnf_transformation,[],[f56])).

fof(f83,plain,(
    ~ v2_struct_0(sK3) ),
    inference(cnf_transformation,[],[f56])).

fof(f84,plain,(
    v3_orders_2(sK3) ),
    inference(cnf_transformation,[],[f56])).

fof(f85,plain,(
    v4_orders_2(sK3) ),
    inference(cnf_transformation,[],[f56])).

fof(f88,plain,(
    l1_orders_2(sK3) ),
    inference(cnf_transformation,[],[f56])).

fof(f91,plain,(
    m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(sK3))) ),
    inference(cnf_transformation,[],[f56])).

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

fof(f51,plain,(
    ! [X0,X1] :
      ( ( ( v1_subset_1(X1,X0)
          | X0 = X1 )
        & ( X0 != X1
          | ~ v1_subset_1(X1,X0) ) )
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(nnf_transformation,[],[f37])).

fof(f81,plain,(
    ! [X0,X1] :
      ( X0 != X1
      | ~ v1_subset_1(X1,X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f51])).

fof(f96,plain,(
    ! [X1] :
      ( ~ v1_subset_1(X1,X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X1)) ) ),
    inference(equality_resolution,[],[f81])).

fof(f92,plain,
    ( ~ r2_hidden(k3_yellow_0(sK3),sK4)
    | v1_subset_1(sK4,u1_struct_0(sK3)) ),
    inference(cnf_transformation,[],[f56])).

fof(f66,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ) ),
    inference(cnf_transformation,[],[f45])).

fof(f61,plain,(
    ! [X0,X1] :
      ( X0 = X1
      | ~ r1_tarski(X1,X0)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f44])).

fof(f4,axiom,(
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
    inference(ennf_transformation,[],[f4])).

fof(f63,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(X2,X0)
      | ~ r2_hidden(X2,X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f58,plain,(
    ! [X0,X1] :
      ( X0 = X1
      | ~ r2_hidden(sK0(X0,X1),X1)
      | ~ r2_hidden(sK0(X0,X1),X0) ) ),
    inference(cnf_transformation,[],[f42])).

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

fof(f69,plain,(
    ! [X0] :
      ( k3_yellow_0(X0) = k1_yellow_0(X0,k1_xboole_0)
      | ~ l1_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f10,axiom,(
    ! [X0,X1] :
      ( l1_orders_2(X0)
     => m1_subset_1(k1_yellow_0(X0,X1),u1_struct_0(X0)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f28,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k1_yellow_0(X0,X1),u1_struct_0(X0))
      | ~ l1_orders_2(X0) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f70,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k1_yellow_0(X0,X1),u1_struct_0(X0))
      | ~ l1_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f28])).

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

fof(f71,plain,(
    ! [X2,X0,X1] :
      ( r1_orders_2(X0,k1_yellow_0(X0,X1),k1_yellow_0(X0,X2))
      | ~ r1_yellow_0(X0,X2)
      | ~ r1_yellow_0(X0,X1)
      | ~ r1_tarski(X1,X2)
      | ~ l1_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f79,plain,(
    ! [X0,X1] :
      ( r1_yellow_0(X0,k5_waybel_0(X0,X1))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | ~ v5_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f36])).

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

fof(f46,plain,(
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
    inference(rectify,[],[f46])).

fof(f49,plain,(
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

fof(f48,plain,(
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

fof(f50,plain,(
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
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1,sK2])],[f47,f49,f48])).

fof(f73,plain,(
    ! [X4,X0,X5,X1] :
      ( r2_hidden(X5,X1)
      | ~ r1_orders_2(X0,X4,X5)
      | ~ r2_hidden(X4,X1)
      | ~ m1_subset_1(X5,u1_struct_0(X0))
      | ~ m1_subset_1(X4,u1_struct_0(X0))
      | ~ v13_waybel_0(X1,X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f50])).

fof(f90,plain,(
    v13_waybel_0(sK4,sK3) ),
    inference(cnf_transformation,[],[f56])).

fof(f82,plain,(
    ! [X0,X1] :
      ( v1_subset_1(X1,X0)
      | X0 = X1
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f51])).

fof(f93,plain,
    ( r2_hidden(k3_yellow_0(sK3),sK4)
    | ~ v1_subset_1(sK4,u1_struct_0(sK3)) ),
    inference(cnf_transformation,[],[f56])).

fof(f87,plain,(
    v1_yellow_0(sK3) ),
    inference(cnf_transformation,[],[f56])).

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

fof(f72,plain,(
    ! [X0] :
      ( r1_yellow_0(X0,k1_xboole_0)
      | ~ l1_orders_2(X0)
      | ~ v1_yellow_0(X0)
      | ~ v5_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f32])).

fof(f3,axiom,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f62,plain,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    inference(cnf_transformation,[],[f3])).

cnf(c_4,plain,
    ( r1_tarski(X0,X0) ),
    inference(cnf_transformation,[],[f95])).

cnf(c_2215,plain,
    ( r1_tarski(X0,X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_4])).

cnf(c_1,plain,
    ( r2_hidden(sK0(X0,X1),X1)
    | r2_hidden(sK0(X0,X1),X0)
    | X1 = X0 ),
    inference(cnf_transformation,[],[f57])).

cnf(c_2217,plain,
    ( X0 = X1
    | r2_hidden(sK0(X1,X0),X0) = iProver_top
    | r2_hidden(sK0(X1,X0),X1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1])).

cnf(c_9,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(X1))
    | ~ r1_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f67])).

cnf(c_2212,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(X1)) = iProver_top
    | r1_tarski(X0,X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_9])).

cnf(c_11,plain,
    ( m1_subset_1(X0,X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(X1))
    | ~ r2_hidden(X0,X2) ),
    inference(cnf_transformation,[],[f68])).

cnf(c_2210,plain,
    ( m1_subset_1(X0,X1) = iProver_top
    | m1_subset_1(X2,k1_zfmisc_1(X1)) != iProver_top
    | r2_hidden(X0,X2) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_11])).

cnf(c_3062,plain,
    ( m1_subset_1(X0,X1) = iProver_top
    | r1_tarski(X2,X1) != iProver_top
    | r2_hidden(X0,X2) != iProver_top ),
    inference(superposition,[status(thm)],[c_2212,c_2210])).

cnf(c_5473,plain,
    ( X0 = X1
    | m1_subset_1(sK0(X0,X1),X2) = iProver_top
    | r1_tarski(X0,X2) != iProver_top
    | r2_hidden(sK0(X0,X1),X1) = iProver_top ),
    inference(superposition,[status(thm)],[c_2217,c_3062])).

cnf(c_8,plain,
    ( ~ m1_subset_1(X0,X1)
    | r2_hidden(X0,X1)
    | v1_xboole_0(X1) ),
    inference(cnf_transformation,[],[f65])).

cnf(c_30,negated_conjecture,
    ( ~ v1_xboole_0(sK4) ),
    inference(cnf_transformation,[],[f89])).

cnf(c_493,plain,
    ( ~ m1_subset_1(X0,X1)
    | r2_hidden(X0,X1)
    | sK4 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_8,c_30])).

cnf(c_494,plain,
    ( ~ m1_subset_1(X0,sK4)
    | r2_hidden(X0,sK4) ),
    inference(unflattening,[status(thm)],[c_493])).

cnf(c_2206,plain,
    ( m1_subset_1(X0,sK4) != iProver_top
    | r2_hidden(X0,sK4) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_494])).

cnf(c_14986,plain,
    ( X0 = X1
    | r1_tarski(X1,sK4) != iProver_top
    | r2_hidden(sK0(X1,X0),X0) = iProver_top
    | r2_hidden(sK0(X1,X0),sK4) = iProver_top ),
    inference(superposition,[status(thm)],[c_5473,c_2206])).

cnf(c_7,plain,
    ( m1_subset_1(X0,X1)
    | ~ r2_hidden(X0,X1) ),
    inference(cnf_transformation,[],[f64])).

cnf(c_2213,plain,
    ( m1_subset_1(X0,X1) = iProver_top
    | r2_hidden(X0,X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_7])).

cnf(c_15414,plain,
    ( X0 = X1
    | m1_subset_1(sK0(X0,X1),X1) = iProver_top
    | r1_tarski(X0,sK4) != iProver_top
    | r2_hidden(sK0(X0,X1),sK4) = iProver_top ),
    inference(superposition,[status(thm)],[c_14986,c_2213])).

cnf(c_22,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(X1))
    | ~ v3_orders_2(X1)
    | ~ v4_orders_2(X1)
    | v2_struct_0(X1)
    | ~ v5_orders_2(X1)
    | ~ l1_orders_2(X1)
    | k1_yellow_0(X1,k5_waybel_0(X1,X0)) = X0 ),
    inference(cnf_transformation,[],[f80])).

cnf(c_33,negated_conjecture,
    ( v5_orders_2(sK3) ),
    inference(cnf_transformation,[],[f86])).

cnf(c_576,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(X1))
    | ~ v3_orders_2(X1)
    | ~ v4_orders_2(X1)
    | v2_struct_0(X1)
    | ~ l1_orders_2(X1)
    | k1_yellow_0(X1,k5_waybel_0(X1,X0)) = X0
    | sK3 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_22,c_33])).

cnf(c_577,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(sK3))
    | ~ v3_orders_2(sK3)
    | ~ v4_orders_2(sK3)
    | v2_struct_0(sK3)
    | ~ l1_orders_2(sK3)
    | k1_yellow_0(sK3,k5_waybel_0(sK3,X0)) = X0 ),
    inference(unflattening,[status(thm)],[c_576])).

cnf(c_36,negated_conjecture,
    ( ~ v2_struct_0(sK3) ),
    inference(cnf_transformation,[],[f83])).

cnf(c_35,negated_conjecture,
    ( v3_orders_2(sK3) ),
    inference(cnf_transformation,[],[f84])).

cnf(c_34,negated_conjecture,
    ( v4_orders_2(sK3) ),
    inference(cnf_transformation,[],[f85])).

cnf(c_31,negated_conjecture,
    ( l1_orders_2(sK3) ),
    inference(cnf_transformation,[],[f88])).

cnf(c_581,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(sK3))
    | k1_yellow_0(sK3,k5_waybel_0(sK3,X0)) = X0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_577,c_36,c_35,c_34,c_31])).

cnf(c_2201,plain,
    ( k1_yellow_0(sK3,k5_waybel_0(sK3,X0)) = X0
    | m1_subset_1(X0,u1_struct_0(sK3)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_581])).

cnf(c_16602,plain,
    ( k1_yellow_0(sK3,k5_waybel_0(sK3,sK0(X0,u1_struct_0(sK3)))) = sK0(X0,u1_struct_0(sK3))
    | u1_struct_0(sK3) = X0
    | r1_tarski(X0,sK4) != iProver_top
    | r2_hidden(sK0(X0,u1_struct_0(sK3)),sK4) = iProver_top ),
    inference(superposition,[status(thm)],[c_15414,c_2201])).

cnf(c_28,negated_conjecture,
    ( m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(sK3))) ),
    inference(cnf_transformation,[],[f91])).

cnf(c_45,plain,
    ( m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(sK3))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_28])).

cnf(c_25,plain,
    ( ~ v1_subset_1(X0,X0)
    | ~ m1_subset_1(X0,k1_zfmisc_1(X0)) ),
    inference(cnf_transformation,[],[f96])).

cnf(c_27,negated_conjecture,
    ( v1_subset_1(sK4,u1_struct_0(sK3))
    | ~ r2_hidden(k3_yellow_0(sK3),sK4) ),
    inference(cnf_transformation,[],[f92])).

cnf(c_279,plain,
    ( v1_subset_1(sK4,u1_struct_0(sK3))
    | ~ r2_hidden(k3_yellow_0(sK3),sK4) ),
    inference(prop_impl,[status(thm)],[c_27])).

cnf(c_537,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X0))
    | ~ r2_hidden(k3_yellow_0(sK3),sK4)
    | u1_struct_0(sK3) != X0
    | sK4 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_25,c_279])).

cnf(c_538,plain,
    ( ~ m1_subset_1(u1_struct_0(sK3),k1_zfmisc_1(u1_struct_0(sK3)))
    | ~ r2_hidden(k3_yellow_0(sK3),sK4)
    | sK4 != u1_struct_0(sK3) ),
    inference(unflattening,[status(thm)],[c_537])).

cnf(c_539,plain,
    ( sK4 != u1_struct_0(sK3)
    | m1_subset_1(u1_struct_0(sK3),k1_zfmisc_1(u1_struct_0(sK3))) != iProver_top
    | r2_hidden(k3_yellow_0(sK3),sK4) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_538])).

cnf(c_10,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | r1_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f66])).

cnf(c_2438,plain,
    ( ~ m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(sK3)))
    | r1_tarski(sK4,u1_struct_0(sK3)) ),
    inference(instantiation,[status(thm)],[c_10])).

cnf(c_2439,plain,
    ( m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(sK3))) != iProver_top
    | r1_tarski(sK4,u1_struct_0(sK3)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2438])).

cnf(c_1542,plain,
    ( X0 = X0 ),
    theory(equality)).

cnf(c_2506,plain,
    ( sK4 = sK4 ),
    inference(instantiation,[status(thm)],[c_1542])).

cnf(c_2433,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK3)))
    | ~ r1_tarski(X0,u1_struct_0(sK3)) ),
    inference(instantiation,[status(thm)],[c_9])).

cnf(c_2526,plain,
    ( m1_subset_1(u1_struct_0(sK3),k1_zfmisc_1(u1_struct_0(sK3)))
    | ~ r1_tarski(u1_struct_0(sK3),u1_struct_0(sK3)) ),
    inference(instantiation,[status(thm)],[c_2433])).

cnf(c_2528,plain,
    ( m1_subset_1(u1_struct_0(sK3),k1_zfmisc_1(u1_struct_0(sK3))) = iProver_top
    | r1_tarski(u1_struct_0(sK3),u1_struct_0(sK3)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2526])).

cnf(c_2527,plain,
    ( r1_tarski(u1_struct_0(sK3),u1_struct_0(sK3)) ),
    inference(instantiation,[status(thm)],[c_4])).

cnf(c_2530,plain,
    ( r1_tarski(u1_struct_0(sK3),u1_struct_0(sK3)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2527])).

cnf(c_2,plain,
    ( ~ r1_tarski(X0,X1)
    | ~ r1_tarski(X1,X0)
    | X0 = X1 ),
    inference(cnf_transformation,[],[f61])).

cnf(c_2579,plain,
    ( ~ r1_tarski(X0,u1_struct_0(sK3))
    | ~ r1_tarski(u1_struct_0(sK3),X0)
    | X0 = u1_struct_0(sK3) ),
    inference(instantiation,[status(thm)],[c_2])).

cnf(c_3362,plain,
    ( ~ r1_tarski(u1_struct_0(sK3),sK4)
    | ~ r1_tarski(sK4,u1_struct_0(sK3))
    | sK4 = u1_struct_0(sK3) ),
    inference(instantiation,[status(thm)],[c_2579])).

cnf(c_3363,plain,
    ( sK4 = u1_struct_0(sK3)
    | r1_tarski(u1_struct_0(sK3),sK4) != iProver_top
    | r1_tarski(sK4,u1_struct_0(sK3)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3362])).

cnf(c_2209,plain,
    ( m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(sK3))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_28])).

cnf(c_2211,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(X1)) != iProver_top
    | r1_tarski(X0,X1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_10])).

cnf(c_2758,plain,
    ( r1_tarski(sK4,u1_struct_0(sK3)) = iProver_top ),
    inference(superposition,[status(thm)],[c_2209,c_2211])).

cnf(c_6,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | ~ r2_hidden(X2,X0)
    | r2_hidden(X2,X1) ),
    inference(cnf_transformation,[],[f63])).

cnf(c_277,plain,
    ( ~ r1_tarski(X0,X1)
    | m1_subset_1(X0,k1_zfmisc_1(X1)) ),
    inference(prop_impl,[status(thm)],[c_9])).

cnf(c_278,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(X1))
    | ~ r1_tarski(X0,X1) ),
    inference(renaming,[status(thm)],[c_277])).

cnf(c_358,plain,
    ( ~ r1_tarski(X0,X1)
    | ~ r2_hidden(X2,X0)
    | r2_hidden(X2,X1) ),
    inference(bin_hyper_res,[status(thm)],[c_6,c_278])).

cnf(c_2207,plain,
    ( r1_tarski(X0,X1) != iProver_top
    | r2_hidden(X2,X0) != iProver_top
    | r2_hidden(X2,X1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_358])).

cnf(c_3779,plain,
    ( r2_hidden(X0,u1_struct_0(sK3)) = iProver_top
    | r2_hidden(X0,sK4) != iProver_top ),
    inference(superposition,[status(thm)],[c_2758,c_2207])).

cnf(c_0,plain,
    ( ~ r2_hidden(sK0(X0,X1),X1)
    | ~ r2_hidden(sK0(X0,X1),X0)
    | X1 = X0 ),
    inference(cnf_transformation,[],[f58])).

cnf(c_2218,plain,
    ( X0 = X1
    | r2_hidden(sK0(X1,X0),X0) != iProver_top
    | r2_hidden(sK0(X1,X0),X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_0])).

cnf(c_3899,plain,
    ( u1_struct_0(sK3) = X0
    | r2_hidden(sK0(X0,u1_struct_0(sK3)),X0) != iProver_top
    | r2_hidden(sK0(X0,u1_struct_0(sK3)),sK4) != iProver_top ),
    inference(superposition,[status(thm)],[c_3779,c_2218])).

cnf(c_3041,plain,
    ( X0 = X1
    | m1_subset_1(sK0(X0,X1),X1) = iProver_top
    | r2_hidden(sK0(X0,X1),X0) = iProver_top ),
    inference(superposition,[status(thm)],[c_2217,c_2213])).

cnf(c_4892,plain,
    ( k1_yellow_0(sK3,k5_waybel_0(sK3,sK0(X0,u1_struct_0(sK3)))) = sK0(X0,u1_struct_0(sK3))
    | u1_struct_0(sK3) = X0
    | r2_hidden(sK0(X0,u1_struct_0(sK3)),X0) = iProver_top ),
    inference(superposition,[status(thm)],[c_3041,c_2201])).

cnf(c_12,plain,
    ( ~ l1_orders_2(X0)
    | k1_yellow_0(X0,k1_xboole_0) = k3_yellow_0(X0) ),
    inference(cnf_transformation,[],[f69])).

cnf(c_745,plain,
    ( k1_yellow_0(X0,k1_xboole_0) = k3_yellow_0(X0)
    | sK3 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_12,c_31])).

cnf(c_746,plain,
    ( k1_yellow_0(sK3,k1_xboole_0) = k3_yellow_0(sK3) ),
    inference(unflattening,[status(thm)],[c_745])).

cnf(c_13,plain,
    ( m1_subset_1(k1_yellow_0(X0,X1),u1_struct_0(X0))
    | ~ l1_orders_2(X0) ),
    inference(cnf_transformation,[],[f70])).

cnf(c_736,plain,
    ( m1_subset_1(k1_yellow_0(X0,X1),u1_struct_0(X0))
    | sK3 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_13,c_31])).

cnf(c_737,plain,
    ( m1_subset_1(k1_yellow_0(sK3,X0),u1_struct_0(sK3)) ),
    inference(unflattening,[status(thm)],[c_736])).

cnf(c_2197,plain,
    ( m1_subset_1(k1_yellow_0(sK3,X0),u1_struct_0(sK3)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_737])).

cnf(c_2447,plain,
    ( m1_subset_1(k3_yellow_0(sK3),u1_struct_0(sK3)) = iProver_top ),
    inference(superposition,[status(thm)],[c_746,c_2197])).

cnf(c_2479,plain,
    ( k1_yellow_0(sK3,k5_waybel_0(sK3,k3_yellow_0(sK3))) = k3_yellow_0(sK3) ),
    inference(superposition,[status(thm)],[c_2447,c_2201])).

cnf(c_2478,plain,
    ( k1_yellow_0(sK3,k5_waybel_0(sK3,k1_yellow_0(sK3,X0))) = k1_yellow_0(sK3,X0) ),
    inference(superposition,[status(thm)],[c_2197,c_2201])).

cnf(c_14,plain,
    ( r1_orders_2(X0,k1_yellow_0(X0,X1),k1_yellow_0(X0,X2))
    | ~ r1_yellow_0(X0,X2)
    | ~ r1_yellow_0(X0,X1)
    | ~ r1_tarski(X1,X2)
    | ~ l1_orders_2(X0) ),
    inference(cnf_transformation,[],[f71])).

cnf(c_718,plain,
    ( r1_orders_2(X0,k1_yellow_0(X0,X1),k1_yellow_0(X0,X2))
    | ~ r1_yellow_0(X0,X2)
    | ~ r1_yellow_0(X0,X1)
    | ~ r1_tarski(X1,X2)
    | sK3 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_14,c_31])).

cnf(c_719,plain,
    ( r1_orders_2(sK3,k1_yellow_0(sK3,X0),k1_yellow_0(sK3,X1))
    | ~ r1_yellow_0(sK3,X0)
    | ~ r1_yellow_0(sK3,X1)
    | ~ r1_tarski(X0,X1) ),
    inference(unflattening,[status(thm)],[c_718])).

cnf(c_2198,plain,
    ( r1_orders_2(sK3,k1_yellow_0(sK3,X0),k1_yellow_0(sK3,X1)) = iProver_top
    | r1_yellow_0(sK3,X0) != iProver_top
    | r1_yellow_0(sK3,X1) != iProver_top
    | r1_tarski(X0,X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_719])).

cnf(c_3266,plain,
    ( r1_orders_2(sK3,k1_yellow_0(sK3,X0),k1_yellow_0(sK3,X1)) = iProver_top
    | r1_yellow_0(sK3,X1) != iProver_top
    | r1_yellow_0(sK3,k5_waybel_0(sK3,k1_yellow_0(sK3,X0))) != iProver_top
    | r1_tarski(k5_waybel_0(sK3,k1_yellow_0(sK3,X0)),X1) != iProver_top ),
    inference(superposition,[status(thm)],[c_2478,c_2198])).

cnf(c_738,plain,
    ( m1_subset_1(k1_yellow_0(sK3,X0),u1_struct_0(sK3)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_737])).

cnf(c_23,plain,
    ( r1_yellow_0(X0,k5_waybel_0(X0,X1))
    | ~ m1_subset_1(X1,u1_struct_0(X0))
    | ~ v3_orders_2(X0)
    | ~ v4_orders_2(X0)
    | v2_struct_0(X0)
    | ~ v5_orders_2(X0)
    | ~ l1_orders_2(X0) ),
    inference(cnf_transformation,[],[f79])).

cnf(c_558,plain,
    ( r1_yellow_0(X0,k5_waybel_0(X0,X1))
    | ~ m1_subset_1(X1,u1_struct_0(X0))
    | ~ v3_orders_2(X0)
    | ~ v4_orders_2(X0)
    | v2_struct_0(X0)
    | ~ l1_orders_2(X0)
    | sK3 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_23,c_33])).

cnf(c_559,plain,
    ( r1_yellow_0(sK3,k5_waybel_0(sK3,X0))
    | ~ m1_subset_1(X0,u1_struct_0(sK3))
    | ~ v3_orders_2(sK3)
    | ~ v4_orders_2(sK3)
    | v2_struct_0(sK3)
    | ~ l1_orders_2(sK3) ),
    inference(unflattening,[status(thm)],[c_558])).

cnf(c_563,plain,
    ( r1_yellow_0(sK3,k5_waybel_0(sK3,X0))
    | ~ m1_subset_1(X0,u1_struct_0(sK3)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_559,c_36,c_35,c_34,c_31])).

cnf(c_2407,plain,
    ( r1_yellow_0(sK3,k5_waybel_0(sK3,k1_yellow_0(sK3,X0)))
    | ~ m1_subset_1(k1_yellow_0(sK3,X0),u1_struct_0(sK3)) ),
    inference(instantiation,[status(thm)],[c_563])).

cnf(c_2408,plain,
    ( r1_yellow_0(sK3,k5_waybel_0(sK3,k1_yellow_0(sK3,X0))) = iProver_top
    | m1_subset_1(k1_yellow_0(sK3,X0),u1_struct_0(sK3)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2407])).

cnf(c_4312,plain,
    ( r1_yellow_0(sK3,X1) != iProver_top
    | r1_orders_2(sK3,k1_yellow_0(sK3,X0),k1_yellow_0(sK3,X1)) = iProver_top
    | r1_tarski(k5_waybel_0(sK3,k1_yellow_0(sK3,X0)),X1) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_3266,c_738,c_2408])).

cnf(c_4313,plain,
    ( r1_orders_2(sK3,k1_yellow_0(sK3,X0),k1_yellow_0(sK3,X1)) = iProver_top
    | r1_yellow_0(sK3,X1) != iProver_top
    | r1_tarski(k5_waybel_0(sK3,k1_yellow_0(sK3,X0)),X1) != iProver_top ),
    inference(renaming,[status(thm)],[c_4312])).

cnf(c_21,plain,
    ( ~ r1_orders_2(X0,X1,X2)
    | ~ v13_waybel_0(X3,X0)
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | ~ m1_subset_1(X1,u1_struct_0(X0))
    | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))
    | ~ r2_hidden(X1,X3)
    | r2_hidden(X2,X3)
    | ~ l1_orders_2(X0) ),
    inference(cnf_transformation,[],[f73])).

cnf(c_678,plain,
    ( ~ r1_orders_2(X0,X1,X2)
    | ~ v13_waybel_0(X3,X0)
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | ~ m1_subset_1(X1,u1_struct_0(X0))
    | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))
    | ~ r2_hidden(X1,X3)
    | r2_hidden(X2,X3)
    | sK3 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_21,c_31])).

cnf(c_679,plain,
    ( ~ r1_orders_2(sK3,X0,X1)
    | ~ v13_waybel_0(X2,sK3)
    | ~ m1_subset_1(X0,u1_struct_0(sK3))
    | ~ m1_subset_1(X1,u1_struct_0(sK3))
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK3)))
    | ~ r2_hidden(X0,X2)
    | r2_hidden(X1,X2) ),
    inference(unflattening,[status(thm)],[c_678])).

cnf(c_695,plain,
    ( ~ r1_orders_2(sK3,X0,X1)
    | ~ v13_waybel_0(X2,sK3)
    | ~ m1_subset_1(X1,u1_struct_0(sK3))
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK3)))
    | ~ r2_hidden(X0,X2)
    | r2_hidden(X1,X2) ),
    inference(forward_subsumption_resolution,[status(thm)],[c_679,c_11])).

cnf(c_2200,plain,
    ( r1_orders_2(sK3,X0,X1) != iProver_top
    | v13_waybel_0(X2,sK3) != iProver_top
    | m1_subset_1(X1,u1_struct_0(sK3)) != iProver_top
    | m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK3))) != iProver_top
    | r2_hidden(X0,X2) != iProver_top
    | r2_hidden(X1,X2) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_695])).

cnf(c_3627,plain,
    ( r1_orders_2(sK3,X0,X1) != iProver_top
    | v13_waybel_0(sK4,sK3) != iProver_top
    | m1_subset_1(X1,u1_struct_0(sK3)) != iProver_top
    | r2_hidden(X0,sK4) != iProver_top
    | r2_hidden(X1,sK4) = iProver_top ),
    inference(superposition,[status(thm)],[c_2209,c_2200])).

cnf(c_29,negated_conjecture,
    ( v13_waybel_0(sK4,sK3) ),
    inference(cnf_transformation,[],[f90])).

cnf(c_911,plain,
    ( ~ r1_orders_2(sK3,X0,X1)
    | ~ m1_subset_1(X1,u1_struct_0(sK3))
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK3)))
    | ~ r2_hidden(X0,X2)
    | r2_hidden(X1,X2)
    | sK4 != X2
    | sK3 != sK3 ),
    inference(resolution_lifted,[status(thm)],[c_29,c_695])).

cnf(c_912,plain,
    ( ~ r1_orders_2(sK3,X0,X1)
    | ~ m1_subset_1(X1,u1_struct_0(sK3))
    | ~ m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(sK3)))
    | ~ r2_hidden(X0,sK4)
    | r2_hidden(X1,sK4) ),
    inference(unflattening,[status(thm)],[c_911])).

cnf(c_913,plain,
    ( r1_orders_2(sK3,X0,X1) != iProver_top
    | m1_subset_1(X1,u1_struct_0(sK3)) != iProver_top
    | m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(sK3))) != iProver_top
    | r2_hidden(X0,sK4) != iProver_top
    | r2_hidden(X1,sK4) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_912])).

cnf(c_3834,plain,
    ( r1_orders_2(sK3,X0,X1) != iProver_top
    | m1_subset_1(X1,u1_struct_0(sK3)) != iProver_top
    | r2_hidden(X0,sK4) != iProver_top
    | r2_hidden(X1,sK4) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_3627,c_45,c_913])).

cnf(c_4327,plain,
    ( r1_yellow_0(sK3,X0) != iProver_top
    | m1_subset_1(k1_yellow_0(sK3,X0),u1_struct_0(sK3)) != iProver_top
    | r1_tarski(k5_waybel_0(sK3,k1_yellow_0(sK3,X1)),X0) != iProver_top
    | r2_hidden(k1_yellow_0(sK3,X1),sK4) != iProver_top
    | r2_hidden(k1_yellow_0(sK3,X0),sK4) = iProver_top ),
    inference(superposition,[status(thm)],[c_4313,c_3834])).

cnf(c_24,plain,
    ( v1_subset_1(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | X0 = X1 ),
    inference(cnf_transformation,[],[f82])).

cnf(c_361,plain,
    ( v1_subset_1(X0,X1)
    | ~ r1_tarski(X0,X1)
    | X0 = X1 ),
    inference(bin_hyper_res,[status(thm)],[c_24,c_278])).

cnf(c_26,negated_conjecture,
    ( ~ v1_subset_1(sK4,u1_struct_0(sK3))
    | r2_hidden(k3_yellow_0(sK3),sK4) ),
    inference(cnf_transformation,[],[f93])).

cnf(c_281,plain,
    ( ~ v1_subset_1(sK4,u1_struct_0(sK3))
    | r2_hidden(k3_yellow_0(sK3),sK4) ),
    inference(prop_impl,[status(thm)],[c_26])).

cnf(c_524,plain,
    ( ~ r1_tarski(X0,X1)
    | r2_hidden(k3_yellow_0(sK3),sK4)
    | X1 = X0
    | u1_struct_0(sK3) != X1
    | sK4 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_361,c_281])).

cnf(c_525,plain,
    ( ~ r1_tarski(sK4,u1_struct_0(sK3))
    | r2_hidden(k3_yellow_0(sK3),sK4)
    | u1_struct_0(sK3) = sK4 ),
    inference(unflattening,[status(thm)],[c_524])).

cnf(c_526,plain,
    ( u1_struct_0(sK3) = sK4
    | r1_tarski(sK4,u1_struct_0(sK3)) != iProver_top
    | r2_hidden(k3_yellow_0(sK3),sK4) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_525])).

cnf(c_2778,plain,
    ( k1_yellow_0(sK3,X0) = k1_yellow_0(sK3,X0) ),
    inference(instantiation,[status(thm)],[c_1542])).

cnf(c_1547,plain,
    ( ~ m1_subset_1(X0,X1)
    | m1_subset_1(X2,X3)
    | X2 != X0
    | X3 != X1 ),
    theory(equality)).

cnf(c_2457,plain,
    ( m1_subset_1(X0,X1)
    | ~ m1_subset_1(k1_yellow_0(sK3,X2),u1_struct_0(sK3))
    | X0 != k1_yellow_0(sK3,X2)
    | X1 != u1_struct_0(sK3) ),
    inference(instantiation,[status(thm)],[c_1547])).

cnf(c_2777,plain,
    ( m1_subset_1(k1_yellow_0(sK3,X0),X1)
    | ~ m1_subset_1(k1_yellow_0(sK3,X0),u1_struct_0(sK3))
    | X1 != u1_struct_0(sK3)
    | k1_yellow_0(sK3,X0) != k1_yellow_0(sK3,X0) ),
    inference(instantiation,[status(thm)],[c_2457])).

cnf(c_3139,plain,
    ( ~ m1_subset_1(k1_yellow_0(sK3,X0),u1_struct_0(sK3))
    | m1_subset_1(k1_yellow_0(sK3,X0),sK4)
    | k1_yellow_0(sK3,X0) != k1_yellow_0(sK3,X0)
    | sK4 != u1_struct_0(sK3) ),
    inference(instantiation,[status(thm)],[c_2777])).

cnf(c_3141,plain,
    ( k1_yellow_0(sK3,X0) != k1_yellow_0(sK3,X0)
    | sK4 != u1_struct_0(sK3)
    | m1_subset_1(k1_yellow_0(sK3,X0),u1_struct_0(sK3)) != iProver_top
    | m1_subset_1(k1_yellow_0(sK3,X0),sK4) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3139])).

cnf(c_3140,plain,
    ( ~ m1_subset_1(k1_yellow_0(sK3,X0),sK4)
    | r2_hidden(k1_yellow_0(sK3,X0),sK4) ),
    inference(instantiation,[status(thm)],[c_494])).

cnf(c_3145,plain,
    ( m1_subset_1(k1_yellow_0(sK3,X0),sK4) != iProver_top
    | r2_hidden(k1_yellow_0(sK3,X0),sK4) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3140])).

cnf(c_2822,plain,
    ( r1_orders_2(sK3,k3_yellow_0(sK3),k1_yellow_0(sK3,X0)) = iProver_top
    | r1_yellow_0(sK3,X0) != iProver_top
    | r1_yellow_0(sK3,k1_xboole_0) != iProver_top
    | r1_tarski(k1_xboole_0,X0) != iProver_top ),
    inference(superposition,[status(thm)],[c_746,c_2198])).

cnf(c_37,plain,
    ( v2_struct_0(sK3) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_36])).

cnf(c_40,plain,
    ( v5_orders_2(sK3) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_33])).

cnf(c_32,negated_conjecture,
    ( v1_yellow_0(sK3) ),
    inference(cnf_transformation,[],[f87])).

cnf(c_41,plain,
    ( v1_yellow_0(sK3) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_32])).

cnf(c_42,plain,
    ( l1_orders_2(sK3) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_31])).

cnf(c_15,plain,
    ( r1_yellow_0(X0,k1_xboole_0)
    | v2_struct_0(X0)
    | ~ v5_orders_2(X0)
    | ~ v1_yellow_0(X0)
    | ~ l1_orders_2(X0) ),
    inference(cnf_transformation,[],[f72])).

cnf(c_76,plain,
    ( r1_yellow_0(X0,k1_xboole_0) = iProver_top
    | v2_struct_0(X0) = iProver_top
    | v5_orders_2(X0) != iProver_top
    | v1_yellow_0(X0) != iProver_top
    | l1_orders_2(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_15])).

cnf(c_78,plain,
    ( r1_yellow_0(sK3,k1_xboole_0) = iProver_top
    | v2_struct_0(sK3) = iProver_top
    | v5_orders_2(sK3) != iProver_top
    | v1_yellow_0(sK3) != iProver_top
    | l1_orders_2(sK3) != iProver_top ),
    inference(instantiation,[status(thm)],[c_76])).

cnf(c_5,plain,
    ( r1_tarski(k1_xboole_0,X0) ),
    inference(cnf_transformation,[],[f62])).

cnf(c_104,plain,
    ( r1_tarski(k1_xboole_0,X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_5])).

cnf(c_2922,plain,
    ( r1_orders_2(sK3,k3_yellow_0(sK3),k1_yellow_0(sK3,X0)) = iProver_top
    | r1_yellow_0(sK3,X0) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_2822,c_37,c_40,c_41,c_42,c_78,c_104])).

cnf(c_3265,plain,
    ( r1_orders_2(sK3,k3_yellow_0(sK3),k1_yellow_0(sK3,X0)) = iProver_top
    | r1_yellow_0(sK3,k5_waybel_0(sK3,k1_yellow_0(sK3,X0))) != iProver_top ),
    inference(superposition,[status(thm)],[c_2478,c_2922])).

cnf(c_3514,plain,
    ( r1_orders_2(sK3,k3_yellow_0(sK3),k1_yellow_0(sK3,X0)) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_3265,c_738,c_2408])).

cnf(c_3844,plain,
    ( m1_subset_1(k1_yellow_0(sK3,X0),u1_struct_0(sK3)) != iProver_top
    | r2_hidden(k1_yellow_0(sK3,X0),sK4) = iProver_top
    | r2_hidden(k3_yellow_0(sK3),sK4) != iProver_top ),
    inference(superposition,[status(thm)],[c_3514,c_3834])).

cnf(c_3944,plain,
    ( r2_hidden(k1_yellow_0(sK3,X0),sK4) = iProver_top
    | r2_hidden(k3_yellow_0(sK3),sK4) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_3844,c_738])).

cnf(c_1543,plain,
    ( X0 != X1
    | X2 != X1
    | X2 = X0 ),
    theory(equality)).

cnf(c_2600,plain,
    ( X0 != X1
    | X0 = u1_struct_0(sK3)
    | u1_struct_0(sK3) != X1 ),
    inference(instantiation,[status(thm)],[c_1543])).

cnf(c_3359,plain,
    ( u1_struct_0(sK3) != X0
    | sK4 != X0
    | sK4 = u1_struct_0(sK3) ),
    inference(instantiation,[status(thm)],[c_2600])).

cnf(c_4807,plain,
    ( u1_struct_0(sK3) != sK4
    | sK4 = u1_struct_0(sK3)
    | sK4 != sK4 ),
    inference(instantiation,[status(thm)],[c_3359])).

cnf(c_4982,plain,
    ( r2_hidden(k1_yellow_0(sK3,X0),sK4) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_4327,c_45,c_526,c_738,c_2439,c_2506,c_2778,c_3141,c_3145,c_3944,c_4807])).

cnf(c_4991,plain,
    ( r2_hidden(k3_yellow_0(sK3),sK4) = iProver_top ),
    inference(superposition,[status(thm)],[c_2479,c_4982])).

cnf(c_1545,plain,
    ( ~ r1_tarski(X0,X1)
    | r1_tarski(X2,X3)
    | X2 != X0
    | X3 != X1 ),
    theory(equality)).

cnf(c_4385,plain,
    ( ~ r1_tarski(X0,X1)
    | r1_tarski(X2,sK4)
    | X2 != X0
    | sK4 != X1 ),
    inference(instantiation,[status(thm)],[c_1545])).

cnf(c_6513,plain,
    ( ~ r1_tarski(X0,X1)
    | r1_tarski(u1_struct_0(sK3),sK4)
    | u1_struct_0(sK3) != X0
    | sK4 != X1 ),
    inference(instantiation,[status(thm)],[c_4385])).

cnf(c_16220,plain,
    ( ~ r1_tarski(X0,sK4)
    | r1_tarski(u1_struct_0(sK3),sK4)
    | u1_struct_0(sK3) != X0
    | sK4 != sK4 ),
    inference(instantiation,[status(thm)],[c_6513])).

cnf(c_16221,plain,
    ( u1_struct_0(sK3) != X0
    | sK4 != sK4
    | r1_tarski(X0,sK4) != iProver_top
    | r1_tarski(u1_struct_0(sK3),sK4) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_16220])).

cnf(c_17388,plain,
    ( r1_tarski(X0,sK4) != iProver_top
    | k1_yellow_0(sK3,k5_waybel_0(sK3,sK0(X0,u1_struct_0(sK3)))) = sK0(X0,u1_struct_0(sK3)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_16602,c_45,c_539,c_2439,c_2506,c_2528,c_2530,c_3363,c_3899,c_4892,c_4991,c_16221])).

cnf(c_17389,plain,
    ( k1_yellow_0(sK3,k5_waybel_0(sK3,sK0(X0,u1_struct_0(sK3)))) = sK0(X0,u1_struct_0(sK3))
    | r1_tarski(X0,sK4) != iProver_top ),
    inference(renaming,[status(thm)],[c_17388])).

cnf(c_17396,plain,
    ( k1_yellow_0(sK3,k5_waybel_0(sK3,sK0(sK4,u1_struct_0(sK3)))) = sK0(sK4,u1_struct_0(sK3)) ),
    inference(superposition,[status(thm)],[c_2215,c_17389])).

cnf(c_19618,plain,
    ( r2_hidden(sK0(sK4,u1_struct_0(sK3)),sK4) = iProver_top ),
    inference(superposition,[status(thm)],[c_17396,c_4982])).

cnf(c_15413,plain,
    ( u1_struct_0(sK3) = sK4
    | r1_tarski(sK4,sK4) != iProver_top
    | r2_hidden(sK0(sK4,u1_struct_0(sK3)),u1_struct_0(sK3)) = iProver_top
    | r2_hidden(sK0(sK4,u1_struct_0(sK3)),sK4) != iProver_top ),
    inference(superposition,[status(thm)],[c_14986,c_3899])).

cnf(c_15475,plain,
    ( u1_struct_0(sK3) = sK4
    | r1_tarski(sK4,sK4) != iProver_top
    | r2_hidden(sK0(sK4,u1_struct_0(sK3)),u1_struct_0(sK3)) = iProver_top ),
    inference(forward_subsumption_resolution,[status(thm)],[c_15413,c_14986])).

cnf(c_6044,plain,
    ( r1_tarski(sK4,sK4) ),
    inference(instantiation,[status(thm)],[c_4])).

cnf(c_6049,plain,
    ( r1_tarski(sK4,sK4) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_6044])).

cnf(c_2496,plain,
    ( ~ r2_hidden(sK0(sK4,X0),X0)
    | ~ r2_hidden(sK0(sK4,X0),sK4)
    | X0 = sK4 ),
    inference(instantiation,[status(thm)],[c_0])).

cnf(c_2882,plain,
    ( ~ r2_hidden(sK0(sK4,u1_struct_0(sK3)),u1_struct_0(sK3))
    | ~ r2_hidden(sK0(sK4,u1_struct_0(sK3)),sK4)
    | u1_struct_0(sK3) = sK4 ),
    inference(instantiation,[status(thm)],[c_2496])).

cnf(c_2893,plain,
    ( u1_struct_0(sK3) = sK4
    | r2_hidden(sK0(sK4,u1_struct_0(sK3)),u1_struct_0(sK3)) != iProver_top
    | r2_hidden(sK0(sK4,u1_struct_0(sK3)),sK4) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2882])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_19618,c_15475,c_6049,c_4991,c_4807,c_2893,c_2530,c_2528,c_2506,c_539])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.08/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.08/0.13  % Command    : iproveropt_run.sh %d %s
% 0.13/0.34  % Computer   : n007.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 20:19:36 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  % Running in FOF mode
% 7.63/1.51  % SZS status Started for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 7.63/1.51  
% 7.63/1.51  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 7.63/1.51  
% 7.63/1.51  ------  iProver source info
% 7.63/1.51  
% 7.63/1.51  git: date: 2020-06-30 10:37:57 +0100
% 7.63/1.51  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 7.63/1.51  git: non_committed_changes: false
% 7.63/1.51  git: last_make_outside_of_git: false
% 7.63/1.51  
% 7.63/1.51  ------ 
% 7.63/1.51  
% 7.63/1.51  ------ Input Options
% 7.63/1.51  
% 7.63/1.51  --out_options                           all
% 7.63/1.51  --tptp_safe_out                         true
% 7.63/1.51  --problem_path                          ""
% 7.63/1.51  --include_path                          ""
% 7.63/1.51  --clausifier                            res/vclausify_rel
% 7.63/1.51  --clausifier_options                    --mode clausify
% 7.63/1.51  --stdin                                 false
% 7.63/1.51  --stats_out                             all
% 7.63/1.51  
% 7.63/1.51  ------ General Options
% 7.63/1.51  
% 7.63/1.51  --fof                                   false
% 7.63/1.51  --time_out_real                         305.
% 7.63/1.51  --time_out_virtual                      -1.
% 7.63/1.51  --symbol_type_check                     false
% 7.63/1.51  --clausify_out                          false
% 7.63/1.51  --sig_cnt_out                           false
% 7.63/1.51  --trig_cnt_out                          false
% 7.63/1.51  --trig_cnt_out_tolerance                1.
% 7.63/1.51  --trig_cnt_out_sk_spl                   false
% 7.63/1.51  --abstr_cl_out                          false
% 7.63/1.51  
% 7.63/1.51  ------ Global Options
% 7.63/1.51  
% 7.63/1.51  --schedule                              default
% 7.63/1.51  --add_important_lit                     false
% 7.63/1.51  --prop_solver_per_cl                    1000
% 7.63/1.51  --min_unsat_core                        false
% 7.63/1.51  --soft_assumptions                      false
% 7.63/1.51  --soft_lemma_size                       3
% 7.63/1.51  --prop_impl_unit_size                   0
% 7.63/1.51  --prop_impl_unit                        []
% 7.63/1.51  --share_sel_clauses                     true
% 7.63/1.51  --reset_solvers                         false
% 7.63/1.51  --bc_imp_inh                            [conj_cone]
% 7.63/1.51  --conj_cone_tolerance                   3.
% 7.63/1.51  --extra_neg_conj                        none
% 7.63/1.51  --large_theory_mode                     true
% 7.63/1.51  --prolific_symb_bound                   200
% 7.63/1.51  --lt_threshold                          2000
% 7.63/1.51  --clause_weak_htbl                      true
% 7.63/1.51  --gc_record_bc_elim                     false
% 7.63/1.51  
% 7.63/1.51  ------ Preprocessing Options
% 7.63/1.51  
% 7.63/1.51  --preprocessing_flag                    true
% 7.63/1.51  --time_out_prep_mult                    0.1
% 7.63/1.51  --splitting_mode                        input
% 7.63/1.51  --splitting_grd                         true
% 7.63/1.51  --splitting_cvd                         false
% 7.63/1.51  --splitting_cvd_svl                     false
% 7.63/1.51  --splitting_nvd                         32
% 7.63/1.51  --sub_typing                            true
% 7.63/1.51  --prep_gs_sim                           true
% 7.63/1.51  --prep_unflatten                        true
% 7.63/1.51  --prep_res_sim                          true
% 7.63/1.51  --prep_upred                            true
% 7.63/1.51  --prep_sem_filter                       exhaustive
% 7.63/1.51  --prep_sem_filter_out                   false
% 7.63/1.51  --pred_elim                             true
% 7.63/1.51  --res_sim_input                         true
% 7.63/1.51  --eq_ax_congr_red                       true
% 7.63/1.51  --pure_diseq_elim                       true
% 7.63/1.51  --brand_transform                       false
% 7.63/1.51  --non_eq_to_eq                          false
% 7.63/1.51  --prep_def_merge                        true
% 7.63/1.51  --prep_def_merge_prop_impl              false
% 7.63/1.51  --prep_def_merge_mbd                    true
% 7.63/1.51  --prep_def_merge_tr_red                 false
% 7.63/1.51  --prep_def_merge_tr_cl                  false
% 7.63/1.51  --smt_preprocessing                     true
% 7.63/1.51  --smt_ac_axioms                         fast
% 7.63/1.51  --preprocessed_out                      false
% 7.63/1.51  --preprocessed_stats                    false
% 7.63/1.51  
% 7.63/1.51  ------ Abstraction refinement Options
% 7.63/1.51  
% 7.63/1.51  --abstr_ref                             []
% 7.63/1.51  --abstr_ref_prep                        false
% 7.63/1.51  --abstr_ref_until_sat                   false
% 7.63/1.51  --abstr_ref_sig_restrict                funpre
% 7.63/1.51  --abstr_ref_af_restrict_to_split_sk     false
% 7.63/1.51  --abstr_ref_under                       []
% 7.63/1.51  
% 7.63/1.51  ------ SAT Options
% 7.63/1.51  
% 7.63/1.51  --sat_mode                              false
% 7.63/1.51  --sat_fm_restart_options                ""
% 7.63/1.51  --sat_gr_def                            false
% 7.63/1.51  --sat_epr_types                         true
% 7.63/1.51  --sat_non_cyclic_types                  false
% 7.63/1.51  --sat_finite_models                     false
% 7.63/1.51  --sat_fm_lemmas                         false
% 7.63/1.51  --sat_fm_prep                           false
% 7.63/1.51  --sat_fm_uc_incr                        true
% 7.63/1.51  --sat_out_model                         small
% 7.63/1.51  --sat_out_clauses                       false
% 7.63/1.51  
% 7.63/1.51  ------ QBF Options
% 7.63/1.51  
% 7.63/1.51  --qbf_mode                              false
% 7.63/1.51  --qbf_elim_univ                         false
% 7.63/1.51  --qbf_dom_inst                          none
% 7.63/1.51  --qbf_dom_pre_inst                      false
% 7.63/1.51  --qbf_sk_in                             false
% 7.63/1.51  --qbf_pred_elim                         true
% 7.63/1.51  --qbf_split                             512
% 7.63/1.51  
% 7.63/1.51  ------ BMC1 Options
% 7.63/1.51  
% 7.63/1.51  --bmc1_incremental                      false
% 7.63/1.51  --bmc1_axioms                           reachable_all
% 7.63/1.51  --bmc1_min_bound                        0
% 7.63/1.51  --bmc1_max_bound                        -1
% 7.63/1.51  --bmc1_max_bound_default                -1
% 7.63/1.51  --bmc1_symbol_reachability              true
% 7.63/1.51  --bmc1_property_lemmas                  false
% 7.63/1.51  --bmc1_k_induction                      false
% 7.63/1.51  --bmc1_non_equiv_states                 false
% 7.63/1.51  --bmc1_deadlock                         false
% 7.63/1.51  --bmc1_ucm                              false
% 7.63/1.51  --bmc1_add_unsat_core                   none
% 7.63/1.51  --bmc1_unsat_core_children              false
% 7.63/1.51  --bmc1_unsat_core_extrapolate_axioms    false
% 7.63/1.51  --bmc1_out_stat                         full
% 7.63/1.51  --bmc1_ground_init                      false
% 7.63/1.51  --bmc1_pre_inst_next_state              false
% 7.63/1.51  --bmc1_pre_inst_state                   false
% 7.63/1.51  --bmc1_pre_inst_reach_state             false
% 7.63/1.51  --bmc1_out_unsat_core                   false
% 7.63/1.51  --bmc1_aig_witness_out                  false
% 7.63/1.51  --bmc1_verbose                          false
% 7.63/1.51  --bmc1_dump_clauses_tptp                false
% 7.63/1.51  --bmc1_dump_unsat_core_tptp             false
% 7.63/1.51  --bmc1_dump_file                        -
% 7.63/1.51  --bmc1_ucm_expand_uc_limit              128
% 7.63/1.51  --bmc1_ucm_n_expand_iterations          6
% 7.63/1.51  --bmc1_ucm_extend_mode                  1
% 7.63/1.51  --bmc1_ucm_init_mode                    2
% 7.63/1.51  --bmc1_ucm_cone_mode                    none
% 7.63/1.51  --bmc1_ucm_reduced_relation_type        0
% 7.63/1.51  --bmc1_ucm_relax_model                  4
% 7.63/1.51  --bmc1_ucm_full_tr_after_sat            true
% 7.63/1.51  --bmc1_ucm_expand_neg_assumptions       false
% 7.63/1.51  --bmc1_ucm_layered_model                none
% 7.63/1.51  --bmc1_ucm_max_lemma_size               10
% 7.63/1.51  
% 7.63/1.51  ------ AIG Options
% 7.63/1.51  
% 7.63/1.51  --aig_mode                              false
% 7.63/1.51  
% 7.63/1.51  ------ Instantiation Options
% 7.63/1.51  
% 7.63/1.51  --instantiation_flag                    true
% 7.63/1.51  --inst_sos_flag                         false
% 7.63/1.51  --inst_sos_phase                        true
% 7.63/1.51  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 7.63/1.51  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 7.63/1.51  --inst_lit_sel_side                     num_symb
% 7.63/1.51  --inst_solver_per_active                1400
% 7.63/1.51  --inst_solver_calls_frac                1.
% 7.63/1.51  --inst_passive_queue_type               priority_queues
% 7.63/1.51  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 7.63/1.51  --inst_passive_queues_freq              [25;2]
% 7.63/1.51  --inst_dismatching                      true
% 7.63/1.51  --inst_eager_unprocessed_to_passive     true
% 7.63/1.51  --inst_prop_sim_given                   true
% 7.63/1.51  --inst_prop_sim_new                     false
% 7.63/1.51  --inst_subs_new                         false
% 7.63/1.51  --inst_eq_res_simp                      false
% 7.63/1.51  --inst_subs_given                       false
% 7.63/1.51  --inst_orphan_elimination               true
% 7.63/1.51  --inst_learning_loop_flag               true
% 7.63/1.51  --inst_learning_start                   3000
% 7.63/1.51  --inst_learning_factor                  2
% 7.63/1.51  --inst_start_prop_sim_after_learn       3
% 7.63/1.51  --inst_sel_renew                        solver
% 7.63/1.51  --inst_lit_activity_flag                true
% 7.63/1.51  --inst_restr_to_given                   false
% 7.63/1.51  --inst_activity_threshold               500
% 7.63/1.51  --inst_out_proof                        true
% 7.63/1.51  
% 7.63/1.51  ------ Resolution Options
% 7.63/1.51  
% 7.63/1.51  --resolution_flag                       true
% 7.63/1.51  --res_lit_sel                           adaptive
% 7.63/1.51  --res_lit_sel_side                      none
% 7.63/1.51  --res_ordering                          kbo
% 7.63/1.51  --res_to_prop_solver                    active
% 7.63/1.51  --res_prop_simpl_new                    false
% 7.63/1.51  --res_prop_simpl_given                  true
% 7.63/1.51  --res_passive_queue_type                priority_queues
% 7.63/1.51  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 7.63/1.51  --res_passive_queues_freq               [15;5]
% 7.63/1.51  --res_forward_subs                      full
% 7.63/1.51  --res_backward_subs                     full
% 7.63/1.51  --res_forward_subs_resolution           true
% 7.63/1.51  --res_backward_subs_resolution          true
% 7.63/1.51  --res_orphan_elimination                true
% 7.63/1.51  --res_time_limit                        2.
% 7.63/1.51  --res_out_proof                         true
% 7.63/1.51  
% 7.63/1.51  ------ Superposition Options
% 7.63/1.51  
% 7.63/1.51  --superposition_flag                    true
% 7.63/1.51  --sup_passive_queue_type                priority_queues
% 7.63/1.51  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 7.63/1.51  --sup_passive_queues_freq               [8;1;4]
% 7.63/1.51  --demod_completeness_check              fast
% 7.63/1.51  --demod_use_ground                      true
% 7.63/1.51  --sup_to_prop_solver                    passive
% 7.63/1.51  --sup_prop_simpl_new                    true
% 7.63/1.51  --sup_prop_simpl_given                  true
% 7.63/1.51  --sup_fun_splitting                     false
% 7.63/1.51  --sup_smt_interval                      50000
% 7.63/1.51  
% 7.63/1.51  ------ Superposition Simplification Setup
% 7.63/1.51  
% 7.63/1.51  --sup_indices_passive                   []
% 7.63/1.51  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 7.63/1.51  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 7.63/1.51  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 7.63/1.51  --sup_full_triv                         [TrivRules;PropSubs]
% 7.63/1.51  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 7.63/1.51  --sup_full_bw                           [BwDemod]
% 7.63/1.51  --sup_immed_triv                        [TrivRules]
% 7.63/1.51  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 7.63/1.51  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 7.63/1.51  --sup_immed_bw_main                     []
% 7.63/1.51  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 7.63/1.51  --sup_input_triv                        [Unflattening;TrivRules]
% 7.63/1.51  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 7.63/1.51  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 7.63/1.51  
% 7.63/1.51  ------ Combination Options
% 7.63/1.51  
% 7.63/1.51  --comb_res_mult                         3
% 7.63/1.51  --comb_sup_mult                         2
% 7.63/1.51  --comb_inst_mult                        10
% 7.63/1.51  
% 7.63/1.51  ------ Debug Options
% 7.63/1.51  
% 7.63/1.51  --dbg_backtrace                         false
% 7.63/1.51  --dbg_dump_prop_clauses                 false
% 7.63/1.51  --dbg_dump_prop_clauses_file            -
% 7.63/1.51  --dbg_out_stat                          false
% 7.63/1.51  ------ Parsing...
% 7.63/1.51  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 7.63/1.51  
% 7.63/1.51  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe:1:0s pe:2:0s pe:4:0s pe:8:0s pe_e  sf_s  rm: 9 0s  sf_e  pe_s  pe_e 
% 7.63/1.51  
% 7.63/1.51  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 7.63/1.51  
% 7.63/1.51  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 7.63/1.51  ------ Proving...
% 7.63/1.51  ------ Problem Properties 
% 7.63/1.51  
% 7.63/1.51  
% 7.63/1.51  clauses                                 27
% 7.63/1.51  conjectures                             2
% 7.63/1.51  EPR                                     8
% 7.63/1.51  Horn                                    21
% 7.63/1.51  unary                                   7
% 7.63/1.51  binary                                  6
% 7.63/1.51  lits                                    65
% 7.63/1.51  lits eq                                 7
% 7.63/1.51  fd_pure                                 0
% 7.63/1.51  fd_pseudo                               0
% 7.63/1.51  fd_cond                                 0
% 7.63/1.51  fd_pseudo_cond                          3
% 7.63/1.51  AC symbols                              0
% 7.63/1.51  
% 7.63/1.51  ------ Schedule dynamic 5 is on 
% 7.63/1.51  
% 7.63/1.51  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" Time Limit: 10.
% 7.63/1.51  
% 7.63/1.51  
% 7.63/1.51  ------ 
% 7.63/1.51  Current options:
% 7.63/1.51  ------ 
% 7.63/1.51  
% 7.63/1.51  ------ Input Options
% 7.63/1.51  
% 7.63/1.51  --out_options                           all
% 7.63/1.51  --tptp_safe_out                         true
% 7.63/1.51  --problem_path                          ""
% 7.63/1.51  --include_path                          ""
% 7.63/1.51  --clausifier                            res/vclausify_rel
% 7.63/1.51  --clausifier_options                    --mode clausify
% 7.63/1.51  --stdin                                 false
% 7.63/1.51  --stats_out                             all
% 7.63/1.51  
% 7.63/1.51  ------ General Options
% 7.63/1.51  
% 7.63/1.51  --fof                                   false
% 7.63/1.51  --time_out_real                         305.
% 7.63/1.51  --time_out_virtual                      -1.
% 7.63/1.51  --symbol_type_check                     false
% 7.63/1.51  --clausify_out                          false
% 7.63/1.51  --sig_cnt_out                           false
% 7.63/1.51  --trig_cnt_out                          false
% 7.63/1.51  --trig_cnt_out_tolerance                1.
% 7.63/1.51  --trig_cnt_out_sk_spl                   false
% 7.63/1.51  --abstr_cl_out                          false
% 7.63/1.51  
% 7.63/1.51  ------ Global Options
% 7.63/1.51  
% 7.63/1.51  --schedule                              default
% 7.63/1.51  --add_important_lit                     false
% 7.63/1.51  --prop_solver_per_cl                    1000
% 7.63/1.51  --min_unsat_core                        false
% 7.63/1.51  --soft_assumptions                      false
% 7.63/1.51  --soft_lemma_size                       3
% 7.63/1.51  --prop_impl_unit_size                   0
% 7.63/1.51  --prop_impl_unit                        []
% 7.63/1.51  --share_sel_clauses                     true
% 7.63/1.51  --reset_solvers                         false
% 7.63/1.51  --bc_imp_inh                            [conj_cone]
% 7.63/1.51  --conj_cone_tolerance                   3.
% 7.63/1.51  --extra_neg_conj                        none
% 7.63/1.51  --large_theory_mode                     true
% 7.63/1.51  --prolific_symb_bound                   200
% 7.63/1.51  --lt_threshold                          2000
% 7.63/1.51  --clause_weak_htbl                      true
% 7.63/1.51  --gc_record_bc_elim                     false
% 7.63/1.51  
% 7.63/1.51  ------ Preprocessing Options
% 7.63/1.51  
% 7.63/1.51  --preprocessing_flag                    true
% 7.63/1.51  --time_out_prep_mult                    0.1
% 7.63/1.51  --splitting_mode                        input
% 7.63/1.51  --splitting_grd                         true
% 7.63/1.51  --splitting_cvd                         false
% 7.63/1.51  --splitting_cvd_svl                     false
% 7.63/1.51  --splitting_nvd                         32
% 7.63/1.51  --sub_typing                            true
% 7.63/1.51  --prep_gs_sim                           true
% 7.63/1.51  --prep_unflatten                        true
% 7.63/1.51  --prep_res_sim                          true
% 7.63/1.51  --prep_upred                            true
% 7.63/1.51  --prep_sem_filter                       exhaustive
% 7.63/1.51  --prep_sem_filter_out                   false
% 7.63/1.51  --pred_elim                             true
% 7.63/1.51  --res_sim_input                         true
% 7.63/1.51  --eq_ax_congr_red                       true
% 7.63/1.51  --pure_diseq_elim                       true
% 7.63/1.51  --brand_transform                       false
% 7.63/1.51  --non_eq_to_eq                          false
% 7.63/1.51  --prep_def_merge                        true
% 7.63/1.51  --prep_def_merge_prop_impl              false
% 7.63/1.51  --prep_def_merge_mbd                    true
% 7.63/1.51  --prep_def_merge_tr_red                 false
% 7.63/1.51  --prep_def_merge_tr_cl                  false
% 7.63/1.51  --smt_preprocessing                     true
% 7.63/1.51  --smt_ac_axioms                         fast
% 7.63/1.51  --preprocessed_out                      false
% 7.63/1.51  --preprocessed_stats                    false
% 7.63/1.51  
% 7.63/1.51  ------ Abstraction refinement Options
% 7.63/1.51  
% 7.63/1.51  --abstr_ref                             []
% 7.63/1.51  --abstr_ref_prep                        false
% 7.63/1.51  --abstr_ref_until_sat                   false
% 7.63/1.51  --abstr_ref_sig_restrict                funpre
% 7.63/1.51  --abstr_ref_af_restrict_to_split_sk     false
% 7.63/1.51  --abstr_ref_under                       []
% 7.63/1.51  
% 7.63/1.51  ------ SAT Options
% 7.63/1.51  
% 7.63/1.51  --sat_mode                              false
% 7.63/1.51  --sat_fm_restart_options                ""
% 7.63/1.51  --sat_gr_def                            false
% 7.63/1.51  --sat_epr_types                         true
% 7.63/1.51  --sat_non_cyclic_types                  false
% 7.63/1.51  --sat_finite_models                     false
% 7.63/1.51  --sat_fm_lemmas                         false
% 7.63/1.51  --sat_fm_prep                           false
% 7.63/1.51  --sat_fm_uc_incr                        true
% 7.63/1.51  --sat_out_model                         small
% 7.63/1.51  --sat_out_clauses                       false
% 7.63/1.51  
% 7.63/1.51  ------ QBF Options
% 7.63/1.51  
% 7.63/1.51  --qbf_mode                              false
% 7.63/1.51  --qbf_elim_univ                         false
% 7.63/1.51  --qbf_dom_inst                          none
% 7.63/1.51  --qbf_dom_pre_inst                      false
% 7.63/1.51  --qbf_sk_in                             false
% 7.63/1.51  --qbf_pred_elim                         true
% 7.63/1.51  --qbf_split                             512
% 7.63/1.51  
% 7.63/1.51  ------ BMC1 Options
% 7.63/1.51  
% 7.63/1.51  --bmc1_incremental                      false
% 7.63/1.51  --bmc1_axioms                           reachable_all
% 7.63/1.51  --bmc1_min_bound                        0
% 7.63/1.51  --bmc1_max_bound                        -1
% 7.63/1.51  --bmc1_max_bound_default                -1
% 7.63/1.51  --bmc1_symbol_reachability              true
% 7.63/1.51  --bmc1_property_lemmas                  false
% 7.63/1.51  --bmc1_k_induction                      false
% 7.63/1.51  --bmc1_non_equiv_states                 false
% 7.63/1.51  --bmc1_deadlock                         false
% 7.63/1.51  --bmc1_ucm                              false
% 7.63/1.51  --bmc1_add_unsat_core                   none
% 7.63/1.51  --bmc1_unsat_core_children              false
% 7.63/1.51  --bmc1_unsat_core_extrapolate_axioms    false
% 7.63/1.51  --bmc1_out_stat                         full
% 7.63/1.51  --bmc1_ground_init                      false
% 7.63/1.51  --bmc1_pre_inst_next_state              false
% 7.63/1.51  --bmc1_pre_inst_state                   false
% 7.63/1.51  --bmc1_pre_inst_reach_state             false
% 7.63/1.51  --bmc1_out_unsat_core                   false
% 7.63/1.51  --bmc1_aig_witness_out                  false
% 7.63/1.51  --bmc1_verbose                          false
% 7.63/1.51  --bmc1_dump_clauses_tptp                false
% 7.63/1.51  --bmc1_dump_unsat_core_tptp             false
% 7.63/1.51  --bmc1_dump_file                        -
% 7.63/1.51  --bmc1_ucm_expand_uc_limit              128
% 7.63/1.51  --bmc1_ucm_n_expand_iterations          6
% 7.63/1.51  --bmc1_ucm_extend_mode                  1
% 7.63/1.51  --bmc1_ucm_init_mode                    2
% 7.63/1.51  --bmc1_ucm_cone_mode                    none
% 7.63/1.51  --bmc1_ucm_reduced_relation_type        0
% 7.63/1.51  --bmc1_ucm_relax_model                  4
% 7.63/1.51  --bmc1_ucm_full_tr_after_sat            true
% 7.63/1.51  --bmc1_ucm_expand_neg_assumptions       false
% 7.63/1.51  --bmc1_ucm_layered_model                none
% 7.63/1.51  --bmc1_ucm_max_lemma_size               10
% 7.63/1.51  
% 7.63/1.51  ------ AIG Options
% 7.63/1.51  
% 7.63/1.51  --aig_mode                              false
% 7.63/1.51  
% 7.63/1.51  ------ Instantiation Options
% 7.63/1.51  
% 7.63/1.51  --instantiation_flag                    true
% 7.63/1.51  --inst_sos_flag                         false
% 7.63/1.51  --inst_sos_phase                        true
% 7.63/1.51  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 7.63/1.51  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 7.63/1.51  --inst_lit_sel_side                     none
% 7.63/1.51  --inst_solver_per_active                1400
% 7.63/1.51  --inst_solver_calls_frac                1.
% 7.63/1.51  --inst_passive_queue_type               priority_queues
% 7.63/1.51  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 7.63/1.51  --inst_passive_queues_freq              [25;2]
% 7.63/1.51  --inst_dismatching                      true
% 7.63/1.51  --inst_eager_unprocessed_to_passive     true
% 7.63/1.51  --inst_prop_sim_given                   true
% 7.63/1.51  --inst_prop_sim_new                     false
% 7.63/1.51  --inst_subs_new                         false
% 7.63/1.51  --inst_eq_res_simp                      false
% 7.63/1.51  --inst_subs_given                       false
% 7.63/1.51  --inst_orphan_elimination               true
% 7.63/1.51  --inst_learning_loop_flag               true
% 7.63/1.51  --inst_learning_start                   3000
% 7.63/1.51  --inst_learning_factor                  2
% 7.63/1.51  --inst_start_prop_sim_after_learn       3
% 7.63/1.51  --inst_sel_renew                        solver
% 7.63/1.51  --inst_lit_activity_flag                true
% 7.63/1.51  --inst_restr_to_given                   false
% 7.63/1.51  --inst_activity_threshold               500
% 7.63/1.51  --inst_out_proof                        true
% 7.63/1.51  
% 7.63/1.51  ------ Resolution Options
% 7.63/1.51  
% 7.63/1.51  --resolution_flag                       false
% 7.63/1.51  --res_lit_sel                           adaptive
% 7.63/1.51  --res_lit_sel_side                      none
% 7.63/1.51  --res_ordering                          kbo
% 7.63/1.51  --res_to_prop_solver                    active
% 7.63/1.51  --res_prop_simpl_new                    false
% 7.63/1.51  --res_prop_simpl_given                  true
% 7.63/1.51  --res_passive_queue_type                priority_queues
% 7.63/1.51  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 7.63/1.51  --res_passive_queues_freq               [15;5]
% 7.63/1.51  --res_forward_subs                      full
% 7.63/1.51  --res_backward_subs                     full
% 7.63/1.51  --res_forward_subs_resolution           true
% 7.63/1.51  --res_backward_subs_resolution          true
% 7.63/1.51  --res_orphan_elimination                true
% 7.63/1.51  --res_time_limit                        2.
% 7.63/1.51  --res_out_proof                         true
% 7.63/1.51  
% 7.63/1.51  ------ Superposition Options
% 7.63/1.51  
% 7.63/1.51  --superposition_flag                    true
% 7.63/1.51  --sup_passive_queue_type                priority_queues
% 7.63/1.51  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 7.63/1.51  --sup_passive_queues_freq               [8;1;4]
% 7.63/1.51  --demod_completeness_check              fast
% 7.63/1.51  --demod_use_ground                      true
% 7.63/1.51  --sup_to_prop_solver                    passive
% 7.63/1.51  --sup_prop_simpl_new                    true
% 7.63/1.51  --sup_prop_simpl_given                  true
% 7.63/1.51  --sup_fun_splitting                     false
% 7.63/1.51  --sup_smt_interval                      50000
% 7.63/1.51  
% 7.63/1.51  ------ Superposition Simplification Setup
% 7.63/1.51  
% 7.63/1.51  --sup_indices_passive                   []
% 7.63/1.51  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 7.63/1.51  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 7.63/1.51  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 7.63/1.51  --sup_full_triv                         [TrivRules;PropSubs]
% 7.63/1.51  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 7.63/1.51  --sup_full_bw                           [BwDemod]
% 7.63/1.51  --sup_immed_triv                        [TrivRules]
% 7.63/1.51  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 7.63/1.51  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 7.63/1.51  --sup_immed_bw_main                     []
% 7.63/1.51  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 7.63/1.51  --sup_input_triv                        [Unflattening;TrivRules]
% 7.63/1.51  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 7.63/1.51  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 7.63/1.51  
% 7.63/1.51  ------ Combination Options
% 7.63/1.51  
% 7.63/1.51  --comb_res_mult                         3
% 7.63/1.51  --comb_sup_mult                         2
% 7.63/1.51  --comb_inst_mult                        10
% 7.63/1.51  
% 7.63/1.51  ------ Debug Options
% 7.63/1.51  
% 7.63/1.51  --dbg_backtrace                         false
% 7.63/1.51  --dbg_dump_prop_clauses                 false
% 7.63/1.51  --dbg_dump_prop_clauses_file            -
% 7.63/1.51  --dbg_out_stat                          false
% 7.63/1.51  
% 7.63/1.51  
% 7.63/1.51  
% 7.63/1.51  
% 7.63/1.51  ------ Proving...
% 7.63/1.51  
% 7.63/1.51  
% 7.63/1.51  % SZS status Theorem for theBenchmark.p
% 7.63/1.51  
% 7.63/1.51  % SZS output start CNFRefutation for theBenchmark.p
% 7.63/1.51  
% 7.63/1.51  fof(f2,axiom,(
% 7.63/1.51    ! [X0,X1] : (X0 = X1 <=> (r1_tarski(X1,X0) & r1_tarski(X0,X1)))),
% 7.63/1.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.63/1.51  
% 7.63/1.51  fof(f43,plain,(
% 7.63/1.51    ! [X0,X1] : ((X0 = X1 | (~r1_tarski(X1,X0) | ~r1_tarski(X0,X1))) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 7.63/1.51    inference(nnf_transformation,[],[f2])).
% 7.63/1.51  
% 7.63/1.51  fof(f44,plain,(
% 7.63/1.51    ! [X0,X1] : ((X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 7.63/1.51    inference(flattening,[],[f43])).
% 7.63/1.51  
% 7.63/1.51  fof(f59,plain,(
% 7.63/1.51    ( ! [X0,X1] : (r1_tarski(X0,X1) | X0 != X1) )),
% 7.63/1.51    inference(cnf_transformation,[],[f44])).
% 7.63/1.51  
% 7.63/1.51  fof(f95,plain,(
% 7.63/1.51    ( ! [X1] : (r1_tarski(X1,X1)) )),
% 7.63/1.51    inference(equality_resolution,[],[f59])).
% 7.63/1.51  
% 7.63/1.51  fof(f1,axiom,(
% 7.63/1.51    ! [X0,X1] : (! [X2] : (r2_hidden(X2,X0) <=> r2_hidden(X2,X1)) => X0 = X1)),
% 7.63/1.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.63/1.51  
% 7.63/1.51  fof(f20,plain,(
% 7.63/1.51    ! [X0,X1] : (X0 = X1 | ? [X2] : (r2_hidden(X2,X0) <~> r2_hidden(X2,X1)))),
% 7.63/1.51    inference(ennf_transformation,[],[f1])).
% 7.63/1.51  
% 7.63/1.51  fof(f40,plain,(
% 7.63/1.51    ! [X0,X1] : (X0 = X1 | ? [X2] : ((~r2_hidden(X2,X1) | ~r2_hidden(X2,X0)) & (r2_hidden(X2,X1) | r2_hidden(X2,X0))))),
% 7.63/1.51    inference(nnf_transformation,[],[f20])).
% 7.63/1.51  
% 7.63/1.51  fof(f41,plain,(
% 7.63/1.51    ! [X1,X0] : (? [X2] : ((~r2_hidden(X2,X1) | ~r2_hidden(X2,X0)) & (r2_hidden(X2,X1) | r2_hidden(X2,X0))) => ((~r2_hidden(sK0(X0,X1),X1) | ~r2_hidden(sK0(X0,X1),X0)) & (r2_hidden(sK0(X0,X1),X1) | r2_hidden(sK0(X0,X1),X0))))),
% 7.63/1.51    introduced(choice_axiom,[])).
% 7.63/1.51  
% 7.63/1.51  fof(f42,plain,(
% 7.63/1.51    ! [X0,X1] : (X0 = X1 | ((~r2_hidden(sK0(X0,X1),X1) | ~r2_hidden(sK0(X0,X1),X0)) & (r2_hidden(sK0(X0,X1),X1) | r2_hidden(sK0(X0,X1),X0))))),
% 7.63/1.51    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f40,f41])).
% 7.63/1.51  
% 7.63/1.51  fof(f57,plain,(
% 7.63/1.51    ( ! [X0,X1] : (X0 = X1 | r2_hidden(sK0(X0,X1),X1) | r2_hidden(sK0(X0,X1),X0)) )),
% 7.63/1.51    inference(cnf_transformation,[],[f42])).
% 7.63/1.51  
% 7.63/1.51  fof(f7,axiom,(
% 7.63/1.51    ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) <=> r1_tarski(X0,X1))),
% 7.63/1.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.63/1.51  
% 7.63/1.51  fof(f45,plain,(
% 7.63/1.51    ! [X0,X1] : ((m1_subset_1(X0,k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1)) & (r1_tarski(X0,X1) | ~m1_subset_1(X0,k1_zfmisc_1(X1))))),
% 7.63/1.51    inference(nnf_transformation,[],[f7])).
% 7.63/1.51  
% 7.63/1.51  fof(f67,plain,(
% 7.63/1.51    ( ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1)) )),
% 7.63/1.51    inference(cnf_transformation,[],[f45])).
% 7.63/1.51  
% 7.63/1.51  fof(f8,axiom,(
% 7.63/1.51    ! [X0,X1,X2] : ((m1_subset_1(X1,k1_zfmisc_1(X2)) & r2_hidden(X0,X1)) => m1_subset_1(X0,X2))),
% 7.63/1.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.63/1.51  
% 7.63/1.51  fof(f25,plain,(
% 7.63/1.51    ! [X0,X1,X2] : (m1_subset_1(X0,X2) | (~m1_subset_1(X1,k1_zfmisc_1(X2)) | ~r2_hidden(X0,X1)))),
% 7.63/1.51    inference(ennf_transformation,[],[f8])).
% 7.63/1.51  
% 7.63/1.51  fof(f26,plain,(
% 7.63/1.51    ! [X0,X1,X2] : (m1_subset_1(X0,X2) | ~m1_subset_1(X1,k1_zfmisc_1(X2)) | ~r2_hidden(X0,X1))),
% 7.63/1.51    inference(flattening,[],[f25])).
% 7.63/1.51  
% 7.63/1.51  fof(f68,plain,(
% 7.63/1.51    ( ! [X2,X0,X1] : (m1_subset_1(X0,X2) | ~m1_subset_1(X1,k1_zfmisc_1(X2)) | ~r2_hidden(X0,X1)) )),
% 7.63/1.51    inference(cnf_transformation,[],[f26])).
% 7.63/1.51  
% 7.63/1.51  fof(f6,axiom,(
% 7.63/1.51    ! [X0,X1] : (m1_subset_1(X0,X1) => (r2_hidden(X0,X1) | v1_xboole_0(X1)))),
% 7.63/1.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.63/1.51  
% 7.63/1.51  fof(f23,plain,(
% 7.63/1.51    ! [X0,X1] : ((r2_hidden(X0,X1) | v1_xboole_0(X1)) | ~m1_subset_1(X0,X1))),
% 7.63/1.51    inference(ennf_transformation,[],[f6])).
% 7.63/1.51  
% 7.63/1.51  fof(f24,plain,(
% 7.63/1.51    ! [X0,X1] : (r2_hidden(X0,X1) | v1_xboole_0(X1) | ~m1_subset_1(X0,X1))),
% 7.63/1.51    inference(flattening,[],[f23])).
% 7.63/1.51  
% 7.63/1.51  fof(f65,plain,(
% 7.63/1.51    ( ! [X0,X1] : (r2_hidden(X0,X1) | v1_xboole_0(X1) | ~m1_subset_1(X0,X1)) )),
% 7.63/1.51    inference(cnf_transformation,[],[f24])).
% 7.63/1.51  
% 7.63/1.51  fof(f16,conjecture,(
% 7.63/1.51    ! [X0] : ((l1_orders_2(X0) & v1_yellow_0(X0) & v5_orders_2(X0) & v4_orders_2(X0) & v3_orders_2(X0) & ~v2_struct_0(X0)) => ! [X1] : ((m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & v13_waybel_0(X1,X0) & v2_waybel_0(X1,X0) & ~v1_xboole_0(X1)) => (v1_subset_1(X1,u1_struct_0(X0)) <=> ~r2_hidden(k3_yellow_0(X0),X1))))),
% 7.63/1.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.63/1.51  
% 7.63/1.51  fof(f17,negated_conjecture,(
% 7.63/1.51    ~! [X0] : ((l1_orders_2(X0) & v1_yellow_0(X0) & v5_orders_2(X0) & v4_orders_2(X0) & v3_orders_2(X0) & ~v2_struct_0(X0)) => ! [X1] : ((m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & v13_waybel_0(X1,X0) & v2_waybel_0(X1,X0) & ~v1_xboole_0(X1)) => (v1_subset_1(X1,u1_struct_0(X0)) <=> ~r2_hidden(k3_yellow_0(X0),X1))))),
% 7.63/1.51    inference(negated_conjecture,[],[f16])).
% 7.63/1.51  
% 7.63/1.51  fof(f18,plain,(
% 7.63/1.51    ~! [X0] : ((l1_orders_2(X0) & v1_yellow_0(X0) & v5_orders_2(X0) & v4_orders_2(X0) & v3_orders_2(X0) & ~v2_struct_0(X0)) => ! [X1] : ((m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & v13_waybel_0(X1,X0) & ~v1_xboole_0(X1)) => (v1_subset_1(X1,u1_struct_0(X0)) <=> ~r2_hidden(k3_yellow_0(X0),X1))))),
% 7.63/1.51    inference(pure_predicate_removal,[],[f17])).
% 7.63/1.51  
% 7.63/1.51  fof(f38,plain,(
% 7.63/1.51    ? [X0] : (? [X1] : ((v1_subset_1(X1,u1_struct_0(X0)) <~> ~r2_hidden(k3_yellow_0(X0),X1)) & (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & v13_waybel_0(X1,X0) & ~v1_xboole_0(X1))) & (l1_orders_2(X0) & v1_yellow_0(X0) & v5_orders_2(X0) & v4_orders_2(X0) & v3_orders_2(X0) & ~v2_struct_0(X0)))),
% 7.63/1.51    inference(ennf_transformation,[],[f18])).
% 7.63/1.51  
% 7.63/1.51  fof(f39,plain,(
% 7.63/1.51    ? [X0] : (? [X1] : ((v1_subset_1(X1,u1_struct_0(X0)) <~> ~r2_hidden(k3_yellow_0(X0),X1)) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & v13_waybel_0(X1,X0) & ~v1_xboole_0(X1)) & l1_orders_2(X0) & v1_yellow_0(X0) & v5_orders_2(X0) & v4_orders_2(X0) & v3_orders_2(X0) & ~v2_struct_0(X0))),
% 7.63/1.51    inference(flattening,[],[f38])).
% 7.63/1.51  
% 7.63/1.51  fof(f52,plain,(
% 7.63/1.51    ? [X0] : (? [X1] : (((r2_hidden(k3_yellow_0(X0),X1) | ~v1_subset_1(X1,u1_struct_0(X0))) & (~r2_hidden(k3_yellow_0(X0),X1) | v1_subset_1(X1,u1_struct_0(X0)))) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & v13_waybel_0(X1,X0) & ~v1_xboole_0(X1)) & l1_orders_2(X0) & v1_yellow_0(X0) & v5_orders_2(X0) & v4_orders_2(X0) & v3_orders_2(X0) & ~v2_struct_0(X0))),
% 7.63/1.51    inference(nnf_transformation,[],[f39])).
% 7.63/1.51  
% 7.63/1.51  fof(f53,plain,(
% 7.63/1.51    ? [X0] : (? [X1] : ((r2_hidden(k3_yellow_0(X0),X1) | ~v1_subset_1(X1,u1_struct_0(X0))) & (~r2_hidden(k3_yellow_0(X0),X1) | v1_subset_1(X1,u1_struct_0(X0))) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & v13_waybel_0(X1,X0) & ~v1_xboole_0(X1)) & l1_orders_2(X0) & v1_yellow_0(X0) & v5_orders_2(X0) & v4_orders_2(X0) & v3_orders_2(X0) & ~v2_struct_0(X0))),
% 7.63/1.51    inference(flattening,[],[f52])).
% 7.63/1.51  
% 7.63/1.51  fof(f55,plain,(
% 7.63/1.51    ( ! [X0] : (? [X1] : ((r2_hidden(k3_yellow_0(X0),X1) | ~v1_subset_1(X1,u1_struct_0(X0))) & (~r2_hidden(k3_yellow_0(X0),X1) | v1_subset_1(X1,u1_struct_0(X0))) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & v13_waybel_0(X1,X0) & ~v1_xboole_0(X1)) => ((r2_hidden(k3_yellow_0(X0),sK4) | ~v1_subset_1(sK4,u1_struct_0(X0))) & (~r2_hidden(k3_yellow_0(X0),sK4) | v1_subset_1(sK4,u1_struct_0(X0))) & m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(X0))) & v13_waybel_0(sK4,X0) & ~v1_xboole_0(sK4))) )),
% 7.63/1.51    introduced(choice_axiom,[])).
% 7.63/1.51  
% 7.63/1.51  fof(f54,plain,(
% 7.63/1.51    ? [X0] : (? [X1] : ((r2_hidden(k3_yellow_0(X0),X1) | ~v1_subset_1(X1,u1_struct_0(X0))) & (~r2_hidden(k3_yellow_0(X0),X1) | v1_subset_1(X1,u1_struct_0(X0))) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & v13_waybel_0(X1,X0) & ~v1_xboole_0(X1)) & l1_orders_2(X0) & v1_yellow_0(X0) & v5_orders_2(X0) & v4_orders_2(X0) & v3_orders_2(X0) & ~v2_struct_0(X0)) => (? [X1] : ((r2_hidden(k3_yellow_0(sK3),X1) | ~v1_subset_1(X1,u1_struct_0(sK3))) & (~r2_hidden(k3_yellow_0(sK3),X1) | v1_subset_1(X1,u1_struct_0(sK3))) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK3))) & v13_waybel_0(X1,sK3) & ~v1_xboole_0(X1)) & l1_orders_2(sK3) & v1_yellow_0(sK3) & v5_orders_2(sK3) & v4_orders_2(sK3) & v3_orders_2(sK3) & ~v2_struct_0(sK3))),
% 7.63/1.51    introduced(choice_axiom,[])).
% 7.63/1.51  
% 7.63/1.51  fof(f56,plain,(
% 7.63/1.51    ((r2_hidden(k3_yellow_0(sK3),sK4) | ~v1_subset_1(sK4,u1_struct_0(sK3))) & (~r2_hidden(k3_yellow_0(sK3),sK4) | v1_subset_1(sK4,u1_struct_0(sK3))) & m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(sK3))) & v13_waybel_0(sK4,sK3) & ~v1_xboole_0(sK4)) & l1_orders_2(sK3) & v1_yellow_0(sK3) & v5_orders_2(sK3) & v4_orders_2(sK3) & v3_orders_2(sK3) & ~v2_struct_0(sK3)),
% 7.63/1.51    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3,sK4])],[f53,f55,f54])).
% 7.63/1.51  
% 7.63/1.51  fof(f89,plain,(
% 7.63/1.51    ~v1_xboole_0(sK4)),
% 7.63/1.51    inference(cnf_transformation,[],[f56])).
% 7.63/1.51  
% 7.63/1.51  fof(f5,axiom,(
% 7.63/1.51    ! [X0,X1] : (r2_hidden(X0,X1) => m1_subset_1(X0,X1))),
% 7.63/1.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.63/1.51  
% 7.63/1.51  fof(f22,plain,(
% 7.63/1.51    ! [X0,X1] : (m1_subset_1(X0,X1) | ~r2_hidden(X0,X1))),
% 7.63/1.51    inference(ennf_transformation,[],[f5])).
% 7.63/1.51  
% 7.63/1.51  fof(f64,plain,(
% 7.63/1.51    ( ! [X0,X1] : (m1_subset_1(X0,X1) | ~r2_hidden(X0,X1)) )),
% 7.63/1.51    inference(cnf_transformation,[],[f22])).
% 7.63/1.51  
% 7.63/1.51  fof(f14,axiom,(
% 7.63/1.51    ! [X0] : ((l1_orders_2(X0) & v5_orders_2(X0) & v4_orders_2(X0) & v3_orders_2(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,u1_struct_0(X0)) => (k1_yellow_0(X0,k5_waybel_0(X0,X1)) = X1 & r1_yellow_0(X0,k5_waybel_0(X0,X1)))))),
% 7.63/1.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.63/1.51  
% 7.63/1.51  fof(f35,plain,(
% 7.63/1.51    ! [X0] : (! [X1] : ((k1_yellow_0(X0,k5_waybel_0(X0,X1)) = X1 & r1_yellow_0(X0,k5_waybel_0(X0,X1))) | ~m1_subset_1(X1,u1_struct_0(X0))) | (~l1_orders_2(X0) | ~v5_orders_2(X0) | ~v4_orders_2(X0) | ~v3_orders_2(X0) | v2_struct_0(X0)))),
% 7.63/1.51    inference(ennf_transformation,[],[f14])).
% 7.63/1.51  
% 7.63/1.51  fof(f36,plain,(
% 7.63/1.51    ! [X0] : (! [X1] : ((k1_yellow_0(X0,k5_waybel_0(X0,X1)) = X1 & r1_yellow_0(X0,k5_waybel_0(X0,X1))) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~l1_orders_2(X0) | ~v5_orders_2(X0) | ~v4_orders_2(X0) | ~v3_orders_2(X0) | v2_struct_0(X0))),
% 7.63/1.51    inference(flattening,[],[f35])).
% 7.63/1.51  
% 7.63/1.51  fof(f80,plain,(
% 7.63/1.51    ( ! [X0,X1] : (k1_yellow_0(X0,k5_waybel_0(X0,X1)) = X1 | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_orders_2(X0) | ~v5_orders_2(X0) | ~v4_orders_2(X0) | ~v3_orders_2(X0) | v2_struct_0(X0)) )),
% 7.63/1.51    inference(cnf_transformation,[],[f36])).
% 7.63/1.51  
% 7.63/1.51  fof(f86,plain,(
% 7.63/1.51    v5_orders_2(sK3)),
% 7.63/1.51    inference(cnf_transformation,[],[f56])).
% 7.63/1.51  
% 7.63/1.51  fof(f83,plain,(
% 7.63/1.51    ~v2_struct_0(sK3)),
% 7.63/1.51    inference(cnf_transformation,[],[f56])).
% 7.63/1.51  
% 7.63/1.51  fof(f84,plain,(
% 7.63/1.51    v3_orders_2(sK3)),
% 7.63/1.51    inference(cnf_transformation,[],[f56])).
% 7.63/1.51  
% 7.63/1.51  fof(f85,plain,(
% 7.63/1.51    v4_orders_2(sK3)),
% 7.63/1.51    inference(cnf_transformation,[],[f56])).
% 7.63/1.51  
% 7.63/1.51  fof(f88,plain,(
% 7.63/1.51    l1_orders_2(sK3)),
% 7.63/1.51    inference(cnf_transformation,[],[f56])).
% 7.63/1.51  
% 7.63/1.51  fof(f91,plain,(
% 7.63/1.51    m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(sK3)))),
% 7.63/1.51    inference(cnf_transformation,[],[f56])).
% 7.63/1.51  
% 7.63/1.51  fof(f15,axiom,(
% 7.63/1.51    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => (v1_subset_1(X1,X0) <=> X0 != X1))),
% 7.63/1.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.63/1.51  
% 7.63/1.51  fof(f37,plain,(
% 7.63/1.51    ! [X0,X1] : ((v1_subset_1(X1,X0) <=> X0 != X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 7.63/1.51    inference(ennf_transformation,[],[f15])).
% 7.63/1.51  
% 7.63/1.51  fof(f51,plain,(
% 7.63/1.51    ! [X0,X1] : (((v1_subset_1(X1,X0) | X0 = X1) & (X0 != X1 | ~v1_subset_1(X1,X0))) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 7.63/1.51    inference(nnf_transformation,[],[f37])).
% 7.63/1.51  
% 7.63/1.51  fof(f81,plain,(
% 7.63/1.51    ( ! [X0,X1] : (X0 != X1 | ~v1_subset_1(X1,X0) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 7.63/1.51    inference(cnf_transformation,[],[f51])).
% 7.63/1.51  
% 7.63/1.51  fof(f96,plain,(
% 7.63/1.51    ( ! [X1] : (~v1_subset_1(X1,X1) | ~m1_subset_1(X1,k1_zfmisc_1(X1))) )),
% 7.63/1.51    inference(equality_resolution,[],[f81])).
% 7.63/1.51  
% 7.63/1.51  fof(f92,plain,(
% 7.63/1.51    ~r2_hidden(k3_yellow_0(sK3),sK4) | v1_subset_1(sK4,u1_struct_0(sK3))),
% 7.63/1.51    inference(cnf_transformation,[],[f56])).
% 7.63/1.51  
% 7.63/1.51  fof(f66,plain,(
% 7.63/1.51    ( ! [X0,X1] : (r1_tarski(X0,X1) | ~m1_subset_1(X0,k1_zfmisc_1(X1))) )),
% 7.63/1.51    inference(cnf_transformation,[],[f45])).
% 7.63/1.51  
% 7.63/1.51  fof(f61,plain,(
% 7.63/1.51    ( ! [X0,X1] : (X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) )),
% 7.63/1.51    inference(cnf_transformation,[],[f44])).
% 7.63/1.51  
% 7.63/1.51  fof(f4,axiom,(
% 7.63/1.51    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => ! [X2] : (r2_hidden(X2,X1) => r2_hidden(X2,X0)))),
% 7.63/1.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.63/1.51  
% 7.63/1.51  fof(f21,plain,(
% 7.63/1.51    ! [X0,X1] : (! [X2] : (r2_hidden(X2,X0) | ~r2_hidden(X2,X1)) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 7.63/1.51    inference(ennf_transformation,[],[f4])).
% 7.63/1.51  
% 7.63/1.51  fof(f63,plain,(
% 7.63/1.51    ( ! [X2,X0,X1] : (r2_hidden(X2,X0) | ~r2_hidden(X2,X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 7.63/1.51    inference(cnf_transformation,[],[f21])).
% 7.63/1.51  
% 7.63/1.51  fof(f58,plain,(
% 7.63/1.51    ( ! [X0,X1] : (X0 = X1 | ~r2_hidden(sK0(X0,X1),X1) | ~r2_hidden(sK0(X0,X1),X0)) )),
% 7.63/1.51    inference(cnf_transformation,[],[f42])).
% 7.63/1.51  
% 7.63/1.51  fof(f9,axiom,(
% 7.63/1.51    ! [X0] : (l1_orders_2(X0) => k3_yellow_0(X0) = k1_yellow_0(X0,k1_xboole_0))),
% 7.63/1.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.63/1.51  
% 7.63/1.51  fof(f27,plain,(
% 7.63/1.51    ! [X0] : (k3_yellow_0(X0) = k1_yellow_0(X0,k1_xboole_0) | ~l1_orders_2(X0))),
% 7.63/1.51    inference(ennf_transformation,[],[f9])).
% 7.63/1.51  
% 7.63/1.51  fof(f69,plain,(
% 7.63/1.51    ( ! [X0] : (k3_yellow_0(X0) = k1_yellow_0(X0,k1_xboole_0) | ~l1_orders_2(X0)) )),
% 7.63/1.51    inference(cnf_transformation,[],[f27])).
% 7.63/1.51  
% 7.63/1.51  fof(f10,axiom,(
% 7.63/1.51    ! [X0,X1] : (l1_orders_2(X0) => m1_subset_1(k1_yellow_0(X0,X1),u1_struct_0(X0)))),
% 7.63/1.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.63/1.51  
% 7.63/1.51  fof(f28,plain,(
% 7.63/1.51    ! [X0,X1] : (m1_subset_1(k1_yellow_0(X0,X1),u1_struct_0(X0)) | ~l1_orders_2(X0))),
% 7.63/1.51    inference(ennf_transformation,[],[f10])).
% 7.63/1.51  
% 7.63/1.51  fof(f70,plain,(
% 7.63/1.51    ( ! [X0,X1] : (m1_subset_1(k1_yellow_0(X0,X1),u1_struct_0(X0)) | ~l1_orders_2(X0)) )),
% 7.63/1.51    inference(cnf_transformation,[],[f28])).
% 7.63/1.51  
% 7.63/1.51  fof(f11,axiom,(
% 7.63/1.51    ! [X0] : (l1_orders_2(X0) => ! [X1,X2] : ((r1_yellow_0(X0,X2) & r1_yellow_0(X0,X1) & r1_tarski(X1,X2)) => r1_orders_2(X0,k1_yellow_0(X0,X1),k1_yellow_0(X0,X2))))),
% 7.63/1.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.63/1.51  
% 7.63/1.51  fof(f29,plain,(
% 7.63/1.51    ! [X0] : (! [X1,X2] : (r1_orders_2(X0,k1_yellow_0(X0,X1),k1_yellow_0(X0,X2)) | (~r1_yellow_0(X0,X2) | ~r1_yellow_0(X0,X1) | ~r1_tarski(X1,X2))) | ~l1_orders_2(X0))),
% 7.63/1.51    inference(ennf_transformation,[],[f11])).
% 7.63/1.51  
% 7.63/1.51  fof(f30,plain,(
% 7.63/1.51    ! [X0] : (! [X1,X2] : (r1_orders_2(X0,k1_yellow_0(X0,X1),k1_yellow_0(X0,X2)) | ~r1_yellow_0(X0,X2) | ~r1_yellow_0(X0,X1) | ~r1_tarski(X1,X2)) | ~l1_orders_2(X0))),
% 7.63/1.51    inference(flattening,[],[f29])).
% 7.63/1.51  
% 7.63/1.51  fof(f71,plain,(
% 7.63/1.51    ( ! [X2,X0,X1] : (r1_orders_2(X0,k1_yellow_0(X0,X1),k1_yellow_0(X0,X2)) | ~r1_yellow_0(X0,X2) | ~r1_yellow_0(X0,X1) | ~r1_tarski(X1,X2) | ~l1_orders_2(X0)) )),
% 7.63/1.51    inference(cnf_transformation,[],[f30])).
% 7.63/1.51  
% 7.63/1.51  fof(f79,plain,(
% 7.63/1.51    ( ! [X0,X1] : (r1_yellow_0(X0,k5_waybel_0(X0,X1)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_orders_2(X0) | ~v5_orders_2(X0) | ~v4_orders_2(X0) | ~v3_orders_2(X0) | v2_struct_0(X0)) )),
% 7.63/1.51    inference(cnf_transformation,[],[f36])).
% 7.63/1.51  
% 7.63/1.51  fof(f13,axiom,(
% 7.63/1.51    ! [X0] : (l1_orders_2(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => (v13_waybel_0(X1,X0) <=> ! [X2] : (m1_subset_1(X2,u1_struct_0(X0)) => ! [X3] : (m1_subset_1(X3,u1_struct_0(X0)) => ((r1_orders_2(X0,X2,X3) & r2_hidden(X2,X1)) => r2_hidden(X3,X1)))))))),
% 7.63/1.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.63/1.51  
% 7.63/1.51  fof(f33,plain,(
% 7.63/1.51    ! [X0] : (! [X1] : ((v13_waybel_0(X1,X0) <=> ! [X2] : (! [X3] : ((r2_hidden(X3,X1) | (~r1_orders_2(X0,X2,X3) | ~r2_hidden(X2,X1))) | ~m1_subset_1(X3,u1_struct_0(X0))) | ~m1_subset_1(X2,u1_struct_0(X0)))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_orders_2(X0))),
% 7.63/1.51    inference(ennf_transformation,[],[f13])).
% 7.63/1.51  
% 7.63/1.51  fof(f34,plain,(
% 7.63/1.51    ! [X0] : (! [X1] : ((v13_waybel_0(X1,X0) <=> ! [X2] : (! [X3] : (r2_hidden(X3,X1) | ~r1_orders_2(X0,X2,X3) | ~r2_hidden(X2,X1) | ~m1_subset_1(X3,u1_struct_0(X0))) | ~m1_subset_1(X2,u1_struct_0(X0)))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_orders_2(X0))),
% 7.63/1.51    inference(flattening,[],[f33])).
% 7.63/1.51  
% 7.63/1.51  fof(f46,plain,(
% 7.63/1.51    ! [X0] : (! [X1] : (((v13_waybel_0(X1,X0) | ? [X2] : (? [X3] : (~r2_hidden(X3,X1) & r1_orders_2(X0,X2,X3) & r2_hidden(X2,X1) & m1_subset_1(X3,u1_struct_0(X0))) & m1_subset_1(X2,u1_struct_0(X0)))) & (! [X2] : (! [X3] : (r2_hidden(X3,X1) | ~r1_orders_2(X0,X2,X3) | ~r2_hidden(X2,X1) | ~m1_subset_1(X3,u1_struct_0(X0))) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~v13_waybel_0(X1,X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_orders_2(X0))),
% 7.63/1.51    inference(nnf_transformation,[],[f34])).
% 7.63/1.51  
% 7.63/1.51  fof(f47,plain,(
% 7.63/1.51    ! [X0] : (! [X1] : (((v13_waybel_0(X1,X0) | ? [X2] : (? [X3] : (~r2_hidden(X3,X1) & r1_orders_2(X0,X2,X3) & r2_hidden(X2,X1) & m1_subset_1(X3,u1_struct_0(X0))) & m1_subset_1(X2,u1_struct_0(X0)))) & (! [X4] : (! [X5] : (r2_hidden(X5,X1) | ~r1_orders_2(X0,X4,X5) | ~r2_hidden(X4,X1) | ~m1_subset_1(X5,u1_struct_0(X0))) | ~m1_subset_1(X4,u1_struct_0(X0))) | ~v13_waybel_0(X1,X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_orders_2(X0))),
% 7.63/1.51    inference(rectify,[],[f46])).
% 7.63/1.51  
% 7.63/1.51  fof(f49,plain,(
% 7.63/1.51    ( ! [X2] : (! [X1,X0] : (? [X3] : (~r2_hidden(X3,X1) & r1_orders_2(X0,X2,X3) & r2_hidden(X2,X1) & m1_subset_1(X3,u1_struct_0(X0))) => (~r2_hidden(sK2(X0,X1),X1) & r1_orders_2(X0,X2,sK2(X0,X1)) & r2_hidden(X2,X1) & m1_subset_1(sK2(X0,X1),u1_struct_0(X0))))) )),
% 7.63/1.51    introduced(choice_axiom,[])).
% 7.63/1.51  
% 7.63/1.51  fof(f48,plain,(
% 7.63/1.51    ! [X1,X0] : (? [X2] : (? [X3] : (~r2_hidden(X3,X1) & r1_orders_2(X0,X2,X3) & r2_hidden(X2,X1) & m1_subset_1(X3,u1_struct_0(X0))) & m1_subset_1(X2,u1_struct_0(X0))) => (? [X3] : (~r2_hidden(X3,X1) & r1_orders_2(X0,sK1(X0,X1),X3) & r2_hidden(sK1(X0,X1),X1) & m1_subset_1(X3,u1_struct_0(X0))) & m1_subset_1(sK1(X0,X1),u1_struct_0(X0))))),
% 7.63/1.51    introduced(choice_axiom,[])).
% 7.63/1.51  
% 7.63/1.51  fof(f50,plain,(
% 7.63/1.51    ! [X0] : (! [X1] : (((v13_waybel_0(X1,X0) | ((~r2_hidden(sK2(X0,X1),X1) & r1_orders_2(X0,sK1(X0,X1),sK2(X0,X1)) & r2_hidden(sK1(X0,X1),X1) & m1_subset_1(sK2(X0,X1),u1_struct_0(X0))) & m1_subset_1(sK1(X0,X1),u1_struct_0(X0)))) & (! [X4] : (! [X5] : (r2_hidden(X5,X1) | ~r1_orders_2(X0,X4,X5) | ~r2_hidden(X4,X1) | ~m1_subset_1(X5,u1_struct_0(X0))) | ~m1_subset_1(X4,u1_struct_0(X0))) | ~v13_waybel_0(X1,X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_orders_2(X0))),
% 7.63/1.51    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1,sK2])],[f47,f49,f48])).
% 7.63/1.51  
% 7.63/1.51  fof(f73,plain,(
% 7.63/1.51    ( ! [X4,X0,X5,X1] : (r2_hidden(X5,X1) | ~r1_orders_2(X0,X4,X5) | ~r2_hidden(X4,X1) | ~m1_subset_1(X5,u1_struct_0(X0)) | ~m1_subset_1(X4,u1_struct_0(X0)) | ~v13_waybel_0(X1,X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_orders_2(X0)) )),
% 7.63/1.51    inference(cnf_transformation,[],[f50])).
% 7.63/1.51  
% 7.63/1.51  fof(f90,plain,(
% 7.63/1.51    v13_waybel_0(sK4,sK3)),
% 7.63/1.51    inference(cnf_transformation,[],[f56])).
% 7.63/1.51  
% 7.63/1.51  fof(f82,plain,(
% 7.63/1.51    ( ! [X0,X1] : (v1_subset_1(X1,X0) | X0 = X1 | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 7.63/1.51    inference(cnf_transformation,[],[f51])).
% 7.63/1.51  
% 7.63/1.51  fof(f93,plain,(
% 7.63/1.51    r2_hidden(k3_yellow_0(sK3),sK4) | ~v1_subset_1(sK4,u1_struct_0(sK3))),
% 7.63/1.51    inference(cnf_transformation,[],[f56])).
% 7.63/1.51  
% 7.63/1.51  fof(f87,plain,(
% 7.63/1.51    v1_yellow_0(sK3)),
% 7.63/1.51    inference(cnf_transformation,[],[f56])).
% 7.63/1.51  
% 7.63/1.51  fof(f12,axiom,(
% 7.63/1.51    ! [X0] : ((l1_orders_2(X0) & v1_yellow_0(X0) & v5_orders_2(X0) & ~v2_struct_0(X0)) => (r2_yellow_0(X0,u1_struct_0(X0)) & r1_yellow_0(X0,k1_xboole_0)))),
% 7.63/1.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.63/1.51  
% 7.63/1.51  fof(f19,plain,(
% 7.63/1.51    ! [X0] : ((l1_orders_2(X0) & v1_yellow_0(X0) & v5_orders_2(X0) & ~v2_struct_0(X0)) => r1_yellow_0(X0,k1_xboole_0))),
% 7.63/1.51    inference(pure_predicate_removal,[],[f12])).
% 7.63/1.51  
% 7.63/1.51  fof(f31,plain,(
% 7.63/1.51    ! [X0] : (r1_yellow_0(X0,k1_xboole_0) | (~l1_orders_2(X0) | ~v1_yellow_0(X0) | ~v5_orders_2(X0) | v2_struct_0(X0)))),
% 7.63/1.51    inference(ennf_transformation,[],[f19])).
% 7.63/1.51  
% 7.63/1.51  fof(f32,plain,(
% 7.63/1.51    ! [X0] : (r1_yellow_0(X0,k1_xboole_0) | ~l1_orders_2(X0) | ~v1_yellow_0(X0) | ~v5_orders_2(X0) | v2_struct_0(X0))),
% 7.63/1.51    inference(flattening,[],[f31])).
% 7.63/1.51  
% 7.63/1.51  fof(f72,plain,(
% 7.63/1.51    ( ! [X0] : (r1_yellow_0(X0,k1_xboole_0) | ~l1_orders_2(X0) | ~v1_yellow_0(X0) | ~v5_orders_2(X0) | v2_struct_0(X0)) )),
% 7.63/1.51    inference(cnf_transformation,[],[f32])).
% 7.63/1.51  
% 7.63/1.51  fof(f3,axiom,(
% 7.63/1.51    ! [X0] : r1_tarski(k1_xboole_0,X0)),
% 7.63/1.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.63/1.51  
% 7.63/1.51  fof(f62,plain,(
% 7.63/1.51    ( ! [X0] : (r1_tarski(k1_xboole_0,X0)) )),
% 7.63/1.51    inference(cnf_transformation,[],[f3])).
% 7.63/1.51  
% 7.63/1.51  cnf(c_4,plain,
% 7.63/1.51      ( r1_tarski(X0,X0) ),
% 7.63/1.51      inference(cnf_transformation,[],[f95]) ).
% 7.63/1.51  
% 7.63/1.51  cnf(c_2215,plain,
% 7.63/1.51      ( r1_tarski(X0,X0) = iProver_top ),
% 7.63/1.51      inference(predicate_to_equality,[status(thm)],[c_4]) ).
% 7.63/1.51  
% 7.63/1.51  cnf(c_1,plain,
% 7.63/1.51      ( r2_hidden(sK0(X0,X1),X1) | r2_hidden(sK0(X0,X1),X0) | X1 = X0 ),
% 7.63/1.51      inference(cnf_transformation,[],[f57]) ).
% 7.63/1.51  
% 7.63/1.51  cnf(c_2217,plain,
% 7.63/1.51      ( X0 = X1
% 7.63/1.51      | r2_hidden(sK0(X1,X0),X0) = iProver_top
% 7.63/1.51      | r2_hidden(sK0(X1,X0),X1) = iProver_top ),
% 7.63/1.51      inference(predicate_to_equality,[status(thm)],[c_1]) ).
% 7.63/1.51  
% 7.63/1.51  cnf(c_9,plain,
% 7.63/1.51      ( m1_subset_1(X0,k1_zfmisc_1(X1)) | ~ r1_tarski(X0,X1) ),
% 7.63/1.51      inference(cnf_transformation,[],[f67]) ).
% 7.63/1.51  
% 7.63/1.51  cnf(c_2212,plain,
% 7.63/1.51      ( m1_subset_1(X0,k1_zfmisc_1(X1)) = iProver_top
% 7.63/1.51      | r1_tarski(X0,X1) != iProver_top ),
% 7.63/1.51      inference(predicate_to_equality,[status(thm)],[c_9]) ).
% 7.63/1.51  
% 7.63/1.51  cnf(c_11,plain,
% 7.63/1.51      ( m1_subset_1(X0,X1)
% 7.63/1.51      | ~ m1_subset_1(X2,k1_zfmisc_1(X1))
% 7.63/1.51      | ~ r2_hidden(X0,X2) ),
% 7.63/1.51      inference(cnf_transformation,[],[f68]) ).
% 7.63/1.51  
% 7.63/1.51  cnf(c_2210,plain,
% 7.63/1.51      ( m1_subset_1(X0,X1) = iProver_top
% 7.63/1.51      | m1_subset_1(X2,k1_zfmisc_1(X1)) != iProver_top
% 7.63/1.51      | r2_hidden(X0,X2) != iProver_top ),
% 7.63/1.51      inference(predicate_to_equality,[status(thm)],[c_11]) ).
% 7.63/1.51  
% 7.63/1.51  cnf(c_3062,plain,
% 7.63/1.51      ( m1_subset_1(X0,X1) = iProver_top
% 7.63/1.51      | r1_tarski(X2,X1) != iProver_top
% 7.63/1.51      | r2_hidden(X0,X2) != iProver_top ),
% 7.63/1.51      inference(superposition,[status(thm)],[c_2212,c_2210]) ).
% 7.63/1.51  
% 7.63/1.51  cnf(c_5473,plain,
% 7.63/1.51      ( X0 = X1
% 7.63/1.51      | m1_subset_1(sK0(X0,X1),X2) = iProver_top
% 7.63/1.51      | r1_tarski(X0,X2) != iProver_top
% 7.63/1.51      | r2_hidden(sK0(X0,X1),X1) = iProver_top ),
% 7.63/1.51      inference(superposition,[status(thm)],[c_2217,c_3062]) ).
% 7.63/1.51  
% 7.63/1.51  cnf(c_8,plain,
% 7.63/1.51      ( ~ m1_subset_1(X0,X1) | r2_hidden(X0,X1) | v1_xboole_0(X1) ),
% 7.63/1.51      inference(cnf_transformation,[],[f65]) ).
% 7.63/1.51  
% 7.63/1.51  cnf(c_30,negated_conjecture,
% 7.63/1.51      ( ~ v1_xboole_0(sK4) ),
% 7.63/1.51      inference(cnf_transformation,[],[f89]) ).
% 7.63/1.51  
% 7.63/1.51  cnf(c_493,plain,
% 7.63/1.51      ( ~ m1_subset_1(X0,X1) | r2_hidden(X0,X1) | sK4 != X1 ),
% 7.63/1.51      inference(resolution_lifted,[status(thm)],[c_8,c_30]) ).
% 7.63/1.51  
% 7.63/1.51  cnf(c_494,plain,
% 7.63/1.51      ( ~ m1_subset_1(X0,sK4) | r2_hidden(X0,sK4) ),
% 7.63/1.51      inference(unflattening,[status(thm)],[c_493]) ).
% 7.63/1.51  
% 7.63/1.51  cnf(c_2206,plain,
% 7.63/1.51      ( m1_subset_1(X0,sK4) != iProver_top
% 7.63/1.51      | r2_hidden(X0,sK4) = iProver_top ),
% 7.63/1.51      inference(predicate_to_equality,[status(thm)],[c_494]) ).
% 7.63/1.51  
% 7.63/1.51  cnf(c_14986,plain,
% 7.63/1.51      ( X0 = X1
% 7.63/1.51      | r1_tarski(X1,sK4) != iProver_top
% 7.63/1.51      | r2_hidden(sK0(X1,X0),X0) = iProver_top
% 7.63/1.51      | r2_hidden(sK0(X1,X0),sK4) = iProver_top ),
% 7.63/1.51      inference(superposition,[status(thm)],[c_5473,c_2206]) ).
% 7.63/1.51  
% 7.63/1.51  cnf(c_7,plain,
% 7.63/1.51      ( m1_subset_1(X0,X1) | ~ r2_hidden(X0,X1) ),
% 7.63/1.51      inference(cnf_transformation,[],[f64]) ).
% 7.63/1.51  
% 7.63/1.51  cnf(c_2213,plain,
% 7.63/1.51      ( m1_subset_1(X0,X1) = iProver_top
% 7.63/1.51      | r2_hidden(X0,X1) != iProver_top ),
% 7.63/1.51      inference(predicate_to_equality,[status(thm)],[c_7]) ).
% 7.63/1.51  
% 7.63/1.51  cnf(c_15414,plain,
% 7.63/1.51      ( X0 = X1
% 7.63/1.51      | m1_subset_1(sK0(X0,X1),X1) = iProver_top
% 7.63/1.51      | r1_tarski(X0,sK4) != iProver_top
% 7.63/1.51      | r2_hidden(sK0(X0,X1),sK4) = iProver_top ),
% 7.63/1.51      inference(superposition,[status(thm)],[c_14986,c_2213]) ).
% 7.63/1.51  
% 7.63/1.51  cnf(c_22,plain,
% 7.63/1.51      ( ~ m1_subset_1(X0,u1_struct_0(X1))
% 7.63/1.51      | ~ v3_orders_2(X1)
% 7.63/1.51      | ~ v4_orders_2(X1)
% 7.63/1.51      | v2_struct_0(X1)
% 7.63/1.51      | ~ v5_orders_2(X1)
% 7.63/1.51      | ~ l1_orders_2(X1)
% 7.63/1.51      | k1_yellow_0(X1,k5_waybel_0(X1,X0)) = X0 ),
% 7.63/1.51      inference(cnf_transformation,[],[f80]) ).
% 7.63/1.51  
% 7.63/1.51  cnf(c_33,negated_conjecture,
% 7.63/1.51      ( v5_orders_2(sK3) ),
% 7.63/1.51      inference(cnf_transformation,[],[f86]) ).
% 7.63/1.51  
% 7.63/1.51  cnf(c_576,plain,
% 7.63/1.51      ( ~ m1_subset_1(X0,u1_struct_0(X1))
% 7.63/1.51      | ~ v3_orders_2(X1)
% 7.63/1.51      | ~ v4_orders_2(X1)
% 7.63/1.51      | v2_struct_0(X1)
% 7.63/1.51      | ~ l1_orders_2(X1)
% 7.63/1.51      | k1_yellow_0(X1,k5_waybel_0(X1,X0)) = X0
% 7.63/1.51      | sK3 != X1 ),
% 7.63/1.51      inference(resolution_lifted,[status(thm)],[c_22,c_33]) ).
% 7.63/1.51  
% 7.63/1.51  cnf(c_577,plain,
% 7.63/1.51      ( ~ m1_subset_1(X0,u1_struct_0(sK3))
% 7.63/1.51      | ~ v3_orders_2(sK3)
% 7.63/1.51      | ~ v4_orders_2(sK3)
% 7.63/1.51      | v2_struct_0(sK3)
% 7.63/1.51      | ~ l1_orders_2(sK3)
% 7.63/1.51      | k1_yellow_0(sK3,k5_waybel_0(sK3,X0)) = X0 ),
% 7.63/1.51      inference(unflattening,[status(thm)],[c_576]) ).
% 7.63/1.51  
% 7.63/1.51  cnf(c_36,negated_conjecture,
% 7.63/1.51      ( ~ v2_struct_0(sK3) ),
% 7.63/1.51      inference(cnf_transformation,[],[f83]) ).
% 7.63/1.51  
% 7.63/1.51  cnf(c_35,negated_conjecture,
% 7.63/1.51      ( v3_orders_2(sK3) ),
% 7.63/1.51      inference(cnf_transformation,[],[f84]) ).
% 7.63/1.51  
% 7.63/1.51  cnf(c_34,negated_conjecture,
% 7.63/1.51      ( v4_orders_2(sK3) ),
% 7.63/1.51      inference(cnf_transformation,[],[f85]) ).
% 7.63/1.51  
% 7.63/1.51  cnf(c_31,negated_conjecture,
% 7.63/1.51      ( l1_orders_2(sK3) ),
% 7.63/1.51      inference(cnf_transformation,[],[f88]) ).
% 7.63/1.51  
% 7.63/1.51  cnf(c_581,plain,
% 7.63/1.51      ( ~ m1_subset_1(X0,u1_struct_0(sK3))
% 7.63/1.51      | k1_yellow_0(sK3,k5_waybel_0(sK3,X0)) = X0 ),
% 7.63/1.51      inference(global_propositional_subsumption,
% 7.63/1.51                [status(thm)],
% 7.63/1.51                [c_577,c_36,c_35,c_34,c_31]) ).
% 7.63/1.51  
% 7.63/1.51  cnf(c_2201,plain,
% 7.63/1.51      ( k1_yellow_0(sK3,k5_waybel_0(sK3,X0)) = X0
% 7.63/1.51      | m1_subset_1(X0,u1_struct_0(sK3)) != iProver_top ),
% 7.63/1.51      inference(predicate_to_equality,[status(thm)],[c_581]) ).
% 7.63/1.51  
% 7.63/1.51  cnf(c_16602,plain,
% 7.63/1.51      ( k1_yellow_0(sK3,k5_waybel_0(sK3,sK0(X0,u1_struct_0(sK3)))) = sK0(X0,u1_struct_0(sK3))
% 7.63/1.51      | u1_struct_0(sK3) = X0
% 7.63/1.51      | r1_tarski(X0,sK4) != iProver_top
% 7.63/1.51      | r2_hidden(sK0(X0,u1_struct_0(sK3)),sK4) = iProver_top ),
% 7.63/1.51      inference(superposition,[status(thm)],[c_15414,c_2201]) ).
% 7.63/1.51  
% 7.63/1.51  cnf(c_28,negated_conjecture,
% 7.63/1.51      ( m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(sK3))) ),
% 7.63/1.51      inference(cnf_transformation,[],[f91]) ).
% 7.63/1.51  
% 7.63/1.51  cnf(c_45,plain,
% 7.63/1.51      ( m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(sK3))) = iProver_top ),
% 7.63/1.51      inference(predicate_to_equality,[status(thm)],[c_28]) ).
% 7.63/1.51  
% 7.63/1.51  cnf(c_25,plain,
% 7.63/1.51      ( ~ v1_subset_1(X0,X0) | ~ m1_subset_1(X0,k1_zfmisc_1(X0)) ),
% 7.63/1.51      inference(cnf_transformation,[],[f96]) ).
% 7.63/1.51  
% 7.63/1.51  cnf(c_27,negated_conjecture,
% 7.63/1.51      ( v1_subset_1(sK4,u1_struct_0(sK3))
% 7.63/1.51      | ~ r2_hidden(k3_yellow_0(sK3),sK4) ),
% 7.63/1.51      inference(cnf_transformation,[],[f92]) ).
% 7.63/1.51  
% 7.63/1.51  cnf(c_279,plain,
% 7.63/1.51      ( v1_subset_1(sK4,u1_struct_0(sK3))
% 7.63/1.51      | ~ r2_hidden(k3_yellow_0(sK3),sK4) ),
% 7.63/1.51      inference(prop_impl,[status(thm)],[c_27]) ).
% 7.63/1.51  
% 7.63/1.51  cnf(c_537,plain,
% 7.63/1.51      ( ~ m1_subset_1(X0,k1_zfmisc_1(X0))
% 7.63/1.51      | ~ r2_hidden(k3_yellow_0(sK3),sK4)
% 7.63/1.51      | u1_struct_0(sK3) != X0
% 7.63/1.51      | sK4 != X0 ),
% 7.63/1.51      inference(resolution_lifted,[status(thm)],[c_25,c_279]) ).
% 7.63/1.51  
% 7.63/1.51  cnf(c_538,plain,
% 7.63/1.51      ( ~ m1_subset_1(u1_struct_0(sK3),k1_zfmisc_1(u1_struct_0(sK3)))
% 7.63/1.51      | ~ r2_hidden(k3_yellow_0(sK3),sK4)
% 7.63/1.51      | sK4 != u1_struct_0(sK3) ),
% 7.63/1.51      inference(unflattening,[status(thm)],[c_537]) ).
% 7.63/1.51  
% 7.63/1.51  cnf(c_539,plain,
% 7.63/1.51      ( sK4 != u1_struct_0(sK3)
% 7.63/1.51      | m1_subset_1(u1_struct_0(sK3),k1_zfmisc_1(u1_struct_0(sK3))) != iProver_top
% 7.63/1.51      | r2_hidden(k3_yellow_0(sK3),sK4) != iProver_top ),
% 7.63/1.51      inference(predicate_to_equality,[status(thm)],[c_538]) ).
% 7.63/1.51  
% 7.63/1.51  cnf(c_10,plain,
% 7.63/1.51      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1)) | r1_tarski(X0,X1) ),
% 7.63/1.51      inference(cnf_transformation,[],[f66]) ).
% 7.63/1.51  
% 7.63/1.51  cnf(c_2438,plain,
% 7.63/1.51      ( ~ m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(sK3)))
% 7.63/1.51      | r1_tarski(sK4,u1_struct_0(sK3)) ),
% 7.63/1.51      inference(instantiation,[status(thm)],[c_10]) ).
% 7.63/1.51  
% 7.63/1.51  cnf(c_2439,plain,
% 7.63/1.51      ( m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(sK3))) != iProver_top
% 7.63/1.51      | r1_tarski(sK4,u1_struct_0(sK3)) = iProver_top ),
% 7.63/1.51      inference(predicate_to_equality,[status(thm)],[c_2438]) ).
% 7.63/1.51  
% 7.63/1.51  cnf(c_1542,plain,( X0 = X0 ),theory(equality) ).
% 7.63/1.51  
% 7.63/1.51  cnf(c_2506,plain,
% 7.63/1.51      ( sK4 = sK4 ),
% 7.63/1.51      inference(instantiation,[status(thm)],[c_1542]) ).
% 7.63/1.51  
% 7.63/1.51  cnf(c_2433,plain,
% 7.63/1.51      ( m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK3)))
% 7.63/1.51      | ~ r1_tarski(X0,u1_struct_0(sK3)) ),
% 7.63/1.51      inference(instantiation,[status(thm)],[c_9]) ).
% 7.63/1.51  
% 7.63/1.51  cnf(c_2526,plain,
% 7.63/1.51      ( m1_subset_1(u1_struct_0(sK3),k1_zfmisc_1(u1_struct_0(sK3)))
% 7.63/1.51      | ~ r1_tarski(u1_struct_0(sK3),u1_struct_0(sK3)) ),
% 7.63/1.51      inference(instantiation,[status(thm)],[c_2433]) ).
% 7.63/1.51  
% 7.63/1.51  cnf(c_2528,plain,
% 7.63/1.51      ( m1_subset_1(u1_struct_0(sK3),k1_zfmisc_1(u1_struct_0(sK3))) = iProver_top
% 7.63/1.51      | r1_tarski(u1_struct_0(sK3),u1_struct_0(sK3)) != iProver_top ),
% 7.63/1.51      inference(predicate_to_equality,[status(thm)],[c_2526]) ).
% 7.63/1.51  
% 7.63/1.51  cnf(c_2527,plain,
% 7.63/1.51      ( r1_tarski(u1_struct_0(sK3),u1_struct_0(sK3)) ),
% 7.63/1.51      inference(instantiation,[status(thm)],[c_4]) ).
% 7.63/1.51  
% 7.63/1.51  cnf(c_2530,plain,
% 7.63/1.51      ( r1_tarski(u1_struct_0(sK3),u1_struct_0(sK3)) = iProver_top ),
% 7.63/1.51      inference(predicate_to_equality,[status(thm)],[c_2527]) ).
% 7.63/1.51  
% 7.63/1.51  cnf(c_2,plain,
% 7.63/1.51      ( ~ r1_tarski(X0,X1) | ~ r1_tarski(X1,X0) | X0 = X1 ),
% 7.63/1.51      inference(cnf_transformation,[],[f61]) ).
% 7.63/1.51  
% 7.63/1.51  cnf(c_2579,plain,
% 7.63/1.51      ( ~ r1_tarski(X0,u1_struct_0(sK3))
% 7.63/1.51      | ~ r1_tarski(u1_struct_0(sK3),X0)
% 7.63/1.51      | X0 = u1_struct_0(sK3) ),
% 7.63/1.51      inference(instantiation,[status(thm)],[c_2]) ).
% 7.63/1.51  
% 7.63/1.51  cnf(c_3362,plain,
% 7.63/1.51      ( ~ r1_tarski(u1_struct_0(sK3),sK4)
% 7.63/1.51      | ~ r1_tarski(sK4,u1_struct_0(sK3))
% 7.63/1.51      | sK4 = u1_struct_0(sK3) ),
% 7.63/1.51      inference(instantiation,[status(thm)],[c_2579]) ).
% 7.63/1.51  
% 7.63/1.51  cnf(c_3363,plain,
% 7.63/1.51      ( sK4 = u1_struct_0(sK3)
% 7.63/1.51      | r1_tarski(u1_struct_0(sK3),sK4) != iProver_top
% 7.63/1.51      | r1_tarski(sK4,u1_struct_0(sK3)) != iProver_top ),
% 7.63/1.51      inference(predicate_to_equality,[status(thm)],[c_3362]) ).
% 7.63/1.51  
% 7.63/1.51  cnf(c_2209,plain,
% 7.63/1.51      ( m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(sK3))) = iProver_top ),
% 7.63/1.51      inference(predicate_to_equality,[status(thm)],[c_28]) ).
% 7.63/1.51  
% 7.63/1.51  cnf(c_2211,plain,
% 7.63/1.51      ( m1_subset_1(X0,k1_zfmisc_1(X1)) != iProver_top
% 7.63/1.51      | r1_tarski(X0,X1) = iProver_top ),
% 7.63/1.51      inference(predicate_to_equality,[status(thm)],[c_10]) ).
% 7.63/1.51  
% 7.63/1.51  cnf(c_2758,plain,
% 7.63/1.51      ( r1_tarski(sK4,u1_struct_0(sK3)) = iProver_top ),
% 7.63/1.51      inference(superposition,[status(thm)],[c_2209,c_2211]) ).
% 7.63/1.51  
% 7.63/1.51  cnf(c_6,plain,
% 7.63/1.51      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
% 7.63/1.51      | ~ r2_hidden(X2,X0)
% 7.63/1.51      | r2_hidden(X2,X1) ),
% 7.63/1.51      inference(cnf_transformation,[],[f63]) ).
% 7.63/1.51  
% 7.63/1.51  cnf(c_277,plain,
% 7.63/1.51      ( ~ r1_tarski(X0,X1) | m1_subset_1(X0,k1_zfmisc_1(X1)) ),
% 7.63/1.51      inference(prop_impl,[status(thm)],[c_9]) ).
% 7.63/1.51  
% 7.63/1.51  cnf(c_278,plain,
% 7.63/1.51      ( m1_subset_1(X0,k1_zfmisc_1(X1)) | ~ r1_tarski(X0,X1) ),
% 7.63/1.51      inference(renaming,[status(thm)],[c_277]) ).
% 7.63/1.51  
% 7.63/1.51  cnf(c_358,plain,
% 7.63/1.51      ( ~ r1_tarski(X0,X1) | ~ r2_hidden(X2,X0) | r2_hidden(X2,X1) ),
% 7.63/1.51      inference(bin_hyper_res,[status(thm)],[c_6,c_278]) ).
% 7.63/1.51  
% 7.63/1.51  cnf(c_2207,plain,
% 7.63/1.51      ( r1_tarski(X0,X1) != iProver_top
% 7.63/1.51      | r2_hidden(X2,X0) != iProver_top
% 7.63/1.51      | r2_hidden(X2,X1) = iProver_top ),
% 7.63/1.51      inference(predicate_to_equality,[status(thm)],[c_358]) ).
% 7.63/1.51  
% 7.63/1.51  cnf(c_3779,plain,
% 7.63/1.51      ( r2_hidden(X0,u1_struct_0(sK3)) = iProver_top
% 7.63/1.51      | r2_hidden(X0,sK4) != iProver_top ),
% 7.63/1.51      inference(superposition,[status(thm)],[c_2758,c_2207]) ).
% 7.63/1.51  
% 7.63/1.51  cnf(c_0,plain,
% 7.63/1.51      ( ~ r2_hidden(sK0(X0,X1),X1)
% 7.63/1.51      | ~ r2_hidden(sK0(X0,X1),X0)
% 7.63/1.51      | X1 = X0 ),
% 7.63/1.51      inference(cnf_transformation,[],[f58]) ).
% 7.63/1.51  
% 7.63/1.51  cnf(c_2218,plain,
% 7.63/1.51      ( X0 = X1
% 7.63/1.51      | r2_hidden(sK0(X1,X0),X0) != iProver_top
% 7.63/1.51      | r2_hidden(sK0(X1,X0),X1) != iProver_top ),
% 7.63/1.51      inference(predicate_to_equality,[status(thm)],[c_0]) ).
% 7.63/1.51  
% 7.63/1.51  cnf(c_3899,plain,
% 7.63/1.51      ( u1_struct_0(sK3) = X0
% 7.63/1.51      | r2_hidden(sK0(X0,u1_struct_0(sK3)),X0) != iProver_top
% 7.63/1.51      | r2_hidden(sK0(X0,u1_struct_0(sK3)),sK4) != iProver_top ),
% 7.63/1.51      inference(superposition,[status(thm)],[c_3779,c_2218]) ).
% 7.63/1.51  
% 7.63/1.51  cnf(c_3041,plain,
% 7.63/1.51      ( X0 = X1
% 7.63/1.51      | m1_subset_1(sK0(X0,X1),X1) = iProver_top
% 7.63/1.51      | r2_hidden(sK0(X0,X1),X0) = iProver_top ),
% 7.63/1.51      inference(superposition,[status(thm)],[c_2217,c_2213]) ).
% 7.63/1.51  
% 7.63/1.51  cnf(c_4892,plain,
% 7.63/1.51      ( k1_yellow_0(sK3,k5_waybel_0(sK3,sK0(X0,u1_struct_0(sK3)))) = sK0(X0,u1_struct_0(sK3))
% 7.63/1.51      | u1_struct_0(sK3) = X0
% 7.63/1.51      | r2_hidden(sK0(X0,u1_struct_0(sK3)),X0) = iProver_top ),
% 7.63/1.51      inference(superposition,[status(thm)],[c_3041,c_2201]) ).
% 7.63/1.51  
% 7.63/1.51  cnf(c_12,plain,
% 7.63/1.51      ( ~ l1_orders_2(X0)
% 7.63/1.51      | k1_yellow_0(X0,k1_xboole_0) = k3_yellow_0(X0) ),
% 7.63/1.51      inference(cnf_transformation,[],[f69]) ).
% 7.63/1.51  
% 7.63/1.51  cnf(c_745,plain,
% 7.63/1.51      ( k1_yellow_0(X0,k1_xboole_0) = k3_yellow_0(X0) | sK3 != X0 ),
% 7.63/1.51      inference(resolution_lifted,[status(thm)],[c_12,c_31]) ).
% 7.63/1.51  
% 7.63/1.51  cnf(c_746,plain,
% 7.63/1.51      ( k1_yellow_0(sK3,k1_xboole_0) = k3_yellow_0(sK3) ),
% 7.63/1.51      inference(unflattening,[status(thm)],[c_745]) ).
% 7.63/1.51  
% 7.63/1.51  cnf(c_13,plain,
% 7.63/1.51      ( m1_subset_1(k1_yellow_0(X0,X1),u1_struct_0(X0))
% 7.63/1.51      | ~ l1_orders_2(X0) ),
% 7.63/1.51      inference(cnf_transformation,[],[f70]) ).
% 7.63/1.51  
% 7.63/1.51  cnf(c_736,plain,
% 7.63/1.51      ( m1_subset_1(k1_yellow_0(X0,X1),u1_struct_0(X0)) | sK3 != X0 ),
% 7.63/1.51      inference(resolution_lifted,[status(thm)],[c_13,c_31]) ).
% 7.63/1.51  
% 7.63/1.51  cnf(c_737,plain,
% 7.63/1.51      ( m1_subset_1(k1_yellow_0(sK3,X0),u1_struct_0(sK3)) ),
% 7.63/1.51      inference(unflattening,[status(thm)],[c_736]) ).
% 7.63/1.51  
% 7.63/1.51  cnf(c_2197,plain,
% 7.63/1.51      ( m1_subset_1(k1_yellow_0(sK3,X0),u1_struct_0(sK3)) = iProver_top ),
% 7.63/1.51      inference(predicate_to_equality,[status(thm)],[c_737]) ).
% 7.63/1.51  
% 7.63/1.51  cnf(c_2447,plain,
% 7.63/1.51      ( m1_subset_1(k3_yellow_0(sK3),u1_struct_0(sK3)) = iProver_top ),
% 7.63/1.51      inference(superposition,[status(thm)],[c_746,c_2197]) ).
% 7.63/1.51  
% 7.63/1.51  cnf(c_2479,plain,
% 7.63/1.51      ( k1_yellow_0(sK3,k5_waybel_0(sK3,k3_yellow_0(sK3))) = k3_yellow_0(sK3) ),
% 7.63/1.51      inference(superposition,[status(thm)],[c_2447,c_2201]) ).
% 7.63/1.51  
% 7.63/1.51  cnf(c_2478,plain,
% 7.63/1.51      ( k1_yellow_0(sK3,k5_waybel_0(sK3,k1_yellow_0(sK3,X0))) = k1_yellow_0(sK3,X0) ),
% 7.63/1.51      inference(superposition,[status(thm)],[c_2197,c_2201]) ).
% 7.63/1.51  
% 7.63/1.51  cnf(c_14,plain,
% 7.63/1.51      ( r1_orders_2(X0,k1_yellow_0(X0,X1),k1_yellow_0(X0,X2))
% 7.63/1.51      | ~ r1_yellow_0(X0,X2)
% 7.63/1.51      | ~ r1_yellow_0(X0,X1)
% 7.63/1.51      | ~ r1_tarski(X1,X2)
% 7.63/1.51      | ~ l1_orders_2(X0) ),
% 7.63/1.51      inference(cnf_transformation,[],[f71]) ).
% 7.63/1.51  
% 7.63/1.51  cnf(c_718,plain,
% 7.63/1.51      ( r1_orders_2(X0,k1_yellow_0(X0,X1),k1_yellow_0(X0,X2))
% 7.63/1.51      | ~ r1_yellow_0(X0,X2)
% 7.63/1.51      | ~ r1_yellow_0(X0,X1)
% 7.63/1.51      | ~ r1_tarski(X1,X2)
% 7.63/1.51      | sK3 != X0 ),
% 7.63/1.51      inference(resolution_lifted,[status(thm)],[c_14,c_31]) ).
% 7.63/1.51  
% 7.63/1.51  cnf(c_719,plain,
% 7.63/1.51      ( r1_orders_2(sK3,k1_yellow_0(sK3,X0),k1_yellow_0(sK3,X1))
% 7.63/1.51      | ~ r1_yellow_0(sK3,X0)
% 7.63/1.51      | ~ r1_yellow_0(sK3,X1)
% 7.63/1.51      | ~ r1_tarski(X0,X1) ),
% 7.63/1.51      inference(unflattening,[status(thm)],[c_718]) ).
% 7.63/1.51  
% 7.63/1.51  cnf(c_2198,plain,
% 7.63/1.51      ( r1_orders_2(sK3,k1_yellow_0(sK3,X0),k1_yellow_0(sK3,X1)) = iProver_top
% 7.63/1.51      | r1_yellow_0(sK3,X0) != iProver_top
% 7.63/1.51      | r1_yellow_0(sK3,X1) != iProver_top
% 7.63/1.51      | r1_tarski(X0,X1) != iProver_top ),
% 7.63/1.51      inference(predicate_to_equality,[status(thm)],[c_719]) ).
% 7.63/1.51  
% 7.63/1.51  cnf(c_3266,plain,
% 7.63/1.51      ( r1_orders_2(sK3,k1_yellow_0(sK3,X0),k1_yellow_0(sK3,X1)) = iProver_top
% 7.63/1.51      | r1_yellow_0(sK3,X1) != iProver_top
% 7.63/1.51      | r1_yellow_0(sK3,k5_waybel_0(sK3,k1_yellow_0(sK3,X0))) != iProver_top
% 7.63/1.51      | r1_tarski(k5_waybel_0(sK3,k1_yellow_0(sK3,X0)),X1) != iProver_top ),
% 7.63/1.51      inference(superposition,[status(thm)],[c_2478,c_2198]) ).
% 7.63/1.51  
% 7.63/1.51  cnf(c_738,plain,
% 7.63/1.51      ( m1_subset_1(k1_yellow_0(sK3,X0),u1_struct_0(sK3)) = iProver_top ),
% 7.63/1.51      inference(predicate_to_equality,[status(thm)],[c_737]) ).
% 7.63/1.51  
% 7.63/1.51  cnf(c_23,plain,
% 7.63/1.51      ( r1_yellow_0(X0,k5_waybel_0(X0,X1))
% 7.63/1.51      | ~ m1_subset_1(X1,u1_struct_0(X0))
% 7.63/1.51      | ~ v3_orders_2(X0)
% 7.63/1.51      | ~ v4_orders_2(X0)
% 7.63/1.51      | v2_struct_0(X0)
% 7.63/1.51      | ~ v5_orders_2(X0)
% 7.63/1.51      | ~ l1_orders_2(X0) ),
% 7.63/1.51      inference(cnf_transformation,[],[f79]) ).
% 7.63/1.51  
% 7.63/1.51  cnf(c_558,plain,
% 7.63/1.51      ( r1_yellow_0(X0,k5_waybel_0(X0,X1))
% 7.63/1.51      | ~ m1_subset_1(X1,u1_struct_0(X0))
% 7.63/1.51      | ~ v3_orders_2(X0)
% 7.63/1.51      | ~ v4_orders_2(X0)
% 7.63/1.51      | v2_struct_0(X0)
% 7.63/1.51      | ~ l1_orders_2(X0)
% 7.63/1.51      | sK3 != X0 ),
% 7.63/1.51      inference(resolution_lifted,[status(thm)],[c_23,c_33]) ).
% 7.63/1.51  
% 7.63/1.51  cnf(c_559,plain,
% 7.63/1.51      ( r1_yellow_0(sK3,k5_waybel_0(sK3,X0))
% 7.63/1.51      | ~ m1_subset_1(X0,u1_struct_0(sK3))
% 7.63/1.51      | ~ v3_orders_2(sK3)
% 7.63/1.51      | ~ v4_orders_2(sK3)
% 7.63/1.51      | v2_struct_0(sK3)
% 7.63/1.51      | ~ l1_orders_2(sK3) ),
% 7.63/1.51      inference(unflattening,[status(thm)],[c_558]) ).
% 7.63/1.51  
% 7.63/1.51  cnf(c_563,plain,
% 7.63/1.51      ( r1_yellow_0(sK3,k5_waybel_0(sK3,X0))
% 7.63/1.51      | ~ m1_subset_1(X0,u1_struct_0(sK3)) ),
% 7.63/1.51      inference(global_propositional_subsumption,
% 7.63/1.51                [status(thm)],
% 7.63/1.51                [c_559,c_36,c_35,c_34,c_31]) ).
% 7.63/1.51  
% 7.63/1.51  cnf(c_2407,plain,
% 7.63/1.51      ( r1_yellow_0(sK3,k5_waybel_0(sK3,k1_yellow_0(sK3,X0)))
% 7.63/1.51      | ~ m1_subset_1(k1_yellow_0(sK3,X0),u1_struct_0(sK3)) ),
% 7.63/1.51      inference(instantiation,[status(thm)],[c_563]) ).
% 7.63/1.51  
% 7.63/1.51  cnf(c_2408,plain,
% 7.63/1.51      ( r1_yellow_0(sK3,k5_waybel_0(sK3,k1_yellow_0(sK3,X0))) = iProver_top
% 7.63/1.51      | m1_subset_1(k1_yellow_0(sK3,X0),u1_struct_0(sK3)) != iProver_top ),
% 7.63/1.51      inference(predicate_to_equality,[status(thm)],[c_2407]) ).
% 7.63/1.51  
% 7.63/1.51  cnf(c_4312,plain,
% 7.63/1.51      ( r1_yellow_0(sK3,X1) != iProver_top
% 7.63/1.51      | r1_orders_2(sK3,k1_yellow_0(sK3,X0),k1_yellow_0(sK3,X1)) = iProver_top
% 7.63/1.51      | r1_tarski(k5_waybel_0(sK3,k1_yellow_0(sK3,X0)),X1) != iProver_top ),
% 7.63/1.51      inference(global_propositional_subsumption,
% 7.63/1.51                [status(thm)],
% 7.63/1.51                [c_3266,c_738,c_2408]) ).
% 7.63/1.51  
% 7.63/1.51  cnf(c_4313,plain,
% 7.63/1.51      ( r1_orders_2(sK3,k1_yellow_0(sK3,X0),k1_yellow_0(sK3,X1)) = iProver_top
% 7.63/1.51      | r1_yellow_0(sK3,X1) != iProver_top
% 7.63/1.51      | r1_tarski(k5_waybel_0(sK3,k1_yellow_0(sK3,X0)),X1) != iProver_top ),
% 7.63/1.51      inference(renaming,[status(thm)],[c_4312]) ).
% 7.63/1.51  
% 7.63/1.51  cnf(c_21,plain,
% 7.63/1.51      ( ~ r1_orders_2(X0,X1,X2)
% 7.63/1.51      | ~ v13_waybel_0(X3,X0)
% 7.63/1.51      | ~ m1_subset_1(X2,u1_struct_0(X0))
% 7.63/1.51      | ~ m1_subset_1(X1,u1_struct_0(X0))
% 7.63/1.51      | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))
% 7.63/1.51      | ~ r2_hidden(X1,X3)
% 7.63/1.51      | r2_hidden(X2,X3)
% 7.63/1.51      | ~ l1_orders_2(X0) ),
% 7.63/1.51      inference(cnf_transformation,[],[f73]) ).
% 7.63/1.51  
% 7.63/1.51  cnf(c_678,plain,
% 7.63/1.51      ( ~ r1_orders_2(X0,X1,X2)
% 7.63/1.51      | ~ v13_waybel_0(X3,X0)
% 7.63/1.51      | ~ m1_subset_1(X2,u1_struct_0(X0))
% 7.63/1.51      | ~ m1_subset_1(X1,u1_struct_0(X0))
% 7.63/1.51      | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))
% 7.63/1.51      | ~ r2_hidden(X1,X3)
% 7.63/1.51      | r2_hidden(X2,X3)
% 7.63/1.51      | sK3 != X0 ),
% 7.63/1.51      inference(resolution_lifted,[status(thm)],[c_21,c_31]) ).
% 7.63/1.51  
% 7.63/1.51  cnf(c_679,plain,
% 7.63/1.51      ( ~ r1_orders_2(sK3,X0,X1)
% 7.63/1.51      | ~ v13_waybel_0(X2,sK3)
% 7.63/1.51      | ~ m1_subset_1(X0,u1_struct_0(sK3))
% 7.63/1.51      | ~ m1_subset_1(X1,u1_struct_0(sK3))
% 7.63/1.51      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK3)))
% 7.63/1.51      | ~ r2_hidden(X0,X2)
% 7.63/1.51      | r2_hidden(X1,X2) ),
% 7.63/1.51      inference(unflattening,[status(thm)],[c_678]) ).
% 7.63/1.51  
% 7.63/1.51  cnf(c_695,plain,
% 7.63/1.51      ( ~ r1_orders_2(sK3,X0,X1)
% 7.63/1.51      | ~ v13_waybel_0(X2,sK3)
% 7.63/1.51      | ~ m1_subset_1(X1,u1_struct_0(sK3))
% 7.63/1.51      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK3)))
% 7.63/1.51      | ~ r2_hidden(X0,X2)
% 7.63/1.51      | r2_hidden(X1,X2) ),
% 7.63/1.51      inference(forward_subsumption_resolution,
% 7.63/1.51                [status(thm)],
% 7.63/1.51                [c_679,c_11]) ).
% 7.63/1.51  
% 7.63/1.51  cnf(c_2200,plain,
% 7.63/1.51      ( r1_orders_2(sK3,X0,X1) != iProver_top
% 7.63/1.51      | v13_waybel_0(X2,sK3) != iProver_top
% 7.63/1.51      | m1_subset_1(X1,u1_struct_0(sK3)) != iProver_top
% 7.63/1.51      | m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK3))) != iProver_top
% 7.63/1.51      | r2_hidden(X0,X2) != iProver_top
% 7.63/1.51      | r2_hidden(X1,X2) = iProver_top ),
% 7.63/1.51      inference(predicate_to_equality,[status(thm)],[c_695]) ).
% 7.63/1.51  
% 7.63/1.51  cnf(c_3627,plain,
% 7.63/1.51      ( r1_orders_2(sK3,X0,X1) != iProver_top
% 7.63/1.51      | v13_waybel_0(sK4,sK3) != iProver_top
% 7.63/1.51      | m1_subset_1(X1,u1_struct_0(sK3)) != iProver_top
% 7.63/1.51      | r2_hidden(X0,sK4) != iProver_top
% 7.63/1.51      | r2_hidden(X1,sK4) = iProver_top ),
% 7.63/1.51      inference(superposition,[status(thm)],[c_2209,c_2200]) ).
% 7.63/1.51  
% 7.63/1.51  cnf(c_29,negated_conjecture,
% 7.63/1.51      ( v13_waybel_0(sK4,sK3) ),
% 7.63/1.51      inference(cnf_transformation,[],[f90]) ).
% 7.63/1.51  
% 7.63/1.51  cnf(c_911,plain,
% 7.63/1.51      ( ~ r1_orders_2(sK3,X0,X1)
% 7.63/1.51      | ~ m1_subset_1(X1,u1_struct_0(sK3))
% 7.63/1.51      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK3)))
% 7.63/1.51      | ~ r2_hidden(X0,X2)
% 7.63/1.51      | r2_hidden(X1,X2)
% 7.63/1.51      | sK4 != X2
% 7.63/1.51      | sK3 != sK3 ),
% 7.63/1.51      inference(resolution_lifted,[status(thm)],[c_29,c_695]) ).
% 7.63/1.51  
% 7.63/1.51  cnf(c_912,plain,
% 7.63/1.51      ( ~ r1_orders_2(sK3,X0,X1)
% 7.63/1.51      | ~ m1_subset_1(X1,u1_struct_0(sK3))
% 7.63/1.51      | ~ m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(sK3)))
% 7.63/1.51      | ~ r2_hidden(X0,sK4)
% 7.63/1.51      | r2_hidden(X1,sK4) ),
% 7.63/1.51      inference(unflattening,[status(thm)],[c_911]) ).
% 7.63/1.51  
% 7.63/1.51  cnf(c_913,plain,
% 7.63/1.51      ( r1_orders_2(sK3,X0,X1) != iProver_top
% 7.63/1.51      | m1_subset_1(X1,u1_struct_0(sK3)) != iProver_top
% 7.63/1.51      | m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(sK3))) != iProver_top
% 7.63/1.51      | r2_hidden(X0,sK4) != iProver_top
% 7.63/1.51      | r2_hidden(X1,sK4) = iProver_top ),
% 7.63/1.51      inference(predicate_to_equality,[status(thm)],[c_912]) ).
% 7.63/1.51  
% 7.63/1.51  cnf(c_3834,plain,
% 7.63/1.51      ( r1_orders_2(sK3,X0,X1) != iProver_top
% 7.63/1.51      | m1_subset_1(X1,u1_struct_0(sK3)) != iProver_top
% 7.63/1.51      | r2_hidden(X0,sK4) != iProver_top
% 7.63/1.51      | r2_hidden(X1,sK4) = iProver_top ),
% 7.63/1.51      inference(global_propositional_subsumption,
% 7.63/1.51                [status(thm)],
% 7.63/1.51                [c_3627,c_45,c_913]) ).
% 7.63/1.51  
% 7.63/1.51  cnf(c_4327,plain,
% 7.63/1.51      ( r1_yellow_0(sK3,X0) != iProver_top
% 7.63/1.51      | m1_subset_1(k1_yellow_0(sK3,X0),u1_struct_0(sK3)) != iProver_top
% 7.63/1.51      | r1_tarski(k5_waybel_0(sK3,k1_yellow_0(sK3,X1)),X0) != iProver_top
% 7.63/1.51      | r2_hidden(k1_yellow_0(sK3,X1),sK4) != iProver_top
% 7.63/1.51      | r2_hidden(k1_yellow_0(sK3,X0),sK4) = iProver_top ),
% 7.63/1.51      inference(superposition,[status(thm)],[c_4313,c_3834]) ).
% 7.63/1.51  
% 7.63/1.51  cnf(c_24,plain,
% 7.63/1.51      ( v1_subset_1(X0,X1)
% 7.63/1.51      | ~ m1_subset_1(X0,k1_zfmisc_1(X1))
% 7.63/1.51      | X0 = X1 ),
% 7.63/1.51      inference(cnf_transformation,[],[f82]) ).
% 7.63/1.51  
% 7.63/1.51  cnf(c_361,plain,
% 7.63/1.51      ( v1_subset_1(X0,X1) | ~ r1_tarski(X0,X1) | X0 = X1 ),
% 7.63/1.51      inference(bin_hyper_res,[status(thm)],[c_24,c_278]) ).
% 7.63/1.51  
% 7.63/1.51  cnf(c_26,negated_conjecture,
% 7.63/1.51      ( ~ v1_subset_1(sK4,u1_struct_0(sK3))
% 7.63/1.51      | r2_hidden(k3_yellow_0(sK3),sK4) ),
% 7.63/1.51      inference(cnf_transformation,[],[f93]) ).
% 7.63/1.51  
% 7.63/1.51  cnf(c_281,plain,
% 7.63/1.51      ( ~ v1_subset_1(sK4,u1_struct_0(sK3))
% 7.63/1.51      | r2_hidden(k3_yellow_0(sK3),sK4) ),
% 7.63/1.51      inference(prop_impl,[status(thm)],[c_26]) ).
% 7.63/1.51  
% 7.63/1.51  cnf(c_524,plain,
% 7.63/1.51      ( ~ r1_tarski(X0,X1)
% 7.63/1.51      | r2_hidden(k3_yellow_0(sK3),sK4)
% 7.63/1.51      | X1 = X0
% 7.63/1.51      | u1_struct_0(sK3) != X1
% 7.63/1.51      | sK4 != X0 ),
% 7.63/1.51      inference(resolution_lifted,[status(thm)],[c_361,c_281]) ).
% 7.63/1.51  
% 7.63/1.51  cnf(c_525,plain,
% 7.63/1.51      ( ~ r1_tarski(sK4,u1_struct_0(sK3))
% 7.63/1.51      | r2_hidden(k3_yellow_0(sK3),sK4)
% 7.63/1.51      | u1_struct_0(sK3) = sK4 ),
% 7.63/1.51      inference(unflattening,[status(thm)],[c_524]) ).
% 7.63/1.51  
% 7.63/1.51  cnf(c_526,plain,
% 7.63/1.51      ( u1_struct_0(sK3) = sK4
% 7.63/1.51      | r1_tarski(sK4,u1_struct_0(sK3)) != iProver_top
% 7.63/1.51      | r2_hidden(k3_yellow_0(sK3),sK4) = iProver_top ),
% 7.63/1.51      inference(predicate_to_equality,[status(thm)],[c_525]) ).
% 7.63/1.51  
% 7.63/1.51  cnf(c_2778,plain,
% 7.63/1.51      ( k1_yellow_0(sK3,X0) = k1_yellow_0(sK3,X0) ),
% 7.63/1.51      inference(instantiation,[status(thm)],[c_1542]) ).
% 7.63/1.51  
% 7.63/1.51  cnf(c_1547,plain,
% 7.63/1.51      ( ~ m1_subset_1(X0,X1) | m1_subset_1(X2,X3) | X2 != X0 | X3 != X1 ),
% 7.63/1.51      theory(equality) ).
% 7.63/1.51  
% 7.63/1.51  cnf(c_2457,plain,
% 7.63/1.51      ( m1_subset_1(X0,X1)
% 7.63/1.51      | ~ m1_subset_1(k1_yellow_0(sK3,X2),u1_struct_0(sK3))
% 7.63/1.51      | X0 != k1_yellow_0(sK3,X2)
% 7.63/1.51      | X1 != u1_struct_0(sK3) ),
% 7.63/1.51      inference(instantiation,[status(thm)],[c_1547]) ).
% 7.63/1.51  
% 7.63/1.51  cnf(c_2777,plain,
% 7.63/1.51      ( m1_subset_1(k1_yellow_0(sK3,X0),X1)
% 7.63/1.51      | ~ m1_subset_1(k1_yellow_0(sK3,X0),u1_struct_0(sK3))
% 7.63/1.51      | X1 != u1_struct_0(sK3)
% 7.63/1.51      | k1_yellow_0(sK3,X0) != k1_yellow_0(sK3,X0) ),
% 7.63/1.51      inference(instantiation,[status(thm)],[c_2457]) ).
% 7.63/1.51  
% 7.63/1.51  cnf(c_3139,plain,
% 7.63/1.51      ( ~ m1_subset_1(k1_yellow_0(sK3,X0),u1_struct_0(sK3))
% 7.63/1.51      | m1_subset_1(k1_yellow_0(sK3,X0),sK4)
% 7.63/1.51      | k1_yellow_0(sK3,X0) != k1_yellow_0(sK3,X0)
% 7.63/1.51      | sK4 != u1_struct_0(sK3) ),
% 7.63/1.51      inference(instantiation,[status(thm)],[c_2777]) ).
% 7.63/1.51  
% 7.63/1.51  cnf(c_3141,plain,
% 7.63/1.51      ( k1_yellow_0(sK3,X0) != k1_yellow_0(sK3,X0)
% 7.63/1.51      | sK4 != u1_struct_0(sK3)
% 7.63/1.51      | m1_subset_1(k1_yellow_0(sK3,X0),u1_struct_0(sK3)) != iProver_top
% 7.63/1.51      | m1_subset_1(k1_yellow_0(sK3,X0),sK4) = iProver_top ),
% 7.63/1.51      inference(predicate_to_equality,[status(thm)],[c_3139]) ).
% 7.63/1.51  
% 7.63/1.51  cnf(c_3140,plain,
% 7.63/1.51      ( ~ m1_subset_1(k1_yellow_0(sK3,X0),sK4)
% 7.63/1.51      | r2_hidden(k1_yellow_0(sK3,X0),sK4) ),
% 7.63/1.51      inference(instantiation,[status(thm)],[c_494]) ).
% 7.63/1.51  
% 7.63/1.51  cnf(c_3145,plain,
% 7.63/1.51      ( m1_subset_1(k1_yellow_0(sK3,X0),sK4) != iProver_top
% 7.63/1.51      | r2_hidden(k1_yellow_0(sK3,X0),sK4) = iProver_top ),
% 7.63/1.51      inference(predicate_to_equality,[status(thm)],[c_3140]) ).
% 7.63/1.51  
% 7.63/1.51  cnf(c_2822,plain,
% 7.63/1.51      ( r1_orders_2(sK3,k3_yellow_0(sK3),k1_yellow_0(sK3,X0)) = iProver_top
% 7.63/1.51      | r1_yellow_0(sK3,X0) != iProver_top
% 7.63/1.51      | r1_yellow_0(sK3,k1_xboole_0) != iProver_top
% 7.63/1.51      | r1_tarski(k1_xboole_0,X0) != iProver_top ),
% 7.63/1.51      inference(superposition,[status(thm)],[c_746,c_2198]) ).
% 7.63/1.51  
% 7.63/1.51  cnf(c_37,plain,
% 7.63/1.51      ( v2_struct_0(sK3) != iProver_top ),
% 7.63/1.51      inference(predicate_to_equality,[status(thm)],[c_36]) ).
% 7.63/1.51  
% 7.63/1.51  cnf(c_40,plain,
% 7.63/1.51      ( v5_orders_2(sK3) = iProver_top ),
% 7.63/1.51      inference(predicate_to_equality,[status(thm)],[c_33]) ).
% 7.63/1.51  
% 7.63/1.51  cnf(c_32,negated_conjecture,
% 7.63/1.51      ( v1_yellow_0(sK3) ),
% 7.63/1.51      inference(cnf_transformation,[],[f87]) ).
% 7.63/1.51  
% 7.63/1.51  cnf(c_41,plain,
% 7.63/1.51      ( v1_yellow_0(sK3) = iProver_top ),
% 7.63/1.51      inference(predicate_to_equality,[status(thm)],[c_32]) ).
% 7.63/1.51  
% 7.63/1.51  cnf(c_42,plain,
% 7.63/1.51      ( l1_orders_2(sK3) = iProver_top ),
% 7.63/1.51      inference(predicate_to_equality,[status(thm)],[c_31]) ).
% 7.63/1.51  
% 7.63/1.51  cnf(c_15,plain,
% 7.63/1.51      ( r1_yellow_0(X0,k1_xboole_0)
% 7.63/1.51      | v2_struct_0(X0)
% 7.63/1.51      | ~ v5_orders_2(X0)
% 7.63/1.51      | ~ v1_yellow_0(X0)
% 7.63/1.51      | ~ l1_orders_2(X0) ),
% 7.63/1.51      inference(cnf_transformation,[],[f72]) ).
% 7.63/1.51  
% 7.63/1.51  cnf(c_76,plain,
% 7.63/1.51      ( r1_yellow_0(X0,k1_xboole_0) = iProver_top
% 7.63/1.51      | v2_struct_0(X0) = iProver_top
% 7.63/1.51      | v5_orders_2(X0) != iProver_top
% 7.63/1.51      | v1_yellow_0(X0) != iProver_top
% 7.63/1.51      | l1_orders_2(X0) != iProver_top ),
% 7.63/1.51      inference(predicate_to_equality,[status(thm)],[c_15]) ).
% 7.63/1.51  
% 7.63/1.51  cnf(c_78,plain,
% 7.63/1.51      ( r1_yellow_0(sK3,k1_xboole_0) = iProver_top
% 7.63/1.51      | v2_struct_0(sK3) = iProver_top
% 7.63/1.51      | v5_orders_2(sK3) != iProver_top
% 7.63/1.51      | v1_yellow_0(sK3) != iProver_top
% 7.63/1.51      | l1_orders_2(sK3) != iProver_top ),
% 7.63/1.51      inference(instantiation,[status(thm)],[c_76]) ).
% 7.63/1.51  
% 7.63/1.51  cnf(c_5,plain,
% 7.63/1.51      ( r1_tarski(k1_xboole_0,X0) ),
% 7.63/1.51      inference(cnf_transformation,[],[f62]) ).
% 7.63/1.51  
% 7.63/1.51  cnf(c_104,plain,
% 7.63/1.51      ( r1_tarski(k1_xboole_0,X0) = iProver_top ),
% 7.63/1.51      inference(predicate_to_equality,[status(thm)],[c_5]) ).
% 7.63/1.51  
% 7.63/1.51  cnf(c_2922,plain,
% 7.63/1.51      ( r1_orders_2(sK3,k3_yellow_0(sK3),k1_yellow_0(sK3,X0)) = iProver_top
% 7.63/1.51      | r1_yellow_0(sK3,X0) != iProver_top ),
% 7.63/1.51      inference(global_propositional_subsumption,
% 7.63/1.51                [status(thm)],
% 7.63/1.51                [c_2822,c_37,c_40,c_41,c_42,c_78,c_104]) ).
% 7.63/1.51  
% 7.63/1.51  cnf(c_3265,plain,
% 7.63/1.51      ( r1_orders_2(sK3,k3_yellow_0(sK3),k1_yellow_0(sK3,X0)) = iProver_top
% 7.63/1.51      | r1_yellow_0(sK3,k5_waybel_0(sK3,k1_yellow_0(sK3,X0))) != iProver_top ),
% 7.63/1.51      inference(superposition,[status(thm)],[c_2478,c_2922]) ).
% 7.63/1.51  
% 7.63/1.51  cnf(c_3514,plain,
% 7.63/1.51      ( r1_orders_2(sK3,k3_yellow_0(sK3),k1_yellow_0(sK3,X0)) = iProver_top ),
% 7.63/1.51      inference(global_propositional_subsumption,
% 7.63/1.51                [status(thm)],
% 7.63/1.51                [c_3265,c_738,c_2408]) ).
% 7.63/1.51  
% 7.63/1.51  cnf(c_3844,plain,
% 7.63/1.51      ( m1_subset_1(k1_yellow_0(sK3,X0),u1_struct_0(sK3)) != iProver_top
% 7.63/1.51      | r2_hidden(k1_yellow_0(sK3,X0),sK4) = iProver_top
% 7.63/1.51      | r2_hidden(k3_yellow_0(sK3),sK4) != iProver_top ),
% 7.63/1.51      inference(superposition,[status(thm)],[c_3514,c_3834]) ).
% 7.63/1.51  
% 7.63/1.51  cnf(c_3944,plain,
% 7.63/1.51      ( r2_hidden(k1_yellow_0(sK3,X0),sK4) = iProver_top
% 7.63/1.51      | r2_hidden(k3_yellow_0(sK3),sK4) != iProver_top ),
% 7.63/1.51      inference(global_propositional_subsumption,
% 7.63/1.51                [status(thm)],
% 7.63/1.51                [c_3844,c_738]) ).
% 7.63/1.51  
% 7.63/1.51  cnf(c_1543,plain,( X0 != X1 | X2 != X1 | X2 = X0 ),theory(equality) ).
% 7.63/1.51  
% 7.63/1.51  cnf(c_2600,plain,
% 7.63/1.51      ( X0 != X1 | X0 = u1_struct_0(sK3) | u1_struct_0(sK3) != X1 ),
% 7.63/1.51      inference(instantiation,[status(thm)],[c_1543]) ).
% 7.63/1.51  
% 7.63/1.51  cnf(c_3359,plain,
% 7.63/1.51      ( u1_struct_0(sK3) != X0 | sK4 != X0 | sK4 = u1_struct_0(sK3) ),
% 7.63/1.51      inference(instantiation,[status(thm)],[c_2600]) ).
% 7.63/1.51  
% 7.63/1.51  cnf(c_4807,plain,
% 7.63/1.51      ( u1_struct_0(sK3) != sK4 | sK4 = u1_struct_0(sK3) | sK4 != sK4 ),
% 7.63/1.51      inference(instantiation,[status(thm)],[c_3359]) ).
% 7.63/1.51  
% 7.63/1.51  cnf(c_4982,plain,
% 7.63/1.51      ( r2_hidden(k1_yellow_0(sK3,X0),sK4) = iProver_top ),
% 7.63/1.51      inference(global_propositional_subsumption,
% 7.63/1.51                [status(thm)],
% 7.63/1.51                [c_4327,c_45,c_526,c_738,c_2439,c_2506,c_2778,c_3141,
% 7.63/1.51                 c_3145,c_3944,c_4807]) ).
% 7.63/1.51  
% 7.63/1.51  cnf(c_4991,plain,
% 7.63/1.51      ( r2_hidden(k3_yellow_0(sK3),sK4) = iProver_top ),
% 7.63/1.51      inference(superposition,[status(thm)],[c_2479,c_4982]) ).
% 7.63/1.51  
% 7.63/1.51  cnf(c_1545,plain,
% 7.63/1.51      ( ~ r1_tarski(X0,X1) | r1_tarski(X2,X3) | X2 != X0 | X3 != X1 ),
% 7.63/1.51      theory(equality) ).
% 7.63/1.51  
% 7.63/1.51  cnf(c_4385,plain,
% 7.63/1.51      ( ~ r1_tarski(X0,X1) | r1_tarski(X2,sK4) | X2 != X0 | sK4 != X1 ),
% 7.63/1.51      inference(instantiation,[status(thm)],[c_1545]) ).
% 7.63/1.51  
% 7.63/1.51  cnf(c_6513,plain,
% 7.63/1.51      ( ~ r1_tarski(X0,X1)
% 7.63/1.51      | r1_tarski(u1_struct_0(sK3),sK4)
% 7.63/1.51      | u1_struct_0(sK3) != X0
% 7.63/1.51      | sK4 != X1 ),
% 7.63/1.51      inference(instantiation,[status(thm)],[c_4385]) ).
% 7.63/1.51  
% 7.63/1.51  cnf(c_16220,plain,
% 7.63/1.51      ( ~ r1_tarski(X0,sK4)
% 7.63/1.51      | r1_tarski(u1_struct_0(sK3),sK4)
% 7.63/1.51      | u1_struct_0(sK3) != X0
% 7.63/1.51      | sK4 != sK4 ),
% 7.63/1.51      inference(instantiation,[status(thm)],[c_6513]) ).
% 7.63/1.51  
% 7.63/1.51  cnf(c_16221,plain,
% 7.63/1.51      ( u1_struct_0(sK3) != X0
% 7.63/1.51      | sK4 != sK4
% 7.63/1.51      | r1_tarski(X0,sK4) != iProver_top
% 7.63/1.51      | r1_tarski(u1_struct_0(sK3),sK4) = iProver_top ),
% 7.63/1.51      inference(predicate_to_equality,[status(thm)],[c_16220]) ).
% 7.63/1.51  
% 7.63/1.51  cnf(c_17388,plain,
% 7.63/1.51      ( r1_tarski(X0,sK4) != iProver_top
% 7.63/1.51      | k1_yellow_0(sK3,k5_waybel_0(sK3,sK0(X0,u1_struct_0(sK3)))) = sK0(X0,u1_struct_0(sK3)) ),
% 7.63/1.51      inference(global_propositional_subsumption,
% 7.63/1.51                [status(thm)],
% 7.63/1.51                [c_16602,c_45,c_539,c_2439,c_2506,c_2528,c_2530,c_3363,
% 7.63/1.51                 c_3899,c_4892,c_4991,c_16221]) ).
% 7.63/1.51  
% 7.63/1.51  cnf(c_17389,plain,
% 7.63/1.51      ( k1_yellow_0(sK3,k5_waybel_0(sK3,sK0(X0,u1_struct_0(sK3)))) = sK0(X0,u1_struct_0(sK3))
% 7.63/1.51      | r1_tarski(X0,sK4) != iProver_top ),
% 7.63/1.51      inference(renaming,[status(thm)],[c_17388]) ).
% 7.63/1.51  
% 7.63/1.51  cnf(c_17396,plain,
% 7.63/1.51      ( k1_yellow_0(sK3,k5_waybel_0(sK3,sK0(sK4,u1_struct_0(sK3)))) = sK0(sK4,u1_struct_0(sK3)) ),
% 7.63/1.51      inference(superposition,[status(thm)],[c_2215,c_17389]) ).
% 7.63/1.51  
% 7.63/1.51  cnf(c_19618,plain,
% 7.63/1.51      ( r2_hidden(sK0(sK4,u1_struct_0(sK3)),sK4) = iProver_top ),
% 7.63/1.51      inference(superposition,[status(thm)],[c_17396,c_4982]) ).
% 7.63/1.51  
% 7.63/1.51  cnf(c_15413,plain,
% 7.63/1.51      ( u1_struct_0(sK3) = sK4
% 7.63/1.51      | r1_tarski(sK4,sK4) != iProver_top
% 7.63/1.51      | r2_hidden(sK0(sK4,u1_struct_0(sK3)),u1_struct_0(sK3)) = iProver_top
% 7.63/1.51      | r2_hidden(sK0(sK4,u1_struct_0(sK3)),sK4) != iProver_top ),
% 7.63/1.51      inference(superposition,[status(thm)],[c_14986,c_3899]) ).
% 7.63/1.51  
% 7.63/1.51  cnf(c_15475,plain,
% 7.63/1.51      ( u1_struct_0(sK3) = sK4
% 7.63/1.51      | r1_tarski(sK4,sK4) != iProver_top
% 7.63/1.51      | r2_hidden(sK0(sK4,u1_struct_0(sK3)),u1_struct_0(sK3)) = iProver_top ),
% 7.63/1.51      inference(forward_subsumption_resolution,
% 7.63/1.51                [status(thm)],
% 7.63/1.51                [c_15413,c_14986]) ).
% 7.63/1.51  
% 7.63/1.51  cnf(c_6044,plain,
% 7.63/1.51      ( r1_tarski(sK4,sK4) ),
% 7.63/1.51      inference(instantiation,[status(thm)],[c_4]) ).
% 7.63/1.51  
% 7.63/1.51  cnf(c_6049,plain,
% 7.63/1.51      ( r1_tarski(sK4,sK4) = iProver_top ),
% 7.63/1.51      inference(predicate_to_equality,[status(thm)],[c_6044]) ).
% 7.63/1.51  
% 7.63/1.51  cnf(c_2496,plain,
% 7.63/1.51      ( ~ r2_hidden(sK0(sK4,X0),X0)
% 7.63/1.51      | ~ r2_hidden(sK0(sK4,X0),sK4)
% 7.63/1.51      | X0 = sK4 ),
% 7.63/1.51      inference(instantiation,[status(thm)],[c_0]) ).
% 7.63/1.51  
% 7.63/1.51  cnf(c_2882,plain,
% 7.63/1.51      ( ~ r2_hidden(sK0(sK4,u1_struct_0(sK3)),u1_struct_0(sK3))
% 7.63/1.51      | ~ r2_hidden(sK0(sK4,u1_struct_0(sK3)),sK4)
% 7.63/1.51      | u1_struct_0(sK3) = sK4 ),
% 7.63/1.51      inference(instantiation,[status(thm)],[c_2496]) ).
% 7.63/1.51  
% 7.63/1.51  cnf(c_2893,plain,
% 7.63/1.51      ( u1_struct_0(sK3) = sK4
% 7.63/1.51      | r2_hidden(sK0(sK4,u1_struct_0(sK3)),u1_struct_0(sK3)) != iProver_top
% 7.63/1.51      | r2_hidden(sK0(sK4,u1_struct_0(sK3)),sK4) != iProver_top ),
% 7.63/1.51      inference(predicate_to_equality,[status(thm)],[c_2882]) ).
% 7.63/1.51  
% 7.63/1.51  cnf(contradiction,plain,
% 7.63/1.51      ( $false ),
% 7.63/1.51      inference(minisat,
% 7.63/1.51                [status(thm)],
% 7.63/1.51                [c_19618,c_15475,c_6049,c_4991,c_4807,c_2893,c_2530,
% 7.63/1.51                 c_2528,c_2506,c_539]) ).
% 7.63/1.51  
% 7.63/1.51  
% 7.63/1.51  % SZS output end CNFRefutation for theBenchmark.p
% 7.63/1.51  
% 7.63/1.51  ------                               Statistics
% 7.63/1.51  
% 7.63/1.51  ------ General
% 7.63/1.51  
% 7.63/1.51  abstr_ref_over_cycles:                  0
% 7.63/1.51  abstr_ref_under_cycles:                 0
% 7.63/1.51  gc_basic_clause_elim:                   0
% 7.63/1.51  forced_gc_time:                         0
% 7.63/1.51  parsing_time:                           0.008
% 7.63/1.51  unif_index_cands_time:                  0.
% 7.63/1.51  unif_index_add_time:                    0.
% 7.63/1.51  orderings_time:                         0.
% 7.63/1.51  out_proof_time:                         0.015
% 7.63/1.51  total_time:                             0.544
% 7.63/1.51  num_of_symbols:                         56
% 7.63/1.51  num_of_terms:                           11763
% 7.63/1.51  
% 7.63/1.51  ------ Preprocessing
% 7.63/1.51  
% 7.63/1.51  num_of_splits:                          0
% 7.63/1.51  num_of_split_atoms:                     0
% 7.63/1.51  num_of_reused_defs:                     0
% 7.63/1.51  num_eq_ax_congr_red:                    22
% 7.63/1.51  num_of_sem_filtered_clauses:            1
% 7.63/1.51  num_of_subtypes:                        0
% 7.63/1.51  monotx_restored_types:                  0
% 7.63/1.51  sat_num_of_epr_types:                   0
% 7.63/1.51  sat_num_of_non_cyclic_types:            0
% 7.63/1.51  sat_guarded_non_collapsed_types:        0
% 7.63/1.51  num_pure_diseq_elim:                    0
% 7.63/1.51  simp_replaced_by:                       0
% 7.63/1.51  res_preprocessed:                       148
% 7.63/1.51  prep_upred:                             0
% 7.63/1.51  prep_unflattend:                        44
% 7.63/1.51  smt_new_axioms:                         0
% 7.63/1.51  pred_elim_cands:                        6
% 7.63/1.51  pred_elim:                              8
% 7.63/1.51  pred_elim_cl:                           9
% 7.63/1.51  pred_elim_cycles:                       13
% 7.63/1.51  merged_defs:                            10
% 7.63/1.51  merged_defs_ncl:                        0
% 7.63/1.51  bin_hyper_res:                          12
% 7.63/1.51  prep_cycles:                            4
% 7.63/1.51  pred_elim_time:                         0.019
% 7.63/1.51  splitting_time:                         0.
% 7.63/1.51  sem_filter_time:                        0.
% 7.63/1.51  monotx_time:                            0.001
% 7.63/1.51  subtype_inf_time:                       0.
% 7.63/1.51  
% 7.63/1.51  ------ Problem properties
% 7.63/1.51  
% 7.63/1.51  clauses:                                27
% 7.63/1.51  conjectures:                            2
% 7.63/1.51  epr:                                    8
% 7.63/1.51  horn:                                   21
% 7.63/1.51  ground:                                 6
% 7.63/1.51  unary:                                  7
% 7.63/1.51  binary:                                 6
% 7.63/1.51  lits:                                   65
% 7.63/1.51  lits_eq:                                7
% 7.63/1.51  fd_pure:                                0
% 7.63/1.51  fd_pseudo:                              0
% 7.63/1.51  fd_cond:                                0
% 7.63/1.51  fd_pseudo_cond:                         3
% 7.63/1.51  ac_symbols:                             0
% 7.63/1.51  
% 7.63/1.51  ------ Propositional Solver
% 7.63/1.51  
% 7.63/1.51  prop_solver_calls:                      29
% 7.63/1.51  prop_fast_solver_calls:                 1635
% 7.63/1.51  smt_solver_calls:                       0
% 7.63/1.51  smt_fast_solver_calls:                  0
% 7.63/1.51  prop_num_of_clauses:                    5867
% 7.63/1.51  prop_preprocess_simplified:             10996
% 7.63/1.51  prop_fo_subsumed:                       59
% 7.63/1.51  prop_solver_time:                       0.
% 7.63/1.51  smt_solver_time:                        0.
% 7.63/1.51  smt_fast_solver_time:                   0.
% 7.63/1.51  prop_fast_solver_time:                  0.
% 7.63/1.51  prop_unsat_core_time:                   0.
% 7.63/1.51  
% 7.63/1.51  ------ QBF
% 7.63/1.51  
% 7.63/1.51  qbf_q_res:                              0
% 7.63/1.51  qbf_num_tautologies:                    0
% 7.63/1.51  qbf_prep_cycles:                        0
% 7.63/1.51  
% 7.63/1.51  ------ BMC1
% 7.63/1.51  
% 7.63/1.51  bmc1_current_bound:                     -1
% 7.63/1.51  bmc1_last_solved_bound:                 -1
% 7.63/1.51  bmc1_unsat_core_size:                   -1
% 7.63/1.51  bmc1_unsat_core_parents_size:           -1
% 7.63/1.51  bmc1_merge_next_fun:                    0
% 7.63/1.51  bmc1_unsat_core_clauses_time:           0.
% 7.63/1.51  
% 7.63/1.51  ------ Instantiation
% 7.63/1.51  
% 7.63/1.51  inst_num_of_clauses:                    1268
% 7.63/1.51  inst_num_in_passive:                    115
% 7.63/1.51  inst_num_in_active:                     607
% 7.63/1.51  inst_num_in_unprocessed:                547
% 7.63/1.51  inst_num_of_loops:                      800
% 7.63/1.51  inst_num_of_learning_restarts:          0
% 7.63/1.51  inst_num_moves_active_passive:          190
% 7.63/1.51  inst_lit_activity:                      0
% 7.63/1.51  inst_lit_activity_moves:                0
% 7.63/1.51  inst_num_tautologies:                   0
% 7.63/1.51  inst_num_prop_implied:                  0
% 7.63/1.51  inst_num_existing_simplified:           0
% 7.63/1.51  inst_num_eq_res_simplified:             0
% 7.63/1.51  inst_num_child_elim:                    0
% 7.63/1.51  inst_num_of_dismatching_blockings:      859
% 7.63/1.51  inst_num_of_non_proper_insts:           1770
% 7.63/1.51  inst_num_of_duplicates:                 0
% 7.63/1.51  inst_inst_num_from_inst_to_res:         0
% 7.63/1.51  inst_dismatching_checking_time:         0.
% 7.63/1.51  
% 7.63/1.51  ------ Resolution
% 7.63/1.51  
% 7.63/1.51  res_num_of_clauses:                     0
% 7.63/1.51  res_num_in_passive:                     0
% 7.63/1.51  res_num_in_active:                      0
% 7.63/1.51  res_num_of_loops:                       152
% 7.63/1.51  res_forward_subset_subsumed:            145
% 7.63/1.51  res_backward_subset_subsumed:           2
% 7.63/1.51  res_forward_subsumed:                   0
% 7.63/1.51  res_backward_subsumed:                  0
% 7.63/1.51  res_forward_subsumption_resolution:     7
% 7.63/1.51  res_backward_subsumption_resolution:    0
% 7.63/1.51  res_clause_to_clause_subsumption:       2636
% 7.63/1.51  res_orphan_elimination:                 0
% 7.63/1.51  res_tautology_del:                      151
% 7.63/1.51  res_num_eq_res_simplified:              0
% 7.63/1.51  res_num_sel_changes:                    0
% 7.63/1.51  res_moves_from_active_to_pass:          0
% 7.63/1.51  
% 7.63/1.51  ------ Superposition
% 7.63/1.51  
% 7.63/1.51  sup_time_total:                         0.
% 7.63/1.51  sup_time_generating:                    0.
% 7.63/1.51  sup_time_sim_full:                      0.
% 7.63/1.51  sup_time_sim_immed:                     0.
% 7.63/1.51  
% 7.63/1.51  sup_num_of_clauses:                     548
% 7.63/1.51  sup_num_in_active:                      154
% 7.63/1.51  sup_num_in_passive:                     394
% 7.63/1.51  sup_num_of_loops:                       159
% 7.63/1.51  sup_fw_superposition:                   297
% 7.63/1.51  sup_bw_superposition:                   617
% 7.63/1.51  sup_immediate_simplified:               183
% 7.63/1.51  sup_given_eliminated:                   0
% 7.63/1.51  comparisons_done:                       0
% 7.63/1.51  comparisons_avoided:                    28
% 7.63/1.51  
% 7.63/1.51  ------ Simplifications
% 7.63/1.51  
% 7.63/1.51  
% 7.63/1.51  sim_fw_subset_subsumed:                 42
% 7.63/1.51  sim_bw_subset_subsumed:                 14
% 7.63/1.51  sim_fw_subsumed:                        43
% 7.63/1.51  sim_bw_subsumed:                        28
% 7.63/1.51  sim_fw_subsumption_res:                 5
% 7.63/1.51  sim_bw_subsumption_res:                 0
% 7.63/1.51  sim_tautology_del:                      30
% 7.63/1.51  sim_eq_tautology_del:                   38
% 7.63/1.51  sim_eq_res_simp:                        4
% 7.63/1.51  sim_fw_demodulated:                     8
% 7.63/1.51  sim_bw_demodulated:                     0
% 7.63/1.51  sim_light_normalised:                   69
% 7.63/1.51  sim_joinable_taut:                      0
% 7.63/1.51  sim_joinable_simp:                      0
% 7.63/1.51  sim_ac_normalised:                      0
% 7.63/1.51  sim_smt_subsumption:                    0
% 7.63/1.51  
%------------------------------------------------------------------------------
