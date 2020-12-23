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
% DateTime   : Thu Dec  3 12:28:07 EST 2020

% Result     : Theorem 3.92s
% Output     : CNFRefutation 3.92s
% Verified   : 
% Statistics : Number of formulae       :  135 ( 493 expanded)
%              Number of clauses        :   67 ( 130 expanded)
%              Number of leaves         :   16 ( 105 expanded)
%              Depth                    :   18
%              Number of atoms          :  497 (2687 expanded)
%              Number of equality atoms :  129 ( 473 expanded)
%              Maximal formula depth    :   14 (   5 average)
%              Maximal clause size      :   14 (   2 average)
%              Maximal term depth       :    5 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f3,axiom,(
    ! [X0,X1] :
      ( X0 = X1
    <=> ( r1_tarski(X1,X0)
        & r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f32,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(nnf_transformation,[],[f3])).

fof(f33,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(flattening,[],[f32])).

fof(f50,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | X0 != X1 ) ),
    inference(cnf_transformation,[],[f33])).

fof(f84,plain,(
    ! [X1] : r1_tarski(X1,X1) ),
    inference(equality_resolution,[],[f50])).

fof(f5,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f34,plain,(
    ! [X0,X1] :
      ( ( m1_subset_1(X0,k1_zfmisc_1(X1))
        | ~ r1_tarski(X0,X1) )
      & ( r1_tarski(X0,X1)
        | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ) ) ),
    inference(nnf_transformation,[],[f5])).

fof(f55,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f34])).

fof(f7,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
     => ( l1_orders_2(g1_orders_2(X0,X1))
        & v1_orders_2(g1_orders_2(X0,X1)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f18,plain,(
    ! [X0,X1] :
      ( ( l1_orders_2(g1_orders_2(X0,X1))
        & v1_orders_2(g1_orders_2(X0,X1)) )
      | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f58,plain,(
    ! [X0,X1] :
      ( l1_orders_2(g1_orders_2(X0,X1))
      | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f6,axiom,(
    ! [X0] :
      ( l1_orders_2(X0)
     => ( v1_orders_2(X0)
       => g1_orders_2(u1_struct_0(X0),u1_orders_2(X0)) = X0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f16,plain,(
    ! [X0] :
      ( g1_orders_2(u1_struct_0(X0),u1_orders_2(X0)) = X0
      | ~ v1_orders_2(X0)
      | ~ l1_orders_2(X0) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f17,plain,(
    ! [X0] :
      ( g1_orders_2(u1_struct_0(X0),u1_orders_2(X0)) = X0
      | ~ v1_orders_2(X0)
      | ~ l1_orders_2(X0) ) ),
    inference(flattening,[],[f16])).

fof(f56,plain,(
    ! [X0] :
      ( g1_orders_2(u1_struct_0(X0),u1_orders_2(X0)) = X0
      | ~ v1_orders_2(X0)
      | ~ l1_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f57,plain,(
    ! [X0,X1] :
      ( v1_orders_2(g1_orders_2(X0,X1))
      | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f8,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
     => ! [X2,X3] :
          ( g1_orders_2(X0,X1) = g1_orders_2(X2,X3)
         => ( X1 = X3
            & X0 = X2 ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f19,plain,(
    ! [X0,X1] :
      ( ! [X2,X3] :
          ( ( X1 = X3
            & X0 = X2 )
          | g1_orders_2(X0,X1) != g1_orders_2(X2,X3) )
      | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f59,plain,(
    ! [X2,X0,X3,X1] :
      ( X0 = X2
      | g1_orders_2(X0,X1) != g1_orders_2(X2,X3)
      | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f9,axiom,(
    ! [X0] :
      ( l1_orders_2(X0)
     => m1_subset_1(k3_yellow_0(X0),u1_struct_0(X0)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f20,plain,(
    ! [X0] :
      ( m1_subset_1(k3_yellow_0(X0),u1_struct_0(X0))
      | ~ l1_orders_2(X0) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f61,plain,(
    ! [X0] :
      ( m1_subset_1(k3_yellow_0(X0),u1_struct_0(X0))
      | ~ l1_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f2,axiom,(
    ! [X0,X1,X2] :
      ( k4_xboole_0(X0,X1) = X2
    <=> ! [X3] :
          ( r2_hidden(X3,X2)
        <=> ( ~ r2_hidden(X3,X1)
            & r2_hidden(X3,X0) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f27,plain,(
    ! [X0,X1,X2] :
      ( ( k4_xboole_0(X0,X1) = X2
        | ? [X3] :
            ( ( r2_hidden(X3,X1)
              | ~ r2_hidden(X3,X0)
              | ~ r2_hidden(X3,X2) )
            & ( ( ~ r2_hidden(X3,X1)
                & r2_hidden(X3,X0) )
              | r2_hidden(X3,X2) ) ) )
      & ( ! [X3] :
            ( ( r2_hidden(X3,X2)
              | r2_hidden(X3,X1)
              | ~ r2_hidden(X3,X0) )
            & ( ( ~ r2_hidden(X3,X1)
                & r2_hidden(X3,X0) )
              | ~ r2_hidden(X3,X2) ) )
        | k4_xboole_0(X0,X1) != X2 ) ) ),
    inference(nnf_transformation,[],[f2])).

fof(f28,plain,(
    ! [X0,X1,X2] :
      ( ( k4_xboole_0(X0,X1) = X2
        | ? [X3] :
            ( ( r2_hidden(X3,X1)
              | ~ r2_hidden(X3,X0)
              | ~ r2_hidden(X3,X2) )
            & ( ( ~ r2_hidden(X3,X1)
                & r2_hidden(X3,X0) )
              | r2_hidden(X3,X2) ) ) )
      & ( ! [X3] :
            ( ( r2_hidden(X3,X2)
              | r2_hidden(X3,X1)
              | ~ r2_hidden(X3,X0) )
            & ( ( ~ r2_hidden(X3,X1)
                & r2_hidden(X3,X0) )
              | ~ r2_hidden(X3,X2) ) )
        | k4_xboole_0(X0,X1) != X2 ) ) ),
    inference(flattening,[],[f27])).

fof(f29,plain,(
    ! [X0,X1,X2] :
      ( ( k4_xboole_0(X0,X1) = X2
        | ? [X3] :
            ( ( r2_hidden(X3,X1)
              | ~ r2_hidden(X3,X0)
              | ~ r2_hidden(X3,X2) )
            & ( ( ~ r2_hidden(X3,X1)
                & r2_hidden(X3,X0) )
              | r2_hidden(X3,X2) ) ) )
      & ( ! [X4] :
            ( ( r2_hidden(X4,X2)
              | r2_hidden(X4,X1)
              | ~ r2_hidden(X4,X0) )
            & ( ( ~ r2_hidden(X4,X1)
                & r2_hidden(X4,X0) )
              | ~ r2_hidden(X4,X2) ) )
        | k4_xboole_0(X0,X1) != X2 ) ) ),
    inference(rectify,[],[f28])).

fof(f30,plain,(
    ! [X2,X1,X0] :
      ( ? [X3] :
          ( ( r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X0)
            | ~ r2_hidden(X3,X2) )
          & ( ( ~ r2_hidden(X3,X1)
              & r2_hidden(X3,X0) )
            | r2_hidden(X3,X2) ) )
     => ( ( r2_hidden(sK0(X0,X1,X2),X1)
          | ~ r2_hidden(sK0(X0,X1,X2),X0)
          | ~ r2_hidden(sK0(X0,X1,X2),X2) )
        & ( ( ~ r2_hidden(sK0(X0,X1,X2),X1)
            & r2_hidden(sK0(X0,X1,X2),X0) )
          | r2_hidden(sK0(X0,X1,X2),X2) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f31,plain,(
    ! [X0,X1,X2] :
      ( ( k4_xboole_0(X0,X1) = X2
        | ( ( r2_hidden(sK0(X0,X1,X2),X1)
            | ~ r2_hidden(sK0(X0,X1,X2),X0)
            | ~ r2_hidden(sK0(X0,X1,X2),X2) )
          & ( ( ~ r2_hidden(sK0(X0,X1,X2),X1)
              & r2_hidden(sK0(X0,X1,X2),X0) )
            | r2_hidden(sK0(X0,X1,X2),X2) ) ) )
      & ( ! [X4] :
            ( ( r2_hidden(X4,X2)
              | r2_hidden(X4,X1)
              | ~ r2_hidden(X4,X0) )
            & ( ( ~ r2_hidden(X4,X1)
                & r2_hidden(X4,X0) )
              | ~ r2_hidden(X4,X2) ) )
        | k4_xboole_0(X0,X1) != X2 ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f29,f30])).

fof(f47,plain,(
    ! [X2,X0,X1] :
      ( k4_xboole_0(X0,X1) = X2
      | r2_hidden(sK0(X0,X1,X2),X0)
      | r2_hidden(sK0(X0,X1,X2),X2) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f4,axiom,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k6_subset_1(X0,X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f53,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k6_subset_1(X0,X1) ),
    inference(cnf_transformation,[],[f4])).

fof(f76,plain,(
    ! [X2,X0,X1] :
      ( k6_subset_1(X0,X1) = X2
      | r2_hidden(sK0(X0,X1,X2),X0)
      | r2_hidden(sK0(X0,X1,X2),X2) ) ),
    inference(definition_unfolding,[],[f47,f53])).

fof(f48,plain,(
    ! [X2,X0,X1] :
      ( k4_xboole_0(X0,X1) = X2
      | ~ r2_hidden(sK0(X0,X1,X2),X1)
      | r2_hidden(sK0(X0,X1,X2),X2) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f75,plain,(
    ! [X2,X0,X1] :
      ( k6_subset_1(X0,X1) = X2
      | ~ r2_hidden(sK0(X0,X1,X2),X1)
      | r2_hidden(sK0(X0,X1,X2),X2) ) ),
    inference(definition_unfolding,[],[f48,f53])).

fof(f44,plain,(
    ! [X4,X2,X0,X1] :
      ( r2_hidden(X4,X0)
      | ~ r2_hidden(X4,X2)
      | k4_xboole_0(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f31])).

fof(f79,plain,(
    ! [X4,X2,X0,X1] :
      ( r2_hidden(X4,X0)
      | ~ r2_hidden(X4,X2)
      | k6_subset_1(X0,X1) != X2 ) ),
    inference(definition_unfolding,[],[f44,f53])).

fof(f82,plain,(
    ! [X4,X0,X1] :
      ( r2_hidden(X4,X0)
      | ~ r2_hidden(X4,k6_subset_1(X0,X1)) ) ),
    inference(equality_resolution,[],[f79])).

fof(f45,plain,(
    ! [X4,X2,X0,X1] :
      ( ~ r2_hidden(X4,X1)
      | ~ r2_hidden(X4,X2)
      | k4_xboole_0(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f31])).

fof(f78,plain,(
    ! [X4,X2,X0,X1] :
      ( ~ r2_hidden(X4,X1)
      | ~ r2_hidden(X4,X2)
      | k6_subset_1(X0,X1) != X2 ) ),
    inference(definition_unfolding,[],[f45,f53])).

fof(f81,plain,(
    ! [X4,X0,X1] :
      ( ~ r2_hidden(X4,X1)
      | ~ r2_hidden(X4,k6_subset_1(X0,X1)) ) ),
    inference(equality_resolution,[],[f78])).

fof(f11,axiom,(
    ! [X0] :
      ( ( l1_struct_0(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( ( l1_waybel_0(X1,X0)
            & ~ v2_struct_0(X1) )
         => ! [X2] :
              ( r1_waybel_0(X0,X1,X2)
            <=> ~ r2_waybel_0(X0,X1,k6_subset_1(u1_struct_0(X0),X2)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f23,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( r1_waybel_0(X0,X1,X2)
            <=> ~ r2_waybel_0(X0,X1,k6_subset_1(u1_struct_0(X0),X2)) )
          | ~ l1_waybel_0(X1,X0)
          | v2_struct_0(X1) )
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f24,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( r1_waybel_0(X0,X1,X2)
            <=> ~ r2_waybel_0(X0,X1,k6_subset_1(u1_struct_0(X0),X2)) )
          | ~ l1_waybel_0(X1,X0)
          | v2_struct_0(X1) )
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f23])).

fof(f40,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( r1_waybel_0(X0,X1,X2)
                | r2_waybel_0(X0,X1,k6_subset_1(u1_struct_0(X0),X2)) )
              & ( ~ r2_waybel_0(X0,X1,k6_subset_1(u1_struct_0(X0),X2))
                | ~ r1_waybel_0(X0,X1,X2) ) )
          | ~ l1_waybel_0(X1,X0)
          | v2_struct_0(X1) )
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(nnf_transformation,[],[f24])).

fof(f68,plain,(
    ! [X2,X0,X1] :
      ( r1_waybel_0(X0,X1,X2)
      | r2_waybel_0(X0,X1,k6_subset_1(u1_struct_0(X0),X2))
      | ~ l1_waybel_0(X1,X0)
      | v2_struct_0(X1)
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f40])).

fof(f12,conjecture,(
    ! [X0] :
      ( ( l1_struct_0(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( ( l1_waybel_0(X1,X0)
            & v7_waybel_0(X1)
            & v4_orders_2(X1)
            & ~ v2_struct_0(X1) )
         => r1_waybel_0(X0,X1,u1_struct_0(X0)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f13,negated_conjecture,(
    ~ ! [X0] :
        ( ( l1_struct_0(X0)
          & ~ v2_struct_0(X0) )
       => ! [X1] :
            ( ( l1_waybel_0(X1,X0)
              & v7_waybel_0(X1)
              & v4_orders_2(X1)
              & ~ v2_struct_0(X1) )
           => r1_waybel_0(X0,X1,u1_struct_0(X0)) ) ) ),
    inference(negated_conjecture,[],[f12])).

fof(f14,plain,(
    ~ ! [X0] :
        ( ( l1_struct_0(X0)
          & ~ v2_struct_0(X0) )
       => ! [X1] :
            ( ( l1_waybel_0(X1,X0)
              & v4_orders_2(X1)
              & ~ v2_struct_0(X1) )
           => r1_waybel_0(X0,X1,u1_struct_0(X0)) ) ) ),
    inference(pure_predicate_removal,[],[f13])).

fof(f15,plain,(
    ~ ! [X0] :
        ( ( l1_struct_0(X0)
          & ~ v2_struct_0(X0) )
       => ! [X1] :
            ( ( l1_waybel_0(X1,X0)
              & ~ v2_struct_0(X1) )
           => r1_waybel_0(X0,X1,u1_struct_0(X0)) ) ) ),
    inference(pure_predicate_removal,[],[f14])).

fof(f25,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ~ r1_waybel_0(X0,X1,u1_struct_0(X0))
          & l1_waybel_0(X1,X0)
          & ~ v2_struct_0(X1) )
      & l1_struct_0(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f15])).

fof(f26,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ~ r1_waybel_0(X0,X1,u1_struct_0(X0))
          & l1_waybel_0(X1,X0)
          & ~ v2_struct_0(X1) )
      & l1_struct_0(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(flattening,[],[f25])).

fof(f42,plain,(
    ! [X0] :
      ( ? [X1] :
          ( ~ r1_waybel_0(X0,X1,u1_struct_0(X0))
          & l1_waybel_0(X1,X0)
          & ~ v2_struct_0(X1) )
     => ( ~ r1_waybel_0(X0,sK4,u1_struct_0(X0))
        & l1_waybel_0(sK4,X0)
        & ~ v2_struct_0(sK4) ) ) ),
    introduced(choice_axiom,[])).

fof(f41,plain,
    ( ? [X0] :
        ( ? [X1] :
            ( ~ r1_waybel_0(X0,X1,u1_struct_0(X0))
            & l1_waybel_0(X1,X0)
            & ~ v2_struct_0(X1) )
        & l1_struct_0(X0)
        & ~ v2_struct_0(X0) )
   => ( ? [X1] :
          ( ~ r1_waybel_0(sK3,X1,u1_struct_0(sK3))
          & l1_waybel_0(X1,sK3)
          & ~ v2_struct_0(X1) )
      & l1_struct_0(sK3)
      & ~ v2_struct_0(sK3) ) ),
    introduced(choice_axiom,[])).

fof(f43,plain,
    ( ~ r1_waybel_0(sK3,sK4,u1_struct_0(sK3))
    & l1_waybel_0(sK4,sK3)
    & ~ v2_struct_0(sK4)
    & l1_struct_0(sK3)
    & ~ v2_struct_0(sK3) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3,sK4])],[f26,f42,f41])).

fof(f73,plain,(
    ~ r1_waybel_0(sK3,sK4,u1_struct_0(sK3)) ),
    inference(cnf_transformation,[],[f43])).

fof(f69,plain,(
    ~ v2_struct_0(sK3) ),
    inference(cnf_transformation,[],[f43])).

fof(f70,plain,(
    l1_struct_0(sK3) ),
    inference(cnf_transformation,[],[f43])).

fof(f71,plain,(
    ~ v2_struct_0(sK4) ),
    inference(cnf_transformation,[],[f43])).

fof(f72,plain,(
    l1_waybel_0(sK4,sK3) ),
    inference(cnf_transformation,[],[f43])).

fof(f10,axiom,(
    ! [X0] :
      ( ( l1_struct_0(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( ( l1_waybel_0(X1,X0)
            & ~ v2_struct_0(X1) )
         => ! [X2] :
              ( r2_waybel_0(X0,X1,X2)
            <=> ! [X3] :
                  ( m1_subset_1(X3,u1_struct_0(X1))
                 => ? [X4] :
                      ( r2_hidden(k2_waybel_0(X0,X1,X4),X2)
                      & r1_orders_2(X1,X3,X4)
                      & m1_subset_1(X4,u1_struct_0(X1)) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f21,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( r2_waybel_0(X0,X1,X2)
            <=> ! [X3] :
                  ( ? [X4] :
                      ( r2_hidden(k2_waybel_0(X0,X1,X4),X2)
                      & r1_orders_2(X1,X3,X4)
                      & m1_subset_1(X4,u1_struct_0(X1)) )
                  | ~ m1_subset_1(X3,u1_struct_0(X1)) ) )
          | ~ l1_waybel_0(X1,X0)
          | v2_struct_0(X1) )
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f22,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( r2_waybel_0(X0,X1,X2)
            <=> ! [X3] :
                  ( ? [X4] :
                      ( r2_hidden(k2_waybel_0(X0,X1,X4),X2)
                      & r1_orders_2(X1,X3,X4)
                      & m1_subset_1(X4,u1_struct_0(X1)) )
                  | ~ m1_subset_1(X3,u1_struct_0(X1)) ) )
          | ~ l1_waybel_0(X1,X0)
          | v2_struct_0(X1) )
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f21])).

fof(f35,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( r2_waybel_0(X0,X1,X2)
                | ? [X3] :
                    ( ! [X4] :
                        ( ~ r2_hidden(k2_waybel_0(X0,X1,X4),X2)
                        | ~ r1_orders_2(X1,X3,X4)
                        | ~ m1_subset_1(X4,u1_struct_0(X1)) )
                    & m1_subset_1(X3,u1_struct_0(X1)) ) )
              & ( ! [X3] :
                    ( ? [X4] :
                        ( r2_hidden(k2_waybel_0(X0,X1,X4),X2)
                        & r1_orders_2(X1,X3,X4)
                        & m1_subset_1(X4,u1_struct_0(X1)) )
                    | ~ m1_subset_1(X3,u1_struct_0(X1)) )
                | ~ r2_waybel_0(X0,X1,X2) ) )
          | ~ l1_waybel_0(X1,X0)
          | v2_struct_0(X1) )
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(nnf_transformation,[],[f22])).

fof(f36,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( r2_waybel_0(X0,X1,X2)
                | ? [X3] :
                    ( ! [X4] :
                        ( ~ r2_hidden(k2_waybel_0(X0,X1,X4),X2)
                        | ~ r1_orders_2(X1,X3,X4)
                        | ~ m1_subset_1(X4,u1_struct_0(X1)) )
                    & m1_subset_1(X3,u1_struct_0(X1)) ) )
              & ( ! [X5] :
                    ( ? [X6] :
                        ( r2_hidden(k2_waybel_0(X0,X1,X6),X2)
                        & r1_orders_2(X1,X5,X6)
                        & m1_subset_1(X6,u1_struct_0(X1)) )
                    | ~ m1_subset_1(X5,u1_struct_0(X1)) )
                | ~ r2_waybel_0(X0,X1,X2) ) )
          | ~ l1_waybel_0(X1,X0)
          | v2_struct_0(X1) )
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(rectify,[],[f35])).

fof(f38,plain,(
    ! [X5,X2,X1,X0] :
      ( ? [X6] :
          ( r2_hidden(k2_waybel_0(X0,X1,X6),X2)
          & r1_orders_2(X1,X5,X6)
          & m1_subset_1(X6,u1_struct_0(X1)) )
     => ( r2_hidden(k2_waybel_0(X0,X1,sK2(X0,X1,X2,X5)),X2)
        & r1_orders_2(X1,X5,sK2(X0,X1,X2,X5))
        & m1_subset_1(sK2(X0,X1,X2,X5),u1_struct_0(X1)) ) ) ),
    introduced(choice_axiom,[])).

fof(f37,plain,(
    ! [X2,X1,X0] :
      ( ? [X3] :
          ( ! [X4] :
              ( ~ r2_hidden(k2_waybel_0(X0,X1,X4),X2)
              | ~ r1_orders_2(X1,X3,X4)
              | ~ m1_subset_1(X4,u1_struct_0(X1)) )
          & m1_subset_1(X3,u1_struct_0(X1)) )
     => ( ! [X4] :
            ( ~ r2_hidden(k2_waybel_0(X0,X1,X4),X2)
            | ~ r1_orders_2(X1,sK1(X0,X1,X2),X4)
            | ~ m1_subset_1(X4,u1_struct_0(X1)) )
        & m1_subset_1(sK1(X0,X1,X2),u1_struct_0(X1)) ) ) ),
    introduced(choice_axiom,[])).

fof(f39,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( r2_waybel_0(X0,X1,X2)
                | ( ! [X4] :
                      ( ~ r2_hidden(k2_waybel_0(X0,X1,X4),X2)
                      | ~ r1_orders_2(X1,sK1(X0,X1,X2),X4)
                      | ~ m1_subset_1(X4,u1_struct_0(X1)) )
                  & m1_subset_1(sK1(X0,X1,X2),u1_struct_0(X1)) ) )
              & ( ! [X5] :
                    ( ( r2_hidden(k2_waybel_0(X0,X1,sK2(X0,X1,X2,X5)),X2)
                      & r1_orders_2(X1,X5,sK2(X0,X1,X2,X5))
                      & m1_subset_1(sK2(X0,X1,X2,X5),u1_struct_0(X1)) )
                    | ~ m1_subset_1(X5,u1_struct_0(X1)) )
                | ~ r2_waybel_0(X0,X1,X2) ) )
          | ~ l1_waybel_0(X1,X0)
          | v2_struct_0(X1) )
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1,sK2])],[f36,f38,f37])).

fof(f64,plain,(
    ! [X2,X0,X5,X1] :
      ( r2_hidden(k2_waybel_0(X0,X1,sK2(X0,X1,X2,X5)),X2)
      | ~ m1_subset_1(X5,u1_struct_0(X1))
      | ~ r2_waybel_0(X0,X1,X2)
      | ~ l1_waybel_0(X1,X0)
      | v2_struct_0(X1)
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f39])).

cnf(c_8,plain,
    ( r1_tarski(X0,X0) ),
    inference(cnf_transformation,[],[f84])).

cnf(c_1438,plain,
    ( r1_tarski(X0,X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_8])).

cnf(c_9,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(X1))
    | ~ r1_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f55])).

cnf(c_1437,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(X1)) = iProver_top
    | r1_tarski(X0,X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_9])).

cnf(c_12,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X1)))
    | l1_orders_2(g1_orders_2(X1,X0)) ),
    inference(cnf_transformation,[],[f58])).

cnf(c_1434,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X1))) != iProver_top
    | l1_orders_2(g1_orders_2(X1,X0)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_12])).

cnf(c_2014,plain,
    ( r1_tarski(X0,k2_zfmisc_1(X1,X1)) != iProver_top
    | l1_orders_2(g1_orders_2(X1,X0)) = iProver_top ),
    inference(superposition,[status(thm)],[c_1437,c_1434])).

cnf(c_2094,plain,
    ( l1_orders_2(g1_orders_2(X0,k2_zfmisc_1(X0,X0))) = iProver_top ),
    inference(superposition,[status(thm)],[c_1438,c_2014])).

cnf(c_11,plain,
    ( ~ l1_orders_2(X0)
    | ~ v1_orders_2(X0)
    | g1_orders_2(u1_struct_0(X0),u1_orders_2(X0)) = X0 ),
    inference(cnf_transformation,[],[f56])).

cnf(c_1435,plain,
    ( g1_orders_2(u1_struct_0(X0),u1_orders_2(X0)) = X0
    | l1_orders_2(X0) != iProver_top
    | v1_orders_2(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_11])).

cnf(c_2261,plain,
    ( g1_orders_2(u1_struct_0(g1_orders_2(X0,k2_zfmisc_1(X0,X0))),u1_orders_2(g1_orders_2(X0,k2_zfmisc_1(X0,X0)))) = g1_orders_2(X0,k2_zfmisc_1(X0,X0))
    | v1_orders_2(g1_orders_2(X0,k2_zfmisc_1(X0,X0))) != iProver_top ),
    inference(superposition,[status(thm)],[c_2094,c_1435])).

cnf(c_13,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X1)))
    | v1_orders_2(g1_orders_2(X1,X0)) ),
    inference(cnf_transformation,[],[f57])).

cnf(c_1433,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X1))) != iProver_top
    | v1_orders_2(g1_orders_2(X1,X0)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_13])).

cnf(c_1907,plain,
    ( r1_tarski(X0,k2_zfmisc_1(X1,X1)) != iProver_top
    | v1_orders_2(g1_orders_2(X1,X0)) = iProver_top ),
    inference(superposition,[status(thm)],[c_1437,c_1433])).

cnf(c_1912,plain,
    ( v1_orders_2(g1_orders_2(X0,k2_zfmisc_1(X0,X0))) = iProver_top ),
    inference(superposition,[status(thm)],[c_1438,c_1907])).

cnf(c_2493,plain,
    ( g1_orders_2(u1_struct_0(g1_orders_2(X0,k2_zfmisc_1(X0,X0))),u1_orders_2(g1_orders_2(X0,k2_zfmisc_1(X0,X0)))) = g1_orders_2(X0,k2_zfmisc_1(X0,X0)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_2261,c_1912])).

cnf(c_15,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X1)))
    | X2 = X1
    | g1_orders_2(X2,X3) != g1_orders_2(X1,X0) ),
    inference(cnf_transformation,[],[f59])).

cnf(c_1431,plain,
    ( X0 = X1
    | g1_orders_2(X0,X2) != g1_orders_2(X1,X3)
    | m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X1))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_15])).

cnf(c_2496,plain,
    ( g1_orders_2(X0,k2_zfmisc_1(X0,X0)) != g1_orders_2(X1,X2)
    | u1_struct_0(g1_orders_2(X0,k2_zfmisc_1(X0,X0))) = X1
    | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X1))) != iProver_top ),
    inference(superposition,[status(thm)],[c_2493,c_1431])).

cnf(c_2514,plain,
    ( u1_struct_0(g1_orders_2(X0,k2_zfmisc_1(X0,X0))) = X0
    | m1_subset_1(k2_zfmisc_1(X0,X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0))) != iProver_top ),
    inference(equality_resolution,[status(thm)],[c_2496])).

cnf(c_1661,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X1)))
    | ~ r1_tarski(X0,k2_zfmisc_1(X1,X1)) ),
    inference(instantiation,[status(thm)],[c_9])).

cnf(c_1889,plain,
    ( m1_subset_1(k2_zfmisc_1(X0,X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
    | ~ r1_tarski(k2_zfmisc_1(X0,X0),k2_zfmisc_1(X0,X0)) ),
    inference(instantiation,[status(thm)],[c_1661])).

cnf(c_1890,plain,
    ( m1_subset_1(k2_zfmisc_1(X0,X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0))) = iProver_top
    | r1_tarski(k2_zfmisc_1(X0,X0),k2_zfmisc_1(X0,X0)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1889])).

cnf(c_2039,plain,
    ( r1_tarski(k2_zfmisc_1(X0,X0),k2_zfmisc_1(X0,X0)) ),
    inference(instantiation,[status(thm)],[c_8])).

cnf(c_2040,plain,
    ( r1_tarski(k2_zfmisc_1(X0,X0),k2_zfmisc_1(X0,X0)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2039])).

cnf(c_2608,plain,
    ( u1_struct_0(g1_orders_2(X0,k2_zfmisc_1(X0,X0))) = X0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_2514,c_1890,c_2040])).

cnf(c_16,plain,
    ( m1_subset_1(k3_yellow_0(X0),u1_struct_0(X0))
    | ~ l1_orders_2(X0) ),
    inference(cnf_transformation,[],[f61])).

cnf(c_1430,plain,
    ( m1_subset_1(k3_yellow_0(X0),u1_struct_0(X0)) = iProver_top
    | l1_orders_2(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_16])).

cnf(c_2615,plain,
    ( m1_subset_1(k3_yellow_0(g1_orders_2(X0,k2_zfmisc_1(X0,X0))),X0) = iProver_top
    | l1_orders_2(g1_orders_2(X0,k2_zfmisc_1(X0,X0))) != iProver_top ),
    inference(superposition,[status(thm)],[c_2608,c_1430])).

cnf(c_2745,plain,
    ( m1_subset_1(k3_yellow_0(g1_orders_2(X0,k2_zfmisc_1(X0,X0))),X0) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_2615,c_2094])).

cnf(c_2,plain,
    ( r2_hidden(sK0(X0,X1,X2),X0)
    | r2_hidden(sK0(X0,X1,X2),X2)
    | k6_subset_1(X0,X1) = X2 ),
    inference(cnf_transformation,[],[f76])).

cnf(c_1443,plain,
    ( k6_subset_1(X0,X1) = X2
    | r2_hidden(sK0(X0,X1,X2),X0) = iProver_top
    | r2_hidden(sK0(X0,X1,X2),X2) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2])).

cnf(c_1,plain,
    ( ~ r2_hidden(sK0(X0,X1,X2),X1)
    | r2_hidden(sK0(X0,X1,X2),X2)
    | k6_subset_1(X0,X1) = X2 ),
    inference(cnf_transformation,[],[f75])).

cnf(c_1444,plain,
    ( k6_subset_1(X0,X1) = X2
    | r2_hidden(sK0(X0,X1,X2),X1) != iProver_top
    | r2_hidden(sK0(X0,X1,X2),X2) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1])).

cnf(c_2880,plain,
    ( k6_subset_1(X0,X0) = X1
    | r2_hidden(sK0(X0,X0,X1),X1) = iProver_top ),
    inference(superposition,[status(thm)],[c_1443,c_1444])).

cnf(c_5,plain,
    ( r2_hidden(X0,X1)
    | ~ r2_hidden(X0,k6_subset_1(X1,X2)) ),
    inference(cnf_transformation,[],[f82])).

cnf(c_1440,plain,
    ( r2_hidden(X0,X1) = iProver_top
    | r2_hidden(X0,k6_subset_1(X1,X2)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_5])).

cnf(c_3649,plain,
    ( k6_subset_1(X0,X0) = k6_subset_1(X1,X2)
    | r2_hidden(sK0(X0,X0,k6_subset_1(X1,X2)),X1) = iProver_top ),
    inference(superposition,[status(thm)],[c_2880,c_1440])).

cnf(c_4,plain,
    ( ~ r2_hidden(X0,X1)
    | ~ r2_hidden(X0,k6_subset_1(X2,X1)) ),
    inference(cnf_transformation,[],[f81])).

cnf(c_1441,plain,
    ( r2_hidden(X0,X1) != iProver_top
    | r2_hidden(X0,k6_subset_1(X2,X1)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_4])).

cnf(c_3650,plain,
    ( k6_subset_1(X0,X0) = k6_subset_1(X1,X2)
    | r2_hidden(sK0(X0,X0,k6_subset_1(X1,X2)),X2) != iProver_top ),
    inference(superposition,[status(thm)],[c_2880,c_1441])).

cnf(c_3839,plain,
    ( k6_subset_1(X0,X0) = k6_subset_1(X1,X1) ),
    inference(superposition,[status(thm)],[c_3649,c_3650])).

cnf(c_3840,plain,
    ( k6_subset_1(X0,X0) = sP0_iProver_split ),
    inference(splitting,[splitting(split),new_symbols(definition,[sP0_iProver_split])],[c_3839])).

cnf(c_22,plain,
    ( r1_waybel_0(X0,X1,X2)
    | r2_waybel_0(X0,X1,k6_subset_1(u1_struct_0(X0),X2))
    | ~ l1_waybel_0(X1,X0)
    | ~ l1_struct_0(X0)
    | v2_struct_0(X0)
    | v2_struct_0(X1) ),
    inference(cnf_transformation,[],[f68])).

cnf(c_24,negated_conjecture,
    ( ~ r1_waybel_0(sK3,sK4,u1_struct_0(sK3)) ),
    inference(cnf_transformation,[],[f73])).

cnf(c_491,plain,
    ( r2_waybel_0(X0,X1,k6_subset_1(u1_struct_0(X0),X2))
    | ~ l1_waybel_0(X1,X0)
    | ~ l1_struct_0(X0)
    | v2_struct_0(X0)
    | v2_struct_0(X1)
    | u1_struct_0(sK3) != X2
    | sK4 != X1
    | sK3 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_22,c_24])).

cnf(c_492,plain,
    ( r2_waybel_0(sK3,sK4,k6_subset_1(u1_struct_0(sK3),u1_struct_0(sK3)))
    | ~ l1_waybel_0(sK4,sK3)
    | ~ l1_struct_0(sK3)
    | v2_struct_0(sK4)
    | v2_struct_0(sK3) ),
    inference(unflattening,[status(thm)],[c_491])).

cnf(c_28,negated_conjecture,
    ( ~ v2_struct_0(sK3) ),
    inference(cnf_transformation,[],[f69])).

cnf(c_27,negated_conjecture,
    ( l1_struct_0(sK3) ),
    inference(cnf_transformation,[],[f70])).

cnf(c_26,negated_conjecture,
    ( ~ v2_struct_0(sK4) ),
    inference(cnf_transformation,[],[f71])).

cnf(c_25,negated_conjecture,
    ( l1_waybel_0(sK4,sK3) ),
    inference(cnf_transformation,[],[f72])).

cnf(c_494,plain,
    ( r2_waybel_0(sK3,sK4,k6_subset_1(u1_struct_0(sK3),u1_struct_0(sK3))) ),
    inference(global_propositional_subsumption,[status(thm)],[c_492,c_28,c_27,c_26,c_25])).

cnf(c_1421,plain,
    ( r2_waybel_0(sK3,sK4,k6_subset_1(u1_struct_0(sK3),u1_struct_0(sK3))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_494])).

cnf(c_4027,plain,
    ( r2_waybel_0(sK3,sK4,sP0_iProver_split) = iProver_top ),
    inference(demodulation,[status(thm)],[c_3840,c_1421])).

cnf(c_19,plain,
    ( ~ r2_waybel_0(X0,X1,X2)
    | ~ l1_waybel_0(X1,X0)
    | ~ m1_subset_1(X3,u1_struct_0(X1))
    | r2_hidden(k2_waybel_0(X0,X1,sK2(X0,X1,X2,X3)),X2)
    | ~ l1_struct_0(X0)
    | v2_struct_0(X0)
    | v2_struct_0(X1) ),
    inference(cnf_transformation,[],[f64])).

cnf(c_1428,plain,
    ( r2_waybel_0(X0,X1,X2) != iProver_top
    | l1_waybel_0(X1,X0) != iProver_top
    | m1_subset_1(X3,u1_struct_0(X1)) != iProver_top
    | r2_hidden(k2_waybel_0(X0,X1,sK2(X0,X1,X2,X3)),X2) = iProver_top
    | l1_struct_0(X0) != iProver_top
    | v2_struct_0(X0) = iProver_top
    | v2_struct_0(X1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_19])).

cnf(c_4037,plain,
    ( r2_hidden(X0,X1) = iProver_top
    | r2_hidden(X0,sP0_iProver_split) != iProver_top ),
    inference(superposition,[status(thm)],[c_3840,c_1440])).

cnf(c_4038,plain,
    ( r2_hidden(X0,X1) != iProver_top
    | r2_hidden(X0,sP0_iProver_split) != iProver_top ),
    inference(superposition,[status(thm)],[c_3840,c_1441])).

cnf(c_4144,plain,
    ( r2_hidden(X0,sP0_iProver_split) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_4037,c_4038])).

cnf(c_4152,plain,
    ( r2_waybel_0(X0,X1,sP0_iProver_split) != iProver_top
    | l1_waybel_0(X1,X0) != iProver_top
    | m1_subset_1(X2,u1_struct_0(X1)) != iProver_top
    | l1_struct_0(X0) != iProver_top
    | v2_struct_0(X0) = iProver_top
    | v2_struct_0(X1) = iProver_top ),
    inference(superposition,[status(thm)],[c_1428,c_4144])).

cnf(c_16227,plain,
    ( l1_waybel_0(sK4,sK3) != iProver_top
    | m1_subset_1(X0,u1_struct_0(sK4)) != iProver_top
    | l1_struct_0(sK3) != iProver_top
    | v2_struct_0(sK4) = iProver_top
    | v2_struct_0(sK3) = iProver_top ),
    inference(superposition,[status(thm)],[c_4027,c_4152])).

cnf(c_29,plain,
    ( v2_struct_0(sK3) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_28])).

cnf(c_30,plain,
    ( l1_struct_0(sK3) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_27])).

cnf(c_31,plain,
    ( v2_struct_0(sK4) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_26])).

cnf(c_32,plain,
    ( l1_waybel_0(sK4,sK3) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_25])).

cnf(c_16942,plain,
    ( m1_subset_1(X0,u1_struct_0(sK4)) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_16227,c_29,c_30,c_31,c_32])).

cnf(c_16951,plain,
    ( $false ),
    inference(superposition,[status(thm)],[c_2745,c_16942])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : iproveropt_run.sh %d %s
% 0.13/0.33  % Computer   : n014.cluster.edu
% 0.13/0.33  % Model      : x86_64 x86_64
% 0.13/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.33  % Memory     : 8042.1875MB
% 0.13/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.33  % CPULimit   : 60
% 0.13/0.33  % WCLimit    : 600
% 0.13/0.33  % DateTime   : Tue Dec  1 12:46:52 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running in FOF mode
% 3.92/1.00  % SZS status Started for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.92/1.00  
% 3.92/1.00  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 3.92/1.00  
% 3.92/1.00  ------  iProver source info
% 3.92/1.00  
% 3.92/1.00  git: date: 2020-06-30 10:37:57 +0100
% 3.92/1.00  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 3.92/1.00  git: non_committed_changes: false
% 3.92/1.00  git: last_make_outside_of_git: false
% 3.92/1.00  
% 3.92/1.00  ------ 
% 3.92/1.00  
% 3.92/1.00  ------ Input Options
% 3.92/1.00  
% 3.92/1.00  --out_options                           all
% 3.92/1.00  --tptp_safe_out                         true
% 3.92/1.00  --problem_path                          ""
% 3.92/1.00  --include_path                          ""
% 3.92/1.00  --clausifier                            res/vclausify_rel
% 3.92/1.00  --clausifier_options                    ""
% 3.92/1.00  --stdin                                 false
% 3.92/1.00  --stats_out                             all
% 3.92/1.00  
% 3.92/1.00  ------ General Options
% 3.92/1.00  
% 3.92/1.00  --fof                                   false
% 3.92/1.00  --time_out_real                         305.
% 3.92/1.00  --time_out_virtual                      -1.
% 3.92/1.00  --symbol_type_check                     false
% 3.92/1.00  --clausify_out                          false
% 3.92/1.00  --sig_cnt_out                           false
% 3.92/1.00  --trig_cnt_out                          false
% 3.92/1.00  --trig_cnt_out_tolerance                1.
% 3.92/1.00  --trig_cnt_out_sk_spl                   false
% 3.92/1.00  --abstr_cl_out                          false
% 3.92/1.00  
% 3.92/1.00  ------ Global Options
% 3.92/1.00  
% 3.92/1.00  --schedule                              default
% 3.92/1.00  --add_important_lit                     false
% 3.92/1.00  --prop_solver_per_cl                    1000
% 3.92/1.00  --min_unsat_core                        false
% 3.92/1.00  --soft_assumptions                      false
% 3.92/1.00  --soft_lemma_size                       3
% 3.92/1.00  --prop_impl_unit_size                   0
% 3.92/1.00  --prop_impl_unit                        []
% 3.92/1.00  --share_sel_clauses                     true
% 3.92/1.00  --reset_solvers                         false
% 3.92/1.00  --bc_imp_inh                            [conj_cone]
% 3.92/1.00  --conj_cone_tolerance                   3.
% 3.92/1.00  --extra_neg_conj                        none
% 3.92/1.00  --large_theory_mode                     true
% 3.92/1.00  --prolific_symb_bound                   200
% 3.92/1.00  --lt_threshold                          2000
% 3.92/1.00  --clause_weak_htbl                      true
% 3.92/1.00  --gc_record_bc_elim                     false
% 3.92/1.00  
% 3.92/1.00  ------ Preprocessing Options
% 3.92/1.00  
% 3.92/1.00  --preprocessing_flag                    true
% 3.92/1.00  --time_out_prep_mult                    0.1
% 3.92/1.00  --splitting_mode                        input
% 3.92/1.00  --splitting_grd                         true
% 3.92/1.00  --splitting_cvd                         false
% 3.92/1.00  --splitting_cvd_svl                     false
% 3.92/1.00  --splitting_nvd                         32
% 3.92/1.00  --sub_typing                            true
% 3.92/1.00  --prep_gs_sim                           true
% 3.92/1.00  --prep_unflatten                        true
% 3.92/1.00  --prep_res_sim                          true
% 3.92/1.00  --prep_upred                            true
% 3.92/1.00  --prep_sem_filter                       exhaustive
% 3.92/1.00  --prep_sem_filter_out                   false
% 3.92/1.00  --pred_elim                             true
% 3.92/1.00  --res_sim_input                         true
% 3.92/1.00  --eq_ax_congr_red                       true
% 3.92/1.00  --pure_diseq_elim                       true
% 3.92/1.00  --brand_transform                       false
% 3.92/1.00  --non_eq_to_eq                          false
% 3.92/1.00  --prep_def_merge                        true
% 3.92/1.00  --prep_def_merge_prop_impl              false
% 3.92/1.00  --prep_def_merge_mbd                    true
% 3.92/1.00  --prep_def_merge_tr_red                 false
% 3.92/1.00  --prep_def_merge_tr_cl                  false
% 3.92/1.00  --smt_preprocessing                     true
% 3.92/1.00  --smt_ac_axioms                         fast
% 3.92/1.00  --preprocessed_out                      false
% 3.92/1.00  --preprocessed_stats                    false
% 3.92/1.00  
% 3.92/1.00  ------ Abstraction refinement Options
% 3.92/1.00  
% 3.92/1.00  --abstr_ref                             []
% 3.92/1.00  --abstr_ref_prep                        false
% 3.92/1.00  --abstr_ref_until_sat                   false
% 3.92/1.00  --abstr_ref_sig_restrict                funpre
% 3.92/1.00  --abstr_ref_af_restrict_to_split_sk     false
% 3.92/1.00  --abstr_ref_under                       []
% 3.92/1.00  
% 3.92/1.00  ------ SAT Options
% 3.92/1.00  
% 3.92/1.00  --sat_mode                              false
% 3.92/1.00  --sat_fm_restart_options                ""
% 3.92/1.00  --sat_gr_def                            false
% 3.92/1.00  --sat_epr_types                         true
% 3.92/1.00  --sat_non_cyclic_types                  false
% 3.92/1.00  --sat_finite_models                     false
% 3.92/1.00  --sat_fm_lemmas                         false
% 3.92/1.00  --sat_fm_prep                           false
% 3.92/1.00  --sat_fm_uc_incr                        true
% 3.92/1.00  --sat_out_model                         small
% 3.92/1.00  --sat_out_clauses                       false
% 3.92/1.00  
% 3.92/1.00  ------ QBF Options
% 3.92/1.00  
% 3.92/1.00  --qbf_mode                              false
% 3.92/1.00  --qbf_elim_univ                         false
% 3.92/1.00  --qbf_dom_inst                          none
% 3.92/1.00  --qbf_dom_pre_inst                      false
% 3.92/1.00  --qbf_sk_in                             false
% 3.92/1.00  --qbf_pred_elim                         true
% 3.92/1.00  --qbf_split                             512
% 3.92/1.00  
% 3.92/1.00  ------ BMC1 Options
% 3.92/1.00  
% 3.92/1.00  --bmc1_incremental                      false
% 3.92/1.00  --bmc1_axioms                           reachable_all
% 3.92/1.00  --bmc1_min_bound                        0
% 3.92/1.00  --bmc1_max_bound                        -1
% 3.92/1.00  --bmc1_max_bound_default                -1
% 3.92/1.00  --bmc1_symbol_reachability              true
% 3.92/1.00  --bmc1_property_lemmas                  false
% 3.92/1.00  --bmc1_k_induction                      false
% 3.92/1.00  --bmc1_non_equiv_states                 false
% 3.92/1.00  --bmc1_deadlock                         false
% 3.92/1.00  --bmc1_ucm                              false
% 3.92/1.00  --bmc1_add_unsat_core                   none
% 3.92/1.00  --bmc1_unsat_core_children              false
% 3.92/1.00  --bmc1_unsat_core_extrapolate_axioms    false
% 3.92/1.00  --bmc1_out_stat                         full
% 3.92/1.00  --bmc1_ground_init                      false
% 3.92/1.00  --bmc1_pre_inst_next_state              false
% 3.92/1.00  --bmc1_pre_inst_state                   false
% 3.92/1.00  --bmc1_pre_inst_reach_state             false
% 3.92/1.00  --bmc1_out_unsat_core                   false
% 3.92/1.00  --bmc1_aig_witness_out                  false
% 3.92/1.00  --bmc1_verbose                          false
% 3.92/1.00  --bmc1_dump_clauses_tptp                false
% 3.92/1.00  --bmc1_dump_unsat_core_tptp             false
% 3.92/1.00  --bmc1_dump_file                        -
% 3.92/1.00  --bmc1_ucm_expand_uc_limit              128
% 3.92/1.00  --bmc1_ucm_n_expand_iterations          6
% 3.92/1.00  --bmc1_ucm_extend_mode                  1
% 3.92/1.00  --bmc1_ucm_init_mode                    2
% 3.92/1.00  --bmc1_ucm_cone_mode                    none
% 3.92/1.00  --bmc1_ucm_reduced_relation_type        0
% 3.92/1.00  --bmc1_ucm_relax_model                  4
% 3.92/1.00  --bmc1_ucm_full_tr_after_sat            true
% 3.92/1.00  --bmc1_ucm_expand_neg_assumptions       false
% 3.92/1.00  --bmc1_ucm_layered_model                none
% 3.92/1.00  --bmc1_ucm_max_lemma_size               10
% 3.92/1.00  
% 3.92/1.00  ------ AIG Options
% 3.92/1.00  
% 3.92/1.00  --aig_mode                              false
% 3.92/1.00  
% 3.92/1.00  ------ Instantiation Options
% 3.92/1.00  
% 3.92/1.00  --instantiation_flag                    true
% 3.92/1.00  --inst_sos_flag                         true
% 3.92/1.00  --inst_sos_phase                        true
% 3.92/1.00  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 3.92/1.00  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 3.92/1.00  --inst_lit_sel_side                     num_symb
% 3.92/1.00  --inst_solver_per_active                1400
% 3.92/1.00  --inst_solver_calls_frac                1.
% 3.92/1.00  --inst_passive_queue_type               priority_queues
% 3.92/1.00  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 3.92/1.00  --inst_passive_queues_freq              [25;2]
% 3.92/1.00  --inst_dismatching                      true
% 3.92/1.00  --inst_eager_unprocessed_to_passive     true
% 3.92/1.00  --inst_prop_sim_given                   true
% 3.92/1.00  --inst_prop_sim_new                     false
% 3.92/1.00  --inst_subs_new                         false
% 3.92/1.00  --inst_eq_res_simp                      false
% 3.92/1.00  --inst_subs_given                       false
% 3.92/1.00  --inst_orphan_elimination               true
% 3.92/1.00  --inst_learning_loop_flag               true
% 3.92/1.00  --inst_learning_start                   3000
% 3.92/1.00  --inst_learning_factor                  2
% 3.92/1.00  --inst_start_prop_sim_after_learn       3
% 3.92/1.00  --inst_sel_renew                        solver
% 3.92/1.00  --inst_lit_activity_flag                true
% 3.92/1.00  --inst_restr_to_given                   false
% 3.92/1.00  --inst_activity_threshold               500
% 3.92/1.00  --inst_out_proof                        true
% 3.92/1.00  
% 3.92/1.00  ------ Resolution Options
% 3.92/1.00  
% 3.92/1.00  --resolution_flag                       true
% 3.92/1.00  --res_lit_sel                           adaptive
% 3.92/1.00  --res_lit_sel_side                      none
% 3.92/1.00  --res_ordering                          kbo
% 3.92/1.00  --res_to_prop_solver                    active
% 3.92/1.00  --res_prop_simpl_new                    false
% 3.92/1.00  --res_prop_simpl_given                  true
% 3.92/1.00  --res_passive_queue_type                priority_queues
% 3.92/1.00  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 3.92/1.00  --res_passive_queues_freq               [15;5]
% 3.92/1.00  --res_forward_subs                      full
% 3.92/1.00  --res_backward_subs                     full
% 3.92/1.00  --res_forward_subs_resolution           true
% 3.92/1.00  --res_backward_subs_resolution          true
% 3.92/1.00  --res_orphan_elimination                true
% 3.92/1.00  --res_time_limit                        2.
% 3.92/1.00  --res_out_proof                         true
% 3.92/1.00  
% 3.92/1.00  ------ Superposition Options
% 3.92/1.00  
% 3.92/1.00  --superposition_flag                    true
% 3.92/1.00  --sup_passive_queue_type                priority_queues
% 3.92/1.00  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 3.92/1.00  --sup_passive_queues_freq               [8;1;4]
% 3.92/1.00  --demod_completeness_check              fast
% 3.92/1.00  --demod_use_ground                      true
% 3.92/1.00  --sup_to_prop_solver                    passive
% 3.92/1.00  --sup_prop_simpl_new                    true
% 3.92/1.00  --sup_prop_simpl_given                  true
% 3.92/1.00  --sup_fun_splitting                     true
% 3.92/1.00  --sup_smt_interval                      50000
% 3.92/1.00  
% 3.92/1.00  ------ Superposition Simplification Setup
% 3.92/1.00  
% 3.92/1.00  --sup_indices_passive                   [LightNormIndex;FwDemodIndex]
% 3.92/1.00  --sup_indices_active                    [SubsumptionIndex;BwDemodIndex]
% 3.92/1.00  --sup_indices_immed                     [SubsumptionIndex;FwDemodIndex;BwDemodIndex]
% 3.92/1.00  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex]
% 3.92/1.00  --sup_full_triv                         [TrivRules;PropSubs]
% 3.92/1.00  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;Joinability]
% 3.92/1.00  --sup_full_bw                           [BwDemod;BwSubsumption]
% 3.92/1.00  --sup_immed_triv                        [TrivRules]
% 3.92/1.00  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 3.92/1.00  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption]
% 3.92/1.00  --sup_immed_bw_main                     []
% 3.92/1.00  --sup_immed_bw_immed                    [BwDemod;BwSubsumption]
% 3.92/1.00  --sup_input_triv                        [Unflattening;TrivRules]
% 3.92/1.00  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption]
% 3.92/1.00  --sup_input_bw                          []
% 3.92/1.00  
% 3.92/1.00  ------ Combination Options
% 3.92/1.00  
% 3.92/1.00  --comb_res_mult                         3
% 3.92/1.00  --comb_sup_mult                         2
% 3.92/1.00  --comb_inst_mult                        10
% 3.92/1.00  
% 3.92/1.00  ------ Debug Options
% 3.92/1.00  
% 3.92/1.00  --dbg_backtrace                         false
% 3.92/1.00  --dbg_dump_prop_clauses                 false
% 3.92/1.00  --dbg_dump_prop_clauses_file            -
% 3.92/1.00  --dbg_out_stat                          false
% 3.92/1.00  ------ Parsing...
% 3.92/1.00  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 3.92/1.00  
% 3.92/1.00  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe:1:0s pe:2:0s pe_e  sf_s  rm: 3 0s  sf_e  pe_s  pe_e 
% 3.92/1.00  
% 3.92/1.00  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 3.92/1.00  
% 3.92/1.00  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 3.92/1.00  ------ Proving...
% 3.92/1.00  ------ Problem Properties 
% 3.92/1.00  
% 3.92/1.00  
% 3.92/1.00  clauses                                 25
% 3.92/1.00  conjectures                             4
% 3.92/1.00  EPR                                     6
% 3.92/1.00  Horn                                    17
% 3.92/1.00  unary                                   6
% 3.92/1.00  binary                                  7
% 3.92/1.00  lits                                    75
% 3.92/1.00  lits eq                                 9
% 3.92/1.00  fd_pure                                 0
% 3.92/1.00  fd_pseudo                               0
% 3.92/1.00  fd_cond                                 0
% 3.92/1.00  fd_pseudo_cond                          6
% 3.92/1.00  AC symbols                              0
% 3.92/1.00  
% 3.92/1.00  ------ Schedule dynamic 5 is on 
% 3.92/1.00  
% 3.92/1.00  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" Time Limit: 10.
% 3.92/1.00  
% 3.92/1.00  
% 3.92/1.00  ------ 
% 3.92/1.00  Current options:
% 3.92/1.00  ------ 
% 3.92/1.00  
% 3.92/1.00  ------ Input Options
% 3.92/1.00  
% 3.92/1.00  --out_options                           all
% 3.92/1.00  --tptp_safe_out                         true
% 3.92/1.00  --problem_path                          ""
% 3.92/1.00  --include_path                          ""
% 3.92/1.00  --clausifier                            res/vclausify_rel
% 3.92/1.00  --clausifier_options                    ""
% 3.92/1.00  --stdin                                 false
% 3.92/1.00  --stats_out                             all
% 3.92/1.00  
% 3.92/1.00  ------ General Options
% 3.92/1.00  
% 3.92/1.00  --fof                                   false
% 3.92/1.00  --time_out_real                         305.
% 3.92/1.00  --time_out_virtual                      -1.
% 3.92/1.00  --symbol_type_check                     false
% 3.92/1.00  --clausify_out                          false
% 3.92/1.00  --sig_cnt_out                           false
% 3.92/1.00  --trig_cnt_out                          false
% 3.92/1.00  --trig_cnt_out_tolerance                1.
% 3.92/1.00  --trig_cnt_out_sk_spl                   false
% 3.92/1.00  --abstr_cl_out                          false
% 3.92/1.00  
% 3.92/1.00  ------ Global Options
% 3.92/1.00  
% 3.92/1.00  --schedule                              default
% 3.92/1.00  --add_important_lit                     false
% 3.92/1.00  --prop_solver_per_cl                    1000
% 3.92/1.00  --min_unsat_core                        false
% 3.92/1.00  --soft_assumptions                      false
% 3.92/1.00  --soft_lemma_size                       3
% 3.92/1.00  --prop_impl_unit_size                   0
% 3.92/1.00  --prop_impl_unit                        []
% 3.92/1.00  --share_sel_clauses                     true
% 3.92/1.00  --reset_solvers                         false
% 3.92/1.00  --bc_imp_inh                            [conj_cone]
% 3.92/1.00  --conj_cone_tolerance                   3.
% 3.92/1.00  --extra_neg_conj                        none
% 3.92/1.00  --large_theory_mode                     true
% 3.92/1.00  --prolific_symb_bound                   200
% 3.92/1.00  --lt_threshold                          2000
% 3.92/1.00  --clause_weak_htbl                      true
% 3.92/1.00  --gc_record_bc_elim                     false
% 3.92/1.00  
% 3.92/1.00  ------ Preprocessing Options
% 3.92/1.00  
% 3.92/1.00  --preprocessing_flag                    true
% 3.92/1.00  --time_out_prep_mult                    0.1
% 3.92/1.00  --splitting_mode                        input
% 3.92/1.00  --splitting_grd                         true
% 3.92/1.00  --splitting_cvd                         false
% 3.92/1.00  --splitting_cvd_svl                     false
% 3.92/1.00  --splitting_nvd                         32
% 3.92/1.00  --sub_typing                            true
% 3.92/1.00  --prep_gs_sim                           true
% 3.92/1.00  --prep_unflatten                        true
% 3.92/1.00  --prep_res_sim                          true
% 3.92/1.00  --prep_upred                            true
% 3.92/1.00  --prep_sem_filter                       exhaustive
% 3.92/1.00  --prep_sem_filter_out                   false
% 3.92/1.00  --pred_elim                             true
% 3.92/1.00  --res_sim_input                         true
% 3.92/1.00  --eq_ax_congr_red                       true
% 3.92/1.00  --pure_diseq_elim                       true
% 3.92/1.00  --brand_transform                       false
% 3.92/1.00  --non_eq_to_eq                          false
% 3.92/1.00  --prep_def_merge                        true
% 3.92/1.00  --prep_def_merge_prop_impl              false
% 3.92/1.00  --prep_def_merge_mbd                    true
% 3.92/1.00  --prep_def_merge_tr_red                 false
% 3.92/1.00  --prep_def_merge_tr_cl                  false
% 3.92/1.00  --smt_preprocessing                     true
% 3.92/1.00  --smt_ac_axioms                         fast
% 3.92/1.00  --preprocessed_out                      false
% 3.92/1.00  --preprocessed_stats                    false
% 3.92/1.00  
% 3.92/1.00  ------ Abstraction refinement Options
% 3.92/1.00  
% 3.92/1.00  --abstr_ref                             []
% 3.92/1.00  --abstr_ref_prep                        false
% 3.92/1.00  --abstr_ref_until_sat                   false
% 3.92/1.00  --abstr_ref_sig_restrict                funpre
% 3.92/1.00  --abstr_ref_af_restrict_to_split_sk     false
% 3.92/1.00  --abstr_ref_under                       []
% 3.92/1.00  
% 3.92/1.00  ------ SAT Options
% 3.92/1.00  
% 3.92/1.00  --sat_mode                              false
% 3.92/1.00  --sat_fm_restart_options                ""
% 3.92/1.00  --sat_gr_def                            false
% 3.92/1.00  --sat_epr_types                         true
% 3.92/1.00  --sat_non_cyclic_types                  false
% 3.92/1.00  --sat_finite_models                     false
% 3.92/1.00  --sat_fm_lemmas                         false
% 3.92/1.00  --sat_fm_prep                           false
% 3.92/1.00  --sat_fm_uc_incr                        true
% 3.92/1.00  --sat_out_model                         small
% 3.92/1.00  --sat_out_clauses                       false
% 3.92/1.00  
% 3.92/1.00  ------ QBF Options
% 3.92/1.00  
% 3.92/1.00  --qbf_mode                              false
% 3.92/1.00  --qbf_elim_univ                         false
% 3.92/1.00  --qbf_dom_inst                          none
% 3.92/1.00  --qbf_dom_pre_inst                      false
% 3.92/1.00  --qbf_sk_in                             false
% 3.92/1.00  --qbf_pred_elim                         true
% 3.92/1.00  --qbf_split                             512
% 3.92/1.00  
% 3.92/1.00  ------ BMC1 Options
% 3.92/1.00  
% 3.92/1.00  --bmc1_incremental                      false
% 3.92/1.00  --bmc1_axioms                           reachable_all
% 3.92/1.00  --bmc1_min_bound                        0
% 3.92/1.00  --bmc1_max_bound                        -1
% 3.92/1.00  --bmc1_max_bound_default                -1
% 3.92/1.00  --bmc1_symbol_reachability              true
% 3.92/1.00  --bmc1_property_lemmas                  false
% 3.92/1.00  --bmc1_k_induction                      false
% 3.92/1.00  --bmc1_non_equiv_states                 false
% 3.92/1.00  --bmc1_deadlock                         false
% 3.92/1.00  --bmc1_ucm                              false
% 3.92/1.00  --bmc1_add_unsat_core                   none
% 3.92/1.00  --bmc1_unsat_core_children              false
% 3.92/1.00  --bmc1_unsat_core_extrapolate_axioms    false
% 3.92/1.00  --bmc1_out_stat                         full
% 3.92/1.00  --bmc1_ground_init                      false
% 3.92/1.00  --bmc1_pre_inst_next_state              false
% 3.92/1.00  --bmc1_pre_inst_state                   false
% 3.92/1.00  --bmc1_pre_inst_reach_state             false
% 3.92/1.00  --bmc1_out_unsat_core                   false
% 3.92/1.00  --bmc1_aig_witness_out                  false
% 3.92/1.00  --bmc1_verbose                          false
% 3.92/1.00  --bmc1_dump_clauses_tptp                false
% 3.92/1.00  --bmc1_dump_unsat_core_tptp             false
% 3.92/1.00  --bmc1_dump_file                        -
% 3.92/1.00  --bmc1_ucm_expand_uc_limit              128
% 3.92/1.00  --bmc1_ucm_n_expand_iterations          6
% 3.92/1.00  --bmc1_ucm_extend_mode                  1
% 3.92/1.00  --bmc1_ucm_init_mode                    2
% 3.92/1.00  --bmc1_ucm_cone_mode                    none
% 3.92/1.00  --bmc1_ucm_reduced_relation_type        0
% 3.92/1.00  --bmc1_ucm_relax_model                  4
% 3.92/1.00  --bmc1_ucm_full_tr_after_sat            true
% 3.92/1.00  --bmc1_ucm_expand_neg_assumptions       false
% 3.92/1.00  --bmc1_ucm_layered_model                none
% 3.92/1.00  --bmc1_ucm_max_lemma_size               10
% 3.92/1.00  
% 3.92/1.00  ------ AIG Options
% 3.92/1.00  
% 3.92/1.00  --aig_mode                              false
% 3.92/1.00  
% 3.92/1.00  ------ Instantiation Options
% 3.92/1.00  
% 3.92/1.00  --instantiation_flag                    true
% 3.92/1.00  --inst_sos_flag                         true
% 3.92/1.00  --inst_sos_phase                        true
% 3.92/1.00  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 3.92/1.00  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 3.92/1.00  --inst_lit_sel_side                     none
% 3.92/1.00  --inst_solver_per_active                1400
% 3.92/1.00  --inst_solver_calls_frac                1.
% 3.92/1.00  --inst_passive_queue_type               priority_queues
% 3.92/1.00  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 3.92/1.00  --inst_passive_queues_freq              [25;2]
% 3.92/1.00  --inst_dismatching                      true
% 3.92/1.00  --inst_eager_unprocessed_to_passive     true
% 3.92/1.00  --inst_prop_sim_given                   true
% 3.92/1.00  --inst_prop_sim_new                     false
% 3.92/1.00  --inst_subs_new                         false
% 3.92/1.00  --inst_eq_res_simp                      false
% 3.92/1.00  --inst_subs_given                       false
% 3.92/1.00  --inst_orphan_elimination               true
% 3.92/1.00  --inst_learning_loop_flag               true
% 3.92/1.00  --inst_learning_start                   3000
% 3.92/1.00  --inst_learning_factor                  2
% 3.92/1.00  --inst_start_prop_sim_after_learn       3
% 3.92/1.00  --inst_sel_renew                        solver
% 3.92/1.00  --inst_lit_activity_flag                true
% 3.92/1.00  --inst_restr_to_given                   false
% 3.92/1.00  --inst_activity_threshold               500
% 3.92/1.00  --inst_out_proof                        true
% 3.92/1.00  
% 3.92/1.00  ------ Resolution Options
% 3.92/1.00  
% 3.92/1.00  --resolution_flag                       false
% 3.92/1.00  --res_lit_sel                           adaptive
% 3.92/1.00  --res_lit_sel_side                      none
% 3.92/1.00  --res_ordering                          kbo
% 3.92/1.00  --res_to_prop_solver                    active
% 3.92/1.00  --res_prop_simpl_new                    false
% 3.92/1.00  --res_prop_simpl_given                  true
% 3.92/1.00  --res_passive_queue_type                priority_queues
% 3.92/1.00  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 3.92/1.00  --res_passive_queues_freq               [15;5]
% 3.92/1.00  --res_forward_subs                      full
% 3.92/1.00  --res_backward_subs                     full
% 3.92/1.00  --res_forward_subs_resolution           true
% 3.92/1.00  --res_backward_subs_resolution          true
% 3.92/1.00  --res_orphan_elimination                true
% 3.92/1.00  --res_time_limit                        2.
% 3.92/1.00  --res_out_proof                         true
% 3.92/1.00  
% 3.92/1.00  ------ Superposition Options
% 3.92/1.00  
% 3.92/1.00  --superposition_flag                    true
% 3.92/1.00  --sup_passive_queue_type                priority_queues
% 3.92/1.00  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 3.92/1.00  --sup_passive_queues_freq               [8;1;4]
% 3.92/1.00  --demod_completeness_check              fast
% 3.92/1.00  --demod_use_ground                      true
% 3.92/1.00  --sup_to_prop_solver                    passive
% 3.92/1.00  --sup_prop_simpl_new                    true
% 3.92/1.00  --sup_prop_simpl_given                  true
% 3.92/1.00  --sup_fun_splitting                     true
% 3.92/1.00  --sup_smt_interval                      50000
% 3.92/1.00  
% 3.92/1.00  ------ Superposition Simplification Setup
% 3.92/1.00  
% 3.92/1.00  --sup_indices_passive                   [LightNormIndex;FwDemodIndex]
% 3.92/1.00  --sup_indices_active                    [SubsumptionIndex;BwDemodIndex]
% 3.92/1.00  --sup_indices_immed                     [SubsumptionIndex;FwDemodIndex;BwDemodIndex]
% 3.92/1.00  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex]
% 3.92/1.00  --sup_full_triv                         [TrivRules;PropSubs]
% 3.92/1.00  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;Joinability]
% 3.92/1.00  --sup_full_bw                           [BwDemod;BwSubsumption]
% 3.92/1.00  --sup_immed_triv                        [TrivRules]
% 3.92/1.00  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 3.92/1.00  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption]
% 3.92/1.00  --sup_immed_bw_main                     []
% 3.92/1.00  --sup_immed_bw_immed                    [BwDemod;BwSubsumption]
% 3.92/1.00  --sup_input_triv                        [Unflattening;TrivRules]
% 3.92/1.00  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption]
% 3.92/1.00  --sup_input_bw                          []
% 3.92/1.00  
% 3.92/1.00  ------ Combination Options
% 3.92/1.00  
% 3.92/1.00  --comb_res_mult                         3
% 3.92/1.00  --comb_sup_mult                         2
% 3.92/1.00  --comb_inst_mult                        10
% 3.92/1.00  
% 3.92/1.00  ------ Debug Options
% 3.92/1.00  
% 3.92/1.00  --dbg_backtrace                         false
% 3.92/1.00  --dbg_dump_prop_clauses                 false
% 3.92/1.00  --dbg_dump_prop_clauses_file            -
% 3.92/1.00  --dbg_out_stat                          false
% 3.92/1.00  
% 3.92/1.00  
% 3.92/1.00  
% 3.92/1.00  
% 3.92/1.00  ------ Proving...
% 3.92/1.00  
% 3.92/1.00  
% 3.92/1.00  % SZS status Theorem for theBenchmark.p
% 3.92/1.00  
% 3.92/1.00   Resolution empty clause
% 3.92/1.00  
% 3.92/1.00  % SZS output start CNFRefutation for theBenchmark.p
% 3.92/1.00  
% 3.92/1.00  fof(f3,axiom,(
% 3.92/1.00    ! [X0,X1] : (X0 = X1 <=> (r1_tarski(X1,X0) & r1_tarski(X0,X1)))),
% 3.92/1.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.92/1.00  
% 3.92/1.00  fof(f32,plain,(
% 3.92/1.00    ! [X0,X1] : ((X0 = X1 | (~r1_tarski(X1,X0) | ~r1_tarski(X0,X1))) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 3.92/1.00    inference(nnf_transformation,[],[f3])).
% 3.92/1.00  
% 3.92/1.00  fof(f33,plain,(
% 3.92/1.00    ! [X0,X1] : ((X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 3.92/1.00    inference(flattening,[],[f32])).
% 3.92/1.00  
% 3.92/1.00  fof(f50,plain,(
% 3.92/1.00    ( ! [X0,X1] : (r1_tarski(X0,X1) | X0 != X1) )),
% 3.92/1.00    inference(cnf_transformation,[],[f33])).
% 3.92/1.00  
% 3.92/1.00  fof(f84,plain,(
% 3.92/1.00    ( ! [X1] : (r1_tarski(X1,X1)) )),
% 3.92/1.00    inference(equality_resolution,[],[f50])).
% 3.92/1.00  
% 3.92/1.00  fof(f5,axiom,(
% 3.92/1.00    ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) <=> r1_tarski(X0,X1))),
% 3.92/1.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.92/1.00  
% 3.92/1.00  fof(f34,plain,(
% 3.92/1.00    ! [X0,X1] : ((m1_subset_1(X0,k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1)) & (r1_tarski(X0,X1) | ~m1_subset_1(X0,k1_zfmisc_1(X1))))),
% 3.92/1.00    inference(nnf_transformation,[],[f5])).
% 3.92/1.00  
% 3.92/1.00  fof(f55,plain,(
% 3.92/1.00    ( ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1)) )),
% 3.92/1.00    inference(cnf_transformation,[],[f34])).
% 3.92/1.00  
% 3.92/1.00  fof(f7,axiom,(
% 3.92/1.00    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) => (l1_orders_2(g1_orders_2(X0,X1)) & v1_orders_2(g1_orders_2(X0,X1))))),
% 3.92/1.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.92/1.00  
% 3.92/1.00  fof(f18,plain,(
% 3.92/1.00    ! [X0,X1] : ((l1_orders_2(g1_orders_2(X0,X1)) & v1_orders_2(g1_orders_2(X0,X1))) | ~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))))),
% 3.92/1.00    inference(ennf_transformation,[],[f7])).
% 3.92/1.00  
% 3.92/1.00  fof(f58,plain,(
% 3.92/1.00    ( ! [X0,X1] : (l1_orders_2(g1_orders_2(X0,X1)) | ~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))) )),
% 3.92/1.00    inference(cnf_transformation,[],[f18])).
% 3.92/1.00  
% 3.92/1.00  fof(f6,axiom,(
% 3.92/1.00    ! [X0] : (l1_orders_2(X0) => (v1_orders_2(X0) => g1_orders_2(u1_struct_0(X0),u1_orders_2(X0)) = X0))),
% 3.92/1.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.92/1.00  
% 3.92/1.00  fof(f16,plain,(
% 3.92/1.00    ! [X0] : ((g1_orders_2(u1_struct_0(X0),u1_orders_2(X0)) = X0 | ~v1_orders_2(X0)) | ~l1_orders_2(X0))),
% 3.92/1.00    inference(ennf_transformation,[],[f6])).
% 3.92/1.00  
% 3.92/1.00  fof(f17,plain,(
% 3.92/1.00    ! [X0] : (g1_orders_2(u1_struct_0(X0),u1_orders_2(X0)) = X0 | ~v1_orders_2(X0) | ~l1_orders_2(X0))),
% 3.92/1.00    inference(flattening,[],[f16])).
% 3.92/1.00  
% 3.92/1.00  fof(f56,plain,(
% 3.92/1.00    ( ! [X0] : (g1_orders_2(u1_struct_0(X0),u1_orders_2(X0)) = X0 | ~v1_orders_2(X0) | ~l1_orders_2(X0)) )),
% 3.92/1.00    inference(cnf_transformation,[],[f17])).
% 3.92/1.00  
% 3.92/1.00  fof(f57,plain,(
% 3.92/1.00    ( ! [X0,X1] : (v1_orders_2(g1_orders_2(X0,X1)) | ~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))) )),
% 3.92/1.00    inference(cnf_transformation,[],[f18])).
% 3.92/1.00  
% 3.92/1.00  fof(f8,axiom,(
% 3.92/1.00    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) => ! [X2,X3] : (g1_orders_2(X0,X1) = g1_orders_2(X2,X3) => (X1 = X3 & X0 = X2)))),
% 3.92/1.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.92/1.00  
% 3.92/1.00  fof(f19,plain,(
% 3.92/1.00    ! [X0,X1] : (! [X2,X3] : ((X1 = X3 & X0 = X2) | g1_orders_2(X0,X1) != g1_orders_2(X2,X3)) | ~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))))),
% 3.92/1.00    inference(ennf_transformation,[],[f8])).
% 3.92/1.00  
% 3.92/1.00  fof(f59,plain,(
% 3.92/1.00    ( ! [X2,X0,X3,X1] : (X0 = X2 | g1_orders_2(X0,X1) != g1_orders_2(X2,X3) | ~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))) )),
% 3.92/1.00    inference(cnf_transformation,[],[f19])).
% 3.92/1.00  
% 3.92/1.00  fof(f9,axiom,(
% 3.92/1.00    ! [X0] : (l1_orders_2(X0) => m1_subset_1(k3_yellow_0(X0),u1_struct_0(X0)))),
% 3.92/1.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.92/1.00  
% 3.92/1.00  fof(f20,plain,(
% 3.92/1.00    ! [X0] : (m1_subset_1(k3_yellow_0(X0),u1_struct_0(X0)) | ~l1_orders_2(X0))),
% 3.92/1.00    inference(ennf_transformation,[],[f9])).
% 3.92/1.00  
% 3.92/1.00  fof(f61,plain,(
% 3.92/1.00    ( ! [X0] : (m1_subset_1(k3_yellow_0(X0),u1_struct_0(X0)) | ~l1_orders_2(X0)) )),
% 3.92/1.00    inference(cnf_transformation,[],[f20])).
% 3.92/1.00  
% 3.92/1.00  fof(f2,axiom,(
% 3.92/1.00    ! [X0,X1,X2] : (k4_xboole_0(X0,X1) = X2 <=> ! [X3] : (r2_hidden(X3,X2) <=> (~r2_hidden(X3,X1) & r2_hidden(X3,X0))))),
% 3.92/1.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.92/1.00  
% 3.92/1.00  fof(f27,plain,(
% 3.92/1.00    ! [X0,X1,X2] : ((k4_xboole_0(X0,X1) = X2 | ? [X3] : (((r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) | ~r2_hidden(X3,X2)) & ((~r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r2_hidden(X3,X2)))) & (! [X3] : ((r2_hidden(X3,X2) | (r2_hidden(X3,X1) | ~r2_hidden(X3,X0))) & ((~r2_hidden(X3,X1) & r2_hidden(X3,X0)) | ~r2_hidden(X3,X2))) | k4_xboole_0(X0,X1) != X2))),
% 3.92/1.00    inference(nnf_transformation,[],[f2])).
% 3.92/1.00  
% 3.92/1.00  fof(f28,plain,(
% 3.92/1.00    ! [X0,X1,X2] : ((k4_xboole_0(X0,X1) = X2 | ? [X3] : ((r2_hidden(X3,X1) | ~r2_hidden(X3,X0) | ~r2_hidden(X3,X2)) & ((~r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r2_hidden(X3,X2)))) & (! [X3] : ((r2_hidden(X3,X2) | r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) & ((~r2_hidden(X3,X1) & r2_hidden(X3,X0)) | ~r2_hidden(X3,X2))) | k4_xboole_0(X0,X1) != X2))),
% 3.92/1.00    inference(flattening,[],[f27])).
% 3.92/1.00  
% 3.92/1.00  fof(f29,plain,(
% 3.92/1.00    ! [X0,X1,X2] : ((k4_xboole_0(X0,X1) = X2 | ? [X3] : ((r2_hidden(X3,X1) | ~r2_hidden(X3,X0) | ~r2_hidden(X3,X2)) & ((~r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r2_hidden(X3,X2)))) & (! [X4] : ((r2_hidden(X4,X2) | r2_hidden(X4,X1) | ~r2_hidden(X4,X0)) & ((~r2_hidden(X4,X1) & r2_hidden(X4,X0)) | ~r2_hidden(X4,X2))) | k4_xboole_0(X0,X1) != X2))),
% 3.92/1.00    inference(rectify,[],[f28])).
% 3.92/1.00  
% 3.92/1.00  fof(f30,plain,(
% 3.92/1.00    ! [X2,X1,X0] : (? [X3] : ((r2_hidden(X3,X1) | ~r2_hidden(X3,X0) | ~r2_hidden(X3,X2)) & ((~r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r2_hidden(X3,X2))) => ((r2_hidden(sK0(X0,X1,X2),X1) | ~r2_hidden(sK0(X0,X1,X2),X0) | ~r2_hidden(sK0(X0,X1,X2),X2)) & ((~r2_hidden(sK0(X0,X1,X2),X1) & r2_hidden(sK0(X0,X1,X2),X0)) | r2_hidden(sK0(X0,X1,X2),X2))))),
% 3.92/1.00    introduced(choice_axiom,[])).
% 3.92/1.00  
% 3.92/1.00  fof(f31,plain,(
% 3.92/1.00    ! [X0,X1,X2] : ((k4_xboole_0(X0,X1) = X2 | ((r2_hidden(sK0(X0,X1,X2),X1) | ~r2_hidden(sK0(X0,X1,X2),X0) | ~r2_hidden(sK0(X0,X1,X2),X2)) & ((~r2_hidden(sK0(X0,X1,X2),X1) & r2_hidden(sK0(X0,X1,X2),X0)) | r2_hidden(sK0(X0,X1,X2),X2)))) & (! [X4] : ((r2_hidden(X4,X2) | r2_hidden(X4,X1) | ~r2_hidden(X4,X0)) & ((~r2_hidden(X4,X1) & r2_hidden(X4,X0)) | ~r2_hidden(X4,X2))) | k4_xboole_0(X0,X1) != X2))),
% 3.92/1.00    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f29,f30])).
% 3.92/1.00  
% 3.92/1.00  fof(f47,plain,(
% 3.92/1.00    ( ! [X2,X0,X1] : (k4_xboole_0(X0,X1) = X2 | r2_hidden(sK0(X0,X1,X2),X0) | r2_hidden(sK0(X0,X1,X2),X2)) )),
% 3.92/1.00    inference(cnf_transformation,[],[f31])).
% 3.92/1.00  
% 3.92/1.00  fof(f4,axiom,(
% 3.92/1.00    ! [X0,X1] : k4_xboole_0(X0,X1) = k6_subset_1(X0,X1)),
% 3.92/1.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.92/1.00  
% 3.92/1.00  fof(f53,plain,(
% 3.92/1.00    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k6_subset_1(X0,X1)) )),
% 3.92/1.00    inference(cnf_transformation,[],[f4])).
% 3.92/1.00  
% 3.92/1.00  fof(f76,plain,(
% 3.92/1.00    ( ! [X2,X0,X1] : (k6_subset_1(X0,X1) = X2 | r2_hidden(sK0(X0,X1,X2),X0) | r2_hidden(sK0(X0,X1,X2),X2)) )),
% 3.92/1.00    inference(definition_unfolding,[],[f47,f53])).
% 3.92/1.00  
% 3.92/1.00  fof(f48,plain,(
% 3.92/1.00    ( ! [X2,X0,X1] : (k4_xboole_0(X0,X1) = X2 | ~r2_hidden(sK0(X0,X1,X2),X1) | r2_hidden(sK0(X0,X1,X2),X2)) )),
% 3.92/1.00    inference(cnf_transformation,[],[f31])).
% 3.92/1.00  
% 3.92/1.00  fof(f75,plain,(
% 3.92/1.00    ( ! [X2,X0,X1] : (k6_subset_1(X0,X1) = X2 | ~r2_hidden(sK0(X0,X1,X2),X1) | r2_hidden(sK0(X0,X1,X2),X2)) )),
% 3.92/1.00    inference(definition_unfolding,[],[f48,f53])).
% 3.92/1.00  
% 3.92/1.00  fof(f44,plain,(
% 3.92/1.00    ( ! [X4,X2,X0,X1] : (r2_hidden(X4,X0) | ~r2_hidden(X4,X2) | k4_xboole_0(X0,X1) != X2) )),
% 3.92/1.00    inference(cnf_transformation,[],[f31])).
% 3.92/1.00  
% 3.92/1.00  fof(f79,plain,(
% 3.92/1.00    ( ! [X4,X2,X0,X1] : (r2_hidden(X4,X0) | ~r2_hidden(X4,X2) | k6_subset_1(X0,X1) != X2) )),
% 3.92/1.00    inference(definition_unfolding,[],[f44,f53])).
% 3.92/1.00  
% 3.92/1.00  fof(f82,plain,(
% 3.92/1.00    ( ! [X4,X0,X1] : (r2_hidden(X4,X0) | ~r2_hidden(X4,k6_subset_1(X0,X1))) )),
% 3.92/1.00    inference(equality_resolution,[],[f79])).
% 3.92/1.00  
% 3.92/1.00  fof(f45,plain,(
% 3.92/1.00    ( ! [X4,X2,X0,X1] : (~r2_hidden(X4,X1) | ~r2_hidden(X4,X2) | k4_xboole_0(X0,X1) != X2) )),
% 3.92/1.00    inference(cnf_transformation,[],[f31])).
% 3.92/1.00  
% 3.92/1.00  fof(f78,plain,(
% 3.92/1.00    ( ! [X4,X2,X0,X1] : (~r2_hidden(X4,X1) | ~r2_hidden(X4,X2) | k6_subset_1(X0,X1) != X2) )),
% 3.92/1.00    inference(definition_unfolding,[],[f45,f53])).
% 3.92/1.00  
% 3.92/1.00  fof(f81,plain,(
% 3.92/1.00    ( ! [X4,X0,X1] : (~r2_hidden(X4,X1) | ~r2_hidden(X4,k6_subset_1(X0,X1))) )),
% 3.92/1.00    inference(equality_resolution,[],[f78])).
% 3.92/1.00  
% 3.92/1.00  fof(f11,axiom,(
% 3.92/1.00    ! [X0] : ((l1_struct_0(X0) & ~v2_struct_0(X0)) => ! [X1] : ((l1_waybel_0(X1,X0) & ~v2_struct_0(X1)) => ! [X2] : (r1_waybel_0(X0,X1,X2) <=> ~r2_waybel_0(X0,X1,k6_subset_1(u1_struct_0(X0),X2)))))),
% 3.92/1.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.92/1.00  
% 3.92/1.00  fof(f23,plain,(
% 3.92/1.00    ! [X0] : (! [X1] : (! [X2] : (r1_waybel_0(X0,X1,X2) <=> ~r2_waybel_0(X0,X1,k6_subset_1(u1_struct_0(X0),X2))) | (~l1_waybel_0(X1,X0) | v2_struct_0(X1))) | (~l1_struct_0(X0) | v2_struct_0(X0)))),
% 3.92/1.00    inference(ennf_transformation,[],[f11])).
% 3.92/1.00  
% 3.92/1.00  fof(f24,plain,(
% 3.92/1.00    ! [X0] : (! [X1] : (! [X2] : (r1_waybel_0(X0,X1,X2) <=> ~r2_waybel_0(X0,X1,k6_subset_1(u1_struct_0(X0),X2))) | ~l1_waybel_0(X1,X0) | v2_struct_0(X1)) | ~l1_struct_0(X0) | v2_struct_0(X0))),
% 3.92/1.00    inference(flattening,[],[f23])).
% 3.92/1.00  
% 3.92/1.00  fof(f40,plain,(
% 3.92/1.00    ! [X0] : (! [X1] : (! [X2] : ((r1_waybel_0(X0,X1,X2) | r2_waybel_0(X0,X1,k6_subset_1(u1_struct_0(X0),X2))) & (~r2_waybel_0(X0,X1,k6_subset_1(u1_struct_0(X0),X2)) | ~r1_waybel_0(X0,X1,X2))) | ~l1_waybel_0(X1,X0) | v2_struct_0(X1)) | ~l1_struct_0(X0) | v2_struct_0(X0))),
% 3.92/1.00    inference(nnf_transformation,[],[f24])).
% 3.92/1.00  
% 3.92/1.00  fof(f68,plain,(
% 3.92/1.00    ( ! [X2,X0,X1] : (r1_waybel_0(X0,X1,X2) | r2_waybel_0(X0,X1,k6_subset_1(u1_struct_0(X0),X2)) | ~l1_waybel_0(X1,X0) | v2_struct_0(X1) | ~l1_struct_0(X0) | v2_struct_0(X0)) )),
% 3.92/1.00    inference(cnf_transformation,[],[f40])).
% 3.92/1.00  
% 3.92/1.00  fof(f12,conjecture,(
% 3.92/1.00    ! [X0] : ((l1_struct_0(X0) & ~v2_struct_0(X0)) => ! [X1] : ((l1_waybel_0(X1,X0) & v7_waybel_0(X1) & v4_orders_2(X1) & ~v2_struct_0(X1)) => r1_waybel_0(X0,X1,u1_struct_0(X0))))),
% 3.92/1.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.92/1.00  
% 3.92/1.00  fof(f13,negated_conjecture,(
% 3.92/1.00    ~! [X0] : ((l1_struct_0(X0) & ~v2_struct_0(X0)) => ! [X1] : ((l1_waybel_0(X1,X0) & v7_waybel_0(X1) & v4_orders_2(X1) & ~v2_struct_0(X1)) => r1_waybel_0(X0,X1,u1_struct_0(X0))))),
% 3.92/1.00    inference(negated_conjecture,[],[f12])).
% 3.92/1.00  
% 3.92/1.00  fof(f14,plain,(
% 3.92/1.00    ~! [X0] : ((l1_struct_0(X0) & ~v2_struct_0(X0)) => ! [X1] : ((l1_waybel_0(X1,X0) & v4_orders_2(X1) & ~v2_struct_0(X1)) => r1_waybel_0(X0,X1,u1_struct_0(X0))))),
% 3.92/1.00    inference(pure_predicate_removal,[],[f13])).
% 3.92/1.00  
% 3.92/1.00  fof(f15,plain,(
% 3.92/1.00    ~! [X0] : ((l1_struct_0(X0) & ~v2_struct_0(X0)) => ! [X1] : ((l1_waybel_0(X1,X0) & ~v2_struct_0(X1)) => r1_waybel_0(X0,X1,u1_struct_0(X0))))),
% 3.92/1.00    inference(pure_predicate_removal,[],[f14])).
% 3.92/1.00  
% 3.92/1.00  fof(f25,plain,(
% 3.92/1.00    ? [X0] : (? [X1] : (~r1_waybel_0(X0,X1,u1_struct_0(X0)) & (l1_waybel_0(X1,X0) & ~v2_struct_0(X1))) & (l1_struct_0(X0) & ~v2_struct_0(X0)))),
% 3.92/1.00    inference(ennf_transformation,[],[f15])).
% 3.92/1.00  
% 3.92/1.00  fof(f26,plain,(
% 3.92/1.00    ? [X0] : (? [X1] : (~r1_waybel_0(X0,X1,u1_struct_0(X0)) & l1_waybel_0(X1,X0) & ~v2_struct_0(X1)) & l1_struct_0(X0) & ~v2_struct_0(X0))),
% 3.92/1.00    inference(flattening,[],[f25])).
% 3.92/1.00  
% 3.92/1.00  fof(f42,plain,(
% 3.92/1.00    ( ! [X0] : (? [X1] : (~r1_waybel_0(X0,X1,u1_struct_0(X0)) & l1_waybel_0(X1,X0) & ~v2_struct_0(X1)) => (~r1_waybel_0(X0,sK4,u1_struct_0(X0)) & l1_waybel_0(sK4,X0) & ~v2_struct_0(sK4))) )),
% 3.92/1.00    introduced(choice_axiom,[])).
% 3.92/1.00  
% 3.92/1.00  fof(f41,plain,(
% 3.92/1.00    ? [X0] : (? [X1] : (~r1_waybel_0(X0,X1,u1_struct_0(X0)) & l1_waybel_0(X1,X0) & ~v2_struct_0(X1)) & l1_struct_0(X0) & ~v2_struct_0(X0)) => (? [X1] : (~r1_waybel_0(sK3,X1,u1_struct_0(sK3)) & l1_waybel_0(X1,sK3) & ~v2_struct_0(X1)) & l1_struct_0(sK3) & ~v2_struct_0(sK3))),
% 3.92/1.00    introduced(choice_axiom,[])).
% 3.92/1.00  
% 3.92/1.00  fof(f43,plain,(
% 3.92/1.00    (~r1_waybel_0(sK3,sK4,u1_struct_0(sK3)) & l1_waybel_0(sK4,sK3) & ~v2_struct_0(sK4)) & l1_struct_0(sK3) & ~v2_struct_0(sK3)),
% 3.92/1.00    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3,sK4])],[f26,f42,f41])).
% 3.92/1.00  
% 3.92/1.00  fof(f73,plain,(
% 3.92/1.00    ~r1_waybel_0(sK3,sK4,u1_struct_0(sK3))),
% 3.92/1.00    inference(cnf_transformation,[],[f43])).
% 3.92/1.00  
% 3.92/1.00  fof(f69,plain,(
% 3.92/1.00    ~v2_struct_0(sK3)),
% 3.92/1.00    inference(cnf_transformation,[],[f43])).
% 3.92/1.00  
% 3.92/1.00  fof(f70,plain,(
% 3.92/1.00    l1_struct_0(sK3)),
% 3.92/1.00    inference(cnf_transformation,[],[f43])).
% 3.92/1.00  
% 3.92/1.00  fof(f71,plain,(
% 3.92/1.00    ~v2_struct_0(sK4)),
% 3.92/1.00    inference(cnf_transformation,[],[f43])).
% 3.92/1.00  
% 3.92/1.00  fof(f72,plain,(
% 3.92/1.00    l1_waybel_0(sK4,sK3)),
% 3.92/1.00    inference(cnf_transformation,[],[f43])).
% 3.92/1.00  
% 3.92/1.00  fof(f10,axiom,(
% 3.92/1.00    ! [X0] : ((l1_struct_0(X0) & ~v2_struct_0(X0)) => ! [X1] : ((l1_waybel_0(X1,X0) & ~v2_struct_0(X1)) => ! [X2] : (r2_waybel_0(X0,X1,X2) <=> ! [X3] : (m1_subset_1(X3,u1_struct_0(X1)) => ? [X4] : (r2_hidden(k2_waybel_0(X0,X1,X4),X2) & r1_orders_2(X1,X3,X4) & m1_subset_1(X4,u1_struct_0(X1)))))))),
% 3.92/1.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.92/1.00  
% 3.92/1.00  fof(f21,plain,(
% 3.92/1.00    ! [X0] : (! [X1] : (! [X2] : (r2_waybel_0(X0,X1,X2) <=> ! [X3] : (? [X4] : (r2_hidden(k2_waybel_0(X0,X1,X4),X2) & r1_orders_2(X1,X3,X4) & m1_subset_1(X4,u1_struct_0(X1))) | ~m1_subset_1(X3,u1_struct_0(X1)))) | (~l1_waybel_0(X1,X0) | v2_struct_0(X1))) | (~l1_struct_0(X0) | v2_struct_0(X0)))),
% 3.92/1.00    inference(ennf_transformation,[],[f10])).
% 3.92/1.00  
% 3.92/1.00  fof(f22,plain,(
% 3.92/1.00    ! [X0] : (! [X1] : (! [X2] : (r2_waybel_0(X0,X1,X2) <=> ! [X3] : (? [X4] : (r2_hidden(k2_waybel_0(X0,X1,X4),X2) & r1_orders_2(X1,X3,X4) & m1_subset_1(X4,u1_struct_0(X1))) | ~m1_subset_1(X3,u1_struct_0(X1)))) | ~l1_waybel_0(X1,X0) | v2_struct_0(X1)) | ~l1_struct_0(X0) | v2_struct_0(X0))),
% 3.92/1.00    inference(flattening,[],[f21])).
% 3.92/1.00  
% 3.92/1.00  fof(f35,plain,(
% 3.92/1.00    ! [X0] : (! [X1] : (! [X2] : ((r2_waybel_0(X0,X1,X2) | ? [X3] : (! [X4] : (~r2_hidden(k2_waybel_0(X0,X1,X4),X2) | ~r1_orders_2(X1,X3,X4) | ~m1_subset_1(X4,u1_struct_0(X1))) & m1_subset_1(X3,u1_struct_0(X1)))) & (! [X3] : (? [X4] : (r2_hidden(k2_waybel_0(X0,X1,X4),X2) & r1_orders_2(X1,X3,X4) & m1_subset_1(X4,u1_struct_0(X1))) | ~m1_subset_1(X3,u1_struct_0(X1))) | ~r2_waybel_0(X0,X1,X2))) | ~l1_waybel_0(X1,X0) | v2_struct_0(X1)) | ~l1_struct_0(X0) | v2_struct_0(X0))),
% 3.92/1.00    inference(nnf_transformation,[],[f22])).
% 3.92/1.00  
% 3.92/1.00  fof(f36,plain,(
% 3.92/1.00    ! [X0] : (! [X1] : (! [X2] : ((r2_waybel_0(X0,X1,X2) | ? [X3] : (! [X4] : (~r2_hidden(k2_waybel_0(X0,X1,X4),X2) | ~r1_orders_2(X1,X3,X4) | ~m1_subset_1(X4,u1_struct_0(X1))) & m1_subset_1(X3,u1_struct_0(X1)))) & (! [X5] : (? [X6] : (r2_hidden(k2_waybel_0(X0,X1,X6),X2) & r1_orders_2(X1,X5,X6) & m1_subset_1(X6,u1_struct_0(X1))) | ~m1_subset_1(X5,u1_struct_0(X1))) | ~r2_waybel_0(X0,X1,X2))) | ~l1_waybel_0(X1,X0) | v2_struct_0(X1)) | ~l1_struct_0(X0) | v2_struct_0(X0))),
% 3.92/1.00    inference(rectify,[],[f35])).
% 3.92/1.00  
% 3.92/1.00  fof(f38,plain,(
% 3.92/1.00    ! [X5,X2,X1,X0] : (? [X6] : (r2_hidden(k2_waybel_0(X0,X1,X6),X2) & r1_orders_2(X1,X5,X6) & m1_subset_1(X6,u1_struct_0(X1))) => (r2_hidden(k2_waybel_0(X0,X1,sK2(X0,X1,X2,X5)),X2) & r1_orders_2(X1,X5,sK2(X0,X1,X2,X5)) & m1_subset_1(sK2(X0,X1,X2,X5),u1_struct_0(X1))))),
% 3.92/1.00    introduced(choice_axiom,[])).
% 3.92/1.00  
% 3.92/1.00  fof(f37,plain,(
% 3.92/1.00    ! [X2,X1,X0] : (? [X3] : (! [X4] : (~r2_hidden(k2_waybel_0(X0,X1,X4),X2) | ~r1_orders_2(X1,X3,X4) | ~m1_subset_1(X4,u1_struct_0(X1))) & m1_subset_1(X3,u1_struct_0(X1))) => (! [X4] : (~r2_hidden(k2_waybel_0(X0,X1,X4),X2) | ~r1_orders_2(X1,sK1(X0,X1,X2),X4) | ~m1_subset_1(X4,u1_struct_0(X1))) & m1_subset_1(sK1(X0,X1,X2),u1_struct_0(X1))))),
% 3.92/1.00    introduced(choice_axiom,[])).
% 3.92/1.00  
% 3.92/1.00  fof(f39,plain,(
% 3.92/1.00    ! [X0] : (! [X1] : (! [X2] : ((r2_waybel_0(X0,X1,X2) | (! [X4] : (~r2_hidden(k2_waybel_0(X0,X1,X4),X2) | ~r1_orders_2(X1,sK1(X0,X1,X2),X4) | ~m1_subset_1(X4,u1_struct_0(X1))) & m1_subset_1(sK1(X0,X1,X2),u1_struct_0(X1)))) & (! [X5] : ((r2_hidden(k2_waybel_0(X0,X1,sK2(X0,X1,X2,X5)),X2) & r1_orders_2(X1,X5,sK2(X0,X1,X2,X5)) & m1_subset_1(sK2(X0,X1,X2,X5),u1_struct_0(X1))) | ~m1_subset_1(X5,u1_struct_0(X1))) | ~r2_waybel_0(X0,X1,X2))) | ~l1_waybel_0(X1,X0) | v2_struct_0(X1)) | ~l1_struct_0(X0) | v2_struct_0(X0))),
% 3.92/1.00    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1,sK2])],[f36,f38,f37])).
% 3.92/1.00  
% 3.92/1.00  fof(f64,plain,(
% 3.92/1.00    ( ! [X2,X0,X5,X1] : (r2_hidden(k2_waybel_0(X0,X1,sK2(X0,X1,X2,X5)),X2) | ~m1_subset_1(X5,u1_struct_0(X1)) | ~r2_waybel_0(X0,X1,X2) | ~l1_waybel_0(X1,X0) | v2_struct_0(X1) | ~l1_struct_0(X0) | v2_struct_0(X0)) )),
% 3.92/1.00    inference(cnf_transformation,[],[f39])).
% 3.92/1.00  
% 3.92/1.00  cnf(c_8,plain,( r1_tarski(X0,X0) ),inference(cnf_transformation,[],[f84]) ).
% 3.92/1.00  
% 3.92/1.00  cnf(c_1438,plain,
% 3.92/1.00      ( r1_tarski(X0,X0) = iProver_top ),
% 3.92/1.00      inference(predicate_to_equality,[status(thm)],[c_8]) ).
% 3.92/1.00  
% 3.92/1.00  cnf(c_9,plain,
% 3.92/1.00      ( m1_subset_1(X0,k1_zfmisc_1(X1)) | ~ r1_tarski(X0,X1) ),
% 3.92/1.00      inference(cnf_transformation,[],[f55]) ).
% 3.92/1.00  
% 3.92/1.00  cnf(c_1437,plain,
% 3.92/1.00      ( m1_subset_1(X0,k1_zfmisc_1(X1)) = iProver_top
% 3.92/1.00      | r1_tarski(X0,X1) != iProver_top ),
% 3.92/1.00      inference(predicate_to_equality,[status(thm)],[c_9]) ).
% 3.92/1.00  
% 3.92/1.00  cnf(c_12,plain,
% 3.92/1.00      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X1)))
% 3.92/1.00      | l1_orders_2(g1_orders_2(X1,X0)) ),
% 3.92/1.00      inference(cnf_transformation,[],[f58]) ).
% 3.92/1.00  
% 3.92/1.00  cnf(c_1434,plain,
% 3.92/1.00      ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X1))) != iProver_top
% 3.92/1.00      | l1_orders_2(g1_orders_2(X1,X0)) = iProver_top ),
% 3.92/1.00      inference(predicate_to_equality,[status(thm)],[c_12]) ).
% 3.92/1.00  
% 3.92/1.00  cnf(c_2014,plain,
% 3.92/1.00      ( r1_tarski(X0,k2_zfmisc_1(X1,X1)) != iProver_top
% 3.92/1.00      | l1_orders_2(g1_orders_2(X1,X0)) = iProver_top ),
% 3.92/1.00      inference(superposition,[status(thm)],[c_1437,c_1434]) ).
% 3.92/1.00  
% 3.92/1.00  cnf(c_2094,plain,
% 3.92/1.00      ( l1_orders_2(g1_orders_2(X0,k2_zfmisc_1(X0,X0))) = iProver_top ),
% 3.92/1.00      inference(superposition,[status(thm)],[c_1438,c_2014]) ).
% 3.92/1.00  
% 3.92/1.00  cnf(c_11,plain,
% 3.92/1.00      ( ~ l1_orders_2(X0)
% 3.92/1.00      | ~ v1_orders_2(X0)
% 3.92/1.00      | g1_orders_2(u1_struct_0(X0),u1_orders_2(X0)) = X0 ),
% 3.92/1.00      inference(cnf_transformation,[],[f56]) ).
% 3.92/1.00  
% 3.92/1.00  cnf(c_1435,plain,
% 3.92/1.00      ( g1_orders_2(u1_struct_0(X0),u1_orders_2(X0)) = X0
% 3.92/1.00      | l1_orders_2(X0) != iProver_top
% 3.92/1.00      | v1_orders_2(X0) != iProver_top ),
% 3.92/1.00      inference(predicate_to_equality,[status(thm)],[c_11]) ).
% 3.92/1.00  
% 3.92/1.00  cnf(c_2261,plain,
% 3.92/1.00      ( g1_orders_2(u1_struct_0(g1_orders_2(X0,k2_zfmisc_1(X0,X0))),u1_orders_2(g1_orders_2(X0,k2_zfmisc_1(X0,X0)))) = g1_orders_2(X0,k2_zfmisc_1(X0,X0))
% 3.92/1.00      | v1_orders_2(g1_orders_2(X0,k2_zfmisc_1(X0,X0))) != iProver_top ),
% 3.92/1.00      inference(superposition,[status(thm)],[c_2094,c_1435]) ).
% 3.92/1.00  
% 3.92/1.00  cnf(c_13,plain,
% 3.92/1.00      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X1)))
% 3.92/1.00      | v1_orders_2(g1_orders_2(X1,X0)) ),
% 3.92/1.00      inference(cnf_transformation,[],[f57]) ).
% 3.92/1.00  
% 3.92/1.00  cnf(c_1433,plain,
% 3.92/1.00      ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X1))) != iProver_top
% 3.92/1.00      | v1_orders_2(g1_orders_2(X1,X0)) = iProver_top ),
% 3.92/1.00      inference(predicate_to_equality,[status(thm)],[c_13]) ).
% 3.92/1.00  
% 3.92/1.00  cnf(c_1907,plain,
% 3.92/1.00      ( r1_tarski(X0,k2_zfmisc_1(X1,X1)) != iProver_top
% 3.92/1.00      | v1_orders_2(g1_orders_2(X1,X0)) = iProver_top ),
% 3.92/1.00      inference(superposition,[status(thm)],[c_1437,c_1433]) ).
% 3.92/1.00  
% 3.92/1.00  cnf(c_1912,plain,
% 3.92/1.00      ( v1_orders_2(g1_orders_2(X0,k2_zfmisc_1(X0,X0))) = iProver_top ),
% 3.92/1.00      inference(superposition,[status(thm)],[c_1438,c_1907]) ).
% 3.92/1.00  
% 3.92/1.00  cnf(c_2493,plain,
% 3.92/1.00      ( g1_orders_2(u1_struct_0(g1_orders_2(X0,k2_zfmisc_1(X0,X0))),u1_orders_2(g1_orders_2(X0,k2_zfmisc_1(X0,X0)))) = g1_orders_2(X0,k2_zfmisc_1(X0,X0)) ),
% 3.92/1.00      inference(global_propositional_subsumption,[status(thm)],[c_2261,c_1912]) ).
% 3.92/1.00  
% 3.92/1.00  cnf(c_15,plain,
% 3.92/1.00      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X1)))
% 3.92/1.00      | X2 = X1
% 3.92/1.00      | g1_orders_2(X2,X3) != g1_orders_2(X1,X0) ),
% 3.92/1.00      inference(cnf_transformation,[],[f59]) ).
% 3.92/1.00  
% 3.92/1.00  cnf(c_1431,plain,
% 3.92/1.00      ( X0 = X1
% 3.92/1.00      | g1_orders_2(X0,X2) != g1_orders_2(X1,X3)
% 3.92/1.00      | m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X1))) != iProver_top ),
% 3.92/1.00      inference(predicate_to_equality,[status(thm)],[c_15]) ).
% 3.92/1.00  
% 3.92/1.00  cnf(c_2496,plain,
% 3.92/1.00      ( g1_orders_2(X0,k2_zfmisc_1(X0,X0)) != g1_orders_2(X1,X2)
% 3.92/1.00      | u1_struct_0(g1_orders_2(X0,k2_zfmisc_1(X0,X0))) = X1
% 3.92/1.00      | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X1))) != iProver_top ),
% 3.92/1.00      inference(superposition,[status(thm)],[c_2493,c_1431]) ).
% 3.92/1.00  
% 3.92/1.00  cnf(c_2514,plain,
% 3.92/1.00      ( u1_struct_0(g1_orders_2(X0,k2_zfmisc_1(X0,X0))) = X0
% 3.92/1.00      | m1_subset_1(k2_zfmisc_1(X0,X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0))) != iProver_top ),
% 3.92/1.00      inference(equality_resolution,[status(thm)],[c_2496]) ).
% 3.92/1.00  
% 3.92/1.00  cnf(c_1661,plain,
% 3.92/1.00      ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X1)))
% 3.92/1.00      | ~ r1_tarski(X0,k2_zfmisc_1(X1,X1)) ),
% 3.92/1.00      inference(instantiation,[status(thm)],[c_9]) ).
% 3.92/1.00  
% 3.92/1.00  cnf(c_1889,plain,
% 3.92/1.00      ( m1_subset_1(k2_zfmisc_1(X0,X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
% 3.92/1.00      | ~ r1_tarski(k2_zfmisc_1(X0,X0),k2_zfmisc_1(X0,X0)) ),
% 3.92/1.00      inference(instantiation,[status(thm)],[c_1661]) ).
% 3.92/1.00  
% 3.92/1.00  cnf(c_1890,plain,
% 3.92/1.00      ( m1_subset_1(k2_zfmisc_1(X0,X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0))) = iProver_top
% 3.92/1.00      | r1_tarski(k2_zfmisc_1(X0,X0),k2_zfmisc_1(X0,X0)) != iProver_top ),
% 3.92/1.00      inference(predicate_to_equality,[status(thm)],[c_1889]) ).
% 3.92/1.00  
% 3.92/1.00  cnf(c_2039,plain,
% 3.92/1.00      ( r1_tarski(k2_zfmisc_1(X0,X0),k2_zfmisc_1(X0,X0)) ),
% 3.92/1.00      inference(instantiation,[status(thm)],[c_8]) ).
% 3.92/1.00  
% 3.92/1.00  cnf(c_2040,plain,
% 3.92/1.00      ( r1_tarski(k2_zfmisc_1(X0,X0),k2_zfmisc_1(X0,X0)) = iProver_top ),
% 3.92/1.00      inference(predicate_to_equality,[status(thm)],[c_2039]) ).
% 3.92/1.00  
% 3.92/1.00  cnf(c_2608,plain,
% 3.92/1.00      ( u1_struct_0(g1_orders_2(X0,k2_zfmisc_1(X0,X0))) = X0 ),
% 3.92/1.00      inference(global_propositional_subsumption,
% 3.92/1.00                [status(thm)],
% 3.92/1.00                [c_2514,c_1890,c_2040]) ).
% 3.92/1.00  
% 3.92/1.00  cnf(c_16,plain,
% 3.92/1.00      ( m1_subset_1(k3_yellow_0(X0),u1_struct_0(X0)) | ~ l1_orders_2(X0) ),
% 3.92/1.00      inference(cnf_transformation,[],[f61]) ).
% 3.92/1.00  
% 3.92/1.00  cnf(c_1430,plain,
% 3.92/1.00      ( m1_subset_1(k3_yellow_0(X0),u1_struct_0(X0)) = iProver_top
% 3.92/1.00      | l1_orders_2(X0) != iProver_top ),
% 3.92/1.00      inference(predicate_to_equality,[status(thm)],[c_16]) ).
% 3.92/1.00  
% 3.92/1.00  cnf(c_2615,plain,
% 3.92/1.00      ( m1_subset_1(k3_yellow_0(g1_orders_2(X0,k2_zfmisc_1(X0,X0))),X0) = iProver_top
% 3.92/1.00      | l1_orders_2(g1_orders_2(X0,k2_zfmisc_1(X0,X0))) != iProver_top ),
% 3.92/1.00      inference(superposition,[status(thm)],[c_2608,c_1430]) ).
% 3.92/1.00  
% 3.92/1.00  cnf(c_2745,plain,
% 3.92/1.00      ( m1_subset_1(k3_yellow_0(g1_orders_2(X0,k2_zfmisc_1(X0,X0))),X0) = iProver_top ),
% 3.92/1.00      inference(global_propositional_subsumption,[status(thm)],[c_2615,c_2094]) ).
% 3.92/1.00  
% 3.92/1.00  cnf(c_2,plain,
% 3.92/1.00      ( r2_hidden(sK0(X0,X1,X2),X0)
% 3.92/1.00      | r2_hidden(sK0(X0,X1,X2),X2)
% 3.92/1.00      | k6_subset_1(X0,X1) = X2 ),
% 3.92/1.00      inference(cnf_transformation,[],[f76]) ).
% 3.92/1.00  
% 3.92/1.00  cnf(c_1443,plain,
% 3.92/1.00      ( k6_subset_1(X0,X1) = X2
% 3.92/1.00      | r2_hidden(sK0(X0,X1,X2),X0) = iProver_top
% 3.92/1.00      | r2_hidden(sK0(X0,X1,X2),X2) = iProver_top ),
% 3.92/1.00      inference(predicate_to_equality,[status(thm)],[c_2]) ).
% 3.92/1.00  
% 3.92/1.00  cnf(c_1,plain,
% 3.92/1.00      ( ~ r2_hidden(sK0(X0,X1,X2),X1)
% 3.92/1.00      | r2_hidden(sK0(X0,X1,X2),X2)
% 3.92/1.00      | k6_subset_1(X0,X1) = X2 ),
% 3.92/1.00      inference(cnf_transformation,[],[f75]) ).
% 3.92/1.00  
% 3.92/1.00  cnf(c_1444,plain,
% 3.92/1.00      ( k6_subset_1(X0,X1) = X2
% 3.92/1.00      | r2_hidden(sK0(X0,X1,X2),X1) != iProver_top
% 3.92/1.00      | r2_hidden(sK0(X0,X1,X2),X2) = iProver_top ),
% 3.92/1.00      inference(predicate_to_equality,[status(thm)],[c_1]) ).
% 3.92/1.00  
% 3.92/1.00  cnf(c_2880,plain,
% 3.92/1.00      ( k6_subset_1(X0,X0) = X1 | r2_hidden(sK0(X0,X0,X1),X1) = iProver_top ),
% 3.92/1.00      inference(superposition,[status(thm)],[c_1443,c_1444]) ).
% 3.92/1.00  
% 3.92/1.00  cnf(c_5,plain,
% 3.92/1.00      ( r2_hidden(X0,X1) | ~ r2_hidden(X0,k6_subset_1(X1,X2)) ),
% 3.92/1.00      inference(cnf_transformation,[],[f82]) ).
% 3.92/1.00  
% 3.92/1.00  cnf(c_1440,plain,
% 3.92/1.00      ( r2_hidden(X0,X1) = iProver_top
% 3.92/1.00      | r2_hidden(X0,k6_subset_1(X1,X2)) != iProver_top ),
% 3.92/1.00      inference(predicate_to_equality,[status(thm)],[c_5]) ).
% 3.92/1.00  
% 3.92/1.00  cnf(c_3649,plain,
% 3.92/1.00      ( k6_subset_1(X0,X0) = k6_subset_1(X1,X2)
% 3.92/1.00      | r2_hidden(sK0(X0,X0,k6_subset_1(X1,X2)),X1) = iProver_top ),
% 3.92/1.00      inference(superposition,[status(thm)],[c_2880,c_1440]) ).
% 3.92/1.00  
% 3.92/1.00  cnf(c_4,plain,
% 3.92/1.00      ( ~ r2_hidden(X0,X1) | ~ r2_hidden(X0,k6_subset_1(X2,X1)) ),
% 3.92/1.00      inference(cnf_transformation,[],[f81]) ).
% 3.92/1.00  
% 3.92/1.00  cnf(c_1441,plain,
% 3.92/1.00      ( r2_hidden(X0,X1) != iProver_top
% 3.92/1.00      | r2_hidden(X0,k6_subset_1(X2,X1)) != iProver_top ),
% 3.92/1.00      inference(predicate_to_equality,[status(thm)],[c_4]) ).
% 3.92/1.00  
% 3.92/1.00  cnf(c_3650,plain,
% 3.92/1.00      ( k6_subset_1(X0,X0) = k6_subset_1(X1,X2)
% 3.92/1.00      | r2_hidden(sK0(X0,X0,k6_subset_1(X1,X2)),X2) != iProver_top ),
% 3.92/1.00      inference(superposition,[status(thm)],[c_2880,c_1441]) ).
% 3.92/1.00  
% 3.92/1.00  cnf(c_3839,plain,
% 3.92/1.00      ( k6_subset_1(X0,X0) = k6_subset_1(X1,X1) ),
% 3.92/1.00      inference(superposition,[status(thm)],[c_3649,c_3650]) ).
% 3.92/1.00  
% 3.92/1.00  cnf(c_3840,plain,
% 3.92/1.00      ( k6_subset_1(X0,X0) = sP0_iProver_split ),
% 3.92/1.00      inference(splitting,
% 3.92/1.00                [splitting(split),new_symbols(definition,[sP0_iProver_split])],
% 3.92/1.00                [c_3839]) ).
% 3.92/1.00  
% 3.92/1.00  cnf(c_22,plain,
% 3.92/1.00      ( r1_waybel_0(X0,X1,X2)
% 3.92/1.00      | r2_waybel_0(X0,X1,k6_subset_1(u1_struct_0(X0),X2))
% 3.92/1.00      | ~ l1_waybel_0(X1,X0)
% 3.92/1.00      | ~ l1_struct_0(X0)
% 3.92/1.00      | v2_struct_0(X0)
% 3.92/1.00      | v2_struct_0(X1) ),
% 3.92/1.00      inference(cnf_transformation,[],[f68]) ).
% 3.92/1.00  
% 3.92/1.00  cnf(c_24,negated_conjecture,
% 3.92/1.00      ( ~ r1_waybel_0(sK3,sK4,u1_struct_0(sK3)) ),
% 3.92/1.00      inference(cnf_transformation,[],[f73]) ).
% 3.92/1.00  
% 3.92/1.00  cnf(c_491,plain,
% 3.92/1.00      ( r2_waybel_0(X0,X1,k6_subset_1(u1_struct_0(X0),X2))
% 3.92/1.00      | ~ l1_waybel_0(X1,X0)
% 3.92/1.00      | ~ l1_struct_0(X0)
% 3.92/1.00      | v2_struct_0(X0)
% 3.92/1.00      | v2_struct_0(X1)
% 3.92/1.00      | u1_struct_0(sK3) != X2
% 3.92/1.00      | sK4 != X1
% 3.92/1.00      | sK3 != X0 ),
% 3.92/1.00      inference(resolution_lifted,[status(thm)],[c_22,c_24]) ).
% 3.92/1.00  
% 3.92/1.00  cnf(c_492,plain,
% 3.92/1.00      ( r2_waybel_0(sK3,sK4,k6_subset_1(u1_struct_0(sK3),u1_struct_0(sK3)))
% 3.92/1.00      | ~ l1_waybel_0(sK4,sK3)
% 3.92/1.00      | ~ l1_struct_0(sK3)
% 3.92/1.00      | v2_struct_0(sK4)
% 3.92/1.00      | v2_struct_0(sK3) ),
% 3.92/1.00      inference(unflattening,[status(thm)],[c_491]) ).
% 3.92/1.00  
% 3.92/1.00  cnf(c_28,negated_conjecture,
% 3.92/1.00      ( ~ v2_struct_0(sK3) ),
% 3.92/1.00      inference(cnf_transformation,[],[f69]) ).
% 3.92/1.00  
% 3.92/1.00  cnf(c_27,negated_conjecture,
% 3.92/1.00      ( l1_struct_0(sK3) ),
% 3.92/1.00      inference(cnf_transformation,[],[f70]) ).
% 3.92/1.00  
% 3.92/1.00  cnf(c_26,negated_conjecture,
% 3.92/1.00      ( ~ v2_struct_0(sK4) ),
% 3.92/1.00      inference(cnf_transformation,[],[f71]) ).
% 3.92/1.00  
% 3.92/1.00  cnf(c_25,negated_conjecture,
% 3.92/1.00      ( l1_waybel_0(sK4,sK3) ),
% 3.92/1.00      inference(cnf_transformation,[],[f72]) ).
% 3.92/1.00  
% 3.92/1.00  cnf(c_494,plain,
% 3.92/1.00      ( r2_waybel_0(sK3,sK4,k6_subset_1(u1_struct_0(sK3),u1_struct_0(sK3))) ),
% 3.92/1.00      inference(global_propositional_subsumption,
% 3.92/1.00                [status(thm)],
% 3.92/1.00                [c_492,c_28,c_27,c_26,c_25]) ).
% 3.92/1.00  
% 3.92/1.00  cnf(c_1421,plain,
% 3.92/1.00      ( r2_waybel_0(sK3,sK4,k6_subset_1(u1_struct_0(sK3),u1_struct_0(sK3))) = iProver_top ),
% 3.92/1.00      inference(predicate_to_equality,[status(thm)],[c_494]) ).
% 3.92/1.00  
% 3.92/1.00  cnf(c_4027,plain,
% 3.92/1.00      ( r2_waybel_0(sK3,sK4,sP0_iProver_split) = iProver_top ),
% 3.92/1.00      inference(demodulation,[status(thm)],[c_3840,c_1421]) ).
% 3.92/1.00  
% 3.92/1.00  cnf(c_19,plain,
% 3.92/1.00      ( ~ r2_waybel_0(X0,X1,X2)
% 3.92/1.00      | ~ l1_waybel_0(X1,X0)
% 3.92/1.00      | ~ m1_subset_1(X3,u1_struct_0(X1))
% 3.92/1.00      | r2_hidden(k2_waybel_0(X0,X1,sK2(X0,X1,X2,X3)),X2)
% 3.92/1.00      | ~ l1_struct_0(X0)
% 3.92/1.00      | v2_struct_0(X0)
% 3.92/1.00      | v2_struct_0(X1) ),
% 3.92/1.00      inference(cnf_transformation,[],[f64]) ).
% 3.92/1.00  
% 3.92/1.00  cnf(c_1428,plain,
% 3.92/1.00      ( r2_waybel_0(X0,X1,X2) != iProver_top
% 3.92/1.00      | l1_waybel_0(X1,X0) != iProver_top
% 3.92/1.00      | m1_subset_1(X3,u1_struct_0(X1)) != iProver_top
% 3.92/1.00      | r2_hidden(k2_waybel_0(X0,X1,sK2(X0,X1,X2,X3)),X2) = iProver_top
% 3.92/1.00      | l1_struct_0(X0) != iProver_top
% 3.92/1.00      | v2_struct_0(X0) = iProver_top
% 3.92/1.00      | v2_struct_0(X1) = iProver_top ),
% 3.92/1.00      inference(predicate_to_equality,[status(thm)],[c_19]) ).
% 3.92/1.00  
% 3.92/1.00  cnf(c_4037,plain,
% 3.92/1.00      ( r2_hidden(X0,X1) = iProver_top
% 3.92/1.00      | r2_hidden(X0,sP0_iProver_split) != iProver_top ),
% 3.92/1.00      inference(superposition,[status(thm)],[c_3840,c_1440]) ).
% 3.92/1.00  
% 3.92/1.00  cnf(c_4038,plain,
% 3.92/1.00      ( r2_hidden(X0,X1) != iProver_top
% 3.92/1.00      | r2_hidden(X0,sP0_iProver_split) != iProver_top ),
% 3.92/1.00      inference(superposition,[status(thm)],[c_3840,c_1441]) ).
% 3.92/1.00  
% 3.92/1.00  cnf(c_4144,plain,
% 3.92/1.00      ( r2_hidden(X0,sP0_iProver_split) != iProver_top ),
% 3.92/1.00      inference(global_propositional_subsumption,[status(thm)],[c_4037,c_4038]) ).
% 3.92/1.00  
% 3.92/1.00  cnf(c_4152,plain,
% 3.92/1.00      ( r2_waybel_0(X0,X1,sP0_iProver_split) != iProver_top
% 3.92/1.00      | l1_waybel_0(X1,X0) != iProver_top
% 3.92/1.00      | m1_subset_1(X2,u1_struct_0(X1)) != iProver_top
% 3.92/1.00      | l1_struct_0(X0) != iProver_top
% 3.92/1.00      | v2_struct_0(X0) = iProver_top
% 3.92/1.00      | v2_struct_0(X1) = iProver_top ),
% 3.92/1.00      inference(superposition,[status(thm)],[c_1428,c_4144]) ).
% 3.92/1.00  
% 3.92/1.00  cnf(c_16227,plain,
% 3.92/1.00      ( l1_waybel_0(sK4,sK3) != iProver_top
% 3.92/1.00      | m1_subset_1(X0,u1_struct_0(sK4)) != iProver_top
% 3.92/1.00      | l1_struct_0(sK3) != iProver_top
% 3.92/1.00      | v2_struct_0(sK4) = iProver_top
% 3.92/1.00      | v2_struct_0(sK3) = iProver_top ),
% 3.92/1.00      inference(superposition,[status(thm)],[c_4027,c_4152]) ).
% 3.92/1.00  
% 3.92/1.00  cnf(c_29,plain,
% 3.92/1.00      ( v2_struct_0(sK3) != iProver_top ),
% 3.92/1.00      inference(predicate_to_equality,[status(thm)],[c_28]) ).
% 3.92/1.00  
% 3.92/1.00  cnf(c_30,plain,
% 3.92/1.00      ( l1_struct_0(sK3) = iProver_top ),
% 3.92/1.00      inference(predicate_to_equality,[status(thm)],[c_27]) ).
% 3.92/1.00  
% 3.92/1.00  cnf(c_31,plain,
% 3.92/1.00      ( v2_struct_0(sK4) != iProver_top ),
% 3.92/1.00      inference(predicate_to_equality,[status(thm)],[c_26]) ).
% 3.92/1.00  
% 3.92/1.00  cnf(c_32,plain,
% 3.92/1.00      ( l1_waybel_0(sK4,sK3) = iProver_top ),
% 3.92/1.00      inference(predicate_to_equality,[status(thm)],[c_25]) ).
% 3.92/1.00  
% 3.92/1.00  cnf(c_16942,plain,
% 3.92/1.00      ( m1_subset_1(X0,u1_struct_0(sK4)) != iProver_top ),
% 3.92/1.00      inference(global_propositional_subsumption,
% 3.92/1.00                [status(thm)],
% 3.92/1.00                [c_16227,c_29,c_30,c_31,c_32]) ).
% 3.92/1.00  
% 3.92/1.00  cnf(c_16951,plain,
% 3.92/1.00      ( $false ),
% 3.92/1.00      inference(superposition,[status(thm)],[c_2745,c_16942]) ).
% 3.92/1.00  
% 3.92/1.00  
% 3.92/1.00  % SZS output end CNFRefutation for theBenchmark.p
% 3.92/1.00  
% 3.92/1.00  ------                               Statistics
% 3.92/1.00  
% 3.92/1.00  ------ General
% 3.92/1.01  
% 3.92/1.01  abstr_ref_over_cycles:                  0
% 3.92/1.01  abstr_ref_under_cycles:                 0
% 3.92/1.01  gc_basic_clause_elim:                   0
% 3.92/1.01  forced_gc_time:                         0
% 3.92/1.01  parsing_time:                           0.008
% 3.92/1.01  unif_index_cands_time:                  0.
% 3.92/1.01  unif_index_add_time:                    0.
% 3.92/1.01  orderings_time:                         0.
% 3.92/1.01  out_proof_time:                         0.009
% 3.92/1.01  total_time:                             0.492
% 3.92/1.01  num_of_symbols:                         56
% 3.92/1.01  num_of_terms:                           27767
% 3.92/1.01  
% 3.92/1.01  ------ Preprocessing
% 3.92/1.01  
% 3.92/1.01  num_of_splits:                          0
% 3.92/1.01  num_of_split_atoms:                     1
% 3.92/1.01  num_of_reused_defs:                     0
% 3.92/1.01  num_eq_ax_congr_red:                    56
% 3.92/1.01  num_of_sem_filtered_clauses:            1
% 3.92/1.01  num_of_subtypes:                        0
% 3.92/1.01  monotx_restored_types:                  0
% 3.92/1.01  sat_num_of_epr_types:                   0
% 3.92/1.01  sat_num_of_non_cyclic_types:            0
% 3.92/1.01  sat_guarded_non_collapsed_types:        0
% 3.92/1.01  num_pure_diseq_elim:                    0
% 3.92/1.01  simp_replaced_by:                       0
% 3.92/1.01  res_preprocessed:                       136
% 3.92/1.01  prep_upred:                             0
% 3.92/1.01  prep_unflattend:                        12
% 3.92/1.01  smt_new_axioms:                         0
% 3.92/1.01  pred_elim_cands:                        9
% 3.92/1.01  pred_elim:                              2
% 3.92/1.01  pred_elim_cl:                           3
% 3.92/1.01  pred_elim_cycles:                       7
% 3.92/1.01  merged_defs:                            8
% 3.92/1.01  merged_defs_ncl:                        0
% 3.92/1.01  bin_hyper_res:                          8
% 3.92/1.01  prep_cycles:                            4
% 3.92/1.01  pred_elim_time:                         0.002
% 3.92/1.01  splitting_time:                         0.
% 3.92/1.01  sem_filter_time:                        0.
% 3.92/1.01  monotx_time:                            0.
% 3.92/1.01  subtype_inf_time:                       0.
% 3.92/1.01  
% 3.92/1.01  ------ Problem properties
% 3.92/1.01  
% 3.92/1.01  clauses:                                25
% 3.92/1.01  conjectures:                            4
% 3.92/1.01  epr:                                    6
% 3.92/1.01  horn:                                   17
% 3.92/1.01  ground:                                 5
% 3.92/1.01  unary:                                  6
% 3.92/1.01  binary:                                 7
% 3.92/1.01  lits:                                   75
% 3.92/1.01  lits_eq:                                9
% 3.92/1.01  fd_pure:                                0
% 3.92/1.01  fd_pseudo:                              0
% 3.92/1.01  fd_cond:                                0
% 3.92/1.01  fd_pseudo_cond:                         6
% 3.92/1.01  ac_symbols:                             0
% 3.92/1.01  
% 3.92/1.01  ------ Propositional Solver
% 3.92/1.01  
% 3.92/1.01  prop_solver_calls:                      33
% 3.92/1.01  prop_fast_solver_calls:                 1304
% 3.92/1.01  smt_solver_calls:                       0
% 3.92/1.01  smt_fast_solver_calls:                  0
% 3.92/1.01  prop_num_of_clauses:                    5793
% 3.92/1.01  prop_preprocess_simplified:             12900
% 3.92/1.01  prop_fo_subsumed:                       26
% 3.92/1.01  prop_solver_time:                       0.
% 3.92/1.01  smt_solver_time:                        0.
% 3.92/1.01  smt_fast_solver_time:                   0.
% 3.92/1.01  prop_fast_solver_time:                  0.
% 3.92/1.01  prop_unsat_core_time:                   0.
% 3.92/1.01  
% 3.92/1.01  ------ QBF
% 3.92/1.01  
% 3.92/1.01  qbf_q_res:                              0
% 3.92/1.01  qbf_num_tautologies:                    0
% 3.92/1.01  qbf_prep_cycles:                        0
% 3.92/1.01  
% 3.92/1.01  ------ BMC1
% 3.92/1.01  
% 3.92/1.01  bmc1_current_bound:                     -1
% 3.92/1.01  bmc1_last_solved_bound:                 -1
% 3.92/1.01  bmc1_unsat_core_size:                   -1
% 3.92/1.01  bmc1_unsat_core_parents_size:           -1
% 3.92/1.01  bmc1_merge_next_fun:                    0
% 3.92/1.01  bmc1_unsat_core_clauses_time:           0.
% 3.92/1.01  
% 3.92/1.01  ------ Instantiation
% 3.92/1.01  
% 3.92/1.01  inst_num_of_clauses:                    1457
% 3.92/1.01  inst_num_in_passive:                    537
% 3.92/1.01  inst_num_in_active:                     622
% 3.92/1.01  inst_num_in_unprocessed:                301
% 3.92/1.01  inst_num_of_loops:                      700
% 3.92/1.01  inst_num_of_learning_restarts:          0
% 3.92/1.01  inst_num_moves_active_passive:          69
% 3.92/1.01  inst_lit_activity:                      0
% 3.92/1.01  inst_lit_activity_moves:                0
% 3.92/1.01  inst_num_tautologies:                   0
% 3.92/1.01  inst_num_prop_implied:                  0
% 3.92/1.01  inst_num_existing_simplified:           0
% 3.92/1.01  inst_num_eq_res_simplified:             0
% 3.92/1.01  inst_num_child_elim:                    0
% 3.92/1.01  inst_num_of_dismatching_blockings:      2793
% 3.92/1.01  inst_num_of_non_proper_insts:           2637
% 3.92/1.01  inst_num_of_duplicates:                 0
% 3.92/1.01  inst_inst_num_from_inst_to_res:         0
% 3.92/1.01  inst_dismatching_checking_time:         0.
% 3.92/1.01  
% 3.92/1.01  ------ Resolution
% 3.92/1.01  
% 3.92/1.01  res_num_of_clauses:                     0
% 3.92/1.01  res_num_in_passive:                     0
% 3.92/1.01  res_num_in_active:                      0
% 3.92/1.01  res_num_of_loops:                       140
% 3.92/1.01  res_forward_subset_subsumed:            155
% 3.92/1.01  res_backward_subset_subsumed:           12
% 3.92/1.01  res_forward_subsumed:                   0
% 3.92/1.01  res_backward_subsumed:                  0
% 3.92/1.01  res_forward_subsumption_resolution:     2
% 3.92/1.01  res_backward_subsumption_resolution:    0
% 3.92/1.01  res_clause_to_clause_subsumption:       3896
% 3.92/1.01  res_orphan_elimination:                 0
% 3.92/1.01  res_tautology_del:                      329
% 3.92/1.01  res_num_eq_res_simplified:              0
% 3.92/1.01  res_num_sel_changes:                    0
% 3.92/1.01  res_moves_from_active_to_pass:          0
% 3.92/1.01  
% 3.92/1.01  ------ Superposition
% 3.92/1.01  
% 3.92/1.01  sup_time_total:                         0.
% 3.92/1.01  sup_time_generating:                    0.
% 3.92/1.01  sup_time_sim_full:                      0.
% 3.92/1.01  sup_time_sim_immed:                     0.
% 3.92/1.01  
% 3.92/1.01  sup_num_of_clauses:                     301
% 3.92/1.01  sup_num_in_active:                      116
% 3.92/1.01  sup_num_in_passive:                     185
% 3.92/1.01  sup_num_of_loops:                       139
% 3.92/1.01  sup_fw_superposition:                   627
% 3.92/1.01  sup_bw_superposition:                   468
% 3.92/1.01  sup_immediate_simplified:               761
% 3.92/1.01  sup_given_eliminated:                   2
% 3.92/1.01  comparisons_done:                       0
% 3.92/1.01  comparisons_avoided:                    0
% 3.92/1.01  
% 3.92/1.01  ------ Simplifications
% 3.92/1.01  
% 3.92/1.01  
% 3.92/1.01  sim_fw_subset_subsumed:                 76
% 3.92/1.01  sim_bw_subset_subsumed:                 17
% 3.92/1.01  sim_fw_subsumed:                        288
% 3.92/1.01  sim_bw_subsumed:                        11
% 3.92/1.01  sim_fw_subsumption_res:                 0
% 3.92/1.01  sim_bw_subsumption_res:                 0
% 3.92/1.01  sim_tautology_del:                      23
% 3.92/1.01  sim_eq_tautology_del:                   204
% 3.92/1.01  sim_eq_res_simp:                        7
% 3.92/1.01  sim_fw_demodulated:                     496
% 3.92/1.01  sim_bw_demodulated:                     20
% 3.92/1.01  sim_light_normalised:                   305
% 3.92/1.01  sim_joinable_taut:                      0
% 3.92/1.01  sim_joinable_simp:                      0
% 3.92/1.01  sim_ac_normalised:                      0
% 3.92/1.01  sim_smt_subsumption:                    0
% 3.92/1.01  
%------------------------------------------------------------------------------
