%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n016.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:13:00 EST 2020

% Result     : Theorem 3.14s
% Output     : CNFRefutation 3.14s
% Verified   : 
% Statistics : Number of formulae       :  130 ( 388 expanded)
%              Number of clauses        :   62 ( 104 expanded)
%              Number of leaves         :   19 ( 100 expanded)
%              Depth                    :   16
%              Number of atoms          :  479 (1996 expanded)
%              Number of equality atoms :  152 ( 409 expanded)
%              Maximal formula depth    :   14 (   5 average)
%              Maximal clause size      :   16 (   3 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f15,conjecture,(
    ! [X0] :
      ( ( l1_orders_2(X0)
        & v5_orders_2(X0)
        & v4_orders_2(X0)
        & v3_orders_2(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( m1_orders_1(X1,k1_orders_1(u1_struct_0(X0)))
         => k1_xboole_0 != k3_tarski(k4_orders_2(X0,X1)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f16,negated_conjecture,(
    ~ ! [X0] :
        ( ( l1_orders_2(X0)
          & v5_orders_2(X0)
          & v4_orders_2(X0)
          & v3_orders_2(X0)
          & ~ v2_struct_0(X0) )
       => ! [X1] :
            ( m1_orders_1(X1,k1_orders_1(u1_struct_0(X0)))
           => k1_xboole_0 != k3_tarski(k4_orders_2(X0,X1)) ) ) ),
    inference(negated_conjecture,[],[f15])).

fof(f27,plain,(
    ? [X0] :
      ( ? [X1] :
          ( k1_xboole_0 = k3_tarski(k4_orders_2(X0,X1))
          & m1_orders_1(X1,k1_orders_1(u1_struct_0(X0))) )
      & l1_orders_2(X0)
      & v5_orders_2(X0)
      & v4_orders_2(X0)
      & v3_orders_2(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f16])).

fof(f28,plain,(
    ? [X0] :
      ( ? [X1] :
          ( k1_xboole_0 = k3_tarski(k4_orders_2(X0,X1))
          & m1_orders_1(X1,k1_orders_1(u1_struct_0(X0))) )
      & l1_orders_2(X0)
      & v5_orders_2(X0)
      & v4_orders_2(X0)
      & v3_orders_2(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(flattening,[],[f27])).

fof(f41,plain,(
    ! [X0] :
      ( ? [X1] :
          ( k1_xboole_0 = k3_tarski(k4_orders_2(X0,X1))
          & m1_orders_1(X1,k1_orders_1(u1_struct_0(X0))) )
     => ( k1_xboole_0 = k3_tarski(k4_orders_2(X0,sK3))
        & m1_orders_1(sK3,k1_orders_1(u1_struct_0(X0))) ) ) ),
    introduced(choice_axiom,[])).

fof(f40,plain,
    ( ? [X0] :
        ( ? [X1] :
            ( k1_xboole_0 = k3_tarski(k4_orders_2(X0,X1))
            & m1_orders_1(X1,k1_orders_1(u1_struct_0(X0))) )
        & l1_orders_2(X0)
        & v5_orders_2(X0)
        & v4_orders_2(X0)
        & v3_orders_2(X0)
        & ~ v2_struct_0(X0) )
   => ( ? [X1] :
          ( k1_xboole_0 = k3_tarski(k4_orders_2(sK2,X1))
          & m1_orders_1(X1,k1_orders_1(u1_struct_0(sK2))) )
      & l1_orders_2(sK2)
      & v5_orders_2(sK2)
      & v4_orders_2(sK2)
      & v3_orders_2(sK2)
      & ~ v2_struct_0(sK2) ) ),
    introduced(choice_axiom,[])).

fof(f42,plain,
    ( k1_xboole_0 = k3_tarski(k4_orders_2(sK2,sK3))
    & m1_orders_1(sK3,k1_orders_1(u1_struct_0(sK2)))
    & l1_orders_2(sK2)
    & v5_orders_2(sK2)
    & v4_orders_2(sK2)
    & v3_orders_2(sK2)
    & ~ v2_struct_0(sK2) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2,sK3])],[f28,f41,f40])).

fof(f70,plain,(
    m1_orders_1(sK3,k1_orders_1(u1_struct_0(sK2))) ),
    inference(cnf_transformation,[],[f42])).

fof(f14,axiom,(
    ! [X0] :
      ( ( l1_orders_2(X0)
        & v5_orders_2(X0)
        & v4_orders_2(X0)
        & v3_orders_2(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( m1_orders_1(X1,k1_orders_1(u1_struct_0(X0)))
         => ! [X2] :
              ( m2_orders_2(X2,X0,X1)
             => r2_hidden(k1_funct_1(X1,u1_struct_0(X0)),X2) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f25,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( r2_hidden(k1_funct_1(X1,u1_struct_0(X0)),X2)
              | ~ m2_orders_2(X2,X0,X1) )
          | ~ m1_orders_1(X1,k1_orders_1(u1_struct_0(X0))) )
      | ~ l1_orders_2(X0)
      | ~ v5_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f26,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( r2_hidden(k1_funct_1(X1,u1_struct_0(X0)),X2)
              | ~ m2_orders_2(X2,X0,X1) )
          | ~ m1_orders_1(X1,k1_orders_1(u1_struct_0(X0))) )
      | ~ l1_orders_2(X0)
      | ~ v5_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f25])).

fof(f64,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(k1_funct_1(X1,u1_struct_0(X0)),X2)
      | ~ m2_orders_2(X2,X0,X1)
      | ~ m1_orders_1(X1,k1_orders_1(u1_struct_0(X0)))
      | ~ l1_orders_2(X0)
      | ~ v5_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f6,axiom,(
    ! [X0,X1] :
      ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
    <=> ( k1_xboole_0 = X1
        | k1_xboole_0 = X0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f33,plain,(
    ! [X0,X1] :
      ( ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
        | ( k1_xboole_0 != X1
          & k1_xboole_0 != X0 ) )
      & ( k1_xboole_0 = X1
        | k1_xboole_0 = X0
        | k1_xboole_0 != k2_zfmisc_1(X0,X1) ) ) ),
    inference(nnf_transformation,[],[f6])).

fof(f34,plain,(
    ! [X0,X1] :
      ( ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
        | ( k1_xboole_0 != X1
          & k1_xboole_0 != X0 ) )
      & ( k1_xboole_0 = X1
        | k1_xboole_0 = X0
        | k1_xboole_0 != k2_zfmisc_1(X0,X1) ) ) ),
    inference(flattening,[],[f33])).

fof(f52,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
      | k1_xboole_0 != X1 ) ),
    inference(cnf_transformation,[],[f34])).

fof(f77,plain,(
    ! [X0] : k1_xboole_0 = k2_zfmisc_1(X0,k1_xboole_0) ),
    inference(equality_resolution,[],[f52])).

fof(f7,axiom,(
    ! [X0,X1] : ~ r2_hidden(X0,k2_zfmisc_1(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f53,plain,(
    ! [X0,X1] : ~ r2_hidden(X0,k2_zfmisc_1(X0,X1)) ),
    inference(cnf_transformation,[],[f7])).

fof(f1,axiom,(
    ! [X0] :
      ( v1_xboole_0(X0)
    <=> ! [X1] : ~ r2_hidden(X1,X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f17,plain,(
    ! [X0] :
      ( ! [X1] : ~ r2_hidden(X1,X0)
     => v1_xboole_0(X0) ) ),
    inference(unused_predicate_definition_removal,[],[f1])).

fof(f18,plain,(
    ! [X0] :
      ( v1_xboole_0(X0)
      | ? [X1] : r2_hidden(X1,X0) ) ),
    inference(ennf_transformation,[],[f17])).

fof(f29,plain,(
    ! [X0] :
      ( ? [X1] : r2_hidden(X1,X0)
     => r2_hidden(sK0(X0),X0) ) ),
    introduced(choice_axiom,[])).

fof(f30,plain,(
    ! [X0] :
      ( v1_xboole_0(X0)
      | r2_hidden(sK0(X0),X0) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f18,f29])).

fof(f43,plain,(
    ! [X0] :
      ( v1_xboole_0(X0)
      | r2_hidden(sK0(X0),X0) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f10,axiom,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
     => m1_subset_1(k1_tarski(X0),k1_zfmisc_1(X1)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f20,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k1_tarski(X0),k1_zfmisc_1(X1))
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f56,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k1_tarski(X0),k1_zfmisc_1(X1))
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f4,axiom,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f48,plain,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    inference(cnf_transformation,[],[f4])).

fof(f5,axiom,(
    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f49,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1) ),
    inference(cnf_transformation,[],[f5])).

fof(f72,plain,(
    ! [X0] : k1_tarski(X0) = k1_enumset1(X0,X0,X0) ),
    inference(definition_unfolding,[],[f48,f49])).

fof(f74,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k1_enumset1(X0,X0,X0),k1_zfmisc_1(X1))
      | ~ r2_hidden(X0,X1) ) ),
    inference(definition_unfolding,[],[f56,f72])).

fof(f11,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f35,plain,(
    ! [X0,X1] :
      ( ( m1_subset_1(X0,k1_zfmisc_1(X1))
        | ~ r1_tarski(X0,X1) )
      & ( r1_tarski(X0,X1)
        | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ) ) ),
    inference(nnf_transformation,[],[f11])).

fof(f57,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ) ),
    inference(cnf_transformation,[],[f35])).

fof(f71,plain,(
    k1_xboole_0 = k3_tarski(k4_orders_2(sK2,sK3)) ),
    inference(cnf_transformation,[],[f42])).

fof(f9,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
     => r1_tarski(k3_tarski(X0),k3_tarski(X1)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f19,plain,(
    ! [X0,X1] :
      ( r1_tarski(k3_tarski(X0),k3_tarski(X1))
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f55,plain,(
    ! [X0,X1] :
      ( r1_tarski(k3_tarski(X0),k3_tarski(X1))
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f8,axiom,(
    ! [X0] : k3_tarski(k1_tarski(X0)) = X0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f54,plain,(
    ! [X0] : k3_tarski(k1_tarski(X0)) = X0 ),
    inference(cnf_transformation,[],[f8])).

fof(f73,plain,(
    ! [X0] : k3_tarski(k1_enumset1(X0,X0,X0)) = X0 ),
    inference(definition_unfolding,[],[f54,f72])).

fof(f65,plain,(
    ~ v2_struct_0(sK2) ),
    inference(cnf_transformation,[],[f42])).

fof(f66,plain,(
    v3_orders_2(sK2) ),
    inference(cnf_transformation,[],[f42])).

fof(f67,plain,(
    v4_orders_2(sK2) ),
    inference(cnf_transformation,[],[f42])).

fof(f68,plain,(
    v5_orders_2(sK2) ),
    inference(cnf_transformation,[],[f42])).

fof(f69,plain,(
    l1_orders_2(sK2) ),
    inference(cnf_transformation,[],[f42])).

fof(f13,axiom,(
    ! [X0,X1] :
      ( ( m1_orders_1(X1,k1_orders_1(u1_struct_0(X0)))
        & l1_orders_2(X0)
        & v5_orders_2(X0)
        & v4_orders_2(X0)
        & v3_orders_2(X0)
        & ~ v2_struct_0(X0) )
     => ~ v1_xboole_0(k4_orders_2(X0,X1)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f23,plain,(
    ! [X0,X1] :
      ( ~ v1_xboole_0(k4_orders_2(X0,X1))
      | ~ m1_orders_1(X1,k1_orders_1(u1_struct_0(X0)))
      | ~ l1_orders_2(X0)
      | ~ v5_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f24,plain,(
    ! [X0,X1] :
      ( ~ v1_xboole_0(k4_orders_2(X0,X1))
      | ~ m1_orders_1(X1,k1_orders_1(u1_struct_0(X0)))
      | ~ l1_orders_2(X0)
      | ~ v5_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f23])).

fof(f63,plain,(
    ! [X0,X1] :
      ( ~ v1_xboole_0(k4_orders_2(X0,X1))
      | ~ m1_orders_1(X1,k1_orders_1(u1_struct_0(X0)))
      | ~ l1_orders_2(X0)
      | ~ v5_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f2,axiom,(
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
    inference(nnf_transformation,[],[f2])).

fof(f32,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(flattening,[],[f31])).

fof(f46,plain,(
    ! [X0,X1] :
      ( X0 = X1
      | ~ r1_tarski(X1,X0)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f32])).

fof(f3,axiom,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f47,plain,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    inference(cnf_transformation,[],[f3])).

fof(f12,axiom,(
    ! [X0] :
      ( ( l1_orders_2(X0)
        & v5_orders_2(X0)
        & v4_orders_2(X0)
        & v3_orders_2(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( m1_orders_1(X1,k1_orders_1(u1_struct_0(X0)))
         => ! [X2] :
              ( k4_orders_2(X0,X1) = X2
            <=> ! [X3] :
                  ( r2_hidden(X3,X2)
                <=> m2_orders_2(X3,X0,X1) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f21,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( k4_orders_2(X0,X1) = X2
            <=> ! [X3] :
                  ( r2_hidden(X3,X2)
                <=> m2_orders_2(X3,X0,X1) ) )
          | ~ m1_orders_1(X1,k1_orders_1(u1_struct_0(X0))) )
      | ~ l1_orders_2(X0)
      | ~ v5_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f22,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( k4_orders_2(X0,X1) = X2
            <=> ! [X3] :
                  ( r2_hidden(X3,X2)
                <=> m2_orders_2(X3,X0,X1) ) )
          | ~ m1_orders_1(X1,k1_orders_1(u1_struct_0(X0))) )
      | ~ l1_orders_2(X0)
      | ~ v5_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f21])).

fof(f36,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( k4_orders_2(X0,X1) = X2
                | ? [X3] :
                    ( ( ~ m2_orders_2(X3,X0,X1)
                      | ~ r2_hidden(X3,X2) )
                    & ( m2_orders_2(X3,X0,X1)
                      | r2_hidden(X3,X2) ) ) )
              & ( ! [X3] :
                    ( ( r2_hidden(X3,X2)
                      | ~ m2_orders_2(X3,X0,X1) )
                    & ( m2_orders_2(X3,X0,X1)
                      | ~ r2_hidden(X3,X2) ) )
                | k4_orders_2(X0,X1) != X2 ) )
          | ~ m1_orders_1(X1,k1_orders_1(u1_struct_0(X0))) )
      | ~ l1_orders_2(X0)
      | ~ v5_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(nnf_transformation,[],[f22])).

fof(f37,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( k4_orders_2(X0,X1) = X2
                | ? [X3] :
                    ( ( ~ m2_orders_2(X3,X0,X1)
                      | ~ r2_hidden(X3,X2) )
                    & ( m2_orders_2(X3,X0,X1)
                      | r2_hidden(X3,X2) ) ) )
              & ( ! [X4] :
                    ( ( r2_hidden(X4,X2)
                      | ~ m2_orders_2(X4,X0,X1) )
                    & ( m2_orders_2(X4,X0,X1)
                      | ~ r2_hidden(X4,X2) ) )
                | k4_orders_2(X0,X1) != X2 ) )
          | ~ m1_orders_1(X1,k1_orders_1(u1_struct_0(X0))) )
      | ~ l1_orders_2(X0)
      | ~ v5_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(rectify,[],[f36])).

fof(f38,plain,(
    ! [X2,X1,X0] :
      ( ? [X3] :
          ( ( ~ m2_orders_2(X3,X0,X1)
            | ~ r2_hidden(X3,X2) )
          & ( m2_orders_2(X3,X0,X1)
            | r2_hidden(X3,X2) ) )
     => ( ( ~ m2_orders_2(sK1(X0,X1,X2),X0,X1)
          | ~ r2_hidden(sK1(X0,X1,X2),X2) )
        & ( m2_orders_2(sK1(X0,X1,X2),X0,X1)
          | r2_hidden(sK1(X0,X1,X2),X2) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f39,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( k4_orders_2(X0,X1) = X2
                | ( ( ~ m2_orders_2(sK1(X0,X1,X2),X0,X1)
                    | ~ r2_hidden(sK1(X0,X1,X2),X2) )
                  & ( m2_orders_2(sK1(X0,X1,X2),X0,X1)
                    | r2_hidden(sK1(X0,X1,X2),X2) ) ) )
              & ( ! [X4] :
                    ( ( r2_hidden(X4,X2)
                      | ~ m2_orders_2(X4,X0,X1) )
                    & ( m2_orders_2(X4,X0,X1)
                      | ~ r2_hidden(X4,X2) ) )
                | k4_orders_2(X0,X1) != X2 ) )
          | ~ m1_orders_1(X1,k1_orders_1(u1_struct_0(X0))) )
      | ~ l1_orders_2(X0)
      | ~ v5_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1])],[f37,f38])).

fof(f59,plain,(
    ! [X4,X2,X0,X1] :
      ( m2_orders_2(X4,X0,X1)
      | ~ r2_hidden(X4,X2)
      | k4_orders_2(X0,X1) != X2
      | ~ m1_orders_1(X1,k1_orders_1(u1_struct_0(X0)))
      | ~ l1_orders_2(X0)
      | ~ v5_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f39])).

fof(f80,plain,(
    ! [X4,X0,X1] :
      ( m2_orders_2(X4,X0,X1)
      | ~ r2_hidden(X4,k4_orders_2(X0,X1))
      | ~ m1_orders_1(X1,k1_orders_1(u1_struct_0(X0)))
      | ~ l1_orders_2(X0)
      | ~ v5_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(equality_resolution,[],[f59])).

cnf(c_21,negated_conjecture,
    ( m1_orders_1(sK3,k1_orders_1(u1_struct_0(sK2))) ),
    inference(cnf_transformation,[],[f70])).

cnf(c_1067,plain,
    ( m1_orders_1(sK3,k1_orders_1(u1_struct_0(sK2))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_21])).

cnf(c_19,plain,
    ( ~ m2_orders_2(X0,X1,X2)
    | ~ m1_orders_1(X2,k1_orders_1(u1_struct_0(X1)))
    | r2_hidden(k1_funct_1(X2,u1_struct_0(X1)),X0)
    | v2_struct_0(X1)
    | ~ v3_orders_2(X1)
    | ~ v4_orders_2(X1)
    | ~ v5_orders_2(X1)
    | ~ l1_orders_2(X1) ),
    inference(cnf_transformation,[],[f64])).

cnf(c_1068,plain,
    ( m2_orders_2(X0,X1,X2) != iProver_top
    | m1_orders_1(X2,k1_orders_1(u1_struct_0(X1))) != iProver_top
    | r2_hidden(k1_funct_1(X2,u1_struct_0(X1)),X0) = iProver_top
    | v2_struct_0(X1) = iProver_top
    | v3_orders_2(X1) != iProver_top
    | v4_orders_2(X1) != iProver_top
    | v5_orders_2(X1) != iProver_top
    | l1_orders_2(X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_19])).

cnf(c_5,plain,
    ( k2_zfmisc_1(X0,k1_xboole_0) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f77])).

cnf(c_8,plain,
    ( ~ r2_hidden(X0,k2_zfmisc_1(X0,X1)) ),
    inference(cnf_transformation,[],[f53])).

cnf(c_1078,plain,
    ( r2_hidden(X0,k2_zfmisc_1(X0,X1)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_8])).

cnf(c_1773,plain,
    ( r2_hidden(X0,k1_xboole_0) != iProver_top ),
    inference(superposition,[status(thm)],[c_5,c_1078])).

cnf(c_1801,plain,
    ( m2_orders_2(k1_xboole_0,X0,X1) != iProver_top
    | m1_orders_1(X1,k1_orders_1(u1_struct_0(X0))) != iProver_top
    | v2_struct_0(X0) = iProver_top
    | v3_orders_2(X0) != iProver_top
    | v4_orders_2(X0) != iProver_top
    | v5_orders_2(X0) != iProver_top
    | l1_orders_2(X0) != iProver_top ),
    inference(superposition,[status(thm)],[c_1068,c_1773])).

cnf(c_6210,plain,
    ( m2_orders_2(k1_xboole_0,sK2,sK3) != iProver_top
    | v2_struct_0(sK2) = iProver_top
    | v3_orders_2(sK2) != iProver_top
    | v4_orders_2(sK2) != iProver_top
    | v5_orders_2(sK2) != iProver_top
    | l1_orders_2(sK2) != iProver_top ),
    inference(superposition,[status(thm)],[c_1067,c_1801])).

cnf(c_0,plain,
    ( r2_hidden(sK0(X0),X0)
    | v1_xboole_0(X0) ),
    inference(cnf_transformation,[],[f43])).

cnf(c_1082,plain,
    ( r2_hidden(sK0(X0),X0) = iProver_top
    | v1_xboole_0(X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_0])).

cnf(c_11,plain,
    ( m1_subset_1(k1_enumset1(X0,X0,X0),k1_zfmisc_1(X1))
    | ~ r2_hidden(X0,X1) ),
    inference(cnf_transformation,[],[f74])).

cnf(c_1076,plain,
    ( m1_subset_1(k1_enumset1(X0,X0,X0),k1_zfmisc_1(X1)) = iProver_top
    | r2_hidden(X0,X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_11])).

cnf(c_13,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | r1_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f57])).

cnf(c_1074,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(X1)) != iProver_top
    | r1_tarski(X0,X1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_13])).

cnf(c_2262,plain,
    ( r1_tarski(k1_enumset1(X0,X0,X0),X1) = iProver_top
    | r2_hidden(X0,X1) != iProver_top ),
    inference(superposition,[status(thm)],[c_1076,c_1074])).

cnf(c_20,negated_conjecture,
    ( k1_xboole_0 = k3_tarski(k4_orders_2(sK2,sK3)) ),
    inference(cnf_transformation,[],[f71])).

cnf(c_10,plain,
    ( ~ r1_tarski(X0,X1)
    | r1_tarski(k3_tarski(X0),k3_tarski(X1)) ),
    inference(cnf_transformation,[],[f55])).

cnf(c_1077,plain,
    ( r1_tarski(X0,X1) != iProver_top
    | r1_tarski(k3_tarski(X0),k3_tarski(X1)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_10])).

cnf(c_2023,plain,
    ( r1_tarski(X0,k4_orders_2(sK2,sK3)) != iProver_top
    | r1_tarski(k3_tarski(X0),k1_xboole_0) = iProver_top ),
    inference(superposition,[status(thm)],[c_20,c_1077])).

cnf(c_2563,plain,
    ( r1_tarski(k3_tarski(k1_enumset1(X0,X0,X0)),k1_xboole_0) = iProver_top
    | r2_hidden(X0,k4_orders_2(sK2,sK3)) != iProver_top ),
    inference(superposition,[status(thm)],[c_2262,c_2023])).

cnf(c_9,plain,
    ( k3_tarski(k1_enumset1(X0,X0,X0)) = X0 ),
    inference(cnf_transformation,[],[f73])).

cnf(c_2566,plain,
    ( r1_tarski(X0,k1_xboole_0) = iProver_top
    | r2_hidden(X0,k4_orders_2(sK2,sK3)) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_2563,c_9])).

cnf(c_2650,plain,
    ( r1_tarski(sK0(k4_orders_2(sK2,sK3)),k1_xboole_0) = iProver_top
    | v1_xboole_0(k4_orders_2(sK2,sK3)) = iProver_top ),
    inference(superposition,[status(thm)],[c_1082,c_2566])).

cnf(c_26,negated_conjecture,
    ( ~ v2_struct_0(sK2) ),
    inference(cnf_transformation,[],[f65])).

cnf(c_27,plain,
    ( v2_struct_0(sK2) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_26])).

cnf(c_25,negated_conjecture,
    ( v3_orders_2(sK2) ),
    inference(cnf_transformation,[],[f66])).

cnf(c_28,plain,
    ( v3_orders_2(sK2) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_25])).

cnf(c_24,negated_conjecture,
    ( v4_orders_2(sK2) ),
    inference(cnf_transformation,[],[f67])).

cnf(c_29,plain,
    ( v4_orders_2(sK2) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_24])).

cnf(c_23,negated_conjecture,
    ( v5_orders_2(sK2) ),
    inference(cnf_transformation,[],[f68])).

cnf(c_30,plain,
    ( v5_orders_2(sK2) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_23])).

cnf(c_22,negated_conjecture,
    ( l1_orders_2(sK2) ),
    inference(cnf_transformation,[],[f69])).

cnf(c_31,plain,
    ( l1_orders_2(sK2) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_22])).

cnf(c_32,plain,
    ( m1_orders_1(sK3,k1_orders_1(u1_struct_0(sK2))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_21])).

cnf(c_18,plain,
    ( ~ m1_orders_1(X0,k1_orders_1(u1_struct_0(X1)))
    | v2_struct_0(X1)
    | ~ v3_orders_2(X1)
    | ~ v4_orders_2(X1)
    | ~ v5_orders_2(X1)
    | ~ l1_orders_2(X1)
    | ~ v1_xboole_0(k4_orders_2(X1,X0)) ),
    inference(cnf_transformation,[],[f63])).

cnf(c_1865,plain,
    ( ~ m1_orders_1(sK3,k1_orders_1(u1_struct_0(sK2)))
    | v2_struct_0(sK2)
    | ~ v3_orders_2(sK2)
    | ~ v4_orders_2(sK2)
    | ~ v5_orders_2(sK2)
    | ~ l1_orders_2(sK2)
    | ~ v1_xboole_0(k4_orders_2(sK2,sK3)) ),
    inference(instantiation,[status(thm)],[c_18])).

cnf(c_1866,plain,
    ( m1_orders_1(sK3,k1_orders_1(u1_struct_0(sK2))) != iProver_top
    | v2_struct_0(sK2) = iProver_top
    | v3_orders_2(sK2) != iProver_top
    | v4_orders_2(sK2) != iProver_top
    | v5_orders_2(sK2) != iProver_top
    | l1_orders_2(sK2) != iProver_top
    | v1_xboole_0(k4_orders_2(sK2,sK3)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1865])).

cnf(c_2677,plain,
    ( r1_tarski(sK0(k4_orders_2(sK2,sK3)),k1_xboole_0) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_2650,c_27,c_28,c_29,c_30,c_31,c_32,c_1866])).

cnf(c_1,plain,
    ( ~ r1_tarski(X0,X1)
    | ~ r1_tarski(X1,X0)
    | X0 = X1 ),
    inference(cnf_transformation,[],[f46])).

cnf(c_1081,plain,
    ( X0 = X1
    | r1_tarski(X0,X1) != iProver_top
    | r1_tarski(X1,X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1])).

cnf(c_3123,plain,
    ( sK0(k4_orders_2(sK2,sK3)) = k1_xboole_0
    | r1_tarski(k1_xboole_0,sK0(k4_orders_2(sK2,sK3))) != iProver_top ),
    inference(superposition,[status(thm)],[c_2677,c_1081])).

cnf(c_4,plain,
    ( r1_tarski(k1_xboole_0,X0) ),
    inference(cnf_transformation,[],[f47])).

cnf(c_1079,plain,
    ( r1_tarski(k1_xboole_0,X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_4])).

cnf(c_3952,plain,
    ( sK0(k4_orders_2(sK2,sK3)) = k1_xboole_0 ),
    inference(forward_subsumption_resolution,[status(thm)],[c_3123,c_1079])).

cnf(c_17,plain,
    ( m2_orders_2(X0,X1,X2)
    | ~ m1_orders_1(X2,k1_orders_1(u1_struct_0(X1)))
    | ~ r2_hidden(X0,k4_orders_2(X1,X2))
    | v2_struct_0(X1)
    | ~ v3_orders_2(X1)
    | ~ v4_orders_2(X1)
    | ~ v5_orders_2(X1)
    | ~ l1_orders_2(X1) ),
    inference(cnf_transformation,[],[f80])).

cnf(c_1070,plain,
    ( m2_orders_2(X0,X1,X2) = iProver_top
    | m1_orders_1(X2,k1_orders_1(u1_struct_0(X1))) != iProver_top
    | r2_hidden(X0,k4_orders_2(X1,X2)) != iProver_top
    | v2_struct_0(X1) = iProver_top
    | v3_orders_2(X1) != iProver_top
    | v4_orders_2(X1) != iProver_top
    | v5_orders_2(X1) != iProver_top
    | l1_orders_2(X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_17])).

cnf(c_2992,plain,
    ( m2_orders_2(X0,sK2,sK3) = iProver_top
    | r2_hidden(X0,k4_orders_2(sK2,sK3)) != iProver_top
    | v2_struct_0(sK2) = iProver_top
    | v3_orders_2(sK2) != iProver_top
    | v4_orders_2(sK2) != iProver_top
    | v5_orders_2(sK2) != iProver_top
    | l1_orders_2(sK2) != iProver_top ),
    inference(superposition,[status(thm)],[c_1067,c_1070])).

cnf(c_3300,plain,
    ( r2_hidden(X0,k4_orders_2(sK2,sK3)) != iProver_top
    | m2_orders_2(X0,sK2,sK3) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_2992,c_27,c_28,c_29,c_30,c_31])).

cnf(c_3301,plain,
    ( m2_orders_2(X0,sK2,sK3) = iProver_top
    | r2_hidden(X0,k4_orders_2(sK2,sK3)) != iProver_top ),
    inference(renaming,[status(thm)],[c_3300])).

cnf(c_3308,plain,
    ( m2_orders_2(sK0(k4_orders_2(sK2,sK3)),sK2,sK3) = iProver_top
    | v1_xboole_0(k4_orders_2(sK2,sK3)) = iProver_top ),
    inference(superposition,[status(thm)],[c_1082,c_3301])).

cnf(c_1521,plain,
    ( r2_hidden(sK0(k4_orders_2(X0,X1)),k4_orders_2(X0,X1))
    | v1_xboole_0(k4_orders_2(X0,X1)) ),
    inference(instantiation,[status(thm)],[c_0])).

cnf(c_2081,plain,
    ( r2_hidden(sK0(k4_orders_2(sK2,sK3)),k4_orders_2(sK2,sK3))
    | v1_xboole_0(k4_orders_2(sK2,sK3)) ),
    inference(instantiation,[status(thm)],[c_1521])).

cnf(c_2082,plain,
    ( r2_hidden(sK0(k4_orders_2(sK2,sK3)),k4_orders_2(sK2,sK3)) = iProver_top
    | v1_xboole_0(k4_orders_2(sK2,sK3)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2081])).

cnf(c_1371,plain,
    ( m2_orders_2(X0,sK2,X1)
    | ~ m1_orders_1(X1,k1_orders_1(u1_struct_0(sK2)))
    | ~ r2_hidden(X0,k4_orders_2(sK2,X1))
    | v2_struct_0(sK2)
    | ~ v3_orders_2(sK2)
    | ~ v4_orders_2(sK2)
    | ~ v5_orders_2(sK2)
    | ~ l1_orders_2(sK2) ),
    inference(instantiation,[status(thm)],[c_17])).

cnf(c_1511,plain,
    ( m2_orders_2(X0,sK2,sK3)
    | ~ m1_orders_1(sK3,k1_orders_1(u1_struct_0(sK2)))
    | ~ r2_hidden(X0,k4_orders_2(sK2,sK3))
    | v2_struct_0(sK2)
    | ~ v3_orders_2(sK2)
    | ~ v4_orders_2(sK2)
    | ~ v5_orders_2(sK2)
    | ~ l1_orders_2(sK2) ),
    inference(instantiation,[status(thm)],[c_1371])).

cnf(c_2384,plain,
    ( m2_orders_2(sK0(k4_orders_2(sK2,sK3)),sK2,sK3)
    | ~ m1_orders_1(sK3,k1_orders_1(u1_struct_0(sK2)))
    | ~ r2_hidden(sK0(k4_orders_2(sK2,sK3)),k4_orders_2(sK2,sK3))
    | v2_struct_0(sK2)
    | ~ v3_orders_2(sK2)
    | ~ v4_orders_2(sK2)
    | ~ v5_orders_2(sK2)
    | ~ l1_orders_2(sK2) ),
    inference(instantiation,[status(thm)],[c_1511])).

cnf(c_2385,plain,
    ( m2_orders_2(sK0(k4_orders_2(sK2,sK3)),sK2,sK3) = iProver_top
    | m1_orders_1(sK3,k1_orders_1(u1_struct_0(sK2))) != iProver_top
    | r2_hidden(sK0(k4_orders_2(sK2,sK3)),k4_orders_2(sK2,sK3)) != iProver_top
    | v2_struct_0(sK2) = iProver_top
    | v3_orders_2(sK2) != iProver_top
    | v4_orders_2(sK2) != iProver_top
    | v5_orders_2(sK2) != iProver_top
    | l1_orders_2(sK2) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2384])).

cnf(c_3702,plain,
    ( m2_orders_2(sK0(k4_orders_2(sK2,sK3)),sK2,sK3) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_3308,c_27,c_28,c_29,c_30,c_31,c_32,c_1866,c_2082,c_2385])).

cnf(c_3953,plain,
    ( m2_orders_2(k1_xboole_0,sK2,sK3) = iProver_top ),
    inference(demodulation,[status(thm)],[c_3952,c_3702])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_6210,c_3953,c_31,c_30,c_29,c_28,c_27])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.12  % Command    : iproveropt_run.sh %d %s
% 0.13/0.33  % Computer   : n016.cluster.edu
% 0.13/0.33  % Model      : x86_64 x86_64
% 0.13/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.33  % Memory     : 8042.1875MB
% 0.13/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 12:57:19 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running in FOF mode
% 3.14/0.98  % SZS status Started for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.14/0.98  
% 3.14/0.98  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 3.14/0.98  
% 3.14/0.98  ------  iProver source info
% 3.14/0.98  
% 3.14/0.98  git: date: 2020-06-30 10:37:57 +0100
% 3.14/0.98  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 3.14/0.98  git: non_committed_changes: false
% 3.14/0.98  git: last_make_outside_of_git: false
% 3.14/0.98  
% 3.14/0.98  ------ 
% 3.14/0.98  ------ Parsing...
% 3.14/0.98  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 3.14/0.98  
% 3.14/0.98  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 1 0s  sf_e 
% 3.14/0.98  
% 3.14/0.98  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 3.14/0.98  
% 3.14/0.98  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 3.14/0.98  ------ Proving...
% 3.14/0.98  ------ Problem Properties 
% 3.14/0.98  
% 3.14/0.98  
% 3.14/0.98  clauses                                 26
% 3.14/0.98  conjectures                             7
% 3.14/0.98  EPR                                     8
% 3.14/0.98  Horn                                    19
% 3.14/0.98  unary                                   13
% 3.14/0.98  binary                                  5
% 3.14/0.98  lits                                    78
% 3.14/0.98  lits eq                                 10
% 3.14/0.98  fd_pure                                 0
% 3.14/0.98  fd_pseudo                               0
% 3.14/0.98  fd_cond                                 1
% 3.14/0.98  fd_pseudo_cond                          3
% 3.14/0.98  AC symbols                              0
% 3.14/0.98  
% 3.14/0.98  ------ Input Options Time Limit: Unbounded
% 3.14/0.98  
% 3.14/0.98  
% 3.14/0.98  ------ 
% 3.14/0.98  Current options:
% 3.14/0.98  ------ 
% 3.14/0.98  
% 3.14/0.98  
% 3.14/0.98  
% 3.14/0.98  
% 3.14/0.98  ------ Proving...
% 3.14/0.98  
% 3.14/0.98  
% 3.14/0.98  % SZS status Theorem for theBenchmark.p
% 3.14/0.98  
% 3.14/0.98  % SZS output start CNFRefutation for theBenchmark.p
% 3.14/0.98  
% 3.14/0.98  fof(f15,conjecture,(
% 3.14/0.98    ! [X0] : ((l1_orders_2(X0) & v5_orders_2(X0) & v4_orders_2(X0) & v3_orders_2(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_orders_1(X1,k1_orders_1(u1_struct_0(X0))) => k1_xboole_0 != k3_tarski(k4_orders_2(X0,X1))))),
% 3.14/0.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.14/0.98  
% 3.14/0.98  fof(f16,negated_conjecture,(
% 3.14/0.98    ~! [X0] : ((l1_orders_2(X0) & v5_orders_2(X0) & v4_orders_2(X0) & v3_orders_2(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_orders_1(X1,k1_orders_1(u1_struct_0(X0))) => k1_xboole_0 != k3_tarski(k4_orders_2(X0,X1))))),
% 3.14/0.98    inference(negated_conjecture,[],[f15])).
% 3.14/0.98  
% 3.14/0.98  fof(f27,plain,(
% 3.14/0.98    ? [X0] : (? [X1] : (k1_xboole_0 = k3_tarski(k4_orders_2(X0,X1)) & m1_orders_1(X1,k1_orders_1(u1_struct_0(X0)))) & (l1_orders_2(X0) & v5_orders_2(X0) & v4_orders_2(X0) & v3_orders_2(X0) & ~v2_struct_0(X0)))),
% 3.14/0.98    inference(ennf_transformation,[],[f16])).
% 3.14/0.98  
% 3.14/0.98  fof(f28,plain,(
% 3.14/0.98    ? [X0] : (? [X1] : (k1_xboole_0 = k3_tarski(k4_orders_2(X0,X1)) & m1_orders_1(X1,k1_orders_1(u1_struct_0(X0)))) & l1_orders_2(X0) & v5_orders_2(X0) & v4_orders_2(X0) & v3_orders_2(X0) & ~v2_struct_0(X0))),
% 3.14/0.98    inference(flattening,[],[f27])).
% 3.14/0.98  
% 3.14/0.98  fof(f41,plain,(
% 3.14/0.98    ( ! [X0] : (? [X1] : (k1_xboole_0 = k3_tarski(k4_orders_2(X0,X1)) & m1_orders_1(X1,k1_orders_1(u1_struct_0(X0)))) => (k1_xboole_0 = k3_tarski(k4_orders_2(X0,sK3)) & m1_orders_1(sK3,k1_orders_1(u1_struct_0(X0))))) )),
% 3.14/0.98    introduced(choice_axiom,[])).
% 3.14/0.98  
% 3.14/0.98  fof(f40,plain,(
% 3.14/0.98    ? [X0] : (? [X1] : (k1_xboole_0 = k3_tarski(k4_orders_2(X0,X1)) & m1_orders_1(X1,k1_orders_1(u1_struct_0(X0)))) & l1_orders_2(X0) & v5_orders_2(X0) & v4_orders_2(X0) & v3_orders_2(X0) & ~v2_struct_0(X0)) => (? [X1] : (k1_xboole_0 = k3_tarski(k4_orders_2(sK2,X1)) & m1_orders_1(X1,k1_orders_1(u1_struct_0(sK2)))) & l1_orders_2(sK2) & v5_orders_2(sK2) & v4_orders_2(sK2) & v3_orders_2(sK2) & ~v2_struct_0(sK2))),
% 3.14/0.98    introduced(choice_axiom,[])).
% 3.14/0.98  
% 3.14/0.98  fof(f42,plain,(
% 3.14/0.98    (k1_xboole_0 = k3_tarski(k4_orders_2(sK2,sK3)) & m1_orders_1(sK3,k1_orders_1(u1_struct_0(sK2)))) & l1_orders_2(sK2) & v5_orders_2(sK2) & v4_orders_2(sK2) & v3_orders_2(sK2) & ~v2_struct_0(sK2)),
% 3.14/0.98    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2,sK3])],[f28,f41,f40])).
% 3.14/0.98  
% 3.14/0.98  fof(f70,plain,(
% 3.14/0.98    m1_orders_1(sK3,k1_orders_1(u1_struct_0(sK2)))),
% 3.14/0.98    inference(cnf_transformation,[],[f42])).
% 3.14/0.98  
% 3.14/0.98  fof(f14,axiom,(
% 3.14/0.98    ! [X0] : ((l1_orders_2(X0) & v5_orders_2(X0) & v4_orders_2(X0) & v3_orders_2(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_orders_1(X1,k1_orders_1(u1_struct_0(X0))) => ! [X2] : (m2_orders_2(X2,X0,X1) => r2_hidden(k1_funct_1(X1,u1_struct_0(X0)),X2))))),
% 3.14/0.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.14/0.98  
% 3.14/0.98  fof(f25,plain,(
% 3.14/0.98    ! [X0] : (! [X1] : (! [X2] : (r2_hidden(k1_funct_1(X1,u1_struct_0(X0)),X2) | ~m2_orders_2(X2,X0,X1)) | ~m1_orders_1(X1,k1_orders_1(u1_struct_0(X0)))) | (~l1_orders_2(X0) | ~v5_orders_2(X0) | ~v4_orders_2(X0) | ~v3_orders_2(X0) | v2_struct_0(X0)))),
% 3.14/0.99    inference(ennf_transformation,[],[f14])).
% 3.14/0.99  
% 3.14/0.99  fof(f26,plain,(
% 3.14/0.99    ! [X0] : (! [X1] : (! [X2] : (r2_hidden(k1_funct_1(X1,u1_struct_0(X0)),X2) | ~m2_orders_2(X2,X0,X1)) | ~m1_orders_1(X1,k1_orders_1(u1_struct_0(X0)))) | ~l1_orders_2(X0) | ~v5_orders_2(X0) | ~v4_orders_2(X0) | ~v3_orders_2(X0) | v2_struct_0(X0))),
% 3.14/0.99    inference(flattening,[],[f25])).
% 3.14/0.99  
% 3.14/0.99  fof(f64,plain,(
% 3.14/0.99    ( ! [X2,X0,X1] : (r2_hidden(k1_funct_1(X1,u1_struct_0(X0)),X2) | ~m2_orders_2(X2,X0,X1) | ~m1_orders_1(X1,k1_orders_1(u1_struct_0(X0))) | ~l1_orders_2(X0) | ~v5_orders_2(X0) | ~v4_orders_2(X0) | ~v3_orders_2(X0) | v2_struct_0(X0)) )),
% 3.14/0.99    inference(cnf_transformation,[],[f26])).
% 3.14/0.99  
% 3.14/0.99  fof(f6,axiom,(
% 3.14/0.99    ! [X0,X1] : (k1_xboole_0 = k2_zfmisc_1(X0,X1) <=> (k1_xboole_0 = X1 | k1_xboole_0 = X0))),
% 3.14/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.14/0.99  
% 3.14/0.99  fof(f33,plain,(
% 3.14/0.99    ! [X0,X1] : ((k1_xboole_0 = k2_zfmisc_1(X0,X1) | (k1_xboole_0 != X1 & k1_xboole_0 != X0)) & ((k1_xboole_0 = X1 | k1_xboole_0 = X0) | k1_xboole_0 != k2_zfmisc_1(X0,X1)))),
% 3.14/0.99    inference(nnf_transformation,[],[f6])).
% 3.14/0.99  
% 3.14/0.99  fof(f34,plain,(
% 3.14/0.99    ! [X0,X1] : ((k1_xboole_0 = k2_zfmisc_1(X0,X1) | (k1_xboole_0 != X1 & k1_xboole_0 != X0)) & (k1_xboole_0 = X1 | k1_xboole_0 = X0 | k1_xboole_0 != k2_zfmisc_1(X0,X1)))),
% 3.14/0.99    inference(flattening,[],[f33])).
% 3.14/0.99  
% 3.14/0.99  fof(f52,plain,(
% 3.14/0.99    ( ! [X0,X1] : (k1_xboole_0 = k2_zfmisc_1(X0,X1) | k1_xboole_0 != X1) )),
% 3.14/0.99    inference(cnf_transformation,[],[f34])).
% 3.14/0.99  
% 3.14/0.99  fof(f77,plain,(
% 3.14/0.99    ( ! [X0] : (k1_xboole_0 = k2_zfmisc_1(X0,k1_xboole_0)) )),
% 3.14/0.99    inference(equality_resolution,[],[f52])).
% 3.14/0.99  
% 3.14/0.99  fof(f7,axiom,(
% 3.14/0.99    ! [X0,X1] : ~r2_hidden(X0,k2_zfmisc_1(X0,X1))),
% 3.14/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.14/0.99  
% 3.14/0.99  fof(f53,plain,(
% 3.14/0.99    ( ! [X0,X1] : (~r2_hidden(X0,k2_zfmisc_1(X0,X1))) )),
% 3.14/0.99    inference(cnf_transformation,[],[f7])).
% 3.14/0.99  
% 3.14/0.99  fof(f1,axiom,(
% 3.14/0.99    ! [X0] : (v1_xboole_0(X0) <=> ! [X1] : ~r2_hidden(X1,X0))),
% 3.14/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.14/0.99  
% 3.14/0.99  fof(f17,plain,(
% 3.14/0.99    ! [X0] : (! [X1] : ~r2_hidden(X1,X0) => v1_xboole_0(X0))),
% 3.14/0.99    inference(unused_predicate_definition_removal,[],[f1])).
% 3.14/0.99  
% 3.14/0.99  fof(f18,plain,(
% 3.14/0.99    ! [X0] : (v1_xboole_0(X0) | ? [X1] : r2_hidden(X1,X0))),
% 3.14/0.99    inference(ennf_transformation,[],[f17])).
% 3.14/0.99  
% 3.14/0.99  fof(f29,plain,(
% 3.14/0.99    ! [X0] : (? [X1] : r2_hidden(X1,X0) => r2_hidden(sK0(X0),X0))),
% 3.14/0.99    introduced(choice_axiom,[])).
% 3.14/0.99  
% 3.14/0.99  fof(f30,plain,(
% 3.14/0.99    ! [X0] : (v1_xboole_0(X0) | r2_hidden(sK0(X0),X0))),
% 3.14/0.99    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f18,f29])).
% 3.14/0.99  
% 3.14/0.99  fof(f43,plain,(
% 3.14/0.99    ( ! [X0] : (v1_xboole_0(X0) | r2_hidden(sK0(X0),X0)) )),
% 3.14/0.99    inference(cnf_transformation,[],[f30])).
% 3.14/0.99  
% 3.14/0.99  fof(f10,axiom,(
% 3.14/0.99    ! [X0,X1] : (r2_hidden(X0,X1) => m1_subset_1(k1_tarski(X0),k1_zfmisc_1(X1)))),
% 3.14/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.14/0.99  
% 3.14/0.99  fof(f20,plain,(
% 3.14/0.99    ! [X0,X1] : (m1_subset_1(k1_tarski(X0),k1_zfmisc_1(X1)) | ~r2_hidden(X0,X1))),
% 3.14/0.99    inference(ennf_transformation,[],[f10])).
% 3.14/0.99  
% 3.14/0.99  fof(f56,plain,(
% 3.14/0.99    ( ! [X0,X1] : (m1_subset_1(k1_tarski(X0),k1_zfmisc_1(X1)) | ~r2_hidden(X0,X1)) )),
% 3.14/0.99    inference(cnf_transformation,[],[f20])).
% 3.14/0.99  
% 3.14/0.99  fof(f4,axiom,(
% 3.14/0.99    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0)),
% 3.14/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.14/0.99  
% 3.14/0.99  fof(f48,plain,(
% 3.14/0.99    ( ! [X0] : (k2_tarski(X0,X0) = k1_tarski(X0)) )),
% 3.14/0.99    inference(cnf_transformation,[],[f4])).
% 3.14/0.99  
% 3.14/0.99  fof(f5,axiom,(
% 3.14/0.99    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1)),
% 3.14/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.14/0.99  
% 3.14/0.99  fof(f49,plain,(
% 3.14/0.99    ( ! [X0,X1] : (k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1)) )),
% 3.14/0.99    inference(cnf_transformation,[],[f5])).
% 3.14/0.99  
% 3.14/0.99  fof(f72,plain,(
% 3.14/0.99    ( ! [X0] : (k1_tarski(X0) = k1_enumset1(X0,X0,X0)) )),
% 3.14/0.99    inference(definition_unfolding,[],[f48,f49])).
% 3.14/0.99  
% 3.14/0.99  fof(f74,plain,(
% 3.14/0.99    ( ! [X0,X1] : (m1_subset_1(k1_enumset1(X0,X0,X0),k1_zfmisc_1(X1)) | ~r2_hidden(X0,X1)) )),
% 3.14/0.99    inference(definition_unfolding,[],[f56,f72])).
% 3.14/0.99  
% 3.14/0.99  fof(f11,axiom,(
% 3.14/0.99    ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) <=> r1_tarski(X0,X1))),
% 3.14/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.14/0.99  
% 3.14/0.99  fof(f35,plain,(
% 3.14/0.99    ! [X0,X1] : ((m1_subset_1(X0,k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1)) & (r1_tarski(X0,X1) | ~m1_subset_1(X0,k1_zfmisc_1(X1))))),
% 3.14/0.99    inference(nnf_transformation,[],[f11])).
% 3.14/0.99  
% 3.14/0.99  fof(f57,plain,(
% 3.14/0.99    ( ! [X0,X1] : (r1_tarski(X0,X1) | ~m1_subset_1(X0,k1_zfmisc_1(X1))) )),
% 3.14/0.99    inference(cnf_transformation,[],[f35])).
% 3.14/0.99  
% 3.14/0.99  fof(f71,plain,(
% 3.14/0.99    k1_xboole_0 = k3_tarski(k4_orders_2(sK2,sK3))),
% 3.14/0.99    inference(cnf_transformation,[],[f42])).
% 3.14/0.99  
% 3.14/0.99  fof(f9,axiom,(
% 3.14/0.99    ! [X0,X1] : (r1_tarski(X0,X1) => r1_tarski(k3_tarski(X0),k3_tarski(X1)))),
% 3.14/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.14/0.99  
% 3.14/0.99  fof(f19,plain,(
% 3.14/0.99    ! [X0,X1] : (r1_tarski(k3_tarski(X0),k3_tarski(X1)) | ~r1_tarski(X0,X1))),
% 3.14/0.99    inference(ennf_transformation,[],[f9])).
% 3.14/0.99  
% 3.14/0.99  fof(f55,plain,(
% 3.14/0.99    ( ! [X0,X1] : (r1_tarski(k3_tarski(X0),k3_tarski(X1)) | ~r1_tarski(X0,X1)) )),
% 3.14/0.99    inference(cnf_transformation,[],[f19])).
% 3.14/0.99  
% 3.14/0.99  fof(f8,axiom,(
% 3.14/0.99    ! [X0] : k3_tarski(k1_tarski(X0)) = X0),
% 3.14/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.14/0.99  
% 3.14/0.99  fof(f54,plain,(
% 3.14/0.99    ( ! [X0] : (k3_tarski(k1_tarski(X0)) = X0) )),
% 3.14/0.99    inference(cnf_transformation,[],[f8])).
% 3.14/0.99  
% 3.14/0.99  fof(f73,plain,(
% 3.14/0.99    ( ! [X0] : (k3_tarski(k1_enumset1(X0,X0,X0)) = X0) )),
% 3.14/0.99    inference(definition_unfolding,[],[f54,f72])).
% 3.14/0.99  
% 3.14/0.99  fof(f65,plain,(
% 3.14/0.99    ~v2_struct_0(sK2)),
% 3.14/0.99    inference(cnf_transformation,[],[f42])).
% 3.14/0.99  
% 3.14/0.99  fof(f66,plain,(
% 3.14/0.99    v3_orders_2(sK2)),
% 3.14/0.99    inference(cnf_transformation,[],[f42])).
% 3.14/0.99  
% 3.14/0.99  fof(f67,plain,(
% 3.14/0.99    v4_orders_2(sK2)),
% 3.14/0.99    inference(cnf_transformation,[],[f42])).
% 3.14/0.99  
% 3.14/0.99  fof(f68,plain,(
% 3.14/0.99    v5_orders_2(sK2)),
% 3.14/0.99    inference(cnf_transformation,[],[f42])).
% 3.14/0.99  
% 3.14/0.99  fof(f69,plain,(
% 3.14/0.99    l1_orders_2(sK2)),
% 3.14/0.99    inference(cnf_transformation,[],[f42])).
% 3.14/0.99  
% 3.14/0.99  fof(f13,axiom,(
% 3.14/0.99    ! [X0,X1] : ((m1_orders_1(X1,k1_orders_1(u1_struct_0(X0))) & l1_orders_2(X0) & v5_orders_2(X0) & v4_orders_2(X0) & v3_orders_2(X0) & ~v2_struct_0(X0)) => ~v1_xboole_0(k4_orders_2(X0,X1)))),
% 3.14/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.14/0.99  
% 3.14/0.99  fof(f23,plain,(
% 3.14/0.99    ! [X0,X1] : (~v1_xboole_0(k4_orders_2(X0,X1)) | (~m1_orders_1(X1,k1_orders_1(u1_struct_0(X0))) | ~l1_orders_2(X0) | ~v5_orders_2(X0) | ~v4_orders_2(X0) | ~v3_orders_2(X0) | v2_struct_0(X0)))),
% 3.14/0.99    inference(ennf_transformation,[],[f13])).
% 3.14/0.99  
% 3.14/0.99  fof(f24,plain,(
% 3.14/0.99    ! [X0,X1] : (~v1_xboole_0(k4_orders_2(X0,X1)) | ~m1_orders_1(X1,k1_orders_1(u1_struct_0(X0))) | ~l1_orders_2(X0) | ~v5_orders_2(X0) | ~v4_orders_2(X0) | ~v3_orders_2(X0) | v2_struct_0(X0))),
% 3.14/0.99    inference(flattening,[],[f23])).
% 3.14/0.99  
% 3.14/0.99  fof(f63,plain,(
% 3.14/0.99    ( ! [X0,X1] : (~v1_xboole_0(k4_orders_2(X0,X1)) | ~m1_orders_1(X1,k1_orders_1(u1_struct_0(X0))) | ~l1_orders_2(X0) | ~v5_orders_2(X0) | ~v4_orders_2(X0) | ~v3_orders_2(X0) | v2_struct_0(X0)) )),
% 3.14/0.99    inference(cnf_transformation,[],[f24])).
% 3.14/0.99  
% 3.14/0.99  fof(f2,axiom,(
% 3.14/0.99    ! [X0,X1] : (X0 = X1 <=> (r1_tarski(X1,X0) & r1_tarski(X0,X1)))),
% 3.14/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.14/0.99  
% 3.14/0.99  fof(f31,plain,(
% 3.14/0.99    ! [X0,X1] : ((X0 = X1 | (~r1_tarski(X1,X0) | ~r1_tarski(X0,X1))) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 3.14/0.99    inference(nnf_transformation,[],[f2])).
% 3.14/0.99  
% 3.14/0.99  fof(f32,plain,(
% 3.14/0.99    ! [X0,X1] : ((X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 3.14/0.99    inference(flattening,[],[f31])).
% 3.14/0.99  
% 3.14/0.99  fof(f46,plain,(
% 3.14/0.99    ( ! [X0,X1] : (X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) )),
% 3.14/0.99    inference(cnf_transformation,[],[f32])).
% 3.14/0.99  
% 3.14/0.99  fof(f3,axiom,(
% 3.14/0.99    ! [X0] : r1_tarski(k1_xboole_0,X0)),
% 3.14/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.14/0.99  
% 3.14/0.99  fof(f47,plain,(
% 3.14/0.99    ( ! [X0] : (r1_tarski(k1_xboole_0,X0)) )),
% 3.14/0.99    inference(cnf_transformation,[],[f3])).
% 3.14/0.99  
% 3.14/0.99  fof(f12,axiom,(
% 3.14/0.99    ! [X0] : ((l1_orders_2(X0) & v5_orders_2(X0) & v4_orders_2(X0) & v3_orders_2(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_orders_1(X1,k1_orders_1(u1_struct_0(X0))) => ! [X2] : (k4_orders_2(X0,X1) = X2 <=> ! [X3] : (r2_hidden(X3,X2) <=> m2_orders_2(X3,X0,X1)))))),
% 3.14/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.14/0.99  
% 3.14/0.99  fof(f21,plain,(
% 3.14/0.99    ! [X0] : (! [X1] : (! [X2] : (k4_orders_2(X0,X1) = X2 <=> ! [X3] : (r2_hidden(X3,X2) <=> m2_orders_2(X3,X0,X1))) | ~m1_orders_1(X1,k1_orders_1(u1_struct_0(X0)))) | (~l1_orders_2(X0) | ~v5_orders_2(X0) | ~v4_orders_2(X0) | ~v3_orders_2(X0) | v2_struct_0(X0)))),
% 3.14/0.99    inference(ennf_transformation,[],[f12])).
% 3.14/0.99  
% 3.14/0.99  fof(f22,plain,(
% 3.14/0.99    ! [X0] : (! [X1] : (! [X2] : (k4_orders_2(X0,X1) = X2 <=> ! [X3] : (r2_hidden(X3,X2) <=> m2_orders_2(X3,X0,X1))) | ~m1_orders_1(X1,k1_orders_1(u1_struct_0(X0)))) | ~l1_orders_2(X0) | ~v5_orders_2(X0) | ~v4_orders_2(X0) | ~v3_orders_2(X0) | v2_struct_0(X0))),
% 3.14/0.99    inference(flattening,[],[f21])).
% 3.14/0.99  
% 3.14/0.99  fof(f36,plain,(
% 3.14/0.99    ! [X0] : (! [X1] : (! [X2] : ((k4_orders_2(X0,X1) = X2 | ? [X3] : ((~m2_orders_2(X3,X0,X1) | ~r2_hidden(X3,X2)) & (m2_orders_2(X3,X0,X1) | r2_hidden(X3,X2)))) & (! [X3] : ((r2_hidden(X3,X2) | ~m2_orders_2(X3,X0,X1)) & (m2_orders_2(X3,X0,X1) | ~r2_hidden(X3,X2))) | k4_orders_2(X0,X1) != X2)) | ~m1_orders_1(X1,k1_orders_1(u1_struct_0(X0)))) | ~l1_orders_2(X0) | ~v5_orders_2(X0) | ~v4_orders_2(X0) | ~v3_orders_2(X0) | v2_struct_0(X0))),
% 3.14/0.99    inference(nnf_transformation,[],[f22])).
% 3.14/0.99  
% 3.14/0.99  fof(f37,plain,(
% 3.14/0.99    ! [X0] : (! [X1] : (! [X2] : ((k4_orders_2(X0,X1) = X2 | ? [X3] : ((~m2_orders_2(X3,X0,X1) | ~r2_hidden(X3,X2)) & (m2_orders_2(X3,X0,X1) | r2_hidden(X3,X2)))) & (! [X4] : ((r2_hidden(X4,X2) | ~m2_orders_2(X4,X0,X1)) & (m2_orders_2(X4,X0,X1) | ~r2_hidden(X4,X2))) | k4_orders_2(X0,X1) != X2)) | ~m1_orders_1(X1,k1_orders_1(u1_struct_0(X0)))) | ~l1_orders_2(X0) | ~v5_orders_2(X0) | ~v4_orders_2(X0) | ~v3_orders_2(X0) | v2_struct_0(X0))),
% 3.14/0.99    inference(rectify,[],[f36])).
% 3.14/0.99  
% 3.14/0.99  fof(f38,plain,(
% 3.14/0.99    ! [X2,X1,X0] : (? [X3] : ((~m2_orders_2(X3,X0,X1) | ~r2_hidden(X3,X2)) & (m2_orders_2(X3,X0,X1) | r2_hidden(X3,X2))) => ((~m2_orders_2(sK1(X0,X1,X2),X0,X1) | ~r2_hidden(sK1(X0,X1,X2),X2)) & (m2_orders_2(sK1(X0,X1,X2),X0,X1) | r2_hidden(sK1(X0,X1,X2),X2))))),
% 3.14/0.99    introduced(choice_axiom,[])).
% 3.14/0.99  
% 3.14/0.99  fof(f39,plain,(
% 3.14/0.99    ! [X0] : (! [X1] : (! [X2] : ((k4_orders_2(X0,X1) = X2 | ((~m2_orders_2(sK1(X0,X1,X2),X0,X1) | ~r2_hidden(sK1(X0,X1,X2),X2)) & (m2_orders_2(sK1(X0,X1,X2),X0,X1) | r2_hidden(sK1(X0,X1,X2),X2)))) & (! [X4] : ((r2_hidden(X4,X2) | ~m2_orders_2(X4,X0,X1)) & (m2_orders_2(X4,X0,X1) | ~r2_hidden(X4,X2))) | k4_orders_2(X0,X1) != X2)) | ~m1_orders_1(X1,k1_orders_1(u1_struct_0(X0)))) | ~l1_orders_2(X0) | ~v5_orders_2(X0) | ~v4_orders_2(X0) | ~v3_orders_2(X0) | v2_struct_0(X0))),
% 3.14/0.99    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1])],[f37,f38])).
% 3.14/0.99  
% 3.14/0.99  fof(f59,plain,(
% 3.14/0.99    ( ! [X4,X2,X0,X1] : (m2_orders_2(X4,X0,X1) | ~r2_hidden(X4,X2) | k4_orders_2(X0,X1) != X2 | ~m1_orders_1(X1,k1_orders_1(u1_struct_0(X0))) | ~l1_orders_2(X0) | ~v5_orders_2(X0) | ~v4_orders_2(X0) | ~v3_orders_2(X0) | v2_struct_0(X0)) )),
% 3.14/0.99    inference(cnf_transformation,[],[f39])).
% 3.14/0.99  
% 3.14/0.99  fof(f80,plain,(
% 3.14/0.99    ( ! [X4,X0,X1] : (m2_orders_2(X4,X0,X1) | ~r2_hidden(X4,k4_orders_2(X0,X1)) | ~m1_orders_1(X1,k1_orders_1(u1_struct_0(X0))) | ~l1_orders_2(X0) | ~v5_orders_2(X0) | ~v4_orders_2(X0) | ~v3_orders_2(X0) | v2_struct_0(X0)) )),
% 3.14/0.99    inference(equality_resolution,[],[f59])).
% 3.14/0.99  
% 3.14/0.99  cnf(c_21,negated_conjecture,
% 3.14/0.99      ( m1_orders_1(sK3,k1_orders_1(u1_struct_0(sK2))) ),
% 3.14/0.99      inference(cnf_transformation,[],[f70]) ).
% 3.14/0.99  
% 3.14/0.99  cnf(c_1067,plain,
% 3.14/0.99      ( m1_orders_1(sK3,k1_orders_1(u1_struct_0(sK2))) = iProver_top ),
% 3.14/0.99      inference(predicate_to_equality,[status(thm)],[c_21]) ).
% 3.14/0.99  
% 3.14/0.99  cnf(c_19,plain,
% 3.14/0.99      ( ~ m2_orders_2(X0,X1,X2)
% 3.14/0.99      | ~ m1_orders_1(X2,k1_orders_1(u1_struct_0(X1)))
% 3.14/0.99      | r2_hidden(k1_funct_1(X2,u1_struct_0(X1)),X0)
% 3.14/0.99      | v2_struct_0(X1)
% 3.14/0.99      | ~ v3_orders_2(X1)
% 3.14/0.99      | ~ v4_orders_2(X1)
% 3.14/0.99      | ~ v5_orders_2(X1)
% 3.14/0.99      | ~ l1_orders_2(X1) ),
% 3.14/0.99      inference(cnf_transformation,[],[f64]) ).
% 3.14/0.99  
% 3.14/0.99  cnf(c_1068,plain,
% 3.14/0.99      ( m2_orders_2(X0,X1,X2) != iProver_top
% 3.14/0.99      | m1_orders_1(X2,k1_orders_1(u1_struct_0(X1))) != iProver_top
% 3.14/0.99      | r2_hidden(k1_funct_1(X2,u1_struct_0(X1)),X0) = iProver_top
% 3.14/0.99      | v2_struct_0(X1) = iProver_top
% 3.14/0.99      | v3_orders_2(X1) != iProver_top
% 3.14/0.99      | v4_orders_2(X1) != iProver_top
% 3.14/0.99      | v5_orders_2(X1) != iProver_top
% 3.14/0.99      | l1_orders_2(X1) != iProver_top ),
% 3.14/0.99      inference(predicate_to_equality,[status(thm)],[c_19]) ).
% 3.14/0.99  
% 3.14/0.99  cnf(c_5,plain,
% 3.14/0.99      ( k2_zfmisc_1(X0,k1_xboole_0) = k1_xboole_0 ),
% 3.14/0.99      inference(cnf_transformation,[],[f77]) ).
% 3.14/0.99  
% 3.14/0.99  cnf(c_8,plain,
% 3.14/0.99      ( ~ r2_hidden(X0,k2_zfmisc_1(X0,X1)) ),
% 3.14/0.99      inference(cnf_transformation,[],[f53]) ).
% 3.14/0.99  
% 3.14/0.99  cnf(c_1078,plain,
% 3.14/0.99      ( r2_hidden(X0,k2_zfmisc_1(X0,X1)) != iProver_top ),
% 3.14/0.99      inference(predicate_to_equality,[status(thm)],[c_8]) ).
% 3.14/0.99  
% 3.14/0.99  cnf(c_1773,plain,
% 3.14/0.99      ( r2_hidden(X0,k1_xboole_0) != iProver_top ),
% 3.14/0.99      inference(superposition,[status(thm)],[c_5,c_1078]) ).
% 3.14/0.99  
% 3.14/0.99  cnf(c_1801,plain,
% 3.14/0.99      ( m2_orders_2(k1_xboole_0,X0,X1) != iProver_top
% 3.14/0.99      | m1_orders_1(X1,k1_orders_1(u1_struct_0(X0))) != iProver_top
% 3.14/0.99      | v2_struct_0(X0) = iProver_top
% 3.14/0.99      | v3_orders_2(X0) != iProver_top
% 3.14/0.99      | v4_orders_2(X0) != iProver_top
% 3.14/0.99      | v5_orders_2(X0) != iProver_top
% 3.14/0.99      | l1_orders_2(X0) != iProver_top ),
% 3.14/0.99      inference(superposition,[status(thm)],[c_1068,c_1773]) ).
% 3.14/0.99  
% 3.14/0.99  cnf(c_6210,plain,
% 3.14/0.99      ( m2_orders_2(k1_xboole_0,sK2,sK3) != iProver_top
% 3.14/0.99      | v2_struct_0(sK2) = iProver_top
% 3.14/0.99      | v3_orders_2(sK2) != iProver_top
% 3.14/0.99      | v4_orders_2(sK2) != iProver_top
% 3.14/0.99      | v5_orders_2(sK2) != iProver_top
% 3.14/0.99      | l1_orders_2(sK2) != iProver_top ),
% 3.14/0.99      inference(superposition,[status(thm)],[c_1067,c_1801]) ).
% 3.14/0.99  
% 3.14/0.99  cnf(c_0,plain,
% 3.14/0.99      ( r2_hidden(sK0(X0),X0) | v1_xboole_0(X0) ),
% 3.14/0.99      inference(cnf_transformation,[],[f43]) ).
% 3.14/0.99  
% 3.14/0.99  cnf(c_1082,plain,
% 3.14/0.99      ( r2_hidden(sK0(X0),X0) = iProver_top
% 3.14/0.99      | v1_xboole_0(X0) = iProver_top ),
% 3.14/0.99      inference(predicate_to_equality,[status(thm)],[c_0]) ).
% 3.14/0.99  
% 3.14/0.99  cnf(c_11,plain,
% 3.14/0.99      ( m1_subset_1(k1_enumset1(X0,X0,X0),k1_zfmisc_1(X1))
% 3.14/0.99      | ~ r2_hidden(X0,X1) ),
% 3.14/0.99      inference(cnf_transformation,[],[f74]) ).
% 3.14/0.99  
% 3.14/0.99  cnf(c_1076,plain,
% 3.14/0.99      ( m1_subset_1(k1_enumset1(X0,X0,X0),k1_zfmisc_1(X1)) = iProver_top
% 3.14/0.99      | r2_hidden(X0,X1) != iProver_top ),
% 3.14/0.99      inference(predicate_to_equality,[status(thm)],[c_11]) ).
% 3.14/0.99  
% 3.14/0.99  cnf(c_13,plain,
% 3.14/0.99      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1)) | r1_tarski(X0,X1) ),
% 3.14/0.99      inference(cnf_transformation,[],[f57]) ).
% 3.14/0.99  
% 3.14/0.99  cnf(c_1074,plain,
% 3.14/0.99      ( m1_subset_1(X0,k1_zfmisc_1(X1)) != iProver_top
% 3.14/0.99      | r1_tarski(X0,X1) = iProver_top ),
% 3.14/0.99      inference(predicate_to_equality,[status(thm)],[c_13]) ).
% 3.14/0.99  
% 3.14/0.99  cnf(c_2262,plain,
% 3.14/0.99      ( r1_tarski(k1_enumset1(X0,X0,X0),X1) = iProver_top
% 3.14/0.99      | r2_hidden(X0,X1) != iProver_top ),
% 3.14/0.99      inference(superposition,[status(thm)],[c_1076,c_1074]) ).
% 3.14/0.99  
% 3.14/0.99  cnf(c_20,negated_conjecture,
% 3.14/0.99      ( k1_xboole_0 = k3_tarski(k4_orders_2(sK2,sK3)) ),
% 3.14/0.99      inference(cnf_transformation,[],[f71]) ).
% 3.14/0.99  
% 3.14/0.99  cnf(c_10,plain,
% 3.14/0.99      ( ~ r1_tarski(X0,X1) | r1_tarski(k3_tarski(X0),k3_tarski(X1)) ),
% 3.14/0.99      inference(cnf_transformation,[],[f55]) ).
% 3.14/0.99  
% 3.14/0.99  cnf(c_1077,plain,
% 3.14/0.99      ( r1_tarski(X0,X1) != iProver_top
% 3.14/0.99      | r1_tarski(k3_tarski(X0),k3_tarski(X1)) = iProver_top ),
% 3.14/0.99      inference(predicate_to_equality,[status(thm)],[c_10]) ).
% 3.14/0.99  
% 3.14/0.99  cnf(c_2023,plain,
% 3.14/0.99      ( r1_tarski(X0,k4_orders_2(sK2,sK3)) != iProver_top
% 3.14/0.99      | r1_tarski(k3_tarski(X0),k1_xboole_0) = iProver_top ),
% 3.14/0.99      inference(superposition,[status(thm)],[c_20,c_1077]) ).
% 3.14/0.99  
% 3.14/0.99  cnf(c_2563,plain,
% 3.14/0.99      ( r1_tarski(k3_tarski(k1_enumset1(X0,X0,X0)),k1_xboole_0) = iProver_top
% 3.14/0.99      | r2_hidden(X0,k4_orders_2(sK2,sK3)) != iProver_top ),
% 3.14/0.99      inference(superposition,[status(thm)],[c_2262,c_2023]) ).
% 3.14/0.99  
% 3.14/0.99  cnf(c_9,plain,
% 3.14/0.99      ( k3_tarski(k1_enumset1(X0,X0,X0)) = X0 ),
% 3.14/0.99      inference(cnf_transformation,[],[f73]) ).
% 3.14/0.99  
% 3.14/0.99  cnf(c_2566,plain,
% 3.14/0.99      ( r1_tarski(X0,k1_xboole_0) = iProver_top
% 3.14/0.99      | r2_hidden(X0,k4_orders_2(sK2,sK3)) != iProver_top ),
% 3.14/0.99      inference(light_normalisation,[status(thm)],[c_2563,c_9]) ).
% 3.14/0.99  
% 3.14/0.99  cnf(c_2650,plain,
% 3.14/0.99      ( r1_tarski(sK0(k4_orders_2(sK2,sK3)),k1_xboole_0) = iProver_top
% 3.14/0.99      | v1_xboole_0(k4_orders_2(sK2,sK3)) = iProver_top ),
% 3.14/0.99      inference(superposition,[status(thm)],[c_1082,c_2566]) ).
% 3.14/0.99  
% 3.14/0.99  cnf(c_26,negated_conjecture,
% 3.14/0.99      ( ~ v2_struct_0(sK2) ),
% 3.14/0.99      inference(cnf_transformation,[],[f65]) ).
% 3.14/0.99  
% 3.14/0.99  cnf(c_27,plain,
% 3.14/0.99      ( v2_struct_0(sK2) != iProver_top ),
% 3.14/0.99      inference(predicate_to_equality,[status(thm)],[c_26]) ).
% 3.14/0.99  
% 3.14/0.99  cnf(c_25,negated_conjecture,
% 3.14/0.99      ( v3_orders_2(sK2) ),
% 3.14/0.99      inference(cnf_transformation,[],[f66]) ).
% 3.14/0.99  
% 3.14/0.99  cnf(c_28,plain,
% 3.14/0.99      ( v3_orders_2(sK2) = iProver_top ),
% 3.14/0.99      inference(predicate_to_equality,[status(thm)],[c_25]) ).
% 3.14/0.99  
% 3.14/0.99  cnf(c_24,negated_conjecture,
% 3.14/0.99      ( v4_orders_2(sK2) ),
% 3.14/0.99      inference(cnf_transformation,[],[f67]) ).
% 3.14/0.99  
% 3.14/0.99  cnf(c_29,plain,
% 3.14/0.99      ( v4_orders_2(sK2) = iProver_top ),
% 3.14/0.99      inference(predicate_to_equality,[status(thm)],[c_24]) ).
% 3.14/0.99  
% 3.14/0.99  cnf(c_23,negated_conjecture,
% 3.14/0.99      ( v5_orders_2(sK2) ),
% 3.14/0.99      inference(cnf_transformation,[],[f68]) ).
% 3.14/0.99  
% 3.14/0.99  cnf(c_30,plain,
% 3.14/0.99      ( v5_orders_2(sK2) = iProver_top ),
% 3.14/0.99      inference(predicate_to_equality,[status(thm)],[c_23]) ).
% 3.14/0.99  
% 3.14/0.99  cnf(c_22,negated_conjecture,
% 3.14/0.99      ( l1_orders_2(sK2) ),
% 3.14/0.99      inference(cnf_transformation,[],[f69]) ).
% 3.14/0.99  
% 3.14/0.99  cnf(c_31,plain,
% 3.14/0.99      ( l1_orders_2(sK2) = iProver_top ),
% 3.14/0.99      inference(predicate_to_equality,[status(thm)],[c_22]) ).
% 3.14/0.99  
% 3.14/0.99  cnf(c_32,plain,
% 3.14/0.99      ( m1_orders_1(sK3,k1_orders_1(u1_struct_0(sK2))) = iProver_top ),
% 3.14/0.99      inference(predicate_to_equality,[status(thm)],[c_21]) ).
% 3.14/0.99  
% 3.14/0.99  cnf(c_18,plain,
% 3.14/0.99      ( ~ m1_orders_1(X0,k1_orders_1(u1_struct_0(X1)))
% 3.14/0.99      | v2_struct_0(X1)
% 3.14/0.99      | ~ v3_orders_2(X1)
% 3.14/0.99      | ~ v4_orders_2(X1)
% 3.14/0.99      | ~ v5_orders_2(X1)
% 3.14/0.99      | ~ l1_orders_2(X1)
% 3.14/0.99      | ~ v1_xboole_0(k4_orders_2(X1,X0)) ),
% 3.14/0.99      inference(cnf_transformation,[],[f63]) ).
% 3.14/0.99  
% 3.14/0.99  cnf(c_1865,plain,
% 3.14/0.99      ( ~ m1_orders_1(sK3,k1_orders_1(u1_struct_0(sK2)))
% 3.14/0.99      | v2_struct_0(sK2)
% 3.14/0.99      | ~ v3_orders_2(sK2)
% 3.14/0.99      | ~ v4_orders_2(sK2)
% 3.14/0.99      | ~ v5_orders_2(sK2)
% 3.14/0.99      | ~ l1_orders_2(sK2)
% 3.14/0.99      | ~ v1_xboole_0(k4_orders_2(sK2,sK3)) ),
% 3.14/0.99      inference(instantiation,[status(thm)],[c_18]) ).
% 3.14/0.99  
% 3.14/0.99  cnf(c_1866,plain,
% 3.14/0.99      ( m1_orders_1(sK3,k1_orders_1(u1_struct_0(sK2))) != iProver_top
% 3.14/0.99      | v2_struct_0(sK2) = iProver_top
% 3.14/0.99      | v3_orders_2(sK2) != iProver_top
% 3.14/0.99      | v4_orders_2(sK2) != iProver_top
% 3.14/0.99      | v5_orders_2(sK2) != iProver_top
% 3.14/0.99      | l1_orders_2(sK2) != iProver_top
% 3.14/0.99      | v1_xboole_0(k4_orders_2(sK2,sK3)) != iProver_top ),
% 3.14/0.99      inference(predicate_to_equality,[status(thm)],[c_1865]) ).
% 3.14/0.99  
% 3.14/0.99  cnf(c_2677,plain,
% 3.14/0.99      ( r1_tarski(sK0(k4_orders_2(sK2,sK3)),k1_xboole_0) = iProver_top ),
% 3.14/0.99      inference(global_propositional_subsumption,
% 3.14/0.99                [status(thm)],
% 3.14/0.99                [c_2650,c_27,c_28,c_29,c_30,c_31,c_32,c_1866]) ).
% 3.14/0.99  
% 3.14/0.99  cnf(c_1,plain,
% 3.14/0.99      ( ~ r1_tarski(X0,X1) | ~ r1_tarski(X1,X0) | X0 = X1 ),
% 3.14/0.99      inference(cnf_transformation,[],[f46]) ).
% 3.14/0.99  
% 3.14/0.99  cnf(c_1081,plain,
% 3.14/0.99      ( X0 = X1
% 3.14/0.99      | r1_tarski(X0,X1) != iProver_top
% 3.14/0.99      | r1_tarski(X1,X0) != iProver_top ),
% 3.14/0.99      inference(predicate_to_equality,[status(thm)],[c_1]) ).
% 3.14/0.99  
% 3.14/0.99  cnf(c_3123,plain,
% 3.14/0.99      ( sK0(k4_orders_2(sK2,sK3)) = k1_xboole_0
% 3.14/0.99      | r1_tarski(k1_xboole_0,sK0(k4_orders_2(sK2,sK3))) != iProver_top ),
% 3.14/0.99      inference(superposition,[status(thm)],[c_2677,c_1081]) ).
% 3.14/0.99  
% 3.14/0.99  cnf(c_4,plain,
% 3.14/0.99      ( r1_tarski(k1_xboole_0,X0) ),
% 3.14/0.99      inference(cnf_transformation,[],[f47]) ).
% 3.14/0.99  
% 3.14/0.99  cnf(c_1079,plain,
% 3.14/0.99      ( r1_tarski(k1_xboole_0,X0) = iProver_top ),
% 3.14/0.99      inference(predicate_to_equality,[status(thm)],[c_4]) ).
% 3.14/0.99  
% 3.14/0.99  cnf(c_3952,plain,
% 3.14/0.99      ( sK0(k4_orders_2(sK2,sK3)) = k1_xboole_0 ),
% 3.14/0.99      inference(forward_subsumption_resolution,
% 3.14/0.99                [status(thm)],
% 3.14/0.99                [c_3123,c_1079]) ).
% 3.14/0.99  
% 3.14/0.99  cnf(c_17,plain,
% 3.14/0.99      ( m2_orders_2(X0,X1,X2)
% 3.14/0.99      | ~ m1_orders_1(X2,k1_orders_1(u1_struct_0(X1)))
% 3.14/0.99      | ~ r2_hidden(X0,k4_orders_2(X1,X2))
% 3.14/0.99      | v2_struct_0(X1)
% 3.14/0.99      | ~ v3_orders_2(X1)
% 3.14/0.99      | ~ v4_orders_2(X1)
% 3.14/0.99      | ~ v5_orders_2(X1)
% 3.14/0.99      | ~ l1_orders_2(X1) ),
% 3.14/0.99      inference(cnf_transformation,[],[f80]) ).
% 3.14/0.99  
% 3.14/0.99  cnf(c_1070,plain,
% 3.14/0.99      ( m2_orders_2(X0,X1,X2) = iProver_top
% 3.14/0.99      | m1_orders_1(X2,k1_orders_1(u1_struct_0(X1))) != iProver_top
% 3.14/0.99      | r2_hidden(X0,k4_orders_2(X1,X2)) != iProver_top
% 3.14/0.99      | v2_struct_0(X1) = iProver_top
% 3.14/0.99      | v3_orders_2(X1) != iProver_top
% 3.14/0.99      | v4_orders_2(X1) != iProver_top
% 3.14/0.99      | v5_orders_2(X1) != iProver_top
% 3.14/0.99      | l1_orders_2(X1) != iProver_top ),
% 3.14/0.99      inference(predicate_to_equality,[status(thm)],[c_17]) ).
% 3.14/0.99  
% 3.14/0.99  cnf(c_2992,plain,
% 3.14/0.99      ( m2_orders_2(X0,sK2,sK3) = iProver_top
% 3.14/0.99      | r2_hidden(X0,k4_orders_2(sK2,sK3)) != iProver_top
% 3.14/0.99      | v2_struct_0(sK2) = iProver_top
% 3.14/0.99      | v3_orders_2(sK2) != iProver_top
% 3.14/0.99      | v4_orders_2(sK2) != iProver_top
% 3.14/0.99      | v5_orders_2(sK2) != iProver_top
% 3.14/0.99      | l1_orders_2(sK2) != iProver_top ),
% 3.14/0.99      inference(superposition,[status(thm)],[c_1067,c_1070]) ).
% 3.14/0.99  
% 3.14/0.99  cnf(c_3300,plain,
% 3.14/0.99      ( r2_hidden(X0,k4_orders_2(sK2,sK3)) != iProver_top
% 3.14/0.99      | m2_orders_2(X0,sK2,sK3) = iProver_top ),
% 3.14/0.99      inference(global_propositional_subsumption,
% 3.14/0.99                [status(thm)],
% 3.14/0.99                [c_2992,c_27,c_28,c_29,c_30,c_31]) ).
% 3.14/0.99  
% 3.14/0.99  cnf(c_3301,plain,
% 3.14/0.99      ( m2_orders_2(X0,sK2,sK3) = iProver_top
% 3.14/0.99      | r2_hidden(X0,k4_orders_2(sK2,sK3)) != iProver_top ),
% 3.14/0.99      inference(renaming,[status(thm)],[c_3300]) ).
% 3.14/0.99  
% 3.14/0.99  cnf(c_3308,plain,
% 3.14/0.99      ( m2_orders_2(sK0(k4_orders_2(sK2,sK3)),sK2,sK3) = iProver_top
% 3.14/0.99      | v1_xboole_0(k4_orders_2(sK2,sK3)) = iProver_top ),
% 3.14/0.99      inference(superposition,[status(thm)],[c_1082,c_3301]) ).
% 3.14/0.99  
% 3.14/0.99  cnf(c_1521,plain,
% 3.14/0.99      ( r2_hidden(sK0(k4_orders_2(X0,X1)),k4_orders_2(X0,X1))
% 3.14/0.99      | v1_xboole_0(k4_orders_2(X0,X1)) ),
% 3.14/0.99      inference(instantiation,[status(thm)],[c_0]) ).
% 3.14/0.99  
% 3.14/0.99  cnf(c_2081,plain,
% 3.14/0.99      ( r2_hidden(sK0(k4_orders_2(sK2,sK3)),k4_orders_2(sK2,sK3))
% 3.14/0.99      | v1_xboole_0(k4_orders_2(sK2,sK3)) ),
% 3.14/0.99      inference(instantiation,[status(thm)],[c_1521]) ).
% 3.14/0.99  
% 3.14/0.99  cnf(c_2082,plain,
% 3.14/0.99      ( r2_hidden(sK0(k4_orders_2(sK2,sK3)),k4_orders_2(sK2,sK3)) = iProver_top
% 3.14/0.99      | v1_xboole_0(k4_orders_2(sK2,sK3)) = iProver_top ),
% 3.14/0.99      inference(predicate_to_equality,[status(thm)],[c_2081]) ).
% 3.14/0.99  
% 3.14/0.99  cnf(c_1371,plain,
% 3.14/0.99      ( m2_orders_2(X0,sK2,X1)
% 3.14/0.99      | ~ m1_orders_1(X1,k1_orders_1(u1_struct_0(sK2)))
% 3.14/0.99      | ~ r2_hidden(X0,k4_orders_2(sK2,X1))
% 3.14/0.99      | v2_struct_0(sK2)
% 3.14/0.99      | ~ v3_orders_2(sK2)
% 3.14/0.99      | ~ v4_orders_2(sK2)
% 3.14/0.99      | ~ v5_orders_2(sK2)
% 3.14/0.99      | ~ l1_orders_2(sK2) ),
% 3.14/0.99      inference(instantiation,[status(thm)],[c_17]) ).
% 3.14/0.99  
% 3.14/0.99  cnf(c_1511,plain,
% 3.14/0.99      ( m2_orders_2(X0,sK2,sK3)
% 3.14/0.99      | ~ m1_orders_1(sK3,k1_orders_1(u1_struct_0(sK2)))
% 3.14/0.99      | ~ r2_hidden(X0,k4_orders_2(sK2,sK3))
% 3.14/0.99      | v2_struct_0(sK2)
% 3.14/0.99      | ~ v3_orders_2(sK2)
% 3.14/0.99      | ~ v4_orders_2(sK2)
% 3.14/0.99      | ~ v5_orders_2(sK2)
% 3.14/0.99      | ~ l1_orders_2(sK2) ),
% 3.14/0.99      inference(instantiation,[status(thm)],[c_1371]) ).
% 3.14/0.99  
% 3.14/0.99  cnf(c_2384,plain,
% 3.14/0.99      ( m2_orders_2(sK0(k4_orders_2(sK2,sK3)),sK2,sK3)
% 3.14/0.99      | ~ m1_orders_1(sK3,k1_orders_1(u1_struct_0(sK2)))
% 3.14/0.99      | ~ r2_hidden(sK0(k4_orders_2(sK2,sK3)),k4_orders_2(sK2,sK3))
% 3.14/0.99      | v2_struct_0(sK2)
% 3.14/0.99      | ~ v3_orders_2(sK2)
% 3.14/0.99      | ~ v4_orders_2(sK2)
% 3.14/0.99      | ~ v5_orders_2(sK2)
% 3.14/0.99      | ~ l1_orders_2(sK2) ),
% 3.14/0.99      inference(instantiation,[status(thm)],[c_1511]) ).
% 3.14/0.99  
% 3.14/0.99  cnf(c_2385,plain,
% 3.14/0.99      ( m2_orders_2(sK0(k4_orders_2(sK2,sK3)),sK2,sK3) = iProver_top
% 3.14/0.99      | m1_orders_1(sK3,k1_orders_1(u1_struct_0(sK2))) != iProver_top
% 3.14/0.99      | r2_hidden(sK0(k4_orders_2(sK2,sK3)),k4_orders_2(sK2,sK3)) != iProver_top
% 3.14/0.99      | v2_struct_0(sK2) = iProver_top
% 3.14/0.99      | v3_orders_2(sK2) != iProver_top
% 3.14/0.99      | v4_orders_2(sK2) != iProver_top
% 3.14/0.99      | v5_orders_2(sK2) != iProver_top
% 3.14/0.99      | l1_orders_2(sK2) != iProver_top ),
% 3.14/0.99      inference(predicate_to_equality,[status(thm)],[c_2384]) ).
% 3.14/0.99  
% 3.14/0.99  cnf(c_3702,plain,
% 3.14/0.99      ( m2_orders_2(sK0(k4_orders_2(sK2,sK3)),sK2,sK3) = iProver_top ),
% 3.14/0.99      inference(global_propositional_subsumption,
% 3.14/0.99                [status(thm)],
% 3.14/0.99                [c_3308,c_27,c_28,c_29,c_30,c_31,c_32,c_1866,c_2082,
% 3.14/0.99                 c_2385]) ).
% 3.14/0.99  
% 3.14/0.99  cnf(c_3953,plain,
% 3.14/0.99      ( m2_orders_2(k1_xboole_0,sK2,sK3) = iProver_top ),
% 3.14/0.99      inference(demodulation,[status(thm)],[c_3952,c_3702]) ).
% 3.14/0.99  
% 3.14/0.99  cnf(contradiction,plain,
% 3.14/0.99      ( $false ),
% 3.14/0.99      inference(minisat,
% 3.14/0.99                [status(thm)],
% 3.14/0.99                [c_6210,c_3953,c_31,c_30,c_29,c_28,c_27]) ).
% 3.14/0.99  
% 3.14/0.99  
% 3.14/0.99  % SZS output end CNFRefutation for theBenchmark.p
% 3.14/0.99  
% 3.14/0.99  ------                               Statistics
% 3.14/0.99  
% 3.14/0.99  ------ Selected
% 3.14/0.99  
% 3.14/0.99  total_time:                             0.171
% 3.14/0.99  
%------------------------------------------------------------------------------
