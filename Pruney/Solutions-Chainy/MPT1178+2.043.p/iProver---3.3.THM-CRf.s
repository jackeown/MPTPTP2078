%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n006.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:13:05 EST 2020

% Result     : Theorem 1.52s
% Output     : CNFRefutation 1.52s
% Verified   : 
% Statistics : Number of formulae       :  141 ( 623 expanded)
%              Number of clauses        :   56 (  83 expanded)
%              Number of leaves         :   27 ( 199 expanded)
%              Depth                    :   22
%              Number of atoms          :  539 (2193 expanded)
%              Number of equality atoms :  159 ( 643 expanded)
%              Maximal formula depth    :   14 (   5 average)
%              Maximal clause size      :   16 (   4 average)
%              Maximal term depth       :    7 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f17,axiom,(
    ! [X0,X1] :
      ( ( m1_orders_1(X1,k1_orders_1(u1_struct_0(X0)))
        & l1_orders_2(X0)
        & v5_orders_2(X0)
        & v4_orders_2(X0)
        & v3_orders_2(X0)
        & ~ v2_struct_0(X0) )
     => ? [X2] : m2_orders_2(X2,X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f25,plain,(
    ! [X0,X1] :
      ( ? [X2] : m2_orders_2(X2,X0,X1)
      | ~ m1_orders_1(X1,k1_orders_1(u1_struct_0(X0)))
      | ~ l1_orders_2(X0)
      | ~ v5_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f17])).

fof(f26,plain,(
    ! [X0,X1] :
      ( ? [X2] : m2_orders_2(X2,X0,X1)
      | ~ m1_orders_1(X1,k1_orders_1(u1_struct_0(X0)))
      | ~ l1_orders_2(X0)
      | ~ v5_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f25])).

fof(f37,plain,(
    ! [X1,X0] :
      ( ? [X2] : m2_orders_2(X2,X0,X1)
     => m2_orders_2(sK1(X0,X1),X0,X1) ) ),
    introduced(choice_axiom,[])).

fof(f38,plain,(
    ! [X0,X1] :
      ( m2_orders_2(sK1(X0,X1),X0,X1)
      | ~ m1_orders_1(X1,k1_orders_1(u1_struct_0(X0)))
      | ~ l1_orders_2(X0)
      | ~ v5_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1])],[f26,f37])).

fof(f64,plain,(
    ! [X0,X1] :
      ( m2_orders_2(sK1(X0,X1),X0,X1)
      | ~ m1_orders_1(X1,k1_orders_1(u1_struct_0(X0)))
      | ~ l1_orders_2(X0)
      | ~ v5_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f38])).

fof(f16,axiom,(
    ! [X0] : k1_orders_1(X0) = k7_subset_1(k1_zfmisc_1(X0),k9_setfam_1(X0),k1_tarski(k1_xboole_0)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f63,plain,(
    ! [X0] : k1_orders_1(X0) = k7_subset_1(k1_zfmisc_1(X0),k9_setfam_1(X0),k1_tarski(k1_xboole_0)) ),
    inference(cnf_transformation,[],[f16])).

fof(f14,axiom,(
    ! [X0] : k1_zfmisc_1(X0) = k9_setfam_1(X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f58,plain,(
    ! [X0] : k1_zfmisc_1(X0) = k9_setfam_1(X0) ),
    inference(cnf_transformation,[],[f14])).

fof(f4,axiom,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f47,plain,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    inference(cnf_transformation,[],[f4])).

fof(f5,axiom,(
    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f48,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1) ),
    inference(cnf_transformation,[],[f5])).

fof(f6,axiom,(
    ! [X0,X1,X2] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f49,plain,(
    ! [X2,X0,X1] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2) ),
    inference(cnf_transformation,[],[f6])).

fof(f7,axiom,(
    ! [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) = k3_enumset1(X0,X0,X1,X2,X3) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f50,plain,(
    ! [X2,X0,X3,X1] : k2_enumset1(X0,X1,X2,X3) = k3_enumset1(X0,X0,X1,X2,X3) ),
    inference(cnf_transformation,[],[f7])).

fof(f8,axiom,(
    ! [X0,X1,X2,X3,X4] : k3_enumset1(X0,X1,X2,X3,X4) = k4_enumset1(X0,X0,X1,X2,X3,X4) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f51,plain,(
    ! [X4,X2,X0,X3,X1] : k3_enumset1(X0,X1,X2,X3,X4) = k4_enumset1(X0,X0,X1,X2,X3,X4) ),
    inference(cnf_transformation,[],[f8])).

fof(f9,axiom,(
    ! [X0,X1,X2,X3,X4,X5] : k4_enumset1(X0,X1,X2,X3,X4,X5) = k5_enumset1(X0,X0,X1,X2,X3,X4,X5) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f52,plain,(
    ! [X4,X2,X0,X5,X3,X1] : k4_enumset1(X0,X1,X2,X3,X4,X5) = k5_enumset1(X0,X0,X1,X2,X3,X4,X5) ),
    inference(cnf_transformation,[],[f9])).

fof(f10,axiom,(
    ! [X0,X1,X2,X3,X4,X5,X6] : k5_enumset1(X0,X1,X2,X3,X4,X5,X6) = k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f53,plain,(
    ! [X6,X4,X2,X0,X5,X3,X1] : k5_enumset1(X0,X1,X2,X3,X4,X5,X6) = k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6) ),
    inference(cnf_transformation,[],[f10])).

fof(f76,plain,(
    ! [X4,X2,X0,X5,X3,X1] : k4_enumset1(X0,X1,X2,X3,X4,X5) = k6_enumset1(X0,X0,X0,X1,X2,X3,X4,X5) ),
    inference(definition_unfolding,[],[f52,f53])).

fof(f77,plain,(
    ! [X4,X2,X0,X3,X1] : k3_enumset1(X0,X1,X2,X3,X4) = k6_enumset1(X0,X0,X0,X0,X1,X2,X3,X4) ),
    inference(definition_unfolding,[],[f51,f76])).

fof(f78,plain,(
    ! [X2,X0,X3,X1] : k2_enumset1(X0,X1,X2,X3) = k6_enumset1(X0,X0,X0,X0,X0,X1,X2,X3) ),
    inference(definition_unfolding,[],[f50,f77])).

fof(f79,plain,(
    ! [X2,X0,X1] : k1_enumset1(X0,X1,X2) = k6_enumset1(X0,X0,X0,X0,X0,X0,X1,X2) ),
    inference(definition_unfolding,[],[f49,f78])).

fof(f80,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1) ),
    inference(definition_unfolding,[],[f48,f79])).

fof(f83,plain,(
    ! [X0] : k1_tarski(X0) = k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0) ),
    inference(definition_unfolding,[],[f47,f80])).

fof(f1,axiom,(
    k1_xboole_0 = o_0_0_xboole_0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f44,plain,(
    k1_xboole_0 = o_0_0_xboole_0 ),
    inference(cnf_transformation,[],[f1])).

fof(f84,plain,(
    ! [X0] : k1_orders_1(X0) = k7_subset_1(k9_setfam_1(X0),k9_setfam_1(X0),k6_enumset1(o_0_0_xboole_0,o_0_0_xboole_0,o_0_0_xboole_0,o_0_0_xboole_0,o_0_0_xboole_0,o_0_0_xboole_0,o_0_0_xboole_0,o_0_0_xboole_0)) ),
    inference(definition_unfolding,[],[f63,f58,f83,f44])).

fof(f93,plain,(
    ! [X0,X1] :
      ( m2_orders_2(sK1(X0,X1),X0,X1)
      | ~ m1_orders_1(X1,k7_subset_1(k9_setfam_1(u1_struct_0(X0)),k9_setfam_1(u1_struct_0(X0)),k6_enumset1(o_0_0_xboole_0,o_0_0_xboole_0,o_0_0_xboole_0,o_0_0_xboole_0,o_0_0_xboole_0,o_0_0_xboole_0,o_0_0_xboole_0,o_0_0_xboole_0)))
      | ~ l1_orders_2(X0)
      | ~ v5_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(definition_unfolding,[],[f64,f84])).

fof(f20,conjecture,(
    ! [X0] :
      ( ( l1_orders_2(X0)
        & v5_orders_2(X0)
        & v4_orders_2(X0)
        & v3_orders_2(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( m1_orders_1(X1,k1_orders_1(u1_struct_0(X0)))
         => k1_xboole_0 != k3_tarski(k4_orders_2(X0,X1)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f21,negated_conjecture,(
    ~ ! [X0] :
        ( ( l1_orders_2(X0)
          & v5_orders_2(X0)
          & v4_orders_2(X0)
          & v3_orders_2(X0)
          & ~ v2_struct_0(X0) )
       => ! [X1] :
            ( m1_orders_1(X1,k1_orders_1(u1_struct_0(X0)))
           => k1_xboole_0 != k3_tarski(k4_orders_2(X0,X1)) ) ) ),
    inference(negated_conjecture,[],[f20])).

fof(f30,plain,(
    ? [X0] :
      ( ? [X1] :
          ( k1_xboole_0 = k3_tarski(k4_orders_2(X0,X1))
          & m1_orders_1(X1,k1_orders_1(u1_struct_0(X0))) )
      & l1_orders_2(X0)
      & v5_orders_2(X0)
      & v4_orders_2(X0)
      & v3_orders_2(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f21])).

fof(f31,plain,(
    ? [X0] :
      ( ? [X1] :
          ( k1_xboole_0 = k3_tarski(k4_orders_2(X0,X1))
          & m1_orders_1(X1,k1_orders_1(u1_struct_0(X0))) )
      & l1_orders_2(X0)
      & v5_orders_2(X0)
      & v4_orders_2(X0)
      & v3_orders_2(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(flattening,[],[f30])).

fof(f42,plain,(
    ! [X0] :
      ( ? [X1] :
          ( k1_xboole_0 = k3_tarski(k4_orders_2(X0,X1))
          & m1_orders_1(X1,k1_orders_1(u1_struct_0(X0))) )
     => ( k1_xboole_0 = k3_tarski(k4_orders_2(X0,sK4))
        & m1_orders_1(sK4,k1_orders_1(u1_struct_0(X0))) ) ) ),
    introduced(choice_axiom,[])).

fof(f41,plain,
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
          ( k1_xboole_0 = k3_tarski(k4_orders_2(sK3,X1))
          & m1_orders_1(X1,k1_orders_1(u1_struct_0(sK3))) )
      & l1_orders_2(sK3)
      & v5_orders_2(sK3)
      & v4_orders_2(sK3)
      & v3_orders_2(sK3)
      & ~ v2_struct_0(sK3) ) ),
    introduced(choice_axiom,[])).

fof(f43,plain,
    ( k1_xboole_0 = k3_tarski(k4_orders_2(sK3,sK4))
    & m1_orders_1(sK4,k1_orders_1(u1_struct_0(sK3)))
    & l1_orders_2(sK3)
    & v5_orders_2(sK3)
    & v4_orders_2(sK3)
    & v3_orders_2(sK3)
    & ~ v2_struct_0(sK3) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3,sK4])],[f31,f42,f41])).

fof(f74,plain,(
    m1_orders_1(sK4,k1_orders_1(u1_struct_0(sK3))) ),
    inference(cnf_transformation,[],[f43])).

fof(f99,plain,(
    m1_orders_1(sK4,k7_subset_1(k9_setfam_1(u1_struct_0(sK3)),k9_setfam_1(u1_struct_0(sK3)),k6_enumset1(o_0_0_xboole_0,o_0_0_xboole_0,o_0_0_xboole_0,o_0_0_xboole_0,o_0_0_xboole_0,o_0_0_xboole_0,o_0_0_xboole_0,o_0_0_xboole_0))) ),
    inference(definition_unfolding,[],[f74,f84])).

fof(f73,plain,(
    l1_orders_2(sK3) ),
    inference(cnf_transformation,[],[f43])).

fof(f69,plain,(
    ~ v2_struct_0(sK3) ),
    inference(cnf_transformation,[],[f43])).

fof(f70,plain,(
    v3_orders_2(sK3) ),
    inference(cnf_transformation,[],[f43])).

fof(f71,plain,(
    v4_orders_2(sK3) ),
    inference(cnf_transformation,[],[f43])).

fof(f72,plain,(
    v5_orders_2(sK3) ),
    inference(cnf_transformation,[],[f43])).

fof(f15,axiom,(
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f23,plain,(
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
    inference(ennf_transformation,[],[f15])).

fof(f24,plain,(
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
    inference(flattening,[],[f23])).

fof(f33,plain,(
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
    inference(nnf_transformation,[],[f24])).

fof(f34,plain,(
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
    inference(rectify,[],[f33])).

fof(f35,plain,(
    ! [X2,X1,X0] :
      ( ? [X3] :
          ( ( ~ m2_orders_2(X3,X0,X1)
            | ~ r2_hidden(X3,X2) )
          & ( m2_orders_2(X3,X0,X1)
            | r2_hidden(X3,X2) ) )
     => ( ( ~ m2_orders_2(sK0(X0,X1,X2),X0,X1)
          | ~ r2_hidden(sK0(X0,X1,X2),X2) )
        & ( m2_orders_2(sK0(X0,X1,X2),X0,X1)
          | r2_hidden(sK0(X0,X1,X2),X2) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f36,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( k4_orders_2(X0,X1) = X2
                | ( ( ~ m2_orders_2(sK0(X0,X1,X2),X0,X1)
                    | ~ r2_hidden(sK0(X0,X1,X2),X2) )
                  & ( m2_orders_2(sK0(X0,X1,X2),X0,X1)
                    | r2_hidden(sK0(X0,X1,X2),X2) ) ) )
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
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f34,f35])).

fof(f60,plain,(
    ! [X4,X2,X0,X1] :
      ( r2_hidden(X4,X2)
      | ~ m2_orders_2(X4,X0,X1)
      | k4_orders_2(X0,X1) != X2
      | ~ m1_orders_1(X1,k1_orders_1(u1_struct_0(X0)))
      | ~ l1_orders_2(X0)
      | ~ v5_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f36])).

fof(f91,plain,(
    ! [X4,X2,X0,X1] :
      ( r2_hidden(X4,X2)
      | ~ m2_orders_2(X4,X0,X1)
      | k4_orders_2(X0,X1) != X2
      | ~ m1_orders_1(X1,k7_subset_1(k9_setfam_1(u1_struct_0(X0)),k9_setfam_1(u1_struct_0(X0)),k6_enumset1(o_0_0_xboole_0,o_0_0_xboole_0,o_0_0_xboole_0,o_0_0_xboole_0,o_0_0_xboole_0,o_0_0_xboole_0,o_0_0_xboole_0,o_0_0_xboole_0)))
      | ~ l1_orders_2(X0)
      | ~ v5_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(definition_unfolding,[],[f60,f84])).

fof(f100,plain,(
    ! [X4,X0,X1] :
      ( r2_hidden(X4,k4_orders_2(X0,X1))
      | ~ m2_orders_2(X4,X0,X1)
      | ~ m1_orders_1(X1,k7_subset_1(k9_setfam_1(u1_struct_0(X0)),k9_setfam_1(u1_struct_0(X0)),k6_enumset1(o_0_0_xboole_0,o_0_0_xboole_0,o_0_0_xboole_0,o_0_0_xboole_0,o_0_0_xboole_0,o_0_0_xboole_0,o_0_0_xboole_0,o_0_0_xboole_0)))
      | ~ l1_orders_2(X0)
      | ~ v5_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(equality_resolution,[],[f91])).

fof(f75,plain,(
    k1_xboole_0 = k3_tarski(k4_orders_2(sK3,sK4)) ),
    inference(cnf_transformation,[],[f43])).

fof(f98,plain,(
    o_0_0_xboole_0 = k3_tarski(k4_orders_2(sK3,sK4)) ),
    inference(definition_unfolding,[],[f75,f44])).

fof(f19,axiom,(
    ! [X0] :
      ( ~ ( ! [X1] :
              ~ ( r2_hidden(X1,X0)
                & k1_xboole_0 != X1 )
          & k1_xboole_0 != k3_tarski(X0) )
      & ~ ( k1_xboole_0 = k3_tarski(X0)
          & ? [X1] :
              ( r2_hidden(X1,X0)
              & k1_xboole_0 != X1 ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f22,plain,(
    ! [X0] :
      ( ~ ( ! [X1] :
              ~ ( r2_hidden(X1,X0)
                & k1_xboole_0 != X1 )
          & k1_xboole_0 != k3_tarski(X0) )
      & ~ ( k1_xboole_0 = k3_tarski(X0)
          & ? [X2] :
              ( r2_hidden(X2,X0)
              & k1_xboole_0 != X2 ) ) ) ),
    inference(rectify,[],[f19])).

fof(f29,plain,(
    ! [X0] :
      ( ( ? [X1] :
            ( r2_hidden(X1,X0)
            & k1_xboole_0 != X1 )
        | k1_xboole_0 = k3_tarski(X0) )
      & ( k1_xboole_0 != k3_tarski(X0)
        | ! [X2] :
            ( ~ r2_hidden(X2,X0)
            | k1_xboole_0 = X2 ) ) ) ),
    inference(ennf_transformation,[],[f22])).

fof(f39,plain,(
    ! [X0] :
      ( ? [X1] :
          ( r2_hidden(X1,X0)
          & k1_xboole_0 != X1 )
     => ( r2_hidden(sK2(X0),X0)
        & k1_xboole_0 != sK2(X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f40,plain,(
    ! [X0] :
      ( ( ( r2_hidden(sK2(X0),X0)
          & k1_xboole_0 != sK2(X0) )
        | k1_xboole_0 = k3_tarski(X0) )
      & ( k1_xboole_0 != k3_tarski(X0)
        | ! [X2] :
            ( ~ r2_hidden(X2,X0)
            | k1_xboole_0 = X2 ) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2])],[f29,f39])).

fof(f66,plain,(
    ! [X2,X0] :
      ( k1_xboole_0 != k3_tarski(X0)
      | ~ r2_hidden(X2,X0)
      | k1_xboole_0 = X2 ) ),
    inference(cnf_transformation,[],[f40])).

fof(f97,plain,(
    ! [X2,X0] :
      ( o_0_0_xboole_0 != k3_tarski(X0)
      | ~ r2_hidden(X2,X0)
      | o_0_0_xboole_0 = X2 ) ),
    inference(definition_unfolding,[],[f66,f44,f44])).

fof(f3,axiom,(
    ! [X0] : k1_xboole_0 = k4_xboole_0(k1_xboole_0,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f46,plain,(
    ! [X0] : k1_xboole_0 = k4_xboole_0(k1_xboole_0,X0) ),
    inference(cnf_transformation,[],[f3])).

fof(f2,axiom,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f45,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f2])).

fof(f13,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f57,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1)) ),
    inference(cnf_transformation,[],[f13])).

fof(f81,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)) ),
    inference(definition_unfolding,[],[f57,f80])).

fof(f82,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k1_setfam_1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1))) ),
    inference(definition_unfolding,[],[f45,f81])).

fof(f85,plain,(
    ! [X0] : o_0_0_xboole_0 = k5_xboole_0(o_0_0_xboole_0,k1_setfam_1(k6_enumset1(o_0_0_xboole_0,o_0_0_xboole_0,o_0_0_xboole_0,o_0_0_xboole_0,o_0_0_xboole_0,o_0_0_xboole_0,o_0_0_xboole_0,X0))) ),
    inference(definition_unfolding,[],[f46,f44,f82,f44])).

fof(f12,axiom,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,k1_tarski(X1)) = X0
    <=> ~ r2_hidden(X1,X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f32,plain,(
    ! [X0,X1] :
      ( ( k4_xboole_0(X0,k1_tarski(X1)) = X0
        | r2_hidden(X1,X0) )
      & ( ~ r2_hidden(X1,X0)
        | k4_xboole_0(X0,k1_tarski(X1)) != X0 ) ) ),
    inference(nnf_transformation,[],[f12])).

fof(f55,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X1,X0)
      | k4_xboole_0(X0,k1_tarski(X1)) != X0 ) ),
    inference(cnf_transformation,[],[f32])).

fof(f88,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X1,X0)
      | k5_xboole_0(X0,k1_setfam_1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1)))) != X0 ) ),
    inference(definition_unfolding,[],[f55,f82,f83])).

fof(f18,axiom,(
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f27,plain,(
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
    inference(ennf_transformation,[],[f18])).

fof(f28,plain,(
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
    inference(flattening,[],[f27])).

fof(f65,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(k1_funct_1(X1,u1_struct_0(X0)),X2)
      | ~ m2_orders_2(X2,X0,X1)
      | ~ m1_orders_1(X1,k1_orders_1(u1_struct_0(X0)))
      | ~ l1_orders_2(X0)
      | ~ v5_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f94,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(k1_funct_1(X1,u1_struct_0(X0)),X2)
      | ~ m2_orders_2(X2,X0,X1)
      | ~ m1_orders_1(X1,k7_subset_1(k9_setfam_1(u1_struct_0(X0)),k9_setfam_1(u1_struct_0(X0)),k6_enumset1(o_0_0_xboole_0,o_0_0_xboole_0,o_0_0_xboole_0,o_0_0_xboole_0,o_0_0_xboole_0,o_0_0_xboole_0,o_0_0_xboole_0,o_0_0_xboole_0)))
      | ~ l1_orders_2(X0)
      | ~ v5_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(definition_unfolding,[],[f65,f84])).

cnf(c_1446,plain,
    ( ~ m2_orders_2(X0,X1,X2)
    | m2_orders_2(X3,X4,X5)
    | X3 != X0
    | X4 != X1
    | X5 != X2 ),
    theory(equality)).

cnf(c_1869,plain,
    ( m2_orders_2(X0,X1,X2)
    | ~ m2_orders_2(sK1(sK3,sK4),sK3,sK4)
    | X0 != sK1(sK3,sK4)
    | X2 != sK4
    | X1 != sK3 ),
    inference(instantiation,[status(thm)],[c_1446])).

cnf(c_1900,plain,
    ( m2_orders_2(X0,X1,sK4)
    | ~ m2_orders_2(sK1(sK3,sK4),sK3,sK4)
    | X0 != sK1(sK3,sK4)
    | X1 != sK3
    | sK4 != sK4 ),
    inference(instantiation,[status(thm)],[c_1869])).

cnf(c_2514,plain,
    ( m2_orders_2(X0,sK3,sK4)
    | ~ m2_orders_2(sK1(sK3,sK4),sK3,sK4)
    | X0 != sK1(sK3,sK4)
    | sK4 != sK4
    | sK3 != sK3 ),
    inference(instantiation,[status(thm)],[c_1900])).

cnf(c_2517,plain,
    ( ~ m2_orders_2(sK1(sK3,sK4),sK3,sK4)
    | m2_orders_2(o_0_0_xboole_0,sK3,sK4)
    | sK4 != sK4
    | sK3 != sK3
    | o_0_0_xboole_0 != sK1(sK3,sK4) ),
    inference(instantiation,[status(thm)],[c_2514])).

cnf(c_8,plain,
    ( m2_orders_2(sK1(X0,X1),X0,X1)
    | ~ m1_orders_1(X1,k7_subset_1(k9_setfam_1(u1_struct_0(X0)),k9_setfam_1(u1_struct_0(X0)),k6_enumset1(o_0_0_xboole_0,o_0_0_xboole_0,o_0_0_xboole_0,o_0_0_xboole_0,o_0_0_xboole_0,o_0_0_xboole_0,o_0_0_xboole_0,o_0_0_xboole_0)))
    | v2_struct_0(X0)
    | ~ v3_orders_2(X0)
    | ~ v4_orders_2(X0)
    | ~ v5_orders_2(X0)
    | ~ l1_orders_2(X0) ),
    inference(cnf_transformation,[],[f93])).

cnf(c_14,negated_conjecture,
    ( m1_orders_1(sK4,k7_subset_1(k9_setfam_1(u1_struct_0(sK3)),k9_setfam_1(u1_struct_0(sK3)),k6_enumset1(o_0_0_xboole_0,o_0_0_xboole_0,o_0_0_xboole_0,o_0_0_xboole_0,o_0_0_xboole_0,o_0_0_xboole_0,o_0_0_xboole_0,o_0_0_xboole_0))) ),
    inference(cnf_transformation,[],[f99])).

cnf(c_240,plain,
    ( m2_orders_2(sK1(X0,X1),X0,X1)
    | v2_struct_0(X0)
    | ~ v3_orders_2(X0)
    | ~ v4_orders_2(X0)
    | ~ v5_orders_2(X0)
    | ~ l1_orders_2(X0)
    | k7_subset_1(k9_setfam_1(u1_struct_0(X0)),k9_setfam_1(u1_struct_0(X0)),k6_enumset1(o_0_0_xboole_0,o_0_0_xboole_0,o_0_0_xboole_0,o_0_0_xboole_0,o_0_0_xboole_0,o_0_0_xboole_0,o_0_0_xboole_0,o_0_0_xboole_0)) != k7_subset_1(k9_setfam_1(u1_struct_0(sK3)),k9_setfam_1(u1_struct_0(sK3)),k6_enumset1(o_0_0_xboole_0,o_0_0_xboole_0,o_0_0_xboole_0,o_0_0_xboole_0,o_0_0_xboole_0,o_0_0_xboole_0,o_0_0_xboole_0,o_0_0_xboole_0))
    | sK4 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_8,c_14])).

cnf(c_241,plain,
    ( m2_orders_2(sK1(X0,sK4),X0,sK4)
    | v2_struct_0(X0)
    | ~ v3_orders_2(X0)
    | ~ v4_orders_2(X0)
    | ~ v5_orders_2(X0)
    | ~ l1_orders_2(X0)
    | k7_subset_1(k9_setfam_1(u1_struct_0(X0)),k9_setfam_1(u1_struct_0(X0)),k6_enumset1(o_0_0_xboole_0,o_0_0_xboole_0,o_0_0_xboole_0,o_0_0_xboole_0,o_0_0_xboole_0,o_0_0_xboole_0,o_0_0_xboole_0,o_0_0_xboole_0)) != k7_subset_1(k9_setfam_1(u1_struct_0(sK3)),k9_setfam_1(u1_struct_0(sK3)),k6_enumset1(o_0_0_xboole_0,o_0_0_xboole_0,o_0_0_xboole_0,o_0_0_xboole_0,o_0_0_xboole_0,o_0_0_xboole_0,o_0_0_xboole_0,o_0_0_xboole_0)) ),
    inference(unflattening,[status(thm)],[c_240])).

cnf(c_15,negated_conjecture,
    ( l1_orders_2(sK3) ),
    inference(cnf_transformation,[],[f73])).

cnf(c_526,plain,
    ( m2_orders_2(sK1(X0,sK4),X0,sK4)
    | v2_struct_0(X0)
    | ~ v3_orders_2(X0)
    | ~ v4_orders_2(X0)
    | ~ v5_orders_2(X0)
    | k7_subset_1(k9_setfam_1(u1_struct_0(X0)),k9_setfam_1(u1_struct_0(X0)),k6_enumset1(o_0_0_xboole_0,o_0_0_xboole_0,o_0_0_xboole_0,o_0_0_xboole_0,o_0_0_xboole_0,o_0_0_xboole_0,o_0_0_xboole_0,o_0_0_xboole_0)) != k7_subset_1(k9_setfam_1(u1_struct_0(sK3)),k9_setfam_1(u1_struct_0(sK3)),k6_enumset1(o_0_0_xboole_0,o_0_0_xboole_0,o_0_0_xboole_0,o_0_0_xboole_0,o_0_0_xboole_0,o_0_0_xboole_0,o_0_0_xboole_0,o_0_0_xboole_0))
    | sK3 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_241,c_15])).

cnf(c_527,plain,
    ( m2_orders_2(sK1(sK3,sK4),sK3,sK4)
    | v2_struct_0(sK3)
    | ~ v3_orders_2(sK3)
    | ~ v4_orders_2(sK3)
    | ~ v5_orders_2(sK3)
    | k7_subset_1(k9_setfam_1(u1_struct_0(sK3)),k9_setfam_1(u1_struct_0(sK3)),k6_enumset1(o_0_0_xboole_0,o_0_0_xboole_0,o_0_0_xboole_0,o_0_0_xboole_0,o_0_0_xboole_0,o_0_0_xboole_0,o_0_0_xboole_0,o_0_0_xboole_0)) != k7_subset_1(k9_setfam_1(u1_struct_0(sK3)),k9_setfam_1(u1_struct_0(sK3)),k6_enumset1(o_0_0_xboole_0,o_0_0_xboole_0,o_0_0_xboole_0,o_0_0_xboole_0,o_0_0_xboole_0,o_0_0_xboole_0,o_0_0_xboole_0,o_0_0_xboole_0)) ),
    inference(unflattening,[status(thm)],[c_526])).

cnf(c_19,negated_conjecture,
    ( ~ v2_struct_0(sK3) ),
    inference(cnf_transformation,[],[f69])).

cnf(c_18,negated_conjecture,
    ( v3_orders_2(sK3) ),
    inference(cnf_transformation,[],[f70])).

cnf(c_17,negated_conjecture,
    ( v4_orders_2(sK3) ),
    inference(cnf_transformation,[],[f71])).

cnf(c_16,negated_conjecture,
    ( v5_orders_2(sK3) ),
    inference(cnf_transformation,[],[f72])).

cnf(c_529,plain,
    ( m2_orders_2(sK1(sK3,sK4),sK3,sK4)
    | k7_subset_1(k9_setfam_1(u1_struct_0(sK3)),k9_setfam_1(u1_struct_0(sK3)),k6_enumset1(o_0_0_xboole_0,o_0_0_xboole_0,o_0_0_xboole_0,o_0_0_xboole_0,o_0_0_xboole_0,o_0_0_xboole_0,o_0_0_xboole_0,o_0_0_xboole_0)) != k7_subset_1(k9_setfam_1(u1_struct_0(sK3)),k9_setfam_1(u1_struct_0(sK3)),k6_enumset1(o_0_0_xboole_0,o_0_0_xboole_0,o_0_0_xboole_0,o_0_0_xboole_0,o_0_0_xboole_0,o_0_0_xboole_0,o_0_0_xboole_0,o_0_0_xboole_0)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_527,c_19,c_18,c_17,c_16])).

cnf(c_1006,plain,
    ( m2_orders_2(sK1(sK3,sK4),sK3,sK4) ),
    inference(equality_resolution_simp,[status(thm)],[c_529])).

cnf(c_1774,plain,
    ( m2_orders_2(sK1(sK3,sK4),sK3,sK4) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1006])).

cnf(c_6,plain,
    ( ~ m2_orders_2(X0,X1,X2)
    | ~ m1_orders_1(X2,k7_subset_1(k9_setfam_1(u1_struct_0(X1)),k9_setfam_1(u1_struct_0(X1)),k6_enumset1(o_0_0_xboole_0,o_0_0_xboole_0,o_0_0_xboole_0,o_0_0_xboole_0,o_0_0_xboole_0,o_0_0_xboole_0,o_0_0_xboole_0,o_0_0_xboole_0)))
    | r2_hidden(X0,k4_orders_2(X1,X2))
    | v2_struct_0(X1)
    | ~ v3_orders_2(X1)
    | ~ v4_orders_2(X1)
    | ~ v5_orders_2(X1)
    | ~ l1_orders_2(X1) ),
    inference(cnf_transformation,[],[f100])).

cnf(c_393,plain,
    ( ~ m2_orders_2(X0,X1,X2)
    | r2_hidden(X0,k4_orders_2(X1,X2))
    | v2_struct_0(X1)
    | ~ v3_orders_2(X1)
    | ~ v4_orders_2(X1)
    | ~ v5_orders_2(X1)
    | ~ l1_orders_2(X1)
    | k7_subset_1(k9_setfam_1(u1_struct_0(X1)),k9_setfam_1(u1_struct_0(X1)),k6_enumset1(o_0_0_xboole_0,o_0_0_xboole_0,o_0_0_xboole_0,o_0_0_xboole_0,o_0_0_xboole_0,o_0_0_xboole_0,o_0_0_xboole_0,o_0_0_xboole_0)) != k7_subset_1(k9_setfam_1(u1_struct_0(sK3)),k9_setfam_1(u1_struct_0(sK3)),k6_enumset1(o_0_0_xboole_0,o_0_0_xboole_0,o_0_0_xboole_0,o_0_0_xboole_0,o_0_0_xboole_0,o_0_0_xboole_0,o_0_0_xboole_0,o_0_0_xboole_0))
    | sK4 != X2 ),
    inference(resolution_lifted,[status(thm)],[c_6,c_14])).

cnf(c_394,plain,
    ( ~ m2_orders_2(X0,X1,sK4)
    | r2_hidden(X0,k4_orders_2(X1,sK4))
    | v2_struct_0(X1)
    | ~ v3_orders_2(X1)
    | ~ v4_orders_2(X1)
    | ~ v5_orders_2(X1)
    | ~ l1_orders_2(X1)
    | k7_subset_1(k9_setfam_1(u1_struct_0(X1)),k9_setfam_1(u1_struct_0(X1)),k6_enumset1(o_0_0_xboole_0,o_0_0_xboole_0,o_0_0_xboole_0,o_0_0_xboole_0,o_0_0_xboole_0,o_0_0_xboole_0,o_0_0_xboole_0,o_0_0_xboole_0)) != k7_subset_1(k9_setfam_1(u1_struct_0(sK3)),k9_setfam_1(u1_struct_0(sK3)),k6_enumset1(o_0_0_xboole_0,o_0_0_xboole_0,o_0_0_xboole_0,o_0_0_xboole_0,o_0_0_xboole_0,o_0_0_xboole_0,o_0_0_xboole_0,o_0_0_xboole_0)) ),
    inference(unflattening,[status(thm)],[c_393])).

cnf(c_540,plain,
    ( ~ m2_orders_2(X0,X1,sK4)
    | r2_hidden(X0,k4_orders_2(X1,sK4))
    | v2_struct_0(X1)
    | ~ v3_orders_2(X1)
    | ~ v4_orders_2(X1)
    | ~ v5_orders_2(X1)
    | k7_subset_1(k9_setfam_1(u1_struct_0(X1)),k9_setfam_1(u1_struct_0(X1)),k6_enumset1(o_0_0_xboole_0,o_0_0_xboole_0,o_0_0_xboole_0,o_0_0_xboole_0,o_0_0_xboole_0,o_0_0_xboole_0,o_0_0_xboole_0,o_0_0_xboole_0)) != k7_subset_1(k9_setfam_1(u1_struct_0(sK3)),k9_setfam_1(u1_struct_0(sK3)),k6_enumset1(o_0_0_xboole_0,o_0_0_xboole_0,o_0_0_xboole_0,o_0_0_xboole_0,o_0_0_xboole_0,o_0_0_xboole_0,o_0_0_xboole_0,o_0_0_xboole_0))
    | sK3 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_394,c_15])).

cnf(c_541,plain,
    ( ~ m2_orders_2(X0,sK3,sK4)
    | r2_hidden(X0,k4_orders_2(sK3,sK4))
    | v2_struct_0(sK3)
    | ~ v3_orders_2(sK3)
    | ~ v4_orders_2(sK3)
    | ~ v5_orders_2(sK3)
    | k7_subset_1(k9_setfam_1(u1_struct_0(sK3)),k9_setfam_1(u1_struct_0(sK3)),k6_enumset1(o_0_0_xboole_0,o_0_0_xboole_0,o_0_0_xboole_0,o_0_0_xboole_0,o_0_0_xboole_0,o_0_0_xboole_0,o_0_0_xboole_0,o_0_0_xboole_0)) != k7_subset_1(k9_setfam_1(u1_struct_0(sK3)),k9_setfam_1(u1_struct_0(sK3)),k6_enumset1(o_0_0_xboole_0,o_0_0_xboole_0,o_0_0_xboole_0,o_0_0_xboole_0,o_0_0_xboole_0,o_0_0_xboole_0,o_0_0_xboole_0,o_0_0_xboole_0)) ),
    inference(unflattening,[status(thm)],[c_540])).

cnf(c_545,plain,
    ( ~ m2_orders_2(X0,sK3,sK4)
    | r2_hidden(X0,k4_orders_2(sK3,sK4))
    | k7_subset_1(k9_setfam_1(u1_struct_0(sK3)),k9_setfam_1(u1_struct_0(sK3)),k6_enumset1(o_0_0_xboole_0,o_0_0_xboole_0,o_0_0_xboole_0,o_0_0_xboole_0,o_0_0_xboole_0,o_0_0_xboole_0,o_0_0_xboole_0,o_0_0_xboole_0)) != k7_subset_1(k9_setfam_1(u1_struct_0(sK3)),k9_setfam_1(u1_struct_0(sK3)),k6_enumset1(o_0_0_xboole_0,o_0_0_xboole_0,o_0_0_xboole_0,o_0_0_xboole_0,o_0_0_xboole_0,o_0_0_xboole_0,o_0_0_xboole_0,o_0_0_xboole_0)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_541,c_19,c_18,c_17,c_16])).

cnf(c_1002,plain,
    ( ~ m2_orders_2(X0,sK3,sK4)
    | r2_hidden(X0,k4_orders_2(sK3,sK4)) ),
    inference(equality_resolution_simp,[status(thm)],[c_545])).

cnf(c_1042,plain,
    ( ~ m2_orders_2(X0,sK3,sK4)
    | r2_hidden(X0,k4_orders_2(sK3,sK4)) ),
    inference(prop_impl,[status(thm)],[c_1002])).

cnf(c_1775,plain,
    ( m2_orders_2(X0,sK3,sK4) != iProver_top
    | r2_hidden(X0,k4_orders_2(sK3,sK4)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1042])).

cnf(c_13,negated_conjecture,
    ( o_0_0_xboole_0 = k3_tarski(k4_orders_2(sK3,sK4)) ),
    inference(cnf_transformation,[],[f98])).

cnf(c_12,plain,
    ( ~ r2_hidden(X0,X1)
    | k3_tarski(X1) != o_0_0_xboole_0
    | o_0_0_xboole_0 = X0 ),
    inference(cnf_transformation,[],[f97])).

cnf(c_1778,plain,
    ( k3_tarski(X0) != o_0_0_xboole_0
    | o_0_0_xboole_0 = X1
    | r2_hidden(X1,X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_12])).

cnf(c_2463,plain,
    ( o_0_0_xboole_0 = X0
    | r2_hidden(X0,k4_orders_2(sK3,sK4)) != iProver_top ),
    inference(superposition,[status(thm)],[c_13,c_1778])).

cnf(c_2480,plain,
    ( o_0_0_xboole_0 = X0
    | m2_orders_2(X0,sK3,sK4) != iProver_top ),
    inference(superposition,[status(thm)],[c_1775,c_2463])).

cnf(c_2499,plain,
    ( sK1(sK3,sK4) = o_0_0_xboole_0 ),
    inference(superposition,[status(thm)],[c_1774,c_2480])).

cnf(c_1438,plain,
    ( X0 != X1
    | X2 != X1
    | X2 = X0 ),
    theory(equality)).

cnf(c_2445,plain,
    ( X0 != X1
    | X0 = sK1(sK3,sK4)
    | sK1(sK3,sK4) != X1 ),
    inference(instantiation,[status(thm)],[c_1438])).

cnf(c_2446,plain,
    ( sK1(sK3,sK4) != o_0_0_xboole_0
    | o_0_0_xboole_0 = sK1(sK3,sK4)
    | o_0_0_xboole_0 != o_0_0_xboole_0 ),
    inference(instantiation,[status(thm)],[c_2445])).

cnf(c_1437,plain,
    ( X0 = X0 ),
    theory(equality)).

cnf(c_2052,plain,
    ( sK3 = sK3 ),
    inference(instantiation,[status(thm)],[c_1437])).

cnf(c_0,plain,
    ( k5_xboole_0(o_0_0_xboole_0,k1_setfam_1(k6_enumset1(o_0_0_xboole_0,o_0_0_xboole_0,o_0_0_xboole_0,o_0_0_xboole_0,o_0_0_xboole_0,o_0_0_xboole_0,o_0_0_xboole_0,X0))) = o_0_0_xboole_0 ),
    inference(cnf_transformation,[],[f85])).

cnf(c_1880,plain,
    ( k5_xboole_0(o_0_0_xboole_0,k1_setfam_1(k6_enumset1(o_0_0_xboole_0,o_0_0_xboole_0,o_0_0_xboole_0,o_0_0_xboole_0,o_0_0_xboole_0,o_0_0_xboole_0,o_0_0_xboole_0,k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0)))) = o_0_0_xboole_0 ),
    inference(instantiation,[status(thm)],[c_0])).

cnf(c_2025,plain,
    ( k5_xboole_0(o_0_0_xboole_0,k1_setfam_1(k6_enumset1(o_0_0_xboole_0,o_0_0_xboole_0,o_0_0_xboole_0,o_0_0_xboole_0,o_0_0_xboole_0,o_0_0_xboole_0,o_0_0_xboole_0,k6_enumset1(k1_funct_1(sK4,u1_struct_0(sK3)),k1_funct_1(sK4,u1_struct_0(sK3)),k1_funct_1(sK4,u1_struct_0(sK3)),k1_funct_1(sK4,u1_struct_0(sK3)),k1_funct_1(sK4,u1_struct_0(sK3)),k1_funct_1(sK4,u1_struct_0(sK3)),k1_funct_1(sK4,u1_struct_0(sK3)),k1_funct_1(sK4,u1_struct_0(sK3)))))) = o_0_0_xboole_0 ),
    inference(instantiation,[status(thm)],[c_1880])).

cnf(c_1901,plain,
    ( sK4 = sK4 ),
    inference(instantiation,[status(thm)],[c_1437])).

cnf(c_1464,plain,
    ( o_0_0_xboole_0 = o_0_0_xboole_0 ),
    inference(instantiation,[status(thm)],[c_1437])).

cnf(c_3,plain,
    ( ~ r2_hidden(X0,X1)
    | k5_xboole_0(X1,k1_setfam_1(k6_enumset1(X1,X1,X1,X1,X1,X1,X1,k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0)))) != X1 ),
    inference(cnf_transformation,[],[f88])).

cnf(c_125,plain,
    ( ~ r2_hidden(X0,X1)
    | k5_xboole_0(X1,k1_setfam_1(k6_enumset1(X1,X1,X1,X1,X1,X1,X1,k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0)))) != X1 ),
    inference(prop_impl,[status(thm)],[c_3])).

cnf(c_9,plain,
    ( ~ m2_orders_2(X0,X1,X2)
    | ~ m1_orders_1(X2,k7_subset_1(k9_setfam_1(u1_struct_0(X1)),k9_setfam_1(u1_struct_0(X1)),k6_enumset1(o_0_0_xboole_0,o_0_0_xboole_0,o_0_0_xboole_0,o_0_0_xboole_0,o_0_0_xboole_0,o_0_0_xboole_0,o_0_0_xboole_0,o_0_0_xboole_0)))
    | r2_hidden(k1_funct_1(X2,u1_struct_0(X1)),X0)
    | v2_struct_0(X1)
    | ~ v3_orders_2(X1)
    | ~ v4_orders_2(X1)
    | ~ v5_orders_2(X1)
    | ~ l1_orders_2(X1) ),
    inference(cnf_transformation,[],[f94])).

cnf(c_333,plain,
    ( ~ m2_orders_2(X0,X1,X2)
    | r2_hidden(k1_funct_1(X2,u1_struct_0(X1)),X0)
    | v2_struct_0(X1)
    | ~ v3_orders_2(X1)
    | ~ v4_orders_2(X1)
    | ~ v5_orders_2(X1)
    | ~ l1_orders_2(X1)
    | k7_subset_1(k9_setfam_1(u1_struct_0(X1)),k9_setfam_1(u1_struct_0(X1)),k6_enumset1(o_0_0_xboole_0,o_0_0_xboole_0,o_0_0_xboole_0,o_0_0_xboole_0,o_0_0_xboole_0,o_0_0_xboole_0,o_0_0_xboole_0,o_0_0_xboole_0)) != k7_subset_1(k9_setfam_1(u1_struct_0(sK3)),k9_setfam_1(u1_struct_0(sK3)),k6_enumset1(o_0_0_xboole_0,o_0_0_xboole_0,o_0_0_xboole_0,o_0_0_xboole_0,o_0_0_xboole_0,o_0_0_xboole_0,o_0_0_xboole_0,o_0_0_xboole_0))
    | sK4 != X2 ),
    inference(resolution_lifted,[status(thm)],[c_9,c_14])).

cnf(c_334,plain,
    ( ~ m2_orders_2(X0,X1,sK4)
    | r2_hidden(k1_funct_1(sK4,u1_struct_0(X1)),X0)
    | v2_struct_0(X1)
    | ~ v3_orders_2(X1)
    | ~ v4_orders_2(X1)
    | ~ v5_orders_2(X1)
    | ~ l1_orders_2(X1)
    | k7_subset_1(k9_setfam_1(u1_struct_0(X1)),k9_setfam_1(u1_struct_0(X1)),k6_enumset1(o_0_0_xboole_0,o_0_0_xboole_0,o_0_0_xboole_0,o_0_0_xboole_0,o_0_0_xboole_0,o_0_0_xboole_0,o_0_0_xboole_0,o_0_0_xboole_0)) != k7_subset_1(k9_setfam_1(u1_struct_0(sK3)),k9_setfam_1(u1_struct_0(sK3)),k6_enumset1(o_0_0_xboole_0,o_0_0_xboole_0,o_0_0_xboole_0,o_0_0_xboole_0,o_0_0_xboole_0,o_0_0_xboole_0,o_0_0_xboole_0,o_0_0_xboole_0)) ),
    inference(unflattening,[status(thm)],[c_333])).

cnf(c_582,plain,
    ( ~ m2_orders_2(X0,X1,sK4)
    | r2_hidden(k1_funct_1(sK4,u1_struct_0(X1)),X0)
    | v2_struct_0(X1)
    | ~ v3_orders_2(X1)
    | ~ v4_orders_2(X1)
    | ~ v5_orders_2(X1)
    | k7_subset_1(k9_setfam_1(u1_struct_0(X1)),k9_setfam_1(u1_struct_0(X1)),k6_enumset1(o_0_0_xboole_0,o_0_0_xboole_0,o_0_0_xboole_0,o_0_0_xboole_0,o_0_0_xboole_0,o_0_0_xboole_0,o_0_0_xboole_0,o_0_0_xboole_0)) != k7_subset_1(k9_setfam_1(u1_struct_0(sK3)),k9_setfam_1(u1_struct_0(sK3)),k6_enumset1(o_0_0_xboole_0,o_0_0_xboole_0,o_0_0_xboole_0,o_0_0_xboole_0,o_0_0_xboole_0,o_0_0_xboole_0,o_0_0_xboole_0,o_0_0_xboole_0))
    | sK3 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_334,c_15])).

cnf(c_583,plain,
    ( ~ m2_orders_2(X0,sK3,sK4)
    | r2_hidden(k1_funct_1(sK4,u1_struct_0(sK3)),X0)
    | v2_struct_0(sK3)
    | ~ v3_orders_2(sK3)
    | ~ v4_orders_2(sK3)
    | ~ v5_orders_2(sK3)
    | k7_subset_1(k9_setfam_1(u1_struct_0(sK3)),k9_setfam_1(u1_struct_0(sK3)),k6_enumset1(o_0_0_xboole_0,o_0_0_xboole_0,o_0_0_xboole_0,o_0_0_xboole_0,o_0_0_xboole_0,o_0_0_xboole_0,o_0_0_xboole_0,o_0_0_xboole_0)) != k7_subset_1(k9_setfam_1(u1_struct_0(sK3)),k9_setfam_1(u1_struct_0(sK3)),k6_enumset1(o_0_0_xboole_0,o_0_0_xboole_0,o_0_0_xboole_0,o_0_0_xboole_0,o_0_0_xboole_0,o_0_0_xboole_0,o_0_0_xboole_0,o_0_0_xboole_0)) ),
    inference(unflattening,[status(thm)],[c_582])).

cnf(c_587,plain,
    ( ~ m2_orders_2(X0,sK3,sK4)
    | r2_hidden(k1_funct_1(sK4,u1_struct_0(sK3)),X0)
    | k7_subset_1(k9_setfam_1(u1_struct_0(sK3)),k9_setfam_1(u1_struct_0(sK3)),k6_enumset1(o_0_0_xboole_0,o_0_0_xboole_0,o_0_0_xboole_0,o_0_0_xboole_0,o_0_0_xboole_0,o_0_0_xboole_0,o_0_0_xboole_0,o_0_0_xboole_0)) != k7_subset_1(k9_setfam_1(u1_struct_0(sK3)),k9_setfam_1(u1_struct_0(sK3)),k6_enumset1(o_0_0_xboole_0,o_0_0_xboole_0,o_0_0_xboole_0,o_0_0_xboole_0,o_0_0_xboole_0,o_0_0_xboole_0,o_0_0_xboole_0,o_0_0_xboole_0)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_583,c_19,c_18,c_17,c_16])).

cnf(c_873,plain,
    ( ~ m2_orders_2(X0,sK3,sK4)
    | X0 != X1
    | k7_subset_1(k9_setfam_1(u1_struct_0(sK3)),k9_setfam_1(u1_struct_0(sK3)),k6_enumset1(o_0_0_xboole_0,o_0_0_xboole_0,o_0_0_xboole_0,o_0_0_xboole_0,o_0_0_xboole_0,o_0_0_xboole_0,o_0_0_xboole_0,o_0_0_xboole_0)) != k7_subset_1(k9_setfam_1(u1_struct_0(sK3)),k9_setfam_1(u1_struct_0(sK3)),k6_enumset1(o_0_0_xboole_0,o_0_0_xboole_0,o_0_0_xboole_0,o_0_0_xboole_0,o_0_0_xboole_0,o_0_0_xboole_0,o_0_0_xboole_0,o_0_0_xboole_0))
    | k1_funct_1(sK4,u1_struct_0(sK3)) != X2
    | k5_xboole_0(X1,k1_setfam_1(k6_enumset1(X1,X1,X1,X1,X1,X1,X1,k6_enumset1(X2,X2,X2,X2,X2,X2,X2,X2)))) != X1 ),
    inference(resolution_lifted,[status(thm)],[c_125,c_587])).

cnf(c_874,plain,
    ( ~ m2_orders_2(X0,sK3,sK4)
    | k5_xboole_0(X0,k1_setfam_1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,k6_enumset1(k1_funct_1(sK4,u1_struct_0(sK3)),k1_funct_1(sK4,u1_struct_0(sK3)),k1_funct_1(sK4,u1_struct_0(sK3)),k1_funct_1(sK4,u1_struct_0(sK3)),k1_funct_1(sK4,u1_struct_0(sK3)),k1_funct_1(sK4,u1_struct_0(sK3)),k1_funct_1(sK4,u1_struct_0(sK3)),k1_funct_1(sK4,u1_struct_0(sK3)))))) != X0 ),
    inference(unflattening,[status(thm)],[c_873])).

cnf(c_876,plain,
    ( ~ m2_orders_2(o_0_0_xboole_0,sK3,sK4)
    | k5_xboole_0(o_0_0_xboole_0,k1_setfam_1(k6_enumset1(o_0_0_xboole_0,o_0_0_xboole_0,o_0_0_xboole_0,o_0_0_xboole_0,o_0_0_xboole_0,o_0_0_xboole_0,o_0_0_xboole_0,k6_enumset1(k1_funct_1(sK4,u1_struct_0(sK3)),k1_funct_1(sK4,u1_struct_0(sK3)),k1_funct_1(sK4,u1_struct_0(sK3)),k1_funct_1(sK4,u1_struct_0(sK3)),k1_funct_1(sK4,u1_struct_0(sK3)),k1_funct_1(sK4,u1_struct_0(sK3)),k1_funct_1(sK4,u1_struct_0(sK3)),k1_funct_1(sK4,u1_struct_0(sK3)))))) != o_0_0_xboole_0 ),
    inference(instantiation,[status(thm)],[c_874])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_2517,c_2499,c_2446,c_2052,c_2025,c_1901,c_1464,c_1006,c_876])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.12  % Command    : iproveropt_run.sh %d %s
% 0.12/0.32  % Computer   : n006.cluster.edu
% 0.12/0.32  % Model      : x86_64 x86_64
% 0.12/0.32  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.32  % Memory     : 8042.1875MB
% 0.12/0.32  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.32  % CPULimit   : 60
% 0.12/0.32  % WCLimit    : 600
% 0.12/0.32  % DateTime   : Tue Dec  1 19:48:22 EST 2020
% 0.12/0.32  % CPUTime    : 
% 0.12/0.32  % Running in FOF mode
% 1.52/0.97  % SZS status Started for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.52/0.97  
% 1.52/0.97  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 1.52/0.97  
% 1.52/0.97  ------  iProver source info
% 1.52/0.97  
% 1.52/0.97  git: date: 2020-06-30 10:37:57 +0100
% 1.52/0.97  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 1.52/0.97  git: non_committed_changes: false
% 1.52/0.97  git: last_make_outside_of_git: false
% 1.52/0.97  
% 1.52/0.97  ------ 
% 1.52/0.97  
% 1.52/0.97  ------ Input Options
% 1.52/0.97  
% 1.52/0.97  --out_options                           all
% 1.52/0.97  --tptp_safe_out                         true
% 1.52/0.97  --problem_path                          ""
% 1.52/0.97  --include_path                          ""
% 1.52/0.97  --clausifier                            res/vclausify_rel
% 1.52/0.97  --clausifier_options                    --mode clausify
% 1.52/0.97  --stdin                                 false
% 1.52/0.97  --stats_out                             all
% 1.52/0.97  
% 1.52/0.97  ------ General Options
% 1.52/0.97  
% 1.52/0.97  --fof                                   false
% 1.52/0.97  --time_out_real                         305.
% 1.52/0.97  --time_out_virtual                      -1.
% 1.52/0.97  --symbol_type_check                     false
% 1.52/0.97  --clausify_out                          false
% 1.52/0.97  --sig_cnt_out                           false
% 1.52/0.97  --trig_cnt_out                          false
% 1.52/0.97  --trig_cnt_out_tolerance                1.
% 1.52/0.97  --trig_cnt_out_sk_spl                   false
% 1.52/0.97  --abstr_cl_out                          false
% 1.52/0.97  
% 1.52/0.97  ------ Global Options
% 1.52/0.97  
% 1.52/0.97  --schedule                              default
% 1.52/0.97  --add_important_lit                     false
% 1.52/0.97  --prop_solver_per_cl                    1000
% 1.52/0.97  --min_unsat_core                        false
% 1.52/0.97  --soft_assumptions                      false
% 1.52/0.97  --soft_lemma_size                       3
% 1.52/0.97  --prop_impl_unit_size                   0
% 1.52/0.97  --prop_impl_unit                        []
% 1.52/0.97  --share_sel_clauses                     true
% 1.52/0.97  --reset_solvers                         false
% 1.52/0.97  --bc_imp_inh                            [conj_cone]
% 1.52/0.97  --conj_cone_tolerance                   3.
% 1.52/0.97  --extra_neg_conj                        none
% 1.52/0.97  --large_theory_mode                     true
% 1.52/0.97  --prolific_symb_bound                   200
% 1.52/0.97  --lt_threshold                          2000
% 1.52/0.97  --clause_weak_htbl                      true
% 1.52/0.97  --gc_record_bc_elim                     false
% 1.52/0.97  
% 1.52/0.97  ------ Preprocessing Options
% 1.52/0.97  
% 1.52/0.97  --preprocessing_flag                    true
% 1.52/0.97  --time_out_prep_mult                    0.1
% 1.52/0.97  --splitting_mode                        input
% 1.52/0.97  --splitting_grd                         true
% 1.52/0.97  --splitting_cvd                         false
% 1.52/0.97  --splitting_cvd_svl                     false
% 1.52/0.97  --splitting_nvd                         32
% 1.52/0.97  --sub_typing                            true
% 1.52/0.97  --prep_gs_sim                           true
% 1.52/0.97  --prep_unflatten                        true
% 1.52/0.97  --prep_res_sim                          true
% 1.52/0.97  --prep_upred                            true
% 1.52/0.97  --prep_sem_filter                       exhaustive
% 1.52/0.97  --prep_sem_filter_out                   false
% 1.52/0.97  --pred_elim                             true
% 1.52/0.97  --res_sim_input                         true
% 1.52/0.97  --eq_ax_congr_red                       true
% 1.52/0.97  --pure_diseq_elim                       true
% 1.52/0.97  --brand_transform                       false
% 1.52/0.97  --non_eq_to_eq                          false
% 1.52/0.97  --prep_def_merge                        true
% 1.52/0.97  --prep_def_merge_prop_impl              false
% 1.52/0.97  --prep_def_merge_mbd                    true
% 1.52/0.97  --prep_def_merge_tr_red                 false
% 1.52/0.97  --prep_def_merge_tr_cl                  false
% 1.52/0.97  --smt_preprocessing                     true
% 1.52/0.97  --smt_ac_axioms                         fast
% 1.52/0.97  --preprocessed_out                      false
% 1.52/0.97  --preprocessed_stats                    false
% 1.52/0.97  
% 1.52/0.97  ------ Abstraction refinement Options
% 1.52/0.97  
% 1.52/0.97  --abstr_ref                             []
% 1.52/0.97  --abstr_ref_prep                        false
% 1.52/0.97  --abstr_ref_until_sat                   false
% 1.52/0.97  --abstr_ref_sig_restrict                funpre
% 1.52/0.97  --abstr_ref_af_restrict_to_split_sk     false
% 1.52/0.97  --abstr_ref_under                       []
% 1.52/0.97  
% 1.52/0.97  ------ SAT Options
% 1.52/0.97  
% 1.52/0.97  --sat_mode                              false
% 1.52/0.97  --sat_fm_restart_options                ""
% 1.52/0.97  --sat_gr_def                            false
% 1.52/0.97  --sat_epr_types                         true
% 1.52/0.97  --sat_non_cyclic_types                  false
% 1.52/0.97  --sat_finite_models                     false
% 1.52/0.97  --sat_fm_lemmas                         false
% 1.52/0.97  --sat_fm_prep                           false
% 1.52/0.97  --sat_fm_uc_incr                        true
% 1.52/0.97  --sat_out_model                         small
% 1.52/0.97  --sat_out_clauses                       false
% 1.52/0.97  
% 1.52/0.97  ------ QBF Options
% 1.52/0.97  
% 1.52/0.97  --qbf_mode                              false
% 1.52/0.97  --qbf_elim_univ                         false
% 1.52/0.97  --qbf_dom_inst                          none
% 1.52/0.97  --qbf_dom_pre_inst                      false
% 1.52/0.97  --qbf_sk_in                             false
% 1.52/0.97  --qbf_pred_elim                         true
% 1.52/0.97  --qbf_split                             512
% 1.52/0.97  
% 1.52/0.97  ------ BMC1 Options
% 1.52/0.97  
% 1.52/0.97  --bmc1_incremental                      false
% 1.52/0.97  --bmc1_axioms                           reachable_all
% 1.52/0.97  --bmc1_min_bound                        0
% 1.52/0.97  --bmc1_max_bound                        -1
% 1.52/0.97  --bmc1_max_bound_default                -1
% 1.52/0.97  --bmc1_symbol_reachability              true
% 1.52/0.97  --bmc1_property_lemmas                  false
% 1.52/0.97  --bmc1_k_induction                      false
% 1.52/0.97  --bmc1_non_equiv_states                 false
% 1.52/0.97  --bmc1_deadlock                         false
% 1.52/0.97  --bmc1_ucm                              false
% 1.52/0.97  --bmc1_add_unsat_core                   none
% 1.52/0.97  --bmc1_unsat_core_children              false
% 1.52/0.97  --bmc1_unsat_core_extrapolate_axioms    false
% 1.52/0.97  --bmc1_out_stat                         full
% 1.52/0.97  --bmc1_ground_init                      false
% 1.52/0.97  --bmc1_pre_inst_next_state              false
% 1.52/0.97  --bmc1_pre_inst_state                   false
% 1.52/0.97  --bmc1_pre_inst_reach_state             false
% 1.52/0.97  --bmc1_out_unsat_core                   false
% 1.52/0.97  --bmc1_aig_witness_out                  false
% 1.52/0.97  --bmc1_verbose                          false
% 1.52/0.97  --bmc1_dump_clauses_tptp                false
% 1.52/0.97  --bmc1_dump_unsat_core_tptp             false
% 1.52/0.97  --bmc1_dump_file                        -
% 1.52/0.97  --bmc1_ucm_expand_uc_limit              128
% 1.52/0.97  --bmc1_ucm_n_expand_iterations          6
% 1.52/0.97  --bmc1_ucm_extend_mode                  1
% 1.52/0.97  --bmc1_ucm_init_mode                    2
% 1.52/0.97  --bmc1_ucm_cone_mode                    none
% 1.52/0.97  --bmc1_ucm_reduced_relation_type        0
% 1.52/0.97  --bmc1_ucm_relax_model                  4
% 1.52/0.97  --bmc1_ucm_full_tr_after_sat            true
% 1.52/0.97  --bmc1_ucm_expand_neg_assumptions       false
% 1.52/0.97  --bmc1_ucm_layered_model                none
% 1.52/0.97  --bmc1_ucm_max_lemma_size               10
% 1.52/0.97  
% 1.52/0.97  ------ AIG Options
% 1.52/0.97  
% 1.52/0.97  --aig_mode                              false
% 1.52/0.97  
% 1.52/0.97  ------ Instantiation Options
% 1.52/0.97  
% 1.52/0.97  --instantiation_flag                    true
% 1.52/0.97  --inst_sos_flag                         false
% 1.52/0.97  --inst_sos_phase                        true
% 1.52/0.97  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 1.52/0.97  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 1.52/0.97  --inst_lit_sel_side                     num_symb
% 1.52/0.97  --inst_solver_per_active                1400
% 1.52/0.97  --inst_solver_calls_frac                1.
% 1.52/0.97  --inst_passive_queue_type               priority_queues
% 1.52/0.97  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 1.52/0.97  --inst_passive_queues_freq              [25;2]
% 1.52/0.97  --inst_dismatching                      true
% 1.52/0.97  --inst_eager_unprocessed_to_passive     true
% 1.52/0.97  --inst_prop_sim_given                   true
% 1.52/0.97  --inst_prop_sim_new                     false
% 1.52/0.97  --inst_subs_new                         false
% 1.52/0.97  --inst_eq_res_simp                      false
% 1.52/0.97  --inst_subs_given                       false
% 1.52/0.97  --inst_orphan_elimination               true
% 1.52/0.97  --inst_learning_loop_flag               true
% 1.52/0.97  --inst_learning_start                   3000
% 1.52/0.97  --inst_learning_factor                  2
% 1.52/0.97  --inst_start_prop_sim_after_learn       3
% 1.52/0.97  --inst_sel_renew                        solver
% 1.52/0.97  --inst_lit_activity_flag                true
% 1.52/0.97  --inst_restr_to_given                   false
% 1.52/0.97  --inst_activity_threshold               500
% 1.52/0.97  --inst_out_proof                        true
% 1.52/0.97  
% 1.52/0.97  ------ Resolution Options
% 1.52/0.97  
% 1.52/0.97  --resolution_flag                       true
% 1.52/0.97  --res_lit_sel                           adaptive
% 1.52/0.97  --res_lit_sel_side                      none
% 1.52/0.97  --res_ordering                          kbo
% 1.52/0.97  --res_to_prop_solver                    active
% 1.52/0.97  --res_prop_simpl_new                    false
% 1.52/0.97  --res_prop_simpl_given                  true
% 1.52/0.97  --res_passive_queue_type                priority_queues
% 1.52/0.97  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 1.52/0.97  --res_passive_queues_freq               [15;5]
% 1.52/0.97  --res_forward_subs                      full
% 1.52/0.97  --res_backward_subs                     full
% 1.52/0.97  --res_forward_subs_resolution           true
% 1.52/0.97  --res_backward_subs_resolution          true
% 1.52/0.97  --res_orphan_elimination                true
% 1.52/0.97  --res_time_limit                        2.
% 1.52/0.97  --res_out_proof                         true
% 1.52/0.97  
% 1.52/0.97  ------ Superposition Options
% 1.52/0.97  
% 1.52/0.97  --superposition_flag                    true
% 1.52/0.97  --sup_passive_queue_type                priority_queues
% 1.52/0.97  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 1.52/0.97  --sup_passive_queues_freq               [8;1;4]
% 1.52/0.97  --demod_completeness_check              fast
% 1.52/0.97  --demod_use_ground                      true
% 1.52/0.97  --sup_to_prop_solver                    passive
% 1.52/0.97  --sup_prop_simpl_new                    true
% 1.52/0.97  --sup_prop_simpl_given                  true
% 1.52/0.97  --sup_fun_splitting                     false
% 1.52/0.97  --sup_smt_interval                      50000
% 1.52/0.97  
% 1.52/0.97  ------ Superposition Simplification Setup
% 1.52/0.97  
% 1.52/0.97  --sup_indices_passive                   []
% 1.52/0.97  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 1.52/0.97  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 1.52/0.97  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 1.52/0.97  --sup_full_triv                         [TrivRules;PropSubs]
% 1.52/0.97  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 1.52/0.97  --sup_full_bw                           [BwDemod]
% 1.52/0.97  --sup_immed_triv                        [TrivRules]
% 1.52/0.97  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 1.52/0.97  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 1.52/0.97  --sup_immed_bw_main                     []
% 1.52/0.97  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 1.52/0.97  --sup_input_triv                        [Unflattening;TrivRules]
% 1.52/0.97  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 1.52/0.97  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 1.52/0.97  
% 1.52/0.97  ------ Combination Options
% 1.52/0.97  
% 1.52/0.97  --comb_res_mult                         3
% 1.52/0.97  --comb_sup_mult                         2
% 1.52/0.97  --comb_inst_mult                        10
% 1.52/0.97  
% 1.52/0.97  ------ Debug Options
% 1.52/0.97  
% 1.52/0.97  --dbg_backtrace                         false
% 1.52/0.97  --dbg_dump_prop_clauses                 false
% 1.52/0.97  --dbg_dump_prop_clauses_file            -
% 1.52/0.97  --dbg_out_stat                          false
% 1.52/0.97  ------ Parsing...
% 1.52/0.97  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 1.52/0.97  
% 1.52/0.97  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe:1:0s pe:2:0s pe:4:0s pe_e  sf_s  rm: 7 0s  sf_e  pe_s  pe_e 
% 1.52/0.97  
% 1.52/0.97  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 1.52/0.97  
% 1.52/0.97  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 1.52/0.97  ------ Proving...
% 1.52/0.97  ------ Problem Properties 
% 1.52/0.97  
% 1.52/0.97  
% 1.52/0.97  clauses                                 14
% 1.52/0.97  conjectures                             1
% 1.52/0.97  EPR                                     0
% 1.52/0.97  Horn                                    11
% 1.52/0.97  unary                                   4
% 1.52/0.97  binary                                  7
% 1.52/0.97  lits                                    27
% 1.52/0.97  lits eq                                 12
% 1.52/0.97  fd_pure                                 0
% 1.52/0.97  fd_pseudo                               0
% 1.52/0.97  fd_cond                                 3
% 1.52/0.97  fd_pseudo_cond                          0
% 1.52/0.97  AC symbols                              0
% 1.52/0.97  
% 1.52/0.97  ------ Schedule dynamic 5 is on 
% 1.52/0.97  
% 1.52/0.97  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" Time Limit: 10.
% 1.52/0.97  
% 1.52/0.97  
% 1.52/0.97  ------ 
% 1.52/0.97  Current options:
% 1.52/0.97  ------ 
% 1.52/0.97  
% 1.52/0.97  ------ Input Options
% 1.52/0.97  
% 1.52/0.97  --out_options                           all
% 1.52/0.97  --tptp_safe_out                         true
% 1.52/0.97  --problem_path                          ""
% 1.52/0.97  --include_path                          ""
% 1.52/0.97  --clausifier                            res/vclausify_rel
% 1.52/0.97  --clausifier_options                    --mode clausify
% 1.52/0.97  --stdin                                 false
% 1.52/0.97  --stats_out                             all
% 1.52/0.97  
% 1.52/0.97  ------ General Options
% 1.52/0.97  
% 1.52/0.97  --fof                                   false
% 1.52/0.97  --time_out_real                         305.
% 1.52/0.97  --time_out_virtual                      -1.
% 1.52/0.97  --symbol_type_check                     false
% 1.52/0.97  --clausify_out                          false
% 1.52/0.97  --sig_cnt_out                           false
% 1.52/0.97  --trig_cnt_out                          false
% 1.52/0.97  --trig_cnt_out_tolerance                1.
% 1.52/0.97  --trig_cnt_out_sk_spl                   false
% 1.52/0.97  --abstr_cl_out                          false
% 1.52/0.97  
% 1.52/0.97  ------ Global Options
% 1.52/0.97  
% 1.52/0.97  --schedule                              default
% 1.52/0.97  --add_important_lit                     false
% 1.52/0.97  --prop_solver_per_cl                    1000
% 1.52/0.97  --min_unsat_core                        false
% 1.52/0.97  --soft_assumptions                      false
% 1.52/0.97  --soft_lemma_size                       3
% 1.52/0.97  --prop_impl_unit_size                   0
% 1.52/0.97  --prop_impl_unit                        []
% 1.52/0.97  --share_sel_clauses                     true
% 1.52/0.97  --reset_solvers                         false
% 1.52/0.97  --bc_imp_inh                            [conj_cone]
% 1.52/0.97  --conj_cone_tolerance                   3.
% 1.52/0.97  --extra_neg_conj                        none
% 1.52/0.97  --large_theory_mode                     true
% 1.52/0.97  --prolific_symb_bound                   200
% 1.52/0.97  --lt_threshold                          2000
% 1.52/0.97  --clause_weak_htbl                      true
% 1.52/0.97  --gc_record_bc_elim                     false
% 1.52/0.97  
% 1.52/0.97  ------ Preprocessing Options
% 1.52/0.97  
% 1.52/0.97  --preprocessing_flag                    true
% 1.52/0.97  --time_out_prep_mult                    0.1
% 1.52/0.97  --splitting_mode                        input
% 1.52/0.97  --splitting_grd                         true
% 1.52/0.97  --splitting_cvd                         false
% 1.52/0.97  --splitting_cvd_svl                     false
% 1.52/0.97  --splitting_nvd                         32
% 1.52/0.97  --sub_typing                            true
% 1.52/0.97  --prep_gs_sim                           true
% 1.52/0.97  --prep_unflatten                        true
% 1.52/0.97  --prep_res_sim                          true
% 1.52/0.97  --prep_upred                            true
% 1.52/0.97  --prep_sem_filter                       exhaustive
% 1.52/0.97  --prep_sem_filter_out                   false
% 1.52/0.97  --pred_elim                             true
% 1.52/0.97  --res_sim_input                         true
% 1.52/0.97  --eq_ax_congr_red                       true
% 1.52/0.97  --pure_diseq_elim                       true
% 1.52/0.97  --brand_transform                       false
% 1.52/0.97  --non_eq_to_eq                          false
% 1.52/0.97  --prep_def_merge                        true
% 1.52/0.97  --prep_def_merge_prop_impl              false
% 1.52/0.97  --prep_def_merge_mbd                    true
% 1.52/0.97  --prep_def_merge_tr_red                 false
% 1.52/0.97  --prep_def_merge_tr_cl                  false
% 1.52/0.97  --smt_preprocessing                     true
% 1.52/0.97  --smt_ac_axioms                         fast
% 1.52/0.97  --preprocessed_out                      false
% 1.52/0.97  --preprocessed_stats                    false
% 1.52/0.97  
% 1.52/0.97  ------ Abstraction refinement Options
% 1.52/0.97  
% 1.52/0.97  --abstr_ref                             []
% 1.52/0.97  --abstr_ref_prep                        false
% 1.52/0.97  --abstr_ref_until_sat                   false
% 1.52/0.97  --abstr_ref_sig_restrict                funpre
% 1.52/0.97  --abstr_ref_af_restrict_to_split_sk     false
% 1.52/0.97  --abstr_ref_under                       []
% 1.52/0.97  
% 1.52/0.97  ------ SAT Options
% 1.52/0.97  
% 1.52/0.97  --sat_mode                              false
% 1.52/0.97  --sat_fm_restart_options                ""
% 1.52/0.97  --sat_gr_def                            false
% 1.52/0.97  --sat_epr_types                         true
% 1.52/0.97  --sat_non_cyclic_types                  false
% 1.52/0.97  --sat_finite_models                     false
% 1.52/0.97  --sat_fm_lemmas                         false
% 1.52/0.97  --sat_fm_prep                           false
% 1.52/0.97  --sat_fm_uc_incr                        true
% 1.52/0.97  --sat_out_model                         small
% 1.52/0.97  --sat_out_clauses                       false
% 1.52/0.97  
% 1.52/0.97  ------ QBF Options
% 1.52/0.97  
% 1.52/0.97  --qbf_mode                              false
% 1.52/0.97  --qbf_elim_univ                         false
% 1.52/0.97  --qbf_dom_inst                          none
% 1.52/0.97  --qbf_dom_pre_inst                      false
% 1.52/0.97  --qbf_sk_in                             false
% 1.52/0.97  --qbf_pred_elim                         true
% 1.52/0.97  --qbf_split                             512
% 1.52/0.97  
% 1.52/0.97  ------ BMC1 Options
% 1.52/0.97  
% 1.52/0.97  --bmc1_incremental                      false
% 1.52/0.97  --bmc1_axioms                           reachable_all
% 1.52/0.97  --bmc1_min_bound                        0
% 1.52/0.97  --bmc1_max_bound                        -1
% 1.52/0.97  --bmc1_max_bound_default                -1
% 1.52/0.97  --bmc1_symbol_reachability              true
% 1.52/0.97  --bmc1_property_lemmas                  false
% 1.52/0.97  --bmc1_k_induction                      false
% 1.52/0.97  --bmc1_non_equiv_states                 false
% 1.52/0.97  --bmc1_deadlock                         false
% 1.52/0.97  --bmc1_ucm                              false
% 1.52/0.97  --bmc1_add_unsat_core                   none
% 1.52/0.97  --bmc1_unsat_core_children              false
% 1.52/0.97  --bmc1_unsat_core_extrapolate_axioms    false
% 1.52/0.97  --bmc1_out_stat                         full
% 1.52/0.97  --bmc1_ground_init                      false
% 1.52/0.97  --bmc1_pre_inst_next_state              false
% 1.52/0.97  --bmc1_pre_inst_state                   false
% 1.52/0.97  --bmc1_pre_inst_reach_state             false
% 1.52/0.97  --bmc1_out_unsat_core                   false
% 1.52/0.97  --bmc1_aig_witness_out                  false
% 1.52/0.97  --bmc1_verbose                          false
% 1.52/0.97  --bmc1_dump_clauses_tptp                false
% 1.52/0.97  --bmc1_dump_unsat_core_tptp             false
% 1.52/0.97  --bmc1_dump_file                        -
% 1.52/0.97  --bmc1_ucm_expand_uc_limit              128
% 1.52/0.97  --bmc1_ucm_n_expand_iterations          6
% 1.52/0.97  --bmc1_ucm_extend_mode                  1
% 1.52/0.97  --bmc1_ucm_init_mode                    2
% 1.52/0.97  --bmc1_ucm_cone_mode                    none
% 1.52/0.97  --bmc1_ucm_reduced_relation_type        0
% 1.52/0.97  --bmc1_ucm_relax_model                  4
% 1.52/0.97  --bmc1_ucm_full_tr_after_sat            true
% 1.52/0.97  --bmc1_ucm_expand_neg_assumptions       false
% 1.52/0.97  --bmc1_ucm_layered_model                none
% 1.52/0.97  --bmc1_ucm_max_lemma_size               10
% 1.52/0.97  
% 1.52/0.97  ------ AIG Options
% 1.52/0.97  
% 1.52/0.97  --aig_mode                              false
% 1.52/0.97  
% 1.52/0.97  ------ Instantiation Options
% 1.52/0.97  
% 1.52/0.97  --instantiation_flag                    true
% 1.52/0.97  --inst_sos_flag                         false
% 1.52/0.97  --inst_sos_phase                        true
% 1.52/0.97  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 1.52/0.97  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 1.52/0.97  --inst_lit_sel_side                     none
% 1.52/0.97  --inst_solver_per_active                1400
% 1.52/0.97  --inst_solver_calls_frac                1.
% 1.52/0.97  --inst_passive_queue_type               priority_queues
% 1.52/0.97  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 1.52/0.97  --inst_passive_queues_freq              [25;2]
% 1.52/0.97  --inst_dismatching                      true
% 1.52/0.97  --inst_eager_unprocessed_to_passive     true
% 1.52/0.97  --inst_prop_sim_given                   true
% 1.52/0.97  --inst_prop_sim_new                     false
% 1.52/0.97  --inst_subs_new                         false
% 1.52/0.97  --inst_eq_res_simp                      false
% 1.52/0.97  --inst_subs_given                       false
% 1.52/0.97  --inst_orphan_elimination               true
% 1.52/0.97  --inst_learning_loop_flag               true
% 1.52/0.97  --inst_learning_start                   3000
% 1.52/0.97  --inst_learning_factor                  2
% 1.52/0.97  --inst_start_prop_sim_after_learn       3
% 1.52/0.97  --inst_sel_renew                        solver
% 1.52/0.97  --inst_lit_activity_flag                true
% 1.52/0.97  --inst_restr_to_given                   false
% 1.52/0.97  --inst_activity_threshold               500
% 1.52/0.97  --inst_out_proof                        true
% 1.52/0.97  
% 1.52/0.97  ------ Resolution Options
% 1.52/0.97  
% 1.52/0.97  --resolution_flag                       false
% 1.52/0.97  --res_lit_sel                           adaptive
% 1.52/0.97  --res_lit_sel_side                      none
% 1.52/0.97  --res_ordering                          kbo
% 1.52/0.97  --res_to_prop_solver                    active
% 1.52/0.97  --res_prop_simpl_new                    false
% 1.52/0.97  --res_prop_simpl_given                  true
% 1.52/0.97  --res_passive_queue_type                priority_queues
% 1.52/0.97  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 1.52/0.97  --res_passive_queues_freq               [15;5]
% 1.52/0.97  --res_forward_subs                      full
% 1.52/0.97  --res_backward_subs                     full
% 1.52/0.97  --res_forward_subs_resolution           true
% 1.52/0.97  --res_backward_subs_resolution          true
% 1.52/0.97  --res_orphan_elimination                true
% 1.52/0.97  --res_time_limit                        2.
% 1.52/0.97  --res_out_proof                         true
% 1.52/0.97  
% 1.52/0.97  ------ Superposition Options
% 1.52/0.97  
% 1.52/0.97  --superposition_flag                    true
% 1.52/0.97  --sup_passive_queue_type                priority_queues
% 1.52/0.97  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 1.52/0.97  --sup_passive_queues_freq               [8;1;4]
% 1.52/0.97  --demod_completeness_check              fast
% 1.52/0.97  --demod_use_ground                      true
% 1.52/0.97  --sup_to_prop_solver                    passive
% 1.52/0.97  --sup_prop_simpl_new                    true
% 1.52/0.97  --sup_prop_simpl_given                  true
% 1.52/0.97  --sup_fun_splitting                     false
% 1.52/0.97  --sup_smt_interval                      50000
% 1.52/0.97  
% 1.52/0.97  ------ Superposition Simplification Setup
% 1.52/0.97  
% 1.52/0.97  --sup_indices_passive                   []
% 1.52/0.97  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 1.52/0.97  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 1.52/0.97  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 1.52/0.97  --sup_full_triv                         [TrivRules;PropSubs]
% 1.52/0.97  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 1.52/0.97  --sup_full_bw                           [BwDemod]
% 1.52/0.97  --sup_immed_triv                        [TrivRules]
% 1.52/0.97  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 1.52/0.97  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 1.52/0.97  --sup_immed_bw_main                     []
% 1.52/0.97  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 1.52/0.97  --sup_input_triv                        [Unflattening;TrivRules]
% 1.52/0.97  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 1.52/0.97  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 1.52/0.97  
% 1.52/0.97  ------ Combination Options
% 1.52/0.97  
% 1.52/0.97  --comb_res_mult                         3
% 1.52/0.97  --comb_sup_mult                         2
% 1.52/0.97  --comb_inst_mult                        10
% 1.52/0.97  
% 1.52/0.97  ------ Debug Options
% 1.52/0.97  
% 1.52/0.97  --dbg_backtrace                         false
% 1.52/0.97  --dbg_dump_prop_clauses                 false
% 1.52/0.97  --dbg_dump_prop_clauses_file            -
% 1.52/0.97  --dbg_out_stat                          false
% 1.52/0.97  
% 1.52/0.97  
% 1.52/0.97  
% 1.52/0.97  
% 1.52/0.97  ------ Proving...
% 1.52/0.97  
% 1.52/0.97  
% 1.52/0.97  % SZS status Theorem for theBenchmark.p
% 1.52/0.97  
% 1.52/0.97  % SZS output start CNFRefutation for theBenchmark.p
% 1.52/0.97  
% 1.52/0.97  fof(f17,axiom,(
% 1.52/0.97    ! [X0,X1] : ((m1_orders_1(X1,k1_orders_1(u1_struct_0(X0))) & l1_orders_2(X0) & v5_orders_2(X0) & v4_orders_2(X0) & v3_orders_2(X0) & ~v2_struct_0(X0)) => ? [X2] : m2_orders_2(X2,X0,X1))),
% 1.52/0.97    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 1.52/0.97  
% 1.52/0.97  fof(f25,plain,(
% 1.52/0.97    ! [X0,X1] : (? [X2] : m2_orders_2(X2,X0,X1) | (~m1_orders_1(X1,k1_orders_1(u1_struct_0(X0))) | ~l1_orders_2(X0) | ~v5_orders_2(X0) | ~v4_orders_2(X0) | ~v3_orders_2(X0) | v2_struct_0(X0)))),
% 1.52/0.97    inference(ennf_transformation,[],[f17])).
% 1.52/0.97  
% 1.52/0.97  fof(f26,plain,(
% 1.52/0.97    ! [X0,X1] : (? [X2] : m2_orders_2(X2,X0,X1) | ~m1_orders_1(X1,k1_orders_1(u1_struct_0(X0))) | ~l1_orders_2(X0) | ~v5_orders_2(X0) | ~v4_orders_2(X0) | ~v3_orders_2(X0) | v2_struct_0(X0))),
% 1.52/0.97    inference(flattening,[],[f25])).
% 1.52/0.97  
% 1.52/0.97  fof(f37,plain,(
% 1.52/0.97    ! [X1,X0] : (? [X2] : m2_orders_2(X2,X0,X1) => m2_orders_2(sK1(X0,X1),X0,X1))),
% 1.52/0.97    introduced(choice_axiom,[])).
% 1.52/0.97  
% 1.52/0.97  fof(f38,plain,(
% 1.52/0.97    ! [X0,X1] : (m2_orders_2(sK1(X0,X1),X0,X1) | ~m1_orders_1(X1,k1_orders_1(u1_struct_0(X0))) | ~l1_orders_2(X0) | ~v5_orders_2(X0) | ~v4_orders_2(X0) | ~v3_orders_2(X0) | v2_struct_0(X0))),
% 1.52/0.97    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1])],[f26,f37])).
% 1.52/0.97  
% 1.52/0.97  fof(f64,plain,(
% 1.52/0.97    ( ! [X0,X1] : (m2_orders_2(sK1(X0,X1),X0,X1) | ~m1_orders_1(X1,k1_orders_1(u1_struct_0(X0))) | ~l1_orders_2(X0) | ~v5_orders_2(X0) | ~v4_orders_2(X0) | ~v3_orders_2(X0) | v2_struct_0(X0)) )),
% 1.52/0.97    inference(cnf_transformation,[],[f38])).
% 1.52/0.97  
% 1.52/0.97  fof(f16,axiom,(
% 1.52/0.97    ! [X0] : k1_orders_1(X0) = k7_subset_1(k1_zfmisc_1(X0),k9_setfam_1(X0),k1_tarski(k1_xboole_0))),
% 1.52/0.97    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 1.52/0.97  
% 1.52/0.97  fof(f63,plain,(
% 1.52/0.97    ( ! [X0] : (k1_orders_1(X0) = k7_subset_1(k1_zfmisc_1(X0),k9_setfam_1(X0),k1_tarski(k1_xboole_0))) )),
% 1.52/0.97    inference(cnf_transformation,[],[f16])).
% 1.52/0.97  
% 1.52/0.97  fof(f14,axiom,(
% 1.52/0.97    ! [X0] : k1_zfmisc_1(X0) = k9_setfam_1(X0)),
% 1.52/0.97    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 1.52/0.97  
% 1.52/0.97  fof(f58,plain,(
% 1.52/0.97    ( ! [X0] : (k1_zfmisc_1(X0) = k9_setfam_1(X0)) )),
% 1.52/0.97    inference(cnf_transformation,[],[f14])).
% 1.52/0.97  
% 1.52/0.97  fof(f4,axiom,(
% 1.52/0.97    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0)),
% 1.52/0.97    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 1.52/0.97  
% 1.52/0.97  fof(f47,plain,(
% 1.52/0.97    ( ! [X0] : (k2_tarski(X0,X0) = k1_tarski(X0)) )),
% 1.52/0.97    inference(cnf_transformation,[],[f4])).
% 1.52/0.97  
% 1.52/0.97  fof(f5,axiom,(
% 1.52/0.97    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1)),
% 1.52/0.97    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 1.52/0.97  
% 1.52/0.97  fof(f48,plain,(
% 1.52/0.97    ( ! [X0,X1] : (k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1)) )),
% 1.52/0.97    inference(cnf_transformation,[],[f5])).
% 1.52/0.97  
% 1.52/0.97  fof(f6,axiom,(
% 1.52/0.97    ! [X0,X1,X2] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2)),
% 1.52/0.97    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 1.52/0.97  
% 1.52/0.97  fof(f49,plain,(
% 1.52/0.97    ( ! [X2,X0,X1] : (k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2)) )),
% 1.52/0.97    inference(cnf_transformation,[],[f6])).
% 1.52/0.97  
% 1.52/0.97  fof(f7,axiom,(
% 1.52/0.97    ! [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) = k3_enumset1(X0,X0,X1,X2,X3)),
% 1.52/0.97    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 1.52/0.97  
% 1.52/0.97  fof(f50,plain,(
% 1.52/0.97    ( ! [X2,X0,X3,X1] : (k2_enumset1(X0,X1,X2,X3) = k3_enumset1(X0,X0,X1,X2,X3)) )),
% 1.52/0.97    inference(cnf_transformation,[],[f7])).
% 1.52/0.97  
% 1.52/0.97  fof(f8,axiom,(
% 1.52/0.97    ! [X0,X1,X2,X3,X4] : k3_enumset1(X0,X1,X2,X3,X4) = k4_enumset1(X0,X0,X1,X2,X3,X4)),
% 1.52/0.97    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 1.52/0.97  
% 1.52/0.97  fof(f51,plain,(
% 1.52/0.97    ( ! [X4,X2,X0,X3,X1] : (k3_enumset1(X0,X1,X2,X3,X4) = k4_enumset1(X0,X0,X1,X2,X3,X4)) )),
% 1.52/0.97    inference(cnf_transformation,[],[f8])).
% 1.52/0.97  
% 1.52/0.97  fof(f9,axiom,(
% 1.52/0.97    ! [X0,X1,X2,X3,X4,X5] : k4_enumset1(X0,X1,X2,X3,X4,X5) = k5_enumset1(X0,X0,X1,X2,X3,X4,X5)),
% 1.52/0.97    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 1.52/0.97  
% 1.52/0.97  fof(f52,plain,(
% 1.52/0.97    ( ! [X4,X2,X0,X5,X3,X1] : (k4_enumset1(X0,X1,X2,X3,X4,X5) = k5_enumset1(X0,X0,X1,X2,X3,X4,X5)) )),
% 1.52/0.97    inference(cnf_transformation,[],[f9])).
% 1.52/0.97  
% 1.52/0.97  fof(f10,axiom,(
% 1.52/0.97    ! [X0,X1,X2,X3,X4,X5,X6] : k5_enumset1(X0,X1,X2,X3,X4,X5,X6) = k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6)),
% 1.52/0.97    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 1.52/0.97  
% 1.52/0.97  fof(f53,plain,(
% 1.52/0.97    ( ! [X6,X4,X2,X0,X5,X3,X1] : (k5_enumset1(X0,X1,X2,X3,X4,X5,X6) = k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6)) )),
% 1.52/0.97    inference(cnf_transformation,[],[f10])).
% 1.52/0.97  
% 1.52/0.97  fof(f76,plain,(
% 1.52/0.97    ( ! [X4,X2,X0,X5,X3,X1] : (k4_enumset1(X0,X1,X2,X3,X4,X5) = k6_enumset1(X0,X0,X0,X1,X2,X3,X4,X5)) )),
% 1.52/0.97    inference(definition_unfolding,[],[f52,f53])).
% 1.52/0.97  
% 1.52/0.97  fof(f77,plain,(
% 1.52/0.97    ( ! [X4,X2,X0,X3,X1] : (k3_enumset1(X0,X1,X2,X3,X4) = k6_enumset1(X0,X0,X0,X0,X1,X2,X3,X4)) )),
% 1.52/0.97    inference(definition_unfolding,[],[f51,f76])).
% 1.52/0.97  
% 1.52/0.97  fof(f78,plain,(
% 1.52/0.97    ( ! [X2,X0,X3,X1] : (k2_enumset1(X0,X1,X2,X3) = k6_enumset1(X0,X0,X0,X0,X0,X1,X2,X3)) )),
% 1.52/0.97    inference(definition_unfolding,[],[f50,f77])).
% 1.52/0.97  
% 1.52/0.97  fof(f79,plain,(
% 1.52/0.97    ( ! [X2,X0,X1] : (k1_enumset1(X0,X1,X2) = k6_enumset1(X0,X0,X0,X0,X0,X0,X1,X2)) )),
% 1.52/0.97    inference(definition_unfolding,[],[f49,f78])).
% 1.52/0.97  
% 1.52/0.97  fof(f80,plain,(
% 1.52/0.97    ( ! [X0,X1] : (k2_tarski(X0,X1) = k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)) )),
% 1.52/0.97    inference(definition_unfolding,[],[f48,f79])).
% 1.52/0.97  
% 1.52/0.97  fof(f83,plain,(
% 1.52/0.97    ( ! [X0] : (k1_tarski(X0) = k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0)) )),
% 1.52/0.97    inference(definition_unfolding,[],[f47,f80])).
% 1.52/0.97  
% 1.52/0.97  fof(f1,axiom,(
% 1.52/0.97    k1_xboole_0 = o_0_0_xboole_0),
% 1.52/0.97    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 1.52/0.97  
% 1.52/0.97  fof(f44,plain,(
% 1.52/0.97    k1_xboole_0 = o_0_0_xboole_0),
% 1.52/0.97    inference(cnf_transformation,[],[f1])).
% 1.52/0.97  
% 1.52/0.97  fof(f84,plain,(
% 1.52/0.97    ( ! [X0] : (k1_orders_1(X0) = k7_subset_1(k9_setfam_1(X0),k9_setfam_1(X0),k6_enumset1(o_0_0_xboole_0,o_0_0_xboole_0,o_0_0_xboole_0,o_0_0_xboole_0,o_0_0_xboole_0,o_0_0_xboole_0,o_0_0_xboole_0,o_0_0_xboole_0))) )),
% 1.52/0.97    inference(definition_unfolding,[],[f63,f58,f83,f44])).
% 1.52/0.97  
% 1.52/0.97  fof(f93,plain,(
% 1.52/0.97    ( ! [X0,X1] : (m2_orders_2(sK1(X0,X1),X0,X1) | ~m1_orders_1(X1,k7_subset_1(k9_setfam_1(u1_struct_0(X0)),k9_setfam_1(u1_struct_0(X0)),k6_enumset1(o_0_0_xboole_0,o_0_0_xboole_0,o_0_0_xboole_0,o_0_0_xboole_0,o_0_0_xboole_0,o_0_0_xboole_0,o_0_0_xboole_0,o_0_0_xboole_0))) | ~l1_orders_2(X0) | ~v5_orders_2(X0) | ~v4_orders_2(X0) | ~v3_orders_2(X0) | v2_struct_0(X0)) )),
% 1.52/0.97    inference(definition_unfolding,[],[f64,f84])).
% 1.52/0.97  
% 1.52/0.97  fof(f20,conjecture,(
% 1.52/0.97    ! [X0] : ((l1_orders_2(X0) & v5_orders_2(X0) & v4_orders_2(X0) & v3_orders_2(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_orders_1(X1,k1_orders_1(u1_struct_0(X0))) => k1_xboole_0 != k3_tarski(k4_orders_2(X0,X1))))),
% 1.52/0.97    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 1.52/0.97  
% 1.52/0.97  fof(f21,negated_conjecture,(
% 1.52/0.97    ~! [X0] : ((l1_orders_2(X0) & v5_orders_2(X0) & v4_orders_2(X0) & v3_orders_2(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_orders_1(X1,k1_orders_1(u1_struct_0(X0))) => k1_xboole_0 != k3_tarski(k4_orders_2(X0,X1))))),
% 1.52/0.97    inference(negated_conjecture,[],[f20])).
% 1.52/0.97  
% 1.52/0.97  fof(f30,plain,(
% 1.52/0.97    ? [X0] : (? [X1] : (k1_xboole_0 = k3_tarski(k4_orders_2(X0,X1)) & m1_orders_1(X1,k1_orders_1(u1_struct_0(X0)))) & (l1_orders_2(X0) & v5_orders_2(X0) & v4_orders_2(X0) & v3_orders_2(X0) & ~v2_struct_0(X0)))),
% 1.52/0.97    inference(ennf_transformation,[],[f21])).
% 1.52/0.97  
% 1.52/0.97  fof(f31,plain,(
% 1.52/0.97    ? [X0] : (? [X1] : (k1_xboole_0 = k3_tarski(k4_orders_2(X0,X1)) & m1_orders_1(X1,k1_orders_1(u1_struct_0(X0)))) & l1_orders_2(X0) & v5_orders_2(X0) & v4_orders_2(X0) & v3_orders_2(X0) & ~v2_struct_0(X0))),
% 1.52/0.97    inference(flattening,[],[f30])).
% 1.52/0.97  
% 1.52/0.97  fof(f42,plain,(
% 1.52/0.97    ( ! [X0] : (? [X1] : (k1_xboole_0 = k3_tarski(k4_orders_2(X0,X1)) & m1_orders_1(X1,k1_orders_1(u1_struct_0(X0)))) => (k1_xboole_0 = k3_tarski(k4_orders_2(X0,sK4)) & m1_orders_1(sK4,k1_orders_1(u1_struct_0(X0))))) )),
% 1.52/0.97    introduced(choice_axiom,[])).
% 1.52/0.97  
% 1.52/0.97  fof(f41,plain,(
% 1.52/0.97    ? [X0] : (? [X1] : (k1_xboole_0 = k3_tarski(k4_orders_2(X0,X1)) & m1_orders_1(X1,k1_orders_1(u1_struct_0(X0)))) & l1_orders_2(X0) & v5_orders_2(X0) & v4_orders_2(X0) & v3_orders_2(X0) & ~v2_struct_0(X0)) => (? [X1] : (k1_xboole_0 = k3_tarski(k4_orders_2(sK3,X1)) & m1_orders_1(X1,k1_orders_1(u1_struct_0(sK3)))) & l1_orders_2(sK3) & v5_orders_2(sK3) & v4_orders_2(sK3) & v3_orders_2(sK3) & ~v2_struct_0(sK3))),
% 1.52/0.97    introduced(choice_axiom,[])).
% 1.52/0.97  
% 1.52/0.97  fof(f43,plain,(
% 1.52/0.97    (k1_xboole_0 = k3_tarski(k4_orders_2(sK3,sK4)) & m1_orders_1(sK4,k1_orders_1(u1_struct_0(sK3)))) & l1_orders_2(sK3) & v5_orders_2(sK3) & v4_orders_2(sK3) & v3_orders_2(sK3) & ~v2_struct_0(sK3)),
% 1.52/0.97    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3,sK4])],[f31,f42,f41])).
% 1.52/0.97  
% 1.52/0.97  fof(f74,plain,(
% 1.52/0.97    m1_orders_1(sK4,k1_orders_1(u1_struct_0(sK3)))),
% 1.52/0.97    inference(cnf_transformation,[],[f43])).
% 1.52/0.97  
% 1.52/0.97  fof(f99,plain,(
% 1.52/0.97    m1_orders_1(sK4,k7_subset_1(k9_setfam_1(u1_struct_0(sK3)),k9_setfam_1(u1_struct_0(sK3)),k6_enumset1(o_0_0_xboole_0,o_0_0_xboole_0,o_0_0_xboole_0,o_0_0_xboole_0,o_0_0_xboole_0,o_0_0_xboole_0,o_0_0_xboole_0,o_0_0_xboole_0)))),
% 1.52/0.97    inference(definition_unfolding,[],[f74,f84])).
% 1.52/0.97  
% 1.52/0.97  fof(f73,plain,(
% 1.52/0.97    l1_orders_2(sK3)),
% 1.52/0.97    inference(cnf_transformation,[],[f43])).
% 1.52/0.97  
% 1.52/0.97  fof(f69,plain,(
% 1.52/0.97    ~v2_struct_0(sK3)),
% 1.52/0.97    inference(cnf_transformation,[],[f43])).
% 1.52/0.97  
% 1.52/0.97  fof(f70,plain,(
% 1.52/0.97    v3_orders_2(sK3)),
% 1.52/0.97    inference(cnf_transformation,[],[f43])).
% 1.52/0.97  
% 1.52/0.97  fof(f71,plain,(
% 1.52/0.97    v4_orders_2(sK3)),
% 1.52/0.97    inference(cnf_transformation,[],[f43])).
% 1.52/0.97  
% 1.52/0.97  fof(f72,plain,(
% 1.52/0.97    v5_orders_2(sK3)),
% 1.52/0.97    inference(cnf_transformation,[],[f43])).
% 1.52/0.97  
% 1.52/0.97  fof(f15,axiom,(
% 1.52/0.97    ! [X0] : ((l1_orders_2(X0) & v5_orders_2(X0) & v4_orders_2(X0) & v3_orders_2(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_orders_1(X1,k1_orders_1(u1_struct_0(X0))) => ! [X2] : (k4_orders_2(X0,X1) = X2 <=> ! [X3] : (r2_hidden(X3,X2) <=> m2_orders_2(X3,X0,X1)))))),
% 1.52/0.97    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 1.52/0.97  
% 1.52/0.97  fof(f23,plain,(
% 1.52/0.97    ! [X0] : (! [X1] : (! [X2] : (k4_orders_2(X0,X1) = X2 <=> ! [X3] : (r2_hidden(X3,X2) <=> m2_orders_2(X3,X0,X1))) | ~m1_orders_1(X1,k1_orders_1(u1_struct_0(X0)))) | (~l1_orders_2(X0) | ~v5_orders_2(X0) | ~v4_orders_2(X0) | ~v3_orders_2(X0) | v2_struct_0(X0)))),
% 1.52/0.97    inference(ennf_transformation,[],[f15])).
% 1.52/0.97  
% 1.52/0.97  fof(f24,plain,(
% 1.52/0.97    ! [X0] : (! [X1] : (! [X2] : (k4_orders_2(X0,X1) = X2 <=> ! [X3] : (r2_hidden(X3,X2) <=> m2_orders_2(X3,X0,X1))) | ~m1_orders_1(X1,k1_orders_1(u1_struct_0(X0)))) | ~l1_orders_2(X0) | ~v5_orders_2(X0) | ~v4_orders_2(X0) | ~v3_orders_2(X0) | v2_struct_0(X0))),
% 1.52/0.97    inference(flattening,[],[f23])).
% 1.52/0.97  
% 1.52/0.97  fof(f33,plain,(
% 1.52/0.97    ! [X0] : (! [X1] : (! [X2] : ((k4_orders_2(X0,X1) = X2 | ? [X3] : ((~m2_orders_2(X3,X0,X1) | ~r2_hidden(X3,X2)) & (m2_orders_2(X3,X0,X1) | r2_hidden(X3,X2)))) & (! [X3] : ((r2_hidden(X3,X2) | ~m2_orders_2(X3,X0,X1)) & (m2_orders_2(X3,X0,X1) | ~r2_hidden(X3,X2))) | k4_orders_2(X0,X1) != X2)) | ~m1_orders_1(X1,k1_orders_1(u1_struct_0(X0)))) | ~l1_orders_2(X0) | ~v5_orders_2(X0) | ~v4_orders_2(X0) | ~v3_orders_2(X0) | v2_struct_0(X0))),
% 1.52/0.97    inference(nnf_transformation,[],[f24])).
% 1.52/0.97  
% 1.52/0.97  fof(f34,plain,(
% 1.52/0.97    ! [X0] : (! [X1] : (! [X2] : ((k4_orders_2(X0,X1) = X2 | ? [X3] : ((~m2_orders_2(X3,X0,X1) | ~r2_hidden(X3,X2)) & (m2_orders_2(X3,X0,X1) | r2_hidden(X3,X2)))) & (! [X4] : ((r2_hidden(X4,X2) | ~m2_orders_2(X4,X0,X1)) & (m2_orders_2(X4,X0,X1) | ~r2_hidden(X4,X2))) | k4_orders_2(X0,X1) != X2)) | ~m1_orders_1(X1,k1_orders_1(u1_struct_0(X0)))) | ~l1_orders_2(X0) | ~v5_orders_2(X0) | ~v4_orders_2(X0) | ~v3_orders_2(X0) | v2_struct_0(X0))),
% 1.52/0.97    inference(rectify,[],[f33])).
% 1.52/0.97  
% 1.52/0.97  fof(f35,plain,(
% 1.52/0.97    ! [X2,X1,X0] : (? [X3] : ((~m2_orders_2(X3,X0,X1) | ~r2_hidden(X3,X2)) & (m2_orders_2(X3,X0,X1) | r2_hidden(X3,X2))) => ((~m2_orders_2(sK0(X0,X1,X2),X0,X1) | ~r2_hidden(sK0(X0,X1,X2),X2)) & (m2_orders_2(sK0(X0,X1,X2),X0,X1) | r2_hidden(sK0(X0,X1,X2),X2))))),
% 1.52/0.97    introduced(choice_axiom,[])).
% 1.52/0.97  
% 1.52/0.97  fof(f36,plain,(
% 1.52/0.97    ! [X0] : (! [X1] : (! [X2] : ((k4_orders_2(X0,X1) = X2 | ((~m2_orders_2(sK0(X0,X1,X2),X0,X1) | ~r2_hidden(sK0(X0,X1,X2),X2)) & (m2_orders_2(sK0(X0,X1,X2),X0,X1) | r2_hidden(sK0(X0,X1,X2),X2)))) & (! [X4] : ((r2_hidden(X4,X2) | ~m2_orders_2(X4,X0,X1)) & (m2_orders_2(X4,X0,X1) | ~r2_hidden(X4,X2))) | k4_orders_2(X0,X1) != X2)) | ~m1_orders_1(X1,k1_orders_1(u1_struct_0(X0)))) | ~l1_orders_2(X0) | ~v5_orders_2(X0) | ~v4_orders_2(X0) | ~v3_orders_2(X0) | v2_struct_0(X0))),
% 1.52/0.97    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f34,f35])).
% 1.52/0.97  
% 1.52/0.97  fof(f60,plain,(
% 1.52/0.97    ( ! [X4,X2,X0,X1] : (r2_hidden(X4,X2) | ~m2_orders_2(X4,X0,X1) | k4_orders_2(X0,X1) != X2 | ~m1_orders_1(X1,k1_orders_1(u1_struct_0(X0))) | ~l1_orders_2(X0) | ~v5_orders_2(X0) | ~v4_orders_2(X0) | ~v3_orders_2(X0) | v2_struct_0(X0)) )),
% 1.52/0.97    inference(cnf_transformation,[],[f36])).
% 1.52/0.97  
% 1.52/0.97  fof(f91,plain,(
% 1.52/0.97    ( ! [X4,X2,X0,X1] : (r2_hidden(X4,X2) | ~m2_orders_2(X4,X0,X1) | k4_orders_2(X0,X1) != X2 | ~m1_orders_1(X1,k7_subset_1(k9_setfam_1(u1_struct_0(X0)),k9_setfam_1(u1_struct_0(X0)),k6_enumset1(o_0_0_xboole_0,o_0_0_xboole_0,o_0_0_xboole_0,o_0_0_xboole_0,o_0_0_xboole_0,o_0_0_xboole_0,o_0_0_xboole_0,o_0_0_xboole_0))) | ~l1_orders_2(X0) | ~v5_orders_2(X0) | ~v4_orders_2(X0) | ~v3_orders_2(X0) | v2_struct_0(X0)) )),
% 1.52/0.97    inference(definition_unfolding,[],[f60,f84])).
% 1.52/0.97  
% 1.52/0.97  fof(f100,plain,(
% 1.52/0.97    ( ! [X4,X0,X1] : (r2_hidden(X4,k4_orders_2(X0,X1)) | ~m2_orders_2(X4,X0,X1) | ~m1_orders_1(X1,k7_subset_1(k9_setfam_1(u1_struct_0(X0)),k9_setfam_1(u1_struct_0(X0)),k6_enumset1(o_0_0_xboole_0,o_0_0_xboole_0,o_0_0_xboole_0,o_0_0_xboole_0,o_0_0_xboole_0,o_0_0_xboole_0,o_0_0_xboole_0,o_0_0_xboole_0))) | ~l1_orders_2(X0) | ~v5_orders_2(X0) | ~v4_orders_2(X0) | ~v3_orders_2(X0) | v2_struct_0(X0)) )),
% 1.52/0.97    inference(equality_resolution,[],[f91])).
% 1.52/0.97  
% 1.52/0.97  fof(f75,plain,(
% 1.52/0.97    k1_xboole_0 = k3_tarski(k4_orders_2(sK3,sK4))),
% 1.52/0.97    inference(cnf_transformation,[],[f43])).
% 1.52/0.97  
% 1.52/0.97  fof(f98,plain,(
% 1.52/0.97    o_0_0_xboole_0 = k3_tarski(k4_orders_2(sK3,sK4))),
% 1.52/0.97    inference(definition_unfolding,[],[f75,f44])).
% 1.52/0.97  
% 1.52/0.97  fof(f19,axiom,(
% 1.52/0.97    ! [X0] : (~(! [X1] : ~(r2_hidden(X1,X0) & k1_xboole_0 != X1) & k1_xboole_0 != k3_tarski(X0)) & ~(k1_xboole_0 = k3_tarski(X0) & ? [X1] : (r2_hidden(X1,X0) & k1_xboole_0 != X1)))),
% 1.52/0.97    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 1.52/0.97  
% 1.52/0.97  fof(f22,plain,(
% 1.52/0.97    ! [X0] : (~(! [X1] : ~(r2_hidden(X1,X0) & k1_xboole_0 != X1) & k1_xboole_0 != k3_tarski(X0)) & ~(k1_xboole_0 = k3_tarski(X0) & ? [X2] : (r2_hidden(X2,X0) & k1_xboole_0 != X2)))),
% 1.52/0.97    inference(rectify,[],[f19])).
% 1.52/0.97  
% 1.52/0.97  fof(f29,plain,(
% 1.52/0.97    ! [X0] : ((? [X1] : (r2_hidden(X1,X0) & k1_xboole_0 != X1) | k1_xboole_0 = k3_tarski(X0)) & (k1_xboole_0 != k3_tarski(X0) | ! [X2] : (~r2_hidden(X2,X0) | k1_xboole_0 = X2)))),
% 1.52/0.97    inference(ennf_transformation,[],[f22])).
% 1.52/0.97  
% 1.52/0.97  fof(f39,plain,(
% 1.52/0.97    ! [X0] : (? [X1] : (r2_hidden(X1,X0) & k1_xboole_0 != X1) => (r2_hidden(sK2(X0),X0) & k1_xboole_0 != sK2(X0)))),
% 1.52/0.97    introduced(choice_axiom,[])).
% 1.52/0.97  
% 1.52/0.97  fof(f40,plain,(
% 1.52/0.97    ! [X0] : (((r2_hidden(sK2(X0),X0) & k1_xboole_0 != sK2(X0)) | k1_xboole_0 = k3_tarski(X0)) & (k1_xboole_0 != k3_tarski(X0) | ! [X2] : (~r2_hidden(X2,X0) | k1_xboole_0 = X2)))),
% 1.52/0.97    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2])],[f29,f39])).
% 1.52/0.97  
% 1.52/0.97  fof(f66,plain,(
% 1.52/0.97    ( ! [X2,X0] : (k1_xboole_0 != k3_tarski(X0) | ~r2_hidden(X2,X0) | k1_xboole_0 = X2) )),
% 1.52/0.97    inference(cnf_transformation,[],[f40])).
% 1.52/0.97  
% 1.52/0.97  fof(f97,plain,(
% 1.52/0.97    ( ! [X2,X0] : (o_0_0_xboole_0 != k3_tarski(X0) | ~r2_hidden(X2,X0) | o_0_0_xboole_0 = X2) )),
% 1.52/0.97    inference(definition_unfolding,[],[f66,f44,f44])).
% 1.52/0.97  
% 1.52/0.97  fof(f3,axiom,(
% 1.52/0.97    ! [X0] : k1_xboole_0 = k4_xboole_0(k1_xboole_0,X0)),
% 1.52/0.97    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 1.52/0.97  
% 1.52/0.97  fof(f46,plain,(
% 1.52/0.97    ( ! [X0] : (k1_xboole_0 = k4_xboole_0(k1_xboole_0,X0)) )),
% 1.52/0.97    inference(cnf_transformation,[],[f3])).
% 1.52/0.97  
% 1.52/0.97  fof(f2,axiom,(
% 1.52/0.97    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))),
% 1.52/0.97    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 1.52/0.97  
% 1.52/0.97  fof(f45,plain,(
% 1.52/0.97    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))) )),
% 1.52/0.97    inference(cnf_transformation,[],[f2])).
% 1.52/0.97  
% 1.52/0.97  fof(f13,axiom,(
% 1.52/0.97    ! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1))),
% 1.52/0.97    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 1.52/0.97  
% 1.52/0.97  fof(f57,plain,(
% 1.52/0.97    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1))) )),
% 1.52/0.97    inference(cnf_transformation,[],[f13])).
% 1.52/0.97  
% 1.52/0.97  fof(f81,plain,(
% 1.52/0.97    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k1_setfam_1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1))) )),
% 1.52/0.97    inference(definition_unfolding,[],[f57,f80])).
% 1.52/0.97  
% 1.52/0.97  fof(f82,plain,(
% 1.52/0.97    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k5_xboole_0(X0,k1_setfam_1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)))) )),
% 1.52/0.97    inference(definition_unfolding,[],[f45,f81])).
% 1.52/0.97  
% 1.52/0.97  fof(f85,plain,(
% 1.52/0.97    ( ! [X0] : (o_0_0_xboole_0 = k5_xboole_0(o_0_0_xboole_0,k1_setfam_1(k6_enumset1(o_0_0_xboole_0,o_0_0_xboole_0,o_0_0_xboole_0,o_0_0_xboole_0,o_0_0_xboole_0,o_0_0_xboole_0,o_0_0_xboole_0,X0)))) )),
% 1.52/0.97    inference(definition_unfolding,[],[f46,f44,f82,f44])).
% 1.52/0.97  
% 1.52/0.97  fof(f12,axiom,(
% 1.52/0.97    ! [X0,X1] : (k4_xboole_0(X0,k1_tarski(X1)) = X0 <=> ~r2_hidden(X1,X0))),
% 1.52/0.97    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 1.52/0.97  
% 1.52/0.97  fof(f32,plain,(
% 1.52/0.97    ! [X0,X1] : ((k4_xboole_0(X0,k1_tarski(X1)) = X0 | r2_hidden(X1,X0)) & (~r2_hidden(X1,X0) | k4_xboole_0(X0,k1_tarski(X1)) != X0))),
% 1.52/0.97    inference(nnf_transformation,[],[f12])).
% 1.52/0.97  
% 1.52/0.97  fof(f55,plain,(
% 1.52/0.97    ( ! [X0,X1] : (~r2_hidden(X1,X0) | k4_xboole_0(X0,k1_tarski(X1)) != X0) )),
% 1.52/0.97    inference(cnf_transformation,[],[f32])).
% 1.52/0.97  
% 1.52/0.97  fof(f88,plain,(
% 1.52/0.97    ( ! [X0,X1] : (~r2_hidden(X1,X0) | k5_xboole_0(X0,k1_setfam_1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1)))) != X0) )),
% 1.52/0.97    inference(definition_unfolding,[],[f55,f82,f83])).
% 1.52/0.97  
% 1.52/0.97  fof(f18,axiom,(
% 1.52/0.97    ! [X0] : ((l1_orders_2(X0) & v5_orders_2(X0) & v4_orders_2(X0) & v3_orders_2(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_orders_1(X1,k1_orders_1(u1_struct_0(X0))) => ! [X2] : (m2_orders_2(X2,X0,X1) => r2_hidden(k1_funct_1(X1,u1_struct_0(X0)),X2))))),
% 1.52/0.97    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 1.52/0.97  
% 1.52/0.97  fof(f27,plain,(
% 1.52/0.97    ! [X0] : (! [X1] : (! [X2] : (r2_hidden(k1_funct_1(X1,u1_struct_0(X0)),X2) | ~m2_orders_2(X2,X0,X1)) | ~m1_orders_1(X1,k1_orders_1(u1_struct_0(X0)))) | (~l1_orders_2(X0) | ~v5_orders_2(X0) | ~v4_orders_2(X0) | ~v3_orders_2(X0) | v2_struct_0(X0)))),
% 1.52/0.97    inference(ennf_transformation,[],[f18])).
% 1.52/0.97  
% 1.52/0.97  fof(f28,plain,(
% 1.52/0.97    ! [X0] : (! [X1] : (! [X2] : (r2_hidden(k1_funct_1(X1,u1_struct_0(X0)),X2) | ~m2_orders_2(X2,X0,X1)) | ~m1_orders_1(X1,k1_orders_1(u1_struct_0(X0)))) | ~l1_orders_2(X0) | ~v5_orders_2(X0) | ~v4_orders_2(X0) | ~v3_orders_2(X0) | v2_struct_0(X0))),
% 1.52/0.97    inference(flattening,[],[f27])).
% 1.52/0.97  
% 1.52/0.97  fof(f65,plain,(
% 1.52/0.97    ( ! [X2,X0,X1] : (r2_hidden(k1_funct_1(X1,u1_struct_0(X0)),X2) | ~m2_orders_2(X2,X0,X1) | ~m1_orders_1(X1,k1_orders_1(u1_struct_0(X0))) | ~l1_orders_2(X0) | ~v5_orders_2(X0) | ~v4_orders_2(X0) | ~v3_orders_2(X0) | v2_struct_0(X0)) )),
% 1.52/0.97    inference(cnf_transformation,[],[f28])).
% 1.52/0.97  
% 1.52/0.97  fof(f94,plain,(
% 1.52/0.97    ( ! [X2,X0,X1] : (r2_hidden(k1_funct_1(X1,u1_struct_0(X0)),X2) | ~m2_orders_2(X2,X0,X1) | ~m1_orders_1(X1,k7_subset_1(k9_setfam_1(u1_struct_0(X0)),k9_setfam_1(u1_struct_0(X0)),k6_enumset1(o_0_0_xboole_0,o_0_0_xboole_0,o_0_0_xboole_0,o_0_0_xboole_0,o_0_0_xboole_0,o_0_0_xboole_0,o_0_0_xboole_0,o_0_0_xboole_0))) | ~l1_orders_2(X0) | ~v5_orders_2(X0) | ~v4_orders_2(X0) | ~v3_orders_2(X0) | v2_struct_0(X0)) )),
% 1.52/0.97    inference(definition_unfolding,[],[f65,f84])).
% 1.52/0.97  
% 1.52/0.97  cnf(c_1446,plain,
% 1.52/0.97      ( ~ m2_orders_2(X0,X1,X2)
% 1.52/0.97      | m2_orders_2(X3,X4,X5)
% 1.52/0.97      | X3 != X0
% 1.52/0.97      | X4 != X1
% 1.52/0.97      | X5 != X2 ),
% 1.52/0.97      theory(equality) ).
% 1.52/0.97  
% 1.52/0.97  cnf(c_1869,plain,
% 1.52/0.97      ( m2_orders_2(X0,X1,X2)
% 1.52/0.97      | ~ m2_orders_2(sK1(sK3,sK4),sK3,sK4)
% 1.52/0.97      | X0 != sK1(sK3,sK4)
% 1.52/0.97      | X2 != sK4
% 1.52/0.97      | X1 != sK3 ),
% 1.52/0.97      inference(instantiation,[status(thm)],[c_1446]) ).
% 1.52/0.97  
% 1.52/0.97  cnf(c_1900,plain,
% 1.52/0.97      ( m2_orders_2(X0,X1,sK4)
% 1.52/0.97      | ~ m2_orders_2(sK1(sK3,sK4),sK3,sK4)
% 1.52/0.97      | X0 != sK1(sK3,sK4)
% 1.52/0.97      | X1 != sK3
% 1.52/0.97      | sK4 != sK4 ),
% 1.52/0.97      inference(instantiation,[status(thm)],[c_1869]) ).
% 1.52/0.97  
% 1.52/0.97  cnf(c_2514,plain,
% 1.52/0.97      ( m2_orders_2(X0,sK3,sK4)
% 1.52/0.97      | ~ m2_orders_2(sK1(sK3,sK4),sK3,sK4)
% 1.52/0.97      | X0 != sK1(sK3,sK4)
% 1.52/0.97      | sK4 != sK4
% 1.52/0.97      | sK3 != sK3 ),
% 1.52/0.97      inference(instantiation,[status(thm)],[c_1900]) ).
% 1.52/0.97  
% 1.52/0.97  cnf(c_2517,plain,
% 1.52/0.97      ( ~ m2_orders_2(sK1(sK3,sK4),sK3,sK4)
% 1.52/0.98      | m2_orders_2(o_0_0_xboole_0,sK3,sK4)
% 1.52/0.98      | sK4 != sK4
% 1.52/0.98      | sK3 != sK3
% 1.52/0.98      | o_0_0_xboole_0 != sK1(sK3,sK4) ),
% 1.52/0.98      inference(instantiation,[status(thm)],[c_2514]) ).
% 1.52/0.98  
% 1.52/0.98  cnf(c_8,plain,
% 1.52/0.98      ( m2_orders_2(sK1(X0,X1),X0,X1)
% 1.52/0.98      | ~ m1_orders_1(X1,k7_subset_1(k9_setfam_1(u1_struct_0(X0)),k9_setfam_1(u1_struct_0(X0)),k6_enumset1(o_0_0_xboole_0,o_0_0_xboole_0,o_0_0_xboole_0,o_0_0_xboole_0,o_0_0_xboole_0,o_0_0_xboole_0,o_0_0_xboole_0,o_0_0_xboole_0)))
% 1.52/0.98      | v2_struct_0(X0)
% 1.52/0.98      | ~ v3_orders_2(X0)
% 1.52/0.98      | ~ v4_orders_2(X0)
% 1.52/0.98      | ~ v5_orders_2(X0)
% 1.52/0.98      | ~ l1_orders_2(X0) ),
% 1.52/0.98      inference(cnf_transformation,[],[f93]) ).
% 1.52/0.98  
% 1.52/0.98  cnf(c_14,negated_conjecture,
% 1.52/0.98      ( m1_orders_1(sK4,k7_subset_1(k9_setfam_1(u1_struct_0(sK3)),k9_setfam_1(u1_struct_0(sK3)),k6_enumset1(o_0_0_xboole_0,o_0_0_xboole_0,o_0_0_xboole_0,o_0_0_xboole_0,o_0_0_xboole_0,o_0_0_xboole_0,o_0_0_xboole_0,o_0_0_xboole_0))) ),
% 1.52/0.98      inference(cnf_transformation,[],[f99]) ).
% 1.52/0.98  
% 1.52/0.98  cnf(c_240,plain,
% 1.52/0.98      ( m2_orders_2(sK1(X0,X1),X0,X1)
% 1.52/0.98      | v2_struct_0(X0)
% 1.52/0.98      | ~ v3_orders_2(X0)
% 1.52/0.98      | ~ v4_orders_2(X0)
% 1.52/0.98      | ~ v5_orders_2(X0)
% 1.52/0.98      | ~ l1_orders_2(X0)
% 1.52/0.98      | k7_subset_1(k9_setfam_1(u1_struct_0(X0)),k9_setfam_1(u1_struct_0(X0)),k6_enumset1(o_0_0_xboole_0,o_0_0_xboole_0,o_0_0_xboole_0,o_0_0_xboole_0,o_0_0_xboole_0,o_0_0_xboole_0,o_0_0_xboole_0,o_0_0_xboole_0)) != k7_subset_1(k9_setfam_1(u1_struct_0(sK3)),k9_setfam_1(u1_struct_0(sK3)),k6_enumset1(o_0_0_xboole_0,o_0_0_xboole_0,o_0_0_xboole_0,o_0_0_xboole_0,o_0_0_xboole_0,o_0_0_xboole_0,o_0_0_xboole_0,o_0_0_xboole_0))
% 1.52/0.98      | sK4 != X1 ),
% 1.52/0.98      inference(resolution_lifted,[status(thm)],[c_8,c_14]) ).
% 1.52/0.98  
% 1.52/0.98  cnf(c_241,plain,
% 1.52/0.98      ( m2_orders_2(sK1(X0,sK4),X0,sK4)
% 1.52/0.98      | v2_struct_0(X0)
% 1.52/0.98      | ~ v3_orders_2(X0)
% 1.52/0.98      | ~ v4_orders_2(X0)
% 1.52/0.98      | ~ v5_orders_2(X0)
% 1.52/0.98      | ~ l1_orders_2(X0)
% 1.52/0.98      | k7_subset_1(k9_setfam_1(u1_struct_0(X0)),k9_setfam_1(u1_struct_0(X0)),k6_enumset1(o_0_0_xboole_0,o_0_0_xboole_0,o_0_0_xboole_0,o_0_0_xboole_0,o_0_0_xboole_0,o_0_0_xboole_0,o_0_0_xboole_0,o_0_0_xboole_0)) != k7_subset_1(k9_setfam_1(u1_struct_0(sK3)),k9_setfam_1(u1_struct_0(sK3)),k6_enumset1(o_0_0_xboole_0,o_0_0_xboole_0,o_0_0_xboole_0,o_0_0_xboole_0,o_0_0_xboole_0,o_0_0_xboole_0,o_0_0_xboole_0,o_0_0_xboole_0)) ),
% 1.52/0.98      inference(unflattening,[status(thm)],[c_240]) ).
% 1.52/0.98  
% 1.52/0.98  cnf(c_15,negated_conjecture,
% 1.52/0.98      ( l1_orders_2(sK3) ),
% 1.52/0.98      inference(cnf_transformation,[],[f73]) ).
% 1.52/0.98  
% 1.52/0.98  cnf(c_526,plain,
% 1.52/0.98      ( m2_orders_2(sK1(X0,sK4),X0,sK4)
% 1.52/0.98      | v2_struct_0(X0)
% 1.52/0.98      | ~ v3_orders_2(X0)
% 1.52/0.98      | ~ v4_orders_2(X0)
% 1.52/0.98      | ~ v5_orders_2(X0)
% 1.52/0.98      | k7_subset_1(k9_setfam_1(u1_struct_0(X0)),k9_setfam_1(u1_struct_0(X0)),k6_enumset1(o_0_0_xboole_0,o_0_0_xboole_0,o_0_0_xboole_0,o_0_0_xboole_0,o_0_0_xboole_0,o_0_0_xboole_0,o_0_0_xboole_0,o_0_0_xboole_0)) != k7_subset_1(k9_setfam_1(u1_struct_0(sK3)),k9_setfam_1(u1_struct_0(sK3)),k6_enumset1(o_0_0_xboole_0,o_0_0_xboole_0,o_0_0_xboole_0,o_0_0_xboole_0,o_0_0_xboole_0,o_0_0_xboole_0,o_0_0_xboole_0,o_0_0_xboole_0))
% 1.52/0.98      | sK3 != X0 ),
% 1.52/0.98      inference(resolution_lifted,[status(thm)],[c_241,c_15]) ).
% 1.52/0.98  
% 1.52/0.98  cnf(c_527,plain,
% 1.52/0.98      ( m2_orders_2(sK1(sK3,sK4),sK3,sK4)
% 1.52/0.98      | v2_struct_0(sK3)
% 1.52/0.98      | ~ v3_orders_2(sK3)
% 1.52/0.98      | ~ v4_orders_2(sK3)
% 1.52/0.98      | ~ v5_orders_2(sK3)
% 1.52/0.98      | k7_subset_1(k9_setfam_1(u1_struct_0(sK3)),k9_setfam_1(u1_struct_0(sK3)),k6_enumset1(o_0_0_xboole_0,o_0_0_xboole_0,o_0_0_xboole_0,o_0_0_xboole_0,o_0_0_xboole_0,o_0_0_xboole_0,o_0_0_xboole_0,o_0_0_xboole_0)) != k7_subset_1(k9_setfam_1(u1_struct_0(sK3)),k9_setfam_1(u1_struct_0(sK3)),k6_enumset1(o_0_0_xboole_0,o_0_0_xboole_0,o_0_0_xboole_0,o_0_0_xboole_0,o_0_0_xboole_0,o_0_0_xboole_0,o_0_0_xboole_0,o_0_0_xboole_0)) ),
% 1.52/0.98      inference(unflattening,[status(thm)],[c_526]) ).
% 1.52/0.98  
% 1.52/0.98  cnf(c_19,negated_conjecture,
% 1.52/0.98      ( ~ v2_struct_0(sK3) ),
% 1.52/0.98      inference(cnf_transformation,[],[f69]) ).
% 1.52/0.98  
% 1.52/0.98  cnf(c_18,negated_conjecture,
% 1.52/0.98      ( v3_orders_2(sK3) ),
% 1.52/0.98      inference(cnf_transformation,[],[f70]) ).
% 1.52/0.98  
% 1.52/0.98  cnf(c_17,negated_conjecture,
% 1.52/0.98      ( v4_orders_2(sK3) ),
% 1.52/0.98      inference(cnf_transformation,[],[f71]) ).
% 1.52/0.98  
% 1.52/0.98  cnf(c_16,negated_conjecture,
% 1.52/0.98      ( v5_orders_2(sK3) ),
% 1.52/0.98      inference(cnf_transformation,[],[f72]) ).
% 1.52/0.98  
% 1.52/0.98  cnf(c_529,plain,
% 1.52/0.98      ( m2_orders_2(sK1(sK3,sK4),sK3,sK4)
% 1.52/0.98      | k7_subset_1(k9_setfam_1(u1_struct_0(sK3)),k9_setfam_1(u1_struct_0(sK3)),k6_enumset1(o_0_0_xboole_0,o_0_0_xboole_0,o_0_0_xboole_0,o_0_0_xboole_0,o_0_0_xboole_0,o_0_0_xboole_0,o_0_0_xboole_0,o_0_0_xboole_0)) != k7_subset_1(k9_setfam_1(u1_struct_0(sK3)),k9_setfam_1(u1_struct_0(sK3)),k6_enumset1(o_0_0_xboole_0,o_0_0_xboole_0,o_0_0_xboole_0,o_0_0_xboole_0,o_0_0_xboole_0,o_0_0_xboole_0,o_0_0_xboole_0,o_0_0_xboole_0)) ),
% 1.52/0.98      inference(global_propositional_subsumption,
% 1.52/0.98                [status(thm)],
% 1.52/0.98                [c_527,c_19,c_18,c_17,c_16]) ).
% 1.52/0.98  
% 1.52/0.98  cnf(c_1006,plain,
% 1.52/0.98      ( m2_orders_2(sK1(sK3,sK4),sK3,sK4) ),
% 1.52/0.98      inference(equality_resolution_simp,[status(thm)],[c_529]) ).
% 1.52/0.98  
% 1.52/0.98  cnf(c_1774,plain,
% 1.52/0.98      ( m2_orders_2(sK1(sK3,sK4),sK3,sK4) = iProver_top ),
% 1.52/0.98      inference(predicate_to_equality,[status(thm)],[c_1006]) ).
% 1.52/0.98  
% 1.52/0.98  cnf(c_6,plain,
% 1.52/0.98      ( ~ m2_orders_2(X0,X1,X2)
% 1.52/0.98      | ~ m1_orders_1(X2,k7_subset_1(k9_setfam_1(u1_struct_0(X1)),k9_setfam_1(u1_struct_0(X1)),k6_enumset1(o_0_0_xboole_0,o_0_0_xboole_0,o_0_0_xboole_0,o_0_0_xboole_0,o_0_0_xboole_0,o_0_0_xboole_0,o_0_0_xboole_0,o_0_0_xboole_0)))
% 1.52/0.98      | r2_hidden(X0,k4_orders_2(X1,X2))
% 1.52/0.98      | v2_struct_0(X1)
% 1.52/0.98      | ~ v3_orders_2(X1)
% 1.52/0.98      | ~ v4_orders_2(X1)
% 1.52/0.98      | ~ v5_orders_2(X1)
% 1.52/0.98      | ~ l1_orders_2(X1) ),
% 1.52/0.98      inference(cnf_transformation,[],[f100]) ).
% 1.52/0.98  
% 1.52/0.98  cnf(c_393,plain,
% 1.52/0.98      ( ~ m2_orders_2(X0,X1,X2)
% 1.52/0.98      | r2_hidden(X0,k4_orders_2(X1,X2))
% 1.52/0.98      | v2_struct_0(X1)
% 1.52/0.98      | ~ v3_orders_2(X1)
% 1.52/0.98      | ~ v4_orders_2(X1)
% 1.52/0.98      | ~ v5_orders_2(X1)
% 1.52/0.98      | ~ l1_orders_2(X1)
% 1.52/0.98      | k7_subset_1(k9_setfam_1(u1_struct_0(X1)),k9_setfam_1(u1_struct_0(X1)),k6_enumset1(o_0_0_xboole_0,o_0_0_xboole_0,o_0_0_xboole_0,o_0_0_xboole_0,o_0_0_xboole_0,o_0_0_xboole_0,o_0_0_xboole_0,o_0_0_xboole_0)) != k7_subset_1(k9_setfam_1(u1_struct_0(sK3)),k9_setfam_1(u1_struct_0(sK3)),k6_enumset1(o_0_0_xboole_0,o_0_0_xboole_0,o_0_0_xboole_0,o_0_0_xboole_0,o_0_0_xboole_0,o_0_0_xboole_0,o_0_0_xboole_0,o_0_0_xboole_0))
% 1.52/0.98      | sK4 != X2 ),
% 1.52/0.98      inference(resolution_lifted,[status(thm)],[c_6,c_14]) ).
% 1.52/0.98  
% 1.52/0.98  cnf(c_394,plain,
% 1.52/0.98      ( ~ m2_orders_2(X0,X1,sK4)
% 1.52/0.98      | r2_hidden(X0,k4_orders_2(X1,sK4))
% 1.52/0.98      | v2_struct_0(X1)
% 1.52/0.98      | ~ v3_orders_2(X1)
% 1.52/0.98      | ~ v4_orders_2(X1)
% 1.52/0.98      | ~ v5_orders_2(X1)
% 1.52/0.98      | ~ l1_orders_2(X1)
% 1.52/0.98      | k7_subset_1(k9_setfam_1(u1_struct_0(X1)),k9_setfam_1(u1_struct_0(X1)),k6_enumset1(o_0_0_xboole_0,o_0_0_xboole_0,o_0_0_xboole_0,o_0_0_xboole_0,o_0_0_xboole_0,o_0_0_xboole_0,o_0_0_xboole_0,o_0_0_xboole_0)) != k7_subset_1(k9_setfam_1(u1_struct_0(sK3)),k9_setfam_1(u1_struct_0(sK3)),k6_enumset1(o_0_0_xboole_0,o_0_0_xboole_0,o_0_0_xboole_0,o_0_0_xboole_0,o_0_0_xboole_0,o_0_0_xboole_0,o_0_0_xboole_0,o_0_0_xboole_0)) ),
% 1.52/0.98      inference(unflattening,[status(thm)],[c_393]) ).
% 1.52/0.98  
% 1.52/0.98  cnf(c_540,plain,
% 1.52/0.98      ( ~ m2_orders_2(X0,X1,sK4)
% 1.52/0.98      | r2_hidden(X0,k4_orders_2(X1,sK4))
% 1.52/0.98      | v2_struct_0(X1)
% 1.52/0.98      | ~ v3_orders_2(X1)
% 1.52/0.98      | ~ v4_orders_2(X1)
% 1.52/0.98      | ~ v5_orders_2(X1)
% 1.52/0.98      | k7_subset_1(k9_setfam_1(u1_struct_0(X1)),k9_setfam_1(u1_struct_0(X1)),k6_enumset1(o_0_0_xboole_0,o_0_0_xboole_0,o_0_0_xboole_0,o_0_0_xboole_0,o_0_0_xboole_0,o_0_0_xboole_0,o_0_0_xboole_0,o_0_0_xboole_0)) != k7_subset_1(k9_setfam_1(u1_struct_0(sK3)),k9_setfam_1(u1_struct_0(sK3)),k6_enumset1(o_0_0_xboole_0,o_0_0_xboole_0,o_0_0_xboole_0,o_0_0_xboole_0,o_0_0_xboole_0,o_0_0_xboole_0,o_0_0_xboole_0,o_0_0_xboole_0))
% 1.52/0.98      | sK3 != X1 ),
% 1.52/0.98      inference(resolution_lifted,[status(thm)],[c_394,c_15]) ).
% 1.52/0.98  
% 1.52/0.98  cnf(c_541,plain,
% 1.52/0.98      ( ~ m2_orders_2(X0,sK3,sK4)
% 1.52/0.98      | r2_hidden(X0,k4_orders_2(sK3,sK4))
% 1.52/0.98      | v2_struct_0(sK3)
% 1.52/0.98      | ~ v3_orders_2(sK3)
% 1.52/0.98      | ~ v4_orders_2(sK3)
% 1.52/0.98      | ~ v5_orders_2(sK3)
% 1.52/0.98      | k7_subset_1(k9_setfam_1(u1_struct_0(sK3)),k9_setfam_1(u1_struct_0(sK3)),k6_enumset1(o_0_0_xboole_0,o_0_0_xboole_0,o_0_0_xboole_0,o_0_0_xboole_0,o_0_0_xboole_0,o_0_0_xboole_0,o_0_0_xboole_0,o_0_0_xboole_0)) != k7_subset_1(k9_setfam_1(u1_struct_0(sK3)),k9_setfam_1(u1_struct_0(sK3)),k6_enumset1(o_0_0_xboole_0,o_0_0_xboole_0,o_0_0_xboole_0,o_0_0_xboole_0,o_0_0_xboole_0,o_0_0_xboole_0,o_0_0_xboole_0,o_0_0_xboole_0)) ),
% 1.52/0.98      inference(unflattening,[status(thm)],[c_540]) ).
% 1.52/0.98  
% 1.52/0.98  cnf(c_545,plain,
% 1.52/0.98      ( ~ m2_orders_2(X0,sK3,sK4)
% 1.52/0.98      | r2_hidden(X0,k4_orders_2(sK3,sK4))
% 1.52/0.98      | k7_subset_1(k9_setfam_1(u1_struct_0(sK3)),k9_setfam_1(u1_struct_0(sK3)),k6_enumset1(o_0_0_xboole_0,o_0_0_xboole_0,o_0_0_xboole_0,o_0_0_xboole_0,o_0_0_xboole_0,o_0_0_xboole_0,o_0_0_xboole_0,o_0_0_xboole_0)) != k7_subset_1(k9_setfam_1(u1_struct_0(sK3)),k9_setfam_1(u1_struct_0(sK3)),k6_enumset1(o_0_0_xboole_0,o_0_0_xboole_0,o_0_0_xboole_0,o_0_0_xboole_0,o_0_0_xboole_0,o_0_0_xboole_0,o_0_0_xboole_0,o_0_0_xboole_0)) ),
% 1.52/0.98      inference(global_propositional_subsumption,
% 1.52/0.98                [status(thm)],
% 1.52/0.98                [c_541,c_19,c_18,c_17,c_16]) ).
% 1.52/0.98  
% 1.52/0.98  cnf(c_1002,plain,
% 1.52/0.98      ( ~ m2_orders_2(X0,sK3,sK4) | r2_hidden(X0,k4_orders_2(sK3,sK4)) ),
% 1.52/0.98      inference(equality_resolution_simp,[status(thm)],[c_545]) ).
% 1.52/0.98  
% 1.52/0.98  cnf(c_1042,plain,
% 1.52/0.98      ( ~ m2_orders_2(X0,sK3,sK4) | r2_hidden(X0,k4_orders_2(sK3,sK4)) ),
% 1.52/0.98      inference(prop_impl,[status(thm)],[c_1002]) ).
% 1.52/0.98  
% 1.52/0.98  cnf(c_1775,plain,
% 1.52/0.98      ( m2_orders_2(X0,sK3,sK4) != iProver_top
% 1.52/0.98      | r2_hidden(X0,k4_orders_2(sK3,sK4)) = iProver_top ),
% 1.52/0.98      inference(predicate_to_equality,[status(thm)],[c_1042]) ).
% 1.52/0.98  
% 1.52/0.98  cnf(c_13,negated_conjecture,
% 1.52/0.98      ( o_0_0_xboole_0 = k3_tarski(k4_orders_2(sK3,sK4)) ),
% 1.52/0.98      inference(cnf_transformation,[],[f98]) ).
% 1.52/0.98  
% 1.52/0.98  cnf(c_12,plain,
% 1.52/0.98      ( ~ r2_hidden(X0,X1)
% 1.52/0.98      | k3_tarski(X1) != o_0_0_xboole_0
% 1.52/0.98      | o_0_0_xboole_0 = X0 ),
% 1.52/0.98      inference(cnf_transformation,[],[f97]) ).
% 1.52/0.98  
% 1.52/0.98  cnf(c_1778,plain,
% 1.52/0.98      ( k3_tarski(X0) != o_0_0_xboole_0
% 1.52/0.98      | o_0_0_xboole_0 = X1
% 1.52/0.98      | r2_hidden(X1,X0) != iProver_top ),
% 1.52/0.98      inference(predicate_to_equality,[status(thm)],[c_12]) ).
% 1.52/0.98  
% 1.52/0.98  cnf(c_2463,plain,
% 1.52/0.98      ( o_0_0_xboole_0 = X0
% 1.52/0.98      | r2_hidden(X0,k4_orders_2(sK3,sK4)) != iProver_top ),
% 1.52/0.98      inference(superposition,[status(thm)],[c_13,c_1778]) ).
% 1.52/0.98  
% 1.52/0.98  cnf(c_2480,plain,
% 1.52/0.98      ( o_0_0_xboole_0 = X0 | m2_orders_2(X0,sK3,sK4) != iProver_top ),
% 1.52/0.98      inference(superposition,[status(thm)],[c_1775,c_2463]) ).
% 1.52/0.98  
% 1.52/0.98  cnf(c_2499,plain,
% 1.52/0.98      ( sK1(sK3,sK4) = o_0_0_xboole_0 ),
% 1.52/0.98      inference(superposition,[status(thm)],[c_1774,c_2480]) ).
% 1.52/0.98  
% 1.52/0.98  cnf(c_1438,plain,( X0 != X1 | X2 != X1 | X2 = X0 ),theory(equality) ).
% 1.52/0.98  
% 1.52/0.98  cnf(c_2445,plain,
% 1.52/0.98      ( X0 != X1 | X0 = sK1(sK3,sK4) | sK1(sK3,sK4) != X1 ),
% 1.52/0.98      inference(instantiation,[status(thm)],[c_1438]) ).
% 1.52/0.98  
% 1.52/0.98  cnf(c_2446,plain,
% 1.52/0.98      ( sK1(sK3,sK4) != o_0_0_xboole_0
% 1.52/0.98      | o_0_0_xboole_0 = sK1(sK3,sK4)
% 1.52/0.98      | o_0_0_xboole_0 != o_0_0_xboole_0 ),
% 1.52/0.98      inference(instantiation,[status(thm)],[c_2445]) ).
% 1.52/0.98  
% 1.52/0.98  cnf(c_1437,plain,( X0 = X0 ),theory(equality) ).
% 1.52/0.98  
% 1.52/0.98  cnf(c_2052,plain,
% 1.52/0.98      ( sK3 = sK3 ),
% 1.52/0.98      inference(instantiation,[status(thm)],[c_1437]) ).
% 1.52/0.98  
% 1.52/0.98  cnf(c_0,plain,
% 1.52/0.98      ( k5_xboole_0(o_0_0_xboole_0,k1_setfam_1(k6_enumset1(o_0_0_xboole_0,o_0_0_xboole_0,o_0_0_xboole_0,o_0_0_xboole_0,o_0_0_xboole_0,o_0_0_xboole_0,o_0_0_xboole_0,X0))) = o_0_0_xboole_0 ),
% 1.52/0.98      inference(cnf_transformation,[],[f85]) ).
% 1.52/0.98  
% 1.52/0.98  cnf(c_1880,plain,
% 1.52/0.98      ( k5_xboole_0(o_0_0_xboole_0,k1_setfam_1(k6_enumset1(o_0_0_xboole_0,o_0_0_xboole_0,o_0_0_xboole_0,o_0_0_xboole_0,o_0_0_xboole_0,o_0_0_xboole_0,o_0_0_xboole_0,k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0)))) = o_0_0_xboole_0 ),
% 1.52/0.98      inference(instantiation,[status(thm)],[c_0]) ).
% 1.52/0.98  
% 1.52/0.98  cnf(c_2025,plain,
% 1.52/0.98      ( k5_xboole_0(o_0_0_xboole_0,k1_setfam_1(k6_enumset1(o_0_0_xboole_0,o_0_0_xboole_0,o_0_0_xboole_0,o_0_0_xboole_0,o_0_0_xboole_0,o_0_0_xboole_0,o_0_0_xboole_0,k6_enumset1(k1_funct_1(sK4,u1_struct_0(sK3)),k1_funct_1(sK4,u1_struct_0(sK3)),k1_funct_1(sK4,u1_struct_0(sK3)),k1_funct_1(sK4,u1_struct_0(sK3)),k1_funct_1(sK4,u1_struct_0(sK3)),k1_funct_1(sK4,u1_struct_0(sK3)),k1_funct_1(sK4,u1_struct_0(sK3)),k1_funct_1(sK4,u1_struct_0(sK3)))))) = o_0_0_xboole_0 ),
% 1.52/0.98      inference(instantiation,[status(thm)],[c_1880]) ).
% 1.52/0.98  
% 1.52/0.98  cnf(c_1901,plain,
% 1.52/0.98      ( sK4 = sK4 ),
% 1.52/0.98      inference(instantiation,[status(thm)],[c_1437]) ).
% 1.52/0.98  
% 1.52/0.98  cnf(c_1464,plain,
% 1.52/0.98      ( o_0_0_xboole_0 = o_0_0_xboole_0 ),
% 1.52/0.98      inference(instantiation,[status(thm)],[c_1437]) ).
% 1.52/0.98  
% 1.52/0.98  cnf(c_3,plain,
% 1.52/0.98      ( ~ r2_hidden(X0,X1)
% 1.52/0.98      | k5_xboole_0(X1,k1_setfam_1(k6_enumset1(X1,X1,X1,X1,X1,X1,X1,k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0)))) != X1 ),
% 1.52/0.98      inference(cnf_transformation,[],[f88]) ).
% 1.52/0.98  
% 1.52/0.98  cnf(c_125,plain,
% 1.52/0.98      ( ~ r2_hidden(X0,X1)
% 1.52/0.98      | k5_xboole_0(X1,k1_setfam_1(k6_enumset1(X1,X1,X1,X1,X1,X1,X1,k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0)))) != X1 ),
% 1.52/0.98      inference(prop_impl,[status(thm)],[c_3]) ).
% 1.52/0.98  
% 1.52/0.98  cnf(c_9,plain,
% 1.52/0.98      ( ~ m2_orders_2(X0,X1,X2)
% 1.52/0.98      | ~ m1_orders_1(X2,k7_subset_1(k9_setfam_1(u1_struct_0(X1)),k9_setfam_1(u1_struct_0(X1)),k6_enumset1(o_0_0_xboole_0,o_0_0_xboole_0,o_0_0_xboole_0,o_0_0_xboole_0,o_0_0_xboole_0,o_0_0_xboole_0,o_0_0_xboole_0,o_0_0_xboole_0)))
% 1.52/0.98      | r2_hidden(k1_funct_1(X2,u1_struct_0(X1)),X0)
% 1.52/0.98      | v2_struct_0(X1)
% 1.52/0.98      | ~ v3_orders_2(X1)
% 1.52/0.98      | ~ v4_orders_2(X1)
% 1.52/0.98      | ~ v5_orders_2(X1)
% 1.52/0.98      | ~ l1_orders_2(X1) ),
% 1.52/0.98      inference(cnf_transformation,[],[f94]) ).
% 1.52/0.98  
% 1.52/0.98  cnf(c_333,plain,
% 1.52/0.98      ( ~ m2_orders_2(X0,X1,X2)
% 1.52/0.98      | r2_hidden(k1_funct_1(X2,u1_struct_0(X1)),X0)
% 1.52/0.98      | v2_struct_0(X1)
% 1.52/0.98      | ~ v3_orders_2(X1)
% 1.52/0.98      | ~ v4_orders_2(X1)
% 1.52/0.98      | ~ v5_orders_2(X1)
% 1.52/0.98      | ~ l1_orders_2(X1)
% 1.52/0.98      | k7_subset_1(k9_setfam_1(u1_struct_0(X1)),k9_setfam_1(u1_struct_0(X1)),k6_enumset1(o_0_0_xboole_0,o_0_0_xboole_0,o_0_0_xboole_0,o_0_0_xboole_0,o_0_0_xboole_0,o_0_0_xboole_0,o_0_0_xboole_0,o_0_0_xboole_0)) != k7_subset_1(k9_setfam_1(u1_struct_0(sK3)),k9_setfam_1(u1_struct_0(sK3)),k6_enumset1(o_0_0_xboole_0,o_0_0_xboole_0,o_0_0_xboole_0,o_0_0_xboole_0,o_0_0_xboole_0,o_0_0_xboole_0,o_0_0_xboole_0,o_0_0_xboole_0))
% 1.52/0.98      | sK4 != X2 ),
% 1.52/0.98      inference(resolution_lifted,[status(thm)],[c_9,c_14]) ).
% 1.52/0.98  
% 1.52/0.98  cnf(c_334,plain,
% 1.52/0.98      ( ~ m2_orders_2(X0,X1,sK4)
% 1.52/0.98      | r2_hidden(k1_funct_1(sK4,u1_struct_0(X1)),X0)
% 1.52/0.98      | v2_struct_0(X1)
% 1.52/0.98      | ~ v3_orders_2(X1)
% 1.52/0.98      | ~ v4_orders_2(X1)
% 1.52/0.98      | ~ v5_orders_2(X1)
% 1.52/0.98      | ~ l1_orders_2(X1)
% 1.52/0.98      | k7_subset_1(k9_setfam_1(u1_struct_0(X1)),k9_setfam_1(u1_struct_0(X1)),k6_enumset1(o_0_0_xboole_0,o_0_0_xboole_0,o_0_0_xboole_0,o_0_0_xboole_0,o_0_0_xboole_0,o_0_0_xboole_0,o_0_0_xboole_0,o_0_0_xboole_0)) != k7_subset_1(k9_setfam_1(u1_struct_0(sK3)),k9_setfam_1(u1_struct_0(sK3)),k6_enumset1(o_0_0_xboole_0,o_0_0_xboole_0,o_0_0_xboole_0,o_0_0_xboole_0,o_0_0_xboole_0,o_0_0_xboole_0,o_0_0_xboole_0,o_0_0_xboole_0)) ),
% 1.52/0.98      inference(unflattening,[status(thm)],[c_333]) ).
% 1.52/0.98  
% 1.52/0.98  cnf(c_582,plain,
% 1.52/0.98      ( ~ m2_orders_2(X0,X1,sK4)
% 1.52/0.98      | r2_hidden(k1_funct_1(sK4,u1_struct_0(X1)),X0)
% 1.52/0.98      | v2_struct_0(X1)
% 1.52/0.98      | ~ v3_orders_2(X1)
% 1.52/0.98      | ~ v4_orders_2(X1)
% 1.52/0.98      | ~ v5_orders_2(X1)
% 1.52/0.98      | k7_subset_1(k9_setfam_1(u1_struct_0(X1)),k9_setfam_1(u1_struct_0(X1)),k6_enumset1(o_0_0_xboole_0,o_0_0_xboole_0,o_0_0_xboole_0,o_0_0_xboole_0,o_0_0_xboole_0,o_0_0_xboole_0,o_0_0_xboole_0,o_0_0_xboole_0)) != k7_subset_1(k9_setfam_1(u1_struct_0(sK3)),k9_setfam_1(u1_struct_0(sK3)),k6_enumset1(o_0_0_xboole_0,o_0_0_xboole_0,o_0_0_xboole_0,o_0_0_xboole_0,o_0_0_xboole_0,o_0_0_xboole_0,o_0_0_xboole_0,o_0_0_xboole_0))
% 1.52/0.98      | sK3 != X1 ),
% 1.52/0.98      inference(resolution_lifted,[status(thm)],[c_334,c_15]) ).
% 1.52/0.98  
% 1.52/0.98  cnf(c_583,plain,
% 1.52/0.98      ( ~ m2_orders_2(X0,sK3,sK4)
% 1.52/0.98      | r2_hidden(k1_funct_1(sK4,u1_struct_0(sK3)),X0)
% 1.52/0.98      | v2_struct_0(sK3)
% 1.52/0.98      | ~ v3_orders_2(sK3)
% 1.52/0.98      | ~ v4_orders_2(sK3)
% 1.52/0.98      | ~ v5_orders_2(sK3)
% 1.52/0.98      | k7_subset_1(k9_setfam_1(u1_struct_0(sK3)),k9_setfam_1(u1_struct_0(sK3)),k6_enumset1(o_0_0_xboole_0,o_0_0_xboole_0,o_0_0_xboole_0,o_0_0_xboole_0,o_0_0_xboole_0,o_0_0_xboole_0,o_0_0_xboole_0,o_0_0_xboole_0)) != k7_subset_1(k9_setfam_1(u1_struct_0(sK3)),k9_setfam_1(u1_struct_0(sK3)),k6_enumset1(o_0_0_xboole_0,o_0_0_xboole_0,o_0_0_xboole_0,o_0_0_xboole_0,o_0_0_xboole_0,o_0_0_xboole_0,o_0_0_xboole_0,o_0_0_xboole_0)) ),
% 1.52/0.98      inference(unflattening,[status(thm)],[c_582]) ).
% 1.52/0.98  
% 1.52/0.98  cnf(c_587,plain,
% 1.52/0.98      ( ~ m2_orders_2(X0,sK3,sK4)
% 1.52/0.98      | r2_hidden(k1_funct_1(sK4,u1_struct_0(sK3)),X0)
% 1.52/0.98      | k7_subset_1(k9_setfam_1(u1_struct_0(sK3)),k9_setfam_1(u1_struct_0(sK3)),k6_enumset1(o_0_0_xboole_0,o_0_0_xboole_0,o_0_0_xboole_0,o_0_0_xboole_0,o_0_0_xboole_0,o_0_0_xboole_0,o_0_0_xboole_0,o_0_0_xboole_0)) != k7_subset_1(k9_setfam_1(u1_struct_0(sK3)),k9_setfam_1(u1_struct_0(sK3)),k6_enumset1(o_0_0_xboole_0,o_0_0_xboole_0,o_0_0_xboole_0,o_0_0_xboole_0,o_0_0_xboole_0,o_0_0_xboole_0,o_0_0_xboole_0,o_0_0_xboole_0)) ),
% 1.52/0.98      inference(global_propositional_subsumption,
% 1.52/0.98                [status(thm)],
% 1.52/0.98                [c_583,c_19,c_18,c_17,c_16]) ).
% 1.52/0.98  
% 1.52/0.98  cnf(c_873,plain,
% 1.52/0.98      ( ~ m2_orders_2(X0,sK3,sK4)
% 1.52/0.98      | X0 != X1
% 1.52/0.98      | k7_subset_1(k9_setfam_1(u1_struct_0(sK3)),k9_setfam_1(u1_struct_0(sK3)),k6_enumset1(o_0_0_xboole_0,o_0_0_xboole_0,o_0_0_xboole_0,o_0_0_xboole_0,o_0_0_xboole_0,o_0_0_xboole_0,o_0_0_xboole_0,o_0_0_xboole_0)) != k7_subset_1(k9_setfam_1(u1_struct_0(sK3)),k9_setfam_1(u1_struct_0(sK3)),k6_enumset1(o_0_0_xboole_0,o_0_0_xboole_0,o_0_0_xboole_0,o_0_0_xboole_0,o_0_0_xboole_0,o_0_0_xboole_0,o_0_0_xboole_0,o_0_0_xboole_0))
% 1.52/0.98      | k1_funct_1(sK4,u1_struct_0(sK3)) != X2
% 1.52/0.98      | k5_xboole_0(X1,k1_setfam_1(k6_enumset1(X1,X1,X1,X1,X1,X1,X1,k6_enumset1(X2,X2,X2,X2,X2,X2,X2,X2)))) != X1 ),
% 1.52/0.98      inference(resolution_lifted,[status(thm)],[c_125,c_587]) ).
% 1.52/0.98  
% 1.52/0.98  cnf(c_874,plain,
% 1.52/0.98      ( ~ m2_orders_2(X0,sK3,sK4)
% 1.52/0.98      | k5_xboole_0(X0,k1_setfam_1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,k6_enumset1(k1_funct_1(sK4,u1_struct_0(sK3)),k1_funct_1(sK4,u1_struct_0(sK3)),k1_funct_1(sK4,u1_struct_0(sK3)),k1_funct_1(sK4,u1_struct_0(sK3)),k1_funct_1(sK4,u1_struct_0(sK3)),k1_funct_1(sK4,u1_struct_0(sK3)),k1_funct_1(sK4,u1_struct_0(sK3)),k1_funct_1(sK4,u1_struct_0(sK3)))))) != X0 ),
% 1.52/0.98      inference(unflattening,[status(thm)],[c_873]) ).
% 1.52/0.98  
% 1.52/0.98  cnf(c_876,plain,
% 1.52/0.98      ( ~ m2_orders_2(o_0_0_xboole_0,sK3,sK4)
% 1.52/0.98      | k5_xboole_0(o_0_0_xboole_0,k1_setfam_1(k6_enumset1(o_0_0_xboole_0,o_0_0_xboole_0,o_0_0_xboole_0,o_0_0_xboole_0,o_0_0_xboole_0,o_0_0_xboole_0,o_0_0_xboole_0,k6_enumset1(k1_funct_1(sK4,u1_struct_0(sK3)),k1_funct_1(sK4,u1_struct_0(sK3)),k1_funct_1(sK4,u1_struct_0(sK3)),k1_funct_1(sK4,u1_struct_0(sK3)),k1_funct_1(sK4,u1_struct_0(sK3)),k1_funct_1(sK4,u1_struct_0(sK3)),k1_funct_1(sK4,u1_struct_0(sK3)),k1_funct_1(sK4,u1_struct_0(sK3)))))) != o_0_0_xboole_0 ),
% 1.52/0.98      inference(instantiation,[status(thm)],[c_874]) ).
% 1.52/0.98  
% 1.52/0.98  cnf(contradiction,plain,
% 1.52/0.98      ( $false ),
% 1.52/0.98      inference(minisat,
% 1.52/0.98                [status(thm)],
% 1.52/0.98                [c_2517,c_2499,c_2446,c_2052,c_2025,c_1901,c_1464,c_1006,
% 1.52/0.98                 c_876]) ).
% 1.52/0.98  
% 1.52/0.98  
% 1.52/0.98  % SZS output end CNFRefutation for theBenchmark.p
% 1.52/0.98  
% 1.52/0.98  ------                               Statistics
% 1.52/0.98  
% 1.52/0.98  ------ General
% 1.52/0.98  
% 1.52/0.98  abstr_ref_over_cycles:                  0
% 1.52/0.98  abstr_ref_under_cycles:                 0
% 1.52/0.98  gc_basic_clause_elim:                   0
% 1.52/0.98  forced_gc_time:                         0
% 1.52/0.98  parsing_time:                           0.01
% 1.52/0.98  unif_index_cands_time:                  0.
% 1.52/0.98  unif_index_add_time:                    0.
% 1.52/0.98  orderings_time:                         0.
% 1.52/0.98  out_proof_time:                         0.015
% 1.52/0.98  total_time:                             0.11
% 1.52/0.98  num_of_symbols:                         54
% 1.52/0.98  num_of_terms:                           1609
% 1.52/0.98  
% 1.52/0.98  ------ Preprocessing
% 1.52/0.98  
% 1.52/0.98  num_of_splits:                          0
% 1.52/0.98  num_of_split_atoms:                     0
% 1.52/0.98  num_of_reused_defs:                     0
% 1.52/0.98  num_eq_ax_congr_red:                    13
% 1.52/0.98  num_of_sem_filtered_clauses:            1
% 1.52/0.98  num_of_subtypes:                        0
% 1.52/0.98  monotx_restored_types:                  0
% 1.52/0.98  sat_num_of_epr_types:                   0
% 1.52/0.98  sat_num_of_non_cyclic_types:            0
% 1.52/0.98  sat_guarded_non_collapsed_types:        0
% 1.52/0.98  num_pure_diseq_elim:                    0
% 1.52/0.98  simp_replaced_by:                       0
% 1.52/0.98  res_preprocessed:                       91
% 1.52/0.98  prep_upred:                             0
% 1.52/0.98  prep_unflattend:                        82
% 1.52/0.98  smt_new_axioms:                         0
% 1.52/0.98  pred_elim_cands:                        2
% 1.52/0.98  pred_elim:                              6
% 1.52/0.98  pred_elim_cl:                           6
% 1.52/0.98  pred_elim_cycles:                       10
% 1.52/0.98  merged_defs:                            14
% 1.52/0.98  merged_defs_ncl:                        0
% 1.52/0.98  bin_hyper_res:                          14
% 1.52/0.98  prep_cycles:                            4
% 1.52/0.98  pred_elim_time:                         0.021
% 1.52/0.98  splitting_time:                         0.
% 1.52/0.98  sem_filter_time:                        0.
% 1.52/0.98  monotx_time:                            0.
% 1.52/0.98  subtype_inf_time:                       0.
% 1.52/0.98  
% 1.52/0.98  ------ Problem properties
% 1.52/0.98  
% 1.52/0.98  clauses:                                14
% 1.52/0.98  conjectures:                            1
% 1.52/0.98  epr:                                    0
% 1.52/0.98  horn:                                   11
% 1.52/0.98  ground:                                 3
% 1.52/0.98  unary:                                  4
% 1.52/0.98  binary:                                 7
% 1.52/0.98  lits:                                   27
% 1.52/0.98  lits_eq:                                12
% 1.52/0.98  fd_pure:                                0
% 1.52/0.98  fd_pseudo:                              0
% 1.52/0.98  fd_cond:                                3
% 1.52/0.98  fd_pseudo_cond:                         0
% 1.52/0.98  ac_symbols:                             0
% 1.52/0.98  
% 1.52/0.98  ------ Propositional Solver
% 1.52/0.98  
% 1.52/0.98  prop_solver_calls:                      25
% 1.52/0.98  prop_fast_solver_calls:                 739
% 1.52/0.98  smt_solver_calls:                       0
% 1.52/0.98  smt_fast_solver_calls:                  0
% 1.52/0.98  prop_num_of_clauses:                    572
% 1.52/0.98  prop_preprocess_simplified:             2968
% 1.52/0.98  prop_fo_subsumed:                       24
% 1.52/0.98  prop_solver_time:                       0.
% 1.52/0.98  smt_solver_time:                        0.
% 1.52/0.98  smt_fast_solver_time:                   0.
% 1.52/0.98  prop_fast_solver_time:                  0.
% 1.52/0.98  prop_unsat_core_time:                   0.
% 1.52/0.98  
% 1.52/0.98  ------ QBF
% 1.52/0.98  
% 1.52/0.98  qbf_q_res:                              0
% 1.52/0.98  qbf_num_tautologies:                    0
% 1.52/0.98  qbf_prep_cycles:                        0
% 1.52/0.98  
% 1.52/0.98  ------ BMC1
% 1.52/0.98  
% 1.52/0.98  bmc1_current_bound:                     -1
% 1.52/0.98  bmc1_last_solved_bound:                 -1
% 1.52/0.98  bmc1_unsat_core_size:                   -1
% 1.52/0.98  bmc1_unsat_core_parents_size:           -1
% 1.52/0.98  bmc1_merge_next_fun:                    0
% 1.52/0.98  bmc1_unsat_core_clauses_time:           0.
% 1.52/0.98  
% 1.52/0.98  ------ Instantiation
% 1.52/0.98  
% 1.52/0.98  inst_num_of_clauses:                    141
% 1.52/0.98  inst_num_in_passive:                    56
% 1.52/0.98  inst_num_in_active:                     70
% 1.52/0.98  inst_num_in_unprocessed:                14
% 1.52/0.98  inst_num_of_loops:                      85
% 1.52/0.98  inst_num_of_learning_restarts:          0
% 1.52/0.98  inst_num_moves_active_passive:          13
% 1.52/0.98  inst_lit_activity:                      0
% 1.52/0.98  inst_lit_activity_moves:                0
% 1.52/0.98  inst_num_tautologies:                   0
% 1.52/0.98  inst_num_prop_implied:                  0
% 1.52/0.98  inst_num_existing_simplified:           0
% 1.52/0.98  inst_num_eq_res_simplified:             0
% 1.52/0.98  inst_num_child_elim:                    0
% 1.52/0.98  inst_num_of_dismatching_blockings:      14
% 1.52/0.98  inst_num_of_non_proper_insts:           65
% 1.52/0.98  inst_num_of_duplicates:                 0
% 1.52/0.98  inst_inst_num_from_inst_to_res:         0
% 1.52/0.98  inst_dismatching_checking_time:         0.
% 1.52/0.98  
% 1.52/0.98  ------ Resolution
% 1.52/0.98  
% 1.52/0.98  res_num_of_clauses:                     0
% 1.52/0.98  res_num_in_passive:                     0
% 1.52/0.98  res_num_in_active:                      0
% 1.52/0.98  res_num_of_loops:                       95
% 1.52/0.98  res_forward_subset_subsumed:            2
% 1.52/0.98  res_backward_subset_subsumed:           0
% 1.52/0.98  res_forward_subsumed:                   0
% 1.52/0.98  res_backward_subsumed:                  0
% 1.52/0.98  res_forward_subsumption_resolution:     0
% 1.52/0.98  res_backward_subsumption_resolution:    0
% 1.52/0.98  res_clause_to_clause_subsumption:       34
% 1.52/0.98  res_orphan_elimination:                 0
% 1.52/0.98  res_tautology_del:                      46
% 1.52/0.98  res_num_eq_res_simplified:              6
% 1.52/0.98  res_num_sel_changes:                    0
% 1.52/0.98  res_moves_from_active_to_pass:          0
% 1.52/0.98  
% 1.52/0.98  ------ Superposition
% 1.52/0.98  
% 1.52/0.98  sup_time_total:                         0.
% 1.52/0.98  sup_time_generating:                    0.
% 1.52/0.98  sup_time_sim_full:                      0.
% 1.52/0.98  sup_time_sim_immed:                     0.
% 1.52/0.98  
% 1.52/0.98  sup_num_of_clauses:                     22
% 1.52/0.98  sup_num_in_active:                      16
% 1.52/0.98  sup_num_in_passive:                     6
% 1.52/0.98  sup_num_of_loops:                       16
% 1.52/0.98  sup_fw_superposition:                   13
% 1.52/0.98  sup_bw_superposition:                   1
% 1.52/0.98  sup_immediate_simplified:               2
% 1.52/0.98  sup_given_eliminated:                   0
% 1.52/0.98  comparisons_done:                       0
% 1.52/0.98  comparisons_avoided:                    0
% 1.52/0.98  
% 1.52/0.98  ------ Simplifications
% 1.52/0.98  
% 1.52/0.98  
% 1.52/0.98  sim_fw_subset_subsumed:                 0
% 1.52/0.98  sim_bw_subset_subsumed:                 0
% 1.52/0.98  sim_fw_subsumed:                        0
% 1.52/0.98  sim_bw_subsumed:                        0
% 1.52/0.98  sim_fw_subsumption_res:                 0
% 1.52/0.98  sim_bw_subsumption_res:                 0
% 1.52/0.98  sim_tautology_del:                      2
% 1.52/0.98  sim_eq_tautology_del:                   4
% 1.52/0.98  sim_eq_res_simp:                        0
% 1.52/0.98  sim_fw_demodulated:                     2
% 1.52/0.98  sim_bw_demodulated:                     0
% 1.52/0.98  sim_light_normalised:                   0
% 1.52/0.98  sim_joinable_taut:                      0
% 1.52/0.98  sim_joinable_simp:                      0
% 1.52/0.98  sim_ac_normalised:                      0
% 1.52/0.98  sim_smt_subsumption:                    0
% 1.52/0.98  
%------------------------------------------------------------------------------
