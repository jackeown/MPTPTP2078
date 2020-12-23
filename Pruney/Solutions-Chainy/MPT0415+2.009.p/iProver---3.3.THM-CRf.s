%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n023.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 11:42:13 EST 2020

% Result     : Theorem 1.88s
% Output     : CNFRefutation 1.88s
% Verified   : 
% Statistics : Number of formulae       :   87 ( 224 expanded)
%              Number of clauses        :   29 (  36 expanded)
%              Number of leaves         :   20 (  65 expanded)
%              Depth                    :   19
%              Number of atoms          :  212 ( 387 expanded)
%              Number of equality atoms :  111 ( 261 expanded)
%              Maximal formula depth    :   13 (   4 average)
%              Maximal clause size      :   14 (   2 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f14,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0)))
     => ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(X0)))
         => ( k7_setfam_1(X0,X1) = X2
          <=> ! [X3] :
                ( m1_subset_1(X3,k1_zfmisc_1(X0))
               => ( r2_hidden(X3,X2)
                <=> r2_hidden(k3_subset_1(X0,X3),X1) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f21,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( ( k7_setfam_1(X0,X1) = X2
          <=> ! [X3] :
                ( ( r2_hidden(X3,X2)
                <=> r2_hidden(k3_subset_1(X0,X3),X1) )
                | ~ m1_subset_1(X3,k1_zfmisc_1(X0)) ) )
          | ~ m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(X0))) )
      | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f30,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( ( ( k7_setfam_1(X0,X1) = X2
              | ? [X3] :
                  ( ( ~ r2_hidden(k3_subset_1(X0,X3),X1)
                    | ~ r2_hidden(X3,X2) )
                  & ( r2_hidden(k3_subset_1(X0,X3),X1)
                    | r2_hidden(X3,X2) )
                  & m1_subset_1(X3,k1_zfmisc_1(X0)) ) )
            & ( ! [X3] :
                  ( ( ( r2_hidden(X3,X2)
                      | ~ r2_hidden(k3_subset_1(X0,X3),X1) )
                    & ( r2_hidden(k3_subset_1(X0,X3),X1)
                      | ~ r2_hidden(X3,X2) ) )
                  | ~ m1_subset_1(X3,k1_zfmisc_1(X0)) )
              | k7_setfam_1(X0,X1) != X2 ) )
          | ~ m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(X0))) )
      | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) ) ),
    inference(nnf_transformation,[],[f21])).

fof(f31,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( ( ( k7_setfam_1(X0,X1) = X2
              | ? [X3] :
                  ( ( ~ r2_hidden(k3_subset_1(X0,X3),X1)
                    | ~ r2_hidden(X3,X2) )
                  & ( r2_hidden(k3_subset_1(X0,X3),X1)
                    | r2_hidden(X3,X2) )
                  & m1_subset_1(X3,k1_zfmisc_1(X0)) ) )
            & ( ! [X3] :
                  ( ( ( r2_hidden(X3,X2)
                      | ~ r2_hidden(k3_subset_1(X0,X3),X1) )
                    & ( r2_hidden(k3_subset_1(X0,X3),X1)
                      | ~ r2_hidden(X3,X2) ) )
                  | ~ m1_subset_1(X3,k1_zfmisc_1(X0)) )
              | k7_setfam_1(X0,X1) != X2 ) )
          | ~ m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(X0))) )
      | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) ) ),
    inference(flattening,[],[f30])).

fof(f32,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( ( ( k7_setfam_1(X0,X1) = X2
              | ? [X3] :
                  ( ( ~ r2_hidden(k3_subset_1(X0,X3),X1)
                    | ~ r2_hidden(X3,X2) )
                  & ( r2_hidden(k3_subset_1(X0,X3),X1)
                    | r2_hidden(X3,X2) )
                  & m1_subset_1(X3,k1_zfmisc_1(X0)) ) )
            & ( ! [X4] :
                  ( ( ( r2_hidden(X4,X2)
                      | ~ r2_hidden(k3_subset_1(X0,X4),X1) )
                    & ( r2_hidden(k3_subset_1(X0,X4),X1)
                      | ~ r2_hidden(X4,X2) ) )
                  | ~ m1_subset_1(X4,k1_zfmisc_1(X0)) )
              | k7_setfam_1(X0,X1) != X2 ) )
          | ~ m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(X0))) )
      | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) ) ),
    inference(rectify,[],[f31])).

fof(f33,plain,(
    ! [X2,X1,X0] :
      ( ? [X3] :
          ( ( ~ r2_hidden(k3_subset_1(X0,X3),X1)
            | ~ r2_hidden(X3,X2) )
          & ( r2_hidden(k3_subset_1(X0,X3),X1)
            | r2_hidden(X3,X2) )
          & m1_subset_1(X3,k1_zfmisc_1(X0)) )
     => ( ( ~ r2_hidden(k3_subset_1(X0,sK1(X0,X1,X2)),X1)
          | ~ r2_hidden(sK1(X0,X1,X2),X2) )
        & ( r2_hidden(k3_subset_1(X0,sK1(X0,X1,X2)),X1)
          | r2_hidden(sK1(X0,X1,X2),X2) )
        & m1_subset_1(sK1(X0,X1,X2),k1_zfmisc_1(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f34,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( ( ( k7_setfam_1(X0,X1) = X2
              | ( ( ~ r2_hidden(k3_subset_1(X0,sK1(X0,X1,X2)),X1)
                  | ~ r2_hidden(sK1(X0,X1,X2),X2) )
                & ( r2_hidden(k3_subset_1(X0,sK1(X0,X1,X2)),X1)
                  | r2_hidden(sK1(X0,X1,X2),X2) )
                & m1_subset_1(sK1(X0,X1,X2),k1_zfmisc_1(X0)) ) )
            & ( ! [X4] :
                  ( ( ( r2_hidden(X4,X2)
                      | ~ r2_hidden(k3_subset_1(X0,X4),X1) )
                    & ( r2_hidden(k3_subset_1(X0,X4),X1)
                      | ~ r2_hidden(X4,X2) ) )
                  | ~ m1_subset_1(X4,k1_zfmisc_1(X0)) )
              | k7_setfam_1(X0,X1) != X2 ) )
          | ~ m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(X0))) )
      | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1])],[f32,f33])).

fof(f54,plain,(
    ! [X2,X0,X1] :
      ( k7_setfam_1(X0,X1) = X2
      | r2_hidden(k3_subset_1(X0,sK1(X0,X1,X2)),X1)
      | r2_hidden(sK1(X0,X1,X2),X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) ) ),
    inference(cnf_transformation,[],[f34])).

fof(f3,axiom,(
    ! [X0] : k1_xboole_0 = k4_xboole_0(k1_xboole_0,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f39,plain,(
    ! [X0] : k1_xboole_0 = k4_xboole_0(k1_xboole_0,X0) ),
    inference(cnf_transformation,[],[f3])).

fof(f2,axiom,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f38,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f2])).

fof(f16,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f57,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1)) ),
    inference(cnf_transformation,[],[f16])).

fof(f5,axiom,(
    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f41,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1) ),
    inference(cnf_transformation,[],[f5])).

fof(f6,axiom,(
    ! [X0,X1,X2] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f42,plain,(
    ! [X2,X0,X1] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2) ),
    inference(cnf_transformation,[],[f6])).

fof(f7,axiom,(
    ! [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) = k3_enumset1(X0,X0,X1,X2,X3) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f43,plain,(
    ! [X2,X0,X3,X1] : k2_enumset1(X0,X1,X2,X3) = k3_enumset1(X0,X0,X1,X2,X3) ),
    inference(cnf_transformation,[],[f7])).

fof(f8,axiom,(
    ! [X0,X1,X2,X3,X4] : k3_enumset1(X0,X1,X2,X3,X4) = k4_enumset1(X0,X0,X1,X2,X3,X4) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f44,plain,(
    ! [X4,X2,X0,X3,X1] : k3_enumset1(X0,X1,X2,X3,X4) = k4_enumset1(X0,X0,X1,X2,X3,X4) ),
    inference(cnf_transformation,[],[f8])).

fof(f9,axiom,(
    ! [X0,X1,X2,X3,X4,X5] : k4_enumset1(X0,X1,X2,X3,X4,X5) = k5_enumset1(X0,X0,X1,X2,X3,X4,X5) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f45,plain,(
    ! [X4,X2,X0,X5,X3,X1] : k4_enumset1(X0,X1,X2,X3,X4,X5) = k5_enumset1(X0,X0,X1,X2,X3,X4,X5) ),
    inference(cnf_transformation,[],[f9])).

fof(f10,axiom,(
    ! [X0,X1,X2,X3,X4,X5,X6] : k5_enumset1(X0,X1,X2,X3,X4,X5,X6) = k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f46,plain,(
    ! [X6,X4,X2,X0,X5,X3,X1] : k5_enumset1(X0,X1,X2,X3,X4,X5,X6) = k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6) ),
    inference(cnf_transformation,[],[f10])).

fof(f62,plain,(
    ! [X4,X2,X0,X5,X3,X1] : k4_enumset1(X0,X1,X2,X3,X4,X5) = k6_enumset1(X0,X0,X0,X1,X2,X3,X4,X5) ),
    inference(definition_unfolding,[],[f45,f46])).

fof(f63,plain,(
    ! [X4,X2,X0,X3,X1] : k3_enumset1(X0,X1,X2,X3,X4) = k6_enumset1(X0,X0,X0,X0,X1,X2,X3,X4) ),
    inference(definition_unfolding,[],[f44,f62])).

fof(f64,plain,(
    ! [X2,X0,X3,X1] : k2_enumset1(X0,X1,X2,X3) = k6_enumset1(X0,X0,X0,X0,X0,X1,X2,X3) ),
    inference(definition_unfolding,[],[f43,f63])).

fof(f65,plain,(
    ! [X2,X0,X1] : k1_enumset1(X0,X1,X2) = k6_enumset1(X0,X0,X0,X0,X0,X0,X1,X2) ),
    inference(definition_unfolding,[],[f42,f64])).

fof(f66,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1) ),
    inference(definition_unfolding,[],[f41,f65])).

fof(f67,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)) ),
    inference(definition_unfolding,[],[f57,f66])).

fof(f68,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k1_setfam_1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1))) ),
    inference(definition_unfolding,[],[f38,f67])).

fof(f70,plain,(
    ! [X0] : k1_xboole_0 = k5_xboole_0(k1_xboole_0,k1_setfam_1(k6_enumset1(k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,X0))) ),
    inference(definition_unfolding,[],[f39,f68])).

fof(f11,axiom,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,k1_tarski(X1)) = X0
    <=> ~ r2_hidden(X1,X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f29,plain,(
    ! [X0,X1] :
      ( ( k4_xboole_0(X0,k1_tarski(X1)) = X0
        | r2_hidden(X1,X0) )
      & ( ~ r2_hidden(X1,X0)
        | k4_xboole_0(X0,k1_tarski(X1)) != X0 ) ) ),
    inference(nnf_transformation,[],[f11])).

fof(f47,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X1,X0)
      | k4_xboole_0(X0,k1_tarski(X1)) != X0 ) ),
    inference(cnf_transformation,[],[f29])).

fof(f4,axiom,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f40,plain,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    inference(cnf_transformation,[],[f4])).

fof(f69,plain,(
    ! [X0] : k1_tarski(X0) = k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0) ),
    inference(definition_unfolding,[],[f40,f66])).

fof(f72,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X1,X0)
      | k5_xboole_0(X0,k1_setfam_1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1)))) != X0 ) ),
    inference(definition_unfolding,[],[f47,f68,f69])).

fof(f13,axiom,(
    ! [X0] : m1_subset_1(k1_subset_1(X0),k1_zfmisc_1(X0)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f50,plain,(
    ! [X0] : m1_subset_1(k1_subset_1(X0),k1_zfmisc_1(X0)) ),
    inference(cnf_transformation,[],[f13])).

fof(f12,axiom,(
    ! [X0] : k1_xboole_0 = k1_subset_1(X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f49,plain,(
    ! [X0] : k1_xboole_0 = k1_subset_1(X0) ),
    inference(cnf_transformation,[],[f12])).

fof(f73,plain,(
    ! [X0] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0)) ),
    inference(definition_unfolding,[],[f50,f49])).

fof(f18,conjecture,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0)))
     => ~ ( k1_xboole_0 = k7_setfam_1(X0,X1)
          & k1_xboole_0 != X1 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f19,negated_conjecture,(
    ~ ! [X0,X1] :
        ( m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0)))
       => ~ ( k1_xboole_0 = k7_setfam_1(X0,X1)
            & k1_xboole_0 != X1 ) ) ),
    inference(negated_conjecture,[],[f18])).

fof(f25,plain,(
    ? [X0,X1] :
      ( k1_xboole_0 = k7_setfam_1(X0,X1)
      & k1_xboole_0 != X1
      & m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) ) ),
    inference(ennf_transformation,[],[f19])).

fof(f26,plain,(
    ? [X0,X1] :
      ( k1_xboole_0 = k7_setfam_1(X0,X1)
      & k1_xboole_0 != X1
      & m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) ) ),
    inference(flattening,[],[f25])).

fof(f35,plain,
    ( ? [X0,X1] :
        ( k1_xboole_0 = k7_setfam_1(X0,X1)
        & k1_xboole_0 != X1
        & m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) )
   => ( k1_xboole_0 = k7_setfam_1(sK2,sK3)
      & k1_xboole_0 != sK3
      & m1_subset_1(sK3,k1_zfmisc_1(k1_zfmisc_1(sK2))) ) ),
    introduced(choice_axiom,[])).

fof(f36,plain,
    ( k1_xboole_0 = k7_setfam_1(sK2,sK3)
    & k1_xboole_0 != sK3
    & m1_subset_1(sK3,k1_zfmisc_1(k1_zfmisc_1(sK2))) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2,sK3])],[f26,f35])).

fof(f59,plain,(
    m1_subset_1(sK3,k1_zfmisc_1(k1_zfmisc_1(sK2))) ),
    inference(cnf_transformation,[],[f36])).

fof(f15,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0)))
     => k7_setfam_1(X0,k7_setfam_1(X0,X1)) = X1 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f22,plain,(
    ! [X0,X1] :
      ( k7_setfam_1(X0,k7_setfam_1(X0,X1)) = X1
      | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) ) ),
    inference(ennf_transformation,[],[f15])).

fof(f56,plain,(
    ! [X0,X1] :
      ( k7_setfam_1(X0,k7_setfam_1(X0,X1)) = X1
      | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f61,plain,(
    k1_xboole_0 = k7_setfam_1(sK2,sK3) ),
    inference(cnf_transformation,[],[f36])).

fof(f60,plain,(
    k1_xboole_0 != sK3 ),
    inference(cnf_transformation,[],[f36])).

cnf(c_6,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k1_zfmisc_1(X1)))
    | ~ m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(X1)))
    | r2_hidden(sK1(X1,X2,X0),X0)
    | r2_hidden(k3_subset_1(X1,sK1(X1,X2,X0)),X2)
    | k7_setfam_1(X1,X2) = X0 ),
    inference(cnf_transformation,[],[f54])).

cnf(c_528,plain,
    ( k7_setfam_1(X0,X1) = X2
    | m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(X0))) != iProver_top
    | m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) != iProver_top
    | r2_hidden(sK1(X0,X1,X2),X2) = iProver_top
    | r2_hidden(k3_subset_1(X0,sK1(X0,X1,X2)),X1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_6])).

cnf(c_1,plain,
    ( k5_xboole_0(k1_xboole_0,k1_setfam_1(k6_enumset1(k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,X0))) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f70])).

cnf(c_3,plain,
    ( ~ r2_hidden(X0,X1)
    | k5_xboole_0(X1,k1_setfam_1(k6_enumset1(X1,X1,X1,X1,X1,X1,X1,k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0)))) != X1 ),
    inference(cnf_transformation,[],[f72])).

cnf(c_531,plain,
    ( k5_xboole_0(X0,k1_setfam_1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1)))) != X0
    | r2_hidden(X1,X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3])).

cnf(c_838,plain,
    ( r2_hidden(X0,k1_xboole_0) != iProver_top ),
    inference(superposition,[status(thm)],[c_1,c_531])).

cnf(c_1630,plain,
    ( k7_setfam_1(X0,k1_xboole_0) = X1
    | m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) != iProver_top
    | m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_zfmisc_1(X0))) != iProver_top
    | r2_hidden(sK1(X0,k1_xboole_0,X1),X1) = iProver_top ),
    inference(superposition,[status(thm)],[c_528,c_838])).

cnf(c_4,plain,
    ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0)) ),
    inference(cnf_transformation,[],[f73])).

cnf(c_646,plain,
    ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_zfmisc_1(X0))) ),
    inference(instantiation,[status(thm)],[c_4])).

cnf(c_649,plain,
    ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_zfmisc_1(X0))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_646])).

cnf(c_1874,plain,
    ( m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) != iProver_top
    | k7_setfam_1(X0,k1_xboole_0) = X1
    | r2_hidden(sK1(X0,k1_xboole_0,X1),X1) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_1630,c_649])).

cnf(c_1875,plain,
    ( k7_setfam_1(X0,k1_xboole_0) = X1
    | m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) != iProver_top
    | r2_hidden(sK1(X0,k1_xboole_0,X1),X1) = iProver_top ),
    inference(renaming,[status(thm)],[c_1874])).

cnf(c_1882,plain,
    ( k7_setfam_1(X0,k1_xboole_0) = k1_xboole_0
    | m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_zfmisc_1(X0))) != iProver_top ),
    inference(superposition,[status(thm)],[c_1875,c_838])).

cnf(c_2490,plain,
    ( k7_setfam_1(X0,k1_xboole_0) = k1_xboole_0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_1882,c_649])).

cnf(c_14,negated_conjecture,
    ( m1_subset_1(sK3,k1_zfmisc_1(k1_zfmisc_1(sK2))) ),
    inference(cnf_transformation,[],[f59])).

cnf(c_522,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(k1_zfmisc_1(sK2))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_14])).

cnf(c_10,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k1_zfmisc_1(X1)))
    | k7_setfam_1(X1,k7_setfam_1(X1,X0)) = X0 ),
    inference(cnf_transformation,[],[f56])).

cnf(c_524,plain,
    ( k7_setfam_1(X0,k7_setfam_1(X0,X1)) = X1
    | m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_10])).

cnf(c_733,plain,
    ( k7_setfam_1(sK2,k7_setfam_1(sK2,sK3)) = sK3 ),
    inference(superposition,[status(thm)],[c_522,c_524])).

cnf(c_12,negated_conjecture,
    ( k1_xboole_0 = k7_setfam_1(sK2,sK3) ),
    inference(cnf_transformation,[],[f61])).

cnf(c_735,plain,
    ( k7_setfam_1(sK2,k1_xboole_0) = sK3 ),
    inference(light_normalisation,[status(thm)],[c_733,c_12])).

cnf(c_2497,plain,
    ( sK3 = k1_xboole_0 ),
    inference(demodulation,[status(thm)],[c_2490,c_735])).

cnf(c_186,plain,
    ( X0 != X1
    | X2 != X1
    | X2 = X0 ),
    theory(equality)).

cnf(c_661,plain,
    ( sK3 != X0
    | k1_xboole_0 != X0
    | k1_xboole_0 = sK3 ),
    inference(instantiation,[status(thm)],[c_186])).

cnf(c_662,plain,
    ( sK3 != k1_xboole_0
    | k1_xboole_0 = sK3
    | k1_xboole_0 != k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_661])).

cnf(c_185,plain,
    ( X0 = X0 ),
    theory(equality)).

cnf(c_204,plain,
    ( k1_xboole_0 = k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_185])).

cnf(c_13,negated_conjecture,
    ( k1_xboole_0 != sK3 ),
    inference(cnf_transformation,[],[f60])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_2497,c_662,c_204,c_13])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.10/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.10/0.13  % Command    : iproveropt_run.sh %d %s
% 0.13/0.34  % Computer   : n023.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 12:38:06 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running in FOF mode
% 1.88/1.02  % SZS status Started for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.88/1.02  
% 1.88/1.02  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 1.88/1.02  
% 1.88/1.02  ------  iProver source info
% 1.88/1.02  
% 1.88/1.02  git: date: 2020-06-30 10:37:57 +0100
% 1.88/1.02  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 1.88/1.02  git: non_committed_changes: false
% 1.88/1.02  git: last_make_outside_of_git: false
% 1.88/1.02  
% 1.88/1.02  ------ 
% 1.88/1.02  
% 1.88/1.02  ------ Input Options
% 1.88/1.02  
% 1.88/1.02  --out_options                           all
% 1.88/1.02  --tptp_safe_out                         true
% 1.88/1.02  --problem_path                          ""
% 1.88/1.02  --include_path                          ""
% 1.88/1.02  --clausifier                            res/vclausify_rel
% 1.88/1.02  --clausifier_options                    --mode clausify
% 1.88/1.02  --stdin                                 false
% 1.88/1.02  --stats_out                             all
% 1.88/1.02  
% 1.88/1.02  ------ General Options
% 1.88/1.02  
% 1.88/1.02  --fof                                   false
% 1.88/1.02  --time_out_real                         305.
% 1.88/1.02  --time_out_virtual                      -1.
% 1.88/1.02  --symbol_type_check                     false
% 1.88/1.02  --clausify_out                          false
% 1.88/1.02  --sig_cnt_out                           false
% 1.88/1.02  --trig_cnt_out                          false
% 1.88/1.02  --trig_cnt_out_tolerance                1.
% 1.88/1.02  --trig_cnt_out_sk_spl                   false
% 1.88/1.02  --abstr_cl_out                          false
% 1.88/1.02  
% 1.88/1.02  ------ Global Options
% 1.88/1.02  
% 1.88/1.02  --schedule                              default
% 1.88/1.02  --add_important_lit                     false
% 1.88/1.02  --prop_solver_per_cl                    1000
% 1.88/1.02  --min_unsat_core                        false
% 1.88/1.02  --soft_assumptions                      false
% 1.88/1.02  --soft_lemma_size                       3
% 1.88/1.02  --prop_impl_unit_size                   0
% 1.88/1.02  --prop_impl_unit                        []
% 1.88/1.02  --share_sel_clauses                     true
% 1.88/1.02  --reset_solvers                         false
% 1.88/1.02  --bc_imp_inh                            [conj_cone]
% 1.88/1.02  --conj_cone_tolerance                   3.
% 1.88/1.02  --extra_neg_conj                        none
% 1.88/1.02  --large_theory_mode                     true
% 1.88/1.02  --prolific_symb_bound                   200
% 1.88/1.02  --lt_threshold                          2000
% 1.88/1.02  --clause_weak_htbl                      true
% 1.88/1.02  --gc_record_bc_elim                     false
% 1.88/1.02  
% 1.88/1.02  ------ Preprocessing Options
% 1.88/1.02  
% 1.88/1.02  --preprocessing_flag                    true
% 1.88/1.02  --time_out_prep_mult                    0.1
% 1.88/1.02  --splitting_mode                        input
% 1.88/1.02  --splitting_grd                         true
% 1.88/1.02  --splitting_cvd                         false
% 1.88/1.02  --splitting_cvd_svl                     false
% 1.88/1.02  --splitting_nvd                         32
% 1.88/1.02  --sub_typing                            true
% 1.88/1.02  --prep_gs_sim                           true
% 1.88/1.02  --prep_unflatten                        true
% 1.88/1.02  --prep_res_sim                          true
% 1.88/1.02  --prep_upred                            true
% 1.88/1.02  --prep_sem_filter                       exhaustive
% 1.88/1.02  --prep_sem_filter_out                   false
% 1.88/1.02  --pred_elim                             true
% 1.88/1.02  --res_sim_input                         true
% 1.88/1.02  --eq_ax_congr_red                       true
% 1.88/1.02  --pure_diseq_elim                       true
% 1.88/1.02  --brand_transform                       false
% 1.88/1.02  --non_eq_to_eq                          false
% 1.88/1.02  --prep_def_merge                        true
% 1.88/1.02  --prep_def_merge_prop_impl              false
% 1.88/1.02  --prep_def_merge_mbd                    true
% 1.88/1.02  --prep_def_merge_tr_red                 false
% 1.88/1.02  --prep_def_merge_tr_cl                  false
% 1.88/1.02  --smt_preprocessing                     true
% 1.88/1.02  --smt_ac_axioms                         fast
% 1.88/1.02  --preprocessed_out                      false
% 1.88/1.02  --preprocessed_stats                    false
% 1.88/1.02  
% 1.88/1.02  ------ Abstraction refinement Options
% 1.88/1.02  
% 1.88/1.02  --abstr_ref                             []
% 1.88/1.02  --abstr_ref_prep                        false
% 1.88/1.02  --abstr_ref_until_sat                   false
% 1.88/1.02  --abstr_ref_sig_restrict                funpre
% 1.88/1.02  --abstr_ref_af_restrict_to_split_sk     false
% 1.88/1.02  --abstr_ref_under                       []
% 1.88/1.02  
% 1.88/1.02  ------ SAT Options
% 1.88/1.02  
% 1.88/1.02  --sat_mode                              false
% 1.88/1.02  --sat_fm_restart_options                ""
% 1.88/1.02  --sat_gr_def                            false
% 1.88/1.02  --sat_epr_types                         true
% 1.88/1.02  --sat_non_cyclic_types                  false
% 1.88/1.02  --sat_finite_models                     false
% 1.88/1.02  --sat_fm_lemmas                         false
% 1.88/1.02  --sat_fm_prep                           false
% 1.88/1.02  --sat_fm_uc_incr                        true
% 1.88/1.02  --sat_out_model                         small
% 1.88/1.02  --sat_out_clauses                       false
% 1.88/1.02  
% 1.88/1.02  ------ QBF Options
% 1.88/1.02  
% 1.88/1.02  --qbf_mode                              false
% 1.88/1.02  --qbf_elim_univ                         false
% 1.88/1.02  --qbf_dom_inst                          none
% 1.88/1.02  --qbf_dom_pre_inst                      false
% 1.88/1.02  --qbf_sk_in                             false
% 1.88/1.02  --qbf_pred_elim                         true
% 1.88/1.02  --qbf_split                             512
% 1.88/1.02  
% 1.88/1.02  ------ BMC1 Options
% 1.88/1.02  
% 1.88/1.02  --bmc1_incremental                      false
% 1.88/1.02  --bmc1_axioms                           reachable_all
% 1.88/1.02  --bmc1_min_bound                        0
% 1.88/1.02  --bmc1_max_bound                        -1
% 1.88/1.02  --bmc1_max_bound_default                -1
% 1.88/1.02  --bmc1_symbol_reachability              true
% 1.88/1.02  --bmc1_property_lemmas                  false
% 1.88/1.02  --bmc1_k_induction                      false
% 1.88/1.02  --bmc1_non_equiv_states                 false
% 1.88/1.02  --bmc1_deadlock                         false
% 1.88/1.02  --bmc1_ucm                              false
% 1.88/1.02  --bmc1_add_unsat_core                   none
% 1.88/1.02  --bmc1_unsat_core_children              false
% 1.88/1.02  --bmc1_unsat_core_extrapolate_axioms    false
% 1.88/1.02  --bmc1_out_stat                         full
% 1.88/1.02  --bmc1_ground_init                      false
% 1.88/1.02  --bmc1_pre_inst_next_state              false
% 1.88/1.02  --bmc1_pre_inst_state                   false
% 1.88/1.02  --bmc1_pre_inst_reach_state             false
% 1.88/1.02  --bmc1_out_unsat_core                   false
% 1.88/1.02  --bmc1_aig_witness_out                  false
% 1.88/1.02  --bmc1_verbose                          false
% 1.88/1.02  --bmc1_dump_clauses_tptp                false
% 1.88/1.02  --bmc1_dump_unsat_core_tptp             false
% 1.88/1.02  --bmc1_dump_file                        -
% 1.88/1.02  --bmc1_ucm_expand_uc_limit              128
% 1.88/1.02  --bmc1_ucm_n_expand_iterations          6
% 1.88/1.02  --bmc1_ucm_extend_mode                  1
% 1.88/1.02  --bmc1_ucm_init_mode                    2
% 1.88/1.02  --bmc1_ucm_cone_mode                    none
% 1.88/1.02  --bmc1_ucm_reduced_relation_type        0
% 1.88/1.02  --bmc1_ucm_relax_model                  4
% 1.88/1.02  --bmc1_ucm_full_tr_after_sat            true
% 1.88/1.02  --bmc1_ucm_expand_neg_assumptions       false
% 1.88/1.02  --bmc1_ucm_layered_model                none
% 1.88/1.02  --bmc1_ucm_max_lemma_size               10
% 1.88/1.02  
% 1.88/1.02  ------ AIG Options
% 1.88/1.02  
% 1.88/1.02  --aig_mode                              false
% 1.88/1.02  
% 1.88/1.02  ------ Instantiation Options
% 1.88/1.02  
% 1.88/1.02  --instantiation_flag                    true
% 1.88/1.02  --inst_sos_flag                         false
% 1.88/1.02  --inst_sos_phase                        true
% 1.88/1.02  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 1.88/1.02  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 1.88/1.02  --inst_lit_sel_side                     num_symb
% 1.88/1.02  --inst_solver_per_active                1400
% 1.88/1.02  --inst_solver_calls_frac                1.
% 1.88/1.02  --inst_passive_queue_type               priority_queues
% 1.88/1.02  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 1.88/1.02  --inst_passive_queues_freq              [25;2]
% 1.88/1.02  --inst_dismatching                      true
% 1.88/1.02  --inst_eager_unprocessed_to_passive     true
% 1.88/1.02  --inst_prop_sim_given                   true
% 1.88/1.02  --inst_prop_sim_new                     false
% 1.88/1.02  --inst_subs_new                         false
% 1.88/1.02  --inst_eq_res_simp                      false
% 1.88/1.02  --inst_subs_given                       false
% 1.88/1.02  --inst_orphan_elimination               true
% 1.88/1.02  --inst_learning_loop_flag               true
% 1.88/1.02  --inst_learning_start                   3000
% 1.88/1.02  --inst_learning_factor                  2
% 1.88/1.02  --inst_start_prop_sim_after_learn       3
% 1.88/1.02  --inst_sel_renew                        solver
% 1.88/1.02  --inst_lit_activity_flag                true
% 1.88/1.02  --inst_restr_to_given                   false
% 1.88/1.02  --inst_activity_threshold               500
% 1.88/1.02  --inst_out_proof                        true
% 1.88/1.02  
% 1.88/1.02  ------ Resolution Options
% 1.88/1.02  
% 1.88/1.02  --resolution_flag                       true
% 1.88/1.02  --res_lit_sel                           adaptive
% 1.88/1.02  --res_lit_sel_side                      none
% 1.88/1.02  --res_ordering                          kbo
% 1.88/1.02  --res_to_prop_solver                    active
% 1.88/1.02  --res_prop_simpl_new                    false
% 1.88/1.02  --res_prop_simpl_given                  true
% 1.88/1.02  --res_passive_queue_type                priority_queues
% 1.88/1.02  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 1.88/1.02  --res_passive_queues_freq               [15;5]
% 1.88/1.02  --res_forward_subs                      full
% 1.88/1.02  --res_backward_subs                     full
% 1.88/1.02  --res_forward_subs_resolution           true
% 1.88/1.02  --res_backward_subs_resolution          true
% 1.88/1.02  --res_orphan_elimination                true
% 1.88/1.02  --res_time_limit                        2.
% 1.88/1.02  --res_out_proof                         true
% 1.88/1.02  
% 1.88/1.02  ------ Superposition Options
% 1.88/1.02  
% 1.88/1.02  --superposition_flag                    true
% 1.88/1.02  --sup_passive_queue_type                priority_queues
% 1.88/1.02  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 1.88/1.02  --sup_passive_queues_freq               [8;1;4]
% 1.88/1.02  --demod_completeness_check              fast
% 1.88/1.02  --demod_use_ground                      true
% 1.88/1.02  --sup_to_prop_solver                    passive
% 1.88/1.02  --sup_prop_simpl_new                    true
% 1.88/1.02  --sup_prop_simpl_given                  true
% 1.88/1.02  --sup_fun_splitting                     false
% 1.88/1.02  --sup_smt_interval                      50000
% 1.88/1.02  
% 1.88/1.02  ------ Superposition Simplification Setup
% 1.88/1.02  
% 1.88/1.02  --sup_indices_passive                   []
% 1.88/1.02  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 1.88/1.02  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 1.88/1.02  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 1.88/1.02  --sup_full_triv                         [TrivRules;PropSubs]
% 1.88/1.02  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 1.88/1.02  --sup_full_bw                           [BwDemod]
% 1.88/1.02  --sup_immed_triv                        [TrivRules]
% 1.88/1.02  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 1.88/1.02  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 1.88/1.02  --sup_immed_bw_main                     []
% 1.88/1.02  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 1.88/1.02  --sup_input_triv                        [Unflattening;TrivRules]
% 1.88/1.02  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 1.88/1.02  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 1.88/1.02  
% 1.88/1.02  ------ Combination Options
% 1.88/1.02  
% 1.88/1.02  --comb_res_mult                         3
% 1.88/1.02  --comb_sup_mult                         2
% 1.88/1.02  --comb_inst_mult                        10
% 1.88/1.02  
% 1.88/1.02  ------ Debug Options
% 1.88/1.02  
% 1.88/1.02  --dbg_backtrace                         false
% 1.88/1.02  --dbg_dump_prop_clauses                 false
% 1.88/1.02  --dbg_dump_prop_clauses_file            -
% 1.88/1.02  --dbg_out_stat                          false
% 1.88/1.02  ------ Parsing...
% 1.88/1.02  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 1.88/1.02  
% 1.88/1.02  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe_e 
% 1.88/1.02  
% 1.88/1.02  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 1.88/1.02  
% 1.88/1.02  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 1.88/1.02  ------ Proving...
% 1.88/1.02  ------ Problem Properties 
% 1.88/1.02  
% 1.88/1.02  
% 1.88/1.02  clauses                                 15
% 1.88/1.02  conjectures                             3
% 1.88/1.02  EPR                                     1
% 1.88/1.02  Horn                                    11
% 1.88/1.02  unary                                   5
% 1.88/1.02  binary                                  4
% 1.88/1.02  lits                                    40
% 1.88/1.02  lits eq                                 10
% 1.88/1.02  fd_pure                                 0
% 1.88/1.02  fd_pseudo                               0
% 1.88/1.02  fd_cond                                 1
% 1.88/1.02  fd_pseudo_cond                          3
% 1.88/1.02  AC symbols                              0
% 1.88/1.02  
% 1.88/1.02  ------ Schedule dynamic 5 is on 
% 1.88/1.02  
% 1.88/1.02  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" Time Limit: 10.
% 1.88/1.02  
% 1.88/1.02  
% 1.88/1.02  ------ 
% 1.88/1.02  Current options:
% 1.88/1.02  ------ 
% 1.88/1.02  
% 1.88/1.02  ------ Input Options
% 1.88/1.02  
% 1.88/1.02  --out_options                           all
% 1.88/1.02  --tptp_safe_out                         true
% 1.88/1.02  --problem_path                          ""
% 1.88/1.02  --include_path                          ""
% 1.88/1.02  --clausifier                            res/vclausify_rel
% 1.88/1.02  --clausifier_options                    --mode clausify
% 1.88/1.02  --stdin                                 false
% 1.88/1.02  --stats_out                             all
% 1.88/1.02  
% 1.88/1.02  ------ General Options
% 1.88/1.02  
% 1.88/1.02  --fof                                   false
% 1.88/1.02  --time_out_real                         305.
% 1.88/1.02  --time_out_virtual                      -1.
% 1.88/1.02  --symbol_type_check                     false
% 1.88/1.02  --clausify_out                          false
% 1.88/1.02  --sig_cnt_out                           false
% 1.88/1.02  --trig_cnt_out                          false
% 1.88/1.02  --trig_cnt_out_tolerance                1.
% 1.88/1.02  --trig_cnt_out_sk_spl                   false
% 1.88/1.02  --abstr_cl_out                          false
% 1.88/1.02  
% 1.88/1.02  ------ Global Options
% 1.88/1.02  
% 1.88/1.02  --schedule                              default
% 1.88/1.02  --add_important_lit                     false
% 1.88/1.02  --prop_solver_per_cl                    1000
% 1.88/1.02  --min_unsat_core                        false
% 1.88/1.02  --soft_assumptions                      false
% 1.88/1.02  --soft_lemma_size                       3
% 1.88/1.02  --prop_impl_unit_size                   0
% 1.88/1.02  --prop_impl_unit                        []
% 1.88/1.02  --share_sel_clauses                     true
% 1.88/1.02  --reset_solvers                         false
% 1.88/1.02  --bc_imp_inh                            [conj_cone]
% 1.88/1.02  --conj_cone_tolerance                   3.
% 1.88/1.02  --extra_neg_conj                        none
% 1.88/1.02  --large_theory_mode                     true
% 1.88/1.02  --prolific_symb_bound                   200
% 1.88/1.02  --lt_threshold                          2000
% 1.88/1.02  --clause_weak_htbl                      true
% 1.88/1.02  --gc_record_bc_elim                     false
% 1.88/1.02  
% 1.88/1.02  ------ Preprocessing Options
% 1.88/1.02  
% 1.88/1.02  --preprocessing_flag                    true
% 1.88/1.02  --time_out_prep_mult                    0.1
% 1.88/1.02  --splitting_mode                        input
% 1.88/1.02  --splitting_grd                         true
% 1.88/1.02  --splitting_cvd                         false
% 1.88/1.02  --splitting_cvd_svl                     false
% 1.88/1.02  --splitting_nvd                         32
% 1.88/1.02  --sub_typing                            true
% 1.88/1.02  --prep_gs_sim                           true
% 1.88/1.02  --prep_unflatten                        true
% 1.88/1.02  --prep_res_sim                          true
% 1.88/1.02  --prep_upred                            true
% 1.88/1.02  --prep_sem_filter                       exhaustive
% 1.88/1.02  --prep_sem_filter_out                   false
% 1.88/1.02  --pred_elim                             true
% 1.88/1.02  --res_sim_input                         true
% 1.88/1.02  --eq_ax_congr_red                       true
% 1.88/1.02  --pure_diseq_elim                       true
% 1.88/1.02  --brand_transform                       false
% 1.88/1.02  --non_eq_to_eq                          false
% 1.88/1.02  --prep_def_merge                        true
% 1.88/1.02  --prep_def_merge_prop_impl              false
% 1.88/1.02  --prep_def_merge_mbd                    true
% 1.88/1.02  --prep_def_merge_tr_red                 false
% 1.88/1.02  --prep_def_merge_tr_cl                  false
% 1.88/1.02  --smt_preprocessing                     true
% 1.88/1.02  --smt_ac_axioms                         fast
% 1.88/1.02  --preprocessed_out                      false
% 1.88/1.02  --preprocessed_stats                    false
% 1.88/1.02  
% 1.88/1.02  ------ Abstraction refinement Options
% 1.88/1.02  
% 1.88/1.02  --abstr_ref                             []
% 1.88/1.02  --abstr_ref_prep                        false
% 1.88/1.02  --abstr_ref_until_sat                   false
% 1.88/1.02  --abstr_ref_sig_restrict                funpre
% 1.88/1.02  --abstr_ref_af_restrict_to_split_sk     false
% 1.88/1.02  --abstr_ref_under                       []
% 1.88/1.02  
% 1.88/1.02  ------ SAT Options
% 1.88/1.02  
% 1.88/1.02  --sat_mode                              false
% 1.88/1.02  --sat_fm_restart_options                ""
% 1.88/1.02  --sat_gr_def                            false
% 1.88/1.02  --sat_epr_types                         true
% 1.88/1.02  --sat_non_cyclic_types                  false
% 1.88/1.02  --sat_finite_models                     false
% 1.88/1.02  --sat_fm_lemmas                         false
% 1.88/1.02  --sat_fm_prep                           false
% 1.88/1.02  --sat_fm_uc_incr                        true
% 1.88/1.02  --sat_out_model                         small
% 1.88/1.02  --sat_out_clauses                       false
% 1.88/1.02  
% 1.88/1.02  ------ QBF Options
% 1.88/1.02  
% 1.88/1.02  --qbf_mode                              false
% 1.88/1.02  --qbf_elim_univ                         false
% 1.88/1.02  --qbf_dom_inst                          none
% 1.88/1.02  --qbf_dom_pre_inst                      false
% 1.88/1.02  --qbf_sk_in                             false
% 1.88/1.02  --qbf_pred_elim                         true
% 1.88/1.02  --qbf_split                             512
% 1.88/1.02  
% 1.88/1.02  ------ BMC1 Options
% 1.88/1.02  
% 1.88/1.02  --bmc1_incremental                      false
% 1.88/1.02  --bmc1_axioms                           reachable_all
% 1.88/1.02  --bmc1_min_bound                        0
% 1.88/1.02  --bmc1_max_bound                        -1
% 1.88/1.02  --bmc1_max_bound_default                -1
% 1.88/1.02  --bmc1_symbol_reachability              true
% 1.88/1.02  --bmc1_property_lemmas                  false
% 1.88/1.02  --bmc1_k_induction                      false
% 1.88/1.02  --bmc1_non_equiv_states                 false
% 1.88/1.02  --bmc1_deadlock                         false
% 1.88/1.02  --bmc1_ucm                              false
% 1.88/1.02  --bmc1_add_unsat_core                   none
% 1.88/1.02  --bmc1_unsat_core_children              false
% 1.88/1.02  --bmc1_unsat_core_extrapolate_axioms    false
% 1.88/1.02  --bmc1_out_stat                         full
% 1.88/1.02  --bmc1_ground_init                      false
% 1.88/1.02  --bmc1_pre_inst_next_state              false
% 1.88/1.02  --bmc1_pre_inst_state                   false
% 1.88/1.02  --bmc1_pre_inst_reach_state             false
% 1.88/1.02  --bmc1_out_unsat_core                   false
% 1.88/1.02  --bmc1_aig_witness_out                  false
% 1.88/1.02  --bmc1_verbose                          false
% 1.88/1.02  --bmc1_dump_clauses_tptp                false
% 1.88/1.02  --bmc1_dump_unsat_core_tptp             false
% 1.88/1.02  --bmc1_dump_file                        -
% 1.88/1.02  --bmc1_ucm_expand_uc_limit              128
% 1.88/1.02  --bmc1_ucm_n_expand_iterations          6
% 1.88/1.02  --bmc1_ucm_extend_mode                  1
% 1.88/1.02  --bmc1_ucm_init_mode                    2
% 1.88/1.02  --bmc1_ucm_cone_mode                    none
% 1.88/1.02  --bmc1_ucm_reduced_relation_type        0
% 1.88/1.02  --bmc1_ucm_relax_model                  4
% 1.88/1.02  --bmc1_ucm_full_tr_after_sat            true
% 1.88/1.02  --bmc1_ucm_expand_neg_assumptions       false
% 1.88/1.02  --bmc1_ucm_layered_model                none
% 1.88/1.02  --bmc1_ucm_max_lemma_size               10
% 1.88/1.02  
% 1.88/1.02  ------ AIG Options
% 1.88/1.02  
% 1.88/1.02  --aig_mode                              false
% 1.88/1.02  
% 1.88/1.02  ------ Instantiation Options
% 1.88/1.02  
% 1.88/1.02  --instantiation_flag                    true
% 1.88/1.02  --inst_sos_flag                         false
% 1.88/1.02  --inst_sos_phase                        true
% 1.88/1.02  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 1.88/1.02  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 1.88/1.02  --inst_lit_sel_side                     none
% 1.88/1.02  --inst_solver_per_active                1400
% 1.88/1.02  --inst_solver_calls_frac                1.
% 1.88/1.02  --inst_passive_queue_type               priority_queues
% 1.88/1.02  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 1.88/1.02  --inst_passive_queues_freq              [25;2]
% 1.88/1.02  --inst_dismatching                      true
% 1.88/1.02  --inst_eager_unprocessed_to_passive     true
% 1.88/1.02  --inst_prop_sim_given                   true
% 1.88/1.02  --inst_prop_sim_new                     false
% 1.88/1.02  --inst_subs_new                         false
% 1.88/1.02  --inst_eq_res_simp                      false
% 1.88/1.02  --inst_subs_given                       false
% 1.88/1.02  --inst_orphan_elimination               true
% 1.88/1.02  --inst_learning_loop_flag               true
% 1.88/1.02  --inst_learning_start                   3000
% 1.88/1.02  --inst_learning_factor                  2
% 1.88/1.02  --inst_start_prop_sim_after_learn       3
% 1.88/1.02  --inst_sel_renew                        solver
% 1.88/1.02  --inst_lit_activity_flag                true
% 1.88/1.02  --inst_restr_to_given                   false
% 1.88/1.02  --inst_activity_threshold               500
% 1.88/1.02  --inst_out_proof                        true
% 1.88/1.02  
% 1.88/1.02  ------ Resolution Options
% 1.88/1.02  
% 1.88/1.02  --resolution_flag                       false
% 1.88/1.02  --res_lit_sel                           adaptive
% 1.88/1.02  --res_lit_sel_side                      none
% 1.88/1.02  --res_ordering                          kbo
% 1.88/1.02  --res_to_prop_solver                    active
% 1.88/1.02  --res_prop_simpl_new                    false
% 1.88/1.02  --res_prop_simpl_given                  true
% 1.88/1.02  --res_passive_queue_type                priority_queues
% 1.88/1.02  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 1.88/1.02  --res_passive_queues_freq               [15;5]
% 1.88/1.02  --res_forward_subs                      full
% 1.88/1.02  --res_backward_subs                     full
% 1.88/1.02  --res_forward_subs_resolution           true
% 1.88/1.02  --res_backward_subs_resolution          true
% 1.88/1.02  --res_orphan_elimination                true
% 1.88/1.02  --res_time_limit                        2.
% 1.88/1.02  --res_out_proof                         true
% 1.88/1.02  
% 1.88/1.02  ------ Superposition Options
% 1.88/1.02  
% 1.88/1.02  --superposition_flag                    true
% 1.88/1.02  --sup_passive_queue_type                priority_queues
% 1.88/1.02  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 1.88/1.02  --sup_passive_queues_freq               [8;1;4]
% 1.88/1.02  --demod_completeness_check              fast
% 1.88/1.02  --demod_use_ground                      true
% 1.88/1.02  --sup_to_prop_solver                    passive
% 1.88/1.02  --sup_prop_simpl_new                    true
% 1.88/1.02  --sup_prop_simpl_given                  true
% 1.88/1.02  --sup_fun_splitting                     false
% 1.88/1.02  --sup_smt_interval                      50000
% 1.88/1.02  
% 1.88/1.02  ------ Superposition Simplification Setup
% 1.88/1.02  
% 1.88/1.02  --sup_indices_passive                   []
% 1.88/1.02  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 1.88/1.02  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 1.88/1.02  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 1.88/1.02  --sup_full_triv                         [TrivRules;PropSubs]
% 1.88/1.02  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 1.88/1.02  --sup_full_bw                           [BwDemod]
% 1.88/1.02  --sup_immed_triv                        [TrivRules]
% 1.88/1.02  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 1.88/1.02  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 1.88/1.02  --sup_immed_bw_main                     []
% 1.88/1.02  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 1.88/1.02  --sup_input_triv                        [Unflattening;TrivRules]
% 1.88/1.02  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 1.88/1.02  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 1.88/1.02  
% 1.88/1.02  ------ Combination Options
% 1.88/1.02  
% 1.88/1.02  --comb_res_mult                         3
% 1.88/1.02  --comb_sup_mult                         2
% 1.88/1.02  --comb_inst_mult                        10
% 1.88/1.02  
% 1.88/1.02  ------ Debug Options
% 1.88/1.02  
% 1.88/1.02  --dbg_backtrace                         false
% 1.88/1.02  --dbg_dump_prop_clauses                 false
% 1.88/1.02  --dbg_dump_prop_clauses_file            -
% 1.88/1.02  --dbg_out_stat                          false
% 1.88/1.02  
% 1.88/1.02  
% 1.88/1.02  
% 1.88/1.02  
% 1.88/1.02  ------ Proving...
% 1.88/1.02  
% 1.88/1.02  
% 1.88/1.02  % SZS status Theorem for theBenchmark.p
% 1.88/1.02  
% 1.88/1.02  % SZS output start CNFRefutation for theBenchmark.p
% 1.88/1.02  
% 1.88/1.02  fof(f14,axiom,(
% 1.88/1.02    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(X0))) => (k7_setfam_1(X0,X1) = X2 <=> ! [X3] : (m1_subset_1(X3,k1_zfmisc_1(X0)) => (r2_hidden(X3,X2) <=> r2_hidden(k3_subset_1(X0,X3),X1))))))),
% 1.88/1.03    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 1.88/1.03  
% 1.88/1.03  fof(f21,plain,(
% 1.88/1.03    ! [X0,X1] : (! [X2] : ((k7_setfam_1(X0,X1) = X2 <=> ! [X3] : ((r2_hidden(X3,X2) <=> r2_hidden(k3_subset_1(X0,X3),X1)) | ~m1_subset_1(X3,k1_zfmisc_1(X0)))) | ~m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(X0)))) | ~m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))))),
% 1.88/1.03    inference(ennf_transformation,[],[f14])).
% 1.88/1.03  
% 1.88/1.03  fof(f30,plain,(
% 1.88/1.03    ! [X0,X1] : (! [X2] : (((k7_setfam_1(X0,X1) = X2 | ? [X3] : (((~r2_hidden(k3_subset_1(X0,X3),X1) | ~r2_hidden(X3,X2)) & (r2_hidden(k3_subset_1(X0,X3),X1) | r2_hidden(X3,X2))) & m1_subset_1(X3,k1_zfmisc_1(X0)))) & (! [X3] : (((r2_hidden(X3,X2) | ~r2_hidden(k3_subset_1(X0,X3),X1)) & (r2_hidden(k3_subset_1(X0,X3),X1) | ~r2_hidden(X3,X2))) | ~m1_subset_1(X3,k1_zfmisc_1(X0))) | k7_setfam_1(X0,X1) != X2)) | ~m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(X0)))) | ~m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))))),
% 1.88/1.03    inference(nnf_transformation,[],[f21])).
% 1.88/1.03  
% 1.88/1.03  fof(f31,plain,(
% 1.88/1.03    ! [X0,X1] : (! [X2] : (((k7_setfam_1(X0,X1) = X2 | ? [X3] : ((~r2_hidden(k3_subset_1(X0,X3),X1) | ~r2_hidden(X3,X2)) & (r2_hidden(k3_subset_1(X0,X3),X1) | r2_hidden(X3,X2)) & m1_subset_1(X3,k1_zfmisc_1(X0)))) & (! [X3] : (((r2_hidden(X3,X2) | ~r2_hidden(k3_subset_1(X0,X3),X1)) & (r2_hidden(k3_subset_1(X0,X3),X1) | ~r2_hidden(X3,X2))) | ~m1_subset_1(X3,k1_zfmisc_1(X0))) | k7_setfam_1(X0,X1) != X2)) | ~m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(X0)))) | ~m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))))),
% 1.88/1.03    inference(flattening,[],[f30])).
% 1.88/1.03  
% 1.88/1.03  fof(f32,plain,(
% 1.88/1.03    ! [X0,X1] : (! [X2] : (((k7_setfam_1(X0,X1) = X2 | ? [X3] : ((~r2_hidden(k3_subset_1(X0,X3),X1) | ~r2_hidden(X3,X2)) & (r2_hidden(k3_subset_1(X0,X3),X1) | r2_hidden(X3,X2)) & m1_subset_1(X3,k1_zfmisc_1(X0)))) & (! [X4] : (((r2_hidden(X4,X2) | ~r2_hidden(k3_subset_1(X0,X4),X1)) & (r2_hidden(k3_subset_1(X0,X4),X1) | ~r2_hidden(X4,X2))) | ~m1_subset_1(X4,k1_zfmisc_1(X0))) | k7_setfam_1(X0,X1) != X2)) | ~m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(X0)))) | ~m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))))),
% 1.88/1.03    inference(rectify,[],[f31])).
% 1.88/1.03  
% 1.88/1.03  fof(f33,plain,(
% 1.88/1.03    ! [X2,X1,X0] : (? [X3] : ((~r2_hidden(k3_subset_1(X0,X3),X1) | ~r2_hidden(X3,X2)) & (r2_hidden(k3_subset_1(X0,X3),X1) | r2_hidden(X3,X2)) & m1_subset_1(X3,k1_zfmisc_1(X0))) => ((~r2_hidden(k3_subset_1(X0,sK1(X0,X1,X2)),X1) | ~r2_hidden(sK1(X0,X1,X2),X2)) & (r2_hidden(k3_subset_1(X0,sK1(X0,X1,X2)),X1) | r2_hidden(sK1(X0,X1,X2),X2)) & m1_subset_1(sK1(X0,X1,X2),k1_zfmisc_1(X0))))),
% 1.88/1.03    introduced(choice_axiom,[])).
% 1.88/1.03  
% 1.88/1.03  fof(f34,plain,(
% 1.88/1.03    ! [X0,X1] : (! [X2] : (((k7_setfam_1(X0,X1) = X2 | ((~r2_hidden(k3_subset_1(X0,sK1(X0,X1,X2)),X1) | ~r2_hidden(sK1(X0,X1,X2),X2)) & (r2_hidden(k3_subset_1(X0,sK1(X0,X1,X2)),X1) | r2_hidden(sK1(X0,X1,X2),X2)) & m1_subset_1(sK1(X0,X1,X2),k1_zfmisc_1(X0)))) & (! [X4] : (((r2_hidden(X4,X2) | ~r2_hidden(k3_subset_1(X0,X4),X1)) & (r2_hidden(k3_subset_1(X0,X4),X1) | ~r2_hidden(X4,X2))) | ~m1_subset_1(X4,k1_zfmisc_1(X0))) | k7_setfam_1(X0,X1) != X2)) | ~m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(X0)))) | ~m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))))),
% 1.88/1.03    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1])],[f32,f33])).
% 1.88/1.03  
% 1.88/1.03  fof(f54,plain,(
% 1.88/1.03    ( ! [X2,X0,X1] : (k7_setfam_1(X0,X1) = X2 | r2_hidden(k3_subset_1(X0,sK1(X0,X1,X2)),X1) | r2_hidden(sK1(X0,X1,X2),X2) | ~m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0)))) )),
% 1.88/1.03    inference(cnf_transformation,[],[f34])).
% 1.88/1.03  
% 1.88/1.03  fof(f3,axiom,(
% 1.88/1.03    ! [X0] : k1_xboole_0 = k4_xboole_0(k1_xboole_0,X0)),
% 1.88/1.03    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 1.88/1.03  
% 1.88/1.03  fof(f39,plain,(
% 1.88/1.03    ( ! [X0] : (k1_xboole_0 = k4_xboole_0(k1_xboole_0,X0)) )),
% 1.88/1.03    inference(cnf_transformation,[],[f3])).
% 1.88/1.03  
% 1.88/1.03  fof(f2,axiom,(
% 1.88/1.03    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))),
% 1.88/1.03    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 1.88/1.03  
% 1.88/1.03  fof(f38,plain,(
% 1.88/1.03    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))) )),
% 1.88/1.03    inference(cnf_transformation,[],[f2])).
% 1.88/1.03  
% 1.88/1.03  fof(f16,axiom,(
% 1.88/1.03    ! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1))),
% 1.88/1.03    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 1.88/1.03  
% 1.88/1.03  fof(f57,plain,(
% 1.88/1.03    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1))) )),
% 1.88/1.03    inference(cnf_transformation,[],[f16])).
% 1.88/1.03  
% 1.88/1.03  fof(f5,axiom,(
% 1.88/1.03    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1)),
% 1.88/1.03    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 1.88/1.03  
% 1.88/1.03  fof(f41,plain,(
% 1.88/1.03    ( ! [X0,X1] : (k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1)) )),
% 1.88/1.03    inference(cnf_transformation,[],[f5])).
% 1.88/1.03  
% 1.88/1.03  fof(f6,axiom,(
% 1.88/1.03    ! [X0,X1,X2] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2)),
% 1.88/1.03    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 1.88/1.03  
% 1.88/1.03  fof(f42,plain,(
% 1.88/1.03    ( ! [X2,X0,X1] : (k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2)) )),
% 1.88/1.03    inference(cnf_transformation,[],[f6])).
% 1.88/1.03  
% 1.88/1.03  fof(f7,axiom,(
% 1.88/1.03    ! [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) = k3_enumset1(X0,X0,X1,X2,X3)),
% 1.88/1.03    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 1.88/1.03  
% 1.88/1.03  fof(f43,plain,(
% 1.88/1.03    ( ! [X2,X0,X3,X1] : (k2_enumset1(X0,X1,X2,X3) = k3_enumset1(X0,X0,X1,X2,X3)) )),
% 1.88/1.03    inference(cnf_transformation,[],[f7])).
% 1.88/1.03  
% 1.88/1.03  fof(f8,axiom,(
% 1.88/1.03    ! [X0,X1,X2,X3,X4] : k3_enumset1(X0,X1,X2,X3,X4) = k4_enumset1(X0,X0,X1,X2,X3,X4)),
% 1.88/1.03    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 1.88/1.03  
% 1.88/1.03  fof(f44,plain,(
% 1.88/1.03    ( ! [X4,X2,X0,X3,X1] : (k3_enumset1(X0,X1,X2,X3,X4) = k4_enumset1(X0,X0,X1,X2,X3,X4)) )),
% 1.88/1.03    inference(cnf_transformation,[],[f8])).
% 1.88/1.03  
% 1.88/1.03  fof(f9,axiom,(
% 1.88/1.03    ! [X0,X1,X2,X3,X4,X5] : k4_enumset1(X0,X1,X2,X3,X4,X5) = k5_enumset1(X0,X0,X1,X2,X3,X4,X5)),
% 1.88/1.03    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 1.88/1.03  
% 1.88/1.03  fof(f45,plain,(
% 1.88/1.03    ( ! [X4,X2,X0,X5,X3,X1] : (k4_enumset1(X0,X1,X2,X3,X4,X5) = k5_enumset1(X0,X0,X1,X2,X3,X4,X5)) )),
% 1.88/1.03    inference(cnf_transformation,[],[f9])).
% 1.88/1.03  
% 1.88/1.03  fof(f10,axiom,(
% 1.88/1.03    ! [X0,X1,X2,X3,X4,X5,X6] : k5_enumset1(X0,X1,X2,X3,X4,X5,X6) = k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6)),
% 1.88/1.03    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 1.88/1.03  
% 1.88/1.03  fof(f46,plain,(
% 1.88/1.03    ( ! [X6,X4,X2,X0,X5,X3,X1] : (k5_enumset1(X0,X1,X2,X3,X4,X5,X6) = k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6)) )),
% 1.88/1.03    inference(cnf_transformation,[],[f10])).
% 1.88/1.03  
% 1.88/1.03  fof(f62,plain,(
% 1.88/1.03    ( ! [X4,X2,X0,X5,X3,X1] : (k4_enumset1(X0,X1,X2,X3,X4,X5) = k6_enumset1(X0,X0,X0,X1,X2,X3,X4,X5)) )),
% 1.88/1.03    inference(definition_unfolding,[],[f45,f46])).
% 1.88/1.03  
% 1.88/1.03  fof(f63,plain,(
% 1.88/1.03    ( ! [X4,X2,X0,X3,X1] : (k3_enumset1(X0,X1,X2,X3,X4) = k6_enumset1(X0,X0,X0,X0,X1,X2,X3,X4)) )),
% 1.88/1.03    inference(definition_unfolding,[],[f44,f62])).
% 1.88/1.03  
% 1.88/1.03  fof(f64,plain,(
% 1.88/1.03    ( ! [X2,X0,X3,X1] : (k2_enumset1(X0,X1,X2,X3) = k6_enumset1(X0,X0,X0,X0,X0,X1,X2,X3)) )),
% 1.88/1.03    inference(definition_unfolding,[],[f43,f63])).
% 1.88/1.03  
% 1.88/1.03  fof(f65,plain,(
% 1.88/1.03    ( ! [X2,X0,X1] : (k1_enumset1(X0,X1,X2) = k6_enumset1(X0,X0,X0,X0,X0,X0,X1,X2)) )),
% 1.88/1.03    inference(definition_unfolding,[],[f42,f64])).
% 1.88/1.03  
% 1.88/1.03  fof(f66,plain,(
% 1.88/1.03    ( ! [X0,X1] : (k2_tarski(X0,X1) = k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)) )),
% 1.88/1.03    inference(definition_unfolding,[],[f41,f65])).
% 1.88/1.03  
% 1.88/1.03  fof(f67,plain,(
% 1.88/1.03    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k1_setfam_1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1))) )),
% 1.88/1.03    inference(definition_unfolding,[],[f57,f66])).
% 1.88/1.03  
% 1.88/1.03  fof(f68,plain,(
% 1.88/1.03    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k5_xboole_0(X0,k1_setfam_1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)))) )),
% 1.88/1.03    inference(definition_unfolding,[],[f38,f67])).
% 1.88/1.03  
% 1.88/1.03  fof(f70,plain,(
% 1.88/1.03    ( ! [X0] : (k1_xboole_0 = k5_xboole_0(k1_xboole_0,k1_setfam_1(k6_enumset1(k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,X0)))) )),
% 1.88/1.03    inference(definition_unfolding,[],[f39,f68])).
% 1.88/1.03  
% 1.88/1.03  fof(f11,axiom,(
% 1.88/1.03    ! [X0,X1] : (k4_xboole_0(X0,k1_tarski(X1)) = X0 <=> ~r2_hidden(X1,X0))),
% 1.88/1.03    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 1.88/1.03  
% 1.88/1.03  fof(f29,plain,(
% 1.88/1.03    ! [X0,X1] : ((k4_xboole_0(X0,k1_tarski(X1)) = X0 | r2_hidden(X1,X0)) & (~r2_hidden(X1,X0) | k4_xboole_0(X0,k1_tarski(X1)) != X0))),
% 1.88/1.03    inference(nnf_transformation,[],[f11])).
% 1.88/1.03  
% 1.88/1.03  fof(f47,plain,(
% 1.88/1.03    ( ! [X0,X1] : (~r2_hidden(X1,X0) | k4_xboole_0(X0,k1_tarski(X1)) != X0) )),
% 1.88/1.03    inference(cnf_transformation,[],[f29])).
% 1.88/1.03  
% 1.88/1.03  fof(f4,axiom,(
% 1.88/1.03    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0)),
% 1.88/1.03    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 1.88/1.03  
% 1.88/1.03  fof(f40,plain,(
% 1.88/1.03    ( ! [X0] : (k2_tarski(X0,X0) = k1_tarski(X0)) )),
% 1.88/1.03    inference(cnf_transformation,[],[f4])).
% 1.88/1.03  
% 1.88/1.03  fof(f69,plain,(
% 1.88/1.03    ( ! [X0] : (k1_tarski(X0) = k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0)) )),
% 1.88/1.03    inference(definition_unfolding,[],[f40,f66])).
% 1.88/1.03  
% 1.88/1.03  fof(f72,plain,(
% 1.88/1.03    ( ! [X0,X1] : (~r2_hidden(X1,X0) | k5_xboole_0(X0,k1_setfam_1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1)))) != X0) )),
% 1.88/1.03    inference(definition_unfolding,[],[f47,f68,f69])).
% 1.88/1.03  
% 1.88/1.03  fof(f13,axiom,(
% 1.88/1.03    ! [X0] : m1_subset_1(k1_subset_1(X0),k1_zfmisc_1(X0))),
% 1.88/1.03    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 1.88/1.03  
% 1.88/1.03  fof(f50,plain,(
% 1.88/1.03    ( ! [X0] : (m1_subset_1(k1_subset_1(X0),k1_zfmisc_1(X0))) )),
% 1.88/1.03    inference(cnf_transformation,[],[f13])).
% 1.88/1.03  
% 1.88/1.03  fof(f12,axiom,(
% 1.88/1.03    ! [X0] : k1_xboole_0 = k1_subset_1(X0)),
% 1.88/1.03    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 1.88/1.03  
% 1.88/1.03  fof(f49,plain,(
% 1.88/1.03    ( ! [X0] : (k1_xboole_0 = k1_subset_1(X0)) )),
% 1.88/1.03    inference(cnf_transformation,[],[f12])).
% 1.88/1.03  
% 1.88/1.03  fof(f73,plain,(
% 1.88/1.03    ( ! [X0] : (m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0))) )),
% 1.88/1.03    inference(definition_unfolding,[],[f50,f49])).
% 1.88/1.03  
% 1.88/1.03  fof(f18,conjecture,(
% 1.88/1.03    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) => ~(k1_xboole_0 = k7_setfam_1(X0,X1) & k1_xboole_0 != X1))),
% 1.88/1.03    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 1.88/1.03  
% 1.88/1.03  fof(f19,negated_conjecture,(
% 1.88/1.03    ~! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) => ~(k1_xboole_0 = k7_setfam_1(X0,X1) & k1_xboole_0 != X1))),
% 1.88/1.03    inference(negated_conjecture,[],[f18])).
% 1.88/1.03  
% 1.88/1.03  fof(f25,plain,(
% 1.88/1.03    ? [X0,X1] : ((k1_xboole_0 = k7_setfam_1(X0,X1) & k1_xboole_0 != X1) & m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))))),
% 1.88/1.03    inference(ennf_transformation,[],[f19])).
% 1.88/1.03  
% 1.88/1.03  fof(f26,plain,(
% 1.88/1.03    ? [X0,X1] : (k1_xboole_0 = k7_setfam_1(X0,X1) & k1_xboole_0 != X1 & m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))))),
% 1.88/1.03    inference(flattening,[],[f25])).
% 1.88/1.03  
% 1.88/1.03  fof(f35,plain,(
% 1.88/1.03    ? [X0,X1] : (k1_xboole_0 = k7_setfam_1(X0,X1) & k1_xboole_0 != X1 & m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0)))) => (k1_xboole_0 = k7_setfam_1(sK2,sK3) & k1_xboole_0 != sK3 & m1_subset_1(sK3,k1_zfmisc_1(k1_zfmisc_1(sK2))))),
% 1.88/1.03    introduced(choice_axiom,[])).
% 1.88/1.03  
% 1.88/1.03  fof(f36,plain,(
% 1.88/1.03    k1_xboole_0 = k7_setfam_1(sK2,sK3) & k1_xboole_0 != sK3 & m1_subset_1(sK3,k1_zfmisc_1(k1_zfmisc_1(sK2)))),
% 1.88/1.03    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2,sK3])],[f26,f35])).
% 1.88/1.03  
% 1.88/1.03  fof(f59,plain,(
% 1.88/1.03    m1_subset_1(sK3,k1_zfmisc_1(k1_zfmisc_1(sK2)))),
% 1.88/1.03    inference(cnf_transformation,[],[f36])).
% 1.88/1.03  
% 1.88/1.03  fof(f15,axiom,(
% 1.88/1.03    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) => k7_setfam_1(X0,k7_setfam_1(X0,X1)) = X1)),
% 1.88/1.03    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 1.88/1.03  
% 1.88/1.03  fof(f22,plain,(
% 1.88/1.03    ! [X0,X1] : (k7_setfam_1(X0,k7_setfam_1(X0,X1)) = X1 | ~m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))))),
% 1.88/1.03    inference(ennf_transformation,[],[f15])).
% 1.88/1.03  
% 1.88/1.03  fof(f56,plain,(
% 1.88/1.03    ( ! [X0,X1] : (k7_setfam_1(X0,k7_setfam_1(X0,X1)) = X1 | ~m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0)))) )),
% 1.88/1.03    inference(cnf_transformation,[],[f22])).
% 1.88/1.03  
% 1.88/1.03  fof(f61,plain,(
% 1.88/1.03    k1_xboole_0 = k7_setfam_1(sK2,sK3)),
% 1.88/1.03    inference(cnf_transformation,[],[f36])).
% 1.88/1.03  
% 1.88/1.03  fof(f60,plain,(
% 1.88/1.03    k1_xboole_0 != sK3),
% 1.88/1.03    inference(cnf_transformation,[],[f36])).
% 1.88/1.03  
% 1.88/1.03  cnf(c_6,plain,
% 1.88/1.03      ( ~ m1_subset_1(X0,k1_zfmisc_1(k1_zfmisc_1(X1)))
% 1.88/1.03      | ~ m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(X1)))
% 1.88/1.03      | r2_hidden(sK1(X1,X2,X0),X0)
% 1.88/1.03      | r2_hidden(k3_subset_1(X1,sK1(X1,X2,X0)),X2)
% 1.88/1.03      | k7_setfam_1(X1,X2) = X0 ),
% 1.88/1.03      inference(cnf_transformation,[],[f54]) ).
% 1.88/1.03  
% 1.88/1.03  cnf(c_528,plain,
% 1.88/1.03      ( k7_setfam_1(X0,X1) = X2
% 1.88/1.03      | m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(X0))) != iProver_top
% 1.88/1.03      | m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) != iProver_top
% 1.88/1.03      | r2_hidden(sK1(X0,X1,X2),X2) = iProver_top
% 1.88/1.03      | r2_hidden(k3_subset_1(X0,sK1(X0,X1,X2)),X1) = iProver_top ),
% 1.88/1.03      inference(predicate_to_equality,[status(thm)],[c_6]) ).
% 1.88/1.03  
% 1.88/1.03  cnf(c_1,plain,
% 1.88/1.03      ( k5_xboole_0(k1_xboole_0,k1_setfam_1(k6_enumset1(k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,X0))) = k1_xboole_0 ),
% 1.88/1.03      inference(cnf_transformation,[],[f70]) ).
% 1.88/1.03  
% 1.88/1.03  cnf(c_3,plain,
% 1.88/1.03      ( ~ r2_hidden(X0,X1)
% 1.88/1.03      | k5_xboole_0(X1,k1_setfam_1(k6_enumset1(X1,X1,X1,X1,X1,X1,X1,k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0)))) != X1 ),
% 1.88/1.03      inference(cnf_transformation,[],[f72]) ).
% 1.88/1.03  
% 1.88/1.03  cnf(c_531,plain,
% 1.88/1.03      ( k5_xboole_0(X0,k1_setfam_1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1)))) != X0
% 1.88/1.03      | r2_hidden(X1,X0) != iProver_top ),
% 1.88/1.03      inference(predicate_to_equality,[status(thm)],[c_3]) ).
% 1.88/1.03  
% 1.88/1.03  cnf(c_838,plain,
% 1.88/1.03      ( r2_hidden(X0,k1_xboole_0) != iProver_top ),
% 1.88/1.03      inference(superposition,[status(thm)],[c_1,c_531]) ).
% 1.88/1.03  
% 1.88/1.03  cnf(c_1630,plain,
% 1.88/1.03      ( k7_setfam_1(X0,k1_xboole_0) = X1
% 1.88/1.03      | m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) != iProver_top
% 1.88/1.03      | m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_zfmisc_1(X0))) != iProver_top
% 1.88/1.03      | r2_hidden(sK1(X0,k1_xboole_0,X1),X1) = iProver_top ),
% 1.88/1.03      inference(superposition,[status(thm)],[c_528,c_838]) ).
% 1.88/1.03  
% 1.88/1.03  cnf(c_4,plain,
% 1.88/1.03      ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0)) ),
% 1.88/1.03      inference(cnf_transformation,[],[f73]) ).
% 1.88/1.03  
% 1.88/1.03  cnf(c_646,plain,
% 1.88/1.03      ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_zfmisc_1(X0))) ),
% 1.88/1.03      inference(instantiation,[status(thm)],[c_4]) ).
% 1.88/1.03  
% 1.88/1.03  cnf(c_649,plain,
% 1.88/1.03      ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_zfmisc_1(X0))) = iProver_top ),
% 1.88/1.03      inference(predicate_to_equality,[status(thm)],[c_646]) ).
% 1.88/1.03  
% 1.88/1.03  cnf(c_1874,plain,
% 1.88/1.03      ( m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) != iProver_top
% 1.88/1.03      | k7_setfam_1(X0,k1_xboole_0) = X1
% 1.88/1.03      | r2_hidden(sK1(X0,k1_xboole_0,X1),X1) = iProver_top ),
% 1.88/1.03      inference(global_propositional_subsumption,
% 1.88/1.03                [status(thm)],
% 1.88/1.03                [c_1630,c_649]) ).
% 1.88/1.03  
% 1.88/1.03  cnf(c_1875,plain,
% 1.88/1.03      ( k7_setfam_1(X0,k1_xboole_0) = X1
% 1.88/1.03      | m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) != iProver_top
% 1.88/1.03      | r2_hidden(sK1(X0,k1_xboole_0,X1),X1) = iProver_top ),
% 1.88/1.03      inference(renaming,[status(thm)],[c_1874]) ).
% 1.88/1.03  
% 1.88/1.03  cnf(c_1882,plain,
% 1.88/1.03      ( k7_setfam_1(X0,k1_xboole_0) = k1_xboole_0
% 1.88/1.03      | m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_zfmisc_1(X0))) != iProver_top ),
% 1.88/1.03      inference(superposition,[status(thm)],[c_1875,c_838]) ).
% 1.88/1.03  
% 1.88/1.03  cnf(c_2490,plain,
% 1.88/1.03      ( k7_setfam_1(X0,k1_xboole_0) = k1_xboole_0 ),
% 1.88/1.03      inference(global_propositional_subsumption,
% 1.88/1.03                [status(thm)],
% 1.88/1.03                [c_1882,c_649]) ).
% 1.88/1.03  
% 1.88/1.03  cnf(c_14,negated_conjecture,
% 1.88/1.03      ( m1_subset_1(sK3,k1_zfmisc_1(k1_zfmisc_1(sK2))) ),
% 1.88/1.03      inference(cnf_transformation,[],[f59]) ).
% 1.88/1.03  
% 1.88/1.03  cnf(c_522,plain,
% 1.88/1.03      ( m1_subset_1(sK3,k1_zfmisc_1(k1_zfmisc_1(sK2))) = iProver_top ),
% 1.88/1.03      inference(predicate_to_equality,[status(thm)],[c_14]) ).
% 1.88/1.03  
% 1.88/1.03  cnf(c_10,plain,
% 1.88/1.03      ( ~ m1_subset_1(X0,k1_zfmisc_1(k1_zfmisc_1(X1)))
% 1.88/1.03      | k7_setfam_1(X1,k7_setfam_1(X1,X0)) = X0 ),
% 1.88/1.03      inference(cnf_transformation,[],[f56]) ).
% 1.88/1.03  
% 1.88/1.03  cnf(c_524,plain,
% 1.88/1.03      ( k7_setfam_1(X0,k7_setfam_1(X0,X1)) = X1
% 1.88/1.03      | m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) != iProver_top ),
% 1.88/1.03      inference(predicate_to_equality,[status(thm)],[c_10]) ).
% 1.88/1.03  
% 1.88/1.03  cnf(c_733,plain,
% 1.88/1.03      ( k7_setfam_1(sK2,k7_setfam_1(sK2,sK3)) = sK3 ),
% 1.88/1.03      inference(superposition,[status(thm)],[c_522,c_524]) ).
% 1.88/1.03  
% 1.88/1.03  cnf(c_12,negated_conjecture,
% 1.88/1.03      ( k1_xboole_0 = k7_setfam_1(sK2,sK3) ),
% 1.88/1.03      inference(cnf_transformation,[],[f61]) ).
% 1.88/1.03  
% 1.88/1.03  cnf(c_735,plain,
% 1.88/1.03      ( k7_setfam_1(sK2,k1_xboole_0) = sK3 ),
% 1.88/1.03      inference(light_normalisation,[status(thm)],[c_733,c_12]) ).
% 1.88/1.03  
% 1.88/1.03  cnf(c_2497,plain,
% 1.88/1.03      ( sK3 = k1_xboole_0 ),
% 1.88/1.03      inference(demodulation,[status(thm)],[c_2490,c_735]) ).
% 1.88/1.03  
% 1.88/1.03  cnf(c_186,plain,( X0 != X1 | X2 != X1 | X2 = X0 ),theory(equality) ).
% 1.88/1.03  
% 1.88/1.03  cnf(c_661,plain,
% 1.88/1.03      ( sK3 != X0 | k1_xboole_0 != X0 | k1_xboole_0 = sK3 ),
% 1.88/1.03      inference(instantiation,[status(thm)],[c_186]) ).
% 1.88/1.03  
% 1.88/1.03  cnf(c_662,plain,
% 1.88/1.03      ( sK3 != k1_xboole_0
% 1.88/1.03      | k1_xboole_0 = sK3
% 1.88/1.03      | k1_xboole_0 != k1_xboole_0 ),
% 1.88/1.03      inference(instantiation,[status(thm)],[c_661]) ).
% 1.88/1.03  
% 1.88/1.03  cnf(c_185,plain,( X0 = X0 ),theory(equality) ).
% 1.88/1.03  
% 1.88/1.03  cnf(c_204,plain,
% 1.88/1.03      ( k1_xboole_0 = k1_xboole_0 ),
% 1.88/1.03      inference(instantiation,[status(thm)],[c_185]) ).
% 1.88/1.03  
% 1.88/1.03  cnf(c_13,negated_conjecture,
% 1.88/1.03      ( k1_xboole_0 != sK3 ),
% 1.88/1.03      inference(cnf_transformation,[],[f60]) ).
% 1.88/1.03  
% 1.88/1.03  cnf(contradiction,plain,
% 1.88/1.03      ( $false ),
% 1.88/1.03      inference(minisat,[status(thm)],[c_2497,c_662,c_204,c_13]) ).
% 1.88/1.03  
% 1.88/1.03  
% 1.88/1.03  % SZS output end CNFRefutation for theBenchmark.p
% 1.88/1.03  
% 1.88/1.03  ------                               Statistics
% 1.88/1.03  
% 1.88/1.03  ------ General
% 1.88/1.03  
% 1.88/1.03  abstr_ref_over_cycles:                  0
% 1.88/1.03  abstr_ref_under_cycles:                 0
% 1.88/1.03  gc_basic_clause_elim:                   0
% 1.88/1.03  forced_gc_time:                         0
% 1.88/1.03  parsing_time:                           0.015
% 1.88/1.03  unif_index_cands_time:                  0.
% 1.88/1.03  unif_index_add_time:                    0.
% 1.88/1.03  orderings_time:                         0.
% 1.88/1.03  out_proof_time:                         0.009
% 1.88/1.03  total_time:                             0.13
% 1.88/1.03  num_of_symbols:                         44
% 1.88/1.03  num_of_terms:                           2969
% 1.88/1.03  
% 1.88/1.03  ------ Preprocessing
% 1.88/1.03  
% 1.88/1.03  num_of_splits:                          0
% 1.88/1.03  num_of_split_atoms:                     0
% 1.88/1.03  num_of_reused_defs:                     0
% 1.88/1.03  num_eq_ax_congr_red:                    10
% 1.88/1.03  num_of_sem_filtered_clauses:            1
% 1.88/1.03  num_of_subtypes:                        0
% 1.88/1.03  monotx_restored_types:                  0
% 1.88/1.03  sat_num_of_epr_types:                   0
% 1.88/1.03  sat_num_of_non_cyclic_types:            0
% 1.88/1.03  sat_guarded_non_collapsed_types:        0
% 1.88/1.03  num_pure_diseq_elim:                    0
% 1.88/1.03  simp_replaced_by:                       0
% 1.88/1.03  res_preprocessed:                       66
% 1.88/1.03  prep_upred:                             0
% 1.88/1.03  prep_unflattend:                        0
% 1.88/1.03  smt_new_axioms:                         0
% 1.88/1.03  pred_elim_cands:                        2
% 1.88/1.03  pred_elim:                              0
% 1.88/1.03  pred_elim_cl:                           0
% 1.88/1.03  pred_elim_cycles:                       1
% 1.88/1.03  merged_defs:                            6
% 1.88/1.03  merged_defs_ncl:                        0
% 1.88/1.03  bin_hyper_res:                          6
% 1.88/1.03  prep_cycles:                            3
% 1.88/1.03  pred_elim_time:                         0.
% 1.88/1.03  splitting_time:                         0.
% 1.88/1.03  sem_filter_time:                        0.
% 1.88/1.03  monotx_time:                            0.001
% 1.88/1.03  subtype_inf_time:                       0.
% 1.88/1.03  
% 1.88/1.03  ------ Problem properties
% 1.88/1.03  
% 1.88/1.03  clauses:                                15
% 1.88/1.03  conjectures:                            3
% 1.88/1.03  epr:                                    1
% 1.88/1.03  horn:                                   11
% 1.88/1.03  ground:                                 3
% 1.88/1.03  unary:                                  5
% 1.88/1.03  binary:                                 4
% 1.88/1.03  lits:                                   40
% 1.88/1.03  lits_eq:                                10
% 1.88/1.03  fd_pure:                                0
% 1.88/1.03  fd_pseudo:                              0
% 1.88/1.03  fd_cond:                                1
% 1.88/1.03  fd_pseudo_cond:                         3
% 1.88/1.03  ac_symbols:                             0
% 1.88/1.03  
% 1.88/1.03  ------ Propositional Solver
% 1.88/1.03  
% 1.88/1.03  prop_solver_calls:                      23
% 1.88/1.03  prop_fast_solver_calls:                 484
% 1.88/1.03  smt_solver_calls:                       0
% 1.88/1.03  smt_fast_solver_calls:                  0
% 1.88/1.03  prop_num_of_clauses:                    865
% 1.88/1.03  prop_preprocess_simplified:             2696
% 1.88/1.03  prop_fo_subsumed:                       9
% 1.88/1.03  prop_solver_time:                       0.
% 1.88/1.03  smt_solver_time:                        0.
% 1.88/1.03  smt_fast_solver_time:                   0.
% 1.88/1.03  prop_fast_solver_time:                  0.
% 1.88/1.03  prop_unsat_core_time:                   0.
% 1.88/1.03  
% 1.88/1.03  ------ QBF
% 1.88/1.03  
% 1.88/1.03  qbf_q_res:                              0
% 1.88/1.03  qbf_num_tautologies:                    0
% 1.88/1.03  qbf_prep_cycles:                        0
% 1.88/1.03  
% 1.88/1.03  ------ BMC1
% 1.88/1.03  
% 1.88/1.03  bmc1_current_bound:                     -1
% 1.88/1.03  bmc1_last_solved_bound:                 -1
% 1.88/1.03  bmc1_unsat_core_size:                   -1
% 1.88/1.03  bmc1_unsat_core_parents_size:           -1
% 1.88/1.03  bmc1_merge_next_fun:                    0
% 1.88/1.03  bmc1_unsat_core_clauses_time:           0.
% 1.88/1.03  
% 1.88/1.03  ------ Instantiation
% 1.88/1.03  
% 1.88/1.03  inst_num_of_clauses:                    263
% 1.88/1.03  inst_num_in_passive:                    84
% 1.88/1.03  inst_num_in_active:                     138
% 1.88/1.03  inst_num_in_unprocessed:                41
% 1.88/1.03  inst_num_of_loops:                      170
% 1.88/1.03  inst_num_of_learning_restarts:          0
% 1.88/1.03  inst_num_moves_active_passive:          29
% 1.88/1.03  inst_lit_activity:                      0
% 1.88/1.03  inst_lit_activity_moves:                0
% 1.88/1.03  inst_num_tautologies:                   0
% 1.88/1.03  inst_num_prop_implied:                  0
% 1.88/1.03  inst_num_existing_simplified:           0
% 1.88/1.03  inst_num_eq_res_simplified:             0
% 1.88/1.03  inst_num_child_elim:                    0
% 1.88/1.03  inst_num_of_dismatching_blockings:      96
% 1.88/1.03  inst_num_of_non_proper_insts:           265
% 1.88/1.03  inst_num_of_duplicates:                 0
% 1.88/1.03  inst_inst_num_from_inst_to_res:         0
% 1.88/1.03  inst_dismatching_checking_time:         0.
% 1.88/1.03  
% 1.88/1.03  ------ Resolution
% 1.88/1.03  
% 1.88/1.03  res_num_of_clauses:                     0
% 1.88/1.03  res_num_in_passive:                     0
% 1.88/1.03  res_num_in_active:                      0
% 1.88/1.03  res_num_of_loops:                       69
% 1.88/1.03  res_forward_subset_subsumed:            18
% 1.88/1.03  res_backward_subset_subsumed:           0
% 1.88/1.03  res_forward_subsumed:                   0
% 1.88/1.03  res_backward_subsumed:                  0
% 1.88/1.03  res_forward_subsumption_resolution:     0
% 1.88/1.03  res_backward_subsumption_resolution:    0
% 1.88/1.03  res_clause_to_clause_subsumption:       118
% 1.88/1.03  res_orphan_elimination:                 0
% 1.88/1.03  res_tautology_del:                      31
% 1.88/1.03  res_num_eq_res_simplified:              0
% 1.88/1.03  res_num_sel_changes:                    0
% 1.88/1.03  res_moves_from_active_to_pass:          0
% 1.88/1.03  
% 1.88/1.03  ------ Superposition
% 1.88/1.03  
% 1.88/1.03  sup_time_total:                         0.
% 1.88/1.03  sup_time_generating:                    0.
% 1.88/1.03  sup_time_sim_full:                      0.
% 1.88/1.03  sup_time_sim_immed:                     0.
% 1.88/1.03  
% 1.88/1.03  sup_num_of_clauses:                     52
% 1.88/1.03  sup_num_in_active:                      29
% 1.88/1.03  sup_num_in_passive:                     23
% 1.88/1.03  sup_num_of_loops:                       33
% 1.88/1.03  sup_fw_superposition:                   35
% 1.88/1.03  sup_bw_superposition:                   15
% 1.88/1.03  sup_immediate_simplified:               11
% 1.88/1.03  sup_given_eliminated:                   0
% 1.88/1.03  comparisons_done:                       0
% 1.88/1.03  comparisons_avoided:                    3
% 1.88/1.03  
% 1.88/1.03  ------ Simplifications
% 1.88/1.03  
% 1.88/1.03  
% 1.88/1.03  sim_fw_subset_subsumed:                 0
% 1.88/1.03  sim_bw_subset_subsumed:                 1
% 1.88/1.03  sim_fw_subsumed:                        5
% 1.88/1.03  sim_bw_subsumed:                        0
% 1.88/1.03  sim_fw_subsumption_res:                 1
% 1.88/1.03  sim_bw_subsumption_res:                 0
% 1.88/1.03  sim_tautology_del:                      1
% 1.88/1.03  sim_eq_tautology_del:                   2
% 1.88/1.03  sim_eq_res_simp:                        0
% 1.88/1.03  sim_fw_demodulated:                     3
% 1.88/1.03  sim_bw_demodulated:                     4
% 1.88/1.03  sim_light_normalised:                   7
% 1.88/1.03  sim_joinable_taut:                      0
% 1.88/1.03  sim_joinable_simp:                      0
% 1.88/1.03  sim_ac_normalised:                      0
% 1.88/1.03  sim_smt_subsumption:                    0
% 1.88/1.03  
%------------------------------------------------------------------------------
