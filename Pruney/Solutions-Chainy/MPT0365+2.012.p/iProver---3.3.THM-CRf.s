%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n017.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 11:40:46 EST 2020

% Result     : Theorem 7.23s
% Output     : CNFRefutation 7.23s
% Verified   : 
% Statistics : Number of formulae       :  120 ( 273 expanded)
%              Number of clauses        :   52 (  71 expanded)
%              Number of leaves         :   22 (  73 expanded)
%              Depth                    :   17
%              Number of atoms          :  220 ( 712 expanded)
%              Number of equality atoms :  119 ( 283 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal clause size      :   10 (   2 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f20,conjecture,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(X0))
         => ( ( r1_xboole_0(k3_subset_1(X0,X1),k3_subset_1(X0,X2))
              & r1_xboole_0(X1,X2) )
           => k3_subset_1(X0,X2) = X1 ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f21,negated_conjecture,(
    ~ ! [X0,X1] :
        ( m1_subset_1(X1,k1_zfmisc_1(X0))
       => ! [X2] :
            ( m1_subset_1(X2,k1_zfmisc_1(X0))
           => ( ( r1_xboole_0(k3_subset_1(X0,X1),k3_subset_1(X0,X2))
                & r1_xboole_0(X1,X2) )
             => k3_subset_1(X0,X2) = X1 ) ) ) ),
    inference(negated_conjecture,[],[f20])).

fof(f28,plain,(
    ? [X0,X1] :
      ( ? [X2] :
          ( k3_subset_1(X0,X2) != X1
          & r1_xboole_0(k3_subset_1(X0,X1),k3_subset_1(X0,X2))
          & r1_xboole_0(X1,X2)
          & m1_subset_1(X2,k1_zfmisc_1(X0)) )
      & m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f21])).

fof(f29,plain,(
    ? [X0,X1] :
      ( ? [X2] :
          ( k3_subset_1(X0,X2) != X1
          & r1_xboole_0(k3_subset_1(X0,X1),k3_subset_1(X0,X2))
          & r1_xboole_0(X1,X2)
          & m1_subset_1(X2,k1_zfmisc_1(X0)) )
      & m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(flattening,[],[f28])).

fof(f33,plain,(
    ! [X0,X1] :
      ( ? [X2] :
          ( k3_subset_1(X0,X2) != X1
          & r1_xboole_0(k3_subset_1(X0,X1),k3_subset_1(X0,X2))
          & r1_xboole_0(X1,X2)
          & m1_subset_1(X2,k1_zfmisc_1(X0)) )
     => ( k3_subset_1(X0,sK2) != X1
        & r1_xboole_0(k3_subset_1(X0,X1),k3_subset_1(X0,sK2))
        & r1_xboole_0(X1,sK2)
        & m1_subset_1(sK2,k1_zfmisc_1(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f32,plain,
    ( ? [X0,X1] :
        ( ? [X2] :
            ( k3_subset_1(X0,X2) != X1
            & r1_xboole_0(k3_subset_1(X0,X1),k3_subset_1(X0,X2))
            & r1_xboole_0(X1,X2)
            & m1_subset_1(X2,k1_zfmisc_1(X0)) )
        & m1_subset_1(X1,k1_zfmisc_1(X0)) )
   => ( ? [X2] :
          ( k3_subset_1(sK0,X2) != sK1
          & r1_xboole_0(k3_subset_1(sK0,sK1),k3_subset_1(sK0,X2))
          & r1_xboole_0(sK1,X2)
          & m1_subset_1(X2,k1_zfmisc_1(sK0)) )
      & m1_subset_1(sK1,k1_zfmisc_1(sK0)) ) ),
    introduced(choice_axiom,[])).

fof(f34,plain,
    ( k3_subset_1(sK0,sK2) != sK1
    & r1_xboole_0(k3_subset_1(sK0,sK1),k3_subset_1(sK0,sK2))
    & r1_xboole_0(sK1,sK2)
    & m1_subset_1(sK2,k1_zfmisc_1(sK0))
    & m1_subset_1(sK1,k1_zfmisc_1(sK0)) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f29,f33,f32])).

fof(f59,plain,(
    r1_xboole_0(k3_subset_1(sK0,sK1),k3_subset_1(sK0,sK2)) ),
    inference(cnf_transformation,[],[f34])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( r1_xboole_0(X0,X1)
     => r1_xboole_0(X1,X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f22,plain,(
    ! [X0,X1] :
      ( r1_xboole_0(X1,X0)
      | ~ r1_xboole_0(X0,X1) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f35,plain,(
    ! [X0,X1] :
      ( r1_xboole_0(X1,X0)
      | ~ r1_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f9,axiom,(
    ! [X0,X1] :
      ( r1_xboole_0(X0,X1)
    <=> k4_xboole_0(X0,X1) = X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f30,plain,(
    ! [X0,X1] :
      ( ( r1_xboole_0(X0,X1)
        | k4_xboole_0(X0,X1) != X0 )
      & ( k4_xboole_0(X0,X1) = X0
        | ~ r1_xboole_0(X0,X1) ) ) ),
    inference(nnf_transformation,[],[f9])).

fof(f43,plain,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,X1) = X0
      | ~ r1_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f57,plain,(
    m1_subset_1(sK2,k1_zfmisc_1(sK0)) ),
    inference(cnf_transformation,[],[f34])).

fof(f16,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => k4_xboole_0(X0,X1) = k3_subset_1(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f24,plain,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,X1) = k3_subset_1(X0,X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f16])).

fof(f51,plain,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,X1) = k3_subset_1(X0,X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f56,plain,(
    m1_subset_1(sK1,k1_zfmisc_1(sK0)) ),
    inference(cnf_transformation,[],[f34])).

fof(f8,axiom,(
    ! [X0,X1,X2] : k3_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X0,X2)) = k4_xboole_0(X0,k2_xboole_0(X1,X2)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f42,plain,(
    ! [X2,X0,X1] : k3_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X0,X2)) = k4_xboole_0(X0,k2_xboole_0(X1,X2)) ),
    inference(cnf_transformation,[],[f8])).

fof(f7,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f41,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f7])).

fof(f15,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f50,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1)) ),
    inference(cnf_transformation,[],[f15])).

fof(f14,axiom,(
    ! [X0,X1] : k2_enumset1(X0,X0,X0,X1) = k2_tarski(X0,X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f49,plain,(
    ! [X0,X1] : k2_enumset1(X0,X0,X0,X1) = k2_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f14])).

fof(f10,axiom,(
    ! [X0,X1,X2,X3] : k3_enumset1(X0,X0,X1,X2,X3) = k2_enumset1(X0,X1,X2,X3) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f45,plain,(
    ! [X2,X0,X3,X1] : k3_enumset1(X0,X0,X1,X2,X3) = k2_enumset1(X0,X1,X2,X3) ),
    inference(cnf_transformation,[],[f10])).

fof(f11,axiom,(
    ! [X0,X1,X2,X3,X4] : k3_enumset1(X0,X1,X2,X3,X4) = k4_enumset1(X0,X0,X1,X2,X3,X4) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f46,plain,(
    ! [X4,X2,X0,X3,X1] : k3_enumset1(X0,X1,X2,X3,X4) = k4_enumset1(X0,X0,X1,X2,X3,X4) ),
    inference(cnf_transformation,[],[f11])).

fof(f12,axiom,(
    ! [X0,X1,X2,X3,X4,X5] : k4_enumset1(X0,X1,X2,X3,X4,X5) = k5_enumset1(X0,X0,X1,X2,X3,X4,X5) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f47,plain,(
    ! [X4,X2,X0,X5,X3,X1] : k4_enumset1(X0,X1,X2,X3,X4,X5) = k5_enumset1(X0,X0,X1,X2,X3,X4,X5) ),
    inference(cnf_transformation,[],[f12])).

fof(f13,axiom,(
    ! [X0,X1,X2,X3,X4,X5,X6] : k5_enumset1(X0,X1,X2,X3,X4,X5,X6) = k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f48,plain,(
    ! [X6,X4,X2,X0,X5,X3,X1] : k5_enumset1(X0,X1,X2,X3,X4,X5,X6) = k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6) ),
    inference(cnf_transformation,[],[f13])).

fof(f61,plain,(
    ! [X4,X2,X0,X5,X3,X1] : k4_enumset1(X0,X1,X2,X3,X4,X5) = k6_enumset1(X0,X0,X0,X1,X2,X3,X4,X5) ),
    inference(definition_unfolding,[],[f47,f48])).

fof(f62,plain,(
    ! [X4,X2,X0,X3,X1] : k3_enumset1(X0,X1,X2,X3,X4) = k6_enumset1(X0,X0,X0,X0,X1,X2,X3,X4) ),
    inference(definition_unfolding,[],[f46,f61])).

fof(f63,plain,(
    ! [X2,X0,X3,X1] : k2_enumset1(X0,X1,X2,X3) = k6_enumset1(X0,X0,X0,X0,X0,X1,X2,X3) ),
    inference(definition_unfolding,[],[f45,f62])).

fof(f64,plain,(
    ! [X0,X1] : k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1) = k2_tarski(X0,X1) ),
    inference(definition_unfolding,[],[f49,f63])).

fof(f65,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)) ),
    inference(definition_unfolding,[],[f50,f64])).

fof(f70,plain,(
    ! [X2,X0,X1] : k4_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X0,X2))) = k4_xboole_0(X0,k3_tarski(k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X2))) ),
    inference(definition_unfolding,[],[f42,f41,f65])).

fof(f5,axiom,(
    ! [X0,X1,X2] : k4_xboole_0(X0,k2_xboole_0(X1,X2)) = k4_xboole_0(k4_xboole_0(X0,X1),X2) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f39,plain,(
    ! [X2,X0,X1] : k4_xboole_0(X0,k2_xboole_0(X1,X2)) = k4_xboole_0(k4_xboole_0(X0,X1),X2) ),
    inference(cnf_transformation,[],[f5])).

fof(f68,plain,(
    ! [X2,X0,X1] : k4_xboole_0(k4_xboole_0(X0,X1),X2) = k4_xboole_0(X0,k3_tarski(k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X2))) ),
    inference(definition_unfolding,[],[f39,f65])).

fof(f2,axiom,(
    ! [X0] : k1_xboole_0 = k3_xboole_0(X0,k1_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f36,plain,(
    ! [X0] : k1_xboole_0 = k3_xboole_0(X0,k1_xboole_0) ),
    inference(cnf_transformation,[],[f2])).

fof(f66,plain,(
    ! [X0] : k1_xboole_0 = k4_xboole_0(X0,k4_xboole_0(X0,k1_xboole_0)) ),
    inference(definition_unfolding,[],[f36,f41])).

fof(f3,axiom,(
    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f37,plain,(
    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(cnf_transformation,[],[f3])).

fof(f18,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => k3_subset_1(X0,k3_subset_1(X0,X1)) = X1 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f26,plain,(
    ! [X0,X1] :
      ( k3_subset_1(X0,k3_subset_1(X0,X1)) = X1
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f18])).

fof(f53,plain,(
    ! [X0,X1] :
      ( k3_subset_1(X0,k3_subset_1(X0,X1)) = X1
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f19,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(X0))
         => ( r1_xboole_0(X1,k3_subset_1(X0,X2))
          <=> r1_tarski(X1,X2) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f27,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( ( r1_xboole_0(X1,k3_subset_1(X0,X2))
          <=> r1_tarski(X1,X2) )
          | ~ m1_subset_1(X2,k1_zfmisc_1(X0)) )
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f19])).

fof(f31,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( ( ( r1_xboole_0(X1,k3_subset_1(X0,X2))
              | ~ r1_tarski(X1,X2) )
            & ( r1_tarski(X1,X2)
              | ~ r1_xboole_0(X1,k3_subset_1(X0,X2)) ) )
          | ~ m1_subset_1(X2,k1_zfmisc_1(X0)) )
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(nnf_transformation,[],[f27])).

fof(f54,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(X1,X2)
      | ~ r1_xboole_0(X1,k3_subset_1(X0,X2))
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f17,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => m1_subset_1(k3_subset_1(X0,X1),k1_zfmisc_1(X0)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f25,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k3_subset_1(X0,X1),k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f17])).

fof(f52,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k3_subset_1(X0,X1),k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f6,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
     => k2_xboole_0(X0,k4_xboole_0(X1,X0)) = X1 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f23,plain,(
    ! [X0,X1] :
      ( k2_xboole_0(X0,k4_xboole_0(X1,X0)) = X1
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f40,plain,(
    ! [X0,X1] :
      ( k2_xboole_0(X0,k4_xboole_0(X1,X0)) = X1
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f69,plain,(
    ! [X0,X1] :
      ( k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,k4_xboole_0(X1,X0))) = X1
      | ~ r1_tarski(X0,X1) ) ),
    inference(definition_unfolding,[],[f40,f65])).

fof(f58,plain,(
    r1_xboole_0(sK1,sK2) ),
    inference(cnf_transformation,[],[f34])).

fof(f4,axiom,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k4_xboole_0(k2_xboole_0(X0,X1),X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f38,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k4_xboole_0(k2_xboole_0(X0,X1),X1) ),
    inference(cnf_transformation,[],[f4])).

fof(f67,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k4_xboole_0(k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)),X1) ),
    inference(definition_unfolding,[],[f38,f65])).

fof(f60,plain,(
    k3_subset_1(sK0,sK2) != sK1 ),
    inference(cnf_transformation,[],[f34])).

cnf(c_15,negated_conjecture,
    ( r1_xboole_0(k3_subset_1(sK0,sK1),k3_subset_1(sK0,sK2)) ),
    inference(cnf_transformation,[],[f59])).

cnf(c_581,plain,
    ( r1_xboole_0(k3_subset_1(sK0,sK1),k3_subset_1(sK0,sK2)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_15])).

cnf(c_0,plain,
    ( ~ r1_xboole_0(X0,X1)
    | r1_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f35])).

cnf(c_590,plain,
    ( r1_xboole_0(X0,X1) != iProver_top
    | r1_xboole_0(X1,X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_0])).

cnf(c_1415,plain,
    ( r1_xboole_0(k3_subset_1(sK0,sK2),k3_subset_1(sK0,sK1)) = iProver_top ),
    inference(superposition,[status(thm)],[c_581,c_590])).

cnf(c_8,plain,
    ( ~ r1_xboole_0(X0,X1)
    | k4_xboole_0(X0,X1) = X0 ),
    inference(cnf_transformation,[],[f43])).

cnf(c_587,plain,
    ( k4_xboole_0(X0,X1) = X0
    | r1_xboole_0(X0,X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_8])).

cnf(c_1544,plain,
    ( k4_xboole_0(k3_subset_1(sK0,sK2),k3_subset_1(sK0,sK1)) = k3_subset_1(sK0,sK2) ),
    inference(superposition,[status(thm)],[c_1415,c_587])).

cnf(c_17,negated_conjecture,
    ( m1_subset_1(sK2,k1_zfmisc_1(sK0)) ),
    inference(cnf_transformation,[],[f57])).

cnf(c_579,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(sK0)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_17])).

cnf(c_9,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | k3_subset_1(X1,X0) = k4_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f51])).

cnf(c_586,plain,
    ( k3_subset_1(X0,X1) = k4_xboole_0(X0,X1)
    | m1_subset_1(X1,k1_zfmisc_1(X0)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_9])).

cnf(c_2001,plain,
    ( k3_subset_1(sK0,sK2) = k4_xboole_0(sK0,sK2) ),
    inference(superposition,[status(thm)],[c_579,c_586])).

cnf(c_18,negated_conjecture,
    ( m1_subset_1(sK1,k1_zfmisc_1(sK0)) ),
    inference(cnf_transformation,[],[f56])).

cnf(c_578,plain,
    ( m1_subset_1(sK1,k1_zfmisc_1(sK0)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_18])).

cnf(c_2002,plain,
    ( k3_subset_1(sK0,sK1) = k4_xboole_0(sK0,sK1) ),
    inference(superposition,[status(thm)],[c_578,c_586])).

cnf(c_3254,plain,
    ( k4_xboole_0(k4_xboole_0(sK0,sK2),k4_xboole_0(sK0,sK1)) = k4_xboole_0(sK0,sK2) ),
    inference(light_normalisation,[status(thm)],[c_1544,c_2001,c_2002])).

cnf(c_6,plain,
    ( k4_xboole_0(X0,k3_tarski(k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X2))) = k4_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X0,X2))) ),
    inference(cnf_transformation,[],[f70])).

cnf(c_4,plain,
    ( k4_xboole_0(X0,k3_tarski(k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X2))) = k4_xboole_0(k4_xboole_0(X0,X1),X2) ),
    inference(cnf_transformation,[],[f68])).

cnf(c_638,plain,
    ( k4_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X0,X2))) = k4_xboole_0(k4_xboole_0(X0,X1),X2) ),
    inference(light_normalisation,[status(thm)],[c_6,c_4])).

cnf(c_3261,plain,
    ( k4_xboole_0(k4_xboole_0(sK0,sK2),k4_xboole_0(sK0,sK2)) = k4_xboole_0(k4_xboole_0(sK0,sK2),sK1) ),
    inference(superposition,[status(thm)],[c_3254,c_638])).

cnf(c_1,plain,
    ( k4_xboole_0(X0,k4_xboole_0(X0,k1_xboole_0)) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f66])).

cnf(c_2,plain,
    ( k4_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(cnf_transformation,[],[f37])).

cnf(c_601,plain,
    ( k4_xboole_0(X0,X0) = k1_xboole_0 ),
    inference(light_normalisation,[status(thm)],[c_1,c_2])).

cnf(c_3263,plain,
    ( k4_xboole_0(k4_xboole_0(sK0,sK2),sK1) = k1_xboole_0 ),
    inference(demodulation,[status(thm)],[c_3261,c_601])).

cnf(c_11,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | k3_subset_1(X1,k3_subset_1(X1,X0)) = X0 ),
    inference(cnf_transformation,[],[f53])).

cnf(c_584,plain,
    ( k3_subset_1(X0,k3_subset_1(X0,X1)) = X1
    | m1_subset_1(X1,k1_zfmisc_1(X0)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_11])).

cnf(c_1838,plain,
    ( k3_subset_1(sK0,k3_subset_1(sK0,sK2)) = sK2 ),
    inference(superposition,[status(thm)],[c_579,c_584])).

cnf(c_13,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | ~ m1_subset_1(X2,k1_zfmisc_1(X1))
    | r1_tarski(X0,X2)
    | ~ r1_xboole_0(X0,k3_subset_1(X1,X2)) ),
    inference(cnf_transformation,[],[f54])).

cnf(c_582,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(X1)) != iProver_top
    | m1_subset_1(X2,k1_zfmisc_1(X1)) != iProver_top
    | r1_tarski(X0,X2) = iProver_top
    | r1_xboole_0(X0,k3_subset_1(X1,X2)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_13])).

cnf(c_2087,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(sK0)) != iProver_top
    | m1_subset_1(k3_subset_1(sK0,sK2),k1_zfmisc_1(sK0)) != iProver_top
    | r1_tarski(X0,k3_subset_1(sK0,sK2)) = iProver_top
    | r1_xboole_0(X0,sK2) != iProver_top ),
    inference(superposition,[status(thm)],[c_1838,c_582])).

cnf(c_20,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(sK0)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_17])).

cnf(c_10,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | m1_subset_1(k3_subset_1(X1,X0),k1_zfmisc_1(X1)) ),
    inference(cnf_transformation,[],[f52])).

cnf(c_711,plain,
    ( m1_subset_1(k3_subset_1(sK0,sK2),k1_zfmisc_1(sK0))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(sK0)) ),
    inference(instantiation,[status(thm)],[c_10])).

cnf(c_712,plain,
    ( m1_subset_1(k3_subset_1(sK0,sK2),k1_zfmisc_1(sK0)) = iProver_top
    | m1_subset_1(sK2,k1_zfmisc_1(sK0)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_711])).

cnf(c_4677,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(sK0)) != iProver_top
    | r1_tarski(X0,k3_subset_1(sK0,sK2)) = iProver_top
    | r1_xboole_0(X0,sK2) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_2087,c_20,c_712])).

cnf(c_4683,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(sK0)) != iProver_top
    | r1_tarski(X0,k4_xboole_0(sK0,sK2)) = iProver_top
    | r1_xboole_0(X0,sK2) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_4677,c_2001])).

cnf(c_5,plain,
    ( ~ r1_tarski(X0,X1)
    | k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,k4_xboole_0(X1,X0))) = X1 ),
    inference(cnf_transformation,[],[f69])).

cnf(c_589,plain,
    ( k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,k4_xboole_0(X1,X0))) = X1
    | r1_tarski(X0,X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_5])).

cnf(c_21928,plain,
    ( k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,k4_xboole_0(k4_xboole_0(sK0,sK2),X0))) = k4_xboole_0(sK0,sK2)
    | m1_subset_1(X0,k1_zfmisc_1(sK0)) != iProver_top
    | r1_xboole_0(X0,sK2) != iProver_top ),
    inference(superposition,[status(thm)],[c_4683,c_589])).

cnf(c_23085,plain,
    ( k3_tarski(k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,k4_xboole_0(k4_xboole_0(sK0,sK2),sK1))) = k4_xboole_0(sK0,sK2)
    | r1_xboole_0(sK1,sK2) != iProver_top ),
    inference(superposition,[status(thm)],[c_578,c_21928])).

cnf(c_16,negated_conjecture,
    ( r1_xboole_0(sK1,sK2) ),
    inference(cnf_transformation,[],[f58])).

cnf(c_21,plain,
    ( r1_xboole_0(sK1,sK2) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_16])).

cnf(c_23290,plain,
    ( k3_tarski(k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,k4_xboole_0(k4_xboole_0(sK0,sK2),sK1))) = k4_xboole_0(sK0,sK2) ),
    inference(global_propositional_subsumption,[status(thm)],[c_23085,c_21])).

cnf(c_32285,plain,
    ( k3_tarski(k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,k1_xboole_0)) = k4_xboole_0(sK0,sK2) ),
    inference(demodulation,[status(thm)],[c_3263,c_23290])).

cnf(c_3,plain,
    ( k4_xboole_0(k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)),X1) = k4_xboole_0(X0,X1) ),
    inference(cnf_transformation,[],[f67])).

cnf(c_982,plain,
    ( k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,k1_xboole_0)) = k4_xboole_0(X0,k1_xboole_0) ),
    inference(superposition,[status(thm)],[c_2,c_3])).

cnf(c_984,plain,
    ( k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,k1_xboole_0)) = X0 ),
    inference(light_normalisation,[status(thm)],[c_982,c_2])).

cnf(c_32287,plain,
    ( k4_xboole_0(sK0,sK2) = sK1 ),
    inference(demodulation,[status(thm)],[c_32285,c_984])).

cnf(c_14,negated_conjecture,
    ( k3_subset_1(sK0,sK2) != sK1 ),
    inference(cnf_transformation,[],[f60])).

cnf(c_2229,plain,
    ( k4_xboole_0(sK0,sK2) != sK1 ),
    inference(demodulation,[status(thm)],[c_2001,c_14])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_32287,c_2229])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : iproveropt_run.sh %d %s
% 0.15/0.34  % Computer   : n017.cluster.edu
% 0.15/0.34  % Model      : x86_64 x86_64
% 0.15/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.15/0.34  % Memory     : 8042.1875MB
% 0.15/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.15/0.34  % CPULimit   : 60
% 0.15/0.34  % WCLimit    : 600
% 0.15/0.34  % DateTime   : Tue Dec  1 19:59:47 EST 2020
% 0.15/0.35  % CPUTime    : 
% 0.15/0.35  % Running in FOF mode
% 7.23/1.55  % SZS status Started for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 7.23/1.55  
% 7.23/1.55  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 7.23/1.55  
% 7.23/1.55  ------  iProver source info
% 7.23/1.55  
% 7.23/1.55  git: date: 2020-06-30 10:37:57 +0100
% 7.23/1.55  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 7.23/1.55  git: non_committed_changes: false
% 7.23/1.55  git: last_make_outside_of_git: false
% 7.23/1.55  
% 7.23/1.55  ------ 
% 7.23/1.55  
% 7.23/1.55  ------ Input Options
% 7.23/1.55  
% 7.23/1.55  --out_options                           all
% 7.23/1.55  --tptp_safe_out                         true
% 7.23/1.55  --problem_path                          ""
% 7.23/1.55  --include_path                          ""
% 7.23/1.55  --clausifier                            res/vclausify_rel
% 7.23/1.55  --clausifier_options                    --mode clausify
% 7.23/1.55  --stdin                                 false
% 7.23/1.55  --stats_out                             all
% 7.23/1.55  
% 7.23/1.55  ------ General Options
% 7.23/1.55  
% 7.23/1.55  --fof                                   false
% 7.23/1.55  --time_out_real                         305.
% 7.23/1.55  --time_out_virtual                      -1.
% 7.23/1.55  --symbol_type_check                     false
% 7.23/1.55  --clausify_out                          false
% 7.23/1.55  --sig_cnt_out                           false
% 7.23/1.55  --trig_cnt_out                          false
% 7.23/1.55  --trig_cnt_out_tolerance                1.
% 7.23/1.55  --trig_cnt_out_sk_spl                   false
% 7.23/1.55  --abstr_cl_out                          false
% 7.23/1.55  
% 7.23/1.55  ------ Global Options
% 7.23/1.55  
% 7.23/1.55  --schedule                              default
% 7.23/1.55  --add_important_lit                     false
% 7.23/1.55  --prop_solver_per_cl                    1000
% 7.23/1.55  --min_unsat_core                        false
% 7.23/1.55  --soft_assumptions                      false
% 7.23/1.55  --soft_lemma_size                       3
% 7.23/1.55  --prop_impl_unit_size                   0
% 7.23/1.55  --prop_impl_unit                        []
% 7.23/1.55  --share_sel_clauses                     true
% 7.23/1.55  --reset_solvers                         false
% 7.23/1.55  --bc_imp_inh                            [conj_cone]
% 7.23/1.55  --conj_cone_tolerance                   3.
% 7.23/1.55  --extra_neg_conj                        none
% 7.23/1.55  --large_theory_mode                     true
% 7.23/1.55  --prolific_symb_bound                   200
% 7.23/1.55  --lt_threshold                          2000
% 7.23/1.55  --clause_weak_htbl                      true
% 7.23/1.55  --gc_record_bc_elim                     false
% 7.23/1.55  
% 7.23/1.55  ------ Preprocessing Options
% 7.23/1.55  
% 7.23/1.55  --preprocessing_flag                    true
% 7.23/1.55  --time_out_prep_mult                    0.1
% 7.23/1.55  --splitting_mode                        input
% 7.23/1.55  --splitting_grd                         true
% 7.23/1.55  --splitting_cvd                         false
% 7.23/1.55  --splitting_cvd_svl                     false
% 7.23/1.55  --splitting_nvd                         32
% 7.23/1.55  --sub_typing                            true
% 7.23/1.55  --prep_gs_sim                           true
% 7.23/1.55  --prep_unflatten                        true
% 7.23/1.55  --prep_res_sim                          true
% 7.23/1.55  --prep_upred                            true
% 7.23/1.55  --prep_sem_filter                       exhaustive
% 7.23/1.55  --prep_sem_filter_out                   false
% 7.23/1.55  --pred_elim                             true
% 7.23/1.55  --res_sim_input                         true
% 7.23/1.55  --eq_ax_congr_red                       true
% 7.23/1.55  --pure_diseq_elim                       true
% 7.23/1.55  --brand_transform                       false
% 7.23/1.55  --non_eq_to_eq                          false
% 7.23/1.55  --prep_def_merge                        true
% 7.23/1.55  --prep_def_merge_prop_impl              false
% 7.23/1.55  --prep_def_merge_mbd                    true
% 7.23/1.55  --prep_def_merge_tr_red                 false
% 7.23/1.55  --prep_def_merge_tr_cl                  false
% 7.23/1.55  --smt_preprocessing                     true
% 7.23/1.55  --smt_ac_axioms                         fast
% 7.23/1.55  --preprocessed_out                      false
% 7.23/1.55  --preprocessed_stats                    false
% 7.23/1.55  
% 7.23/1.55  ------ Abstraction refinement Options
% 7.23/1.55  
% 7.23/1.55  --abstr_ref                             []
% 7.23/1.55  --abstr_ref_prep                        false
% 7.23/1.55  --abstr_ref_until_sat                   false
% 7.23/1.55  --abstr_ref_sig_restrict                funpre
% 7.23/1.55  --abstr_ref_af_restrict_to_split_sk     false
% 7.23/1.55  --abstr_ref_under                       []
% 7.23/1.55  
% 7.23/1.55  ------ SAT Options
% 7.23/1.55  
% 7.23/1.55  --sat_mode                              false
% 7.23/1.55  --sat_fm_restart_options                ""
% 7.23/1.55  --sat_gr_def                            false
% 7.23/1.55  --sat_epr_types                         true
% 7.23/1.55  --sat_non_cyclic_types                  false
% 7.23/1.55  --sat_finite_models                     false
% 7.23/1.55  --sat_fm_lemmas                         false
% 7.23/1.55  --sat_fm_prep                           false
% 7.23/1.55  --sat_fm_uc_incr                        true
% 7.23/1.55  --sat_out_model                         small
% 7.23/1.55  --sat_out_clauses                       false
% 7.23/1.55  
% 7.23/1.55  ------ QBF Options
% 7.23/1.55  
% 7.23/1.55  --qbf_mode                              false
% 7.23/1.55  --qbf_elim_univ                         false
% 7.23/1.55  --qbf_dom_inst                          none
% 7.23/1.55  --qbf_dom_pre_inst                      false
% 7.23/1.55  --qbf_sk_in                             false
% 7.23/1.55  --qbf_pred_elim                         true
% 7.23/1.55  --qbf_split                             512
% 7.23/1.55  
% 7.23/1.55  ------ BMC1 Options
% 7.23/1.55  
% 7.23/1.55  --bmc1_incremental                      false
% 7.23/1.55  --bmc1_axioms                           reachable_all
% 7.23/1.55  --bmc1_min_bound                        0
% 7.23/1.55  --bmc1_max_bound                        -1
% 7.23/1.55  --bmc1_max_bound_default                -1
% 7.23/1.55  --bmc1_symbol_reachability              true
% 7.23/1.55  --bmc1_property_lemmas                  false
% 7.23/1.55  --bmc1_k_induction                      false
% 7.23/1.55  --bmc1_non_equiv_states                 false
% 7.23/1.55  --bmc1_deadlock                         false
% 7.23/1.55  --bmc1_ucm                              false
% 7.23/1.55  --bmc1_add_unsat_core                   none
% 7.23/1.55  --bmc1_unsat_core_children              false
% 7.23/1.55  --bmc1_unsat_core_extrapolate_axioms    false
% 7.23/1.55  --bmc1_out_stat                         full
% 7.23/1.55  --bmc1_ground_init                      false
% 7.23/1.55  --bmc1_pre_inst_next_state              false
% 7.23/1.55  --bmc1_pre_inst_state                   false
% 7.23/1.55  --bmc1_pre_inst_reach_state             false
% 7.23/1.55  --bmc1_out_unsat_core                   false
% 7.23/1.55  --bmc1_aig_witness_out                  false
% 7.23/1.55  --bmc1_verbose                          false
% 7.23/1.55  --bmc1_dump_clauses_tptp                false
% 7.23/1.55  --bmc1_dump_unsat_core_tptp             false
% 7.23/1.55  --bmc1_dump_file                        -
% 7.23/1.55  --bmc1_ucm_expand_uc_limit              128
% 7.23/1.55  --bmc1_ucm_n_expand_iterations          6
% 7.23/1.55  --bmc1_ucm_extend_mode                  1
% 7.23/1.55  --bmc1_ucm_init_mode                    2
% 7.23/1.55  --bmc1_ucm_cone_mode                    none
% 7.23/1.55  --bmc1_ucm_reduced_relation_type        0
% 7.23/1.55  --bmc1_ucm_relax_model                  4
% 7.23/1.55  --bmc1_ucm_full_tr_after_sat            true
% 7.23/1.55  --bmc1_ucm_expand_neg_assumptions       false
% 7.23/1.55  --bmc1_ucm_layered_model                none
% 7.23/1.55  --bmc1_ucm_max_lemma_size               10
% 7.23/1.55  
% 7.23/1.55  ------ AIG Options
% 7.23/1.55  
% 7.23/1.55  --aig_mode                              false
% 7.23/1.55  
% 7.23/1.55  ------ Instantiation Options
% 7.23/1.55  
% 7.23/1.55  --instantiation_flag                    true
% 7.23/1.55  --inst_sos_flag                         false
% 7.23/1.55  --inst_sos_phase                        true
% 7.23/1.55  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 7.23/1.55  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 7.23/1.55  --inst_lit_sel_side                     num_symb
% 7.23/1.55  --inst_solver_per_active                1400
% 7.23/1.55  --inst_solver_calls_frac                1.
% 7.23/1.55  --inst_passive_queue_type               priority_queues
% 7.23/1.55  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 7.23/1.55  --inst_passive_queues_freq              [25;2]
% 7.23/1.55  --inst_dismatching                      true
% 7.23/1.55  --inst_eager_unprocessed_to_passive     true
% 7.23/1.55  --inst_prop_sim_given                   true
% 7.23/1.55  --inst_prop_sim_new                     false
% 7.23/1.55  --inst_subs_new                         false
% 7.23/1.56  --inst_eq_res_simp                      false
% 7.23/1.56  --inst_subs_given                       false
% 7.23/1.56  --inst_orphan_elimination               true
% 7.23/1.56  --inst_learning_loop_flag               true
% 7.23/1.56  --inst_learning_start                   3000
% 7.23/1.56  --inst_learning_factor                  2
% 7.23/1.56  --inst_start_prop_sim_after_learn       3
% 7.23/1.56  --inst_sel_renew                        solver
% 7.23/1.56  --inst_lit_activity_flag                true
% 7.23/1.56  --inst_restr_to_given                   false
% 7.23/1.56  --inst_activity_threshold               500
% 7.23/1.56  --inst_out_proof                        true
% 7.23/1.56  
% 7.23/1.56  ------ Resolution Options
% 7.23/1.56  
% 7.23/1.56  --resolution_flag                       true
% 7.23/1.56  --res_lit_sel                           adaptive
% 7.23/1.56  --res_lit_sel_side                      none
% 7.23/1.56  --res_ordering                          kbo
% 7.23/1.56  --res_to_prop_solver                    active
% 7.23/1.56  --res_prop_simpl_new                    false
% 7.23/1.56  --res_prop_simpl_given                  true
% 7.23/1.56  --res_passive_queue_type                priority_queues
% 7.23/1.56  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 7.23/1.56  --res_passive_queues_freq               [15;5]
% 7.23/1.56  --res_forward_subs                      full
% 7.23/1.56  --res_backward_subs                     full
% 7.23/1.56  --res_forward_subs_resolution           true
% 7.23/1.56  --res_backward_subs_resolution          true
% 7.23/1.56  --res_orphan_elimination                true
% 7.23/1.56  --res_time_limit                        2.
% 7.23/1.56  --res_out_proof                         true
% 7.23/1.56  
% 7.23/1.56  ------ Superposition Options
% 7.23/1.56  
% 7.23/1.56  --superposition_flag                    true
% 7.23/1.56  --sup_passive_queue_type                priority_queues
% 7.23/1.56  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 7.23/1.56  --sup_passive_queues_freq               [8;1;4]
% 7.23/1.56  --demod_completeness_check              fast
% 7.23/1.56  --demod_use_ground                      true
% 7.23/1.56  --sup_to_prop_solver                    passive
% 7.23/1.56  --sup_prop_simpl_new                    true
% 7.23/1.56  --sup_prop_simpl_given                  true
% 7.23/1.56  --sup_fun_splitting                     false
% 7.23/1.56  --sup_smt_interval                      50000
% 7.23/1.56  
% 7.23/1.56  ------ Superposition Simplification Setup
% 7.23/1.56  
% 7.23/1.56  --sup_indices_passive                   []
% 7.23/1.56  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 7.23/1.56  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 7.23/1.56  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 7.23/1.56  --sup_full_triv                         [TrivRules;PropSubs]
% 7.23/1.56  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 7.23/1.56  --sup_full_bw                           [BwDemod]
% 7.23/1.56  --sup_immed_triv                        [TrivRules]
% 7.23/1.56  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 7.23/1.56  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 7.23/1.56  --sup_immed_bw_main                     []
% 7.23/1.56  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 7.23/1.56  --sup_input_triv                        [Unflattening;TrivRules]
% 7.23/1.56  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 7.23/1.56  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 7.23/1.56  
% 7.23/1.56  ------ Combination Options
% 7.23/1.56  
% 7.23/1.56  --comb_res_mult                         3
% 7.23/1.56  --comb_sup_mult                         2
% 7.23/1.56  --comb_inst_mult                        10
% 7.23/1.56  
% 7.23/1.56  ------ Debug Options
% 7.23/1.56  
% 7.23/1.56  --dbg_backtrace                         false
% 7.23/1.56  --dbg_dump_prop_clauses                 false
% 7.23/1.56  --dbg_dump_prop_clauses_file            -
% 7.23/1.56  --dbg_out_stat                          false
% 7.23/1.56  ------ Parsing...
% 7.23/1.56  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 7.23/1.56  
% 7.23/1.56  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe_e 
% 7.23/1.56  
% 7.23/1.56  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 7.23/1.56  
% 7.23/1.56  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 7.23/1.56  ------ Proving...
% 7.23/1.56  ------ Problem Properties 
% 7.23/1.56  
% 7.23/1.56  
% 7.23/1.56  clauses                                 19
% 7.23/1.56  conjectures                             5
% 7.23/1.56  EPR                                     2
% 7.23/1.56  Horn                                    19
% 7.23/1.56  unary                                   10
% 7.23/1.56  binary                                  7
% 7.23/1.56  lits                                    32
% 7.23/1.56  lits eq                                 11
% 7.23/1.56  fd_pure                                 0
% 7.23/1.56  fd_pseudo                               0
% 7.23/1.56  fd_cond                                 0
% 7.23/1.56  fd_pseudo_cond                          0
% 7.23/1.56  AC symbols                              0
% 7.23/1.56  
% 7.23/1.56  ------ Schedule dynamic 5 is on 
% 7.23/1.56  
% 7.23/1.56  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" Time Limit: 10.
% 7.23/1.56  
% 7.23/1.56  
% 7.23/1.56  ------ 
% 7.23/1.56  Current options:
% 7.23/1.56  ------ 
% 7.23/1.56  
% 7.23/1.56  ------ Input Options
% 7.23/1.56  
% 7.23/1.56  --out_options                           all
% 7.23/1.56  --tptp_safe_out                         true
% 7.23/1.56  --problem_path                          ""
% 7.23/1.56  --include_path                          ""
% 7.23/1.56  --clausifier                            res/vclausify_rel
% 7.23/1.56  --clausifier_options                    --mode clausify
% 7.23/1.56  --stdin                                 false
% 7.23/1.56  --stats_out                             all
% 7.23/1.56  
% 7.23/1.56  ------ General Options
% 7.23/1.56  
% 7.23/1.56  --fof                                   false
% 7.23/1.56  --time_out_real                         305.
% 7.23/1.56  --time_out_virtual                      -1.
% 7.23/1.56  --symbol_type_check                     false
% 7.23/1.56  --clausify_out                          false
% 7.23/1.56  --sig_cnt_out                           false
% 7.23/1.56  --trig_cnt_out                          false
% 7.23/1.56  --trig_cnt_out_tolerance                1.
% 7.23/1.56  --trig_cnt_out_sk_spl                   false
% 7.23/1.56  --abstr_cl_out                          false
% 7.23/1.56  
% 7.23/1.56  ------ Global Options
% 7.23/1.56  
% 7.23/1.56  --schedule                              default
% 7.23/1.56  --add_important_lit                     false
% 7.23/1.56  --prop_solver_per_cl                    1000
% 7.23/1.56  --min_unsat_core                        false
% 7.23/1.56  --soft_assumptions                      false
% 7.23/1.56  --soft_lemma_size                       3
% 7.23/1.56  --prop_impl_unit_size                   0
% 7.23/1.56  --prop_impl_unit                        []
% 7.23/1.56  --share_sel_clauses                     true
% 7.23/1.56  --reset_solvers                         false
% 7.23/1.56  --bc_imp_inh                            [conj_cone]
% 7.23/1.56  --conj_cone_tolerance                   3.
% 7.23/1.56  --extra_neg_conj                        none
% 7.23/1.56  --large_theory_mode                     true
% 7.23/1.56  --prolific_symb_bound                   200
% 7.23/1.56  --lt_threshold                          2000
% 7.23/1.56  --clause_weak_htbl                      true
% 7.23/1.56  --gc_record_bc_elim                     false
% 7.23/1.56  
% 7.23/1.56  ------ Preprocessing Options
% 7.23/1.56  
% 7.23/1.56  --preprocessing_flag                    true
% 7.23/1.56  --time_out_prep_mult                    0.1
% 7.23/1.56  --splitting_mode                        input
% 7.23/1.56  --splitting_grd                         true
% 7.23/1.56  --splitting_cvd                         false
% 7.23/1.56  --splitting_cvd_svl                     false
% 7.23/1.56  --splitting_nvd                         32
% 7.23/1.56  --sub_typing                            true
% 7.23/1.56  --prep_gs_sim                           true
% 7.23/1.56  --prep_unflatten                        true
% 7.23/1.56  --prep_res_sim                          true
% 7.23/1.56  --prep_upred                            true
% 7.23/1.56  --prep_sem_filter                       exhaustive
% 7.23/1.56  --prep_sem_filter_out                   false
% 7.23/1.56  --pred_elim                             true
% 7.23/1.56  --res_sim_input                         true
% 7.23/1.56  --eq_ax_congr_red                       true
% 7.23/1.56  --pure_diseq_elim                       true
% 7.23/1.56  --brand_transform                       false
% 7.23/1.56  --non_eq_to_eq                          false
% 7.23/1.56  --prep_def_merge                        true
% 7.23/1.56  --prep_def_merge_prop_impl              false
% 7.23/1.56  --prep_def_merge_mbd                    true
% 7.23/1.56  --prep_def_merge_tr_red                 false
% 7.23/1.56  --prep_def_merge_tr_cl                  false
% 7.23/1.56  --smt_preprocessing                     true
% 7.23/1.56  --smt_ac_axioms                         fast
% 7.23/1.56  --preprocessed_out                      false
% 7.23/1.56  --preprocessed_stats                    false
% 7.23/1.56  
% 7.23/1.56  ------ Abstraction refinement Options
% 7.23/1.56  
% 7.23/1.56  --abstr_ref                             []
% 7.23/1.56  --abstr_ref_prep                        false
% 7.23/1.56  --abstr_ref_until_sat                   false
% 7.23/1.56  --abstr_ref_sig_restrict                funpre
% 7.23/1.56  --abstr_ref_af_restrict_to_split_sk     false
% 7.23/1.56  --abstr_ref_under                       []
% 7.23/1.56  
% 7.23/1.56  ------ SAT Options
% 7.23/1.56  
% 7.23/1.56  --sat_mode                              false
% 7.23/1.56  --sat_fm_restart_options                ""
% 7.23/1.56  --sat_gr_def                            false
% 7.23/1.56  --sat_epr_types                         true
% 7.23/1.56  --sat_non_cyclic_types                  false
% 7.23/1.56  --sat_finite_models                     false
% 7.23/1.56  --sat_fm_lemmas                         false
% 7.23/1.56  --sat_fm_prep                           false
% 7.23/1.56  --sat_fm_uc_incr                        true
% 7.23/1.56  --sat_out_model                         small
% 7.23/1.56  --sat_out_clauses                       false
% 7.23/1.56  
% 7.23/1.56  ------ QBF Options
% 7.23/1.56  
% 7.23/1.56  --qbf_mode                              false
% 7.23/1.56  --qbf_elim_univ                         false
% 7.23/1.56  --qbf_dom_inst                          none
% 7.23/1.56  --qbf_dom_pre_inst                      false
% 7.23/1.56  --qbf_sk_in                             false
% 7.23/1.56  --qbf_pred_elim                         true
% 7.23/1.56  --qbf_split                             512
% 7.23/1.56  
% 7.23/1.56  ------ BMC1 Options
% 7.23/1.56  
% 7.23/1.56  --bmc1_incremental                      false
% 7.23/1.56  --bmc1_axioms                           reachable_all
% 7.23/1.56  --bmc1_min_bound                        0
% 7.23/1.56  --bmc1_max_bound                        -1
% 7.23/1.56  --bmc1_max_bound_default                -1
% 7.23/1.56  --bmc1_symbol_reachability              true
% 7.23/1.56  --bmc1_property_lemmas                  false
% 7.23/1.56  --bmc1_k_induction                      false
% 7.23/1.56  --bmc1_non_equiv_states                 false
% 7.23/1.56  --bmc1_deadlock                         false
% 7.23/1.56  --bmc1_ucm                              false
% 7.23/1.56  --bmc1_add_unsat_core                   none
% 7.23/1.56  --bmc1_unsat_core_children              false
% 7.23/1.56  --bmc1_unsat_core_extrapolate_axioms    false
% 7.23/1.56  --bmc1_out_stat                         full
% 7.23/1.56  --bmc1_ground_init                      false
% 7.23/1.56  --bmc1_pre_inst_next_state              false
% 7.23/1.56  --bmc1_pre_inst_state                   false
% 7.23/1.56  --bmc1_pre_inst_reach_state             false
% 7.23/1.56  --bmc1_out_unsat_core                   false
% 7.23/1.56  --bmc1_aig_witness_out                  false
% 7.23/1.56  --bmc1_verbose                          false
% 7.23/1.56  --bmc1_dump_clauses_tptp                false
% 7.23/1.56  --bmc1_dump_unsat_core_tptp             false
% 7.23/1.56  --bmc1_dump_file                        -
% 7.23/1.56  --bmc1_ucm_expand_uc_limit              128
% 7.23/1.56  --bmc1_ucm_n_expand_iterations          6
% 7.23/1.56  --bmc1_ucm_extend_mode                  1
% 7.23/1.56  --bmc1_ucm_init_mode                    2
% 7.23/1.56  --bmc1_ucm_cone_mode                    none
% 7.23/1.56  --bmc1_ucm_reduced_relation_type        0
% 7.23/1.56  --bmc1_ucm_relax_model                  4
% 7.23/1.56  --bmc1_ucm_full_tr_after_sat            true
% 7.23/1.56  --bmc1_ucm_expand_neg_assumptions       false
% 7.23/1.56  --bmc1_ucm_layered_model                none
% 7.23/1.56  --bmc1_ucm_max_lemma_size               10
% 7.23/1.56  
% 7.23/1.56  ------ AIG Options
% 7.23/1.56  
% 7.23/1.56  --aig_mode                              false
% 7.23/1.56  
% 7.23/1.56  ------ Instantiation Options
% 7.23/1.56  
% 7.23/1.56  --instantiation_flag                    true
% 7.23/1.56  --inst_sos_flag                         false
% 7.23/1.56  --inst_sos_phase                        true
% 7.23/1.56  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 7.23/1.56  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 7.23/1.56  --inst_lit_sel_side                     none
% 7.23/1.56  --inst_solver_per_active                1400
% 7.23/1.56  --inst_solver_calls_frac                1.
% 7.23/1.56  --inst_passive_queue_type               priority_queues
% 7.23/1.56  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 7.23/1.56  --inst_passive_queues_freq              [25;2]
% 7.23/1.56  --inst_dismatching                      true
% 7.23/1.56  --inst_eager_unprocessed_to_passive     true
% 7.23/1.56  --inst_prop_sim_given                   true
% 7.23/1.56  --inst_prop_sim_new                     false
% 7.23/1.56  --inst_subs_new                         false
% 7.23/1.56  --inst_eq_res_simp                      false
% 7.23/1.56  --inst_subs_given                       false
% 7.23/1.56  --inst_orphan_elimination               true
% 7.23/1.56  --inst_learning_loop_flag               true
% 7.23/1.56  --inst_learning_start                   3000
% 7.23/1.56  --inst_learning_factor                  2
% 7.23/1.56  --inst_start_prop_sim_after_learn       3
% 7.23/1.56  --inst_sel_renew                        solver
% 7.23/1.56  --inst_lit_activity_flag                true
% 7.23/1.56  --inst_restr_to_given                   false
% 7.23/1.56  --inst_activity_threshold               500
% 7.23/1.56  --inst_out_proof                        true
% 7.23/1.56  
% 7.23/1.56  ------ Resolution Options
% 7.23/1.56  
% 7.23/1.56  --resolution_flag                       false
% 7.23/1.56  --res_lit_sel                           adaptive
% 7.23/1.56  --res_lit_sel_side                      none
% 7.23/1.56  --res_ordering                          kbo
% 7.23/1.56  --res_to_prop_solver                    active
% 7.23/1.56  --res_prop_simpl_new                    false
% 7.23/1.56  --res_prop_simpl_given                  true
% 7.23/1.56  --res_passive_queue_type                priority_queues
% 7.23/1.56  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 7.23/1.56  --res_passive_queues_freq               [15;5]
% 7.23/1.56  --res_forward_subs                      full
% 7.23/1.56  --res_backward_subs                     full
% 7.23/1.56  --res_forward_subs_resolution           true
% 7.23/1.56  --res_backward_subs_resolution          true
% 7.23/1.56  --res_orphan_elimination                true
% 7.23/1.56  --res_time_limit                        2.
% 7.23/1.56  --res_out_proof                         true
% 7.23/1.56  
% 7.23/1.56  ------ Superposition Options
% 7.23/1.56  
% 7.23/1.56  --superposition_flag                    true
% 7.23/1.56  --sup_passive_queue_type                priority_queues
% 7.23/1.56  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 7.23/1.56  --sup_passive_queues_freq               [8;1;4]
% 7.23/1.56  --demod_completeness_check              fast
% 7.23/1.56  --demod_use_ground                      true
% 7.23/1.56  --sup_to_prop_solver                    passive
% 7.23/1.56  --sup_prop_simpl_new                    true
% 7.23/1.56  --sup_prop_simpl_given                  true
% 7.23/1.56  --sup_fun_splitting                     false
% 7.23/1.56  --sup_smt_interval                      50000
% 7.23/1.56  
% 7.23/1.56  ------ Superposition Simplification Setup
% 7.23/1.56  
% 7.23/1.56  --sup_indices_passive                   []
% 7.23/1.56  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 7.23/1.56  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 7.23/1.56  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 7.23/1.56  --sup_full_triv                         [TrivRules;PropSubs]
% 7.23/1.56  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 7.23/1.56  --sup_full_bw                           [BwDemod]
% 7.23/1.56  --sup_immed_triv                        [TrivRules]
% 7.23/1.56  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 7.23/1.56  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 7.23/1.56  --sup_immed_bw_main                     []
% 7.23/1.56  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 7.23/1.56  --sup_input_triv                        [Unflattening;TrivRules]
% 7.23/1.56  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 7.23/1.56  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 7.23/1.56  
% 7.23/1.56  ------ Combination Options
% 7.23/1.56  
% 7.23/1.56  --comb_res_mult                         3
% 7.23/1.56  --comb_sup_mult                         2
% 7.23/1.56  --comb_inst_mult                        10
% 7.23/1.56  
% 7.23/1.56  ------ Debug Options
% 7.23/1.56  
% 7.23/1.56  --dbg_backtrace                         false
% 7.23/1.56  --dbg_dump_prop_clauses                 false
% 7.23/1.56  --dbg_dump_prop_clauses_file            -
% 7.23/1.56  --dbg_out_stat                          false
% 7.23/1.56  
% 7.23/1.56  
% 7.23/1.56  
% 7.23/1.56  
% 7.23/1.56  ------ Proving...
% 7.23/1.56  
% 7.23/1.56  
% 7.23/1.56  % SZS status Theorem for theBenchmark.p
% 7.23/1.56  
% 7.23/1.56  % SZS output start CNFRefutation for theBenchmark.p
% 7.23/1.56  
% 7.23/1.56  fof(f20,conjecture,(
% 7.23/1.56    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(X0)) => ((r1_xboole_0(k3_subset_1(X0,X1),k3_subset_1(X0,X2)) & r1_xboole_0(X1,X2)) => k3_subset_1(X0,X2) = X1)))),
% 7.23/1.56    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.23/1.56  
% 7.23/1.56  fof(f21,negated_conjecture,(
% 7.23/1.56    ~! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(X0)) => ((r1_xboole_0(k3_subset_1(X0,X1),k3_subset_1(X0,X2)) & r1_xboole_0(X1,X2)) => k3_subset_1(X0,X2) = X1)))),
% 7.23/1.56    inference(negated_conjecture,[],[f20])).
% 7.23/1.56  
% 7.23/1.56  fof(f28,plain,(
% 7.23/1.56    ? [X0,X1] : (? [X2] : ((k3_subset_1(X0,X2) != X1 & (r1_xboole_0(k3_subset_1(X0,X1),k3_subset_1(X0,X2)) & r1_xboole_0(X1,X2))) & m1_subset_1(X2,k1_zfmisc_1(X0))) & m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 7.23/1.56    inference(ennf_transformation,[],[f21])).
% 7.23/1.56  
% 7.23/1.56  fof(f29,plain,(
% 7.23/1.56    ? [X0,X1] : (? [X2] : (k3_subset_1(X0,X2) != X1 & r1_xboole_0(k3_subset_1(X0,X1),k3_subset_1(X0,X2)) & r1_xboole_0(X1,X2) & m1_subset_1(X2,k1_zfmisc_1(X0))) & m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 7.23/1.56    inference(flattening,[],[f28])).
% 7.23/1.56  
% 7.23/1.56  fof(f33,plain,(
% 7.23/1.56    ( ! [X0,X1] : (? [X2] : (k3_subset_1(X0,X2) != X1 & r1_xboole_0(k3_subset_1(X0,X1),k3_subset_1(X0,X2)) & r1_xboole_0(X1,X2) & m1_subset_1(X2,k1_zfmisc_1(X0))) => (k3_subset_1(X0,sK2) != X1 & r1_xboole_0(k3_subset_1(X0,X1),k3_subset_1(X0,sK2)) & r1_xboole_0(X1,sK2) & m1_subset_1(sK2,k1_zfmisc_1(X0)))) )),
% 7.23/1.56    introduced(choice_axiom,[])).
% 7.23/1.56  
% 7.23/1.56  fof(f32,plain,(
% 7.23/1.56    ? [X0,X1] : (? [X2] : (k3_subset_1(X0,X2) != X1 & r1_xboole_0(k3_subset_1(X0,X1),k3_subset_1(X0,X2)) & r1_xboole_0(X1,X2) & m1_subset_1(X2,k1_zfmisc_1(X0))) & m1_subset_1(X1,k1_zfmisc_1(X0))) => (? [X2] : (k3_subset_1(sK0,X2) != sK1 & r1_xboole_0(k3_subset_1(sK0,sK1),k3_subset_1(sK0,X2)) & r1_xboole_0(sK1,X2) & m1_subset_1(X2,k1_zfmisc_1(sK0))) & m1_subset_1(sK1,k1_zfmisc_1(sK0)))),
% 7.23/1.56    introduced(choice_axiom,[])).
% 7.23/1.56  
% 7.23/1.56  fof(f34,plain,(
% 7.23/1.56    (k3_subset_1(sK0,sK2) != sK1 & r1_xboole_0(k3_subset_1(sK0,sK1),k3_subset_1(sK0,sK2)) & r1_xboole_0(sK1,sK2) & m1_subset_1(sK2,k1_zfmisc_1(sK0))) & m1_subset_1(sK1,k1_zfmisc_1(sK0))),
% 7.23/1.56    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f29,f33,f32])).
% 7.23/1.56  
% 7.23/1.56  fof(f59,plain,(
% 7.23/1.56    r1_xboole_0(k3_subset_1(sK0,sK1),k3_subset_1(sK0,sK2))),
% 7.23/1.56    inference(cnf_transformation,[],[f34])).
% 7.23/1.56  
% 7.23/1.56  fof(f1,axiom,(
% 7.23/1.56    ! [X0,X1] : (r1_xboole_0(X0,X1) => r1_xboole_0(X1,X0))),
% 7.23/1.56    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.23/1.56  
% 7.23/1.56  fof(f22,plain,(
% 7.23/1.56    ! [X0,X1] : (r1_xboole_0(X1,X0) | ~r1_xboole_0(X0,X1))),
% 7.23/1.56    inference(ennf_transformation,[],[f1])).
% 7.23/1.56  
% 7.23/1.56  fof(f35,plain,(
% 7.23/1.56    ( ! [X0,X1] : (r1_xboole_0(X1,X0) | ~r1_xboole_0(X0,X1)) )),
% 7.23/1.56    inference(cnf_transformation,[],[f22])).
% 7.23/1.56  
% 7.23/1.56  fof(f9,axiom,(
% 7.23/1.56    ! [X0,X1] : (r1_xboole_0(X0,X1) <=> k4_xboole_0(X0,X1) = X0)),
% 7.23/1.56    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.23/1.56  
% 7.23/1.56  fof(f30,plain,(
% 7.23/1.56    ! [X0,X1] : ((r1_xboole_0(X0,X1) | k4_xboole_0(X0,X1) != X0) & (k4_xboole_0(X0,X1) = X0 | ~r1_xboole_0(X0,X1)))),
% 7.23/1.56    inference(nnf_transformation,[],[f9])).
% 7.23/1.56  
% 7.23/1.56  fof(f43,plain,(
% 7.23/1.56    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = X0 | ~r1_xboole_0(X0,X1)) )),
% 7.23/1.56    inference(cnf_transformation,[],[f30])).
% 7.23/1.56  
% 7.23/1.56  fof(f57,plain,(
% 7.23/1.56    m1_subset_1(sK2,k1_zfmisc_1(sK0))),
% 7.23/1.56    inference(cnf_transformation,[],[f34])).
% 7.23/1.56  
% 7.23/1.56  fof(f16,axiom,(
% 7.23/1.56    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => k4_xboole_0(X0,X1) = k3_subset_1(X0,X1))),
% 7.23/1.56    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.23/1.56  
% 7.23/1.56  fof(f24,plain,(
% 7.23/1.56    ! [X0,X1] : (k4_xboole_0(X0,X1) = k3_subset_1(X0,X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 7.23/1.56    inference(ennf_transformation,[],[f16])).
% 7.23/1.56  
% 7.23/1.56  fof(f51,plain,(
% 7.23/1.56    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k3_subset_1(X0,X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 7.23/1.56    inference(cnf_transformation,[],[f24])).
% 7.23/1.56  
% 7.23/1.56  fof(f56,plain,(
% 7.23/1.56    m1_subset_1(sK1,k1_zfmisc_1(sK0))),
% 7.23/1.56    inference(cnf_transformation,[],[f34])).
% 7.23/1.56  
% 7.23/1.56  fof(f8,axiom,(
% 7.23/1.56    ! [X0,X1,X2] : k3_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X0,X2)) = k4_xboole_0(X0,k2_xboole_0(X1,X2))),
% 7.23/1.56    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.23/1.56  
% 7.23/1.56  fof(f42,plain,(
% 7.23/1.56    ( ! [X2,X0,X1] : (k3_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X0,X2)) = k4_xboole_0(X0,k2_xboole_0(X1,X2))) )),
% 7.23/1.56    inference(cnf_transformation,[],[f8])).
% 7.23/1.56  
% 7.23/1.56  fof(f7,axiom,(
% 7.23/1.56    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1))),
% 7.23/1.56    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.23/1.56  
% 7.23/1.56  fof(f41,plain,(
% 7.23/1.56    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1))) )),
% 7.23/1.56    inference(cnf_transformation,[],[f7])).
% 7.23/1.56  
% 7.23/1.56  fof(f15,axiom,(
% 7.23/1.56    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1))),
% 7.23/1.56    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.23/1.56  
% 7.23/1.56  fof(f50,plain,(
% 7.23/1.56    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1))) )),
% 7.23/1.56    inference(cnf_transformation,[],[f15])).
% 7.23/1.56  
% 7.23/1.56  fof(f14,axiom,(
% 7.23/1.56    ! [X0,X1] : k2_enumset1(X0,X0,X0,X1) = k2_tarski(X0,X1)),
% 7.23/1.56    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.23/1.56  
% 7.23/1.56  fof(f49,plain,(
% 7.23/1.56    ( ! [X0,X1] : (k2_enumset1(X0,X0,X0,X1) = k2_tarski(X0,X1)) )),
% 7.23/1.56    inference(cnf_transformation,[],[f14])).
% 7.23/1.56  
% 7.23/1.56  fof(f10,axiom,(
% 7.23/1.56    ! [X0,X1,X2,X3] : k3_enumset1(X0,X0,X1,X2,X3) = k2_enumset1(X0,X1,X2,X3)),
% 7.23/1.56    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.23/1.56  
% 7.23/1.56  fof(f45,plain,(
% 7.23/1.56    ( ! [X2,X0,X3,X1] : (k3_enumset1(X0,X0,X1,X2,X3) = k2_enumset1(X0,X1,X2,X3)) )),
% 7.23/1.56    inference(cnf_transformation,[],[f10])).
% 7.23/1.56  
% 7.23/1.56  fof(f11,axiom,(
% 7.23/1.56    ! [X0,X1,X2,X3,X4] : k3_enumset1(X0,X1,X2,X3,X4) = k4_enumset1(X0,X0,X1,X2,X3,X4)),
% 7.23/1.56    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.23/1.56  
% 7.23/1.56  fof(f46,plain,(
% 7.23/1.56    ( ! [X4,X2,X0,X3,X1] : (k3_enumset1(X0,X1,X2,X3,X4) = k4_enumset1(X0,X0,X1,X2,X3,X4)) )),
% 7.23/1.56    inference(cnf_transformation,[],[f11])).
% 7.23/1.56  
% 7.23/1.56  fof(f12,axiom,(
% 7.23/1.56    ! [X0,X1,X2,X3,X4,X5] : k4_enumset1(X0,X1,X2,X3,X4,X5) = k5_enumset1(X0,X0,X1,X2,X3,X4,X5)),
% 7.23/1.56    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.23/1.56  
% 7.23/1.56  fof(f47,plain,(
% 7.23/1.56    ( ! [X4,X2,X0,X5,X3,X1] : (k4_enumset1(X0,X1,X2,X3,X4,X5) = k5_enumset1(X0,X0,X1,X2,X3,X4,X5)) )),
% 7.23/1.56    inference(cnf_transformation,[],[f12])).
% 7.23/1.56  
% 7.23/1.56  fof(f13,axiom,(
% 7.23/1.56    ! [X0,X1,X2,X3,X4,X5,X6] : k5_enumset1(X0,X1,X2,X3,X4,X5,X6) = k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6)),
% 7.23/1.56    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.23/1.56  
% 7.23/1.56  fof(f48,plain,(
% 7.23/1.56    ( ! [X6,X4,X2,X0,X5,X3,X1] : (k5_enumset1(X0,X1,X2,X3,X4,X5,X6) = k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6)) )),
% 7.23/1.56    inference(cnf_transformation,[],[f13])).
% 7.23/1.56  
% 7.23/1.56  fof(f61,plain,(
% 7.23/1.56    ( ! [X4,X2,X0,X5,X3,X1] : (k4_enumset1(X0,X1,X2,X3,X4,X5) = k6_enumset1(X0,X0,X0,X1,X2,X3,X4,X5)) )),
% 7.23/1.56    inference(definition_unfolding,[],[f47,f48])).
% 7.23/1.56  
% 7.23/1.56  fof(f62,plain,(
% 7.23/1.56    ( ! [X4,X2,X0,X3,X1] : (k3_enumset1(X0,X1,X2,X3,X4) = k6_enumset1(X0,X0,X0,X0,X1,X2,X3,X4)) )),
% 7.23/1.56    inference(definition_unfolding,[],[f46,f61])).
% 7.23/1.56  
% 7.23/1.56  fof(f63,plain,(
% 7.23/1.56    ( ! [X2,X0,X3,X1] : (k2_enumset1(X0,X1,X2,X3) = k6_enumset1(X0,X0,X0,X0,X0,X1,X2,X3)) )),
% 7.23/1.56    inference(definition_unfolding,[],[f45,f62])).
% 7.23/1.56  
% 7.23/1.56  fof(f64,plain,(
% 7.23/1.56    ( ! [X0,X1] : (k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1) = k2_tarski(X0,X1)) )),
% 7.23/1.56    inference(definition_unfolding,[],[f49,f63])).
% 7.23/1.56  
% 7.23/1.56  fof(f65,plain,(
% 7.23/1.56    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1))) )),
% 7.23/1.56    inference(definition_unfolding,[],[f50,f64])).
% 7.23/1.56  
% 7.23/1.56  fof(f70,plain,(
% 7.23/1.56    ( ! [X2,X0,X1] : (k4_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X0,X2))) = k4_xboole_0(X0,k3_tarski(k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X2)))) )),
% 7.23/1.56    inference(definition_unfolding,[],[f42,f41,f65])).
% 7.23/1.56  
% 7.23/1.56  fof(f5,axiom,(
% 7.23/1.56    ! [X0,X1,X2] : k4_xboole_0(X0,k2_xboole_0(X1,X2)) = k4_xboole_0(k4_xboole_0(X0,X1),X2)),
% 7.23/1.56    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.23/1.56  
% 7.23/1.56  fof(f39,plain,(
% 7.23/1.56    ( ! [X2,X0,X1] : (k4_xboole_0(X0,k2_xboole_0(X1,X2)) = k4_xboole_0(k4_xboole_0(X0,X1),X2)) )),
% 7.23/1.56    inference(cnf_transformation,[],[f5])).
% 7.23/1.56  
% 7.23/1.56  fof(f68,plain,(
% 7.23/1.56    ( ! [X2,X0,X1] : (k4_xboole_0(k4_xboole_0(X0,X1),X2) = k4_xboole_0(X0,k3_tarski(k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X2)))) )),
% 7.23/1.56    inference(definition_unfolding,[],[f39,f65])).
% 7.23/1.56  
% 7.23/1.56  fof(f2,axiom,(
% 7.23/1.56    ! [X0] : k1_xboole_0 = k3_xboole_0(X0,k1_xboole_0)),
% 7.23/1.56    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.23/1.56  
% 7.23/1.56  fof(f36,plain,(
% 7.23/1.56    ( ! [X0] : (k1_xboole_0 = k3_xboole_0(X0,k1_xboole_0)) )),
% 7.23/1.56    inference(cnf_transformation,[],[f2])).
% 7.23/1.56  
% 7.23/1.56  fof(f66,plain,(
% 7.23/1.56    ( ! [X0] : (k1_xboole_0 = k4_xboole_0(X0,k4_xboole_0(X0,k1_xboole_0))) )),
% 7.23/1.56    inference(definition_unfolding,[],[f36,f41])).
% 7.23/1.56  
% 7.23/1.56  fof(f3,axiom,(
% 7.23/1.56    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0),
% 7.23/1.56    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.23/1.56  
% 7.23/1.56  fof(f37,plain,(
% 7.23/1.56    ( ! [X0] : (k4_xboole_0(X0,k1_xboole_0) = X0) )),
% 7.23/1.56    inference(cnf_transformation,[],[f3])).
% 7.23/1.56  
% 7.23/1.56  fof(f18,axiom,(
% 7.23/1.56    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => k3_subset_1(X0,k3_subset_1(X0,X1)) = X1)),
% 7.23/1.56    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.23/1.56  
% 7.23/1.56  fof(f26,plain,(
% 7.23/1.56    ! [X0,X1] : (k3_subset_1(X0,k3_subset_1(X0,X1)) = X1 | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 7.23/1.56    inference(ennf_transformation,[],[f18])).
% 7.23/1.56  
% 7.23/1.56  fof(f53,plain,(
% 7.23/1.56    ( ! [X0,X1] : (k3_subset_1(X0,k3_subset_1(X0,X1)) = X1 | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 7.23/1.56    inference(cnf_transformation,[],[f26])).
% 7.23/1.56  
% 7.23/1.56  fof(f19,axiom,(
% 7.23/1.56    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(X0)) => (r1_xboole_0(X1,k3_subset_1(X0,X2)) <=> r1_tarski(X1,X2))))),
% 7.23/1.56    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.23/1.56  
% 7.23/1.56  fof(f27,plain,(
% 7.23/1.56    ! [X0,X1] : (! [X2] : ((r1_xboole_0(X1,k3_subset_1(X0,X2)) <=> r1_tarski(X1,X2)) | ~m1_subset_1(X2,k1_zfmisc_1(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 7.23/1.56    inference(ennf_transformation,[],[f19])).
% 7.23/1.56  
% 7.23/1.56  fof(f31,plain,(
% 7.23/1.56    ! [X0,X1] : (! [X2] : (((r1_xboole_0(X1,k3_subset_1(X0,X2)) | ~r1_tarski(X1,X2)) & (r1_tarski(X1,X2) | ~r1_xboole_0(X1,k3_subset_1(X0,X2)))) | ~m1_subset_1(X2,k1_zfmisc_1(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 7.23/1.56    inference(nnf_transformation,[],[f27])).
% 7.23/1.56  
% 7.23/1.56  fof(f54,plain,(
% 7.23/1.56    ( ! [X2,X0,X1] : (r1_tarski(X1,X2) | ~r1_xboole_0(X1,k3_subset_1(X0,X2)) | ~m1_subset_1(X2,k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 7.23/1.56    inference(cnf_transformation,[],[f31])).
% 7.23/1.56  
% 7.23/1.56  fof(f17,axiom,(
% 7.23/1.56    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => m1_subset_1(k3_subset_1(X0,X1),k1_zfmisc_1(X0)))),
% 7.23/1.56    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.23/1.56  
% 7.23/1.56  fof(f25,plain,(
% 7.23/1.56    ! [X0,X1] : (m1_subset_1(k3_subset_1(X0,X1),k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 7.23/1.56    inference(ennf_transformation,[],[f17])).
% 7.23/1.56  
% 7.23/1.56  fof(f52,plain,(
% 7.23/1.56    ( ! [X0,X1] : (m1_subset_1(k3_subset_1(X0,X1),k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 7.23/1.56    inference(cnf_transformation,[],[f25])).
% 7.23/1.56  
% 7.23/1.56  fof(f6,axiom,(
% 7.23/1.56    ! [X0,X1] : (r1_tarski(X0,X1) => k2_xboole_0(X0,k4_xboole_0(X1,X0)) = X1)),
% 7.23/1.56    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.23/1.56  
% 7.23/1.56  fof(f23,plain,(
% 7.23/1.56    ! [X0,X1] : (k2_xboole_0(X0,k4_xboole_0(X1,X0)) = X1 | ~r1_tarski(X0,X1))),
% 7.23/1.56    inference(ennf_transformation,[],[f6])).
% 7.23/1.56  
% 7.23/1.56  fof(f40,plain,(
% 7.23/1.56    ( ! [X0,X1] : (k2_xboole_0(X0,k4_xboole_0(X1,X0)) = X1 | ~r1_tarski(X0,X1)) )),
% 7.23/1.56    inference(cnf_transformation,[],[f23])).
% 7.23/1.56  
% 7.23/1.56  fof(f69,plain,(
% 7.23/1.56    ( ! [X0,X1] : (k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,k4_xboole_0(X1,X0))) = X1 | ~r1_tarski(X0,X1)) )),
% 7.23/1.56    inference(definition_unfolding,[],[f40,f65])).
% 7.23/1.56  
% 7.23/1.56  fof(f58,plain,(
% 7.23/1.56    r1_xboole_0(sK1,sK2)),
% 7.23/1.56    inference(cnf_transformation,[],[f34])).
% 7.23/1.56  
% 7.23/1.56  fof(f4,axiom,(
% 7.23/1.56    ! [X0,X1] : k4_xboole_0(X0,X1) = k4_xboole_0(k2_xboole_0(X0,X1),X1)),
% 7.23/1.56    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.23/1.56  
% 7.23/1.56  fof(f38,plain,(
% 7.23/1.56    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k4_xboole_0(k2_xboole_0(X0,X1),X1)) )),
% 7.23/1.56    inference(cnf_transformation,[],[f4])).
% 7.23/1.56  
% 7.23/1.56  fof(f67,plain,(
% 7.23/1.56    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k4_xboole_0(k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)),X1)) )),
% 7.23/1.56    inference(definition_unfolding,[],[f38,f65])).
% 7.23/1.56  
% 7.23/1.56  fof(f60,plain,(
% 7.23/1.56    k3_subset_1(sK0,sK2) != sK1),
% 7.23/1.56    inference(cnf_transformation,[],[f34])).
% 7.23/1.56  
% 7.23/1.56  cnf(c_15,negated_conjecture,
% 7.23/1.56      ( r1_xboole_0(k3_subset_1(sK0,sK1),k3_subset_1(sK0,sK2)) ),
% 7.23/1.56      inference(cnf_transformation,[],[f59]) ).
% 7.23/1.56  
% 7.23/1.56  cnf(c_581,plain,
% 7.23/1.56      ( r1_xboole_0(k3_subset_1(sK0,sK1),k3_subset_1(sK0,sK2)) = iProver_top ),
% 7.23/1.56      inference(predicate_to_equality,[status(thm)],[c_15]) ).
% 7.23/1.56  
% 7.23/1.56  cnf(c_0,plain,
% 7.23/1.56      ( ~ r1_xboole_0(X0,X1) | r1_xboole_0(X1,X0) ),
% 7.23/1.56      inference(cnf_transformation,[],[f35]) ).
% 7.23/1.56  
% 7.23/1.56  cnf(c_590,plain,
% 7.23/1.56      ( r1_xboole_0(X0,X1) != iProver_top
% 7.23/1.56      | r1_xboole_0(X1,X0) = iProver_top ),
% 7.23/1.56      inference(predicate_to_equality,[status(thm)],[c_0]) ).
% 7.23/1.56  
% 7.23/1.56  cnf(c_1415,plain,
% 7.23/1.56      ( r1_xboole_0(k3_subset_1(sK0,sK2),k3_subset_1(sK0,sK1)) = iProver_top ),
% 7.23/1.56      inference(superposition,[status(thm)],[c_581,c_590]) ).
% 7.23/1.56  
% 7.23/1.56  cnf(c_8,plain,
% 7.23/1.56      ( ~ r1_xboole_0(X0,X1) | k4_xboole_0(X0,X1) = X0 ),
% 7.23/1.56      inference(cnf_transformation,[],[f43]) ).
% 7.23/1.56  
% 7.23/1.56  cnf(c_587,plain,
% 7.23/1.56      ( k4_xboole_0(X0,X1) = X0 | r1_xboole_0(X0,X1) != iProver_top ),
% 7.23/1.56      inference(predicate_to_equality,[status(thm)],[c_8]) ).
% 7.23/1.56  
% 7.23/1.56  cnf(c_1544,plain,
% 7.23/1.56      ( k4_xboole_0(k3_subset_1(sK0,sK2),k3_subset_1(sK0,sK1)) = k3_subset_1(sK0,sK2) ),
% 7.23/1.56      inference(superposition,[status(thm)],[c_1415,c_587]) ).
% 7.23/1.56  
% 7.23/1.56  cnf(c_17,negated_conjecture,
% 7.23/1.56      ( m1_subset_1(sK2,k1_zfmisc_1(sK0)) ),
% 7.23/1.56      inference(cnf_transformation,[],[f57]) ).
% 7.23/1.56  
% 7.23/1.56  cnf(c_579,plain,
% 7.23/1.56      ( m1_subset_1(sK2,k1_zfmisc_1(sK0)) = iProver_top ),
% 7.23/1.56      inference(predicate_to_equality,[status(thm)],[c_17]) ).
% 7.23/1.56  
% 7.23/1.56  cnf(c_9,plain,
% 7.23/1.56      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
% 7.23/1.56      | k3_subset_1(X1,X0) = k4_xboole_0(X1,X0) ),
% 7.23/1.56      inference(cnf_transformation,[],[f51]) ).
% 7.23/1.56  
% 7.23/1.56  cnf(c_586,plain,
% 7.23/1.56      ( k3_subset_1(X0,X1) = k4_xboole_0(X0,X1)
% 7.23/1.56      | m1_subset_1(X1,k1_zfmisc_1(X0)) != iProver_top ),
% 7.23/1.56      inference(predicate_to_equality,[status(thm)],[c_9]) ).
% 7.23/1.56  
% 7.23/1.56  cnf(c_2001,plain,
% 7.23/1.56      ( k3_subset_1(sK0,sK2) = k4_xboole_0(sK0,sK2) ),
% 7.23/1.56      inference(superposition,[status(thm)],[c_579,c_586]) ).
% 7.23/1.56  
% 7.23/1.56  cnf(c_18,negated_conjecture,
% 7.23/1.56      ( m1_subset_1(sK1,k1_zfmisc_1(sK0)) ),
% 7.23/1.56      inference(cnf_transformation,[],[f56]) ).
% 7.23/1.56  
% 7.23/1.56  cnf(c_578,plain,
% 7.23/1.56      ( m1_subset_1(sK1,k1_zfmisc_1(sK0)) = iProver_top ),
% 7.23/1.56      inference(predicate_to_equality,[status(thm)],[c_18]) ).
% 7.23/1.56  
% 7.23/1.56  cnf(c_2002,plain,
% 7.23/1.56      ( k3_subset_1(sK0,sK1) = k4_xboole_0(sK0,sK1) ),
% 7.23/1.56      inference(superposition,[status(thm)],[c_578,c_586]) ).
% 7.23/1.56  
% 7.23/1.56  cnf(c_3254,plain,
% 7.23/1.56      ( k4_xboole_0(k4_xboole_0(sK0,sK2),k4_xboole_0(sK0,sK1)) = k4_xboole_0(sK0,sK2) ),
% 7.23/1.56      inference(light_normalisation,[status(thm)],[c_1544,c_2001,c_2002]) ).
% 7.23/1.56  
% 7.23/1.56  cnf(c_6,plain,
% 7.23/1.56      ( k4_xboole_0(X0,k3_tarski(k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X2))) = k4_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X0,X2))) ),
% 7.23/1.56      inference(cnf_transformation,[],[f70]) ).
% 7.23/1.56  
% 7.23/1.56  cnf(c_4,plain,
% 7.23/1.56      ( k4_xboole_0(X0,k3_tarski(k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X2))) = k4_xboole_0(k4_xboole_0(X0,X1),X2) ),
% 7.23/1.56      inference(cnf_transformation,[],[f68]) ).
% 7.23/1.56  
% 7.23/1.56  cnf(c_638,plain,
% 7.23/1.56      ( k4_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X0,X2))) = k4_xboole_0(k4_xboole_0(X0,X1),X2) ),
% 7.23/1.56      inference(light_normalisation,[status(thm)],[c_6,c_4]) ).
% 7.23/1.56  
% 7.23/1.56  cnf(c_3261,plain,
% 7.23/1.56      ( k4_xboole_0(k4_xboole_0(sK0,sK2),k4_xboole_0(sK0,sK2)) = k4_xboole_0(k4_xboole_0(sK0,sK2),sK1) ),
% 7.23/1.56      inference(superposition,[status(thm)],[c_3254,c_638]) ).
% 7.23/1.56  
% 7.23/1.56  cnf(c_1,plain,
% 7.23/1.56      ( k4_xboole_0(X0,k4_xboole_0(X0,k1_xboole_0)) = k1_xboole_0 ),
% 7.23/1.56      inference(cnf_transformation,[],[f66]) ).
% 7.23/1.56  
% 7.23/1.56  cnf(c_2,plain,
% 7.23/1.56      ( k4_xboole_0(X0,k1_xboole_0) = X0 ),
% 7.23/1.56      inference(cnf_transformation,[],[f37]) ).
% 7.23/1.56  
% 7.23/1.56  cnf(c_601,plain,
% 7.23/1.56      ( k4_xboole_0(X0,X0) = k1_xboole_0 ),
% 7.23/1.56      inference(light_normalisation,[status(thm)],[c_1,c_2]) ).
% 7.23/1.56  
% 7.23/1.56  cnf(c_3263,plain,
% 7.23/1.56      ( k4_xboole_0(k4_xboole_0(sK0,sK2),sK1) = k1_xboole_0 ),
% 7.23/1.56      inference(demodulation,[status(thm)],[c_3261,c_601]) ).
% 7.23/1.56  
% 7.23/1.56  cnf(c_11,plain,
% 7.23/1.56      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
% 7.23/1.56      | k3_subset_1(X1,k3_subset_1(X1,X0)) = X0 ),
% 7.23/1.56      inference(cnf_transformation,[],[f53]) ).
% 7.23/1.56  
% 7.23/1.56  cnf(c_584,plain,
% 7.23/1.56      ( k3_subset_1(X0,k3_subset_1(X0,X1)) = X1
% 7.23/1.56      | m1_subset_1(X1,k1_zfmisc_1(X0)) != iProver_top ),
% 7.23/1.56      inference(predicate_to_equality,[status(thm)],[c_11]) ).
% 7.23/1.56  
% 7.23/1.56  cnf(c_1838,plain,
% 7.23/1.56      ( k3_subset_1(sK0,k3_subset_1(sK0,sK2)) = sK2 ),
% 7.23/1.56      inference(superposition,[status(thm)],[c_579,c_584]) ).
% 7.23/1.56  
% 7.23/1.56  cnf(c_13,plain,
% 7.23/1.56      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
% 7.23/1.56      | ~ m1_subset_1(X2,k1_zfmisc_1(X1))
% 7.23/1.56      | r1_tarski(X0,X2)
% 7.23/1.56      | ~ r1_xboole_0(X0,k3_subset_1(X1,X2)) ),
% 7.23/1.56      inference(cnf_transformation,[],[f54]) ).
% 7.23/1.56  
% 7.23/1.56  cnf(c_582,plain,
% 7.23/1.56      ( m1_subset_1(X0,k1_zfmisc_1(X1)) != iProver_top
% 7.23/1.56      | m1_subset_1(X2,k1_zfmisc_1(X1)) != iProver_top
% 7.23/1.56      | r1_tarski(X0,X2) = iProver_top
% 7.23/1.56      | r1_xboole_0(X0,k3_subset_1(X1,X2)) != iProver_top ),
% 7.23/1.56      inference(predicate_to_equality,[status(thm)],[c_13]) ).
% 7.23/1.56  
% 7.23/1.56  cnf(c_2087,plain,
% 7.23/1.56      ( m1_subset_1(X0,k1_zfmisc_1(sK0)) != iProver_top
% 7.23/1.56      | m1_subset_1(k3_subset_1(sK0,sK2),k1_zfmisc_1(sK0)) != iProver_top
% 7.23/1.56      | r1_tarski(X0,k3_subset_1(sK0,sK2)) = iProver_top
% 7.23/1.56      | r1_xboole_0(X0,sK2) != iProver_top ),
% 7.23/1.56      inference(superposition,[status(thm)],[c_1838,c_582]) ).
% 7.23/1.56  
% 7.23/1.56  cnf(c_20,plain,
% 7.23/1.56      ( m1_subset_1(sK2,k1_zfmisc_1(sK0)) = iProver_top ),
% 7.23/1.56      inference(predicate_to_equality,[status(thm)],[c_17]) ).
% 7.23/1.56  
% 7.23/1.56  cnf(c_10,plain,
% 7.23/1.56      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
% 7.23/1.56      | m1_subset_1(k3_subset_1(X1,X0),k1_zfmisc_1(X1)) ),
% 7.23/1.56      inference(cnf_transformation,[],[f52]) ).
% 7.23/1.56  
% 7.23/1.56  cnf(c_711,plain,
% 7.23/1.56      ( m1_subset_1(k3_subset_1(sK0,sK2),k1_zfmisc_1(sK0))
% 7.23/1.56      | ~ m1_subset_1(sK2,k1_zfmisc_1(sK0)) ),
% 7.23/1.56      inference(instantiation,[status(thm)],[c_10]) ).
% 7.23/1.56  
% 7.23/1.56  cnf(c_712,plain,
% 7.23/1.56      ( m1_subset_1(k3_subset_1(sK0,sK2),k1_zfmisc_1(sK0)) = iProver_top
% 7.23/1.56      | m1_subset_1(sK2,k1_zfmisc_1(sK0)) != iProver_top ),
% 7.23/1.56      inference(predicate_to_equality,[status(thm)],[c_711]) ).
% 7.23/1.56  
% 7.23/1.56  cnf(c_4677,plain,
% 7.23/1.56      ( m1_subset_1(X0,k1_zfmisc_1(sK0)) != iProver_top
% 7.23/1.56      | r1_tarski(X0,k3_subset_1(sK0,sK2)) = iProver_top
% 7.23/1.56      | r1_xboole_0(X0,sK2) != iProver_top ),
% 7.23/1.56      inference(global_propositional_subsumption,
% 7.23/1.56                [status(thm)],
% 7.23/1.56                [c_2087,c_20,c_712]) ).
% 7.23/1.56  
% 7.23/1.56  cnf(c_4683,plain,
% 7.23/1.56      ( m1_subset_1(X0,k1_zfmisc_1(sK0)) != iProver_top
% 7.23/1.56      | r1_tarski(X0,k4_xboole_0(sK0,sK2)) = iProver_top
% 7.23/1.56      | r1_xboole_0(X0,sK2) != iProver_top ),
% 7.23/1.56      inference(light_normalisation,[status(thm)],[c_4677,c_2001]) ).
% 7.23/1.56  
% 7.23/1.56  cnf(c_5,plain,
% 7.23/1.56      ( ~ r1_tarski(X0,X1)
% 7.23/1.56      | k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,k4_xboole_0(X1,X0))) = X1 ),
% 7.23/1.56      inference(cnf_transformation,[],[f69]) ).
% 7.23/1.56  
% 7.23/1.56  cnf(c_589,plain,
% 7.23/1.56      ( k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,k4_xboole_0(X1,X0))) = X1
% 7.23/1.56      | r1_tarski(X0,X1) != iProver_top ),
% 7.23/1.56      inference(predicate_to_equality,[status(thm)],[c_5]) ).
% 7.23/1.56  
% 7.23/1.56  cnf(c_21928,plain,
% 7.23/1.56      ( k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,k4_xboole_0(k4_xboole_0(sK0,sK2),X0))) = k4_xboole_0(sK0,sK2)
% 7.23/1.56      | m1_subset_1(X0,k1_zfmisc_1(sK0)) != iProver_top
% 7.23/1.56      | r1_xboole_0(X0,sK2) != iProver_top ),
% 7.23/1.56      inference(superposition,[status(thm)],[c_4683,c_589]) ).
% 7.23/1.56  
% 7.23/1.56  cnf(c_23085,plain,
% 7.23/1.56      ( k3_tarski(k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,k4_xboole_0(k4_xboole_0(sK0,sK2),sK1))) = k4_xboole_0(sK0,sK2)
% 7.23/1.56      | r1_xboole_0(sK1,sK2) != iProver_top ),
% 7.23/1.56      inference(superposition,[status(thm)],[c_578,c_21928]) ).
% 7.23/1.56  
% 7.23/1.56  cnf(c_16,negated_conjecture,
% 7.23/1.56      ( r1_xboole_0(sK1,sK2) ),
% 7.23/1.56      inference(cnf_transformation,[],[f58]) ).
% 7.23/1.56  
% 7.23/1.56  cnf(c_21,plain,
% 7.23/1.56      ( r1_xboole_0(sK1,sK2) = iProver_top ),
% 7.23/1.56      inference(predicate_to_equality,[status(thm)],[c_16]) ).
% 7.23/1.56  
% 7.23/1.56  cnf(c_23290,plain,
% 7.23/1.56      ( k3_tarski(k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,k4_xboole_0(k4_xboole_0(sK0,sK2),sK1))) = k4_xboole_0(sK0,sK2) ),
% 7.23/1.56      inference(global_propositional_subsumption,
% 7.23/1.56                [status(thm)],
% 7.23/1.56                [c_23085,c_21]) ).
% 7.23/1.56  
% 7.23/1.56  cnf(c_32285,plain,
% 7.23/1.56      ( k3_tarski(k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,k1_xboole_0)) = k4_xboole_0(sK0,sK2) ),
% 7.23/1.56      inference(demodulation,[status(thm)],[c_3263,c_23290]) ).
% 7.23/1.56  
% 7.23/1.56  cnf(c_3,plain,
% 7.23/1.56      ( k4_xboole_0(k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)),X1) = k4_xboole_0(X0,X1) ),
% 7.23/1.56      inference(cnf_transformation,[],[f67]) ).
% 7.23/1.56  
% 7.23/1.56  cnf(c_982,plain,
% 7.23/1.56      ( k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,k1_xboole_0)) = k4_xboole_0(X0,k1_xboole_0) ),
% 7.23/1.56      inference(superposition,[status(thm)],[c_2,c_3]) ).
% 7.23/1.56  
% 7.23/1.56  cnf(c_984,plain,
% 7.23/1.56      ( k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,k1_xboole_0)) = X0 ),
% 7.23/1.56      inference(light_normalisation,[status(thm)],[c_982,c_2]) ).
% 7.23/1.56  
% 7.23/1.56  cnf(c_32287,plain,
% 7.23/1.56      ( k4_xboole_0(sK0,sK2) = sK1 ),
% 7.23/1.56      inference(demodulation,[status(thm)],[c_32285,c_984]) ).
% 7.23/1.56  
% 7.23/1.56  cnf(c_14,negated_conjecture,
% 7.23/1.56      ( k3_subset_1(sK0,sK2) != sK1 ),
% 7.23/1.56      inference(cnf_transformation,[],[f60]) ).
% 7.23/1.56  
% 7.23/1.56  cnf(c_2229,plain,
% 7.23/1.56      ( k4_xboole_0(sK0,sK2) != sK1 ),
% 7.23/1.56      inference(demodulation,[status(thm)],[c_2001,c_14]) ).
% 7.23/1.56  
% 7.23/1.56  cnf(contradiction,plain,
% 7.23/1.56      ( $false ),
% 7.23/1.56      inference(minisat,[status(thm)],[c_32287,c_2229]) ).
% 7.23/1.56  
% 7.23/1.56  
% 7.23/1.56  % SZS output end CNFRefutation for theBenchmark.p
% 7.23/1.56  
% 7.23/1.56  ------                               Statistics
% 7.23/1.56  
% 7.23/1.56  ------ General
% 7.23/1.56  
% 7.23/1.56  abstr_ref_over_cycles:                  0
% 7.23/1.56  abstr_ref_under_cycles:                 0
% 7.23/1.56  gc_basic_clause_elim:                   0
% 7.23/1.56  forced_gc_time:                         0
% 7.23/1.56  parsing_time:                           0.009
% 7.23/1.56  unif_index_cands_time:                  0.
% 7.23/1.56  unif_index_add_time:                    0.
% 7.23/1.56  orderings_time:                         0.
% 7.23/1.56  out_proof_time:                         0.012
% 7.23/1.56  total_time:                             0.944
% 7.23/1.56  num_of_symbols:                         43
% 7.23/1.56  num_of_terms:                           38435
% 7.23/1.56  
% 7.23/1.56  ------ Preprocessing
% 7.23/1.56  
% 7.23/1.56  num_of_splits:                          0
% 7.23/1.56  num_of_split_atoms:                     0
% 7.23/1.56  num_of_reused_defs:                     0
% 7.23/1.56  num_eq_ax_congr_red:                    18
% 7.23/1.56  num_of_sem_filtered_clauses:            1
% 7.23/1.56  num_of_subtypes:                        0
% 7.23/1.56  monotx_restored_types:                  0
% 7.23/1.56  sat_num_of_epr_types:                   0
% 7.23/1.56  sat_num_of_non_cyclic_types:            0
% 7.23/1.56  sat_guarded_non_collapsed_types:        0
% 7.23/1.56  num_pure_diseq_elim:                    0
% 7.23/1.56  simp_replaced_by:                       0
% 7.23/1.56  res_preprocessed:                       76
% 7.23/1.56  prep_upred:                             0
% 7.23/1.56  prep_unflattend:                        2
% 7.23/1.56  smt_new_axioms:                         0
% 7.23/1.56  pred_elim_cands:                        3
% 7.23/1.56  pred_elim:                              0
% 7.23/1.56  pred_elim_cl:                           0
% 7.23/1.56  pred_elim_cycles:                       1
% 7.23/1.56  merged_defs:                            6
% 7.23/1.56  merged_defs_ncl:                        0
% 7.23/1.56  bin_hyper_res:                          6
% 7.23/1.56  prep_cycles:                            3
% 7.23/1.56  pred_elim_time:                         0.001
% 7.23/1.56  splitting_time:                         0.
% 7.23/1.56  sem_filter_time:                        0.
% 7.23/1.56  monotx_time:                            0.
% 7.23/1.56  subtype_inf_time:                       0.
% 7.23/1.56  
% 7.23/1.56  ------ Problem properties
% 7.23/1.56  
% 7.23/1.56  clauses:                                19
% 7.23/1.56  conjectures:                            5
% 7.23/1.56  epr:                                    2
% 7.23/1.56  horn:                                   19
% 7.23/1.56  ground:                                 5
% 7.23/1.56  unary:                                  10
% 7.23/1.56  binary:                                 7
% 7.23/1.56  lits:                                   32
% 7.23/1.56  lits_eq:                                11
% 7.23/1.56  fd_pure:                                0
% 7.23/1.56  fd_pseudo:                              0
% 7.23/1.56  fd_cond:                                0
% 7.23/1.56  fd_pseudo_cond:                         0
% 7.23/1.56  ac_symbols:                             0
% 7.23/1.56  
% 7.23/1.56  ------ Propositional Solver
% 7.23/1.56  
% 7.23/1.56  prop_solver_calls:                      24
% 7.23/1.56  prop_fast_solver_calls:                 708
% 7.23/1.56  smt_solver_calls:                       0
% 7.23/1.56  smt_fast_solver_calls:                  0
% 7.23/1.56  prop_num_of_clauses:                    9789
% 7.23/1.56  prop_preprocess_simplified:             16544
% 7.23/1.56  prop_fo_subsumed:                       27
% 7.23/1.56  prop_solver_time:                       0.
% 7.23/1.56  smt_solver_time:                        0.
% 7.23/1.56  smt_fast_solver_time:                   0.
% 7.23/1.56  prop_fast_solver_time:                  0.
% 7.23/1.56  prop_unsat_core_time:                   0.001
% 7.23/1.56  
% 7.23/1.56  ------ QBF
% 7.23/1.56  
% 7.23/1.56  qbf_q_res:                              0
% 7.23/1.56  qbf_num_tautologies:                    0
% 7.23/1.56  qbf_prep_cycles:                        0
% 7.23/1.56  
% 7.23/1.56  ------ BMC1
% 7.23/1.56  
% 7.23/1.56  bmc1_current_bound:                     -1
% 7.23/1.56  bmc1_last_solved_bound:                 -1
% 7.23/1.56  bmc1_unsat_core_size:                   -1
% 7.23/1.56  bmc1_unsat_core_parents_size:           -1
% 7.23/1.56  bmc1_merge_next_fun:                    0
% 7.23/1.56  bmc1_unsat_core_clauses_time:           0.
% 7.23/1.56  
% 7.23/1.56  ------ Instantiation
% 7.23/1.56  
% 7.23/1.56  inst_num_of_clauses:                    2876
% 7.23/1.56  inst_num_in_passive:                    1144
% 7.23/1.56  inst_num_in_active:                     926
% 7.23/1.56  inst_num_in_unprocessed:                806
% 7.23/1.56  inst_num_of_loops:                      930
% 7.23/1.56  inst_num_of_learning_restarts:          0
% 7.23/1.56  inst_num_moves_active_passive:          3
% 7.23/1.56  inst_lit_activity:                      0
% 7.23/1.56  inst_lit_activity_moves:                0
% 7.23/1.56  inst_num_tautologies:                   0
% 7.23/1.56  inst_num_prop_implied:                  0
% 7.23/1.56  inst_num_existing_simplified:           0
% 7.23/1.56  inst_num_eq_res_simplified:             0
% 7.23/1.56  inst_num_child_elim:                    0
% 7.23/1.56  inst_num_of_dismatching_blockings:      1416
% 7.23/1.56  inst_num_of_non_proper_insts:           2503
% 7.23/1.56  inst_num_of_duplicates:                 0
% 7.23/1.56  inst_inst_num_from_inst_to_res:         0
% 7.23/1.56  inst_dismatching_checking_time:         0.
% 7.23/1.56  
% 7.23/1.56  ------ Resolution
% 7.23/1.56  
% 7.23/1.56  res_num_of_clauses:                     0
% 7.23/1.56  res_num_in_passive:                     0
% 7.23/1.56  res_num_in_active:                      0
% 7.23/1.56  res_num_of_loops:                       79
% 7.23/1.56  res_forward_subset_subsumed:            99
% 7.23/1.56  res_backward_subset_subsumed:           2
% 7.23/1.56  res_forward_subsumed:                   0
% 7.23/1.56  res_backward_subsumed:                  0
% 7.23/1.56  res_forward_subsumption_resolution:     0
% 7.23/1.56  res_backward_subsumption_resolution:    0
% 7.23/1.56  res_clause_to_clause_subsumption:       15548
% 7.23/1.56  res_orphan_elimination:                 0
% 7.23/1.56  res_tautology_del:                      169
% 7.23/1.56  res_num_eq_res_simplified:              0
% 7.23/1.56  res_num_sel_changes:                    0
% 7.23/1.56  res_moves_from_active_to_pass:          0
% 7.23/1.56  
% 7.23/1.56  ------ Superposition
% 7.23/1.56  
% 7.23/1.56  sup_time_total:                         0.
% 7.23/1.56  sup_time_generating:                    0.
% 7.23/1.56  sup_time_sim_full:                      0.
% 7.23/1.56  sup_time_sim_immed:                     0.
% 7.23/1.56  
% 7.23/1.56  sup_num_of_clauses:                     1290
% 7.23/1.56  sup_num_in_active:                      161
% 7.23/1.56  sup_num_in_passive:                     1129
% 7.23/1.56  sup_num_of_loops:                       184
% 7.23/1.56  sup_fw_superposition:                   3513
% 7.23/1.56  sup_bw_superposition:                   2912
% 7.23/1.56  sup_immediate_simplified:               3619
% 7.23/1.56  sup_given_eliminated:                   3
% 7.23/1.56  comparisons_done:                       0
% 7.23/1.56  comparisons_avoided:                    0
% 7.23/1.56  
% 7.23/1.56  ------ Simplifications
% 7.23/1.56  
% 7.23/1.56  
% 7.23/1.56  sim_fw_subset_subsumed:                 14
% 7.23/1.56  sim_bw_subset_subsumed:                 0
% 7.23/1.56  sim_fw_subsumed:                        974
% 7.23/1.56  sim_bw_subsumed:                        64
% 7.23/1.56  sim_fw_subsumption_res:                 1
% 7.23/1.56  sim_bw_subsumption_res:                 0
% 7.23/1.56  sim_tautology_del:                      7
% 7.23/1.56  sim_eq_tautology_del:                   397
% 7.23/1.56  sim_eq_res_simp:                        7
% 7.23/1.56  sim_fw_demodulated:                     1025
% 7.23/1.56  sim_bw_demodulated:                     179
% 7.23/1.56  sim_light_normalised:                   1869
% 7.23/1.56  sim_joinable_taut:                      0
% 7.23/1.56  sim_joinable_simp:                      0
% 7.23/1.56  sim_ac_normalised:                      0
% 7.23/1.56  sim_smt_subsumption:                    0
% 7.23/1.56  
%------------------------------------------------------------------------------
