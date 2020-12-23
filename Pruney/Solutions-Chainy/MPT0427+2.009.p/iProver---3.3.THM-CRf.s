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
% DateTime   : Thu Dec  3 11:42:28 EST 2020

% Result     : Theorem 2.53s
% Output     : CNFRefutation 2.53s
% Verified   : 
% Statistics : Number of formulae       :  131 (1645 expanded)
%              Number of clauses        :   72 ( 567 expanded)
%              Number of leaves         :   18 ( 385 expanded)
%              Depth                    :   25
%              Number of atoms          :  270 (5255 expanded)
%              Number of equality atoms :  131 (1232 expanded)
%              Maximal formula depth    :    8 (   3 average)
%              Maximal clause size      :    8 (   2 average)
%              Maximal term depth       :    7 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f6,axiom,(
    ! [X0] :
    ? [X1] : m1_subset_1(X1,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f29,plain,(
    ! [X0] :
      ( ? [X1] : m1_subset_1(X1,X0)
     => m1_subset_1(sK0(X0),X0) ) ),
    introduced(choice_axiom,[])).

fof(f30,plain,(
    ! [X0] : m1_subset_1(sK0(X0),X0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f6,f29])).

fof(f40,plain,(
    ! [X0] : m1_subset_1(sK0(X0),X0) ),
    inference(cnf_transformation,[],[f30])).

fof(f12,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,X1)
     => ( r2_hidden(X0,X1)
        | v1_xboole_0(X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f23,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
      | v1_xboole_0(X1)
      | ~ m1_subset_1(X0,X1) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f24,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
      | v1_xboole_0(X1)
      | ~ m1_subset_1(X0,X1) ) ),
    inference(flattening,[],[f23])).

fof(f47,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
      | v1_xboole_0(X1)
      | ~ m1_subset_1(X0,X1) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
     => k2_xboole_0(k1_tarski(X0),X1) = X1 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f18,plain,(
    ! [X0,X1] :
      ( k2_xboole_0(k1_tarski(X0),X1) = X1
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f38,plain,(
    ! [X0,X1] :
      ( k2_xboole_0(k1_tarski(X0),X1) = X1
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f3,axiom,(
    ! [X0,X1] : k5_xboole_0(X0,k4_xboole_0(X1,X0)) = k2_xboole_0(X0,X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f37,plain,(
    ! [X0,X1] : k5_xboole_0(X0,k4_xboole_0(X1,X0)) = k2_xboole_0(X0,X1) ),
    inference(cnf_transformation,[],[f3])).

fof(f2,axiom,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f36,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f2])).

fof(f11,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f46,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1)) ),
    inference(cnf_transformation,[],[f11])).

fof(f55,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k1_setfam_1(k2_tarski(X0,X1))) ),
    inference(definition_unfolding,[],[f36,f46])).

fof(f56,plain,(
    ! [X0,X1] : k5_xboole_0(X0,k5_xboole_0(X1,k1_setfam_1(k2_tarski(X1,X0)))) = k2_xboole_0(X0,X1) ),
    inference(definition_unfolding,[],[f37,f55])).

fof(f57,plain,(
    ! [X0,X1] :
      ( k5_xboole_0(k1_tarski(X0),k5_xboole_0(X1,k1_setfam_1(k2_tarski(X1,k1_tarski(X0))))) = X1
      | ~ r2_hidden(X0,X1) ) ),
    inference(definition_unfolding,[],[f38,f56])).

fof(f14,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
     => ( r1_tarski(k1_setfam_1(X1),k1_setfam_1(X0))
        | k1_xboole_0 = X0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f25,plain,(
    ! [X0,X1] :
      ( r1_tarski(k1_setfam_1(X1),k1_setfam_1(X0))
      | k1_xboole_0 = X0
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f26,plain,(
    ! [X0,X1] :
      ( r1_tarski(k1_setfam_1(X1),k1_setfam_1(X0))
      | k1_xboole_0 = X0
      | ~ r1_tarski(X0,X1) ) ),
    inference(flattening,[],[f25])).

fof(f50,plain,(
    ! [X0,X1] :
      ( r1_tarski(k1_setfam_1(X1),k1_setfam_1(X0))
      | k1_xboole_0 = X0
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f15,conjecture,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0)))
     => ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(X0)))
         => ( r1_tarski(X1,X2)
           => r1_tarski(k8_setfam_1(X0,X2),k8_setfam_1(X0,X1)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f16,negated_conjecture,(
    ~ ! [X0,X1] :
        ( m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0)))
       => ! [X2] :
            ( m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(X0)))
           => ( r1_tarski(X1,X2)
             => r1_tarski(k8_setfam_1(X0,X2),k8_setfam_1(X0,X1)) ) ) ) ),
    inference(negated_conjecture,[],[f15])).

fof(f27,plain,(
    ? [X0,X1] :
      ( ? [X2] :
          ( ~ r1_tarski(k8_setfam_1(X0,X2),k8_setfam_1(X0,X1))
          & r1_tarski(X1,X2)
          & m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(X0))) )
      & m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) ) ),
    inference(ennf_transformation,[],[f16])).

fof(f28,plain,(
    ? [X0,X1] :
      ( ? [X2] :
          ( ~ r1_tarski(k8_setfam_1(X0,X2),k8_setfam_1(X0,X1))
          & r1_tarski(X1,X2)
          & m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(X0))) )
      & m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) ) ),
    inference(flattening,[],[f27])).

fof(f33,plain,(
    ! [X0,X1] :
      ( ? [X2] :
          ( ~ r1_tarski(k8_setfam_1(X0,X2),k8_setfam_1(X0,X1))
          & r1_tarski(X1,X2)
          & m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(X0))) )
     => ( ~ r1_tarski(k8_setfam_1(X0,sK3),k8_setfam_1(X0,X1))
        & r1_tarski(X1,sK3)
        & m1_subset_1(sK3,k1_zfmisc_1(k1_zfmisc_1(X0))) ) ) ),
    introduced(choice_axiom,[])).

fof(f32,plain,
    ( ? [X0,X1] :
        ( ? [X2] :
            ( ~ r1_tarski(k8_setfam_1(X0,X2),k8_setfam_1(X0,X1))
            & r1_tarski(X1,X2)
            & m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(X0))) )
        & m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) )
   => ( ? [X2] :
          ( ~ r1_tarski(k8_setfam_1(sK1,X2),k8_setfam_1(sK1,sK2))
          & r1_tarski(sK2,X2)
          & m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(sK1))) )
      & m1_subset_1(sK2,k1_zfmisc_1(k1_zfmisc_1(sK1))) ) ),
    introduced(choice_axiom,[])).

fof(f34,plain,
    ( ~ r1_tarski(k8_setfam_1(sK1,sK3),k8_setfam_1(sK1,sK2))
    & r1_tarski(sK2,sK3)
    & m1_subset_1(sK3,k1_zfmisc_1(k1_zfmisc_1(sK1)))
    & m1_subset_1(sK2,k1_zfmisc_1(k1_zfmisc_1(sK1))) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1,sK2,sK3])],[f28,f33,f32])).

fof(f52,plain,(
    m1_subset_1(sK3,k1_zfmisc_1(k1_zfmisc_1(sK1))) ),
    inference(cnf_transformation,[],[f34])).

fof(f8,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0)))
     => ( ( k1_xboole_0 = X1
         => k8_setfam_1(X0,X1) = X0 )
        & ( k1_xboole_0 != X1
         => k8_setfam_1(X0,X1) = k6_setfam_1(X0,X1) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f20,plain,(
    ! [X0,X1] :
      ( ( ( k8_setfam_1(X0,X1) = X0
          | k1_xboole_0 != X1 )
        & ( k8_setfam_1(X0,X1) = k6_setfam_1(X0,X1)
          | k1_xboole_0 = X1 ) )
      | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f42,plain,(
    ! [X0,X1] :
      ( k8_setfam_1(X0,X1) = k6_setfam_1(X0,X1)
      | k1_xboole_0 = X1
      | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f10,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0)))
     => k6_setfam_1(X0,X1) = k1_setfam_1(X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f22,plain,(
    ! [X0,X1] :
      ( k6_setfam_1(X0,X1) = k1_setfam_1(X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f45,plain,(
    ! [X0,X1] :
      ( k6_setfam_1(X0,X1) = k1_setfam_1(X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f51,plain,(
    m1_subset_1(sK2,k1_zfmisc_1(k1_zfmisc_1(sK1))) ),
    inference(cnf_transformation,[],[f34])).

fof(f54,plain,(
    ~ r1_tarski(k8_setfam_1(sK1,sK3),k8_setfam_1(sK1,sK2)) ),
    inference(cnf_transformation,[],[f34])).

fof(f53,plain,(
    r1_tarski(sK2,sK3) ),
    inference(cnf_transformation,[],[f34])).

fof(f43,plain,(
    ! [X0,X1] :
      ( k8_setfam_1(X0,X1) = X0
      | k1_xboole_0 != X1
      | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f59,plain,(
    ! [X0] :
      ( k8_setfam_1(X0,k1_xboole_0) = X0
      | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_zfmisc_1(X0))) ) ),
    inference(equality_resolution,[],[f43])).

fof(f9,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0)))
     => m1_subset_1(k8_setfam_1(X0,X1),k1_zfmisc_1(X0)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f21,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k8_setfam_1(X0,X1),k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f44,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k8_setfam_1(X0,X1),k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f13,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f31,plain,(
    ! [X0,X1] :
      ( ( m1_subset_1(X0,k1_zfmisc_1(X1))
        | ~ r1_tarski(X0,X1) )
      & ( r1_tarski(X0,X1)
        | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ) ) ),
    inference(nnf_transformation,[],[f13])).

fof(f48,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f7,axiom,(
    ! [X0] :
      ( v1_xboole_0(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(X0))
         => v1_xboole_0(X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f19,plain,(
    ! [X0] :
      ( ! [X1] :
          ( v1_xboole_0(X1)
          | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) )
      | ~ v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f41,plain,(
    ! [X0,X1] :
      ( v1_xboole_0(X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | ~ v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f49,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f5,axiom,(
    ! [X0,X1] : k1_xboole_0 != k2_xboole_0(k1_tarski(X0),X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f39,plain,(
    ! [X0,X1] : k1_xboole_0 != k2_xboole_0(k1_tarski(X0),X1) ),
    inference(cnf_transformation,[],[f5])).

fof(f58,plain,(
    ! [X0,X1] : k1_xboole_0 != k5_xboole_0(k1_tarski(X0),k5_xboole_0(X1,k1_setfam_1(k2_tarski(X1,k1_tarski(X0))))) ),
    inference(definition_unfolding,[],[f39,f56])).

fof(f1,axiom,(
    ! [X0] :
      ( v1_xboole_0(X0)
     => k1_xboole_0 = X0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f17,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | ~ v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f35,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | ~ v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f17])).

cnf(c_3,plain,
    ( m1_subset_1(sK0(X0),X0) ),
    inference(cnf_transformation,[],[f40])).

cnf(c_741,plain,
    ( m1_subset_1(sK0(X0),X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3])).

cnf(c_9,plain,
    ( ~ m1_subset_1(X0,X1)
    | r2_hidden(X0,X1)
    | v1_xboole_0(X1) ),
    inference(cnf_transformation,[],[f47])).

cnf(c_1,plain,
    ( ~ r2_hidden(X0,X1)
    | k5_xboole_0(k1_tarski(X0),k5_xboole_0(X1,k1_setfam_1(k2_tarski(X1,k1_tarski(X0))))) = X1 ),
    inference(cnf_transformation,[],[f57])).

cnf(c_218,plain,
    ( ~ m1_subset_1(X0,X1)
    | v1_xboole_0(X1)
    | k5_xboole_0(k1_tarski(X0),k5_xboole_0(X1,k1_setfam_1(k2_tarski(X1,k1_tarski(X0))))) = X1 ),
    inference(resolution,[status(thm)],[c_9,c_1])).

cnf(c_728,plain,
    ( k5_xboole_0(k1_tarski(X0),k5_xboole_0(X1,k1_setfam_1(k2_tarski(X1,k1_tarski(X0))))) = X1
    | m1_subset_1(X0,X1) != iProver_top
    | v1_xboole_0(X1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_218])).

cnf(c_1139,plain,
    ( k5_xboole_0(k1_tarski(sK0(X0)),k5_xboole_0(X0,k1_setfam_1(k2_tarski(X0,k1_tarski(sK0(X0)))))) = X0
    | v1_xboole_0(X0) = iProver_top ),
    inference(superposition,[status(thm)],[c_741,c_728])).

cnf(c_12,plain,
    ( ~ r1_tarski(X0,X1)
    | r1_tarski(k1_setfam_1(X1),k1_setfam_1(X0))
    | k1_xboole_0 = X0 ),
    inference(cnf_transformation,[],[f50])).

cnf(c_734,plain,
    ( k1_xboole_0 = X0
    | r1_tarski(X0,X1) != iProver_top
    | r1_tarski(k1_setfam_1(X1),k1_setfam_1(X0)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_12])).

cnf(c_15,negated_conjecture,
    ( m1_subset_1(sK3,k1_zfmisc_1(k1_zfmisc_1(sK1))) ),
    inference(cnf_transformation,[],[f52])).

cnf(c_731,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(k1_zfmisc_1(sK1))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_15])).

cnf(c_6,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k1_zfmisc_1(X1)))
    | k6_setfam_1(X1,X0) = k8_setfam_1(X1,X0)
    | k1_xboole_0 = X0 ),
    inference(cnf_transformation,[],[f42])).

cnf(c_739,plain,
    ( k6_setfam_1(X0,X1) = k8_setfam_1(X0,X1)
    | k1_xboole_0 = X1
    | m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_6])).

cnf(c_1914,plain,
    ( k6_setfam_1(sK1,sK3) = k8_setfam_1(sK1,sK3)
    | sK3 = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_731,c_739])).

cnf(c_8,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k1_zfmisc_1(X1)))
    | k6_setfam_1(X1,X0) = k1_setfam_1(X0) ),
    inference(cnf_transformation,[],[f45])).

cnf(c_737,plain,
    ( k6_setfam_1(X0,X1) = k1_setfam_1(X1)
    | m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_8])).

cnf(c_1291,plain,
    ( k6_setfam_1(sK1,sK3) = k1_setfam_1(sK3) ),
    inference(superposition,[status(thm)],[c_731,c_737])).

cnf(c_1923,plain,
    ( k8_setfam_1(sK1,sK3) = k1_setfam_1(sK3)
    | sK3 = k1_xboole_0 ),
    inference(light_normalisation,[status(thm)],[c_1914,c_1291])).

cnf(c_16,negated_conjecture,
    ( m1_subset_1(sK2,k1_zfmisc_1(k1_zfmisc_1(sK1))) ),
    inference(cnf_transformation,[],[f51])).

cnf(c_730,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(k1_zfmisc_1(sK1))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_16])).

cnf(c_1915,plain,
    ( k6_setfam_1(sK1,sK2) = k8_setfam_1(sK1,sK2)
    | sK2 = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_730,c_739])).

cnf(c_1292,plain,
    ( k6_setfam_1(sK1,sK2) = k1_setfam_1(sK2) ),
    inference(superposition,[status(thm)],[c_730,c_737])).

cnf(c_1918,plain,
    ( k8_setfam_1(sK1,sK2) = k1_setfam_1(sK2)
    | sK2 = k1_xboole_0 ),
    inference(light_normalisation,[status(thm)],[c_1915,c_1292])).

cnf(c_13,negated_conjecture,
    ( ~ r1_tarski(k8_setfam_1(sK1,sK3),k8_setfam_1(sK1,sK2)) ),
    inference(cnf_transformation,[],[f54])).

cnf(c_733,plain,
    ( r1_tarski(k8_setfam_1(sK1,sK3),k8_setfam_1(sK1,sK2)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_13])).

cnf(c_2164,plain,
    ( sK2 = k1_xboole_0
    | r1_tarski(k8_setfam_1(sK1,sK3),k1_setfam_1(sK2)) != iProver_top ),
    inference(superposition,[status(thm)],[c_1918,c_733])).

cnf(c_2256,plain,
    ( sK2 = k1_xboole_0
    | sK3 = k1_xboole_0
    | r1_tarski(k1_setfam_1(sK3),k1_setfam_1(sK2)) != iProver_top ),
    inference(superposition,[status(thm)],[c_1923,c_2164])).

cnf(c_2357,plain,
    ( sK2 = k1_xboole_0
    | sK3 = k1_xboole_0
    | r1_tarski(sK2,sK3) != iProver_top ),
    inference(superposition,[status(thm)],[c_734,c_2256])).

cnf(c_14,negated_conjecture,
    ( r1_tarski(sK2,sK3) ),
    inference(cnf_transformation,[],[f53])).

cnf(c_19,plain,
    ( r1_tarski(sK2,sK3) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_14])).

cnf(c_2516,plain,
    ( sK3 = k1_xboole_0
    | sK2 = k1_xboole_0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_2357,c_19])).

cnf(c_2517,plain,
    ( sK2 = k1_xboole_0
    | sK3 = k1_xboole_0 ),
    inference(renaming,[status(thm)],[c_2516])).

cnf(c_2528,plain,
    ( sK3 = k1_xboole_0
    | m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_zfmisc_1(sK1))) = iProver_top ),
    inference(superposition,[status(thm)],[c_2517,c_730])).

cnf(c_5,plain,
    ( ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_zfmisc_1(X0)))
    | k8_setfam_1(X0,k1_xboole_0) = X0 ),
    inference(cnf_transformation,[],[f59])).

cnf(c_740,plain,
    ( k8_setfam_1(X0,k1_xboole_0) = X0
    | m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_zfmisc_1(X0))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_5])).

cnf(c_2756,plain,
    ( k8_setfam_1(sK1,k1_xboole_0) = sK1
    | sK3 = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_2528,c_740])).

cnf(c_2527,plain,
    ( sK3 = k1_xboole_0
    | r1_tarski(k8_setfam_1(sK1,sK3),k8_setfam_1(sK1,k1_xboole_0)) != iProver_top ),
    inference(superposition,[status(thm)],[c_2517,c_733])).

cnf(c_2968,plain,
    ( sK3 = k1_xboole_0
    | r1_tarski(k8_setfam_1(sK1,sK3),sK1) != iProver_top ),
    inference(superposition,[status(thm)],[c_2756,c_2527])).

cnf(c_18,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(k1_zfmisc_1(sK1))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_15])).

cnf(c_7,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k1_zfmisc_1(X1)))
    | m1_subset_1(k8_setfam_1(X1,X0),k1_zfmisc_1(X1)) ),
    inference(cnf_transformation,[],[f44])).

cnf(c_860,plain,
    ( m1_subset_1(k8_setfam_1(sK1,sK3),k1_zfmisc_1(sK1))
    | ~ m1_subset_1(sK3,k1_zfmisc_1(k1_zfmisc_1(sK1))) ),
    inference(instantiation,[status(thm)],[c_7])).

cnf(c_861,plain,
    ( m1_subset_1(k8_setfam_1(sK1,sK3),k1_zfmisc_1(sK1)) = iProver_top
    | m1_subset_1(sK3,k1_zfmisc_1(k1_zfmisc_1(sK1))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_860])).

cnf(c_11,plain,
    ( r1_tarski(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ),
    inference(cnf_transformation,[],[f48])).

cnf(c_954,plain,
    ( r1_tarski(k8_setfam_1(sK1,sK3),sK1)
    | ~ m1_subset_1(k8_setfam_1(sK1,sK3),k1_zfmisc_1(sK1)) ),
    inference(instantiation,[status(thm)],[c_11])).

cnf(c_955,plain,
    ( r1_tarski(k8_setfam_1(sK1,sK3),sK1) = iProver_top
    | m1_subset_1(k8_setfam_1(sK1,sK3),k1_zfmisc_1(sK1)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_954])).

cnf(c_3076,plain,
    ( sK3 = k1_xboole_0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_2968,c_18,c_861,c_955])).

cnf(c_732,plain,
    ( r1_tarski(sK2,sK3) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_14])).

cnf(c_4,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | ~ v1_xboole_0(X1)
    | v1_xboole_0(X0) ),
    inference(cnf_transformation,[],[f41])).

cnf(c_10,plain,
    ( ~ r1_tarski(X0,X1)
    | m1_subset_1(X0,k1_zfmisc_1(X1)) ),
    inference(cnf_transformation,[],[f49])).

cnf(c_129,plain,
    ( ~ r1_tarski(X0,X1)
    | m1_subset_1(X0,k1_zfmisc_1(X1)) ),
    inference(prop_impl,[status(thm)],[c_10])).

cnf(c_157,plain,
    ( ~ r1_tarski(X0,X1)
    | ~ v1_xboole_0(X1)
    | v1_xboole_0(X0) ),
    inference(bin_hyper_res,[status(thm)],[c_4,c_129])).

cnf(c_729,plain,
    ( r1_tarski(X0,X1) != iProver_top
    | v1_xboole_0(X1) != iProver_top
    | v1_xboole_0(X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_157])).

cnf(c_1784,plain,
    ( v1_xboole_0(sK2) = iProver_top
    | v1_xboole_0(sK3) != iProver_top ),
    inference(superposition,[status(thm)],[c_732,c_729])).

cnf(c_3083,plain,
    ( v1_xboole_0(sK2) = iProver_top
    | v1_xboole_0(k1_xboole_0) != iProver_top ),
    inference(demodulation,[status(thm)],[c_3076,c_1784])).

cnf(c_4467,plain,
    ( k5_xboole_0(k1_tarski(sK0(k1_xboole_0)),k5_xboole_0(k1_xboole_0,k1_setfam_1(k2_tarski(k1_xboole_0,k1_tarski(sK0(k1_xboole_0)))))) = k1_xboole_0
    | v1_xboole_0(sK2) = iProver_top ),
    inference(superposition,[status(thm)],[c_1139,c_3083])).

cnf(c_2,plain,
    ( k5_xboole_0(k1_tarski(X0),k5_xboole_0(X1,k1_setfam_1(k2_tarski(X1,k1_tarski(X0))))) != k1_xboole_0 ),
    inference(cnf_transformation,[],[f58])).

cnf(c_4889,plain,
    ( v1_xboole_0(sK2) = iProver_top ),
    inference(forward_subsumption_resolution,[status(thm)],[c_4467,c_2])).

cnf(c_0,plain,
    ( ~ v1_xboole_0(X0)
    | k1_xboole_0 = X0 ),
    inference(cnf_transformation,[],[f35])).

cnf(c_742,plain,
    ( k1_xboole_0 = X0
    | v1_xboole_0(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_0])).

cnf(c_4892,plain,
    ( sK2 = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_4889,c_742])).

cnf(c_3088,plain,
    ( r1_tarski(k8_setfam_1(sK1,k1_xboole_0),k8_setfam_1(sK1,sK2)) != iProver_top ),
    inference(demodulation,[status(thm)],[c_3076,c_733])).

cnf(c_3089,plain,
    ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_zfmisc_1(sK1))) = iProver_top ),
    inference(demodulation,[status(thm)],[c_3076,c_731])).

cnf(c_3290,plain,
    ( k8_setfam_1(sK1,k1_xboole_0) = sK1 ),
    inference(superposition,[status(thm)],[c_3089,c_740])).

cnf(c_3648,plain,
    ( r1_tarski(sK1,k8_setfam_1(sK1,sK2)) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_3088,c_3290])).

cnf(c_5159,plain,
    ( r1_tarski(sK1,k8_setfam_1(sK1,k1_xboole_0)) != iProver_top ),
    inference(demodulation,[status(thm)],[c_4892,c_3648])).

cnf(c_5172,plain,
    ( r1_tarski(sK1,sK1) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_5159,c_3290])).

cnf(c_738,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(k1_zfmisc_1(X1))) != iProver_top
    | m1_subset_1(k8_setfam_1(X1,X0),k1_zfmisc_1(X1)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_7])).

cnf(c_735,plain,
    ( r1_tarski(X0,X1) = iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(X1)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_11])).

cnf(c_1402,plain,
    ( r1_tarski(k8_setfam_1(X0,X1),X0) = iProver_top
    | m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) != iProver_top ),
    inference(superposition,[status(thm)],[c_738,c_735])).

cnf(c_3291,plain,
    ( r1_tarski(k8_setfam_1(sK1,k1_xboole_0),sK1) = iProver_top ),
    inference(superposition,[status(thm)],[c_3089,c_1402])).

cnf(c_3298,plain,
    ( r1_tarski(sK1,sK1) = iProver_top ),
    inference(demodulation,[status(thm)],[c_3290,c_3291])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_5172,c_3298])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.12  % Command    : iproveropt_run.sh %d %s
% 0.12/0.33  % Computer   : n006.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.33  % CPULimit   : 60
% 0.12/0.33  % WCLimit    : 600
% 0.12/0.33  % DateTime   : Tue Dec  1 15:55:07 EST 2020
% 0.12/0.33  % CPUTime    : 
% 0.12/0.33  % Running in FOF mode
% 2.53/0.99  % SZS status Started for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.53/0.99  
% 2.53/0.99  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 2.53/0.99  
% 2.53/0.99  ------  iProver source info
% 2.53/0.99  
% 2.53/0.99  git: date: 2020-06-30 10:37:57 +0100
% 2.53/0.99  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 2.53/0.99  git: non_committed_changes: false
% 2.53/0.99  git: last_make_outside_of_git: false
% 2.53/0.99  
% 2.53/0.99  ------ 
% 2.53/0.99  
% 2.53/0.99  ------ Input Options
% 2.53/0.99  
% 2.53/0.99  --out_options                           all
% 2.53/0.99  --tptp_safe_out                         true
% 2.53/0.99  --problem_path                          ""
% 2.53/0.99  --include_path                          ""
% 2.53/0.99  --clausifier                            res/vclausify_rel
% 2.53/0.99  --clausifier_options                    --mode clausify
% 2.53/0.99  --stdin                                 false
% 2.53/0.99  --stats_out                             all
% 2.53/0.99  
% 2.53/0.99  ------ General Options
% 2.53/0.99  
% 2.53/0.99  --fof                                   false
% 2.53/0.99  --time_out_real                         305.
% 2.53/0.99  --time_out_virtual                      -1.
% 2.53/0.99  --symbol_type_check                     false
% 2.53/0.99  --clausify_out                          false
% 2.53/0.99  --sig_cnt_out                           false
% 2.53/0.99  --trig_cnt_out                          false
% 2.53/0.99  --trig_cnt_out_tolerance                1.
% 2.53/0.99  --trig_cnt_out_sk_spl                   false
% 2.53/0.99  --abstr_cl_out                          false
% 2.53/0.99  
% 2.53/0.99  ------ Global Options
% 2.53/0.99  
% 2.53/0.99  --schedule                              default
% 2.53/0.99  --add_important_lit                     false
% 2.53/0.99  --prop_solver_per_cl                    1000
% 2.53/0.99  --min_unsat_core                        false
% 2.53/0.99  --soft_assumptions                      false
% 2.53/0.99  --soft_lemma_size                       3
% 2.53/0.99  --prop_impl_unit_size                   0
% 2.53/0.99  --prop_impl_unit                        []
% 2.53/0.99  --share_sel_clauses                     true
% 2.53/0.99  --reset_solvers                         false
% 2.53/0.99  --bc_imp_inh                            [conj_cone]
% 2.53/0.99  --conj_cone_tolerance                   3.
% 2.53/0.99  --extra_neg_conj                        none
% 2.53/0.99  --large_theory_mode                     true
% 2.53/0.99  --prolific_symb_bound                   200
% 2.53/0.99  --lt_threshold                          2000
% 2.53/0.99  --clause_weak_htbl                      true
% 2.53/0.99  --gc_record_bc_elim                     false
% 2.53/0.99  
% 2.53/0.99  ------ Preprocessing Options
% 2.53/0.99  
% 2.53/0.99  --preprocessing_flag                    true
% 2.53/0.99  --time_out_prep_mult                    0.1
% 2.53/0.99  --splitting_mode                        input
% 2.53/0.99  --splitting_grd                         true
% 2.53/0.99  --splitting_cvd                         false
% 2.53/0.99  --splitting_cvd_svl                     false
% 2.53/0.99  --splitting_nvd                         32
% 2.53/0.99  --sub_typing                            true
% 2.53/0.99  --prep_gs_sim                           true
% 2.53/0.99  --prep_unflatten                        true
% 2.53/0.99  --prep_res_sim                          true
% 2.53/0.99  --prep_upred                            true
% 2.53/0.99  --prep_sem_filter                       exhaustive
% 2.53/0.99  --prep_sem_filter_out                   false
% 2.53/0.99  --pred_elim                             true
% 2.53/0.99  --res_sim_input                         true
% 2.53/0.99  --eq_ax_congr_red                       true
% 2.53/0.99  --pure_diseq_elim                       true
% 2.53/0.99  --brand_transform                       false
% 2.53/0.99  --non_eq_to_eq                          false
% 2.53/0.99  --prep_def_merge                        true
% 2.53/0.99  --prep_def_merge_prop_impl              false
% 2.53/0.99  --prep_def_merge_mbd                    true
% 2.53/0.99  --prep_def_merge_tr_red                 false
% 2.53/0.99  --prep_def_merge_tr_cl                  false
% 2.53/0.99  --smt_preprocessing                     true
% 2.53/0.99  --smt_ac_axioms                         fast
% 2.53/0.99  --preprocessed_out                      false
% 2.53/0.99  --preprocessed_stats                    false
% 2.53/0.99  
% 2.53/0.99  ------ Abstraction refinement Options
% 2.53/0.99  
% 2.53/0.99  --abstr_ref                             []
% 2.53/0.99  --abstr_ref_prep                        false
% 2.53/0.99  --abstr_ref_until_sat                   false
% 2.53/0.99  --abstr_ref_sig_restrict                funpre
% 2.53/0.99  --abstr_ref_af_restrict_to_split_sk     false
% 2.53/0.99  --abstr_ref_under                       []
% 2.53/0.99  
% 2.53/0.99  ------ SAT Options
% 2.53/0.99  
% 2.53/0.99  --sat_mode                              false
% 2.53/0.99  --sat_fm_restart_options                ""
% 2.53/0.99  --sat_gr_def                            false
% 2.53/0.99  --sat_epr_types                         true
% 2.53/0.99  --sat_non_cyclic_types                  false
% 2.53/0.99  --sat_finite_models                     false
% 2.53/0.99  --sat_fm_lemmas                         false
% 2.53/0.99  --sat_fm_prep                           false
% 2.53/0.99  --sat_fm_uc_incr                        true
% 2.53/0.99  --sat_out_model                         small
% 2.53/0.99  --sat_out_clauses                       false
% 2.53/0.99  
% 2.53/0.99  ------ QBF Options
% 2.53/0.99  
% 2.53/0.99  --qbf_mode                              false
% 2.53/0.99  --qbf_elim_univ                         false
% 2.53/0.99  --qbf_dom_inst                          none
% 2.53/0.99  --qbf_dom_pre_inst                      false
% 2.53/0.99  --qbf_sk_in                             false
% 2.53/0.99  --qbf_pred_elim                         true
% 2.53/0.99  --qbf_split                             512
% 2.53/0.99  
% 2.53/0.99  ------ BMC1 Options
% 2.53/0.99  
% 2.53/0.99  --bmc1_incremental                      false
% 2.53/0.99  --bmc1_axioms                           reachable_all
% 2.53/0.99  --bmc1_min_bound                        0
% 2.53/0.99  --bmc1_max_bound                        -1
% 2.53/0.99  --bmc1_max_bound_default                -1
% 2.53/0.99  --bmc1_symbol_reachability              true
% 2.53/0.99  --bmc1_property_lemmas                  false
% 2.53/0.99  --bmc1_k_induction                      false
% 2.53/0.99  --bmc1_non_equiv_states                 false
% 2.53/0.99  --bmc1_deadlock                         false
% 2.53/0.99  --bmc1_ucm                              false
% 2.53/0.99  --bmc1_add_unsat_core                   none
% 2.53/0.99  --bmc1_unsat_core_children              false
% 2.53/0.99  --bmc1_unsat_core_extrapolate_axioms    false
% 2.53/0.99  --bmc1_out_stat                         full
% 2.53/0.99  --bmc1_ground_init                      false
% 2.53/0.99  --bmc1_pre_inst_next_state              false
% 2.53/0.99  --bmc1_pre_inst_state                   false
% 2.53/0.99  --bmc1_pre_inst_reach_state             false
% 2.53/0.99  --bmc1_out_unsat_core                   false
% 2.53/0.99  --bmc1_aig_witness_out                  false
% 2.53/0.99  --bmc1_verbose                          false
% 2.53/0.99  --bmc1_dump_clauses_tptp                false
% 2.53/0.99  --bmc1_dump_unsat_core_tptp             false
% 2.53/0.99  --bmc1_dump_file                        -
% 2.53/0.99  --bmc1_ucm_expand_uc_limit              128
% 2.53/0.99  --bmc1_ucm_n_expand_iterations          6
% 2.53/0.99  --bmc1_ucm_extend_mode                  1
% 2.53/0.99  --bmc1_ucm_init_mode                    2
% 2.53/0.99  --bmc1_ucm_cone_mode                    none
% 2.53/0.99  --bmc1_ucm_reduced_relation_type        0
% 2.53/0.99  --bmc1_ucm_relax_model                  4
% 2.53/0.99  --bmc1_ucm_full_tr_after_sat            true
% 2.53/0.99  --bmc1_ucm_expand_neg_assumptions       false
% 2.53/0.99  --bmc1_ucm_layered_model                none
% 2.53/0.99  --bmc1_ucm_max_lemma_size               10
% 2.53/0.99  
% 2.53/0.99  ------ AIG Options
% 2.53/0.99  
% 2.53/0.99  --aig_mode                              false
% 2.53/0.99  
% 2.53/0.99  ------ Instantiation Options
% 2.53/0.99  
% 2.53/0.99  --instantiation_flag                    true
% 2.53/0.99  --inst_sos_flag                         false
% 2.53/0.99  --inst_sos_phase                        true
% 2.53/0.99  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 2.53/0.99  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 2.53/0.99  --inst_lit_sel_side                     num_symb
% 2.53/0.99  --inst_solver_per_active                1400
% 2.53/0.99  --inst_solver_calls_frac                1.
% 2.53/0.99  --inst_passive_queue_type               priority_queues
% 2.53/0.99  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 2.53/0.99  --inst_passive_queues_freq              [25;2]
% 2.53/0.99  --inst_dismatching                      true
% 2.53/0.99  --inst_eager_unprocessed_to_passive     true
% 2.53/0.99  --inst_prop_sim_given                   true
% 2.53/0.99  --inst_prop_sim_new                     false
% 2.53/0.99  --inst_subs_new                         false
% 2.53/0.99  --inst_eq_res_simp                      false
% 2.53/0.99  --inst_subs_given                       false
% 2.53/0.99  --inst_orphan_elimination               true
% 2.53/0.99  --inst_learning_loop_flag               true
% 2.53/0.99  --inst_learning_start                   3000
% 2.53/0.99  --inst_learning_factor                  2
% 2.53/0.99  --inst_start_prop_sim_after_learn       3
% 2.53/0.99  --inst_sel_renew                        solver
% 2.53/0.99  --inst_lit_activity_flag                true
% 2.53/0.99  --inst_restr_to_given                   false
% 2.53/0.99  --inst_activity_threshold               500
% 2.53/0.99  --inst_out_proof                        true
% 2.53/0.99  
% 2.53/0.99  ------ Resolution Options
% 2.53/0.99  
% 2.53/0.99  --resolution_flag                       true
% 2.53/0.99  --res_lit_sel                           adaptive
% 2.53/0.99  --res_lit_sel_side                      none
% 2.53/0.99  --res_ordering                          kbo
% 2.53/0.99  --res_to_prop_solver                    active
% 2.53/0.99  --res_prop_simpl_new                    false
% 2.53/0.99  --res_prop_simpl_given                  true
% 2.53/0.99  --res_passive_queue_type                priority_queues
% 2.53/0.99  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 2.53/0.99  --res_passive_queues_freq               [15;5]
% 2.53/0.99  --res_forward_subs                      full
% 2.53/0.99  --res_backward_subs                     full
% 2.53/0.99  --res_forward_subs_resolution           true
% 2.53/0.99  --res_backward_subs_resolution          true
% 2.53/0.99  --res_orphan_elimination                true
% 2.53/0.99  --res_time_limit                        2.
% 2.53/0.99  --res_out_proof                         true
% 2.53/0.99  
% 2.53/0.99  ------ Superposition Options
% 2.53/0.99  
% 2.53/0.99  --superposition_flag                    true
% 2.53/0.99  --sup_passive_queue_type                priority_queues
% 2.53/0.99  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 2.53/0.99  --sup_passive_queues_freq               [8;1;4]
% 2.53/0.99  --demod_completeness_check              fast
% 2.53/0.99  --demod_use_ground                      true
% 2.53/0.99  --sup_to_prop_solver                    passive
% 2.53/0.99  --sup_prop_simpl_new                    true
% 2.53/0.99  --sup_prop_simpl_given                  true
% 2.53/0.99  --sup_fun_splitting                     false
% 2.53/0.99  --sup_smt_interval                      50000
% 2.53/0.99  
% 2.53/0.99  ------ Superposition Simplification Setup
% 2.53/0.99  
% 2.53/0.99  --sup_indices_passive                   []
% 2.53/0.99  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.53/0.99  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.53/0.99  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.53/0.99  --sup_full_triv                         [TrivRules;PropSubs]
% 2.53/0.99  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.53/0.99  --sup_full_bw                           [BwDemod]
% 2.53/0.99  --sup_immed_triv                        [TrivRules]
% 2.53/0.99  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 2.53/0.99  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.53/0.99  --sup_immed_bw_main                     []
% 2.53/0.99  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.53/0.99  --sup_input_triv                        [Unflattening;TrivRules]
% 2.53/0.99  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.53/0.99  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.53/0.99  
% 2.53/0.99  ------ Combination Options
% 2.53/0.99  
% 2.53/0.99  --comb_res_mult                         3
% 2.53/0.99  --comb_sup_mult                         2
% 2.53/0.99  --comb_inst_mult                        10
% 2.53/0.99  
% 2.53/0.99  ------ Debug Options
% 2.53/0.99  
% 2.53/0.99  --dbg_backtrace                         false
% 2.53/0.99  --dbg_dump_prop_clauses                 false
% 2.53/0.99  --dbg_dump_prop_clauses_file            -
% 2.53/0.99  --dbg_out_stat                          false
% 2.53/0.99  ------ Parsing...
% 2.53/0.99  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 2.53/0.99  
% 2.53/0.99  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe:1:0s pe_e  sf_s  rm: 1 0s  sf_e  pe_s  pe_e 
% 2.53/0.99  
% 2.53/0.99  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 2.53/0.99  
% 2.53/0.99  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 2.53/0.99  ------ Proving...
% 2.53/0.99  ------ Problem Properties 
% 2.53/0.99  
% 2.53/0.99  
% 2.53/0.99  clauses                                 16
% 2.53/0.99  conjectures                             4
% 2.53/0.99  EPR                                     3
% 2.53/0.99  Horn                                    13
% 2.53/0.99  unary                                   6
% 2.53/0.99  binary                                  6
% 2.53/0.99  lits                                    30
% 2.53/0.99  lits eq                                 8
% 2.53/0.99  fd_pure                                 0
% 2.53/0.99  fd_pseudo                               0
% 2.53/0.99  fd_cond                                 3
% 2.53/0.99  fd_pseudo_cond                          0
% 2.53/0.99  AC symbols                              0
% 2.53/0.99  
% 2.53/0.99  ------ Schedule dynamic 5 is on 
% 2.53/0.99  
% 2.53/0.99  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" Time Limit: 10.
% 2.53/0.99  
% 2.53/0.99  
% 2.53/0.99  ------ 
% 2.53/0.99  Current options:
% 2.53/0.99  ------ 
% 2.53/0.99  
% 2.53/0.99  ------ Input Options
% 2.53/0.99  
% 2.53/0.99  --out_options                           all
% 2.53/0.99  --tptp_safe_out                         true
% 2.53/0.99  --problem_path                          ""
% 2.53/0.99  --include_path                          ""
% 2.53/0.99  --clausifier                            res/vclausify_rel
% 2.53/0.99  --clausifier_options                    --mode clausify
% 2.53/0.99  --stdin                                 false
% 2.53/0.99  --stats_out                             all
% 2.53/0.99  
% 2.53/0.99  ------ General Options
% 2.53/0.99  
% 2.53/0.99  --fof                                   false
% 2.53/0.99  --time_out_real                         305.
% 2.53/0.99  --time_out_virtual                      -1.
% 2.53/0.99  --symbol_type_check                     false
% 2.53/0.99  --clausify_out                          false
% 2.53/0.99  --sig_cnt_out                           false
% 2.53/0.99  --trig_cnt_out                          false
% 2.53/0.99  --trig_cnt_out_tolerance                1.
% 2.53/0.99  --trig_cnt_out_sk_spl                   false
% 2.53/0.99  --abstr_cl_out                          false
% 2.53/0.99  
% 2.53/0.99  ------ Global Options
% 2.53/0.99  
% 2.53/0.99  --schedule                              default
% 2.53/0.99  --add_important_lit                     false
% 2.53/0.99  --prop_solver_per_cl                    1000
% 2.53/0.99  --min_unsat_core                        false
% 2.53/0.99  --soft_assumptions                      false
% 2.53/0.99  --soft_lemma_size                       3
% 2.53/0.99  --prop_impl_unit_size                   0
% 2.53/0.99  --prop_impl_unit                        []
% 2.53/0.99  --share_sel_clauses                     true
% 2.53/0.99  --reset_solvers                         false
% 2.53/0.99  --bc_imp_inh                            [conj_cone]
% 2.53/0.99  --conj_cone_tolerance                   3.
% 2.53/0.99  --extra_neg_conj                        none
% 2.53/0.99  --large_theory_mode                     true
% 2.53/0.99  --prolific_symb_bound                   200
% 2.53/0.99  --lt_threshold                          2000
% 2.53/0.99  --clause_weak_htbl                      true
% 2.53/0.99  --gc_record_bc_elim                     false
% 2.53/0.99  
% 2.53/0.99  ------ Preprocessing Options
% 2.53/0.99  
% 2.53/0.99  --preprocessing_flag                    true
% 2.53/0.99  --time_out_prep_mult                    0.1
% 2.53/0.99  --splitting_mode                        input
% 2.53/0.99  --splitting_grd                         true
% 2.53/0.99  --splitting_cvd                         false
% 2.53/0.99  --splitting_cvd_svl                     false
% 2.53/0.99  --splitting_nvd                         32
% 2.53/0.99  --sub_typing                            true
% 2.53/0.99  --prep_gs_sim                           true
% 2.53/0.99  --prep_unflatten                        true
% 2.53/0.99  --prep_res_sim                          true
% 2.53/0.99  --prep_upred                            true
% 2.53/0.99  --prep_sem_filter                       exhaustive
% 2.53/0.99  --prep_sem_filter_out                   false
% 2.53/0.99  --pred_elim                             true
% 2.53/0.99  --res_sim_input                         true
% 2.53/0.99  --eq_ax_congr_red                       true
% 2.53/0.99  --pure_diseq_elim                       true
% 2.53/0.99  --brand_transform                       false
% 2.53/0.99  --non_eq_to_eq                          false
% 2.53/0.99  --prep_def_merge                        true
% 2.53/0.99  --prep_def_merge_prop_impl              false
% 2.53/0.99  --prep_def_merge_mbd                    true
% 2.53/0.99  --prep_def_merge_tr_red                 false
% 2.53/0.99  --prep_def_merge_tr_cl                  false
% 2.53/0.99  --smt_preprocessing                     true
% 2.53/0.99  --smt_ac_axioms                         fast
% 2.53/0.99  --preprocessed_out                      false
% 2.53/0.99  --preprocessed_stats                    false
% 2.53/0.99  
% 2.53/0.99  ------ Abstraction refinement Options
% 2.53/0.99  
% 2.53/0.99  --abstr_ref                             []
% 2.53/0.99  --abstr_ref_prep                        false
% 2.53/0.99  --abstr_ref_until_sat                   false
% 2.53/0.99  --abstr_ref_sig_restrict                funpre
% 2.53/0.99  --abstr_ref_af_restrict_to_split_sk     false
% 2.53/0.99  --abstr_ref_under                       []
% 2.53/0.99  
% 2.53/0.99  ------ SAT Options
% 2.53/0.99  
% 2.53/0.99  --sat_mode                              false
% 2.53/0.99  --sat_fm_restart_options                ""
% 2.53/0.99  --sat_gr_def                            false
% 2.53/0.99  --sat_epr_types                         true
% 2.53/0.99  --sat_non_cyclic_types                  false
% 2.53/0.99  --sat_finite_models                     false
% 2.53/0.99  --sat_fm_lemmas                         false
% 2.53/0.99  --sat_fm_prep                           false
% 2.53/0.99  --sat_fm_uc_incr                        true
% 2.53/0.99  --sat_out_model                         small
% 2.53/0.99  --sat_out_clauses                       false
% 2.53/0.99  
% 2.53/0.99  ------ QBF Options
% 2.53/0.99  
% 2.53/0.99  --qbf_mode                              false
% 2.53/0.99  --qbf_elim_univ                         false
% 2.53/0.99  --qbf_dom_inst                          none
% 2.53/0.99  --qbf_dom_pre_inst                      false
% 2.53/0.99  --qbf_sk_in                             false
% 2.53/0.99  --qbf_pred_elim                         true
% 2.53/0.99  --qbf_split                             512
% 2.53/0.99  
% 2.53/0.99  ------ BMC1 Options
% 2.53/0.99  
% 2.53/0.99  --bmc1_incremental                      false
% 2.53/0.99  --bmc1_axioms                           reachable_all
% 2.53/0.99  --bmc1_min_bound                        0
% 2.53/0.99  --bmc1_max_bound                        -1
% 2.53/0.99  --bmc1_max_bound_default                -1
% 2.53/0.99  --bmc1_symbol_reachability              true
% 2.53/0.99  --bmc1_property_lemmas                  false
% 2.53/0.99  --bmc1_k_induction                      false
% 2.53/0.99  --bmc1_non_equiv_states                 false
% 2.53/0.99  --bmc1_deadlock                         false
% 2.53/0.99  --bmc1_ucm                              false
% 2.53/0.99  --bmc1_add_unsat_core                   none
% 2.53/0.99  --bmc1_unsat_core_children              false
% 2.53/0.99  --bmc1_unsat_core_extrapolate_axioms    false
% 2.53/0.99  --bmc1_out_stat                         full
% 2.53/0.99  --bmc1_ground_init                      false
% 2.53/0.99  --bmc1_pre_inst_next_state              false
% 2.53/0.99  --bmc1_pre_inst_state                   false
% 2.53/0.99  --bmc1_pre_inst_reach_state             false
% 2.53/0.99  --bmc1_out_unsat_core                   false
% 2.53/0.99  --bmc1_aig_witness_out                  false
% 2.53/0.99  --bmc1_verbose                          false
% 2.53/0.99  --bmc1_dump_clauses_tptp                false
% 2.53/0.99  --bmc1_dump_unsat_core_tptp             false
% 2.53/0.99  --bmc1_dump_file                        -
% 2.53/0.99  --bmc1_ucm_expand_uc_limit              128
% 2.53/0.99  --bmc1_ucm_n_expand_iterations          6
% 2.53/0.99  --bmc1_ucm_extend_mode                  1
% 2.53/0.99  --bmc1_ucm_init_mode                    2
% 2.53/0.99  --bmc1_ucm_cone_mode                    none
% 2.53/0.99  --bmc1_ucm_reduced_relation_type        0
% 2.53/0.99  --bmc1_ucm_relax_model                  4
% 2.53/0.99  --bmc1_ucm_full_tr_after_sat            true
% 2.53/0.99  --bmc1_ucm_expand_neg_assumptions       false
% 2.53/0.99  --bmc1_ucm_layered_model                none
% 2.53/0.99  --bmc1_ucm_max_lemma_size               10
% 2.53/0.99  
% 2.53/0.99  ------ AIG Options
% 2.53/0.99  
% 2.53/0.99  --aig_mode                              false
% 2.53/0.99  
% 2.53/0.99  ------ Instantiation Options
% 2.53/0.99  
% 2.53/0.99  --instantiation_flag                    true
% 2.53/0.99  --inst_sos_flag                         false
% 2.53/0.99  --inst_sos_phase                        true
% 2.53/0.99  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 2.53/0.99  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 2.53/0.99  --inst_lit_sel_side                     none
% 2.53/0.99  --inst_solver_per_active                1400
% 2.53/0.99  --inst_solver_calls_frac                1.
% 2.53/0.99  --inst_passive_queue_type               priority_queues
% 2.53/0.99  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 2.53/0.99  --inst_passive_queues_freq              [25;2]
% 2.53/0.99  --inst_dismatching                      true
% 2.53/0.99  --inst_eager_unprocessed_to_passive     true
% 2.53/0.99  --inst_prop_sim_given                   true
% 2.53/0.99  --inst_prop_sim_new                     false
% 2.53/0.99  --inst_subs_new                         false
% 2.53/0.99  --inst_eq_res_simp                      false
% 2.53/0.99  --inst_subs_given                       false
% 2.53/0.99  --inst_orphan_elimination               true
% 2.53/0.99  --inst_learning_loop_flag               true
% 2.53/0.99  --inst_learning_start                   3000
% 2.53/0.99  --inst_learning_factor                  2
% 2.53/0.99  --inst_start_prop_sim_after_learn       3
% 2.53/0.99  --inst_sel_renew                        solver
% 2.53/0.99  --inst_lit_activity_flag                true
% 2.53/0.99  --inst_restr_to_given                   false
% 2.53/0.99  --inst_activity_threshold               500
% 2.53/0.99  --inst_out_proof                        true
% 2.53/0.99  
% 2.53/0.99  ------ Resolution Options
% 2.53/0.99  
% 2.53/0.99  --resolution_flag                       false
% 2.53/0.99  --res_lit_sel                           adaptive
% 2.53/0.99  --res_lit_sel_side                      none
% 2.53/0.99  --res_ordering                          kbo
% 2.53/0.99  --res_to_prop_solver                    active
% 2.53/0.99  --res_prop_simpl_new                    false
% 2.53/0.99  --res_prop_simpl_given                  true
% 2.53/0.99  --res_passive_queue_type                priority_queues
% 2.53/0.99  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 2.53/0.99  --res_passive_queues_freq               [15;5]
% 2.53/0.99  --res_forward_subs                      full
% 2.53/0.99  --res_backward_subs                     full
% 2.53/0.99  --res_forward_subs_resolution           true
% 2.53/0.99  --res_backward_subs_resolution          true
% 2.53/0.99  --res_orphan_elimination                true
% 2.53/0.99  --res_time_limit                        2.
% 2.53/0.99  --res_out_proof                         true
% 2.53/0.99  
% 2.53/0.99  ------ Superposition Options
% 2.53/0.99  
% 2.53/0.99  --superposition_flag                    true
% 2.53/0.99  --sup_passive_queue_type                priority_queues
% 2.53/0.99  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 2.53/0.99  --sup_passive_queues_freq               [8;1;4]
% 2.53/0.99  --demod_completeness_check              fast
% 2.53/0.99  --demod_use_ground                      true
% 2.53/0.99  --sup_to_prop_solver                    passive
% 2.53/0.99  --sup_prop_simpl_new                    true
% 2.53/0.99  --sup_prop_simpl_given                  true
% 2.53/0.99  --sup_fun_splitting                     false
% 2.53/0.99  --sup_smt_interval                      50000
% 2.53/0.99  
% 2.53/0.99  ------ Superposition Simplification Setup
% 2.53/0.99  
% 2.53/0.99  --sup_indices_passive                   []
% 2.53/0.99  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.53/0.99  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.53/0.99  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.53/0.99  --sup_full_triv                         [TrivRules;PropSubs]
% 2.53/0.99  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.53/0.99  --sup_full_bw                           [BwDemod]
% 2.53/0.99  --sup_immed_triv                        [TrivRules]
% 2.53/0.99  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 2.53/0.99  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.53/0.99  --sup_immed_bw_main                     []
% 2.53/0.99  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.53/0.99  --sup_input_triv                        [Unflattening;TrivRules]
% 2.53/0.99  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.53/0.99  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.53/0.99  
% 2.53/0.99  ------ Combination Options
% 2.53/0.99  
% 2.53/0.99  --comb_res_mult                         3
% 2.53/0.99  --comb_sup_mult                         2
% 2.53/0.99  --comb_inst_mult                        10
% 2.53/0.99  
% 2.53/0.99  ------ Debug Options
% 2.53/0.99  
% 2.53/0.99  --dbg_backtrace                         false
% 2.53/0.99  --dbg_dump_prop_clauses                 false
% 2.53/0.99  --dbg_dump_prop_clauses_file            -
% 2.53/0.99  --dbg_out_stat                          false
% 2.53/0.99  
% 2.53/0.99  
% 2.53/0.99  
% 2.53/0.99  
% 2.53/0.99  ------ Proving...
% 2.53/0.99  
% 2.53/0.99  
% 2.53/0.99  % SZS status Theorem for theBenchmark.p
% 2.53/0.99  
% 2.53/0.99  % SZS output start CNFRefutation for theBenchmark.p
% 2.53/0.99  
% 2.53/0.99  fof(f6,axiom,(
% 2.53/0.99    ! [X0] : ? [X1] : m1_subset_1(X1,X0)),
% 2.53/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.53/0.99  
% 2.53/0.99  fof(f29,plain,(
% 2.53/0.99    ! [X0] : (? [X1] : m1_subset_1(X1,X0) => m1_subset_1(sK0(X0),X0))),
% 2.53/0.99    introduced(choice_axiom,[])).
% 2.53/0.99  
% 2.53/0.99  fof(f30,plain,(
% 2.53/0.99    ! [X0] : m1_subset_1(sK0(X0),X0)),
% 2.53/0.99    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f6,f29])).
% 2.53/0.99  
% 2.53/0.99  fof(f40,plain,(
% 2.53/0.99    ( ! [X0] : (m1_subset_1(sK0(X0),X0)) )),
% 2.53/0.99    inference(cnf_transformation,[],[f30])).
% 2.53/0.99  
% 2.53/0.99  fof(f12,axiom,(
% 2.53/0.99    ! [X0,X1] : (m1_subset_1(X0,X1) => (r2_hidden(X0,X1) | v1_xboole_0(X1)))),
% 2.53/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.53/0.99  
% 2.53/0.99  fof(f23,plain,(
% 2.53/0.99    ! [X0,X1] : ((r2_hidden(X0,X1) | v1_xboole_0(X1)) | ~m1_subset_1(X0,X1))),
% 2.53/0.99    inference(ennf_transformation,[],[f12])).
% 2.53/0.99  
% 2.53/0.99  fof(f24,plain,(
% 2.53/0.99    ! [X0,X1] : (r2_hidden(X0,X1) | v1_xboole_0(X1) | ~m1_subset_1(X0,X1))),
% 2.53/0.99    inference(flattening,[],[f23])).
% 2.53/0.99  
% 2.53/0.99  fof(f47,plain,(
% 2.53/0.99    ( ! [X0,X1] : (r2_hidden(X0,X1) | v1_xboole_0(X1) | ~m1_subset_1(X0,X1)) )),
% 2.53/0.99    inference(cnf_transformation,[],[f24])).
% 2.53/0.99  
% 2.53/0.99  fof(f4,axiom,(
% 2.53/0.99    ! [X0,X1] : (r2_hidden(X0,X1) => k2_xboole_0(k1_tarski(X0),X1) = X1)),
% 2.53/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.53/0.99  
% 2.53/0.99  fof(f18,plain,(
% 2.53/0.99    ! [X0,X1] : (k2_xboole_0(k1_tarski(X0),X1) = X1 | ~r2_hidden(X0,X1))),
% 2.53/0.99    inference(ennf_transformation,[],[f4])).
% 2.53/0.99  
% 2.53/0.99  fof(f38,plain,(
% 2.53/0.99    ( ! [X0,X1] : (k2_xboole_0(k1_tarski(X0),X1) = X1 | ~r2_hidden(X0,X1)) )),
% 2.53/0.99    inference(cnf_transformation,[],[f18])).
% 2.53/0.99  
% 2.53/0.99  fof(f3,axiom,(
% 2.53/0.99    ! [X0,X1] : k5_xboole_0(X0,k4_xboole_0(X1,X0)) = k2_xboole_0(X0,X1)),
% 2.53/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.53/0.99  
% 2.53/0.99  fof(f37,plain,(
% 2.53/0.99    ( ! [X0,X1] : (k5_xboole_0(X0,k4_xboole_0(X1,X0)) = k2_xboole_0(X0,X1)) )),
% 2.53/0.99    inference(cnf_transformation,[],[f3])).
% 2.53/0.99  
% 2.53/0.99  fof(f2,axiom,(
% 2.53/0.99    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))),
% 2.53/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.53/0.99  
% 2.53/0.99  fof(f36,plain,(
% 2.53/0.99    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))) )),
% 2.53/0.99    inference(cnf_transformation,[],[f2])).
% 2.53/0.99  
% 2.53/0.99  fof(f11,axiom,(
% 2.53/0.99    ! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1))),
% 2.53/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.53/0.99  
% 2.53/0.99  fof(f46,plain,(
% 2.53/0.99    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1))) )),
% 2.53/0.99    inference(cnf_transformation,[],[f11])).
% 2.53/0.99  
% 2.53/0.99  fof(f55,plain,(
% 2.53/0.99    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k5_xboole_0(X0,k1_setfam_1(k2_tarski(X0,X1)))) )),
% 2.53/0.99    inference(definition_unfolding,[],[f36,f46])).
% 2.53/0.99  
% 2.53/0.99  fof(f56,plain,(
% 2.53/0.99    ( ! [X0,X1] : (k5_xboole_0(X0,k5_xboole_0(X1,k1_setfam_1(k2_tarski(X1,X0)))) = k2_xboole_0(X0,X1)) )),
% 2.53/0.99    inference(definition_unfolding,[],[f37,f55])).
% 2.53/0.99  
% 2.53/0.99  fof(f57,plain,(
% 2.53/0.99    ( ! [X0,X1] : (k5_xboole_0(k1_tarski(X0),k5_xboole_0(X1,k1_setfam_1(k2_tarski(X1,k1_tarski(X0))))) = X1 | ~r2_hidden(X0,X1)) )),
% 2.53/0.99    inference(definition_unfolding,[],[f38,f56])).
% 2.53/0.99  
% 2.53/0.99  fof(f14,axiom,(
% 2.53/0.99    ! [X0,X1] : (r1_tarski(X0,X1) => (r1_tarski(k1_setfam_1(X1),k1_setfam_1(X0)) | k1_xboole_0 = X0))),
% 2.53/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.53/0.99  
% 2.53/0.99  fof(f25,plain,(
% 2.53/0.99    ! [X0,X1] : ((r1_tarski(k1_setfam_1(X1),k1_setfam_1(X0)) | k1_xboole_0 = X0) | ~r1_tarski(X0,X1))),
% 2.53/0.99    inference(ennf_transformation,[],[f14])).
% 2.53/0.99  
% 2.53/0.99  fof(f26,plain,(
% 2.53/0.99    ! [X0,X1] : (r1_tarski(k1_setfam_1(X1),k1_setfam_1(X0)) | k1_xboole_0 = X0 | ~r1_tarski(X0,X1))),
% 2.53/0.99    inference(flattening,[],[f25])).
% 2.53/0.99  
% 2.53/0.99  fof(f50,plain,(
% 2.53/0.99    ( ! [X0,X1] : (r1_tarski(k1_setfam_1(X1),k1_setfam_1(X0)) | k1_xboole_0 = X0 | ~r1_tarski(X0,X1)) )),
% 2.53/0.99    inference(cnf_transformation,[],[f26])).
% 2.53/0.99  
% 2.53/0.99  fof(f15,conjecture,(
% 2.53/0.99    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(X0))) => (r1_tarski(X1,X2) => r1_tarski(k8_setfam_1(X0,X2),k8_setfam_1(X0,X1)))))),
% 2.53/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.53/0.99  
% 2.53/0.99  fof(f16,negated_conjecture,(
% 2.53/0.99    ~! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(X0))) => (r1_tarski(X1,X2) => r1_tarski(k8_setfam_1(X0,X2),k8_setfam_1(X0,X1)))))),
% 2.53/0.99    inference(negated_conjecture,[],[f15])).
% 2.53/0.99  
% 2.53/0.99  fof(f27,plain,(
% 2.53/0.99    ? [X0,X1] : (? [X2] : ((~r1_tarski(k8_setfam_1(X0,X2),k8_setfam_1(X0,X1)) & r1_tarski(X1,X2)) & m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(X0)))) & m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))))),
% 2.53/0.99    inference(ennf_transformation,[],[f16])).
% 2.53/0.99  
% 2.53/0.99  fof(f28,plain,(
% 2.53/0.99    ? [X0,X1] : (? [X2] : (~r1_tarski(k8_setfam_1(X0,X2),k8_setfam_1(X0,X1)) & r1_tarski(X1,X2) & m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(X0)))) & m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))))),
% 2.53/0.99    inference(flattening,[],[f27])).
% 2.53/0.99  
% 2.53/0.99  fof(f33,plain,(
% 2.53/0.99    ( ! [X0,X1] : (? [X2] : (~r1_tarski(k8_setfam_1(X0,X2),k8_setfam_1(X0,X1)) & r1_tarski(X1,X2) & m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(X0)))) => (~r1_tarski(k8_setfam_1(X0,sK3),k8_setfam_1(X0,X1)) & r1_tarski(X1,sK3) & m1_subset_1(sK3,k1_zfmisc_1(k1_zfmisc_1(X0))))) )),
% 2.53/0.99    introduced(choice_axiom,[])).
% 2.53/0.99  
% 2.53/0.99  fof(f32,plain,(
% 2.53/0.99    ? [X0,X1] : (? [X2] : (~r1_tarski(k8_setfam_1(X0,X2),k8_setfam_1(X0,X1)) & r1_tarski(X1,X2) & m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(X0)))) & m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0)))) => (? [X2] : (~r1_tarski(k8_setfam_1(sK1,X2),k8_setfam_1(sK1,sK2)) & r1_tarski(sK2,X2) & m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(sK1)))) & m1_subset_1(sK2,k1_zfmisc_1(k1_zfmisc_1(sK1))))),
% 2.53/0.99    introduced(choice_axiom,[])).
% 2.53/0.99  
% 2.53/0.99  fof(f34,plain,(
% 2.53/0.99    (~r1_tarski(k8_setfam_1(sK1,sK3),k8_setfam_1(sK1,sK2)) & r1_tarski(sK2,sK3) & m1_subset_1(sK3,k1_zfmisc_1(k1_zfmisc_1(sK1)))) & m1_subset_1(sK2,k1_zfmisc_1(k1_zfmisc_1(sK1)))),
% 2.53/0.99    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1,sK2,sK3])],[f28,f33,f32])).
% 2.53/0.99  
% 2.53/0.99  fof(f52,plain,(
% 2.53/0.99    m1_subset_1(sK3,k1_zfmisc_1(k1_zfmisc_1(sK1)))),
% 2.53/0.99    inference(cnf_transformation,[],[f34])).
% 2.53/0.99  
% 2.53/0.99  fof(f8,axiom,(
% 2.53/0.99    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) => ((k1_xboole_0 = X1 => k8_setfam_1(X0,X1) = X0) & (k1_xboole_0 != X1 => k8_setfam_1(X0,X1) = k6_setfam_1(X0,X1))))),
% 2.53/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.53/0.99  
% 2.53/0.99  fof(f20,plain,(
% 2.53/0.99    ! [X0,X1] : (((k8_setfam_1(X0,X1) = X0 | k1_xboole_0 != X1) & (k8_setfam_1(X0,X1) = k6_setfam_1(X0,X1) | k1_xboole_0 = X1)) | ~m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))))),
% 2.53/0.99    inference(ennf_transformation,[],[f8])).
% 2.53/0.99  
% 2.53/0.99  fof(f42,plain,(
% 2.53/0.99    ( ! [X0,X1] : (k8_setfam_1(X0,X1) = k6_setfam_1(X0,X1) | k1_xboole_0 = X1 | ~m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0)))) )),
% 2.53/0.99    inference(cnf_transformation,[],[f20])).
% 2.53/0.99  
% 2.53/0.99  fof(f10,axiom,(
% 2.53/0.99    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) => k6_setfam_1(X0,X1) = k1_setfam_1(X1))),
% 2.53/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.53/0.99  
% 2.53/0.99  fof(f22,plain,(
% 2.53/0.99    ! [X0,X1] : (k6_setfam_1(X0,X1) = k1_setfam_1(X1) | ~m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))))),
% 2.53/0.99    inference(ennf_transformation,[],[f10])).
% 2.53/0.99  
% 2.53/0.99  fof(f45,plain,(
% 2.53/0.99    ( ! [X0,X1] : (k6_setfam_1(X0,X1) = k1_setfam_1(X1) | ~m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0)))) )),
% 2.53/0.99    inference(cnf_transformation,[],[f22])).
% 2.53/0.99  
% 2.53/0.99  fof(f51,plain,(
% 2.53/0.99    m1_subset_1(sK2,k1_zfmisc_1(k1_zfmisc_1(sK1)))),
% 2.53/0.99    inference(cnf_transformation,[],[f34])).
% 2.53/0.99  
% 2.53/0.99  fof(f54,plain,(
% 2.53/0.99    ~r1_tarski(k8_setfam_1(sK1,sK3),k8_setfam_1(sK1,sK2))),
% 2.53/0.99    inference(cnf_transformation,[],[f34])).
% 2.53/0.99  
% 2.53/0.99  fof(f53,plain,(
% 2.53/0.99    r1_tarski(sK2,sK3)),
% 2.53/0.99    inference(cnf_transformation,[],[f34])).
% 2.53/0.99  
% 2.53/0.99  fof(f43,plain,(
% 2.53/0.99    ( ! [X0,X1] : (k8_setfam_1(X0,X1) = X0 | k1_xboole_0 != X1 | ~m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0)))) )),
% 2.53/0.99    inference(cnf_transformation,[],[f20])).
% 2.53/0.99  
% 2.53/0.99  fof(f59,plain,(
% 2.53/0.99    ( ! [X0] : (k8_setfam_1(X0,k1_xboole_0) = X0 | ~m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_zfmisc_1(X0)))) )),
% 2.53/0.99    inference(equality_resolution,[],[f43])).
% 2.53/0.99  
% 2.53/0.99  fof(f9,axiom,(
% 2.53/0.99    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) => m1_subset_1(k8_setfam_1(X0,X1),k1_zfmisc_1(X0)))),
% 2.53/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.53/0.99  
% 2.53/0.99  fof(f21,plain,(
% 2.53/0.99    ! [X0,X1] : (m1_subset_1(k8_setfam_1(X0,X1),k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))))),
% 2.53/0.99    inference(ennf_transformation,[],[f9])).
% 2.53/0.99  
% 2.53/0.99  fof(f44,plain,(
% 2.53/0.99    ( ! [X0,X1] : (m1_subset_1(k8_setfam_1(X0,X1),k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0)))) )),
% 2.53/0.99    inference(cnf_transformation,[],[f21])).
% 2.53/0.99  
% 2.53/0.99  fof(f13,axiom,(
% 2.53/0.99    ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) <=> r1_tarski(X0,X1))),
% 2.53/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.53/0.99  
% 2.53/0.99  fof(f31,plain,(
% 2.53/0.99    ! [X0,X1] : ((m1_subset_1(X0,k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1)) & (r1_tarski(X0,X1) | ~m1_subset_1(X0,k1_zfmisc_1(X1))))),
% 2.53/0.99    inference(nnf_transformation,[],[f13])).
% 2.53/0.99  
% 2.53/0.99  fof(f48,plain,(
% 2.53/0.99    ( ! [X0,X1] : (r1_tarski(X0,X1) | ~m1_subset_1(X0,k1_zfmisc_1(X1))) )),
% 2.53/0.99    inference(cnf_transformation,[],[f31])).
% 2.53/0.99  
% 2.53/0.99  fof(f7,axiom,(
% 2.53/0.99    ! [X0] : (v1_xboole_0(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => v1_xboole_0(X1)))),
% 2.53/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.53/0.99  
% 2.53/0.99  fof(f19,plain,(
% 2.53/0.99    ! [X0] : (! [X1] : (v1_xboole_0(X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) | ~v1_xboole_0(X0))),
% 2.53/0.99    inference(ennf_transformation,[],[f7])).
% 2.53/0.99  
% 2.53/0.99  fof(f41,plain,(
% 2.53/0.99    ( ! [X0,X1] : (v1_xboole_0(X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0)) | ~v1_xboole_0(X0)) )),
% 2.53/0.99    inference(cnf_transformation,[],[f19])).
% 2.53/0.99  
% 2.53/0.99  fof(f49,plain,(
% 2.53/0.99    ( ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1)) )),
% 2.53/0.99    inference(cnf_transformation,[],[f31])).
% 2.53/0.99  
% 2.53/0.99  fof(f5,axiom,(
% 2.53/0.99    ! [X0,X1] : k1_xboole_0 != k2_xboole_0(k1_tarski(X0),X1)),
% 2.53/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.53/0.99  
% 2.53/0.99  fof(f39,plain,(
% 2.53/0.99    ( ! [X0,X1] : (k1_xboole_0 != k2_xboole_0(k1_tarski(X0),X1)) )),
% 2.53/0.99    inference(cnf_transformation,[],[f5])).
% 2.53/0.99  
% 2.53/0.99  fof(f58,plain,(
% 2.53/0.99    ( ! [X0,X1] : (k1_xboole_0 != k5_xboole_0(k1_tarski(X0),k5_xboole_0(X1,k1_setfam_1(k2_tarski(X1,k1_tarski(X0)))))) )),
% 2.53/0.99    inference(definition_unfolding,[],[f39,f56])).
% 2.53/0.99  
% 2.53/0.99  fof(f1,axiom,(
% 2.53/0.99    ! [X0] : (v1_xboole_0(X0) => k1_xboole_0 = X0)),
% 2.53/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.53/0.99  
% 2.53/0.99  fof(f17,plain,(
% 2.53/0.99    ! [X0] : (k1_xboole_0 = X0 | ~v1_xboole_0(X0))),
% 2.53/0.99    inference(ennf_transformation,[],[f1])).
% 2.53/0.99  
% 2.53/0.99  fof(f35,plain,(
% 2.53/0.99    ( ! [X0] : (k1_xboole_0 = X0 | ~v1_xboole_0(X0)) )),
% 2.53/0.99    inference(cnf_transformation,[],[f17])).
% 2.53/0.99  
% 2.53/0.99  cnf(c_3,plain,
% 2.53/0.99      ( m1_subset_1(sK0(X0),X0) ),
% 2.53/0.99      inference(cnf_transformation,[],[f40]) ).
% 2.53/0.99  
% 2.53/0.99  cnf(c_741,plain,
% 2.53/0.99      ( m1_subset_1(sK0(X0),X0) = iProver_top ),
% 2.53/0.99      inference(predicate_to_equality,[status(thm)],[c_3]) ).
% 2.53/0.99  
% 2.53/0.99  cnf(c_9,plain,
% 2.53/0.99      ( ~ m1_subset_1(X0,X1) | r2_hidden(X0,X1) | v1_xboole_0(X1) ),
% 2.53/0.99      inference(cnf_transformation,[],[f47]) ).
% 2.53/0.99  
% 2.53/0.99  cnf(c_1,plain,
% 2.53/0.99      ( ~ r2_hidden(X0,X1)
% 2.53/0.99      | k5_xboole_0(k1_tarski(X0),k5_xboole_0(X1,k1_setfam_1(k2_tarski(X1,k1_tarski(X0))))) = X1 ),
% 2.53/0.99      inference(cnf_transformation,[],[f57]) ).
% 2.53/0.99  
% 2.53/0.99  cnf(c_218,plain,
% 2.53/0.99      ( ~ m1_subset_1(X0,X1)
% 2.53/0.99      | v1_xboole_0(X1)
% 2.53/0.99      | k5_xboole_0(k1_tarski(X0),k5_xboole_0(X1,k1_setfam_1(k2_tarski(X1,k1_tarski(X0))))) = X1 ),
% 2.53/0.99      inference(resolution,[status(thm)],[c_9,c_1]) ).
% 2.53/0.99  
% 2.53/0.99  cnf(c_728,plain,
% 2.53/0.99      ( k5_xboole_0(k1_tarski(X0),k5_xboole_0(X1,k1_setfam_1(k2_tarski(X1,k1_tarski(X0))))) = X1
% 2.53/0.99      | m1_subset_1(X0,X1) != iProver_top
% 2.53/0.99      | v1_xboole_0(X1) = iProver_top ),
% 2.53/0.99      inference(predicate_to_equality,[status(thm)],[c_218]) ).
% 2.53/0.99  
% 2.53/0.99  cnf(c_1139,plain,
% 2.53/0.99      ( k5_xboole_0(k1_tarski(sK0(X0)),k5_xboole_0(X0,k1_setfam_1(k2_tarski(X0,k1_tarski(sK0(X0)))))) = X0
% 2.53/0.99      | v1_xboole_0(X0) = iProver_top ),
% 2.53/0.99      inference(superposition,[status(thm)],[c_741,c_728]) ).
% 2.53/0.99  
% 2.53/0.99  cnf(c_12,plain,
% 2.53/0.99      ( ~ r1_tarski(X0,X1)
% 2.53/0.99      | r1_tarski(k1_setfam_1(X1),k1_setfam_1(X0))
% 2.53/0.99      | k1_xboole_0 = X0 ),
% 2.53/0.99      inference(cnf_transformation,[],[f50]) ).
% 2.53/0.99  
% 2.53/0.99  cnf(c_734,plain,
% 2.53/0.99      ( k1_xboole_0 = X0
% 2.53/0.99      | r1_tarski(X0,X1) != iProver_top
% 2.53/0.99      | r1_tarski(k1_setfam_1(X1),k1_setfam_1(X0)) = iProver_top ),
% 2.53/0.99      inference(predicate_to_equality,[status(thm)],[c_12]) ).
% 2.53/0.99  
% 2.53/0.99  cnf(c_15,negated_conjecture,
% 2.53/0.99      ( m1_subset_1(sK3,k1_zfmisc_1(k1_zfmisc_1(sK1))) ),
% 2.53/0.99      inference(cnf_transformation,[],[f52]) ).
% 2.53/0.99  
% 2.53/0.99  cnf(c_731,plain,
% 2.53/0.99      ( m1_subset_1(sK3,k1_zfmisc_1(k1_zfmisc_1(sK1))) = iProver_top ),
% 2.53/0.99      inference(predicate_to_equality,[status(thm)],[c_15]) ).
% 2.53/0.99  
% 2.53/0.99  cnf(c_6,plain,
% 2.53/0.99      ( ~ m1_subset_1(X0,k1_zfmisc_1(k1_zfmisc_1(X1)))
% 2.53/0.99      | k6_setfam_1(X1,X0) = k8_setfam_1(X1,X0)
% 2.53/0.99      | k1_xboole_0 = X0 ),
% 2.53/0.99      inference(cnf_transformation,[],[f42]) ).
% 2.53/0.99  
% 2.53/0.99  cnf(c_739,plain,
% 2.53/0.99      ( k6_setfam_1(X0,X1) = k8_setfam_1(X0,X1)
% 2.53/0.99      | k1_xboole_0 = X1
% 2.53/0.99      | m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) != iProver_top ),
% 2.53/0.99      inference(predicate_to_equality,[status(thm)],[c_6]) ).
% 2.53/0.99  
% 2.53/0.99  cnf(c_1914,plain,
% 2.53/0.99      ( k6_setfam_1(sK1,sK3) = k8_setfam_1(sK1,sK3) | sK3 = k1_xboole_0 ),
% 2.53/0.99      inference(superposition,[status(thm)],[c_731,c_739]) ).
% 2.53/0.99  
% 2.53/0.99  cnf(c_8,plain,
% 2.53/0.99      ( ~ m1_subset_1(X0,k1_zfmisc_1(k1_zfmisc_1(X1)))
% 2.53/0.99      | k6_setfam_1(X1,X0) = k1_setfam_1(X0) ),
% 2.53/0.99      inference(cnf_transformation,[],[f45]) ).
% 2.53/0.99  
% 2.53/0.99  cnf(c_737,plain,
% 2.53/0.99      ( k6_setfam_1(X0,X1) = k1_setfam_1(X1)
% 2.53/0.99      | m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) != iProver_top ),
% 2.53/0.99      inference(predicate_to_equality,[status(thm)],[c_8]) ).
% 2.53/0.99  
% 2.53/0.99  cnf(c_1291,plain,
% 2.53/0.99      ( k6_setfam_1(sK1,sK3) = k1_setfam_1(sK3) ),
% 2.53/0.99      inference(superposition,[status(thm)],[c_731,c_737]) ).
% 2.53/0.99  
% 2.53/0.99  cnf(c_1923,plain,
% 2.53/0.99      ( k8_setfam_1(sK1,sK3) = k1_setfam_1(sK3) | sK3 = k1_xboole_0 ),
% 2.53/0.99      inference(light_normalisation,[status(thm)],[c_1914,c_1291]) ).
% 2.53/0.99  
% 2.53/0.99  cnf(c_16,negated_conjecture,
% 2.53/0.99      ( m1_subset_1(sK2,k1_zfmisc_1(k1_zfmisc_1(sK1))) ),
% 2.53/0.99      inference(cnf_transformation,[],[f51]) ).
% 2.53/0.99  
% 2.53/0.99  cnf(c_730,plain,
% 2.53/0.99      ( m1_subset_1(sK2,k1_zfmisc_1(k1_zfmisc_1(sK1))) = iProver_top ),
% 2.53/0.99      inference(predicate_to_equality,[status(thm)],[c_16]) ).
% 2.53/0.99  
% 2.53/0.99  cnf(c_1915,plain,
% 2.53/0.99      ( k6_setfam_1(sK1,sK2) = k8_setfam_1(sK1,sK2) | sK2 = k1_xboole_0 ),
% 2.53/0.99      inference(superposition,[status(thm)],[c_730,c_739]) ).
% 2.53/0.99  
% 2.53/0.99  cnf(c_1292,plain,
% 2.53/0.99      ( k6_setfam_1(sK1,sK2) = k1_setfam_1(sK2) ),
% 2.53/0.99      inference(superposition,[status(thm)],[c_730,c_737]) ).
% 2.53/0.99  
% 2.53/0.99  cnf(c_1918,plain,
% 2.53/0.99      ( k8_setfam_1(sK1,sK2) = k1_setfam_1(sK2) | sK2 = k1_xboole_0 ),
% 2.53/0.99      inference(light_normalisation,[status(thm)],[c_1915,c_1292]) ).
% 2.53/0.99  
% 2.53/0.99  cnf(c_13,negated_conjecture,
% 2.53/0.99      ( ~ r1_tarski(k8_setfam_1(sK1,sK3),k8_setfam_1(sK1,sK2)) ),
% 2.53/0.99      inference(cnf_transformation,[],[f54]) ).
% 2.53/0.99  
% 2.53/0.99  cnf(c_733,plain,
% 2.53/0.99      ( r1_tarski(k8_setfam_1(sK1,sK3),k8_setfam_1(sK1,sK2)) != iProver_top ),
% 2.53/0.99      inference(predicate_to_equality,[status(thm)],[c_13]) ).
% 2.53/0.99  
% 2.53/0.99  cnf(c_2164,plain,
% 2.53/0.99      ( sK2 = k1_xboole_0
% 2.53/0.99      | r1_tarski(k8_setfam_1(sK1,sK3),k1_setfam_1(sK2)) != iProver_top ),
% 2.53/0.99      inference(superposition,[status(thm)],[c_1918,c_733]) ).
% 2.53/0.99  
% 2.53/0.99  cnf(c_2256,plain,
% 2.53/0.99      ( sK2 = k1_xboole_0
% 2.53/0.99      | sK3 = k1_xboole_0
% 2.53/0.99      | r1_tarski(k1_setfam_1(sK3),k1_setfam_1(sK2)) != iProver_top ),
% 2.53/0.99      inference(superposition,[status(thm)],[c_1923,c_2164]) ).
% 2.53/0.99  
% 2.53/0.99  cnf(c_2357,plain,
% 2.53/0.99      ( sK2 = k1_xboole_0
% 2.53/0.99      | sK3 = k1_xboole_0
% 2.53/0.99      | r1_tarski(sK2,sK3) != iProver_top ),
% 2.53/0.99      inference(superposition,[status(thm)],[c_734,c_2256]) ).
% 2.53/0.99  
% 2.53/0.99  cnf(c_14,negated_conjecture,
% 2.53/0.99      ( r1_tarski(sK2,sK3) ),
% 2.53/0.99      inference(cnf_transformation,[],[f53]) ).
% 2.53/0.99  
% 2.53/0.99  cnf(c_19,plain,
% 2.53/0.99      ( r1_tarski(sK2,sK3) = iProver_top ),
% 2.53/0.99      inference(predicate_to_equality,[status(thm)],[c_14]) ).
% 2.53/0.99  
% 2.53/0.99  cnf(c_2516,plain,
% 2.53/0.99      ( sK3 = k1_xboole_0 | sK2 = k1_xboole_0 ),
% 2.53/0.99      inference(global_propositional_subsumption,
% 2.53/0.99                [status(thm)],
% 2.53/0.99                [c_2357,c_19]) ).
% 2.53/0.99  
% 2.53/0.99  cnf(c_2517,plain,
% 2.53/0.99      ( sK2 = k1_xboole_0 | sK3 = k1_xboole_0 ),
% 2.53/0.99      inference(renaming,[status(thm)],[c_2516]) ).
% 2.53/0.99  
% 2.53/0.99  cnf(c_2528,plain,
% 2.53/0.99      ( sK3 = k1_xboole_0
% 2.53/0.99      | m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_zfmisc_1(sK1))) = iProver_top ),
% 2.53/0.99      inference(superposition,[status(thm)],[c_2517,c_730]) ).
% 2.53/0.99  
% 2.53/0.99  cnf(c_5,plain,
% 2.53/0.99      ( ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_zfmisc_1(X0)))
% 2.53/0.99      | k8_setfam_1(X0,k1_xboole_0) = X0 ),
% 2.53/0.99      inference(cnf_transformation,[],[f59]) ).
% 2.53/0.99  
% 2.53/0.99  cnf(c_740,plain,
% 2.53/0.99      ( k8_setfam_1(X0,k1_xboole_0) = X0
% 2.53/0.99      | m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_zfmisc_1(X0))) != iProver_top ),
% 2.53/0.99      inference(predicate_to_equality,[status(thm)],[c_5]) ).
% 2.53/0.99  
% 2.53/0.99  cnf(c_2756,plain,
% 2.53/0.99      ( k8_setfam_1(sK1,k1_xboole_0) = sK1 | sK3 = k1_xboole_0 ),
% 2.53/0.99      inference(superposition,[status(thm)],[c_2528,c_740]) ).
% 2.53/0.99  
% 2.53/0.99  cnf(c_2527,plain,
% 2.53/0.99      ( sK3 = k1_xboole_0
% 2.53/0.99      | r1_tarski(k8_setfam_1(sK1,sK3),k8_setfam_1(sK1,k1_xboole_0)) != iProver_top ),
% 2.53/0.99      inference(superposition,[status(thm)],[c_2517,c_733]) ).
% 2.53/0.99  
% 2.53/0.99  cnf(c_2968,plain,
% 2.53/0.99      ( sK3 = k1_xboole_0
% 2.53/0.99      | r1_tarski(k8_setfam_1(sK1,sK3),sK1) != iProver_top ),
% 2.53/0.99      inference(superposition,[status(thm)],[c_2756,c_2527]) ).
% 2.53/0.99  
% 2.53/0.99  cnf(c_18,plain,
% 2.53/0.99      ( m1_subset_1(sK3,k1_zfmisc_1(k1_zfmisc_1(sK1))) = iProver_top ),
% 2.53/0.99      inference(predicate_to_equality,[status(thm)],[c_15]) ).
% 2.53/0.99  
% 2.53/0.99  cnf(c_7,plain,
% 2.53/0.99      ( ~ m1_subset_1(X0,k1_zfmisc_1(k1_zfmisc_1(X1)))
% 2.53/0.99      | m1_subset_1(k8_setfam_1(X1,X0),k1_zfmisc_1(X1)) ),
% 2.53/0.99      inference(cnf_transformation,[],[f44]) ).
% 2.53/0.99  
% 2.53/0.99  cnf(c_860,plain,
% 2.53/0.99      ( m1_subset_1(k8_setfam_1(sK1,sK3),k1_zfmisc_1(sK1))
% 2.53/0.99      | ~ m1_subset_1(sK3,k1_zfmisc_1(k1_zfmisc_1(sK1))) ),
% 2.53/0.99      inference(instantiation,[status(thm)],[c_7]) ).
% 2.53/0.99  
% 2.53/0.99  cnf(c_861,plain,
% 2.53/0.99      ( m1_subset_1(k8_setfam_1(sK1,sK3),k1_zfmisc_1(sK1)) = iProver_top
% 2.53/0.99      | m1_subset_1(sK3,k1_zfmisc_1(k1_zfmisc_1(sK1))) != iProver_top ),
% 2.53/0.99      inference(predicate_to_equality,[status(thm)],[c_860]) ).
% 2.53/0.99  
% 2.53/0.99  cnf(c_11,plain,
% 2.53/0.99      ( r1_tarski(X0,X1) | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ),
% 2.53/0.99      inference(cnf_transformation,[],[f48]) ).
% 2.53/0.99  
% 2.53/0.99  cnf(c_954,plain,
% 2.53/0.99      ( r1_tarski(k8_setfam_1(sK1,sK3),sK1)
% 2.53/0.99      | ~ m1_subset_1(k8_setfam_1(sK1,sK3),k1_zfmisc_1(sK1)) ),
% 2.53/0.99      inference(instantiation,[status(thm)],[c_11]) ).
% 2.53/0.99  
% 2.53/0.99  cnf(c_955,plain,
% 2.53/0.99      ( r1_tarski(k8_setfam_1(sK1,sK3),sK1) = iProver_top
% 2.53/0.99      | m1_subset_1(k8_setfam_1(sK1,sK3),k1_zfmisc_1(sK1)) != iProver_top ),
% 2.53/0.99      inference(predicate_to_equality,[status(thm)],[c_954]) ).
% 2.53/0.99  
% 2.53/0.99  cnf(c_3076,plain,
% 2.53/0.99      ( sK3 = k1_xboole_0 ),
% 2.53/0.99      inference(global_propositional_subsumption,
% 2.53/0.99                [status(thm)],
% 2.53/0.99                [c_2968,c_18,c_861,c_955]) ).
% 2.53/0.99  
% 2.53/0.99  cnf(c_732,plain,
% 2.53/0.99      ( r1_tarski(sK2,sK3) = iProver_top ),
% 2.53/0.99      inference(predicate_to_equality,[status(thm)],[c_14]) ).
% 2.53/0.99  
% 2.53/0.99  cnf(c_4,plain,
% 2.53/0.99      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
% 2.53/0.99      | ~ v1_xboole_0(X1)
% 2.53/0.99      | v1_xboole_0(X0) ),
% 2.53/0.99      inference(cnf_transformation,[],[f41]) ).
% 2.53/0.99  
% 2.53/0.99  cnf(c_10,plain,
% 2.53/0.99      ( ~ r1_tarski(X0,X1) | m1_subset_1(X0,k1_zfmisc_1(X1)) ),
% 2.53/0.99      inference(cnf_transformation,[],[f49]) ).
% 2.53/0.99  
% 2.53/0.99  cnf(c_129,plain,
% 2.53/0.99      ( ~ r1_tarski(X0,X1) | m1_subset_1(X0,k1_zfmisc_1(X1)) ),
% 2.53/0.99      inference(prop_impl,[status(thm)],[c_10]) ).
% 2.53/0.99  
% 2.53/0.99  cnf(c_157,plain,
% 2.53/0.99      ( ~ r1_tarski(X0,X1) | ~ v1_xboole_0(X1) | v1_xboole_0(X0) ),
% 2.53/0.99      inference(bin_hyper_res,[status(thm)],[c_4,c_129]) ).
% 2.53/0.99  
% 2.53/0.99  cnf(c_729,plain,
% 2.53/0.99      ( r1_tarski(X0,X1) != iProver_top
% 2.53/0.99      | v1_xboole_0(X1) != iProver_top
% 2.53/0.99      | v1_xboole_0(X0) = iProver_top ),
% 2.53/0.99      inference(predicate_to_equality,[status(thm)],[c_157]) ).
% 2.53/0.99  
% 2.53/0.99  cnf(c_1784,plain,
% 2.53/0.99      ( v1_xboole_0(sK2) = iProver_top
% 2.53/0.99      | v1_xboole_0(sK3) != iProver_top ),
% 2.53/0.99      inference(superposition,[status(thm)],[c_732,c_729]) ).
% 2.53/0.99  
% 2.53/0.99  cnf(c_3083,plain,
% 2.53/0.99      ( v1_xboole_0(sK2) = iProver_top
% 2.53/0.99      | v1_xboole_0(k1_xboole_0) != iProver_top ),
% 2.53/0.99      inference(demodulation,[status(thm)],[c_3076,c_1784]) ).
% 2.53/0.99  
% 2.53/0.99  cnf(c_4467,plain,
% 2.53/0.99      ( k5_xboole_0(k1_tarski(sK0(k1_xboole_0)),k5_xboole_0(k1_xboole_0,k1_setfam_1(k2_tarski(k1_xboole_0,k1_tarski(sK0(k1_xboole_0)))))) = k1_xboole_0
% 2.53/0.99      | v1_xboole_0(sK2) = iProver_top ),
% 2.53/0.99      inference(superposition,[status(thm)],[c_1139,c_3083]) ).
% 2.53/0.99  
% 2.53/0.99  cnf(c_2,plain,
% 2.53/0.99      ( k5_xboole_0(k1_tarski(X0),k5_xboole_0(X1,k1_setfam_1(k2_tarski(X1,k1_tarski(X0))))) != k1_xboole_0 ),
% 2.53/0.99      inference(cnf_transformation,[],[f58]) ).
% 2.53/0.99  
% 2.53/0.99  cnf(c_4889,plain,
% 2.53/0.99      ( v1_xboole_0(sK2) = iProver_top ),
% 2.53/0.99      inference(forward_subsumption_resolution,
% 2.53/0.99                [status(thm)],
% 2.53/0.99                [c_4467,c_2]) ).
% 2.53/0.99  
% 2.53/0.99  cnf(c_0,plain,
% 2.53/0.99      ( ~ v1_xboole_0(X0) | k1_xboole_0 = X0 ),
% 2.53/0.99      inference(cnf_transformation,[],[f35]) ).
% 2.53/0.99  
% 2.53/0.99  cnf(c_742,plain,
% 2.53/0.99      ( k1_xboole_0 = X0 | v1_xboole_0(X0) != iProver_top ),
% 2.53/0.99      inference(predicate_to_equality,[status(thm)],[c_0]) ).
% 2.53/0.99  
% 2.53/0.99  cnf(c_4892,plain,
% 2.53/0.99      ( sK2 = k1_xboole_0 ),
% 2.53/0.99      inference(superposition,[status(thm)],[c_4889,c_742]) ).
% 2.53/0.99  
% 2.53/0.99  cnf(c_3088,plain,
% 2.53/0.99      ( r1_tarski(k8_setfam_1(sK1,k1_xboole_0),k8_setfam_1(sK1,sK2)) != iProver_top ),
% 2.53/0.99      inference(demodulation,[status(thm)],[c_3076,c_733]) ).
% 2.53/0.99  
% 2.53/0.99  cnf(c_3089,plain,
% 2.53/0.99      ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_zfmisc_1(sK1))) = iProver_top ),
% 2.53/0.99      inference(demodulation,[status(thm)],[c_3076,c_731]) ).
% 2.53/0.99  
% 2.53/0.99  cnf(c_3290,plain,
% 2.53/0.99      ( k8_setfam_1(sK1,k1_xboole_0) = sK1 ),
% 2.53/0.99      inference(superposition,[status(thm)],[c_3089,c_740]) ).
% 2.53/0.99  
% 2.53/0.99  cnf(c_3648,plain,
% 2.53/0.99      ( r1_tarski(sK1,k8_setfam_1(sK1,sK2)) != iProver_top ),
% 2.53/0.99      inference(light_normalisation,[status(thm)],[c_3088,c_3290]) ).
% 2.53/0.99  
% 2.53/0.99  cnf(c_5159,plain,
% 2.53/0.99      ( r1_tarski(sK1,k8_setfam_1(sK1,k1_xboole_0)) != iProver_top ),
% 2.53/0.99      inference(demodulation,[status(thm)],[c_4892,c_3648]) ).
% 2.53/0.99  
% 2.53/0.99  cnf(c_5172,plain,
% 2.53/0.99      ( r1_tarski(sK1,sK1) != iProver_top ),
% 2.53/0.99      inference(light_normalisation,[status(thm)],[c_5159,c_3290]) ).
% 2.53/0.99  
% 2.53/0.99  cnf(c_738,plain,
% 2.53/0.99      ( m1_subset_1(X0,k1_zfmisc_1(k1_zfmisc_1(X1))) != iProver_top
% 2.53/0.99      | m1_subset_1(k8_setfam_1(X1,X0),k1_zfmisc_1(X1)) = iProver_top ),
% 2.53/0.99      inference(predicate_to_equality,[status(thm)],[c_7]) ).
% 2.53/0.99  
% 2.53/0.99  cnf(c_735,plain,
% 2.53/0.99      ( r1_tarski(X0,X1) = iProver_top
% 2.53/0.99      | m1_subset_1(X0,k1_zfmisc_1(X1)) != iProver_top ),
% 2.53/0.99      inference(predicate_to_equality,[status(thm)],[c_11]) ).
% 2.53/0.99  
% 2.53/0.99  cnf(c_1402,plain,
% 2.53/0.99      ( r1_tarski(k8_setfam_1(X0,X1),X0) = iProver_top
% 2.53/0.99      | m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) != iProver_top ),
% 2.53/0.99      inference(superposition,[status(thm)],[c_738,c_735]) ).
% 2.53/0.99  
% 2.53/0.99  cnf(c_3291,plain,
% 2.53/0.99      ( r1_tarski(k8_setfam_1(sK1,k1_xboole_0),sK1) = iProver_top ),
% 2.53/0.99      inference(superposition,[status(thm)],[c_3089,c_1402]) ).
% 2.53/0.99  
% 2.53/0.99  cnf(c_3298,plain,
% 2.53/0.99      ( r1_tarski(sK1,sK1) = iProver_top ),
% 2.53/0.99      inference(demodulation,[status(thm)],[c_3290,c_3291]) ).
% 2.53/0.99  
% 2.53/0.99  cnf(contradiction,plain,
% 2.53/0.99      ( $false ),
% 2.53/0.99      inference(minisat,[status(thm)],[c_5172,c_3298]) ).
% 2.53/0.99  
% 2.53/0.99  
% 2.53/0.99  % SZS output end CNFRefutation for theBenchmark.p
% 2.53/0.99  
% 2.53/0.99  ------                               Statistics
% 2.53/0.99  
% 2.53/0.99  ------ General
% 2.53/0.99  
% 2.53/0.99  abstr_ref_over_cycles:                  0
% 2.53/0.99  abstr_ref_under_cycles:                 0
% 2.53/0.99  gc_basic_clause_elim:                   0
% 2.53/0.99  forced_gc_time:                         0
% 2.53/0.99  parsing_time:                           0.009
% 2.53/0.99  unif_index_cands_time:                  0.
% 2.53/0.99  unif_index_add_time:                    0.
% 2.53/0.99  orderings_time:                         0.
% 2.53/0.99  out_proof_time:                         0.007
% 2.53/0.99  total_time:                             0.22
% 2.53/0.99  num_of_symbols:                         47
% 2.53/0.99  num_of_terms:                           3952
% 2.53/0.99  
% 2.53/0.99  ------ Preprocessing
% 2.53/0.99  
% 2.53/0.99  num_of_splits:                          0
% 2.53/0.99  num_of_split_atoms:                     0
% 2.53/0.99  num_of_reused_defs:                     0
% 2.53/0.99  num_eq_ax_congr_red:                    20
% 2.53/0.99  num_of_sem_filtered_clauses:            1
% 2.53/0.99  num_of_subtypes:                        0
% 2.53/0.99  monotx_restored_types:                  0
% 2.53/0.99  sat_num_of_epr_types:                   0
% 2.53/0.99  sat_num_of_non_cyclic_types:            0
% 2.53/0.99  sat_guarded_non_collapsed_types:        0
% 2.53/0.99  num_pure_diseq_elim:                    0
% 2.53/0.99  simp_replaced_by:                       0
% 2.53/0.99  res_preprocessed:                       84
% 2.53/0.99  prep_upred:                             0
% 2.53/0.99  prep_unflattend:                        0
% 2.53/0.99  smt_new_axioms:                         0
% 2.53/0.99  pred_elim_cands:                        3
% 2.53/0.99  pred_elim:                              1
% 2.53/0.99  pred_elim_cl:                           1
% 2.53/0.99  pred_elim_cycles:                       3
% 2.53/0.99  merged_defs:                            8
% 2.53/0.99  merged_defs_ncl:                        0
% 2.53/0.99  bin_hyper_res:                          9
% 2.53/0.99  prep_cycles:                            4
% 2.53/0.99  pred_elim_time:                         0.
% 2.53/0.99  splitting_time:                         0.
% 2.53/0.99  sem_filter_time:                        0.
% 2.53/0.99  monotx_time:                            0.001
% 2.53/0.99  subtype_inf_time:                       0.
% 2.53/0.99  
% 2.53/0.99  ------ Problem properties
% 2.53/0.99  
% 2.53/0.99  clauses:                                16
% 2.53/0.99  conjectures:                            4
% 2.53/0.99  epr:                                    3
% 2.53/0.99  horn:                                   13
% 2.53/0.99  ground:                                 4
% 2.53/0.99  unary:                                  6
% 2.53/0.99  binary:                                 6
% 2.53/0.99  lits:                                   30
% 2.53/0.99  lits_eq:                                8
% 2.53/0.99  fd_pure:                                0
% 2.53/0.99  fd_pseudo:                              0
% 2.53/0.99  fd_cond:                                3
% 2.53/0.99  fd_pseudo_cond:                         0
% 2.53/0.99  ac_symbols:                             0
% 2.53/0.99  
% 2.53/0.99  ------ Propositional Solver
% 2.53/0.99  
% 2.53/0.99  prop_solver_calls:                      26
% 2.53/0.99  prop_fast_solver_calls:                 508
% 2.53/0.99  smt_solver_calls:                       0
% 2.53/0.99  smt_fast_solver_calls:                  0
% 2.53/0.99  prop_num_of_clauses:                    2087
% 2.53/0.99  prop_preprocess_simplified:             5037
% 2.53/0.99  prop_fo_subsumed:                       8
% 2.53/0.99  prop_solver_time:                       0.
% 2.53/0.99  smt_solver_time:                        0.
% 2.53/0.99  smt_fast_solver_time:                   0.
% 2.53/0.99  prop_fast_solver_time:                  0.
% 2.53/0.99  prop_unsat_core_time:                   0.
% 2.53/0.99  
% 2.53/0.99  ------ QBF
% 2.53/0.99  
% 2.53/0.99  qbf_q_res:                              0
% 2.53/0.99  qbf_num_tautologies:                    0
% 2.53/0.99  qbf_prep_cycles:                        0
% 2.53/0.99  
% 2.53/0.99  ------ BMC1
% 2.53/0.99  
% 2.53/0.99  bmc1_current_bound:                     -1
% 2.53/0.99  bmc1_last_solved_bound:                 -1
% 2.53/0.99  bmc1_unsat_core_size:                   -1
% 2.53/0.99  bmc1_unsat_core_parents_size:           -1
% 2.53/0.99  bmc1_merge_next_fun:                    0
% 2.53/0.99  bmc1_unsat_core_clauses_time:           0.
% 2.53/0.99  
% 2.53/0.99  ------ Instantiation
% 2.53/0.99  
% 2.53/0.99  inst_num_of_clauses:                    670
% 2.53/0.99  inst_num_in_passive:                    151
% 2.53/0.99  inst_num_in_active:                     283
% 2.53/0.99  inst_num_in_unprocessed:                236
% 2.53/0.99  inst_num_of_loops:                      380
% 2.53/0.99  inst_num_of_learning_restarts:          0
% 2.53/0.99  inst_num_moves_active_passive:          94
% 2.53/0.99  inst_lit_activity:                      0
% 2.53/0.99  inst_lit_activity_moves:                0
% 2.53/0.99  inst_num_tautologies:                   0
% 2.53/0.99  inst_num_prop_implied:                  0
% 2.53/0.99  inst_num_existing_simplified:           0
% 2.53/0.99  inst_num_eq_res_simplified:             0
% 2.53/0.99  inst_num_child_elim:                    0
% 2.53/0.99  inst_num_of_dismatching_blockings:      286
% 2.53/0.99  inst_num_of_non_proper_insts:           526
% 2.53/0.99  inst_num_of_duplicates:                 0
% 2.53/0.99  inst_inst_num_from_inst_to_res:         0
% 2.53/0.99  inst_dismatching_checking_time:         0.
% 2.53/0.99  
% 2.53/0.99  ------ Resolution
% 2.53/0.99  
% 2.53/0.99  res_num_of_clauses:                     0
% 2.53/0.99  res_num_in_passive:                     0
% 2.53/0.99  res_num_in_active:                      0
% 2.53/0.99  res_num_of_loops:                       88
% 2.53/0.99  res_forward_subset_subsumed:            25
% 2.53/0.99  res_backward_subset_subsumed:           0
% 2.53/0.99  res_forward_subsumed:                   0
% 2.53/0.99  res_backward_subsumed:                  0
% 2.53/0.99  res_forward_subsumption_resolution:     0
% 2.53/0.99  res_backward_subsumption_resolution:    0
% 2.53/0.99  res_clause_to_clause_subsumption:       202
% 2.53/0.99  res_orphan_elimination:                 0
% 2.53/0.99  res_tautology_del:                      77
% 2.53/0.99  res_num_eq_res_simplified:              0
% 2.53/0.99  res_num_sel_changes:                    0
% 2.53/0.99  res_moves_from_active_to_pass:          0
% 2.53/0.99  
% 2.53/0.99  ------ Superposition
% 2.53/0.99  
% 2.53/0.99  sup_time_total:                         0.
% 2.53/0.99  sup_time_generating:                    0.
% 2.53/0.99  sup_time_sim_full:                      0.
% 2.53/0.99  sup_time_sim_immed:                     0.
% 2.53/0.99  
% 2.53/0.99  sup_num_of_clauses:                     74
% 2.53/0.99  sup_num_in_active:                      35
% 2.53/0.99  sup_num_in_passive:                     39
% 2.53/0.99  sup_num_of_loops:                       75
% 2.53/0.99  sup_fw_superposition:                   73
% 2.53/0.99  sup_bw_superposition:                   77
% 2.53/0.99  sup_immediate_simplified:               22
% 2.53/0.99  sup_given_eliminated:                   1
% 2.53/0.99  comparisons_done:                       0
% 2.53/0.99  comparisons_avoided:                    13
% 2.53/0.99  
% 2.53/0.99  ------ Simplifications
% 2.53/0.99  
% 2.53/0.99  
% 2.53/0.99  sim_fw_subset_subsumed:                 15
% 2.53/0.99  sim_bw_subset_subsumed:                 21
% 2.53/0.99  sim_fw_subsumed:                        0
% 2.53/0.99  sim_bw_subsumed:                        0
% 2.53/0.99  sim_fw_subsumption_res:                 1
% 2.53/0.99  sim_bw_subsumption_res:                 0
% 2.53/0.99  sim_tautology_del:                      7
% 2.53/0.99  sim_eq_tautology_del:                   6
% 2.53/0.99  sim_eq_res_simp:                        0
% 2.53/0.99  sim_fw_demodulated:                     1
% 2.53/0.99  sim_bw_demodulated:                     29
% 2.53/0.99  sim_light_normalised:                   8
% 2.53/0.99  sim_joinable_taut:                      0
% 2.53/0.99  sim_joinable_simp:                      0
% 2.53/0.99  sim_ac_normalised:                      0
% 2.53/0.99  sim_smt_subsumption:                    0
% 2.53/0.99  
%------------------------------------------------------------------------------
