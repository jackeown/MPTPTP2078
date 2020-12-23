%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n020.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 11:39:15 EST 2020

% Result     : Theorem 3.43s
% Output     : CNFRefutation 3.43s
% Verified   : 
% Statistics : Number of formulae       :  140 (1001 expanded)
%              Number of clauses        :   76 ( 302 expanded)
%              Number of leaves         :   21 ( 257 expanded)
%              Depth                    :   21
%              Number of atoms          :  248 (1949 expanded)
%              Number of equality atoms :  139 ( 958 expanded)
%              Maximal formula depth    :    9 (   3 average)
%              Maximal clause size      :   10 (   1 average)
%              Maximal term depth       :    6 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f22,conjecture,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => k2_subset_1(X0) = k4_subset_1(X0,X1,k3_subset_1(X0,X1)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f23,negated_conjecture,(
    ~ ! [X0,X1] :
        ( m1_subset_1(X1,k1_zfmisc_1(X0))
       => k2_subset_1(X0) = k4_subset_1(X0,X1,k3_subset_1(X0,X1)) ) ),
    inference(negated_conjecture,[],[f22])).

fof(f30,plain,(
    ? [X0,X1] :
      ( k2_subset_1(X0) != k4_subset_1(X0,X1,k3_subset_1(X0,X1))
      & m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f23])).

fof(f38,plain,
    ( ? [X0,X1] :
        ( k2_subset_1(X0) != k4_subset_1(X0,X1,k3_subset_1(X0,X1))
        & m1_subset_1(X1,k1_zfmisc_1(X0)) )
   => ( k2_subset_1(sK1) != k4_subset_1(sK1,sK2,k3_subset_1(sK1,sK2))
      & m1_subset_1(sK2,k1_zfmisc_1(sK1)) ) ),
    introduced(choice_axiom,[])).

fof(f39,plain,
    ( k2_subset_1(sK1) != k4_subset_1(sK1,sK2,k3_subset_1(sK1,sK2))
    & m1_subset_1(sK2,k1_zfmisc_1(sK1)) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1,sK2])],[f30,f38])).

fof(f69,plain,(
    m1_subset_1(sK2,k1_zfmisc_1(sK1)) ),
    inference(cnf_transformation,[],[f39])).

fof(f18,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => k4_xboole_0(X0,X1) = k3_subset_1(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f26,plain,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,X1) = k3_subset_1(X0,X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f18])).

fof(f65,plain,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,X1) = k3_subset_1(X0,X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f19,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => m1_subset_1(k3_subset_1(X0,X1),k1_zfmisc_1(X0)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f27,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k3_subset_1(X0,X1),k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f19])).

fof(f66,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k3_subset_1(X0,X1),k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f21,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(X0))
        & m1_subset_1(X1,k1_zfmisc_1(X0)) )
     => k2_xboole_0(X1,X2) = k4_subset_1(X0,X1,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f28,plain,(
    ! [X0,X1,X2] :
      ( k2_xboole_0(X1,X2) = k4_subset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f21])).

fof(f29,plain,(
    ! [X0,X1,X2] :
      ( k2_xboole_0(X1,X2) = k4_subset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(flattening,[],[f28])).

fof(f68,plain,(
    ! [X2,X0,X1] :
      ( k2_xboole_0(X1,X2) = k4_subset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f11,axiom,(
    ! [X0,X1] : k5_xboole_0(k5_xboole_0(X0,X1),k3_xboole_0(X0,X1)) = k2_xboole_0(X0,X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f52,plain,(
    ! [X0,X1] : k5_xboole_0(k5_xboole_0(X0,X1),k3_xboole_0(X0,X1)) = k2_xboole_0(X0,X1) ),
    inference(cnf_transformation,[],[f11])).

fof(f9,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f50,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f9])).

fof(f71,plain,(
    ! [X0,X1] : k5_xboole_0(k5_xboole_0(X0,X1),k4_xboole_0(X0,k4_xboole_0(X0,X1))) = k2_xboole_0(X0,X1) ),
    inference(definition_unfolding,[],[f52,f50])).

fof(f80,plain,(
    ! [X2,X0,X1] :
      ( k5_xboole_0(k5_xboole_0(X1,X2),k4_xboole_0(X1,k4_xboole_0(X1,X2))) = k4_subset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(definition_unfolding,[],[f68,f71])).

fof(f15,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f59,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1)) ),
    inference(cnf_transformation,[],[f15])).

fof(f13,axiom,(
    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f54,plain,(
    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f13])).

fof(f79,plain,(
    ! [X0,X1] : k5_xboole_0(k5_xboole_0(X0,X1),k4_xboole_0(X0,k4_xboole_0(X0,X1))) = k3_tarski(k1_enumset1(X0,X0,X1)) ),
    inference(definition_unfolding,[],[f59,f71,f54])).

fof(f16,axiom,(
    ! [X0,X1] :
      ( ( v1_xboole_0(X0)
       => ( m1_subset_1(X1,X0)
        <=> v1_xboole_0(X1) ) )
      & ( ~ v1_xboole_0(X0)
       => ( m1_subset_1(X1,X0)
        <=> r2_hidden(X1,X0) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f25,plain,(
    ! [X0,X1] :
      ( ( ( m1_subset_1(X1,X0)
        <=> v1_xboole_0(X1) )
        | ~ v1_xboole_0(X0) )
      & ( ( m1_subset_1(X1,X0)
        <=> r2_hidden(X1,X0) )
        | v1_xboole_0(X0) ) ) ),
    inference(ennf_transformation,[],[f16])).

fof(f37,plain,(
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
    inference(nnf_transformation,[],[f25])).

fof(f60,plain,(
    ! [X0,X1] :
      ( r2_hidden(X1,X0)
      | ~ m1_subset_1(X1,X0)
      | v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f37])).

fof(f20,axiom,(
    ! [X0] : ~ v1_xboole_0(k1_zfmisc_1(X0)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f67,plain,(
    ! [X0] : ~ v1_xboole_0(k1_zfmisc_1(X0)) ),
    inference(cnf_transformation,[],[f20])).

fof(f14,axiom,(
    ! [X0,X1] :
      ( k1_zfmisc_1(X0) = X1
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
        <=> r1_tarski(X2,X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f33,plain,(
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
    inference(nnf_transformation,[],[f14])).

fof(f34,plain,(
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
    inference(rectify,[],[f33])).

fof(f35,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ( ~ r1_tarski(X2,X0)
            | ~ r2_hidden(X2,X1) )
          & ( r1_tarski(X2,X0)
            | r2_hidden(X2,X1) ) )
     => ( ( ~ r1_tarski(sK0(X0,X1),X0)
          | ~ r2_hidden(sK0(X0,X1),X1) )
        & ( r1_tarski(sK0(X0,X1),X0)
          | r2_hidden(sK0(X0,X1),X1) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f36,plain,(
    ! [X0,X1] :
      ( ( k1_zfmisc_1(X0) = X1
        | ( ( ~ r1_tarski(sK0(X0,X1),X0)
            | ~ r2_hidden(sK0(X0,X1),X1) )
          & ( r1_tarski(sK0(X0,X1),X0)
            | r2_hidden(sK0(X0,X1),X1) ) ) )
      & ( ! [X3] :
            ( ( r2_hidden(X3,X1)
              | ~ r1_tarski(X3,X0) )
            & ( r1_tarski(X3,X0)
              | ~ r2_hidden(X3,X1) ) )
        | k1_zfmisc_1(X0) != X1 ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f34,f35])).

fof(f55,plain,(
    ! [X0,X3,X1] :
      ( r1_tarski(X3,X0)
      | ~ r2_hidden(X3,X1)
      | k1_zfmisc_1(X0) != X1 ) ),
    inference(cnf_transformation,[],[f36])).

fof(f84,plain,(
    ! [X0,X3] :
      ( r1_tarski(X3,X0)
      | ~ r2_hidden(X3,k1_zfmisc_1(X0)) ) ),
    inference(equality_resolution,[],[f55])).

fof(f6,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
     => k3_xboole_0(X0,X1) = X0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f24,plain,(
    ! [X0,X1] :
      ( k3_xboole_0(X0,X1) = X0
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f47,plain,(
    ! [X0,X1] :
      ( k3_xboole_0(X0,X1) = X0
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f76,plain,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,k4_xboole_0(X0,X1)) = X0
      | ~ r1_tarski(X0,X1) ) ),
    inference(definition_unfolding,[],[f47,f50])).

fof(f1,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f40,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f1])).

fof(f73,plain,(
    ! [X0,X1] : k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k4_xboole_0(X1,k4_xboole_0(X1,X0)) ),
    inference(definition_unfolding,[],[f40,f50,f50])).

fof(f3,axiom,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f44,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f3])).

fof(f72,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X0,X1))) ),
    inference(definition_unfolding,[],[f44,f50])).

fof(f5,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,k3_xboole_0(X0,X1)) = X0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f46,plain,(
    ! [X0,X1] : k2_xboole_0(X0,k3_xboole_0(X0,X1)) = X0 ),
    inference(cnf_transformation,[],[f5])).

fof(f75,plain,(
    ! [X0,X1] : k5_xboole_0(k5_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X0,X1))),k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X0,X1))))) = X0 ),
    inference(definition_unfolding,[],[f46,f71,f50])).

fof(f4,axiom,(
    ! [X0,X1,X2] : k3_xboole_0(k5_xboole_0(X0,X2),X1) = k5_xboole_0(k3_xboole_0(X0,X1),k3_xboole_0(X2,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f45,plain,(
    ! [X2,X0,X1] : k3_xboole_0(k5_xboole_0(X0,X2),X1) = k5_xboole_0(k3_xboole_0(X0,X1),k3_xboole_0(X2,X1)) ),
    inference(cnf_transformation,[],[f4])).

fof(f74,plain,(
    ! [X2,X0,X1] : k4_xboole_0(k5_xboole_0(X0,X2),k4_xboole_0(k5_xboole_0(X0,X2),X1)) = k5_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),k4_xboole_0(X2,k4_xboole_0(X2,X1))) ),
    inference(definition_unfolding,[],[f45,f50,f50,f50])).

fof(f10,axiom,(
    ! [X0] : k5_xboole_0(X0,k1_xboole_0) = X0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f51,plain,(
    ! [X0] : k5_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(cnf_transformation,[],[f10])).

fof(f8,axiom,(
    ! [X0,X1] : k4_xboole_0(X0,k2_xboole_0(X0,X1)) = k1_xboole_0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f49,plain,(
    ! [X0,X1] : k4_xboole_0(X0,k2_xboole_0(X0,X1)) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f8])).

fof(f77,plain,(
    ! [X0,X1] : k4_xboole_0(X0,k5_xboole_0(k5_xboole_0(X0,X1),k4_xboole_0(X0,k4_xboole_0(X0,X1)))) = k1_xboole_0 ),
    inference(definition_unfolding,[],[f49,f71])).

fof(f70,plain,(
    k2_subset_1(sK1) != k4_subset_1(sK1,sK2,k3_subset_1(sK1,sK2)) ),
    inference(cnf_transformation,[],[f39])).

fof(f17,axiom,(
    ! [X0] : k2_subset_1(X0) = X0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f64,plain,(
    ! [X0] : k2_subset_1(X0) = X0 ),
    inference(cnf_transformation,[],[f17])).

cnf(c_27,negated_conjecture,
    ( m1_subset_1(sK2,k1_zfmisc_1(sK1)) ),
    inference(cnf_transformation,[],[f69])).

cnf(c_1097,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(sK1)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_27])).

cnf(c_22,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | k3_subset_1(X1,X0) = k4_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f65])).

cnf(c_1101,plain,
    ( k3_subset_1(X0,X1) = k4_xboole_0(X0,X1)
    | m1_subset_1(X1,k1_zfmisc_1(X0)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_22])).

cnf(c_3249,plain,
    ( k3_subset_1(sK1,sK2) = k4_xboole_0(sK1,sK2) ),
    inference(superposition,[status(thm)],[c_1097,c_1101])).

cnf(c_23,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | m1_subset_1(k3_subset_1(X1,X0),k1_zfmisc_1(X1)) ),
    inference(cnf_transformation,[],[f66])).

cnf(c_1100,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(X1)) != iProver_top
    | m1_subset_1(k3_subset_1(X1,X0),k1_zfmisc_1(X1)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_23])).

cnf(c_3310,plain,
    ( m1_subset_1(k4_xboole_0(sK1,sK2),k1_zfmisc_1(sK1)) = iProver_top
    | m1_subset_1(sK2,k1_zfmisc_1(sK1)) != iProver_top ),
    inference(superposition,[status(thm)],[c_3249,c_1100])).

cnf(c_28,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(sK1)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_27])).

cnf(c_3464,plain,
    ( m1_subset_1(k4_xboole_0(sK1,sK2),k1_zfmisc_1(sK1)) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_3310,c_28])).

cnf(c_25,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | ~ m1_subset_1(X2,k1_zfmisc_1(X1))
    | k5_xboole_0(k5_xboole_0(X0,X2),k4_xboole_0(X0,k4_xboole_0(X0,X2))) = k4_subset_1(X1,X0,X2) ),
    inference(cnf_transformation,[],[f80])).

cnf(c_1098,plain,
    ( k5_xboole_0(k5_xboole_0(X0,X1),k4_xboole_0(X0,k4_xboole_0(X0,X1))) = k4_subset_1(X2,X0,X1)
    | m1_subset_1(X0,k1_zfmisc_1(X2)) != iProver_top
    | m1_subset_1(X1,k1_zfmisc_1(X2)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_25])).

cnf(c_16,plain,
    ( k5_xboole_0(k5_xboole_0(X0,X1),k4_xboole_0(X0,k4_xboole_0(X0,X1))) = k3_tarski(k1_enumset1(X0,X0,X1)) ),
    inference(cnf_transformation,[],[f79])).

cnf(c_1117,plain,
    ( k3_tarski(k1_enumset1(X0,X0,X1)) = k4_subset_1(X2,X0,X1)
    | m1_subset_1(X0,k1_zfmisc_1(X2)) != iProver_top
    | m1_subset_1(X1,k1_zfmisc_1(X2)) != iProver_top ),
    inference(demodulation,[status(thm)],[c_1098,c_16])).

cnf(c_8270,plain,
    ( k3_tarski(k1_enumset1(sK2,sK2,X0)) = k4_subset_1(sK1,sK2,X0)
    | m1_subset_1(X0,k1_zfmisc_1(sK1)) != iProver_top ),
    inference(superposition,[status(thm)],[c_1097,c_1117])).

cnf(c_8858,plain,
    ( k3_tarski(k1_enumset1(sK2,sK2,k4_xboole_0(sK1,sK2))) = k4_subset_1(sK1,sK2,k4_xboole_0(sK1,sK2)) ),
    inference(superposition,[status(thm)],[c_3464,c_8270])).

cnf(c_20,plain,
    ( ~ m1_subset_1(X0,X1)
    | r2_hidden(X0,X1)
    | v1_xboole_0(X1) ),
    inference(cnf_transformation,[],[f60])).

cnf(c_1102,plain,
    ( m1_subset_1(X0,X1) != iProver_top
    | r2_hidden(X0,X1) = iProver_top
    | v1_xboole_0(X1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_20])).

cnf(c_2094,plain,
    ( r2_hidden(sK2,k1_zfmisc_1(sK1)) = iProver_top
    | v1_xboole_0(k1_zfmisc_1(sK1)) = iProver_top ),
    inference(superposition,[status(thm)],[c_1097,c_1102])).

cnf(c_24,plain,
    ( ~ v1_xboole_0(k1_zfmisc_1(X0)) ),
    inference(cnf_transformation,[],[f67])).

cnf(c_32,plain,
    ( v1_xboole_0(k1_zfmisc_1(X0)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_24])).

cnf(c_34,plain,
    ( v1_xboole_0(k1_zfmisc_1(sK1)) != iProver_top ),
    inference(instantiation,[status(thm)],[c_32])).

cnf(c_2490,plain,
    ( r2_hidden(sK2,k1_zfmisc_1(sK1)) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_2094,c_34])).

cnf(c_15,plain,
    ( ~ r2_hidden(X0,k1_zfmisc_1(X1))
    | r1_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f84])).

cnf(c_1106,plain,
    ( r2_hidden(X0,k1_zfmisc_1(X1)) != iProver_top
    | r1_tarski(X0,X1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_15])).

cnf(c_2800,plain,
    ( r1_tarski(sK2,sK1) = iProver_top ),
    inference(superposition,[status(thm)],[c_2490,c_1106])).

cnf(c_7,plain,
    ( ~ r1_tarski(X0,X1)
    | k4_xboole_0(X0,k4_xboole_0(X0,X1)) = X0 ),
    inference(cnf_transformation,[],[f76])).

cnf(c_1111,plain,
    ( k4_xboole_0(X0,k4_xboole_0(X0,X1)) = X0
    | r1_tarski(X0,X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_7])).

cnf(c_3245,plain,
    ( k4_xboole_0(sK2,k4_xboole_0(sK2,sK1)) = sK2 ),
    inference(superposition,[status(thm)],[c_2800,c_1111])).

cnf(c_1,plain,
    ( k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k4_xboole_0(X1,k4_xboole_0(X1,X0)) ),
    inference(cnf_transformation,[],[f73])).

cnf(c_3489,plain,
    ( k4_xboole_0(sK1,k4_xboole_0(sK1,sK2)) = sK2 ),
    inference(superposition,[status(thm)],[c_3245,c_1])).

cnf(c_3771,plain,
    ( k5_xboole_0(k5_xboole_0(sK1,k4_xboole_0(sK1,sK2)),k4_xboole_0(sK1,sK2)) = k3_tarski(k1_enumset1(sK1,sK1,k4_xboole_0(sK1,sK2))) ),
    inference(superposition,[status(thm)],[c_3489,c_16])).

cnf(c_0,plain,
    ( k5_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X0,X1))) = k4_xboole_0(X0,X1) ),
    inference(cnf_transformation,[],[f72])).

cnf(c_3772,plain,
    ( k5_xboole_0(sK1,k4_xboole_0(sK1,sK2)) = k4_xboole_0(sK1,k4_xboole_0(sK1,sK2)) ),
    inference(superposition,[status(thm)],[c_3489,c_0])).

cnf(c_3791,plain,
    ( k5_xboole_0(sK1,k4_xboole_0(sK1,sK2)) = sK2 ),
    inference(demodulation,[status(thm)],[c_3772,c_3489])).

cnf(c_3792,plain,
    ( k3_tarski(k1_enumset1(sK1,sK1,k4_xboole_0(sK1,sK2))) = k5_xboole_0(sK2,k4_xboole_0(sK1,sK2)) ),
    inference(demodulation,[status(thm)],[c_3771,c_3791])).

cnf(c_1602,plain,
    ( k5_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X0,X1))))) = k3_tarski(k1_enumset1(X0,X0,k4_xboole_0(X0,k4_xboole_0(X0,X1)))) ),
    inference(superposition,[status(thm)],[c_0,c_16])).

cnf(c_6,plain,
    ( k5_xboole_0(k5_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X0,X1))),k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X0,X1))))) = X0 ),
    inference(cnf_transformation,[],[f75])).

cnf(c_1116,plain,
    ( k5_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X0,X1))))) = X0 ),
    inference(light_normalisation,[status(thm)],[c_6,c_0])).

cnf(c_1612,plain,
    ( k3_tarski(k1_enumset1(X0,X0,k4_xboole_0(X0,k4_xboole_0(X0,X1)))) = X0 ),
    inference(light_normalisation,[status(thm)],[c_1602,c_1116])).

cnf(c_2652,plain,
    ( k3_tarski(k1_enumset1(X0,X0,k4_xboole_0(X0,k4_xboole_0(X1,k4_xboole_0(X1,X0))))) = X0 ),
    inference(superposition,[status(thm)],[c_1,c_1612])).

cnf(c_3486,plain,
    ( k3_tarski(k1_enumset1(sK1,sK1,k4_xboole_0(sK1,sK2))) = sK1 ),
    inference(superposition,[status(thm)],[c_3245,c_2652])).

cnf(c_3793,plain,
    ( k5_xboole_0(sK2,k4_xboole_0(sK1,sK2)) = sK1 ),
    inference(light_normalisation,[status(thm)],[c_3792,c_3486])).

cnf(c_5217,plain,
    ( k5_xboole_0(sK1,k4_xboole_0(sK2,k4_xboole_0(sK2,k4_xboole_0(sK1,sK2)))) = k3_tarski(k1_enumset1(sK2,sK2,k4_xboole_0(sK1,sK2))) ),
    inference(superposition,[status(thm)],[c_3793,c_16])).

cnf(c_1489,plain,
    ( k5_xboole_0(X0,k4_xboole_0(X1,k4_xboole_0(X1,X0))) = k4_xboole_0(X0,X1) ),
    inference(superposition,[status(thm)],[c_1,c_0])).

cnf(c_3488,plain,
    ( k5_xboole_0(sK1,sK2) = k4_xboole_0(sK1,sK2) ),
    inference(superposition,[status(thm)],[c_3245,c_1489])).

cnf(c_3689,plain,
    ( k5_xboole_0(k4_xboole_0(sK1,sK2),k4_xboole_0(sK1,k4_xboole_0(sK1,sK2))) = k3_tarski(k1_enumset1(sK1,sK1,sK2)) ),
    inference(superposition,[status(thm)],[c_3488,c_16])).

cnf(c_2649,plain,
    ( k3_tarski(k1_enumset1(X0,X0,k4_xboole_0(X1,k4_xboole_0(X1,X0)))) = X0 ),
    inference(superposition,[status(thm)],[c_1,c_1612])).

cnf(c_3487,plain,
    ( k3_tarski(k1_enumset1(sK1,sK1,sK2)) = sK1 ),
    inference(superposition,[status(thm)],[c_3245,c_2649])).

cnf(c_3690,plain,
    ( k5_xboole_0(k4_xboole_0(sK1,sK2),sK2) = sK1 ),
    inference(light_normalisation,[status(thm)],[c_3689,c_3487,c_3489])).

cnf(c_1605,plain,
    ( k5_xboole_0(k5_xboole_0(X0,X1),k4_xboole_0(X1,k4_xboole_0(X1,X0))) = k3_tarski(k1_enumset1(X0,X0,X1)) ),
    inference(superposition,[status(thm)],[c_1,c_16])).

cnf(c_4909,plain,
    ( k3_tarski(k1_enumset1(k4_xboole_0(sK1,sK2),k4_xboole_0(sK1,sK2),sK2)) = k5_xboole_0(sK1,k4_xboole_0(sK2,k4_xboole_0(sK2,k4_xboole_0(sK1,sK2)))) ),
    inference(superposition,[status(thm)],[c_3690,c_1605])).

cnf(c_4733,plain,
    ( k5_xboole_0(sK1,k4_xboole_0(k4_xboole_0(sK1,sK2),k4_xboole_0(k4_xboole_0(sK1,sK2),sK2))) = k3_tarski(k1_enumset1(k4_xboole_0(sK1,sK2),k4_xboole_0(sK1,sK2),sK2)) ),
    inference(superposition,[status(thm)],[c_3690,c_16])).

cnf(c_5,plain,
    ( k5_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),k4_xboole_0(X2,k4_xboole_0(X2,X1))) = k4_xboole_0(k5_xboole_0(X0,X2),k4_xboole_0(k5_xboole_0(X0,X2),X1)) ),
    inference(cnf_transformation,[],[f74])).

cnf(c_1714,plain,
    ( k4_xboole_0(k5_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X0,X1))),k4_xboole_0(k5_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X0,X1))),X1)) = k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),X1) ),
    inference(superposition,[status(thm)],[c_5,c_0])).

cnf(c_1716,plain,
    ( k4_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(k4_xboole_0(X0,X1),X1)) = k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),X1) ),
    inference(light_normalisation,[status(thm)],[c_1714,c_0])).

cnf(c_4734,plain,
    ( k3_tarski(k1_enumset1(k4_xboole_0(sK1,sK2),k4_xboole_0(sK1,sK2),sK2)) = k5_xboole_0(sK1,k4_xboole_0(k4_xboole_0(sK1,k4_xboole_0(sK1,sK2)),sK2)) ),
    inference(demodulation,[status(thm)],[c_4733,c_1716])).

cnf(c_4735,plain,
    ( k3_tarski(k1_enumset1(k4_xboole_0(sK1,sK2),k4_xboole_0(sK1,sK2),sK2)) = k5_xboole_0(sK1,k4_xboole_0(sK2,sK2)) ),
    inference(light_normalisation,[status(thm)],[c_4734,c_3489])).

cnf(c_10,plain,
    ( k5_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(cnf_transformation,[],[f51])).

cnf(c_1604,plain,
    ( k5_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X0,k1_xboole_0))) = k3_tarski(k1_enumset1(X0,X0,k1_xboole_0)) ),
    inference(superposition,[status(thm)],[c_10,c_16])).

cnf(c_1611,plain,
    ( k3_tarski(k1_enumset1(X0,X0,k1_xboole_0)) = k4_xboole_0(X0,k1_xboole_0) ),
    inference(demodulation,[status(thm)],[c_1604,c_0])).

cnf(c_9,plain,
    ( k4_xboole_0(X0,k5_xboole_0(k5_xboole_0(X0,X1),k4_xboole_0(X0,k4_xboole_0(X0,X1)))) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f77])).

cnf(c_1597,plain,
    ( k4_xboole_0(X0,k3_tarski(k1_enumset1(X0,X0,X1))) = k1_xboole_0 ),
    inference(light_normalisation,[status(thm)],[c_9,c_9,c_16])).

cnf(c_1793,plain,
    ( k4_xboole_0(X0,k4_xboole_0(X0,k1_xboole_0)) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_1611,c_1597])).

cnf(c_1803,plain,
    ( k5_xboole_0(X0,k1_xboole_0) = k4_xboole_0(X0,k1_xboole_0) ),
    inference(superposition,[status(thm)],[c_1793,c_0])).

cnf(c_1808,plain,
    ( k4_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(light_normalisation,[status(thm)],[c_1803,c_10])).

cnf(c_1809,plain,
    ( k4_xboole_0(X0,X0) = k1_xboole_0 ),
    inference(demodulation,[status(thm)],[c_1808,c_1793])).

cnf(c_4736,plain,
    ( k3_tarski(k1_enumset1(k4_xboole_0(sK1,sK2),k4_xboole_0(sK1,sK2),sK2)) = sK1 ),
    inference(demodulation,[status(thm)],[c_4735,c_10,c_1809])).

cnf(c_4934,plain,
    ( k5_xboole_0(sK1,k4_xboole_0(sK2,k4_xboole_0(sK2,k4_xboole_0(sK1,sK2)))) = sK1 ),
    inference(light_normalisation,[status(thm)],[c_4909,c_4736])).

cnf(c_5219,plain,
    ( k3_tarski(k1_enumset1(sK2,sK2,k4_xboole_0(sK1,sK2))) = sK1 ),
    inference(light_normalisation,[status(thm)],[c_5217,c_4934])).

cnf(c_8859,plain,
    ( k4_subset_1(sK1,sK2,k4_xboole_0(sK1,sK2)) = sK1 ),
    inference(light_normalisation,[status(thm)],[c_8858,c_5219])).

cnf(c_26,negated_conjecture,
    ( k2_subset_1(sK1) != k4_subset_1(sK1,sK2,k3_subset_1(sK1,sK2)) ),
    inference(cnf_transformation,[],[f70])).

cnf(c_21,plain,
    ( k2_subset_1(X0) = X0 ),
    inference(cnf_transformation,[],[f64])).

cnf(c_1114,plain,
    ( k4_subset_1(sK1,sK2,k3_subset_1(sK1,sK2)) != sK1 ),
    inference(demodulation,[status(thm)],[c_26,c_21])).

cnf(c_3309,plain,
    ( k4_subset_1(sK1,sK2,k4_xboole_0(sK1,sK2)) != sK1 ),
    inference(demodulation,[status(thm)],[c_3249,c_1114])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_8859,c_3309])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : iproveropt_run.sh %d %s
% 0.13/0.34  % Computer   : n020.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 19:52:07 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running in FOF mode
% 3.43/1.00  % SZS status Started for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.43/1.00  
% 3.43/1.00  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 3.43/1.00  
% 3.43/1.00  ------  iProver source info
% 3.43/1.00  
% 3.43/1.00  git: date: 2020-06-30 10:37:57 +0100
% 3.43/1.00  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 3.43/1.00  git: non_committed_changes: false
% 3.43/1.00  git: last_make_outside_of_git: false
% 3.43/1.00  
% 3.43/1.00  ------ 
% 3.43/1.00  
% 3.43/1.00  ------ Input Options
% 3.43/1.00  
% 3.43/1.00  --out_options                           all
% 3.43/1.00  --tptp_safe_out                         true
% 3.43/1.00  --problem_path                          ""
% 3.43/1.00  --include_path                          ""
% 3.43/1.00  --clausifier                            res/vclausify_rel
% 3.43/1.00  --clausifier_options                    ""
% 3.43/1.00  --stdin                                 false
% 3.43/1.00  --stats_out                             all
% 3.43/1.00  
% 3.43/1.00  ------ General Options
% 3.43/1.00  
% 3.43/1.00  --fof                                   false
% 3.43/1.00  --time_out_real                         305.
% 3.43/1.00  --time_out_virtual                      -1.
% 3.43/1.00  --symbol_type_check                     false
% 3.43/1.00  --clausify_out                          false
% 3.43/1.00  --sig_cnt_out                           false
% 3.43/1.00  --trig_cnt_out                          false
% 3.43/1.00  --trig_cnt_out_tolerance                1.
% 3.43/1.00  --trig_cnt_out_sk_spl                   false
% 3.43/1.00  --abstr_cl_out                          false
% 3.43/1.00  
% 3.43/1.00  ------ Global Options
% 3.43/1.00  
% 3.43/1.00  --schedule                              default
% 3.43/1.00  --add_important_lit                     false
% 3.43/1.00  --prop_solver_per_cl                    1000
% 3.43/1.00  --min_unsat_core                        false
% 3.43/1.00  --soft_assumptions                      false
% 3.43/1.00  --soft_lemma_size                       3
% 3.43/1.00  --prop_impl_unit_size                   0
% 3.43/1.00  --prop_impl_unit                        []
% 3.43/1.00  --share_sel_clauses                     true
% 3.43/1.00  --reset_solvers                         false
% 3.43/1.00  --bc_imp_inh                            [conj_cone]
% 3.43/1.00  --conj_cone_tolerance                   3.
% 3.43/1.00  --extra_neg_conj                        none
% 3.43/1.00  --large_theory_mode                     true
% 3.43/1.00  --prolific_symb_bound                   200
% 3.43/1.00  --lt_threshold                          2000
% 3.43/1.00  --clause_weak_htbl                      true
% 3.43/1.00  --gc_record_bc_elim                     false
% 3.43/1.00  
% 3.43/1.00  ------ Preprocessing Options
% 3.43/1.00  
% 3.43/1.00  --preprocessing_flag                    true
% 3.43/1.00  --time_out_prep_mult                    0.1
% 3.43/1.00  --splitting_mode                        input
% 3.43/1.00  --splitting_grd                         true
% 3.43/1.00  --splitting_cvd                         false
% 3.43/1.00  --splitting_cvd_svl                     false
% 3.43/1.00  --splitting_nvd                         32
% 3.43/1.00  --sub_typing                            true
% 3.43/1.00  --prep_gs_sim                           true
% 3.43/1.00  --prep_unflatten                        true
% 3.43/1.00  --prep_res_sim                          true
% 3.43/1.00  --prep_upred                            true
% 3.43/1.00  --prep_sem_filter                       exhaustive
% 3.43/1.00  --prep_sem_filter_out                   false
% 3.43/1.00  --pred_elim                             true
% 3.43/1.00  --res_sim_input                         true
% 3.43/1.00  --eq_ax_congr_red                       true
% 3.43/1.00  --pure_diseq_elim                       true
% 3.43/1.00  --brand_transform                       false
% 3.43/1.00  --non_eq_to_eq                          false
% 3.43/1.00  --prep_def_merge                        true
% 3.43/1.00  --prep_def_merge_prop_impl              false
% 3.43/1.00  --prep_def_merge_mbd                    true
% 3.43/1.00  --prep_def_merge_tr_red                 false
% 3.43/1.00  --prep_def_merge_tr_cl                  false
% 3.43/1.00  --smt_preprocessing                     true
% 3.43/1.00  --smt_ac_axioms                         fast
% 3.43/1.00  --preprocessed_out                      false
% 3.43/1.00  --preprocessed_stats                    false
% 3.43/1.00  
% 3.43/1.00  ------ Abstraction refinement Options
% 3.43/1.00  
% 3.43/1.00  --abstr_ref                             []
% 3.43/1.00  --abstr_ref_prep                        false
% 3.43/1.00  --abstr_ref_until_sat                   false
% 3.43/1.00  --abstr_ref_sig_restrict                funpre
% 3.43/1.00  --abstr_ref_af_restrict_to_split_sk     false
% 3.43/1.00  --abstr_ref_under                       []
% 3.43/1.00  
% 3.43/1.00  ------ SAT Options
% 3.43/1.00  
% 3.43/1.00  --sat_mode                              false
% 3.43/1.00  --sat_fm_restart_options                ""
% 3.43/1.00  --sat_gr_def                            false
% 3.43/1.00  --sat_epr_types                         true
% 3.43/1.00  --sat_non_cyclic_types                  false
% 3.43/1.00  --sat_finite_models                     false
% 3.43/1.00  --sat_fm_lemmas                         false
% 3.43/1.00  --sat_fm_prep                           false
% 3.43/1.00  --sat_fm_uc_incr                        true
% 3.43/1.00  --sat_out_model                         small
% 3.43/1.00  --sat_out_clauses                       false
% 3.43/1.00  
% 3.43/1.00  ------ QBF Options
% 3.43/1.00  
% 3.43/1.00  --qbf_mode                              false
% 3.43/1.00  --qbf_elim_univ                         false
% 3.43/1.00  --qbf_dom_inst                          none
% 3.43/1.00  --qbf_dom_pre_inst                      false
% 3.43/1.00  --qbf_sk_in                             false
% 3.43/1.00  --qbf_pred_elim                         true
% 3.43/1.00  --qbf_split                             512
% 3.43/1.00  
% 3.43/1.00  ------ BMC1 Options
% 3.43/1.00  
% 3.43/1.00  --bmc1_incremental                      false
% 3.43/1.00  --bmc1_axioms                           reachable_all
% 3.43/1.00  --bmc1_min_bound                        0
% 3.43/1.00  --bmc1_max_bound                        -1
% 3.43/1.00  --bmc1_max_bound_default                -1
% 3.43/1.00  --bmc1_symbol_reachability              true
% 3.43/1.00  --bmc1_property_lemmas                  false
% 3.43/1.00  --bmc1_k_induction                      false
% 3.43/1.00  --bmc1_non_equiv_states                 false
% 3.43/1.00  --bmc1_deadlock                         false
% 3.43/1.00  --bmc1_ucm                              false
% 3.43/1.00  --bmc1_add_unsat_core                   none
% 3.43/1.00  --bmc1_unsat_core_children              false
% 3.43/1.00  --bmc1_unsat_core_extrapolate_axioms    false
% 3.43/1.00  --bmc1_out_stat                         full
% 3.43/1.00  --bmc1_ground_init                      false
% 3.43/1.00  --bmc1_pre_inst_next_state              false
% 3.43/1.00  --bmc1_pre_inst_state                   false
% 3.43/1.00  --bmc1_pre_inst_reach_state             false
% 3.43/1.00  --bmc1_out_unsat_core                   false
% 3.43/1.00  --bmc1_aig_witness_out                  false
% 3.43/1.00  --bmc1_verbose                          false
% 3.43/1.00  --bmc1_dump_clauses_tptp                false
% 3.43/1.00  --bmc1_dump_unsat_core_tptp             false
% 3.43/1.00  --bmc1_dump_file                        -
% 3.43/1.00  --bmc1_ucm_expand_uc_limit              128
% 3.43/1.00  --bmc1_ucm_n_expand_iterations          6
% 3.43/1.00  --bmc1_ucm_extend_mode                  1
% 3.43/1.00  --bmc1_ucm_init_mode                    2
% 3.43/1.00  --bmc1_ucm_cone_mode                    none
% 3.43/1.00  --bmc1_ucm_reduced_relation_type        0
% 3.43/1.00  --bmc1_ucm_relax_model                  4
% 3.43/1.00  --bmc1_ucm_full_tr_after_sat            true
% 3.43/1.00  --bmc1_ucm_expand_neg_assumptions       false
% 3.43/1.00  --bmc1_ucm_layered_model                none
% 3.43/1.00  --bmc1_ucm_max_lemma_size               10
% 3.43/1.00  
% 3.43/1.00  ------ AIG Options
% 3.43/1.00  
% 3.43/1.00  --aig_mode                              false
% 3.43/1.00  
% 3.43/1.00  ------ Instantiation Options
% 3.43/1.00  
% 3.43/1.00  --instantiation_flag                    true
% 3.43/1.00  --inst_sos_flag                         true
% 3.43/1.00  --inst_sos_phase                        true
% 3.43/1.00  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 3.43/1.00  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 3.43/1.00  --inst_lit_sel_side                     num_symb
% 3.43/1.00  --inst_solver_per_active                1400
% 3.43/1.00  --inst_solver_calls_frac                1.
% 3.43/1.00  --inst_passive_queue_type               priority_queues
% 3.43/1.00  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 3.43/1.00  --inst_passive_queues_freq              [25;2]
% 3.43/1.00  --inst_dismatching                      true
% 3.43/1.00  --inst_eager_unprocessed_to_passive     true
% 3.43/1.00  --inst_prop_sim_given                   true
% 3.43/1.00  --inst_prop_sim_new                     false
% 3.43/1.00  --inst_subs_new                         false
% 3.43/1.00  --inst_eq_res_simp                      false
% 3.43/1.00  --inst_subs_given                       false
% 3.43/1.00  --inst_orphan_elimination               true
% 3.43/1.00  --inst_learning_loop_flag               true
% 3.43/1.00  --inst_learning_start                   3000
% 3.43/1.00  --inst_learning_factor                  2
% 3.43/1.00  --inst_start_prop_sim_after_learn       3
% 3.43/1.00  --inst_sel_renew                        solver
% 3.43/1.00  --inst_lit_activity_flag                true
% 3.43/1.00  --inst_restr_to_given                   false
% 3.43/1.00  --inst_activity_threshold               500
% 3.43/1.00  --inst_out_proof                        true
% 3.43/1.00  
% 3.43/1.00  ------ Resolution Options
% 3.43/1.00  
% 3.43/1.00  --resolution_flag                       true
% 3.43/1.00  --res_lit_sel                           adaptive
% 3.43/1.00  --res_lit_sel_side                      none
% 3.43/1.00  --res_ordering                          kbo
% 3.43/1.00  --res_to_prop_solver                    active
% 3.43/1.00  --res_prop_simpl_new                    false
% 3.43/1.00  --res_prop_simpl_given                  true
% 3.43/1.00  --res_passive_queue_type                priority_queues
% 3.43/1.00  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 3.43/1.00  --res_passive_queues_freq               [15;5]
% 3.43/1.00  --res_forward_subs                      full
% 3.43/1.00  --res_backward_subs                     full
% 3.43/1.00  --res_forward_subs_resolution           true
% 3.43/1.00  --res_backward_subs_resolution          true
% 3.43/1.00  --res_orphan_elimination                true
% 3.43/1.00  --res_time_limit                        2.
% 3.43/1.00  --res_out_proof                         true
% 3.43/1.00  
% 3.43/1.00  ------ Superposition Options
% 3.43/1.00  
% 3.43/1.00  --superposition_flag                    true
% 3.43/1.00  --sup_passive_queue_type                priority_queues
% 3.43/1.00  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 3.43/1.00  --sup_passive_queues_freq               [8;1;4]
% 3.43/1.00  --demod_completeness_check              fast
% 3.43/1.00  --demod_use_ground                      true
% 3.43/1.00  --sup_to_prop_solver                    passive
% 3.43/1.00  --sup_prop_simpl_new                    true
% 3.43/1.00  --sup_prop_simpl_given                  true
% 3.43/1.00  --sup_fun_splitting                     true
% 3.43/1.00  --sup_smt_interval                      50000
% 3.43/1.00  
% 3.43/1.00  ------ Superposition Simplification Setup
% 3.43/1.00  
% 3.43/1.00  --sup_indices_passive                   [LightNormIndex;FwDemodIndex]
% 3.43/1.00  --sup_indices_active                    [SubsumptionIndex;BwDemodIndex]
% 3.43/1.00  --sup_indices_immed                     [SubsumptionIndex;FwDemodIndex;BwDemodIndex]
% 3.43/1.00  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex]
% 3.43/1.00  --sup_full_triv                         [TrivRules;PropSubs]
% 3.43/1.00  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;Joinability]
% 3.43/1.00  --sup_full_bw                           [BwDemod;BwSubsumption]
% 3.43/1.00  --sup_immed_triv                        [TrivRules]
% 3.43/1.00  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 3.43/1.00  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption]
% 3.43/1.00  --sup_immed_bw_main                     []
% 3.43/1.00  --sup_immed_bw_immed                    [BwDemod;BwSubsumption]
% 3.43/1.00  --sup_input_triv                        [Unflattening;TrivRules]
% 3.43/1.00  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption]
% 3.43/1.00  --sup_input_bw                          []
% 3.43/1.00  
% 3.43/1.00  ------ Combination Options
% 3.43/1.00  
% 3.43/1.00  --comb_res_mult                         3
% 3.43/1.00  --comb_sup_mult                         2
% 3.43/1.00  --comb_inst_mult                        10
% 3.43/1.00  
% 3.43/1.00  ------ Debug Options
% 3.43/1.00  
% 3.43/1.00  --dbg_backtrace                         false
% 3.43/1.00  --dbg_dump_prop_clauses                 false
% 3.43/1.00  --dbg_dump_prop_clauses_file            -
% 3.43/1.00  --dbg_out_stat                          false
% 3.43/1.00  ------ Parsing...
% 3.43/1.00  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 3.43/1.00  
% 3.43/1.00  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe_e  sf_s  rm: 1 0s  sf_e  pe_s  pe_e 
% 3.43/1.00  
% 3.43/1.00  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 3.43/1.00  
% 3.43/1.00  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 3.43/1.00  ------ Proving...
% 3.43/1.00  ------ Problem Properties 
% 3.43/1.00  
% 3.43/1.00  
% 3.43/1.00  clauses                                 27
% 3.43/1.00  conjectures                             2
% 3.43/1.00  EPR                                     7
% 3.43/1.00  Horn                                    24
% 3.43/1.00  unary                                   14
% 3.43/1.00  binary                                  5
% 3.43/1.00  lits                                    48
% 3.43/1.00  lits eq                                 16
% 3.43/1.00  fd_pure                                 0
% 3.43/1.00  fd_pseudo                               0
% 3.43/1.00  fd_cond                                 0
% 3.43/1.00  fd_pseudo_cond                          3
% 3.43/1.00  AC symbols                              0
% 3.43/1.00  
% 3.43/1.00  ------ Schedule dynamic 5 is on 
% 3.43/1.00  
% 3.43/1.00  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" Time Limit: 10.
% 3.43/1.00  
% 3.43/1.00  
% 3.43/1.00  ------ 
% 3.43/1.00  Current options:
% 3.43/1.00  ------ 
% 3.43/1.00  
% 3.43/1.00  ------ Input Options
% 3.43/1.00  
% 3.43/1.00  --out_options                           all
% 3.43/1.00  --tptp_safe_out                         true
% 3.43/1.00  --problem_path                          ""
% 3.43/1.00  --include_path                          ""
% 3.43/1.00  --clausifier                            res/vclausify_rel
% 3.43/1.00  --clausifier_options                    ""
% 3.43/1.00  --stdin                                 false
% 3.43/1.00  --stats_out                             all
% 3.43/1.00  
% 3.43/1.00  ------ General Options
% 3.43/1.00  
% 3.43/1.00  --fof                                   false
% 3.43/1.00  --time_out_real                         305.
% 3.43/1.00  --time_out_virtual                      -1.
% 3.43/1.00  --symbol_type_check                     false
% 3.43/1.00  --clausify_out                          false
% 3.43/1.00  --sig_cnt_out                           false
% 3.43/1.00  --trig_cnt_out                          false
% 3.43/1.00  --trig_cnt_out_tolerance                1.
% 3.43/1.00  --trig_cnt_out_sk_spl                   false
% 3.43/1.00  --abstr_cl_out                          false
% 3.43/1.00  
% 3.43/1.00  ------ Global Options
% 3.43/1.00  
% 3.43/1.00  --schedule                              default
% 3.43/1.00  --add_important_lit                     false
% 3.43/1.00  --prop_solver_per_cl                    1000
% 3.43/1.00  --min_unsat_core                        false
% 3.43/1.00  --soft_assumptions                      false
% 3.43/1.00  --soft_lemma_size                       3
% 3.43/1.00  --prop_impl_unit_size                   0
% 3.43/1.00  --prop_impl_unit                        []
% 3.43/1.00  --share_sel_clauses                     true
% 3.43/1.00  --reset_solvers                         false
% 3.43/1.00  --bc_imp_inh                            [conj_cone]
% 3.43/1.00  --conj_cone_tolerance                   3.
% 3.43/1.00  --extra_neg_conj                        none
% 3.43/1.00  --large_theory_mode                     true
% 3.43/1.00  --prolific_symb_bound                   200
% 3.43/1.00  --lt_threshold                          2000
% 3.43/1.00  --clause_weak_htbl                      true
% 3.43/1.00  --gc_record_bc_elim                     false
% 3.43/1.00  
% 3.43/1.00  ------ Preprocessing Options
% 3.43/1.00  
% 3.43/1.00  --preprocessing_flag                    true
% 3.43/1.00  --time_out_prep_mult                    0.1
% 3.43/1.00  --splitting_mode                        input
% 3.43/1.00  --splitting_grd                         true
% 3.43/1.00  --splitting_cvd                         false
% 3.43/1.00  --splitting_cvd_svl                     false
% 3.43/1.00  --splitting_nvd                         32
% 3.43/1.00  --sub_typing                            true
% 3.43/1.00  --prep_gs_sim                           true
% 3.43/1.00  --prep_unflatten                        true
% 3.43/1.00  --prep_res_sim                          true
% 3.43/1.00  --prep_upred                            true
% 3.43/1.00  --prep_sem_filter                       exhaustive
% 3.43/1.00  --prep_sem_filter_out                   false
% 3.43/1.00  --pred_elim                             true
% 3.43/1.00  --res_sim_input                         true
% 3.43/1.00  --eq_ax_congr_red                       true
% 3.43/1.00  --pure_diseq_elim                       true
% 3.43/1.00  --brand_transform                       false
% 3.43/1.00  --non_eq_to_eq                          false
% 3.43/1.00  --prep_def_merge                        true
% 3.43/1.00  --prep_def_merge_prop_impl              false
% 3.43/1.00  --prep_def_merge_mbd                    true
% 3.43/1.00  --prep_def_merge_tr_red                 false
% 3.43/1.00  --prep_def_merge_tr_cl                  false
% 3.43/1.00  --smt_preprocessing                     true
% 3.43/1.00  --smt_ac_axioms                         fast
% 3.43/1.00  --preprocessed_out                      false
% 3.43/1.00  --preprocessed_stats                    false
% 3.43/1.00  
% 3.43/1.00  ------ Abstraction refinement Options
% 3.43/1.00  
% 3.43/1.00  --abstr_ref                             []
% 3.43/1.00  --abstr_ref_prep                        false
% 3.43/1.00  --abstr_ref_until_sat                   false
% 3.43/1.00  --abstr_ref_sig_restrict                funpre
% 3.43/1.00  --abstr_ref_af_restrict_to_split_sk     false
% 3.43/1.00  --abstr_ref_under                       []
% 3.43/1.00  
% 3.43/1.00  ------ SAT Options
% 3.43/1.00  
% 3.43/1.00  --sat_mode                              false
% 3.43/1.00  --sat_fm_restart_options                ""
% 3.43/1.00  --sat_gr_def                            false
% 3.43/1.00  --sat_epr_types                         true
% 3.43/1.00  --sat_non_cyclic_types                  false
% 3.43/1.00  --sat_finite_models                     false
% 3.43/1.00  --sat_fm_lemmas                         false
% 3.43/1.00  --sat_fm_prep                           false
% 3.43/1.00  --sat_fm_uc_incr                        true
% 3.43/1.00  --sat_out_model                         small
% 3.43/1.00  --sat_out_clauses                       false
% 3.43/1.00  
% 3.43/1.00  ------ QBF Options
% 3.43/1.00  
% 3.43/1.00  --qbf_mode                              false
% 3.43/1.00  --qbf_elim_univ                         false
% 3.43/1.00  --qbf_dom_inst                          none
% 3.43/1.00  --qbf_dom_pre_inst                      false
% 3.43/1.00  --qbf_sk_in                             false
% 3.43/1.00  --qbf_pred_elim                         true
% 3.43/1.00  --qbf_split                             512
% 3.43/1.00  
% 3.43/1.00  ------ BMC1 Options
% 3.43/1.00  
% 3.43/1.00  --bmc1_incremental                      false
% 3.43/1.00  --bmc1_axioms                           reachable_all
% 3.43/1.00  --bmc1_min_bound                        0
% 3.43/1.00  --bmc1_max_bound                        -1
% 3.43/1.00  --bmc1_max_bound_default                -1
% 3.43/1.00  --bmc1_symbol_reachability              true
% 3.43/1.00  --bmc1_property_lemmas                  false
% 3.43/1.00  --bmc1_k_induction                      false
% 3.43/1.00  --bmc1_non_equiv_states                 false
% 3.43/1.00  --bmc1_deadlock                         false
% 3.43/1.00  --bmc1_ucm                              false
% 3.43/1.00  --bmc1_add_unsat_core                   none
% 3.43/1.00  --bmc1_unsat_core_children              false
% 3.43/1.00  --bmc1_unsat_core_extrapolate_axioms    false
% 3.43/1.00  --bmc1_out_stat                         full
% 3.43/1.00  --bmc1_ground_init                      false
% 3.43/1.00  --bmc1_pre_inst_next_state              false
% 3.43/1.00  --bmc1_pre_inst_state                   false
% 3.43/1.00  --bmc1_pre_inst_reach_state             false
% 3.43/1.00  --bmc1_out_unsat_core                   false
% 3.43/1.00  --bmc1_aig_witness_out                  false
% 3.43/1.00  --bmc1_verbose                          false
% 3.43/1.00  --bmc1_dump_clauses_tptp                false
% 3.43/1.00  --bmc1_dump_unsat_core_tptp             false
% 3.43/1.00  --bmc1_dump_file                        -
% 3.43/1.00  --bmc1_ucm_expand_uc_limit              128
% 3.43/1.00  --bmc1_ucm_n_expand_iterations          6
% 3.43/1.00  --bmc1_ucm_extend_mode                  1
% 3.43/1.00  --bmc1_ucm_init_mode                    2
% 3.43/1.00  --bmc1_ucm_cone_mode                    none
% 3.43/1.00  --bmc1_ucm_reduced_relation_type        0
% 3.43/1.00  --bmc1_ucm_relax_model                  4
% 3.43/1.00  --bmc1_ucm_full_tr_after_sat            true
% 3.43/1.00  --bmc1_ucm_expand_neg_assumptions       false
% 3.43/1.00  --bmc1_ucm_layered_model                none
% 3.43/1.00  --bmc1_ucm_max_lemma_size               10
% 3.43/1.00  
% 3.43/1.00  ------ AIG Options
% 3.43/1.00  
% 3.43/1.00  --aig_mode                              false
% 3.43/1.00  
% 3.43/1.00  ------ Instantiation Options
% 3.43/1.00  
% 3.43/1.00  --instantiation_flag                    true
% 3.43/1.00  --inst_sos_flag                         true
% 3.43/1.00  --inst_sos_phase                        true
% 3.43/1.00  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 3.43/1.00  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 3.43/1.00  --inst_lit_sel_side                     none
% 3.43/1.00  --inst_solver_per_active                1400
% 3.43/1.00  --inst_solver_calls_frac                1.
% 3.43/1.00  --inst_passive_queue_type               priority_queues
% 3.43/1.00  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 3.43/1.00  --inst_passive_queues_freq              [25;2]
% 3.43/1.00  --inst_dismatching                      true
% 3.43/1.00  --inst_eager_unprocessed_to_passive     true
% 3.43/1.00  --inst_prop_sim_given                   true
% 3.43/1.00  --inst_prop_sim_new                     false
% 3.43/1.00  --inst_subs_new                         false
% 3.43/1.00  --inst_eq_res_simp                      false
% 3.43/1.00  --inst_subs_given                       false
% 3.43/1.00  --inst_orphan_elimination               true
% 3.43/1.00  --inst_learning_loop_flag               true
% 3.43/1.00  --inst_learning_start                   3000
% 3.43/1.00  --inst_learning_factor                  2
% 3.43/1.00  --inst_start_prop_sim_after_learn       3
% 3.43/1.00  --inst_sel_renew                        solver
% 3.43/1.00  --inst_lit_activity_flag                true
% 3.43/1.00  --inst_restr_to_given                   false
% 3.43/1.00  --inst_activity_threshold               500
% 3.43/1.00  --inst_out_proof                        true
% 3.43/1.00  
% 3.43/1.00  ------ Resolution Options
% 3.43/1.00  
% 3.43/1.00  --resolution_flag                       false
% 3.43/1.00  --res_lit_sel                           adaptive
% 3.43/1.00  --res_lit_sel_side                      none
% 3.43/1.00  --res_ordering                          kbo
% 3.43/1.00  --res_to_prop_solver                    active
% 3.43/1.00  --res_prop_simpl_new                    false
% 3.43/1.00  --res_prop_simpl_given                  true
% 3.43/1.00  --res_passive_queue_type                priority_queues
% 3.43/1.00  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 3.43/1.00  --res_passive_queues_freq               [15;5]
% 3.43/1.00  --res_forward_subs                      full
% 3.43/1.00  --res_backward_subs                     full
% 3.43/1.00  --res_forward_subs_resolution           true
% 3.43/1.00  --res_backward_subs_resolution          true
% 3.43/1.00  --res_orphan_elimination                true
% 3.43/1.00  --res_time_limit                        2.
% 3.43/1.00  --res_out_proof                         true
% 3.43/1.00  
% 3.43/1.00  ------ Superposition Options
% 3.43/1.00  
% 3.43/1.00  --superposition_flag                    true
% 3.43/1.00  --sup_passive_queue_type                priority_queues
% 3.43/1.00  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 3.43/1.00  --sup_passive_queues_freq               [8;1;4]
% 3.43/1.00  --demod_completeness_check              fast
% 3.43/1.00  --demod_use_ground                      true
% 3.43/1.00  --sup_to_prop_solver                    passive
% 3.43/1.00  --sup_prop_simpl_new                    true
% 3.43/1.00  --sup_prop_simpl_given                  true
% 3.43/1.00  --sup_fun_splitting                     true
% 3.43/1.00  --sup_smt_interval                      50000
% 3.43/1.00  
% 3.43/1.00  ------ Superposition Simplification Setup
% 3.43/1.00  
% 3.43/1.00  --sup_indices_passive                   [LightNormIndex;FwDemodIndex]
% 3.43/1.00  --sup_indices_active                    [SubsumptionIndex;BwDemodIndex]
% 3.43/1.00  --sup_indices_immed                     [SubsumptionIndex;FwDemodIndex;BwDemodIndex]
% 3.43/1.00  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex]
% 3.43/1.00  --sup_full_triv                         [TrivRules;PropSubs]
% 3.43/1.00  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;Joinability]
% 3.43/1.00  --sup_full_bw                           [BwDemod;BwSubsumption]
% 3.43/1.00  --sup_immed_triv                        [TrivRules]
% 3.43/1.00  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 3.43/1.00  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption]
% 3.43/1.00  --sup_immed_bw_main                     []
% 3.43/1.00  --sup_immed_bw_immed                    [BwDemod;BwSubsumption]
% 3.43/1.00  --sup_input_triv                        [Unflattening;TrivRules]
% 3.43/1.00  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption]
% 3.43/1.00  --sup_input_bw                          []
% 3.43/1.00  
% 3.43/1.00  ------ Combination Options
% 3.43/1.00  
% 3.43/1.00  --comb_res_mult                         3
% 3.43/1.00  --comb_sup_mult                         2
% 3.43/1.00  --comb_inst_mult                        10
% 3.43/1.00  
% 3.43/1.00  ------ Debug Options
% 3.43/1.00  
% 3.43/1.00  --dbg_backtrace                         false
% 3.43/1.00  --dbg_dump_prop_clauses                 false
% 3.43/1.00  --dbg_dump_prop_clauses_file            -
% 3.43/1.00  --dbg_out_stat                          false
% 3.43/1.00  
% 3.43/1.00  
% 3.43/1.00  
% 3.43/1.00  
% 3.43/1.00  ------ Proving...
% 3.43/1.00  
% 3.43/1.00  
% 3.43/1.00  % SZS status Theorem for theBenchmark.p
% 3.43/1.00  
% 3.43/1.00  % SZS output start CNFRefutation for theBenchmark.p
% 3.43/1.00  
% 3.43/1.00  fof(f22,conjecture,(
% 3.43/1.00    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => k2_subset_1(X0) = k4_subset_1(X0,X1,k3_subset_1(X0,X1)))),
% 3.43/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.43/1.00  
% 3.43/1.00  fof(f23,negated_conjecture,(
% 3.43/1.00    ~! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => k2_subset_1(X0) = k4_subset_1(X0,X1,k3_subset_1(X0,X1)))),
% 3.43/1.00    inference(negated_conjecture,[],[f22])).
% 3.43/1.00  
% 3.43/1.00  fof(f30,plain,(
% 3.43/1.00    ? [X0,X1] : (k2_subset_1(X0) != k4_subset_1(X0,X1,k3_subset_1(X0,X1)) & m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 3.43/1.00    inference(ennf_transformation,[],[f23])).
% 3.43/1.00  
% 3.43/1.00  fof(f38,plain,(
% 3.43/1.00    ? [X0,X1] : (k2_subset_1(X0) != k4_subset_1(X0,X1,k3_subset_1(X0,X1)) & m1_subset_1(X1,k1_zfmisc_1(X0))) => (k2_subset_1(sK1) != k4_subset_1(sK1,sK2,k3_subset_1(sK1,sK2)) & m1_subset_1(sK2,k1_zfmisc_1(sK1)))),
% 3.43/1.00    introduced(choice_axiom,[])).
% 3.43/1.00  
% 3.43/1.00  fof(f39,plain,(
% 3.43/1.00    k2_subset_1(sK1) != k4_subset_1(sK1,sK2,k3_subset_1(sK1,sK2)) & m1_subset_1(sK2,k1_zfmisc_1(sK1))),
% 3.43/1.00    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1,sK2])],[f30,f38])).
% 3.43/1.00  
% 3.43/1.00  fof(f69,plain,(
% 3.43/1.00    m1_subset_1(sK2,k1_zfmisc_1(sK1))),
% 3.43/1.00    inference(cnf_transformation,[],[f39])).
% 3.43/1.00  
% 3.43/1.00  fof(f18,axiom,(
% 3.43/1.00    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => k4_xboole_0(X0,X1) = k3_subset_1(X0,X1))),
% 3.43/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.43/1.00  
% 3.43/1.00  fof(f26,plain,(
% 3.43/1.00    ! [X0,X1] : (k4_xboole_0(X0,X1) = k3_subset_1(X0,X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 3.43/1.00    inference(ennf_transformation,[],[f18])).
% 3.43/1.00  
% 3.43/1.00  fof(f65,plain,(
% 3.43/1.00    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k3_subset_1(X0,X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 3.43/1.00    inference(cnf_transformation,[],[f26])).
% 3.43/1.00  
% 3.43/1.00  fof(f19,axiom,(
% 3.43/1.00    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => m1_subset_1(k3_subset_1(X0,X1),k1_zfmisc_1(X0)))),
% 3.43/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.43/1.00  
% 3.43/1.00  fof(f27,plain,(
% 3.43/1.00    ! [X0,X1] : (m1_subset_1(k3_subset_1(X0,X1),k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 3.43/1.00    inference(ennf_transformation,[],[f19])).
% 3.43/1.00  
% 3.43/1.00  fof(f66,plain,(
% 3.43/1.00    ( ! [X0,X1] : (m1_subset_1(k3_subset_1(X0,X1),k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 3.43/1.00    inference(cnf_transformation,[],[f27])).
% 3.43/1.00  
% 3.43/1.00  fof(f21,axiom,(
% 3.43/1.00    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(X0)) & m1_subset_1(X1,k1_zfmisc_1(X0))) => k2_xboole_0(X1,X2) = k4_subset_1(X0,X1,X2))),
% 3.43/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.43/1.00  
% 3.43/1.00  fof(f28,plain,(
% 3.43/1.00    ! [X0,X1,X2] : (k2_xboole_0(X1,X2) = k4_subset_1(X0,X1,X2) | (~m1_subset_1(X2,k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0))))),
% 3.43/1.00    inference(ennf_transformation,[],[f21])).
% 3.43/1.00  
% 3.43/1.00  fof(f29,plain,(
% 3.43/1.00    ! [X0,X1,X2] : (k2_xboole_0(X1,X2) = k4_subset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 3.43/1.00    inference(flattening,[],[f28])).
% 3.43/1.00  
% 3.43/1.00  fof(f68,plain,(
% 3.43/1.00    ( ! [X2,X0,X1] : (k2_xboole_0(X1,X2) = k4_subset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 3.43/1.00    inference(cnf_transformation,[],[f29])).
% 3.43/1.00  
% 3.43/1.00  fof(f11,axiom,(
% 3.43/1.00    ! [X0,X1] : k5_xboole_0(k5_xboole_0(X0,X1),k3_xboole_0(X0,X1)) = k2_xboole_0(X0,X1)),
% 3.43/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.43/1.00  
% 3.43/1.00  fof(f52,plain,(
% 3.43/1.00    ( ! [X0,X1] : (k5_xboole_0(k5_xboole_0(X0,X1),k3_xboole_0(X0,X1)) = k2_xboole_0(X0,X1)) )),
% 3.43/1.00    inference(cnf_transformation,[],[f11])).
% 3.43/1.00  
% 3.43/1.00  fof(f9,axiom,(
% 3.43/1.00    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1))),
% 3.43/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.43/1.00  
% 3.43/1.00  fof(f50,plain,(
% 3.43/1.00    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1))) )),
% 3.43/1.00    inference(cnf_transformation,[],[f9])).
% 3.43/1.00  
% 3.43/1.00  fof(f71,plain,(
% 3.43/1.00    ( ! [X0,X1] : (k5_xboole_0(k5_xboole_0(X0,X1),k4_xboole_0(X0,k4_xboole_0(X0,X1))) = k2_xboole_0(X0,X1)) )),
% 3.43/1.00    inference(definition_unfolding,[],[f52,f50])).
% 3.43/1.00  
% 3.43/1.00  fof(f80,plain,(
% 3.43/1.00    ( ! [X2,X0,X1] : (k5_xboole_0(k5_xboole_0(X1,X2),k4_xboole_0(X1,k4_xboole_0(X1,X2))) = k4_subset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 3.43/1.00    inference(definition_unfolding,[],[f68,f71])).
% 3.43/1.00  
% 3.43/1.00  fof(f15,axiom,(
% 3.43/1.00    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1))),
% 3.43/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.43/1.00  
% 3.43/1.00  fof(f59,plain,(
% 3.43/1.00    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1))) )),
% 3.43/1.00    inference(cnf_transformation,[],[f15])).
% 3.43/1.00  
% 3.43/1.00  fof(f13,axiom,(
% 3.43/1.00    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1)),
% 3.43/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.43/1.00  
% 3.43/1.00  fof(f54,plain,(
% 3.43/1.00    ( ! [X0,X1] : (k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1)) )),
% 3.43/1.00    inference(cnf_transformation,[],[f13])).
% 3.43/1.00  
% 3.43/1.00  fof(f79,plain,(
% 3.43/1.00    ( ! [X0,X1] : (k5_xboole_0(k5_xboole_0(X0,X1),k4_xboole_0(X0,k4_xboole_0(X0,X1))) = k3_tarski(k1_enumset1(X0,X0,X1))) )),
% 3.43/1.00    inference(definition_unfolding,[],[f59,f71,f54])).
% 3.43/1.00  
% 3.43/1.00  fof(f16,axiom,(
% 3.43/1.00    ! [X0,X1] : ((v1_xboole_0(X0) => (m1_subset_1(X1,X0) <=> v1_xboole_0(X1))) & (~v1_xboole_0(X0) => (m1_subset_1(X1,X0) <=> r2_hidden(X1,X0))))),
% 3.43/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.43/1.00  
% 3.43/1.00  fof(f25,plain,(
% 3.43/1.00    ! [X0,X1] : (((m1_subset_1(X1,X0) <=> v1_xboole_0(X1)) | ~v1_xboole_0(X0)) & ((m1_subset_1(X1,X0) <=> r2_hidden(X1,X0)) | v1_xboole_0(X0)))),
% 3.43/1.00    inference(ennf_transformation,[],[f16])).
% 3.43/1.00  
% 3.43/1.00  fof(f37,plain,(
% 3.43/1.00    ! [X0,X1] : ((((m1_subset_1(X1,X0) | ~v1_xboole_0(X1)) & (v1_xboole_0(X1) | ~m1_subset_1(X1,X0))) | ~v1_xboole_0(X0)) & (((m1_subset_1(X1,X0) | ~r2_hidden(X1,X0)) & (r2_hidden(X1,X0) | ~m1_subset_1(X1,X0))) | v1_xboole_0(X0)))),
% 3.43/1.00    inference(nnf_transformation,[],[f25])).
% 3.43/1.00  
% 3.43/1.00  fof(f60,plain,(
% 3.43/1.00    ( ! [X0,X1] : (r2_hidden(X1,X0) | ~m1_subset_1(X1,X0) | v1_xboole_0(X0)) )),
% 3.43/1.00    inference(cnf_transformation,[],[f37])).
% 3.43/1.00  
% 3.43/1.00  fof(f20,axiom,(
% 3.43/1.00    ! [X0] : ~v1_xboole_0(k1_zfmisc_1(X0))),
% 3.43/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.43/1.00  
% 3.43/1.00  fof(f67,plain,(
% 3.43/1.00    ( ! [X0] : (~v1_xboole_0(k1_zfmisc_1(X0))) )),
% 3.43/1.00    inference(cnf_transformation,[],[f20])).
% 3.43/1.00  
% 3.43/1.00  fof(f14,axiom,(
% 3.43/1.00    ! [X0,X1] : (k1_zfmisc_1(X0) = X1 <=> ! [X2] : (r2_hidden(X2,X1) <=> r1_tarski(X2,X0)))),
% 3.43/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.43/1.00  
% 3.43/1.00  fof(f33,plain,(
% 3.43/1.00    ! [X0,X1] : ((k1_zfmisc_1(X0) = X1 | ? [X2] : ((~r1_tarski(X2,X0) | ~r2_hidden(X2,X1)) & (r1_tarski(X2,X0) | r2_hidden(X2,X1)))) & (! [X2] : ((r2_hidden(X2,X1) | ~r1_tarski(X2,X0)) & (r1_tarski(X2,X0) | ~r2_hidden(X2,X1))) | k1_zfmisc_1(X0) != X1))),
% 3.43/1.00    inference(nnf_transformation,[],[f14])).
% 3.43/1.00  
% 3.43/1.00  fof(f34,plain,(
% 3.43/1.00    ! [X0,X1] : ((k1_zfmisc_1(X0) = X1 | ? [X2] : ((~r1_tarski(X2,X0) | ~r2_hidden(X2,X1)) & (r1_tarski(X2,X0) | r2_hidden(X2,X1)))) & (! [X3] : ((r2_hidden(X3,X1) | ~r1_tarski(X3,X0)) & (r1_tarski(X3,X0) | ~r2_hidden(X3,X1))) | k1_zfmisc_1(X0) != X1))),
% 3.43/1.00    inference(rectify,[],[f33])).
% 3.43/1.00  
% 3.43/1.00  fof(f35,plain,(
% 3.43/1.00    ! [X1,X0] : (? [X2] : ((~r1_tarski(X2,X0) | ~r2_hidden(X2,X1)) & (r1_tarski(X2,X0) | r2_hidden(X2,X1))) => ((~r1_tarski(sK0(X0,X1),X0) | ~r2_hidden(sK0(X0,X1),X1)) & (r1_tarski(sK0(X0,X1),X0) | r2_hidden(sK0(X0,X1),X1))))),
% 3.43/1.00    introduced(choice_axiom,[])).
% 3.43/1.00  
% 3.43/1.00  fof(f36,plain,(
% 3.43/1.00    ! [X0,X1] : ((k1_zfmisc_1(X0) = X1 | ((~r1_tarski(sK0(X0,X1),X0) | ~r2_hidden(sK0(X0,X1),X1)) & (r1_tarski(sK0(X0,X1),X0) | r2_hidden(sK0(X0,X1),X1)))) & (! [X3] : ((r2_hidden(X3,X1) | ~r1_tarski(X3,X0)) & (r1_tarski(X3,X0) | ~r2_hidden(X3,X1))) | k1_zfmisc_1(X0) != X1))),
% 3.43/1.00    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f34,f35])).
% 3.43/1.00  
% 3.43/1.00  fof(f55,plain,(
% 3.43/1.00    ( ! [X0,X3,X1] : (r1_tarski(X3,X0) | ~r2_hidden(X3,X1) | k1_zfmisc_1(X0) != X1) )),
% 3.43/1.00    inference(cnf_transformation,[],[f36])).
% 3.43/1.00  
% 3.43/1.00  fof(f84,plain,(
% 3.43/1.00    ( ! [X0,X3] : (r1_tarski(X3,X0) | ~r2_hidden(X3,k1_zfmisc_1(X0))) )),
% 3.43/1.00    inference(equality_resolution,[],[f55])).
% 3.43/1.00  
% 3.43/1.00  fof(f6,axiom,(
% 3.43/1.00    ! [X0,X1] : (r1_tarski(X0,X1) => k3_xboole_0(X0,X1) = X0)),
% 3.43/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.43/1.00  
% 3.43/1.00  fof(f24,plain,(
% 3.43/1.00    ! [X0,X1] : (k3_xboole_0(X0,X1) = X0 | ~r1_tarski(X0,X1))),
% 3.43/1.00    inference(ennf_transformation,[],[f6])).
% 3.43/1.00  
% 3.43/1.00  fof(f47,plain,(
% 3.43/1.00    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = X0 | ~r1_tarski(X0,X1)) )),
% 3.43/1.00    inference(cnf_transformation,[],[f24])).
% 3.43/1.00  
% 3.43/1.00  fof(f76,plain,(
% 3.43/1.00    ( ! [X0,X1] : (k4_xboole_0(X0,k4_xboole_0(X0,X1)) = X0 | ~r1_tarski(X0,X1)) )),
% 3.43/1.00    inference(definition_unfolding,[],[f47,f50])).
% 3.43/1.00  
% 3.43/1.00  fof(f1,axiom,(
% 3.43/1.00    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0)),
% 3.43/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.43/1.00  
% 3.43/1.00  fof(f40,plain,(
% 3.43/1.00    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0)) )),
% 3.43/1.00    inference(cnf_transformation,[],[f1])).
% 3.43/1.00  
% 3.43/1.00  fof(f73,plain,(
% 3.43/1.00    ( ! [X0,X1] : (k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k4_xboole_0(X1,k4_xboole_0(X1,X0))) )),
% 3.43/1.00    inference(definition_unfolding,[],[f40,f50,f50])).
% 3.43/1.00  
% 3.43/1.00  fof(f3,axiom,(
% 3.43/1.00    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))),
% 3.43/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.43/1.00  
% 3.43/1.00  fof(f44,plain,(
% 3.43/1.00    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))) )),
% 3.43/1.00    inference(cnf_transformation,[],[f3])).
% 3.43/1.00  
% 3.43/1.00  fof(f72,plain,(
% 3.43/1.00    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k5_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X0,X1)))) )),
% 3.43/1.00    inference(definition_unfolding,[],[f44,f50])).
% 3.43/1.00  
% 3.43/1.00  fof(f5,axiom,(
% 3.43/1.00    ! [X0,X1] : k2_xboole_0(X0,k3_xboole_0(X0,X1)) = X0),
% 3.43/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.43/1.00  
% 3.43/1.00  fof(f46,plain,(
% 3.43/1.00    ( ! [X0,X1] : (k2_xboole_0(X0,k3_xboole_0(X0,X1)) = X0) )),
% 3.43/1.00    inference(cnf_transformation,[],[f5])).
% 3.43/1.00  
% 3.43/1.00  fof(f75,plain,(
% 3.43/1.00    ( ! [X0,X1] : (k5_xboole_0(k5_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X0,X1))),k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X0,X1))))) = X0) )),
% 3.43/1.00    inference(definition_unfolding,[],[f46,f71,f50])).
% 3.43/1.00  
% 3.43/1.00  fof(f4,axiom,(
% 3.43/1.00    ! [X0,X1,X2] : k3_xboole_0(k5_xboole_0(X0,X2),X1) = k5_xboole_0(k3_xboole_0(X0,X1),k3_xboole_0(X2,X1))),
% 3.43/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.43/1.00  
% 3.43/1.00  fof(f45,plain,(
% 3.43/1.00    ( ! [X2,X0,X1] : (k3_xboole_0(k5_xboole_0(X0,X2),X1) = k5_xboole_0(k3_xboole_0(X0,X1),k3_xboole_0(X2,X1))) )),
% 3.43/1.00    inference(cnf_transformation,[],[f4])).
% 3.43/1.00  
% 3.43/1.00  fof(f74,plain,(
% 3.43/1.00    ( ! [X2,X0,X1] : (k4_xboole_0(k5_xboole_0(X0,X2),k4_xboole_0(k5_xboole_0(X0,X2),X1)) = k5_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),k4_xboole_0(X2,k4_xboole_0(X2,X1)))) )),
% 3.43/1.00    inference(definition_unfolding,[],[f45,f50,f50,f50])).
% 3.43/1.00  
% 3.43/1.00  fof(f10,axiom,(
% 3.43/1.00    ! [X0] : k5_xboole_0(X0,k1_xboole_0) = X0),
% 3.43/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.43/1.00  
% 3.43/1.00  fof(f51,plain,(
% 3.43/1.00    ( ! [X0] : (k5_xboole_0(X0,k1_xboole_0) = X0) )),
% 3.43/1.00    inference(cnf_transformation,[],[f10])).
% 3.43/1.00  
% 3.43/1.00  fof(f8,axiom,(
% 3.43/1.00    ! [X0,X1] : k4_xboole_0(X0,k2_xboole_0(X0,X1)) = k1_xboole_0),
% 3.43/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.43/1.00  
% 3.43/1.00  fof(f49,plain,(
% 3.43/1.00    ( ! [X0,X1] : (k4_xboole_0(X0,k2_xboole_0(X0,X1)) = k1_xboole_0) )),
% 3.43/1.00    inference(cnf_transformation,[],[f8])).
% 3.43/1.00  
% 3.43/1.00  fof(f77,plain,(
% 3.43/1.00    ( ! [X0,X1] : (k4_xboole_0(X0,k5_xboole_0(k5_xboole_0(X0,X1),k4_xboole_0(X0,k4_xboole_0(X0,X1)))) = k1_xboole_0) )),
% 3.43/1.00    inference(definition_unfolding,[],[f49,f71])).
% 3.43/1.00  
% 3.43/1.00  fof(f70,plain,(
% 3.43/1.00    k2_subset_1(sK1) != k4_subset_1(sK1,sK2,k3_subset_1(sK1,sK2))),
% 3.43/1.00    inference(cnf_transformation,[],[f39])).
% 3.43/1.00  
% 3.43/1.00  fof(f17,axiom,(
% 3.43/1.00    ! [X0] : k2_subset_1(X0) = X0),
% 3.43/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.43/1.00  
% 3.43/1.00  fof(f64,plain,(
% 3.43/1.00    ( ! [X0] : (k2_subset_1(X0) = X0) )),
% 3.43/1.00    inference(cnf_transformation,[],[f17])).
% 3.43/1.00  
% 3.43/1.00  cnf(c_27,negated_conjecture,
% 3.43/1.00      ( m1_subset_1(sK2,k1_zfmisc_1(sK1)) ),
% 3.43/1.00      inference(cnf_transformation,[],[f69]) ).
% 3.43/1.00  
% 3.43/1.00  cnf(c_1097,plain,
% 3.43/1.00      ( m1_subset_1(sK2,k1_zfmisc_1(sK1)) = iProver_top ),
% 3.43/1.00      inference(predicate_to_equality,[status(thm)],[c_27]) ).
% 3.43/1.00  
% 3.43/1.00  cnf(c_22,plain,
% 3.43/1.00      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
% 3.43/1.00      | k3_subset_1(X1,X0) = k4_xboole_0(X1,X0) ),
% 3.43/1.00      inference(cnf_transformation,[],[f65]) ).
% 3.43/1.00  
% 3.43/1.00  cnf(c_1101,plain,
% 3.43/1.00      ( k3_subset_1(X0,X1) = k4_xboole_0(X0,X1)
% 3.43/1.00      | m1_subset_1(X1,k1_zfmisc_1(X0)) != iProver_top ),
% 3.43/1.00      inference(predicate_to_equality,[status(thm)],[c_22]) ).
% 3.43/1.00  
% 3.43/1.00  cnf(c_3249,plain,
% 3.43/1.00      ( k3_subset_1(sK1,sK2) = k4_xboole_0(sK1,sK2) ),
% 3.43/1.00      inference(superposition,[status(thm)],[c_1097,c_1101]) ).
% 3.43/1.00  
% 3.43/1.00  cnf(c_23,plain,
% 3.43/1.00      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
% 3.43/1.00      | m1_subset_1(k3_subset_1(X1,X0),k1_zfmisc_1(X1)) ),
% 3.43/1.00      inference(cnf_transformation,[],[f66]) ).
% 3.43/1.00  
% 3.43/1.00  cnf(c_1100,plain,
% 3.43/1.00      ( m1_subset_1(X0,k1_zfmisc_1(X1)) != iProver_top
% 3.43/1.00      | m1_subset_1(k3_subset_1(X1,X0),k1_zfmisc_1(X1)) = iProver_top ),
% 3.43/1.00      inference(predicate_to_equality,[status(thm)],[c_23]) ).
% 3.43/1.00  
% 3.43/1.00  cnf(c_3310,plain,
% 3.43/1.00      ( m1_subset_1(k4_xboole_0(sK1,sK2),k1_zfmisc_1(sK1)) = iProver_top
% 3.43/1.00      | m1_subset_1(sK2,k1_zfmisc_1(sK1)) != iProver_top ),
% 3.43/1.00      inference(superposition,[status(thm)],[c_3249,c_1100]) ).
% 3.43/1.00  
% 3.43/1.00  cnf(c_28,plain,
% 3.43/1.00      ( m1_subset_1(sK2,k1_zfmisc_1(sK1)) = iProver_top ),
% 3.43/1.00      inference(predicate_to_equality,[status(thm)],[c_27]) ).
% 3.43/1.00  
% 3.43/1.00  cnf(c_3464,plain,
% 3.43/1.00      ( m1_subset_1(k4_xboole_0(sK1,sK2),k1_zfmisc_1(sK1)) = iProver_top ),
% 3.43/1.00      inference(global_propositional_subsumption,
% 3.43/1.00                [status(thm)],
% 3.43/1.00                [c_3310,c_28]) ).
% 3.43/1.00  
% 3.43/1.00  cnf(c_25,plain,
% 3.43/1.00      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
% 3.43/1.00      | ~ m1_subset_1(X2,k1_zfmisc_1(X1))
% 3.43/1.00      | k5_xboole_0(k5_xboole_0(X0,X2),k4_xboole_0(X0,k4_xboole_0(X0,X2))) = k4_subset_1(X1,X0,X2) ),
% 3.43/1.00      inference(cnf_transformation,[],[f80]) ).
% 3.43/1.00  
% 3.43/1.00  cnf(c_1098,plain,
% 3.43/1.00      ( k5_xboole_0(k5_xboole_0(X0,X1),k4_xboole_0(X0,k4_xboole_0(X0,X1))) = k4_subset_1(X2,X0,X1)
% 3.43/1.00      | m1_subset_1(X0,k1_zfmisc_1(X2)) != iProver_top
% 3.43/1.00      | m1_subset_1(X1,k1_zfmisc_1(X2)) != iProver_top ),
% 3.43/1.00      inference(predicate_to_equality,[status(thm)],[c_25]) ).
% 3.43/1.00  
% 3.43/1.00  cnf(c_16,plain,
% 3.43/1.00      ( k5_xboole_0(k5_xboole_0(X0,X1),k4_xboole_0(X0,k4_xboole_0(X0,X1))) = k3_tarski(k1_enumset1(X0,X0,X1)) ),
% 3.43/1.00      inference(cnf_transformation,[],[f79]) ).
% 3.43/1.00  
% 3.43/1.00  cnf(c_1117,plain,
% 3.43/1.00      ( k3_tarski(k1_enumset1(X0,X0,X1)) = k4_subset_1(X2,X0,X1)
% 3.43/1.00      | m1_subset_1(X0,k1_zfmisc_1(X2)) != iProver_top
% 3.43/1.00      | m1_subset_1(X1,k1_zfmisc_1(X2)) != iProver_top ),
% 3.43/1.00      inference(demodulation,[status(thm)],[c_1098,c_16]) ).
% 3.43/1.00  
% 3.43/1.00  cnf(c_8270,plain,
% 3.43/1.00      ( k3_tarski(k1_enumset1(sK2,sK2,X0)) = k4_subset_1(sK1,sK2,X0)
% 3.43/1.00      | m1_subset_1(X0,k1_zfmisc_1(sK1)) != iProver_top ),
% 3.43/1.00      inference(superposition,[status(thm)],[c_1097,c_1117]) ).
% 3.43/1.00  
% 3.43/1.00  cnf(c_8858,plain,
% 3.43/1.00      ( k3_tarski(k1_enumset1(sK2,sK2,k4_xboole_0(sK1,sK2))) = k4_subset_1(sK1,sK2,k4_xboole_0(sK1,sK2)) ),
% 3.43/1.00      inference(superposition,[status(thm)],[c_3464,c_8270]) ).
% 3.43/1.00  
% 3.43/1.00  cnf(c_20,plain,
% 3.43/1.00      ( ~ m1_subset_1(X0,X1) | r2_hidden(X0,X1) | v1_xboole_0(X1) ),
% 3.43/1.00      inference(cnf_transformation,[],[f60]) ).
% 3.43/1.00  
% 3.43/1.00  cnf(c_1102,plain,
% 3.43/1.00      ( m1_subset_1(X0,X1) != iProver_top
% 3.43/1.00      | r2_hidden(X0,X1) = iProver_top
% 3.43/1.00      | v1_xboole_0(X1) = iProver_top ),
% 3.43/1.00      inference(predicate_to_equality,[status(thm)],[c_20]) ).
% 3.43/1.00  
% 3.43/1.00  cnf(c_2094,plain,
% 3.43/1.00      ( r2_hidden(sK2,k1_zfmisc_1(sK1)) = iProver_top
% 3.43/1.00      | v1_xboole_0(k1_zfmisc_1(sK1)) = iProver_top ),
% 3.43/1.00      inference(superposition,[status(thm)],[c_1097,c_1102]) ).
% 3.43/1.00  
% 3.43/1.00  cnf(c_24,plain,
% 3.43/1.00      ( ~ v1_xboole_0(k1_zfmisc_1(X0)) ),
% 3.43/1.00      inference(cnf_transformation,[],[f67]) ).
% 3.43/1.00  
% 3.43/1.00  cnf(c_32,plain,
% 3.43/1.00      ( v1_xboole_0(k1_zfmisc_1(X0)) != iProver_top ),
% 3.43/1.00      inference(predicate_to_equality,[status(thm)],[c_24]) ).
% 3.43/1.00  
% 3.43/1.00  cnf(c_34,plain,
% 3.43/1.00      ( v1_xboole_0(k1_zfmisc_1(sK1)) != iProver_top ),
% 3.43/1.00      inference(instantiation,[status(thm)],[c_32]) ).
% 3.43/1.00  
% 3.43/1.00  cnf(c_2490,plain,
% 3.43/1.00      ( r2_hidden(sK2,k1_zfmisc_1(sK1)) = iProver_top ),
% 3.43/1.00      inference(global_propositional_subsumption,
% 3.43/1.00                [status(thm)],
% 3.43/1.00                [c_2094,c_34]) ).
% 3.43/1.00  
% 3.43/1.00  cnf(c_15,plain,
% 3.43/1.00      ( ~ r2_hidden(X0,k1_zfmisc_1(X1)) | r1_tarski(X0,X1) ),
% 3.43/1.00      inference(cnf_transformation,[],[f84]) ).
% 3.43/1.00  
% 3.43/1.00  cnf(c_1106,plain,
% 3.43/1.00      ( r2_hidden(X0,k1_zfmisc_1(X1)) != iProver_top
% 3.43/1.00      | r1_tarski(X0,X1) = iProver_top ),
% 3.43/1.00      inference(predicate_to_equality,[status(thm)],[c_15]) ).
% 3.43/1.00  
% 3.43/1.00  cnf(c_2800,plain,
% 3.43/1.00      ( r1_tarski(sK2,sK1) = iProver_top ),
% 3.43/1.00      inference(superposition,[status(thm)],[c_2490,c_1106]) ).
% 3.43/1.00  
% 3.43/1.00  cnf(c_7,plain,
% 3.43/1.00      ( ~ r1_tarski(X0,X1) | k4_xboole_0(X0,k4_xboole_0(X0,X1)) = X0 ),
% 3.43/1.00      inference(cnf_transformation,[],[f76]) ).
% 3.43/1.00  
% 3.43/1.00  cnf(c_1111,plain,
% 3.43/1.00      ( k4_xboole_0(X0,k4_xboole_0(X0,X1)) = X0
% 3.43/1.00      | r1_tarski(X0,X1) != iProver_top ),
% 3.43/1.00      inference(predicate_to_equality,[status(thm)],[c_7]) ).
% 3.43/1.00  
% 3.43/1.00  cnf(c_3245,plain,
% 3.43/1.00      ( k4_xboole_0(sK2,k4_xboole_0(sK2,sK1)) = sK2 ),
% 3.43/1.00      inference(superposition,[status(thm)],[c_2800,c_1111]) ).
% 3.43/1.00  
% 3.43/1.00  cnf(c_1,plain,
% 3.43/1.00      ( k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k4_xboole_0(X1,k4_xboole_0(X1,X0)) ),
% 3.43/1.00      inference(cnf_transformation,[],[f73]) ).
% 3.43/1.00  
% 3.43/1.00  cnf(c_3489,plain,
% 3.43/1.00      ( k4_xboole_0(sK1,k4_xboole_0(sK1,sK2)) = sK2 ),
% 3.43/1.00      inference(superposition,[status(thm)],[c_3245,c_1]) ).
% 3.43/1.00  
% 3.43/1.00  cnf(c_3771,plain,
% 3.43/1.00      ( k5_xboole_0(k5_xboole_0(sK1,k4_xboole_0(sK1,sK2)),k4_xboole_0(sK1,sK2)) = k3_tarski(k1_enumset1(sK1,sK1,k4_xboole_0(sK1,sK2))) ),
% 3.43/1.00      inference(superposition,[status(thm)],[c_3489,c_16]) ).
% 3.43/1.00  
% 3.43/1.00  cnf(c_0,plain,
% 3.43/1.00      ( k5_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X0,X1))) = k4_xboole_0(X0,X1) ),
% 3.43/1.00      inference(cnf_transformation,[],[f72]) ).
% 3.43/1.00  
% 3.43/1.00  cnf(c_3772,plain,
% 3.43/1.00      ( k5_xboole_0(sK1,k4_xboole_0(sK1,sK2)) = k4_xboole_0(sK1,k4_xboole_0(sK1,sK2)) ),
% 3.43/1.00      inference(superposition,[status(thm)],[c_3489,c_0]) ).
% 3.43/1.00  
% 3.43/1.00  cnf(c_3791,plain,
% 3.43/1.00      ( k5_xboole_0(sK1,k4_xboole_0(sK1,sK2)) = sK2 ),
% 3.43/1.00      inference(demodulation,[status(thm)],[c_3772,c_3489]) ).
% 3.43/1.00  
% 3.43/1.00  cnf(c_3792,plain,
% 3.43/1.00      ( k3_tarski(k1_enumset1(sK1,sK1,k4_xboole_0(sK1,sK2))) = k5_xboole_0(sK2,k4_xboole_0(sK1,sK2)) ),
% 3.43/1.00      inference(demodulation,[status(thm)],[c_3771,c_3791]) ).
% 3.43/1.00  
% 3.43/1.00  cnf(c_1602,plain,
% 3.43/1.00      ( k5_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X0,X1))))) = k3_tarski(k1_enumset1(X0,X0,k4_xboole_0(X0,k4_xboole_0(X0,X1)))) ),
% 3.43/1.00      inference(superposition,[status(thm)],[c_0,c_16]) ).
% 3.43/1.00  
% 3.43/1.00  cnf(c_6,plain,
% 3.43/1.00      ( k5_xboole_0(k5_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X0,X1))),k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X0,X1))))) = X0 ),
% 3.43/1.00      inference(cnf_transformation,[],[f75]) ).
% 3.43/1.00  
% 3.43/1.00  cnf(c_1116,plain,
% 3.43/1.00      ( k5_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X0,X1))))) = X0 ),
% 3.43/1.00      inference(light_normalisation,[status(thm)],[c_6,c_0]) ).
% 3.43/1.00  
% 3.43/1.00  cnf(c_1612,plain,
% 3.43/1.00      ( k3_tarski(k1_enumset1(X0,X0,k4_xboole_0(X0,k4_xboole_0(X0,X1)))) = X0 ),
% 3.43/1.00      inference(light_normalisation,[status(thm)],[c_1602,c_1116]) ).
% 3.43/1.00  
% 3.43/1.00  cnf(c_2652,plain,
% 3.43/1.00      ( k3_tarski(k1_enumset1(X0,X0,k4_xboole_0(X0,k4_xboole_0(X1,k4_xboole_0(X1,X0))))) = X0 ),
% 3.43/1.00      inference(superposition,[status(thm)],[c_1,c_1612]) ).
% 3.43/1.00  
% 3.43/1.00  cnf(c_3486,plain,
% 3.43/1.00      ( k3_tarski(k1_enumset1(sK1,sK1,k4_xboole_0(sK1,sK2))) = sK1 ),
% 3.43/1.00      inference(superposition,[status(thm)],[c_3245,c_2652]) ).
% 3.43/1.00  
% 3.43/1.00  cnf(c_3793,plain,
% 3.43/1.00      ( k5_xboole_0(sK2,k4_xboole_0(sK1,sK2)) = sK1 ),
% 3.43/1.00      inference(light_normalisation,[status(thm)],[c_3792,c_3486]) ).
% 3.43/1.00  
% 3.43/1.00  cnf(c_5217,plain,
% 3.43/1.00      ( k5_xboole_0(sK1,k4_xboole_0(sK2,k4_xboole_0(sK2,k4_xboole_0(sK1,sK2)))) = k3_tarski(k1_enumset1(sK2,sK2,k4_xboole_0(sK1,sK2))) ),
% 3.43/1.00      inference(superposition,[status(thm)],[c_3793,c_16]) ).
% 3.43/1.00  
% 3.43/1.00  cnf(c_1489,plain,
% 3.43/1.00      ( k5_xboole_0(X0,k4_xboole_0(X1,k4_xboole_0(X1,X0))) = k4_xboole_0(X0,X1) ),
% 3.43/1.00      inference(superposition,[status(thm)],[c_1,c_0]) ).
% 3.43/1.00  
% 3.43/1.00  cnf(c_3488,plain,
% 3.43/1.00      ( k5_xboole_0(sK1,sK2) = k4_xboole_0(sK1,sK2) ),
% 3.43/1.00      inference(superposition,[status(thm)],[c_3245,c_1489]) ).
% 3.43/1.00  
% 3.43/1.00  cnf(c_3689,plain,
% 3.43/1.00      ( k5_xboole_0(k4_xboole_0(sK1,sK2),k4_xboole_0(sK1,k4_xboole_0(sK1,sK2))) = k3_tarski(k1_enumset1(sK1,sK1,sK2)) ),
% 3.43/1.00      inference(superposition,[status(thm)],[c_3488,c_16]) ).
% 3.43/1.00  
% 3.43/1.00  cnf(c_2649,plain,
% 3.43/1.00      ( k3_tarski(k1_enumset1(X0,X0,k4_xboole_0(X1,k4_xboole_0(X1,X0)))) = X0 ),
% 3.43/1.00      inference(superposition,[status(thm)],[c_1,c_1612]) ).
% 3.43/1.00  
% 3.43/1.00  cnf(c_3487,plain,
% 3.43/1.00      ( k3_tarski(k1_enumset1(sK1,sK1,sK2)) = sK1 ),
% 3.43/1.00      inference(superposition,[status(thm)],[c_3245,c_2649]) ).
% 3.43/1.00  
% 3.43/1.00  cnf(c_3690,plain,
% 3.43/1.00      ( k5_xboole_0(k4_xboole_0(sK1,sK2),sK2) = sK1 ),
% 3.43/1.00      inference(light_normalisation,[status(thm)],[c_3689,c_3487,c_3489]) ).
% 3.43/1.00  
% 3.43/1.00  cnf(c_1605,plain,
% 3.43/1.00      ( k5_xboole_0(k5_xboole_0(X0,X1),k4_xboole_0(X1,k4_xboole_0(X1,X0))) = k3_tarski(k1_enumset1(X0,X0,X1)) ),
% 3.43/1.00      inference(superposition,[status(thm)],[c_1,c_16]) ).
% 3.43/1.00  
% 3.43/1.00  cnf(c_4909,plain,
% 3.43/1.00      ( k3_tarski(k1_enumset1(k4_xboole_0(sK1,sK2),k4_xboole_0(sK1,sK2),sK2)) = k5_xboole_0(sK1,k4_xboole_0(sK2,k4_xboole_0(sK2,k4_xboole_0(sK1,sK2)))) ),
% 3.43/1.00      inference(superposition,[status(thm)],[c_3690,c_1605]) ).
% 3.43/1.00  
% 3.43/1.00  cnf(c_4733,plain,
% 3.43/1.00      ( k5_xboole_0(sK1,k4_xboole_0(k4_xboole_0(sK1,sK2),k4_xboole_0(k4_xboole_0(sK1,sK2),sK2))) = k3_tarski(k1_enumset1(k4_xboole_0(sK1,sK2),k4_xboole_0(sK1,sK2),sK2)) ),
% 3.43/1.00      inference(superposition,[status(thm)],[c_3690,c_16]) ).
% 3.43/1.00  
% 3.43/1.00  cnf(c_5,plain,
% 3.43/1.00      ( k5_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),k4_xboole_0(X2,k4_xboole_0(X2,X1))) = k4_xboole_0(k5_xboole_0(X0,X2),k4_xboole_0(k5_xboole_0(X0,X2),X1)) ),
% 3.43/1.00      inference(cnf_transformation,[],[f74]) ).
% 3.43/1.00  
% 3.43/1.00  cnf(c_1714,plain,
% 3.43/1.00      ( k4_xboole_0(k5_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X0,X1))),k4_xboole_0(k5_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X0,X1))),X1)) = k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),X1) ),
% 3.43/1.00      inference(superposition,[status(thm)],[c_5,c_0]) ).
% 3.43/1.00  
% 3.43/1.00  cnf(c_1716,plain,
% 3.43/1.00      ( k4_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(k4_xboole_0(X0,X1),X1)) = k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),X1) ),
% 3.43/1.00      inference(light_normalisation,[status(thm)],[c_1714,c_0]) ).
% 3.43/1.00  
% 3.43/1.00  cnf(c_4734,plain,
% 3.43/1.00      ( k3_tarski(k1_enumset1(k4_xboole_0(sK1,sK2),k4_xboole_0(sK1,sK2),sK2)) = k5_xboole_0(sK1,k4_xboole_0(k4_xboole_0(sK1,k4_xboole_0(sK1,sK2)),sK2)) ),
% 3.43/1.00      inference(demodulation,[status(thm)],[c_4733,c_1716]) ).
% 3.43/1.00  
% 3.43/1.00  cnf(c_4735,plain,
% 3.43/1.00      ( k3_tarski(k1_enumset1(k4_xboole_0(sK1,sK2),k4_xboole_0(sK1,sK2),sK2)) = k5_xboole_0(sK1,k4_xboole_0(sK2,sK2)) ),
% 3.43/1.00      inference(light_normalisation,[status(thm)],[c_4734,c_3489]) ).
% 3.43/1.00  
% 3.43/1.00  cnf(c_10,plain,
% 3.43/1.00      ( k5_xboole_0(X0,k1_xboole_0) = X0 ),
% 3.43/1.00      inference(cnf_transformation,[],[f51]) ).
% 3.43/1.00  
% 3.43/1.00  cnf(c_1604,plain,
% 3.43/1.00      ( k5_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X0,k1_xboole_0))) = k3_tarski(k1_enumset1(X0,X0,k1_xboole_0)) ),
% 3.43/1.00      inference(superposition,[status(thm)],[c_10,c_16]) ).
% 3.43/1.00  
% 3.43/1.00  cnf(c_1611,plain,
% 3.43/1.00      ( k3_tarski(k1_enumset1(X0,X0,k1_xboole_0)) = k4_xboole_0(X0,k1_xboole_0) ),
% 3.43/1.00      inference(demodulation,[status(thm)],[c_1604,c_0]) ).
% 3.43/1.00  
% 3.43/1.00  cnf(c_9,plain,
% 3.43/1.01      ( k4_xboole_0(X0,k5_xboole_0(k5_xboole_0(X0,X1),k4_xboole_0(X0,k4_xboole_0(X0,X1)))) = k1_xboole_0 ),
% 3.43/1.01      inference(cnf_transformation,[],[f77]) ).
% 3.43/1.01  
% 3.43/1.01  cnf(c_1597,plain,
% 3.43/1.01      ( k4_xboole_0(X0,k3_tarski(k1_enumset1(X0,X0,X1))) = k1_xboole_0 ),
% 3.43/1.01      inference(light_normalisation,[status(thm)],[c_9,c_9,c_16]) ).
% 3.43/1.01  
% 3.43/1.01  cnf(c_1793,plain,
% 3.43/1.01      ( k4_xboole_0(X0,k4_xboole_0(X0,k1_xboole_0)) = k1_xboole_0 ),
% 3.43/1.01      inference(superposition,[status(thm)],[c_1611,c_1597]) ).
% 3.43/1.01  
% 3.43/1.01  cnf(c_1803,plain,
% 3.43/1.01      ( k5_xboole_0(X0,k1_xboole_0) = k4_xboole_0(X0,k1_xboole_0) ),
% 3.43/1.01      inference(superposition,[status(thm)],[c_1793,c_0]) ).
% 3.43/1.01  
% 3.43/1.01  cnf(c_1808,plain,
% 3.43/1.01      ( k4_xboole_0(X0,k1_xboole_0) = X0 ),
% 3.43/1.01      inference(light_normalisation,[status(thm)],[c_1803,c_10]) ).
% 3.43/1.01  
% 3.43/1.01  cnf(c_1809,plain,
% 3.43/1.01      ( k4_xboole_0(X0,X0) = k1_xboole_0 ),
% 3.43/1.01      inference(demodulation,[status(thm)],[c_1808,c_1793]) ).
% 3.43/1.01  
% 3.43/1.01  cnf(c_4736,plain,
% 3.43/1.01      ( k3_tarski(k1_enumset1(k4_xboole_0(sK1,sK2),k4_xboole_0(sK1,sK2),sK2)) = sK1 ),
% 3.43/1.01      inference(demodulation,[status(thm)],[c_4735,c_10,c_1809]) ).
% 3.43/1.01  
% 3.43/1.01  cnf(c_4934,plain,
% 3.43/1.01      ( k5_xboole_0(sK1,k4_xboole_0(sK2,k4_xboole_0(sK2,k4_xboole_0(sK1,sK2)))) = sK1 ),
% 3.43/1.01      inference(light_normalisation,[status(thm)],[c_4909,c_4736]) ).
% 3.43/1.01  
% 3.43/1.01  cnf(c_5219,plain,
% 3.43/1.01      ( k3_tarski(k1_enumset1(sK2,sK2,k4_xboole_0(sK1,sK2))) = sK1 ),
% 3.43/1.01      inference(light_normalisation,[status(thm)],[c_5217,c_4934]) ).
% 3.43/1.01  
% 3.43/1.01  cnf(c_8859,plain,
% 3.43/1.01      ( k4_subset_1(sK1,sK2,k4_xboole_0(sK1,sK2)) = sK1 ),
% 3.43/1.01      inference(light_normalisation,[status(thm)],[c_8858,c_5219]) ).
% 3.43/1.01  
% 3.43/1.01  cnf(c_26,negated_conjecture,
% 3.43/1.01      ( k2_subset_1(sK1) != k4_subset_1(sK1,sK2,k3_subset_1(sK1,sK2)) ),
% 3.43/1.01      inference(cnf_transformation,[],[f70]) ).
% 3.43/1.01  
% 3.43/1.01  cnf(c_21,plain,
% 3.43/1.01      ( k2_subset_1(X0) = X0 ),
% 3.43/1.01      inference(cnf_transformation,[],[f64]) ).
% 3.43/1.01  
% 3.43/1.01  cnf(c_1114,plain,
% 3.43/1.01      ( k4_subset_1(sK1,sK2,k3_subset_1(sK1,sK2)) != sK1 ),
% 3.43/1.01      inference(demodulation,[status(thm)],[c_26,c_21]) ).
% 3.43/1.01  
% 3.43/1.01  cnf(c_3309,plain,
% 3.43/1.01      ( k4_subset_1(sK1,sK2,k4_xboole_0(sK1,sK2)) != sK1 ),
% 3.43/1.01      inference(demodulation,[status(thm)],[c_3249,c_1114]) ).
% 3.43/1.01  
% 3.43/1.01  cnf(contradiction,plain,
% 3.43/1.01      ( $false ),
% 3.43/1.01      inference(minisat,[status(thm)],[c_8859,c_3309]) ).
% 3.43/1.01  
% 3.43/1.01  
% 3.43/1.01  % SZS output end CNFRefutation for theBenchmark.p
% 3.43/1.01  
% 3.43/1.01  ------                               Statistics
% 3.43/1.01  
% 3.43/1.01  ------ General
% 3.43/1.01  
% 3.43/1.01  abstr_ref_over_cycles:                  0
% 3.43/1.01  abstr_ref_under_cycles:                 0
% 3.43/1.01  gc_basic_clause_elim:                   0
% 3.43/1.01  forced_gc_time:                         0
% 3.43/1.01  parsing_time:                           0.029
% 3.43/1.01  unif_index_cands_time:                  0.
% 3.43/1.01  unif_index_add_time:                    0.
% 3.43/1.01  orderings_time:                         0.
% 3.43/1.01  out_proof_time:                         0.011
% 3.43/1.01  total_time:                             0.516
% 3.43/1.01  num_of_symbols:                         47
% 3.43/1.01  num_of_terms:                           10835
% 3.43/1.01  
% 3.43/1.01  ------ Preprocessing
% 3.43/1.01  
% 3.43/1.01  num_of_splits:                          0
% 3.43/1.01  num_of_split_atoms:                     0
% 3.43/1.01  num_of_reused_defs:                     0
% 3.43/1.01  num_eq_ax_congr_red:                    18
% 3.43/1.01  num_of_sem_filtered_clauses:            1
% 3.43/1.01  num_of_subtypes:                        0
% 3.43/1.01  monotx_restored_types:                  0
% 3.43/1.01  sat_num_of_epr_types:                   0
% 3.43/1.01  sat_num_of_non_cyclic_types:            0
% 3.43/1.01  sat_guarded_non_collapsed_types:        0
% 3.43/1.01  num_pure_diseq_elim:                    0
% 3.43/1.01  simp_replaced_by:                       0
% 3.43/1.01  res_preprocessed:                       135
% 3.43/1.01  prep_upred:                             0
% 3.43/1.01  prep_unflattend:                        24
% 3.43/1.01  smt_new_axioms:                         0
% 3.43/1.01  pred_elim_cands:                        4
% 3.43/1.01  pred_elim:                              0
% 3.43/1.01  pred_elim_cl:                           0
% 3.43/1.01  pred_elim_cycles:                       2
% 3.43/1.01  merged_defs:                            8
% 3.43/1.01  merged_defs_ncl:                        0
% 3.43/1.01  bin_hyper_res:                          8
% 3.43/1.01  prep_cycles:                            4
% 3.43/1.01  pred_elim_time:                         0.004
% 3.43/1.01  splitting_time:                         0.
% 3.43/1.01  sem_filter_time:                        0.
% 3.43/1.01  monotx_time:                            0.
% 3.43/1.01  subtype_inf_time:                       0.
% 3.43/1.01  
% 3.43/1.01  ------ Problem properties
% 3.43/1.01  
% 3.43/1.01  clauses:                                27
% 3.43/1.01  conjectures:                            2
% 3.43/1.01  epr:                                    7
% 3.43/1.01  horn:                                   24
% 3.43/1.01  ground:                                 2
% 3.43/1.01  unary:                                  14
% 3.43/1.01  binary:                                 5
% 3.43/1.01  lits:                                   48
% 3.43/1.01  lits_eq:                                16
% 3.43/1.01  fd_pure:                                0
% 3.43/1.01  fd_pseudo:                              0
% 3.43/1.01  fd_cond:                                0
% 3.43/1.01  fd_pseudo_cond:                         3
% 3.43/1.01  ac_symbols:                             0
% 3.43/1.01  
% 3.43/1.01  ------ Propositional Solver
% 3.43/1.01  
% 3.43/1.01  prop_solver_calls:                      32
% 3.43/1.01  prop_fast_solver_calls:                 716
% 3.43/1.01  smt_solver_calls:                       0
% 3.43/1.01  smt_fast_solver_calls:                  0
% 3.43/1.01  prop_num_of_clauses:                    3358
% 3.43/1.01  prop_preprocess_simplified:             7286
% 3.43/1.01  prop_fo_subsumed:                       5
% 3.43/1.01  prop_solver_time:                       0.
% 3.43/1.01  smt_solver_time:                        0.
% 3.43/1.01  smt_fast_solver_time:                   0.
% 3.43/1.01  prop_fast_solver_time:                  0.
% 3.43/1.01  prop_unsat_core_time:                   0.
% 3.43/1.01  
% 3.43/1.01  ------ QBF
% 3.43/1.01  
% 3.43/1.01  qbf_q_res:                              0
% 3.43/1.01  qbf_num_tautologies:                    0
% 3.43/1.01  qbf_prep_cycles:                        0
% 3.43/1.01  
% 3.43/1.01  ------ BMC1
% 3.43/1.01  
% 3.43/1.01  bmc1_current_bound:                     -1
% 3.43/1.01  bmc1_last_solved_bound:                 -1
% 3.43/1.01  bmc1_unsat_core_size:                   -1
% 3.43/1.01  bmc1_unsat_core_parents_size:           -1
% 3.43/1.01  bmc1_merge_next_fun:                    0
% 3.43/1.01  bmc1_unsat_core_clauses_time:           0.
% 3.43/1.01  
% 3.43/1.01  ------ Instantiation
% 3.43/1.01  
% 3.43/1.01  inst_num_of_clauses:                    907
% 3.43/1.01  inst_num_in_passive:                    219
% 3.43/1.01  inst_num_in_active:                     408
% 3.43/1.01  inst_num_in_unprocessed:                280
% 3.43/1.01  inst_num_of_loops:                      520
% 3.43/1.01  inst_num_of_learning_restarts:          0
% 3.43/1.01  inst_num_moves_active_passive:          109
% 3.43/1.01  inst_lit_activity:                      0
% 3.43/1.01  inst_lit_activity_moves:                0
% 3.43/1.01  inst_num_tautologies:                   0
% 3.43/1.01  inst_num_prop_implied:                  0
% 3.43/1.01  inst_num_existing_simplified:           0
% 3.43/1.01  inst_num_eq_res_simplified:             0
% 3.43/1.01  inst_num_child_elim:                    0
% 3.43/1.01  inst_num_of_dismatching_blockings:      479
% 3.43/1.01  inst_num_of_non_proper_insts:           1411
% 3.43/1.01  inst_num_of_duplicates:                 0
% 3.43/1.01  inst_inst_num_from_inst_to_res:         0
% 3.43/1.01  inst_dismatching_checking_time:         0.
% 3.43/1.01  
% 3.43/1.01  ------ Resolution
% 3.43/1.01  
% 3.43/1.01  res_num_of_clauses:                     0
% 3.43/1.01  res_num_in_passive:                     0
% 3.43/1.01  res_num_in_active:                      0
% 3.43/1.01  res_num_of_loops:                       139
% 3.43/1.01  res_forward_subset_subsumed:            202
% 3.43/1.01  res_backward_subset_subsumed:           0
% 3.43/1.01  res_forward_subsumed:                   0
% 3.43/1.01  res_backward_subsumed:                  0
% 3.43/1.01  res_forward_subsumption_resolution:     2
% 3.43/1.01  res_backward_subsumption_resolution:    0
% 3.43/1.01  res_clause_to_clause_subsumption:       2921
% 3.43/1.01  res_orphan_elimination:                 0
% 3.43/1.01  res_tautology_del:                      140
% 3.43/1.01  res_num_eq_res_simplified:              0
% 3.43/1.01  res_num_sel_changes:                    0
% 3.43/1.01  res_moves_from_active_to_pass:          0
% 3.43/1.01  
% 3.43/1.01  ------ Superposition
% 3.43/1.01  
% 3.43/1.01  sup_time_total:                         0.
% 3.43/1.01  sup_time_generating:                    0.
% 3.43/1.01  sup_time_sim_full:                      0.
% 3.43/1.01  sup_time_sim_immed:                     0.
% 3.43/1.01  
% 3.43/1.01  sup_num_of_clauses:                     444
% 3.43/1.01  sup_num_in_active:                      90
% 3.43/1.01  sup_num_in_passive:                     354
% 3.43/1.01  sup_num_of_loops:                       102
% 3.43/1.01  sup_fw_superposition:                   476
% 3.43/1.01  sup_bw_superposition:                   706
% 3.43/1.01  sup_immediate_simplified:               549
% 3.43/1.01  sup_given_eliminated:                   7
% 3.43/1.01  comparisons_done:                       0
% 3.43/1.01  comparisons_avoided:                    0
% 3.43/1.01  
% 3.43/1.01  ------ Simplifications
% 3.43/1.01  
% 3.43/1.01  
% 3.43/1.01  sim_fw_subset_subsumed:                 4
% 3.43/1.01  sim_bw_subset_subsumed:                 0
% 3.43/1.01  sim_fw_subsumed:                        93
% 3.43/1.01  sim_bw_subsumed:                        1
% 3.43/1.01  sim_fw_subsumption_res:                 0
% 3.43/1.01  sim_bw_subsumption_res:                 0
% 3.43/1.01  sim_tautology_del:                      4
% 3.43/1.01  sim_eq_tautology_del:                   210
% 3.43/1.01  sim_eq_res_simp:                        0
% 3.43/1.01  sim_fw_demodulated:                     298
% 3.43/1.01  sim_bw_demodulated:                     54
% 3.43/1.01  sim_light_normalised:                   303
% 3.43/1.01  sim_joinable_taut:                      0
% 3.43/1.01  sim_joinable_simp:                      0
% 3.43/1.01  sim_ac_normalised:                      0
% 3.43/1.01  sim_smt_subsumption:                    0
% 3.43/1.01  
%------------------------------------------------------------------------------
