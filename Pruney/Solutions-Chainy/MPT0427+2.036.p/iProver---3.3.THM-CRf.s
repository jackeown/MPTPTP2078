%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n001.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 11:42:33 EST 2020

% Result     : Theorem 2.59s
% Output     : CNFRefutation 2.59s
% Verified   : 
% Statistics : Number of formulae       :  116 ( 555 expanded)
%              Number of clauses        :   64 ( 198 expanded)
%              Number of leaves         :   15 ( 126 expanded)
%              Depth                    :   23
%              Number of atoms          :  266 (1742 expanded)
%              Number of equality atoms :  122 ( 439 expanded)
%              Maximal formula depth    :    8 (   4 average)
%              Maximal clause size      :    8 (   2 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f11,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
     => ( r1_tarski(k1_setfam_1(X1),k1_setfam_1(X0))
        | k1_xboole_0 = X0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f21,plain,(
    ! [X0,X1] :
      ( r1_tarski(k1_setfam_1(X1),k1_setfam_1(X0))
      | k1_xboole_0 = X0
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f22,plain,(
    ! [X0,X1] :
      ( r1_tarski(k1_setfam_1(X1),k1_setfam_1(X0))
      | k1_xboole_0 = X0
      | ~ r1_tarski(X0,X1) ) ),
    inference(flattening,[],[f21])).

fof(f53,plain,(
    ! [X0,X1] :
      ( r1_tarski(k1_setfam_1(X1),k1_setfam_1(X0))
      | k1_xboole_0 = X0
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f12,conjecture,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0)))
     => ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(X0)))
         => ( r1_tarski(X1,X2)
           => r1_tarski(k8_setfam_1(X0,X2),k8_setfam_1(X0,X1)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f13,negated_conjecture,(
    ~ ! [X0,X1] :
        ( m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0)))
       => ! [X2] :
            ( m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(X0)))
           => ( r1_tarski(X1,X2)
             => r1_tarski(k8_setfam_1(X0,X2),k8_setfam_1(X0,X1)) ) ) ) ),
    inference(negated_conjecture,[],[f12])).

fof(f23,plain,(
    ? [X0,X1] :
      ( ? [X2] :
          ( ~ r1_tarski(k8_setfam_1(X0,X2),k8_setfam_1(X0,X1))
          & r1_tarski(X1,X2)
          & m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(X0))) )
      & m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f24,plain,(
    ? [X0,X1] :
      ( ? [X2] :
          ( ~ r1_tarski(k8_setfam_1(X0,X2),k8_setfam_1(X0,X1))
          & r1_tarski(X1,X2)
          & m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(X0))) )
      & m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) ) ),
    inference(flattening,[],[f23])).

fof(f35,plain,(
    ! [X0,X1] :
      ( ? [X2] :
          ( ~ r1_tarski(k8_setfam_1(X0,X2),k8_setfam_1(X0,X1))
          & r1_tarski(X1,X2)
          & m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(X0))) )
     => ( ~ r1_tarski(k8_setfam_1(X0,sK4),k8_setfam_1(X0,X1))
        & r1_tarski(X1,sK4)
        & m1_subset_1(sK4,k1_zfmisc_1(k1_zfmisc_1(X0))) ) ) ),
    introduced(choice_axiom,[])).

fof(f34,plain,
    ( ? [X0,X1] :
        ( ? [X2] :
            ( ~ r1_tarski(k8_setfam_1(X0,X2),k8_setfam_1(X0,X1))
            & r1_tarski(X1,X2)
            & m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(X0))) )
        & m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) )
   => ( ? [X2] :
          ( ~ r1_tarski(k8_setfam_1(sK2,X2),k8_setfam_1(sK2,sK3))
          & r1_tarski(sK3,X2)
          & m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(sK2))) )
      & m1_subset_1(sK3,k1_zfmisc_1(k1_zfmisc_1(sK2))) ) ),
    introduced(choice_axiom,[])).

fof(f36,plain,
    ( ~ r1_tarski(k8_setfam_1(sK2,sK4),k8_setfam_1(sK2,sK3))
    & r1_tarski(sK3,sK4)
    & m1_subset_1(sK4,k1_zfmisc_1(k1_zfmisc_1(sK2)))
    & m1_subset_1(sK3,k1_zfmisc_1(k1_zfmisc_1(sK2))) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2,sK3,sK4])],[f24,f35,f34])).

fof(f55,plain,(
    m1_subset_1(sK4,k1_zfmisc_1(k1_zfmisc_1(sK2))) ),
    inference(cnf_transformation,[],[f36])).

fof(f6,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0)))
     => ( ( k1_xboole_0 = X1
         => k8_setfam_1(X0,X1) = X0 )
        & ( k1_xboole_0 != X1
         => k8_setfam_1(X0,X1) = k6_setfam_1(X0,X1) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f16,plain,(
    ! [X0,X1] :
      ( ( ( k8_setfam_1(X0,X1) = X0
          | k1_xboole_0 != X1 )
        & ( k8_setfam_1(X0,X1) = k6_setfam_1(X0,X1)
          | k1_xboole_0 = X1 ) )
      | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f46,plain,(
    ! [X0,X1] :
      ( k8_setfam_1(X0,X1) = k6_setfam_1(X0,X1)
      | k1_xboole_0 = X1
      | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) ) ),
    inference(cnf_transformation,[],[f16])).

fof(f8,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0)))
     => k6_setfam_1(X0,X1) = k1_setfam_1(X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f18,plain,(
    ! [X0,X1] :
      ( k6_setfam_1(X0,X1) = k1_setfam_1(X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f49,plain,(
    ! [X0,X1] :
      ( k6_setfam_1(X0,X1) = k1_setfam_1(X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f54,plain,(
    m1_subset_1(sK3,k1_zfmisc_1(k1_zfmisc_1(sK2))) ),
    inference(cnf_transformation,[],[f36])).

fof(f57,plain,(
    ~ r1_tarski(k8_setfam_1(sK2,sK4),k8_setfam_1(sK2,sK3)) ),
    inference(cnf_transformation,[],[f36])).

fof(f56,plain,(
    r1_tarski(sK3,sK4) ),
    inference(cnf_transformation,[],[f36])).

fof(f47,plain,(
    ! [X0,X1] :
      ( k8_setfam_1(X0,X1) = X0
      | k1_xboole_0 != X1
      | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) ) ),
    inference(cnf_transformation,[],[f16])).

fof(f60,plain,(
    ! [X0] :
      ( k8_setfam_1(X0,k1_xboole_0) = X0
      | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_zfmisc_1(X0))) ) ),
    inference(equality_resolution,[],[f47])).

fof(f5,axiom,(
    ! [X0] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f45,plain,(
    ! [X0] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0)) ),
    inference(cnf_transformation,[],[f5])).

fof(f7,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0)))
     => m1_subset_1(k8_setfam_1(X0,X1),k1_zfmisc_1(X0)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f17,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k8_setfam_1(X0,X1),k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f48,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k8_setfam_1(X0,X1),k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f9,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f33,plain,(
    ! [X0,X1] :
      ( ( m1_subset_1(X0,k1_zfmisc_1(X1))
        | ~ r1_tarski(X0,X1) )
      & ( r1_tarski(X0,X1)
        | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ) ) ),
    inference(nnf_transformation,[],[f9])).

fof(f50,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ) ),
    inference(cnf_transformation,[],[f33])).

fof(f2,axiom,(
    ! [X0] :
      ~ ( ! [X1] : ~ r2_hidden(X1,X0)
        & k1_xboole_0 != X0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f15,plain,(
    ! [X0] :
      ( ? [X1] : r2_hidden(X1,X0)
      | k1_xboole_0 = X0 ) ),
    inference(ennf_transformation,[],[f2])).

fof(f29,plain,(
    ! [X0] :
      ( ? [X1] : r2_hidden(X1,X0)
     => r2_hidden(sK1(X0),X0) ) ),
    introduced(choice_axiom,[])).

fof(f30,plain,(
    ! [X0] :
      ( r2_hidden(sK1(X0),X0)
      | k1_xboole_0 = X0 ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1])],[f15,f29])).

fof(f40,plain,(
    ! [X0] :
      ( r2_hidden(sK1(X0),X0)
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f30])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
    <=> ! [X2] :
          ( r2_hidden(X2,X0)
         => r2_hidden(X2,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f14,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
          | ~ r2_hidden(X2,X0) ) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f25,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ? [X2] :
            ( ~ r2_hidden(X2,X1)
            & r2_hidden(X2,X0) ) )
      & ( ! [X2] :
            ( r2_hidden(X2,X1)
            | ~ r2_hidden(X2,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(nnf_transformation,[],[f14])).

fof(f26,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ? [X2] :
            ( ~ r2_hidden(X2,X1)
            & r2_hidden(X2,X0) ) )
      & ( ! [X3] :
            ( r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(rectify,[],[f25])).

fof(f27,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ~ r2_hidden(X2,X1)
          & r2_hidden(X2,X0) )
     => ( ~ r2_hidden(sK0(X0,X1),X1)
        & r2_hidden(sK0(X0,X1),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f28,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ( ~ r2_hidden(sK0(X0,X1),X1)
          & r2_hidden(sK0(X0,X1),X0) ) )
      & ( ! [X3] :
            ( r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f26,f27])).

fof(f37,plain,(
    ! [X0,X3,X1] :
      ( r2_hidden(X3,X1)
      | ~ r2_hidden(X3,X0)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
    <=> ( k1_xboole_0 = X1
        | k1_xboole_0 = X0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f31,plain,(
    ! [X0,X1] :
      ( ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
        | ( k1_xboole_0 != X1
          & k1_xboole_0 != X0 ) )
      & ( k1_xboole_0 = X1
        | k1_xboole_0 = X0
        | k1_xboole_0 != k2_zfmisc_1(X0,X1) ) ) ),
    inference(nnf_transformation,[],[f3])).

fof(f32,plain,(
    ! [X0,X1] :
      ( ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
        | ( k1_xboole_0 != X1
          & k1_xboole_0 != X0 ) )
      & ( k1_xboole_0 = X1
        | k1_xboole_0 = X0
        | k1_xboole_0 != k2_zfmisc_1(X0,X1) ) ) ),
    inference(flattening,[],[f31])).

fof(f43,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
      | k1_xboole_0 != X1 ) ),
    inference(cnf_transformation,[],[f32])).

fof(f58,plain,(
    ! [X0] : k1_xboole_0 = k2_zfmisc_1(X0,k1_xboole_0) ),
    inference(equality_resolution,[],[f43])).

fof(f4,axiom,(
    ! [X0,X1] : ~ r2_hidden(X0,k2_zfmisc_1(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f44,plain,(
    ! [X0,X1] : ~ r2_hidden(X0,k2_zfmisc_1(X0,X1)) ),
    inference(cnf_transformation,[],[f4])).

fof(f38,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | r2_hidden(sK0(X0,X1),X0) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f39,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | ~ r2_hidden(sK0(X0,X1),X1) ) ),
    inference(cnf_transformation,[],[f28])).

cnf(c_16,plain,
    ( ~ r1_tarski(X0,X1)
    | r1_tarski(k1_setfam_1(X1),k1_setfam_1(X0))
    | k1_xboole_0 = X0 ),
    inference(cnf_transformation,[],[f53])).

cnf(c_678,plain,
    ( k1_xboole_0 = X0
    | r1_tarski(X0,X1) != iProver_top
    | r1_tarski(k1_setfam_1(X1),k1_setfam_1(X0)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_16])).

cnf(c_19,negated_conjecture,
    ( m1_subset_1(sK4,k1_zfmisc_1(k1_zfmisc_1(sK2))) ),
    inference(cnf_transformation,[],[f55])).

cnf(c_675,plain,
    ( m1_subset_1(sK4,k1_zfmisc_1(k1_zfmisc_1(sK2))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_19])).

cnf(c_10,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k1_zfmisc_1(X1)))
    | k6_setfam_1(X1,X0) = k8_setfam_1(X1,X0)
    | k1_xboole_0 = X0 ),
    inference(cnf_transformation,[],[f46])).

cnf(c_684,plain,
    ( k6_setfam_1(X0,X1) = k8_setfam_1(X0,X1)
    | k1_xboole_0 = X1
    | m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_10])).

cnf(c_2165,plain,
    ( k6_setfam_1(sK2,sK4) = k8_setfam_1(sK2,sK4)
    | sK4 = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_675,c_684])).

cnf(c_12,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k1_zfmisc_1(X1)))
    | k6_setfam_1(X1,X0) = k1_setfam_1(X0) ),
    inference(cnf_transformation,[],[f49])).

cnf(c_682,plain,
    ( k6_setfam_1(X0,X1) = k1_setfam_1(X1)
    | m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_12])).

cnf(c_1437,plain,
    ( k6_setfam_1(sK2,sK4) = k1_setfam_1(sK4) ),
    inference(superposition,[status(thm)],[c_675,c_682])).

cnf(c_2174,plain,
    ( k8_setfam_1(sK2,sK4) = k1_setfam_1(sK4)
    | sK4 = k1_xboole_0 ),
    inference(light_normalisation,[status(thm)],[c_2165,c_1437])).

cnf(c_20,negated_conjecture,
    ( m1_subset_1(sK3,k1_zfmisc_1(k1_zfmisc_1(sK2))) ),
    inference(cnf_transformation,[],[f54])).

cnf(c_674,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(k1_zfmisc_1(sK2))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_20])).

cnf(c_2166,plain,
    ( k6_setfam_1(sK2,sK3) = k8_setfam_1(sK2,sK3)
    | sK3 = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_674,c_684])).

cnf(c_1438,plain,
    ( k6_setfam_1(sK2,sK3) = k1_setfam_1(sK3) ),
    inference(superposition,[status(thm)],[c_674,c_682])).

cnf(c_2169,plain,
    ( k8_setfam_1(sK2,sK3) = k1_setfam_1(sK3)
    | sK3 = k1_xboole_0 ),
    inference(light_normalisation,[status(thm)],[c_2166,c_1438])).

cnf(c_17,negated_conjecture,
    ( ~ r1_tarski(k8_setfam_1(sK2,sK4),k8_setfam_1(sK2,sK3)) ),
    inference(cnf_transformation,[],[f57])).

cnf(c_677,plain,
    ( r1_tarski(k8_setfam_1(sK2,sK4),k8_setfam_1(sK2,sK3)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_17])).

cnf(c_2344,plain,
    ( sK3 = k1_xboole_0
    | r1_tarski(k8_setfam_1(sK2,sK4),k1_setfam_1(sK3)) != iProver_top ),
    inference(superposition,[status(thm)],[c_2169,c_677])).

cnf(c_2472,plain,
    ( sK3 = k1_xboole_0
    | sK4 = k1_xboole_0
    | r1_tarski(k1_setfam_1(sK4),k1_setfam_1(sK3)) != iProver_top ),
    inference(superposition,[status(thm)],[c_2174,c_2344])).

cnf(c_2596,plain,
    ( sK3 = k1_xboole_0
    | sK4 = k1_xboole_0
    | r1_tarski(sK3,sK4) != iProver_top ),
    inference(superposition,[status(thm)],[c_678,c_2472])).

cnf(c_18,negated_conjecture,
    ( r1_tarski(sK3,sK4) ),
    inference(cnf_transformation,[],[f56])).

cnf(c_2597,plain,
    ( ~ r1_tarski(sK3,sK4)
    | sK3 = k1_xboole_0
    | sK4 = k1_xboole_0 ),
    inference(predicate_to_equality_rev,[status(thm)],[c_2596])).

cnf(c_2746,plain,
    ( sK4 = k1_xboole_0
    | sK3 = k1_xboole_0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_2596,c_18,c_2597])).

cnf(c_2747,plain,
    ( sK3 = k1_xboole_0
    | sK4 = k1_xboole_0 ),
    inference(renaming,[status(thm)],[c_2746])).

cnf(c_2758,plain,
    ( sK4 = k1_xboole_0
    | r1_tarski(k8_setfam_1(sK2,sK4),k8_setfam_1(sK2,k1_xboole_0)) != iProver_top ),
    inference(superposition,[status(thm)],[c_2747,c_677])).

cnf(c_9,plain,
    ( ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_zfmisc_1(X0)))
    | k8_setfam_1(X0,k1_xboole_0) = X0 ),
    inference(cnf_transformation,[],[f60])).

cnf(c_685,plain,
    ( k8_setfam_1(X0,k1_xboole_0) = X0
    | m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_zfmisc_1(X0))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_9])).

cnf(c_8,plain,
    ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0)) ),
    inference(cnf_transformation,[],[f45])).

cnf(c_686,plain,
    ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_8])).

cnf(c_726,plain,
    ( k8_setfam_1(X0,k1_xboole_0) = X0 ),
    inference(forward_subsumption_resolution,[status(thm)],[c_685,c_686])).

cnf(c_2767,plain,
    ( sK4 = k1_xboole_0
    | r1_tarski(k8_setfam_1(sK2,sK4),sK2) != iProver_top ),
    inference(demodulation,[status(thm)],[c_2758,c_726])).

cnf(c_22,plain,
    ( m1_subset_1(sK4,k1_zfmisc_1(k1_zfmisc_1(sK2))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_19])).

cnf(c_11,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k1_zfmisc_1(X1)))
    | m1_subset_1(k8_setfam_1(X1,X0),k1_zfmisc_1(X1)) ),
    inference(cnf_transformation,[],[f48])).

cnf(c_833,plain,
    ( m1_subset_1(k8_setfam_1(sK2,sK4),k1_zfmisc_1(sK2))
    | ~ m1_subset_1(sK4,k1_zfmisc_1(k1_zfmisc_1(sK2))) ),
    inference(instantiation,[status(thm)],[c_11])).

cnf(c_834,plain,
    ( m1_subset_1(k8_setfam_1(sK2,sK4),k1_zfmisc_1(sK2)) = iProver_top
    | m1_subset_1(sK4,k1_zfmisc_1(k1_zfmisc_1(sK2))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_833])).

cnf(c_14,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | r1_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f50])).

cnf(c_963,plain,
    ( ~ m1_subset_1(k8_setfam_1(sK2,sK4),k1_zfmisc_1(X0))
    | r1_tarski(k8_setfam_1(sK2,sK4),X0) ),
    inference(instantiation,[status(thm)],[c_14])).

cnf(c_1286,plain,
    ( ~ m1_subset_1(k8_setfam_1(sK2,sK4),k1_zfmisc_1(sK2))
    | r1_tarski(k8_setfam_1(sK2,sK4),sK2) ),
    inference(instantiation,[status(thm)],[c_963])).

cnf(c_1287,plain,
    ( m1_subset_1(k8_setfam_1(sK2,sK4),k1_zfmisc_1(sK2)) != iProver_top
    | r1_tarski(k8_setfam_1(sK2,sK4),sK2) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1286])).

cnf(c_2873,plain,
    ( sK4 = k1_xboole_0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_2767,c_22,c_834,c_1287])).

cnf(c_676,plain,
    ( r1_tarski(sK3,sK4) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_18])).

cnf(c_2886,plain,
    ( r1_tarski(sK3,k1_xboole_0) = iProver_top ),
    inference(demodulation,[status(thm)],[c_2873,c_676])).

cnf(c_3,plain,
    ( r2_hidden(sK1(X0),X0)
    | k1_xboole_0 = X0 ),
    inference(cnf_transformation,[],[f40])).

cnf(c_688,plain,
    ( k1_xboole_0 = X0
    | r2_hidden(sK1(X0),X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3])).

cnf(c_2,plain,
    ( ~ r2_hidden(X0,X1)
    | r2_hidden(X0,X2)
    | ~ r1_tarski(X1,X2) ),
    inference(cnf_transformation,[],[f37])).

cnf(c_689,plain,
    ( r2_hidden(X0,X1) != iProver_top
    | r2_hidden(X0,X2) = iProver_top
    | r1_tarski(X1,X2) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2])).

cnf(c_1742,plain,
    ( k1_xboole_0 = X0
    | r2_hidden(sK1(X0),X1) = iProver_top
    | r1_tarski(X0,X1) != iProver_top ),
    inference(superposition,[status(thm)],[c_688,c_689])).

cnf(c_4,plain,
    ( k2_zfmisc_1(X0,k1_xboole_0) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f58])).

cnf(c_7,plain,
    ( ~ r2_hidden(X0,k2_zfmisc_1(X0,X1)) ),
    inference(cnf_transformation,[],[f44])).

cnf(c_687,plain,
    ( r2_hidden(X0,k2_zfmisc_1(X0,X1)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_7])).

cnf(c_1119,plain,
    ( r2_hidden(X0,k1_xboole_0) != iProver_top ),
    inference(superposition,[status(thm)],[c_4,c_687])).

cnf(c_4317,plain,
    ( k1_xboole_0 = X0
    | r1_tarski(X0,k1_xboole_0) != iProver_top ),
    inference(superposition,[status(thm)],[c_1742,c_1119])).

cnf(c_4937,plain,
    ( sK3 = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_2886,c_4317])).

cnf(c_2884,plain,
    ( r1_tarski(k8_setfam_1(sK2,k1_xboole_0),k8_setfam_1(sK2,sK3)) != iProver_top ),
    inference(demodulation,[status(thm)],[c_2873,c_677])).

cnf(c_2891,plain,
    ( r1_tarski(sK2,k8_setfam_1(sK2,sK3)) != iProver_top ),
    inference(demodulation,[status(thm)],[c_2884,c_726])).

cnf(c_5208,plain,
    ( r1_tarski(sK2,k8_setfam_1(sK2,k1_xboole_0)) != iProver_top ),
    inference(demodulation,[status(thm)],[c_4937,c_2891])).

cnf(c_5220,plain,
    ( r1_tarski(sK2,sK2) != iProver_top ),
    inference(demodulation,[status(thm)],[c_5208,c_726])).

cnf(c_1,plain,
    ( r2_hidden(sK0(X0,X1),X0)
    | r1_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f38])).

cnf(c_690,plain,
    ( r2_hidden(sK0(X0,X1),X0) = iProver_top
    | r1_tarski(X0,X1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1])).

cnf(c_0,plain,
    ( ~ r2_hidden(sK0(X0,X1),X1)
    | r1_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f39])).

cnf(c_691,plain,
    ( r2_hidden(sK0(X0,X1),X1) != iProver_top
    | r1_tarski(X0,X1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_0])).

cnf(c_1597,plain,
    ( r1_tarski(X0,X0) = iProver_top ),
    inference(superposition,[status(thm)],[c_690,c_691])).

cnf(c_5235,plain,
    ( $false ),
    inference(forward_subsumption_resolution,[status(thm)],[c_5220,c_1597])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : iproveropt_run.sh %d %s
% 0.12/0.33  % Computer   : n001.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.33  % CPULimit   : 60
% 0.12/0.33  % WCLimit    : 600
% 0.12/0.33  % DateTime   : Tue Dec  1 18:11:45 EST 2020
% 0.12/0.33  % CPUTime    : 
% 0.12/0.34  % Running in FOF mode
% 2.59/0.94  % SZS status Started for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.59/0.94  
% 2.59/0.94  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 2.59/0.94  
% 2.59/0.94  ------  iProver source info
% 2.59/0.94  
% 2.59/0.94  git: date: 2020-06-30 10:37:57 +0100
% 2.59/0.94  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 2.59/0.94  git: non_committed_changes: false
% 2.59/0.94  git: last_make_outside_of_git: false
% 2.59/0.94  
% 2.59/0.94  ------ 
% 2.59/0.94  
% 2.59/0.94  ------ Input Options
% 2.59/0.94  
% 2.59/0.94  --out_options                           all
% 2.59/0.94  --tptp_safe_out                         true
% 2.59/0.94  --problem_path                          ""
% 2.59/0.94  --include_path                          ""
% 2.59/0.94  --clausifier                            res/vclausify_rel
% 2.59/0.94  --clausifier_options                    --mode clausify
% 2.59/0.94  --stdin                                 false
% 2.59/0.94  --stats_out                             all
% 2.59/0.94  
% 2.59/0.94  ------ General Options
% 2.59/0.94  
% 2.59/0.94  --fof                                   false
% 2.59/0.94  --time_out_real                         305.
% 2.59/0.94  --time_out_virtual                      -1.
% 2.59/0.94  --symbol_type_check                     false
% 2.59/0.94  --clausify_out                          false
% 2.59/0.94  --sig_cnt_out                           false
% 2.59/0.94  --trig_cnt_out                          false
% 2.59/0.94  --trig_cnt_out_tolerance                1.
% 2.59/0.94  --trig_cnt_out_sk_spl                   false
% 2.59/0.94  --abstr_cl_out                          false
% 2.59/0.94  
% 2.59/0.94  ------ Global Options
% 2.59/0.94  
% 2.59/0.94  --schedule                              default
% 2.59/0.94  --add_important_lit                     false
% 2.59/0.94  --prop_solver_per_cl                    1000
% 2.59/0.94  --min_unsat_core                        false
% 2.59/0.94  --soft_assumptions                      false
% 2.59/0.94  --soft_lemma_size                       3
% 2.59/0.94  --prop_impl_unit_size                   0
% 2.59/0.94  --prop_impl_unit                        []
% 2.59/0.94  --share_sel_clauses                     true
% 2.59/0.94  --reset_solvers                         false
% 2.59/0.94  --bc_imp_inh                            [conj_cone]
% 2.59/0.94  --conj_cone_tolerance                   3.
% 2.59/0.94  --extra_neg_conj                        none
% 2.59/0.94  --large_theory_mode                     true
% 2.59/0.94  --prolific_symb_bound                   200
% 2.59/0.94  --lt_threshold                          2000
% 2.59/0.94  --clause_weak_htbl                      true
% 2.59/0.94  --gc_record_bc_elim                     false
% 2.59/0.94  
% 2.59/0.94  ------ Preprocessing Options
% 2.59/0.94  
% 2.59/0.94  --preprocessing_flag                    true
% 2.59/0.94  --time_out_prep_mult                    0.1
% 2.59/0.94  --splitting_mode                        input
% 2.59/0.94  --splitting_grd                         true
% 2.59/0.94  --splitting_cvd                         false
% 2.59/0.94  --splitting_cvd_svl                     false
% 2.59/0.94  --splitting_nvd                         32
% 2.59/0.94  --sub_typing                            true
% 2.59/0.94  --prep_gs_sim                           true
% 2.59/0.94  --prep_unflatten                        true
% 2.59/0.94  --prep_res_sim                          true
% 2.59/0.94  --prep_upred                            true
% 2.59/0.94  --prep_sem_filter                       exhaustive
% 2.59/0.94  --prep_sem_filter_out                   false
% 2.59/0.94  --pred_elim                             true
% 2.59/0.94  --res_sim_input                         true
% 2.59/0.94  --eq_ax_congr_red                       true
% 2.59/0.94  --pure_diseq_elim                       true
% 2.59/0.94  --brand_transform                       false
% 2.59/0.94  --non_eq_to_eq                          false
% 2.59/0.94  --prep_def_merge                        true
% 2.59/0.94  --prep_def_merge_prop_impl              false
% 2.59/0.94  --prep_def_merge_mbd                    true
% 2.59/0.94  --prep_def_merge_tr_red                 false
% 2.59/0.94  --prep_def_merge_tr_cl                  false
% 2.59/0.94  --smt_preprocessing                     true
% 2.59/0.94  --smt_ac_axioms                         fast
% 2.59/0.94  --preprocessed_out                      false
% 2.59/0.94  --preprocessed_stats                    false
% 2.59/0.94  
% 2.59/0.94  ------ Abstraction refinement Options
% 2.59/0.94  
% 2.59/0.94  --abstr_ref                             []
% 2.59/0.94  --abstr_ref_prep                        false
% 2.59/0.94  --abstr_ref_until_sat                   false
% 2.59/0.94  --abstr_ref_sig_restrict                funpre
% 2.59/0.94  --abstr_ref_af_restrict_to_split_sk     false
% 2.59/0.94  --abstr_ref_under                       []
% 2.59/0.94  
% 2.59/0.94  ------ SAT Options
% 2.59/0.94  
% 2.59/0.94  --sat_mode                              false
% 2.59/0.94  --sat_fm_restart_options                ""
% 2.59/0.94  --sat_gr_def                            false
% 2.59/0.94  --sat_epr_types                         true
% 2.59/0.94  --sat_non_cyclic_types                  false
% 2.59/0.94  --sat_finite_models                     false
% 2.59/0.94  --sat_fm_lemmas                         false
% 2.59/0.94  --sat_fm_prep                           false
% 2.59/0.94  --sat_fm_uc_incr                        true
% 2.59/0.94  --sat_out_model                         small
% 2.59/0.94  --sat_out_clauses                       false
% 2.59/0.94  
% 2.59/0.94  ------ QBF Options
% 2.59/0.94  
% 2.59/0.94  --qbf_mode                              false
% 2.59/0.94  --qbf_elim_univ                         false
% 2.59/0.94  --qbf_dom_inst                          none
% 2.59/0.94  --qbf_dom_pre_inst                      false
% 2.59/0.94  --qbf_sk_in                             false
% 2.59/0.94  --qbf_pred_elim                         true
% 2.59/0.94  --qbf_split                             512
% 2.59/0.94  
% 2.59/0.94  ------ BMC1 Options
% 2.59/0.94  
% 2.59/0.94  --bmc1_incremental                      false
% 2.59/0.94  --bmc1_axioms                           reachable_all
% 2.59/0.94  --bmc1_min_bound                        0
% 2.59/0.94  --bmc1_max_bound                        -1
% 2.59/0.94  --bmc1_max_bound_default                -1
% 2.59/0.94  --bmc1_symbol_reachability              true
% 2.59/0.94  --bmc1_property_lemmas                  false
% 2.59/0.94  --bmc1_k_induction                      false
% 2.59/0.94  --bmc1_non_equiv_states                 false
% 2.59/0.94  --bmc1_deadlock                         false
% 2.59/0.94  --bmc1_ucm                              false
% 2.59/0.94  --bmc1_add_unsat_core                   none
% 2.59/0.94  --bmc1_unsat_core_children              false
% 2.59/0.94  --bmc1_unsat_core_extrapolate_axioms    false
% 2.59/0.94  --bmc1_out_stat                         full
% 2.59/0.94  --bmc1_ground_init                      false
% 2.59/0.94  --bmc1_pre_inst_next_state              false
% 2.59/0.94  --bmc1_pre_inst_state                   false
% 2.59/0.94  --bmc1_pre_inst_reach_state             false
% 2.59/0.94  --bmc1_out_unsat_core                   false
% 2.59/0.94  --bmc1_aig_witness_out                  false
% 2.59/0.94  --bmc1_verbose                          false
% 2.59/0.94  --bmc1_dump_clauses_tptp                false
% 2.59/0.94  --bmc1_dump_unsat_core_tptp             false
% 2.59/0.94  --bmc1_dump_file                        -
% 2.59/0.94  --bmc1_ucm_expand_uc_limit              128
% 2.59/0.94  --bmc1_ucm_n_expand_iterations          6
% 2.59/0.94  --bmc1_ucm_extend_mode                  1
% 2.59/0.94  --bmc1_ucm_init_mode                    2
% 2.59/0.94  --bmc1_ucm_cone_mode                    none
% 2.59/0.94  --bmc1_ucm_reduced_relation_type        0
% 2.59/0.94  --bmc1_ucm_relax_model                  4
% 2.59/0.94  --bmc1_ucm_full_tr_after_sat            true
% 2.59/0.94  --bmc1_ucm_expand_neg_assumptions       false
% 2.59/0.94  --bmc1_ucm_layered_model                none
% 2.59/0.94  --bmc1_ucm_max_lemma_size               10
% 2.59/0.94  
% 2.59/0.94  ------ AIG Options
% 2.59/0.94  
% 2.59/0.94  --aig_mode                              false
% 2.59/0.94  
% 2.59/0.94  ------ Instantiation Options
% 2.59/0.94  
% 2.59/0.94  --instantiation_flag                    true
% 2.59/0.94  --inst_sos_flag                         false
% 2.59/0.94  --inst_sos_phase                        true
% 2.59/0.94  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 2.59/0.94  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 2.59/0.94  --inst_lit_sel_side                     num_symb
% 2.59/0.94  --inst_solver_per_active                1400
% 2.59/0.94  --inst_solver_calls_frac                1.
% 2.59/0.94  --inst_passive_queue_type               priority_queues
% 2.59/0.94  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 2.59/0.94  --inst_passive_queues_freq              [25;2]
% 2.59/0.94  --inst_dismatching                      true
% 2.59/0.94  --inst_eager_unprocessed_to_passive     true
% 2.59/0.94  --inst_prop_sim_given                   true
% 2.59/0.94  --inst_prop_sim_new                     false
% 2.59/0.94  --inst_subs_new                         false
% 2.59/0.94  --inst_eq_res_simp                      false
% 2.59/0.94  --inst_subs_given                       false
% 2.59/0.94  --inst_orphan_elimination               true
% 2.59/0.94  --inst_learning_loop_flag               true
% 2.59/0.94  --inst_learning_start                   3000
% 2.59/0.94  --inst_learning_factor                  2
% 2.59/0.94  --inst_start_prop_sim_after_learn       3
% 2.59/0.94  --inst_sel_renew                        solver
% 2.59/0.94  --inst_lit_activity_flag                true
% 2.59/0.94  --inst_restr_to_given                   false
% 2.59/0.94  --inst_activity_threshold               500
% 2.59/0.94  --inst_out_proof                        true
% 2.59/0.94  
% 2.59/0.94  ------ Resolution Options
% 2.59/0.94  
% 2.59/0.94  --resolution_flag                       true
% 2.59/0.94  --res_lit_sel                           adaptive
% 2.59/0.94  --res_lit_sel_side                      none
% 2.59/0.94  --res_ordering                          kbo
% 2.59/0.94  --res_to_prop_solver                    active
% 2.59/0.94  --res_prop_simpl_new                    false
% 2.59/0.94  --res_prop_simpl_given                  true
% 2.59/0.94  --res_passive_queue_type                priority_queues
% 2.59/0.94  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 2.59/0.94  --res_passive_queues_freq               [15;5]
% 2.59/0.94  --res_forward_subs                      full
% 2.59/0.94  --res_backward_subs                     full
% 2.59/0.94  --res_forward_subs_resolution           true
% 2.59/0.94  --res_backward_subs_resolution          true
% 2.59/0.94  --res_orphan_elimination                true
% 2.59/0.94  --res_time_limit                        2.
% 2.59/0.94  --res_out_proof                         true
% 2.59/0.94  
% 2.59/0.94  ------ Superposition Options
% 2.59/0.94  
% 2.59/0.94  --superposition_flag                    true
% 2.59/0.94  --sup_passive_queue_type                priority_queues
% 2.59/0.94  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 2.59/0.94  --sup_passive_queues_freq               [8;1;4]
% 2.59/0.94  --demod_completeness_check              fast
% 2.59/0.94  --demod_use_ground                      true
% 2.59/0.94  --sup_to_prop_solver                    passive
% 2.59/0.94  --sup_prop_simpl_new                    true
% 2.59/0.94  --sup_prop_simpl_given                  true
% 2.59/0.94  --sup_fun_splitting                     false
% 2.59/0.94  --sup_smt_interval                      50000
% 2.59/0.94  
% 2.59/0.94  ------ Superposition Simplification Setup
% 2.59/0.94  
% 2.59/0.94  --sup_indices_passive                   []
% 2.59/0.94  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.59/0.94  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.59/0.94  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.59/0.94  --sup_full_triv                         [TrivRules;PropSubs]
% 2.59/0.94  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.59/0.94  --sup_full_bw                           [BwDemod]
% 2.59/0.94  --sup_immed_triv                        [TrivRules]
% 2.59/0.94  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 2.59/0.94  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.59/0.94  --sup_immed_bw_main                     []
% 2.59/0.94  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.59/0.94  --sup_input_triv                        [Unflattening;TrivRules]
% 2.59/0.94  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.59/0.94  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.59/0.94  
% 2.59/0.94  ------ Combination Options
% 2.59/0.94  
% 2.59/0.94  --comb_res_mult                         3
% 2.59/0.94  --comb_sup_mult                         2
% 2.59/0.94  --comb_inst_mult                        10
% 2.59/0.94  
% 2.59/0.94  ------ Debug Options
% 2.59/0.94  
% 2.59/0.94  --dbg_backtrace                         false
% 2.59/0.94  --dbg_dump_prop_clauses                 false
% 2.59/0.94  --dbg_dump_prop_clauses_file            -
% 2.59/0.94  --dbg_out_stat                          false
% 2.59/0.94  ------ Parsing...
% 2.59/0.94  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 2.59/0.94  
% 2.59/0.94  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe_e 
% 2.59/0.94  
% 2.59/0.94  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 2.59/0.94  
% 2.59/0.94  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 2.59/0.94  ------ Proving...
% 2.59/0.94  ------ Problem Properties 
% 2.59/0.94  
% 2.59/0.94  
% 2.59/0.94  clauses                                 21
% 2.59/0.94  conjectures                             4
% 2.59/0.94  EPR                                     2
% 2.59/0.94  Horn                                    16
% 2.59/0.94  unary                                   8
% 2.59/0.94  binary                                  8
% 2.59/0.94  lits                                    39
% 2.59/0.94  lits eq                                 11
% 2.59/0.94  fd_pure                                 0
% 2.59/0.94  fd_pseudo                               0
% 2.59/0.94  fd_cond                                 4
% 2.59/0.94  fd_pseudo_cond                          0
% 2.59/0.94  AC symbols                              0
% 2.59/0.94  
% 2.59/0.94  ------ Schedule dynamic 5 is on 
% 2.59/0.94  
% 2.59/0.94  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" Time Limit: 10.
% 2.59/0.94  
% 2.59/0.94  
% 2.59/0.94  ------ 
% 2.59/0.94  Current options:
% 2.59/0.94  ------ 
% 2.59/0.94  
% 2.59/0.94  ------ Input Options
% 2.59/0.94  
% 2.59/0.94  --out_options                           all
% 2.59/0.94  --tptp_safe_out                         true
% 2.59/0.94  --problem_path                          ""
% 2.59/0.94  --include_path                          ""
% 2.59/0.94  --clausifier                            res/vclausify_rel
% 2.59/0.94  --clausifier_options                    --mode clausify
% 2.59/0.94  --stdin                                 false
% 2.59/0.94  --stats_out                             all
% 2.59/0.94  
% 2.59/0.94  ------ General Options
% 2.59/0.94  
% 2.59/0.94  --fof                                   false
% 2.59/0.94  --time_out_real                         305.
% 2.59/0.94  --time_out_virtual                      -1.
% 2.59/0.94  --symbol_type_check                     false
% 2.59/0.94  --clausify_out                          false
% 2.59/0.94  --sig_cnt_out                           false
% 2.59/0.94  --trig_cnt_out                          false
% 2.59/0.94  --trig_cnt_out_tolerance                1.
% 2.59/0.94  --trig_cnt_out_sk_spl                   false
% 2.59/0.94  --abstr_cl_out                          false
% 2.59/0.94  
% 2.59/0.94  ------ Global Options
% 2.59/0.94  
% 2.59/0.94  --schedule                              default
% 2.59/0.94  --add_important_lit                     false
% 2.59/0.94  --prop_solver_per_cl                    1000
% 2.59/0.94  --min_unsat_core                        false
% 2.59/0.94  --soft_assumptions                      false
% 2.59/0.94  --soft_lemma_size                       3
% 2.59/0.94  --prop_impl_unit_size                   0
% 2.59/0.94  --prop_impl_unit                        []
% 2.59/0.94  --share_sel_clauses                     true
% 2.59/0.94  --reset_solvers                         false
% 2.59/0.94  --bc_imp_inh                            [conj_cone]
% 2.59/0.94  --conj_cone_tolerance                   3.
% 2.59/0.94  --extra_neg_conj                        none
% 2.59/0.94  --large_theory_mode                     true
% 2.59/0.94  --prolific_symb_bound                   200
% 2.59/0.94  --lt_threshold                          2000
% 2.59/0.94  --clause_weak_htbl                      true
% 2.59/0.94  --gc_record_bc_elim                     false
% 2.59/0.94  
% 2.59/0.94  ------ Preprocessing Options
% 2.59/0.94  
% 2.59/0.94  --preprocessing_flag                    true
% 2.59/0.94  --time_out_prep_mult                    0.1
% 2.59/0.94  --splitting_mode                        input
% 2.59/0.94  --splitting_grd                         true
% 2.59/0.94  --splitting_cvd                         false
% 2.59/0.94  --splitting_cvd_svl                     false
% 2.59/0.94  --splitting_nvd                         32
% 2.59/0.94  --sub_typing                            true
% 2.59/0.94  --prep_gs_sim                           true
% 2.59/0.94  --prep_unflatten                        true
% 2.59/0.94  --prep_res_sim                          true
% 2.59/0.94  --prep_upred                            true
% 2.59/0.94  --prep_sem_filter                       exhaustive
% 2.59/0.94  --prep_sem_filter_out                   false
% 2.59/0.94  --pred_elim                             true
% 2.59/0.94  --res_sim_input                         true
% 2.59/0.94  --eq_ax_congr_red                       true
% 2.59/0.94  --pure_diseq_elim                       true
% 2.59/0.94  --brand_transform                       false
% 2.59/0.94  --non_eq_to_eq                          false
% 2.59/0.94  --prep_def_merge                        true
% 2.59/0.94  --prep_def_merge_prop_impl              false
% 2.59/0.94  --prep_def_merge_mbd                    true
% 2.59/0.94  --prep_def_merge_tr_red                 false
% 2.59/0.94  --prep_def_merge_tr_cl                  false
% 2.59/0.94  --smt_preprocessing                     true
% 2.59/0.94  --smt_ac_axioms                         fast
% 2.59/0.94  --preprocessed_out                      false
% 2.59/0.94  --preprocessed_stats                    false
% 2.59/0.94  
% 2.59/0.94  ------ Abstraction refinement Options
% 2.59/0.94  
% 2.59/0.94  --abstr_ref                             []
% 2.59/0.94  --abstr_ref_prep                        false
% 2.59/0.94  --abstr_ref_until_sat                   false
% 2.59/0.94  --abstr_ref_sig_restrict                funpre
% 2.59/0.94  --abstr_ref_af_restrict_to_split_sk     false
% 2.59/0.94  --abstr_ref_under                       []
% 2.59/0.94  
% 2.59/0.94  ------ SAT Options
% 2.59/0.94  
% 2.59/0.94  --sat_mode                              false
% 2.59/0.94  --sat_fm_restart_options                ""
% 2.59/0.94  --sat_gr_def                            false
% 2.59/0.94  --sat_epr_types                         true
% 2.59/0.94  --sat_non_cyclic_types                  false
% 2.59/0.94  --sat_finite_models                     false
% 2.59/0.94  --sat_fm_lemmas                         false
% 2.59/0.94  --sat_fm_prep                           false
% 2.59/0.94  --sat_fm_uc_incr                        true
% 2.59/0.94  --sat_out_model                         small
% 2.59/0.94  --sat_out_clauses                       false
% 2.59/0.94  
% 2.59/0.94  ------ QBF Options
% 2.59/0.94  
% 2.59/0.94  --qbf_mode                              false
% 2.59/0.94  --qbf_elim_univ                         false
% 2.59/0.94  --qbf_dom_inst                          none
% 2.59/0.94  --qbf_dom_pre_inst                      false
% 2.59/0.94  --qbf_sk_in                             false
% 2.59/0.94  --qbf_pred_elim                         true
% 2.59/0.94  --qbf_split                             512
% 2.59/0.94  
% 2.59/0.94  ------ BMC1 Options
% 2.59/0.94  
% 2.59/0.94  --bmc1_incremental                      false
% 2.59/0.94  --bmc1_axioms                           reachable_all
% 2.59/0.94  --bmc1_min_bound                        0
% 2.59/0.94  --bmc1_max_bound                        -1
% 2.59/0.94  --bmc1_max_bound_default                -1
% 2.59/0.94  --bmc1_symbol_reachability              true
% 2.59/0.94  --bmc1_property_lemmas                  false
% 2.59/0.94  --bmc1_k_induction                      false
% 2.59/0.94  --bmc1_non_equiv_states                 false
% 2.59/0.94  --bmc1_deadlock                         false
% 2.59/0.94  --bmc1_ucm                              false
% 2.59/0.94  --bmc1_add_unsat_core                   none
% 2.59/0.94  --bmc1_unsat_core_children              false
% 2.59/0.94  --bmc1_unsat_core_extrapolate_axioms    false
% 2.59/0.94  --bmc1_out_stat                         full
% 2.59/0.94  --bmc1_ground_init                      false
% 2.59/0.94  --bmc1_pre_inst_next_state              false
% 2.59/0.94  --bmc1_pre_inst_state                   false
% 2.59/0.94  --bmc1_pre_inst_reach_state             false
% 2.59/0.94  --bmc1_out_unsat_core                   false
% 2.59/0.94  --bmc1_aig_witness_out                  false
% 2.59/0.94  --bmc1_verbose                          false
% 2.59/0.94  --bmc1_dump_clauses_tptp                false
% 2.59/0.94  --bmc1_dump_unsat_core_tptp             false
% 2.59/0.94  --bmc1_dump_file                        -
% 2.59/0.94  --bmc1_ucm_expand_uc_limit              128
% 2.59/0.94  --bmc1_ucm_n_expand_iterations          6
% 2.59/0.94  --bmc1_ucm_extend_mode                  1
% 2.59/0.94  --bmc1_ucm_init_mode                    2
% 2.59/0.94  --bmc1_ucm_cone_mode                    none
% 2.59/0.94  --bmc1_ucm_reduced_relation_type        0
% 2.59/0.94  --bmc1_ucm_relax_model                  4
% 2.59/0.94  --bmc1_ucm_full_tr_after_sat            true
% 2.59/0.94  --bmc1_ucm_expand_neg_assumptions       false
% 2.59/0.94  --bmc1_ucm_layered_model                none
% 2.59/0.94  --bmc1_ucm_max_lemma_size               10
% 2.59/0.94  
% 2.59/0.94  ------ AIG Options
% 2.59/0.94  
% 2.59/0.94  --aig_mode                              false
% 2.59/0.94  
% 2.59/0.94  ------ Instantiation Options
% 2.59/0.94  
% 2.59/0.94  --instantiation_flag                    true
% 2.59/0.94  --inst_sos_flag                         false
% 2.59/0.94  --inst_sos_phase                        true
% 2.59/0.94  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 2.59/0.94  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 2.59/0.94  --inst_lit_sel_side                     none
% 2.59/0.94  --inst_solver_per_active                1400
% 2.59/0.94  --inst_solver_calls_frac                1.
% 2.59/0.94  --inst_passive_queue_type               priority_queues
% 2.59/0.94  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 2.59/0.94  --inst_passive_queues_freq              [25;2]
% 2.59/0.94  --inst_dismatching                      true
% 2.59/0.94  --inst_eager_unprocessed_to_passive     true
% 2.59/0.94  --inst_prop_sim_given                   true
% 2.59/0.94  --inst_prop_sim_new                     false
% 2.59/0.94  --inst_subs_new                         false
% 2.59/0.94  --inst_eq_res_simp                      false
% 2.59/0.94  --inst_subs_given                       false
% 2.59/0.94  --inst_orphan_elimination               true
% 2.59/0.94  --inst_learning_loop_flag               true
% 2.59/0.94  --inst_learning_start                   3000
% 2.59/0.94  --inst_learning_factor                  2
% 2.59/0.94  --inst_start_prop_sim_after_learn       3
% 2.59/0.94  --inst_sel_renew                        solver
% 2.59/0.94  --inst_lit_activity_flag                true
% 2.59/0.94  --inst_restr_to_given                   false
% 2.59/0.94  --inst_activity_threshold               500
% 2.59/0.94  --inst_out_proof                        true
% 2.59/0.94  
% 2.59/0.94  ------ Resolution Options
% 2.59/0.94  
% 2.59/0.94  --resolution_flag                       false
% 2.59/0.94  --res_lit_sel                           adaptive
% 2.59/0.94  --res_lit_sel_side                      none
% 2.59/0.94  --res_ordering                          kbo
% 2.59/0.94  --res_to_prop_solver                    active
% 2.59/0.94  --res_prop_simpl_new                    false
% 2.59/0.94  --res_prop_simpl_given                  true
% 2.59/0.94  --res_passive_queue_type                priority_queues
% 2.59/0.94  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 2.59/0.94  --res_passive_queues_freq               [15;5]
% 2.59/0.94  --res_forward_subs                      full
% 2.59/0.94  --res_backward_subs                     full
% 2.59/0.94  --res_forward_subs_resolution           true
% 2.59/0.94  --res_backward_subs_resolution          true
% 2.59/0.94  --res_orphan_elimination                true
% 2.59/0.94  --res_time_limit                        2.
% 2.59/0.94  --res_out_proof                         true
% 2.59/0.94  
% 2.59/0.94  ------ Superposition Options
% 2.59/0.94  
% 2.59/0.94  --superposition_flag                    true
% 2.59/0.94  --sup_passive_queue_type                priority_queues
% 2.59/0.94  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 2.59/0.94  --sup_passive_queues_freq               [8;1;4]
% 2.59/0.94  --demod_completeness_check              fast
% 2.59/0.94  --demod_use_ground                      true
% 2.59/0.94  --sup_to_prop_solver                    passive
% 2.59/0.94  --sup_prop_simpl_new                    true
% 2.59/0.94  --sup_prop_simpl_given                  true
% 2.59/0.94  --sup_fun_splitting                     false
% 2.59/0.94  --sup_smt_interval                      50000
% 2.59/0.94  
% 2.59/0.94  ------ Superposition Simplification Setup
% 2.59/0.94  
% 2.59/0.94  --sup_indices_passive                   []
% 2.59/0.94  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.59/0.94  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.59/0.94  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.59/0.94  --sup_full_triv                         [TrivRules;PropSubs]
% 2.59/0.94  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.59/0.94  --sup_full_bw                           [BwDemod]
% 2.59/0.94  --sup_immed_triv                        [TrivRules]
% 2.59/0.94  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 2.59/0.94  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.59/0.94  --sup_immed_bw_main                     []
% 2.59/0.94  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.59/0.94  --sup_input_triv                        [Unflattening;TrivRules]
% 2.59/0.94  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.59/0.94  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.59/0.94  
% 2.59/0.94  ------ Combination Options
% 2.59/0.94  
% 2.59/0.94  --comb_res_mult                         3
% 2.59/0.94  --comb_sup_mult                         2
% 2.59/0.94  --comb_inst_mult                        10
% 2.59/0.94  
% 2.59/0.94  ------ Debug Options
% 2.59/0.94  
% 2.59/0.94  --dbg_backtrace                         false
% 2.59/0.94  --dbg_dump_prop_clauses                 false
% 2.59/0.94  --dbg_dump_prop_clauses_file            -
% 2.59/0.94  --dbg_out_stat                          false
% 2.59/0.94  
% 2.59/0.94  
% 2.59/0.94  
% 2.59/0.94  
% 2.59/0.94  ------ Proving...
% 2.59/0.94  
% 2.59/0.94  
% 2.59/0.94  % SZS status Theorem for theBenchmark.p
% 2.59/0.94  
% 2.59/0.94   Resolution empty clause
% 2.59/0.94  
% 2.59/0.94  % SZS output start CNFRefutation for theBenchmark.p
% 2.59/0.94  
% 2.59/0.94  fof(f11,axiom,(
% 2.59/0.94    ! [X0,X1] : (r1_tarski(X0,X1) => (r1_tarski(k1_setfam_1(X1),k1_setfam_1(X0)) | k1_xboole_0 = X0))),
% 2.59/0.94    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.59/0.94  
% 2.59/0.94  fof(f21,plain,(
% 2.59/0.94    ! [X0,X1] : ((r1_tarski(k1_setfam_1(X1),k1_setfam_1(X0)) | k1_xboole_0 = X0) | ~r1_tarski(X0,X1))),
% 2.59/0.94    inference(ennf_transformation,[],[f11])).
% 2.59/0.94  
% 2.59/0.94  fof(f22,plain,(
% 2.59/0.94    ! [X0,X1] : (r1_tarski(k1_setfam_1(X1),k1_setfam_1(X0)) | k1_xboole_0 = X0 | ~r1_tarski(X0,X1))),
% 2.59/0.94    inference(flattening,[],[f21])).
% 2.59/0.94  
% 2.59/0.94  fof(f53,plain,(
% 2.59/0.94    ( ! [X0,X1] : (r1_tarski(k1_setfam_1(X1),k1_setfam_1(X0)) | k1_xboole_0 = X0 | ~r1_tarski(X0,X1)) )),
% 2.59/0.94    inference(cnf_transformation,[],[f22])).
% 2.59/0.94  
% 2.59/0.94  fof(f12,conjecture,(
% 2.59/0.94    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(X0))) => (r1_tarski(X1,X2) => r1_tarski(k8_setfam_1(X0,X2),k8_setfam_1(X0,X1)))))),
% 2.59/0.94    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.59/0.94  
% 2.59/0.94  fof(f13,negated_conjecture,(
% 2.59/0.94    ~! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(X0))) => (r1_tarski(X1,X2) => r1_tarski(k8_setfam_1(X0,X2),k8_setfam_1(X0,X1)))))),
% 2.59/0.94    inference(negated_conjecture,[],[f12])).
% 2.59/0.94  
% 2.59/0.94  fof(f23,plain,(
% 2.59/0.94    ? [X0,X1] : (? [X2] : ((~r1_tarski(k8_setfam_1(X0,X2),k8_setfam_1(X0,X1)) & r1_tarski(X1,X2)) & m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(X0)))) & m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))))),
% 2.59/0.94    inference(ennf_transformation,[],[f13])).
% 2.59/0.94  
% 2.59/0.94  fof(f24,plain,(
% 2.59/0.94    ? [X0,X1] : (? [X2] : (~r1_tarski(k8_setfam_1(X0,X2),k8_setfam_1(X0,X1)) & r1_tarski(X1,X2) & m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(X0)))) & m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))))),
% 2.59/0.94    inference(flattening,[],[f23])).
% 2.59/0.94  
% 2.59/0.94  fof(f35,plain,(
% 2.59/0.94    ( ! [X0,X1] : (? [X2] : (~r1_tarski(k8_setfam_1(X0,X2),k8_setfam_1(X0,X1)) & r1_tarski(X1,X2) & m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(X0)))) => (~r1_tarski(k8_setfam_1(X0,sK4),k8_setfam_1(X0,X1)) & r1_tarski(X1,sK4) & m1_subset_1(sK4,k1_zfmisc_1(k1_zfmisc_1(X0))))) )),
% 2.59/0.94    introduced(choice_axiom,[])).
% 2.59/0.94  
% 2.59/0.94  fof(f34,plain,(
% 2.59/0.94    ? [X0,X1] : (? [X2] : (~r1_tarski(k8_setfam_1(X0,X2),k8_setfam_1(X0,X1)) & r1_tarski(X1,X2) & m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(X0)))) & m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0)))) => (? [X2] : (~r1_tarski(k8_setfam_1(sK2,X2),k8_setfam_1(sK2,sK3)) & r1_tarski(sK3,X2) & m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(sK2)))) & m1_subset_1(sK3,k1_zfmisc_1(k1_zfmisc_1(sK2))))),
% 2.59/0.94    introduced(choice_axiom,[])).
% 2.59/0.94  
% 2.59/0.94  fof(f36,plain,(
% 2.59/0.94    (~r1_tarski(k8_setfam_1(sK2,sK4),k8_setfam_1(sK2,sK3)) & r1_tarski(sK3,sK4) & m1_subset_1(sK4,k1_zfmisc_1(k1_zfmisc_1(sK2)))) & m1_subset_1(sK3,k1_zfmisc_1(k1_zfmisc_1(sK2)))),
% 2.59/0.94    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2,sK3,sK4])],[f24,f35,f34])).
% 2.59/0.94  
% 2.59/0.94  fof(f55,plain,(
% 2.59/0.94    m1_subset_1(sK4,k1_zfmisc_1(k1_zfmisc_1(sK2)))),
% 2.59/0.94    inference(cnf_transformation,[],[f36])).
% 2.59/0.94  
% 2.59/0.94  fof(f6,axiom,(
% 2.59/0.94    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) => ((k1_xboole_0 = X1 => k8_setfam_1(X0,X1) = X0) & (k1_xboole_0 != X1 => k8_setfam_1(X0,X1) = k6_setfam_1(X0,X1))))),
% 2.59/0.94    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.59/0.94  
% 2.59/0.94  fof(f16,plain,(
% 2.59/0.94    ! [X0,X1] : (((k8_setfam_1(X0,X1) = X0 | k1_xboole_0 != X1) & (k8_setfam_1(X0,X1) = k6_setfam_1(X0,X1) | k1_xboole_0 = X1)) | ~m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))))),
% 2.59/0.94    inference(ennf_transformation,[],[f6])).
% 2.59/0.94  
% 2.59/0.94  fof(f46,plain,(
% 2.59/0.94    ( ! [X0,X1] : (k8_setfam_1(X0,X1) = k6_setfam_1(X0,X1) | k1_xboole_0 = X1 | ~m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0)))) )),
% 2.59/0.94    inference(cnf_transformation,[],[f16])).
% 2.59/0.94  
% 2.59/0.94  fof(f8,axiom,(
% 2.59/0.94    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) => k6_setfam_1(X0,X1) = k1_setfam_1(X1))),
% 2.59/0.94    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.59/0.94  
% 2.59/0.94  fof(f18,plain,(
% 2.59/0.94    ! [X0,X1] : (k6_setfam_1(X0,X1) = k1_setfam_1(X1) | ~m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))))),
% 2.59/0.94    inference(ennf_transformation,[],[f8])).
% 2.59/0.94  
% 2.59/0.94  fof(f49,plain,(
% 2.59/0.94    ( ! [X0,X1] : (k6_setfam_1(X0,X1) = k1_setfam_1(X1) | ~m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0)))) )),
% 2.59/0.94    inference(cnf_transformation,[],[f18])).
% 2.59/0.94  
% 2.59/0.94  fof(f54,plain,(
% 2.59/0.94    m1_subset_1(sK3,k1_zfmisc_1(k1_zfmisc_1(sK2)))),
% 2.59/0.94    inference(cnf_transformation,[],[f36])).
% 2.59/0.94  
% 2.59/0.94  fof(f57,plain,(
% 2.59/0.94    ~r1_tarski(k8_setfam_1(sK2,sK4),k8_setfam_1(sK2,sK3))),
% 2.59/0.94    inference(cnf_transformation,[],[f36])).
% 2.59/0.94  
% 2.59/0.94  fof(f56,plain,(
% 2.59/0.94    r1_tarski(sK3,sK4)),
% 2.59/0.94    inference(cnf_transformation,[],[f36])).
% 2.59/0.94  
% 2.59/0.94  fof(f47,plain,(
% 2.59/0.94    ( ! [X0,X1] : (k8_setfam_1(X0,X1) = X0 | k1_xboole_0 != X1 | ~m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0)))) )),
% 2.59/0.94    inference(cnf_transformation,[],[f16])).
% 2.59/0.94  
% 2.59/0.94  fof(f60,plain,(
% 2.59/0.94    ( ! [X0] : (k8_setfam_1(X0,k1_xboole_0) = X0 | ~m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_zfmisc_1(X0)))) )),
% 2.59/0.94    inference(equality_resolution,[],[f47])).
% 2.59/0.94  
% 2.59/0.94  fof(f5,axiom,(
% 2.59/0.94    ! [X0] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0))),
% 2.59/0.94    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.59/0.94  
% 2.59/0.94  fof(f45,plain,(
% 2.59/0.94    ( ! [X0] : (m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0))) )),
% 2.59/0.94    inference(cnf_transformation,[],[f5])).
% 2.59/0.94  
% 2.59/0.94  fof(f7,axiom,(
% 2.59/0.94    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) => m1_subset_1(k8_setfam_1(X0,X1),k1_zfmisc_1(X0)))),
% 2.59/0.94    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.59/0.94  
% 2.59/0.94  fof(f17,plain,(
% 2.59/0.94    ! [X0,X1] : (m1_subset_1(k8_setfam_1(X0,X1),k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))))),
% 2.59/0.94    inference(ennf_transformation,[],[f7])).
% 2.59/0.94  
% 2.59/0.94  fof(f48,plain,(
% 2.59/0.94    ( ! [X0,X1] : (m1_subset_1(k8_setfam_1(X0,X1),k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0)))) )),
% 2.59/0.94    inference(cnf_transformation,[],[f17])).
% 2.59/0.94  
% 2.59/0.94  fof(f9,axiom,(
% 2.59/0.94    ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) <=> r1_tarski(X0,X1))),
% 2.59/0.94    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.59/0.94  
% 2.59/0.94  fof(f33,plain,(
% 2.59/0.94    ! [X0,X1] : ((m1_subset_1(X0,k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1)) & (r1_tarski(X0,X1) | ~m1_subset_1(X0,k1_zfmisc_1(X1))))),
% 2.59/0.94    inference(nnf_transformation,[],[f9])).
% 2.59/0.94  
% 2.59/0.94  fof(f50,plain,(
% 2.59/0.94    ( ! [X0,X1] : (r1_tarski(X0,X1) | ~m1_subset_1(X0,k1_zfmisc_1(X1))) )),
% 2.59/0.94    inference(cnf_transformation,[],[f33])).
% 2.59/0.94  
% 2.59/0.94  fof(f2,axiom,(
% 2.59/0.94    ! [X0] : ~(! [X1] : ~r2_hidden(X1,X0) & k1_xboole_0 != X0)),
% 2.59/0.94    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.59/0.94  
% 2.59/0.94  fof(f15,plain,(
% 2.59/0.94    ! [X0] : (? [X1] : r2_hidden(X1,X0) | k1_xboole_0 = X0)),
% 2.59/0.94    inference(ennf_transformation,[],[f2])).
% 2.59/0.94  
% 2.59/0.94  fof(f29,plain,(
% 2.59/0.94    ! [X0] : (? [X1] : r2_hidden(X1,X0) => r2_hidden(sK1(X0),X0))),
% 2.59/0.94    introduced(choice_axiom,[])).
% 2.59/0.94  
% 2.59/0.94  fof(f30,plain,(
% 2.59/0.94    ! [X0] : (r2_hidden(sK1(X0),X0) | k1_xboole_0 = X0)),
% 2.59/0.94    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1])],[f15,f29])).
% 2.59/0.94  
% 2.59/0.94  fof(f40,plain,(
% 2.59/0.94    ( ! [X0] : (r2_hidden(sK1(X0),X0) | k1_xboole_0 = X0) )),
% 2.59/0.94    inference(cnf_transformation,[],[f30])).
% 2.59/0.94  
% 2.59/0.94  fof(f1,axiom,(
% 2.59/0.94    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X0) => r2_hidden(X2,X1)))),
% 2.59/0.94    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.59/0.94  
% 2.59/0.94  fof(f14,plain,(
% 2.59/0.94    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X1) | ~r2_hidden(X2,X0)))),
% 2.59/0.94    inference(ennf_transformation,[],[f1])).
% 2.59/0.94  
% 2.59/0.94  fof(f25,plain,(
% 2.59/0.94    ! [X0,X1] : ((r1_tarski(X0,X1) | ? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0))) & (! [X2] : (r2_hidden(X2,X1) | ~r2_hidden(X2,X0)) | ~r1_tarski(X0,X1)))),
% 2.59/0.94    inference(nnf_transformation,[],[f14])).
% 2.59/0.94  
% 2.59/0.94  fof(f26,plain,(
% 2.59/0.94    ! [X0,X1] : ((r1_tarski(X0,X1) | ? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0))) & (! [X3] : (r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) | ~r1_tarski(X0,X1)))),
% 2.59/0.94    inference(rectify,[],[f25])).
% 2.59/0.94  
% 2.59/0.94  fof(f27,plain,(
% 2.59/0.94    ! [X1,X0] : (? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0)) => (~r2_hidden(sK0(X0,X1),X1) & r2_hidden(sK0(X0,X1),X0)))),
% 2.59/0.94    introduced(choice_axiom,[])).
% 2.59/0.94  
% 2.59/0.94  fof(f28,plain,(
% 2.59/0.94    ! [X0,X1] : ((r1_tarski(X0,X1) | (~r2_hidden(sK0(X0,X1),X1) & r2_hidden(sK0(X0,X1),X0))) & (! [X3] : (r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) | ~r1_tarski(X0,X1)))),
% 2.59/0.94    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f26,f27])).
% 2.59/0.94  
% 2.59/0.94  fof(f37,plain,(
% 2.59/0.94    ( ! [X0,X3,X1] : (r2_hidden(X3,X1) | ~r2_hidden(X3,X0) | ~r1_tarski(X0,X1)) )),
% 2.59/0.94    inference(cnf_transformation,[],[f28])).
% 2.59/0.94  
% 2.59/0.94  fof(f3,axiom,(
% 2.59/0.94    ! [X0,X1] : (k1_xboole_0 = k2_zfmisc_1(X0,X1) <=> (k1_xboole_0 = X1 | k1_xboole_0 = X0))),
% 2.59/0.94    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.59/0.94  
% 2.59/0.94  fof(f31,plain,(
% 2.59/0.94    ! [X0,X1] : ((k1_xboole_0 = k2_zfmisc_1(X0,X1) | (k1_xboole_0 != X1 & k1_xboole_0 != X0)) & ((k1_xboole_0 = X1 | k1_xboole_0 = X0) | k1_xboole_0 != k2_zfmisc_1(X0,X1)))),
% 2.59/0.94    inference(nnf_transformation,[],[f3])).
% 2.59/0.94  
% 2.59/0.94  fof(f32,plain,(
% 2.59/0.94    ! [X0,X1] : ((k1_xboole_0 = k2_zfmisc_1(X0,X1) | (k1_xboole_0 != X1 & k1_xboole_0 != X0)) & (k1_xboole_0 = X1 | k1_xboole_0 = X0 | k1_xboole_0 != k2_zfmisc_1(X0,X1)))),
% 2.59/0.94    inference(flattening,[],[f31])).
% 2.59/0.94  
% 2.59/0.94  fof(f43,plain,(
% 2.59/0.94    ( ! [X0,X1] : (k1_xboole_0 = k2_zfmisc_1(X0,X1) | k1_xboole_0 != X1) )),
% 2.59/0.94    inference(cnf_transformation,[],[f32])).
% 2.59/0.94  
% 2.59/0.94  fof(f58,plain,(
% 2.59/0.94    ( ! [X0] : (k1_xboole_0 = k2_zfmisc_1(X0,k1_xboole_0)) )),
% 2.59/0.94    inference(equality_resolution,[],[f43])).
% 2.59/0.94  
% 2.59/0.94  fof(f4,axiom,(
% 2.59/0.94    ! [X0,X1] : ~r2_hidden(X0,k2_zfmisc_1(X0,X1))),
% 2.59/0.94    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.59/0.94  
% 2.59/0.94  fof(f44,plain,(
% 2.59/0.94    ( ! [X0,X1] : (~r2_hidden(X0,k2_zfmisc_1(X0,X1))) )),
% 2.59/0.94    inference(cnf_transformation,[],[f4])).
% 2.59/0.94  
% 2.59/0.94  fof(f38,plain,(
% 2.59/0.94    ( ! [X0,X1] : (r1_tarski(X0,X1) | r2_hidden(sK0(X0,X1),X0)) )),
% 2.59/0.94    inference(cnf_transformation,[],[f28])).
% 2.59/0.94  
% 2.59/0.94  fof(f39,plain,(
% 2.59/0.94    ( ! [X0,X1] : (r1_tarski(X0,X1) | ~r2_hidden(sK0(X0,X1),X1)) )),
% 2.59/0.94    inference(cnf_transformation,[],[f28])).
% 2.59/0.94  
% 2.59/0.94  cnf(c_16,plain,
% 2.59/0.94      ( ~ r1_tarski(X0,X1)
% 2.59/0.94      | r1_tarski(k1_setfam_1(X1),k1_setfam_1(X0))
% 2.59/0.94      | k1_xboole_0 = X0 ),
% 2.59/0.94      inference(cnf_transformation,[],[f53]) ).
% 2.59/0.94  
% 2.59/0.94  cnf(c_678,plain,
% 2.59/0.94      ( k1_xboole_0 = X0
% 2.59/0.94      | r1_tarski(X0,X1) != iProver_top
% 2.59/0.94      | r1_tarski(k1_setfam_1(X1),k1_setfam_1(X0)) = iProver_top ),
% 2.59/0.94      inference(predicate_to_equality,[status(thm)],[c_16]) ).
% 2.59/0.94  
% 2.59/0.94  cnf(c_19,negated_conjecture,
% 2.59/0.94      ( m1_subset_1(sK4,k1_zfmisc_1(k1_zfmisc_1(sK2))) ),
% 2.59/0.94      inference(cnf_transformation,[],[f55]) ).
% 2.59/0.94  
% 2.59/0.94  cnf(c_675,plain,
% 2.59/0.94      ( m1_subset_1(sK4,k1_zfmisc_1(k1_zfmisc_1(sK2))) = iProver_top ),
% 2.59/0.94      inference(predicate_to_equality,[status(thm)],[c_19]) ).
% 2.59/0.94  
% 2.59/0.94  cnf(c_10,plain,
% 2.59/0.94      ( ~ m1_subset_1(X0,k1_zfmisc_1(k1_zfmisc_1(X1)))
% 2.59/0.94      | k6_setfam_1(X1,X0) = k8_setfam_1(X1,X0)
% 2.59/0.94      | k1_xboole_0 = X0 ),
% 2.59/0.94      inference(cnf_transformation,[],[f46]) ).
% 2.59/0.94  
% 2.59/0.94  cnf(c_684,plain,
% 2.59/0.94      ( k6_setfam_1(X0,X1) = k8_setfam_1(X0,X1)
% 2.59/0.94      | k1_xboole_0 = X1
% 2.59/0.94      | m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) != iProver_top ),
% 2.59/0.94      inference(predicate_to_equality,[status(thm)],[c_10]) ).
% 2.59/0.94  
% 2.59/0.94  cnf(c_2165,plain,
% 2.59/0.94      ( k6_setfam_1(sK2,sK4) = k8_setfam_1(sK2,sK4) | sK4 = k1_xboole_0 ),
% 2.59/0.94      inference(superposition,[status(thm)],[c_675,c_684]) ).
% 2.59/0.94  
% 2.59/0.94  cnf(c_12,plain,
% 2.59/0.94      ( ~ m1_subset_1(X0,k1_zfmisc_1(k1_zfmisc_1(X1)))
% 2.59/0.94      | k6_setfam_1(X1,X0) = k1_setfam_1(X0) ),
% 2.59/0.94      inference(cnf_transformation,[],[f49]) ).
% 2.59/0.94  
% 2.59/0.94  cnf(c_682,plain,
% 2.59/0.94      ( k6_setfam_1(X0,X1) = k1_setfam_1(X1)
% 2.59/0.94      | m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) != iProver_top ),
% 2.59/0.94      inference(predicate_to_equality,[status(thm)],[c_12]) ).
% 2.59/0.94  
% 2.59/0.94  cnf(c_1437,plain,
% 2.59/0.94      ( k6_setfam_1(sK2,sK4) = k1_setfam_1(sK4) ),
% 2.59/0.94      inference(superposition,[status(thm)],[c_675,c_682]) ).
% 2.59/0.94  
% 2.59/0.94  cnf(c_2174,plain,
% 2.59/0.94      ( k8_setfam_1(sK2,sK4) = k1_setfam_1(sK4) | sK4 = k1_xboole_0 ),
% 2.59/0.94      inference(light_normalisation,[status(thm)],[c_2165,c_1437]) ).
% 2.59/0.94  
% 2.59/0.94  cnf(c_20,negated_conjecture,
% 2.59/0.94      ( m1_subset_1(sK3,k1_zfmisc_1(k1_zfmisc_1(sK2))) ),
% 2.59/0.94      inference(cnf_transformation,[],[f54]) ).
% 2.59/0.94  
% 2.59/0.94  cnf(c_674,plain,
% 2.59/0.94      ( m1_subset_1(sK3,k1_zfmisc_1(k1_zfmisc_1(sK2))) = iProver_top ),
% 2.59/0.94      inference(predicate_to_equality,[status(thm)],[c_20]) ).
% 2.59/0.94  
% 2.59/0.94  cnf(c_2166,plain,
% 2.59/0.94      ( k6_setfam_1(sK2,sK3) = k8_setfam_1(sK2,sK3) | sK3 = k1_xboole_0 ),
% 2.59/0.94      inference(superposition,[status(thm)],[c_674,c_684]) ).
% 2.59/0.94  
% 2.59/0.94  cnf(c_1438,plain,
% 2.59/0.94      ( k6_setfam_1(sK2,sK3) = k1_setfam_1(sK3) ),
% 2.59/0.94      inference(superposition,[status(thm)],[c_674,c_682]) ).
% 2.59/0.94  
% 2.59/0.94  cnf(c_2169,plain,
% 2.59/0.94      ( k8_setfam_1(sK2,sK3) = k1_setfam_1(sK3) | sK3 = k1_xboole_0 ),
% 2.59/0.94      inference(light_normalisation,[status(thm)],[c_2166,c_1438]) ).
% 2.59/0.94  
% 2.59/0.94  cnf(c_17,negated_conjecture,
% 2.59/0.94      ( ~ r1_tarski(k8_setfam_1(sK2,sK4),k8_setfam_1(sK2,sK3)) ),
% 2.59/0.94      inference(cnf_transformation,[],[f57]) ).
% 2.59/0.94  
% 2.59/0.94  cnf(c_677,plain,
% 2.59/0.94      ( r1_tarski(k8_setfam_1(sK2,sK4),k8_setfam_1(sK2,sK3)) != iProver_top ),
% 2.59/0.94      inference(predicate_to_equality,[status(thm)],[c_17]) ).
% 2.59/0.94  
% 2.59/0.94  cnf(c_2344,plain,
% 2.59/0.94      ( sK3 = k1_xboole_0
% 2.59/0.94      | r1_tarski(k8_setfam_1(sK2,sK4),k1_setfam_1(sK3)) != iProver_top ),
% 2.59/0.94      inference(superposition,[status(thm)],[c_2169,c_677]) ).
% 2.59/0.94  
% 2.59/0.94  cnf(c_2472,plain,
% 2.59/0.94      ( sK3 = k1_xboole_0
% 2.59/0.94      | sK4 = k1_xboole_0
% 2.59/0.94      | r1_tarski(k1_setfam_1(sK4),k1_setfam_1(sK3)) != iProver_top ),
% 2.59/0.94      inference(superposition,[status(thm)],[c_2174,c_2344]) ).
% 2.59/0.94  
% 2.59/0.94  cnf(c_2596,plain,
% 2.59/0.94      ( sK3 = k1_xboole_0
% 2.59/0.94      | sK4 = k1_xboole_0
% 2.59/0.94      | r1_tarski(sK3,sK4) != iProver_top ),
% 2.59/0.94      inference(superposition,[status(thm)],[c_678,c_2472]) ).
% 2.59/0.94  
% 2.59/0.94  cnf(c_18,negated_conjecture,
% 2.59/0.94      ( r1_tarski(sK3,sK4) ),
% 2.59/0.94      inference(cnf_transformation,[],[f56]) ).
% 2.59/0.94  
% 2.59/0.94  cnf(c_2597,plain,
% 2.59/0.94      ( ~ r1_tarski(sK3,sK4) | sK3 = k1_xboole_0 | sK4 = k1_xboole_0 ),
% 2.59/0.94      inference(predicate_to_equality_rev,[status(thm)],[c_2596]) ).
% 2.59/0.94  
% 2.59/0.94  cnf(c_2746,plain,
% 2.59/0.94      ( sK4 = k1_xboole_0 | sK3 = k1_xboole_0 ),
% 2.59/0.94      inference(global_propositional_subsumption,
% 2.59/0.94                [status(thm)],
% 2.59/0.94                [c_2596,c_18,c_2597]) ).
% 2.59/0.94  
% 2.59/0.94  cnf(c_2747,plain,
% 2.59/0.94      ( sK3 = k1_xboole_0 | sK4 = k1_xboole_0 ),
% 2.59/0.94      inference(renaming,[status(thm)],[c_2746]) ).
% 2.59/0.94  
% 2.59/0.94  cnf(c_2758,plain,
% 2.59/0.94      ( sK4 = k1_xboole_0
% 2.59/0.94      | r1_tarski(k8_setfam_1(sK2,sK4),k8_setfam_1(sK2,k1_xboole_0)) != iProver_top ),
% 2.59/0.94      inference(superposition,[status(thm)],[c_2747,c_677]) ).
% 2.59/0.94  
% 2.59/0.94  cnf(c_9,plain,
% 2.59/0.94      ( ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_zfmisc_1(X0)))
% 2.59/0.94      | k8_setfam_1(X0,k1_xboole_0) = X0 ),
% 2.59/0.94      inference(cnf_transformation,[],[f60]) ).
% 2.59/0.94  
% 2.59/0.94  cnf(c_685,plain,
% 2.59/0.94      ( k8_setfam_1(X0,k1_xboole_0) = X0
% 2.59/0.94      | m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_zfmisc_1(X0))) != iProver_top ),
% 2.59/0.94      inference(predicate_to_equality,[status(thm)],[c_9]) ).
% 2.59/0.94  
% 2.59/0.94  cnf(c_8,plain,
% 2.59/0.94      ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0)) ),
% 2.59/0.94      inference(cnf_transformation,[],[f45]) ).
% 2.59/0.94  
% 2.59/0.94  cnf(c_686,plain,
% 2.59/0.94      ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0)) = iProver_top ),
% 2.59/0.94      inference(predicate_to_equality,[status(thm)],[c_8]) ).
% 2.59/0.94  
% 2.59/0.94  cnf(c_726,plain,
% 2.59/0.94      ( k8_setfam_1(X0,k1_xboole_0) = X0 ),
% 2.59/0.94      inference(forward_subsumption_resolution,[status(thm)],[c_685,c_686]) ).
% 2.59/0.94  
% 2.59/0.94  cnf(c_2767,plain,
% 2.59/0.94      ( sK4 = k1_xboole_0
% 2.59/0.94      | r1_tarski(k8_setfam_1(sK2,sK4),sK2) != iProver_top ),
% 2.59/0.94      inference(demodulation,[status(thm)],[c_2758,c_726]) ).
% 2.59/0.94  
% 2.59/0.94  cnf(c_22,plain,
% 2.59/0.94      ( m1_subset_1(sK4,k1_zfmisc_1(k1_zfmisc_1(sK2))) = iProver_top ),
% 2.59/0.94      inference(predicate_to_equality,[status(thm)],[c_19]) ).
% 2.59/0.94  
% 2.59/0.94  cnf(c_11,plain,
% 2.59/0.94      ( ~ m1_subset_1(X0,k1_zfmisc_1(k1_zfmisc_1(X1)))
% 2.59/0.94      | m1_subset_1(k8_setfam_1(X1,X0),k1_zfmisc_1(X1)) ),
% 2.59/0.94      inference(cnf_transformation,[],[f48]) ).
% 2.59/0.94  
% 2.59/0.94  cnf(c_833,plain,
% 2.59/0.94      ( m1_subset_1(k8_setfam_1(sK2,sK4),k1_zfmisc_1(sK2))
% 2.59/0.94      | ~ m1_subset_1(sK4,k1_zfmisc_1(k1_zfmisc_1(sK2))) ),
% 2.59/0.94      inference(instantiation,[status(thm)],[c_11]) ).
% 2.59/0.94  
% 2.59/0.94  cnf(c_834,plain,
% 2.59/0.94      ( m1_subset_1(k8_setfam_1(sK2,sK4),k1_zfmisc_1(sK2)) = iProver_top
% 2.59/0.94      | m1_subset_1(sK4,k1_zfmisc_1(k1_zfmisc_1(sK2))) != iProver_top ),
% 2.59/0.94      inference(predicate_to_equality,[status(thm)],[c_833]) ).
% 2.59/0.94  
% 2.59/0.94  cnf(c_14,plain,
% 2.59/0.94      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1)) | r1_tarski(X0,X1) ),
% 2.59/0.94      inference(cnf_transformation,[],[f50]) ).
% 2.59/0.94  
% 2.59/0.94  cnf(c_963,plain,
% 2.59/0.94      ( ~ m1_subset_1(k8_setfam_1(sK2,sK4),k1_zfmisc_1(X0))
% 2.59/0.94      | r1_tarski(k8_setfam_1(sK2,sK4),X0) ),
% 2.59/0.94      inference(instantiation,[status(thm)],[c_14]) ).
% 2.59/0.94  
% 2.59/0.94  cnf(c_1286,plain,
% 2.59/0.94      ( ~ m1_subset_1(k8_setfam_1(sK2,sK4),k1_zfmisc_1(sK2))
% 2.59/0.94      | r1_tarski(k8_setfam_1(sK2,sK4),sK2) ),
% 2.59/0.94      inference(instantiation,[status(thm)],[c_963]) ).
% 2.59/0.94  
% 2.59/0.94  cnf(c_1287,plain,
% 2.59/0.94      ( m1_subset_1(k8_setfam_1(sK2,sK4),k1_zfmisc_1(sK2)) != iProver_top
% 2.59/0.94      | r1_tarski(k8_setfam_1(sK2,sK4),sK2) = iProver_top ),
% 2.59/0.94      inference(predicate_to_equality,[status(thm)],[c_1286]) ).
% 2.59/0.94  
% 2.59/0.94  cnf(c_2873,plain,
% 2.59/0.94      ( sK4 = k1_xboole_0 ),
% 2.59/0.94      inference(global_propositional_subsumption,
% 2.59/0.94                [status(thm)],
% 2.59/0.94                [c_2767,c_22,c_834,c_1287]) ).
% 2.59/0.94  
% 2.59/0.94  cnf(c_676,plain,
% 2.59/0.94      ( r1_tarski(sK3,sK4) = iProver_top ),
% 2.59/0.94      inference(predicate_to_equality,[status(thm)],[c_18]) ).
% 2.59/0.94  
% 2.59/0.94  cnf(c_2886,plain,
% 2.59/0.94      ( r1_tarski(sK3,k1_xboole_0) = iProver_top ),
% 2.59/0.94      inference(demodulation,[status(thm)],[c_2873,c_676]) ).
% 2.59/0.94  
% 2.59/0.94  cnf(c_3,plain,
% 2.59/0.94      ( r2_hidden(sK1(X0),X0) | k1_xboole_0 = X0 ),
% 2.59/0.94      inference(cnf_transformation,[],[f40]) ).
% 2.59/0.94  
% 2.59/0.94  cnf(c_688,plain,
% 2.59/0.94      ( k1_xboole_0 = X0 | r2_hidden(sK1(X0),X0) = iProver_top ),
% 2.59/0.94      inference(predicate_to_equality,[status(thm)],[c_3]) ).
% 2.59/0.94  
% 2.59/0.94  cnf(c_2,plain,
% 2.59/0.94      ( ~ r2_hidden(X0,X1) | r2_hidden(X0,X2) | ~ r1_tarski(X1,X2) ),
% 2.59/0.94      inference(cnf_transformation,[],[f37]) ).
% 2.59/0.94  
% 2.59/0.94  cnf(c_689,plain,
% 2.59/0.94      ( r2_hidden(X0,X1) != iProver_top
% 2.59/0.94      | r2_hidden(X0,X2) = iProver_top
% 2.59/0.94      | r1_tarski(X1,X2) != iProver_top ),
% 2.59/0.94      inference(predicate_to_equality,[status(thm)],[c_2]) ).
% 2.59/0.94  
% 2.59/0.94  cnf(c_1742,plain,
% 2.59/0.94      ( k1_xboole_0 = X0
% 2.59/0.94      | r2_hidden(sK1(X0),X1) = iProver_top
% 2.59/0.94      | r1_tarski(X0,X1) != iProver_top ),
% 2.59/0.94      inference(superposition,[status(thm)],[c_688,c_689]) ).
% 2.59/0.94  
% 2.59/0.94  cnf(c_4,plain,
% 2.59/0.94      ( k2_zfmisc_1(X0,k1_xboole_0) = k1_xboole_0 ),
% 2.59/0.94      inference(cnf_transformation,[],[f58]) ).
% 2.59/0.94  
% 2.59/0.94  cnf(c_7,plain,
% 2.59/0.94      ( ~ r2_hidden(X0,k2_zfmisc_1(X0,X1)) ),
% 2.59/0.94      inference(cnf_transformation,[],[f44]) ).
% 2.59/0.94  
% 2.59/0.94  cnf(c_687,plain,
% 2.59/0.94      ( r2_hidden(X0,k2_zfmisc_1(X0,X1)) != iProver_top ),
% 2.59/0.94      inference(predicate_to_equality,[status(thm)],[c_7]) ).
% 2.59/0.94  
% 2.59/0.94  cnf(c_1119,plain,
% 2.59/0.94      ( r2_hidden(X0,k1_xboole_0) != iProver_top ),
% 2.59/0.94      inference(superposition,[status(thm)],[c_4,c_687]) ).
% 2.59/0.94  
% 2.59/0.94  cnf(c_4317,plain,
% 2.59/0.94      ( k1_xboole_0 = X0 | r1_tarski(X0,k1_xboole_0) != iProver_top ),
% 2.59/0.94      inference(superposition,[status(thm)],[c_1742,c_1119]) ).
% 2.59/0.94  
% 2.59/0.94  cnf(c_4937,plain,
% 2.59/0.94      ( sK3 = k1_xboole_0 ),
% 2.59/0.94      inference(superposition,[status(thm)],[c_2886,c_4317]) ).
% 2.59/0.94  
% 2.59/0.94  cnf(c_2884,plain,
% 2.59/0.94      ( r1_tarski(k8_setfam_1(sK2,k1_xboole_0),k8_setfam_1(sK2,sK3)) != iProver_top ),
% 2.59/0.94      inference(demodulation,[status(thm)],[c_2873,c_677]) ).
% 2.59/0.94  
% 2.59/0.94  cnf(c_2891,plain,
% 2.59/0.94      ( r1_tarski(sK2,k8_setfam_1(sK2,sK3)) != iProver_top ),
% 2.59/0.94      inference(demodulation,[status(thm)],[c_2884,c_726]) ).
% 2.59/0.94  
% 2.59/0.94  cnf(c_5208,plain,
% 2.59/0.94      ( r1_tarski(sK2,k8_setfam_1(sK2,k1_xboole_0)) != iProver_top ),
% 2.59/0.94      inference(demodulation,[status(thm)],[c_4937,c_2891]) ).
% 2.59/0.94  
% 2.59/0.94  cnf(c_5220,plain,
% 2.59/0.94      ( r1_tarski(sK2,sK2) != iProver_top ),
% 2.59/0.94      inference(demodulation,[status(thm)],[c_5208,c_726]) ).
% 2.59/0.94  
% 2.59/0.94  cnf(c_1,plain,
% 2.59/0.94      ( r2_hidden(sK0(X0,X1),X0) | r1_tarski(X0,X1) ),
% 2.59/0.94      inference(cnf_transformation,[],[f38]) ).
% 2.59/0.94  
% 2.59/0.94  cnf(c_690,plain,
% 2.59/0.94      ( r2_hidden(sK0(X0,X1),X0) = iProver_top
% 2.59/0.94      | r1_tarski(X0,X1) = iProver_top ),
% 2.59/0.94      inference(predicate_to_equality,[status(thm)],[c_1]) ).
% 2.59/0.94  
% 2.59/0.94  cnf(c_0,plain,
% 2.59/0.94      ( ~ r2_hidden(sK0(X0,X1),X1) | r1_tarski(X0,X1) ),
% 2.59/0.94      inference(cnf_transformation,[],[f39]) ).
% 2.59/0.94  
% 2.59/0.94  cnf(c_691,plain,
% 2.59/0.94      ( r2_hidden(sK0(X0,X1),X1) != iProver_top
% 2.59/0.94      | r1_tarski(X0,X1) = iProver_top ),
% 2.59/0.94      inference(predicate_to_equality,[status(thm)],[c_0]) ).
% 2.59/0.94  
% 2.59/0.94  cnf(c_1597,plain,
% 2.59/0.94      ( r1_tarski(X0,X0) = iProver_top ),
% 2.59/0.94      inference(superposition,[status(thm)],[c_690,c_691]) ).
% 2.59/0.94  
% 2.59/0.94  cnf(c_5235,plain,
% 2.59/0.94      ( $false ),
% 2.59/0.94      inference(forward_subsumption_resolution,[status(thm)],[c_5220,c_1597]) ).
% 2.59/0.94  
% 2.59/0.94  
% 2.59/0.94  % SZS output end CNFRefutation for theBenchmark.p
% 2.59/0.94  
% 2.59/0.94  ------                               Statistics
% 2.59/0.94  
% 2.59/0.94  ------ General
% 2.59/0.94  
% 2.59/0.94  abstr_ref_over_cycles:                  0
% 2.59/0.94  abstr_ref_under_cycles:                 0
% 2.59/0.94  gc_basic_clause_elim:                   0
% 2.59/0.94  forced_gc_time:                         0
% 2.59/0.94  parsing_time:                           0.007
% 2.59/0.94  unif_index_cands_time:                  0.
% 2.59/0.94  unif_index_add_time:                    0.
% 2.59/0.94  orderings_time:                         0.
% 2.59/0.94  out_proof_time:                         0.008
% 2.59/0.94  total_time:                             0.14
% 2.59/0.94  num_of_symbols:                         45
% 2.59/0.94  num_of_terms:                           3855
% 2.59/0.94  
% 2.59/0.94  ------ Preprocessing
% 2.59/0.94  
% 2.59/0.94  num_of_splits:                          0
% 2.59/0.94  num_of_split_atoms:                     0
% 2.59/0.94  num_of_reused_defs:                     0
% 2.59/0.94  num_eq_ax_congr_red:                    12
% 2.59/0.94  num_of_sem_filtered_clauses:            1
% 2.59/0.94  num_of_subtypes:                        0
% 2.59/0.94  monotx_restored_types:                  0
% 2.59/0.94  sat_num_of_epr_types:                   0
% 2.59/0.94  sat_num_of_non_cyclic_types:            0
% 2.59/0.94  sat_guarded_non_collapsed_types:        0
% 2.59/0.94  num_pure_diseq_elim:                    0
% 2.59/0.94  simp_replaced_by:                       0
% 2.59/0.94  res_preprocessed:                       80
% 2.59/0.94  prep_upred:                             0
% 2.59/0.94  prep_unflattend:                        0
% 2.59/0.94  smt_new_axioms:                         0
% 2.59/0.94  pred_elim_cands:                        3
% 2.59/0.94  pred_elim:                              0
% 2.59/0.94  pred_elim_cl:                           0
% 2.59/0.94  pred_elim_cycles:                       1
% 2.59/0.94  merged_defs:                            6
% 2.59/0.94  merged_defs_ncl:                        0
% 2.59/0.94  bin_hyper_res:                          6
% 2.59/0.94  prep_cycles:                            3
% 2.59/0.94  pred_elim_time:                         0.
% 2.59/0.94  splitting_time:                         0.
% 2.59/0.94  sem_filter_time:                        0.
% 2.59/0.94  monotx_time:                            0.
% 2.59/0.94  subtype_inf_time:                       0.
% 2.59/0.94  
% 2.59/0.94  ------ Problem properties
% 2.59/0.94  
% 2.59/0.94  clauses:                                21
% 2.59/0.94  conjectures:                            4
% 2.59/0.94  epr:                                    2
% 2.59/0.94  horn:                                   16
% 2.59/0.94  ground:                                 4
% 2.59/0.94  unary:                                  8
% 2.59/0.94  binary:                                 8
% 2.59/0.94  lits:                                   39
% 2.59/0.94  lits_eq:                                11
% 2.59/0.94  fd_pure:                                0
% 2.59/0.94  fd_pseudo:                              0
% 2.59/0.94  fd_cond:                                4
% 2.59/0.94  fd_pseudo_cond:                         0
% 2.59/0.94  ac_symbols:                             0
% 2.59/0.94  
% 2.59/0.94  ------ Propositional Solver
% 2.59/0.94  
% 2.59/0.94  prop_solver_calls:                      26
% 2.59/0.94  prop_fast_solver_calls:                 523
% 2.59/0.94  smt_solver_calls:                       0
% 2.59/0.94  smt_fast_solver_calls:                  0
% 2.59/0.94  prop_num_of_clauses:                    1706
% 2.59/0.94  prop_preprocess_simplified:             4374
% 2.59/0.94  prop_fo_subsumed:                       5
% 2.59/0.94  prop_solver_time:                       0.
% 2.59/0.94  smt_solver_time:                        0.
% 2.59/0.94  smt_fast_solver_time:                   0.
% 2.59/0.94  prop_fast_solver_time:                  0.
% 2.59/0.94  prop_unsat_core_time:                   0.
% 2.59/0.94  
% 2.59/0.94  ------ QBF
% 2.59/0.94  
% 2.59/0.94  qbf_q_res:                              0
% 2.59/0.94  qbf_num_tautologies:                    0
% 2.59/0.94  qbf_prep_cycles:                        0
% 2.59/0.94  
% 2.59/0.94  ------ BMC1
% 2.59/0.94  
% 2.59/0.94  bmc1_current_bound:                     -1
% 2.59/0.94  bmc1_last_solved_bound:                 -1
% 2.59/0.94  bmc1_unsat_core_size:                   -1
% 2.59/0.94  bmc1_unsat_core_parents_size:           -1
% 2.59/0.94  bmc1_merge_next_fun:                    0
% 2.59/0.94  bmc1_unsat_core_clauses_time:           0.
% 2.59/0.94  
% 2.59/0.94  ------ Instantiation
% 2.59/0.94  
% 2.59/0.94  inst_num_of_clauses:                    543
% 2.59/0.94  inst_num_in_passive:                    247
% 2.59/0.94  inst_num_in_active:                     271
% 2.59/0.94  inst_num_in_unprocessed:                25
% 2.59/0.94  inst_num_of_loops:                      420
% 2.59/0.94  inst_num_of_learning_restarts:          0
% 2.59/0.94  inst_num_moves_active_passive:          145
% 2.59/0.94  inst_lit_activity:                      0
% 2.59/0.94  inst_lit_activity_moves:                0
% 2.59/0.94  inst_num_tautologies:                   0
% 2.59/0.94  inst_num_prop_implied:                  0
% 2.59/0.94  inst_num_existing_simplified:           0
% 2.59/0.94  inst_num_eq_res_simplified:             0
% 2.59/0.94  inst_num_child_elim:                    0
% 2.59/0.94  inst_num_of_dismatching_blockings:      199
% 2.59/0.94  inst_num_of_non_proper_insts:           610
% 2.59/0.94  inst_num_of_duplicates:                 0
% 2.59/0.94  inst_inst_num_from_inst_to_res:         0
% 2.59/0.94  inst_dismatching_checking_time:         0.
% 2.59/0.94  
% 2.59/0.94  ------ Resolution
% 2.59/0.94  
% 2.59/0.94  res_num_of_clauses:                     0
% 2.59/0.94  res_num_in_passive:                     0
% 2.59/0.94  res_num_in_active:                      0
% 2.59/0.94  res_num_of_loops:                       83
% 2.59/0.94  res_forward_subset_subsumed:            105
% 2.59/0.94  res_backward_subset_subsumed:           0
% 2.59/0.94  res_forward_subsumed:                   0
% 2.59/0.94  res_backward_subsumed:                  0
% 2.59/0.94  res_forward_subsumption_resolution:     0
% 2.59/0.94  res_backward_subsumption_resolution:    0
% 2.59/0.94  res_clause_to_clause_subsumption:       462
% 2.59/0.94  res_orphan_elimination:                 0
% 2.59/0.94  res_tautology_del:                      85
% 2.59/0.94  res_num_eq_res_simplified:              0
% 2.59/0.94  res_num_sel_changes:                    0
% 2.59/0.94  res_moves_from_active_to_pass:          0
% 2.59/0.94  
% 2.59/0.94  ------ Superposition
% 2.59/0.94  
% 2.59/0.94  sup_time_total:                         0.
% 2.59/0.94  sup_time_generating:                    0.
% 2.59/0.94  sup_time_sim_full:                      0.
% 2.59/0.94  sup_time_sim_immed:                     0.
% 2.59/0.94  
% 2.59/0.94  sup_num_of_clauses:                     85
% 2.59/0.94  sup_num_in_active:                      41
% 2.59/0.94  sup_num_in_passive:                     44
% 2.59/0.94  sup_num_of_loops:                       83
% 2.59/0.94  sup_fw_superposition:                   97
% 2.59/0.94  sup_bw_superposition:                   61
% 2.59/0.94  sup_immediate_simplified:               52
% 2.59/0.94  sup_given_eliminated:                   0
% 2.59/0.94  comparisons_done:                       0
% 2.59/0.94  comparisons_avoided:                    14
% 2.59/0.94  
% 2.59/0.94  ------ Simplifications
% 2.59/0.94  
% 2.59/0.94  
% 2.59/0.94  sim_fw_subset_subsumed:                 28
% 2.59/0.94  sim_bw_subset_subsumed:                 16
% 2.59/0.94  sim_fw_subsumed:                        15
% 2.59/0.94  sim_bw_subsumed:                        1
% 2.59/0.94  sim_fw_subsumption_res:                 2
% 2.59/0.94  sim_bw_subsumption_res:                 0
% 2.59/0.94  sim_tautology_del:                      1
% 2.59/0.94  sim_eq_tautology_del:                   9
% 2.59/0.94  sim_eq_res_simp:                        0
% 2.59/0.94  sim_fw_demodulated:                     9
% 2.59/0.94  sim_bw_demodulated:                     31
% 2.59/0.94  sim_light_normalised:                   5
% 2.59/0.94  sim_joinable_taut:                      0
% 2.59/0.94  sim_joinable_simp:                      0
% 2.59/0.94  sim_ac_normalised:                      0
% 2.59/0.94  sim_smt_subsumption:                    0
% 2.59/0.94  
%------------------------------------------------------------------------------
