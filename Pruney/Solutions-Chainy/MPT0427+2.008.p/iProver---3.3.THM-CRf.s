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
% DateTime   : Thu Dec  3 11:42:28 EST 2020

% Result     : Theorem 2.13s
% Output     : CNFRefutation 2.13s
% Verified   : 
% Statistics : Number of formulae       :  143 (1189 expanded)
%              Number of clauses        :   83 ( 449 expanded)
%              Number of leaves         :   21 ( 289 expanded)
%              Depth                    :   26
%              Number of atoms          :  308 (3766 expanded)
%              Number of equality atoms :  159 ( 979 expanded)
%              Maximal formula depth    :    8 (   3 average)
%              Maximal clause size      :    8 (   2 average)
%              Maximal term depth       :    7 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f1,axiom,(
    ! [X0] :
      ( v1_xboole_0(X0)
    <=> ! [X1] : ~ r2_hidden(X1,X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f26,plain,(
    ! [X0] :
      ( ( v1_xboole_0(X0)
        | ? [X1] : r2_hidden(X1,X0) )
      & ( ! [X1] : ~ r2_hidden(X1,X0)
        | ~ v1_xboole_0(X0) ) ) ),
    inference(nnf_transformation,[],[f1])).

fof(f27,plain,(
    ! [X0] :
      ( ( v1_xboole_0(X0)
        | ? [X1] : r2_hidden(X1,X0) )
      & ( ! [X2] : ~ r2_hidden(X2,X0)
        | ~ v1_xboole_0(X0) ) ) ),
    inference(rectify,[],[f26])).

fof(f28,plain,(
    ! [X0] :
      ( ? [X1] : r2_hidden(X1,X0)
     => r2_hidden(sK0(X0),X0) ) ),
    introduced(choice_axiom,[])).

fof(f29,plain,(
    ! [X0] :
      ( ( v1_xboole_0(X0)
        | r2_hidden(sK0(X0),X0) )
      & ( ! [X2] : ~ r2_hidden(X2,X0)
        | ~ v1_xboole_0(X0) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f27,f28])).

fof(f37,plain,(
    ! [X0] :
      ( v1_xboole_0(X0)
      | r2_hidden(sK0(X0),X0) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f5,axiom,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
     => k2_xboole_0(k1_tarski(X0),X1) = X1 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f17,plain,(
    ! [X0,X1] :
      ( k2_xboole_0(k1_tarski(X0),X1) = X1
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f41,plain,(
    ! [X0,X1] :
      ( k2_xboole_0(k1_tarski(X0),X1) = X1
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f4,axiom,(
    ! [X0,X1] : k5_xboole_0(X0,k4_xboole_0(X1,X0)) = k2_xboole_0(X0,X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f40,plain,(
    ! [X0,X1] : k5_xboole_0(X0,k4_xboole_0(X1,X0)) = k2_xboole_0(X0,X1) ),
    inference(cnf_transformation,[],[f4])).

fof(f3,axiom,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f39,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f3])).

fof(f11,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f48,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1)) ),
    inference(cnf_transformation,[],[f11])).

fof(f56,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k1_setfam_1(k2_tarski(X0,X1))) ),
    inference(definition_unfolding,[],[f39,f48])).

fof(f57,plain,(
    ! [X0,X1] : k5_xboole_0(X0,k5_xboole_0(X1,k1_setfam_1(k2_tarski(X1,X0)))) = k2_xboole_0(X0,X1) ),
    inference(definition_unfolding,[],[f40,f56])).

fof(f58,plain,(
    ! [X0,X1] :
      ( k5_xboole_0(k1_tarski(X0),k5_xboole_0(X1,k1_setfam_1(k2_tarski(X1,k1_tarski(X0))))) = X1
      | ~ r2_hidden(X0,X1) ) ),
    inference(definition_unfolding,[],[f41,f57])).

fof(f13,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
     => ( r1_tarski(k1_setfam_1(X1),k1_setfam_1(X0))
        | k1_xboole_0 = X0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f22,plain,(
    ! [X0,X1] :
      ( r1_tarski(k1_setfam_1(X1),k1_setfam_1(X0))
      | k1_xboole_0 = X0
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f23,plain,(
    ! [X0,X1] :
      ( r1_tarski(k1_setfam_1(X1),k1_setfam_1(X0))
      | k1_xboole_0 = X0
      | ~ r1_tarski(X0,X1) ) ),
    inference(flattening,[],[f22])).

fof(f51,plain,(
    ! [X0,X1] :
      ( r1_tarski(k1_setfam_1(X1),k1_setfam_1(X0))
      | k1_xboole_0 = X0
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f14,conjecture,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0)))
     => ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(X0)))
         => ( r1_tarski(X1,X2)
           => r1_tarski(k8_setfam_1(X0,X2),k8_setfam_1(X0,X1)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f15,negated_conjecture,(
    ~ ! [X0,X1] :
        ( m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0)))
       => ! [X2] :
            ( m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(X0)))
           => ( r1_tarski(X1,X2)
             => r1_tarski(k8_setfam_1(X0,X2),k8_setfam_1(X0,X1)) ) ) ) ),
    inference(negated_conjecture,[],[f14])).

fof(f24,plain,(
    ? [X0,X1] :
      ( ? [X2] :
          ( ~ r1_tarski(k8_setfam_1(X0,X2),k8_setfam_1(X0,X1))
          & r1_tarski(X1,X2)
          & m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(X0))) )
      & m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) ) ),
    inference(ennf_transformation,[],[f15])).

fof(f25,plain,(
    ? [X0,X1] :
      ( ? [X2] :
          ( ~ r1_tarski(k8_setfam_1(X0,X2),k8_setfam_1(X0,X1))
          & r1_tarski(X1,X2)
          & m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(X0))) )
      & m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) ) ),
    inference(flattening,[],[f24])).

fof(f34,plain,(
    ! [X0,X1] :
      ( ? [X2] :
          ( ~ r1_tarski(k8_setfam_1(X0,X2),k8_setfam_1(X0,X1))
          & r1_tarski(X1,X2)
          & m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(X0))) )
     => ( ~ r1_tarski(k8_setfam_1(X0,sK4),k8_setfam_1(X0,X1))
        & r1_tarski(X1,sK4)
        & m1_subset_1(sK4,k1_zfmisc_1(k1_zfmisc_1(X0))) ) ) ),
    introduced(choice_axiom,[])).

fof(f33,plain,
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

fof(f35,plain,
    ( ~ r1_tarski(k8_setfam_1(sK2,sK4),k8_setfam_1(sK2,sK3))
    & r1_tarski(sK3,sK4)
    & m1_subset_1(sK4,k1_zfmisc_1(k1_zfmisc_1(sK2)))
    & m1_subset_1(sK3,k1_zfmisc_1(k1_zfmisc_1(sK2))) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2,sK3,sK4])],[f25,f34,f33])).

fof(f52,plain,(
    m1_subset_1(sK3,k1_zfmisc_1(k1_zfmisc_1(sK2))) ),
    inference(cnf_transformation,[],[f35])).

fof(f8,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0)))
     => ( ( k1_xboole_0 = X1
         => k8_setfam_1(X0,X1) = X0 )
        & ( k1_xboole_0 != X1
         => k8_setfam_1(X0,X1) = k6_setfam_1(X0,X1) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f19,plain,(
    ! [X0,X1] :
      ( ( ( k8_setfam_1(X0,X1) = X0
          | k1_xboole_0 != X1 )
        & ( k8_setfam_1(X0,X1) = k6_setfam_1(X0,X1)
          | k1_xboole_0 = X1 ) )
      | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f44,plain,(
    ! [X0,X1] :
      ( k8_setfam_1(X0,X1) = k6_setfam_1(X0,X1)
      | k1_xboole_0 = X1
      | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f10,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0)))
     => k6_setfam_1(X0,X1) = k1_setfam_1(X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f21,plain,(
    ! [X0,X1] :
      ( k6_setfam_1(X0,X1) = k1_setfam_1(X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f47,plain,(
    ! [X0,X1] :
      ( k6_setfam_1(X0,X1) = k1_setfam_1(X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f53,plain,(
    m1_subset_1(sK4,k1_zfmisc_1(k1_zfmisc_1(sK2))) ),
    inference(cnf_transformation,[],[f35])).

fof(f55,plain,(
    ~ r1_tarski(k8_setfam_1(sK2,sK4),k8_setfam_1(sK2,sK3)) ),
    inference(cnf_transformation,[],[f35])).

fof(f54,plain,(
    r1_tarski(sK3,sK4) ),
    inference(cnf_transformation,[],[f35])).

fof(f45,plain,(
    ! [X0,X1] :
      ( k8_setfam_1(X0,X1) = X0
      | k1_xboole_0 != X1
      | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f60,plain,(
    ! [X0] :
      ( k8_setfam_1(X0,k1_xboole_0) = X0
      | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_zfmisc_1(X0))) ) ),
    inference(equality_resolution,[],[f45])).

fof(f9,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0)))
     => m1_subset_1(k8_setfam_1(X0,X1),k1_zfmisc_1(X0)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f20,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k8_setfam_1(X0,X1),k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f46,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k8_setfam_1(X0,X1),k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f12,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f32,plain,(
    ! [X0,X1] :
      ( ( m1_subset_1(X0,k1_zfmisc_1(X1))
        | ~ r1_tarski(X0,X1) )
      & ( r1_tarski(X0,X1)
        | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ) ) ),
    inference(nnf_transformation,[],[f12])).

fof(f49,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ) ),
    inference(cnf_transformation,[],[f32])).

fof(f7,axiom,(
    ! [X0] :
      ( v1_xboole_0(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(X0))
         => v1_xboole_0(X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f18,plain,(
    ! [X0] :
      ( ! [X1] :
          ( v1_xboole_0(X1)
          | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) )
      | ~ v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f43,plain,(
    ! [X0,X1] :
      ( v1_xboole_0(X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | ~ v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f50,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f32])).

fof(f6,axiom,(
    ! [X0,X1] : k1_xboole_0 != k2_xboole_0(k1_tarski(X0),X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f42,plain,(
    ! [X0,X1] : k1_xboole_0 != k2_xboole_0(k1_tarski(X0),X1) ),
    inference(cnf_transformation,[],[f6])).

fof(f59,plain,(
    ! [X0,X1] : k1_xboole_0 != k5_xboole_0(k1_tarski(X0),k5_xboole_0(X1,k1_setfam_1(k2_tarski(X1,k1_tarski(X0))))) ),
    inference(definition_unfolding,[],[f42,f57])).

fof(f2,axiom,(
    ! [X0] :
      ~ ( ! [X1] : ~ r2_hidden(X1,X0)
        & k1_xboole_0 != X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f16,plain,(
    ! [X0] :
      ( ? [X1] : r2_hidden(X1,X0)
      | k1_xboole_0 = X0 ) ),
    inference(ennf_transformation,[],[f2])).

fof(f30,plain,(
    ! [X0] :
      ( ? [X1] : r2_hidden(X1,X0)
     => r2_hidden(sK1(X0),X0) ) ),
    introduced(choice_axiom,[])).

fof(f31,plain,(
    ! [X0] :
      ( r2_hidden(sK1(X0),X0)
      | k1_xboole_0 = X0 ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1])],[f16,f30])).

fof(f38,plain,(
    ! [X0] :
      ( r2_hidden(sK1(X0),X0)
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f31])).

fof(f36,plain,(
    ! [X2,X0] :
      ( ~ r2_hidden(X2,X0)
      | ~ v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f29])).

cnf(c_0,plain,
    ( r2_hidden(sK0(X0),X0)
    | v1_xboole_0(X0) ),
    inference(cnf_transformation,[],[f37])).

cnf(c_667,plain,
    ( r2_hidden(sK0(X0),X0) = iProver_top
    | v1_xboole_0(X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_0])).

cnf(c_3,plain,
    ( ~ r2_hidden(X0,X1)
    | k5_xboole_0(k1_tarski(X0),k5_xboole_0(X1,k1_setfam_1(k2_tarski(X1,k1_tarski(X0))))) = X1 ),
    inference(cnf_transformation,[],[f58])).

cnf(c_664,plain,
    ( k5_xboole_0(k1_tarski(X0),k5_xboole_0(X1,k1_setfam_1(k2_tarski(X1,k1_tarski(X0))))) = X1
    | r2_hidden(X0,X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3])).

cnf(c_1603,plain,
    ( k5_xboole_0(k1_tarski(sK0(X0)),k5_xboole_0(X0,k1_setfam_1(k2_tarski(X0,k1_tarski(sK0(X0)))))) = X0
    | v1_xboole_0(X0) = iProver_top ),
    inference(superposition,[status(thm)],[c_667,c_664])).

cnf(c_12,plain,
    ( ~ r1_tarski(X0,X1)
    | r1_tarski(k1_setfam_1(X1),k1_setfam_1(X0))
    | k1_xboole_0 = X0 ),
    inference(cnf_transformation,[],[f51])).

cnf(c_657,plain,
    ( k1_xboole_0 = X0
    | r1_tarski(X0,X1) != iProver_top
    | r1_tarski(k1_setfam_1(X1),k1_setfam_1(X0)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_12])).

cnf(c_16,negated_conjecture,
    ( m1_subset_1(sK3,k1_zfmisc_1(k1_zfmisc_1(sK2))) ),
    inference(cnf_transformation,[],[f52])).

cnf(c_653,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(k1_zfmisc_1(sK2))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_16])).

cnf(c_7,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k1_zfmisc_1(X1)))
    | k6_setfam_1(X1,X0) = k8_setfam_1(X1,X0)
    | k1_xboole_0 = X0 ),
    inference(cnf_transformation,[],[f44])).

cnf(c_662,plain,
    ( k6_setfam_1(X0,X1) = k8_setfam_1(X0,X1)
    | k1_xboole_0 = X1
    | m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_7])).

cnf(c_1621,plain,
    ( k6_setfam_1(sK2,sK3) = k8_setfam_1(sK2,sK3)
    | sK3 = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_653,c_662])).

cnf(c_9,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k1_zfmisc_1(X1)))
    | k6_setfam_1(X1,X0) = k1_setfam_1(X0) ),
    inference(cnf_transformation,[],[f47])).

cnf(c_660,plain,
    ( k6_setfam_1(X0,X1) = k1_setfam_1(X1)
    | m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_9])).

cnf(c_1544,plain,
    ( k6_setfam_1(sK2,sK3) = k1_setfam_1(sK3) ),
    inference(superposition,[status(thm)],[c_653,c_660])).

cnf(c_1896,plain,
    ( k8_setfam_1(sK2,sK3) = k1_setfam_1(sK3)
    | sK3 = k1_xboole_0 ),
    inference(light_normalisation,[status(thm)],[c_1621,c_1544])).

cnf(c_15,negated_conjecture,
    ( m1_subset_1(sK4,k1_zfmisc_1(k1_zfmisc_1(sK2))) ),
    inference(cnf_transformation,[],[f53])).

cnf(c_654,plain,
    ( m1_subset_1(sK4,k1_zfmisc_1(k1_zfmisc_1(sK2))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_15])).

cnf(c_1620,plain,
    ( k6_setfam_1(sK2,sK4) = k8_setfam_1(sK2,sK4)
    | sK4 = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_654,c_662])).

cnf(c_1543,plain,
    ( k6_setfam_1(sK2,sK4) = k1_setfam_1(sK4) ),
    inference(superposition,[status(thm)],[c_654,c_660])).

cnf(c_1748,plain,
    ( k8_setfam_1(sK2,sK4) = k1_setfam_1(sK4)
    | sK4 = k1_xboole_0 ),
    inference(light_normalisation,[status(thm)],[c_1620,c_1543])).

cnf(c_13,negated_conjecture,
    ( ~ r1_tarski(k8_setfam_1(sK2,sK4),k8_setfam_1(sK2,sK3)) ),
    inference(cnf_transformation,[],[f55])).

cnf(c_656,plain,
    ( r1_tarski(k8_setfam_1(sK2,sK4),k8_setfam_1(sK2,sK3)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_13])).

cnf(c_1752,plain,
    ( sK4 = k1_xboole_0
    | r1_tarski(k1_setfam_1(sK4),k8_setfam_1(sK2,sK3)) != iProver_top ),
    inference(superposition,[status(thm)],[c_1748,c_656])).

cnf(c_1900,plain,
    ( sK3 = k1_xboole_0
    | sK4 = k1_xboole_0
    | r1_tarski(k1_setfam_1(sK4),k1_setfam_1(sK3)) != iProver_top ),
    inference(superposition,[status(thm)],[c_1896,c_1752])).

cnf(c_2060,plain,
    ( sK3 = k1_xboole_0
    | sK4 = k1_xboole_0
    | r1_tarski(sK3,sK4) != iProver_top ),
    inference(superposition,[status(thm)],[c_657,c_1900])).

cnf(c_14,negated_conjecture,
    ( r1_tarski(sK3,sK4) ),
    inference(cnf_transformation,[],[f54])).

cnf(c_19,plain,
    ( r1_tarski(sK3,sK4) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_14])).

cnf(c_2063,plain,
    ( sK4 = k1_xboole_0
    | sK3 = k1_xboole_0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_2060,c_19])).

cnf(c_2064,plain,
    ( sK3 = k1_xboole_0
    | sK4 = k1_xboole_0 ),
    inference(renaming,[status(thm)],[c_2063])).

cnf(c_2072,plain,
    ( sK4 = k1_xboole_0
    | r1_tarski(k8_setfam_1(sK2,sK4),k8_setfam_1(sK2,k1_xboole_0)) != iProver_top ),
    inference(superposition,[status(thm)],[c_2064,c_656])).

cnf(c_2073,plain,
    ( sK4 = k1_xboole_0
    | m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_zfmisc_1(sK2))) = iProver_top ),
    inference(superposition,[status(thm)],[c_2064,c_653])).

cnf(c_18,plain,
    ( m1_subset_1(sK4,k1_zfmisc_1(k1_zfmisc_1(sK2))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_15])).

cnf(c_260,plain,
    ( X0 = X0 ),
    theory(equality)).

cnf(c_279,plain,
    ( k1_xboole_0 = k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_260])).

cnf(c_261,plain,
    ( X0 != X1
    | X2 != X1
    | X2 = X0 ),
    theory(equality)).

cnf(c_872,plain,
    ( X0 != X1
    | X0 = sK4
    | sK4 != X1 ),
    inference(instantiation,[status(thm)],[c_261])).

cnf(c_873,plain,
    ( sK4 != k1_xboole_0
    | k1_xboole_0 = sK4
    | k1_xboole_0 != k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_872])).

cnf(c_267,plain,
    ( ~ m1_subset_1(X0,X1)
    | m1_subset_1(X2,X3)
    | X2 != X0
    | X3 != X1 ),
    theory(equality)).

cnf(c_792,plain,
    ( m1_subset_1(X0,X1)
    | ~ m1_subset_1(sK4,k1_zfmisc_1(k1_zfmisc_1(sK2)))
    | X1 != k1_zfmisc_1(k1_zfmisc_1(sK2))
    | X0 != sK4 ),
    inference(instantiation,[status(thm)],[c_267])).

cnf(c_947,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(k1_zfmisc_1(sK2)))
    | ~ m1_subset_1(sK4,k1_zfmisc_1(k1_zfmisc_1(sK2)))
    | X0 != sK4
    | k1_zfmisc_1(k1_zfmisc_1(sK2)) != k1_zfmisc_1(k1_zfmisc_1(sK2)) ),
    inference(instantiation,[status(thm)],[c_792])).

cnf(c_949,plain,
    ( X0 != sK4
    | k1_zfmisc_1(k1_zfmisc_1(sK2)) != k1_zfmisc_1(k1_zfmisc_1(sK2))
    | m1_subset_1(X0,k1_zfmisc_1(k1_zfmisc_1(sK2))) = iProver_top
    | m1_subset_1(sK4,k1_zfmisc_1(k1_zfmisc_1(sK2))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_947])).

cnf(c_951,plain,
    ( k1_zfmisc_1(k1_zfmisc_1(sK2)) != k1_zfmisc_1(k1_zfmisc_1(sK2))
    | k1_xboole_0 != sK4
    | m1_subset_1(sK4,k1_zfmisc_1(k1_zfmisc_1(sK2))) != iProver_top
    | m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_zfmisc_1(sK2))) = iProver_top ),
    inference(instantiation,[status(thm)],[c_949])).

cnf(c_948,plain,
    ( k1_zfmisc_1(k1_zfmisc_1(sK2)) = k1_zfmisc_1(k1_zfmisc_1(sK2)) ),
    inference(instantiation,[status(thm)],[c_260])).

cnf(c_2297,plain,
    ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_zfmisc_1(sK2))) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_2073,c_18,c_279,c_873,c_951,c_948])).

cnf(c_6,plain,
    ( ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_zfmisc_1(X0)))
    | k8_setfam_1(X0,k1_xboole_0) = X0 ),
    inference(cnf_transformation,[],[f60])).

cnf(c_663,plain,
    ( k8_setfam_1(X0,k1_xboole_0) = X0
    | m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_zfmisc_1(X0))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_6])).

cnf(c_2303,plain,
    ( k8_setfam_1(sK2,k1_xboole_0) = sK2 ),
    inference(superposition,[status(thm)],[c_2297,c_663])).

cnf(c_2379,plain,
    ( sK4 = k1_xboole_0
    | r1_tarski(k8_setfam_1(sK2,sK4),sK2) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_2072,c_2303])).

cnf(c_8,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k1_zfmisc_1(X1)))
    | m1_subset_1(k8_setfam_1(X1,X0),k1_zfmisc_1(X1)) ),
    inference(cnf_transformation,[],[f46])).

cnf(c_776,plain,
    ( m1_subset_1(k8_setfam_1(sK2,sK4),k1_zfmisc_1(sK2))
    | ~ m1_subset_1(sK4,k1_zfmisc_1(k1_zfmisc_1(sK2))) ),
    inference(instantiation,[status(thm)],[c_8])).

cnf(c_777,plain,
    ( m1_subset_1(k8_setfam_1(sK2,sK4),k1_zfmisc_1(sK2)) = iProver_top
    | m1_subset_1(sK4,k1_zfmisc_1(k1_zfmisc_1(sK2))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_776])).

cnf(c_11,plain,
    ( r1_tarski(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ),
    inference(cnf_transformation,[],[f49])).

cnf(c_834,plain,
    ( r1_tarski(k8_setfam_1(sK2,sK4),sK2)
    | ~ m1_subset_1(k8_setfam_1(sK2,sK4),k1_zfmisc_1(sK2)) ),
    inference(instantiation,[status(thm)],[c_11])).

cnf(c_835,plain,
    ( r1_tarski(k8_setfam_1(sK2,sK4),sK2) = iProver_top
    | m1_subset_1(k8_setfam_1(sK2,sK4),k1_zfmisc_1(sK2)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_834])).

cnf(c_2383,plain,
    ( sK4 = k1_xboole_0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_2379,c_18,c_777,c_835])).

cnf(c_655,plain,
    ( r1_tarski(sK3,sK4) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_14])).

cnf(c_5,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | ~ v1_xboole_0(X1)
    | v1_xboole_0(X0) ),
    inference(cnf_transformation,[],[f43])).

cnf(c_10,plain,
    ( ~ r1_tarski(X0,X1)
    | m1_subset_1(X0,k1_zfmisc_1(X1)) ),
    inference(cnf_transformation,[],[f50])).

cnf(c_131,plain,
    ( ~ r1_tarski(X0,X1)
    | m1_subset_1(X0,k1_zfmisc_1(X1)) ),
    inference(prop_impl,[status(thm)],[c_10])).

cnf(c_156,plain,
    ( ~ r1_tarski(X0,X1)
    | ~ v1_xboole_0(X1)
    | v1_xboole_0(X0) ),
    inference(bin_hyper_res,[status(thm)],[c_5,c_131])).

cnf(c_652,plain,
    ( r1_tarski(X0,X1) != iProver_top
    | v1_xboole_0(X1) != iProver_top
    | v1_xboole_0(X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_156])).

cnf(c_1001,plain,
    ( v1_xboole_0(sK3) = iProver_top
    | v1_xboole_0(sK4) != iProver_top ),
    inference(superposition,[status(thm)],[c_655,c_652])).

cnf(c_2389,plain,
    ( v1_xboole_0(sK3) = iProver_top
    | v1_xboole_0(k1_xboole_0) != iProver_top ),
    inference(demodulation,[status(thm)],[c_2383,c_1001])).

cnf(c_3434,plain,
    ( k5_xboole_0(k1_tarski(sK0(k1_xboole_0)),k5_xboole_0(k1_xboole_0,k1_setfam_1(k2_tarski(k1_xboole_0,k1_tarski(sK0(k1_xboole_0)))))) = k1_xboole_0
    | v1_xboole_0(sK3) = iProver_top ),
    inference(superposition,[status(thm)],[c_1603,c_2389])).

cnf(c_4,plain,
    ( k5_xboole_0(k1_tarski(X0),k5_xboole_0(X1,k1_setfam_1(k2_tarski(X1,k1_tarski(X0))))) != k1_xboole_0 ),
    inference(cnf_transformation,[],[f59])).

cnf(c_3833,plain,
    ( v1_xboole_0(sK3) = iProver_top ),
    inference(forward_subsumption_resolution,[status(thm)],[c_3434,c_4])).

cnf(c_2,plain,
    ( r2_hidden(sK1(X0),X0)
    | k1_xboole_0 = X0 ),
    inference(cnf_transformation,[],[f38])).

cnf(c_665,plain,
    ( k1_xboole_0 = X0
    | r2_hidden(sK1(X0),X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2])).

cnf(c_1,plain,
    ( ~ r2_hidden(X0,X1)
    | ~ v1_xboole_0(X1) ),
    inference(cnf_transformation,[],[f36])).

cnf(c_666,plain,
    ( r2_hidden(X0,X1) != iProver_top
    | v1_xboole_0(X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1])).

cnf(c_1016,plain,
    ( k1_xboole_0 = X0
    | v1_xboole_0(X0) != iProver_top ),
    inference(superposition,[status(thm)],[c_665,c_666])).

cnf(c_3836,plain,
    ( sK3 = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_3833,c_1016])).

cnf(c_2391,plain,
    ( r1_tarski(k8_setfam_1(sK2,k1_xboole_0),k8_setfam_1(sK2,sK3)) != iProver_top ),
    inference(demodulation,[status(thm)],[c_2383,c_656])).

cnf(c_2397,plain,
    ( r1_tarski(sK2,k8_setfam_1(sK2,sK3)) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_2391,c_2303])).

cnf(c_3913,plain,
    ( r1_tarski(sK2,k8_setfam_1(sK2,k1_xboole_0)) != iProver_top ),
    inference(demodulation,[status(thm)],[c_3836,c_2397])).

cnf(c_3923,plain,
    ( r1_tarski(sK2,sK2) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_3913,c_2303])).

cnf(c_661,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(k1_zfmisc_1(X1))) != iProver_top
    | m1_subset_1(k8_setfam_1(X1,X0),k1_zfmisc_1(X1)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_8])).

cnf(c_2314,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(sK2)) = iProver_top
    | m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_zfmisc_1(sK2))) != iProver_top ),
    inference(superposition,[status(thm)],[c_2303,c_661])).

cnf(c_2791,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(sK2)) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_2314,c_18,c_279,c_873,c_951,c_948,c_2073])).

cnf(c_658,plain,
    ( r1_tarski(X0,X1) = iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(X1)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_11])).

cnf(c_2796,plain,
    ( r1_tarski(sK2,sK2) = iProver_top ),
    inference(superposition,[status(thm)],[c_2791,c_658])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_3923,c_2796])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : iproveropt_run.sh %d %s
% 0.14/0.34  % Computer   : n023.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % WCLimit    : 600
% 0.14/0.34  % DateTime   : Tue Dec  1 12:38:51 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.35  % Running in FOF mode
% 2.13/0.99  % SZS status Started for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.13/0.99  
% 2.13/0.99  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 2.13/0.99  
% 2.13/0.99  ------  iProver source info
% 2.13/0.99  
% 2.13/0.99  git: date: 2020-06-30 10:37:57 +0100
% 2.13/0.99  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 2.13/0.99  git: non_committed_changes: false
% 2.13/0.99  git: last_make_outside_of_git: false
% 2.13/0.99  
% 2.13/0.99  ------ 
% 2.13/0.99  
% 2.13/0.99  ------ Input Options
% 2.13/0.99  
% 2.13/0.99  --out_options                           all
% 2.13/0.99  --tptp_safe_out                         true
% 2.13/0.99  --problem_path                          ""
% 2.13/0.99  --include_path                          ""
% 2.13/0.99  --clausifier                            res/vclausify_rel
% 2.13/0.99  --clausifier_options                    --mode clausify
% 2.13/0.99  --stdin                                 false
% 2.13/0.99  --stats_out                             all
% 2.13/0.99  
% 2.13/0.99  ------ General Options
% 2.13/0.99  
% 2.13/0.99  --fof                                   false
% 2.13/0.99  --time_out_real                         305.
% 2.13/0.99  --time_out_virtual                      -1.
% 2.13/0.99  --symbol_type_check                     false
% 2.13/0.99  --clausify_out                          false
% 2.13/0.99  --sig_cnt_out                           false
% 2.13/0.99  --trig_cnt_out                          false
% 2.13/0.99  --trig_cnt_out_tolerance                1.
% 2.13/0.99  --trig_cnt_out_sk_spl                   false
% 2.13/0.99  --abstr_cl_out                          false
% 2.13/0.99  
% 2.13/0.99  ------ Global Options
% 2.13/0.99  
% 2.13/0.99  --schedule                              default
% 2.13/0.99  --add_important_lit                     false
% 2.13/0.99  --prop_solver_per_cl                    1000
% 2.13/0.99  --min_unsat_core                        false
% 2.13/0.99  --soft_assumptions                      false
% 2.13/0.99  --soft_lemma_size                       3
% 2.13/0.99  --prop_impl_unit_size                   0
% 2.13/0.99  --prop_impl_unit                        []
% 2.13/0.99  --share_sel_clauses                     true
% 2.13/0.99  --reset_solvers                         false
% 2.13/0.99  --bc_imp_inh                            [conj_cone]
% 2.13/0.99  --conj_cone_tolerance                   3.
% 2.13/0.99  --extra_neg_conj                        none
% 2.13/0.99  --large_theory_mode                     true
% 2.13/0.99  --prolific_symb_bound                   200
% 2.13/0.99  --lt_threshold                          2000
% 2.13/0.99  --clause_weak_htbl                      true
% 2.13/0.99  --gc_record_bc_elim                     false
% 2.13/0.99  
% 2.13/0.99  ------ Preprocessing Options
% 2.13/0.99  
% 2.13/0.99  --preprocessing_flag                    true
% 2.13/0.99  --time_out_prep_mult                    0.1
% 2.13/0.99  --splitting_mode                        input
% 2.13/0.99  --splitting_grd                         true
% 2.13/0.99  --splitting_cvd                         false
% 2.13/0.99  --splitting_cvd_svl                     false
% 2.13/0.99  --splitting_nvd                         32
% 2.13/0.99  --sub_typing                            true
% 2.13/0.99  --prep_gs_sim                           true
% 2.13/0.99  --prep_unflatten                        true
% 2.13/0.99  --prep_res_sim                          true
% 2.13/0.99  --prep_upred                            true
% 2.13/0.99  --prep_sem_filter                       exhaustive
% 2.13/0.99  --prep_sem_filter_out                   false
% 2.13/0.99  --pred_elim                             true
% 2.13/0.99  --res_sim_input                         true
% 2.13/0.99  --eq_ax_congr_red                       true
% 2.13/0.99  --pure_diseq_elim                       true
% 2.13/0.99  --brand_transform                       false
% 2.13/0.99  --non_eq_to_eq                          false
% 2.13/0.99  --prep_def_merge                        true
% 2.13/0.99  --prep_def_merge_prop_impl              false
% 2.13/0.99  --prep_def_merge_mbd                    true
% 2.13/0.99  --prep_def_merge_tr_red                 false
% 2.13/0.99  --prep_def_merge_tr_cl                  false
% 2.13/0.99  --smt_preprocessing                     true
% 2.13/0.99  --smt_ac_axioms                         fast
% 2.13/0.99  --preprocessed_out                      false
% 2.13/0.99  --preprocessed_stats                    false
% 2.13/0.99  
% 2.13/0.99  ------ Abstraction refinement Options
% 2.13/0.99  
% 2.13/0.99  --abstr_ref                             []
% 2.13/0.99  --abstr_ref_prep                        false
% 2.13/0.99  --abstr_ref_until_sat                   false
% 2.13/0.99  --abstr_ref_sig_restrict                funpre
% 2.13/0.99  --abstr_ref_af_restrict_to_split_sk     false
% 2.13/0.99  --abstr_ref_under                       []
% 2.13/0.99  
% 2.13/0.99  ------ SAT Options
% 2.13/0.99  
% 2.13/0.99  --sat_mode                              false
% 2.13/0.99  --sat_fm_restart_options                ""
% 2.13/0.99  --sat_gr_def                            false
% 2.13/0.99  --sat_epr_types                         true
% 2.13/0.99  --sat_non_cyclic_types                  false
% 2.13/0.99  --sat_finite_models                     false
% 2.13/0.99  --sat_fm_lemmas                         false
% 2.13/0.99  --sat_fm_prep                           false
% 2.13/0.99  --sat_fm_uc_incr                        true
% 2.13/0.99  --sat_out_model                         small
% 2.13/0.99  --sat_out_clauses                       false
% 2.13/0.99  
% 2.13/0.99  ------ QBF Options
% 2.13/0.99  
% 2.13/0.99  --qbf_mode                              false
% 2.13/0.99  --qbf_elim_univ                         false
% 2.13/0.99  --qbf_dom_inst                          none
% 2.13/0.99  --qbf_dom_pre_inst                      false
% 2.13/0.99  --qbf_sk_in                             false
% 2.13/0.99  --qbf_pred_elim                         true
% 2.13/0.99  --qbf_split                             512
% 2.13/0.99  
% 2.13/0.99  ------ BMC1 Options
% 2.13/0.99  
% 2.13/0.99  --bmc1_incremental                      false
% 2.13/0.99  --bmc1_axioms                           reachable_all
% 2.13/0.99  --bmc1_min_bound                        0
% 2.13/0.99  --bmc1_max_bound                        -1
% 2.13/0.99  --bmc1_max_bound_default                -1
% 2.13/0.99  --bmc1_symbol_reachability              true
% 2.13/0.99  --bmc1_property_lemmas                  false
% 2.13/0.99  --bmc1_k_induction                      false
% 2.13/0.99  --bmc1_non_equiv_states                 false
% 2.13/0.99  --bmc1_deadlock                         false
% 2.13/0.99  --bmc1_ucm                              false
% 2.13/0.99  --bmc1_add_unsat_core                   none
% 2.13/0.99  --bmc1_unsat_core_children              false
% 2.13/0.99  --bmc1_unsat_core_extrapolate_axioms    false
% 2.13/0.99  --bmc1_out_stat                         full
% 2.13/0.99  --bmc1_ground_init                      false
% 2.13/0.99  --bmc1_pre_inst_next_state              false
% 2.13/0.99  --bmc1_pre_inst_state                   false
% 2.13/0.99  --bmc1_pre_inst_reach_state             false
% 2.13/0.99  --bmc1_out_unsat_core                   false
% 2.13/0.99  --bmc1_aig_witness_out                  false
% 2.13/0.99  --bmc1_verbose                          false
% 2.13/0.99  --bmc1_dump_clauses_tptp                false
% 2.13/0.99  --bmc1_dump_unsat_core_tptp             false
% 2.13/0.99  --bmc1_dump_file                        -
% 2.13/0.99  --bmc1_ucm_expand_uc_limit              128
% 2.13/0.99  --bmc1_ucm_n_expand_iterations          6
% 2.13/0.99  --bmc1_ucm_extend_mode                  1
% 2.13/0.99  --bmc1_ucm_init_mode                    2
% 2.13/0.99  --bmc1_ucm_cone_mode                    none
% 2.13/0.99  --bmc1_ucm_reduced_relation_type        0
% 2.13/0.99  --bmc1_ucm_relax_model                  4
% 2.13/0.99  --bmc1_ucm_full_tr_after_sat            true
% 2.13/0.99  --bmc1_ucm_expand_neg_assumptions       false
% 2.13/0.99  --bmc1_ucm_layered_model                none
% 2.13/0.99  --bmc1_ucm_max_lemma_size               10
% 2.13/0.99  
% 2.13/0.99  ------ AIG Options
% 2.13/0.99  
% 2.13/0.99  --aig_mode                              false
% 2.13/0.99  
% 2.13/0.99  ------ Instantiation Options
% 2.13/0.99  
% 2.13/0.99  --instantiation_flag                    true
% 2.13/0.99  --inst_sos_flag                         false
% 2.13/0.99  --inst_sos_phase                        true
% 2.13/0.99  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 2.13/0.99  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 2.13/0.99  --inst_lit_sel_side                     num_symb
% 2.13/0.99  --inst_solver_per_active                1400
% 2.13/0.99  --inst_solver_calls_frac                1.
% 2.13/0.99  --inst_passive_queue_type               priority_queues
% 2.13/0.99  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 2.13/0.99  --inst_passive_queues_freq              [25;2]
% 2.13/0.99  --inst_dismatching                      true
% 2.13/0.99  --inst_eager_unprocessed_to_passive     true
% 2.13/0.99  --inst_prop_sim_given                   true
% 2.13/0.99  --inst_prop_sim_new                     false
% 2.13/0.99  --inst_subs_new                         false
% 2.13/0.99  --inst_eq_res_simp                      false
% 2.13/0.99  --inst_subs_given                       false
% 2.13/0.99  --inst_orphan_elimination               true
% 2.13/0.99  --inst_learning_loop_flag               true
% 2.13/0.99  --inst_learning_start                   3000
% 2.13/0.99  --inst_learning_factor                  2
% 2.13/0.99  --inst_start_prop_sim_after_learn       3
% 2.13/0.99  --inst_sel_renew                        solver
% 2.13/0.99  --inst_lit_activity_flag                true
% 2.13/0.99  --inst_restr_to_given                   false
% 2.13/0.99  --inst_activity_threshold               500
% 2.13/0.99  --inst_out_proof                        true
% 2.13/0.99  
% 2.13/0.99  ------ Resolution Options
% 2.13/0.99  
% 2.13/0.99  --resolution_flag                       true
% 2.13/0.99  --res_lit_sel                           adaptive
% 2.13/0.99  --res_lit_sel_side                      none
% 2.13/0.99  --res_ordering                          kbo
% 2.13/0.99  --res_to_prop_solver                    active
% 2.13/0.99  --res_prop_simpl_new                    false
% 2.13/0.99  --res_prop_simpl_given                  true
% 2.13/0.99  --res_passive_queue_type                priority_queues
% 2.13/0.99  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 2.13/0.99  --res_passive_queues_freq               [15;5]
% 2.13/0.99  --res_forward_subs                      full
% 2.13/0.99  --res_backward_subs                     full
% 2.13/0.99  --res_forward_subs_resolution           true
% 2.13/0.99  --res_backward_subs_resolution          true
% 2.13/0.99  --res_orphan_elimination                true
% 2.13/0.99  --res_time_limit                        2.
% 2.13/0.99  --res_out_proof                         true
% 2.13/0.99  
% 2.13/0.99  ------ Superposition Options
% 2.13/0.99  
% 2.13/0.99  --superposition_flag                    true
% 2.13/0.99  --sup_passive_queue_type                priority_queues
% 2.13/0.99  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 2.13/0.99  --sup_passive_queues_freq               [8;1;4]
% 2.13/0.99  --demod_completeness_check              fast
% 2.13/0.99  --demod_use_ground                      true
% 2.13/0.99  --sup_to_prop_solver                    passive
% 2.13/0.99  --sup_prop_simpl_new                    true
% 2.13/0.99  --sup_prop_simpl_given                  true
% 2.13/0.99  --sup_fun_splitting                     false
% 2.13/0.99  --sup_smt_interval                      50000
% 2.13/0.99  
% 2.13/0.99  ------ Superposition Simplification Setup
% 2.13/0.99  
% 2.13/0.99  --sup_indices_passive                   []
% 2.13/0.99  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.13/0.99  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.13/0.99  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.13/0.99  --sup_full_triv                         [TrivRules;PropSubs]
% 2.13/0.99  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.13/0.99  --sup_full_bw                           [BwDemod]
% 2.13/0.99  --sup_immed_triv                        [TrivRules]
% 2.13/0.99  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 2.13/0.99  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.13/0.99  --sup_immed_bw_main                     []
% 2.13/0.99  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.13/0.99  --sup_input_triv                        [Unflattening;TrivRules]
% 2.13/0.99  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.13/0.99  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.13/0.99  
% 2.13/0.99  ------ Combination Options
% 2.13/0.99  
% 2.13/0.99  --comb_res_mult                         3
% 2.13/0.99  --comb_sup_mult                         2
% 2.13/0.99  --comb_inst_mult                        10
% 2.13/0.99  
% 2.13/0.99  ------ Debug Options
% 2.13/0.99  
% 2.13/0.99  --dbg_backtrace                         false
% 2.13/0.99  --dbg_dump_prop_clauses                 false
% 2.13/0.99  --dbg_dump_prop_clauses_file            -
% 2.13/0.99  --dbg_out_stat                          false
% 2.13/0.99  ------ Parsing...
% 2.13/0.99  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 2.13/0.99  
% 2.13/0.99  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe_e 
% 2.13/0.99  
% 2.13/0.99  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 2.13/0.99  
% 2.13/0.99  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 2.13/0.99  ------ Proving...
% 2.13/0.99  ------ Problem Properties 
% 2.13/0.99  
% 2.13/0.99  
% 2.13/0.99  clauses                                 17
% 2.13/0.99  conjectures                             4
% 2.13/0.99  EPR                                     3
% 2.13/0.99  Horn                                    13
% 2.13/0.99  unary                                   5
% 2.13/0.99  binary                                  9
% 2.13/0.99  lits                                    32
% 2.13/0.99  lits eq                                 8
% 2.13/0.99  fd_pure                                 0
% 2.13/0.99  fd_pseudo                               0
% 2.13/0.99  fd_cond                                 3
% 2.13/0.99  fd_pseudo_cond                          0
% 2.13/0.99  AC symbols                              0
% 2.13/0.99  
% 2.13/0.99  ------ Schedule dynamic 5 is on 
% 2.13/0.99  
% 2.13/0.99  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" Time Limit: 10.
% 2.13/0.99  
% 2.13/0.99  
% 2.13/0.99  ------ 
% 2.13/0.99  Current options:
% 2.13/0.99  ------ 
% 2.13/0.99  
% 2.13/0.99  ------ Input Options
% 2.13/0.99  
% 2.13/0.99  --out_options                           all
% 2.13/0.99  --tptp_safe_out                         true
% 2.13/0.99  --problem_path                          ""
% 2.13/0.99  --include_path                          ""
% 2.13/0.99  --clausifier                            res/vclausify_rel
% 2.13/0.99  --clausifier_options                    --mode clausify
% 2.13/0.99  --stdin                                 false
% 2.13/0.99  --stats_out                             all
% 2.13/0.99  
% 2.13/0.99  ------ General Options
% 2.13/0.99  
% 2.13/0.99  --fof                                   false
% 2.13/0.99  --time_out_real                         305.
% 2.13/0.99  --time_out_virtual                      -1.
% 2.13/0.99  --symbol_type_check                     false
% 2.13/0.99  --clausify_out                          false
% 2.13/0.99  --sig_cnt_out                           false
% 2.13/0.99  --trig_cnt_out                          false
% 2.13/0.99  --trig_cnt_out_tolerance                1.
% 2.13/0.99  --trig_cnt_out_sk_spl                   false
% 2.13/0.99  --abstr_cl_out                          false
% 2.13/0.99  
% 2.13/0.99  ------ Global Options
% 2.13/0.99  
% 2.13/0.99  --schedule                              default
% 2.13/0.99  --add_important_lit                     false
% 2.13/0.99  --prop_solver_per_cl                    1000
% 2.13/0.99  --min_unsat_core                        false
% 2.13/0.99  --soft_assumptions                      false
% 2.13/0.99  --soft_lemma_size                       3
% 2.13/0.99  --prop_impl_unit_size                   0
% 2.13/0.99  --prop_impl_unit                        []
% 2.13/0.99  --share_sel_clauses                     true
% 2.13/0.99  --reset_solvers                         false
% 2.13/0.99  --bc_imp_inh                            [conj_cone]
% 2.13/0.99  --conj_cone_tolerance                   3.
% 2.13/0.99  --extra_neg_conj                        none
% 2.13/0.99  --large_theory_mode                     true
% 2.13/0.99  --prolific_symb_bound                   200
% 2.13/0.99  --lt_threshold                          2000
% 2.13/0.99  --clause_weak_htbl                      true
% 2.13/0.99  --gc_record_bc_elim                     false
% 2.13/0.99  
% 2.13/0.99  ------ Preprocessing Options
% 2.13/0.99  
% 2.13/0.99  --preprocessing_flag                    true
% 2.13/0.99  --time_out_prep_mult                    0.1
% 2.13/0.99  --splitting_mode                        input
% 2.13/0.99  --splitting_grd                         true
% 2.13/0.99  --splitting_cvd                         false
% 2.13/0.99  --splitting_cvd_svl                     false
% 2.13/0.99  --splitting_nvd                         32
% 2.13/0.99  --sub_typing                            true
% 2.13/0.99  --prep_gs_sim                           true
% 2.13/0.99  --prep_unflatten                        true
% 2.13/0.99  --prep_res_sim                          true
% 2.13/0.99  --prep_upred                            true
% 2.13/0.99  --prep_sem_filter                       exhaustive
% 2.13/0.99  --prep_sem_filter_out                   false
% 2.13/0.99  --pred_elim                             true
% 2.13/0.99  --res_sim_input                         true
% 2.13/0.99  --eq_ax_congr_red                       true
% 2.13/0.99  --pure_diseq_elim                       true
% 2.13/0.99  --brand_transform                       false
% 2.13/0.99  --non_eq_to_eq                          false
% 2.13/0.99  --prep_def_merge                        true
% 2.13/0.99  --prep_def_merge_prop_impl              false
% 2.13/0.99  --prep_def_merge_mbd                    true
% 2.13/0.99  --prep_def_merge_tr_red                 false
% 2.13/0.99  --prep_def_merge_tr_cl                  false
% 2.13/0.99  --smt_preprocessing                     true
% 2.13/0.99  --smt_ac_axioms                         fast
% 2.13/0.99  --preprocessed_out                      false
% 2.13/0.99  --preprocessed_stats                    false
% 2.13/0.99  
% 2.13/0.99  ------ Abstraction refinement Options
% 2.13/0.99  
% 2.13/0.99  --abstr_ref                             []
% 2.13/0.99  --abstr_ref_prep                        false
% 2.13/0.99  --abstr_ref_until_sat                   false
% 2.13/0.99  --abstr_ref_sig_restrict                funpre
% 2.13/0.99  --abstr_ref_af_restrict_to_split_sk     false
% 2.13/0.99  --abstr_ref_under                       []
% 2.13/0.99  
% 2.13/0.99  ------ SAT Options
% 2.13/0.99  
% 2.13/0.99  --sat_mode                              false
% 2.13/0.99  --sat_fm_restart_options                ""
% 2.13/0.99  --sat_gr_def                            false
% 2.13/0.99  --sat_epr_types                         true
% 2.13/0.99  --sat_non_cyclic_types                  false
% 2.13/0.99  --sat_finite_models                     false
% 2.13/0.99  --sat_fm_lemmas                         false
% 2.13/0.99  --sat_fm_prep                           false
% 2.13/0.99  --sat_fm_uc_incr                        true
% 2.13/0.99  --sat_out_model                         small
% 2.13/0.99  --sat_out_clauses                       false
% 2.13/0.99  
% 2.13/0.99  ------ QBF Options
% 2.13/0.99  
% 2.13/0.99  --qbf_mode                              false
% 2.13/0.99  --qbf_elim_univ                         false
% 2.13/0.99  --qbf_dom_inst                          none
% 2.13/0.99  --qbf_dom_pre_inst                      false
% 2.13/0.99  --qbf_sk_in                             false
% 2.13/0.99  --qbf_pred_elim                         true
% 2.13/0.99  --qbf_split                             512
% 2.13/0.99  
% 2.13/0.99  ------ BMC1 Options
% 2.13/0.99  
% 2.13/0.99  --bmc1_incremental                      false
% 2.13/0.99  --bmc1_axioms                           reachable_all
% 2.13/0.99  --bmc1_min_bound                        0
% 2.13/0.99  --bmc1_max_bound                        -1
% 2.13/0.99  --bmc1_max_bound_default                -1
% 2.13/0.99  --bmc1_symbol_reachability              true
% 2.13/0.99  --bmc1_property_lemmas                  false
% 2.13/0.99  --bmc1_k_induction                      false
% 2.13/0.99  --bmc1_non_equiv_states                 false
% 2.13/0.99  --bmc1_deadlock                         false
% 2.13/0.99  --bmc1_ucm                              false
% 2.13/0.99  --bmc1_add_unsat_core                   none
% 2.13/0.99  --bmc1_unsat_core_children              false
% 2.13/0.99  --bmc1_unsat_core_extrapolate_axioms    false
% 2.13/0.99  --bmc1_out_stat                         full
% 2.13/0.99  --bmc1_ground_init                      false
% 2.13/0.99  --bmc1_pre_inst_next_state              false
% 2.13/0.99  --bmc1_pre_inst_state                   false
% 2.13/0.99  --bmc1_pre_inst_reach_state             false
% 2.13/0.99  --bmc1_out_unsat_core                   false
% 2.13/0.99  --bmc1_aig_witness_out                  false
% 2.13/0.99  --bmc1_verbose                          false
% 2.13/0.99  --bmc1_dump_clauses_tptp                false
% 2.13/0.99  --bmc1_dump_unsat_core_tptp             false
% 2.13/0.99  --bmc1_dump_file                        -
% 2.13/0.99  --bmc1_ucm_expand_uc_limit              128
% 2.13/0.99  --bmc1_ucm_n_expand_iterations          6
% 2.13/0.99  --bmc1_ucm_extend_mode                  1
% 2.13/0.99  --bmc1_ucm_init_mode                    2
% 2.13/0.99  --bmc1_ucm_cone_mode                    none
% 2.13/0.99  --bmc1_ucm_reduced_relation_type        0
% 2.13/0.99  --bmc1_ucm_relax_model                  4
% 2.13/0.99  --bmc1_ucm_full_tr_after_sat            true
% 2.13/0.99  --bmc1_ucm_expand_neg_assumptions       false
% 2.13/0.99  --bmc1_ucm_layered_model                none
% 2.13/0.99  --bmc1_ucm_max_lemma_size               10
% 2.13/0.99  
% 2.13/0.99  ------ AIG Options
% 2.13/0.99  
% 2.13/0.99  --aig_mode                              false
% 2.13/0.99  
% 2.13/0.99  ------ Instantiation Options
% 2.13/0.99  
% 2.13/0.99  --instantiation_flag                    true
% 2.13/0.99  --inst_sos_flag                         false
% 2.13/0.99  --inst_sos_phase                        true
% 2.13/0.99  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 2.13/0.99  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 2.13/0.99  --inst_lit_sel_side                     none
% 2.13/0.99  --inst_solver_per_active                1400
% 2.13/0.99  --inst_solver_calls_frac                1.
% 2.13/0.99  --inst_passive_queue_type               priority_queues
% 2.13/0.99  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 2.13/0.99  --inst_passive_queues_freq              [25;2]
% 2.13/0.99  --inst_dismatching                      true
% 2.13/0.99  --inst_eager_unprocessed_to_passive     true
% 2.13/0.99  --inst_prop_sim_given                   true
% 2.13/0.99  --inst_prop_sim_new                     false
% 2.13/0.99  --inst_subs_new                         false
% 2.13/0.99  --inst_eq_res_simp                      false
% 2.13/0.99  --inst_subs_given                       false
% 2.13/0.99  --inst_orphan_elimination               true
% 2.13/0.99  --inst_learning_loop_flag               true
% 2.13/0.99  --inst_learning_start                   3000
% 2.13/0.99  --inst_learning_factor                  2
% 2.13/0.99  --inst_start_prop_sim_after_learn       3
% 2.13/0.99  --inst_sel_renew                        solver
% 2.13/0.99  --inst_lit_activity_flag                true
% 2.13/0.99  --inst_restr_to_given                   false
% 2.13/0.99  --inst_activity_threshold               500
% 2.13/0.99  --inst_out_proof                        true
% 2.13/0.99  
% 2.13/0.99  ------ Resolution Options
% 2.13/0.99  
% 2.13/0.99  --resolution_flag                       false
% 2.13/0.99  --res_lit_sel                           adaptive
% 2.13/0.99  --res_lit_sel_side                      none
% 2.13/0.99  --res_ordering                          kbo
% 2.13/0.99  --res_to_prop_solver                    active
% 2.13/0.99  --res_prop_simpl_new                    false
% 2.13/0.99  --res_prop_simpl_given                  true
% 2.13/0.99  --res_passive_queue_type                priority_queues
% 2.13/0.99  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 2.13/0.99  --res_passive_queues_freq               [15;5]
% 2.13/0.99  --res_forward_subs                      full
% 2.13/0.99  --res_backward_subs                     full
% 2.13/0.99  --res_forward_subs_resolution           true
% 2.13/0.99  --res_backward_subs_resolution          true
% 2.13/0.99  --res_orphan_elimination                true
% 2.13/0.99  --res_time_limit                        2.
% 2.13/0.99  --res_out_proof                         true
% 2.13/0.99  
% 2.13/0.99  ------ Superposition Options
% 2.13/0.99  
% 2.13/0.99  --superposition_flag                    true
% 2.13/0.99  --sup_passive_queue_type                priority_queues
% 2.13/0.99  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 2.13/0.99  --sup_passive_queues_freq               [8;1;4]
% 2.13/0.99  --demod_completeness_check              fast
% 2.13/0.99  --demod_use_ground                      true
% 2.13/0.99  --sup_to_prop_solver                    passive
% 2.13/0.99  --sup_prop_simpl_new                    true
% 2.13/0.99  --sup_prop_simpl_given                  true
% 2.13/0.99  --sup_fun_splitting                     false
% 2.13/0.99  --sup_smt_interval                      50000
% 2.13/0.99  
% 2.13/0.99  ------ Superposition Simplification Setup
% 2.13/0.99  
% 2.13/0.99  --sup_indices_passive                   []
% 2.13/0.99  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.13/0.99  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.13/0.99  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.13/0.99  --sup_full_triv                         [TrivRules;PropSubs]
% 2.13/0.99  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.13/0.99  --sup_full_bw                           [BwDemod]
% 2.13/0.99  --sup_immed_triv                        [TrivRules]
% 2.13/0.99  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 2.13/0.99  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.13/0.99  --sup_immed_bw_main                     []
% 2.13/0.99  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.13/0.99  --sup_input_triv                        [Unflattening;TrivRules]
% 2.13/0.99  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.13/0.99  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.13/0.99  
% 2.13/0.99  ------ Combination Options
% 2.13/0.99  
% 2.13/0.99  --comb_res_mult                         3
% 2.13/0.99  --comb_sup_mult                         2
% 2.13/0.99  --comb_inst_mult                        10
% 2.13/0.99  
% 2.13/0.99  ------ Debug Options
% 2.13/0.99  
% 2.13/0.99  --dbg_backtrace                         false
% 2.13/0.99  --dbg_dump_prop_clauses                 false
% 2.13/0.99  --dbg_dump_prop_clauses_file            -
% 2.13/0.99  --dbg_out_stat                          false
% 2.13/0.99  
% 2.13/0.99  
% 2.13/0.99  
% 2.13/0.99  
% 2.13/0.99  ------ Proving...
% 2.13/0.99  
% 2.13/0.99  
% 2.13/0.99  % SZS status Theorem for theBenchmark.p
% 2.13/0.99  
% 2.13/0.99  % SZS output start CNFRefutation for theBenchmark.p
% 2.13/0.99  
% 2.13/0.99  fof(f1,axiom,(
% 2.13/0.99    ! [X0] : (v1_xboole_0(X0) <=> ! [X1] : ~r2_hidden(X1,X0))),
% 2.13/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.13/0.99  
% 2.13/0.99  fof(f26,plain,(
% 2.13/0.99    ! [X0] : ((v1_xboole_0(X0) | ? [X1] : r2_hidden(X1,X0)) & (! [X1] : ~r2_hidden(X1,X0) | ~v1_xboole_0(X0)))),
% 2.13/0.99    inference(nnf_transformation,[],[f1])).
% 2.13/0.99  
% 2.13/0.99  fof(f27,plain,(
% 2.13/0.99    ! [X0] : ((v1_xboole_0(X0) | ? [X1] : r2_hidden(X1,X0)) & (! [X2] : ~r2_hidden(X2,X0) | ~v1_xboole_0(X0)))),
% 2.13/0.99    inference(rectify,[],[f26])).
% 2.13/0.99  
% 2.13/0.99  fof(f28,plain,(
% 2.13/0.99    ! [X0] : (? [X1] : r2_hidden(X1,X0) => r2_hidden(sK0(X0),X0))),
% 2.13/0.99    introduced(choice_axiom,[])).
% 2.13/0.99  
% 2.13/0.99  fof(f29,plain,(
% 2.13/0.99    ! [X0] : ((v1_xboole_0(X0) | r2_hidden(sK0(X0),X0)) & (! [X2] : ~r2_hidden(X2,X0) | ~v1_xboole_0(X0)))),
% 2.13/0.99    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f27,f28])).
% 2.13/0.99  
% 2.13/0.99  fof(f37,plain,(
% 2.13/0.99    ( ! [X0] : (v1_xboole_0(X0) | r2_hidden(sK0(X0),X0)) )),
% 2.13/0.99    inference(cnf_transformation,[],[f29])).
% 2.13/0.99  
% 2.13/0.99  fof(f5,axiom,(
% 2.13/0.99    ! [X0,X1] : (r2_hidden(X0,X1) => k2_xboole_0(k1_tarski(X0),X1) = X1)),
% 2.13/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.13/0.99  
% 2.13/0.99  fof(f17,plain,(
% 2.13/0.99    ! [X0,X1] : (k2_xboole_0(k1_tarski(X0),X1) = X1 | ~r2_hidden(X0,X1))),
% 2.13/0.99    inference(ennf_transformation,[],[f5])).
% 2.13/0.99  
% 2.13/0.99  fof(f41,plain,(
% 2.13/0.99    ( ! [X0,X1] : (k2_xboole_0(k1_tarski(X0),X1) = X1 | ~r2_hidden(X0,X1)) )),
% 2.13/0.99    inference(cnf_transformation,[],[f17])).
% 2.13/0.99  
% 2.13/0.99  fof(f4,axiom,(
% 2.13/0.99    ! [X0,X1] : k5_xboole_0(X0,k4_xboole_0(X1,X0)) = k2_xboole_0(X0,X1)),
% 2.13/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.13/0.99  
% 2.13/0.99  fof(f40,plain,(
% 2.13/0.99    ( ! [X0,X1] : (k5_xboole_0(X0,k4_xboole_0(X1,X0)) = k2_xboole_0(X0,X1)) )),
% 2.13/0.99    inference(cnf_transformation,[],[f4])).
% 2.13/0.99  
% 2.13/0.99  fof(f3,axiom,(
% 2.13/0.99    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))),
% 2.13/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.13/0.99  
% 2.13/0.99  fof(f39,plain,(
% 2.13/0.99    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))) )),
% 2.13/0.99    inference(cnf_transformation,[],[f3])).
% 2.13/0.99  
% 2.13/0.99  fof(f11,axiom,(
% 2.13/0.99    ! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1))),
% 2.13/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.13/0.99  
% 2.13/0.99  fof(f48,plain,(
% 2.13/0.99    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1))) )),
% 2.13/0.99    inference(cnf_transformation,[],[f11])).
% 2.13/0.99  
% 2.13/0.99  fof(f56,plain,(
% 2.13/0.99    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k5_xboole_0(X0,k1_setfam_1(k2_tarski(X0,X1)))) )),
% 2.13/0.99    inference(definition_unfolding,[],[f39,f48])).
% 2.13/0.99  
% 2.13/0.99  fof(f57,plain,(
% 2.13/0.99    ( ! [X0,X1] : (k5_xboole_0(X0,k5_xboole_0(X1,k1_setfam_1(k2_tarski(X1,X0)))) = k2_xboole_0(X0,X1)) )),
% 2.13/0.99    inference(definition_unfolding,[],[f40,f56])).
% 2.13/0.99  
% 2.13/0.99  fof(f58,plain,(
% 2.13/0.99    ( ! [X0,X1] : (k5_xboole_0(k1_tarski(X0),k5_xboole_0(X1,k1_setfam_1(k2_tarski(X1,k1_tarski(X0))))) = X1 | ~r2_hidden(X0,X1)) )),
% 2.13/0.99    inference(definition_unfolding,[],[f41,f57])).
% 2.13/0.99  
% 2.13/0.99  fof(f13,axiom,(
% 2.13/0.99    ! [X0,X1] : (r1_tarski(X0,X1) => (r1_tarski(k1_setfam_1(X1),k1_setfam_1(X0)) | k1_xboole_0 = X0))),
% 2.13/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.13/0.99  
% 2.13/0.99  fof(f22,plain,(
% 2.13/0.99    ! [X0,X1] : ((r1_tarski(k1_setfam_1(X1),k1_setfam_1(X0)) | k1_xboole_0 = X0) | ~r1_tarski(X0,X1))),
% 2.13/0.99    inference(ennf_transformation,[],[f13])).
% 2.13/0.99  
% 2.13/0.99  fof(f23,plain,(
% 2.13/0.99    ! [X0,X1] : (r1_tarski(k1_setfam_1(X1),k1_setfam_1(X0)) | k1_xboole_0 = X0 | ~r1_tarski(X0,X1))),
% 2.13/0.99    inference(flattening,[],[f22])).
% 2.13/0.99  
% 2.13/0.99  fof(f51,plain,(
% 2.13/0.99    ( ! [X0,X1] : (r1_tarski(k1_setfam_1(X1),k1_setfam_1(X0)) | k1_xboole_0 = X0 | ~r1_tarski(X0,X1)) )),
% 2.13/0.99    inference(cnf_transformation,[],[f23])).
% 2.13/0.99  
% 2.13/0.99  fof(f14,conjecture,(
% 2.13/0.99    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(X0))) => (r1_tarski(X1,X2) => r1_tarski(k8_setfam_1(X0,X2),k8_setfam_1(X0,X1)))))),
% 2.13/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.13/0.99  
% 2.13/0.99  fof(f15,negated_conjecture,(
% 2.13/0.99    ~! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(X0))) => (r1_tarski(X1,X2) => r1_tarski(k8_setfam_1(X0,X2),k8_setfam_1(X0,X1)))))),
% 2.13/0.99    inference(negated_conjecture,[],[f14])).
% 2.13/0.99  
% 2.13/0.99  fof(f24,plain,(
% 2.13/0.99    ? [X0,X1] : (? [X2] : ((~r1_tarski(k8_setfam_1(X0,X2),k8_setfam_1(X0,X1)) & r1_tarski(X1,X2)) & m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(X0)))) & m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))))),
% 2.13/0.99    inference(ennf_transformation,[],[f15])).
% 2.13/0.99  
% 2.13/0.99  fof(f25,plain,(
% 2.13/0.99    ? [X0,X1] : (? [X2] : (~r1_tarski(k8_setfam_1(X0,X2),k8_setfam_1(X0,X1)) & r1_tarski(X1,X2) & m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(X0)))) & m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))))),
% 2.13/0.99    inference(flattening,[],[f24])).
% 2.13/0.99  
% 2.13/0.99  fof(f34,plain,(
% 2.13/0.99    ( ! [X0,X1] : (? [X2] : (~r1_tarski(k8_setfam_1(X0,X2),k8_setfam_1(X0,X1)) & r1_tarski(X1,X2) & m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(X0)))) => (~r1_tarski(k8_setfam_1(X0,sK4),k8_setfam_1(X0,X1)) & r1_tarski(X1,sK4) & m1_subset_1(sK4,k1_zfmisc_1(k1_zfmisc_1(X0))))) )),
% 2.13/0.99    introduced(choice_axiom,[])).
% 2.13/0.99  
% 2.13/0.99  fof(f33,plain,(
% 2.13/0.99    ? [X0,X1] : (? [X2] : (~r1_tarski(k8_setfam_1(X0,X2),k8_setfam_1(X0,X1)) & r1_tarski(X1,X2) & m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(X0)))) & m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0)))) => (? [X2] : (~r1_tarski(k8_setfam_1(sK2,X2),k8_setfam_1(sK2,sK3)) & r1_tarski(sK3,X2) & m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(sK2)))) & m1_subset_1(sK3,k1_zfmisc_1(k1_zfmisc_1(sK2))))),
% 2.13/0.99    introduced(choice_axiom,[])).
% 2.13/0.99  
% 2.13/0.99  fof(f35,plain,(
% 2.13/0.99    (~r1_tarski(k8_setfam_1(sK2,sK4),k8_setfam_1(sK2,sK3)) & r1_tarski(sK3,sK4) & m1_subset_1(sK4,k1_zfmisc_1(k1_zfmisc_1(sK2)))) & m1_subset_1(sK3,k1_zfmisc_1(k1_zfmisc_1(sK2)))),
% 2.13/0.99    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2,sK3,sK4])],[f25,f34,f33])).
% 2.13/0.99  
% 2.13/0.99  fof(f52,plain,(
% 2.13/0.99    m1_subset_1(sK3,k1_zfmisc_1(k1_zfmisc_1(sK2)))),
% 2.13/0.99    inference(cnf_transformation,[],[f35])).
% 2.13/0.99  
% 2.13/0.99  fof(f8,axiom,(
% 2.13/0.99    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) => ((k1_xboole_0 = X1 => k8_setfam_1(X0,X1) = X0) & (k1_xboole_0 != X1 => k8_setfam_1(X0,X1) = k6_setfam_1(X0,X1))))),
% 2.13/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.13/0.99  
% 2.13/0.99  fof(f19,plain,(
% 2.13/0.99    ! [X0,X1] : (((k8_setfam_1(X0,X1) = X0 | k1_xboole_0 != X1) & (k8_setfam_1(X0,X1) = k6_setfam_1(X0,X1) | k1_xboole_0 = X1)) | ~m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))))),
% 2.13/0.99    inference(ennf_transformation,[],[f8])).
% 2.13/0.99  
% 2.13/0.99  fof(f44,plain,(
% 2.13/0.99    ( ! [X0,X1] : (k8_setfam_1(X0,X1) = k6_setfam_1(X0,X1) | k1_xboole_0 = X1 | ~m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0)))) )),
% 2.13/0.99    inference(cnf_transformation,[],[f19])).
% 2.13/0.99  
% 2.13/0.99  fof(f10,axiom,(
% 2.13/0.99    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) => k6_setfam_1(X0,X1) = k1_setfam_1(X1))),
% 2.13/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.13/0.99  
% 2.13/0.99  fof(f21,plain,(
% 2.13/0.99    ! [X0,X1] : (k6_setfam_1(X0,X1) = k1_setfam_1(X1) | ~m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))))),
% 2.13/0.99    inference(ennf_transformation,[],[f10])).
% 2.13/0.99  
% 2.13/0.99  fof(f47,plain,(
% 2.13/0.99    ( ! [X0,X1] : (k6_setfam_1(X0,X1) = k1_setfam_1(X1) | ~m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0)))) )),
% 2.13/0.99    inference(cnf_transformation,[],[f21])).
% 2.13/0.99  
% 2.13/0.99  fof(f53,plain,(
% 2.13/0.99    m1_subset_1(sK4,k1_zfmisc_1(k1_zfmisc_1(sK2)))),
% 2.13/0.99    inference(cnf_transformation,[],[f35])).
% 2.13/0.99  
% 2.13/0.99  fof(f55,plain,(
% 2.13/0.99    ~r1_tarski(k8_setfam_1(sK2,sK4),k8_setfam_1(sK2,sK3))),
% 2.13/0.99    inference(cnf_transformation,[],[f35])).
% 2.13/0.99  
% 2.13/0.99  fof(f54,plain,(
% 2.13/0.99    r1_tarski(sK3,sK4)),
% 2.13/0.99    inference(cnf_transformation,[],[f35])).
% 2.13/0.99  
% 2.13/0.99  fof(f45,plain,(
% 2.13/0.99    ( ! [X0,X1] : (k8_setfam_1(X0,X1) = X0 | k1_xboole_0 != X1 | ~m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0)))) )),
% 2.13/0.99    inference(cnf_transformation,[],[f19])).
% 2.13/0.99  
% 2.13/0.99  fof(f60,plain,(
% 2.13/0.99    ( ! [X0] : (k8_setfam_1(X0,k1_xboole_0) = X0 | ~m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_zfmisc_1(X0)))) )),
% 2.13/0.99    inference(equality_resolution,[],[f45])).
% 2.13/0.99  
% 2.13/0.99  fof(f9,axiom,(
% 2.13/0.99    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) => m1_subset_1(k8_setfam_1(X0,X1),k1_zfmisc_1(X0)))),
% 2.13/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.13/0.99  
% 2.13/0.99  fof(f20,plain,(
% 2.13/0.99    ! [X0,X1] : (m1_subset_1(k8_setfam_1(X0,X1),k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))))),
% 2.13/0.99    inference(ennf_transformation,[],[f9])).
% 2.13/0.99  
% 2.13/0.99  fof(f46,plain,(
% 2.13/0.99    ( ! [X0,X1] : (m1_subset_1(k8_setfam_1(X0,X1),k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0)))) )),
% 2.13/0.99    inference(cnf_transformation,[],[f20])).
% 2.13/0.99  
% 2.13/0.99  fof(f12,axiom,(
% 2.13/0.99    ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) <=> r1_tarski(X0,X1))),
% 2.13/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.13/0.99  
% 2.13/0.99  fof(f32,plain,(
% 2.13/0.99    ! [X0,X1] : ((m1_subset_1(X0,k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1)) & (r1_tarski(X0,X1) | ~m1_subset_1(X0,k1_zfmisc_1(X1))))),
% 2.13/0.99    inference(nnf_transformation,[],[f12])).
% 2.13/0.99  
% 2.13/0.99  fof(f49,plain,(
% 2.13/0.99    ( ! [X0,X1] : (r1_tarski(X0,X1) | ~m1_subset_1(X0,k1_zfmisc_1(X1))) )),
% 2.13/0.99    inference(cnf_transformation,[],[f32])).
% 2.13/0.99  
% 2.13/0.99  fof(f7,axiom,(
% 2.13/0.99    ! [X0] : (v1_xboole_0(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => v1_xboole_0(X1)))),
% 2.13/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.13/0.99  
% 2.13/0.99  fof(f18,plain,(
% 2.13/0.99    ! [X0] : (! [X1] : (v1_xboole_0(X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) | ~v1_xboole_0(X0))),
% 2.13/0.99    inference(ennf_transformation,[],[f7])).
% 2.13/0.99  
% 2.13/0.99  fof(f43,plain,(
% 2.13/0.99    ( ! [X0,X1] : (v1_xboole_0(X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0)) | ~v1_xboole_0(X0)) )),
% 2.13/0.99    inference(cnf_transformation,[],[f18])).
% 2.13/0.99  
% 2.13/0.99  fof(f50,plain,(
% 2.13/0.99    ( ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1)) )),
% 2.13/0.99    inference(cnf_transformation,[],[f32])).
% 2.13/0.99  
% 2.13/0.99  fof(f6,axiom,(
% 2.13/0.99    ! [X0,X1] : k1_xboole_0 != k2_xboole_0(k1_tarski(X0),X1)),
% 2.13/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.13/0.99  
% 2.13/0.99  fof(f42,plain,(
% 2.13/0.99    ( ! [X0,X1] : (k1_xboole_0 != k2_xboole_0(k1_tarski(X0),X1)) )),
% 2.13/0.99    inference(cnf_transformation,[],[f6])).
% 2.13/0.99  
% 2.13/0.99  fof(f59,plain,(
% 2.13/0.99    ( ! [X0,X1] : (k1_xboole_0 != k5_xboole_0(k1_tarski(X0),k5_xboole_0(X1,k1_setfam_1(k2_tarski(X1,k1_tarski(X0)))))) )),
% 2.13/0.99    inference(definition_unfolding,[],[f42,f57])).
% 2.13/0.99  
% 2.13/0.99  fof(f2,axiom,(
% 2.13/0.99    ! [X0] : ~(! [X1] : ~r2_hidden(X1,X0) & k1_xboole_0 != X0)),
% 2.13/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.13/0.99  
% 2.13/0.99  fof(f16,plain,(
% 2.13/0.99    ! [X0] : (? [X1] : r2_hidden(X1,X0) | k1_xboole_0 = X0)),
% 2.13/0.99    inference(ennf_transformation,[],[f2])).
% 2.13/0.99  
% 2.13/0.99  fof(f30,plain,(
% 2.13/0.99    ! [X0] : (? [X1] : r2_hidden(X1,X0) => r2_hidden(sK1(X0),X0))),
% 2.13/0.99    introduced(choice_axiom,[])).
% 2.13/0.99  
% 2.13/0.99  fof(f31,plain,(
% 2.13/0.99    ! [X0] : (r2_hidden(sK1(X0),X0) | k1_xboole_0 = X0)),
% 2.13/0.99    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1])],[f16,f30])).
% 2.13/0.99  
% 2.13/0.99  fof(f38,plain,(
% 2.13/0.99    ( ! [X0] : (r2_hidden(sK1(X0),X0) | k1_xboole_0 = X0) )),
% 2.13/0.99    inference(cnf_transformation,[],[f31])).
% 2.13/0.99  
% 2.13/0.99  fof(f36,plain,(
% 2.13/0.99    ( ! [X2,X0] : (~r2_hidden(X2,X0) | ~v1_xboole_0(X0)) )),
% 2.13/0.99    inference(cnf_transformation,[],[f29])).
% 2.13/0.99  
% 2.13/0.99  cnf(c_0,plain,
% 2.13/0.99      ( r2_hidden(sK0(X0),X0) | v1_xboole_0(X0) ),
% 2.13/0.99      inference(cnf_transformation,[],[f37]) ).
% 2.13/0.99  
% 2.13/0.99  cnf(c_667,plain,
% 2.13/0.99      ( r2_hidden(sK0(X0),X0) = iProver_top
% 2.13/0.99      | v1_xboole_0(X0) = iProver_top ),
% 2.13/0.99      inference(predicate_to_equality,[status(thm)],[c_0]) ).
% 2.13/0.99  
% 2.13/0.99  cnf(c_3,plain,
% 2.13/0.99      ( ~ r2_hidden(X0,X1)
% 2.13/0.99      | k5_xboole_0(k1_tarski(X0),k5_xboole_0(X1,k1_setfam_1(k2_tarski(X1,k1_tarski(X0))))) = X1 ),
% 2.13/0.99      inference(cnf_transformation,[],[f58]) ).
% 2.13/0.99  
% 2.13/0.99  cnf(c_664,plain,
% 2.13/0.99      ( k5_xboole_0(k1_tarski(X0),k5_xboole_0(X1,k1_setfam_1(k2_tarski(X1,k1_tarski(X0))))) = X1
% 2.13/0.99      | r2_hidden(X0,X1) != iProver_top ),
% 2.13/0.99      inference(predicate_to_equality,[status(thm)],[c_3]) ).
% 2.13/0.99  
% 2.13/0.99  cnf(c_1603,plain,
% 2.13/0.99      ( k5_xboole_0(k1_tarski(sK0(X0)),k5_xboole_0(X0,k1_setfam_1(k2_tarski(X0,k1_tarski(sK0(X0)))))) = X0
% 2.13/0.99      | v1_xboole_0(X0) = iProver_top ),
% 2.13/0.99      inference(superposition,[status(thm)],[c_667,c_664]) ).
% 2.13/0.99  
% 2.13/0.99  cnf(c_12,plain,
% 2.13/0.99      ( ~ r1_tarski(X0,X1)
% 2.13/0.99      | r1_tarski(k1_setfam_1(X1),k1_setfam_1(X0))
% 2.13/0.99      | k1_xboole_0 = X0 ),
% 2.13/0.99      inference(cnf_transformation,[],[f51]) ).
% 2.13/0.99  
% 2.13/0.99  cnf(c_657,plain,
% 2.13/0.99      ( k1_xboole_0 = X0
% 2.13/0.99      | r1_tarski(X0,X1) != iProver_top
% 2.13/0.99      | r1_tarski(k1_setfam_1(X1),k1_setfam_1(X0)) = iProver_top ),
% 2.13/0.99      inference(predicate_to_equality,[status(thm)],[c_12]) ).
% 2.13/0.99  
% 2.13/0.99  cnf(c_16,negated_conjecture,
% 2.13/0.99      ( m1_subset_1(sK3,k1_zfmisc_1(k1_zfmisc_1(sK2))) ),
% 2.13/0.99      inference(cnf_transformation,[],[f52]) ).
% 2.13/0.99  
% 2.13/0.99  cnf(c_653,plain,
% 2.13/0.99      ( m1_subset_1(sK3,k1_zfmisc_1(k1_zfmisc_1(sK2))) = iProver_top ),
% 2.13/0.99      inference(predicate_to_equality,[status(thm)],[c_16]) ).
% 2.13/0.99  
% 2.13/0.99  cnf(c_7,plain,
% 2.13/0.99      ( ~ m1_subset_1(X0,k1_zfmisc_1(k1_zfmisc_1(X1)))
% 2.13/0.99      | k6_setfam_1(X1,X0) = k8_setfam_1(X1,X0)
% 2.13/0.99      | k1_xboole_0 = X0 ),
% 2.13/0.99      inference(cnf_transformation,[],[f44]) ).
% 2.13/0.99  
% 2.13/0.99  cnf(c_662,plain,
% 2.13/0.99      ( k6_setfam_1(X0,X1) = k8_setfam_1(X0,X1)
% 2.13/0.99      | k1_xboole_0 = X1
% 2.13/0.99      | m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) != iProver_top ),
% 2.13/0.99      inference(predicate_to_equality,[status(thm)],[c_7]) ).
% 2.13/0.99  
% 2.13/0.99  cnf(c_1621,plain,
% 2.13/0.99      ( k6_setfam_1(sK2,sK3) = k8_setfam_1(sK2,sK3) | sK3 = k1_xboole_0 ),
% 2.13/0.99      inference(superposition,[status(thm)],[c_653,c_662]) ).
% 2.13/0.99  
% 2.13/0.99  cnf(c_9,plain,
% 2.13/0.99      ( ~ m1_subset_1(X0,k1_zfmisc_1(k1_zfmisc_1(X1)))
% 2.13/0.99      | k6_setfam_1(X1,X0) = k1_setfam_1(X0) ),
% 2.13/0.99      inference(cnf_transformation,[],[f47]) ).
% 2.13/0.99  
% 2.13/0.99  cnf(c_660,plain,
% 2.13/0.99      ( k6_setfam_1(X0,X1) = k1_setfam_1(X1)
% 2.13/0.99      | m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) != iProver_top ),
% 2.13/0.99      inference(predicate_to_equality,[status(thm)],[c_9]) ).
% 2.13/0.99  
% 2.13/0.99  cnf(c_1544,plain,
% 2.13/0.99      ( k6_setfam_1(sK2,sK3) = k1_setfam_1(sK3) ),
% 2.13/0.99      inference(superposition,[status(thm)],[c_653,c_660]) ).
% 2.13/0.99  
% 2.13/0.99  cnf(c_1896,plain,
% 2.13/0.99      ( k8_setfam_1(sK2,sK3) = k1_setfam_1(sK3) | sK3 = k1_xboole_0 ),
% 2.13/0.99      inference(light_normalisation,[status(thm)],[c_1621,c_1544]) ).
% 2.13/0.99  
% 2.13/0.99  cnf(c_15,negated_conjecture,
% 2.13/0.99      ( m1_subset_1(sK4,k1_zfmisc_1(k1_zfmisc_1(sK2))) ),
% 2.13/0.99      inference(cnf_transformation,[],[f53]) ).
% 2.13/0.99  
% 2.13/0.99  cnf(c_654,plain,
% 2.13/0.99      ( m1_subset_1(sK4,k1_zfmisc_1(k1_zfmisc_1(sK2))) = iProver_top ),
% 2.13/0.99      inference(predicate_to_equality,[status(thm)],[c_15]) ).
% 2.13/0.99  
% 2.13/0.99  cnf(c_1620,plain,
% 2.13/0.99      ( k6_setfam_1(sK2,sK4) = k8_setfam_1(sK2,sK4) | sK4 = k1_xboole_0 ),
% 2.13/0.99      inference(superposition,[status(thm)],[c_654,c_662]) ).
% 2.13/0.99  
% 2.13/0.99  cnf(c_1543,plain,
% 2.13/0.99      ( k6_setfam_1(sK2,sK4) = k1_setfam_1(sK4) ),
% 2.13/0.99      inference(superposition,[status(thm)],[c_654,c_660]) ).
% 2.13/0.99  
% 2.13/0.99  cnf(c_1748,plain,
% 2.13/0.99      ( k8_setfam_1(sK2,sK4) = k1_setfam_1(sK4) | sK4 = k1_xboole_0 ),
% 2.13/0.99      inference(light_normalisation,[status(thm)],[c_1620,c_1543]) ).
% 2.13/0.99  
% 2.13/0.99  cnf(c_13,negated_conjecture,
% 2.13/0.99      ( ~ r1_tarski(k8_setfam_1(sK2,sK4),k8_setfam_1(sK2,sK3)) ),
% 2.13/0.99      inference(cnf_transformation,[],[f55]) ).
% 2.13/0.99  
% 2.13/0.99  cnf(c_656,plain,
% 2.13/0.99      ( r1_tarski(k8_setfam_1(sK2,sK4),k8_setfam_1(sK2,sK3)) != iProver_top ),
% 2.13/0.99      inference(predicate_to_equality,[status(thm)],[c_13]) ).
% 2.13/0.99  
% 2.13/0.99  cnf(c_1752,plain,
% 2.13/0.99      ( sK4 = k1_xboole_0
% 2.13/0.99      | r1_tarski(k1_setfam_1(sK4),k8_setfam_1(sK2,sK3)) != iProver_top ),
% 2.13/0.99      inference(superposition,[status(thm)],[c_1748,c_656]) ).
% 2.13/0.99  
% 2.13/0.99  cnf(c_1900,plain,
% 2.13/0.99      ( sK3 = k1_xboole_0
% 2.13/0.99      | sK4 = k1_xboole_0
% 2.13/0.99      | r1_tarski(k1_setfam_1(sK4),k1_setfam_1(sK3)) != iProver_top ),
% 2.13/0.99      inference(superposition,[status(thm)],[c_1896,c_1752]) ).
% 2.13/0.99  
% 2.13/0.99  cnf(c_2060,plain,
% 2.13/0.99      ( sK3 = k1_xboole_0
% 2.13/0.99      | sK4 = k1_xboole_0
% 2.13/0.99      | r1_tarski(sK3,sK4) != iProver_top ),
% 2.13/0.99      inference(superposition,[status(thm)],[c_657,c_1900]) ).
% 2.13/0.99  
% 2.13/0.99  cnf(c_14,negated_conjecture,
% 2.13/0.99      ( r1_tarski(sK3,sK4) ),
% 2.13/0.99      inference(cnf_transformation,[],[f54]) ).
% 2.13/0.99  
% 2.13/0.99  cnf(c_19,plain,
% 2.13/0.99      ( r1_tarski(sK3,sK4) = iProver_top ),
% 2.13/0.99      inference(predicate_to_equality,[status(thm)],[c_14]) ).
% 2.13/0.99  
% 2.13/0.99  cnf(c_2063,plain,
% 2.13/0.99      ( sK4 = k1_xboole_0 | sK3 = k1_xboole_0 ),
% 2.13/0.99      inference(global_propositional_subsumption,
% 2.13/0.99                [status(thm)],
% 2.13/0.99                [c_2060,c_19]) ).
% 2.13/0.99  
% 2.13/0.99  cnf(c_2064,plain,
% 2.13/0.99      ( sK3 = k1_xboole_0 | sK4 = k1_xboole_0 ),
% 2.13/0.99      inference(renaming,[status(thm)],[c_2063]) ).
% 2.13/0.99  
% 2.13/0.99  cnf(c_2072,plain,
% 2.13/0.99      ( sK4 = k1_xboole_0
% 2.13/0.99      | r1_tarski(k8_setfam_1(sK2,sK4),k8_setfam_1(sK2,k1_xboole_0)) != iProver_top ),
% 2.13/0.99      inference(superposition,[status(thm)],[c_2064,c_656]) ).
% 2.13/0.99  
% 2.13/0.99  cnf(c_2073,plain,
% 2.13/0.99      ( sK4 = k1_xboole_0
% 2.13/0.99      | m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_zfmisc_1(sK2))) = iProver_top ),
% 2.13/0.99      inference(superposition,[status(thm)],[c_2064,c_653]) ).
% 2.13/0.99  
% 2.13/0.99  cnf(c_18,plain,
% 2.13/0.99      ( m1_subset_1(sK4,k1_zfmisc_1(k1_zfmisc_1(sK2))) = iProver_top ),
% 2.13/0.99      inference(predicate_to_equality,[status(thm)],[c_15]) ).
% 2.13/0.99  
% 2.13/0.99  cnf(c_260,plain,( X0 = X0 ),theory(equality) ).
% 2.13/0.99  
% 2.13/0.99  cnf(c_279,plain,
% 2.13/0.99      ( k1_xboole_0 = k1_xboole_0 ),
% 2.13/0.99      inference(instantiation,[status(thm)],[c_260]) ).
% 2.13/0.99  
% 2.13/0.99  cnf(c_261,plain,( X0 != X1 | X2 != X1 | X2 = X0 ),theory(equality) ).
% 2.13/0.99  
% 2.13/0.99  cnf(c_872,plain,
% 2.13/0.99      ( X0 != X1 | X0 = sK4 | sK4 != X1 ),
% 2.13/0.99      inference(instantiation,[status(thm)],[c_261]) ).
% 2.13/0.99  
% 2.13/0.99  cnf(c_873,plain,
% 2.13/0.99      ( sK4 != k1_xboole_0
% 2.13/0.99      | k1_xboole_0 = sK4
% 2.13/0.99      | k1_xboole_0 != k1_xboole_0 ),
% 2.13/0.99      inference(instantiation,[status(thm)],[c_872]) ).
% 2.13/0.99  
% 2.13/0.99  cnf(c_267,plain,
% 2.13/0.99      ( ~ m1_subset_1(X0,X1) | m1_subset_1(X2,X3) | X2 != X0 | X3 != X1 ),
% 2.13/0.99      theory(equality) ).
% 2.13/0.99  
% 2.13/0.99  cnf(c_792,plain,
% 2.13/0.99      ( m1_subset_1(X0,X1)
% 2.13/0.99      | ~ m1_subset_1(sK4,k1_zfmisc_1(k1_zfmisc_1(sK2)))
% 2.13/0.99      | X1 != k1_zfmisc_1(k1_zfmisc_1(sK2))
% 2.13/0.99      | X0 != sK4 ),
% 2.13/0.99      inference(instantiation,[status(thm)],[c_267]) ).
% 2.13/0.99  
% 2.13/0.99  cnf(c_947,plain,
% 2.13/0.99      ( m1_subset_1(X0,k1_zfmisc_1(k1_zfmisc_1(sK2)))
% 2.13/0.99      | ~ m1_subset_1(sK4,k1_zfmisc_1(k1_zfmisc_1(sK2)))
% 2.13/0.99      | X0 != sK4
% 2.13/0.99      | k1_zfmisc_1(k1_zfmisc_1(sK2)) != k1_zfmisc_1(k1_zfmisc_1(sK2)) ),
% 2.13/0.99      inference(instantiation,[status(thm)],[c_792]) ).
% 2.13/0.99  
% 2.13/0.99  cnf(c_949,plain,
% 2.13/0.99      ( X0 != sK4
% 2.13/0.99      | k1_zfmisc_1(k1_zfmisc_1(sK2)) != k1_zfmisc_1(k1_zfmisc_1(sK2))
% 2.13/0.99      | m1_subset_1(X0,k1_zfmisc_1(k1_zfmisc_1(sK2))) = iProver_top
% 2.13/0.99      | m1_subset_1(sK4,k1_zfmisc_1(k1_zfmisc_1(sK2))) != iProver_top ),
% 2.13/0.99      inference(predicate_to_equality,[status(thm)],[c_947]) ).
% 2.13/0.99  
% 2.13/0.99  cnf(c_951,plain,
% 2.13/0.99      ( k1_zfmisc_1(k1_zfmisc_1(sK2)) != k1_zfmisc_1(k1_zfmisc_1(sK2))
% 2.13/0.99      | k1_xboole_0 != sK4
% 2.13/0.99      | m1_subset_1(sK4,k1_zfmisc_1(k1_zfmisc_1(sK2))) != iProver_top
% 2.13/0.99      | m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_zfmisc_1(sK2))) = iProver_top ),
% 2.13/0.99      inference(instantiation,[status(thm)],[c_949]) ).
% 2.13/0.99  
% 2.13/0.99  cnf(c_948,plain,
% 2.13/0.99      ( k1_zfmisc_1(k1_zfmisc_1(sK2)) = k1_zfmisc_1(k1_zfmisc_1(sK2)) ),
% 2.13/0.99      inference(instantiation,[status(thm)],[c_260]) ).
% 2.13/0.99  
% 2.13/0.99  cnf(c_2297,plain,
% 2.13/0.99      ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_zfmisc_1(sK2))) = iProver_top ),
% 2.13/0.99      inference(global_propositional_subsumption,
% 2.13/0.99                [status(thm)],
% 2.13/0.99                [c_2073,c_18,c_279,c_873,c_951,c_948]) ).
% 2.13/0.99  
% 2.13/0.99  cnf(c_6,plain,
% 2.13/0.99      ( ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_zfmisc_1(X0)))
% 2.13/0.99      | k8_setfam_1(X0,k1_xboole_0) = X0 ),
% 2.13/0.99      inference(cnf_transformation,[],[f60]) ).
% 2.13/0.99  
% 2.13/0.99  cnf(c_663,plain,
% 2.13/0.99      ( k8_setfam_1(X0,k1_xboole_0) = X0
% 2.13/0.99      | m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_zfmisc_1(X0))) != iProver_top ),
% 2.13/0.99      inference(predicate_to_equality,[status(thm)],[c_6]) ).
% 2.13/0.99  
% 2.13/0.99  cnf(c_2303,plain,
% 2.13/0.99      ( k8_setfam_1(sK2,k1_xboole_0) = sK2 ),
% 2.13/0.99      inference(superposition,[status(thm)],[c_2297,c_663]) ).
% 2.13/0.99  
% 2.13/0.99  cnf(c_2379,plain,
% 2.13/0.99      ( sK4 = k1_xboole_0
% 2.13/0.99      | r1_tarski(k8_setfam_1(sK2,sK4),sK2) != iProver_top ),
% 2.13/0.99      inference(light_normalisation,[status(thm)],[c_2072,c_2303]) ).
% 2.13/0.99  
% 2.13/0.99  cnf(c_8,plain,
% 2.13/0.99      ( ~ m1_subset_1(X0,k1_zfmisc_1(k1_zfmisc_1(X1)))
% 2.13/0.99      | m1_subset_1(k8_setfam_1(X1,X0),k1_zfmisc_1(X1)) ),
% 2.13/0.99      inference(cnf_transformation,[],[f46]) ).
% 2.13/0.99  
% 2.13/0.99  cnf(c_776,plain,
% 2.13/0.99      ( m1_subset_1(k8_setfam_1(sK2,sK4),k1_zfmisc_1(sK2))
% 2.13/0.99      | ~ m1_subset_1(sK4,k1_zfmisc_1(k1_zfmisc_1(sK2))) ),
% 2.13/0.99      inference(instantiation,[status(thm)],[c_8]) ).
% 2.13/0.99  
% 2.13/0.99  cnf(c_777,plain,
% 2.13/0.99      ( m1_subset_1(k8_setfam_1(sK2,sK4),k1_zfmisc_1(sK2)) = iProver_top
% 2.13/0.99      | m1_subset_1(sK4,k1_zfmisc_1(k1_zfmisc_1(sK2))) != iProver_top ),
% 2.13/0.99      inference(predicate_to_equality,[status(thm)],[c_776]) ).
% 2.13/0.99  
% 2.13/0.99  cnf(c_11,plain,
% 2.13/0.99      ( r1_tarski(X0,X1) | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ),
% 2.13/0.99      inference(cnf_transformation,[],[f49]) ).
% 2.13/0.99  
% 2.13/0.99  cnf(c_834,plain,
% 2.13/0.99      ( r1_tarski(k8_setfam_1(sK2,sK4),sK2)
% 2.13/0.99      | ~ m1_subset_1(k8_setfam_1(sK2,sK4),k1_zfmisc_1(sK2)) ),
% 2.13/0.99      inference(instantiation,[status(thm)],[c_11]) ).
% 2.13/0.99  
% 2.13/0.99  cnf(c_835,plain,
% 2.13/0.99      ( r1_tarski(k8_setfam_1(sK2,sK4),sK2) = iProver_top
% 2.13/0.99      | m1_subset_1(k8_setfam_1(sK2,sK4),k1_zfmisc_1(sK2)) != iProver_top ),
% 2.13/0.99      inference(predicate_to_equality,[status(thm)],[c_834]) ).
% 2.13/0.99  
% 2.13/0.99  cnf(c_2383,plain,
% 2.13/0.99      ( sK4 = k1_xboole_0 ),
% 2.13/0.99      inference(global_propositional_subsumption,
% 2.13/0.99                [status(thm)],
% 2.13/0.99                [c_2379,c_18,c_777,c_835]) ).
% 2.13/0.99  
% 2.13/0.99  cnf(c_655,plain,
% 2.13/0.99      ( r1_tarski(sK3,sK4) = iProver_top ),
% 2.13/0.99      inference(predicate_to_equality,[status(thm)],[c_14]) ).
% 2.13/0.99  
% 2.13/0.99  cnf(c_5,plain,
% 2.13/0.99      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
% 2.13/0.99      | ~ v1_xboole_0(X1)
% 2.13/0.99      | v1_xboole_0(X0) ),
% 2.13/0.99      inference(cnf_transformation,[],[f43]) ).
% 2.13/0.99  
% 2.13/0.99  cnf(c_10,plain,
% 2.13/0.99      ( ~ r1_tarski(X0,X1) | m1_subset_1(X0,k1_zfmisc_1(X1)) ),
% 2.13/0.99      inference(cnf_transformation,[],[f50]) ).
% 2.13/0.99  
% 2.13/0.99  cnf(c_131,plain,
% 2.13/0.99      ( ~ r1_tarski(X0,X1) | m1_subset_1(X0,k1_zfmisc_1(X1)) ),
% 2.13/0.99      inference(prop_impl,[status(thm)],[c_10]) ).
% 2.13/0.99  
% 2.13/0.99  cnf(c_156,plain,
% 2.13/0.99      ( ~ r1_tarski(X0,X1) | ~ v1_xboole_0(X1) | v1_xboole_0(X0) ),
% 2.13/0.99      inference(bin_hyper_res,[status(thm)],[c_5,c_131]) ).
% 2.13/0.99  
% 2.13/0.99  cnf(c_652,plain,
% 2.13/0.99      ( r1_tarski(X0,X1) != iProver_top
% 2.13/0.99      | v1_xboole_0(X1) != iProver_top
% 2.13/0.99      | v1_xboole_0(X0) = iProver_top ),
% 2.13/0.99      inference(predicate_to_equality,[status(thm)],[c_156]) ).
% 2.13/0.99  
% 2.13/0.99  cnf(c_1001,plain,
% 2.13/0.99      ( v1_xboole_0(sK3) = iProver_top
% 2.13/0.99      | v1_xboole_0(sK4) != iProver_top ),
% 2.13/0.99      inference(superposition,[status(thm)],[c_655,c_652]) ).
% 2.13/0.99  
% 2.13/0.99  cnf(c_2389,plain,
% 2.13/0.99      ( v1_xboole_0(sK3) = iProver_top
% 2.13/0.99      | v1_xboole_0(k1_xboole_0) != iProver_top ),
% 2.13/0.99      inference(demodulation,[status(thm)],[c_2383,c_1001]) ).
% 2.13/0.99  
% 2.13/0.99  cnf(c_3434,plain,
% 2.13/0.99      ( k5_xboole_0(k1_tarski(sK0(k1_xboole_0)),k5_xboole_0(k1_xboole_0,k1_setfam_1(k2_tarski(k1_xboole_0,k1_tarski(sK0(k1_xboole_0)))))) = k1_xboole_0
% 2.13/0.99      | v1_xboole_0(sK3) = iProver_top ),
% 2.13/0.99      inference(superposition,[status(thm)],[c_1603,c_2389]) ).
% 2.13/0.99  
% 2.13/0.99  cnf(c_4,plain,
% 2.13/0.99      ( k5_xboole_0(k1_tarski(X0),k5_xboole_0(X1,k1_setfam_1(k2_tarski(X1,k1_tarski(X0))))) != k1_xboole_0 ),
% 2.13/0.99      inference(cnf_transformation,[],[f59]) ).
% 2.13/0.99  
% 2.13/0.99  cnf(c_3833,plain,
% 2.13/0.99      ( v1_xboole_0(sK3) = iProver_top ),
% 2.13/0.99      inference(forward_subsumption_resolution,
% 2.13/0.99                [status(thm)],
% 2.13/0.99                [c_3434,c_4]) ).
% 2.13/0.99  
% 2.13/0.99  cnf(c_2,plain,
% 2.13/0.99      ( r2_hidden(sK1(X0),X0) | k1_xboole_0 = X0 ),
% 2.13/0.99      inference(cnf_transformation,[],[f38]) ).
% 2.13/0.99  
% 2.13/0.99  cnf(c_665,plain,
% 2.13/0.99      ( k1_xboole_0 = X0 | r2_hidden(sK1(X0),X0) = iProver_top ),
% 2.13/0.99      inference(predicate_to_equality,[status(thm)],[c_2]) ).
% 2.13/0.99  
% 2.13/0.99  cnf(c_1,plain,
% 2.13/0.99      ( ~ r2_hidden(X0,X1) | ~ v1_xboole_0(X1) ),
% 2.13/0.99      inference(cnf_transformation,[],[f36]) ).
% 2.13/0.99  
% 2.13/0.99  cnf(c_666,plain,
% 2.13/0.99      ( r2_hidden(X0,X1) != iProver_top
% 2.13/0.99      | v1_xboole_0(X1) != iProver_top ),
% 2.13/0.99      inference(predicate_to_equality,[status(thm)],[c_1]) ).
% 2.13/0.99  
% 2.13/0.99  cnf(c_1016,plain,
% 2.13/0.99      ( k1_xboole_0 = X0 | v1_xboole_0(X0) != iProver_top ),
% 2.13/0.99      inference(superposition,[status(thm)],[c_665,c_666]) ).
% 2.13/0.99  
% 2.13/0.99  cnf(c_3836,plain,
% 2.13/0.99      ( sK3 = k1_xboole_0 ),
% 2.13/0.99      inference(superposition,[status(thm)],[c_3833,c_1016]) ).
% 2.13/0.99  
% 2.13/0.99  cnf(c_2391,plain,
% 2.13/0.99      ( r1_tarski(k8_setfam_1(sK2,k1_xboole_0),k8_setfam_1(sK2,sK3)) != iProver_top ),
% 2.13/0.99      inference(demodulation,[status(thm)],[c_2383,c_656]) ).
% 2.13/0.99  
% 2.13/0.99  cnf(c_2397,plain,
% 2.13/0.99      ( r1_tarski(sK2,k8_setfam_1(sK2,sK3)) != iProver_top ),
% 2.13/0.99      inference(light_normalisation,[status(thm)],[c_2391,c_2303]) ).
% 2.13/0.99  
% 2.13/0.99  cnf(c_3913,plain,
% 2.13/0.99      ( r1_tarski(sK2,k8_setfam_1(sK2,k1_xboole_0)) != iProver_top ),
% 2.13/0.99      inference(demodulation,[status(thm)],[c_3836,c_2397]) ).
% 2.13/0.99  
% 2.13/0.99  cnf(c_3923,plain,
% 2.13/0.99      ( r1_tarski(sK2,sK2) != iProver_top ),
% 2.13/0.99      inference(light_normalisation,[status(thm)],[c_3913,c_2303]) ).
% 2.13/0.99  
% 2.13/0.99  cnf(c_661,plain,
% 2.13/0.99      ( m1_subset_1(X0,k1_zfmisc_1(k1_zfmisc_1(X1))) != iProver_top
% 2.13/0.99      | m1_subset_1(k8_setfam_1(X1,X0),k1_zfmisc_1(X1)) = iProver_top ),
% 2.13/0.99      inference(predicate_to_equality,[status(thm)],[c_8]) ).
% 2.13/0.99  
% 2.13/0.99  cnf(c_2314,plain,
% 2.13/0.99      ( m1_subset_1(sK2,k1_zfmisc_1(sK2)) = iProver_top
% 2.13/0.99      | m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_zfmisc_1(sK2))) != iProver_top ),
% 2.13/0.99      inference(superposition,[status(thm)],[c_2303,c_661]) ).
% 2.13/0.99  
% 2.13/0.99  cnf(c_2791,plain,
% 2.13/0.99      ( m1_subset_1(sK2,k1_zfmisc_1(sK2)) = iProver_top ),
% 2.13/0.99      inference(global_propositional_subsumption,
% 2.13/0.99                [status(thm)],
% 2.13/0.99                [c_2314,c_18,c_279,c_873,c_951,c_948,c_2073]) ).
% 2.13/0.99  
% 2.13/0.99  cnf(c_658,plain,
% 2.13/0.99      ( r1_tarski(X0,X1) = iProver_top
% 2.13/0.99      | m1_subset_1(X0,k1_zfmisc_1(X1)) != iProver_top ),
% 2.13/0.99      inference(predicate_to_equality,[status(thm)],[c_11]) ).
% 2.13/0.99  
% 2.13/0.99  cnf(c_2796,plain,
% 2.13/0.99      ( r1_tarski(sK2,sK2) = iProver_top ),
% 2.13/0.99      inference(superposition,[status(thm)],[c_2791,c_658]) ).
% 2.13/0.99  
% 2.13/0.99  cnf(contradiction,plain,
% 2.13/0.99      ( $false ),
% 2.13/0.99      inference(minisat,[status(thm)],[c_3923,c_2796]) ).
% 2.13/0.99  
% 2.13/0.99  
% 2.13/0.99  % SZS output end CNFRefutation for theBenchmark.p
% 2.13/0.99  
% 2.13/0.99  ------                               Statistics
% 2.13/0.99  
% 2.13/0.99  ------ General
% 2.13/0.99  
% 2.13/0.99  abstr_ref_over_cycles:                  0
% 2.13/0.99  abstr_ref_under_cycles:                 0
% 2.13/0.99  gc_basic_clause_elim:                   0
% 2.13/0.99  forced_gc_time:                         0
% 2.13/0.99  parsing_time:                           0.021
% 2.13/0.99  unif_index_cands_time:                  0.
% 2.13/0.99  unif_index_add_time:                    0.
% 2.13/0.99  orderings_time:                         0.
% 2.13/0.99  out_proof_time:                         0.01
% 2.13/0.99  total_time:                             0.149
% 2.13/0.99  num_of_symbols:                         48
% 2.13/0.99  num_of_terms:                           2696
% 2.13/0.99  
% 2.13/0.99  ------ Preprocessing
% 2.13/0.99  
% 2.13/0.99  num_of_splits:                          0
% 2.13/0.99  num_of_split_atoms:                     0
% 2.13/0.99  num_of_reused_defs:                     0
% 2.13/0.99  num_eq_ax_congr_red:                    16
% 2.13/0.99  num_of_sem_filtered_clauses:            1
% 2.13/0.99  num_of_subtypes:                        0
% 2.13/0.99  monotx_restored_types:                  0
% 2.13/0.99  sat_num_of_epr_types:                   0
% 2.13/0.99  sat_num_of_non_cyclic_types:            0
% 2.13/0.99  sat_guarded_non_collapsed_types:        0
% 2.13/0.99  num_pure_diseq_elim:                    0
% 2.13/0.99  simp_replaced_by:                       0
% 2.13/0.99  res_preprocessed:                       72
% 2.13/0.99  prep_upred:                             0
% 2.13/0.99  prep_unflattend:                        8
% 2.13/0.99  smt_new_axioms:                         0
% 2.13/0.99  pred_elim_cands:                        4
% 2.13/0.99  pred_elim:                              0
% 2.13/0.99  pred_elim_cl:                           0
% 2.13/0.99  pred_elim_cycles:                       1
% 2.13/0.99  merged_defs:                            6
% 2.13/0.99  merged_defs_ncl:                        0
% 2.13/0.99  bin_hyper_res:                          7
% 2.13/0.99  prep_cycles:                            3
% 2.13/0.99  pred_elim_time:                         0.001
% 2.13/0.99  splitting_time:                         0.
% 2.13/0.99  sem_filter_time:                        0.
% 2.13/0.99  monotx_time:                            0.001
% 2.13/0.99  subtype_inf_time:                       0.
% 2.13/0.99  
% 2.13/0.99  ------ Problem properties
% 2.13/0.99  
% 2.13/0.99  clauses:                                17
% 2.13/0.99  conjectures:                            4
% 2.13/0.99  epr:                                    3
% 2.13/0.99  horn:                                   13
% 2.13/0.99  ground:                                 4
% 2.13/0.99  unary:                                  5
% 2.13/0.99  binary:                                 9
% 2.13/0.99  lits:                                   32
% 2.13/0.99  lits_eq:                                8
% 2.13/0.99  fd_pure:                                0
% 2.13/0.99  fd_pseudo:                              0
% 2.13/0.99  fd_cond:                                3
% 2.13/0.99  fd_pseudo_cond:                         0
% 2.13/0.99  ac_symbols:                             0
% 2.13/0.99  
% 2.13/0.99  ------ Propositional Solver
% 2.13/0.99  
% 2.13/0.99  prop_solver_calls:                      24
% 2.13/0.99  prop_fast_solver_calls:                 453
% 2.13/0.99  smt_solver_calls:                       0
% 2.13/0.99  smt_fast_solver_calls:                  0
% 2.13/0.99  prop_num_of_clauses:                    1343
% 2.13/0.99  prop_preprocess_simplified:             3784
% 2.13/0.99  prop_fo_subsumed:                       5
% 2.13/0.99  prop_solver_time:                       0.
% 2.13/0.99  smt_solver_time:                        0.
% 2.13/0.99  smt_fast_solver_time:                   0.
% 2.13/0.99  prop_fast_solver_time:                  0.
% 2.13/0.99  prop_unsat_core_time:                   0.
% 2.13/0.99  
% 2.13/0.99  ------ QBF
% 2.13/0.99  
% 2.13/0.99  qbf_q_res:                              0
% 2.13/0.99  qbf_num_tautologies:                    0
% 2.13/0.99  qbf_prep_cycles:                        0
% 2.13/0.99  
% 2.13/0.99  ------ BMC1
% 2.13/0.99  
% 2.13/0.99  bmc1_current_bound:                     -1
% 2.13/0.99  bmc1_last_solved_bound:                 -1
% 2.13/0.99  bmc1_unsat_core_size:                   -1
% 2.13/0.99  bmc1_unsat_core_parents_size:           -1
% 2.13/0.99  bmc1_merge_next_fun:                    0
% 2.13/0.99  bmc1_unsat_core_clauses_time:           0.
% 2.13/0.99  
% 2.13/0.99  ------ Instantiation
% 2.13/0.99  
% 2.13/0.99  inst_num_of_clauses:                    489
% 2.13/0.99  inst_num_in_passive:                    207
% 2.13/0.99  inst_num_in_active:                     263
% 2.13/0.99  inst_num_in_unprocessed:                19
% 2.13/0.99  inst_num_of_loops:                      330
% 2.13/0.99  inst_num_of_learning_restarts:          0
% 2.13/0.99  inst_num_moves_active_passive:          64
% 2.13/0.99  inst_lit_activity:                      0
% 2.13/0.99  inst_lit_activity_moves:                0
% 2.13/0.99  inst_num_tautologies:                   0
% 2.13/0.99  inst_num_prop_implied:                  0
% 2.13/0.99  inst_num_existing_simplified:           0
% 2.13/0.99  inst_num_eq_res_simplified:             0
% 2.13/0.99  inst_num_child_elim:                    0
% 2.13/0.99  inst_num_of_dismatching_blockings:      92
% 2.13/0.99  inst_num_of_non_proper_insts:           334
% 2.13/0.99  inst_num_of_duplicates:                 0
% 2.13/0.99  inst_inst_num_from_inst_to_res:         0
% 2.13/0.99  inst_dismatching_checking_time:         0.
% 2.13/0.99  
% 2.13/0.99  ------ Resolution
% 2.13/0.99  
% 2.13/0.99  res_num_of_clauses:                     0
% 2.13/0.99  res_num_in_passive:                     0
% 2.13/0.99  res_num_in_active:                      0
% 2.13/0.99  res_num_of_loops:                       75
% 2.13/0.99  res_forward_subset_subsumed:            34
% 2.13/0.99  res_backward_subset_subsumed:           0
% 2.13/0.99  res_forward_subsumed:                   0
% 2.13/0.99  res_backward_subsumed:                  0
% 2.13/0.99  res_forward_subsumption_resolution:     0
% 2.13/0.99  res_backward_subsumption_resolution:    0
% 2.13/0.99  res_clause_to_clause_subsumption:       181
% 2.13/0.99  res_orphan_elimination:                 0
% 2.13/0.99  res_tautology_del:                      102
% 2.13/0.99  res_num_eq_res_simplified:              0
% 2.13/0.99  res_num_sel_changes:                    0
% 2.13/0.99  res_moves_from_active_to_pass:          0
% 2.13/0.99  
% 2.13/0.99  ------ Superposition
% 2.13/0.99  
% 2.13/0.99  sup_time_total:                         0.
% 2.13/0.99  sup_time_generating:                    0.
% 2.13/0.99  sup_time_sim_full:                      0.
% 2.13/0.99  sup_time_sim_immed:                     0.
% 2.13/0.99  
% 2.13/0.99  sup_num_of_clauses:                     58
% 2.13/0.99  sup_num_in_active:                      31
% 2.13/0.99  sup_num_in_passive:                     27
% 2.13/0.99  sup_num_of_loops:                       64
% 2.13/0.99  sup_fw_superposition:                   52
% 2.13/0.99  sup_bw_superposition:                   54
% 2.13/0.99  sup_immediate_simplified:               22
% 2.13/0.99  sup_given_eliminated:                   1
% 2.13/0.99  comparisons_done:                       0
% 2.13/0.99  comparisons_avoided:                    10
% 2.13/0.99  
% 2.13/0.99  ------ Simplifications
% 2.13/0.99  
% 2.13/0.99  
% 2.13/0.99  sim_fw_subset_subsumed:                 15
% 2.13/0.99  sim_bw_subset_subsumed:                 18
% 2.13/0.99  sim_fw_subsumed:                        0
% 2.13/0.99  sim_bw_subsumed:                        0
% 2.13/0.99  sim_fw_subsumption_res:                 1
% 2.13/0.99  sim_bw_subsumption_res:                 0
% 2.13/0.99  sim_tautology_del:                      7
% 2.13/0.99  sim_eq_tautology_del:                   7
% 2.13/0.99  sim_eq_res_simp:                        0
% 2.13/0.99  sim_fw_demodulated:                     1
% 2.13/0.99  sim_bw_demodulated:                     22
% 2.13/0.99  sim_light_normalised:                   10
% 2.13/0.99  sim_joinable_taut:                      0
% 2.13/0.99  sim_joinable_simp:                      0
% 2.13/0.99  sim_ac_normalised:                      0
% 2.13/0.99  sim_smt_subsumption:                    0
% 2.13/0.99  
%------------------------------------------------------------------------------
