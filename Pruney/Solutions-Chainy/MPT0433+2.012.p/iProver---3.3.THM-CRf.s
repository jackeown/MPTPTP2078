%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n013.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 11:42:52 EST 2020

% Result     : Theorem 3.85s
% Output     : CNFRefutation 3.85s
% Verified   : 
% Statistics : Number of formulae       :   88 ( 309 expanded)
%              Number of clauses        :   39 (  64 expanded)
%              Number of leaves         :   15 (  89 expanded)
%              Depth                    :   15
%              Number of atoms          :  162 ( 488 expanded)
%              Number of equality atoms :   62 ( 236 expanded)
%              Maximal formula depth    :    7 (   3 average)
%              Maximal clause size      :    6 (   2 average)
%              Maximal term depth       :    7 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f3,axiom,(
    ! [X0,X1] : r1_tarski(k3_xboole_0(X0,X1),X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f27,plain,(
    ! [X0,X1] : r1_tarski(k3_xboole_0(X0,X1),X0) ),
    inference(cnf_transformation,[],[f3])).

fof(f9,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f33,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1)) ),
    inference(cnf_transformation,[],[f9])).

fof(f6,axiom,(
    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f30,plain,(
    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f6])).

fof(f7,axiom,(
    ! [X0,X1,X2] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f31,plain,(
    ! [X2,X0,X1] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2) ),
    inference(cnf_transformation,[],[f7])).

fof(f41,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k2_enumset1(X0,X0,X0,X1) ),
    inference(definition_unfolding,[],[f30,f31])).

fof(f42,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k2_enumset1(X0,X0,X0,X1)) ),
    inference(definition_unfolding,[],[f33,f41])).

fof(f46,plain,(
    ! [X0,X1] : r1_tarski(k1_setfam_1(k2_enumset1(X0,X0,X0,X1)),X0) ),
    inference(definition_unfolding,[],[f27,f42])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
     => k2_xboole_0(X0,X1) = X1 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f15,plain,(
    ! [X0,X1] :
      ( k2_xboole_0(X0,X1) = X1
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f26,plain,(
    ! [X0,X1] :
      ( k2_xboole_0(X0,X1) = X1
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f15])).

fof(f8,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f32,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1)) ),
    inference(cnf_transformation,[],[f8])).

fof(f43,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k2_enumset1(X0,X0,X0,X1)) ),
    inference(definition_unfolding,[],[f32,f41])).

fof(f45,plain,(
    ! [X0,X1] :
      ( k3_tarski(k2_enumset1(X0,X0,X0,X1)) = X1
      | ~ r1_tarski(X0,X1) ) ),
    inference(definition_unfolding,[],[f26,f43])).

fof(f1,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f25,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f1])).

fof(f44,plain,(
    ! [X0,X1] : k1_setfam_1(k2_enumset1(X0,X0,X0,X1)) = k1_setfam_1(k2_enumset1(X1,X1,X1,X0)) ),
    inference(definition_unfolding,[],[f25,f42,f42])).

fof(f13,conjecture,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( v1_relat_1(X1)
         => r1_tarski(k1_relat_1(k3_xboole_0(X0,X1)),k3_xboole_0(k1_relat_1(X0),k1_relat_1(X1))) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f14,negated_conjecture,(
    ~ ! [X0] :
        ( v1_relat_1(X0)
       => ! [X1] :
            ( v1_relat_1(X1)
           => r1_tarski(k1_relat_1(k3_xboole_0(X0,X1)),k3_xboole_0(k1_relat_1(X0),k1_relat_1(X1))) ) ) ),
    inference(negated_conjecture,[],[f13])).

fof(f20,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ~ r1_tarski(k1_relat_1(k3_xboole_0(X0,X1)),k3_xboole_0(k1_relat_1(X0),k1_relat_1(X1)))
          & v1_relat_1(X1) )
      & v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f23,plain,(
    ! [X0] :
      ( ? [X1] :
          ( ~ r1_tarski(k1_relat_1(k3_xboole_0(X0,X1)),k3_xboole_0(k1_relat_1(X0),k1_relat_1(X1)))
          & v1_relat_1(X1) )
     => ( ~ r1_tarski(k1_relat_1(k3_xboole_0(X0,sK1)),k3_xboole_0(k1_relat_1(X0),k1_relat_1(sK1)))
        & v1_relat_1(sK1) ) ) ),
    introduced(choice_axiom,[])).

fof(f22,plain,
    ( ? [X0] :
        ( ? [X1] :
            ( ~ r1_tarski(k1_relat_1(k3_xboole_0(X0,X1)),k3_xboole_0(k1_relat_1(X0),k1_relat_1(X1)))
            & v1_relat_1(X1) )
        & v1_relat_1(X0) )
   => ( ? [X1] :
          ( ~ r1_tarski(k1_relat_1(k3_xboole_0(sK0,X1)),k3_xboole_0(k1_relat_1(sK0),k1_relat_1(X1)))
          & v1_relat_1(X1) )
      & v1_relat_1(sK0) ) ),
    introduced(choice_axiom,[])).

fof(f24,plain,
    ( ~ r1_tarski(k1_relat_1(k3_xboole_0(sK0,sK1)),k3_xboole_0(k1_relat_1(sK0),k1_relat_1(sK1)))
    & v1_relat_1(sK1)
    & v1_relat_1(sK0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f20,f23,f22])).

fof(f38,plain,(
    v1_relat_1(sK0) ),
    inference(cnf_transformation,[],[f24])).

fof(f39,plain,(
    v1_relat_1(sK1) ),
    inference(cnf_transformation,[],[f24])).

fof(f11,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(X0))
         => v1_relat_1(X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f18,plain,(
    ! [X0] :
      ( ! [X1] :
          ( v1_relat_1(X1)
          | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f36,plain,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f10,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f21,plain,(
    ! [X0,X1] :
      ( ( m1_subset_1(X0,k1_zfmisc_1(X1))
        | ~ r1_tarski(X0,X1) )
      & ( r1_tarski(X0,X1)
        | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ) ) ),
    inference(nnf_transformation,[],[f10])).

fof(f35,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f12,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( v1_relat_1(X1)
         => k2_xboole_0(k1_relat_1(X0),k1_relat_1(X1)) = k1_relat_1(k2_xboole_0(X0,X1)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f19,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k2_xboole_0(k1_relat_1(X0),k1_relat_1(X1)) = k1_relat_1(k2_xboole_0(X0,X1))
          | ~ v1_relat_1(X1) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f37,plain,(
    ! [X0,X1] :
      ( k2_xboole_0(k1_relat_1(X0),k1_relat_1(X1)) = k1_relat_1(k2_xboole_0(X0,X1))
      | ~ v1_relat_1(X1)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f49,plain,(
    ! [X0,X1] :
      ( k3_tarski(k2_enumset1(k1_relat_1(X0),k1_relat_1(X0),k1_relat_1(X0),k1_relat_1(X1))) = k1_relat_1(k3_tarski(k2_enumset1(X0,X0,X0,X1)))
      | ~ v1_relat_1(X1)
      | ~ v1_relat_1(X0) ) ),
    inference(definition_unfolding,[],[f37,f43,f43])).

fof(f5,axiom,(
    ! [X0,X1] : r1_tarski(X0,k2_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f29,plain,(
    ! [X0,X1] : r1_tarski(X0,k2_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f5])).

fof(f48,plain,(
    ! [X0,X1] : r1_tarski(X0,k3_tarski(k2_enumset1(X0,X0,X0,X1))) ),
    inference(definition_unfolding,[],[f29,f43])).

fof(f4,axiom,(
    ! [X0,X1,X2] :
      ( ( r1_tarski(X0,X2)
        & r1_tarski(X0,X1) )
     => r1_tarski(X0,k3_xboole_0(X1,X2)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f16,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,k3_xboole_0(X1,X2))
      | ~ r1_tarski(X0,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f17,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,k3_xboole_0(X1,X2))
      | ~ r1_tarski(X0,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(flattening,[],[f16])).

fof(f28,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(X0,k3_xboole_0(X1,X2))
      | ~ r1_tarski(X0,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f47,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(X0,k1_setfam_1(k2_enumset1(X1,X1,X1,X2)))
      | ~ r1_tarski(X0,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(definition_unfolding,[],[f28,f42])).

fof(f40,plain,(
    ~ r1_tarski(k1_relat_1(k3_xboole_0(sK0,sK1)),k3_xboole_0(k1_relat_1(sK0),k1_relat_1(sK1))) ),
    inference(cnf_transformation,[],[f24])).

fof(f50,plain,(
    ~ r1_tarski(k1_relat_1(k1_setfam_1(k2_enumset1(sK0,sK0,sK0,sK1))),k1_setfam_1(k2_enumset1(k1_relat_1(sK0),k1_relat_1(sK0),k1_relat_1(sK0),k1_relat_1(sK1)))) ),
    inference(definition_unfolding,[],[f40,f42,f42])).

cnf(c_2,plain,
    ( r1_tarski(k1_setfam_1(k2_enumset1(X0,X0,X0,X1)),X0) ),
    inference(cnf_transformation,[],[f46])).

cnf(c_7082,plain,
    ( r1_tarski(k1_setfam_1(k2_enumset1(X0,X0,X0,X1)),X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2])).

cnf(c_1,plain,
    ( ~ r1_tarski(X0,X1)
    | k3_tarski(k2_enumset1(X0,X0,X0,X1)) = X1 ),
    inference(cnf_transformation,[],[f45])).

cnf(c_7083,plain,
    ( k3_tarski(k2_enumset1(X0,X0,X0,X1)) = X1
    | r1_tarski(X0,X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1])).

cnf(c_7193,plain,
    ( k3_tarski(k2_enumset1(k1_setfam_1(k2_enumset1(X0,X0,X0,X1)),k1_setfam_1(k2_enumset1(X0,X0,X0,X1)),k1_setfam_1(k2_enumset1(X0,X0,X0,X1)),X0)) = X0 ),
    inference(superposition,[status(thm)],[c_7082,c_7083])).

cnf(c_0,plain,
    ( k1_setfam_1(k2_enumset1(X0,X0,X0,X1)) = k1_setfam_1(k2_enumset1(X1,X1,X1,X0)) ),
    inference(cnf_transformation,[],[f44])).

cnf(c_11,negated_conjecture,
    ( v1_relat_1(sK0) ),
    inference(cnf_transformation,[],[f38])).

cnf(c_7076,plain,
    ( v1_relat_1(sK0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_11])).

cnf(c_10,negated_conjecture,
    ( v1_relat_1(sK1) ),
    inference(cnf_transformation,[],[f39])).

cnf(c_7077,plain,
    ( v1_relat_1(sK1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_10])).

cnf(c_7,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | ~ v1_relat_1(X1)
    | v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f36])).

cnf(c_5,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(X1))
    | ~ r1_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f35])).

cnf(c_87,plain,
    ( ~ r1_tarski(X0,X1)
    | m1_subset_1(X0,k1_zfmisc_1(X1)) ),
    inference(prop_impl,[status(thm)],[c_5])).

cnf(c_88,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(X1))
    | ~ r1_tarski(X0,X1) ),
    inference(renaming,[status(thm)],[c_87])).

cnf(c_108,plain,
    ( ~ r1_tarski(X0,X1)
    | ~ v1_relat_1(X1)
    | v1_relat_1(X0) ),
    inference(bin_hyper_res,[status(thm)],[c_7,c_88])).

cnf(c_7075,plain,
    ( r1_tarski(X0,X1) != iProver_top
    | v1_relat_1(X1) != iProver_top
    | v1_relat_1(X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_108])).

cnf(c_7223,plain,
    ( v1_relat_1(X0) != iProver_top
    | v1_relat_1(k1_setfam_1(k2_enumset1(X0,X0,X0,X1))) = iProver_top ),
    inference(superposition,[status(thm)],[c_7082,c_7075])).

cnf(c_8,plain,
    ( ~ v1_relat_1(X0)
    | ~ v1_relat_1(X1)
    | k3_tarski(k2_enumset1(k1_relat_1(X0),k1_relat_1(X0),k1_relat_1(X0),k1_relat_1(X1))) = k1_relat_1(k3_tarski(k2_enumset1(X0,X0,X0,X1))) ),
    inference(cnf_transformation,[],[f49])).

cnf(c_7079,plain,
    ( k3_tarski(k2_enumset1(k1_relat_1(X0),k1_relat_1(X0),k1_relat_1(X0),k1_relat_1(X1))) = k1_relat_1(k3_tarski(k2_enumset1(X0,X0,X0,X1)))
    | v1_relat_1(X0) != iProver_top
    | v1_relat_1(X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_8])).

cnf(c_7332,plain,
    ( k3_tarski(k2_enumset1(k1_relat_1(k1_setfam_1(k2_enumset1(X0,X0,X0,X1))),k1_relat_1(k1_setfam_1(k2_enumset1(X0,X0,X0,X1))),k1_relat_1(k1_setfam_1(k2_enumset1(X0,X0,X0,X1))),k1_relat_1(X2))) = k1_relat_1(k3_tarski(k2_enumset1(k1_setfam_1(k2_enumset1(X0,X0,X0,X1)),k1_setfam_1(k2_enumset1(X0,X0,X0,X1)),k1_setfam_1(k2_enumset1(X0,X0,X0,X1)),X2)))
    | v1_relat_1(X0) != iProver_top
    | v1_relat_1(X2) != iProver_top ),
    inference(superposition,[status(thm)],[c_7223,c_7079])).

cnf(c_9091,plain,
    ( k3_tarski(k2_enumset1(k1_relat_1(k1_setfam_1(k2_enumset1(sK1,sK1,sK1,X0))),k1_relat_1(k1_setfam_1(k2_enumset1(sK1,sK1,sK1,X0))),k1_relat_1(k1_setfam_1(k2_enumset1(sK1,sK1,sK1,X0))),k1_relat_1(X1))) = k1_relat_1(k3_tarski(k2_enumset1(k1_setfam_1(k2_enumset1(sK1,sK1,sK1,X0)),k1_setfam_1(k2_enumset1(sK1,sK1,sK1,X0)),k1_setfam_1(k2_enumset1(sK1,sK1,sK1,X0)),X1)))
    | v1_relat_1(X1) != iProver_top ),
    inference(superposition,[status(thm)],[c_7077,c_7332])).

cnf(c_9235,plain,
    ( k3_tarski(k2_enumset1(k1_relat_1(k1_setfam_1(k2_enumset1(sK1,sK1,sK1,X0))),k1_relat_1(k1_setfam_1(k2_enumset1(sK1,sK1,sK1,X0))),k1_relat_1(k1_setfam_1(k2_enumset1(sK1,sK1,sK1,X0))),k1_relat_1(sK0))) = k1_relat_1(k3_tarski(k2_enumset1(k1_setfam_1(k2_enumset1(sK1,sK1,sK1,X0)),k1_setfam_1(k2_enumset1(sK1,sK1,sK1,X0)),k1_setfam_1(k2_enumset1(sK1,sK1,sK1,X0)),sK0))) ),
    inference(superposition,[status(thm)],[c_7076,c_9091])).

cnf(c_4,plain,
    ( r1_tarski(X0,k3_tarski(k2_enumset1(X0,X0,X0,X1))) ),
    inference(cnf_transformation,[],[f48])).

cnf(c_7080,plain,
    ( r1_tarski(X0,k3_tarski(k2_enumset1(X0,X0,X0,X1))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_4])).

cnf(c_9281,plain,
    ( r1_tarski(k1_relat_1(k1_setfam_1(k2_enumset1(sK1,sK1,sK1,X0))),k1_relat_1(k3_tarski(k2_enumset1(k1_setfam_1(k2_enumset1(sK1,sK1,sK1,X0)),k1_setfam_1(k2_enumset1(sK1,sK1,sK1,X0)),k1_setfam_1(k2_enumset1(sK1,sK1,sK1,X0)),sK0)))) = iProver_top ),
    inference(superposition,[status(thm)],[c_9235,c_7080])).

cnf(c_9456,plain,
    ( r1_tarski(k1_relat_1(k1_setfam_1(k2_enumset1(X0,X0,X0,sK1))),k1_relat_1(k3_tarski(k2_enumset1(k1_setfam_1(k2_enumset1(X0,X0,X0,sK1)),k1_setfam_1(k2_enumset1(X0,X0,X0,sK1)),k1_setfam_1(k2_enumset1(X0,X0,X0,sK1)),sK0)))) = iProver_top ),
    inference(superposition,[status(thm)],[c_0,c_9281])).

cnf(c_9632,plain,
    ( r1_tarski(k1_relat_1(k1_setfam_1(k2_enumset1(sK0,sK0,sK0,sK1))),k1_relat_1(sK0)) = iProver_top ),
    inference(superposition,[status(thm)],[c_7193,c_9456])).

cnf(c_7168,plain,
    ( r1_tarski(k1_setfam_1(k2_enumset1(X0,X0,X0,X1)),X1) = iProver_top ),
    inference(superposition,[status(thm)],[c_0,c_7082])).

cnf(c_7195,plain,
    ( k3_tarski(k2_enumset1(k1_setfam_1(k2_enumset1(X0,X0,X0,X1)),k1_setfam_1(k2_enumset1(X0,X0,X0,X1)),k1_setfam_1(k2_enumset1(X0,X0,X0,X1)),X1)) = X1 ),
    inference(superposition,[status(thm)],[c_7168,c_7083])).

cnf(c_9092,plain,
    ( k3_tarski(k2_enumset1(k1_relat_1(k1_setfam_1(k2_enumset1(sK0,sK0,sK0,X0))),k1_relat_1(k1_setfam_1(k2_enumset1(sK0,sK0,sK0,X0))),k1_relat_1(k1_setfam_1(k2_enumset1(sK0,sK0,sK0,X0))),k1_relat_1(X1))) = k1_relat_1(k3_tarski(k2_enumset1(k1_setfam_1(k2_enumset1(sK0,sK0,sK0,X0)),k1_setfam_1(k2_enumset1(sK0,sK0,sK0,X0)),k1_setfam_1(k2_enumset1(sK0,sK0,sK0,X0)),X1)))
    | v1_relat_1(X1) != iProver_top ),
    inference(superposition,[status(thm)],[c_7076,c_7332])).

cnf(c_9304,plain,
    ( k3_tarski(k2_enumset1(k1_relat_1(k1_setfam_1(k2_enumset1(sK0,sK0,sK0,X0))),k1_relat_1(k1_setfam_1(k2_enumset1(sK0,sK0,sK0,X0))),k1_relat_1(k1_setfam_1(k2_enumset1(sK0,sK0,sK0,X0))),k1_relat_1(sK1))) = k1_relat_1(k3_tarski(k2_enumset1(k1_setfam_1(k2_enumset1(sK0,sK0,sK0,X0)),k1_setfam_1(k2_enumset1(sK0,sK0,sK0,X0)),k1_setfam_1(k2_enumset1(sK0,sK0,sK0,X0)),sK1))) ),
    inference(superposition,[status(thm)],[c_7077,c_9092])).

cnf(c_9351,plain,
    ( r1_tarski(k1_relat_1(k1_setfam_1(k2_enumset1(sK0,sK0,sK0,X0))),k1_relat_1(k3_tarski(k2_enumset1(k1_setfam_1(k2_enumset1(sK0,sK0,sK0,X0)),k1_setfam_1(k2_enumset1(sK0,sK0,sK0,X0)),k1_setfam_1(k2_enumset1(sK0,sK0,sK0,X0)),sK1)))) = iProver_top ),
    inference(superposition,[status(thm)],[c_9304,c_7080])).

cnf(c_9499,plain,
    ( r1_tarski(k1_relat_1(k1_setfam_1(k2_enumset1(sK0,sK0,sK0,sK1))),k1_relat_1(sK1)) = iProver_top ),
    inference(superposition,[status(thm)],[c_7195,c_9351])).

cnf(c_3,plain,
    ( ~ r1_tarski(X0,X1)
    | ~ r1_tarski(X0,X2)
    | r1_tarski(X0,k1_setfam_1(k2_enumset1(X1,X1,X1,X2))) ),
    inference(cnf_transformation,[],[f47])).

cnf(c_5664,plain,
    ( r1_tarski(X0,X1) != iProver_top
    | r1_tarski(X0,X2) != iProver_top
    | r1_tarski(X0,k1_setfam_1(k2_enumset1(X1,X1,X1,X2))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3])).

cnf(c_9,negated_conjecture,
    ( ~ r1_tarski(k1_relat_1(k1_setfam_1(k2_enumset1(sK0,sK0,sK0,sK1))),k1_setfam_1(k2_enumset1(k1_relat_1(sK0),k1_relat_1(sK0),k1_relat_1(sK0),k1_relat_1(sK1)))) ),
    inference(cnf_transformation,[],[f50])).

cnf(c_5662,plain,
    ( r1_tarski(k1_relat_1(k1_setfam_1(k2_enumset1(sK0,sK0,sK0,sK1))),k1_setfam_1(k2_enumset1(k1_relat_1(sK0),k1_relat_1(sK0),k1_relat_1(sK0),k1_relat_1(sK1)))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_9])).

cnf(c_5696,plain,
    ( r1_tarski(k1_relat_1(k1_setfam_1(k2_enumset1(sK0,sK0,sK0,sK1))),k1_relat_1(sK1)) != iProver_top
    | r1_tarski(k1_relat_1(k1_setfam_1(k2_enumset1(sK0,sK0,sK0,sK1))),k1_relat_1(sK0)) != iProver_top ),
    inference(superposition,[status(thm)],[c_5664,c_5662])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_9632,c_9499,c_5696])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.12  % Command    : iproveropt_run.sh %d %s
% 0.12/0.33  % Computer   : n013.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.33  % CPULimit   : 60
% 0.12/0.33  % WCLimit    : 600
% 0.12/0.33  % DateTime   : Tue Dec  1 10:23:24 EST 2020
% 0.12/0.33  % CPUTime    : 
% 0.12/0.33  % Running in FOF mode
% 3.85/0.98  % SZS status Started for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.85/0.98  
% 3.85/0.98  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 3.85/0.98  
% 3.85/0.98  ------  iProver source info
% 3.85/0.98  
% 3.85/0.98  git: date: 2020-06-30 10:37:57 +0100
% 3.85/0.98  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 3.85/0.98  git: non_committed_changes: false
% 3.85/0.98  git: last_make_outside_of_git: false
% 3.85/0.98  
% 3.85/0.98  ------ 
% 3.85/0.98  ------ Parsing...
% 3.85/0.98  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 3.85/0.98  
% 3.85/0.98  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe:1:0s pe_e  sf_s  rm: 2 0s  sf_e  pe_s  pe_e 
% 3.85/0.98  
% 3.85/0.98  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 3.85/0.98  
% 3.85/0.98  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 3.85/0.98  ------ Proving...
% 3.85/0.98  ------ Problem Properties 
% 3.85/0.98  
% 3.85/0.98  
% 3.85/0.98  clauses                                 10
% 3.85/0.98  conjectures                             3
% 3.85/0.98  EPR                                     3
% 3.85/0.98  Horn                                    10
% 3.85/0.98  unary                                   6
% 3.85/0.98  binary                                  1
% 3.85/0.98  lits                                    17
% 3.85/0.98  lits eq                                 3
% 3.85/0.98  fd_pure                                 0
% 3.85/0.98  fd_pseudo                               0
% 3.85/0.98  fd_cond                                 0
% 3.85/0.98  fd_pseudo_cond                          0
% 3.85/0.98  AC symbols                              0
% 3.85/0.98  
% 3.85/0.98  ------ Input Options Time Limit: Unbounded
% 3.85/0.98  
% 3.85/0.98  
% 3.85/0.98  
% 3.85/0.98  
% 3.85/0.98  ------ Preprocessing...
% 3.85/0.98  
% 3.85/0.98  ------ Preprocessing... sf_s  rm: 2 0s  sf_e  sf_s  rm: 0 0s  sf_e ------ 
% 3.85/0.98  Current options:
% 3.85/0.98  ------ 
% 3.85/0.98  
% 3.85/0.98  
% 3.85/0.98  
% 3.85/0.98  
% 3.85/0.98  ------ Proving...
% 3.85/0.98  
% 3.85/0.98  
% 3.85/0.98  ------ Preprocessing... sf_s  rm: 0 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 3.85/0.98  
% 3.85/0.98  ------ Proving...
% 3.85/0.98  
% 3.85/0.98  
% 3.85/0.98  ------ Preprocessing...
% 3.85/0.98  
% 3.85/0.98  ------ Preprocessing... sf_s  rm: 2 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 3.85/0.98  
% 3.85/0.98  ------ Proving...
% 3.85/0.98  
% 3.85/0.98  
% 3.85/0.98  ------ Preprocessing... sf_s  rm: 0 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 3.85/0.98  
% 3.85/0.98  ------ Proving...
% 3.85/0.98  
% 3.85/0.98  
% 3.85/0.98  ------ Preprocessing...
% 3.85/0.98  
% 3.85/0.98  ------ Preprocessing... sf_s  rm: 3 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 3.85/0.98  
% 3.85/0.98  ------ Proving...
% 3.85/0.98  
% 3.85/0.98  
% 3.85/0.98  ------ Preprocessing... sf_s  rm: 0 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 3.85/0.98  
% 3.85/0.98  ------ Proving...
% 3.85/0.98  
% 3.85/0.98  
% 3.85/0.98  ------ Preprocessing... sf_s  rm: 2 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 3.85/0.98  
% 3.85/0.98  ------ Proving...
% 3.85/0.98  
% 3.85/0.98  
% 3.85/0.98  ------ Preprocessing... sf_s  rm: 0 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 3.85/0.98  
% 3.85/0.98  ------ Proving...
% 3.85/0.98  
% 3.85/0.98  
% 3.85/0.98  ------ Preprocessing... sf_s  rm: 4 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 3.85/0.98  
% 3.85/0.98  ------ Proving...
% 3.85/0.98  
% 3.85/0.98  
% 3.85/0.98  ------ Preprocessing... sf_s  rm: 0 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 3.85/0.98  
% 3.85/0.98  ------ Proving...
% 3.85/0.98  
% 3.85/0.98  
% 3.85/0.98  ------ Preprocessing... sf_s  rm: 4 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 3.85/0.98  
% 3.85/0.98  ------ Proving...
% 3.85/0.98  
% 3.85/0.98  
% 3.85/0.98  ------ Preprocessing... sf_s  rm: 0 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 3.85/0.98  
% 3.85/0.98  ------ Proving...
% 3.85/0.98  
% 3.85/0.98  
% 3.85/0.98  ------ Preprocessing... sf_s  rm: 4 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 3.85/0.98  
% 3.85/0.98  ------ Proving...
% 3.85/0.98  
% 3.85/0.98  
% 3.85/0.98  ------ Preprocessing... sf_s  rm: 0 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 3.85/0.98  
% 3.85/0.98  ------ Proving...
% 3.85/0.98  
% 3.85/0.98  
% 3.85/0.98  ------ Preprocessing... sf_s  rm: 4 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 3.85/0.98  
% 3.85/0.98  ------ Proving...
% 3.85/0.98  
% 3.85/0.98  
% 3.85/0.98  ------ Preprocessing... sf_s  rm: 0 0s  sf_e 
% 3.85/0.98  
% 3.85/0.98  ------ Proving...
% 3.85/0.98  
% 3.85/0.98  
% 3.85/0.98  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 3.85/0.98  
% 3.85/0.98  ------ Proving...
% 3.85/0.98  
% 3.85/0.98  
% 3.85/0.98  ------ Preprocessing... sf_s  rm: 0 0s  sf_e 
% 3.85/0.98  
% 3.85/0.98  ------ Proving...
% 3.85/0.98  
% 3.85/0.98  
% 3.85/0.98  % SZS status Theorem for theBenchmark.p
% 3.85/0.98  
% 3.85/0.98  % SZS output start CNFRefutation for theBenchmark.p
% 3.85/0.98  
% 3.85/0.98  fof(f3,axiom,(
% 3.85/0.98    ! [X0,X1] : r1_tarski(k3_xboole_0(X0,X1),X0)),
% 3.85/0.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.85/0.98  
% 3.85/0.98  fof(f27,plain,(
% 3.85/0.98    ( ! [X0,X1] : (r1_tarski(k3_xboole_0(X0,X1),X0)) )),
% 3.85/0.98    inference(cnf_transformation,[],[f3])).
% 3.85/0.98  
% 3.85/0.98  fof(f9,axiom,(
% 3.85/0.98    ! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1))),
% 3.85/0.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.85/0.98  
% 3.85/0.98  fof(f33,plain,(
% 3.85/0.98    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1))) )),
% 3.85/0.98    inference(cnf_transformation,[],[f9])).
% 3.85/0.98  
% 3.85/0.98  fof(f6,axiom,(
% 3.85/0.98    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1)),
% 3.85/0.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.85/0.98  
% 3.85/0.98  fof(f30,plain,(
% 3.85/0.98    ( ! [X0,X1] : (k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1)) )),
% 3.85/0.98    inference(cnf_transformation,[],[f6])).
% 3.85/0.98  
% 3.85/0.98  fof(f7,axiom,(
% 3.85/0.98    ! [X0,X1,X2] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2)),
% 3.85/0.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.85/0.98  
% 3.85/0.98  fof(f31,plain,(
% 3.85/0.98    ( ! [X2,X0,X1] : (k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2)) )),
% 3.85/0.98    inference(cnf_transformation,[],[f7])).
% 3.85/0.98  
% 3.85/0.98  fof(f41,plain,(
% 3.85/0.98    ( ! [X0,X1] : (k2_tarski(X0,X1) = k2_enumset1(X0,X0,X0,X1)) )),
% 3.85/0.98    inference(definition_unfolding,[],[f30,f31])).
% 3.85/0.98  
% 3.85/0.98  fof(f42,plain,(
% 3.85/0.98    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k1_setfam_1(k2_enumset1(X0,X0,X0,X1))) )),
% 3.85/0.98    inference(definition_unfolding,[],[f33,f41])).
% 3.85/0.98  
% 3.85/0.98  fof(f46,plain,(
% 3.85/0.98    ( ! [X0,X1] : (r1_tarski(k1_setfam_1(k2_enumset1(X0,X0,X0,X1)),X0)) )),
% 3.85/0.98    inference(definition_unfolding,[],[f27,f42])).
% 3.85/0.98  
% 3.85/0.98  fof(f2,axiom,(
% 3.85/0.98    ! [X0,X1] : (r1_tarski(X0,X1) => k2_xboole_0(X0,X1) = X1)),
% 3.85/0.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.85/0.98  
% 3.85/0.98  fof(f15,plain,(
% 3.85/0.98    ! [X0,X1] : (k2_xboole_0(X0,X1) = X1 | ~r1_tarski(X0,X1))),
% 3.85/0.98    inference(ennf_transformation,[],[f2])).
% 3.85/0.98  
% 3.85/0.98  fof(f26,plain,(
% 3.85/0.98    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = X1 | ~r1_tarski(X0,X1)) )),
% 3.85/0.98    inference(cnf_transformation,[],[f15])).
% 3.85/0.98  
% 3.85/0.98  fof(f8,axiom,(
% 3.85/0.98    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1))),
% 3.85/0.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.85/0.98  
% 3.85/0.98  fof(f32,plain,(
% 3.85/0.98    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1))) )),
% 3.85/0.98    inference(cnf_transformation,[],[f8])).
% 3.85/0.98  
% 3.85/0.98  fof(f43,plain,(
% 3.85/0.98    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k3_tarski(k2_enumset1(X0,X0,X0,X1))) )),
% 3.85/0.98    inference(definition_unfolding,[],[f32,f41])).
% 3.85/0.98  
% 3.85/0.98  fof(f45,plain,(
% 3.85/0.98    ( ! [X0,X1] : (k3_tarski(k2_enumset1(X0,X0,X0,X1)) = X1 | ~r1_tarski(X0,X1)) )),
% 3.85/0.98    inference(definition_unfolding,[],[f26,f43])).
% 3.85/0.98  
% 3.85/0.98  fof(f1,axiom,(
% 3.85/0.98    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0)),
% 3.85/0.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.85/0.98  
% 3.85/0.98  fof(f25,plain,(
% 3.85/0.98    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0)) )),
% 3.85/0.98    inference(cnf_transformation,[],[f1])).
% 3.85/0.98  
% 3.85/0.98  fof(f44,plain,(
% 3.85/0.98    ( ! [X0,X1] : (k1_setfam_1(k2_enumset1(X0,X0,X0,X1)) = k1_setfam_1(k2_enumset1(X1,X1,X1,X0))) )),
% 3.85/0.98    inference(definition_unfolding,[],[f25,f42,f42])).
% 3.85/0.98  
% 3.85/0.98  fof(f13,conjecture,(
% 3.85/0.98    ! [X0] : (v1_relat_1(X0) => ! [X1] : (v1_relat_1(X1) => r1_tarski(k1_relat_1(k3_xboole_0(X0,X1)),k3_xboole_0(k1_relat_1(X0),k1_relat_1(X1)))))),
% 3.85/0.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.85/0.98  
% 3.85/0.98  fof(f14,negated_conjecture,(
% 3.85/0.98    ~! [X0] : (v1_relat_1(X0) => ! [X1] : (v1_relat_1(X1) => r1_tarski(k1_relat_1(k3_xboole_0(X0,X1)),k3_xboole_0(k1_relat_1(X0),k1_relat_1(X1)))))),
% 3.85/0.98    inference(negated_conjecture,[],[f13])).
% 3.85/0.98  
% 3.85/0.98  fof(f20,plain,(
% 3.85/0.98    ? [X0] : (? [X1] : (~r1_tarski(k1_relat_1(k3_xboole_0(X0,X1)),k3_xboole_0(k1_relat_1(X0),k1_relat_1(X1))) & v1_relat_1(X1)) & v1_relat_1(X0))),
% 3.85/0.98    inference(ennf_transformation,[],[f14])).
% 3.85/0.98  
% 3.85/0.98  fof(f23,plain,(
% 3.85/0.98    ( ! [X0] : (? [X1] : (~r1_tarski(k1_relat_1(k3_xboole_0(X0,X1)),k3_xboole_0(k1_relat_1(X0),k1_relat_1(X1))) & v1_relat_1(X1)) => (~r1_tarski(k1_relat_1(k3_xboole_0(X0,sK1)),k3_xboole_0(k1_relat_1(X0),k1_relat_1(sK1))) & v1_relat_1(sK1))) )),
% 3.85/0.98    introduced(choice_axiom,[])).
% 3.85/0.98  
% 3.85/0.98  fof(f22,plain,(
% 3.85/0.98    ? [X0] : (? [X1] : (~r1_tarski(k1_relat_1(k3_xboole_0(X0,X1)),k3_xboole_0(k1_relat_1(X0),k1_relat_1(X1))) & v1_relat_1(X1)) & v1_relat_1(X0)) => (? [X1] : (~r1_tarski(k1_relat_1(k3_xboole_0(sK0,X1)),k3_xboole_0(k1_relat_1(sK0),k1_relat_1(X1))) & v1_relat_1(X1)) & v1_relat_1(sK0))),
% 3.85/0.98    introduced(choice_axiom,[])).
% 3.85/0.98  
% 3.85/0.98  fof(f24,plain,(
% 3.85/0.98    (~r1_tarski(k1_relat_1(k3_xboole_0(sK0,sK1)),k3_xboole_0(k1_relat_1(sK0),k1_relat_1(sK1))) & v1_relat_1(sK1)) & v1_relat_1(sK0)),
% 3.85/0.98    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f20,f23,f22])).
% 3.85/0.98  
% 3.85/0.98  fof(f38,plain,(
% 3.85/0.98    v1_relat_1(sK0)),
% 3.85/0.98    inference(cnf_transformation,[],[f24])).
% 3.85/0.98  
% 3.85/0.98  fof(f39,plain,(
% 3.85/0.98    v1_relat_1(sK1)),
% 3.85/0.98    inference(cnf_transformation,[],[f24])).
% 3.85/0.98  
% 3.85/0.98  fof(f11,axiom,(
% 3.85/0.98    ! [X0] : (v1_relat_1(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => v1_relat_1(X1)))),
% 3.85/0.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.85/0.98  
% 3.85/0.98  fof(f18,plain,(
% 3.85/0.98    ! [X0] : (! [X1] : (v1_relat_1(X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) | ~v1_relat_1(X0))),
% 3.85/0.98    inference(ennf_transformation,[],[f11])).
% 3.85/0.98  
% 3.85/0.98  fof(f36,plain,(
% 3.85/0.98    ( ! [X0,X1] : (v1_relat_1(X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0)) | ~v1_relat_1(X0)) )),
% 3.85/0.98    inference(cnf_transformation,[],[f18])).
% 3.85/0.98  
% 3.85/0.98  fof(f10,axiom,(
% 3.85/0.98    ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) <=> r1_tarski(X0,X1))),
% 3.85/0.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.85/0.98  
% 3.85/0.98  fof(f21,plain,(
% 3.85/0.98    ! [X0,X1] : ((m1_subset_1(X0,k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1)) & (r1_tarski(X0,X1) | ~m1_subset_1(X0,k1_zfmisc_1(X1))))),
% 3.85/0.98    inference(nnf_transformation,[],[f10])).
% 3.85/0.98  
% 3.85/0.98  fof(f35,plain,(
% 3.85/0.98    ( ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1)) )),
% 3.85/0.98    inference(cnf_transformation,[],[f21])).
% 3.85/0.98  
% 3.85/0.98  fof(f12,axiom,(
% 3.85/0.98    ! [X0] : (v1_relat_1(X0) => ! [X1] : (v1_relat_1(X1) => k2_xboole_0(k1_relat_1(X0),k1_relat_1(X1)) = k1_relat_1(k2_xboole_0(X0,X1))))),
% 3.85/0.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.85/0.98  
% 3.85/0.98  fof(f19,plain,(
% 3.85/0.98    ! [X0] : (! [X1] : (k2_xboole_0(k1_relat_1(X0),k1_relat_1(X1)) = k1_relat_1(k2_xboole_0(X0,X1)) | ~v1_relat_1(X1)) | ~v1_relat_1(X0))),
% 3.85/0.98    inference(ennf_transformation,[],[f12])).
% 3.85/0.98  
% 3.85/0.98  fof(f37,plain,(
% 3.85/0.98    ( ! [X0,X1] : (k2_xboole_0(k1_relat_1(X0),k1_relat_1(X1)) = k1_relat_1(k2_xboole_0(X0,X1)) | ~v1_relat_1(X1) | ~v1_relat_1(X0)) )),
% 3.85/0.98    inference(cnf_transformation,[],[f19])).
% 3.85/0.98  
% 3.85/0.98  fof(f49,plain,(
% 3.85/0.98    ( ! [X0,X1] : (k3_tarski(k2_enumset1(k1_relat_1(X0),k1_relat_1(X0),k1_relat_1(X0),k1_relat_1(X1))) = k1_relat_1(k3_tarski(k2_enumset1(X0,X0,X0,X1))) | ~v1_relat_1(X1) | ~v1_relat_1(X0)) )),
% 3.85/0.98    inference(definition_unfolding,[],[f37,f43,f43])).
% 3.85/0.98  
% 3.85/0.98  fof(f5,axiom,(
% 3.85/0.98    ! [X0,X1] : r1_tarski(X0,k2_xboole_0(X0,X1))),
% 3.85/0.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.85/0.98  
% 3.85/0.98  fof(f29,plain,(
% 3.85/0.98    ( ! [X0,X1] : (r1_tarski(X0,k2_xboole_0(X0,X1))) )),
% 3.85/0.98    inference(cnf_transformation,[],[f5])).
% 3.85/0.98  
% 3.85/0.98  fof(f48,plain,(
% 3.85/0.98    ( ! [X0,X1] : (r1_tarski(X0,k3_tarski(k2_enumset1(X0,X0,X0,X1)))) )),
% 3.85/0.98    inference(definition_unfolding,[],[f29,f43])).
% 3.85/0.98  
% 3.85/0.98  fof(f4,axiom,(
% 3.85/0.98    ! [X0,X1,X2] : ((r1_tarski(X0,X2) & r1_tarski(X0,X1)) => r1_tarski(X0,k3_xboole_0(X1,X2)))),
% 3.85/0.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.85/0.98  
% 3.85/0.98  fof(f16,plain,(
% 3.85/0.98    ! [X0,X1,X2] : (r1_tarski(X0,k3_xboole_0(X1,X2)) | (~r1_tarski(X0,X2) | ~r1_tarski(X0,X1)))),
% 3.85/0.98    inference(ennf_transformation,[],[f4])).
% 3.85/0.98  
% 3.85/0.98  fof(f17,plain,(
% 3.85/0.98    ! [X0,X1,X2] : (r1_tarski(X0,k3_xboole_0(X1,X2)) | ~r1_tarski(X0,X2) | ~r1_tarski(X0,X1))),
% 3.85/0.98    inference(flattening,[],[f16])).
% 3.85/0.98  
% 3.85/0.98  fof(f28,plain,(
% 3.85/0.98    ( ! [X2,X0,X1] : (r1_tarski(X0,k3_xboole_0(X1,X2)) | ~r1_tarski(X0,X2) | ~r1_tarski(X0,X1)) )),
% 3.85/0.98    inference(cnf_transformation,[],[f17])).
% 3.85/0.98  
% 3.85/0.98  fof(f47,plain,(
% 3.85/0.98    ( ! [X2,X0,X1] : (r1_tarski(X0,k1_setfam_1(k2_enumset1(X1,X1,X1,X2))) | ~r1_tarski(X0,X2) | ~r1_tarski(X0,X1)) )),
% 3.85/0.98    inference(definition_unfolding,[],[f28,f42])).
% 3.85/0.98  
% 3.85/0.98  fof(f40,plain,(
% 3.85/0.98    ~r1_tarski(k1_relat_1(k3_xboole_0(sK0,sK1)),k3_xboole_0(k1_relat_1(sK0),k1_relat_1(sK1)))),
% 3.85/0.98    inference(cnf_transformation,[],[f24])).
% 3.85/0.98  
% 3.85/0.98  fof(f50,plain,(
% 3.85/0.98    ~r1_tarski(k1_relat_1(k1_setfam_1(k2_enumset1(sK0,sK0,sK0,sK1))),k1_setfam_1(k2_enumset1(k1_relat_1(sK0),k1_relat_1(sK0),k1_relat_1(sK0),k1_relat_1(sK1))))),
% 3.85/0.98    inference(definition_unfolding,[],[f40,f42,f42])).
% 3.85/0.98  
% 3.85/0.98  cnf(c_2,plain,
% 3.85/0.98      ( r1_tarski(k1_setfam_1(k2_enumset1(X0,X0,X0,X1)),X0) ),
% 3.85/0.98      inference(cnf_transformation,[],[f46]) ).
% 3.85/0.98  
% 3.85/0.98  cnf(c_7082,plain,
% 3.85/0.98      ( r1_tarski(k1_setfam_1(k2_enumset1(X0,X0,X0,X1)),X0) = iProver_top ),
% 3.85/0.98      inference(predicate_to_equality,[status(thm)],[c_2]) ).
% 3.85/0.98  
% 3.85/0.98  cnf(c_1,plain,
% 3.85/0.98      ( ~ r1_tarski(X0,X1) | k3_tarski(k2_enumset1(X0,X0,X0,X1)) = X1 ),
% 3.85/0.98      inference(cnf_transformation,[],[f45]) ).
% 3.85/0.98  
% 3.85/0.98  cnf(c_7083,plain,
% 3.85/0.98      ( k3_tarski(k2_enumset1(X0,X0,X0,X1)) = X1
% 3.85/0.98      | r1_tarski(X0,X1) != iProver_top ),
% 3.85/0.98      inference(predicate_to_equality,[status(thm)],[c_1]) ).
% 3.85/0.98  
% 3.85/0.98  cnf(c_7193,plain,
% 3.85/0.98      ( k3_tarski(k2_enumset1(k1_setfam_1(k2_enumset1(X0,X0,X0,X1)),k1_setfam_1(k2_enumset1(X0,X0,X0,X1)),k1_setfam_1(k2_enumset1(X0,X0,X0,X1)),X0)) = X0 ),
% 3.85/0.98      inference(superposition,[status(thm)],[c_7082,c_7083]) ).
% 3.85/0.98  
% 3.85/0.98  cnf(c_0,plain,
% 3.85/0.98      ( k1_setfam_1(k2_enumset1(X0,X0,X0,X1)) = k1_setfam_1(k2_enumset1(X1,X1,X1,X0)) ),
% 3.85/0.98      inference(cnf_transformation,[],[f44]) ).
% 3.85/0.98  
% 3.85/0.98  cnf(c_11,negated_conjecture,
% 3.85/0.98      ( v1_relat_1(sK0) ),
% 3.85/0.98      inference(cnf_transformation,[],[f38]) ).
% 3.85/0.98  
% 3.85/0.98  cnf(c_7076,plain,
% 3.85/0.98      ( v1_relat_1(sK0) = iProver_top ),
% 3.85/0.98      inference(predicate_to_equality,[status(thm)],[c_11]) ).
% 3.85/0.98  
% 3.85/0.98  cnf(c_10,negated_conjecture,
% 3.85/0.98      ( v1_relat_1(sK1) ),
% 3.85/0.98      inference(cnf_transformation,[],[f39]) ).
% 3.85/0.98  
% 3.85/0.98  cnf(c_7077,plain,
% 3.85/0.98      ( v1_relat_1(sK1) = iProver_top ),
% 3.85/0.98      inference(predicate_to_equality,[status(thm)],[c_10]) ).
% 3.85/0.98  
% 3.85/0.98  cnf(c_7,plain,
% 3.85/0.98      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
% 3.85/0.98      | ~ v1_relat_1(X1)
% 3.85/0.98      | v1_relat_1(X0) ),
% 3.85/0.98      inference(cnf_transformation,[],[f36]) ).
% 3.85/0.98  
% 3.85/0.98  cnf(c_5,plain,
% 3.85/0.98      ( m1_subset_1(X0,k1_zfmisc_1(X1)) | ~ r1_tarski(X0,X1) ),
% 3.85/0.98      inference(cnf_transformation,[],[f35]) ).
% 3.85/0.98  
% 3.85/0.98  cnf(c_87,plain,
% 3.85/0.98      ( ~ r1_tarski(X0,X1) | m1_subset_1(X0,k1_zfmisc_1(X1)) ),
% 3.85/0.98      inference(prop_impl,[status(thm)],[c_5]) ).
% 3.85/0.98  
% 3.85/0.98  cnf(c_88,plain,
% 3.85/0.98      ( m1_subset_1(X0,k1_zfmisc_1(X1)) | ~ r1_tarski(X0,X1) ),
% 3.85/0.98      inference(renaming,[status(thm)],[c_87]) ).
% 3.85/0.98  
% 3.85/0.98  cnf(c_108,plain,
% 3.85/0.98      ( ~ r1_tarski(X0,X1) | ~ v1_relat_1(X1) | v1_relat_1(X0) ),
% 3.85/0.98      inference(bin_hyper_res,[status(thm)],[c_7,c_88]) ).
% 3.85/0.98  
% 3.85/0.98  cnf(c_7075,plain,
% 3.85/0.98      ( r1_tarski(X0,X1) != iProver_top
% 3.85/0.98      | v1_relat_1(X1) != iProver_top
% 3.85/0.98      | v1_relat_1(X0) = iProver_top ),
% 3.85/0.98      inference(predicate_to_equality,[status(thm)],[c_108]) ).
% 3.85/0.98  
% 3.85/0.98  cnf(c_7223,plain,
% 3.85/0.98      ( v1_relat_1(X0) != iProver_top
% 3.85/0.98      | v1_relat_1(k1_setfam_1(k2_enumset1(X0,X0,X0,X1))) = iProver_top ),
% 3.85/0.98      inference(superposition,[status(thm)],[c_7082,c_7075]) ).
% 3.85/0.98  
% 3.85/0.98  cnf(c_8,plain,
% 3.85/0.98      ( ~ v1_relat_1(X0)
% 3.85/0.98      | ~ v1_relat_1(X1)
% 3.85/0.98      | k3_tarski(k2_enumset1(k1_relat_1(X0),k1_relat_1(X0),k1_relat_1(X0),k1_relat_1(X1))) = k1_relat_1(k3_tarski(k2_enumset1(X0,X0,X0,X1))) ),
% 3.85/0.98      inference(cnf_transformation,[],[f49]) ).
% 3.85/0.98  
% 3.85/0.98  cnf(c_7079,plain,
% 3.85/0.98      ( k3_tarski(k2_enumset1(k1_relat_1(X0),k1_relat_1(X0),k1_relat_1(X0),k1_relat_1(X1))) = k1_relat_1(k3_tarski(k2_enumset1(X0,X0,X0,X1)))
% 3.85/0.98      | v1_relat_1(X0) != iProver_top
% 3.85/0.98      | v1_relat_1(X1) != iProver_top ),
% 3.85/0.98      inference(predicate_to_equality,[status(thm)],[c_8]) ).
% 3.85/0.98  
% 3.85/0.98  cnf(c_7332,plain,
% 3.85/0.98      ( k3_tarski(k2_enumset1(k1_relat_1(k1_setfam_1(k2_enumset1(X0,X0,X0,X1))),k1_relat_1(k1_setfam_1(k2_enumset1(X0,X0,X0,X1))),k1_relat_1(k1_setfam_1(k2_enumset1(X0,X0,X0,X1))),k1_relat_1(X2))) = k1_relat_1(k3_tarski(k2_enumset1(k1_setfam_1(k2_enumset1(X0,X0,X0,X1)),k1_setfam_1(k2_enumset1(X0,X0,X0,X1)),k1_setfam_1(k2_enumset1(X0,X0,X0,X1)),X2)))
% 3.85/0.98      | v1_relat_1(X0) != iProver_top
% 3.85/0.98      | v1_relat_1(X2) != iProver_top ),
% 3.85/0.98      inference(superposition,[status(thm)],[c_7223,c_7079]) ).
% 3.85/0.98  
% 3.85/0.98  cnf(c_9091,plain,
% 3.85/0.98      ( k3_tarski(k2_enumset1(k1_relat_1(k1_setfam_1(k2_enumset1(sK1,sK1,sK1,X0))),k1_relat_1(k1_setfam_1(k2_enumset1(sK1,sK1,sK1,X0))),k1_relat_1(k1_setfam_1(k2_enumset1(sK1,sK1,sK1,X0))),k1_relat_1(X1))) = k1_relat_1(k3_tarski(k2_enumset1(k1_setfam_1(k2_enumset1(sK1,sK1,sK1,X0)),k1_setfam_1(k2_enumset1(sK1,sK1,sK1,X0)),k1_setfam_1(k2_enumset1(sK1,sK1,sK1,X0)),X1)))
% 3.85/0.98      | v1_relat_1(X1) != iProver_top ),
% 3.85/0.98      inference(superposition,[status(thm)],[c_7077,c_7332]) ).
% 3.85/0.98  
% 3.85/0.98  cnf(c_9235,plain,
% 3.85/0.98      ( k3_tarski(k2_enumset1(k1_relat_1(k1_setfam_1(k2_enumset1(sK1,sK1,sK1,X0))),k1_relat_1(k1_setfam_1(k2_enumset1(sK1,sK1,sK1,X0))),k1_relat_1(k1_setfam_1(k2_enumset1(sK1,sK1,sK1,X0))),k1_relat_1(sK0))) = k1_relat_1(k3_tarski(k2_enumset1(k1_setfam_1(k2_enumset1(sK1,sK1,sK1,X0)),k1_setfam_1(k2_enumset1(sK1,sK1,sK1,X0)),k1_setfam_1(k2_enumset1(sK1,sK1,sK1,X0)),sK0))) ),
% 3.85/0.98      inference(superposition,[status(thm)],[c_7076,c_9091]) ).
% 3.85/0.98  
% 3.85/0.98  cnf(c_4,plain,
% 3.85/0.98      ( r1_tarski(X0,k3_tarski(k2_enumset1(X0,X0,X0,X1))) ),
% 3.85/0.98      inference(cnf_transformation,[],[f48]) ).
% 3.85/0.98  
% 3.85/0.98  cnf(c_7080,plain,
% 3.85/0.98      ( r1_tarski(X0,k3_tarski(k2_enumset1(X0,X0,X0,X1))) = iProver_top ),
% 3.85/0.98      inference(predicate_to_equality,[status(thm)],[c_4]) ).
% 3.85/0.98  
% 3.85/0.98  cnf(c_9281,plain,
% 3.85/0.98      ( r1_tarski(k1_relat_1(k1_setfam_1(k2_enumset1(sK1,sK1,sK1,X0))),k1_relat_1(k3_tarski(k2_enumset1(k1_setfam_1(k2_enumset1(sK1,sK1,sK1,X0)),k1_setfam_1(k2_enumset1(sK1,sK1,sK1,X0)),k1_setfam_1(k2_enumset1(sK1,sK1,sK1,X0)),sK0)))) = iProver_top ),
% 3.85/0.98      inference(superposition,[status(thm)],[c_9235,c_7080]) ).
% 3.85/0.98  
% 3.85/0.98  cnf(c_9456,plain,
% 3.85/0.98      ( r1_tarski(k1_relat_1(k1_setfam_1(k2_enumset1(X0,X0,X0,sK1))),k1_relat_1(k3_tarski(k2_enumset1(k1_setfam_1(k2_enumset1(X0,X0,X0,sK1)),k1_setfam_1(k2_enumset1(X0,X0,X0,sK1)),k1_setfam_1(k2_enumset1(X0,X0,X0,sK1)),sK0)))) = iProver_top ),
% 3.85/0.98      inference(superposition,[status(thm)],[c_0,c_9281]) ).
% 3.85/0.98  
% 3.85/0.98  cnf(c_9632,plain,
% 3.85/0.98      ( r1_tarski(k1_relat_1(k1_setfam_1(k2_enumset1(sK0,sK0,sK0,sK1))),k1_relat_1(sK0)) = iProver_top ),
% 3.85/0.98      inference(superposition,[status(thm)],[c_7193,c_9456]) ).
% 3.85/0.98  
% 3.85/0.98  cnf(c_7168,plain,
% 3.85/0.98      ( r1_tarski(k1_setfam_1(k2_enumset1(X0,X0,X0,X1)),X1) = iProver_top ),
% 3.85/0.98      inference(superposition,[status(thm)],[c_0,c_7082]) ).
% 3.85/0.98  
% 3.85/0.98  cnf(c_7195,plain,
% 3.85/0.98      ( k3_tarski(k2_enumset1(k1_setfam_1(k2_enumset1(X0,X0,X0,X1)),k1_setfam_1(k2_enumset1(X0,X0,X0,X1)),k1_setfam_1(k2_enumset1(X0,X0,X0,X1)),X1)) = X1 ),
% 3.85/0.98      inference(superposition,[status(thm)],[c_7168,c_7083]) ).
% 3.85/0.98  
% 3.85/0.98  cnf(c_9092,plain,
% 3.85/0.98      ( k3_tarski(k2_enumset1(k1_relat_1(k1_setfam_1(k2_enumset1(sK0,sK0,sK0,X0))),k1_relat_1(k1_setfam_1(k2_enumset1(sK0,sK0,sK0,X0))),k1_relat_1(k1_setfam_1(k2_enumset1(sK0,sK0,sK0,X0))),k1_relat_1(X1))) = k1_relat_1(k3_tarski(k2_enumset1(k1_setfam_1(k2_enumset1(sK0,sK0,sK0,X0)),k1_setfam_1(k2_enumset1(sK0,sK0,sK0,X0)),k1_setfam_1(k2_enumset1(sK0,sK0,sK0,X0)),X1)))
% 3.85/0.98      | v1_relat_1(X1) != iProver_top ),
% 3.85/0.98      inference(superposition,[status(thm)],[c_7076,c_7332]) ).
% 3.85/0.98  
% 3.85/0.98  cnf(c_9304,plain,
% 3.85/0.98      ( k3_tarski(k2_enumset1(k1_relat_1(k1_setfam_1(k2_enumset1(sK0,sK0,sK0,X0))),k1_relat_1(k1_setfam_1(k2_enumset1(sK0,sK0,sK0,X0))),k1_relat_1(k1_setfam_1(k2_enumset1(sK0,sK0,sK0,X0))),k1_relat_1(sK1))) = k1_relat_1(k3_tarski(k2_enumset1(k1_setfam_1(k2_enumset1(sK0,sK0,sK0,X0)),k1_setfam_1(k2_enumset1(sK0,sK0,sK0,X0)),k1_setfam_1(k2_enumset1(sK0,sK0,sK0,X0)),sK1))) ),
% 3.85/0.98      inference(superposition,[status(thm)],[c_7077,c_9092]) ).
% 3.85/0.98  
% 3.85/0.98  cnf(c_9351,plain,
% 3.85/0.98      ( r1_tarski(k1_relat_1(k1_setfam_1(k2_enumset1(sK0,sK0,sK0,X0))),k1_relat_1(k3_tarski(k2_enumset1(k1_setfam_1(k2_enumset1(sK0,sK0,sK0,X0)),k1_setfam_1(k2_enumset1(sK0,sK0,sK0,X0)),k1_setfam_1(k2_enumset1(sK0,sK0,sK0,X0)),sK1)))) = iProver_top ),
% 3.85/0.98      inference(superposition,[status(thm)],[c_9304,c_7080]) ).
% 3.85/0.98  
% 3.85/0.98  cnf(c_9499,plain,
% 3.85/0.98      ( r1_tarski(k1_relat_1(k1_setfam_1(k2_enumset1(sK0,sK0,sK0,sK1))),k1_relat_1(sK1)) = iProver_top ),
% 3.85/0.98      inference(superposition,[status(thm)],[c_7195,c_9351]) ).
% 3.85/0.98  
% 3.85/0.98  cnf(c_3,plain,
% 3.85/0.98      ( ~ r1_tarski(X0,X1)
% 3.85/0.98      | ~ r1_tarski(X0,X2)
% 3.85/0.98      | r1_tarski(X0,k1_setfam_1(k2_enumset1(X1,X1,X1,X2))) ),
% 3.85/0.98      inference(cnf_transformation,[],[f47]) ).
% 3.85/0.98  
% 3.85/0.98  cnf(c_5664,plain,
% 3.85/0.98      ( r1_tarski(X0,X1) != iProver_top
% 3.85/0.98      | r1_tarski(X0,X2) != iProver_top
% 3.85/0.98      | r1_tarski(X0,k1_setfam_1(k2_enumset1(X1,X1,X1,X2))) = iProver_top ),
% 3.85/0.98      inference(predicate_to_equality,[status(thm)],[c_3]) ).
% 3.85/0.98  
% 3.85/0.98  cnf(c_9,negated_conjecture,
% 3.85/0.98      ( ~ r1_tarski(k1_relat_1(k1_setfam_1(k2_enumset1(sK0,sK0,sK0,sK1))),k1_setfam_1(k2_enumset1(k1_relat_1(sK0),k1_relat_1(sK0),k1_relat_1(sK0),k1_relat_1(sK1)))) ),
% 3.85/0.98      inference(cnf_transformation,[],[f50]) ).
% 3.85/0.98  
% 3.85/0.98  cnf(c_5662,plain,
% 3.85/0.98      ( r1_tarski(k1_relat_1(k1_setfam_1(k2_enumset1(sK0,sK0,sK0,sK1))),k1_setfam_1(k2_enumset1(k1_relat_1(sK0),k1_relat_1(sK0),k1_relat_1(sK0),k1_relat_1(sK1)))) != iProver_top ),
% 3.85/0.98      inference(predicate_to_equality,[status(thm)],[c_9]) ).
% 3.85/0.98  
% 3.85/0.98  cnf(c_5696,plain,
% 3.85/0.98      ( r1_tarski(k1_relat_1(k1_setfam_1(k2_enumset1(sK0,sK0,sK0,sK1))),k1_relat_1(sK1)) != iProver_top
% 3.85/0.98      | r1_tarski(k1_relat_1(k1_setfam_1(k2_enumset1(sK0,sK0,sK0,sK1))),k1_relat_1(sK0)) != iProver_top ),
% 3.85/0.98      inference(superposition,[status(thm)],[c_5664,c_5662]) ).
% 3.85/0.98  
% 3.85/0.98  cnf(contradiction,plain,
% 3.85/0.98      ( $false ),
% 3.85/0.98      inference(minisat,[status(thm)],[c_9632,c_9499,c_5696]) ).
% 3.85/0.98  
% 3.85/0.98  
% 3.85/0.98  % SZS output end CNFRefutation for theBenchmark.p
% 3.85/0.98  
% 3.85/0.98  ------                               Statistics
% 3.85/0.98  
% 3.85/0.98  ------ Selected
% 3.85/0.98  
% 3.85/0.98  total_time:                             0.287
% 3.85/0.98  
%------------------------------------------------------------------------------
