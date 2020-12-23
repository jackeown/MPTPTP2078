%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n010.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 11:42:53 EST 2020

% Result     : Theorem 7.87s
% Output     : CNFRefutation 7.87s
% Verified   : 
% Statistics : Number of formulae       :   86 ( 231 expanded)
%              Number of clauses        :   39 (  64 expanded)
%              Number of leaves         :   15 (  63 expanded)
%              Depth                    :   15
%              Number of atoms          :  161 ( 411 expanded)
%              Number of equality atoms :   59 ( 160 expanded)
%              Maximal formula depth    :    7 (   3 average)
%              Maximal clause size      :    6 (   2 average)
%              Maximal term depth       :    7 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f4,axiom,(
    ! [X0,X1] : r1_tarski(k4_xboole_0(X0,X1),X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f29,plain,(
    ! [X0,X1] : r1_tarski(k4_xboole_0(X0,X1),X0) ),
    inference(cnf_transformation,[],[f4])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
     => k2_xboole_0(X0,X1) = X1 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f16,plain,(
    ! [X0,X1] :
      ( k2_xboole_0(X0,X1) = X1
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f27,plain,(
    ! [X0,X1] :
      ( k2_xboole_0(X0,X1) = X1
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f16])).

fof(f9,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f34,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1)) ),
    inference(cnf_transformation,[],[f9])).

fof(f7,axiom,(
    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f32,plain,(
    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f7])).

fof(f8,axiom,(
    ! [X0,X1,X2] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f33,plain,(
    ! [X2,X0,X1] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2) ),
    inference(cnf_transformation,[],[f8])).

fof(f43,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k2_enumset1(X0,X0,X0,X1) ),
    inference(definition_unfolding,[],[f32,f33])).

fof(f44,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k2_enumset1(X0,X0,X0,X1)) ),
    inference(definition_unfolding,[],[f34,f43])).

fof(f46,plain,(
    ! [X0,X1] :
      ( k3_tarski(k2_enumset1(X0,X0,X0,X1)) = X1
      | ~ r1_tarski(X0,X1) ) ),
    inference(definition_unfolding,[],[f27,f44])).

fof(f1,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f26,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f1])).

fof(f5,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f30,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f5])).

fof(f45,plain,(
    ! [X0,X1] : k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k4_xboole_0(X1,k4_xboole_0(X1,X0)) ),
    inference(definition_unfolding,[],[f26,f30,f30])).

fof(f14,conjecture,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( v1_relat_1(X1)
         => r1_tarski(k1_relat_1(k3_xboole_0(X0,X1)),k3_xboole_0(k1_relat_1(X0),k1_relat_1(X1))) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f15,negated_conjecture,(
    ~ ! [X0] :
        ( v1_relat_1(X0)
       => ! [X1] :
            ( v1_relat_1(X1)
           => r1_tarski(k1_relat_1(k3_xboole_0(X0,X1)),k3_xboole_0(k1_relat_1(X0),k1_relat_1(X1))) ) ) ),
    inference(negated_conjecture,[],[f14])).

fof(f21,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ~ r1_tarski(k1_relat_1(k3_xboole_0(X0,X1)),k3_xboole_0(k1_relat_1(X0),k1_relat_1(X1)))
          & v1_relat_1(X1) )
      & v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f15])).

fof(f24,plain,(
    ! [X0] :
      ( ? [X1] :
          ( ~ r1_tarski(k1_relat_1(k3_xboole_0(X0,X1)),k3_xboole_0(k1_relat_1(X0),k1_relat_1(X1)))
          & v1_relat_1(X1) )
     => ( ~ r1_tarski(k1_relat_1(k3_xboole_0(X0,sK1)),k3_xboole_0(k1_relat_1(X0),k1_relat_1(sK1)))
        & v1_relat_1(sK1) ) ) ),
    introduced(choice_axiom,[])).

fof(f23,plain,
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

fof(f25,plain,
    ( ~ r1_tarski(k1_relat_1(k3_xboole_0(sK0,sK1)),k3_xboole_0(k1_relat_1(sK0),k1_relat_1(sK1)))
    & v1_relat_1(sK1)
    & v1_relat_1(sK0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f21,f24,f23])).

fof(f40,plain,(
    v1_relat_1(sK0) ),
    inference(cnf_transformation,[],[f25])).

fof(f41,plain,(
    v1_relat_1(sK1) ),
    inference(cnf_transformation,[],[f25])).

fof(f12,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(X0))
         => v1_relat_1(X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f19,plain,(
    ! [X0] :
      ( ! [X1] :
          ( v1_relat_1(X1)
          | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f38,plain,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f11,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f22,plain,(
    ! [X0,X1] :
      ( ( m1_subset_1(X0,k1_zfmisc_1(X1))
        | ~ r1_tarski(X0,X1) )
      & ( r1_tarski(X0,X1)
        | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ) ) ),
    inference(nnf_transformation,[],[f11])).

fof(f37,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f13,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( v1_relat_1(X1)
         => k2_xboole_0(k1_relat_1(X0),k1_relat_1(X1)) = k1_relat_1(k2_xboole_0(X0,X1)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f20,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k2_xboole_0(k1_relat_1(X0),k1_relat_1(X1)) = k1_relat_1(k2_xboole_0(X0,X1))
          | ~ v1_relat_1(X1) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f39,plain,(
    ! [X0,X1] :
      ( k2_xboole_0(k1_relat_1(X0),k1_relat_1(X1)) = k1_relat_1(k2_xboole_0(X0,X1))
      | ~ v1_relat_1(X1)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f50,plain,(
    ! [X0,X1] :
      ( k3_tarski(k2_enumset1(k1_relat_1(X0),k1_relat_1(X0),k1_relat_1(X0),k1_relat_1(X1))) = k1_relat_1(k3_tarski(k2_enumset1(X0,X0,X0,X1)))
      | ~ v1_relat_1(X1)
      | ~ v1_relat_1(X0) ) ),
    inference(definition_unfolding,[],[f39,f44,f44])).

fof(f6,axiom,(
    ! [X0,X1] : r1_tarski(X0,k2_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f31,plain,(
    ! [X0,X1] : r1_tarski(X0,k2_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f6])).

fof(f48,plain,(
    ! [X0,X1] : r1_tarski(X0,k3_tarski(k2_enumset1(X0,X0,X0,X1))) ),
    inference(definition_unfolding,[],[f31,f44])).

fof(f3,axiom,(
    ! [X0,X1,X2] :
      ( ( r1_tarski(X0,X2)
        & r1_tarski(X0,X1) )
     => r1_tarski(X0,k3_xboole_0(X1,X2)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f17,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,k3_xboole_0(X1,X2))
      | ~ r1_tarski(X0,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f18,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,k3_xboole_0(X1,X2))
      | ~ r1_tarski(X0,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(flattening,[],[f17])).

fof(f28,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(X0,k3_xboole_0(X1,X2))
      | ~ r1_tarski(X0,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f47,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(X0,k4_xboole_0(X1,k4_xboole_0(X1,X2)))
      | ~ r1_tarski(X0,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(definition_unfolding,[],[f28,f30])).

fof(f42,plain,(
    ~ r1_tarski(k1_relat_1(k3_xboole_0(sK0,sK1)),k3_xboole_0(k1_relat_1(sK0),k1_relat_1(sK1))) ),
    inference(cnf_transformation,[],[f25])).

fof(f51,plain,(
    ~ r1_tarski(k1_relat_1(k4_xboole_0(sK0,k4_xboole_0(sK0,sK1))),k4_xboole_0(k1_relat_1(sK0),k4_xboole_0(k1_relat_1(sK0),k1_relat_1(sK1)))) ),
    inference(definition_unfolding,[],[f42,f30,f30])).

cnf(c_3,plain,
    ( r1_tarski(k4_xboole_0(X0,X1),X0) ),
    inference(cnf_transformation,[],[f29])).

cnf(c_393,plain,
    ( r1_tarski(k4_xboole_0(X0,X1),X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3])).

cnf(c_1,plain,
    ( ~ r1_tarski(X0,X1)
    | k3_tarski(k2_enumset1(X0,X0,X0,X1)) = X1 ),
    inference(cnf_transformation,[],[f46])).

cnf(c_395,plain,
    ( k3_tarski(k2_enumset1(X0,X0,X0,X1)) = X1
    | r1_tarski(X0,X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1])).

cnf(c_789,plain,
    ( k3_tarski(k2_enumset1(k4_xboole_0(X0,X1),k4_xboole_0(X0,X1),k4_xboole_0(X0,X1),X0)) = X0 ),
    inference(superposition,[status(thm)],[c_393,c_395])).

cnf(c_0,plain,
    ( k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k4_xboole_0(X1,k4_xboole_0(X1,X0)) ),
    inference(cnf_transformation,[],[f45])).

cnf(c_12,negated_conjecture,
    ( v1_relat_1(sK0) ),
    inference(cnf_transformation,[],[f40])).

cnf(c_388,plain,
    ( v1_relat_1(sK0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_12])).

cnf(c_11,negated_conjecture,
    ( v1_relat_1(sK1) ),
    inference(cnf_transformation,[],[f41])).

cnf(c_389,plain,
    ( v1_relat_1(sK1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_11])).

cnf(c_8,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | ~ v1_relat_1(X1)
    | v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f38])).

cnf(c_6,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(X1))
    | ~ r1_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f37])).

cnf(c_89,plain,
    ( ~ r1_tarski(X0,X1)
    | m1_subset_1(X0,k1_zfmisc_1(X1)) ),
    inference(prop_impl,[status(thm)],[c_6])).

cnf(c_90,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(X1))
    | ~ r1_tarski(X0,X1) ),
    inference(renaming,[status(thm)],[c_89])).

cnf(c_111,plain,
    ( ~ r1_tarski(X0,X1)
    | ~ v1_relat_1(X1)
    | v1_relat_1(X0) ),
    inference(bin_hyper_res,[status(thm)],[c_8,c_90])).

cnf(c_387,plain,
    ( r1_tarski(X0,X1) != iProver_top
    | v1_relat_1(X1) != iProver_top
    | v1_relat_1(X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_111])).

cnf(c_701,plain,
    ( v1_relat_1(X0) != iProver_top
    | v1_relat_1(k4_xboole_0(X0,X1)) = iProver_top ),
    inference(superposition,[status(thm)],[c_393,c_387])).

cnf(c_9,plain,
    ( ~ v1_relat_1(X0)
    | ~ v1_relat_1(X1)
    | k3_tarski(k2_enumset1(k1_relat_1(X0),k1_relat_1(X0),k1_relat_1(X0),k1_relat_1(X1))) = k1_relat_1(k3_tarski(k2_enumset1(X0,X0,X0,X1))) ),
    inference(cnf_transformation,[],[f50])).

cnf(c_391,plain,
    ( k3_tarski(k2_enumset1(k1_relat_1(X0),k1_relat_1(X0),k1_relat_1(X0),k1_relat_1(X1))) = k1_relat_1(k3_tarski(k2_enumset1(X0,X0,X0,X1)))
    | v1_relat_1(X0) != iProver_top
    | v1_relat_1(X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_9])).

cnf(c_1197,plain,
    ( k3_tarski(k2_enumset1(k1_relat_1(k4_xboole_0(X0,X1)),k1_relat_1(k4_xboole_0(X0,X1)),k1_relat_1(k4_xboole_0(X0,X1)),k1_relat_1(X2))) = k1_relat_1(k3_tarski(k2_enumset1(k4_xboole_0(X0,X1),k4_xboole_0(X0,X1),k4_xboole_0(X0,X1),X2)))
    | v1_relat_1(X0) != iProver_top
    | v1_relat_1(X2) != iProver_top ),
    inference(superposition,[status(thm)],[c_701,c_391])).

cnf(c_10277,plain,
    ( k3_tarski(k2_enumset1(k1_relat_1(k4_xboole_0(sK1,X0)),k1_relat_1(k4_xboole_0(sK1,X0)),k1_relat_1(k4_xboole_0(sK1,X0)),k1_relat_1(X1))) = k1_relat_1(k3_tarski(k2_enumset1(k4_xboole_0(sK1,X0),k4_xboole_0(sK1,X0),k4_xboole_0(sK1,X0),X1)))
    | v1_relat_1(X1) != iProver_top ),
    inference(superposition,[status(thm)],[c_389,c_1197])).

cnf(c_11253,plain,
    ( k3_tarski(k2_enumset1(k1_relat_1(k4_xboole_0(sK1,X0)),k1_relat_1(k4_xboole_0(sK1,X0)),k1_relat_1(k4_xboole_0(sK1,X0)),k1_relat_1(sK0))) = k1_relat_1(k3_tarski(k2_enumset1(k4_xboole_0(sK1,X0),k4_xboole_0(sK1,X0),k4_xboole_0(sK1,X0),sK0))) ),
    inference(superposition,[status(thm)],[c_388,c_10277])).

cnf(c_4,plain,
    ( r1_tarski(X0,k3_tarski(k2_enumset1(X0,X0,X0,X1))) ),
    inference(cnf_transformation,[],[f48])).

cnf(c_392,plain,
    ( r1_tarski(X0,k3_tarski(k2_enumset1(X0,X0,X0,X1))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_4])).

cnf(c_11295,plain,
    ( r1_tarski(k1_relat_1(k4_xboole_0(sK1,X0)),k1_relat_1(k3_tarski(k2_enumset1(k4_xboole_0(sK1,X0),k4_xboole_0(sK1,X0),k4_xboole_0(sK1,X0),sK0)))) = iProver_top ),
    inference(superposition,[status(thm)],[c_11253,c_392])).

cnf(c_12087,plain,
    ( r1_tarski(k1_relat_1(k4_xboole_0(X0,k4_xboole_0(X0,sK1))),k1_relat_1(k3_tarski(k2_enumset1(k4_xboole_0(X0,k4_xboole_0(X0,sK1)),k4_xboole_0(X0,k4_xboole_0(X0,sK1)),k4_xboole_0(X0,k4_xboole_0(X0,sK1)),sK0)))) = iProver_top ),
    inference(superposition,[status(thm)],[c_0,c_11295])).

cnf(c_13031,plain,
    ( r1_tarski(k1_relat_1(k4_xboole_0(sK0,k4_xboole_0(sK0,sK1))),k1_relat_1(sK0)) = iProver_top ),
    inference(superposition,[status(thm)],[c_789,c_12087])).

cnf(c_573,plain,
    ( r1_tarski(k4_xboole_0(X0,k4_xboole_0(X0,X1)),X1) = iProver_top ),
    inference(superposition,[status(thm)],[c_0,c_393])).

cnf(c_791,plain,
    ( k3_tarski(k2_enumset1(k4_xboole_0(X0,k4_xboole_0(X0,X1)),k4_xboole_0(X0,k4_xboole_0(X0,X1)),k4_xboole_0(X0,k4_xboole_0(X0,X1)),X1)) = X1 ),
    inference(superposition,[status(thm)],[c_573,c_395])).

cnf(c_10278,plain,
    ( k3_tarski(k2_enumset1(k1_relat_1(k4_xboole_0(sK0,X0)),k1_relat_1(k4_xboole_0(sK0,X0)),k1_relat_1(k4_xboole_0(sK0,X0)),k1_relat_1(X1))) = k1_relat_1(k3_tarski(k2_enumset1(k4_xboole_0(sK0,X0),k4_xboole_0(sK0,X0),k4_xboole_0(sK0,X0),X1)))
    | v1_relat_1(X1) != iProver_top ),
    inference(superposition,[status(thm)],[c_388,c_1197])).

cnf(c_11487,plain,
    ( k3_tarski(k2_enumset1(k1_relat_1(k4_xboole_0(sK0,X0)),k1_relat_1(k4_xboole_0(sK0,X0)),k1_relat_1(k4_xboole_0(sK0,X0)),k1_relat_1(sK1))) = k1_relat_1(k3_tarski(k2_enumset1(k4_xboole_0(sK0,X0),k4_xboole_0(sK0,X0),k4_xboole_0(sK0,X0),sK1))) ),
    inference(superposition,[status(thm)],[c_389,c_10278])).

cnf(c_11530,plain,
    ( r1_tarski(k1_relat_1(k4_xboole_0(sK0,X0)),k1_relat_1(k3_tarski(k2_enumset1(k4_xboole_0(sK0,X0),k4_xboole_0(sK0,X0),k4_xboole_0(sK0,X0),sK1)))) = iProver_top ),
    inference(superposition,[status(thm)],[c_11487,c_392])).

cnf(c_12102,plain,
    ( r1_tarski(k1_relat_1(k4_xboole_0(sK0,k4_xboole_0(sK0,sK1))),k1_relat_1(sK1)) = iProver_top ),
    inference(superposition,[status(thm)],[c_791,c_11530])).

cnf(c_2,plain,
    ( ~ r1_tarski(X0,X1)
    | ~ r1_tarski(X0,X2)
    | r1_tarski(X0,k4_xboole_0(X1,k4_xboole_0(X1,X2))) ),
    inference(cnf_transformation,[],[f47])).

cnf(c_408,plain,
    ( r1_tarski(k1_relat_1(k4_xboole_0(sK0,k4_xboole_0(sK0,sK1))),k4_xboole_0(k1_relat_1(sK0),k4_xboole_0(k1_relat_1(sK0),k1_relat_1(sK1))))
    | ~ r1_tarski(k1_relat_1(k4_xboole_0(sK0,k4_xboole_0(sK0,sK1))),k1_relat_1(sK1))
    | ~ r1_tarski(k1_relat_1(k4_xboole_0(sK0,k4_xboole_0(sK0,sK1))),k1_relat_1(sK0)) ),
    inference(instantiation,[status(thm)],[c_2])).

cnf(c_409,plain,
    ( r1_tarski(k1_relat_1(k4_xboole_0(sK0,k4_xboole_0(sK0,sK1))),k4_xboole_0(k1_relat_1(sK0),k4_xboole_0(k1_relat_1(sK0),k1_relat_1(sK1)))) = iProver_top
    | r1_tarski(k1_relat_1(k4_xboole_0(sK0,k4_xboole_0(sK0,sK1))),k1_relat_1(sK1)) != iProver_top
    | r1_tarski(k1_relat_1(k4_xboole_0(sK0,k4_xboole_0(sK0,sK1))),k1_relat_1(sK0)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_408])).

cnf(c_10,negated_conjecture,
    ( ~ r1_tarski(k1_relat_1(k4_xboole_0(sK0,k4_xboole_0(sK0,sK1))),k4_xboole_0(k1_relat_1(sK0),k4_xboole_0(k1_relat_1(sK0),k1_relat_1(sK1)))) ),
    inference(cnf_transformation,[],[f51])).

cnf(c_15,plain,
    ( r1_tarski(k1_relat_1(k4_xboole_0(sK0,k4_xboole_0(sK0,sK1))),k4_xboole_0(k1_relat_1(sK0),k4_xboole_0(k1_relat_1(sK0),k1_relat_1(sK1)))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_10])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_13031,c_12102,c_409,c_15])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.12/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : iproveropt_run.sh %d %s
% 0.12/0.33  % Computer   : n010.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % WCLimit    : 600
% 0.12/0.34  % DateTime   : Tue Dec  1 15:49:44 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.34  % Running in FOF mode
% 7.87/1.47  % SZS status Started for /export/starexec/sandbox/benchmark/theBenchmark.p
% 7.87/1.47  
% 7.87/1.47  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 7.87/1.47  
% 7.87/1.47  ------  iProver source info
% 7.87/1.47  
% 7.87/1.47  git: date: 2020-06-30 10:37:57 +0100
% 7.87/1.47  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 7.87/1.47  git: non_committed_changes: false
% 7.87/1.47  git: last_make_outside_of_git: false
% 7.87/1.47  
% 7.87/1.47  ------ 
% 7.87/1.47  
% 7.87/1.47  ------ Input Options
% 7.87/1.47  
% 7.87/1.47  --out_options                           all
% 7.87/1.47  --tptp_safe_out                         true
% 7.87/1.47  --problem_path                          ""
% 7.87/1.47  --include_path                          ""
% 7.87/1.47  --clausifier                            res/vclausify_rel
% 7.87/1.47  --clausifier_options                    ""
% 7.87/1.47  --stdin                                 false
% 7.87/1.47  --stats_out                             all
% 7.87/1.47  
% 7.87/1.47  ------ General Options
% 7.87/1.47  
% 7.87/1.47  --fof                                   false
% 7.87/1.47  --time_out_real                         305.
% 7.87/1.47  --time_out_virtual                      -1.
% 7.87/1.47  --symbol_type_check                     false
% 7.87/1.47  --clausify_out                          false
% 7.87/1.47  --sig_cnt_out                           false
% 7.87/1.47  --trig_cnt_out                          false
% 7.87/1.47  --trig_cnt_out_tolerance                1.
% 7.87/1.47  --trig_cnt_out_sk_spl                   false
% 7.87/1.47  --abstr_cl_out                          false
% 7.87/1.47  
% 7.87/1.47  ------ Global Options
% 7.87/1.47  
% 7.87/1.47  --schedule                              default
% 7.87/1.47  --add_important_lit                     false
% 7.87/1.47  --prop_solver_per_cl                    1000
% 7.87/1.47  --min_unsat_core                        false
% 7.87/1.47  --soft_assumptions                      false
% 7.87/1.47  --soft_lemma_size                       3
% 7.87/1.47  --prop_impl_unit_size                   0
% 7.87/1.47  --prop_impl_unit                        []
% 7.87/1.47  --share_sel_clauses                     true
% 7.87/1.47  --reset_solvers                         false
% 7.87/1.47  --bc_imp_inh                            [conj_cone]
% 7.87/1.47  --conj_cone_tolerance                   3.
% 7.87/1.47  --extra_neg_conj                        none
% 7.87/1.47  --large_theory_mode                     true
% 7.87/1.47  --prolific_symb_bound                   200
% 7.87/1.47  --lt_threshold                          2000
% 7.87/1.47  --clause_weak_htbl                      true
% 7.87/1.47  --gc_record_bc_elim                     false
% 7.87/1.47  
% 7.87/1.47  ------ Preprocessing Options
% 7.87/1.47  
% 7.87/1.47  --preprocessing_flag                    true
% 7.87/1.47  --time_out_prep_mult                    0.1
% 7.87/1.47  --splitting_mode                        input
% 7.87/1.47  --splitting_grd                         true
% 7.87/1.47  --splitting_cvd                         false
% 7.87/1.47  --splitting_cvd_svl                     false
% 7.87/1.47  --splitting_nvd                         32
% 7.87/1.47  --sub_typing                            true
% 7.87/1.47  --prep_gs_sim                           true
% 7.87/1.47  --prep_unflatten                        true
% 7.87/1.47  --prep_res_sim                          true
% 7.87/1.47  --prep_upred                            true
% 7.87/1.47  --prep_sem_filter                       exhaustive
% 7.87/1.47  --prep_sem_filter_out                   false
% 7.87/1.47  --pred_elim                             true
% 7.87/1.47  --res_sim_input                         true
% 7.87/1.47  --eq_ax_congr_red                       true
% 7.87/1.47  --pure_diseq_elim                       true
% 7.87/1.47  --brand_transform                       false
% 7.87/1.47  --non_eq_to_eq                          false
% 7.87/1.47  --prep_def_merge                        true
% 7.87/1.47  --prep_def_merge_prop_impl              false
% 7.87/1.47  --prep_def_merge_mbd                    true
% 7.87/1.47  --prep_def_merge_tr_red                 false
% 7.87/1.47  --prep_def_merge_tr_cl                  false
% 7.87/1.47  --smt_preprocessing                     true
% 7.87/1.47  --smt_ac_axioms                         fast
% 7.87/1.47  --preprocessed_out                      false
% 7.87/1.47  --preprocessed_stats                    false
% 7.87/1.47  
% 7.87/1.47  ------ Abstraction refinement Options
% 7.87/1.47  
% 7.87/1.47  --abstr_ref                             []
% 7.87/1.47  --abstr_ref_prep                        false
% 7.87/1.47  --abstr_ref_until_sat                   false
% 7.87/1.47  --abstr_ref_sig_restrict                funpre
% 7.87/1.47  --abstr_ref_af_restrict_to_split_sk     false
% 7.87/1.47  --abstr_ref_under                       []
% 7.87/1.47  
% 7.87/1.47  ------ SAT Options
% 7.87/1.47  
% 7.87/1.47  --sat_mode                              false
% 7.87/1.47  --sat_fm_restart_options                ""
% 7.87/1.47  --sat_gr_def                            false
% 7.87/1.47  --sat_epr_types                         true
% 7.87/1.47  --sat_non_cyclic_types                  false
% 7.87/1.47  --sat_finite_models                     false
% 7.87/1.47  --sat_fm_lemmas                         false
% 7.87/1.47  --sat_fm_prep                           false
% 7.87/1.47  --sat_fm_uc_incr                        true
% 7.87/1.47  --sat_out_model                         small
% 7.87/1.47  --sat_out_clauses                       false
% 7.87/1.47  
% 7.87/1.47  ------ QBF Options
% 7.87/1.47  
% 7.87/1.47  --qbf_mode                              false
% 7.87/1.47  --qbf_elim_univ                         false
% 7.87/1.47  --qbf_dom_inst                          none
% 7.87/1.47  --qbf_dom_pre_inst                      false
% 7.87/1.47  --qbf_sk_in                             false
% 7.87/1.47  --qbf_pred_elim                         true
% 7.87/1.47  --qbf_split                             512
% 7.87/1.47  
% 7.87/1.47  ------ BMC1 Options
% 7.87/1.47  
% 7.87/1.47  --bmc1_incremental                      false
% 7.87/1.47  --bmc1_axioms                           reachable_all
% 7.87/1.47  --bmc1_min_bound                        0
% 7.87/1.47  --bmc1_max_bound                        -1
% 7.87/1.47  --bmc1_max_bound_default                -1
% 7.87/1.47  --bmc1_symbol_reachability              true
% 7.87/1.47  --bmc1_property_lemmas                  false
% 7.87/1.47  --bmc1_k_induction                      false
% 7.87/1.47  --bmc1_non_equiv_states                 false
% 7.87/1.47  --bmc1_deadlock                         false
% 7.87/1.47  --bmc1_ucm                              false
% 7.87/1.47  --bmc1_add_unsat_core                   none
% 7.87/1.47  --bmc1_unsat_core_children              false
% 7.87/1.47  --bmc1_unsat_core_extrapolate_axioms    false
% 7.87/1.47  --bmc1_out_stat                         full
% 7.87/1.47  --bmc1_ground_init                      false
% 7.87/1.47  --bmc1_pre_inst_next_state              false
% 7.87/1.47  --bmc1_pre_inst_state                   false
% 7.87/1.47  --bmc1_pre_inst_reach_state             false
% 7.87/1.47  --bmc1_out_unsat_core                   false
% 7.87/1.47  --bmc1_aig_witness_out                  false
% 7.87/1.47  --bmc1_verbose                          false
% 7.87/1.47  --bmc1_dump_clauses_tptp                false
% 7.87/1.47  --bmc1_dump_unsat_core_tptp             false
% 7.87/1.47  --bmc1_dump_file                        -
% 7.87/1.47  --bmc1_ucm_expand_uc_limit              128
% 7.87/1.47  --bmc1_ucm_n_expand_iterations          6
% 7.87/1.47  --bmc1_ucm_extend_mode                  1
% 7.87/1.47  --bmc1_ucm_init_mode                    2
% 7.87/1.47  --bmc1_ucm_cone_mode                    none
% 7.87/1.47  --bmc1_ucm_reduced_relation_type        0
% 7.87/1.47  --bmc1_ucm_relax_model                  4
% 7.87/1.47  --bmc1_ucm_full_tr_after_sat            true
% 7.87/1.47  --bmc1_ucm_expand_neg_assumptions       false
% 7.87/1.47  --bmc1_ucm_layered_model                none
% 7.87/1.47  --bmc1_ucm_max_lemma_size               10
% 7.87/1.47  
% 7.87/1.47  ------ AIG Options
% 7.87/1.47  
% 7.87/1.47  --aig_mode                              false
% 7.87/1.47  
% 7.87/1.47  ------ Instantiation Options
% 7.87/1.47  
% 7.87/1.47  --instantiation_flag                    true
% 7.87/1.47  --inst_sos_flag                         true
% 7.87/1.47  --inst_sos_phase                        true
% 7.87/1.47  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 7.87/1.47  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 7.87/1.47  --inst_lit_sel_side                     num_symb
% 7.87/1.47  --inst_solver_per_active                1400
% 7.87/1.47  --inst_solver_calls_frac                1.
% 7.87/1.47  --inst_passive_queue_type               priority_queues
% 7.87/1.47  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 7.87/1.47  --inst_passive_queues_freq              [25;2]
% 7.87/1.47  --inst_dismatching                      true
% 7.87/1.47  --inst_eager_unprocessed_to_passive     true
% 7.87/1.47  --inst_prop_sim_given                   true
% 7.87/1.47  --inst_prop_sim_new                     false
% 7.87/1.47  --inst_subs_new                         false
% 7.87/1.47  --inst_eq_res_simp                      false
% 7.87/1.47  --inst_subs_given                       false
% 7.87/1.47  --inst_orphan_elimination               true
% 7.87/1.47  --inst_learning_loop_flag               true
% 7.87/1.47  --inst_learning_start                   3000
% 7.87/1.47  --inst_learning_factor                  2
% 7.87/1.47  --inst_start_prop_sim_after_learn       3
% 7.87/1.47  --inst_sel_renew                        solver
% 7.87/1.47  --inst_lit_activity_flag                true
% 7.87/1.47  --inst_restr_to_given                   false
% 7.87/1.47  --inst_activity_threshold               500
% 7.87/1.47  --inst_out_proof                        true
% 7.87/1.47  
% 7.87/1.47  ------ Resolution Options
% 7.87/1.47  
% 7.87/1.47  --resolution_flag                       true
% 7.87/1.47  --res_lit_sel                           adaptive
% 7.87/1.47  --res_lit_sel_side                      none
% 7.87/1.47  --res_ordering                          kbo
% 7.87/1.47  --res_to_prop_solver                    active
% 7.87/1.47  --res_prop_simpl_new                    false
% 7.87/1.47  --res_prop_simpl_given                  true
% 7.87/1.47  --res_passive_queue_type                priority_queues
% 7.87/1.47  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 7.87/1.47  --res_passive_queues_freq               [15;5]
% 7.87/1.47  --res_forward_subs                      full
% 7.87/1.47  --res_backward_subs                     full
% 7.87/1.47  --res_forward_subs_resolution           true
% 7.87/1.47  --res_backward_subs_resolution          true
% 7.87/1.47  --res_orphan_elimination                true
% 7.87/1.47  --res_time_limit                        2.
% 7.87/1.47  --res_out_proof                         true
% 7.87/1.47  
% 7.87/1.47  ------ Superposition Options
% 7.87/1.47  
% 7.87/1.47  --superposition_flag                    true
% 7.87/1.47  --sup_passive_queue_type                priority_queues
% 7.87/1.47  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 7.87/1.47  --sup_passive_queues_freq               [8;1;4]
% 7.87/1.47  --demod_completeness_check              fast
% 7.87/1.47  --demod_use_ground                      true
% 7.87/1.47  --sup_to_prop_solver                    passive
% 7.87/1.47  --sup_prop_simpl_new                    true
% 7.87/1.47  --sup_prop_simpl_given                  true
% 7.87/1.47  --sup_fun_splitting                     true
% 7.87/1.47  --sup_smt_interval                      50000
% 7.87/1.47  
% 7.87/1.47  ------ Superposition Simplification Setup
% 7.87/1.47  
% 7.87/1.47  --sup_indices_passive                   [LightNormIndex;FwDemodIndex]
% 7.87/1.47  --sup_indices_active                    [SubsumptionIndex;BwDemodIndex]
% 7.87/1.47  --sup_indices_immed                     [SubsumptionIndex;FwDemodIndex;BwDemodIndex]
% 7.87/1.47  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex]
% 7.87/1.47  --sup_full_triv                         [TrivRules;PropSubs]
% 7.87/1.47  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;Joinability]
% 7.87/1.47  --sup_full_bw                           [BwDemod;BwSubsumption]
% 7.87/1.47  --sup_immed_triv                        [TrivRules]
% 7.87/1.47  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 7.87/1.47  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption]
% 7.87/1.47  --sup_immed_bw_main                     []
% 7.87/1.47  --sup_immed_bw_immed                    [BwDemod;BwSubsumption]
% 7.87/1.47  --sup_input_triv                        [Unflattening;TrivRules]
% 7.87/1.47  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption]
% 7.87/1.47  --sup_input_bw                          []
% 7.87/1.47  
% 7.87/1.47  ------ Combination Options
% 7.87/1.47  
% 7.87/1.47  --comb_res_mult                         3
% 7.87/1.47  --comb_sup_mult                         2
% 7.87/1.47  --comb_inst_mult                        10
% 7.87/1.47  
% 7.87/1.47  ------ Debug Options
% 7.87/1.47  
% 7.87/1.47  --dbg_backtrace                         false
% 7.87/1.47  --dbg_dump_prop_clauses                 false
% 7.87/1.47  --dbg_dump_prop_clauses_file            -
% 7.87/1.47  --dbg_out_stat                          false
% 7.87/1.47  ------ Parsing...
% 7.87/1.47  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 7.87/1.47  
% 7.87/1.47  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe:1:0s pe_e  sf_s  rm: 2 0s  sf_e  pe_s  pe_e 
% 7.87/1.47  
% 7.87/1.47  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 7.87/1.47  
% 7.87/1.47  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 7.87/1.47  ------ Proving...
% 7.87/1.47  ------ Problem Properties 
% 7.87/1.47  
% 7.87/1.47  
% 7.87/1.47  clauses                                 11
% 7.87/1.47  conjectures                             3
% 7.87/1.47  EPR                                     3
% 7.87/1.47  Horn                                    11
% 7.87/1.47  unary                                   7
% 7.87/1.47  binary                                  1
% 7.87/1.47  lits                                    18
% 7.87/1.47  lits eq                                 4
% 7.87/1.47  fd_pure                                 0
% 7.87/1.47  fd_pseudo                               0
% 7.87/1.47  fd_cond                                 0
% 7.87/1.47  fd_pseudo_cond                          0
% 7.87/1.47  AC symbols                              0
% 7.87/1.47  
% 7.87/1.47  ------ Schedule dynamic 5 is on 
% 7.87/1.47  
% 7.87/1.47  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" Time Limit: 10.
% 7.87/1.47  
% 7.87/1.47  
% 7.87/1.47  ------ 
% 7.87/1.47  Current options:
% 7.87/1.47  ------ 
% 7.87/1.47  
% 7.87/1.47  ------ Input Options
% 7.87/1.47  
% 7.87/1.47  --out_options                           all
% 7.87/1.47  --tptp_safe_out                         true
% 7.87/1.47  --problem_path                          ""
% 7.87/1.47  --include_path                          ""
% 7.87/1.47  --clausifier                            res/vclausify_rel
% 7.87/1.47  --clausifier_options                    ""
% 7.87/1.47  --stdin                                 false
% 7.87/1.47  --stats_out                             all
% 7.87/1.47  
% 7.87/1.47  ------ General Options
% 7.87/1.47  
% 7.87/1.47  --fof                                   false
% 7.87/1.47  --time_out_real                         305.
% 7.87/1.47  --time_out_virtual                      -1.
% 7.87/1.47  --symbol_type_check                     false
% 7.87/1.47  --clausify_out                          false
% 7.87/1.47  --sig_cnt_out                           false
% 7.87/1.47  --trig_cnt_out                          false
% 7.87/1.47  --trig_cnt_out_tolerance                1.
% 7.87/1.47  --trig_cnt_out_sk_spl                   false
% 7.87/1.47  --abstr_cl_out                          false
% 7.87/1.47  
% 7.87/1.47  ------ Global Options
% 7.87/1.47  
% 7.87/1.47  --schedule                              default
% 7.87/1.47  --add_important_lit                     false
% 7.87/1.47  --prop_solver_per_cl                    1000
% 7.87/1.47  --min_unsat_core                        false
% 7.87/1.47  --soft_assumptions                      false
% 7.87/1.47  --soft_lemma_size                       3
% 7.87/1.47  --prop_impl_unit_size                   0
% 7.87/1.47  --prop_impl_unit                        []
% 7.87/1.47  --share_sel_clauses                     true
% 7.87/1.47  --reset_solvers                         false
% 7.87/1.47  --bc_imp_inh                            [conj_cone]
% 7.87/1.47  --conj_cone_tolerance                   3.
% 7.87/1.47  --extra_neg_conj                        none
% 7.87/1.47  --large_theory_mode                     true
% 7.87/1.47  --prolific_symb_bound                   200
% 7.87/1.47  --lt_threshold                          2000
% 7.87/1.47  --clause_weak_htbl                      true
% 7.87/1.47  --gc_record_bc_elim                     false
% 7.87/1.47  
% 7.87/1.47  ------ Preprocessing Options
% 7.87/1.47  
% 7.87/1.47  --preprocessing_flag                    true
% 7.87/1.47  --time_out_prep_mult                    0.1
% 7.87/1.47  --splitting_mode                        input
% 7.87/1.47  --splitting_grd                         true
% 7.87/1.47  --splitting_cvd                         false
% 7.87/1.47  --splitting_cvd_svl                     false
% 7.87/1.47  --splitting_nvd                         32
% 7.87/1.47  --sub_typing                            true
% 7.87/1.47  --prep_gs_sim                           true
% 7.87/1.47  --prep_unflatten                        true
% 7.87/1.47  --prep_res_sim                          true
% 7.87/1.47  --prep_upred                            true
% 7.87/1.47  --prep_sem_filter                       exhaustive
% 7.87/1.47  --prep_sem_filter_out                   false
% 7.87/1.47  --pred_elim                             true
% 7.87/1.47  --res_sim_input                         true
% 7.87/1.47  --eq_ax_congr_red                       true
% 7.87/1.47  --pure_diseq_elim                       true
% 7.87/1.47  --brand_transform                       false
% 7.87/1.47  --non_eq_to_eq                          false
% 7.87/1.47  --prep_def_merge                        true
% 7.87/1.47  --prep_def_merge_prop_impl              false
% 7.87/1.47  --prep_def_merge_mbd                    true
% 7.87/1.47  --prep_def_merge_tr_red                 false
% 7.87/1.47  --prep_def_merge_tr_cl                  false
% 7.87/1.47  --smt_preprocessing                     true
% 7.87/1.47  --smt_ac_axioms                         fast
% 7.87/1.47  --preprocessed_out                      false
% 7.87/1.47  --preprocessed_stats                    false
% 7.87/1.47  
% 7.87/1.47  ------ Abstraction refinement Options
% 7.87/1.47  
% 7.87/1.47  --abstr_ref                             []
% 7.87/1.47  --abstr_ref_prep                        false
% 7.87/1.47  --abstr_ref_until_sat                   false
% 7.87/1.47  --abstr_ref_sig_restrict                funpre
% 7.87/1.47  --abstr_ref_af_restrict_to_split_sk     false
% 7.87/1.47  --abstr_ref_under                       []
% 7.87/1.47  
% 7.87/1.47  ------ SAT Options
% 7.87/1.47  
% 7.87/1.47  --sat_mode                              false
% 7.87/1.47  --sat_fm_restart_options                ""
% 7.87/1.47  --sat_gr_def                            false
% 7.87/1.47  --sat_epr_types                         true
% 7.87/1.47  --sat_non_cyclic_types                  false
% 7.87/1.47  --sat_finite_models                     false
% 7.87/1.47  --sat_fm_lemmas                         false
% 7.87/1.47  --sat_fm_prep                           false
% 7.87/1.47  --sat_fm_uc_incr                        true
% 7.87/1.47  --sat_out_model                         small
% 7.87/1.47  --sat_out_clauses                       false
% 7.87/1.47  
% 7.87/1.47  ------ QBF Options
% 7.87/1.47  
% 7.87/1.47  --qbf_mode                              false
% 7.87/1.47  --qbf_elim_univ                         false
% 7.87/1.47  --qbf_dom_inst                          none
% 7.87/1.47  --qbf_dom_pre_inst                      false
% 7.87/1.47  --qbf_sk_in                             false
% 7.87/1.47  --qbf_pred_elim                         true
% 7.87/1.47  --qbf_split                             512
% 7.87/1.47  
% 7.87/1.47  ------ BMC1 Options
% 7.87/1.47  
% 7.87/1.47  --bmc1_incremental                      false
% 7.87/1.47  --bmc1_axioms                           reachable_all
% 7.87/1.47  --bmc1_min_bound                        0
% 7.87/1.47  --bmc1_max_bound                        -1
% 7.87/1.47  --bmc1_max_bound_default                -1
% 7.87/1.47  --bmc1_symbol_reachability              true
% 7.87/1.47  --bmc1_property_lemmas                  false
% 7.87/1.47  --bmc1_k_induction                      false
% 7.87/1.47  --bmc1_non_equiv_states                 false
% 7.87/1.47  --bmc1_deadlock                         false
% 7.87/1.47  --bmc1_ucm                              false
% 7.87/1.47  --bmc1_add_unsat_core                   none
% 7.87/1.47  --bmc1_unsat_core_children              false
% 7.87/1.47  --bmc1_unsat_core_extrapolate_axioms    false
% 7.87/1.47  --bmc1_out_stat                         full
% 7.87/1.47  --bmc1_ground_init                      false
% 7.87/1.47  --bmc1_pre_inst_next_state              false
% 7.87/1.47  --bmc1_pre_inst_state                   false
% 7.87/1.47  --bmc1_pre_inst_reach_state             false
% 7.87/1.47  --bmc1_out_unsat_core                   false
% 7.87/1.47  --bmc1_aig_witness_out                  false
% 7.87/1.47  --bmc1_verbose                          false
% 7.87/1.47  --bmc1_dump_clauses_tptp                false
% 7.87/1.47  --bmc1_dump_unsat_core_tptp             false
% 7.87/1.47  --bmc1_dump_file                        -
% 7.87/1.47  --bmc1_ucm_expand_uc_limit              128
% 7.87/1.47  --bmc1_ucm_n_expand_iterations          6
% 7.87/1.47  --bmc1_ucm_extend_mode                  1
% 7.87/1.47  --bmc1_ucm_init_mode                    2
% 7.87/1.47  --bmc1_ucm_cone_mode                    none
% 7.87/1.47  --bmc1_ucm_reduced_relation_type        0
% 7.87/1.47  --bmc1_ucm_relax_model                  4
% 7.87/1.47  --bmc1_ucm_full_tr_after_sat            true
% 7.87/1.47  --bmc1_ucm_expand_neg_assumptions       false
% 7.87/1.47  --bmc1_ucm_layered_model                none
% 7.87/1.47  --bmc1_ucm_max_lemma_size               10
% 7.87/1.47  
% 7.87/1.47  ------ AIG Options
% 7.87/1.47  
% 7.87/1.47  --aig_mode                              false
% 7.87/1.47  
% 7.87/1.47  ------ Instantiation Options
% 7.87/1.47  
% 7.87/1.47  --instantiation_flag                    true
% 7.87/1.47  --inst_sos_flag                         true
% 7.87/1.47  --inst_sos_phase                        true
% 7.87/1.47  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 7.87/1.47  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 7.87/1.47  --inst_lit_sel_side                     none
% 7.87/1.47  --inst_solver_per_active                1400
% 7.87/1.47  --inst_solver_calls_frac                1.
% 7.87/1.47  --inst_passive_queue_type               priority_queues
% 7.87/1.47  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 7.87/1.47  --inst_passive_queues_freq              [25;2]
% 7.87/1.47  --inst_dismatching                      true
% 7.87/1.47  --inst_eager_unprocessed_to_passive     true
% 7.87/1.47  --inst_prop_sim_given                   true
% 7.87/1.47  --inst_prop_sim_new                     false
% 7.87/1.47  --inst_subs_new                         false
% 7.87/1.47  --inst_eq_res_simp                      false
% 7.87/1.47  --inst_subs_given                       false
% 7.87/1.47  --inst_orphan_elimination               true
% 7.87/1.47  --inst_learning_loop_flag               true
% 7.87/1.47  --inst_learning_start                   3000
% 7.87/1.47  --inst_learning_factor                  2
% 7.87/1.47  --inst_start_prop_sim_after_learn       3
% 7.87/1.47  --inst_sel_renew                        solver
% 7.87/1.47  --inst_lit_activity_flag                true
% 7.87/1.47  --inst_restr_to_given                   false
% 7.87/1.47  --inst_activity_threshold               500
% 7.87/1.47  --inst_out_proof                        true
% 7.87/1.47  
% 7.87/1.47  ------ Resolution Options
% 7.87/1.47  
% 7.87/1.47  --resolution_flag                       false
% 7.87/1.47  --res_lit_sel                           adaptive
% 7.87/1.47  --res_lit_sel_side                      none
% 7.87/1.47  --res_ordering                          kbo
% 7.87/1.47  --res_to_prop_solver                    active
% 7.87/1.47  --res_prop_simpl_new                    false
% 7.87/1.47  --res_prop_simpl_given                  true
% 7.87/1.47  --res_passive_queue_type                priority_queues
% 7.87/1.47  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 7.87/1.47  --res_passive_queues_freq               [15;5]
% 7.87/1.47  --res_forward_subs                      full
% 7.87/1.47  --res_backward_subs                     full
% 7.87/1.47  --res_forward_subs_resolution           true
% 7.87/1.47  --res_backward_subs_resolution          true
% 7.87/1.47  --res_orphan_elimination                true
% 7.87/1.47  --res_time_limit                        2.
% 7.87/1.47  --res_out_proof                         true
% 7.87/1.47  
% 7.87/1.47  ------ Superposition Options
% 7.87/1.47  
% 7.87/1.47  --superposition_flag                    true
% 7.87/1.47  --sup_passive_queue_type                priority_queues
% 7.87/1.47  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 7.87/1.47  --sup_passive_queues_freq               [8;1;4]
% 7.87/1.47  --demod_completeness_check              fast
% 7.87/1.47  --demod_use_ground                      true
% 7.87/1.47  --sup_to_prop_solver                    passive
% 7.87/1.47  --sup_prop_simpl_new                    true
% 7.87/1.47  --sup_prop_simpl_given                  true
% 7.87/1.47  --sup_fun_splitting                     true
% 7.87/1.47  --sup_smt_interval                      50000
% 7.87/1.47  
% 7.87/1.47  ------ Superposition Simplification Setup
% 7.87/1.47  
% 7.87/1.47  --sup_indices_passive                   [LightNormIndex;FwDemodIndex]
% 7.87/1.47  --sup_indices_active                    [SubsumptionIndex;BwDemodIndex]
% 7.87/1.47  --sup_indices_immed                     [SubsumptionIndex;FwDemodIndex;BwDemodIndex]
% 7.87/1.47  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex]
% 7.87/1.47  --sup_full_triv                         [TrivRules;PropSubs]
% 7.87/1.47  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;Joinability]
% 7.87/1.47  --sup_full_bw                           [BwDemod;BwSubsumption]
% 7.87/1.47  --sup_immed_triv                        [TrivRules]
% 7.87/1.47  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 7.87/1.47  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption]
% 7.87/1.47  --sup_immed_bw_main                     []
% 7.87/1.47  --sup_immed_bw_immed                    [BwDemod;BwSubsumption]
% 7.87/1.47  --sup_input_triv                        [Unflattening;TrivRules]
% 7.87/1.47  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption]
% 7.87/1.47  --sup_input_bw                          []
% 7.87/1.47  
% 7.87/1.47  ------ Combination Options
% 7.87/1.47  
% 7.87/1.47  --comb_res_mult                         3
% 7.87/1.47  --comb_sup_mult                         2
% 7.87/1.47  --comb_inst_mult                        10
% 7.87/1.47  
% 7.87/1.47  ------ Debug Options
% 7.87/1.47  
% 7.87/1.47  --dbg_backtrace                         false
% 7.87/1.47  --dbg_dump_prop_clauses                 false
% 7.87/1.47  --dbg_dump_prop_clauses_file            -
% 7.87/1.47  --dbg_out_stat                          false
% 7.87/1.47  
% 7.87/1.47  
% 7.87/1.47  
% 7.87/1.47  
% 7.87/1.47  ------ Proving...
% 7.87/1.47  
% 7.87/1.47  
% 7.87/1.47  % SZS status Theorem for theBenchmark.p
% 7.87/1.47  
% 7.87/1.47  % SZS output start CNFRefutation for theBenchmark.p
% 7.87/1.47  
% 7.87/1.47  fof(f4,axiom,(
% 7.87/1.47    ! [X0,X1] : r1_tarski(k4_xboole_0(X0,X1),X0)),
% 7.87/1.47    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.87/1.47  
% 7.87/1.47  fof(f29,plain,(
% 7.87/1.47    ( ! [X0,X1] : (r1_tarski(k4_xboole_0(X0,X1),X0)) )),
% 7.87/1.47    inference(cnf_transformation,[],[f4])).
% 7.87/1.47  
% 7.87/1.47  fof(f2,axiom,(
% 7.87/1.47    ! [X0,X1] : (r1_tarski(X0,X1) => k2_xboole_0(X0,X1) = X1)),
% 7.87/1.47    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.87/1.47  
% 7.87/1.47  fof(f16,plain,(
% 7.87/1.47    ! [X0,X1] : (k2_xboole_0(X0,X1) = X1 | ~r1_tarski(X0,X1))),
% 7.87/1.47    inference(ennf_transformation,[],[f2])).
% 7.87/1.47  
% 7.87/1.47  fof(f27,plain,(
% 7.87/1.47    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = X1 | ~r1_tarski(X0,X1)) )),
% 7.87/1.47    inference(cnf_transformation,[],[f16])).
% 7.87/1.47  
% 7.87/1.47  fof(f9,axiom,(
% 7.87/1.47    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1))),
% 7.87/1.47    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.87/1.47  
% 7.87/1.47  fof(f34,plain,(
% 7.87/1.47    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1))) )),
% 7.87/1.47    inference(cnf_transformation,[],[f9])).
% 7.87/1.47  
% 7.87/1.47  fof(f7,axiom,(
% 7.87/1.47    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1)),
% 7.87/1.47    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.87/1.47  
% 7.87/1.47  fof(f32,plain,(
% 7.87/1.47    ( ! [X0,X1] : (k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1)) )),
% 7.87/1.47    inference(cnf_transformation,[],[f7])).
% 7.87/1.47  
% 7.87/1.47  fof(f8,axiom,(
% 7.87/1.47    ! [X0,X1,X2] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2)),
% 7.87/1.47    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.87/1.47  
% 7.87/1.47  fof(f33,plain,(
% 7.87/1.47    ( ! [X2,X0,X1] : (k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2)) )),
% 7.87/1.47    inference(cnf_transformation,[],[f8])).
% 7.87/1.47  
% 7.87/1.47  fof(f43,plain,(
% 7.87/1.47    ( ! [X0,X1] : (k2_tarski(X0,X1) = k2_enumset1(X0,X0,X0,X1)) )),
% 7.87/1.47    inference(definition_unfolding,[],[f32,f33])).
% 7.87/1.47  
% 7.87/1.47  fof(f44,plain,(
% 7.87/1.47    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k3_tarski(k2_enumset1(X0,X0,X0,X1))) )),
% 7.87/1.47    inference(definition_unfolding,[],[f34,f43])).
% 7.87/1.47  
% 7.87/1.47  fof(f46,plain,(
% 7.87/1.47    ( ! [X0,X1] : (k3_tarski(k2_enumset1(X0,X0,X0,X1)) = X1 | ~r1_tarski(X0,X1)) )),
% 7.87/1.47    inference(definition_unfolding,[],[f27,f44])).
% 7.87/1.47  
% 7.87/1.47  fof(f1,axiom,(
% 7.87/1.47    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0)),
% 7.87/1.47    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.87/1.47  
% 7.87/1.47  fof(f26,plain,(
% 7.87/1.47    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0)) )),
% 7.87/1.47    inference(cnf_transformation,[],[f1])).
% 7.87/1.47  
% 7.87/1.47  fof(f5,axiom,(
% 7.87/1.47    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1))),
% 7.87/1.47    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.87/1.47  
% 7.87/1.47  fof(f30,plain,(
% 7.87/1.47    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1))) )),
% 7.87/1.48    inference(cnf_transformation,[],[f5])).
% 7.87/1.48  
% 7.87/1.48  fof(f45,plain,(
% 7.87/1.48    ( ! [X0,X1] : (k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k4_xboole_0(X1,k4_xboole_0(X1,X0))) )),
% 7.87/1.48    inference(definition_unfolding,[],[f26,f30,f30])).
% 7.87/1.48  
% 7.87/1.48  fof(f14,conjecture,(
% 7.87/1.48    ! [X0] : (v1_relat_1(X0) => ! [X1] : (v1_relat_1(X1) => r1_tarski(k1_relat_1(k3_xboole_0(X0,X1)),k3_xboole_0(k1_relat_1(X0),k1_relat_1(X1)))))),
% 7.87/1.48    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.87/1.48  
% 7.87/1.48  fof(f15,negated_conjecture,(
% 7.87/1.48    ~! [X0] : (v1_relat_1(X0) => ! [X1] : (v1_relat_1(X1) => r1_tarski(k1_relat_1(k3_xboole_0(X0,X1)),k3_xboole_0(k1_relat_1(X0),k1_relat_1(X1)))))),
% 7.87/1.48    inference(negated_conjecture,[],[f14])).
% 7.87/1.48  
% 7.87/1.48  fof(f21,plain,(
% 7.87/1.48    ? [X0] : (? [X1] : (~r1_tarski(k1_relat_1(k3_xboole_0(X0,X1)),k3_xboole_0(k1_relat_1(X0),k1_relat_1(X1))) & v1_relat_1(X1)) & v1_relat_1(X0))),
% 7.87/1.48    inference(ennf_transformation,[],[f15])).
% 7.87/1.48  
% 7.87/1.48  fof(f24,plain,(
% 7.87/1.48    ( ! [X0] : (? [X1] : (~r1_tarski(k1_relat_1(k3_xboole_0(X0,X1)),k3_xboole_0(k1_relat_1(X0),k1_relat_1(X1))) & v1_relat_1(X1)) => (~r1_tarski(k1_relat_1(k3_xboole_0(X0,sK1)),k3_xboole_0(k1_relat_1(X0),k1_relat_1(sK1))) & v1_relat_1(sK1))) )),
% 7.87/1.48    introduced(choice_axiom,[])).
% 7.87/1.48  
% 7.87/1.48  fof(f23,plain,(
% 7.87/1.48    ? [X0] : (? [X1] : (~r1_tarski(k1_relat_1(k3_xboole_0(X0,X1)),k3_xboole_0(k1_relat_1(X0),k1_relat_1(X1))) & v1_relat_1(X1)) & v1_relat_1(X0)) => (? [X1] : (~r1_tarski(k1_relat_1(k3_xboole_0(sK0,X1)),k3_xboole_0(k1_relat_1(sK0),k1_relat_1(X1))) & v1_relat_1(X1)) & v1_relat_1(sK0))),
% 7.87/1.48    introduced(choice_axiom,[])).
% 7.87/1.48  
% 7.87/1.48  fof(f25,plain,(
% 7.87/1.48    (~r1_tarski(k1_relat_1(k3_xboole_0(sK0,sK1)),k3_xboole_0(k1_relat_1(sK0),k1_relat_1(sK1))) & v1_relat_1(sK1)) & v1_relat_1(sK0)),
% 7.87/1.48    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f21,f24,f23])).
% 7.87/1.48  
% 7.87/1.48  fof(f40,plain,(
% 7.87/1.48    v1_relat_1(sK0)),
% 7.87/1.48    inference(cnf_transformation,[],[f25])).
% 7.87/1.48  
% 7.87/1.48  fof(f41,plain,(
% 7.87/1.48    v1_relat_1(sK1)),
% 7.87/1.48    inference(cnf_transformation,[],[f25])).
% 7.87/1.48  
% 7.87/1.48  fof(f12,axiom,(
% 7.87/1.48    ! [X0] : (v1_relat_1(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => v1_relat_1(X1)))),
% 7.87/1.48    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.87/1.48  
% 7.87/1.48  fof(f19,plain,(
% 7.87/1.48    ! [X0] : (! [X1] : (v1_relat_1(X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) | ~v1_relat_1(X0))),
% 7.87/1.48    inference(ennf_transformation,[],[f12])).
% 7.87/1.48  
% 7.87/1.48  fof(f38,plain,(
% 7.87/1.48    ( ! [X0,X1] : (v1_relat_1(X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0)) | ~v1_relat_1(X0)) )),
% 7.87/1.48    inference(cnf_transformation,[],[f19])).
% 7.87/1.48  
% 7.87/1.48  fof(f11,axiom,(
% 7.87/1.48    ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) <=> r1_tarski(X0,X1))),
% 7.87/1.48    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.87/1.48  
% 7.87/1.48  fof(f22,plain,(
% 7.87/1.48    ! [X0,X1] : ((m1_subset_1(X0,k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1)) & (r1_tarski(X0,X1) | ~m1_subset_1(X0,k1_zfmisc_1(X1))))),
% 7.87/1.48    inference(nnf_transformation,[],[f11])).
% 7.87/1.48  
% 7.87/1.48  fof(f37,plain,(
% 7.87/1.48    ( ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1)) )),
% 7.87/1.48    inference(cnf_transformation,[],[f22])).
% 7.87/1.48  
% 7.87/1.48  fof(f13,axiom,(
% 7.87/1.48    ! [X0] : (v1_relat_1(X0) => ! [X1] : (v1_relat_1(X1) => k2_xboole_0(k1_relat_1(X0),k1_relat_1(X1)) = k1_relat_1(k2_xboole_0(X0,X1))))),
% 7.87/1.48    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.87/1.48  
% 7.87/1.48  fof(f20,plain,(
% 7.87/1.48    ! [X0] : (! [X1] : (k2_xboole_0(k1_relat_1(X0),k1_relat_1(X1)) = k1_relat_1(k2_xboole_0(X0,X1)) | ~v1_relat_1(X1)) | ~v1_relat_1(X0))),
% 7.87/1.48    inference(ennf_transformation,[],[f13])).
% 7.87/1.48  
% 7.87/1.48  fof(f39,plain,(
% 7.87/1.48    ( ! [X0,X1] : (k2_xboole_0(k1_relat_1(X0),k1_relat_1(X1)) = k1_relat_1(k2_xboole_0(X0,X1)) | ~v1_relat_1(X1) | ~v1_relat_1(X0)) )),
% 7.87/1.48    inference(cnf_transformation,[],[f20])).
% 7.87/1.48  
% 7.87/1.48  fof(f50,plain,(
% 7.87/1.48    ( ! [X0,X1] : (k3_tarski(k2_enumset1(k1_relat_1(X0),k1_relat_1(X0),k1_relat_1(X0),k1_relat_1(X1))) = k1_relat_1(k3_tarski(k2_enumset1(X0,X0,X0,X1))) | ~v1_relat_1(X1) | ~v1_relat_1(X0)) )),
% 7.87/1.48    inference(definition_unfolding,[],[f39,f44,f44])).
% 7.87/1.48  
% 7.87/1.48  fof(f6,axiom,(
% 7.87/1.48    ! [X0,X1] : r1_tarski(X0,k2_xboole_0(X0,X1))),
% 7.87/1.48    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.87/1.48  
% 7.87/1.48  fof(f31,plain,(
% 7.87/1.48    ( ! [X0,X1] : (r1_tarski(X0,k2_xboole_0(X0,X1))) )),
% 7.87/1.48    inference(cnf_transformation,[],[f6])).
% 7.87/1.48  
% 7.87/1.48  fof(f48,plain,(
% 7.87/1.48    ( ! [X0,X1] : (r1_tarski(X0,k3_tarski(k2_enumset1(X0,X0,X0,X1)))) )),
% 7.87/1.48    inference(definition_unfolding,[],[f31,f44])).
% 7.87/1.48  
% 7.87/1.48  fof(f3,axiom,(
% 7.87/1.48    ! [X0,X1,X2] : ((r1_tarski(X0,X2) & r1_tarski(X0,X1)) => r1_tarski(X0,k3_xboole_0(X1,X2)))),
% 7.87/1.48    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.87/1.48  
% 7.87/1.48  fof(f17,plain,(
% 7.87/1.48    ! [X0,X1,X2] : (r1_tarski(X0,k3_xboole_0(X1,X2)) | (~r1_tarski(X0,X2) | ~r1_tarski(X0,X1)))),
% 7.87/1.48    inference(ennf_transformation,[],[f3])).
% 7.87/1.48  
% 7.87/1.48  fof(f18,plain,(
% 7.87/1.48    ! [X0,X1,X2] : (r1_tarski(X0,k3_xboole_0(X1,X2)) | ~r1_tarski(X0,X2) | ~r1_tarski(X0,X1))),
% 7.87/1.48    inference(flattening,[],[f17])).
% 7.87/1.48  
% 7.87/1.48  fof(f28,plain,(
% 7.87/1.48    ( ! [X2,X0,X1] : (r1_tarski(X0,k3_xboole_0(X1,X2)) | ~r1_tarski(X0,X2) | ~r1_tarski(X0,X1)) )),
% 7.87/1.48    inference(cnf_transformation,[],[f18])).
% 7.87/1.48  
% 7.87/1.48  fof(f47,plain,(
% 7.87/1.48    ( ! [X2,X0,X1] : (r1_tarski(X0,k4_xboole_0(X1,k4_xboole_0(X1,X2))) | ~r1_tarski(X0,X2) | ~r1_tarski(X0,X1)) )),
% 7.87/1.48    inference(definition_unfolding,[],[f28,f30])).
% 7.87/1.48  
% 7.87/1.48  fof(f42,plain,(
% 7.87/1.48    ~r1_tarski(k1_relat_1(k3_xboole_0(sK0,sK1)),k3_xboole_0(k1_relat_1(sK0),k1_relat_1(sK1)))),
% 7.87/1.48    inference(cnf_transformation,[],[f25])).
% 7.87/1.48  
% 7.87/1.48  fof(f51,plain,(
% 7.87/1.48    ~r1_tarski(k1_relat_1(k4_xboole_0(sK0,k4_xboole_0(sK0,sK1))),k4_xboole_0(k1_relat_1(sK0),k4_xboole_0(k1_relat_1(sK0),k1_relat_1(sK1))))),
% 7.87/1.48    inference(definition_unfolding,[],[f42,f30,f30])).
% 7.87/1.48  
% 7.87/1.48  cnf(c_3,plain,
% 7.87/1.48      ( r1_tarski(k4_xboole_0(X0,X1),X0) ),
% 7.87/1.48      inference(cnf_transformation,[],[f29]) ).
% 7.87/1.48  
% 7.87/1.48  cnf(c_393,plain,
% 7.87/1.48      ( r1_tarski(k4_xboole_0(X0,X1),X0) = iProver_top ),
% 7.87/1.48      inference(predicate_to_equality,[status(thm)],[c_3]) ).
% 7.87/1.48  
% 7.87/1.48  cnf(c_1,plain,
% 7.87/1.48      ( ~ r1_tarski(X0,X1) | k3_tarski(k2_enumset1(X0,X0,X0,X1)) = X1 ),
% 7.87/1.48      inference(cnf_transformation,[],[f46]) ).
% 7.87/1.48  
% 7.87/1.48  cnf(c_395,plain,
% 7.87/1.48      ( k3_tarski(k2_enumset1(X0,X0,X0,X1)) = X1
% 7.87/1.48      | r1_tarski(X0,X1) != iProver_top ),
% 7.87/1.48      inference(predicate_to_equality,[status(thm)],[c_1]) ).
% 7.87/1.48  
% 7.87/1.48  cnf(c_789,plain,
% 7.87/1.48      ( k3_tarski(k2_enumset1(k4_xboole_0(X0,X1),k4_xboole_0(X0,X1),k4_xboole_0(X0,X1),X0)) = X0 ),
% 7.87/1.48      inference(superposition,[status(thm)],[c_393,c_395]) ).
% 7.87/1.48  
% 7.87/1.48  cnf(c_0,plain,
% 7.87/1.48      ( k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k4_xboole_0(X1,k4_xboole_0(X1,X0)) ),
% 7.87/1.48      inference(cnf_transformation,[],[f45]) ).
% 7.87/1.48  
% 7.87/1.48  cnf(c_12,negated_conjecture,
% 7.87/1.48      ( v1_relat_1(sK0) ),
% 7.87/1.48      inference(cnf_transformation,[],[f40]) ).
% 7.87/1.48  
% 7.87/1.48  cnf(c_388,plain,
% 7.87/1.48      ( v1_relat_1(sK0) = iProver_top ),
% 7.87/1.48      inference(predicate_to_equality,[status(thm)],[c_12]) ).
% 7.87/1.48  
% 7.87/1.48  cnf(c_11,negated_conjecture,
% 7.87/1.48      ( v1_relat_1(sK1) ),
% 7.87/1.48      inference(cnf_transformation,[],[f41]) ).
% 7.87/1.48  
% 7.87/1.48  cnf(c_389,plain,
% 7.87/1.48      ( v1_relat_1(sK1) = iProver_top ),
% 7.87/1.48      inference(predicate_to_equality,[status(thm)],[c_11]) ).
% 7.87/1.48  
% 7.87/1.48  cnf(c_8,plain,
% 7.87/1.48      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
% 7.87/1.48      | ~ v1_relat_1(X1)
% 7.87/1.48      | v1_relat_1(X0) ),
% 7.87/1.48      inference(cnf_transformation,[],[f38]) ).
% 7.87/1.48  
% 7.87/1.48  cnf(c_6,plain,
% 7.87/1.48      ( m1_subset_1(X0,k1_zfmisc_1(X1)) | ~ r1_tarski(X0,X1) ),
% 7.87/1.48      inference(cnf_transformation,[],[f37]) ).
% 7.87/1.48  
% 7.87/1.48  cnf(c_89,plain,
% 7.87/1.48      ( ~ r1_tarski(X0,X1) | m1_subset_1(X0,k1_zfmisc_1(X1)) ),
% 7.87/1.48      inference(prop_impl,[status(thm)],[c_6]) ).
% 7.87/1.48  
% 7.87/1.48  cnf(c_90,plain,
% 7.87/1.48      ( m1_subset_1(X0,k1_zfmisc_1(X1)) | ~ r1_tarski(X0,X1) ),
% 7.87/1.48      inference(renaming,[status(thm)],[c_89]) ).
% 7.87/1.48  
% 7.87/1.48  cnf(c_111,plain,
% 7.87/1.48      ( ~ r1_tarski(X0,X1) | ~ v1_relat_1(X1) | v1_relat_1(X0) ),
% 7.87/1.48      inference(bin_hyper_res,[status(thm)],[c_8,c_90]) ).
% 7.87/1.48  
% 7.87/1.48  cnf(c_387,plain,
% 7.87/1.48      ( r1_tarski(X0,X1) != iProver_top
% 7.87/1.48      | v1_relat_1(X1) != iProver_top
% 7.87/1.48      | v1_relat_1(X0) = iProver_top ),
% 7.87/1.48      inference(predicate_to_equality,[status(thm)],[c_111]) ).
% 7.87/1.48  
% 7.87/1.48  cnf(c_701,plain,
% 7.87/1.48      ( v1_relat_1(X0) != iProver_top
% 7.87/1.48      | v1_relat_1(k4_xboole_0(X0,X1)) = iProver_top ),
% 7.87/1.48      inference(superposition,[status(thm)],[c_393,c_387]) ).
% 7.87/1.48  
% 7.87/1.48  cnf(c_9,plain,
% 7.87/1.48      ( ~ v1_relat_1(X0)
% 7.87/1.48      | ~ v1_relat_1(X1)
% 7.87/1.48      | k3_tarski(k2_enumset1(k1_relat_1(X0),k1_relat_1(X0),k1_relat_1(X0),k1_relat_1(X1))) = k1_relat_1(k3_tarski(k2_enumset1(X0,X0,X0,X1))) ),
% 7.87/1.48      inference(cnf_transformation,[],[f50]) ).
% 7.87/1.48  
% 7.87/1.48  cnf(c_391,plain,
% 7.87/1.48      ( k3_tarski(k2_enumset1(k1_relat_1(X0),k1_relat_1(X0),k1_relat_1(X0),k1_relat_1(X1))) = k1_relat_1(k3_tarski(k2_enumset1(X0,X0,X0,X1)))
% 7.87/1.48      | v1_relat_1(X0) != iProver_top
% 7.87/1.48      | v1_relat_1(X1) != iProver_top ),
% 7.87/1.48      inference(predicate_to_equality,[status(thm)],[c_9]) ).
% 7.87/1.48  
% 7.87/1.48  cnf(c_1197,plain,
% 7.87/1.48      ( k3_tarski(k2_enumset1(k1_relat_1(k4_xboole_0(X0,X1)),k1_relat_1(k4_xboole_0(X0,X1)),k1_relat_1(k4_xboole_0(X0,X1)),k1_relat_1(X2))) = k1_relat_1(k3_tarski(k2_enumset1(k4_xboole_0(X0,X1),k4_xboole_0(X0,X1),k4_xboole_0(X0,X1),X2)))
% 7.87/1.48      | v1_relat_1(X0) != iProver_top
% 7.87/1.48      | v1_relat_1(X2) != iProver_top ),
% 7.87/1.48      inference(superposition,[status(thm)],[c_701,c_391]) ).
% 7.87/1.48  
% 7.87/1.48  cnf(c_10277,plain,
% 7.87/1.48      ( k3_tarski(k2_enumset1(k1_relat_1(k4_xboole_0(sK1,X0)),k1_relat_1(k4_xboole_0(sK1,X0)),k1_relat_1(k4_xboole_0(sK1,X0)),k1_relat_1(X1))) = k1_relat_1(k3_tarski(k2_enumset1(k4_xboole_0(sK1,X0),k4_xboole_0(sK1,X0),k4_xboole_0(sK1,X0),X1)))
% 7.87/1.48      | v1_relat_1(X1) != iProver_top ),
% 7.87/1.48      inference(superposition,[status(thm)],[c_389,c_1197]) ).
% 7.87/1.48  
% 7.87/1.48  cnf(c_11253,plain,
% 7.87/1.48      ( k3_tarski(k2_enumset1(k1_relat_1(k4_xboole_0(sK1,X0)),k1_relat_1(k4_xboole_0(sK1,X0)),k1_relat_1(k4_xboole_0(sK1,X0)),k1_relat_1(sK0))) = k1_relat_1(k3_tarski(k2_enumset1(k4_xboole_0(sK1,X0),k4_xboole_0(sK1,X0),k4_xboole_0(sK1,X0),sK0))) ),
% 7.87/1.48      inference(superposition,[status(thm)],[c_388,c_10277]) ).
% 7.87/1.48  
% 7.87/1.48  cnf(c_4,plain,
% 7.87/1.48      ( r1_tarski(X0,k3_tarski(k2_enumset1(X0,X0,X0,X1))) ),
% 7.87/1.48      inference(cnf_transformation,[],[f48]) ).
% 7.87/1.48  
% 7.87/1.48  cnf(c_392,plain,
% 7.87/1.48      ( r1_tarski(X0,k3_tarski(k2_enumset1(X0,X0,X0,X1))) = iProver_top ),
% 7.87/1.48      inference(predicate_to_equality,[status(thm)],[c_4]) ).
% 7.87/1.48  
% 7.87/1.48  cnf(c_11295,plain,
% 7.87/1.48      ( r1_tarski(k1_relat_1(k4_xboole_0(sK1,X0)),k1_relat_1(k3_tarski(k2_enumset1(k4_xboole_0(sK1,X0),k4_xboole_0(sK1,X0),k4_xboole_0(sK1,X0),sK0)))) = iProver_top ),
% 7.87/1.48      inference(superposition,[status(thm)],[c_11253,c_392]) ).
% 7.87/1.48  
% 7.87/1.48  cnf(c_12087,plain,
% 7.87/1.48      ( r1_tarski(k1_relat_1(k4_xboole_0(X0,k4_xboole_0(X0,sK1))),k1_relat_1(k3_tarski(k2_enumset1(k4_xboole_0(X0,k4_xboole_0(X0,sK1)),k4_xboole_0(X0,k4_xboole_0(X0,sK1)),k4_xboole_0(X0,k4_xboole_0(X0,sK1)),sK0)))) = iProver_top ),
% 7.87/1.48      inference(superposition,[status(thm)],[c_0,c_11295]) ).
% 7.87/1.48  
% 7.87/1.48  cnf(c_13031,plain,
% 7.87/1.48      ( r1_tarski(k1_relat_1(k4_xboole_0(sK0,k4_xboole_0(sK0,sK1))),k1_relat_1(sK0)) = iProver_top ),
% 7.87/1.48      inference(superposition,[status(thm)],[c_789,c_12087]) ).
% 7.87/1.48  
% 7.87/1.48  cnf(c_573,plain,
% 7.87/1.48      ( r1_tarski(k4_xboole_0(X0,k4_xboole_0(X0,X1)),X1) = iProver_top ),
% 7.87/1.48      inference(superposition,[status(thm)],[c_0,c_393]) ).
% 7.87/1.48  
% 7.87/1.48  cnf(c_791,plain,
% 7.87/1.48      ( k3_tarski(k2_enumset1(k4_xboole_0(X0,k4_xboole_0(X0,X1)),k4_xboole_0(X0,k4_xboole_0(X0,X1)),k4_xboole_0(X0,k4_xboole_0(X0,X1)),X1)) = X1 ),
% 7.87/1.48      inference(superposition,[status(thm)],[c_573,c_395]) ).
% 7.87/1.48  
% 7.87/1.48  cnf(c_10278,plain,
% 7.87/1.48      ( k3_tarski(k2_enumset1(k1_relat_1(k4_xboole_0(sK0,X0)),k1_relat_1(k4_xboole_0(sK0,X0)),k1_relat_1(k4_xboole_0(sK0,X0)),k1_relat_1(X1))) = k1_relat_1(k3_tarski(k2_enumset1(k4_xboole_0(sK0,X0),k4_xboole_0(sK0,X0),k4_xboole_0(sK0,X0),X1)))
% 7.87/1.48      | v1_relat_1(X1) != iProver_top ),
% 7.87/1.48      inference(superposition,[status(thm)],[c_388,c_1197]) ).
% 7.87/1.48  
% 7.87/1.48  cnf(c_11487,plain,
% 7.87/1.48      ( k3_tarski(k2_enumset1(k1_relat_1(k4_xboole_0(sK0,X0)),k1_relat_1(k4_xboole_0(sK0,X0)),k1_relat_1(k4_xboole_0(sK0,X0)),k1_relat_1(sK1))) = k1_relat_1(k3_tarski(k2_enumset1(k4_xboole_0(sK0,X0),k4_xboole_0(sK0,X0),k4_xboole_0(sK0,X0),sK1))) ),
% 7.87/1.48      inference(superposition,[status(thm)],[c_389,c_10278]) ).
% 7.87/1.48  
% 7.87/1.48  cnf(c_11530,plain,
% 7.87/1.48      ( r1_tarski(k1_relat_1(k4_xboole_0(sK0,X0)),k1_relat_1(k3_tarski(k2_enumset1(k4_xboole_0(sK0,X0),k4_xboole_0(sK0,X0),k4_xboole_0(sK0,X0),sK1)))) = iProver_top ),
% 7.87/1.48      inference(superposition,[status(thm)],[c_11487,c_392]) ).
% 7.87/1.48  
% 7.87/1.48  cnf(c_12102,plain,
% 7.87/1.48      ( r1_tarski(k1_relat_1(k4_xboole_0(sK0,k4_xboole_0(sK0,sK1))),k1_relat_1(sK1)) = iProver_top ),
% 7.87/1.48      inference(superposition,[status(thm)],[c_791,c_11530]) ).
% 7.87/1.48  
% 7.87/1.48  cnf(c_2,plain,
% 7.87/1.48      ( ~ r1_tarski(X0,X1)
% 7.87/1.48      | ~ r1_tarski(X0,X2)
% 7.87/1.48      | r1_tarski(X0,k4_xboole_0(X1,k4_xboole_0(X1,X2))) ),
% 7.87/1.48      inference(cnf_transformation,[],[f47]) ).
% 7.87/1.48  
% 7.87/1.48  cnf(c_408,plain,
% 7.87/1.48      ( r1_tarski(k1_relat_1(k4_xboole_0(sK0,k4_xboole_0(sK0,sK1))),k4_xboole_0(k1_relat_1(sK0),k4_xboole_0(k1_relat_1(sK0),k1_relat_1(sK1))))
% 7.87/1.48      | ~ r1_tarski(k1_relat_1(k4_xboole_0(sK0,k4_xboole_0(sK0,sK1))),k1_relat_1(sK1))
% 7.87/1.48      | ~ r1_tarski(k1_relat_1(k4_xboole_0(sK0,k4_xboole_0(sK0,sK1))),k1_relat_1(sK0)) ),
% 7.87/1.48      inference(instantiation,[status(thm)],[c_2]) ).
% 7.87/1.48  
% 7.87/1.48  cnf(c_409,plain,
% 7.87/1.48      ( r1_tarski(k1_relat_1(k4_xboole_0(sK0,k4_xboole_0(sK0,sK1))),k4_xboole_0(k1_relat_1(sK0),k4_xboole_0(k1_relat_1(sK0),k1_relat_1(sK1)))) = iProver_top
% 7.87/1.48      | r1_tarski(k1_relat_1(k4_xboole_0(sK0,k4_xboole_0(sK0,sK1))),k1_relat_1(sK1)) != iProver_top
% 7.87/1.48      | r1_tarski(k1_relat_1(k4_xboole_0(sK0,k4_xboole_0(sK0,sK1))),k1_relat_1(sK0)) != iProver_top ),
% 7.87/1.48      inference(predicate_to_equality,[status(thm)],[c_408]) ).
% 7.87/1.48  
% 7.87/1.48  cnf(c_10,negated_conjecture,
% 7.87/1.48      ( ~ r1_tarski(k1_relat_1(k4_xboole_0(sK0,k4_xboole_0(sK0,sK1))),k4_xboole_0(k1_relat_1(sK0),k4_xboole_0(k1_relat_1(sK0),k1_relat_1(sK1)))) ),
% 7.87/1.48      inference(cnf_transformation,[],[f51]) ).
% 7.87/1.48  
% 7.87/1.48  cnf(c_15,plain,
% 7.87/1.48      ( r1_tarski(k1_relat_1(k4_xboole_0(sK0,k4_xboole_0(sK0,sK1))),k4_xboole_0(k1_relat_1(sK0),k4_xboole_0(k1_relat_1(sK0),k1_relat_1(sK1)))) != iProver_top ),
% 7.87/1.48      inference(predicate_to_equality,[status(thm)],[c_10]) ).
% 7.87/1.48  
% 7.87/1.48  cnf(contradiction,plain,
% 7.87/1.48      ( $false ),
% 7.87/1.48      inference(minisat,[status(thm)],[c_13031,c_12102,c_409,c_15]) ).
% 7.87/1.48  
% 7.87/1.48  
% 7.87/1.48  % SZS output end CNFRefutation for theBenchmark.p
% 7.87/1.48  
% 7.87/1.48  ------                               Statistics
% 7.87/1.48  
% 7.87/1.48  ------ General
% 7.87/1.48  
% 7.87/1.48  abstr_ref_over_cycles:                  0
% 7.87/1.48  abstr_ref_under_cycles:                 0
% 7.87/1.48  gc_basic_clause_elim:                   0
% 7.87/1.48  forced_gc_time:                         0
% 7.87/1.48  parsing_time:                           0.008
% 7.87/1.48  unif_index_cands_time:                  0.
% 7.87/1.48  unif_index_add_time:                    0.
% 7.87/1.48  orderings_time:                         0.
% 7.87/1.48  out_proof_time:                         0.006
% 7.87/1.48  total_time:                             0.882
% 7.87/1.48  num_of_symbols:                         42
% 7.87/1.48  num_of_terms:                           19734
% 7.87/1.48  
% 7.87/1.48  ------ Preprocessing
% 7.87/1.48  
% 7.87/1.48  num_of_splits:                          0
% 7.87/1.48  num_of_split_atoms:                     0
% 7.87/1.48  num_of_reused_defs:                     0
% 7.87/1.48  num_eq_ax_congr_red:                    2
% 7.87/1.48  num_of_sem_filtered_clauses:            1
% 7.87/1.48  num_of_subtypes:                        0
% 7.87/1.48  monotx_restored_types:                  0
% 7.87/1.48  sat_num_of_epr_types:                   0
% 7.87/1.48  sat_num_of_non_cyclic_types:            0
% 7.87/1.48  sat_guarded_non_collapsed_types:        0
% 7.87/1.48  num_pure_diseq_elim:                    0
% 7.87/1.48  simp_replaced_by:                       0
% 7.87/1.48  res_preprocessed:                       65
% 7.87/1.48  prep_upred:                             0
% 7.87/1.48  prep_unflattend:                        0
% 7.87/1.48  smt_new_axioms:                         0
% 7.87/1.48  pred_elim_cands:                        2
% 7.87/1.48  pred_elim:                              1
% 7.87/1.48  pred_elim_cl:                           2
% 7.87/1.48  pred_elim_cycles:                       3
% 7.87/1.48  merged_defs:                            2
% 7.87/1.48  merged_defs_ncl:                        0
% 7.87/1.48  bin_hyper_res:                          3
% 7.87/1.48  prep_cycles:                            4
% 7.87/1.48  pred_elim_time:                         0.
% 7.87/1.48  splitting_time:                         0.
% 7.87/1.48  sem_filter_time:                        0.
% 7.87/1.48  monotx_time:                            0.
% 7.87/1.48  subtype_inf_time:                       0.
% 7.87/1.48  
% 7.87/1.48  ------ Problem properties
% 7.87/1.48  
% 7.87/1.48  clauses:                                11
% 7.87/1.48  conjectures:                            3
% 7.87/1.48  epr:                                    3
% 7.87/1.48  horn:                                   11
% 7.87/1.48  ground:                                 3
% 7.87/1.48  unary:                                  7
% 7.87/1.48  binary:                                 1
% 7.87/1.48  lits:                                   18
% 7.87/1.48  lits_eq:                                4
% 7.87/1.48  fd_pure:                                0
% 7.87/1.48  fd_pseudo:                              0
% 7.87/1.48  fd_cond:                                0
% 7.87/1.48  fd_pseudo_cond:                         0
% 7.87/1.48  ac_symbols:                             0
% 7.87/1.48  
% 7.87/1.48  ------ Propositional Solver
% 7.87/1.48  
% 7.87/1.48  prop_solver_calls:                      37
% 7.87/1.48  prop_fast_solver_calls:                 464
% 7.87/1.48  smt_solver_calls:                       0
% 7.87/1.48  smt_fast_solver_calls:                  0
% 7.87/1.48  prop_num_of_clauses:                    7102
% 7.87/1.48  prop_preprocess_simplified:             11693
% 7.87/1.48  prop_fo_subsumed:                       0
% 7.87/1.48  prop_solver_time:                       0.
% 7.87/1.48  smt_solver_time:                        0.
% 7.87/1.48  smt_fast_solver_time:                   0.
% 7.87/1.48  prop_fast_solver_time:                  0.
% 7.87/1.48  prop_unsat_core_time:                   0.
% 7.87/1.48  
% 7.87/1.48  ------ QBF
% 7.87/1.48  
% 7.87/1.48  qbf_q_res:                              0
% 7.87/1.48  qbf_num_tautologies:                    0
% 7.87/1.48  qbf_prep_cycles:                        0
% 7.87/1.48  
% 7.87/1.48  ------ BMC1
% 7.87/1.48  
% 7.87/1.48  bmc1_current_bound:                     -1
% 7.87/1.48  bmc1_last_solved_bound:                 -1
% 7.87/1.48  bmc1_unsat_core_size:                   -1
% 7.87/1.48  bmc1_unsat_core_parents_size:           -1
% 7.87/1.48  bmc1_merge_next_fun:                    0
% 7.87/1.48  bmc1_unsat_core_clauses_time:           0.
% 7.87/1.48  
% 7.87/1.48  ------ Instantiation
% 7.87/1.48  
% 7.87/1.48  inst_num_of_clauses:                    1998
% 7.87/1.48  inst_num_in_passive:                    723
% 7.87/1.48  inst_num_in_active:                     714
% 7.87/1.48  inst_num_in_unprocessed:                562
% 7.87/1.48  inst_num_of_loops:                      760
% 7.87/1.48  inst_num_of_learning_restarts:          0
% 7.87/1.48  inst_num_moves_active_passive:          39
% 7.87/1.48  inst_lit_activity:                      0
% 7.87/1.48  inst_lit_activity_moves:                0
% 7.87/1.48  inst_num_tautologies:                   0
% 7.87/1.48  inst_num_prop_implied:                  0
% 7.87/1.48  inst_num_existing_simplified:           0
% 7.87/1.48  inst_num_eq_res_simplified:             0
% 7.87/1.48  inst_num_child_elim:                    0
% 7.87/1.48  inst_num_of_dismatching_blockings:      841
% 7.87/1.48  inst_num_of_non_proper_insts:           2044
% 7.87/1.48  inst_num_of_duplicates:                 0
% 7.87/1.48  inst_inst_num_from_inst_to_res:         0
% 7.87/1.48  inst_dismatching_checking_time:         0.
% 7.87/1.48  
% 7.87/1.48  ------ Resolution
% 7.87/1.48  
% 7.87/1.48  res_num_of_clauses:                     0
% 7.87/1.48  res_num_in_passive:                     0
% 7.87/1.48  res_num_in_active:                      0
% 7.87/1.48  res_num_of_loops:                       69
% 7.87/1.48  res_forward_subset_subsumed:            310
% 7.87/1.48  res_backward_subset_subsumed:           2
% 7.87/1.48  res_forward_subsumed:                   0
% 7.87/1.48  res_backward_subsumed:                  0
% 7.87/1.48  res_forward_subsumption_resolution:     0
% 7.87/1.48  res_backward_subsumption_resolution:    0
% 7.87/1.48  res_clause_to_clause_subsumption:       3207
% 7.87/1.48  res_orphan_elimination:                 0
% 7.87/1.48  res_tautology_del:                      206
% 7.87/1.48  res_num_eq_res_simplified:              0
% 7.87/1.48  res_num_sel_changes:                    0
% 7.87/1.48  res_moves_from_active_to_pass:          0
% 7.87/1.48  
% 7.87/1.48  ------ Superposition
% 7.87/1.48  
% 7.87/1.48  sup_time_total:                         0.
% 7.87/1.48  sup_time_generating:                    0.
% 7.87/1.48  sup_time_sim_full:                      0.
% 7.87/1.48  sup_time_sim_immed:                     0.
% 7.87/1.48  
% 7.87/1.48  sup_num_of_clauses:                     405
% 7.87/1.48  sup_num_in_active:                      150
% 7.87/1.48  sup_num_in_passive:                     255
% 7.87/1.48  sup_num_of_loops:                       151
% 7.87/1.48  sup_fw_superposition:                   857
% 7.87/1.48  sup_bw_superposition:                   318
% 7.87/1.48  sup_immediate_simplified:               134
% 7.87/1.48  sup_given_eliminated:                   0
% 7.87/1.48  comparisons_done:                       0
% 7.87/1.48  comparisons_avoided:                    0
% 7.87/1.48  
% 7.87/1.48  ------ Simplifications
% 7.87/1.48  
% 7.87/1.48  
% 7.87/1.48  sim_fw_subset_subsumed:                 0
% 7.87/1.48  sim_bw_subset_subsumed:                 0
% 7.87/1.48  sim_fw_subsumed:                        93
% 7.87/1.48  sim_bw_subsumed:                        2
% 7.87/1.48  sim_fw_subsumption_res:                 0
% 7.87/1.48  sim_bw_subsumption_res:                 0
% 7.87/1.48  sim_tautology_del:                      0
% 7.87/1.48  sim_eq_tautology_del:                   6
% 7.87/1.48  sim_eq_res_simp:                        0
% 7.87/1.48  sim_fw_demodulated:                     42
% 7.87/1.48  sim_bw_demodulated:                     0
% 7.87/1.48  sim_light_normalised:                   2
% 7.87/1.48  sim_joinable_taut:                      0
% 7.87/1.48  sim_joinable_simp:                      0
% 7.87/1.48  sim_ac_normalised:                      0
% 7.87/1.48  sim_smt_subsumption:                    0
% 7.87/1.48  
%------------------------------------------------------------------------------
