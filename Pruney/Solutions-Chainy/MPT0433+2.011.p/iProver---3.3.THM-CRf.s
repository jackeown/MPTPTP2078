%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n021.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 11:42:52 EST 2020

% Result     : Theorem 7.78s
% Output     : CNFRefutation 7.78s
% Verified   : 
% Statistics : Number of formulae       :  114 ( 297 expanded)
%              Number of clauses        :   60 (  95 expanded)
%              Number of leaves         :   19 (  78 expanded)
%              Depth                    :   14
%              Number of atoms          :  244 ( 580 expanded)
%              Number of equality atoms :  103 ( 246 expanded)
%              Maximal formula depth    :    7 (   4 average)
%              Maximal clause size      :    6 (   2 average)
%              Maximal term depth       :    6 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f1,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f30,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f1])).

fof(f7,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f38,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f7])).

fof(f52,plain,(
    ! [X0,X1] : k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k4_xboole_0(X1,k4_xboole_0(X1,X0)) ),
    inference(definition_unfolding,[],[f30,f38,f38])).

fof(f6,axiom,(
    ! [X0,X1] : r1_tarski(k4_xboole_0(X0,X1),X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f37,plain,(
    ! [X0,X1] : r1_tarski(k4_xboole_0(X0,X1),X0) ),
    inference(cnf_transformation,[],[f6])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
     => k2_xboole_0(X0,X1) = X1 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f18,plain,(
    ! [X0,X1] :
      ( k2_xboole_0(X0,X1) = X1
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f35,plain,(
    ! [X0,X1] :
      ( k2_xboole_0(X0,X1) = X1
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f10,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f41,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1)) ),
    inference(cnf_transformation,[],[f10])).

fof(f8,axiom,(
    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f39,plain,(
    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f8])).

fof(f9,axiom,(
    ! [X0,X1,X2] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f40,plain,(
    ! [X2,X0,X1] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2) ),
    inference(cnf_transformation,[],[f9])).

fof(f50,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k2_enumset1(X0,X0,X0,X1) ),
    inference(definition_unfolding,[],[f39,f40])).

fof(f51,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k2_enumset1(X0,X0,X0,X1)) ),
    inference(definition_unfolding,[],[f41,f50])).

fof(f54,plain,(
    ! [X0,X1] :
      ( k3_tarski(k2_enumset1(X0,X0,X0,X1)) = X1
      | ~ r1_tarski(X0,X1) ) ),
    inference(definition_unfolding,[],[f35,f51])).

fof(f15,conjecture,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( v1_relat_1(X1)
         => r1_tarski(k1_relat_1(k3_xboole_0(X0,X1)),k3_xboole_0(k1_relat_1(X0),k1_relat_1(X1))) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f16,negated_conjecture,(
    ~ ! [X0] :
        ( v1_relat_1(X0)
       => ! [X1] :
            ( v1_relat_1(X1)
           => r1_tarski(k1_relat_1(k3_xboole_0(X0,X1)),k3_xboole_0(k1_relat_1(X0),k1_relat_1(X1))) ) ) ),
    inference(negated_conjecture,[],[f15])).

fof(f23,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ~ r1_tarski(k1_relat_1(k3_xboole_0(X0,X1)),k3_xboole_0(k1_relat_1(X0),k1_relat_1(X1)))
          & v1_relat_1(X1) )
      & v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f16])).

fof(f28,plain,(
    ! [X0] :
      ( ? [X1] :
          ( ~ r1_tarski(k1_relat_1(k3_xboole_0(X0,X1)),k3_xboole_0(k1_relat_1(X0),k1_relat_1(X1)))
          & v1_relat_1(X1) )
     => ( ~ r1_tarski(k1_relat_1(k3_xboole_0(X0,sK1)),k3_xboole_0(k1_relat_1(X0),k1_relat_1(sK1)))
        & v1_relat_1(sK1) ) ) ),
    introduced(choice_axiom,[])).

fof(f27,plain,
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

fof(f29,plain,
    ( ~ r1_tarski(k1_relat_1(k3_xboole_0(sK0,sK1)),k3_xboole_0(k1_relat_1(sK0),k1_relat_1(sK1)))
    & v1_relat_1(sK1)
    & v1_relat_1(sK0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f23,f28,f27])).

fof(f48,plain,(
    v1_relat_1(sK1) ),
    inference(cnf_transformation,[],[f29])).

fof(f47,plain,(
    v1_relat_1(sK0) ),
    inference(cnf_transformation,[],[f29])).

fof(f13,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(X0))
         => v1_relat_1(X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f21,plain,(
    ! [X0] :
      ( ! [X1] :
          ( v1_relat_1(X1)
          | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f45,plain,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f12,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f26,plain,(
    ! [X0,X1] :
      ( ( m1_subset_1(X0,k1_zfmisc_1(X1))
        | ~ r1_tarski(X0,X1) )
      & ( r1_tarski(X0,X1)
        | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ) ) ),
    inference(nnf_transformation,[],[f12])).

fof(f44,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f14,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( v1_relat_1(X1)
         => k2_xboole_0(k1_relat_1(X0),k1_relat_1(X1)) = k1_relat_1(k2_xboole_0(X0,X1)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f22,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k2_xboole_0(k1_relat_1(X0),k1_relat_1(X1)) = k1_relat_1(k2_xboole_0(X0,X1))
          | ~ v1_relat_1(X1) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f46,plain,(
    ! [X0,X1] :
      ( k2_xboole_0(k1_relat_1(X0),k1_relat_1(X1)) = k1_relat_1(k2_xboole_0(X0,X1))
      | ~ v1_relat_1(X1)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f57,plain,(
    ! [X0,X1] :
      ( k3_tarski(k2_enumset1(k1_relat_1(X0),k1_relat_1(X0),k1_relat_1(X0),k1_relat_1(X1))) = k1_relat_1(k3_tarski(k2_enumset1(X0,X0,X0,X1)))
      | ~ v1_relat_1(X1)
      | ~ v1_relat_1(X0) ) ),
    inference(definition_unfolding,[],[f46,f51,f51])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( X0 = X1
    <=> ( r1_tarski(X1,X0)
        & r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f24,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(nnf_transformation,[],[f2])).

fof(f25,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(flattening,[],[f24])).

fof(f31,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | X0 != X1 ) ),
    inference(cnf_transformation,[],[f25])).

fof(f60,plain,(
    ! [X1] : r1_tarski(X1,X1) ),
    inference(equality_resolution,[],[f31])).

fof(f3,axiom,(
    ! [X0,X1,X2] :
      ( r1_tarski(k2_xboole_0(X0,X1),X2)
     => r1_tarski(X0,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f17,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,X2)
      | ~ r1_tarski(k2_xboole_0(X0,X1),X2) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f34,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(X0,X2)
      | ~ r1_tarski(k2_xboole_0(X0,X1),X2) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f53,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(X0,X2)
      | ~ r1_tarski(k3_tarski(k2_enumset1(X0,X0,X0,X1)),X2) ) ),
    inference(definition_unfolding,[],[f34,f51])).

fof(f5,axiom,(
    ! [X0,X1,X2] :
      ( ( r1_tarski(X0,X2)
        & r1_tarski(X0,X1) )
     => r1_tarski(X0,k3_xboole_0(X1,X2)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f19,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,k3_xboole_0(X1,X2))
      | ~ r1_tarski(X0,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f20,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,k3_xboole_0(X1,X2))
      | ~ r1_tarski(X0,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(flattening,[],[f19])).

fof(f36,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(X0,k3_xboole_0(X1,X2))
      | ~ r1_tarski(X0,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f55,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(X0,k4_xboole_0(X1,k4_xboole_0(X1,X2)))
      | ~ r1_tarski(X0,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(definition_unfolding,[],[f36,f38])).

fof(f33,plain,(
    ! [X0,X1] :
      ( X0 = X1
      | ~ r1_tarski(X1,X0)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f49,plain,(
    ~ r1_tarski(k1_relat_1(k3_xboole_0(sK0,sK1)),k3_xboole_0(k1_relat_1(sK0),k1_relat_1(sK1))) ),
    inference(cnf_transformation,[],[f29])).

fof(f58,plain,(
    ~ r1_tarski(k1_relat_1(k4_xboole_0(sK0,k4_xboole_0(sK0,sK1))),k4_xboole_0(k1_relat_1(sK0),k4_xboole_0(k1_relat_1(sK0),k1_relat_1(sK1)))) ),
    inference(definition_unfolding,[],[f49,f38,f38])).

cnf(c_0,plain,
    ( k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k4_xboole_0(X1,k4_xboole_0(X1,X0)) ),
    inference(cnf_transformation,[],[f52])).

cnf(c_7,plain,
    ( r1_tarski(k4_xboole_0(X0,X1),X0) ),
    inference(cnf_transformation,[],[f37])).

cnf(c_588,plain,
    ( r1_tarski(k4_xboole_0(X0,X1),X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_7])).

cnf(c_811,plain,
    ( r1_tarski(k4_xboole_0(X0,k4_xboole_0(X0,X1)),X1) = iProver_top ),
    inference(superposition,[status(thm)],[c_0,c_588])).

cnf(c_5,plain,
    ( ~ r1_tarski(X0,X1)
    | k3_tarski(k2_enumset1(X0,X0,X0,X1)) = X1 ),
    inference(cnf_transformation,[],[f54])).

cnf(c_590,plain,
    ( k3_tarski(k2_enumset1(X0,X0,X0,X1)) = X1
    | r1_tarski(X0,X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_5])).

cnf(c_1337,plain,
    ( k3_tarski(k2_enumset1(k4_xboole_0(X0,k4_xboole_0(X0,X1)),k4_xboole_0(X0,k4_xboole_0(X0,X1)),k4_xboole_0(X0,k4_xboole_0(X0,X1)),X1)) = X1 ),
    inference(superposition,[status(thm)],[c_811,c_590])).

cnf(c_14,negated_conjecture,
    ( v1_relat_1(sK1) ),
    inference(cnf_transformation,[],[f48])).

cnf(c_583,plain,
    ( v1_relat_1(sK1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_14])).

cnf(c_15,negated_conjecture,
    ( v1_relat_1(sK0) ),
    inference(cnf_transformation,[],[f47])).

cnf(c_582,plain,
    ( v1_relat_1(sK0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_15])).

cnf(c_11,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | ~ v1_relat_1(X1)
    | v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f45])).

cnf(c_9,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(X1))
    | ~ r1_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f44])).

cnf(c_97,plain,
    ( ~ r1_tarski(X0,X1)
    | m1_subset_1(X0,k1_zfmisc_1(X1)) ),
    inference(prop_impl,[status(thm)],[c_9])).

cnf(c_98,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(X1))
    | ~ r1_tarski(X0,X1) ),
    inference(renaming,[status(thm)],[c_97])).

cnf(c_122,plain,
    ( ~ r1_tarski(X0,X1)
    | ~ v1_relat_1(X1)
    | v1_relat_1(X0) ),
    inference(bin_hyper_res,[status(thm)],[c_11,c_98])).

cnf(c_581,plain,
    ( r1_tarski(X0,X1) != iProver_top
    | v1_relat_1(X1) != iProver_top
    | v1_relat_1(X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_122])).

cnf(c_1055,plain,
    ( v1_relat_1(X0) != iProver_top
    | v1_relat_1(k4_xboole_0(X0,X1)) = iProver_top ),
    inference(superposition,[status(thm)],[c_588,c_581])).

cnf(c_12,plain,
    ( ~ v1_relat_1(X0)
    | ~ v1_relat_1(X1)
    | k3_tarski(k2_enumset1(k1_relat_1(X0),k1_relat_1(X0),k1_relat_1(X0),k1_relat_1(X1))) = k1_relat_1(k3_tarski(k2_enumset1(X0,X0,X0,X1))) ),
    inference(cnf_transformation,[],[f57])).

cnf(c_585,plain,
    ( k3_tarski(k2_enumset1(k1_relat_1(X0),k1_relat_1(X0),k1_relat_1(X0),k1_relat_1(X1))) = k1_relat_1(k3_tarski(k2_enumset1(X0,X0,X0,X1)))
    | v1_relat_1(X0) != iProver_top
    | v1_relat_1(X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_12])).

cnf(c_2201,plain,
    ( k3_tarski(k2_enumset1(k1_relat_1(k4_xboole_0(X0,X1)),k1_relat_1(k4_xboole_0(X0,X1)),k1_relat_1(k4_xboole_0(X0,X1)),k1_relat_1(X2))) = k1_relat_1(k3_tarski(k2_enumset1(k4_xboole_0(X0,X1),k4_xboole_0(X0,X1),k4_xboole_0(X0,X1),X2)))
    | v1_relat_1(X0) != iProver_top
    | v1_relat_1(X2) != iProver_top ),
    inference(superposition,[status(thm)],[c_1055,c_585])).

cnf(c_18385,plain,
    ( k3_tarski(k2_enumset1(k1_relat_1(k4_xboole_0(sK0,X0)),k1_relat_1(k4_xboole_0(sK0,X0)),k1_relat_1(k4_xboole_0(sK0,X0)),k1_relat_1(X1))) = k1_relat_1(k3_tarski(k2_enumset1(k4_xboole_0(sK0,X0),k4_xboole_0(sK0,X0),k4_xboole_0(sK0,X0),X1)))
    | v1_relat_1(X1) != iProver_top ),
    inference(superposition,[status(thm)],[c_582,c_2201])).

cnf(c_19675,plain,
    ( k3_tarski(k2_enumset1(k1_relat_1(k4_xboole_0(sK0,X0)),k1_relat_1(k4_xboole_0(sK0,X0)),k1_relat_1(k4_xboole_0(sK0,X0)),k1_relat_1(sK1))) = k1_relat_1(k3_tarski(k2_enumset1(k4_xboole_0(sK0,X0),k4_xboole_0(sK0,X0),k4_xboole_0(sK0,X0),sK1))) ),
    inference(superposition,[status(thm)],[c_583,c_18385])).

cnf(c_3,plain,
    ( r1_tarski(X0,X0) ),
    inference(cnf_transformation,[],[f60])).

cnf(c_592,plain,
    ( r1_tarski(X0,X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3])).

cnf(c_4,plain,
    ( r1_tarski(X0,X1)
    | ~ r1_tarski(k3_tarski(k2_enumset1(X0,X0,X0,X2)),X1) ),
    inference(cnf_transformation,[],[f53])).

cnf(c_591,plain,
    ( r1_tarski(X0,X1) = iProver_top
    | r1_tarski(k3_tarski(k2_enumset1(X0,X0,X0,X2)),X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_4])).

cnf(c_1799,plain,
    ( r1_tarski(X0,k3_tarski(k2_enumset1(X0,X0,X0,X1))) = iProver_top ),
    inference(superposition,[status(thm)],[c_592,c_591])).

cnf(c_19981,plain,
    ( r1_tarski(k1_relat_1(k4_xboole_0(sK0,X0)),k1_relat_1(k3_tarski(k2_enumset1(k4_xboole_0(sK0,X0),k4_xboole_0(sK0,X0),k4_xboole_0(sK0,X0),sK1)))) = iProver_top ),
    inference(superposition,[status(thm)],[c_19675,c_1799])).

cnf(c_20683,plain,
    ( r1_tarski(k1_relat_1(k4_xboole_0(sK0,k4_xboole_0(sK0,sK1))),k1_relat_1(sK1)) = iProver_top ),
    inference(superposition,[status(thm)],[c_1337,c_19981])).

cnf(c_18384,plain,
    ( k3_tarski(k2_enumset1(k1_relat_1(k4_xboole_0(sK1,X0)),k1_relat_1(k4_xboole_0(sK1,X0)),k1_relat_1(k4_xboole_0(sK1,X0)),k1_relat_1(X1))) = k1_relat_1(k3_tarski(k2_enumset1(k4_xboole_0(sK1,X0),k4_xboole_0(sK1,X0),k4_xboole_0(sK1,X0),X1)))
    | v1_relat_1(X1) != iProver_top ),
    inference(superposition,[status(thm)],[c_583,c_2201])).

cnf(c_19256,plain,
    ( k3_tarski(k2_enumset1(k1_relat_1(k4_xboole_0(sK1,X0)),k1_relat_1(k4_xboole_0(sK1,X0)),k1_relat_1(k4_xboole_0(sK1,X0)),k1_relat_1(sK0))) = k1_relat_1(k3_tarski(k2_enumset1(k4_xboole_0(sK1,X0),k4_xboole_0(sK1,X0),k4_xboole_0(sK1,X0),sK0))) ),
    inference(superposition,[status(thm)],[c_582,c_18384])).

cnf(c_19643,plain,
    ( r1_tarski(k1_relat_1(k4_xboole_0(sK1,X0)),k1_relat_1(k3_tarski(k2_enumset1(k4_xboole_0(sK1,X0),k4_xboole_0(sK1,X0),k4_xboole_0(sK1,X0),sK0)))) = iProver_top ),
    inference(superposition,[status(thm)],[c_19256,c_1799])).

cnf(c_20305,plain,
    ( r1_tarski(k1_relat_1(k4_xboole_0(sK1,k4_xboole_0(sK1,sK0))),k1_relat_1(sK0)) = iProver_top ),
    inference(superposition,[status(thm)],[c_1337,c_19643])).

cnf(c_258,plain,
    ( ~ r1_tarski(X0,X1)
    | r1_tarski(X2,X3)
    | X2 != X0
    | X3 != X1 ),
    theory(equality)).

cnf(c_803,plain,
    ( ~ r1_tarski(X0,X1)
    | r1_tarski(k1_relat_1(k4_xboole_0(sK0,k4_xboole_0(sK0,sK1))),k1_relat_1(sK0))
    | k1_relat_1(k4_xboole_0(sK0,k4_xboole_0(sK0,sK1))) != X0
    | k1_relat_1(sK0) != X1 ),
    inference(instantiation,[status(thm)],[c_258])).

cnf(c_1026,plain,
    ( ~ r1_tarski(X0,k1_relat_1(sK0))
    | r1_tarski(k1_relat_1(k4_xboole_0(sK0,k4_xboole_0(sK0,sK1))),k1_relat_1(sK0))
    | k1_relat_1(k4_xboole_0(sK0,k4_xboole_0(sK0,sK1))) != X0
    | k1_relat_1(sK0) != k1_relat_1(sK0) ),
    inference(instantiation,[status(thm)],[c_803])).

cnf(c_1328,plain,
    ( ~ r1_tarski(k1_relat_1(k4_xboole_0(sK1,k4_xboole_0(sK1,sK0))),k1_relat_1(sK0))
    | r1_tarski(k1_relat_1(k4_xboole_0(sK0,k4_xboole_0(sK0,sK1))),k1_relat_1(sK0))
    | k1_relat_1(k4_xboole_0(sK0,k4_xboole_0(sK0,sK1))) != k1_relat_1(k4_xboole_0(sK1,k4_xboole_0(sK1,sK0)))
    | k1_relat_1(sK0) != k1_relat_1(sK0) ),
    inference(instantiation,[status(thm)],[c_1026])).

cnf(c_1329,plain,
    ( k1_relat_1(k4_xboole_0(sK0,k4_xboole_0(sK0,sK1))) != k1_relat_1(k4_xboole_0(sK1,k4_xboole_0(sK1,sK0)))
    | k1_relat_1(sK0) != k1_relat_1(sK0)
    | r1_tarski(k1_relat_1(k4_xboole_0(sK1,k4_xboole_0(sK1,sK0))),k1_relat_1(sK0)) != iProver_top
    | r1_tarski(k1_relat_1(k4_xboole_0(sK0,k4_xboole_0(sK0,sK1))),k1_relat_1(sK0)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1328])).

cnf(c_6,plain,
    ( ~ r1_tarski(X0,X1)
    | ~ r1_tarski(X0,X2)
    | r1_tarski(X0,k4_xboole_0(X1,k4_xboole_0(X1,X2))) ),
    inference(cnf_transformation,[],[f55])).

cnf(c_1206,plain,
    ( r1_tarski(k1_relat_1(k4_xboole_0(sK0,k4_xboole_0(sK0,sK1))),k4_xboole_0(k1_relat_1(sK1),k4_xboole_0(k1_relat_1(sK1),k1_relat_1(sK0))))
    | ~ r1_tarski(k1_relat_1(k4_xboole_0(sK0,k4_xboole_0(sK0,sK1))),k1_relat_1(sK1))
    | ~ r1_tarski(k1_relat_1(k4_xboole_0(sK0,k4_xboole_0(sK0,sK1))),k1_relat_1(sK0)) ),
    inference(instantiation,[status(thm)],[c_6])).

cnf(c_1207,plain,
    ( r1_tarski(k1_relat_1(k4_xboole_0(sK0,k4_xboole_0(sK0,sK1))),k4_xboole_0(k1_relat_1(sK1),k4_xboole_0(k1_relat_1(sK1),k1_relat_1(sK0)))) = iProver_top
    | r1_tarski(k1_relat_1(k4_xboole_0(sK0,k4_xboole_0(sK0,sK1))),k1_relat_1(sK1)) != iProver_top
    | r1_tarski(k1_relat_1(k4_xboole_0(sK0,k4_xboole_0(sK0,sK1))),k1_relat_1(sK0)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1206])).

cnf(c_962,plain,
    ( k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)) = k4_xboole_0(sK1,k4_xboole_0(sK1,sK0)) ),
    inference(instantiation,[status(thm)],[c_0])).

cnf(c_264,plain,
    ( X0 != X1
    | k1_relat_1(X0) = k1_relat_1(X1) ),
    theory(equality)).

cnf(c_847,plain,
    ( k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)) != X0
    | k1_relat_1(k4_xboole_0(sK0,k4_xboole_0(sK0,sK1))) = k1_relat_1(X0) ),
    inference(instantiation,[status(thm)],[c_264])).

cnf(c_961,plain,
    ( k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)) != k4_xboole_0(sK1,k4_xboole_0(sK1,sK0))
    | k1_relat_1(k4_xboole_0(sK0,k4_xboole_0(sK0,sK1))) = k1_relat_1(k4_xboole_0(sK1,k4_xboole_0(sK1,sK0))) ),
    inference(instantiation,[status(thm)],[c_847])).

cnf(c_944,plain,
    ( k4_xboole_0(k1_relat_1(sK0),k4_xboole_0(k1_relat_1(sK0),k1_relat_1(sK1))) = k4_xboole_0(k1_relat_1(sK1),k4_xboole_0(k1_relat_1(sK1),k1_relat_1(sK0))) ),
    inference(instantiation,[status(thm)],[c_0])).

cnf(c_740,plain,
    ( ~ r1_tarski(X0,X1)
    | r1_tarski(k1_relat_1(k4_xboole_0(sK0,k4_xboole_0(sK0,sK1))),k4_xboole_0(k1_relat_1(sK0),k4_xboole_0(k1_relat_1(sK0),k1_relat_1(sK1))))
    | k4_xboole_0(k1_relat_1(sK0),k4_xboole_0(k1_relat_1(sK0),k1_relat_1(sK1))) != X1
    | k1_relat_1(k4_xboole_0(sK0,k4_xboole_0(sK0,sK1))) != X0 ),
    inference(instantiation,[status(thm)],[c_258])).

cnf(c_839,plain,
    ( ~ r1_tarski(k1_relat_1(k4_xboole_0(sK0,k4_xboole_0(sK0,sK1))),X0)
    | r1_tarski(k1_relat_1(k4_xboole_0(sK0,k4_xboole_0(sK0,sK1))),k4_xboole_0(k1_relat_1(sK0),k4_xboole_0(k1_relat_1(sK0),k1_relat_1(sK1))))
    | k4_xboole_0(k1_relat_1(sK0),k4_xboole_0(k1_relat_1(sK0),k1_relat_1(sK1))) != X0
    | k1_relat_1(k4_xboole_0(sK0,k4_xboole_0(sK0,sK1))) != k1_relat_1(k4_xboole_0(sK0,k4_xboole_0(sK0,sK1))) ),
    inference(instantiation,[status(thm)],[c_740])).

cnf(c_943,plain,
    ( ~ r1_tarski(k1_relat_1(k4_xboole_0(sK0,k4_xboole_0(sK0,sK1))),k4_xboole_0(k1_relat_1(sK1),k4_xboole_0(k1_relat_1(sK1),k1_relat_1(sK0))))
    | r1_tarski(k1_relat_1(k4_xboole_0(sK0,k4_xboole_0(sK0,sK1))),k4_xboole_0(k1_relat_1(sK0),k4_xboole_0(k1_relat_1(sK0),k1_relat_1(sK1))))
    | k4_xboole_0(k1_relat_1(sK0),k4_xboole_0(k1_relat_1(sK0),k1_relat_1(sK1))) != k4_xboole_0(k1_relat_1(sK1),k4_xboole_0(k1_relat_1(sK1),k1_relat_1(sK0)))
    | k1_relat_1(k4_xboole_0(sK0,k4_xboole_0(sK0,sK1))) != k1_relat_1(k4_xboole_0(sK0,k4_xboole_0(sK0,sK1))) ),
    inference(instantiation,[status(thm)],[c_839])).

cnf(c_945,plain,
    ( k4_xboole_0(k1_relat_1(sK0),k4_xboole_0(k1_relat_1(sK0),k1_relat_1(sK1))) != k4_xboole_0(k1_relat_1(sK1),k4_xboole_0(k1_relat_1(sK1),k1_relat_1(sK0)))
    | k1_relat_1(k4_xboole_0(sK0,k4_xboole_0(sK0,sK1))) != k1_relat_1(k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)))
    | r1_tarski(k1_relat_1(k4_xboole_0(sK0,k4_xboole_0(sK0,sK1))),k4_xboole_0(k1_relat_1(sK1),k4_xboole_0(k1_relat_1(sK1),k1_relat_1(sK0)))) != iProver_top
    | r1_tarski(k1_relat_1(k4_xboole_0(sK0,k4_xboole_0(sK0,sK1))),k4_xboole_0(k1_relat_1(sK0),k4_xboole_0(k1_relat_1(sK0),k1_relat_1(sK1)))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_943])).

cnf(c_255,plain,
    ( X0 = X0 ),
    theory(equality)).

cnf(c_840,plain,
    ( k1_relat_1(k4_xboole_0(sK0,k4_xboole_0(sK0,sK1))) = k1_relat_1(k4_xboole_0(sK0,k4_xboole_0(sK0,sK1))) ),
    inference(instantiation,[status(thm)],[c_255])).

cnf(c_272,plain,
    ( k1_relat_1(sK0) = k1_relat_1(sK0)
    | sK0 != sK0 ),
    inference(instantiation,[status(thm)],[c_264])).

cnf(c_1,plain,
    ( ~ r1_tarski(X0,X1)
    | ~ r1_tarski(X1,X0)
    | X0 = X1 ),
    inference(cnf_transformation,[],[f33])).

cnf(c_47,plain,
    ( ~ r1_tarski(sK0,sK0)
    | sK0 = sK0 ),
    inference(instantiation,[status(thm)],[c_1])).

cnf(c_43,plain,
    ( r1_tarski(sK0,sK0) ),
    inference(instantiation,[status(thm)],[c_3])).

cnf(c_13,negated_conjecture,
    ( ~ r1_tarski(k1_relat_1(k4_xboole_0(sK0,k4_xboole_0(sK0,sK1))),k4_xboole_0(k1_relat_1(sK0),k4_xboole_0(k1_relat_1(sK0),k1_relat_1(sK1)))) ),
    inference(cnf_transformation,[],[f58])).

cnf(c_18,plain,
    ( r1_tarski(k1_relat_1(k4_xboole_0(sK0,k4_xboole_0(sK0,sK1))),k4_xboole_0(k1_relat_1(sK0),k4_xboole_0(k1_relat_1(sK0),k1_relat_1(sK1)))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_13])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_20683,c_20305,c_1329,c_1207,c_962,c_961,c_944,c_945,c_840,c_272,c_47,c_43,c_18])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.10/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.10/0.12  % Command    : iproveropt_run.sh %d %s
% 0.13/0.33  % Computer   : n021.cluster.edu
% 0.13/0.33  % Model      : x86_64 x86_64
% 0.13/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.33  % Memory     : 8042.1875MB
% 0.13/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.33  % CPULimit   : 60
% 0.13/0.33  % WCLimit    : 600
% 0.13/0.33  % DateTime   : Tue Dec  1 10:01:49 EST 2020
% 0.13/0.33  % CPUTime    : 
% 0.13/0.34  % Running in FOF mode
% 7.78/1.50  % SZS status Started for /export/starexec/sandbox/benchmark/theBenchmark.p
% 7.78/1.50  
% 7.78/1.50  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 7.78/1.50  
% 7.78/1.50  ------  iProver source info
% 7.78/1.50  
% 7.78/1.50  git: date: 2020-06-30 10:37:57 +0100
% 7.78/1.50  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 7.78/1.50  git: non_committed_changes: false
% 7.78/1.50  git: last_make_outside_of_git: false
% 7.78/1.50  
% 7.78/1.50  ------ 
% 7.78/1.50  ------ Parsing...
% 7.78/1.50  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 7.78/1.50  
% 7.78/1.50  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 1 0s  sf_e 
% 7.78/1.50  
% 7.78/1.50  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 7.78/1.50  
% 7.78/1.50  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 7.78/1.50  ------ Proving...
% 7.78/1.50  ------ Problem Properties 
% 7.78/1.50  
% 7.78/1.50  
% 7.78/1.50  clauses                                 15
% 7.78/1.50  conjectures                             3
% 7.78/1.50  EPR                                     5
% 7.78/1.50  Horn                                    15
% 7.78/1.50  unary                                   7
% 7.78/1.50  binary                                  4
% 7.78/1.50  lits                                    27
% 7.78/1.50  lits eq                                 5
% 7.78/1.50  fd_pure                                 0
% 7.78/1.50  fd_pseudo                               0
% 7.78/1.50  fd_cond                                 0
% 7.78/1.50  fd_pseudo_cond                          1
% 7.78/1.50  AC symbols                              0
% 7.78/1.50  
% 7.78/1.50  ------ Input Options Time Limit: Unbounded
% 7.78/1.50  
% 7.78/1.50  
% 7.78/1.50  ------ 
% 7.78/1.50  Current options:
% 7.78/1.50  ------ 
% 7.78/1.50  
% 7.78/1.50  
% 7.78/1.50  
% 7.78/1.50  
% 7.78/1.50  ------ Proving...
% 7.78/1.50  
% 7.78/1.50  
% 7.78/1.50  % SZS status Theorem for theBenchmark.p
% 7.78/1.50  
% 7.78/1.50  % SZS output start CNFRefutation for theBenchmark.p
% 7.78/1.50  
% 7.78/1.50  fof(f1,axiom,(
% 7.78/1.50    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0)),
% 7.78/1.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.78/1.50  
% 7.78/1.50  fof(f30,plain,(
% 7.78/1.50    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0)) )),
% 7.78/1.50    inference(cnf_transformation,[],[f1])).
% 7.78/1.50  
% 7.78/1.50  fof(f7,axiom,(
% 7.78/1.50    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1))),
% 7.78/1.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.78/1.50  
% 7.78/1.50  fof(f38,plain,(
% 7.78/1.50    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1))) )),
% 7.78/1.50    inference(cnf_transformation,[],[f7])).
% 7.78/1.50  
% 7.78/1.50  fof(f52,plain,(
% 7.78/1.50    ( ! [X0,X1] : (k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k4_xboole_0(X1,k4_xboole_0(X1,X0))) )),
% 7.78/1.50    inference(definition_unfolding,[],[f30,f38,f38])).
% 7.78/1.50  
% 7.78/1.50  fof(f6,axiom,(
% 7.78/1.50    ! [X0,X1] : r1_tarski(k4_xboole_0(X0,X1),X0)),
% 7.78/1.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.78/1.50  
% 7.78/1.50  fof(f37,plain,(
% 7.78/1.50    ( ! [X0,X1] : (r1_tarski(k4_xboole_0(X0,X1),X0)) )),
% 7.78/1.50    inference(cnf_transformation,[],[f6])).
% 7.78/1.50  
% 7.78/1.50  fof(f4,axiom,(
% 7.78/1.50    ! [X0,X1] : (r1_tarski(X0,X1) => k2_xboole_0(X0,X1) = X1)),
% 7.78/1.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.78/1.50  
% 7.78/1.50  fof(f18,plain,(
% 7.78/1.50    ! [X0,X1] : (k2_xboole_0(X0,X1) = X1 | ~r1_tarski(X0,X1))),
% 7.78/1.50    inference(ennf_transformation,[],[f4])).
% 7.78/1.50  
% 7.78/1.50  fof(f35,plain,(
% 7.78/1.50    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = X1 | ~r1_tarski(X0,X1)) )),
% 7.78/1.50    inference(cnf_transformation,[],[f18])).
% 7.78/1.50  
% 7.78/1.50  fof(f10,axiom,(
% 7.78/1.50    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1))),
% 7.78/1.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.78/1.50  
% 7.78/1.50  fof(f41,plain,(
% 7.78/1.50    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1))) )),
% 7.78/1.50    inference(cnf_transformation,[],[f10])).
% 7.78/1.50  
% 7.78/1.50  fof(f8,axiom,(
% 7.78/1.50    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1)),
% 7.78/1.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.78/1.50  
% 7.78/1.50  fof(f39,plain,(
% 7.78/1.50    ( ! [X0,X1] : (k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1)) )),
% 7.78/1.50    inference(cnf_transformation,[],[f8])).
% 7.78/1.50  
% 7.78/1.50  fof(f9,axiom,(
% 7.78/1.50    ! [X0,X1,X2] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2)),
% 7.78/1.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.78/1.50  
% 7.78/1.50  fof(f40,plain,(
% 7.78/1.50    ( ! [X2,X0,X1] : (k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2)) )),
% 7.78/1.50    inference(cnf_transformation,[],[f9])).
% 7.78/1.50  
% 7.78/1.50  fof(f50,plain,(
% 7.78/1.50    ( ! [X0,X1] : (k2_tarski(X0,X1) = k2_enumset1(X0,X0,X0,X1)) )),
% 7.78/1.50    inference(definition_unfolding,[],[f39,f40])).
% 7.78/1.50  
% 7.78/1.50  fof(f51,plain,(
% 7.78/1.50    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k3_tarski(k2_enumset1(X0,X0,X0,X1))) )),
% 7.78/1.50    inference(definition_unfolding,[],[f41,f50])).
% 7.78/1.50  
% 7.78/1.50  fof(f54,plain,(
% 7.78/1.50    ( ! [X0,X1] : (k3_tarski(k2_enumset1(X0,X0,X0,X1)) = X1 | ~r1_tarski(X0,X1)) )),
% 7.78/1.50    inference(definition_unfolding,[],[f35,f51])).
% 7.78/1.50  
% 7.78/1.50  fof(f15,conjecture,(
% 7.78/1.50    ! [X0] : (v1_relat_1(X0) => ! [X1] : (v1_relat_1(X1) => r1_tarski(k1_relat_1(k3_xboole_0(X0,X1)),k3_xboole_0(k1_relat_1(X0),k1_relat_1(X1)))))),
% 7.78/1.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.78/1.50  
% 7.78/1.50  fof(f16,negated_conjecture,(
% 7.78/1.50    ~! [X0] : (v1_relat_1(X0) => ! [X1] : (v1_relat_1(X1) => r1_tarski(k1_relat_1(k3_xboole_0(X0,X1)),k3_xboole_0(k1_relat_1(X0),k1_relat_1(X1)))))),
% 7.78/1.50    inference(negated_conjecture,[],[f15])).
% 7.78/1.50  
% 7.78/1.50  fof(f23,plain,(
% 7.78/1.50    ? [X0] : (? [X1] : (~r1_tarski(k1_relat_1(k3_xboole_0(X0,X1)),k3_xboole_0(k1_relat_1(X0),k1_relat_1(X1))) & v1_relat_1(X1)) & v1_relat_1(X0))),
% 7.78/1.50    inference(ennf_transformation,[],[f16])).
% 7.78/1.50  
% 7.78/1.50  fof(f28,plain,(
% 7.78/1.50    ( ! [X0] : (? [X1] : (~r1_tarski(k1_relat_1(k3_xboole_0(X0,X1)),k3_xboole_0(k1_relat_1(X0),k1_relat_1(X1))) & v1_relat_1(X1)) => (~r1_tarski(k1_relat_1(k3_xboole_0(X0,sK1)),k3_xboole_0(k1_relat_1(X0),k1_relat_1(sK1))) & v1_relat_1(sK1))) )),
% 7.78/1.50    introduced(choice_axiom,[])).
% 7.78/1.50  
% 7.78/1.50  fof(f27,plain,(
% 7.78/1.50    ? [X0] : (? [X1] : (~r1_tarski(k1_relat_1(k3_xboole_0(X0,X1)),k3_xboole_0(k1_relat_1(X0),k1_relat_1(X1))) & v1_relat_1(X1)) & v1_relat_1(X0)) => (? [X1] : (~r1_tarski(k1_relat_1(k3_xboole_0(sK0,X1)),k3_xboole_0(k1_relat_1(sK0),k1_relat_1(X1))) & v1_relat_1(X1)) & v1_relat_1(sK0))),
% 7.78/1.50    introduced(choice_axiom,[])).
% 7.78/1.50  
% 7.78/1.50  fof(f29,plain,(
% 7.78/1.50    (~r1_tarski(k1_relat_1(k3_xboole_0(sK0,sK1)),k3_xboole_0(k1_relat_1(sK0),k1_relat_1(sK1))) & v1_relat_1(sK1)) & v1_relat_1(sK0)),
% 7.78/1.50    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f23,f28,f27])).
% 7.78/1.50  
% 7.78/1.50  fof(f48,plain,(
% 7.78/1.50    v1_relat_1(sK1)),
% 7.78/1.50    inference(cnf_transformation,[],[f29])).
% 7.78/1.50  
% 7.78/1.50  fof(f47,plain,(
% 7.78/1.50    v1_relat_1(sK0)),
% 7.78/1.50    inference(cnf_transformation,[],[f29])).
% 7.78/1.50  
% 7.78/1.50  fof(f13,axiom,(
% 7.78/1.50    ! [X0] : (v1_relat_1(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => v1_relat_1(X1)))),
% 7.78/1.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.78/1.50  
% 7.78/1.50  fof(f21,plain,(
% 7.78/1.50    ! [X0] : (! [X1] : (v1_relat_1(X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) | ~v1_relat_1(X0))),
% 7.78/1.50    inference(ennf_transformation,[],[f13])).
% 7.78/1.50  
% 7.78/1.50  fof(f45,plain,(
% 7.78/1.50    ( ! [X0,X1] : (v1_relat_1(X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0)) | ~v1_relat_1(X0)) )),
% 7.78/1.50    inference(cnf_transformation,[],[f21])).
% 7.78/1.50  
% 7.78/1.50  fof(f12,axiom,(
% 7.78/1.50    ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) <=> r1_tarski(X0,X1))),
% 7.78/1.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.78/1.50  
% 7.78/1.50  fof(f26,plain,(
% 7.78/1.50    ! [X0,X1] : ((m1_subset_1(X0,k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1)) & (r1_tarski(X0,X1) | ~m1_subset_1(X0,k1_zfmisc_1(X1))))),
% 7.78/1.50    inference(nnf_transformation,[],[f12])).
% 7.78/1.50  
% 7.78/1.50  fof(f44,plain,(
% 7.78/1.50    ( ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1)) )),
% 7.78/1.50    inference(cnf_transformation,[],[f26])).
% 7.78/1.50  
% 7.78/1.50  fof(f14,axiom,(
% 7.78/1.50    ! [X0] : (v1_relat_1(X0) => ! [X1] : (v1_relat_1(X1) => k2_xboole_0(k1_relat_1(X0),k1_relat_1(X1)) = k1_relat_1(k2_xboole_0(X0,X1))))),
% 7.78/1.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.78/1.50  
% 7.78/1.50  fof(f22,plain,(
% 7.78/1.50    ! [X0] : (! [X1] : (k2_xboole_0(k1_relat_1(X0),k1_relat_1(X1)) = k1_relat_1(k2_xboole_0(X0,X1)) | ~v1_relat_1(X1)) | ~v1_relat_1(X0))),
% 7.78/1.50    inference(ennf_transformation,[],[f14])).
% 7.78/1.50  
% 7.78/1.50  fof(f46,plain,(
% 7.78/1.50    ( ! [X0,X1] : (k2_xboole_0(k1_relat_1(X0),k1_relat_1(X1)) = k1_relat_1(k2_xboole_0(X0,X1)) | ~v1_relat_1(X1) | ~v1_relat_1(X0)) )),
% 7.78/1.50    inference(cnf_transformation,[],[f22])).
% 7.78/1.50  
% 7.78/1.50  fof(f57,plain,(
% 7.78/1.50    ( ! [X0,X1] : (k3_tarski(k2_enumset1(k1_relat_1(X0),k1_relat_1(X0),k1_relat_1(X0),k1_relat_1(X1))) = k1_relat_1(k3_tarski(k2_enumset1(X0,X0,X0,X1))) | ~v1_relat_1(X1) | ~v1_relat_1(X0)) )),
% 7.78/1.50    inference(definition_unfolding,[],[f46,f51,f51])).
% 7.78/1.50  
% 7.78/1.50  fof(f2,axiom,(
% 7.78/1.50    ! [X0,X1] : (X0 = X1 <=> (r1_tarski(X1,X0) & r1_tarski(X0,X1)))),
% 7.78/1.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.78/1.50  
% 7.78/1.50  fof(f24,plain,(
% 7.78/1.50    ! [X0,X1] : ((X0 = X1 | (~r1_tarski(X1,X0) | ~r1_tarski(X0,X1))) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 7.78/1.50    inference(nnf_transformation,[],[f2])).
% 7.78/1.50  
% 7.78/1.50  fof(f25,plain,(
% 7.78/1.50    ! [X0,X1] : ((X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 7.78/1.50    inference(flattening,[],[f24])).
% 7.78/1.50  
% 7.78/1.50  fof(f31,plain,(
% 7.78/1.50    ( ! [X0,X1] : (r1_tarski(X0,X1) | X0 != X1) )),
% 7.78/1.50    inference(cnf_transformation,[],[f25])).
% 7.78/1.50  
% 7.78/1.50  fof(f60,plain,(
% 7.78/1.50    ( ! [X1] : (r1_tarski(X1,X1)) )),
% 7.78/1.50    inference(equality_resolution,[],[f31])).
% 7.78/1.50  
% 7.78/1.50  fof(f3,axiom,(
% 7.78/1.50    ! [X0,X1,X2] : (r1_tarski(k2_xboole_0(X0,X1),X2) => r1_tarski(X0,X2))),
% 7.78/1.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.78/1.50  
% 7.78/1.50  fof(f17,plain,(
% 7.78/1.50    ! [X0,X1,X2] : (r1_tarski(X0,X2) | ~r1_tarski(k2_xboole_0(X0,X1),X2))),
% 7.78/1.50    inference(ennf_transformation,[],[f3])).
% 7.78/1.50  
% 7.78/1.50  fof(f34,plain,(
% 7.78/1.50    ( ! [X2,X0,X1] : (r1_tarski(X0,X2) | ~r1_tarski(k2_xboole_0(X0,X1),X2)) )),
% 7.78/1.50    inference(cnf_transformation,[],[f17])).
% 7.78/1.50  
% 7.78/1.50  fof(f53,plain,(
% 7.78/1.50    ( ! [X2,X0,X1] : (r1_tarski(X0,X2) | ~r1_tarski(k3_tarski(k2_enumset1(X0,X0,X0,X1)),X2)) )),
% 7.78/1.50    inference(definition_unfolding,[],[f34,f51])).
% 7.78/1.50  
% 7.78/1.50  fof(f5,axiom,(
% 7.78/1.50    ! [X0,X1,X2] : ((r1_tarski(X0,X2) & r1_tarski(X0,X1)) => r1_tarski(X0,k3_xboole_0(X1,X2)))),
% 7.78/1.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.78/1.50  
% 7.78/1.50  fof(f19,plain,(
% 7.78/1.50    ! [X0,X1,X2] : (r1_tarski(X0,k3_xboole_0(X1,X2)) | (~r1_tarski(X0,X2) | ~r1_tarski(X0,X1)))),
% 7.78/1.50    inference(ennf_transformation,[],[f5])).
% 7.78/1.50  
% 7.78/1.50  fof(f20,plain,(
% 7.78/1.50    ! [X0,X1,X2] : (r1_tarski(X0,k3_xboole_0(X1,X2)) | ~r1_tarski(X0,X2) | ~r1_tarski(X0,X1))),
% 7.78/1.50    inference(flattening,[],[f19])).
% 7.78/1.50  
% 7.78/1.50  fof(f36,plain,(
% 7.78/1.50    ( ! [X2,X0,X1] : (r1_tarski(X0,k3_xboole_0(X1,X2)) | ~r1_tarski(X0,X2) | ~r1_tarski(X0,X1)) )),
% 7.78/1.50    inference(cnf_transformation,[],[f20])).
% 7.78/1.50  
% 7.78/1.50  fof(f55,plain,(
% 7.78/1.50    ( ! [X2,X0,X1] : (r1_tarski(X0,k4_xboole_0(X1,k4_xboole_0(X1,X2))) | ~r1_tarski(X0,X2) | ~r1_tarski(X0,X1)) )),
% 7.78/1.50    inference(definition_unfolding,[],[f36,f38])).
% 7.78/1.50  
% 7.78/1.50  fof(f33,plain,(
% 7.78/1.50    ( ! [X0,X1] : (X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) )),
% 7.78/1.50    inference(cnf_transformation,[],[f25])).
% 7.78/1.50  
% 7.78/1.50  fof(f49,plain,(
% 7.78/1.50    ~r1_tarski(k1_relat_1(k3_xboole_0(sK0,sK1)),k3_xboole_0(k1_relat_1(sK0),k1_relat_1(sK1)))),
% 7.78/1.50    inference(cnf_transformation,[],[f29])).
% 7.78/1.50  
% 7.78/1.50  fof(f58,plain,(
% 7.78/1.50    ~r1_tarski(k1_relat_1(k4_xboole_0(sK0,k4_xboole_0(sK0,sK1))),k4_xboole_0(k1_relat_1(sK0),k4_xboole_0(k1_relat_1(sK0),k1_relat_1(sK1))))),
% 7.78/1.50    inference(definition_unfolding,[],[f49,f38,f38])).
% 7.78/1.50  
% 7.78/1.50  cnf(c_0,plain,
% 7.78/1.50      ( k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k4_xboole_0(X1,k4_xboole_0(X1,X0)) ),
% 7.78/1.50      inference(cnf_transformation,[],[f52]) ).
% 7.78/1.50  
% 7.78/1.50  cnf(c_7,plain,
% 7.78/1.50      ( r1_tarski(k4_xboole_0(X0,X1),X0) ),
% 7.78/1.50      inference(cnf_transformation,[],[f37]) ).
% 7.78/1.50  
% 7.78/1.50  cnf(c_588,plain,
% 7.78/1.50      ( r1_tarski(k4_xboole_0(X0,X1),X0) = iProver_top ),
% 7.78/1.50      inference(predicate_to_equality,[status(thm)],[c_7]) ).
% 7.78/1.50  
% 7.78/1.50  cnf(c_811,plain,
% 7.78/1.50      ( r1_tarski(k4_xboole_0(X0,k4_xboole_0(X0,X1)),X1) = iProver_top ),
% 7.78/1.50      inference(superposition,[status(thm)],[c_0,c_588]) ).
% 7.78/1.50  
% 7.78/1.50  cnf(c_5,plain,
% 7.78/1.50      ( ~ r1_tarski(X0,X1) | k3_tarski(k2_enumset1(X0,X0,X0,X1)) = X1 ),
% 7.78/1.50      inference(cnf_transformation,[],[f54]) ).
% 7.78/1.50  
% 7.78/1.50  cnf(c_590,plain,
% 7.78/1.50      ( k3_tarski(k2_enumset1(X0,X0,X0,X1)) = X1
% 7.78/1.50      | r1_tarski(X0,X1) != iProver_top ),
% 7.78/1.50      inference(predicate_to_equality,[status(thm)],[c_5]) ).
% 7.78/1.50  
% 7.78/1.50  cnf(c_1337,plain,
% 7.78/1.50      ( k3_tarski(k2_enumset1(k4_xboole_0(X0,k4_xboole_0(X0,X1)),k4_xboole_0(X0,k4_xboole_0(X0,X1)),k4_xboole_0(X0,k4_xboole_0(X0,X1)),X1)) = X1 ),
% 7.78/1.50      inference(superposition,[status(thm)],[c_811,c_590]) ).
% 7.78/1.50  
% 7.78/1.50  cnf(c_14,negated_conjecture,
% 7.78/1.50      ( v1_relat_1(sK1) ),
% 7.78/1.50      inference(cnf_transformation,[],[f48]) ).
% 7.78/1.50  
% 7.78/1.50  cnf(c_583,plain,
% 7.78/1.50      ( v1_relat_1(sK1) = iProver_top ),
% 7.78/1.50      inference(predicate_to_equality,[status(thm)],[c_14]) ).
% 7.78/1.50  
% 7.78/1.50  cnf(c_15,negated_conjecture,
% 7.78/1.50      ( v1_relat_1(sK0) ),
% 7.78/1.50      inference(cnf_transformation,[],[f47]) ).
% 7.78/1.50  
% 7.78/1.50  cnf(c_582,plain,
% 7.78/1.50      ( v1_relat_1(sK0) = iProver_top ),
% 7.78/1.50      inference(predicate_to_equality,[status(thm)],[c_15]) ).
% 7.78/1.50  
% 7.78/1.50  cnf(c_11,plain,
% 7.78/1.50      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
% 7.78/1.50      | ~ v1_relat_1(X1)
% 7.78/1.50      | v1_relat_1(X0) ),
% 7.78/1.50      inference(cnf_transformation,[],[f45]) ).
% 7.78/1.50  
% 7.78/1.50  cnf(c_9,plain,
% 7.78/1.50      ( m1_subset_1(X0,k1_zfmisc_1(X1)) | ~ r1_tarski(X0,X1) ),
% 7.78/1.50      inference(cnf_transformation,[],[f44]) ).
% 7.78/1.50  
% 7.78/1.50  cnf(c_97,plain,
% 7.78/1.50      ( ~ r1_tarski(X0,X1) | m1_subset_1(X0,k1_zfmisc_1(X1)) ),
% 7.78/1.50      inference(prop_impl,[status(thm)],[c_9]) ).
% 7.78/1.50  
% 7.78/1.50  cnf(c_98,plain,
% 7.78/1.50      ( m1_subset_1(X0,k1_zfmisc_1(X1)) | ~ r1_tarski(X0,X1) ),
% 7.78/1.50      inference(renaming,[status(thm)],[c_97]) ).
% 7.78/1.50  
% 7.78/1.50  cnf(c_122,plain,
% 7.78/1.50      ( ~ r1_tarski(X0,X1) | ~ v1_relat_1(X1) | v1_relat_1(X0) ),
% 7.78/1.50      inference(bin_hyper_res,[status(thm)],[c_11,c_98]) ).
% 7.78/1.50  
% 7.78/1.50  cnf(c_581,plain,
% 7.78/1.50      ( r1_tarski(X0,X1) != iProver_top
% 7.78/1.50      | v1_relat_1(X1) != iProver_top
% 7.78/1.50      | v1_relat_1(X0) = iProver_top ),
% 7.78/1.50      inference(predicate_to_equality,[status(thm)],[c_122]) ).
% 7.78/1.50  
% 7.78/1.50  cnf(c_1055,plain,
% 7.78/1.50      ( v1_relat_1(X0) != iProver_top
% 7.78/1.50      | v1_relat_1(k4_xboole_0(X0,X1)) = iProver_top ),
% 7.78/1.50      inference(superposition,[status(thm)],[c_588,c_581]) ).
% 7.78/1.50  
% 7.78/1.50  cnf(c_12,plain,
% 7.78/1.50      ( ~ v1_relat_1(X0)
% 7.78/1.50      | ~ v1_relat_1(X1)
% 7.78/1.50      | k3_tarski(k2_enumset1(k1_relat_1(X0),k1_relat_1(X0),k1_relat_1(X0),k1_relat_1(X1))) = k1_relat_1(k3_tarski(k2_enumset1(X0,X0,X0,X1))) ),
% 7.78/1.50      inference(cnf_transformation,[],[f57]) ).
% 7.78/1.50  
% 7.78/1.50  cnf(c_585,plain,
% 7.78/1.50      ( k3_tarski(k2_enumset1(k1_relat_1(X0),k1_relat_1(X0),k1_relat_1(X0),k1_relat_1(X1))) = k1_relat_1(k3_tarski(k2_enumset1(X0,X0,X0,X1)))
% 7.78/1.50      | v1_relat_1(X0) != iProver_top
% 7.78/1.50      | v1_relat_1(X1) != iProver_top ),
% 7.78/1.50      inference(predicate_to_equality,[status(thm)],[c_12]) ).
% 7.78/1.50  
% 7.78/1.50  cnf(c_2201,plain,
% 7.78/1.50      ( k3_tarski(k2_enumset1(k1_relat_1(k4_xboole_0(X0,X1)),k1_relat_1(k4_xboole_0(X0,X1)),k1_relat_1(k4_xboole_0(X0,X1)),k1_relat_1(X2))) = k1_relat_1(k3_tarski(k2_enumset1(k4_xboole_0(X0,X1),k4_xboole_0(X0,X1),k4_xboole_0(X0,X1),X2)))
% 7.78/1.50      | v1_relat_1(X0) != iProver_top
% 7.78/1.50      | v1_relat_1(X2) != iProver_top ),
% 7.78/1.50      inference(superposition,[status(thm)],[c_1055,c_585]) ).
% 7.78/1.50  
% 7.78/1.50  cnf(c_18385,plain,
% 7.78/1.50      ( k3_tarski(k2_enumset1(k1_relat_1(k4_xboole_0(sK0,X0)),k1_relat_1(k4_xboole_0(sK0,X0)),k1_relat_1(k4_xboole_0(sK0,X0)),k1_relat_1(X1))) = k1_relat_1(k3_tarski(k2_enumset1(k4_xboole_0(sK0,X0),k4_xboole_0(sK0,X0),k4_xboole_0(sK0,X0),X1)))
% 7.78/1.50      | v1_relat_1(X1) != iProver_top ),
% 7.78/1.50      inference(superposition,[status(thm)],[c_582,c_2201]) ).
% 7.78/1.50  
% 7.78/1.50  cnf(c_19675,plain,
% 7.78/1.50      ( k3_tarski(k2_enumset1(k1_relat_1(k4_xboole_0(sK0,X0)),k1_relat_1(k4_xboole_0(sK0,X0)),k1_relat_1(k4_xboole_0(sK0,X0)),k1_relat_1(sK1))) = k1_relat_1(k3_tarski(k2_enumset1(k4_xboole_0(sK0,X0),k4_xboole_0(sK0,X0),k4_xboole_0(sK0,X0),sK1))) ),
% 7.78/1.50      inference(superposition,[status(thm)],[c_583,c_18385]) ).
% 7.78/1.50  
% 7.78/1.50  cnf(c_3,plain,
% 7.78/1.50      ( r1_tarski(X0,X0) ),
% 7.78/1.50      inference(cnf_transformation,[],[f60]) ).
% 7.78/1.50  
% 7.78/1.50  cnf(c_592,plain,
% 7.78/1.50      ( r1_tarski(X0,X0) = iProver_top ),
% 7.78/1.50      inference(predicate_to_equality,[status(thm)],[c_3]) ).
% 7.78/1.50  
% 7.78/1.50  cnf(c_4,plain,
% 7.78/1.50      ( r1_tarski(X0,X1)
% 7.78/1.50      | ~ r1_tarski(k3_tarski(k2_enumset1(X0,X0,X0,X2)),X1) ),
% 7.78/1.50      inference(cnf_transformation,[],[f53]) ).
% 7.78/1.50  
% 7.78/1.50  cnf(c_591,plain,
% 7.78/1.50      ( r1_tarski(X0,X1) = iProver_top
% 7.78/1.50      | r1_tarski(k3_tarski(k2_enumset1(X0,X0,X0,X2)),X1) != iProver_top ),
% 7.78/1.50      inference(predicate_to_equality,[status(thm)],[c_4]) ).
% 7.78/1.50  
% 7.78/1.50  cnf(c_1799,plain,
% 7.78/1.50      ( r1_tarski(X0,k3_tarski(k2_enumset1(X0,X0,X0,X1))) = iProver_top ),
% 7.78/1.50      inference(superposition,[status(thm)],[c_592,c_591]) ).
% 7.78/1.50  
% 7.78/1.50  cnf(c_19981,plain,
% 7.78/1.50      ( r1_tarski(k1_relat_1(k4_xboole_0(sK0,X0)),k1_relat_1(k3_tarski(k2_enumset1(k4_xboole_0(sK0,X0),k4_xboole_0(sK0,X0),k4_xboole_0(sK0,X0),sK1)))) = iProver_top ),
% 7.78/1.50      inference(superposition,[status(thm)],[c_19675,c_1799]) ).
% 7.78/1.50  
% 7.78/1.50  cnf(c_20683,plain,
% 7.78/1.50      ( r1_tarski(k1_relat_1(k4_xboole_0(sK0,k4_xboole_0(sK0,sK1))),k1_relat_1(sK1)) = iProver_top ),
% 7.78/1.50      inference(superposition,[status(thm)],[c_1337,c_19981]) ).
% 7.78/1.50  
% 7.78/1.50  cnf(c_18384,plain,
% 7.78/1.50      ( k3_tarski(k2_enumset1(k1_relat_1(k4_xboole_0(sK1,X0)),k1_relat_1(k4_xboole_0(sK1,X0)),k1_relat_1(k4_xboole_0(sK1,X0)),k1_relat_1(X1))) = k1_relat_1(k3_tarski(k2_enumset1(k4_xboole_0(sK1,X0),k4_xboole_0(sK1,X0),k4_xboole_0(sK1,X0),X1)))
% 7.78/1.50      | v1_relat_1(X1) != iProver_top ),
% 7.78/1.50      inference(superposition,[status(thm)],[c_583,c_2201]) ).
% 7.78/1.50  
% 7.78/1.50  cnf(c_19256,plain,
% 7.78/1.50      ( k3_tarski(k2_enumset1(k1_relat_1(k4_xboole_0(sK1,X0)),k1_relat_1(k4_xboole_0(sK1,X0)),k1_relat_1(k4_xboole_0(sK1,X0)),k1_relat_1(sK0))) = k1_relat_1(k3_tarski(k2_enumset1(k4_xboole_0(sK1,X0),k4_xboole_0(sK1,X0),k4_xboole_0(sK1,X0),sK0))) ),
% 7.78/1.50      inference(superposition,[status(thm)],[c_582,c_18384]) ).
% 7.78/1.50  
% 7.78/1.50  cnf(c_19643,plain,
% 7.78/1.50      ( r1_tarski(k1_relat_1(k4_xboole_0(sK1,X0)),k1_relat_1(k3_tarski(k2_enumset1(k4_xboole_0(sK1,X0),k4_xboole_0(sK1,X0),k4_xboole_0(sK1,X0),sK0)))) = iProver_top ),
% 7.78/1.50      inference(superposition,[status(thm)],[c_19256,c_1799]) ).
% 7.78/1.50  
% 7.78/1.50  cnf(c_20305,plain,
% 7.78/1.50      ( r1_tarski(k1_relat_1(k4_xboole_0(sK1,k4_xboole_0(sK1,sK0))),k1_relat_1(sK0)) = iProver_top ),
% 7.78/1.50      inference(superposition,[status(thm)],[c_1337,c_19643]) ).
% 7.78/1.50  
% 7.78/1.50  cnf(c_258,plain,
% 7.78/1.50      ( ~ r1_tarski(X0,X1) | r1_tarski(X2,X3) | X2 != X0 | X3 != X1 ),
% 7.78/1.50      theory(equality) ).
% 7.78/1.50  
% 7.78/1.50  cnf(c_803,plain,
% 7.78/1.50      ( ~ r1_tarski(X0,X1)
% 7.78/1.50      | r1_tarski(k1_relat_1(k4_xboole_0(sK0,k4_xboole_0(sK0,sK1))),k1_relat_1(sK0))
% 7.78/1.50      | k1_relat_1(k4_xboole_0(sK0,k4_xboole_0(sK0,sK1))) != X0
% 7.78/1.50      | k1_relat_1(sK0) != X1 ),
% 7.78/1.50      inference(instantiation,[status(thm)],[c_258]) ).
% 7.78/1.50  
% 7.78/1.50  cnf(c_1026,plain,
% 7.78/1.50      ( ~ r1_tarski(X0,k1_relat_1(sK0))
% 7.78/1.50      | r1_tarski(k1_relat_1(k4_xboole_0(sK0,k4_xboole_0(sK0,sK1))),k1_relat_1(sK0))
% 7.78/1.50      | k1_relat_1(k4_xboole_0(sK0,k4_xboole_0(sK0,sK1))) != X0
% 7.78/1.50      | k1_relat_1(sK0) != k1_relat_1(sK0) ),
% 7.78/1.50      inference(instantiation,[status(thm)],[c_803]) ).
% 7.78/1.50  
% 7.78/1.50  cnf(c_1328,plain,
% 7.78/1.50      ( ~ r1_tarski(k1_relat_1(k4_xboole_0(sK1,k4_xboole_0(sK1,sK0))),k1_relat_1(sK0))
% 7.78/1.50      | r1_tarski(k1_relat_1(k4_xboole_0(sK0,k4_xboole_0(sK0,sK1))),k1_relat_1(sK0))
% 7.78/1.50      | k1_relat_1(k4_xboole_0(sK0,k4_xboole_0(sK0,sK1))) != k1_relat_1(k4_xboole_0(sK1,k4_xboole_0(sK1,sK0)))
% 7.78/1.50      | k1_relat_1(sK0) != k1_relat_1(sK0) ),
% 7.78/1.50      inference(instantiation,[status(thm)],[c_1026]) ).
% 7.78/1.50  
% 7.78/1.50  cnf(c_1329,plain,
% 7.78/1.50      ( k1_relat_1(k4_xboole_0(sK0,k4_xboole_0(sK0,sK1))) != k1_relat_1(k4_xboole_0(sK1,k4_xboole_0(sK1,sK0)))
% 7.78/1.50      | k1_relat_1(sK0) != k1_relat_1(sK0)
% 7.78/1.50      | r1_tarski(k1_relat_1(k4_xboole_0(sK1,k4_xboole_0(sK1,sK0))),k1_relat_1(sK0)) != iProver_top
% 7.78/1.50      | r1_tarski(k1_relat_1(k4_xboole_0(sK0,k4_xboole_0(sK0,sK1))),k1_relat_1(sK0)) = iProver_top ),
% 7.78/1.50      inference(predicate_to_equality,[status(thm)],[c_1328]) ).
% 7.78/1.50  
% 7.78/1.50  cnf(c_6,plain,
% 7.78/1.50      ( ~ r1_tarski(X0,X1)
% 7.78/1.50      | ~ r1_tarski(X0,X2)
% 7.78/1.50      | r1_tarski(X0,k4_xboole_0(X1,k4_xboole_0(X1,X2))) ),
% 7.78/1.50      inference(cnf_transformation,[],[f55]) ).
% 7.78/1.50  
% 7.78/1.50  cnf(c_1206,plain,
% 7.78/1.50      ( r1_tarski(k1_relat_1(k4_xboole_0(sK0,k4_xboole_0(sK0,sK1))),k4_xboole_0(k1_relat_1(sK1),k4_xboole_0(k1_relat_1(sK1),k1_relat_1(sK0))))
% 7.78/1.50      | ~ r1_tarski(k1_relat_1(k4_xboole_0(sK0,k4_xboole_0(sK0,sK1))),k1_relat_1(sK1))
% 7.78/1.50      | ~ r1_tarski(k1_relat_1(k4_xboole_0(sK0,k4_xboole_0(sK0,sK1))),k1_relat_1(sK0)) ),
% 7.78/1.50      inference(instantiation,[status(thm)],[c_6]) ).
% 7.78/1.50  
% 7.78/1.50  cnf(c_1207,plain,
% 7.78/1.50      ( r1_tarski(k1_relat_1(k4_xboole_0(sK0,k4_xboole_0(sK0,sK1))),k4_xboole_0(k1_relat_1(sK1),k4_xboole_0(k1_relat_1(sK1),k1_relat_1(sK0)))) = iProver_top
% 7.78/1.50      | r1_tarski(k1_relat_1(k4_xboole_0(sK0,k4_xboole_0(sK0,sK1))),k1_relat_1(sK1)) != iProver_top
% 7.78/1.50      | r1_tarski(k1_relat_1(k4_xboole_0(sK0,k4_xboole_0(sK0,sK1))),k1_relat_1(sK0)) != iProver_top ),
% 7.78/1.50      inference(predicate_to_equality,[status(thm)],[c_1206]) ).
% 7.78/1.50  
% 7.78/1.50  cnf(c_962,plain,
% 7.78/1.50      ( k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)) = k4_xboole_0(sK1,k4_xboole_0(sK1,sK0)) ),
% 7.78/1.50      inference(instantiation,[status(thm)],[c_0]) ).
% 7.78/1.50  
% 7.78/1.50  cnf(c_264,plain,
% 7.78/1.50      ( X0 != X1 | k1_relat_1(X0) = k1_relat_1(X1) ),
% 7.78/1.50      theory(equality) ).
% 7.78/1.50  
% 7.78/1.50  cnf(c_847,plain,
% 7.78/1.50      ( k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)) != X0
% 7.78/1.50      | k1_relat_1(k4_xboole_0(sK0,k4_xboole_0(sK0,sK1))) = k1_relat_1(X0) ),
% 7.78/1.50      inference(instantiation,[status(thm)],[c_264]) ).
% 7.78/1.50  
% 7.78/1.50  cnf(c_961,plain,
% 7.78/1.50      ( k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)) != k4_xboole_0(sK1,k4_xboole_0(sK1,sK0))
% 7.78/1.50      | k1_relat_1(k4_xboole_0(sK0,k4_xboole_0(sK0,sK1))) = k1_relat_1(k4_xboole_0(sK1,k4_xboole_0(sK1,sK0))) ),
% 7.78/1.50      inference(instantiation,[status(thm)],[c_847]) ).
% 7.78/1.50  
% 7.78/1.50  cnf(c_944,plain,
% 7.78/1.50      ( k4_xboole_0(k1_relat_1(sK0),k4_xboole_0(k1_relat_1(sK0),k1_relat_1(sK1))) = k4_xboole_0(k1_relat_1(sK1),k4_xboole_0(k1_relat_1(sK1),k1_relat_1(sK0))) ),
% 7.78/1.50      inference(instantiation,[status(thm)],[c_0]) ).
% 7.78/1.50  
% 7.78/1.50  cnf(c_740,plain,
% 7.78/1.50      ( ~ r1_tarski(X0,X1)
% 7.78/1.50      | r1_tarski(k1_relat_1(k4_xboole_0(sK0,k4_xboole_0(sK0,sK1))),k4_xboole_0(k1_relat_1(sK0),k4_xboole_0(k1_relat_1(sK0),k1_relat_1(sK1))))
% 7.78/1.50      | k4_xboole_0(k1_relat_1(sK0),k4_xboole_0(k1_relat_1(sK0),k1_relat_1(sK1))) != X1
% 7.78/1.50      | k1_relat_1(k4_xboole_0(sK0,k4_xboole_0(sK0,sK1))) != X0 ),
% 7.78/1.50      inference(instantiation,[status(thm)],[c_258]) ).
% 7.78/1.50  
% 7.78/1.50  cnf(c_839,plain,
% 7.78/1.50      ( ~ r1_tarski(k1_relat_1(k4_xboole_0(sK0,k4_xboole_0(sK0,sK1))),X0)
% 7.78/1.50      | r1_tarski(k1_relat_1(k4_xboole_0(sK0,k4_xboole_0(sK0,sK1))),k4_xboole_0(k1_relat_1(sK0),k4_xboole_0(k1_relat_1(sK0),k1_relat_1(sK1))))
% 7.78/1.50      | k4_xboole_0(k1_relat_1(sK0),k4_xboole_0(k1_relat_1(sK0),k1_relat_1(sK1))) != X0
% 7.78/1.50      | k1_relat_1(k4_xboole_0(sK0,k4_xboole_0(sK0,sK1))) != k1_relat_1(k4_xboole_0(sK0,k4_xboole_0(sK0,sK1))) ),
% 7.78/1.50      inference(instantiation,[status(thm)],[c_740]) ).
% 7.78/1.50  
% 7.78/1.50  cnf(c_943,plain,
% 7.78/1.50      ( ~ r1_tarski(k1_relat_1(k4_xboole_0(sK0,k4_xboole_0(sK0,sK1))),k4_xboole_0(k1_relat_1(sK1),k4_xboole_0(k1_relat_1(sK1),k1_relat_1(sK0))))
% 7.78/1.50      | r1_tarski(k1_relat_1(k4_xboole_0(sK0,k4_xboole_0(sK0,sK1))),k4_xboole_0(k1_relat_1(sK0),k4_xboole_0(k1_relat_1(sK0),k1_relat_1(sK1))))
% 7.78/1.50      | k4_xboole_0(k1_relat_1(sK0),k4_xboole_0(k1_relat_1(sK0),k1_relat_1(sK1))) != k4_xboole_0(k1_relat_1(sK1),k4_xboole_0(k1_relat_1(sK1),k1_relat_1(sK0)))
% 7.78/1.50      | k1_relat_1(k4_xboole_0(sK0,k4_xboole_0(sK0,sK1))) != k1_relat_1(k4_xboole_0(sK0,k4_xboole_0(sK0,sK1))) ),
% 7.78/1.50      inference(instantiation,[status(thm)],[c_839]) ).
% 7.78/1.50  
% 7.78/1.50  cnf(c_945,plain,
% 7.78/1.50      ( k4_xboole_0(k1_relat_1(sK0),k4_xboole_0(k1_relat_1(sK0),k1_relat_1(sK1))) != k4_xboole_0(k1_relat_1(sK1),k4_xboole_0(k1_relat_1(sK1),k1_relat_1(sK0)))
% 7.78/1.50      | k1_relat_1(k4_xboole_0(sK0,k4_xboole_0(sK0,sK1))) != k1_relat_1(k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)))
% 7.78/1.50      | r1_tarski(k1_relat_1(k4_xboole_0(sK0,k4_xboole_0(sK0,sK1))),k4_xboole_0(k1_relat_1(sK1),k4_xboole_0(k1_relat_1(sK1),k1_relat_1(sK0)))) != iProver_top
% 7.78/1.50      | r1_tarski(k1_relat_1(k4_xboole_0(sK0,k4_xboole_0(sK0,sK1))),k4_xboole_0(k1_relat_1(sK0),k4_xboole_0(k1_relat_1(sK0),k1_relat_1(sK1)))) = iProver_top ),
% 7.78/1.50      inference(predicate_to_equality,[status(thm)],[c_943]) ).
% 7.78/1.50  
% 7.78/1.50  cnf(c_255,plain,( X0 = X0 ),theory(equality) ).
% 7.78/1.50  
% 7.78/1.50  cnf(c_840,plain,
% 7.78/1.50      ( k1_relat_1(k4_xboole_0(sK0,k4_xboole_0(sK0,sK1))) = k1_relat_1(k4_xboole_0(sK0,k4_xboole_0(sK0,sK1))) ),
% 7.78/1.50      inference(instantiation,[status(thm)],[c_255]) ).
% 7.78/1.50  
% 7.78/1.50  cnf(c_272,plain,
% 7.78/1.50      ( k1_relat_1(sK0) = k1_relat_1(sK0) | sK0 != sK0 ),
% 7.78/1.50      inference(instantiation,[status(thm)],[c_264]) ).
% 7.78/1.50  
% 7.78/1.50  cnf(c_1,plain,
% 7.78/1.50      ( ~ r1_tarski(X0,X1) | ~ r1_tarski(X1,X0) | X0 = X1 ),
% 7.78/1.50      inference(cnf_transformation,[],[f33]) ).
% 7.78/1.50  
% 7.78/1.50  cnf(c_47,plain,
% 7.78/1.50      ( ~ r1_tarski(sK0,sK0) | sK0 = sK0 ),
% 7.78/1.50      inference(instantiation,[status(thm)],[c_1]) ).
% 7.78/1.50  
% 7.78/1.50  cnf(c_43,plain,
% 7.78/1.50      ( r1_tarski(sK0,sK0) ),
% 7.78/1.50      inference(instantiation,[status(thm)],[c_3]) ).
% 7.78/1.50  
% 7.78/1.50  cnf(c_13,negated_conjecture,
% 7.78/1.50      ( ~ r1_tarski(k1_relat_1(k4_xboole_0(sK0,k4_xboole_0(sK0,sK1))),k4_xboole_0(k1_relat_1(sK0),k4_xboole_0(k1_relat_1(sK0),k1_relat_1(sK1)))) ),
% 7.78/1.50      inference(cnf_transformation,[],[f58]) ).
% 7.78/1.50  
% 7.78/1.50  cnf(c_18,plain,
% 7.78/1.50      ( r1_tarski(k1_relat_1(k4_xboole_0(sK0,k4_xboole_0(sK0,sK1))),k4_xboole_0(k1_relat_1(sK0),k4_xboole_0(k1_relat_1(sK0),k1_relat_1(sK1)))) != iProver_top ),
% 7.78/1.50      inference(predicate_to_equality,[status(thm)],[c_13]) ).
% 7.78/1.50  
% 7.78/1.50  cnf(contradiction,plain,
% 7.78/1.50      ( $false ),
% 7.78/1.50      inference(minisat,
% 7.78/1.50                [status(thm)],
% 7.78/1.50                [c_20683,c_20305,c_1329,c_1207,c_962,c_961,c_944,c_945,
% 7.78/1.50                 c_840,c_272,c_47,c_43,c_18]) ).
% 7.78/1.50  
% 7.78/1.50  
% 7.78/1.50  % SZS output end CNFRefutation for theBenchmark.p
% 7.78/1.50  
% 7.78/1.50  ------                               Statistics
% 7.78/1.50  
% 7.78/1.50  ------ Selected
% 7.78/1.50  
% 7.78/1.50  total_time:                             0.636
% 7.78/1.50  
%------------------------------------------------------------------------------
