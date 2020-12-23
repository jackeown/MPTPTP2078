%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n024.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 11:54:54 EST 2020

% Result     : Theorem 27.72s
% Output     : CNFRefutation 27.72s
% Verified   : 
% Statistics : Number of formulae       :  190 (6439 expanded)
%              Number of clauses        :  136 (1744 expanded)
%              Number of leaves         :   17 (1953 expanded)
%              Depth                    :   32
%              Number of atoms          :  290 (8171 expanded)
%              Number of equality atoms :  175 (5988 expanded)
%              Maximal formula depth    :    7 (   2 average)
%              Maximal clause size      :    5 (   1 average)
%              Maximal term depth       :    9 (   3 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f8,axiom,(
    ! [X0,X1] : k2_tarski(X0,X1) = k2_tarski(X1,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f39,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k2_tarski(X1,X0) ),
    inference(cnf_transformation,[],[f8])).

fof(f9,axiom,(
    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f40,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1) ),
    inference(cnf_transformation,[],[f9])).

fof(f57,plain,(
    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k1_enumset1(X1,X1,X0) ),
    inference(definition_unfolding,[],[f39,f40,f40])).

fof(f2,axiom,(
    ! [X0] : k2_xboole_0(X0,k1_xboole_0) = X0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f33,plain,(
    ! [X0] : k2_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(cnf_transformation,[],[f2])).

fof(f7,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k5_xboole_0(X0,k4_xboole_0(X1,X0)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f38,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k5_xboole_0(X0,k4_xboole_0(X1,X0)) ),
    inference(cnf_transformation,[],[f7])).

fof(f53,plain,(
    ! [X0] : k5_xboole_0(X0,k4_xboole_0(k1_xboole_0,X0)) = X0 ),
    inference(definition_unfolding,[],[f33,f38])).

fof(f10,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f41,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1)) ),
    inference(cnf_transformation,[],[f10])).

fof(f58,plain,(
    ! [X0,X1] : k5_xboole_0(X0,k4_xboole_0(X1,X0)) = k3_tarski(k1_enumset1(X0,X0,X1)) ),
    inference(definition_unfolding,[],[f41,f38,f40])).

fof(f4,axiom,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k4_xboole_0(k2_xboole_0(X0,X1),X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f35,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k4_xboole_0(k2_xboole_0(X0,X1),X1) ),
    inference(cnf_transformation,[],[f4])).

fof(f54,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k4_xboole_0(k5_xboole_0(X0,k4_xboole_0(X1,X0)),X1) ),
    inference(definition_unfolding,[],[f35,f38])).

fof(f13,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ( v5_relat_1(X1,X0)
      <=> r1_tarski(k2_relat_1(X1),X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f22,plain,(
    ! [X0,X1] :
      ( ( v5_relat_1(X1,X0)
      <=> r1_tarski(k2_relat_1(X1),X0) )
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f28,plain,(
    ! [X0,X1] :
      ( ( ( v5_relat_1(X1,X0)
          | ~ r1_tarski(k2_relat_1(X1),X0) )
        & ( r1_tarski(k2_relat_1(X1),X0)
          | ~ v5_relat_1(X1,X0) ) )
      | ~ v1_relat_1(X1) ) ),
    inference(nnf_transformation,[],[f22])).

fof(f45,plain,(
    ! [X0,X1] :
      ( r1_tarski(k2_relat_1(X1),X0)
      | ~ v5_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f16,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => ( v5_relat_1(X2,X1)
        & v4_relat_1(X2,X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f24,plain,(
    ! [X0,X1,X2] :
      ( ( v5_relat_1(X2,X1)
        & v4_relat_1(X2,X0) )
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f16])).

fof(f50,plain,(
    ! [X2,X0,X1] :
      ( v5_relat_1(X2,X1)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f17,conjecture,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => r1_tarski(k3_relat_1(X2),k2_xboole_0(X0,X1)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f18,negated_conjecture,(
    ~ ! [X0,X1,X2] :
        ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
       => r1_tarski(k3_relat_1(X2),k2_xboole_0(X0,X1)) ) ),
    inference(negated_conjecture,[],[f17])).

fof(f25,plain,(
    ? [X0,X1,X2] :
      ( ~ r1_tarski(k3_relat_1(X2),k2_xboole_0(X0,X1))
      & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f18])).

fof(f29,plain,
    ( ? [X0,X1,X2] :
        ( ~ r1_tarski(k3_relat_1(X2),k2_xboole_0(X0,X1))
        & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) )
   => ( ~ r1_tarski(k3_relat_1(sK2),k2_xboole_0(sK0,sK1))
      & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ) ),
    introduced(choice_axiom,[])).

fof(f30,plain,
    ( ~ r1_tarski(k3_relat_1(sK2),k2_xboole_0(sK0,sK1))
    & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f25,f29])).

fof(f51,plain,(
    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ),
    inference(cnf_transformation,[],[f30])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,X1) = k1_xboole_0
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f26,plain,(
    ! [X0,X1] :
      ( ( k4_xboole_0(X0,X1) = k1_xboole_0
        | ~ r1_tarski(X0,X1) )
      & ( r1_tarski(X0,X1)
        | k4_xboole_0(X0,X1) != k1_xboole_0 ) ) ),
    inference(nnf_transformation,[],[f1])).

fof(f32,plain,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,X1) = k1_xboole_0
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f11,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(X0))
         => v1_relat_1(X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f20,plain,(
    ! [X0] :
      ( ! [X1] :
          ( v1_relat_1(X1)
          | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f42,plain,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f15,axiom,(
    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f48,plain,(
    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1)) ),
    inference(cnf_transformation,[],[f15])).

fof(f6,axiom,(
    ! [X0,X1,X2] : k2_xboole_0(X0,k2_xboole_0(X1,X2)) = k2_xboole_0(k2_xboole_0(X0,X1),X2) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f37,plain,(
    ! [X2,X0,X1] : k2_xboole_0(X0,k2_xboole_0(X1,X2)) = k2_xboole_0(k2_xboole_0(X0,X1),X2) ),
    inference(cnf_transformation,[],[f6])).

fof(f56,plain,(
    ! [X2,X0,X1] : k5_xboole_0(X0,k4_xboole_0(k5_xboole_0(X1,k4_xboole_0(X2,X1)),X0)) = k5_xboole_0(k5_xboole_0(X0,k4_xboole_0(X1,X0)),k4_xboole_0(X2,k5_xboole_0(X0,k4_xboole_0(X1,X0)))) ),
    inference(definition_unfolding,[],[f37,f38,f38,f38,f38])).

fof(f3,axiom,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f34,plain,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    inference(cnf_transformation,[],[f3])).

fof(f14,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => k2_xboole_0(k1_relat_1(X0),k2_relat_1(X0)) = k3_relat_1(X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f23,plain,(
    ! [X0] :
      ( k2_xboole_0(k1_relat_1(X0),k2_relat_1(X0)) = k3_relat_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f47,plain,(
    ! [X0] :
      ( k2_xboole_0(k1_relat_1(X0),k2_relat_1(X0)) = k3_relat_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f59,plain,(
    ! [X0] :
      ( k5_xboole_0(k1_relat_1(X0),k4_xboole_0(k2_relat_1(X0),k1_relat_1(X0))) = k3_relat_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(definition_unfolding,[],[f47,f38])).

fof(f31,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | k4_xboole_0(X0,X1) != k1_xboole_0 ) ),
    inference(cnf_transformation,[],[f26])).

fof(f12,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ( v4_relat_1(X1,X0)
      <=> r1_tarski(k1_relat_1(X1),X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f21,plain,(
    ! [X0,X1] :
      ( ( v4_relat_1(X1,X0)
      <=> r1_tarski(k1_relat_1(X1),X0) )
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f27,plain,(
    ! [X0,X1] :
      ( ( ( v4_relat_1(X1,X0)
          | ~ r1_tarski(k1_relat_1(X1),X0) )
        & ( r1_tarski(k1_relat_1(X1),X0)
          | ~ v4_relat_1(X1,X0) ) )
      | ~ v1_relat_1(X1) ) ),
    inference(nnf_transformation,[],[f21])).

fof(f43,plain,(
    ! [X0,X1] :
      ( r1_tarski(k1_relat_1(X1),X0)
      | ~ v4_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f49,plain,(
    ! [X2,X0,X1] :
      ( v4_relat_1(X2,X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f52,plain,(
    ~ r1_tarski(k3_relat_1(sK2),k2_xboole_0(sK0,sK1)) ),
    inference(cnf_transformation,[],[f30])).

fof(f60,plain,(
    ~ r1_tarski(k3_relat_1(sK2),k5_xboole_0(sK0,k4_xboole_0(sK1,sK0))) ),
    inference(definition_unfolding,[],[f52,f38])).

cnf(c_7,plain,
    ( k1_enumset1(X0,X0,X1) = k1_enumset1(X1,X1,X0) ),
    inference(cnf_transformation,[],[f57])).

cnf(c_2,plain,
    ( k5_xboole_0(X0,k4_xboole_0(k1_xboole_0,X0)) = X0 ),
    inference(cnf_transformation,[],[f53])).

cnf(c_8,plain,
    ( k3_tarski(k1_enumset1(X0,X0,X1)) = k5_xboole_0(X0,k4_xboole_0(X1,X0)) ),
    inference(cnf_transformation,[],[f58])).

cnf(c_1158,plain,
    ( k3_tarski(k1_enumset1(X0,X0,k1_xboole_0)) = X0 ),
    inference(superposition,[status(thm)],[c_2,c_8])).

cnf(c_1244,plain,
    ( k3_tarski(k1_enumset1(k1_xboole_0,k1_xboole_0,X0)) = X0 ),
    inference(superposition,[status(thm)],[c_7,c_1158])).

cnf(c_4,plain,
    ( k4_xboole_0(k5_xboole_0(X0,k4_xboole_0(X1,X0)),X1) = k4_xboole_0(X0,X1) ),
    inference(cnf_transformation,[],[f54])).

cnf(c_747,plain,
    ( k4_xboole_0(k3_tarski(k1_enumset1(X0,X0,X1)),X1) = k4_xboole_0(X0,X1) ),
    inference(light_normalisation,[status(thm)],[c_4,c_8])).

cnf(c_1350,plain,
    ( k4_xboole_0(X0,X0) = k4_xboole_0(k1_xboole_0,X0) ),
    inference(superposition,[status(thm)],[c_1244,c_747])).

cnf(c_1423,plain,
    ( k3_tarski(k1_enumset1(X0,X0,X0)) = k5_xboole_0(X0,k4_xboole_0(k1_xboole_0,X0)) ),
    inference(superposition,[status(thm)],[c_1350,c_8])).

cnf(c_1430,plain,
    ( k3_tarski(k1_enumset1(X0,X0,X0)) = X0 ),
    inference(light_normalisation,[status(thm)],[c_1423,c_2])).

cnf(c_13,plain,
    ( ~ v5_relat_1(X0,X1)
    | r1_tarski(k2_relat_1(X0),X1)
    | ~ v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f45])).

cnf(c_16,plain,
    ( v5_relat_1(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) ),
    inference(cnf_transformation,[],[f50])).

cnf(c_19,negated_conjecture,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ),
    inference(cnf_transformation,[],[f51])).

cnf(c_236,plain,
    ( v5_relat_1(X0,X1)
    | k1_zfmisc_1(k2_zfmisc_1(X2,X1)) != k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))
    | sK2 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_16,c_19])).

cnf(c_237,plain,
    ( v5_relat_1(sK2,X0)
    | k1_zfmisc_1(k2_zfmisc_1(X1,X0)) != k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)) ),
    inference(unflattening,[status(thm)],[c_236])).

cnf(c_291,plain,
    ( r1_tarski(k2_relat_1(X0),X1)
    | ~ v1_relat_1(X0)
    | X2 != X1
    | k1_zfmisc_1(k2_zfmisc_1(X3,X2)) != k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))
    | sK2 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_13,c_237])).

cnf(c_292,plain,
    ( r1_tarski(k2_relat_1(sK2),X0)
    | ~ v1_relat_1(sK2)
    | k1_zfmisc_1(k2_zfmisc_1(X1,X0)) != k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)) ),
    inference(unflattening,[status(thm)],[c_291])).

cnf(c_722,plain,
    ( k1_zfmisc_1(k2_zfmisc_1(X0,X1)) != k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))
    | r1_tarski(k2_relat_1(sK2),X1) = iProver_top
    | v1_relat_1(sK2) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_292])).

cnf(c_897,plain,
    ( r1_tarski(k2_relat_1(sK2),sK1) = iProver_top
    | v1_relat_1(sK2) != iProver_top ),
    inference(equality_resolution,[status(thm)],[c_722])).

cnf(c_0,plain,
    ( ~ r1_tarski(X0,X1)
    | k4_xboole_0(X0,X1) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f32])).

cnf(c_731,plain,
    ( k4_xboole_0(X0,X1) = k1_xboole_0
    | r1_tarski(X0,X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_0])).

cnf(c_1643,plain,
    ( k4_xboole_0(k2_relat_1(sK2),sK1) = k1_xboole_0
    | v1_relat_1(sK2) != iProver_top ),
    inference(superposition,[status(thm)],[c_897,c_731])).

cnf(c_9,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | ~ v1_relat_1(X1)
    | v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f42])).

cnf(c_221,plain,
    ( ~ v1_relat_1(X0)
    | v1_relat_1(X1)
    | k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)) != k1_zfmisc_1(X0)
    | sK2 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_9,c_19])).

cnf(c_222,plain,
    ( ~ v1_relat_1(X0)
    | v1_relat_1(sK2)
    | k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)) != k1_zfmisc_1(X0) ),
    inference(unflattening,[status(thm)],[c_221])).

cnf(c_724,plain,
    ( k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)) != k1_zfmisc_1(X0)
    | v1_relat_1(X0) != iProver_top
    | v1_relat_1(sK2) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_222])).

cnf(c_852,plain,
    ( v1_relat_1(k2_zfmisc_1(sK0,sK1)) != iProver_top
    | v1_relat_1(sK2) = iProver_top ),
    inference(equality_resolution,[status(thm)],[c_724])).

cnf(c_15,plain,
    ( v1_relat_1(k2_zfmisc_1(X0,X1)) ),
    inference(cnf_transformation,[],[f48])).

cnf(c_1063,plain,
    ( v1_relat_1(k2_zfmisc_1(sK0,sK1)) ),
    inference(instantiation,[status(thm)],[c_15])).

cnf(c_1064,plain,
    ( v1_relat_1(k2_zfmisc_1(sK0,sK1)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1063])).

cnf(c_2203,plain,
    ( k4_xboole_0(k2_relat_1(sK2),sK1) = k1_xboole_0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_1643,c_852,c_1064])).

cnf(c_2207,plain,
    ( k3_tarski(k1_enumset1(sK1,sK1,k2_relat_1(sK2))) = k5_xboole_0(sK1,k1_xboole_0) ),
    inference(superposition,[status(thm)],[c_2203,c_8])).

cnf(c_6,plain,
    ( k5_xboole_0(k5_xboole_0(X0,k4_xboole_0(X1,X0)),k4_xboole_0(X2,k5_xboole_0(X0,k4_xboole_0(X1,X0)))) = k5_xboole_0(X0,k4_xboole_0(k5_xboole_0(X1,k4_xboole_0(X2,X1)),X0)) ),
    inference(cnf_transformation,[],[f56])).

cnf(c_786,plain,
    ( k5_xboole_0(k3_tarski(k1_enumset1(X0,X0,X1)),k4_xboole_0(X2,k3_tarski(k1_enumset1(X0,X0,X1)))) = k5_xboole_0(X0,k4_xboole_0(k5_xboole_0(X1,k4_xboole_0(X2,X1)),X0)) ),
    inference(light_normalisation,[status(thm)],[c_6,c_8])).

cnf(c_787,plain,
    ( k5_xboole_0(k3_tarski(k1_enumset1(X0,X0,X1)),k4_xboole_0(X2,k3_tarski(k1_enumset1(X0,X0,X1)))) = k3_tarski(k1_enumset1(X0,X0,k3_tarski(k1_enumset1(X1,X1,X2)))) ),
    inference(demodulation,[status(thm)],[c_786,c_8])).

cnf(c_2681,plain,
    ( k3_tarski(k1_enumset1(sK1,sK1,k3_tarski(k1_enumset1(k2_relat_1(sK2),k2_relat_1(sK2),X0)))) = k5_xboole_0(k5_xboole_0(sK1,k1_xboole_0),k4_xboole_0(X0,k5_xboole_0(sK1,k1_xboole_0))) ),
    inference(superposition,[status(thm)],[c_2207,c_787])).

cnf(c_2696,plain,
    ( k3_tarski(k1_enumset1(sK1,sK1,k3_tarski(k1_enumset1(k2_relat_1(sK2),k2_relat_1(sK2),X0)))) = k3_tarski(k1_enumset1(k5_xboole_0(sK1,k1_xboole_0),k5_xboole_0(sK1,k1_xboole_0),X0)) ),
    inference(demodulation,[status(thm)],[c_2681,c_8])).

cnf(c_2920,plain,
    ( k3_tarski(k1_enumset1(k5_xboole_0(sK1,k1_xboole_0),k5_xboole_0(sK1,k1_xboole_0),k2_relat_1(sK2))) = k3_tarski(k1_enumset1(sK1,sK1,k2_relat_1(sK2))) ),
    inference(superposition,[status(thm)],[c_1430,c_2696])).

cnf(c_2962,plain,
    ( k3_tarski(k1_enumset1(k5_xboole_0(sK1,k1_xboole_0),k5_xboole_0(sK1,k1_xboole_0),k2_relat_1(sK2))) = k5_xboole_0(sK1,k1_xboole_0) ),
    inference(light_normalisation,[status(thm)],[c_2920,c_2207])).

cnf(c_7363,plain,
    ( k3_tarski(k1_enumset1(k2_relat_1(sK2),k2_relat_1(sK2),k5_xboole_0(sK1,k1_xboole_0))) = k5_xboole_0(sK1,k1_xboole_0) ),
    inference(superposition,[status(thm)],[c_7,c_2962])).

cnf(c_3,plain,
    ( r1_tarski(k1_xboole_0,X0) ),
    inference(cnf_transformation,[],[f34])).

cnf(c_729,plain,
    ( r1_tarski(k1_xboole_0,X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3])).

cnf(c_1642,plain,
    ( k4_xboole_0(k1_xboole_0,X0) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_729,c_731])).

cnf(c_7624,plain,
    ( k5_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(demodulation,[status(thm)],[c_1642,c_2])).

cnf(c_7763,plain,
    ( k3_tarski(k1_enumset1(k2_relat_1(sK2),k2_relat_1(sK2),sK1)) = sK1 ),
    inference(demodulation,[status(thm)],[c_7363,c_7624])).

cnf(c_7769,plain,
    ( k3_tarski(k1_enumset1(k2_relat_1(sK2),k2_relat_1(sK2),k3_tarski(k1_enumset1(sK1,sK1,X0)))) = k5_xboole_0(sK1,k4_xboole_0(X0,sK1)) ),
    inference(superposition,[status(thm)],[c_7763,c_787])).

cnf(c_7791,plain,
    ( k3_tarski(k1_enumset1(k2_relat_1(sK2),k2_relat_1(sK2),k3_tarski(k1_enumset1(sK1,sK1,X0)))) = k3_tarski(k1_enumset1(sK1,sK1,X0)) ),
    inference(demodulation,[status(thm)],[c_7769,c_8])).

cnf(c_726,plain,
    ( v1_relat_1(k2_zfmisc_1(X0,X1)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_15])).

cnf(c_1163,plain,
    ( v1_relat_1(sK2) = iProver_top ),
    inference(superposition,[status(thm)],[c_726,c_852])).

cnf(c_14,plain,
    ( ~ v1_relat_1(X0)
    | k5_xboole_0(k1_relat_1(X0),k4_xboole_0(k2_relat_1(X0),k1_relat_1(X0))) = k3_relat_1(X0) ),
    inference(cnf_transformation,[],[f59])).

cnf(c_727,plain,
    ( k5_xboole_0(k1_relat_1(X0),k4_xboole_0(k2_relat_1(X0),k1_relat_1(X0))) = k3_relat_1(X0)
    | v1_relat_1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_14])).

cnf(c_758,plain,
    ( k3_tarski(k1_enumset1(k1_relat_1(X0),k1_relat_1(X0),k2_relat_1(X0))) = k3_relat_1(X0)
    | v1_relat_1(X0) != iProver_top ),
    inference(demodulation,[status(thm)],[c_727,c_8])).

cnf(c_1904,plain,
    ( k3_tarski(k1_enumset1(k1_relat_1(sK2),k1_relat_1(sK2),k2_relat_1(sK2))) = k3_relat_1(sK2) ),
    inference(superposition,[status(thm)],[c_1163,c_758])).

cnf(c_2685,plain,
    ( k3_tarski(k1_enumset1(k3_tarski(k1_enumset1(X0,X0,X1)),k3_tarski(k1_enumset1(X0,X0,X1)),X2)) = k3_tarski(k1_enumset1(X0,X0,k3_tarski(k1_enumset1(X1,X1,X2)))) ),
    inference(superposition,[status(thm)],[c_787,c_8])).

cnf(c_12319,plain,
    ( k3_tarski(k1_enumset1(X0,X0,k3_tarski(k1_enumset1(X1,X1,X2)))) = k3_tarski(k1_enumset1(X2,X2,k3_tarski(k1_enumset1(X0,X0,X1)))) ),
    inference(superposition,[status(thm)],[c_7,c_2685])).

cnf(c_12678,plain,
    ( k3_tarski(k1_enumset1(k1_relat_1(sK2),k1_relat_1(sK2),k3_tarski(k1_enumset1(k2_relat_1(sK2),k2_relat_1(sK2),X0)))) = k3_tarski(k1_enumset1(X0,X0,k3_relat_1(sK2))) ),
    inference(superposition,[status(thm)],[c_1904,c_12319])).

cnf(c_13676,plain,
    ( k3_tarski(k1_enumset1(k3_tarski(k1_enumset1(sK1,sK1,X0)),k3_tarski(k1_enumset1(sK1,sK1,X0)),k3_relat_1(sK2))) = k3_tarski(k1_enumset1(k1_relat_1(sK2),k1_relat_1(sK2),k3_tarski(k1_enumset1(sK1,sK1,X0)))) ),
    inference(superposition,[status(thm)],[c_7791,c_12678])).

cnf(c_12632,plain,
    ( k3_tarski(k1_enumset1(k3_tarski(k1_enumset1(X0,X0,X1)),k3_tarski(k1_enumset1(X0,X0,X1)),X2)) = k3_tarski(k1_enumset1(X1,X1,k3_tarski(k1_enumset1(X2,X2,X0)))) ),
    inference(superposition,[status(thm)],[c_7,c_12319])).

cnf(c_16720,plain,
    ( k3_tarski(k1_enumset1(k3_tarski(k1_enumset1(X0,X0,X1)),k3_tarski(k1_enumset1(X0,X0,X1)),X2)) = k3_tarski(k1_enumset1(k3_tarski(k1_enumset1(X2,X2,X0)),k3_tarski(k1_enumset1(X2,X2,X0)),X1)) ),
    inference(superposition,[status(thm)],[c_7,c_12632])).

cnf(c_20341,plain,
    ( k3_tarski(k1_enumset1(k3_tarski(k1_enumset1(X0,X0,k1_relat_1(sK2))),k3_tarski(k1_enumset1(X0,X0,k1_relat_1(sK2))),k2_relat_1(sK2))) = k3_tarski(k1_enumset1(k3_relat_1(sK2),k3_relat_1(sK2),X0)) ),
    inference(superposition,[status(thm)],[c_1904,c_16720])).

cnf(c_20445,plain,
    ( k3_tarski(k1_enumset1(k3_tarski(k1_enumset1(X0,X0,X1)),k3_tarski(k1_enumset1(X0,X0,X1)),X2)) = k3_tarski(k1_enumset1(k3_tarski(k1_enumset1(X0,X0,X2)),k3_tarski(k1_enumset1(X0,X0,X2)),X1)) ),
    inference(superposition,[status(thm)],[c_7,c_16720])).

cnf(c_23989,plain,
    ( k3_tarski(k1_enumset1(k3_tarski(k1_enumset1(k3_tarski(k1_enumset1(X0,X0,k1_relat_1(sK2))),k3_tarski(k1_enumset1(X0,X0,k1_relat_1(sK2))),X1)),k3_tarski(k1_enumset1(k3_tarski(k1_enumset1(X0,X0,k1_relat_1(sK2))),k3_tarski(k1_enumset1(X0,X0,k1_relat_1(sK2))),X1)),k2_relat_1(sK2))) = k3_tarski(k1_enumset1(k3_tarski(k1_enumset1(k3_relat_1(sK2),k3_relat_1(sK2),X0)),k3_tarski(k1_enumset1(k3_relat_1(sK2),k3_relat_1(sK2),X0)),X1)) ),
    inference(superposition,[status(thm)],[c_20341,c_20445])).

cnf(c_2682,plain,
    ( k5_xboole_0(k3_tarski(k1_enumset1(X0,X0,X1)),k4_xboole_0(X2,k3_tarski(k1_enumset1(X0,X0,X1)))) = k3_tarski(k1_enumset1(X1,X1,k3_tarski(k1_enumset1(X0,X0,X2)))) ),
    inference(superposition,[status(thm)],[c_7,c_787])).

cnf(c_12215,plain,
    ( k3_tarski(k1_enumset1(k3_tarski(k1_enumset1(X0,X0,X1)),k3_tarski(k1_enumset1(X0,X0,X1)),X2)) = k3_tarski(k1_enumset1(X1,X1,k3_tarski(k1_enumset1(X0,X0,X2)))) ),
    inference(superposition,[status(thm)],[c_2682,c_8])).

cnf(c_24283,plain,
    ( k3_tarski(k1_enumset1(k3_tarski(k1_enumset1(X0,X0,X1)),k3_tarski(k1_enumset1(X0,X0,X1)),k3_tarski(k1_enumset1(k1_relat_1(sK2),k1_relat_1(sK2),k2_relat_1(sK2))))) = k3_tarski(k1_enumset1(X0,X0,k3_tarski(k1_enumset1(k3_relat_1(sK2),k3_relat_1(sK2),X1)))) ),
    inference(demodulation,[status(thm)],[c_23989,c_12215])).

cnf(c_24284,plain,
    ( k3_tarski(k1_enumset1(k3_tarski(k1_enumset1(X0,X0,X1)),k3_tarski(k1_enumset1(X0,X0,X1)),k3_relat_1(sK2))) = k3_tarski(k1_enumset1(X0,X0,k3_tarski(k1_enumset1(k3_relat_1(sK2),k3_relat_1(sK2),X1)))) ),
    inference(light_normalisation,[status(thm)],[c_24283,c_1904])).

cnf(c_79780,plain,
    ( k3_tarski(k1_enumset1(k1_relat_1(sK2),k1_relat_1(sK2),k3_tarski(k1_enumset1(sK1,sK1,X0)))) = k3_tarski(k1_enumset1(sK1,sK1,k3_tarski(k1_enumset1(k3_relat_1(sK2),k3_relat_1(sK2),X0)))) ),
    inference(demodulation,[status(thm)],[c_13676,c_24284])).

cnf(c_12640,plain,
    ( k3_tarski(k1_enumset1(k2_relat_1(sK2),k2_relat_1(sK2),k3_tarski(k1_enumset1(X0,X0,k1_relat_1(sK2))))) = k3_tarski(k1_enumset1(X0,X0,k3_relat_1(sK2))) ),
    inference(superposition,[status(thm)],[c_1904,c_12319])).

cnf(c_13569,plain,
    ( k4_xboole_0(k3_tarski(k1_enumset1(X0,X0,k3_relat_1(sK2))),k3_tarski(k1_enumset1(X0,X0,k1_relat_1(sK2)))) = k4_xboole_0(k2_relat_1(sK2),k3_tarski(k1_enumset1(X0,X0,k1_relat_1(sK2)))) ),
    inference(superposition,[status(thm)],[c_12640,c_747])).

cnf(c_45408,plain,
    ( k4_xboole_0(k3_tarski(k1_enumset1(X0,X0,k3_relat_1(sK2))),k3_tarski(k1_enumset1(k1_relat_1(sK2),k1_relat_1(sK2),X0))) = k4_xboole_0(k2_relat_1(sK2),k3_tarski(k1_enumset1(X0,X0,k1_relat_1(sK2)))) ),
    inference(superposition,[status(thm)],[c_7,c_13569])).

cnf(c_79870,plain,
    ( k4_xboole_0(k3_tarski(k1_enumset1(k3_tarski(k1_enumset1(sK1,sK1,X0)),k3_tarski(k1_enumset1(sK1,sK1,X0)),k3_relat_1(sK2))),k3_tarski(k1_enumset1(sK1,sK1,k3_tarski(k1_enumset1(k3_relat_1(sK2),k3_relat_1(sK2),X0))))) = k4_xboole_0(k2_relat_1(sK2),k3_tarski(k1_enumset1(k3_tarski(k1_enumset1(sK1,sK1,X0)),k3_tarski(k1_enumset1(sK1,sK1,X0)),k1_relat_1(sK2)))) ),
    inference(superposition,[status(thm)],[c_79780,c_45408])).

cnf(c_1,plain,
    ( r1_tarski(X0,X1)
    | k4_xboole_0(X0,X1) != k1_xboole_0 ),
    inference(cnf_transformation,[],[f31])).

cnf(c_730,plain,
    ( k4_xboole_0(X0,X1) != k1_xboole_0
    | r1_tarski(X0,X1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1])).

cnf(c_1620,plain,
    ( k4_xboole_0(k1_xboole_0,X0) != k1_xboole_0
    | r1_tarski(X0,X0) = iProver_top ),
    inference(superposition,[status(thm)],[c_1350,c_730])).

cnf(c_5113,plain,
    ( r1_tarski(X0,X0) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_1620,c_1642])).

cnf(c_5118,plain,
    ( k4_xboole_0(X0,X0) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_5113,c_731])).

cnf(c_79961,plain,
    ( k4_xboole_0(k2_relat_1(sK2),k3_tarski(k1_enumset1(X0,X0,k3_tarski(k1_enumset1(sK1,sK1,k1_relat_1(sK2)))))) = k1_xboole_0 ),
    inference(demodulation,[status(thm)],[c_79870,c_5118,c_12215,c_24284])).

cnf(c_80332,plain,
    ( k3_tarski(k1_enumset1(X0,X0,k3_tarski(k1_enumset1(k3_tarski(k1_enumset1(sK1,sK1,k1_relat_1(sK2))),k3_tarski(k1_enumset1(sK1,sK1,k1_relat_1(sK2))),k2_relat_1(sK2))))) = k5_xboole_0(k3_tarski(k1_enumset1(X0,X0,k3_tarski(k1_enumset1(sK1,sK1,k1_relat_1(sK2))))),k1_xboole_0) ),
    inference(superposition,[status(thm)],[c_79961,c_787])).

cnf(c_80370,plain,
    ( k3_tarski(k1_enumset1(X0,X0,k3_tarski(k1_enumset1(k3_relat_1(sK2),k3_relat_1(sK2),sK1)))) = k3_tarski(k1_enumset1(X0,X0,k3_tarski(k1_enumset1(sK1,sK1,k1_relat_1(sK2))))) ),
    inference(demodulation,[status(thm)],[c_80332,c_7624,c_20341])).

cnf(c_11,plain,
    ( ~ v4_relat_1(X0,X1)
    | r1_tarski(k1_relat_1(X0),X1)
    | ~ v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f43])).

cnf(c_17,plain,
    ( v4_relat_1(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) ),
    inference(cnf_transformation,[],[f49])).

cnf(c_248,plain,
    ( v4_relat_1(X0,X1)
    | k1_zfmisc_1(k2_zfmisc_1(X1,X2)) != k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))
    | sK2 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_17,c_19])).

cnf(c_249,plain,
    ( v4_relat_1(sK2,X0)
    | k1_zfmisc_1(k2_zfmisc_1(X0,X1)) != k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)) ),
    inference(unflattening,[status(thm)],[c_248])).

cnf(c_271,plain,
    ( r1_tarski(k1_relat_1(X0),X1)
    | ~ v1_relat_1(X0)
    | X2 != X1
    | k1_zfmisc_1(k2_zfmisc_1(X2,X3)) != k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))
    | sK2 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_11,c_249])).

cnf(c_272,plain,
    ( r1_tarski(k1_relat_1(sK2),X0)
    | ~ v1_relat_1(sK2)
    | k1_zfmisc_1(k2_zfmisc_1(X0,X1)) != k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)) ),
    inference(unflattening,[status(thm)],[c_271])).

cnf(c_723,plain,
    ( k1_zfmisc_1(k2_zfmisc_1(X0,X1)) != k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))
    | r1_tarski(k1_relat_1(sK2),X0) = iProver_top
    | v1_relat_1(sK2) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_272])).

cnf(c_939,plain,
    ( r1_tarski(k1_relat_1(sK2),sK0) = iProver_top
    | v1_relat_1(sK2) != iProver_top ),
    inference(equality_resolution,[status(thm)],[c_723])).

cnf(c_1644,plain,
    ( k4_xboole_0(k1_relat_1(sK2),sK0) = k1_xboole_0
    | v1_relat_1(sK2) != iProver_top ),
    inference(superposition,[status(thm)],[c_939,c_731])).

cnf(c_2214,plain,
    ( k4_xboole_0(k1_relat_1(sK2),sK0) = k1_xboole_0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_1644,c_852,c_1064])).

cnf(c_2218,plain,
    ( k3_tarski(k1_enumset1(sK0,sK0,k1_relat_1(sK2))) = k5_xboole_0(sK0,k1_xboole_0) ),
    inference(superposition,[status(thm)],[c_2214,c_8])).

cnf(c_2730,plain,
    ( k3_tarski(k1_enumset1(sK0,sK0,k3_tarski(k1_enumset1(k1_relat_1(sK2),k1_relat_1(sK2),X0)))) = k5_xboole_0(k5_xboole_0(sK0,k1_xboole_0),k4_xboole_0(X0,k5_xboole_0(sK0,k1_xboole_0))) ),
    inference(superposition,[status(thm)],[c_2218,c_787])).

cnf(c_2752,plain,
    ( k3_tarski(k1_enumset1(sK0,sK0,k3_tarski(k1_enumset1(k1_relat_1(sK2),k1_relat_1(sK2),X0)))) = k3_tarski(k1_enumset1(k5_xboole_0(sK0,k1_xboole_0),k5_xboole_0(sK0,k1_xboole_0),X0)) ),
    inference(demodulation,[status(thm)],[c_2730,c_8])).

cnf(c_4213,plain,
    ( k3_tarski(k1_enumset1(k5_xboole_0(sK0,k1_xboole_0),k5_xboole_0(sK0,k1_xboole_0),k1_relat_1(sK2))) = k3_tarski(k1_enumset1(sK0,sK0,k1_relat_1(sK2))) ),
    inference(superposition,[status(thm)],[c_1430,c_2752])).

cnf(c_4267,plain,
    ( k3_tarski(k1_enumset1(k5_xboole_0(sK0,k1_xboole_0),k5_xboole_0(sK0,k1_xboole_0),k1_relat_1(sK2))) = k5_xboole_0(sK0,k1_xboole_0) ),
    inference(light_normalisation,[status(thm)],[c_4213,c_2218])).

cnf(c_7529,plain,
    ( k3_tarski(k1_enumset1(k1_relat_1(sK2),k1_relat_1(sK2),k5_xboole_0(sK0,k1_xboole_0))) = k5_xboole_0(sK0,k1_xboole_0) ),
    inference(superposition,[status(thm)],[c_7,c_4267])).

cnf(c_8078,plain,
    ( k3_tarski(k1_enumset1(k1_relat_1(sK2),k1_relat_1(sK2),sK0)) = sK0 ),
    inference(demodulation,[status(thm)],[c_7529,c_7624])).

cnf(c_8084,plain,
    ( k3_tarski(k1_enumset1(k1_relat_1(sK2),k1_relat_1(sK2),k3_tarski(k1_enumset1(sK0,sK0,X0)))) = k5_xboole_0(sK0,k4_xboole_0(X0,sK0)) ),
    inference(superposition,[status(thm)],[c_8078,c_787])).

cnf(c_8103,plain,
    ( k3_tarski(k1_enumset1(k1_relat_1(sK2),k1_relat_1(sK2),k3_tarski(k1_enumset1(sK0,sK0,X0)))) = k3_tarski(k1_enumset1(sK0,sK0,X0)) ),
    inference(demodulation,[status(thm)],[c_8084,c_8])).

cnf(c_9268,plain,
    ( k3_tarski(k1_enumset1(k1_relat_1(sK2),k1_relat_1(sK2),k3_tarski(k1_enumset1(X0,X0,sK0)))) = k3_tarski(k1_enumset1(sK0,sK0,X0)) ),
    inference(superposition,[status(thm)],[c_7,c_8103])).

cnf(c_1351,plain,
    ( k4_xboole_0(k3_tarski(k1_enumset1(X0,X0,X1)),X0) = k4_xboole_0(X1,X0) ),
    inference(superposition,[status(thm)],[c_7,c_747])).

cnf(c_24845,plain,
    ( k4_xboole_0(k3_tarski(k1_enumset1(X0,X0,k3_tarski(k1_enumset1(k3_relat_1(sK2),k3_relat_1(sK2),X1)))),k3_tarski(k1_enumset1(X0,X0,X1))) = k4_xboole_0(k3_relat_1(sK2),k3_tarski(k1_enumset1(X0,X0,X1))) ),
    inference(superposition,[status(thm)],[c_24284,c_1351])).

cnf(c_85609,plain,
    ( k4_xboole_0(k3_tarski(k1_enumset1(X0,X0,k3_tarski(k1_enumset1(k3_relat_1(sK2),k3_relat_1(sK2),X1)))),k3_tarski(k1_enumset1(X1,X1,X0))) = k4_xboole_0(k3_relat_1(sK2),k3_tarski(k1_enumset1(X0,X0,X1))) ),
    inference(superposition,[status(thm)],[c_7,c_24845])).

cnf(c_91696,plain,
    ( k4_xboole_0(k3_tarski(k1_enumset1(X0,X0,k3_tarski(k1_enumset1(X1,X1,k3_relat_1(sK2))))),k3_tarski(k1_enumset1(X1,X1,X0))) = k4_xboole_0(k3_relat_1(sK2),k3_tarski(k1_enumset1(X0,X0,X1))) ),
    inference(superposition,[status(thm)],[c_7,c_85609])).

cnf(c_92502,plain,
    ( k4_xboole_0(k3_tarski(k1_enumset1(k3_tarski(k1_enumset1(X0,X0,sK0)),k3_tarski(k1_enumset1(X0,X0,sK0)),k3_tarski(k1_enumset1(k1_relat_1(sK2),k1_relat_1(sK2),k3_relat_1(sK2))))),k3_tarski(k1_enumset1(sK0,sK0,X0))) = k4_xboole_0(k3_relat_1(sK2),k3_tarski(k1_enumset1(k3_tarski(k1_enumset1(X0,X0,sK0)),k3_tarski(k1_enumset1(X0,X0,sK0)),k1_relat_1(sK2)))) ),
    inference(superposition,[status(thm)],[c_9268,c_91696])).

cnf(c_1510,plain,
    ( k3_tarski(k1_enumset1(X0,X0,k3_tarski(k1_enumset1(X0,X0,X1)))) = k5_xboole_0(X0,k4_xboole_0(X1,X0)) ),
    inference(superposition,[status(thm)],[c_1351,c_8])).

cnf(c_1512,plain,
    ( k3_tarski(k1_enumset1(X0,X0,k3_tarski(k1_enumset1(X0,X0,X1)))) = k3_tarski(k1_enumset1(X0,X0,X1)) ),
    inference(light_normalisation,[status(thm)],[c_1510,c_8])).

cnf(c_2093,plain,
    ( k3_tarski(k1_enumset1(k1_relat_1(sK2),k1_relat_1(sK2),k3_relat_1(sK2))) = k3_tarski(k1_enumset1(k1_relat_1(sK2),k1_relat_1(sK2),k2_relat_1(sK2))) ),
    inference(superposition,[status(thm)],[c_1904,c_1512])).

cnf(c_2108,plain,
    ( k3_tarski(k1_enumset1(k1_relat_1(sK2),k1_relat_1(sK2),k3_relat_1(sK2))) = k3_relat_1(sK2) ),
    inference(light_normalisation,[status(thm)],[c_2093,c_1904])).

cnf(c_92782,plain,
    ( k4_xboole_0(k3_tarski(k1_enumset1(k3_tarski(k1_enumset1(X0,X0,sK0)),k3_tarski(k1_enumset1(X0,X0,sK0)),k3_relat_1(sK2))),k3_tarski(k1_enumset1(sK0,sK0,X0))) = k4_xboole_0(k3_relat_1(sK2),k3_tarski(k1_enumset1(k3_tarski(k1_enumset1(X0,X0,sK0)),k3_tarski(k1_enumset1(X0,X0,sK0)),k1_relat_1(sK2)))) ),
    inference(light_normalisation,[status(thm)],[c_92502,c_2108])).

cnf(c_92783,plain,
    ( k4_xboole_0(k3_relat_1(sK2),k3_tarski(k1_enumset1(sK0,sK0,k3_tarski(k1_enumset1(X0,X0,k1_relat_1(sK2)))))) = k4_xboole_0(k3_relat_1(sK2),k3_tarski(k1_enumset1(X0,X0,sK0))) ),
    inference(demodulation,[status(thm)],[c_92782,c_12215,c_24284,c_85609])).

cnf(c_93522,plain,
    ( k4_xboole_0(k3_relat_1(sK2),k3_tarski(k1_enumset1(sK0,sK0,k3_tarski(k1_enumset1(k1_relat_1(sK2),k1_relat_1(sK2),X0))))) = k4_xboole_0(k3_relat_1(sK2),k3_tarski(k1_enumset1(X0,X0,sK0))) ),
    inference(superposition,[status(thm)],[c_7,c_92783])).

cnf(c_98085,plain,
    ( k4_xboole_0(k3_relat_1(sK2),k3_tarski(k1_enumset1(sK0,sK0,k3_tarski(k1_enumset1(k1_relat_1(sK2),k1_relat_1(sK2),X0))))) = k4_xboole_0(k3_relat_1(sK2),k3_tarski(k1_enumset1(sK0,sK0,X0))) ),
    inference(superposition,[status(thm)],[c_7,c_93522])).

cnf(c_98435,plain,
    ( k4_xboole_0(k3_relat_1(sK2),k3_tarski(k1_enumset1(sK0,sK0,k3_tarski(k1_enumset1(k1_relat_1(sK2),k1_relat_1(sK2),k3_tarski(k1_enumset1(sK1,sK1,k1_relat_1(sK2)))))))) = k4_xboole_0(k3_relat_1(sK2),k3_tarski(k1_enumset1(sK0,sK0,k3_tarski(k1_enumset1(k3_relat_1(sK2),k3_relat_1(sK2),sK1))))) ),
    inference(superposition,[status(thm)],[c_80370,c_98085])).

cnf(c_98439,plain,
    ( k4_xboole_0(k3_relat_1(sK2),k3_tarski(k1_enumset1(sK0,sK0,k3_tarski(k1_enumset1(X0,X0,k1_relat_1(sK2)))))) = k4_xboole_0(k3_relat_1(sK2),k3_tarski(k1_enumset1(sK0,sK0,X0))) ),
    inference(superposition,[status(thm)],[c_7,c_98085])).

cnf(c_98532,plain,
    ( k4_xboole_0(k3_relat_1(sK2),k3_tarski(k1_enumset1(sK0,sK0,k3_tarski(k1_enumset1(k3_relat_1(sK2),k3_relat_1(sK2),sK1))))) = k4_xboole_0(k3_relat_1(sK2),k3_tarski(k1_enumset1(sK0,sK0,sK1))) ),
    inference(demodulation,[status(thm)],[c_98435,c_98085,c_98439])).

cnf(c_24770,plain,
    ( k3_tarski(k1_enumset1(k1_xboole_0,k1_xboole_0,k3_tarski(k1_enumset1(k3_relat_1(sK2),k3_relat_1(sK2),X0)))) = k3_tarski(k1_enumset1(X0,X0,k3_relat_1(sK2))) ),
    inference(superposition,[status(thm)],[c_1244,c_24284])).

cnf(c_1758,plain,
    ( k4_xboole_0(k3_tarski(k1_enumset1(X0,X0,X1)),k3_tarski(k1_enumset1(X0,X0,X1))) = k4_xboole_0(X0,k3_tarski(k1_enumset1(X0,X0,X1))) ),
    inference(superposition,[status(thm)],[c_1512,c_747])).

cnf(c_25321,plain,
    ( k4_xboole_0(k3_tarski(k1_enumset1(X0,X0,k3_relat_1(sK2))),k3_tarski(k1_enumset1(X0,X0,k3_relat_1(sK2)))) = k4_xboole_0(k1_xboole_0,k3_tarski(k1_enumset1(k1_xboole_0,k1_xboole_0,k3_tarski(k1_enumset1(k3_relat_1(sK2),k3_relat_1(sK2),X0))))) ),
    inference(superposition,[status(thm)],[c_24770,c_1758])).

cnf(c_1353,plain,
    ( k3_tarski(k1_enumset1(X0,X0,k3_tarski(k1_enumset1(X1,X1,X0)))) = k5_xboole_0(X0,k4_xboole_0(X1,X0)) ),
    inference(superposition,[status(thm)],[c_747,c_8])).

cnf(c_1355,plain,
    ( k3_tarski(k1_enumset1(X0,X0,k3_tarski(k1_enumset1(X1,X1,X0)))) = k3_tarski(k1_enumset1(X0,X0,X1)) ),
    inference(light_normalisation,[status(thm)],[c_1353,c_8])).

cnf(c_1738,plain,
    ( k4_xboole_0(k3_tarski(k1_enumset1(X0,X0,X1)),k3_tarski(k1_enumset1(X1,X1,X0))) = k4_xboole_0(X0,k3_tarski(k1_enumset1(X1,X1,X0))) ),
    inference(superposition,[status(thm)],[c_1355,c_747])).

cnf(c_13564,plain,
    ( k4_xboole_0(k3_tarski(k1_enumset1(X0,X0,k3_relat_1(sK2))),k3_tarski(k1_enumset1(k3_tarski(k1_enumset1(X0,X0,k1_relat_1(sK2))),k3_tarski(k1_enumset1(X0,X0,k1_relat_1(sK2))),k2_relat_1(sK2)))) = k4_xboole_0(k2_relat_1(sK2),k3_tarski(k1_enumset1(k3_tarski(k1_enumset1(X0,X0,k1_relat_1(sK2))),k3_tarski(k1_enumset1(X0,X0,k1_relat_1(sK2))),k2_relat_1(sK2)))) ),
    inference(superposition,[status(thm)],[c_12640,c_1738])).

cnf(c_13611,plain,
    ( k4_xboole_0(k3_tarski(k1_enumset1(X0,X0,k3_relat_1(sK2))),k3_tarski(k1_enumset1(X0,X0,k3_tarski(k1_enumset1(k1_relat_1(sK2),k1_relat_1(sK2),k2_relat_1(sK2)))))) = k4_xboole_0(k2_relat_1(sK2),k3_tarski(k1_enumset1(X0,X0,k3_tarski(k1_enumset1(k1_relat_1(sK2),k1_relat_1(sK2),k2_relat_1(sK2)))))) ),
    inference(demodulation,[status(thm)],[c_13564,c_2685])).

cnf(c_13612,plain,
    ( k4_xboole_0(k3_tarski(k1_enumset1(X0,X0,k3_relat_1(sK2))),k3_tarski(k1_enumset1(X0,X0,k3_relat_1(sK2)))) = k4_xboole_0(k2_relat_1(sK2),k3_tarski(k1_enumset1(X0,X0,k3_relat_1(sK2)))) ),
    inference(light_normalisation,[status(thm)],[c_13611,c_1904])).

cnf(c_25571,plain,
    ( k4_xboole_0(k3_tarski(k1_enumset1(X0,X0,k3_relat_1(sK2))),k3_tarski(k1_enumset1(X0,X0,k3_relat_1(sK2)))) = k1_xboole_0 ),
    inference(demodulation,[status(thm)],[c_25321,c_1642,c_13612])).

cnf(c_25940,plain,
    ( k4_xboole_0(k3_tarski(k1_enumset1(k3_tarski(k1_enumset1(X0,X0,k3_relat_1(sK2))),k3_tarski(k1_enumset1(X0,X0,k3_relat_1(sK2))),X1)),k3_tarski(k1_enumset1(k3_tarski(k1_enumset1(X0,X0,k3_relat_1(sK2))),k3_tarski(k1_enumset1(X0,X0,k3_relat_1(sK2))),X1))) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_16720,c_25571])).

cnf(c_9126,plain,
    ( k4_xboole_0(k3_tarski(k1_enumset1(X0,X0,X1)),k3_tarski(k1_enumset1(X0,X0,X1))) = k4_xboole_0(X0,k3_tarski(k1_enumset1(X1,X1,X0))) ),
    inference(superposition,[status(thm)],[c_7,c_1738])).

cnf(c_25990,plain,
    ( k4_xboole_0(k3_relat_1(sK2),k3_tarski(k1_enumset1(k3_tarski(k1_enumset1(X0,X0,X1)),k3_tarski(k1_enumset1(X0,X0,X1)),k3_relat_1(sK2)))) = k1_xboole_0 ),
    inference(demodulation,[status(thm)],[c_25940,c_9126,c_12215])).

cnf(c_25991,plain,
    ( k4_xboole_0(k3_relat_1(sK2),k3_tarski(k1_enumset1(X0,X0,k3_tarski(k1_enumset1(k3_relat_1(sK2),k3_relat_1(sK2),X1))))) = k1_xboole_0 ),
    inference(light_normalisation,[status(thm)],[c_25990,c_24284])).

cnf(c_98534,plain,
    ( k4_xboole_0(k3_relat_1(sK2),k3_tarski(k1_enumset1(sK0,sK0,sK1))) = k1_xboole_0 ),
    inference(demodulation,[status(thm)],[c_98532,c_25991])).

cnf(c_2324,plain,
    ( r1_tarski(k3_relat_1(sK2),k3_tarski(k1_enumset1(sK0,sK0,sK1)))
    | k4_xboole_0(k3_relat_1(sK2),k3_tarski(k1_enumset1(sK0,sK0,sK1))) != k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_1])).

cnf(c_18,negated_conjecture,
    ( ~ r1_tarski(k3_relat_1(sK2),k5_xboole_0(sK0,k4_xboole_0(sK1,sK0))) ),
    inference(cnf_transformation,[],[f60])).

cnf(c_725,plain,
    ( r1_tarski(k3_relat_1(sK2),k5_xboole_0(sK0,k4_xboole_0(sK1,sK0))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_18])).

cnf(c_743,plain,
    ( r1_tarski(k3_relat_1(sK2),k3_tarski(k1_enumset1(sK0,sK0,sK1))) != iProver_top ),
    inference(demodulation,[status(thm)],[c_8,c_725])).

cnf(c_801,plain,
    ( ~ r1_tarski(k3_relat_1(sK2),k3_tarski(k1_enumset1(sK0,sK0,sK1))) ),
    inference(predicate_to_equality_rev,[status(thm)],[c_743])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_98534,c_2324,c_801])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : iproveropt_run.sh %d %s
% 0.13/0.34  % Computer   : n024.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 20:07:51 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  % Running in FOF mode
% 27.72/4.01  % SZS status Started for /export/starexec/sandbox/benchmark/theBenchmark.p
% 27.72/4.01  
% 27.72/4.01  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 27.72/4.01  
% 27.72/4.01  ------  iProver source info
% 27.72/4.01  
% 27.72/4.01  git: date: 2020-06-30 10:37:57 +0100
% 27.72/4.01  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 27.72/4.01  git: non_committed_changes: false
% 27.72/4.01  git: last_make_outside_of_git: false
% 27.72/4.01  
% 27.72/4.01  ------ 
% 27.72/4.01  ------ Parsing...
% 27.72/4.01  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 27.72/4.01  
% 27.72/4.01  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe:1:0s pe:2:0s pe_e  sf_s  rm: 2 0s  sf_e  pe_s  pe_e 
% 27.72/4.01  
% 27.72/4.01  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 27.72/4.01  
% 27.72/4.01  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 27.72/4.01  ------ Proving...
% 27.72/4.01  ------ Problem Properties 
% 27.72/4.01  
% 27.72/4.01  
% 27.72/4.01  clauses                                 15
% 27.72/4.01  conjectures                             1
% 27.72/4.01  EPR                                     1
% 27.72/4.01  Horn                                    15
% 27.72/4.01  unary                                   8
% 27.72/4.01  binary                                  4
% 27.72/4.01  lits                                    25
% 27.72/4.01  lits eq                                 11
% 27.72/4.01  fd_pure                                 0
% 27.72/4.01  fd_pseudo                               0
% 27.72/4.01  fd_cond                                 0
% 27.72/4.01  fd_pseudo_cond                          0
% 27.72/4.01  AC symbols                              0
% 27.72/4.01  
% 27.72/4.01  ------ Input Options Time Limit: Unbounded
% 27.72/4.01  
% 27.72/4.01  
% 27.72/4.01  ------ 
% 27.72/4.01  Current options:
% 27.72/4.01  ------ 
% 27.72/4.01  
% 27.72/4.01  
% 27.72/4.01  
% 27.72/4.01  
% 27.72/4.01  ------ Proving...
% 27.72/4.01  
% 27.72/4.01  
% 27.72/4.01  % SZS status Theorem for theBenchmark.p
% 27.72/4.01  
% 27.72/4.01  % SZS output start CNFRefutation for theBenchmark.p
% 27.72/4.01  
% 27.72/4.01  fof(f8,axiom,(
% 27.72/4.01    ! [X0,X1] : k2_tarski(X0,X1) = k2_tarski(X1,X0)),
% 27.72/4.01    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 27.72/4.01  
% 27.72/4.01  fof(f39,plain,(
% 27.72/4.01    ( ! [X0,X1] : (k2_tarski(X0,X1) = k2_tarski(X1,X0)) )),
% 27.72/4.01    inference(cnf_transformation,[],[f8])).
% 27.72/4.01  
% 27.72/4.01  fof(f9,axiom,(
% 27.72/4.01    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1)),
% 27.72/4.01    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 27.72/4.01  
% 27.72/4.01  fof(f40,plain,(
% 27.72/4.01    ( ! [X0,X1] : (k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1)) )),
% 27.72/4.01    inference(cnf_transformation,[],[f9])).
% 27.72/4.01  
% 27.72/4.01  fof(f57,plain,(
% 27.72/4.01    ( ! [X0,X1] : (k1_enumset1(X0,X0,X1) = k1_enumset1(X1,X1,X0)) )),
% 27.72/4.01    inference(definition_unfolding,[],[f39,f40,f40])).
% 27.72/4.01  
% 27.72/4.01  fof(f2,axiom,(
% 27.72/4.01    ! [X0] : k2_xboole_0(X0,k1_xboole_0) = X0),
% 27.72/4.01    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 27.72/4.01  
% 27.72/4.01  fof(f33,plain,(
% 27.72/4.01    ( ! [X0] : (k2_xboole_0(X0,k1_xboole_0) = X0) )),
% 27.72/4.01    inference(cnf_transformation,[],[f2])).
% 27.72/4.01  
% 27.72/4.01  fof(f7,axiom,(
% 27.72/4.01    ! [X0,X1] : k2_xboole_0(X0,X1) = k5_xboole_0(X0,k4_xboole_0(X1,X0))),
% 27.72/4.01    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 27.72/4.01  
% 27.72/4.01  fof(f38,plain,(
% 27.72/4.01    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k5_xboole_0(X0,k4_xboole_0(X1,X0))) )),
% 27.72/4.01    inference(cnf_transformation,[],[f7])).
% 27.72/4.01  
% 27.72/4.01  fof(f53,plain,(
% 27.72/4.01    ( ! [X0] : (k5_xboole_0(X0,k4_xboole_0(k1_xboole_0,X0)) = X0) )),
% 27.72/4.01    inference(definition_unfolding,[],[f33,f38])).
% 27.72/4.01  
% 27.72/4.01  fof(f10,axiom,(
% 27.72/4.01    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1))),
% 27.72/4.01    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 27.72/4.01  
% 27.72/4.01  fof(f41,plain,(
% 27.72/4.01    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1))) )),
% 27.72/4.01    inference(cnf_transformation,[],[f10])).
% 27.72/4.01  
% 27.72/4.01  fof(f58,plain,(
% 27.72/4.01    ( ! [X0,X1] : (k5_xboole_0(X0,k4_xboole_0(X1,X0)) = k3_tarski(k1_enumset1(X0,X0,X1))) )),
% 27.72/4.01    inference(definition_unfolding,[],[f41,f38,f40])).
% 27.72/4.01  
% 27.72/4.01  fof(f4,axiom,(
% 27.72/4.01    ! [X0,X1] : k4_xboole_0(X0,X1) = k4_xboole_0(k2_xboole_0(X0,X1),X1)),
% 27.72/4.01    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 27.72/4.01  
% 27.72/4.01  fof(f35,plain,(
% 27.72/4.01    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k4_xboole_0(k2_xboole_0(X0,X1),X1)) )),
% 27.72/4.01    inference(cnf_transformation,[],[f4])).
% 27.72/4.01  
% 27.72/4.01  fof(f54,plain,(
% 27.72/4.01    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k4_xboole_0(k5_xboole_0(X0,k4_xboole_0(X1,X0)),X1)) )),
% 27.72/4.01    inference(definition_unfolding,[],[f35,f38])).
% 27.72/4.01  
% 27.72/4.01  fof(f13,axiom,(
% 27.72/4.01    ! [X0,X1] : (v1_relat_1(X1) => (v5_relat_1(X1,X0) <=> r1_tarski(k2_relat_1(X1),X0)))),
% 27.72/4.01    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 27.72/4.01  
% 27.72/4.01  fof(f22,plain,(
% 27.72/4.01    ! [X0,X1] : ((v5_relat_1(X1,X0) <=> r1_tarski(k2_relat_1(X1),X0)) | ~v1_relat_1(X1))),
% 27.72/4.01    inference(ennf_transformation,[],[f13])).
% 27.72/4.01  
% 27.72/4.01  fof(f28,plain,(
% 27.72/4.01    ! [X0,X1] : (((v5_relat_1(X1,X0) | ~r1_tarski(k2_relat_1(X1),X0)) & (r1_tarski(k2_relat_1(X1),X0) | ~v5_relat_1(X1,X0))) | ~v1_relat_1(X1))),
% 27.72/4.01    inference(nnf_transformation,[],[f22])).
% 27.72/4.01  
% 27.72/4.01  fof(f45,plain,(
% 27.72/4.01    ( ! [X0,X1] : (r1_tarski(k2_relat_1(X1),X0) | ~v5_relat_1(X1,X0) | ~v1_relat_1(X1)) )),
% 27.72/4.01    inference(cnf_transformation,[],[f28])).
% 27.72/4.01  
% 27.72/4.01  fof(f16,axiom,(
% 27.72/4.01    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => (v5_relat_1(X2,X1) & v4_relat_1(X2,X0)))),
% 27.72/4.01    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 27.72/4.01  
% 27.72/4.01  fof(f24,plain,(
% 27.72/4.01    ! [X0,X1,X2] : ((v5_relat_1(X2,X1) & v4_relat_1(X2,X0)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 27.72/4.01    inference(ennf_transformation,[],[f16])).
% 27.72/4.01  
% 27.72/4.01  fof(f50,plain,(
% 27.72/4.01    ( ! [X2,X0,X1] : (v5_relat_1(X2,X1) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 27.72/4.01    inference(cnf_transformation,[],[f24])).
% 27.72/4.01  
% 27.72/4.01  fof(f17,conjecture,(
% 27.72/4.01    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => r1_tarski(k3_relat_1(X2),k2_xboole_0(X0,X1)))),
% 27.72/4.01    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 27.72/4.01  
% 27.72/4.01  fof(f18,negated_conjecture,(
% 27.72/4.01    ~! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => r1_tarski(k3_relat_1(X2),k2_xboole_0(X0,X1)))),
% 27.72/4.01    inference(negated_conjecture,[],[f17])).
% 27.72/4.01  
% 27.72/4.01  fof(f25,plain,(
% 27.72/4.01    ? [X0,X1,X2] : (~r1_tarski(k3_relat_1(X2),k2_xboole_0(X0,X1)) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 27.72/4.01    inference(ennf_transformation,[],[f18])).
% 27.72/4.01  
% 27.72/4.01  fof(f29,plain,(
% 27.72/4.01    ? [X0,X1,X2] : (~r1_tarski(k3_relat_1(X2),k2_xboole_0(X0,X1)) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) => (~r1_tarski(k3_relat_1(sK2),k2_xboole_0(sK0,sK1)) & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))))),
% 27.72/4.01    introduced(choice_axiom,[])).
% 27.72/4.01  
% 27.72/4.01  fof(f30,plain,(
% 27.72/4.01    ~r1_tarski(k3_relat_1(sK2),k2_xboole_0(sK0,sK1)) & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))),
% 27.72/4.01    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f25,f29])).
% 27.72/4.01  
% 27.72/4.01  fof(f51,plain,(
% 27.72/4.01    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))),
% 27.72/4.01    inference(cnf_transformation,[],[f30])).
% 27.72/4.01  
% 27.72/4.01  fof(f1,axiom,(
% 27.72/4.01    ! [X0,X1] : (k4_xboole_0(X0,X1) = k1_xboole_0 <=> r1_tarski(X0,X1))),
% 27.72/4.01    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 27.72/4.01  
% 27.72/4.01  fof(f26,plain,(
% 27.72/4.01    ! [X0,X1] : ((k4_xboole_0(X0,X1) = k1_xboole_0 | ~r1_tarski(X0,X1)) & (r1_tarski(X0,X1) | k4_xboole_0(X0,X1) != k1_xboole_0))),
% 27.72/4.01    inference(nnf_transformation,[],[f1])).
% 27.72/4.01  
% 27.72/4.01  fof(f32,plain,(
% 27.72/4.01    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k1_xboole_0 | ~r1_tarski(X0,X1)) )),
% 27.72/4.01    inference(cnf_transformation,[],[f26])).
% 27.72/4.01  
% 27.72/4.01  fof(f11,axiom,(
% 27.72/4.01    ! [X0] : (v1_relat_1(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => v1_relat_1(X1)))),
% 27.72/4.01    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 27.72/4.01  
% 27.72/4.01  fof(f20,plain,(
% 27.72/4.01    ! [X0] : (! [X1] : (v1_relat_1(X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) | ~v1_relat_1(X0))),
% 27.72/4.01    inference(ennf_transformation,[],[f11])).
% 27.72/4.01  
% 27.72/4.01  fof(f42,plain,(
% 27.72/4.01    ( ! [X0,X1] : (v1_relat_1(X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0)) | ~v1_relat_1(X0)) )),
% 27.72/4.01    inference(cnf_transformation,[],[f20])).
% 27.72/4.01  
% 27.72/4.01  fof(f15,axiom,(
% 27.72/4.01    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1))),
% 27.72/4.01    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 27.72/4.01  
% 27.72/4.01  fof(f48,plain,(
% 27.72/4.01    ( ! [X0,X1] : (v1_relat_1(k2_zfmisc_1(X0,X1))) )),
% 27.72/4.01    inference(cnf_transformation,[],[f15])).
% 27.72/4.01  
% 27.72/4.01  fof(f6,axiom,(
% 27.72/4.01    ! [X0,X1,X2] : k2_xboole_0(X0,k2_xboole_0(X1,X2)) = k2_xboole_0(k2_xboole_0(X0,X1),X2)),
% 27.72/4.01    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 27.72/4.01  
% 27.72/4.01  fof(f37,plain,(
% 27.72/4.01    ( ! [X2,X0,X1] : (k2_xboole_0(X0,k2_xboole_0(X1,X2)) = k2_xboole_0(k2_xboole_0(X0,X1),X2)) )),
% 27.72/4.01    inference(cnf_transformation,[],[f6])).
% 27.72/4.01  
% 27.72/4.01  fof(f56,plain,(
% 27.72/4.01    ( ! [X2,X0,X1] : (k5_xboole_0(X0,k4_xboole_0(k5_xboole_0(X1,k4_xboole_0(X2,X1)),X0)) = k5_xboole_0(k5_xboole_0(X0,k4_xboole_0(X1,X0)),k4_xboole_0(X2,k5_xboole_0(X0,k4_xboole_0(X1,X0))))) )),
% 27.72/4.01    inference(definition_unfolding,[],[f37,f38,f38,f38,f38])).
% 27.72/4.01  
% 27.72/4.01  fof(f3,axiom,(
% 27.72/4.01    ! [X0] : r1_tarski(k1_xboole_0,X0)),
% 27.72/4.01    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 27.72/4.01  
% 27.72/4.01  fof(f34,plain,(
% 27.72/4.01    ( ! [X0] : (r1_tarski(k1_xboole_0,X0)) )),
% 27.72/4.01    inference(cnf_transformation,[],[f3])).
% 27.72/4.01  
% 27.72/4.01  fof(f14,axiom,(
% 27.72/4.01    ! [X0] : (v1_relat_1(X0) => k2_xboole_0(k1_relat_1(X0),k2_relat_1(X0)) = k3_relat_1(X0))),
% 27.72/4.01    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 27.72/4.01  
% 27.72/4.01  fof(f23,plain,(
% 27.72/4.01    ! [X0] : (k2_xboole_0(k1_relat_1(X0),k2_relat_1(X0)) = k3_relat_1(X0) | ~v1_relat_1(X0))),
% 27.72/4.01    inference(ennf_transformation,[],[f14])).
% 27.72/4.01  
% 27.72/4.01  fof(f47,plain,(
% 27.72/4.01    ( ! [X0] : (k2_xboole_0(k1_relat_1(X0),k2_relat_1(X0)) = k3_relat_1(X0) | ~v1_relat_1(X0)) )),
% 27.72/4.01    inference(cnf_transformation,[],[f23])).
% 27.72/4.01  
% 27.72/4.01  fof(f59,plain,(
% 27.72/4.01    ( ! [X0] : (k5_xboole_0(k1_relat_1(X0),k4_xboole_0(k2_relat_1(X0),k1_relat_1(X0))) = k3_relat_1(X0) | ~v1_relat_1(X0)) )),
% 27.72/4.01    inference(definition_unfolding,[],[f47,f38])).
% 27.72/4.01  
% 27.72/4.01  fof(f31,plain,(
% 27.72/4.01    ( ! [X0,X1] : (r1_tarski(X0,X1) | k4_xboole_0(X0,X1) != k1_xboole_0) )),
% 27.72/4.01    inference(cnf_transformation,[],[f26])).
% 27.72/4.01  
% 27.72/4.01  fof(f12,axiom,(
% 27.72/4.01    ! [X0,X1] : (v1_relat_1(X1) => (v4_relat_1(X1,X0) <=> r1_tarski(k1_relat_1(X1),X0)))),
% 27.72/4.01    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 27.72/4.01  
% 27.72/4.01  fof(f21,plain,(
% 27.72/4.01    ! [X0,X1] : ((v4_relat_1(X1,X0) <=> r1_tarski(k1_relat_1(X1),X0)) | ~v1_relat_1(X1))),
% 27.72/4.01    inference(ennf_transformation,[],[f12])).
% 27.72/4.01  
% 27.72/4.01  fof(f27,plain,(
% 27.72/4.01    ! [X0,X1] : (((v4_relat_1(X1,X0) | ~r1_tarski(k1_relat_1(X1),X0)) & (r1_tarski(k1_relat_1(X1),X0) | ~v4_relat_1(X1,X0))) | ~v1_relat_1(X1))),
% 27.72/4.01    inference(nnf_transformation,[],[f21])).
% 27.72/4.01  
% 27.72/4.01  fof(f43,plain,(
% 27.72/4.01    ( ! [X0,X1] : (r1_tarski(k1_relat_1(X1),X0) | ~v4_relat_1(X1,X0) | ~v1_relat_1(X1)) )),
% 27.72/4.01    inference(cnf_transformation,[],[f27])).
% 27.72/4.01  
% 27.72/4.01  fof(f49,plain,(
% 27.72/4.01    ( ! [X2,X0,X1] : (v4_relat_1(X2,X0) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 27.72/4.01    inference(cnf_transformation,[],[f24])).
% 27.72/4.01  
% 27.72/4.01  fof(f52,plain,(
% 27.72/4.01    ~r1_tarski(k3_relat_1(sK2),k2_xboole_0(sK0,sK1))),
% 27.72/4.01    inference(cnf_transformation,[],[f30])).
% 27.72/4.01  
% 27.72/4.01  fof(f60,plain,(
% 27.72/4.01    ~r1_tarski(k3_relat_1(sK2),k5_xboole_0(sK0,k4_xboole_0(sK1,sK0)))),
% 27.72/4.01    inference(definition_unfolding,[],[f52,f38])).
% 27.72/4.01  
% 27.72/4.01  cnf(c_7,plain,
% 27.72/4.01      ( k1_enumset1(X0,X0,X1) = k1_enumset1(X1,X1,X0) ),
% 27.72/4.01      inference(cnf_transformation,[],[f57]) ).
% 27.72/4.01  
% 27.72/4.01  cnf(c_2,plain,
% 27.72/4.01      ( k5_xboole_0(X0,k4_xboole_0(k1_xboole_0,X0)) = X0 ),
% 27.72/4.01      inference(cnf_transformation,[],[f53]) ).
% 27.72/4.01  
% 27.72/4.01  cnf(c_8,plain,
% 27.72/4.01      ( k3_tarski(k1_enumset1(X0,X0,X1)) = k5_xboole_0(X0,k4_xboole_0(X1,X0)) ),
% 27.72/4.01      inference(cnf_transformation,[],[f58]) ).
% 27.72/4.01  
% 27.72/4.01  cnf(c_1158,plain,
% 27.72/4.01      ( k3_tarski(k1_enumset1(X0,X0,k1_xboole_0)) = X0 ),
% 27.72/4.01      inference(superposition,[status(thm)],[c_2,c_8]) ).
% 27.72/4.01  
% 27.72/4.01  cnf(c_1244,plain,
% 27.72/4.01      ( k3_tarski(k1_enumset1(k1_xboole_0,k1_xboole_0,X0)) = X0 ),
% 27.72/4.01      inference(superposition,[status(thm)],[c_7,c_1158]) ).
% 27.72/4.01  
% 27.72/4.01  cnf(c_4,plain,
% 27.72/4.01      ( k4_xboole_0(k5_xboole_0(X0,k4_xboole_0(X1,X0)),X1) = k4_xboole_0(X0,X1) ),
% 27.72/4.01      inference(cnf_transformation,[],[f54]) ).
% 27.72/4.01  
% 27.72/4.01  cnf(c_747,plain,
% 27.72/4.01      ( k4_xboole_0(k3_tarski(k1_enumset1(X0,X0,X1)),X1) = k4_xboole_0(X0,X1) ),
% 27.72/4.01      inference(light_normalisation,[status(thm)],[c_4,c_8]) ).
% 27.72/4.01  
% 27.72/4.01  cnf(c_1350,plain,
% 27.72/4.01      ( k4_xboole_0(X0,X0) = k4_xboole_0(k1_xboole_0,X0) ),
% 27.72/4.01      inference(superposition,[status(thm)],[c_1244,c_747]) ).
% 27.72/4.01  
% 27.72/4.01  cnf(c_1423,plain,
% 27.72/4.01      ( k3_tarski(k1_enumset1(X0,X0,X0)) = k5_xboole_0(X0,k4_xboole_0(k1_xboole_0,X0)) ),
% 27.72/4.01      inference(superposition,[status(thm)],[c_1350,c_8]) ).
% 27.72/4.01  
% 27.72/4.01  cnf(c_1430,plain,
% 27.72/4.01      ( k3_tarski(k1_enumset1(X0,X0,X0)) = X0 ),
% 27.72/4.01      inference(light_normalisation,[status(thm)],[c_1423,c_2]) ).
% 27.72/4.01  
% 27.72/4.01  cnf(c_13,plain,
% 27.72/4.01      ( ~ v5_relat_1(X0,X1)
% 27.72/4.01      | r1_tarski(k2_relat_1(X0),X1)
% 27.72/4.01      | ~ v1_relat_1(X0) ),
% 27.72/4.01      inference(cnf_transformation,[],[f45]) ).
% 27.72/4.01  
% 27.72/4.01  cnf(c_16,plain,
% 27.72/4.01      ( v5_relat_1(X0,X1)
% 27.72/4.01      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) ),
% 27.72/4.01      inference(cnf_transformation,[],[f50]) ).
% 27.72/4.01  
% 27.72/4.01  cnf(c_19,negated_conjecture,
% 27.72/4.01      ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ),
% 27.72/4.01      inference(cnf_transformation,[],[f51]) ).
% 27.72/4.01  
% 27.72/4.01  cnf(c_236,plain,
% 27.72/4.01      ( v5_relat_1(X0,X1)
% 27.72/4.01      | k1_zfmisc_1(k2_zfmisc_1(X2,X1)) != k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))
% 27.72/4.01      | sK2 != X0 ),
% 27.72/4.01      inference(resolution_lifted,[status(thm)],[c_16,c_19]) ).
% 27.72/4.01  
% 27.72/4.01  cnf(c_237,plain,
% 27.72/4.01      ( v5_relat_1(sK2,X0)
% 27.72/4.01      | k1_zfmisc_1(k2_zfmisc_1(X1,X0)) != k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)) ),
% 27.72/4.01      inference(unflattening,[status(thm)],[c_236]) ).
% 27.72/4.01  
% 27.72/4.01  cnf(c_291,plain,
% 27.72/4.01      ( r1_tarski(k2_relat_1(X0),X1)
% 27.72/4.01      | ~ v1_relat_1(X0)
% 27.72/4.01      | X2 != X1
% 27.72/4.01      | k1_zfmisc_1(k2_zfmisc_1(X3,X2)) != k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))
% 27.72/4.01      | sK2 != X0 ),
% 27.72/4.01      inference(resolution_lifted,[status(thm)],[c_13,c_237]) ).
% 27.72/4.01  
% 27.72/4.01  cnf(c_292,plain,
% 27.72/4.01      ( r1_tarski(k2_relat_1(sK2),X0)
% 27.72/4.01      | ~ v1_relat_1(sK2)
% 27.72/4.01      | k1_zfmisc_1(k2_zfmisc_1(X1,X0)) != k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)) ),
% 27.72/4.01      inference(unflattening,[status(thm)],[c_291]) ).
% 27.72/4.01  
% 27.72/4.01  cnf(c_722,plain,
% 27.72/4.01      ( k1_zfmisc_1(k2_zfmisc_1(X0,X1)) != k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))
% 27.72/4.01      | r1_tarski(k2_relat_1(sK2),X1) = iProver_top
% 27.72/4.01      | v1_relat_1(sK2) != iProver_top ),
% 27.72/4.01      inference(predicate_to_equality,[status(thm)],[c_292]) ).
% 27.72/4.01  
% 27.72/4.01  cnf(c_897,plain,
% 27.72/4.01      ( r1_tarski(k2_relat_1(sK2),sK1) = iProver_top
% 27.72/4.01      | v1_relat_1(sK2) != iProver_top ),
% 27.72/4.01      inference(equality_resolution,[status(thm)],[c_722]) ).
% 27.72/4.01  
% 27.72/4.01  cnf(c_0,plain,
% 27.72/4.01      ( ~ r1_tarski(X0,X1) | k4_xboole_0(X0,X1) = k1_xboole_0 ),
% 27.72/4.01      inference(cnf_transformation,[],[f32]) ).
% 27.72/4.01  
% 27.72/4.01  cnf(c_731,plain,
% 27.72/4.01      ( k4_xboole_0(X0,X1) = k1_xboole_0
% 27.72/4.01      | r1_tarski(X0,X1) != iProver_top ),
% 27.72/4.01      inference(predicate_to_equality,[status(thm)],[c_0]) ).
% 27.72/4.01  
% 27.72/4.01  cnf(c_1643,plain,
% 27.72/4.01      ( k4_xboole_0(k2_relat_1(sK2),sK1) = k1_xboole_0
% 27.72/4.01      | v1_relat_1(sK2) != iProver_top ),
% 27.72/4.01      inference(superposition,[status(thm)],[c_897,c_731]) ).
% 27.72/4.01  
% 27.72/4.01  cnf(c_9,plain,
% 27.72/4.01      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
% 27.72/4.01      | ~ v1_relat_1(X1)
% 27.72/4.01      | v1_relat_1(X0) ),
% 27.72/4.01      inference(cnf_transformation,[],[f42]) ).
% 27.72/4.01  
% 27.72/4.01  cnf(c_221,plain,
% 27.72/4.01      ( ~ v1_relat_1(X0)
% 27.72/4.01      | v1_relat_1(X1)
% 27.72/4.01      | k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)) != k1_zfmisc_1(X0)
% 27.72/4.01      | sK2 != X1 ),
% 27.72/4.01      inference(resolution_lifted,[status(thm)],[c_9,c_19]) ).
% 27.72/4.01  
% 27.72/4.01  cnf(c_222,plain,
% 27.72/4.01      ( ~ v1_relat_1(X0)
% 27.72/4.01      | v1_relat_1(sK2)
% 27.72/4.01      | k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)) != k1_zfmisc_1(X0) ),
% 27.72/4.01      inference(unflattening,[status(thm)],[c_221]) ).
% 27.72/4.01  
% 27.72/4.01  cnf(c_724,plain,
% 27.72/4.01      ( k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)) != k1_zfmisc_1(X0)
% 27.72/4.01      | v1_relat_1(X0) != iProver_top
% 27.72/4.01      | v1_relat_1(sK2) = iProver_top ),
% 27.72/4.01      inference(predicate_to_equality,[status(thm)],[c_222]) ).
% 27.72/4.01  
% 27.72/4.01  cnf(c_852,plain,
% 27.72/4.01      ( v1_relat_1(k2_zfmisc_1(sK0,sK1)) != iProver_top
% 27.72/4.01      | v1_relat_1(sK2) = iProver_top ),
% 27.72/4.01      inference(equality_resolution,[status(thm)],[c_724]) ).
% 27.72/4.01  
% 27.72/4.01  cnf(c_15,plain,
% 27.72/4.01      ( v1_relat_1(k2_zfmisc_1(X0,X1)) ),
% 27.72/4.01      inference(cnf_transformation,[],[f48]) ).
% 27.72/4.01  
% 27.72/4.01  cnf(c_1063,plain,
% 27.72/4.01      ( v1_relat_1(k2_zfmisc_1(sK0,sK1)) ),
% 27.72/4.01      inference(instantiation,[status(thm)],[c_15]) ).
% 27.72/4.01  
% 27.72/4.01  cnf(c_1064,plain,
% 27.72/4.01      ( v1_relat_1(k2_zfmisc_1(sK0,sK1)) = iProver_top ),
% 27.72/4.01      inference(predicate_to_equality,[status(thm)],[c_1063]) ).
% 27.72/4.01  
% 27.72/4.01  cnf(c_2203,plain,
% 27.72/4.01      ( k4_xboole_0(k2_relat_1(sK2),sK1) = k1_xboole_0 ),
% 27.72/4.01      inference(global_propositional_subsumption,
% 27.72/4.01                [status(thm)],
% 27.72/4.01                [c_1643,c_852,c_1064]) ).
% 27.72/4.01  
% 27.72/4.01  cnf(c_2207,plain,
% 27.72/4.01      ( k3_tarski(k1_enumset1(sK1,sK1,k2_relat_1(sK2))) = k5_xboole_0(sK1,k1_xboole_0) ),
% 27.72/4.01      inference(superposition,[status(thm)],[c_2203,c_8]) ).
% 27.72/4.01  
% 27.72/4.01  cnf(c_6,plain,
% 27.72/4.01      ( k5_xboole_0(k5_xboole_0(X0,k4_xboole_0(X1,X0)),k4_xboole_0(X2,k5_xboole_0(X0,k4_xboole_0(X1,X0)))) = k5_xboole_0(X0,k4_xboole_0(k5_xboole_0(X1,k4_xboole_0(X2,X1)),X0)) ),
% 27.72/4.01      inference(cnf_transformation,[],[f56]) ).
% 27.72/4.01  
% 27.72/4.01  cnf(c_786,plain,
% 27.72/4.01      ( k5_xboole_0(k3_tarski(k1_enumset1(X0,X0,X1)),k4_xboole_0(X2,k3_tarski(k1_enumset1(X0,X0,X1)))) = k5_xboole_0(X0,k4_xboole_0(k5_xboole_0(X1,k4_xboole_0(X2,X1)),X0)) ),
% 27.72/4.01      inference(light_normalisation,[status(thm)],[c_6,c_8]) ).
% 27.72/4.01  
% 27.72/4.01  cnf(c_787,plain,
% 27.72/4.01      ( k5_xboole_0(k3_tarski(k1_enumset1(X0,X0,X1)),k4_xboole_0(X2,k3_tarski(k1_enumset1(X0,X0,X1)))) = k3_tarski(k1_enumset1(X0,X0,k3_tarski(k1_enumset1(X1,X1,X2)))) ),
% 27.72/4.01      inference(demodulation,[status(thm)],[c_786,c_8]) ).
% 27.72/4.01  
% 27.72/4.01  cnf(c_2681,plain,
% 27.72/4.01      ( k3_tarski(k1_enumset1(sK1,sK1,k3_tarski(k1_enumset1(k2_relat_1(sK2),k2_relat_1(sK2),X0)))) = k5_xboole_0(k5_xboole_0(sK1,k1_xboole_0),k4_xboole_0(X0,k5_xboole_0(sK1,k1_xboole_0))) ),
% 27.72/4.01      inference(superposition,[status(thm)],[c_2207,c_787]) ).
% 27.72/4.01  
% 27.72/4.01  cnf(c_2696,plain,
% 27.72/4.01      ( k3_tarski(k1_enumset1(sK1,sK1,k3_tarski(k1_enumset1(k2_relat_1(sK2),k2_relat_1(sK2),X0)))) = k3_tarski(k1_enumset1(k5_xboole_0(sK1,k1_xboole_0),k5_xboole_0(sK1,k1_xboole_0),X0)) ),
% 27.72/4.01      inference(demodulation,[status(thm)],[c_2681,c_8]) ).
% 27.72/4.01  
% 27.72/4.01  cnf(c_2920,plain,
% 27.72/4.01      ( k3_tarski(k1_enumset1(k5_xboole_0(sK1,k1_xboole_0),k5_xboole_0(sK1,k1_xboole_0),k2_relat_1(sK2))) = k3_tarski(k1_enumset1(sK1,sK1,k2_relat_1(sK2))) ),
% 27.72/4.01      inference(superposition,[status(thm)],[c_1430,c_2696]) ).
% 27.72/4.01  
% 27.72/4.01  cnf(c_2962,plain,
% 27.72/4.01      ( k3_tarski(k1_enumset1(k5_xboole_0(sK1,k1_xboole_0),k5_xboole_0(sK1,k1_xboole_0),k2_relat_1(sK2))) = k5_xboole_0(sK1,k1_xboole_0) ),
% 27.72/4.01      inference(light_normalisation,[status(thm)],[c_2920,c_2207]) ).
% 27.72/4.01  
% 27.72/4.01  cnf(c_7363,plain,
% 27.72/4.01      ( k3_tarski(k1_enumset1(k2_relat_1(sK2),k2_relat_1(sK2),k5_xboole_0(sK1,k1_xboole_0))) = k5_xboole_0(sK1,k1_xboole_0) ),
% 27.72/4.01      inference(superposition,[status(thm)],[c_7,c_2962]) ).
% 27.72/4.01  
% 27.72/4.01  cnf(c_3,plain,
% 27.72/4.01      ( r1_tarski(k1_xboole_0,X0) ),
% 27.72/4.01      inference(cnf_transformation,[],[f34]) ).
% 27.72/4.01  
% 27.72/4.01  cnf(c_729,plain,
% 27.72/4.01      ( r1_tarski(k1_xboole_0,X0) = iProver_top ),
% 27.72/4.01      inference(predicate_to_equality,[status(thm)],[c_3]) ).
% 27.72/4.01  
% 27.72/4.01  cnf(c_1642,plain,
% 27.72/4.01      ( k4_xboole_0(k1_xboole_0,X0) = k1_xboole_0 ),
% 27.72/4.01      inference(superposition,[status(thm)],[c_729,c_731]) ).
% 27.72/4.01  
% 27.72/4.01  cnf(c_7624,plain,
% 27.72/4.01      ( k5_xboole_0(X0,k1_xboole_0) = X0 ),
% 27.72/4.01      inference(demodulation,[status(thm)],[c_1642,c_2]) ).
% 27.72/4.01  
% 27.72/4.01  cnf(c_7763,plain,
% 27.72/4.01      ( k3_tarski(k1_enumset1(k2_relat_1(sK2),k2_relat_1(sK2),sK1)) = sK1 ),
% 27.72/4.01      inference(demodulation,[status(thm)],[c_7363,c_7624]) ).
% 27.72/4.01  
% 27.72/4.01  cnf(c_7769,plain,
% 27.72/4.01      ( k3_tarski(k1_enumset1(k2_relat_1(sK2),k2_relat_1(sK2),k3_tarski(k1_enumset1(sK1,sK1,X0)))) = k5_xboole_0(sK1,k4_xboole_0(X0,sK1)) ),
% 27.72/4.01      inference(superposition,[status(thm)],[c_7763,c_787]) ).
% 27.72/4.01  
% 27.72/4.01  cnf(c_7791,plain,
% 27.72/4.01      ( k3_tarski(k1_enumset1(k2_relat_1(sK2),k2_relat_1(sK2),k3_tarski(k1_enumset1(sK1,sK1,X0)))) = k3_tarski(k1_enumset1(sK1,sK1,X0)) ),
% 27.72/4.01      inference(demodulation,[status(thm)],[c_7769,c_8]) ).
% 27.72/4.01  
% 27.72/4.01  cnf(c_726,plain,
% 27.72/4.01      ( v1_relat_1(k2_zfmisc_1(X0,X1)) = iProver_top ),
% 27.72/4.01      inference(predicate_to_equality,[status(thm)],[c_15]) ).
% 27.72/4.01  
% 27.72/4.01  cnf(c_1163,plain,
% 27.72/4.01      ( v1_relat_1(sK2) = iProver_top ),
% 27.72/4.01      inference(superposition,[status(thm)],[c_726,c_852]) ).
% 27.72/4.01  
% 27.72/4.01  cnf(c_14,plain,
% 27.72/4.01      ( ~ v1_relat_1(X0)
% 27.72/4.01      | k5_xboole_0(k1_relat_1(X0),k4_xboole_0(k2_relat_1(X0),k1_relat_1(X0))) = k3_relat_1(X0) ),
% 27.72/4.01      inference(cnf_transformation,[],[f59]) ).
% 27.72/4.01  
% 27.72/4.01  cnf(c_727,plain,
% 27.72/4.01      ( k5_xboole_0(k1_relat_1(X0),k4_xboole_0(k2_relat_1(X0),k1_relat_1(X0))) = k3_relat_1(X0)
% 27.72/4.01      | v1_relat_1(X0) != iProver_top ),
% 27.72/4.01      inference(predicate_to_equality,[status(thm)],[c_14]) ).
% 27.72/4.01  
% 27.72/4.01  cnf(c_758,plain,
% 27.72/4.01      ( k3_tarski(k1_enumset1(k1_relat_1(X0),k1_relat_1(X0),k2_relat_1(X0))) = k3_relat_1(X0)
% 27.72/4.01      | v1_relat_1(X0) != iProver_top ),
% 27.72/4.01      inference(demodulation,[status(thm)],[c_727,c_8]) ).
% 27.72/4.01  
% 27.72/4.01  cnf(c_1904,plain,
% 27.72/4.01      ( k3_tarski(k1_enumset1(k1_relat_1(sK2),k1_relat_1(sK2),k2_relat_1(sK2))) = k3_relat_1(sK2) ),
% 27.72/4.01      inference(superposition,[status(thm)],[c_1163,c_758]) ).
% 27.72/4.01  
% 27.72/4.01  cnf(c_2685,plain,
% 27.72/4.01      ( k3_tarski(k1_enumset1(k3_tarski(k1_enumset1(X0,X0,X1)),k3_tarski(k1_enumset1(X0,X0,X1)),X2)) = k3_tarski(k1_enumset1(X0,X0,k3_tarski(k1_enumset1(X1,X1,X2)))) ),
% 27.72/4.01      inference(superposition,[status(thm)],[c_787,c_8]) ).
% 27.72/4.01  
% 27.72/4.01  cnf(c_12319,plain,
% 27.72/4.01      ( k3_tarski(k1_enumset1(X0,X0,k3_tarski(k1_enumset1(X1,X1,X2)))) = k3_tarski(k1_enumset1(X2,X2,k3_tarski(k1_enumset1(X0,X0,X1)))) ),
% 27.72/4.01      inference(superposition,[status(thm)],[c_7,c_2685]) ).
% 27.72/4.01  
% 27.72/4.01  cnf(c_12678,plain,
% 27.72/4.01      ( k3_tarski(k1_enumset1(k1_relat_1(sK2),k1_relat_1(sK2),k3_tarski(k1_enumset1(k2_relat_1(sK2),k2_relat_1(sK2),X0)))) = k3_tarski(k1_enumset1(X0,X0,k3_relat_1(sK2))) ),
% 27.72/4.01      inference(superposition,[status(thm)],[c_1904,c_12319]) ).
% 27.72/4.01  
% 27.72/4.01  cnf(c_13676,plain,
% 27.72/4.01      ( k3_tarski(k1_enumset1(k3_tarski(k1_enumset1(sK1,sK1,X0)),k3_tarski(k1_enumset1(sK1,sK1,X0)),k3_relat_1(sK2))) = k3_tarski(k1_enumset1(k1_relat_1(sK2),k1_relat_1(sK2),k3_tarski(k1_enumset1(sK1,sK1,X0)))) ),
% 27.72/4.01      inference(superposition,[status(thm)],[c_7791,c_12678]) ).
% 27.72/4.01  
% 27.72/4.01  cnf(c_12632,plain,
% 27.72/4.01      ( k3_tarski(k1_enumset1(k3_tarski(k1_enumset1(X0,X0,X1)),k3_tarski(k1_enumset1(X0,X0,X1)),X2)) = k3_tarski(k1_enumset1(X1,X1,k3_tarski(k1_enumset1(X2,X2,X0)))) ),
% 27.72/4.01      inference(superposition,[status(thm)],[c_7,c_12319]) ).
% 27.72/4.01  
% 27.72/4.01  cnf(c_16720,plain,
% 27.72/4.01      ( k3_tarski(k1_enumset1(k3_tarski(k1_enumset1(X0,X0,X1)),k3_tarski(k1_enumset1(X0,X0,X1)),X2)) = k3_tarski(k1_enumset1(k3_tarski(k1_enumset1(X2,X2,X0)),k3_tarski(k1_enumset1(X2,X2,X0)),X1)) ),
% 27.72/4.01      inference(superposition,[status(thm)],[c_7,c_12632]) ).
% 27.72/4.01  
% 27.72/4.01  cnf(c_20341,plain,
% 27.72/4.01      ( k3_tarski(k1_enumset1(k3_tarski(k1_enumset1(X0,X0,k1_relat_1(sK2))),k3_tarski(k1_enumset1(X0,X0,k1_relat_1(sK2))),k2_relat_1(sK2))) = k3_tarski(k1_enumset1(k3_relat_1(sK2),k3_relat_1(sK2),X0)) ),
% 27.72/4.01      inference(superposition,[status(thm)],[c_1904,c_16720]) ).
% 27.72/4.01  
% 27.72/4.01  cnf(c_20445,plain,
% 27.72/4.01      ( k3_tarski(k1_enumset1(k3_tarski(k1_enumset1(X0,X0,X1)),k3_tarski(k1_enumset1(X0,X0,X1)),X2)) = k3_tarski(k1_enumset1(k3_tarski(k1_enumset1(X0,X0,X2)),k3_tarski(k1_enumset1(X0,X0,X2)),X1)) ),
% 27.72/4.01      inference(superposition,[status(thm)],[c_7,c_16720]) ).
% 27.72/4.01  
% 27.72/4.01  cnf(c_23989,plain,
% 27.72/4.01      ( k3_tarski(k1_enumset1(k3_tarski(k1_enumset1(k3_tarski(k1_enumset1(X0,X0,k1_relat_1(sK2))),k3_tarski(k1_enumset1(X0,X0,k1_relat_1(sK2))),X1)),k3_tarski(k1_enumset1(k3_tarski(k1_enumset1(X0,X0,k1_relat_1(sK2))),k3_tarski(k1_enumset1(X0,X0,k1_relat_1(sK2))),X1)),k2_relat_1(sK2))) = k3_tarski(k1_enumset1(k3_tarski(k1_enumset1(k3_relat_1(sK2),k3_relat_1(sK2),X0)),k3_tarski(k1_enumset1(k3_relat_1(sK2),k3_relat_1(sK2),X0)),X1)) ),
% 27.72/4.01      inference(superposition,[status(thm)],[c_20341,c_20445]) ).
% 27.72/4.01  
% 27.72/4.01  cnf(c_2682,plain,
% 27.72/4.01      ( k5_xboole_0(k3_tarski(k1_enumset1(X0,X0,X1)),k4_xboole_0(X2,k3_tarski(k1_enumset1(X0,X0,X1)))) = k3_tarski(k1_enumset1(X1,X1,k3_tarski(k1_enumset1(X0,X0,X2)))) ),
% 27.72/4.01      inference(superposition,[status(thm)],[c_7,c_787]) ).
% 27.72/4.01  
% 27.72/4.01  cnf(c_12215,plain,
% 27.72/4.01      ( k3_tarski(k1_enumset1(k3_tarski(k1_enumset1(X0,X0,X1)),k3_tarski(k1_enumset1(X0,X0,X1)),X2)) = k3_tarski(k1_enumset1(X1,X1,k3_tarski(k1_enumset1(X0,X0,X2)))) ),
% 27.72/4.01      inference(superposition,[status(thm)],[c_2682,c_8]) ).
% 27.72/4.01  
% 27.72/4.01  cnf(c_24283,plain,
% 27.72/4.01      ( k3_tarski(k1_enumset1(k3_tarski(k1_enumset1(X0,X0,X1)),k3_tarski(k1_enumset1(X0,X0,X1)),k3_tarski(k1_enumset1(k1_relat_1(sK2),k1_relat_1(sK2),k2_relat_1(sK2))))) = k3_tarski(k1_enumset1(X0,X0,k3_tarski(k1_enumset1(k3_relat_1(sK2),k3_relat_1(sK2),X1)))) ),
% 27.72/4.01      inference(demodulation,[status(thm)],[c_23989,c_12215]) ).
% 27.72/4.01  
% 27.72/4.01  cnf(c_24284,plain,
% 27.72/4.01      ( k3_tarski(k1_enumset1(k3_tarski(k1_enumset1(X0,X0,X1)),k3_tarski(k1_enumset1(X0,X0,X1)),k3_relat_1(sK2))) = k3_tarski(k1_enumset1(X0,X0,k3_tarski(k1_enumset1(k3_relat_1(sK2),k3_relat_1(sK2),X1)))) ),
% 27.72/4.01      inference(light_normalisation,[status(thm)],[c_24283,c_1904]) ).
% 27.72/4.01  
% 27.72/4.01  cnf(c_79780,plain,
% 27.72/4.01      ( k3_tarski(k1_enumset1(k1_relat_1(sK2),k1_relat_1(sK2),k3_tarski(k1_enumset1(sK1,sK1,X0)))) = k3_tarski(k1_enumset1(sK1,sK1,k3_tarski(k1_enumset1(k3_relat_1(sK2),k3_relat_1(sK2),X0)))) ),
% 27.72/4.01      inference(demodulation,[status(thm)],[c_13676,c_24284]) ).
% 27.72/4.01  
% 27.72/4.01  cnf(c_12640,plain,
% 27.72/4.01      ( k3_tarski(k1_enumset1(k2_relat_1(sK2),k2_relat_1(sK2),k3_tarski(k1_enumset1(X0,X0,k1_relat_1(sK2))))) = k3_tarski(k1_enumset1(X0,X0,k3_relat_1(sK2))) ),
% 27.72/4.01      inference(superposition,[status(thm)],[c_1904,c_12319]) ).
% 27.72/4.01  
% 27.72/4.01  cnf(c_13569,plain,
% 27.72/4.01      ( k4_xboole_0(k3_tarski(k1_enumset1(X0,X0,k3_relat_1(sK2))),k3_tarski(k1_enumset1(X0,X0,k1_relat_1(sK2)))) = k4_xboole_0(k2_relat_1(sK2),k3_tarski(k1_enumset1(X0,X0,k1_relat_1(sK2)))) ),
% 27.72/4.01      inference(superposition,[status(thm)],[c_12640,c_747]) ).
% 27.72/4.01  
% 27.72/4.01  cnf(c_45408,plain,
% 27.72/4.01      ( k4_xboole_0(k3_tarski(k1_enumset1(X0,X0,k3_relat_1(sK2))),k3_tarski(k1_enumset1(k1_relat_1(sK2),k1_relat_1(sK2),X0))) = k4_xboole_0(k2_relat_1(sK2),k3_tarski(k1_enumset1(X0,X0,k1_relat_1(sK2)))) ),
% 27.72/4.01      inference(superposition,[status(thm)],[c_7,c_13569]) ).
% 27.72/4.01  
% 27.72/4.01  cnf(c_79870,plain,
% 27.72/4.01      ( k4_xboole_0(k3_tarski(k1_enumset1(k3_tarski(k1_enumset1(sK1,sK1,X0)),k3_tarski(k1_enumset1(sK1,sK1,X0)),k3_relat_1(sK2))),k3_tarski(k1_enumset1(sK1,sK1,k3_tarski(k1_enumset1(k3_relat_1(sK2),k3_relat_1(sK2),X0))))) = k4_xboole_0(k2_relat_1(sK2),k3_tarski(k1_enumset1(k3_tarski(k1_enumset1(sK1,sK1,X0)),k3_tarski(k1_enumset1(sK1,sK1,X0)),k1_relat_1(sK2)))) ),
% 27.72/4.01      inference(superposition,[status(thm)],[c_79780,c_45408]) ).
% 27.72/4.01  
% 27.72/4.01  cnf(c_1,plain,
% 27.72/4.01      ( r1_tarski(X0,X1) | k4_xboole_0(X0,X1) != k1_xboole_0 ),
% 27.72/4.01      inference(cnf_transformation,[],[f31]) ).
% 27.72/4.01  
% 27.72/4.01  cnf(c_730,plain,
% 27.72/4.01      ( k4_xboole_0(X0,X1) != k1_xboole_0
% 27.72/4.01      | r1_tarski(X0,X1) = iProver_top ),
% 27.72/4.01      inference(predicate_to_equality,[status(thm)],[c_1]) ).
% 27.72/4.01  
% 27.72/4.01  cnf(c_1620,plain,
% 27.72/4.01      ( k4_xboole_0(k1_xboole_0,X0) != k1_xboole_0
% 27.72/4.01      | r1_tarski(X0,X0) = iProver_top ),
% 27.72/4.01      inference(superposition,[status(thm)],[c_1350,c_730]) ).
% 27.72/4.01  
% 27.72/4.01  cnf(c_5113,plain,
% 27.72/4.01      ( r1_tarski(X0,X0) = iProver_top ),
% 27.72/4.01      inference(global_propositional_subsumption,
% 27.72/4.01                [status(thm)],
% 27.72/4.01                [c_1620,c_1642]) ).
% 27.72/4.01  
% 27.72/4.01  cnf(c_5118,plain,
% 27.72/4.01      ( k4_xboole_0(X0,X0) = k1_xboole_0 ),
% 27.72/4.01      inference(superposition,[status(thm)],[c_5113,c_731]) ).
% 27.72/4.01  
% 27.72/4.01  cnf(c_79961,plain,
% 27.72/4.01      ( k4_xboole_0(k2_relat_1(sK2),k3_tarski(k1_enumset1(X0,X0,k3_tarski(k1_enumset1(sK1,sK1,k1_relat_1(sK2)))))) = k1_xboole_0 ),
% 27.72/4.01      inference(demodulation,
% 27.72/4.01                [status(thm)],
% 27.72/4.01                [c_79870,c_5118,c_12215,c_24284]) ).
% 27.72/4.01  
% 27.72/4.01  cnf(c_80332,plain,
% 27.72/4.01      ( k3_tarski(k1_enumset1(X0,X0,k3_tarski(k1_enumset1(k3_tarski(k1_enumset1(sK1,sK1,k1_relat_1(sK2))),k3_tarski(k1_enumset1(sK1,sK1,k1_relat_1(sK2))),k2_relat_1(sK2))))) = k5_xboole_0(k3_tarski(k1_enumset1(X0,X0,k3_tarski(k1_enumset1(sK1,sK1,k1_relat_1(sK2))))),k1_xboole_0) ),
% 27.72/4.01      inference(superposition,[status(thm)],[c_79961,c_787]) ).
% 27.72/4.01  
% 27.72/4.01  cnf(c_80370,plain,
% 27.72/4.01      ( k3_tarski(k1_enumset1(X0,X0,k3_tarski(k1_enumset1(k3_relat_1(sK2),k3_relat_1(sK2),sK1)))) = k3_tarski(k1_enumset1(X0,X0,k3_tarski(k1_enumset1(sK1,sK1,k1_relat_1(sK2))))) ),
% 27.72/4.01      inference(demodulation,[status(thm)],[c_80332,c_7624,c_20341]) ).
% 27.72/4.01  
% 27.72/4.01  cnf(c_11,plain,
% 27.72/4.01      ( ~ v4_relat_1(X0,X1)
% 27.72/4.01      | r1_tarski(k1_relat_1(X0),X1)
% 27.72/4.01      | ~ v1_relat_1(X0) ),
% 27.72/4.01      inference(cnf_transformation,[],[f43]) ).
% 27.72/4.01  
% 27.72/4.01  cnf(c_17,plain,
% 27.72/4.01      ( v4_relat_1(X0,X1)
% 27.72/4.01      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) ),
% 27.72/4.01      inference(cnf_transformation,[],[f49]) ).
% 27.72/4.01  
% 27.72/4.01  cnf(c_248,plain,
% 27.72/4.01      ( v4_relat_1(X0,X1)
% 27.72/4.01      | k1_zfmisc_1(k2_zfmisc_1(X1,X2)) != k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))
% 27.72/4.01      | sK2 != X0 ),
% 27.72/4.01      inference(resolution_lifted,[status(thm)],[c_17,c_19]) ).
% 27.72/4.01  
% 27.72/4.01  cnf(c_249,plain,
% 27.72/4.01      ( v4_relat_1(sK2,X0)
% 27.72/4.01      | k1_zfmisc_1(k2_zfmisc_1(X0,X1)) != k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)) ),
% 27.72/4.01      inference(unflattening,[status(thm)],[c_248]) ).
% 27.72/4.01  
% 27.72/4.01  cnf(c_271,plain,
% 27.72/4.01      ( r1_tarski(k1_relat_1(X0),X1)
% 27.72/4.01      | ~ v1_relat_1(X0)
% 27.72/4.01      | X2 != X1
% 27.72/4.01      | k1_zfmisc_1(k2_zfmisc_1(X2,X3)) != k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))
% 27.72/4.01      | sK2 != X0 ),
% 27.72/4.01      inference(resolution_lifted,[status(thm)],[c_11,c_249]) ).
% 27.72/4.01  
% 27.72/4.01  cnf(c_272,plain,
% 27.72/4.01      ( r1_tarski(k1_relat_1(sK2),X0)
% 27.72/4.01      | ~ v1_relat_1(sK2)
% 27.72/4.01      | k1_zfmisc_1(k2_zfmisc_1(X0,X1)) != k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)) ),
% 27.72/4.01      inference(unflattening,[status(thm)],[c_271]) ).
% 27.72/4.01  
% 27.72/4.01  cnf(c_723,plain,
% 27.72/4.01      ( k1_zfmisc_1(k2_zfmisc_1(X0,X1)) != k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))
% 27.72/4.01      | r1_tarski(k1_relat_1(sK2),X0) = iProver_top
% 27.72/4.01      | v1_relat_1(sK2) != iProver_top ),
% 27.72/4.01      inference(predicate_to_equality,[status(thm)],[c_272]) ).
% 27.72/4.01  
% 27.72/4.01  cnf(c_939,plain,
% 27.72/4.01      ( r1_tarski(k1_relat_1(sK2),sK0) = iProver_top
% 27.72/4.01      | v1_relat_1(sK2) != iProver_top ),
% 27.72/4.01      inference(equality_resolution,[status(thm)],[c_723]) ).
% 27.72/4.01  
% 27.72/4.01  cnf(c_1644,plain,
% 27.72/4.01      ( k4_xboole_0(k1_relat_1(sK2),sK0) = k1_xboole_0
% 27.72/4.01      | v1_relat_1(sK2) != iProver_top ),
% 27.72/4.01      inference(superposition,[status(thm)],[c_939,c_731]) ).
% 27.72/4.01  
% 27.72/4.01  cnf(c_2214,plain,
% 27.72/4.01      ( k4_xboole_0(k1_relat_1(sK2),sK0) = k1_xboole_0 ),
% 27.72/4.01      inference(global_propositional_subsumption,
% 27.72/4.01                [status(thm)],
% 27.72/4.01                [c_1644,c_852,c_1064]) ).
% 27.72/4.01  
% 27.72/4.01  cnf(c_2218,plain,
% 27.72/4.01      ( k3_tarski(k1_enumset1(sK0,sK0,k1_relat_1(sK2))) = k5_xboole_0(sK0,k1_xboole_0) ),
% 27.72/4.01      inference(superposition,[status(thm)],[c_2214,c_8]) ).
% 27.72/4.01  
% 27.72/4.01  cnf(c_2730,plain,
% 27.72/4.01      ( k3_tarski(k1_enumset1(sK0,sK0,k3_tarski(k1_enumset1(k1_relat_1(sK2),k1_relat_1(sK2),X0)))) = k5_xboole_0(k5_xboole_0(sK0,k1_xboole_0),k4_xboole_0(X0,k5_xboole_0(sK0,k1_xboole_0))) ),
% 27.72/4.01      inference(superposition,[status(thm)],[c_2218,c_787]) ).
% 27.72/4.01  
% 27.72/4.01  cnf(c_2752,plain,
% 27.72/4.01      ( k3_tarski(k1_enumset1(sK0,sK0,k3_tarski(k1_enumset1(k1_relat_1(sK2),k1_relat_1(sK2),X0)))) = k3_tarski(k1_enumset1(k5_xboole_0(sK0,k1_xboole_0),k5_xboole_0(sK0,k1_xboole_0),X0)) ),
% 27.72/4.01      inference(demodulation,[status(thm)],[c_2730,c_8]) ).
% 27.72/4.01  
% 27.72/4.01  cnf(c_4213,plain,
% 27.72/4.01      ( k3_tarski(k1_enumset1(k5_xboole_0(sK0,k1_xboole_0),k5_xboole_0(sK0,k1_xboole_0),k1_relat_1(sK2))) = k3_tarski(k1_enumset1(sK0,sK0,k1_relat_1(sK2))) ),
% 27.72/4.01      inference(superposition,[status(thm)],[c_1430,c_2752]) ).
% 27.72/4.01  
% 27.72/4.01  cnf(c_4267,plain,
% 27.72/4.01      ( k3_tarski(k1_enumset1(k5_xboole_0(sK0,k1_xboole_0),k5_xboole_0(sK0,k1_xboole_0),k1_relat_1(sK2))) = k5_xboole_0(sK0,k1_xboole_0) ),
% 27.72/4.01      inference(light_normalisation,[status(thm)],[c_4213,c_2218]) ).
% 27.72/4.01  
% 27.72/4.01  cnf(c_7529,plain,
% 27.72/4.01      ( k3_tarski(k1_enumset1(k1_relat_1(sK2),k1_relat_1(sK2),k5_xboole_0(sK0,k1_xboole_0))) = k5_xboole_0(sK0,k1_xboole_0) ),
% 27.72/4.01      inference(superposition,[status(thm)],[c_7,c_4267]) ).
% 27.72/4.01  
% 27.72/4.01  cnf(c_8078,plain,
% 27.72/4.01      ( k3_tarski(k1_enumset1(k1_relat_1(sK2),k1_relat_1(sK2),sK0)) = sK0 ),
% 27.72/4.01      inference(demodulation,[status(thm)],[c_7529,c_7624]) ).
% 27.72/4.01  
% 27.72/4.01  cnf(c_8084,plain,
% 27.72/4.01      ( k3_tarski(k1_enumset1(k1_relat_1(sK2),k1_relat_1(sK2),k3_tarski(k1_enumset1(sK0,sK0,X0)))) = k5_xboole_0(sK0,k4_xboole_0(X0,sK0)) ),
% 27.72/4.01      inference(superposition,[status(thm)],[c_8078,c_787]) ).
% 27.72/4.01  
% 27.72/4.01  cnf(c_8103,plain,
% 27.72/4.01      ( k3_tarski(k1_enumset1(k1_relat_1(sK2),k1_relat_1(sK2),k3_tarski(k1_enumset1(sK0,sK0,X0)))) = k3_tarski(k1_enumset1(sK0,sK0,X0)) ),
% 27.72/4.01      inference(demodulation,[status(thm)],[c_8084,c_8]) ).
% 27.72/4.01  
% 27.72/4.01  cnf(c_9268,plain,
% 27.72/4.01      ( k3_tarski(k1_enumset1(k1_relat_1(sK2),k1_relat_1(sK2),k3_tarski(k1_enumset1(X0,X0,sK0)))) = k3_tarski(k1_enumset1(sK0,sK0,X0)) ),
% 27.72/4.01      inference(superposition,[status(thm)],[c_7,c_8103]) ).
% 27.72/4.01  
% 27.72/4.01  cnf(c_1351,plain,
% 27.72/4.01      ( k4_xboole_0(k3_tarski(k1_enumset1(X0,X0,X1)),X0) = k4_xboole_0(X1,X0) ),
% 27.72/4.01      inference(superposition,[status(thm)],[c_7,c_747]) ).
% 27.72/4.01  
% 27.72/4.01  cnf(c_24845,plain,
% 27.72/4.01      ( k4_xboole_0(k3_tarski(k1_enumset1(X0,X0,k3_tarski(k1_enumset1(k3_relat_1(sK2),k3_relat_1(sK2),X1)))),k3_tarski(k1_enumset1(X0,X0,X1))) = k4_xboole_0(k3_relat_1(sK2),k3_tarski(k1_enumset1(X0,X0,X1))) ),
% 27.72/4.01      inference(superposition,[status(thm)],[c_24284,c_1351]) ).
% 27.72/4.01  
% 27.72/4.01  cnf(c_85609,plain,
% 27.72/4.01      ( k4_xboole_0(k3_tarski(k1_enumset1(X0,X0,k3_tarski(k1_enumset1(k3_relat_1(sK2),k3_relat_1(sK2),X1)))),k3_tarski(k1_enumset1(X1,X1,X0))) = k4_xboole_0(k3_relat_1(sK2),k3_tarski(k1_enumset1(X0,X0,X1))) ),
% 27.72/4.01      inference(superposition,[status(thm)],[c_7,c_24845]) ).
% 27.72/4.01  
% 27.72/4.01  cnf(c_91696,plain,
% 27.72/4.01      ( k4_xboole_0(k3_tarski(k1_enumset1(X0,X0,k3_tarski(k1_enumset1(X1,X1,k3_relat_1(sK2))))),k3_tarski(k1_enumset1(X1,X1,X0))) = k4_xboole_0(k3_relat_1(sK2),k3_tarski(k1_enumset1(X0,X0,X1))) ),
% 27.72/4.01      inference(superposition,[status(thm)],[c_7,c_85609]) ).
% 27.72/4.01  
% 27.72/4.01  cnf(c_92502,plain,
% 27.72/4.01      ( k4_xboole_0(k3_tarski(k1_enumset1(k3_tarski(k1_enumset1(X0,X0,sK0)),k3_tarski(k1_enumset1(X0,X0,sK0)),k3_tarski(k1_enumset1(k1_relat_1(sK2),k1_relat_1(sK2),k3_relat_1(sK2))))),k3_tarski(k1_enumset1(sK0,sK0,X0))) = k4_xboole_0(k3_relat_1(sK2),k3_tarski(k1_enumset1(k3_tarski(k1_enumset1(X0,X0,sK0)),k3_tarski(k1_enumset1(X0,X0,sK0)),k1_relat_1(sK2)))) ),
% 27.72/4.01      inference(superposition,[status(thm)],[c_9268,c_91696]) ).
% 27.72/4.01  
% 27.72/4.01  cnf(c_1510,plain,
% 27.72/4.01      ( k3_tarski(k1_enumset1(X0,X0,k3_tarski(k1_enumset1(X0,X0,X1)))) = k5_xboole_0(X0,k4_xboole_0(X1,X0)) ),
% 27.72/4.01      inference(superposition,[status(thm)],[c_1351,c_8]) ).
% 27.72/4.01  
% 27.72/4.01  cnf(c_1512,plain,
% 27.72/4.01      ( k3_tarski(k1_enumset1(X0,X0,k3_tarski(k1_enumset1(X0,X0,X1)))) = k3_tarski(k1_enumset1(X0,X0,X1)) ),
% 27.72/4.01      inference(light_normalisation,[status(thm)],[c_1510,c_8]) ).
% 27.72/4.01  
% 27.72/4.01  cnf(c_2093,plain,
% 27.72/4.01      ( k3_tarski(k1_enumset1(k1_relat_1(sK2),k1_relat_1(sK2),k3_relat_1(sK2))) = k3_tarski(k1_enumset1(k1_relat_1(sK2),k1_relat_1(sK2),k2_relat_1(sK2))) ),
% 27.72/4.01      inference(superposition,[status(thm)],[c_1904,c_1512]) ).
% 27.72/4.01  
% 27.72/4.01  cnf(c_2108,plain,
% 27.72/4.01      ( k3_tarski(k1_enumset1(k1_relat_1(sK2),k1_relat_1(sK2),k3_relat_1(sK2))) = k3_relat_1(sK2) ),
% 27.72/4.01      inference(light_normalisation,[status(thm)],[c_2093,c_1904]) ).
% 27.72/4.01  
% 27.72/4.01  cnf(c_92782,plain,
% 27.72/4.01      ( k4_xboole_0(k3_tarski(k1_enumset1(k3_tarski(k1_enumset1(X0,X0,sK0)),k3_tarski(k1_enumset1(X0,X0,sK0)),k3_relat_1(sK2))),k3_tarski(k1_enumset1(sK0,sK0,X0))) = k4_xboole_0(k3_relat_1(sK2),k3_tarski(k1_enumset1(k3_tarski(k1_enumset1(X0,X0,sK0)),k3_tarski(k1_enumset1(X0,X0,sK0)),k1_relat_1(sK2)))) ),
% 27.72/4.01      inference(light_normalisation,[status(thm)],[c_92502,c_2108]) ).
% 27.72/4.01  
% 27.72/4.01  cnf(c_92783,plain,
% 27.72/4.01      ( k4_xboole_0(k3_relat_1(sK2),k3_tarski(k1_enumset1(sK0,sK0,k3_tarski(k1_enumset1(X0,X0,k1_relat_1(sK2)))))) = k4_xboole_0(k3_relat_1(sK2),k3_tarski(k1_enumset1(X0,X0,sK0))) ),
% 27.72/4.01      inference(demodulation,
% 27.72/4.01                [status(thm)],
% 27.72/4.01                [c_92782,c_12215,c_24284,c_85609]) ).
% 27.72/4.01  
% 27.72/4.01  cnf(c_93522,plain,
% 27.72/4.01      ( k4_xboole_0(k3_relat_1(sK2),k3_tarski(k1_enumset1(sK0,sK0,k3_tarski(k1_enumset1(k1_relat_1(sK2),k1_relat_1(sK2),X0))))) = k4_xboole_0(k3_relat_1(sK2),k3_tarski(k1_enumset1(X0,X0,sK0))) ),
% 27.72/4.01      inference(superposition,[status(thm)],[c_7,c_92783]) ).
% 27.72/4.01  
% 27.72/4.01  cnf(c_98085,plain,
% 27.72/4.01      ( k4_xboole_0(k3_relat_1(sK2),k3_tarski(k1_enumset1(sK0,sK0,k3_tarski(k1_enumset1(k1_relat_1(sK2),k1_relat_1(sK2),X0))))) = k4_xboole_0(k3_relat_1(sK2),k3_tarski(k1_enumset1(sK0,sK0,X0))) ),
% 27.72/4.01      inference(superposition,[status(thm)],[c_7,c_93522]) ).
% 27.72/4.01  
% 27.72/4.01  cnf(c_98435,plain,
% 27.72/4.01      ( k4_xboole_0(k3_relat_1(sK2),k3_tarski(k1_enumset1(sK0,sK0,k3_tarski(k1_enumset1(k1_relat_1(sK2),k1_relat_1(sK2),k3_tarski(k1_enumset1(sK1,sK1,k1_relat_1(sK2)))))))) = k4_xboole_0(k3_relat_1(sK2),k3_tarski(k1_enumset1(sK0,sK0,k3_tarski(k1_enumset1(k3_relat_1(sK2),k3_relat_1(sK2),sK1))))) ),
% 27.72/4.01      inference(superposition,[status(thm)],[c_80370,c_98085]) ).
% 27.72/4.01  
% 27.72/4.01  cnf(c_98439,plain,
% 27.72/4.01      ( k4_xboole_0(k3_relat_1(sK2),k3_tarski(k1_enumset1(sK0,sK0,k3_tarski(k1_enumset1(X0,X0,k1_relat_1(sK2)))))) = k4_xboole_0(k3_relat_1(sK2),k3_tarski(k1_enumset1(sK0,sK0,X0))) ),
% 27.72/4.01      inference(superposition,[status(thm)],[c_7,c_98085]) ).
% 27.72/4.01  
% 27.72/4.01  cnf(c_98532,plain,
% 27.72/4.01      ( k4_xboole_0(k3_relat_1(sK2),k3_tarski(k1_enumset1(sK0,sK0,k3_tarski(k1_enumset1(k3_relat_1(sK2),k3_relat_1(sK2),sK1))))) = k4_xboole_0(k3_relat_1(sK2),k3_tarski(k1_enumset1(sK0,sK0,sK1))) ),
% 27.72/4.01      inference(demodulation,[status(thm)],[c_98435,c_98085,c_98439]) ).
% 27.72/4.01  
% 27.72/4.01  cnf(c_24770,plain,
% 27.72/4.01      ( k3_tarski(k1_enumset1(k1_xboole_0,k1_xboole_0,k3_tarski(k1_enumset1(k3_relat_1(sK2),k3_relat_1(sK2),X0)))) = k3_tarski(k1_enumset1(X0,X0,k3_relat_1(sK2))) ),
% 27.72/4.01      inference(superposition,[status(thm)],[c_1244,c_24284]) ).
% 27.72/4.01  
% 27.72/4.01  cnf(c_1758,plain,
% 27.72/4.01      ( k4_xboole_0(k3_tarski(k1_enumset1(X0,X0,X1)),k3_tarski(k1_enumset1(X0,X0,X1))) = k4_xboole_0(X0,k3_tarski(k1_enumset1(X0,X0,X1))) ),
% 27.72/4.01      inference(superposition,[status(thm)],[c_1512,c_747]) ).
% 27.72/4.01  
% 27.72/4.01  cnf(c_25321,plain,
% 27.72/4.01      ( k4_xboole_0(k3_tarski(k1_enumset1(X0,X0,k3_relat_1(sK2))),k3_tarski(k1_enumset1(X0,X0,k3_relat_1(sK2)))) = k4_xboole_0(k1_xboole_0,k3_tarski(k1_enumset1(k1_xboole_0,k1_xboole_0,k3_tarski(k1_enumset1(k3_relat_1(sK2),k3_relat_1(sK2),X0))))) ),
% 27.72/4.01      inference(superposition,[status(thm)],[c_24770,c_1758]) ).
% 27.72/4.01  
% 27.72/4.01  cnf(c_1353,plain,
% 27.72/4.01      ( k3_tarski(k1_enumset1(X0,X0,k3_tarski(k1_enumset1(X1,X1,X0)))) = k5_xboole_0(X0,k4_xboole_0(X1,X0)) ),
% 27.72/4.01      inference(superposition,[status(thm)],[c_747,c_8]) ).
% 27.72/4.01  
% 27.72/4.01  cnf(c_1355,plain,
% 27.72/4.01      ( k3_tarski(k1_enumset1(X0,X0,k3_tarski(k1_enumset1(X1,X1,X0)))) = k3_tarski(k1_enumset1(X0,X0,X1)) ),
% 27.72/4.01      inference(light_normalisation,[status(thm)],[c_1353,c_8]) ).
% 27.72/4.01  
% 27.72/4.01  cnf(c_1738,plain,
% 27.72/4.01      ( k4_xboole_0(k3_tarski(k1_enumset1(X0,X0,X1)),k3_tarski(k1_enumset1(X1,X1,X0))) = k4_xboole_0(X0,k3_tarski(k1_enumset1(X1,X1,X0))) ),
% 27.72/4.01      inference(superposition,[status(thm)],[c_1355,c_747]) ).
% 27.72/4.01  
% 27.72/4.01  cnf(c_13564,plain,
% 27.72/4.01      ( k4_xboole_0(k3_tarski(k1_enumset1(X0,X0,k3_relat_1(sK2))),k3_tarski(k1_enumset1(k3_tarski(k1_enumset1(X0,X0,k1_relat_1(sK2))),k3_tarski(k1_enumset1(X0,X0,k1_relat_1(sK2))),k2_relat_1(sK2)))) = k4_xboole_0(k2_relat_1(sK2),k3_tarski(k1_enumset1(k3_tarski(k1_enumset1(X0,X0,k1_relat_1(sK2))),k3_tarski(k1_enumset1(X0,X0,k1_relat_1(sK2))),k2_relat_1(sK2)))) ),
% 27.72/4.01      inference(superposition,[status(thm)],[c_12640,c_1738]) ).
% 27.72/4.01  
% 27.72/4.01  cnf(c_13611,plain,
% 27.72/4.01      ( k4_xboole_0(k3_tarski(k1_enumset1(X0,X0,k3_relat_1(sK2))),k3_tarski(k1_enumset1(X0,X0,k3_tarski(k1_enumset1(k1_relat_1(sK2),k1_relat_1(sK2),k2_relat_1(sK2)))))) = k4_xboole_0(k2_relat_1(sK2),k3_tarski(k1_enumset1(X0,X0,k3_tarski(k1_enumset1(k1_relat_1(sK2),k1_relat_1(sK2),k2_relat_1(sK2)))))) ),
% 27.72/4.01      inference(demodulation,[status(thm)],[c_13564,c_2685]) ).
% 27.72/4.01  
% 27.72/4.01  cnf(c_13612,plain,
% 27.72/4.01      ( k4_xboole_0(k3_tarski(k1_enumset1(X0,X0,k3_relat_1(sK2))),k3_tarski(k1_enumset1(X0,X0,k3_relat_1(sK2)))) = k4_xboole_0(k2_relat_1(sK2),k3_tarski(k1_enumset1(X0,X0,k3_relat_1(sK2)))) ),
% 27.72/4.01      inference(light_normalisation,[status(thm)],[c_13611,c_1904]) ).
% 27.72/4.01  
% 27.72/4.01  cnf(c_25571,plain,
% 27.72/4.01      ( k4_xboole_0(k3_tarski(k1_enumset1(X0,X0,k3_relat_1(sK2))),k3_tarski(k1_enumset1(X0,X0,k3_relat_1(sK2)))) = k1_xboole_0 ),
% 27.72/4.01      inference(demodulation,[status(thm)],[c_25321,c_1642,c_13612]) ).
% 27.72/4.01  
% 27.72/4.01  cnf(c_25940,plain,
% 27.72/4.01      ( k4_xboole_0(k3_tarski(k1_enumset1(k3_tarski(k1_enumset1(X0,X0,k3_relat_1(sK2))),k3_tarski(k1_enumset1(X0,X0,k3_relat_1(sK2))),X1)),k3_tarski(k1_enumset1(k3_tarski(k1_enumset1(X0,X0,k3_relat_1(sK2))),k3_tarski(k1_enumset1(X0,X0,k3_relat_1(sK2))),X1))) = k1_xboole_0 ),
% 27.72/4.01      inference(superposition,[status(thm)],[c_16720,c_25571]) ).
% 27.72/4.01  
% 27.72/4.01  cnf(c_9126,plain,
% 27.72/4.01      ( k4_xboole_0(k3_tarski(k1_enumset1(X0,X0,X1)),k3_tarski(k1_enumset1(X0,X0,X1))) = k4_xboole_0(X0,k3_tarski(k1_enumset1(X1,X1,X0))) ),
% 27.72/4.01      inference(superposition,[status(thm)],[c_7,c_1738]) ).
% 27.72/4.01  
% 27.72/4.01  cnf(c_25990,plain,
% 27.72/4.01      ( k4_xboole_0(k3_relat_1(sK2),k3_tarski(k1_enumset1(k3_tarski(k1_enumset1(X0,X0,X1)),k3_tarski(k1_enumset1(X0,X0,X1)),k3_relat_1(sK2)))) = k1_xboole_0 ),
% 27.72/4.01      inference(demodulation,[status(thm)],[c_25940,c_9126,c_12215]) ).
% 27.72/4.01  
% 27.72/4.01  cnf(c_25991,plain,
% 27.72/4.01      ( k4_xboole_0(k3_relat_1(sK2),k3_tarski(k1_enumset1(X0,X0,k3_tarski(k1_enumset1(k3_relat_1(sK2),k3_relat_1(sK2),X1))))) = k1_xboole_0 ),
% 27.72/4.01      inference(light_normalisation,[status(thm)],[c_25990,c_24284]) ).
% 27.72/4.01  
% 27.72/4.01  cnf(c_98534,plain,
% 27.72/4.01      ( k4_xboole_0(k3_relat_1(sK2),k3_tarski(k1_enumset1(sK0,sK0,sK1))) = k1_xboole_0 ),
% 27.72/4.01      inference(demodulation,[status(thm)],[c_98532,c_25991]) ).
% 27.72/4.01  
% 27.72/4.01  cnf(c_2324,plain,
% 27.72/4.01      ( r1_tarski(k3_relat_1(sK2),k3_tarski(k1_enumset1(sK0,sK0,sK1)))
% 27.72/4.01      | k4_xboole_0(k3_relat_1(sK2),k3_tarski(k1_enumset1(sK0,sK0,sK1))) != k1_xboole_0 ),
% 27.72/4.01      inference(instantiation,[status(thm)],[c_1]) ).
% 27.72/4.01  
% 27.72/4.01  cnf(c_18,negated_conjecture,
% 27.72/4.01      ( ~ r1_tarski(k3_relat_1(sK2),k5_xboole_0(sK0,k4_xboole_0(sK1,sK0))) ),
% 27.72/4.01      inference(cnf_transformation,[],[f60]) ).
% 27.72/4.01  
% 27.72/4.01  cnf(c_725,plain,
% 27.72/4.01      ( r1_tarski(k3_relat_1(sK2),k5_xboole_0(sK0,k4_xboole_0(sK1,sK0))) != iProver_top ),
% 27.72/4.01      inference(predicate_to_equality,[status(thm)],[c_18]) ).
% 27.72/4.01  
% 27.72/4.01  cnf(c_743,plain,
% 27.72/4.01      ( r1_tarski(k3_relat_1(sK2),k3_tarski(k1_enumset1(sK0,sK0,sK1))) != iProver_top ),
% 27.72/4.01      inference(demodulation,[status(thm)],[c_8,c_725]) ).
% 27.72/4.01  
% 27.72/4.01  cnf(c_801,plain,
% 27.72/4.01      ( ~ r1_tarski(k3_relat_1(sK2),k3_tarski(k1_enumset1(sK0,sK0,sK1))) ),
% 27.72/4.01      inference(predicate_to_equality_rev,[status(thm)],[c_743]) ).
% 27.72/4.01  
% 27.72/4.01  cnf(contradiction,plain,
% 27.72/4.01      ( $false ),
% 27.72/4.01      inference(minisat,[status(thm)],[c_98534,c_2324,c_801]) ).
% 27.72/4.01  
% 27.72/4.01  
% 27.72/4.01  % SZS output end CNFRefutation for theBenchmark.p
% 27.72/4.01  
% 27.72/4.01  ------                               Statistics
% 27.72/4.01  
% 27.72/4.01  ------ Selected
% 27.72/4.01  
% 27.72/4.01  total_time:                             3.162
% 27.72/4.01  
%------------------------------------------------------------------------------
