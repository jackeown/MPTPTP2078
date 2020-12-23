%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n016.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 11:47:15 EST 2020

% Result     : Theorem 11.97s
% Output     : CNFRefutation 11.97s
% Verified   : 
% Statistics : Number of formulae       :   97 ( 547 expanded)
%              Number of clauses        :   50 ( 181 expanded)
%              Number of leaves         :   18 ( 138 expanded)
%              Depth                    :   16
%              Number of atoms          :  219 (1436 expanded)
%              Number of equality atoms :  134 ( 781 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal clause size      :   10 (   2 average)
%              Maximal term depth       :    5 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f21,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
    <=> ! [X1] :
          ~ ( ! [X2,X3] : k4_tarski(X2,X3) != X1
            & r2_hidden(X1,X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f27,plain,(
    ! [X0] :
      ( ! [X1] :
          ~ ( ! [X2,X3] : k4_tarski(X2,X3) != X1
            & r2_hidden(X1,X0) )
     => v1_relat_1(X0) ) ),
    inference(unused_predicate_definition_removal,[],[f21])).

fof(f35,plain,(
    ! [X0] :
      ( v1_relat_1(X0)
      | ? [X1] :
          ( ! [X2,X3] : k4_tarski(X2,X3) != X1
          & r2_hidden(X1,X0) ) ) ),
    inference(ennf_transformation,[],[f27])).

fof(f45,plain,(
    ! [X0] :
      ( ? [X1] :
          ( ! [X2,X3] : k4_tarski(X2,X3) != X1
          & r2_hidden(X1,X0) )
     => ( ! [X3,X2] : k4_tarski(X2,X3) != sK1(X0)
        & r2_hidden(sK1(X0),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f46,plain,(
    ! [X0] :
      ( v1_relat_1(X0)
      | ( ! [X2,X3] : k4_tarski(X2,X3) != sK1(X0)
        & r2_hidden(sK1(X0),X0) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1])],[f35,f45])).

fof(f74,plain,(
    ! [X0] :
      ( v1_relat_1(X0)
      | r2_hidden(sK1(X0),X0) ) ),
    inference(cnf_transformation,[],[f46])).

fof(f19,axiom,(
    ! [X0] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f72,plain,(
    ! [X0] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0)) ),
    inference(cnf_transformation,[],[f19])).

fof(f18,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => ! [X2] :
          ( r2_hidden(X2,X1)
         => r2_hidden(X2,X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f32,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( r2_hidden(X2,X0)
          | ~ r2_hidden(X2,X1) )
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f18])).

fof(f71,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(X2,X0)
      | ~ r2_hidden(X2,X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f32])).

fof(f11,axiom,(
    ! [X0,X1] :
      ( k1_tarski(X0) = X1
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
        <=> X0 = X2 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f39,plain,(
    ! [X0,X1] :
      ( ( k1_tarski(X0) = X1
        | ? [X2] :
            ( ( X0 != X2
              | ~ r2_hidden(X2,X1) )
            & ( X0 = X2
              | r2_hidden(X2,X1) ) ) )
      & ( ! [X2] :
            ( ( r2_hidden(X2,X1)
              | X0 != X2 )
            & ( X0 = X2
              | ~ r2_hidden(X2,X1) ) )
        | k1_tarski(X0) != X1 ) ) ),
    inference(nnf_transformation,[],[f11])).

fof(f40,plain,(
    ! [X0,X1] :
      ( ( k1_tarski(X0) = X1
        | ? [X2] :
            ( ( X0 != X2
              | ~ r2_hidden(X2,X1) )
            & ( X0 = X2
              | r2_hidden(X2,X1) ) ) )
      & ( ! [X3] :
            ( ( r2_hidden(X3,X1)
              | X0 != X3 )
            & ( X0 = X3
              | ~ r2_hidden(X3,X1) ) )
        | k1_tarski(X0) != X1 ) ) ),
    inference(rectify,[],[f39])).

fof(f41,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ( X0 != X2
            | ~ r2_hidden(X2,X1) )
          & ( X0 = X2
            | r2_hidden(X2,X1) ) )
     => ( ( sK0(X0,X1) != X0
          | ~ r2_hidden(sK0(X0,X1),X1) )
        & ( sK0(X0,X1) = X0
          | r2_hidden(sK0(X0,X1),X1) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f42,plain,(
    ! [X0,X1] :
      ( ( k1_tarski(X0) = X1
        | ( ( sK0(X0,X1) != X0
            | ~ r2_hidden(sK0(X0,X1),X1) )
          & ( sK0(X0,X1) = X0
            | r2_hidden(sK0(X0,X1),X1) ) ) )
      & ( ! [X3] :
            ( ( r2_hidden(X3,X1)
              | X0 != X3 )
            & ( X0 = X3
              | ~ r2_hidden(X3,X1) ) )
        | k1_tarski(X0) != X1 ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f40,f41])).

fof(f59,plain,(
    ! [X0,X3,X1] :
      ( X0 = X3
      | ~ r2_hidden(X3,X1)
      | k1_tarski(X0) != X1 ) ),
    inference(cnf_transformation,[],[f42])).

fof(f13,axiom,(
    ! [X0] : k1_tarski(X0) = k2_tarski(X0,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f64,plain,(
    ! [X0] : k1_tarski(X0) = k2_tarski(X0,X0) ),
    inference(cnf_transformation,[],[f13])).

fof(f91,plain,(
    ! [X0,X3,X1] :
      ( X0 = X3
      | ~ r2_hidden(X3,X1)
      | k2_tarski(X0,X0) != X1 ) ),
    inference(definition_unfolding,[],[f59,f64])).

fof(f100,plain,(
    ! [X0,X3] :
      ( X0 = X3
      | ~ r2_hidden(X3,k2_tarski(X0,X0)) ) ),
    inference(equality_resolution,[],[f91])).

fof(f22,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => k10_relat_1(X1,X0) = k10_relat_1(X1,k3_xboole_0(k2_relat_1(X1),X0)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f36,plain,(
    ! [X0,X1] :
      ( k10_relat_1(X1,X0) = k10_relat_1(X1,k3_xboole_0(k2_relat_1(X1),X0))
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f22])).

fof(f76,plain,(
    ! [X0,X1] :
      ( k10_relat_1(X1,X0) = k10_relat_1(X1,k3_xboole_0(k2_relat_1(X1),X0))
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f36])).

fof(f5,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f53,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f5])).

fof(f97,plain,(
    ! [X0,X1] :
      ( k10_relat_1(X1,X0) = k10_relat_1(X1,k4_xboole_0(k2_relat_1(X1),k4_xboole_0(k2_relat_1(X1),X0)))
      | ~ v1_relat_1(X1) ) ),
    inference(definition_unfolding,[],[f76,f53])).

fof(f7,axiom,(
    ! [X0] : k4_xboole_0(k1_xboole_0,X0) = k1_xboole_0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f55,plain,(
    ! [X0] : k4_xboole_0(k1_xboole_0,X0) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f7])).

fof(f24,axiom,
    ( k1_xboole_0 = k2_relat_1(k1_xboole_0)
    & k1_xboole_0 = k1_relat_1(k1_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f79,plain,(
    k1_xboole_0 = k2_relat_1(k1_xboole_0) ),
    inference(cnf_transformation,[],[f24])).

fof(f23,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => k1_xboole_0 = k10_relat_1(X0,k1_xboole_0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f37,plain,(
    ! [X0] :
      ( k1_xboole_0 = k10_relat_1(X0,k1_xboole_0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f23])).

fof(f77,plain,(
    ! [X0] :
      ( k1_xboole_0 = k10_relat_1(X0,k1_xboole_0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f37])).

fof(f25,conjecture,(
    ! [X0] : k1_xboole_0 = k10_relat_1(k1_xboole_0,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f26,negated_conjecture,(
    ~ ! [X0] : k1_xboole_0 = k10_relat_1(k1_xboole_0,X0) ),
    inference(negated_conjecture,[],[f25])).

fof(f38,plain,(
    ? [X0] : k1_xboole_0 != k10_relat_1(k1_xboole_0,X0) ),
    inference(ennf_transformation,[],[f26])).

fof(f47,plain,
    ( ? [X0] : k1_xboole_0 != k10_relat_1(k1_xboole_0,X0)
   => k1_xboole_0 != k10_relat_1(k1_xboole_0,sK2) ),
    introduced(choice_axiom,[])).

fof(f48,plain,(
    k1_xboole_0 != k10_relat_1(k1_xboole_0,sK2) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2])],[f38,f47])).

fof(f80,plain,(
    k1_xboole_0 != k10_relat_1(k1_xboole_0,sK2) ),
    inference(cnf_transformation,[],[f48])).

fof(f15,axiom,(
    ! [X0,X1] :
      ( k4_xboole_0(k1_tarski(X0),k1_tarski(X1)) = k1_tarski(X0)
    <=> X0 != X1 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f43,plain,(
    ! [X0,X1] :
      ( ( k4_xboole_0(k1_tarski(X0),k1_tarski(X1)) = k1_tarski(X0)
        | X0 = X1 )
      & ( X0 != X1
        | k4_xboole_0(k1_tarski(X0),k1_tarski(X1)) != k1_tarski(X0) ) ) ),
    inference(nnf_transformation,[],[f15])).

fof(f66,plain,(
    ! [X0,X1] :
      ( X0 != X1
      | k4_xboole_0(k1_tarski(X0),k1_tarski(X1)) != k1_tarski(X0) ) ),
    inference(cnf_transformation,[],[f43])).

fof(f94,plain,(
    ! [X0,X1] :
      ( X0 != X1
      | k4_xboole_0(k2_tarski(X0,X0),k2_tarski(X1,X1)) != k2_tarski(X0,X0) ) ),
    inference(definition_unfolding,[],[f66,f64,f64,f64])).

fof(f101,plain,(
    ! [X1] : k4_xboole_0(k2_tarski(X1,X1),k2_tarski(X1,X1)) != k2_tarski(X1,X1) ),
    inference(equality_resolution,[],[f94])).

fof(f67,plain,(
    ! [X0,X1] :
      ( k4_xboole_0(k1_tarski(X0),k1_tarski(X1)) = k1_tarski(X0)
      | X0 = X1 ) ),
    inference(cnf_transformation,[],[f43])).

fof(f93,plain,(
    ! [X0,X1] :
      ( k4_xboole_0(k2_tarski(X0,X0),k2_tarski(X1,X1)) = k2_tarski(X0,X0)
      | X0 = X1 ) ),
    inference(definition_unfolding,[],[f67,f64,f64,f64])).

cnf(c_24,plain,
    ( r2_hidden(sK1(X0),X0)
    | v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f74])).

cnf(c_59385,plain,
    ( r2_hidden(sK1(X0),X0) = iProver_top
    | v1_relat_1(X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_24])).

cnf(c_21,plain,
    ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0)) ),
    inference(cnf_transformation,[],[f72])).

cnf(c_59386,plain,
    ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_21])).

cnf(c_20,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | ~ r2_hidden(X2,X0)
    | r2_hidden(X2,X1) ),
    inference(cnf_transformation,[],[f71])).

cnf(c_59387,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(X1)) != iProver_top
    | r2_hidden(X2,X0) != iProver_top
    | r2_hidden(X2,X1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_20])).

cnf(c_59792,plain,
    ( r2_hidden(X0,X1) = iProver_top
    | r2_hidden(X0,k1_xboole_0) != iProver_top ),
    inference(superposition,[status(thm)],[c_59386,c_59387])).

cnf(c_59797,plain,
    ( r2_hidden(sK1(k1_xboole_0),X0) = iProver_top
    | v1_relat_1(k1_xboole_0) = iProver_top ),
    inference(superposition,[status(thm)],[c_59385,c_59792])).

cnf(c_13,plain,
    ( ~ r2_hidden(X0,k2_tarski(X1,X1))
    | X0 = X1 ),
    inference(cnf_transformation,[],[f100])).

cnf(c_59388,plain,
    ( X0 = X1
    | r2_hidden(X0,k2_tarski(X1,X1)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_13])).

cnf(c_59872,plain,
    ( sK1(k1_xboole_0) = X0
    | v1_relat_1(k1_xboole_0) = iProver_top ),
    inference(superposition,[status(thm)],[c_59797,c_59388])).

cnf(c_25,plain,
    ( ~ v1_relat_1(X0)
    | k10_relat_1(X0,k4_xboole_0(k2_relat_1(X0),k4_xboole_0(k2_relat_1(X0),X1))) = k10_relat_1(X0,X1) ),
    inference(cnf_transformation,[],[f97])).

cnf(c_59384,plain,
    ( k10_relat_1(X0,k4_xboole_0(k2_relat_1(X0),k4_xboole_0(k2_relat_1(X0),X1))) = k10_relat_1(X0,X1)
    | v1_relat_1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_25])).

cnf(c_59884,plain,
    ( k10_relat_1(k1_xboole_0,k4_xboole_0(k2_relat_1(k1_xboole_0),k4_xboole_0(k2_relat_1(k1_xboole_0),X0))) = k10_relat_1(k1_xboole_0,X0)
    | sK1(k1_xboole_0) = X1 ),
    inference(superposition,[status(thm)],[c_59872,c_59384])).

cnf(c_6,plain,
    ( k4_xboole_0(k1_xboole_0,X0) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f55])).

cnf(c_27,plain,
    ( k2_relat_1(k1_xboole_0) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f79])).

cnf(c_59892,plain,
    ( k10_relat_1(k1_xboole_0,k4_xboole_0(k1_xboole_0,k1_xboole_0)) = k10_relat_1(k1_xboole_0,X0)
    | sK1(k1_xboole_0) = X1 ),
    inference(light_normalisation,[status(thm)],[c_59884,c_6,c_27])).

cnf(c_59893,plain,
    ( k10_relat_1(k1_xboole_0,X0) = k10_relat_1(k1_xboole_0,k1_xboole_0)
    | sK1(k1_xboole_0) = X1 ),
    inference(demodulation,[status(thm)],[c_59892,c_6])).

cnf(c_26,plain,
    ( ~ v1_relat_1(X0)
    | k10_relat_1(X0,k1_xboole_0) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f77])).

cnf(c_59383,plain,
    ( k10_relat_1(X0,k1_xboole_0) = k1_xboole_0
    | v1_relat_1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_26])).

cnf(c_59885,plain,
    ( k10_relat_1(k1_xboole_0,k1_xboole_0) = k1_xboole_0
    | sK1(k1_xboole_0) = X0 ),
    inference(superposition,[status(thm)],[c_59872,c_59383])).

cnf(c_31,plain,
    ( ~ v1_relat_1(k1_xboole_0)
    | k10_relat_1(k1_xboole_0,k1_xboole_0) = k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_26])).

cnf(c_59741,plain,
    ( r2_hidden(X0,X1)
    | ~ r2_hidden(X0,k1_xboole_0) ),
    inference(resolution,[status(thm)],[c_20,c_21])).

cnf(c_59818,plain,
    ( r2_hidden(sK1(k1_xboole_0),X0)
    | v1_relat_1(k1_xboole_0) ),
    inference(resolution,[status(thm)],[c_59741,c_24])).

cnf(c_59904,plain,
    ( v1_relat_1(k1_xboole_0)
    | sK1(k1_xboole_0) = X0 ),
    inference(resolution,[status(thm)],[c_59818,c_13])).

cnf(c_249,plain,
    ( X0 != X1
    | X2 != X1
    | X2 = X0 ),
    theory(equality)).

cnf(c_248,plain,
    ( X0 = X0 ),
    theory(equality)).

cnf(c_59581,plain,
    ( X0 != X1
    | X1 = X0 ),
    inference(resolution,[status(thm)],[c_249,c_248])).

cnf(c_59913,plain,
    ( v1_relat_1(k1_xboole_0)
    | X0 = sK1(k1_xboole_0) ),
    inference(resolution,[status(thm)],[c_59904,c_59581])).

cnf(c_29,negated_conjecture,
    ( k1_xboole_0 != k10_relat_1(k1_xboole_0,sK2) ),
    inference(cnf_transformation,[],[f80])).

cnf(c_37,plain,
    ( r2_hidden(sK1(k1_xboole_0),k1_xboole_0)
    | v1_relat_1(k1_xboole_0) ),
    inference(instantiation,[status(thm)],[c_24])).

cnf(c_16,plain,
    ( k4_xboole_0(k2_tarski(X0,X0),k2_tarski(X0,X0)) != k2_tarski(X0,X0) ),
    inference(cnf_transformation,[],[f101])).

cnf(c_58,plain,
    ( k4_xboole_0(k2_tarski(k1_xboole_0,k1_xboole_0),k2_tarski(k1_xboole_0,k1_xboole_0)) != k2_tarski(k1_xboole_0,k1_xboole_0) ),
    inference(instantiation,[status(thm)],[c_16])).

cnf(c_15,plain,
    ( X0 = X1
    | k4_xboole_0(k2_tarski(X1,X1),k2_tarski(X0,X0)) = k2_tarski(X1,X1) ),
    inference(cnf_transformation,[],[f93])).

cnf(c_59,plain,
    ( k4_xboole_0(k2_tarski(k1_xboole_0,k1_xboole_0),k2_tarski(k1_xboole_0,k1_xboole_0)) = k2_tarski(k1_xboole_0,k1_xboole_0)
    | k1_xboole_0 = k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_15])).

cnf(c_2447,plain,
    ( ~ r2_hidden(k1_xboole_0,k2_tarski(k10_relat_1(k1_xboole_0,sK2),k10_relat_1(k1_xboole_0,sK2)))
    | k1_xboole_0 = k10_relat_1(k1_xboole_0,sK2) ),
    inference(instantiation,[status(thm)],[c_13])).

cnf(c_21400,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_tarski(k10_relat_1(k1_xboole_0,sK2),k10_relat_1(k1_xboole_0,sK2))))
    | ~ r2_hidden(k1_xboole_0,X0)
    | r2_hidden(k1_xboole_0,k2_tarski(k10_relat_1(k1_xboole_0,sK2),k10_relat_1(k1_xboole_0,sK2))) ),
    inference(instantiation,[status(thm)],[c_20])).

cnf(c_21407,plain,
    ( ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_tarski(k10_relat_1(k1_xboole_0,sK2),k10_relat_1(k1_xboole_0,sK2))))
    | r2_hidden(k1_xboole_0,k2_tarski(k10_relat_1(k1_xboole_0,sK2),k10_relat_1(k1_xboole_0,sK2)))
    | ~ r2_hidden(k1_xboole_0,k1_xboole_0) ),
    inference(instantiation,[status(thm)],[c_21400])).

cnf(c_21422,plain,
    ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_tarski(k10_relat_1(k1_xboole_0,sK2),k10_relat_1(k1_xboole_0,sK2)))) ),
    inference(instantiation,[status(thm)],[c_21])).

cnf(c_255,plain,
    ( ~ r2_hidden(X0,X1)
    | r2_hidden(X2,X3)
    | X2 != X0
    | X3 != X1 ),
    theory(equality)).

cnf(c_59523,plain,
    ( r2_hidden(X0,X1)
    | ~ r2_hidden(sK1(X2),X2)
    | X1 != X2
    | X0 != sK1(X2) ),
    inference(instantiation,[status(thm)],[c_255])).

cnf(c_59525,plain,
    ( ~ r2_hidden(sK1(k1_xboole_0),k1_xboole_0)
    | r2_hidden(k1_xboole_0,k1_xboole_0)
    | k1_xboole_0 != sK1(k1_xboole_0)
    | k1_xboole_0 != k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_59523])).

cnf(c_59915,plain,
    ( v1_relat_1(k1_xboole_0)
    | k1_xboole_0 = sK1(k1_xboole_0) ),
    inference(instantiation,[status(thm)],[c_59913])).

cnf(c_59922,plain,
    ( v1_relat_1(k1_xboole_0) ),
    inference(global_propositional_subsumption,[status(thm)],[c_59913,c_29,c_37,c_58,c_59,c_2447,c_21407,c_21422,c_59525,c_59915])).

cnf(c_59987,plain,
    ( k10_relat_1(k1_xboole_0,k1_xboole_0) = k1_xboole_0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_59885,c_29,c_31,c_37,c_58,c_59,c_2447,c_21407,c_21422,c_59525,c_59915])).

cnf(c_59990,plain,
    ( k10_relat_1(k1_xboole_0,X0) = k1_xboole_0
    | sK1(k1_xboole_0) = X1 ),
    inference(light_normalisation,[status(thm)],[c_59893,c_59987])).

cnf(c_60013,plain,
    ( sK1(k1_xboole_0) = X0 ),
    inference(superposition,[status(thm)],[c_59990,c_29])).

cnf(c_60117,plain,
    ( sK1(k1_xboole_0) != k1_xboole_0 ),
    inference(demodulation,[status(thm)],[c_60013,c_29])).

cnf(c_60028,plain,
    ( sK1(k1_xboole_0) = k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_60013])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_60117,c_60028])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : iproveropt_run.sh %d %s
% 0.13/0.34  % Computer   : n016.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 18:16:49 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.35  % Running in FOF mode
% 11.97/2.00  % SZS status Started for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 11.97/2.00  
% 11.97/2.00  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 11.97/2.00  
% 11.97/2.00  ------  iProver source info
% 11.97/2.00  
% 11.97/2.00  git: date: 2020-06-30 10:37:57 +0100
% 11.97/2.00  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 11.97/2.00  git: non_committed_changes: false
% 11.97/2.00  git: last_make_outside_of_git: false
% 11.97/2.00  
% 11.97/2.00  ------ 
% 11.97/2.00  ------ Parsing...
% 11.97/2.00  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 11.97/2.00  
% 11.97/2.00  ------ Preprocessing... sf_s  rm: 1 0s  sf_e 
% 11.97/2.00  
% 11.97/2.00  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 11.97/2.00  
% 11.97/2.00  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 11.97/2.00  ------ Proving...
% 11.97/2.00  ------ Problem Properties 
% 11.97/2.00  
% 11.97/2.00  
% 11.97/2.00  clauses                                 30
% 11.97/2.00  conjectures                             1
% 11.97/2.00  EPR                                     1
% 11.97/2.00  Horn                                    26
% 11.97/2.00  unary                                   15
% 11.97/2.00  binary                                  9
% 11.97/2.00  lits                                    52
% 11.97/2.00  lits eq                                 22
% 11.97/2.00  fd_pure                                 0
% 11.97/2.00  fd_pseudo                               0
% 11.97/2.00  fd_cond                                 0
% 11.97/2.00  fd_pseudo_cond                          3
% 11.97/2.00  AC symbols                              0
% 11.97/2.00  
% 11.97/2.00  ------ Input Options Time Limit: Unbounded
% 11.97/2.00  
% 11.97/2.00  
% 11.97/2.00  
% 11.97/2.00  
% 11.97/2.00  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e ------ 
% 11.97/2.00  Current options:
% 11.97/2.00  ------ 
% 11.97/2.00  
% 11.97/2.00  
% 11.97/2.00  
% 11.97/2.00  
% 11.97/2.00  ------ Proving...
% 11.97/2.00  
% 11.97/2.00  
% 11.97/2.00  ------ Preprocessing... sf_s  rm: 0 0s  sf_e 
% 11.97/2.00  
% 11.97/2.00  ------ Proving...
% 11.97/2.00  
% 11.97/2.00  
% 11.97/2.00  ------ Preprocessing... sf_s  rm: 0 0s  sf_e 
% 11.97/2.00  
% 11.97/2.00  ------ Proving...
% 11.97/2.00  
% 11.97/2.00  
% 11.97/2.00  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 11.97/2.00  
% 11.97/2.00  ------ Proving...
% 11.97/2.00  
% 11.97/2.00  
% 11.97/2.00  ------ Preprocessing... sf_s  rm: 0 0s  sf_e 
% 11.97/2.00  
% 11.97/2.00  ------ Proving...
% 11.97/2.00  
% 11.97/2.00  
% 11.97/2.00  ------ Preprocessing... sf_s  rm: 0 0s  sf_e 
% 11.97/2.00  
% 11.97/2.00  ------ Proving...
% 11.97/2.00  
% 11.97/2.00  
% 11.97/2.00  ------ Preprocessing... sf_s  rm: 0 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 11.97/2.00  
% 11.97/2.00  ------ Proving...
% 11.97/2.00  
% 11.97/2.00  
% 11.97/2.00  ------ Preprocessing... sf_s  rm: 2 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 11.97/2.00  
% 11.97/2.00  ------ Proving...
% 11.97/2.00  
% 11.97/2.00  
% 11.97/2.00  ------ Preprocessing... sf_s  rm: 2 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 11.97/2.00  
% 11.97/2.00  ------ Proving...
% 11.97/2.00  
% 11.97/2.00  
% 11.97/2.00  ------ Preprocessing... sf_s  rm: 0 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 11.97/2.00  
% 11.97/2.00  ------ Proving...
% 11.97/2.00  
% 11.97/2.00  
% 11.97/2.00  ------ Preprocessing... sf_s  rm: 0 0s  sf_e 
% 11.97/2.00  
% 11.97/2.00  ------ Proving...
% 11.97/2.00  
% 11.97/2.00  
% 11.97/2.00  ------ Preprocessing... sf_s  rm: 0 0s  sf_e 
% 11.97/2.00  
% 11.97/2.00  ------ Proving...
% 11.97/2.00  
% 11.97/2.00  
% 11.97/2.00  ------ Preprocessing... sf_s  rm: 0 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 11.97/2.00  
% 11.97/2.00  ------ Proving...
% 11.97/2.00  
% 11.97/2.00  
% 11.97/2.00  ------ Preprocessing... sf_s  rm: 0 0s  sf_e 
% 11.97/2.00  
% 11.97/2.00  ------ Proving...
% 11.97/2.00  
% 11.97/2.00  
% 11.97/2.00  ------ Preprocessing... sf_s  rm: 0 0s  sf_e 
% 11.97/2.00  
% 11.97/2.00  ------ Proving...
% 11.97/2.00  
% 11.97/2.00  
% 11.97/2.00  ------ Preprocessing... sf_s  rm: 0 0s  sf_e 
% 11.97/2.00  
% 11.97/2.00  ------ Proving...
% 11.97/2.00  
% 11.97/2.00  
% 11.97/2.00  ------ Preprocessing... sf_s  rm: 0 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 11.97/2.00  
% 11.97/2.00  ------ Proving...
% 11.97/2.00  
% 11.97/2.00  
% 11.97/2.00  ------ Preprocessing... sf_s  rm: 0 0s  sf_e 
% 11.97/2.00  
% 11.97/2.00  ------ Proving...
% 11.97/2.00  
% 11.97/2.00  
% 11.97/2.00  ------ Preprocessing... sf_s  rm: 0 0s  sf_e 
% 11.97/2.00  
% 11.97/2.00  ------ Proving...
% 11.97/2.00  
% 11.97/2.00  
% 11.97/2.00  ------ Preprocessing... sf_s  rm: 0 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 11.97/2.00  
% 11.97/2.00  ------ Proving...
% 11.97/2.00  
% 11.97/2.00  
% 11.97/2.00  ------ Preprocessing... sf_s  rm: 0 0s  sf_e 
% 11.97/2.00  
% 11.97/2.00  ------ Proving...
% 11.97/2.00  
% 11.97/2.00  
% 11.97/2.00  ------ Preprocessing... sf_s  rm: 0 0s  sf_e 
% 11.97/2.00  
% 11.97/2.00  ------ Proving...
% 11.97/2.00  
% 11.97/2.00  
% 11.97/2.00  ------ Preprocessing... sf_s  rm: 0 0s  sf_e 
% 11.97/2.00  
% 11.97/2.00  ------ Proving...
% 11.97/2.00  
% 11.97/2.00  
% 11.97/2.00  ------ Preprocessing... sf_s  rm: 0 0s  sf_e 
% 11.97/2.00  
% 11.97/2.00  ------ Proving...
% 11.97/2.00  
% 11.97/2.00  
% 11.97/2.00  ------ Preprocessing... sf_s  rm: 0 0s  sf_e 
% 11.97/2.00  
% 11.97/2.00  ------ Proving...
% 11.97/2.00  
% 11.97/2.00  
% 11.97/2.00  % SZS status Theorem for theBenchmark.p
% 11.97/2.00  
% 11.97/2.00  % SZS output start CNFRefutation for theBenchmark.p
% 11.97/2.00  
% 11.97/2.00  fof(f21,axiom,(
% 11.97/2.00    ! [X0] : (v1_relat_1(X0) <=> ! [X1] : ~(! [X2,X3] : k4_tarski(X2,X3) != X1 & r2_hidden(X1,X0)))),
% 11.97/2.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 11.97/2.00  
% 11.97/2.00  fof(f27,plain,(
% 11.97/2.00    ! [X0] : (! [X1] : ~(! [X2,X3] : k4_tarski(X2,X3) != X1 & r2_hidden(X1,X0)) => v1_relat_1(X0))),
% 11.97/2.00    inference(unused_predicate_definition_removal,[],[f21])).
% 11.97/2.00  
% 11.97/2.00  fof(f35,plain,(
% 11.97/2.00    ! [X0] : (v1_relat_1(X0) | ? [X1] : (! [X2,X3] : k4_tarski(X2,X3) != X1 & r2_hidden(X1,X0)))),
% 11.97/2.00    inference(ennf_transformation,[],[f27])).
% 11.97/2.00  
% 11.97/2.00  fof(f45,plain,(
% 11.97/2.00    ! [X0] : (? [X1] : (! [X2,X3] : k4_tarski(X2,X3) != X1 & r2_hidden(X1,X0)) => (! [X3,X2] : k4_tarski(X2,X3) != sK1(X0) & r2_hidden(sK1(X0),X0)))),
% 11.97/2.00    introduced(choice_axiom,[])).
% 11.97/2.00  
% 11.97/2.00  fof(f46,plain,(
% 11.97/2.00    ! [X0] : (v1_relat_1(X0) | (! [X2,X3] : k4_tarski(X2,X3) != sK1(X0) & r2_hidden(sK1(X0),X0)))),
% 11.97/2.00    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1])],[f35,f45])).
% 11.97/2.00  
% 11.97/2.00  fof(f74,plain,(
% 11.97/2.00    ( ! [X0] : (v1_relat_1(X0) | r2_hidden(sK1(X0),X0)) )),
% 11.97/2.00    inference(cnf_transformation,[],[f46])).
% 11.97/2.00  
% 11.97/2.00  fof(f19,axiom,(
% 11.97/2.00    ! [X0] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0))),
% 11.97/2.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 11.97/2.00  
% 11.97/2.00  fof(f72,plain,(
% 11.97/2.00    ( ! [X0] : (m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0))) )),
% 11.97/2.00    inference(cnf_transformation,[],[f19])).
% 11.97/2.00  
% 11.97/2.00  fof(f18,axiom,(
% 11.97/2.00    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => ! [X2] : (r2_hidden(X2,X1) => r2_hidden(X2,X0)))),
% 11.97/2.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 11.97/2.00  
% 11.97/2.00  fof(f32,plain,(
% 11.97/2.00    ! [X0,X1] : (! [X2] : (r2_hidden(X2,X0) | ~r2_hidden(X2,X1)) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 11.97/2.00    inference(ennf_transformation,[],[f18])).
% 11.97/2.00  
% 11.97/2.00  fof(f71,plain,(
% 11.97/2.00    ( ! [X2,X0,X1] : (r2_hidden(X2,X0) | ~r2_hidden(X2,X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 11.97/2.00    inference(cnf_transformation,[],[f32])).
% 11.97/2.00  
% 11.97/2.00  fof(f11,axiom,(
% 11.97/2.00    ! [X0,X1] : (k1_tarski(X0) = X1 <=> ! [X2] : (r2_hidden(X2,X1) <=> X0 = X2))),
% 11.97/2.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 11.97/2.00  
% 11.97/2.00  fof(f39,plain,(
% 11.97/2.00    ! [X0,X1] : ((k1_tarski(X0) = X1 | ? [X2] : ((X0 != X2 | ~r2_hidden(X2,X1)) & (X0 = X2 | r2_hidden(X2,X1)))) & (! [X2] : ((r2_hidden(X2,X1) | X0 != X2) & (X0 = X2 | ~r2_hidden(X2,X1))) | k1_tarski(X0) != X1))),
% 11.97/2.00    inference(nnf_transformation,[],[f11])).
% 11.97/2.00  
% 11.97/2.00  fof(f40,plain,(
% 11.97/2.00    ! [X0,X1] : ((k1_tarski(X0) = X1 | ? [X2] : ((X0 != X2 | ~r2_hidden(X2,X1)) & (X0 = X2 | r2_hidden(X2,X1)))) & (! [X3] : ((r2_hidden(X3,X1) | X0 != X3) & (X0 = X3 | ~r2_hidden(X3,X1))) | k1_tarski(X0) != X1))),
% 11.97/2.00    inference(rectify,[],[f39])).
% 11.97/2.00  
% 11.97/2.00  fof(f41,plain,(
% 11.97/2.00    ! [X1,X0] : (? [X2] : ((X0 != X2 | ~r2_hidden(X2,X1)) & (X0 = X2 | r2_hidden(X2,X1))) => ((sK0(X0,X1) != X0 | ~r2_hidden(sK0(X0,X1),X1)) & (sK0(X0,X1) = X0 | r2_hidden(sK0(X0,X1),X1))))),
% 11.97/2.00    introduced(choice_axiom,[])).
% 11.97/2.00  
% 11.97/2.00  fof(f42,plain,(
% 11.97/2.00    ! [X0,X1] : ((k1_tarski(X0) = X1 | ((sK0(X0,X1) != X0 | ~r2_hidden(sK0(X0,X1),X1)) & (sK0(X0,X1) = X0 | r2_hidden(sK0(X0,X1),X1)))) & (! [X3] : ((r2_hidden(X3,X1) | X0 != X3) & (X0 = X3 | ~r2_hidden(X3,X1))) | k1_tarski(X0) != X1))),
% 11.97/2.00    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f40,f41])).
% 11.97/2.00  
% 11.97/2.00  fof(f59,plain,(
% 11.97/2.00    ( ! [X0,X3,X1] : (X0 = X3 | ~r2_hidden(X3,X1) | k1_tarski(X0) != X1) )),
% 11.97/2.00    inference(cnf_transformation,[],[f42])).
% 11.97/2.00  
% 11.97/2.00  fof(f13,axiom,(
% 11.97/2.00    ! [X0] : k1_tarski(X0) = k2_tarski(X0,X0)),
% 11.97/2.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 11.97/2.00  
% 11.97/2.00  fof(f64,plain,(
% 11.97/2.00    ( ! [X0] : (k1_tarski(X0) = k2_tarski(X0,X0)) )),
% 11.97/2.00    inference(cnf_transformation,[],[f13])).
% 11.97/2.00  
% 11.97/2.00  fof(f91,plain,(
% 11.97/2.00    ( ! [X0,X3,X1] : (X0 = X3 | ~r2_hidden(X3,X1) | k2_tarski(X0,X0) != X1) )),
% 11.97/2.00    inference(definition_unfolding,[],[f59,f64])).
% 11.97/2.00  
% 11.97/2.00  fof(f100,plain,(
% 11.97/2.00    ( ! [X0,X3] : (X0 = X3 | ~r2_hidden(X3,k2_tarski(X0,X0))) )),
% 11.97/2.00    inference(equality_resolution,[],[f91])).
% 11.97/2.00  
% 11.97/2.00  fof(f22,axiom,(
% 11.97/2.00    ! [X0,X1] : (v1_relat_1(X1) => k10_relat_1(X1,X0) = k10_relat_1(X1,k3_xboole_0(k2_relat_1(X1),X0)))),
% 11.97/2.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 11.97/2.00  
% 11.97/2.00  fof(f36,plain,(
% 11.97/2.00    ! [X0,X1] : (k10_relat_1(X1,X0) = k10_relat_1(X1,k3_xboole_0(k2_relat_1(X1),X0)) | ~v1_relat_1(X1))),
% 11.97/2.00    inference(ennf_transformation,[],[f22])).
% 11.97/2.00  
% 11.97/2.00  fof(f76,plain,(
% 11.97/2.00    ( ! [X0,X1] : (k10_relat_1(X1,X0) = k10_relat_1(X1,k3_xboole_0(k2_relat_1(X1),X0)) | ~v1_relat_1(X1)) )),
% 11.97/2.00    inference(cnf_transformation,[],[f36])).
% 11.97/2.00  
% 11.97/2.00  fof(f5,axiom,(
% 11.97/2.00    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1))),
% 11.97/2.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 11.97/2.00  
% 11.97/2.00  fof(f53,plain,(
% 11.97/2.00    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1))) )),
% 11.97/2.00    inference(cnf_transformation,[],[f5])).
% 11.97/2.00  
% 11.97/2.00  fof(f97,plain,(
% 11.97/2.00    ( ! [X0,X1] : (k10_relat_1(X1,X0) = k10_relat_1(X1,k4_xboole_0(k2_relat_1(X1),k4_xboole_0(k2_relat_1(X1),X0))) | ~v1_relat_1(X1)) )),
% 11.97/2.00    inference(definition_unfolding,[],[f76,f53])).
% 11.97/2.00  
% 11.97/2.00  fof(f7,axiom,(
% 11.97/2.00    ! [X0] : k4_xboole_0(k1_xboole_0,X0) = k1_xboole_0),
% 11.97/2.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 11.97/2.00  
% 11.97/2.00  fof(f55,plain,(
% 11.97/2.00    ( ! [X0] : (k4_xboole_0(k1_xboole_0,X0) = k1_xboole_0) )),
% 11.97/2.00    inference(cnf_transformation,[],[f7])).
% 11.97/2.00  
% 11.97/2.00  fof(f24,axiom,(
% 11.97/2.00    k1_xboole_0 = k2_relat_1(k1_xboole_0) & k1_xboole_0 = k1_relat_1(k1_xboole_0)),
% 11.97/2.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 11.97/2.00  
% 11.97/2.00  fof(f79,plain,(
% 11.97/2.00    k1_xboole_0 = k2_relat_1(k1_xboole_0)),
% 11.97/2.00    inference(cnf_transformation,[],[f24])).
% 11.97/2.00  
% 11.97/2.00  fof(f23,axiom,(
% 11.97/2.00    ! [X0] : (v1_relat_1(X0) => k1_xboole_0 = k10_relat_1(X0,k1_xboole_0))),
% 11.97/2.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 11.97/2.00  
% 11.97/2.00  fof(f37,plain,(
% 11.97/2.00    ! [X0] : (k1_xboole_0 = k10_relat_1(X0,k1_xboole_0) | ~v1_relat_1(X0))),
% 11.97/2.00    inference(ennf_transformation,[],[f23])).
% 11.97/2.00  
% 11.97/2.00  fof(f77,plain,(
% 11.97/2.00    ( ! [X0] : (k1_xboole_0 = k10_relat_1(X0,k1_xboole_0) | ~v1_relat_1(X0)) )),
% 11.97/2.00    inference(cnf_transformation,[],[f37])).
% 11.97/2.00  
% 11.97/2.00  fof(f25,conjecture,(
% 11.97/2.00    ! [X0] : k1_xboole_0 = k10_relat_1(k1_xboole_0,X0)),
% 11.97/2.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 11.97/2.00  
% 11.97/2.00  fof(f26,negated_conjecture,(
% 11.97/2.00    ~! [X0] : k1_xboole_0 = k10_relat_1(k1_xboole_0,X0)),
% 11.97/2.00    inference(negated_conjecture,[],[f25])).
% 11.97/2.00  
% 11.97/2.00  fof(f38,plain,(
% 11.97/2.00    ? [X0] : k1_xboole_0 != k10_relat_1(k1_xboole_0,X0)),
% 11.97/2.00    inference(ennf_transformation,[],[f26])).
% 11.97/2.00  
% 11.97/2.00  fof(f47,plain,(
% 11.97/2.00    ? [X0] : k1_xboole_0 != k10_relat_1(k1_xboole_0,X0) => k1_xboole_0 != k10_relat_1(k1_xboole_0,sK2)),
% 11.97/2.00    introduced(choice_axiom,[])).
% 11.97/2.00  
% 11.97/2.00  fof(f48,plain,(
% 11.97/2.00    k1_xboole_0 != k10_relat_1(k1_xboole_0,sK2)),
% 11.97/2.00    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2])],[f38,f47])).
% 11.97/2.00  
% 11.97/2.00  fof(f80,plain,(
% 11.97/2.00    k1_xboole_0 != k10_relat_1(k1_xboole_0,sK2)),
% 11.97/2.00    inference(cnf_transformation,[],[f48])).
% 11.97/2.00  
% 11.97/2.00  fof(f15,axiom,(
% 11.97/2.00    ! [X0,X1] : (k4_xboole_0(k1_tarski(X0),k1_tarski(X1)) = k1_tarski(X0) <=> X0 != X1)),
% 11.97/2.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 11.97/2.00  
% 11.97/2.00  fof(f43,plain,(
% 11.97/2.00    ! [X0,X1] : ((k4_xboole_0(k1_tarski(X0),k1_tarski(X1)) = k1_tarski(X0) | X0 = X1) & (X0 != X1 | k4_xboole_0(k1_tarski(X0),k1_tarski(X1)) != k1_tarski(X0)))),
% 11.97/2.00    inference(nnf_transformation,[],[f15])).
% 11.97/2.00  
% 11.97/2.00  fof(f66,plain,(
% 11.97/2.00    ( ! [X0,X1] : (X0 != X1 | k4_xboole_0(k1_tarski(X0),k1_tarski(X1)) != k1_tarski(X0)) )),
% 11.97/2.00    inference(cnf_transformation,[],[f43])).
% 11.97/2.00  
% 11.97/2.00  fof(f94,plain,(
% 11.97/2.00    ( ! [X0,X1] : (X0 != X1 | k4_xboole_0(k2_tarski(X0,X0),k2_tarski(X1,X1)) != k2_tarski(X0,X0)) )),
% 11.97/2.00    inference(definition_unfolding,[],[f66,f64,f64,f64])).
% 11.97/2.00  
% 11.97/2.00  fof(f101,plain,(
% 11.97/2.00    ( ! [X1] : (k4_xboole_0(k2_tarski(X1,X1),k2_tarski(X1,X1)) != k2_tarski(X1,X1)) )),
% 11.97/2.00    inference(equality_resolution,[],[f94])).
% 11.97/2.00  
% 11.97/2.00  fof(f67,plain,(
% 11.97/2.00    ( ! [X0,X1] : (k4_xboole_0(k1_tarski(X0),k1_tarski(X1)) = k1_tarski(X0) | X0 = X1) )),
% 11.97/2.00    inference(cnf_transformation,[],[f43])).
% 11.97/2.00  
% 11.97/2.00  fof(f93,plain,(
% 11.97/2.00    ( ! [X0,X1] : (k4_xboole_0(k2_tarski(X0,X0),k2_tarski(X1,X1)) = k2_tarski(X0,X0) | X0 = X1) )),
% 11.97/2.00    inference(definition_unfolding,[],[f67,f64,f64,f64])).
% 11.97/2.00  
% 11.97/2.00  cnf(c_24,plain,
% 11.97/2.00      ( r2_hidden(sK1(X0),X0) | v1_relat_1(X0) ),
% 11.97/2.00      inference(cnf_transformation,[],[f74]) ).
% 11.97/2.00  
% 11.97/2.00  cnf(c_59385,plain,
% 11.97/2.00      ( r2_hidden(sK1(X0),X0) = iProver_top
% 11.97/2.00      | v1_relat_1(X0) = iProver_top ),
% 11.97/2.00      inference(predicate_to_equality,[status(thm)],[c_24]) ).
% 11.97/2.00  
% 11.97/2.00  cnf(c_21,plain,
% 11.97/2.00      ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0)) ),
% 11.97/2.00      inference(cnf_transformation,[],[f72]) ).
% 11.97/2.00  
% 11.97/2.00  cnf(c_59386,plain,
% 11.97/2.00      ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0)) = iProver_top ),
% 11.97/2.00      inference(predicate_to_equality,[status(thm)],[c_21]) ).
% 11.97/2.00  
% 11.97/2.00  cnf(c_20,plain,
% 11.97/2.00      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
% 11.97/2.00      | ~ r2_hidden(X2,X0)
% 11.97/2.00      | r2_hidden(X2,X1) ),
% 11.97/2.00      inference(cnf_transformation,[],[f71]) ).
% 11.97/2.00  
% 11.97/2.00  cnf(c_59387,plain,
% 11.97/2.00      ( m1_subset_1(X0,k1_zfmisc_1(X1)) != iProver_top
% 11.97/2.00      | r2_hidden(X2,X0) != iProver_top
% 11.97/2.00      | r2_hidden(X2,X1) = iProver_top ),
% 11.97/2.00      inference(predicate_to_equality,[status(thm)],[c_20]) ).
% 11.97/2.00  
% 11.97/2.00  cnf(c_59792,plain,
% 11.97/2.00      ( r2_hidden(X0,X1) = iProver_top
% 11.97/2.00      | r2_hidden(X0,k1_xboole_0) != iProver_top ),
% 11.97/2.00      inference(superposition,[status(thm)],[c_59386,c_59387]) ).
% 11.97/2.00  
% 11.97/2.00  cnf(c_59797,plain,
% 11.97/2.00      ( r2_hidden(sK1(k1_xboole_0),X0) = iProver_top
% 11.97/2.00      | v1_relat_1(k1_xboole_0) = iProver_top ),
% 11.97/2.00      inference(superposition,[status(thm)],[c_59385,c_59792]) ).
% 11.97/2.00  
% 11.97/2.00  cnf(c_13,plain,
% 11.97/2.00      ( ~ r2_hidden(X0,k2_tarski(X1,X1)) | X0 = X1 ),
% 11.97/2.00      inference(cnf_transformation,[],[f100]) ).
% 11.97/2.00  
% 11.97/2.00  cnf(c_59388,plain,
% 11.97/2.00      ( X0 = X1 | r2_hidden(X0,k2_tarski(X1,X1)) != iProver_top ),
% 11.97/2.00      inference(predicate_to_equality,[status(thm)],[c_13]) ).
% 11.97/2.00  
% 11.97/2.00  cnf(c_59872,plain,
% 11.97/2.00      ( sK1(k1_xboole_0) = X0 | v1_relat_1(k1_xboole_0) = iProver_top ),
% 11.97/2.00      inference(superposition,[status(thm)],[c_59797,c_59388]) ).
% 11.97/2.00  
% 11.97/2.00  cnf(c_25,plain,
% 11.97/2.00      ( ~ v1_relat_1(X0)
% 11.97/2.00      | k10_relat_1(X0,k4_xboole_0(k2_relat_1(X0),k4_xboole_0(k2_relat_1(X0),X1))) = k10_relat_1(X0,X1) ),
% 11.97/2.00      inference(cnf_transformation,[],[f97]) ).
% 11.97/2.00  
% 11.97/2.00  cnf(c_59384,plain,
% 11.97/2.00      ( k10_relat_1(X0,k4_xboole_0(k2_relat_1(X0),k4_xboole_0(k2_relat_1(X0),X1))) = k10_relat_1(X0,X1)
% 11.97/2.00      | v1_relat_1(X0) != iProver_top ),
% 11.97/2.00      inference(predicate_to_equality,[status(thm)],[c_25]) ).
% 11.97/2.00  
% 11.97/2.00  cnf(c_59884,plain,
% 11.97/2.00      ( k10_relat_1(k1_xboole_0,k4_xboole_0(k2_relat_1(k1_xboole_0),k4_xboole_0(k2_relat_1(k1_xboole_0),X0))) = k10_relat_1(k1_xboole_0,X0)
% 11.97/2.00      | sK1(k1_xboole_0) = X1 ),
% 11.97/2.00      inference(superposition,[status(thm)],[c_59872,c_59384]) ).
% 11.97/2.00  
% 11.97/2.00  cnf(c_6,plain,
% 11.97/2.00      ( k4_xboole_0(k1_xboole_0,X0) = k1_xboole_0 ),
% 11.97/2.00      inference(cnf_transformation,[],[f55]) ).
% 11.97/2.00  
% 11.97/2.00  cnf(c_27,plain,
% 11.97/2.00      ( k2_relat_1(k1_xboole_0) = k1_xboole_0 ),
% 11.97/2.00      inference(cnf_transformation,[],[f79]) ).
% 11.97/2.00  
% 11.97/2.00  cnf(c_59892,plain,
% 11.97/2.00      ( k10_relat_1(k1_xboole_0,k4_xboole_0(k1_xboole_0,k1_xboole_0)) = k10_relat_1(k1_xboole_0,X0)
% 11.97/2.00      | sK1(k1_xboole_0) = X1 ),
% 11.97/2.00      inference(light_normalisation,[status(thm)],[c_59884,c_6,c_27]) ).
% 11.97/2.00  
% 11.97/2.00  cnf(c_59893,plain,
% 11.97/2.00      ( k10_relat_1(k1_xboole_0,X0) = k10_relat_1(k1_xboole_0,k1_xboole_0)
% 11.97/2.00      | sK1(k1_xboole_0) = X1 ),
% 11.97/2.00      inference(demodulation,[status(thm)],[c_59892,c_6]) ).
% 11.97/2.00  
% 11.97/2.00  cnf(c_26,plain,
% 11.97/2.00      ( ~ v1_relat_1(X0) | k10_relat_1(X0,k1_xboole_0) = k1_xboole_0 ),
% 11.97/2.00      inference(cnf_transformation,[],[f77]) ).
% 11.97/2.00  
% 11.97/2.00  cnf(c_59383,plain,
% 11.97/2.00      ( k10_relat_1(X0,k1_xboole_0) = k1_xboole_0
% 11.97/2.00      | v1_relat_1(X0) != iProver_top ),
% 11.97/2.00      inference(predicate_to_equality,[status(thm)],[c_26]) ).
% 11.97/2.00  
% 11.97/2.00  cnf(c_59885,plain,
% 11.97/2.00      ( k10_relat_1(k1_xboole_0,k1_xboole_0) = k1_xboole_0
% 11.97/2.00      | sK1(k1_xboole_0) = X0 ),
% 11.97/2.00      inference(superposition,[status(thm)],[c_59872,c_59383]) ).
% 11.97/2.00  
% 11.97/2.00  cnf(c_31,plain,
% 11.97/2.00      ( ~ v1_relat_1(k1_xboole_0)
% 11.97/2.00      | k10_relat_1(k1_xboole_0,k1_xboole_0) = k1_xboole_0 ),
% 11.97/2.00      inference(instantiation,[status(thm)],[c_26]) ).
% 11.97/2.00  
% 11.97/2.00  cnf(c_59741,plain,
% 11.97/2.00      ( r2_hidden(X0,X1) | ~ r2_hidden(X0,k1_xboole_0) ),
% 11.97/2.00      inference(resolution,[status(thm)],[c_20,c_21]) ).
% 11.97/2.00  
% 11.97/2.00  cnf(c_59818,plain,
% 11.97/2.00      ( r2_hidden(sK1(k1_xboole_0),X0) | v1_relat_1(k1_xboole_0) ),
% 11.97/2.00      inference(resolution,[status(thm)],[c_59741,c_24]) ).
% 11.97/2.00  
% 11.97/2.00  cnf(c_59904,plain,
% 11.97/2.00      ( v1_relat_1(k1_xboole_0) | sK1(k1_xboole_0) = X0 ),
% 11.97/2.00      inference(resolution,[status(thm)],[c_59818,c_13]) ).
% 11.97/2.00  
% 11.97/2.00  cnf(c_249,plain,( X0 != X1 | X2 != X1 | X2 = X0 ),theory(equality) ).
% 11.97/2.00  
% 11.97/2.00  cnf(c_248,plain,( X0 = X0 ),theory(equality) ).
% 11.97/2.00  
% 11.97/2.00  cnf(c_59581,plain,
% 11.97/2.00      ( X0 != X1 | X1 = X0 ),
% 11.97/2.00      inference(resolution,[status(thm)],[c_249,c_248]) ).
% 11.97/2.00  
% 11.97/2.00  cnf(c_59913,plain,
% 11.97/2.00      ( v1_relat_1(k1_xboole_0) | X0 = sK1(k1_xboole_0) ),
% 11.97/2.00      inference(resolution,[status(thm)],[c_59904,c_59581]) ).
% 11.97/2.00  
% 11.97/2.00  cnf(c_29,negated_conjecture,
% 11.97/2.00      ( k1_xboole_0 != k10_relat_1(k1_xboole_0,sK2) ),
% 11.97/2.00      inference(cnf_transformation,[],[f80]) ).
% 11.97/2.00  
% 11.97/2.00  cnf(c_37,plain,
% 11.97/2.00      ( r2_hidden(sK1(k1_xboole_0),k1_xboole_0)
% 11.97/2.00      | v1_relat_1(k1_xboole_0) ),
% 11.97/2.00      inference(instantiation,[status(thm)],[c_24]) ).
% 11.97/2.00  
% 11.97/2.00  cnf(c_16,plain,
% 11.97/2.00      ( k4_xboole_0(k2_tarski(X0,X0),k2_tarski(X0,X0)) != k2_tarski(X0,X0) ),
% 11.97/2.00      inference(cnf_transformation,[],[f101]) ).
% 11.97/2.00  
% 11.97/2.00  cnf(c_58,plain,
% 11.97/2.00      ( k4_xboole_0(k2_tarski(k1_xboole_0,k1_xboole_0),k2_tarski(k1_xboole_0,k1_xboole_0)) != k2_tarski(k1_xboole_0,k1_xboole_0) ),
% 11.97/2.00      inference(instantiation,[status(thm)],[c_16]) ).
% 11.97/2.00  
% 11.97/2.00  cnf(c_15,plain,
% 11.97/2.00      ( X0 = X1
% 11.97/2.00      | k4_xboole_0(k2_tarski(X1,X1),k2_tarski(X0,X0)) = k2_tarski(X1,X1) ),
% 11.97/2.00      inference(cnf_transformation,[],[f93]) ).
% 11.97/2.00  
% 11.97/2.00  cnf(c_59,plain,
% 11.97/2.00      ( k4_xboole_0(k2_tarski(k1_xboole_0,k1_xboole_0),k2_tarski(k1_xboole_0,k1_xboole_0)) = k2_tarski(k1_xboole_0,k1_xboole_0)
% 11.97/2.00      | k1_xboole_0 = k1_xboole_0 ),
% 11.97/2.00      inference(instantiation,[status(thm)],[c_15]) ).
% 11.97/2.00  
% 11.97/2.00  cnf(c_2447,plain,
% 11.97/2.00      ( ~ r2_hidden(k1_xboole_0,k2_tarski(k10_relat_1(k1_xboole_0,sK2),k10_relat_1(k1_xboole_0,sK2)))
% 11.97/2.00      | k1_xboole_0 = k10_relat_1(k1_xboole_0,sK2) ),
% 11.97/2.00      inference(instantiation,[status(thm)],[c_13]) ).
% 11.97/2.00  
% 11.97/2.00  cnf(c_21400,plain,
% 11.97/2.00      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_tarski(k10_relat_1(k1_xboole_0,sK2),k10_relat_1(k1_xboole_0,sK2))))
% 11.97/2.00      | ~ r2_hidden(k1_xboole_0,X0)
% 11.97/2.00      | r2_hidden(k1_xboole_0,k2_tarski(k10_relat_1(k1_xboole_0,sK2),k10_relat_1(k1_xboole_0,sK2))) ),
% 11.97/2.00      inference(instantiation,[status(thm)],[c_20]) ).
% 11.97/2.00  
% 11.97/2.00  cnf(c_21407,plain,
% 11.97/2.00      ( ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_tarski(k10_relat_1(k1_xboole_0,sK2),k10_relat_1(k1_xboole_0,sK2))))
% 11.97/2.00      | r2_hidden(k1_xboole_0,k2_tarski(k10_relat_1(k1_xboole_0,sK2),k10_relat_1(k1_xboole_0,sK2)))
% 11.97/2.00      | ~ r2_hidden(k1_xboole_0,k1_xboole_0) ),
% 11.97/2.00      inference(instantiation,[status(thm)],[c_21400]) ).
% 11.97/2.00  
% 11.97/2.00  cnf(c_21422,plain,
% 11.97/2.00      ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_tarski(k10_relat_1(k1_xboole_0,sK2),k10_relat_1(k1_xboole_0,sK2)))) ),
% 11.97/2.00      inference(instantiation,[status(thm)],[c_21]) ).
% 11.97/2.00  
% 11.97/2.00  cnf(c_255,plain,
% 11.97/2.00      ( ~ r2_hidden(X0,X1) | r2_hidden(X2,X3) | X2 != X0 | X3 != X1 ),
% 11.97/2.00      theory(equality) ).
% 11.97/2.00  
% 11.97/2.00  cnf(c_59523,plain,
% 11.97/2.00      ( r2_hidden(X0,X1)
% 11.97/2.00      | ~ r2_hidden(sK1(X2),X2)
% 11.97/2.00      | X1 != X2
% 11.97/2.00      | X0 != sK1(X2) ),
% 11.97/2.00      inference(instantiation,[status(thm)],[c_255]) ).
% 11.97/2.00  
% 11.97/2.00  cnf(c_59525,plain,
% 11.97/2.00      ( ~ r2_hidden(sK1(k1_xboole_0),k1_xboole_0)
% 11.97/2.00      | r2_hidden(k1_xboole_0,k1_xboole_0)
% 11.97/2.00      | k1_xboole_0 != sK1(k1_xboole_0)
% 11.97/2.00      | k1_xboole_0 != k1_xboole_0 ),
% 11.97/2.00      inference(instantiation,[status(thm)],[c_59523]) ).
% 11.97/2.00  
% 11.97/2.00  cnf(c_59915,plain,
% 11.97/2.00      ( v1_relat_1(k1_xboole_0) | k1_xboole_0 = sK1(k1_xboole_0) ),
% 11.97/2.00      inference(instantiation,[status(thm)],[c_59913]) ).
% 11.97/2.00  
% 11.97/2.00  cnf(c_59922,plain,
% 11.97/2.00      ( v1_relat_1(k1_xboole_0) ),
% 11.97/2.00      inference(global_propositional_subsumption,
% 11.97/2.00                [status(thm)],
% 11.97/2.00                [c_59913,c_29,c_37,c_58,c_59,c_2447,c_21407,c_21422,
% 11.97/2.00                 c_59525,c_59915]) ).
% 11.97/2.00  
% 11.97/2.00  cnf(c_59987,plain,
% 11.97/2.00      ( k10_relat_1(k1_xboole_0,k1_xboole_0) = k1_xboole_0 ),
% 11.97/2.00      inference(global_propositional_subsumption,
% 11.97/2.00                [status(thm)],
% 11.97/2.00                [c_59885,c_29,c_31,c_37,c_58,c_59,c_2447,c_21407,c_21422,
% 11.97/2.00                 c_59525,c_59915]) ).
% 11.97/2.00  
% 11.97/2.00  cnf(c_59990,plain,
% 11.97/2.00      ( k10_relat_1(k1_xboole_0,X0) = k1_xboole_0
% 11.97/2.00      | sK1(k1_xboole_0) = X1 ),
% 11.97/2.00      inference(light_normalisation,[status(thm)],[c_59893,c_59987]) ).
% 11.97/2.00  
% 11.97/2.00  cnf(c_60013,plain,
% 11.97/2.00      ( sK1(k1_xboole_0) = X0 ),
% 11.97/2.00      inference(superposition,[status(thm)],[c_59990,c_29]) ).
% 11.97/2.00  
% 11.97/2.00  cnf(c_60117,plain,
% 11.97/2.00      ( sK1(k1_xboole_0) != k1_xboole_0 ),
% 11.97/2.00      inference(demodulation,[status(thm)],[c_60013,c_29]) ).
% 11.97/2.00  
% 11.97/2.00  cnf(c_60028,plain,
% 11.97/2.00      ( sK1(k1_xboole_0) = k1_xboole_0 ),
% 11.97/2.00      inference(instantiation,[status(thm)],[c_60013]) ).
% 11.97/2.00  
% 11.97/2.00  cnf(contradiction,plain,
% 11.97/2.00      ( $false ),
% 11.97/2.00      inference(minisat,[status(thm)],[c_60117,c_60028]) ).
% 11.97/2.00  
% 11.97/2.00  
% 11.97/2.00  % SZS output end CNFRefutation for theBenchmark.p
% 11.97/2.00  
% 11.97/2.00  ------                               Statistics
% 11.97/2.00  
% 11.97/2.00  ------ Selected
% 11.97/2.00  
% 11.97/2.00  total_time:                             1.473
% 11.97/2.00  
%------------------------------------------------------------------------------
