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
% DateTime   : Thu Dec  3 11:43:12 EST 2020

% Result     : Theorem 3.78s
% Output     : CNFRefutation 3.78s
% Verified   : 
% Statistics : Number of formulae       :   86 ( 180 expanded)
%              Number of clauses        :   48 (  66 expanded)
%              Number of leaves         :   12 (  41 expanded)
%              Depth                    :   15
%              Number of atoms          :  196 ( 525 expanded)
%              Number of equality atoms :   61 (  87 expanded)
%              Maximal formula depth    :    7 (   4 average)
%              Maximal clause size      :    8 (   2 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f12,conjecture,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( v1_relat_1(X1)
         => ( r1_tarski(X0,X1)
           => r1_tarski(k3_relat_1(X0),k3_relat_1(X1)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f13,negated_conjecture,(
    ~ ! [X0] :
        ( v1_relat_1(X0)
       => ! [X1] :
            ( v1_relat_1(X1)
           => ( r1_tarski(X0,X1)
             => r1_tarski(k3_relat_1(X0),k3_relat_1(X1)) ) ) ) ),
    inference(negated_conjecture,[],[f12])).

fof(f22,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ~ r1_tarski(k3_relat_1(X0),k3_relat_1(X1))
          & r1_tarski(X0,X1)
          & v1_relat_1(X1) )
      & v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f23,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ~ r1_tarski(k3_relat_1(X0),k3_relat_1(X1))
          & r1_tarski(X0,X1)
          & v1_relat_1(X1) )
      & v1_relat_1(X0) ) ),
    inference(flattening,[],[f22])).

fof(f28,plain,(
    ! [X0] :
      ( ? [X1] :
          ( ~ r1_tarski(k3_relat_1(X0),k3_relat_1(X1))
          & r1_tarski(X0,X1)
          & v1_relat_1(X1) )
     => ( ~ r1_tarski(k3_relat_1(X0),k3_relat_1(sK1))
        & r1_tarski(X0,sK1)
        & v1_relat_1(sK1) ) ) ),
    introduced(choice_axiom,[])).

fof(f27,plain,
    ( ? [X0] :
        ( ? [X1] :
            ( ~ r1_tarski(k3_relat_1(X0),k3_relat_1(X1))
            & r1_tarski(X0,X1)
            & v1_relat_1(X1) )
        & v1_relat_1(X0) )
   => ( ? [X1] :
          ( ~ r1_tarski(k3_relat_1(sK0),k3_relat_1(X1))
          & r1_tarski(sK0,X1)
          & v1_relat_1(X1) )
      & v1_relat_1(sK0) ) ),
    introduced(choice_axiom,[])).

fof(f29,plain,
    ( ~ r1_tarski(k3_relat_1(sK0),k3_relat_1(sK1))
    & r1_tarski(sK0,sK1)
    & v1_relat_1(sK1)
    & v1_relat_1(sK0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f23,f28,f27])).

fof(f47,plain,(
    r1_tarski(sK0,sK1) ),
    inference(cnf_transformation,[],[f29])).

fof(f11,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( v1_relat_1(X1)
         => ( r1_tarski(X0,X1)
           => ( r1_tarski(k2_relat_1(X0),k2_relat_1(X1))
              & r1_tarski(k1_relat_1(X0),k1_relat_1(X1)) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f20,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( r1_tarski(k2_relat_1(X0),k2_relat_1(X1))
            & r1_tarski(k1_relat_1(X0),k1_relat_1(X1)) )
          | ~ r1_tarski(X0,X1)
          | ~ v1_relat_1(X1) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f21,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( r1_tarski(k2_relat_1(X0),k2_relat_1(X1))
            & r1_tarski(k1_relat_1(X0),k1_relat_1(X1)) )
          | ~ r1_tarski(X0,X1)
          | ~ v1_relat_1(X1) )
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f20])).

fof(f44,plain,(
    ! [X0,X1] :
      ( r1_tarski(k2_relat_1(X0),k2_relat_1(X1))
      | ~ r1_tarski(X0,X1)
      | ~ v1_relat_1(X1)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f9,axiom,(
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
    inference(ennf_transformation,[],[f9])).

fof(f41,plain,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f8,axiom,(
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
    inference(nnf_transformation,[],[f8])).

fof(f40,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f5,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
     => k2_xboole_0(X0,X1) = X1 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f16,plain,(
    ! [X0,X1] :
      ( k2_xboole_0(X0,X1) = X1
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f36,plain,(
    ! [X0,X1] :
      ( k2_xboole_0(X0,X1) = X1
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f16])).

fof(f46,plain,(
    v1_relat_1(sK1) ),
    inference(cnf_transformation,[],[f29])).

fof(f6,axiom,(
    ! [X0,X1] : r1_tarski(X0,k2_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f37,plain,(
    ! [X0,X1] : r1_tarski(X0,k2_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f6])).

fof(f10,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => k2_xboole_0(k1_relat_1(X0),k2_relat_1(X0)) = k3_relat_1(X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f19,plain,(
    ! [X0] :
      ( k2_xboole_0(k1_relat_1(X0),k2_relat_1(X0)) = k3_relat_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f42,plain,(
    ! [X0] :
      ( k2_xboole_0(k1_relat_1(X0),k2_relat_1(X0)) = k3_relat_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f3,axiom,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,X1)
     => r1_tarski(X0,k2_xboole_0(X2,X1)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f14,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,k2_xboole_0(X2,X1))
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f34,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(X0,k2_xboole_0(X2,X1))
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f14])).

fof(f45,plain,(
    v1_relat_1(sK0) ),
    inference(cnf_transformation,[],[f29])).

fof(f1,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f30,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f1])).

fof(f7,axiom,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,X1)
     => r1_tarski(k2_xboole_0(X0,X2),k2_xboole_0(X1,X2)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f17,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(k2_xboole_0(X0,X2),k2_xboole_0(X1,X2))
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f38,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(k2_xboole_0(X0,X2),k2_xboole_0(X1,X2))
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f43,plain,(
    ! [X0,X1] :
      ( r1_tarski(k1_relat_1(X0),k1_relat_1(X1))
      | ~ r1_tarski(X0,X1)
      | ~ v1_relat_1(X1)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f48,plain,(
    ~ r1_tarski(k3_relat_1(sK0),k3_relat_1(sK1)) ),
    inference(cnf_transformation,[],[f29])).

cnf(c_16,negated_conjecture,
    ( r1_tarski(sK0,sK1) ),
    inference(cnf_transformation,[],[f47])).

cnf(c_691,plain,
    ( r1_tarski(sK0,sK1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_16])).

cnf(c_13,plain,
    ( ~ r1_tarski(X0,X1)
    | r1_tarski(k2_relat_1(X0),k2_relat_1(X1))
    | ~ v1_relat_1(X0)
    | ~ v1_relat_1(X1) ),
    inference(cnf_transformation,[],[f44])).

cnf(c_11,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | ~ v1_relat_1(X1)
    | v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f41])).

cnf(c_9,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(X1))
    | ~ r1_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f40])).

cnf(c_188,plain,
    ( r1_tarski(k2_relat_1(X0),k2_relat_1(X1))
    | ~ r1_tarski(X0,X1)
    | ~ v1_relat_1(X1) ),
    inference(global_propositional_subsumption,[status(thm)],[c_13,c_11,c_9])).

cnf(c_189,plain,
    ( ~ r1_tarski(X0,X1)
    | r1_tarski(k2_relat_1(X0),k2_relat_1(X1))
    | ~ v1_relat_1(X1) ),
    inference(renaming,[status(thm)],[c_188])).

cnf(c_686,plain,
    ( r1_tarski(X0,X1) != iProver_top
    | r1_tarski(k2_relat_1(X0),k2_relat_1(X1)) = iProver_top
    | v1_relat_1(X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_189])).

cnf(c_6,plain,
    ( ~ r1_tarski(X0,X1)
    | k2_xboole_0(X0,X1) = X1 ),
    inference(cnf_transformation,[],[f36])).

cnf(c_698,plain,
    ( k2_xboole_0(X0,X1) = X1
    | r1_tarski(X0,X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_6])).

cnf(c_1165,plain,
    ( k2_xboole_0(k2_relat_1(X0),k2_relat_1(X1)) = k2_relat_1(X1)
    | r1_tarski(X0,X1) != iProver_top
    | v1_relat_1(X1) != iProver_top ),
    inference(superposition,[status(thm)],[c_686,c_698])).

cnf(c_7367,plain,
    ( k2_xboole_0(k2_relat_1(sK0),k2_relat_1(sK1)) = k2_relat_1(sK1)
    | v1_relat_1(sK1) != iProver_top ),
    inference(superposition,[status(thm)],[c_691,c_1165])).

cnf(c_17,negated_conjecture,
    ( v1_relat_1(sK1) ),
    inference(cnf_transformation,[],[f46])).

cnf(c_20,plain,
    ( v1_relat_1(sK1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_17])).

cnf(c_8429,plain,
    ( k2_xboole_0(k2_relat_1(sK0),k2_relat_1(sK1)) = k2_relat_1(sK1) ),
    inference(global_propositional_subsumption,[status(thm)],[c_7367,c_20])).

cnf(c_7,plain,
    ( r1_tarski(X0,k2_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f37])).

cnf(c_697,plain,
    ( r1_tarski(X0,k2_xboole_0(X0,X1)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_7])).

cnf(c_8432,plain,
    ( r1_tarski(k2_relat_1(sK0),k2_relat_1(sK1)) = iProver_top ),
    inference(superposition,[status(thm)],[c_8429,c_697])).

cnf(c_690,plain,
    ( v1_relat_1(sK1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_17])).

cnf(c_12,plain,
    ( ~ v1_relat_1(X0)
    | k2_xboole_0(k1_relat_1(X0),k2_relat_1(X0)) = k3_relat_1(X0) ),
    inference(cnf_transformation,[],[f42])).

cnf(c_693,plain,
    ( k2_xboole_0(k1_relat_1(X0),k2_relat_1(X0)) = k3_relat_1(X0)
    | v1_relat_1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_12])).

cnf(c_1407,plain,
    ( k2_xboole_0(k1_relat_1(sK1),k2_relat_1(sK1)) = k3_relat_1(sK1) ),
    inference(superposition,[status(thm)],[c_690,c_693])).

cnf(c_4,plain,
    ( ~ r1_tarski(X0,X1)
    | r1_tarski(X0,k2_xboole_0(X2,X1)) ),
    inference(cnf_transformation,[],[f34])).

cnf(c_700,plain,
    ( r1_tarski(X0,X1) != iProver_top
    | r1_tarski(X0,k2_xboole_0(X2,X1)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_4])).

cnf(c_2133,plain,
    ( r1_tarski(X0,k3_relat_1(sK1)) = iProver_top
    | r1_tarski(X0,k2_relat_1(sK1)) != iProver_top ),
    inference(superposition,[status(thm)],[c_1407,c_700])).

cnf(c_8768,plain,
    ( r1_tarski(k2_relat_1(sK0),k3_relat_1(sK1)) = iProver_top ),
    inference(superposition,[status(thm)],[c_8432,c_2133])).

cnf(c_17585,plain,
    ( k2_xboole_0(k2_relat_1(sK0),k3_relat_1(sK1)) = k3_relat_1(sK1) ),
    inference(superposition,[status(thm)],[c_8768,c_698])).

cnf(c_18,negated_conjecture,
    ( v1_relat_1(sK0) ),
    inference(cnf_transformation,[],[f45])).

cnf(c_689,plain,
    ( v1_relat_1(sK0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_18])).

cnf(c_1408,plain,
    ( k2_xboole_0(k1_relat_1(sK0),k2_relat_1(sK0)) = k3_relat_1(sK0) ),
    inference(superposition,[status(thm)],[c_689,c_693])).

cnf(c_0,plain,
    ( k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f30])).

cnf(c_8,plain,
    ( ~ r1_tarski(X0,X1)
    | r1_tarski(k2_xboole_0(X0,X2),k2_xboole_0(X1,X2)) ),
    inference(cnf_transformation,[],[f38])).

cnf(c_696,plain,
    ( r1_tarski(X0,X1) != iProver_top
    | r1_tarski(k2_xboole_0(X0,X2),k2_xboole_0(X1,X2)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_8])).

cnf(c_3655,plain,
    ( r1_tarski(X0,X1) != iProver_top
    | r1_tarski(k2_xboole_0(X0,X2),k2_xboole_0(X2,X1)) = iProver_top ),
    inference(superposition,[status(thm)],[c_0,c_696])).

cnf(c_3967,plain,
    ( r1_tarski(k3_relat_1(sK0),k2_xboole_0(k2_relat_1(sK0),X0)) = iProver_top
    | r1_tarski(k1_relat_1(sK0),X0) != iProver_top ),
    inference(superposition,[status(thm)],[c_1408,c_3655])).

cnf(c_18237,plain,
    ( r1_tarski(k3_relat_1(sK0),k3_relat_1(sK1)) = iProver_top
    | r1_tarski(k1_relat_1(sK0),k3_relat_1(sK1)) != iProver_top ),
    inference(superposition,[status(thm)],[c_17585,c_3967])).

cnf(c_14,plain,
    ( ~ r1_tarski(X0,X1)
    | r1_tarski(k1_relat_1(X0),k1_relat_1(X1))
    | ~ v1_relat_1(X0)
    | ~ v1_relat_1(X1) ),
    inference(cnf_transformation,[],[f43])).

cnf(c_181,plain,
    ( r1_tarski(k1_relat_1(X0),k1_relat_1(X1))
    | ~ r1_tarski(X0,X1)
    | ~ v1_relat_1(X1) ),
    inference(global_propositional_subsumption,[status(thm)],[c_14,c_11,c_9])).

cnf(c_182,plain,
    ( ~ r1_tarski(X0,X1)
    | r1_tarski(k1_relat_1(X0),k1_relat_1(X1))
    | ~ v1_relat_1(X1) ),
    inference(renaming,[status(thm)],[c_181])).

cnf(c_687,plain,
    ( r1_tarski(X0,X1) != iProver_top
    | r1_tarski(k1_relat_1(X0),k1_relat_1(X1)) = iProver_top
    | v1_relat_1(X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_182])).

cnf(c_2129,plain,
    ( r1_tarski(X0,X1) != iProver_top
    | r1_tarski(X0,k2_xboole_0(X1,X2)) = iProver_top ),
    inference(superposition,[status(thm)],[c_0,c_700])).

cnf(c_2392,plain,
    ( r1_tarski(X0,k3_relat_1(sK1)) = iProver_top
    | r1_tarski(X0,k1_relat_1(sK1)) != iProver_top ),
    inference(superposition,[status(thm)],[c_1407,c_2129])).

cnf(c_4524,plain,
    ( r1_tarski(X0,sK1) != iProver_top
    | r1_tarski(k1_relat_1(X0),k3_relat_1(sK1)) = iProver_top
    | v1_relat_1(sK1) != iProver_top ),
    inference(superposition,[status(thm)],[c_687,c_2392])).

cnf(c_4532,plain,
    ( r1_tarski(k1_relat_1(sK0),k3_relat_1(sK1)) = iProver_top
    | r1_tarski(sK0,sK1) != iProver_top
    | v1_relat_1(sK1) != iProver_top ),
    inference(instantiation,[status(thm)],[c_4524])).

cnf(c_15,negated_conjecture,
    ( ~ r1_tarski(k3_relat_1(sK0),k3_relat_1(sK1)) ),
    inference(cnf_transformation,[],[f48])).

cnf(c_22,plain,
    ( r1_tarski(k3_relat_1(sK0),k3_relat_1(sK1)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_15])).

cnf(c_21,plain,
    ( r1_tarski(sK0,sK1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_16])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_18237,c_4532,c_22,c_21,c_20])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : iproveropt_run.sh %d %s
% 0.13/0.34  % Computer   : n021.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 15:27:34 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running in FOF mode
% 3.78/1.00  % SZS status Started for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.78/1.00  
% 3.78/1.00  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 3.78/1.00  
% 3.78/1.00  ------  iProver source info
% 3.78/1.00  
% 3.78/1.00  git: date: 2020-06-30 10:37:57 +0100
% 3.78/1.00  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 3.78/1.00  git: non_committed_changes: false
% 3.78/1.00  git: last_make_outside_of_git: false
% 3.78/1.00  
% 3.78/1.00  ------ 
% 3.78/1.00  ------ Parsing...
% 3.78/1.00  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 3.78/1.00  
% 3.78/1.00  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 1 0s  sf_e 
% 3.78/1.00  
% 3.78/1.00  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 3.78/1.00  
% 3.78/1.00  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 3.78/1.00  ------ Proving...
% 3.78/1.00  ------ Problem Properties 
% 3.78/1.00  
% 3.78/1.00  
% 3.78/1.00  clauses                                 18
% 3.78/1.00  conjectures                             4
% 3.78/1.00  EPR                                     6
% 3.78/1.00  Horn                                    18
% 3.78/1.00  unary                                   7
% 3.78/1.00  binary                                  7
% 3.78/1.00  lits                                    33
% 3.78/1.00  lits eq                                 4
% 3.78/1.00  fd_pure                                 0
% 3.78/1.00  fd_pseudo                               0
% 3.78/1.00  fd_cond                                 0
% 3.78/1.00  fd_pseudo_cond                          1
% 3.78/1.00  AC symbols                              0
% 3.78/1.00  
% 3.78/1.00  ------ Input Options Time Limit: Unbounded
% 3.78/1.00  
% 3.78/1.00  
% 3.78/1.00  ------ 
% 3.78/1.00  Current options:
% 3.78/1.00  ------ 
% 3.78/1.00  
% 3.78/1.00  
% 3.78/1.00  
% 3.78/1.00  
% 3.78/1.00  ------ Proving...
% 3.78/1.00  
% 3.78/1.00  
% 3.78/1.00  % SZS status Theorem for theBenchmark.p
% 3.78/1.00  
% 3.78/1.00  % SZS output start CNFRefutation for theBenchmark.p
% 3.78/1.00  
% 3.78/1.00  fof(f12,conjecture,(
% 3.78/1.00    ! [X0] : (v1_relat_1(X0) => ! [X1] : (v1_relat_1(X1) => (r1_tarski(X0,X1) => r1_tarski(k3_relat_1(X0),k3_relat_1(X1)))))),
% 3.78/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.78/1.00  
% 3.78/1.00  fof(f13,negated_conjecture,(
% 3.78/1.00    ~! [X0] : (v1_relat_1(X0) => ! [X1] : (v1_relat_1(X1) => (r1_tarski(X0,X1) => r1_tarski(k3_relat_1(X0),k3_relat_1(X1)))))),
% 3.78/1.00    inference(negated_conjecture,[],[f12])).
% 3.78/1.00  
% 3.78/1.00  fof(f22,plain,(
% 3.78/1.00    ? [X0] : (? [X1] : ((~r1_tarski(k3_relat_1(X0),k3_relat_1(X1)) & r1_tarski(X0,X1)) & v1_relat_1(X1)) & v1_relat_1(X0))),
% 3.78/1.00    inference(ennf_transformation,[],[f13])).
% 3.78/1.00  
% 3.78/1.00  fof(f23,plain,(
% 3.78/1.00    ? [X0] : (? [X1] : (~r1_tarski(k3_relat_1(X0),k3_relat_1(X1)) & r1_tarski(X0,X1) & v1_relat_1(X1)) & v1_relat_1(X0))),
% 3.78/1.00    inference(flattening,[],[f22])).
% 3.78/1.00  
% 3.78/1.00  fof(f28,plain,(
% 3.78/1.00    ( ! [X0] : (? [X1] : (~r1_tarski(k3_relat_1(X0),k3_relat_1(X1)) & r1_tarski(X0,X1) & v1_relat_1(X1)) => (~r1_tarski(k3_relat_1(X0),k3_relat_1(sK1)) & r1_tarski(X0,sK1) & v1_relat_1(sK1))) )),
% 3.78/1.00    introduced(choice_axiom,[])).
% 3.78/1.00  
% 3.78/1.00  fof(f27,plain,(
% 3.78/1.00    ? [X0] : (? [X1] : (~r1_tarski(k3_relat_1(X0),k3_relat_1(X1)) & r1_tarski(X0,X1) & v1_relat_1(X1)) & v1_relat_1(X0)) => (? [X1] : (~r1_tarski(k3_relat_1(sK0),k3_relat_1(X1)) & r1_tarski(sK0,X1) & v1_relat_1(X1)) & v1_relat_1(sK0))),
% 3.78/1.00    introduced(choice_axiom,[])).
% 3.78/1.00  
% 3.78/1.00  fof(f29,plain,(
% 3.78/1.00    (~r1_tarski(k3_relat_1(sK0),k3_relat_1(sK1)) & r1_tarski(sK0,sK1) & v1_relat_1(sK1)) & v1_relat_1(sK0)),
% 3.78/1.00    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f23,f28,f27])).
% 3.78/1.00  
% 3.78/1.00  fof(f47,plain,(
% 3.78/1.00    r1_tarski(sK0,sK1)),
% 3.78/1.00    inference(cnf_transformation,[],[f29])).
% 3.78/1.00  
% 3.78/1.00  fof(f11,axiom,(
% 3.78/1.00    ! [X0] : (v1_relat_1(X0) => ! [X1] : (v1_relat_1(X1) => (r1_tarski(X0,X1) => (r1_tarski(k2_relat_1(X0),k2_relat_1(X1)) & r1_tarski(k1_relat_1(X0),k1_relat_1(X1))))))),
% 3.78/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.78/1.00  
% 3.78/1.00  fof(f20,plain,(
% 3.78/1.00    ! [X0] : (! [X1] : (((r1_tarski(k2_relat_1(X0),k2_relat_1(X1)) & r1_tarski(k1_relat_1(X0),k1_relat_1(X1))) | ~r1_tarski(X0,X1)) | ~v1_relat_1(X1)) | ~v1_relat_1(X0))),
% 3.78/1.00    inference(ennf_transformation,[],[f11])).
% 3.78/1.00  
% 3.78/1.00  fof(f21,plain,(
% 3.78/1.00    ! [X0] : (! [X1] : ((r1_tarski(k2_relat_1(X0),k2_relat_1(X1)) & r1_tarski(k1_relat_1(X0),k1_relat_1(X1))) | ~r1_tarski(X0,X1) | ~v1_relat_1(X1)) | ~v1_relat_1(X0))),
% 3.78/1.00    inference(flattening,[],[f20])).
% 3.78/1.00  
% 3.78/1.00  fof(f44,plain,(
% 3.78/1.00    ( ! [X0,X1] : (r1_tarski(k2_relat_1(X0),k2_relat_1(X1)) | ~r1_tarski(X0,X1) | ~v1_relat_1(X1) | ~v1_relat_1(X0)) )),
% 3.78/1.00    inference(cnf_transformation,[],[f21])).
% 3.78/1.00  
% 3.78/1.00  fof(f9,axiom,(
% 3.78/1.00    ! [X0] : (v1_relat_1(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => v1_relat_1(X1)))),
% 3.78/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.78/1.00  
% 3.78/1.00  fof(f18,plain,(
% 3.78/1.00    ! [X0] : (! [X1] : (v1_relat_1(X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) | ~v1_relat_1(X0))),
% 3.78/1.00    inference(ennf_transformation,[],[f9])).
% 3.78/1.00  
% 3.78/1.00  fof(f41,plain,(
% 3.78/1.00    ( ! [X0,X1] : (v1_relat_1(X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0)) | ~v1_relat_1(X0)) )),
% 3.78/1.00    inference(cnf_transformation,[],[f18])).
% 3.78/1.00  
% 3.78/1.00  fof(f8,axiom,(
% 3.78/1.00    ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) <=> r1_tarski(X0,X1))),
% 3.78/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.78/1.00  
% 3.78/1.00  fof(f26,plain,(
% 3.78/1.00    ! [X0,X1] : ((m1_subset_1(X0,k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1)) & (r1_tarski(X0,X1) | ~m1_subset_1(X0,k1_zfmisc_1(X1))))),
% 3.78/1.00    inference(nnf_transformation,[],[f8])).
% 3.78/1.00  
% 3.78/1.00  fof(f40,plain,(
% 3.78/1.00    ( ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1)) )),
% 3.78/1.00    inference(cnf_transformation,[],[f26])).
% 3.78/1.00  
% 3.78/1.00  fof(f5,axiom,(
% 3.78/1.00    ! [X0,X1] : (r1_tarski(X0,X1) => k2_xboole_0(X0,X1) = X1)),
% 3.78/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.78/1.00  
% 3.78/1.00  fof(f16,plain,(
% 3.78/1.00    ! [X0,X1] : (k2_xboole_0(X0,X1) = X1 | ~r1_tarski(X0,X1))),
% 3.78/1.00    inference(ennf_transformation,[],[f5])).
% 3.78/1.00  
% 3.78/1.00  fof(f36,plain,(
% 3.78/1.00    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = X1 | ~r1_tarski(X0,X1)) )),
% 3.78/1.00    inference(cnf_transformation,[],[f16])).
% 3.78/1.00  
% 3.78/1.00  fof(f46,plain,(
% 3.78/1.00    v1_relat_1(sK1)),
% 3.78/1.00    inference(cnf_transformation,[],[f29])).
% 3.78/1.00  
% 3.78/1.00  fof(f6,axiom,(
% 3.78/1.00    ! [X0,X1] : r1_tarski(X0,k2_xboole_0(X0,X1))),
% 3.78/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.78/1.00  
% 3.78/1.00  fof(f37,plain,(
% 3.78/1.00    ( ! [X0,X1] : (r1_tarski(X0,k2_xboole_0(X0,X1))) )),
% 3.78/1.00    inference(cnf_transformation,[],[f6])).
% 3.78/1.00  
% 3.78/1.00  fof(f10,axiom,(
% 3.78/1.00    ! [X0] : (v1_relat_1(X0) => k2_xboole_0(k1_relat_1(X0),k2_relat_1(X0)) = k3_relat_1(X0))),
% 3.78/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.78/1.00  
% 3.78/1.00  fof(f19,plain,(
% 3.78/1.00    ! [X0] : (k2_xboole_0(k1_relat_1(X0),k2_relat_1(X0)) = k3_relat_1(X0) | ~v1_relat_1(X0))),
% 3.78/1.00    inference(ennf_transformation,[],[f10])).
% 3.78/1.00  
% 3.78/1.00  fof(f42,plain,(
% 3.78/1.00    ( ! [X0] : (k2_xboole_0(k1_relat_1(X0),k2_relat_1(X0)) = k3_relat_1(X0) | ~v1_relat_1(X0)) )),
% 3.78/1.00    inference(cnf_transformation,[],[f19])).
% 3.78/1.00  
% 3.78/1.00  fof(f3,axiom,(
% 3.78/1.00    ! [X0,X1,X2] : (r1_tarski(X0,X1) => r1_tarski(X0,k2_xboole_0(X2,X1)))),
% 3.78/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.78/1.00  
% 3.78/1.00  fof(f14,plain,(
% 3.78/1.00    ! [X0,X1,X2] : (r1_tarski(X0,k2_xboole_0(X2,X1)) | ~r1_tarski(X0,X1))),
% 3.78/1.00    inference(ennf_transformation,[],[f3])).
% 3.78/1.00  
% 3.78/1.00  fof(f34,plain,(
% 3.78/1.00    ( ! [X2,X0,X1] : (r1_tarski(X0,k2_xboole_0(X2,X1)) | ~r1_tarski(X0,X1)) )),
% 3.78/1.00    inference(cnf_transformation,[],[f14])).
% 3.78/1.00  
% 3.78/1.00  fof(f45,plain,(
% 3.78/1.00    v1_relat_1(sK0)),
% 3.78/1.00    inference(cnf_transformation,[],[f29])).
% 3.78/1.00  
% 3.78/1.00  fof(f1,axiom,(
% 3.78/1.00    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0)),
% 3.78/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.78/1.00  
% 3.78/1.00  fof(f30,plain,(
% 3.78/1.00    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0)) )),
% 3.78/1.00    inference(cnf_transformation,[],[f1])).
% 3.78/1.00  
% 3.78/1.00  fof(f7,axiom,(
% 3.78/1.00    ! [X0,X1,X2] : (r1_tarski(X0,X1) => r1_tarski(k2_xboole_0(X0,X2),k2_xboole_0(X1,X2)))),
% 3.78/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.78/1.00  
% 3.78/1.00  fof(f17,plain,(
% 3.78/1.00    ! [X0,X1,X2] : (r1_tarski(k2_xboole_0(X0,X2),k2_xboole_0(X1,X2)) | ~r1_tarski(X0,X1))),
% 3.78/1.00    inference(ennf_transformation,[],[f7])).
% 3.78/1.00  
% 3.78/1.00  fof(f38,plain,(
% 3.78/1.00    ( ! [X2,X0,X1] : (r1_tarski(k2_xboole_0(X0,X2),k2_xboole_0(X1,X2)) | ~r1_tarski(X0,X1)) )),
% 3.78/1.00    inference(cnf_transformation,[],[f17])).
% 3.78/1.00  
% 3.78/1.00  fof(f43,plain,(
% 3.78/1.00    ( ! [X0,X1] : (r1_tarski(k1_relat_1(X0),k1_relat_1(X1)) | ~r1_tarski(X0,X1) | ~v1_relat_1(X1) | ~v1_relat_1(X0)) )),
% 3.78/1.00    inference(cnf_transformation,[],[f21])).
% 3.78/1.00  
% 3.78/1.00  fof(f48,plain,(
% 3.78/1.00    ~r1_tarski(k3_relat_1(sK0),k3_relat_1(sK1))),
% 3.78/1.00    inference(cnf_transformation,[],[f29])).
% 3.78/1.00  
% 3.78/1.00  cnf(c_16,negated_conjecture,
% 3.78/1.00      ( r1_tarski(sK0,sK1) ),
% 3.78/1.00      inference(cnf_transformation,[],[f47]) ).
% 3.78/1.00  
% 3.78/1.00  cnf(c_691,plain,
% 3.78/1.00      ( r1_tarski(sK0,sK1) = iProver_top ),
% 3.78/1.00      inference(predicate_to_equality,[status(thm)],[c_16]) ).
% 3.78/1.00  
% 3.78/1.00  cnf(c_13,plain,
% 3.78/1.00      ( ~ r1_tarski(X0,X1)
% 3.78/1.00      | r1_tarski(k2_relat_1(X0),k2_relat_1(X1))
% 3.78/1.00      | ~ v1_relat_1(X0)
% 3.78/1.00      | ~ v1_relat_1(X1) ),
% 3.78/1.00      inference(cnf_transformation,[],[f44]) ).
% 3.78/1.00  
% 3.78/1.00  cnf(c_11,plain,
% 3.78/1.00      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
% 3.78/1.00      | ~ v1_relat_1(X1)
% 3.78/1.00      | v1_relat_1(X0) ),
% 3.78/1.00      inference(cnf_transformation,[],[f41]) ).
% 3.78/1.00  
% 3.78/1.00  cnf(c_9,plain,
% 3.78/1.00      ( m1_subset_1(X0,k1_zfmisc_1(X1)) | ~ r1_tarski(X0,X1) ),
% 3.78/1.00      inference(cnf_transformation,[],[f40]) ).
% 3.78/1.00  
% 3.78/1.00  cnf(c_188,plain,
% 3.78/1.00      ( r1_tarski(k2_relat_1(X0),k2_relat_1(X1))
% 3.78/1.00      | ~ r1_tarski(X0,X1)
% 3.78/1.00      | ~ v1_relat_1(X1) ),
% 3.78/1.00      inference(global_propositional_subsumption,
% 3.78/1.00                [status(thm)],
% 3.78/1.00                [c_13,c_11,c_9]) ).
% 3.78/1.00  
% 3.78/1.00  cnf(c_189,plain,
% 3.78/1.00      ( ~ r1_tarski(X0,X1)
% 3.78/1.00      | r1_tarski(k2_relat_1(X0),k2_relat_1(X1))
% 3.78/1.00      | ~ v1_relat_1(X1) ),
% 3.78/1.00      inference(renaming,[status(thm)],[c_188]) ).
% 3.78/1.00  
% 3.78/1.00  cnf(c_686,plain,
% 3.78/1.00      ( r1_tarski(X0,X1) != iProver_top
% 3.78/1.00      | r1_tarski(k2_relat_1(X0),k2_relat_1(X1)) = iProver_top
% 3.78/1.00      | v1_relat_1(X1) != iProver_top ),
% 3.78/1.00      inference(predicate_to_equality,[status(thm)],[c_189]) ).
% 3.78/1.00  
% 3.78/1.00  cnf(c_6,plain,
% 3.78/1.00      ( ~ r1_tarski(X0,X1) | k2_xboole_0(X0,X1) = X1 ),
% 3.78/1.00      inference(cnf_transformation,[],[f36]) ).
% 3.78/1.00  
% 3.78/1.00  cnf(c_698,plain,
% 3.78/1.00      ( k2_xboole_0(X0,X1) = X1 | r1_tarski(X0,X1) != iProver_top ),
% 3.78/1.00      inference(predicate_to_equality,[status(thm)],[c_6]) ).
% 3.78/1.00  
% 3.78/1.00  cnf(c_1165,plain,
% 3.78/1.00      ( k2_xboole_0(k2_relat_1(X0),k2_relat_1(X1)) = k2_relat_1(X1)
% 3.78/1.00      | r1_tarski(X0,X1) != iProver_top
% 3.78/1.00      | v1_relat_1(X1) != iProver_top ),
% 3.78/1.00      inference(superposition,[status(thm)],[c_686,c_698]) ).
% 3.78/1.00  
% 3.78/1.00  cnf(c_7367,plain,
% 3.78/1.00      ( k2_xboole_0(k2_relat_1(sK0),k2_relat_1(sK1)) = k2_relat_1(sK1)
% 3.78/1.00      | v1_relat_1(sK1) != iProver_top ),
% 3.78/1.00      inference(superposition,[status(thm)],[c_691,c_1165]) ).
% 3.78/1.00  
% 3.78/1.00  cnf(c_17,negated_conjecture,
% 3.78/1.00      ( v1_relat_1(sK1) ),
% 3.78/1.00      inference(cnf_transformation,[],[f46]) ).
% 3.78/1.00  
% 3.78/1.00  cnf(c_20,plain,
% 3.78/1.00      ( v1_relat_1(sK1) = iProver_top ),
% 3.78/1.00      inference(predicate_to_equality,[status(thm)],[c_17]) ).
% 3.78/1.00  
% 3.78/1.00  cnf(c_8429,plain,
% 3.78/1.00      ( k2_xboole_0(k2_relat_1(sK0),k2_relat_1(sK1)) = k2_relat_1(sK1) ),
% 3.78/1.00      inference(global_propositional_subsumption,
% 3.78/1.00                [status(thm)],
% 3.78/1.00                [c_7367,c_20]) ).
% 3.78/1.00  
% 3.78/1.00  cnf(c_7,plain,
% 3.78/1.00      ( r1_tarski(X0,k2_xboole_0(X0,X1)) ),
% 3.78/1.00      inference(cnf_transformation,[],[f37]) ).
% 3.78/1.00  
% 3.78/1.00  cnf(c_697,plain,
% 3.78/1.00      ( r1_tarski(X0,k2_xboole_0(X0,X1)) = iProver_top ),
% 3.78/1.00      inference(predicate_to_equality,[status(thm)],[c_7]) ).
% 3.78/1.00  
% 3.78/1.00  cnf(c_8432,plain,
% 3.78/1.00      ( r1_tarski(k2_relat_1(sK0),k2_relat_1(sK1)) = iProver_top ),
% 3.78/1.00      inference(superposition,[status(thm)],[c_8429,c_697]) ).
% 3.78/1.00  
% 3.78/1.00  cnf(c_690,plain,
% 3.78/1.00      ( v1_relat_1(sK1) = iProver_top ),
% 3.78/1.00      inference(predicate_to_equality,[status(thm)],[c_17]) ).
% 3.78/1.00  
% 3.78/1.00  cnf(c_12,plain,
% 3.78/1.00      ( ~ v1_relat_1(X0)
% 3.78/1.00      | k2_xboole_0(k1_relat_1(X0),k2_relat_1(X0)) = k3_relat_1(X0) ),
% 3.78/1.00      inference(cnf_transformation,[],[f42]) ).
% 3.78/1.00  
% 3.78/1.00  cnf(c_693,plain,
% 3.78/1.00      ( k2_xboole_0(k1_relat_1(X0),k2_relat_1(X0)) = k3_relat_1(X0)
% 3.78/1.00      | v1_relat_1(X0) != iProver_top ),
% 3.78/1.00      inference(predicate_to_equality,[status(thm)],[c_12]) ).
% 3.78/1.00  
% 3.78/1.00  cnf(c_1407,plain,
% 3.78/1.00      ( k2_xboole_0(k1_relat_1(sK1),k2_relat_1(sK1)) = k3_relat_1(sK1) ),
% 3.78/1.00      inference(superposition,[status(thm)],[c_690,c_693]) ).
% 3.78/1.00  
% 3.78/1.00  cnf(c_4,plain,
% 3.78/1.00      ( ~ r1_tarski(X0,X1) | r1_tarski(X0,k2_xboole_0(X2,X1)) ),
% 3.78/1.00      inference(cnf_transformation,[],[f34]) ).
% 3.78/1.00  
% 3.78/1.00  cnf(c_700,plain,
% 3.78/1.00      ( r1_tarski(X0,X1) != iProver_top
% 3.78/1.00      | r1_tarski(X0,k2_xboole_0(X2,X1)) = iProver_top ),
% 3.78/1.00      inference(predicate_to_equality,[status(thm)],[c_4]) ).
% 3.78/1.00  
% 3.78/1.00  cnf(c_2133,plain,
% 3.78/1.00      ( r1_tarski(X0,k3_relat_1(sK1)) = iProver_top
% 3.78/1.00      | r1_tarski(X0,k2_relat_1(sK1)) != iProver_top ),
% 3.78/1.00      inference(superposition,[status(thm)],[c_1407,c_700]) ).
% 3.78/1.00  
% 3.78/1.00  cnf(c_8768,plain,
% 3.78/1.00      ( r1_tarski(k2_relat_1(sK0),k3_relat_1(sK1)) = iProver_top ),
% 3.78/1.00      inference(superposition,[status(thm)],[c_8432,c_2133]) ).
% 3.78/1.00  
% 3.78/1.00  cnf(c_17585,plain,
% 3.78/1.00      ( k2_xboole_0(k2_relat_1(sK0),k3_relat_1(sK1)) = k3_relat_1(sK1) ),
% 3.78/1.00      inference(superposition,[status(thm)],[c_8768,c_698]) ).
% 3.78/1.00  
% 3.78/1.00  cnf(c_18,negated_conjecture,
% 3.78/1.00      ( v1_relat_1(sK0) ),
% 3.78/1.00      inference(cnf_transformation,[],[f45]) ).
% 3.78/1.00  
% 3.78/1.00  cnf(c_689,plain,
% 3.78/1.00      ( v1_relat_1(sK0) = iProver_top ),
% 3.78/1.00      inference(predicate_to_equality,[status(thm)],[c_18]) ).
% 3.78/1.00  
% 3.78/1.00  cnf(c_1408,plain,
% 3.78/1.00      ( k2_xboole_0(k1_relat_1(sK0),k2_relat_1(sK0)) = k3_relat_1(sK0) ),
% 3.78/1.00      inference(superposition,[status(thm)],[c_689,c_693]) ).
% 3.78/1.00  
% 3.78/1.00  cnf(c_0,plain,
% 3.78/1.00      ( k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0) ),
% 3.78/1.00      inference(cnf_transformation,[],[f30]) ).
% 3.78/1.00  
% 3.78/1.00  cnf(c_8,plain,
% 3.78/1.00      ( ~ r1_tarski(X0,X1)
% 3.78/1.00      | r1_tarski(k2_xboole_0(X0,X2),k2_xboole_0(X1,X2)) ),
% 3.78/1.00      inference(cnf_transformation,[],[f38]) ).
% 3.78/1.00  
% 3.78/1.00  cnf(c_696,plain,
% 3.78/1.00      ( r1_tarski(X0,X1) != iProver_top
% 3.78/1.00      | r1_tarski(k2_xboole_0(X0,X2),k2_xboole_0(X1,X2)) = iProver_top ),
% 3.78/1.00      inference(predicate_to_equality,[status(thm)],[c_8]) ).
% 3.78/1.00  
% 3.78/1.00  cnf(c_3655,plain,
% 3.78/1.00      ( r1_tarski(X0,X1) != iProver_top
% 3.78/1.00      | r1_tarski(k2_xboole_0(X0,X2),k2_xboole_0(X2,X1)) = iProver_top ),
% 3.78/1.00      inference(superposition,[status(thm)],[c_0,c_696]) ).
% 3.78/1.00  
% 3.78/1.00  cnf(c_3967,plain,
% 3.78/1.00      ( r1_tarski(k3_relat_1(sK0),k2_xboole_0(k2_relat_1(sK0),X0)) = iProver_top
% 3.78/1.00      | r1_tarski(k1_relat_1(sK0),X0) != iProver_top ),
% 3.78/1.00      inference(superposition,[status(thm)],[c_1408,c_3655]) ).
% 3.78/1.00  
% 3.78/1.00  cnf(c_18237,plain,
% 3.78/1.00      ( r1_tarski(k3_relat_1(sK0),k3_relat_1(sK1)) = iProver_top
% 3.78/1.00      | r1_tarski(k1_relat_1(sK0),k3_relat_1(sK1)) != iProver_top ),
% 3.78/1.00      inference(superposition,[status(thm)],[c_17585,c_3967]) ).
% 3.78/1.00  
% 3.78/1.00  cnf(c_14,plain,
% 3.78/1.00      ( ~ r1_tarski(X0,X1)
% 3.78/1.00      | r1_tarski(k1_relat_1(X0),k1_relat_1(X1))
% 3.78/1.00      | ~ v1_relat_1(X0)
% 3.78/1.00      | ~ v1_relat_1(X1) ),
% 3.78/1.00      inference(cnf_transformation,[],[f43]) ).
% 3.78/1.00  
% 3.78/1.00  cnf(c_181,plain,
% 3.78/1.00      ( r1_tarski(k1_relat_1(X0),k1_relat_1(X1))
% 3.78/1.00      | ~ r1_tarski(X0,X1)
% 3.78/1.00      | ~ v1_relat_1(X1) ),
% 3.78/1.00      inference(global_propositional_subsumption,
% 3.78/1.00                [status(thm)],
% 3.78/1.00                [c_14,c_11,c_9]) ).
% 3.78/1.00  
% 3.78/1.00  cnf(c_182,plain,
% 3.78/1.00      ( ~ r1_tarski(X0,X1)
% 3.78/1.00      | r1_tarski(k1_relat_1(X0),k1_relat_1(X1))
% 3.78/1.00      | ~ v1_relat_1(X1) ),
% 3.78/1.00      inference(renaming,[status(thm)],[c_181]) ).
% 3.78/1.00  
% 3.78/1.00  cnf(c_687,plain,
% 3.78/1.00      ( r1_tarski(X0,X1) != iProver_top
% 3.78/1.00      | r1_tarski(k1_relat_1(X0),k1_relat_1(X1)) = iProver_top
% 3.78/1.00      | v1_relat_1(X1) != iProver_top ),
% 3.78/1.00      inference(predicate_to_equality,[status(thm)],[c_182]) ).
% 3.78/1.00  
% 3.78/1.00  cnf(c_2129,plain,
% 3.78/1.00      ( r1_tarski(X0,X1) != iProver_top
% 3.78/1.00      | r1_tarski(X0,k2_xboole_0(X1,X2)) = iProver_top ),
% 3.78/1.00      inference(superposition,[status(thm)],[c_0,c_700]) ).
% 3.78/1.00  
% 3.78/1.00  cnf(c_2392,plain,
% 3.78/1.00      ( r1_tarski(X0,k3_relat_1(sK1)) = iProver_top
% 3.78/1.00      | r1_tarski(X0,k1_relat_1(sK1)) != iProver_top ),
% 3.78/1.00      inference(superposition,[status(thm)],[c_1407,c_2129]) ).
% 3.78/1.00  
% 3.78/1.00  cnf(c_4524,plain,
% 3.78/1.00      ( r1_tarski(X0,sK1) != iProver_top
% 3.78/1.00      | r1_tarski(k1_relat_1(X0),k3_relat_1(sK1)) = iProver_top
% 3.78/1.00      | v1_relat_1(sK1) != iProver_top ),
% 3.78/1.00      inference(superposition,[status(thm)],[c_687,c_2392]) ).
% 3.78/1.00  
% 3.78/1.00  cnf(c_4532,plain,
% 3.78/1.00      ( r1_tarski(k1_relat_1(sK0),k3_relat_1(sK1)) = iProver_top
% 3.78/1.00      | r1_tarski(sK0,sK1) != iProver_top
% 3.78/1.00      | v1_relat_1(sK1) != iProver_top ),
% 3.78/1.00      inference(instantiation,[status(thm)],[c_4524]) ).
% 3.78/1.00  
% 3.78/1.00  cnf(c_15,negated_conjecture,
% 3.78/1.00      ( ~ r1_tarski(k3_relat_1(sK0),k3_relat_1(sK1)) ),
% 3.78/1.00      inference(cnf_transformation,[],[f48]) ).
% 3.78/1.00  
% 3.78/1.00  cnf(c_22,plain,
% 3.78/1.00      ( r1_tarski(k3_relat_1(sK0),k3_relat_1(sK1)) != iProver_top ),
% 3.78/1.00      inference(predicate_to_equality,[status(thm)],[c_15]) ).
% 3.78/1.00  
% 3.78/1.00  cnf(c_21,plain,
% 3.78/1.00      ( r1_tarski(sK0,sK1) = iProver_top ),
% 3.78/1.00      inference(predicate_to_equality,[status(thm)],[c_16]) ).
% 3.78/1.00  
% 3.78/1.00  cnf(contradiction,plain,
% 3.78/1.00      ( $false ),
% 3.78/1.00      inference(minisat,[status(thm)],[c_18237,c_4532,c_22,c_21,c_20]) ).
% 3.78/1.00  
% 3.78/1.00  
% 3.78/1.00  % SZS output end CNFRefutation for theBenchmark.p
% 3.78/1.00  
% 3.78/1.00  ------                               Statistics
% 3.78/1.00  
% 3.78/1.00  ------ Selected
% 3.78/1.00  
% 3.78/1.00  total_time:                             0.469
% 3.78/1.00  
%------------------------------------------------------------------------------
