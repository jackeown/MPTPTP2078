%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n018.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 11:43:12 EST 2020

% Result     : Theorem 7.95s
% Output     : CNFRefutation 7.95s
% Verified   : 
% Statistics : Number of formulae       :   98 ( 172 expanded)
%              Number of clauses        :   55 (  68 expanded)
%              Number of leaves         :   16 (  39 expanded)
%              Depth                    :   13
%              Number of atoms          :  265 ( 533 expanded)
%              Number of equality atoms :   74 (  95 expanded)
%              Maximal formula depth    :    7 (   4 average)
%              Maximal clause size      :    8 (   2 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f9,axiom,(
    ! [X0,X1,X2] :
      ( ( r1_tarski(X2,X1)
        & r1_tarski(X0,X1) )
     => r1_tarski(k2_xboole_0(X0,X2),X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f22,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(k2_xboole_0(X0,X2),X1)
      | ~ r1_tarski(X2,X1)
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f23,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(k2_xboole_0(X0,X2),X1)
      | ~ r1_tarski(X2,X1)
      | ~ r1_tarski(X0,X1) ) ),
    inference(flattening,[],[f22])).

fof(f47,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(k2_xboole_0(X0,X2),X1)
      | ~ r1_tarski(X2,X1)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f15,conjecture,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( v1_relat_1(X1)
         => ( r1_tarski(X0,X1)
           => r1_tarski(k3_relat_1(X0),k3_relat_1(X1)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f16,negated_conjecture,(
    ~ ! [X0] :
        ( v1_relat_1(X0)
       => ! [X1] :
            ( v1_relat_1(X1)
           => ( r1_tarski(X0,X1)
             => r1_tarski(k3_relat_1(X0),k3_relat_1(X1)) ) ) ) ),
    inference(negated_conjecture,[],[f15])).

fof(f29,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ~ r1_tarski(k3_relat_1(X0),k3_relat_1(X1))
          & r1_tarski(X0,X1)
          & v1_relat_1(X1) )
      & v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f16])).

fof(f30,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ~ r1_tarski(k3_relat_1(X0),k3_relat_1(X1))
          & r1_tarski(X0,X1)
          & v1_relat_1(X1) )
      & v1_relat_1(X0) ) ),
    inference(flattening,[],[f29])).

fof(f35,plain,(
    ! [X0] :
      ( ? [X1] :
          ( ~ r1_tarski(k3_relat_1(X0),k3_relat_1(X1))
          & r1_tarski(X0,X1)
          & v1_relat_1(X1) )
     => ( ~ r1_tarski(k3_relat_1(X0),k3_relat_1(sK1))
        & r1_tarski(X0,sK1)
        & v1_relat_1(sK1) ) ) ),
    introduced(choice_axiom,[])).

fof(f34,plain,
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

fof(f36,plain,
    ( ~ r1_tarski(k3_relat_1(sK0),k3_relat_1(sK1))
    & r1_tarski(sK0,sK1)
    & v1_relat_1(sK1)
    & v1_relat_1(sK0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f30,f35,f34])).

fof(f56,plain,(
    v1_relat_1(sK1) ),
    inference(cnf_transformation,[],[f36])).

fof(f12,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => k2_xboole_0(k1_relat_1(X0),k2_relat_1(X0)) = k3_relat_1(X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f25,plain,(
    ! [X0] :
      ( k2_xboole_0(k1_relat_1(X0),k2_relat_1(X0)) = k3_relat_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f51,plain,(
    ! [X0] :
      ( k2_xboole_0(k1_relat_1(X0),k2_relat_1(X0)) = k3_relat_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f8,axiom,(
    ! [X0,X1] : r1_tarski(X0,k2_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f46,plain,(
    ! [X0,X1] : r1_tarski(X0,k2_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f8])).

fof(f13,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( v1_relat_1(X1)
         => ( r1_tarski(X0,X1)
           => ( r1_tarski(k2_relat_1(X0),k2_relat_1(X1))
              & r1_tarski(k1_relat_1(X0),k1_relat_1(X1)) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f26,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( r1_tarski(k2_relat_1(X0),k2_relat_1(X1))
            & r1_tarski(k1_relat_1(X0),k1_relat_1(X1)) )
          | ~ r1_tarski(X0,X1)
          | ~ v1_relat_1(X1) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f27,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( r1_tarski(k2_relat_1(X0),k2_relat_1(X1))
            & r1_tarski(k1_relat_1(X0),k1_relat_1(X1)) )
          | ~ r1_tarski(X0,X1)
          | ~ v1_relat_1(X1) )
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f26])).

fof(f52,plain,(
    ! [X0,X1] :
      ( r1_tarski(k1_relat_1(X0),k1_relat_1(X1))
      | ~ r1_tarski(X0,X1)
      | ~ v1_relat_1(X1)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f11,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(X0))
         => v1_relat_1(X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f24,plain,(
    ! [X0] :
      ( ! [X1] :
          ( v1_relat_1(X1)
          | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f50,plain,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f10,axiom,(
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
    inference(nnf_transformation,[],[f10])).

fof(f49,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f33])).

fof(f4,axiom,(
    ! [X0,X1,X2] :
      ( ( r1_tarski(X1,X2)
        & r1_tarski(X0,X1) )
     => r1_tarski(X0,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f18,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,X2)
      | ~ r1_tarski(X1,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f19,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,X2)
      | ~ r1_tarski(X1,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(flattening,[],[f18])).

fof(f42,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(X0,X2)
      | ~ r1_tarski(X1,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f1,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f37,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f1])).

fof(f53,plain,(
    ! [X0,X1] :
      ( r1_tarski(k2_relat_1(X0),k2_relat_1(X1))
      | ~ r1_tarski(X0,X1)
      | ~ v1_relat_1(X1)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( X0 = X1
    <=> ( r1_tarski(X1,X0)
        & r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f31,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(nnf_transformation,[],[f2])).

fof(f32,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(flattening,[],[f31])).

fof(f40,plain,(
    ! [X0,X1] :
      ( X0 = X1
      | ~ r1_tarski(X1,X0)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f32])).

fof(f38,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | X0 != X1 ) ),
    inference(cnf_transformation,[],[f32])).

fof(f60,plain,(
    ! [X1] : r1_tarski(X1,X1) ),
    inference(equality_resolution,[],[f38])).

fof(f58,plain,(
    ~ r1_tarski(k3_relat_1(sK0),k3_relat_1(sK1)) ),
    inference(cnf_transformation,[],[f36])).

fof(f57,plain,(
    r1_tarski(sK0,sK1) ),
    inference(cnf_transformation,[],[f36])).

fof(f55,plain,(
    v1_relat_1(sK0) ),
    inference(cnf_transformation,[],[f36])).

cnf(c_10,plain,
    ( ~ r1_tarski(X0,X1)
    | ~ r1_tarski(X2,X1)
    | r1_tarski(k2_xboole_0(X0,X2),X1) ),
    inference(cnf_transformation,[],[f47])).

cnf(c_1064,plain,
    ( ~ r1_tarski(X0,k3_relat_1(sK1))
    | ~ r1_tarski(X1,k3_relat_1(sK1))
    | r1_tarski(k2_xboole_0(X0,X1),k3_relat_1(sK1)) ),
    inference(instantiation,[status(thm)],[c_10])).

cnf(c_30596,plain,
    ( r1_tarski(k2_xboole_0(k1_relat_1(sK0),k2_relat_1(sK0)),k3_relat_1(sK1))
    | ~ r1_tarski(k2_relat_1(sK0),k3_relat_1(sK1))
    | ~ r1_tarski(k1_relat_1(sK0),k3_relat_1(sK1)) ),
    inference(instantiation,[status(thm)],[c_1064])).

cnf(c_20,negated_conjecture,
    ( v1_relat_1(sK1) ),
    inference(cnf_transformation,[],[f56])).

cnf(c_850,plain,
    ( v1_relat_1(sK1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_20])).

cnf(c_14,plain,
    ( ~ v1_relat_1(X0)
    | k2_xboole_0(k1_relat_1(X0),k2_relat_1(X0)) = k3_relat_1(X0) ),
    inference(cnf_transformation,[],[f51])).

cnf(c_854,plain,
    ( k2_xboole_0(k1_relat_1(X0),k2_relat_1(X0)) = k3_relat_1(X0)
    | v1_relat_1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_14])).

cnf(c_1730,plain,
    ( k2_xboole_0(k1_relat_1(sK1),k2_relat_1(sK1)) = k3_relat_1(sK1) ),
    inference(superposition,[status(thm)],[c_850,c_854])).

cnf(c_9,plain,
    ( r1_tarski(X0,k2_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f46])).

cnf(c_856,plain,
    ( r1_tarski(X0,k2_xboole_0(X0,X1)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_9])).

cnf(c_4382,plain,
    ( r1_tarski(k1_relat_1(sK1),k3_relat_1(sK1)) = iProver_top ),
    inference(superposition,[status(thm)],[c_1730,c_856])).

cnf(c_16,plain,
    ( ~ r1_tarski(X0,X1)
    | r1_tarski(k1_relat_1(X0),k1_relat_1(X1))
    | ~ v1_relat_1(X0)
    | ~ v1_relat_1(X1) ),
    inference(cnf_transformation,[],[f52])).

cnf(c_13,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | ~ v1_relat_1(X1)
    | v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f50])).

cnf(c_11,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(X1))
    | ~ r1_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f49])).

cnf(c_118,plain,
    ( r1_tarski(k1_relat_1(X0),k1_relat_1(X1))
    | ~ r1_tarski(X0,X1)
    | ~ v1_relat_1(X1) ),
    inference(global_propositional_subsumption,[status(thm)],[c_16,c_13,c_11])).

cnf(c_119,plain,
    ( ~ r1_tarski(X0,X1)
    | r1_tarski(k1_relat_1(X0),k1_relat_1(X1))
    | ~ v1_relat_1(X1) ),
    inference(renaming,[status(thm)],[c_118])).

cnf(c_848,plain,
    ( r1_tarski(X0,X1) != iProver_top
    | r1_tarski(k1_relat_1(X0),k1_relat_1(X1)) = iProver_top
    | v1_relat_1(X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_119])).

cnf(c_5,plain,
    ( ~ r1_tarski(X0,X1)
    | ~ r1_tarski(X1,X2)
    | r1_tarski(X0,X2) ),
    inference(cnf_transformation,[],[f42])).

cnf(c_860,plain,
    ( r1_tarski(X0,X1) != iProver_top
    | r1_tarski(X1,X2) != iProver_top
    | r1_tarski(X0,X2) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_5])).

cnf(c_2365,plain,
    ( r1_tarski(X0,X1) != iProver_top
    | r1_tarski(k1_relat_1(X1),X2) != iProver_top
    | r1_tarski(k1_relat_1(X0),X2) = iProver_top
    | v1_relat_1(X1) != iProver_top ),
    inference(superposition,[status(thm)],[c_848,c_860])).

cnf(c_27498,plain,
    ( r1_tarski(X0,sK1) != iProver_top
    | r1_tarski(k1_relat_1(X0),k3_relat_1(sK1)) = iProver_top
    | v1_relat_1(sK1) != iProver_top ),
    inference(superposition,[status(thm)],[c_4382,c_2365])).

cnf(c_27516,plain,
    ( ~ r1_tarski(X0,sK1)
    | r1_tarski(k1_relat_1(X0),k3_relat_1(sK1))
    | ~ v1_relat_1(sK1) ),
    inference(predicate_to_equality_rev,[status(thm)],[c_27498])).

cnf(c_27518,plain,
    ( r1_tarski(k1_relat_1(sK0),k3_relat_1(sK1))
    | ~ r1_tarski(sK0,sK1)
    | ~ v1_relat_1(sK1) ),
    inference(instantiation,[status(thm)],[c_27516])).

cnf(c_0,plain,
    ( k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f37])).

cnf(c_1167,plain,
    ( r1_tarski(X0,k2_xboole_0(X1,X0)) = iProver_top ),
    inference(superposition,[status(thm)],[c_0,c_856])).

cnf(c_4383,plain,
    ( r1_tarski(k2_relat_1(sK1),k3_relat_1(sK1)) = iProver_top ),
    inference(superposition,[status(thm)],[c_1730,c_1167])).

cnf(c_15,plain,
    ( ~ r1_tarski(X0,X1)
    | r1_tarski(k2_relat_1(X0),k2_relat_1(X1))
    | ~ v1_relat_1(X0)
    | ~ v1_relat_1(X1) ),
    inference(cnf_transformation,[],[f53])).

cnf(c_123,plain,
    ( r1_tarski(k2_relat_1(X0),k2_relat_1(X1))
    | ~ r1_tarski(X0,X1)
    | ~ v1_relat_1(X1) ),
    inference(global_propositional_subsumption,[status(thm)],[c_15,c_13,c_11])).

cnf(c_124,plain,
    ( ~ r1_tarski(X0,X1)
    | r1_tarski(k2_relat_1(X0),k2_relat_1(X1))
    | ~ v1_relat_1(X1) ),
    inference(renaming,[status(thm)],[c_123])).

cnf(c_847,plain,
    ( r1_tarski(X0,X1) != iProver_top
    | r1_tarski(k2_relat_1(X0),k2_relat_1(X1)) = iProver_top
    | v1_relat_1(X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_124])).

cnf(c_2364,plain,
    ( r1_tarski(X0,X1) != iProver_top
    | r1_tarski(k2_relat_1(X1),X2) != iProver_top
    | r1_tarski(k2_relat_1(X0),X2) = iProver_top
    | v1_relat_1(X1) != iProver_top ),
    inference(superposition,[status(thm)],[c_847,c_860])).

cnf(c_25851,plain,
    ( r1_tarski(X0,sK1) != iProver_top
    | r1_tarski(k2_relat_1(X0),k3_relat_1(sK1)) = iProver_top
    | v1_relat_1(sK1) != iProver_top ),
    inference(superposition,[status(thm)],[c_4383,c_2364])).

cnf(c_25869,plain,
    ( ~ r1_tarski(X0,sK1)
    | r1_tarski(k2_relat_1(X0),k3_relat_1(sK1))
    | ~ v1_relat_1(sK1) ),
    inference(predicate_to_equality_rev,[status(thm)],[c_25851])).

cnf(c_25871,plain,
    ( r1_tarski(k2_relat_1(sK0),k3_relat_1(sK1))
    | ~ r1_tarski(sK0,sK1)
    | ~ v1_relat_1(sK1) ),
    inference(instantiation,[status(thm)],[c_25869])).

cnf(c_437,plain,
    ( ~ r1_tarski(X0,X1)
    | r1_tarski(X2,X3)
    | X2 != X0
    | X3 != X1 ),
    theory(equality)).

cnf(c_957,plain,
    ( ~ r1_tarski(X0,X1)
    | r1_tarski(k3_relat_1(sK0),k3_relat_1(sK1))
    | k3_relat_1(sK1) != X1
    | k3_relat_1(sK0) != X0 ),
    inference(instantiation,[status(thm)],[c_437])).

cnf(c_1793,plain,
    ( ~ r1_tarski(k2_xboole_0(k1_relat_1(sK0),k2_relat_1(sK0)),X0)
    | r1_tarski(k3_relat_1(sK0),k3_relat_1(sK1))
    | k3_relat_1(sK1) != X0
    | k3_relat_1(sK0) != k2_xboole_0(k1_relat_1(sK0),k2_relat_1(sK0)) ),
    inference(instantiation,[status(thm)],[c_957])).

cnf(c_2597,plain,
    ( ~ r1_tarski(k2_xboole_0(k1_relat_1(sK0),k2_relat_1(sK0)),k3_relat_1(sK1))
    | r1_tarski(k3_relat_1(sK0),k3_relat_1(sK1))
    | k3_relat_1(sK1) != k3_relat_1(sK1)
    | k3_relat_1(sK0) != k2_xboole_0(k1_relat_1(sK0),k2_relat_1(sK0)) ),
    inference(instantiation,[status(thm)],[c_1793])).

cnf(c_435,plain,
    ( X0 != X1
    | X2 != X1
    | X2 = X0 ),
    theory(equality)).

cnf(c_993,plain,
    ( X0 != X1
    | k3_relat_1(sK0) != X1
    | k3_relat_1(sK0) = X0 ),
    inference(instantiation,[status(thm)],[c_435])).

cnf(c_1140,plain,
    ( X0 != k3_relat_1(sK0)
    | k3_relat_1(sK0) = X0
    | k3_relat_1(sK0) != k3_relat_1(sK0) ),
    inference(instantiation,[status(thm)],[c_993])).

cnf(c_1534,plain,
    ( k2_xboole_0(k1_relat_1(sK0),k2_relat_1(sK0)) != k3_relat_1(sK0)
    | k3_relat_1(sK0) = k2_xboole_0(k1_relat_1(sK0),k2_relat_1(sK0))
    | k3_relat_1(sK0) != k3_relat_1(sK0) ),
    inference(instantiation,[status(thm)],[c_1140])).

cnf(c_434,plain,
    ( X0 = X0 ),
    theory(equality)).

cnf(c_1145,plain,
    ( k3_relat_1(sK1) = k3_relat_1(sK1) ),
    inference(instantiation,[status(thm)],[c_434])).

cnf(c_440,plain,
    ( X0 != X1
    | k3_relat_1(X0) = k3_relat_1(X1) ),
    theory(equality)).

cnf(c_444,plain,
    ( k3_relat_1(sK0) = k3_relat_1(sK0)
    | sK0 != sK0 ),
    inference(instantiation,[status(thm)],[c_440])).

cnf(c_1,plain,
    ( ~ r1_tarski(X0,X1)
    | ~ r1_tarski(X1,X0)
    | X0 = X1 ),
    inference(cnf_transformation,[],[f40])).

cnf(c_67,plain,
    ( ~ r1_tarski(sK0,sK0)
    | sK0 = sK0 ),
    inference(instantiation,[status(thm)],[c_1])).

cnf(c_3,plain,
    ( r1_tarski(X0,X0) ),
    inference(cnf_transformation,[],[f60])).

cnf(c_63,plain,
    ( r1_tarski(sK0,sK0) ),
    inference(instantiation,[status(thm)],[c_3])).

cnf(c_36,plain,
    ( ~ v1_relat_1(sK0)
    | k2_xboole_0(k1_relat_1(sK0),k2_relat_1(sK0)) = k3_relat_1(sK0) ),
    inference(instantiation,[status(thm)],[c_14])).

cnf(c_18,negated_conjecture,
    ( ~ r1_tarski(k3_relat_1(sK0),k3_relat_1(sK1)) ),
    inference(cnf_transformation,[],[f58])).

cnf(c_19,negated_conjecture,
    ( r1_tarski(sK0,sK1) ),
    inference(cnf_transformation,[],[f57])).

cnf(c_21,negated_conjecture,
    ( v1_relat_1(sK0) ),
    inference(cnf_transformation,[],[f55])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_30596,c_27518,c_25871,c_2597,c_1534,c_1145,c_444,c_67,c_63,c_36,c_18,c_19,c_20,c_21])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.12  % Command    : iproveropt_run.sh %d %s
% 0.12/0.34  % Computer   : n018.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % WCLimit    : 600
% 0.12/0.34  % DateTime   : Tue Dec  1 18:30:12 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.34  % Running in FOF mode
% 7.95/1.49  % SZS status Started for /export/starexec/sandbox/benchmark/theBenchmark.p
% 7.95/1.49  
% 7.95/1.49  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 7.95/1.49  
% 7.95/1.49  ------  iProver source info
% 7.95/1.49  
% 7.95/1.49  git: date: 2020-06-30 10:37:57 +0100
% 7.95/1.49  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 7.95/1.49  git: non_committed_changes: false
% 7.95/1.49  git: last_make_outside_of_git: false
% 7.95/1.49  
% 7.95/1.49  ------ 
% 7.95/1.49  ------ Parsing...
% 7.95/1.49  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 7.95/1.49  
% 7.95/1.49  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe:1:0s pe_e  sf_s  rm: 2 0s  sf_e  pe_s  pe_e 
% 7.95/1.49  
% 7.95/1.49  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 7.95/1.49  
% 7.95/1.49  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 7.95/1.49  ------ Proving...
% 7.95/1.49  ------ Problem Properties 
% 7.95/1.49  
% 7.95/1.49  
% 7.95/1.49  clauses                                 19
% 7.95/1.49  conjectures                             4
% 7.95/1.49  EPR                                     7
% 7.95/1.49  Horn                                    19
% 7.95/1.49  unary                                   8
% 7.95/1.49  binary                                  4
% 7.95/1.49  lits                                    37
% 7.95/1.49  lits eq                                 5
% 7.95/1.49  fd_pure                                 0
% 7.95/1.49  fd_pseudo                               0
% 7.95/1.49  fd_cond                                 0
% 7.95/1.49  fd_pseudo_cond                          1
% 7.95/1.49  AC symbols                              0
% 7.95/1.49  
% 7.95/1.49  ------ Input Options Time Limit: Unbounded
% 7.95/1.49  
% 7.95/1.49  
% 7.95/1.49  ------ 
% 7.95/1.49  Current options:
% 7.95/1.49  ------ 
% 7.95/1.49  
% 7.95/1.49  
% 7.95/1.49  
% 7.95/1.49  
% 7.95/1.49  ------ Proving...
% 7.95/1.49  
% 7.95/1.49  
% 7.95/1.49  % SZS status Theorem for theBenchmark.p
% 7.95/1.49  
% 7.95/1.49  % SZS output start CNFRefutation for theBenchmark.p
% 7.95/1.49  
% 7.95/1.49  fof(f9,axiom,(
% 7.95/1.49    ! [X0,X1,X2] : ((r1_tarski(X2,X1) & r1_tarski(X0,X1)) => r1_tarski(k2_xboole_0(X0,X2),X1))),
% 7.95/1.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.95/1.49  
% 7.95/1.49  fof(f22,plain,(
% 7.95/1.49    ! [X0,X1,X2] : (r1_tarski(k2_xboole_0(X0,X2),X1) | (~r1_tarski(X2,X1) | ~r1_tarski(X0,X1)))),
% 7.95/1.49    inference(ennf_transformation,[],[f9])).
% 7.95/1.49  
% 7.95/1.49  fof(f23,plain,(
% 7.95/1.49    ! [X0,X1,X2] : (r1_tarski(k2_xboole_0(X0,X2),X1) | ~r1_tarski(X2,X1) | ~r1_tarski(X0,X1))),
% 7.95/1.49    inference(flattening,[],[f22])).
% 7.95/1.49  
% 7.95/1.49  fof(f47,plain,(
% 7.95/1.49    ( ! [X2,X0,X1] : (r1_tarski(k2_xboole_0(X0,X2),X1) | ~r1_tarski(X2,X1) | ~r1_tarski(X0,X1)) )),
% 7.95/1.49    inference(cnf_transformation,[],[f23])).
% 7.95/1.49  
% 7.95/1.49  fof(f15,conjecture,(
% 7.95/1.49    ! [X0] : (v1_relat_1(X0) => ! [X1] : (v1_relat_1(X1) => (r1_tarski(X0,X1) => r1_tarski(k3_relat_1(X0),k3_relat_1(X1)))))),
% 7.95/1.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.95/1.49  
% 7.95/1.49  fof(f16,negated_conjecture,(
% 7.95/1.49    ~! [X0] : (v1_relat_1(X0) => ! [X1] : (v1_relat_1(X1) => (r1_tarski(X0,X1) => r1_tarski(k3_relat_1(X0),k3_relat_1(X1)))))),
% 7.95/1.49    inference(negated_conjecture,[],[f15])).
% 7.95/1.49  
% 7.95/1.49  fof(f29,plain,(
% 7.95/1.49    ? [X0] : (? [X1] : ((~r1_tarski(k3_relat_1(X0),k3_relat_1(X1)) & r1_tarski(X0,X1)) & v1_relat_1(X1)) & v1_relat_1(X0))),
% 7.95/1.49    inference(ennf_transformation,[],[f16])).
% 7.95/1.49  
% 7.95/1.49  fof(f30,plain,(
% 7.95/1.49    ? [X0] : (? [X1] : (~r1_tarski(k3_relat_1(X0),k3_relat_1(X1)) & r1_tarski(X0,X1) & v1_relat_1(X1)) & v1_relat_1(X0))),
% 7.95/1.49    inference(flattening,[],[f29])).
% 7.95/1.49  
% 7.95/1.49  fof(f35,plain,(
% 7.95/1.49    ( ! [X0] : (? [X1] : (~r1_tarski(k3_relat_1(X0),k3_relat_1(X1)) & r1_tarski(X0,X1) & v1_relat_1(X1)) => (~r1_tarski(k3_relat_1(X0),k3_relat_1(sK1)) & r1_tarski(X0,sK1) & v1_relat_1(sK1))) )),
% 7.95/1.49    introduced(choice_axiom,[])).
% 7.95/1.49  
% 7.95/1.49  fof(f34,plain,(
% 7.95/1.49    ? [X0] : (? [X1] : (~r1_tarski(k3_relat_1(X0),k3_relat_1(X1)) & r1_tarski(X0,X1) & v1_relat_1(X1)) & v1_relat_1(X0)) => (? [X1] : (~r1_tarski(k3_relat_1(sK0),k3_relat_1(X1)) & r1_tarski(sK0,X1) & v1_relat_1(X1)) & v1_relat_1(sK0))),
% 7.95/1.49    introduced(choice_axiom,[])).
% 7.95/1.49  
% 7.95/1.49  fof(f36,plain,(
% 7.95/1.49    (~r1_tarski(k3_relat_1(sK0),k3_relat_1(sK1)) & r1_tarski(sK0,sK1) & v1_relat_1(sK1)) & v1_relat_1(sK0)),
% 7.95/1.49    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f30,f35,f34])).
% 7.95/1.49  
% 7.95/1.49  fof(f56,plain,(
% 7.95/1.49    v1_relat_1(sK1)),
% 7.95/1.49    inference(cnf_transformation,[],[f36])).
% 7.95/1.49  
% 7.95/1.49  fof(f12,axiom,(
% 7.95/1.49    ! [X0] : (v1_relat_1(X0) => k2_xboole_0(k1_relat_1(X0),k2_relat_1(X0)) = k3_relat_1(X0))),
% 7.95/1.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.95/1.49  
% 7.95/1.49  fof(f25,plain,(
% 7.95/1.49    ! [X0] : (k2_xboole_0(k1_relat_1(X0),k2_relat_1(X0)) = k3_relat_1(X0) | ~v1_relat_1(X0))),
% 7.95/1.49    inference(ennf_transformation,[],[f12])).
% 7.95/1.49  
% 7.95/1.49  fof(f51,plain,(
% 7.95/1.49    ( ! [X0] : (k2_xboole_0(k1_relat_1(X0),k2_relat_1(X0)) = k3_relat_1(X0) | ~v1_relat_1(X0)) )),
% 7.95/1.49    inference(cnf_transformation,[],[f25])).
% 7.95/1.49  
% 7.95/1.49  fof(f8,axiom,(
% 7.95/1.49    ! [X0,X1] : r1_tarski(X0,k2_xboole_0(X0,X1))),
% 7.95/1.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.95/1.49  
% 7.95/1.49  fof(f46,plain,(
% 7.95/1.49    ( ! [X0,X1] : (r1_tarski(X0,k2_xboole_0(X0,X1))) )),
% 7.95/1.49    inference(cnf_transformation,[],[f8])).
% 7.95/1.49  
% 7.95/1.49  fof(f13,axiom,(
% 7.95/1.49    ! [X0] : (v1_relat_1(X0) => ! [X1] : (v1_relat_1(X1) => (r1_tarski(X0,X1) => (r1_tarski(k2_relat_1(X0),k2_relat_1(X1)) & r1_tarski(k1_relat_1(X0),k1_relat_1(X1))))))),
% 7.95/1.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.95/1.49  
% 7.95/1.49  fof(f26,plain,(
% 7.95/1.49    ! [X0] : (! [X1] : (((r1_tarski(k2_relat_1(X0),k2_relat_1(X1)) & r1_tarski(k1_relat_1(X0),k1_relat_1(X1))) | ~r1_tarski(X0,X1)) | ~v1_relat_1(X1)) | ~v1_relat_1(X0))),
% 7.95/1.49    inference(ennf_transformation,[],[f13])).
% 7.95/1.49  
% 7.95/1.49  fof(f27,plain,(
% 7.95/1.49    ! [X0] : (! [X1] : ((r1_tarski(k2_relat_1(X0),k2_relat_1(X1)) & r1_tarski(k1_relat_1(X0),k1_relat_1(X1))) | ~r1_tarski(X0,X1) | ~v1_relat_1(X1)) | ~v1_relat_1(X0))),
% 7.95/1.49    inference(flattening,[],[f26])).
% 7.95/1.49  
% 7.95/1.49  fof(f52,plain,(
% 7.95/1.49    ( ! [X0,X1] : (r1_tarski(k1_relat_1(X0),k1_relat_1(X1)) | ~r1_tarski(X0,X1) | ~v1_relat_1(X1) | ~v1_relat_1(X0)) )),
% 7.95/1.49    inference(cnf_transformation,[],[f27])).
% 7.95/1.49  
% 7.95/1.49  fof(f11,axiom,(
% 7.95/1.49    ! [X0] : (v1_relat_1(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => v1_relat_1(X1)))),
% 7.95/1.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.95/1.49  
% 7.95/1.49  fof(f24,plain,(
% 7.95/1.49    ! [X0] : (! [X1] : (v1_relat_1(X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) | ~v1_relat_1(X0))),
% 7.95/1.49    inference(ennf_transformation,[],[f11])).
% 7.95/1.49  
% 7.95/1.49  fof(f50,plain,(
% 7.95/1.49    ( ! [X0,X1] : (v1_relat_1(X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0)) | ~v1_relat_1(X0)) )),
% 7.95/1.49    inference(cnf_transformation,[],[f24])).
% 7.95/1.49  
% 7.95/1.49  fof(f10,axiom,(
% 7.95/1.49    ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) <=> r1_tarski(X0,X1))),
% 7.95/1.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.95/1.49  
% 7.95/1.49  fof(f33,plain,(
% 7.95/1.49    ! [X0,X1] : ((m1_subset_1(X0,k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1)) & (r1_tarski(X0,X1) | ~m1_subset_1(X0,k1_zfmisc_1(X1))))),
% 7.95/1.49    inference(nnf_transformation,[],[f10])).
% 7.95/1.49  
% 7.95/1.49  fof(f49,plain,(
% 7.95/1.49    ( ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1)) )),
% 7.95/1.49    inference(cnf_transformation,[],[f33])).
% 7.95/1.49  
% 7.95/1.49  fof(f4,axiom,(
% 7.95/1.49    ! [X0,X1,X2] : ((r1_tarski(X1,X2) & r1_tarski(X0,X1)) => r1_tarski(X0,X2))),
% 7.95/1.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.95/1.49  
% 7.95/1.49  fof(f18,plain,(
% 7.95/1.49    ! [X0,X1,X2] : (r1_tarski(X0,X2) | (~r1_tarski(X1,X2) | ~r1_tarski(X0,X1)))),
% 7.95/1.49    inference(ennf_transformation,[],[f4])).
% 7.95/1.49  
% 7.95/1.49  fof(f19,plain,(
% 7.95/1.49    ! [X0,X1,X2] : (r1_tarski(X0,X2) | ~r1_tarski(X1,X2) | ~r1_tarski(X0,X1))),
% 7.95/1.49    inference(flattening,[],[f18])).
% 7.95/1.49  
% 7.95/1.49  fof(f42,plain,(
% 7.95/1.49    ( ! [X2,X0,X1] : (r1_tarski(X0,X2) | ~r1_tarski(X1,X2) | ~r1_tarski(X0,X1)) )),
% 7.95/1.49    inference(cnf_transformation,[],[f19])).
% 7.95/1.49  
% 7.95/1.49  fof(f1,axiom,(
% 7.95/1.49    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0)),
% 7.95/1.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.95/1.49  
% 7.95/1.49  fof(f37,plain,(
% 7.95/1.49    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0)) )),
% 7.95/1.49    inference(cnf_transformation,[],[f1])).
% 7.95/1.49  
% 7.95/1.49  fof(f53,plain,(
% 7.95/1.49    ( ! [X0,X1] : (r1_tarski(k2_relat_1(X0),k2_relat_1(X1)) | ~r1_tarski(X0,X1) | ~v1_relat_1(X1) | ~v1_relat_1(X0)) )),
% 7.95/1.49    inference(cnf_transformation,[],[f27])).
% 7.95/1.49  
% 7.95/1.49  fof(f2,axiom,(
% 7.95/1.49    ! [X0,X1] : (X0 = X1 <=> (r1_tarski(X1,X0) & r1_tarski(X0,X1)))),
% 7.95/1.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.95/1.49  
% 7.95/1.49  fof(f31,plain,(
% 7.95/1.49    ! [X0,X1] : ((X0 = X1 | (~r1_tarski(X1,X0) | ~r1_tarski(X0,X1))) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 7.95/1.49    inference(nnf_transformation,[],[f2])).
% 7.95/1.49  
% 7.95/1.49  fof(f32,plain,(
% 7.95/1.49    ! [X0,X1] : ((X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 7.95/1.49    inference(flattening,[],[f31])).
% 7.95/1.49  
% 7.95/1.49  fof(f40,plain,(
% 7.95/1.49    ( ! [X0,X1] : (X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) )),
% 7.95/1.49    inference(cnf_transformation,[],[f32])).
% 7.95/1.49  
% 7.95/1.49  fof(f38,plain,(
% 7.95/1.49    ( ! [X0,X1] : (r1_tarski(X0,X1) | X0 != X1) )),
% 7.95/1.49    inference(cnf_transformation,[],[f32])).
% 7.95/1.49  
% 7.95/1.49  fof(f60,plain,(
% 7.95/1.49    ( ! [X1] : (r1_tarski(X1,X1)) )),
% 7.95/1.49    inference(equality_resolution,[],[f38])).
% 7.95/1.49  
% 7.95/1.49  fof(f58,plain,(
% 7.95/1.49    ~r1_tarski(k3_relat_1(sK0),k3_relat_1(sK1))),
% 7.95/1.49    inference(cnf_transformation,[],[f36])).
% 7.95/1.49  
% 7.95/1.49  fof(f57,plain,(
% 7.95/1.49    r1_tarski(sK0,sK1)),
% 7.95/1.49    inference(cnf_transformation,[],[f36])).
% 7.95/1.49  
% 7.95/1.49  fof(f55,plain,(
% 7.95/1.49    v1_relat_1(sK0)),
% 7.95/1.49    inference(cnf_transformation,[],[f36])).
% 7.95/1.49  
% 7.95/1.49  cnf(c_10,plain,
% 7.95/1.49      ( ~ r1_tarski(X0,X1)
% 7.95/1.49      | ~ r1_tarski(X2,X1)
% 7.95/1.49      | r1_tarski(k2_xboole_0(X0,X2),X1) ),
% 7.95/1.49      inference(cnf_transformation,[],[f47]) ).
% 7.95/1.49  
% 7.95/1.49  cnf(c_1064,plain,
% 7.95/1.49      ( ~ r1_tarski(X0,k3_relat_1(sK1))
% 7.95/1.49      | ~ r1_tarski(X1,k3_relat_1(sK1))
% 7.95/1.49      | r1_tarski(k2_xboole_0(X0,X1),k3_relat_1(sK1)) ),
% 7.95/1.49      inference(instantiation,[status(thm)],[c_10]) ).
% 7.95/1.49  
% 7.95/1.49  cnf(c_30596,plain,
% 7.95/1.49      ( r1_tarski(k2_xboole_0(k1_relat_1(sK0),k2_relat_1(sK0)),k3_relat_1(sK1))
% 7.95/1.49      | ~ r1_tarski(k2_relat_1(sK0),k3_relat_1(sK1))
% 7.95/1.49      | ~ r1_tarski(k1_relat_1(sK0),k3_relat_1(sK1)) ),
% 7.95/1.49      inference(instantiation,[status(thm)],[c_1064]) ).
% 7.95/1.49  
% 7.95/1.49  cnf(c_20,negated_conjecture,
% 7.95/1.49      ( v1_relat_1(sK1) ),
% 7.95/1.49      inference(cnf_transformation,[],[f56]) ).
% 7.95/1.49  
% 7.95/1.49  cnf(c_850,plain,
% 7.95/1.49      ( v1_relat_1(sK1) = iProver_top ),
% 7.95/1.49      inference(predicate_to_equality,[status(thm)],[c_20]) ).
% 7.95/1.49  
% 7.95/1.49  cnf(c_14,plain,
% 7.95/1.49      ( ~ v1_relat_1(X0)
% 7.95/1.49      | k2_xboole_0(k1_relat_1(X0),k2_relat_1(X0)) = k3_relat_1(X0) ),
% 7.95/1.49      inference(cnf_transformation,[],[f51]) ).
% 7.95/1.49  
% 7.95/1.49  cnf(c_854,plain,
% 7.95/1.49      ( k2_xboole_0(k1_relat_1(X0),k2_relat_1(X0)) = k3_relat_1(X0)
% 7.95/1.49      | v1_relat_1(X0) != iProver_top ),
% 7.95/1.49      inference(predicate_to_equality,[status(thm)],[c_14]) ).
% 7.95/1.49  
% 7.95/1.49  cnf(c_1730,plain,
% 7.95/1.49      ( k2_xboole_0(k1_relat_1(sK1),k2_relat_1(sK1)) = k3_relat_1(sK1) ),
% 7.95/1.49      inference(superposition,[status(thm)],[c_850,c_854]) ).
% 7.95/1.49  
% 7.95/1.49  cnf(c_9,plain,
% 7.95/1.49      ( r1_tarski(X0,k2_xboole_0(X0,X1)) ),
% 7.95/1.49      inference(cnf_transformation,[],[f46]) ).
% 7.95/1.49  
% 7.95/1.49  cnf(c_856,plain,
% 7.95/1.49      ( r1_tarski(X0,k2_xboole_0(X0,X1)) = iProver_top ),
% 7.95/1.49      inference(predicate_to_equality,[status(thm)],[c_9]) ).
% 7.95/1.49  
% 7.95/1.49  cnf(c_4382,plain,
% 7.95/1.49      ( r1_tarski(k1_relat_1(sK1),k3_relat_1(sK1)) = iProver_top ),
% 7.95/1.49      inference(superposition,[status(thm)],[c_1730,c_856]) ).
% 7.95/1.49  
% 7.95/1.49  cnf(c_16,plain,
% 7.95/1.49      ( ~ r1_tarski(X0,X1)
% 7.95/1.49      | r1_tarski(k1_relat_1(X0),k1_relat_1(X1))
% 7.95/1.49      | ~ v1_relat_1(X0)
% 7.95/1.49      | ~ v1_relat_1(X1) ),
% 7.95/1.49      inference(cnf_transformation,[],[f52]) ).
% 7.95/1.49  
% 7.95/1.49  cnf(c_13,plain,
% 7.95/1.49      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
% 7.95/1.49      | ~ v1_relat_1(X1)
% 7.95/1.49      | v1_relat_1(X0) ),
% 7.95/1.49      inference(cnf_transformation,[],[f50]) ).
% 7.95/1.49  
% 7.95/1.49  cnf(c_11,plain,
% 7.95/1.49      ( m1_subset_1(X0,k1_zfmisc_1(X1)) | ~ r1_tarski(X0,X1) ),
% 7.95/1.49      inference(cnf_transformation,[],[f49]) ).
% 7.95/1.49  
% 7.95/1.49  cnf(c_118,plain,
% 7.95/1.49      ( r1_tarski(k1_relat_1(X0),k1_relat_1(X1))
% 7.95/1.49      | ~ r1_tarski(X0,X1)
% 7.95/1.49      | ~ v1_relat_1(X1) ),
% 7.95/1.49      inference(global_propositional_subsumption,
% 7.95/1.49                [status(thm)],
% 7.95/1.49                [c_16,c_13,c_11]) ).
% 7.95/1.49  
% 7.95/1.49  cnf(c_119,plain,
% 7.95/1.49      ( ~ r1_tarski(X0,X1)
% 7.95/1.49      | r1_tarski(k1_relat_1(X0),k1_relat_1(X1))
% 7.95/1.49      | ~ v1_relat_1(X1) ),
% 7.95/1.49      inference(renaming,[status(thm)],[c_118]) ).
% 7.95/1.49  
% 7.95/1.49  cnf(c_848,plain,
% 7.95/1.49      ( r1_tarski(X0,X1) != iProver_top
% 7.95/1.49      | r1_tarski(k1_relat_1(X0),k1_relat_1(X1)) = iProver_top
% 7.95/1.49      | v1_relat_1(X1) != iProver_top ),
% 7.95/1.49      inference(predicate_to_equality,[status(thm)],[c_119]) ).
% 7.95/1.49  
% 7.95/1.49  cnf(c_5,plain,
% 7.95/1.49      ( ~ r1_tarski(X0,X1) | ~ r1_tarski(X1,X2) | r1_tarski(X0,X2) ),
% 7.95/1.49      inference(cnf_transformation,[],[f42]) ).
% 7.95/1.49  
% 7.95/1.49  cnf(c_860,plain,
% 7.95/1.49      ( r1_tarski(X0,X1) != iProver_top
% 7.95/1.49      | r1_tarski(X1,X2) != iProver_top
% 7.95/1.49      | r1_tarski(X0,X2) = iProver_top ),
% 7.95/1.49      inference(predicate_to_equality,[status(thm)],[c_5]) ).
% 7.95/1.49  
% 7.95/1.49  cnf(c_2365,plain,
% 7.95/1.49      ( r1_tarski(X0,X1) != iProver_top
% 7.95/1.49      | r1_tarski(k1_relat_1(X1),X2) != iProver_top
% 7.95/1.49      | r1_tarski(k1_relat_1(X0),X2) = iProver_top
% 7.95/1.49      | v1_relat_1(X1) != iProver_top ),
% 7.95/1.49      inference(superposition,[status(thm)],[c_848,c_860]) ).
% 7.95/1.49  
% 7.95/1.49  cnf(c_27498,plain,
% 7.95/1.49      ( r1_tarski(X0,sK1) != iProver_top
% 7.95/1.49      | r1_tarski(k1_relat_1(X0),k3_relat_1(sK1)) = iProver_top
% 7.95/1.49      | v1_relat_1(sK1) != iProver_top ),
% 7.95/1.49      inference(superposition,[status(thm)],[c_4382,c_2365]) ).
% 7.95/1.49  
% 7.95/1.49  cnf(c_27516,plain,
% 7.95/1.49      ( ~ r1_tarski(X0,sK1)
% 7.95/1.49      | r1_tarski(k1_relat_1(X0),k3_relat_1(sK1))
% 7.95/1.49      | ~ v1_relat_1(sK1) ),
% 7.95/1.49      inference(predicate_to_equality_rev,[status(thm)],[c_27498]) ).
% 7.95/1.49  
% 7.95/1.49  cnf(c_27518,plain,
% 7.95/1.49      ( r1_tarski(k1_relat_1(sK0),k3_relat_1(sK1))
% 7.95/1.49      | ~ r1_tarski(sK0,sK1)
% 7.95/1.49      | ~ v1_relat_1(sK1) ),
% 7.95/1.49      inference(instantiation,[status(thm)],[c_27516]) ).
% 7.95/1.49  
% 7.95/1.49  cnf(c_0,plain,
% 7.95/1.49      ( k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0) ),
% 7.95/1.49      inference(cnf_transformation,[],[f37]) ).
% 7.95/1.49  
% 7.95/1.49  cnf(c_1167,plain,
% 7.95/1.49      ( r1_tarski(X0,k2_xboole_0(X1,X0)) = iProver_top ),
% 7.95/1.49      inference(superposition,[status(thm)],[c_0,c_856]) ).
% 7.95/1.49  
% 7.95/1.49  cnf(c_4383,plain,
% 7.95/1.49      ( r1_tarski(k2_relat_1(sK1),k3_relat_1(sK1)) = iProver_top ),
% 7.95/1.49      inference(superposition,[status(thm)],[c_1730,c_1167]) ).
% 7.95/1.49  
% 7.95/1.49  cnf(c_15,plain,
% 7.95/1.49      ( ~ r1_tarski(X0,X1)
% 7.95/1.49      | r1_tarski(k2_relat_1(X0),k2_relat_1(X1))
% 7.95/1.49      | ~ v1_relat_1(X0)
% 7.95/1.49      | ~ v1_relat_1(X1) ),
% 7.95/1.49      inference(cnf_transformation,[],[f53]) ).
% 7.95/1.49  
% 7.95/1.49  cnf(c_123,plain,
% 7.95/1.49      ( r1_tarski(k2_relat_1(X0),k2_relat_1(X1))
% 7.95/1.49      | ~ r1_tarski(X0,X1)
% 7.95/1.49      | ~ v1_relat_1(X1) ),
% 7.95/1.49      inference(global_propositional_subsumption,
% 7.95/1.49                [status(thm)],
% 7.95/1.49                [c_15,c_13,c_11]) ).
% 7.95/1.49  
% 7.95/1.49  cnf(c_124,plain,
% 7.95/1.49      ( ~ r1_tarski(X0,X1)
% 7.95/1.49      | r1_tarski(k2_relat_1(X0),k2_relat_1(X1))
% 7.95/1.49      | ~ v1_relat_1(X1) ),
% 7.95/1.49      inference(renaming,[status(thm)],[c_123]) ).
% 7.95/1.49  
% 7.95/1.49  cnf(c_847,plain,
% 7.95/1.49      ( r1_tarski(X0,X1) != iProver_top
% 7.95/1.49      | r1_tarski(k2_relat_1(X0),k2_relat_1(X1)) = iProver_top
% 7.95/1.49      | v1_relat_1(X1) != iProver_top ),
% 7.95/1.49      inference(predicate_to_equality,[status(thm)],[c_124]) ).
% 7.95/1.49  
% 7.95/1.49  cnf(c_2364,plain,
% 7.95/1.49      ( r1_tarski(X0,X1) != iProver_top
% 7.95/1.49      | r1_tarski(k2_relat_1(X1),X2) != iProver_top
% 7.95/1.49      | r1_tarski(k2_relat_1(X0),X2) = iProver_top
% 7.95/1.49      | v1_relat_1(X1) != iProver_top ),
% 7.95/1.49      inference(superposition,[status(thm)],[c_847,c_860]) ).
% 7.95/1.49  
% 7.95/1.49  cnf(c_25851,plain,
% 7.95/1.49      ( r1_tarski(X0,sK1) != iProver_top
% 7.95/1.49      | r1_tarski(k2_relat_1(X0),k3_relat_1(sK1)) = iProver_top
% 7.95/1.49      | v1_relat_1(sK1) != iProver_top ),
% 7.95/1.49      inference(superposition,[status(thm)],[c_4383,c_2364]) ).
% 7.95/1.49  
% 7.95/1.49  cnf(c_25869,plain,
% 7.95/1.49      ( ~ r1_tarski(X0,sK1)
% 7.95/1.49      | r1_tarski(k2_relat_1(X0),k3_relat_1(sK1))
% 7.95/1.49      | ~ v1_relat_1(sK1) ),
% 7.95/1.49      inference(predicate_to_equality_rev,[status(thm)],[c_25851]) ).
% 7.95/1.49  
% 7.95/1.49  cnf(c_25871,plain,
% 7.95/1.49      ( r1_tarski(k2_relat_1(sK0),k3_relat_1(sK1))
% 7.95/1.49      | ~ r1_tarski(sK0,sK1)
% 7.95/1.49      | ~ v1_relat_1(sK1) ),
% 7.95/1.49      inference(instantiation,[status(thm)],[c_25869]) ).
% 7.95/1.49  
% 7.95/1.49  cnf(c_437,plain,
% 7.95/1.49      ( ~ r1_tarski(X0,X1) | r1_tarski(X2,X3) | X2 != X0 | X3 != X1 ),
% 7.95/1.49      theory(equality) ).
% 7.95/1.49  
% 7.95/1.49  cnf(c_957,plain,
% 7.95/1.49      ( ~ r1_tarski(X0,X1)
% 7.95/1.49      | r1_tarski(k3_relat_1(sK0),k3_relat_1(sK1))
% 7.95/1.49      | k3_relat_1(sK1) != X1
% 7.95/1.49      | k3_relat_1(sK0) != X0 ),
% 7.95/1.49      inference(instantiation,[status(thm)],[c_437]) ).
% 7.95/1.49  
% 7.95/1.49  cnf(c_1793,plain,
% 7.95/1.49      ( ~ r1_tarski(k2_xboole_0(k1_relat_1(sK0),k2_relat_1(sK0)),X0)
% 7.95/1.49      | r1_tarski(k3_relat_1(sK0),k3_relat_1(sK1))
% 7.95/1.49      | k3_relat_1(sK1) != X0
% 7.95/1.49      | k3_relat_1(sK0) != k2_xboole_0(k1_relat_1(sK0),k2_relat_1(sK0)) ),
% 7.95/1.49      inference(instantiation,[status(thm)],[c_957]) ).
% 7.95/1.49  
% 7.95/1.49  cnf(c_2597,plain,
% 7.95/1.49      ( ~ r1_tarski(k2_xboole_0(k1_relat_1(sK0),k2_relat_1(sK0)),k3_relat_1(sK1))
% 7.95/1.49      | r1_tarski(k3_relat_1(sK0),k3_relat_1(sK1))
% 7.95/1.49      | k3_relat_1(sK1) != k3_relat_1(sK1)
% 7.95/1.49      | k3_relat_1(sK0) != k2_xboole_0(k1_relat_1(sK0),k2_relat_1(sK0)) ),
% 7.95/1.49      inference(instantiation,[status(thm)],[c_1793]) ).
% 7.95/1.49  
% 7.95/1.49  cnf(c_435,plain,( X0 != X1 | X2 != X1 | X2 = X0 ),theory(equality) ).
% 7.95/1.49  
% 7.95/1.49  cnf(c_993,plain,
% 7.95/1.49      ( X0 != X1 | k3_relat_1(sK0) != X1 | k3_relat_1(sK0) = X0 ),
% 7.95/1.49      inference(instantiation,[status(thm)],[c_435]) ).
% 7.95/1.49  
% 7.95/1.49  cnf(c_1140,plain,
% 7.95/1.49      ( X0 != k3_relat_1(sK0)
% 7.95/1.49      | k3_relat_1(sK0) = X0
% 7.95/1.49      | k3_relat_1(sK0) != k3_relat_1(sK0) ),
% 7.95/1.49      inference(instantiation,[status(thm)],[c_993]) ).
% 7.95/1.49  
% 7.95/1.49  cnf(c_1534,plain,
% 7.95/1.49      ( k2_xboole_0(k1_relat_1(sK0),k2_relat_1(sK0)) != k3_relat_1(sK0)
% 7.95/1.49      | k3_relat_1(sK0) = k2_xboole_0(k1_relat_1(sK0),k2_relat_1(sK0))
% 7.95/1.49      | k3_relat_1(sK0) != k3_relat_1(sK0) ),
% 7.95/1.49      inference(instantiation,[status(thm)],[c_1140]) ).
% 7.95/1.49  
% 7.95/1.49  cnf(c_434,plain,( X0 = X0 ),theory(equality) ).
% 7.95/1.49  
% 7.95/1.49  cnf(c_1145,plain,
% 7.95/1.49      ( k3_relat_1(sK1) = k3_relat_1(sK1) ),
% 7.95/1.49      inference(instantiation,[status(thm)],[c_434]) ).
% 7.95/1.49  
% 7.95/1.49  cnf(c_440,plain,
% 7.95/1.49      ( X0 != X1 | k3_relat_1(X0) = k3_relat_1(X1) ),
% 7.95/1.49      theory(equality) ).
% 7.95/1.49  
% 7.95/1.49  cnf(c_444,plain,
% 7.95/1.49      ( k3_relat_1(sK0) = k3_relat_1(sK0) | sK0 != sK0 ),
% 7.95/1.49      inference(instantiation,[status(thm)],[c_440]) ).
% 7.95/1.49  
% 7.95/1.49  cnf(c_1,plain,
% 7.95/1.49      ( ~ r1_tarski(X0,X1) | ~ r1_tarski(X1,X0) | X0 = X1 ),
% 7.95/1.49      inference(cnf_transformation,[],[f40]) ).
% 7.95/1.49  
% 7.95/1.49  cnf(c_67,plain,
% 7.95/1.49      ( ~ r1_tarski(sK0,sK0) | sK0 = sK0 ),
% 7.95/1.49      inference(instantiation,[status(thm)],[c_1]) ).
% 7.95/1.49  
% 7.95/1.49  cnf(c_3,plain,
% 7.95/1.49      ( r1_tarski(X0,X0) ),
% 7.95/1.49      inference(cnf_transformation,[],[f60]) ).
% 7.95/1.49  
% 7.95/1.49  cnf(c_63,plain,
% 7.95/1.49      ( r1_tarski(sK0,sK0) ),
% 7.95/1.49      inference(instantiation,[status(thm)],[c_3]) ).
% 7.95/1.49  
% 7.95/1.49  cnf(c_36,plain,
% 7.95/1.49      ( ~ v1_relat_1(sK0)
% 7.95/1.49      | k2_xboole_0(k1_relat_1(sK0),k2_relat_1(sK0)) = k3_relat_1(sK0) ),
% 7.95/1.49      inference(instantiation,[status(thm)],[c_14]) ).
% 7.95/1.49  
% 7.95/1.49  cnf(c_18,negated_conjecture,
% 7.95/1.49      ( ~ r1_tarski(k3_relat_1(sK0),k3_relat_1(sK1)) ),
% 7.95/1.49      inference(cnf_transformation,[],[f58]) ).
% 7.95/1.49  
% 7.95/1.49  cnf(c_19,negated_conjecture,
% 7.95/1.49      ( r1_tarski(sK0,sK1) ),
% 7.95/1.49      inference(cnf_transformation,[],[f57]) ).
% 7.95/1.49  
% 7.95/1.49  cnf(c_21,negated_conjecture,
% 7.95/1.49      ( v1_relat_1(sK0) ),
% 7.95/1.49      inference(cnf_transformation,[],[f55]) ).
% 7.95/1.49  
% 7.95/1.49  cnf(contradiction,plain,
% 7.95/1.49      ( $false ),
% 7.95/1.49      inference(minisat,
% 7.95/1.49                [status(thm)],
% 7.95/1.49                [c_30596,c_27518,c_25871,c_2597,c_1534,c_1145,c_444,c_67,
% 7.95/1.49                 c_63,c_36,c_18,c_19,c_20,c_21]) ).
% 7.95/1.49  
% 7.95/1.49  
% 7.95/1.49  % SZS output end CNFRefutation for theBenchmark.p
% 7.95/1.49  
% 7.95/1.49  ------                               Statistics
% 7.95/1.49  
% 7.95/1.49  ------ Selected
% 7.95/1.49  
% 7.95/1.49  total_time:                             0.973
% 7.95/1.49  
%------------------------------------------------------------------------------
