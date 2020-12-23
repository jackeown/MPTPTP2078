%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n012.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 11:55:07 EST 2020

% Result     : Theorem 2.46s
% Output     : CNFRefutation 2.46s
% Verified   : 
% Statistics : Number of formulae       :  141 ( 344 expanded)
%              Number of clauses        :   99 ( 176 expanded)
%              Number of leaves         :   16 (  62 expanded)
%              Depth                    :   16
%              Number of atoms          :  341 ( 842 expanded)
%              Number of equality atoms :  165 ( 358 expanded)
%              Maximal formula depth    :    8 (   4 average)
%              Maximal clause size      :    6 (   2 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f11,conjecture,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => ( k1_relset_1(X0,X1,X2) = k2_relset_1(X1,X0,k3_relset_1(X0,X1,X2))
        & k1_relset_1(X1,X0,k3_relset_1(X0,X1,X2)) = k2_relset_1(X0,X1,X2) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f12,negated_conjecture,(
    ~ ! [X0,X1,X2] :
        ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
       => ( k1_relset_1(X0,X1,X2) = k2_relset_1(X1,X0,k3_relset_1(X0,X1,X2))
          & k1_relset_1(X1,X0,k3_relset_1(X0,X1,X2)) = k2_relset_1(X0,X1,X2) ) ) ),
    inference(negated_conjecture,[],[f11])).

fof(f24,plain,(
    ? [X0,X1,X2] :
      ( ( k1_relset_1(X0,X1,X2) != k2_relset_1(X1,X0,k3_relset_1(X0,X1,X2))
        | k1_relset_1(X1,X0,k3_relset_1(X0,X1,X2)) != k2_relset_1(X0,X1,X2) )
      & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f27,plain,
    ( ? [X0,X1,X2] :
        ( ( k1_relset_1(X0,X1,X2) != k2_relset_1(X1,X0,k3_relset_1(X0,X1,X2))
          | k1_relset_1(X1,X0,k3_relset_1(X0,X1,X2)) != k2_relset_1(X0,X1,X2) )
        & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) )
   => ( ( k1_relset_1(sK0,sK1,sK2) != k2_relset_1(sK1,sK0,k3_relset_1(sK0,sK1,sK2))
        | k1_relset_1(sK1,sK0,k3_relset_1(sK0,sK1,sK2)) != k2_relset_1(sK0,sK1,sK2) )
      & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ) ),
    introduced(choice_axiom,[])).

fof(f28,plain,
    ( ( k1_relset_1(sK0,sK1,sK2) != k2_relset_1(sK1,sK0,k3_relset_1(sK0,sK1,sK2))
      | k1_relset_1(sK1,sK0,k3_relset_1(sK0,sK1,sK2)) != k2_relset_1(sK0,sK1,sK2) )
    & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f24,f27])).

fof(f43,plain,(
    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ),
    inference(cnf_transformation,[],[f28])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ( v5_relat_1(X1,X0)
      <=> r1_tarski(k2_relat_1(X1),X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f14,plain,(
    ! [X0,X1] :
      ( ( v5_relat_1(X1,X0)
      <=> r1_tarski(k2_relat_1(X1),X0) )
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f26,plain,(
    ! [X0,X1] :
      ( ( ( v5_relat_1(X1,X0)
          | ~ r1_tarski(k2_relat_1(X1),X0) )
        & ( r1_tarski(k2_relat_1(X1),X0)
          | ~ v5_relat_1(X1,X0) ) )
      | ~ v1_relat_1(X1) ) ),
    inference(nnf_transformation,[],[f14])).

fof(f31,plain,(
    ! [X0,X1] :
      ( r1_tarski(k2_relat_1(X1),X0)
      | ~ v5_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f6,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => ( v5_relat_1(X2,X1)
        & v4_relat_1(X2,X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f18,plain,(
    ! [X0,X1,X2] :
      ( ( v5_relat_1(X2,X1)
        & v4_relat_1(X2,X0) )
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f38,plain,(
    ! [X2,X0,X1] :
      ( v5_relat_1(X2,X1)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f5,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => v1_relat_1(X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f17,plain,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f36,plain,(
    ! [X2,X0,X1] :
      ( v1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f37,plain,(
    ! [X2,X0,X1] :
      ( v4_relat_1(X2,X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ( v4_relat_1(X1,X0)
      <=> r1_tarski(k1_relat_1(X1),X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f13,plain,(
    ! [X0,X1] :
      ( ( v4_relat_1(X1,X0)
      <=> r1_tarski(k1_relat_1(X1),X0) )
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f25,plain,(
    ! [X0,X1] :
      ( ( ( v4_relat_1(X1,X0)
          | ~ r1_tarski(k1_relat_1(X1),X0) )
        & ( r1_tarski(k1_relat_1(X1),X0)
          | ~ v4_relat_1(X1,X0) ) )
      | ~ v1_relat_1(X1) ) ),
    inference(nnf_transformation,[],[f13])).

fof(f29,plain,(
    ! [X0,X1] :
      ( r1_tarski(k1_relat_1(X1),X0)
      | ~ v4_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f4,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ( k1_relat_1(X0) = k2_relat_1(k4_relat_1(X0))
        & k1_relat_1(k4_relat_1(X0)) = k2_relat_1(X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f16,plain,(
    ! [X0] :
      ( ( k1_relat_1(X0) = k2_relat_1(k4_relat_1(X0))
        & k1_relat_1(k4_relat_1(X0)) = k2_relat_1(X0) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f35,plain,(
    ! [X0] :
      ( k1_relat_1(X0) = k2_relat_1(k4_relat_1(X0))
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f16])).

fof(f10,axiom,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
     => ( ( r1_tarski(k2_relat_1(X2),X1)
          & r1_tarski(k1_relat_1(X2),X0) )
       => m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f22,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ r1_tarski(k2_relat_1(X2),X1)
      | ~ r1_tarski(k1_relat_1(X2),X0)
      | ~ v1_relat_1(X2) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f23,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ r1_tarski(k2_relat_1(X2),X1)
      | ~ r1_tarski(k1_relat_1(X2),X0)
      | ~ v1_relat_1(X2) ) ),
    inference(flattening,[],[f22])).

fof(f42,plain,(
    ! [X2,X0,X1] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ r1_tarski(k2_relat_1(X2),X1)
      | ~ r1_tarski(k1_relat_1(X2),X0)
      | ~ v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f8,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k2_relat_1(X2) = k2_relset_1(X0,X1,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f20,plain,(
    ! [X0,X1,X2] :
      ( k2_relat_1(X2) = k2_relset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f40,plain,(
    ! [X2,X0,X1] :
      ( k2_relat_1(X2) = k2_relset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f34,plain,(
    ! [X0] :
      ( k1_relat_1(k4_relat_1(X0)) = k2_relat_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f16])).

fof(f3,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => v1_relat_1(k4_relat_1(X0)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f15,plain,(
    ! [X0] :
      ( v1_relat_1(k4_relat_1(X0))
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f33,plain,(
    ! [X0] :
      ( v1_relat_1(k4_relat_1(X0))
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f15])).

fof(f7,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k1_relat_1(X2) = k1_relset_1(X0,X1,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f19,plain,(
    ! [X0,X1,X2] :
      ( k1_relat_1(X2) = k1_relset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f39,plain,(
    ! [X2,X0,X1] :
      ( k1_relat_1(X2) = k1_relset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f44,plain,
    ( k1_relset_1(sK0,sK1,sK2) != k2_relset_1(sK1,sK0,k3_relset_1(sK0,sK1,sK2))
    | k1_relset_1(sK1,sK0,k3_relset_1(sK0,sK1,sK2)) != k2_relset_1(sK0,sK1,sK2) ),
    inference(cnf_transformation,[],[f28])).

fof(f9,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k4_relat_1(X2) = k3_relset_1(X0,X1,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f21,plain,(
    ! [X0,X1,X2] :
      ( k4_relat_1(X2) = k3_relset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f41,plain,(
    ! [X2,X0,X1] :
      ( k4_relat_1(X2) = k3_relset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f21])).

cnf(c_15,negated_conjecture,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ),
    inference(cnf_transformation,[],[f43])).

cnf(c_586,negated_conjecture,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ),
    inference(subtyping,[status(esa)],[c_15])).

cnf(c_859,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_586])).

cnf(c_3,plain,
    ( ~ v5_relat_1(X0,X1)
    | r1_tarski(k2_relat_1(X0),X1)
    | ~ v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f31])).

cnf(c_8,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | v5_relat_1(X0,X2) ),
    inference(cnf_transformation,[],[f38])).

cnf(c_208,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | r1_tarski(k2_relat_1(X3),X4)
    | ~ v1_relat_1(X3)
    | X0 != X3
    | X2 != X4 ),
    inference(resolution_lifted,[status(thm)],[c_3,c_8])).

cnf(c_209,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | r1_tarski(k2_relat_1(X0),X2)
    | ~ v1_relat_1(X0) ),
    inference(unflattening,[status(thm)],[c_208])).

cnf(c_7,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f36])).

cnf(c_213,plain,
    ( r1_tarski(k2_relat_1(X0),X2)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) ),
    inference(global_propositional_subsumption,[status(thm)],[c_209,c_7])).

cnf(c_214,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | r1_tarski(k2_relat_1(X0),X2) ),
    inference(renaming,[status(thm)],[c_213])).

cnf(c_584,plain,
    ( ~ m1_subset_1(X0_44,k1_zfmisc_1(k2_zfmisc_1(X0_47,X1_47)))
    | r1_tarski(k2_relat_1(X0_44),X1_47) ),
    inference(subtyping,[status(esa)],[c_214])).

cnf(c_861,plain,
    ( m1_subset_1(X0_44,k1_zfmisc_1(k2_zfmisc_1(X0_47,X1_47))) != iProver_top
    | r1_tarski(k2_relat_1(X0_44),X1_47) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_584])).

cnf(c_2060,plain,
    ( r1_tarski(k2_relat_1(sK2),sK1) = iProver_top ),
    inference(superposition,[status(thm)],[c_859,c_861])).

cnf(c_9,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | v4_relat_1(X0,X1) ),
    inference(cnf_transformation,[],[f37])).

cnf(c_1,plain,
    ( r1_tarski(k1_relat_1(X0),X1)
    | ~ v4_relat_1(X0,X1)
    | ~ v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f29])).

cnf(c_186,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | r1_tarski(k1_relat_1(X0),X1)
    | ~ v1_relat_1(X0) ),
    inference(resolution,[status(thm)],[c_9,c_1])).

cnf(c_190,plain,
    ( r1_tarski(k1_relat_1(X0),X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) ),
    inference(global_propositional_subsumption,[status(thm)],[c_186,c_7])).

cnf(c_191,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | r1_tarski(k1_relat_1(X0),X1) ),
    inference(renaming,[status(thm)],[c_190])).

cnf(c_585,plain,
    ( ~ m1_subset_1(X0_44,k1_zfmisc_1(k2_zfmisc_1(X0_47,X1_47)))
    | r1_tarski(k1_relat_1(X0_44),X0_47) ),
    inference(subtyping,[status(esa)],[c_191])).

cnf(c_860,plain,
    ( m1_subset_1(X0_44,k1_zfmisc_1(k2_zfmisc_1(X0_47,X1_47))) != iProver_top
    | r1_tarski(k1_relat_1(X0_44),X0_47) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_585])).

cnf(c_1605,plain,
    ( r1_tarski(k1_relat_1(sK2),sK0) = iProver_top ),
    inference(superposition,[status(thm)],[c_859,c_860])).

cnf(c_592,plain,
    ( ~ m1_subset_1(X0_44,k1_zfmisc_1(k2_zfmisc_1(X0_47,X1_47)))
    | v1_relat_1(X0_44) ),
    inference(subtyping,[status(esa)],[c_7])).

cnf(c_854,plain,
    ( m1_subset_1(X0_44,k1_zfmisc_1(k2_zfmisc_1(X0_47,X1_47))) != iProver_top
    | v1_relat_1(X0_44) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_592])).

cnf(c_994,plain,
    ( v1_relat_1(sK2) = iProver_top ),
    inference(superposition,[status(thm)],[c_859,c_854])).

cnf(c_5,plain,
    ( ~ v1_relat_1(X0)
    | k2_relat_1(k4_relat_1(X0)) = k1_relat_1(X0) ),
    inference(cnf_transformation,[],[f35])).

cnf(c_594,plain,
    ( ~ v1_relat_1(X0_44)
    | k2_relat_1(k4_relat_1(X0_44)) = k1_relat_1(X0_44) ),
    inference(subtyping,[status(esa)],[c_5])).

cnf(c_852,plain,
    ( k2_relat_1(k4_relat_1(X0_44)) = k1_relat_1(X0_44)
    | v1_relat_1(X0_44) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_594])).

cnf(c_1031,plain,
    ( k2_relat_1(k4_relat_1(sK2)) = k1_relat_1(sK2) ),
    inference(superposition,[status(thm)],[c_994,c_852])).

cnf(c_13,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ r1_tarski(k2_relat_1(X0),X2)
    | ~ r1_tarski(k1_relat_1(X0),X1)
    | ~ v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f42])).

cnf(c_588,plain,
    ( m1_subset_1(X0_44,k1_zfmisc_1(k2_zfmisc_1(X0_47,X1_47)))
    | ~ r1_tarski(k2_relat_1(X0_44),X1_47)
    | ~ r1_tarski(k1_relat_1(X0_44),X0_47)
    | ~ v1_relat_1(X0_44) ),
    inference(subtyping,[status(esa)],[c_13])).

cnf(c_858,plain,
    ( m1_subset_1(X0_44,k1_zfmisc_1(k2_zfmisc_1(X0_47,X1_47))) = iProver_top
    | r1_tarski(k2_relat_1(X0_44),X1_47) != iProver_top
    | r1_tarski(k1_relat_1(X0_44),X0_47) != iProver_top
    | v1_relat_1(X0_44) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_588])).

cnf(c_11,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k2_relset_1(X1,X2,X0) = k2_relat_1(X0) ),
    inference(cnf_transformation,[],[f40])).

cnf(c_590,plain,
    ( ~ m1_subset_1(X0_44,k1_zfmisc_1(k2_zfmisc_1(X0_47,X1_47)))
    | k2_relset_1(X0_47,X1_47,X0_44) = k2_relat_1(X0_44) ),
    inference(subtyping,[status(esa)],[c_11])).

cnf(c_856,plain,
    ( k2_relset_1(X0_47,X1_47,X0_44) = k2_relat_1(X0_44)
    | m1_subset_1(X0_44,k1_zfmisc_1(k2_zfmisc_1(X0_47,X1_47))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_590])).

cnf(c_1168,plain,
    ( k2_relset_1(X0_47,X1_47,X0_44) = k2_relat_1(X0_44)
    | r1_tarski(k2_relat_1(X0_44),X1_47) != iProver_top
    | r1_tarski(k1_relat_1(X0_44),X0_47) != iProver_top
    | v1_relat_1(X0_44) != iProver_top ),
    inference(superposition,[status(thm)],[c_858,c_856])).

cnf(c_2981,plain,
    ( k2_relset_1(X0_47,X1_47,k4_relat_1(sK2)) = k2_relat_1(k4_relat_1(sK2))
    | r1_tarski(k1_relat_1(k4_relat_1(sK2)),X0_47) != iProver_top
    | r1_tarski(k1_relat_1(sK2),X1_47) != iProver_top
    | v1_relat_1(k4_relat_1(sK2)) != iProver_top ),
    inference(superposition,[status(thm)],[c_1031,c_1168])).

cnf(c_6,plain,
    ( ~ v1_relat_1(X0)
    | k1_relat_1(k4_relat_1(X0)) = k2_relat_1(X0) ),
    inference(cnf_transformation,[],[f34])).

cnf(c_593,plain,
    ( ~ v1_relat_1(X0_44)
    | k1_relat_1(k4_relat_1(X0_44)) = k2_relat_1(X0_44) ),
    inference(subtyping,[status(esa)],[c_6])).

cnf(c_853,plain,
    ( k1_relat_1(k4_relat_1(X0_44)) = k2_relat_1(X0_44)
    | v1_relat_1(X0_44) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_593])).

cnf(c_1030,plain,
    ( k1_relat_1(k4_relat_1(sK2)) = k2_relat_1(sK2) ),
    inference(superposition,[status(thm)],[c_994,c_853])).

cnf(c_3036,plain,
    ( k2_relset_1(X0_47,X1_47,k4_relat_1(sK2)) = k1_relat_1(sK2)
    | r1_tarski(k2_relat_1(sK2),X0_47) != iProver_top
    | r1_tarski(k1_relat_1(sK2),X1_47) != iProver_top
    | v1_relat_1(k4_relat_1(sK2)) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_2981,c_1030,c_1031])).

cnf(c_16,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_15])).

cnf(c_4,plain,
    ( ~ v1_relat_1(X0)
    | v1_relat_1(k4_relat_1(X0)) ),
    inference(cnf_transformation,[],[f33])).

cnf(c_595,plain,
    ( ~ v1_relat_1(X0_44)
    | v1_relat_1(k4_relat_1(X0_44)) ),
    inference(subtyping,[status(esa)],[c_4])).

cnf(c_620,plain,
    ( v1_relat_1(X0_44) != iProver_top
    | v1_relat_1(k4_relat_1(X0_44)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_595])).

cnf(c_622,plain,
    ( v1_relat_1(k4_relat_1(sK2)) = iProver_top
    | v1_relat_1(sK2) != iProver_top ),
    inference(instantiation,[status(thm)],[c_620])).

cnf(c_937,plain,
    ( ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    | v1_relat_1(sK2) ),
    inference(instantiation,[status(thm)],[c_592])).

cnf(c_938,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) != iProver_top
    | v1_relat_1(sK2) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_937])).

cnf(c_6034,plain,
    ( r1_tarski(k1_relat_1(sK2),X1_47) != iProver_top
    | r1_tarski(k2_relat_1(sK2),X0_47) != iProver_top
    | k2_relset_1(X0_47,X1_47,k4_relat_1(sK2)) = k1_relat_1(sK2) ),
    inference(global_propositional_subsumption,[status(thm)],[c_3036,c_16,c_622,c_938])).

cnf(c_6035,plain,
    ( k2_relset_1(X0_47,X1_47,k4_relat_1(sK2)) = k1_relat_1(sK2)
    | r1_tarski(k2_relat_1(sK2),X0_47) != iProver_top
    | r1_tarski(k1_relat_1(sK2),X1_47) != iProver_top ),
    inference(renaming,[status(thm)],[c_6034])).

cnf(c_6043,plain,
    ( k2_relset_1(X0_47,sK0,k4_relat_1(sK2)) = k1_relat_1(sK2)
    | r1_tarski(k2_relat_1(sK2),X0_47) != iProver_top ),
    inference(superposition,[status(thm)],[c_1605,c_6035])).

cnf(c_6119,plain,
    ( k2_relset_1(sK1,sK0,k4_relat_1(sK2)) = k1_relat_1(sK2) ),
    inference(superposition,[status(thm)],[c_2060,c_6043])).

cnf(c_600,plain,
    ( X0_48 != X1_48
    | X2_48 != X1_48
    | X2_48 = X0_48 ),
    theory(equality)).

cnf(c_1298,plain,
    ( X0_48 != X1_48
    | X0_48 = k2_relat_1(X0_44)
    | k2_relat_1(X0_44) != X1_48 ),
    inference(instantiation,[status(thm)],[c_600])).

cnf(c_1938,plain,
    ( X0_48 != k2_relset_1(sK0,sK1,sK2)
    | X0_48 = k2_relat_1(X0_44)
    | k2_relat_1(X0_44) != k2_relset_1(sK0,sK1,sK2) ),
    inference(instantiation,[status(thm)],[c_1298])).

cnf(c_4984,plain,
    ( k1_relset_1(sK1,sK0,k4_relat_1(sK2)) != k2_relset_1(sK0,sK1,sK2)
    | k1_relset_1(sK1,sK0,k4_relat_1(sK2)) = k2_relat_1(X0_44)
    | k2_relat_1(X0_44) != k2_relset_1(sK0,sK1,sK2) ),
    inference(instantiation,[status(thm)],[c_1938])).

cnf(c_4992,plain,
    ( k1_relset_1(sK1,sK0,k4_relat_1(sK2)) != k2_relset_1(sK0,sK1,sK2)
    | k1_relset_1(sK1,sK0,k4_relat_1(sK2)) = k2_relat_1(sK2)
    | k2_relat_1(sK2) != k2_relset_1(sK0,sK1,sK2) ),
    inference(instantiation,[status(thm)],[c_4984])).

cnf(c_1235,plain,
    ( X0_48 != X1_48
    | X0_48 = k2_relset_1(sK0,sK1,sK2)
    | k2_relset_1(sK0,sK1,sK2) != X1_48 ),
    inference(instantiation,[status(thm)],[c_600])).

cnf(c_1535,plain,
    ( X0_48 = k2_relset_1(sK0,sK1,sK2)
    | X0_48 != k1_relat_1(k4_relat_1(sK2))
    | k2_relset_1(sK0,sK1,sK2) != k1_relat_1(k4_relat_1(sK2)) ),
    inference(instantiation,[status(thm)],[c_1235])).

cnf(c_2455,plain,
    ( k2_relset_1(sK0,sK1,sK2) != k1_relat_1(k4_relat_1(sK2))
    | k1_relset_1(sK1,sK0,k4_relat_1(sK2)) = k2_relset_1(sK0,sK1,sK2)
    | k1_relset_1(sK1,sK0,k4_relat_1(sK2)) != k1_relat_1(k4_relat_1(sK2)) ),
    inference(instantiation,[status(thm)],[c_1535])).

cnf(c_10,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k1_relset_1(X1,X2,X0) = k1_relat_1(X0) ),
    inference(cnf_transformation,[],[f39])).

cnf(c_591,plain,
    ( ~ m1_subset_1(X0_44,k1_zfmisc_1(k2_zfmisc_1(X0_47,X1_47)))
    | k1_relset_1(X0_47,X1_47,X0_44) = k1_relat_1(X0_44) ),
    inference(subtyping,[status(esa)],[c_10])).

cnf(c_1867,plain,
    ( ~ m1_subset_1(k4_relat_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
    | k1_relset_1(sK1,sK0,k4_relat_1(sK2)) = k1_relat_1(k4_relat_1(sK2)) ),
    inference(instantiation,[status(thm)],[c_591])).

cnf(c_1529,plain,
    ( X0_48 = k2_relset_1(sK0,sK1,sK2)
    | X0_48 != k2_relat_1(sK2)
    | k2_relset_1(sK0,sK1,sK2) != k2_relat_1(sK2) ),
    inference(instantiation,[status(thm)],[c_1235])).

cnf(c_1716,plain,
    ( k2_relset_1(sK0,sK1,sK2) != k2_relat_1(sK2)
    | k2_relat_1(X0_44) = k2_relset_1(sK0,sK1,sK2)
    | k2_relat_1(X0_44) != k2_relat_1(sK2) ),
    inference(instantiation,[status(thm)],[c_1529])).

cnf(c_1717,plain,
    ( k2_relset_1(sK0,sK1,sK2) != k2_relat_1(sK2)
    | k2_relat_1(sK2) = k2_relset_1(sK0,sK1,sK2)
    | k2_relat_1(sK2) != k2_relat_1(sK2) ),
    inference(instantiation,[status(thm)],[c_1716])).

cnf(c_1219,plain,
    ( m1_subset_1(k4_relat_1(sK2),k1_zfmisc_1(k2_zfmisc_1(X0_47,sK0)))
    | ~ r1_tarski(k2_relat_1(k4_relat_1(sK2)),sK0)
    | ~ r1_tarski(k1_relat_1(k4_relat_1(sK2)),X0_47)
    | ~ v1_relat_1(k4_relat_1(sK2)) ),
    inference(instantiation,[status(thm)],[c_588])).

cnf(c_1448,plain,
    ( m1_subset_1(k4_relat_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
    | ~ r1_tarski(k2_relat_1(k4_relat_1(sK2)),sK0)
    | ~ r1_tarski(k1_relat_1(k4_relat_1(sK2)),sK1)
    | ~ v1_relat_1(k4_relat_1(sK2)) ),
    inference(instantiation,[status(thm)],[c_1219])).

cnf(c_1118,plain,
    ( k2_relset_1(sK0,sK1,sK2) = k2_relat_1(sK2) ),
    inference(superposition,[status(thm)],[c_859,c_856])).

cnf(c_855,plain,
    ( k1_relset_1(X0_47,X1_47,X0_44) = k1_relat_1(X0_44)
    | m1_subset_1(X0_44,k1_zfmisc_1(k2_zfmisc_1(X0_47,X1_47))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_591])).

cnf(c_1114,plain,
    ( k1_relset_1(sK0,sK1,sK2) = k1_relat_1(sK2) ),
    inference(superposition,[status(thm)],[c_859,c_855])).

cnf(c_14,negated_conjecture,
    ( k1_relset_1(sK1,sK0,k3_relset_1(sK0,sK1,sK2)) != k2_relset_1(sK0,sK1,sK2)
    | k1_relset_1(sK0,sK1,sK2) != k2_relset_1(sK1,sK0,k3_relset_1(sK0,sK1,sK2)) ),
    inference(cnf_transformation,[],[f44])).

cnf(c_587,negated_conjecture,
    ( k1_relset_1(sK1,sK0,k3_relset_1(sK0,sK1,sK2)) != k2_relset_1(sK0,sK1,sK2)
    | k1_relset_1(sK0,sK1,sK2) != k2_relset_1(sK1,sK0,k3_relset_1(sK0,sK1,sK2)) ),
    inference(subtyping,[status(esa)],[c_14])).

cnf(c_1246,plain,
    ( k2_relset_1(sK1,sK0,k3_relset_1(sK0,sK1,sK2)) != k1_relat_1(sK2)
    | k1_relset_1(sK1,sK0,k3_relset_1(sK0,sK1,sK2)) != k2_relset_1(sK0,sK1,sK2) ),
    inference(demodulation,[status(thm)],[c_1114,c_587])).

cnf(c_1312,plain,
    ( k2_relset_1(sK1,sK0,k3_relset_1(sK0,sK1,sK2)) != k1_relat_1(sK2)
    | k1_relset_1(sK1,sK0,k3_relset_1(sK0,sK1,sK2)) != k2_relat_1(sK2) ),
    inference(demodulation,[status(thm)],[c_1118,c_1246])).

cnf(c_12,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k3_relset_1(X1,X2,X0) = k4_relat_1(X0) ),
    inference(cnf_transformation,[],[f41])).

cnf(c_589,plain,
    ( ~ m1_subset_1(X0_44,k1_zfmisc_1(k2_zfmisc_1(X0_47,X1_47)))
    | k3_relset_1(X0_47,X1_47,X0_44) = k4_relat_1(X0_44) ),
    inference(subtyping,[status(esa)],[c_12])).

cnf(c_857,plain,
    ( k3_relset_1(X0_47,X1_47,X0_44) = k4_relat_1(X0_44)
    | m1_subset_1(X0_44,k1_zfmisc_1(k2_zfmisc_1(X0_47,X1_47))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_589])).

cnf(c_1161,plain,
    ( k3_relset_1(sK0,sK1,sK2) = k4_relat_1(sK2) ),
    inference(superposition,[status(thm)],[c_859,c_857])).

cnf(c_1400,plain,
    ( k2_relset_1(sK1,sK0,k4_relat_1(sK2)) != k1_relat_1(sK2)
    | k1_relset_1(sK1,sK0,k4_relat_1(sK2)) != k2_relat_1(sK2) ),
    inference(light_normalisation,[status(thm)],[c_1312,c_1161])).

cnf(c_997,plain,
    ( X0_48 != X1_48
    | k2_relset_1(sK0,sK1,sK2) != X1_48
    | k2_relset_1(sK0,sK1,sK2) = X0_48 ),
    inference(instantiation,[status(thm)],[c_600])).

cnf(c_1127,plain,
    ( X0_48 != k2_relat_1(sK2)
    | k2_relset_1(sK0,sK1,sK2) = X0_48
    | k2_relset_1(sK0,sK1,sK2) != k2_relat_1(sK2) ),
    inference(instantiation,[status(thm)],[c_997])).

cnf(c_1215,plain,
    ( k2_relset_1(sK0,sK1,sK2) != k2_relat_1(sK2)
    | k2_relset_1(sK0,sK1,sK2) = k1_relat_1(k4_relat_1(sK2))
    | k1_relat_1(k4_relat_1(sK2)) != k2_relat_1(sK2) ),
    inference(instantiation,[status(thm)],[c_1127])).

cnf(c_602,plain,
    ( ~ r1_tarski(X0_48,X0_47)
    | r1_tarski(X1_48,X0_47)
    | X1_48 != X0_48 ),
    theory(equality)).

cnf(c_979,plain,
    ( r1_tarski(X0_48,sK0)
    | ~ r1_tarski(k1_relat_1(sK2),sK0)
    | X0_48 != k1_relat_1(sK2) ),
    inference(instantiation,[status(thm)],[c_602])).

cnf(c_1062,plain,
    ( r1_tarski(k2_relat_1(k4_relat_1(sK2)),sK0)
    | ~ r1_tarski(k1_relat_1(sK2),sK0)
    | k2_relat_1(k4_relat_1(sK2)) != k1_relat_1(sK2) ),
    inference(instantiation,[status(thm)],[c_979])).

cnf(c_974,plain,
    ( r1_tarski(X0_48,sK1)
    | ~ r1_tarski(k2_relat_1(sK2),sK1)
    | X0_48 != k2_relat_1(sK2) ),
    inference(instantiation,[status(thm)],[c_602])).

cnf(c_1037,plain,
    ( ~ r1_tarski(k2_relat_1(sK2),sK1)
    | r1_tarski(k1_relat_1(k4_relat_1(sK2)),sK1)
    | k1_relat_1(k4_relat_1(sK2)) != k2_relat_1(sK2) ),
    inference(instantiation,[status(thm)],[c_974])).

cnf(c_958,plain,
    ( ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    | k2_relset_1(sK0,sK1,sK2) = k2_relat_1(sK2) ),
    inference(instantiation,[status(thm)],[c_590])).

cnf(c_947,plain,
    ( ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    | r1_tarski(k1_relat_1(sK2),sK0) ),
    inference(instantiation,[status(thm)],[c_585])).

cnf(c_944,plain,
    ( ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    | r1_tarski(k2_relat_1(sK2),sK1) ),
    inference(instantiation,[status(thm)],[c_584])).

cnf(c_627,plain,
    ( ~ v1_relat_1(sK2)
    | k1_relat_1(k4_relat_1(sK2)) = k2_relat_1(sK2) ),
    inference(instantiation,[status(thm)],[c_593])).

cnf(c_624,plain,
    ( ~ v1_relat_1(sK2)
    | k2_relat_1(k4_relat_1(sK2)) = k1_relat_1(sK2) ),
    inference(instantiation,[status(thm)],[c_594])).

cnf(c_621,plain,
    ( v1_relat_1(k4_relat_1(sK2))
    | ~ v1_relat_1(sK2) ),
    inference(instantiation,[status(thm)],[c_595])).

cnf(c_597,plain,
    ( X0_44 = X0_44 ),
    theory(equality)).

cnf(c_618,plain,
    ( sK2 = sK2 ),
    inference(instantiation,[status(thm)],[c_597])).

cnf(c_604,plain,
    ( k2_relat_1(X0_44) = k2_relat_1(X1_44)
    | X0_44 != X1_44 ),
    theory(equality)).

cnf(c_612,plain,
    ( k2_relat_1(sK2) = k2_relat_1(sK2)
    | sK2 != sK2 ),
    inference(instantiation,[status(thm)],[c_604])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_6119,c_4992,c_2455,c_1867,c_1717,c_1448,c_1400,c_1215,c_1062,c_1037,c_958,c_947,c_944,c_937,c_627,c_624,c_621,c_618,c_612,c_15])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.10/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.10/0.12  % Command    : iproveropt_run.sh %d %s
% 0.13/0.33  % Computer   : n012.cluster.edu
% 0.13/0.33  % Model      : x86_64 x86_64
% 0.13/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.33  % Memory     : 8042.1875MB
% 0.13/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.33  % CPULimit   : 60
% 0.13/0.33  % WCLimit    : 600
% 0.13/0.33  % DateTime   : Tue Dec  1 12:14:52 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running in FOF mode
% 2.46/0.99  % SZS status Started for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.46/0.99  
% 2.46/0.99  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 2.46/0.99  
% 2.46/0.99  ------  iProver source info
% 2.46/0.99  
% 2.46/0.99  git: date: 2020-06-30 10:37:57 +0100
% 2.46/0.99  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 2.46/0.99  git: non_committed_changes: false
% 2.46/0.99  git: last_make_outside_of_git: false
% 2.46/0.99  
% 2.46/0.99  ------ 
% 2.46/0.99  
% 2.46/0.99  ------ Input Options
% 2.46/0.99  
% 2.46/0.99  --out_options                           all
% 2.46/0.99  --tptp_safe_out                         true
% 2.46/0.99  --problem_path                          ""
% 2.46/0.99  --include_path                          ""
% 2.46/0.99  --clausifier                            res/vclausify_rel
% 2.46/0.99  --clausifier_options                    --mode clausify
% 2.46/0.99  --stdin                                 false
% 2.46/0.99  --stats_out                             all
% 2.46/0.99  
% 2.46/0.99  ------ General Options
% 2.46/0.99  
% 2.46/0.99  --fof                                   false
% 2.46/0.99  --time_out_real                         305.
% 2.46/0.99  --time_out_virtual                      -1.
% 2.46/0.99  --symbol_type_check                     false
% 2.46/0.99  --clausify_out                          false
% 2.46/0.99  --sig_cnt_out                           false
% 2.46/0.99  --trig_cnt_out                          false
% 2.46/0.99  --trig_cnt_out_tolerance                1.
% 2.46/0.99  --trig_cnt_out_sk_spl                   false
% 2.46/0.99  --abstr_cl_out                          false
% 2.46/0.99  
% 2.46/0.99  ------ Global Options
% 2.46/0.99  
% 2.46/0.99  --schedule                              default
% 2.46/0.99  --add_important_lit                     false
% 2.46/0.99  --prop_solver_per_cl                    1000
% 2.46/0.99  --min_unsat_core                        false
% 2.46/0.99  --soft_assumptions                      false
% 2.46/0.99  --soft_lemma_size                       3
% 2.46/0.99  --prop_impl_unit_size                   0
% 2.46/0.99  --prop_impl_unit                        []
% 2.46/0.99  --share_sel_clauses                     true
% 2.46/0.99  --reset_solvers                         false
% 2.46/0.99  --bc_imp_inh                            [conj_cone]
% 2.46/0.99  --conj_cone_tolerance                   3.
% 2.46/0.99  --extra_neg_conj                        none
% 2.46/0.99  --large_theory_mode                     true
% 2.46/0.99  --prolific_symb_bound                   200
% 2.46/0.99  --lt_threshold                          2000
% 2.46/0.99  --clause_weak_htbl                      true
% 2.46/0.99  --gc_record_bc_elim                     false
% 2.46/0.99  
% 2.46/0.99  ------ Preprocessing Options
% 2.46/0.99  
% 2.46/0.99  --preprocessing_flag                    true
% 2.46/0.99  --time_out_prep_mult                    0.1
% 2.46/0.99  --splitting_mode                        input
% 2.46/0.99  --splitting_grd                         true
% 2.46/0.99  --splitting_cvd                         false
% 2.46/0.99  --splitting_cvd_svl                     false
% 2.46/0.99  --splitting_nvd                         32
% 2.46/0.99  --sub_typing                            true
% 2.46/0.99  --prep_gs_sim                           true
% 2.46/0.99  --prep_unflatten                        true
% 2.46/0.99  --prep_res_sim                          true
% 2.46/0.99  --prep_upred                            true
% 2.46/0.99  --prep_sem_filter                       exhaustive
% 2.46/0.99  --prep_sem_filter_out                   false
% 2.46/0.99  --pred_elim                             true
% 2.46/0.99  --res_sim_input                         true
% 2.46/0.99  --eq_ax_congr_red                       true
% 2.46/0.99  --pure_diseq_elim                       true
% 2.46/0.99  --brand_transform                       false
% 2.46/0.99  --non_eq_to_eq                          false
% 2.46/0.99  --prep_def_merge                        true
% 2.46/0.99  --prep_def_merge_prop_impl              false
% 2.46/0.99  --prep_def_merge_mbd                    true
% 2.46/0.99  --prep_def_merge_tr_red                 false
% 2.46/0.99  --prep_def_merge_tr_cl                  false
% 2.46/0.99  --smt_preprocessing                     true
% 2.46/0.99  --smt_ac_axioms                         fast
% 2.46/0.99  --preprocessed_out                      false
% 2.46/0.99  --preprocessed_stats                    false
% 2.46/0.99  
% 2.46/0.99  ------ Abstraction refinement Options
% 2.46/0.99  
% 2.46/0.99  --abstr_ref                             []
% 2.46/0.99  --abstr_ref_prep                        false
% 2.46/0.99  --abstr_ref_until_sat                   false
% 2.46/0.99  --abstr_ref_sig_restrict                funpre
% 2.46/0.99  --abstr_ref_af_restrict_to_split_sk     false
% 2.46/0.99  --abstr_ref_under                       []
% 2.46/0.99  
% 2.46/0.99  ------ SAT Options
% 2.46/0.99  
% 2.46/0.99  --sat_mode                              false
% 2.46/0.99  --sat_fm_restart_options                ""
% 2.46/0.99  --sat_gr_def                            false
% 2.46/0.99  --sat_epr_types                         true
% 2.46/0.99  --sat_non_cyclic_types                  false
% 2.46/0.99  --sat_finite_models                     false
% 2.46/0.99  --sat_fm_lemmas                         false
% 2.46/0.99  --sat_fm_prep                           false
% 2.46/0.99  --sat_fm_uc_incr                        true
% 2.46/0.99  --sat_out_model                         small
% 2.46/0.99  --sat_out_clauses                       false
% 2.46/0.99  
% 2.46/0.99  ------ QBF Options
% 2.46/0.99  
% 2.46/0.99  --qbf_mode                              false
% 2.46/0.99  --qbf_elim_univ                         false
% 2.46/0.99  --qbf_dom_inst                          none
% 2.46/0.99  --qbf_dom_pre_inst                      false
% 2.46/0.99  --qbf_sk_in                             false
% 2.46/0.99  --qbf_pred_elim                         true
% 2.46/0.99  --qbf_split                             512
% 2.46/0.99  
% 2.46/0.99  ------ BMC1 Options
% 2.46/0.99  
% 2.46/0.99  --bmc1_incremental                      false
% 2.46/0.99  --bmc1_axioms                           reachable_all
% 2.46/0.99  --bmc1_min_bound                        0
% 2.46/0.99  --bmc1_max_bound                        -1
% 2.46/0.99  --bmc1_max_bound_default                -1
% 2.46/0.99  --bmc1_symbol_reachability              true
% 2.46/0.99  --bmc1_property_lemmas                  false
% 2.46/0.99  --bmc1_k_induction                      false
% 2.46/0.99  --bmc1_non_equiv_states                 false
% 2.46/0.99  --bmc1_deadlock                         false
% 2.46/0.99  --bmc1_ucm                              false
% 2.46/0.99  --bmc1_add_unsat_core                   none
% 2.46/0.99  --bmc1_unsat_core_children              false
% 2.46/0.99  --bmc1_unsat_core_extrapolate_axioms    false
% 2.46/0.99  --bmc1_out_stat                         full
% 2.46/0.99  --bmc1_ground_init                      false
% 2.46/0.99  --bmc1_pre_inst_next_state              false
% 2.46/0.99  --bmc1_pre_inst_state                   false
% 2.46/0.99  --bmc1_pre_inst_reach_state             false
% 2.46/0.99  --bmc1_out_unsat_core                   false
% 2.46/0.99  --bmc1_aig_witness_out                  false
% 2.46/0.99  --bmc1_verbose                          false
% 2.46/0.99  --bmc1_dump_clauses_tptp                false
% 2.46/0.99  --bmc1_dump_unsat_core_tptp             false
% 2.46/0.99  --bmc1_dump_file                        -
% 2.46/0.99  --bmc1_ucm_expand_uc_limit              128
% 2.46/0.99  --bmc1_ucm_n_expand_iterations          6
% 2.46/0.99  --bmc1_ucm_extend_mode                  1
% 2.46/0.99  --bmc1_ucm_init_mode                    2
% 2.46/0.99  --bmc1_ucm_cone_mode                    none
% 2.46/0.99  --bmc1_ucm_reduced_relation_type        0
% 2.46/0.99  --bmc1_ucm_relax_model                  4
% 2.46/0.99  --bmc1_ucm_full_tr_after_sat            true
% 2.46/0.99  --bmc1_ucm_expand_neg_assumptions       false
% 2.46/0.99  --bmc1_ucm_layered_model                none
% 2.46/0.99  --bmc1_ucm_max_lemma_size               10
% 2.46/0.99  
% 2.46/0.99  ------ AIG Options
% 2.46/0.99  
% 2.46/0.99  --aig_mode                              false
% 2.46/0.99  
% 2.46/0.99  ------ Instantiation Options
% 2.46/0.99  
% 2.46/0.99  --instantiation_flag                    true
% 2.46/0.99  --inst_sos_flag                         false
% 2.46/0.99  --inst_sos_phase                        true
% 2.46/0.99  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 2.46/0.99  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 2.46/0.99  --inst_lit_sel_side                     num_symb
% 2.46/0.99  --inst_solver_per_active                1400
% 2.46/0.99  --inst_solver_calls_frac                1.
% 2.46/0.99  --inst_passive_queue_type               priority_queues
% 2.46/0.99  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 2.46/0.99  --inst_passive_queues_freq              [25;2]
% 2.46/0.99  --inst_dismatching                      true
% 2.46/0.99  --inst_eager_unprocessed_to_passive     true
% 2.46/0.99  --inst_prop_sim_given                   true
% 2.46/0.99  --inst_prop_sim_new                     false
% 2.46/0.99  --inst_subs_new                         false
% 2.46/0.99  --inst_eq_res_simp                      false
% 2.46/0.99  --inst_subs_given                       false
% 2.46/0.99  --inst_orphan_elimination               true
% 2.46/0.99  --inst_learning_loop_flag               true
% 2.46/0.99  --inst_learning_start                   3000
% 2.46/0.99  --inst_learning_factor                  2
% 2.46/0.99  --inst_start_prop_sim_after_learn       3
% 2.46/0.99  --inst_sel_renew                        solver
% 2.46/0.99  --inst_lit_activity_flag                true
% 2.46/0.99  --inst_restr_to_given                   false
% 2.46/0.99  --inst_activity_threshold               500
% 2.46/0.99  --inst_out_proof                        true
% 2.46/0.99  
% 2.46/0.99  ------ Resolution Options
% 2.46/0.99  
% 2.46/0.99  --resolution_flag                       true
% 2.46/0.99  --res_lit_sel                           adaptive
% 2.46/0.99  --res_lit_sel_side                      none
% 2.46/0.99  --res_ordering                          kbo
% 2.46/0.99  --res_to_prop_solver                    active
% 2.46/0.99  --res_prop_simpl_new                    false
% 2.46/0.99  --res_prop_simpl_given                  true
% 2.46/0.99  --res_passive_queue_type                priority_queues
% 2.46/0.99  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 2.46/0.99  --res_passive_queues_freq               [15;5]
% 2.46/0.99  --res_forward_subs                      full
% 2.46/0.99  --res_backward_subs                     full
% 2.46/0.99  --res_forward_subs_resolution           true
% 2.46/0.99  --res_backward_subs_resolution          true
% 2.46/0.99  --res_orphan_elimination                true
% 2.46/0.99  --res_time_limit                        2.
% 2.46/0.99  --res_out_proof                         true
% 2.46/0.99  
% 2.46/0.99  ------ Superposition Options
% 2.46/0.99  
% 2.46/0.99  --superposition_flag                    true
% 2.46/0.99  --sup_passive_queue_type                priority_queues
% 2.46/0.99  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 2.46/0.99  --sup_passive_queues_freq               [8;1;4]
% 2.46/0.99  --demod_completeness_check              fast
% 2.46/0.99  --demod_use_ground                      true
% 2.46/0.99  --sup_to_prop_solver                    passive
% 2.46/0.99  --sup_prop_simpl_new                    true
% 2.46/0.99  --sup_prop_simpl_given                  true
% 2.46/0.99  --sup_fun_splitting                     false
% 2.46/0.99  --sup_smt_interval                      50000
% 2.46/0.99  
% 2.46/0.99  ------ Superposition Simplification Setup
% 2.46/0.99  
% 2.46/0.99  --sup_indices_passive                   []
% 2.46/0.99  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.46/0.99  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.46/0.99  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.46/0.99  --sup_full_triv                         [TrivRules;PropSubs]
% 2.46/0.99  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.46/0.99  --sup_full_bw                           [BwDemod]
% 2.46/0.99  --sup_immed_triv                        [TrivRules]
% 2.46/0.99  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 2.46/0.99  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.46/0.99  --sup_immed_bw_main                     []
% 2.46/0.99  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.46/0.99  --sup_input_triv                        [Unflattening;TrivRules]
% 2.46/0.99  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.46/0.99  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.46/0.99  
% 2.46/0.99  ------ Combination Options
% 2.46/0.99  
% 2.46/0.99  --comb_res_mult                         3
% 2.46/0.99  --comb_sup_mult                         2
% 2.46/0.99  --comb_inst_mult                        10
% 2.46/0.99  
% 2.46/0.99  ------ Debug Options
% 2.46/0.99  
% 2.46/0.99  --dbg_backtrace                         false
% 2.46/0.99  --dbg_dump_prop_clauses                 false
% 2.46/0.99  --dbg_dump_prop_clauses_file            -
% 2.46/0.99  --dbg_out_stat                          false
% 2.46/0.99  ------ Parsing...
% 2.46/0.99  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 2.46/0.99  
% 2.46/0.99  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe:1:0s pe:2:0s pe_e  sf_s  rm: 1 0s  sf_e  pe_s  pe_e 
% 2.46/0.99  
% 2.46/0.99  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 2.46/0.99  
% 2.46/0.99  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 2.46/0.99  ------ Proving...
% 2.46/0.99  ------ Problem Properties 
% 2.46/0.99  
% 2.46/0.99  
% 2.46/0.99  clauses                                 12
% 2.46/0.99  conjectures                             2
% 2.46/0.99  EPR                                     0
% 2.46/0.99  Horn                                    12
% 2.46/0.99  unary                                   1
% 2.46/0.99  binary                                  10
% 2.46/0.99  lits                                    25
% 2.46/0.99  lits eq                                 7
% 2.46/0.99  fd_pure                                 0
% 2.46/0.99  fd_pseudo                               0
% 2.46/0.99  fd_cond                                 0
% 2.46/0.99  fd_pseudo_cond                          0
% 2.46/0.99  AC symbols                              0
% 2.46/0.99  
% 2.46/0.99  ------ Schedule dynamic 5 is on 
% 2.46/0.99  
% 2.46/0.99  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" Time Limit: 10.
% 2.46/0.99  
% 2.46/0.99  
% 2.46/0.99  ------ 
% 2.46/0.99  Current options:
% 2.46/0.99  ------ 
% 2.46/0.99  
% 2.46/0.99  ------ Input Options
% 2.46/0.99  
% 2.46/0.99  --out_options                           all
% 2.46/0.99  --tptp_safe_out                         true
% 2.46/0.99  --problem_path                          ""
% 2.46/0.99  --include_path                          ""
% 2.46/0.99  --clausifier                            res/vclausify_rel
% 2.46/0.99  --clausifier_options                    --mode clausify
% 2.46/0.99  --stdin                                 false
% 2.46/0.99  --stats_out                             all
% 2.46/0.99  
% 2.46/0.99  ------ General Options
% 2.46/0.99  
% 2.46/0.99  --fof                                   false
% 2.46/0.99  --time_out_real                         305.
% 2.46/0.99  --time_out_virtual                      -1.
% 2.46/0.99  --symbol_type_check                     false
% 2.46/0.99  --clausify_out                          false
% 2.46/0.99  --sig_cnt_out                           false
% 2.46/0.99  --trig_cnt_out                          false
% 2.46/0.99  --trig_cnt_out_tolerance                1.
% 2.46/0.99  --trig_cnt_out_sk_spl                   false
% 2.46/0.99  --abstr_cl_out                          false
% 2.46/0.99  
% 2.46/0.99  ------ Global Options
% 2.46/0.99  
% 2.46/0.99  --schedule                              default
% 2.46/0.99  --add_important_lit                     false
% 2.46/0.99  --prop_solver_per_cl                    1000
% 2.46/0.99  --min_unsat_core                        false
% 2.46/0.99  --soft_assumptions                      false
% 2.46/0.99  --soft_lemma_size                       3
% 2.46/0.99  --prop_impl_unit_size                   0
% 2.46/0.99  --prop_impl_unit                        []
% 2.46/0.99  --share_sel_clauses                     true
% 2.46/0.99  --reset_solvers                         false
% 2.46/0.99  --bc_imp_inh                            [conj_cone]
% 2.46/0.99  --conj_cone_tolerance                   3.
% 2.46/0.99  --extra_neg_conj                        none
% 2.46/0.99  --large_theory_mode                     true
% 2.46/0.99  --prolific_symb_bound                   200
% 2.46/0.99  --lt_threshold                          2000
% 2.46/0.99  --clause_weak_htbl                      true
% 2.46/0.99  --gc_record_bc_elim                     false
% 2.46/0.99  
% 2.46/0.99  ------ Preprocessing Options
% 2.46/0.99  
% 2.46/0.99  --preprocessing_flag                    true
% 2.46/0.99  --time_out_prep_mult                    0.1
% 2.46/0.99  --splitting_mode                        input
% 2.46/0.99  --splitting_grd                         true
% 2.46/0.99  --splitting_cvd                         false
% 2.46/0.99  --splitting_cvd_svl                     false
% 2.46/0.99  --splitting_nvd                         32
% 2.46/0.99  --sub_typing                            true
% 2.46/0.99  --prep_gs_sim                           true
% 2.46/0.99  --prep_unflatten                        true
% 2.46/0.99  --prep_res_sim                          true
% 2.46/0.99  --prep_upred                            true
% 2.46/0.99  --prep_sem_filter                       exhaustive
% 2.46/0.99  --prep_sem_filter_out                   false
% 2.46/0.99  --pred_elim                             true
% 2.46/0.99  --res_sim_input                         true
% 2.46/0.99  --eq_ax_congr_red                       true
% 2.46/0.99  --pure_diseq_elim                       true
% 2.46/0.99  --brand_transform                       false
% 2.46/0.99  --non_eq_to_eq                          false
% 2.46/0.99  --prep_def_merge                        true
% 2.46/0.99  --prep_def_merge_prop_impl              false
% 2.46/0.99  --prep_def_merge_mbd                    true
% 2.46/0.99  --prep_def_merge_tr_red                 false
% 2.46/0.99  --prep_def_merge_tr_cl                  false
% 2.46/0.99  --smt_preprocessing                     true
% 2.46/0.99  --smt_ac_axioms                         fast
% 2.46/0.99  --preprocessed_out                      false
% 2.46/0.99  --preprocessed_stats                    false
% 2.46/0.99  
% 2.46/0.99  ------ Abstraction refinement Options
% 2.46/0.99  
% 2.46/0.99  --abstr_ref                             []
% 2.46/0.99  --abstr_ref_prep                        false
% 2.46/0.99  --abstr_ref_until_sat                   false
% 2.46/0.99  --abstr_ref_sig_restrict                funpre
% 2.46/0.99  --abstr_ref_af_restrict_to_split_sk     false
% 2.46/0.99  --abstr_ref_under                       []
% 2.46/0.99  
% 2.46/0.99  ------ SAT Options
% 2.46/0.99  
% 2.46/0.99  --sat_mode                              false
% 2.46/0.99  --sat_fm_restart_options                ""
% 2.46/0.99  --sat_gr_def                            false
% 2.46/0.99  --sat_epr_types                         true
% 2.46/0.99  --sat_non_cyclic_types                  false
% 2.46/0.99  --sat_finite_models                     false
% 2.46/0.99  --sat_fm_lemmas                         false
% 2.46/0.99  --sat_fm_prep                           false
% 2.46/0.99  --sat_fm_uc_incr                        true
% 2.46/0.99  --sat_out_model                         small
% 2.46/0.99  --sat_out_clauses                       false
% 2.46/0.99  
% 2.46/0.99  ------ QBF Options
% 2.46/0.99  
% 2.46/0.99  --qbf_mode                              false
% 2.46/0.99  --qbf_elim_univ                         false
% 2.46/0.99  --qbf_dom_inst                          none
% 2.46/0.99  --qbf_dom_pre_inst                      false
% 2.46/0.99  --qbf_sk_in                             false
% 2.46/0.99  --qbf_pred_elim                         true
% 2.46/0.99  --qbf_split                             512
% 2.46/0.99  
% 2.46/0.99  ------ BMC1 Options
% 2.46/0.99  
% 2.46/0.99  --bmc1_incremental                      false
% 2.46/0.99  --bmc1_axioms                           reachable_all
% 2.46/0.99  --bmc1_min_bound                        0
% 2.46/0.99  --bmc1_max_bound                        -1
% 2.46/0.99  --bmc1_max_bound_default                -1
% 2.46/0.99  --bmc1_symbol_reachability              true
% 2.46/0.99  --bmc1_property_lemmas                  false
% 2.46/0.99  --bmc1_k_induction                      false
% 2.46/0.99  --bmc1_non_equiv_states                 false
% 2.46/0.99  --bmc1_deadlock                         false
% 2.46/0.99  --bmc1_ucm                              false
% 2.46/0.99  --bmc1_add_unsat_core                   none
% 2.46/0.99  --bmc1_unsat_core_children              false
% 2.46/0.99  --bmc1_unsat_core_extrapolate_axioms    false
% 2.46/0.99  --bmc1_out_stat                         full
% 2.46/0.99  --bmc1_ground_init                      false
% 2.46/0.99  --bmc1_pre_inst_next_state              false
% 2.46/0.99  --bmc1_pre_inst_state                   false
% 2.46/0.99  --bmc1_pre_inst_reach_state             false
% 2.46/0.99  --bmc1_out_unsat_core                   false
% 2.46/0.99  --bmc1_aig_witness_out                  false
% 2.46/0.99  --bmc1_verbose                          false
% 2.46/0.99  --bmc1_dump_clauses_tptp                false
% 2.46/0.99  --bmc1_dump_unsat_core_tptp             false
% 2.46/0.99  --bmc1_dump_file                        -
% 2.46/0.99  --bmc1_ucm_expand_uc_limit              128
% 2.46/0.99  --bmc1_ucm_n_expand_iterations          6
% 2.46/0.99  --bmc1_ucm_extend_mode                  1
% 2.46/0.99  --bmc1_ucm_init_mode                    2
% 2.46/0.99  --bmc1_ucm_cone_mode                    none
% 2.46/0.99  --bmc1_ucm_reduced_relation_type        0
% 2.46/0.99  --bmc1_ucm_relax_model                  4
% 2.46/0.99  --bmc1_ucm_full_tr_after_sat            true
% 2.46/0.99  --bmc1_ucm_expand_neg_assumptions       false
% 2.46/0.99  --bmc1_ucm_layered_model                none
% 2.46/0.99  --bmc1_ucm_max_lemma_size               10
% 2.46/0.99  
% 2.46/0.99  ------ AIG Options
% 2.46/0.99  
% 2.46/0.99  --aig_mode                              false
% 2.46/0.99  
% 2.46/0.99  ------ Instantiation Options
% 2.46/0.99  
% 2.46/0.99  --instantiation_flag                    true
% 2.46/0.99  --inst_sos_flag                         false
% 2.46/0.99  --inst_sos_phase                        true
% 2.46/0.99  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 2.46/0.99  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 2.46/0.99  --inst_lit_sel_side                     none
% 2.46/0.99  --inst_solver_per_active                1400
% 2.46/0.99  --inst_solver_calls_frac                1.
% 2.46/0.99  --inst_passive_queue_type               priority_queues
% 2.46/0.99  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 2.46/0.99  --inst_passive_queues_freq              [25;2]
% 2.46/0.99  --inst_dismatching                      true
% 2.46/0.99  --inst_eager_unprocessed_to_passive     true
% 2.46/0.99  --inst_prop_sim_given                   true
% 2.46/0.99  --inst_prop_sim_new                     false
% 2.46/0.99  --inst_subs_new                         false
% 2.46/0.99  --inst_eq_res_simp                      false
% 2.46/0.99  --inst_subs_given                       false
% 2.46/0.99  --inst_orphan_elimination               true
% 2.46/0.99  --inst_learning_loop_flag               true
% 2.46/0.99  --inst_learning_start                   3000
% 2.46/0.99  --inst_learning_factor                  2
% 2.46/0.99  --inst_start_prop_sim_after_learn       3
% 2.46/0.99  --inst_sel_renew                        solver
% 2.46/0.99  --inst_lit_activity_flag                true
% 2.46/0.99  --inst_restr_to_given                   false
% 2.46/0.99  --inst_activity_threshold               500
% 2.46/0.99  --inst_out_proof                        true
% 2.46/0.99  
% 2.46/0.99  ------ Resolution Options
% 2.46/0.99  
% 2.46/0.99  --resolution_flag                       false
% 2.46/0.99  --res_lit_sel                           adaptive
% 2.46/0.99  --res_lit_sel_side                      none
% 2.46/0.99  --res_ordering                          kbo
% 2.46/0.99  --res_to_prop_solver                    active
% 2.46/0.99  --res_prop_simpl_new                    false
% 2.46/0.99  --res_prop_simpl_given                  true
% 2.46/0.99  --res_passive_queue_type                priority_queues
% 2.46/0.99  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 2.46/0.99  --res_passive_queues_freq               [15;5]
% 2.46/0.99  --res_forward_subs                      full
% 2.46/0.99  --res_backward_subs                     full
% 2.46/0.99  --res_forward_subs_resolution           true
% 2.46/0.99  --res_backward_subs_resolution          true
% 2.46/0.99  --res_orphan_elimination                true
% 2.46/0.99  --res_time_limit                        2.
% 2.46/0.99  --res_out_proof                         true
% 2.46/0.99  
% 2.46/0.99  ------ Superposition Options
% 2.46/0.99  
% 2.46/0.99  --superposition_flag                    true
% 2.46/0.99  --sup_passive_queue_type                priority_queues
% 2.46/0.99  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 2.46/0.99  --sup_passive_queues_freq               [8;1;4]
% 2.46/0.99  --demod_completeness_check              fast
% 2.46/0.99  --demod_use_ground                      true
% 2.46/0.99  --sup_to_prop_solver                    passive
% 2.46/0.99  --sup_prop_simpl_new                    true
% 2.46/0.99  --sup_prop_simpl_given                  true
% 2.46/0.99  --sup_fun_splitting                     false
% 2.46/0.99  --sup_smt_interval                      50000
% 2.46/0.99  
% 2.46/0.99  ------ Superposition Simplification Setup
% 2.46/0.99  
% 2.46/0.99  --sup_indices_passive                   []
% 2.46/0.99  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.46/0.99  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.46/0.99  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.46/0.99  --sup_full_triv                         [TrivRules;PropSubs]
% 2.46/0.99  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.46/0.99  --sup_full_bw                           [BwDemod]
% 2.46/0.99  --sup_immed_triv                        [TrivRules]
% 2.46/0.99  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 2.46/0.99  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.46/0.99  --sup_immed_bw_main                     []
% 2.46/0.99  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.46/0.99  --sup_input_triv                        [Unflattening;TrivRules]
% 2.46/0.99  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.46/0.99  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.46/0.99  
% 2.46/0.99  ------ Combination Options
% 2.46/0.99  
% 2.46/0.99  --comb_res_mult                         3
% 2.46/0.99  --comb_sup_mult                         2
% 2.46/0.99  --comb_inst_mult                        10
% 2.46/0.99  
% 2.46/0.99  ------ Debug Options
% 2.46/0.99  
% 2.46/0.99  --dbg_backtrace                         false
% 2.46/0.99  --dbg_dump_prop_clauses                 false
% 2.46/0.99  --dbg_dump_prop_clauses_file            -
% 2.46/0.99  --dbg_out_stat                          false
% 2.46/0.99  
% 2.46/0.99  
% 2.46/0.99  
% 2.46/0.99  
% 2.46/0.99  ------ Proving...
% 2.46/0.99  
% 2.46/0.99  
% 2.46/0.99  % SZS status Theorem for theBenchmark.p
% 2.46/0.99  
% 2.46/0.99  % SZS output start CNFRefutation for theBenchmark.p
% 2.46/0.99  
% 2.46/0.99  fof(f11,conjecture,(
% 2.46/0.99    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => (k1_relset_1(X0,X1,X2) = k2_relset_1(X1,X0,k3_relset_1(X0,X1,X2)) & k1_relset_1(X1,X0,k3_relset_1(X0,X1,X2)) = k2_relset_1(X0,X1,X2)))),
% 2.46/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.46/0.99  
% 2.46/0.99  fof(f12,negated_conjecture,(
% 2.46/0.99    ~! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => (k1_relset_1(X0,X1,X2) = k2_relset_1(X1,X0,k3_relset_1(X0,X1,X2)) & k1_relset_1(X1,X0,k3_relset_1(X0,X1,X2)) = k2_relset_1(X0,X1,X2)))),
% 2.46/0.99    inference(negated_conjecture,[],[f11])).
% 2.46/0.99  
% 2.46/0.99  fof(f24,plain,(
% 2.46/0.99    ? [X0,X1,X2] : ((k1_relset_1(X0,X1,X2) != k2_relset_1(X1,X0,k3_relset_1(X0,X1,X2)) | k1_relset_1(X1,X0,k3_relset_1(X0,X1,X2)) != k2_relset_1(X0,X1,X2)) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 2.46/0.99    inference(ennf_transformation,[],[f12])).
% 2.46/0.99  
% 2.46/0.99  fof(f27,plain,(
% 2.46/0.99    ? [X0,X1,X2] : ((k1_relset_1(X0,X1,X2) != k2_relset_1(X1,X0,k3_relset_1(X0,X1,X2)) | k1_relset_1(X1,X0,k3_relset_1(X0,X1,X2)) != k2_relset_1(X0,X1,X2)) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) => ((k1_relset_1(sK0,sK1,sK2) != k2_relset_1(sK1,sK0,k3_relset_1(sK0,sK1,sK2)) | k1_relset_1(sK1,sK0,k3_relset_1(sK0,sK1,sK2)) != k2_relset_1(sK0,sK1,sK2)) & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))))),
% 2.46/0.99    introduced(choice_axiom,[])).
% 2.46/0.99  
% 2.46/0.99  fof(f28,plain,(
% 2.46/0.99    (k1_relset_1(sK0,sK1,sK2) != k2_relset_1(sK1,sK0,k3_relset_1(sK0,sK1,sK2)) | k1_relset_1(sK1,sK0,k3_relset_1(sK0,sK1,sK2)) != k2_relset_1(sK0,sK1,sK2)) & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))),
% 2.46/0.99    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f24,f27])).
% 2.46/0.99  
% 2.46/0.99  fof(f43,plain,(
% 2.46/0.99    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))),
% 2.46/0.99    inference(cnf_transformation,[],[f28])).
% 2.46/0.99  
% 2.46/0.99  fof(f2,axiom,(
% 2.46/0.99    ! [X0,X1] : (v1_relat_1(X1) => (v5_relat_1(X1,X0) <=> r1_tarski(k2_relat_1(X1),X0)))),
% 2.46/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.46/0.99  
% 2.46/0.99  fof(f14,plain,(
% 2.46/0.99    ! [X0,X1] : ((v5_relat_1(X1,X0) <=> r1_tarski(k2_relat_1(X1),X0)) | ~v1_relat_1(X1))),
% 2.46/0.99    inference(ennf_transformation,[],[f2])).
% 2.46/0.99  
% 2.46/0.99  fof(f26,plain,(
% 2.46/0.99    ! [X0,X1] : (((v5_relat_1(X1,X0) | ~r1_tarski(k2_relat_1(X1),X0)) & (r1_tarski(k2_relat_1(X1),X0) | ~v5_relat_1(X1,X0))) | ~v1_relat_1(X1))),
% 2.46/0.99    inference(nnf_transformation,[],[f14])).
% 2.46/0.99  
% 2.46/0.99  fof(f31,plain,(
% 2.46/0.99    ( ! [X0,X1] : (r1_tarski(k2_relat_1(X1),X0) | ~v5_relat_1(X1,X0) | ~v1_relat_1(X1)) )),
% 2.46/0.99    inference(cnf_transformation,[],[f26])).
% 2.46/0.99  
% 2.46/0.99  fof(f6,axiom,(
% 2.46/0.99    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => (v5_relat_1(X2,X1) & v4_relat_1(X2,X0)))),
% 2.46/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.46/0.99  
% 2.46/0.99  fof(f18,plain,(
% 2.46/0.99    ! [X0,X1,X2] : ((v5_relat_1(X2,X1) & v4_relat_1(X2,X0)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 2.46/0.99    inference(ennf_transformation,[],[f6])).
% 2.46/0.99  
% 2.46/0.99  fof(f38,plain,(
% 2.46/0.99    ( ! [X2,X0,X1] : (v5_relat_1(X2,X1) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 2.46/0.99    inference(cnf_transformation,[],[f18])).
% 2.46/0.99  
% 2.46/0.99  fof(f5,axiom,(
% 2.46/0.99    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => v1_relat_1(X2))),
% 2.46/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.46/0.99  
% 2.46/0.99  fof(f17,plain,(
% 2.46/1.00    ! [X0,X1,X2] : (v1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 2.46/1.00    inference(ennf_transformation,[],[f5])).
% 2.46/1.00  
% 2.46/1.00  fof(f36,plain,(
% 2.46/1.00    ( ! [X2,X0,X1] : (v1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 2.46/1.00    inference(cnf_transformation,[],[f17])).
% 2.46/1.00  
% 2.46/1.00  fof(f37,plain,(
% 2.46/1.00    ( ! [X2,X0,X1] : (v4_relat_1(X2,X0) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 2.46/1.00    inference(cnf_transformation,[],[f18])).
% 2.46/1.00  
% 2.46/1.00  fof(f1,axiom,(
% 2.46/1.00    ! [X0,X1] : (v1_relat_1(X1) => (v4_relat_1(X1,X0) <=> r1_tarski(k1_relat_1(X1),X0)))),
% 2.46/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.46/1.00  
% 2.46/1.00  fof(f13,plain,(
% 2.46/1.00    ! [X0,X1] : ((v4_relat_1(X1,X0) <=> r1_tarski(k1_relat_1(X1),X0)) | ~v1_relat_1(X1))),
% 2.46/1.00    inference(ennf_transformation,[],[f1])).
% 2.46/1.00  
% 2.46/1.00  fof(f25,plain,(
% 2.46/1.00    ! [X0,X1] : (((v4_relat_1(X1,X0) | ~r1_tarski(k1_relat_1(X1),X0)) & (r1_tarski(k1_relat_1(X1),X0) | ~v4_relat_1(X1,X0))) | ~v1_relat_1(X1))),
% 2.46/1.00    inference(nnf_transformation,[],[f13])).
% 2.46/1.00  
% 2.46/1.00  fof(f29,plain,(
% 2.46/1.00    ( ! [X0,X1] : (r1_tarski(k1_relat_1(X1),X0) | ~v4_relat_1(X1,X0) | ~v1_relat_1(X1)) )),
% 2.46/1.00    inference(cnf_transformation,[],[f25])).
% 2.46/1.00  
% 2.46/1.00  fof(f4,axiom,(
% 2.46/1.00    ! [X0] : (v1_relat_1(X0) => (k1_relat_1(X0) = k2_relat_1(k4_relat_1(X0)) & k1_relat_1(k4_relat_1(X0)) = k2_relat_1(X0)))),
% 2.46/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.46/1.00  
% 2.46/1.00  fof(f16,plain,(
% 2.46/1.00    ! [X0] : ((k1_relat_1(X0) = k2_relat_1(k4_relat_1(X0)) & k1_relat_1(k4_relat_1(X0)) = k2_relat_1(X0)) | ~v1_relat_1(X0))),
% 2.46/1.00    inference(ennf_transformation,[],[f4])).
% 2.46/1.00  
% 2.46/1.00  fof(f35,plain,(
% 2.46/1.00    ( ! [X0] : (k1_relat_1(X0) = k2_relat_1(k4_relat_1(X0)) | ~v1_relat_1(X0)) )),
% 2.46/1.00    inference(cnf_transformation,[],[f16])).
% 2.46/1.00  
% 2.46/1.00  fof(f10,axiom,(
% 2.46/1.00    ! [X0,X1,X2] : (v1_relat_1(X2) => ((r1_tarski(k2_relat_1(X2),X1) & r1_tarski(k1_relat_1(X2),X0)) => m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))))),
% 2.46/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.46/1.00  
% 2.46/1.00  fof(f22,plain,(
% 2.46/1.00    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | (~r1_tarski(k2_relat_1(X2),X1) | ~r1_tarski(k1_relat_1(X2),X0))) | ~v1_relat_1(X2))),
% 2.46/1.00    inference(ennf_transformation,[],[f10])).
% 2.46/1.00  
% 2.46/1.00  fof(f23,plain,(
% 2.46/1.00    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~r1_tarski(k2_relat_1(X2),X1) | ~r1_tarski(k1_relat_1(X2),X0) | ~v1_relat_1(X2))),
% 2.46/1.00    inference(flattening,[],[f22])).
% 2.46/1.00  
% 2.46/1.00  fof(f42,plain,(
% 2.46/1.00    ( ! [X2,X0,X1] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~r1_tarski(k2_relat_1(X2),X1) | ~r1_tarski(k1_relat_1(X2),X0) | ~v1_relat_1(X2)) )),
% 2.46/1.00    inference(cnf_transformation,[],[f23])).
% 2.46/1.00  
% 2.46/1.00  fof(f8,axiom,(
% 2.46/1.00    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k2_relat_1(X2) = k2_relset_1(X0,X1,X2))),
% 2.46/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.46/1.00  
% 2.46/1.00  fof(f20,plain,(
% 2.46/1.00    ! [X0,X1,X2] : (k2_relat_1(X2) = k2_relset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 2.46/1.00    inference(ennf_transformation,[],[f8])).
% 2.46/1.00  
% 2.46/1.00  fof(f40,plain,(
% 2.46/1.00    ( ! [X2,X0,X1] : (k2_relat_1(X2) = k2_relset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 2.46/1.00    inference(cnf_transformation,[],[f20])).
% 2.46/1.00  
% 2.46/1.00  fof(f34,plain,(
% 2.46/1.00    ( ! [X0] : (k1_relat_1(k4_relat_1(X0)) = k2_relat_1(X0) | ~v1_relat_1(X0)) )),
% 2.46/1.00    inference(cnf_transformation,[],[f16])).
% 2.46/1.00  
% 2.46/1.00  fof(f3,axiom,(
% 2.46/1.00    ! [X0] : (v1_relat_1(X0) => v1_relat_1(k4_relat_1(X0)))),
% 2.46/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.46/1.00  
% 2.46/1.00  fof(f15,plain,(
% 2.46/1.00    ! [X0] : (v1_relat_1(k4_relat_1(X0)) | ~v1_relat_1(X0))),
% 2.46/1.00    inference(ennf_transformation,[],[f3])).
% 2.46/1.00  
% 2.46/1.00  fof(f33,plain,(
% 2.46/1.00    ( ! [X0] : (v1_relat_1(k4_relat_1(X0)) | ~v1_relat_1(X0)) )),
% 2.46/1.00    inference(cnf_transformation,[],[f15])).
% 2.46/1.00  
% 2.46/1.00  fof(f7,axiom,(
% 2.46/1.00    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k1_relat_1(X2) = k1_relset_1(X0,X1,X2))),
% 2.46/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.46/1.00  
% 2.46/1.00  fof(f19,plain,(
% 2.46/1.00    ! [X0,X1,X2] : (k1_relat_1(X2) = k1_relset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 2.46/1.00    inference(ennf_transformation,[],[f7])).
% 2.46/1.00  
% 2.46/1.00  fof(f39,plain,(
% 2.46/1.00    ( ! [X2,X0,X1] : (k1_relat_1(X2) = k1_relset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 2.46/1.00    inference(cnf_transformation,[],[f19])).
% 2.46/1.00  
% 2.46/1.00  fof(f44,plain,(
% 2.46/1.00    k1_relset_1(sK0,sK1,sK2) != k2_relset_1(sK1,sK0,k3_relset_1(sK0,sK1,sK2)) | k1_relset_1(sK1,sK0,k3_relset_1(sK0,sK1,sK2)) != k2_relset_1(sK0,sK1,sK2)),
% 2.46/1.00    inference(cnf_transformation,[],[f28])).
% 2.46/1.00  
% 2.46/1.00  fof(f9,axiom,(
% 2.46/1.00    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k4_relat_1(X2) = k3_relset_1(X0,X1,X2))),
% 2.46/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.46/1.00  
% 2.46/1.00  fof(f21,plain,(
% 2.46/1.00    ! [X0,X1,X2] : (k4_relat_1(X2) = k3_relset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 2.46/1.00    inference(ennf_transformation,[],[f9])).
% 2.46/1.00  
% 2.46/1.00  fof(f41,plain,(
% 2.46/1.00    ( ! [X2,X0,X1] : (k4_relat_1(X2) = k3_relset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 2.46/1.00    inference(cnf_transformation,[],[f21])).
% 2.46/1.00  
% 2.46/1.00  cnf(c_15,negated_conjecture,
% 2.46/1.00      ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ),
% 2.46/1.00      inference(cnf_transformation,[],[f43]) ).
% 2.46/1.00  
% 2.46/1.00  cnf(c_586,negated_conjecture,
% 2.46/1.00      ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ),
% 2.46/1.00      inference(subtyping,[status(esa)],[c_15]) ).
% 2.46/1.00  
% 2.46/1.00  cnf(c_859,plain,
% 2.46/1.00      ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) = iProver_top ),
% 2.46/1.00      inference(predicate_to_equality,[status(thm)],[c_586]) ).
% 2.46/1.00  
% 2.46/1.00  cnf(c_3,plain,
% 2.46/1.00      ( ~ v5_relat_1(X0,X1)
% 2.46/1.00      | r1_tarski(k2_relat_1(X0),X1)
% 2.46/1.00      | ~ v1_relat_1(X0) ),
% 2.46/1.00      inference(cnf_transformation,[],[f31]) ).
% 2.46/1.00  
% 2.46/1.00  cnf(c_8,plain,
% 2.46/1.00      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 2.46/1.00      | v5_relat_1(X0,X2) ),
% 2.46/1.00      inference(cnf_transformation,[],[f38]) ).
% 2.46/1.00  
% 2.46/1.00  cnf(c_208,plain,
% 2.46/1.00      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 2.46/1.00      | r1_tarski(k2_relat_1(X3),X4)
% 2.46/1.00      | ~ v1_relat_1(X3)
% 2.46/1.00      | X0 != X3
% 2.46/1.00      | X2 != X4 ),
% 2.46/1.00      inference(resolution_lifted,[status(thm)],[c_3,c_8]) ).
% 2.46/1.00  
% 2.46/1.00  cnf(c_209,plain,
% 2.46/1.00      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 2.46/1.00      | r1_tarski(k2_relat_1(X0),X2)
% 2.46/1.00      | ~ v1_relat_1(X0) ),
% 2.46/1.00      inference(unflattening,[status(thm)],[c_208]) ).
% 2.46/1.00  
% 2.46/1.00  cnf(c_7,plain,
% 2.46/1.00      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 2.46/1.00      | v1_relat_1(X0) ),
% 2.46/1.00      inference(cnf_transformation,[],[f36]) ).
% 2.46/1.00  
% 2.46/1.00  cnf(c_213,plain,
% 2.46/1.00      ( r1_tarski(k2_relat_1(X0),X2)
% 2.46/1.00      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) ),
% 2.46/1.00      inference(global_propositional_subsumption,
% 2.46/1.00                [status(thm)],
% 2.46/1.00                [c_209,c_7]) ).
% 2.46/1.00  
% 2.46/1.00  cnf(c_214,plain,
% 2.46/1.00      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 2.46/1.00      | r1_tarski(k2_relat_1(X0),X2) ),
% 2.46/1.00      inference(renaming,[status(thm)],[c_213]) ).
% 2.46/1.00  
% 2.46/1.00  cnf(c_584,plain,
% 2.46/1.00      ( ~ m1_subset_1(X0_44,k1_zfmisc_1(k2_zfmisc_1(X0_47,X1_47)))
% 2.46/1.00      | r1_tarski(k2_relat_1(X0_44),X1_47) ),
% 2.46/1.00      inference(subtyping,[status(esa)],[c_214]) ).
% 2.46/1.00  
% 2.46/1.00  cnf(c_861,plain,
% 2.46/1.00      ( m1_subset_1(X0_44,k1_zfmisc_1(k2_zfmisc_1(X0_47,X1_47))) != iProver_top
% 2.46/1.00      | r1_tarski(k2_relat_1(X0_44),X1_47) = iProver_top ),
% 2.46/1.00      inference(predicate_to_equality,[status(thm)],[c_584]) ).
% 2.46/1.00  
% 2.46/1.00  cnf(c_2060,plain,
% 2.46/1.00      ( r1_tarski(k2_relat_1(sK2),sK1) = iProver_top ),
% 2.46/1.00      inference(superposition,[status(thm)],[c_859,c_861]) ).
% 2.46/1.00  
% 2.46/1.00  cnf(c_9,plain,
% 2.46/1.00      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 2.46/1.00      | v4_relat_1(X0,X1) ),
% 2.46/1.00      inference(cnf_transformation,[],[f37]) ).
% 2.46/1.00  
% 2.46/1.00  cnf(c_1,plain,
% 2.46/1.00      ( r1_tarski(k1_relat_1(X0),X1)
% 2.46/1.00      | ~ v4_relat_1(X0,X1)
% 2.46/1.00      | ~ v1_relat_1(X0) ),
% 2.46/1.00      inference(cnf_transformation,[],[f29]) ).
% 2.46/1.00  
% 2.46/1.00  cnf(c_186,plain,
% 2.46/1.00      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 2.46/1.00      | r1_tarski(k1_relat_1(X0),X1)
% 2.46/1.00      | ~ v1_relat_1(X0) ),
% 2.46/1.00      inference(resolution,[status(thm)],[c_9,c_1]) ).
% 2.46/1.00  
% 2.46/1.00  cnf(c_190,plain,
% 2.46/1.00      ( r1_tarski(k1_relat_1(X0),X1)
% 2.46/1.00      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) ),
% 2.46/1.00      inference(global_propositional_subsumption,
% 2.46/1.00                [status(thm)],
% 2.46/1.00                [c_186,c_7]) ).
% 2.46/1.00  
% 2.46/1.00  cnf(c_191,plain,
% 2.46/1.00      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 2.46/1.00      | r1_tarski(k1_relat_1(X0),X1) ),
% 2.46/1.00      inference(renaming,[status(thm)],[c_190]) ).
% 2.46/1.00  
% 2.46/1.00  cnf(c_585,plain,
% 2.46/1.00      ( ~ m1_subset_1(X0_44,k1_zfmisc_1(k2_zfmisc_1(X0_47,X1_47)))
% 2.46/1.00      | r1_tarski(k1_relat_1(X0_44),X0_47) ),
% 2.46/1.00      inference(subtyping,[status(esa)],[c_191]) ).
% 2.46/1.00  
% 2.46/1.00  cnf(c_860,plain,
% 2.46/1.00      ( m1_subset_1(X0_44,k1_zfmisc_1(k2_zfmisc_1(X0_47,X1_47))) != iProver_top
% 2.46/1.00      | r1_tarski(k1_relat_1(X0_44),X0_47) = iProver_top ),
% 2.46/1.00      inference(predicate_to_equality,[status(thm)],[c_585]) ).
% 2.46/1.00  
% 2.46/1.00  cnf(c_1605,plain,
% 2.46/1.00      ( r1_tarski(k1_relat_1(sK2),sK0) = iProver_top ),
% 2.46/1.00      inference(superposition,[status(thm)],[c_859,c_860]) ).
% 2.46/1.00  
% 2.46/1.00  cnf(c_592,plain,
% 2.46/1.00      ( ~ m1_subset_1(X0_44,k1_zfmisc_1(k2_zfmisc_1(X0_47,X1_47)))
% 2.46/1.00      | v1_relat_1(X0_44) ),
% 2.46/1.00      inference(subtyping,[status(esa)],[c_7]) ).
% 2.46/1.00  
% 2.46/1.00  cnf(c_854,plain,
% 2.46/1.00      ( m1_subset_1(X0_44,k1_zfmisc_1(k2_zfmisc_1(X0_47,X1_47))) != iProver_top
% 2.46/1.00      | v1_relat_1(X0_44) = iProver_top ),
% 2.46/1.00      inference(predicate_to_equality,[status(thm)],[c_592]) ).
% 2.46/1.00  
% 2.46/1.00  cnf(c_994,plain,
% 2.46/1.00      ( v1_relat_1(sK2) = iProver_top ),
% 2.46/1.00      inference(superposition,[status(thm)],[c_859,c_854]) ).
% 2.46/1.00  
% 2.46/1.00  cnf(c_5,plain,
% 2.46/1.00      ( ~ v1_relat_1(X0) | k2_relat_1(k4_relat_1(X0)) = k1_relat_1(X0) ),
% 2.46/1.00      inference(cnf_transformation,[],[f35]) ).
% 2.46/1.00  
% 2.46/1.00  cnf(c_594,plain,
% 2.46/1.00      ( ~ v1_relat_1(X0_44)
% 2.46/1.00      | k2_relat_1(k4_relat_1(X0_44)) = k1_relat_1(X0_44) ),
% 2.46/1.00      inference(subtyping,[status(esa)],[c_5]) ).
% 2.46/1.00  
% 2.46/1.00  cnf(c_852,plain,
% 2.46/1.00      ( k2_relat_1(k4_relat_1(X0_44)) = k1_relat_1(X0_44)
% 2.46/1.00      | v1_relat_1(X0_44) != iProver_top ),
% 2.46/1.00      inference(predicate_to_equality,[status(thm)],[c_594]) ).
% 2.46/1.00  
% 2.46/1.00  cnf(c_1031,plain,
% 2.46/1.00      ( k2_relat_1(k4_relat_1(sK2)) = k1_relat_1(sK2) ),
% 2.46/1.00      inference(superposition,[status(thm)],[c_994,c_852]) ).
% 2.46/1.00  
% 2.46/1.00  cnf(c_13,plain,
% 2.46/1.00      ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 2.46/1.00      | ~ r1_tarski(k2_relat_1(X0),X2)
% 2.46/1.00      | ~ r1_tarski(k1_relat_1(X0),X1)
% 2.46/1.00      | ~ v1_relat_1(X0) ),
% 2.46/1.00      inference(cnf_transformation,[],[f42]) ).
% 2.46/1.00  
% 2.46/1.00  cnf(c_588,plain,
% 2.46/1.00      ( m1_subset_1(X0_44,k1_zfmisc_1(k2_zfmisc_1(X0_47,X1_47)))
% 2.46/1.00      | ~ r1_tarski(k2_relat_1(X0_44),X1_47)
% 2.46/1.00      | ~ r1_tarski(k1_relat_1(X0_44),X0_47)
% 2.46/1.00      | ~ v1_relat_1(X0_44) ),
% 2.46/1.00      inference(subtyping,[status(esa)],[c_13]) ).
% 2.46/1.00  
% 2.46/1.00  cnf(c_858,plain,
% 2.46/1.00      ( m1_subset_1(X0_44,k1_zfmisc_1(k2_zfmisc_1(X0_47,X1_47))) = iProver_top
% 2.46/1.00      | r1_tarski(k2_relat_1(X0_44),X1_47) != iProver_top
% 2.46/1.00      | r1_tarski(k1_relat_1(X0_44),X0_47) != iProver_top
% 2.46/1.00      | v1_relat_1(X0_44) != iProver_top ),
% 2.46/1.00      inference(predicate_to_equality,[status(thm)],[c_588]) ).
% 2.46/1.00  
% 2.46/1.00  cnf(c_11,plain,
% 2.46/1.00      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 2.46/1.00      | k2_relset_1(X1,X2,X0) = k2_relat_1(X0) ),
% 2.46/1.00      inference(cnf_transformation,[],[f40]) ).
% 2.46/1.00  
% 2.46/1.00  cnf(c_590,plain,
% 2.46/1.00      ( ~ m1_subset_1(X0_44,k1_zfmisc_1(k2_zfmisc_1(X0_47,X1_47)))
% 2.46/1.00      | k2_relset_1(X0_47,X1_47,X0_44) = k2_relat_1(X0_44) ),
% 2.46/1.00      inference(subtyping,[status(esa)],[c_11]) ).
% 2.46/1.00  
% 2.46/1.00  cnf(c_856,plain,
% 2.46/1.00      ( k2_relset_1(X0_47,X1_47,X0_44) = k2_relat_1(X0_44)
% 2.46/1.00      | m1_subset_1(X0_44,k1_zfmisc_1(k2_zfmisc_1(X0_47,X1_47))) != iProver_top ),
% 2.46/1.00      inference(predicate_to_equality,[status(thm)],[c_590]) ).
% 2.46/1.00  
% 2.46/1.00  cnf(c_1168,plain,
% 2.46/1.00      ( k2_relset_1(X0_47,X1_47,X0_44) = k2_relat_1(X0_44)
% 2.46/1.00      | r1_tarski(k2_relat_1(X0_44),X1_47) != iProver_top
% 2.46/1.00      | r1_tarski(k1_relat_1(X0_44),X0_47) != iProver_top
% 2.46/1.00      | v1_relat_1(X0_44) != iProver_top ),
% 2.46/1.00      inference(superposition,[status(thm)],[c_858,c_856]) ).
% 2.46/1.00  
% 2.46/1.00  cnf(c_2981,plain,
% 2.46/1.00      ( k2_relset_1(X0_47,X1_47,k4_relat_1(sK2)) = k2_relat_1(k4_relat_1(sK2))
% 2.46/1.00      | r1_tarski(k1_relat_1(k4_relat_1(sK2)),X0_47) != iProver_top
% 2.46/1.00      | r1_tarski(k1_relat_1(sK2),X1_47) != iProver_top
% 2.46/1.00      | v1_relat_1(k4_relat_1(sK2)) != iProver_top ),
% 2.46/1.00      inference(superposition,[status(thm)],[c_1031,c_1168]) ).
% 2.46/1.00  
% 2.46/1.00  cnf(c_6,plain,
% 2.46/1.00      ( ~ v1_relat_1(X0) | k1_relat_1(k4_relat_1(X0)) = k2_relat_1(X0) ),
% 2.46/1.00      inference(cnf_transformation,[],[f34]) ).
% 2.46/1.00  
% 2.46/1.00  cnf(c_593,plain,
% 2.46/1.00      ( ~ v1_relat_1(X0_44)
% 2.46/1.00      | k1_relat_1(k4_relat_1(X0_44)) = k2_relat_1(X0_44) ),
% 2.46/1.00      inference(subtyping,[status(esa)],[c_6]) ).
% 2.46/1.00  
% 2.46/1.00  cnf(c_853,plain,
% 2.46/1.00      ( k1_relat_1(k4_relat_1(X0_44)) = k2_relat_1(X0_44)
% 2.46/1.00      | v1_relat_1(X0_44) != iProver_top ),
% 2.46/1.00      inference(predicate_to_equality,[status(thm)],[c_593]) ).
% 2.46/1.00  
% 2.46/1.00  cnf(c_1030,plain,
% 2.46/1.00      ( k1_relat_1(k4_relat_1(sK2)) = k2_relat_1(sK2) ),
% 2.46/1.00      inference(superposition,[status(thm)],[c_994,c_853]) ).
% 2.46/1.00  
% 2.46/1.00  cnf(c_3036,plain,
% 2.46/1.00      ( k2_relset_1(X0_47,X1_47,k4_relat_1(sK2)) = k1_relat_1(sK2)
% 2.46/1.00      | r1_tarski(k2_relat_1(sK2),X0_47) != iProver_top
% 2.46/1.00      | r1_tarski(k1_relat_1(sK2),X1_47) != iProver_top
% 2.46/1.00      | v1_relat_1(k4_relat_1(sK2)) != iProver_top ),
% 2.46/1.00      inference(light_normalisation,[status(thm)],[c_2981,c_1030,c_1031]) ).
% 2.46/1.00  
% 2.46/1.00  cnf(c_16,plain,
% 2.46/1.00      ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) = iProver_top ),
% 2.46/1.00      inference(predicate_to_equality,[status(thm)],[c_15]) ).
% 2.46/1.00  
% 2.46/1.00  cnf(c_4,plain,
% 2.46/1.00      ( ~ v1_relat_1(X0) | v1_relat_1(k4_relat_1(X0)) ),
% 2.46/1.00      inference(cnf_transformation,[],[f33]) ).
% 2.46/1.00  
% 2.46/1.00  cnf(c_595,plain,
% 2.46/1.00      ( ~ v1_relat_1(X0_44) | v1_relat_1(k4_relat_1(X0_44)) ),
% 2.46/1.00      inference(subtyping,[status(esa)],[c_4]) ).
% 2.46/1.00  
% 2.46/1.00  cnf(c_620,plain,
% 2.46/1.00      ( v1_relat_1(X0_44) != iProver_top
% 2.46/1.00      | v1_relat_1(k4_relat_1(X0_44)) = iProver_top ),
% 2.46/1.00      inference(predicate_to_equality,[status(thm)],[c_595]) ).
% 2.46/1.00  
% 2.46/1.00  cnf(c_622,plain,
% 2.46/1.00      ( v1_relat_1(k4_relat_1(sK2)) = iProver_top
% 2.46/1.00      | v1_relat_1(sK2) != iProver_top ),
% 2.46/1.00      inference(instantiation,[status(thm)],[c_620]) ).
% 2.46/1.00  
% 2.46/1.00  cnf(c_937,plain,
% 2.46/1.00      ( ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
% 2.46/1.00      | v1_relat_1(sK2) ),
% 2.46/1.00      inference(instantiation,[status(thm)],[c_592]) ).
% 2.46/1.00  
% 2.46/1.00  cnf(c_938,plain,
% 2.46/1.00      ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) != iProver_top
% 2.46/1.00      | v1_relat_1(sK2) = iProver_top ),
% 2.46/1.00      inference(predicate_to_equality,[status(thm)],[c_937]) ).
% 2.46/1.00  
% 2.46/1.00  cnf(c_6034,plain,
% 2.46/1.00      ( r1_tarski(k1_relat_1(sK2),X1_47) != iProver_top
% 2.46/1.00      | r1_tarski(k2_relat_1(sK2),X0_47) != iProver_top
% 2.46/1.00      | k2_relset_1(X0_47,X1_47,k4_relat_1(sK2)) = k1_relat_1(sK2) ),
% 2.46/1.00      inference(global_propositional_subsumption,
% 2.46/1.00                [status(thm)],
% 2.46/1.00                [c_3036,c_16,c_622,c_938]) ).
% 2.46/1.00  
% 2.46/1.00  cnf(c_6035,plain,
% 2.46/1.00      ( k2_relset_1(X0_47,X1_47,k4_relat_1(sK2)) = k1_relat_1(sK2)
% 2.46/1.00      | r1_tarski(k2_relat_1(sK2),X0_47) != iProver_top
% 2.46/1.00      | r1_tarski(k1_relat_1(sK2),X1_47) != iProver_top ),
% 2.46/1.00      inference(renaming,[status(thm)],[c_6034]) ).
% 2.46/1.00  
% 2.46/1.00  cnf(c_6043,plain,
% 2.46/1.00      ( k2_relset_1(X0_47,sK0,k4_relat_1(sK2)) = k1_relat_1(sK2)
% 2.46/1.00      | r1_tarski(k2_relat_1(sK2),X0_47) != iProver_top ),
% 2.46/1.00      inference(superposition,[status(thm)],[c_1605,c_6035]) ).
% 2.46/1.00  
% 2.46/1.00  cnf(c_6119,plain,
% 2.46/1.00      ( k2_relset_1(sK1,sK0,k4_relat_1(sK2)) = k1_relat_1(sK2) ),
% 2.46/1.00      inference(superposition,[status(thm)],[c_2060,c_6043]) ).
% 2.46/1.00  
% 2.46/1.00  cnf(c_600,plain,
% 2.46/1.00      ( X0_48 != X1_48 | X2_48 != X1_48 | X2_48 = X0_48 ),
% 2.46/1.00      theory(equality) ).
% 2.46/1.00  
% 2.46/1.00  cnf(c_1298,plain,
% 2.46/1.00      ( X0_48 != X1_48
% 2.46/1.00      | X0_48 = k2_relat_1(X0_44)
% 2.46/1.00      | k2_relat_1(X0_44) != X1_48 ),
% 2.46/1.00      inference(instantiation,[status(thm)],[c_600]) ).
% 2.46/1.00  
% 2.46/1.00  cnf(c_1938,plain,
% 2.46/1.00      ( X0_48 != k2_relset_1(sK0,sK1,sK2)
% 2.46/1.00      | X0_48 = k2_relat_1(X0_44)
% 2.46/1.00      | k2_relat_1(X0_44) != k2_relset_1(sK0,sK1,sK2) ),
% 2.46/1.00      inference(instantiation,[status(thm)],[c_1298]) ).
% 2.46/1.00  
% 2.46/1.00  cnf(c_4984,plain,
% 2.46/1.00      ( k1_relset_1(sK1,sK0,k4_relat_1(sK2)) != k2_relset_1(sK0,sK1,sK2)
% 2.46/1.00      | k1_relset_1(sK1,sK0,k4_relat_1(sK2)) = k2_relat_1(X0_44)
% 2.46/1.00      | k2_relat_1(X0_44) != k2_relset_1(sK0,sK1,sK2) ),
% 2.46/1.00      inference(instantiation,[status(thm)],[c_1938]) ).
% 2.46/1.00  
% 2.46/1.00  cnf(c_4992,plain,
% 2.46/1.00      ( k1_relset_1(sK1,sK0,k4_relat_1(sK2)) != k2_relset_1(sK0,sK1,sK2)
% 2.46/1.00      | k1_relset_1(sK1,sK0,k4_relat_1(sK2)) = k2_relat_1(sK2)
% 2.46/1.00      | k2_relat_1(sK2) != k2_relset_1(sK0,sK1,sK2) ),
% 2.46/1.00      inference(instantiation,[status(thm)],[c_4984]) ).
% 2.46/1.00  
% 2.46/1.00  cnf(c_1235,plain,
% 2.46/1.00      ( X0_48 != X1_48
% 2.46/1.00      | X0_48 = k2_relset_1(sK0,sK1,sK2)
% 2.46/1.00      | k2_relset_1(sK0,sK1,sK2) != X1_48 ),
% 2.46/1.00      inference(instantiation,[status(thm)],[c_600]) ).
% 2.46/1.00  
% 2.46/1.00  cnf(c_1535,plain,
% 2.46/1.00      ( X0_48 = k2_relset_1(sK0,sK1,sK2)
% 2.46/1.00      | X0_48 != k1_relat_1(k4_relat_1(sK2))
% 2.46/1.00      | k2_relset_1(sK0,sK1,sK2) != k1_relat_1(k4_relat_1(sK2)) ),
% 2.46/1.00      inference(instantiation,[status(thm)],[c_1235]) ).
% 2.46/1.00  
% 2.46/1.00  cnf(c_2455,plain,
% 2.46/1.00      ( k2_relset_1(sK0,sK1,sK2) != k1_relat_1(k4_relat_1(sK2))
% 2.46/1.00      | k1_relset_1(sK1,sK0,k4_relat_1(sK2)) = k2_relset_1(sK0,sK1,sK2)
% 2.46/1.00      | k1_relset_1(sK1,sK0,k4_relat_1(sK2)) != k1_relat_1(k4_relat_1(sK2)) ),
% 2.46/1.00      inference(instantiation,[status(thm)],[c_1535]) ).
% 2.46/1.00  
% 2.46/1.00  cnf(c_10,plain,
% 2.46/1.00      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 2.46/1.00      | k1_relset_1(X1,X2,X0) = k1_relat_1(X0) ),
% 2.46/1.00      inference(cnf_transformation,[],[f39]) ).
% 2.46/1.00  
% 2.46/1.00  cnf(c_591,plain,
% 2.46/1.00      ( ~ m1_subset_1(X0_44,k1_zfmisc_1(k2_zfmisc_1(X0_47,X1_47)))
% 2.46/1.00      | k1_relset_1(X0_47,X1_47,X0_44) = k1_relat_1(X0_44) ),
% 2.46/1.00      inference(subtyping,[status(esa)],[c_10]) ).
% 2.46/1.00  
% 2.46/1.00  cnf(c_1867,plain,
% 2.46/1.00      ( ~ m1_subset_1(k4_relat_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
% 2.46/1.00      | k1_relset_1(sK1,sK0,k4_relat_1(sK2)) = k1_relat_1(k4_relat_1(sK2)) ),
% 2.46/1.00      inference(instantiation,[status(thm)],[c_591]) ).
% 2.46/1.00  
% 2.46/1.00  cnf(c_1529,plain,
% 2.46/1.00      ( X0_48 = k2_relset_1(sK0,sK1,sK2)
% 2.46/1.00      | X0_48 != k2_relat_1(sK2)
% 2.46/1.00      | k2_relset_1(sK0,sK1,sK2) != k2_relat_1(sK2) ),
% 2.46/1.00      inference(instantiation,[status(thm)],[c_1235]) ).
% 2.46/1.00  
% 2.46/1.00  cnf(c_1716,plain,
% 2.46/1.00      ( k2_relset_1(sK0,sK1,sK2) != k2_relat_1(sK2)
% 2.46/1.00      | k2_relat_1(X0_44) = k2_relset_1(sK0,sK1,sK2)
% 2.46/1.00      | k2_relat_1(X0_44) != k2_relat_1(sK2) ),
% 2.46/1.00      inference(instantiation,[status(thm)],[c_1529]) ).
% 2.46/1.00  
% 2.46/1.00  cnf(c_1717,plain,
% 2.46/1.00      ( k2_relset_1(sK0,sK1,sK2) != k2_relat_1(sK2)
% 2.46/1.00      | k2_relat_1(sK2) = k2_relset_1(sK0,sK1,sK2)
% 2.46/1.00      | k2_relat_1(sK2) != k2_relat_1(sK2) ),
% 2.46/1.00      inference(instantiation,[status(thm)],[c_1716]) ).
% 2.46/1.00  
% 2.46/1.00  cnf(c_1219,plain,
% 2.46/1.00      ( m1_subset_1(k4_relat_1(sK2),k1_zfmisc_1(k2_zfmisc_1(X0_47,sK0)))
% 2.46/1.00      | ~ r1_tarski(k2_relat_1(k4_relat_1(sK2)),sK0)
% 2.46/1.00      | ~ r1_tarski(k1_relat_1(k4_relat_1(sK2)),X0_47)
% 2.46/1.00      | ~ v1_relat_1(k4_relat_1(sK2)) ),
% 2.46/1.00      inference(instantiation,[status(thm)],[c_588]) ).
% 2.46/1.00  
% 2.46/1.00  cnf(c_1448,plain,
% 2.46/1.00      ( m1_subset_1(k4_relat_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
% 2.46/1.00      | ~ r1_tarski(k2_relat_1(k4_relat_1(sK2)),sK0)
% 2.46/1.00      | ~ r1_tarski(k1_relat_1(k4_relat_1(sK2)),sK1)
% 2.46/1.00      | ~ v1_relat_1(k4_relat_1(sK2)) ),
% 2.46/1.00      inference(instantiation,[status(thm)],[c_1219]) ).
% 2.46/1.00  
% 2.46/1.00  cnf(c_1118,plain,
% 2.46/1.00      ( k2_relset_1(sK0,sK1,sK2) = k2_relat_1(sK2) ),
% 2.46/1.00      inference(superposition,[status(thm)],[c_859,c_856]) ).
% 2.46/1.00  
% 2.46/1.00  cnf(c_855,plain,
% 2.46/1.00      ( k1_relset_1(X0_47,X1_47,X0_44) = k1_relat_1(X0_44)
% 2.46/1.00      | m1_subset_1(X0_44,k1_zfmisc_1(k2_zfmisc_1(X0_47,X1_47))) != iProver_top ),
% 2.46/1.00      inference(predicate_to_equality,[status(thm)],[c_591]) ).
% 2.46/1.00  
% 2.46/1.00  cnf(c_1114,plain,
% 2.46/1.00      ( k1_relset_1(sK0,sK1,sK2) = k1_relat_1(sK2) ),
% 2.46/1.00      inference(superposition,[status(thm)],[c_859,c_855]) ).
% 2.46/1.00  
% 2.46/1.00  cnf(c_14,negated_conjecture,
% 2.46/1.00      ( k1_relset_1(sK1,sK0,k3_relset_1(sK0,sK1,sK2)) != k2_relset_1(sK0,sK1,sK2)
% 2.46/1.00      | k1_relset_1(sK0,sK1,sK2) != k2_relset_1(sK1,sK0,k3_relset_1(sK0,sK1,sK2)) ),
% 2.46/1.00      inference(cnf_transformation,[],[f44]) ).
% 2.46/1.00  
% 2.46/1.00  cnf(c_587,negated_conjecture,
% 2.46/1.00      ( k1_relset_1(sK1,sK0,k3_relset_1(sK0,sK1,sK2)) != k2_relset_1(sK0,sK1,sK2)
% 2.46/1.00      | k1_relset_1(sK0,sK1,sK2) != k2_relset_1(sK1,sK0,k3_relset_1(sK0,sK1,sK2)) ),
% 2.46/1.00      inference(subtyping,[status(esa)],[c_14]) ).
% 2.46/1.00  
% 2.46/1.00  cnf(c_1246,plain,
% 2.46/1.00      ( k2_relset_1(sK1,sK0,k3_relset_1(sK0,sK1,sK2)) != k1_relat_1(sK2)
% 2.46/1.00      | k1_relset_1(sK1,sK0,k3_relset_1(sK0,sK1,sK2)) != k2_relset_1(sK0,sK1,sK2) ),
% 2.46/1.00      inference(demodulation,[status(thm)],[c_1114,c_587]) ).
% 2.46/1.00  
% 2.46/1.00  cnf(c_1312,plain,
% 2.46/1.00      ( k2_relset_1(sK1,sK0,k3_relset_1(sK0,sK1,sK2)) != k1_relat_1(sK2)
% 2.46/1.00      | k1_relset_1(sK1,sK0,k3_relset_1(sK0,sK1,sK2)) != k2_relat_1(sK2) ),
% 2.46/1.00      inference(demodulation,[status(thm)],[c_1118,c_1246]) ).
% 2.46/1.00  
% 2.46/1.00  cnf(c_12,plain,
% 2.46/1.00      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 2.46/1.00      | k3_relset_1(X1,X2,X0) = k4_relat_1(X0) ),
% 2.46/1.00      inference(cnf_transformation,[],[f41]) ).
% 2.46/1.00  
% 2.46/1.00  cnf(c_589,plain,
% 2.46/1.00      ( ~ m1_subset_1(X0_44,k1_zfmisc_1(k2_zfmisc_1(X0_47,X1_47)))
% 2.46/1.00      | k3_relset_1(X0_47,X1_47,X0_44) = k4_relat_1(X0_44) ),
% 2.46/1.00      inference(subtyping,[status(esa)],[c_12]) ).
% 2.46/1.00  
% 2.46/1.00  cnf(c_857,plain,
% 2.46/1.00      ( k3_relset_1(X0_47,X1_47,X0_44) = k4_relat_1(X0_44)
% 2.46/1.00      | m1_subset_1(X0_44,k1_zfmisc_1(k2_zfmisc_1(X0_47,X1_47))) != iProver_top ),
% 2.46/1.00      inference(predicate_to_equality,[status(thm)],[c_589]) ).
% 2.46/1.00  
% 2.46/1.00  cnf(c_1161,plain,
% 2.46/1.00      ( k3_relset_1(sK0,sK1,sK2) = k4_relat_1(sK2) ),
% 2.46/1.00      inference(superposition,[status(thm)],[c_859,c_857]) ).
% 2.46/1.00  
% 2.46/1.00  cnf(c_1400,plain,
% 2.46/1.00      ( k2_relset_1(sK1,sK0,k4_relat_1(sK2)) != k1_relat_1(sK2)
% 2.46/1.00      | k1_relset_1(sK1,sK0,k4_relat_1(sK2)) != k2_relat_1(sK2) ),
% 2.46/1.00      inference(light_normalisation,[status(thm)],[c_1312,c_1161]) ).
% 2.46/1.00  
% 2.46/1.00  cnf(c_997,plain,
% 2.46/1.00      ( X0_48 != X1_48
% 2.46/1.00      | k2_relset_1(sK0,sK1,sK2) != X1_48
% 2.46/1.00      | k2_relset_1(sK0,sK1,sK2) = X0_48 ),
% 2.46/1.00      inference(instantiation,[status(thm)],[c_600]) ).
% 2.46/1.00  
% 2.46/1.00  cnf(c_1127,plain,
% 2.46/1.00      ( X0_48 != k2_relat_1(sK2)
% 2.46/1.00      | k2_relset_1(sK0,sK1,sK2) = X0_48
% 2.46/1.00      | k2_relset_1(sK0,sK1,sK2) != k2_relat_1(sK2) ),
% 2.46/1.00      inference(instantiation,[status(thm)],[c_997]) ).
% 2.46/1.00  
% 2.46/1.00  cnf(c_1215,plain,
% 2.46/1.00      ( k2_relset_1(sK0,sK1,sK2) != k2_relat_1(sK2)
% 2.46/1.00      | k2_relset_1(sK0,sK1,sK2) = k1_relat_1(k4_relat_1(sK2))
% 2.46/1.00      | k1_relat_1(k4_relat_1(sK2)) != k2_relat_1(sK2) ),
% 2.46/1.00      inference(instantiation,[status(thm)],[c_1127]) ).
% 2.46/1.00  
% 2.46/1.00  cnf(c_602,plain,
% 2.46/1.00      ( ~ r1_tarski(X0_48,X0_47)
% 2.46/1.00      | r1_tarski(X1_48,X0_47)
% 2.46/1.00      | X1_48 != X0_48 ),
% 2.46/1.00      theory(equality) ).
% 2.46/1.00  
% 2.46/1.00  cnf(c_979,plain,
% 2.46/1.00      ( r1_tarski(X0_48,sK0)
% 2.46/1.00      | ~ r1_tarski(k1_relat_1(sK2),sK0)
% 2.46/1.00      | X0_48 != k1_relat_1(sK2) ),
% 2.46/1.00      inference(instantiation,[status(thm)],[c_602]) ).
% 2.46/1.00  
% 2.46/1.00  cnf(c_1062,plain,
% 2.46/1.00      ( r1_tarski(k2_relat_1(k4_relat_1(sK2)),sK0)
% 2.46/1.00      | ~ r1_tarski(k1_relat_1(sK2),sK0)
% 2.46/1.00      | k2_relat_1(k4_relat_1(sK2)) != k1_relat_1(sK2) ),
% 2.46/1.00      inference(instantiation,[status(thm)],[c_979]) ).
% 2.46/1.00  
% 2.46/1.00  cnf(c_974,plain,
% 2.46/1.00      ( r1_tarski(X0_48,sK1)
% 2.46/1.00      | ~ r1_tarski(k2_relat_1(sK2),sK1)
% 2.46/1.00      | X0_48 != k2_relat_1(sK2) ),
% 2.46/1.00      inference(instantiation,[status(thm)],[c_602]) ).
% 2.46/1.00  
% 2.46/1.00  cnf(c_1037,plain,
% 2.46/1.00      ( ~ r1_tarski(k2_relat_1(sK2),sK1)
% 2.46/1.00      | r1_tarski(k1_relat_1(k4_relat_1(sK2)),sK1)
% 2.46/1.00      | k1_relat_1(k4_relat_1(sK2)) != k2_relat_1(sK2) ),
% 2.46/1.00      inference(instantiation,[status(thm)],[c_974]) ).
% 2.46/1.00  
% 2.46/1.00  cnf(c_958,plain,
% 2.46/1.00      ( ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
% 2.46/1.00      | k2_relset_1(sK0,sK1,sK2) = k2_relat_1(sK2) ),
% 2.46/1.00      inference(instantiation,[status(thm)],[c_590]) ).
% 2.46/1.00  
% 2.46/1.00  cnf(c_947,plain,
% 2.46/1.00      ( ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
% 2.46/1.00      | r1_tarski(k1_relat_1(sK2),sK0) ),
% 2.46/1.00      inference(instantiation,[status(thm)],[c_585]) ).
% 2.46/1.00  
% 2.46/1.00  cnf(c_944,plain,
% 2.46/1.00      ( ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
% 2.46/1.00      | r1_tarski(k2_relat_1(sK2),sK1) ),
% 2.46/1.00      inference(instantiation,[status(thm)],[c_584]) ).
% 2.46/1.00  
% 2.46/1.00  cnf(c_627,plain,
% 2.46/1.00      ( ~ v1_relat_1(sK2)
% 2.46/1.00      | k1_relat_1(k4_relat_1(sK2)) = k2_relat_1(sK2) ),
% 2.46/1.00      inference(instantiation,[status(thm)],[c_593]) ).
% 2.46/1.00  
% 2.46/1.00  cnf(c_624,plain,
% 2.46/1.00      ( ~ v1_relat_1(sK2)
% 2.46/1.00      | k2_relat_1(k4_relat_1(sK2)) = k1_relat_1(sK2) ),
% 2.46/1.00      inference(instantiation,[status(thm)],[c_594]) ).
% 2.46/1.00  
% 2.46/1.00  cnf(c_621,plain,
% 2.46/1.00      ( v1_relat_1(k4_relat_1(sK2)) | ~ v1_relat_1(sK2) ),
% 2.46/1.00      inference(instantiation,[status(thm)],[c_595]) ).
% 2.46/1.00  
% 2.46/1.00  cnf(c_597,plain,( X0_44 = X0_44 ),theory(equality) ).
% 2.46/1.00  
% 2.46/1.00  cnf(c_618,plain,
% 2.46/1.00      ( sK2 = sK2 ),
% 2.46/1.00      inference(instantiation,[status(thm)],[c_597]) ).
% 2.46/1.00  
% 2.46/1.00  cnf(c_604,plain,
% 2.46/1.00      ( k2_relat_1(X0_44) = k2_relat_1(X1_44) | X0_44 != X1_44 ),
% 2.46/1.00      theory(equality) ).
% 2.46/1.00  
% 2.46/1.00  cnf(c_612,plain,
% 2.46/1.00      ( k2_relat_1(sK2) = k2_relat_1(sK2) | sK2 != sK2 ),
% 2.46/1.00      inference(instantiation,[status(thm)],[c_604]) ).
% 2.46/1.00  
% 2.46/1.00  cnf(contradiction,plain,
% 2.46/1.00      ( $false ),
% 2.46/1.00      inference(minisat,
% 2.46/1.00                [status(thm)],
% 2.46/1.00                [c_6119,c_4992,c_2455,c_1867,c_1717,c_1448,c_1400,c_1215,
% 2.46/1.00                 c_1062,c_1037,c_958,c_947,c_944,c_937,c_627,c_624,c_621,
% 2.46/1.00                 c_618,c_612,c_15]) ).
% 2.46/1.00  
% 2.46/1.00  
% 2.46/1.00  % SZS output end CNFRefutation for theBenchmark.p
% 2.46/1.00  
% 2.46/1.00  ------                               Statistics
% 2.46/1.00  
% 2.46/1.00  ------ General
% 2.46/1.00  
% 2.46/1.00  abstr_ref_over_cycles:                  0
% 2.46/1.00  abstr_ref_under_cycles:                 0
% 2.46/1.00  gc_basic_clause_elim:                   0
% 2.46/1.00  forced_gc_time:                         0
% 2.46/1.00  parsing_time:                           0.007
% 2.46/1.00  unif_index_cands_time:                  0.
% 2.46/1.00  unif_index_add_time:                    0.
% 2.46/1.00  orderings_time:                         0.
% 2.46/1.00  out_proof_time:                         0.008
% 2.46/1.00  total_time:                             0.207
% 2.46/1.00  num_of_symbols:                         49
% 2.46/1.00  num_of_terms:                           3096
% 2.46/1.00  
% 2.46/1.00  ------ Preprocessing
% 2.46/1.00  
% 2.46/1.00  num_of_splits:                          0
% 2.46/1.00  num_of_split_atoms:                     0
% 2.46/1.00  num_of_reused_defs:                     0
% 2.46/1.00  num_eq_ax_congr_red:                    20
% 2.46/1.00  num_of_sem_filtered_clauses:            1
% 2.46/1.00  num_of_subtypes:                        5
% 2.46/1.00  monotx_restored_types:                  0
% 2.46/1.00  sat_num_of_epr_types:                   0
% 2.46/1.00  sat_num_of_non_cyclic_types:            0
% 2.46/1.00  sat_guarded_non_collapsed_types:        0
% 2.46/1.00  num_pure_diseq_elim:                    0
% 2.46/1.00  simp_replaced_by:                       0
% 2.46/1.00  res_preprocessed:                       77
% 2.46/1.00  prep_upred:                             0
% 2.46/1.00  prep_unflattend:                        14
% 2.46/1.00  smt_new_axioms:                         0
% 2.46/1.00  pred_elim_cands:                        3
% 2.46/1.00  pred_elim:                              2
% 2.46/1.00  pred_elim_cl:                           4
% 2.46/1.00  pred_elim_cycles:                       4
% 2.46/1.00  merged_defs:                            0
% 2.46/1.00  merged_defs_ncl:                        0
% 2.46/1.00  bin_hyper_res:                          0
% 2.46/1.00  prep_cycles:                            4
% 2.46/1.00  pred_elim_time:                         0.004
% 2.46/1.00  splitting_time:                         0.
% 2.46/1.00  sem_filter_time:                        0.
% 2.46/1.00  monotx_time:                            0.
% 2.46/1.00  subtype_inf_time:                       0.
% 2.46/1.00  
% 2.46/1.00  ------ Problem properties
% 2.46/1.00  
% 2.46/1.00  clauses:                                12
% 2.46/1.00  conjectures:                            2
% 2.46/1.00  epr:                                    0
% 2.46/1.00  horn:                                   12
% 2.46/1.00  ground:                                 2
% 2.46/1.00  unary:                                  1
% 2.46/1.00  binary:                                 10
% 2.46/1.00  lits:                                   25
% 2.46/1.00  lits_eq:                                7
% 2.46/1.00  fd_pure:                                0
% 2.46/1.00  fd_pseudo:                              0
% 2.46/1.00  fd_cond:                                0
% 2.46/1.00  fd_pseudo_cond:                         0
% 2.46/1.00  ac_symbols:                             0
% 2.46/1.00  
% 2.46/1.00  ------ Propositional Solver
% 2.46/1.00  
% 2.46/1.00  prop_solver_calls:                      31
% 2.46/1.00  prop_fast_solver_calls:                 559
% 2.46/1.00  smt_solver_calls:                       0
% 2.46/1.00  smt_fast_solver_calls:                  0
% 2.46/1.00  prop_num_of_clauses:                    1870
% 2.46/1.00  prop_preprocess_simplified:             6725
% 2.46/1.00  prop_fo_subsumed:                       7
% 2.46/1.00  prop_solver_time:                       0.
% 2.46/1.00  smt_solver_time:                        0.
% 2.46/1.00  smt_fast_solver_time:                   0.
% 2.46/1.00  prop_fast_solver_time:                  0.
% 2.46/1.00  prop_unsat_core_time:                   0.
% 2.46/1.00  
% 2.46/1.00  ------ QBF
% 2.46/1.00  
% 2.46/1.00  qbf_q_res:                              0
% 2.46/1.00  qbf_num_tautologies:                    0
% 2.46/1.00  qbf_prep_cycles:                        0
% 2.46/1.00  
% 2.46/1.00  ------ BMC1
% 2.46/1.00  
% 2.46/1.00  bmc1_current_bound:                     -1
% 2.46/1.00  bmc1_last_solved_bound:                 -1
% 2.46/1.00  bmc1_unsat_core_size:                   -1
% 2.46/1.00  bmc1_unsat_core_parents_size:           -1
% 2.46/1.00  bmc1_merge_next_fun:                    0
% 2.46/1.00  bmc1_unsat_core_clauses_time:           0.
% 2.46/1.00  
% 2.46/1.00  ------ Instantiation
% 2.46/1.00  
% 2.46/1.00  inst_num_of_clauses:                    973
% 2.46/1.00  inst_num_in_passive:                    525
% 2.46/1.00  inst_num_in_active:                     412
% 2.46/1.00  inst_num_in_unprocessed:                37
% 2.46/1.00  inst_num_of_loops:                      430
% 2.46/1.00  inst_num_of_learning_restarts:          0
% 2.46/1.00  inst_num_moves_active_passive:          13
% 2.46/1.00  inst_lit_activity:                      0
% 2.46/1.00  inst_lit_activity_moves:                0
% 2.46/1.00  inst_num_tautologies:                   0
% 2.46/1.00  inst_num_prop_implied:                  0
% 2.46/1.00  inst_num_existing_simplified:           0
% 2.46/1.00  inst_num_eq_res_simplified:             0
% 2.46/1.00  inst_num_child_elim:                    0
% 2.46/1.00  inst_num_of_dismatching_blockings:      256
% 2.46/1.00  inst_num_of_non_proper_insts:           1108
% 2.46/1.00  inst_num_of_duplicates:                 0
% 2.46/1.00  inst_inst_num_from_inst_to_res:         0
% 2.46/1.00  inst_dismatching_checking_time:         0.
% 2.46/1.00  
% 2.46/1.00  ------ Resolution
% 2.46/1.00  
% 2.46/1.00  res_num_of_clauses:                     0
% 2.46/1.00  res_num_in_passive:                     0
% 2.46/1.00  res_num_in_active:                      0
% 2.46/1.00  res_num_of_loops:                       81
% 2.46/1.00  res_forward_subset_subsumed:            154
% 2.46/1.00  res_backward_subset_subsumed:           4
% 2.46/1.00  res_forward_subsumed:                   0
% 2.46/1.00  res_backward_subsumed:                  0
% 2.46/1.00  res_forward_subsumption_resolution:     0
% 2.46/1.00  res_backward_subsumption_resolution:    0
% 2.46/1.00  res_clause_to_clause_subsumption:       705
% 2.46/1.00  res_orphan_elimination:                 0
% 2.46/1.00  res_tautology_del:                      281
% 2.46/1.00  res_num_eq_res_simplified:              0
% 2.46/1.00  res_num_sel_changes:                    0
% 2.46/1.00  res_moves_from_active_to_pass:          0
% 2.46/1.00  
% 2.46/1.00  ------ Superposition
% 2.46/1.00  
% 2.46/1.00  sup_time_total:                         0.
% 2.46/1.00  sup_time_generating:                    0.
% 2.46/1.00  sup_time_sim_full:                      0.
% 2.46/1.00  sup_time_sim_immed:                     0.
% 2.46/1.00  
% 2.46/1.00  sup_num_of_clauses:                     123
% 2.46/1.00  sup_num_in_active:                      73
% 2.46/1.00  sup_num_in_passive:                     50
% 2.46/1.00  sup_num_of_loops:                       84
% 2.46/1.00  sup_fw_superposition:                   80
% 2.46/1.00  sup_bw_superposition:                   37
% 2.46/1.00  sup_immediate_simplified:               41
% 2.46/1.00  sup_given_eliminated:                   0
% 2.46/1.00  comparisons_done:                       0
% 2.46/1.00  comparisons_avoided:                    0
% 2.46/1.00  
% 2.46/1.00  ------ Simplifications
% 2.46/1.00  
% 2.46/1.00  
% 2.46/1.00  sim_fw_subset_subsumed:                 0
% 2.46/1.00  sim_bw_subset_subsumed:                 0
% 2.46/1.00  sim_fw_subsumed:                        0
% 2.46/1.00  sim_bw_subsumed:                        0
% 2.46/1.00  sim_fw_subsumption_res:                 0
% 2.46/1.00  sim_bw_subsumption_res:                 0
% 2.46/1.00  sim_tautology_del:                      3
% 2.46/1.00  sim_eq_tautology_del:                   0
% 2.46/1.00  sim_eq_res_simp:                        0
% 2.46/1.00  sim_fw_demodulated:                     0
% 2.46/1.00  sim_bw_demodulated:                     12
% 2.46/1.00  sim_light_normalised:                   45
% 2.46/1.00  sim_joinable_taut:                      0
% 2.46/1.00  sim_joinable_simp:                      0
% 2.46/1.00  sim_ac_normalised:                      0
% 2.46/1.00  sim_smt_subsumption:                    0
% 2.46/1.00  
%------------------------------------------------------------------------------
