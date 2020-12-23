%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n006.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 11:55:42 EST 2020

% Result     : Theorem 1.19s
% Output     : CNFRefutation 1.19s
% Verified   : 
% Statistics : Number of formulae       :   99 ( 234 expanded)
%              Number of clauses        :   60 (  95 expanded)
%              Number of leaves         :   13 (  43 expanded)
%              Depth                    :   17
%              Number of atoms          :  232 ( 601 expanded)
%              Number of equality atoms :   79 ( 106 expanded)
%              Maximal formula depth    :    8 (   4 average)
%              Maximal clause size      :    6 (   2 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f10,conjecture,(
    ! [X0,X1,X2,X3] :
      ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
     => ( r1_tarski(X1,X2)
       => r2_relset_1(X1,X0,k5_relset_1(X1,X0,X3,X2),X3) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f11,negated_conjecture,(
    ~ ! [X0,X1,X2,X3] :
        ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
       => ( r1_tarski(X1,X2)
         => r2_relset_1(X1,X0,k5_relset_1(X1,X0,X3,X2),X3) ) ) ),
    inference(negated_conjecture,[],[f10])).

fof(f23,plain,(
    ? [X0,X1,X2,X3] :
      ( ~ r2_relset_1(X1,X0,k5_relset_1(X1,X0,X3,X2),X3)
      & r1_tarski(X1,X2)
      & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f24,plain,(
    ? [X0,X1,X2,X3] :
      ( ~ r2_relset_1(X1,X0,k5_relset_1(X1,X0,X3,X2),X3)
      & r1_tarski(X1,X2)
      & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) ) ),
    inference(flattening,[],[f23])).

fof(f26,plain,
    ( ? [X0,X1,X2,X3] :
        ( ~ r2_relset_1(X1,X0,k5_relset_1(X1,X0,X3,X2),X3)
        & r1_tarski(X1,X2)
        & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) )
   => ( ~ r2_relset_1(sK1,sK0,k5_relset_1(sK1,sK0,sK3,sK2),sK3)
      & r1_tarski(sK1,sK2)
      & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) ) ),
    introduced(choice_axiom,[])).

fof(f27,plain,
    ( ~ r2_relset_1(sK1,sK0,k5_relset_1(sK1,sK0,sK3,sK2),sK3)
    & r1_tarski(sK1,sK2)
    & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3])],[f24,f26])).

fof(f39,plain,(
    r1_tarski(sK1,sK2) ),
    inference(cnf_transformation,[],[f27])).

fof(f38,plain,(
    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) ),
    inference(cnf_transformation,[],[f27])).

fof(f7,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => ( v5_relat_1(X2,X1)
        & v4_relat_1(X2,X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f12,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => v4_relat_1(X2,X0) ) ),
    inference(pure_predicate_removal,[],[f7])).

fof(f19,plain,(
    ! [X0,X1,X2] :
      ( v4_relat_1(X2,X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f35,plain,(
    ! [X2,X0,X1] :
      ( v4_relat_1(X2,X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ( v4_relat_1(X1,X0)
      <=> r1_tarski(k1_relat_1(X1),X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f16,plain,(
    ! [X0,X1] :
      ( ( v4_relat_1(X1,X0)
      <=> r1_tarski(k1_relat_1(X1),X0) )
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f25,plain,(
    ! [X0,X1] :
      ( ( ( v4_relat_1(X1,X0)
          | ~ r1_tarski(k1_relat_1(X1),X0) )
        & ( r1_tarski(k1_relat_1(X1),X0)
          | ~ v4_relat_1(X1,X0) ) )
      | ~ v1_relat_1(X1) ) ),
    inference(nnf_transformation,[],[f16])).

fof(f31,plain,(
    ! [X0,X1] :
      ( r1_tarski(k1_relat_1(X1),X0)
      | ~ v4_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f3,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(X0))
         => v1_relat_1(X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f15,plain,(
    ! [X0] :
      ( ! [X1] :
          ( v1_relat_1(X1)
          | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f30,plain,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f15])).

fof(f5,axiom,(
    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f33,plain,(
    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1)) ),
    inference(cnf_transformation,[],[f5])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
     => k2_xboole_0(X0,X1) = X1 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f14,plain,(
    ! [X0,X1] :
      ( k2_xboole_0(X0,X1) = X1
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f29,plain,(
    ! [X0,X1] :
      ( k2_xboole_0(X0,X1) = X1
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f14])).

fof(f1,axiom,(
    ! [X0,X1,X2] :
      ( r1_tarski(k2_xboole_0(X0,X1),X2)
     => r1_tarski(X0,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f13,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,X2)
      | ~ r1_tarski(k2_xboole_0(X0,X1),X2) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f28,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(X0,X2)
      | ~ r1_tarski(k2_xboole_0(X0,X1),X2) ) ),
    inference(cnf_transformation,[],[f13])).

fof(f6,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ( r1_tarski(k1_relat_1(X1),X0)
       => k7_relat_1(X1,X0) = X1 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f17,plain,(
    ! [X0,X1] :
      ( k7_relat_1(X1,X0) = X1
      | ~ r1_tarski(k1_relat_1(X1),X0)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f18,plain,(
    ! [X0,X1] :
      ( k7_relat_1(X1,X0) = X1
      | ~ r1_tarski(k1_relat_1(X1),X0)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f17])).

fof(f34,plain,(
    ! [X0,X1] :
      ( k7_relat_1(X1,X0) = X1
      | ~ r1_tarski(k1_relat_1(X1),X0)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f8,axiom,(
    ! [X0,X1,X2,X3] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k7_relat_1(X2,X3) = k5_relset_1(X0,X1,X2,X3) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f20,plain,(
    ! [X0,X1,X2,X3] :
      ( k7_relat_1(X2,X3) = k5_relset_1(X0,X1,X2,X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f36,plain,(
    ! [X2,X0,X3,X1] :
      ( k7_relat_1(X2,X3) = k5_relset_1(X0,X1,X2,X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f9,axiom,(
    ! [X0,X1,X2,X3] :
      ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) )
     => r2_relset_1(X0,X1,X2,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f21,plain,(
    ! [X0,X1,X2,X3] :
      ( r2_relset_1(X0,X1,X2,X2)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f22,plain,(
    ! [X0,X1,X2,X3] :
      ( r2_relset_1(X0,X1,X2,X2)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(flattening,[],[f21])).

fof(f37,plain,(
    ! [X2,X0,X3,X1] :
      ( r2_relset_1(X0,X1,X2,X2)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f40,plain,(
    ~ r2_relset_1(sK1,sK0,k5_relset_1(sK1,sK0,sK3,sK2),sK3) ),
    inference(cnf_transformation,[],[f27])).

cnf(c_11,negated_conjecture,
    ( r1_tarski(sK1,sK2) ),
    inference(cnf_transformation,[],[f39])).

cnf(c_485,plain,
    ( r1_tarski(sK1,sK2) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_11])).

cnf(c_12,negated_conjecture,
    ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) ),
    inference(cnf_transformation,[],[f38])).

cnf(c_484,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_12])).

cnf(c_7,plain,
    ( v4_relat_1(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) ),
    inference(cnf_transformation,[],[f35])).

cnf(c_4,plain,
    ( ~ v4_relat_1(X0,X1)
    | r1_tarski(k1_relat_1(X0),X1)
    | ~ v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f31])).

cnf(c_168,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | r1_tarski(k1_relat_1(X0),X1)
    | ~ v1_relat_1(X0) ),
    inference(resolution,[status(thm)],[c_7,c_4])).

cnf(c_481,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) != iProver_top
    | r1_tarski(k1_relat_1(X0),X1) = iProver_top
    | v1_relat_1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_168])).

cnf(c_783,plain,
    ( r1_tarski(k1_relat_1(sK3),sK1) = iProver_top
    | v1_relat_1(sK3) != iProver_top ),
    inference(superposition,[status(thm)],[c_484,c_481])).

cnf(c_13,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_12])).

cnf(c_2,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | ~ v1_relat_1(X1)
    | v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f30])).

cnf(c_563,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | v1_relat_1(X0)
    | ~ v1_relat_1(k2_zfmisc_1(X1,X2)) ),
    inference(instantiation,[status(thm)],[c_2])).

cnf(c_636,plain,
    ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
    | ~ v1_relat_1(k2_zfmisc_1(sK1,sK0))
    | v1_relat_1(sK3) ),
    inference(instantiation,[status(thm)],[c_563])).

cnf(c_637,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) != iProver_top
    | v1_relat_1(k2_zfmisc_1(sK1,sK0)) != iProver_top
    | v1_relat_1(sK3) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_636])).

cnf(c_5,plain,
    ( v1_relat_1(k2_zfmisc_1(X0,X1)) ),
    inference(cnf_transformation,[],[f33])).

cnf(c_741,plain,
    ( v1_relat_1(k2_zfmisc_1(sK1,sK0)) ),
    inference(instantiation,[status(thm)],[c_5])).

cnf(c_742,plain,
    ( v1_relat_1(k2_zfmisc_1(sK1,sK0)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_741])).

cnf(c_994,plain,
    ( r1_tarski(k1_relat_1(sK3),sK1) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_783,c_13,c_637,c_742])).

cnf(c_1,plain,
    ( ~ r1_tarski(X0,X1)
    | k2_xboole_0(X0,X1) = X1 ),
    inference(cnf_transformation,[],[f29])).

cnf(c_490,plain,
    ( k2_xboole_0(X0,X1) = X1
    | r1_tarski(X0,X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1])).

cnf(c_999,plain,
    ( k2_xboole_0(k1_relat_1(sK3),sK1) = sK1 ),
    inference(superposition,[status(thm)],[c_994,c_490])).

cnf(c_0,plain,
    ( r1_tarski(X0,X1)
    | ~ r1_tarski(k2_xboole_0(X0,X2),X1) ),
    inference(cnf_transformation,[],[f28])).

cnf(c_491,plain,
    ( r1_tarski(X0,X1) = iProver_top
    | r1_tarski(k2_xboole_0(X0,X2),X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_0])).

cnf(c_1066,plain,
    ( r1_tarski(k1_relat_1(sK3),X0) = iProver_top
    | r1_tarski(sK1,X0) != iProver_top ),
    inference(superposition,[status(thm)],[c_999,c_491])).

cnf(c_6,plain,
    ( ~ r1_tarski(k1_relat_1(X0),X1)
    | ~ v1_relat_1(X0)
    | k7_relat_1(X0,X1) = X0 ),
    inference(cnf_transformation,[],[f34])).

cnf(c_487,plain,
    ( k7_relat_1(X0,X1) = X0
    | r1_tarski(k1_relat_1(X0),X1) != iProver_top
    | v1_relat_1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_6])).

cnf(c_1249,plain,
    ( k7_relat_1(sK3,X0) = sK3
    | r1_tarski(sK1,X0) != iProver_top
    | v1_relat_1(sK3) != iProver_top ),
    inference(superposition,[status(thm)],[c_1066,c_487])).

cnf(c_1381,plain,
    ( r1_tarski(sK1,X0) != iProver_top
    | k7_relat_1(sK3,X0) = sK3 ),
    inference(global_propositional_subsumption,[status(thm)],[c_1249,c_13,c_637,c_742])).

cnf(c_1382,plain,
    ( k7_relat_1(sK3,X0) = sK3
    | r1_tarski(sK1,X0) != iProver_top ),
    inference(renaming,[status(thm)],[c_1381])).

cnf(c_1387,plain,
    ( k7_relat_1(sK3,sK2) = sK3 ),
    inference(superposition,[status(thm)],[c_485,c_1382])).

cnf(c_8,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k5_relset_1(X1,X2,X0,X3) = k7_relat_1(X0,X3) ),
    inference(cnf_transformation,[],[f36])).

cnf(c_486,plain,
    ( k5_relset_1(X0,X1,X2,X3) = k7_relat_1(X2,X3)
    | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_8])).

cnf(c_846,plain,
    ( k5_relset_1(sK1,sK0,sK3,X0) = k7_relat_1(sK3,X0) ),
    inference(superposition,[status(thm)],[c_484,c_486])).

cnf(c_9,plain,
    ( r2_relset_1(X0,X1,X2,X2)
    | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ),
    inference(cnf_transformation,[],[f37])).

cnf(c_10,negated_conjecture,
    ( ~ r2_relset_1(sK1,sK0,k5_relset_1(sK1,sK0,sK3,sK2),sK3) ),
    inference(cnf_transformation,[],[f40])).

cnf(c_149,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k5_relset_1(sK1,sK0,sK3,sK2) != X0
    | sK3 != X0
    | sK0 != X2
    | sK1 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_9,c_10])).

cnf(c_150,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
    | ~ m1_subset_1(k5_relset_1(sK1,sK0,sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
    | sK3 != k5_relset_1(sK1,sK0,sK3,sK2) ),
    inference(unflattening,[status(thm)],[c_149])).

cnf(c_260,plain,
    ( ~ m1_subset_1(k5_relset_1(sK1,sK0,sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
    | sP0_iProver_split
    | sK3 != k5_relset_1(sK1,sK0,sK3,sK2) ),
    inference(splitting,[splitting(split),new_symbols(definition,[])],[c_150])).

cnf(c_482,plain,
    ( sK3 != k5_relset_1(sK1,sK0,sK3,sK2)
    | m1_subset_1(k5_relset_1(sK1,sK0,sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) != iProver_top
    | sP0_iProver_split = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_260])).

cnf(c_259,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
    | ~ sP0_iProver_split ),
    inference(splitting,[splitting(split),new_symbols(definition,[sP0_iProver_split])],[c_150])).

cnf(c_483,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) != iProver_top
    | sP0_iProver_split != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_259])).

cnf(c_535,plain,
    ( k5_relset_1(sK1,sK0,sK3,sK2) != sK3
    | m1_subset_1(k5_relset_1(sK1,sK0,sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) != iProver_top ),
    inference(forward_subsumption_resolution,[status(thm)],[c_482,c_483])).

cnf(c_900,plain,
    ( k7_relat_1(sK3,sK2) != sK3
    | m1_subset_1(k7_relat_1(sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) != iProver_top ),
    inference(demodulation,[status(thm)],[c_846,c_535])).

cnf(c_262,plain,
    ( X0 = X0 ),
    theory(equality)).

cnf(c_615,plain,
    ( sK2 = sK2 ),
    inference(instantiation,[status(thm)],[c_262])).

cnf(c_784,plain,
    ( r1_tarski(k1_relat_1(sK3),sK1)
    | ~ v1_relat_1(sK3) ),
    inference(predicate_to_equality_rev,[status(thm)],[c_783])).

cnf(c_652,plain,
    ( ~ r1_tarski(k1_relat_1(sK3),X0)
    | ~ v1_relat_1(sK3)
    | k7_relat_1(sK3,X0) = sK3 ),
    inference(instantiation,[status(thm)],[c_6])).

cnf(c_792,plain,
    ( ~ r1_tarski(k1_relat_1(sK3),sK2)
    | ~ v1_relat_1(sK3)
    | k7_relat_1(sK3,sK2) = sK3 ),
    inference(instantiation,[status(thm)],[c_652])).

cnf(c_915,plain,
    ( ~ r1_tarski(k1_relat_1(sK3),sK1)
    | k2_xboole_0(k1_relat_1(sK3),sK1) = sK1 ),
    inference(instantiation,[status(thm)],[c_1])).

cnf(c_678,plain,
    ( r1_tarski(X0,sK2)
    | ~ r1_tarski(k2_xboole_0(X0,X1),sK2) ),
    inference(instantiation,[status(thm)],[c_0])).

cnf(c_958,plain,
    ( ~ r1_tarski(k2_xboole_0(k1_relat_1(sK3),X0),sK2)
    | r1_tarski(k1_relat_1(sK3),sK2) ),
    inference(instantiation,[status(thm)],[c_678])).

cnf(c_961,plain,
    ( ~ r1_tarski(k2_xboole_0(k1_relat_1(sK3),sK1),sK2)
    | r1_tarski(k1_relat_1(sK3),sK2) ),
    inference(instantiation,[status(thm)],[c_958])).

cnf(c_264,plain,
    ( ~ r1_tarski(X0,X1)
    | r1_tarski(X2,X3)
    | X2 != X0
    | X3 != X1 ),
    theory(equality)).

cnf(c_585,plain,
    ( r1_tarski(X0,X1)
    | ~ r1_tarski(sK1,sK2)
    | X1 != sK2
    | X0 != sK1 ),
    inference(instantiation,[status(thm)],[c_264])).

cnf(c_614,plain,
    ( r1_tarski(X0,sK2)
    | ~ r1_tarski(sK1,sK2)
    | X0 != sK1
    | sK2 != sK2 ),
    inference(instantiation,[status(thm)],[c_585])).

cnf(c_677,plain,
    ( r1_tarski(k2_xboole_0(X0,X1),sK2)
    | ~ r1_tarski(sK1,sK2)
    | k2_xboole_0(X0,X1) != sK1
    | sK2 != sK2 ),
    inference(instantiation,[status(thm)],[c_614])).

cnf(c_1163,plain,
    ( r1_tarski(k2_xboole_0(k1_relat_1(sK3),sK1),sK2)
    | ~ r1_tarski(sK1,sK2)
    | k2_xboole_0(k1_relat_1(sK3),sK1) != sK1
    | sK2 != sK2 ),
    inference(instantiation,[status(thm)],[c_677])).

cnf(c_1173,plain,
    ( m1_subset_1(k7_relat_1(sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_900,c_12,c_11,c_615,c_636,c_741,c_784,c_792,c_915,c_961,c_1163])).

cnf(c_1499,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) != iProver_top ),
    inference(demodulation,[status(thm)],[c_1387,c_1173])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_1499,c_13])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : iproveropt_run.sh %d %s
% 0.13/0.34  % Computer   : n006.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 10:54:52 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  % Running in FOF mode
% 1.19/1.02  % SZS status Started for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.19/1.02  
% 1.19/1.02  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 1.19/1.02  
% 1.19/1.02  ------  iProver source info
% 1.19/1.02  
% 1.19/1.02  git: date: 2020-06-30 10:37:57 +0100
% 1.19/1.02  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 1.19/1.02  git: non_committed_changes: false
% 1.19/1.02  git: last_make_outside_of_git: false
% 1.19/1.02  
% 1.19/1.02  ------ 
% 1.19/1.02  
% 1.19/1.02  ------ Input Options
% 1.19/1.02  
% 1.19/1.02  --out_options                           all
% 1.19/1.02  --tptp_safe_out                         true
% 1.19/1.02  --problem_path                          ""
% 1.19/1.02  --include_path                          ""
% 1.19/1.02  --clausifier                            res/vclausify_rel
% 1.19/1.02  --clausifier_options                    --mode clausify
% 1.19/1.02  --stdin                                 false
% 1.19/1.02  --stats_out                             all
% 1.19/1.02  
% 1.19/1.02  ------ General Options
% 1.19/1.02  
% 1.19/1.02  --fof                                   false
% 1.19/1.02  --time_out_real                         305.
% 1.19/1.02  --time_out_virtual                      -1.
% 1.19/1.02  --symbol_type_check                     false
% 1.19/1.02  --clausify_out                          false
% 1.19/1.02  --sig_cnt_out                           false
% 1.19/1.02  --trig_cnt_out                          false
% 1.19/1.02  --trig_cnt_out_tolerance                1.
% 1.19/1.02  --trig_cnt_out_sk_spl                   false
% 1.19/1.02  --abstr_cl_out                          false
% 1.19/1.02  
% 1.19/1.02  ------ Global Options
% 1.19/1.02  
% 1.19/1.02  --schedule                              default
% 1.19/1.02  --add_important_lit                     false
% 1.19/1.02  --prop_solver_per_cl                    1000
% 1.19/1.02  --min_unsat_core                        false
% 1.19/1.02  --soft_assumptions                      false
% 1.19/1.02  --soft_lemma_size                       3
% 1.19/1.02  --prop_impl_unit_size                   0
% 1.19/1.02  --prop_impl_unit                        []
% 1.19/1.02  --share_sel_clauses                     true
% 1.19/1.02  --reset_solvers                         false
% 1.19/1.02  --bc_imp_inh                            [conj_cone]
% 1.19/1.02  --conj_cone_tolerance                   3.
% 1.19/1.02  --extra_neg_conj                        none
% 1.19/1.02  --large_theory_mode                     true
% 1.19/1.02  --prolific_symb_bound                   200
% 1.19/1.02  --lt_threshold                          2000
% 1.19/1.02  --clause_weak_htbl                      true
% 1.19/1.02  --gc_record_bc_elim                     false
% 1.19/1.02  
% 1.19/1.02  ------ Preprocessing Options
% 1.19/1.02  
% 1.19/1.02  --preprocessing_flag                    true
% 1.19/1.02  --time_out_prep_mult                    0.1
% 1.19/1.02  --splitting_mode                        input
% 1.19/1.02  --splitting_grd                         true
% 1.19/1.02  --splitting_cvd                         false
% 1.19/1.02  --splitting_cvd_svl                     false
% 1.19/1.02  --splitting_nvd                         32
% 1.19/1.02  --sub_typing                            true
% 1.19/1.02  --prep_gs_sim                           true
% 1.19/1.02  --prep_unflatten                        true
% 1.19/1.02  --prep_res_sim                          true
% 1.19/1.02  --prep_upred                            true
% 1.19/1.02  --prep_sem_filter                       exhaustive
% 1.19/1.02  --prep_sem_filter_out                   false
% 1.19/1.02  --pred_elim                             true
% 1.19/1.02  --res_sim_input                         true
% 1.19/1.02  --eq_ax_congr_red                       true
% 1.19/1.02  --pure_diseq_elim                       true
% 1.19/1.02  --brand_transform                       false
% 1.19/1.02  --non_eq_to_eq                          false
% 1.19/1.02  --prep_def_merge                        true
% 1.19/1.02  --prep_def_merge_prop_impl              false
% 1.19/1.02  --prep_def_merge_mbd                    true
% 1.19/1.02  --prep_def_merge_tr_red                 false
% 1.19/1.02  --prep_def_merge_tr_cl                  false
% 1.19/1.02  --smt_preprocessing                     true
% 1.19/1.02  --smt_ac_axioms                         fast
% 1.19/1.02  --preprocessed_out                      false
% 1.19/1.02  --preprocessed_stats                    false
% 1.19/1.02  
% 1.19/1.02  ------ Abstraction refinement Options
% 1.19/1.02  
% 1.19/1.02  --abstr_ref                             []
% 1.19/1.02  --abstr_ref_prep                        false
% 1.19/1.02  --abstr_ref_until_sat                   false
% 1.19/1.02  --abstr_ref_sig_restrict                funpre
% 1.19/1.02  --abstr_ref_af_restrict_to_split_sk     false
% 1.19/1.02  --abstr_ref_under                       []
% 1.19/1.02  
% 1.19/1.02  ------ SAT Options
% 1.19/1.02  
% 1.19/1.02  --sat_mode                              false
% 1.19/1.02  --sat_fm_restart_options                ""
% 1.19/1.02  --sat_gr_def                            false
% 1.19/1.02  --sat_epr_types                         true
% 1.19/1.02  --sat_non_cyclic_types                  false
% 1.19/1.02  --sat_finite_models                     false
% 1.19/1.02  --sat_fm_lemmas                         false
% 1.19/1.02  --sat_fm_prep                           false
% 1.19/1.02  --sat_fm_uc_incr                        true
% 1.19/1.02  --sat_out_model                         small
% 1.19/1.02  --sat_out_clauses                       false
% 1.19/1.02  
% 1.19/1.02  ------ QBF Options
% 1.19/1.02  
% 1.19/1.02  --qbf_mode                              false
% 1.19/1.02  --qbf_elim_univ                         false
% 1.19/1.02  --qbf_dom_inst                          none
% 1.19/1.02  --qbf_dom_pre_inst                      false
% 1.19/1.02  --qbf_sk_in                             false
% 1.19/1.02  --qbf_pred_elim                         true
% 1.19/1.02  --qbf_split                             512
% 1.19/1.02  
% 1.19/1.02  ------ BMC1 Options
% 1.19/1.02  
% 1.19/1.02  --bmc1_incremental                      false
% 1.19/1.02  --bmc1_axioms                           reachable_all
% 1.19/1.02  --bmc1_min_bound                        0
% 1.19/1.02  --bmc1_max_bound                        -1
% 1.19/1.02  --bmc1_max_bound_default                -1
% 1.19/1.02  --bmc1_symbol_reachability              true
% 1.19/1.02  --bmc1_property_lemmas                  false
% 1.19/1.02  --bmc1_k_induction                      false
% 1.19/1.02  --bmc1_non_equiv_states                 false
% 1.19/1.02  --bmc1_deadlock                         false
% 1.19/1.02  --bmc1_ucm                              false
% 1.19/1.02  --bmc1_add_unsat_core                   none
% 1.19/1.02  --bmc1_unsat_core_children              false
% 1.19/1.02  --bmc1_unsat_core_extrapolate_axioms    false
% 1.19/1.02  --bmc1_out_stat                         full
% 1.19/1.02  --bmc1_ground_init                      false
% 1.19/1.02  --bmc1_pre_inst_next_state              false
% 1.19/1.02  --bmc1_pre_inst_state                   false
% 1.19/1.02  --bmc1_pre_inst_reach_state             false
% 1.19/1.02  --bmc1_out_unsat_core                   false
% 1.19/1.02  --bmc1_aig_witness_out                  false
% 1.19/1.02  --bmc1_verbose                          false
% 1.19/1.02  --bmc1_dump_clauses_tptp                false
% 1.19/1.02  --bmc1_dump_unsat_core_tptp             false
% 1.19/1.02  --bmc1_dump_file                        -
% 1.19/1.02  --bmc1_ucm_expand_uc_limit              128
% 1.19/1.02  --bmc1_ucm_n_expand_iterations          6
% 1.19/1.02  --bmc1_ucm_extend_mode                  1
% 1.19/1.02  --bmc1_ucm_init_mode                    2
% 1.19/1.02  --bmc1_ucm_cone_mode                    none
% 1.19/1.02  --bmc1_ucm_reduced_relation_type        0
% 1.19/1.02  --bmc1_ucm_relax_model                  4
% 1.19/1.02  --bmc1_ucm_full_tr_after_sat            true
% 1.19/1.02  --bmc1_ucm_expand_neg_assumptions       false
% 1.19/1.02  --bmc1_ucm_layered_model                none
% 1.19/1.02  --bmc1_ucm_max_lemma_size               10
% 1.19/1.02  
% 1.19/1.02  ------ AIG Options
% 1.19/1.02  
% 1.19/1.02  --aig_mode                              false
% 1.19/1.02  
% 1.19/1.02  ------ Instantiation Options
% 1.19/1.02  
% 1.19/1.02  --instantiation_flag                    true
% 1.19/1.02  --inst_sos_flag                         false
% 1.19/1.02  --inst_sos_phase                        true
% 1.19/1.02  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 1.19/1.02  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 1.19/1.02  --inst_lit_sel_side                     num_symb
% 1.19/1.02  --inst_solver_per_active                1400
% 1.19/1.02  --inst_solver_calls_frac                1.
% 1.19/1.02  --inst_passive_queue_type               priority_queues
% 1.19/1.02  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 1.19/1.02  --inst_passive_queues_freq              [25;2]
% 1.19/1.02  --inst_dismatching                      true
% 1.19/1.02  --inst_eager_unprocessed_to_passive     true
% 1.19/1.02  --inst_prop_sim_given                   true
% 1.19/1.02  --inst_prop_sim_new                     false
% 1.19/1.02  --inst_subs_new                         false
% 1.19/1.02  --inst_eq_res_simp                      false
% 1.19/1.02  --inst_subs_given                       false
% 1.19/1.02  --inst_orphan_elimination               true
% 1.19/1.02  --inst_learning_loop_flag               true
% 1.19/1.02  --inst_learning_start                   3000
% 1.19/1.02  --inst_learning_factor                  2
% 1.19/1.02  --inst_start_prop_sim_after_learn       3
% 1.19/1.02  --inst_sel_renew                        solver
% 1.19/1.02  --inst_lit_activity_flag                true
% 1.19/1.02  --inst_restr_to_given                   false
% 1.19/1.02  --inst_activity_threshold               500
% 1.19/1.02  --inst_out_proof                        true
% 1.19/1.02  
% 1.19/1.02  ------ Resolution Options
% 1.19/1.02  
% 1.19/1.02  --resolution_flag                       true
% 1.19/1.02  --res_lit_sel                           adaptive
% 1.19/1.02  --res_lit_sel_side                      none
% 1.19/1.02  --res_ordering                          kbo
% 1.19/1.02  --res_to_prop_solver                    active
% 1.19/1.02  --res_prop_simpl_new                    false
% 1.19/1.02  --res_prop_simpl_given                  true
% 1.19/1.02  --res_passive_queue_type                priority_queues
% 1.19/1.02  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 1.19/1.02  --res_passive_queues_freq               [15;5]
% 1.19/1.02  --res_forward_subs                      full
% 1.19/1.02  --res_backward_subs                     full
% 1.19/1.02  --res_forward_subs_resolution           true
% 1.19/1.02  --res_backward_subs_resolution          true
% 1.19/1.02  --res_orphan_elimination                true
% 1.19/1.02  --res_time_limit                        2.
% 1.19/1.02  --res_out_proof                         true
% 1.19/1.02  
% 1.19/1.02  ------ Superposition Options
% 1.19/1.02  
% 1.19/1.02  --superposition_flag                    true
% 1.19/1.02  --sup_passive_queue_type                priority_queues
% 1.19/1.02  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 1.19/1.02  --sup_passive_queues_freq               [8;1;4]
% 1.19/1.02  --demod_completeness_check              fast
% 1.19/1.02  --demod_use_ground                      true
% 1.19/1.02  --sup_to_prop_solver                    passive
% 1.19/1.02  --sup_prop_simpl_new                    true
% 1.19/1.02  --sup_prop_simpl_given                  true
% 1.19/1.02  --sup_fun_splitting                     false
% 1.19/1.02  --sup_smt_interval                      50000
% 1.19/1.02  
% 1.19/1.02  ------ Superposition Simplification Setup
% 1.19/1.02  
% 1.19/1.02  --sup_indices_passive                   []
% 1.19/1.02  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 1.19/1.02  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 1.19/1.02  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 1.19/1.02  --sup_full_triv                         [TrivRules;PropSubs]
% 1.19/1.02  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 1.19/1.02  --sup_full_bw                           [BwDemod]
% 1.19/1.02  --sup_immed_triv                        [TrivRules]
% 1.19/1.02  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 1.19/1.02  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 1.19/1.02  --sup_immed_bw_main                     []
% 1.19/1.02  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 1.19/1.02  --sup_input_triv                        [Unflattening;TrivRules]
% 1.19/1.02  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 1.19/1.02  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 1.19/1.02  
% 1.19/1.02  ------ Combination Options
% 1.19/1.02  
% 1.19/1.02  --comb_res_mult                         3
% 1.19/1.02  --comb_sup_mult                         2
% 1.19/1.02  --comb_inst_mult                        10
% 1.19/1.02  
% 1.19/1.02  ------ Debug Options
% 1.19/1.02  
% 1.19/1.02  --dbg_backtrace                         false
% 1.19/1.02  --dbg_dump_prop_clauses                 false
% 1.19/1.02  --dbg_dump_prop_clauses_file            -
% 1.19/1.02  --dbg_out_stat                          false
% 1.19/1.02  ------ Parsing...
% 1.19/1.02  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 1.19/1.02  
% 1.19/1.02  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe:1:0s pe:2:0s pe_e  sf_s  rm: 2 0s  sf_e  pe_s  pe_e 
% 1.19/1.02  
% 1.19/1.02  ------ Preprocessing... gs_s  sp: 1 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 1.19/1.02  
% 1.19/1.02  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 1.19/1.02  ------ Proving...
% 1.19/1.02  ------ Problem Properties 
% 1.19/1.02  
% 1.19/1.02  
% 1.19/1.02  clauses                                 11
% 1.19/1.02  conjectures                             2
% 1.19/1.02  EPR                                     1
% 1.19/1.02  Horn                                    11
% 1.19/1.02  unary                                   3
% 1.19/1.02  binary                                  4
% 1.19/1.02  lits                                    23
% 1.19/1.02  lits eq                                 4
% 1.19/1.02  fd_pure                                 0
% 1.19/1.02  fd_pseudo                               0
% 1.19/1.02  fd_cond                                 0
% 1.19/1.02  fd_pseudo_cond                          0
% 1.19/1.02  AC symbols                              0
% 1.19/1.02  
% 1.19/1.02  ------ Schedule dynamic 5 is on 
% 1.19/1.02  
% 1.19/1.02  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" Time Limit: 10.
% 1.19/1.02  
% 1.19/1.02  
% 1.19/1.02  ------ 
% 1.19/1.02  Current options:
% 1.19/1.02  ------ 
% 1.19/1.02  
% 1.19/1.02  ------ Input Options
% 1.19/1.02  
% 1.19/1.02  --out_options                           all
% 1.19/1.02  --tptp_safe_out                         true
% 1.19/1.02  --problem_path                          ""
% 1.19/1.02  --include_path                          ""
% 1.19/1.02  --clausifier                            res/vclausify_rel
% 1.19/1.02  --clausifier_options                    --mode clausify
% 1.19/1.02  --stdin                                 false
% 1.19/1.02  --stats_out                             all
% 1.19/1.02  
% 1.19/1.02  ------ General Options
% 1.19/1.02  
% 1.19/1.02  --fof                                   false
% 1.19/1.02  --time_out_real                         305.
% 1.19/1.02  --time_out_virtual                      -1.
% 1.19/1.02  --symbol_type_check                     false
% 1.19/1.02  --clausify_out                          false
% 1.19/1.02  --sig_cnt_out                           false
% 1.19/1.02  --trig_cnt_out                          false
% 1.19/1.02  --trig_cnt_out_tolerance                1.
% 1.19/1.02  --trig_cnt_out_sk_spl                   false
% 1.19/1.02  --abstr_cl_out                          false
% 1.19/1.02  
% 1.19/1.02  ------ Global Options
% 1.19/1.02  
% 1.19/1.02  --schedule                              default
% 1.19/1.02  --add_important_lit                     false
% 1.19/1.02  --prop_solver_per_cl                    1000
% 1.19/1.02  --min_unsat_core                        false
% 1.19/1.02  --soft_assumptions                      false
% 1.19/1.02  --soft_lemma_size                       3
% 1.19/1.02  --prop_impl_unit_size                   0
% 1.19/1.02  --prop_impl_unit                        []
% 1.19/1.02  --share_sel_clauses                     true
% 1.19/1.02  --reset_solvers                         false
% 1.19/1.02  --bc_imp_inh                            [conj_cone]
% 1.19/1.02  --conj_cone_tolerance                   3.
% 1.19/1.02  --extra_neg_conj                        none
% 1.19/1.02  --large_theory_mode                     true
% 1.19/1.02  --prolific_symb_bound                   200
% 1.19/1.02  --lt_threshold                          2000
% 1.19/1.02  --clause_weak_htbl                      true
% 1.19/1.02  --gc_record_bc_elim                     false
% 1.19/1.02  
% 1.19/1.02  ------ Preprocessing Options
% 1.19/1.02  
% 1.19/1.02  --preprocessing_flag                    true
% 1.19/1.02  --time_out_prep_mult                    0.1
% 1.19/1.02  --splitting_mode                        input
% 1.19/1.02  --splitting_grd                         true
% 1.19/1.02  --splitting_cvd                         false
% 1.19/1.02  --splitting_cvd_svl                     false
% 1.19/1.02  --splitting_nvd                         32
% 1.19/1.02  --sub_typing                            true
% 1.19/1.02  --prep_gs_sim                           true
% 1.19/1.02  --prep_unflatten                        true
% 1.19/1.02  --prep_res_sim                          true
% 1.19/1.02  --prep_upred                            true
% 1.19/1.02  --prep_sem_filter                       exhaustive
% 1.19/1.02  --prep_sem_filter_out                   false
% 1.19/1.02  --pred_elim                             true
% 1.19/1.02  --res_sim_input                         true
% 1.19/1.02  --eq_ax_congr_red                       true
% 1.19/1.02  --pure_diseq_elim                       true
% 1.19/1.02  --brand_transform                       false
% 1.19/1.02  --non_eq_to_eq                          false
% 1.19/1.02  --prep_def_merge                        true
% 1.19/1.02  --prep_def_merge_prop_impl              false
% 1.19/1.02  --prep_def_merge_mbd                    true
% 1.19/1.02  --prep_def_merge_tr_red                 false
% 1.19/1.02  --prep_def_merge_tr_cl                  false
% 1.19/1.02  --smt_preprocessing                     true
% 1.19/1.02  --smt_ac_axioms                         fast
% 1.19/1.02  --preprocessed_out                      false
% 1.19/1.02  --preprocessed_stats                    false
% 1.19/1.02  
% 1.19/1.02  ------ Abstraction refinement Options
% 1.19/1.02  
% 1.19/1.02  --abstr_ref                             []
% 1.19/1.02  --abstr_ref_prep                        false
% 1.19/1.02  --abstr_ref_until_sat                   false
% 1.19/1.02  --abstr_ref_sig_restrict                funpre
% 1.19/1.02  --abstr_ref_af_restrict_to_split_sk     false
% 1.19/1.02  --abstr_ref_under                       []
% 1.19/1.02  
% 1.19/1.02  ------ SAT Options
% 1.19/1.02  
% 1.19/1.02  --sat_mode                              false
% 1.19/1.02  --sat_fm_restart_options                ""
% 1.19/1.02  --sat_gr_def                            false
% 1.19/1.02  --sat_epr_types                         true
% 1.19/1.02  --sat_non_cyclic_types                  false
% 1.19/1.02  --sat_finite_models                     false
% 1.19/1.02  --sat_fm_lemmas                         false
% 1.19/1.02  --sat_fm_prep                           false
% 1.19/1.02  --sat_fm_uc_incr                        true
% 1.19/1.02  --sat_out_model                         small
% 1.19/1.02  --sat_out_clauses                       false
% 1.19/1.02  
% 1.19/1.02  ------ QBF Options
% 1.19/1.02  
% 1.19/1.02  --qbf_mode                              false
% 1.19/1.02  --qbf_elim_univ                         false
% 1.19/1.02  --qbf_dom_inst                          none
% 1.19/1.02  --qbf_dom_pre_inst                      false
% 1.19/1.02  --qbf_sk_in                             false
% 1.19/1.02  --qbf_pred_elim                         true
% 1.19/1.02  --qbf_split                             512
% 1.19/1.02  
% 1.19/1.02  ------ BMC1 Options
% 1.19/1.02  
% 1.19/1.02  --bmc1_incremental                      false
% 1.19/1.02  --bmc1_axioms                           reachable_all
% 1.19/1.02  --bmc1_min_bound                        0
% 1.19/1.02  --bmc1_max_bound                        -1
% 1.19/1.02  --bmc1_max_bound_default                -1
% 1.19/1.02  --bmc1_symbol_reachability              true
% 1.19/1.02  --bmc1_property_lemmas                  false
% 1.19/1.02  --bmc1_k_induction                      false
% 1.19/1.02  --bmc1_non_equiv_states                 false
% 1.19/1.02  --bmc1_deadlock                         false
% 1.19/1.02  --bmc1_ucm                              false
% 1.19/1.02  --bmc1_add_unsat_core                   none
% 1.19/1.02  --bmc1_unsat_core_children              false
% 1.19/1.02  --bmc1_unsat_core_extrapolate_axioms    false
% 1.19/1.02  --bmc1_out_stat                         full
% 1.19/1.02  --bmc1_ground_init                      false
% 1.19/1.02  --bmc1_pre_inst_next_state              false
% 1.19/1.02  --bmc1_pre_inst_state                   false
% 1.19/1.02  --bmc1_pre_inst_reach_state             false
% 1.19/1.02  --bmc1_out_unsat_core                   false
% 1.19/1.02  --bmc1_aig_witness_out                  false
% 1.19/1.02  --bmc1_verbose                          false
% 1.19/1.02  --bmc1_dump_clauses_tptp                false
% 1.19/1.02  --bmc1_dump_unsat_core_tptp             false
% 1.19/1.02  --bmc1_dump_file                        -
% 1.19/1.02  --bmc1_ucm_expand_uc_limit              128
% 1.19/1.02  --bmc1_ucm_n_expand_iterations          6
% 1.19/1.02  --bmc1_ucm_extend_mode                  1
% 1.19/1.02  --bmc1_ucm_init_mode                    2
% 1.19/1.02  --bmc1_ucm_cone_mode                    none
% 1.19/1.02  --bmc1_ucm_reduced_relation_type        0
% 1.19/1.02  --bmc1_ucm_relax_model                  4
% 1.19/1.02  --bmc1_ucm_full_tr_after_sat            true
% 1.19/1.02  --bmc1_ucm_expand_neg_assumptions       false
% 1.19/1.02  --bmc1_ucm_layered_model                none
% 1.19/1.02  --bmc1_ucm_max_lemma_size               10
% 1.19/1.02  
% 1.19/1.02  ------ AIG Options
% 1.19/1.02  
% 1.19/1.02  --aig_mode                              false
% 1.19/1.02  
% 1.19/1.02  ------ Instantiation Options
% 1.19/1.02  
% 1.19/1.02  --instantiation_flag                    true
% 1.19/1.02  --inst_sos_flag                         false
% 1.19/1.02  --inst_sos_phase                        true
% 1.19/1.02  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 1.19/1.02  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 1.19/1.02  --inst_lit_sel_side                     none
% 1.19/1.02  --inst_solver_per_active                1400
% 1.19/1.02  --inst_solver_calls_frac                1.
% 1.19/1.02  --inst_passive_queue_type               priority_queues
% 1.19/1.02  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 1.19/1.02  --inst_passive_queues_freq              [25;2]
% 1.19/1.02  --inst_dismatching                      true
% 1.19/1.02  --inst_eager_unprocessed_to_passive     true
% 1.19/1.02  --inst_prop_sim_given                   true
% 1.19/1.02  --inst_prop_sim_new                     false
% 1.19/1.02  --inst_subs_new                         false
% 1.19/1.02  --inst_eq_res_simp                      false
% 1.19/1.02  --inst_subs_given                       false
% 1.19/1.02  --inst_orphan_elimination               true
% 1.19/1.02  --inst_learning_loop_flag               true
% 1.19/1.02  --inst_learning_start                   3000
% 1.19/1.02  --inst_learning_factor                  2
% 1.19/1.02  --inst_start_prop_sim_after_learn       3
% 1.19/1.02  --inst_sel_renew                        solver
% 1.19/1.02  --inst_lit_activity_flag                true
% 1.19/1.02  --inst_restr_to_given                   false
% 1.19/1.02  --inst_activity_threshold               500
% 1.19/1.02  --inst_out_proof                        true
% 1.19/1.02  
% 1.19/1.02  ------ Resolution Options
% 1.19/1.02  
% 1.19/1.02  --resolution_flag                       false
% 1.19/1.02  --res_lit_sel                           adaptive
% 1.19/1.02  --res_lit_sel_side                      none
% 1.19/1.02  --res_ordering                          kbo
% 1.19/1.02  --res_to_prop_solver                    active
% 1.19/1.02  --res_prop_simpl_new                    false
% 1.19/1.02  --res_prop_simpl_given                  true
% 1.19/1.02  --res_passive_queue_type                priority_queues
% 1.19/1.02  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 1.19/1.02  --res_passive_queues_freq               [15;5]
% 1.19/1.02  --res_forward_subs                      full
% 1.19/1.02  --res_backward_subs                     full
% 1.19/1.02  --res_forward_subs_resolution           true
% 1.19/1.02  --res_backward_subs_resolution          true
% 1.19/1.02  --res_orphan_elimination                true
% 1.19/1.02  --res_time_limit                        2.
% 1.19/1.02  --res_out_proof                         true
% 1.19/1.02  
% 1.19/1.02  ------ Superposition Options
% 1.19/1.02  
% 1.19/1.02  --superposition_flag                    true
% 1.19/1.02  --sup_passive_queue_type                priority_queues
% 1.19/1.02  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 1.19/1.02  --sup_passive_queues_freq               [8;1;4]
% 1.19/1.02  --demod_completeness_check              fast
% 1.19/1.02  --demod_use_ground                      true
% 1.19/1.02  --sup_to_prop_solver                    passive
% 1.19/1.02  --sup_prop_simpl_new                    true
% 1.19/1.02  --sup_prop_simpl_given                  true
% 1.19/1.02  --sup_fun_splitting                     false
% 1.19/1.02  --sup_smt_interval                      50000
% 1.19/1.02  
% 1.19/1.02  ------ Superposition Simplification Setup
% 1.19/1.02  
% 1.19/1.02  --sup_indices_passive                   []
% 1.19/1.02  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 1.19/1.02  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 1.19/1.02  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 1.19/1.02  --sup_full_triv                         [TrivRules;PropSubs]
% 1.19/1.02  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 1.19/1.02  --sup_full_bw                           [BwDemod]
% 1.19/1.02  --sup_immed_triv                        [TrivRules]
% 1.19/1.02  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 1.19/1.02  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 1.19/1.02  --sup_immed_bw_main                     []
% 1.19/1.02  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 1.19/1.02  --sup_input_triv                        [Unflattening;TrivRules]
% 1.19/1.02  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 1.19/1.02  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 1.19/1.02  
% 1.19/1.02  ------ Combination Options
% 1.19/1.02  
% 1.19/1.02  --comb_res_mult                         3
% 1.19/1.02  --comb_sup_mult                         2
% 1.19/1.02  --comb_inst_mult                        10
% 1.19/1.02  
% 1.19/1.02  ------ Debug Options
% 1.19/1.02  
% 1.19/1.02  --dbg_backtrace                         false
% 1.19/1.02  --dbg_dump_prop_clauses                 false
% 1.19/1.02  --dbg_dump_prop_clauses_file            -
% 1.19/1.02  --dbg_out_stat                          false
% 1.19/1.02  
% 1.19/1.02  
% 1.19/1.02  
% 1.19/1.02  
% 1.19/1.02  ------ Proving...
% 1.19/1.02  
% 1.19/1.02  
% 1.19/1.02  % SZS status Theorem for theBenchmark.p
% 1.19/1.02  
% 1.19/1.02  % SZS output start CNFRefutation for theBenchmark.p
% 1.19/1.02  
% 1.19/1.02  fof(f10,conjecture,(
% 1.19/1.02    ! [X0,X1,X2,X3] : (m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) => (r1_tarski(X1,X2) => r2_relset_1(X1,X0,k5_relset_1(X1,X0,X3,X2),X3)))),
% 1.19/1.02    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 1.19/1.02  
% 1.19/1.02  fof(f11,negated_conjecture,(
% 1.19/1.02    ~! [X0,X1,X2,X3] : (m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) => (r1_tarski(X1,X2) => r2_relset_1(X1,X0,k5_relset_1(X1,X0,X3,X2),X3)))),
% 1.19/1.02    inference(negated_conjecture,[],[f10])).
% 1.19/1.02  
% 1.19/1.02  fof(f23,plain,(
% 1.19/1.02    ? [X0,X1,X2,X3] : ((~r2_relset_1(X1,X0,k5_relset_1(X1,X0,X3,X2),X3) & r1_tarski(X1,X2)) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))))),
% 1.19/1.02    inference(ennf_transformation,[],[f11])).
% 1.19/1.02  
% 1.19/1.02  fof(f24,plain,(
% 1.19/1.02    ? [X0,X1,X2,X3] : (~r2_relset_1(X1,X0,k5_relset_1(X1,X0,X3,X2),X3) & r1_tarski(X1,X2) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))))),
% 1.19/1.02    inference(flattening,[],[f23])).
% 1.19/1.02  
% 1.19/1.02  fof(f26,plain,(
% 1.19/1.02    ? [X0,X1,X2,X3] : (~r2_relset_1(X1,X0,k5_relset_1(X1,X0,X3,X2),X3) & r1_tarski(X1,X2) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0)))) => (~r2_relset_1(sK1,sK0,k5_relset_1(sK1,sK0,sK3,sK2),sK3) & r1_tarski(sK1,sK2) & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))))),
% 1.19/1.02    introduced(choice_axiom,[])).
% 1.19/1.02  
% 1.19/1.02  fof(f27,plain,(
% 1.19/1.02    ~r2_relset_1(sK1,sK0,k5_relset_1(sK1,sK0,sK3,sK2),sK3) & r1_tarski(sK1,sK2) & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))),
% 1.19/1.02    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3])],[f24,f26])).
% 1.19/1.02  
% 1.19/1.02  fof(f39,plain,(
% 1.19/1.02    r1_tarski(sK1,sK2)),
% 1.19/1.02    inference(cnf_transformation,[],[f27])).
% 1.19/1.02  
% 1.19/1.02  fof(f38,plain,(
% 1.19/1.02    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))),
% 1.19/1.02    inference(cnf_transformation,[],[f27])).
% 1.19/1.02  
% 1.19/1.02  fof(f7,axiom,(
% 1.19/1.02    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => (v5_relat_1(X2,X1) & v4_relat_1(X2,X0)))),
% 1.19/1.02    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 1.19/1.02  
% 1.19/1.02  fof(f12,plain,(
% 1.19/1.02    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => v4_relat_1(X2,X0))),
% 1.19/1.02    inference(pure_predicate_removal,[],[f7])).
% 1.19/1.02  
% 1.19/1.02  fof(f19,plain,(
% 1.19/1.02    ! [X0,X1,X2] : (v4_relat_1(X2,X0) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 1.19/1.02    inference(ennf_transformation,[],[f12])).
% 1.19/1.02  
% 1.19/1.02  fof(f35,plain,(
% 1.19/1.02    ( ! [X2,X0,X1] : (v4_relat_1(X2,X0) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 1.19/1.02    inference(cnf_transformation,[],[f19])).
% 1.19/1.02  
% 1.19/1.02  fof(f4,axiom,(
% 1.19/1.02    ! [X0,X1] : (v1_relat_1(X1) => (v4_relat_1(X1,X0) <=> r1_tarski(k1_relat_1(X1),X0)))),
% 1.19/1.02    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 1.19/1.02  
% 1.19/1.02  fof(f16,plain,(
% 1.19/1.02    ! [X0,X1] : ((v4_relat_1(X1,X0) <=> r1_tarski(k1_relat_1(X1),X0)) | ~v1_relat_1(X1))),
% 1.19/1.02    inference(ennf_transformation,[],[f4])).
% 1.19/1.02  
% 1.19/1.02  fof(f25,plain,(
% 1.19/1.02    ! [X0,X1] : (((v4_relat_1(X1,X0) | ~r1_tarski(k1_relat_1(X1),X0)) & (r1_tarski(k1_relat_1(X1),X0) | ~v4_relat_1(X1,X0))) | ~v1_relat_1(X1))),
% 1.19/1.02    inference(nnf_transformation,[],[f16])).
% 1.19/1.02  
% 1.19/1.02  fof(f31,plain,(
% 1.19/1.02    ( ! [X0,X1] : (r1_tarski(k1_relat_1(X1),X0) | ~v4_relat_1(X1,X0) | ~v1_relat_1(X1)) )),
% 1.19/1.02    inference(cnf_transformation,[],[f25])).
% 1.19/1.02  
% 1.19/1.02  fof(f3,axiom,(
% 1.19/1.02    ! [X0] : (v1_relat_1(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => v1_relat_1(X1)))),
% 1.19/1.02    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 1.19/1.02  
% 1.19/1.02  fof(f15,plain,(
% 1.19/1.02    ! [X0] : (! [X1] : (v1_relat_1(X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) | ~v1_relat_1(X0))),
% 1.19/1.02    inference(ennf_transformation,[],[f3])).
% 1.19/1.02  
% 1.19/1.02  fof(f30,plain,(
% 1.19/1.02    ( ! [X0,X1] : (v1_relat_1(X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0)) | ~v1_relat_1(X0)) )),
% 1.19/1.02    inference(cnf_transformation,[],[f15])).
% 1.19/1.02  
% 1.19/1.02  fof(f5,axiom,(
% 1.19/1.02    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1))),
% 1.19/1.02    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 1.19/1.02  
% 1.19/1.02  fof(f33,plain,(
% 1.19/1.02    ( ! [X0,X1] : (v1_relat_1(k2_zfmisc_1(X0,X1))) )),
% 1.19/1.02    inference(cnf_transformation,[],[f5])).
% 1.19/1.02  
% 1.19/1.02  fof(f2,axiom,(
% 1.19/1.02    ! [X0,X1] : (r1_tarski(X0,X1) => k2_xboole_0(X0,X1) = X1)),
% 1.19/1.02    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 1.19/1.02  
% 1.19/1.02  fof(f14,plain,(
% 1.19/1.02    ! [X0,X1] : (k2_xboole_0(X0,X1) = X1 | ~r1_tarski(X0,X1))),
% 1.19/1.02    inference(ennf_transformation,[],[f2])).
% 1.19/1.02  
% 1.19/1.02  fof(f29,plain,(
% 1.19/1.02    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = X1 | ~r1_tarski(X0,X1)) )),
% 1.19/1.02    inference(cnf_transformation,[],[f14])).
% 1.19/1.02  
% 1.19/1.02  fof(f1,axiom,(
% 1.19/1.02    ! [X0,X1,X2] : (r1_tarski(k2_xboole_0(X0,X1),X2) => r1_tarski(X0,X2))),
% 1.19/1.02    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 1.19/1.02  
% 1.19/1.02  fof(f13,plain,(
% 1.19/1.02    ! [X0,X1,X2] : (r1_tarski(X0,X2) | ~r1_tarski(k2_xboole_0(X0,X1),X2))),
% 1.19/1.02    inference(ennf_transformation,[],[f1])).
% 1.19/1.02  
% 1.19/1.02  fof(f28,plain,(
% 1.19/1.02    ( ! [X2,X0,X1] : (r1_tarski(X0,X2) | ~r1_tarski(k2_xboole_0(X0,X1),X2)) )),
% 1.19/1.02    inference(cnf_transformation,[],[f13])).
% 1.19/1.02  
% 1.19/1.02  fof(f6,axiom,(
% 1.19/1.02    ! [X0,X1] : (v1_relat_1(X1) => (r1_tarski(k1_relat_1(X1),X0) => k7_relat_1(X1,X0) = X1))),
% 1.19/1.02    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 1.19/1.02  
% 1.19/1.02  fof(f17,plain,(
% 1.19/1.02    ! [X0,X1] : ((k7_relat_1(X1,X0) = X1 | ~r1_tarski(k1_relat_1(X1),X0)) | ~v1_relat_1(X1))),
% 1.19/1.02    inference(ennf_transformation,[],[f6])).
% 1.19/1.02  
% 1.19/1.02  fof(f18,plain,(
% 1.19/1.02    ! [X0,X1] : (k7_relat_1(X1,X0) = X1 | ~r1_tarski(k1_relat_1(X1),X0) | ~v1_relat_1(X1))),
% 1.19/1.02    inference(flattening,[],[f17])).
% 1.19/1.02  
% 1.19/1.02  fof(f34,plain,(
% 1.19/1.02    ( ! [X0,X1] : (k7_relat_1(X1,X0) = X1 | ~r1_tarski(k1_relat_1(X1),X0) | ~v1_relat_1(X1)) )),
% 1.19/1.02    inference(cnf_transformation,[],[f18])).
% 1.19/1.02  
% 1.19/1.02  fof(f8,axiom,(
% 1.19/1.02    ! [X0,X1,X2,X3] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k7_relat_1(X2,X3) = k5_relset_1(X0,X1,X2,X3))),
% 1.19/1.02    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 1.19/1.02  
% 1.19/1.02  fof(f20,plain,(
% 1.19/1.02    ! [X0,X1,X2,X3] : (k7_relat_1(X2,X3) = k5_relset_1(X0,X1,X2,X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 1.19/1.02    inference(ennf_transformation,[],[f8])).
% 1.19/1.02  
% 1.19/1.02  fof(f36,plain,(
% 1.19/1.02    ( ! [X2,X0,X3,X1] : (k7_relat_1(X2,X3) = k5_relset_1(X0,X1,X2,X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 1.19/1.02    inference(cnf_transformation,[],[f20])).
% 1.19/1.02  
% 1.19/1.02  fof(f9,axiom,(
% 1.19/1.02    ! [X0,X1,X2,X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) => r2_relset_1(X0,X1,X2,X2))),
% 1.19/1.02    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 1.19/1.02  
% 1.19/1.02  fof(f21,plain,(
% 1.19/1.02    ! [X0,X1,X2,X3] : (r2_relset_1(X0,X1,X2,X2) | (~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))))),
% 1.19/1.02    inference(ennf_transformation,[],[f9])).
% 1.19/1.02  
% 1.19/1.02  fof(f22,plain,(
% 1.19/1.02    ! [X0,X1,X2,X3] : (r2_relset_1(X0,X1,X2,X2) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 1.19/1.02    inference(flattening,[],[f21])).
% 1.19/1.02  
% 1.19/1.02  fof(f37,plain,(
% 1.19/1.02    ( ! [X2,X0,X3,X1] : (r2_relset_1(X0,X1,X2,X2) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 1.19/1.02    inference(cnf_transformation,[],[f22])).
% 1.19/1.02  
% 1.19/1.02  fof(f40,plain,(
% 1.19/1.02    ~r2_relset_1(sK1,sK0,k5_relset_1(sK1,sK0,sK3,sK2),sK3)),
% 1.19/1.02    inference(cnf_transformation,[],[f27])).
% 1.19/1.02  
% 1.19/1.02  cnf(c_11,negated_conjecture,
% 1.19/1.02      ( r1_tarski(sK1,sK2) ),
% 1.19/1.02      inference(cnf_transformation,[],[f39]) ).
% 1.19/1.02  
% 1.19/1.02  cnf(c_485,plain,
% 1.19/1.02      ( r1_tarski(sK1,sK2) = iProver_top ),
% 1.19/1.02      inference(predicate_to_equality,[status(thm)],[c_11]) ).
% 1.19/1.02  
% 1.19/1.02  cnf(c_12,negated_conjecture,
% 1.19/1.02      ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) ),
% 1.19/1.02      inference(cnf_transformation,[],[f38]) ).
% 1.19/1.02  
% 1.19/1.02  cnf(c_484,plain,
% 1.19/1.02      ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) = iProver_top ),
% 1.19/1.02      inference(predicate_to_equality,[status(thm)],[c_12]) ).
% 1.19/1.02  
% 1.19/1.02  cnf(c_7,plain,
% 1.19/1.02      ( v4_relat_1(X0,X1)
% 1.19/1.02      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) ),
% 1.19/1.02      inference(cnf_transformation,[],[f35]) ).
% 1.19/1.02  
% 1.19/1.02  cnf(c_4,plain,
% 1.19/1.02      ( ~ v4_relat_1(X0,X1)
% 1.19/1.02      | r1_tarski(k1_relat_1(X0),X1)
% 1.19/1.02      | ~ v1_relat_1(X0) ),
% 1.19/1.02      inference(cnf_transformation,[],[f31]) ).
% 1.19/1.02  
% 1.19/1.02  cnf(c_168,plain,
% 1.19/1.02      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 1.19/1.02      | r1_tarski(k1_relat_1(X0),X1)
% 1.19/1.02      | ~ v1_relat_1(X0) ),
% 1.19/1.02      inference(resolution,[status(thm)],[c_7,c_4]) ).
% 1.19/1.02  
% 1.19/1.02  cnf(c_481,plain,
% 1.19/1.02      ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) != iProver_top
% 1.19/1.02      | r1_tarski(k1_relat_1(X0),X1) = iProver_top
% 1.19/1.02      | v1_relat_1(X0) != iProver_top ),
% 1.19/1.02      inference(predicate_to_equality,[status(thm)],[c_168]) ).
% 1.19/1.02  
% 1.19/1.02  cnf(c_783,plain,
% 1.19/1.02      ( r1_tarski(k1_relat_1(sK3),sK1) = iProver_top
% 1.19/1.02      | v1_relat_1(sK3) != iProver_top ),
% 1.19/1.02      inference(superposition,[status(thm)],[c_484,c_481]) ).
% 1.19/1.02  
% 1.19/1.02  cnf(c_13,plain,
% 1.19/1.02      ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) = iProver_top ),
% 1.19/1.02      inference(predicate_to_equality,[status(thm)],[c_12]) ).
% 1.19/1.02  
% 1.19/1.02  cnf(c_2,plain,
% 1.19/1.02      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
% 1.19/1.02      | ~ v1_relat_1(X1)
% 1.19/1.02      | v1_relat_1(X0) ),
% 1.19/1.02      inference(cnf_transformation,[],[f30]) ).
% 1.19/1.02  
% 1.19/1.02  cnf(c_563,plain,
% 1.19/1.02      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 1.19/1.02      | v1_relat_1(X0)
% 1.19/1.02      | ~ v1_relat_1(k2_zfmisc_1(X1,X2)) ),
% 1.19/1.02      inference(instantiation,[status(thm)],[c_2]) ).
% 1.19/1.02  
% 1.19/1.02  cnf(c_636,plain,
% 1.19/1.02      ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
% 1.19/1.02      | ~ v1_relat_1(k2_zfmisc_1(sK1,sK0))
% 1.19/1.02      | v1_relat_1(sK3) ),
% 1.19/1.02      inference(instantiation,[status(thm)],[c_563]) ).
% 1.19/1.02  
% 1.19/1.02  cnf(c_637,plain,
% 1.19/1.02      ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) != iProver_top
% 1.19/1.02      | v1_relat_1(k2_zfmisc_1(sK1,sK0)) != iProver_top
% 1.19/1.02      | v1_relat_1(sK3) = iProver_top ),
% 1.19/1.02      inference(predicate_to_equality,[status(thm)],[c_636]) ).
% 1.19/1.02  
% 1.19/1.02  cnf(c_5,plain,
% 1.19/1.02      ( v1_relat_1(k2_zfmisc_1(X0,X1)) ),
% 1.19/1.02      inference(cnf_transformation,[],[f33]) ).
% 1.19/1.02  
% 1.19/1.02  cnf(c_741,plain,
% 1.19/1.02      ( v1_relat_1(k2_zfmisc_1(sK1,sK0)) ),
% 1.19/1.02      inference(instantiation,[status(thm)],[c_5]) ).
% 1.19/1.02  
% 1.19/1.02  cnf(c_742,plain,
% 1.19/1.02      ( v1_relat_1(k2_zfmisc_1(sK1,sK0)) = iProver_top ),
% 1.19/1.02      inference(predicate_to_equality,[status(thm)],[c_741]) ).
% 1.19/1.02  
% 1.19/1.02  cnf(c_994,plain,
% 1.19/1.02      ( r1_tarski(k1_relat_1(sK3),sK1) = iProver_top ),
% 1.19/1.02      inference(global_propositional_subsumption,
% 1.19/1.02                [status(thm)],
% 1.19/1.02                [c_783,c_13,c_637,c_742]) ).
% 1.19/1.02  
% 1.19/1.02  cnf(c_1,plain,
% 1.19/1.02      ( ~ r1_tarski(X0,X1) | k2_xboole_0(X0,X1) = X1 ),
% 1.19/1.02      inference(cnf_transformation,[],[f29]) ).
% 1.19/1.02  
% 1.19/1.02  cnf(c_490,plain,
% 1.19/1.02      ( k2_xboole_0(X0,X1) = X1 | r1_tarski(X0,X1) != iProver_top ),
% 1.19/1.02      inference(predicate_to_equality,[status(thm)],[c_1]) ).
% 1.19/1.02  
% 1.19/1.02  cnf(c_999,plain,
% 1.19/1.02      ( k2_xboole_0(k1_relat_1(sK3),sK1) = sK1 ),
% 1.19/1.02      inference(superposition,[status(thm)],[c_994,c_490]) ).
% 1.19/1.02  
% 1.19/1.02  cnf(c_0,plain,
% 1.19/1.02      ( r1_tarski(X0,X1) | ~ r1_tarski(k2_xboole_0(X0,X2),X1) ),
% 1.19/1.02      inference(cnf_transformation,[],[f28]) ).
% 1.19/1.02  
% 1.19/1.02  cnf(c_491,plain,
% 1.19/1.02      ( r1_tarski(X0,X1) = iProver_top
% 1.19/1.02      | r1_tarski(k2_xboole_0(X0,X2),X1) != iProver_top ),
% 1.19/1.02      inference(predicate_to_equality,[status(thm)],[c_0]) ).
% 1.19/1.02  
% 1.19/1.02  cnf(c_1066,plain,
% 1.19/1.02      ( r1_tarski(k1_relat_1(sK3),X0) = iProver_top
% 1.19/1.02      | r1_tarski(sK1,X0) != iProver_top ),
% 1.19/1.02      inference(superposition,[status(thm)],[c_999,c_491]) ).
% 1.19/1.02  
% 1.19/1.02  cnf(c_6,plain,
% 1.19/1.02      ( ~ r1_tarski(k1_relat_1(X0),X1)
% 1.19/1.02      | ~ v1_relat_1(X0)
% 1.19/1.02      | k7_relat_1(X0,X1) = X0 ),
% 1.19/1.02      inference(cnf_transformation,[],[f34]) ).
% 1.19/1.02  
% 1.19/1.02  cnf(c_487,plain,
% 1.19/1.02      ( k7_relat_1(X0,X1) = X0
% 1.19/1.02      | r1_tarski(k1_relat_1(X0),X1) != iProver_top
% 1.19/1.02      | v1_relat_1(X0) != iProver_top ),
% 1.19/1.02      inference(predicate_to_equality,[status(thm)],[c_6]) ).
% 1.19/1.02  
% 1.19/1.02  cnf(c_1249,plain,
% 1.19/1.02      ( k7_relat_1(sK3,X0) = sK3
% 1.19/1.02      | r1_tarski(sK1,X0) != iProver_top
% 1.19/1.02      | v1_relat_1(sK3) != iProver_top ),
% 1.19/1.02      inference(superposition,[status(thm)],[c_1066,c_487]) ).
% 1.19/1.02  
% 1.19/1.02  cnf(c_1381,plain,
% 1.19/1.02      ( r1_tarski(sK1,X0) != iProver_top | k7_relat_1(sK3,X0) = sK3 ),
% 1.19/1.02      inference(global_propositional_subsumption,
% 1.19/1.02                [status(thm)],
% 1.19/1.02                [c_1249,c_13,c_637,c_742]) ).
% 1.19/1.02  
% 1.19/1.02  cnf(c_1382,plain,
% 1.19/1.02      ( k7_relat_1(sK3,X0) = sK3 | r1_tarski(sK1,X0) != iProver_top ),
% 1.19/1.02      inference(renaming,[status(thm)],[c_1381]) ).
% 1.19/1.02  
% 1.19/1.02  cnf(c_1387,plain,
% 1.19/1.02      ( k7_relat_1(sK3,sK2) = sK3 ),
% 1.19/1.02      inference(superposition,[status(thm)],[c_485,c_1382]) ).
% 1.19/1.02  
% 1.19/1.02  cnf(c_8,plain,
% 1.19/1.02      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 1.19/1.02      | k5_relset_1(X1,X2,X0,X3) = k7_relat_1(X0,X3) ),
% 1.19/1.02      inference(cnf_transformation,[],[f36]) ).
% 1.19/1.02  
% 1.19/1.02  cnf(c_486,plain,
% 1.19/1.02      ( k5_relset_1(X0,X1,X2,X3) = k7_relat_1(X2,X3)
% 1.19/1.02      | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
% 1.19/1.02      inference(predicate_to_equality,[status(thm)],[c_8]) ).
% 1.19/1.02  
% 1.19/1.02  cnf(c_846,plain,
% 1.19/1.02      ( k5_relset_1(sK1,sK0,sK3,X0) = k7_relat_1(sK3,X0) ),
% 1.19/1.02      inference(superposition,[status(thm)],[c_484,c_486]) ).
% 1.19/1.02  
% 1.19/1.02  cnf(c_9,plain,
% 1.19/1.02      ( r2_relset_1(X0,X1,X2,X2)
% 1.19/1.02      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
% 1.19/1.02      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ),
% 1.19/1.02      inference(cnf_transformation,[],[f37]) ).
% 1.19/1.02  
% 1.19/1.02  cnf(c_10,negated_conjecture,
% 1.19/1.02      ( ~ r2_relset_1(sK1,sK0,k5_relset_1(sK1,sK0,sK3,sK2),sK3) ),
% 1.19/1.02      inference(cnf_transformation,[],[f40]) ).
% 1.19/1.02  
% 1.19/1.02  cnf(c_149,plain,
% 1.19/1.02      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 1.19/1.02      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 1.19/1.02      | k5_relset_1(sK1,sK0,sK3,sK2) != X0
% 1.19/1.02      | sK3 != X0
% 1.19/1.02      | sK0 != X2
% 1.19/1.02      | sK1 != X1 ),
% 1.19/1.02      inference(resolution_lifted,[status(thm)],[c_9,c_10]) ).
% 1.19/1.02  
% 1.19/1.02  cnf(c_150,plain,
% 1.19/1.02      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
% 1.19/1.02      | ~ m1_subset_1(k5_relset_1(sK1,sK0,sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
% 1.19/1.02      | sK3 != k5_relset_1(sK1,sK0,sK3,sK2) ),
% 1.19/1.02      inference(unflattening,[status(thm)],[c_149]) ).
% 1.19/1.02  
% 1.19/1.02  cnf(c_260,plain,
% 1.19/1.02      ( ~ m1_subset_1(k5_relset_1(sK1,sK0,sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
% 1.19/1.02      | sP0_iProver_split
% 1.19/1.02      | sK3 != k5_relset_1(sK1,sK0,sK3,sK2) ),
% 1.19/1.02      inference(splitting,
% 1.19/1.02                [splitting(split),new_symbols(definition,[])],
% 1.19/1.02                [c_150]) ).
% 1.19/1.02  
% 1.19/1.02  cnf(c_482,plain,
% 1.19/1.02      ( sK3 != k5_relset_1(sK1,sK0,sK3,sK2)
% 1.19/1.02      | m1_subset_1(k5_relset_1(sK1,sK0,sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) != iProver_top
% 1.19/1.02      | sP0_iProver_split = iProver_top ),
% 1.19/1.02      inference(predicate_to_equality,[status(thm)],[c_260]) ).
% 1.19/1.02  
% 1.19/1.02  cnf(c_259,plain,
% 1.19/1.02      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
% 1.19/1.02      | ~ sP0_iProver_split ),
% 1.19/1.02      inference(splitting,
% 1.19/1.02                [splitting(split),new_symbols(definition,[sP0_iProver_split])],
% 1.19/1.02                [c_150]) ).
% 1.19/1.02  
% 1.19/1.02  cnf(c_483,plain,
% 1.19/1.02      ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) != iProver_top
% 1.19/1.02      | sP0_iProver_split != iProver_top ),
% 1.19/1.02      inference(predicate_to_equality,[status(thm)],[c_259]) ).
% 1.19/1.02  
% 1.19/1.02  cnf(c_535,plain,
% 1.19/1.02      ( k5_relset_1(sK1,sK0,sK3,sK2) != sK3
% 1.19/1.02      | m1_subset_1(k5_relset_1(sK1,sK0,sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) != iProver_top ),
% 1.19/1.02      inference(forward_subsumption_resolution,
% 1.19/1.02                [status(thm)],
% 1.19/1.02                [c_482,c_483]) ).
% 1.19/1.02  
% 1.19/1.02  cnf(c_900,plain,
% 1.19/1.02      ( k7_relat_1(sK3,sK2) != sK3
% 1.19/1.02      | m1_subset_1(k7_relat_1(sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) != iProver_top ),
% 1.19/1.02      inference(demodulation,[status(thm)],[c_846,c_535]) ).
% 1.19/1.02  
% 1.19/1.02  cnf(c_262,plain,( X0 = X0 ),theory(equality) ).
% 1.19/1.02  
% 1.19/1.02  cnf(c_615,plain,
% 1.19/1.02      ( sK2 = sK2 ),
% 1.19/1.02      inference(instantiation,[status(thm)],[c_262]) ).
% 1.19/1.03  
% 1.19/1.03  cnf(c_784,plain,
% 1.19/1.03      ( r1_tarski(k1_relat_1(sK3),sK1) | ~ v1_relat_1(sK3) ),
% 1.19/1.03      inference(predicate_to_equality_rev,[status(thm)],[c_783]) ).
% 1.19/1.03  
% 1.19/1.03  cnf(c_652,plain,
% 1.19/1.03      ( ~ r1_tarski(k1_relat_1(sK3),X0)
% 1.19/1.03      | ~ v1_relat_1(sK3)
% 1.19/1.03      | k7_relat_1(sK3,X0) = sK3 ),
% 1.19/1.03      inference(instantiation,[status(thm)],[c_6]) ).
% 1.19/1.03  
% 1.19/1.03  cnf(c_792,plain,
% 1.19/1.03      ( ~ r1_tarski(k1_relat_1(sK3),sK2)
% 1.19/1.03      | ~ v1_relat_1(sK3)
% 1.19/1.03      | k7_relat_1(sK3,sK2) = sK3 ),
% 1.19/1.03      inference(instantiation,[status(thm)],[c_652]) ).
% 1.19/1.03  
% 1.19/1.03  cnf(c_915,plain,
% 1.19/1.03      ( ~ r1_tarski(k1_relat_1(sK3),sK1)
% 1.19/1.03      | k2_xboole_0(k1_relat_1(sK3),sK1) = sK1 ),
% 1.19/1.03      inference(instantiation,[status(thm)],[c_1]) ).
% 1.19/1.03  
% 1.19/1.03  cnf(c_678,plain,
% 1.19/1.03      ( r1_tarski(X0,sK2) | ~ r1_tarski(k2_xboole_0(X0,X1),sK2) ),
% 1.19/1.03      inference(instantiation,[status(thm)],[c_0]) ).
% 1.19/1.03  
% 1.19/1.03  cnf(c_958,plain,
% 1.19/1.03      ( ~ r1_tarski(k2_xboole_0(k1_relat_1(sK3),X0),sK2)
% 1.19/1.03      | r1_tarski(k1_relat_1(sK3),sK2) ),
% 1.19/1.03      inference(instantiation,[status(thm)],[c_678]) ).
% 1.19/1.03  
% 1.19/1.03  cnf(c_961,plain,
% 1.19/1.03      ( ~ r1_tarski(k2_xboole_0(k1_relat_1(sK3),sK1),sK2)
% 1.19/1.03      | r1_tarski(k1_relat_1(sK3),sK2) ),
% 1.19/1.03      inference(instantiation,[status(thm)],[c_958]) ).
% 1.19/1.03  
% 1.19/1.03  cnf(c_264,plain,
% 1.19/1.03      ( ~ r1_tarski(X0,X1) | r1_tarski(X2,X3) | X2 != X0 | X3 != X1 ),
% 1.19/1.03      theory(equality) ).
% 1.19/1.03  
% 1.19/1.03  cnf(c_585,plain,
% 1.19/1.03      ( r1_tarski(X0,X1) | ~ r1_tarski(sK1,sK2) | X1 != sK2 | X0 != sK1 ),
% 1.19/1.03      inference(instantiation,[status(thm)],[c_264]) ).
% 1.19/1.03  
% 1.19/1.03  cnf(c_614,plain,
% 1.19/1.03      ( r1_tarski(X0,sK2)
% 1.19/1.03      | ~ r1_tarski(sK1,sK2)
% 1.19/1.03      | X0 != sK1
% 1.19/1.03      | sK2 != sK2 ),
% 1.19/1.03      inference(instantiation,[status(thm)],[c_585]) ).
% 1.19/1.03  
% 1.19/1.03  cnf(c_677,plain,
% 1.19/1.03      ( r1_tarski(k2_xboole_0(X0,X1),sK2)
% 1.19/1.03      | ~ r1_tarski(sK1,sK2)
% 1.19/1.03      | k2_xboole_0(X0,X1) != sK1
% 1.19/1.03      | sK2 != sK2 ),
% 1.19/1.03      inference(instantiation,[status(thm)],[c_614]) ).
% 1.19/1.03  
% 1.19/1.03  cnf(c_1163,plain,
% 1.19/1.03      ( r1_tarski(k2_xboole_0(k1_relat_1(sK3),sK1),sK2)
% 1.19/1.03      | ~ r1_tarski(sK1,sK2)
% 1.19/1.03      | k2_xboole_0(k1_relat_1(sK3),sK1) != sK1
% 1.19/1.03      | sK2 != sK2 ),
% 1.19/1.03      inference(instantiation,[status(thm)],[c_677]) ).
% 1.19/1.03  
% 1.19/1.03  cnf(c_1173,plain,
% 1.19/1.03      ( m1_subset_1(k7_relat_1(sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) != iProver_top ),
% 1.19/1.03      inference(global_propositional_subsumption,
% 1.19/1.03                [status(thm)],
% 1.19/1.03                [c_900,c_12,c_11,c_615,c_636,c_741,c_784,c_792,c_915,
% 1.19/1.03                 c_961,c_1163]) ).
% 1.19/1.03  
% 1.19/1.03  cnf(c_1499,plain,
% 1.19/1.03      ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) != iProver_top ),
% 1.19/1.03      inference(demodulation,[status(thm)],[c_1387,c_1173]) ).
% 1.19/1.03  
% 1.19/1.03  cnf(contradiction,plain,
% 1.19/1.03      ( $false ),
% 1.19/1.03      inference(minisat,[status(thm)],[c_1499,c_13]) ).
% 1.19/1.03  
% 1.19/1.03  
% 1.19/1.03  % SZS output end CNFRefutation for theBenchmark.p
% 1.19/1.03  
% 1.19/1.03  ------                               Statistics
% 1.19/1.03  
% 1.19/1.03  ------ General
% 1.19/1.03  
% 1.19/1.03  abstr_ref_over_cycles:                  0
% 1.19/1.03  abstr_ref_under_cycles:                 0
% 1.19/1.03  gc_basic_clause_elim:                   0
% 1.19/1.03  forced_gc_time:                         0
% 1.19/1.03  parsing_time:                           0.01
% 1.19/1.03  unif_index_cands_time:                  0.
% 1.19/1.03  unif_index_add_time:                    0.
% 1.19/1.03  orderings_time:                         0.
% 1.19/1.03  out_proof_time:                         0.008
% 1.19/1.03  total_time:                             0.063
% 1.19/1.03  num_of_symbols:                         47
% 1.19/1.03  num_of_terms:                           1338
% 1.19/1.03  
% 1.19/1.03  ------ Preprocessing
% 1.19/1.03  
% 1.19/1.03  num_of_splits:                          1
% 1.19/1.03  num_of_split_atoms:                     1
% 1.19/1.03  num_of_reused_defs:                     0
% 1.19/1.03  num_eq_ax_congr_red:                    17
% 1.19/1.03  num_of_sem_filtered_clauses:            1
% 1.19/1.03  num_of_subtypes:                        0
% 1.19/1.03  monotx_restored_types:                  0
% 1.19/1.03  sat_num_of_epr_types:                   0
% 1.19/1.03  sat_num_of_non_cyclic_types:            0
% 1.19/1.03  sat_guarded_non_collapsed_types:        0
% 1.19/1.03  num_pure_diseq_elim:                    0
% 1.19/1.03  simp_replaced_by:                       0
% 1.19/1.03  res_preprocessed:                       62
% 1.19/1.03  prep_upred:                             0
% 1.19/1.03  prep_unflattend:                        3
% 1.19/1.03  smt_new_axioms:                         0
% 1.19/1.03  pred_elim_cands:                        3
% 1.19/1.03  pred_elim:                              2
% 1.19/1.03  pred_elim_cl:                           3
% 1.19/1.03  pred_elim_cycles:                       4
% 1.19/1.03  merged_defs:                            0
% 1.19/1.03  merged_defs_ncl:                        0
% 1.19/1.03  bin_hyper_res:                          0
% 1.19/1.03  prep_cycles:                            4
% 1.19/1.03  pred_elim_time:                         0.
% 1.19/1.03  splitting_time:                         0.
% 1.19/1.03  sem_filter_time:                        0.
% 1.19/1.03  monotx_time:                            0.
% 1.19/1.03  subtype_inf_time:                       0.
% 1.19/1.03  
% 1.19/1.03  ------ Problem properties
% 1.19/1.03  
% 1.19/1.03  clauses:                                11
% 1.19/1.03  conjectures:                            2
% 1.19/1.03  epr:                                    1
% 1.19/1.03  horn:                                   11
% 1.19/1.03  ground:                                 3
% 1.19/1.03  unary:                                  3
% 1.19/1.03  binary:                                 4
% 1.19/1.03  lits:                                   23
% 1.19/1.03  lits_eq:                                4
% 1.19/1.03  fd_pure:                                0
% 1.19/1.03  fd_pseudo:                              0
% 1.19/1.03  fd_cond:                                0
% 1.19/1.03  fd_pseudo_cond:                         0
% 1.19/1.03  ac_symbols:                             0
% 1.19/1.03  
% 1.19/1.03  ------ Propositional Solver
% 1.19/1.03  
% 1.19/1.03  prop_solver_calls:                      28
% 1.19/1.03  prop_fast_solver_calls:                 351
% 1.19/1.03  smt_solver_calls:                       0
% 1.19/1.03  smt_fast_solver_calls:                  0
% 1.19/1.03  prop_num_of_clauses:                    535
% 1.19/1.03  prop_preprocess_simplified:             2449
% 1.19/1.03  prop_fo_subsumed:                       5
% 1.19/1.03  prop_solver_time:                       0.
% 1.19/1.03  smt_solver_time:                        0.
% 1.19/1.03  smt_fast_solver_time:                   0.
% 1.19/1.03  prop_fast_solver_time:                  0.
% 1.19/1.03  prop_unsat_core_time:                   0.
% 1.19/1.03  
% 1.19/1.03  ------ QBF
% 1.19/1.03  
% 1.19/1.03  qbf_q_res:                              0
% 1.19/1.03  qbf_num_tautologies:                    0
% 1.19/1.03  qbf_prep_cycles:                        0
% 1.19/1.03  
% 1.19/1.03  ------ BMC1
% 1.19/1.03  
% 1.19/1.03  bmc1_current_bound:                     -1
% 1.19/1.03  bmc1_last_solved_bound:                 -1
% 1.19/1.03  bmc1_unsat_core_size:                   -1
% 1.19/1.03  bmc1_unsat_core_parents_size:           -1
% 1.19/1.03  bmc1_merge_next_fun:                    0
% 1.19/1.03  bmc1_unsat_core_clauses_time:           0.
% 1.19/1.03  
% 1.19/1.03  ------ Instantiation
% 1.19/1.03  
% 1.19/1.03  inst_num_of_clauses:                    193
% 1.19/1.03  inst_num_in_passive:                    52
% 1.19/1.03  inst_num_in_active:                     127
% 1.19/1.03  inst_num_in_unprocessed:                14
% 1.19/1.03  inst_num_of_loops:                      140
% 1.19/1.03  inst_num_of_learning_restarts:          0
% 1.19/1.03  inst_num_moves_active_passive:          9
% 1.19/1.03  inst_lit_activity:                      0
% 1.19/1.03  inst_lit_activity_moves:                0
% 1.19/1.03  inst_num_tautologies:                   0
% 1.19/1.03  inst_num_prop_implied:                  0
% 1.19/1.03  inst_num_existing_simplified:           0
% 1.19/1.03  inst_num_eq_res_simplified:             0
% 1.19/1.03  inst_num_child_elim:                    0
% 1.19/1.03  inst_num_of_dismatching_blockings:      45
% 1.19/1.03  inst_num_of_non_proper_insts:           175
% 1.19/1.03  inst_num_of_duplicates:                 0
% 1.19/1.03  inst_inst_num_from_inst_to_res:         0
% 1.19/1.03  inst_dismatching_checking_time:         0.
% 1.19/1.03  
% 1.19/1.03  ------ Resolution
% 1.19/1.03  
% 1.19/1.03  res_num_of_clauses:                     0
% 1.19/1.03  res_num_in_passive:                     0
% 1.19/1.03  res_num_in_active:                      0
% 1.19/1.03  res_num_of_loops:                       66
% 1.19/1.03  res_forward_subset_subsumed:            21
% 1.19/1.03  res_backward_subset_subsumed:           0
% 1.19/1.03  res_forward_subsumed:                   0
% 1.19/1.03  res_backward_subsumed:                  0
% 1.19/1.03  res_forward_subsumption_resolution:     0
% 1.19/1.03  res_backward_subsumption_resolution:    0
% 1.19/1.03  res_clause_to_clause_subsumption:       26
% 1.19/1.03  res_orphan_elimination:                 0
% 1.19/1.03  res_tautology_del:                      25
% 1.19/1.03  res_num_eq_res_simplified:              0
% 1.19/1.03  res_num_sel_changes:                    0
% 1.19/1.03  res_moves_from_active_to_pass:          0
% 1.19/1.03  
% 1.19/1.03  ------ Superposition
% 1.19/1.03  
% 1.19/1.03  sup_time_total:                         0.
% 1.19/1.03  sup_time_generating:                    0.
% 1.19/1.03  sup_time_sim_full:                      0.
% 1.19/1.03  sup_time_sim_immed:                     0.
% 1.19/1.03  
% 1.19/1.03  sup_num_of_clauses:                     27
% 1.19/1.03  sup_num_in_active:                      24
% 1.19/1.03  sup_num_in_passive:                     3
% 1.19/1.03  sup_num_of_loops:                       26
% 1.19/1.03  sup_fw_superposition:                   8
% 1.19/1.03  sup_bw_superposition:                   8
% 1.19/1.03  sup_immediate_simplified:               0
% 1.19/1.03  sup_given_eliminated:                   0
% 1.19/1.03  comparisons_done:                       0
% 1.19/1.03  comparisons_avoided:                    0
% 1.19/1.03  
% 1.19/1.03  ------ Simplifications
% 1.19/1.03  
% 1.19/1.03  
% 1.19/1.03  sim_fw_subset_subsumed:                 0
% 1.19/1.03  sim_bw_subset_subsumed:                 0
% 1.19/1.03  sim_fw_subsumed:                        0
% 1.19/1.03  sim_bw_subsumed:                        0
% 1.19/1.03  sim_fw_subsumption_res:                 1
% 1.19/1.03  sim_bw_subsumption_res:                 0
% 1.19/1.03  sim_tautology_del:                      0
% 1.19/1.03  sim_eq_tautology_del:                   0
% 1.19/1.03  sim_eq_res_simp:                        0
% 1.19/1.03  sim_fw_demodulated:                     0
% 1.19/1.03  sim_bw_demodulated:                     2
% 1.19/1.03  sim_light_normalised:                   0
% 1.19/1.03  sim_joinable_taut:                      0
% 1.19/1.03  sim_joinable_simp:                      0
% 1.19/1.03  sim_ac_normalised:                      0
% 1.19/1.03  sim_smt_subsumption:                    0
% 1.19/1.03  
%------------------------------------------------------------------------------
