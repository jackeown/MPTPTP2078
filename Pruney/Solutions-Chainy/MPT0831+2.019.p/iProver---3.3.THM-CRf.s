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
% DateTime   : Thu Dec  3 11:55:38 EST 2020

% Result     : Theorem 7.01s
% Output     : CNFRefutation 7.01s
% Verified   : 
% Statistics : Number of formulae       :   93 ( 258 expanded)
%              Number of clauses        :   51 ( 104 expanded)
%              Number of leaves         :   12 (  46 expanded)
%              Depth                    :   17
%              Number of atoms          :  225 ( 660 expanded)
%              Number of equality atoms :   81 ( 144 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal clause size      :    6 (   2 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f10,conjecture,(
    ! [X0,X1,X2,X3] :
      ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
     => ( r1_tarski(X1,X2)
       => r2_relset_1(X1,X0,k5_relset_1(X1,X0,X3,X2),X3) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

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

fof(f27,plain,
    ( ? [X0,X1,X2,X3] :
        ( ~ r2_relset_1(X1,X0,k5_relset_1(X1,X0,X3,X2),X3)
        & r1_tarski(X1,X2)
        & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) )
   => ( ~ r2_relset_1(sK1,sK0,k5_relset_1(sK1,sK0,sK3,sK2),sK3)
      & r1_tarski(sK1,sK2)
      & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) ) ),
    introduced(choice_axiom,[])).

fof(f28,plain,
    ( ~ r2_relset_1(sK1,sK0,k5_relset_1(sK1,sK0,sK3,sK2),sK3)
    & r1_tarski(sK1,sK2)
    & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3])],[f24,f27])).

fof(f42,plain,(
    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) ),
    inference(cnf_transformation,[],[f28])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f25,plain,(
    ! [X0,X1] :
      ( ( m1_subset_1(X0,k1_zfmisc_1(X1))
        | ~ r1_tarski(X0,X1) )
      & ( r1_tarski(X0,X1)
        | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ) ) ),
    inference(nnf_transformation,[],[f3])).

fof(f32,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f5,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( v1_relat_1(X1)
         => ( r1_tarski(X0,X1)
           => ( r1_tarski(k2_relat_1(X0),k2_relat_1(X1))
              & r1_tarski(k1_relat_1(X0),k1_relat_1(X1)) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f15,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( r1_tarski(k2_relat_1(X0),k2_relat_1(X1))
            & r1_tarski(k1_relat_1(X0),k1_relat_1(X1)) )
          | ~ r1_tarski(X0,X1)
          | ~ v1_relat_1(X1) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f16,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( r1_tarski(k2_relat_1(X0),k2_relat_1(X1))
            & r1_tarski(k1_relat_1(X0),k1_relat_1(X1)) )
          | ~ r1_tarski(X0,X1)
          | ~ v1_relat_1(X1) )
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f15])).

fof(f35,plain,(
    ! [X0,X1] :
      ( r1_tarski(k1_relat_1(X0),k1_relat_1(X1))
      | ~ r1_tarski(X0,X1)
      | ~ v1_relat_1(X1)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f16])).

fof(f4,axiom,(
    ! [X0,X1] : r1_tarski(k1_relat_1(k2_zfmisc_1(X0,X1)),X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f34,plain,(
    ! [X0,X1] : r1_tarski(k1_relat_1(k2_zfmisc_1(X0,X1)),X0) ),
    inference(cnf_transformation,[],[f4])).

fof(f43,plain,(
    r1_tarski(sK1,sK2) ),
    inference(cnf_transformation,[],[f28])).

fof(f1,axiom,(
    ! [X0,X1,X2] :
      ( ( r1_tarski(X1,X2)
        & r1_tarski(X0,X1) )
     => r1_tarski(X0,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f12,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,X2)
      | ~ r1_tarski(X1,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f13,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,X2)
      | ~ r1_tarski(X1,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(flattening,[],[f12])).

fof(f29,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(X0,X2)
      | ~ r1_tarski(X1,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f13])).

fof(f2,axiom,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,X1)
     => ( r1_tarski(k2_zfmisc_1(X2,X0),k2_zfmisc_1(X2,X1))
        & r1_tarski(k2_zfmisc_1(X0,X2),k2_zfmisc_1(X1,X2)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f14,plain,(
    ! [X0,X1,X2] :
      ( ( r1_tarski(k2_zfmisc_1(X2,X0),k2_zfmisc_1(X2,X1))
        & r1_tarski(k2_zfmisc_1(X0,X2),k2_zfmisc_1(X1,X2)) )
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f30,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(k2_zfmisc_1(X0,X2),k2_zfmisc_1(X1,X2))
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f14])).

fof(f33,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f7,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => v1_relat_1(X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f19,plain,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f38,plain,(
    ! [X2,X0,X1] :
      ( v1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f6,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ( r1_tarski(k1_relat_1(X1),X0)
       => k7_relat_1(X1,X0) = X1 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

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

fof(f37,plain,(
    ! [X0,X1] :
      ( k7_relat_1(X1,X0) = X1
      | ~ r1_tarski(k1_relat_1(X1),X0)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f8,axiom,(
    ! [X0,X1,X2,X3] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k7_relat_1(X2,X3) = k5_relset_1(X0,X1,X2,X3) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f20,plain,(
    ! [X0,X1,X2,X3] :
      ( k7_relat_1(X2,X3) = k5_relset_1(X0,X1,X2,X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f39,plain,(
    ! [X2,X0,X3,X1] :
      ( k7_relat_1(X2,X3) = k5_relset_1(X0,X1,X2,X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f9,axiom,(
    ! [X0,X1,X2,X3] :
      ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) )
     => ( r2_relset_1(X0,X1,X2,X3)
      <=> X2 = X3 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f21,plain,(
    ! [X0,X1,X2,X3] :
      ( ( r2_relset_1(X0,X1,X2,X3)
      <=> X2 = X3 )
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f22,plain,(
    ! [X0,X1,X2,X3] :
      ( ( r2_relset_1(X0,X1,X2,X3)
      <=> X2 = X3 )
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(flattening,[],[f21])).

fof(f26,plain,(
    ! [X0,X1,X2,X3] :
      ( ( ( r2_relset_1(X0,X1,X2,X3)
          | X2 != X3 )
        & ( X2 = X3
          | ~ r2_relset_1(X0,X1,X2,X3) ) )
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(nnf_transformation,[],[f22])).

fof(f41,plain,(
    ! [X2,X0,X3,X1] :
      ( r2_relset_1(X0,X1,X2,X3)
      | X2 != X3
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f45,plain,(
    ! [X0,X3,X1] :
      ( r2_relset_1(X0,X1,X3,X3)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(equality_resolution,[],[f41])).

fof(f44,plain,(
    ~ r2_relset_1(sK1,sK0,k5_relset_1(sK1,sK0,sK3,sK2),sK3) ),
    inference(cnf_transformation,[],[f28])).

cnf(c_15,negated_conjecture,
    ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) ),
    inference(cnf_transformation,[],[f42])).

cnf(c_896,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_15])).

cnf(c_4,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | r1_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f32])).

cnf(c_904,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(X1)) != iProver_top
    | r1_tarski(X0,X1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_4])).

cnf(c_1197,plain,
    ( r1_tarski(sK3,k2_zfmisc_1(sK1,sK0)) = iProver_top ),
    inference(superposition,[status(thm)],[c_896,c_904])).

cnf(c_7,plain,
    ( ~ r1_tarski(X0,X1)
    | r1_tarski(k1_relat_1(X0),k1_relat_1(X1))
    | ~ v1_relat_1(X1)
    | ~ v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f35])).

cnf(c_901,plain,
    ( r1_tarski(X0,X1) != iProver_top
    | r1_tarski(k1_relat_1(X0),k1_relat_1(X1)) = iProver_top
    | v1_relat_1(X0) != iProver_top
    | v1_relat_1(X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_7])).

cnf(c_5,plain,
    ( r1_tarski(k1_relat_1(k2_zfmisc_1(X0,X1)),X0) ),
    inference(cnf_transformation,[],[f34])).

cnf(c_903,plain,
    ( r1_tarski(k1_relat_1(k2_zfmisc_1(X0,X1)),X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_5])).

cnf(c_14,negated_conjecture,
    ( r1_tarski(sK1,sK2) ),
    inference(cnf_transformation,[],[f43])).

cnf(c_897,plain,
    ( r1_tarski(sK1,sK2) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_14])).

cnf(c_0,plain,
    ( ~ r1_tarski(X0,X1)
    | ~ r1_tarski(X2,X0)
    | r1_tarski(X2,X1) ),
    inference(cnf_transformation,[],[f29])).

cnf(c_908,plain,
    ( r1_tarski(X0,X1) != iProver_top
    | r1_tarski(X2,X0) != iProver_top
    | r1_tarski(X2,X1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_0])).

cnf(c_2358,plain,
    ( r1_tarski(X0,sK2) = iProver_top
    | r1_tarski(X0,sK1) != iProver_top ),
    inference(superposition,[status(thm)],[c_897,c_908])).

cnf(c_2871,plain,
    ( r1_tarski(k1_relat_1(k2_zfmisc_1(sK1,X0)),sK2) = iProver_top ),
    inference(superposition,[status(thm)],[c_903,c_2358])).

cnf(c_2877,plain,
    ( r1_tarski(X0,k1_relat_1(k2_zfmisc_1(sK1,X1))) != iProver_top
    | r1_tarski(X0,sK2) = iProver_top ),
    inference(superposition,[status(thm)],[c_2871,c_908])).

cnf(c_3158,plain,
    ( r1_tarski(X0,k2_zfmisc_1(sK1,X1)) != iProver_top
    | r1_tarski(k1_relat_1(X0),sK2) = iProver_top
    | v1_relat_1(X0) != iProver_top
    | v1_relat_1(k2_zfmisc_1(sK1,X1)) != iProver_top ),
    inference(superposition,[status(thm)],[c_901,c_2877])).

cnf(c_2,plain,
    ( ~ r1_tarski(X0,X1)
    | r1_tarski(k2_zfmisc_1(X0,X2),k2_zfmisc_1(X1,X2)) ),
    inference(cnf_transformation,[],[f30])).

cnf(c_906,plain,
    ( r1_tarski(X0,X1) != iProver_top
    | r1_tarski(k2_zfmisc_1(X0,X2),k2_zfmisc_1(X1,X2)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2])).

cnf(c_3,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(X1))
    | ~ r1_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f33])).

cnf(c_905,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(X1)) = iProver_top
    | r1_tarski(X0,X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3])).

cnf(c_9,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f38])).

cnf(c_899,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) != iProver_top
    | v1_relat_1(X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_9])).

cnf(c_1457,plain,
    ( r1_tarski(X0,k2_zfmisc_1(X1,X2)) != iProver_top
    | v1_relat_1(X0) = iProver_top ),
    inference(superposition,[status(thm)],[c_905,c_899])).

cnf(c_1941,plain,
    ( r1_tarski(X0,X1) != iProver_top
    | v1_relat_1(k2_zfmisc_1(X0,X2)) = iProver_top ),
    inference(superposition,[status(thm)],[c_906,c_1457])).

cnf(c_4162,plain,
    ( v1_relat_1(k2_zfmisc_1(sK1,X0)) = iProver_top ),
    inference(superposition,[status(thm)],[c_897,c_1941])).

cnf(c_21154,plain,
    ( r1_tarski(X0,k2_zfmisc_1(sK1,X1)) != iProver_top
    | r1_tarski(k1_relat_1(X0),sK2) = iProver_top ),
    inference(forward_subsumption_resolution,[status(thm)],[c_3158,c_4162,c_1457])).

cnf(c_21161,plain,
    ( r1_tarski(k1_relat_1(sK3),sK2) = iProver_top ),
    inference(superposition,[status(thm)],[c_1197,c_21154])).

cnf(c_8,plain,
    ( ~ r1_tarski(k1_relat_1(X0),X1)
    | ~ v1_relat_1(X0)
    | k7_relat_1(X0,X1) = X0 ),
    inference(cnf_transformation,[],[f37])).

cnf(c_900,plain,
    ( k7_relat_1(X0,X1) = X0
    | r1_tarski(k1_relat_1(X0),X1) != iProver_top
    | v1_relat_1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_8])).

cnf(c_21869,plain,
    ( k7_relat_1(sK3,sK2) = sK3
    | v1_relat_1(sK3) != iProver_top ),
    inference(superposition,[status(thm)],[c_21161,c_900])).

cnf(c_16,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_15])).

cnf(c_1012,plain,
    ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
    | v1_relat_1(sK3) ),
    inference(instantiation,[status(thm)],[c_9])).

cnf(c_1013,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) != iProver_top
    | v1_relat_1(sK3) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1012])).

cnf(c_1101,plain,
    ( ~ r1_tarski(k1_relat_1(sK3),X0)
    | ~ v1_relat_1(sK3)
    | k7_relat_1(sK3,X0) = sK3 ),
    inference(instantiation,[status(thm)],[c_8])).

cnf(c_1278,plain,
    ( ~ r1_tarski(k1_relat_1(sK3),sK2)
    | ~ v1_relat_1(sK3)
    | k7_relat_1(sK3,sK2) = sK3 ),
    inference(instantiation,[status(thm)],[c_1101])).

cnf(c_1280,plain,
    ( k7_relat_1(sK3,sK2) = sK3
    | r1_tarski(k1_relat_1(sK3),sK2) != iProver_top
    | v1_relat_1(sK3) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1278])).

cnf(c_23439,plain,
    ( k7_relat_1(sK3,sK2) = sK3 ),
    inference(global_propositional_subsumption,[status(thm)],[c_21869,c_16,c_1013,c_1280,c_21161])).

cnf(c_10,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k5_relset_1(X1,X2,X0,X3) = k7_relat_1(X0,X3) ),
    inference(cnf_transformation,[],[f39])).

cnf(c_898,plain,
    ( k5_relset_1(X0,X1,X2,X3) = k7_relat_1(X2,X3)
    | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_10])).

cnf(c_1305,plain,
    ( k5_relset_1(sK1,sK0,sK3,X0) = k7_relat_1(sK3,X0) ),
    inference(superposition,[status(thm)],[c_896,c_898])).

cnf(c_11,plain,
    ( r2_relset_1(X0,X1,X2,X2)
    | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ),
    inference(cnf_transformation,[],[f45])).

cnf(c_13,negated_conjecture,
    ( ~ r2_relset_1(sK1,sK0,k5_relset_1(sK1,sK0,sK3,sK2),sK3) ),
    inference(cnf_transformation,[],[f44])).

cnf(c_217,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k5_relset_1(sK1,sK0,sK3,sK2) != X0
    | sK3 != X0
    | sK0 != X2
    | sK1 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_11,c_13])).

cnf(c_218,plain,
    ( ~ m1_subset_1(k5_relset_1(sK1,sK0,sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
    | sK3 != k5_relset_1(sK1,sK0,sK3,sK2) ),
    inference(unflattening,[status(thm)],[c_217])).

cnf(c_895,plain,
    ( sK3 != k5_relset_1(sK1,sK0,sK3,sK2)
    | m1_subset_1(k5_relset_1(sK1,sK0,sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_218])).

cnf(c_1825,plain,
    ( k7_relat_1(sK3,sK2) != sK3
    | m1_subset_1(k7_relat_1(sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) != iProver_top ),
    inference(demodulation,[status(thm)],[c_1305,c_895])).

cnf(c_23442,plain,
    ( sK3 != sK3
    | m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) != iProver_top ),
    inference(demodulation,[status(thm)],[c_23439,c_1825])).

cnf(c_554,plain,
    ( X0 = X0 ),
    theory(equality)).

cnf(c_1208,plain,
    ( sK3 = sK3 ),
    inference(instantiation,[status(thm)],[c_554])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_23442,c_1208,c_16])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.10/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.10/0.13  % Command    : iproveropt_run.sh %d %s
% 0.12/0.34  % Computer   : n021.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % WCLimit    : 600
% 0.12/0.34  % DateTime   : Tue Dec  1 10:15:19 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.34  % Running in FOF mode
% 7.01/1.56  % SZS status Started for /export/starexec/sandbox/benchmark/theBenchmark.p
% 7.01/1.56  
% 7.01/1.56  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 7.01/1.56  
% 7.01/1.56  ------  iProver source info
% 7.01/1.56  
% 7.01/1.56  git: date: 2020-06-30 10:37:57 +0100
% 7.01/1.56  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 7.01/1.56  git: non_committed_changes: false
% 7.01/1.56  git: last_make_outside_of_git: false
% 7.01/1.56  
% 7.01/1.56  ------ 
% 7.01/1.56  
% 7.01/1.56  ------ Input Options
% 7.01/1.56  
% 7.01/1.56  --out_options                           all
% 7.01/1.56  --tptp_safe_out                         true
% 7.01/1.56  --problem_path                          ""
% 7.01/1.56  --include_path                          ""
% 7.01/1.56  --clausifier                            res/vclausify_rel
% 7.01/1.56  --clausifier_options                    --mode clausify
% 7.01/1.56  --stdin                                 false
% 7.01/1.56  --stats_out                             all
% 7.01/1.56  
% 7.01/1.56  ------ General Options
% 7.01/1.56  
% 7.01/1.56  --fof                                   false
% 7.01/1.56  --time_out_real                         305.
% 7.01/1.56  --time_out_virtual                      -1.
% 7.01/1.56  --symbol_type_check                     false
% 7.01/1.56  --clausify_out                          false
% 7.01/1.56  --sig_cnt_out                           false
% 7.01/1.56  --trig_cnt_out                          false
% 7.01/1.56  --trig_cnt_out_tolerance                1.
% 7.01/1.56  --trig_cnt_out_sk_spl                   false
% 7.01/1.56  --abstr_cl_out                          false
% 7.01/1.56  
% 7.01/1.56  ------ Global Options
% 7.01/1.56  
% 7.01/1.56  --schedule                              default
% 7.01/1.56  --add_important_lit                     false
% 7.01/1.56  --prop_solver_per_cl                    1000
% 7.01/1.56  --min_unsat_core                        false
% 7.01/1.56  --soft_assumptions                      false
% 7.01/1.56  --soft_lemma_size                       3
% 7.01/1.56  --prop_impl_unit_size                   0
% 7.01/1.56  --prop_impl_unit                        []
% 7.01/1.56  --share_sel_clauses                     true
% 7.01/1.56  --reset_solvers                         false
% 7.01/1.56  --bc_imp_inh                            [conj_cone]
% 7.01/1.56  --conj_cone_tolerance                   3.
% 7.01/1.56  --extra_neg_conj                        none
% 7.01/1.56  --large_theory_mode                     true
% 7.01/1.56  --prolific_symb_bound                   200
% 7.01/1.56  --lt_threshold                          2000
% 7.01/1.56  --clause_weak_htbl                      true
% 7.01/1.56  --gc_record_bc_elim                     false
% 7.01/1.56  
% 7.01/1.56  ------ Preprocessing Options
% 7.01/1.56  
% 7.01/1.56  --preprocessing_flag                    true
% 7.01/1.56  --time_out_prep_mult                    0.1
% 7.01/1.56  --splitting_mode                        input
% 7.01/1.56  --splitting_grd                         true
% 7.01/1.56  --splitting_cvd                         false
% 7.01/1.56  --splitting_cvd_svl                     false
% 7.01/1.56  --splitting_nvd                         32
% 7.01/1.56  --sub_typing                            true
% 7.01/1.56  --prep_gs_sim                           true
% 7.01/1.56  --prep_unflatten                        true
% 7.01/1.56  --prep_res_sim                          true
% 7.01/1.56  --prep_upred                            true
% 7.01/1.56  --prep_sem_filter                       exhaustive
% 7.01/1.56  --prep_sem_filter_out                   false
% 7.01/1.56  --pred_elim                             true
% 7.01/1.56  --res_sim_input                         true
% 7.01/1.56  --eq_ax_congr_red                       true
% 7.01/1.56  --pure_diseq_elim                       true
% 7.01/1.56  --brand_transform                       false
% 7.01/1.56  --non_eq_to_eq                          false
% 7.01/1.56  --prep_def_merge                        true
% 7.01/1.56  --prep_def_merge_prop_impl              false
% 7.01/1.56  --prep_def_merge_mbd                    true
% 7.01/1.56  --prep_def_merge_tr_red                 false
% 7.01/1.56  --prep_def_merge_tr_cl                  false
% 7.01/1.56  --smt_preprocessing                     true
% 7.01/1.56  --smt_ac_axioms                         fast
% 7.01/1.56  --preprocessed_out                      false
% 7.01/1.56  --preprocessed_stats                    false
% 7.01/1.56  
% 7.01/1.56  ------ Abstraction refinement Options
% 7.01/1.56  
% 7.01/1.56  --abstr_ref                             []
% 7.01/1.56  --abstr_ref_prep                        false
% 7.01/1.56  --abstr_ref_until_sat                   false
% 7.01/1.56  --abstr_ref_sig_restrict                funpre
% 7.01/1.56  --abstr_ref_af_restrict_to_split_sk     false
% 7.01/1.56  --abstr_ref_under                       []
% 7.01/1.56  
% 7.01/1.56  ------ SAT Options
% 7.01/1.56  
% 7.01/1.56  --sat_mode                              false
% 7.01/1.56  --sat_fm_restart_options                ""
% 7.01/1.56  --sat_gr_def                            false
% 7.01/1.56  --sat_epr_types                         true
% 7.01/1.56  --sat_non_cyclic_types                  false
% 7.01/1.56  --sat_finite_models                     false
% 7.01/1.56  --sat_fm_lemmas                         false
% 7.01/1.56  --sat_fm_prep                           false
% 7.01/1.56  --sat_fm_uc_incr                        true
% 7.01/1.56  --sat_out_model                         small
% 7.01/1.56  --sat_out_clauses                       false
% 7.01/1.56  
% 7.01/1.56  ------ QBF Options
% 7.01/1.56  
% 7.01/1.56  --qbf_mode                              false
% 7.01/1.56  --qbf_elim_univ                         false
% 7.01/1.56  --qbf_dom_inst                          none
% 7.01/1.56  --qbf_dom_pre_inst                      false
% 7.01/1.56  --qbf_sk_in                             false
% 7.01/1.56  --qbf_pred_elim                         true
% 7.01/1.56  --qbf_split                             512
% 7.01/1.56  
% 7.01/1.56  ------ BMC1 Options
% 7.01/1.56  
% 7.01/1.56  --bmc1_incremental                      false
% 7.01/1.56  --bmc1_axioms                           reachable_all
% 7.01/1.56  --bmc1_min_bound                        0
% 7.01/1.56  --bmc1_max_bound                        -1
% 7.01/1.56  --bmc1_max_bound_default                -1
% 7.01/1.56  --bmc1_symbol_reachability              true
% 7.01/1.56  --bmc1_property_lemmas                  false
% 7.01/1.56  --bmc1_k_induction                      false
% 7.01/1.56  --bmc1_non_equiv_states                 false
% 7.01/1.56  --bmc1_deadlock                         false
% 7.01/1.56  --bmc1_ucm                              false
% 7.01/1.56  --bmc1_add_unsat_core                   none
% 7.01/1.56  --bmc1_unsat_core_children              false
% 7.01/1.56  --bmc1_unsat_core_extrapolate_axioms    false
% 7.01/1.56  --bmc1_out_stat                         full
% 7.01/1.56  --bmc1_ground_init                      false
% 7.01/1.56  --bmc1_pre_inst_next_state              false
% 7.01/1.56  --bmc1_pre_inst_state                   false
% 7.01/1.56  --bmc1_pre_inst_reach_state             false
% 7.01/1.56  --bmc1_out_unsat_core                   false
% 7.01/1.56  --bmc1_aig_witness_out                  false
% 7.01/1.56  --bmc1_verbose                          false
% 7.01/1.56  --bmc1_dump_clauses_tptp                false
% 7.01/1.56  --bmc1_dump_unsat_core_tptp             false
% 7.01/1.56  --bmc1_dump_file                        -
% 7.01/1.56  --bmc1_ucm_expand_uc_limit              128
% 7.01/1.56  --bmc1_ucm_n_expand_iterations          6
% 7.01/1.56  --bmc1_ucm_extend_mode                  1
% 7.01/1.56  --bmc1_ucm_init_mode                    2
% 7.01/1.56  --bmc1_ucm_cone_mode                    none
% 7.01/1.56  --bmc1_ucm_reduced_relation_type        0
% 7.01/1.56  --bmc1_ucm_relax_model                  4
% 7.01/1.56  --bmc1_ucm_full_tr_after_sat            true
% 7.01/1.56  --bmc1_ucm_expand_neg_assumptions       false
% 7.01/1.56  --bmc1_ucm_layered_model                none
% 7.01/1.56  --bmc1_ucm_max_lemma_size               10
% 7.01/1.56  
% 7.01/1.56  ------ AIG Options
% 7.01/1.56  
% 7.01/1.56  --aig_mode                              false
% 7.01/1.56  
% 7.01/1.56  ------ Instantiation Options
% 7.01/1.56  
% 7.01/1.56  --instantiation_flag                    true
% 7.01/1.56  --inst_sos_flag                         false
% 7.01/1.56  --inst_sos_phase                        true
% 7.01/1.56  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 7.01/1.56  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 7.01/1.56  --inst_lit_sel_side                     num_symb
% 7.01/1.56  --inst_solver_per_active                1400
% 7.01/1.56  --inst_solver_calls_frac                1.
% 7.01/1.56  --inst_passive_queue_type               priority_queues
% 7.01/1.56  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 7.01/1.56  --inst_passive_queues_freq              [25;2]
% 7.01/1.56  --inst_dismatching                      true
% 7.01/1.56  --inst_eager_unprocessed_to_passive     true
% 7.01/1.56  --inst_prop_sim_given                   true
% 7.01/1.56  --inst_prop_sim_new                     false
% 7.01/1.56  --inst_subs_new                         false
% 7.01/1.56  --inst_eq_res_simp                      false
% 7.01/1.56  --inst_subs_given                       false
% 7.01/1.56  --inst_orphan_elimination               true
% 7.01/1.56  --inst_learning_loop_flag               true
% 7.01/1.56  --inst_learning_start                   3000
% 7.01/1.56  --inst_learning_factor                  2
% 7.01/1.56  --inst_start_prop_sim_after_learn       3
% 7.01/1.56  --inst_sel_renew                        solver
% 7.01/1.56  --inst_lit_activity_flag                true
% 7.01/1.56  --inst_restr_to_given                   false
% 7.01/1.56  --inst_activity_threshold               500
% 7.01/1.56  --inst_out_proof                        true
% 7.01/1.56  
% 7.01/1.56  ------ Resolution Options
% 7.01/1.56  
% 7.01/1.56  --resolution_flag                       true
% 7.01/1.56  --res_lit_sel                           adaptive
% 7.01/1.56  --res_lit_sel_side                      none
% 7.01/1.56  --res_ordering                          kbo
% 7.01/1.56  --res_to_prop_solver                    active
% 7.01/1.56  --res_prop_simpl_new                    false
% 7.01/1.56  --res_prop_simpl_given                  true
% 7.01/1.56  --res_passive_queue_type                priority_queues
% 7.01/1.56  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 7.01/1.56  --res_passive_queues_freq               [15;5]
% 7.01/1.56  --res_forward_subs                      full
% 7.01/1.56  --res_backward_subs                     full
% 7.01/1.56  --res_forward_subs_resolution           true
% 7.01/1.56  --res_backward_subs_resolution          true
% 7.01/1.56  --res_orphan_elimination                true
% 7.01/1.56  --res_time_limit                        2.
% 7.01/1.56  --res_out_proof                         true
% 7.01/1.56  
% 7.01/1.56  ------ Superposition Options
% 7.01/1.56  
% 7.01/1.56  --superposition_flag                    true
% 7.01/1.56  --sup_passive_queue_type                priority_queues
% 7.01/1.56  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 7.01/1.56  --sup_passive_queues_freq               [8;1;4]
% 7.01/1.56  --demod_completeness_check              fast
% 7.01/1.56  --demod_use_ground                      true
% 7.01/1.56  --sup_to_prop_solver                    passive
% 7.01/1.56  --sup_prop_simpl_new                    true
% 7.01/1.56  --sup_prop_simpl_given                  true
% 7.01/1.56  --sup_fun_splitting                     false
% 7.01/1.56  --sup_smt_interval                      50000
% 7.01/1.56  
% 7.01/1.56  ------ Superposition Simplification Setup
% 7.01/1.56  
% 7.01/1.56  --sup_indices_passive                   []
% 7.01/1.56  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 7.01/1.56  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 7.01/1.56  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 7.01/1.56  --sup_full_triv                         [TrivRules;PropSubs]
% 7.01/1.56  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 7.01/1.56  --sup_full_bw                           [BwDemod]
% 7.01/1.56  --sup_immed_triv                        [TrivRules]
% 7.01/1.56  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 7.01/1.56  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 7.01/1.56  --sup_immed_bw_main                     []
% 7.01/1.56  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 7.01/1.56  --sup_input_triv                        [Unflattening;TrivRules]
% 7.01/1.56  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 7.01/1.56  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 7.01/1.56  
% 7.01/1.56  ------ Combination Options
% 7.01/1.56  
% 7.01/1.56  --comb_res_mult                         3
% 7.01/1.56  --comb_sup_mult                         2
% 7.01/1.56  --comb_inst_mult                        10
% 7.01/1.56  
% 7.01/1.56  ------ Debug Options
% 7.01/1.56  
% 7.01/1.56  --dbg_backtrace                         false
% 7.01/1.56  --dbg_dump_prop_clauses                 false
% 7.01/1.56  --dbg_dump_prop_clauses_file            -
% 7.01/1.56  --dbg_out_stat                          false
% 7.01/1.56  ------ Parsing...
% 7.01/1.56  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 7.01/1.56  
% 7.01/1.56  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe:1:0s pe_e  sf_s  rm: 2 0s  sf_e  pe_s  pe_e 
% 7.01/1.56  
% 7.01/1.56  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 7.01/1.56  
% 7.01/1.56  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 7.01/1.56  ------ Proving...
% 7.01/1.56  ------ Problem Properties 
% 7.01/1.56  
% 7.01/1.56  
% 7.01/1.56  clauses                                 14
% 7.01/1.56  conjectures                             2
% 7.01/1.56  EPR                                     2
% 7.01/1.56  Horn                                    14
% 7.01/1.56  unary                                   3
% 7.01/1.56  binary                                  7
% 7.01/1.56  lits                                    31
% 7.01/1.56  lits eq                                 3
% 7.01/1.56  fd_pure                                 0
% 7.01/1.56  fd_pseudo                               0
% 7.01/1.56  fd_cond                                 0
% 7.01/1.56  fd_pseudo_cond                          0
% 7.01/1.56  AC symbols                              0
% 7.01/1.56  
% 7.01/1.56  ------ Schedule dynamic 5 is on 
% 7.01/1.56  
% 7.01/1.56  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" Time Limit: 10.
% 7.01/1.56  
% 7.01/1.56  
% 7.01/1.56  ------ 
% 7.01/1.56  Current options:
% 7.01/1.56  ------ 
% 7.01/1.56  
% 7.01/1.56  ------ Input Options
% 7.01/1.56  
% 7.01/1.56  --out_options                           all
% 7.01/1.56  --tptp_safe_out                         true
% 7.01/1.56  --problem_path                          ""
% 7.01/1.56  --include_path                          ""
% 7.01/1.56  --clausifier                            res/vclausify_rel
% 7.01/1.56  --clausifier_options                    --mode clausify
% 7.01/1.56  --stdin                                 false
% 7.01/1.56  --stats_out                             all
% 7.01/1.56  
% 7.01/1.56  ------ General Options
% 7.01/1.56  
% 7.01/1.56  --fof                                   false
% 7.01/1.56  --time_out_real                         305.
% 7.01/1.56  --time_out_virtual                      -1.
% 7.01/1.56  --symbol_type_check                     false
% 7.01/1.56  --clausify_out                          false
% 7.01/1.56  --sig_cnt_out                           false
% 7.01/1.56  --trig_cnt_out                          false
% 7.01/1.56  --trig_cnt_out_tolerance                1.
% 7.01/1.56  --trig_cnt_out_sk_spl                   false
% 7.01/1.56  --abstr_cl_out                          false
% 7.01/1.56  
% 7.01/1.56  ------ Global Options
% 7.01/1.56  
% 7.01/1.56  --schedule                              default
% 7.01/1.56  --add_important_lit                     false
% 7.01/1.56  --prop_solver_per_cl                    1000
% 7.01/1.56  --min_unsat_core                        false
% 7.01/1.56  --soft_assumptions                      false
% 7.01/1.56  --soft_lemma_size                       3
% 7.01/1.56  --prop_impl_unit_size                   0
% 7.01/1.56  --prop_impl_unit                        []
% 7.01/1.56  --share_sel_clauses                     true
% 7.01/1.56  --reset_solvers                         false
% 7.01/1.56  --bc_imp_inh                            [conj_cone]
% 7.01/1.56  --conj_cone_tolerance                   3.
% 7.01/1.56  --extra_neg_conj                        none
% 7.01/1.56  --large_theory_mode                     true
% 7.01/1.56  --prolific_symb_bound                   200
% 7.01/1.56  --lt_threshold                          2000
% 7.01/1.56  --clause_weak_htbl                      true
% 7.01/1.56  --gc_record_bc_elim                     false
% 7.01/1.56  
% 7.01/1.56  ------ Preprocessing Options
% 7.01/1.56  
% 7.01/1.56  --preprocessing_flag                    true
% 7.01/1.56  --time_out_prep_mult                    0.1
% 7.01/1.56  --splitting_mode                        input
% 7.01/1.56  --splitting_grd                         true
% 7.01/1.56  --splitting_cvd                         false
% 7.01/1.56  --splitting_cvd_svl                     false
% 7.01/1.56  --splitting_nvd                         32
% 7.01/1.56  --sub_typing                            true
% 7.01/1.56  --prep_gs_sim                           true
% 7.01/1.56  --prep_unflatten                        true
% 7.01/1.56  --prep_res_sim                          true
% 7.01/1.56  --prep_upred                            true
% 7.01/1.56  --prep_sem_filter                       exhaustive
% 7.01/1.56  --prep_sem_filter_out                   false
% 7.01/1.56  --pred_elim                             true
% 7.01/1.56  --res_sim_input                         true
% 7.01/1.56  --eq_ax_congr_red                       true
% 7.01/1.56  --pure_diseq_elim                       true
% 7.01/1.56  --brand_transform                       false
% 7.01/1.56  --non_eq_to_eq                          false
% 7.01/1.56  --prep_def_merge                        true
% 7.01/1.56  --prep_def_merge_prop_impl              false
% 7.01/1.56  --prep_def_merge_mbd                    true
% 7.01/1.56  --prep_def_merge_tr_red                 false
% 7.01/1.56  --prep_def_merge_tr_cl                  false
% 7.01/1.56  --smt_preprocessing                     true
% 7.01/1.56  --smt_ac_axioms                         fast
% 7.01/1.56  --preprocessed_out                      false
% 7.01/1.56  --preprocessed_stats                    false
% 7.01/1.56  
% 7.01/1.56  ------ Abstraction refinement Options
% 7.01/1.56  
% 7.01/1.56  --abstr_ref                             []
% 7.01/1.56  --abstr_ref_prep                        false
% 7.01/1.56  --abstr_ref_until_sat                   false
% 7.01/1.56  --abstr_ref_sig_restrict                funpre
% 7.01/1.56  --abstr_ref_af_restrict_to_split_sk     false
% 7.01/1.56  --abstr_ref_under                       []
% 7.01/1.56  
% 7.01/1.56  ------ SAT Options
% 7.01/1.56  
% 7.01/1.56  --sat_mode                              false
% 7.01/1.56  --sat_fm_restart_options                ""
% 7.01/1.56  --sat_gr_def                            false
% 7.01/1.56  --sat_epr_types                         true
% 7.01/1.56  --sat_non_cyclic_types                  false
% 7.01/1.56  --sat_finite_models                     false
% 7.01/1.56  --sat_fm_lemmas                         false
% 7.01/1.56  --sat_fm_prep                           false
% 7.01/1.56  --sat_fm_uc_incr                        true
% 7.01/1.56  --sat_out_model                         small
% 7.01/1.56  --sat_out_clauses                       false
% 7.01/1.56  
% 7.01/1.56  ------ QBF Options
% 7.01/1.56  
% 7.01/1.56  --qbf_mode                              false
% 7.01/1.56  --qbf_elim_univ                         false
% 7.01/1.56  --qbf_dom_inst                          none
% 7.01/1.56  --qbf_dom_pre_inst                      false
% 7.01/1.56  --qbf_sk_in                             false
% 7.01/1.56  --qbf_pred_elim                         true
% 7.01/1.56  --qbf_split                             512
% 7.01/1.56  
% 7.01/1.56  ------ BMC1 Options
% 7.01/1.56  
% 7.01/1.56  --bmc1_incremental                      false
% 7.01/1.56  --bmc1_axioms                           reachable_all
% 7.01/1.56  --bmc1_min_bound                        0
% 7.01/1.56  --bmc1_max_bound                        -1
% 7.01/1.56  --bmc1_max_bound_default                -1
% 7.01/1.56  --bmc1_symbol_reachability              true
% 7.01/1.56  --bmc1_property_lemmas                  false
% 7.01/1.56  --bmc1_k_induction                      false
% 7.01/1.56  --bmc1_non_equiv_states                 false
% 7.01/1.56  --bmc1_deadlock                         false
% 7.01/1.56  --bmc1_ucm                              false
% 7.01/1.56  --bmc1_add_unsat_core                   none
% 7.01/1.56  --bmc1_unsat_core_children              false
% 7.01/1.56  --bmc1_unsat_core_extrapolate_axioms    false
% 7.01/1.56  --bmc1_out_stat                         full
% 7.01/1.56  --bmc1_ground_init                      false
% 7.01/1.56  --bmc1_pre_inst_next_state              false
% 7.01/1.56  --bmc1_pre_inst_state                   false
% 7.01/1.56  --bmc1_pre_inst_reach_state             false
% 7.01/1.56  --bmc1_out_unsat_core                   false
% 7.01/1.56  --bmc1_aig_witness_out                  false
% 7.01/1.56  --bmc1_verbose                          false
% 7.01/1.56  --bmc1_dump_clauses_tptp                false
% 7.01/1.56  --bmc1_dump_unsat_core_tptp             false
% 7.01/1.56  --bmc1_dump_file                        -
% 7.01/1.56  --bmc1_ucm_expand_uc_limit              128
% 7.01/1.56  --bmc1_ucm_n_expand_iterations          6
% 7.01/1.56  --bmc1_ucm_extend_mode                  1
% 7.01/1.56  --bmc1_ucm_init_mode                    2
% 7.01/1.56  --bmc1_ucm_cone_mode                    none
% 7.01/1.56  --bmc1_ucm_reduced_relation_type        0
% 7.01/1.56  --bmc1_ucm_relax_model                  4
% 7.01/1.56  --bmc1_ucm_full_tr_after_sat            true
% 7.01/1.56  --bmc1_ucm_expand_neg_assumptions       false
% 7.01/1.56  --bmc1_ucm_layered_model                none
% 7.01/1.56  --bmc1_ucm_max_lemma_size               10
% 7.01/1.56  
% 7.01/1.56  ------ AIG Options
% 7.01/1.56  
% 7.01/1.56  --aig_mode                              false
% 7.01/1.56  
% 7.01/1.56  ------ Instantiation Options
% 7.01/1.56  
% 7.01/1.56  --instantiation_flag                    true
% 7.01/1.56  --inst_sos_flag                         false
% 7.01/1.56  --inst_sos_phase                        true
% 7.01/1.56  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 7.01/1.56  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 7.01/1.56  --inst_lit_sel_side                     none
% 7.01/1.56  --inst_solver_per_active                1400
% 7.01/1.56  --inst_solver_calls_frac                1.
% 7.01/1.56  --inst_passive_queue_type               priority_queues
% 7.01/1.56  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 7.01/1.56  --inst_passive_queues_freq              [25;2]
% 7.01/1.56  --inst_dismatching                      true
% 7.01/1.56  --inst_eager_unprocessed_to_passive     true
% 7.01/1.56  --inst_prop_sim_given                   true
% 7.01/1.56  --inst_prop_sim_new                     false
% 7.01/1.56  --inst_subs_new                         false
% 7.01/1.56  --inst_eq_res_simp                      false
% 7.01/1.56  --inst_subs_given                       false
% 7.01/1.56  --inst_orphan_elimination               true
% 7.01/1.56  --inst_learning_loop_flag               true
% 7.01/1.56  --inst_learning_start                   3000
% 7.01/1.56  --inst_learning_factor                  2
% 7.01/1.56  --inst_start_prop_sim_after_learn       3
% 7.01/1.56  --inst_sel_renew                        solver
% 7.01/1.56  --inst_lit_activity_flag                true
% 7.01/1.56  --inst_restr_to_given                   false
% 7.01/1.56  --inst_activity_threshold               500
% 7.01/1.56  --inst_out_proof                        true
% 7.01/1.56  
% 7.01/1.56  ------ Resolution Options
% 7.01/1.56  
% 7.01/1.56  --resolution_flag                       false
% 7.01/1.56  --res_lit_sel                           adaptive
% 7.01/1.56  --res_lit_sel_side                      none
% 7.01/1.56  --res_ordering                          kbo
% 7.01/1.56  --res_to_prop_solver                    active
% 7.01/1.56  --res_prop_simpl_new                    false
% 7.01/1.56  --res_prop_simpl_given                  true
% 7.01/1.56  --res_passive_queue_type                priority_queues
% 7.01/1.56  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 7.01/1.56  --res_passive_queues_freq               [15;5]
% 7.01/1.56  --res_forward_subs                      full
% 7.01/1.56  --res_backward_subs                     full
% 7.01/1.56  --res_forward_subs_resolution           true
% 7.01/1.56  --res_backward_subs_resolution          true
% 7.01/1.56  --res_orphan_elimination                true
% 7.01/1.56  --res_time_limit                        2.
% 7.01/1.56  --res_out_proof                         true
% 7.01/1.56  
% 7.01/1.56  ------ Superposition Options
% 7.01/1.56  
% 7.01/1.56  --superposition_flag                    true
% 7.01/1.56  --sup_passive_queue_type                priority_queues
% 7.01/1.56  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 7.01/1.56  --sup_passive_queues_freq               [8;1;4]
% 7.01/1.56  --demod_completeness_check              fast
% 7.01/1.56  --demod_use_ground                      true
% 7.01/1.56  --sup_to_prop_solver                    passive
% 7.01/1.56  --sup_prop_simpl_new                    true
% 7.01/1.56  --sup_prop_simpl_given                  true
% 7.01/1.56  --sup_fun_splitting                     false
% 7.01/1.56  --sup_smt_interval                      50000
% 7.01/1.56  
% 7.01/1.56  ------ Superposition Simplification Setup
% 7.01/1.56  
% 7.01/1.56  --sup_indices_passive                   []
% 7.01/1.56  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 7.01/1.56  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 7.01/1.56  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 7.01/1.56  --sup_full_triv                         [TrivRules;PropSubs]
% 7.01/1.56  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 7.01/1.56  --sup_full_bw                           [BwDemod]
% 7.01/1.56  --sup_immed_triv                        [TrivRules]
% 7.01/1.56  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 7.01/1.56  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 7.01/1.56  --sup_immed_bw_main                     []
% 7.01/1.56  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 7.01/1.56  --sup_input_triv                        [Unflattening;TrivRules]
% 7.01/1.56  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 7.01/1.56  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 7.01/1.56  
% 7.01/1.56  ------ Combination Options
% 7.01/1.56  
% 7.01/1.56  --comb_res_mult                         3
% 7.01/1.56  --comb_sup_mult                         2
% 7.01/1.56  --comb_inst_mult                        10
% 7.01/1.56  
% 7.01/1.56  ------ Debug Options
% 7.01/1.56  
% 7.01/1.56  --dbg_backtrace                         false
% 7.01/1.56  --dbg_dump_prop_clauses                 false
% 7.01/1.56  --dbg_dump_prop_clauses_file            -
% 7.01/1.56  --dbg_out_stat                          false
% 7.01/1.56  
% 7.01/1.56  
% 7.01/1.56  
% 7.01/1.56  
% 7.01/1.56  ------ Proving...
% 7.01/1.56  
% 7.01/1.56  
% 7.01/1.56  % SZS status Theorem for theBenchmark.p
% 7.01/1.56  
% 7.01/1.56  % SZS output start CNFRefutation for theBenchmark.p
% 7.01/1.56  
% 7.01/1.56  fof(f10,conjecture,(
% 7.01/1.56    ! [X0,X1,X2,X3] : (m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) => (r1_tarski(X1,X2) => r2_relset_1(X1,X0,k5_relset_1(X1,X0,X3,X2),X3)))),
% 7.01/1.56    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.01/1.56  
% 7.01/1.56  fof(f11,negated_conjecture,(
% 7.01/1.56    ~! [X0,X1,X2,X3] : (m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) => (r1_tarski(X1,X2) => r2_relset_1(X1,X0,k5_relset_1(X1,X0,X3,X2),X3)))),
% 7.01/1.56    inference(negated_conjecture,[],[f10])).
% 7.01/1.56  
% 7.01/1.56  fof(f23,plain,(
% 7.01/1.56    ? [X0,X1,X2,X3] : ((~r2_relset_1(X1,X0,k5_relset_1(X1,X0,X3,X2),X3) & r1_tarski(X1,X2)) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))))),
% 7.01/1.56    inference(ennf_transformation,[],[f11])).
% 7.01/1.56  
% 7.01/1.56  fof(f24,plain,(
% 7.01/1.56    ? [X0,X1,X2,X3] : (~r2_relset_1(X1,X0,k5_relset_1(X1,X0,X3,X2),X3) & r1_tarski(X1,X2) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))))),
% 7.01/1.56    inference(flattening,[],[f23])).
% 7.01/1.56  
% 7.01/1.56  fof(f27,plain,(
% 7.01/1.56    ? [X0,X1,X2,X3] : (~r2_relset_1(X1,X0,k5_relset_1(X1,X0,X3,X2),X3) & r1_tarski(X1,X2) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0)))) => (~r2_relset_1(sK1,sK0,k5_relset_1(sK1,sK0,sK3,sK2),sK3) & r1_tarski(sK1,sK2) & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))))),
% 7.01/1.56    introduced(choice_axiom,[])).
% 7.01/1.56  
% 7.01/1.56  fof(f28,plain,(
% 7.01/1.56    ~r2_relset_1(sK1,sK0,k5_relset_1(sK1,sK0,sK3,sK2),sK3) & r1_tarski(sK1,sK2) & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))),
% 7.01/1.56    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3])],[f24,f27])).
% 7.01/1.56  
% 7.01/1.56  fof(f42,plain,(
% 7.01/1.56    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))),
% 7.01/1.56    inference(cnf_transformation,[],[f28])).
% 7.01/1.56  
% 7.01/1.56  fof(f3,axiom,(
% 7.01/1.56    ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) <=> r1_tarski(X0,X1))),
% 7.01/1.56    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.01/1.56  
% 7.01/1.56  fof(f25,plain,(
% 7.01/1.56    ! [X0,X1] : ((m1_subset_1(X0,k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1)) & (r1_tarski(X0,X1) | ~m1_subset_1(X0,k1_zfmisc_1(X1))))),
% 7.01/1.56    inference(nnf_transformation,[],[f3])).
% 7.01/1.56  
% 7.01/1.56  fof(f32,plain,(
% 7.01/1.56    ( ! [X0,X1] : (r1_tarski(X0,X1) | ~m1_subset_1(X0,k1_zfmisc_1(X1))) )),
% 7.01/1.56    inference(cnf_transformation,[],[f25])).
% 7.01/1.56  
% 7.01/1.56  fof(f5,axiom,(
% 7.01/1.56    ! [X0] : (v1_relat_1(X0) => ! [X1] : (v1_relat_1(X1) => (r1_tarski(X0,X1) => (r1_tarski(k2_relat_1(X0),k2_relat_1(X1)) & r1_tarski(k1_relat_1(X0),k1_relat_1(X1))))))),
% 7.01/1.56    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.01/1.56  
% 7.01/1.56  fof(f15,plain,(
% 7.01/1.56    ! [X0] : (! [X1] : (((r1_tarski(k2_relat_1(X0),k2_relat_1(X1)) & r1_tarski(k1_relat_1(X0),k1_relat_1(X1))) | ~r1_tarski(X0,X1)) | ~v1_relat_1(X1)) | ~v1_relat_1(X0))),
% 7.01/1.56    inference(ennf_transformation,[],[f5])).
% 7.01/1.56  
% 7.01/1.56  fof(f16,plain,(
% 7.01/1.56    ! [X0] : (! [X1] : ((r1_tarski(k2_relat_1(X0),k2_relat_1(X1)) & r1_tarski(k1_relat_1(X0),k1_relat_1(X1))) | ~r1_tarski(X0,X1) | ~v1_relat_1(X1)) | ~v1_relat_1(X0))),
% 7.01/1.56    inference(flattening,[],[f15])).
% 7.01/1.56  
% 7.01/1.56  fof(f35,plain,(
% 7.01/1.56    ( ! [X0,X1] : (r1_tarski(k1_relat_1(X0),k1_relat_1(X1)) | ~r1_tarski(X0,X1) | ~v1_relat_1(X1) | ~v1_relat_1(X0)) )),
% 7.01/1.56    inference(cnf_transformation,[],[f16])).
% 7.01/1.56  
% 7.01/1.56  fof(f4,axiom,(
% 7.01/1.56    ! [X0,X1] : r1_tarski(k1_relat_1(k2_zfmisc_1(X0,X1)),X0)),
% 7.01/1.56    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.01/1.56  
% 7.01/1.56  fof(f34,plain,(
% 7.01/1.56    ( ! [X0,X1] : (r1_tarski(k1_relat_1(k2_zfmisc_1(X0,X1)),X0)) )),
% 7.01/1.56    inference(cnf_transformation,[],[f4])).
% 7.01/1.56  
% 7.01/1.56  fof(f43,plain,(
% 7.01/1.56    r1_tarski(sK1,sK2)),
% 7.01/1.56    inference(cnf_transformation,[],[f28])).
% 7.01/1.56  
% 7.01/1.56  fof(f1,axiom,(
% 7.01/1.56    ! [X0,X1,X2] : ((r1_tarski(X1,X2) & r1_tarski(X0,X1)) => r1_tarski(X0,X2))),
% 7.01/1.56    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.01/1.56  
% 7.01/1.56  fof(f12,plain,(
% 7.01/1.56    ! [X0,X1,X2] : (r1_tarski(X0,X2) | (~r1_tarski(X1,X2) | ~r1_tarski(X0,X1)))),
% 7.01/1.56    inference(ennf_transformation,[],[f1])).
% 7.01/1.56  
% 7.01/1.56  fof(f13,plain,(
% 7.01/1.56    ! [X0,X1,X2] : (r1_tarski(X0,X2) | ~r1_tarski(X1,X2) | ~r1_tarski(X0,X1))),
% 7.01/1.56    inference(flattening,[],[f12])).
% 7.01/1.56  
% 7.01/1.56  fof(f29,plain,(
% 7.01/1.56    ( ! [X2,X0,X1] : (r1_tarski(X0,X2) | ~r1_tarski(X1,X2) | ~r1_tarski(X0,X1)) )),
% 7.01/1.56    inference(cnf_transformation,[],[f13])).
% 7.01/1.56  
% 7.01/1.56  fof(f2,axiom,(
% 7.01/1.56    ! [X0,X1,X2] : (r1_tarski(X0,X1) => (r1_tarski(k2_zfmisc_1(X2,X0),k2_zfmisc_1(X2,X1)) & r1_tarski(k2_zfmisc_1(X0,X2),k2_zfmisc_1(X1,X2))))),
% 7.01/1.56    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.01/1.56  
% 7.01/1.56  fof(f14,plain,(
% 7.01/1.56    ! [X0,X1,X2] : ((r1_tarski(k2_zfmisc_1(X2,X0),k2_zfmisc_1(X2,X1)) & r1_tarski(k2_zfmisc_1(X0,X2),k2_zfmisc_1(X1,X2))) | ~r1_tarski(X0,X1))),
% 7.01/1.56    inference(ennf_transformation,[],[f2])).
% 7.01/1.56  
% 7.01/1.56  fof(f30,plain,(
% 7.01/1.56    ( ! [X2,X0,X1] : (r1_tarski(k2_zfmisc_1(X0,X2),k2_zfmisc_1(X1,X2)) | ~r1_tarski(X0,X1)) )),
% 7.01/1.56    inference(cnf_transformation,[],[f14])).
% 7.01/1.56  
% 7.01/1.56  fof(f33,plain,(
% 7.01/1.56    ( ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1)) )),
% 7.01/1.56    inference(cnf_transformation,[],[f25])).
% 7.01/1.56  
% 7.01/1.56  fof(f7,axiom,(
% 7.01/1.56    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => v1_relat_1(X2))),
% 7.01/1.56    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.01/1.56  
% 7.01/1.56  fof(f19,plain,(
% 7.01/1.56    ! [X0,X1,X2] : (v1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 7.01/1.56    inference(ennf_transformation,[],[f7])).
% 7.01/1.56  
% 7.01/1.56  fof(f38,plain,(
% 7.01/1.56    ( ! [X2,X0,X1] : (v1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 7.01/1.56    inference(cnf_transformation,[],[f19])).
% 7.01/1.56  
% 7.01/1.56  fof(f6,axiom,(
% 7.01/1.56    ! [X0,X1] : (v1_relat_1(X1) => (r1_tarski(k1_relat_1(X1),X0) => k7_relat_1(X1,X0) = X1))),
% 7.01/1.56    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.01/1.56  
% 7.01/1.56  fof(f17,plain,(
% 7.01/1.56    ! [X0,X1] : ((k7_relat_1(X1,X0) = X1 | ~r1_tarski(k1_relat_1(X1),X0)) | ~v1_relat_1(X1))),
% 7.01/1.56    inference(ennf_transformation,[],[f6])).
% 7.01/1.56  
% 7.01/1.56  fof(f18,plain,(
% 7.01/1.56    ! [X0,X1] : (k7_relat_1(X1,X0) = X1 | ~r1_tarski(k1_relat_1(X1),X0) | ~v1_relat_1(X1))),
% 7.01/1.56    inference(flattening,[],[f17])).
% 7.01/1.56  
% 7.01/1.56  fof(f37,plain,(
% 7.01/1.56    ( ! [X0,X1] : (k7_relat_1(X1,X0) = X1 | ~r1_tarski(k1_relat_1(X1),X0) | ~v1_relat_1(X1)) )),
% 7.01/1.56    inference(cnf_transformation,[],[f18])).
% 7.01/1.56  
% 7.01/1.56  fof(f8,axiom,(
% 7.01/1.56    ! [X0,X1,X2,X3] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k7_relat_1(X2,X3) = k5_relset_1(X0,X1,X2,X3))),
% 7.01/1.56    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.01/1.56  
% 7.01/1.56  fof(f20,plain,(
% 7.01/1.56    ! [X0,X1,X2,X3] : (k7_relat_1(X2,X3) = k5_relset_1(X0,X1,X2,X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 7.01/1.56    inference(ennf_transformation,[],[f8])).
% 7.01/1.56  
% 7.01/1.56  fof(f39,plain,(
% 7.01/1.56    ( ! [X2,X0,X3,X1] : (k7_relat_1(X2,X3) = k5_relset_1(X0,X1,X2,X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 7.01/1.56    inference(cnf_transformation,[],[f20])).
% 7.01/1.56  
% 7.01/1.56  fof(f9,axiom,(
% 7.01/1.56    ! [X0,X1,X2,X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) => (r2_relset_1(X0,X1,X2,X3) <=> X2 = X3))),
% 7.01/1.56    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.01/1.56  
% 7.01/1.56  fof(f21,plain,(
% 7.01/1.56    ! [X0,X1,X2,X3] : ((r2_relset_1(X0,X1,X2,X3) <=> X2 = X3) | (~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))))),
% 7.01/1.56    inference(ennf_transformation,[],[f9])).
% 7.01/1.56  
% 7.01/1.56  fof(f22,plain,(
% 7.01/1.56    ! [X0,X1,X2,X3] : ((r2_relset_1(X0,X1,X2,X3) <=> X2 = X3) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 7.01/1.56    inference(flattening,[],[f21])).
% 7.01/1.56  
% 7.01/1.56  fof(f26,plain,(
% 7.01/1.56    ! [X0,X1,X2,X3] : (((r2_relset_1(X0,X1,X2,X3) | X2 != X3) & (X2 = X3 | ~r2_relset_1(X0,X1,X2,X3))) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 7.01/1.56    inference(nnf_transformation,[],[f22])).
% 7.01/1.56  
% 7.01/1.56  fof(f41,plain,(
% 7.01/1.56    ( ! [X2,X0,X3,X1] : (r2_relset_1(X0,X1,X2,X3) | X2 != X3 | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 7.01/1.56    inference(cnf_transformation,[],[f26])).
% 7.01/1.56  
% 7.01/1.56  fof(f45,plain,(
% 7.01/1.56    ( ! [X0,X3,X1] : (r2_relset_1(X0,X1,X3,X3) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 7.01/1.56    inference(equality_resolution,[],[f41])).
% 7.01/1.56  
% 7.01/1.56  fof(f44,plain,(
% 7.01/1.56    ~r2_relset_1(sK1,sK0,k5_relset_1(sK1,sK0,sK3,sK2),sK3)),
% 7.01/1.56    inference(cnf_transformation,[],[f28])).
% 7.01/1.56  
% 7.01/1.56  cnf(c_15,negated_conjecture,
% 7.01/1.56      ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) ),
% 7.01/1.56      inference(cnf_transformation,[],[f42]) ).
% 7.01/1.56  
% 7.01/1.56  cnf(c_896,plain,
% 7.01/1.56      ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) = iProver_top ),
% 7.01/1.56      inference(predicate_to_equality,[status(thm)],[c_15]) ).
% 7.01/1.56  
% 7.01/1.56  cnf(c_4,plain,
% 7.01/1.56      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1)) | r1_tarski(X0,X1) ),
% 7.01/1.56      inference(cnf_transformation,[],[f32]) ).
% 7.01/1.56  
% 7.01/1.56  cnf(c_904,plain,
% 7.01/1.56      ( m1_subset_1(X0,k1_zfmisc_1(X1)) != iProver_top
% 7.01/1.56      | r1_tarski(X0,X1) = iProver_top ),
% 7.01/1.56      inference(predicate_to_equality,[status(thm)],[c_4]) ).
% 7.01/1.56  
% 7.01/1.56  cnf(c_1197,plain,
% 7.01/1.56      ( r1_tarski(sK3,k2_zfmisc_1(sK1,sK0)) = iProver_top ),
% 7.01/1.56      inference(superposition,[status(thm)],[c_896,c_904]) ).
% 7.01/1.56  
% 7.01/1.56  cnf(c_7,plain,
% 7.01/1.56      ( ~ r1_tarski(X0,X1)
% 7.01/1.56      | r1_tarski(k1_relat_1(X0),k1_relat_1(X1))
% 7.01/1.56      | ~ v1_relat_1(X1)
% 7.01/1.56      | ~ v1_relat_1(X0) ),
% 7.01/1.56      inference(cnf_transformation,[],[f35]) ).
% 7.01/1.56  
% 7.01/1.56  cnf(c_901,plain,
% 7.01/1.56      ( r1_tarski(X0,X1) != iProver_top
% 7.01/1.56      | r1_tarski(k1_relat_1(X0),k1_relat_1(X1)) = iProver_top
% 7.01/1.56      | v1_relat_1(X0) != iProver_top
% 7.01/1.56      | v1_relat_1(X1) != iProver_top ),
% 7.01/1.56      inference(predicate_to_equality,[status(thm)],[c_7]) ).
% 7.01/1.56  
% 7.01/1.56  cnf(c_5,plain,
% 7.01/1.56      ( r1_tarski(k1_relat_1(k2_zfmisc_1(X0,X1)),X0) ),
% 7.01/1.56      inference(cnf_transformation,[],[f34]) ).
% 7.01/1.56  
% 7.01/1.56  cnf(c_903,plain,
% 7.01/1.56      ( r1_tarski(k1_relat_1(k2_zfmisc_1(X0,X1)),X0) = iProver_top ),
% 7.01/1.56      inference(predicate_to_equality,[status(thm)],[c_5]) ).
% 7.01/1.56  
% 7.01/1.56  cnf(c_14,negated_conjecture,
% 7.01/1.56      ( r1_tarski(sK1,sK2) ),
% 7.01/1.56      inference(cnf_transformation,[],[f43]) ).
% 7.01/1.56  
% 7.01/1.56  cnf(c_897,plain,
% 7.01/1.56      ( r1_tarski(sK1,sK2) = iProver_top ),
% 7.01/1.56      inference(predicate_to_equality,[status(thm)],[c_14]) ).
% 7.01/1.56  
% 7.01/1.56  cnf(c_0,plain,
% 7.01/1.56      ( ~ r1_tarski(X0,X1) | ~ r1_tarski(X2,X0) | r1_tarski(X2,X1) ),
% 7.01/1.56      inference(cnf_transformation,[],[f29]) ).
% 7.01/1.56  
% 7.01/1.56  cnf(c_908,plain,
% 7.01/1.56      ( r1_tarski(X0,X1) != iProver_top
% 7.01/1.56      | r1_tarski(X2,X0) != iProver_top
% 7.01/1.56      | r1_tarski(X2,X1) = iProver_top ),
% 7.01/1.56      inference(predicate_to_equality,[status(thm)],[c_0]) ).
% 7.01/1.56  
% 7.01/1.56  cnf(c_2358,plain,
% 7.01/1.56      ( r1_tarski(X0,sK2) = iProver_top
% 7.01/1.56      | r1_tarski(X0,sK1) != iProver_top ),
% 7.01/1.56      inference(superposition,[status(thm)],[c_897,c_908]) ).
% 7.01/1.56  
% 7.01/1.56  cnf(c_2871,plain,
% 7.01/1.56      ( r1_tarski(k1_relat_1(k2_zfmisc_1(sK1,X0)),sK2) = iProver_top ),
% 7.01/1.56      inference(superposition,[status(thm)],[c_903,c_2358]) ).
% 7.01/1.56  
% 7.01/1.56  cnf(c_2877,plain,
% 7.01/1.56      ( r1_tarski(X0,k1_relat_1(k2_zfmisc_1(sK1,X1))) != iProver_top
% 7.01/1.56      | r1_tarski(X0,sK2) = iProver_top ),
% 7.01/1.56      inference(superposition,[status(thm)],[c_2871,c_908]) ).
% 7.01/1.56  
% 7.01/1.56  cnf(c_3158,plain,
% 7.01/1.56      ( r1_tarski(X0,k2_zfmisc_1(sK1,X1)) != iProver_top
% 7.01/1.56      | r1_tarski(k1_relat_1(X0),sK2) = iProver_top
% 7.01/1.56      | v1_relat_1(X0) != iProver_top
% 7.01/1.56      | v1_relat_1(k2_zfmisc_1(sK1,X1)) != iProver_top ),
% 7.01/1.56      inference(superposition,[status(thm)],[c_901,c_2877]) ).
% 7.01/1.56  
% 7.01/1.56  cnf(c_2,plain,
% 7.01/1.56      ( ~ r1_tarski(X0,X1)
% 7.01/1.56      | r1_tarski(k2_zfmisc_1(X0,X2),k2_zfmisc_1(X1,X2)) ),
% 7.01/1.56      inference(cnf_transformation,[],[f30]) ).
% 7.01/1.56  
% 7.01/1.56  cnf(c_906,plain,
% 7.01/1.56      ( r1_tarski(X0,X1) != iProver_top
% 7.01/1.56      | r1_tarski(k2_zfmisc_1(X0,X2),k2_zfmisc_1(X1,X2)) = iProver_top ),
% 7.01/1.56      inference(predicate_to_equality,[status(thm)],[c_2]) ).
% 7.01/1.56  
% 7.01/1.56  cnf(c_3,plain,
% 7.01/1.56      ( m1_subset_1(X0,k1_zfmisc_1(X1)) | ~ r1_tarski(X0,X1) ),
% 7.01/1.56      inference(cnf_transformation,[],[f33]) ).
% 7.01/1.56  
% 7.01/1.56  cnf(c_905,plain,
% 7.01/1.56      ( m1_subset_1(X0,k1_zfmisc_1(X1)) = iProver_top
% 7.01/1.56      | r1_tarski(X0,X1) != iProver_top ),
% 7.01/1.56      inference(predicate_to_equality,[status(thm)],[c_3]) ).
% 7.01/1.56  
% 7.01/1.56  cnf(c_9,plain,
% 7.01/1.56      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 7.01/1.56      | v1_relat_1(X0) ),
% 7.01/1.56      inference(cnf_transformation,[],[f38]) ).
% 7.01/1.56  
% 7.01/1.56  cnf(c_899,plain,
% 7.01/1.56      ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) != iProver_top
% 7.01/1.56      | v1_relat_1(X0) = iProver_top ),
% 7.01/1.56      inference(predicate_to_equality,[status(thm)],[c_9]) ).
% 7.01/1.56  
% 7.01/1.56  cnf(c_1457,plain,
% 7.01/1.56      ( r1_tarski(X0,k2_zfmisc_1(X1,X2)) != iProver_top
% 7.01/1.56      | v1_relat_1(X0) = iProver_top ),
% 7.01/1.56      inference(superposition,[status(thm)],[c_905,c_899]) ).
% 7.01/1.56  
% 7.01/1.56  cnf(c_1941,plain,
% 7.01/1.56      ( r1_tarski(X0,X1) != iProver_top
% 7.01/1.56      | v1_relat_1(k2_zfmisc_1(X0,X2)) = iProver_top ),
% 7.01/1.56      inference(superposition,[status(thm)],[c_906,c_1457]) ).
% 7.01/1.56  
% 7.01/1.56  cnf(c_4162,plain,
% 7.01/1.56      ( v1_relat_1(k2_zfmisc_1(sK1,X0)) = iProver_top ),
% 7.01/1.56      inference(superposition,[status(thm)],[c_897,c_1941]) ).
% 7.01/1.56  
% 7.01/1.56  cnf(c_21154,plain,
% 7.01/1.56      ( r1_tarski(X0,k2_zfmisc_1(sK1,X1)) != iProver_top
% 7.01/1.56      | r1_tarski(k1_relat_1(X0),sK2) = iProver_top ),
% 7.01/1.56      inference(forward_subsumption_resolution,
% 7.01/1.56                [status(thm)],
% 7.01/1.56                [c_3158,c_4162,c_1457]) ).
% 7.01/1.56  
% 7.01/1.56  cnf(c_21161,plain,
% 7.01/1.56      ( r1_tarski(k1_relat_1(sK3),sK2) = iProver_top ),
% 7.01/1.56      inference(superposition,[status(thm)],[c_1197,c_21154]) ).
% 7.01/1.56  
% 7.01/1.56  cnf(c_8,plain,
% 7.01/1.56      ( ~ r1_tarski(k1_relat_1(X0),X1)
% 7.01/1.56      | ~ v1_relat_1(X0)
% 7.01/1.56      | k7_relat_1(X0,X1) = X0 ),
% 7.01/1.56      inference(cnf_transformation,[],[f37]) ).
% 7.01/1.56  
% 7.01/1.56  cnf(c_900,plain,
% 7.01/1.56      ( k7_relat_1(X0,X1) = X0
% 7.01/1.56      | r1_tarski(k1_relat_1(X0),X1) != iProver_top
% 7.01/1.56      | v1_relat_1(X0) != iProver_top ),
% 7.01/1.56      inference(predicate_to_equality,[status(thm)],[c_8]) ).
% 7.01/1.56  
% 7.01/1.56  cnf(c_21869,plain,
% 7.01/1.56      ( k7_relat_1(sK3,sK2) = sK3 | v1_relat_1(sK3) != iProver_top ),
% 7.01/1.56      inference(superposition,[status(thm)],[c_21161,c_900]) ).
% 7.01/1.56  
% 7.01/1.56  cnf(c_16,plain,
% 7.01/1.56      ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) = iProver_top ),
% 7.01/1.56      inference(predicate_to_equality,[status(thm)],[c_15]) ).
% 7.01/1.56  
% 7.01/1.56  cnf(c_1012,plain,
% 7.01/1.56      ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
% 7.01/1.56      | v1_relat_1(sK3) ),
% 7.01/1.56      inference(instantiation,[status(thm)],[c_9]) ).
% 7.01/1.56  
% 7.01/1.56  cnf(c_1013,plain,
% 7.01/1.56      ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) != iProver_top
% 7.01/1.56      | v1_relat_1(sK3) = iProver_top ),
% 7.01/1.56      inference(predicate_to_equality,[status(thm)],[c_1012]) ).
% 7.01/1.56  
% 7.01/1.56  cnf(c_1101,plain,
% 7.01/1.56      ( ~ r1_tarski(k1_relat_1(sK3),X0)
% 7.01/1.56      | ~ v1_relat_1(sK3)
% 7.01/1.56      | k7_relat_1(sK3,X0) = sK3 ),
% 7.01/1.56      inference(instantiation,[status(thm)],[c_8]) ).
% 7.01/1.56  
% 7.01/1.56  cnf(c_1278,plain,
% 7.01/1.56      ( ~ r1_tarski(k1_relat_1(sK3),sK2)
% 7.01/1.56      | ~ v1_relat_1(sK3)
% 7.01/1.56      | k7_relat_1(sK3,sK2) = sK3 ),
% 7.01/1.56      inference(instantiation,[status(thm)],[c_1101]) ).
% 7.01/1.56  
% 7.01/1.56  cnf(c_1280,plain,
% 7.01/1.56      ( k7_relat_1(sK3,sK2) = sK3
% 7.01/1.56      | r1_tarski(k1_relat_1(sK3),sK2) != iProver_top
% 7.01/1.56      | v1_relat_1(sK3) != iProver_top ),
% 7.01/1.56      inference(predicate_to_equality,[status(thm)],[c_1278]) ).
% 7.01/1.56  
% 7.01/1.56  cnf(c_23439,plain,
% 7.01/1.56      ( k7_relat_1(sK3,sK2) = sK3 ),
% 7.01/1.56      inference(global_propositional_subsumption,
% 7.01/1.56                [status(thm)],
% 7.01/1.56                [c_21869,c_16,c_1013,c_1280,c_21161]) ).
% 7.01/1.56  
% 7.01/1.56  cnf(c_10,plain,
% 7.01/1.56      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 7.01/1.56      | k5_relset_1(X1,X2,X0,X3) = k7_relat_1(X0,X3) ),
% 7.01/1.56      inference(cnf_transformation,[],[f39]) ).
% 7.01/1.56  
% 7.01/1.56  cnf(c_898,plain,
% 7.01/1.56      ( k5_relset_1(X0,X1,X2,X3) = k7_relat_1(X2,X3)
% 7.01/1.56      | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
% 7.01/1.56      inference(predicate_to_equality,[status(thm)],[c_10]) ).
% 7.01/1.56  
% 7.01/1.56  cnf(c_1305,plain,
% 7.01/1.56      ( k5_relset_1(sK1,sK0,sK3,X0) = k7_relat_1(sK3,X0) ),
% 7.01/1.56      inference(superposition,[status(thm)],[c_896,c_898]) ).
% 7.01/1.56  
% 7.01/1.56  cnf(c_11,plain,
% 7.01/1.56      ( r2_relset_1(X0,X1,X2,X2)
% 7.01/1.56      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ),
% 7.01/1.56      inference(cnf_transformation,[],[f45]) ).
% 7.01/1.56  
% 7.01/1.56  cnf(c_13,negated_conjecture,
% 7.01/1.56      ( ~ r2_relset_1(sK1,sK0,k5_relset_1(sK1,sK0,sK3,sK2),sK3) ),
% 7.01/1.56      inference(cnf_transformation,[],[f44]) ).
% 7.01/1.56  
% 7.01/1.56  cnf(c_217,plain,
% 7.01/1.56      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 7.01/1.56      | k5_relset_1(sK1,sK0,sK3,sK2) != X0
% 7.01/1.56      | sK3 != X0
% 7.01/1.56      | sK0 != X2
% 7.01/1.56      | sK1 != X1 ),
% 7.01/1.56      inference(resolution_lifted,[status(thm)],[c_11,c_13]) ).
% 7.01/1.56  
% 7.01/1.56  cnf(c_218,plain,
% 7.01/1.56      ( ~ m1_subset_1(k5_relset_1(sK1,sK0,sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
% 7.01/1.56      | sK3 != k5_relset_1(sK1,sK0,sK3,sK2) ),
% 7.01/1.56      inference(unflattening,[status(thm)],[c_217]) ).
% 7.01/1.56  
% 7.01/1.56  cnf(c_895,plain,
% 7.01/1.56      ( sK3 != k5_relset_1(sK1,sK0,sK3,sK2)
% 7.01/1.56      | m1_subset_1(k5_relset_1(sK1,sK0,sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) != iProver_top ),
% 7.01/1.56      inference(predicate_to_equality,[status(thm)],[c_218]) ).
% 7.01/1.56  
% 7.01/1.56  cnf(c_1825,plain,
% 7.01/1.56      ( k7_relat_1(sK3,sK2) != sK3
% 7.01/1.56      | m1_subset_1(k7_relat_1(sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) != iProver_top ),
% 7.01/1.56      inference(demodulation,[status(thm)],[c_1305,c_895]) ).
% 7.01/1.56  
% 7.01/1.56  cnf(c_23442,plain,
% 7.01/1.56      ( sK3 != sK3
% 7.01/1.56      | m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) != iProver_top ),
% 7.01/1.56      inference(demodulation,[status(thm)],[c_23439,c_1825]) ).
% 7.01/1.56  
% 7.01/1.56  cnf(c_554,plain,( X0 = X0 ),theory(equality) ).
% 7.01/1.56  
% 7.01/1.56  cnf(c_1208,plain,
% 7.01/1.56      ( sK3 = sK3 ),
% 7.01/1.56      inference(instantiation,[status(thm)],[c_554]) ).
% 7.01/1.56  
% 7.01/1.56  cnf(contradiction,plain,
% 7.01/1.56      ( $false ),
% 7.01/1.56      inference(minisat,[status(thm)],[c_23442,c_1208,c_16]) ).
% 7.01/1.56  
% 7.01/1.56  
% 7.01/1.56  % SZS output end CNFRefutation for theBenchmark.p
% 7.01/1.56  
% 7.01/1.56  ------                               Statistics
% 7.01/1.56  
% 7.01/1.56  ------ General
% 7.01/1.56  
% 7.01/1.56  abstr_ref_over_cycles:                  0
% 7.01/1.56  abstr_ref_under_cycles:                 0
% 7.01/1.56  gc_basic_clause_elim:                   0
% 7.01/1.56  forced_gc_time:                         0
% 7.01/1.56  parsing_time:                           0.01
% 7.01/1.56  unif_index_cands_time:                  0.
% 7.01/1.56  unif_index_add_time:                    0.
% 7.01/1.56  orderings_time:                         0.
% 7.01/1.56  out_proof_time:                         0.009
% 7.01/1.56  total_time:                             0.662
% 7.01/1.56  num_of_symbols:                         45
% 7.01/1.56  num_of_terms:                           31615
% 7.01/1.56  
% 7.01/1.56  ------ Preprocessing
% 7.01/1.56  
% 7.01/1.56  num_of_splits:                          0
% 7.01/1.56  num_of_split_atoms:                     0
% 7.01/1.56  num_of_reused_defs:                     0
% 7.01/1.56  num_eq_ax_congr_red:                    12
% 7.01/1.56  num_of_sem_filtered_clauses:            1
% 7.01/1.56  num_of_subtypes:                        0
% 7.01/1.56  monotx_restored_types:                  0
% 7.01/1.56  sat_num_of_epr_types:                   0
% 7.01/1.56  sat_num_of_non_cyclic_types:            0
% 7.01/1.56  sat_guarded_non_collapsed_types:        0
% 7.01/1.56  num_pure_diseq_elim:                    0
% 7.01/1.56  simp_replaced_by:                       0
% 7.01/1.56  res_preprocessed:                       75
% 7.01/1.56  prep_upred:                             0
% 7.01/1.56  prep_unflattend:                        19
% 7.01/1.56  smt_new_axioms:                         0
% 7.01/1.56  pred_elim_cands:                        3
% 7.01/1.56  pred_elim:                              1
% 7.01/1.56  pred_elim_cl:                           2
% 7.01/1.56  pred_elim_cycles:                       3
% 7.01/1.56  merged_defs:                            8
% 7.01/1.56  merged_defs_ncl:                        0
% 7.01/1.56  bin_hyper_res:                          8
% 7.01/1.56  prep_cycles:                            4
% 7.01/1.56  pred_elim_time:                         0.006
% 7.01/1.56  splitting_time:                         0.
% 7.01/1.56  sem_filter_time:                        0.
% 7.01/1.56  monotx_time:                            0.
% 7.01/1.56  subtype_inf_time:                       0.
% 7.01/1.56  
% 7.01/1.56  ------ Problem properties
% 7.01/1.56  
% 7.01/1.56  clauses:                                14
% 7.01/1.56  conjectures:                            2
% 7.01/1.56  epr:                                    2
% 7.01/1.56  horn:                                   14
% 7.01/1.56  ground:                                 3
% 7.01/1.56  unary:                                  3
% 7.01/1.56  binary:                                 7
% 7.01/1.56  lits:                                   31
% 7.01/1.56  lits_eq:                                3
% 7.01/1.56  fd_pure:                                0
% 7.01/1.56  fd_pseudo:                              0
% 7.01/1.56  fd_cond:                                0
% 7.01/1.56  fd_pseudo_cond:                         0
% 7.01/1.56  ac_symbols:                             0
% 7.01/1.56  
% 7.01/1.56  ------ Propositional Solver
% 7.01/1.56  
% 7.01/1.56  prop_solver_calls:                      30
% 7.01/1.56  prop_fast_solver_calls:                 750
% 7.01/1.56  smt_solver_calls:                       0
% 7.01/1.56  smt_fast_solver_calls:                  0
% 7.01/1.56  prop_num_of_clauses:                    9277
% 7.01/1.56  prop_preprocess_simplified:             20351
% 7.01/1.56  prop_fo_subsumed:                       11
% 7.01/1.56  prop_solver_time:                       0.
% 7.01/1.56  smt_solver_time:                        0.
% 7.01/1.56  smt_fast_solver_time:                   0.
% 7.01/1.56  prop_fast_solver_time:                  0.
% 7.01/1.56  prop_unsat_core_time:                   0.001
% 7.01/1.56  
% 7.01/1.56  ------ QBF
% 7.01/1.56  
% 7.01/1.56  qbf_q_res:                              0
% 7.01/1.56  qbf_num_tautologies:                    0
% 7.01/1.56  qbf_prep_cycles:                        0
% 7.01/1.56  
% 7.01/1.56  ------ BMC1
% 7.01/1.56  
% 7.01/1.56  bmc1_current_bound:                     -1
% 7.01/1.56  bmc1_last_solved_bound:                 -1
% 7.01/1.56  bmc1_unsat_core_size:                   -1
% 7.01/1.56  bmc1_unsat_core_parents_size:           -1
% 7.01/1.56  bmc1_merge_next_fun:                    0
% 7.01/1.56  bmc1_unsat_core_clauses_time:           0.
% 7.01/1.56  
% 7.01/1.56  ------ Instantiation
% 7.01/1.56  
% 7.01/1.56  inst_num_of_clauses:                    2534
% 7.01/1.56  inst_num_in_passive:                    940
% 7.01/1.56  inst_num_in_active:                     845
% 7.01/1.56  inst_num_in_unprocessed:                749
% 7.01/1.56  inst_num_of_loops:                      890
% 7.01/1.56  inst_num_of_learning_restarts:          0
% 7.01/1.56  inst_num_moves_active_passive:          44
% 7.01/1.56  inst_lit_activity:                      0
% 7.01/1.56  inst_lit_activity_moves:                1
% 7.01/1.56  inst_num_tautologies:                   0
% 7.01/1.56  inst_num_prop_implied:                  0
% 7.01/1.56  inst_num_existing_simplified:           0
% 7.01/1.56  inst_num_eq_res_simplified:             0
% 7.01/1.56  inst_num_child_elim:                    0
% 7.01/1.56  inst_num_of_dismatching_blockings:      2609
% 7.01/1.56  inst_num_of_non_proper_insts:           2120
% 7.01/1.56  inst_num_of_duplicates:                 0
% 7.01/1.56  inst_inst_num_from_inst_to_res:         0
% 7.01/1.56  inst_dismatching_checking_time:         0.
% 7.01/1.56  
% 7.01/1.56  ------ Resolution
% 7.01/1.56  
% 7.01/1.56  res_num_of_clauses:                     0
% 7.01/1.56  res_num_in_passive:                     0
% 7.01/1.56  res_num_in_active:                      0
% 7.01/1.56  res_num_of_loops:                       79
% 7.01/1.56  res_forward_subset_subsumed:            36
% 7.01/1.56  res_backward_subset_subsumed:           0
% 7.01/1.56  res_forward_subsumed:                   0
% 7.01/1.56  res_backward_subsumed:                  0
% 7.01/1.56  res_forward_subsumption_resolution:     0
% 7.01/1.56  res_backward_subsumption_resolution:    0
% 7.01/1.56  res_clause_to_clause_subsumption:       5098
% 7.01/1.56  res_orphan_elimination:                 0
% 7.01/1.56  res_tautology_del:                      425
% 7.01/1.56  res_num_eq_res_simplified:              0
% 7.01/1.56  res_num_sel_changes:                    0
% 7.01/1.56  res_moves_from_active_to_pass:          0
% 7.01/1.56  
% 7.01/1.56  ------ Superposition
% 7.01/1.56  
% 7.01/1.56  sup_time_total:                         0.
% 7.01/1.56  sup_time_generating:                    0.
% 7.01/1.56  sup_time_sim_full:                      0.
% 7.01/1.56  sup_time_sim_immed:                     0.
% 7.01/1.56  
% 7.01/1.56  sup_num_of_clauses:                     490
% 7.01/1.56  sup_num_in_active:                      174
% 7.01/1.56  sup_num_in_passive:                     316
% 7.01/1.56  sup_num_of_loops:                       176
% 7.01/1.56  sup_fw_superposition:                   420
% 7.01/1.56  sup_bw_superposition:                   470
% 7.01/1.56  sup_immediate_simplified:               394
% 7.01/1.56  sup_given_eliminated:                   0
% 7.01/1.56  comparisons_done:                       0
% 7.01/1.56  comparisons_avoided:                    0
% 7.01/1.56  
% 7.01/1.56  ------ Simplifications
% 7.01/1.56  
% 7.01/1.56  
% 7.01/1.56  sim_fw_subset_subsumed:                 112
% 7.01/1.56  sim_bw_subset_subsumed:                 5
% 7.01/1.56  sim_fw_subsumed:                        175
% 7.01/1.56  sim_bw_subsumed:                        100
% 7.01/1.56  sim_fw_subsumption_res:                 10
% 7.01/1.56  sim_bw_subsumption_res:                 0
% 7.01/1.56  sim_tautology_del:                      1
% 7.01/1.56  sim_eq_tautology_del:                   0
% 7.01/1.56  sim_eq_res_simp:                        0
% 7.01/1.56  sim_fw_demodulated:                     0
% 7.01/1.56  sim_bw_demodulated:                     2
% 7.01/1.56  sim_light_normalised:                   0
% 7.01/1.56  sim_joinable_taut:                      0
% 7.01/1.56  sim_joinable_simp:                      0
% 7.01/1.56  sim_ac_normalised:                      0
% 7.01/1.56  sim_smt_subsumption:                    0
% 7.01/1.56  
%------------------------------------------------------------------------------
