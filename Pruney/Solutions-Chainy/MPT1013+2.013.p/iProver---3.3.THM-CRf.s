%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n011.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:06:45 EST 2020

% Result     : Theorem 2.10s
% Output     : CNFRefutation 2.10s
% Verified   : 
% Statistics : Number of formulae       :  139 ( 322 expanded)
%              Number of clauses        :   96 ( 150 expanded)
%              Number of leaves         :   19 (  71 expanded)
%              Depth                    :   16
%              Number of atoms          :  347 (1040 expanded)
%              Number of equality atoms :  196 ( 546 expanded)
%              Maximal formula depth    :   10 (   4 average)
%              Maximal clause size      :   10 (   2 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f10,conjecture,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
     => ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
         => ( ( k2_relset_1(X0,X0,X2) = X0
              & k2_relset_1(X0,X0,X1) = X0 )
           => k2_relset_1(X0,X0,k4_relset_1(X0,X0,X0,X0,X2,X1)) = X0 ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f11,negated_conjecture,(
    ~ ! [X0,X1] :
        ( m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
       => ! [X2] :
            ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
           => ( ( k2_relset_1(X0,X0,X2) = X0
                & k2_relset_1(X0,X0,X1) = X0 )
             => k2_relset_1(X0,X0,k4_relset_1(X0,X0,X0,X0,X2,X1)) = X0 ) ) ) ),
    inference(negated_conjecture,[],[f10])).

fof(f25,plain,(
    ? [X0,X1] :
      ( ? [X2] :
          ( k2_relset_1(X0,X0,k4_relset_1(X0,X0,X0,X0,X2,X1)) != X0
          & k2_relset_1(X0,X0,X2) = X0
          & k2_relset_1(X0,X0,X1) = X0
          & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) )
      & m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f26,plain,(
    ? [X0,X1] :
      ( ? [X2] :
          ( k2_relset_1(X0,X0,k4_relset_1(X0,X0,X0,X0,X2,X1)) != X0
          & k2_relset_1(X0,X0,X2) = X0
          & k2_relset_1(X0,X0,X1) = X0
          & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) )
      & m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) ) ),
    inference(flattening,[],[f25])).

fof(f28,plain,(
    ! [X0,X1] :
      ( ? [X2] :
          ( k2_relset_1(X0,X0,k4_relset_1(X0,X0,X0,X0,X2,X1)) != X0
          & k2_relset_1(X0,X0,X2) = X0
          & k2_relset_1(X0,X0,X1) = X0
          & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) )
     => ( k2_relset_1(X0,X0,k4_relset_1(X0,X0,X0,X0,sK2,X1)) != X0
        & k2_relset_1(X0,X0,sK2) = X0
        & k2_relset_1(X0,X0,X1) = X0
        & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) ) ) ),
    introduced(choice_axiom,[])).

fof(f27,plain,
    ( ? [X0,X1] :
        ( ? [X2] :
            ( k2_relset_1(X0,X0,k4_relset_1(X0,X0,X0,X0,X2,X1)) != X0
            & k2_relset_1(X0,X0,X2) = X0
            & k2_relset_1(X0,X0,X1) = X0
            & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) )
        & m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) )
   => ( ? [X2] :
          ( k2_relset_1(sK0,sK0,k4_relset_1(sK0,sK0,sK0,sK0,X2,sK1)) != sK0
          & k2_relset_1(sK0,sK0,X2) = sK0
          & k2_relset_1(sK0,sK0,sK1) = sK0
          & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) )
      & m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) ) ),
    introduced(choice_axiom,[])).

fof(f29,plain,
    ( k2_relset_1(sK0,sK0,k4_relset_1(sK0,sK0,sK0,sK0,sK2,sK1)) != sK0
    & k2_relset_1(sK0,sK0,sK2) = sK0
    & k2_relset_1(sK0,sK0,sK1) = sK0
    & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
    & m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f26,f28,f27])).

fof(f39,plain,(
    m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) ),
    inference(cnf_transformation,[],[f29])).

fof(f6,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => ( v5_relat_1(X2,X1)
        & v4_relat_1(X2,X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f12,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => v4_relat_1(X2,X0) ) ),
    inference(pure_predicate_removal,[],[f6])).

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

fof(f3,axiom,(
    ! [X0,X1] :
      ( ( v4_relat_1(X1,X0)
        & v1_relat_1(X1) )
     => k7_relat_1(X1,X0) = X1 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f14,plain,(
    ! [X0,X1] :
      ( k7_relat_1(X1,X0) = X1
      | ~ v4_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f15,plain,(
    ! [X0,X1] :
      ( k7_relat_1(X1,X0) = X1
      | ~ v4_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f14])).

fof(f32,plain,(
    ! [X0,X1] :
      ( k7_relat_1(X1,X0) = X1
      | ~ v4_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f15])).

fof(f2,axiom,(
    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f31,plain,(
    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1)) ),
    inference(cnf_transformation,[],[f2])).

fof(f1,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(X0))
         => v1_relat_1(X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f13,plain,(
    ! [X0] :
      ( ! [X1] :
          ( v1_relat_1(X1)
          | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f30,plain,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f13])).

fof(f5,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => r1_tarski(k1_relat_1(k7_relat_1(X1,X0)),X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f18,plain,(
    ! [X0,X1] :
      ( r1_tarski(k1_relat_1(k7_relat_1(X1,X0)),X0)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f34,plain,(
    ! [X0,X1] :
      ( r1_tarski(k1_relat_1(k7_relat_1(X1,X0)),X0)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f40,plain,(
    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) ),
    inference(cnf_transformation,[],[f29])).

fof(f8,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k2_relat_1(X2) = k2_relset_1(X0,X1,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f22,plain,(
    ! [X0,X1,X2] :
      ( k2_relat_1(X2) = k2_relset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f37,plain,(
    ! [X2,X0,X1] :
      ( k2_relat_1(X2) = k2_relset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f42,plain,(
    k2_relset_1(sK0,sK0,sK2) = sK0 ),
    inference(cnf_transformation,[],[f29])).

fof(f4,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( v1_relat_1(X1)
         => ( r1_tarski(k1_relat_1(X0),k2_relat_1(X1))
           => k2_relat_1(X0) = k2_relat_1(k5_relat_1(X1,X0)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f16,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k2_relat_1(X0) = k2_relat_1(k5_relat_1(X1,X0))
          | ~ r1_tarski(k1_relat_1(X0),k2_relat_1(X1))
          | ~ v1_relat_1(X1) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f17,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k2_relat_1(X0) = k2_relat_1(k5_relat_1(X1,X0))
          | ~ r1_tarski(k1_relat_1(X0),k2_relat_1(X1))
          | ~ v1_relat_1(X1) )
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f16])).

fof(f33,plain,(
    ! [X0,X1] :
      ( k2_relat_1(X0) = k2_relat_1(k5_relat_1(X1,X0))
      | ~ r1_tarski(k1_relat_1(X0),k2_relat_1(X1))
      | ~ v1_relat_1(X1)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f41,plain,(
    k2_relset_1(sK0,sK0,sK1) = sK0 ),
    inference(cnf_transformation,[],[f29])).

fof(f9,axiom,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( ( m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
        & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) )
     => k5_relat_1(X4,X5) = k4_relset_1(X0,X1,X2,X3,X4,X5) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f23,plain,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( k5_relat_1(X4,X5) = k4_relset_1(X0,X1,X2,X3,X4,X5)
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f24,plain,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( k5_relat_1(X4,X5) = k4_relset_1(X0,X1,X2,X3,X4,X5)
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(flattening,[],[f23])).

fof(f38,plain,(
    ! [X4,X2,X0,X5,X3,X1] :
      ( k5_relat_1(X4,X5) = k4_relset_1(X0,X1,X2,X3,X4,X5)
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f7,axiom,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( ( m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
        & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) )
     => m1_subset_1(k4_relset_1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3))) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f20,plain,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( m1_subset_1(k4_relset_1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3)))
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f21,plain,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( m1_subset_1(k4_relset_1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3)))
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(flattening,[],[f20])).

fof(f36,plain,(
    ! [X4,X2,X0,X5,X3,X1] :
      ( m1_subset_1(k4_relset_1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3)))
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f43,plain,(
    k2_relset_1(sK0,sK0,k4_relset_1(sK0,sK0,sK0,sK0,sK2,sK1)) != sK0 ),
    inference(cnf_transformation,[],[f29])).

cnf(c_13,negated_conjecture,
    ( m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) ),
    inference(cnf_transformation,[],[f39])).

cnf(c_276,negated_conjecture,
    ( m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) ),
    inference(subtyping,[status(esa)],[c_13])).

cnf(c_521,plain,
    ( m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_276])).

cnf(c_5,plain,
    ( v4_relat_1(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) ),
    inference(cnf_transformation,[],[f35])).

cnf(c_2,plain,
    ( ~ v4_relat_1(X0,X1)
    | ~ v1_relat_1(X0)
    | k7_relat_1(X0,X1) = X0 ),
    inference(cnf_transformation,[],[f32])).

cnf(c_133,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ v1_relat_1(X0)
    | k7_relat_1(X0,X1) = X0 ),
    inference(resolution,[status(thm)],[c_5,c_2])).

cnf(c_275,plain,
    ( ~ m1_subset_1(X0_43,k1_zfmisc_1(k2_zfmisc_1(X0_45,X1_45)))
    | ~ v1_relat_1(X0_43)
    | k7_relat_1(X0_43,X0_45) = X0_43 ),
    inference(subtyping,[status(esa)],[c_133])).

cnf(c_522,plain,
    ( k7_relat_1(X0_43,X0_45) = X0_43
    | m1_subset_1(X0_43,k1_zfmisc_1(k2_zfmisc_1(X0_45,X1_45))) != iProver_top
    | v1_relat_1(X0_43) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_275])).

cnf(c_1,plain,
    ( v1_relat_1(k2_zfmisc_1(X0,X1)) ),
    inference(cnf_transformation,[],[f31])).

cnf(c_286,plain,
    ( v1_relat_1(k2_zfmisc_1(X0_45,X1_45)) ),
    inference(subtyping,[status(esa)],[c_1])).

cnf(c_319,plain,
    ( v1_relat_1(k2_zfmisc_1(X0_45,X1_45)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_286])).

cnf(c_337,plain,
    ( k7_relat_1(X0_43,X0_45) = X0_43
    | m1_subset_1(X0_43,k1_zfmisc_1(k2_zfmisc_1(X0_45,X1_45))) != iProver_top
    | v1_relat_1(X0_43) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_275])).

cnf(c_0,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | ~ v1_relat_1(X1)
    | v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f30])).

cnf(c_287,plain,
    ( ~ m1_subset_1(X0_43,k1_zfmisc_1(X1_43))
    | ~ v1_relat_1(X1_43)
    | v1_relat_1(X0_43) ),
    inference(subtyping,[status(esa)],[c_0])).

cnf(c_600,plain,
    ( ~ m1_subset_1(X0_43,k1_zfmisc_1(k2_zfmisc_1(X0_45,X1_45)))
    | v1_relat_1(X0_43)
    | ~ v1_relat_1(k2_zfmisc_1(X0_45,X1_45)) ),
    inference(instantiation,[status(thm)],[c_287])).

cnf(c_601,plain,
    ( m1_subset_1(X0_43,k1_zfmisc_1(k2_zfmisc_1(X0_45,X1_45))) != iProver_top
    | v1_relat_1(X0_43) = iProver_top
    | v1_relat_1(k2_zfmisc_1(X0_45,X1_45)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_600])).

cnf(c_1878,plain,
    ( m1_subset_1(X0_43,k1_zfmisc_1(k2_zfmisc_1(X0_45,X1_45))) != iProver_top
    | k7_relat_1(X0_43,X0_45) = X0_43 ),
    inference(global_propositional_subsumption,[status(thm)],[c_522,c_319,c_337,c_601])).

cnf(c_1879,plain,
    ( k7_relat_1(X0_43,X0_45) = X0_43
    | m1_subset_1(X0_43,k1_zfmisc_1(k2_zfmisc_1(X0_45,X1_45))) != iProver_top ),
    inference(renaming,[status(thm)],[c_1878])).

cnf(c_1887,plain,
    ( k7_relat_1(sK1,sK0) = sK1 ),
    inference(superposition,[status(thm)],[c_521,c_1879])).

cnf(c_4,plain,
    ( r1_tarski(k1_relat_1(k7_relat_1(X0,X1)),X1)
    | ~ v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f34])).

cnf(c_284,plain,
    ( r1_tarski(k1_relat_1(k7_relat_1(X0_43,X0_45)),X0_45)
    | ~ v1_relat_1(X0_43) ),
    inference(subtyping,[status(esa)],[c_4])).

cnf(c_516,plain,
    ( r1_tarski(k1_relat_1(k7_relat_1(X0_43,X0_45)),X0_45) = iProver_top
    | v1_relat_1(X0_43) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_284])).

cnf(c_2055,plain,
    ( r1_tarski(k1_relat_1(sK1),sK0) = iProver_top
    | v1_relat_1(sK1) != iProver_top ),
    inference(superposition,[status(thm)],[c_1887,c_516])).

cnf(c_14,plain,
    ( m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_13])).

cnf(c_38,plain,
    ( v1_relat_1(k2_zfmisc_1(sK0,sK0)) ),
    inference(instantiation,[status(thm)],[c_1])).

cnf(c_37,plain,
    ( v1_relat_1(k2_zfmisc_1(X0,X1)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1])).

cnf(c_39,plain,
    ( v1_relat_1(k2_zfmisc_1(sK0,sK0)) = iProver_top ),
    inference(instantiation,[status(thm)],[c_37])).

cnf(c_289,plain,
    ( X0_43 = X0_43 ),
    theory(equality)).

cnf(c_314,plain,
    ( sK1 = sK1 ),
    inference(instantiation,[status(thm)],[c_289])).

cnf(c_291,plain,
    ( X0_45 = X0_45 ),
    theory(equality)).

cnf(c_316,plain,
    ( sK0 = sK0 ),
    inference(instantiation,[status(thm)],[c_291])).

cnf(c_323,plain,
    ( r1_tarski(k1_relat_1(k7_relat_1(X0_43,X0_45)),X0_45) = iProver_top
    | v1_relat_1(X0_43) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_284])).

cnf(c_325,plain,
    ( r1_tarski(k1_relat_1(k7_relat_1(sK1,sK0)),sK0) = iProver_top
    | v1_relat_1(sK1) != iProver_top ),
    inference(instantiation,[status(thm)],[c_323])).

cnf(c_338,plain,
    ( ~ m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
    | ~ v1_relat_1(sK1)
    | k7_relat_1(sK1,sK0) = sK1 ),
    inference(instantiation,[status(thm)],[c_275])).

cnf(c_602,plain,
    ( ~ m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
    | ~ v1_relat_1(k2_zfmisc_1(sK0,sK0))
    | v1_relat_1(sK1) ),
    inference(instantiation,[status(thm)],[c_600])).

cnf(c_603,plain,
    ( m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) != iProver_top
    | v1_relat_1(k2_zfmisc_1(sK0,sK0)) != iProver_top
    | v1_relat_1(sK1) = iProver_top ),
    inference(instantiation,[status(thm)],[c_601])).

cnf(c_301,plain,
    ( ~ r1_tarski(X0_46,X0_45)
    | r1_tarski(X1_46,X1_45)
    | X1_46 != X0_46
    | X1_45 != X0_45 ),
    theory(equality)).

cnf(c_824,plain,
    ( r1_tarski(X0_46,X0_45)
    | ~ r1_tarski(k1_relat_1(k7_relat_1(X0_43,X1_45)),X1_45)
    | X0_46 != k1_relat_1(k7_relat_1(X0_43,X1_45))
    | X0_45 != X1_45 ),
    inference(instantiation,[status(thm)],[c_301])).

cnf(c_1041,plain,
    ( r1_tarski(k1_relat_1(X0_43),X0_45)
    | ~ r1_tarski(k1_relat_1(k7_relat_1(X1_43,X1_45)),X1_45)
    | k1_relat_1(X0_43) != k1_relat_1(k7_relat_1(X1_43,X1_45))
    | X0_45 != X1_45 ),
    inference(instantiation,[status(thm)],[c_824])).

cnf(c_1043,plain,
    ( k1_relat_1(X0_43) != k1_relat_1(k7_relat_1(X1_43,X0_45))
    | X1_45 != X0_45
    | r1_tarski(k1_relat_1(X0_43),X1_45) = iProver_top
    | r1_tarski(k1_relat_1(k7_relat_1(X1_43,X0_45)),X0_45) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1041])).

cnf(c_1045,plain,
    ( k1_relat_1(sK1) != k1_relat_1(k7_relat_1(sK1,sK0))
    | sK0 != sK0
    | r1_tarski(k1_relat_1(k7_relat_1(sK1,sK0)),sK0) != iProver_top
    | r1_tarski(k1_relat_1(sK1),sK0) = iProver_top ),
    inference(instantiation,[status(thm)],[c_1043])).

cnf(c_300,plain,
    ( k1_relat_1(X0_43) = k1_relat_1(X1_43)
    | X0_43 != X1_43 ),
    theory(equality)).

cnf(c_1042,plain,
    ( k1_relat_1(X0_43) = k1_relat_1(k7_relat_1(X1_43,X0_45))
    | X0_43 != k7_relat_1(X1_43,X0_45) ),
    inference(instantiation,[status(thm)],[c_300])).

cnf(c_1047,plain,
    ( k1_relat_1(sK1) = k1_relat_1(k7_relat_1(sK1,sK0))
    | sK1 != k7_relat_1(sK1,sK0) ),
    inference(instantiation,[status(thm)],[c_1042])).

cnf(c_293,plain,
    ( X0_43 != X1_43
    | X2_43 != X1_43
    | X2_43 = X0_43 ),
    theory(equality)).

cnf(c_1359,plain,
    ( X0_43 != X1_43
    | X0_43 = k7_relat_1(X2_43,X0_45)
    | k7_relat_1(X2_43,X0_45) != X1_43 ),
    inference(instantiation,[status(thm)],[c_293])).

cnf(c_1360,plain,
    ( k7_relat_1(sK1,sK0) != sK1
    | sK1 = k7_relat_1(sK1,sK0)
    | sK1 != sK1 ),
    inference(instantiation,[status(thm)],[c_1359])).

cnf(c_2464,plain,
    ( r1_tarski(k1_relat_1(sK1),sK0) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_2055,c_13,c_14,c_38,c_39,c_314,c_316,c_325,c_338,c_602,c_603,c_1045,c_1047,c_1360])).

cnf(c_12,negated_conjecture,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) ),
    inference(cnf_transformation,[],[f40])).

cnf(c_277,negated_conjecture,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) ),
    inference(subtyping,[status(esa)],[c_12])).

cnf(c_520,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_277])).

cnf(c_7,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k2_relset_1(X1,X2,X0) = k2_relat_1(X0) ),
    inference(cnf_transformation,[],[f37])).

cnf(c_282,plain,
    ( ~ m1_subset_1(X0_43,k1_zfmisc_1(k2_zfmisc_1(X0_45,X1_45)))
    | k2_relset_1(X0_45,X1_45,X0_43) = k2_relat_1(X0_43) ),
    inference(subtyping,[status(esa)],[c_7])).

cnf(c_518,plain,
    ( k2_relset_1(X0_45,X1_45,X0_43) = k2_relat_1(X0_43)
    | m1_subset_1(X0_43,k1_zfmisc_1(k2_zfmisc_1(X0_45,X1_45))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_282])).

cnf(c_709,plain,
    ( k2_relset_1(sK0,sK0,sK2) = k2_relat_1(sK2) ),
    inference(superposition,[status(thm)],[c_520,c_518])).

cnf(c_10,negated_conjecture,
    ( k2_relset_1(sK0,sK0,sK2) = sK0 ),
    inference(cnf_transformation,[],[f42])).

cnf(c_279,negated_conjecture,
    ( k2_relset_1(sK0,sK0,sK2) = sK0 ),
    inference(subtyping,[status(esa)],[c_10])).

cnf(c_715,plain,
    ( k2_relat_1(sK2) = sK0 ),
    inference(light_normalisation,[status(thm)],[c_709,c_279])).

cnf(c_3,plain,
    ( ~ r1_tarski(k1_relat_1(X0),k2_relat_1(X1))
    | ~ v1_relat_1(X0)
    | ~ v1_relat_1(X1)
    | k2_relat_1(k5_relat_1(X1,X0)) = k2_relat_1(X0) ),
    inference(cnf_transformation,[],[f33])).

cnf(c_285,plain,
    ( ~ r1_tarski(k1_relat_1(X0_43),k2_relat_1(X1_43))
    | ~ v1_relat_1(X0_43)
    | ~ v1_relat_1(X1_43)
    | k2_relat_1(k5_relat_1(X1_43,X0_43)) = k2_relat_1(X0_43) ),
    inference(subtyping,[status(esa)],[c_3])).

cnf(c_515,plain,
    ( k2_relat_1(k5_relat_1(X0_43,X1_43)) = k2_relat_1(X1_43)
    | r1_tarski(k1_relat_1(X1_43),k2_relat_1(X0_43)) != iProver_top
    | v1_relat_1(X1_43) != iProver_top
    | v1_relat_1(X0_43) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_285])).

cnf(c_862,plain,
    ( k2_relat_1(k5_relat_1(sK2,X0_43)) = k2_relat_1(X0_43)
    | r1_tarski(k1_relat_1(X0_43),sK0) != iProver_top
    | v1_relat_1(X0_43) != iProver_top
    | v1_relat_1(sK2) != iProver_top ),
    inference(superposition,[status(thm)],[c_715,c_515])).

cnf(c_513,plain,
    ( m1_subset_1(X0_43,k1_zfmisc_1(X1_43)) != iProver_top
    | v1_relat_1(X1_43) != iProver_top
    | v1_relat_1(X0_43) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_287])).

cnf(c_770,plain,
    ( v1_relat_1(k2_zfmisc_1(sK0,sK0)) != iProver_top
    | v1_relat_1(sK2) = iProver_top ),
    inference(superposition,[status(thm)],[c_520,c_513])).

cnf(c_1543,plain,
    ( v1_relat_1(X0_43) != iProver_top
    | r1_tarski(k1_relat_1(X0_43),sK0) != iProver_top
    | k2_relat_1(k5_relat_1(sK2,X0_43)) = k2_relat_1(X0_43) ),
    inference(global_propositional_subsumption,[status(thm)],[c_862,c_39,c_770])).

cnf(c_1544,plain,
    ( k2_relat_1(k5_relat_1(sK2,X0_43)) = k2_relat_1(X0_43)
    | r1_tarski(k1_relat_1(X0_43),sK0) != iProver_top
    | v1_relat_1(X0_43) != iProver_top ),
    inference(renaming,[status(thm)],[c_1543])).

cnf(c_2469,plain,
    ( k2_relat_1(k5_relat_1(sK2,sK1)) = k2_relat_1(sK1)
    | v1_relat_1(sK1) != iProver_top ),
    inference(superposition,[status(thm)],[c_2464,c_1544])).

cnf(c_710,plain,
    ( k2_relset_1(sK0,sK0,sK1) = k2_relat_1(sK1) ),
    inference(superposition,[status(thm)],[c_521,c_518])).

cnf(c_11,negated_conjecture,
    ( k2_relset_1(sK0,sK0,sK1) = sK0 ),
    inference(cnf_transformation,[],[f41])).

cnf(c_278,negated_conjecture,
    ( k2_relset_1(sK0,sK0,sK1) = sK0 ),
    inference(subtyping,[status(esa)],[c_11])).

cnf(c_712,plain,
    ( k2_relat_1(sK1) = sK0 ),
    inference(light_normalisation,[status(thm)],[c_710,c_278])).

cnf(c_2476,plain,
    ( k2_relat_1(k5_relat_1(sK2,sK1)) = sK0
    | v1_relat_1(sK1) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_2469,c_712])).

cnf(c_294,plain,
    ( X0_45 != X1_45
    | X2_45 != X1_45
    | X2_45 = X0_45 ),
    theory(equality)).

cnf(c_1168,plain,
    ( k2_relat_1(X0_43) != X0_45
    | sK0 != X0_45
    | sK0 = k2_relat_1(X0_43) ),
    inference(instantiation,[status(thm)],[c_294])).

cnf(c_2419,plain,
    ( k2_relat_1(k5_relat_1(sK2,sK1)) != X0_45
    | sK0 != X0_45
    | sK0 = k2_relat_1(k5_relat_1(sK2,sK1)) ),
    inference(instantiation,[status(thm)],[c_1168])).

cnf(c_2420,plain,
    ( k2_relat_1(k5_relat_1(sK2,sK1)) != sK0
    | sK0 = k2_relat_1(k5_relat_1(sK2,sK1))
    | sK0 != sK0 ),
    inference(instantiation,[status(thm)],[c_2419])).

cnf(c_983,plain,
    ( X0_45 != X1_45
    | k2_relat_1(k4_relset_1(sK0,sK0,sK0,sK0,sK2,sK1)) != X1_45
    | k2_relat_1(k4_relset_1(sK0,sK0,sK0,sK0,sK2,sK1)) = X0_45 ),
    inference(instantiation,[status(thm)],[c_294])).

cnf(c_1587,plain,
    ( X0_45 != k2_relat_1(k5_relat_1(sK2,sK1))
    | k2_relat_1(k4_relset_1(sK0,sK0,sK0,sK0,sK2,sK1)) = X0_45
    | k2_relat_1(k4_relset_1(sK0,sK0,sK0,sK0,sK2,sK1)) != k2_relat_1(k5_relat_1(sK2,sK1)) ),
    inference(instantiation,[status(thm)],[c_983])).

cnf(c_1588,plain,
    ( k2_relat_1(k4_relset_1(sK0,sK0,sK0,sK0,sK2,sK1)) != k2_relat_1(k5_relat_1(sK2,sK1))
    | k2_relat_1(k4_relset_1(sK0,sK0,sK0,sK0,sK2,sK1)) = sK0
    | sK0 != k2_relat_1(k5_relat_1(sK2,sK1)) ),
    inference(instantiation,[status(thm)],[c_1587])).

cnf(c_299,plain,
    ( k2_relat_1(X0_43) = k2_relat_1(X1_43)
    | X0_43 != X1_43 ),
    theory(equality)).

cnf(c_985,plain,
    ( k2_relat_1(k4_relset_1(sK0,sK0,sK0,sK0,sK2,sK1)) = k2_relat_1(X0_43)
    | k4_relset_1(sK0,sK0,sK0,sK0,sK2,sK1) != X0_43 ),
    inference(instantiation,[status(thm)],[c_299])).

cnf(c_1177,plain,
    ( k2_relat_1(k4_relset_1(sK0,sK0,sK0,sK0,sK2,sK1)) = k2_relat_1(k5_relat_1(sK2,sK1))
    | k4_relset_1(sK0,sK0,sK0,sK0,sK2,sK1) != k5_relat_1(sK2,sK1) ),
    inference(instantiation,[status(thm)],[c_985])).

cnf(c_8,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X4,X5)))
    | k4_relset_1(X4,X5,X1,X2,X3,X0) = k5_relat_1(X3,X0) ),
    inference(cnf_transformation,[],[f38])).

cnf(c_281,plain,
    ( ~ m1_subset_1(X0_43,k1_zfmisc_1(k2_zfmisc_1(X0_45,X1_45)))
    | ~ m1_subset_1(X1_43,k1_zfmisc_1(k2_zfmisc_1(X2_45,X3_45)))
    | k4_relset_1(X2_45,X3_45,X0_45,X1_45,X1_43,X0_43) = k5_relat_1(X1_43,X0_43) ),
    inference(subtyping,[status(esa)],[c_8])).

cnf(c_843,plain,
    ( ~ m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
    | k4_relset_1(sK0,sK0,sK0,sK0,sK2,sK1) = k5_relat_1(sK2,sK1) ),
    inference(instantiation,[status(thm)],[c_281])).

cnf(c_6,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X4,X5)))
    | m1_subset_1(k4_relset_1(X4,X5,X1,X2,X3,X0),k1_zfmisc_1(k2_zfmisc_1(X4,X2))) ),
    inference(cnf_transformation,[],[f36])).

cnf(c_283,plain,
    ( ~ m1_subset_1(X0_43,k1_zfmisc_1(k2_zfmisc_1(X0_45,X1_45)))
    | ~ m1_subset_1(X1_43,k1_zfmisc_1(k2_zfmisc_1(X2_45,X3_45)))
    | m1_subset_1(k4_relset_1(X2_45,X3_45,X0_45,X1_45,X1_43,X0_43),k1_zfmisc_1(k2_zfmisc_1(X2_45,X1_45))) ),
    inference(subtyping,[status(esa)],[c_6])).

cnf(c_740,plain,
    ( m1_subset_1(k4_relset_1(sK0,sK0,sK0,sK0,sK2,sK1),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
    | ~ m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) ),
    inference(instantiation,[status(thm)],[c_283])).

cnf(c_738,plain,
    ( k2_relat_1(k4_relset_1(sK0,sK0,sK0,sK0,sK2,sK1)) != X0_45
    | sK0 != X0_45
    | sK0 = k2_relat_1(k4_relset_1(sK0,sK0,sK0,sK0,sK2,sK1)) ),
    inference(instantiation,[status(thm)],[c_294])).

cnf(c_739,plain,
    ( k2_relat_1(k4_relset_1(sK0,sK0,sK0,sK0,sK2,sK1)) != sK0
    | sK0 = k2_relat_1(k4_relset_1(sK0,sK0,sK0,sK0,sK2,sK1))
    | sK0 != sK0 ),
    inference(instantiation,[status(thm)],[c_738])).

cnf(c_645,plain,
    ( ~ m1_subset_1(k4_relset_1(sK0,sK0,sK0,sK0,sK2,sK1),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
    | k2_relset_1(sK0,sK0,k4_relset_1(sK0,sK0,sK0,sK0,sK2,sK1)) = k2_relat_1(k4_relset_1(sK0,sK0,sK0,sK0,sK2,sK1)) ),
    inference(instantiation,[status(thm)],[c_282])).

cnf(c_610,plain,
    ( k2_relset_1(sK0,sK0,k4_relset_1(sK0,sK0,sK0,sK0,sK2,sK1)) != X0_45
    | k2_relset_1(sK0,sK0,k4_relset_1(sK0,sK0,sK0,sK0,sK2,sK1)) = sK0
    | sK0 != X0_45 ),
    inference(instantiation,[status(thm)],[c_294])).

cnf(c_644,plain,
    ( k2_relset_1(sK0,sK0,k4_relset_1(sK0,sK0,sK0,sK0,sK2,sK1)) != k2_relat_1(k4_relset_1(sK0,sK0,sK0,sK0,sK2,sK1))
    | k2_relset_1(sK0,sK0,k4_relset_1(sK0,sK0,sK0,sK0,sK2,sK1)) = sK0
    | sK0 != k2_relat_1(k4_relset_1(sK0,sK0,sK0,sK0,sK2,sK1)) ),
    inference(instantiation,[status(thm)],[c_610])).

cnf(c_9,negated_conjecture,
    ( k2_relset_1(sK0,sK0,k4_relset_1(sK0,sK0,sK0,sK0,sK2,sK1)) != sK0 ),
    inference(cnf_transformation,[],[f43])).

cnf(c_280,negated_conjecture,
    ( k2_relset_1(sK0,sK0,k4_relset_1(sK0,sK0,sK0,sK0,sK2,sK1)) != sK0 ),
    inference(subtyping,[status(esa)],[c_9])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_2476,c_2420,c_1588,c_1177,c_843,c_740,c_739,c_645,c_644,c_603,c_280,c_316,c_39,c_12,c_14,c_13])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.12/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : iproveropt_run.sh %d %s
% 0.13/0.34  % Computer   : n011.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 18:37:27 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  % Running in FOF mode
% 2.10/1.00  % SZS status Started for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.10/1.00  
% 2.10/1.00  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 2.10/1.00  
% 2.10/1.00  ------  iProver source info
% 2.10/1.00  
% 2.10/1.00  git: date: 2020-06-30 10:37:57 +0100
% 2.10/1.00  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 2.10/1.00  git: non_committed_changes: false
% 2.10/1.00  git: last_make_outside_of_git: false
% 2.10/1.00  
% 2.10/1.00  ------ 
% 2.10/1.00  
% 2.10/1.00  ------ Input Options
% 2.10/1.00  
% 2.10/1.00  --out_options                           all
% 2.10/1.00  --tptp_safe_out                         true
% 2.10/1.00  --problem_path                          ""
% 2.10/1.00  --include_path                          ""
% 2.10/1.00  --clausifier                            res/vclausify_rel
% 2.10/1.00  --clausifier_options                    --mode clausify
% 2.10/1.00  --stdin                                 false
% 2.10/1.00  --stats_out                             all
% 2.10/1.00  
% 2.10/1.00  ------ General Options
% 2.10/1.00  
% 2.10/1.00  --fof                                   false
% 2.10/1.00  --time_out_real                         305.
% 2.10/1.00  --time_out_virtual                      -1.
% 2.10/1.00  --symbol_type_check                     false
% 2.10/1.00  --clausify_out                          false
% 2.10/1.00  --sig_cnt_out                           false
% 2.10/1.00  --trig_cnt_out                          false
% 2.10/1.00  --trig_cnt_out_tolerance                1.
% 2.10/1.00  --trig_cnt_out_sk_spl                   false
% 2.10/1.00  --abstr_cl_out                          false
% 2.10/1.00  
% 2.10/1.00  ------ Global Options
% 2.10/1.00  
% 2.10/1.00  --schedule                              default
% 2.10/1.00  --add_important_lit                     false
% 2.10/1.00  --prop_solver_per_cl                    1000
% 2.10/1.00  --min_unsat_core                        false
% 2.10/1.00  --soft_assumptions                      false
% 2.10/1.00  --soft_lemma_size                       3
% 2.10/1.00  --prop_impl_unit_size                   0
% 2.10/1.00  --prop_impl_unit                        []
% 2.10/1.00  --share_sel_clauses                     true
% 2.10/1.00  --reset_solvers                         false
% 2.10/1.00  --bc_imp_inh                            [conj_cone]
% 2.10/1.00  --conj_cone_tolerance                   3.
% 2.10/1.00  --extra_neg_conj                        none
% 2.10/1.00  --large_theory_mode                     true
% 2.10/1.00  --prolific_symb_bound                   200
% 2.10/1.00  --lt_threshold                          2000
% 2.10/1.00  --clause_weak_htbl                      true
% 2.10/1.00  --gc_record_bc_elim                     false
% 2.10/1.00  
% 2.10/1.00  ------ Preprocessing Options
% 2.10/1.00  
% 2.10/1.00  --preprocessing_flag                    true
% 2.10/1.00  --time_out_prep_mult                    0.1
% 2.10/1.00  --splitting_mode                        input
% 2.10/1.00  --splitting_grd                         true
% 2.10/1.00  --splitting_cvd                         false
% 2.10/1.00  --splitting_cvd_svl                     false
% 2.10/1.00  --splitting_nvd                         32
% 2.10/1.00  --sub_typing                            true
% 2.10/1.00  --prep_gs_sim                           true
% 2.10/1.00  --prep_unflatten                        true
% 2.10/1.00  --prep_res_sim                          true
% 2.10/1.00  --prep_upred                            true
% 2.10/1.00  --prep_sem_filter                       exhaustive
% 2.10/1.00  --prep_sem_filter_out                   false
% 2.10/1.00  --pred_elim                             true
% 2.10/1.00  --res_sim_input                         true
% 2.10/1.00  --eq_ax_congr_red                       true
% 2.10/1.00  --pure_diseq_elim                       true
% 2.10/1.00  --brand_transform                       false
% 2.10/1.00  --non_eq_to_eq                          false
% 2.10/1.00  --prep_def_merge                        true
% 2.10/1.00  --prep_def_merge_prop_impl              false
% 2.10/1.00  --prep_def_merge_mbd                    true
% 2.10/1.00  --prep_def_merge_tr_red                 false
% 2.10/1.00  --prep_def_merge_tr_cl                  false
% 2.10/1.00  --smt_preprocessing                     true
% 2.10/1.00  --smt_ac_axioms                         fast
% 2.10/1.00  --preprocessed_out                      false
% 2.10/1.00  --preprocessed_stats                    false
% 2.10/1.00  
% 2.10/1.00  ------ Abstraction refinement Options
% 2.10/1.00  
% 2.10/1.00  --abstr_ref                             []
% 2.10/1.00  --abstr_ref_prep                        false
% 2.10/1.00  --abstr_ref_until_sat                   false
% 2.10/1.00  --abstr_ref_sig_restrict                funpre
% 2.10/1.00  --abstr_ref_af_restrict_to_split_sk     false
% 2.10/1.00  --abstr_ref_under                       []
% 2.10/1.00  
% 2.10/1.00  ------ SAT Options
% 2.10/1.00  
% 2.10/1.00  --sat_mode                              false
% 2.10/1.00  --sat_fm_restart_options                ""
% 2.10/1.00  --sat_gr_def                            false
% 2.10/1.00  --sat_epr_types                         true
% 2.10/1.00  --sat_non_cyclic_types                  false
% 2.10/1.00  --sat_finite_models                     false
% 2.10/1.00  --sat_fm_lemmas                         false
% 2.10/1.00  --sat_fm_prep                           false
% 2.10/1.00  --sat_fm_uc_incr                        true
% 2.10/1.00  --sat_out_model                         small
% 2.10/1.00  --sat_out_clauses                       false
% 2.10/1.00  
% 2.10/1.00  ------ QBF Options
% 2.10/1.00  
% 2.10/1.00  --qbf_mode                              false
% 2.10/1.00  --qbf_elim_univ                         false
% 2.10/1.00  --qbf_dom_inst                          none
% 2.10/1.00  --qbf_dom_pre_inst                      false
% 2.10/1.00  --qbf_sk_in                             false
% 2.10/1.00  --qbf_pred_elim                         true
% 2.10/1.00  --qbf_split                             512
% 2.10/1.00  
% 2.10/1.00  ------ BMC1 Options
% 2.10/1.00  
% 2.10/1.00  --bmc1_incremental                      false
% 2.10/1.00  --bmc1_axioms                           reachable_all
% 2.10/1.00  --bmc1_min_bound                        0
% 2.10/1.00  --bmc1_max_bound                        -1
% 2.10/1.00  --bmc1_max_bound_default                -1
% 2.10/1.00  --bmc1_symbol_reachability              true
% 2.10/1.00  --bmc1_property_lemmas                  false
% 2.10/1.00  --bmc1_k_induction                      false
% 2.10/1.00  --bmc1_non_equiv_states                 false
% 2.10/1.00  --bmc1_deadlock                         false
% 2.10/1.00  --bmc1_ucm                              false
% 2.10/1.00  --bmc1_add_unsat_core                   none
% 2.10/1.00  --bmc1_unsat_core_children              false
% 2.10/1.00  --bmc1_unsat_core_extrapolate_axioms    false
% 2.10/1.00  --bmc1_out_stat                         full
% 2.10/1.00  --bmc1_ground_init                      false
% 2.10/1.00  --bmc1_pre_inst_next_state              false
% 2.10/1.00  --bmc1_pre_inst_state                   false
% 2.10/1.00  --bmc1_pre_inst_reach_state             false
% 2.10/1.00  --bmc1_out_unsat_core                   false
% 2.10/1.00  --bmc1_aig_witness_out                  false
% 2.10/1.00  --bmc1_verbose                          false
% 2.10/1.00  --bmc1_dump_clauses_tptp                false
% 2.10/1.00  --bmc1_dump_unsat_core_tptp             false
% 2.10/1.00  --bmc1_dump_file                        -
% 2.10/1.00  --bmc1_ucm_expand_uc_limit              128
% 2.10/1.00  --bmc1_ucm_n_expand_iterations          6
% 2.10/1.00  --bmc1_ucm_extend_mode                  1
% 2.10/1.00  --bmc1_ucm_init_mode                    2
% 2.10/1.00  --bmc1_ucm_cone_mode                    none
% 2.10/1.00  --bmc1_ucm_reduced_relation_type        0
% 2.10/1.00  --bmc1_ucm_relax_model                  4
% 2.10/1.00  --bmc1_ucm_full_tr_after_sat            true
% 2.10/1.00  --bmc1_ucm_expand_neg_assumptions       false
% 2.10/1.00  --bmc1_ucm_layered_model                none
% 2.10/1.00  --bmc1_ucm_max_lemma_size               10
% 2.10/1.00  
% 2.10/1.00  ------ AIG Options
% 2.10/1.00  
% 2.10/1.00  --aig_mode                              false
% 2.10/1.00  
% 2.10/1.00  ------ Instantiation Options
% 2.10/1.00  
% 2.10/1.00  --instantiation_flag                    true
% 2.10/1.00  --inst_sos_flag                         false
% 2.10/1.00  --inst_sos_phase                        true
% 2.10/1.00  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 2.10/1.00  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 2.10/1.00  --inst_lit_sel_side                     num_symb
% 2.10/1.00  --inst_solver_per_active                1400
% 2.10/1.00  --inst_solver_calls_frac                1.
% 2.10/1.00  --inst_passive_queue_type               priority_queues
% 2.10/1.00  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 2.10/1.00  --inst_passive_queues_freq              [25;2]
% 2.10/1.00  --inst_dismatching                      true
% 2.10/1.00  --inst_eager_unprocessed_to_passive     true
% 2.10/1.00  --inst_prop_sim_given                   true
% 2.10/1.00  --inst_prop_sim_new                     false
% 2.10/1.00  --inst_subs_new                         false
% 2.10/1.00  --inst_eq_res_simp                      false
% 2.10/1.00  --inst_subs_given                       false
% 2.10/1.00  --inst_orphan_elimination               true
% 2.10/1.00  --inst_learning_loop_flag               true
% 2.10/1.00  --inst_learning_start                   3000
% 2.10/1.00  --inst_learning_factor                  2
% 2.10/1.00  --inst_start_prop_sim_after_learn       3
% 2.10/1.00  --inst_sel_renew                        solver
% 2.10/1.00  --inst_lit_activity_flag                true
% 2.10/1.00  --inst_restr_to_given                   false
% 2.10/1.00  --inst_activity_threshold               500
% 2.10/1.00  --inst_out_proof                        true
% 2.10/1.00  
% 2.10/1.00  ------ Resolution Options
% 2.10/1.00  
% 2.10/1.00  --resolution_flag                       true
% 2.10/1.00  --res_lit_sel                           adaptive
% 2.10/1.00  --res_lit_sel_side                      none
% 2.10/1.00  --res_ordering                          kbo
% 2.10/1.00  --res_to_prop_solver                    active
% 2.10/1.00  --res_prop_simpl_new                    false
% 2.10/1.00  --res_prop_simpl_given                  true
% 2.10/1.00  --res_passive_queue_type                priority_queues
% 2.10/1.00  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 2.10/1.00  --res_passive_queues_freq               [15;5]
% 2.10/1.00  --res_forward_subs                      full
% 2.10/1.00  --res_backward_subs                     full
% 2.10/1.00  --res_forward_subs_resolution           true
% 2.10/1.00  --res_backward_subs_resolution          true
% 2.10/1.00  --res_orphan_elimination                true
% 2.10/1.00  --res_time_limit                        2.
% 2.10/1.00  --res_out_proof                         true
% 2.10/1.00  
% 2.10/1.00  ------ Superposition Options
% 2.10/1.00  
% 2.10/1.00  --superposition_flag                    true
% 2.10/1.00  --sup_passive_queue_type                priority_queues
% 2.10/1.00  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 2.10/1.00  --sup_passive_queues_freq               [8;1;4]
% 2.10/1.00  --demod_completeness_check              fast
% 2.10/1.00  --demod_use_ground                      true
% 2.10/1.00  --sup_to_prop_solver                    passive
% 2.10/1.00  --sup_prop_simpl_new                    true
% 2.10/1.00  --sup_prop_simpl_given                  true
% 2.10/1.00  --sup_fun_splitting                     false
% 2.10/1.00  --sup_smt_interval                      50000
% 2.10/1.00  
% 2.10/1.00  ------ Superposition Simplification Setup
% 2.10/1.00  
% 2.10/1.00  --sup_indices_passive                   []
% 2.10/1.00  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.10/1.00  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.10/1.00  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.10/1.00  --sup_full_triv                         [TrivRules;PropSubs]
% 2.10/1.00  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.10/1.00  --sup_full_bw                           [BwDemod]
% 2.10/1.00  --sup_immed_triv                        [TrivRules]
% 2.10/1.00  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 2.10/1.00  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.10/1.00  --sup_immed_bw_main                     []
% 2.10/1.00  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.10/1.00  --sup_input_triv                        [Unflattening;TrivRules]
% 2.10/1.00  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.10/1.00  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.10/1.00  
% 2.10/1.00  ------ Combination Options
% 2.10/1.00  
% 2.10/1.00  --comb_res_mult                         3
% 2.10/1.00  --comb_sup_mult                         2
% 2.10/1.00  --comb_inst_mult                        10
% 2.10/1.00  
% 2.10/1.00  ------ Debug Options
% 2.10/1.00  
% 2.10/1.00  --dbg_backtrace                         false
% 2.10/1.00  --dbg_dump_prop_clauses                 false
% 2.10/1.00  --dbg_dump_prop_clauses_file            -
% 2.10/1.00  --dbg_out_stat                          false
% 2.10/1.00  ------ Parsing...
% 2.10/1.00  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 2.10/1.00  
% 2.10/1.00  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe:1:0s pe_e  sf_s  rm: 1 0s  sf_e  pe_s  pe_e 
% 2.10/1.00  
% 2.10/1.00  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 2.10/1.00  
% 2.10/1.00  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 2.10/1.00  ------ Proving...
% 2.10/1.00  ------ Problem Properties 
% 2.10/1.00  
% 2.10/1.00  
% 2.10/1.00  clauses                                 13
% 2.10/1.00  conjectures                             5
% 2.10/1.00  EPR                                     0
% 2.10/1.00  Horn                                    13
% 2.10/1.00  unary                                   6
% 2.10/1.00  binary                                  2
% 2.10/1.00  lits                                    26
% 2.10/1.00  lits eq                                 7
% 2.10/1.00  fd_pure                                 0
% 2.10/1.00  fd_pseudo                               0
% 2.10/1.00  fd_cond                                 0
% 2.10/1.00  fd_pseudo_cond                          0
% 2.10/1.00  AC symbols                              0
% 2.10/1.00  
% 2.10/1.00  ------ Schedule dynamic 5 is on 
% 2.10/1.00  
% 2.10/1.00  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" Time Limit: 10.
% 2.10/1.00  
% 2.10/1.00  
% 2.10/1.00  ------ 
% 2.10/1.00  Current options:
% 2.10/1.00  ------ 
% 2.10/1.00  
% 2.10/1.00  ------ Input Options
% 2.10/1.00  
% 2.10/1.00  --out_options                           all
% 2.10/1.00  --tptp_safe_out                         true
% 2.10/1.00  --problem_path                          ""
% 2.10/1.00  --include_path                          ""
% 2.10/1.00  --clausifier                            res/vclausify_rel
% 2.10/1.00  --clausifier_options                    --mode clausify
% 2.10/1.00  --stdin                                 false
% 2.10/1.00  --stats_out                             all
% 2.10/1.00  
% 2.10/1.00  ------ General Options
% 2.10/1.00  
% 2.10/1.00  --fof                                   false
% 2.10/1.00  --time_out_real                         305.
% 2.10/1.00  --time_out_virtual                      -1.
% 2.10/1.00  --symbol_type_check                     false
% 2.10/1.00  --clausify_out                          false
% 2.10/1.00  --sig_cnt_out                           false
% 2.10/1.00  --trig_cnt_out                          false
% 2.10/1.00  --trig_cnt_out_tolerance                1.
% 2.10/1.00  --trig_cnt_out_sk_spl                   false
% 2.10/1.00  --abstr_cl_out                          false
% 2.10/1.00  
% 2.10/1.00  ------ Global Options
% 2.10/1.00  
% 2.10/1.00  --schedule                              default
% 2.10/1.00  --add_important_lit                     false
% 2.10/1.00  --prop_solver_per_cl                    1000
% 2.10/1.00  --min_unsat_core                        false
% 2.10/1.00  --soft_assumptions                      false
% 2.10/1.00  --soft_lemma_size                       3
% 2.10/1.00  --prop_impl_unit_size                   0
% 2.10/1.00  --prop_impl_unit                        []
% 2.10/1.00  --share_sel_clauses                     true
% 2.10/1.00  --reset_solvers                         false
% 2.10/1.00  --bc_imp_inh                            [conj_cone]
% 2.10/1.00  --conj_cone_tolerance                   3.
% 2.10/1.00  --extra_neg_conj                        none
% 2.10/1.00  --large_theory_mode                     true
% 2.10/1.00  --prolific_symb_bound                   200
% 2.10/1.00  --lt_threshold                          2000
% 2.10/1.00  --clause_weak_htbl                      true
% 2.10/1.00  --gc_record_bc_elim                     false
% 2.10/1.00  
% 2.10/1.00  ------ Preprocessing Options
% 2.10/1.00  
% 2.10/1.00  --preprocessing_flag                    true
% 2.10/1.00  --time_out_prep_mult                    0.1
% 2.10/1.00  --splitting_mode                        input
% 2.10/1.00  --splitting_grd                         true
% 2.10/1.00  --splitting_cvd                         false
% 2.10/1.00  --splitting_cvd_svl                     false
% 2.10/1.00  --splitting_nvd                         32
% 2.10/1.00  --sub_typing                            true
% 2.10/1.00  --prep_gs_sim                           true
% 2.10/1.00  --prep_unflatten                        true
% 2.10/1.00  --prep_res_sim                          true
% 2.10/1.00  --prep_upred                            true
% 2.10/1.00  --prep_sem_filter                       exhaustive
% 2.10/1.00  --prep_sem_filter_out                   false
% 2.10/1.00  --pred_elim                             true
% 2.10/1.00  --res_sim_input                         true
% 2.10/1.00  --eq_ax_congr_red                       true
% 2.10/1.00  --pure_diseq_elim                       true
% 2.10/1.00  --brand_transform                       false
% 2.10/1.00  --non_eq_to_eq                          false
% 2.10/1.00  --prep_def_merge                        true
% 2.10/1.00  --prep_def_merge_prop_impl              false
% 2.10/1.00  --prep_def_merge_mbd                    true
% 2.10/1.00  --prep_def_merge_tr_red                 false
% 2.10/1.00  --prep_def_merge_tr_cl                  false
% 2.10/1.00  --smt_preprocessing                     true
% 2.10/1.00  --smt_ac_axioms                         fast
% 2.10/1.00  --preprocessed_out                      false
% 2.10/1.00  --preprocessed_stats                    false
% 2.10/1.00  
% 2.10/1.00  ------ Abstraction refinement Options
% 2.10/1.00  
% 2.10/1.00  --abstr_ref                             []
% 2.10/1.00  --abstr_ref_prep                        false
% 2.10/1.00  --abstr_ref_until_sat                   false
% 2.10/1.00  --abstr_ref_sig_restrict                funpre
% 2.10/1.00  --abstr_ref_af_restrict_to_split_sk     false
% 2.10/1.00  --abstr_ref_under                       []
% 2.10/1.00  
% 2.10/1.00  ------ SAT Options
% 2.10/1.00  
% 2.10/1.00  --sat_mode                              false
% 2.10/1.00  --sat_fm_restart_options                ""
% 2.10/1.00  --sat_gr_def                            false
% 2.10/1.00  --sat_epr_types                         true
% 2.10/1.00  --sat_non_cyclic_types                  false
% 2.10/1.00  --sat_finite_models                     false
% 2.10/1.00  --sat_fm_lemmas                         false
% 2.10/1.00  --sat_fm_prep                           false
% 2.10/1.00  --sat_fm_uc_incr                        true
% 2.10/1.00  --sat_out_model                         small
% 2.10/1.00  --sat_out_clauses                       false
% 2.10/1.00  
% 2.10/1.00  ------ QBF Options
% 2.10/1.00  
% 2.10/1.00  --qbf_mode                              false
% 2.10/1.00  --qbf_elim_univ                         false
% 2.10/1.00  --qbf_dom_inst                          none
% 2.10/1.00  --qbf_dom_pre_inst                      false
% 2.10/1.00  --qbf_sk_in                             false
% 2.10/1.00  --qbf_pred_elim                         true
% 2.10/1.00  --qbf_split                             512
% 2.10/1.00  
% 2.10/1.00  ------ BMC1 Options
% 2.10/1.00  
% 2.10/1.00  --bmc1_incremental                      false
% 2.10/1.00  --bmc1_axioms                           reachable_all
% 2.10/1.00  --bmc1_min_bound                        0
% 2.10/1.00  --bmc1_max_bound                        -1
% 2.10/1.00  --bmc1_max_bound_default                -1
% 2.10/1.00  --bmc1_symbol_reachability              true
% 2.10/1.00  --bmc1_property_lemmas                  false
% 2.10/1.00  --bmc1_k_induction                      false
% 2.10/1.00  --bmc1_non_equiv_states                 false
% 2.10/1.00  --bmc1_deadlock                         false
% 2.10/1.00  --bmc1_ucm                              false
% 2.10/1.00  --bmc1_add_unsat_core                   none
% 2.10/1.00  --bmc1_unsat_core_children              false
% 2.10/1.00  --bmc1_unsat_core_extrapolate_axioms    false
% 2.10/1.00  --bmc1_out_stat                         full
% 2.10/1.00  --bmc1_ground_init                      false
% 2.10/1.00  --bmc1_pre_inst_next_state              false
% 2.10/1.00  --bmc1_pre_inst_state                   false
% 2.10/1.00  --bmc1_pre_inst_reach_state             false
% 2.10/1.00  --bmc1_out_unsat_core                   false
% 2.10/1.00  --bmc1_aig_witness_out                  false
% 2.10/1.00  --bmc1_verbose                          false
% 2.10/1.00  --bmc1_dump_clauses_tptp                false
% 2.10/1.00  --bmc1_dump_unsat_core_tptp             false
% 2.10/1.00  --bmc1_dump_file                        -
% 2.10/1.00  --bmc1_ucm_expand_uc_limit              128
% 2.10/1.00  --bmc1_ucm_n_expand_iterations          6
% 2.10/1.00  --bmc1_ucm_extend_mode                  1
% 2.10/1.00  --bmc1_ucm_init_mode                    2
% 2.10/1.00  --bmc1_ucm_cone_mode                    none
% 2.10/1.00  --bmc1_ucm_reduced_relation_type        0
% 2.10/1.00  --bmc1_ucm_relax_model                  4
% 2.10/1.00  --bmc1_ucm_full_tr_after_sat            true
% 2.10/1.00  --bmc1_ucm_expand_neg_assumptions       false
% 2.10/1.00  --bmc1_ucm_layered_model                none
% 2.10/1.00  --bmc1_ucm_max_lemma_size               10
% 2.10/1.00  
% 2.10/1.00  ------ AIG Options
% 2.10/1.00  
% 2.10/1.00  --aig_mode                              false
% 2.10/1.00  
% 2.10/1.00  ------ Instantiation Options
% 2.10/1.00  
% 2.10/1.00  --instantiation_flag                    true
% 2.10/1.00  --inst_sos_flag                         false
% 2.10/1.00  --inst_sos_phase                        true
% 2.10/1.00  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 2.10/1.00  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 2.10/1.00  --inst_lit_sel_side                     none
% 2.10/1.00  --inst_solver_per_active                1400
% 2.10/1.00  --inst_solver_calls_frac                1.
% 2.10/1.00  --inst_passive_queue_type               priority_queues
% 2.10/1.00  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 2.10/1.00  --inst_passive_queues_freq              [25;2]
% 2.10/1.00  --inst_dismatching                      true
% 2.10/1.00  --inst_eager_unprocessed_to_passive     true
% 2.10/1.00  --inst_prop_sim_given                   true
% 2.10/1.00  --inst_prop_sim_new                     false
% 2.10/1.00  --inst_subs_new                         false
% 2.10/1.00  --inst_eq_res_simp                      false
% 2.10/1.00  --inst_subs_given                       false
% 2.10/1.00  --inst_orphan_elimination               true
% 2.10/1.00  --inst_learning_loop_flag               true
% 2.10/1.00  --inst_learning_start                   3000
% 2.10/1.00  --inst_learning_factor                  2
% 2.10/1.00  --inst_start_prop_sim_after_learn       3
% 2.10/1.00  --inst_sel_renew                        solver
% 2.10/1.00  --inst_lit_activity_flag                true
% 2.10/1.00  --inst_restr_to_given                   false
% 2.10/1.00  --inst_activity_threshold               500
% 2.10/1.00  --inst_out_proof                        true
% 2.10/1.00  
% 2.10/1.00  ------ Resolution Options
% 2.10/1.00  
% 2.10/1.00  --resolution_flag                       false
% 2.10/1.00  --res_lit_sel                           adaptive
% 2.10/1.00  --res_lit_sel_side                      none
% 2.10/1.00  --res_ordering                          kbo
% 2.10/1.00  --res_to_prop_solver                    active
% 2.10/1.00  --res_prop_simpl_new                    false
% 2.10/1.00  --res_prop_simpl_given                  true
% 2.10/1.00  --res_passive_queue_type                priority_queues
% 2.10/1.00  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 2.10/1.00  --res_passive_queues_freq               [15;5]
% 2.10/1.00  --res_forward_subs                      full
% 2.10/1.00  --res_backward_subs                     full
% 2.10/1.00  --res_forward_subs_resolution           true
% 2.10/1.00  --res_backward_subs_resolution          true
% 2.10/1.00  --res_orphan_elimination                true
% 2.10/1.00  --res_time_limit                        2.
% 2.10/1.00  --res_out_proof                         true
% 2.10/1.00  
% 2.10/1.00  ------ Superposition Options
% 2.10/1.00  
% 2.10/1.00  --superposition_flag                    true
% 2.10/1.00  --sup_passive_queue_type                priority_queues
% 2.10/1.00  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 2.10/1.00  --sup_passive_queues_freq               [8;1;4]
% 2.10/1.00  --demod_completeness_check              fast
% 2.10/1.00  --demod_use_ground                      true
% 2.10/1.00  --sup_to_prop_solver                    passive
% 2.10/1.00  --sup_prop_simpl_new                    true
% 2.10/1.00  --sup_prop_simpl_given                  true
% 2.10/1.00  --sup_fun_splitting                     false
% 2.10/1.00  --sup_smt_interval                      50000
% 2.10/1.00  
% 2.10/1.00  ------ Superposition Simplification Setup
% 2.10/1.00  
% 2.10/1.00  --sup_indices_passive                   []
% 2.10/1.00  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.10/1.00  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.10/1.00  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.10/1.00  --sup_full_triv                         [TrivRules;PropSubs]
% 2.10/1.00  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.10/1.00  --sup_full_bw                           [BwDemod]
% 2.10/1.00  --sup_immed_triv                        [TrivRules]
% 2.10/1.00  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 2.10/1.00  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.10/1.00  --sup_immed_bw_main                     []
% 2.10/1.00  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.10/1.00  --sup_input_triv                        [Unflattening;TrivRules]
% 2.10/1.00  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.10/1.00  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.10/1.00  
% 2.10/1.00  ------ Combination Options
% 2.10/1.00  
% 2.10/1.00  --comb_res_mult                         3
% 2.10/1.00  --comb_sup_mult                         2
% 2.10/1.00  --comb_inst_mult                        10
% 2.10/1.00  
% 2.10/1.00  ------ Debug Options
% 2.10/1.00  
% 2.10/1.00  --dbg_backtrace                         false
% 2.10/1.00  --dbg_dump_prop_clauses                 false
% 2.10/1.00  --dbg_dump_prop_clauses_file            -
% 2.10/1.00  --dbg_out_stat                          false
% 2.10/1.00  
% 2.10/1.00  
% 2.10/1.00  
% 2.10/1.00  
% 2.10/1.00  ------ Proving...
% 2.10/1.00  
% 2.10/1.00  
% 2.10/1.00  % SZS status Theorem for theBenchmark.p
% 2.10/1.00  
% 2.10/1.00  % SZS output start CNFRefutation for theBenchmark.p
% 2.10/1.00  
% 2.10/1.00  fof(f10,conjecture,(
% 2.10/1.00    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) => ((k2_relset_1(X0,X0,X2) = X0 & k2_relset_1(X0,X0,X1) = X0) => k2_relset_1(X0,X0,k4_relset_1(X0,X0,X0,X0,X2,X1)) = X0)))),
% 2.10/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.10/1.00  
% 2.10/1.00  fof(f11,negated_conjecture,(
% 2.10/1.00    ~! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) => ((k2_relset_1(X0,X0,X2) = X0 & k2_relset_1(X0,X0,X1) = X0) => k2_relset_1(X0,X0,k4_relset_1(X0,X0,X0,X0,X2,X1)) = X0)))),
% 2.10/1.00    inference(negated_conjecture,[],[f10])).
% 2.10/1.00  
% 2.10/1.00  fof(f25,plain,(
% 2.10/1.00    ? [X0,X1] : (? [X2] : ((k2_relset_1(X0,X0,k4_relset_1(X0,X0,X0,X0,X2,X1)) != X0 & (k2_relset_1(X0,X0,X2) = X0 & k2_relset_1(X0,X0,X1) = X0)) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))) & m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))))),
% 2.10/1.00    inference(ennf_transformation,[],[f11])).
% 2.10/1.00  
% 2.10/1.00  fof(f26,plain,(
% 2.10/1.00    ? [X0,X1] : (? [X2] : (k2_relset_1(X0,X0,k4_relset_1(X0,X0,X0,X0,X2,X1)) != X0 & k2_relset_1(X0,X0,X2) = X0 & k2_relset_1(X0,X0,X1) = X0 & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))) & m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))))),
% 2.10/1.00    inference(flattening,[],[f25])).
% 2.10/1.00  
% 2.10/1.00  fof(f28,plain,(
% 2.10/1.00    ( ! [X0,X1] : (? [X2] : (k2_relset_1(X0,X0,k4_relset_1(X0,X0,X0,X0,X2,X1)) != X0 & k2_relset_1(X0,X0,X2) = X0 & k2_relset_1(X0,X0,X1) = X0 & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))) => (k2_relset_1(X0,X0,k4_relset_1(X0,X0,X0,X0,sK2,X1)) != X0 & k2_relset_1(X0,X0,sK2) = X0 & k2_relset_1(X0,X0,X1) = X0 & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X0,X0))))) )),
% 2.10/1.00    introduced(choice_axiom,[])).
% 2.10/1.00  
% 2.10/1.00  fof(f27,plain,(
% 2.10/1.00    ? [X0,X1] : (? [X2] : (k2_relset_1(X0,X0,k4_relset_1(X0,X0,X0,X0,X2,X1)) != X0 & k2_relset_1(X0,X0,X2) = X0 & k2_relset_1(X0,X0,X1) = X0 & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))) & m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))) => (? [X2] : (k2_relset_1(sK0,sK0,k4_relset_1(sK0,sK0,sK0,sK0,X2,sK1)) != sK0 & k2_relset_1(sK0,sK0,X2) = sK0 & k2_relset_1(sK0,sK0,sK1) = sK0 & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))) & m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))))),
% 2.10/1.00    introduced(choice_axiom,[])).
% 2.10/1.00  
% 2.10/1.00  fof(f29,plain,(
% 2.10/1.00    (k2_relset_1(sK0,sK0,k4_relset_1(sK0,sK0,sK0,sK0,sK2,sK1)) != sK0 & k2_relset_1(sK0,sK0,sK2) = sK0 & k2_relset_1(sK0,sK0,sK1) = sK0 & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))) & m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))),
% 2.10/1.00    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f26,f28,f27])).
% 2.10/1.00  
% 2.10/1.00  fof(f39,plain,(
% 2.10/1.00    m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))),
% 2.10/1.00    inference(cnf_transformation,[],[f29])).
% 2.10/1.00  
% 2.10/1.00  fof(f6,axiom,(
% 2.10/1.00    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => (v5_relat_1(X2,X1) & v4_relat_1(X2,X0)))),
% 2.10/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.10/1.00  
% 2.10/1.00  fof(f12,plain,(
% 2.10/1.00    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => v4_relat_1(X2,X0))),
% 2.10/1.00    inference(pure_predicate_removal,[],[f6])).
% 2.10/1.00  
% 2.10/1.00  fof(f19,plain,(
% 2.10/1.00    ! [X0,X1,X2] : (v4_relat_1(X2,X0) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 2.10/1.00    inference(ennf_transformation,[],[f12])).
% 2.10/1.00  
% 2.10/1.00  fof(f35,plain,(
% 2.10/1.00    ( ! [X2,X0,X1] : (v4_relat_1(X2,X0) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 2.10/1.00    inference(cnf_transformation,[],[f19])).
% 2.10/1.00  
% 2.10/1.00  fof(f3,axiom,(
% 2.10/1.00    ! [X0,X1] : ((v4_relat_1(X1,X0) & v1_relat_1(X1)) => k7_relat_1(X1,X0) = X1)),
% 2.10/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.10/1.00  
% 2.10/1.00  fof(f14,plain,(
% 2.10/1.00    ! [X0,X1] : (k7_relat_1(X1,X0) = X1 | (~v4_relat_1(X1,X0) | ~v1_relat_1(X1)))),
% 2.10/1.00    inference(ennf_transformation,[],[f3])).
% 2.10/1.00  
% 2.10/1.00  fof(f15,plain,(
% 2.10/1.00    ! [X0,X1] : (k7_relat_1(X1,X0) = X1 | ~v4_relat_1(X1,X0) | ~v1_relat_1(X1))),
% 2.10/1.00    inference(flattening,[],[f14])).
% 2.10/1.00  
% 2.10/1.00  fof(f32,plain,(
% 2.10/1.00    ( ! [X0,X1] : (k7_relat_1(X1,X0) = X1 | ~v4_relat_1(X1,X0) | ~v1_relat_1(X1)) )),
% 2.10/1.00    inference(cnf_transformation,[],[f15])).
% 2.10/1.00  
% 2.10/1.00  fof(f2,axiom,(
% 2.10/1.00    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1))),
% 2.10/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.10/1.00  
% 2.10/1.00  fof(f31,plain,(
% 2.10/1.00    ( ! [X0,X1] : (v1_relat_1(k2_zfmisc_1(X0,X1))) )),
% 2.10/1.00    inference(cnf_transformation,[],[f2])).
% 2.10/1.00  
% 2.10/1.00  fof(f1,axiom,(
% 2.10/1.00    ! [X0] : (v1_relat_1(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => v1_relat_1(X1)))),
% 2.10/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.10/1.00  
% 2.10/1.00  fof(f13,plain,(
% 2.10/1.00    ! [X0] : (! [X1] : (v1_relat_1(X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) | ~v1_relat_1(X0))),
% 2.10/1.00    inference(ennf_transformation,[],[f1])).
% 2.10/1.00  
% 2.10/1.00  fof(f30,plain,(
% 2.10/1.00    ( ! [X0,X1] : (v1_relat_1(X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0)) | ~v1_relat_1(X0)) )),
% 2.10/1.00    inference(cnf_transformation,[],[f13])).
% 2.10/1.00  
% 2.10/1.00  fof(f5,axiom,(
% 2.10/1.00    ! [X0,X1] : (v1_relat_1(X1) => r1_tarski(k1_relat_1(k7_relat_1(X1,X0)),X0))),
% 2.10/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.10/1.00  
% 2.10/1.00  fof(f18,plain,(
% 2.10/1.00    ! [X0,X1] : (r1_tarski(k1_relat_1(k7_relat_1(X1,X0)),X0) | ~v1_relat_1(X1))),
% 2.10/1.00    inference(ennf_transformation,[],[f5])).
% 2.10/1.00  
% 2.10/1.00  fof(f34,plain,(
% 2.10/1.00    ( ! [X0,X1] : (r1_tarski(k1_relat_1(k7_relat_1(X1,X0)),X0) | ~v1_relat_1(X1)) )),
% 2.10/1.00    inference(cnf_transformation,[],[f18])).
% 2.10/1.00  
% 2.10/1.00  fof(f40,plain,(
% 2.10/1.00    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))),
% 2.10/1.00    inference(cnf_transformation,[],[f29])).
% 2.10/1.00  
% 2.10/1.00  fof(f8,axiom,(
% 2.10/1.00    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k2_relat_1(X2) = k2_relset_1(X0,X1,X2))),
% 2.10/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.10/1.00  
% 2.10/1.00  fof(f22,plain,(
% 2.10/1.00    ! [X0,X1,X2] : (k2_relat_1(X2) = k2_relset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 2.10/1.00    inference(ennf_transformation,[],[f8])).
% 2.10/1.00  
% 2.10/1.00  fof(f37,plain,(
% 2.10/1.00    ( ! [X2,X0,X1] : (k2_relat_1(X2) = k2_relset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 2.10/1.00    inference(cnf_transformation,[],[f22])).
% 2.10/1.00  
% 2.10/1.00  fof(f42,plain,(
% 2.10/1.00    k2_relset_1(sK0,sK0,sK2) = sK0),
% 2.10/1.00    inference(cnf_transformation,[],[f29])).
% 2.10/1.00  
% 2.10/1.00  fof(f4,axiom,(
% 2.10/1.00    ! [X0] : (v1_relat_1(X0) => ! [X1] : (v1_relat_1(X1) => (r1_tarski(k1_relat_1(X0),k2_relat_1(X1)) => k2_relat_1(X0) = k2_relat_1(k5_relat_1(X1,X0)))))),
% 2.10/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.10/1.00  
% 2.10/1.00  fof(f16,plain,(
% 2.10/1.00    ! [X0] : (! [X1] : ((k2_relat_1(X0) = k2_relat_1(k5_relat_1(X1,X0)) | ~r1_tarski(k1_relat_1(X0),k2_relat_1(X1))) | ~v1_relat_1(X1)) | ~v1_relat_1(X0))),
% 2.10/1.01    inference(ennf_transformation,[],[f4])).
% 2.10/1.01  
% 2.10/1.01  fof(f17,plain,(
% 2.10/1.01    ! [X0] : (! [X1] : (k2_relat_1(X0) = k2_relat_1(k5_relat_1(X1,X0)) | ~r1_tarski(k1_relat_1(X0),k2_relat_1(X1)) | ~v1_relat_1(X1)) | ~v1_relat_1(X0))),
% 2.10/1.01    inference(flattening,[],[f16])).
% 2.10/1.01  
% 2.10/1.01  fof(f33,plain,(
% 2.10/1.01    ( ! [X0,X1] : (k2_relat_1(X0) = k2_relat_1(k5_relat_1(X1,X0)) | ~r1_tarski(k1_relat_1(X0),k2_relat_1(X1)) | ~v1_relat_1(X1) | ~v1_relat_1(X0)) )),
% 2.10/1.01    inference(cnf_transformation,[],[f17])).
% 2.10/1.01  
% 2.10/1.01  fof(f41,plain,(
% 2.10/1.01    k2_relset_1(sK0,sK0,sK1) = sK0),
% 2.10/1.01    inference(cnf_transformation,[],[f29])).
% 2.10/1.01  
% 2.10/1.01  fof(f9,axiom,(
% 2.10/1.01    ! [X0,X1,X2,X3,X4,X5] : ((m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) => k5_relat_1(X4,X5) = k4_relset_1(X0,X1,X2,X3,X4,X5))),
% 2.10/1.01    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.10/1.01  
% 2.10/1.01  fof(f23,plain,(
% 2.10/1.01    ! [X0,X1,X2,X3,X4,X5] : (k5_relat_1(X4,X5) = k4_relset_1(X0,X1,X2,X3,X4,X5) | (~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))))),
% 2.10/1.01    inference(ennf_transformation,[],[f9])).
% 2.10/1.01  
% 2.10/1.01  fof(f24,plain,(
% 2.10/1.01    ! [X0,X1,X2,X3,X4,X5] : (k5_relat_1(X4,X5) = k4_relset_1(X0,X1,X2,X3,X4,X5) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 2.10/1.01    inference(flattening,[],[f23])).
% 2.10/1.01  
% 2.10/1.01  fof(f38,plain,(
% 2.10/1.01    ( ! [X4,X2,X0,X5,X3,X1] : (k5_relat_1(X4,X5) = k4_relset_1(X0,X1,X2,X3,X4,X5) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 2.10/1.01    inference(cnf_transformation,[],[f24])).
% 2.10/1.01  
% 2.10/1.01  fof(f7,axiom,(
% 2.10/1.01    ! [X0,X1,X2,X3,X4,X5] : ((m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) => m1_subset_1(k4_relset_1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3))))),
% 2.10/1.01    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.10/1.01  
% 2.10/1.01  fof(f20,plain,(
% 2.10/1.01    ! [X0,X1,X2,X3,X4,X5] : (m1_subset_1(k4_relset_1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3))) | (~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))))),
% 2.10/1.01    inference(ennf_transformation,[],[f7])).
% 2.10/1.01  
% 2.10/1.01  fof(f21,plain,(
% 2.10/1.01    ! [X0,X1,X2,X3,X4,X5] : (m1_subset_1(k4_relset_1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3))) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 2.10/1.01    inference(flattening,[],[f20])).
% 2.10/1.01  
% 2.10/1.01  fof(f36,plain,(
% 2.10/1.01    ( ! [X4,X2,X0,X5,X3,X1] : (m1_subset_1(k4_relset_1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3))) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 2.10/1.01    inference(cnf_transformation,[],[f21])).
% 2.10/1.01  
% 2.10/1.01  fof(f43,plain,(
% 2.10/1.01    k2_relset_1(sK0,sK0,k4_relset_1(sK0,sK0,sK0,sK0,sK2,sK1)) != sK0),
% 2.10/1.01    inference(cnf_transformation,[],[f29])).
% 2.10/1.01  
% 2.10/1.01  cnf(c_13,negated_conjecture,
% 2.10/1.01      ( m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) ),
% 2.10/1.01      inference(cnf_transformation,[],[f39]) ).
% 2.10/1.01  
% 2.10/1.01  cnf(c_276,negated_conjecture,
% 2.10/1.01      ( m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) ),
% 2.10/1.01      inference(subtyping,[status(esa)],[c_13]) ).
% 2.10/1.01  
% 2.10/1.01  cnf(c_521,plain,
% 2.10/1.01      ( m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) = iProver_top ),
% 2.10/1.01      inference(predicate_to_equality,[status(thm)],[c_276]) ).
% 2.10/1.01  
% 2.10/1.01  cnf(c_5,plain,
% 2.10/1.01      ( v4_relat_1(X0,X1)
% 2.10/1.01      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) ),
% 2.10/1.01      inference(cnf_transformation,[],[f35]) ).
% 2.10/1.01  
% 2.10/1.01  cnf(c_2,plain,
% 2.10/1.01      ( ~ v4_relat_1(X0,X1) | ~ v1_relat_1(X0) | k7_relat_1(X0,X1) = X0 ),
% 2.10/1.01      inference(cnf_transformation,[],[f32]) ).
% 2.10/1.01  
% 2.10/1.01  cnf(c_133,plain,
% 2.10/1.01      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 2.10/1.01      | ~ v1_relat_1(X0)
% 2.10/1.01      | k7_relat_1(X0,X1) = X0 ),
% 2.10/1.01      inference(resolution,[status(thm)],[c_5,c_2]) ).
% 2.10/1.01  
% 2.10/1.01  cnf(c_275,plain,
% 2.10/1.01      ( ~ m1_subset_1(X0_43,k1_zfmisc_1(k2_zfmisc_1(X0_45,X1_45)))
% 2.10/1.01      | ~ v1_relat_1(X0_43)
% 2.10/1.01      | k7_relat_1(X0_43,X0_45) = X0_43 ),
% 2.10/1.01      inference(subtyping,[status(esa)],[c_133]) ).
% 2.10/1.01  
% 2.10/1.01  cnf(c_522,plain,
% 2.10/1.01      ( k7_relat_1(X0_43,X0_45) = X0_43
% 2.10/1.01      | m1_subset_1(X0_43,k1_zfmisc_1(k2_zfmisc_1(X0_45,X1_45))) != iProver_top
% 2.10/1.01      | v1_relat_1(X0_43) != iProver_top ),
% 2.10/1.01      inference(predicate_to_equality,[status(thm)],[c_275]) ).
% 2.10/1.01  
% 2.10/1.01  cnf(c_1,plain,
% 2.10/1.01      ( v1_relat_1(k2_zfmisc_1(X0,X1)) ),
% 2.10/1.01      inference(cnf_transformation,[],[f31]) ).
% 2.10/1.01  
% 2.10/1.01  cnf(c_286,plain,
% 2.10/1.01      ( v1_relat_1(k2_zfmisc_1(X0_45,X1_45)) ),
% 2.10/1.01      inference(subtyping,[status(esa)],[c_1]) ).
% 2.10/1.01  
% 2.10/1.01  cnf(c_319,plain,
% 2.10/1.01      ( v1_relat_1(k2_zfmisc_1(X0_45,X1_45)) = iProver_top ),
% 2.10/1.01      inference(predicate_to_equality,[status(thm)],[c_286]) ).
% 2.10/1.01  
% 2.10/1.01  cnf(c_337,plain,
% 2.10/1.01      ( k7_relat_1(X0_43,X0_45) = X0_43
% 2.10/1.01      | m1_subset_1(X0_43,k1_zfmisc_1(k2_zfmisc_1(X0_45,X1_45))) != iProver_top
% 2.10/1.01      | v1_relat_1(X0_43) != iProver_top ),
% 2.10/1.01      inference(predicate_to_equality,[status(thm)],[c_275]) ).
% 2.10/1.01  
% 2.10/1.01  cnf(c_0,plain,
% 2.10/1.01      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
% 2.10/1.01      | ~ v1_relat_1(X1)
% 2.10/1.01      | v1_relat_1(X0) ),
% 2.10/1.01      inference(cnf_transformation,[],[f30]) ).
% 2.10/1.01  
% 2.10/1.01  cnf(c_287,plain,
% 2.10/1.01      ( ~ m1_subset_1(X0_43,k1_zfmisc_1(X1_43))
% 2.10/1.01      | ~ v1_relat_1(X1_43)
% 2.10/1.01      | v1_relat_1(X0_43) ),
% 2.10/1.01      inference(subtyping,[status(esa)],[c_0]) ).
% 2.10/1.01  
% 2.10/1.01  cnf(c_600,plain,
% 2.10/1.01      ( ~ m1_subset_1(X0_43,k1_zfmisc_1(k2_zfmisc_1(X0_45,X1_45)))
% 2.10/1.01      | v1_relat_1(X0_43)
% 2.10/1.01      | ~ v1_relat_1(k2_zfmisc_1(X0_45,X1_45)) ),
% 2.10/1.01      inference(instantiation,[status(thm)],[c_287]) ).
% 2.10/1.01  
% 2.10/1.01  cnf(c_601,plain,
% 2.10/1.01      ( m1_subset_1(X0_43,k1_zfmisc_1(k2_zfmisc_1(X0_45,X1_45))) != iProver_top
% 2.10/1.01      | v1_relat_1(X0_43) = iProver_top
% 2.10/1.01      | v1_relat_1(k2_zfmisc_1(X0_45,X1_45)) != iProver_top ),
% 2.10/1.01      inference(predicate_to_equality,[status(thm)],[c_600]) ).
% 2.10/1.01  
% 2.10/1.01  cnf(c_1878,plain,
% 2.10/1.01      ( m1_subset_1(X0_43,k1_zfmisc_1(k2_zfmisc_1(X0_45,X1_45))) != iProver_top
% 2.10/1.01      | k7_relat_1(X0_43,X0_45) = X0_43 ),
% 2.10/1.01      inference(global_propositional_subsumption,
% 2.10/1.01                [status(thm)],
% 2.10/1.01                [c_522,c_319,c_337,c_601]) ).
% 2.10/1.01  
% 2.10/1.01  cnf(c_1879,plain,
% 2.10/1.01      ( k7_relat_1(X0_43,X0_45) = X0_43
% 2.10/1.01      | m1_subset_1(X0_43,k1_zfmisc_1(k2_zfmisc_1(X0_45,X1_45))) != iProver_top ),
% 2.10/1.01      inference(renaming,[status(thm)],[c_1878]) ).
% 2.10/1.01  
% 2.10/1.01  cnf(c_1887,plain,
% 2.10/1.01      ( k7_relat_1(sK1,sK0) = sK1 ),
% 2.10/1.01      inference(superposition,[status(thm)],[c_521,c_1879]) ).
% 2.10/1.01  
% 2.10/1.01  cnf(c_4,plain,
% 2.10/1.01      ( r1_tarski(k1_relat_1(k7_relat_1(X0,X1)),X1) | ~ v1_relat_1(X0) ),
% 2.10/1.01      inference(cnf_transformation,[],[f34]) ).
% 2.10/1.01  
% 2.10/1.01  cnf(c_284,plain,
% 2.10/1.01      ( r1_tarski(k1_relat_1(k7_relat_1(X0_43,X0_45)),X0_45)
% 2.10/1.01      | ~ v1_relat_1(X0_43) ),
% 2.10/1.01      inference(subtyping,[status(esa)],[c_4]) ).
% 2.10/1.01  
% 2.10/1.01  cnf(c_516,plain,
% 2.10/1.01      ( r1_tarski(k1_relat_1(k7_relat_1(X0_43,X0_45)),X0_45) = iProver_top
% 2.10/1.01      | v1_relat_1(X0_43) != iProver_top ),
% 2.10/1.01      inference(predicate_to_equality,[status(thm)],[c_284]) ).
% 2.10/1.01  
% 2.10/1.01  cnf(c_2055,plain,
% 2.10/1.01      ( r1_tarski(k1_relat_1(sK1),sK0) = iProver_top
% 2.10/1.01      | v1_relat_1(sK1) != iProver_top ),
% 2.10/1.01      inference(superposition,[status(thm)],[c_1887,c_516]) ).
% 2.10/1.01  
% 2.10/1.01  cnf(c_14,plain,
% 2.10/1.01      ( m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) = iProver_top ),
% 2.10/1.01      inference(predicate_to_equality,[status(thm)],[c_13]) ).
% 2.10/1.01  
% 2.10/1.01  cnf(c_38,plain,
% 2.10/1.01      ( v1_relat_1(k2_zfmisc_1(sK0,sK0)) ),
% 2.10/1.01      inference(instantiation,[status(thm)],[c_1]) ).
% 2.10/1.01  
% 2.10/1.01  cnf(c_37,plain,
% 2.10/1.01      ( v1_relat_1(k2_zfmisc_1(X0,X1)) = iProver_top ),
% 2.10/1.01      inference(predicate_to_equality,[status(thm)],[c_1]) ).
% 2.10/1.01  
% 2.10/1.01  cnf(c_39,plain,
% 2.10/1.01      ( v1_relat_1(k2_zfmisc_1(sK0,sK0)) = iProver_top ),
% 2.10/1.01      inference(instantiation,[status(thm)],[c_37]) ).
% 2.10/1.01  
% 2.10/1.01  cnf(c_289,plain,( X0_43 = X0_43 ),theory(equality) ).
% 2.10/1.01  
% 2.10/1.01  cnf(c_314,plain,
% 2.10/1.01      ( sK1 = sK1 ),
% 2.10/1.01      inference(instantiation,[status(thm)],[c_289]) ).
% 2.10/1.01  
% 2.10/1.01  cnf(c_291,plain,( X0_45 = X0_45 ),theory(equality) ).
% 2.10/1.01  
% 2.10/1.01  cnf(c_316,plain,
% 2.10/1.01      ( sK0 = sK0 ),
% 2.10/1.01      inference(instantiation,[status(thm)],[c_291]) ).
% 2.10/1.01  
% 2.10/1.01  cnf(c_323,plain,
% 2.10/1.01      ( r1_tarski(k1_relat_1(k7_relat_1(X0_43,X0_45)),X0_45) = iProver_top
% 2.10/1.01      | v1_relat_1(X0_43) != iProver_top ),
% 2.10/1.01      inference(predicate_to_equality,[status(thm)],[c_284]) ).
% 2.10/1.01  
% 2.10/1.01  cnf(c_325,plain,
% 2.10/1.01      ( r1_tarski(k1_relat_1(k7_relat_1(sK1,sK0)),sK0) = iProver_top
% 2.10/1.01      | v1_relat_1(sK1) != iProver_top ),
% 2.10/1.01      inference(instantiation,[status(thm)],[c_323]) ).
% 2.10/1.01  
% 2.10/1.01  cnf(c_338,plain,
% 2.10/1.01      ( ~ m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
% 2.10/1.01      | ~ v1_relat_1(sK1)
% 2.10/1.01      | k7_relat_1(sK1,sK0) = sK1 ),
% 2.10/1.01      inference(instantiation,[status(thm)],[c_275]) ).
% 2.10/1.01  
% 2.10/1.01  cnf(c_602,plain,
% 2.10/1.01      ( ~ m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
% 2.10/1.01      | ~ v1_relat_1(k2_zfmisc_1(sK0,sK0))
% 2.10/1.01      | v1_relat_1(sK1) ),
% 2.10/1.01      inference(instantiation,[status(thm)],[c_600]) ).
% 2.10/1.01  
% 2.10/1.01  cnf(c_603,plain,
% 2.10/1.01      ( m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) != iProver_top
% 2.10/1.01      | v1_relat_1(k2_zfmisc_1(sK0,sK0)) != iProver_top
% 2.10/1.01      | v1_relat_1(sK1) = iProver_top ),
% 2.10/1.01      inference(instantiation,[status(thm)],[c_601]) ).
% 2.10/1.01  
% 2.10/1.01  cnf(c_301,plain,
% 2.10/1.01      ( ~ r1_tarski(X0_46,X0_45)
% 2.10/1.01      | r1_tarski(X1_46,X1_45)
% 2.10/1.01      | X1_46 != X0_46
% 2.10/1.01      | X1_45 != X0_45 ),
% 2.10/1.01      theory(equality) ).
% 2.10/1.01  
% 2.10/1.01  cnf(c_824,plain,
% 2.10/1.01      ( r1_tarski(X0_46,X0_45)
% 2.10/1.01      | ~ r1_tarski(k1_relat_1(k7_relat_1(X0_43,X1_45)),X1_45)
% 2.10/1.01      | X0_46 != k1_relat_1(k7_relat_1(X0_43,X1_45))
% 2.10/1.01      | X0_45 != X1_45 ),
% 2.10/1.01      inference(instantiation,[status(thm)],[c_301]) ).
% 2.10/1.01  
% 2.10/1.01  cnf(c_1041,plain,
% 2.10/1.01      ( r1_tarski(k1_relat_1(X0_43),X0_45)
% 2.10/1.01      | ~ r1_tarski(k1_relat_1(k7_relat_1(X1_43,X1_45)),X1_45)
% 2.10/1.01      | k1_relat_1(X0_43) != k1_relat_1(k7_relat_1(X1_43,X1_45))
% 2.10/1.01      | X0_45 != X1_45 ),
% 2.10/1.01      inference(instantiation,[status(thm)],[c_824]) ).
% 2.10/1.01  
% 2.10/1.01  cnf(c_1043,plain,
% 2.10/1.01      ( k1_relat_1(X0_43) != k1_relat_1(k7_relat_1(X1_43,X0_45))
% 2.10/1.01      | X1_45 != X0_45
% 2.10/1.01      | r1_tarski(k1_relat_1(X0_43),X1_45) = iProver_top
% 2.10/1.01      | r1_tarski(k1_relat_1(k7_relat_1(X1_43,X0_45)),X0_45) != iProver_top ),
% 2.10/1.01      inference(predicate_to_equality,[status(thm)],[c_1041]) ).
% 2.10/1.01  
% 2.10/1.01  cnf(c_1045,plain,
% 2.10/1.01      ( k1_relat_1(sK1) != k1_relat_1(k7_relat_1(sK1,sK0))
% 2.10/1.01      | sK0 != sK0
% 2.10/1.01      | r1_tarski(k1_relat_1(k7_relat_1(sK1,sK0)),sK0) != iProver_top
% 2.10/1.01      | r1_tarski(k1_relat_1(sK1),sK0) = iProver_top ),
% 2.10/1.01      inference(instantiation,[status(thm)],[c_1043]) ).
% 2.10/1.01  
% 2.10/1.01  cnf(c_300,plain,
% 2.10/1.01      ( k1_relat_1(X0_43) = k1_relat_1(X1_43) | X0_43 != X1_43 ),
% 2.10/1.01      theory(equality) ).
% 2.10/1.01  
% 2.10/1.01  cnf(c_1042,plain,
% 2.10/1.01      ( k1_relat_1(X0_43) = k1_relat_1(k7_relat_1(X1_43,X0_45))
% 2.10/1.01      | X0_43 != k7_relat_1(X1_43,X0_45) ),
% 2.10/1.01      inference(instantiation,[status(thm)],[c_300]) ).
% 2.10/1.01  
% 2.10/1.01  cnf(c_1047,plain,
% 2.10/1.01      ( k1_relat_1(sK1) = k1_relat_1(k7_relat_1(sK1,sK0))
% 2.10/1.01      | sK1 != k7_relat_1(sK1,sK0) ),
% 2.10/1.01      inference(instantiation,[status(thm)],[c_1042]) ).
% 2.10/1.01  
% 2.10/1.01  cnf(c_293,plain,
% 2.10/1.01      ( X0_43 != X1_43 | X2_43 != X1_43 | X2_43 = X0_43 ),
% 2.10/1.01      theory(equality) ).
% 2.10/1.01  
% 2.10/1.01  cnf(c_1359,plain,
% 2.10/1.01      ( X0_43 != X1_43
% 2.10/1.01      | X0_43 = k7_relat_1(X2_43,X0_45)
% 2.10/1.01      | k7_relat_1(X2_43,X0_45) != X1_43 ),
% 2.10/1.01      inference(instantiation,[status(thm)],[c_293]) ).
% 2.10/1.01  
% 2.10/1.01  cnf(c_1360,plain,
% 2.10/1.01      ( k7_relat_1(sK1,sK0) != sK1
% 2.10/1.01      | sK1 = k7_relat_1(sK1,sK0)
% 2.10/1.01      | sK1 != sK1 ),
% 2.10/1.01      inference(instantiation,[status(thm)],[c_1359]) ).
% 2.10/1.01  
% 2.10/1.01  cnf(c_2464,plain,
% 2.10/1.01      ( r1_tarski(k1_relat_1(sK1),sK0) = iProver_top ),
% 2.10/1.01      inference(global_propositional_subsumption,
% 2.10/1.01                [status(thm)],
% 2.10/1.01                [c_2055,c_13,c_14,c_38,c_39,c_314,c_316,c_325,c_338,
% 2.10/1.01                 c_602,c_603,c_1045,c_1047,c_1360]) ).
% 2.10/1.01  
% 2.10/1.01  cnf(c_12,negated_conjecture,
% 2.10/1.01      ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) ),
% 2.10/1.01      inference(cnf_transformation,[],[f40]) ).
% 2.10/1.01  
% 2.10/1.01  cnf(c_277,negated_conjecture,
% 2.10/1.01      ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) ),
% 2.10/1.01      inference(subtyping,[status(esa)],[c_12]) ).
% 2.10/1.01  
% 2.10/1.01  cnf(c_520,plain,
% 2.10/1.01      ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) = iProver_top ),
% 2.10/1.01      inference(predicate_to_equality,[status(thm)],[c_277]) ).
% 2.10/1.01  
% 2.10/1.01  cnf(c_7,plain,
% 2.10/1.01      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 2.10/1.01      | k2_relset_1(X1,X2,X0) = k2_relat_1(X0) ),
% 2.10/1.01      inference(cnf_transformation,[],[f37]) ).
% 2.10/1.01  
% 2.10/1.01  cnf(c_282,plain,
% 2.10/1.01      ( ~ m1_subset_1(X0_43,k1_zfmisc_1(k2_zfmisc_1(X0_45,X1_45)))
% 2.10/1.01      | k2_relset_1(X0_45,X1_45,X0_43) = k2_relat_1(X0_43) ),
% 2.10/1.01      inference(subtyping,[status(esa)],[c_7]) ).
% 2.10/1.01  
% 2.10/1.01  cnf(c_518,plain,
% 2.10/1.01      ( k2_relset_1(X0_45,X1_45,X0_43) = k2_relat_1(X0_43)
% 2.10/1.01      | m1_subset_1(X0_43,k1_zfmisc_1(k2_zfmisc_1(X0_45,X1_45))) != iProver_top ),
% 2.10/1.01      inference(predicate_to_equality,[status(thm)],[c_282]) ).
% 2.10/1.01  
% 2.10/1.01  cnf(c_709,plain,
% 2.10/1.01      ( k2_relset_1(sK0,sK0,sK2) = k2_relat_1(sK2) ),
% 2.10/1.01      inference(superposition,[status(thm)],[c_520,c_518]) ).
% 2.10/1.01  
% 2.10/1.01  cnf(c_10,negated_conjecture,
% 2.10/1.01      ( k2_relset_1(sK0,sK0,sK2) = sK0 ),
% 2.10/1.01      inference(cnf_transformation,[],[f42]) ).
% 2.10/1.01  
% 2.10/1.01  cnf(c_279,negated_conjecture,
% 2.10/1.01      ( k2_relset_1(sK0,sK0,sK2) = sK0 ),
% 2.10/1.01      inference(subtyping,[status(esa)],[c_10]) ).
% 2.10/1.01  
% 2.10/1.01  cnf(c_715,plain,
% 2.10/1.01      ( k2_relat_1(sK2) = sK0 ),
% 2.10/1.01      inference(light_normalisation,[status(thm)],[c_709,c_279]) ).
% 2.10/1.01  
% 2.10/1.01  cnf(c_3,plain,
% 2.10/1.01      ( ~ r1_tarski(k1_relat_1(X0),k2_relat_1(X1))
% 2.10/1.01      | ~ v1_relat_1(X0)
% 2.10/1.01      | ~ v1_relat_1(X1)
% 2.10/1.01      | k2_relat_1(k5_relat_1(X1,X0)) = k2_relat_1(X0) ),
% 2.10/1.01      inference(cnf_transformation,[],[f33]) ).
% 2.10/1.01  
% 2.10/1.01  cnf(c_285,plain,
% 2.10/1.01      ( ~ r1_tarski(k1_relat_1(X0_43),k2_relat_1(X1_43))
% 2.10/1.01      | ~ v1_relat_1(X0_43)
% 2.10/1.01      | ~ v1_relat_1(X1_43)
% 2.10/1.01      | k2_relat_1(k5_relat_1(X1_43,X0_43)) = k2_relat_1(X0_43) ),
% 2.10/1.01      inference(subtyping,[status(esa)],[c_3]) ).
% 2.10/1.01  
% 2.10/1.01  cnf(c_515,plain,
% 2.10/1.01      ( k2_relat_1(k5_relat_1(X0_43,X1_43)) = k2_relat_1(X1_43)
% 2.10/1.01      | r1_tarski(k1_relat_1(X1_43),k2_relat_1(X0_43)) != iProver_top
% 2.10/1.01      | v1_relat_1(X1_43) != iProver_top
% 2.10/1.01      | v1_relat_1(X0_43) != iProver_top ),
% 2.10/1.01      inference(predicate_to_equality,[status(thm)],[c_285]) ).
% 2.10/1.01  
% 2.10/1.01  cnf(c_862,plain,
% 2.10/1.01      ( k2_relat_1(k5_relat_1(sK2,X0_43)) = k2_relat_1(X0_43)
% 2.10/1.01      | r1_tarski(k1_relat_1(X0_43),sK0) != iProver_top
% 2.10/1.01      | v1_relat_1(X0_43) != iProver_top
% 2.10/1.01      | v1_relat_1(sK2) != iProver_top ),
% 2.10/1.01      inference(superposition,[status(thm)],[c_715,c_515]) ).
% 2.10/1.01  
% 2.10/1.01  cnf(c_513,plain,
% 2.10/1.01      ( m1_subset_1(X0_43,k1_zfmisc_1(X1_43)) != iProver_top
% 2.10/1.01      | v1_relat_1(X1_43) != iProver_top
% 2.10/1.01      | v1_relat_1(X0_43) = iProver_top ),
% 2.10/1.01      inference(predicate_to_equality,[status(thm)],[c_287]) ).
% 2.10/1.01  
% 2.10/1.01  cnf(c_770,plain,
% 2.10/1.01      ( v1_relat_1(k2_zfmisc_1(sK0,sK0)) != iProver_top
% 2.10/1.01      | v1_relat_1(sK2) = iProver_top ),
% 2.10/1.01      inference(superposition,[status(thm)],[c_520,c_513]) ).
% 2.10/1.01  
% 2.10/1.01  cnf(c_1543,plain,
% 2.10/1.01      ( v1_relat_1(X0_43) != iProver_top
% 2.10/1.01      | r1_tarski(k1_relat_1(X0_43),sK0) != iProver_top
% 2.10/1.01      | k2_relat_1(k5_relat_1(sK2,X0_43)) = k2_relat_1(X0_43) ),
% 2.10/1.01      inference(global_propositional_subsumption,
% 2.10/1.01                [status(thm)],
% 2.10/1.01                [c_862,c_39,c_770]) ).
% 2.10/1.01  
% 2.10/1.01  cnf(c_1544,plain,
% 2.10/1.01      ( k2_relat_1(k5_relat_1(sK2,X0_43)) = k2_relat_1(X0_43)
% 2.10/1.01      | r1_tarski(k1_relat_1(X0_43),sK0) != iProver_top
% 2.10/1.01      | v1_relat_1(X0_43) != iProver_top ),
% 2.10/1.01      inference(renaming,[status(thm)],[c_1543]) ).
% 2.10/1.01  
% 2.10/1.01  cnf(c_2469,plain,
% 2.10/1.01      ( k2_relat_1(k5_relat_1(sK2,sK1)) = k2_relat_1(sK1)
% 2.10/1.01      | v1_relat_1(sK1) != iProver_top ),
% 2.10/1.01      inference(superposition,[status(thm)],[c_2464,c_1544]) ).
% 2.10/1.01  
% 2.10/1.01  cnf(c_710,plain,
% 2.10/1.01      ( k2_relset_1(sK0,sK0,sK1) = k2_relat_1(sK1) ),
% 2.10/1.01      inference(superposition,[status(thm)],[c_521,c_518]) ).
% 2.10/1.01  
% 2.10/1.01  cnf(c_11,negated_conjecture,
% 2.10/1.01      ( k2_relset_1(sK0,sK0,sK1) = sK0 ),
% 2.10/1.01      inference(cnf_transformation,[],[f41]) ).
% 2.10/1.01  
% 2.10/1.01  cnf(c_278,negated_conjecture,
% 2.10/1.01      ( k2_relset_1(sK0,sK0,sK1) = sK0 ),
% 2.10/1.01      inference(subtyping,[status(esa)],[c_11]) ).
% 2.10/1.01  
% 2.10/1.01  cnf(c_712,plain,
% 2.10/1.01      ( k2_relat_1(sK1) = sK0 ),
% 2.10/1.01      inference(light_normalisation,[status(thm)],[c_710,c_278]) ).
% 2.10/1.01  
% 2.10/1.01  cnf(c_2476,plain,
% 2.10/1.01      ( k2_relat_1(k5_relat_1(sK2,sK1)) = sK0
% 2.10/1.01      | v1_relat_1(sK1) != iProver_top ),
% 2.10/1.01      inference(light_normalisation,[status(thm)],[c_2469,c_712]) ).
% 2.10/1.01  
% 2.10/1.01  cnf(c_294,plain,
% 2.10/1.01      ( X0_45 != X1_45 | X2_45 != X1_45 | X2_45 = X0_45 ),
% 2.10/1.01      theory(equality) ).
% 2.10/1.01  
% 2.10/1.01  cnf(c_1168,plain,
% 2.10/1.01      ( k2_relat_1(X0_43) != X0_45
% 2.10/1.01      | sK0 != X0_45
% 2.10/1.01      | sK0 = k2_relat_1(X0_43) ),
% 2.10/1.01      inference(instantiation,[status(thm)],[c_294]) ).
% 2.10/1.01  
% 2.10/1.01  cnf(c_2419,plain,
% 2.10/1.01      ( k2_relat_1(k5_relat_1(sK2,sK1)) != X0_45
% 2.10/1.01      | sK0 != X0_45
% 2.10/1.01      | sK0 = k2_relat_1(k5_relat_1(sK2,sK1)) ),
% 2.10/1.01      inference(instantiation,[status(thm)],[c_1168]) ).
% 2.10/1.01  
% 2.10/1.01  cnf(c_2420,plain,
% 2.10/1.01      ( k2_relat_1(k5_relat_1(sK2,sK1)) != sK0
% 2.10/1.01      | sK0 = k2_relat_1(k5_relat_1(sK2,sK1))
% 2.10/1.01      | sK0 != sK0 ),
% 2.10/1.01      inference(instantiation,[status(thm)],[c_2419]) ).
% 2.10/1.01  
% 2.10/1.01  cnf(c_983,plain,
% 2.10/1.01      ( X0_45 != X1_45
% 2.10/1.01      | k2_relat_1(k4_relset_1(sK0,sK0,sK0,sK0,sK2,sK1)) != X1_45
% 2.10/1.01      | k2_relat_1(k4_relset_1(sK0,sK0,sK0,sK0,sK2,sK1)) = X0_45 ),
% 2.10/1.01      inference(instantiation,[status(thm)],[c_294]) ).
% 2.10/1.01  
% 2.10/1.01  cnf(c_1587,plain,
% 2.10/1.01      ( X0_45 != k2_relat_1(k5_relat_1(sK2,sK1))
% 2.10/1.01      | k2_relat_1(k4_relset_1(sK0,sK0,sK0,sK0,sK2,sK1)) = X0_45
% 2.10/1.01      | k2_relat_1(k4_relset_1(sK0,sK0,sK0,sK0,sK2,sK1)) != k2_relat_1(k5_relat_1(sK2,sK1)) ),
% 2.10/1.01      inference(instantiation,[status(thm)],[c_983]) ).
% 2.10/1.01  
% 2.10/1.01  cnf(c_1588,plain,
% 2.10/1.01      ( k2_relat_1(k4_relset_1(sK0,sK0,sK0,sK0,sK2,sK1)) != k2_relat_1(k5_relat_1(sK2,sK1))
% 2.10/1.01      | k2_relat_1(k4_relset_1(sK0,sK0,sK0,sK0,sK2,sK1)) = sK0
% 2.10/1.01      | sK0 != k2_relat_1(k5_relat_1(sK2,sK1)) ),
% 2.10/1.01      inference(instantiation,[status(thm)],[c_1587]) ).
% 2.10/1.01  
% 2.10/1.01  cnf(c_299,plain,
% 2.10/1.01      ( k2_relat_1(X0_43) = k2_relat_1(X1_43) | X0_43 != X1_43 ),
% 2.10/1.01      theory(equality) ).
% 2.10/1.01  
% 2.10/1.01  cnf(c_985,plain,
% 2.10/1.01      ( k2_relat_1(k4_relset_1(sK0,sK0,sK0,sK0,sK2,sK1)) = k2_relat_1(X0_43)
% 2.10/1.01      | k4_relset_1(sK0,sK0,sK0,sK0,sK2,sK1) != X0_43 ),
% 2.10/1.01      inference(instantiation,[status(thm)],[c_299]) ).
% 2.10/1.01  
% 2.10/1.01  cnf(c_1177,plain,
% 2.10/1.01      ( k2_relat_1(k4_relset_1(sK0,sK0,sK0,sK0,sK2,sK1)) = k2_relat_1(k5_relat_1(sK2,sK1))
% 2.10/1.01      | k4_relset_1(sK0,sK0,sK0,sK0,sK2,sK1) != k5_relat_1(sK2,sK1) ),
% 2.10/1.01      inference(instantiation,[status(thm)],[c_985]) ).
% 2.10/1.01  
% 2.10/1.01  cnf(c_8,plain,
% 2.10/1.01      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 2.10/1.01      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X4,X5)))
% 2.10/1.01      | k4_relset_1(X4,X5,X1,X2,X3,X0) = k5_relat_1(X3,X0) ),
% 2.10/1.01      inference(cnf_transformation,[],[f38]) ).
% 2.10/1.01  
% 2.10/1.01  cnf(c_281,plain,
% 2.10/1.01      ( ~ m1_subset_1(X0_43,k1_zfmisc_1(k2_zfmisc_1(X0_45,X1_45)))
% 2.10/1.01      | ~ m1_subset_1(X1_43,k1_zfmisc_1(k2_zfmisc_1(X2_45,X3_45)))
% 2.10/1.01      | k4_relset_1(X2_45,X3_45,X0_45,X1_45,X1_43,X0_43) = k5_relat_1(X1_43,X0_43) ),
% 2.10/1.01      inference(subtyping,[status(esa)],[c_8]) ).
% 2.10/1.01  
% 2.10/1.01  cnf(c_843,plain,
% 2.10/1.01      ( ~ m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
% 2.10/1.01      | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
% 2.10/1.01      | k4_relset_1(sK0,sK0,sK0,sK0,sK2,sK1) = k5_relat_1(sK2,sK1) ),
% 2.10/1.01      inference(instantiation,[status(thm)],[c_281]) ).
% 2.10/1.01  
% 2.10/1.01  cnf(c_6,plain,
% 2.10/1.01      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 2.10/1.01      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X4,X5)))
% 2.10/1.01      | m1_subset_1(k4_relset_1(X4,X5,X1,X2,X3,X0),k1_zfmisc_1(k2_zfmisc_1(X4,X2))) ),
% 2.10/1.01      inference(cnf_transformation,[],[f36]) ).
% 2.10/1.01  
% 2.10/1.01  cnf(c_283,plain,
% 2.10/1.01      ( ~ m1_subset_1(X0_43,k1_zfmisc_1(k2_zfmisc_1(X0_45,X1_45)))
% 2.10/1.01      | ~ m1_subset_1(X1_43,k1_zfmisc_1(k2_zfmisc_1(X2_45,X3_45)))
% 2.10/1.01      | m1_subset_1(k4_relset_1(X2_45,X3_45,X0_45,X1_45,X1_43,X0_43),k1_zfmisc_1(k2_zfmisc_1(X2_45,X1_45))) ),
% 2.10/1.01      inference(subtyping,[status(esa)],[c_6]) ).
% 2.10/1.01  
% 2.10/1.01  cnf(c_740,plain,
% 2.10/1.01      ( m1_subset_1(k4_relset_1(sK0,sK0,sK0,sK0,sK2,sK1),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
% 2.10/1.01      | ~ m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
% 2.10/1.01      | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) ),
% 2.10/1.01      inference(instantiation,[status(thm)],[c_283]) ).
% 2.10/1.01  
% 2.10/1.01  cnf(c_738,plain,
% 2.10/1.01      ( k2_relat_1(k4_relset_1(sK0,sK0,sK0,sK0,sK2,sK1)) != X0_45
% 2.10/1.01      | sK0 != X0_45
% 2.10/1.01      | sK0 = k2_relat_1(k4_relset_1(sK0,sK0,sK0,sK0,sK2,sK1)) ),
% 2.10/1.01      inference(instantiation,[status(thm)],[c_294]) ).
% 2.10/1.01  
% 2.10/1.01  cnf(c_739,plain,
% 2.10/1.01      ( k2_relat_1(k4_relset_1(sK0,sK0,sK0,sK0,sK2,sK1)) != sK0
% 2.10/1.01      | sK0 = k2_relat_1(k4_relset_1(sK0,sK0,sK0,sK0,sK2,sK1))
% 2.10/1.01      | sK0 != sK0 ),
% 2.10/1.01      inference(instantiation,[status(thm)],[c_738]) ).
% 2.10/1.01  
% 2.10/1.01  cnf(c_645,plain,
% 2.10/1.01      ( ~ m1_subset_1(k4_relset_1(sK0,sK0,sK0,sK0,sK2,sK1),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
% 2.10/1.01      | k2_relset_1(sK0,sK0,k4_relset_1(sK0,sK0,sK0,sK0,sK2,sK1)) = k2_relat_1(k4_relset_1(sK0,sK0,sK0,sK0,sK2,sK1)) ),
% 2.10/1.01      inference(instantiation,[status(thm)],[c_282]) ).
% 2.10/1.01  
% 2.10/1.01  cnf(c_610,plain,
% 2.10/1.01      ( k2_relset_1(sK0,sK0,k4_relset_1(sK0,sK0,sK0,sK0,sK2,sK1)) != X0_45
% 2.10/1.01      | k2_relset_1(sK0,sK0,k4_relset_1(sK0,sK0,sK0,sK0,sK2,sK1)) = sK0
% 2.10/1.01      | sK0 != X0_45 ),
% 2.10/1.01      inference(instantiation,[status(thm)],[c_294]) ).
% 2.10/1.01  
% 2.10/1.01  cnf(c_644,plain,
% 2.10/1.01      ( k2_relset_1(sK0,sK0,k4_relset_1(sK0,sK0,sK0,sK0,sK2,sK1)) != k2_relat_1(k4_relset_1(sK0,sK0,sK0,sK0,sK2,sK1))
% 2.10/1.01      | k2_relset_1(sK0,sK0,k4_relset_1(sK0,sK0,sK0,sK0,sK2,sK1)) = sK0
% 2.10/1.01      | sK0 != k2_relat_1(k4_relset_1(sK0,sK0,sK0,sK0,sK2,sK1)) ),
% 2.10/1.01      inference(instantiation,[status(thm)],[c_610]) ).
% 2.10/1.01  
% 2.10/1.01  cnf(c_9,negated_conjecture,
% 2.10/1.01      ( k2_relset_1(sK0,sK0,k4_relset_1(sK0,sK0,sK0,sK0,sK2,sK1)) != sK0 ),
% 2.10/1.01      inference(cnf_transformation,[],[f43]) ).
% 2.10/1.01  
% 2.10/1.01  cnf(c_280,negated_conjecture,
% 2.10/1.01      ( k2_relset_1(sK0,sK0,k4_relset_1(sK0,sK0,sK0,sK0,sK2,sK1)) != sK0 ),
% 2.10/1.01      inference(subtyping,[status(esa)],[c_9]) ).
% 2.10/1.01  
% 2.10/1.01  cnf(contradiction,plain,
% 2.10/1.01      ( $false ),
% 2.10/1.01      inference(minisat,
% 2.10/1.01                [status(thm)],
% 2.10/1.01                [c_2476,c_2420,c_1588,c_1177,c_843,c_740,c_739,c_645,
% 2.10/1.01                 c_644,c_603,c_280,c_316,c_39,c_12,c_14,c_13]) ).
% 2.10/1.01  
% 2.10/1.01  
% 2.10/1.01  % SZS output end CNFRefutation for theBenchmark.p
% 2.10/1.01  
% 2.10/1.01  ------                               Statistics
% 2.10/1.01  
% 2.10/1.01  ------ General
% 2.10/1.01  
% 2.10/1.01  abstr_ref_over_cycles:                  0
% 2.10/1.01  abstr_ref_under_cycles:                 0
% 2.10/1.01  gc_basic_clause_elim:                   0
% 2.10/1.01  forced_gc_time:                         0
% 2.10/1.01  parsing_time:                           0.031
% 2.10/1.01  unif_index_cands_time:                  0.
% 2.10/1.01  unif_index_add_time:                    0.
% 2.10/1.01  orderings_time:                         0.
% 2.10/1.01  out_proof_time:                         0.015
% 2.10/1.01  total_time:                             0.174
% 2.10/1.01  num_of_symbols:                         50
% 2.10/1.01  num_of_terms:                           2808
% 2.10/1.01  
% 2.10/1.01  ------ Preprocessing
% 2.10/1.01  
% 2.10/1.01  num_of_splits:                          0
% 2.10/1.01  num_of_split_atoms:                     0
% 2.10/1.01  num_of_reused_defs:                     0
% 2.10/1.01  num_eq_ax_congr_red:                    14
% 2.10/1.01  num_of_sem_filtered_clauses:            1
% 2.10/1.01  num_of_subtypes:                        4
% 2.10/1.01  monotx_restored_types:                  0
% 2.10/1.01  sat_num_of_epr_types:                   0
% 2.10/1.01  sat_num_of_non_cyclic_types:            0
% 2.10/1.01  sat_guarded_non_collapsed_types:        1
% 2.10/1.01  num_pure_diseq_elim:                    0
% 2.10/1.01  simp_replaced_by:                       0
% 2.10/1.01  res_preprocessed:                       84
% 2.10/1.01  prep_upred:                             0
% 2.10/1.01  prep_unflattend:                        2
% 2.10/1.01  smt_new_axioms:                         0
% 2.10/1.01  pred_elim_cands:                        3
% 2.10/1.01  pred_elim:                              1
% 2.10/1.01  pred_elim_cl:                           1
% 2.10/1.01  pred_elim_cycles:                       3
% 2.10/1.01  merged_defs:                            0
% 2.10/1.01  merged_defs_ncl:                        0
% 2.10/1.01  bin_hyper_res:                          0
% 2.10/1.01  prep_cycles:                            4
% 2.10/1.01  pred_elim_time:                         0.001
% 2.10/1.01  splitting_time:                         0.
% 2.10/1.01  sem_filter_time:                        0.
% 2.10/1.01  monotx_time:                            0.
% 2.10/1.01  subtype_inf_time:                       0.
% 2.10/1.01  
% 2.10/1.01  ------ Problem properties
% 2.10/1.01  
% 2.10/1.01  clauses:                                13
% 2.10/1.01  conjectures:                            5
% 2.10/1.01  epr:                                    0
% 2.10/1.01  horn:                                   13
% 2.10/1.01  ground:                                 5
% 2.10/1.01  unary:                                  6
% 2.10/1.01  binary:                                 2
% 2.10/1.01  lits:                                   26
% 2.10/1.01  lits_eq:                                7
% 2.10/1.01  fd_pure:                                0
% 2.10/1.01  fd_pseudo:                              0
% 2.10/1.01  fd_cond:                                0
% 2.10/1.01  fd_pseudo_cond:                         0
% 2.10/1.01  ac_symbols:                             0
% 2.10/1.01  
% 2.10/1.01  ------ Propositional Solver
% 2.10/1.01  
% 2.10/1.01  prop_solver_calls:                      28
% 2.10/1.01  prop_fast_solver_calls:                 487
% 2.10/1.01  smt_solver_calls:                       0
% 2.10/1.01  smt_fast_solver_calls:                  0
% 2.10/1.01  prop_num_of_clauses:                    926
% 2.10/1.01  prop_preprocess_simplified:             3169
% 2.10/1.01  prop_fo_subsumed:                       13
% 2.10/1.01  prop_solver_time:                       0.
% 2.10/1.01  smt_solver_time:                        0.
% 2.10/1.01  smt_fast_solver_time:                   0.
% 2.10/1.01  prop_fast_solver_time:                  0.
% 2.10/1.01  prop_unsat_core_time:                   0.
% 2.10/1.01  
% 2.10/1.01  ------ QBF
% 2.10/1.01  
% 2.10/1.01  qbf_q_res:                              0
% 2.10/1.01  qbf_num_tautologies:                    0
% 2.10/1.01  qbf_prep_cycles:                        0
% 2.10/1.01  
% 2.10/1.01  ------ BMC1
% 2.10/1.01  
% 2.10/1.01  bmc1_current_bound:                     -1
% 2.10/1.01  bmc1_last_solved_bound:                 -1
% 2.10/1.01  bmc1_unsat_core_size:                   -1
% 2.10/1.01  bmc1_unsat_core_parents_size:           -1
% 2.10/1.01  bmc1_merge_next_fun:                    0
% 2.10/1.01  bmc1_unsat_core_clauses_time:           0.
% 2.10/1.01  
% 2.10/1.01  ------ Instantiation
% 2.10/1.01  
% 2.10/1.01  inst_num_of_clauses:                    342
% 2.10/1.01  inst_num_in_passive:                    39
% 2.10/1.01  inst_num_in_active:                     215
% 2.10/1.01  inst_num_in_unprocessed:                88
% 2.10/1.01  inst_num_of_loops:                      230
% 2.10/1.01  inst_num_of_learning_restarts:          0
% 2.10/1.01  inst_num_moves_active_passive:          12
% 2.10/1.01  inst_lit_activity:                      0
% 2.10/1.01  inst_lit_activity_moves:                0
% 2.10/1.01  inst_num_tautologies:                   0
% 2.10/1.01  inst_num_prop_implied:                  0
% 2.10/1.01  inst_num_existing_simplified:           0
% 2.10/1.01  inst_num_eq_res_simplified:             0
% 2.10/1.01  inst_num_child_elim:                    0
% 2.10/1.01  inst_num_of_dismatching_blockings:      101
% 2.10/1.01  inst_num_of_non_proper_insts:           335
% 2.10/1.01  inst_num_of_duplicates:                 0
% 2.10/1.01  inst_inst_num_from_inst_to_res:         0
% 2.10/1.01  inst_dismatching_checking_time:         0.
% 2.10/1.01  
% 2.10/1.01  ------ Resolution
% 2.10/1.01  
% 2.10/1.01  res_num_of_clauses:                     0
% 2.10/1.01  res_num_in_passive:                     0
% 2.10/1.01  res_num_in_active:                      0
% 2.10/1.01  res_num_of_loops:                       88
% 2.10/1.01  res_forward_subset_subsumed:            70
% 2.10/1.01  res_backward_subset_subsumed:           2
% 2.10/1.01  res_forward_subsumed:                   0
% 2.10/1.01  res_backward_subsumed:                  0
% 2.10/1.01  res_forward_subsumption_resolution:     0
% 2.10/1.01  res_backward_subsumption_resolution:    0
% 2.10/1.01  res_clause_to_clause_subsumption:       74
% 2.10/1.01  res_orphan_elimination:                 0
% 2.10/1.01  res_tautology_del:                      53
% 2.10/1.01  res_num_eq_res_simplified:              0
% 2.10/1.01  res_num_sel_changes:                    0
% 2.10/1.01  res_moves_from_active_to_pass:          0
% 2.10/1.01  
% 2.10/1.01  ------ Superposition
% 2.10/1.01  
% 2.10/1.01  sup_time_total:                         0.
% 2.10/1.01  sup_time_generating:                    0.
% 2.10/1.01  sup_time_sim_full:                      0.
% 2.10/1.01  sup_time_sim_immed:                     0.
% 2.10/1.01  
% 2.10/1.01  sup_num_of_clauses:                     65
% 2.10/1.01  sup_num_in_active:                      42
% 2.10/1.01  sup_num_in_passive:                     23
% 2.10/1.01  sup_num_of_loops:                       44
% 2.10/1.01  sup_fw_superposition:                   23
% 2.10/1.01  sup_bw_superposition:                   31
% 2.10/1.01  sup_immediate_simplified:               8
% 2.10/1.01  sup_given_eliminated:                   0
% 2.10/1.01  comparisons_done:                       0
% 2.10/1.01  comparisons_avoided:                    0
% 2.10/1.01  
% 2.10/1.01  ------ Simplifications
% 2.10/1.01  
% 2.10/1.01  
% 2.10/1.01  sim_fw_subset_subsumed:                 0
% 2.10/1.01  sim_bw_subset_subsumed:                 0
% 2.10/1.01  sim_fw_subsumed:                        0
% 2.10/1.01  sim_bw_subsumed:                        0
% 2.10/1.01  sim_fw_subsumption_res:                 0
% 2.10/1.01  sim_bw_subsumption_res:                 0
% 2.10/1.01  sim_tautology_del:                      0
% 2.10/1.01  sim_eq_tautology_del:                   1
% 2.10/1.01  sim_eq_res_simp:                        0
% 2.10/1.01  sim_fw_demodulated:                     0
% 2.10/1.01  sim_bw_demodulated:                     3
% 2.10/1.01  sim_light_normalised:                   8
% 2.10/1.01  sim_joinable_taut:                      0
% 2.10/1.01  sim_joinable_simp:                      0
% 2.10/1.01  sim_ac_normalised:                      0
% 2.10/1.01  sim_smt_subsumption:                    0
% 2.10/1.01  
%------------------------------------------------------------------------------
