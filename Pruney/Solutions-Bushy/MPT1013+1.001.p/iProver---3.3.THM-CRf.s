%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT1013+1.001 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n029.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:44:39 EST 2020

% Result     : Theorem 1.12s
% Output     : CNFRefutation 1.12s
% Verified   : 
% Statistics : Number of formulae       :   97 ( 190 expanded)
%              Number of clauses        :   62 (  81 expanded)
%              Number of leaves         :   13 (  45 expanded)
%              Depth                    :   13
%              Number of atoms          :  226 ( 660 expanded)
%              Number of equality atoms :  132 ( 394 expanded)
%              Maximal formula depth    :   10 (   4 average)
%              Maximal clause size      :   10 (   2 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f8,conjecture,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
     => ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
         => ( ( k2_relset_1(X0,X0,X2) = X0
              & k2_relset_1(X0,X0,X1) = X0 )
           => k2_relset_1(X0,X0,k4_relset_1(X0,X0,X0,X0,X2,X1)) = X0 ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f9,negated_conjecture,(
    ~ ! [X0,X1] :
        ( m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
       => ! [X2] :
            ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
           => ( ( k2_relset_1(X0,X0,X2) = X0
                & k2_relset_1(X0,X0,X1) = X0 )
             => k2_relset_1(X0,X0,k4_relset_1(X0,X0,X0,X0,X2,X1)) = X0 ) ) ) ),
    inference(negated_conjecture,[],[f8])).

fof(f19,plain,(
    ? [X0,X1] :
      ( ? [X2] :
          ( k2_relset_1(X0,X0,k4_relset_1(X0,X0,X0,X0,X2,X1)) != X0
          & k2_relset_1(X0,X0,X2) = X0
          & k2_relset_1(X0,X0,X1) = X0
          & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) )
      & m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f20,plain,(
    ? [X0,X1] :
      ( ? [X2] :
          ( k2_relset_1(X0,X0,k4_relset_1(X0,X0,X0,X0,X2,X1)) != X0
          & k2_relset_1(X0,X0,X2) = X0
          & k2_relset_1(X0,X0,X1) = X0
          & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) )
      & m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) ) ),
    inference(flattening,[],[f19])).

fof(f22,plain,(
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

fof(f21,plain,
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

fof(f23,plain,
    ( k2_relset_1(sK0,sK0,k4_relset_1(sK0,sK0,sK0,sK0,sK2,sK1)) != sK0
    & k2_relset_1(sK0,sK0,sK2) = sK0
    & k2_relset_1(sK0,sK0,sK1) = sK0
    & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
    & m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f20,f22,f21])).

fof(f33,plain,(
    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) ),
    inference(cnf_transformation,[],[f23])).

fof(f1,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => v1_relat_1(X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f10,plain,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f24,plain,(
    ! [X2,X0,X1] :
      ( v1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f10])).

fof(f32,plain,(
    m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) ),
    inference(cnf_transformation,[],[f23])).

fof(f6,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( v1_relat_1(X1)
         => k2_relat_1(k5_relat_1(X0,X1)) = k9_relat_1(X1,k2_relat_1(X0)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f17,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k2_relat_1(k5_relat_1(X0,X1)) = k9_relat_1(X1,k2_relat_1(X0))
          | ~ v1_relat_1(X1) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f29,plain,(
    ! [X0,X1] :
      ( k2_relat_1(k5_relat_1(X0,X1)) = k9_relat_1(X1,k2_relat_1(X0))
      | ~ v1_relat_1(X1)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f3,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k2_relset_1(X0,X1,X2) = k2_relat_1(X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f13,plain,(
    ! [X0,X1,X2] :
      ( k2_relset_1(X0,X1,X2) = k2_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f26,plain,(
    ! [X2,X0,X1] :
      ( k2_relset_1(X0,X1,X2) = k2_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f13])).

fof(f35,plain,(
    k2_relset_1(sK0,sK0,sK2) = sK0 ),
    inference(cnf_transformation,[],[f23])).

fof(f5,axiom,(
    ! [X0,X1,X2,X3] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k7_relset_1(X0,X1,X2,X3) = k9_relat_1(X2,X3) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f16,plain,(
    ! [X0,X1,X2,X3] :
      ( k7_relset_1(X0,X1,X2,X3) = k9_relat_1(X2,X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f28,plain,(
    ! [X2,X0,X3,X1] :
      ( k7_relset_1(X0,X1,X2,X3) = k9_relat_1(X2,X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f16])).

fof(f7,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => ( k8_relset_1(X0,X1,X2,X1) = k1_relset_1(X0,X1,X2)
        & k2_relset_1(X0,X1,X2) = k7_relset_1(X0,X1,X2,X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f18,plain,(
    ! [X0,X1,X2] :
      ( ( k8_relset_1(X0,X1,X2,X1) = k1_relset_1(X0,X1,X2)
        & k2_relset_1(X0,X1,X2) = k7_relset_1(X0,X1,X2,X0) )
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f30,plain,(
    ! [X2,X0,X1] :
      ( k2_relset_1(X0,X1,X2) = k7_relset_1(X0,X1,X2,X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f34,plain,(
    k2_relset_1(sK0,sK0,sK1) = sK0 ),
    inference(cnf_transformation,[],[f23])).

fof(f4,axiom,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( ( m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
        & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) )
     => k4_relset_1(X0,X1,X2,X3,X4,X5) = k5_relat_1(X4,X5) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f14,plain,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( k4_relset_1(X0,X1,X2,X3,X4,X5) = k5_relat_1(X4,X5)
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f15,plain,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( k4_relset_1(X0,X1,X2,X3,X4,X5) = k5_relat_1(X4,X5)
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(flattening,[],[f14])).

fof(f27,plain,(
    ! [X4,X2,X0,X5,X3,X1] :
      ( k4_relset_1(X0,X1,X2,X3,X4,X5) = k5_relat_1(X4,X5)
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f15])).

fof(f2,axiom,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( ( m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
        & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) )
     => m1_subset_1(k4_relset_1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3))) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f11,plain,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( m1_subset_1(k4_relset_1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3)))
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f12,plain,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( m1_subset_1(k4_relset_1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3)))
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(flattening,[],[f11])).

fof(f25,plain,(
    ! [X4,X2,X0,X5,X3,X1] :
      ( m1_subset_1(k4_relset_1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3)))
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f12])).

fof(f36,plain,(
    k2_relset_1(sK0,sK0,k4_relset_1(sK0,sK0,sK0,sK0,sK2,sK1)) != sK0 ),
    inference(cnf_transformation,[],[f23])).

cnf(c_144,plain,
    ( X0_46 != X1_46
    | X2_46 != X1_46
    | X2_46 = X0_46 ),
    theory(equality)).

cnf(c_719,plain,
    ( k2_relat_1(X0_43) != X0_46
    | sK0 != X0_46
    | sK0 = k2_relat_1(X0_43) ),
    inference(instantiation,[status(thm)],[c_144])).

cnf(c_1197,plain,
    ( k2_relat_1(k5_relat_1(sK2,sK1)) != X0_46
    | sK0 != X0_46
    | sK0 = k2_relat_1(k5_relat_1(sK2,sK1)) ),
    inference(instantiation,[status(thm)],[c_719])).

cnf(c_1198,plain,
    ( k2_relat_1(k5_relat_1(sK2,sK1)) != sK0
    | sK0 = k2_relat_1(k5_relat_1(sK2,sK1))
    | sK0 != sK0 ),
    inference(instantiation,[status(thm)],[c_1197])).

cnf(c_11,negated_conjecture,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) ),
    inference(cnf_transformation,[],[f33])).

cnf(c_125,negated_conjecture,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) ),
    inference(subtyping,[status(esa)],[c_11])).

cnf(c_344,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_125])).

cnf(c_0,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f24])).

cnf(c_136,plain,
    ( ~ m1_subset_1(X0_43,k1_zfmisc_1(k2_zfmisc_1(X0_46,X1_46)))
    | v1_relat_1(X0_43) ),
    inference(subtyping,[status(esa)],[c_0])).

cnf(c_336,plain,
    ( m1_subset_1(X0_43,k1_zfmisc_1(k2_zfmisc_1(X0_46,X1_46))) != iProver_top
    | v1_relat_1(X0_43) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_136])).

cnf(c_480,plain,
    ( v1_relat_1(sK2) = iProver_top ),
    inference(superposition,[status(thm)],[c_344,c_336])).

cnf(c_12,negated_conjecture,
    ( m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) ),
    inference(cnf_transformation,[],[f32])).

cnf(c_124,negated_conjecture,
    ( m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) ),
    inference(subtyping,[status(esa)],[c_12])).

cnf(c_345,plain,
    ( m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_124])).

cnf(c_481,plain,
    ( v1_relat_1(sK1) = iProver_top ),
    inference(superposition,[status(thm)],[c_345,c_336])).

cnf(c_5,plain,
    ( ~ v1_relat_1(X0)
    | ~ v1_relat_1(X1)
    | k9_relat_1(X0,k2_relat_1(X1)) = k2_relat_1(k5_relat_1(X1,X0)) ),
    inference(cnf_transformation,[],[f29])).

cnf(c_131,plain,
    ( ~ v1_relat_1(X0_43)
    | ~ v1_relat_1(X1_43)
    | k9_relat_1(X0_43,k2_relat_1(X1_43)) = k2_relat_1(k5_relat_1(X1_43,X0_43)) ),
    inference(subtyping,[status(esa)],[c_5])).

cnf(c_341,plain,
    ( k9_relat_1(X0_43,k2_relat_1(X1_43)) = k2_relat_1(k5_relat_1(X1_43,X0_43))
    | v1_relat_1(X0_43) != iProver_top
    | v1_relat_1(X1_43) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_131])).

cnf(c_1046,plain,
    ( k9_relat_1(sK1,k2_relat_1(X0_43)) = k2_relat_1(k5_relat_1(X0_43,sK1))
    | v1_relat_1(X0_43) != iProver_top ),
    inference(superposition,[status(thm)],[c_481,c_341])).

cnf(c_1158,plain,
    ( k9_relat_1(sK1,k2_relat_1(sK2)) = k2_relat_1(k5_relat_1(sK2,sK1)) ),
    inference(superposition,[status(thm)],[c_480,c_1046])).

cnf(c_2,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k2_relset_1(X1,X2,X0) = k2_relat_1(X0) ),
    inference(cnf_transformation,[],[f26])).

cnf(c_134,plain,
    ( ~ m1_subset_1(X0_43,k1_zfmisc_1(k2_zfmisc_1(X0_46,X1_46)))
    | k2_relset_1(X0_46,X1_46,X0_43) = k2_relat_1(X0_43) ),
    inference(subtyping,[status(esa)],[c_2])).

cnf(c_338,plain,
    ( k2_relset_1(X0_46,X1_46,X0_43) = k2_relat_1(X0_43)
    | m1_subset_1(X0_43,k1_zfmisc_1(k2_zfmisc_1(X0_46,X1_46))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_134])).

cnf(c_575,plain,
    ( k2_relset_1(sK0,sK0,sK2) = k2_relat_1(sK2) ),
    inference(superposition,[status(thm)],[c_344,c_338])).

cnf(c_9,negated_conjecture,
    ( k2_relset_1(sK0,sK0,sK2) = sK0 ),
    inference(cnf_transformation,[],[f35])).

cnf(c_127,negated_conjecture,
    ( k2_relset_1(sK0,sK0,sK2) = sK0 ),
    inference(subtyping,[status(esa)],[c_9])).

cnf(c_588,plain,
    ( k2_relat_1(sK2) = sK0 ),
    inference(light_normalisation,[status(thm)],[c_575,c_127])).

cnf(c_4,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k7_relset_1(X1,X2,X0,X3) = k9_relat_1(X0,X3) ),
    inference(cnf_transformation,[],[f28])).

cnf(c_132,plain,
    ( ~ m1_subset_1(X0_43,k1_zfmisc_1(k2_zfmisc_1(X0_46,X1_46)))
    | k7_relset_1(X0_46,X1_46,X0_43,X2_46) = k9_relat_1(X0_43,X2_46) ),
    inference(subtyping,[status(esa)],[c_4])).

cnf(c_340,plain,
    ( k7_relset_1(X0_46,X1_46,X0_43,X2_46) = k9_relat_1(X0_43,X2_46)
    | m1_subset_1(X0_43,k1_zfmisc_1(k2_zfmisc_1(X0_46,X1_46))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_132])).

cnf(c_693,plain,
    ( k7_relset_1(sK0,sK0,sK1,X0_46) = k9_relat_1(sK1,X0_46) ),
    inference(superposition,[status(thm)],[c_345,c_340])).

cnf(c_7,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k7_relset_1(X1,X2,X0,X1) = k2_relset_1(X1,X2,X0) ),
    inference(cnf_transformation,[],[f30])).

cnf(c_129,plain,
    ( ~ m1_subset_1(X0_43,k1_zfmisc_1(k2_zfmisc_1(X0_46,X1_46)))
    | k7_relset_1(X0_46,X1_46,X0_43,X0_46) = k2_relset_1(X0_46,X1_46,X0_43) ),
    inference(subtyping,[status(esa)],[c_7])).

cnf(c_343,plain,
    ( k7_relset_1(X0_46,X1_46,X0_43,X0_46) = k2_relset_1(X0_46,X1_46,X0_43)
    | m1_subset_1(X0_43,k1_zfmisc_1(k2_zfmisc_1(X0_46,X1_46))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_129])).

cnf(c_890,plain,
    ( k7_relset_1(sK0,sK0,sK1,sK0) = k2_relset_1(sK0,sK0,sK1) ),
    inference(superposition,[status(thm)],[c_345,c_343])).

cnf(c_10,negated_conjecture,
    ( k2_relset_1(sK0,sK0,sK1) = sK0 ),
    inference(cnf_transformation,[],[f34])).

cnf(c_126,negated_conjecture,
    ( k2_relset_1(sK0,sK0,sK1) = sK0 ),
    inference(subtyping,[status(esa)],[c_10])).

cnf(c_899,plain,
    ( k7_relset_1(sK0,sK0,sK1,sK0) = sK0 ),
    inference(light_normalisation,[status(thm)],[c_890,c_126])).

cnf(c_908,plain,
    ( k9_relat_1(sK1,sK0) = sK0 ),
    inference(superposition,[status(thm)],[c_693,c_899])).

cnf(c_1160,plain,
    ( k2_relat_1(k5_relat_1(sK2,sK1)) = sK0 ),
    inference(light_normalisation,[status(thm)],[c_1158,c_588,c_908])).

cnf(c_551,plain,
    ( X0_46 != X1_46
    | k2_relat_1(k4_relset_1(sK0,sK0,sK0,sK0,sK2,sK1)) != X1_46
    | k2_relat_1(k4_relset_1(sK0,sK0,sK0,sK0,sK2,sK1)) = X0_46 ),
    inference(instantiation,[status(thm)],[c_144])).

cnf(c_836,plain,
    ( X0_46 != k2_relat_1(k5_relat_1(sK2,sK1))
    | k2_relat_1(k4_relset_1(sK0,sK0,sK0,sK0,sK2,sK1)) = X0_46
    | k2_relat_1(k4_relset_1(sK0,sK0,sK0,sK0,sK2,sK1)) != k2_relat_1(k5_relat_1(sK2,sK1)) ),
    inference(instantiation,[status(thm)],[c_551])).

cnf(c_837,plain,
    ( k2_relat_1(k4_relset_1(sK0,sK0,sK0,sK0,sK2,sK1)) != k2_relat_1(k5_relat_1(sK2,sK1))
    | k2_relat_1(k4_relset_1(sK0,sK0,sK0,sK0,sK2,sK1)) = sK0
    | sK0 != k2_relat_1(k5_relat_1(sK2,sK1)) ),
    inference(instantiation,[status(thm)],[c_836])).

cnf(c_151,plain,
    ( k2_relat_1(X0_43) = k2_relat_1(X1_43)
    | X0_43 != X1_43 ),
    theory(equality)).

cnf(c_553,plain,
    ( k2_relat_1(k4_relset_1(sK0,sK0,sK0,sK0,sK2,sK1)) = k2_relat_1(X0_43)
    | k4_relset_1(sK0,sK0,sK0,sK0,sK2,sK1) != X0_43 ),
    inference(instantiation,[status(thm)],[c_151])).

cnf(c_728,plain,
    ( k2_relat_1(k4_relset_1(sK0,sK0,sK0,sK0,sK2,sK1)) = k2_relat_1(k5_relat_1(sK2,sK1))
    | k4_relset_1(sK0,sK0,sK0,sK0,sK2,sK1) != k5_relat_1(sK2,sK1) ),
    inference(instantiation,[status(thm)],[c_553])).

cnf(c_3,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X4,X5)))
    | k4_relset_1(X4,X5,X1,X2,X3,X0) = k5_relat_1(X3,X0) ),
    inference(cnf_transformation,[],[f27])).

cnf(c_133,plain,
    ( ~ m1_subset_1(X0_43,k1_zfmisc_1(k2_zfmisc_1(X0_46,X1_46)))
    | ~ m1_subset_1(X1_43,k1_zfmisc_1(k2_zfmisc_1(X2_46,X3_46)))
    | k4_relset_1(X2_46,X3_46,X0_46,X1_46,X1_43,X0_43) = k5_relat_1(X1_43,X0_43) ),
    inference(subtyping,[status(esa)],[c_3])).

cnf(c_535,plain,
    ( ~ m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
    | k4_relset_1(sK0,sK0,sK0,sK0,sK2,sK1) = k5_relat_1(sK2,sK1) ),
    inference(instantiation,[status(thm)],[c_133])).

cnf(c_1,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X4,X5)))
    | m1_subset_1(k4_relset_1(X4,X5,X1,X2,X3,X0),k1_zfmisc_1(k2_zfmisc_1(X4,X2))) ),
    inference(cnf_transformation,[],[f25])).

cnf(c_135,plain,
    ( ~ m1_subset_1(X0_43,k1_zfmisc_1(k2_zfmisc_1(X0_46,X1_46)))
    | ~ m1_subset_1(X1_43,k1_zfmisc_1(k2_zfmisc_1(X2_46,X3_46)))
    | m1_subset_1(k4_relset_1(X2_46,X3_46,X0_46,X1_46,X1_43,X0_43),k1_zfmisc_1(k2_zfmisc_1(X2_46,X1_46))) ),
    inference(subtyping,[status(esa)],[c_1])).

cnf(c_493,plain,
    ( m1_subset_1(k4_relset_1(sK0,sK0,sK0,sK0,sK2,sK1),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
    | ~ m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) ),
    inference(instantiation,[status(thm)],[c_135])).

cnf(c_491,plain,
    ( k2_relat_1(k4_relset_1(sK0,sK0,sK0,sK0,sK2,sK1)) != X0_46
    | sK0 != X0_46
    | sK0 = k2_relat_1(k4_relset_1(sK0,sK0,sK0,sK0,sK2,sK1)) ),
    inference(instantiation,[status(thm)],[c_144])).

cnf(c_492,plain,
    ( k2_relat_1(k4_relset_1(sK0,sK0,sK0,sK0,sK2,sK1)) != sK0
    | sK0 = k2_relat_1(k4_relset_1(sK0,sK0,sK0,sK0,sK2,sK1))
    | sK0 != sK0 ),
    inference(instantiation,[status(thm)],[c_491])).

cnf(c_455,plain,
    ( ~ m1_subset_1(k4_relset_1(sK0,sK0,sK0,sK0,sK2,sK1),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
    | k2_relset_1(sK0,sK0,k4_relset_1(sK0,sK0,sK0,sK0,sK2,sK1)) = k2_relat_1(k4_relset_1(sK0,sK0,sK0,sK0,sK2,sK1)) ),
    inference(instantiation,[status(thm)],[c_134])).

cnf(c_416,plain,
    ( k2_relset_1(sK0,sK0,k4_relset_1(sK0,sK0,sK0,sK0,sK2,sK1)) != X0_46
    | k2_relset_1(sK0,sK0,k4_relset_1(sK0,sK0,sK0,sK0,sK2,sK1)) = sK0
    | sK0 != X0_46 ),
    inference(instantiation,[status(thm)],[c_144])).

cnf(c_454,plain,
    ( k2_relset_1(sK0,sK0,k4_relset_1(sK0,sK0,sK0,sK0,sK2,sK1)) != k2_relat_1(k4_relset_1(sK0,sK0,sK0,sK0,sK2,sK1))
    | k2_relset_1(sK0,sK0,k4_relset_1(sK0,sK0,sK0,sK0,sK2,sK1)) = sK0
    | sK0 != k2_relat_1(k4_relset_1(sK0,sK0,sK0,sK0,sK2,sK1)) ),
    inference(instantiation,[status(thm)],[c_416])).

cnf(c_8,negated_conjecture,
    ( k2_relset_1(sK0,sK0,k4_relset_1(sK0,sK0,sK0,sK0,sK2,sK1)) != sK0 ),
    inference(cnf_transformation,[],[f36])).

cnf(c_128,negated_conjecture,
    ( k2_relset_1(sK0,sK0,k4_relset_1(sK0,sK0,sK0,sK0,sK2,sK1)) != sK0 ),
    inference(subtyping,[status(esa)],[c_8])).

cnf(c_141,plain,
    ( X0_46 = X0_46 ),
    theory(equality)).

cnf(c_164,plain,
    ( sK0 = sK0 ),
    inference(instantiation,[status(thm)],[c_141])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_1198,c_1160,c_837,c_728,c_535,c_493,c_492,c_455,c_454,c_128,c_164,c_11,c_12])).


%------------------------------------------------------------------------------
