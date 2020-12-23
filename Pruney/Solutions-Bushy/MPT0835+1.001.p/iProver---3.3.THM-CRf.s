%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0835+1.001 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n027.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:44:12 EST 2020

% Result     : Theorem 1.19s
% Output     : CNFRefutation 1.19s
% Verified   : 
% Statistics : Number of formulae       :   93 ( 257 expanded)
%              Number of clauses        :   61 ( 113 expanded)
%              Number of leaves         :   11 (  50 expanded)
%              Depth                    :   17
%              Number of atoms          :  187 ( 606 expanded)
%              Number of equality atoms :  138 ( 391 expanded)
%              Maximal formula depth    :    8 (   4 average)
%              Maximal clause size      :    6 (   2 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f4,axiom,(
    ! [X0,X1,X2,X3] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k7_relset_1(X0,X1,X2,X3) = k9_relat_1(X2,X3) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f14,plain,(
    ! [X0,X1,X2,X3] :
      ( k7_relset_1(X0,X1,X2,X3) = k9_relat_1(X2,X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f25,plain,(
    ! [X2,X0,X3,X1] :
      ( k7_relset_1(X0,X1,X2,X3) = k9_relat_1(X2,X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f14])).

fof(f9,conjecture,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
     => ( k1_relset_1(X1,X0,X2) = k8_relset_1(X1,X0,X2,k7_relset_1(X1,X0,X2,X1))
        & k2_relset_1(X1,X0,X2) = k7_relset_1(X1,X0,X2,k8_relset_1(X1,X0,X2,X0)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f10,negated_conjecture,(
    ~ ! [X0,X1,X2] :
        ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
       => ( k1_relset_1(X1,X0,X2) = k8_relset_1(X1,X0,X2,k7_relset_1(X1,X0,X2,X1))
          & k2_relset_1(X1,X0,X2) = k7_relset_1(X1,X0,X2,k8_relset_1(X1,X0,X2,X0)) ) ) ),
    inference(negated_conjecture,[],[f9])).

fof(f19,plain,(
    ? [X0,X1,X2] :
      ( ( k1_relset_1(X1,X0,X2) != k8_relset_1(X1,X0,X2,k7_relset_1(X1,X0,X2,X1))
        | k2_relset_1(X1,X0,X2) != k7_relset_1(X1,X0,X2,k8_relset_1(X1,X0,X2,X0)) )
      & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f20,plain,
    ( ? [X0,X1,X2] :
        ( ( k1_relset_1(X1,X0,X2) != k8_relset_1(X1,X0,X2,k7_relset_1(X1,X0,X2,X1))
          | k2_relset_1(X1,X0,X2) != k7_relset_1(X1,X0,X2,k8_relset_1(X1,X0,X2,X0)) )
        & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) )
   => ( ( k1_relset_1(sK1,sK0,sK2) != k8_relset_1(sK1,sK0,sK2,k7_relset_1(sK1,sK0,sK2,sK1))
        | k2_relset_1(sK1,sK0,sK2) != k7_relset_1(sK1,sK0,sK2,k8_relset_1(sK1,sK0,sK2,sK0)) )
      & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) ) ),
    introduced(choice_axiom,[])).

fof(f21,plain,
    ( ( k1_relset_1(sK1,sK0,sK2) != k8_relset_1(sK1,sK0,sK2,k7_relset_1(sK1,sK0,sK2,sK1))
      | k2_relset_1(sK1,sK0,sK2) != k7_relset_1(sK1,sK0,sK2,k8_relset_1(sK1,sK0,sK2,sK0)) )
    & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f19,f20])).

fof(f31,plain,(
    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) ),
    inference(cnf_transformation,[],[f21])).

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

fof(f24,plain,(
    ! [X2,X0,X1] :
      ( k2_relset_1(X0,X1,X2) = k2_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f13])).

fof(f2,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k1_relset_1(X0,X1,X2) = k1_relat_1(X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f12,plain,(
    ! [X0,X1,X2] :
      ( k1_relset_1(X0,X1,X2) = k1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f23,plain,(
    ! [X2,X0,X1] :
      ( k1_relset_1(X0,X1,X2) = k1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f12])).

fof(f32,plain,
    ( k1_relset_1(sK1,sK0,sK2) != k8_relset_1(sK1,sK0,sK2,k7_relset_1(sK1,sK0,sK2,sK1))
    | k2_relset_1(sK1,sK0,sK2) != k7_relset_1(sK1,sK0,sK2,k8_relset_1(sK1,sK0,sK2,sK0)) ),
    inference(cnf_transformation,[],[f21])).

fof(f6,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => k2_relat_1(X0) = k9_relat_1(X0,k1_relat_1(X0)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f16,plain,(
    ! [X0] :
      ( k2_relat_1(X0) = k9_relat_1(X0,k1_relat_1(X0))
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f27,plain,(
    ! [X0] :
      ( k2_relat_1(X0) = k9_relat_1(X0,k1_relat_1(X0))
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f16])).

fof(f1,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => v1_relat_1(X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f11,plain,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f22,plain,(
    ! [X2,X0,X1] :
      ( v1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f11])).

fof(f8,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => ( k1_relset_1(X0,X1,X2) = k8_relset_1(X0,X1,X2,X1)
        & k2_relset_1(X0,X1,X2) = k7_relset_1(X0,X1,X2,X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f18,plain,(
    ! [X0,X1,X2] :
      ( ( k1_relset_1(X0,X1,X2) = k8_relset_1(X0,X1,X2,X1)
        & k2_relset_1(X0,X1,X2) = k7_relset_1(X0,X1,X2,X0) )
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f30,plain,(
    ! [X2,X0,X1] :
      ( k1_relset_1(X0,X1,X2) = k8_relset_1(X0,X1,X2,X1)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f29,plain,(
    ! [X2,X0,X1] :
      ( k2_relset_1(X0,X1,X2) = k7_relset_1(X0,X1,X2,X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f5,axiom,(
    ! [X0,X1,X2,X3] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k8_relset_1(X0,X1,X2,X3) = k10_relat_1(X2,X3) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f15,plain,(
    ! [X0,X1,X2,X3] :
      ( k8_relset_1(X0,X1,X2,X3) = k10_relat_1(X2,X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f26,plain,(
    ! [X2,X0,X3,X1] :
      ( k8_relset_1(X0,X1,X2,X3) = k10_relat_1(X2,X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f15])).

fof(f7,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => k1_relat_1(X0) = k10_relat_1(X0,k2_relat_1(X0)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f17,plain,(
    ! [X0] :
      ( k1_relat_1(X0) = k10_relat_1(X0,k2_relat_1(X0))
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f28,plain,(
    ! [X0] :
      ( k1_relat_1(X0) = k10_relat_1(X0,k2_relat_1(X0))
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f17])).

cnf(c_3,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k7_relset_1(X1,X2,X0,X3) = k9_relat_1(X0,X3) ),
    inference(cnf_transformation,[],[f25])).

cnf(c_10,negated_conjecture,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) ),
    inference(cnf_transformation,[],[f31])).

cnf(c_183,plain,
    ( k7_relset_1(X0,X1,X2,X3) = k9_relat_1(X2,X3)
    | k1_zfmisc_1(k2_zfmisc_1(X0,X1)) != k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))
    | sK2 != X2 ),
    inference(resolution_lifted,[status(thm)],[c_3,c_10])).

cnf(c_184,plain,
    ( k7_relset_1(X0,X1,sK2,X2) = k9_relat_1(sK2,X2)
    | k1_zfmisc_1(k2_zfmisc_1(X0,X1)) != k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)) ),
    inference(unflattening,[status(thm)],[c_183])).

cnf(c_275,plain,
    ( k1_zfmisc_1(k2_zfmisc_1(X0_45,X0_43)) != k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))
    | k7_relset_1(X0_45,X0_43,sK2,X1_45) = k9_relat_1(sK2,X1_45) ),
    inference(subtyping,[status(esa)],[c_184])).

cnf(c_374,plain,
    ( k7_relset_1(sK1,sK0,sK2,X0_45) = k9_relat_1(sK2,X0_45) ),
    inference(equality_resolution,[status(thm)],[c_275])).

cnf(c_2,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k2_relset_1(X1,X2,X0) = k2_relat_1(X0) ),
    inference(cnf_transformation,[],[f24])).

cnf(c_192,plain,
    ( k2_relset_1(X0,X1,X2) = k2_relat_1(X2)
    | k1_zfmisc_1(k2_zfmisc_1(X0,X1)) != k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))
    | sK2 != X2 ),
    inference(resolution_lifted,[status(thm)],[c_2,c_10])).

cnf(c_193,plain,
    ( k2_relset_1(X0,X1,sK2) = k2_relat_1(sK2)
    | k1_zfmisc_1(k2_zfmisc_1(X0,X1)) != k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)) ),
    inference(unflattening,[status(thm)],[c_192])).

cnf(c_274,plain,
    ( k1_zfmisc_1(k2_zfmisc_1(X0_45,X0_43)) != k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))
    | k2_relset_1(X0_45,X0_43,sK2) = k2_relat_1(sK2) ),
    inference(subtyping,[status(esa)],[c_193])).

cnf(c_371,plain,
    ( k2_relset_1(sK1,sK0,sK2) = k2_relat_1(sK2) ),
    inference(equality_resolution,[status(thm)],[c_274])).

cnf(c_1,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k1_relset_1(X1,X2,X0) = k1_relat_1(X0) ),
    inference(cnf_transformation,[],[f23])).

cnf(c_201,plain,
    ( k1_relset_1(X0,X1,X2) = k1_relat_1(X2)
    | k1_zfmisc_1(k2_zfmisc_1(X0,X1)) != k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))
    | sK2 != X2 ),
    inference(resolution_lifted,[status(thm)],[c_1,c_10])).

cnf(c_202,plain,
    ( k1_relset_1(X0,X1,sK2) = k1_relat_1(sK2)
    | k1_zfmisc_1(k2_zfmisc_1(X0,X1)) != k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)) ),
    inference(unflattening,[status(thm)],[c_201])).

cnf(c_273,plain,
    ( k1_zfmisc_1(k2_zfmisc_1(X0_45,X0_43)) != k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))
    | k1_relset_1(X0_45,X0_43,sK2) = k1_relat_1(sK2) ),
    inference(subtyping,[status(esa)],[c_202])).

cnf(c_355,plain,
    ( k1_relset_1(sK1,sK0,sK2) = k1_relat_1(sK2) ),
    inference(equality_resolution,[status(thm)],[c_273])).

cnf(c_9,negated_conjecture,
    ( k2_relset_1(sK1,sK0,sK2) != k7_relset_1(sK1,sK0,sK2,k8_relset_1(sK1,sK0,sK2,sK0))
    | k1_relset_1(sK1,sK0,sK2) != k8_relset_1(sK1,sK0,sK2,k7_relset_1(sK1,sK0,sK2,sK1)) ),
    inference(cnf_transformation,[],[f32])).

cnf(c_279,negated_conjecture,
    ( k1_relset_1(sK1,sK0,sK2) != k8_relset_1(sK1,sK0,sK2,k7_relset_1(sK1,sK0,sK2,sK1))
    | k2_relset_1(sK1,sK0,sK2) != k7_relset_1(sK1,sK0,sK2,k8_relset_1(sK1,sK0,sK2,sK0)) ),
    inference(subtyping,[status(esa)],[c_9])).

cnf(c_394,plain,
    ( k8_relset_1(sK1,sK0,sK2,k7_relset_1(sK1,sK0,sK2,sK1)) != k1_relat_1(sK2)
    | k7_relset_1(sK1,sK0,sK2,k8_relset_1(sK1,sK0,sK2,sK0)) != k2_relset_1(sK1,sK0,sK2) ),
    inference(demodulation,[status(thm)],[c_355,c_279])).

cnf(c_460,plain,
    ( k8_relset_1(sK1,sK0,sK2,k7_relset_1(sK1,sK0,sK2,sK1)) != k1_relat_1(sK2)
    | k7_relset_1(sK1,sK0,sK2,k8_relset_1(sK1,sK0,sK2,sK0)) != k2_relat_1(sK2) ),
    inference(demodulation,[status(thm)],[c_371,c_394])).

cnf(c_513,plain,
    ( k8_relset_1(sK1,sK0,sK2,k9_relat_1(sK2,sK1)) != k1_relat_1(sK2)
    | k7_relset_1(sK1,sK0,sK2,k8_relset_1(sK1,sK0,sK2,sK0)) != k2_relat_1(sK2) ),
    inference(demodulation,[status(thm)],[c_374,c_460])).

cnf(c_514,plain,
    ( k8_relset_1(sK1,sK0,sK2,k9_relat_1(sK2,sK1)) != k1_relat_1(sK2)
    | k9_relat_1(sK2,k8_relset_1(sK1,sK0,sK2,sK0)) != k2_relat_1(sK2) ),
    inference(demodulation,[status(thm)],[c_513,c_374])).

cnf(c_5,plain,
    ( ~ v1_relat_1(X0)
    | k9_relat_1(X0,k1_relat_1(X0)) = k2_relat_1(X0) ),
    inference(cnf_transformation,[],[f27])).

cnf(c_0,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f22])).

cnf(c_210,plain,
    ( v1_relat_1(X0)
    | k1_zfmisc_1(k2_zfmisc_1(X1,X2)) != k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))
    | sK2 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_0,c_10])).

cnf(c_211,plain,
    ( v1_relat_1(sK2)
    | k1_zfmisc_1(k2_zfmisc_1(X0,X1)) != k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)) ),
    inference(unflattening,[status(thm)],[c_210])).

cnf(c_246,plain,
    ( k9_relat_1(X0,k1_relat_1(X0)) = k2_relat_1(X0)
    | k1_zfmisc_1(k2_zfmisc_1(X1,X2)) != k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))
    | sK2 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_5,c_211])).

cnf(c_247,plain,
    ( k9_relat_1(sK2,k1_relat_1(sK2)) = k2_relat_1(sK2)
    | k1_zfmisc_1(k2_zfmisc_1(X0,X1)) != k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)) ),
    inference(unflattening,[status(thm)],[c_246])).

cnf(c_271,plain,
    ( k1_zfmisc_1(k2_zfmisc_1(X0_45,X0_43)) != k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))
    | k9_relat_1(sK2,k1_relat_1(sK2)) = k2_relat_1(sK2) ),
    inference(subtyping,[status(esa)],[c_247])).

cnf(c_314,plain,
    ( k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)) != k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))
    | k9_relat_1(sK2,k1_relat_1(sK2)) = k2_relat_1(sK2) ),
    inference(instantiation,[status(thm)],[c_271])).

cnf(c_282,plain,
    ( X0_46 = X0_46 ),
    theory(equality)).

cnf(c_356,plain,
    ( k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)) = k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)) ),
    inference(instantiation,[status(thm)],[c_282])).

cnf(c_411,plain,
    ( k9_relat_1(sK2,k1_relat_1(sK2)) = k2_relat_1(sK2) ),
    inference(global_propositional_subsumption,[status(thm)],[c_271,c_314,c_356])).

cnf(c_7,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k8_relset_1(X1,X2,X0,X2) = k1_relset_1(X1,X2,X0) ),
    inference(cnf_transformation,[],[f30])).

cnf(c_165,plain,
    ( k8_relset_1(X0,X1,X2,X1) = k1_relset_1(X0,X1,X2)
    | k1_zfmisc_1(k2_zfmisc_1(X0,X1)) != k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))
    | sK2 != X2 ),
    inference(resolution_lifted,[status(thm)],[c_7,c_10])).

cnf(c_166,plain,
    ( k8_relset_1(X0,X1,sK2,X1) = k1_relset_1(X0,X1,sK2)
    | k1_zfmisc_1(k2_zfmisc_1(X0,X1)) != k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)) ),
    inference(unflattening,[status(thm)],[c_165])).

cnf(c_277,plain,
    ( k1_zfmisc_1(k2_zfmisc_1(X0_45,X0_43)) != k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))
    | k8_relset_1(X0_45,X0_43,sK2,X0_43) = k1_relset_1(X0_45,X0_43,sK2) ),
    inference(subtyping,[status(esa)],[c_166])).

cnf(c_388,plain,
    ( k8_relset_1(sK1,sK0,sK2,sK0) = k1_relset_1(sK1,sK0,sK2) ),
    inference(equality_resolution,[status(thm)],[c_277])).

cnf(c_584,plain,
    ( k8_relset_1(sK1,sK0,sK2,sK0) = k1_relat_1(sK2) ),
    inference(light_normalisation,[status(thm)],[c_388,c_355])).

cnf(c_8,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k7_relset_1(X1,X2,X0,X1) = k2_relset_1(X1,X2,X0) ),
    inference(cnf_transformation,[],[f29])).

cnf(c_156,plain,
    ( k7_relset_1(X0,X1,X2,X0) = k2_relset_1(X0,X1,X2)
    | k1_zfmisc_1(k2_zfmisc_1(X0,X1)) != k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))
    | sK2 != X2 ),
    inference(resolution_lifted,[status(thm)],[c_8,c_10])).

cnf(c_157,plain,
    ( k7_relset_1(X0,X1,sK2,X0) = k2_relset_1(X0,X1,sK2)
    | k1_zfmisc_1(k2_zfmisc_1(X0,X1)) != k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)) ),
    inference(unflattening,[status(thm)],[c_156])).

cnf(c_278,plain,
    ( k1_zfmisc_1(k2_zfmisc_1(X0_45,X0_43)) != k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))
    | k7_relset_1(X0_45,X0_43,sK2,X0_45) = k2_relset_1(X0_45,X0_43,sK2) ),
    inference(subtyping,[status(esa)],[c_157])).

cnf(c_392,plain,
    ( k7_relset_1(sK1,sK0,sK2,sK1) = k2_relset_1(sK1,sK0,sK2) ),
    inference(equality_resolution,[status(thm)],[c_278])).

cnf(c_636,plain,
    ( k7_relset_1(sK1,sK0,sK2,sK1) = k2_relat_1(sK2) ),
    inference(light_normalisation,[status(thm)],[c_392,c_371])).

cnf(c_638,plain,
    ( k9_relat_1(sK2,sK1) = k2_relat_1(sK2) ),
    inference(superposition,[status(thm)],[c_374,c_636])).

cnf(c_722,plain,
    ( k8_relset_1(sK1,sK0,sK2,k2_relat_1(sK2)) != k1_relat_1(sK2)
    | k2_relat_1(sK2) != k2_relat_1(sK2) ),
    inference(light_normalisation,[status(thm)],[c_514,c_411,c_584,c_638])).

cnf(c_723,plain,
    ( k8_relset_1(sK1,sK0,sK2,k2_relat_1(sK2)) != k1_relat_1(sK2) ),
    inference(equality_resolution_simp,[status(thm)],[c_722])).

cnf(c_4,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k8_relset_1(X1,X2,X0,X3) = k10_relat_1(X0,X3) ),
    inference(cnf_transformation,[],[f26])).

cnf(c_174,plain,
    ( k8_relset_1(X0,X1,X2,X3) = k10_relat_1(X2,X3)
    | k1_zfmisc_1(k2_zfmisc_1(X0,X1)) != k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))
    | sK2 != X2 ),
    inference(resolution_lifted,[status(thm)],[c_4,c_10])).

cnf(c_175,plain,
    ( k8_relset_1(X0,X1,sK2,X2) = k10_relat_1(sK2,X2)
    | k1_zfmisc_1(k2_zfmisc_1(X0,X1)) != k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)) ),
    inference(unflattening,[status(thm)],[c_174])).

cnf(c_276,plain,
    ( k1_zfmisc_1(k2_zfmisc_1(X0_45,X0_43)) != k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))
    | k8_relset_1(X0_45,X0_43,sK2,X1_43) = k10_relat_1(sK2,X1_43) ),
    inference(subtyping,[status(esa)],[c_175])).

cnf(c_384,plain,
    ( k8_relset_1(sK1,sK0,sK2,X0_43) = k10_relat_1(sK2,X0_43) ),
    inference(equality_resolution,[status(thm)],[c_276])).

cnf(c_6,plain,
    ( ~ v1_relat_1(X0)
    | k10_relat_1(X0,k2_relat_1(X0)) = k1_relat_1(X0) ),
    inference(cnf_transformation,[],[f28])).

cnf(c_237,plain,
    ( k10_relat_1(X0,k2_relat_1(X0)) = k1_relat_1(X0)
    | k1_zfmisc_1(k2_zfmisc_1(X1,X2)) != k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))
    | sK2 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_6,c_211])).

cnf(c_238,plain,
    ( k10_relat_1(sK2,k2_relat_1(sK2)) = k1_relat_1(sK2)
    | k1_zfmisc_1(k2_zfmisc_1(X0,X1)) != k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)) ),
    inference(unflattening,[status(thm)],[c_237])).

cnf(c_272,plain,
    ( k1_zfmisc_1(k2_zfmisc_1(X0_45,X0_43)) != k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))
    | k10_relat_1(sK2,k2_relat_1(sK2)) = k1_relat_1(sK2) ),
    inference(subtyping,[status(esa)],[c_238])).

cnf(c_313,plain,
    ( k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)) != k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))
    | k10_relat_1(sK2,k2_relat_1(sK2)) = k1_relat_1(sK2) ),
    inference(instantiation,[status(thm)],[c_272])).

cnf(c_456,plain,
    ( k10_relat_1(sK2,k2_relat_1(sK2)) = k1_relat_1(sK2) ),
    inference(global_propositional_subsumption,[status(thm)],[c_272,c_313,c_356])).

cnf(c_724,plain,
    ( k1_relat_1(sK2) != k1_relat_1(sK2) ),
    inference(demodulation,[status(thm)],[c_723,c_384,c_456])).

cnf(c_725,plain,
    ( $false ),
    inference(equality_resolution_simp,[status(thm)],[c_724])).


%------------------------------------------------------------------------------
