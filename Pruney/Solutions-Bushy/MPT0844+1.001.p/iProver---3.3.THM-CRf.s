%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0844+1.001 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n031.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:44:15 EST 2020

% Result     : Theorem 1.25s
% Output     : CNFRefutation 1.25s
% Verified   : 
% Statistics : Number of formulae       :   80 ( 106 expanded)
%              Number of clauses        :   45 (  49 expanded)
%              Number of leaves         :   12 (  20 expanded)
%              Depth                    :   12
%              Number of atoms          :  177 ( 255 expanded)
%              Number of equality atoms :   54 (  78 expanded)
%              Maximal formula depth    :    8 (   4 average)
%              Maximal clause size      :    6 (   2 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f7,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f11,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
     => r1_tarski(X0,X1) ) ),
    inference(unused_predicate_definition_removal,[],[f7])).

fof(f18,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f31,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f8,axiom,(
    ! [X0,X1,X2] :
      ( ( r1_xboole_0(X1,X2)
        & r1_tarski(X0,X1) )
     => r1_xboole_0(X0,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f19,plain,(
    ! [X0,X1,X2] :
      ( r1_xboole_0(X0,X2)
      | ~ r1_xboole_0(X1,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f20,plain,(
    ! [X0,X1,X2] :
      ( r1_xboole_0(X0,X2)
      | ~ r1_xboole_0(X1,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(flattening,[],[f19])).

fof(f32,plain,(
    ! [X2,X0,X1] :
      ( r1_xboole_0(X0,X2)
      | ~ r1_xboole_0(X1,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f9,conjecture,(
    ! [X0,X1,X2,X3] :
      ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X2,X0)))
     => ( r1_xboole_0(X1,X2)
       => k5_relset_1(X2,X0,X3,X1) = k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f10,negated_conjecture,(
    ~ ! [X0,X1,X2,X3] :
        ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X2,X0)))
       => ( r1_xboole_0(X1,X2)
         => k5_relset_1(X2,X0,X3,X1) = k1_xboole_0 ) ) ),
    inference(negated_conjecture,[],[f9])).

fof(f21,plain,(
    ? [X0,X1,X2,X3] :
      ( k5_relset_1(X2,X0,X3,X1) != k1_xboole_0
      & r1_xboole_0(X1,X2)
      & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X2,X0))) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f22,plain,(
    ? [X0,X1,X2,X3] :
      ( k5_relset_1(X2,X0,X3,X1) != k1_xboole_0
      & r1_xboole_0(X1,X2)
      & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X2,X0))) ) ),
    inference(flattening,[],[f21])).

fof(f23,plain,
    ( ? [X0,X1,X2,X3] :
        ( k5_relset_1(X2,X0,X3,X1) != k1_xboole_0
        & r1_xboole_0(X1,X2)
        & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X2,X0))) )
   => ( k5_relset_1(sK2,sK0,sK3,sK1) != k1_xboole_0
      & r1_xboole_0(sK1,sK2)
      & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK2,sK0))) ) ),
    introduced(choice_axiom,[])).

fof(f24,plain,
    ( k5_relset_1(sK2,sK0,sK3,sK1) != k1_xboole_0
    & r1_xboole_0(sK1,sK2)
    & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK2,sK0))) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3])],[f22,f23])).

fof(f33,plain,(
    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK2,sK0))) ),
    inference(cnf_transformation,[],[f24])).

fof(f3,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k1_relset_1(X0,X1,X2) = k1_relat_1(X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f14,plain,(
    ! [X0,X1,X2] :
      ( k1_relset_1(X0,X1,X2) = k1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f27,plain,(
    ! [X2,X0,X1] :
      ( k1_relset_1(X0,X1,X2) = k1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f14])).

fof(f2,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => m1_subset_1(k1_relset_1(X0,X1,X2),k1_zfmisc_1(X0)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f13,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(k1_relset_1(X0,X1,X2),k1_zfmisc_1(X0))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f26,plain,(
    ! [X2,X0,X1] :
      ( m1_subset_1(k1_relset_1(X0,X1,X2),k1_zfmisc_1(X0))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f13])).

fof(f5,axiom,(
    ! [X0,X1] :
      ( r1_xboole_0(X0,X1)
     => r1_xboole_0(X1,X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f16,plain,(
    ! [X0,X1] :
      ( r1_xboole_0(X1,X0)
      | ~ r1_xboole_0(X0,X1) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f29,plain,(
    ! [X0,X1] :
      ( r1_xboole_0(X1,X0)
      | ~ r1_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f16])).

fof(f6,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( r1_xboole_0(X1,k1_relat_1(X0))
         => k7_relat_1(X0,X1) = k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f17,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k7_relat_1(X0,X1) = k1_xboole_0
          | ~ r1_xboole_0(X1,k1_relat_1(X0)) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f30,plain,(
    ! [X0,X1] :
      ( k7_relat_1(X0,X1) = k1_xboole_0
      | ~ r1_xboole_0(X1,k1_relat_1(X0))
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f4,axiom,(
    ! [X0,X1,X2,X3] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k5_relset_1(X0,X1,X2,X3) = k7_relat_1(X2,X3) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f15,plain,(
    ! [X0,X1,X2,X3] :
      ( k5_relset_1(X0,X1,X2,X3) = k7_relat_1(X2,X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f28,plain,(
    ! [X2,X0,X3,X1] :
      ( k5_relset_1(X0,X1,X2,X3) = k7_relat_1(X2,X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f15])).

fof(f1,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => v1_relat_1(X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f12,plain,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f25,plain,(
    ! [X2,X0,X1] :
      ( v1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f12])).

fof(f35,plain,(
    k5_relset_1(sK2,sK0,sK3,sK1) != k1_xboole_0 ),
    inference(cnf_transformation,[],[f24])).

fof(f34,plain,(
    r1_xboole_0(sK1,sK2) ),
    inference(cnf_transformation,[],[f24])).

cnf(c_6,plain,
    ( r1_tarski(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ),
    inference(cnf_transformation,[],[f31])).

cnf(c_7,plain,
    ( ~ r1_tarski(X0,X1)
    | ~ r1_xboole_0(X1,X2)
    | r1_xboole_0(X0,X2) ),
    inference(cnf_transformation,[],[f32])).

cnf(c_135,plain,
    ( ~ r1_xboole_0(X0,X1)
    | r1_xboole_0(X2,X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(X0)) ),
    inference(resolution,[status(thm)],[c_6,c_7])).

cnf(c_234,plain,
    ( ~ r1_xboole_0(X0_43,X1_43)
    | r1_xboole_0(X2_43,X1_43)
    | ~ m1_subset_1(X2_43,k1_zfmisc_1(X0_43)) ),
    inference(subtyping,[status(esa)],[c_135])).

cnf(c_547,plain,
    ( r1_xboole_0(X0_43,sK1)
    | ~ r1_xboole_0(sK2,sK1)
    | ~ m1_subset_1(X0_43,k1_zfmisc_1(sK2)) ),
    inference(instantiation,[status(thm)],[c_234])).

cnf(c_965,plain,
    ( r1_xboole_0(k1_relat_1(sK3),sK1)
    | ~ r1_xboole_0(sK2,sK1)
    | ~ m1_subset_1(k1_relat_1(sK3),k1_zfmisc_1(sK2)) ),
    inference(instantiation,[status(thm)],[c_547])).

cnf(c_10,negated_conjecture,
    ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK2,sK0))) ),
    inference(cnf_transformation,[],[f33])).

cnf(c_235,negated_conjecture,
    ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK2,sK0))) ),
    inference(subtyping,[status(esa)],[c_10])).

cnf(c_443,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK2,sK0))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_235])).

cnf(c_2,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k1_relset_1(X1,X2,X0) = k1_relat_1(X0) ),
    inference(cnf_transformation,[],[f27])).

cnf(c_241,plain,
    ( ~ m1_subset_1(X0_43,k1_zfmisc_1(k2_zfmisc_1(X1_43,X0_45)))
    | k1_relset_1(X1_43,X0_45,X0_43) = k1_relat_1(X0_43) ),
    inference(subtyping,[status(esa)],[c_2])).

cnf(c_438,plain,
    ( k1_relset_1(X0_43,X0_45,X1_43) = k1_relat_1(X1_43)
    | m1_subset_1(X1_43,k1_zfmisc_1(k2_zfmisc_1(X0_43,X0_45))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_241])).

cnf(c_655,plain,
    ( k1_relset_1(sK2,sK0,sK3) = k1_relat_1(sK3) ),
    inference(superposition,[status(thm)],[c_443,c_438])).

cnf(c_1,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | m1_subset_1(k1_relset_1(X1,X2,X0),k1_zfmisc_1(X1)) ),
    inference(cnf_transformation,[],[f26])).

cnf(c_242,plain,
    ( ~ m1_subset_1(X0_43,k1_zfmisc_1(k2_zfmisc_1(X1_43,X0_45)))
    | m1_subset_1(k1_relset_1(X1_43,X0_45,X0_43),k1_zfmisc_1(X1_43)) ),
    inference(subtyping,[status(esa)],[c_1])).

cnf(c_437,plain,
    ( m1_subset_1(X0_43,k1_zfmisc_1(k2_zfmisc_1(X1_43,X0_45))) != iProver_top
    | m1_subset_1(k1_relset_1(X1_43,X0_45,X0_43),k1_zfmisc_1(X1_43)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_242])).

cnf(c_779,plain,
    ( m1_subset_1(k1_relat_1(sK3),k1_zfmisc_1(sK2)) = iProver_top
    | m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK2,sK0))) != iProver_top ),
    inference(superposition,[status(thm)],[c_655,c_437])).

cnf(c_780,plain,
    ( m1_subset_1(k1_relat_1(sK3),k1_zfmisc_1(sK2))
    | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK2,sK0))) ),
    inference(predicate_to_equality_rev,[status(thm)],[c_779])).

cnf(c_4,plain,
    ( ~ r1_xboole_0(X0,X1)
    | r1_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f29])).

cnf(c_239,plain,
    ( ~ r1_xboole_0(X0_43,X1_43)
    | r1_xboole_0(X1_43,X0_43) ),
    inference(subtyping,[status(esa)],[c_4])).

cnf(c_612,plain,
    ( ~ r1_xboole_0(X0_43,sK1)
    | r1_xboole_0(sK1,X0_43) ),
    inference(instantiation,[status(thm)],[c_239])).

cnf(c_760,plain,
    ( ~ r1_xboole_0(k1_relat_1(sK3),sK1)
    | r1_xboole_0(sK1,k1_relat_1(sK3)) ),
    inference(instantiation,[status(thm)],[c_612])).

cnf(c_5,plain,
    ( ~ r1_xboole_0(X0,k1_relat_1(X1))
    | ~ v1_relat_1(X1)
    | k7_relat_1(X1,X0) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f30])).

cnf(c_238,plain,
    ( ~ r1_xboole_0(X0_43,k1_relat_1(X1_43))
    | ~ v1_relat_1(X1_43)
    | k7_relat_1(X1_43,X0_43) = k1_xboole_0 ),
    inference(subtyping,[status(esa)],[c_5])).

cnf(c_555,plain,
    ( ~ r1_xboole_0(X0_43,k1_relat_1(sK3))
    | ~ v1_relat_1(sK3)
    | k7_relat_1(sK3,X0_43) = k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_238])).

cnf(c_629,plain,
    ( ~ r1_xboole_0(sK1,k1_relat_1(sK3))
    | ~ v1_relat_1(sK3)
    | k7_relat_1(sK3,sK1) = k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_555])).

cnf(c_249,plain,
    ( X0_46 != X1_46
    | X2_46 != X1_46
    | X2_46 = X0_46 ),
    theory(equality)).

cnf(c_607,plain,
    ( k7_relat_1(sK3,sK1) != X0_46
    | k1_xboole_0 != X0_46
    | k1_xboole_0 = k7_relat_1(sK3,sK1) ),
    inference(instantiation,[status(thm)],[c_249])).

cnf(c_608,plain,
    ( k7_relat_1(sK3,sK1) != k1_xboole_0
    | k1_xboole_0 = k7_relat_1(sK3,sK1)
    | k1_xboole_0 != k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_607])).

cnf(c_3,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k5_relset_1(X1,X2,X0,X3) = k7_relat_1(X0,X3) ),
    inference(cnf_transformation,[],[f28])).

cnf(c_240,plain,
    ( ~ m1_subset_1(X0_43,k1_zfmisc_1(k2_zfmisc_1(X1_43,X0_45)))
    | k5_relset_1(X1_43,X0_45,X0_43,X2_43) = k7_relat_1(X0_43,X2_43) ),
    inference(subtyping,[status(esa)],[c_3])).

cnf(c_534,plain,
    ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK2,sK0)))
    | k5_relset_1(sK2,sK0,sK3,X0_43) = k7_relat_1(sK3,X0_43) ),
    inference(instantiation,[status(thm)],[c_240])).

cnf(c_579,plain,
    ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK2,sK0)))
    | k5_relset_1(sK2,sK0,sK3,sK1) = k7_relat_1(sK3,sK1) ),
    inference(instantiation,[status(thm)],[c_534])).

cnf(c_517,plain,
    ( k5_relset_1(sK2,sK0,sK3,sK1) != X0_46
    | k5_relset_1(sK2,sK0,sK3,sK1) = k1_xboole_0
    | k1_xboole_0 != X0_46 ),
    inference(instantiation,[status(thm)],[c_249])).

cnf(c_578,plain,
    ( k5_relset_1(sK2,sK0,sK3,sK1) != k7_relat_1(sK3,sK1)
    | k5_relset_1(sK2,sK0,sK3,sK1) = k1_xboole_0
    | k1_xboole_0 != k7_relat_1(sK3,sK1) ),
    inference(instantiation,[status(thm)],[c_517])).

cnf(c_0,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f25])).

cnf(c_243,plain,
    ( ~ m1_subset_1(X0_43,k1_zfmisc_1(k2_zfmisc_1(X1_43,X0_45)))
    | v1_relat_1(X0_43) ),
    inference(subtyping,[status(esa)],[c_0])).

cnf(c_506,plain,
    ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK2,sK0)))
    | v1_relat_1(sK3) ),
    inference(instantiation,[status(thm)],[c_243])).

cnf(c_503,plain,
    ( ~ r1_xboole_0(sK1,sK2)
    | r1_xboole_0(sK2,sK1) ),
    inference(instantiation,[status(thm)],[c_239])).

cnf(c_8,negated_conjecture,
    ( k5_relset_1(sK2,sK0,sK3,sK1) != k1_xboole_0 ),
    inference(cnf_transformation,[],[f35])).

cnf(c_237,negated_conjecture,
    ( k5_relset_1(sK2,sK0,sK3,sK1) != k1_xboole_0 ),
    inference(subtyping,[status(esa)],[c_8])).

cnf(c_247,plain,
    ( X0_46 = X0_46 ),
    theory(equality)).

cnf(c_263,plain,
    ( k1_xboole_0 = k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_247])).

cnf(c_9,negated_conjecture,
    ( r1_xboole_0(sK1,sK2) ),
    inference(cnf_transformation,[],[f34])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_965,c_780,c_760,c_629,c_608,c_579,c_578,c_506,c_503,c_237,c_263,c_9,c_10])).


%------------------------------------------------------------------------------
