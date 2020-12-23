%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n017.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 11:55:43 EST 2020

% Result     : Theorem 3.44s
% Output     : CNFRefutation 3.44s
% Verified   : 
% Statistics : Number of formulae       :   92 ( 249 expanded)
%              Number of clauses        :   50 (  91 expanded)
%              Number of leaves         :   15 (  50 expanded)
%              Depth                    :   16
%              Number of atoms          :  230 ( 662 expanded)
%              Number of equality atoms :   52 (  75 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal clause size      :    6 (   2 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
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

fof(f38,plain,(
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

fof(f40,plain,(
    ! [X2,X0,X3,X1] :
      ( r2_relset_1(X0,X1,X2,X3)
      | X2 != X3
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f44,plain,(
    ! [X0,X3,X1] :
      ( r2_relset_1(X0,X1,X3,X3)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(equality_resolution,[],[f40])).

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

fof(f43,plain,(
    ~ r2_relset_1(sK1,sK0,k5_relset_1(sK1,sK0,sK3,sK2),sK3) ),
    inference(cnf_transformation,[],[f28])).

fof(f41,plain,(
    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) ),
    inference(cnf_transformation,[],[f28])).

fof(f42,plain,(
    r1_tarski(sK1,sK2) ),
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

fof(f4,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(X0))
         => v1_relat_1(X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f16,plain,(
    ! [X0] :
      ( ! [X1] :
          ( v1_relat_1(X1)
          | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f34,plain,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f16])).

fof(f33,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f5,axiom,(
    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f35,plain,(
    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1)) ),
    inference(cnf_transformation,[],[f5])).

fof(f1,axiom,(
    ! [X0,X1,X2] :
      ( ( r1_tarski(X1,X2)
        & r1_tarski(X0,X1) )
     => r1_tarski(X0,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f13,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,X2)
      | ~ r1_tarski(X1,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f14,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,X2)
      | ~ r1_tarski(X1,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(flattening,[],[f13])).

fof(f29,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(X0,X2)
      | ~ r1_tarski(X1,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f14])).

fof(f2,axiom,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,X1)
     => ( r1_tarski(k2_zfmisc_1(X2,X0),k2_zfmisc_1(X2,X1))
        & r1_tarski(k2_zfmisc_1(X0,X2),k2_zfmisc_1(X1,X2)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f15,plain,(
    ! [X0,X1,X2] :
      ( ( r1_tarski(k2_zfmisc_1(X2,X0),k2_zfmisc_1(X2,X1))
        & r1_tarski(k2_zfmisc_1(X0,X2),k2_zfmisc_1(X1,X2)) )
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f30,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(k2_zfmisc_1(X0,X2),k2_zfmisc_1(X1,X2))
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f15])).

fof(f7,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => ( v5_relat_1(X2,X1)
        & v4_relat_1(X2,X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

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

fof(f37,plain,(
    ! [X2,X0,X1] :
      ( v4_relat_1(X2,X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f6,axiom,(
    ! [X0,X1] :
      ( ( v4_relat_1(X1,X0)
        & v1_relat_1(X1) )
     => k7_relat_1(X1,X0) = X1 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f17,plain,(
    ! [X0,X1] :
      ( k7_relat_1(X1,X0) = X1
      | ~ v4_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f18,plain,(
    ! [X0,X1] :
      ( k7_relat_1(X1,X0) = X1
      | ~ v4_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f17])).

fof(f36,plain,(
    ! [X0,X1] :
      ( k7_relat_1(X1,X0) = X1
      | ~ v4_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f18])).

cnf(c_564,plain,
    ( ~ m1_subset_1(X0,X1)
    | m1_subset_1(X2,X3)
    | X2 != X0
    | X3 != X1 ),
    theory(equality)).

cnf(c_559,plain,
    ( X0 = X0 ),
    theory(equality)).

cnf(c_2857,plain,
    ( ~ m1_subset_1(X0,X1)
    | m1_subset_1(X2,X1)
    | X2 != X0 ),
    inference(resolution,[status(thm)],[c_564,c_559])).

cnf(c_9,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k5_relset_1(X1,X2,X0,X3) = k7_relat_1(X0,X3) ),
    inference(cnf_transformation,[],[f38])).

cnf(c_3391,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | m1_subset_1(k5_relset_1(X1,X2,X0,X3),X4)
    | ~ m1_subset_1(k7_relat_1(X0,X3),X4) ),
    inference(resolution,[status(thm)],[c_2857,c_9])).

cnf(c_10,plain,
    ( r2_relset_1(X0,X1,X2,X2)
    | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ),
    inference(cnf_transformation,[],[f44])).

cnf(c_12,negated_conjecture,
    ( ~ r2_relset_1(sK1,sK0,k5_relset_1(sK1,sK0,sK3,sK2),sK3) ),
    inference(cnf_transformation,[],[f43])).

cnf(c_222,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k5_relset_1(sK1,sK0,sK3,sK2) != X0
    | sK3 != X0
    | sK0 != X2
    | sK1 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_10,c_12])).

cnf(c_223,plain,
    ( ~ m1_subset_1(k5_relset_1(sK1,sK0,sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
    | sK3 != k5_relset_1(sK1,sK0,sK3,sK2) ),
    inference(unflattening,[status(thm)],[c_222])).

cnf(c_19015,plain,
    ( ~ m1_subset_1(k7_relat_1(sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
    | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
    | sK3 != k5_relset_1(sK1,sK0,sK3,sK2) ),
    inference(resolution,[status(thm)],[c_3391,c_223])).

cnf(c_14,negated_conjecture,
    ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) ),
    inference(cnf_transformation,[],[f41])).

cnf(c_13,negated_conjecture,
    ( r1_tarski(sK1,sK2) ),
    inference(cnf_transformation,[],[f42])).

cnf(c_4,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | r1_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f32])).

cnf(c_998,plain,
    ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
    | r1_tarski(sK3,k2_zfmisc_1(sK1,sK0)) ),
    inference(instantiation,[status(thm)],[c_4])).

cnf(c_5,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | ~ v1_relat_1(X1)
    | v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f34])).

cnf(c_3,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(X1))
    | ~ r1_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f33])).

cnf(c_117,plain,
    ( ~ r1_tarski(X0,X1)
    | m1_subset_1(X0,k1_zfmisc_1(X1)) ),
    inference(prop_impl,[status(thm)],[c_3])).

cnf(c_118,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(X1))
    | ~ r1_tarski(X0,X1) ),
    inference(renaming,[status(thm)],[c_117])).

cnf(c_146,plain,
    ( ~ r1_tarski(X0,X1)
    | ~ v1_relat_1(X1)
    | v1_relat_1(X0) ),
    inference(bin_hyper_res,[status(thm)],[c_5,c_118])).

cnf(c_1077,plain,
    ( r1_tarski(sK3,k2_zfmisc_1(sK1,sK0)) ),
    inference(resolution,[status(thm)],[c_4,c_14])).

cnf(c_1093,plain,
    ( ~ v1_relat_1(k2_zfmisc_1(sK1,sK0))
    | v1_relat_1(sK3) ),
    inference(resolution,[status(thm)],[c_146,c_1077])).

cnf(c_6,plain,
    ( v1_relat_1(k2_zfmisc_1(X0,X1)) ),
    inference(cnf_transformation,[],[f35])).

cnf(c_1221,plain,
    ( v1_relat_1(sK3) ),
    inference(forward_subsumption_resolution,[status(thm)],[c_1093,c_6])).

cnf(c_0,plain,
    ( ~ r1_tarski(X0,X1)
    | ~ r1_tarski(X2,X0)
    | r1_tarski(X2,X1) ),
    inference(cnf_transformation,[],[f29])).

cnf(c_1120,plain,
    ( ~ r1_tarski(k2_zfmisc_1(sK1,sK0),X0)
    | r1_tarski(sK3,X0)
    | ~ r1_tarski(sK3,k2_zfmisc_1(sK1,sK0)) ),
    inference(instantiation,[status(thm)],[c_0])).

cnf(c_1303,plain,
    ( ~ r1_tarski(k2_zfmisc_1(sK1,sK0),k2_zfmisc_1(sK2,sK0))
    | r1_tarski(sK3,k2_zfmisc_1(sK2,sK0))
    | ~ r1_tarski(sK3,k2_zfmisc_1(sK1,sK0)) ),
    inference(instantiation,[status(thm)],[c_1120])).

cnf(c_2,plain,
    ( ~ r1_tarski(X0,X1)
    | r1_tarski(k2_zfmisc_1(X0,X2),k2_zfmisc_1(X1,X2)) ),
    inference(cnf_transformation,[],[f30])).

cnf(c_1033,plain,
    ( r1_tarski(k2_zfmisc_1(sK1,X0),k2_zfmisc_1(sK2,X0))
    | ~ r1_tarski(sK1,sK2) ),
    inference(instantiation,[status(thm)],[c_2])).

cnf(c_1304,plain,
    ( r1_tarski(k2_zfmisc_1(sK1,sK0),k2_zfmisc_1(sK2,sK0))
    | ~ r1_tarski(sK1,sK2) ),
    inference(instantiation,[status(thm)],[c_1033])).

cnf(c_1512,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK2,sK0)))
    | ~ r1_tarski(sK3,k2_zfmisc_1(sK2,sK0)) ),
    inference(instantiation,[status(thm)],[c_3])).

cnf(c_897,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_14])).

cnf(c_899,plain,
    ( k5_relset_1(X0,X1,X2,X3) = k7_relat_1(X2,X3)
    | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_9])).

cnf(c_1802,plain,
    ( k5_relset_1(sK1,sK0,sK3,X0) = k7_relat_1(sK3,X0) ),
    inference(superposition,[status(thm)],[c_897,c_899])).

cnf(c_894,plain,
    ( sK3 != k5_relset_1(sK1,sK0,sK3,sK2)
    | m1_subset_1(k5_relset_1(sK1,sK0,sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_223])).

cnf(c_1954,plain,
    ( k7_relat_1(sK3,sK2) != sK3
    | m1_subset_1(k7_relat_1(sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) != iProver_top ),
    inference(demodulation,[status(thm)],[c_1802,c_894])).

cnf(c_1955,plain,
    ( ~ m1_subset_1(k7_relat_1(sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
    | k7_relat_1(sK3,sK2) != sK3 ),
    inference(predicate_to_equality_rev,[status(thm)],[c_1954])).

cnf(c_8,plain,
    ( v4_relat_1(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) ),
    inference(cnf_transformation,[],[f37])).

cnf(c_7,plain,
    ( ~ v4_relat_1(X0,X1)
    | ~ v1_relat_1(X0)
    | k7_relat_1(X0,X1) = X0 ),
    inference(cnf_transformation,[],[f36])).

cnf(c_202,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ v1_relat_1(X0)
    | k7_relat_1(X0,X1) = X0 ),
    inference(resolution,[status(thm)],[c_8,c_7])).

cnf(c_1671,plain,
    ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
    | ~ v1_relat_1(sK3)
    | k7_relat_1(sK3,X0) = sK3 ),
    inference(instantiation,[status(thm)],[c_202])).

cnf(c_2631,plain,
    ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK2,sK0)))
    | ~ v1_relat_1(sK3)
    | k7_relat_1(sK3,sK2) = sK3 ),
    inference(instantiation,[status(thm)],[c_1671])).

cnf(c_19399,plain,
    ( ~ m1_subset_1(k7_relat_1(sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) ),
    inference(global_propositional_subsumption,[status(thm)],[c_19015,c_14,c_13,c_998,c_1221,c_1303,c_1304,c_1512,c_1955,c_2631])).

cnf(c_19942,plain,
    ( ~ r1_tarski(k7_relat_1(sK3,sK2),k2_zfmisc_1(sK1,sK0)) ),
    inference(resolution,[status(thm)],[c_19399,c_3])).

cnf(c_562,plain,
    ( X0 != X1
    | X2 != X3
    | k2_zfmisc_1(X0,X2) = k2_zfmisc_1(X1,X3) ),
    theory(equality)).

cnf(c_561,plain,
    ( ~ r1_tarski(X0,X1)
    | r1_tarski(X2,X3)
    | X2 != X0
    | X3 != X1 ),
    theory(equality)).

cnf(c_3016,plain,
    ( ~ r1_tarski(X0,k2_zfmisc_1(X1,X2))
    | r1_tarski(X3,k2_zfmisc_1(X4,X5))
    | X5 != X2
    | X4 != X1
    | X3 != X0 ),
    inference(resolution,[status(thm)],[c_562,c_561])).

cnf(c_10326,plain,
    ( r1_tarski(X0,k2_zfmisc_1(X1,X2))
    | X0 != sK3
    | X2 != sK0
    | X1 != sK1 ),
    inference(resolution,[status(thm)],[c_3016,c_1077])).

cnf(c_20689,plain,
    ( k7_relat_1(sK3,sK2) != sK3
    | sK0 != sK0
    | sK1 != sK1 ),
    inference(resolution,[status(thm)],[c_19942,c_10326])).

cnf(c_20690,plain,
    ( k7_relat_1(sK3,sK2) != sK3 ),
    inference(equality_resolution_simp,[status(thm)],[c_20689])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_20690,c_2631,c_1512,c_1304,c_1303,c_1221,c_998,c_13,c_14])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : iproveropt_run.sh %d %s
% 0.13/0.34  % Computer   : n017.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 20:29:16 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running in FOF mode
% 3.44/0.98  % SZS status Started for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.44/0.98  
% 3.44/0.98  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 3.44/0.98  
% 3.44/0.98  ------  iProver source info
% 3.44/0.98  
% 3.44/0.98  git: date: 2020-06-30 10:37:57 +0100
% 3.44/0.98  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 3.44/0.98  git: non_committed_changes: false
% 3.44/0.98  git: last_make_outside_of_git: false
% 3.44/0.98  
% 3.44/0.98  ------ 
% 3.44/0.98  ------ Parsing...
% 3.44/0.98  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 3.44/0.98  
% 3.44/0.98  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe:1:0s pe:2:0s pe_e  sf_s  rm: 2 0s  sf_e  pe_s  pe_e 
% 3.44/0.98  
% 3.44/0.98  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 3.44/0.98  
% 3.44/0.98  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 3.44/0.98  ------ Proving...
% 3.44/0.98  ------ Problem Properties 
% 3.44/0.98  
% 3.44/0.98  
% 3.44/0.98  clauses                                 12
% 3.44/0.98  conjectures                             2
% 3.44/0.98  EPR                                     3
% 3.44/0.98  Horn                                    12
% 3.44/0.98  unary                                   3
% 3.44/0.98  binary                                  6
% 3.44/0.98  lits                                    24
% 3.44/0.98  lits eq                                 3
% 3.44/0.99  fd_pure                                 0
% 3.44/0.99  fd_pseudo                               0
% 3.44/0.99  fd_cond                                 0
% 3.44/0.99  fd_pseudo_cond                          0
% 3.44/0.99  AC symbols                              0
% 3.44/0.99  
% 3.44/0.99  ------ Input Options Time Limit: Unbounded
% 3.44/0.99  
% 3.44/0.99  
% 3.44/0.99  ------ 
% 3.44/0.99  Current options:
% 3.44/0.99  ------ 
% 3.44/0.99  
% 3.44/0.99  
% 3.44/0.99  
% 3.44/0.99  
% 3.44/0.99  ------ Proving...
% 3.44/0.99  
% 3.44/0.99  
% 3.44/0.99  % SZS status Theorem for theBenchmark.p
% 3.44/0.99  
% 3.44/0.99  % SZS output start CNFRefutation for theBenchmark.p
% 3.44/0.99  
% 3.44/0.99  fof(f8,axiom,(
% 3.44/0.99    ! [X0,X1,X2,X3] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k7_relat_1(X2,X3) = k5_relset_1(X0,X1,X2,X3))),
% 3.44/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.44/0.99  
% 3.44/0.99  fof(f20,plain,(
% 3.44/0.99    ! [X0,X1,X2,X3] : (k7_relat_1(X2,X3) = k5_relset_1(X0,X1,X2,X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 3.44/0.99    inference(ennf_transformation,[],[f8])).
% 3.44/0.99  
% 3.44/0.99  fof(f38,plain,(
% 3.44/0.99    ( ! [X2,X0,X3,X1] : (k7_relat_1(X2,X3) = k5_relset_1(X0,X1,X2,X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 3.44/0.99    inference(cnf_transformation,[],[f20])).
% 3.44/0.99  
% 3.44/0.99  fof(f9,axiom,(
% 3.44/0.99    ! [X0,X1,X2,X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) => (r2_relset_1(X0,X1,X2,X3) <=> X2 = X3))),
% 3.44/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.44/0.99  
% 3.44/0.99  fof(f21,plain,(
% 3.44/0.99    ! [X0,X1,X2,X3] : ((r2_relset_1(X0,X1,X2,X3) <=> X2 = X3) | (~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))))),
% 3.44/0.99    inference(ennf_transformation,[],[f9])).
% 3.44/0.99  
% 3.44/0.99  fof(f22,plain,(
% 3.44/0.99    ! [X0,X1,X2,X3] : ((r2_relset_1(X0,X1,X2,X3) <=> X2 = X3) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 3.44/0.99    inference(flattening,[],[f21])).
% 3.44/0.99  
% 3.44/0.99  fof(f26,plain,(
% 3.44/0.99    ! [X0,X1,X2,X3] : (((r2_relset_1(X0,X1,X2,X3) | X2 != X3) & (X2 = X3 | ~r2_relset_1(X0,X1,X2,X3))) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 3.44/0.99    inference(nnf_transformation,[],[f22])).
% 3.44/0.99  
% 3.44/0.99  fof(f40,plain,(
% 3.44/0.99    ( ! [X2,X0,X3,X1] : (r2_relset_1(X0,X1,X2,X3) | X2 != X3 | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 3.44/0.99    inference(cnf_transformation,[],[f26])).
% 3.44/0.99  
% 3.44/0.99  fof(f44,plain,(
% 3.44/0.99    ( ! [X0,X3,X1] : (r2_relset_1(X0,X1,X3,X3) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 3.44/0.99    inference(equality_resolution,[],[f40])).
% 3.44/0.99  
% 3.44/0.99  fof(f10,conjecture,(
% 3.44/0.99    ! [X0,X1,X2,X3] : (m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) => (r1_tarski(X1,X2) => r2_relset_1(X1,X0,k5_relset_1(X1,X0,X3,X2),X3)))),
% 3.44/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.44/0.99  
% 3.44/0.99  fof(f11,negated_conjecture,(
% 3.44/0.99    ~! [X0,X1,X2,X3] : (m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) => (r1_tarski(X1,X2) => r2_relset_1(X1,X0,k5_relset_1(X1,X0,X3,X2),X3)))),
% 3.44/0.99    inference(negated_conjecture,[],[f10])).
% 3.44/0.99  
% 3.44/0.99  fof(f23,plain,(
% 3.44/0.99    ? [X0,X1,X2,X3] : ((~r2_relset_1(X1,X0,k5_relset_1(X1,X0,X3,X2),X3) & r1_tarski(X1,X2)) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))))),
% 3.44/0.99    inference(ennf_transformation,[],[f11])).
% 3.44/0.99  
% 3.44/0.99  fof(f24,plain,(
% 3.44/0.99    ? [X0,X1,X2,X3] : (~r2_relset_1(X1,X0,k5_relset_1(X1,X0,X3,X2),X3) & r1_tarski(X1,X2) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))))),
% 3.44/0.99    inference(flattening,[],[f23])).
% 3.44/0.99  
% 3.44/0.99  fof(f27,plain,(
% 3.44/0.99    ? [X0,X1,X2,X3] : (~r2_relset_1(X1,X0,k5_relset_1(X1,X0,X3,X2),X3) & r1_tarski(X1,X2) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0)))) => (~r2_relset_1(sK1,sK0,k5_relset_1(sK1,sK0,sK3,sK2),sK3) & r1_tarski(sK1,sK2) & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))))),
% 3.44/0.99    introduced(choice_axiom,[])).
% 3.44/0.99  
% 3.44/0.99  fof(f28,plain,(
% 3.44/0.99    ~r2_relset_1(sK1,sK0,k5_relset_1(sK1,sK0,sK3,sK2),sK3) & r1_tarski(sK1,sK2) & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))),
% 3.44/0.99    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3])],[f24,f27])).
% 3.44/0.99  
% 3.44/0.99  fof(f43,plain,(
% 3.44/0.99    ~r2_relset_1(sK1,sK0,k5_relset_1(sK1,sK0,sK3,sK2),sK3)),
% 3.44/0.99    inference(cnf_transformation,[],[f28])).
% 3.44/0.99  
% 3.44/0.99  fof(f41,plain,(
% 3.44/0.99    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))),
% 3.44/0.99    inference(cnf_transformation,[],[f28])).
% 3.44/0.99  
% 3.44/0.99  fof(f42,plain,(
% 3.44/0.99    r1_tarski(sK1,sK2)),
% 3.44/0.99    inference(cnf_transformation,[],[f28])).
% 3.44/0.99  
% 3.44/0.99  fof(f3,axiom,(
% 3.44/0.99    ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) <=> r1_tarski(X0,X1))),
% 3.44/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.44/0.99  
% 3.44/0.99  fof(f25,plain,(
% 3.44/0.99    ! [X0,X1] : ((m1_subset_1(X0,k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1)) & (r1_tarski(X0,X1) | ~m1_subset_1(X0,k1_zfmisc_1(X1))))),
% 3.44/0.99    inference(nnf_transformation,[],[f3])).
% 3.44/0.99  
% 3.44/0.99  fof(f32,plain,(
% 3.44/0.99    ( ! [X0,X1] : (r1_tarski(X0,X1) | ~m1_subset_1(X0,k1_zfmisc_1(X1))) )),
% 3.44/0.99    inference(cnf_transformation,[],[f25])).
% 3.44/0.99  
% 3.44/0.99  fof(f4,axiom,(
% 3.44/0.99    ! [X0] : (v1_relat_1(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => v1_relat_1(X1)))),
% 3.44/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.44/0.99  
% 3.44/0.99  fof(f16,plain,(
% 3.44/0.99    ! [X0] : (! [X1] : (v1_relat_1(X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) | ~v1_relat_1(X0))),
% 3.44/0.99    inference(ennf_transformation,[],[f4])).
% 3.44/0.99  
% 3.44/0.99  fof(f34,plain,(
% 3.44/0.99    ( ! [X0,X1] : (v1_relat_1(X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0)) | ~v1_relat_1(X0)) )),
% 3.44/0.99    inference(cnf_transformation,[],[f16])).
% 3.44/0.99  
% 3.44/0.99  fof(f33,plain,(
% 3.44/0.99    ( ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1)) )),
% 3.44/0.99    inference(cnf_transformation,[],[f25])).
% 3.44/0.99  
% 3.44/0.99  fof(f5,axiom,(
% 3.44/0.99    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1))),
% 3.44/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.44/0.99  
% 3.44/0.99  fof(f35,plain,(
% 3.44/0.99    ( ! [X0,X1] : (v1_relat_1(k2_zfmisc_1(X0,X1))) )),
% 3.44/0.99    inference(cnf_transformation,[],[f5])).
% 3.44/0.99  
% 3.44/0.99  fof(f1,axiom,(
% 3.44/0.99    ! [X0,X1,X2] : ((r1_tarski(X1,X2) & r1_tarski(X0,X1)) => r1_tarski(X0,X2))),
% 3.44/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.44/0.99  
% 3.44/0.99  fof(f13,plain,(
% 3.44/0.99    ! [X0,X1,X2] : (r1_tarski(X0,X2) | (~r1_tarski(X1,X2) | ~r1_tarski(X0,X1)))),
% 3.44/0.99    inference(ennf_transformation,[],[f1])).
% 3.44/0.99  
% 3.44/0.99  fof(f14,plain,(
% 3.44/0.99    ! [X0,X1,X2] : (r1_tarski(X0,X2) | ~r1_tarski(X1,X2) | ~r1_tarski(X0,X1))),
% 3.44/0.99    inference(flattening,[],[f13])).
% 3.44/0.99  
% 3.44/0.99  fof(f29,plain,(
% 3.44/0.99    ( ! [X2,X0,X1] : (r1_tarski(X0,X2) | ~r1_tarski(X1,X2) | ~r1_tarski(X0,X1)) )),
% 3.44/0.99    inference(cnf_transformation,[],[f14])).
% 3.44/0.99  
% 3.44/0.99  fof(f2,axiom,(
% 3.44/0.99    ! [X0,X1,X2] : (r1_tarski(X0,X1) => (r1_tarski(k2_zfmisc_1(X2,X0),k2_zfmisc_1(X2,X1)) & r1_tarski(k2_zfmisc_1(X0,X2),k2_zfmisc_1(X1,X2))))),
% 3.44/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.44/0.99  
% 3.44/0.99  fof(f15,plain,(
% 3.44/0.99    ! [X0,X1,X2] : ((r1_tarski(k2_zfmisc_1(X2,X0),k2_zfmisc_1(X2,X1)) & r1_tarski(k2_zfmisc_1(X0,X2),k2_zfmisc_1(X1,X2))) | ~r1_tarski(X0,X1))),
% 3.44/0.99    inference(ennf_transformation,[],[f2])).
% 3.44/0.99  
% 3.44/0.99  fof(f30,plain,(
% 3.44/0.99    ( ! [X2,X0,X1] : (r1_tarski(k2_zfmisc_1(X0,X2),k2_zfmisc_1(X1,X2)) | ~r1_tarski(X0,X1)) )),
% 3.44/0.99    inference(cnf_transformation,[],[f15])).
% 3.44/0.99  
% 3.44/0.99  fof(f7,axiom,(
% 3.44/0.99    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => (v5_relat_1(X2,X1) & v4_relat_1(X2,X0)))),
% 3.44/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.44/0.99  
% 3.44/0.99  fof(f12,plain,(
% 3.44/0.99    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => v4_relat_1(X2,X0))),
% 3.44/0.99    inference(pure_predicate_removal,[],[f7])).
% 3.44/0.99  
% 3.44/0.99  fof(f19,plain,(
% 3.44/0.99    ! [X0,X1,X2] : (v4_relat_1(X2,X0) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 3.44/0.99    inference(ennf_transformation,[],[f12])).
% 3.44/0.99  
% 3.44/0.99  fof(f37,plain,(
% 3.44/0.99    ( ! [X2,X0,X1] : (v4_relat_1(X2,X0) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 3.44/0.99    inference(cnf_transformation,[],[f19])).
% 3.44/0.99  
% 3.44/0.99  fof(f6,axiom,(
% 3.44/0.99    ! [X0,X1] : ((v4_relat_1(X1,X0) & v1_relat_1(X1)) => k7_relat_1(X1,X0) = X1)),
% 3.44/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.44/0.99  
% 3.44/0.99  fof(f17,plain,(
% 3.44/0.99    ! [X0,X1] : (k7_relat_1(X1,X0) = X1 | (~v4_relat_1(X1,X0) | ~v1_relat_1(X1)))),
% 3.44/0.99    inference(ennf_transformation,[],[f6])).
% 3.44/0.99  
% 3.44/0.99  fof(f18,plain,(
% 3.44/0.99    ! [X0,X1] : (k7_relat_1(X1,X0) = X1 | ~v4_relat_1(X1,X0) | ~v1_relat_1(X1))),
% 3.44/0.99    inference(flattening,[],[f17])).
% 3.44/0.99  
% 3.44/0.99  fof(f36,plain,(
% 3.44/0.99    ( ! [X0,X1] : (k7_relat_1(X1,X0) = X1 | ~v4_relat_1(X1,X0) | ~v1_relat_1(X1)) )),
% 3.44/0.99    inference(cnf_transformation,[],[f18])).
% 3.44/0.99  
% 3.44/0.99  cnf(c_564,plain,
% 3.44/0.99      ( ~ m1_subset_1(X0,X1) | m1_subset_1(X2,X3) | X2 != X0 | X3 != X1 ),
% 3.44/0.99      theory(equality) ).
% 3.44/0.99  
% 3.44/0.99  cnf(c_559,plain,( X0 = X0 ),theory(equality) ).
% 3.44/0.99  
% 3.44/0.99  cnf(c_2857,plain,
% 3.44/0.99      ( ~ m1_subset_1(X0,X1) | m1_subset_1(X2,X1) | X2 != X0 ),
% 3.44/0.99      inference(resolution,[status(thm)],[c_564,c_559]) ).
% 3.44/0.99  
% 3.44/0.99  cnf(c_9,plain,
% 3.44/0.99      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.44/0.99      | k5_relset_1(X1,X2,X0,X3) = k7_relat_1(X0,X3) ),
% 3.44/0.99      inference(cnf_transformation,[],[f38]) ).
% 3.44/0.99  
% 3.44/0.99  cnf(c_3391,plain,
% 3.44/0.99      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.44/0.99      | m1_subset_1(k5_relset_1(X1,X2,X0,X3),X4)
% 3.44/0.99      | ~ m1_subset_1(k7_relat_1(X0,X3),X4) ),
% 3.44/0.99      inference(resolution,[status(thm)],[c_2857,c_9]) ).
% 3.44/0.99  
% 3.44/0.99  cnf(c_10,plain,
% 3.44/0.99      ( r2_relset_1(X0,X1,X2,X2)
% 3.44/0.99      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ),
% 3.44/0.99      inference(cnf_transformation,[],[f44]) ).
% 3.44/0.99  
% 3.44/0.99  cnf(c_12,negated_conjecture,
% 3.44/0.99      ( ~ r2_relset_1(sK1,sK0,k5_relset_1(sK1,sK0,sK3,sK2),sK3) ),
% 3.44/0.99      inference(cnf_transformation,[],[f43]) ).
% 3.44/0.99  
% 3.44/0.99  cnf(c_222,plain,
% 3.44/0.99      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.44/0.99      | k5_relset_1(sK1,sK0,sK3,sK2) != X0
% 3.44/0.99      | sK3 != X0
% 3.44/0.99      | sK0 != X2
% 3.44/0.99      | sK1 != X1 ),
% 3.44/0.99      inference(resolution_lifted,[status(thm)],[c_10,c_12]) ).
% 3.44/0.99  
% 3.44/0.99  cnf(c_223,plain,
% 3.44/0.99      ( ~ m1_subset_1(k5_relset_1(sK1,sK0,sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
% 3.44/0.99      | sK3 != k5_relset_1(sK1,sK0,sK3,sK2) ),
% 3.44/0.99      inference(unflattening,[status(thm)],[c_222]) ).
% 3.44/0.99  
% 3.44/0.99  cnf(c_19015,plain,
% 3.44/0.99      ( ~ m1_subset_1(k7_relat_1(sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
% 3.44/0.99      | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
% 3.44/0.99      | sK3 != k5_relset_1(sK1,sK0,sK3,sK2) ),
% 3.44/0.99      inference(resolution,[status(thm)],[c_3391,c_223]) ).
% 3.44/0.99  
% 3.44/0.99  cnf(c_14,negated_conjecture,
% 3.44/0.99      ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) ),
% 3.44/0.99      inference(cnf_transformation,[],[f41]) ).
% 3.44/0.99  
% 3.44/0.99  cnf(c_13,negated_conjecture,
% 3.44/0.99      ( r1_tarski(sK1,sK2) ),
% 3.44/0.99      inference(cnf_transformation,[],[f42]) ).
% 3.44/0.99  
% 3.44/0.99  cnf(c_4,plain,
% 3.44/0.99      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1)) | r1_tarski(X0,X1) ),
% 3.44/0.99      inference(cnf_transformation,[],[f32]) ).
% 3.44/0.99  
% 3.44/0.99  cnf(c_998,plain,
% 3.44/0.99      ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
% 3.44/0.99      | r1_tarski(sK3,k2_zfmisc_1(sK1,sK0)) ),
% 3.44/0.99      inference(instantiation,[status(thm)],[c_4]) ).
% 3.44/0.99  
% 3.44/0.99  cnf(c_5,plain,
% 3.44/0.99      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
% 3.44/0.99      | ~ v1_relat_1(X1)
% 3.44/0.99      | v1_relat_1(X0) ),
% 3.44/0.99      inference(cnf_transformation,[],[f34]) ).
% 3.44/0.99  
% 3.44/0.99  cnf(c_3,plain,
% 3.44/0.99      ( m1_subset_1(X0,k1_zfmisc_1(X1)) | ~ r1_tarski(X0,X1) ),
% 3.44/0.99      inference(cnf_transformation,[],[f33]) ).
% 3.44/0.99  
% 3.44/0.99  cnf(c_117,plain,
% 3.44/0.99      ( ~ r1_tarski(X0,X1) | m1_subset_1(X0,k1_zfmisc_1(X1)) ),
% 3.44/0.99      inference(prop_impl,[status(thm)],[c_3]) ).
% 3.44/0.99  
% 3.44/0.99  cnf(c_118,plain,
% 3.44/0.99      ( m1_subset_1(X0,k1_zfmisc_1(X1)) | ~ r1_tarski(X0,X1) ),
% 3.44/0.99      inference(renaming,[status(thm)],[c_117]) ).
% 3.44/0.99  
% 3.44/0.99  cnf(c_146,plain,
% 3.44/0.99      ( ~ r1_tarski(X0,X1) | ~ v1_relat_1(X1) | v1_relat_1(X0) ),
% 3.44/0.99      inference(bin_hyper_res,[status(thm)],[c_5,c_118]) ).
% 3.44/0.99  
% 3.44/0.99  cnf(c_1077,plain,
% 3.44/0.99      ( r1_tarski(sK3,k2_zfmisc_1(sK1,sK0)) ),
% 3.44/0.99      inference(resolution,[status(thm)],[c_4,c_14]) ).
% 3.44/0.99  
% 3.44/0.99  cnf(c_1093,plain,
% 3.44/0.99      ( ~ v1_relat_1(k2_zfmisc_1(sK1,sK0)) | v1_relat_1(sK3) ),
% 3.44/0.99      inference(resolution,[status(thm)],[c_146,c_1077]) ).
% 3.44/0.99  
% 3.44/0.99  cnf(c_6,plain,
% 3.44/0.99      ( v1_relat_1(k2_zfmisc_1(X0,X1)) ),
% 3.44/0.99      inference(cnf_transformation,[],[f35]) ).
% 3.44/0.99  
% 3.44/0.99  cnf(c_1221,plain,
% 3.44/0.99      ( v1_relat_1(sK3) ),
% 3.44/0.99      inference(forward_subsumption_resolution,
% 3.44/0.99                [status(thm)],
% 3.44/0.99                [c_1093,c_6]) ).
% 3.44/0.99  
% 3.44/0.99  cnf(c_0,plain,
% 3.44/0.99      ( ~ r1_tarski(X0,X1) | ~ r1_tarski(X2,X0) | r1_tarski(X2,X1) ),
% 3.44/0.99      inference(cnf_transformation,[],[f29]) ).
% 3.44/0.99  
% 3.44/0.99  cnf(c_1120,plain,
% 3.44/0.99      ( ~ r1_tarski(k2_zfmisc_1(sK1,sK0),X0)
% 3.44/0.99      | r1_tarski(sK3,X0)
% 3.44/0.99      | ~ r1_tarski(sK3,k2_zfmisc_1(sK1,sK0)) ),
% 3.44/0.99      inference(instantiation,[status(thm)],[c_0]) ).
% 3.44/0.99  
% 3.44/0.99  cnf(c_1303,plain,
% 3.44/0.99      ( ~ r1_tarski(k2_zfmisc_1(sK1,sK0),k2_zfmisc_1(sK2,sK0))
% 3.44/0.99      | r1_tarski(sK3,k2_zfmisc_1(sK2,sK0))
% 3.44/0.99      | ~ r1_tarski(sK3,k2_zfmisc_1(sK1,sK0)) ),
% 3.44/0.99      inference(instantiation,[status(thm)],[c_1120]) ).
% 3.44/0.99  
% 3.44/0.99  cnf(c_2,plain,
% 3.44/0.99      ( ~ r1_tarski(X0,X1)
% 3.44/0.99      | r1_tarski(k2_zfmisc_1(X0,X2),k2_zfmisc_1(X1,X2)) ),
% 3.44/0.99      inference(cnf_transformation,[],[f30]) ).
% 3.44/0.99  
% 3.44/0.99  cnf(c_1033,plain,
% 3.44/0.99      ( r1_tarski(k2_zfmisc_1(sK1,X0),k2_zfmisc_1(sK2,X0))
% 3.44/0.99      | ~ r1_tarski(sK1,sK2) ),
% 3.44/0.99      inference(instantiation,[status(thm)],[c_2]) ).
% 3.44/0.99  
% 3.44/0.99  cnf(c_1304,plain,
% 3.44/0.99      ( r1_tarski(k2_zfmisc_1(sK1,sK0),k2_zfmisc_1(sK2,sK0))
% 3.44/0.99      | ~ r1_tarski(sK1,sK2) ),
% 3.44/0.99      inference(instantiation,[status(thm)],[c_1033]) ).
% 3.44/0.99  
% 3.44/0.99  cnf(c_1512,plain,
% 3.44/0.99      ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK2,sK0)))
% 3.44/0.99      | ~ r1_tarski(sK3,k2_zfmisc_1(sK2,sK0)) ),
% 3.44/0.99      inference(instantiation,[status(thm)],[c_3]) ).
% 3.44/0.99  
% 3.44/0.99  cnf(c_897,plain,
% 3.44/0.99      ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) = iProver_top ),
% 3.44/0.99      inference(predicate_to_equality,[status(thm)],[c_14]) ).
% 3.44/0.99  
% 3.44/0.99  cnf(c_899,plain,
% 3.44/0.99      ( k5_relset_1(X0,X1,X2,X3) = k7_relat_1(X2,X3)
% 3.44/0.99      | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
% 3.44/0.99      inference(predicate_to_equality,[status(thm)],[c_9]) ).
% 3.44/0.99  
% 3.44/0.99  cnf(c_1802,plain,
% 3.44/0.99      ( k5_relset_1(sK1,sK0,sK3,X0) = k7_relat_1(sK3,X0) ),
% 3.44/0.99      inference(superposition,[status(thm)],[c_897,c_899]) ).
% 3.44/0.99  
% 3.44/0.99  cnf(c_894,plain,
% 3.44/0.99      ( sK3 != k5_relset_1(sK1,sK0,sK3,sK2)
% 3.44/0.99      | m1_subset_1(k5_relset_1(sK1,sK0,sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) != iProver_top ),
% 3.44/0.99      inference(predicate_to_equality,[status(thm)],[c_223]) ).
% 3.44/0.99  
% 3.44/0.99  cnf(c_1954,plain,
% 3.44/0.99      ( k7_relat_1(sK3,sK2) != sK3
% 3.44/0.99      | m1_subset_1(k7_relat_1(sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) != iProver_top ),
% 3.44/0.99      inference(demodulation,[status(thm)],[c_1802,c_894]) ).
% 3.44/0.99  
% 3.44/0.99  cnf(c_1955,plain,
% 3.44/0.99      ( ~ m1_subset_1(k7_relat_1(sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
% 3.44/0.99      | k7_relat_1(sK3,sK2) != sK3 ),
% 3.44/0.99      inference(predicate_to_equality_rev,[status(thm)],[c_1954]) ).
% 3.44/0.99  
% 3.44/0.99  cnf(c_8,plain,
% 3.44/0.99      ( v4_relat_1(X0,X1)
% 3.44/0.99      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) ),
% 3.44/0.99      inference(cnf_transformation,[],[f37]) ).
% 3.44/0.99  
% 3.44/0.99  cnf(c_7,plain,
% 3.44/0.99      ( ~ v4_relat_1(X0,X1) | ~ v1_relat_1(X0) | k7_relat_1(X0,X1) = X0 ),
% 3.44/0.99      inference(cnf_transformation,[],[f36]) ).
% 3.44/0.99  
% 3.44/0.99  cnf(c_202,plain,
% 3.44/0.99      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.44/0.99      | ~ v1_relat_1(X0)
% 3.44/0.99      | k7_relat_1(X0,X1) = X0 ),
% 3.44/0.99      inference(resolution,[status(thm)],[c_8,c_7]) ).
% 3.44/0.99  
% 3.44/0.99  cnf(c_1671,plain,
% 3.44/0.99      ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
% 3.44/0.99      | ~ v1_relat_1(sK3)
% 3.44/0.99      | k7_relat_1(sK3,X0) = sK3 ),
% 3.44/0.99      inference(instantiation,[status(thm)],[c_202]) ).
% 3.44/0.99  
% 3.44/0.99  cnf(c_2631,plain,
% 3.44/0.99      ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK2,sK0)))
% 3.44/0.99      | ~ v1_relat_1(sK3)
% 3.44/0.99      | k7_relat_1(sK3,sK2) = sK3 ),
% 3.44/0.99      inference(instantiation,[status(thm)],[c_1671]) ).
% 3.44/0.99  
% 3.44/0.99  cnf(c_19399,plain,
% 3.44/0.99      ( ~ m1_subset_1(k7_relat_1(sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) ),
% 3.44/0.99      inference(global_propositional_subsumption,
% 3.44/0.99                [status(thm)],
% 3.44/0.99                [c_19015,c_14,c_13,c_998,c_1221,c_1303,c_1304,c_1512,
% 3.44/0.99                 c_1955,c_2631]) ).
% 3.44/0.99  
% 3.44/0.99  cnf(c_19942,plain,
% 3.44/0.99      ( ~ r1_tarski(k7_relat_1(sK3,sK2),k2_zfmisc_1(sK1,sK0)) ),
% 3.44/0.99      inference(resolution,[status(thm)],[c_19399,c_3]) ).
% 3.44/0.99  
% 3.44/0.99  cnf(c_562,plain,
% 3.44/0.99      ( X0 != X1 | X2 != X3 | k2_zfmisc_1(X0,X2) = k2_zfmisc_1(X1,X3) ),
% 3.44/0.99      theory(equality) ).
% 3.44/0.99  
% 3.44/0.99  cnf(c_561,plain,
% 3.44/0.99      ( ~ r1_tarski(X0,X1) | r1_tarski(X2,X3) | X2 != X0 | X3 != X1 ),
% 3.44/0.99      theory(equality) ).
% 3.44/0.99  
% 3.44/0.99  cnf(c_3016,plain,
% 3.44/0.99      ( ~ r1_tarski(X0,k2_zfmisc_1(X1,X2))
% 3.44/0.99      | r1_tarski(X3,k2_zfmisc_1(X4,X5))
% 3.44/0.99      | X5 != X2
% 3.44/0.99      | X4 != X1
% 3.44/0.99      | X3 != X0 ),
% 3.44/0.99      inference(resolution,[status(thm)],[c_562,c_561]) ).
% 3.44/0.99  
% 3.44/0.99  cnf(c_10326,plain,
% 3.44/0.99      ( r1_tarski(X0,k2_zfmisc_1(X1,X2))
% 3.44/0.99      | X0 != sK3
% 3.44/0.99      | X2 != sK0
% 3.44/0.99      | X1 != sK1 ),
% 3.44/0.99      inference(resolution,[status(thm)],[c_3016,c_1077]) ).
% 3.44/0.99  
% 3.44/0.99  cnf(c_20689,plain,
% 3.44/0.99      ( k7_relat_1(sK3,sK2) != sK3 | sK0 != sK0 | sK1 != sK1 ),
% 3.44/0.99      inference(resolution,[status(thm)],[c_19942,c_10326]) ).
% 3.44/0.99  
% 3.44/0.99  cnf(c_20690,plain,
% 3.44/0.99      ( k7_relat_1(sK3,sK2) != sK3 ),
% 3.44/0.99      inference(equality_resolution_simp,[status(thm)],[c_20689]) ).
% 3.44/0.99  
% 3.44/0.99  cnf(contradiction,plain,
% 3.44/0.99      ( $false ),
% 3.44/0.99      inference(minisat,
% 3.44/0.99                [status(thm)],
% 3.44/0.99                [c_20690,c_2631,c_1512,c_1304,c_1303,c_1221,c_998,c_13,
% 3.44/0.99                 c_14]) ).
% 3.44/0.99  
% 3.44/0.99  
% 3.44/0.99  % SZS output end CNFRefutation for theBenchmark.p
% 3.44/0.99  
% 3.44/0.99  ------                               Statistics
% 3.44/0.99  
% 3.44/0.99  ------ Selected
% 3.44/0.99  
% 3.44/0.99  total_time:                             0.49
% 3.44/0.99  
%------------------------------------------------------------------------------
