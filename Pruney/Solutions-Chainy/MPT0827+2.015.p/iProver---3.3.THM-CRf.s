%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n002.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 11:55:13 EST 2020

% Result     : Theorem 3.98s
% Output     : CNFRefutation 3.98s
% Verified   : 
% Statistics : Number of formulae       :  139 ( 243 expanded)
%              Number of clauses        :   85 ( 107 expanded)
%              Number of leaves         :   17 (  43 expanded)
%              Depth                    :   14
%              Number of atoms          :  359 ( 717 expanded)
%              Number of equality atoms :  135 ( 158 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal clause size      :    8 (   2 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f13,conjecture,(
    ! [X0,X1,X2,X3] :
      ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => ( r1_tarski(k6_relat_1(X2),X3)
       => ( r1_tarski(X2,k2_relset_1(X0,X1,X3))
          & r1_tarski(X2,k1_relset_1(X0,X1,X3)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f14,negated_conjecture,(
    ~ ! [X0,X1,X2,X3] :
        ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
       => ( r1_tarski(k6_relat_1(X2),X3)
         => ( r1_tarski(X2,k2_relset_1(X0,X1,X3))
            & r1_tarski(X2,k1_relset_1(X0,X1,X3)) ) ) ) ),
    inference(negated_conjecture,[],[f13])).

fof(f24,plain,(
    ? [X0,X1,X2,X3] :
      ( ( ~ r1_tarski(X2,k2_relset_1(X0,X1,X3))
        | ~ r1_tarski(X2,k1_relset_1(X0,X1,X3)) )
      & r1_tarski(k6_relat_1(X2),X3)
      & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f25,plain,(
    ? [X0,X1,X2,X3] :
      ( ( ~ r1_tarski(X2,k2_relset_1(X0,X1,X3))
        | ~ r1_tarski(X2,k1_relset_1(X0,X1,X3)) )
      & r1_tarski(k6_relat_1(X2),X3)
      & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(flattening,[],[f24])).

fof(f31,plain,
    ( ? [X0,X1,X2,X3] :
        ( ( ~ r1_tarski(X2,k2_relset_1(X0,X1,X3))
          | ~ r1_tarski(X2,k1_relset_1(X0,X1,X3)) )
        & r1_tarski(k6_relat_1(X2),X3)
        & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) )
   => ( ( ~ r1_tarski(sK2,k2_relset_1(sK0,sK1,sK3))
        | ~ r1_tarski(sK2,k1_relset_1(sK0,sK1,sK3)) )
      & r1_tarski(k6_relat_1(sK2),sK3)
      & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ) ),
    introduced(choice_axiom,[])).

fof(f32,plain,
    ( ( ~ r1_tarski(sK2,k2_relset_1(sK0,sK1,sK3))
      | ~ r1_tarski(sK2,k1_relset_1(sK0,sK1,sK3)) )
    & r1_tarski(k6_relat_1(sK2),sK3)
    & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3])],[f25,f31])).

fof(f52,plain,(
    r1_tarski(k6_relat_1(sK2),sK3) ),
    inference(cnf_transformation,[],[f32])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( X0 = X1
    <=> ( r1_tarski(X1,X0)
        & r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f26,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(nnf_transformation,[],[f1])).

fof(f27,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(flattening,[],[f26])).

fof(f34,plain,(
    ! [X0,X1] :
      ( r1_tarski(X1,X0)
      | X0 != X1 ) ),
    inference(cnf_transformation,[],[f27])).

fof(f54,plain,(
    ! [X1] : r1_tarski(X1,X1) ),
    inference(equality_resolution,[],[f34])).

fof(f7,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ( v5_relat_1(X1,X0)
      <=> r1_tarski(k2_relat_1(X1),X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f21,plain,(
    ! [X0,X1] :
      ( ( v5_relat_1(X1,X0)
      <=> r1_tarski(k2_relat_1(X1),X0) )
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f30,plain,(
    ! [X0,X1] :
      ( ( ( v5_relat_1(X1,X0)
          | ~ r1_tarski(k2_relat_1(X1),X0) )
        & ( r1_tarski(k2_relat_1(X1),X0)
          | ~ v5_relat_1(X1,X0) ) )
      | ~ v1_relat_1(X1) ) ),
    inference(nnf_transformation,[],[f21])).

fof(f44,plain,(
    ! [X0,X1] :
      ( v5_relat_1(X1,X0)
      | ~ r1_tarski(k2_relat_1(X1),X0)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f28,plain,(
    ! [X0,X1] :
      ( ( m1_subset_1(X0,k1_zfmisc_1(X1))
        | ~ r1_tarski(X0,X1) )
      & ( r1_tarski(X0,X1)
        | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ) ) ),
    inference(nnf_transformation,[],[f2])).

fof(f37,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f5,axiom,(
    ! [X0,X1] :
      ( ( v5_relat_1(X1,X0)
        & v1_relat_1(X1) )
     => ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(X1))
         => v5_relat_1(X2,X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f18,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( v5_relat_1(X2,X0)
          | ~ m1_subset_1(X2,k1_zfmisc_1(X1)) )
      | ~ v5_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f19,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( v5_relat_1(X2,X0)
          | ~ m1_subset_1(X2,k1_zfmisc_1(X1)) )
      | ~ v5_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f18])).

fof(f40,plain,(
    ! [X2,X0,X1] :
      ( v5_relat_1(X2,X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(X1))
      | ~ v5_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f3,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(X0))
         => v1_relat_1(X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f15,plain,(
    ! [X0] :
      ( ! [X1] :
          ( v1_relat_1(X1)
          | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f38,plain,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f15])).

fof(f10,axiom,(
    ! [X0] :
      ( k2_relat_1(k6_relat_1(X0)) = X0
      & k1_relat_1(k6_relat_1(X0)) = X0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f48,plain,(
    ! [X0] : k2_relat_1(k6_relat_1(X0)) = X0 ),
    inference(cnf_transformation,[],[f10])).

fof(f43,plain,(
    ! [X0,X1] :
      ( r1_tarski(k2_relat_1(X1),X0)
      | ~ v5_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f8,axiom,(
    ! [X0] : v1_relat_1(k6_relat_1(X0)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f45,plain,(
    ! [X0] : v1_relat_1(k6_relat_1(X0)) ),
    inference(cnf_transformation,[],[f8])).

fof(f6,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ( v4_relat_1(X1,X0)
      <=> r1_tarski(k1_relat_1(X1),X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f20,plain,(
    ! [X0,X1] :
      ( ( v4_relat_1(X1,X0)
      <=> r1_tarski(k1_relat_1(X1),X0) )
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f29,plain,(
    ! [X0,X1] :
      ( ( ( v4_relat_1(X1,X0)
          | ~ r1_tarski(k1_relat_1(X1),X0) )
        & ( r1_tarski(k1_relat_1(X1),X0)
          | ~ v4_relat_1(X1,X0) ) )
      | ~ v1_relat_1(X1) ) ),
    inference(nnf_transformation,[],[f20])).

fof(f41,plain,(
    ! [X0,X1] :
      ( r1_tarski(k1_relat_1(X1),X0)
      | ~ v4_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( ( v4_relat_1(X1,X0)
        & v1_relat_1(X1) )
     => ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(X1))
         => v4_relat_1(X2,X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f16,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( v4_relat_1(X2,X0)
          | ~ m1_subset_1(X2,k1_zfmisc_1(X1)) )
      | ~ v4_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f17,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( v4_relat_1(X2,X0)
          | ~ m1_subset_1(X2,k1_zfmisc_1(X1)) )
      | ~ v4_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f16])).

fof(f39,plain,(
    ! [X2,X0,X1] :
      ( v4_relat_1(X2,X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(X1))
      | ~ v4_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f51,plain,(
    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ),
    inference(cnf_transformation,[],[f32])).

fof(f12,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k2_relat_1(X2) = k2_relset_1(X0,X1,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f23,plain,(
    ! [X0,X1,X2] :
      ( k2_relat_1(X2) = k2_relset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f50,plain,(
    ! [X2,X0,X1] :
      ( k2_relat_1(X2) = k2_relset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f53,plain,
    ( ~ r1_tarski(sK2,k2_relset_1(sK0,sK1,sK3))
    | ~ r1_tarski(sK2,k1_relset_1(sK0,sK1,sK3)) ),
    inference(cnf_transformation,[],[f32])).

fof(f47,plain,(
    ! [X0] : k1_relat_1(k6_relat_1(X0)) = X0 ),
    inference(cnf_transformation,[],[f10])).

fof(f42,plain,(
    ! [X0,X1] :
      ( v4_relat_1(X1,X0)
      | ~ r1_tarski(k1_relat_1(X1),X0)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f36,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f9,axiom,(
    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f46,plain,(
    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1)) ),
    inference(cnf_transformation,[],[f9])).

fof(f11,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k1_relat_1(X2) = k1_relset_1(X0,X1,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f22,plain,(
    ! [X0,X1,X2] :
      ( k1_relat_1(X2) = k1_relset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f49,plain,(
    ! [X2,X0,X1] :
      ( k1_relat_1(X2) = k1_relset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f33,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | X0 != X1 ) ),
    inference(cnf_transformation,[],[f27])).

fof(f55,plain,(
    ! [X1] : r1_tarski(X1,X1) ),
    inference(equality_resolution,[],[f33])).

cnf(c_19,negated_conjecture,
    ( r1_tarski(k6_relat_1(sK2),sK3) ),
    inference(cnf_transformation,[],[f52])).

cnf(c_767,plain,
    ( r1_tarski(k6_relat_1(sK2),sK3) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_19])).

cnf(c_1,plain,
    ( r1_tarski(X0,X0) ),
    inference(cnf_transformation,[],[f54])).

cnf(c_781,plain,
    ( r1_tarski(X0,X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1])).

cnf(c_10,plain,
    ( v5_relat_1(X0,X1)
    | ~ r1_tarski(k2_relat_1(X0),X1)
    | ~ v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f44])).

cnf(c_774,plain,
    ( v5_relat_1(X0,X1) = iProver_top
    | r1_tarski(k2_relat_1(X0),X1) != iProver_top
    | v1_relat_1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_10])).

cnf(c_1617,plain,
    ( v5_relat_1(X0,k2_relat_1(X0)) = iProver_top
    | v1_relat_1(X0) != iProver_top ),
    inference(superposition,[status(thm)],[c_781,c_774])).

cnf(c_3,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(X1))
    | ~ r1_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f37])).

cnf(c_780,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(X1)) = iProver_top
    | r1_tarski(X0,X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3])).

cnf(c_7,plain,
    ( ~ v5_relat_1(X0,X1)
    | v5_relat_1(X2,X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(X0))
    | ~ v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f40])).

cnf(c_777,plain,
    ( v5_relat_1(X0,X1) != iProver_top
    | v5_relat_1(X2,X1) = iProver_top
    | m1_subset_1(X2,k1_zfmisc_1(X0)) != iProver_top
    | v1_relat_1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_7])).

cnf(c_1965,plain,
    ( v5_relat_1(X0,X1) != iProver_top
    | v5_relat_1(X2,X1) = iProver_top
    | r1_tarski(X2,X0) != iProver_top
    | v1_relat_1(X0) != iProver_top ),
    inference(superposition,[status(thm)],[c_780,c_777])).

cnf(c_4519,plain,
    ( v5_relat_1(X0,k2_relat_1(X1)) = iProver_top
    | r1_tarski(X0,X1) != iProver_top
    | v1_relat_1(X1) != iProver_top ),
    inference(superposition,[status(thm)],[c_1617,c_1965])).

cnf(c_6417,plain,
    ( v5_relat_1(X0,k2_relat_1(X1)) = iProver_top
    | r1_tarski(X2,X1) != iProver_top
    | r1_tarski(X0,X2) != iProver_top
    | v1_relat_1(X2) != iProver_top
    | v1_relat_1(X1) != iProver_top ),
    inference(superposition,[status(thm)],[c_4519,c_1965])).

cnf(c_5,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | ~ v1_relat_1(X1)
    | v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f38])).

cnf(c_129,plain,
    ( ~ r1_tarski(X0,X1)
    | m1_subset_1(X0,k1_zfmisc_1(X1)) ),
    inference(prop_impl,[status(thm)],[c_3])).

cnf(c_130,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(X1))
    | ~ r1_tarski(X0,X1) ),
    inference(renaming,[status(thm)],[c_129])).

cnf(c_165,plain,
    ( ~ r1_tarski(X0,X1)
    | ~ v1_relat_1(X1)
    | v1_relat_1(X0) ),
    inference(bin_hyper_res,[status(thm)],[c_5,c_130])).

cnf(c_765,plain,
    ( r1_tarski(X0,X1) != iProver_top
    | v1_relat_1(X1) != iProver_top
    | v1_relat_1(X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_165])).

cnf(c_10697,plain,
    ( v5_relat_1(X0,k2_relat_1(X1)) = iProver_top
    | r1_tarski(X0,X2) != iProver_top
    | r1_tarski(X2,X1) != iProver_top
    | v1_relat_1(X1) != iProver_top ),
    inference(forward_subsumption_resolution,[status(thm)],[c_6417,c_765])).

cnf(c_10702,plain,
    ( v5_relat_1(k6_relat_1(sK2),k2_relat_1(X0)) = iProver_top
    | r1_tarski(sK3,X0) != iProver_top
    | v1_relat_1(X0) != iProver_top ),
    inference(superposition,[status(thm)],[c_767,c_10697])).

cnf(c_14,plain,
    ( k2_relat_1(k6_relat_1(X0)) = X0 ),
    inference(cnf_transformation,[],[f48])).

cnf(c_11,plain,
    ( ~ v5_relat_1(X0,X1)
    | r1_tarski(k2_relat_1(X0),X1)
    | ~ v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f43])).

cnf(c_773,plain,
    ( v5_relat_1(X0,X1) != iProver_top
    | r1_tarski(k2_relat_1(X0),X1) = iProver_top
    | v1_relat_1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_11])).

cnf(c_1581,plain,
    ( v5_relat_1(k6_relat_1(X0),X1) != iProver_top
    | r1_tarski(X0,X1) = iProver_top
    | v1_relat_1(k6_relat_1(X0)) != iProver_top ),
    inference(superposition,[status(thm)],[c_14,c_773])).

cnf(c_12,plain,
    ( v1_relat_1(k6_relat_1(X0)) ),
    inference(cnf_transformation,[],[f45])).

cnf(c_35,plain,
    ( v1_relat_1(k6_relat_1(X0)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_12])).

cnf(c_1873,plain,
    ( r1_tarski(X0,X1) = iProver_top
    | v5_relat_1(k6_relat_1(X0),X1) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_1581,c_35])).

cnf(c_1874,plain,
    ( v5_relat_1(k6_relat_1(X0),X1) != iProver_top
    | r1_tarski(X0,X1) = iProver_top ),
    inference(renaming,[status(thm)],[c_1873])).

cnf(c_10876,plain,
    ( r1_tarski(sK3,X0) != iProver_top
    | r1_tarski(sK2,k2_relat_1(X0)) = iProver_top
    | v1_relat_1(X0) != iProver_top ),
    inference(superposition,[status(thm)],[c_10702,c_1874])).

cnf(c_10966,plain,
    ( r1_tarski(sK3,sK3) != iProver_top
    | r1_tarski(sK2,k2_relat_1(sK3)) = iProver_top
    | v1_relat_1(sK3) != iProver_top ),
    inference(instantiation,[status(thm)],[c_10876])).

cnf(c_9,plain,
    ( ~ v4_relat_1(X0,X1)
    | r1_tarski(k1_relat_1(X0),X1)
    | ~ v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f41])).

cnf(c_1345,plain,
    ( ~ v4_relat_1(k6_relat_1(X0),X1)
    | r1_tarski(k1_relat_1(k6_relat_1(X0)),X1)
    | ~ v1_relat_1(k6_relat_1(X0)) ),
    inference(instantiation,[status(thm)],[c_9])).

cnf(c_2901,plain,
    ( ~ v4_relat_1(k6_relat_1(sK2),X0)
    | r1_tarski(k1_relat_1(k6_relat_1(sK2)),X0)
    | ~ v1_relat_1(k6_relat_1(sK2)) ),
    inference(instantiation,[status(thm)],[c_1345])).

cnf(c_4423,plain,
    ( ~ v4_relat_1(k6_relat_1(sK2),k1_relat_1(X0))
    | r1_tarski(k1_relat_1(k6_relat_1(sK2)),k1_relat_1(X0))
    | ~ v1_relat_1(k6_relat_1(sK2)) ),
    inference(instantiation,[status(thm)],[c_2901])).

cnf(c_4428,plain,
    ( v4_relat_1(k6_relat_1(sK2),k1_relat_1(X0)) != iProver_top
    | r1_tarski(k1_relat_1(k6_relat_1(sK2)),k1_relat_1(X0)) = iProver_top
    | v1_relat_1(k6_relat_1(sK2)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_4423])).

cnf(c_4430,plain,
    ( v4_relat_1(k6_relat_1(sK2),k1_relat_1(sK3)) != iProver_top
    | r1_tarski(k1_relat_1(k6_relat_1(sK2)),k1_relat_1(sK3)) = iProver_top
    | v1_relat_1(k6_relat_1(sK2)) != iProver_top ),
    inference(instantiation,[status(thm)],[c_4428])).

cnf(c_6,plain,
    ( ~ v4_relat_1(X0,X1)
    | v4_relat_1(X2,X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(X0))
    | ~ v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f39])).

cnf(c_1952,plain,
    ( ~ v4_relat_1(X0,k1_relat_1(X0))
    | v4_relat_1(X1,k1_relat_1(X0))
    | ~ m1_subset_1(X1,k1_zfmisc_1(X0))
    | ~ v1_relat_1(X0) ),
    inference(instantiation,[status(thm)],[c_6])).

cnf(c_4422,plain,
    ( ~ v4_relat_1(X0,k1_relat_1(X0))
    | v4_relat_1(k6_relat_1(sK2),k1_relat_1(X0))
    | ~ m1_subset_1(k6_relat_1(sK2),k1_zfmisc_1(X0))
    | ~ v1_relat_1(X0) ),
    inference(instantiation,[status(thm)],[c_1952])).

cnf(c_4424,plain,
    ( v4_relat_1(X0,k1_relat_1(X0)) != iProver_top
    | v4_relat_1(k6_relat_1(sK2),k1_relat_1(X0)) = iProver_top
    | m1_subset_1(k6_relat_1(sK2),k1_zfmisc_1(X0)) != iProver_top
    | v1_relat_1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_4422])).

cnf(c_4426,plain,
    ( v4_relat_1(k6_relat_1(sK2),k1_relat_1(sK3)) = iProver_top
    | v4_relat_1(sK3,k1_relat_1(sK3)) != iProver_top
    | m1_subset_1(k6_relat_1(sK2),k1_zfmisc_1(sK3)) != iProver_top
    | v1_relat_1(sK3) != iProver_top ),
    inference(instantiation,[status(thm)],[c_4424])).

cnf(c_3057,plain,
    ( m1_subset_1(k6_relat_1(X0),k1_zfmisc_1(X1))
    | ~ r1_tarski(k6_relat_1(X0),X1) ),
    inference(instantiation,[status(thm)],[c_3])).

cnf(c_4299,plain,
    ( m1_subset_1(k6_relat_1(sK2),k1_zfmisc_1(sK3))
    | ~ r1_tarski(k6_relat_1(sK2),sK3) ),
    inference(instantiation,[status(thm)],[c_3057])).

cnf(c_4300,plain,
    ( m1_subset_1(k6_relat_1(sK2),k1_zfmisc_1(sK3)) = iProver_top
    | r1_tarski(k6_relat_1(sK2),sK3) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_4299])).

cnf(c_346,plain,
    ( ~ r1_tarski(X0,X1)
    | r1_tarski(X2,X3)
    | X2 != X0
    | X3 != X1 ),
    theory(equality)).

cnf(c_994,plain,
    ( ~ r1_tarski(X0,X1)
    | r1_tarski(sK2,k1_relset_1(sK0,sK1,sK3))
    | k1_relset_1(sK0,sK1,sK3) != X1
    | sK2 != X0 ),
    inference(instantiation,[status(thm)],[c_346])).

cnf(c_1854,plain,
    ( ~ r1_tarski(k1_relat_1(k6_relat_1(sK2)),X0)
    | r1_tarski(sK2,k1_relset_1(sK0,sK1,sK3))
    | k1_relset_1(sK0,sK1,sK3) != X0
    | sK2 != k1_relat_1(k6_relat_1(sK2)) ),
    inference(instantiation,[status(thm)],[c_994])).

cnf(c_2760,plain,
    ( ~ r1_tarski(k1_relat_1(k6_relat_1(sK2)),k1_relat_1(sK3))
    | r1_tarski(sK2,k1_relset_1(sK0,sK1,sK3))
    | k1_relset_1(sK0,sK1,sK3) != k1_relat_1(sK3)
    | sK2 != k1_relat_1(k6_relat_1(sK2)) ),
    inference(instantiation,[status(thm)],[c_1854])).

cnf(c_2761,plain,
    ( k1_relset_1(sK0,sK1,sK3) != k1_relat_1(sK3)
    | sK2 != k1_relat_1(k6_relat_1(sK2))
    | r1_tarski(k1_relat_1(k6_relat_1(sK2)),k1_relat_1(sK3)) != iProver_top
    | r1_tarski(sK2,k1_relset_1(sK0,sK1,sK3)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2760])).

cnf(c_20,negated_conjecture,
    ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ),
    inference(cnf_transformation,[],[f51])).

cnf(c_766,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_20])).

cnf(c_17,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k2_relset_1(X1,X2,X0) = k2_relat_1(X0) ),
    inference(cnf_transformation,[],[f50])).

cnf(c_769,plain,
    ( k2_relset_1(X0,X1,X2) = k2_relat_1(X2)
    | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_17])).

cnf(c_1310,plain,
    ( k2_relset_1(sK0,sK1,sK3) = k2_relat_1(sK3) ),
    inference(superposition,[status(thm)],[c_766,c_769])).

cnf(c_18,negated_conjecture,
    ( ~ r1_tarski(sK2,k2_relset_1(sK0,sK1,sK3))
    | ~ r1_tarski(sK2,k1_relset_1(sK0,sK1,sK3)) ),
    inference(cnf_transformation,[],[f53])).

cnf(c_768,plain,
    ( r1_tarski(sK2,k2_relset_1(sK0,sK1,sK3)) != iProver_top
    | r1_tarski(sK2,k1_relset_1(sK0,sK1,sK3)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_18])).

cnf(c_2289,plain,
    ( r1_tarski(sK2,k1_relset_1(sK0,sK1,sK3)) != iProver_top
    | r1_tarski(sK2,k2_relat_1(sK3)) != iProver_top ),
    inference(demodulation,[status(thm)],[c_1310,c_768])).

cnf(c_15,plain,
    ( k1_relat_1(k6_relat_1(X0)) = X0 ),
    inference(cnf_transformation,[],[f47])).

cnf(c_1572,plain,
    ( k1_relat_1(k6_relat_1(sK2)) = sK2 ),
    inference(instantiation,[status(thm)],[c_15])).

cnf(c_345,plain,
    ( X0 != X1
    | X2 != X1
    | X2 = X0 ),
    theory(equality)).

cnf(c_1058,plain,
    ( X0 != X1
    | sK2 != X1
    | sK2 = X0 ),
    inference(instantiation,[status(thm)],[c_345])).

cnf(c_1203,plain,
    ( X0 != sK2
    | sK2 = X0
    | sK2 != sK2 ),
    inference(instantiation,[status(thm)],[c_1058])).

cnf(c_1571,plain,
    ( k1_relat_1(k6_relat_1(sK2)) != sK2
    | sK2 = k1_relat_1(k6_relat_1(sK2))
    | sK2 != sK2 ),
    inference(instantiation,[status(thm)],[c_1203])).

cnf(c_8,plain,
    ( v4_relat_1(X0,X1)
    | ~ r1_tarski(k1_relat_1(X0),X1)
    | ~ v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f42])).

cnf(c_1244,plain,
    ( v4_relat_1(X0,k1_relat_1(X0))
    | ~ v1_relat_1(X0) ),
    inference(resolution,[status(thm)],[c_8,c_1])).

cnf(c_1245,plain,
    ( v4_relat_1(X0,k1_relat_1(X0)) = iProver_top
    | v1_relat_1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1244])).

cnf(c_1247,plain,
    ( v4_relat_1(sK3,k1_relat_1(sK3)) = iProver_top
    | v1_relat_1(sK3) != iProver_top ),
    inference(instantiation,[status(thm)],[c_1245])).

cnf(c_4,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | r1_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f36])).

cnf(c_1038,plain,
    ( r1_tarski(sK3,k2_zfmisc_1(sK0,sK1)) ),
    inference(resolution,[status(thm)],[c_4,c_20])).

cnf(c_1130,plain,
    ( ~ v1_relat_1(k2_zfmisc_1(sK0,sK1))
    | v1_relat_1(sK3) ),
    inference(resolution,[status(thm)],[c_165,c_1038])).

cnf(c_13,plain,
    ( v1_relat_1(k2_zfmisc_1(X0,X1)) ),
    inference(cnf_transformation,[],[f46])).

cnf(c_1136,plain,
    ( v1_relat_1(sK3) ),
    inference(forward_subsumption_resolution,[status(thm)],[c_1130,c_13])).

cnf(c_1137,plain,
    ( v1_relat_1(sK3) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1136])).

cnf(c_1128,plain,
    ( v1_relat_1(k6_relat_1(sK2))
    | ~ v1_relat_1(sK3) ),
    inference(resolution,[status(thm)],[c_165,c_19])).

cnf(c_1129,plain,
    ( v1_relat_1(k6_relat_1(sK2)) = iProver_top
    | v1_relat_1(sK3) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1128])).

cnf(c_344,plain,
    ( X0 = X0 ),
    theory(equality)).

cnf(c_1053,plain,
    ( sK2 = sK2 ),
    inference(instantiation,[status(thm)],[c_344])).

cnf(c_16,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k1_relset_1(X1,X2,X0) = k1_relat_1(X0) ),
    inference(cnf_transformation,[],[f49])).

cnf(c_987,plain,
    ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    | k1_relset_1(sK0,sK1,sK3) = k1_relat_1(sK3) ),
    inference(instantiation,[status(thm)],[c_16])).

cnf(c_2,plain,
    ( r1_tarski(X0,X0) ),
    inference(cnf_transformation,[],[f55])).

cnf(c_59,plain,
    ( r1_tarski(X0,X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2])).

cnf(c_61,plain,
    ( r1_tarski(sK3,sK3) = iProver_top ),
    inference(instantiation,[status(thm)],[c_59])).

cnf(c_22,plain,
    ( r1_tarski(k6_relat_1(sK2),sK3) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_19])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_10966,c_4430,c_4426,c_4300,c_2761,c_2289,c_1572,c_1571,c_1247,c_1137,c_1129,c_1053,c_987,c_61,c_22,c_20])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : iproveropt_run.sh %d %s
% 0.13/0.34  % Computer   : n002.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 11:50:07 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running in FOF mode
% 3.98/0.98  % SZS status Started for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.98/0.98  
% 3.98/0.98  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 3.98/0.98  
% 3.98/0.98  ------  iProver source info
% 3.98/0.98  
% 3.98/0.98  git: date: 2020-06-30 10:37:57 +0100
% 3.98/0.98  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 3.98/0.98  git: non_committed_changes: false
% 3.98/0.98  git: last_make_outside_of_git: false
% 3.98/0.98  
% 3.98/0.98  ------ 
% 3.98/0.98  
% 3.98/0.98  ------ Input Options
% 3.98/0.98  
% 3.98/0.98  --out_options                           all
% 3.98/0.98  --tptp_safe_out                         true
% 3.98/0.98  --problem_path                          ""
% 3.98/0.98  --include_path                          ""
% 3.98/0.98  --clausifier                            res/vclausify_rel
% 3.98/0.98  --clausifier_options                    --mode clausify
% 3.98/0.98  --stdin                                 false
% 3.98/0.98  --stats_out                             sel
% 3.98/0.98  
% 3.98/0.98  ------ General Options
% 3.98/0.98  
% 3.98/0.98  --fof                                   false
% 3.98/0.98  --time_out_real                         604.99
% 3.98/0.98  --time_out_virtual                      -1.
% 3.98/0.98  --symbol_type_check                     false
% 3.98/0.98  --clausify_out                          false
% 3.98/0.98  --sig_cnt_out                           false
% 3.98/0.98  --trig_cnt_out                          false
% 3.98/0.98  --trig_cnt_out_tolerance                1.
% 3.98/0.98  --trig_cnt_out_sk_spl                   false
% 3.98/0.98  --abstr_cl_out                          false
% 3.98/0.98  
% 3.98/0.98  ------ Global Options
% 3.98/0.98  
% 3.98/0.98  --schedule                              none
% 3.98/0.98  --add_important_lit                     false
% 3.98/0.98  --prop_solver_per_cl                    1000
% 3.98/0.98  --min_unsat_core                        false
% 3.98/0.98  --soft_assumptions                      false
% 3.98/0.98  --soft_lemma_size                       3
% 3.98/0.98  --prop_impl_unit_size                   0
% 3.98/0.98  --prop_impl_unit                        []
% 3.98/0.98  --share_sel_clauses                     true
% 3.98/0.98  --reset_solvers                         false
% 3.98/0.98  --bc_imp_inh                            [conj_cone]
% 3.98/0.98  --conj_cone_tolerance                   3.
% 3.98/0.98  --extra_neg_conj                        none
% 3.98/0.98  --large_theory_mode                     true
% 3.98/0.98  --prolific_symb_bound                   200
% 3.98/0.98  --lt_threshold                          2000
% 3.98/0.98  --clause_weak_htbl                      true
% 3.98/0.98  --gc_record_bc_elim                     false
% 3.98/0.98  
% 3.98/0.98  ------ Preprocessing Options
% 3.98/0.98  
% 3.98/0.98  --preprocessing_flag                    true
% 3.98/0.98  --time_out_prep_mult                    0.1
% 3.98/0.98  --splitting_mode                        input
% 3.98/0.98  --splitting_grd                         true
% 3.98/0.98  --splitting_cvd                         false
% 3.98/0.98  --splitting_cvd_svl                     false
% 3.98/0.98  --splitting_nvd                         32
% 3.98/0.98  --sub_typing                            true
% 3.98/0.98  --prep_gs_sim                           false
% 3.98/0.98  --prep_unflatten                        true
% 3.98/0.98  --prep_res_sim                          true
% 3.98/0.98  --prep_upred                            true
% 3.98/0.98  --prep_sem_filter                       exhaustive
% 3.98/0.98  --prep_sem_filter_out                   false
% 3.98/0.98  --pred_elim                             false
% 3.98/0.98  --res_sim_input                         true
% 3.98/0.98  --eq_ax_congr_red                       true
% 3.98/0.98  --pure_diseq_elim                       true
% 3.98/0.98  --brand_transform                       false
% 3.98/0.98  --non_eq_to_eq                          false
% 3.98/0.98  --prep_def_merge                        true
% 3.98/0.98  --prep_def_merge_prop_impl              false
% 3.98/0.98  --prep_def_merge_mbd                    true
% 3.98/0.98  --prep_def_merge_tr_red                 false
% 3.98/0.98  --prep_def_merge_tr_cl                  false
% 3.98/0.98  --smt_preprocessing                     true
% 3.98/0.98  --smt_ac_axioms                         fast
% 3.98/0.98  --preprocessed_out                      false
% 3.98/0.98  --preprocessed_stats                    false
% 3.98/0.98  
% 3.98/0.98  ------ Abstraction refinement Options
% 3.98/0.98  
% 3.98/0.98  --abstr_ref                             []
% 3.98/0.98  --abstr_ref_prep                        false
% 3.98/0.98  --abstr_ref_until_sat                   false
% 3.98/0.98  --abstr_ref_sig_restrict                funpre
% 3.98/0.98  --abstr_ref_af_restrict_to_split_sk     false
% 3.98/0.98  --abstr_ref_under                       []
% 3.98/0.98  
% 3.98/0.98  ------ SAT Options
% 3.98/0.98  
% 3.98/0.98  --sat_mode                              false
% 3.98/0.98  --sat_fm_restart_options                ""
% 3.98/0.98  --sat_gr_def                            false
% 3.98/0.98  --sat_epr_types                         true
% 3.98/0.98  --sat_non_cyclic_types                  false
% 3.98/0.98  --sat_finite_models                     false
% 3.98/0.98  --sat_fm_lemmas                         false
% 3.98/0.98  --sat_fm_prep                           false
% 3.98/0.98  --sat_fm_uc_incr                        true
% 3.98/0.98  --sat_out_model                         small
% 3.98/0.98  --sat_out_clauses                       false
% 3.98/0.98  
% 3.98/0.98  ------ QBF Options
% 3.98/0.98  
% 3.98/0.98  --qbf_mode                              false
% 3.98/0.98  --qbf_elim_univ                         false
% 3.98/0.98  --qbf_dom_inst                          none
% 3.98/0.98  --qbf_dom_pre_inst                      false
% 3.98/0.98  --qbf_sk_in                             false
% 3.98/0.98  --qbf_pred_elim                         true
% 3.98/0.98  --qbf_split                             512
% 3.98/0.98  
% 3.98/0.98  ------ BMC1 Options
% 3.98/0.98  
% 3.98/0.98  --bmc1_incremental                      false
% 3.98/0.98  --bmc1_axioms                           reachable_all
% 3.98/0.98  --bmc1_min_bound                        0
% 3.98/0.98  --bmc1_max_bound                        -1
% 3.98/0.98  --bmc1_max_bound_default                -1
% 3.98/0.98  --bmc1_symbol_reachability              true
% 3.98/0.98  --bmc1_property_lemmas                  false
% 3.98/0.98  --bmc1_k_induction                      false
% 3.98/0.98  --bmc1_non_equiv_states                 false
% 3.98/0.98  --bmc1_deadlock                         false
% 3.98/0.98  --bmc1_ucm                              false
% 3.98/0.98  --bmc1_add_unsat_core                   none
% 3.98/0.98  --bmc1_unsat_core_children              false
% 3.98/0.98  --bmc1_unsat_core_extrapolate_axioms    false
% 3.98/0.98  --bmc1_out_stat                         full
% 3.98/0.98  --bmc1_ground_init                      false
% 3.98/0.98  --bmc1_pre_inst_next_state              false
% 3.98/0.98  --bmc1_pre_inst_state                   false
% 3.98/0.98  --bmc1_pre_inst_reach_state             false
% 3.98/0.98  --bmc1_out_unsat_core                   false
% 3.98/0.98  --bmc1_aig_witness_out                  false
% 3.98/0.98  --bmc1_verbose                          false
% 3.98/0.98  --bmc1_dump_clauses_tptp                false
% 3.98/0.98  --bmc1_dump_unsat_core_tptp             false
% 3.98/0.98  --bmc1_dump_file                        -
% 3.98/0.98  --bmc1_ucm_expand_uc_limit              128
% 3.98/0.98  --bmc1_ucm_n_expand_iterations          6
% 3.98/0.98  --bmc1_ucm_extend_mode                  1
% 3.98/0.98  --bmc1_ucm_init_mode                    2
% 3.98/0.98  --bmc1_ucm_cone_mode                    none
% 3.98/0.98  --bmc1_ucm_reduced_relation_type        0
% 3.98/0.98  --bmc1_ucm_relax_model                  4
% 3.98/0.98  --bmc1_ucm_full_tr_after_sat            true
% 3.98/0.98  --bmc1_ucm_expand_neg_assumptions       false
% 3.98/0.98  --bmc1_ucm_layered_model                none
% 3.98/0.98  --bmc1_ucm_max_lemma_size               10
% 3.98/0.98  
% 3.98/0.98  ------ AIG Options
% 3.98/0.98  
% 3.98/0.98  --aig_mode                              false
% 3.98/0.98  
% 3.98/0.98  ------ Instantiation Options
% 3.98/0.98  
% 3.98/0.98  --instantiation_flag                    true
% 3.98/0.98  --inst_sos_flag                         false
% 3.98/0.98  --inst_sos_phase                        true
% 3.98/0.98  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 3.98/0.98  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 3.98/0.98  --inst_lit_sel_side                     num_symb
% 3.98/0.98  --inst_solver_per_active                1400
% 3.98/0.98  --inst_solver_calls_frac                1.
% 3.98/0.98  --inst_passive_queue_type               priority_queues
% 3.98/0.98  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 3.98/0.98  --inst_passive_queues_freq              [25;2]
% 3.98/0.98  --inst_dismatching                      true
% 3.98/0.98  --inst_eager_unprocessed_to_passive     true
% 3.98/0.98  --inst_prop_sim_given                   true
% 3.98/0.98  --inst_prop_sim_new                     false
% 3.98/0.98  --inst_subs_new                         false
% 3.98/0.98  --inst_eq_res_simp                      false
% 3.98/0.98  --inst_subs_given                       false
% 3.98/0.98  --inst_orphan_elimination               true
% 3.98/0.98  --inst_learning_loop_flag               true
% 3.98/0.98  --inst_learning_start                   3000
% 3.98/0.98  --inst_learning_factor                  2
% 3.98/0.98  --inst_start_prop_sim_after_learn       3
% 3.98/0.98  --inst_sel_renew                        solver
% 3.98/0.98  --inst_lit_activity_flag                true
% 3.98/0.98  --inst_restr_to_given                   false
% 3.98/0.98  --inst_activity_threshold               500
% 3.98/0.98  --inst_out_proof                        true
% 3.98/0.98  
% 3.98/0.98  ------ Resolution Options
% 3.98/0.98  
% 3.98/0.98  --resolution_flag                       true
% 3.98/0.98  --res_lit_sel                           adaptive
% 3.98/0.98  --res_lit_sel_side                      none
% 3.98/0.98  --res_ordering                          kbo
% 3.98/0.98  --res_to_prop_solver                    active
% 3.98/0.98  --res_prop_simpl_new                    false
% 3.98/0.98  --res_prop_simpl_given                  true
% 3.98/0.98  --res_passive_queue_type                priority_queues
% 3.98/0.98  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 3.98/0.98  --res_passive_queues_freq               [15;5]
% 3.98/0.98  --res_forward_subs                      full
% 3.98/0.98  --res_backward_subs                     full
% 3.98/0.98  --res_forward_subs_resolution           true
% 3.98/0.98  --res_backward_subs_resolution          true
% 3.98/0.98  --res_orphan_elimination                true
% 3.98/0.98  --res_time_limit                        2.
% 3.98/0.98  --res_out_proof                         true
% 3.98/0.98  
% 3.98/0.98  ------ Superposition Options
% 3.98/0.98  
% 3.98/0.98  --superposition_flag                    true
% 3.98/0.98  --sup_passive_queue_type                priority_queues
% 3.98/0.98  --sup_passive_queues                    [[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 3.98/0.98  --sup_passive_queues_freq               [1;4]
% 3.98/0.98  --demod_completeness_check              fast
% 3.98/0.98  --demod_use_ground                      true
% 3.98/0.98  --sup_to_prop_solver                    passive
% 3.98/0.98  --sup_prop_simpl_new                    true
% 3.98/0.98  --sup_prop_simpl_given                  true
% 3.98/0.98  --sup_fun_splitting                     false
% 3.98/0.98  --sup_smt_interval                      50000
% 3.98/0.98  
% 3.98/0.98  ------ Superposition Simplification Setup
% 3.98/0.98  
% 3.98/0.98  --sup_indices_passive                   []
% 3.98/0.98  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.98/0.98  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.98/0.98  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.98/0.98  --sup_full_triv                         [TrivRules;PropSubs]
% 3.98/0.98  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.98/0.98  --sup_full_bw                           [BwDemod]
% 3.98/0.98  --sup_immed_triv                        [TrivRules]
% 3.98/0.98  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 3.98/0.98  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.98/0.98  --sup_immed_bw_main                     []
% 3.98/0.98  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 3.98/0.98  --sup_input_triv                        [Unflattening;TrivRules]
% 3.98/0.98  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.98/0.98  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 3.98/0.98  
% 3.98/0.98  ------ Combination Options
% 3.98/0.98  
% 3.98/0.98  --comb_res_mult                         3
% 3.98/0.98  --comb_sup_mult                         2
% 3.98/0.98  --comb_inst_mult                        10
% 3.98/0.98  
% 3.98/0.98  ------ Debug Options
% 3.98/0.98  
% 3.98/0.98  --dbg_backtrace                         false
% 3.98/0.98  --dbg_dump_prop_clauses                 false
% 3.98/0.98  --dbg_dump_prop_clauses_file            -
% 3.98/0.98  --dbg_out_stat                          false
% 3.98/0.98  ------ Parsing...
% 3.98/0.98  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 3.98/0.98  
% 3.98/0.98  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 1 0s  sf_e 
% 3.98/0.98  
% 3.98/0.98  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 3.98/0.98  
% 3.98/0.98  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 3.98/0.98  ------ Proving...
% 3.98/0.98  ------ Problem Properties 
% 3.98/0.98  
% 3.98/0.98  
% 3.98/0.98  clauses                                 20
% 3.98/0.98  conjectures                             3
% 3.98/0.98  EPR                                     3
% 3.98/0.98  Horn                                    20
% 3.98/0.98  unary                                   7
% 3.98/0.98  binary                                  5
% 3.98/0.98  lits                                    43
% 3.98/0.98  lits eq                                 5
% 3.98/0.98  fd_pure                                 0
% 3.98/0.98  fd_pseudo                               0
% 3.98/0.98  fd_cond                                 0
% 3.98/0.98  fd_pseudo_cond                          1
% 3.98/0.98  AC symbols                              0
% 3.98/0.98  
% 3.98/0.98  ------ Input Options Time Limit: Unbounded
% 3.98/0.98  
% 3.98/0.98  
% 3.98/0.98  ------ 
% 3.98/0.98  Current options:
% 3.98/0.98  ------ 
% 3.98/0.98  
% 3.98/0.98  ------ Input Options
% 3.98/0.98  
% 3.98/0.98  --out_options                           all
% 3.98/0.98  --tptp_safe_out                         true
% 3.98/0.98  --problem_path                          ""
% 3.98/0.98  --include_path                          ""
% 3.98/0.98  --clausifier                            res/vclausify_rel
% 3.98/0.98  --clausifier_options                    --mode clausify
% 3.98/0.98  --stdin                                 false
% 3.98/0.98  --stats_out                             sel
% 3.98/0.98  
% 3.98/0.98  ------ General Options
% 3.98/0.98  
% 3.98/0.98  --fof                                   false
% 3.98/0.98  --time_out_real                         604.99
% 3.98/0.98  --time_out_virtual                      -1.
% 3.98/0.98  --symbol_type_check                     false
% 3.98/0.98  --clausify_out                          false
% 3.98/0.98  --sig_cnt_out                           false
% 3.98/0.98  --trig_cnt_out                          false
% 3.98/0.98  --trig_cnt_out_tolerance                1.
% 3.98/0.98  --trig_cnt_out_sk_spl                   false
% 3.98/0.98  --abstr_cl_out                          false
% 3.98/0.98  
% 3.98/0.98  ------ Global Options
% 3.98/0.98  
% 3.98/0.98  --schedule                              none
% 3.98/0.98  --add_important_lit                     false
% 3.98/0.98  --prop_solver_per_cl                    1000
% 3.98/0.98  --min_unsat_core                        false
% 3.98/0.98  --soft_assumptions                      false
% 3.98/0.98  --soft_lemma_size                       3
% 3.98/0.98  --prop_impl_unit_size                   0
% 3.98/0.98  --prop_impl_unit                        []
% 3.98/0.98  --share_sel_clauses                     true
% 3.98/0.98  --reset_solvers                         false
% 3.98/0.98  --bc_imp_inh                            [conj_cone]
% 3.98/0.98  --conj_cone_tolerance                   3.
% 3.98/0.98  --extra_neg_conj                        none
% 3.98/0.98  --large_theory_mode                     true
% 3.98/0.98  --prolific_symb_bound                   200
% 3.98/0.98  --lt_threshold                          2000
% 3.98/0.98  --clause_weak_htbl                      true
% 3.98/0.98  --gc_record_bc_elim                     false
% 3.98/0.98  
% 3.98/0.98  ------ Preprocessing Options
% 3.98/0.98  
% 3.98/0.98  --preprocessing_flag                    true
% 3.98/0.98  --time_out_prep_mult                    0.1
% 3.98/0.98  --splitting_mode                        input
% 3.98/0.98  --splitting_grd                         true
% 3.98/0.98  --splitting_cvd                         false
% 3.98/0.98  --splitting_cvd_svl                     false
% 3.98/0.98  --splitting_nvd                         32
% 3.98/0.98  --sub_typing                            true
% 3.98/0.98  --prep_gs_sim                           false
% 3.98/0.98  --prep_unflatten                        true
% 3.98/0.98  --prep_res_sim                          true
% 3.98/0.98  --prep_upred                            true
% 3.98/0.98  --prep_sem_filter                       exhaustive
% 3.98/0.98  --prep_sem_filter_out                   false
% 3.98/0.98  --pred_elim                             false
% 3.98/0.98  --res_sim_input                         true
% 3.98/0.98  --eq_ax_congr_red                       true
% 3.98/0.98  --pure_diseq_elim                       true
% 3.98/0.98  --brand_transform                       false
% 3.98/0.98  --non_eq_to_eq                          false
% 3.98/0.98  --prep_def_merge                        true
% 3.98/0.98  --prep_def_merge_prop_impl              false
% 3.98/0.98  --prep_def_merge_mbd                    true
% 3.98/0.98  --prep_def_merge_tr_red                 false
% 3.98/0.98  --prep_def_merge_tr_cl                  false
% 3.98/0.98  --smt_preprocessing                     true
% 3.98/0.98  --smt_ac_axioms                         fast
% 3.98/0.98  --preprocessed_out                      false
% 3.98/0.98  --preprocessed_stats                    false
% 3.98/0.98  
% 3.98/0.98  ------ Abstraction refinement Options
% 3.98/0.98  
% 3.98/0.98  --abstr_ref                             []
% 3.98/0.98  --abstr_ref_prep                        false
% 3.98/0.98  --abstr_ref_until_sat                   false
% 3.98/0.98  --abstr_ref_sig_restrict                funpre
% 3.98/0.98  --abstr_ref_af_restrict_to_split_sk     false
% 3.98/0.98  --abstr_ref_under                       []
% 3.98/0.98  
% 3.98/0.98  ------ SAT Options
% 3.98/0.98  
% 3.98/0.98  --sat_mode                              false
% 3.98/0.98  --sat_fm_restart_options                ""
% 3.98/0.98  --sat_gr_def                            false
% 3.98/0.98  --sat_epr_types                         true
% 3.98/0.98  --sat_non_cyclic_types                  false
% 3.98/0.98  --sat_finite_models                     false
% 3.98/0.98  --sat_fm_lemmas                         false
% 3.98/0.98  --sat_fm_prep                           false
% 3.98/0.98  --sat_fm_uc_incr                        true
% 3.98/0.98  --sat_out_model                         small
% 3.98/0.98  --sat_out_clauses                       false
% 3.98/0.98  
% 3.98/0.98  ------ QBF Options
% 3.98/0.98  
% 3.98/0.98  --qbf_mode                              false
% 3.98/0.98  --qbf_elim_univ                         false
% 3.98/0.98  --qbf_dom_inst                          none
% 3.98/0.98  --qbf_dom_pre_inst                      false
% 3.98/0.98  --qbf_sk_in                             false
% 3.98/0.98  --qbf_pred_elim                         true
% 3.98/0.98  --qbf_split                             512
% 3.98/0.98  
% 3.98/0.98  ------ BMC1 Options
% 3.98/0.98  
% 3.98/0.98  --bmc1_incremental                      false
% 3.98/0.98  --bmc1_axioms                           reachable_all
% 3.98/0.98  --bmc1_min_bound                        0
% 3.98/0.98  --bmc1_max_bound                        -1
% 3.98/0.98  --bmc1_max_bound_default                -1
% 3.98/0.98  --bmc1_symbol_reachability              true
% 3.98/0.98  --bmc1_property_lemmas                  false
% 3.98/0.98  --bmc1_k_induction                      false
% 3.98/0.98  --bmc1_non_equiv_states                 false
% 3.98/0.98  --bmc1_deadlock                         false
% 3.98/0.98  --bmc1_ucm                              false
% 3.98/0.98  --bmc1_add_unsat_core                   none
% 3.98/0.98  --bmc1_unsat_core_children              false
% 3.98/0.98  --bmc1_unsat_core_extrapolate_axioms    false
% 3.98/0.98  --bmc1_out_stat                         full
% 3.98/0.98  --bmc1_ground_init                      false
% 3.98/0.98  --bmc1_pre_inst_next_state              false
% 3.98/0.98  --bmc1_pre_inst_state                   false
% 3.98/0.98  --bmc1_pre_inst_reach_state             false
% 3.98/0.98  --bmc1_out_unsat_core                   false
% 3.98/0.98  --bmc1_aig_witness_out                  false
% 3.98/0.98  --bmc1_verbose                          false
% 3.98/0.98  --bmc1_dump_clauses_tptp                false
% 3.98/0.98  --bmc1_dump_unsat_core_tptp             false
% 3.98/0.98  --bmc1_dump_file                        -
% 3.98/0.98  --bmc1_ucm_expand_uc_limit              128
% 3.98/0.98  --bmc1_ucm_n_expand_iterations          6
% 3.98/0.98  --bmc1_ucm_extend_mode                  1
% 3.98/0.98  --bmc1_ucm_init_mode                    2
% 3.98/0.98  --bmc1_ucm_cone_mode                    none
% 3.98/0.98  --bmc1_ucm_reduced_relation_type        0
% 3.98/0.98  --bmc1_ucm_relax_model                  4
% 3.98/0.98  --bmc1_ucm_full_tr_after_sat            true
% 3.98/0.98  --bmc1_ucm_expand_neg_assumptions       false
% 3.98/0.98  --bmc1_ucm_layered_model                none
% 3.98/0.98  --bmc1_ucm_max_lemma_size               10
% 3.98/0.98  
% 3.98/0.98  ------ AIG Options
% 3.98/0.98  
% 3.98/0.98  --aig_mode                              false
% 3.98/0.98  
% 3.98/0.98  ------ Instantiation Options
% 3.98/0.98  
% 3.98/0.98  --instantiation_flag                    true
% 3.98/0.98  --inst_sos_flag                         false
% 3.98/0.98  --inst_sos_phase                        true
% 3.98/0.98  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 3.98/0.98  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 3.98/0.98  --inst_lit_sel_side                     num_symb
% 3.98/0.98  --inst_solver_per_active                1400
% 3.98/0.98  --inst_solver_calls_frac                1.
% 3.98/0.98  --inst_passive_queue_type               priority_queues
% 3.98/0.98  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 3.98/0.98  --inst_passive_queues_freq              [25;2]
% 3.98/0.98  --inst_dismatching                      true
% 3.98/0.98  --inst_eager_unprocessed_to_passive     true
% 3.98/0.98  --inst_prop_sim_given                   true
% 3.98/0.98  --inst_prop_sim_new                     false
% 3.98/0.98  --inst_subs_new                         false
% 3.98/0.98  --inst_eq_res_simp                      false
% 3.98/0.98  --inst_subs_given                       false
% 3.98/0.98  --inst_orphan_elimination               true
% 3.98/0.98  --inst_learning_loop_flag               true
% 3.98/0.98  --inst_learning_start                   3000
% 3.98/0.98  --inst_learning_factor                  2
% 3.98/0.98  --inst_start_prop_sim_after_learn       3
% 3.98/0.98  --inst_sel_renew                        solver
% 3.98/0.98  --inst_lit_activity_flag                true
% 3.98/0.98  --inst_restr_to_given                   false
% 3.98/0.98  --inst_activity_threshold               500
% 3.98/0.98  --inst_out_proof                        true
% 3.98/0.98  
% 3.98/0.98  ------ Resolution Options
% 3.98/0.98  
% 3.98/0.98  --resolution_flag                       true
% 3.98/0.98  --res_lit_sel                           adaptive
% 3.98/0.98  --res_lit_sel_side                      none
% 3.98/0.98  --res_ordering                          kbo
% 3.98/0.98  --res_to_prop_solver                    active
% 3.98/0.98  --res_prop_simpl_new                    false
% 3.98/0.98  --res_prop_simpl_given                  true
% 3.98/0.98  --res_passive_queue_type                priority_queues
% 3.98/0.98  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 3.98/0.98  --res_passive_queues_freq               [15;5]
% 3.98/0.98  --res_forward_subs                      full
% 3.98/0.98  --res_backward_subs                     full
% 3.98/0.98  --res_forward_subs_resolution           true
% 3.98/0.98  --res_backward_subs_resolution          true
% 3.98/0.98  --res_orphan_elimination                true
% 3.98/0.98  --res_time_limit                        2.
% 3.98/0.98  --res_out_proof                         true
% 3.98/0.98  
% 3.98/0.98  ------ Superposition Options
% 3.98/0.98  
% 3.98/0.98  --superposition_flag                    true
% 3.98/0.98  --sup_passive_queue_type                priority_queues
% 3.98/0.98  --sup_passive_queues                    [[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 3.98/0.98  --sup_passive_queues_freq               [1;4]
% 3.98/0.98  --demod_completeness_check              fast
% 3.98/0.98  --demod_use_ground                      true
% 3.98/0.98  --sup_to_prop_solver                    passive
% 3.98/0.98  --sup_prop_simpl_new                    true
% 3.98/0.98  --sup_prop_simpl_given                  true
% 3.98/0.98  --sup_fun_splitting                     false
% 3.98/0.98  --sup_smt_interval                      50000
% 3.98/0.98  
% 3.98/0.98  ------ Superposition Simplification Setup
% 3.98/0.98  
% 3.98/0.98  --sup_indices_passive                   []
% 3.98/0.98  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.98/0.98  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.98/0.98  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.98/0.98  --sup_full_triv                         [TrivRules;PropSubs]
% 3.98/0.98  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.98/0.98  --sup_full_bw                           [BwDemod]
% 3.98/0.98  --sup_immed_triv                        [TrivRules]
% 3.98/0.98  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 3.98/0.98  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.98/0.98  --sup_immed_bw_main                     []
% 3.98/0.98  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 3.98/0.98  --sup_input_triv                        [Unflattening;TrivRules]
% 3.98/0.98  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.98/0.98  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 3.98/0.98  
% 3.98/0.98  ------ Combination Options
% 3.98/0.98  
% 3.98/0.98  --comb_res_mult                         3
% 3.98/0.98  --comb_sup_mult                         2
% 3.98/0.98  --comb_inst_mult                        10
% 3.98/0.98  
% 3.98/0.98  ------ Debug Options
% 3.98/0.98  
% 3.98/0.98  --dbg_backtrace                         false
% 3.98/0.98  --dbg_dump_prop_clauses                 false
% 3.98/0.98  --dbg_dump_prop_clauses_file            -
% 3.98/0.98  --dbg_out_stat                          false
% 3.98/0.98  
% 3.98/0.98  
% 3.98/0.98  
% 3.98/0.98  
% 3.98/0.98  ------ Proving...
% 3.98/0.98  
% 3.98/0.98  
% 3.98/0.98  % SZS status Theorem for theBenchmark.p
% 3.98/0.98  
% 3.98/0.98  % SZS output start CNFRefutation for theBenchmark.p
% 3.98/0.98  
% 3.98/0.98  fof(f13,conjecture,(
% 3.98/0.98    ! [X0,X1,X2,X3] : (m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => (r1_tarski(k6_relat_1(X2),X3) => (r1_tarski(X2,k2_relset_1(X0,X1,X3)) & r1_tarski(X2,k1_relset_1(X0,X1,X3)))))),
% 3.98/0.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.98/0.98  
% 3.98/0.98  fof(f14,negated_conjecture,(
% 3.98/0.98    ~! [X0,X1,X2,X3] : (m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => (r1_tarski(k6_relat_1(X2),X3) => (r1_tarski(X2,k2_relset_1(X0,X1,X3)) & r1_tarski(X2,k1_relset_1(X0,X1,X3)))))),
% 3.98/0.98    inference(negated_conjecture,[],[f13])).
% 3.98/0.98  
% 3.98/0.98  fof(f24,plain,(
% 3.98/0.98    ? [X0,X1,X2,X3] : (((~r1_tarski(X2,k2_relset_1(X0,X1,X3)) | ~r1_tarski(X2,k1_relset_1(X0,X1,X3))) & r1_tarski(k6_relat_1(X2),X3)) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 3.98/0.98    inference(ennf_transformation,[],[f14])).
% 3.98/0.98  
% 3.98/0.98  fof(f25,plain,(
% 3.98/0.98    ? [X0,X1,X2,X3] : ((~r1_tarski(X2,k2_relset_1(X0,X1,X3)) | ~r1_tarski(X2,k1_relset_1(X0,X1,X3))) & r1_tarski(k6_relat_1(X2),X3) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 3.98/0.98    inference(flattening,[],[f24])).
% 3.98/0.98  
% 3.98/0.98  fof(f31,plain,(
% 3.98/0.98    ? [X0,X1,X2,X3] : ((~r1_tarski(X2,k2_relset_1(X0,X1,X3)) | ~r1_tarski(X2,k1_relset_1(X0,X1,X3))) & r1_tarski(k6_relat_1(X2),X3) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) => ((~r1_tarski(sK2,k2_relset_1(sK0,sK1,sK3)) | ~r1_tarski(sK2,k1_relset_1(sK0,sK1,sK3))) & r1_tarski(k6_relat_1(sK2),sK3) & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))))),
% 3.98/0.98    introduced(choice_axiom,[])).
% 3.98/0.98  
% 3.98/0.98  fof(f32,plain,(
% 3.98/0.98    (~r1_tarski(sK2,k2_relset_1(sK0,sK1,sK3)) | ~r1_tarski(sK2,k1_relset_1(sK0,sK1,sK3))) & r1_tarski(k6_relat_1(sK2),sK3) & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))),
% 3.98/0.98    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3])],[f25,f31])).
% 3.98/0.98  
% 3.98/0.98  fof(f52,plain,(
% 3.98/0.98    r1_tarski(k6_relat_1(sK2),sK3)),
% 3.98/0.98    inference(cnf_transformation,[],[f32])).
% 3.98/0.98  
% 3.98/0.98  fof(f1,axiom,(
% 3.98/0.98    ! [X0,X1] : (X0 = X1 <=> (r1_tarski(X1,X0) & r1_tarski(X0,X1)))),
% 3.98/0.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.98/0.98  
% 3.98/0.98  fof(f26,plain,(
% 3.98/0.98    ! [X0,X1] : ((X0 = X1 | (~r1_tarski(X1,X0) | ~r1_tarski(X0,X1))) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 3.98/0.98    inference(nnf_transformation,[],[f1])).
% 3.98/0.98  
% 3.98/0.98  fof(f27,plain,(
% 3.98/0.98    ! [X0,X1] : ((X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 3.98/0.99    inference(flattening,[],[f26])).
% 3.98/0.99  
% 3.98/0.99  fof(f34,plain,(
% 3.98/0.99    ( ! [X0,X1] : (r1_tarski(X1,X0) | X0 != X1) )),
% 3.98/0.99    inference(cnf_transformation,[],[f27])).
% 3.98/0.99  
% 3.98/0.99  fof(f54,plain,(
% 3.98/0.99    ( ! [X1] : (r1_tarski(X1,X1)) )),
% 3.98/0.99    inference(equality_resolution,[],[f34])).
% 3.98/0.99  
% 3.98/0.99  fof(f7,axiom,(
% 3.98/0.99    ! [X0,X1] : (v1_relat_1(X1) => (v5_relat_1(X1,X0) <=> r1_tarski(k2_relat_1(X1),X0)))),
% 3.98/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.98/0.99  
% 3.98/0.99  fof(f21,plain,(
% 3.98/0.99    ! [X0,X1] : ((v5_relat_1(X1,X0) <=> r1_tarski(k2_relat_1(X1),X0)) | ~v1_relat_1(X1))),
% 3.98/0.99    inference(ennf_transformation,[],[f7])).
% 3.98/0.99  
% 3.98/0.99  fof(f30,plain,(
% 3.98/0.99    ! [X0,X1] : (((v5_relat_1(X1,X0) | ~r1_tarski(k2_relat_1(X1),X0)) & (r1_tarski(k2_relat_1(X1),X0) | ~v5_relat_1(X1,X0))) | ~v1_relat_1(X1))),
% 3.98/0.99    inference(nnf_transformation,[],[f21])).
% 3.98/0.99  
% 3.98/0.99  fof(f44,plain,(
% 3.98/0.99    ( ! [X0,X1] : (v5_relat_1(X1,X0) | ~r1_tarski(k2_relat_1(X1),X0) | ~v1_relat_1(X1)) )),
% 3.98/0.99    inference(cnf_transformation,[],[f30])).
% 3.98/0.99  
% 3.98/0.99  fof(f2,axiom,(
% 3.98/0.99    ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) <=> r1_tarski(X0,X1))),
% 3.98/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.98/0.99  
% 3.98/0.99  fof(f28,plain,(
% 3.98/0.99    ! [X0,X1] : ((m1_subset_1(X0,k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1)) & (r1_tarski(X0,X1) | ~m1_subset_1(X0,k1_zfmisc_1(X1))))),
% 3.98/0.99    inference(nnf_transformation,[],[f2])).
% 3.98/0.99  
% 3.98/0.99  fof(f37,plain,(
% 3.98/0.99    ( ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1)) )),
% 3.98/0.99    inference(cnf_transformation,[],[f28])).
% 3.98/0.99  
% 3.98/0.99  fof(f5,axiom,(
% 3.98/0.99    ! [X0,X1] : ((v5_relat_1(X1,X0) & v1_relat_1(X1)) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(X1)) => v5_relat_1(X2,X0)))),
% 3.98/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.98/0.99  
% 3.98/0.99  fof(f18,plain,(
% 3.98/0.99    ! [X0,X1] : (! [X2] : (v5_relat_1(X2,X0) | ~m1_subset_1(X2,k1_zfmisc_1(X1))) | (~v5_relat_1(X1,X0) | ~v1_relat_1(X1)))),
% 3.98/0.99    inference(ennf_transformation,[],[f5])).
% 3.98/0.99  
% 3.98/0.99  fof(f19,plain,(
% 3.98/0.99    ! [X0,X1] : (! [X2] : (v5_relat_1(X2,X0) | ~m1_subset_1(X2,k1_zfmisc_1(X1))) | ~v5_relat_1(X1,X0) | ~v1_relat_1(X1))),
% 3.98/0.99    inference(flattening,[],[f18])).
% 3.98/0.99  
% 3.98/0.99  fof(f40,plain,(
% 3.98/0.99    ( ! [X2,X0,X1] : (v5_relat_1(X2,X0) | ~m1_subset_1(X2,k1_zfmisc_1(X1)) | ~v5_relat_1(X1,X0) | ~v1_relat_1(X1)) )),
% 3.98/0.99    inference(cnf_transformation,[],[f19])).
% 3.98/0.99  
% 3.98/0.99  fof(f3,axiom,(
% 3.98/0.99    ! [X0] : (v1_relat_1(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => v1_relat_1(X1)))),
% 3.98/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.98/0.99  
% 3.98/0.99  fof(f15,plain,(
% 3.98/0.99    ! [X0] : (! [X1] : (v1_relat_1(X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) | ~v1_relat_1(X0))),
% 3.98/0.99    inference(ennf_transformation,[],[f3])).
% 3.98/0.99  
% 3.98/0.99  fof(f38,plain,(
% 3.98/0.99    ( ! [X0,X1] : (v1_relat_1(X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0)) | ~v1_relat_1(X0)) )),
% 3.98/0.99    inference(cnf_transformation,[],[f15])).
% 3.98/0.99  
% 3.98/0.99  fof(f10,axiom,(
% 3.98/0.99    ! [X0] : (k2_relat_1(k6_relat_1(X0)) = X0 & k1_relat_1(k6_relat_1(X0)) = X0)),
% 3.98/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.98/0.99  
% 3.98/0.99  fof(f48,plain,(
% 3.98/0.99    ( ! [X0] : (k2_relat_1(k6_relat_1(X0)) = X0) )),
% 3.98/0.99    inference(cnf_transformation,[],[f10])).
% 3.98/0.99  
% 3.98/0.99  fof(f43,plain,(
% 3.98/0.99    ( ! [X0,X1] : (r1_tarski(k2_relat_1(X1),X0) | ~v5_relat_1(X1,X0) | ~v1_relat_1(X1)) )),
% 3.98/0.99    inference(cnf_transformation,[],[f30])).
% 3.98/0.99  
% 3.98/0.99  fof(f8,axiom,(
% 3.98/0.99    ! [X0] : v1_relat_1(k6_relat_1(X0))),
% 3.98/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.98/0.99  
% 3.98/0.99  fof(f45,plain,(
% 3.98/0.99    ( ! [X0] : (v1_relat_1(k6_relat_1(X0))) )),
% 3.98/0.99    inference(cnf_transformation,[],[f8])).
% 3.98/0.99  
% 3.98/0.99  fof(f6,axiom,(
% 3.98/0.99    ! [X0,X1] : (v1_relat_1(X1) => (v4_relat_1(X1,X0) <=> r1_tarski(k1_relat_1(X1),X0)))),
% 3.98/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.98/0.99  
% 3.98/0.99  fof(f20,plain,(
% 3.98/0.99    ! [X0,X1] : ((v4_relat_1(X1,X0) <=> r1_tarski(k1_relat_1(X1),X0)) | ~v1_relat_1(X1))),
% 3.98/0.99    inference(ennf_transformation,[],[f6])).
% 3.98/0.99  
% 3.98/0.99  fof(f29,plain,(
% 3.98/0.99    ! [X0,X1] : (((v4_relat_1(X1,X0) | ~r1_tarski(k1_relat_1(X1),X0)) & (r1_tarski(k1_relat_1(X1),X0) | ~v4_relat_1(X1,X0))) | ~v1_relat_1(X1))),
% 3.98/0.99    inference(nnf_transformation,[],[f20])).
% 3.98/0.99  
% 3.98/0.99  fof(f41,plain,(
% 3.98/0.99    ( ! [X0,X1] : (r1_tarski(k1_relat_1(X1),X0) | ~v4_relat_1(X1,X0) | ~v1_relat_1(X1)) )),
% 3.98/0.99    inference(cnf_transformation,[],[f29])).
% 3.98/0.99  
% 3.98/0.99  fof(f4,axiom,(
% 3.98/0.99    ! [X0,X1] : ((v4_relat_1(X1,X0) & v1_relat_1(X1)) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(X1)) => v4_relat_1(X2,X0)))),
% 3.98/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.98/0.99  
% 3.98/0.99  fof(f16,plain,(
% 3.98/0.99    ! [X0,X1] : (! [X2] : (v4_relat_1(X2,X0) | ~m1_subset_1(X2,k1_zfmisc_1(X1))) | (~v4_relat_1(X1,X0) | ~v1_relat_1(X1)))),
% 3.98/0.99    inference(ennf_transformation,[],[f4])).
% 3.98/0.99  
% 3.98/0.99  fof(f17,plain,(
% 3.98/0.99    ! [X0,X1] : (! [X2] : (v4_relat_1(X2,X0) | ~m1_subset_1(X2,k1_zfmisc_1(X1))) | ~v4_relat_1(X1,X0) | ~v1_relat_1(X1))),
% 3.98/0.99    inference(flattening,[],[f16])).
% 3.98/0.99  
% 3.98/0.99  fof(f39,plain,(
% 3.98/0.99    ( ! [X2,X0,X1] : (v4_relat_1(X2,X0) | ~m1_subset_1(X2,k1_zfmisc_1(X1)) | ~v4_relat_1(X1,X0) | ~v1_relat_1(X1)) )),
% 3.98/0.99    inference(cnf_transformation,[],[f17])).
% 3.98/0.99  
% 3.98/0.99  fof(f51,plain,(
% 3.98/0.99    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))),
% 3.98/0.99    inference(cnf_transformation,[],[f32])).
% 3.98/0.99  
% 3.98/0.99  fof(f12,axiom,(
% 3.98/0.99    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k2_relat_1(X2) = k2_relset_1(X0,X1,X2))),
% 3.98/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.98/0.99  
% 3.98/0.99  fof(f23,plain,(
% 3.98/0.99    ! [X0,X1,X2] : (k2_relat_1(X2) = k2_relset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 3.98/0.99    inference(ennf_transformation,[],[f12])).
% 3.98/0.99  
% 3.98/0.99  fof(f50,plain,(
% 3.98/0.99    ( ! [X2,X0,X1] : (k2_relat_1(X2) = k2_relset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 3.98/0.99    inference(cnf_transformation,[],[f23])).
% 3.98/0.99  
% 3.98/0.99  fof(f53,plain,(
% 3.98/0.99    ~r1_tarski(sK2,k2_relset_1(sK0,sK1,sK3)) | ~r1_tarski(sK2,k1_relset_1(sK0,sK1,sK3))),
% 3.98/0.99    inference(cnf_transformation,[],[f32])).
% 3.98/0.99  
% 3.98/0.99  fof(f47,plain,(
% 3.98/0.99    ( ! [X0] : (k1_relat_1(k6_relat_1(X0)) = X0) )),
% 3.98/0.99    inference(cnf_transformation,[],[f10])).
% 3.98/0.99  
% 3.98/0.99  fof(f42,plain,(
% 3.98/0.99    ( ! [X0,X1] : (v4_relat_1(X1,X0) | ~r1_tarski(k1_relat_1(X1),X0) | ~v1_relat_1(X1)) )),
% 3.98/0.99    inference(cnf_transformation,[],[f29])).
% 3.98/0.99  
% 3.98/0.99  fof(f36,plain,(
% 3.98/0.99    ( ! [X0,X1] : (r1_tarski(X0,X1) | ~m1_subset_1(X0,k1_zfmisc_1(X1))) )),
% 3.98/0.99    inference(cnf_transformation,[],[f28])).
% 3.98/0.99  
% 3.98/0.99  fof(f9,axiom,(
% 3.98/0.99    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1))),
% 3.98/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.98/0.99  
% 3.98/0.99  fof(f46,plain,(
% 3.98/0.99    ( ! [X0,X1] : (v1_relat_1(k2_zfmisc_1(X0,X1))) )),
% 3.98/0.99    inference(cnf_transformation,[],[f9])).
% 3.98/0.99  
% 3.98/0.99  fof(f11,axiom,(
% 3.98/0.99    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k1_relat_1(X2) = k1_relset_1(X0,X1,X2))),
% 3.98/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.98/0.99  
% 3.98/0.99  fof(f22,plain,(
% 3.98/0.99    ! [X0,X1,X2] : (k1_relat_1(X2) = k1_relset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 3.98/0.99    inference(ennf_transformation,[],[f11])).
% 3.98/0.99  
% 3.98/0.99  fof(f49,plain,(
% 3.98/0.99    ( ! [X2,X0,X1] : (k1_relat_1(X2) = k1_relset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 3.98/0.99    inference(cnf_transformation,[],[f22])).
% 3.98/0.99  
% 3.98/0.99  fof(f33,plain,(
% 3.98/0.99    ( ! [X0,X1] : (r1_tarski(X0,X1) | X0 != X1) )),
% 3.98/0.99    inference(cnf_transformation,[],[f27])).
% 3.98/0.99  
% 3.98/0.99  fof(f55,plain,(
% 3.98/0.99    ( ! [X1] : (r1_tarski(X1,X1)) )),
% 3.98/0.99    inference(equality_resolution,[],[f33])).
% 3.98/0.99  
% 3.98/0.99  cnf(c_19,negated_conjecture,
% 3.98/0.99      ( r1_tarski(k6_relat_1(sK2),sK3) ),
% 3.98/0.99      inference(cnf_transformation,[],[f52]) ).
% 3.98/0.99  
% 3.98/0.99  cnf(c_767,plain,
% 3.98/0.99      ( r1_tarski(k6_relat_1(sK2),sK3) = iProver_top ),
% 3.98/0.99      inference(predicate_to_equality,[status(thm)],[c_19]) ).
% 3.98/0.99  
% 3.98/0.99  cnf(c_1,plain,
% 3.98/0.99      ( r1_tarski(X0,X0) ),
% 3.98/0.99      inference(cnf_transformation,[],[f54]) ).
% 3.98/0.99  
% 3.98/0.99  cnf(c_781,plain,
% 3.98/0.99      ( r1_tarski(X0,X0) = iProver_top ),
% 3.98/0.99      inference(predicate_to_equality,[status(thm)],[c_1]) ).
% 3.98/0.99  
% 3.98/0.99  cnf(c_10,plain,
% 3.98/0.99      ( v5_relat_1(X0,X1)
% 3.98/0.99      | ~ r1_tarski(k2_relat_1(X0),X1)
% 3.98/0.99      | ~ v1_relat_1(X0) ),
% 3.98/0.99      inference(cnf_transformation,[],[f44]) ).
% 3.98/0.99  
% 3.98/0.99  cnf(c_774,plain,
% 3.98/0.99      ( v5_relat_1(X0,X1) = iProver_top
% 3.98/0.99      | r1_tarski(k2_relat_1(X0),X1) != iProver_top
% 3.98/0.99      | v1_relat_1(X0) != iProver_top ),
% 3.98/0.99      inference(predicate_to_equality,[status(thm)],[c_10]) ).
% 3.98/0.99  
% 3.98/0.99  cnf(c_1617,plain,
% 3.98/0.99      ( v5_relat_1(X0,k2_relat_1(X0)) = iProver_top
% 3.98/0.99      | v1_relat_1(X0) != iProver_top ),
% 3.98/0.99      inference(superposition,[status(thm)],[c_781,c_774]) ).
% 3.98/0.99  
% 3.98/0.99  cnf(c_3,plain,
% 3.98/0.99      ( m1_subset_1(X0,k1_zfmisc_1(X1)) | ~ r1_tarski(X0,X1) ),
% 3.98/0.99      inference(cnf_transformation,[],[f37]) ).
% 3.98/0.99  
% 3.98/0.99  cnf(c_780,plain,
% 3.98/0.99      ( m1_subset_1(X0,k1_zfmisc_1(X1)) = iProver_top
% 3.98/0.99      | r1_tarski(X0,X1) != iProver_top ),
% 3.98/0.99      inference(predicate_to_equality,[status(thm)],[c_3]) ).
% 3.98/0.99  
% 3.98/0.99  cnf(c_7,plain,
% 3.98/0.99      ( ~ v5_relat_1(X0,X1)
% 3.98/0.99      | v5_relat_1(X2,X1)
% 3.98/0.99      | ~ m1_subset_1(X2,k1_zfmisc_1(X0))
% 3.98/0.99      | ~ v1_relat_1(X0) ),
% 3.98/0.99      inference(cnf_transformation,[],[f40]) ).
% 3.98/0.99  
% 3.98/0.99  cnf(c_777,plain,
% 3.98/0.99      ( v5_relat_1(X0,X1) != iProver_top
% 3.98/0.99      | v5_relat_1(X2,X1) = iProver_top
% 3.98/0.99      | m1_subset_1(X2,k1_zfmisc_1(X0)) != iProver_top
% 3.98/0.99      | v1_relat_1(X0) != iProver_top ),
% 3.98/0.99      inference(predicate_to_equality,[status(thm)],[c_7]) ).
% 3.98/0.99  
% 3.98/0.99  cnf(c_1965,plain,
% 3.98/0.99      ( v5_relat_1(X0,X1) != iProver_top
% 3.98/0.99      | v5_relat_1(X2,X1) = iProver_top
% 3.98/0.99      | r1_tarski(X2,X0) != iProver_top
% 3.98/0.99      | v1_relat_1(X0) != iProver_top ),
% 3.98/0.99      inference(superposition,[status(thm)],[c_780,c_777]) ).
% 3.98/0.99  
% 3.98/0.99  cnf(c_4519,plain,
% 3.98/0.99      ( v5_relat_1(X0,k2_relat_1(X1)) = iProver_top
% 3.98/0.99      | r1_tarski(X0,X1) != iProver_top
% 3.98/0.99      | v1_relat_1(X1) != iProver_top ),
% 3.98/0.99      inference(superposition,[status(thm)],[c_1617,c_1965]) ).
% 3.98/0.99  
% 3.98/0.99  cnf(c_6417,plain,
% 3.98/0.99      ( v5_relat_1(X0,k2_relat_1(X1)) = iProver_top
% 3.98/0.99      | r1_tarski(X2,X1) != iProver_top
% 3.98/0.99      | r1_tarski(X0,X2) != iProver_top
% 3.98/0.99      | v1_relat_1(X2) != iProver_top
% 3.98/0.99      | v1_relat_1(X1) != iProver_top ),
% 3.98/0.99      inference(superposition,[status(thm)],[c_4519,c_1965]) ).
% 3.98/0.99  
% 3.98/0.99  cnf(c_5,plain,
% 3.98/0.99      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
% 3.98/0.99      | ~ v1_relat_1(X1)
% 3.98/0.99      | v1_relat_1(X0) ),
% 3.98/0.99      inference(cnf_transformation,[],[f38]) ).
% 3.98/0.99  
% 3.98/0.99  cnf(c_129,plain,
% 3.98/0.99      ( ~ r1_tarski(X0,X1) | m1_subset_1(X0,k1_zfmisc_1(X1)) ),
% 3.98/0.99      inference(prop_impl,[status(thm)],[c_3]) ).
% 3.98/0.99  
% 3.98/0.99  cnf(c_130,plain,
% 3.98/0.99      ( m1_subset_1(X0,k1_zfmisc_1(X1)) | ~ r1_tarski(X0,X1) ),
% 3.98/0.99      inference(renaming,[status(thm)],[c_129]) ).
% 3.98/0.99  
% 3.98/0.99  cnf(c_165,plain,
% 3.98/0.99      ( ~ r1_tarski(X0,X1) | ~ v1_relat_1(X1) | v1_relat_1(X0) ),
% 3.98/0.99      inference(bin_hyper_res,[status(thm)],[c_5,c_130]) ).
% 3.98/0.99  
% 3.98/0.99  cnf(c_765,plain,
% 3.98/0.99      ( r1_tarski(X0,X1) != iProver_top
% 3.98/0.99      | v1_relat_1(X1) != iProver_top
% 3.98/0.99      | v1_relat_1(X0) = iProver_top ),
% 3.98/0.99      inference(predicate_to_equality,[status(thm)],[c_165]) ).
% 3.98/0.99  
% 3.98/0.99  cnf(c_10697,plain,
% 3.98/0.99      ( v5_relat_1(X0,k2_relat_1(X1)) = iProver_top
% 3.98/0.99      | r1_tarski(X0,X2) != iProver_top
% 3.98/0.99      | r1_tarski(X2,X1) != iProver_top
% 3.98/0.99      | v1_relat_1(X1) != iProver_top ),
% 3.98/0.99      inference(forward_subsumption_resolution,
% 3.98/0.99                [status(thm)],
% 3.98/0.99                [c_6417,c_765]) ).
% 3.98/0.99  
% 3.98/0.99  cnf(c_10702,plain,
% 3.98/0.99      ( v5_relat_1(k6_relat_1(sK2),k2_relat_1(X0)) = iProver_top
% 3.98/0.99      | r1_tarski(sK3,X0) != iProver_top
% 3.98/0.99      | v1_relat_1(X0) != iProver_top ),
% 3.98/0.99      inference(superposition,[status(thm)],[c_767,c_10697]) ).
% 3.98/0.99  
% 3.98/0.99  cnf(c_14,plain,
% 3.98/0.99      ( k2_relat_1(k6_relat_1(X0)) = X0 ),
% 3.98/0.99      inference(cnf_transformation,[],[f48]) ).
% 3.98/0.99  
% 3.98/0.99  cnf(c_11,plain,
% 3.98/0.99      ( ~ v5_relat_1(X0,X1)
% 3.98/0.99      | r1_tarski(k2_relat_1(X0),X1)
% 3.98/0.99      | ~ v1_relat_1(X0) ),
% 3.98/0.99      inference(cnf_transformation,[],[f43]) ).
% 3.98/0.99  
% 3.98/0.99  cnf(c_773,plain,
% 3.98/0.99      ( v5_relat_1(X0,X1) != iProver_top
% 3.98/0.99      | r1_tarski(k2_relat_1(X0),X1) = iProver_top
% 3.98/0.99      | v1_relat_1(X0) != iProver_top ),
% 3.98/0.99      inference(predicate_to_equality,[status(thm)],[c_11]) ).
% 3.98/0.99  
% 3.98/0.99  cnf(c_1581,plain,
% 3.98/0.99      ( v5_relat_1(k6_relat_1(X0),X1) != iProver_top
% 3.98/0.99      | r1_tarski(X0,X1) = iProver_top
% 3.98/0.99      | v1_relat_1(k6_relat_1(X0)) != iProver_top ),
% 3.98/0.99      inference(superposition,[status(thm)],[c_14,c_773]) ).
% 3.98/0.99  
% 3.98/0.99  cnf(c_12,plain,
% 3.98/0.99      ( v1_relat_1(k6_relat_1(X0)) ),
% 3.98/0.99      inference(cnf_transformation,[],[f45]) ).
% 3.98/0.99  
% 3.98/0.99  cnf(c_35,plain,
% 3.98/0.99      ( v1_relat_1(k6_relat_1(X0)) = iProver_top ),
% 3.98/0.99      inference(predicate_to_equality,[status(thm)],[c_12]) ).
% 3.98/0.99  
% 3.98/0.99  cnf(c_1873,plain,
% 3.98/0.99      ( r1_tarski(X0,X1) = iProver_top
% 3.98/0.99      | v5_relat_1(k6_relat_1(X0),X1) != iProver_top ),
% 3.98/0.99      inference(global_propositional_subsumption,
% 3.98/0.99                [status(thm)],
% 3.98/0.99                [c_1581,c_35]) ).
% 3.98/0.99  
% 3.98/0.99  cnf(c_1874,plain,
% 3.98/0.99      ( v5_relat_1(k6_relat_1(X0),X1) != iProver_top
% 3.98/0.99      | r1_tarski(X0,X1) = iProver_top ),
% 3.98/0.99      inference(renaming,[status(thm)],[c_1873]) ).
% 3.98/0.99  
% 3.98/0.99  cnf(c_10876,plain,
% 3.98/0.99      ( r1_tarski(sK3,X0) != iProver_top
% 3.98/0.99      | r1_tarski(sK2,k2_relat_1(X0)) = iProver_top
% 3.98/0.99      | v1_relat_1(X0) != iProver_top ),
% 3.98/0.99      inference(superposition,[status(thm)],[c_10702,c_1874]) ).
% 3.98/0.99  
% 3.98/0.99  cnf(c_10966,plain,
% 3.98/0.99      ( r1_tarski(sK3,sK3) != iProver_top
% 3.98/0.99      | r1_tarski(sK2,k2_relat_1(sK3)) = iProver_top
% 3.98/0.99      | v1_relat_1(sK3) != iProver_top ),
% 3.98/0.99      inference(instantiation,[status(thm)],[c_10876]) ).
% 3.98/0.99  
% 3.98/0.99  cnf(c_9,plain,
% 3.98/0.99      ( ~ v4_relat_1(X0,X1)
% 3.98/0.99      | r1_tarski(k1_relat_1(X0),X1)
% 3.98/0.99      | ~ v1_relat_1(X0) ),
% 3.98/0.99      inference(cnf_transformation,[],[f41]) ).
% 3.98/0.99  
% 3.98/0.99  cnf(c_1345,plain,
% 3.98/0.99      ( ~ v4_relat_1(k6_relat_1(X0),X1)
% 3.98/0.99      | r1_tarski(k1_relat_1(k6_relat_1(X0)),X1)
% 3.98/0.99      | ~ v1_relat_1(k6_relat_1(X0)) ),
% 3.98/0.99      inference(instantiation,[status(thm)],[c_9]) ).
% 3.98/0.99  
% 3.98/0.99  cnf(c_2901,plain,
% 3.98/0.99      ( ~ v4_relat_1(k6_relat_1(sK2),X0)
% 3.98/0.99      | r1_tarski(k1_relat_1(k6_relat_1(sK2)),X0)
% 3.98/0.99      | ~ v1_relat_1(k6_relat_1(sK2)) ),
% 3.98/0.99      inference(instantiation,[status(thm)],[c_1345]) ).
% 3.98/0.99  
% 3.98/0.99  cnf(c_4423,plain,
% 3.98/0.99      ( ~ v4_relat_1(k6_relat_1(sK2),k1_relat_1(X0))
% 3.98/0.99      | r1_tarski(k1_relat_1(k6_relat_1(sK2)),k1_relat_1(X0))
% 3.98/0.99      | ~ v1_relat_1(k6_relat_1(sK2)) ),
% 3.98/0.99      inference(instantiation,[status(thm)],[c_2901]) ).
% 3.98/0.99  
% 3.98/0.99  cnf(c_4428,plain,
% 3.98/0.99      ( v4_relat_1(k6_relat_1(sK2),k1_relat_1(X0)) != iProver_top
% 3.98/0.99      | r1_tarski(k1_relat_1(k6_relat_1(sK2)),k1_relat_1(X0)) = iProver_top
% 3.98/0.99      | v1_relat_1(k6_relat_1(sK2)) != iProver_top ),
% 3.98/0.99      inference(predicate_to_equality,[status(thm)],[c_4423]) ).
% 3.98/0.99  
% 3.98/0.99  cnf(c_4430,plain,
% 3.98/0.99      ( v4_relat_1(k6_relat_1(sK2),k1_relat_1(sK3)) != iProver_top
% 3.98/0.99      | r1_tarski(k1_relat_1(k6_relat_1(sK2)),k1_relat_1(sK3)) = iProver_top
% 3.98/0.99      | v1_relat_1(k6_relat_1(sK2)) != iProver_top ),
% 3.98/0.99      inference(instantiation,[status(thm)],[c_4428]) ).
% 3.98/0.99  
% 3.98/0.99  cnf(c_6,plain,
% 3.98/0.99      ( ~ v4_relat_1(X0,X1)
% 3.98/0.99      | v4_relat_1(X2,X1)
% 3.98/0.99      | ~ m1_subset_1(X2,k1_zfmisc_1(X0))
% 3.98/0.99      | ~ v1_relat_1(X0) ),
% 3.98/0.99      inference(cnf_transformation,[],[f39]) ).
% 3.98/0.99  
% 3.98/0.99  cnf(c_1952,plain,
% 3.98/0.99      ( ~ v4_relat_1(X0,k1_relat_1(X0))
% 3.98/0.99      | v4_relat_1(X1,k1_relat_1(X0))
% 3.98/0.99      | ~ m1_subset_1(X1,k1_zfmisc_1(X0))
% 3.98/0.99      | ~ v1_relat_1(X0) ),
% 3.98/0.99      inference(instantiation,[status(thm)],[c_6]) ).
% 3.98/0.99  
% 3.98/0.99  cnf(c_4422,plain,
% 3.98/0.99      ( ~ v4_relat_1(X0,k1_relat_1(X0))
% 3.98/0.99      | v4_relat_1(k6_relat_1(sK2),k1_relat_1(X0))
% 3.98/0.99      | ~ m1_subset_1(k6_relat_1(sK2),k1_zfmisc_1(X0))
% 3.98/0.99      | ~ v1_relat_1(X0) ),
% 3.98/0.99      inference(instantiation,[status(thm)],[c_1952]) ).
% 3.98/0.99  
% 3.98/0.99  cnf(c_4424,plain,
% 3.98/0.99      ( v4_relat_1(X0,k1_relat_1(X0)) != iProver_top
% 3.98/0.99      | v4_relat_1(k6_relat_1(sK2),k1_relat_1(X0)) = iProver_top
% 3.98/0.99      | m1_subset_1(k6_relat_1(sK2),k1_zfmisc_1(X0)) != iProver_top
% 3.98/0.99      | v1_relat_1(X0) != iProver_top ),
% 3.98/0.99      inference(predicate_to_equality,[status(thm)],[c_4422]) ).
% 3.98/0.99  
% 3.98/0.99  cnf(c_4426,plain,
% 3.98/0.99      ( v4_relat_1(k6_relat_1(sK2),k1_relat_1(sK3)) = iProver_top
% 3.98/0.99      | v4_relat_1(sK3,k1_relat_1(sK3)) != iProver_top
% 3.98/0.99      | m1_subset_1(k6_relat_1(sK2),k1_zfmisc_1(sK3)) != iProver_top
% 3.98/0.99      | v1_relat_1(sK3) != iProver_top ),
% 3.98/0.99      inference(instantiation,[status(thm)],[c_4424]) ).
% 3.98/0.99  
% 3.98/0.99  cnf(c_3057,plain,
% 3.98/0.99      ( m1_subset_1(k6_relat_1(X0),k1_zfmisc_1(X1))
% 3.98/0.99      | ~ r1_tarski(k6_relat_1(X0),X1) ),
% 3.98/0.99      inference(instantiation,[status(thm)],[c_3]) ).
% 3.98/0.99  
% 3.98/0.99  cnf(c_4299,plain,
% 3.98/0.99      ( m1_subset_1(k6_relat_1(sK2),k1_zfmisc_1(sK3))
% 3.98/0.99      | ~ r1_tarski(k6_relat_1(sK2),sK3) ),
% 3.98/0.99      inference(instantiation,[status(thm)],[c_3057]) ).
% 3.98/0.99  
% 3.98/0.99  cnf(c_4300,plain,
% 3.98/0.99      ( m1_subset_1(k6_relat_1(sK2),k1_zfmisc_1(sK3)) = iProver_top
% 3.98/0.99      | r1_tarski(k6_relat_1(sK2),sK3) != iProver_top ),
% 3.98/0.99      inference(predicate_to_equality,[status(thm)],[c_4299]) ).
% 3.98/0.99  
% 3.98/0.99  cnf(c_346,plain,
% 3.98/0.99      ( ~ r1_tarski(X0,X1) | r1_tarski(X2,X3) | X2 != X0 | X3 != X1 ),
% 3.98/0.99      theory(equality) ).
% 3.98/0.99  
% 3.98/0.99  cnf(c_994,plain,
% 3.98/0.99      ( ~ r1_tarski(X0,X1)
% 3.98/0.99      | r1_tarski(sK2,k1_relset_1(sK0,sK1,sK3))
% 3.98/0.99      | k1_relset_1(sK0,sK1,sK3) != X1
% 3.98/0.99      | sK2 != X0 ),
% 3.98/0.99      inference(instantiation,[status(thm)],[c_346]) ).
% 3.98/0.99  
% 3.98/0.99  cnf(c_1854,plain,
% 3.98/0.99      ( ~ r1_tarski(k1_relat_1(k6_relat_1(sK2)),X0)
% 3.98/0.99      | r1_tarski(sK2,k1_relset_1(sK0,sK1,sK3))
% 3.98/0.99      | k1_relset_1(sK0,sK1,sK3) != X0
% 3.98/0.99      | sK2 != k1_relat_1(k6_relat_1(sK2)) ),
% 3.98/0.99      inference(instantiation,[status(thm)],[c_994]) ).
% 3.98/0.99  
% 3.98/0.99  cnf(c_2760,plain,
% 3.98/0.99      ( ~ r1_tarski(k1_relat_1(k6_relat_1(sK2)),k1_relat_1(sK3))
% 3.98/0.99      | r1_tarski(sK2,k1_relset_1(sK0,sK1,sK3))
% 3.98/0.99      | k1_relset_1(sK0,sK1,sK3) != k1_relat_1(sK3)
% 3.98/0.99      | sK2 != k1_relat_1(k6_relat_1(sK2)) ),
% 3.98/0.99      inference(instantiation,[status(thm)],[c_1854]) ).
% 3.98/0.99  
% 3.98/0.99  cnf(c_2761,plain,
% 3.98/0.99      ( k1_relset_1(sK0,sK1,sK3) != k1_relat_1(sK3)
% 3.98/0.99      | sK2 != k1_relat_1(k6_relat_1(sK2))
% 3.98/0.99      | r1_tarski(k1_relat_1(k6_relat_1(sK2)),k1_relat_1(sK3)) != iProver_top
% 3.98/0.99      | r1_tarski(sK2,k1_relset_1(sK0,sK1,sK3)) = iProver_top ),
% 3.98/0.99      inference(predicate_to_equality,[status(thm)],[c_2760]) ).
% 3.98/0.99  
% 3.98/0.99  cnf(c_20,negated_conjecture,
% 3.98/0.99      ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ),
% 3.98/0.99      inference(cnf_transformation,[],[f51]) ).
% 3.98/0.99  
% 3.98/0.99  cnf(c_766,plain,
% 3.98/0.99      ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) = iProver_top ),
% 3.98/0.99      inference(predicate_to_equality,[status(thm)],[c_20]) ).
% 3.98/0.99  
% 3.98/0.99  cnf(c_17,plain,
% 3.98/0.99      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.98/0.99      | k2_relset_1(X1,X2,X0) = k2_relat_1(X0) ),
% 3.98/0.99      inference(cnf_transformation,[],[f50]) ).
% 3.98/0.99  
% 3.98/0.99  cnf(c_769,plain,
% 3.98/0.99      ( k2_relset_1(X0,X1,X2) = k2_relat_1(X2)
% 3.98/0.99      | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
% 3.98/0.99      inference(predicate_to_equality,[status(thm)],[c_17]) ).
% 3.98/0.99  
% 3.98/0.99  cnf(c_1310,plain,
% 3.98/0.99      ( k2_relset_1(sK0,sK1,sK3) = k2_relat_1(sK3) ),
% 3.98/0.99      inference(superposition,[status(thm)],[c_766,c_769]) ).
% 3.98/0.99  
% 3.98/0.99  cnf(c_18,negated_conjecture,
% 3.98/0.99      ( ~ r1_tarski(sK2,k2_relset_1(sK0,sK1,sK3))
% 3.98/0.99      | ~ r1_tarski(sK2,k1_relset_1(sK0,sK1,sK3)) ),
% 3.98/0.99      inference(cnf_transformation,[],[f53]) ).
% 3.98/0.99  
% 3.98/0.99  cnf(c_768,plain,
% 3.98/0.99      ( r1_tarski(sK2,k2_relset_1(sK0,sK1,sK3)) != iProver_top
% 3.98/0.99      | r1_tarski(sK2,k1_relset_1(sK0,sK1,sK3)) != iProver_top ),
% 3.98/0.99      inference(predicate_to_equality,[status(thm)],[c_18]) ).
% 3.98/0.99  
% 3.98/0.99  cnf(c_2289,plain,
% 3.98/0.99      ( r1_tarski(sK2,k1_relset_1(sK0,sK1,sK3)) != iProver_top
% 3.98/0.99      | r1_tarski(sK2,k2_relat_1(sK3)) != iProver_top ),
% 3.98/0.99      inference(demodulation,[status(thm)],[c_1310,c_768]) ).
% 3.98/0.99  
% 3.98/0.99  cnf(c_15,plain,
% 3.98/0.99      ( k1_relat_1(k6_relat_1(X0)) = X0 ),
% 3.98/0.99      inference(cnf_transformation,[],[f47]) ).
% 3.98/0.99  
% 3.98/0.99  cnf(c_1572,plain,
% 3.98/0.99      ( k1_relat_1(k6_relat_1(sK2)) = sK2 ),
% 3.98/0.99      inference(instantiation,[status(thm)],[c_15]) ).
% 3.98/0.99  
% 3.98/0.99  cnf(c_345,plain,( X0 != X1 | X2 != X1 | X2 = X0 ),theory(equality) ).
% 3.98/0.99  
% 3.98/0.99  cnf(c_1058,plain,
% 3.98/0.99      ( X0 != X1 | sK2 != X1 | sK2 = X0 ),
% 3.98/0.99      inference(instantiation,[status(thm)],[c_345]) ).
% 3.98/0.99  
% 3.98/0.99  cnf(c_1203,plain,
% 3.98/0.99      ( X0 != sK2 | sK2 = X0 | sK2 != sK2 ),
% 3.98/0.99      inference(instantiation,[status(thm)],[c_1058]) ).
% 3.98/0.99  
% 3.98/0.99  cnf(c_1571,plain,
% 3.98/0.99      ( k1_relat_1(k6_relat_1(sK2)) != sK2
% 3.98/0.99      | sK2 = k1_relat_1(k6_relat_1(sK2))
% 3.98/0.99      | sK2 != sK2 ),
% 3.98/0.99      inference(instantiation,[status(thm)],[c_1203]) ).
% 3.98/0.99  
% 3.98/0.99  cnf(c_8,plain,
% 3.98/0.99      ( v4_relat_1(X0,X1)
% 3.98/0.99      | ~ r1_tarski(k1_relat_1(X0),X1)
% 3.98/0.99      | ~ v1_relat_1(X0) ),
% 3.98/0.99      inference(cnf_transformation,[],[f42]) ).
% 3.98/0.99  
% 3.98/0.99  cnf(c_1244,plain,
% 3.98/0.99      ( v4_relat_1(X0,k1_relat_1(X0)) | ~ v1_relat_1(X0) ),
% 3.98/0.99      inference(resolution,[status(thm)],[c_8,c_1]) ).
% 3.98/0.99  
% 3.98/0.99  cnf(c_1245,plain,
% 3.98/0.99      ( v4_relat_1(X0,k1_relat_1(X0)) = iProver_top
% 3.98/0.99      | v1_relat_1(X0) != iProver_top ),
% 3.98/0.99      inference(predicate_to_equality,[status(thm)],[c_1244]) ).
% 3.98/0.99  
% 3.98/0.99  cnf(c_1247,plain,
% 3.98/0.99      ( v4_relat_1(sK3,k1_relat_1(sK3)) = iProver_top
% 3.98/0.99      | v1_relat_1(sK3) != iProver_top ),
% 3.98/0.99      inference(instantiation,[status(thm)],[c_1245]) ).
% 3.98/0.99  
% 3.98/0.99  cnf(c_4,plain,
% 3.98/0.99      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1)) | r1_tarski(X0,X1) ),
% 3.98/0.99      inference(cnf_transformation,[],[f36]) ).
% 3.98/0.99  
% 3.98/0.99  cnf(c_1038,plain,
% 3.98/0.99      ( r1_tarski(sK3,k2_zfmisc_1(sK0,sK1)) ),
% 3.98/0.99      inference(resolution,[status(thm)],[c_4,c_20]) ).
% 3.98/0.99  
% 3.98/0.99  cnf(c_1130,plain,
% 3.98/0.99      ( ~ v1_relat_1(k2_zfmisc_1(sK0,sK1)) | v1_relat_1(sK3) ),
% 3.98/0.99      inference(resolution,[status(thm)],[c_165,c_1038]) ).
% 3.98/0.99  
% 3.98/0.99  cnf(c_13,plain,
% 3.98/0.99      ( v1_relat_1(k2_zfmisc_1(X0,X1)) ),
% 3.98/0.99      inference(cnf_transformation,[],[f46]) ).
% 3.98/0.99  
% 3.98/0.99  cnf(c_1136,plain,
% 3.98/0.99      ( v1_relat_1(sK3) ),
% 3.98/0.99      inference(forward_subsumption_resolution,
% 3.98/0.99                [status(thm)],
% 3.98/0.99                [c_1130,c_13]) ).
% 3.98/0.99  
% 3.98/0.99  cnf(c_1137,plain,
% 3.98/0.99      ( v1_relat_1(sK3) = iProver_top ),
% 3.98/0.99      inference(predicate_to_equality,[status(thm)],[c_1136]) ).
% 3.98/0.99  
% 3.98/0.99  cnf(c_1128,plain,
% 3.98/0.99      ( v1_relat_1(k6_relat_1(sK2)) | ~ v1_relat_1(sK3) ),
% 3.98/0.99      inference(resolution,[status(thm)],[c_165,c_19]) ).
% 3.98/0.99  
% 3.98/0.99  cnf(c_1129,plain,
% 3.98/0.99      ( v1_relat_1(k6_relat_1(sK2)) = iProver_top
% 3.98/0.99      | v1_relat_1(sK3) != iProver_top ),
% 3.98/0.99      inference(predicate_to_equality,[status(thm)],[c_1128]) ).
% 3.98/0.99  
% 3.98/0.99  cnf(c_344,plain,( X0 = X0 ),theory(equality) ).
% 3.98/0.99  
% 3.98/0.99  cnf(c_1053,plain,
% 3.98/0.99      ( sK2 = sK2 ),
% 3.98/0.99      inference(instantiation,[status(thm)],[c_344]) ).
% 3.98/0.99  
% 3.98/0.99  cnf(c_16,plain,
% 3.98/0.99      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.98/0.99      | k1_relset_1(X1,X2,X0) = k1_relat_1(X0) ),
% 3.98/0.99      inference(cnf_transformation,[],[f49]) ).
% 3.98/0.99  
% 3.98/0.99  cnf(c_987,plain,
% 3.98/0.99      ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
% 3.98/0.99      | k1_relset_1(sK0,sK1,sK3) = k1_relat_1(sK3) ),
% 3.98/0.99      inference(instantiation,[status(thm)],[c_16]) ).
% 3.98/0.99  
% 3.98/0.99  cnf(c_2,plain,
% 3.98/0.99      ( r1_tarski(X0,X0) ),
% 3.98/0.99      inference(cnf_transformation,[],[f55]) ).
% 3.98/0.99  
% 3.98/0.99  cnf(c_59,plain,
% 3.98/0.99      ( r1_tarski(X0,X0) = iProver_top ),
% 3.98/0.99      inference(predicate_to_equality,[status(thm)],[c_2]) ).
% 3.98/0.99  
% 3.98/0.99  cnf(c_61,plain,
% 3.98/0.99      ( r1_tarski(sK3,sK3) = iProver_top ),
% 3.98/0.99      inference(instantiation,[status(thm)],[c_59]) ).
% 3.98/0.99  
% 3.98/0.99  cnf(c_22,plain,
% 3.98/0.99      ( r1_tarski(k6_relat_1(sK2),sK3) = iProver_top ),
% 3.98/0.99      inference(predicate_to_equality,[status(thm)],[c_19]) ).
% 3.98/0.99  
% 3.98/0.99  cnf(contradiction,plain,
% 3.98/0.99      ( $false ),
% 3.98/0.99      inference(minisat,
% 3.98/0.99                [status(thm)],
% 3.98/0.99                [c_10966,c_4430,c_4426,c_4300,c_2761,c_2289,c_1572,
% 3.98/0.99                 c_1571,c_1247,c_1137,c_1129,c_1053,c_987,c_61,c_22,c_20]) ).
% 3.98/0.99  
% 3.98/0.99  
% 3.98/0.99  % SZS output end CNFRefutation for theBenchmark.p
% 3.98/0.99  
% 3.98/0.99  ------                               Statistics
% 3.98/0.99  
% 3.98/0.99  ------ Selected
% 3.98/0.99  
% 3.98/0.99  total_time:                             0.293
% 3.98/0.99  
%------------------------------------------------------------------------------
