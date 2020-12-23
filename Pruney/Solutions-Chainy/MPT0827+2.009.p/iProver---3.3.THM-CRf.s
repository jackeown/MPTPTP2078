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
% DateTime   : Thu Dec  3 11:55:12 EST 2020

% Result     : Theorem 19.56s
% Output     : CNFRefutation 19.56s
% Verified   : 
% Statistics : Number of formulae       :  144 ( 342 expanded)
%              Number of clauses        :   92 ( 159 expanded)
%              Number of leaves         :   18 (  63 expanded)
%              Depth                    :   19
%              Number of atoms          :  369 ( 917 expanded)
%              Number of equality atoms :  167 ( 249 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal clause size      :    8 (   2 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f14,conjecture,(
    ! [X0,X1,X2,X3] :
      ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => ( r1_tarski(k6_relat_1(X2),X3)
       => ( r1_tarski(X2,k2_relset_1(X0,X1,X3))
          & r1_tarski(X2,k1_relset_1(X0,X1,X3)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f15,negated_conjecture,(
    ~ ! [X0,X1,X2,X3] :
        ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
       => ( r1_tarski(k6_relat_1(X2),X3)
         => ( r1_tarski(X2,k2_relset_1(X0,X1,X3))
            & r1_tarski(X2,k1_relset_1(X0,X1,X3)) ) ) ) ),
    inference(negated_conjecture,[],[f14])).

fof(f27,plain,(
    ? [X0,X1,X2,X3] :
      ( ( ~ r1_tarski(X2,k2_relset_1(X0,X1,X3))
        | ~ r1_tarski(X2,k1_relset_1(X0,X1,X3)) )
      & r1_tarski(k6_relat_1(X2),X3)
      & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f15])).

fof(f28,plain,(
    ? [X0,X1,X2,X3] :
      ( ( ~ r1_tarski(X2,k2_relset_1(X0,X1,X3))
        | ~ r1_tarski(X2,k1_relset_1(X0,X1,X3)) )
      & r1_tarski(k6_relat_1(X2),X3)
      & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(flattening,[],[f27])).

fof(f32,plain,
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

fof(f33,plain,
    ( ( ~ r1_tarski(sK2,k2_relset_1(sK0,sK1,sK3))
      | ~ r1_tarski(sK2,k1_relset_1(sK0,sK1,sK3)) )
    & r1_tarski(k6_relat_1(sK2),sK3)
    & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3])],[f28,f32])).

fof(f53,plain,(
    r1_tarski(k6_relat_1(sK2),sK3) ),
    inference(cnf_transformation,[],[f33])).

fof(f9,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => r1_tarski(X0,k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0))) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f23,plain,(
    ! [X0] :
      ( r1_tarski(X0,k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0)))
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f45,plain,(
    ! [X0] :
      ( r1_tarski(X0,k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0)))
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f29,plain,(
    ! [X0,X1] :
      ( ( m1_subset_1(X0,k1_zfmisc_1(X1))
        | ~ r1_tarski(X0,X1) )
      & ( r1_tarski(X0,X1)
        | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ) ) ),
    inference(nnf_transformation,[],[f1])).

fof(f35,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f11,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => ( v5_relat_1(X2,X1)
        & v4_relat_1(X2,X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f24,plain,(
    ! [X0,X1,X2] :
      ( ( v5_relat_1(X2,X1)
        & v4_relat_1(X2,X0) )
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f48,plain,(
    ! [X2,X0,X1] :
      ( v4_relat_1(X2,X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( ( v4_relat_1(X1,X0)
        & v1_relat_1(X1) )
     => ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(X1))
         => v4_relat_1(X2,X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f17,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( v4_relat_1(X2,X0)
          | ~ m1_subset_1(X2,k1_zfmisc_1(X1)) )
      | ~ v4_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f18,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( v4_relat_1(X2,X0)
          | ~ m1_subset_1(X2,k1_zfmisc_1(X1)) )
      | ~ v4_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f17])).

fof(f37,plain,(
    ! [X2,X0,X1] :
      ( v4_relat_1(X2,X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(X1))
      | ~ v4_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f2,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(X0))
         => v1_relat_1(X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f16,plain,(
    ! [X0] :
      ( ! [X1] :
          ( v1_relat_1(X1)
          | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f36,plain,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f16])).

fof(f5,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ( v4_relat_1(X1,X0)
      <=> r1_tarski(k1_relat_1(X1),X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f21,plain,(
    ! [X0,X1] :
      ( ( v4_relat_1(X1,X0)
      <=> r1_tarski(k1_relat_1(X1),X0) )
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f30,plain,(
    ! [X0,X1] :
      ( ( ( v4_relat_1(X1,X0)
          | ~ r1_tarski(k1_relat_1(X1),X0) )
        & ( r1_tarski(k1_relat_1(X1),X0)
          | ~ v4_relat_1(X1,X0) ) )
      | ~ v1_relat_1(X1) ) ),
    inference(nnf_transformation,[],[f21])).

fof(f39,plain,(
    ! [X0,X1] :
      ( r1_tarski(k1_relat_1(X1),X0)
      | ~ v4_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f10,axiom,(
    ! [X0] :
      ( k2_relat_1(k6_relat_1(X0)) = X0
      & k1_relat_1(k6_relat_1(X0)) = X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f46,plain,(
    ! [X0] : k1_relat_1(k6_relat_1(X0)) = X0 ),
    inference(cnf_transformation,[],[f10])).

fof(f7,axiom,(
    ! [X0] : v1_relat_1(k6_relat_1(X0)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f43,plain,(
    ! [X0] : v1_relat_1(k6_relat_1(X0)) ),
    inference(cnf_transformation,[],[f7])).

fof(f6,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ( v5_relat_1(X1,X0)
      <=> r1_tarski(k2_relat_1(X1),X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f22,plain,(
    ! [X0,X1] :
      ( ( v5_relat_1(X1,X0)
      <=> r1_tarski(k2_relat_1(X1),X0) )
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f31,plain,(
    ! [X0,X1] :
      ( ( ( v5_relat_1(X1,X0)
          | ~ r1_tarski(k2_relat_1(X1),X0) )
        & ( r1_tarski(k2_relat_1(X1),X0)
          | ~ v5_relat_1(X1,X0) ) )
      | ~ v1_relat_1(X1) ) ),
    inference(nnf_transformation,[],[f22])).

fof(f42,plain,(
    ! [X0,X1] :
      ( v5_relat_1(X1,X0)
      | ~ r1_tarski(k2_relat_1(X1),X0)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( ( v5_relat_1(X1,X0)
        & v1_relat_1(X1) )
     => ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(X1))
         => v5_relat_1(X2,X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f19,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( v5_relat_1(X2,X0)
          | ~ m1_subset_1(X2,k1_zfmisc_1(X1)) )
      | ~ v5_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f20,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( v5_relat_1(X2,X0)
          | ~ m1_subset_1(X2,k1_zfmisc_1(X1)) )
      | ~ v5_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f19])).

fof(f38,plain,(
    ! [X2,X0,X1] :
      ( v5_relat_1(X2,X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(X1))
      | ~ v5_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f47,plain,(
    ! [X0] : k2_relat_1(k6_relat_1(X0)) = X0 ),
    inference(cnf_transformation,[],[f10])).

fof(f41,plain,(
    ! [X0,X1] :
      ( r1_tarski(k2_relat_1(X1),X0)
      | ~ v5_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f52,plain,(
    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ),
    inference(cnf_transformation,[],[f33])).

fof(f13,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k2_relat_1(X2) = k2_relset_1(X0,X1,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f26,plain,(
    ! [X0,X1,X2] :
      ( k2_relat_1(X2) = k2_relset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f51,plain,(
    ! [X2,X0,X1] :
      ( k2_relat_1(X2) = k2_relset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f54,plain,
    ( ~ r1_tarski(sK2,k2_relset_1(sK0,sK1,sK3))
    | ~ r1_tarski(sK2,k1_relset_1(sK0,sK1,sK3)) ),
    inference(cnf_transformation,[],[f33])).

fof(f34,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f8,axiom,(
    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f44,plain,(
    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1)) ),
    inference(cnf_transformation,[],[f8])).

fof(f12,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k1_relat_1(X2) = k1_relset_1(X0,X1,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f25,plain,(
    ! [X0,X1,X2] :
      ( k1_relat_1(X2) = k1_relset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f50,plain,(
    ! [X2,X0,X1] :
      ( k1_relat_1(X2) = k1_relset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f25])).

cnf(c_19,negated_conjecture,
    ( r1_tarski(k6_relat_1(sK2),sK3) ),
    inference(cnf_transformation,[],[f53])).

cnf(c_663,plain,
    ( r1_tarski(k6_relat_1(sK2),sK3) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_19])).

cnf(c_11,plain,
    ( r1_tarski(X0,k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0)))
    | ~ v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f45])).

cnf(c_669,plain,
    ( r1_tarski(X0,k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0))) = iProver_top
    | v1_relat_1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_11])).

cnf(c_0,plain,
    ( ~ r1_tarski(X0,X1)
    | m1_subset_1(X0,k1_zfmisc_1(X1)) ),
    inference(cnf_transformation,[],[f35])).

cnf(c_679,plain,
    ( r1_tarski(X0,X1) != iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(X1)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_0])).

cnf(c_15,plain,
    ( v4_relat_1(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) ),
    inference(cnf_transformation,[],[f48])).

cnf(c_667,plain,
    ( v4_relat_1(X0,X1) = iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_15])).

cnf(c_1093,plain,
    ( v4_relat_1(X0,X1) = iProver_top
    | r1_tarski(X0,k2_zfmisc_1(X1,X2)) != iProver_top ),
    inference(superposition,[status(thm)],[c_679,c_667])).

cnf(c_2770,plain,
    ( v4_relat_1(X0,k1_relat_1(X0)) = iProver_top
    | v1_relat_1(X0) != iProver_top ),
    inference(superposition,[status(thm)],[c_669,c_1093])).

cnf(c_3,plain,
    ( ~ v4_relat_1(X0,X1)
    | v4_relat_1(X2,X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(X0))
    | ~ v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f37])).

cnf(c_677,plain,
    ( v4_relat_1(X0,X1) != iProver_top
    | v4_relat_1(X2,X1) = iProver_top
    | m1_subset_1(X2,k1_zfmisc_1(X0)) != iProver_top
    | v1_relat_1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3])).

cnf(c_2273,plain,
    ( v4_relat_1(X0,X1) != iProver_top
    | v4_relat_1(X2,X1) = iProver_top
    | r1_tarski(X2,X0) != iProver_top
    | v1_relat_1(X0) != iProver_top ),
    inference(superposition,[status(thm)],[c_679,c_677])).

cnf(c_5743,plain,
    ( v4_relat_1(X0,k1_relat_1(X1)) = iProver_top
    | r1_tarski(X0,X1) != iProver_top
    | v1_relat_1(X1) != iProver_top ),
    inference(superposition,[status(thm)],[c_2770,c_2273])).

cnf(c_11710,plain,
    ( v4_relat_1(X0,k1_relat_1(X1)) = iProver_top
    | r1_tarski(X2,X1) != iProver_top
    | r1_tarski(X0,X2) != iProver_top
    | v1_relat_1(X2) != iProver_top
    | v1_relat_1(X1) != iProver_top ),
    inference(superposition,[status(thm)],[c_5743,c_2273])).

cnf(c_2,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | ~ v1_relat_1(X1)
    | v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f36])).

cnf(c_135,plain,
    ( ~ r1_tarski(X0,X1)
    | m1_subset_1(X0,k1_zfmisc_1(X1)) ),
    inference(prop_impl,[status(thm)],[c_0])).

cnf(c_170,plain,
    ( ~ r1_tarski(X0,X1)
    | ~ v1_relat_1(X1)
    | v1_relat_1(X0) ),
    inference(bin_hyper_res,[status(thm)],[c_2,c_135])).

cnf(c_661,plain,
    ( r1_tarski(X0,X1) != iProver_top
    | v1_relat_1(X1) != iProver_top
    | v1_relat_1(X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_170])).

cnf(c_82798,plain,
    ( v4_relat_1(X0,k1_relat_1(X1)) = iProver_top
    | r1_tarski(X0,X2) != iProver_top
    | r1_tarski(X2,X1) != iProver_top
    | v1_relat_1(X1) != iProver_top ),
    inference(forward_subsumption_resolution,[status(thm)],[c_11710,c_661])).

cnf(c_82803,plain,
    ( v4_relat_1(k6_relat_1(sK2),k1_relat_1(X0)) = iProver_top
    | r1_tarski(sK3,X0) != iProver_top
    | v1_relat_1(X0) != iProver_top ),
    inference(superposition,[status(thm)],[c_663,c_82798])).

cnf(c_82900,plain,
    ( v4_relat_1(k6_relat_1(sK2),k1_relat_1(sK3)) = iProver_top
    | r1_tarski(sK3,sK3) != iProver_top
    | v1_relat_1(sK3) != iProver_top ),
    inference(instantiation,[status(thm)],[c_82803])).

cnf(c_6,plain,
    ( ~ v4_relat_1(X0,X1)
    | r1_tarski(k1_relat_1(X0),X1)
    | ~ v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f39])).

cnf(c_21388,plain,
    ( ~ v4_relat_1(X0,k1_relat_1(X1))
    | r1_tarski(k1_relat_1(X0),k1_relat_1(X1))
    | ~ v1_relat_1(X0) ),
    inference(instantiation,[status(thm)],[c_6])).

cnf(c_62743,plain,
    ( ~ v4_relat_1(k6_relat_1(sK2),k1_relat_1(sK3))
    | r1_tarski(k1_relat_1(k6_relat_1(sK2)),k1_relat_1(sK3))
    | ~ v1_relat_1(k6_relat_1(sK2)) ),
    inference(instantiation,[status(thm)],[c_21388])).

cnf(c_62744,plain,
    ( v4_relat_1(k6_relat_1(sK2),k1_relat_1(sK3)) != iProver_top
    | r1_tarski(k1_relat_1(k6_relat_1(sK2)),k1_relat_1(sK3)) = iProver_top
    | v1_relat_1(k6_relat_1(sK2)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_62743])).

cnf(c_13,plain,
    ( k1_relat_1(k6_relat_1(X0)) = X0 ),
    inference(cnf_transformation,[],[f46])).

cnf(c_674,plain,
    ( v4_relat_1(X0,X1) != iProver_top
    | r1_tarski(k1_relat_1(X0),X1) = iProver_top
    | v1_relat_1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_6])).

cnf(c_1725,plain,
    ( v4_relat_1(k6_relat_1(X0),X1) != iProver_top
    | r1_tarski(X0,X1) = iProver_top
    | v1_relat_1(k6_relat_1(X0)) != iProver_top ),
    inference(superposition,[status(thm)],[c_13,c_674])).

cnf(c_9,plain,
    ( v1_relat_1(k6_relat_1(X0)) ),
    inference(cnf_transformation,[],[f43])).

cnf(c_44,plain,
    ( v1_relat_1(k6_relat_1(X0)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_9])).

cnf(c_2149,plain,
    ( r1_tarski(X0,X1) = iProver_top
    | v4_relat_1(k6_relat_1(X0),X1) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_1725,c_44])).

cnf(c_2150,plain,
    ( v4_relat_1(k6_relat_1(X0),X1) != iProver_top
    | r1_tarski(X0,X1) = iProver_top ),
    inference(renaming,[status(thm)],[c_2149])).

cnf(c_3043,plain,
    ( r1_tarski(X0,k1_relat_1(k6_relat_1(X0))) = iProver_top
    | v1_relat_1(k6_relat_1(X0)) != iProver_top ),
    inference(superposition,[status(thm)],[c_2770,c_2150])).

cnf(c_3046,plain,
    ( r1_tarski(X0,X0) = iProver_top
    | v1_relat_1(k6_relat_1(X0)) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_3043,c_13])).

cnf(c_3053,plain,
    ( r1_tarski(X0,X0) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_3046,c_44])).

cnf(c_7,plain,
    ( v5_relat_1(X0,X1)
    | ~ r1_tarski(k2_relat_1(X0),X1)
    | ~ v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f42])).

cnf(c_673,plain,
    ( v5_relat_1(X0,X1) = iProver_top
    | r1_tarski(k2_relat_1(X0),X1) != iProver_top
    | v1_relat_1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_7])).

cnf(c_3062,plain,
    ( v5_relat_1(X0,k2_relat_1(X0)) = iProver_top
    | v1_relat_1(X0) != iProver_top ),
    inference(superposition,[status(thm)],[c_3053,c_673])).

cnf(c_4,plain,
    ( ~ v5_relat_1(X0,X1)
    | v5_relat_1(X2,X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(X0))
    | ~ v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f38])).

cnf(c_676,plain,
    ( v5_relat_1(X0,X1) != iProver_top
    | v5_relat_1(X2,X1) = iProver_top
    | m1_subset_1(X2,k1_zfmisc_1(X0)) != iProver_top
    | v1_relat_1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_4])).

cnf(c_1953,plain,
    ( v5_relat_1(X0,X1) != iProver_top
    | v5_relat_1(X2,X1) = iProver_top
    | r1_tarski(X2,X0) != iProver_top
    | v1_relat_1(X0) != iProver_top ),
    inference(superposition,[status(thm)],[c_679,c_676])).

cnf(c_5076,plain,
    ( v5_relat_1(X0,k2_relat_1(X1)) = iProver_top
    | r1_tarski(X0,X1) != iProver_top
    | v1_relat_1(X1) != iProver_top ),
    inference(superposition,[status(thm)],[c_3062,c_1953])).

cnf(c_8997,plain,
    ( v5_relat_1(X0,k2_relat_1(X1)) = iProver_top
    | r1_tarski(X2,X1) != iProver_top
    | r1_tarski(X0,X2) != iProver_top
    | v1_relat_1(X2) != iProver_top
    | v1_relat_1(X1) != iProver_top ),
    inference(superposition,[status(thm)],[c_5076,c_1953])).

cnf(c_37323,plain,
    ( v5_relat_1(X0,k2_relat_1(X1)) = iProver_top
    | r1_tarski(X0,X2) != iProver_top
    | r1_tarski(X2,X1) != iProver_top
    | v1_relat_1(X1) != iProver_top ),
    inference(forward_subsumption_resolution,[status(thm)],[c_8997,c_661])).

cnf(c_37328,plain,
    ( v5_relat_1(k6_relat_1(sK2),k2_relat_1(X0)) = iProver_top
    | r1_tarski(sK3,X0) != iProver_top
    | v1_relat_1(X0) != iProver_top ),
    inference(superposition,[status(thm)],[c_663,c_37323])).

cnf(c_12,plain,
    ( k2_relat_1(k6_relat_1(X0)) = X0 ),
    inference(cnf_transformation,[],[f47])).

cnf(c_8,plain,
    ( ~ v5_relat_1(X0,X1)
    | r1_tarski(k2_relat_1(X0),X1)
    | ~ v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f41])).

cnf(c_672,plain,
    ( v5_relat_1(X0,X1) != iProver_top
    | r1_tarski(k2_relat_1(X0),X1) = iProver_top
    | v1_relat_1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_8])).

cnf(c_1452,plain,
    ( v5_relat_1(k6_relat_1(X0),X1) != iProver_top
    | r1_tarski(X0,X1) = iProver_top
    | v1_relat_1(k6_relat_1(X0)) != iProver_top ),
    inference(superposition,[status(thm)],[c_12,c_672])).

cnf(c_1974,plain,
    ( r1_tarski(X0,X1) = iProver_top
    | v5_relat_1(k6_relat_1(X0),X1) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_1452,c_44])).

cnf(c_1975,plain,
    ( v5_relat_1(k6_relat_1(X0),X1) != iProver_top
    | r1_tarski(X0,X1) = iProver_top ),
    inference(renaming,[status(thm)],[c_1974])).

cnf(c_38192,plain,
    ( r1_tarski(sK3,X0) != iProver_top
    | r1_tarski(sK2,k2_relat_1(X0)) = iProver_top
    | v1_relat_1(X0) != iProver_top ),
    inference(superposition,[status(thm)],[c_37328,c_1975])).

cnf(c_38241,plain,
    ( r1_tarski(sK3,sK3) != iProver_top
    | r1_tarski(sK2,k2_relat_1(sK3)) = iProver_top
    | v1_relat_1(sK3) != iProver_top ),
    inference(instantiation,[status(thm)],[c_38192])).

cnf(c_227,plain,
    ( ~ r1_tarski(X0,X1)
    | r1_tarski(X2,X3)
    | X2 != X0
    | X3 != X1 ),
    theory(equality)).

cnf(c_6311,plain,
    ( ~ r1_tarski(X0,X1)
    | r1_tarski(sK2,k1_relset_1(sK0,sK1,sK3))
    | k1_relset_1(sK0,sK1,sK3) != X1
    | sK2 != X0 ),
    inference(instantiation,[status(thm)],[c_227])).

cnf(c_17532,plain,
    ( ~ r1_tarski(k1_relat_1(k6_relat_1(sK2)),X0)
    | r1_tarski(sK2,k1_relset_1(sK0,sK1,sK3))
    | k1_relset_1(sK0,sK1,sK3) != X0
    | sK2 != k1_relat_1(k6_relat_1(sK2)) ),
    inference(instantiation,[status(thm)],[c_6311])).

cnf(c_31425,plain,
    ( ~ r1_tarski(k1_relat_1(k6_relat_1(sK2)),k1_relat_1(sK3))
    | r1_tarski(sK2,k1_relset_1(sK0,sK1,sK3))
    | k1_relset_1(sK0,sK1,sK3) != k1_relat_1(sK3)
    | sK2 != k1_relat_1(k6_relat_1(sK2)) ),
    inference(instantiation,[status(thm)],[c_17532])).

cnf(c_31426,plain,
    ( k1_relset_1(sK0,sK1,sK3) != k1_relat_1(sK3)
    | sK2 != k1_relat_1(k6_relat_1(sK2))
    | r1_tarski(k1_relat_1(k6_relat_1(sK2)),k1_relat_1(sK3)) != iProver_top
    | r1_tarski(sK2,k1_relset_1(sK0,sK1,sK3)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_31425])).

cnf(c_224,plain,
    ( X0 != X1
    | X2 != X1
    | X2 = X0 ),
    theory(equality)).

cnf(c_2204,plain,
    ( X0 != X1
    | sK2 != X1
    | sK2 = X0 ),
    inference(instantiation,[status(thm)],[c_224])).

cnf(c_4879,plain,
    ( X0 != sK2
    | sK2 = X0
    | sK2 != sK2 ),
    inference(instantiation,[status(thm)],[c_2204])).

cnf(c_11347,plain,
    ( k1_relat_1(k6_relat_1(sK2)) != sK2
    | sK2 = k1_relat_1(k6_relat_1(sK2))
    | sK2 != sK2 ),
    inference(instantiation,[status(thm)],[c_4879])).

cnf(c_223,plain,
    ( X0 = X0 ),
    theory(equality)).

cnf(c_4880,plain,
    ( sK2 = sK2 ),
    inference(instantiation,[status(thm)],[c_223])).

cnf(c_1372,plain,
    ( r1_tarski(k6_relat_1(X0),k2_zfmisc_1(k1_relat_1(k6_relat_1(X0)),X0)) = iProver_top
    | v1_relat_1(k6_relat_1(X0)) != iProver_top ),
    inference(superposition,[status(thm)],[c_12,c_669])).

cnf(c_1376,plain,
    ( r1_tarski(k6_relat_1(X0),k2_zfmisc_1(X0,X0)) = iProver_top
    | v1_relat_1(k6_relat_1(X0)) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_1372,c_13])).

cnf(c_1386,plain,
    ( r1_tarski(k6_relat_1(X0),k2_zfmisc_1(X0,X0)) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_1376,c_44])).

cnf(c_2772,plain,
    ( v4_relat_1(k6_relat_1(X0),X0) = iProver_top ),
    inference(superposition,[status(thm)],[c_1386,c_1093])).

cnf(c_2795,plain,
    ( v4_relat_1(k6_relat_1(sK3),sK3) = iProver_top ),
    inference(instantiation,[status(thm)],[c_2772])).

cnf(c_20,negated_conjecture,
    ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ),
    inference(cnf_transformation,[],[f52])).

cnf(c_662,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_20])).

cnf(c_17,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k2_relset_1(X1,X2,X0) = k2_relat_1(X0) ),
    inference(cnf_transformation,[],[f51])).

cnf(c_665,plain,
    ( k2_relset_1(X0,X1,X2) = k2_relat_1(X2)
    | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_17])).

cnf(c_1438,plain,
    ( k2_relset_1(sK0,sK1,sK3) = k2_relat_1(sK3) ),
    inference(superposition,[status(thm)],[c_662,c_665])).

cnf(c_18,negated_conjecture,
    ( ~ r1_tarski(sK2,k2_relset_1(sK0,sK1,sK3))
    | ~ r1_tarski(sK2,k1_relset_1(sK0,sK1,sK3)) ),
    inference(cnf_transformation,[],[f54])).

cnf(c_664,plain,
    ( r1_tarski(sK2,k2_relset_1(sK0,sK1,sK3)) != iProver_top
    | r1_tarski(sK2,k1_relset_1(sK0,sK1,sK3)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_18])).

cnf(c_2666,plain,
    ( r1_tarski(sK2,k1_relset_1(sK0,sK1,sK3)) != iProver_top
    | r1_tarski(sK2,k2_relat_1(sK3)) != iProver_top ),
    inference(demodulation,[status(thm)],[c_1438,c_664])).

cnf(c_2152,plain,
    ( v4_relat_1(k6_relat_1(sK3),sK3) != iProver_top
    | r1_tarski(sK3,sK3) = iProver_top ),
    inference(instantiation,[status(thm)],[c_2150])).

cnf(c_1311,plain,
    ( k1_relat_1(k6_relat_1(sK2)) = sK2 ),
    inference(instantiation,[status(thm)],[c_13])).

cnf(c_1,plain,
    ( r1_tarski(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ),
    inference(cnf_transformation,[],[f34])).

cnf(c_881,plain,
    ( r1_tarski(sK3,k2_zfmisc_1(sK0,sK1)) ),
    inference(resolution,[status(thm)],[c_1,c_20])).

cnf(c_930,plain,
    ( ~ v1_relat_1(k2_zfmisc_1(sK0,sK1))
    | v1_relat_1(sK3) ),
    inference(resolution,[status(thm)],[c_170,c_881])).

cnf(c_10,plain,
    ( v1_relat_1(k2_zfmisc_1(X0,X1)) ),
    inference(cnf_transformation,[],[f44])).

cnf(c_970,plain,
    ( v1_relat_1(sK3) ),
    inference(forward_subsumption_resolution,[status(thm)],[c_930,c_10])).

cnf(c_971,plain,
    ( v1_relat_1(sK3) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_970])).

cnf(c_16,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k1_relset_1(X1,X2,X0) = k1_relat_1(X0) ),
    inference(cnf_transformation,[],[f50])).

cnf(c_883,plain,
    ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    | k1_relset_1(sK0,sK1,sK3) = k1_relat_1(sK3) ),
    inference(instantiation,[status(thm)],[c_16])).

cnf(c_853,plain,
    ( ~ r1_tarski(k6_relat_1(sK2),sK3)
    | v1_relat_1(k6_relat_1(sK2))
    | ~ v1_relat_1(sK3) ),
    inference(instantiation,[status(thm)],[c_170])).

cnf(c_854,plain,
    ( r1_tarski(k6_relat_1(sK2),sK3) != iProver_top
    | v1_relat_1(k6_relat_1(sK2)) = iProver_top
    | v1_relat_1(sK3) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_853])).

cnf(c_22,plain,
    ( r1_tarski(k6_relat_1(sK2),sK3) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_19])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_82900,c_62744,c_38241,c_31426,c_11347,c_4880,c_2795,c_2666,c_2152,c_1311,c_971,c_883,c_854,c_22,c_20])).

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
% 0.13/0.34  % DateTime   : Tue Dec  1 16:33:12 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running in FOF mode
% 19.56/3.00  % SZS status Started for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 19.56/3.00  
% 19.56/3.00  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 19.56/3.00  
% 19.56/3.00  ------  iProver source info
% 19.56/3.00  
% 19.56/3.00  git: date: 2020-06-30 10:37:57 +0100
% 19.56/3.00  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 19.56/3.00  git: non_committed_changes: false
% 19.56/3.00  git: last_make_outside_of_git: false
% 19.56/3.00  
% 19.56/3.00  ------ 
% 19.56/3.00  
% 19.56/3.00  ------ Input Options
% 19.56/3.00  
% 19.56/3.00  --out_options                           all
% 19.56/3.00  --tptp_safe_out                         true
% 19.56/3.00  --problem_path                          ""
% 19.56/3.00  --include_path                          ""
% 19.56/3.00  --clausifier                            res/vclausify_rel
% 19.56/3.00  --clausifier_options                    --mode clausify
% 19.56/3.00  --stdin                                 false
% 19.56/3.00  --stats_out                             sel
% 19.56/3.00  
% 19.56/3.00  ------ General Options
% 19.56/3.00  
% 19.56/3.00  --fof                                   false
% 19.56/3.00  --time_out_real                         604.99
% 19.56/3.00  --time_out_virtual                      -1.
% 19.56/3.00  --symbol_type_check                     false
% 19.56/3.00  --clausify_out                          false
% 19.56/3.00  --sig_cnt_out                           false
% 19.56/3.00  --trig_cnt_out                          false
% 19.56/3.00  --trig_cnt_out_tolerance                1.
% 19.56/3.00  --trig_cnt_out_sk_spl                   false
% 19.56/3.00  --abstr_cl_out                          false
% 19.56/3.00  
% 19.56/3.00  ------ Global Options
% 19.56/3.00  
% 19.56/3.00  --schedule                              none
% 19.56/3.00  --add_important_lit                     false
% 19.56/3.00  --prop_solver_per_cl                    1000
% 19.56/3.00  --min_unsat_core                        false
% 19.56/3.00  --soft_assumptions                      false
% 19.56/3.00  --soft_lemma_size                       3
% 19.56/3.00  --prop_impl_unit_size                   0
% 19.56/3.00  --prop_impl_unit                        []
% 19.56/3.00  --share_sel_clauses                     true
% 19.56/3.00  --reset_solvers                         false
% 19.56/3.00  --bc_imp_inh                            [conj_cone]
% 19.56/3.00  --conj_cone_tolerance                   3.
% 19.56/3.00  --extra_neg_conj                        none
% 19.56/3.00  --large_theory_mode                     true
% 19.56/3.00  --prolific_symb_bound                   200
% 19.56/3.00  --lt_threshold                          2000
% 19.56/3.00  --clause_weak_htbl                      true
% 19.56/3.00  --gc_record_bc_elim                     false
% 19.56/3.00  
% 19.56/3.00  ------ Preprocessing Options
% 19.56/3.00  
% 19.56/3.00  --preprocessing_flag                    true
% 19.56/3.00  --time_out_prep_mult                    0.1
% 19.56/3.00  --splitting_mode                        input
% 19.56/3.00  --splitting_grd                         true
% 19.56/3.00  --splitting_cvd                         false
% 19.56/3.00  --splitting_cvd_svl                     false
% 19.56/3.00  --splitting_nvd                         32
% 19.56/3.00  --sub_typing                            true
% 19.56/3.00  --prep_gs_sim                           false
% 19.56/3.00  --prep_unflatten                        true
% 19.56/3.00  --prep_res_sim                          true
% 19.56/3.00  --prep_upred                            true
% 19.56/3.00  --prep_sem_filter                       exhaustive
% 19.56/3.00  --prep_sem_filter_out                   false
% 19.56/3.00  --pred_elim                             false
% 19.56/3.00  --res_sim_input                         true
% 19.56/3.00  --eq_ax_congr_red                       true
% 19.56/3.00  --pure_diseq_elim                       true
% 19.56/3.00  --brand_transform                       false
% 19.56/3.00  --non_eq_to_eq                          false
% 19.56/3.00  --prep_def_merge                        true
% 19.56/3.00  --prep_def_merge_prop_impl              false
% 19.56/3.00  --prep_def_merge_mbd                    true
% 19.56/3.00  --prep_def_merge_tr_red                 false
% 19.56/3.00  --prep_def_merge_tr_cl                  false
% 19.56/3.00  --smt_preprocessing                     true
% 19.56/3.00  --smt_ac_axioms                         fast
% 19.56/3.00  --preprocessed_out                      false
% 19.56/3.00  --preprocessed_stats                    false
% 19.56/3.00  
% 19.56/3.00  ------ Abstraction refinement Options
% 19.56/3.00  
% 19.56/3.00  --abstr_ref                             []
% 19.56/3.00  --abstr_ref_prep                        false
% 19.56/3.00  --abstr_ref_until_sat                   false
% 19.56/3.00  --abstr_ref_sig_restrict                funpre
% 19.56/3.00  --abstr_ref_af_restrict_to_split_sk     false
% 19.56/3.00  --abstr_ref_under                       []
% 19.56/3.00  
% 19.56/3.00  ------ SAT Options
% 19.56/3.00  
% 19.56/3.00  --sat_mode                              false
% 19.56/3.00  --sat_fm_restart_options                ""
% 19.56/3.00  --sat_gr_def                            false
% 19.56/3.00  --sat_epr_types                         true
% 19.56/3.00  --sat_non_cyclic_types                  false
% 19.56/3.00  --sat_finite_models                     false
% 19.56/3.00  --sat_fm_lemmas                         false
% 19.56/3.00  --sat_fm_prep                           false
% 19.56/3.00  --sat_fm_uc_incr                        true
% 19.56/3.00  --sat_out_model                         small
% 19.56/3.00  --sat_out_clauses                       false
% 19.56/3.00  
% 19.56/3.00  ------ QBF Options
% 19.56/3.00  
% 19.56/3.00  --qbf_mode                              false
% 19.56/3.00  --qbf_elim_univ                         false
% 19.56/3.00  --qbf_dom_inst                          none
% 19.56/3.00  --qbf_dom_pre_inst                      false
% 19.56/3.00  --qbf_sk_in                             false
% 19.56/3.00  --qbf_pred_elim                         true
% 19.56/3.00  --qbf_split                             512
% 19.56/3.00  
% 19.56/3.00  ------ BMC1 Options
% 19.56/3.00  
% 19.56/3.00  --bmc1_incremental                      false
% 19.56/3.00  --bmc1_axioms                           reachable_all
% 19.56/3.00  --bmc1_min_bound                        0
% 19.56/3.00  --bmc1_max_bound                        -1
% 19.56/3.00  --bmc1_max_bound_default                -1
% 19.56/3.00  --bmc1_symbol_reachability              true
% 19.56/3.00  --bmc1_property_lemmas                  false
% 19.56/3.00  --bmc1_k_induction                      false
% 19.56/3.00  --bmc1_non_equiv_states                 false
% 19.56/3.00  --bmc1_deadlock                         false
% 19.56/3.00  --bmc1_ucm                              false
% 19.56/3.00  --bmc1_add_unsat_core                   none
% 19.56/3.00  --bmc1_unsat_core_children              false
% 19.56/3.00  --bmc1_unsat_core_extrapolate_axioms    false
% 19.56/3.00  --bmc1_out_stat                         full
% 19.56/3.00  --bmc1_ground_init                      false
% 19.56/3.00  --bmc1_pre_inst_next_state              false
% 19.56/3.00  --bmc1_pre_inst_state                   false
% 19.56/3.00  --bmc1_pre_inst_reach_state             false
% 19.56/3.00  --bmc1_out_unsat_core                   false
% 19.56/3.00  --bmc1_aig_witness_out                  false
% 19.56/3.00  --bmc1_verbose                          false
% 19.56/3.00  --bmc1_dump_clauses_tptp                false
% 19.56/3.00  --bmc1_dump_unsat_core_tptp             false
% 19.56/3.00  --bmc1_dump_file                        -
% 19.56/3.00  --bmc1_ucm_expand_uc_limit              128
% 19.56/3.00  --bmc1_ucm_n_expand_iterations          6
% 19.56/3.00  --bmc1_ucm_extend_mode                  1
% 19.56/3.00  --bmc1_ucm_init_mode                    2
% 19.56/3.00  --bmc1_ucm_cone_mode                    none
% 19.56/3.00  --bmc1_ucm_reduced_relation_type        0
% 19.56/3.00  --bmc1_ucm_relax_model                  4
% 19.56/3.00  --bmc1_ucm_full_tr_after_sat            true
% 19.56/3.00  --bmc1_ucm_expand_neg_assumptions       false
% 19.56/3.00  --bmc1_ucm_layered_model                none
% 19.56/3.00  --bmc1_ucm_max_lemma_size               10
% 19.56/3.00  
% 19.56/3.00  ------ AIG Options
% 19.56/3.00  
% 19.56/3.00  --aig_mode                              false
% 19.56/3.00  
% 19.56/3.00  ------ Instantiation Options
% 19.56/3.00  
% 19.56/3.00  --instantiation_flag                    true
% 19.56/3.00  --inst_sos_flag                         false
% 19.56/3.00  --inst_sos_phase                        true
% 19.56/3.00  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 19.56/3.00  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 19.56/3.00  --inst_lit_sel_side                     num_symb
% 19.56/3.00  --inst_solver_per_active                1400
% 19.56/3.00  --inst_solver_calls_frac                1.
% 19.56/3.00  --inst_passive_queue_type               priority_queues
% 19.56/3.00  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 19.56/3.00  --inst_passive_queues_freq              [25;2]
% 19.56/3.00  --inst_dismatching                      true
% 19.56/3.00  --inst_eager_unprocessed_to_passive     true
% 19.56/3.00  --inst_prop_sim_given                   true
% 19.56/3.00  --inst_prop_sim_new                     false
% 19.56/3.00  --inst_subs_new                         false
% 19.56/3.00  --inst_eq_res_simp                      false
% 19.56/3.00  --inst_subs_given                       false
% 19.56/3.00  --inst_orphan_elimination               true
% 19.56/3.00  --inst_learning_loop_flag               true
% 19.56/3.00  --inst_learning_start                   3000
% 19.56/3.00  --inst_learning_factor                  2
% 19.56/3.00  --inst_start_prop_sim_after_learn       3
% 19.56/3.00  --inst_sel_renew                        solver
% 19.56/3.00  --inst_lit_activity_flag                true
% 19.56/3.00  --inst_restr_to_given                   false
% 19.56/3.00  --inst_activity_threshold               500
% 19.56/3.00  --inst_out_proof                        true
% 19.56/3.00  
% 19.56/3.00  ------ Resolution Options
% 19.56/3.00  
% 19.56/3.00  --resolution_flag                       true
% 19.56/3.00  --res_lit_sel                           adaptive
% 19.56/3.00  --res_lit_sel_side                      none
% 19.56/3.00  --res_ordering                          kbo
% 19.56/3.00  --res_to_prop_solver                    active
% 19.56/3.00  --res_prop_simpl_new                    false
% 19.56/3.00  --res_prop_simpl_given                  true
% 19.56/3.00  --res_passive_queue_type                priority_queues
% 19.56/3.00  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 19.56/3.00  --res_passive_queues_freq               [15;5]
% 19.56/3.00  --res_forward_subs                      full
% 19.56/3.00  --res_backward_subs                     full
% 19.56/3.00  --res_forward_subs_resolution           true
% 19.56/3.00  --res_backward_subs_resolution          true
% 19.56/3.00  --res_orphan_elimination                true
% 19.56/3.00  --res_time_limit                        2.
% 19.56/3.00  --res_out_proof                         true
% 19.56/3.00  
% 19.56/3.00  ------ Superposition Options
% 19.56/3.00  
% 19.56/3.00  --superposition_flag                    true
% 19.56/3.00  --sup_passive_queue_type                priority_queues
% 19.56/3.00  --sup_passive_queues                    [[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 19.56/3.00  --sup_passive_queues_freq               [1;4]
% 19.56/3.00  --demod_completeness_check              fast
% 19.56/3.00  --demod_use_ground                      true
% 19.56/3.00  --sup_to_prop_solver                    passive
% 19.56/3.00  --sup_prop_simpl_new                    true
% 19.56/3.00  --sup_prop_simpl_given                  true
% 19.56/3.00  --sup_fun_splitting                     false
% 19.56/3.00  --sup_smt_interval                      50000
% 19.56/3.00  
% 19.56/3.00  ------ Superposition Simplification Setup
% 19.56/3.00  
% 19.56/3.00  --sup_indices_passive                   []
% 19.56/3.00  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 19.56/3.00  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 19.56/3.00  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 19.56/3.00  --sup_full_triv                         [TrivRules;PropSubs]
% 19.56/3.00  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 19.56/3.00  --sup_full_bw                           [BwDemod]
% 19.56/3.00  --sup_immed_triv                        [TrivRules]
% 19.56/3.00  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 19.56/3.00  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 19.56/3.00  --sup_immed_bw_main                     []
% 19.56/3.00  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 19.56/3.00  --sup_input_triv                        [Unflattening;TrivRules]
% 19.56/3.00  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 19.56/3.00  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 19.56/3.00  
% 19.56/3.00  ------ Combination Options
% 19.56/3.00  
% 19.56/3.00  --comb_res_mult                         3
% 19.56/3.00  --comb_sup_mult                         2
% 19.56/3.00  --comb_inst_mult                        10
% 19.56/3.00  
% 19.56/3.00  ------ Debug Options
% 19.56/3.00  
% 19.56/3.00  --dbg_backtrace                         false
% 19.56/3.00  --dbg_dump_prop_clauses                 false
% 19.56/3.00  --dbg_dump_prop_clauses_file            -
% 19.56/3.00  --dbg_out_stat                          false
% 19.56/3.00  ------ Parsing...
% 19.56/3.00  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 19.56/3.00  
% 19.56/3.00  ------ Preprocessing... sf_s  rm: 1 0s  sf_e 
% 19.56/3.00  
% 19.56/3.00  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 19.56/3.00  
% 19.56/3.00  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 19.56/3.00  ------ Proving...
% 19.56/3.00  ------ Problem Properties 
% 19.56/3.00  
% 19.56/3.00  
% 19.56/3.00  clauses                                 21
% 19.56/3.00  conjectures                             3
% 19.56/3.00  EPR                                     1
% 19.56/3.00  Horn                                    21
% 19.56/3.00  unary                                   6
% 19.56/3.00  binary                                  8
% 19.56/3.00  lits                                    45
% 19.56/3.00  lits eq                                 4
% 19.56/3.00  fd_pure                                 0
% 19.56/3.00  fd_pseudo                               0
% 19.56/3.00  fd_cond                                 0
% 19.56/3.00  fd_pseudo_cond                          0
% 19.56/3.00  AC symbols                              0
% 19.56/3.00  
% 19.56/3.00  ------ Input Options Time Limit: Unbounded
% 19.56/3.00  
% 19.56/3.00  
% 19.56/3.00  ------ 
% 19.56/3.00  Current options:
% 19.56/3.00  ------ 
% 19.56/3.00  
% 19.56/3.00  ------ Input Options
% 19.56/3.00  
% 19.56/3.00  --out_options                           all
% 19.56/3.00  --tptp_safe_out                         true
% 19.56/3.00  --problem_path                          ""
% 19.56/3.00  --include_path                          ""
% 19.56/3.00  --clausifier                            res/vclausify_rel
% 19.56/3.00  --clausifier_options                    --mode clausify
% 19.56/3.00  --stdin                                 false
% 19.56/3.00  --stats_out                             sel
% 19.56/3.00  
% 19.56/3.00  ------ General Options
% 19.56/3.00  
% 19.56/3.00  --fof                                   false
% 19.56/3.00  --time_out_real                         604.99
% 19.56/3.00  --time_out_virtual                      -1.
% 19.56/3.00  --symbol_type_check                     false
% 19.56/3.00  --clausify_out                          false
% 19.56/3.00  --sig_cnt_out                           false
% 19.56/3.00  --trig_cnt_out                          false
% 19.56/3.00  --trig_cnt_out_tolerance                1.
% 19.56/3.00  --trig_cnt_out_sk_spl                   false
% 19.56/3.00  --abstr_cl_out                          false
% 19.56/3.00  
% 19.56/3.00  ------ Global Options
% 19.56/3.00  
% 19.56/3.00  --schedule                              none
% 19.56/3.00  --add_important_lit                     false
% 19.56/3.00  --prop_solver_per_cl                    1000
% 19.56/3.00  --min_unsat_core                        false
% 19.56/3.00  --soft_assumptions                      false
% 19.56/3.00  --soft_lemma_size                       3
% 19.56/3.00  --prop_impl_unit_size                   0
% 19.56/3.00  --prop_impl_unit                        []
% 19.56/3.00  --share_sel_clauses                     true
% 19.56/3.00  --reset_solvers                         false
% 19.56/3.00  --bc_imp_inh                            [conj_cone]
% 19.56/3.00  --conj_cone_tolerance                   3.
% 19.56/3.00  --extra_neg_conj                        none
% 19.56/3.00  --large_theory_mode                     true
% 19.56/3.00  --prolific_symb_bound                   200
% 19.56/3.00  --lt_threshold                          2000
% 19.56/3.00  --clause_weak_htbl                      true
% 19.56/3.00  --gc_record_bc_elim                     false
% 19.56/3.00  
% 19.56/3.00  ------ Preprocessing Options
% 19.56/3.00  
% 19.56/3.00  --preprocessing_flag                    true
% 19.56/3.00  --time_out_prep_mult                    0.1
% 19.56/3.00  --splitting_mode                        input
% 19.56/3.00  --splitting_grd                         true
% 19.56/3.00  --splitting_cvd                         false
% 19.56/3.00  --splitting_cvd_svl                     false
% 19.56/3.00  --splitting_nvd                         32
% 19.56/3.00  --sub_typing                            true
% 19.56/3.00  --prep_gs_sim                           false
% 19.56/3.00  --prep_unflatten                        true
% 19.56/3.00  --prep_res_sim                          true
% 19.56/3.00  --prep_upred                            true
% 19.56/3.00  --prep_sem_filter                       exhaustive
% 19.56/3.00  --prep_sem_filter_out                   false
% 19.56/3.00  --pred_elim                             false
% 19.56/3.00  --res_sim_input                         true
% 19.56/3.00  --eq_ax_congr_red                       true
% 19.56/3.00  --pure_diseq_elim                       true
% 19.56/3.00  --brand_transform                       false
% 19.56/3.00  --non_eq_to_eq                          false
% 19.56/3.00  --prep_def_merge                        true
% 19.56/3.00  --prep_def_merge_prop_impl              false
% 19.56/3.00  --prep_def_merge_mbd                    true
% 19.56/3.00  --prep_def_merge_tr_red                 false
% 19.56/3.00  --prep_def_merge_tr_cl                  false
% 19.56/3.00  --smt_preprocessing                     true
% 19.56/3.00  --smt_ac_axioms                         fast
% 19.56/3.00  --preprocessed_out                      false
% 19.56/3.00  --preprocessed_stats                    false
% 19.56/3.00  
% 19.56/3.00  ------ Abstraction refinement Options
% 19.56/3.00  
% 19.56/3.00  --abstr_ref                             []
% 19.56/3.00  --abstr_ref_prep                        false
% 19.56/3.00  --abstr_ref_until_sat                   false
% 19.56/3.00  --abstr_ref_sig_restrict                funpre
% 19.56/3.00  --abstr_ref_af_restrict_to_split_sk     false
% 19.56/3.00  --abstr_ref_under                       []
% 19.56/3.00  
% 19.56/3.00  ------ SAT Options
% 19.56/3.00  
% 19.56/3.00  --sat_mode                              false
% 19.56/3.00  --sat_fm_restart_options                ""
% 19.56/3.00  --sat_gr_def                            false
% 19.56/3.00  --sat_epr_types                         true
% 19.56/3.00  --sat_non_cyclic_types                  false
% 19.56/3.00  --sat_finite_models                     false
% 19.56/3.00  --sat_fm_lemmas                         false
% 19.56/3.00  --sat_fm_prep                           false
% 19.56/3.00  --sat_fm_uc_incr                        true
% 19.56/3.00  --sat_out_model                         small
% 19.56/3.00  --sat_out_clauses                       false
% 19.56/3.00  
% 19.56/3.00  ------ QBF Options
% 19.56/3.00  
% 19.56/3.00  --qbf_mode                              false
% 19.56/3.00  --qbf_elim_univ                         false
% 19.56/3.00  --qbf_dom_inst                          none
% 19.56/3.00  --qbf_dom_pre_inst                      false
% 19.56/3.00  --qbf_sk_in                             false
% 19.56/3.00  --qbf_pred_elim                         true
% 19.56/3.00  --qbf_split                             512
% 19.56/3.00  
% 19.56/3.00  ------ BMC1 Options
% 19.56/3.00  
% 19.56/3.00  --bmc1_incremental                      false
% 19.56/3.00  --bmc1_axioms                           reachable_all
% 19.56/3.00  --bmc1_min_bound                        0
% 19.56/3.00  --bmc1_max_bound                        -1
% 19.56/3.00  --bmc1_max_bound_default                -1
% 19.56/3.00  --bmc1_symbol_reachability              true
% 19.56/3.00  --bmc1_property_lemmas                  false
% 19.56/3.00  --bmc1_k_induction                      false
% 19.56/3.00  --bmc1_non_equiv_states                 false
% 19.56/3.00  --bmc1_deadlock                         false
% 19.56/3.00  --bmc1_ucm                              false
% 19.56/3.00  --bmc1_add_unsat_core                   none
% 19.56/3.00  --bmc1_unsat_core_children              false
% 19.56/3.00  --bmc1_unsat_core_extrapolate_axioms    false
% 19.56/3.00  --bmc1_out_stat                         full
% 19.56/3.00  --bmc1_ground_init                      false
% 19.56/3.00  --bmc1_pre_inst_next_state              false
% 19.56/3.00  --bmc1_pre_inst_state                   false
% 19.56/3.00  --bmc1_pre_inst_reach_state             false
% 19.56/3.00  --bmc1_out_unsat_core                   false
% 19.56/3.00  --bmc1_aig_witness_out                  false
% 19.56/3.00  --bmc1_verbose                          false
% 19.56/3.00  --bmc1_dump_clauses_tptp                false
% 19.56/3.00  --bmc1_dump_unsat_core_tptp             false
% 19.56/3.00  --bmc1_dump_file                        -
% 19.56/3.00  --bmc1_ucm_expand_uc_limit              128
% 19.56/3.00  --bmc1_ucm_n_expand_iterations          6
% 19.56/3.00  --bmc1_ucm_extend_mode                  1
% 19.56/3.00  --bmc1_ucm_init_mode                    2
% 19.56/3.00  --bmc1_ucm_cone_mode                    none
% 19.56/3.00  --bmc1_ucm_reduced_relation_type        0
% 19.56/3.00  --bmc1_ucm_relax_model                  4
% 19.56/3.00  --bmc1_ucm_full_tr_after_sat            true
% 19.56/3.00  --bmc1_ucm_expand_neg_assumptions       false
% 19.56/3.00  --bmc1_ucm_layered_model                none
% 19.56/3.00  --bmc1_ucm_max_lemma_size               10
% 19.56/3.00  
% 19.56/3.00  ------ AIG Options
% 19.56/3.00  
% 19.56/3.00  --aig_mode                              false
% 19.56/3.00  
% 19.56/3.00  ------ Instantiation Options
% 19.56/3.00  
% 19.56/3.00  --instantiation_flag                    true
% 19.56/3.00  --inst_sos_flag                         false
% 19.56/3.00  --inst_sos_phase                        true
% 19.56/3.00  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 19.56/3.00  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 19.56/3.00  --inst_lit_sel_side                     num_symb
% 19.56/3.00  --inst_solver_per_active                1400
% 19.56/3.00  --inst_solver_calls_frac                1.
% 19.56/3.00  --inst_passive_queue_type               priority_queues
% 19.56/3.00  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 19.56/3.00  --inst_passive_queues_freq              [25;2]
% 19.56/3.00  --inst_dismatching                      true
% 19.56/3.00  --inst_eager_unprocessed_to_passive     true
% 19.56/3.00  --inst_prop_sim_given                   true
% 19.56/3.00  --inst_prop_sim_new                     false
% 19.56/3.00  --inst_subs_new                         false
% 19.56/3.00  --inst_eq_res_simp                      false
% 19.56/3.00  --inst_subs_given                       false
% 19.56/3.00  --inst_orphan_elimination               true
% 19.56/3.00  --inst_learning_loop_flag               true
% 19.56/3.00  --inst_learning_start                   3000
% 19.56/3.00  --inst_learning_factor                  2
% 19.56/3.00  --inst_start_prop_sim_after_learn       3
% 19.56/3.00  --inst_sel_renew                        solver
% 19.56/3.00  --inst_lit_activity_flag                true
% 19.56/3.00  --inst_restr_to_given                   false
% 19.56/3.00  --inst_activity_threshold               500
% 19.56/3.00  --inst_out_proof                        true
% 19.56/3.00  
% 19.56/3.00  ------ Resolution Options
% 19.56/3.00  
% 19.56/3.00  --resolution_flag                       true
% 19.56/3.00  --res_lit_sel                           adaptive
% 19.56/3.00  --res_lit_sel_side                      none
% 19.56/3.00  --res_ordering                          kbo
% 19.56/3.00  --res_to_prop_solver                    active
% 19.56/3.00  --res_prop_simpl_new                    false
% 19.56/3.00  --res_prop_simpl_given                  true
% 19.56/3.00  --res_passive_queue_type                priority_queues
% 19.56/3.00  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 19.56/3.00  --res_passive_queues_freq               [15;5]
% 19.56/3.00  --res_forward_subs                      full
% 19.56/3.00  --res_backward_subs                     full
% 19.56/3.00  --res_forward_subs_resolution           true
% 19.56/3.00  --res_backward_subs_resolution          true
% 19.56/3.00  --res_orphan_elimination                true
% 19.56/3.00  --res_time_limit                        2.
% 19.56/3.00  --res_out_proof                         true
% 19.56/3.00  
% 19.56/3.00  ------ Superposition Options
% 19.56/3.00  
% 19.56/3.00  --superposition_flag                    true
% 19.56/3.00  --sup_passive_queue_type                priority_queues
% 19.56/3.00  --sup_passive_queues                    [[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 19.56/3.00  --sup_passive_queues_freq               [1;4]
% 19.56/3.00  --demod_completeness_check              fast
% 19.56/3.00  --demod_use_ground                      true
% 19.56/3.00  --sup_to_prop_solver                    passive
% 19.56/3.00  --sup_prop_simpl_new                    true
% 19.56/3.00  --sup_prop_simpl_given                  true
% 19.56/3.00  --sup_fun_splitting                     false
% 19.56/3.00  --sup_smt_interval                      50000
% 19.56/3.00  
% 19.56/3.00  ------ Superposition Simplification Setup
% 19.56/3.00  
% 19.56/3.00  --sup_indices_passive                   []
% 19.56/3.00  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 19.56/3.00  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 19.56/3.00  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 19.56/3.00  --sup_full_triv                         [TrivRules;PropSubs]
% 19.56/3.00  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 19.56/3.00  --sup_full_bw                           [BwDemod]
% 19.56/3.00  --sup_immed_triv                        [TrivRules]
% 19.56/3.00  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 19.56/3.00  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 19.56/3.00  --sup_immed_bw_main                     []
% 19.56/3.00  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 19.56/3.00  --sup_input_triv                        [Unflattening;TrivRules]
% 19.56/3.00  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 19.56/3.00  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 19.56/3.00  
% 19.56/3.00  ------ Combination Options
% 19.56/3.00  
% 19.56/3.00  --comb_res_mult                         3
% 19.56/3.00  --comb_sup_mult                         2
% 19.56/3.00  --comb_inst_mult                        10
% 19.56/3.00  
% 19.56/3.00  ------ Debug Options
% 19.56/3.00  
% 19.56/3.00  --dbg_backtrace                         false
% 19.56/3.00  --dbg_dump_prop_clauses                 false
% 19.56/3.00  --dbg_dump_prop_clauses_file            -
% 19.56/3.00  --dbg_out_stat                          false
% 19.56/3.00  
% 19.56/3.00  
% 19.56/3.00  
% 19.56/3.00  
% 19.56/3.00  ------ Proving...
% 19.56/3.00  
% 19.56/3.00  
% 19.56/3.00  % SZS status Theorem for theBenchmark.p
% 19.56/3.00  
% 19.56/3.00  % SZS output start CNFRefutation for theBenchmark.p
% 19.56/3.00  
% 19.56/3.00  fof(f14,conjecture,(
% 19.56/3.00    ! [X0,X1,X2,X3] : (m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => (r1_tarski(k6_relat_1(X2),X3) => (r1_tarski(X2,k2_relset_1(X0,X1,X3)) & r1_tarski(X2,k1_relset_1(X0,X1,X3)))))),
% 19.56/3.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 19.56/3.00  
% 19.56/3.00  fof(f15,negated_conjecture,(
% 19.56/3.00    ~! [X0,X1,X2,X3] : (m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => (r1_tarski(k6_relat_1(X2),X3) => (r1_tarski(X2,k2_relset_1(X0,X1,X3)) & r1_tarski(X2,k1_relset_1(X0,X1,X3)))))),
% 19.56/3.00    inference(negated_conjecture,[],[f14])).
% 19.56/3.00  
% 19.56/3.00  fof(f27,plain,(
% 19.56/3.00    ? [X0,X1,X2,X3] : (((~r1_tarski(X2,k2_relset_1(X0,X1,X3)) | ~r1_tarski(X2,k1_relset_1(X0,X1,X3))) & r1_tarski(k6_relat_1(X2),X3)) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 19.56/3.00    inference(ennf_transformation,[],[f15])).
% 19.56/3.00  
% 19.56/3.00  fof(f28,plain,(
% 19.56/3.00    ? [X0,X1,X2,X3] : ((~r1_tarski(X2,k2_relset_1(X0,X1,X3)) | ~r1_tarski(X2,k1_relset_1(X0,X1,X3))) & r1_tarski(k6_relat_1(X2),X3) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 19.56/3.00    inference(flattening,[],[f27])).
% 19.56/3.00  
% 19.56/3.00  fof(f32,plain,(
% 19.56/3.00    ? [X0,X1,X2,X3] : ((~r1_tarski(X2,k2_relset_1(X0,X1,X3)) | ~r1_tarski(X2,k1_relset_1(X0,X1,X3))) & r1_tarski(k6_relat_1(X2),X3) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) => ((~r1_tarski(sK2,k2_relset_1(sK0,sK1,sK3)) | ~r1_tarski(sK2,k1_relset_1(sK0,sK1,sK3))) & r1_tarski(k6_relat_1(sK2),sK3) & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))))),
% 19.56/3.00    introduced(choice_axiom,[])).
% 19.56/3.00  
% 19.56/3.00  fof(f33,plain,(
% 19.56/3.00    (~r1_tarski(sK2,k2_relset_1(sK0,sK1,sK3)) | ~r1_tarski(sK2,k1_relset_1(sK0,sK1,sK3))) & r1_tarski(k6_relat_1(sK2),sK3) & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))),
% 19.56/3.00    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3])],[f28,f32])).
% 19.56/3.00  
% 19.56/3.00  fof(f53,plain,(
% 19.56/3.00    r1_tarski(k6_relat_1(sK2),sK3)),
% 19.56/3.00    inference(cnf_transformation,[],[f33])).
% 19.56/3.00  
% 19.56/3.00  fof(f9,axiom,(
% 19.56/3.00    ! [X0] : (v1_relat_1(X0) => r1_tarski(X0,k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0))))),
% 19.56/3.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 19.56/3.00  
% 19.56/3.00  fof(f23,plain,(
% 19.56/3.00    ! [X0] : (r1_tarski(X0,k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0))) | ~v1_relat_1(X0))),
% 19.56/3.00    inference(ennf_transformation,[],[f9])).
% 19.56/3.00  
% 19.56/3.00  fof(f45,plain,(
% 19.56/3.00    ( ! [X0] : (r1_tarski(X0,k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0))) | ~v1_relat_1(X0)) )),
% 19.56/3.00    inference(cnf_transformation,[],[f23])).
% 19.56/3.00  
% 19.56/3.00  fof(f1,axiom,(
% 19.56/3.00    ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) <=> r1_tarski(X0,X1))),
% 19.56/3.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 19.56/3.00  
% 19.56/3.00  fof(f29,plain,(
% 19.56/3.00    ! [X0,X1] : ((m1_subset_1(X0,k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1)) & (r1_tarski(X0,X1) | ~m1_subset_1(X0,k1_zfmisc_1(X1))))),
% 19.56/3.00    inference(nnf_transformation,[],[f1])).
% 19.56/3.00  
% 19.56/3.00  fof(f35,plain,(
% 19.56/3.00    ( ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1)) )),
% 19.56/3.00    inference(cnf_transformation,[],[f29])).
% 19.56/3.00  
% 19.56/3.00  fof(f11,axiom,(
% 19.56/3.00    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => (v5_relat_1(X2,X1) & v4_relat_1(X2,X0)))),
% 19.56/3.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 19.56/3.00  
% 19.56/3.00  fof(f24,plain,(
% 19.56/3.00    ! [X0,X1,X2] : ((v5_relat_1(X2,X1) & v4_relat_1(X2,X0)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 19.56/3.00    inference(ennf_transformation,[],[f11])).
% 19.56/3.00  
% 19.56/3.00  fof(f48,plain,(
% 19.56/3.00    ( ! [X2,X0,X1] : (v4_relat_1(X2,X0) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 19.56/3.00    inference(cnf_transformation,[],[f24])).
% 19.56/3.00  
% 19.56/3.00  fof(f3,axiom,(
% 19.56/3.00    ! [X0,X1] : ((v4_relat_1(X1,X0) & v1_relat_1(X1)) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(X1)) => v4_relat_1(X2,X0)))),
% 19.56/3.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 19.56/3.00  
% 19.56/3.00  fof(f17,plain,(
% 19.56/3.00    ! [X0,X1] : (! [X2] : (v4_relat_1(X2,X0) | ~m1_subset_1(X2,k1_zfmisc_1(X1))) | (~v4_relat_1(X1,X0) | ~v1_relat_1(X1)))),
% 19.56/3.00    inference(ennf_transformation,[],[f3])).
% 19.56/3.00  
% 19.56/3.00  fof(f18,plain,(
% 19.56/3.00    ! [X0,X1] : (! [X2] : (v4_relat_1(X2,X0) | ~m1_subset_1(X2,k1_zfmisc_1(X1))) | ~v4_relat_1(X1,X0) | ~v1_relat_1(X1))),
% 19.56/3.00    inference(flattening,[],[f17])).
% 19.56/3.00  
% 19.56/3.00  fof(f37,plain,(
% 19.56/3.00    ( ! [X2,X0,X1] : (v4_relat_1(X2,X0) | ~m1_subset_1(X2,k1_zfmisc_1(X1)) | ~v4_relat_1(X1,X0) | ~v1_relat_1(X1)) )),
% 19.56/3.00    inference(cnf_transformation,[],[f18])).
% 19.56/3.00  
% 19.56/3.00  fof(f2,axiom,(
% 19.56/3.00    ! [X0] : (v1_relat_1(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => v1_relat_1(X1)))),
% 19.56/3.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 19.56/3.00  
% 19.56/3.00  fof(f16,plain,(
% 19.56/3.00    ! [X0] : (! [X1] : (v1_relat_1(X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) | ~v1_relat_1(X0))),
% 19.56/3.00    inference(ennf_transformation,[],[f2])).
% 19.56/3.00  
% 19.56/3.00  fof(f36,plain,(
% 19.56/3.00    ( ! [X0,X1] : (v1_relat_1(X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0)) | ~v1_relat_1(X0)) )),
% 19.56/3.00    inference(cnf_transformation,[],[f16])).
% 19.56/3.00  
% 19.56/3.00  fof(f5,axiom,(
% 19.56/3.00    ! [X0,X1] : (v1_relat_1(X1) => (v4_relat_1(X1,X0) <=> r1_tarski(k1_relat_1(X1),X0)))),
% 19.56/3.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 19.56/3.00  
% 19.56/3.00  fof(f21,plain,(
% 19.56/3.00    ! [X0,X1] : ((v4_relat_1(X1,X0) <=> r1_tarski(k1_relat_1(X1),X0)) | ~v1_relat_1(X1))),
% 19.56/3.00    inference(ennf_transformation,[],[f5])).
% 19.56/3.00  
% 19.56/3.00  fof(f30,plain,(
% 19.56/3.00    ! [X0,X1] : (((v4_relat_1(X1,X0) | ~r1_tarski(k1_relat_1(X1),X0)) & (r1_tarski(k1_relat_1(X1),X0) | ~v4_relat_1(X1,X0))) | ~v1_relat_1(X1))),
% 19.56/3.00    inference(nnf_transformation,[],[f21])).
% 19.56/3.00  
% 19.56/3.00  fof(f39,plain,(
% 19.56/3.00    ( ! [X0,X1] : (r1_tarski(k1_relat_1(X1),X0) | ~v4_relat_1(X1,X0) | ~v1_relat_1(X1)) )),
% 19.56/3.00    inference(cnf_transformation,[],[f30])).
% 19.56/3.00  
% 19.56/3.00  fof(f10,axiom,(
% 19.56/3.00    ! [X0] : (k2_relat_1(k6_relat_1(X0)) = X0 & k1_relat_1(k6_relat_1(X0)) = X0)),
% 19.56/3.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 19.56/3.00  
% 19.56/3.00  fof(f46,plain,(
% 19.56/3.00    ( ! [X0] : (k1_relat_1(k6_relat_1(X0)) = X0) )),
% 19.56/3.00    inference(cnf_transformation,[],[f10])).
% 19.56/3.00  
% 19.56/3.00  fof(f7,axiom,(
% 19.56/3.00    ! [X0] : v1_relat_1(k6_relat_1(X0))),
% 19.56/3.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 19.56/3.00  
% 19.56/3.00  fof(f43,plain,(
% 19.56/3.00    ( ! [X0] : (v1_relat_1(k6_relat_1(X0))) )),
% 19.56/3.00    inference(cnf_transformation,[],[f7])).
% 19.56/3.00  
% 19.56/3.00  fof(f6,axiom,(
% 19.56/3.00    ! [X0,X1] : (v1_relat_1(X1) => (v5_relat_1(X1,X0) <=> r1_tarski(k2_relat_1(X1),X0)))),
% 19.56/3.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 19.56/3.00  
% 19.56/3.00  fof(f22,plain,(
% 19.56/3.00    ! [X0,X1] : ((v5_relat_1(X1,X0) <=> r1_tarski(k2_relat_1(X1),X0)) | ~v1_relat_1(X1))),
% 19.56/3.00    inference(ennf_transformation,[],[f6])).
% 19.56/3.00  
% 19.56/3.00  fof(f31,plain,(
% 19.56/3.00    ! [X0,X1] : (((v5_relat_1(X1,X0) | ~r1_tarski(k2_relat_1(X1),X0)) & (r1_tarski(k2_relat_1(X1),X0) | ~v5_relat_1(X1,X0))) | ~v1_relat_1(X1))),
% 19.56/3.00    inference(nnf_transformation,[],[f22])).
% 19.56/3.00  
% 19.56/3.00  fof(f42,plain,(
% 19.56/3.00    ( ! [X0,X1] : (v5_relat_1(X1,X0) | ~r1_tarski(k2_relat_1(X1),X0) | ~v1_relat_1(X1)) )),
% 19.56/3.00    inference(cnf_transformation,[],[f31])).
% 19.56/3.00  
% 19.56/3.00  fof(f4,axiom,(
% 19.56/3.00    ! [X0,X1] : ((v5_relat_1(X1,X0) & v1_relat_1(X1)) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(X1)) => v5_relat_1(X2,X0)))),
% 19.56/3.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 19.56/3.00  
% 19.56/3.00  fof(f19,plain,(
% 19.56/3.00    ! [X0,X1] : (! [X2] : (v5_relat_1(X2,X0) | ~m1_subset_1(X2,k1_zfmisc_1(X1))) | (~v5_relat_1(X1,X0) | ~v1_relat_1(X1)))),
% 19.56/3.00    inference(ennf_transformation,[],[f4])).
% 19.56/3.00  
% 19.56/3.00  fof(f20,plain,(
% 19.56/3.00    ! [X0,X1] : (! [X2] : (v5_relat_1(X2,X0) | ~m1_subset_1(X2,k1_zfmisc_1(X1))) | ~v5_relat_1(X1,X0) | ~v1_relat_1(X1))),
% 19.56/3.00    inference(flattening,[],[f19])).
% 19.56/3.00  
% 19.56/3.00  fof(f38,plain,(
% 19.56/3.00    ( ! [X2,X0,X1] : (v5_relat_1(X2,X0) | ~m1_subset_1(X2,k1_zfmisc_1(X1)) | ~v5_relat_1(X1,X0) | ~v1_relat_1(X1)) )),
% 19.56/3.00    inference(cnf_transformation,[],[f20])).
% 19.56/3.00  
% 19.56/3.00  fof(f47,plain,(
% 19.56/3.00    ( ! [X0] : (k2_relat_1(k6_relat_1(X0)) = X0) )),
% 19.56/3.00    inference(cnf_transformation,[],[f10])).
% 19.56/3.00  
% 19.56/3.00  fof(f41,plain,(
% 19.56/3.00    ( ! [X0,X1] : (r1_tarski(k2_relat_1(X1),X0) | ~v5_relat_1(X1,X0) | ~v1_relat_1(X1)) )),
% 19.56/3.00    inference(cnf_transformation,[],[f31])).
% 19.56/3.00  
% 19.56/3.00  fof(f52,plain,(
% 19.56/3.00    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))),
% 19.56/3.00    inference(cnf_transformation,[],[f33])).
% 19.56/3.00  
% 19.56/3.00  fof(f13,axiom,(
% 19.56/3.00    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k2_relat_1(X2) = k2_relset_1(X0,X1,X2))),
% 19.56/3.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 19.56/3.00  
% 19.56/3.00  fof(f26,plain,(
% 19.56/3.00    ! [X0,X1,X2] : (k2_relat_1(X2) = k2_relset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 19.56/3.00    inference(ennf_transformation,[],[f13])).
% 19.56/3.00  
% 19.56/3.00  fof(f51,plain,(
% 19.56/3.00    ( ! [X2,X0,X1] : (k2_relat_1(X2) = k2_relset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 19.56/3.00    inference(cnf_transformation,[],[f26])).
% 19.56/3.00  
% 19.56/3.00  fof(f54,plain,(
% 19.56/3.00    ~r1_tarski(sK2,k2_relset_1(sK0,sK1,sK3)) | ~r1_tarski(sK2,k1_relset_1(sK0,sK1,sK3))),
% 19.56/3.00    inference(cnf_transformation,[],[f33])).
% 19.56/3.00  
% 19.56/3.00  fof(f34,plain,(
% 19.56/3.00    ( ! [X0,X1] : (r1_tarski(X0,X1) | ~m1_subset_1(X0,k1_zfmisc_1(X1))) )),
% 19.56/3.00    inference(cnf_transformation,[],[f29])).
% 19.56/3.00  
% 19.56/3.00  fof(f8,axiom,(
% 19.56/3.00    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1))),
% 19.56/3.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 19.56/3.00  
% 19.56/3.00  fof(f44,plain,(
% 19.56/3.00    ( ! [X0,X1] : (v1_relat_1(k2_zfmisc_1(X0,X1))) )),
% 19.56/3.00    inference(cnf_transformation,[],[f8])).
% 19.56/3.00  
% 19.56/3.00  fof(f12,axiom,(
% 19.56/3.00    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k1_relat_1(X2) = k1_relset_1(X0,X1,X2))),
% 19.56/3.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 19.56/3.00  
% 19.56/3.00  fof(f25,plain,(
% 19.56/3.00    ! [X0,X1,X2] : (k1_relat_1(X2) = k1_relset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 19.56/3.00    inference(ennf_transformation,[],[f12])).
% 19.56/3.00  
% 19.56/3.00  fof(f50,plain,(
% 19.56/3.00    ( ! [X2,X0,X1] : (k1_relat_1(X2) = k1_relset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 19.56/3.00    inference(cnf_transformation,[],[f25])).
% 19.56/3.00  
% 19.56/3.00  cnf(c_19,negated_conjecture,
% 19.56/3.00      ( r1_tarski(k6_relat_1(sK2),sK3) ),
% 19.56/3.00      inference(cnf_transformation,[],[f53]) ).
% 19.56/3.00  
% 19.56/3.00  cnf(c_663,plain,
% 19.56/3.00      ( r1_tarski(k6_relat_1(sK2),sK3) = iProver_top ),
% 19.56/3.00      inference(predicate_to_equality,[status(thm)],[c_19]) ).
% 19.56/3.00  
% 19.56/3.00  cnf(c_11,plain,
% 19.56/3.00      ( r1_tarski(X0,k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0)))
% 19.56/3.00      | ~ v1_relat_1(X0) ),
% 19.56/3.00      inference(cnf_transformation,[],[f45]) ).
% 19.56/3.00  
% 19.56/3.00  cnf(c_669,plain,
% 19.56/3.00      ( r1_tarski(X0,k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0))) = iProver_top
% 19.56/3.00      | v1_relat_1(X0) != iProver_top ),
% 19.56/3.00      inference(predicate_to_equality,[status(thm)],[c_11]) ).
% 19.56/3.00  
% 19.56/3.00  cnf(c_0,plain,
% 19.56/3.00      ( ~ r1_tarski(X0,X1) | m1_subset_1(X0,k1_zfmisc_1(X1)) ),
% 19.56/3.00      inference(cnf_transformation,[],[f35]) ).
% 19.56/3.00  
% 19.56/3.00  cnf(c_679,plain,
% 19.56/3.00      ( r1_tarski(X0,X1) != iProver_top
% 19.56/3.00      | m1_subset_1(X0,k1_zfmisc_1(X1)) = iProver_top ),
% 19.56/3.00      inference(predicate_to_equality,[status(thm)],[c_0]) ).
% 19.56/3.00  
% 19.56/3.00  cnf(c_15,plain,
% 19.56/3.00      ( v4_relat_1(X0,X1)
% 19.56/3.00      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) ),
% 19.56/3.00      inference(cnf_transformation,[],[f48]) ).
% 19.56/3.00  
% 19.56/3.00  cnf(c_667,plain,
% 19.56/3.00      ( v4_relat_1(X0,X1) = iProver_top
% 19.56/3.00      | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) != iProver_top ),
% 19.56/3.00      inference(predicate_to_equality,[status(thm)],[c_15]) ).
% 19.56/3.00  
% 19.56/3.00  cnf(c_1093,plain,
% 19.56/3.00      ( v4_relat_1(X0,X1) = iProver_top
% 19.56/3.00      | r1_tarski(X0,k2_zfmisc_1(X1,X2)) != iProver_top ),
% 19.56/3.00      inference(superposition,[status(thm)],[c_679,c_667]) ).
% 19.56/3.00  
% 19.56/3.00  cnf(c_2770,plain,
% 19.56/3.00      ( v4_relat_1(X0,k1_relat_1(X0)) = iProver_top
% 19.56/3.00      | v1_relat_1(X0) != iProver_top ),
% 19.56/3.00      inference(superposition,[status(thm)],[c_669,c_1093]) ).
% 19.56/3.00  
% 19.56/3.00  cnf(c_3,plain,
% 19.56/3.00      ( ~ v4_relat_1(X0,X1)
% 19.56/3.00      | v4_relat_1(X2,X1)
% 19.56/3.00      | ~ m1_subset_1(X2,k1_zfmisc_1(X0))
% 19.56/3.00      | ~ v1_relat_1(X0) ),
% 19.56/3.00      inference(cnf_transformation,[],[f37]) ).
% 19.56/3.00  
% 19.56/3.00  cnf(c_677,plain,
% 19.56/3.00      ( v4_relat_1(X0,X1) != iProver_top
% 19.56/3.00      | v4_relat_1(X2,X1) = iProver_top
% 19.56/3.00      | m1_subset_1(X2,k1_zfmisc_1(X0)) != iProver_top
% 19.56/3.00      | v1_relat_1(X0) != iProver_top ),
% 19.56/3.00      inference(predicate_to_equality,[status(thm)],[c_3]) ).
% 19.56/3.00  
% 19.56/3.00  cnf(c_2273,plain,
% 19.56/3.00      ( v4_relat_1(X0,X1) != iProver_top
% 19.56/3.00      | v4_relat_1(X2,X1) = iProver_top
% 19.56/3.00      | r1_tarski(X2,X0) != iProver_top
% 19.56/3.00      | v1_relat_1(X0) != iProver_top ),
% 19.56/3.00      inference(superposition,[status(thm)],[c_679,c_677]) ).
% 19.56/3.00  
% 19.56/3.00  cnf(c_5743,plain,
% 19.56/3.00      ( v4_relat_1(X0,k1_relat_1(X1)) = iProver_top
% 19.56/3.00      | r1_tarski(X0,X1) != iProver_top
% 19.56/3.00      | v1_relat_1(X1) != iProver_top ),
% 19.56/3.00      inference(superposition,[status(thm)],[c_2770,c_2273]) ).
% 19.56/3.00  
% 19.56/3.00  cnf(c_11710,plain,
% 19.56/3.00      ( v4_relat_1(X0,k1_relat_1(X1)) = iProver_top
% 19.56/3.00      | r1_tarski(X2,X1) != iProver_top
% 19.56/3.00      | r1_tarski(X0,X2) != iProver_top
% 19.56/3.00      | v1_relat_1(X2) != iProver_top
% 19.56/3.00      | v1_relat_1(X1) != iProver_top ),
% 19.56/3.00      inference(superposition,[status(thm)],[c_5743,c_2273]) ).
% 19.56/3.00  
% 19.56/3.00  cnf(c_2,plain,
% 19.56/3.00      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
% 19.56/3.00      | ~ v1_relat_1(X1)
% 19.56/3.00      | v1_relat_1(X0) ),
% 19.56/3.00      inference(cnf_transformation,[],[f36]) ).
% 19.56/3.00  
% 19.56/3.00  cnf(c_135,plain,
% 19.56/3.00      ( ~ r1_tarski(X0,X1) | m1_subset_1(X0,k1_zfmisc_1(X1)) ),
% 19.56/3.00      inference(prop_impl,[status(thm)],[c_0]) ).
% 19.56/3.00  
% 19.56/3.00  cnf(c_170,plain,
% 19.56/3.00      ( ~ r1_tarski(X0,X1) | ~ v1_relat_1(X1) | v1_relat_1(X0) ),
% 19.56/3.00      inference(bin_hyper_res,[status(thm)],[c_2,c_135]) ).
% 19.56/3.00  
% 19.56/3.00  cnf(c_661,plain,
% 19.56/3.00      ( r1_tarski(X0,X1) != iProver_top
% 19.56/3.00      | v1_relat_1(X1) != iProver_top
% 19.56/3.00      | v1_relat_1(X0) = iProver_top ),
% 19.56/3.00      inference(predicate_to_equality,[status(thm)],[c_170]) ).
% 19.56/3.00  
% 19.56/3.00  cnf(c_82798,plain,
% 19.56/3.00      ( v4_relat_1(X0,k1_relat_1(X1)) = iProver_top
% 19.56/3.00      | r1_tarski(X0,X2) != iProver_top
% 19.56/3.00      | r1_tarski(X2,X1) != iProver_top
% 19.56/3.00      | v1_relat_1(X1) != iProver_top ),
% 19.56/3.00      inference(forward_subsumption_resolution,
% 19.56/3.00                [status(thm)],
% 19.56/3.00                [c_11710,c_661]) ).
% 19.56/3.00  
% 19.56/3.00  cnf(c_82803,plain,
% 19.56/3.00      ( v4_relat_1(k6_relat_1(sK2),k1_relat_1(X0)) = iProver_top
% 19.56/3.00      | r1_tarski(sK3,X0) != iProver_top
% 19.56/3.00      | v1_relat_1(X0) != iProver_top ),
% 19.56/3.00      inference(superposition,[status(thm)],[c_663,c_82798]) ).
% 19.56/3.00  
% 19.56/3.00  cnf(c_82900,plain,
% 19.56/3.00      ( v4_relat_1(k6_relat_1(sK2),k1_relat_1(sK3)) = iProver_top
% 19.56/3.00      | r1_tarski(sK3,sK3) != iProver_top
% 19.56/3.00      | v1_relat_1(sK3) != iProver_top ),
% 19.56/3.00      inference(instantiation,[status(thm)],[c_82803]) ).
% 19.56/3.00  
% 19.56/3.00  cnf(c_6,plain,
% 19.56/3.00      ( ~ v4_relat_1(X0,X1)
% 19.56/3.00      | r1_tarski(k1_relat_1(X0),X1)
% 19.56/3.00      | ~ v1_relat_1(X0) ),
% 19.56/3.00      inference(cnf_transformation,[],[f39]) ).
% 19.56/3.00  
% 19.56/3.00  cnf(c_21388,plain,
% 19.56/3.00      ( ~ v4_relat_1(X0,k1_relat_1(X1))
% 19.56/3.00      | r1_tarski(k1_relat_1(X0),k1_relat_1(X1))
% 19.56/3.00      | ~ v1_relat_1(X0) ),
% 19.56/3.00      inference(instantiation,[status(thm)],[c_6]) ).
% 19.56/3.00  
% 19.56/3.00  cnf(c_62743,plain,
% 19.56/3.00      ( ~ v4_relat_1(k6_relat_1(sK2),k1_relat_1(sK3))
% 19.56/3.00      | r1_tarski(k1_relat_1(k6_relat_1(sK2)),k1_relat_1(sK3))
% 19.56/3.00      | ~ v1_relat_1(k6_relat_1(sK2)) ),
% 19.56/3.00      inference(instantiation,[status(thm)],[c_21388]) ).
% 19.56/3.00  
% 19.56/3.00  cnf(c_62744,plain,
% 19.56/3.00      ( v4_relat_1(k6_relat_1(sK2),k1_relat_1(sK3)) != iProver_top
% 19.56/3.00      | r1_tarski(k1_relat_1(k6_relat_1(sK2)),k1_relat_1(sK3)) = iProver_top
% 19.56/3.00      | v1_relat_1(k6_relat_1(sK2)) != iProver_top ),
% 19.56/3.00      inference(predicate_to_equality,[status(thm)],[c_62743]) ).
% 19.56/3.00  
% 19.56/3.00  cnf(c_13,plain,
% 19.56/3.00      ( k1_relat_1(k6_relat_1(X0)) = X0 ),
% 19.56/3.00      inference(cnf_transformation,[],[f46]) ).
% 19.56/3.00  
% 19.56/3.00  cnf(c_674,plain,
% 19.56/3.00      ( v4_relat_1(X0,X1) != iProver_top
% 19.56/3.00      | r1_tarski(k1_relat_1(X0),X1) = iProver_top
% 19.56/3.00      | v1_relat_1(X0) != iProver_top ),
% 19.56/3.00      inference(predicate_to_equality,[status(thm)],[c_6]) ).
% 19.56/3.00  
% 19.56/3.00  cnf(c_1725,plain,
% 19.56/3.00      ( v4_relat_1(k6_relat_1(X0),X1) != iProver_top
% 19.56/3.00      | r1_tarski(X0,X1) = iProver_top
% 19.56/3.00      | v1_relat_1(k6_relat_1(X0)) != iProver_top ),
% 19.56/3.00      inference(superposition,[status(thm)],[c_13,c_674]) ).
% 19.56/3.00  
% 19.56/3.00  cnf(c_9,plain,
% 19.56/3.00      ( v1_relat_1(k6_relat_1(X0)) ),
% 19.56/3.00      inference(cnf_transformation,[],[f43]) ).
% 19.56/3.00  
% 19.56/3.00  cnf(c_44,plain,
% 19.56/3.00      ( v1_relat_1(k6_relat_1(X0)) = iProver_top ),
% 19.56/3.00      inference(predicate_to_equality,[status(thm)],[c_9]) ).
% 19.56/3.00  
% 19.56/3.00  cnf(c_2149,plain,
% 19.56/3.00      ( r1_tarski(X0,X1) = iProver_top
% 19.56/3.00      | v4_relat_1(k6_relat_1(X0),X1) != iProver_top ),
% 19.56/3.00      inference(global_propositional_subsumption,
% 19.56/3.00                [status(thm)],
% 19.56/3.00                [c_1725,c_44]) ).
% 19.56/3.00  
% 19.56/3.00  cnf(c_2150,plain,
% 19.56/3.00      ( v4_relat_1(k6_relat_1(X0),X1) != iProver_top
% 19.56/3.00      | r1_tarski(X0,X1) = iProver_top ),
% 19.56/3.00      inference(renaming,[status(thm)],[c_2149]) ).
% 19.56/3.00  
% 19.56/3.00  cnf(c_3043,plain,
% 19.56/3.00      ( r1_tarski(X0,k1_relat_1(k6_relat_1(X0))) = iProver_top
% 19.56/3.00      | v1_relat_1(k6_relat_1(X0)) != iProver_top ),
% 19.56/3.00      inference(superposition,[status(thm)],[c_2770,c_2150]) ).
% 19.56/3.00  
% 19.56/3.00  cnf(c_3046,plain,
% 19.56/3.00      ( r1_tarski(X0,X0) = iProver_top
% 19.56/3.00      | v1_relat_1(k6_relat_1(X0)) != iProver_top ),
% 19.56/3.00      inference(light_normalisation,[status(thm)],[c_3043,c_13]) ).
% 19.56/3.00  
% 19.56/3.00  cnf(c_3053,plain,
% 19.56/3.00      ( r1_tarski(X0,X0) = iProver_top ),
% 19.56/3.00      inference(global_propositional_subsumption,
% 19.56/3.00                [status(thm)],
% 19.56/3.00                [c_3046,c_44]) ).
% 19.56/3.00  
% 19.56/3.00  cnf(c_7,plain,
% 19.56/3.00      ( v5_relat_1(X0,X1)
% 19.56/3.00      | ~ r1_tarski(k2_relat_1(X0),X1)
% 19.56/3.00      | ~ v1_relat_1(X0) ),
% 19.56/3.00      inference(cnf_transformation,[],[f42]) ).
% 19.56/3.00  
% 19.56/3.00  cnf(c_673,plain,
% 19.56/3.00      ( v5_relat_1(X0,X1) = iProver_top
% 19.56/3.00      | r1_tarski(k2_relat_1(X0),X1) != iProver_top
% 19.56/3.00      | v1_relat_1(X0) != iProver_top ),
% 19.56/3.00      inference(predicate_to_equality,[status(thm)],[c_7]) ).
% 19.56/3.00  
% 19.56/3.00  cnf(c_3062,plain,
% 19.56/3.00      ( v5_relat_1(X0,k2_relat_1(X0)) = iProver_top
% 19.56/3.00      | v1_relat_1(X0) != iProver_top ),
% 19.56/3.00      inference(superposition,[status(thm)],[c_3053,c_673]) ).
% 19.56/3.00  
% 19.56/3.00  cnf(c_4,plain,
% 19.56/3.00      ( ~ v5_relat_1(X0,X1)
% 19.56/3.00      | v5_relat_1(X2,X1)
% 19.56/3.00      | ~ m1_subset_1(X2,k1_zfmisc_1(X0))
% 19.56/3.00      | ~ v1_relat_1(X0) ),
% 19.56/3.00      inference(cnf_transformation,[],[f38]) ).
% 19.56/3.00  
% 19.56/3.00  cnf(c_676,plain,
% 19.56/3.00      ( v5_relat_1(X0,X1) != iProver_top
% 19.56/3.00      | v5_relat_1(X2,X1) = iProver_top
% 19.56/3.00      | m1_subset_1(X2,k1_zfmisc_1(X0)) != iProver_top
% 19.56/3.00      | v1_relat_1(X0) != iProver_top ),
% 19.56/3.00      inference(predicate_to_equality,[status(thm)],[c_4]) ).
% 19.56/3.00  
% 19.56/3.00  cnf(c_1953,plain,
% 19.56/3.00      ( v5_relat_1(X0,X1) != iProver_top
% 19.56/3.00      | v5_relat_1(X2,X1) = iProver_top
% 19.56/3.00      | r1_tarski(X2,X0) != iProver_top
% 19.56/3.00      | v1_relat_1(X0) != iProver_top ),
% 19.56/3.00      inference(superposition,[status(thm)],[c_679,c_676]) ).
% 19.56/3.00  
% 19.56/3.00  cnf(c_5076,plain,
% 19.56/3.00      ( v5_relat_1(X0,k2_relat_1(X1)) = iProver_top
% 19.56/3.00      | r1_tarski(X0,X1) != iProver_top
% 19.56/3.00      | v1_relat_1(X1) != iProver_top ),
% 19.56/3.00      inference(superposition,[status(thm)],[c_3062,c_1953]) ).
% 19.56/3.00  
% 19.56/3.00  cnf(c_8997,plain,
% 19.56/3.00      ( v5_relat_1(X0,k2_relat_1(X1)) = iProver_top
% 19.56/3.00      | r1_tarski(X2,X1) != iProver_top
% 19.56/3.00      | r1_tarski(X0,X2) != iProver_top
% 19.56/3.00      | v1_relat_1(X2) != iProver_top
% 19.56/3.00      | v1_relat_1(X1) != iProver_top ),
% 19.56/3.00      inference(superposition,[status(thm)],[c_5076,c_1953]) ).
% 19.56/3.00  
% 19.56/3.00  cnf(c_37323,plain,
% 19.56/3.00      ( v5_relat_1(X0,k2_relat_1(X1)) = iProver_top
% 19.56/3.00      | r1_tarski(X0,X2) != iProver_top
% 19.56/3.00      | r1_tarski(X2,X1) != iProver_top
% 19.56/3.00      | v1_relat_1(X1) != iProver_top ),
% 19.56/3.00      inference(forward_subsumption_resolution,
% 19.56/3.00                [status(thm)],
% 19.56/3.00                [c_8997,c_661]) ).
% 19.56/3.00  
% 19.56/3.00  cnf(c_37328,plain,
% 19.56/3.00      ( v5_relat_1(k6_relat_1(sK2),k2_relat_1(X0)) = iProver_top
% 19.56/3.00      | r1_tarski(sK3,X0) != iProver_top
% 19.56/3.00      | v1_relat_1(X0) != iProver_top ),
% 19.56/3.00      inference(superposition,[status(thm)],[c_663,c_37323]) ).
% 19.56/3.00  
% 19.56/3.00  cnf(c_12,plain,
% 19.56/3.00      ( k2_relat_1(k6_relat_1(X0)) = X0 ),
% 19.56/3.00      inference(cnf_transformation,[],[f47]) ).
% 19.56/3.00  
% 19.56/3.00  cnf(c_8,plain,
% 19.56/3.00      ( ~ v5_relat_1(X0,X1)
% 19.56/3.00      | r1_tarski(k2_relat_1(X0),X1)
% 19.56/3.00      | ~ v1_relat_1(X0) ),
% 19.56/3.00      inference(cnf_transformation,[],[f41]) ).
% 19.56/3.00  
% 19.56/3.00  cnf(c_672,plain,
% 19.56/3.00      ( v5_relat_1(X0,X1) != iProver_top
% 19.56/3.00      | r1_tarski(k2_relat_1(X0),X1) = iProver_top
% 19.56/3.00      | v1_relat_1(X0) != iProver_top ),
% 19.56/3.00      inference(predicate_to_equality,[status(thm)],[c_8]) ).
% 19.56/3.00  
% 19.56/3.00  cnf(c_1452,plain,
% 19.56/3.00      ( v5_relat_1(k6_relat_1(X0),X1) != iProver_top
% 19.56/3.00      | r1_tarski(X0,X1) = iProver_top
% 19.56/3.00      | v1_relat_1(k6_relat_1(X0)) != iProver_top ),
% 19.56/3.00      inference(superposition,[status(thm)],[c_12,c_672]) ).
% 19.56/3.00  
% 19.56/3.00  cnf(c_1974,plain,
% 19.56/3.00      ( r1_tarski(X0,X1) = iProver_top
% 19.56/3.00      | v5_relat_1(k6_relat_1(X0),X1) != iProver_top ),
% 19.56/3.00      inference(global_propositional_subsumption,
% 19.56/3.00                [status(thm)],
% 19.56/3.00                [c_1452,c_44]) ).
% 19.56/3.00  
% 19.56/3.00  cnf(c_1975,plain,
% 19.56/3.00      ( v5_relat_1(k6_relat_1(X0),X1) != iProver_top
% 19.56/3.00      | r1_tarski(X0,X1) = iProver_top ),
% 19.56/3.00      inference(renaming,[status(thm)],[c_1974]) ).
% 19.56/3.00  
% 19.56/3.00  cnf(c_38192,plain,
% 19.56/3.00      ( r1_tarski(sK3,X0) != iProver_top
% 19.56/3.00      | r1_tarski(sK2,k2_relat_1(X0)) = iProver_top
% 19.56/3.00      | v1_relat_1(X0) != iProver_top ),
% 19.56/3.00      inference(superposition,[status(thm)],[c_37328,c_1975]) ).
% 19.56/3.00  
% 19.56/3.00  cnf(c_38241,plain,
% 19.56/3.00      ( r1_tarski(sK3,sK3) != iProver_top
% 19.56/3.00      | r1_tarski(sK2,k2_relat_1(sK3)) = iProver_top
% 19.56/3.00      | v1_relat_1(sK3) != iProver_top ),
% 19.56/3.00      inference(instantiation,[status(thm)],[c_38192]) ).
% 19.56/3.00  
% 19.56/3.00  cnf(c_227,plain,
% 19.56/3.00      ( ~ r1_tarski(X0,X1) | r1_tarski(X2,X3) | X2 != X0 | X3 != X1 ),
% 19.56/3.00      theory(equality) ).
% 19.56/3.00  
% 19.56/3.00  cnf(c_6311,plain,
% 19.56/3.00      ( ~ r1_tarski(X0,X1)
% 19.56/3.00      | r1_tarski(sK2,k1_relset_1(sK0,sK1,sK3))
% 19.56/3.00      | k1_relset_1(sK0,sK1,sK3) != X1
% 19.56/3.00      | sK2 != X0 ),
% 19.56/3.00      inference(instantiation,[status(thm)],[c_227]) ).
% 19.56/3.00  
% 19.56/3.00  cnf(c_17532,plain,
% 19.56/3.00      ( ~ r1_tarski(k1_relat_1(k6_relat_1(sK2)),X0)
% 19.56/3.00      | r1_tarski(sK2,k1_relset_1(sK0,sK1,sK3))
% 19.56/3.00      | k1_relset_1(sK0,sK1,sK3) != X0
% 19.56/3.00      | sK2 != k1_relat_1(k6_relat_1(sK2)) ),
% 19.56/3.00      inference(instantiation,[status(thm)],[c_6311]) ).
% 19.56/3.00  
% 19.56/3.00  cnf(c_31425,plain,
% 19.56/3.00      ( ~ r1_tarski(k1_relat_1(k6_relat_1(sK2)),k1_relat_1(sK3))
% 19.56/3.00      | r1_tarski(sK2,k1_relset_1(sK0,sK1,sK3))
% 19.56/3.00      | k1_relset_1(sK0,sK1,sK3) != k1_relat_1(sK3)
% 19.56/3.00      | sK2 != k1_relat_1(k6_relat_1(sK2)) ),
% 19.56/3.00      inference(instantiation,[status(thm)],[c_17532]) ).
% 19.56/3.00  
% 19.56/3.00  cnf(c_31426,plain,
% 19.56/3.00      ( k1_relset_1(sK0,sK1,sK3) != k1_relat_1(sK3)
% 19.56/3.00      | sK2 != k1_relat_1(k6_relat_1(sK2))
% 19.56/3.00      | r1_tarski(k1_relat_1(k6_relat_1(sK2)),k1_relat_1(sK3)) != iProver_top
% 19.56/3.00      | r1_tarski(sK2,k1_relset_1(sK0,sK1,sK3)) = iProver_top ),
% 19.56/3.00      inference(predicate_to_equality,[status(thm)],[c_31425]) ).
% 19.56/3.00  
% 19.56/3.00  cnf(c_224,plain,( X0 != X1 | X2 != X1 | X2 = X0 ),theory(equality) ).
% 19.56/3.00  
% 19.56/3.00  cnf(c_2204,plain,
% 19.56/3.00      ( X0 != X1 | sK2 != X1 | sK2 = X0 ),
% 19.56/3.00      inference(instantiation,[status(thm)],[c_224]) ).
% 19.56/3.00  
% 19.56/3.00  cnf(c_4879,plain,
% 19.56/3.00      ( X0 != sK2 | sK2 = X0 | sK2 != sK2 ),
% 19.56/3.00      inference(instantiation,[status(thm)],[c_2204]) ).
% 19.56/3.00  
% 19.56/3.00  cnf(c_11347,plain,
% 19.56/3.00      ( k1_relat_1(k6_relat_1(sK2)) != sK2
% 19.56/3.00      | sK2 = k1_relat_1(k6_relat_1(sK2))
% 19.56/3.00      | sK2 != sK2 ),
% 19.56/3.00      inference(instantiation,[status(thm)],[c_4879]) ).
% 19.56/3.00  
% 19.56/3.00  cnf(c_223,plain,( X0 = X0 ),theory(equality) ).
% 19.56/3.00  
% 19.56/3.00  cnf(c_4880,plain,
% 19.56/3.00      ( sK2 = sK2 ),
% 19.56/3.00      inference(instantiation,[status(thm)],[c_223]) ).
% 19.56/3.00  
% 19.56/3.00  cnf(c_1372,plain,
% 19.56/3.00      ( r1_tarski(k6_relat_1(X0),k2_zfmisc_1(k1_relat_1(k6_relat_1(X0)),X0)) = iProver_top
% 19.56/3.00      | v1_relat_1(k6_relat_1(X0)) != iProver_top ),
% 19.56/3.00      inference(superposition,[status(thm)],[c_12,c_669]) ).
% 19.56/3.00  
% 19.56/3.00  cnf(c_1376,plain,
% 19.56/3.00      ( r1_tarski(k6_relat_1(X0),k2_zfmisc_1(X0,X0)) = iProver_top
% 19.56/3.00      | v1_relat_1(k6_relat_1(X0)) != iProver_top ),
% 19.56/3.00      inference(light_normalisation,[status(thm)],[c_1372,c_13]) ).
% 19.56/3.00  
% 19.56/3.00  cnf(c_1386,plain,
% 19.56/3.00      ( r1_tarski(k6_relat_1(X0),k2_zfmisc_1(X0,X0)) = iProver_top ),
% 19.56/3.00      inference(global_propositional_subsumption,
% 19.56/3.00                [status(thm)],
% 19.56/3.00                [c_1376,c_44]) ).
% 19.56/3.00  
% 19.56/3.00  cnf(c_2772,plain,
% 19.56/3.00      ( v4_relat_1(k6_relat_1(X0),X0) = iProver_top ),
% 19.56/3.00      inference(superposition,[status(thm)],[c_1386,c_1093]) ).
% 19.56/3.00  
% 19.56/3.00  cnf(c_2795,plain,
% 19.56/3.00      ( v4_relat_1(k6_relat_1(sK3),sK3) = iProver_top ),
% 19.56/3.00      inference(instantiation,[status(thm)],[c_2772]) ).
% 19.56/3.00  
% 19.56/3.00  cnf(c_20,negated_conjecture,
% 19.56/3.00      ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ),
% 19.56/3.00      inference(cnf_transformation,[],[f52]) ).
% 19.56/3.00  
% 19.56/3.00  cnf(c_662,plain,
% 19.56/3.00      ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) = iProver_top ),
% 19.56/3.00      inference(predicate_to_equality,[status(thm)],[c_20]) ).
% 19.56/3.00  
% 19.56/3.00  cnf(c_17,plain,
% 19.56/3.00      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 19.56/3.00      | k2_relset_1(X1,X2,X0) = k2_relat_1(X0) ),
% 19.56/3.00      inference(cnf_transformation,[],[f51]) ).
% 19.56/3.00  
% 19.56/3.00  cnf(c_665,plain,
% 19.56/3.00      ( k2_relset_1(X0,X1,X2) = k2_relat_1(X2)
% 19.56/3.00      | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
% 19.56/3.00      inference(predicate_to_equality,[status(thm)],[c_17]) ).
% 19.56/3.00  
% 19.56/3.00  cnf(c_1438,plain,
% 19.56/3.00      ( k2_relset_1(sK0,sK1,sK3) = k2_relat_1(sK3) ),
% 19.56/3.00      inference(superposition,[status(thm)],[c_662,c_665]) ).
% 19.56/3.00  
% 19.56/3.00  cnf(c_18,negated_conjecture,
% 19.56/3.00      ( ~ r1_tarski(sK2,k2_relset_1(sK0,sK1,sK3))
% 19.56/3.00      | ~ r1_tarski(sK2,k1_relset_1(sK0,sK1,sK3)) ),
% 19.56/3.00      inference(cnf_transformation,[],[f54]) ).
% 19.56/3.00  
% 19.56/3.00  cnf(c_664,plain,
% 19.56/3.00      ( r1_tarski(sK2,k2_relset_1(sK0,sK1,sK3)) != iProver_top
% 19.56/3.00      | r1_tarski(sK2,k1_relset_1(sK0,sK1,sK3)) != iProver_top ),
% 19.56/3.00      inference(predicate_to_equality,[status(thm)],[c_18]) ).
% 19.56/3.00  
% 19.56/3.00  cnf(c_2666,plain,
% 19.56/3.00      ( r1_tarski(sK2,k1_relset_1(sK0,sK1,sK3)) != iProver_top
% 19.56/3.00      | r1_tarski(sK2,k2_relat_1(sK3)) != iProver_top ),
% 19.56/3.00      inference(demodulation,[status(thm)],[c_1438,c_664]) ).
% 19.56/3.00  
% 19.56/3.00  cnf(c_2152,plain,
% 19.56/3.00      ( v4_relat_1(k6_relat_1(sK3),sK3) != iProver_top
% 19.56/3.00      | r1_tarski(sK3,sK3) = iProver_top ),
% 19.56/3.00      inference(instantiation,[status(thm)],[c_2150]) ).
% 19.56/3.00  
% 19.56/3.00  cnf(c_1311,plain,
% 19.56/3.00      ( k1_relat_1(k6_relat_1(sK2)) = sK2 ),
% 19.56/3.00      inference(instantiation,[status(thm)],[c_13]) ).
% 19.56/3.00  
% 19.56/3.00  cnf(c_1,plain,
% 19.56/3.00      ( r1_tarski(X0,X1) | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ),
% 19.56/3.00      inference(cnf_transformation,[],[f34]) ).
% 19.56/3.00  
% 19.56/3.00  cnf(c_881,plain,
% 19.56/3.00      ( r1_tarski(sK3,k2_zfmisc_1(sK0,sK1)) ),
% 19.56/3.00      inference(resolution,[status(thm)],[c_1,c_20]) ).
% 19.56/3.00  
% 19.56/3.00  cnf(c_930,plain,
% 19.56/3.00      ( ~ v1_relat_1(k2_zfmisc_1(sK0,sK1)) | v1_relat_1(sK3) ),
% 19.56/3.00      inference(resolution,[status(thm)],[c_170,c_881]) ).
% 19.56/3.00  
% 19.56/3.00  cnf(c_10,plain,
% 19.56/3.00      ( v1_relat_1(k2_zfmisc_1(X0,X1)) ),
% 19.56/3.00      inference(cnf_transformation,[],[f44]) ).
% 19.56/3.00  
% 19.56/3.00  cnf(c_970,plain,
% 19.56/3.00      ( v1_relat_1(sK3) ),
% 19.56/3.00      inference(forward_subsumption_resolution,
% 19.56/3.00                [status(thm)],
% 19.56/3.00                [c_930,c_10]) ).
% 19.56/3.00  
% 19.56/3.00  cnf(c_971,plain,
% 19.56/3.00      ( v1_relat_1(sK3) = iProver_top ),
% 19.56/3.00      inference(predicate_to_equality,[status(thm)],[c_970]) ).
% 19.56/3.00  
% 19.56/3.00  cnf(c_16,plain,
% 19.56/3.00      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 19.56/3.00      | k1_relset_1(X1,X2,X0) = k1_relat_1(X0) ),
% 19.56/3.00      inference(cnf_transformation,[],[f50]) ).
% 19.56/3.00  
% 19.56/3.00  cnf(c_883,plain,
% 19.56/3.00      ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
% 19.56/3.00      | k1_relset_1(sK0,sK1,sK3) = k1_relat_1(sK3) ),
% 19.56/3.00      inference(instantiation,[status(thm)],[c_16]) ).
% 19.56/3.00  
% 19.56/3.00  cnf(c_853,plain,
% 19.56/3.00      ( ~ r1_tarski(k6_relat_1(sK2),sK3)
% 19.56/3.00      | v1_relat_1(k6_relat_1(sK2))
% 19.56/3.00      | ~ v1_relat_1(sK3) ),
% 19.56/3.00      inference(instantiation,[status(thm)],[c_170]) ).
% 19.56/3.00  
% 19.56/3.00  cnf(c_854,plain,
% 19.56/3.00      ( r1_tarski(k6_relat_1(sK2),sK3) != iProver_top
% 19.56/3.00      | v1_relat_1(k6_relat_1(sK2)) = iProver_top
% 19.56/3.00      | v1_relat_1(sK3) != iProver_top ),
% 19.56/3.00      inference(predicate_to_equality,[status(thm)],[c_853]) ).
% 19.56/3.00  
% 19.56/3.00  cnf(c_22,plain,
% 19.56/3.00      ( r1_tarski(k6_relat_1(sK2),sK3) = iProver_top ),
% 19.56/3.00      inference(predicate_to_equality,[status(thm)],[c_19]) ).
% 19.56/3.00  
% 19.56/3.00  cnf(contradiction,plain,
% 19.56/3.00      ( $false ),
% 19.56/3.00      inference(minisat,
% 19.56/3.00                [status(thm)],
% 19.56/3.00                [c_82900,c_62744,c_38241,c_31426,c_11347,c_4880,c_2795,
% 19.56/3.00                 c_2666,c_2152,c_1311,c_971,c_883,c_854,c_22,c_20]) ).
% 19.56/3.00  
% 19.56/3.00  
% 19.56/3.00  % SZS output end CNFRefutation for theBenchmark.p
% 19.56/3.00  
% 19.56/3.00  ------                               Statistics
% 19.56/3.00  
% 19.56/3.00  ------ Selected
% 19.56/3.00  
% 19.56/3.00  total_time:                             2.066
% 19.56/3.00  
%------------------------------------------------------------------------------
