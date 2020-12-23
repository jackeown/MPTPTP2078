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
% DateTime   : Thu Dec  3 11:55:10 EST 2020

% Result     : Theorem 3.99s
% Output     : CNFRefutation 3.99s
% Verified   : 
% Statistics : Number of formulae       :  125 ( 226 expanded)
%              Number of clauses        :   74 (  98 expanded)
%              Number of leaves         :   16 (  40 expanded)
%              Depth                    :   15
%              Number of atoms          :  332 ( 676 expanded)
%              Number of equality atoms :  146 ( 186 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal clause size      :    8 (   2 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f12,conjecture,(
    ! [X0,X1,X2,X3] :
      ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => ( r1_tarski(k6_relat_1(X2),X3)
       => ( r1_tarski(X2,k2_relset_1(X0,X1,X3))
          & r1_tarski(X2,k1_relset_1(X0,X1,X3)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f13,negated_conjecture,(
    ~ ! [X0,X1,X2,X3] :
        ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
       => ( r1_tarski(k6_relat_1(X2),X3)
         => ( r1_tarski(X2,k2_relset_1(X0,X1,X3))
            & r1_tarski(X2,k1_relset_1(X0,X1,X3)) ) ) ) ),
    inference(negated_conjecture,[],[f12])).

fof(f23,plain,(
    ? [X0,X1,X2,X3] :
      ( ( ~ r1_tarski(X2,k2_relset_1(X0,X1,X3))
        | ~ r1_tarski(X2,k1_relset_1(X0,X1,X3)) )
      & r1_tarski(k6_relat_1(X2),X3)
      & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f24,plain,(
    ? [X0,X1,X2,X3] :
      ( ( ~ r1_tarski(X2,k2_relset_1(X0,X1,X3))
        | ~ r1_tarski(X2,k1_relset_1(X0,X1,X3)) )
      & r1_tarski(k6_relat_1(X2),X3)
      & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(flattening,[],[f23])).

fof(f30,plain,
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

fof(f31,plain,
    ( ( ~ r1_tarski(sK2,k2_relset_1(sK0,sK1,sK3))
      | ~ r1_tarski(sK2,k1_relset_1(sK0,sK1,sK3)) )
    & r1_tarski(k6_relat_1(sK2),sK3)
    & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3])],[f24,f30])).

fof(f50,plain,(
    r1_tarski(k6_relat_1(sK2),sK3) ),
    inference(cnf_transformation,[],[f31])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( X0 = X1
    <=> ( r1_tarski(X1,X0)
        & r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f25,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(nnf_transformation,[],[f1])).

fof(f26,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(flattening,[],[f25])).

fof(f33,plain,(
    ! [X0,X1] :
      ( r1_tarski(X1,X0)
      | X0 != X1 ) ),
    inference(cnf_transformation,[],[f26])).

fof(f52,plain,(
    ! [X1] : r1_tarski(X1,X1) ),
    inference(equality_resolution,[],[f33])).

fof(f5,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ( v4_relat_1(X1,X0)
      <=> r1_tarski(k1_relat_1(X1),X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f18,plain,(
    ! [X0,X1] :
      ( ( v4_relat_1(X1,X0)
      <=> r1_tarski(k1_relat_1(X1),X0) )
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f28,plain,(
    ! [X0,X1] :
      ( ( ( v4_relat_1(X1,X0)
          | ~ r1_tarski(k1_relat_1(X1),X0) )
        & ( r1_tarski(k1_relat_1(X1),X0)
          | ~ v4_relat_1(X1,X0) ) )
      | ~ v1_relat_1(X1) ) ),
    inference(nnf_transformation,[],[f18])).

fof(f40,plain,(
    ! [X0,X1] :
      ( v4_relat_1(X1,X0)
      | ~ r1_tarski(k1_relat_1(X1),X0)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f27,plain,(
    ! [X0,X1] :
      ( ( m1_subset_1(X0,k1_zfmisc_1(X1))
        | ~ r1_tarski(X0,X1) )
      & ( r1_tarski(X0,X1)
        | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ) ) ),
    inference(nnf_transformation,[],[f2])).

fof(f36,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( ( v4_relat_1(X1,X0)
        & v1_relat_1(X1) )
     => ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(X1))
         => v4_relat_1(X2,X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f14,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( v4_relat_1(X2,X0)
          | ~ m1_subset_1(X2,k1_zfmisc_1(X1)) )
      | ~ v4_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f15,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( v4_relat_1(X2,X0)
          | ~ m1_subset_1(X2,k1_zfmisc_1(X1)) )
      | ~ v4_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f14])).

fof(f37,plain,(
    ! [X2,X0,X1] :
      ( v4_relat_1(X2,X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(X1))
      | ~ v4_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f15])).

fof(f6,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ( v5_relat_1(X1,X0)
      <=> r1_tarski(k2_relat_1(X1),X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f19,plain,(
    ! [X0,X1] :
      ( ( v5_relat_1(X1,X0)
      <=> r1_tarski(k2_relat_1(X1),X0) )
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f29,plain,(
    ! [X0,X1] :
      ( ( ( v5_relat_1(X1,X0)
          | ~ r1_tarski(k2_relat_1(X1),X0) )
        & ( r1_tarski(k2_relat_1(X1),X0)
          | ~ v5_relat_1(X1,X0) ) )
      | ~ v1_relat_1(X1) ) ),
    inference(nnf_transformation,[],[f19])).

fof(f42,plain,(
    ! [X0,X1] :
      ( v5_relat_1(X1,X0)
      | ~ r1_tarski(k2_relat_1(X1),X0)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( ( v5_relat_1(X1,X0)
        & v1_relat_1(X1) )
     => ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(X1))
         => v5_relat_1(X2,X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f16,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( v5_relat_1(X2,X0)
          | ~ m1_subset_1(X2,k1_zfmisc_1(X1)) )
      | ~ v5_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f17,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( v5_relat_1(X2,X0)
          | ~ m1_subset_1(X2,k1_zfmisc_1(X1)) )
      | ~ v5_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f16])).

fof(f38,plain,(
    ! [X2,X0,X1] :
      ( v5_relat_1(X2,X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(X1))
      | ~ v5_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f49,plain,(
    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ),
    inference(cnf_transformation,[],[f31])).

fof(f9,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => v1_relat_1(X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f20,plain,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f46,plain,(
    ! [X2,X0,X1] :
      ( v1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f8,axiom,(
    ! [X0] :
      ( k2_relat_1(k6_relat_1(X0)) = X0
      & k1_relat_1(k6_relat_1(X0)) = X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f45,plain,(
    ! [X0] : k2_relat_1(k6_relat_1(X0)) = X0 ),
    inference(cnf_transformation,[],[f8])).

fof(f41,plain,(
    ! [X0,X1] :
      ( r1_tarski(k2_relat_1(X1),X0)
      | ~ v5_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f7,axiom,(
    ! [X0] : v1_relat_1(k6_relat_1(X0)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f43,plain,(
    ! [X0] : v1_relat_1(k6_relat_1(X0)) ),
    inference(cnf_transformation,[],[f7])).

fof(f39,plain,(
    ! [X0,X1] :
      ( r1_tarski(k1_relat_1(X1),X0)
      | ~ v4_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f11,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k2_relat_1(X2) = k2_relset_1(X0,X1,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f22,plain,(
    ! [X0,X1,X2] :
      ( k2_relat_1(X2) = k2_relset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f48,plain,(
    ! [X2,X0,X1] :
      ( k2_relat_1(X2) = k2_relset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f51,plain,
    ( ~ r1_tarski(sK2,k2_relset_1(sK0,sK1,sK3))
    | ~ r1_tarski(sK2,k1_relset_1(sK0,sK1,sK3)) ),
    inference(cnf_transformation,[],[f31])).

fof(f44,plain,(
    ! [X0] : k1_relat_1(k6_relat_1(X0)) = X0 ),
    inference(cnf_transformation,[],[f8])).

fof(f10,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k1_relat_1(X2) = k1_relset_1(X0,X1,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f21,plain,(
    ! [X0,X1,X2] :
      ( k1_relat_1(X2) = k1_relset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f47,plain,(
    ! [X2,X0,X1] :
      ( k1_relat_1(X2) = k1_relset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f32,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | X0 != X1 ) ),
    inference(cnf_transformation,[],[f26])).

fof(f53,plain,(
    ! [X1] : r1_tarski(X1,X1) ),
    inference(equality_resolution,[],[f32])).

cnf(c_18,negated_conjecture,
    ( r1_tarski(k6_relat_1(sK2),sK3) ),
    inference(cnf_transformation,[],[f50])).

cnf(c_737,plain,
    ( r1_tarski(k6_relat_1(sK2),sK3) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_18])).

cnf(c_1,plain,
    ( r1_tarski(X0,X0) ),
    inference(cnf_transformation,[],[f52])).

cnf(c_751,plain,
    ( r1_tarski(X0,X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1])).

cnf(c_7,plain,
    ( v4_relat_1(X0,X1)
    | ~ r1_tarski(k1_relat_1(X0),X1)
    | ~ v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f40])).

cnf(c_746,plain,
    ( v4_relat_1(X0,X1) = iProver_top
    | r1_tarski(k1_relat_1(X0),X1) != iProver_top
    | v1_relat_1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_7])).

cnf(c_1726,plain,
    ( v4_relat_1(X0,k1_relat_1(X0)) = iProver_top
    | v1_relat_1(X0) != iProver_top ),
    inference(superposition,[status(thm)],[c_751,c_746])).

cnf(c_3,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(X1))
    | ~ r1_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f36])).

cnf(c_750,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(X1)) = iProver_top
    | r1_tarski(X0,X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3])).

cnf(c_5,plain,
    ( ~ v4_relat_1(X0,X1)
    | v4_relat_1(X2,X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(X0))
    | ~ v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f37])).

cnf(c_748,plain,
    ( v4_relat_1(X0,X1) != iProver_top
    | v4_relat_1(X2,X1) = iProver_top
    | m1_subset_1(X2,k1_zfmisc_1(X0)) != iProver_top
    | v1_relat_1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_5])).

cnf(c_2122,plain,
    ( v4_relat_1(X0,X1) != iProver_top
    | v4_relat_1(X2,X1) = iProver_top
    | r1_tarski(X2,X0) != iProver_top
    | v1_relat_1(X0) != iProver_top ),
    inference(superposition,[status(thm)],[c_750,c_748])).

cnf(c_5576,plain,
    ( v4_relat_1(X0,k1_relat_1(X1)) = iProver_top
    | r1_tarski(X0,X1) != iProver_top
    | v1_relat_1(X1) != iProver_top ),
    inference(superposition,[status(thm)],[c_1726,c_2122])).

cnf(c_7772,plain,
    ( v4_relat_1(X0,k1_relat_1(X1)) = iProver_top
    | r1_tarski(X2,X1) != iProver_top
    | r1_tarski(X0,X2) != iProver_top
    | v1_relat_1(X2) != iProver_top
    | v1_relat_1(X1) != iProver_top ),
    inference(superposition,[status(thm)],[c_5576,c_2122])).

cnf(c_15460,plain,
    ( v4_relat_1(k6_relat_1(sK2),k1_relat_1(X0)) = iProver_top
    | r1_tarski(sK3,X0) != iProver_top
    | v1_relat_1(X0) != iProver_top
    | v1_relat_1(sK3) != iProver_top ),
    inference(superposition,[status(thm)],[c_737,c_7772])).

cnf(c_15514,plain,
    ( v4_relat_1(k6_relat_1(sK2),k1_relat_1(sK3)) = iProver_top
    | r1_tarski(sK3,sK3) != iProver_top
    | v1_relat_1(sK3) != iProver_top ),
    inference(instantiation,[status(thm)],[c_15460])).

cnf(c_9,plain,
    ( v5_relat_1(X0,X1)
    | ~ r1_tarski(k2_relat_1(X0),X1)
    | ~ v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f42])).

cnf(c_744,plain,
    ( v5_relat_1(X0,X1) = iProver_top
    | r1_tarski(k2_relat_1(X0),X1) != iProver_top
    | v1_relat_1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_9])).

cnf(c_1577,plain,
    ( v5_relat_1(X0,k2_relat_1(X0)) = iProver_top
    | v1_relat_1(X0) != iProver_top ),
    inference(superposition,[status(thm)],[c_751,c_744])).

cnf(c_6,plain,
    ( ~ v5_relat_1(X0,X1)
    | v5_relat_1(X2,X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(X0))
    | ~ v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f38])).

cnf(c_747,plain,
    ( v5_relat_1(X0,X1) != iProver_top
    | v5_relat_1(X2,X1) = iProver_top
    | m1_subset_1(X2,k1_zfmisc_1(X0)) != iProver_top
    | v1_relat_1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_6])).

cnf(c_1985,plain,
    ( v5_relat_1(X0,X1) != iProver_top
    | v5_relat_1(X2,X1) = iProver_top
    | r1_tarski(X2,X0) != iProver_top
    | v1_relat_1(X0) != iProver_top ),
    inference(superposition,[status(thm)],[c_750,c_747])).

cnf(c_4964,plain,
    ( v5_relat_1(X0,k2_relat_1(X1)) = iProver_top
    | r1_tarski(X0,X1) != iProver_top
    | v1_relat_1(X1) != iProver_top ),
    inference(superposition,[status(thm)],[c_1577,c_1985])).

cnf(c_7677,plain,
    ( v5_relat_1(X0,k2_relat_1(X1)) = iProver_top
    | r1_tarski(X2,X1) != iProver_top
    | r1_tarski(X0,X2) != iProver_top
    | v1_relat_1(X2) != iProver_top
    | v1_relat_1(X1) != iProver_top ),
    inference(superposition,[status(thm)],[c_4964,c_1985])).

cnf(c_10685,plain,
    ( v5_relat_1(k6_relat_1(sK2),k2_relat_1(X0)) = iProver_top
    | r1_tarski(sK3,X0) != iProver_top
    | v1_relat_1(X0) != iProver_top
    | v1_relat_1(sK3) != iProver_top ),
    inference(superposition,[status(thm)],[c_737,c_7677])).

cnf(c_19,negated_conjecture,
    ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ),
    inference(cnf_transformation,[],[f49])).

cnf(c_20,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_19])).

cnf(c_14,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f46])).

cnf(c_894,plain,
    ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    | v1_relat_1(sK3) ),
    inference(instantiation,[status(thm)],[c_14])).

cnf(c_895,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) != iProver_top
    | v1_relat_1(sK3) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_894])).

cnf(c_10881,plain,
    ( v1_relat_1(X0) != iProver_top
    | r1_tarski(sK3,X0) != iProver_top
    | v5_relat_1(k6_relat_1(sK2),k2_relat_1(X0)) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_10685,c_20,c_895])).

cnf(c_10882,plain,
    ( v5_relat_1(k6_relat_1(sK2),k2_relat_1(X0)) = iProver_top
    | r1_tarski(sK3,X0) != iProver_top
    | v1_relat_1(X0) != iProver_top ),
    inference(renaming,[status(thm)],[c_10881])).

cnf(c_12,plain,
    ( k2_relat_1(k6_relat_1(X0)) = X0 ),
    inference(cnf_transformation,[],[f45])).

cnf(c_10,plain,
    ( ~ v5_relat_1(X0,X1)
    | r1_tarski(k2_relat_1(X0),X1)
    | ~ v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f41])).

cnf(c_743,plain,
    ( v5_relat_1(X0,X1) != iProver_top
    | r1_tarski(k2_relat_1(X0),X1) = iProver_top
    | v1_relat_1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_10])).

cnf(c_1467,plain,
    ( v5_relat_1(k6_relat_1(X0),X1) != iProver_top
    | r1_tarski(X0,X1) = iProver_top
    | v1_relat_1(k6_relat_1(X0)) != iProver_top ),
    inference(superposition,[status(thm)],[c_12,c_743])).

cnf(c_11,plain,
    ( v1_relat_1(k6_relat_1(X0)) ),
    inference(cnf_transformation,[],[f43])).

cnf(c_34,plain,
    ( v1_relat_1(k6_relat_1(X0)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_11])).

cnf(c_1744,plain,
    ( r1_tarski(X0,X1) = iProver_top
    | v5_relat_1(k6_relat_1(X0),X1) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_1467,c_34])).

cnf(c_1745,plain,
    ( v5_relat_1(k6_relat_1(X0),X1) != iProver_top
    | r1_tarski(X0,X1) = iProver_top ),
    inference(renaming,[status(thm)],[c_1744])).

cnf(c_10893,plain,
    ( r1_tarski(sK3,X0) != iProver_top
    | r1_tarski(sK2,k2_relat_1(X0)) = iProver_top
    | v1_relat_1(X0) != iProver_top ),
    inference(superposition,[status(thm)],[c_10882,c_1745])).

cnf(c_10970,plain,
    ( r1_tarski(sK3,sK3) != iProver_top
    | r1_tarski(sK2,k2_relat_1(sK3)) = iProver_top
    | v1_relat_1(sK3) != iProver_top ),
    inference(instantiation,[status(thm)],[c_10893])).

cnf(c_5508,plain,
    ( v1_relat_1(k6_relat_1(sK2)) ),
    inference(instantiation,[status(thm)],[c_11])).

cnf(c_5509,plain,
    ( v1_relat_1(k6_relat_1(sK2)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_5508])).

cnf(c_8,plain,
    ( ~ v4_relat_1(X0,X1)
    | r1_tarski(k1_relat_1(X0),X1)
    | ~ v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f39])).

cnf(c_1647,plain,
    ( ~ v4_relat_1(k6_relat_1(X0),X1)
    | r1_tarski(k1_relat_1(k6_relat_1(X0)),X1)
    | ~ v1_relat_1(k6_relat_1(X0)) ),
    inference(instantiation,[status(thm)],[c_8])).

cnf(c_2924,plain,
    ( ~ v4_relat_1(k6_relat_1(sK2),k1_relat_1(sK3))
    | r1_tarski(k1_relat_1(k6_relat_1(sK2)),k1_relat_1(sK3))
    | ~ v1_relat_1(k6_relat_1(sK2)) ),
    inference(instantiation,[status(thm)],[c_1647])).

cnf(c_2925,plain,
    ( v4_relat_1(k6_relat_1(sK2),k1_relat_1(sK3)) != iProver_top
    | r1_tarski(k1_relat_1(k6_relat_1(sK2)),k1_relat_1(sK3)) = iProver_top
    | v1_relat_1(k6_relat_1(sK2)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2924])).

cnf(c_332,plain,
    ( ~ r1_tarski(X0,X1)
    | r1_tarski(X2,X3)
    | X2 != X0
    | X3 != X1 ),
    theory(equality)).

cnf(c_944,plain,
    ( ~ r1_tarski(X0,X1)
    | r1_tarski(sK2,k1_relset_1(sK0,sK1,sK3))
    | k1_relset_1(sK0,sK1,sK3) != X1
    | sK2 != X0 ),
    inference(instantiation,[status(thm)],[c_332])).

cnf(c_1804,plain,
    ( ~ r1_tarski(k1_relat_1(k6_relat_1(sK2)),X0)
    | r1_tarski(sK2,k1_relset_1(sK0,sK1,sK3))
    | k1_relset_1(sK0,sK1,sK3) != X0
    | sK2 != k1_relat_1(k6_relat_1(sK2)) ),
    inference(instantiation,[status(thm)],[c_944])).

cnf(c_2677,plain,
    ( ~ r1_tarski(k1_relat_1(k6_relat_1(sK2)),k1_relat_1(sK3))
    | r1_tarski(sK2,k1_relset_1(sK0,sK1,sK3))
    | k1_relset_1(sK0,sK1,sK3) != k1_relat_1(sK3)
    | sK2 != k1_relat_1(k6_relat_1(sK2)) ),
    inference(instantiation,[status(thm)],[c_1804])).

cnf(c_2678,plain,
    ( k1_relset_1(sK0,sK1,sK3) != k1_relat_1(sK3)
    | sK2 != k1_relat_1(k6_relat_1(sK2))
    | r1_tarski(k1_relat_1(k6_relat_1(sK2)),k1_relat_1(sK3)) != iProver_top
    | r1_tarski(sK2,k1_relset_1(sK0,sK1,sK3)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2677])).

cnf(c_736,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_19])).

cnf(c_16,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k2_relset_1(X1,X2,X0) = k2_relat_1(X0) ),
    inference(cnf_transformation,[],[f48])).

cnf(c_739,plain,
    ( k2_relset_1(X0,X1,X2) = k2_relat_1(X2)
    | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_16])).

cnf(c_1214,plain,
    ( k2_relset_1(sK0,sK1,sK3) = k2_relat_1(sK3) ),
    inference(superposition,[status(thm)],[c_736,c_739])).

cnf(c_17,negated_conjecture,
    ( ~ r1_tarski(sK2,k2_relset_1(sK0,sK1,sK3))
    | ~ r1_tarski(sK2,k1_relset_1(sK0,sK1,sK3)) ),
    inference(cnf_transformation,[],[f51])).

cnf(c_738,plain,
    ( r1_tarski(sK2,k2_relset_1(sK0,sK1,sK3)) != iProver_top
    | r1_tarski(sK2,k1_relset_1(sK0,sK1,sK3)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_17])).

cnf(c_2395,plain,
    ( r1_tarski(sK2,k1_relset_1(sK0,sK1,sK3)) != iProver_top
    | r1_tarski(sK2,k2_relat_1(sK3)) != iProver_top ),
    inference(demodulation,[status(thm)],[c_1214,c_738])).

cnf(c_13,plain,
    ( k1_relat_1(k6_relat_1(X0)) = X0 ),
    inference(cnf_transformation,[],[f44])).

cnf(c_1561,plain,
    ( k1_relat_1(k6_relat_1(sK2)) = sK2 ),
    inference(instantiation,[status(thm)],[c_13])).

cnf(c_331,plain,
    ( X0 != X1
    | X2 != X1
    | X2 = X0 ),
    theory(equality)).

cnf(c_1003,plain,
    ( X0 != X1
    | sK2 != X1
    | sK2 = X0 ),
    inference(instantiation,[status(thm)],[c_331])).

cnf(c_1184,plain,
    ( X0 != sK2
    | sK2 = X0
    | sK2 != sK2 ),
    inference(instantiation,[status(thm)],[c_1003])).

cnf(c_1560,plain,
    ( k1_relat_1(k6_relat_1(sK2)) != sK2
    | sK2 = k1_relat_1(k6_relat_1(sK2))
    | sK2 != sK2 ),
    inference(instantiation,[status(thm)],[c_1184])).

cnf(c_330,plain,
    ( X0 = X0 ),
    theory(equality)).

cnf(c_998,plain,
    ( sK2 = sK2 ),
    inference(instantiation,[status(thm)],[c_330])).

cnf(c_15,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k1_relset_1(X1,X2,X0) = k1_relat_1(X0) ),
    inference(cnf_transformation,[],[f47])).

cnf(c_923,plain,
    ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    | k1_relset_1(sK0,sK1,sK3) = k1_relat_1(sK3) ),
    inference(instantiation,[status(thm)],[c_15])).

cnf(c_2,plain,
    ( r1_tarski(X0,X0) ),
    inference(cnf_transformation,[],[f53])).

cnf(c_57,plain,
    ( r1_tarski(X0,X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2])).

cnf(c_59,plain,
    ( r1_tarski(sK3,sK3) = iProver_top ),
    inference(instantiation,[status(thm)],[c_57])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_15514,c_10970,c_5509,c_2925,c_2678,c_2395,c_1561,c_1560,c_998,c_923,c_895,c_59,c_20,c_19])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.12  % Command    : iproveropt_run.sh %d %s
% 0.13/0.33  % Computer   : n021.cluster.edu
% 0.13/0.33  % Model      : x86_64 x86_64
% 0.13/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.33  % Memory     : 8042.1875MB
% 0.13/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.33  % CPULimit   : 60
% 0.13/0.33  % WCLimit    : 600
% 0.13/0.33  % DateTime   : Tue Dec  1 15:18:34 EST 2020
% 0.13/0.33  % CPUTime    : 
% 0.13/0.34  % Running in FOF mode
% 3.99/0.99  % SZS status Started for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.99/0.99  
% 3.99/0.99  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 3.99/0.99  
% 3.99/0.99  ------  iProver source info
% 3.99/0.99  
% 3.99/0.99  git: date: 2020-06-30 10:37:57 +0100
% 3.99/0.99  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 3.99/0.99  git: non_committed_changes: false
% 3.99/0.99  git: last_make_outside_of_git: false
% 3.99/0.99  
% 3.99/0.99  ------ 
% 3.99/0.99  
% 3.99/0.99  ------ Input Options
% 3.99/0.99  
% 3.99/0.99  --out_options                           all
% 3.99/0.99  --tptp_safe_out                         true
% 3.99/0.99  --problem_path                          ""
% 3.99/0.99  --include_path                          ""
% 3.99/0.99  --clausifier                            res/vclausify_rel
% 3.99/0.99  --clausifier_options                    --mode clausify
% 3.99/0.99  --stdin                                 false
% 3.99/0.99  --stats_out                             sel
% 3.99/0.99  
% 3.99/0.99  ------ General Options
% 3.99/0.99  
% 3.99/0.99  --fof                                   false
% 3.99/0.99  --time_out_real                         604.99
% 3.99/0.99  --time_out_virtual                      -1.
% 3.99/0.99  --symbol_type_check                     false
% 3.99/0.99  --clausify_out                          false
% 3.99/0.99  --sig_cnt_out                           false
% 3.99/0.99  --trig_cnt_out                          false
% 3.99/0.99  --trig_cnt_out_tolerance                1.
% 3.99/0.99  --trig_cnt_out_sk_spl                   false
% 3.99/0.99  --abstr_cl_out                          false
% 3.99/0.99  
% 3.99/0.99  ------ Global Options
% 3.99/0.99  
% 3.99/0.99  --schedule                              none
% 3.99/0.99  --add_important_lit                     false
% 3.99/0.99  --prop_solver_per_cl                    1000
% 3.99/0.99  --min_unsat_core                        false
% 3.99/0.99  --soft_assumptions                      false
% 3.99/0.99  --soft_lemma_size                       3
% 3.99/0.99  --prop_impl_unit_size                   0
% 3.99/0.99  --prop_impl_unit                        []
% 3.99/0.99  --share_sel_clauses                     true
% 3.99/0.99  --reset_solvers                         false
% 3.99/0.99  --bc_imp_inh                            [conj_cone]
% 3.99/0.99  --conj_cone_tolerance                   3.
% 3.99/0.99  --extra_neg_conj                        none
% 3.99/0.99  --large_theory_mode                     true
% 3.99/0.99  --prolific_symb_bound                   200
% 3.99/0.99  --lt_threshold                          2000
% 3.99/0.99  --clause_weak_htbl                      true
% 3.99/0.99  --gc_record_bc_elim                     false
% 3.99/0.99  
% 3.99/0.99  ------ Preprocessing Options
% 3.99/0.99  
% 3.99/0.99  --preprocessing_flag                    true
% 3.99/0.99  --time_out_prep_mult                    0.1
% 3.99/0.99  --splitting_mode                        input
% 3.99/0.99  --splitting_grd                         true
% 3.99/0.99  --splitting_cvd                         false
% 3.99/0.99  --splitting_cvd_svl                     false
% 3.99/0.99  --splitting_nvd                         32
% 3.99/0.99  --sub_typing                            true
% 3.99/0.99  --prep_gs_sim                           false
% 3.99/0.99  --prep_unflatten                        true
% 3.99/0.99  --prep_res_sim                          true
% 3.99/0.99  --prep_upred                            true
% 3.99/0.99  --prep_sem_filter                       exhaustive
% 3.99/0.99  --prep_sem_filter_out                   false
% 3.99/0.99  --pred_elim                             false
% 3.99/0.99  --res_sim_input                         true
% 3.99/0.99  --eq_ax_congr_red                       true
% 3.99/0.99  --pure_diseq_elim                       true
% 3.99/0.99  --brand_transform                       false
% 3.99/0.99  --non_eq_to_eq                          false
% 3.99/0.99  --prep_def_merge                        true
% 3.99/0.99  --prep_def_merge_prop_impl              false
% 3.99/0.99  --prep_def_merge_mbd                    true
% 3.99/0.99  --prep_def_merge_tr_red                 false
% 3.99/0.99  --prep_def_merge_tr_cl                  false
% 3.99/0.99  --smt_preprocessing                     true
% 3.99/0.99  --smt_ac_axioms                         fast
% 3.99/0.99  --preprocessed_out                      false
% 3.99/0.99  --preprocessed_stats                    false
% 3.99/0.99  
% 3.99/0.99  ------ Abstraction refinement Options
% 3.99/0.99  
% 3.99/0.99  --abstr_ref                             []
% 3.99/0.99  --abstr_ref_prep                        false
% 3.99/0.99  --abstr_ref_until_sat                   false
% 3.99/0.99  --abstr_ref_sig_restrict                funpre
% 3.99/0.99  --abstr_ref_af_restrict_to_split_sk     false
% 3.99/0.99  --abstr_ref_under                       []
% 3.99/0.99  
% 3.99/0.99  ------ SAT Options
% 3.99/0.99  
% 3.99/0.99  --sat_mode                              false
% 3.99/0.99  --sat_fm_restart_options                ""
% 3.99/0.99  --sat_gr_def                            false
% 3.99/0.99  --sat_epr_types                         true
% 3.99/0.99  --sat_non_cyclic_types                  false
% 3.99/0.99  --sat_finite_models                     false
% 3.99/0.99  --sat_fm_lemmas                         false
% 3.99/0.99  --sat_fm_prep                           false
% 3.99/0.99  --sat_fm_uc_incr                        true
% 3.99/0.99  --sat_out_model                         small
% 3.99/0.99  --sat_out_clauses                       false
% 3.99/0.99  
% 3.99/0.99  ------ QBF Options
% 3.99/0.99  
% 3.99/0.99  --qbf_mode                              false
% 3.99/0.99  --qbf_elim_univ                         false
% 3.99/0.99  --qbf_dom_inst                          none
% 3.99/0.99  --qbf_dom_pre_inst                      false
% 3.99/0.99  --qbf_sk_in                             false
% 3.99/0.99  --qbf_pred_elim                         true
% 3.99/0.99  --qbf_split                             512
% 3.99/0.99  
% 3.99/0.99  ------ BMC1 Options
% 3.99/0.99  
% 3.99/0.99  --bmc1_incremental                      false
% 3.99/0.99  --bmc1_axioms                           reachable_all
% 3.99/0.99  --bmc1_min_bound                        0
% 3.99/0.99  --bmc1_max_bound                        -1
% 3.99/0.99  --bmc1_max_bound_default                -1
% 3.99/0.99  --bmc1_symbol_reachability              true
% 3.99/0.99  --bmc1_property_lemmas                  false
% 3.99/0.99  --bmc1_k_induction                      false
% 3.99/0.99  --bmc1_non_equiv_states                 false
% 3.99/0.99  --bmc1_deadlock                         false
% 3.99/0.99  --bmc1_ucm                              false
% 3.99/0.99  --bmc1_add_unsat_core                   none
% 3.99/0.99  --bmc1_unsat_core_children              false
% 3.99/0.99  --bmc1_unsat_core_extrapolate_axioms    false
% 3.99/0.99  --bmc1_out_stat                         full
% 3.99/0.99  --bmc1_ground_init                      false
% 3.99/0.99  --bmc1_pre_inst_next_state              false
% 3.99/0.99  --bmc1_pre_inst_state                   false
% 3.99/0.99  --bmc1_pre_inst_reach_state             false
% 3.99/0.99  --bmc1_out_unsat_core                   false
% 3.99/0.99  --bmc1_aig_witness_out                  false
% 3.99/0.99  --bmc1_verbose                          false
% 3.99/0.99  --bmc1_dump_clauses_tptp                false
% 3.99/0.99  --bmc1_dump_unsat_core_tptp             false
% 3.99/0.99  --bmc1_dump_file                        -
% 3.99/0.99  --bmc1_ucm_expand_uc_limit              128
% 3.99/0.99  --bmc1_ucm_n_expand_iterations          6
% 3.99/0.99  --bmc1_ucm_extend_mode                  1
% 3.99/0.99  --bmc1_ucm_init_mode                    2
% 3.99/0.99  --bmc1_ucm_cone_mode                    none
% 3.99/0.99  --bmc1_ucm_reduced_relation_type        0
% 3.99/0.99  --bmc1_ucm_relax_model                  4
% 3.99/0.99  --bmc1_ucm_full_tr_after_sat            true
% 3.99/0.99  --bmc1_ucm_expand_neg_assumptions       false
% 3.99/0.99  --bmc1_ucm_layered_model                none
% 3.99/0.99  --bmc1_ucm_max_lemma_size               10
% 3.99/0.99  
% 3.99/0.99  ------ AIG Options
% 3.99/0.99  
% 3.99/0.99  --aig_mode                              false
% 3.99/0.99  
% 3.99/0.99  ------ Instantiation Options
% 3.99/0.99  
% 3.99/0.99  --instantiation_flag                    true
% 3.99/0.99  --inst_sos_flag                         false
% 3.99/0.99  --inst_sos_phase                        true
% 3.99/0.99  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 3.99/0.99  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 3.99/0.99  --inst_lit_sel_side                     num_symb
% 3.99/0.99  --inst_solver_per_active                1400
% 3.99/0.99  --inst_solver_calls_frac                1.
% 3.99/0.99  --inst_passive_queue_type               priority_queues
% 3.99/0.99  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 3.99/0.99  --inst_passive_queues_freq              [25;2]
% 3.99/0.99  --inst_dismatching                      true
% 3.99/0.99  --inst_eager_unprocessed_to_passive     true
% 3.99/0.99  --inst_prop_sim_given                   true
% 3.99/0.99  --inst_prop_sim_new                     false
% 3.99/0.99  --inst_subs_new                         false
% 3.99/1.00  --inst_eq_res_simp                      false
% 3.99/1.00  --inst_subs_given                       false
% 3.99/1.00  --inst_orphan_elimination               true
% 3.99/1.00  --inst_learning_loop_flag               true
% 3.99/1.00  --inst_learning_start                   3000
% 3.99/1.00  --inst_learning_factor                  2
% 3.99/1.00  --inst_start_prop_sim_after_learn       3
% 3.99/1.00  --inst_sel_renew                        solver
% 3.99/1.00  --inst_lit_activity_flag                true
% 3.99/1.00  --inst_restr_to_given                   false
% 3.99/1.00  --inst_activity_threshold               500
% 3.99/1.00  --inst_out_proof                        true
% 3.99/1.00  
% 3.99/1.00  ------ Resolution Options
% 3.99/1.00  
% 3.99/1.00  --resolution_flag                       true
% 3.99/1.00  --res_lit_sel                           adaptive
% 3.99/1.00  --res_lit_sel_side                      none
% 3.99/1.00  --res_ordering                          kbo
% 3.99/1.00  --res_to_prop_solver                    active
% 3.99/1.00  --res_prop_simpl_new                    false
% 3.99/1.00  --res_prop_simpl_given                  true
% 3.99/1.00  --res_passive_queue_type                priority_queues
% 3.99/1.00  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 3.99/1.00  --res_passive_queues_freq               [15;5]
% 3.99/1.00  --res_forward_subs                      full
% 3.99/1.00  --res_backward_subs                     full
% 3.99/1.00  --res_forward_subs_resolution           true
% 3.99/1.00  --res_backward_subs_resolution          true
% 3.99/1.00  --res_orphan_elimination                true
% 3.99/1.00  --res_time_limit                        2.
% 3.99/1.00  --res_out_proof                         true
% 3.99/1.00  
% 3.99/1.00  ------ Superposition Options
% 3.99/1.00  
% 3.99/1.00  --superposition_flag                    true
% 3.99/1.00  --sup_passive_queue_type                priority_queues
% 3.99/1.00  --sup_passive_queues                    [[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 3.99/1.00  --sup_passive_queues_freq               [1;4]
% 3.99/1.00  --demod_completeness_check              fast
% 3.99/1.00  --demod_use_ground                      true
% 3.99/1.00  --sup_to_prop_solver                    passive
% 3.99/1.00  --sup_prop_simpl_new                    true
% 3.99/1.00  --sup_prop_simpl_given                  true
% 3.99/1.00  --sup_fun_splitting                     false
% 3.99/1.00  --sup_smt_interval                      50000
% 3.99/1.00  
% 3.99/1.00  ------ Superposition Simplification Setup
% 3.99/1.00  
% 3.99/1.00  --sup_indices_passive                   []
% 3.99/1.00  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.99/1.00  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.99/1.00  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.99/1.00  --sup_full_triv                         [TrivRules;PropSubs]
% 3.99/1.00  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.99/1.00  --sup_full_bw                           [BwDemod]
% 3.99/1.00  --sup_immed_triv                        [TrivRules]
% 3.99/1.00  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 3.99/1.00  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.99/1.00  --sup_immed_bw_main                     []
% 3.99/1.00  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 3.99/1.00  --sup_input_triv                        [Unflattening;TrivRules]
% 3.99/1.00  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.99/1.00  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 3.99/1.00  
% 3.99/1.00  ------ Combination Options
% 3.99/1.00  
% 3.99/1.00  --comb_res_mult                         3
% 3.99/1.00  --comb_sup_mult                         2
% 3.99/1.00  --comb_inst_mult                        10
% 3.99/1.00  
% 3.99/1.00  ------ Debug Options
% 3.99/1.00  
% 3.99/1.00  --dbg_backtrace                         false
% 3.99/1.00  --dbg_dump_prop_clauses                 false
% 3.99/1.00  --dbg_dump_prop_clauses_file            -
% 3.99/1.00  --dbg_out_stat                          false
% 3.99/1.00  ------ Parsing...
% 3.99/1.00  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 3.99/1.00  
% 3.99/1.00  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 1 0s  sf_e 
% 3.99/1.00  
% 3.99/1.00  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 3.99/1.00  
% 3.99/1.00  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 3.99/1.00  ------ Proving...
% 3.99/1.00  ------ Problem Properties 
% 3.99/1.00  
% 3.99/1.00  
% 3.99/1.00  clauses                                 19
% 3.99/1.00  conjectures                             3
% 3.99/1.00  EPR                                     2
% 3.99/1.00  Horn                                    19
% 3.99/1.00  unary                                   6
% 3.99/1.00  binary                                  6
% 3.99/1.00  lits                                    41
% 3.99/1.00  lits eq                                 5
% 3.99/1.00  fd_pure                                 0
% 3.99/1.00  fd_pseudo                               0
% 3.99/1.00  fd_cond                                 0
% 3.99/1.00  fd_pseudo_cond                          1
% 3.99/1.00  AC symbols                              0
% 3.99/1.00  
% 3.99/1.00  ------ Input Options Time Limit: Unbounded
% 3.99/1.00  
% 3.99/1.00  
% 3.99/1.00  ------ 
% 3.99/1.00  Current options:
% 3.99/1.00  ------ 
% 3.99/1.00  
% 3.99/1.00  ------ Input Options
% 3.99/1.00  
% 3.99/1.00  --out_options                           all
% 3.99/1.00  --tptp_safe_out                         true
% 3.99/1.00  --problem_path                          ""
% 3.99/1.00  --include_path                          ""
% 3.99/1.00  --clausifier                            res/vclausify_rel
% 3.99/1.00  --clausifier_options                    --mode clausify
% 3.99/1.00  --stdin                                 false
% 3.99/1.00  --stats_out                             sel
% 3.99/1.00  
% 3.99/1.00  ------ General Options
% 3.99/1.00  
% 3.99/1.00  --fof                                   false
% 3.99/1.00  --time_out_real                         604.99
% 3.99/1.00  --time_out_virtual                      -1.
% 3.99/1.00  --symbol_type_check                     false
% 3.99/1.00  --clausify_out                          false
% 3.99/1.00  --sig_cnt_out                           false
% 3.99/1.00  --trig_cnt_out                          false
% 3.99/1.00  --trig_cnt_out_tolerance                1.
% 3.99/1.00  --trig_cnt_out_sk_spl                   false
% 3.99/1.00  --abstr_cl_out                          false
% 3.99/1.00  
% 3.99/1.00  ------ Global Options
% 3.99/1.00  
% 3.99/1.00  --schedule                              none
% 3.99/1.00  --add_important_lit                     false
% 3.99/1.00  --prop_solver_per_cl                    1000
% 3.99/1.00  --min_unsat_core                        false
% 3.99/1.00  --soft_assumptions                      false
% 3.99/1.00  --soft_lemma_size                       3
% 3.99/1.00  --prop_impl_unit_size                   0
% 3.99/1.00  --prop_impl_unit                        []
% 3.99/1.00  --share_sel_clauses                     true
% 3.99/1.00  --reset_solvers                         false
% 3.99/1.00  --bc_imp_inh                            [conj_cone]
% 3.99/1.00  --conj_cone_tolerance                   3.
% 3.99/1.00  --extra_neg_conj                        none
% 3.99/1.00  --large_theory_mode                     true
% 3.99/1.00  --prolific_symb_bound                   200
% 3.99/1.00  --lt_threshold                          2000
% 3.99/1.00  --clause_weak_htbl                      true
% 3.99/1.00  --gc_record_bc_elim                     false
% 3.99/1.00  
% 3.99/1.00  ------ Preprocessing Options
% 3.99/1.00  
% 3.99/1.00  --preprocessing_flag                    true
% 3.99/1.00  --time_out_prep_mult                    0.1
% 3.99/1.00  --splitting_mode                        input
% 3.99/1.00  --splitting_grd                         true
% 3.99/1.00  --splitting_cvd                         false
% 3.99/1.00  --splitting_cvd_svl                     false
% 3.99/1.00  --splitting_nvd                         32
% 3.99/1.00  --sub_typing                            true
% 3.99/1.00  --prep_gs_sim                           false
% 3.99/1.00  --prep_unflatten                        true
% 3.99/1.00  --prep_res_sim                          true
% 3.99/1.00  --prep_upred                            true
% 3.99/1.00  --prep_sem_filter                       exhaustive
% 3.99/1.00  --prep_sem_filter_out                   false
% 3.99/1.00  --pred_elim                             false
% 3.99/1.00  --res_sim_input                         true
% 3.99/1.00  --eq_ax_congr_red                       true
% 3.99/1.00  --pure_diseq_elim                       true
% 3.99/1.00  --brand_transform                       false
% 3.99/1.00  --non_eq_to_eq                          false
% 3.99/1.00  --prep_def_merge                        true
% 3.99/1.00  --prep_def_merge_prop_impl              false
% 3.99/1.00  --prep_def_merge_mbd                    true
% 3.99/1.00  --prep_def_merge_tr_red                 false
% 3.99/1.00  --prep_def_merge_tr_cl                  false
% 3.99/1.00  --smt_preprocessing                     true
% 3.99/1.00  --smt_ac_axioms                         fast
% 3.99/1.00  --preprocessed_out                      false
% 3.99/1.00  --preprocessed_stats                    false
% 3.99/1.00  
% 3.99/1.00  ------ Abstraction refinement Options
% 3.99/1.00  
% 3.99/1.00  --abstr_ref                             []
% 3.99/1.00  --abstr_ref_prep                        false
% 3.99/1.00  --abstr_ref_until_sat                   false
% 3.99/1.00  --abstr_ref_sig_restrict                funpre
% 3.99/1.00  --abstr_ref_af_restrict_to_split_sk     false
% 3.99/1.00  --abstr_ref_under                       []
% 3.99/1.00  
% 3.99/1.00  ------ SAT Options
% 3.99/1.00  
% 3.99/1.00  --sat_mode                              false
% 3.99/1.00  --sat_fm_restart_options                ""
% 3.99/1.00  --sat_gr_def                            false
% 3.99/1.00  --sat_epr_types                         true
% 3.99/1.00  --sat_non_cyclic_types                  false
% 3.99/1.00  --sat_finite_models                     false
% 3.99/1.00  --sat_fm_lemmas                         false
% 3.99/1.00  --sat_fm_prep                           false
% 3.99/1.00  --sat_fm_uc_incr                        true
% 3.99/1.00  --sat_out_model                         small
% 3.99/1.00  --sat_out_clauses                       false
% 3.99/1.00  
% 3.99/1.00  ------ QBF Options
% 3.99/1.00  
% 3.99/1.00  --qbf_mode                              false
% 3.99/1.00  --qbf_elim_univ                         false
% 3.99/1.00  --qbf_dom_inst                          none
% 3.99/1.00  --qbf_dom_pre_inst                      false
% 3.99/1.00  --qbf_sk_in                             false
% 3.99/1.00  --qbf_pred_elim                         true
% 3.99/1.00  --qbf_split                             512
% 3.99/1.00  
% 3.99/1.00  ------ BMC1 Options
% 3.99/1.00  
% 3.99/1.00  --bmc1_incremental                      false
% 3.99/1.00  --bmc1_axioms                           reachable_all
% 3.99/1.00  --bmc1_min_bound                        0
% 3.99/1.00  --bmc1_max_bound                        -1
% 3.99/1.00  --bmc1_max_bound_default                -1
% 3.99/1.00  --bmc1_symbol_reachability              true
% 3.99/1.00  --bmc1_property_lemmas                  false
% 3.99/1.00  --bmc1_k_induction                      false
% 3.99/1.00  --bmc1_non_equiv_states                 false
% 3.99/1.00  --bmc1_deadlock                         false
% 3.99/1.00  --bmc1_ucm                              false
% 3.99/1.00  --bmc1_add_unsat_core                   none
% 3.99/1.00  --bmc1_unsat_core_children              false
% 3.99/1.00  --bmc1_unsat_core_extrapolate_axioms    false
% 3.99/1.00  --bmc1_out_stat                         full
% 3.99/1.00  --bmc1_ground_init                      false
% 3.99/1.00  --bmc1_pre_inst_next_state              false
% 3.99/1.00  --bmc1_pre_inst_state                   false
% 3.99/1.00  --bmc1_pre_inst_reach_state             false
% 3.99/1.00  --bmc1_out_unsat_core                   false
% 3.99/1.00  --bmc1_aig_witness_out                  false
% 3.99/1.00  --bmc1_verbose                          false
% 3.99/1.00  --bmc1_dump_clauses_tptp                false
% 3.99/1.00  --bmc1_dump_unsat_core_tptp             false
% 3.99/1.00  --bmc1_dump_file                        -
% 3.99/1.00  --bmc1_ucm_expand_uc_limit              128
% 3.99/1.00  --bmc1_ucm_n_expand_iterations          6
% 3.99/1.00  --bmc1_ucm_extend_mode                  1
% 3.99/1.00  --bmc1_ucm_init_mode                    2
% 3.99/1.00  --bmc1_ucm_cone_mode                    none
% 3.99/1.00  --bmc1_ucm_reduced_relation_type        0
% 3.99/1.00  --bmc1_ucm_relax_model                  4
% 3.99/1.00  --bmc1_ucm_full_tr_after_sat            true
% 3.99/1.00  --bmc1_ucm_expand_neg_assumptions       false
% 3.99/1.00  --bmc1_ucm_layered_model                none
% 3.99/1.00  --bmc1_ucm_max_lemma_size               10
% 3.99/1.00  
% 3.99/1.00  ------ AIG Options
% 3.99/1.00  
% 3.99/1.00  --aig_mode                              false
% 3.99/1.00  
% 3.99/1.00  ------ Instantiation Options
% 3.99/1.00  
% 3.99/1.00  --instantiation_flag                    true
% 3.99/1.00  --inst_sos_flag                         false
% 3.99/1.00  --inst_sos_phase                        true
% 3.99/1.00  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 3.99/1.00  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 3.99/1.00  --inst_lit_sel_side                     num_symb
% 3.99/1.00  --inst_solver_per_active                1400
% 3.99/1.00  --inst_solver_calls_frac                1.
% 3.99/1.00  --inst_passive_queue_type               priority_queues
% 3.99/1.00  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 3.99/1.00  --inst_passive_queues_freq              [25;2]
% 3.99/1.00  --inst_dismatching                      true
% 3.99/1.00  --inst_eager_unprocessed_to_passive     true
% 3.99/1.00  --inst_prop_sim_given                   true
% 3.99/1.00  --inst_prop_sim_new                     false
% 3.99/1.00  --inst_subs_new                         false
% 3.99/1.00  --inst_eq_res_simp                      false
% 3.99/1.00  --inst_subs_given                       false
% 3.99/1.00  --inst_orphan_elimination               true
% 3.99/1.00  --inst_learning_loop_flag               true
% 3.99/1.00  --inst_learning_start                   3000
% 3.99/1.00  --inst_learning_factor                  2
% 3.99/1.00  --inst_start_prop_sim_after_learn       3
% 3.99/1.00  --inst_sel_renew                        solver
% 3.99/1.00  --inst_lit_activity_flag                true
% 3.99/1.00  --inst_restr_to_given                   false
% 3.99/1.00  --inst_activity_threshold               500
% 3.99/1.00  --inst_out_proof                        true
% 3.99/1.00  
% 3.99/1.00  ------ Resolution Options
% 3.99/1.00  
% 3.99/1.00  --resolution_flag                       true
% 3.99/1.00  --res_lit_sel                           adaptive
% 3.99/1.00  --res_lit_sel_side                      none
% 3.99/1.00  --res_ordering                          kbo
% 3.99/1.00  --res_to_prop_solver                    active
% 3.99/1.00  --res_prop_simpl_new                    false
% 3.99/1.00  --res_prop_simpl_given                  true
% 3.99/1.00  --res_passive_queue_type                priority_queues
% 3.99/1.00  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 3.99/1.00  --res_passive_queues_freq               [15;5]
% 3.99/1.00  --res_forward_subs                      full
% 3.99/1.00  --res_backward_subs                     full
% 3.99/1.00  --res_forward_subs_resolution           true
% 3.99/1.00  --res_backward_subs_resolution          true
% 3.99/1.00  --res_orphan_elimination                true
% 3.99/1.00  --res_time_limit                        2.
% 3.99/1.00  --res_out_proof                         true
% 3.99/1.00  
% 3.99/1.00  ------ Superposition Options
% 3.99/1.00  
% 3.99/1.00  --superposition_flag                    true
% 3.99/1.00  --sup_passive_queue_type                priority_queues
% 3.99/1.00  --sup_passive_queues                    [[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 3.99/1.00  --sup_passive_queues_freq               [1;4]
% 3.99/1.00  --demod_completeness_check              fast
% 3.99/1.00  --demod_use_ground                      true
% 3.99/1.00  --sup_to_prop_solver                    passive
% 3.99/1.00  --sup_prop_simpl_new                    true
% 3.99/1.00  --sup_prop_simpl_given                  true
% 3.99/1.00  --sup_fun_splitting                     false
% 3.99/1.00  --sup_smt_interval                      50000
% 3.99/1.00  
% 3.99/1.00  ------ Superposition Simplification Setup
% 3.99/1.00  
% 3.99/1.00  --sup_indices_passive                   []
% 3.99/1.00  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.99/1.00  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.99/1.00  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.99/1.00  --sup_full_triv                         [TrivRules;PropSubs]
% 3.99/1.00  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.99/1.00  --sup_full_bw                           [BwDemod]
% 3.99/1.00  --sup_immed_triv                        [TrivRules]
% 3.99/1.00  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 3.99/1.00  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.99/1.00  --sup_immed_bw_main                     []
% 3.99/1.00  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 3.99/1.00  --sup_input_triv                        [Unflattening;TrivRules]
% 3.99/1.00  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.99/1.00  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 3.99/1.00  
% 3.99/1.00  ------ Combination Options
% 3.99/1.00  
% 3.99/1.00  --comb_res_mult                         3
% 3.99/1.00  --comb_sup_mult                         2
% 3.99/1.00  --comb_inst_mult                        10
% 3.99/1.00  
% 3.99/1.00  ------ Debug Options
% 3.99/1.00  
% 3.99/1.00  --dbg_backtrace                         false
% 3.99/1.00  --dbg_dump_prop_clauses                 false
% 3.99/1.00  --dbg_dump_prop_clauses_file            -
% 3.99/1.00  --dbg_out_stat                          false
% 3.99/1.00  
% 3.99/1.00  
% 3.99/1.00  
% 3.99/1.00  
% 3.99/1.00  ------ Proving...
% 3.99/1.00  
% 3.99/1.00  
% 3.99/1.00  % SZS status Theorem for theBenchmark.p
% 3.99/1.00  
% 3.99/1.00  % SZS output start CNFRefutation for theBenchmark.p
% 3.99/1.00  
% 3.99/1.00  fof(f12,conjecture,(
% 3.99/1.00    ! [X0,X1,X2,X3] : (m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => (r1_tarski(k6_relat_1(X2),X3) => (r1_tarski(X2,k2_relset_1(X0,X1,X3)) & r1_tarski(X2,k1_relset_1(X0,X1,X3)))))),
% 3.99/1.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.99/1.00  
% 3.99/1.00  fof(f13,negated_conjecture,(
% 3.99/1.00    ~! [X0,X1,X2,X3] : (m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => (r1_tarski(k6_relat_1(X2),X3) => (r1_tarski(X2,k2_relset_1(X0,X1,X3)) & r1_tarski(X2,k1_relset_1(X0,X1,X3)))))),
% 3.99/1.00    inference(negated_conjecture,[],[f12])).
% 3.99/1.00  
% 3.99/1.00  fof(f23,plain,(
% 3.99/1.00    ? [X0,X1,X2,X3] : (((~r1_tarski(X2,k2_relset_1(X0,X1,X3)) | ~r1_tarski(X2,k1_relset_1(X0,X1,X3))) & r1_tarski(k6_relat_1(X2),X3)) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 3.99/1.00    inference(ennf_transformation,[],[f13])).
% 3.99/1.00  
% 3.99/1.00  fof(f24,plain,(
% 3.99/1.00    ? [X0,X1,X2,X3] : ((~r1_tarski(X2,k2_relset_1(X0,X1,X3)) | ~r1_tarski(X2,k1_relset_1(X0,X1,X3))) & r1_tarski(k6_relat_1(X2),X3) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 3.99/1.00    inference(flattening,[],[f23])).
% 3.99/1.00  
% 3.99/1.00  fof(f30,plain,(
% 3.99/1.00    ? [X0,X1,X2,X3] : ((~r1_tarski(X2,k2_relset_1(X0,X1,X3)) | ~r1_tarski(X2,k1_relset_1(X0,X1,X3))) & r1_tarski(k6_relat_1(X2),X3) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) => ((~r1_tarski(sK2,k2_relset_1(sK0,sK1,sK3)) | ~r1_tarski(sK2,k1_relset_1(sK0,sK1,sK3))) & r1_tarski(k6_relat_1(sK2),sK3) & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))))),
% 3.99/1.00    introduced(choice_axiom,[])).
% 3.99/1.00  
% 3.99/1.00  fof(f31,plain,(
% 3.99/1.00    (~r1_tarski(sK2,k2_relset_1(sK0,sK1,sK3)) | ~r1_tarski(sK2,k1_relset_1(sK0,sK1,sK3))) & r1_tarski(k6_relat_1(sK2),sK3) & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))),
% 3.99/1.00    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3])],[f24,f30])).
% 3.99/1.00  
% 3.99/1.00  fof(f50,plain,(
% 3.99/1.00    r1_tarski(k6_relat_1(sK2),sK3)),
% 3.99/1.00    inference(cnf_transformation,[],[f31])).
% 3.99/1.00  
% 3.99/1.00  fof(f1,axiom,(
% 3.99/1.00    ! [X0,X1] : (X0 = X1 <=> (r1_tarski(X1,X0) & r1_tarski(X0,X1)))),
% 3.99/1.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.99/1.00  
% 3.99/1.00  fof(f25,plain,(
% 3.99/1.00    ! [X0,X1] : ((X0 = X1 | (~r1_tarski(X1,X0) | ~r1_tarski(X0,X1))) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 3.99/1.00    inference(nnf_transformation,[],[f1])).
% 3.99/1.00  
% 3.99/1.00  fof(f26,plain,(
% 3.99/1.00    ! [X0,X1] : ((X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 3.99/1.00    inference(flattening,[],[f25])).
% 3.99/1.00  
% 3.99/1.00  fof(f33,plain,(
% 3.99/1.00    ( ! [X0,X1] : (r1_tarski(X1,X0) | X0 != X1) )),
% 3.99/1.00    inference(cnf_transformation,[],[f26])).
% 3.99/1.00  
% 3.99/1.00  fof(f52,plain,(
% 3.99/1.00    ( ! [X1] : (r1_tarski(X1,X1)) )),
% 3.99/1.00    inference(equality_resolution,[],[f33])).
% 3.99/1.00  
% 3.99/1.00  fof(f5,axiom,(
% 3.99/1.00    ! [X0,X1] : (v1_relat_1(X1) => (v4_relat_1(X1,X0) <=> r1_tarski(k1_relat_1(X1),X0)))),
% 3.99/1.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.99/1.00  
% 3.99/1.00  fof(f18,plain,(
% 3.99/1.00    ! [X0,X1] : ((v4_relat_1(X1,X0) <=> r1_tarski(k1_relat_1(X1),X0)) | ~v1_relat_1(X1))),
% 3.99/1.00    inference(ennf_transformation,[],[f5])).
% 3.99/1.00  
% 3.99/1.00  fof(f28,plain,(
% 3.99/1.00    ! [X0,X1] : (((v4_relat_1(X1,X0) | ~r1_tarski(k1_relat_1(X1),X0)) & (r1_tarski(k1_relat_1(X1),X0) | ~v4_relat_1(X1,X0))) | ~v1_relat_1(X1))),
% 3.99/1.00    inference(nnf_transformation,[],[f18])).
% 3.99/1.00  
% 3.99/1.00  fof(f40,plain,(
% 3.99/1.00    ( ! [X0,X1] : (v4_relat_1(X1,X0) | ~r1_tarski(k1_relat_1(X1),X0) | ~v1_relat_1(X1)) )),
% 3.99/1.00    inference(cnf_transformation,[],[f28])).
% 3.99/1.00  
% 3.99/1.00  fof(f2,axiom,(
% 3.99/1.00    ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) <=> r1_tarski(X0,X1))),
% 3.99/1.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.99/1.00  
% 3.99/1.00  fof(f27,plain,(
% 3.99/1.00    ! [X0,X1] : ((m1_subset_1(X0,k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1)) & (r1_tarski(X0,X1) | ~m1_subset_1(X0,k1_zfmisc_1(X1))))),
% 3.99/1.00    inference(nnf_transformation,[],[f2])).
% 3.99/1.00  
% 3.99/1.00  fof(f36,plain,(
% 3.99/1.00    ( ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1)) )),
% 3.99/1.00    inference(cnf_transformation,[],[f27])).
% 3.99/1.00  
% 3.99/1.00  fof(f3,axiom,(
% 3.99/1.00    ! [X0,X1] : ((v4_relat_1(X1,X0) & v1_relat_1(X1)) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(X1)) => v4_relat_1(X2,X0)))),
% 3.99/1.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.99/1.00  
% 3.99/1.00  fof(f14,plain,(
% 3.99/1.00    ! [X0,X1] : (! [X2] : (v4_relat_1(X2,X0) | ~m1_subset_1(X2,k1_zfmisc_1(X1))) | (~v4_relat_1(X1,X0) | ~v1_relat_1(X1)))),
% 3.99/1.00    inference(ennf_transformation,[],[f3])).
% 3.99/1.00  
% 3.99/1.00  fof(f15,plain,(
% 3.99/1.00    ! [X0,X1] : (! [X2] : (v4_relat_1(X2,X0) | ~m1_subset_1(X2,k1_zfmisc_1(X1))) | ~v4_relat_1(X1,X0) | ~v1_relat_1(X1))),
% 3.99/1.00    inference(flattening,[],[f14])).
% 3.99/1.00  
% 3.99/1.00  fof(f37,plain,(
% 3.99/1.00    ( ! [X2,X0,X1] : (v4_relat_1(X2,X0) | ~m1_subset_1(X2,k1_zfmisc_1(X1)) | ~v4_relat_1(X1,X0) | ~v1_relat_1(X1)) )),
% 3.99/1.00    inference(cnf_transformation,[],[f15])).
% 3.99/1.00  
% 3.99/1.00  fof(f6,axiom,(
% 3.99/1.00    ! [X0,X1] : (v1_relat_1(X1) => (v5_relat_1(X1,X0) <=> r1_tarski(k2_relat_1(X1),X0)))),
% 3.99/1.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.99/1.00  
% 3.99/1.00  fof(f19,plain,(
% 3.99/1.00    ! [X0,X1] : ((v5_relat_1(X1,X0) <=> r1_tarski(k2_relat_1(X1),X0)) | ~v1_relat_1(X1))),
% 3.99/1.00    inference(ennf_transformation,[],[f6])).
% 3.99/1.00  
% 3.99/1.00  fof(f29,plain,(
% 3.99/1.00    ! [X0,X1] : (((v5_relat_1(X1,X0) | ~r1_tarski(k2_relat_1(X1),X0)) & (r1_tarski(k2_relat_1(X1),X0) | ~v5_relat_1(X1,X0))) | ~v1_relat_1(X1))),
% 3.99/1.00    inference(nnf_transformation,[],[f19])).
% 3.99/1.00  
% 3.99/1.00  fof(f42,plain,(
% 3.99/1.00    ( ! [X0,X1] : (v5_relat_1(X1,X0) | ~r1_tarski(k2_relat_1(X1),X0) | ~v1_relat_1(X1)) )),
% 3.99/1.00    inference(cnf_transformation,[],[f29])).
% 3.99/1.00  
% 3.99/1.00  fof(f4,axiom,(
% 3.99/1.00    ! [X0,X1] : ((v5_relat_1(X1,X0) & v1_relat_1(X1)) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(X1)) => v5_relat_1(X2,X0)))),
% 3.99/1.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.99/1.00  
% 3.99/1.00  fof(f16,plain,(
% 3.99/1.00    ! [X0,X1] : (! [X2] : (v5_relat_1(X2,X0) | ~m1_subset_1(X2,k1_zfmisc_1(X1))) | (~v5_relat_1(X1,X0) | ~v1_relat_1(X1)))),
% 3.99/1.00    inference(ennf_transformation,[],[f4])).
% 3.99/1.00  
% 3.99/1.00  fof(f17,plain,(
% 3.99/1.00    ! [X0,X1] : (! [X2] : (v5_relat_1(X2,X0) | ~m1_subset_1(X2,k1_zfmisc_1(X1))) | ~v5_relat_1(X1,X0) | ~v1_relat_1(X1))),
% 3.99/1.00    inference(flattening,[],[f16])).
% 3.99/1.00  
% 3.99/1.00  fof(f38,plain,(
% 3.99/1.00    ( ! [X2,X0,X1] : (v5_relat_1(X2,X0) | ~m1_subset_1(X2,k1_zfmisc_1(X1)) | ~v5_relat_1(X1,X0) | ~v1_relat_1(X1)) )),
% 3.99/1.00    inference(cnf_transformation,[],[f17])).
% 3.99/1.00  
% 3.99/1.00  fof(f49,plain,(
% 3.99/1.00    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))),
% 3.99/1.00    inference(cnf_transformation,[],[f31])).
% 3.99/1.00  
% 3.99/1.00  fof(f9,axiom,(
% 3.99/1.00    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => v1_relat_1(X2))),
% 3.99/1.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.99/1.00  
% 3.99/1.00  fof(f20,plain,(
% 3.99/1.00    ! [X0,X1,X2] : (v1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 3.99/1.00    inference(ennf_transformation,[],[f9])).
% 3.99/1.00  
% 3.99/1.00  fof(f46,plain,(
% 3.99/1.00    ( ! [X2,X0,X1] : (v1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 3.99/1.00    inference(cnf_transformation,[],[f20])).
% 3.99/1.00  
% 3.99/1.00  fof(f8,axiom,(
% 3.99/1.00    ! [X0] : (k2_relat_1(k6_relat_1(X0)) = X0 & k1_relat_1(k6_relat_1(X0)) = X0)),
% 3.99/1.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.99/1.00  
% 3.99/1.00  fof(f45,plain,(
% 3.99/1.00    ( ! [X0] : (k2_relat_1(k6_relat_1(X0)) = X0) )),
% 3.99/1.00    inference(cnf_transformation,[],[f8])).
% 3.99/1.00  
% 3.99/1.00  fof(f41,plain,(
% 3.99/1.00    ( ! [X0,X1] : (r1_tarski(k2_relat_1(X1),X0) | ~v5_relat_1(X1,X0) | ~v1_relat_1(X1)) )),
% 3.99/1.00    inference(cnf_transformation,[],[f29])).
% 3.99/1.00  
% 3.99/1.00  fof(f7,axiom,(
% 3.99/1.00    ! [X0] : v1_relat_1(k6_relat_1(X0))),
% 3.99/1.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.99/1.00  
% 3.99/1.00  fof(f43,plain,(
% 3.99/1.00    ( ! [X0] : (v1_relat_1(k6_relat_1(X0))) )),
% 3.99/1.00    inference(cnf_transformation,[],[f7])).
% 3.99/1.00  
% 3.99/1.00  fof(f39,plain,(
% 3.99/1.00    ( ! [X0,X1] : (r1_tarski(k1_relat_1(X1),X0) | ~v4_relat_1(X1,X0) | ~v1_relat_1(X1)) )),
% 3.99/1.00    inference(cnf_transformation,[],[f28])).
% 3.99/1.00  
% 3.99/1.00  fof(f11,axiom,(
% 3.99/1.00    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k2_relat_1(X2) = k2_relset_1(X0,X1,X2))),
% 3.99/1.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.99/1.00  
% 3.99/1.00  fof(f22,plain,(
% 3.99/1.00    ! [X0,X1,X2] : (k2_relat_1(X2) = k2_relset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 3.99/1.00    inference(ennf_transformation,[],[f11])).
% 3.99/1.00  
% 3.99/1.00  fof(f48,plain,(
% 3.99/1.00    ( ! [X2,X0,X1] : (k2_relat_1(X2) = k2_relset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 3.99/1.00    inference(cnf_transformation,[],[f22])).
% 3.99/1.00  
% 3.99/1.00  fof(f51,plain,(
% 3.99/1.00    ~r1_tarski(sK2,k2_relset_1(sK0,sK1,sK3)) | ~r1_tarski(sK2,k1_relset_1(sK0,sK1,sK3))),
% 3.99/1.00    inference(cnf_transformation,[],[f31])).
% 3.99/1.00  
% 3.99/1.00  fof(f44,plain,(
% 3.99/1.00    ( ! [X0] : (k1_relat_1(k6_relat_1(X0)) = X0) )),
% 3.99/1.00    inference(cnf_transformation,[],[f8])).
% 3.99/1.00  
% 3.99/1.00  fof(f10,axiom,(
% 3.99/1.00    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k1_relat_1(X2) = k1_relset_1(X0,X1,X2))),
% 3.99/1.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.99/1.00  
% 3.99/1.00  fof(f21,plain,(
% 3.99/1.00    ! [X0,X1,X2] : (k1_relat_1(X2) = k1_relset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 3.99/1.00    inference(ennf_transformation,[],[f10])).
% 3.99/1.00  
% 3.99/1.00  fof(f47,plain,(
% 3.99/1.00    ( ! [X2,X0,X1] : (k1_relat_1(X2) = k1_relset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 3.99/1.00    inference(cnf_transformation,[],[f21])).
% 3.99/1.00  
% 3.99/1.00  fof(f32,plain,(
% 3.99/1.00    ( ! [X0,X1] : (r1_tarski(X0,X1) | X0 != X1) )),
% 3.99/1.00    inference(cnf_transformation,[],[f26])).
% 3.99/1.00  
% 3.99/1.00  fof(f53,plain,(
% 3.99/1.00    ( ! [X1] : (r1_tarski(X1,X1)) )),
% 3.99/1.00    inference(equality_resolution,[],[f32])).
% 3.99/1.00  
% 3.99/1.00  cnf(c_18,negated_conjecture,
% 3.99/1.00      ( r1_tarski(k6_relat_1(sK2),sK3) ),
% 3.99/1.00      inference(cnf_transformation,[],[f50]) ).
% 3.99/1.00  
% 3.99/1.00  cnf(c_737,plain,
% 3.99/1.00      ( r1_tarski(k6_relat_1(sK2),sK3) = iProver_top ),
% 3.99/1.00      inference(predicate_to_equality,[status(thm)],[c_18]) ).
% 3.99/1.00  
% 3.99/1.00  cnf(c_1,plain,
% 3.99/1.00      ( r1_tarski(X0,X0) ),
% 3.99/1.00      inference(cnf_transformation,[],[f52]) ).
% 3.99/1.00  
% 3.99/1.00  cnf(c_751,plain,
% 3.99/1.00      ( r1_tarski(X0,X0) = iProver_top ),
% 3.99/1.00      inference(predicate_to_equality,[status(thm)],[c_1]) ).
% 3.99/1.00  
% 3.99/1.00  cnf(c_7,plain,
% 3.99/1.00      ( v4_relat_1(X0,X1)
% 3.99/1.00      | ~ r1_tarski(k1_relat_1(X0),X1)
% 3.99/1.00      | ~ v1_relat_1(X0) ),
% 3.99/1.00      inference(cnf_transformation,[],[f40]) ).
% 3.99/1.00  
% 3.99/1.00  cnf(c_746,plain,
% 3.99/1.00      ( v4_relat_1(X0,X1) = iProver_top
% 3.99/1.00      | r1_tarski(k1_relat_1(X0),X1) != iProver_top
% 3.99/1.00      | v1_relat_1(X0) != iProver_top ),
% 3.99/1.00      inference(predicate_to_equality,[status(thm)],[c_7]) ).
% 3.99/1.00  
% 3.99/1.00  cnf(c_1726,plain,
% 3.99/1.00      ( v4_relat_1(X0,k1_relat_1(X0)) = iProver_top
% 3.99/1.00      | v1_relat_1(X0) != iProver_top ),
% 3.99/1.00      inference(superposition,[status(thm)],[c_751,c_746]) ).
% 3.99/1.00  
% 3.99/1.00  cnf(c_3,plain,
% 3.99/1.00      ( m1_subset_1(X0,k1_zfmisc_1(X1)) | ~ r1_tarski(X0,X1) ),
% 3.99/1.00      inference(cnf_transformation,[],[f36]) ).
% 3.99/1.00  
% 3.99/1.00  cnf(c_750,plain,
% 3.99/1.00      ( m1_subset_1(X0,k1_zfmisc_1(X1)) = iProver_top
% 3.99/1.00      | r1_tarski(X0,X1) != iProver_top ),
% 3.99/1.00      inference(predicate_to_equality,[status(thm)],[c_3]) ).
% 3.99/1.00  
% 3.99/1.00  cnf(c_5,plain,
% 3.99/1.00      ( ~ v4_relat_1(X0,X1)
% 3.99/1.00      | v4_relat_1(X2,X1)
% 3.99/1.00      | ~ m1_subset_1(X2,k1_zfmisc_1(X0))
% 3.99/1.00      | ~ v1_relat_1(X0) ),
% 3.99/1.00      inference(cnf_transformation,[],[f37]) ).
% 3.99/1.00  
% 3.99/1.00  cnf(c_748,plain,
% 3.99/1.00      ( v4_relat_1(X0,X1) != iProver_top
% 3.99/1.00      | v4_relat_1(X2,X1) = iProver_top
% 3.99/1.00      | m1_subset_1(X2,k1_zfmisc_1(X0)) != iProver_top
% 3.99/1.00      | v1_relat_1(X0) != iProver_top ),
% 3.99/1.00      inference(predicate_to_equality,[status(thm)],[c_5]) ).
% 3.99/1.00  
% 3.99/1.00  cnf(c_2122,plain,
% 3.99/1.00      ( v4_relat_1(X0,X1) != iProver_top
% 3.99/1.00      | v4_relat_1(X2,X1) = iProver_top
% 3.99/1.00      | r1_tarski(X2,X0) != iProver_top
% 3.99/1.00      | v1_relat_1(X0) != iProver_top ),
% 3.99/1.00      inference(superposition,[status(thm)],[c_750,c_748]) ).
% 3.99/1.00  
% 3.99/1.00  cnf(c_5576,plain,
% 3.99/1.00      ( v4_relat_1(X0,k1_relat_1(X1)) = iProver_top
% 3.99/1.00      | r1_tarski(X0,X1) != iProver_top
% 3.99/1.00      | v1_relat_1(X1) != iProver_top ),
% 3.99/1.00      inference(superposition,[status(thm)],[c_1726,c_2122]) ).
% 3.99/1.00  
% 3.99/1.00  cnf(c_7772,plain,
% 3.99/1.00      ( v4_relat_1(X0,k1_relat_1(X1)) = iProver_top
% 3.99/1.00      | r1_tarski(X2,X1) != iProver_top
% 3.99/1.00      | r1_tarski(X0,X2) != iProver_top
% 3.99/1.00      | v1_relat_1(X2) != iProver_top
% 3.99/1.00      | v1_relat_1(X1) != iProver_top ),
% 3.99/1.00      inference(superposition,[status(thm)],[c_5576,c_2122]) ).
% 3.99/1.00  
% 3.99/1.00  cnf(c_15460,plain,
% 3.99/1.00      ( v4_relat_1(k6_relat_1(sK2),k1_relat_1(X0)) = iProver_top
% 3.99/1.00      | r1_tarski(sK3,X0) != iProver_top
% 3.99/1.00      | v1_relat_1(X0) != iProver_top
% 3.99/1.00      | v1_relat_1(sK3) != iProver_top ),
% 3.99/1.00      inference(superposition,[status(thm)],[c_737,c_7772]) ).
% 3.99/1.00  
% 3.99/1.00  cnf(c_15514,plain,
% 3.99/1.00      ( v4_relat_1(k6_relat_1(sK2),k1_relat_1(sK3)) = iProver_top
% 3.99/1.00      | r1_tarski(sK3,sK3) != iProver_top
% 3.99/1.00      | v1_relat_1(sK3) != iProver_top ),
% 3.99/1.00      inference(instantiation,[status(thm)],[c_15460]) ).
% 3.99/1.00  
% 3.99/1.00  cnf(c_9,plain,
% 3.99/1.00      ( v5_relat_1(X0,X1)
% 3.99/1.00      | ~ r1_tarski(k2_relat_1(X0),X1)
% 3.99/1.00      | ~ v1_relat_1(X0) ),
% 3.99/1.00      inference(cnf_transformation,[],[f42]) ).
% 3.99/1.00  
% 3.99/1.00  cnf(c_744,plain,
% 3.99/1.00      ( v5_relat_1(X0,X1) = iProver_top
% 3.99/1.00      | r1_tarski(k2_relat_1(X0),X1) != iProver_top
% 3.99/1.00      | v1_relat_1(X0) != iProver_top ),
% 3.99/1.00      inference(predicate_to_equality,[status(thm)],[c_9]) ).
% 3.99/1.00  
% 3.99/1.00  cnf(c_1577,plain,
% 3.99/1.00      ( v5_relat_1(X0,k2_relat_1(X0)) = iProver_top
% 3.99/1.00      | v1_relat_1(X0) != iProver_top ),
% 3.99/1.00      inference(superposition,[status(thm)],[c_751,c_744]) ).
% 3.99/1.00  
% 3.99/1.00  cnf(c_6,plain,
% 3.99/1.00      ( ~ v5_relat_1(X0,X1)
% 3.99/1.00      | v5_relat_1(X2,X1)
% 3.99/1.00      | ~ m1_subset_1(X2,k1_zfmisc_1(X0))
% 3.99/1.00      | ~ v1_relat_1(X0) ),
% 3.99/1.00      inference(cnf_transformation,[],[f38]) ).
% 3.99/1.00  
% 3.99/1.00  cnf(c_747,plain,
% 3.99/1.00      ( v5_relat_1(X0,X1) != iProver_top
% 3.99/1.00      | v5_relat_1(X2,X1) = iProver_top
% 3.99/1.00      | m1_subset_1(X2,k1_zfmisc_1(X0)) != iProver_top
% 3.99/1.00      | v1_relat_1(X0) != iProver_top ),
% 3.99/1.00      inference(predicate_to_equality,[status(thm)],[c_6]) ).
% 3.99/1.00  
% 3.99/1.00  cnf(c_1985,plain,
% 3.99/1.00      ( v5_relat_1(X0,X1) != iProver_top
% 3.99/1.00      | v5_relat_1(X2,X1) = iProver_top
% 3.99/1.00      | r1_tarski(X2,X0) != iProver_top
% 3.99/1.00      | v1_relat_1(X0) != iProver_top ),
% 3.99/1.00      inference(superposition,[status(thm)],[c_750,c_747]) ).
% 3.99/1.00  
% 3.99/1.00  cnf(c_4964,plain,
% 3.99/1.00      ( v5_relat_1(X0,k2_relat_1(X1)) = iProver_top
% 3.99/1.00      | r1_tarski(X0,X1) != iProver_top
% 3.99/1.00      | v1_relat_1(X1) != iProver_top ),
% 3.99/1.00      inference(superposition,[status(thm)],[c_1577,c_1985]) ).
% 3.99/1.00  
% 3.99/1.00  cnf(c_7677,plain,
% 3.99/1.00      ( v5_relat_1(X0,k2_relat_1(X1)) = iProver_top
% 3.99/1.00      | r1_tarski(X2,X1) != iProver_top
% 3.99/1.00      | r1_tarski(X0,X2) != iProver_top
% 3.99/1.00      | v1_relat_1(X2) != iProver_top
% 3.99/1.00      | v1_relat_1(X1) != iProver_top ),
% 3.99/1.00      inference(superposition,[status(thm)],[c_4964,c_1985]) ).
% 3.99/1.00  
% 3.99/1.00  cnf(c_10685,plain,
% 3.99/1.00      ( v5_relat_1(k6_relat_1(sK2),k2_relat_1(X0)) = iProver_top
% 3.99/1.00      | r1_tarski(sK3,X0) != iProver_top
% 3.99/1.00      | v1_relat_1(X0) != iProver_top
% 3.99/1.00      | v1_relat_1(sK3) != iProver_top ),
% 3.99/1.00      inference(superposition,[status(thm)],[c_737,c_7677]) ).
% 3.99/1.00  
% 3.99/1.00  cnf(c_19,negated_conjecture,
% 3.99/1.00      ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ),
% 3.99/1.00      inference(cnf_transformation,[],[f49]) ).
% 3.99/1.00  
% 3.99/1.00  cnf(c_20,plain,
% 3.99/1.00      ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) = iProver_top ),
% 3.99/1.00      inference(predicate_to_equality,[status(thm)],[c_19]) ).
% 3.99/1.00  
% 3.99/1.00  cnf(c_14,plain,
% 3.99/1.00      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.99/1.00      | v1_relat_1(X0) ),
% 3.99/1.00      inference(cnf_transformation,[],[f46]) ).
% 3.99/1.00  
% 3.99/1.00  cnf(c_894,plain,
% 3.99/1.00      ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
% 3.99/1.00      | v1_relat_1(sK3) ),
% 3.99/1.00      inference(instantiation,[status(thm)],[c_14]) ).
% 3.99/1.00  
% 3.99/1.00  cnf(c_895,plain,
% 3.99/1.00      ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) != iProver_top
% 3.99/1.00      | v1_relat_1(sK3) = iProver_top ),
% 3.99/1.00      inference(predicate_to_equality,[status(thm)],[c_894]) ).
% 3.99/1.00  
% 3.99/1.00  cnf(c_10881,plain,
% 3.99/1.00      ( v1_relat_1(X0) != iProver_top
% 3.99/1.00      | r1_tarski(sK3,X0) != iProver_top
% 3.99/1.00      | v5_relat_1(k6_relat_1(sK2),k2_relat_1(X0)) = iProver_top ),
% 3.99/1.00      inference(global_propositional_subsumption,
% 3.99/1.00                [status(thm)],
% 3.99/1.00                [c_10685,c_20,c_895]) ).
% 3.99/1.00  
% 3.99/1.00  cnf(c_10882,plain,
% 3.99/1.00      ( v5_relat_1(k6_relat_1(sK2),k2_relat_1(X0)) = iProver_top
% 3.99/1.00      | r1_tarski(sK3,X0) != iProver_top
% 3.99/1.00      | v1_relat_1(X0) != iProver_top ),
% 3.99/1.00      inference(renaming,[status(thm)],[c_10881]) ).
% 3.99/1.00  
% 3.99/1.00  cnf(c_12,plain,
% 3.99/1.00      ( k2_relat_1(k6_relat_1(X0)) = X0 ),
% 3.99/1.00      inference(cnf_transformation,[],[f45]) ).
% 3.99/1.00  
% 3.99/1.00  cnf(c_10,plain,
% 3.99/1.00      ( ~ v5_relat_1(X0,X1)
% 3.99/1.00      | r1_tarski(k2_relat_1(X0),X1)
% 3.99/1.00      | ~ v1_relat_1(X0) ),
% 3.99/1.00      inference(cnf_transformation,[],[f41]) ).
% 3.99/1.00  
% 3.99/1.00  cnf(c_743,plain,
% 3.99/1.00      ( v5_relat_1(X0,X1) != iProver_top
% 3.99/1.00      | r1_tarski(k2_relat_1(X0),X1) = iProver_top
% 3.99/1.00      | v1_relat_1(X0) != iProver_top ),
% 3.99/1.00      inference(predicate_to_equality,[status(thm)],[c_10]) ).
% 3.99/1.00  
% 3.99/1.00  cnf(c_1467,plain,
% 3.99/1.00      ( v5_relat_1(k6_relat_1(X0),X1) != iProver_top
% 3.99/1.00      | r1_tarski(X0,X1) = iProver_top
% 3.99/1.00      | v1_relat_1(k6_relat_1(X0)) != iProver_top ),
% 3.99/1.00      inference(superposition,[status(thm)],[c_12,c_743]) ).
% 3.99/1.00  
% 3.99/1.00  cnf(c_11,plain,
% 3.99/1.00      ( v1_relat_1(k6_relat_1(X0)) ),
% 3.99/1.00      inference(cnf_transformation,[],[f43]) ).
% 3.99/1.00  
% 3.99/1.00  cnf(c_34,plain,
% 3.99/1.00      ( v1_relat_1(k6_relat_1(X0)) = iProver_top ),
% 3.99/1.00      inference(predicate_to_equality,[status(thm)],[c_11]) ).
% 3.99/1.00  
% 3.99/1.00  cnf(c_1744,plain,
% 3.99/1.00      ( r1_tarski(X0,X1) = iProver_top
% 3.99/1.00      | v5_relat_1(k6_relat_1(X0),X1) != iProver_top ),
% 3.99/1.00      inference(global_propositional_subsumption,
% 3.99/1.00                [status(thm)],
% 3.99/1.00                [c_1467,c_34]) ).
% 3.99/1.00  
% 3.99/1.00  cnf(c_1745,plain,
% 3.99/1.00      ( v5_relat_1(k6_relat_1(X0),X1) != iProver_top
% 3.99/1.00      | r1_tarski(X0,X1) = iProver_top ),
% 3.99/1.00      inference(renaming,[status(thm)],[c_1744]) ).
% 3.99/1.00  
% 3.99/1.00  cnf(c_10893,plain,
% 3.99/1.00      ( r1_tarski(sK3,X0) != iProver_top
% 3.99/1.00      | r1_tarski(sK2,k2_relat_1(X0)) = iProver_top
% 3.99/1.00      | v1_relat_1(X0) != iProver_top ),
% 3.99/1.00      inference(superposition,[status(thm)],[c_10882,c_1745]) ).
% 3.99/1.00  
% 3.99/1.00  cnf(c_10970,plain,
% 3.99/1.00      ( r1_tarski(sK3,sK3) != iProver_top
% 3.99/1.00      | r1_tarski(sK2,k2_relat_1(sK3)) = iProver_top
% 3.99/1.00      | v1_relat_1(sK3) != iProver_top ),
% 3.99/1.00      inference(instantiation,[status(thm)],[c_10893]) ).
% 3.99/1.00  
% 3.99/1.00  cnf(c_5508,plain,
% 3.99/1.00      ( v1_relat_1(k6_relat_1(sK2)) ),
% 3.99/1.00      inference(instantiation,[status(thm)],[c_11]) ).
% 3.99/1.00  
% 3.99/1.00  cnf(c_5509,plain,
% 3.99/1.00      ( v1_relat_1(k6_relat_1(sK2)) = iProver_top ),
% 3.99/1.00      inference(predicate_to_equality,[status(thm)],[c_5508]) ).
% 3.99/1.00  
% 3.99/1.00  cnf(c_8,plain,
% 3.99/1.00      ( ~ v4_relat_1(X0,X1)
% 3.99/1.00      | r1_tarski(k1_relat_1(X0),X1)
% 3.99/1.00      | ~ v1_relat_1(X0) ),
% 3.99/1.00      inference(cnf_transformation,[],[f39]) ).
% 3.99/1.00  
% 3.99/1.00  cnf(c_1647,plain,
% 3.99/1.00      ( ~ v4_relat_1(k6_relat_1(X0),X1)
% 3.99/1.00      | r1_tarski(k1_relat_1(k6_relat_1(X0)),X1)
% 3.99/1.00      | ~ v1_relat_1(k6_relat_1(X0)) ),
% 3.99/1.00      inference(instantiation,[status(thm)],[c_8]) ).
% 3.99/1.00  
% 3.99/1.00  cnf(c_2924,plain,
% 3.99/1.00      ( ~ v4_relat_1(k6_relat_1(sK2),k1_relat_1(sK3))
% 3.99/1.00      | r1_tarski(k1_relat_1(k6_relat_1(sK2)),k1_relat_1(sK3))
% 3.99/1.00      | ~ v1_relat_1(k6_relat_1(sK2)) ),
% 3.99/1.00      inference(instantiation,[status(thm)],[c_1647]) ).
% 3.99/1.00  
% 3.99/1.00  cnf(c_2925,plain,
% 3.99/1.00      ( v4_relat_1(k6_relat_1(sK2),k1_relat_1(sK3)) != iProver_top
% 3.99/1.00      | r1_tarski(k1_relat_1(k6_relat_1(sK2)),k1_relat_1(sK3)) = iProver_top
% 3.99/1.00      | v1_relat_1(k6_relat_1(sK2)) != iProver_top ),
% 3.99/1.00      inference(predicate_to_equality,[status(thm)],[c_2924]) ).
% 3.99/1.00  
% 3.99/1.00  cnf(c_332,plain,
% 3.99/1.00      ( ~ r1_tarski(X0,X1) | r1_tarski(X2,X3) | X2 != X0 | X3 != X1 ),
% 3.99/1.00      theory(equality) ).
% 3.99/1.00  
% 3.99/1.00  cnf(c_944,plain,
% 3.99/1.00      ( ~ r1_tarski(X0,X1)
% 3.99/1.00      | r1_tarski(sK2,k1_relset_1(sK0,sK1,sK3))
% 3.99/1.00      | k1_relset_1(sK0,sK1,sK3) != X1
% 3.99/1.00      | sK2 != X0 ),
% 3.99/1.00      inference(instantiation,[status(thm)],[c_332]) ).
% 3.99/1.00  
% 3.99/1.00  cnf(c_1804,plain,
% 3.99/1.00      ( ~ r1_tarski(k1_relat_1(k6_relat_1(sK2)),X0)
% 3.99/1.00      | r1_tarski(sK2,k1_relset_1(sK0,sK1,sK3))
% 3.99/1.00      | k1_relset_1(sK0,sK1,sK3) != X0
% 3.99/1.00      | sK2 != k1_relat_1(k6_relat_1(sK2)) ),
% 3.99/1.00      inference(instantiation,[status(thm)],[c_944]) ).
% 3.99/1.00  
% 3.99/1.00  cnf(c_2677,plain,
% 3.99/1.00      ( ~ r1_tarski(k1_relat_1(k6_relat_1(sK2)),k1_relat_1(sK3))
% 3.99/1.00      | r1_tarski(sK2,k1_relset_1(sK0,sK1,sK3))
% 3.99/1.00      | k1_relset_1(sK0,sK1,sK3) != k1_relat_1(sK3)
% 3.99/1.00      | sK2 != k1_relat_1(k6_relat_1(sK2)) ),
% 3.99/1.00      inference(instantiation,[status(thm)],[c_1804]) ).
% 3.99/1.00  
% 3.99/1.00  cnf(c_2678,plain,
% 3.99/1.00      ( k1_relset_1(sK0,sK1,sK3) != k1_relat_1(sK3)
% 3.99/1.00      | sK2 != k1_relat_1(k6_relat_1(sK2))
% 3.99/1.00      | r1_tarski(k1_relat_1(k6_relat_1(sK2)),k1_relat_1(sK3)) != iProver_top
% 3.99/1.00      | r1_tarski(sK2,k1_relset_1(sK0,sK1,sK3)) = iProver_top ),
% 3.99/1.00      inference(predicate_to_equality,[status(thm)],[c_2677]) ).
% 3.99/1.00  
% 3.99/1.00  cnf(c_736,plain,
% 3.99/1.00      ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) = iProver_top ),
% 3.99/1.00      inference(predicate_to_equality,[status(thm)],[c_19]) ).
% 3.99/1.00  
% 3.99/1.00  cnf(c_16,plain,
% 3.99/1.00      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.99/1.00      | k2_relset_1(X1,X2,X0) = k2_relat_1(X0) ),
% 3.99/1.00      inference(cnf_transformation,[],[f48]) ).
% 3.99/1.00  
% 3.99/1.00  cnf(c_739,plain,
% 3.99/1.00      ( k2_relset_1(X0,X1,X2) = k2_relat_1(X2)
% 3.99/1.00      | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
% 3.99/1.00      inference(predicate_to_equality,[status(thm)],[c_16]) ).
% 3.99/1.00  
% 3.99/1.00  cnf(c_1214,plain,
% 3.99/1.00      ( k2_relset_1(sK0,sK1,sK3) = k2_relat_1(sK3) ),
% 3.99/1.00      inference(superposition,[status(thm)],[c_736,c_739]) ).
% 3.99/1.00  
% 3.99/1.00  cnf(c_17,negated_conjecture,
% 3.99/1.00      ( ~ r1_tarski(sK2,k2_relset_1(sK0,sK1,sK3))
% 3.99/1.00      | ~ r1_tarski(sK2,k1_relset_1(sK0,sK1,sK3)) ),
% 3.99/1.00      inference(cnf_transformation,[],[f51]) ).
% 3.99/1.00  
% 3.99/1.00  cnf(c_738,plain,
% 3.99/1.00      ( r1_tarski(sK2,k2_relset_1(sK0,sK1,sK3)) != iProver_top
% 3.99/1.00      | r1_tarski(sK2,k1_relset_1(sK0,sK1,sK3)) != iProver_top ),
% 3.99/1.00      inference(predicate_to_equality,[status(thm)],[c_17]) ).
% 3.99/1.00  
% 3.99/1.00  cnf(c_2395,plain,
% 3.99/1.00      ( r1_tarski(sK2,k1_relset_1(sK0,sK1,sK3)) != iProver_top
% 3.99/1.00      | r1_tarski(sK2,k2_relat_1(sK3)) != iProver_top ),
% 3.99/1.00      inference(demodulation,[status(thm)],[c_1214,c_738]) ).
% 3.99/1.00  
% 3.99/1.00  cnf(c_13,plain,
% 3.99/1.00      ( k1_relat_1(k6_relat_1(X0)) = X0 ),
% 3.99/1.00      inference(cnf_transformation,[],[f44]) ).
% 3.99/1.00  
% 3.99/1.00  cnf(c_1561,plain,
% 3.99/1.00      ( k1_relat_1(k6_relat_1(sK2)) = sK2 ),
% 3.99/1.00      inference(instantiation,[status(thm)],[c_13]) ).
% 3.99/1.00  
% 3.99/1.00  cnf(c_331,plain,( X0 != X1 | X2 != X1 | X2 = X0 ),theory(equality) ).
% 3.99/1.00  
% 3.99/1.00  cnf(c_1003,plain,
% 3.99/1.00      ( X0 != X1 | sK2 != X1 | sK2 = X0 ),
% 3.99/1.00      inference(instantiation,[status(thm)],[c_331]) ).
% 3.99/1.00  
% 3.99/1.00  cnf(c_1184,plain,
% 3.99/1.00      ( X0 != sK2 | sK2 = X0 | sK2 != sK2 ),
% 3.99/1.00      inference(instantiation,[status(thm)],[c_1003]) ).
% 3.99/1.00  
% 3.99/1.00  cnf(c_1560,plain,
% 3.99/1.00      ( k1_relat_1(k6_relat_1(sK2)) != sK2
% 3.99/1.00      | sK2 = k1_relat_1(k6_relat_1(sK2))
% 3.99/1.00      | sK2 != sK2 ),
% 3.99/1.00      inference(instantiation,[status(thm)],[c_1184]) ).
% 3.99/1.00  
% 3.99/1.00  cnf(c_330,plain,( X0 = X0 ),theory(equality) ).
% 3.99/1.00  
% 3.99/1.00  cnf(c_998,plain,
% 3.99/1.00      ( sK2 = sK2 ),
% 3.99/1.00      inference(instantiation,[status(thm)],[c_330]) ).
% 3.99/1.00  
% 3.99/1.00  cnf(c_15,plain,
% 3.99/1.00      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.99/1.00      | k1_relset_1(X1,X2,X0) = k1_relat_1(X0) ),
% 3.99/1.00      inference(cnf_transformation,[],[f47]) ).
% 3.99/1.00  
% 3.99/1.00  cnf(c_923,plain,
% 3.99/1.00      ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
% 3.99/1.00      | k1_relset_1(sK0,sK1,sK3) = k1_relat_1(sK3) ),
% 3.99/1.00      inference(instantiation,[status(thm)],[c_15]) ).
% 3.99/1.00  
% 3.99/1.00  cnf(c_2,plain,
% 3.99/1.00      ( r1_tarski(X0,X0) ),
% 3.99/1.00      inference(cnf_transformation,[],[f53]) ).
% 3.99/1.00  
% 3.99/1.00  cnf(c_57,plain,
% 3.99/1.00      ( r1_tarski(X0,X0) = iProver_top ),
% 3.99/1.00      inference(predicate_to_equality,[status(thm)],[c_2]) ).
% 3.99/1.00  
% 3.99/1.00  cnf(c_59,plain,
% 3.99/1.00      ( r1_tarski(sK3,sK3) = iProver_top ),
% 3.99/1.00      inference(instantiation,[status(thm)],[c_57]) ).
% 3.99/1.00  
% 3.99/1.00  cnf(contradiction,plain,
% 3.99/1.00      ( $false ),
% 3.99/1.00      inference(minisat,
% 3.99/1.00                [status(thm)],
% 3.99/1.00                [c_15514,c_10970,c_5509,c_2925,c_2678,c_2395,c_1561,
% 3.99/1.00                 c_1560,c_998,c_923,c_895,c_59,c_20,c_19]) ).
% 3.99/1.00  
% 3.99/1.00  
% 3.99/1.00  % SZS output end CNFRefutation for theBenchmark.p
% 3.99/1.00  
% 3.99/1.00  ------                               Statistics
% 3.99/1.00  
% 3.99/1.00  ------ Selected
% 3.99/1.00  
% 3.99/1.00  total_time:                             0.352
% 3.99/1.00  
%------------------------------------------------------------------------------
