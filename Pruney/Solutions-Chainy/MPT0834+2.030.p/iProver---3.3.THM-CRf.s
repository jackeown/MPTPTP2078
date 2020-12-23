%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n024.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 11:56:05 EST 2020

% Result     : Theorem 2.21s
% Output     : CNFRefutation 2.21s
% Verified   : 
% Statistics : Number of formulae       :  128 ( 402 expanded)
%              Number of clauses        :   75 ( 184 expanded)
%              Number of leaves         :   17 (  80 expanded)
%              Depth                    :   18
%              Number of atoms          :  301 (1024 expanded)
%              Number of equality atoms :  154 ( 475 expanded)
%              Maximal formula depth    :    8 (   4 average)
%              Maximal clause size      :    6 (   2 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f10,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => ( v5_relat_1(X2,X1)
        & v4_relat_1(X2,X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f26,plain,(
    ! [X0,X1,X2] :
      ( ( v5_relat_1(X2,X1)
        & v4_relat_1(X2,X0) )
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f50,plain,(
    ! [X2,X0,X1] :
      ( v5_relat_1(X2,X1)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ( v5_relat_1(X1,X0)
      <=> r1_tarski(k2_relat_1(X1),X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f18,plain,(
    ! [X0,X1] :
      ( ( v5_relat_1(X1,X0)
      <=> r1_tarski(k2_relat_1(X1),X0) )
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f34,plain,(
    ! [X0,X1] :
      ( ( ( v5_relat_1(X1,X0)
          | ~ r1_tarski(k2_relat_1(X1),X0) )
        & ( r1_tarski(k2_relat_1(X1),X0)
          | ~ v5_relat_1(X1,X0) ) )
      | ~ v1_relat_1(X1) ) ),
    inference(nnf_transformation,[],[f18])).

fof(f41,plain,(
    ! [X0,X1] :
      ( r1_tarski(k2_relat_1(X1),X0)
      | ~ v5_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f34])).

fof(f15,conjecture,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => ( k1_relset_1(X0,X1,X2) = k8_relset_1(X0,X1,X2,X1)
        & k2_relset_1(X0,X1,X2) = k7_relset_1(X0,X1,X2,X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f16,negated_conjecture,(
    ~ ! [X0,X1,X2] :
        ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
       => ( k1_relset_1(X0,X1,X2) = k8_relset_1(X0,X1,X2,X1)
          & k2_relset_1(X0,X1,X2) = k7_relset_1(X0,X1,X2,X0) ) ) ),
    inference(negated_conjecture,[],[f15])).

fof(f31,plain,(
    ? [X0,X1,X2] :
      ( ( k1_relset_1(X0,X1,X2) != k8_relset_1(X0,X1,X2,X1)
        | k2_relset_1(X0,X1,X2) != k7_relset_1(X0,X1,X2,X0) )
      & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f16])).

fof(f35,plain,
    ( ? [X0,X1,X2] :
        ( ( k1_relset_1(X0,X1,X2) != k8_relset_1(X0,X1,X2,X1)
          | k2_relset_1(X0,X1,X2) != k7_relset_1(X0,X1,X2,X0) )
        & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) )
   => ( ( k1_relset_1(sK0,sK1,sK2) != k8_relset_1(sK0,sK1,sK2,sK1)
        | k2_relset_1(sK0,sK1,sK2) != k7_relset_1(sK0,sK1,sK2,sK0) )
      & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ) ),
    introduced(choice_axiom,[])).

fof(f36,plain,
    ( ( k1_relset_1(sK0,sK1,sK2) != k8_relset_1(sK0,sK1,sK2,sK1)
      | k2_relset_1(sK0,sK1,sK2) != k7_relset_1(sK0,sK1,sK2,sK0) )
    & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f31,f35])).

fof(f55,plain,(
    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ),
    inference(cnf_transformation,[],[f36])).

fof(f2,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(X0))
         => v1_relat_1(X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f17,plain,(
    ! [X0] :
      ( ! [X1] :
          ( v1_relat_1(X1)
          | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f40,plain,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f4,axiom,(
    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f43,plain,(
    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1)) ),
    inference(cnf_transformation,[],[f4])).

fof(f6,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => k10_relat_1(X0,k2_relat_1(X0)) = k1_relat_1(X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f20,plain,(
    ! [X0] :
      ( k10_relat_1(X0,k2_relat_1(X0)) = k1_relat_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f45,plain,(
    ! [X0] :
      ( k10_relat_1(X0,k2_relat_1(X0)) = k1_relat_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f8,axiom,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
     => ( r1_tarski(X0,X1)
       => r1_tarski(k10_relat_1(X2,X0),k10_relat_1(X2,X1)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f22,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(k10_relat_1(X2,X0),k10_relat_1(X2,X1))
      | ~ r1_tarski(X0,X1)
      | ~ v1_relat_1(X2) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f23,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(k10_relat_1(X2,X0),k10_relat_1(X2,X1))
      | ~ r1_tarski(X0,X1)
      | ~ v1_relat_1(X2) ) ),
    inference(flattening,[],[f22])).

fof(f47,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(k10_relat_1(X2,X0),k10_relat_1(X2,X1))
      | ~ r1_tarski(X0,X1)
      | ~ v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f7,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => r1_tarski(k10_relat_1(X1,X0),k10_relat_1(X1,k2_relat_1(X1))) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f21,plain,(
    ! [X0,X1] :
      ( r1_tarski(k10_relat_1(X1,X0),k10_relat_1(X1,k2_relat_1(X1)))
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f46,plain,(
    ! [X0,X1] :
      ( r1_tarski(k10_relat_1(X1,X0),k10_relat_1(X1,k2_relat_1(X1)))
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( X0 = X1
    <=> ( r1_tarski(X1,X0)
        & r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f32,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(nnf_transformation,[],[f1])).

fof(f33,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(flattening,[],[f32])).

fof(f39,plain,(
    ! [X0,X1] :
      ( X0 = X1
      | ~ r1_tarski(X1,X0)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f33])).

fof(f49,plain,(
    ! [X2,X0,X1] :
      ( v4_relat_1(X2,X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f9,axiom,(
    ! [X0,X1] :
      ( ( v4_relat_1(X1,X0)
        & v1_relat_1(X1) )
     => k7_relat_1(X1,X0) = X1 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f24,plain,(
    ! [X0,X1] :
      ( k7_relat_1(X1,X0) = X1
      | ~ v4_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f25,plain,(
    ! [X0,X1] :
      ( k7_relat_1(X1,X0) = X1
      | ~ v4_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f24])).

fof(f48,plain,(
    ! [X0,X1] :
      ( k7_relat_1(X1,X0) = X1
      | ~ v4_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f5,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => k2_relat_1(k7_relat_1(X1,X0)) = k9_relat_1(X1,X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f19,plain,(
    ! [X0,X1] :
      ( k2_relat_1(k7_relat_1(X1,X0)) = k9_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f44,plain,(
    ! [X0,X1] :
      ( k2_relat_1(k7_relat_1(X1,X0)) = k9_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f11,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k1_relat_1(X2) = k1_relset_1(X0,X1,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f27,plain,(
    ! [X0,X1,X2] :
      ( k1_relat_1(X2) = k1_relset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f51,plain,(
    ! [X2,X0,X1] :
      ( k1_relat_1(X2) = k1_relset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f12,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k2_relat_1(X2) = k2_relset_1(X0,X1,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f28,plain,(
    ! [X0,X1,X2] :
      ( k2_relat_1(X2) = k2_relset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f52,plain,(
    ! [X2,X0,X1] :
      ( k2_relat_1(X2) = k2_relset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f56,plain,
    ( k1_relset_1(sK0,sK1,sK2) != k8_relset_1(sK0,sK1,sK2,sK1)
    | k2_relset_1(sK0,sK1,sK2) != k7_relset_1(sK0,sK1,sK2,sK0) ),
    inference(cnf_transformation,[],[f36])).

fof(f14,axiom,(
    ! [X0,X1,X2,X3] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k10_relat_1(X2,X3) = k8_relset_1(X0,X1,X2,X3) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f30,plain,(
    ! [X0,X1,X2,X3] :
      ( k10_relat_1(X2,X3) = k8_relset_1(X0,X1,X2,X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f54,plain,(
    ! [X2,X0,X3,X1] :
      ( k10_relat_1(X2,X3) = k8_relset_1(X0,X1,X2,X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f13,axiom,(
    ! [X0,X1,X2,X3] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k9_relat_1(X2,X3) = k7_relset_1(X0,X1,X2,X3) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f29,plain,(
    ! [X0,X1,X2,X3] :
      ( k9_relat_1(X2,X3) = k7_relset_1(X0,X1,X2,X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f53,plain,(
    ! [X2,X0,X3,X1] :
      ( k9_relat_1(X2,X3) = k7_relset_1(X0,X1,X2,X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f29])).

cnf(c_12,plain,
    ( v5_relat_1(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) ),
    inference(cnf_transformation,[],[f50])).

cnf(c_5,plain,
    ( ~ v5_relat_1(X0,X1)
    | r1_tarski(k2_relat_1(X0),X1)
    | ~ v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f41])).

cnf(c_241,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | r1_tarski(k2_relat_1(X0),X2)
    | ~ v1_relat_1(X0) ),
    inference(resolution,[status(thm)],[c_12,c_5])).

cnf(c_19,negated_conjecture,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ),
    inference(cnf_transformation,[],[f55])).

cnf(c_275,plain,
    ( r1_tarski(k2_relat_1(X0),X1)
    | ~ v1_relat_1(X0)
    | k1_zfmisc_1(k2_zfmisc_1(X2,X1)) != k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))
    | sK2 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_241,c_19])).

cnf(c_276,plain,
    ( r1_tarski(k2_relat_1(sK2),X0)
    | ~ v1_relat_1(sK2)
    | k1_zfmisc_1(k2_zfmisc_1(X1,X0)) != k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)) ),
    inference(unflattening,[status(thm)],[c_275])).

cnf(c_644,plain,
    ( k1_zfmisc_1(k2_zfmisc_1(X0,X1)) != k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))
    | r1_tarski(k2_relat_1(sK2),X1) = iProver_top
    | v1_relat_1(sK2) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_276])).

cnf(c_277,plain,
    ( k1_zfmisc_1(k2_zfmisc_1(X0,X1)) != k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))
    | r1_tarski(k2_relat_1(sK2),X1) = iProver_top
    | v1_relat_1(sK2) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_276])).

cnf(c_441,plain,
    ( X0 = X0 ),
    theory(equality)).

cnf(c_746,plain,
    ( k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)) = k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)) ),
    inference(instantiation,[status(thm)],[c_441])).

cnf(c_3,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | ~ v1_relat_1(X1)
    | v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f40])).

cnf(c_260,plain,
    ( ~ v1_relat_1(X0)
    | v1_relat_1(X1)
    | k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)) != k1_zfmisc_1(X0)
    | sK2 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_3,c_19])).

cnf(c_261,plain,
    ( ~ v1_relat_1(X0)
    | v1_relat_1(sK2)
    | k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)) != k1_zfmisc_1(X0) ),
    inference(unflattening,[status(thm)],[c_260])).

cnf(c_741,plain,
    ( ~ v1_relat_1(k2_zfmisc_1(X0,X1))
    | v1_relat_1(sK2)
    | k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)) != k1_zfmisc_1(k2_zfmisc_1(X0,X1)) ),
    inference(instantiation,[status(thm)],[c_261])).

cnf(c_843,plain,
    ( ~ v1_relat_1(k2_zfmisc_1(sK0,sK1))
    | v1_relat_1(sK2)
    | k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)) != k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)) ),
    inference(instantiation,[status(thm)],[c_741])).

cnf(c_844,plain,
    ( k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)) != k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))
    | v1_relat_1(k2_zfmisc_1(sK0,sK1)) != iProver_top
    | v1_relat_1(sK2) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_843])).

cnf(c_6,plain,
    ( v1_relat_1(k2_zfmisc_1(X0,X1)) ),
    inference(cnf_transformation,[],[f43])).

cnf(c_949,plain,
    ( v1_relat_1(k2_zfmisc_1(sK0,sK1)) ),
    inference(instantiation,[status(thm)],[c_6])).

cnf(c_950,plain,
    ( v1_relat_1(k2_zfmisc_1(sK0,sK1)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_949])).

cnf(c_1262,plain,
    ( r1_tarski(k2_relat_1(sK2),X1) = iProver_top
    | k1_zfmisc_1(k2_zfmisc_1(X0,X1)) != k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_644,c_277,c_746,c_844,c_950])).

cnf(c_1263,plain,
    ( k1_zfmisc_1(k2_zfmisc_1(X0,X1)) != k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))
    | r1_tarski(k2_relat_1(sK2),X1) = iProver_top ),
    inference(renaming,[status(thm)],[c_1262])).

cnf(c_1270,plain,
    ( r1_tarski(k2_relat_1(sK2),sK1) = iProver_top ),
    inference(equality_resolution,[status(thm)],[c_1263])).

cnf(c_645,plain,
    ( k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)) != k1_zfmisc_1(X0)
    | v1_relat_1(X0) != iProver_top
    | v1_relat_1(sK2) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_261])).

cnf(c_1151,plain,
    ( v1_relat_1(sK2) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_645,c_746,c_844,c_950])).

cnf(c_8,plain,
    ( ~ v1_relat_1(X0)
    | k10_relat_1(X0,k2_relat_1(X0)) = k1_relat_1(X0) ),
    inference(cnf_transformation,[],[f45])).

cnf(c_648,plain,
    ( k10_relat_1(X0,k2_relat_1(X0)) = k1_relat_1(X0)
    | v1_relat_1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_8])).

cnf(c_1157,plain,
    ( k10_relat_1(sK2,k2_relat_1(sK2)) = k1_relat_1(sK2) ),
    inference(superposition,[status(thm)],[c_1151,c_648])).

cnf(c_10,plain,
    ( ~ r1_tarski(X0,X1)
    | r1_tarski(k10_relat_1(X2,X0),k10_relat_1(X2,X1))
    | ~ v1_relat_1(X2) ),
    inference(cnf_transformation,[],[f47])).

cnf(c_646,plain,
    ( r1_tarski(X0,X1) != iProver_top
    | r1_tarski(k10_relat_1(X2,X0),k10_relat_1(X2,X1)) = iProver_top
    | v1_relat_1(X2) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_10])).

cnf(c_1570,plain,
    ( r1_tarski(k1_relat_1(sK2),k10_relat_1(sK2,X0)) = iProver_top
    | r1_tarski(k2_relat_1(sK2),X0) != iProver_top
    | v1_relat_1(sK2) != iProver_top ),
    inference(superposition,[status(thm)],[c_1157,c_646])).

cnf(c_1821,plain,
    ( r1_tarski(k2_relat_1(sK2),X0) != iProver_top
    | r1_tarski(k1_relat_1(sK2),k10_relat_1(sK2,X0)) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_1570,c_746,c_844,c_950])).

cnf(c_1822,plain,
    ( r1_tarski(k1_relat_1(sK2),k10_relat_1(sK2,X0)) = iProver_top
    | r1_tarski(k2_relat_1(sK2),X0) != iProver_top ),
    inference(renaming,[status(thm)],[c_1821])).

cnf(c_9,plain,
    ( r1_tarski(k10_relat_1(X0,X1),k10_relat_1(X0,k2_relat_1(X0)))
    | ~ v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f46])).

cnf(c_647,plain,
    ( r1_tarski(k10_relat_1(X0,X1),k10_relat_1(X0,k2_relat_1(X0))) = iProver_top
    | v1_relat_1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_9])).

cnf(c_1452,plain,
    ( r1_tarski(k10_relat_1(sK2,X0),k1_relat_1(sK2)) = iProver_top
    | v1_relat_1(sK2) != iProver_top ),
    inference(superposition,[status(thm)],[c_1157,c_647])).

cnf(c_1729,plain,
    ( r1_tarski(k10_relat_1(sK2,X0),k1_relat_1(sK2)) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_1452,c_746,c_844,c_950])).

cnf(c_0,plain,
    ( ~ r1_tarski(X0,X1)
    | ~ r1_tarski(X1,X0)
    | X0 = X1 ),
    inference(cnf_transformation,[],[f39])).

cnf(c_652,plain,
    ( X0 = X1
    | r1_tarski(X0,X1) != iProver_top
    | r1_tarski(X1,X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_0])).

cnf(c_1737,plain,
    ( k10_relat_1(sK2,X0) = k1_relat_1(sK2)
    | r1_tarski(k1_relat_1(sK2),k10_relat_1(sK2,X0)) != iProver_top ),
    inference(superposition,[status(thm)],[c_1729,c_652])).

cnf(c_1949,plain,
    ( k10_relat_1(sK2,X0) = k1_relat_1(sK2)
    | r1_tarski(k2_relat_1(sK2),X0) != iProver_top ),
    inference(superposition,[status(thm)],[c_1822,c_1737])).

cnf(c_1962,plain,
    ( k10_relat_1(sK2,sK1) = k1_relat_1(sK2) ),
    inference(superposition,[status(thm)],[c_1270,c_1949])).

cnf(c_13,plain,
    ( v4_relat_1(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) ),
    inference(cnf_transformation,[],[f49])).

cnf(c_11,plain,
    ( ~ v4_relat_1(X0,X1)
    | ~ v1_relat_1(X0)
    | k7_relat_1(X0,X1) = X0 ),
    inference(cnf_transformation,[],[f48])).

cnf(c_223,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ v1_relat_1(X0)
    | k7_relat_1(X0,X1) = X0 ),
    inference(resolution,[status(thm)],[c_13,c_11])).

cnf(c_290,plain,
    ( ~ v1_relat_1(X0)
    | k7_relat_1(X0,X1) = X0
    | k1_zfmisc_1(k2_zfmisc_1(X1,X2)) != k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))
    | sK2 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_223,c_19])).

cnf(c_291,plain,
    ( ~ v1_relat_1(sK2)
    | k7_relat_1(sK2,X0) = sK2
    | k1_zfmisc_1(k2_zfmisc_1(X0,X1)) != k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)) ),
    inference(unflattening,[status(thm)],[c_290])).

cnf(c_643,plain,
    ( k7_relat_1(sK2,X0) = sK2
    | k1_zfmisc_1(k2_zfmisc_1(X0,X1)) != k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))
    | v1_relat_1(sK2) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_291])).

cnf(c_945,plain,
    ( k7_relat_1(sK2,sK0) = sK2
    | v1_relat_1(sK2) != iProver_top ),
    inference(equality_resolution,[status(thm)],[c_643])).

cnf(c_946,plain,
    ( ~ v1_relat_1(sK2)
    | k7_relat_1(sK2,sK0) = sK2 ),
    inference(predicate_to_equality_rev,[status(thm)],[c_945])).

cnf(c_1391,plain,
    ( k7_relat_1(sK2,sK0) = sK2 ),
    inference(global_propositional_subsumption,[status(thm)],[c_945,c_746,c_843,c_946,c_949])).

cnf(c_7,plain,
    ( ~ v1_relat_1(X0)
    | k2_relat_1(k7_relat_1(X0,X1)) = k9_relat_1(X0,X1) ),
    inference(cnf_transformation,[],[f44])).

cnf(c_649,plain,
    ( k2_relat_1(k7_relat_1(X0,X1)) = k9_relat_1(X0,X1)
    | v1_relat_1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_7])).

cnf(c_1156,plain,
    ( k2_relat_1(k7_relat_1(sK2,X0)) = k9_relat_1(sK2,X0) ),
    inference(superposition,[status(thm)],[c_1151,c_649])).

cnf(c_1394,plain,
    ( k9_relat_1(sK2,sK0) = k2_relat_1(sK2) ),
    inference(superposition,[status(thm)],[c_1391,c_1156])).

cnf(c_14,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k1_relset_1(X1,X2,X0) = k1_relat_1(X0) ),
    inference(cnf_transformation,[],[f51])).

cnf(c_332,plain,
    ( k1_relset_1(X0,X1,X2) = k1_relat_1(X2)
    | k1_zfmisc_1(k2_zfmisc_1(X0,X1)) != k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))
    | sK2 != X2 ),
    inference(resolution_lifted,[status(thm)],[c_14,c_19])).

cnf(c_333,plain,
    ( k1_relset_1(X0,X1,sK2) = k1_relat_1(sK2)
    | k1_zfmisc_1(k2_zfmisc_1(X0,X1)) != k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)) ),
    inference(unflattening,[status(thm)],[c_332])).

cnf(c_784,plain,
    ( k1_relset_1(sK0,sK1,sK2) = k1_relat_1(sK2) ),
    inference(equality_resolution,[status(thm)],[c_333])).

cnf(c_15,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k2_relset_1(X1,X2,X0) = k2_relat_1(X0) ),
    inference(cnf_transformation,[],[f52])).

cnf(c_323,plain,
    ( k2_relset_1(X0,X1,X2) = k2_relat_1(X2)
    | k1_zfmisc_1(k2_zfmisc_1(X0,X1)) != k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))
    | sK2 != X2 ),
    inference(resolution_lifted,[status(thm)],[c_15,c_19])).

cnf(c_324,plain,
    ( k2_relset_1(X0,X1,sK2) = k2_relat_1(sK2)
    | k1_zfmisc_1(k2_zfmisc_1(X0,X1)) != k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)) ),
    inference(unflattening,[status(thm)],[c_323])).

cnf(c_757,plain,
    ( k2_relset_1(sK0,sK1,sK2) = k2_relat_1(sK2) ),
    inference(equality_resolution,[status(thm)],[c_324])).

cnf(c_18,negated_conjecture,
    ( k2_relset_1(sK0,sK1,sK2) != k7_relset_1(sK0,sK1,sK2,sK0)
    | k1_relset_1(sK0,sK1,sK2) != k8_relset_1(sK0,sK1,sK2,sK1) ),
    inference(cnf_transformation,[],[f56])).

cnf(c_809,plain,
    ( k8_relset_1(sK0,sK1,sK2,sK1) != k1_relset_1(sK0,sK1,sK2)
    | k7_relset_1(sK0,sK1,sK2,sK0) != k2_relat_1(sK2) ),
    inference(demodulation,[status(thm)],[c_757,c_18])).

cnf(c_859,plain,
    ( k8_relset_1(sK0,sK1,sK2,sK1) != k1_relat_1(sK2)
    | k7_relset_1(sK0,sK1,sK2,sK0) != k2_relat_1(sK2) ),
    inference(demodulation,[status(thm)],[c_784,c_809])).

cnf(c_17,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k8_relset_1(X1,X2,X0,X3) = k10_relat_1(X0,X3) ),
    inference(cnf_transformation,[],[f54])).

cnf(c_305,plain,
    ( k8_relset_1(X0,X1,X2,X3) = k10_relat_1(X2,X3)
    | k1_zfmisc_1(k2_zfmisc_1(X0,X1)) != k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))
    | sK2 != X2 ),
    inference(resolution_lifted,[status(thm)],[c_17,c_19])).

cnf(c_306,plain,
    ( k8_relset_1(X0,X1,sK2,X2) = k10_relat_1(sK2,X2)
    | k1_zfmisc_1(k2_zfmisc_1(X0,X1)) != k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)) ),
    inference(unflattening,[status(thm)],[c_305])).

cnf(c_787,plain,
    ( k8_relset_1(sK0,sK1,sK2,X0) = k10_relat_1(sK2,X0) ),
    inference(equality_resolution,[status(thm)],[c_306])).

cnf(c_16,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k7_relset_1(X1,X2,X0,X3) = k9_relat_1(X0,X3) ),
    inference(cnf_transformation,[],[f53])).

cnf(c_314,plain,
    ( k7_relset_1(X0,X1,X2,X3) = k9_relat_1(X2,X3)
    | k1_zfmisc_1(k2_zfmisc_1(X0,X1)) != k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))
    | sK2 != X2 ),
    inference(resolution_lifted,[status(thm)],[c_16,c_19])).

cnf(c_315,plain,
    ( k7_relset_1(X0,X1,sK2,X2) = k9_relat_1(sK2,X2)
    | k1_zfmisc_1(k2_zfmisc_1(X0,X1)) != k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)) ),
    inference(unflattening,[status(thm)],[c_314])).

cnf(c_806,plain,
    ( k7_relset_1(sK0,sK1,sK2,X0) = k9_relat_1(sK2,X0) ),
    inference(equality_resolution,[status(thm)],[c_315])).

cnf(c_1258,plain,
    ( k10_relat_1(sK2,sK1) != k1_relat_1(sK2)
    | k9_relat_1(sK2,sK0) != k2_relat_1(sK2) ),
    inference(demodulation,[status(thm)],[c_859,c_787,c_806])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_1962,c_1394,c_1258])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.11  % Command    : iproveropt_run.sh %d %s
% 0.11/0.32  % Computer   : n024.cluster.edu
% 0.11/0.32  % Model      : x86_64 x86_64
% 0.11/0.32  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.11/0.32  % Memory     : 8042.1875MB
% 0.11/0.32  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.11/0.32  % CPULimit   : 60
% 0.11/0.32  % WCLimit    : 600
% 0.11/0.32  % DateTime   : Tue Dec  1 14:56:21 EST 2020
% 0.11/0.33  % CPUTime    : 
% 0.11/0.33  % Running in FOF mode
% 2.21/0.97  % SZS status Started for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.21/0.97  
% 2.21/0.97  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 2.21/0.97  
% 2.21/0.97  ------  iProver source info
% 2.21/0.97  
% 2.21/0.97  git: date: 2020-06-30 10:37:57 +0100
% 2.21/0.97  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 2.21/0.97  git: non_committed_changes: false
% 2.21/0.97  git: last_make_outside_of_git: false
% 2.21/0.97  
% 2.21/0.97  ------ 
% 2.21/0.97  
% 2.21/0.97  ------ Input Options
% 2.21/0.97  
% 2.21/0.97  --out_options                           all
% 2.21/0.97  --tptp_safe_out                         true
% 2.21/0.97  --problem_path                          ""
% 2.21/0.97  --include_path                          ""
% 2.21/0.97  --clausifier                            res/vclausify_rel
% 2.21/0.97  --clausifier_options                    --mode clausify
% 2.21/0.97  --stdin                                 false
% 2.21/0.97  --stats_out                             all
% 2.21/0.97  
% 2.21/0.97  ------ General Options
% 2.21/0.97  
% 2.21/0.97  --fof                                   false
% 2.21/0.97  --time_out_real                         305.
% 2.21/0.97  --time_out_virtual                      -1.
% 2.21/0.97  --symbol_type_check                     false
% 2.21/0.97  --clausify_out                          false
% 2.21/0.97  --sig_cnt_out                           false
% 2.21/0.97  --trig_cnt_out                          false
% 2.21/0.97  --trig_cnt_out_tolerance                1.
% 2.21/0.97  --trig_cnt_out_sk_spl                   false
% 2.21/0.97  --abstr_cl_out                          false
% 2.21/0.97  
% 2.21/0.97  ------ Global Options
% 2.21/0.97  
% 2.21/0.97  --schedule                              default
% 2.21/0.97  --add_important_lit                     false
% 2.21/0.97  --prop_solver_per_cl                    1000
% 2.21/0.97  --min_unsat_core                        false
% 2.21/0.97  --soft_assumptions                      false
% 2.21/0.97  --soft_lemma_size                       3
% 2.21/0.97  --prop_impl_unit_size                   0
% 2.21/0.97  --prop_impl_unit                        []
% 2.21/0.97  --share_sel_clauses                     true
% 2.21/0.97  --reset_solvers                         false
% 2.21/0.97  --bc_imp_inh                            [conj_cone]
% 2.21/0.97  --conj_cone_tolerance                   3.
% 2.21/0.97  --extra_neg_conj                        none
% 2.21/0.97  --large_theory_mode                     true
% 2.21/0.97  --prolific_symb_bound                   200
% 2.21/0.97  --lt_threshold                          2000
% 2.21/0.97  --clause_weak_htbl                      true
% 2.21/0.97  --gc_record_bc_elim                     false
% 2.21/0.97  
% 2.21/0.97  ------ Preprocessing Options
% 2.21/0.97  
% 2.21/0.97  --preprocessing_flag                    true
% 2.21/0.97  --time_out_prep_mult                    0.1
% 2.21/0.97  --splitting_mode                        input
% 2.21/0.97  --splitting_grd                         true
% 2.21/0.97  --splitting_cvd                         false
% 2.21/0.97  --splitting_cvd_svl                     false
% 2.21/0.97  --splitting_nvd                         32
% 2.21/0.97  --sub_typing                            true
% 2.21/0.97  --prep_gs_sim                           true
% 2.21/0.97  --prep_unflatten                        true
% 2.21/0.97  --prep_res_sim                          true
% 2.21/0.97  --prep_upred                            true
% 2.21/0.97  --prep_sem_filter                       exhaustive
% 2.21/0.97  --prep_sem_filter_out                   false
% 2.21/0.97  --pred_elim                             true
% 2.21/0.97  --res_sim_input                         true
% 2.21/0.97  --eq_ax_congr_red                       true
% 2.21/0.97  --pure_diseq_elim                       true
% 2.21/0.97  --brand_transform                       false
% 2.21/0.97  --non_eq_to_eq                          false
% 2.21/0.97  --prep_def_merge                        true
% 2.21/0.97  --prep_def_merge_prop_impl              false
% 2.21/0.97  --prep_def_merge_mbd                    true
% 2.21/0.97  --prep_def_merge_tr_red                 false
% 2.21/0.97  --prep_def_merge_tr_cl                  false
% 2.21/0.97  --smt_preprocessing                     true
% 2.21/0.97  --smt_ac_axioms                         fast
% 2.21/0.97  --preprocessed_out                      false
% 2.21/0.97  --preprocessed_stats                    false
% 2.21/0.97  
% 2.21/0.97  ------ Abstraction refinement Options
% 2.21/0.97  
% 2.21/0.97  --abstr_ref                             []
% 2.21/0.97  --abstr_ref_prep                        false
% 2.21/0.97  --abstr_ref_until_sat                   false
% 2.21/0.97  --abstr_ref_sig_restrict                funpre
% 2.21/0.97  --abstr_ref_af_restrict_to_split_sk     false
% 2.21/0.97  --abstr_ref_under                       []
% 2.21/0.97  
% 2.21/0.97  ------ SAT Options
% 2.21/0.97  
% 2.21/0.97  --sat_mode                              false
% 2.21/0.97  --sat_fm_restart_options                ""
% 2.21/0.97  --sat_gr_def                            false
% 2.21/0.97  --sat_epr_types                         true
% 2.21/0.97  --sat_non_cyclic_types                  false
% 2.21/0.97  --sat_finite_models                     false
% 2.21/0.97  --sat_fm_lemmas                         false
% 2.21/0.97  --sat_fm_prep                           false
% 2.21/0.98  --sat_fm_uc_incr                        true
% 2.21/0.98  --sat_out_model                         small
% 2.21/0.98  --sat_out_clauses                       false
% 2.21/0.98  
% 2.21/0.98  ------ QBF Options
% 2.21/0.98  
% 2.21/0.98  --qbf_mode                              false
% 2.21/0.98  --qbf_elim_univ                         false
% 2.21/0.98  --qbf_dom_inst                          none
% 2.21/0.98  --qbf_dom_pre_inst                      false
% 2.21/0.98  --qbf_sk_in                             false
% 2.21/0.98  --qbf_pred_elim                         true
% 2.21/0.98  --qbf_split                             512
% 2.21/0.98  
% 2.21/0.98  ------ BMC1 Options
% 2.21/0.98  
% 2.21/0.98  --bmc1_incremental                      false
% 2.21/0.98  --bmc1_axioms                           reachable_all
% 2.21/0.98  --bmc1_min_bound                        0
% 2.21/0.98  --bmc1_max_bound                        -1
% 2.21/0.98  --bmc1_max_bound_default                -1
% 2.21/0.98  --bmc1_symbol_reachability              true
% 2.21/0.98  --bmc1_property_lemmas                  false
% 2.21/0.98  --bmc1_k_induction                      false
% 2.21/0.98  --bmc1_non_equiv_states                 false
% 2.21/0.98  --bmc1_deadlock                         false
% 2.21/0.98  --bmc1_ucm                              false
% 2.21/0.98  --bmc1_add_unsat_core                   none
% 2.21/0.98  --bmc1_unsat_core_children              false
% 2.21/0.98  --bmc1_unsat_core_extrapolate_axioms    false
% 2.21/0.98  --bmc1_out_stat                         full
% 2.21/0.98  --bmc1_ground_init                      false
% 2.21/0.98  --bmc1_pre_inst_next_state              false
% 2.21/0.98  --bmc1_pre_inst_state                   false
% 2.21/0.98  --bmc1_pre_inst_reach_state             false
% 2.21/0.98  --bmc1_out_unsat_core                   false
% 2.21/0.98  --bmc1_aig_witness_out                  false
% 2.21/0.98  --bmc1_verbose                          false
% 2.21/0.98  --bmc1_dump_clauses_tptp                false
% 2.21/0.98  --bmc1_dump_unsat_core_tptp             false
% 2.21/0.98  --bmc1_dump_file                        -
% 2.21/0.98  --bmc1_ucm_expand_uc_limit              128
% 2.21/0.98  --bmc1_ucm_n_expand_iterations          6
% 2.21/0.98  --bmc1_ucm_extend_mode                  1
% 2.21/0.98  --bmc1_ucm_init_mode                    2
% 2.21/0.98  --bmc1_ucm_cone_mode                    none
% 2.21/0.98  --bmc1_ucm_reduced_relation_type        0
% 2.21/0.98  --bmc1_ucm_relax_model                  4
% 2.21/0.98  --bmc1_ucm_full_tr_after_sat            true
% 2.21/0.98  --bmc1_ucm_expand_neg_assumptions       false
% 2.21/0.98  --bmc1_ucm_layered_model                none
% 2.21/0.98  --bmc1_ucm_max_lemma_size               10
% 2.21/0.98  
% 2.21/0.98  ------ AIG Options
% 2.21/0.98  
% 2.21/0.98  --aig_mode                              false
% 2.21/0.98  
% 2.21/0.98  ------ Instantiation Options
% 2.21/0.98  
% 2.21/0.98  --instantiation_flag                    true
% 2.21/0.98  --inst_sos_flag                         false
% 2.21/0.98  --inst_sos_phase                        true
% 2.21/0.98  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 2.21/0.98  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 2.21/0.98  --inst_lit_sel_side                     num_symb
% 2.21/0.98  --inst_solver_per_active                1400
% 2.21/0.98  --inst_solver_calls_frac                1.
% 2.21/0.98  --inst_passive_queue_type               priority_queues
% 2.21/0.98  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 2.21/0.98  --inst_passive_queues_freq              [25;2]
% 2.21/0.98  --inst_dismatching                      true
% 2.21/0.98  --inst_eager_unprocessed_to_passive     true
% 2.21/0.98  --inst_prop_sim_given                   true
% 2.21/0.98  --inst_prop_sim_new                     false
% 2.21/0.98  --inst_subs_new                         false
% 2.21/0.98  --inst_eq_res_simp                      false
% 2.21/0.98  --inst_subs_given                       false
% 2.21/0.98  --inst_orphan_elimination               true
% 2.21/0.98  --inst_learning_loop_flag               true
% 2.21/0.98  --inst_learning_start                   3000
% 2.21/0.98  --inst_learning_factor                  2
% 2.21/0.98  --inst_start_prop_sim_after_learn       3
% 2.21/0.98  --inst_sel_renew                        solver
% 2.21/0.98  --inst_lit_activity_flag                true
% 2.21/0.98  --inst_restr_to_given                   false
% 2.21/0.98  --inst_activity_threshold               500
% 2.21/0.98  --inst_out_proof                        true
% 2.21/0.98  
% 2.21/0.98  ------ Resolution Options
% 2.21/0.98  
% 2.21/0.98  --resolution_flag                       true
% 2.21/0.98  --res_lit_sel                           adaptive
% 2.21/0.98  --res_lit_sel_side                      none
% 2.21/0.98  --res_ordering                          kbo
% 2.21/0.98  --res_to_prop_solver                    active
% 2.21/0.98  --res_prop_simpl_new                    false
% 2.21/0.98  --res_prop_simpl_given                  true
% 2.21/0.98  --res_passive_queue_type                priority_queues
% 2.21/0.98  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 2.21/0.98  --res_passive_queues_freq               [15;5]
% 2.21/0.98  --res_forward_subs                      full
% 2.21/0.98  --res_backward_subs                     full
% 2.21/0.98  --res_forward_subs_resolution           true
% 2.21/0.98  --res_backward_subs_resolution          true
% 2.21/0.98  --res_orphan_elimination                true
% 2.21/0.98  --res_time_limit                        2.
% 2.21/0.98  --res_out_proof                         true
% 2.21/0.98  
% 2.21/0.98  ------ Superposition Options
% 2.21/0.98  
% 2.21/0.98  --superposition_flag                    true
% 2.21/0.98  --sup_passive_queue_type                priority_queues
% 2.21/0.98  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 2.21/0.98  --sup_passive_queues_freq               [8;1;4]
% 2.21/0.98  --demod_completeness_check              fast
% 2.21/0.98  --demod_use_ground                      true
% 2.21/0.98  --sup_to_prop_solver                    passive
% 2.21/0.98  --sup_prop_simpl_new                    true
% 2.21/0.98  --sup_prop_simpl_given                  true
% 2.21/0.98  --sup_fun_splitting                     false
% 2.21/0.98  --sup_smt_interval                      50000
% 2.21/0.98  
% 2.21/0.98  ------ Superposition Simplification Setup
% 2.21/0.98  
% 2.21/0.98  --sup_indices_passive                   []
% 2.21/0.98  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.21/0.98  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.21/0.98  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.21/0.98  --sup_full_triv                         [TrivRules;PropSubs]
% 2.21/0.98  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.21/0.98  --sup_full_bw                           [BwDemod]
% 2.21/0.98  --sup_immed_triv                        [TrivRules]
% 2.21/0.98  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 2.21/0.98  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.21/0.98  --sup_immed_bw_main                     []
% 2.21/0.98  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.21/0.98  --sup_input_triv                        [Unflattening;TrivRules]
% 2.21/0.98  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.21/0.98  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.21/0.98  
% 2.21/0.98  ------ Combination Options
% 2.21/0.98  
% 2.21/0.98  --comb_res_mult                         3
% 2.21/0.98  --comb_sup_mult                         2
% 2.21/0.98  --comb_inst_mult                        10
% 2.21/0.98  
% 2.21/0.98  ------ Debug Options
% 2.21/0.98  
% 2.21/0.98  --dbg_backtrace                         false
% 2.21/0.98  --dbg_dump_prop_clauses                 false
% 2.21/0.98  --dbg_dump_prop_clauses_file            -
% 2.21/0.98  --dbg_out_stat                          false
% 2.21/0.98  ------ Parsing...
% 2.21/0.98  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 2.21/0.98  
% 2.21/0.98  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe:1:0s pe:2:0s pe_e  sf_s  rm: 2 0s  sf_e  pe_s  pe_e 
% 2.21/0.98  
% 2.21/0.98  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 2.21/0.98  
% 2.21/0.98  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 2.21/0.98  ------ Proving...
% 2.21/0.98  ------ Problem Properties 
% 2.21/0.98  
% 2.21/0.98  
% 2.21/0.98  clauses                                 15
% 2.21/0.98  conjectures                             1
% 2.21/0.98  EPR                                     2
% 2.21/0.98  Horn                                    15
% 2.21/0.98  unary                                   2
% 2.21/0.98  binary                                  8
% 2.21/0.98  lits                                    33
% 2.21/0.98  lits eq                                 17
% 2.21/0.98  fd_pure                                 0
% 2.21/0.98  fd_pseudo                               0
% 2.21/0.98  fd_cond                                 0
% 2.21/0.98  fd_pseudo_cond                          1
% 2.21/0.98  AC symbols                              0
% 2.21/0.98  
% 2.21/0.98  ------ Schedule dynamic 5 is on 
% 2.21/0.98  
% 2.21/0.98  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" Time Limit: 10.
% 2.21/0.98  
% 2.21/0.98  
% 2.21/0.98  ------ 
% 2.21/0.98  Current options:
% 2.21/0.98  ------ 
% 2.21/0.98  
% 2.21/0.98  ------ Input Options
% 2.21/0.98  
% 2.21/0.98  --out_options                           all
% 2.21/0.98  --tptp_safe_out                         true
% 2.21/0.98  --problem_path                          ""
% 2.21/0.98  --include_path                          ""
% 2.21/0.98  --clausifier                            res/vclausify_rel
% 2.21/0.98  --clausifier_options                    --mode clausify
% 2.21/0.98  --stdin                                 false
% 2.21/0.98  --stats_out                             all
% 2.21/0.98  
% 2.21/0.98  ------ General Options
% 2.21/0.98  
% 2.21/0.98  --fof                                   false
% 2.21/0.98  --time_out_real                         305.
% 2.21/0.98  --time_out_virtual                      -1.
% 2.21/0.98  --symbol_type_check                     false
% 2.21/0.98  --clausify_out                          false
% 2.21/0.98  --sig_cnt_out                           false
% 2.21/0.98  --trig_cnt_out                          false
% 2.21/0.98  --trig_cnt_out_tolerance                1.
% 2.21/0.98  --trig_cnt_out_sk_spl                   false
% 2.21/0.98  --abstr_cl_out                          false
% 2.21/0.98  
% 2.21/0.98  ------ Global Options
% 2.21/0.98  
% 2.21/0.98  --schedule                              default
% 2.21/0.98  --add_important_lit                     false
% 2.21/0.98  --prop_solver_per_cl                    1000
% 2.21/0.98  --min_unsat_core                        false
% 2.21/0.98  --soft_assumptions                      false
% 2.21/0.98  --soft_lemma_size                       3
% 2.21/0.98  --prop_impl_unit_size                   0
% 2.21/0.98  --prop_impl_unit                        []
% 2.21/0.98  --share_sel_clauses                     true
% 2.21/0.98  --reset_solvers                         false
% 2.21/0.98  --bc_imp_inh                            [conj_cone]
% 2.21/0.98  --conj_cone_tolerance                   3.
% 2.21/0.98  --extra_neg_conj                        none
% 2.21/0.98  --large_theory_mode                     true
% 2.21/0.98  --prolific_symb_bound                   200
% 2.21/0.98  --lt_threshold                          2000
% 2.21/0.98  --clause_weak_htbl                      true
% 2.21/0.98  --gc_record_bc_elim                     false
% 2.21/0.98  
% 2.21/0.98  ------ Preprocessing Options
% 2.21/0.98  
% 2.21/0.98  --preprocessing_flag                    true
% 2.21/0.98  --time_out_prep_mult                    0.1
% 2.21/0.98  --splitting_mode                        input
% 2.21/0.98  --splitting_grd                         true
% 2.21/0.98  --splitting_cvd                         false
% 2.21/0.98  --splitting_cvd_svl                     false
% 2.21/0.98  --splitting_nvd                         32
% 2.21/0.98  --sub_typing                            true
% 2.21/0.98  --prep_gs_sim                           true
% 2.21/0.98  --prep_unflatten                        true
% 2.21/0.98  --prep_res_sim                          true
% 2.21/0.98  --prep_upred                            true
% 2.21/0.98  --prep_sem_filter                       exhaustive
% 2.21/0.98  --prep_sem_filter_out                   false
% 2.21/0.98  --pred_elim                             true
% 2.21/0.98  --res_sim_input                         true
% 2.21/0.98  --eq_ax_congr_red                       true
% 2.21/0.98  --pure_diseq_elim                       true
% 2.21/0.98  --brand_transform                       false
% 2.21/0.98  --non_eq_to_eq                          false
% 2.21/0.98  --prep_def_merge                        true
% 2.21/0.98  --prep_def_merge_prop_impl              false
% 2.21/0.98  --prep_def_merge_mbd                    true
% 2.21/0.98  --prep_def_merge_tr_red                 false
% 2.21/0.98  --prep_def_merge_tr_cl                  false
% 2.21/0.98  --smt_preprocessing                     true
% 2.21/0.98  --smt_ac_axioms                         fast
% 2.21/0.98  --preprocessed_out                      false
% 2.21/0.98  --preprocessed_stats                    false
% 2.21/0.98  
% 2.21/0.98  ------ Abstraction refinement Options
% 2.21/0.98  
% 2.21/0.98  --abstr_ref                             []
% 2.21/0.98  --abstr_ref_prep                        false
% 2.21/0.98  --abstr_ref_until_sat                   false
% 2.21/0.98  --abstr_ref_sig_restrict                funpre
% 2.21/0.98  --abstr_ref_af_restrict_to_split_sk     false
% 2.21/0.98  --abstr_ref_under                       []
% 2.21/0.98  
% 2.21/0.98  ------ SAT Options
% 2.21/0.98  
% 2.21/0.98  --sat_mode                              false
% 2.21/0.98  --sat_fm_restart_options                ""
% 2.21/0.98  --sat_gr_def                            false
% 2.21/0.98  --sat_epr_types                         true
% 2.21/0.98  --sat_non_cyclic_types                  false
% 2.21/0.98  --sat_finite_models                     false
% 2.21/0.98  --sat_fm_lemmas                         false
% 2.21/0.98  --sat_fm_prep                           false
% 2.21/0.98  --sat_fm_uc_incr                        true
% 2.21/0.98  --sat_out_model                         small
% 2.21/0.98  --sat_out_clauses                       false
% 2.21/0.98  
% 2.21/0.98  ------ QBF Options
% 2.21/0.98  
% 2.21/0.98  --qbf_mode                              false
% 2.21/0.98  --qbf_elim_univ                         false
% 2.21/0.98  --qbf_dom_inst                          none
% 2.21/0.98  --qbf_dom_pre_inst                      false
% 2.21/0.98  --qbf_sk_in                             false
% 2.21/0.98  --qbf_pred_elim                         true
% 2.21/0.98  --qbf_split                             512
% 2.21/0.98  
% 2.21/0.98  ------ BMC1 Options
% 2.21/0.98  
% 2.21/0.98  --bmc1_incremental                      false
% 2.21/0.98  --bmc1_axioms                           reachable_all
% 2.21/0.98  --bmc1_min_bound                        0
% 2.21/0.98  --bmc1_max_bound                        -1
% 2.21/0.98  --bmc1_max_bound_default                -1
% 2.21/0.98  --bmc1_symbol_reachability              true
% 2.21/0.98  --bmc1_property_lemmas                  false
% 2.21/0.98  --bmc1_k_induction                      false
% 2.21/0.98  --bmc1_non_equiv_states                 false
% 2.21/0.98  --bmc1_deadlock                         false
% 2.21/0.98  --bmc1_ucm                              false
% 2.21/0.98  --bmc1_add_unsat_core                   none
% 2.21/0.98  --bmc1_unsat_core_children              false
% 2.21/0.98  --bmc1_unsat_core_extrapolate_axioms    false
% 2.21/0.98  --bmc1_out_stat                         full
% 2.21/0.98  --bmc1_ground_init                      false
% 2.21/0.98  --bmc1_pre_inst_next_state              false
% 2.21/0.98  --bmc1_pre_inst_state                   false
% 2.21/0.98  --bmc1_pre_inst_reach_state             false
% 2.21/0.98  --bmc1_out_unsat_core                   false
% 2.21/0.98  --bmc1_aig_witness_out                  false
% 2.21/0.98  --bmc1_verbose                          false
% 2.21/0.98  --bmc1_dump_clauses_tptp                false
% 2.21/0.98  --bmc1_dump_unsat_core_tptp             false
% 2.21/0.98  --bmc1_dump_file                        -
% 2.21/0.98  --bmc1_ucm_expand_uc_limit              128
% 2.21/0.98  --bmc1_ucm_n_expand_iterations          6
% 2.21/0.98  --bmc1_ucm_extend_mode                  1
% 2.21/0.98  --bmc1_ucm_init_mode                    2
% 2.21/0.98  --bmc1_ucm_cone_mode                    none
% 2.21/0.98  --bmc1_ucm_reduced_relation_type        0
% 2.21/0.98  --bmc1_ucm_relax_model                  4
% 2.21/0.98  --bmc1_ucm_full_tr_after_sat            true
% 2.21/0.98  --bmc1_ucm_expand_neg_assumptions       false
% 2.21/0.98  --bmc1_ucm_layered_model                none
% 2.21/0.98  --bmc1_ucm_max_lemma_size               10
% 2.21/0.98  
% 2.21/0.98  ------ AIG Options
% 2.21/0.98  
% 2.21/0.98  --aig_mode                              false
% 2.21/0.98  
% 2.21/0.98  ------ Instantiation Options
% 2.21/0.98  
% 2.21/0.98  --instantiation_flag                    true
% 2.21/0.98  --inst_sos_flag                         false
% 2.21/0.98  --inst_sos_phase                        true
% 2.21/0.98  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 2.21/0.98  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 2.21/0.98  --inst_lit_sel_side                     none
% 2.21/0.98  --inst_solver_per_active                1400
% 2.21/0.98  --inst_solver_calls_frac                1.
% 2.21/0.98  --inst_passive_queue_type               priority_queues
% 2.21/0.98  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 2.21/0.98  --inst_passive_queues_freq              [25;2]
% 2.21/0.98  --inst_dismatching                      true
% 2.21/0.98  --inst_eager_unprocessed_to_passive     true
% 2.21/0.98  --inst_prop_sim_given                   true
% 2.21/0.98  --inst_prop_sim_new                     false
% 2.21/0.98  --inst_subs_new                         false
% 2.21/0.98  --inst_eq_res_simp                      false
% 2.21/0.98  --inst_subs_given                       false
% 2.21/0.98  --inst_orphan_elimination               true
% 2.21/0.98  --inst_learning_loop_flag               true
% 2.21/0.98  --inst_learning_start                   3000
% 2.21/0.98  --inst_learning_factor                  2
% 2.21/0.98  --inst_start_prop_sim_after_learn       3
% 2.21/0.98  --inst_sel_renew                        solver
% 2.21/0.98  --inst_lit_activity_flag                true
% 2.21/0.98  --inst_restr_to_given                   false
% 2.21/0.98  --inst_activity_threshold               500
% 2.21/0.98  --inst_out_proof                        true
% 2.21/0.98  
% 2.21/0.98  ------ Resolution Options
% 2.21/0.98  
% 2.21/0.98  --resolution_flag                       false
% 2.21/0.98  --res_lit_sel                           adaptive
% 2.21/0.98  --res_lit_sel_side                      none
% 2.21/0.98  --res_ordering                          kbo
% 2.21/0.98  --res_to_prop_solver                    active
% 2.21/0.98  --res_prop_simpl_new                    false
% 2.21/0.98  --res_prop_simpl_given                  true
% 2.21/0.98  --res_passive_queue_type                priority_queues
% 2.21/0.98  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 2.21/0.98  --res_passive_queues_freq               [15;5]
% 2.21/0.98  --res_forward_subs                      full
% 2.21/0.98  --res_backward_subs                     full
% 2.21/0.98  --res_forward_subs_resolution           true
% 2.21/0.98  --res_backward_subs_resolution          true
% 2.21/0.98  --res_orphan_elimination                true
% 2.21/0.98  --res_time_limit                        2.
% 2.21/0.98  --res_out_proof                         true
% 2.21/0.98  
% 2.21/0.98  ------ Superposition Options
% 2.21/0.98  
% 2.21/0.98  --superposition_flag                    true
% 2.21/0.98  --sup_passive_queue_type                priority_queues
% 2.21/0.98  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 2.21/0.98  --sup_passive_queues_freq               [8;1;4]
% 2.21/0.98  --demod_completeness_check              fast
% 2.21/0.98  --demod_use_ground                      true
% 2.21/0.98  --sup_to_prop_solver                    passive
% 2.21/0.98  --sup_prop_simpl_new                    true
% 2.21/0.98  --sup_prop_simpl_given                  true
% 2.21/0.98  --sup_fun_splitting                     false
% 2.21/0.98  --sup_smt_interval                      50000
% 2.21/0.98  
% 2.21/0.98  ------ Superposition Simplification Setup
% 2.21/0.98  
% 2.21/0.98  --sup_indices_passive                   []
% 2.21/0.98  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.21/0.98  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.21/0.98  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.21/0.98  --sup_full_triv                         [TrivRules;PropSubs]
% 2.21/0.98  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.21/0.98  --sup_full_bw                           [BwDemod]
% 2.21/0.98  --sup_immed_triv                        [TrivRules]
% 2.21/0.98  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 2.21/0.98  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.21/0.98  --sup_immed_bw_main                     []
% 2.21/0.98  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.21/0.98  --sup_input_triv                        [Unflattening;TrivRules]
% 2.21/0.98  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.21/0.98  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.21/0.98  
% 2.21/0.98  ------ Combination Options
% 2.21/0.98  
% 2.21/0.98  --comb_res_mult                         3
% 2.21/0.98  --comb_sup_mult                         2
% 2.21/0.98  --comb_inst_mult                        10
% 2.21/0.98  
% 2.21/0.98  ------ Debug Options
% 2.21/0.98  
% 2.21/0.98  --dbg_backtrace                         false
% 2.21/0.98  --dbg_dump_prop_clauses                 false
% 2.21/0.98  --dbg_dump_prop_clauses_file            -
% 2.21/0.98  --dbg_out_stat                          false
% 2.21/0.98  
% 2.21/0.98  
% 2.21/0.98  
% 2.21/0.98  
% 2.21/0.98  ------ Proving...
% 2.21/0.98  
% 2.21/0.98  
% 2.21/0.98  % SZS status Theorem for theBenchmark.p
% 2.21/0.98  
% 2.21/0.98  % SZS output start CNFRefutation for theBenchmark.p
% 2.21/0.98  
% 2.21/0.98  fof(f10,axiom,(
% 2.21/0.98    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => (v5_relat_1(X2,X1) & v4_relat_1(X2,X0)))),
% 2.21/0.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.21/0.98  
% 2.21/0.98  fof(f26,plain,(
% 2.21/0.98    ! [X0,X1,X2] : ((v5_relat_1(X2,X1) & v4_relat_1(X2,X0)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 2.21/0.98    inference(ennf_transformation,[],[f10])).
% 2.21/0.98  
% 2.21/0.98  fof(f50,plain,(
% 2.21/0.98    ( ! [X2,X0,X1] : (v5_relat_1(X2,X1) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 2.21/0.98    inference(cnf_transformation,[],[f26])).
% 2.21/0.98  
% 2.21/0.98  fof(f3,axiom,(
% 2.21/0.98    ! [X0,X1] : (v1_relat_1(X1) => (v5_relat_1(X1,X0) <=> r1_tarski(k2_relat_1(X1),X0)))),
% 2.21/0.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.21/0.98  
% 2.21/0.98  fof(f18,plain,(
% 2.21/0.98    ! [X0,X1] : ((v5_relat_1(X1,X0) <=> r1_tarski(k2_relat_1(X1),X0)) | ~v1_relat_1(X1))),
% 2.21/0.98    inference(ennf_transformation,[],[f3])).
% 2.21/0.98  
% 2.21/0.98  fof(f34,plain,(
% 2.21/0.98    ! [X0,X1] : (((v5_relat_1(X1,X0) | ~r1_tarski(k2_relat_1(X1),X0)) & (r1_tarski(k2_relat_1(X1),X0) | ~v5_relat_1(X1,X0))) | ~v1_relat_1(X1))),
% 2.21/0.98    inference(nnf_transformation,[],[f18])).
% 2.21/0.98  
% 2.21/0.98  fof(f41,plain,(
% 2.21/0.98    ( ! [X0,X1] : (r1_tarski(k2_relat_1(X1),X0) | ~v5_relat_1(X1,X0) | ~v1_relat_1(X1)) )),
% 2.21/0.98    inference(cnf_transformation,[],[f34])).
% 2.21/0.98  
% 2.21/0.98  fof(f15,conjecture,(
% 2.21/0.98    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => (k1_relset_1(X0,X1,X2) = k8_relset_1(X0,X1,X2,X1) & k2_relset_1(X0,X1,X2) = k7_relset_1(X0,X1,X2,X0)))),
% 2.21/0.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.21/0.98  
% 2.21/0.98  fof(f16,negated_conjecture,(
% 2.21/0.98    ~! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => (k1_relset_1(X0,X1,X2) = k8_relset_1(X0,X1,X2,X1) & k2_relset_1(X0,X1,X2) = k7_relset_1(X0,X1,X2,X0)))),
% 2.21/0.98    inference(negated_conjecture,[],[f15])).
% 2.21/0.98  
% 2.21/0.98  fof(f31,plain,(
% 2.21/0.98    ? [X0,X1,X2] : ((k1_relset_1(X0,X1,X2) != k8_relset_1(X0,X1,X2,X1) | k2_relset_1(X0,X1,X2) != k7_relset_1(X0,X1,X2,X0)) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 2.21/0.98    inference(ennf_transformation,[],[f16])).
% 2.21/0.98  
% 2.21/0.98  fof(f35,plain,(
% 2.21/0.98    ? [X0,X1,X2] : ((k1_relset_1(X0,X1,X2) != k8_relset_1(X0,X1,X2,X1) | k2_relset_1(X0,X1,X2) != k7_relset_1(X0,X1,X2,X0)) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) => ((k1_relset_1(sK0,sK1,sK2) != k8_relset_1(sK0,sK1,sK2,sK1) | k2_relset_1(sK0,sK1,sK2) != k7_relset_1(sK0,sK1,sK2,sK0)) & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))))),
% 2.21/0.98    introduced(choice_axiom,[])).
% 2.21/0.98  
% 2.21/0.98  fof(f36,plain,(
% 2.21/0.98    (k1_relset_1(sK0,sK1,sK2) != k8_relset_1(sK0,sK1,sK2,sK1) | k2_relset_1(sK0,sK1,sK2) != k7_relset_1(sK0,sK1,sK2,sK0)) & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))),
% 2.21/0.98    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f31,f35])).
% 2.21/0.98  
% 2.21/0.98  fof(f55,plain,(
% 2.21/0.98    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))),
% 2.21/0.98    inference(cnf_transformation,[],[f36])).
% 2.21/0.98  
% 2.21/0.98  fof(f2,axiom,(
% 2.21/0.98    ! [X0] : (v1_relat_1(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => v1_relat_1(X1)))),
% 2.21/0.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.21/0.98  
% 2.21/0.98  fof(f17,plain,(
% 2.21/0.98    ! [X0] : (! [X1] : (v1_relat_1(X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) | ~v1_relat_1(X0))),
% 2.21/0.98    inference(ennf_transformation,[],[f2])).
% 2.21/0.98  
% 2.21/0.98  fof(f40,plain,(
% 2.21/0.98    ( ! [X0,X1] : (v1_relat_1(X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0)) | ~v1_relat_1(X0)) )),
% 2.21/0.98    inference(cnf_transformation,[],[f17])).
% 2.21/0.98  
% 2.21/0.98  fof(f4,axiom,(
% 2.21/0.98    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1))),
% 2.21/0.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.21/0.98  
% 2.21/0.98  fof(f43,plain,(
% 2.21/0.98    ( ! [X0,X1] : (v1_relat_1(k2_zfmisc_1(X0,X1))) )),
% 2.21/0.98    inference(cnf_transformation,[],[f4])).
% 2.21/0.98  
% 2.21/0.98  fof(f6,axiom,(
% 2.21/0.98    ! [X0] : (v1_relat_1(X0) => k10_relat_1(X0,k2_relat_1(X0)) = k1_relat_1(X0))),
% 2.21/0.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.21/0.98  
% 2.21/0.98  fof(f20,plain,(
% 2.21/0.98    ! [X0] : (k10_relat_1(X0,k2_relat_1(X0)) = k1_relat_1(X0) | ~v1_relat_1(X0))),
% 2.21/0.98    inference(ennf_transformation,[],[f6])).
% 2.21/0.98  
% 2.21/0.98  fof(f45,plain,(
% 2.21/0.98    ( ! [X0] : (k10_relat_1(X0,k2_relat_1(X0)) = k1_relat_1(X0) | ~v1_relat_1(X0)) )),
% 2.21/0.98    inference(cnf_transformation,[],[f20])).
% 2.21/0.98  
% 2.21/0.98  fof(f8,axiom,(
% 2.21/0.98    ! [X0,X1,X2] : (v1_relat_1(X2) => (r1_tarski(X0,X1) => r1_tarski(k10_relat_1(X2,X0),k10_relat_1(X2,X1))))),
% 2.21/0.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.21/0.98  
% 2.21/0.98  fof(f22,plain,(
% 2.21/0.98    ! [X0,X1,X2] : ((r1_tarski(k10_relat_1(X2,X0),k10_relat_1(X2,X1)) | ~r1_tarski(X0,X1)) | ~v1_relat_1(X2))),
% 2.21/0.98    inference(ennf_transformation,[],[f8])).
% 2.21/0.98  
% 2.21/0.98  fof(f23,plain,(
% 2.21/0.98    ! [X0,X1,X2] : (r1_tarski(k10_relat_1(X2,X0),k10_relat_1(X2,X1)) | ~r1_tarski(X0,X1) | ~v1_relat_1(X2))),
% 2.21/0.98    inference(flattening,[],[f22])).
% 2.21/0.98  
% 2.21/0.98  fof(f47,plain,(
% 2.21/0.98    ( ! [X2,X0,X1] : (r1_tarski(k10_relat_1(X2,X0),k10_relat_1(X2,X1)) | ~r1_tarski(X0,X1) | ~v1_relat_1(X2)) )),
% 2.21/0.98    inference(cnf_transformation,[],[f23])).
% 2.21/0.98  
% 2.21/0.98  fof(f7,axiom,(
% 2.21/0.98    ! [X0,X1] : (v1_relat_1(X1) => r1_tarski(k10_relat_1(X1,X0),k10_relat_1(X1,k2_relat_1(X1))))),
% 2.21/0.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.21/0.98  
% 2.21/0.98  fof(f21,plain,(
% 2.21/0.98    ! [X0,X1] : (r1_tarski(k10_relat_1(X1,X0),k10_relat_1(X1,k2_relat_1(X1))) | ~v1_relat_1(X1))),
% 2.21/0.98    inference(ennf_transformation,[],[f7])).
% 2.21/0.98  
% 2.21/0.98  fof(f46,plain,(
% 2.21/0.98    ( ! [X0,X1] : (r1_tarski(k10_relat_1(X1,X0),k10_relat_1(X1,k2_relat_1(X1))) | ~v1_relat_1(X1)) )),
% 2.21/0.98    inference(cnf_transformation,[],[f21])).
% 2.21/0.98  
% 2.21/0.98  fof(f1,axiom,(
% 2.21/0.98    ! [X0,X1] : (X0 = X1 <=> (r1_tarski(X1,X0) & r1_tarski(X0,X1)))),
% 2.21/0.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.21/0.98  
% 2.21/0.98  fof(f32,plain,(
% 2.21/0.98    ! [X0,X1] : ((X0 = X1 | (~r1_tarski(X1,X0) | ~r1_tarski(X0,X1))) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 2.21/0.98    inference(nnf_transformation,[],[f1])).
% 2.21/0.98  
% 2.21/0.98  fof(f33,plain,(
% 2.21/0.98    ! [X0,X1] : ((X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 2.21/0.98    inference(flattening,[],[f32])).
% 2.21/0.98  
% 2.21/0.98  fof(f39,plain,(
% 2.21/0.98    ( ! [X0,X1] : (X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) )),
% 2.21/0.98    inference(cnf_transformation,[],[f33])).
% 2.21/0.98  
% 2.21/0.98  fof(f49,plain,(
% 2.21/0.98    ( ! [X2,X0,X1] : (v4_relat_1(X2,X0) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 2.21/0.98    inference(cnf_transformation,[],[f26])).
% 2.21/0.98  
% 2.21/0.98  fof(f9,axiom,(
% 2.21/0.98    ! [X0,X1] : ((v4_relat_1(X1,X0) & v1_relat_1(X1)) => k7_relat_1(X1,X0) = X1)),
% 2.21/0.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.21/0.98  
% 2.21/0.98  fof(f24,plain,(
% 2.21/0.98    ! [X0,X1] : (k7_relat_1(X1,X0) = X1 | (~v4_relat_1(X1,X0) | ~v1_relat_1(X1)))),
% 2.21/0.98    inference(ennf_transformation,[],[f9])).
% 2.21/0.98  
% 2.21/0.98  fof(f25,plain,(
% 2.21/0.98    ! [X0,X1] : (k7_relat_1(X1,X0) = X1 | ~v4_relat_1(X1,X0) | ~v1_relat_1(X1))),
% 2.21/0.98    inference(flattening,[],[f24])).
% 2.21/0.98  
% 2.21/0.98  fof(f48,plain,(
% 2.21/0.98    ( ! [X0,X1] : (k7_relat_1(X1,X0) = X1 | ~v4_relat_1(X1,X0) | ~v1_relat_1(X1)) )),
% 2.21/0.98    inference(cnf_transformation,[],[f25])).
% 2.21/0.98  
% 2.21/0.98  fof(f5,axiom,(
% 2.21/0.98    ! [X0,X1] : (v1_relat_1(X1) => k2_relat_1(k7_relat_1(X1,X0)) = k9_relat_1(X1,X0))),
% 2.21/0.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.21/0.98  
% 2.21/0.98  fof(f19,plain,(
% 2.21/0.98    ! [X0,X1] : (k2_relat_1(k7_relat_1(X1,X0)) = k9_relat_1(X1,X0) | ~v1_relat_1(X1))),
% 2.21/0.98    inference(ennf_transformation,[],[f5])).
% 2.21/0.98  
% 2.21/0.98  fof(f44,plain,(
% 2.21/0.98    ( ! [X0,X1] : (k2_relat_1(k7_relat_1(X1,X0)) = k9_relat_1(X1,X0) | ~v1_relat_1(X1)) )),
% 2.21/0.98    inference(cnf_transformation,[],[f19])).
% 2.21/0.98  
% 2.21/0.98  fof(f11,axiom,(
% 2.21/0.98    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k1_relat_1(X2) = k1_relset_1(X0,X1,X2))),
% 2.21/0.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.21/0.98  
% 2.21/0.98  fof(f27,plain,(
% 2.21/0.98    ! [X0,X1,X2] : (k1_relat_1(X2) = k1_relset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 2.21/0.98    inference(ennf_transformation,[],[f11])).
% 2.21/0.98  
% 2.21/0.98  fof(f51,plain,(
% 2.21/0.98    ( ! [X2,X0,X1] : (k1_relat_1(X2) = k1_relset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 2.21/0.98    inference(cnf_transformation,[],[f27])).
% 2.21/0.98  
% 2.21/0.98  fof(f12,axiom,(
% 2.21/0.98    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k2_relat_1(X2) = k2_relset_1(X0,X1,X2))),
% 2.21/0.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.21/0.98  
% 2.21/0.98  fof(f28,plain,(
% 2.21/0.98    ! [X0,X1,X2] : (k2_relat_1(X2) = k2_relset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 2.21/0.98    inference(ennf_transformation,[],[f12])).
% 2.21/0.98  
% 2.21/0.98  fof(f52,plain,(
% 2.21/0.98    ( ! [X2,X0,X1] : (k2_relat_1(X2) = k2_relset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 2.21/0.98    inference(cnf_transformation,[],[f28])).
% 2.21/0.98  
% 2.21/0.98  fof(f56,plain,(
% 2.21/0.98    k1_relset_1(sK0,sK1,sK2) != k8_relset_1(sK0,sK1,sK2,sK1) | k2_relset_1(sK0,sK1,sK2) != k7_relset_1(sK0,sK1,sK2,sK0)),
% 2.21/0.98    inference(cnf_transformation,[],[f36])).
% 2.21/0.98  
% 2.21/0.98  fof(f14,axiom,(
% 2.21/0.98    ! [X0,X1,X2,X3] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k10_relat_1(X2,X3) = k8_relset_1(X0,X1,X2,X3))),
% 2.21/0.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.21/0.98  
% 2.21/0.98  fof(f30,plain,(
% 2.21/0.98    ! [X0,X1,X2,X3] : (k10_relat_1(X2,X3) = k8_relset_1(X0,X1,X2,X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 2.21/0.98    inference(ennf_transformation,[],[f14])).
% 2.21/0.98  
% 2.21/0.98  fof(f54,plain,(
% 2.21/0.98    ( ! [X2,X0,X3,X1] : (k10_relat_1(X2,X3) = k8_relset_1(X0,X1,X2,X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 2.21/0.98    inference(cnf_transformation,[],[f30])).
% 2.21/0.98  
% 2.21/0.98  fof(f13,axiom,(
% 2.21/0.98    ! [X0,X1,X2,X3] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k9_relat_1(X2,X3) = k7_relset_1(X0,X1,X2,X3))),
% 2.21/0.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.21/0.98  
% 2.21/0.98  fof(f29,plain,(
% 2.21/0.98    ! [X0,X1,X2,X3] : (k9_relat_1(X2,X3) = k7_relset_1(X0,X1,X2,X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 2.21/0.98    inference(ennf_transformation,[],[f13])).
% 2.21/0.98  
% 2.21/0.98  fof(f53,plain,(
% 2.21/0.98    ( ! [X2,X0,X3,X1] : (k9_relat_1(X2,X3) = k7_relset_1(X0,X1,X2,X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 2.21/0.98    inference(cnf_transformation,[],[f29])).
% 2.21/0.98  
% 2.21/0.98  cnf(c_12,plain,
% 2.21/0.98      ( v5_relat_1(X0,X1)
% 2.21/0.98      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) ),
% 2.21/0.98      inference(cnf_transformation,[],[f50]) ).
% 2.21/0.98  
% 2.21/0.98  cnf(c_5,plain,
% 2.21/0.98      ( ~ v5_relat_1(X0,X1)
% 2.21/0.98      | r1_tarski(k2_relat_1(X0),X1)
% 2.21/0.98      | ~ v1_relat_1(X0) ),
% 2.21/0.98      inference(cnf_transformation,[],[f41]) ).
% 2.21/0.98  
% 2.21/0.98  cnf(c_241,plain,
% 2.21/0.98      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 2.21/0.98      | r1_tarski(k2_relat_1(X0),X2)
% 2.21/0.98      | ~ v1_relat_1(X0) ),
% 2.21/0.98      inference(resolution,[status(thm)],[c_12,c_5]) ).
% 2.21/0.98  
% 2.21/0.98  cnf(c_19,negated_conjecture,
% 2.21/0.98      ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ),
% 2.21/0.98      inference(cnf_transformation,[],[f55]) ).
% 2.21/0.98  
% 2.21/0.98  cnf(c_275,plain,
% 2.21/0.98      ( r1_tarski(k2_relat_1(X0),X1)
% 2.21/0.98      | ~ v1_relat_1(X0)
% 2.21/0.98      | k1_zfmisc_1(k2_zfmisc_1(X2,X1)) != k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))
% 2.21/0.98      | sK2 != X0 ),
% 2.21/0.98      inference(resolution_lifted,[status(thm)],[c_241,c_19]) ).
% 2.21/0.98  
% 2.21/0.98  cnf(c_276,plain,
% 2.21/0.98      ( r1_tarski(k2_relat_1(sK2),X0)
% 2.21/0.98      | ~ v1_relat_1(sK2)
% 2.21/0.98      | k1_zfmisc_1(k2_zfmisc_1(X1,X0)) != k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)) ),
% 2.21/0.98      inference(unflattening,[status(thm)],[c_275]) ).
% 2.21/0.98  
% 2.21/0.98  cnf(c_644,plain,
% 2.21/0.98      ( k1_zfmisc_1(k2_zfmisc_1(X0,X1)) != k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))
% 2.21/0.98      | r1_tarski(k2_relat_1(sK2),X1) = iProver_top
% 2.21/0.98      | v1_relat_1(sK2) != iProver_top ),
% 2.21/0.98      inference(predicate_to_equality,[status(thm)],[c_276]) ).
% 2.21/0.98  
% 2.21/0.98  cnf(c_277,plain,
% 2.21/0.98      ( k1_zfmisc_1(k2_zfmisc_1(X0,X1)) != k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))
% 2.21/0.98      | r1_tarski(k2_relat_1(sK2),X1) = iProver_top
% 2.21/0.98      | v1_relat_1(sK2) != iProver_top ),
% 2.21/0.98      inference(predicate_to_equality,[status(thm)],[c_276]) ).
% 2.21/0.98  
% 2.21/0.98  cnf(c_441,plain,( X0 = X0 ),theory(equality) ).
% 2.21/0.98  
% 2.21/0.98  cnf(c_746,plain,
% 2.21/0.98      ( k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)) = k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)) ),
% 2.21/0.98      inference(instantiation,[status(thm)],[c_441]) ).
% 2.21/0.98  
% 2.21/0.98  cnf(c_3,plain,
% 2.21/0.98      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
% 2.21/0.98      | ~ v1_relat_1(X1)
% 2.21/0.98      | v1_relat_1(X0) ),
% 2.21/0.98      inference(cnf_transformation,[],[f40]) ).
% 2.21/0.98  
% 2.21/0.98  cnf(c_260,plain,
% 2.21/0.98      ( ~ v1_relat_1(X0)
% 2.21/0.98      | v1_relat_1(X1)
% 2.21/0.98      | k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)) != k1_zfmisc_1(X0)
% 2.21/0.98      | sK2 != X1 ),
% 2.21/0.98      inference(resolution_lifted,[status(thm)],[c_3,c_19]) ).
% 2.21/0.98  
% 2.21/0.98  cnf(c_261,plain,
% 2.21/0.98      ( ~ v1_relat_1(X0)
% 2.21/0.98      | v1_relat_1(sK2)
% 2.21/0.98      | k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)) != k1_zfmisc_1(X0) ),
% 2.21/0.98      inference(unflattening,[status(thm)],[c_260]) ).
% 2.21/0.98  
% 2.21/0.98  cnf(c_741,plain,
% 2.21/0.98      ( ~ v1_relat_1(k2_zfmisc_1(X0,X1))
% 2.21/0.98      | v1_relat_1(sK2)
% 2.21/0.98      | k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)) != k1_zfmisc_1(k2_zfmisc_1(X0,X1)) ),
% 2.21/0.98      inference(instantiation,[status(thm)],[c_261]) ).
% 2.21/0.98  
% 2.21/0.98  cnf(c_843,plain,
% 2.21/0.98      ( ~ v1_relat_1(k2_zfmisc_1(sK0,sK1))
% 2.21/0.98      | v1_relat_1(sK2)
% 2.21/0.98      | k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)) != k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)) ),
% 2.21/0.98      inference(instantiation,[status(thm)],[c_741]) ).
% 2.21/0.98  
% 2.21/0.98  cnf(c_844,plain,
% 2.21/0.98      ( k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)) != k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))
% 2.21/0.98      | v1_relat_1(k2_zfmisc_1(sK0,sK1)) != iProver_top
% 2.21/0.98      | v1_relat_1(sK2) = iProver_top ),
% 2.21/0.98      inference(predicate_to_equality,[status(thm)],[c_843]) ).
% 2.21/0.98  
% 2.21/0.98  cnf(c_6,plain,
% 2.21/0.98      ( v1_relat_1(k2_zfmisc_1(X0,X1)) ),
% 2.21/0.98      inference(cnf_transformation,[],[f43]) ).
% 2.21/0.98  
% 2.21/0.98  cnf(c_949,plain,
% 2.21/0.98      ( v1_relat_1(k2_zfmisc_1(sK0,sK1)) ),
% 2.21/0.98      inference(instantiation,[status(thm)],[c_6]) ).
% 2.21/0.98  
% 2.21/0.98  cnf(c_950,plain,
% 2.21/0.98      ( v1_relat_1(k2_zfmisc_1(sK0,sK1)) = iProver_top ),
% 2.21/0.98      inference(predicate_to_equality,[status(thm)],[c_949]) ).
% 2.21/0.98  
% 2.21/0.98  cnf(c_1262,plain,
% 2.21/0.98      ( r1_tarski(k2_relat_1(sK2),X1) = iProver_top
% 2.21/0.98      | k1_zfmisc_1(k2_zfmisc_1(X0,X1)) != k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)) ),
% 2.21/0.98      inference(global_propositional_subsumption,
% 2.21/0.98                [status(thm)],
% 2.21/0.98                [c_644,c_277,c_746,c_844,c_950]) ).
% 2.21/0.98  
% 2.21/0.98  cnf(c_1263,plain,
% 2.21/0.98      ( k1_zfmisc_1(k2_zfmisc_1(X0,X1)) != k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))
% 2.21/0.98      | r1_tarski(k2_relat_1(sK2),X1) = iProver_top ),
% 2.21/0.98      inference(renaming,[status(thm)],[c_1262]) ).
% 2.21/0.98  
% 2.21/0.98  cnf(c_1270,plain,
% 2.21/0.98      ( r1_tarski(k2_relat_1(sK2),sK1) = iProver_top ),
% 2.21/0.98      inference(equality_resolution,[status(thm)],[c_1263]) ).
% 2.21/0.98  
% 2.21/0.98  cnf(c_645,plain,
% 2.21/0.98      ( k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)) != k1_zfmisc_1(X0)
% 2.21/0.98      | v1_relat_1(X0) != iProver_top
% 2.21/0.98      | v1_relat_1(sK2) = iProver_top ),
% 2.21/0.98      inference(predicate_to_equality,[status(thm)],[c_261]) ).
% 2.21/0.98  
% 2.21/0.98  cnf(c_1151,plain,
% 2.21/0.98      ( v1_relat_1(sK2) = iProver_top ),
% 2.21/0.98      inference(global_propositional_subsumption,
% 2.21/0.98                [status(thm)],
% 2.21/0.98                [c_645,c_746,c_844,c_950]) ).
% 2.21/0.98  
% 2.21/0.98  cnf(c_8,plain,
% 2.21/0.98      ( ~ v1_relat_1(X0)
% 2.21/0.98      | k10_relat_1(X0,k2_relat_1(X0)) = k1_relat_1(X0) ),
% 2.21/0.98      inference(cnf_transformation,[],[f45]) ).
% 2.21/0.98  
% 2.21/0.98  cnf(c_648,plain,
% 2.21/0.98      ( k10_relat_1(X0,k2_relat_1(X0)) = k1_relat_1(X0)
% 2.21/0.98      | v1_relat_1(X0) != iProver_top ),
% 2.21/0.98      inference(predicate_to_equality,[status(thm)],[c_8]) ).
% 2.21/0.98  
% 2.21/0.98  cnf(c_1157,plain,
% 2.21/0.98      ( k10_relat_1(sK2,k2_relat_1(sK2)) = k1_relat_1(sK2) ),
% 2.21/0.98      inference(superposition,[status(thm)],[c_1151,c_648]) ).
% 2.21/0.98  
% 2.21/0.98  cnf(c_10,plain,
% 2.21/0.98      ( ~ r1_tarski(X0,X1)
% 2.21/0.98      | r1_tarski(k10_relat_1(X2,X0),k10_relat_1(X2,X1))
% 2.21/0.98      | ~ v1_relat_1(X2) ),
% 2.21/0.98      inference(cnf_transformation,[],[f47]) ).
% 2.21/0.98  
% 2.21/0.98  cnf(c_646,plain,
% 2.21/0.98      ( r1_tarski(X0,X1) != iProver_top
% 2.21/0.98      | r1_tarski(k10_relat_1(X2,X0),k10_relat_1(X2,X1)) = iProver_top
% 2.21/0.98      | v1_relat_1(X2) != iProver_top ),
% 2.21/0.98      inference(predicate_to_equality,[status(thm)],[c_10]) ).
% 2.21/0.98  
% 2.21/0.98  cnf(c_1570,plain,
% 2.21/0.98      ( r1_tarski(k1_relat_1(sK2),k10_relat_1(sK2,X0)) = iProver_top
% 2.21/0.98      | r1_tarski(k2_relat_1(sK2),X0) != iProver_top
% 2.21/0.98      | v1_relat_1(sK2) != iProver_top ),
% 2.21/0.98      inference(superposition,[status(thm)],[c_1157,c_646]) ).
% 2.21/0.98  
% 2.21/0.98  cnf(c_1821,plain,
% 2.21/0.98      ( r1_tarski(k2_relat_1(sK2),X0) != iProver_top
% 2.21/0.98      | r1_tarski(k1_relat_1(sK2),k10_relat_1(sK2,X0)) = iProver_top ),
% 2.21/0.98      inference(global_propositional_subsumption,
% 2.21/0.98                [status(thm)],
% 2.21/0.98                [c_1570,c_746,c_844,c_950]) ).
% 2.21/0.98  
% 2.21/0.98  cnf(c_1822,plain,
% 2.21/0.98      ( r1_tarski(k1_relat_1(sK2),k10_relat_1(sK2,X0)) = iProver_top
% 2.21/0.98      | r1_tarski(k2_relat_1(sK2),X0) != iProver_top ),
% 2.21/0.98      inference(renaming,[status(thm)],[c_1821]) ).
% 2.21/0.98  
% 2.21/0.98  cnf(c_9,plain,
% 2.21/0.98      ( r1_tarski(k10_relat_1(X0,X1),k10_relat_1(X0,k2_relat_1(X0)))
% 2.21/0.98      | ~ v1_relat_1(X0) ),
% 2.21/0.98      inference(cnf_transformation,[],[f46]) ).
% 2.21/0.98  
% 2.21/0.98  cnf(c_647,plain,
% 2.21/0.98      ( r1_tarski(k10_relat_1(X0,X1),k10_relat_1(X0,k2_relat_1(X0))) = iProver_top
% 2.21/0.98      | v1_relat_1(X0) != iProver_top ),
% 2.21/0.98      inference(predicate_to_equality,[status(thm)],[c_9]) ).
% 2.21/0.98  
% 2.21/0.98  cnf(c_1452,plain,
% 2.21/0.98      ( r1_tarski(k10_relat_1(sK2,X0),k1_relat_1(sK2)) = iProver_top
% 2.21/0.98      | v1_relat_1(sK2) != iProver_top ),
% 2.21/0.98      inference(superposition,[status(thm)],[c_1157,c_647]) ).
% 2.21/0.98  
% 2.21/0.98  cnf(c_1729,plain,
% 2.21/0.98      ( r1_tarski(k10_relat_1(sK2,X0),k1_relat_1(sK2)) = iProver_top ),
% 2.21/0.98      inference(global_propositional_subsumption,
% 2.21/0.98                [status(thm)],
% 2.21/0.98                [c_1452,c_746,c_844,c_950]) ).
% 2.21/0.98  
% 2.21/0.98  cnf(c_0,plain,
% 2.21/0.98      ( ~ r1_tarski(X0,X1) | ~ r1_tarski(X1,X0) | X0 = X1 ),
% 2.21/0.98      inference(cnf_transformation,[],[f39]) ).
% 2.21/0.98  
% 2.21/0.98  cnf(c_652,plain,
% 2.21/0.98      ( X0 = X1
% 2.21/0.98      | r1_tarski(X0,X1) != iProver_top
% 2.21/0.98      | r1_tarski(X1,X0) != iProver_top ),
% 2.21/0.98      inference(predicate_to_equality,[status(thm)],[c_0]) ).
% 2.21/0.98  
% 2.21/0.98  cnf(c_1737,plain,
% 2.21/0.98      ( k10_relat_1(sK2,X0) = k1_relat_1(sK2)
% 2.21/0.98      | r1_tarski(k1_relat_1(sK2),k10_relat_1(sK2,X0)) != iProver_top ),
% 2.21/0.98      inference(superposition,[status(thm)],[c_1729,c_652]) ).
% 2.21/0.98  
% 2.21/0.98  cnf(c_1949,plain,
% 2.21/0.98      ( k10_relat_1(sK2,X0) = k1_relat_1(sK2)
% 2.21/0.98      | r1_tarski(k2_relat_1(sK2),X0) != iProver_top ),
% 2.21/0.98      inference(superposition,[status(thm)],[c_1822,c_1737]) ).
% 2.21/0.98  
% 2.21/0.98  cnf(c_1962,plain,
% 2.21/0.98      ( k10_relat_1(sK2,sK1) = k1_relat_1(sK2) ),
% 2.21/0.98      inference(superposition,[status(thm)],[c_1270,c_1949]) ).
% 2.21/0.98  
% 2.21/0.98  cnf(c_13,plain,
% 2.21/0.98      ( v4_relat_1(X0,X1)
% 2.21/0.98      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) ),
% 2.21/0.98      inference(cnf_transformation,[],[f49]) ).
% 2.21/0.98  
% 2.21/0.98  cnf(c_11,plain,
% 2.21/0.98      ( ~ v4_relat_1(X0,X1) | ~ v1_relat_1(X0) | k7_relat_1(X0,X1) = X0 ),
% 2.21/0.98      inference(cnf_transformation,[],[f48]) ).
% 2.21/0.98  
% 2.21/0.98  cnf(c_223,plain,
% 2.21/0.98      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 2.21/0.98      | ~ v1_relat_1(X0)
% 2.21/0.98      | k7_relat_1(X0,X1) = X0 ),
% 2.21/0.98      inference(resolution,[status(thm)],[c_13,c_11]) ).
% 2.21/0.98  
% 2.21/0.98  cnf(c_290,plain,
% 2.21/0.98      ( ~ v1_relat_1(X0)
% 2.21/0.98      | k7_relat_1(X0,X1) = X0
% 2.21/0.98      | k1_zfmisc_1(k2_zfmisc_1(X1,X2)) != k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))
% 2.21/0.98      | sK2 != X0 ),
% 2.21/0.98      inference(resolution_lifted,[status(thm)],[c_223,c_19]) ).
% 2.21/0.98  
% 2.21/0.98  cnf(c_291,plain,
% 2.21/0.98      ( ~ v1_relat_1(sK2)
% 2.21/0.98      | k7_relat_1(sK2,X0) = sK2
% 2.21/0.98      | k1_zfmisc_1(k2_zfmisc_1(X0,X1)) != k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)) ),
% 2.21/0.98      inference(unflattening,[status(thm)],[c_290]) ).
% 2.21/0.98  
% 2.21/0.98  cnf(c_643,plain,
% 2.21/0.98      ( k7_relat_1(sK2,X0) = sK2
% 2.21/0.98      | k1_zfmisc_1(k2_zfmisc_1(X0,X1)) != k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))
% 2.21/0.98      | v1_relat_1(sK2) != iProver_top ),
% 2.21/0.98      inference(predicate_to_equality,[status(thm)],[c_291]) ).
% 2.21/0.98  
% 2.21/0.98  cnf(c_945,plain,
% 2.21/0.98      ( k7_relat_1(sK2,sK0) = sK2 | v1_relat_1(sK2) != iProver_top ),
% 2.21/0.98      inference(equality_resolution,[status(thm)],[c_643]) ).
% 2.21/0.98  
% 2.21/0.98  cnf(c_946,plain,
% 2.21/0.98      ( ~ v1_relat_1(sK2) | k7_relat_1(sK2,sK0) = sK2 ),
% 2.21/0.98      inference(predicate_to_equality_rev,[status(thm)],[c_945]) ).
% 2.21/0.98  
% 2.21/0.98  cnf(c_1391,plain,
% 2.21/0.98      ( k7_relat_1(sK2,sK0) = sK2 ),
% 2.21/0.98      inference(global_propositional_subsumption,
% 2.21/0.98                [status(thm)],
% 2.21/0.98                [c_945,c_746,c_843,c_946,c_949]) ).
% 2.21/0.98  
% 2.21/0.98  cnf(c_7,plain,
% 2.21/0.98      ( ~ v1_relat_1(X0)
% 2.21/0.98      | k2_relat_1(k7_relat_1(X0,X1)) = k9_relat_1(X0,X1) ),
% 2.21/0.98      inference(cnf_transformation,[],[f44]) ).
% 2.21/0.98  
% 2.21/0.98  cnf(c_649,plain,
% 2.21/0.98      ( k2_relat_1(k7_relat_1(X0,X1)) = k9_relat_1(X0,X1)
% 2.21/0.98      | v1_relat_1(X0) != iProver_top ),
% 2.21/0.98      inference(predicate_to_equality,[status(thm)],[c_7]) ).
% 2.21/0.98  
% 2.21/0.98  cnf(c_1156,plain,
% 2.21/0.98      ( k2_relat_1(k7_relat_1(sK2,X0)) = k9_relat_1(sK2,X0) ),
% 2.21/0.98      inference(superposition,[status(thm)],[c_1151,c_649]) ).
% 2.21/0.98  
% 2.21/0.98  cnf(c_1394,plain,
% 2.21/0.98      ( k9_relat_1(sK2,sK0) = k2_relat_1(sK2) ),
% 2.21/0.98      inference(superposition,[status(thm)],[c_1391,c_1156]) ).
% 2.21/0.98  
% 2.21/0.98  cnf(c_14,plain,
% 2.21/0.98      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 2.21/0.98      | k1_relset_1(X1,X2,X0) = k1_relat_1(X0) ),
% 2.21/0.98      inference(cnf_transformation,[],[f51]) ).
% 2.21/0.98  
% 2.21/0.98  cnf(c_332,plain,
% 2.21/0.98      ( k1_relset_1(X0,X1,X2) = k1_relat_1(X2)
% 2.21/0.98      | k1_zfmisc_1(k2_zfmisc_1(X0,X1)) != k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))
% 2.21/0.98      | sK2 != X2 ),
% 2.21/0.98      inference(resolution_lifted,[status(thm)],[c_14,c_19]) ).
% 2.21/0.98  
% 2.21/0.98  cnf(c_333,plain,
% 2.21/0.98      ( k1_relset_1(X0,X1,sK2) = k1_relat_1(sK2)
% 2.21/0.98      | k1_zfmisc_1(k2_zfmisc_1(X0,X1)) != k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)) ),
% 2.21/0.98      inference(unflattening,[status(thm)],[c_332]) ).
% 2.21/0.98  
% 2.21/0.98  cnf(c_784,plain,
% 2.21/0.98      ( k1_relset_1(sK0,sK1,sK2) = k1_relat_1(sK2) ),
% 2.21/0.98      inference(equality_resolution,[status(thm)],[c_333]) ).
% 2.21/0.98  
% 2.21/0.98  cnf(c_15,plain,
% 2.21/0.98      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 2.21/0.98      | k2_relset_1(X1,X2,X0) = k2_relat_1(X0) ),
% 2.21/0.98      inference(cnf_transformation,[],[f52]) ).
% 2.21/0.98  
% 2.21/0.98  cnf(c_323,plain,
% 2.21/0.98      ( k2_relset_1(X0,X1,X2) = k2_relat_1(X2)
% 2.21/0.98      | k1_zfmisc_1(k2_zfmisc_1(X0,X1)) != k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))
% 2.21/0.98      | sK2 != X2 ),
% 2.21/0.98      inference(resolution_lifted,[status(thm)],[c_15,c_19]) ).
% 2.21/0.98  
% 2.21/0.98  cnf(c_324,plain,
% 2.21/0.98      ( k2_relset_1(X0,X1,sK2) = k2_relat_1(sK2)
% 2.21/0.98      | k1_zfmisc_1(k2_zfmisc_1(X0,X1)) != k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)) ),
% 2.21/0.98      inference(unflattening,[status(thm)],[c_323]) ).
% 2.21/0.98  
% 2.21/0.98  cnf(c_757,plain,
% 2.21/0.98      ( k2_relset_1(sK0,sK1,sK2) = k2_relat_1(sK2) ),
% 2.21/0.98      inference(equality_resolution,[status(thm)],[c_324]) ).
% 2.21/0.98  
% 2.21/0.98  cnf(c_18,negated_conjecture,
% 2.21/0.98      ( k2_relset_1(sK0,sK1,sK2) != k7_relset_1(sK0,sK1,sK2,sK0)
% 2.21/0.98      | k1_relset_1(sK0,sK1,sK2) != k8_relset_1(sK0,sK1,sK2,sK1) ),
% 2.21/0.98      inference(cnf_transformation,[],[f56]) ).
% 2.21/0.98  
% 2.21/0.98  cnf(c_809,plain,
% 2.21/0.98      ( k8_relset_1(sK0,sK1,sK2,sK1) != k1_relset_1(sK0,sK1,sK2)
% 2.21/0.98      | k7_relset_1(sK0,sK1,sK2,sK0) != k2_relat_1(sK2) ),
% 2.21/0.98      inference(demodulation,[status(thm)],[c_757,c_18]) ).
% 2.21/0.98  
% 2.21/0.98  cnf(c_859,plain,
% 2.21/0.98      ( k8_relset_1(sK0,sK1,sK2,sK1) != k1_relat_1(sK2)
% 2.21/0.98      | k7_relset_1(sK0,sK1,sK2,sK0) != k2_relat_1(sK2) ),
% 2.21/0.98      inference(demodulation,[status(thm)],[c_784,c_809]) ).
% 2.21/0.98  
% 2.21/0.98  cnf(c_17,plain,
% 2.21/0.98      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 2.21/0.98      | k8_relset_1(X1,X2,X0,X3) = k10_relat_1(X0,X3) ),
% 2.21/0.98      inference(cnf_transformation,[],[f54]) ).
% 2.21/0.98  
% 2.21/0.98  cnf(c_305,plain,
% 2.21/0.98      ( k8_relset_1(X0,X1,X2,X3) = k10_relat_1(X2,X3)
% 2.21/0.98      | k1_zfmisc_1(k2_zfmisc_1(X0,X1)) != k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))
% 2.21/0.98      | sK2 != X2 ),
% 2.21/0.98      inference(resolution_lifted,[status(thm)],[c_17,c_19]) ).
% 2.21/0.98  
% 2.21/0.98  cnf(c_306,plain,
% 2.21/0.98      ( k8_relset_1(X0,X1,sK2,X2) = k10_relat_1(sK2,X2)
% 2.21/0.98      | k1_zfmisc_1(k2_zfmisc_1(X0,X1)) != k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)) ),
% 2.21/0.98      inference(unflattening,[status(thm)],[c_305]) ).
% 2.21/0.98  
% 2.21/0.98  cnf(c_787,plain,
% 2.21/0.98      ( k8_relset_1(sK0,sK1,sK2,X0) = k10_relat_1(sK2,X0) ),
% 2.21/0.98      inference(equality_resolution,[status(thm)],[c_306]) ).
% 2.21/0.98  
% 2.21/0.98  cnf(c_16,plain,
% 2.21/0.98      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 2.21/0.98      | k7_relset_1(X1,X2,X0,X3) = k9_relat_1(X0,X3) ),
% 2.21/0.98      inference(cnf_transformation,[],[f53]) ).
% 2.21/0.98  
% 2.21/0.98  cnf(c_314,plain,
% 2.21/0.98      ( k7_relset_1(X0,X1,X2,X3) = k9_relat_1(X2,X3)
% 2.21/0.98      | k1_zfmisc_1(k2_zfmisc_1(X0,X1)) != k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))
% 2.21/0.98      | sK2 != X2 ),
% 2.21/0.98      inference(resolution_lifted,[status(thm)],[c_16,c_19]) ).
% 2.21/0.98  
% 2.21/0.98  cnf(c_315,plain,
% 2.21/0.98      ( k7_relset_1(X0,X1,sK2,X2) = k9_relat_1(sK2,X2)
% 2.21/0.98      | k1_zfmisc_1(k2_zfmisc_1(X0,X1)) != k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)) ),
% 2.21/0.98      inference(unflattening,[status(thm)],[c_314]) ).
% 2.21/0.98  
% 2.21/0.98  cnf(c_806,plain,
% 2.21/0.98      ( k7_relset_1(sK0,sK1,sK2,X0) = k9_relat_1(sK2,X0) ),
% 2.21/0.98      inference(equality_resolution,[status(thm)],[c_315]) ).
% 2.21/0.98  
% 2.21/0.98  cnf(c_1258,plain,
% 2.21/0.98      ( k10_relat_1(sK2,sK1) != k1_relat_1(sK2)
% 2.21/0.98      | k9_relat_1(sK2,sK0) != k2_relat_1(sK2) ),
% 2.21/0.98      inference(demodulation,[status(thm)],[c_859,c_787,c_806]) ).
% 2.21/0.98  
% 2.21/0.98  cnf(contradiction,plain,
% 2.21/0.98      ( $false ),
% 2.21/0.98      inference(minisat,[status(thm)],[c_1962,c_1394,c_1258]) ).
% 2.21/0.98  
% 2.21/0.98  
% 2.21/0.98  % SZS output end CNFRefutation for theBenchmark.p
% 2.21/0.98  
% 2.21/0.98  ------                               Statistics
% 2.21/0.98  
% 2.21/0.98  ------ General
% 2.21/0.98  
% 2.21/0.98  abstr_ref_over_cycles:                  0
% 2.21/0.98  abstr_ref_under_cycles:                 0
% 2.21/0.98  gc_basic_clause_elim:                   0
% 2.21/0.98  forced_gc_time:                         0
% 2.21/0.98  parsing_time:                           0.013
% 2.21/0.98  unif_index_cands_time:                  0.
% 2.21/0.98  unif_index_add_time:                    0.
% 2.21/0.98  orderings_time:                         0.
% 2.21/0.98  out_proof_time:                         0.013
% 2.21/0.98  total_time:                             0.106
% 2.21/0.98  num_of_symbols:                         50
% 2.21/0.98  num_of_terms:                           1450
% 2.21/0.98  
% 2.21/0.98  ------ Preprocessing
% 2.21/0.98  
% 2.21/0.98  num_of_splits:                          0
% 2.21/0.98  num_of_split_atoms:                     0
% 2.21/0.98  num_of_reused_defs:                     0
% 2.21/0.98  num_eq_ax_congr_red:                    14
% 2.21/0.98  num_of_sem_filtered_clauses:            1
% 2.21/0.98  num_of_subtypes:                        0
% 2.21/0.98  monotx_restored_types:                  0
% 2.21/0.98  sat_num_of_epr_types:                   0
% 2.21/0.98  sat_num_of_non_cyclic_types:            0
% 2.21/0.98  sat_guarded_non_collapsed_types:        0
% 2.21/0.98  num_pure_diseq_elim:                    0
% 2.21/0.98  simp_replaced_by:                       0
% 2.21/0.98  res_preprocessed:                       95
% 2.21/0.98  prep_upred:                             0
% 2.21/0.98  prep_unflattend:                        7
% 2.21/0.98  smt_new_axioms:                         0
% 2.21/0.98  pred_elim_cands:                        2
% 2.21/0.98  pred_elim:                              3
% 2.21/0.98  pred_elim_cl:                           4
% 2.21/0.98  pred_elim_cycles:                       5
% 2.21/0.98  merged_defs:                            0
% 2.21/0.98  merged_defs_ncl:                        0
% 2.21/0.98  bin_hyper_res:                          0
% 2.21/0.98  prep_cycles:                            4
% 2.21/0.98  pred_elim_time:                         0.002
% 2.21/0.98  splitting_time:                         0.
% 2.21/0.98  sem_filter_time:                        0.
% 2.21/0.98  monotx_time:                            0.001
% 2.21/0.98  subtype_inf_time:                       0.
% 2.21/0.98  
% 2.21/0.98  ------ Problem properties
% 2.21/0.98  
% 2.21/0.98  clauses:                                15
% 2.21/0.98  conjectures:                            1
% 2.21/0.98  epr:                                    2
% 2.21/0.98  horn:                                   15
% 2.21/0.98  ground:                                 1
% 2.21/0.98  unary:                                  2
% 2.21/0.98  binary:                                 8
% 2.21/0.98  lits:                                   33
% 2.21/0.98  lits_eq:                                17
% 2.21/0.98  fd_pure:                                0
% 2.21/0.98  fd_pseudo:                              0
% 2.21/0.98  fd_cond:                                0
% 2.21/0.98  fd_pseudo_cond:                         1
% 2.21/0.98  ac_symbols:                             0
% 2.21/0.98  
% 2.21/0.98  ------ Propositional Solver
% 2.21/0.98  
% 2.21/0.98  prop_solver_calls:                      27
% 2.21/0.98  prop_fast_solver_calls:                 557
% 2.21/0.98  smt_solver_calls:                       0
% 2.21/0.98  smt_fast_solver_calls:                  0
% 2.21/0.98  prop_num_of_clauses:                    625
% 2.21/0.98  prop_preprocess_simplified:             3029
% 2.21/0.98  prop_fo_subsumed:                       6
% 2.21/0.98  prop_solver_time:                       0.
% 2.21/0.98  smt_solver_time:                        0.
% 2.21/0.98  smt_fast_solver_time:                   0.
% 2.21/0.98  prop_fast_solver_time:                  0.
% 2.21/0.98  prop_unsat_core_time:                   0.
% 2.21/0.98  
% 2.21/0.98  ------ QBF
% 2.21/0.98  
% 2.21/0.98  qbf_q_res:                              0
% 2.21/0.98  qbf_num_tautologies:                    0
% 2.21/0.98  qbf_prep_cycles:                        0
% 2.21/0.98  
% 2.21/0.98  ------ BMC1
% 2.21/0.98  
% 2.21/0.98  bmc1_current_bound:                     -1
% 2.21/0.98  bmc1_last_solved_bound:                 -1
% 2.21/0.98  bmc1_unsat_core_size:                   -1
% 2.21/0.98  bmc1_unsat_core_parents_size:           -1
% 2.21/0.98  bmc1_merge_next_fun:                    0
% 2.21/0.98  bmc1_unsat_core_clauses_time:           0.
% 2.21/0.98  
% 2.21/0.98  ------ Instantiation
% 2.21/0.98  
% 2.21/0.98  inst_num_of_clauses:                    210
% 2.21/0.98  inst_num_in_passive:                    5
% 2.21/0.98  inst_num_in_active:                     163
% 2.21/0.98  inst_num_in_unprocessed:                42
% 2.21/0.98  inst_num_of_loops:                      170
% 2.21/0.98  inst_num_of_learning_restarts:          0
% 2.21/0.98  inst_num_moves_active_passive:          4
% 2.21/0.98  inst_lit_activity:                      0
% 2.21/0.98  inst_lit_activity_moves:                0
% 2.21/0.98  inst_num_tautologies:                   0
% 2.21/0.98  inst_num_prop_implied:                  0
% 2.21/0.98  inst_num_existing_simplified:           0
% 2.21/0.98  inst_num_eq_res_simplified:             0
% 2.21/0.98  inst_num_child_elim:                    0
% 2.21/0.98  inst_num_of_dismatching_blockings:      41
% 2.21/0.98  inst_num_of_non_proper_insts:           303
% 2.21/0.98  inst_num_of_duplicates:                 0
% 2.21/0.98  inst_inst_num_from_inst_to_res:         0
% 2.21/0.98  inst_dismatching_checking_time:         0.
% 2.21/0.98  
% 2.21/0.98  ------ Resolution
% 2.21/0.98  
% 2.21/0.98  res_num_of_clauses:                     0
% 2.21/0.98  res_num_in_passive:                     0
% 2.21/0.98  res_num_in_active:                      0
% 2.21/0.98  res_num_of_loops:                       99
% 2.21/0.98  res_forward_subset_subsumed:            71
% 2.21/0.98  res_backward_subset_subsumed:           2
% 2.21/0.98  res_forward_subsumed:                   0
% 2.21/0.98  res_backward_subsumed:                  0
% 2.21/0.98  res_forward_subsumption_resolution:     0
% 2.21/0.98  res_backward_subsumption_resolution:    0
% 2.21/0.98  res_clause_to_clause_subsumption:       83
% 2.21/0.98  res_orphan_elimination:                 0
% 2.21/0.98  res_tautology_del:                      43
% 2.21/0.98  res_num_eq_res_simplified:              0
% 2.21/0.98  res_num_sel_changes:                    0
% 2.21/0.98  res_moves_from_active_to_pass:          0
% 2.21/0.98  
% 2.21/0.98  ------ Superposition
% 2.21/0.98  
% 2.21/0.98  sup_time_total:                         0.
% 2.21/0.98  sup_time_generating:                    0.
% 2.21/0.98  sup_time_sim_full:                      0.
% 2.21/0.98  sup_time_sim_immed:                     0.
% 2.21/0.98  
% 2.21/0.98  sup_num_of_clauses:                     38
% 2.21/0.98  sup_num_in_active:                      31
% 2.21/0.98  sup_num_in_passive:                     7
% 2.21/0.98  sup_num_of_loops:                       33
% 2.21/0.98  sup_fw_superposition:                   19
% 2.21/0.98  sup_bw_superposition:                   8
% 2.21/0.98  sup_immediate_simplified:               7
% 2.21/0.98  sup_given_eliminated:                   0
% 2.21/0.98  comparisons_done:                       0
% 2.21/0.98  comparisons_avoided:                    0
% 2.21/0.98  
% 2.21/0.98  ------ Simplifications
% 2.21/0.98  
% 2.21/0.98  
% 2.21/0.98  sim_fw_subset_subsumed:                 2
% 2.21/0.98  sim_bw_subset_subsumed:                 0
% 2.21/0.98  sim_fw_subsumed:                        3
% 2.21/0.98  sim_bw_subsumed:                        0
% 2.21/0.98  sim_fw_subsumption_res:                 0
% 2.21/0.98  sim_bw_subsumption_res:                 0
% 2.21/0.98  sim_tautology_del:                      0
% 2.21/0.98  sim_eq_tautology_del:                   1
% 2.21/0.98  sim_eq_res_simp:                        1
% 2.21/0.98  sim_fw_demodulated:                     1
% 2.21/0.98  sim_bw_demodulated:                     3
% 2.21/0.98  sim_light_normalised:                   3
% 2.21/0.98  sim_joinable_taut:                      0
% 2.21/0.98  sim_joinable_simp:                      0
% 2.21/0.98  sim_ac_normalised:                      0
% 2.21/0.98  sim_smt_subsumption:                    0
% 2.21/0.98  
%------------------------------------------------------------------------------
