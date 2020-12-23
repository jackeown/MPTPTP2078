%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n007.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 11:56:13 EST 2020

% Result     : Theorem 2.82s
% Output     : CNFRefutation 2.82s
% Verified   : 
% Statistics : Number of formulae       :  148 ( 879 expanded)
%              Number of clauses        :   89 ( 401 expanded)
%              Number of leaves         :   19 ( 174 expanded)
%              Depth                    :   19
%              Number of atoms          :  336 (2252 expanded)
%              Number of equality atoms :  181 (1012 expanded)
%              Maximal formula depth    :    8 (   4 average)
%              Maximal clause size      :    6 (   2 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f2,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(X0))
         => v1_relat_1(X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f19,plain,(
    ! [X0] :
      ( ! [X1] :
          ( v1_relat_1(X1)
          | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f43,plain,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f17,conjecture,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
     => ( k1_relset_1(X1,X0,X2) = k8_relset_1(X1,X0,X2,k7_relset_1(X1,X0,X2,X1))
        & k2_relset_1(X1,X0,X2) = k7_relset_1(X1,X0,X2,k8_relset_1(X1,X0,X2,X0)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f18,negated_conjecture,(
    ~ ! [X0,X1,X2] :
        ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
       => ( k1_relset_1(X1,X0,X2) = k8_relset_1(X1,X0,X2,k7_relset_1(X1,X0,X2,X1))
          & k2_relset_1(X1,X0,X2) = k7_relset_1(X1,X0,X2,k8_relset_1(X1,X0,X2,X0)) ) ) ),
    inference(negated_conjecture,[],[f17])).

fof(f34,plain,(
    ? [X0,X1,X2] :
      ( ( k1_relset_1(X1,X0,X2) != k8_relset_1(X1,X0,X2,k7_relset_1(X1,X0,X2,X1))
        | k2_relset_1(X1,X0,X2) != k7_relset_1(X1,X0,X2,k8_relset_1(X1,X0,X2,X0)) )
      & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) ) ),
    inference(ennf_transformation,[],[f18])).

fof(f38,plain,
    ( ? [X0,X1,X2] :
        ( ( k1_relset_1(X1,X0,X2) != k8_relset_1(X1,X0,X2,k7_relset_1(X1,X0,X2,X1))
          | k2_relset_1(X1,X0,X2) != k7_relset_1(X1,X0,X2,k8_relset_1(X1,X0,X2,X0)) )
        & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) )
   => ( ( k1_relset_1(sK1,sK0,sK2) != k8_relset_1(sK1,sK0,sK2,k7_relset_1(sK1,sK0,sK2,sK1))
        | k2_relset_1(sK1,sK0,sK2) != k7_relset_1(sK1,sK0,sK2,k8_relset_1(sK1,sK0,sK2,sK0)) )
      & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) ) ),
    introduced(choice_axiom,[])).

fof(f39,plain,
    ( ( k1_relset_1(sK1,sK0,sK2) != k8_relset_1(sK1,sK0,sK2,k7_relset_1(sK1,sK0,sK2,sK1))
      | k2_relset_1(sK1,sK0,sK2) != k7_relset_1(sK1,sK0,sK2,k8_relset_1(sK1,sK0,sK2,sK0)) )
    & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f34,f38])).

fof(f61,plain,(
    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) ),
    inference(cnf_transformation,[],[f39])).

fof(f5,axiom,(
    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f47,plain,(
    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1)) ),
    inference(cnf_transformation,[],[f5])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( X0 = X1
    <=> ( r1_tarski(X1,X0)
        & r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f35,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(nnf_transformation,[],[f1])).

fof(f36,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(flattening,[],[f35])).

fof(f41,plain,(
    ! [X0,X1] :
      ( r1_tarski(X1,X0)
      | X0 != X1 ) ),
    inference(cnf_transformation,[],[f36])).

fof(f63,plain,(
    ! [X1] : r1_tarski(X1,X1) ),
    inference(equality_resolution,[],[f41])).

fof(f11,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ( r1_tarski(k1_relat_1(X1),X0)
       => k7_relat_1(X1,X0) = X1 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f27,plain,(
    ! [X0,X1] :
      ( k7_relat_1(X1,X0) = X1
      | ~ r1_tarski(k1_relat_1(X1),X0)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f28,plain,(
    ! [X0,X1] :
      ( k7_relat_1(X1,X0) = X1
      | ~ r1_tarski(k1_relat_1(X1),X0)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f27])).

fof(f54,plain,(
    ! [X0,X1] :
      ( k7_relat_1(X1,X0) = X1
      | ~ r1_tarski(k1_relat_1(X1),X0)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f6,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => k2_relat_1(k7_relat_1(X1,X0)) = k9_relat_1(X1,X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f21,plain,(
    ! [X0,X1] :
      ( k2_relat_1(k7_relat_1(X1,X0)) = k9_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f48,plain,(
    ! [X0,X1] :
      ( k2_relat_1(k7_relat_1(X1,X0)) = k9_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f12,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => ( v5_relat_1(X2,X1)
        & v4_relat_1(X2,X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f29,plain,(
    ! [X0,X1,X2] :
      ( ( v5_relat_1(X2,X1)
        & v4_relat_1(X2,X0) )
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f55,plain,(
    ! [X2,X0,X1] :
      ( v4_relat_1(X2,X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f8,axiom,(
    ! [X0,X1] :
      ( ( v4_relat_1(X1,X0)
        & v1_relat_1(X1) )
     => k7_relat_1(X1,X0) = X1 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f23,plain,(
    ! [X0,X1] :
      ( k7_relat_1(X1,X0) = X1
      | ~ v4_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f24,plain,(
    ! [X0,X1] :
      ( k7_relat_1(X1,X0) = X1
      | ~ v4_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f23])).

fof(f50,plain,(
    ! [X0,X1] :
      ( k7_relat_1(X1,X0) = X1
      | ~ v4_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f10,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ( r1_tarski(k2_relat_1(X1),X0)
       => k5_relat_1(X1,k6_relat_1(X0)) = X1 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f25,plain,(
    ! [X0,X1] :
      ( k5_relat_1(X1,k6_relat_1(X0)) = X1
      | ~ r1_tarski(k2_relat_1(X1),X0)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f26,plain,(
    ! [X0,X1] :
      ( k5_relat_1(X1,k6_relat_1(X0)) = X1
      | ~ r1_tarski(k2_relat_1(X1),X0)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f25])).

fof(f53,plain,(
    ! [X0,X1] :
      ( k5_relat_1(X1,k6_relat_1(X0)) = X1
      | ~ r1_tarski(k2_relat_1(X1),X0)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f4,axiom,(
    ! [X0] : v1_relat_1(k6_relat_1(X0)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f46,plain,(
    ! [X0] : v1_relat_1(k6_relat_1(X0)) ),
    inference(cnf_transformation,[],[f4])).

fof(f7,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( v1_relat_1(X1)
         => k1_relat_1(k5_relat_1(X0,X1)) = k10_relat_1(X0,k1_relat_1(X1)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f22,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k1_relat_1(k5_relat_1(X0,X1)) = k10_relat_1(X0,k1_relat_1(X1))
          | ~ v1_relat_1(X1) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f49,plain,(
    ! [X0,X1] :
      ( k1_relat_1(k5_relat_1(X0,X1)) = k10_relat_1(X0,k1_relat_1(X1))
      | ~ v1_relat_1(X1)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f9,axiom,(
    ! [X0] :
      ( k2_relat_1(k6_relat_1(X0)) = X0
      & k1_relat_1(k6_relat_1(X0)) = X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f51,plain,(
    ! [X0] : k1_relat_1(k6_relat_1(X0)) = X0 ),
    inference(cnf_transformation,[],[f9])).

fof(f56,plain,(
    ! [X2,X0,X1] :
      ( v5_relat_1(X2,X1)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ( v5_relat_1(X1,X0)
      <=> r1_tarski(k2_relat_1(X1),X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f20,plain,(
    ! [X0,X1] :
      ( ( v5_relat_1(X1,X0)
      <=> r1_tarski(k2_relat_1(X1),X0) )
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f37,plain,(
    ! [X0,X1] :
      ( ( ( v5_relat_1(X1,X0)
          | ~ r1_tarski(k2_relat_1(X1),X0) )
        & ( r1_tarski(k2_relat_1(X1),X0)
          | ~ v5_relat_1(X1,X0) ) )
      | ~ v1_relat_1(X1) ) ),
    inference(nnf_transformation,[],[f20])).

fof(f44,plain,(
    ! [X0,X1] :
      ( r1_tarski(k2_relat_1(X1),X0)
      | ~ v5_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f37])).

fof(f13,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k1_relat_1(X2) = k1_relset_1(X0,X1,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f30,plain,(
    ! [X0,X1,X2] :
      ( k1_relat_1(X2) = k1_relset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f57,plain,(
    ! [X2,X0,X1] :
      ( k1_relat_1(X2) = k1_relset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f14,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k2_relat_1(X2) = k2_relset_1(X0,X1,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f31,plain,(
    ! [X0,X1,X2] :
      ( k2_relat_1(X2) = k2_relset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f58,plain,(
    ! [X2,X0,X1] :
      ( k2_relat_1(X2) = k2_relset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f62,plain,
    ( k1_relset_1(sK1,sK0,sK2) != k8_relset_1(sK1,sK0,sK2,k7_relset_1(sK1,sK0,sK2,sK1))
    | k2_relset_1(sK1,sK0,sK2) != k7_relset_1(sK1,sK0,sK2,k8_relset_1(sK1,sK0,sK2,sK0)) ),
    inference(cnf_transformation,[],[f39])).

fof(f16,axiom,(
    ! [X0,X1,X2,X3] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k10_relat_1(X2,X3) = k8_relset_1(X0,X1,X2,X3) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f33,plain,(
    ! [X0,X1,X2,X3] :
      ( k10_relat_1(X2,X3) = k8_relset_1(X0,X1,X2,X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f16])).

fof(f60,plain,(
    ! [X2,X0,X3,X1] :
      ( k10_relat_1(X2,X3) = k8_relset_1(X0,X1,X2,X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f33])).

fof(f15,axiom,(
    ! [X0,X1,X2,X3] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k9_relat_1(X2,X3) = k7_relset_1(X0,X1,X2,X3) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f32,plain,(
    ! [X0,X1,X2,X3] :
      ( k9_relat_1(X2,X3) = k7_relset_1(X0,X1,X2,X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f15])).

fof(f59,plain,(
    ! [X2,X0,X3,X1] :
      ( k9_relat_1(X2,X3) = k7_relset_1(X0,X1,X2,X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f32])).

cnf(c_3,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | ~ v1_relat_1(X1)
    | v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f43])).

cnf(c_22,negated_conjecture,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) ),
    inference(cnf_transformation,[],[f61])).

cnf(c_275,plain,
    ( ~ v1_relat_1(X0)
    | v1_relat_1(X1)
    | k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)) != k1_zfmisc_1(X0)
    | sK2 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_3,c_22])).

cnf(c_276,plain,
    ( ~ v1_relat_1(X0)
    | v1_relat_1(sK2)
    | k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)) != k1_zfmisc_1(X0) ),
    inference(unflattening,[status(thm)],[c_275])).

cnf(c_677,plain,
    ( k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)) != k1_zfmisc_1(X0)
    | v1_relat_1(X0) != iProver_top
    | v1_relat_1(sK2) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_276])).

cnf(c_461,plain,
    ( X0 = X0 ),
    theory(equality)).

cnf(c_796,plain,
    ( k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)) = k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)) ),
    inference(instantiation,[status(thm)],[c_461])).

cnf(c_786,plain,
    ( ~ v1_relat_1(k2_zfmisc_1(X0,X1))
    | v1_relat_1(sK2)
    | k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)) != k1_zfmisc_1(k2_zfmisc_1(X0,X1)) ),
    inference(instantiation,[status(thm)],[c_276])).

cnf(c_931,plain,
    ( ~ v1_relat_1(k2_zfmisc_1(sK1,sK0))
    | v1_relat_1(sK2)
    | k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)) != k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)) ),
    inference(instantiation,[status(thm)],[c_786])).

cnf(c_932,plain,
    ( k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)) != k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))
    | v1_relat_1(k2_zfmisc_1(sK1,sK0)) != iProver_top
    | v1_relat_1(sK2) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_931])).

cnf(c_7,plain,
    ( v1_relat_1(k2_zfmisc_1(X0,X1)) ),
    inference(cnf_transformation,[],[f47])).

cnf(c_1067,plain,
    ( v1_relat_1(k2_zfmisc_1(sK1,sK0)) ),
    inference(instantiation,[status(thm)],[c_7])).

cnf(c_1068,plain,
    ( v1_relat_1(k2_zfmisc_1(sK1,sK0)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1067])).

cnf(c_1217,plain,
    ( v1_relat_1(sK2) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_677,c_796,c_932,c_1068])).

cnf(c_1,plain,
    ( r1_tarski(X0,X0) ),
    inference(cnf_transformation,[],[f63])).

cnf(c_684,plain,
    ( r1_tarski(X0,X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1])).

cnf(c_14,plain,
    ( ~ r1_tarski(k1_relat_1(X0),X1)
    | ~ v1_relat_1(X0)
    | k7_relat_1(X0,X1) = X0 ),
    inference(cnf_transformation,[],[f54])).

cnf(c_678,plain,
    ( k7_relat_1(X0,X1) = X0
    | r1_tarski(k1_relat_1(X0),X1) != iProver_top
    | v1_relat_1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_14])).

cnf(c_1479,plain,
    ( k7_relat_1(X0,k1_relat_1(X0)) = X0
    | v1_relat_1(X0) != iProver_top ),
    inference(superposition,[status(thm)],[c_684,c_678])).

cnf(c_4053,plain,
    ( k7_relat_1(sK2,k1_relat_1(sK2)) = sK2 ),
    inference(superposition,[status(thm)],[c_1217,c_1479])).

cnf(c_8,plain,
    ( ~ v1_relat_1(X0)
    | k2_relat_1(k7_relat_1(X0,X1)) = k9_relat_1(X0,X1) ),
    inference(cnf_transformation,[],[f48])).

cnf(c_681,plain,
    ( k2_relat_1(k7_relat_1(X0,X1)) = k9_relat_1(X0,X1)
    | v1_relat_1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_8])).

cnf(c_1551,plain,
    ( k2_relat_1(k7_relat_1(sK2,X0)) = k9_relat_1(sK2,X0) ),
    inference(superposition,[status(thm)],[c_1217,c_681])).

cnf(c_4222,plain,
    ( k9_relat_1(sK2,k1_relat_1(sK2)) = k2_relat_1(sK2) ),
    inference(superposition,[status(thm)],[c_4053,c_1551])).

cnf(c_16,plain,
    ( v4_relat_1(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) ),
    inference(cnf_transformation,[],[f55])).

cnf(c_10,plain,
    ( ~ v4_relat_1(X0,X1)
    | ~ v1_relat_1(X0)
    | k7_relat_1(X0,X1) = X0 ),
    inference(cnf_transformation,[],[f50])).

cnf(c_238,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ v1_relat_1(X0)
    | k7_relat_1(X0,X1) = X0 ),
    inference(resolution,[status(thm)],[c_16,c_10])).

cnf(c_305,plain,
    ( ~ v1_relat_1(X0)
    | k7_relat_1(X0,X1) = X0
    | k1_zfmisc_1(k2_zfmisc_1(X1,X2)) != k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))
    | sK2 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_238,c_22])).

cnf(c_306,plain,
    ( ~ v1_relat_1(sK2)
    | k7_relat_1(sK2,X0) = sK2
    | k1_zfmisc_1(k2_zfmisc_1(X0,X1)) != k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)) ),
    inference(unflattening,[status(thm)],[c_305])).

cnf(c_675,plain,
    ( k7_relat_1(sK2,X0) = sK2
    | k1_zfmisc_1(k2_zfmisc_1(X0,X1)) != k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))
    | v1_relat_1(sK2) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_306])).

cnf(c_975,plain,
    ( k7_relat_1(sK2,sK1) = sK2
    | v1_relat_1(sK2) != iProver_top ),
    inference(equality_resolution,[status(thm)],[c_675])).

cnf(c_976,plain,
    ( ~ v1_relat_1(sK2)
    | k7_relat_1(sK2,sK1) = sK2 ),
    inference(predicate_to_equality_rev,[status(thm)],[c_975])).

cnf(c_1399,plain,
    ( k7_relat_1(sK2,sK1) = sK2 ),
    inference(global_propositional_subsumption,[status(thm)],[c_975,c_796,c_931,c_976,c_1067])).

cnf(c_13,plain,
    ( ~ r1_tarski(k2_relat_1(X0),X1)
    | ~ v1_relat_1(X0)
    | k5_relat_1(X0,k6_relat_1(X1)) = X0 ),
    inference(cnf_transformation,[],[f53])).

cnf(c_679,plain,
    ( k5_relat_1(X0,k6_relat_1(X1)) = X0
    | r1_tarski(k2_relat_1(X0),X1) != iProver_top
    | v1_relat_1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_13])).

cnf(c_1869,plain,
    ( k5_relat_1(k7_relat_1(sK2,X0),k6_relat_1(X1)) = k7_relat_1(sK2,X0)
    | r1_tarski(k9_relat_1(sK2,X0),X1) != iProver_top
    | v1_relat_1(k7_relat_1(sK2,X0)) != iProver_top ),
    inference(superposition,[status(thm)],[c_1551,c_679])).

cnf(c_2802,plain,
    ( k5_relat_1(k7_relat_1(sK2,X0),k6_relat_1(k9_relat_1(sK2,X0))) = k7_relat_1(sK2,X0)
    | v1_relat_1(k7_relat_1(sK2,X0)) != iProver_top ),
    inference(superposition,[status(thm)],[c_684,c_1869])).

cnf(c_2887,plain,
    ( k5_relat_1(k7_relat_1(sK2,sK1),k6_relat_1(k9_relat_1(sK2,sK1))) = k7_relat_1(sK2,sK1)
    | v1_relat_1(sK2) != iProver_top ),
    inference(superposition,[status(thm)],[c_1399,c_2802])).

cnf(c_1868,plain,
    ( k9_relat_1(sK2,sK1) = k2_relat_1(sK2) ),
    inference(superposition,[status(thm)],[c_1399,c_1551])).

cnf(c_2888,plain,
    ( k5_relat_1(sK2,k6_relat_1(k2_relat_1(sK2))) = sK2
    | v1_relat_1(sK2) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_2887,c_1399,c_1868])).

cnf(c_2936,plain,
    ( k5_relat_1(sK2,k6_relat_1(k2_relat_1(sK2))) = sK2 ),
    inference(global_propositional_subsumption,[status(thm)],[c_2888,c_796,c_932,c_1068])).

cnf(c_6,plain,
    ( v1_relat_1(k6_relat_1(X0)) ),
    inference(cnf_transformation,[],[f46])).

cnf(c_683,plain,
    ( v1_relat_1(k6_relat_1(X0)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_6])).

cnf(c_9,plain,
    ( ~ v1_relat_1(X0)
    | ~ v1_relat_1(X1)
    | k10_relat_1(X0,k1_relat_1(X1)) = k1_relat_1(k5_relat_1(X0,X1)) ),
    inference(cnf_transformation,[],[f49])).

cnf(c_680,plain,
    ( k10_relat_1(X0,k1_relat_1(X1)) = k1_relat_1(k5_relat_1(X0,X1))
    | v1_relat_1(X0) != iProver_top
    | v1_relat_1(X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_9])).

cnf(c_1664,plain,
    ( k10_relat_1(sK2,k1_relat_1(X0)) = k1_relat_1(k5_relat_1(sK2,X0))
    | v1_relat_1(X0) != iProver_top ),
    inference(superposition,[status(thm)],[c_1217,c_680])).

cnf(c_1884,plain,
    ( k10_relat_1(sK2,k1_relat_1(k6_relat_1(X0))) = k1_relat_1(k5_relat_1(sK2,k6_relat_1(X0))) ),
    inference(superposition,[status(thm)],[c_683,c_1664])).

cnf(c_12,plain,
    ( k1_relat_1(k6_relat_1(X0)) = X0 ),
    inference(cnf_transformation,[],[f51])).

cnf(c_1892,plain,
    ( k1_relat_1(k5_relat_1(sK2,k6_relat_1(X0))) = k10_relat_1(sK2,X0) ),
    inference(light_normalisation,[status(thm)],[c_1884,c_12])).

cnf(c_2939,plain,
    ( k10_relat_1(sK2,k2_relat_1(sK2)) = k1_relat_1(sK2) ),
    inference(superposition,[status(thm)],[c_2936,c_1892])).

cnf(c_15,plain,
    ( v5_relat_1(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) ),
    inference(cnf_transformation,[],[f56])).

cnf(c_5,plain,
    ( ~ v5_relat_1(X0,X1)
    | r1_tarski(k2_relat_1(X0),X1)
    | ~ v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f44])).

cnf(c_256,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | r1_tarski(k2_relat_1(X0),X2)
    | ~ v1_relat_1(X0) ),
    inference(resolution,[status(thm)],[c_15,c_5])).

cnf(c_290,plain,
    ( r1_tarski(k2_relat_1(X0),X1)
    | ~ v1_relat_1(X0)
    | k1_zfmisc_1(k2_zfmisc_1(X2,X1)) != k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))
    | sK2 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_256,c_22])).

cnf(c_291,plain,
    ( r1_tarski(k2_relat_1(sK2),X0)
    | ~ v1_relat_1(sK2)
    | k1_zfmisc_1(k2_zfmisc_1(X1,X0)) != k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)) ),
    inference(unflattening,[status(thm)],[c_290])).

cnf(c_676,plain,
    ( k1_zfmisc_1(k2_zfmisc_1(X0,X1)) != k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))
    | r1_tarski(k2_relat_1(sK2),X1) = iProver_top
    | v1_relat_1(sK2) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_291])).

cnf(c_292,plain,
    ( k1_zfmisc_1(k2_zfmisc_1(X0,X1)) != k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))
    | r1_tarski(k2_relat_1(sK2),X1) = iProver_top
    | v1_relat_1(sK2) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_291])).

cnf(c_1302,plain,
    ( r1_tarski(k2_relat_1(sK2),X1) = iProver_top
    | k1_zfmisc_1(k2_zfmisc_1(X0,X1)) != k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_676,c_292,c_796,c_932,c_1068])).

cnf(c_1303,plain,
    ( k1_zfmisc_1(k2_zfmisc_1(X0,X1)) != k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))
    | r1_tarski(k2_relat_1(sK2),X1) = iProver_top ),
    inference(renaming,[status(thm)],[c_1302])).

cnf(c_1310,plain,
    ( r1_tarski(k2_relat_1(sK2),sK0) = iProver_top ),
    inference(equality_resolution,[status(thm)],[c_1303])).

cnf(c_1635,plain,
    ( k5_relat_1(sK2,k6_relat_1(sK0)) = sK2
    | v1_relat_1(sK2) != iProver_top ),
    inference(superposition,[status(thm)],[c_1310,c_679])).

cnf(c_1311,plain,
    ( r1_tarski(k2_relat_1(sK2),sK0) ),
    inference(predicate_to_equality_rev,[status(thm)],[c_1310])).

cnf(c_1406,plain,
    ( ~ r1_tarski(k2_relat_1(sK2),X0)
    | ~ v1_relat_1(sK2)
    | k5_relat_1(sK2,k6_relat_1(X0)) = sK2 ),
    inference(instantiation,[status(thm)],[c_13])).

cnf(c_1419,plain,
    ( ~ r1_tarski(k2_relat_1(sK2),sK0)
    | ~ v1_relat_1(sK2)
    | k5_relat_1(sK2,k6_relat_1(sK0)) = sK2 ),
    inference(instantiation,[status(thm)],[c_1406])).

cnf(c_2304,plain,
    ( k5_relat_1(sK2,k6_relat_1(sK0)) = sK2 ),
    inference(global_propositional_subsumption,[status(thm)],[c_1635,c_796,c_931,c_1067,c_1311,c_1419])).

cnf(c_2544,plain,
    ( k10_relat_1(sK2,sK0) = k1_relat_1(sK2) ),
    inference(superposition,[status(thm)],[c_2304,c_1892])).

cnf(c_17,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k1_relset_1(X1,X2,X0) = k1_relat_1(X0) ),
    inference(cnf_transformation,[],[f57])).

cnf(c_347,plain,
    ( k1_relset_1(X0,X1,X2) = k1_relat_1(X2)
    | k1_zfmisc_1(k2_zfmisc_1(X0,X1)) != k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))
    | sK2 != X2 ),
    inference(resolution_lifted,[status(thm)],[c_17,c_22])).

cnf(c_348,plain,
    ( k1_relset_1(X0,X1,sK2) = k1_relat_1(sK2)
    | k1_zfmisc_1(k2_zfmisc_1(X0,X1)) != k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)) ),
    inference(unflattening,[status(thm)],[c_347])).

cnf(c_835,plain,
    ( k1_relset_1(sK1,sK0,sK2) = k1_relat_1(sK2) ),
    inference(equality_resolution,[status(thm)],[c_348])).

cnf(c_18,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k2_relset_1(X1,X2,X0) = k2_relat_1(X0) ),
    inference(cnf_transformation,[],[f58])).

cnf(c_338,plain,
    ( k2_relset_1(X0,X1,X2) = k2_relat_1(X2)
    | k1_zfmisc_1(k2_zfmisc_1(X0,X1)) != k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))
    | sK2 != X2 ),
    inference(resolution_lifted,[status(thm)],[c_18,c_22])).

cnf(c_339,plain,
    ( k2_relset_1(X0,X1,sK2) = k2_relat_1(sK2)
    | k1_zfmisc_1(k2_zfmisc_1(X0,X1)) != k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)) ),
    inference(unflattening,[status(thm)],[c_338])).

cnf(c_795,plain,
    ( k2_relset_1(sK1,sK0,sK2) = k2_relat_1(sK2) ),
    inference(equality_resolution,[status(thm)],[c_339])).

cnf(c_21,negated_conjecture,
    ( k2_relset_1(sK1,sK0,sK2) != k7_relset_1(sK1,sK0,sK2,k8_relset_1(sK1,sK0,sK2,sK0))
    | k1_relset_1(sK1,sK0,sK2) != k8_relset_1(sK1,sK0,sK2,k7_relset_1(sK1,sK0,sK2,sK1)) ),
    inference(cnf_transformation,[],[f62])).

cnf(c_874,plain,
    ( k8_relset_1(sK1,sK0,sK2,k7_relset_1(sK1,sK0,sK2,sK1)) != k1_relset_1(sK1,sK0,sK2)
    | k7_relset_1(sK1,sK0,sK2,k8_relset_1(sK1,sK0,sK2,sK0)) != k2_relat_1(sK2) ),
    inference(demodulation,[status(thm)],[c_795,c_21])).

cnf(c_910,plain,
    ( k8_relset_1(sK1,sK0,sK2,k7_relset_1(sK1,sK0,sK2,sK1)) != k1_relat_1(sK2)
    | k7_relset_1(sK1,sK0,sK2,k8_relset_1(sK1,sK0,sK2,sK0)) != k2_relat_1(sK2) ),
    inference(demodulation,[status(thm)],[c_835,c_874])).

cnf(c_20,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k8_relset_1(X1,X2,X0,X3) = k10_relat_1(X0,X3) ),
    inference(cnf_transformation,[],[f60])).

cnf(c_320,plain,
    ( k8_relset_1(X0,X1,X2,X3) = k10_relat_1(X2,X3)
    | k1_zfmisc_1(k2_zfmisc_1(X0,X1)) != k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))
    | sK2 != X2 ),
    inference(resolution_lifted,[status(thm)],[c_20,c_22])).

cnf(c_321,plain,
    ( k8_relset_1(X0,X1,sK2,X2) = k10_relat_1(sK2,X2)
    | k1_zfmisc_1(k2_zfmisc_1(X0,X1)) != k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)) ),
    inference(unflattening,[status(thm)],[c_320])).

cnf(c_838,plain,
    ( k8_relset_1(sK1,sK0,sK2,X0) = k10_relat_1(sK2,X0) ),
    inference(equality_resolution,[status(thm)],[c_321])).

cnf(c_19,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k7_relset_1(X1,X2,X0,X3) = k9_relat_1(X0,X3) ),
    inference(cnf_transformation,[],[f59])).

cnf(c_329,plain,
    ( k7_relset_1(X0,X1,X2,X3) = k9_relat_1(X2,X3)
    | k1_zfmisc_1(k2_zfmisc_1(X0,X1)) != k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))
    | sK2 != X2 ),
    inference(resolution_lifted,[status(thm)],[c_19,c_22])).

cnf(c_330,plain,
    ( k7_relset_1(X0,X1,sK2,X2) = k9_relat_1(sK2,X2)
    | k1_zfmisc_1(k2_zfmisc_1(X0,X1)) != k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)) ),
    inference(unflattening,[status(thm)],[c_329])).

cnf(c_871,plain,
    ( k7_relset_1(sK1,sK0,sK2,X0) = k9_relat_1(sK2,X0) ),
    inference(equality_resolution,[status(thm)],[c_330])).

cnf(c_1312,plain,
    ( k10_relat_1(sK2,k9_relat_1(sK2,sK1)) != k1_relat_1(sK2)
    | k9_relat_1(sK2,k10_relat_1(sK2,sK0)) != k2_relat_1(sK2) ),
    inference(demodulation,[status(thm)],[c_910,c_838,c_871])).

cnf(c_2137,plain,
    ( k10_relat_1(sK2,k2_relat_1(sK2)) != k1_relat_1(sK2)
    | k9_relat_1(sK2,k10_relat_1(sK2,sK0)) != k2_relat_1(sK2) ),
    inference(demodulation,[status(thm)],[c_1868,c_1312])).

cnf(c_2711,plain,
    ( k10_relat_1(sK2,k2_relat_1(sK2)) != k1_relat_1(sK2)
    | k9_relat_1(sK2,k1_relat_1(sK2)) != k2_relat_1(sK2) ),
    inference(demodulation,[status(thm)],[c_2544,c_2137])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_4222,c_2939,c_2711])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.00/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : iproveropt_run.sh %d %s
% 0.13/0.34  % Computer   : n007.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 15:36:06 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.20/0.34  % Running in FOF mode
% 2.82/0.99  % SZS status Started for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.82/0.99  
% 2.82/0.99  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 2.82/0.99  
% 2.82/0.99  ------  iProver source info
% 2.82/0.99  
% 2.82/0.99  git: date: 2020-06-30 10:37:57 +0100
% 2.82/0.99  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 2.82/0.99  git: non_committed_changes: false
% 2.82/0.99  git: last_make_outside_of_git: false
% 2.82/0.99  
% 2.82/0.99  ------ 
% 2.82/0.99  
% 2.82/0.99  ------ Input Options
% 2.82/0.99  
% 2.82/0.99  --out_options                           all
% 2.82/0.99  --tptp_safe_out                         true
% 2.82/0.99  --problem_path                          ""
% 2.82/0.99  --include_path                          ""
% 2.82/0.99  --clausifier                            res/vclausify_rel
% 2.82/0.99  --clausifier_options                    --mode clausify
% 2.82/0.99  --stdin                                 false
% 2.82/0.99  --stats_out                             all
% 2.82/0.99  
% 2.82/0.99  ------ General Options
% 2.82/0.99  
% 2.82/0.99  --fof                                   false
% 2.82/0.99  --time_out_real                         305.
% 2.82/0.99  --time_out_virtual                      -1.
% 2.82/0.99  --symbol_type_check                     false
% 2.82/0.99  --clausify_out                          false
% 2.82/0.99  --sig_cnt_out                           false
% 2.82/0.99  --trig_cnt_out                          false
% 2.82/0.99  --trig_cnt_out_tolerance                1.
% 2.82/0.99  --trig_cnt_out_sk_spl                   false
% 2.82/0.99  --abstr_cl_out                          false
% 2.82/0.99  
% 2.82/0.99  ------ Global Options
% 2.82/0.99  
% 2.82/0.99  --schedule                              default
% 2.82/0.99  --add_important_lit                     false
% 2.82/0.99  --prop_solver_per_cl                    1000
% 2.82/0.99  --min_unsat_core                        false
% 2.82/0.99  --soft_assumptions                      false
% 2.82/0.99  --soft_lemma_size                       3
% 2.82/0.99  --prop_impl_unit_size                   0
% 2.82/0.99  --prop_impl_unit                        []
% 2.82/0.99  --share_sel_clauses                     true
% 2.82/0.99  --reset_solvers                         false
% 2.82/0.99  --bc_imp_inh                            [conj_cone]
% 2.82/0.99  --conj_cone_tolerance                   3.
% 2.82/0.99  --extra_neg_conj                        none
% 2.82/0.99  --large_theory_mode                     true
% 2.82/0.99  --prolific_symb_bound                   200
% 2.82/0.99  --lt_threshold                          2000
% 2.82/0.99  --clause_weak_htbl                      true
% 2.82/0.99  --gc_record_bc_elim                     false
% 2.82/0.99  
% 2.82/0.99  ------ Preprocessing Options
% 2.82/0.99  
% 2.82/0.99  --preprocessing_flag                    true
% 2.82/0.99  --time_out_prep_mult                    0.1
% 2.82/0.99  --splitting_mode                        input
% 2.82/0.99  --splitting_grd                         true
% 2.82/0.99  --splitting_cvd                         false
% 2.82/0.99  --splitting_cvd_svl                     false
% 2.82/0.99  --splitting_nvd                         32
% 2.82/0.99  --sub_typing                            true
% 2.82/0.99  --prep_gs_sim                           true
% 2.82/0.99  --prep_unflatten                        true
% 2.82/0.99  --prep_res_sim                          true
% 2.82/0.99  --prep_upred                            true
% 2.82/0.99  --prep_sem_filter                       exhaustive
% 2.82/0.99  --prep_sem_filter_out                   false
% 2.82/0.99  --pred_elim                             true
% 2.82/0.99  --res_sim_input                         true
% 2.82/0.99  --eq_ax_congr_red                       true
% 2.82/0.99  --pure_diseq_elim                       true
% 2.82/0.99  --brand_transform                       false
% 2.82/0.99  --non_eq_to_eq                          false
% 2.82/0.99  --prep_def_merge                        true
% 2.82/0.99  --prep_def_merge_prop_impl              false
% 2.82/0.99  --prep_def_merge_mbd                    true
% 2.82/0.99  --prep_def_merge_tr_red                 false
% 2.82/0.99  --prep_def_merge_tr_cl                  false
% 2.82/0.99  --smt_preprocessing                     true
% 2.82/0.99  --smt_ac_axioms                         fast
% 2.82/0.99  --preprocessed_out                      false
% 2.82/0.99  --preprocessed_stats                    false
% 2.82/0.99  
% 2.82/0.99  ------ Abstraction refinement Options
% 2.82/0.99  
% 2.82/0.99  --abstr_ref                             []
% 2.82/0.99  --abstr_ref_prep                        false
% 2.82/0.99  --abstr_ref_until_sat                   false
% 2.82/0.99  --abstr_ref_sig_restrict                funpre
% 2.82/0.99  --abstr_ref_af_restrict_to_split_sk     false
% 2.82/0.99  --abstr_ref_under                       []
% 2.82/0.99  
% 2.82/0.99  ------ SAT Options
% 2.82/0.99  
% 2.82/0.99  --sat_mode                              false
% 2.82/0.99  --sat_fm_restart_options                ""
% 2.82/0.99  --sat_gr_def                            false
% 2.82/0.99  --sat_epr_types                         true
% 2.82/0.99  --sat_non_cyclic_types                  false
% 2.82/0.99  --sat_finite_models                     false
% 2.82/0.99  --sat_fm_lemmas                         false
% 2.82/0.99  --sat_fm_prep                           false
% 2.82/0.99  --sat_fm_uc_incr                        true
% 2.82/0.99  --sat_out_model                         small
% 2.82/0.99  --sat_out_clauses                       false
% 2.82/0.99  
% 2.82/0.99  ------ QBF Options
% 2.82/0.99  
% 2.82/0.99  --qbf_mode                              false
% 2.82/0.99  --qbf_elim_univ                         false
% 2.82/0.99  --qbf_dom_inst                          none
% 2.82/0.99  --qbf_dom_pre_inst                      false
% 2.82/0.99  --qbf_sk_in                             false
% 2.82/0.99  --qbf_pred_elim                         true
% 2.82/0.99  --qbf_split                             512
% 2.82/0.99  
% 2.82/0.99  ------ BMC1 Options
% 2.82/0.99  
% 2.82/0.99  --bmc1_incremental                      false
% 2.82/0.99  --bmc1_axioms                           reachable_all
% 2.82/0.99  --bmc1_min_bound                        0
% 2.82/0.99  --bmc1_max_bound                        -1
% 2.82/0.99  --bmc1_max_bound_default                -1
% 2.82/0.99  --bmc1_symbol_reachability              true
% 2.82/0.99  --bmc1_property_lemmas                  false
% 2.82/0.99  --bmc1_k_induction                      false
% 2.82/0.99  --bmc1_non_equiv_states                 false
% 2.82/0.99  --bmc1_deadlock                         false
% 2.82/0.99  --bmc1_ucm                              false
% 2.82/0.99  --bmc1_add_unsat_core                   none
% 2.82/0.99  --bmc1_unsat_core_children              false
% 2.82/0.99  --bmc1_unsat_core_extrapolate_axioms    false
% 2.82/0.99  --bmc1_out_stat                         full
% 2.82/0.99  --bmc1_ground_init                      false
% 2.82/0.99  --bmc1_pre_inst_next_state              false
% 2.82/0.99  --bmc1_pre_inst_state                   false
% 2.82/0.99  --bmc1_pre_inst_reach_state             false
% 2.82/0.99  --bmc1_out_unsat_core                   false
% 2.82/0.99  --bmc1_aig_witness_out                  false
% 2.82/0.99  --bmc1_verbose                          false
% 2.82/0.99  --bmc1_dump_clauses_tptp                false
% 2.82/0.99  --bmc1_dump_unsat_core_tptp             false
% 2.82/0.99  --bmc1_dump_file                        -
% 2.82/0.99  --bmc1_ucm_expand_uc_limit              128
% 2.82/0.99  --bmc1_ucm_n_expand_iterations          6
% 2.82/0.99  --bmc1_ucm_extend_mode                  1
% 2.82/0.99  --bmc1_ucm_init_mode                    2
% 2.82/0.99  --bmc1_ucm_cone_mode                    none
% 2.82/0.99  --bmc1_ucm_reduced_relation_type        0
% 2.82/0.99  --bmc1_ucm_relax_model                  4
% 2.82/0.99  --bmc1_ucm_full_tr_after_sat            true
% 2.82/0.99  --bmc1_ucm_expand_neg_assumptions       false
% 2.82/0.99  --bmc1_ucm_layered_model                none
% 2.82/0.99  --bmc1_ucm_max_lemma_size               10
% 2.82/0.99  
% 2.82/0.99  ------ AIG Options
% 2.82/0.99  
% 2.82/0.99  --aig_mode                              false
% 2.82/0.99  
% 2.82/0.99  ------ Instantiation Options
% 2.82/0.99  
% 2.82/0.99  --instantiation_flag                    true
% 2.82/0.99  --inst_sos_flag                         false
% 2.82/0.99  --inst_sos_phase                        true
% 2.82/0.99  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 2.82/0.99  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 2.82/0.99  --inst_lit_sel_side                     num_symb
% 2.82/0.99  --inst_solver_per_active                1400
% 2.82/0.99  --inst_solver_calls_frac                1.
% 2.82/0.99  --inst_passive_queue_type               priority_queues
% 2.82/0.99  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 2.82/0.99  --inst_passive_queues_freq              [25;2]
% 2.82/0.99  --inst_dismatching                      true
% 2.82/0.99  --inst_eager_unprocessed_to_passive     true
% 2.82/0.99  --inst_prop_sim_given                   true
% 2.82/0.99  --inst_prop_sim_new                     false
% 2.82/0.99  --inst_subs_new                         false
% 2.82/0.99  --inst_eq_res_simp                      false
% 2.82/0.99  --inst_subs_given                       false
% 2.82/0.99  --inst_orphan_elimination               true
% 2.82/0.99  --inst_learning_loop_flag               true
% 2.82/0.99  --inst_learning_start                   3000
% 2.82/0.99  --inst_learning_factor                  2
% 2.82/0.99  --inst_start_prop_sim_after_learn       3
% 2.82/0.99  --inst_sel_renew                        solver
% 2.82/0.99  --inst_lit_activity_flag                true
% 2.82/0.99  --inst_restr_to_given                   false
% 2.82/0.99  --inst_activity_threshold               500
% 2.82/0.99  --inst_out_proof                        true
% 2.82/0.99  
% 2.82/0.99  ------ Resolution Options
% 2.82/0.99  
% 2.82/0.99  --resolution_flag                       true
% 2.82/0.99  --res_lit_sel                           adaptive
% 2.82/0.99  --res_lit_sel_side                      none
% 2.82/0.99  --res_ordering                          kbo
% 2.82/0.99  --res_to_prop_solver                    active
% 2.82/0.99  --res_prop_simpl_new                    false
% 2.82/0.99  --res_prop_simpl_given                  true
% 2.82/0.99  --res_passive_queue_type                priority_queues
% 2.82/0.99  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 2.82/0.99  --res_passive_queues_freq               [15;5]
% 2.82/0.99  --res_forward_subs                      full
% 2.82/0.99  --res_backward_subs                     full
% 2.82/0.99  --res_forward_subs_resolution           true
% 2.82/0.99  --res_backward_subs_resolution          true
% 2.82/0.99  --res_orphan_elimination                true
% 2.82/0.99  --res_time_limit                        2.
% 2.82/0.99  --res_out_proof                         true
% 2.82/0.99  
% 2.82/0.99  ------ Superposition Options
% 2.82/0.99  
% 2.82/0.99  --superposition_flag                    true
% 2.82/0.99  --sup_passive_queue_type                priority_queues
% 2.82/0.99  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 2.82/0.99  --sup_passive_queues_freq               [8;1;4]
% 2.82/0.99  --demod_completeness_check              fast
% 2.82/0.99  --demod_use_ground                      true
% 2.82/0.99  --sup_to_prop_solver                    passive
% 2.82/0.99  --sup_prop_simpl_new                    true
% 2.82/0.99  --sup_prop_simpl_given                  true
% 2.82/0.99  --sup_fun_splitting                     false
% 2.82/0.99  --sup_smt_interval                      50000
% 2.82/0.99  
% 2.82/0.99  ------ Superposition Simplification Setup
% 2.82/0.99  
% 2.82/0.99  --sup_indices_passive                   []
% 2.82/0.99  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.82/0.99  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.82/0.99  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.82/0.99  --sup_full_triv                         [TrivRules;PropSubs]
% 2.82/0.99  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.82/0.99  --sup_full_bw                           [BwDemod]
% 2.82/0.99  --sup_immed_triv                        [TrivRules]
% 2.82/0.99  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 2.82/0.99  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.82/0.99  --sup_immed_bw_main                     []
% 2.82/0.99  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.82/0.99  --sup_input_triv                        [Unflattening;TrivRules]
% 2.82/0.99  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.82/0.99  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.82/0.99  
% 2.82/0.99  ------ Combination Options
% 2.82/0.99  
% 2.82/0.99  --comb_res_mult                         3
% 2.82/0.99  --comb_sup_mult                         2
% 2.82/0.99  --comb_inst_mult                        10
% 2.82/0.99  
% 2.82/0.99  ------ Debug Options
% 2.82/0.99  
% 2.82/0.99  --dbg_backtrace                         false
% 2.82/0.99  --dbg_dump_prop_clauses                 false
% 2.82/0.99  --dbg_dump_prop_clauses_file            -
% 2.82/0.99  --dbg_out_stat                          false
% 2.82/0.99  ------ Parsing...
% 2.82/0.99  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 2.82/0.99  
% 2.82/0.99  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe:1:0s pe:2:0s pe_e  sf_s  rm: 2 0s  sf_e  pe_s  pe_e 
% 2.82/0.99  
% 2.82/0.99  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 2.82/0.99  
% 2.82/0.99  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 2.82/0.99  ------ Proving...
% 2.82/0.99  ------ Problem Properties 
% 2.82/0.99  
% 2.82/0.99  
% 2.82/0.99  clauses                                 18
% 2.82/0.99  conjectures                             1
% 2.82/0.99  EPR                                     2
% 2.82/0.99  Horn                                    18
% 2.82/0.99  unary                                   5
% 2.82/0.99  binary                                  6
% 2.82/0.99  lits                                    38
% 2.82/0.99  lits eq                                 21
% 2.82/0.99  fd_pure                                 0
% 2.82/0.99  fd_pseudo                               0
% 2.82/0.99  fd_cond                                 0
% 2.82/0.99  fd_pseudo_cond                          1
% 2.82/0.99  AC symbols                              0
% 2.82/0.99  
% 2.82/0.99  ------ Schedule dynamic 5 is on 
% 2.82/0.99  
% 2.82/0.99  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" Time Limit: 10.
% 2.82/0.99  
% 2.82/0.99  
% 2.82/0.99  ------ 
% 2.82/0.99  Current options:
% 2.82/0.99  ------ 
% 2.82/0.99  
% 2.82/0.99  ------ Input Options
% 2.82/0.99  
% 2.82/0.99  --out_options                           all
% 2.82/0.99  --tptp_safe_out                         true
% 2.82/0.99  --problem_path                          ""
% 2.82/0.99  --include_path                          ""
% 2.82/0.99  --clausifier                            res/vclausify_rel
% 2.82/0.99  --clausifier_options                    --mode clausify
% 2.82/0.99  --stdin                                 false
% 2.82/0.99  --stats_out                             all
% 2.82/0.99  
% 2.82/0.99  ------ General Options
% 2.82/0.99  
% 2.82/0.99  --fof                                   false
% 2.82/0.99  --time_out_real                         305.
% 2.82/0.99  --time_out_virtual                      -1.
% 2.82/0.99  --symbol_type_check                     false
% 2.82/0.99  --clausify_out                          false
% 2.82/0.99  --sig_cnt_out                           false
% 2.82/0.99  --trig_cnt_out                          false
% 2.82/0.99  --trig_cnt_out_tolerance                1.
% 2.82/0.99  --trig_cnt_out_sk_spl                   false
% 2.82/0.99  --abstr_cl_out                          false
% 2.82/0.99  
% 2.82/0.99  ------ Global Options
% 2.82/0.99  
% 2.82/0.99  --schedule                              default
% 2.82/0.99  --add_important_lit                     false
% 2.82/0.99  --prop_solver_per_cl                    1000
% 2.82/0.99  --min_unsat_core                        false
% 2.82/0.99  --soft_assumptions                      false
% 2.82/0.99  --soft_lemma_size                       3
% 2.82/0.99  --prop_impl_unit_size                   0
% 2.82/0.99  --prop_impl_unit                        []
% 2.82/0.99  --share_sel_clauses                     true
% 2.82/0.99  --reset_solvers                         false
% 2.82/0.99  --bc_imp_inh                            [conj_cone]
% 2.82/0.99  --conj_cone_tolerance                   3.
% 2.82/0.99  --extra_neg_conj                        none
% 2.82/0.99  --large_theory_mode                     true
% 2.82/0.99  --prolific_symb_bound                   200
% 2.82/0.99  --lt_threshold                          2000
% 2.82/0.99  --clause_weak_htbl                      true
% 2.82/0.99  --gc_record_bc_elim                     false
% 2.82/0.99  
% 2.82/0.99  ------ Preprocessing Options
% 2.82/0.99  
% 2.82/0.99  --preprocessing_flag                    true
% 2.82/0.99  --time_out_prep_mult                    0.1
% 2.82/0.99  --splitting_mode                        input
% 2.82/0.99  --splitting_grd                         true
% 2.82/0.99  --splitting_cvd                         false
% 2.82/0.99  --splitting_cvd_svl                     false
% 2.82/0.99  --splitting_nvd                         32
% 2.82/0.99  --sub_typing                            true
% 2.82/0.99  --prep_gs_sim                           true
% 2.82/0.99  --prep_unflatten                        true
% 2.82/0.99  --prep_res_sim                          true
% 2.82/0.99  --prep_upred                            true
% 2.82/0.99  --prep_sem_filter                       exhaustive
% 2.82/0.99  --prep_sem_filter_out                   false
% 2.82/0.99  --pred_elim                             true
% 2.82/0.99  --res_sim_input                         true
% 2.82/0.99  --eq_ax_congr_red                       true
% 2.82/0.99  --pure_diseq_elim                       true
% 2.82/0.99  --brand_transform                       false
% 2.82/0.99  --non_eq_to_eq                          false
% 2.82/0.99  --prep_def_merge                        true
% 2.82/0.99  --prep_def_merge_prop_impl              false
% 2.82/0.99  --prep_def_merge_mbd                    true
% 2.82/0.99  --prep_def_merge_tr_red                 false
% 2.82/0.99  --prep_def_merge_tr_cl                  false
% 2.82/0.99  --smt_preprocessing                     true
% 2.82/0.99  --smt_ac_axioms                         fast
% 2.82/0.99  --preprocessed_out                      false
% 2.82/0.99  --preprocessed_stats                    false
% 2.82/0.99  
% 2.82/0.99  ------ Abstraction refinement Options
% 2.82/0.99  
% 2.82/0.99  --abstr_ref                             []
% 2.82/0.99  --abstr_ref_prep                        false
% 2.82/0.99  --abstr_ref_until_sat                   false
% 2.82/0.99  --abstr_ref_sig_restrict                funpre
% 2.82/0.99  --abstr_ref_af_restrict_to_split_sk     false
% 2.82/0.99  --abstr_ref_under                       []
% 2.82/0.99  
% 2.82/0.99  ------ SAT Options
% 2.82/0.99  
% 2.82/0.99  --sat_mode                              false
% 2.82/0.99  --sat_fm_restart_options                ""
% 2.82/0.99  --sat_gr_def                            false
% 2.82/0.99  --sat_epr_types                         true
% 2.82/0.99  --sat_non_cyclic_types                  false
% 2.82/0.99  --sat_finite_models                     false
% 2.82/0.99  --sat_fm_lemmas                         false
% 2.82/0.99  --sat_fm_prep                           false
% 2.82/0.99  --sat_fm_uc_incr                        true
% 2.82/0.99  --sat_out_model                         small
% 2.82/0.99  --sat_out_clauses                       false
% 2.82/0.99  
% 2.82/0.99  ------ QBF Options
% 2.82/0.99  
% 2.82/0.99  --qbf_mode                              false
% 2.82/0.99  --qbf_elim_univ                         false
% 2.82/0.99  --qbf_dom_inst                          none
% 2.82/0.99  --qbf_dom_pre_inst                      false
% 2.82/0.99  --qbf_sk_in                             false
% 2.82/0.99  --qbf_pred_elim                         true
% 2.82/0.99  --qbf_split                             512
% 2.82/0.99  
% 2.82/0.99  ------ BMC1 Options
% 2.82/0.99  
% 2.82/0.99  --bmc1_incremental                      false
% 2.82/0.99  --bmc1_axioms                           reachable_all
% 2.82/0.99  --bmc1_min_bound                        0
% 2.82/0.99  --bmc1_max_bound                        -1
% 2.82/0.99  --bmc1_max_bound_default                -1
% 2.82/0.99  --bmc1_symbol_reachability              true
% 2.82/0.99  --bmc1_property_lemmas                  false
% 2.82/0.99  --bmc1_k_induction                      false
% 2.82/0.99  --bmc1_non_equiv_states                 false
% 2.82/0.99  --bmc1_deadlock                         false
% 2.82/0.99  --bmc1_ucm                              false
% 2.82/0.99  --bmc1_add_unsat_core                   none
% 2.82/0.99  --bmc1_unsat_core_children              false
% 2.82/0.99  --bmc1_unsat_core_extrapolate_axioms    false
% 2.82/0.99  --bmc1_out_stat                         full
% 2.82/0.99  --bmc1_ground_init                      false
% 2.82/0.99  --bmc1_pre_inst_next_state              false
% 2.82/0.99  --bmc1_pre_inst_state                   false
% 2.82/0.99  --bmc1_pre_inst_reach_state             false
% 2.82/0.99  --bmc1_out_unsat_core                   false
% 2.82/0.99  --bmc1_aig_witness_out                  false
% 2.82/0.99  --bmc1_verbose                          false
% 2.82/0.99  --bmc1_dump_clauses_tptp                false
% 2.82/0.99  --bmc1_dump_unsat_core_tptp             false
% 2.82/0.99  --bmc1_dump_file                        -
% 2.82/0.99  --bmc1_ucm_expand_uc_limit              128
% 2.82/0.99  --bmc1_ucm_n_expand_iterations          6
% 2.82/0.99  --bmc1_ucm_extend_mode                  1
% 2.82/0.99  --bmc1_ucm_init_mode                    2
% 2.82/0.99  --bmc1_ucm_cone_mode                    none
% 2.82/0.99  --bmc1_ucm_reduced_relation_type        0
% 2.82/0.99  --bmc1_ucm_relax_model                  4
% 2.82/0.99  --bmc1_ucm_full_tr_after_sat            true
% 2.82/0.99  --bmc1_ucm_expand_neg_assumptions       false
% 2.82/0.99  --bmc1_ucm_layered_model                none
% 2.82/0.99  --bmc1_ucm_max_lemma_size               10
% 2.82/0.99  
% 2.82/0.99  ------ AIG Options
% 2.82/0.99  
% 2.82/0.99  --aig_mode                              false
% 2.82/0.99  
% 2.82/0.99  ------ Instantiation Options
% 2.82/0.99  
% 2.82/0.99  --instantiation_flag                    true
% 2.82/0.99  --inst_sos_flag                         false
% 2.82/0.99  --inst_sos_phase                        true
% 2.82/0.99  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 2.82/0.99  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 2.82/0.99  --inst_lit_sel_side                     none
% 2.82/0.99  --inst_solver_per_active                1400
% 2.82/0.99  --inst_solver_calls_frac                1.
% 2.82/0.99  --inst_passive_queue_type               priority_queues
% 2.82/0.99  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 2.82/0.99  --inst_passive_queues_freq              [25;2]
% 2.82/0.99  --inst_dismatching                      true
% 2.82/0.99  --inst_eager_unprocessed_to_passive     true
% 2.82/0.99  --inst_prop_sim_given                   true
% 2.82/0.99  --inst_prop_sim_new                     false
% 2.82/0.99  --inst_subs_new                         false
% 2.82/0.99  --inst_eq_res_simp                      false
% 2.82/0.99  --inst_subs_given                       false
% 2.82/0.99  --inst_orphan_elimination               true
% 2.82/0.99  --inst_learning_loop_flag               true
% 2.82/0.99  --inst_learning_start                   3000
% 2.82/0.99  --inst_learning_factor                  2
% 2.82/0.99  --inst_start_prop_sim_after_learn       3
% 2.82/0.99  --inst_sel_renew                        solver
% 2.82/0.99  --inst_lit_activity_flag                true
% 2.82/0.99  --inst_restr_to_given                   false
% 2.82/0.99  --inst_activity_threshold               500
% 2.82/0.99  --inst_out_proof                        true
% 2.82/0.99  
% 2.82/0.99  ------ Resolution Options
% 2.82/0.99  
% 2.82/0.99  --resolution_flag                       false
% 2.82/0.99  --res_lit_sel                           adaptive
% 2.82/0.99  --res_lit_sel_side                      none
% 2.82/0.99  --res_ordering                          kbo
% 2.82/0.99  --res_to_prop_solver                    active
% 2.82/0.99  --res_prop_simpl_new                    false
% 2.82/0.99  --res_prop_simpl_given                  true
% 2.82/0.99  --res_passive_queue_type                priority_queues
% 2.82/0.99  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 2.82/0.99  --res_passive_queues_freq               [15;5]
% 2.82/0.99  --res_forward_subs                      full
% 2.82/0.99  --res_backward_subs                     full
% 2.82/0.99  --res_forward_subs_resolution           true
% 2.82/0.99  --res_backward_subs_resolution          true
% 2.82/0.99  --res_orphan_elimination                true
% 2.82/0.99  --res_time_limit                        2.
% 2.82/0.99  --res_out_proof                         true
% 2.82/0.99  
% 2.82/0.99  ------ Superposition Options
% 2.82/0.99  
% 2.82/0.99  --superposition_flag                    true
% 2.82/0.99  --sup_passive_queue_type                priority_queues
% 2.82/0.99  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 2.82/0.99  --sup_passive_queues_freq               [8;1;4]
% 2.82/0.99  --demod_completeness_check              fast
% 2.82/0.99  --demod_use_ground                      true
% 2.82/0.99  --sup_to_prop_solver                    passive
% 2.82/0.99  --sup_prop_simpl_new                    true
% 2.82/0.99  --sup_prop_simpl_given                  true
% 2.82/0.99  --sup_fun_splitting                     false
% 2.82/0.99  --sup_smt_interval                      50000
% 2.82/0.99  
% 2.82/0.99  ------ Superposition Simplification Setup
% 2.82/0.99  
% 2.82/0.99  --sup_indices_passive                   []
% 2.82/0.99  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.82/0.99  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.82/0.99  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.82/0.99  --sup_full_triv                         [TrivRules;PropSubs]
% 2.82/0.99  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.82/0.99  --sup_full_bw                           [BwDemod]
% 2.82/0.99  --sup_immed_triv                        [TrivRules]
% 2.82/0.99  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 2.82/0.99  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.82/0.99  --sup_immed_bw_main                     []
% 2.82/0.99  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.82/0.99  --sup_input_triv                        [Unflattening;TrivRules]
% 2.82/0.99  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.82/0.99  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.82/0.99  
% 2.82/0.99  ------ Combination Options
% 2.82/0.99  
% 2.82/0.99  --comb_res_mult                         3
% 2.82/0.99  --comb_sup_mult                         2
% 2.82/0.99  --comb_inst_mult                        10
% 2.82/0.99  
% 2.82/0.99  ------ Debug Options
% 2.82/0.99  
% 2.82/0.99  --dbg_backtrace                         false
% 2.82/0.99  --dbg_dump_prop_clauses                 false
% 2.82/0.99  --dbg_dump_prop_clauses_file            -
% 2.82/0.99  --dbg_out_stat                          false
% 2.82/0.99  
% 2.82/0.99  
% 2.82/0.99  
% 2.82/0.99  
% 2.82/0.99  ------ Proving...
% 2.82/0.99  
% 2.82/0.99  
% 2.82/0.99  % SZS status Theorem for theBenchmark.p
% 2.82/0.99  
% 2.82/0.99  % SZS output start CNFRefutation for theBenchmark.p
% 2.82/0.99  
% 2.82/0.99  fof(f2,axiom,(
% 2.82/0.99    ! [X0] : (v1_relat_1(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => v1_relat_1(X1)))),
% 2.82/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.82/0.99  
% 2.82/0.99  fof(f19,plain,(
% 2.82/0.99    ! [X0] : (! [X1] : (v1_relat_1(X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) | ~v1_relat_1(X0))),
% 2.82/0.99    inference(ennf_transformation,[],[f2])).
% 2.82/0.99  
% 2.82/0.99  fof(f43,plain,(
% 2.82/0.99    ( ! [X0,X1] : (v1_relat_1(X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0)) | ~v1_relat_1(X0)) )),
% 2.82/0.99    inference(cnf_transformation,[],[f19])).
% 2.82/0.99  
% 2.82/0.99  fof(f17,conjecture,(
% 2.82/0.99    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) => (k1_relset_1(X1,X0,X2) = k8_relset_1(X1,X0,X2,k7_relset_1(X1,X0,X2,X1)) & k2_relset_1(X1,X0,X2) = k7_relset_1(X1,X0,X2,k8_relset_1(X1,X0,X2,X0))))),
% 2.82/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.82/0.99  
% 2.82/0.99  fof(f18,negated_conjecture,(
% 2.82/0.99    ~! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) => (k1_relset_1(X1,X0,X2) = k8_relset_1(X1,X0,X2,k7_relset_1(X1,X0,X2,X1)) & k2_relset_1(X1,X0,X2) = k7_relset_1(X1,X0,X2,k8_relset_1(X1,X0,X2,X0))))),
% 2.82/0.99    inference(negated_conjecture,[],[f17])).
% 2.82/0.99  
% 2.82/0.99  fof(f34,plain,(
% 2.82/0.99    ? [X0,X1,X2] : ((k1_relset_1(X1,X0,X2) != k8_relset_1(X1,X0,X2,k7_relset_1(X1,X0,X2,X1)) | k2_relset_1(X1,X0,X2) != k7_relset_1(X1,X0,X2,k8_relset_1(X1,X0,X2,X0))) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X0))))),
% 2.82/0.99    inference(ennf_transformation,[],[f18])).
% 2.82/0.99  
% 2.82/0.99  fof(f38,plain,(
% 2.82/0.99    ? [X0,X1,X2] : ((k1_relset_1(X1,X0,X2) != k8_relset_1(X1,X0,X2,k7_relset_1(X1,X0,X2,X1)) | k2_relset_1(X1,X0,X2) != k7_relset_1(X1,X0,X2,k8_relset_1(X1,X0,X2,X0))) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X0)))) => ((k1_relset_1(sK1,sK0,sK2) != k8_relset_1(sK1,sK0,sK2,k7_relset_1(sK1,sK0,sK2,sK1)) | k2_relset_1(sK1,sK0,sK2) != k7_relset_1(sK1,sK0,sK2,k8_relset_1(sK1,sK0,sK2,sK0))) & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))))),
% 2.82/0.99    introduced(choice_axiom,[])).
% 2.82/0.99  
% 2.82/0.99  fof(f39,plain,(
% 2.82/0.99    (k1_relset_1(sK1,sK0,sK2) != k8_relset_1(sK1,sK0,sK2,k7_relset_1(sK1,sK0,sK2,sK1)) | k2_relset_1(sK1,sK0,sK2) != k7_relset_1(sK1,sK0,sK2,k8_relset_1(sK1,sK0,sK2,sK0))) & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))),
% 2.82/0.99    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f34,f38])).
% 2.82/0.99  
% 2.82/0.99  fof(f61,plain,(
% 2.82/0.99    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))),
% 2.82/0.99    inference(cnf_transformation,[],[f39])).
% 2.82/0.99  
% 2.82/0.99  fof(f5,axiom,(
% 2.82/0.99    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1))),
% 2.82/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.82/0.99  
% 2.82/0.99  fof(f47,plain,(
% 2.82/0.99    ( ! [X0,X1] : (v1_relat_1(k2_zfmisc_1(X0,X1))) )),
% 2.82/0.99    inference(cnf_transformation,[],[f5])).
% 2.82/0.99  
% 2.82/0.99  fof(f1,axiom,(
% 2.82/0.99    ! [X0,X1] : (X0 = X1 <=> (r1_tarski(X1,X0) & r1_tarski(X0,X1)))),
% 2.82/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.82/0.99  
% 2.82/0.99  fof(f35,plain,(
% 2.82/0.99    ! [X0,X1] : ((X0 = X1 | (~r1_tarski(X1,X0) | ~r1_tarski(X0,X1))) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 2.82/0.99    inference(nnf_transformation,[],[f1])).
% 2.82/0.99  
% 2.82/0.99  fof(f36,plain,(
% 2.82/0.99    ! [X0,X1] : ((X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 2.82/0.99    inference(flattening,[],[f35])).
% 2.82/0.99  
% 2.82/0.99  fof(f41,plain,(
% 2.82/0.99    ( ! [X0,X1] : (r1_tarski(X1,X0) | X0 != X1) )),
% 2.82/0.99    inference(cnf_transformation,[],[f36])).
% 2.82/0.99  
% 2.82/0.99  fof(f63,plain,(
% 2.82/0.99    ( ! [X1] : (r1_tarski(X1,X1)) )),
% 2.82/0.99    inference(equality_resolution,[],[f41])).
% 2.82/0.99  
% 2.82/0.99  fof(f11,axiom,(
% 2.82/0.99    ! [X0,X1] : (v1_relat_1(X1) => (r1_tarski(k1_relat_1(X1),X0) => k7_relat_1(X1,X0) = X1))),
% 2.82/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.82/0.99  
% 2.82/0.99  fof(f27,plain,(
% 2.82/0.99    ! [X0,X1] : ((k7_relat_1(X1,X0) = X1 | ~r1_tarski(k1_relat_1(X1),X0)) | ~v1_relat_1(X1))),
% 2.82/0.99    inference(ennf_transformation,[],[f11])).
% 2.82/0.99  
% 2.82/0.99  fof(f28,plain,(
% 2.82/0.99    ! [X0,X1] : (k7_relat_1(X1,X0) = X1 | ~r1_tarski(k1_relat_1(X1),X0) | ~v1_relat_1(X1))),
% 2.82/0.99    inference(flattening,[],[f27])).
% 2.82/0.99  
% 2.82/0.99  fof(f54,plain,(
% 2.82/0.99    ( ! [X0,X1] : (k7_relat_1(X1,X0) = X1 | ~r1_tarski(k1_relat_1(X1),X0) | ~v1_relat_1(X1)) )),
% 2.82/0.99    inference(cnf_transformation,[],[f28])).
% 2.82/0.99  
% 2.82/0.99  fof(f6,axiom,(
% 2.82/0.99    ! [X0,X1] : (v1_relat_1(X1) => k2_relat_1(k7_relat_1(X1,X0)) = k9_relat_1(X1,X0))),
% 2.82/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.82/0.99  
% 2.82/0.99  fof(f21,plain,(
% 2.82/0.99    ! [X0,X1] : (k2_relat_1(k7_relat_1(X1,X0)) = k9_relat_1(X1,X0) | ~v1_relat_1(X1))),
% 2.82/0.99    inference(ennf_transformation,[],[f6])).
% 2.82/0.99  
% 2.82/0.99  fof(f48,plain,(
% 2.82/0.99    ( ! [X0,X1] : (k2_relat_1(k7_relat_1(X1,X0)) = k9_relat_1(X1,X0) | ~v1_relat_1(X1)) )),
% 2.82/0.99    inference(cnf_transformation,[],[f21])).
% 2.82/0.99  
% 2.82/0.99  fof(f12,axiom,(
% 2.82/0.99    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => (v5_relat_1(X2,X1) & v4_relat_1(X2,X0)))),
% 2.82/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.82/0.99  
% 2.82/0.99  fof(f29,plain,(
% 2.82/0.99    ! [X0,X1,X2] : ((v5_relat_1(X2,X1) & v4_relat_1(X2,X0)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 2.82/0.99    inference(ennf_transformation,[],[f12])).
% 2.82/0.99  
% 2.82/0.99  fof(f55,plain,(
% 2.82/0.99    ( ! [X2,X0,X1] : (v4_relat_1(X2,X0) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 2.82/0.99    inference(cnf_transformation,[],[f29])).
% 2.82/0.99  
% 2.82/0.99  fof(f8,axiom,(
% 2.82/0.99    ! [X0,X1] : ((v4_relat_1(X1,X0) & v1_relat_1(X1)) => k7_relat_1(X1,X0) = X1)),
% 2.82/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.82/0.99  
% 2.82/0.99  fof(f23,plain,(
% 2.82/0.99    ! [X0,X1] : (k7_relat_1(X1,X0) = X1 | (~v4_relat_1(X1,X0) | ~v1_relat_1(X1)))),
% 2.82/0.99    inference(ennf_transformation,[],[f8])).
% 2.82/0.99  
% 2.82/0.99  fof(f24,plain,(
% 2.82/0.99    ! [X0,X1] : (k7_relat_1(X1,X0) = X1 | ~v4_relat_1(X1,X0) | ~v1_relat_1(X1))),
% 2.82/0.99    inference(flattening,[],[f23])).
% 2.82/0.99  
% 2.82/0.99  fof(f50,plain,(
% 2.82/0.99    ( ! [X0,X1] : (k7_relat_1(X1,X0) = X1 | ~v4_relat_1(X1,X0) | ~v1_relat_1(X1)) )),
% 2.82/0.99    inference(cnf_transformation,[],[f24])).
% 2.82/0.99  
% 2.82/0.99  fof(f10,axiom,(
% 2.82/0.99    ! [X0,X1] : (v1_relat_1(X1) => (r1_tarski(k2_relat_1(X1),X0) => k5_relat_1(X1,k6_relat_1(X0)) = X1))),
% 2.82/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.82/0.99  
% 2.82/0.99  fof(f25,plain,(
% 2.82/0.99    ! [X0,X1] : ((k5_relat_1(X1,k6_relat_1(X0)) = X1 | ~r1_tarski(k2_relat_1(X1),X0)) | ~v1_relat_1(X1))),
% 2.82/0.99    inference(ennf_transformation,[],[f10])).
% 2.82/0.99  
% 2.82/0.99  fof(f26,plain,(
% 2.82/0.99    ! [X0,X1] : (k5_relat_1(X1,k6_relat_1(X0)) = X1 | ~r1_tarski(k2_relat_1(X1),X0) | ~v1_relat_1(X1))),
% 2.82/0.99    inference(flattening,[],[f25])).
% 2.82/0.99  
% 2.82/0.99  fof(f53,plain,(
% 2.82/0.99    ( ! [X0,X1] : (k5_relat_1(X1,k6_relat_1(X0)) = X1 | ~r1_tarski(k2_relat_1(X1),X0) | ~v1_relat_1(X1)) )),
% 2.82/0.99    inference(cnf_transformation,[],[f26])).
% 2.82/0.99  
% 2.82/0.99  fof(f4,axiom,(
% 2.82/0.99    ! [X0] : v1_relat_1(k6_relat_1(X0))),
% 2.82/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.82/0.99  
% 2.82/0.99  fof(f46,plain,(
% 2.82/0.99    ( ! [X0] : (v1_relat_1(k6_relat_1(X0))) )),
% 2.82/0.99    inference(cnf_transformation,[],[f4])).
% 2.82/0.99  
% 2.82/0.99  fof(f7,axiom,(
% 2.82/0.99    ! [X0] : (v1_relat_1(X0) => ! [X1] : (v1_relat_1(X1) => k1_relat_1(k5_relat_1(X0,X1)) = k10_relat_1(X0,k1_relat_1(X1))))),
% 2.82/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.82/0.99  
% 2.82/0.99  fof(f22,plain,(
% 2.82/0.99    ! [X0] : (! [X1] : (k1_relat_1(k5_relat_1(X0,X1)) = k10_relat_1(X0,k1_relat_1(X1)) | ~v1_relat_1(X1)) | ~v1_relat_1(X0))),
% 2.82/0.99    inference(ennf_transformation,[],[f7])).
% 2.82/0.99  
% 2.82/0.99  fof(f49,plain,(
% 2.82/0.99    ( ! [X0,X1] : (k1_relat_1(k5_relat_1(X0,X1)) = k10_relat_1(X0,k1_relat_1(X1)) | ~v1_relat_1(X1) | ~v1_relat_1(X0)) )),
% 2.82/0.99    inference(cnf_transformation,[],[f22])).
% 2.82/0.99  
% 2.82/0.99  fof(f9,axiom,(
% 2.82/0.99    ! [X0] : (k2_relat_1(k6_relat_1(X0)) = X0 & k1_relat_1(k6_relat_1(X0)) = X0)),
% 2.82/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.82/0.99  
% 2.82/0.99  fof(f51,plain,(
% 2.82/0.99    ( ! [X0] : (k1_relat_1(k6_relat_1(X0)) = X0) )),
% 2.82/0.99    inference(cnf_transformation,[],[f9])).
% 2.82/0.99  
% 2.82/0.99  fof(f56,plain,(
% 2.82/0.99    ( ! [X2,X0,X1] : (v5_relat_1(X2,X1) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 2.82/0.99    inference(cnf_transformation,[],[f29])).
% 2.82/0.99  
% 2.82/0.99  fof(f3,axiom,(
% 2.82/0.99    ! [X0,X1] : (v1_relat_1(X1) => (v5_relat_1(X1,X0) <=> r1_tarski(k2_relat_1(X1),X0)))),
% 2.82/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.82/0.99  
% 2.82/0.99  fof(f20,plain,(
% 2.82/0.99    ! [X0,X1] : ((v5_relat_1(X1,X0) <=> r1_tarski(k2_relat_1(X1),X0)) | ~v1_relat_1(X1))),
% 2.82/0.99    inference(ennf_transformation,[],[f3])).
% 2.82/0.99  
% 2.82/0.99  fof(f37,plain,(
% 2.82/0.99    ! [X0,X1] : (((v5_relat_1(X1,X0) | ~r1_tarski(k2_relat_1(X1),X0)) & (r1_tarski(k2_relat_1(X1),X0) | ~v5_relat_1(X1,X0))) | ~v1_relat_1(X1))),
% 2.82/0.99    inference(nnf_transformation,[],[f20])).
% 2.82/0.99  
% 2.82/0.99  fof(f44,plain,(
% 2.82/0.99    ( ! [X0,X1] : (r1_tarski(k2_relat_1(X1),X0) | ~v5_relat_1(X1,X0) | ~v1_relat_1(X1)) )),
% 2.82/0.99    inference(cnf_transformation,[],[f37])).
% 2.82/0.99  
% 2.82/0.99  fof(f13,axiom,(
% 2.82/0.99    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k1_relat_1(X2) = k1_relset_1(X0,X1,X2))),
% 2.82/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.82/0.99  
% 2.82/0.99  fof(f30,plain,(
% 2.82/0.99    ! [X0,X1,X2] : (k1_relat_1(X2) = k1_relset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 2.82/0.99    inference(ennf_transformation,[],[f13])).
% 2.82/0.99  
% 2.82/0.99  fof(f57,plain,(
% 2.82/0.99    ( ! [X2,X0,X1] : (k1_relat_1(X2) = k1_relset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 2.82/0.99    inference(cnf_transformation,[],[f30])).
% 2.82/0.99  
% 2.82/0.99  fof(f14,axiom,(
% 2.82/0.99    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k2_relat_1(X2) = k2_relset_1(X0,X1,X2))),
% 2.82/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.82/0.99  
% 2.82/0.99  fof(f31,plain,(
% 2.82/0.99    ! [X0,X1,X2] : (k2_relat_1(X2) = k2_relset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 2.82/0.99    inference(ennf_transformation,[],[f14])).
% 2.82/0.99  
% 2.82/0.99  fof(f58,plain,(
% 2.82/0.99    ( ! [X2,X0,X1] : (k2_relat_1(X2) = k2_relset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 2.82/0.99    inference(cnf_transformation,[],[f31])).
% 2.82/0.99  
% 2.82/0.99  fof(f62,plain,(
% 2.82/0.99    k1_relset_1(sK1,sK0,sK2) != k8_relset_1(sK1,sK0,sK2,k7_relset_1(sK1,sK0,sK2,sK1)) | k2_relset_1(sK1,sK0,sK2) != k7_relset_1(sK1,sK0,sK2,k8_relset_1(sK1,sK0,sK2,sK0))),
% 2.82/0.99    inference(cnf_transformation,[],[f39])).
% 2.82/0.99  
% 2.82/0.99  fof(f16,axiom,(
% 2.82/0.99    ! [X0,X1,X2,X3] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k10_relat_1(X2,X3) = k8_relset_1(X0,X1,X2,X3))),
% 2.82/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.82/0.99  
% 2.82/0.99  fof(f33,plain,(
% 2.82/0.99    ! [X0,X1,X2,X3] : (k10_relat_1(X2,X3) = k8_relset_1(X0,X1,X2,X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 2.82/0.99    inference(ennf_transformation,[],[f16])).
% 2.82/0.99  
% 2.82/0.99  fof(f60,plain,(
% 2.82/0.99    ( ! [X2,X0,X3,X1] : (k10_relat_1(X2,X3) = k8_relset_1(X0,X1,X2,X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 2.82/0.99    inference(cnf_transformation,[],[f33])).
% 2.82/0.99  
% 2.82/0.99  fof(f15,axiom,(
% 2.82/0.99    ! [X0,X1,X2,X3] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k9_relat_1(X2,X3) = k7_relset_1(X0,X1,X2,X3))),
% 2.82/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.82/0.99  
% 2.82/0.99  fof(f32,plain,(
% 2.82/0.99    ! [X0,X1,X2,X3] : (k9_relat_1(X2,X3) = k7_relset_1(X0,X1,X2,X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 2.82/0.99    inference(ennf_transformation,[],[f15])).
% 2.82/0.99  
% 2.82/0.99  fof(f59,plain,(
% 2.82/0.99    ( ! [X2,X0,X3,X1] : (k9_relat_1(X2,X3) = k7_relset_1(X0,X1,X2,X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 2.82/0.99    inference(cnf_transformation,[],[f32])).
% 2.82/0.99  
% 2.82/0.99  cnf(c_3,plain,
% 2.82/0.99      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
% 2.82/0.99      | ~ v1_relat_1(X1)
% 2.82/0.99      | v1_relat_1(X0) ),
% 2.82/0.99      inference(cnf_transformation,[],[f43]) ).
% 2.82/0.99  
% 2.82/0.99  cnf(c_22,negated_conjecture,
% 2.82/0.99      ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) ),
% 2.82/0.99      inference(cnf_transformation,[],[f61]) ).
% 2.82/0.99  
% 2.82/0.99  cnf(c_275,plain,
% 2.82/0.99      ( ~ v1_relat_1(X0)
% 2.82/0.99      | v1_relat_1(X1)
% 2.82/0.99      | k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)) != k1_zfmisc_1(X0)
% 2.82/0.99      | sK2 != X1 ),
% 2.82/0.99      inference(resolution_lifted,[status(thm)],[c_3,c_22]) ).
% 2.82/0.99  
% 2.82/0.99  cnf(c_276,plain,
% 2.82/0.99      ( ~ v1_relat_1(X0)
% 2.82/0.99      | v1_relat_1(sK2)
% 2.82/0.99      | k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)) != k1_zfmisc_1(X0) ),
% 2.82/0.99      inference(unflattening,[status(thm)],[c_275]) ).
% 2.82/0.99  
% 2.82/0.99  cnf(c_677,plain,
% 2.82/0.99      ( k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)) != k1_zfmisc_1(X0)
% 2.82/0.99      | v1_relat_1(X0) != iProver_top
% 2.82/0.99      | v1_relat_1(sK2) = iProver_top ),
% 2.82/0.99      inference(predicate_to_equality,[status(thm)],[c_276]) ).
% 2.82/0.99  
% 2.82/0.99  cnf(c_461,plain,( X0 = X0 ),theory(equality) ).
% 2.82/0.99  
% 2.82/0.99  cnf(c_796,plain,
% 2.82/0.99      ( k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)) = k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)) ),
% 2.82/0.99      inference(instantiation,[status(thm)],[c_461]) ).
% 2.82/0.99  
% 2.82/0.99  cnf(c_786,plain,
% 2.82/0.99      ( ~ v1_relat_1(k2_zfmisc_1(X0,X1))
% 2.82/0.99      | v1_relat_1(sK2)
% 2.82/0.99      | k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)) != k1_zfmisc_1(k2_zfmisc_1(X0,X1)) ),
% 2.82/0.99      inference(instantiation,[status(thm)],[c_276]) ).
% 2.82/0.99  
% 2.82/0.99  cnf(c_931,plain,
% 2.82/0.99      ( ~ v1_relat_1(k2_zfmisc_1(sK1,sK0))
% 2.82/0.99      | v1_relat_1(sK2)
% 2.82/0.99      | k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)) != k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)) ),
% 2.82/0.99      inference(instantiation,[status(thm)],[c_786]) ).
% 2.82/0.99  
% 2.82/0.99  cnf(c_932,plain,
% 2.82/0.99      ( k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)) != k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))
% 2.82/0.99      | v1_relat_1(k2_zfmisc_1(sK1,sK0)) != iProver_top
% 2.82/0.99      | v1_relat_1(sK2) = iProver_top ),
% 2.82/0.99      inference(predicate_to_equality,[status(thm)],[c_931]) ).
% 2.82/0.99  
% 2.82/0.99  cnf(c_7,plain,
% 2.82/0.99      ( v1_relat_1(k2_zfmisc_1(X0,X1)) ),
% 2.82/0.99      inference(cnf_transformation,[],[f47]) ).
% 2.82/0.99  
% 2.82/0.99  cnf(c_1067,plain,
% 2.82/0.99      ( v1_relat_1(k2_zfmisc_1(sK1,sK0)) ),
% 2.82/0.99      inference(instantiation,[status(thm)],[c_7]) ).
% 2.82/0.99  
% 2.82/0.99  cnf(c_1068,plain,
% 2.82/0.99      ( v1_relat_1(k2_zfmisc_1(sK1,sK0)) = iProver_top ),
% 2.82/0.99      inference(predicate_to_equality,[status(thm)],[c_1067]) ).
% 2.82/0.99  
% 2.82/0.99  cnf(c_1217,plain,
% 2.82/0.99      ( v1_relat_1(sK2) = iProver_top ),
% 2.82/0.99      inference(global_propositional_subsumption,
% 2.82/0.99                [status(thm)],
% 2.82/0.99                [c_677,c_796,c_932,c_1068]) ).
% 2.82/0.99  
% 2.82/0.99  cnf(c_1,plain,
% 2.82/0.99      ( r1_tarski(X0,X0) ),
% 2.82/0.99      inference(cnf_transformation,[],[f63]) ).
% 2.82/0.99  
% 2.82/0.99  cnf(c_684,plain,
% 2.82/0.99      ( r1_tarski(X0,X0) = iProver_top ),
% 2.82/0.99      inference(predicate_to_equality,[status(thm)],[c_1]) ).
% 2.82/0.99  
% 2.82/0.99  cnf(c_14,plain,
% 2.82/0.99      ( ~ r1_tarski(k1_relat_1(X0),X1)
% 2.82/0.99      | ~ v1_relat_1(X0)
% 2.82/0.99      | k7_relat_1(X0,X1) = X0 ),
% 2.82/0.99      inference(cnf_transformation,[],[f54]) ).
% 2.82/0.99  
% 2.82/0.99  cnf(c_678,plain,
% 2.82/0.99      ( k7_relat_1(X0,X1) = X0
% 2.82/0.99      | r1_tarski(k1_relat_1(X0),X1) != iProver_top
% 2.82/0.99      | v1_relat_1(X0) != iProver_top ),
% 2.82/0.99      inference(predicate_to_equality,[status(thm)],[c_14]) ).
% 2.82/0.99  
% 2.82/0.99  cnf(c_1479,plain,
% 2.82/0.99      ( k7_relat_1(X0,k1_relat_1(X0)) = X0
% 2.82/0.99      | v1_relat_1(X0) != iProver_top ),
% 2.82/0.99      inference(superposition,[status(thm)],[c_684,c_678]) ).
% 2.82/0.99  
% 2.82/0.99  cnf(c_4053,plain,
% 2.82/0.99      ( k7_relat_1(sK2,k1_relat_1(sK2)) = sK2 ),
% 2.82/0.99      inference(superposition,[status(thm)],[c_1217,c_1479]) ).
% 2.82/0.99  
% 2.82/0.99  cnf(c_8,plain,
% 2.82/0.99      ( ~ v1_relat_1(X0)
% 2.82/0.99      | k2_relat_1(k7_relat_1(X0,X1)) = k9_relat_1(X0,X1) ),
% 2.82/0.99      inference(cnf_transformation,[],[f48]) ).
% 2.82/0.99  
% 2.82/0.99  cnf(c_681,plain,
% 2.82/0.99      ( k2_relat_1(k7_relat_1(X0,X1)) = k9_relat_1(X0,X1)
% 2.82/0.99      | v1_relat_1(X0) != iProver_top ),
% 2.82/0.99      inference(predicate_to_equality,[status(thm)],[c_8]) ).
% 2.82/0.99  
% 2.82/0.99  cnf(c_1551,plain,
% 2.82/0.99      ( k2_relat_1(k7_relat_1(sK2,X0)) = k9_relat_1(sK2,X0) ),
% 2.82/0.99      inference(superposition,[status(thm)],[c_1217,c_681]) ).
% 2.82/0.99  
% 2.82/0.99  cnf(c_4222,plain,
% 2.82/0.99      ( k9_relat_1(sK2,k1_relat_1(sK2)) = k2_relat_1(sK2) ),
% 2.82/0.99      inference(superposition,[status(thm)],[c_4053,c_1551]) ).
% 2.82/0.99  
% 2.82/0.99  cnf(c_16,plain,
% 2.82/0.99      ( v4_relat_1(X0,X1)
% 2.82/0.99      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) ),
% 2.82/0.99      inference(cnf_transformation,[],[f55]) ).
% 2.82/0.99  
% 2.82/0.99  cnf(c_10,plain,
% 2.82/0.99      ( ~ v4_relat_1(X0,X1) | ~ v1_relat_1(X0) | k7_relat_1(X0,X1) = X0 ),
% 2.82/0.99      inference(cnf_transformation,[],[f50]) ).
% 2.82/0.99  
% 2.82/0.99  cnf(c_238,plain,
% 2.82/0.99      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 2.82/0.99      | ~ v1_relat_1(X0)
% 2.82/0.99      | k7_relat_1(X0,X1) = X0 ),
% 2.82/0.99      inference(resolution,[status(thm)],[c_16,c_10]) ).
% 2.82/0.99  
% 2.82/0.99  cnf(c_305,plain,
% 2.82/0.99      ( ~ v1_relat_1(X0)
% 2.82/0.99      | k7_relat_1(X0,X1) = X0
% 2.82/0.99      | k1_zfmisc_1(k2_zfmisc_1(X1,X2)) != k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))
% 2.82/0.99      | sK2 != X0 ),
% 2.82/0.99      inference(resolution_lifted,[status(thm)],[c_238,c_22]) ).
% 2.82/0.99  
% 2.82/0.99  cnf(c_306,plain,
% 2.82/0.99      ( ~ v1_relat_1(sK2)
% 2.82/0.99      | k7_relat_1(sK2,X0) = sK2
% 2.82/0.99      | k1_zfmisc_1(k2_zfmisc_1(X0,X1)) != k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)) ),
% 2.82/0.99      inference(unflattening,[status(thm)],[c_305]) ).
% 2.82/0.99  
% 2.82/0.99  cnf(c_675,plain,
% 2.82/0.99      ( k7_relat_1(sK2,X0) = sK2
% 2.82/0.99      | k1_zfmisc_1(k2_zfmisc_1(X0,X1)) != k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))
% 2.82/0.99      | v1_relat_1(sK2) != iProver_top ),
% 2.82/0.99      inference(predicate_to_equality,[status(thm)],[c_306]) ).
% 2.82/0.99  
% 2.82/0.99  cnf(c_975,plain,
% 2.82/0.99      ( k7_relat_1(sK2,sK1) = sK2 | v1_relat_1(sK2) != iProver_top ),
% 2.82/0.99      inference(equality_resolution,[status(thm)],[c_675]) ).
% 2.82/0.99  
% 2.82/0.99  cnf(c_976,plain,
% 2.82/0.99      ( ~ v1_relat_1(sK2) | k7_relat_1(sK2,sK1) = sK2 ),
% 2.82/0.99      inference(predicate_to_equality_rev,[status(thm)],[c_975]) ).
% 2.82/0.99  
% 2.82/0.99  cnf(c_1399,plain,
% 2.82/0.99      ( k7_relat_1(sK2,sK1) = sK2 ),
% 2.82/0.99      inference(global_propositional_subsumption,
% 2.82/0.99                [status(thm)],
% 2.82/0.99                [c_975,c_796,c_931,c_976,c_1067]) ).
% 2.82/0.99  
% 2.82/0.99  cnf(c_13,plain,
% 2.82/0.99      ( ~ r1_tarski(k2_relat_1(X0),X1)
% 2.82/0.99      | ~ v1_relat_1(X0)
% 2.82/0.99      | k5_relat_1(X0,k6_relat_1(X1)) = X0 ),
% 2.82/0.99      inference(cnf_transformation,[],[f53]) ).
% 2.82/0.99  
% 2.82/0.99  cnf(c_679,plain,
% 2.82/0.99      ( k5_relat_1(X0,k6_relat_1(X1)) = X0
% 2.82/0.99      | r1_tarski(k2_relat_1(X0),X1) != iProver_top
% 2.82/0.99      | v1_relat_1(X0) != iProver_top ),
% 2.82/0.99      inference(predicate_to_equality,[status(thm)],[c_13]) ).
% 2.82/0.99  
% 2.82/0.99  cnf(c_1869,plain,
% 2.82/0.99      ( k5_relat_1(k7_relat_1(sK2,X0),k6_relat_1(X1)) = k7_relat_1(sK2,X0)
% 2.82/0.99      | r1_tarski(k9_relat_1(sK2,X0),X1) != iProver_top
% 2.82/0.99      | v1_relat_1(k7_relat_1(sK2,X0)) != iProver_top ),
% 2.82/0.99      inference(superposition,[status(thm)],[c_1551,c_679]) ).
% 2.82/0.99  
% 2.82/0.99  cnf(c_2802,plain,
% 2.82/0.99      ( k5_relat_1(k7_relat_1(sK2,X0),k6_relat_1(k9_relat_1(sK2,X0))) = k7_relat_1(sK2,X0)
% 2.82/0.99      | v1_relat_1(k7_relat_1(sK2,X0)) != iProver_top ),
% 2.82/0.99      inference(superposition,[status(thm)],[c_684,c_1869]) ).
% 2.82/0.99  
% 2.82/0.99  cnf(c_2887,plain,
% 2.82/0.99      ( k5_relat_1(k7_relat_1(sK2,sK1),k6_relat_1(k9_relat_1(sK2,sK1))) = k7_relat_1(sK2,sK1)
% 2.82/0.99      | v1_relat_1(sK2) != iProver_top ),
% 2.82/0.99      inference(superposition,[status(thm)],[c_1399,c_2802]) ).
% 2.82/0.99  
% 2.82/0.99  cnf(c_1868,plain,
% 2.82/0.99      ( k9_relat_1(sK2,sK1) = k2_relat_1(sK2) ),
% 2.82/0.99      inference(superposition,[status(thm)],[c_1399,c_1551]) ).
% 2.82/0.99  
% 2.82/0.99  cnf(c_2888,plain,
% 2.82/0.99      ( k5_relat_1(sK2,k6_relat_1(k2_relat_1(sK2))) = sK2
% 2.82/0.99      | v1_relat_1(sK2) != iProver_top ),
% 2.82/0.99      inference(light_normalisation,[status(thm)],[c_2887,c_1399,c_1868]) ).
% 2.82/0.99  
% 2.82/0.99  cnf(c_2936,plain,
% 2.82/0.99      ( k5_relat_1(sK2,k6_relat_1(k2_relat_1(sK2))) = sK2 ),
% 2.82/0.99      inference(global_propositional_subsumption,
% 2.82/0.99                [status(thm)],
% 2.82/0.99                [c_2888,c_796,c_932,c_1068]) ).
% 2.82/0.99  
% 2.82/0.99  cnf(c_6,plain,
% 2.82/0.99      ( v1_relat_1(k6_relat_1(X0)) ),
% 2.82/0.99      inference(cnf_transformation,[],[f46]) ).
% 2.82/0.99  
% 2.82/0.99  cnf(c_683,plain,
% 2.82/0.99      ( v1_relat_1(k6_relat_1(X0)) = iProver_top ),
% 2.82/0.99      inference(predicate_to_equality,[status(thm)],[c_6]) ).
% 2.82/0.99  
% 2.82/0.99  cnf(c_9,plain,
% 2.82/0.99      ( ~ v1_relat_1(X0)
% 2.82/0.99      | ~ v1_relat_1(X1)
% 2.82/0.99      | k10_relat_1(X0,k1_relat_1(X1)) = k1_relat_1(k5_relat_1(X0,X1)) ),
% 2.82/0.99      inference(cnf_transformation,[],[f49]) ).
% 2.82/0.99  
% 2.82/0.99  cnf(c_680,plain,
% 2.82/0.99      ( k10_relat_1(X0,k1_relat_1(X1)) = k1_relat_1(k5_relat_1(X0,X1))
% 2.82/0.99      | v1_relat_1(X0) != iProver_top
% 2.82/0.99      | v1_relat_1(X1) != iProver_top ),
% 2.82/0.99      inference(predicate_to_equality,[status(thm)],[c_9]) ).
% 2.82/0.99  
% 2.82/0.99  cnf(c_1664,plain,
% 2.82/0.99      ( k10_relat_1(sK2,k1_relat_1(X0)) = k1_relat_1(k5_relat_1(sK2,X0))
% 2.82/0.99      | v1_relat_1(X0) != iProver_top ),
% 2.82/0.99      inference(superposition,[status(thm)],[c_1217,c_680]) ).
% 2.82/0.99  
% 2.82/0.99  cnf(c_1884,plain,
% 2.82/0.99      ( k10_relat_1(sK2,k1_relat_1(k6_relat_1(X0))) = k1_relat_1(k5_relat_1(sK2,k6_relat_1(X0))) ),
% 2.82/0.99      inference(superposition,[status(thm)],[c_683,c_1664]) ).
% 2.82/0.99  
% 2.82/0.99  cnf(c_12,plain,
% 2.82/0.99      ( k1_relat_1(k6_relat_1(X0)) = X0 ),
% 2.82/0.99      inference(cnf_transformation,[],[f51]) ).
% 2.82/0.99  
% 2.82/0.99  cnf(c_1892,plain,
% 2.82/0.99      ( k1_relat_1(k5_relat_1(sK2,k6_relat_1(X0))) = k10_relat_1(sK2,X0) ),
% 2.82/0.99      inference(light_normalisation,[status(thm)],[c_1884,c_12]) ).
% 2.82/0.99  
% 2.82/0.99  cnf(c_2939,plain,
% 2.82/0.99      ( k10_relat_1(sK2,k2_relat_1(sK2)) = k1_relat_1(sK2) ),
% 2.82/0.99      inference(superposition,[status(thm)],[c_2936,c_1892]) ).
% 2.82/0.99  
% 2.82/0.99  cnf(c_15,plain,
% 2.82/0.99      ( v5_relat_1(X0,X1)
% 2.82/0.99      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) ),
% 2.82/0.99      inference(cnf_transformation,[],[f56]) ).
% 2.82/0.99  
% 2.82/0.99  cnf(c_5,plain,
% 2.82/0.99      ( ~ v5_relat_1(X0,X1)
% 2.82/0.99      | r1_tarski(k2_relat_1(X0),X1)
% 2.82/0.99      | ~ v1_relat_1(X0) ),
% 2.82/0.99      inference(cnf_transformation,[],[f44]) ).
% 2.82/0.99  
% 2.82/0.99  cnf(c_256,plain,
% 2.82/0.99      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 2.82/0.99      | r1_tarski(k2_relat_1(X0),X2)
% 2.82/0.99      | ~ v1_relat_1(X0) ),
% 2.82/0.99      inference(resolution,[status(thm)],[c_15,c_5]) ).
% 2.82/0.99  
% 2.82/0.99  cnf(c_290,plain,
% 2.82/0.99      ( r1_tarski(k2_relat_1(X0),X1)
% 2.82/0.99      | ~ v1_relat_1(X0)
% 2.82/0.99      | k1_zfmisc_1(k2_zfmisc_1(X2,X1)) != k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))
% 2.82/0.99      | sK2 != X0 ),
% 2.82/0.99      inference(resolution_lifted,[status(thm)],[c_256,c_22]) ).
% 2.82/0.99  
% 2.82/0.99  cnf(c_291,plain,
% 2.82/0.99      ( r1_tarski(k2_relat_1(sK2),X0)
% 2.82/0.99      | ~ v1_relat_1(sK2)
% 2.82/0.99      | k1_zfmisc_1(k2_zfmisc_1(X1,X0)) != k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)) ),
% 2.82/0.99      inference(unflattening,[status(thm)],[c_290]) ).
% 2.82/0.99  
% 2.82/0.99  cnf(c_676,plain,
% 2.82/0.99      ( k1_zfmisc_1(k2_zfmisc_1(X0,X1)) != k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))
% 2.82/0.99      | r1_tarski(k2_relat_1(sK2),X1) = iProver_top
% 2.82/0.99      | v1_relat_1(sK2) != iProver_top ),
% 2.82/0.99      inference(predicate_to_equality,[status(thm)],[c_291]) ).
% 2.82/0.99  
% 2.82/0.99  cnf(c_292,plain,
% 2.82/0.99      ( k1_zfmisc_1(k2_zfmisc_1(X0,X1)) != k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))
% 2.82/0.99      | r1_tarski(k2_relat_1(sK2),X1) = iProver_top
% 2.82/0.99      | v1_relat_1(sK2) != iProver_top ),
% 2.82/0.99      inference(predicate_to_equality,[status(thm)],[c_291]) ).
% 2.82/0.99  
% 2.82/0.99  cnf(c_1302,plain,
% 2.82/0.99      ( r1_tarski(k2_relat_1(sK2),X1) = iProver_top
% 2.82/0.99      | k1_zfmisc_1(k2_zfmisc_1(X0,X1)) != k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)) ),
% 2.82/0.99      inference(global_propositional_subsumption,
% 2.82/0.99                [status(thm)],
% 2.82/0.99                [c_676,c_292,c_796,c_932,c_1068]) ).
% 2.82/0.99  
% 2.82/0.99  cnf(c_1303,plain,
% 2.82/0.99      ( k1_zfmisc_1(k2_zfmisc_1(X0,X1)) != k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))
% 2.82/0.99      | r1_tarski(k2_relat_1(sK2),X1) = iProver_top ),
% 2.82/0.99      inference(renaming,[status(thm)],[c_1302]) ).
% 2.82/0.99  
% 2.82/0.99  cnf(c_1310,plain,
% 2.82/0.99      ( r1_tarski(k2_relat_1(sK2),sK0) = iProver_top ),
% 2.82/0.99      inference(equality_resolution,[status(thm)],[c_1303]) ).
% 2.82/0.99  
% 2.82/0.99  cnf(c_1635,plain,
% 2.82/0.99      ( k5_relat_1(sK2,k6_relat_1(sK0)) = sK2
% 2.82/0.99      | v1_relat_1(sK2) != iProver_top ),
% 2.82/0.99      inference(superposition,[status(thm)],[c_1310,c_679]) ).
% 2.82/0.99  
% 2.82/0.99  cnf(c_1311,plain,
% 2.82/0.99      ( r1_tarski(k2_relat_1(sK2),sK0) ),
% 2.82/0.99      inference(predicate_to_equality_rev,[status(thm)],[c_1310]) ).
% 2.82/0.99  
% 2.82/0.99  cnf(c_1406,plain,
% 2.82/0.99      ( ~ r1_tarski(k2_relat_1(sK2),X0)
% 2.82/0.99      | ~ v1_relat_1(sK2)
% 2.82/0.99      | k5_relat_1(sK2,k6_relat_1(X0)) = sK2 ),
% 2.82/0.99      inference(instantiation,[status(thm)],[c_13]) ).
% 2.82/0.99  
% 2.82/0.99  cnf(c_1419,plain,
% 2.82/0.99      ( ~ r1_tarski(k2_relat_1(sK2),sK0)
% 2.82/0.99      | ~ v1_relat_1(sK2)
% 2.82/0.99      | k5_relat_1(sK2,k6_relat_1(sK0)) = sK2 ),
% 2.82/0.99      inference(instantiation,[status(thm)],[c_1406]) ).
% 2.82/0.99  
% 2.82/0.99  cnf(c_2304,plain,
% 2.82/0.99      ( k5_relat_1(sK2,k6_relat_1(sK0)) = sK2 ),
% 2.82/0.99      inference(global_propositional_subsumption,
% 2.82/0.99                [status(thm)],
% 2.82/0.99                [c_1635,c_796,c_931,c_1067,c_1311,c_1419]) ).
% 2.82/0.99  
% 2.82/0.99  cnf(c_2544,plain,
% 2.82/0.99      ( k10_relat_1(sK2,sK0) = k1_relat_1(sK2) ),
% 2.82/0.99      inference(superposition,[status(thm)],[c_2304,c_1892]) ).
% 2.82/0.99  
% 2.82/0.99  cnf(c_17,plain,
% 2.82/0.99      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 2.82/0.99      | k1_relset_1(X1,X2,X0) = k1_relat_1(X0) ),
% 2.82/0.99      inference(cnf_transformation,[],[f57]) ).
% 2.82/0.99  
% 2.82/0.99  cnf(c_347,plain,
% 2.82/0.99      ( k1_relset_1(X0,X1,X2) = k1_relat_1(X2)
% 2.82/0.99      | k1_zfmisc_1(k2_zfmisc_1(X0,X1)) != k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))
% 2.82/0.99      | sK2 != X2 ),
% 2.82/0.99      inference(resolution_lifted,[status(thm)],[c_17,c_22]) ).
% 2.82/0.99  
% 2.82/0.99  cnf(c_348,plain,
% 2.82/0.99      ( k1_relset_1(X0,X1,sK2) = k1_relat_1(sK2)
% 2.82/0.99      | k1_zfmisc_1(k2_zfmisc_1(X0,X1)) != k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)) ),
% 2.82/0.99      inference(unflattening,[status(thm)],[c_347]) ).
% 2.82/0.99  
% 2.82/0.99  cnf(c_835,plain,
% 2.82/0.99      ( k1_relset_1(sK1,sK0,sK2) = k1_relat_1(sK2) ),
% 2.82/0.99      inference(equality_resolution,[status(thm)],[c_348]) ).
% 2.82/0.99  
% 2.82/0.99  cnf(c_18,plain,
% 2.82/0.99      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 2.82/0.99      | k2_relset_1(X1,X2,X0) = k2_relat_1(X0) ),
% 2.82/0.99      inference(cnf_transformation,[],[f58]) ).
% 2.82/0.99  
% 2.82/0.99  cnf(c_338,plain,
% 2.82/0.99      ( k2_relset_1(X0,X1,X2) = k2_relat_1(X2)
% 2.82/0.99      | k1_zfmisc_1(k2_zfmisc_1(X0,X1)) != k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))
% 2.82/0.99      | sK2 != X2 ),
% 2.82/0.99      inference(resolution_lifted,[status(thm)],[c_18,c_22]) ).
% 2.82/0.99  
% 2.82/0.99  cnf(c_339,plain,
% 2.82/0.99      ( k2_relset_1(X0,X1,sK2) = k2_relat_1(sK2)
% 2.82/0.99      | k1_zfmisc_1(k2_zfmisc_1(X0,X1)) != k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)) ),
% 2.82/0.99      inference(unflattening,[status(thm)],[c_338]) ).
% 2.82/0.99  
% 2.82/0.99  cnf(c_795,plain,
% 2.82/0.99      ( k2_relset_1(sK1,sK0,sK2) = k2_relat_1(sK2) ),
% 2.82/0.99      inference(equality_resolution,[status(thm)],[c_339]) ).
% 2.82/0.99  
% 2.82/0.99  cnf(c_21,negated_conjecture,
% 2.82/0.99      ( k2_relset_1(sK1,sK0,sK2) != k7_relset_1(sK1,sK0,sK2,k8_relset_1(sK1,sK0,sK2,sK0))
% 2.82/0.99      | k1_relset_1(sK1,sK0,sK2) != k8_relset_1(sK1,sK0,sK2,k7_relset_1(sK1,sK0,sK2,sK1)) ),
% 2.82/0.99      inference(cnf_transformation,[],[f62]) ).
% 2.82/0.99  
% 2.82/0.99  cnf(c_874,plain,
% 2.82/0.99      ( k8_relset_1(sK1,sK0,sK2,k7_relset_1(sK1,sK0,sK2,sK1)) != k1_relset_1(sK1,sK0,sK2)
% 2.82/0.99      | k7_relset_1(sK1,sK0,sK2,k8_relset_1(sK1,sK0,sK2,sK0)) != k2_relat_1(sK2) ),
% 2.82/0.99      inference(demodulation,[status(thm)],[c_795,c_21]) ).
% 2.82/0.99  
% 2.82/0.99  cnf(c_910,plain,
% 2.82/0.99      ( k8_relset_1(sK1,sK0,sK2,k7_relset_1(sK1,sK0,sK2,sK1)) != k1_relat_1(sK2)
% 2.82/0.99      | k7_relset_1(sK1,sK0,sK2,k8_relset_1(sK1,sK0,sK2,sK0)) != k2_relat_1(sK2) ),
% 2.82/0.99      inference(demodulation,[status(thm)],[c_835,c_874]) ).
% 2.82/0.99  
% 2.82/0.99  cnf(c_20,plain,
% 2.82/0.99      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 2.82/0.99      | k8_relset_1(X1,X2,X0,X3) = k10_relat_1(X0,X3) ),
% 2.82/0.99      inference(cnf_transformation,[],[f60]) ).
% 2.82/0.99  
% 2.82/0.99  cnf(c_320,plain,
% 2.82/0.99      ( k8_relset_1(X0,X1,X2,X3) = k10_relat_1(X2,X3)
% 2.82/0.99      | k1_zfmisc_1(k2_zfmisc_1(X0,X1)) != k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))
% 2.82/0.99      | sK2 != X2 ),
% 2.82/0.99      inference(resolution_lifted,[status(thm)],[c_20,c_22]) ).
% 2.82/0.99  
% 2.82/0.99  cnf(c_321,plain,
% 2.82/0.99      ( k8_relset_1(X0,X1,sK2,X2) = k10_relat_1(sK2,X2)
% 2.82/0.99      | k1_zfmisc_1(k2_zfmisc_1(X0,X1)) != k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)) ),
% 2.82/0.99      inference(unflattening,[status(thm)],[c_320]) ).
% 2.82/0.99  
% 2.82/0.99  cnf(c_838,plain,
% 2.82/0.99      ( k8_relset_1(sK1,sK0,sK2,X0) = k10_relat_1(sK2,X0) ),
% 2.82/0.99      inference(equality_resolution,[status(thm)],[c_321]) ).
% 2.82/0.99  
% 2.82/0.99  cnf(c_19,plain,
% 2.82/0.99      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 2.82/0.99      | k7_relset_1(X1,X2,X0,X3) = k9_relat_1(X0,X3) ),
% 2.82/0.99      inference(cnf_transformation,[],[f59]) ).
% 2.82/0.99  
% 2.82/0.99  cnf(c_329,plain,
% 2.82/0.99      ( k7_relset_1(X0,X1,X2,X3) = k9_relat_1(X2,X3)
% 2.82/0.99      | k1_zfmisc_1(k2_zfmisc_1(X0,X1)) != k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))
% 2.82/0.99      | sK2 != X2 ),
% 2.82/0.99      inference(resolution_lifted,[status(thm)],[c_19,c_22]) ).
% 2.82/0.99  
% 2.82/0.99  cnf(c_330,plain,
% 2.82/0.99      ( k7_relset_1(X0,X1,sK2,X2) = k9_relat_1(sK2,X2)
% 2.82/0.99      | k1_zfmisc_1(k2_zfmisc_1(X0,X1)) != k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)) ),
% 2.82/0.99      inference(unflattening,[status(thm)],[c_329]) ).
% 2.82/0.99  
% 2.82/0.99  cnf(c_871,plain,
% 2.82/0.99      ( k7_relset_1(sK1,sK0,sK2,X0) = k9_relat_1(sK2,X0) ),
% 2.82/0.99      inference(equality_resolution,[status(thm)],[c_330]) ).
% 2.82/0.99  
% 2.82/0.99  cnf(c_1312,plain,
% 2.82/0.99      ( k10_relat_1(sK2,k9_relat_1(sK2,sK1)) != k1_relat_1(sK2)
% 2.82/0.99      | k9_relat_1(sK2,k10_relat_1(sK2,sK0)) != k2_relat_1(sK2) ),
% 2.82/0.99      inference(demodulation,[status(thm)],[c_910,c_838,c_871]) ).
% 2.82/0.99  
% 2.82/0.99  cnf(c_2137,plain,
% 2.82/0.99      ( k10_relat_1(sK2,k2_relat_1(sK2)) != k1_relat_1(sK2)
% 2.82/0.99      | k9_relat_1(sK2,k10_relat_1(sK2,sK0)) != k2_relat_1(sK2) ),
% 2.82/0.99      inference(demodulation,[status(thm)],[c_1868,c_1312]) ).
% 2.82/0.99  
% 2.82/0.99  cnf(c_2711,plain,
% 2.82/0.99      ( k10_relat_1(sK2,k2_relat_1(sK2)) != k1_relat_1(sK2)
% 2.82/0.99      | k9_relat_1(sK2,k1_relat_1(sK2)) != k2_relat_1(sK2) ),
% 2.82/0.99      inference(demodulation,[status(thm)],[c_2544,c_2137]) ).
% 2.82/0.99  
% 2.82/0.99  cnf(contradiction,plain,
% 2.82/0.99      ( $false ),
% 2.82/0.99      inference(minisat,[status(thm)],[c_4222,c_2939,c_2711]) ).
% 2.82/0.99  
% 2.82/0.99  
% 2.82/0.99  % SZS output end CNFRefutation for theBenchmark.p
% 2.82/0.99  
% 2.82/0.99  ------                               Statistics
% 2.82/0.99  
% 2.82/0.99  ------ General
% 2.82/0.99  
% 2.82/0.99  abstr_ref_over_cycles:                  0
% 2.82/0.99  abstr_ref_under_cycles:                 0
% 2.82/0.99  gc_basic_clause_elim:                   0
% 2.82/0.99  forced_gc_time:                         0
% 2.82/0.99  parsing_time:                           0.012
% 2.82/0.99  unif_index_cands_time:                  0.
% 2.82/0.99  unif_index_add_time:                    0.
% 2.82/0.99  orderings_time:                         0.
% 2.82/0.99  out_proof_time:                         0.009
% 2.82/0.99  total_time:                             0.165
% 2.82/0.99  num_of_symbols:                         52
% 2.82/0.99  num_of_terms:                           5452
% 2.82/0.99  
% 2.82/0.99  ------ Preprocessing
% 2.82/0.99  
% 2.82/0.99  num_of_splits:                          0
% 2.82/0.99  num_of_split_atoms:                     0
% 2.82/0.99  num_of_reused_defs:                     0
% 2.82/0.99  num_eq_ax_congr_red:                    22
% 2.82/0.99  num_of_sem_filtered_clauses:            1
% 2.82/0.99  num_of_subtypes:                        0
% 2.82/0.99  monotx_restored_types:                  0
% 2.82/0.99  sat_num_of_epr_types:                   0
% 2.82/0.99  sat_num_of_non_cyclic_types:            0
% 2.82/0.99  sat_guarded_non_collapsed_types:        0
% 2.82/0.99  num_pure_diseq_elim:                    0
% 2.82/0.99  simp_replaced_by:                       0
% 2.82/0.99  res_preprocessed:                       109
% 2.82/0.99  prep_upred:                             0
% 2.82/0.99  prep_unflattend:                        7
% 2.82/0.99  smt_new_axioms:                         0
% 2.82/0.99  pred_elim_cands:                        2
% 2.82/0.99  pred_elim:                              3
% 2.82/0.99  pred_elim_cl:                           4
% 2.82/0.99  pred_elim_cycles:                       5
% 2.82/0.99  merged_defs:                            0
% 2.82/0.99  merged_defs_ncl:                        0
% 2.82/0.99  bin_hyper_res:                          0
% 2.82/0.99  prep_cycles:                            4
% 2.82/0.99  pred_elim_time:                         0.002
% 2.82/0.99  splitting_time:                         0.
% 2.82/0.99  sem_filter_time:                        0.
% 2.82/0.99  monotx_time:                            0.
% 2.82/0.99  subtype_inf_time:                       0.
% 2.82/0.99  
% 2.82/0.99  ------ Problem properties
% 2.82/0.99  
% 2.82/0.99  clauses:                                18
% 2.82/0.99  conjectures:                            1
% 2.82/0.99  epr:                                    2
% 2.82/0.99  horn:                                   18
% 2.82/0.99  ground:                                 1
% 2.82/0.99  unary:                                  5
% 2.82/0.99  binary:                                 6
% 2.82/0.99  lits:                                   38
% 2.82/0.99  lits_eq:                                21
% 2.82/0.99  fd_pure:                                0
% 2.82/0.99  fd_pseudo:                              0
% 2.82/0.99  fd_cond:                                0
% 2.82/0.99  fd_pseudo_cond:                         1
% 2.82/0.99  ac_symbols:                             0
% 2.82/0.99  
% 2.82/0.99  ------ Propositional Solver
% 2.82/0.99  
% 2.82/0.99  prop_solver_calls:                      29
% 2.82/0.99  prop_fast_solver_calls:                 658
% 2.82/0.99  smt_solver_calls:                       0
% 2.82/0.99  smt_fast_solver_calls:                  0
% 2.82/0.99  prop_num_of_clauses:                    1987
% 2.82/0.99  prop_preprocess_simplified:             5239
% 2.82/0.99  prop_fo_subsumed:                       8
% 2.82/0.99  prop_solver_time:                       0.
% 2.82/0.99  smt_solver_time:                        0.
% 2.82/0.99  smt_fast_solver_time:                   0.
% 2.82/0.99  prop_fast_solver_time:                  0.
% 2.82/0.99  prop_unsat_core_time:                   0.
% 2.82/0.99  
% 2.82/0.99  ------ QBF
% 2.82/0.99  
% 2.82/0.99  qbf_q_res:                              0
% 2.82/0.99  qbf_num_tautologies:                    0
% 2.82/0.99  qbf_prep_cycles:                        0
% 2.82/0.99  
% 2.82/0.99  ------ BMC1
% 2.82/0.99  
% 2.82/0.99  bmc1_current_bound:                     -1
% 2.82/0.99  bmc1_last_solved_bound:                 -1
% 2.82/0.99  bmc1_unsat_core_size:                   -1
% 2.82/0.99  bmc1_unsat_core_parents_size:           -1
% 2.82/0.99  bmc1_merge_next_fun:                    0
% 2.82/0.99  bmc1_unsat_core_clauses_time:           0.
% 2.82/0.99  
% 2.82/0.99  ------ Instantiation
% 2.82/0.99  
% 2.82/0.99  inst_num_of_clauses:                    642
% 2.82/0.99  inst_num_in_passive:                    286
% 2.82/0.99  inst_num_in_active:                     322
% 2.82/0.99  inst_num_in_unprocessed:                34
% 2.82/0.99  inst_num_of_loops:                      330
% 2.82/0.99  inst_num_of_learning_restarts:          0
% 2.82/0.99  inst_num_moves_active_passive:          5
% 2.82/0.99  inst_lit_activity:                      0
% 2.82/0.99  inst_lit_activity_moves:                0
% 2.82/0.99  inst_num_tautologies:                   0
% 2.82/0.99  inst_num_prop_implied:                  0
% 2.82/0.99  inst_num_existing_simplified:           0
% 2.82/0.99  inst_num_eq_res_simplified:             0
% 2.82/0.99  inst_num_child_elim:                    0
% 2.82/0.99  inst_num_of_dismatching_blockings:      81
% 2.82/0.99  inst_num_of_non_proper_insts:           543
% 2.82/0.99  inst_num_of_duplicates:                 0
% 2.82/0.99  inst_inst_num_from_inst_to_res:         0
% 2.82/0.99  inst_dismatching_checking_time:         0.
% 2.82/0.99  
% 2.82/0.99  ------ Resolution
% 2.82/0.99  
% 2.82/0.99  res_num_of_clauses:                     0
% 2.82/0.99  res_num_in_passive:                     0
% 2.82/0.99  res_num_in_active:                      0
% 2.82/0.99  res_num_of_loops:                       113
% 2.82/0.99  res_forward_subset_subsumed:            67
% 2.82/0.99  res_backward_subset_subsumed:           2
% 2.82/0.99  res_forward_subsumed:                   0
% 2.82/0.99  res_backward_subsumed:                  0
% 2.82/0.99  res_forward_subsumption_resolution:     0
% 2.82/0.99  res_backward_subsumption_resolution:    0
% 2.82/0.99  res_clause_to_clause_subsumption:       128
% 2.82/0.99  res_orphan_elimination:                 0
% 2.82/0.99  res_tautology_del:                      60
% 2.82/0.99  res_num_eq_res_simplified:              0
% 2.82/0.99  res_num_sel_changes:                    0
% 2.82/0.99  res_moves_from_active_to_pass:          0
% 2.82/0.99  
% 2.82/0.99  ------ Superposition
% 2.82/0.99  
% 2.82/0.99  sup_time_total:                         0.
% 2.82/0.99  sup_time_generating:                    0.
% 2.82/0.99  sup_time_sim_full:                      0.
% 2.82/0.99  sup_time_sim_immed:                     0.
% 2.82/0.99  
% 2.82/0.99  sup_num_of_clauses:                     69
% 2.82/0.99  sup_num_in_active:                      61
% 2.82/0.99  sup_num_in_passive:                     8
% 2.82/0.99  sup_num_of_loops:                       65
% 2.82/0.99  sup_fw_superposition:                   46
% 2.82/0.99  sup_bw_superposition:                   9
% 2.82/0.99  sup_immediate_simplified:               14
% 2.82/0.99  sup_given_eliminated:                   0
% 2.82/0.99  comparisons_done:                       0
% 2.82/0.99  comparisons_avoided:                    0
% 2.82/0.99  
% 2.82/0.99  ------ Simplifications
% 2.82/0.99  
% 2.82/0.99  
% 2.82/0.99  sim_fw_subset_subsumed:                 0
% 2.82/0.99  sim_bw_subset_subsumed:                 1
% 2.82/0.99  sim_fw_subsumed:                        3
% 2.82/0.99  sim_bw_subsumed:                        0
% 2.82/0.99  sim_fw_subsumption_res:                 0
% 2.82/0.99  sim_bw_subsumption_res:                 0
% 2.82/0.99  sim_tautology_del:                      0
% 2.82/0.99  sim_eq_tautology_del:                   4
% 2.82/0.99  sim_eq_res_simp:                        1
% 2.82/0.99  sim_fw_demodulated:                     4
% 2.82/0.99  sim_bw_demodulated:                     5
% 2.82/0.99  sim_light_normalised:                   11
% 2.82/0.99  sim_joinable_taut:                      0
% 2.82/0.99  sim_joinable_simp:                      0
% 2.82/0.99  sim_ac_normalised:                      0
% 2.82/0.99  sim_smt_subsumption:                    0
% 2.82/0.99  
%------------------------------------------------------------------------------
