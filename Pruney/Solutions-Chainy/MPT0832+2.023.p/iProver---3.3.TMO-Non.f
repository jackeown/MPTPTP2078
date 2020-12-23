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
% DateTime   : Thu Dec  3 11:55:50 EST 2020

% Result     : Timeout 59.24s
% Output     : None 
% Verified   : 
% Statistics : Number of formulae       :  176 (1399 expanded)
%              Number of clauses        :  107 ( 669 expanded)
%              Number of leaves         :   20 ( 244 expanded)
%              Depth                    :   22
%              Number of atoms          :  395 (3113 expanded)
%              Number of equality atoms :  164 ( 538 expanded)
%              Maximal formula depth    :    8 (   4 average)
%              Maximal clause size      :    5 (   2 average)
%              Maximal term depth       :    6 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f19,conjecture,(
    ! [X0,X1,X2,X3] :
      ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X2,X0)))
     => m1_subset_1(k6_relset_1(X2,X0,X1,X3),k1_zfmisc_1(k2_zfmisc_1(X2,X1))) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f20,negated_conjecture,(
    ~ ! [X0,X1,X2,X3] :
        ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X2,X0)))
       => m1_subset_1(k6_relset_1(X2,X0,X1,X3),k1_zfmisc_1(k2_zfmisc_1(X2,X1))) ) ),
    inference(negated_conjecture,[],[f19])).

fof(f44,plain,(
    ? [X0,X1,X2,X3] :
      ( ~ m1_subset_1(k6_relset_1(X2,X0,X1,X3),k1_zfmisc_1(k2_zfmisc_1(X2,X1)))
      & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X2,X0))) ) ),
    inference(ennf_transformation,[],[f20])).

fof(f47,plain,
    ( ? [X0,X1,X2,X3] :
        ( ~ m1_subset_1(k6_relset_1(X2,X0,X1,X3),k1_zfmisc_1(k2_zfmisc_1(X2,X1)))
        & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X2,X0))) )
   => ( ~ m1_subset_1(k6_relset_1(sK2,sK0,sK1,sK3),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1)))
      & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK2,sK0))) ) ),
    introduced(choice_axiom,[])).

fof(f48,plain,
    ( ~ m1_subset_1(k6_relset_1(sK2,sK0,sK1,sK3),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1)))
    & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK2,sK0))) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3])],[f44,f47])).

fof(f69,plain,(
    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK2,sK0))) ),
    inference(cnf_transformation,[],[f48])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f45,plain,(
    ! [X0,X1] :
      ( ( m1_subset_1(X0,k1_zfmisc_1(X1))
        | ~ r1_tarski(X0,X1) )
      & ( r1_tarski(X0,X1)
        | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ) ) ),
    inference(nnf_transformation,[],[f2])).

fof(f50,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ) ),
    inference(cnf_transformation,[],[f45])).

fof(f3,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(X0))
         => v1_relat_1(X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f24,plain,(
    ! [X0] :
      ( ! [X1] :
          ( v1_relat_1(X1)
          | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f52,plain,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f51,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f45])).

fof(f6,axiom,(
    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f56,plain,(
    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1)) ),
    inference(cnf_transformation,[],[f6])).

fof(f7,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => r1_tarski(k2_relat_1(k8_relat_1(X0,X1)),X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f27,plain,(
    ! [X0,X1] :
      ( r1_tarski(k2_relat_1(k8_relat_1(X0,X1)),X0)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f57,plain,(
    ! [X0,X1] :
      ( r1_tarski(k2_relat_1(k8_relat_1(X0,X1)),X0)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f9,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ( r1_tarski(k2_relat_1(X1),X0)
       => k8_relat_1(X0,X1) = X1 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f29,plain,(
    ! [X0,X1] :
      ( k8_relat_1(X0,X1) = X1
      | ~ r1_tarski(k2_relat_1(X1),X0)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f30,plain,(
    ! [X0,X1] :
      ( k8_relat_1(X0,X1) = X1
      | ~ r1_tarski(k2_relat_1(X1),X0)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f29])).

fof(f59,plain,(
    ! [X0,X1] :
      ( k8_relat_1(X0,X1) = X1
      | ~ r1_tarski(k2_relat_1(X1),X0)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f5,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => v1_relat_1(k8_relat_1(X0,X1)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f26,plain,(
    ! [X0,X1] :
      ( v1_relat_1(k8_relat_1(X0,X1))
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f55,plain,(
    ! [X0,X1] :
      ( v1_relat_1(k8_relat_1(X0,X1))
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f11,axiom,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
     => ( r1_tarski(X0,X1)
       => k8_relat_1(X0,X2) = k8_relat_1(X0,k8_relat_1(X1,X2)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f32,plain,(
    ! [X0,X1,X2] :
      ( k8_relat_1(X0,X2) = k8_relat_1(X0,k8_relat_1(X1,X2))
      | ~ r1_tarski(X0,X1)
      | ~ v1_relat_1(X2) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f33,plain,(
    ! [X0,X1,X2] :
      ( k8_relat_1(X0,X2) = k8_relat_1(X0,k8_relat_1(X1,X2))
      | ~ r1_tarski(X0,X1)
      | ~ v1_relat_1(X2) ) ),
    inference(flattening,[],[f32])).

fof(f61,plain,(
    ! [X2,X0,X1] :
      ( k8_relat_1(X0,X2) = k8_relat_1(X0,k8_relat_1(X1,X2))
      | ~ r1_tarski(X0,X1)
      | ~ v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f33])).

fof(f10,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => k8_relat_1(k2_relat_1(X0),X0) = X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f31,plain,(
    ! [X0] :
      ( k8_relat_1(k2_relat_1(X0),X0) = X0
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f60,plain,(
    ! [X0] :
      ( k8_relat_1(k2_relat_1(X0),X0) = X0
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f8,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => r1_tarski(k2_relat_1(k8_relat_1(X0,X1)),k2_relat_1(X1)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f28,plain,(
    ! [X0,X1] :
      ( r1_tarski(k2_relat_1(k8_relat_1(X0,X1)),k2_relat_1(X1))
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f58,plain,(
    ! [X0,X1] :
      ( r1_tarski(k2_relat_1(k8_relat_1(X0,X1)),k2_relat_1(X1))
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f13,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => ( v5_relat_1(X2,X1)
        & v4_relat_1(X2,X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f21,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => v5_relat_1(X2,X1) ) ),
    inference(pure_predicate_removal,[],[f13])).

fof(f36,plain,(
    ! [X0,X1,X2] :
      ( v5_relat_1(X2,X1)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f21])).

fof(f63,plain,(
    ! [X2,X0,X1] :
      ( v5_relat_1(X2,X1)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f36])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ( v5_relat_1(X1,X0)
      <=> r1_tarski(k2_relat_1(X1),X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f25,plain,(
    ! [X0,X1] :
      ( ( v5_relat_1(X1,X0)
      <=> r1_tarski(k2_relat_1(X1),X0) )
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f46,plain,(
    ! [X0,X1] :
      ( ( ( v5_relat_1(X1,X0)
          | ~ r1_tarski(k2_relat_1(X1),X0) )
        & ( r1_tarski(k2_relat_1(X1),X0)
          | ~ v5_relat_1(X1,X0) ) )
      | ~ v1_relat_1(X1) ) ),
    inference(nnf_transformation,[],[f25])).

fof(f53,plain,(
    ! [X0,X1] :
      ( r1_tarski(k2_relat_1(X1),X0)
      | ~ v5_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f46])).

fof(f1,axiom,(
    ! [X0,X1,X2] :
      ( ( r1_tarski(X1,X2)
        & r1_tarski(X0,X1) )
     => r1_tarski(X0,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f22,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,X2)
      | ~ r1_tarski(X1,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f23,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,X2)
      | ~ r1_tarski(X1,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(flattening,[],[f22])).

fof(f49,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(X0,X2)
      | ~ r1_tarski(X1,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f12,axiom,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
     => ( r1_tarski(X0,X1)
       => r1_tarski(k8_relat_1(X0,X2),k8_relat_1(X1,X2)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f34,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(k8_relat_1(X0,X2),k8_relat_1(X1,X2))
      | ~ r1_tarski(X0,X1)
      | ~ v1_relat_1(X2) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f35,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(k8_relat_1(X0,X2),k8_relat_1(X1,X2))
      | ~ r1_tarski(X0,X1)
      | ~ v1_relat_1(X2) ) ),
    inference(flattening,[],[f34])).

fof(f62,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(k8_relat_1(X0,X2),k8_relat_1(X1,X2))
      | ~ r1_tarski(X0,X1)
      | ~ v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f35])).

fof(f18,axiom,(
    ! [X0,X1,X2,X3] :
      ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
     => ( r1_tarski(X0,X3)
       => m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f42,plain,(
    ! [X0,X1,X2,X3] :
      ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
      | ~ r1_tarski(X0,X3)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) ) ),
    inference(ennf_transformation,[],[f18])).

fof(f43,plain,(
    ! [X0,X1,X2,X3] :
      ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
      | ~ r1_tarski(X0,X3)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) ) ),
    inference(flattening,[],[f42])).

fof(f68,plain,(
    ! [X2,X0,X3,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
      | ~ r1_tarski(X0,X3)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) ) ),
    inference(cnf_transformation,[],[f43])).

fof(f15,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k1_relset_1(X0,X1,X2) = k1_relat_1(X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f38,plain,(
    ! [X0,X1,X2] :
      ( k1_relset_1(X0,X1,X2) = k1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f15])).

fof(f65,plain,(
    ! [X2,X0,X1] :
      ( k1_relset_1(X0,X1,X2) = k1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f38])).

fof(f14,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => m1_subset_1(k1_relset_1(X0,X1,X2),k1_zfmisc_1(X0)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f37,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(k1_relset_1(X0,X1,X2),k1_zfmisc_1(X0))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f64,plain,(
    ! [X2,X0,X1] :
      ( m1_subset_1(k1_relset_1(X0,X1,X2),k1_zfmisc_1(X0))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f37])).

fof(f17,axiom,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
     => ( ( r1_tarski(k2_relat_1(X2),X1)
          & r1_tarski(k1_relat_1(X2),X0) )
       => m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f40,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ r1_tarski(k2_relat_1(X2),X1)
      | ~ r1_tarski(k1_relat_1(X2),X0)
      | ~ v1_relat_1(X2) ) ),
    inference(ennf_transformation,[],[f17])).

fof(f41,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ r1_tarski(k2_relat_1(X2),X1)
      | ~ r1_tarski(k1_relat_1(X2),X0)
      | ~ v1_relat_1(X2) ) ),
    inference(flattening,[],[f40])).

fof(f67,plain,(
    ! [X2,X0,X1] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ r1_tarski(k2_relat_1(X2),X1)
      | ~ r1_tarski(k1_relat_1(X2),X0)
      | ~ v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f41])).

fof(f16,axiom,(
    ! [X0,X1,X2,X3] :
      ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k8_relat_1(X2,X3) = k6_relset_1(X0,X1,X2,X3) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f39,plain,(
    ! [X0,X1,X2,X3] :
      ( k8_relat_1(X2,X3) = k6_relset_1(X0,X1,X2,X3)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f16])).

fof(f66,plain,(
    ! [X2,X0,X3,X1] :
      ( k8_relat_1(X2,X3) = k6_relset_1(X0,X1,X2,X3)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f39])).

fof(f70,plain,(
    ~ m1_subset_1(k6_relset_1(sK2,sK0,sK1,sK3),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) ),
    inference(cnf_transformation,[],[f48])).

cnf(c_21,negated_conjecture,
    ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK2,sK0))) ),
    inference(cnf_transformation,[],[f69])).

cnf(c_963,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK2,sK0))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_21])).

cnf(c_2,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | r1_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f50])).

cnf(c_978,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(X1)) != iProver_top
    | r1_tarski(X0,X1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2])).

cnf(c_1336,plain,
    ( r1_tarski(sK3,k2_zfmisc_1(sK2,sK0)) = iProver_top ),
    inference(superposition,[status(thm)],[c_963,c_978])).

cnf(c_3,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | ~ v1_relat_1(X1)
    | v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f52])).

cnf(c_1,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(X1))
    | ~ r1_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f51])).

cnf(c_178,plain,
    ( ~ r1_tarski(X0,X1)
    | m1_subset_1(X0,k1_zfmisc_1(X1)) ),
    inference(prop_impl,[status(thm)],[c_1])).

cnf(c_179,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(X1))
    | ~ r1_tarski(X0,X1) ),
    inference(renaming,[status(thm)],[c_178])).

cnf(c_216,plain,
    ( ~ r1_tarski(X0,X1)
    | ~ v1_relat_1(X1)
    | v1_relat_1(X0) ),
    inference(bin_hyper_res,[status(thm)],[c_3,c_179])).

cnf(c_962,plain,
    ( r1_tarski(X0,X1) != iProver_top
    | v1_relat_1(X1) != iProver_top
    | v1_relat_1(X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_216])).

cnf(c_2087,plain,
    ( v1_relat_1(k2_zfmisc_1(sK2,sK0)) != iProver_top
    | v1_relat_1(sK3) = iProver_top ),
    inference(superposition,[status(thm)],[c_1336,c_962])).

cnf(c_22,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK2,sK0))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_21])).

cnf(c_1116,plain,
    ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK2,sK0)))
    | r1_tarski(sK3,k2_zfmisc_1(sK2,sK0)) ),
    inference(instantiation,[status(thm)],[c_2])).

cnf(c_1117,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK2,sK0))) != iProver_top
    | r1_tarski(sK3,k2_zfmisc_1(sK2,sK0)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1116])).

cnf(c_1176,plain,
    ( ~ r1_tarski(X0,k2_zfmisc_1(X1,X2))
    | v1_relat_1(X0)
    | ~ v1_relat_1(k2_zfmisc_1(X1,X2)) ),
    inference(instantiation,[status(thm)],[c_216])).

cnf(c_1403,plain,
    ( ~ r1_tarski(sK3,k2_zfmisc_1(sK2,sK0))
    | ~ v1_relat_1(k2_zfmisc_1(sK2,sK0))
    | v1_relat_1(sK3) ),
    inference(instantiation,[status(thm)],[c_1176])).

cnf(c_1404,plain,
    ( r1_tarski(sK3,k2_zfmisc_1(sK2,sK0)) != iProver_top
    | v1_relat_1(k2_zfmisc_1(sK2,sK0)) != iProver_top
    | v1_relat_1(sK3) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1403])).

cnf(c_7,plain,
    ( v1_relat_1(k2_zfmisc_1(X0,X1)) ),
    inference(cnf_transformation,[],[f56])).

cnf(c_1772,plain,
    ( v1_relat_1(k2_zfmisc_1(sK2,sK0)) ),
    inference(instantiation,[status(thm)],[c_7])).

cnf(c_1773,plain,
    ( v1_relat_1(k2_zfmisc_1(sK2,sK0)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1772])).

cnf(c_2371,plain,
    ( v1_relat_1(sK3) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_2087,c_22,c_1117,c_1404,c_1773])).

cnf(c_8,plain,
    ( r1_tarski(k2_relat_1(k8_relat_1(X0,X1)),X0)
    | ~ v1_relat_1(X1) ),
    inference(cnf_transformation,[],[f57])).

cnf(c_975,plain,
    ( r1_tarski(k2_relat_1(k8_relat_1(X0,X1)),X0) = iProver_top
    | v1_relat_1(X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_8])).

cnf(c_10,plain,
    ( ~ r1_tarski(k2_relat_1(X0),X1)
    | ~ v1_relat_1(X0)
    | k8_relat_1(X1,X0) = X0 ),
    inference(cnf_transformation,[],[f59])).

cnf(c_973,plain,
    ( k8_relat_1(X0,X1) = X1
    | r1_tarski(k2_relat_1(X1),X0) != iProver_top
    | v1_relat_1(X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_10])).

cnf(c_3218,plain,
    ( k8_relat_1(X0,k8_relat_1(X0,X1)) = k8_relat_1(X0,X1)
    | v1_relat_1(X1) != iProver_top
    | v1_relat_1(k8_relat_1(X0,X1)) != iProver_top ),
    inference(superposition,[status(thm)],[c_975,c_973])).

cnf(c_6,plain,
    ( ~ v1_relat_1(X0)
    | v1_relat_1(k8_relat_1(X1,X0)) ),
    inference(cnf_transformation,[],[f55])).

cnf(c_977,plain,
    ( v1_relat_1(X0) != iProver_top
    | v1_relat_1(k8_relat_1(X1,X0)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_6])).

cnf(c_187051,plain,
    ( k8_relat_1(X0,k8_relat_1(X0,X1)) = k8_relat_1(X0,X1)
    | v1_relat_1(X1) != iProver_top ),
    inference(forward_subsumption_resolution,[status(thm)],[c_3218,c_977])).

cnf(c_187057,plain,
    ( k8_relat_1(X0,k8_relat_1(X0,sK3)) = k8_relat_1(X0,sK3) ),
    inference(superposition,[status(thm)],[c_2371,c_187051])).

cnf(c_189939,plain,
    ( r1_tarski(k2_relat_1(k8_relat_1(X0,sK3)),X0) = iProver_top
    | v1_relat_1(k8_relat_1(X0,sK3)) != iProver_top ),
    inference(superposition,[status(thm)],[c_187057,c_975])).

cnf(c_2817,plain,
    ( r1_tarski(k2_relat_1(k8_relat_1(X0,sK3)),X0)
    | ~ v1_relat_1(sK3) ),
    inference(instantiation,[status(thm)],[c_8])).

cnf(c_2818,plain,
    ( r1_tarski(k2_relat_1(k8_relat_1(X0,sK3)),X0) = iProver_top
    | v1_relat_1(sK3) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2817])).

cnf(c_190961,plain,
    ( r1_tarski(k2_relat_1(k8_relat_1(X0,sK3)),X0) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_189939,c_22,c_1117,c_1404,c_1773,c_2818])).

cnf(c_12,plain,
    ( ~ r1_tarski(X0,X1)
    | ~ v1_relat_1(X2)
    | k8_relat_1(X0,k8_relat_1(X1,X2)) = k8_relat_1(X0,X2) ),
    inference(cnf_transformation,[],[f61])).

cnf(c_971,plain,
    ( k8_relat_1(X0,k8_relat_1(X1,X2)) = k8_relat_1(X0,X2)
    | r1_tarski(X0,X1) != iProver_top
    | v1_relat_1(X2) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_12])).

cnf(c_190974,plain,
    ( k8_relat_1(k2_relat_1(k8_relat_1(X0,sK3)),k8_relat_1(X0,X1)) = k8_relat_1(k2_relat_1(k8_relat_1(X0,sK3)),X1)
    | v1_relat_1(X1) != iProver_top ),
    inference(superposition,[status(thm)],[c_190961,c_971])).

cnf(c_201208,plain,
    ( k8_relat_1(k2_relat_1(k8_relat_1(X0,sK3)),k8_relat_1(X0,sK3)) = k8_relat_1(k2_relat_1(k8_relat_1(X0,sK3)),sK3) ),
    inference(superposition,[status(thm)],[c_2371,c_190974])).

cnf(c_11,plain,
    ( ~ v1_relat_1(X0)
    | k8_relat_1(k2_relat_1(X0),X0) = X0 ),
    inference(cnf_transformation,[],[f60])).

cnf(c_972,plain,
    ( k8_relat_1(k2_relat_1(X0),X0) = X0
    | v1_relat_1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_11])).

cnf(c_1204,plain,
    ( k8_relat_1(k2_relat_1(k8_relat_1(X0,X1)),k8_relat_1(X0,X1)) = k8_relat_1(X0,X1)
    | v1_relat_1(X1) != iProver_top ),
    inference(superposition,[status(thm)],[c_977,c_972])).

cnf(c_16011,plain,
    ( k8_relat_1(k2_relat_1(k8_relat_1(X0,sK3)),k8_relat_1(X0,sK3)) = k8_relat_1(X0,sK3) ),
    inference(superposition,[status(thm)],[c_2371,c_1204])).

cnf(c_201428,plain,
    ( k8_relat_1(k2_relat_1(k8_relat_1(X0,sK3)),sK3) = k8_relat_1(X0,sK3) ),
    inference(light_normalisation,[status(thm)],[c_201208,c_16011])).

cnf(c_9,plain,
    ( r1_tarski(k2_relat_1(k8_relat_1(X0,X1)),k2_relat_1(X1))
    | ~ v1_relat_1(X1) ),
    inference(cnf_transformation,[],[f58])).

cnf(c_974,plain,
    ( r1_tarski(k2_relat_1(k8_relat_1(X0,X1)),k2_relat_1(X1)) = iProver_top
    | v1_relat_1(X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_9])).

cnf(c_14,plain,
    ( v5_relat_1(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) ),
    inference(cnf_transformation,[],[f63])).

cnf(c_5,plain,
    ( ~ v5_relat_1(X0,X1)
    | r1_tarski(k2_relat_1(X0),X1)
    | ~ v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f53])).

cnf(c_294,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | r1_tarski(k2_relat_1(X0),X2)
    | ~ v1_relat_1(X0) ),
    inference(resolution,[status(thm)],[c_14,c_5])).

cnf(c_961,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) != iProver_top
    | r1_tarski(k2_relat_1(X0),X2) = iProver_top
    | v1_relat_1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_294])).

cnf(c_1501,plain,
    ( r1_tarski(k2_relat_1(sK3),sK0) = iProver_top
    | v1_relat_1(sK3) != iProver_top ),
    inference(superposition,[status(thm)],[c_963,c_961])).

cnf(c_1916,plain,
    ( r1_tarski(k2_relat_1(sK3),sK0) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_1501,c_22,c_1117,c_1404,c_1773])).

cnf(c_0,plain,
    ( ~ r1_tarski(X0,X1)
    | ~ r1_tarski(X2,X0)
    | r1_tarski(X2,X1) ),
    inference(cnf_transformation,[],[f49])).

cnf(c_980,plain,
    ( r1_tarski(X0,X1) != iProver_top
    | r1_tarski(X2,X0) != iProver_top
    | r1_tarski(X2,X1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_0])).

cnf(c_3251,plain,
    ( r1_tarski(X0,k2_relat_1(sK3)) != iProver_top
    | r1_tarski(X0,sK0) = iProver_top ),
    inference(superposition,[status(thm)],[c_1916,c_980])).

cnf(c_3788,plain,
    ( r1_tarski(k2_relat_1(k8_relat_1(X0,sK3)),sK0) = iProver_top
    | v1_relat_1(sK3) != iProver_top ),
    inference(superposition,[status(thm)],[c_974,c_3251])).

cnf(c_5377,plain,
    ( r1_tarski(k2_relat_1(k8_relat_1(X0,sK3)),sK0) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_3788,c_22,c_1117,c_1404,c_1773])).

cnf(c_3220,plain,
    ( k8_relat_1(sK0,sK3) = sK3
    | v1_relat_1(sK3) != iProver_top ),
    inference(superposition,[status(thm)],[c_1916,c_973])).

cnf(c_3778,plain,
    ( k8_relat_1(sK0,sK3) = sK3 ),
    inference(global_propositional_subsumption,[status(thm)],[c_3220,c_22,c_1117,c_1404,c_1773])).

cnf(c_13,plain,
    ( ~ r1_tarski(X0,X1)
    | r1_tarski(k8_relat_1(X0,X2),k8_relat_1(X1,X2))
    | ~ v1_relat_1(X2) ),
    inference(cnf_transformation,[],[f62])).

cnf(c_970,plain,
    ( r1_tarski(X0,X1) != iProver_top
    | r1_tarski(k8_relat_1(X0,X2),k8_relat_1(X1,X2)) = iProver_top
    | v1_relat_1(X2) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_13])).

cnf(c_4404,plain,
    ( r1_tarski(X0,sK0) != iProver_top
    | r1_tarski(k8_relat_1(X0,sK3),sK3) = iProver_top
    | v1_relat_1(sK3) != iProver_top ),
    inference(superposition,[status(thm)],[c_3778,c_970])).

cnf(c_12177,plain,
    ( r1_tarski(k8_relat_1(X0,sK3),sK3) = iProver_top
    | r1_tarski(X0,sK0) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_4404,c_22,c_1117,c_1404,c_1773])).

cnf(c_12178,plain,
    ( r1_tarski(X0,sK0) != iProver_top
    | r1_tarski(k8_relat_1(X0,sK3),sK3) = iProver_top ),
    inference(renaming,[status(thm)],[c_12177])).

cnf(c_19,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ r1_tarski(X3,X0) ),
    inference(cnf_transformation,[],[f68])).

cnf(c_965,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) != iProver_top
    | m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) = iProver_top
    | r1_tarski(X3,X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_19])).

cnf(c_2724,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(sK2,sK0))) = iProver_top
    | r1_tarski(X0,sK3) != iProver_top ),
    inference(superposition,[status(thm)],[c_963,c_965])).

cnf(c_16,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k1_relset_1(X1,X2,X0) = k1_relat_1(X0) ),
    inference(cnf_transformation,[],[f65])).

cnf(c_968,plain,
    ( k1_relset_1(X0,X1,X2) = k1_relat_1(X2)
    | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_16])).

cnf(c_3583,plain,
    ( k1_relset_1(sK2,sK0,X0) = k1_relat_1(X0)
    | r1_tarski(X0,sK3) != iProver_top ),
    inference(superposition,[status(thm)],[c_2724,c_968])).

cnf(c_12194,plain,
    ( k1_relset_1(sK2,sK0,k8_relat_1(X0,sK3)) = k1_relat_1(k8_relat_1(X0,sK3))
    | r1_tarski(X0,sK0) != iProver_top ),
    inference(superposition,[status(thm)],[c_12178,c_3583])).

cnf(c_12256,plain,
    ( k1_relset_1(sK2,sK0,k8_relat_1(k2_relat_1(k8_relat_1(X0,sK3)),sK3)) = k1_relat_1(k8_relat_1(k2_relat_1(k8_relat_1(X0,sK3)),sK3)) ),
    inference(superposition,[status(thm)],[c_5377,c_12194])).

cnf(c_15,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | m1_subset_1(k1_relset_1(X1,X2,X0),k1_zfmisc_1(X1)) ),
    inference(cnf_transformation,[],[f64])).

cnf(c_969,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) != iProver_top
    | m1_subset_1(k1_relset_1(X1,X2,X0),k1_zfmisc_1(X1)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_15])).

cnf(c_2972,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) != iProver_top
    | r1_tarski(k1_relset_1(X1,X2,X0),X1) = iProver_top ),
    inference(superposition,[status(thm)],[c_969,c_978])).

cnf(c_15489,plain,
    ( r1_tarski(X0,sK3) != iProver_top
    | r1_tarski(k1_relset_1(sK2,sK0,X0),sK2) = iProver_top ),
    inference(superposition,[status(thm)],[c_2724,c_2972])).

cnf(c_120811,plain,
    ( r1_tarski(k8_relat_1(k2_relat_1(k8_relat_1(X0,sK3)),sK3),sK3) != iProver_top
    | r1_tarski(k1_relat_1(k8_relat_1(k2_relat_1(k8_relat_1(X0,sK3)),sK3)),sK2) = iProver_top ),
    inference(superposition,[status(thm)],[c_12256,c_15489])).

cnf(c_206983,plain,
    ( r1_tarski(k8_relat_1(X0,sK3),sK3) != iProver_top
    | r1_tarski(k1_relat_1(k8_relat_1(X0,sK3)),sK2) = iProver_top ),
    inference(demodulation,[status(thm)],[c_201428,c_120811])).

cnf(c_2816,plain,
    ( r1_tarski(k2_relat_1(k8_relat_1(X0,sK3)),k2_relat_1(sK3))
    | ~ v1_relat_1(sK3) ),
    inference(instantiation,[status(thm)],[c_9])).

cnf(c_2822,plain,
    ( r1_tarski(k2_relat_1(k8_relat_1(X0,sK3)),k2_relat_1(sK3)) = iProver_top
    | v1_relat_1(sK3) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2816])).

cnf(c_2376,plain,
    ( k8_relat_1(k2_relat_1(sK3),sK3) = sK3 ),
    inference(superposition,[status(thm)],[c_2371,c_972])).

cnf(c_4403,plain,
    ( r1_tarski(X0,k2_relat_1(sK3)) != iProver_top
    | r1_tarski(k8_relat_1(X0,sK3),sK3) = iProver_top
    | v1_relat_1(sK3) != iProver_top ),
    inference(superposition,[status(thm)],[c_2376,c_970])).

cnf(c_54445,plain,
    ( r1_tarski(k8_relat_1(X0,sK3),sK3) = iProver_top
    | r1_tarski(X0,k2_relat_1(sK3)) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_4403,c_22,c_1117,c_1404,c_1773])).

cnf(c_54446,plain,
    ( r1_tarski(X0,k2_relat_1(sK3)) != iProver_top
    | r1_tarski(k8_relat_1(X0,sK3),sK3) = iProver_top ),
    inference(renaming,[status(thm)],[c_54445])).

cnf(c_207080,plain,
    ( r1_tarski(k8_relat_1(X0,sK3),sK3) = iProver_top
    | r1_tarski(k2_relat_1(k8_relat_1(X0,sK3)),k2_relat_1(sK3)) != iProver_top ),
    inference(superposition,[status(thm)],[c_201428,c_54446])).

cnf(c_231908,plain,
    ( r1_tarski(k1_relat_1(k8_relat_1(X0,sK3)),sK2) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_206983,c_22,c_1117,c_1404,c_1773,c_2822,c_207080])).

cnf(c_18,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ r1_tarski(k1_relat_1(X0),X1)
    | ~ r1_tarski(k2_relat_1(X0),X2)
    | ~ v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f67])).

cnf(c_966,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) = iProver_top
    | r1_tarski(k1_relat_1(X0),X1) != iProver_top
    | r1_tarski(k2_relat_1(X0),X2) != iProver_top
    | v1_relat_1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_18])).

cnf(c_17,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k6_relset_1(X1,X2,X3,X0) = k8_relat_1(X3,X0) ),
    inference(cnf_transformation,[],[f66])).

cnf(c_967,plain,
    ( k6_relset_1(X0,X1,X2,X3) = k8_relat_1(X2,X3)
    | m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_17])).

cnf(c_2957,plain,
    ( k6_relset_1(sK2,sK0,X0,sK3) = k8_relat_1(X0,sK3) ),
    inference(superposition,[status(thm)],[c_963,c_967])).

cnf(c_20,negated_conjecture,
    ( ~ m1_subset_1(k6_relset_1(sK2,sK0,sK1,sK3),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) ),
    inference(cnf_transformation,[],[f70])).

cnf(c_964,plain,
    ( m1_subset_1(k6_relset_1(sK2,sK0,sK1,sK3),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_20])).

cnf(c_3349,plain,
    ( m1_subset_1(k8_relat_1(sK1,sK3),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) != iProver_top ),
    inference(demodulation,[status(thm)],[c_2957,c_964])).

cnf(c_4341,plain,
    ( r1_tarski(k1_relat_1(k8_relat_1(sK1,sK3)),sK2) != iProver_top
    | r1_tarski(k2_relat_1(k8_relat_1(sK1,sK3)),sK1) != iProver_top
    | v1_relat_1(k8_relat_1(sK1,sK3)) != iProver_top ),
    inference(superposition,[status(thm)],[c_966,c_3349])).

cnf(c_231927,plain,
    ( r1_tarski(k2_relat_1(k8_relat_1(sK1,sK3)),sK1) != iProver_top
    | v1_relat_1(k8_relat_1(sK1,sK3)) != iProver_top ),
    inference(superposition,[status(thm)],[c_231908,c_4341])).

cnf(c_3250,plain,
    ( r1_tarski(X0,k2_zfmisc_1(sK2,sK0)) = iProver_top
    | r1_tarski(X0,sK3) != iProver_top ),
    inference(superposition,[status(thm)],[c_1336,c_980])).

cnf(c_4074,plain,
    ( r1_tarski(X0,sK3) != iProver_top
    | v1_relat_1(X0) = iProver_top
    | v1_relat_1(k2_zfmisc_1(sK2,sK0)) != iProver_top ),
    inference(superposition,[status(thm)],[c_3250,c_962])).

cnf(c_2815,plain,
    ( ~ r1_tarski(X0,sK3)
    | v1_relat_1(X0)
    | ~ v1_relat_1(sK3) ),
    inference(instantiation,[status(thm)],[c_216])).

cnf(c_2826,plain,
    ( r1_tarski(X0,sK3) != iProver_top
    | v1_relat_1(X0) = iProver_top
    | v1_relat_1(sK3) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2815])).

cnf(c_10131,plain,
    ( v1_relat_1(X0) = iProver_top
    | r1_tarski(X0,sK3) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_4074,c_22,c_1117,c_1404,c_1773,c_2826])).

cnf(c_10132,plain,
    ( r1_tarski(X0,sK3) != iProver_top
    | v1_relat_1(X0) = iProver_top ),
    inference(renaming,[status(thm)],[c_10131])).

cnf(c_12191,plain,
    ( r1_tarski(X0,sK0) != iProver_top
    | v1_relat_1(k8_relat_1(X0,sK3)) = iProver_top ),
    inference(superposition,[status(thm)],[c_12178,c_10132])).

cnf(c_2790,plain,
    ( v1_relat_1(k8_relat_1(X0,sK3))
    | ~ v1_relat_1(sK3) ),
    inference(instantiation,[status(thm)],[c_6])).

cnf(c_2801,plain,
    ( v1_relat_1(k8_relat_1(X0,sK3)) = iProver_top
    | v1_relat_1(sK3) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2790])).

cnf(c_79645,plain,
    ( v1_relat_1(k8_relat_1(X0,sK3)) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_12191,c_22,c_1117,c_1404,c_1773,c_2801])).

cnf(c_232138,plain,
    ( $false ),
    inference(forward_subsumption_resolution,[status(thm)],[c_231927,c_79645,c_190961])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.10  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.11  % Command    : iproveropt_run.sh %d %s
% 0.11/0.32  % Computer   : n002.cluster.edu
% 0.11/0.32  % Model      : x86_64 x86_64
% 0.11/0.32  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.11/0.32  % Memory     : 8042.1875MB
% 0.11/0.32  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.11/0.32  % CPULimit   : 60
% 0.11/0.32  % WCLimit    : 600
% 0.11/0.32  % DateTime   : Tue Dec  1 16:02:52 EST 2020
% 0.11/0.32  % CPUTime    : 
% 0.11/0.32  % Running in FOF mode
% 59.24/7.97  % SZS status Started for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 59.24/7.97  
% 59.24/7.97  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 59.24/7.97  
% 59.24/7.97  ------  iProver source info
% 59.24/7.97  
% 59.24/7.97  git: date: 2020-06-30 10:37:57 +0100
% 59.24/7.97  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 59.24/7.97  git: non_committed_changes: false
% 59.24/7.97  git: last_make_outside_of_git: false
% 59.24/7.97  
% 59.24/7.97  ------ 
% 59.24/7.97  
% 59.24/7.97  ------ Input Options
% 59.24/7.97  
% 59.24/7.97  --out_options                           all
% 59.24/7.97  --tptp_safe_out                         true
% 59.24/7.97  --problem_path                          ""
% 59.24/7.97  --include_path                          ""
% 59.24/7.97  --clausifier                            res/vclausify_rel
% 59.24/7.97  --clausifier_options                    --mode clausify
% 59.24/7.97  --stdin                                 false
% 59.24/7.97  --stats_out                             all
% 59.24/7.97  
% 59.24/7.97  ------ General Options
% 59.24/7.97  
% 59.24/7.97  --fof                                   false
% 59.24/7.97  --time_out_real                         305.
% 59.24/7.97  --time_out_virtual                      -1.
% 59.24/7.97  --symbol_type_check                     false
% 59.24/7.97  --clausify_out                          false
% 59.24/7.97  --sig_cnt_out                           false
% 59.24/7.97  --trig_cnt_out                          false
% 59.24/7.97  --trig_cnt_out_tolerance                1.
% 59.24/7.97  --trig_cnt_out_sk_spl                   false
% 59.24/7.97  --abstr_cl_out                          false
% 59.24/7.97  
% 59.24/7.97  ------ Global Options
% 59.24/7.97  
% 59.24/7.97  --schedule                              default
% 59.24/7.97  --add_important_lit                     false
% 59.24/7.97  --prop_solver_per_cl                    1000
% 59.24/7.97  --min_unsat_core                        false
% 59.24/7.97  --soft_assumptions                      false
% 59.24/7.97  --soft_lemma_size                       3
% 59.24/7.97  --prop_impl_unit_size                   0
% 59.24/7.97  --prop_impl_unit                        []
% 59.24/7.97  --share_sel_clauses                     true
% 59.24/7.97  --reset_solvers                         false
% 59.24/7.97  --bc_imp_inh                            [conj_cone]
% 59.24/7.97  --conj_cone_tolerance                   3.
% 59.24/7.97  --extra_neg_conj                        none
% 59.24/7.97  --large_theory_mode                     true
% 59.24/7.97  --prolific_symb_bound                   200
% 59.24/7.97  --lt_threshold                          2000
% 59.24/7.97  --clause_weak_htbl                      true
% 59.24/7.97  --gc_record_bc_elim                     false
% 59.24/7.97  
% 59.24/7.97  ------ Preprocessing Options
% 59.24/7.97  
% 59.24/7.97  --preprocessing_flag                    true
% 59.24/7.97  --time_out_prep_mult                    0.1
% 59.24/7.97  --splitting_mode                        input
% 59.24/7.97  --splitting_grd                         true
% 59.24/7.97  --splitting_cvd                         false
% 59.24/7.97  --splitting_cvd_svl                     false
% 59.24/7.97  --splitting_nvd                         32
% 59.24/7.97  --sub_typing                            true
% 59.24/7.97  --prep_gs_sim                           true
% 59.24/7.97  --prep_unflatten                        true
% 59.24/7.97  --prep_res_sim                          true
% 59.24/7.97  --prep_upred                            true
% 59.24/7.97  --prep_sem_filter                       exhaustive
% 59.24/7.97  --prep_sem_filter_out                   false
% 59.24/7.97  --pred_elim                             true
% 59.24/7.97  --res_sim_input                         true
% 59.24/7.97  --eq_ax_congr_red                       true
% 59.24/7.97  --pure_diseq_elim                       true
% 59.24/7.97  --brand_transform                       false
% 59.24/7.97  --non_eq_to_eq                          false
% 59.24/7.97  --prep_def_merge                        true
% 59.24/7.97  --prep_def_merge_prop_impl              false
% 59.24/7.97  --prep_def_merge_mbd                    true
% 59.24/7.97  --prep_def_merge_tr_red                 false
% 59.24/7.97  --prep_def_merge_tr_cl                  false
% 59.24/7.97  --smt_preprocessing                     true
% 59.24/7.97  --smt_ac_axioms                         fast
% 59.24/7.97  --preprocessed_out                      false
% 59.24/7.97  --preprocessed_stats                    false
% 59.24/7.97  
% 59.24/7.97  ------ Abstraction refinement Options
% 59.24/7.97  
% 59.24/7.97  --abstr_ref                             []
% 59.24/7.97  --abstr_ref_prep                        false
% 59.24/7.97  --abstr_ref_until_sat                   false
% 59.24/7.97  --abstr_ref_sig_restrict                funpre
% 59.24/7.97  --abstr_ref_af_restrict_to_split_sk     false
% 59.24/7.97  --abstr_ref_under                       []
% 59.24/7.97  
% 59.24/7.97  ------ SAT Options
% 59.24/7.97  
% 59.24/7.97  --sat_mode                              false
% 59.24/7.97  --sat_fm_restart_options                ""
% 59.24/7.97  --sat_gr_def                            false
% 59.24/7.97  --sat_epr_types                         true
% 59.24/7.97  --sat_non_cyclic_types                  false
% 59.24/7.97  --sat_finite_models                     false
% 59.24/7.97  --sat_fm_lemmas                         false
% 59.24/7.97  --sat_fm_prep                           false
% 59.24/7.97  --sat_fm_uc_incr                        true
% 59.24/7.97  --sat_out_model                         small
% 59.24/7.97  --sat_out_clauses                       false
% 59.24/7.97  
% 59.24/7.97  ------ QBF Options
% 59.24/7.97  
% 59.24/7.97  --qbf_mode                              false
% 59.24/7.97  --qbf_elim_univ                         false
% 59.24/7.97  --qbf_dom_inst                          none
% 59.24/7.97  --qbf_dom_pre_inst                      false
% 59.24/7.97  --qbf_sk_in                             false
% 59.24/7.97  --qbf_pred_elim                         true
% 59.24/7.97  --qbf_split                             512
% 59.24/7.97  
% 59.24/7.97  ------ BMC1 Options
% 59.24/7.97  
% 59.24/7.97  --bmc1_incremental                      false
% 59.24/7.97  --bmc1_axioms                           reachable_all
% 59.24/7.97  --bmc1_min_bound                        0
% 59.24/7.97  --bmc1_max_bound                        -1
% 59.24/7.97  --bmc1_max_bound_default                -1
% 59.24/7.97  --bmc1_symbol_reachability              true
% 59.24/7.97  --bmc1_property_lemmas                  false
% 59.24/7.97  --bmc1_k_induction                      false
% 59.24/7.97  --bmc1_non_equiv_states                 false
% 59.24/7.97  --bmc1_deadlock                         false
% 59.24/7.97  --bmc1_ucm                              false
% 59.24/7.97  --bmc1_add_unsat_core                   none
% 59.24/7.97  --bmc1_unsat_core_children              false
% 59.24/7.97  --bmc1_unsat_core_extrapolate_axioms    false
% 59.24/7.97  --bmc1_out_stat                         full
% 59.24/7.97  --bmc1_ground_init                      false
% 59.24/7.97  --bmc1_pre_inst_next_state              false
% 59.24/7.97  --bmc1_pre_inst_state                   false
% 59.24/7.97  --bmc1_pre_inst_reach_state             false
% 59.24/7.97  --bmc1_out_unsat_core                   false
% 59.24/7.97  --bmc1_aig_witness_out                  false
% 59.24/7.97  --bmc1_verbose                          false
% 59.24/7.97  --bmc1_dump_clauses_tptp                false
% 59.24/7.97  --bmc1_dump_unsat_core_tptp             false
% 59.24/7.97  --bmc1_dump_file                        -
% 59.24/7.97  --bmc1_ucm_expand_uc_limit              128
% 59.24/7.97  --bmc1_ucm_n_expand_iterations          6
% 59.24/7.97  --bmc1_ucm_extend_mode                  1
% 59.24/7.97  --bmc1_ucm_init_mode                    2
% 59.24/7.97  --bmc1_ucm_cone_mode                    none
% 59.24/7.97  --bmc1_ucm_reduced_relation_type        0
% 59.24/7.97  --bmc1_ucm_relax_model                  4
% 59.24/7.97  --bmc1_ucm_full_tr_after_sat            true
% 59.24/7.97  --bmc1_ucm_expand_neg_assumptions       false
% 59.24/7.97  --bmc1_ucm_layered_model                none
% 59.24/7.97  --bmc1_ucm_max_lemma_size               10
% 59.24/7.97  
% 59.24/7.97  ------ AIG Options
% 59.24/7.97  
% 59.24/7.97  --aig_mode                              false
% 59.24/7.97  
% 59.24/7.97  ------ Instantiation Options
% 59.24/7.97  
% 59.24/7.97  --instantiation_flag                    true
% 59.24/7.97  --inst_sos_flag                         false
% 59.24/7.97  --inst_sos_phase                        true
% 59.24/7.97  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 59.24/7.97  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 59.24/7.97  --inst_lit_sel_side                     num_symb
% 59.24/7.97  --inst_solver_per_active                1400
% 59.24/7.97  --inst_solver_calls_frac                1.
% 59.24/7.97  --inst_passive_queue_type               priority_queues
% 59.24/7.97  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 59.24/7.97  --inst_passive_queues_freq              [25;2]
% 59.24/7.97  --inst_dismatching                      true
% 59.24/7.97  --inst_eager_unprocessed_to_passive     true
% 59.24/7.97  --inst_prop_sim_given                   true
% 59.24/7.97  --inst_prop_sim_new                     false
% 59.24/7.97  --inst_subs_new                         false
% 59.24/7.97  --inst_eq_res_simp                      false
% 59.24/7.97  --inst_subs_given                       false
% 59.24/7.97  --inst_orphan_elimination               true
% 59.24/7.97  --inst_learning_loop_flag               true
% 59.24/7.97  --inst_learning_start                   3000
% 59.24/7.97  --inst_learning_factor                  2
% 59.24/7.97  --inst_start_prop_sim_after_learn       3
% 59.24/7.97  --inst_sel_renew                        solver
% 59.24/7.97  --inst_lit_activity_flag                true
% 59.24/7.97  --inst_restr_to_given                   false
% 59.24/7.97  --inst_activity_threshold               500
% 59.24/7.97  --inst_out_proof                        true
% 59.24/7.97  
% 59.24/7.97  ------ Resolution Options
% 59.24/7.97  
% 59.24/7.97  --resolution_flag                       true
% 59.24/7.97  --res_lit_sel                           adaptive
% 59.24/7.97  --res_lit_sel_side                      none
% 59.24/7.97  --res_ordering                          kbo
% 59.24/7.97  --res_to_prop_solver                    active
% 59.24/7.97  --res_prop_simpl_new                    false
% 59.24/7.97  --res_prop_simpl_given                  true
% 59.24/7.97  --res_passive_queue_type                priority_queues
% 59.24/7.97  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 59.24/7.97  --res_passive_queues_freq               [15;5]
% 59.24/7.97  --res_forward_subs                      full
% 59.24/7.97  --res_backward_subs                     full
% 59.24/7.97  --res_forward_subs_resolution           true
% 59.24/7.97  --res_backward_subs_resolution          true
% 59.24/7.97  --res_orphan_elimination                true
% 59.24/7.97  --res_time_limit                        2.
% 59.24/7.97  --res_out_proof                         true
% 59.24/7.97  
% 59.24/7.97  ------ Superposition Options
% 59.24/7.97  
% 59.24/7.97  --superposition_flag                    true
% 59.24/7.97  --sup_passive_queue_type                priority_queues
% 59.24/7.97  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 59.24/7.97  --sup_passive_queues_freq               [8;1;4]
% 59.24/7.97  --demod_completeness_check              fast
% 59.24/7.97  --demod_use_ground                      true
% 59.24/7.97  --sup_to_prop_solver                    passive
% 59.24/7.97  --sup_prop_simpl_new                    true
% 59.24/7.97  --sup_prop_simpl_given                  true
% 59.24/7.97  --sup_fun_splitting                     false
% 59.24/7.97  --sup_smt_interval                      50000
% 59.24/7.97  
% 59.24/7.97  ------ Superposition Simplification Setup
% 59.24/7.97  
% 59.24/7.97  --sup_indices_passive                   []
% 59.24/7.97  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 59.24/7.97  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 59.24/7.97  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 59.24/7.97  --sup_full_triv                         [TrivRules;PropSubs]
% 59.24/7.97  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 59.24/7.97  --sup_full_bw                           [BwDemod]
% 59.24/7.97  --sup_immed_triv                        [TrivRules]
% 59.24/7.97  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 59.24/7.97  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 59.24/7.97  --sup_immed_bw_main                     []
% 59.24/7.97  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 59.24/7.97  --sup_input_triv                        [Unflattening;TrivRules]
% 59.24/7.97  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 59.24/7.97  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 59.24/7.97  
% 59.24/7.97  ------ Combination Options
% 59.24/7.97  
% 59.24/7.97  --comb_res_mult                         3
% 59.24/7.97  --comb_sup_mult                         2
% 59.24/7.97  --comb_inst_mult                        10
% 59.24/7.97  
% 59.24/7.97  ------ Debug Options
% 59.24/7.97  
% 59.24/7.97  --dbg_backtrace                         false
% 59.24/7.97  --dbg_dump_prop_clauses                 false
% 59.24/7.97  --dbg_dump_prop_clauses_file            -
% 59.24/7.97  --dbg_out_stat                          false
% 59.24/7.97  ------ Parsing...
% 59.24/7.97  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 59.24/7.97  
% 59.24/7.97  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe:1:0s pe_e  sf_s  rm: 1 0s  sf_e  pe_s  pe_e 
% 59.24/7.97  
% 59.24/7.97  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 59.24/7.97  
% 59.24/7.97  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 59.24/7.97  ------ Proving...
% 59.24/7.97  ------ Problem Properties 
% 59.24/7.97  
% 59.24/7.97  
% 59.24/7.97  clauses                                 20
% 59.24/7.97  conjectures                             2
% 59.24/7.97  EPR                                     2
% 59.24/7.97  Horn                                    20
% 59.24/7.97  unary                                   3
% 59.24/7.97  binary                                  9
% 59.24/7.97  lits                                    46
% 59.24/7.97  lits eq                                 5
% 59.24/7.97  fd_pure                                 0
% 59.24/7.97  fd_pseudo                               0
% 59.24/7.97  fd_cond                                 0
% 59.24/7.97  fd_pseudo_cond                          0
% 59.24/7.97  AC symbols                              0
% 59.24/7.97  
% 59.24/7.97  ------ Schedule dynamic 5 is on 
% 59.24/7.97  
% 59.24/7.97  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" Time Limit: 10.
% 59.24/7.97  
% 59.24/7.97  
% 59.24/7.97  ------ 
% 59.24/7.97  Current options:
% 59.24/7.97  ------ 
% 59.24/7.97  
% 59.24/7.97  ------ Input Options
% 59.24/7.97  
% 59.24/7.97  --out_options                           all
% 59.24/7.97  --tptp_safe_out                         true
% 59.24/7.97  --problem_path                          ""
% 59.24/7.97  --include_path                          ""
% 59.24/7.97  --clausifier                            res/vclausify_rel
% 59.24/7.97  --clausifier_options                    --mode clausify
% 59.24/7.97  --stdin                                 false
% 59.24/7.97  --stats_out                             all
% 59.24/7.97  
% 59.24/7.97  ------ General Options
% 59.24/7.97  
% 59.24/7.97  --fof                                   false
% 59.24/7.97  --time_out_real                         305.
% 59.24/7.97  --time_out_virtual                      -1.
% 59.24/7.97  --symbol_type_check                     false
% 59.24/7.97  --clausify_out                          false
% 59.24/7.97  --sig_cnt_out                           false
% 59.24/7.97  --trig_cnt_out                          false
% 59.24/7.97  --trig_cnt_out_tolerance                1.
% 59.24/7.97  --trig_cnt_out_sk_spl                   false
% 59.24/7.97  --abstr_cl_out                          false
% 59.24/7.97  
% 59.24/7.97  ------ Global Options
% 59.24/7.97  
% 59.24/7.97  --schedule                              default
% 59.24/7.97  --add_important_lit                     false
% 59.24/7.97  --prop_solver_per_cl                    1000
% 59.24/7.97  --min_unsat_core                        false
% 59.24/7.97  --soft_assumptions                      false
% 59.24/7.97  --soft_lemma_size                       3
% 59.24/7.97  --prop_impl_unit_size                   0
% 59.24/7.97  --prop_impl_unit                        []
% 59.24/7.97  --share_sel_clauses                     true
% 59.24/7.97  --reset_solvers                         false
% 59.24/7.97  --bc_imp_inh                            [conj_cone]
% 59.24/7.97  --conj_cone_tolerance                   3.
% 59.24/7.97  --extra_neg_conj                        none
% 59.24/7.97  --large_theory_mode                     true
% 59.24/7.97  --prolific_symb_bound                   200
% 59.24/7.97  --lt_threshold                          2000
% 59.24/7.97  --clause_weak_htbl                      true
% 59.24/7.97  --gc_record_bc_elim                     false
% 59.24/7.97  
% 59.24/7.97  ------ Preprocessing Options
% 59.24/7.97  
% 59.24/7.97  --preprocessing_flag                    true
% 59.24/7.97  --time_out_prep_mult                    0.1
% 59.24/7.97  --splitting_mode                        input
% 59.24/7.97  --splitting_grd                         true
% 59.24/7.97  --splitting_cvd                         false
% 59.24/7.97  --splitting_cvd_svl                     false
% 59.24/7.97  --splitting_nvd                         32
% 59.24/7.97  --sub_typing                            true
% 59.24/7.97  --prep_gs_sim                           true
% 59.24/7.97  --prep_unflatten                        true
% 59.24/7.97  --prep_res_sim                          true
% 59.24/7.97  --prep_upred                            true
% 59.24/7.97  --prep_sem_filter                       exhaustive
% 59.24/7.97  --prep_sem_filter_out                   false
% 59.24/7.97  --pred_elim                             true
% 59.24/7.97  --res_sim_input                         true
% 59.24/7.97  --eq_ax_congr_red                       true
% 59.24/7.97  --pure_diseq_elim                       true
% 59.24/7.97  --brand_transform                       false
% 59.24/7.97  --non_eq_to_eq                          false
% 59.24/7.97  --prep_def_merge                        true
% 59.24/7.97  --prep_def_merge_prop_impl              false
% 59.24/7.97  --prep_def_merge_mbd                    true
% 59.24/7.97  --prep_def_merge_tr_red                 false
% 59.24/7.97  --prep_def_merge_tr_cl                  false
% 59.24/7.97  --smt_preprocessing                     true
% 59.24/7.97  --smt_ac_axioms                         fast
% 59.24/7.97  --preprocessed_out                      false
% 59.24/7.97  --preprocessed_stats                    false
% 59.24/7.97  
% 59.24/7.97  ------ Abstraction refinement Options
% 59.24/7.97  
% 59.24/7.97  --abstr_ref                             []
% 59.24/7.97  --abstr_ref_prep                        false
% 59.24/7.97  --abstr_ref_until_sat                   false
% 59.24/7.97  --abstr_ref_sig_restrict                funpre
% 59.24/7.97  --abstr_ref_af_restrict_to_split_sk     false
% 59.24/7.97  --abstr_ref_under                       []
% 59.24/7.97  
% 59.24/7.97  ------ SAT Options
% 59.24/7.97  
% 59.24/7.97  --sat_mode                              false
% 59.24/7.97  --sat_fm_restart_options                ""
% 59.24/7.97  --sat_gr_def                            false
% 59.24/7.97  --sat_epr_types                         true
% 59.24/7.97  --sat_non_cyclic_types                  false
% 59.24/7.97  --sat_finite_models                     false
% 59.24/7.97  --sat_fm_lemmas                         false
% 59.24/7.97  --sat_fm_prep                           false
% 59.24/7.97  --sat_fm_uc_incr                        true
% 59.24/7.97  --sat_out_model                         small
% 59.24/7.97  --sat_out_clauses                       false
% 59.24/7.97  
% 59.24/7.97  ------ QBF Options
% 59.24/7.97  
% 59.24/7.97  --qbf_mode                              false
% 59.24/7.97  --qbf_elim_univ                         false
% 59.24/7.97  --qbf_dom_inst                          none
% 59.24/7.97  --qbf_dom_pre_inst                      false
% 59.24/7.97  --qbf_sk_in                             false
% 59.24/7.97  --qbf_pred_elim                         true
% 59.24/7.97  --qbf_split                             512
% 59.24/7.97  
% 59.24/7.97  ------ BMC1 Options
% 59.24/7.97  
% 59.24/7.97  --bmc1_incremental                      false
% 59.24/7.97  --bmc1_axioms                           reachable_all
% 59.24/7.97  --bmc1_min_bound                        0
% 59.24/7.97  --bmc1_max_bound                        -1
% 59.24/7.97  --bmc1_max_bound_default                -1
% 59.24/7.97  --bmc1_symbol_reachability              true
% 59.24/7.97  --bmc1_property_lemmas                  false
% 59.24/7.97  --bmc1_k_induction                      false
% 59.24/7.97  --bmc1_non_equiv_states                 false
% 59.24/7.97  --bmc1_deadlock                         false
% 59.24/7.97  --bmc1_ucm                              false
% 59.24/7.97  --bmc1_add_unsat_core                   none
% 59.24/7.97  --bmc1_unsat_core_children              false
% 59.24/7.97  --bmc1_unsat_core_extrapolate_axioms    false
% 59.24/7.97  --bmc1_out_stat                         full
% 59.24/7.97  --bmc1_ground_init                      false
% 59.24/7.97  --bmc1_pre_inst_next_state              false
% 59.24/7.97  --bmc1_pre_inst_state                   false
% 59.24/7.97  --bmc1_pre_inst_reach_state             false
% 59.24/7.97  --bmc1_out_unsat_core                   false
% 59.24/7.97  --bmc1_aig_witness_out                  false
% 59.24/7.97  --bmc1_verbose                          false
% 59.24/7.97  --bmc1_dump_clauses_tptp                false
% 59.24/7.97  --bmc1_dump_unsat_core_tptp             false
% 59.24/7.97  --bmc1_dump_file                        -
% 59.24/7.97  --bmc1_ucm_expand_uc_limit              128
% 59.24/7.97  --bmc1_ucm_n_expand_iterations          6
% 59.24/7.97  --bmc1_ucm_extend_mode                  1
% 59.24/7.97  --bmc1_ucm_init_mode                    2
% 59.24/7.97  --bmc1_ucm_cone_mode                    none
% 59.24/7.97  --bmc1_ucm_reduced_relation_type        0
% 59.24/7.97  --bmc1_ucm_relax_model                  4
% 59.24/7.97  --bmc1_ucm_full_tr_after_sat            true
% 59.24/7.97  --bmc1_ucm_expand_neg_assumptions       false
% 59.24/7.97  --bmc1_ucm_layered_model                none
% 59.24/7.97  --bmc1_ucm_max_lemma_size               10
% 59.24/7.97  
% 59.24/7.97  ------ AIG Options
% 59.24/7.97  
% 59.24/7.97  --aig_mode                              false
% 59.24/7.97  
% 59.24/7.97  ------ Instantiation Options
% 59.24/7.97  
% 59.24/7.97  --instantiation_flag                    true
% 59.24/7.97  --inst_sos_flag                         false
% 59.24/7.97  --inst_sos_phase                        true
% 59.24/7.97  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 59.24/7.97  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 59.24/7.97  --inst_lit_sel_side                     none
% 59.24/7.97  --inst_solver_per_active                1400
% 59.24/7.97  --inst_solver_calls_frac                1.
% 59.24/7.97  --inst_passive_queue_type               priority_queues
% 59.24/7.97  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 59.24/7.97  --inst_passive_queues_freq              [25;2]
% 59.24/7.97  --inst_dismatching                      true
% 59.24/7.97  --inst_eager_unprocessed_to_passive     true
% 59.24/7.97  --inst_prop_sim_given                   true
% 59.24/7.97  --inst_prop_sim_new                     false
% 59.24/7.97  --inst_subs_new                         false
% 59.24/7.97  --inst_eq_res_simp                      false
% 59.24/7.97  --inst_subs_given                       false
% 59.24/7.97  --inst_orphan_elimination               true
% 59.24/7.97  --inst_learning_loop_flag               true
% 59.24/7.97  --inst_learning_start                   3000
% 59.24/7.97  --inst_learning_factor                  2
% 59.24/7.97  --inst_start_prop_sim_after_learn       3
% 59.24/7.97  --inst_sel_renew                        solver
% 59.24/7.97  --inst_lit_activity_flag                true
% 59.24/7.97  --inst_restr_to_given                   false
% 59.24/7.97  --inst_activity_threshold               500
% 59.24/7.97  --inst_out_proof                        true
% 59.24/7.97  
% 59.24/7.97  ------ Resolution Options
% 59.24/7.97  
% 59.24/7.97  --resolution_flag                       false
% 59.24/7.97  --res_lit_sel                           adaptive
% 59.24/7.97  --res_lit_sel_side                      none
% 59.24/7.97  --res_ordering                          kbo
% 59.24/7.97  --res_to_prop_solver                    active
% 59.24/7.97  --res_prop_simpl_new                    false
% 59.24/7.97  --res_prop_simpl_given                  true
% 59.24/7.97  --res_passive_queue_type                priority_queues
% 59.24/7.97  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 59.24/7.97  --res_passive_queues_freq               [15;5]
% 59.24/7.97  --res_forward_subs                      full
% 59.24/7.97  --res_backward_subs                     full
% 59.24/7.97  --res_forward_subs_resolution           true
% 59.24/7.97  --res_backward_subs_resolution          true
% 59.24/7.97  --res_orphan_elimination                true
% 59.24/7.97  --res_time_limit                        2.
% 59.24/7.97  --res_out_proof                         true
% 59.24/7.97  
% 59.24/7.97  ------ Superposition Options
% 59.24/7.97  
% 59.24/7.97  --superposition_flag                    true
% 59.24/7.97  --sup_passive_queue_type                priority_queues
% 59.24/7.97  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 59.24/7.97  --sup_passive_queues_freq               [8;1;4]
% 59.24/7.97  --demod_completeness_check              fast
% 59.24/7.97  --demod_use_ground                      true
% 59.24/7.97  --sup_to_prop_solver                    passive
% 59.24/7.97  --sup_prop_simpl_new                    true
% 59.24/7.97  --sup_prop_simpl_given                  true
% 59.24/7.97  --sup_fun_splitting                     false
% 59.24/7.97  --sup_smt_interval                      50000
% 59.24/7.97  
% 59.24/7.97  ------ Superposition Simplification Setup
% 59.24/7.97  
% 59.24/7.97  --sup_indices_passive                   []
% 59.24/7.97  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 59.24/7.97  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 59.24/7.97  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 59.24/7.97  --sup_full_triv                         [TrivRules;PropSubs]
% 59.24/7.97  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 59.24/7.97  --sup_full_bw                           [BwDemod]
% 59.24/7.97  --sup_immed_triv                        [TrivRules]
% 59.24/7.97  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 59.24/7.97  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 59.24/7.97  --sup_immed_bw_main                     []
% 59.24/7.97  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 59.24/7.97  --sup_input_triv                        [Unflattening;TrivRules]
% 59.24/7.97  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 59.24/7.97  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 59.24/7.97  
% 59.24/7.97  ------ Combination Options
% 59.24/7.97  
% 59.24/7.97  --comb_res_mult                         3
% 59.24/7.97  --comb_sup_mult                         2
% 59.24/7.97  --comb_inst_mult                        10
% 59.24/7.97  
% 59.24/7.97  ------ Debug Options
% 59.24/7.97  
% 59.24/7.97  --dbg_backtrace                         false
% 59.24/7.97  --dbg_dump_prop_clauses                 false
% 59.24/7.97  --dbg_dump_prop_clauses_file            -
% 59.24/7.97  --dbg_out_stat                          false
% 59.24/7.97  
% 59.24/7.97  
% 59.24/7.97  
% 59.24/7.97  
% 59.24/7.97  ------ Proving...
% 59.24/7.97  
% 59.24/7.97  
% 59.24/7.97  % SZS status Theorem for theBenchmark.p
% 59.24/7.97  
% 59.24/7.97   Resolution empty clause
% 59.24/7.97  
% 59.24/7.97  % SZS output start CNFRefutation for theBenchmark.p
% 59.24/7.97  
% 59.24/7.97  fof(f19,conjecture,(
% 59.24/7.97    ! [X0,X1,X2,X3] : (m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X2,X0))) => m1_subset_1(k6_relset_1(X2,X0,X1,X3),k1_zfmisc_1(k2_zfmisc_1(X2,X1))))),
% 59.24/7.97    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 59.24/7.97  
% 59.24/7.97  fof(f20,negated_conjecture,(
% 59.24/7.97    ~! [X0,X1,X2,X3] : (m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X2,X0))) => m1_subset_1(k6_relset_1(X2,X0,X1,X3),k1_zfmisc_1(k2_zfmisc_1(X2,X1))))),
% 59.24/7.97    inference(negated_conjecture,[],[f19])).
% 59.24/7.97  
% 59.24/7.97  fof(f44,plain,(
% 59.24/7.97    ? [X0,X1,X2,X3] : (~m1_subset_1(k6_relset_1(X2,X0,X1,X3),k1_zfmisc_1(k2_zfmisc_1(X2,X1))) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X2,X0))))),
% 59.24/7.97    inference(ennf_transformation,[],[f20])).
% 59.24/7.97  
% 59.24/7.97  fof(f47,plain,(
% 59.24/7.97    ? [X0,X1,X2,X3] : (~m1_subset_1(k6_relset_1(X2,X0,X1,X3),k1_zfmisc_1(k2_zfmisc_1(X2,X1))) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X2,X0)))) => (~m1_subset_1(k6_relset_1(sK2,sK0,sK1,sK3),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK2,sK0))))),
% 59.24/7.97    introduced(choice_axiom,[])).
% 59.24/7.97  
% 59.24/7.97  fof(f48,plain,(
% 59.24/7.97    ~m1_subset_1(k6_relset_1(sK2,sK0,sK1,sK3),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK2,sK0)))),
% 59.24/7.97    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3])],[f44,f47])).
% 59.24/7.97  
% 59.24/7.97  fof(f69,plain,(
% 59.24/7.97    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK2,sK0)))),
% 59.24/7.97    inference(cnf_transformation,[],[f48])).
% 59.24/7.97  
% 59.24/7.97  fof(f2,axiom,(
% 59.24/7.97    ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) <=> r1_tarski(X0,X1))),
% 59.24/7.97    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 59.24/7.97  
% 59.24/7.97  fof(f45,plain,(
% 59.24/7.97    ! [X0,X1] : ((m1_subset_1(X0,k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1)) & (r1_tarski(X0,X1) | ~m1_subset_1(X0,k1_zfmisc_1(X1))))),
% 59.24/7.97    inference(nnf_transformation,[],[f2])).
% 59.24/7.97  
% 59.24/7.97  fof(f50,plain,(
% 59.24/7.97    ( ! [X0,X1] : (r1_tarski(X0,X1) | ~m1_subset_1(X0,k1_zfmisc_1(X1))) )),
% 59.24/7.97    inference(cnf_transformation,[],[f45])).
% 59.24/7.97  
% 59.24/7.97  fof(f3,axiom,(
% 59.24/7.97    ! [X0] : (v1_relat_1(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => v1_relat_1(X1)))),
% 59.24/7.97    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 59.24/7.97  
% 59.24/7.97  fof(f24,plain,(
% 59.24/7.97    ! [X0] : (! [X1] : (v1_relat_1(X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) | ~v1_relat_1(X0))),
% 59.24/7.97    inference(ennf_transformation,[],[f3])).
% 59.24/7.97  
% 59.24/7.97  fof(f52,plain,(
% 59.24/7.97    ( ! [X0,X1] : (v1_relat_1(X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0)) | ~v1_relat_1(X0)) )),
% 59.24/7.97    inference(cnf_transformation,[],[f24])).
% 59.24/7.97  
% 59.24/7.97  fof(f51,plain,(
% 59.24/7.97    ( ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1)) )),
% 59.24/7.97    inference(cnf_transformation,[],[f45])).
% 59.24/7.97  
% 59.24/7.97  fof(f6,axiom,(
% 59.24/7.97    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1))),
% 59.24/7.97    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 59.24/7.97  
% 59.24/7.97  fof(f56,plain,(
% 59.24/7.97    ( ! [X0,X1] : (v1_relat_1(k2_zfmisc_1(X0,X1))) )),
% 59.24/7.97    inference(cnf_transformation,[],[f6])).
% 59.24/7.97  
% 59.24/7.97  fof(f7,axiom,(
% 59.24/7.97    ! [X0,X1] : (v1_relat_1(X1) => r1_tarski(k2_relat_1(k8_relat_1(X0,X1)),X0))),
% 59.24/7.97    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 59.24/7.97  
% 59.24/7.97  fof(f27,plain,(
% 59.24/7.97    ! [X0,X1] : (r1_tarski(k2_relat_1(k8_relat_1(X0,X1)),X0) | ~v1_relat_1(X1))),
% 59.24/7.97    inference(ennf_transformation,[],[f7])).
% 59.24/7.97  
% 59.24/7.97  fof(f57,plain,(
% 59.24/7.97    ( ! [X0,X1] : (r1_tarski(k2_relat_1(k8_relat_1(X0,X1)),X0) | ~v1_relat_1(X1)) )),
% 59.24/7.97    inference(cnf_transformation,[],[f27])).
% 59.24/7.97  
% 59.24/7.97  fof(f9,axiom,(
% 59.24/7.97    ! [X0,X1] : (v1_relat_1(X1) => (r1_tarski(k2_relat_1(X1),X0) => k8_relat_1(X0,X1) = X1))),
% 59.24/7.97    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 59.24/7.97  
% 59.24/7.97  fof(f29,plain,(
% 59.24/7.97    ! [X0,X1] : ((k8_relat_1(X0,X1) = X1 | ~r1_tarski(k2_relat_1(X1),X0)) | ~v1_relat_1(X1))),
% 59.24/7.97    inference(ennf_transformation,[],[f9])).
% 59.24/7.97  
% 59.24/7.97  fof(f30,plain,(
% 59.24/7.97    ! [X0,X1] : (k8_relat_1(X0,X1) = X1 | ~r1_tarski(k2_relat_1(X1),X0) | ~v1_relat_1(X1))),
% 59.24/7.97    inference(flattening,[],[f29])).
% 59.24/7.97  
% 59.24/7.97  fof(f59,plain,(
% 59.24/7.97    ( ! [X0,X1] : (k8_relat_1(X0,X1) = X1 | ~r1_tarski(k2_relat_1(X1),X0) | ~v1_relat_1(X1)) )),
% 59.24/7.97    inference(cnf_transformation,[],[f30])).
% 59.24/7.97  
% 59.24/7.97  fof(f5,axiom,(
% 59.24/7.97    ! [X0,X1] : (v1_relat_1(X1) => v1_relat_1(k8_relat_1(X0,X1)))),
% 59.24/7.97    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 59.24/7.97  
% 59.24/7.97  fof(f26,plain,(
% 59.24/7.97    ! [X0,X1] : (v1_relat_1(k8_relat_1(X0,X1)) | ~v1_relat_1(X1))),
% 59.24/7.97    inference(ennf_transformation,[],[f5])).
% 59.24/7.97  
% 59.24/7.97  fof(f55,plain,(
% 59.24/7.97    ( ! [X0,X1] : (v1_relat_1(k8_relat_1(X0,X1)) | ~v1_relat_1(X1)) )),
% 59.24/7.97    inference(cnf_transformation,[],[f26])).
% 59.24/7.97  
% 59.24/7.97  fof(f11,axiom,(
% 59.24/7.97    ! [X0,X1,X2] : (v1_relat_1(X2) => (r1_tarski(X0,X1) => k8_relat_1(X0,X2) = k8_relat_1(X0,k8_relat_1(X1,X2))))),
% 59.24/7.97    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 59.24/7.97  
% 59.24/7.97  fof(f32,plain,(
% 59.24/7.97    ! [X0,X1,X2] : ((k8_relat_1(X0,X2) = k8_relat_1(X0,k8_relat_1(X1,X2)) | ~r1_tarski(X0,X1)) | ~v1_relat_1(X2))),
% 59.24/7.97    inference(ennf_transformation,[],[f11])).
% 59.24/7.97  
% 59.24/7.97  fof(f33,plain,(
% 59.24/7.97    ! [X0,X1,X2] : (k8_relat_1(X0,X2) = k8_relat_1(X0,k8_relat_1(X1,X2)) | ~r1_tarski(X0,X1) | ~v1_relat_1(X2))),
% 59.24/7.97    inference(flattening,[],[f32])).
% 59.24/7.97  
% 59.24/7.97  fof(f61,plain,(
% 59.24/7.97    ( ! [X2,X0,X1] : (k8_relat_1(X0,X2) = k8_relat_1(X0,k8_relat_1(X1,X2)) | ~r1_tarski(X0,X1) | ~v1_relat_1(X2)) )),
% 59.24/7.97    inference(cnf_transformation,[],[f33])).
% 59.24/7.97  
% 59.24/7.97  fof(f10,axiom,(
% 59.24/7.97    ! [X0] : (v1_relat_1(X0) => k8_relat_1(k2_relat_1(X0),X0) = X0)),
% 59.24/7.97    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 59.24/7.97  
% 59.24/7.97  fof(f31,plain,(
% 59.24/7.97    ! [X0] : (k8_relat_1(k2_relat_1(X0),X0) = X0 | ~v1_relat_1(X0))),
% 59.24/7.97    inference(ennf_transformation,[],[f10])).
% 59.24/7.97  
% 59.24/7.97  fof(f60,plain,(
% 59.24/7.97    ( ! [X0] : (k8_relat_1(k2_relat_1(X0),X0) = X0 | ~v1_relat_1(X0)) )),
% 59.24/7.97    inference(cnf_transformation,[],[f31])).
% 59.24/7.97  
% 59.24/7.97  fof(f8,axiom,(
% 59.24/7.97    ! [X0,X1] : (v1_relat_1(X1) => r1_tarski(k2_relat_1(k8_relat_1(X0,X1)),k2_relat_1(X1)))),
% 59.24/7.97    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 59.24/7.97  
% 59.24/7.97  fof(f28,plain,(
% 59.24/7.97    ! [X0,X1] : (r1_tarski(k2_relat_1(k8_relat_1(X0,X1)),k2_relat_1(X1)) | ~v1_relat_1(X1))),
% 59.24/7.97    inference(ennf_transformation,[],[f8])).
% 59.24/7.97  
% 59.24/7.97  fof(f58,plain,(
% 59.24/7.97    ( ! [X0,X1] : (r1_tarski(k2_relat_1(k8_relat_1(X0,X1)),k2_relat_1(X1)) | ~v1_relat_1(X1)) )),
% 59.24/7.97    inference(cnf_transformation,[],[f28])).
% 59.24/7.97  
% 59.24/7.97  fof(f13,axiom,(
% 59.24/7.97    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => (v5_relat_1(X2,X1) & v4_relat_1(X2,X0)))),
% 59.24/7.97    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 59.24/7.97  
% 59.24/7.97  fof(f21,plain,(
% 59.24/7.97    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => v5_relat_1(X2,X1))),
% 59.24/7.97    inference(pure_predicate_removal,[],[f13])).
% 59.24/7.97  
% 59.24/7.97  fof(f36,plain,(
% 59.24/7.97    ! [X0,X1,X2] : (v5_relat_1(X2,X1) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 59.24/7.97    inference(ennf_transformation,[],[f21])).
% 59.24/7.97  
% 59.24/7.97  fof(f63,plain,(
% 59.24/7.97    ( ! [X2,X0,X1] : (v5_relat_1(X2,X1) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 59.24/7.97    inference(cnf_transformation,[],[f36])).
% 59.24/7.97  
% 59.24/7.97  fof(f4,axiom,(
% 59.24/7.97    ! [X0,X1] : (v1_relat_1(X1) => (v5_relat_1(X1,X0) <=> r1_tarski(k2_relat_1(X1),X0)))),
% 59.24/7.97    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 59.24/7.97  
% 59.24/7.97  fof(f25,plain,(
% 59.24/7.97    ! [X0,X1] : ((v5_relat_1(X1,X0) <=> r1_tarski(k2_relat_1(X1),X0)) | ~v1_relat_1(X1))),
% 59.24/7.97    inference(ennf_transformation,[],[f4])).
% 59.24/7.97  
% 59.24/7.97  fof(f46,plain,(
% 59.24/7.97    ! [X0,X1] : (((v5_relat_1(X1,X0) | ~r1_tarski(k2_relat_1(X1),X0)) & (r1_tarski(k2_relat_1(X1),X0) | ~v5_relat_1(X1,X0))) | ~v1_relat_1(X1))),
% 59.24/7.97    inference(nnf_transformation,[],[f25])).
% 59.24/7.97  
% 59.24/7.97  fof(f53,plain,(
% 59.24/7.97    ( ! [X0,X1] : (r1_tarski(k2_relat_1(X1),X0) | ~v5_relat_1(X1,X0) | ~v1_relat_1(X1)) )),
% 59.24/7.97    inference(cnf_transformation,[],[f46])).
% 59.24/7.97  
% 59.24/7.97  fof(f1,axiom,(
% 59.24/7.97    ! [X0,X1,X2] : ((r1_tarski(X1,X2) & r1_tarski(X0,X1)) => r1_tarski(X0,X2))),
% 59.24/7.97    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 59.24/7.97  
% 59.24/7.97  fof(f22,plain,(
% 59.24/7.97    ! [X0,X1,X2] : (r1_tarski(X0,X2) | (~r1_tarski(X1,X2) | ~r1_tarski(X0,X1)))),
% 59.24/7.97    inference(ennf_transformation,[],[f1])).
% 59.24/7.97  
% 59.24/7.97  fof(f23,plain,(
% 59.24/7.97    ! [X0,X1,X2] : (r1_tarski(X0,X2) | ~r1_tarski(X1,X2) | ~r1_tarski(X0,X1))),
% 59.24/7.97    inference(flattening,[],[f22])).
% 59.24/7.97  
% 59.24/7.97  fof(f49,plain,(
% 59.24/7.97    ( ! [X2,X0,X1] : (r1_tarski(X0,X2) | ~r1_tarski(X1,X2) | ~r1_tarski(X0,X1)) )),
% 59.24/7.97    inference(cnf_transformation,[],[f23])).
% 59.24/7.97  
% 59.24/7.97  fof(f12,axiom,(
% 59.24/7.97    ! [X0,X1,X2] : (v1_relat_1(X2) => (r1_tarski(X0,X1) => r1_tarski(k8_relat_1(X0,X2),k8_relat_1(X1,X2))))),
% 59.24/7.97    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 59.24/7.97  
% 59.24/7.97  fof(f34,plain,(
% 59.24/7.97    ! [X0,X1,X2] : ((r1_tarski(k8_relat_1(X0,X2),k8_relat_1(X1,X2)) | ~r1_tarski(X0,X1)) | ~v1_relat_1(X2))),
% 59.24/7.97    inference(ennf_transformation,[],[f12])).
% 59.24/7.97  
% 59.24/7.97  fof(f35,plain,(
% 59.24/7.97    ! [X0,X1,X2] : (r1_tarski(k8_relat_1(X0,X2),k8_relat_1(X1,X2)) | ~r1_tarski(X0,X1) | ~v1_relat_1(X2))),
% 59.24/7.97    inference(flattening,[],[f34])).
% 59.24/7.97  
% 59.24/7.97  fof(f62,plain,(
% 59.24/7.97    ( ! [X2,X0,X1] : (r1_tarski(k8_relat_1(X0,X2),k8_relat_1(X1,X2)) | ~r1_tarski(X0,X1) | ~v1_relat_1(X2)) )),
% 59.24/7.97    inference(cnf_transformation,[],[f35])).
% 59.24/7.97  
% 59.24/7.97  fof(f18,axiom,(
% 59.24/7.97    ! [X0,X1,X2,X3] : (m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) => (r1_tarski(X0,X3) => m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))))),
% 59.24/7.97    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 59.24/7.97  
% 59.24/7.97  fof(f42,plain,(
% 59.24/7.97    ! [X0,X1,X2,X3] : ((m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) | ~r1_tarski(X0,X3)) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))))),
% 59.24/7.97    inference(ennf_transformation,[],[f18])).
% 59.24/7.97  
% 59.24/7.97  fof(f43,plain,(
% 59.24/7.97    ! [X0,X1,X2,X3] : (m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) | ~r1_tarski(X0,X3) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))))),
% 59.24/7.97    inference(flattening,[],[f42])).
% 59.24/7.97  
% 59.24/7.97  fof(f68,plain,(
% 59.24/7.97    ( ! [X2,X0,X3,X1] : (m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) | ~r1_tarski(X0,X3) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))) )),
% 59.24/7.97    inference(cnf_transformation,[],[f43])).
% 59.24/7.97  
% 59.24/7.97  fof(f15,axiom,(
% 59.24/7.97    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k1_relset_1(X0,X1,X2) = k1_relat_1(X2))),
% 59.24/7.97    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 59.24/7.97  
% 59.24/7.97  fof(f38,plain,(
% 59.24/7.97    ! [X0,X1,X2] : (k1_relset_1(X0,X1,X2) = k1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 59.24/7.97    inference(ennf_transformation,[],[f15])).
% 59.24/7.97  
% 59.24/7.97  fof(f65,plain,(
% 59.24/7.97    ( ! [X2,X0,X1] : (k1_relset_1(X0,X1,X2) = k1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 59.24/7.97    inference(cnf_transformation,[],[f38])).
% 59.24/7.97  
% 59.24/7.97  fof(f14,axiom,(
% 59.24/7.97    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => m1_subset_1(k1_relset_1(X0,X1,X2),k1_zfmisc_1(X0)))),
% 59.24/7.97    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 59.24/7.97  
% 59.24/7.97  fof(f37,plain,(
% 59.24/7.97    ! [X0,X1,X2] : (m1_subset_1(k1_relset_1(X0,X1,X2),k1_zfmisc_1(X0)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 59.24/7.97    inference(ennf_transformation,[],[f14])).
% 59.24/7.97  
% 59.24/7.97  fof(f64,plain,(
% 59.24/7.97    ( ! [X2,X0,X1] : (m1_subset_1(k1_relset_1(X0,X1,X2),k1_zfmisc_1(X0)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 59.24/7.97    inference(cnf_transformation,[],[f37])).
% 59.24/7.97  
% 59.24/7.97  fof(f17,axiom,(
% 59.24/7.97    ! [X0,X1,X2] : (v1_relat_1(X2) => ((r1_tarski(k2_relat_1(X2),X1) & r1_tarski(k1_relat_1(X2),X0)) => m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))))),
% 59.24/7.97    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 59.24/7.97  
% 59.24/7.97  fof(f40,plain,(
% 59.24/7.97    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | (~r1_tarski(k2_relat_1(X2),X1) | ~r1_tarski(k1_relat_1(X2),X0))) | ~v1_relat_1(X2))),
% 59.24/7.97    inference(ennf_transformation,[],[f17])).
% 59.24/7.97  
% 59.24/7.97  fof(f41,plain,(
% 59.24/7.97    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~r1_tarski(k2_relat_1(X2),X1) | ~r1_tarski(k1_relat_1(X2),X0) | ~v1_relat_1(X2))),
% 59.24/7.97    inference(flattening,[],[f40])).
% 59.24/7.97  
% 59.24/7.97  fof(f67,plain,(
% 59.24/7.97    ( ! [X2,X0,X1] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~r1_tarski(k2_relat_1(X2),X1) | ~r1_tarski(k1_relat_1(X2),X0) | ~v1_relat_1(X2)) )),
% 59.24/7.97    inference(cnf_transformation,[],[f41])).
% 59.24/7.97  
% 59.24/7.97  fof(f16,axiom,(
% 59.24/7.97    ! [X0,X1,X2,X3] : (m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k8_relat_1(X2,X3) = k6_relset_1(X0,X1,X2,X3))),
% 59.24/7.97    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 59.24/7.97  
% 59.24/7.97  fof(f39,plain,(
% 59.24/7.97    ! [X0,X1,X2,X3] : (k8_relat_1(X2,X3) = k6_relset_1(X0,X1,X2,X3) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 59.24/7.97    inference(ennf_transformation,[],[f16])).
% 59.24/7.97  
% 59.24/7.97  fof(f66,plain,(
% 59.24/7.97    ( ! [X2,X0,X3,X1] : (k8_relat_1(X2,X3) = k6_relset_1(X0,X1,X2,X3) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 59.24/7.97    inference(cnf_transformation,[],[f39])).
% 59.24/7.97  
% 59.24/7.97  fof(f70,plain,(
% 59.24/7.97    ~m1_subset_1(k6_relset_1(sK2,sK0,sK1,sK3),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1)))),
% 59.24/7.97    inference(cnf_transformation,[],[f48])).
% 59.24/7.97  
% 59.24/7.97  cnf(c_21,negated_conjecture,
% 59.24/7.97      ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK2,sK0))) ),
% 59.24/7.97      inference(cnf_transformation,[],[f69]) ).
% 59.24/7.97  
% 59.24/7.97  cnf(c_963,plain,
% 59.24/7.97      ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK2,sK0))) = iProver_top ),
% 59.24/7.97      inference(predicate_to_equality,[status(thm)],[c_21]) ).
% 59.24/7.97  
% 59.24/7.97  cnf(c_2,plain,
% 59.24/7.97      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1)) | r1_tarski(X0,X1) ),
% 59.24/7.97      inference(cnf_transformation,[],[f50]) ).
% 59.24/7.97  
% 59.24/7.97  cnf(c_978,plain,
% 59.24/7.97      ( m1_subset_1(X0,k1_zfmisc_1(X1)) != iProver_top
% 59.24/7.97      | r1_tarski(X0,X1) = iProver_top ),
% 59.24/7.97      inference(predicate_to_equality,[status(thm)],[c_2]) ).
% 59.24/7.97  
% 59.24/7.97  cnf(c_1336,plain,
% 59.24/7.97      ( r1_tarski(sK3,k2_zfmisc_1(sK2,sK0)) = iProver_top ),
% 59.24/7.97      inference(superposition,[status(thm)],[c_963,c_978]) ).
% 59.24/7.97  
% 59.24/7.97  cnf(c_3,plain,
% 59.24/7.97      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1)) | ~ v1_relat_1(X1) | v1_relat_1(X0) ),
% 59.24/7.97      inference(cnf_transformation,[],[f52]) ).
% 59.24/7.97  
% 59.24/7.97  cnf(c_1,plain,
% 59.24/7.97      ( m1_subset_1(X0,k1_zfmisc_1(X1)) | ~ r1_tarski(X0,X1) ),
% 59.24/7.97      inference(cnf_transformation,[],[f51]) ).
% 59.24/7.97  
% 59.24/7.97  cnf(c_178,plain,
% 59.24/7.97      ( ~ r1_tarski(X0,X1) | m1_subset_1(X0,k1_zfmisc_1(X1)) ),
% 59.24/7.97      inference(prop_impl,[status(thm)],[c_1]) ).
% 59.24/7.97  
% 59.24/7.97  cnf(c_179,plain,
% 59.24/7.97      ( m1_subset_1(X0,k1_zfmisc_1(X1)) | ~ r1_tarski(X0,X1) ),
% 59.24/7.97      inference(renaming,[status(thm)],[c_178]) ).
% 59.24/7.97  
% 59.24/7.97  cnf(c_216,plain,
% 59.24/7.97      ( ~ r1_tarski(X0,X1) | ~ v1_relat_1(X1) | v1_relat_1(X0) ),
% 59.24/7.97      inference(bin_hyper_res,[status(thm)],[c_3,c_179]) ).
% 59.24/7.97  
% 59.24/7.97  cnf(c_962,plain,
% 59.24/7.97      ( r1_tarski(X0,X1) != iProver_top
% 59.24/7.97      | v1_relat_1(X1) != iProver_top
% 59.24/7.97      | v1_relat_1(X0) = iProver_top ),
% 59.24/7.97      inference(predicate_to_equality,[status(thm)],[c_216]) ).
% 59.24/7.97  
% 59.24/7.97  cnf(c_2087,plain,
% 59.24/7.97      ( v1_relat_1(k2_zfmisc_1(sK2,sK0)) != iProver_top
% 59.24/7.97      | v1_relat_1(sK3) = iProver_top ),
% 59.24/7.97      inference(superposition,[status(thm)],[c_1336,c_962]) ).
% 59.24/7.97  
% 59.24/7.97  cnf(c_22,plain,
% 59.24/7.97      ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK2,sK0))) = iProver_top ),
% 59.24/7.97      inference(predicate_to_equality,[status(thm)],[c_21]) ).
% 59.24/7.97  
% 59.24/7.97  cnf(c_1116,plain,
% 59.24/7.97      ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK2,sK0)))
% 59.24/7.97      | r1_tarski(sK3,k2_zfmisc_1(sK2,sK0)) ),
% 59.24/7.97      inference(instantiation,[status(thm)],[c_2]) ).
% 59.24/7.97  
% 59.24/7.97  cnf(c_1117,plain,
% 59.24/7.97      ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK2,sK0))) != iProver_top
% 59.24/7.97      | r1_tarski(sK3,k2_zfmisc_1(sK2,sK0)) = iProver_top ),
% 59.24/7.97      inference(predicate_to_equality,[status(thm)],[c_1116]) ).
% 59.24/7.97  
% 59.24/7.97  cnf(c_1176,plain,
% 59.24/7.97      ( ~ r1_tarski(X0,k2_zfmisc_1(X1,X2))
% 59.24/7.97      | v1_relat_1(X0)
% 59.24/7.97      | ~ v1_relat_1(k2_zfmisc_1(X1,X2)) ),
% 59.24/7.97      inference(instantiation,[status(thm)],[c_216]) ).
% 59.24/7.97  
% 59.24/7.97  cnf(c_1403,plain,
% 59.24/7.97      ( ~ r1_tarski(sK3,k2_zfmisc_1(sK2,sK0))
% 59.24/7.97      | ~ v1_relat_1(k2_zfmisc_1(sK2,sK0))
% 59.24/7.97      | v1_relat_1(sK3) ),
% 59.24/7.97      inference(instantiation,[status(thm)],[c_1176]) ).
% 59.24/7.97  
% 59.24/7.97  cnf(c_1404,plain,
% 59.24/7.97      ( r1_tarski(sK3,k2_zfmisc_1(sK2,sK0)) != iProver_top
% 59.24/7.97      | v1_relat_1(k2_zfmisc_1(sK2,sK0)) != iProver_top
% 59.24/7.97      | v1_relat_1(sK3) = iProver_top ),
% 59.24/7.97      inference(predicate_to_equality,[status(thm)],[c_1403]) ).
% 59.24/7.97  
% 59.24/7.97  cnf(c_7,plain,
% 59.24/7.97      ( v1_relat_1(k2_zfmisc_1(X0,X1)) ),
% 59.24/7.97      inference(cnf_transformation,[],[f56]) ).
% 59.24/7.97  
% 59.24/7.97  cnf(c_1772,plain,
% 59.24/7.97      ( v1_relat_1(k2_zfmisc_1(sK2,sK0)) ),
% 59.24/7.97      inference(instantiation,[status(thm)],[c_7]) ).
% 59.24/7.97  
% 59.24/7.97  cnf(c_1773,plain,
% 59.24/7.97      ( v1_relat_1(k2_zfmisc_1(sK2,sK0)) = iProver_top ),
% 59.24/7.97      inference(predicate_to_equality,[status(thm)],[c_1772]) ).
% 59.24/7.97  
% 59.24/7.97  cnf(c_2371,plain,
% 59.24/7.97      ( v1_relat_1(sK3) = iProver_top ),
% 59.24/7.97      inference(global_propositional_subsumption,
% 59.24/7.97                [status(thm)],
% 59.24/7.97                [c_2087,c_22,c_1117,c_1404,c_1773]) ).
% 59.24/7.97  
% 59.24/7.97  cnf(c_8,plain,
% 59.24/7.97      ( r1_tarski(k2_relat_1(k8_relat_1(X0,X1)),X0) | ~ v1_relat_1(X1) ),
% 59.24/7.97      inference(cnf_transformation,[],[f57]) ).
% 59.24/7.97  
% 59.24/7.97  cnf(c_975,plain,
% 59.24/7.97      ( r1_tarski(k2_relat_1(k8_relat_1(X0,X1)),X0) = iProver_top
% 59.24/7.97      | v1_relat_1(X1) != iProver_top ),
% 59.24/7.97      inference(predicate_to_equality,[status(thm)],[c_8]) ).
% 59.24/7.97  
% 59.24/7.97  cnf(c_10,plain,
% 59.24/7.97      ( ~ r1_tarski(k2_relat_1(X0),X1)
% 59.24/7.97      | ~ v1_relat_1(X0)
% 59.24/7.97      | k8_relat_1(X1,X0) = X0 ),
% 59.24/7.97      inference(cnf_transformation,[],[f59]) ).
% 59.24/7.97  
% 59.24/7.97  cnf(c_973,plain,
% 59.24/7.97      ( k8_relat_1(X0,X1) = X1
% 59.24/7.97      | r1_tarski(k2_relat_1(X1),X0) != iProver_top
% 59.24/7.97      | v1_relat_1(X1) != iProver_top ),
% 59.24/7.97      inference(predicate_to_equality,[status(thm)],[c_10]) ).
% 59.24/7.97  
% 59.24/7.97  cnf(c_3218,plain,
% 59.24/7.97      ( k8_relat_1(X0,k8_relat_1(X0,X1)) = k8_relat_1(X0,X1)
% 59.24/7.97      | v1_relat_1(X1) != iProver_top
% 59.24/7.97      | v1_relat_1(k8_relat_1(X0,X1)) != iProver_top ),
% 59.24/7.97      inference(superposition,[status(thm)],[c_975,c_973]) ).
% 59.24/7.97  
% 59.24/7.97  cnf(c_6,plain,
% 59.24/7.97      ( ~ v1_relat_1(X0) | v1_relat_1(k8_relat_1(X1,X0)) ),
% 59.24/7.97      inference(cnf_transformation,[],[f55]) ).
% 59.24/7.97  
% 59.24/7.97  cnf(c_977,plain,
% 59.24/7.97      ( v1_relat_1(X0) != iProver_top
% 59.24/7.97      | v1_relat_1(k8_relat_1(X1,X0)) = iProver_top ),
% 59.24/7.97      inference(predicate_to_equality,[status(thm)],[c_6]) ).
% 59.24/7.97  
% 59.24/7.97  cnf(c_187051,plain,
% 59.24/7.97      ( k8_relat_1(X0,k8_relat_1(X0,X1)) = k8_relat_1(X0,X1)
% 59.24/7.97      | v1_relat_1(X1) != iProver_top ),
% 59.24/7.97      inference(forward_subsumption_resolution,[status(thm)],[c_3218,c_977]) ).
% 59.24/7.97  
% 59.24/7.97  cnf(c_187057,plain,
% 59.24/7.97      ( k8_relat_1(X0,k8_relat_1(X0,sK3)) = k8_relat_1(X0,sK3) ),
% 59.24/7.97      inference(superposition,[status(thm)],[c_2371,c_187051]) ).
% 59.24/7.97  
% 59.24/7.97  cnf(c_189939,plain,
% 59.24/7.97      ( r1_tarski(k2_relat_1(k8_relat_1(X0,sK3)),X0) = iProver_top
% 59.24/7.97      | v1_relat_1(k8_relat_1(X0,sK3)) != iProver_top ),
% 59.24/7.97      inference(superposition,[status(thm)],[c_187057,c_975]) ).
% 59.24/7.97  
% 59.24/7.97  cnf(c_2817,plain,
% 59.24/7.97      ( r1_tarski(k2_relat_1(k8_relat_1(X0,sK3)),X0) | ~ v1_relat_1(sK3) ),
% 59.24/7.97      inference(instantiation,[status(thm)],[c_8]) ).
% 59.24/7.97  
% 59.24/7.97  cnf(c_2818,plain,
% 59.24/7.97      ( r1_tarski(k2_relat_1(k8_relat_1(X0,sK3)),X0) = iProver_top
% 59.24/7.97      | v1_relat_1(sK3) != iProver_top ),
% 59.24/7.97      inference(predicate_to_equality,[status(thm)],[c_2817]) ).
% 59.24/7.97  
% 59.24/7.97  cnf(c_190961,plain,
% 59.24/7.97      ( r1_tarski(k2_relat_1(k8_relat_1(X0,sK3)),X0) = iProver_top ),
% 59.24/7.97      inference(global_propositional_subsumption,
% 59.24/7.97                [status(thm)],
% 59.24/7.97                [c_189939,c_22,c_1117,c_1404,c_1773,c_2818]) ).
% 59.24/7.97  
% 59.24/7.97  cnf(c_12,plain,
% 59.24/7.97      ( ~ r1_tarski(X0,X1)
% 59.24/7.97      | ~ v1_relat_1(X2)
% 59.24/7.97      | k8_relat_1(X0,k8_relat_1(X1,X2)) = k8_relat_1(X0,X2) ),
% 59.24/7.97      inference(cnf_transformation,[],[f61]) ).
% 59.24/7.97  
% 59.24/7.97  cnf(c_971,plain,
% 59.24/7.97      ( k8_relat_1(X0,k8_relat_1(X1,X2)) = k8_relat_1(X0,X2)
% 59.24/7.97      | r1_tarski(X0,X1) != iProver_top
% 59.24/7.97      | v1_relat_1(X2) != iProver_top ),
% 59.24/7.97      inference(predicate_to_equality,[status(thm)],[c_12]) ).
% 59.24/7.97  
% 59.24/7.97  cnf(c_190974,plain,
% 59.24/7.97      ( k8_relat_1(k2_relat_1(k8_relat_1(X0,sK3)),k8_relat_1(X0,X1)) = k8_relat_1(k2_relat_1(k8_relat_1(X0,sK3)),X1)
% 59.24/7.97      | v1_relat_1(X1) != iProver_top ),
% 59.24/7.97      inference(superposition,[status(thm)],[c_190961,c_971]) ).
% 59.24/7.97  
% 59.24/7.97  cnf(c_201208,plain,
% 59.24/7.97      ( k8_relat_1(k2_relat_1(k8_relat_1(X0,sK3)),k8_relat_1(X0,sK3)) = k8_relat_1(k2_relat_1(k8_relat_1(X0,sK3)),sK3) ),
% 59.24/7.97      inference(superposition,[status(thm)],[c_2371,c_190974]) ).
% 59.24/7.97  
% 59.24/7.97  cnf(c_11,plain,
% 59.24/7.97      ( ~ v1_relat_1(X0) | k8_relat_1(k2_relat_1(X0),X0) = X0 ),
% 59.24/7.97      inference(cnf_transformation,[],[f60]) ).
% 59.24/7.97  
% 59.24/7.97  cnf(c_972,plain,
% 59.24/7.97      ( k8_relat_1(k2_relat_1(X0),X0) = X0 | v1_relat_1(X0) != iProver_top ),
% 59.24/7.97      inference(predicate_to_equality,[status(thm)],[c_11]) ).
% 59.24/7.97  
% 59.24/7.97  cnf(c_1204,plain,
% 59.24/7.97      ( k8_relat_1(k2_relat_1(k8_relat_1(X0,X1)),k8_relat_1(X0,X1)) = k8_relat_1(X0,X1)
% 59.24/7.97      | v1_relat_1(X1) != iProver_top ),
% 59.24/7.97      inference(superposition,[status(thm)],[c_977,c_972]) ).
% 59.24/7.97  
% 59.24/7.97  cnf(c_16011,plain,
% 59.24/7.97      ( k8_relat_1(k2_relat_1(k8_relat_1(X0,sK3)),k8_relat_1(X0,sK3)) = k8_relat_1(X0,sK3) ),
% 59.24/7.97      inference(superposition,[status(thm)],[c_2371,c_1204]) ).
% 59.24/7.97  
% 59.24/7.97  cnf(c_201428,plain,
% 59.24/7.97      ( k8_relat_1(k2_relat_1(k8_relat_1(X0,sK3)),sK3) = k8_relat_1(X0,sK3) ),
% 59.24/7.97      inference(light_normalisation,[status(thm)],[c_201208,c_16011]) ).
% 59.24/7.97  
% 59.24/7.97  cnf(c_9,plain,
% 59.24/7.97      ( r1_tarski(k2_relat_1(k8_relat_1(X0,X1)),k2_relat_1(X1))
% 59.24/7.97      | ~ v1_relat_1(X1) ),
% 59.24/7.97      inference(cnf_transformation,[],[f58]) ).
% 59.24/7.97  
% 59.24/7.97  cnf(c_974,plain,
% 59.24/7.97      ( r1_tarski(k2_relat_1(k8_relat_1(X0,X1)),k2_relat_1(X1)) = iProver_top
% 59.24/7.97      | v1_relat_1(X1) != iProver_top ),
% 59.24/7.97      inference(predicate_to_equality,[status(thm)],[c_9]) ).
% 59.24/7.97  
% 59.24/7.97  cnf(c_14,plain,
% 59.24/7.97      ( v5_relat_1(X0,X1) | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) ),
% 59.24/7.97      inference(cnf_transformation,[],[f63]) ).
% 59.24/7.97  
% 59.24/7.97  cnf(c_5,plain,
% 59.24/7.97      ( ~ v5_relat_1(X0,X1) | r1_tarski(k2_relat_1(X0),X1) | ~ v1_relat_1(X0) ),
% 59.24/7.97      inference(cnf_transformation,[],[f53]) ).
% 59.24/7.97  
% 59.24/7.97  cnf(c_294,plain,
% 59.24/7.97      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 59.24/7.97      | r1_tarski(k2_relat_1(X0),X2)
% 59.24/7.97      | ~ v1_relat_1(X0) ),
% 59.24/7.97      inference(resolution,[status(thm)],[c_14,c_5]) ).
% 59.24/7.97  
% 59.24/7.97  cnf(c_961,plain,
% 59.24/7.97      ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) != iProver_top
% 59.24/7.97      | r1_tarski(k2_relat_1(X0),X2) = iProver_top
% 59.24/7.97      | v1_relat_1(X0) != iProver_top ),
% 59.24/7.97      inference(predicate_to_equality,[status(thm)],[c_294]) ).
% 59.24/7.97  
% 59.24/7.97  cnf(c_1501,plain,
% 59.24/7.97      ( r1_tarski(k2_relat_1(sK3),sK0) = iProver_top
% 59.24/7.97      | v1_relat_1(sK3) != iProver_top ),
% 59.24/7.97      inference(superposition,[status(thm)],[c_963,c_961]) ).
% 59.24/7.97  
% 59.24/7.97  cnf(c_1916,plain,
% 59.24/7.97      ( r1_tarski(k2_relat_1(sK3),sK0) = iProver_top ),
% 59.24/7.97      inference(global_propositional_subsumption,
% 59.24/7.97                [status(thm)],
% 59.24/7.97                [c_1501,c_22,c_1117,c_1404,c_1773]) ).
% 59.24/7.97  
% 59.24/7.97  cnf(c_0,plain,
% 59.24/7.97      ( ~ r1_tarski(X0,X1) | ~ r1_tarski(X2,X0) | r1_tarski(X2,X1) ),
% 59.24/7.97      inference(cnf_transformation,[],[f49]) ).
% 59.24/7.97  
% 59.24/7.97  cnf(c_980,plain,
% 59.24/7.97      ( r1_tarski(X0,X1) != iProver_top
% 59.24/7.97      | r1_tarski(X2,X0) != iProver_top
% 59.24/7.97      | r1_tarski(X2,X1) = iProver_top ),
% 59.24/7.97      inference(predicate_to_equality,[status(thm)],[c_0]) ).
% 59.24/7.97  
% 59.24/7.97  cnf(c_3251,plain,
% 59.24/7.97      ( r1_tarski(X0,k2_relat_1(sK3)) != iProver_top
% 59.24/7.97      | r1_tarski(X0,sK0) = iProver_top ),
% 59.24/7.97      inference(superposition,[status(thm)],[c_1916,c_980]) ).
% 59.24/7.97  
% 59.24/7.97  cnf(c_3788,plain,
% 59.24/7.97      ( r1_tarski(k2_relat_1(k8_relat_1(X0,sK3)),sK0) = iProver_top
% 59.24/7.97      | v1_relat_1(sK3) != iProver_top ),
% 59.24/7.97      inference(superposition,[status(thm)],[c_974,c_3251]) ).
% 59.24/7.97  
% 59.24/7.97  cnf(c_5377,plain,
% 59.24/7.97      ( r1_tarski(k2_relat_1(k8_relat_1(X0,sK3)),sK0) = iProver_top ),
% 59.24/7.97      inference(global_propositional_subsumption,
% 59.24/7.97                [status(thm)],
% 59.24/7.97                [c_3788,c_22,c_1117,c_1404,c_1773]) ).
% 59.24/7.97  
% 59.24/7.97  cnf(c_3220,plain,
% 59.24/7.97      ( k8_relat_1(sK0,sK3) = sK3 | v1_relat_1(sK3) != iProver_top ),
% 59.24/7.97      inference(superposition,[status(thm)],[c_1916,c_973]) ).
% 59.24/7.97  
% 59.24/7.97  cnf(c_3778,plain,
% 59.24/7.97      ( k8_relat_1(sK0,sK3) = sK3 ),
% 59.24/7.97      inference(global_propositional_subsumption,
% 59.24/7.97                [status(thm)],
% 59.24/7.97                [c_3220,c_22,c_1117,c_1404,c_1773]) ).
% 59.24/7.97  
% 59.24/7.97  cnf(c_13,plain,
% 59.24/7.97      ( ~ r1_tarski(X0,X1)
% 59.24/7.97      | r1_tarski(k8_relat_1(X0,X2),k8_relat_1(X1,X2))
% 59.24/7.97      | ~ v1_relat_1(X2) ),
% 59.24/7.97      inference(cnf_transformation,[],[f62]) ).
% 59.24/7.97  
% 59.24/7.97  cnf(c_970,plain,
% 59.24/7.97      ( r1_tarski(X0,X1) != iProver_top
% 59.24/7.97      | r1_tarski(k8_relat_1(X0,X2),k8_relat_1(X1,X2)) = iProver_top
% 59.24/7.97      | v1_relat_1(X2) != iProver_top ),
% 59.24/7.97      inference(predicate_to_equality,[status(thm)],[c_13]) ).
% 59.24/7.97  
% 59.24/7.97  cnf(c_4404,plain,
% 59.24/7.97      ( r1_tarski(X0,sK0) != iProver_top
% 59.24/7.97      | r1_tarski(k8_relat_1(X0,sK3),sK3) = iProver_top
% 59.24/7.97      | v1_relat_1(sK3) != iProver_top ),
% 59.24/7.97      inference(superposition,[status(thm)],[c_3778,c_970]) ).
% 59.24/7.97  
% 59.24/7.97  cnf(c_12177,plain,
% 59.24/7.97      ( r1_tarski(k8_relat_1(X0,sK3),sK3) = iProver_top
% 59.24/7.97      | r1_tarski(X0,sK0) != iProver_top ),
% 59.24/7.97      inference(global_propositional_subsumption,
% 59.24/7.97                [status(thm)],
% 59.24/7.97                [c_4404,c_22,c_1117,c_1404,c_1773]) ).
% 59.24/7.97  
% 59.24/7.97  cnf(c_12178,plain,
% 59.24/7.97      ( r1_tarski(X0,sK0) != iProver_top
% 59.24/7.97      | r1_tarski(k8_relat_1(X0,sK3),sK3) = iProver_top ),
% 59.24/7.97      inference(renaming,[status(thm)],[c_12177]) ).
% 59.24/7.97  
% 59.24/7.97  cnf(c_19,plain,
% 59.24/7.97      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 59.24/7.97      | m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 59.24/7.97      | ~ r1_tarski(X3,X0) ),
% 59.24/7.97      inference(cnf_transformation,[],[f68]) ).
% 59.24/7.97  
% 59.24/7.97  cnf(c_965,plain,
% 59.24/7.97      ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) != iProver_top
% 59.24/7.97      | m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) = iProver_top
% 59.24/7.97      | r1_tarski(X3,X0) != iProver_top ),
% 59.24/7.97      inference(predicate_to_equality,[status(thm)],[c_19]) ).
% 59.24/7.97  
% 59.24/7.97  cnf(c_2724,plain,
% 59.24/7.97      ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(sK2,sK0))) = iProver_top
% 59.24/7.97      | r1_tarski(X0,sK3) != iProver_top ),
% 59.24/7.97      inference(superposition,[status(thm)],[c_963,c_965]) ).
% 59.24/7.97  
% 59.24/7.97  cnf(c_16,plain,
% 59.24/7.97      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 59.24/7.97      | k1_relset_1(X1,X2,X0) = k1_relat_1(X0) ),
% 59.24/7.97      inference(cnf_transformation,[],[f65]) ).
% 59.24/7.97  
% 59.24/7.97  cnf(c_968,plain,
% 59.24/7.97      ( k1_relset_1(X0,X1,X2) = k1_relat_1(X2)
% 59.24/7.97      | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
% 59.24/7.97      inference(predicate_to_equality,[status(thm)],[c_16]) ).
% 59.24/7.97  
% 59.24/7.97  cnf(c_3583,plain,
% 59.24/7.97      ( k1_relset_1(sK2,sK0,X0) = k1_relat_1(X0)
% 59.24/7.97      | r1_tarski(X0,sK3) != iProver_top ),
% 59.24/7.97      inference(superposition,[status(thm)],[c_2724,c_968]) ).
% 59.24/7.97  
% 59.24/7.97  cnf(c_12194,plain,
% 59.24/7.97      ( k1_relset_1(sK2,sK0,k8_relat_1(X0,sK3)) = k1_relat_1(k8_relat_1(X0,sK3))
% 59.24/7.97      | r1_tarski(X0,sK0) != iProver_top ),
% 59.24/7.97      inference(superposition,[status(thm)],[c_12178,c_3583]) ).
% 59.24/7.97  
% 59.24/7.97  cnf(c_12256,plain,
% 59.24/7.97      ( k1_relset_1(sK2,sK0,k8_relat_1(k2_relat_1(k8_relat_1(X0,sK3)),sK3)) = k1_relat_1(k8_relat_1(k2_relat_1(k8_relat_1(X0,sK3)),sK3)) ),
% 59.24/7.97      inference(superposition,[status(thm)],[c_5377,c_12194]) ).
% 59.24/7.97  
% 59.24/7.97  cnf(c_15,plain,
% 59.24/7.97      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 59.24/7.97      | m1_subset_1(k1_relset_1(X1,X2,X0),k1_zfmisc_1(X1)) ),
% 59.24/7.97      inference(cnf_transformation,[],[f64]) ).
% 59.24/7.97  
% 59.24/7.97  cnf(c_969,plain,
% 59.24/7.97      ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) != iProver_top
% 59.24/7.97      | m1_subset_1(k1_relset_1(X1,X2,X0),k1_zfmisc_1(X1)) = iProver_top ),
% 59.24/7.97      inference(predicate_to_equality,[status(thm)],[c_15]) ).
% 59.24/7.97  
% 59.24/7.97  cnf(c_2972,plain,
% 59.24/7.97      ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) != iProver_top
% 59.24/7.97      | r1_tarski(k1_relset_1(X1,X2,X0),X1) = iProver_top ),
% 59.24/7.97      inference(superposition,[status(thm)],[c_969,c_978]) ).
% 59.24/7.97  
% 59.24/7.97  cnf(c_15489,plain,
% 59.24/7.97      ( r1_tarski(X0,sK3) != iProver_top
% 59.24/7.97      | r1_tarski(k1_relset_1(sK2,sK0,X0),sK2) = iProver_top ),
% 59.24/7.97      inference(superposition,[status(thm)],[c_2724,c_2972]) ).
% 59.24/7.97  
% 59.24/7.97  cnf(c_120811,plain,
% 59.24/7.97      ( r1_tarski(k8_relat_1(k2_relat_1(k8_relat_1(X0,sK3)),sK3),sK3) != iProver_top
% 59.24/7.97      | r1_tarski(k1_relat_1(k8_relat_1(k2_relat_1(k8_relat_1(X0,sK3)),sK3)),sK2) = iProver_top ),
% 59.24/7.97      inference(superposition,[status(thm)],[c_12256,c_15489]) ).
% 59.24/7.97  
% 59.24/7.97  cnf(c_206983,plain,
% 59.24/7.97      ( r1_tarski(k8_relat_1(X0,sK3),sK3) != iProver_top
% 59.24/7.97      | r1_tarski(k1_relat_1(k8_relat_1(X0,sK3)),sK2) = iProver_top ),
% 59.24/7.97      inference(demodulation,[status(thm)],[c_201428,c_120811]) ).
% 59.24/7.97  
% 59.24/7.97  cnf(c_2816,plain,
% 59.24/7.97      ( r1_tarski(k2_relat_1(k8_relat_1(X0,sK3)),k2_relat_1(sK3))
% 59.24/7.97      | ~ v1_relat_1(sK3) ),
% 59.24/7.97      inference(instantiation,[status(thm)],[c_9]) ).
% 59.24/7.97  
% 59.24/7.97  cnf(c_2822,plain,
% 59.24/7.97      ( r1_tarski(k2_relat_1(k8_relat_1(X0,sK3)),k2_relat_1(sK3)) = iProver_top
% 59.24/7.97      | v1_relat_1(sK3) != iProver_top ),
% 59.24/7.97      inference(predicate_to_equality,[status(thm)],[c_2816]) ).
% 59.24/7.97  
% 59.24/7.97  cnf(c_2376,plain,
% 59.24/7.97      ( k8_relat_1(k2_relat_1(sK3),sK3) = sK3 ),
% 59.24/7.97      inference(superposition,[status(thm)],[c_2371,c_972]) ).
% 59.24/7.97  
% 59.24/7.97  cnf(c_4403,plain,
% 59.24/7.97      ( r1_tarski(X0,k2_relat_1(sK3)) != iProver_top
% 59.24/7.97      | r1_tarski(k8_relat_1(X0,sK3),sK3) = iProver_top
% 59.24/7.97      | v1_relat_1(sK3) != iProver_top ),
% 59.24/7.97      inference(superposition,[status(thm)],[c_2376,c_970]) ).
% 59.24/7.97  
% 59.24/7.97  cnf(c_54445,plain,
% 59.24/7.97      ( r1_tarski(k8_relat_1(X0,sK3),sK3) = iProver_top
% 59.24/7.97      | r1_tarski(X0,k2_relat_1(sK3)) != iProver_top ),
% 59.24/7.97      inference(global_propositional_subsumption,
% 59.24/7.97                [status(thm)],
% 59.24/7.97                [c_4403,c_22,c_1117,c_1404,c_1773]) ).
% 59.24/7.97  
% 59.24/7.97  cnf(c_54446,plain,
% 59.24/7.97      ( r1_tarski(X0,k2_relat_1(sK3)) != iProver_top
% 59.24/7.97      | r1_tarski(k8_relat_1(X0,sK3),sK3) = iProver_top ),
% 59.24/7.97      inference(renaming,[status(thm)],[c_54445]) ).
% 59.24/7.97  
% 59.24/7.97  cnf(c_207080,plain,
% 59.24/7.97      ( r1_tarski(k8_relat_1(X0,sK3),sK3) = iProver_top
% 59.24/7.97      | r1_tarski(k2_relat_1(k8_relat_1(X0,sK3)),k2_relat_1(sK3)) != iProver_top ),
% 59.24/7.97      inference(superposition,[status(thm)],[c_201428,c_54446]) ).
% 59.24/7.97  
% 59.24/7.97  cnf(c_231908,plain,
% 59.24/7.97      ( r1_tarski(k1_relat_1(k8_relat_1(X0,sK3)),sK2) = iProver_top ),
% 59.24/7.97      inference(global_propositional_subsumption,
% 59.24/7.97                [status(thm)],
% 59.24/7.97                [c_206983,c_22,c_1117,c_1404,c_1773,c_2822,c_207080]) ).
% 59.24/7.97  
% 59.24/7.97  cnf(c_18,plain,
% 59.24/7.97      ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 59.24/7.97      | ~ r1_tarski(k1_relat_1(X0),X1)
% 59.24/7.97      | ~ r1_tarski(k2_relat_1(X0),X2)
% 59.24/7.97      | ~ v1_relat_1(X0) ),
% 59.24/7.97      inference(cnf_transformation,[],[f67]) ).
% 59.24/7.97  
% 59.24/7.97  cnf(c_966,plain,
% 59.24/7.97      ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) = iProver_top
% 59.24/7.97      | r1_tarski(k1_relat_1(X0),X1) != iProver_top
% 59.24/7.97      | r1_tarski(k2_relat_1(X0),X2) != iProver_top
% 59.24/7.97      | v1_relat_1(X0) != iProver_top ),
% 59.24/7.97      inference(predicate_to_equality,[status(thm)],[c_18]) ).
% 59.24/7.97  
% 59.24/7.97  cnf(c_17,plain,
% 59.24/7.97      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 59.24/7.97      | k6_relset_1(X1,X2,X3,X0) = k8_relat_1(X3,X0) ),
% 59.24/7.97      inference(cnf_transformation,[],[f66]) ).
% 59.24/7.97  
% 59.24/7.97  cnf(c_967,plain,
% 59.24/7.97      ( k6_relset_1(X0,X1,X2,X3) = k8_relat_1(X2,X3)
% 59.24/7.97      | m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
% 59.24/7.97      inference(predicate_to_equality,[status(thm)],[c_17]) ).
% 59.24/7.97  
% 59.24/7.97  cnf(c_2957,plain,
% 59.24/7.97      ( k6_relset_1(sK2,sK0,X0,sK3) = k8_relat_1(X0,sK3) ),
% 59.24/7.97      inference(superposition,[status(thm)],[c_963,c_967]) ).
% 59.24/7.97  
% 59.24/7.97  cnf(c_20,negated_conjecture,
% 59.24/7.97      ( ~ m1_subset_1(k6_relset_1(sK2,sK0,sK1,sK3),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) ),
% 59.24/7.97      inference(cnf_transformation,[],[f70]) ).
% 59.24/7.97  
% 59.24/7.97  cnf(c_964,plain,
% 59.24/7.97      ( m1_subset_1(k6_relset_1(sK2,sK0,sK1,sK3),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) != iProver_top ),
% 59.24/7.98      inference(predicate_to_equality,[status(thm)],[c_20]) ).
% 59.24/7.98  
% 59.24/7.98  cnf(c_3349,plain,
% 59.24/7.98      ( m1_subset_1(k8_relat_1(sK1,sK3),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) != iProver_top ),
% 59.24/7.98      inference(demodulation,[status(thm)],[c_2957,c_964]) ).
% 59.24/7.98  
% 59.24/7.98  cnf(c_4341,plain,
% 59.24/7.98      ( r1_tarski(k1_relat_1(k8_relat_1(sK1,sK3)),sK2) != iProver_top
% 59.24/7.98      | r1_tarski(k2_relat_1(k8_relat_1(sK1,sK3)),sK1) != iProver_top
% 59.24/7.98      | v1_relat_1(k8_relat_1(sK1,sK3)) != iProver_top ),
% 59.24/7.98      inference(superposition,[status(thm)],[c_966,c_3349]) ).
% 59.24/7.98  
% 59.24/7.98  cnf(c_231927,plain,
% 59.24/7.98      ( r1_tarski(k2_relat_1(k8_relat_1(sK1,sK3)),sK1) != iProver_top
% 59.24/7.98      | v1_relat_1(k8_relat_1(sK1,sK3)) != iProver_top ),
% 59.24/7.98      inference(superposition,[status(thm)],[c_231908,c_4341]) ).
% 59.24/7.98  
% 59.24/7.98  cnf(c_3250,plain,
% 59.24/7.98      ( r1_tarski(X0,k2_zfmisc_1(sK2,sK0)) = iProver_top
% 59.24/7.98      | r1_tarski(X0,sK3) != iProver_top ),
% 59.24/7.98      inference(superposition,[status(thm)],[c_1336,c_980]) ).
% 59.24/7.98  
% 59.24/7.98  cnf(c_4074,plain,
% 59.24/7.98      ( r1_tarski(X0,sK3) != iProver_top
% 59.24/7.98      | v1_relat_1(X0) = iProver_top
% 59.24/7.98      | v1_relat_1(k2_zfmisc_1(sK2,sK0)) != iProver_top ),
% 59.24/7.98      inference(superposition,[status(thm)],[c_3250,c_962]) ).
% 59.24/7.98  
% 59.24/7.98  cnf(c_2815,plain,
% 59.24/7.98      ( ~ r1_tarski(X0,sK3) | v1_relat_1(X0) | ~ v1_relat_1(sK3) ),
% 59.24/7.98      inference(instantiation,[status(thm)],[c_216]) ).
% 59.24/7.98  
% 59.24/7.98  cnf(c_2826,plain,
% 59.24/7.98      ( r1_tarski(X0,sK3) != iProver_top
% 59.24/7.98      | v1_relat_1(X0) = iProver_top
% 59.24/7.98      | v1_relat_1(sK3) != iProver_top ),
% 59.24/7.98      inference(predicate_to_equality,[status(thm)],[c_2815]) ).
% 59.24/7.98  
% 59.24/7.98  cnf(c_10131,plain,
% 59.24/7.98      ( v1_relat_1(X0) = iProver_top | r1_tarski(X0,sK3) != iProver_top ),
% 59.24/7.98      inference(global_propositional_subsumption,
% 59.24/7.98                [status(thm)],
% 59.24/7.98                [c_4074,c_22,c_1117,c_1404,c_1773,c_2826]) ).
% 59.24/7.98  
% 59.24/7.98  cnf(c_10132,plain,
% 59.24/7.98      ( r1_tarski(X0,sK3) != iProver_top | v1_relat_1(X0) = iProver_top ),
% 59.24/7.98      inference(renaming,[status(thm)],[c_10131]) ).
% 59.24/7.98  
% 59.24/7.98  cnf(c_12191,plain,
% 59.24/7.98      ( r1_tarski(X0,sK0) != iProver_top
% 59.24/7.98      | v1_relat_1(k8_relat_1(X0,sK3)) = iProver_top ),
% 59.24/7.98      inference(superposition,[status(thm)],[c_12178,c_10132]) ).
% 59.24/7.98  
% 59.24/7.98  cnf(c_2790,plain,
% 59.24/7.98      ( v1_relat_1(k8_relat_1(X0,sK3)) | ~ v1_relat_1(sK3) ),
% 59.24/7.98      inference(instantiation,[status(thm)],[c_6]) ).
% 59.24/7.98  
% 59.24/7.98  cnf(c_2801,plain,
% 59.24/7.98      ( v1_relat_1(k8_relat_1(X0,sK3)) = iProver_top
% 59.24/7.98      | v1_relat_1(sK3) != iProver_top ),
% 59.24/7.98      inference(predicate_to_equality,[status(thm)],[c_2790]) ).
% 59.24/7.98  
% 59.24/7.98  cnf(c_79645,plain,
% 59.24/7.98      ( v1_relat_1(k8_relat_1(X0,sK3)) = iProver_top ),
% 59.24/7.98      inference(global_propositional_subsumption,
% 59.24/7.98                [status(thm)],
% 59.24/7.98                [c_12191,c_22,c_1117,c_1404,c_1773,c_2801]) ).
% 59.24/7.98  
% 59.24/7.98  cnf(c_232138,plain,
% 59.24/7.98      ( $false ),
% 59.24/7.98      inference(forward_subsumption_resolution,
% 59.24/7.98                [status(thm)],
% 59.24/7.98                [c_231927,c_79645,c_190961]) ).
% 59.24/7.98  
% 59.24/7.98  
% 59.24/7.98  % SZS output end CNFRefutation for theBenchmark.p
% 59.24/7.98  
% 59.24/7.98  ------                               Statistics
% 59.24/7.98  
% 59.24/7.98  ------ General
% 59.24/7.98  
% 59.24/7.98  abstr_ref_over_cycles:                  0
% 59.24/7.98  abstr_ref_under_cycles:                 0
% 59.24/7.98  gc_basic_clause_elim:                   0
% 59.24/7.98  forced_gc_time:                         0
% 59.24/7.98  parsing_time:                           0.01
% 59.24/7.98  unif_index_cands_time:                  0.
% 59.24/7.98  unif_index_add_time:                    0.
% 59.24/7.98  orderings_time:                         0.
% 59.24/7.98  out_proof_time:                         0.047
% 59.24/7.98  total_time:                             7.064
% 59.24/7.98  num_of_symbols:                         46
% 59.24/7.98  num_of_terms:                           285166
% 59.24/7.98  
% 59.24/7.98  ------ Preprocessing
% 59.24/7.98  
% 59.24/7.98  num_of_splits:                          0
% 59.24/7.98  num_of_split_atoms:                     0
% 59.24/7.98  num_of_reused_defs:                     0
% 59.24/7.98  num_eq_ax_congr_red:                    14
% 59.24/7.98  num_of_sem_filtered_clauses:            1
% 59.24/7.98  num_of_subtypes:                        0
% 59.24/7.98  monotx_restored_types:                  0
% 59.24/7.98  sat_num_of_epr_types:                   0
% 59.24/7.98  sat_num_of_non_cyclic_types:            0
% 59.24/7.98  sat_guarded_non_collapsed_types:        0
% 59.24/7.98  num_pure_diseq_elim:                    0
% 59.24/7.98  simp_replaced_by:                       0
% 59.24/7.98  res_preprocessed:                       103
% 59.24/7.98  prep_upred:                             0
% 59.24/7.98  prep_unflattend:                        0
% 59.24/7.98  smt_new_axioms:                         0
% 59.24/7.98  pred_elim_cands:                        3
% 59.24/7.98  pred_elim:                              1
% 59.24/7.98  pred_elim_cl:                           2
% 59.24/7.98  pred_elim_cycles:                       3
% 59.24/7.98  merged_defs:                            8
% 59.24/7.98  merged_defs_ncl:                        0
% 59.24/7.98  bin_hyper_res:                          9
% 59.24/7.98  prep_cycles:                            4
% 59.24/7.98  pred_elim_time:                         0.001
% 59.24/7.98  splitting_time:                         0.
% 59.24/7.98  sem_filter_time:                        0.
% 59.24/7.98  monotx_time:                            0.
% 59.24/7.98  subtype_inf_time:                       0.
% 59.24/7.98  
% 59.24/7.98  ------ Problem properties
% 59.24/7.98  
% 59.24/7.98  clauses:                                20
% 59.24/7.98  conjectures:                            2
% 59.24/7.98  epr:                                    2
% 59.24/7.98  horn:                                   20
% 59.24/7.98  ground:                                 2
% 59.24/7.98  unary:                                  3
% 59.24/7.98  binary:                                 9
% 59.24/7.98  lits:                                   46
% 59.24/7.98  lits_eq:                                5
% 59.24/7.98  fd_pure:                                0
% 59.24/7.98  fd_pseudo:                              0
% 59.24/7.98  fd_cond:                                0
% 59.24/7.98  fd_pseudo_cond:                         0
% 59.24/7.98  ac_symbols:                             0
% 59.24/7.98  
% 59.24/7.98  ------ Propositional Solver
% 59.24/7.98  
% 59.24/7.98  prop_solver_calls:                      94
% 59.24/7.98  prop_fast_solver_calls:                 2613
% 59.24/7.98  smt_solver_calls:                       0
% 59.24/7.98  smt_fast_solver_calls:                  0
% 59.24/7.98  prop_num_of_clauses:                    93435
% 59.24/7.98  prop_preprocess_simplified:             142656
% 59.24/7.98  prop_fo_subsumed:                       116
% 59.24/7.98  prop_solver_time:                       0.
% 59.24/7.98  smt_solver_time:                        0.
% 59.24/7.98  smt_fast_solver_time:                   0.
% 59.24/7.98  prop_fast_solver_time:                  0.
% 59.24/7.98  prop_unsat_core_time:                   0.
% 59.24/7.98  
% 59.24/7.98  ------ QBF
% 59.24/7.98  
% 59.24/7.98  qbf_q_res:                              0
% 59.24/7.98  qbf_num_tautologies:                    0
% 59.24/7.98  qbf_prep_cycles:                        0
% 59.24/7.98  
% 59.24/7.98  ------ BMC1
% 59.24/7.98  
% 59.24/7.98  bmc1_current_bound:                     -1
% 59.24/7.98  bmc1_last_solved_bound:                 -1
% 59.24/7.98  bmc1_unsat_core_size:                   -1
% 59.24/7.98  bmc1_unsat_core_parents_size:           -1
% 59.24/7.98  bmc1_merge_next_fun:                    0
% 59.24/7.98  bmc1_unsat_core_clauses_time:           0.
% 59.24/7.98  
% 59.24/7.98  ------ Instantiation
% 59.24/7.98  
% 59.24/7.98  inst_num_of_clauses:                    4978
% 59.24/7.98  inst_num_in_passive:                    3057
% 59.24/7.98  inst_num_in_active:                     3958
% 59.24/7.98  inst_num_in_unprocessed:                681
% 59.24/7.98  inst_num_of_loops:                      4309
% 59.24/7.98  inst_num_of_learning_restarts:          1
% 59.24/7.98  inst_num_moves_active_passive:          349
% 59.24/7.98  inst_lit_activity:                      0
% 59.24/7.98  inst_lit_activity_moves:                7
% 59.24/7.98  inst_num_tautologies:                   0
% 59.24/7.98  inst_num_prop_implied:                  0
% 59.24/7.98  inst_num_existing_simplified:           0
% 59.24/7.98  inst_num_eq_res_simplified:             0
% 59.24/7.98  inst_num_child_elim:                    0
% 59.24/7.98  inst_num_of_dismatching_blockings:      31737
% 59.24/7.98  inst_num_of_non_proper_insts:           16488
% 59.24/7.98  inst_num_of_duplicates:                 0
% 59.24/7.98  inst_inst_num_from_inst_to_res:         0
% 59.24/7.98  inst_dismatching_checking_time:         0.
% 59.24/7.98  
% 59.24/7.98  ------ Resolution
% 59.24/7.98  
% 59.24/7.98  res_num_of_clauses:                     30
% 59.24/7.98  res_num_in_passive:                     30
% 59.24/7.98  res_num_in_active:                      0
% 59.24/7.98  res_num_of_loops:                       107
% 59.24/7.98  res_forward_subset_subsumed:            140
% 59.24/7.98  res_backward_subset_subsumed:           0
% 59.24/7.98  res_forward_subsumed:                   0
% 59.24/7.98  res_backward_subsumed:                  0
% 59.24/7.98  res_forward_subsumption_resolution:     0
% 59.24/7.98  res_backward_subsumption_resolution:    0
% 59.24/7.98  res_clause_to_clause_subsumption:       35953
% 59.24/7.98  res_orphan_elimination:                 0
% 59.24/7.98  res_tautology_del:                      387
% 59.24/7.98  res_num_eq_res_simplified:              0
% 59.24/7.98  res_num_sel_changes:                    0
% 59.24/7.98  res_moves_from_active_to_pass:          0
% 59.24/7.98  
% 59.24/7.98  ------ Superposition
% 59.24/7.98  
% 59.24/7.98  sup_time_total:                         0.
% 59.24/7.98  sup_time_generating:                    0.
% 59.24/7.98  sup_time_sim_full:                      0.
% 59.24/7.98  sup_time_sim_immed:                     0.
% 59.24/7.98  
% 59.24/7.98  sup_num_of_clauses:                     8132
% 59.24/7.98  sup_num_in_active:                      823
% 59.24/7.98  sup_num_in_passive:                     7309
% 59.24/7.98  sup_num_of_loops:                       860
% 59.24/7.98  sup_fw_superposition:                   4477
% 59.24/7.98  sup_bw_superposition:                   7586
% 59.24/7.98  sup_immediate_simplified:               1934
% 59.24/7.98  sup_given_eliminated:                   1
% 59.24/7.98  comparisons_done:                       0
% 59.24/7.98  comparisons_avoided:                    0
% 59.24/7.98  
% 59.24/7.98  ------ Simplifications
% 59.24/7.98  
% 59.24/7.98  
% 59.24/7.98  sim_fw_subset_subsumed:                 506
% 59.24/7.98  sim_bw_subset_subsumed:                 228
% 59.24/7.98  sim_fw_subsumed:                        711
% 59.24/7.98  sim_bw_subsumed:                        105
% 59.24/7.98  sim_fw_subsumption_res:                 19
% 59.24/7.98  sim_bw_subsumption_res:                 0
% 59.24/7.98  sim_tautology_del:                      183
% 59.24/7.98  sim_eq_tautology_del:                   261
% 59.24/7.98  sim_eq_res_simp:                        0
% 59.24/7.98  sim_fw_demodulated:                     227
% 59.24/7.98  sim_bw_demodulated:                     46
% 59.24/7.98  sim_light_normalised:                   447
% 59.24/7.98  sim_joinable_taut:                      0
% 59.24/7.98  sim_joinable_simp:                      0
% 59.24/7.98  sim_ac_normalised:                      0
% 59.24/7.98  sim_smt_subsumption:                    0
% 59.24/7.98  
%------------------------------------------------------------------------------
