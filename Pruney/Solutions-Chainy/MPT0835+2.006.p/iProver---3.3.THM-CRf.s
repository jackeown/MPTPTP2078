%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n013.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 11:56:08 EST 2020

% Result     : Theorem 2.49s
% Output     : CNFRefutation 2.49s
% Verified   : 
% Statistics : Number of formulae       :  143 ( 403 expanded)
%              Number of clauses        :   83 ( 174 expanded)
%              Number of leaves         :   19 (  80 expanded)
%              Depth                    :   18
%              Number of atoms          :  315 ( 968 expanded)
%              Number of equality atoms :  166 ( 469 expanded)
%              Maximal formula depth    :    8 (   4 average)
%              Maximal clause size      :    6 (   2 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f2,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ( v5_relat_1(X1,X0)
      <=> r1_tarski(k2_relat_1(X1),X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f19,plain,(
    ! [X0,X1] :
      ( ( v5_relat_1(X1,X0)
      <=> r1_tarski(k2_relat_1(X1),X0) )
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f38,plain,(
    ! [X0,X1] :
      ( ( ( v5_relat_1(X1,X0)
          | ~ r1_tarski(k2_relat_1(X1),X0) )
        & ( r1_tarski(k2_relat_1(X1),X0)
          | ~ v5_relat_1(X1,X0) ) )
      | ~ v1_relat_1(X1) ) ),
    inference(nnf_transformation,[],[f19])).

fof(f44,plain,(
    ! [X0,X1] :
      ( r1_tarski(k2_relat_1(X1),X0)
      | ~ v5_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f38])).

fof(f12,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => ( v5_relat_1(X2,X1)
        & v4_relat_1(X2,X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f30,plain,(
    ! [X0,X1,X2] :
      ( ( v5_relat_1(X2,X1)
        & v4_relat_1(X2,X0) )
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f57,plain,(
    ! [X2,X0,X1] :
      ( v5_relat_1(X2,X1)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f11,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => v1_relat_1(X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f29,plain,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f55,plain,(
    ! [X2,X0,X1] :
      ( v1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f17,conjecture,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
     => ( k1_relset_1(X1,X0,X2) = k8_relset_1(X1,X0,X2,k7_relset_1(X1,X0,X2,X1))
        & k2_relset_1(X1,X0,X2) = k7_relset_1(X1,X0,X2,k8_relset_1(X1,X0,X2,X0)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f18,negated_conjecture,(
    ~ ! [X0,X1,X2] :
        ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
       => ( k1_relset_1(X1,X0,X2) = k8_relset_1(X1,X0,X2,k7_relset_1(X1,X0,X2,X1))
          & k2_relset_1(X1,X0,X2) = k7_relset_1(X1,X0,X2,k8_relset_1(X1,X0,X2,X0)) ) ) ),
    inference(negated_conjecture,[],[f17])).

fof(f35,plain,(
    ? [X0,X1,X2] :
      ( ( k1_relset_1(X1,X0,X2) != k8_relset_1(X1,X0,X2,k7_relset_1(X1,X0,X2,X1))
        | k2_relset_1(X1,X0,X2) != k7_relset_1(X1,X0,X2,k8_relset_1(X1,X0,X2,X0)) )
      & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) ) ),
    inference(ennf_transformation,[],[f18])).

fof(f39,plain,
    ( ? [X0,X1,X2] :
        ( ( k1_relset_1(X1,X0,X2) != k8_relset_1(X1,X0,X2,k7_relset_1(X1,X0,X2,X1))
          | k2_relset_1(X1,X0,X2) != k7_relset_1(X1,X0,X2,k8_relset_1(X1,X0,X2,X0)) )
        & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) )
   => ( ( k1_relset_1(sK1,sK0,sK2) != k8_relset_1(sK1,sK0,sK2,k7_relset_1(sK1,sK0,sK2,sK1))
        | k2_relset_1(sK1,sK0,sK2) != k7_relset_1(sK1,sK0,sK2,k8_relset_1(sK1,sK0,sK2,sK0)) )
      & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) ) ),
    introduced(choice_axiom,[])).

fof(f40,plain,
    ( ( k1_relset_1(sK1,sK0,sK2) != k8_relset_1(sK1,sK0,sK2,k7_relset_1(sK1,sK0,sK2,sK1))
      | k2_relset_1(sK1,sK0,sK2) != k7_relset_1(sK1,sK0,sK2,k8_relset_1(sK1,sK0,sK2,sK0)) )
    & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f35,f39])).

fof(f62,plain,(
    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) ),
    inference(cnf_transformation,[],[f40])).

fof(f9,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ( r1_tarski(k2_relat_1(X1),X0)
       => k5_relat_1(X1,k6_relat_1(X0)) = X1 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f25,plain,(
    ! [X0,X1] :
      ( k5_relat_1(X1,k6_relat_1(X0)) = X1
      | ~ r1_tarski(k2_relat_1(X1),X0)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f9])).

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

fof(f3,axiom,(
    ! [X0] : v1_relat_1(k6_relat_1(X0)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f46,plain,(
    ! [X0] : v1_relat_1(k6_relat_1(X0)) ),
    inference(cnf_transformation,[],[f3])).

fof(f6,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( v1_relat_1(X1)
         => k10_relat_1(X0,k1_relat_1(X1)) = k1_relat_1(k5_relat_1(X0,X1)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f22,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k10_relat_1(X0,k1_relat_1(X1)) = k1_relat_1(k5_relat_1(X0,X1))
          | ~ v1_relat_1(X1) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f49,plain,(
    ! [X0,X1] :
      ( k10_relat_1(X0,k1_relat_1(X1)) = k1_relat_1(k5_relat_1(X0,X1))
      | ~ v1_relat_1(X1)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f8,axiom,(
    ! [X0] :
      ( k2_relat_1(k6_relat_1(X0)) = X0
      & k1_relat_1(k6_relat_1(X0)) = X0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f51,plain,(
    ! [X0] : k1_relat_1(k6_relat_1(X0)) = X0 ),
    inference(cnf_transformation,[],[f8])).

fof(f56,plain,(
    ! [X2,X0,X1] :
      ( v4_relat_1(X2,X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f7,axiom,(
    ! [X0,X1] :
      ( ( v4_relat_1(X1,X0)
        & v1_relat_1(X1) )
     => k7_relat_1(X1,X0) = X1 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f23,plain,(
    ! [X0,X1] :
      ( k7_relat_1(X1,X0) = X1
      | ~ v4_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f7])).

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

fof(f4,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => k2_relat_1(k7_relat_1(X1,X0)) = k9_relat_1(X1,X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f20,plain,(
    ! [X0,X1] :
      ( k2_relat_1(k7_relat_1(X1,X0)) = k9_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f47,plain,(
    ! [X0,X1] :
      ( k2_relat_1(k7_relat_1(X1,X0)) = k9_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f13,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k1_relat_1(X2) = k1_relset_1(X0,X1,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f31,plain,(
    ! [X0,X1,X2] :
      ( k1_relat_1(X2) = k1_relset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f58,plain,(
    ! [X2,X0,X1] :
      ( k1_relat_1(X2) = k1_relset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f14,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k2_relat_1(X2) = k2_relset_1(X0,X1,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f32,plain,(
    ! [X0,X1,X2] :
      ( k2_relat_1(X2) = k2_relset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f59,plain,(
    ! [X2,X0,X1] :
      ( k2_relat_1(X2) = k2_relset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f32])).

fof(f63,plain,
    ( k1_relset_1(sK1,sK0,sK2) != k8_relset_1(sK1,sK0,sK2,k7_relset_1(sK1,sK0,sK2,sK1))
    | k2_relset_1(sK1,sK0,sK2) != k7_relset_1(sK1,sK0,sK2,k8_relset_1(sK1,sK0,sK2,sK0)) ),
    inference(cnf_transformation,[],[f40])).

fof(f16,axiom,(
    ! [X0,X1,X2,X3] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k10_relat_1(X2,X3) = k8_relset_1(X0,X1,X2,X3) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f34,plain,(
    ! [X0,X1,X2,X3] :
      ( k10_relat_1(X2,X3) = k8_relset_1(X0,X1,X2,X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f16])).

fof(f61,plain,(
    ! [X2,X0,X3,X1] :
      ( k10_relat_1(X2,X3) = k8_relset_1(X0,X1,X2,X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f34])).

fof(f15,axiom,(
    ! [X0,X1,X2,X3] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k9_relat_1(X2,X3) = k7_relset_1(X0,X1,X2,X3) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f33,plain,(
    ! [X0,X1,X2,X3] :
      ( k9_relat_1(X2,X3) = k7_relset_1(X0,X1,X2,X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f15])).

fof(f60,plain,(
    ! [X2,X0,X3,X1] :
      ( k9_relat_1(X2,X3) = k7_relset_1(X0,X1,X2,X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f33])).

fof(f5,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => k10_relat_1(X0,k2_relat_1(X0)) = k1_relat_1(X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f21,plain,(
    ! [X0] :
      ( k10_relat_1(X0,k2_relat_1(X0)) = k1_relat_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f48,plain,(
    ! [X0] :
      ( k10_relat_1(X0,k2_relat_1(X0)) = k1_relat_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( X0 = X1
    <=> ( r1_tarski(X1,X0)
        & r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f36,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(nnf_transformation,[],[f1])).

fof(f37,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(flattening,[],[f36])).

fof(f42,plain,(
    ! [X0,X1] :
      ( r1_tarski(X1,X0)
      | X0 != X1 ) ),
    inference(cnf_transformation,[],[f37])).

fof(f64,plain,(
    ! [X1] : r1_tarski(X1,X1) ),
    inference(equality_resolution,[],[f42])).

fof(f10,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ( r1_tarski(k1_relat_1(X1),X0)
       => k7_relat_1(X1,X0) = X1 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f27,plain,(
    ! [X0,X1] :
      ( k7_relat_1(X1,X0) = X1
      | ~ r1_tarski(k1_relat_1(X1),X0)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f10])).

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

cnf(c_4,plain,
    ( ~ v5_relat_1(X0,X1)
    | r1_tarski(k2_relat_1(X0),X1)
    | ~ v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f44])).

cnf(c_15,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | v5_relat_1(X0,X2) ),
    inference(cnf_transformation,[],[f57])).

cnf(c_263,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | r1_tarski(k2_relat_1(X3),X4)
    | ~ v1_relat_1(X3)
    | X0 != X3
    | X2 != X4 ),
    inference(resolution_lifted,[status(thm)],[c_4,c_15])).

cnf(c_264,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | r1_tarski(k2_relat_1(X0),X2)
    | ~ v1_relat_1(X0) ),
    inference(unflattening,[status(thm)],[c_263])).

cnf(c_14,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f55])).

cnf(c_268,plain,
    ( r1_tarski(k2_relat_1(X0),X2)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) ),
    inference(global_propositional_subsumption,[status(thm)],[c_264,c_14])).

cnf(c_269,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | r1_tarski(k2_relat_1(X0),X2) ),
    inference(renaming,[status(thm)],[c_268])).

cnf(c_22,negated_conjecture,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) ),
    inference(cnf_transformation,[],[f62])).

cnf(c_284,plain,
    ( r1_tarski(k2_relat_1(X0),X1)
    | k1_zfmisc_1(k2_zfmisc_1(X2,X1)) != k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))
    | sK2 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_269,c_22])).

cnf(c_285,plain,
    ( r1_tarski(k2_relat_1(sK2),X0)
    | k1_zfmisc_1(k2_zfmisc_1(X1,X0)) != k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)) ),
    inference(unflattening,[status(thm)],[c_284])).

cnf(c_658,plain,
    ( k1_zfmisc_1(k2_zfmisc_1(X0,X1)) != k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))
    | r1_tarski(k2_relat_1(sK2),X1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_285])).

cnf(c_1311,plain,
    ( r1_tarski(k2_relat_1(sK2),sK0) = iProver_top ),
    inference(equality_resolution,[status(thm)],[c_658])).

cnf(c_12,plain,
    ( ~ r1_tarski(k2_relat_1(X0),X1)
    | ~ v1_relat_1(X0)
    | k5_relat_1(X0,k6_relat_1(X1)) = X0 ),
    inference(cnf_transformation,[],[f53])).

cnf(c_660,plain,
    ( k5_relat_1(X0,k6_relat_1(X1)) = X0
    | r1_tarski(k2_relat_1(X0),X1) != iProver_top
    | v1_relat_1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_12])).

cnf(c_2516,plain,
    ( k5_relat_1(sK2,k6_relat_1(sK0)) = sK2
    | v1_relat_1(sK2) != iProver_top ),
    inference(superposition,[status(thm)],[c_1311,c_660])).

cnf(c_451,plain,
    ( X0 = X0 ),
    theory(equality)).

cnf(c_766,plain,
    ( k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)) = k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)) ),
    inference(instantiation,[status(thm)],[c_451])).

cnf(c_767,plain,
    ( r1_tarski(k2_relat_1(sK2),sK0)
    | k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)) != k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)) ),
    inference(instantiation,[status(thm)],[c_285])).

cnf(c_341,plain,
    ( v1_relat_1(X0)
    | k1_zfmisc_1(k2_zfmisc_1(X1,X2)) != k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))
    | sK2 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_14,c_22])).

cnf(c_342,plain,
    ( v1_relat_1(sK2)
    | k1_zfmisc_1(k2_zfmisc_1(X0,X1)) != k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)) ),
    inference(unflattening,[status(thm)],[c_341])).

cnf(c_855,plain,
    ( v1_relat_1(sK2)
    | k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)) != k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)) ),
    inference(instantiation,[status(thm)],[c_342])).

cnf(c_929,plain,
    ( ~ r1_tarski(k2_relat_1(sK2),X0)
    | ~ v1_relat_1(sK2)
    | k5_relat_1(sK2,k6_relat_1(X0)) = sK2 ),
    inference(instantiation,[status(thm)],[c_12])).

cnf(c_944,plain,
    ( ~ r1_tarski(k2_relat_1(sK2),sK0)
    | ~ v1_relat_1(sK2)
    | k5_relat_1(sK2,k6_relat_1(sK0)) = sK2 ),
    inference(instantiation,[status(thm)],[c_929])).

cnf(c_2942,plain,
    ( k5_relat_1(sK2,k6_relat_1(sK0)) = sK2 ),
    inference(global_propositional_subsumption,[status(thm)],[c_2516,c_766,c_767,c_855,c_944])).

cnf(c_5,plain,
    ( v1_relat_1(k6_relat_1(X0)) ),
    inference(cnf_transformation,[],[f46])).

cnf(c_664,plain,
    ( v1_relat_1(k6_relat_1(X0)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_5])).

cnf(c_657,plain,
    ( k1_zfmisc_1(k2_zfmisc_1(X0,X1)) != k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))
    | v1_relat_1(sK2) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_342])).

cnf(c_856,plain,
    ( k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)) != k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))
    | v1_relat_1(sK2) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_855])).

cnf(c_956,plain,
    ( v1_relat_1(sK2) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_657,c_766,c_856])).

cnf(c_8,plain,
    ( ~ v1_relat_1(X0)
    | ~ v1_relat_1(X1)
    | k1_relat_1(k5_relat_1(X1,X0)) = k10_relat_1(X1,k1_relat_1(X0)) ),
    inference(cnf_transformation,[],[f49])).

cnf(c_661,plain,
    ( k1_relat_1(k5_relat_1(X0,X1)) = k10_relat_1(X0,k1_relat_1(X1))
    | v1_relat_1(X1) != iProver_top
    | v1_relat_1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_8])).

cnf(c_2693,plain,
    ( k1_relat_1(k5_relat_1(sK2,X0)) = k10_relat_1(sK2,k1_relat_1(X0))
    | v1_relat_1(X0) != iProver_top ),
    inference(superposition,[status(thm)],[c_956,c_661])).

cnf(c_2828,plain,
    ( k1_relat_1(k5_relat_1(sK2,k6_relat_1(X0))) = k10_relat_1(sK2,k1_relat_1(k6_relat_1(X0))) ),
    inference(superposition,[status(thm)],[c_664,c_2693])).

cnf(c_11,plain,
    ( k1_relat_1(k6_relat_1(X0)) = X0 ),
    inference(cnf_transformation,[],[f51])).

cnf(c_2833,plain,
    ( k1_relat_1(k5_relat_1(sK2,k6_relat_1(X0))) = k10_relat_1(sK2,X0) ),
    inference(light_normalisation,[status(thm)],[c_2828,c_11])).

cnf(c_3038,plain,
    ( k10_relat_1(sK2,sK0) = k1_relat_1(sK2) ),
    inference(superposition,[status(thm)],[c_2942,c_2833])).

cnf(c_16,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | v4_relat_1(X0,X1) ),
    inference(cnf_transformation,[],[f56])).

cnf(c_9,plain,
    ( ~ v4_relat_1(X0,X1)
    | ~ v1_relat_1(X0)
    | k7_relat_1(X0,X1) = X0 ),
    inference(cnf_transformation,[],[f50])).

cnf(c_242,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ v1_relat_1(X0)
    | k7_relat_1(X0,X1) = X0 ),
    inference(resolution,[status(thm)],[c_16,c_9])).

cnf(c_246,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k7_relat_1(X0,X1) = X0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_242,c_16,c_14,c_9])).

cnf(c_296,plain,
    ( k7_relat_1(X0,X1) = X0
    | k1_zfmisc_1(k2_zfmisc_1(X1,X2)) != k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))
    | sK2 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_246,c_22])).

cnf(c_297,plain,
    ( k7_relat_1(sK2,X0) = sK2
    | k1_zfmisc_1(k2_zfmisc_1(X0,X1)) != k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)) ),
    inference(unflattening,[status(thm)],[c_296])).

cnf(c_765,plain,
    ( k7_relat_1(sK2,sK1) = sK2 ),
    inference(equality_resolution,[status(thm)],[c_297])).

cnf(c_6,plain,
    ( ~ v1_relat_1(X0)
    | k2_relat_1(k7_relat_1(X0,X1)) = k9_relat_1(X0,X1) ),
    inference(cnf_transformation,[],[f47])).

cnf(c_663,plain,
    ( k2_relat_1(k7_relat_1(X0,X1)) = k9_relat_1(X0,X1)
    | v1_relat_1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_6])).

cnf(c_1622,plain,
    ( k2_relat_1(k7_relat_1(sK2,X0)) = k9_relat_1(sK2,X0) ),
    inference(superposition,[status(thm)],[c_956,c_663])).

cnf(c_1913,plain,
    ( k9_relat_1(sK2,sK1) = k2_relat_1(sK2) ),
    inference(superposition,[status(thm)],[c_765,c_1622])).

cnf(c_17,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k1_relset_1(X1,X2,X0) = k1_relat_1(X0) ),
    inference(cnf_transformation,[],[f58])).

cnf(c_332,plain,
    ( k1_relset_1(X0,X1,X2) = k1_relat_1(X2)
    | k1_zfmisc_1(k2_zfmisc_1(X0,X1)) != k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))
    | sK2 != X2 ),
    inference(resolution_lifted,[status(thm)],[c_17,c_22])).

cnf(c_333,plain,
    ( k1_relset_1(X0,X1,sK2) = k1_relat_1(sK2)
    | k1_zfmisc_1(k2_zfmisc_1(X0,X1)) != k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)) ),
    inference(unflattening,[status(thm)],[c_332])).

cnf(c_788,plain,
    ( k1_relset_1(sK1,sK0,sK2) = k1_relat_1(sK2) ),
    inference(equality_resolution,[status(thm)],[c_333])).

cnf(c_18,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k2_relset_1(X1,X2,X0) = k2_relat_1(X0) ),
    inference(cnf_transformation,[],[f59])).

cnf(c_323,plain,
    ( k2_relset_1(X0,X1,X2) = k2_relat_1(X2)
    | k1_zfmisc_1(k2_zfmisc_1(X0,X1)) != k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))
    | sK2 != X2 ),
    inference(resolution_lifted,[status(thm)],[c_18,c_22])).

cnf(c_324,plain,
    ( k2_relset_1(X0,X1,sK2) = k2_relat_1(sK2)
    | k1_zfmisc_1(k2_zfmisc_1(X0,X1)) != k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)) ),
    inference(unflattening,[status(thm)],[c_323])).

cnf(c_785,plain,
    ( k2_relset_1(sK1,sK0,sK2) = k2_relat_1(sK2) ),
    inference(equality_resolution,[status(thm)],[c_324])).

cnf(c_21,negated_conjecture,
    ( k2_relset_1(sK1,sK0,sK2) != k7_relset_1(sK1,sK0,sK2,k8_relset_1(sK1,sK0,sK2,sK0))
    | k1_relset_1(sK1,sK0,sK2) != k8_relset_1(sK1,sK0,sK2,k7_relset_1(sK1,sK0,sK2,sK1)) ),
    inference(cnf_transformation,[],[f63])).

cnf(c_870,plain,
    ( k8_relset_1(sK1,sK0,sK2,k7_relset_1(sK1,sK0,sK2,sK1)) != k1_relset_1(sK1,sK0,sK2)
    | k7_relset_1(sK1,sK0,sK2,k8_relset_1(sK1,sK0,sK2,sK0)) != k2_relat_1(sK2) ),
    inference(demodulation,[status(thm)],[c_785,c_21])).

cnf(c_1214,plain,
    ( k8_relset_1(sK1,sK0,sK2,k7_relset_1(sK1,sK0,sK2,sK1)) != k1_relat_1(sK2)
    | k7_relset_1(sK1,sK0,sK2,k8_relset_1(sK1,sK0,sK2,sK0)) != k2_relat_1(sK2) ),
    inference(demodulation,[status(thm)],[c_788,c_870])).

cnf(c_20,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k8_relset_1(X1,X2,X0,X3) = k10_relat_1(X0,X3) ),
    inference(cnf_transformation,[],[f61])).

cnf(c_305,plain,
    ( k8_relset_1(X0,X1,X2,X3) = k10_relat_1(X2,X3)
    | k1_zfmisc_1(k2_zfmisc_1(X0,X1)) != k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))
    | sK2 != X2 ),
    inference(resolution_lifted,[status(thm)],[c_20,c_22])).

cnf(c_306,plain,
    ( k8_relset_1(X0,X1,sK2,X2) = k10_relat_1(sK2,X2)
    | k1_zfmisc_1(k2_zfmisc_1(X0,X1)) != k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)) ),
    inference(unflattening,[status(thm)],[c_305])).

cnf(c_821,plain,
    ( k8_relset_1(sK1,sK0,sK2,X0) = k10_relat_1(sK2,X0) ),
    inference(equality_resolution,[status(thm)],[c_306])).

cnf(c_19,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k7_relset_1(X1,X2,X0,X3) = k9_relat_1(X0,X3) ),
    inference(cnf_transformation,[],[f60])).

cnf(c_314,plain,
    ( k7_relset_1(X0,X1,X2,X3) = k9_relat_1(X2,X3)
    | k1_zfmisc_1(k2_zfmisc_1(X0,X1)) != k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))
    | sK2 != X2 ),
    inference(resolution_lifted,[status(thm)],[c_19,c_22])).

cnf(c_315,plain,
    ( k7_relset_1(X0,X1,sK2,X2) = k9_relat_1(sK2,X2)
    | k1_zfmisc_1(k2_zfmisc_1(X0,X1)) != k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)) ),
    inference(unflattening,[status(thm)],[c_314])).

cnf(c_825,plain,
    ( k7_relset_1(sK1,sK0,sK2,X0) = k9_relat_1(sK2,X0) ),
    inference(equality_resolution,[status(thm)],[c_315])).

cnf(c_1413,plain,
    ( k10_relat_1(sK2,k9_relat_1(sK2,sK1)) != k1_relat_1(sK2)
    | k9_relat_1(sK2,k10_relat_1(sK2,sK0)) != k2_relat_1(sK2) ),
    inference(demodulation,[status(thm)],[c_1214,c_821,c_825])).

cnf(c_1915,plain,
    ( k10_relat_1(sK2,k2_relat_1(sK2)) != k1_relat_1(sK2)
    | k9_relat_1(sK2,k10_relat_1(sK2,sK0)) != k2_relat_1(sK2) ),
    inference(demodulation,[status(thm)],[c_1913,c_1413])).

cnf(c_7,plain,
    ( ~ v1_relat_1(X0)
    | k10_relat_1(X0,k2_relat_1(X0)) = k1_relat_1(X0) ),
    inference(cnf_transformation,[],[f48])).

cnf(c_662,plain,
    ( k10_relat_1(X0,k2_relat_1(X0)) = k1_relat_1(X0)
    | v1_relat_1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_7])).

cnf(c_1507,plain,
    ( k10_relat_1(sK2,k2_relat_1(sK2)) = k1_relat_1(sK2) ),
    inference(superposition,[status(thm)],[c_956,c_662])).

cnf(c_1916,plain,
    ( k9_relat_1(sK2,k10_relat_1(sK2,sK0)) != k2_relat_1(sK2)
    | k1_relat_1(sK2) != k1_relat_1(sK2) ),
    inference(light_normalisation,[status(thm)],[c_1915,c_1507])).

cnf(c_1917,plain,
    ( k9_relat_1(sK2,k10_relat_1(sK2,sK0)) != k2_relat_1(sK2) ),
    inference(equality_resolution_simp,[status(thm)],[c_1916])).

cnf(c_3052,plain,
    ( k9_relat_1(sK2,k1_relat_1(sK2)) != k2_relat_1(sK2) ),
    inference(demodulation,[status(thm)],[c_3038,c_1917])).

cnf(c_1,plain,
    ( r1_tarski(X0,X0) ),
    inference(cnf_transformation,[],[f64])).

cnf(c_665,plain,
    ( r1_tarski(X0,X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1])).

cnf(c_13,plain,
    ( ~ r1_tarski(k1_relat_1(X0),X1)
    | ~ v1_relat_1(X0)
    | k7_relat_1(X0,X1) = X0 ),
    inference(cnf_transformation,[],[f54])).

cnf(c_659,plain,
    ( k7_relat_1(X0,X1) = X0
    | r1_tarski(k1_relat_1(X0),X1) != iProver_top
    | v1_relat_1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_13])).

cnf(c_1719,plain,
    ( k7_relat_1(X0,k1_relat_1(X0)) = X0
    | v1_relat_1(X0) != iProver_top ),
    inference(superposition,[status(thm)],[c_665,c_659])).

cnf(c_2273,plain,
    ( k7_relat_1(sK2,k1_relat_1(sK2)) = sK2 ),
    inference(superposition,[status(thm)],[c_956,c_1719])).

cnf(c_2401,plain,
    ( k9_relat_1(sK2,k1_relat_1(sK2)) = k2_relat_1(sK2) ),
    inference(superposition,[status(thm)],[c_2273,c_1622])).

cnf(c_3053,plain,
    ( k2_relat_1(sK2) != k2_relat_1(sK2) ),
    inference(light_normalisation,[status(thm)],[c_3052,c_2401])).

cnf(c_3054,plain,
    ( $false ),
    inference(equality_resolution_simp,[status(thm)],[c_3053])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.12  % Command    : iproveropt_run.sh %d %s
% 0.12/0.33  % Computer   : n013.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.33  % CPULimit   : 60
% 0.12/0.33  % WCLimit    : 600
% 0.12/0.33  % DateTime   : Tue Dec  1 17:31:24 EST 2020
% 0.12/0.33  % CPUTime    : 
% 0.12/0.33  % Running in FOF mode
% 2.49/0.97  % SZS status Started for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.49/0.97  
% 2.49/0.97  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 2.49/0.97  
% 2.49/0.97  ------  iProver source info
% 2.49/0.97  
% 2.49/0.97  git: date: 2020-06-30 10:37:57 +0100
% 2.49/0.97  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 2.49/0.97  git: non_committed_changes: false
% 2.49/0.97  git: last_make_outside_of_git: false
% 2.49/0.97  
% 2.49/0.97  ------ 
% 2.49/0.97  
% 2.49/0.97  ------ Input Options
% 2.49/0.97  
% 2.49/0.97  --out_options                           all
% 2.49/0.97  --tptp_safe_out                         true
% 2.49/0.97  --problem_path                          ""
% 2.49/0.97  --include_path                          ""
% 2.49/0.97  --clausifier                            res/vclausify_rel
% 2.49/0.97  --clausifier_options                    --mode clausify
% 2.49/0.97  --stdin                                 false
% 2.49/0.97  --stats_out                             all
% 2.49/0.97  
% 2.49/0.97  ------ General Options
% 2.49/0.97  
% 2.49/0.97  --fof                                   false
% 2.49/0.97  --time_out_real                         305.
% 2.49/0.97  --time_out_virtual                      -1.
% 2.49/0.97  --symbol_type_check                     false
% 2.49/0.97  --clausify_out                          false
% 2.49/0.97  --sig_cnt_out                           false
% 2.49/0.98  --trig_cnt_out                          false
% 2.49/0.98  --trig_cnt_out_tolerance                1.
% 2.49/0.98  --trig_cnt_out_sk_spl                   false
% 2.49/0.98  --abstr_cl_out                          false
% 2.49/0.98  
% 2.49/0.98  ------ Global Options
% 2.49/0.98  
% 2.49/0.98  --schedule                              default
% 2.49/0.98  --add_important_lit                     false
% 2.49/0.98  --prop_solver_per_cl                    1000
% 2.49/0.98  --min_unsat_core                        false
% 2.49/0.98  --soft_assumptions                      false
% 2.49/0.98  --soft_lemma_size                       3
% 2.49/0.98  --prop_impl_unit_size                   0
% 2.49/0.98  --prop_impl_unit                        []
% 2.49/0.98  --share_sel_clauses                     true
% 2.49/0.98  --reset_solvers                         false
% 2.49/0.98  --bc_imp_inh                            [conj_cone]
% 2.49/0.98  --conj_cone_tolerance                   3.
% 2.49/0.98  --extra_neg_conj                        none
% 2.49/0.98  --large_theory_mode                     true
% 2.49/0.98  --prolific_symb_bound                   200
% 2.49/0.98  --lt_threshold                          2000
% 2.49/0.98  --clause_weak_htbl                      true
% 2.49/0.98  --gc_record_bc_elim                     false
% 2.49/0.98  
% 2.49/0.98  ------ Preprocessing Options
% 2.49/0.98  
% 2.49/0.98  --preprocessing_flag                    true
% 2.49/0.98  --time_out_prep_mult                    0.1
% 2.49/0.98  --splitting_mode                        input
% 2.49/0.98  --splitting_grd                         true
% 2.49/0.98  --splitting_cvd                         false
% 2.49/0.98  --splitting_cvd_svl                     false
% 2.49/0.98  --splitting_nvd                         32
% 2.49/0.98  --sub_typing                            true
% 2.49/0.98  --prep_gs_sim                           true
% 2.49/0.98  --prep_unflatten                        true
% 2.49/0.98  --prep_res_sim                          true
% 2.49/0.98  --prep_upred                            true
% 2.49/0.98  --prep_sem_filter                       exhaustive
% 2.49/0.98  --prep_sem_filter_out                   false
% 2.49/0.98  --pred_elim                             true
% 2.49/0.98  --res_sim_input                         true
% 2.49/0.98  --eq_ax_congr_red                       true
% 2.49/0.98  --pure_diseq_elim                       true
% 2.49/0.98  --brand_transform                       false
% 2.49/0.98  --non_eq_to_eq                          false
% 2.49/0.98  --prep_def_merge                        true
% 2.49/0.98  --prep_def_merge_prop_impl              false
% 2.49/0.98  --prep_def_merge_mbd                    true
% 2.49/0.98  --prep_def_merge_tr_red                 false
% 2.49/0.98  --prep_def_merge_tr_cl                  false
% 2.49/0.98  --smt_preprocessing                     true
% 2.49/0.98  --smt_ac_axioms                         fast
% 2.49/0.98  --preprocessed_out                      false
% 2.49/0.98  --preprocessed_stats                    false
% 2.49/0.98  
% 2.49/0.98  ------ Abstraction refinement Options
% 2.49/0.98  
% 2.49/0.98  --abstr_ref                             []
% 2.49/0.98  --abstr_ref_prep                        false
% 2.49/0.98  --abstr_ref_until_sat                   false
% 2.49/0.98  --abstr_ref_sig_restrict                funpre
% 2.49/0.98  --abstr_ref_af_restrict_to_split_sk     false
% 2.49/0.98  --abstr_ref_under                       []
% 2.49/0.98  
% 2.49/0.98  ------ SAT Options
% 2.49/0.98  
% 2.49/0.98  --sat_mode                              false
% 2.49/0.98  --sat_fm_restart_options                ""
% 2.49/0.98  --sat_gr_def                            false
% 2.49/0.98  --sat_epr_types                         true
% 2.49/0.98  --sat_non_cyclic_types                  false
% 2.49/0.98  --sat_finite_models                     false
% 2.49/0.98  --sat_fm_lemmas                         false
% 2.49/0.98  --sat_fm_prep                           false
% 2.49/0.98  --sat_fm_uc_incr                        true
% 2.49/0.98  --sat_out_model                         small
% 2.49/0.98  --sat_out_clauses                       false
% 2.49/0.98  
% 2.49/0.98  ------ QBF Options
% 2.49/0.98  
% 2.49/0.98  --qbf_mode                              false
% 2.49/0.98  --qbf_elim_univ                         false
% 2.49/0.98  --qbf_dom_inst                          none
% 2.49/0.98  --qbf_dom_pre_inst                      false
% 2.49/0.98  --qbf_sk_in                             false
% 2.49/0.98  --qbf_pred_elim                         true
% 2.49/0.98  --qbf_split                             512
% 2.49/0.98  
% 2.49/0.98  ------ BMC1 Options
% 2.49/0.98  
% 2.49/0.98  --bmc1_incremental                      false
% 2.49/0.98  --bmc1_axioms                           reachable_all
% 2.49/0.98  --bmc1_min_bound                        0
% 2.49/0.98  --bmc1_max_bound                        -1
% 2.49/0.98  --bmc1_max_bound_default                -1
% 2.49/0.98  --bmc1_symbol_reachability              true
% 2.49/0.98  --bmc1_property_lemmas                  false
% 2.49/0.98  --bmc1_k_induction                      false
% 2.49/0.98  --bmc1_non_equiv_states                 false
% 2.49/0.98  --bmc1_deadlock                         false
% 2.49/0.98  --bmc1_ucm                              false
% 2.49/0.98  --bmc1_add_unsat_core                   none
% 2.49/0.98  --bmc1_unsat_core_children              false
% 2.49/0.98  --bmc1_unsat_core_extrapolate_axioms    false
% 2.49/0.98  --bmc1_out_stat                         full
% 2.49/0.98  --bmc1_ground_init                      false
% 2.49/0.98  --bmc1_pre_inst_next_state              false
% 2.49/0.98  --bmc1_pre_inst_state                   false
% 2.49/0.98  --bmc1_pre_inst_reach_state             false
% 2.49/0.98  --bmc1_out_unsat_core                   false
% 2.49/0.98  --bmc1_aig_witness_out                  false
% 2.49/0.98  --bmc1_verbose                          false
% 2.49/0.98  --bmc1_dump_clauses_tptp                false
% 2.49/0.98  --bmc1_dump_unsat_core_tptp             false
% 2.49/0.98  --bmc1_dump_file                        -
% 2.49/0.98  --bmc1_ucm_expand_uc_limit              128
% 2.49/0.98  --bmc1_ucm_n_expand_iterations          6
% 2.49/0.98  --bmc1_ucm_extend_mode                  1
% 2.49/0.98  --bmc1_ucm_init_mode                    2
% 2.49/0.98  --bmc1_ucm_cone_mode                    none
% 2.49/0.98  --bmc1_ucm_reduced_relation_type        0
% 2.49/0.98  --bmc1_ucm_relax_model                  4
% 2.49/0.98  --bmc1_ucm_full_tr_after_sat            true
% 2.49/0.98  --bmc1_ucm_expand_neg_assumptions       false
% 2.49/0.98  --bmc1_ucm_layered_model                none
% 2.49/0.98  --bmc1_ucm_max_lemma_size               10
% 2.49/0.98  
% 2.49/0.98  ------ AIG Options
% 2.49/0.98  
% 2.49/0.98  --aig_mode                              false
% 2.49/0.98  
% 2.49/0.98  ------ Instantiation Options
% 2.49/0.98  
% 2.49/0.98  --instantiation_flag                    true
% 2.49/0.98  --inst_sos_flag                         false
% 2.49/0.98  --inst_sos_phase                        true
% 2.49/0.98  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 2.49/0.98  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 2.49/0.98  --inst_lit_sel_side                     num_symb
% 2.49/0.98  --inst_solver_per_active                1400
% 2.49/0.98  --inst_solver_calls_frac                1.
% 2.49/0.98  --inst_passive_queue_type               priority_queues
% 2.49/0.98  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 2.49/0.98  --inst_passive_queues_freq              [25;2]
% 2.49/0.98  --inst_dismatching                      true
% 2.49/0.98  --inst_eager_unprocessed_to_passive     true
% 2.49/0.98  --inst_prop_sim_given                   true
% 2.49/0.98  --inst_prop_sim_new                     false
% 2.49/0.98  --inst_subs_new                         false
% 2.49/0.98  --inst_eq_res_simp                      false
% 2.49/0.98  --inst_subs_given                       false
% 2.49/0.98  --inst_orphan_elimination               true
% 2.49/0.98  --inst_learning_loop_flag               true
% 2.49/0.98  --inst_learning_start                   3000
% 2.49/0.98  --inst_learning_factor                  2
% 2.49/0.98  --inst_start_prop_sim_after_learn       3
% 2.49/0.98  --inst_sel_renew                        solver
% 2.49/0.98  --inst_lit_activity_flag                true
% 2.49/0.98  --inst_restr_to_given                   false
% 2.49/0.98  --inst_activity_threshold               500
% 2.49/0.98  --inst_out_proof                        true
% 2.49/0.98  
% 2.49/0.98  ------ Resolution Options
% 2.49/0.98  
% 2.49/0.98  --resolution_flag                       true
% 2.49/0.98  --res_lit_sel                           adaptive
% 2.49/0.98  --res_lit_sel_side                      none
% 2.49/0.98  --res_ordering                          kbo
% 2.49/0.98  --res_to_prop_solver                    active
% 2.49/0.98  --res_prop_simpl_new                    false
% 2.49/0.98  --res_prop_simpl_given                  true
% 2.49/0.98  --res_passive_queue_type                priority_queues
% 2.49/0.98  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 2.49/0.98  --res_passive_queues_freq               [15;5]
% 2.49/0.98  --res_forward_subs                      full
% 2.49/0.98  --res_backward_subs                     full
% 2.49/0.98  --res_forward_subs_resolution           true
% 2.49/0.98  --res_backward_subs_resolution          true
% 2.49/0.98  --res_orphan_elimination                true
% 2.49/0.98  --res_time_limit                        2.
% 2.49/0.98  --res_out_proof                         true
% 2.49/0.98  
% 2.49/0.98  ------ Superposition Options
% 2.49/0.98  
% 2.49/0.98  --superposition_flag                    true
% 2.49/0.98  --sup_passive_queue_type                priority_queues
% 2.49/0.98  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 2.49/0.98  --sup_passive_queues_freq               [8;1;4]
% 2.49/0.98  --demod_completeness_check              fast
% 2.49/0.98  --demod_use_ground                      true
% 2.49/0.98  --sup_to_prop_solver                    passive
% 2.49/0.98  --sup_prop_simpl_new                    true
% 2.49/0.98  --sup_prop_simpl_given                  true
% 2.49/0.98  --sup_fun_splitting                     false
% 2.49/0.98  --sup_smt_interval                      50000
% 2.49/0.98  
% 2.49/0.98  ------ Superposition Simplification Setup
% 2.49/0.98  
% 2.49/0.98  --sup_indices_passive                   []
% 2.49/0.98  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.49/0.98  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.49/0.98  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.49/0.98  --sup_full_triv                         [TrivRules;PropSubs]
% 2.49/0.98  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.49/0.98  --sup_full_bw                           [BwDemod]
% 2.49/0.98  --sup_immed_triv                        [TrivRules]
% 2.49/0.98  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 2.49/0.98  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.49/0.98  --sup_immed_bw_main                     []
% 2.49/0.98  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.49/0.98  --sup_input_triv                        [Unflattening;TrivRules]
% 2.49/0.98  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.49/0.98  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.49/0.98  
% 2.49/0.98  ------ Combination Options
% 2.49/0.98  
% 2.49/0.98  --comb_res_mult                         3
% 2.49/0.98  --comb_sup_mult                         2
% 2.49/0.98  --comb_inst_mult                        10
% 2.49/0.98  
% 2.49/0.98  ------ Debug Options
% 2.49/0.98  
% 2.49/0.98  --dbg_backtrace                         false
% 2.49/0.98  --dbg_dump_prop_clauses                 false
% 2.49/0.98  --dbg_dump_prop_clauses_file            -
% 2.49/0.98  --dbg_out_stat                          false
% 2.49/0.98  ------ Parsing...
% 2.49/0.98  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 2.49/0.98  
% 2.49/0.98  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe:1:0s pe:2:0s pe_e  sf_s  rm: 2 0s  sf_e  pe_s  pe_e 
% 2.49/0.98  
% 2.49/0.98  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 2.49/0.98  
% 2.49/0.98  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 2.49/0.98  ------ Proving...
% 2.49/0.98  ------ Problem Properties 
% 2.49/0.98  
% 2.49/0.98  
% 2.49/0.98  clauses                                 18
% 2.49/0.98  conjectures                             1
% 2.49/0.98  EPR                                     2
% 2.49/0.98  Horn                                    18
% 2.49/0.98  unary                                   4
% 2.49/0.98  binary                                  10
% 2.49/0.98  lits                                    36
% 2.49/0.98  lits eq                                 22
% 2.49/0.98  fd_pure                                 0
% 2.49/0.98  fd_pseudo                               0
% 2.49/0.98  fd_cond                                 0
% 2.49/0.98  fd_pseudo_cond                          1
% 2.49/0.98  AC symbols                              0
% 2.49/0.98  
% 2.49/0.98  ------ Schedule dynamic 5 is on 
% 2.49/0.98  
% 2.49/0.98  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" Time Limit: 10.
% 2.49/0.98  
% 2.49/0.98  
% 2.49/0.98  ------ 
% 2.49/0.98  Current options:
% 2.49/0.98  ------ 
% 2.49/0.98  
% 2.49/0.98  ------ Input Options
% 2.49/0.98  
% 2.49/0.98  --out_options                           all
% 2.49/0.98  --tptp_safe_out                         true
% 2.49/0.98  --problem_path                          ""
% 2.49/0.98  --include_path                          ""
% 2.49/0.98  --clausifier                            res/vclausify_rel
% 2.49/0.98  --clausifier_options                    --mode clausify
% 2.49/0.98  --stdin                                 false
% 2.49/0.98  --stats_out                             all
% 2.49/0.98  
% 2.49/0.98  ------ General Options
% 2.49/0.98  
% 2.49/0.98  --fof                                   false
% 2.49/0.98  --time_out_real                         305.
% 2.49/0.98  --time_out_virtual                      -1.
% 2.49/0.98  --symbol_type_check                     false
% 2.49/0.98  --clausify_out                          false
% 2.49/0.98  --sig_cnt_out                           false
% 2.49/0.98  --trig_cnt_out                          false
% 2.49/0.98  --trig_cnt_out_tolerance                1.
% 2.49/0.98  --trig_cnt_out_sk_spl                   false
% 2.49/0.98  --abstr_cl_out                          false
% 2.49/0.98  
% 2.49/0.98  ------ Global Options
% 2.49/0.98  
% 2.49/0.98  --schedule                              default
% 2.49/0.98  --add_important_lit                     false
% 2.49/0.98  --prop_solver_per_cl                    1000
% 2.49/0.98  --min_unsat_core                        false
% 2.49/0.98  --soft_assumptions                      false
% 2.49/0.98  --soft_lemma_size                       3
% 2.49/0.98  --prop_impl_unit_size                   0
% 2.49/0.98  --prop_impl_unit                        []
% 2.49/0.98  --share_sel_clauses                     true
% 2.49/0.98  --reset_solvers                         false
% 2.49/0.98  --bc_imp_inh                            [conj_cone]
% 2.49/0.98  --conj_cone_tolerance                   3.
% 2.49/0.98  --extra_neg_conj                        none
% 2.49/0.98  --large_theory_mode                     true
% 2.49/0.98  --prolific_symb_bound                   200
% 2.49/0.98  --lt_threshold                          2000
% 2.49/0.98  --clause_weak_htbl                      true
% 2.49/0.98  --gc_record_bc_elim                     false
% 2.49/0.98  
% 2.49/0.98  ------ Preprocessing Options
% 2.49/0.98  
% 2.49/0.98  --preprocessing_flag                    true
% 2.49/0.98  --time_out_prep_mult                    0.1
% 2.49/0.98  --splitting_mode                        input
% 2.49/0.98  --splitting_grd                         true
% 2.49/0.98  --splitting_cvd                         false
% 2.49/0.98  --splitting_cvd_svl                     false
% 2.49/0.98  --splitting_nvd                         32
% 2.49/0.98  --sub_typing                            true
% 2.49/0.98  --prep_gs_sim                           true
% 2.49/0.98  --prep_unflatten                        true
% 2.49/0.98  --prep_res_sim                          true
% 2.49/0.98  --prep_upred                            true
% 2.49/0.98  --prep_sem_filter                       exhaustive
% 2.49/0.98  --prep_sem_filter_out                   false
% 2.49/0.98  --pred_elim                             true
% 2.49/0.98  --res_sim_input                         true
% 2.49/0.98  --eq_ax_congr_red                       true
% 2.49/0.98  --pure_diseq_elim                       true
% 2.49/0.98  --brand_transform                       false
% 2.49/0.98  --non_eq_to_eq                          false
% 2.49/0.98  --prep_def_merge                        true
% 2.49/0.98  --prep_def_merge_prop_impl              false
% 2.49/0.98  --prep_def_merge_mbd                    true
% 2.49/0.98  --prep_def_merge_tr_red                 false
% 2.49/0.98  --prep_def_merge_tr_cl                  false
% 2.49/0.98  --smt_preprocessing                     true
% 2.49/0.98  --smt_ac_axioms                         fast
% 2.49/0.98  --preprocessed_out                      false
% 2.49/0.98  --preprocessed_stats                    false
% 2.49/0.98  
% 2.49/0.98  ------ Abstraction refinement Options
% 2.49/0.98  
% 2.49/0.98  --abstr_ref                             []
% 2.49/0.98  --abstr_ref_prep                        false
% 2.49/0.98  --abstr_ref_until_sat                   false
% 2.49/0.98  --abstr_ref_sig_restrict                funpre
% 2.49/0.98  --abstr_ref_af_restrict_to_split_sk     false
% 2.49/0.98  --abstr_ref_under                       []
% 2.49/0.98  
% 2.49/0.98  ------ SAT Options
% 2.49/0.98  
% 2.49/0.98  --sat_mode                              false
% 2.49/0.98  --sat_fm_restart_options                ""
% 2.49/0.98  --sat_gr_def                            false
% 2.49/0.98  --sat_epr_types                         true
% 2.49/0.98  --sat_non_cyclic_types                  false
% 2.49/0.98  --sat_finite_models                     false
% 2.49/0.98  --sat_fm_lemmas                         false
% 2.49/0.98  --sat_fm_prep                           false
% 2.49/0.98  --sat_fm_uc_incr                        true
% 2.49/0.98  --sat_out_model                         small
% 2.49/0.98  --sat_out_clauses                       false
% 2.49/0.98  
% 2.49/0.98  ------ QBF Options
% 2.49/0.98  
% 2.49/0.98  --qbf_mode                              false
% 2.49/0.98  --qbf_elim_univ                         false
% 2.49/0.98  --qbf_dom_inst                          none
% 2.49/0.98  --qbf_dom_pre_inst                      false
% 2.49/0.98  --qbf_sk_in                             false
% 2.49/0.98  --qbf_pred_elim                         true
% 2.49/0.98  --qbf_split                             512
% 2.49/0.98  
% 2.49/0.98  ------ BMC1 Options
% 2.49/0.98  
% 2.49/0.98  --bmc1_incremental                      false
% 2.49/0.98  --bmc1_axioms                           reachable_all
% 2.49/0.98  --bmc1_min_bound                        0
% 2.49/0.98  --bmc1_max_bound                        -1
% 2.49/0.98  --bmc1_max_bound_default                -1
% 2.49/0.98  --bmc1_symbol_reachability              true
% 2.49/0.98  --bmc1_property_lemmas                  false
% 2.49/0.98  --bmc1_k_induction                      false
% 2.49/0.98  --bmc1_non_equiv_states                 false
% 2.49/0.98  --bmc1_deadlock                         false
% 2.49/0.98  --bmc1_ucm                              false
% 2.49/0.98  --bmc1_add_unsat_core                   none
% 2.49/0.98  --bmc1_unsat_core_children              false
% 2.49/0.98  --bmc1_unsat_core_extrapolate_axioms    false
% 2.49/0.98  --bmc1_out_stat                         full
% 2.49/0.98  --bmc1_ground_init                      false
% 2.49/0.98  --bmc1_pre_inst_next_state              false
% 2.49/0.98  --bmc1_pre_inst_state                   false
% 2.49/0.98  --bmc1_pre_inst_reach_state             false
% 2.49/0.98  --bmc1_out_unsat_core                   false
% 2.49/0.98  --bmc1_aig_witness_out                  false
% 2.49/0.98  --bmc1_verbose                          false
% 2.49/0.98  --bmc1_dump_clauses_tptp                false
% 2.49/0.98  --bmc1_dump_unsat_core_tptp             false
% 2.49/0.98  --bmc1_dump_file                        -
% 2.49/0.98  --bmc1_ucm_expand_uc_limit              128
% 2.49/0.98  --bmc1_ucm_n_expand_iterations          6
% 2.49/0.98  --bmc1_ucm_extend_mode                  1
% 2.49/0.98  --bmc1_ucm_init_mode                    2
% 2.49/0.98  --bmc1_ucm_cone_mode                    none
% 2.49/0.98  --bmc1_ucm_reduced_relation_type        0
% 2.49/0.98  --bmc1_ucm_relax_model                  4
% 2.49/0.98  --bmc1_ucm_full_tr_after_sat            true
% 2.49/0.98  --bmc1_ucm_expand_neg_assumptions       false
% 2.49/0.98  --bmc1_ucm_layered_model                none
% 2.49/0.98  --bmc1_ucm_max_lemma_size               10
% 2.49/0.98  
% 2.49/0.98  ------ AIG Options
% 2.49/0.98  
% 2.49/0.98  --aig_mode                              false
% 2.49/0.98  
% 2.49/0.98  ------ Instantiation Options
% 2.49/0.98  
% 2.49/0.98  --instantiation_flag                    true
% 2.49/0.98  --inst_sos_flag                         false
% 2.49/0.98  --inst_sos_phase                        true
% 2.49/0.98  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 2.49/0.98  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 2.49/0.98  --inst_lit_sel_side                     none
% 2.49/0.98  --inst_solver_per_active                1400
% 2.49/0.98  --inst_solver_calls_frac                1.
% 2.49/0.98  --inst_passive_queue_type               priority_queues
% 2.49/0.98  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 2.49/0.98  --inst_passive_queues_freq              [25;2]
% 2.49/0.98  --inst_dismatching                      true
% 2.49/0.98  --inst_eager_unprocessed_to_passive     true
% 2.49/0.98  --inst_prop_sim_given                   true
% 2.49/0.98  --inst_prop_sim_new                     false
% 2.49/0.98  --inst_subs_new                         false
% 2.49/0.98  --inst_eq_res_simp                      false
% 2.49/0.98  --inst_subs_given                       false
% 2.49/0.98  --inst_orphan_elimination               true
% 2.49/0.98  --inst_learning_loop_flag               true
% 2.49/0.98  --inst_learning_start                   3000
% 2.49/0.98  --inst_learning_factor                  2
% 2.49/0.98  --inst_start_prop_sim_after_learn       3
% 2.49/0.98  --inst_sel_renew                        solver
% 2.49/0.98  --inst_lit_activity_flag                true
% 2.49/0.98  --inst_restr_to_given                   false
% 2.49/0.98  --inst_activity_threshold               500
% 2.49/0.98  --inst_out_proof                        true
% 2.49/0.98  
% 2.49/0.98  ------ Resolution Options
% 2.49/0.98  
% 2.49/0.98  --resolution_flag                       false
% 2.49/0.98  --res_lit_sel                           adaptive
% 2.49/0.98  --res_lit_sel_side                      none
% 2.49/0.98  --res_ordering                          kbo
% 2.49/0.98  --res_to_prop_solver                    active
% 2.49/0.98  --res_prop_simpl_new                    false
% 2.49/0.98  --res_prop_simpl_given                  true
% 2.49/0.98  --res_passive_queue_type                priority_queues
% 2.49/0.98  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 2.49/0.98  --res_passive_queues_freq               [15;5]
% 2.49/0.98  --res_forward_subs                      full
% 2.49/0.98  --res_backward_subs                     full
% 2.49/0.98  --res_forward_subs_resolution           true
% 2.49/0.98  --res_backward_subs_resolution          true
% 2.49/0.98  --res_orphan_elimination                true
% 2.49/0.98  --res_time_limit                        2.
% 2.49/0.98  --res_out_proof                         true
% 2.49/0.98  
% 2.49/0.98  ------ Superposition Options
% 2.49/0.98  
% 2.49/0.98  --superposition_flag                    true
% 2.49/0.98  --sup_passive_queue_type                priority_queues
% 2.49/0.98  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 2.49/0.98  --sup_passive_queues_freq               [8;1;4]
% 2.49/0.98  --demod_completeness_check              fast
% 2.49/0.98  --demod_use_ground                      true
% 2.49/0.98  --sup_to_prop_solver                    passive
% 2.49/0.98  --sup_prop_simpl_new                    true
% 2.49/0.98  --sup_prop_simpl_given                  true
% 2.49/0.98  --sup_fun_splitting                     false
% 2.49/0.98  --sup_smt_interval                      50000
% 2.49/0.98  
% 2.49/0.98  ------ Superposition Simplification Setup
% 2.49/0.98  
% 2.49/0.98  --sup_indices_passive                   []
% 2.49/0.98  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.49/0.98  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.49/0.98  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.49/0.98  --sup_full_triv                         [TrivRules;PropSubs]
% 2.49/0.98  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.49/0.98  --sup_full_bw                           [BwDemod]
% 2.49/0.98  --sup_immed_triv                        [TrivRules]
% 2.49/0.98  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 2.49/0.98  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.49/0.98  --sup_immed_bw_main                     []
% 2.49/0.98  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.49/0.98  --sup_input_triv                        [Unflattening;TrivRules]
% 2.49/0.98  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.49/0.98  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.49/0.98  
% 2.49/0.98  ------ Combination Options
% 2.49/0.98  
% 2.49/0.98  --comb_res_mult                         3
% 2.49/0.98  --comb_sup_mult                         2
% 2.49/0.98  --comb_inst_mult                        10
% 2.49/0.98  
% 2.49/0.98  ------ Debug Options
% 2.49/0.98  
% 2.49/0.98  --dbg_backtrace                         false
% 2.49/0.98  --dbg_dump_prop_clauses                 false
% 2.49/0.98  --dbg_dump_prop_clauses_file            -
% 2.49/0.98  --dbg_out_stat                          false
% 2.49/0.98  
% 2.49/0.98  
% 2.49/0.98  
% 2.49/0.98  
% 2.49/0.98  ------ Proving...
% 2.49/0.98  
% 2.49/0.98  
% 2.49/0.98  % SZS status Theorem for theBenchmark.p
% 2.49/0.98  
% 2.49/0.98   Resolution empty clause
% 2.49/0.98  
% 2.49/0.98  % SZS output start CNFRefutation for theBenchmark.p
% 2.49/0.98  
% 2.49/0.98  fof(f2,axiom,(
% 2.49/0.98    ! [X0,X1] : (v1_relat_1(X1) => (v5_relat_1(X1,X0) <=> r1_tarski(k2_relat_1(X1),X0)))),
% 2.49/0.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.49/0.98  
% 2.49/0.98  fof(f19,plain,(
% 2.49/0.98    ! [X0,X1] : ((v5_relat_1(X1,X0) <=> r1_tarski(k2_relat_1(X1),X0)) | ~v1_relat_1(X1))),
% 2.49/0.98    inference(ennf_transformation,[],[f2])).
% 2.49/0.98  
% 2.49/0.98  fof(f38,plain,(
% 2.49/0.98    ! [X0,X1] : (((v5_relat_1(X1,X0) | ~r1_tarski(k2_relat_1(X1),X0)) & (r1_tarski(k2_relat_1(X1),X0) | ~v5_relat_1(X1,X0))) | ~v1_relat_1(X1))),
% 2.49/0.98    inference(nnf_transformation,[],[f19])).
% 2.49/0.98  
% 2.49/0.98  fof(f44,plain,(
% 2.49/0.98    ( ! [X0,X1] : (r1_tarski(k2_relat_1(X1),X0) | ~v5_relat_1(X1,X0) | ~v1_relat_1(X1)) )),
% 2.49/0.98    inference(cnf_transformation,[],[f38])).
% 2.49/0.98  
% 2.49/0.98  fof(f12,axiom,(
% 2.49/0.98    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => (v5_relat_1(X2,X1) & v4_relat_1(X2,X0)))),
% 2.49/0.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.49/0.98  
% 2.49/0.98  fof(f30,plain,(
% 2.49/0.98    ! [X0,X1,X2] : ((v5_relat_1(X2,X1) & v4_relat_1(X2,X0)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 2.49/0.98    inference(ennf_transformation,[],[f12])).
% 2.49/0.98  
% 2.49/0.98  fof(f57,plain,(
% 2.49/0.98    ( ! [X2,X0,X1] : (v5_relat_1(X2,X1) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 2.49/0.98    inference(cnf_transformation,[],[f30])).
% 2.49/0.98  
% 2.49/0.98  fof(f11,axiom,(
% 2.49/0.98    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => v1_relat_1(X2))),
% 2.49/0.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.49/0.98  
% 2.49/0.98  fof(f29,plain,(
% 2.49/0.98    ! [X0,X1,X2] : (v1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 2.49/0.98    inference(ennf_transformation,[],[f11])).
% 2.49/0.98  
% 2.49/0.98  fof(f55,plain,(
% 2.49/0.98    ( ! [X2,X0,X1] : (v1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 2.49/0.98    inference(cnf_transformation,[],[f29])).
% 2.49/0.98  
% 2.49/0.98  fof(f17,conjecture,(
% 2.49/0.98    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) => (k1_relset_1(X1,X0,X2) = k8_relset_1(X1,X0,X2,k7_relset_1(X1,X0,X2,X1)) & k2_relset_1(X1,X0,X2) = k7_relset_1(X1,X0,X2,k8_relset_1(X1,X0,X2,X0))))),
% 2.49/0.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.49/0.98  
% 2.49/0.98  fof(f18,negated_conjecture,(
% 2.49/0.98    ~! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) => (k1_relset_1(X1,X0,X2) = k8_relset_1(X1,X0,X2,k7_relset_1(X1,X0,X2,X1)) & k2_relset_1(X1,X0,X2) = k7_relset_1(X1,X0,X2,k8_relset_1(X1,X0,X2,X0))))),
% 2.49/0.98    inference(negated_conjecture,[],[f17])).
% 2.49/0.98  
% 2.49/0.98  fof(f35,plain,(
% 2.49/0.98    ? [X0,X1,X2] : ((k1_relset_1(X1,X0,X2) != k8_relset_1(X1,X0,X2,k7_relset_1(X1,X0,X2,X1)) | k2_relset_1(X1,X0,X2) != k7_relset_1(X1,X0,X2,k8_relset_1(X1,X0,X2,X0))) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X0))))),
% 2.49/0.98    inference(ennf_transformation,[],[f18])).
% 2.49/0.98  
% 2.49/0.98  fof(f39,plain,(
% 2.49/0.98    ? [X0,X1,X2] : ((k1_relset_1(X1,X0,X2) != k8_relset_1(X1,X0,X2,k7_relset_1(X1,X0,X2,X1)) | k2_relset_1(X1,X0,X2) != k7_relset_1(X1,X0,X2,k8_relset_1(X1,X0,X2,X0))) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X0)))) => ((k1_relset_1(sK1,sK0,sK2) != k8_relset_1(sK1,sK0,sK2,k7_relset_1(sK1,sK0,sK2,sK1)) | k2_relset_1(sK1,sK0,sK2) != k7_relset_1(sK1,sK0,sK2,k8_relset_1(sK1,sK0,sK2,sK0))) & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))))),
% 2.49/0.98    introduced(choice_axiom,[])).
% 2.49/0.98  
% 2.49/0.98  fof(f40,plain,(
% 2.49/0.98    (k1_relset_1(sK1,sK0,sK2) != k8_relset_1(sK1,sK0,sK2,k7_relset_1(sK1,sK0,sK2,sK1)) | k2_relset_1(sK1,sK0,sK2) != k7_relset_1(sK1,sK0,sK2,k8_relset_1(sK1,sK0,sK2,sK0))) & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))),
% 2.49/0.98    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f35,f39])).
% 2.49/0.98  
% 2.49/0.98  fof(f62,plain,(
% 2.49/0.98    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))),
% 2.49/0.98    inference(cnf_transformation,[],[f40])).
% 2.49/0.98  
% 2.49/0.98  fof(f9,axiom,(
% 2.49/0.98    ! [X0,X1] : (v1_relat_1(X1) => (r1_tarski(k2_relat_1(X1),X0) => k5_relat_1(X1,k6_relat_1(X0)) = X1))),
% 2.49/0.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.49/0.98  
% 2.49/0.98  fof(f25,plain,(
% 2.49/0.98    ! [X0,X1] : ((k5_relat_1(X1,k6_relat_1(X0)) = X1 | ~r1_tarski(k2_relat_1(X1),X0)) | ~v1_relat_1(X1))),
% 2.49/0.98    inference(ennf_transformation,[],[f9])).
% 2.49/0.98  
% 2.49/0.98  fof(f26,plain,(
% 2.49/0.98    ! [X0,X1] : (k5_relat_1(X1,k6_relat_1(X0)) = X1 | ~r1_tarski(k2_relat_1(X1),X0) | ~v1_relat_1(X1))),
% 2.49/0.98    inference(flattening,[],[f25])).
% 2.49/0.98  
% 2.49/0.98  fof(f53,plain,(
% 2.49/0.98    ( ! [X0,X1] : (k5_relat_1(X1,k6_relat_1(X0)) = X1 | ~r1_tarski(k2_relat_1(X1),X0) | ~v1_relat_1(X1)) )),
% 2.49/0.98    inference(cnf_transformation,[],[f26])).
% 2.49/0.98  
% 2.49/0.98  fof(f3,axiom,(
% 2.49/0.98    ! [X0] : v1_relat_1(k6_relat_1(X0))),
% 2.49/0.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.49/0.98  
% 2.49/0.98  fof(f46,plain,(
% 2.49/0.98    ( ! [X0] : (v1_relat_1(k6_relat_1(X0))) )),
% 2.49/0.98    inference(cnf_transformation,[],[f3])).
% 2.49/0.98  
% 2.49/0.98  fof(f6,axiom,(
% 2.49/0.98    ! [X0] : (v1_relat_1(X0) => ! [X1] : (v1_relat_1(X1) => k10_relat_1(X0,k1_relat_1(X1)) = k1_relat_1(k5_relat_1(X0,X1))))),
% 2.49/0.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.49/0.98  
% 2.49/0.98  fof(f22,plain,(
% 2.49/0.98    ! [X0] : (! [X1] : (k10_relat_1(X0,k1_relat_1(X1)) = k1_relat_1(k5_relat_1(X0,X1)) | ~v1_relat_1(X1)) | ~v1_relat_1(X0))),
% 2.49/0.98    inference(ennf_transformation,[],[f6])).
% 2.49/0.98  
% 2.49/0.98  fof(f49,plain,(
% 2.49/0.98    ( ! [X0,X1] : (k10_relat_1(X0,k1_relat_1(X1)) = k1_relat_1(k5_relat_1(X0,X1)) | ~v1_relat_1(X1) | ~v1_relat_1(X0)) )),
% 2.49/0.98    inference(cnf_transformation,[],[f22])).
% 2.49/0.98  
% 2.49/0.98  fof(f8,axiom,(
% 2.49/0.98    ! [X0] : (k2_relat_1(k6_relat_1(X0)) = X0 & k1_relat_1(k6_relat_1(X0)) = X0)),
% 2.49/0.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.49/0.98  
% 2.49/0.98  fof(f51,plain,(
% 2.49/0.98    ( ! [X0] : (k1_relat_1(k6_relat_1(X0)) = X0) )),
% 2.49/0.98    inference(cnf_transformation,[],[f8])).
% 2.49/0.98  
% 2.49/0.98  fof(f56,plain,(
% 2.49/0.98    ( ! [X2,X0,X1] : (v4_relat_1(X2,X0) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 2.49/0.98    inference(cnf_transformation,[],[f30])).
% 2.49/0.98  
% 2.49/0.98  fof(f7,axiom,(
% 2.49/0.98    ! [X0,X1] : ((v4_relat_1(X1,X0) & v1_relat_1(X1)) => k7_relat_1(X1,X0) = X1)),
% 2.49/0.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.49/0.98  
% 2.49/0.98  fof(f23,plain,(
% 2.49/0.98    ! [X0,X1] : (k7_relat_1(X1,X0) = X1 | (~v4_relat_1(X1,X0) | ~v1_relat_1(X1)))),
% 2.49/0.98    inference(ennf_transformation,[],[f7])).
% 2.49/0.98  
% 2.49/0.98  fof(f24,plain,(
% 2.49/0.98    ! [X0,X1] : (k7_relat_1(X1,X0) = X1 | ~v4_relat_1(X1,X0) | ~v1_relat_1(X1))),
% 2.49/0.98    inference(flattening,[],[f23])).
% 2.49/0.98  
% 2.49/0.98  fof(f50,plain,(
% 2.49/0.98    ( ! [X0,X1] : (k7_relat_1(X1,X0) = X1 | ~v4_relat_1(X1,X0) | ~v1_relat_1(X1)) )),
% 2.49/0.98    inference(cnf_transformation,[],[f24])).
% 2.49/0.98  
% 2.49/0.98  fof(f4,axiom,(
% 2.49/0.98    ! [X0,X1] : (v1_relat_1(X1) => k2_relat_1(k7_relat_1(X1,X0)) = k9_relat_1(X1,X0))),
% 2.49/0.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.49/0.98  
% 2.49/0.98  fof(f20,plain,(
% 2.49/0.98    ! [X0,X1] : (k2_relat_1(k7_relat_1(X1,X0)) = k9_relat_1(X1,X0) | ~v1_relat_1(X1))),
% 2.49/0.98    inference(ennf_transformation,[],[f4])).
% 2.49/0.98  
% 2.49/0.98  fof(f47,plain,(
% 2.49/0.98    ( ! [X0,X1] : (k2_relat_1(k7_relat_1(X1,X0)) = k9_relat_1(X1,X0) | ~v1_relat_1(X1)) )),
% 2.49/0.98    inference(cnf_transformation,[],[f20])).
% 2.49/0.98  
% 2.49/0.98  fof(f13,axiom,(
% 2.49/0.98    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k1_relat_1(X2) = k1_relset_1(X0,X1,X2))),
% 2.49/0.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.49/0.98  
% 2.49/0.98  fof(f31,plain,(
% 2.49/0.98    ! [X0,X1,X2] : (k1_relat_1(X2) = k1_relset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 2.49/0.98    inference(ennf_transformation,[],[f13])).
% 2.49/0.98  
% 2.49/0.98  fof(f58,plain,(
% 2.49/0.98    ( ! [X2,X0,X1] : (k1_relat_1(X2) = k1_relset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 2.49/0.98    inference(cnf_transformation,[],[f31])).
% 2.49/0.98  
% 2.49/0.98  fof(f14,axiom,(
% 2.49/0.98    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k2_relat_1(X2) = k2_relset_1(X0,X1,X2))),
% 2.49/0.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.49/0.98  
% 2.49/0.98  fof(f32,plain,(
% 2.49/0.98    ! [X0,X1,X2] : (k2_relat_1(X2) = k2_relset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 2.49/0.98    inference(ennf_transformation,[],[f14])).
% 2.49/0.98  
% 2.49/0.98  fof(f59,plain,(
% 2.49/0.98    ( ! [X2,X0,X1] : (k2_relat_1(X2) = k2_relset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 2.49/0.98    inference(cnf_transformation,[],[f32])).
% 2.49/0.98  
% 2.49/0.98  fof(f63,plain,(
% 2.49/0.98    k1_relset_1(sK1,sK0,sK2) != k8_relset_1(sK1,sK0,sK2,k7_relset_1(sK1,sK0,sK2,sK1)) | k2_relset_1(sK1,sK0,sK2) != k7_relset_1(sK1,sK0,sK2,k8_relset_1(sK1,sK0,sK2,sK0))),
% 2.49/0.98    inference(cnf_transformation,[],[f40])).
% 2.49/0.98  
% 2.49/0.98  fof(f16,axiom,(
% 2.49/0.98    ! [X0,X1,X2,X3] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k10_relat_1(X2,X3) = k8_relset_1(X0,X1,X2,X3))),
% 2.49/0.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.49/0.98  
% 2.49/0.98  fof(f34,plain,(
% 2.49/0.98    ! [X0,X1,X2,X3] : (k10_relat_1(X2,X3) = k8_relset_1(X0,X1,X2,X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 2.49/0.98    inference(ennf_transformation,[],[f16])).
% 2.49/0.98  
% 2.49/0.98  fof(f61,plain,(
% 2.49/0.98    ( ! [X2,X0,X3,X1] : (k10_relat_1(X2,X3) = k8_relset_1(X0,X1,X2,X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 2.49/0.98    inference(cnf_transformation,[],[f34])).
% 2.49/0.98  
% 2.49/0.98  fof(f15,axiom,(
% 2.49/0.98    ! [X0,X1,X2,X3] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k9_relat_1(X2,X3) = k7_relset_1(X0,X1,X2,X3))),
% 2.49/0.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.49/0.98  
% 2.49/0.98  fof(f33,plain,(
% 2.49/0.98    ! [X0,X1,X2,X3] : (k9_relat_1(X2,X3) = k7_relset_1(X0,X1,X2,X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 2.49/0.98    inference(ennf_transformation,[],[f15])).
% 2.49/0.98  
% 2.49/0.98  fof(f60,plain,(
% 2.49/0.98    ( ! [X2,X0,X3,X1] : (k9_relat_1(X2,X3) = k7_relset_1(X0,X1,X2,X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 2.49/0.98    inference(cnf_transformation,[],[f33])).
% 2.49/0.98  
% 2.49/0.98  fof(f5,axiom,(
% 2.49/0.98    ! [X0] : (v1_relat_1(X0) => k10_relat_1(X0,k2_relat_1(X0)) = k1_relat_1(X0))),
% 2.49/0.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.49/0.98  
% 2.49/0.98  fof(f21,plain,(
% 2.49/0.98    ! [X0] : (k10_relat_1(X0,k2_relat_1(X0)) = k1_relat_1(X0) | ~v1_relat_1(X0))),
% 2.49/0.98    inference(ennf_transformation,[],[f5])).
% 2.49/0.98  
% 2.49/0.98  fof(f48,plain,(
% 2.49/0.98    ( ! [X0] : (k10_relat_1(X0,k2_relat_1(X0)) = k1_relat_1(X0) | ~v1_relat_1(X0)) )),
% 2.49/0.98    inference(cnf_transformation,[],[f21])).
% 2.49/0.98  
% 2.49/0.98  fof(f1,axiom,(
% 2.49/0.98    ! [X0,X1] : (X0 = X1 <=> (r1_tarski(X1,X0) & r1_tarski(X0,X1)))),
% 2.49/0.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.49/0.98  
% 2.49/0.98  fof(f36,plain,(
% 2.49/0.98    ! [X0,X1] : ((X0 = X1 | (~r1_tarski(X1,X0) | ~r1_tarski(X0,X1))) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 2.49/0.98    inference(nnf_transformation,[],[f1])).
% 2.49/0.98  
% 2.49/0.98  fof(f37,plain,(
% 2.49/0.98    ! [X0,X1] : ((X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 2.49/0.98    inference(flattening,[],[f36])).
% 2.49/0.98  
% 2.49/0.98  fof(f42,plain,(
% 2.49/0.98    ( ! [X0,X1] : (r1_tarski(X1,X0) | X0 != X1) )),
% 2.49/0.98    inference(cnf_transformation,[],[f37])).
% 2.49/0.98  
% 2.49/0.98  fof(f64,plain,(
% 2.49/0.98    ( ! [X1] : (r1_tarski(X1,X1)) )),
% 2.49/0.98    inference(equality_resolution,[],[f42])).
% 2.49/0.98  
% 2.49/0.98  fof(f10,axiom,(
% 2.49/0.98    ! [X0,X1] : (v1_relat_1(X1) => (r1_tarski(k1_relat_1(X1),X0) => k7_relat_1(X1,X0) = X1))),
% 2.49/0.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.49/0.98  
% 2.49/0.98  fof(f27,plain,(
% 2.49/0.98    ! [X0,X1] : ((k7_relat_1(X1,X0) = X1 | ~r1_tarski(k1_relat_1(X1),X0)) | ~v1_relat_1(X1))),
% 2.49/0.98    inference(ennf_transformation,[],[f10])).
% 2.49/0.98  
% 2.49/0.98  fof(f28,plain,(
% 2.49/0.98    ! [X0,X1] : (k7_relat_1(X1,X0) = X1 | ~r1_tarski(k1_relat_1(X1),X0) | ~v1_relat_1(X1))),
% 2.49/0.98    inference(flattening,[],[f27])).
% 2.49/0.98  
% 2.49/0.98  fof(f54,plain,(
% 2.49/0.98    ( ! [X0,X1] : (k7_relat_1(X1,X0) = X1 | ~r1_tarski(k1_relat_1(X1),X0) | ~v1_relat_1(X1)) )),
% 2.49/0.98    inference(cnf_transformation,[],[f28])).
% 2.49/0.98  
% 2.49/0.98  cnf(c_4,plain,
% 2.49/0.98      ( ~ v5_relat_1(X0,X1) | r1_tarski(k2_relat_1(X0),X1) | ~ v1_relat_1(X0) ),
% 2.49/0.98      inference(cnf_transformation,[],[f44]) ).
% 2.49/0.98  
% 2.49/0.98  cnf(c_15,plain,
% 2.49/0.98      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) | v5_relat_1(X0,X2) ),
% 2.49/0.98      inference(cnf_transformation,[],[f57]) ).
% 2.49/0.98  
% 2.49/0.98  cnf(c_263,plain,
% 2.49/0.98      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 2.49/0.98      | r1_tarski(k2_relat_1(X3),X4)
% 2.49/0.98      | ~ v1_relat_1(X3)
% 2.49/0.98      | X0 != X3
% 2.49/0.98      | X2 != X4 ),
% 2.49/0.98      inference(resolution_lifted,[status(thm)],[c_4,c_15]) ).
% 2.49/0.98  
% 2.49/0.98  cnf(c_264,plain,
% 2.49/0.98      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 2.49/0.98      | r1_tarski(k2_relat_1(X0),X2)
% 2.49/0.98      | ~ v1_relat_1(X0) ),
% 2.49/0.98      inference(unflattening,[status(thm)],[c_263]) ).
% 2.49/0.98  
% 2.49/0.98  cnf(c_14,plain,
% 2.49/0.98      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) | v1_relat_1(X0) ),
% 2.49/0.98      inference(cnf_transformation,[],[f55]) ).
% 2.49/0.98  
% 2.49/0.98  cnf(c_268,plain,
% 2.49/0.98      ( r1_tarski(k2_relat_1(X0),X2)
% 2.49/0.98      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) ),
% 2.49/0.98      inference(global_propositional_subsumption,[status(thm)],[c_264,c_14]) ).
% 2.49/0.98  
% 2.49/0.98  cnf(c_269,plain,
% 2.49/0.98      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 2.49/0.98      | r1_tarski(k2_relat_1(X0),X2) ),
% 2.49/0.98      inference(renaming,[status(thm)],[c_268]) ).
% 2.49/0.98  
% 2.49/0.98  cnf(c_22,negated_conjecture,
% 2.49/0.98      ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) ),
% 2.49/0.98      inference(cnf_transformation,[],[f62]) ).
% 2.49/0.98  
% 2.49/0.98  cnf(c_284,plain,
% 2.49/0.98      ( r1_tarski(k2_relat_1(X0),X1)
% 2.49/0.98      | k1_zfmisc_1(k2_zfmisc_1(X2,X1)) != k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))
% 2.49/0.98      | sK2 != X0 ),
% 2.49/0.98      inference(resolution_lifted,[status(thm)],[c_269,c_22]) ).
% 2.49/0.98  
% 2.49/0.98  cnf(c_285,plain,
% 2.49/0.98      ( r1_tarski(k2_relat_1(sK2),X0)
% 2.49/0.98      | k1_zfmisc_1(k2_zfmisc_1(X1,X0)) != k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)) ),
% 2.49/0.98      inference(unflattening,[status(thm)],[c_284]) ).
% 2.49/0.98  
% 2.49/0.98  cnf(c_658,plain,
% 2.49/0.98      ( k1_zfmisc_1(k2_zfmisc_1(X0,X1)) != k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))
% 2.49/0.98      | r1_tarski(k2_relat_1(sK2),X1) = iProver_top ),
% 2.49/0.98      inference(predicate_to_equality,[status(thm)],[c_285]) ).
% 2.49/0.98  
% 2.49/0.98  cnf(c_1311,plain,
% 2.49/0.98      ( r1_tarski(k2_relat_1(sK2),sK0) = iProver_top ),
% 2.49/0.98      inference(equality_resolution,[status(thm)],[c_658]) ).
% 2.49/0.98  
% 2.49/0.98  cnf(c_12,plain,
% 2.49/0.98      ( ~ r1_tarski(k2_relat_1(X0),X1)
% 2.49/0.98      | ~ v1_relat_1(X0)
% 2.49/0.98      | k5_relat_1(X0,k6_relat_1(X1)) = X0 ),
% 2.49/0.98      inference(cnf_transformation,[],[f53]) ).
% 2.49/0.98  
% 2.49/0.98  cnf(c_660,plain,
% 2.49/0.98      ( k5_relat_1(X0,k6_relat_1(X1)) = X0
% 2.49/0.98      | r1_tarski(k2_relat_1(X0),X1) != iProver_top
% 2.49/0.98      | v1_relat_1(X0) != iProver_top ),
% 2.49/0.98      inference(predicate_to_equality,[status(thm)],[c_12]) ).
% 2.49/0.98  
% 2.49/0.98  cnf(c_2516,plain,
% 2.49/0.98      ( k5_relat_1(sK2,k6_relat_1(sK0)) = sK2
% 2.49/0.98      | v1_relat_1(sK2) != iProver_top ),
% 2.49/0.98      inference(superposition,[status(thm)],[c_1311,c_660]) ).
% 2.49/0.98  
% 2.49/0.98  cnf(c_451,plain,( X0 = X0 ),theory(equality) ).
% 2.49/0.98  
% 2.49/0.98  cnf(c_766,plain,
% 2.49/0.98      ( k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)) = k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)) ),
% 2.49/0.98      inference(instantiation,[status(thm)],[c_451]) ).
% 2.49/0.98  
% 2.49/0.98  cnf(c_767,plain,
% 2.49/0.98      ( r1_tarski(k2_relat_1(sK2),sK0)
% 2.49/0.98      | k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)) != k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)) ),
% 2.49/0.98      inference(instantiation,[status(thm)],[c_285]) ).
% 2.49/0.98  
% 2.49/0.98  cnf(c_341,plain,
% 2.49/0.98      ( v1_relat_1(X0)
% 2.49/0.98      | k1_zfmisc_1(k2_zfmisc_1(X1,X2)) != k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))
% 2.49/0.98      | sK2 != X0 ),
% 2.49/0.98      inference(resolution_lifted,[status(thm)],[c_14,c_22]) ).
% 2.49/0.98  
% 2.49/0.98  cnf(c_342,plain,
% 2.49/0.98      ( v1_relat_1(sK2)
% 2.49/0.98      | k1_zfmisc_1(k2_zfmisc_1(X0,X1)) != k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)) ),
% 2.49/0.98      inference(unflattening,[status(thm)],[c_341]) ).
% 2.49/0.98  
% 2.49/0.98  cnf(c_855,plain,
% 2.49/0.98      ( v1_relat_1(sK2)
% 2.49/0.98      | k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)) != k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)) ),
% 2.49/0.98      inference(instantiation,[status(thm)],[c_342]) ).
% 2.49/0.98  
% 2.49/0.98  cnf(c_929,plain,
% 2.49/0.98      ( ~ r1_tarski(k2_relat_1(sK2),X0)
% 2.49/0.98      | ~ v1_relat_1(sK2)
% 2.49/0.98      | k5_relat_1(sK2,k6_relat_1(X0)) = sK2 ),
% 2.49/0.98      inference(instantiation,[status(thm)],[c_12]) ).
% 2.49/0.98  
% 2.49/0.98  cnf(c_944,plain,
% 2.49/0.98      ( ~ r1_tarski(k2_relat_1(sK2),sK0)
% 2.49/0.98      | ~ v1_relat_1(sK2)
% 2.49/0.98      | k5_relat_1(sK2,k6_relat_1(sK0)) = sK2 ),
% 2.49/0.98      inference(instantiation,[status(thm)],[c_929]) ).
% 2.49/0.98  
% 2.49/0.98  cnf(c_2942,plain,
% 2.49/0.98      ( k5_relat_1(sK2,k6_relat_1(sK0)) = sK2 ),
% 2.49/0.98      inference(global_propositional_subsumption,
% 2.49/0.98                [status(thm)],
% 2.49/0.98                [c_2516,c_766,c_767,c_855,c_944]) ).
% 2.49/0.98  
% 2.49/0.98  cnf(c_5,plain,
% 2.49/0.98      ( v1_relat_1(k6_relat_1(X0)) ),
% 2.49/0.98      inference(cnf_transformation,[],[f46]) ).
% 2.49/0.98  
% 2.49/0.98  cnf(c_664,plain,
% 2.49/0.98      ( v1_relat_1(k6_relat_1(X0)) = iProver_top ),
% 2.49/0.98      inference(predicate_to_equality,[status(thm)],[c_5]) ).
% 2.49/0.98  
% 2.49/0.98  cnf(c_657,plain,
% 2.49/0.98      ( k1_zfmisc_1(k2_zfmisc_1(X0,X1)) != k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))
% 2.49/0.98      | v1_relat_1(sK2) = iProver_top ),
% 2.49/0.98      inference(predicate_to_equality,[status(thm)],[c_342]) ).
% 2.49/0.98  
% 2.49/0.98  cnf(c_856,plain,
% 2.49/0.98      ( k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)) != k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))
% 2.49/0.98      | v1_relat_1(sK2) = iProver_top ),
% 2.49/0.98      inference(predicate_to_equality,[status(thm)],[c_855]) ).
% 2.49/0.98  
% 2.49/0.98  cnf(c_956,plain,
% 2.49/0.98      ( v1_relat_1(sK2) = iProver_top ),
% 2.49/0.98      inference(global_propositional_subsumption,
% 2.49/0.98                [status(thm)],
% 2.49/0.98                [c_657,c_766,c_856]) ).
% 2.49/0.98  
% 2.49/0.98  cnf(c_8,plain,
% 2.49/0.98      ( ~ v1_relat_1(X0)
% 2.49/0.98      | ~ v1_relat_1(X1)
% 2.49/0.98      | k1_relat_1(k5_relat_1(X1,X0)) = k10_relat_1(X1,k1_relat_1(X0)) ),
% 2.49/0.98      inference(cnf_transformation,[],[f49]) ).
% 2.49/0.98  
% 2.49/0.98  cnf(c_661,plain,
% 2.49/0.98      ( k1_relat_1(k5_relat_1(X0,X1)) = k10_relat_1(X0,k1_relat_1(X1))
% 2.49/0.98      | v1_relat_1(X1) != iProver_top
% 2.49/0.98      | v1_relat_1(X0) != iProver_top ),
% 2.49/0.98      inference(predicate_to_equality,[status(thm)],[c_8]) ).
% 2.49/0.98  
% 2.49/0.98  cnf(c_2693,plain,
% 2.49/0.98      ( k1_relat_1(k5_relat_1(sK2,X0)) = k10_relat_1(sK2,k1_relat_1(X0))
% 2.49/0.98      | v1_relat_1(X0) != iProver_top ),
% 2.49/0.98      inference(superposition,[status(thm)],[c_956,c_661]) ).
% 2.49/0.98  
% 2.49/0.98  cnf(c_2828,plain,
% 2.49/0.98      ( k1_relat_1(k5_relat_1(sK2,k6_relat_1(X0))) = k10_relat_1(sK2,k1_relat_1(k6_relat_1(X0))) ),
% 2.49/0.98      inference(superposition,[status(thm)],[c_664,c_2693]) ).
% 2.49/0.98  
% 2.49/0.98  cnf(c_11,plain,
% 2.49/0.98      ( k1_relat_1(k6_relat_1(X0)) = X0 ),
% 2.49/0.98      inference(cnf_transformation,[],[f51]) ).
% 2.49/0.98  
% 2.49/0.98  cnf(c_2833,plain,
% 2.49/0.98      ( k1_relat_1(k5_relat_1(sK2,k6_relat_1(X0))) = k10_relat_1(sK2,X0) ),
% 2.49/0.98      inference(light_normalisation,[status(thm)],[c_2828,c_11]) ).
% 2.49/0.98  
% 2.49/0.98  cnf(c_3038,plain,
% 2.49/0.98      ( k10_relat_1(sK2,sK0) = k1_relat_1(sK2) ),
% 2.49/0.98      inference(superposition,[status(thm)],[c_2942,c_2833]) ).
% 2.49/0.98  
% 2.49/0.98  cnf(c_16,plain,
% 2.49/0.98      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) | v4_relat_1(X0,X1) ),
% 2.49/0.98      inference(cnf_transformation,[],[f56]) ).
% 2.49/0.98  
% 2.49/0.98  cnf(c_9,plain,
% 2.49/0.98      ( ~ v4_relat_1(X0,X1) | ~ v1_relat_1(X0) | k7_relat_1(X0,X1) = X0 ),
% 2.49/0.98      inference(cnf_transformation,[],[f50]) ).
% 2.49/0.98  
% 2.49/0.98  cnf(c_242,plain,
% 2.49/0.98      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 2.49/0.98      | ~ v1_relat_1(X0)
% 2.49/0.98      | k7_relat_1(X0,X1) = X0 ),
% 2.49/0.98      inference(resolution,[status(thm)],[c_16,c_9]) ).
% 2.49/0.98  
% 2.49/0.98  cnf(c_246,plain,
% 2.49/0.98      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 2.49/0.98      | k7_relat_1(X0,X1) = X0 ),
% 2.49/0.98      inference(global_propositional_subsumption,
% 2.49/0.98                [status(thm)],
% 2.49/0.98                [c_242,c_16,c_14,c_9]) ).
% 2.49/0.98  
% 2.49/0.98  cnf(c_296,plain,
% 2.49/0.98      ( k7_relat_1(X0,X1) = X0
% 2.49/0.98      | k1_zfmisc_1(k2_zfmisc_1(X1,X2)) != k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))
% 2.49/0.98      | sK2 != X0 ),
% 2.49/0.98      inference(resolution_lifted,[status(thm)],[c_246,c_22]) ).
% 2.49/0.98  
% 2.49/0.98  cnf(c_297,plain,
% 2.49/0.98      ( k7_relat_1(sK2,X0) = sK2
% 2.49/0.98      | k1_zfmisc_1(k2_zfmisc_1(X0,X1)) != k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)) ),
% 2.49/0.98      inference(unflattening,[status(thm)],[c_296]) ).
% 2.49/0.98  
% 2.49/0.98  cnf(c_765,plain,
% 2.49/0.98      ( k7_relat_1(sK2,sK1) = sK2 ),
% 2.49/0.98      inference(equality_resolution,[status(thm)],[c_297]) ).
% 2.49/0.98  
% 2.49/0.98  cnf(c_6,plain,
% 2.49/0.98      ( ~ v1_relat_1(X0) | k2_relat_1(k7_relat_1(X0,X1)) = k9_relat_1(X0,X1) ),
% 2.49/0.98      inference(cnf_transformation,[],[f47]) ).
% 2.49/0.98  
% 2.49/0.98  cnf(c_663,plain,
% 2.49/0.98      ( k2_relat_1(k7_relat_1(X0,X1)) = k9_relat_1(X0,X1)
% 2.49/0.98      | v1_relat_1(X0) != iProver_top ),
% 2.49/0.98      inference(predicate_to_equality,[status(thm)],[c_6]) ).
% 2.49/0.98  
% 2.49/0.98  cnf(c_1622,plain,
% 2.49/0.98      ( k2_relat_1(k7_relat_1(sK2,X0)) = k9_relat_1(sK2,X0) ),
% 2.49/0.98      inference(superposition,[status(thm)],[c_956,c_663]) ).
% 2.49/0.98  
% 2.49/0.98  cnf(c_1913,plain,
% 2.49/0.98      ( k9_relat_1(sK2,sK1) = k2_relat_1(sK2) ),
% 2.49/0.98      inference(superposition,[status(thm)],[c_765,c_1622]) ).
% 2.49/0.98  
% 2.49/0.98  cnf(c_17,plain,
% 2.49/0.98      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 2.49/0.98      | k1_relset_1(X1,X2,X0) = k1_relat_1(X0) ),
% 2.49/0.98      inference(cnf_transformation,[],[f58]) ).
% 2.49/0.98  
% 2.49/0.98  cnf(c_332,plain,
% 2.49/0.98      ( k1_relset_1(X0,X1,X2) = k1_relat_1(X2)
% 2.49/0.98      | k1_zfmisc_1(k2_zfmisc_1(X0,X1)) != k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))
% 2.49/0.98      | sK2 != X2 ),
% 2.49/0.98      inference(resolution_lifted,[status(thm)],[c_17,c_22]) ).
% 2.49/0.98  
% 2.49/0.98  cnf(c_333,plain,
% 2.49/0.98      ( k1_relset_1(X0,X1,sK2) = k1_relat_1(sK2)
% 2.49/0.98      | k1_zfmisc_1(k2_zfmisc_1(X0,X1)) != k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)) ),
% 2.49/0.98      inference(unflattening,[status(thm)],[c_332]) ).
% 2.49/0.98  
% 2.49/0.98  cnf(c_788,plain,
% 2.49/0.98      ( k1_relset_1(sK1,sK0,sK2) = k1_relat_1(sK2) ),
% 2.49/0.98      inference(equality_resolution,[status(thm)],[c_333]) ).
% 2.49/0.98  
% 2.49/0.98  cnf(c_18,plain,
% 2.49/0.98      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 2.49/0.98      | k2_relset_1(X1,X2,X0) = k2_relat_1(X0) ),
% 2.49/0.98      inference(cnf_transformation,[],[f59]) ).
% 2.49/0.98  
% 2.49/0.98  cnf(c_323,plain,
% 2.49/0.98      ( k2_relset_1(X0,X1,X2) = k2_relat_1(X2)
% 2.49/0.98      | k1_zfmisc_1(k2_zfmisc_1(X0,X1)) != k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))
% 2.49/0.98      | sK2 != X2 ),
% 2.49/0.98      inference(resolution_lifted,[status(thm)],[c_18,c_22]) ).
% 2.49/0.98  
% 2.49/0.98  cnf(c_324,plain,
% 2.49/0.98      ( k2_relset_1(X0,X1,sK2) = k2_relat_1(sK2)
% 2.49/0.98      | k1_zfmisc_1(k2_zfmisc_1(X0,X1)) != k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)) ),
% 2.49/0.98      inference(unflattening,[status(thm)],[c_323]) ).
% 2.49/0.98  
% 2.49/0.98  cnf(c_785,plain,
% 2.49/0.98      ( k2_relset_1(sK1,sK0,sK2) = k2_relat_1(sK2) ),
% 2.49/0.98      inference(equality_resolution,[status(thm)],[c_324]) ).
% 2.49/0.98  
% 2.49/0.98  cnf(c_21,negated_conjecture,
% 2.49/0.98      ( k2_relset_1(sK1,sK0,sK2) != k7_relset_1(sK1,sK0,sK2,k8_relset_1(sK1,sK0,sK2,sK0))
% 2.49/0.98      | k1_relset_1(sK1,sK0,sK2) != k8_relset_1(sK1,sK0,sK2,k7_relset_1(sK1,sK0,sK2,sK1)) ),
% 2.49/0.98      inference(cnf_transformation,[],[f63]) ).
% 2.49/0.98  
% 2.49/0.98  cnf(c_870,plain,
% 2.49/0.98      ( k8_relset_1(sK1,sK0,sK2,k7_relset_1(sK1,sK0,sK2,sK1)) != k1_relset_1(sK1,sK0,sK2)
% 2.49/0.98      | k7_relset_1(sK1,sK0,sK2,k8_relset_1(sK1,sK0,sK2,sK0)) != k2_relat_1(sK2) ),
% 2.49/0.98      inference(demodulation,[status(thm)],[c_785,c_21]) ).
% 2.49/0.98  
% 2.49/0.98  cnf(c_1214,plain,
% 2.49/0.98      ( k8_relset_1(sK1,sK0,sK2,k7_relset_1(sK1,sK0,sK2,sK1)) != k1_relat_1(sK2)
% 2.49/0.98      | k7_relset_1(sK1,sK0,sK2,k8_relset_1(sK1,sK0,sK2,sK0)) != k2_relat_1(sK2) ),
% 2.49/0.98      inference(demodulation,[status(thm)],[c_788,c_870]) ).
% 2.49/0.98  
% 2.49/0.98  cnf(c_20,plain,
% 2.49/0.98      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 2.49/0.98      | k8_relset_1(X1,X2,X0,X3) = k10_relat_1(X0,X3) ),
% 2.49/0.98      inference(cnf_transformation,[],[f61]) ).
% 2.49/0.98  
% 2.49/0.98  cnf(c_305,plain,
% 2.49/0.98      ( k8_relset_1(X0,X1,X2,X3) = k10_relat_1(X2,X3)
% 2.49/0.98      | k1_zfmisc_1(k2_zfmisc_1(X0,X1)) != k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))
% 2.49/0.98      | sK2 != X2 ),
% 2.49/0.98      inference(resolution_lifted,[status(thm)],[c_20,c_22]) ).
% 2.49/0.98  
% 2.49/0.98  cnf(c_306,plain,
% 2.49/0.98      ( k8_relset_1(X0,X1,sK2,X2) = k10_relat_1(sK2,X2)
% 2.49/0.98      | k1_zfmisc_1(k2_zfmisc_1(X0,X1)) != k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)) ),
% 2.49/0.98      inference(unflattening,[status(thm)],[c_305]) ).
% 2.49/0.98  
% 2.49/0.98  cnf(c_821,plain,
% 2.49/0.98      ( k8_relset_1(sK1,sK0,sK2,X0) = k10_relat_1(sK2,X0) ),
% 2.49/0.98      inference(equality_resolution,[status(thm)],[c_306]) ).
% 2.49/0.98  
% 2.49/0.98  cnf(c_19,plain,
% 2.49/0.98      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 2.49/0.98      | k7_relset_1(X1,X2,X0,X3) = k9_relat_1(X0,X3) ),
% 2.49/0.98      inference(cnf_transformation,[],[f60]) ).
% 2.49/0.98  
% 2.49/0.98  cnf(c_314,plain,
% 2.49/0.98      ( k7_relset_1(X0,X1,X2,X3) = k9_relat_1(X2,X3)
% 2.49/0.98      | k1_zfmisc_1(k2_zfmisc_1(X0,X1)) != k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))
% 2.49/0.98      | sK2 != X2 ),
% 2.49/0.98      inference(resolution_lifted,[status(thm)],[c_19,c_22]) ).
% 2.49/0.98  
% 2.49/0.98  cnf(c_315,plain,
% 2.49/0.98      ( k7_relset_1(X0,X1,sK2,X2) = k9_relat_1(sK2,X2)
% 2.49/0.98      | k1_zfmisc_1(k2_zfmisc_1(X0,X1)) != k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)) ),
% 2.49/0.98      inference(unflattening,[status(thm)],[c_314]) ).
% 2.49/0.98  
% 2.49/0.98  cnf(c_825,plain,
% 2.49/0.98      ( k7_relset_1(sK1,sK0,sK2,X0) = k9_relat_1(sK2,X0) ),
% 2.49/0.98      inference(equality_resolution,[status(thm)],[c_315]) ).
% 2.49/0.98  
% 2.49/0.98  cnf(c_1413,plain,
% 2.49/0.98      ( k10_relat_1(sK2,k9_relat_1(sK2,sK1)) != k1_relat_1(sK2)
% 2.49/0.98      | k9_relat_1(sK2,k10_relat_1(sK2,sK0)) != k2_relat_1(sK2) ),
% 2.49/0.98      inference(demodulation,[status(thm)],[c_1214,c_821,c_825]) ).
% 2.49/0.98  
% 2.49/0.98  cnf(c_1915,plain,
% 2.49/0.98      ( k10_relat_1(sK2,k2_relat_1(sK2)) != k1_relat_1(sK2)
% 2.49/0.98      | k9_relat_1(sK2,k10_relat_1(sK2,sK0)) != k2_relat_1(sK2) ),
% 2.49/0.98      inference(demodulation,[status(thm)],[c_1913,c_1413]) ).
% 2.49/0.98  
% 2.49/0.98  cnf(c_7,plain,
% 2.49/0.98      ( ~ v1_relat_1(X0) | k10_relat_1(X0,k2_relat_1(X0)) = k1_relat_1(X0) ),
% 2.49/0.98      inference(cnf_transformation,[],[f48]) ).
% 2.49/0.98  
% 2.49/0.98  cnf(c_662,plain,
% 2.49/0.98      ( k10_relat_1(X0,k2_relat_1(X0)) = k1_relat_1(X0)
% 2.49/0.98      | v1_relat_1(X0) != iProver_top ),
% 2.49/0.98      inference(predicate_to_equality,[status(thm)],[c_7]) ).
% 2.49/0.98  
% 2.49/0.98  cnf(c_1507,plain,
% 2.49/0.98      ( k10_relat_1(sK2,k2_relat_1(sK2)) = k1_relat_1(sK2) ),
% 2.49/0.98      inference(superposition,[status(thm)],[c_956,c_662]) ).
% 2.49/0.98  
% 2.49/0.98  cnf(c_1916,plain,
% 2.49/0.98      ( k9_relat_1(sK2,k10_relat_1(sK2,sK0)) != k2_relat_1(sK2)
% 2.49/0.98      | k1_relat_1(sK2) != k1_relat_1(sK2) ),
% 2.49/0.98      inference(light_normalisation,[status(thm)],[c_1915,c_1507]) ).
% 2.49/0.98  
% 2.49/0.98  cnf(c_1917,plain,
% 2.49/0.98      ( k9_relat_1(sK2,k10_relat_1(sK2,sK0)) != k2_relat_1(sK2) ),
% 2.49/0.98      inference(equality_resolution_simp,[status(thm)],[c_1916]) ).
% 2.49/0.98  
% 2.49/0.98  cnf(c_3052,plain,
% 2.49/0.98      ( k9_relat_1(sK2,k1_relat_1(sK2)) != k2_relat_1(sK2) ),
% 2.49/0.98      inference(demodulation,[status(thm)],[c_3038,c_1917]) ).
% 2.49/0.98  
% 2.49/0.98  cnf(c_1,plain,( r1_tarski(X0,X0) ),inference(cnf_transformation,[],[f64]) ).
% 2.49/0.98  
% 2.49/0.98  cnf(c_665,plain,
% 2.49/0.98      ( r1_tarski(X0,X0) = iProver_top ),
% 2.49/0.98      inference(predicate_to_equality,[status(thm)],[c_1]) ).
% 2.49/0.98  
% 2.49/0.98  cnf(c_13,plain,
% 2.49/0.98      ( ~ r1_tarski(k1_relat_1(X0),X1)
% 2.49/0.98      | ~ v1_relat_1(X0)
% 2.49/0.98      | k7_relat_1(X0,X1) = X0 ),
% 2.49/0.98      inference(cnf_transformation,[],[f54]) ).
% 2.49/0.98  
% 2.49/0.98  cnf(c_659,plain,
% 2.49/0.98      ( k7_relat_1(X0,X1) = X0
% 2.49/0.98      | r1_tarski(k1_relat_1(X0),X1) != iProver_top
% 2.49/0.98      | v1_relat_1(X0) != iProver_top ),
% 2.49/0.98      inference(predicate_to_equality,[status(thm)],[c_13]) ).
% 2.49/0.98  
% 2.49/0.98  cnf(c_1719,plain,
% 2.49/0.98      ( k7_relat_1(X0,k1_relat_1(X0)) = X0 | v1_relat_1(X0) != iProver_top ),
% 2.49/0.98      inference(superposition,[status(thm)],[c_665,c_659]) ).
% 2.49/0.98  
% 2.49/0.98  cnf(c_2273,plain,
% 2.49/0.98      ( k7_relat_1(sK2,k1_relat_1(sK2)) = sK2 ),
% 2.49/0.98      inference(superposition,[status(thm)],[c_956,c_1719]) ).
% 2.49/0.98  
% 2.49/0.98  cnf(c_2401,plain,
% 2.49/0.98      ( k9_relat_1(sK2,k1_relat_1(sK2)) = k2_relat_1(sK2) ),
% 2.49/0.98      inference(superposition,[status(thm)],[c_2273,c_1622]) ).
% 2.49/0.98  
% 2.49/0.98  cnf(c_3053,plain,
% 2.49/0.98      ( k2_relat_1(sK2) != k2_relat_1(sK2) ),
% 2.49/0.98      inference(light_normalisation,[status(thm)],[c_3052,c_2401]) ).
% 2.49/0.98  
% 2.49/0.98  cnf(c_3054,plain,
% 2.49/0.98      ( $false ),
% 2.49/0.98      inference(equality_resolution_simp,[status(thm)],[c_3053]) ).
% 2.49/0.98  
% 2.49/0.98  
% 2.49/0.98  % SZS output end CNFRefutation for theBenchmark.p
% 2.49/0.98  
% 2.49/0.98  ------                               Statistics
% 2.49/0.98  
% 2.49/0.98  ------ General
% 2.49/0.98  
% 2.49/0.98  abstr_ref_over_cycles:                  0
% 2.49/0.98  abstr_ref_under_cycles:                 0
% 2.49/0.98  gc_basic_clause_elim:                   0
% 2.49/0.98  forced_gc_time:                         0
% 2.49/0.98  parsing_time:                           0.008
% 2.49/0.98  unif_index_cands_time:                  0.
% 2.49/0.98  unif_index_add_time:                    0.
% 2.49/0.98  orderings_time:                         0.
% 2.49/0.98  out_proof_time:                         0.011
% 2.49/0.98  total_time:                             0.128
% 2.49/0.98  num_of_symbols:                         52
% 2.49/0.98  num_of_terms:                           3645
% 2.49/0.98  
% 2.49/0.98  ------ Preprocessing
% 2.49/0.98  
% 2.49/0.98  num_of_splits:                          0
% 2.49/0.98  num_of_split_atoms:                     0
% 2.49/0.98  num_of_reused_defs:                     0
% 2.49/0.98  num_eq_ax_congr_red:                    22
% 2.49/0.98  num_of_sem_filtered_clauses:            1
% 2.49/0.98  num_of_subtypes:                        0
% 2.49/0.98  monotx_restored_types:                  0
% 2.49/0.98  sat_num_of_epr_types:                   0
% 2.49/0.98  sat_num_of_non_cyclic_types:            0
% 2.49/0.98  sat_guarded_non_collapsed_types:        0
% 2.49/0.98  num_pure_diseq_elim:                    0
% 2.49/0.98  simp_replaced_by:                       0
% 2.49/0.98  res_preprocessed:                       109
% 2.49/0.98  prep_upred:                             0
% 2.49/0.98  prep_unflattend:                        9
% 2.49/0.98  smt_new_axioms:                         0
% 2.49/0.98  pred_elim_cands:                        2
% 2.49/0.98  pred_elim:                              3
% 2.49/0.98  pred_elim_cl:                           4
% 2.49/0.98  pred_elim_cycles:                       5
% 2.49/0.98  merged_defs:                            0
% 2.49/0.98  merged_defs_ncl:                        0
% 2.49/0.98  bin_hyper_res:                          0
% 2.49/0.98  prep_cycles:                            4
% 2.49/0.98  pred_elim_time:                         0.002
% 2.49/0.98  splitting_time:                         0.
% 2.49/0.98  sem_filter_time:                        0.
% 2.49/0.98  monotx_time:                            0.
% 2.49/0.98  subtype_inf_time:                       0.
% 2.49/0.98  
% 2.49/0.98  ------ Problem properties
% 2.49/0.98  
% 2.49/0.98  clauses:                                18
% 2.49/0.98  conjectures:                            1
% 2.49/0.98  epr:                                    2
% 2.49/0.98  horn:                                   18
% 2.49/0.98  ground:                                 1
% 2.49/0.98  unary:                                  4
% 2.49/0.98  binary:                                 10
% 2.49/0.98  lits:                                   36
% 2.49/0.98  lits_eq:                                22
% 2.49/0.98  fd_pure:                                0
% 2.49/0.98  fd_pseudo:                              0
% 2.49/0.98  fd_cond:                                0
% 2.49/0.98  fd_pseudo_cond:                         1
% 2.49/0.98  ac_symbols:                             0
% 2.49/0.98  
% 2.49/0.98  ------ Propositional Solver
% 2.49/0.98  
% 2.49/0.98  prop_solver_calls:                      27
% 2.49/0.98  prop_fast_solver_calls:                 599
% 2.49/0.98  smt_solver_calls:                       0
% 2.49/0.98  smt_fast_solver_calls:                  0
% 2.49/0.98  prop_num_of_clauses:                    1465
% 2.49/0.98  prop_preprocess_simplified:             4585
% 2.49/0.98  prop_fo_subsumed:                       5
% 2.49/0.98  prop_solver_time:                       0.
% 2.49/0.98  smt_solver_time:                        0.
% 2.49/0.98  smt_fast_solver_time:                   0.
% 2.49/0.98  prop_fast_solver_time:                  0.
% 2.49/0.98  prop_unsat_core_time:                   0.
% 2.49/0.98  
% 2.49/0.98  ------ QBF
% 2.49/0.98  
% 2.49/0.98  qbf_q_res:                              0
% 2.49/0.98  qbf_num_tautologies:                    0
% 2.49/0.98  qbf_prep_cycles:                        0
% 2.49/0.98  
% 2.49/0.98  ------ BMC1
% 2.49/0.98  
% 2.49/0.98  bmc1_current_bound:                     -1
% 2.49/0.98  bmc1_last_solved_bound:                 -1
% 2.49/0.98  bmc1_unsat_core_size:                   -1
% 2.49/0.98  bmc1_unsat_core_parents_size:           -1
% 2.49/0.98  bmc1_merge_next_fun:                    0
% 2.49/0.98  bmc1_unsat_core_clauses_time:           0.
% 2.49/0.98  
% 2.49/0.98  ------ Instantiation
% 2.49/0.98  
% 2.49/0.98  inst_num_of_clauses:                    473
% 2.49/0.98  inst_num_in_passive:                    83
% 2.49/0.98  inst_num_in_active:                     226
% 2.49/0.98  inst_num_in_unprocessed:                165
% 2.49/0.98  inst_num_of_loops:                      230
% 2.49/0.98  inst_num_of_learning_restarts:          0
% 2.49/0.98  inst_num_moves_active_passive:          2
% 2.49/0.98  inst_lit_activity:                      0
% 2.49/0.98  inst_lit_activity_moves:                0
% 2.49/0.98  inst_num_tautologies:                   0
% 2.49/0.98  inst_num_prop_implied:                  0
% 2.49/0.98  inst_num_existing_simplified:           0
% 2.49/0.98  inst_num_eq_res_simplified:             0
% 2.49/0.98  inst_num_child_elim:                    0
% 2.49/0.98  inst_num_of_dismatching_blockings:      20
% 2.49/0.98  inst_num_of_non_proper_insts:           331
% 2.49/0.98  inst_num_of_duplicates:                 0
% 2.49/0.98  inst_inst_num_from_inst_to_res:         0
% 2.49/0.98  inst_dismatching_checking_time:         0.
% 2.49/0.98  
% 2.49/0.98  ------ Resolution
% 2.49/0.98  
% 2.49/0.98  res_num_of_clauses:                     0
% 2.49/0.98  res_num_in_passive:                     0
% 2.49/0.98  res_num_in_active:                      0
% 2.49/0.98  res_num_of_loops:                       113
% 2.49/0.98  res_forward_subset_subsumed:            46
% 2.49/0.98  res_backward_subset_subsumed:           2
% 2.49/0.98  res_forward_subsumed:                   0
% 2.49/0.98  res_backward_subsumed:                  0
% 2.49/0.98  res_forward_subsumption_resolution:     0
% 2.49/0.98  res_backward_subsumption_resolution:    0
% 2.49/0.98  res_clause_to_clause_subsumption:       79
% 2.49/0.98  res_orphan_elimination:                 0
% 2.49/0.98  res_tautology_del:                      32
% 2.49/0.98  res_num_eq_res_simplified:              0
% 2.49/0.98  res_num_sel_changes:                    0
% 2.49/0.98  res_moves_from_active_to_pass:          0
% 2.49/0.98  
% 2.49/0.98  ------ Superposition
% 2.49/0.98  
% 2.49/0.98  sup_time_total:                         0.
% 2.49/0.98  sup_time_generating:                    0.
% 2.49/0.98  sup_time_sim_full:                      0.
% 2.49/0.98  sup_time_sim_immed:                     0.
% 2.49/0.98  
% 2.49/0.98  sup_num_of_clauses:                     49
% 2.49/0.98  sup_num_in_active:                      41
% 2.49/0.98  sup_num_in_passive:                     8
% 2.49/0.98  sup_num_of_loops:                       45
% 2.49/0.98  sup_fw_superposition:                   26
% 2.49/0.98  sup_bw_superposition:                   4
% 2.49/0.98  sup_immediate_simplified:               8
% 2.49/0.98  sup_given_eliminated:                   0
% 2.49/0.98  comparisons_done:                       0
% 2.49/0.98  comparisons_avoided:                    0
% 2.49/0.98  
% 2.49/0.98  ------ Simplifications
% 2.49/0.98  
% 2.49/0.98  
% 2.49/0.98  sim_fw_subset_subsumed:                 0
% 2.49/0.98  sim_bw_subset_subsumed:                 0
% 2.49/0.98  sim_fw_subsumed:                        2
% 2.49/0.98  sim_bw_subsumed:                        0
% 2.49/0.98  sim_fw_subsumption_res:                 0
% 2.49/0.98  sim_bw_subsumption_res:                 0
% 2.49/0.98  sim_tautology_del:                      0
% 2.49/0.98  sim_eq_tautology_del:                   1
% 2.49/0.98  sim_eq_res_simp:                        1
% 2.49/0.98  sim_fw_demodulated:                     2
% 2.49/0.98  sim_bw_demodulated:                     4
% 2.49/0.98  sim_light_normalised:                   8
% 2.49/0.98  sim_joinable_taut:                      0
% 2.49/0.98  sim_joinable_simp:                      0
% 2.49/0.98  sim_ac_normalised:                      0
% 2.49/0.98  sim_smt_subsumption:                    0
% 2.49/0.98  
%------------------------------------------------------------------------------
