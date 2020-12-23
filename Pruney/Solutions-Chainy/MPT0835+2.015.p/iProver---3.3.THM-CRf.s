%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n018.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 11:56:10 EST 2020

% Result     : Theorem 2.02s
% Output     : CNFRefutation 2.02s
% Verified   : 
% Statistics : Number of formulae       :  139 ( 357 expanded)
%              Number of clauses        :   82 ( 156 expanded)
%              Number of leaves         :   19 (  71 expanded)
%              Depth                    :   21
%              Number of atoms          :  303 ( 857 expanded)
%              Number of equality atoms :  172 ( 427 expanded)
%              Maximal formula depth    :    8 (   4 average)
%              Maximal clause size      :    6 (   2 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f10,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ( r1_tarski(k2_relat_1(X1),X0)
       => k5_relat_1(X1,k6_relat_1(X0)) = X1 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f27,plain,(
    ! [X0,X1] :
      ( k5_relat_1(X1,k6_relat_1(X0)) = X1
      | ~ r1_tarski(k2_relat_1(X1),X0)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f28,plain,(
    ! [X0,X1] :
      ( k5_relat_1(X1,k6_relat_1(X0)) = X1
      | ~ r1_tarski(k2_relat_1(X1),X0)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f27])).

fof(f50,plain,(
    ! [X0,X1] :
      ( k5_relat_1(X1,k6_relat_1(X0)) = X1
      | ~ r1_tarski(k2_relat_1(X1),X0)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f2,axiom,(
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
    inference(ennf_transformation,[],[f2])).

fof(f36,plain,(
    ! [X0,X1] :
      ( ( ( v5_relat_1(X1,X0)
          | ~ r1_tarski(k2_relat_1(X1),X0) )
        & ( r1_tarski(k2_relat_1(X1),X0)
          | ~ v5_relat_1(X1,X0) ) )
      | ~ v1_relat_1(X1) ) ),
    inference(nnf_transformation,[],[f20])).

fof(f40,plain,(
    ! [X0,X1] :
      ( r1_tarski(k2_relat_1(X1),X0)
      | ~ v5_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f36])).

fof(f12,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => ( v5_relat_1(X2,X1)
        & v4_relat_1(X2,X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f30,plain,(
    ! [X0,X1,X2] :
      ( ( v5_relat_1(X2,X1)
        & v4_relat_1(X2,X0) )
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f53,plain,(
    ! [X2,X0,X1] :
      ( v5_relat_1(X2,X1)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f11,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => v1_relat_1(X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f29,plain,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f51,plain,(
    ! [X2,X0,X1] :
      ( v1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f29])).

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

fof(f35,plain,(
    ? [X0,X1,X2] :
      ( ( k1_relset_1(X1,X0,X2) != k8_relset_1(X1,X0,X2,k7_relset_1(X1,X0,X2,X1))
        | k2_relset_1(X1,X0,X2) != k7_relset_1(X1,X0,X2,k8_relset_1(X1,X0,X2,X0)) )
      & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) ) ),
    inference(ennf_transformation,[],[f18])).

fof(f37,plain,
    ( ? [X0,X1,X2] :
        ( ( k1_relset_1(X1,X0,X2) != k8_relset_1(X1,X0,X2,k7_relset_1(X1,X0,X2,X1))
          | k2_relset_1(X1,X0,X2) != k7_relset_1(X1,X0,X2,k8_relset_1(X1,X0,X2,X0)) )
        & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) )
   => ( ( k1_relset_1(sK1,sK0,sK2) != k8_relset_1(sK1,sK0,sK2,k7_relset_1(sK1,sK0,sK2,sK1))
        | k2_relset_1(sK1,sK0,sK2) != k7_relset_1(sK1,sK0,sK2,k8_relset_1(sK1,sK0,sK2,sK0)) )
      & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) ) ),
    introduced(choice_axiom,[])).

fof(f38,plain,
    ( ( k1_relset_1(sK1,sK0,sK2) != k8_relset_1(sK1,sK0,sK2,k7_relset_1(sK1,sK0,sK2,sK1))
      | k2_relset_1(sK1,sK0,sK2) != k7_relset_1(sK1,sK0,sK2,k8_relset_1(sK1,sK0,sK2,sK0)) )
    & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f35,f37])).

fof(f58,plain,(
    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) ),
    inference(cnf_transformation,[],[f38])).

fof(f3,axiom,(
    ! [X0] : v1_relat_1(k6_relat_1(X0)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f42,plain,(
    ! [X0] : v1_relat_1(k6_relat_1(X0)) ),
    inference(cnf_transformation,[],[f3])).

fof(f7,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( v1_relat_1(X1)
         => k1_relat_1(k5_relat_1(X0,X1)) = k10_relat_1(X0,k1_relat_1(X1)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f24,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k1_relat_1(k5_relat_1(X0,X1)) = k10_relat_1(X0,k1_relat_1(X1))
          | ~ v1_relat_1(X1) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f46,plain,(
    ! [X0,X1] :
      ( k1_relat_1(k5_relat_1(X0,X1)) = k10_relat_1(X0,k1_relat_1(X1))
      | ~ v1_relat_1(X1)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f9,axiom,(
    ! [X0] :
      ( k2_relat_1(k6_relat_1(X0)) = X0
      & k1_relat_1(k6_relat_1(X0)) = X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f48,plain,(
    ! [X0] : k1_relat_1(k6_relat_1(X0)) = X0 ),
    inference(cnf_transformation,[],[f9])).

fof(f52,plain,(
    ! [X2,X0,X1] :
      ( v4_relat_1(X2,X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f8,axiom,(
    ! [X0,X1] :
      ( ( v4_relat_1(X1,X0)
        & v1_relat_1(X1) )
     => k7_relat_1(X1,X0) = X1 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f25,plain,(
    ! [X0,X1] :
      ( k7_relat_1(X1,X0) = X1
      | ~ v4_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f26,plain,(
    ! [X0,X1] :
      ( k7_relat_1(X1,X0) = X1
      | ~ v4_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f25])).

fof(f47,plain,(
    ! [X0,X1] :
      ( k7_relat_1(X1,X0) = X1
      | ~ v4_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f5,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => k2_relat_1(k7_relat_1(X1,X0)) = k9_relat_1(X1,X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f22,plain,(
    ! [X0,X1] :
      ( k2_relat_1(k7_relat_1(X1,X0)) = k9_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f44,plain,(
    ! [X0,X1] :
      ( k2_relat_1(k7_relat_1(X1,X0)) = k9_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f13,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k1_relat_1(X2) = k1_relset_1(X0,X1,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f31,plain,(
    ! [X0,X1,X2] :
      ( k1_relat_1(X2) = k1_relset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f54,plain,(
    ! [X2,X0,X1] :
      ( k1_relat_1(X2) = k1_relset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f14,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k2_relat_1(X2) = k2_relset_1(X0,X1,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f32,plain,(
    ! [X0,X1,X2] :
      ( k2_relat_1(X2) = k2_relset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f55,plain,(
    ! [X2,X0,X1] :
      ( k2_relat_1(X2) = k2_relset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f32])).

fof(f59,plain,
    ( k1_relset_1(sK1,sK0,sK2) != k8_relset_1(sK1,sK0,sK2,k7_relset_1(sK1,sK0,sK2,sK1))
    | k2_relset_1(sK1,sK0,sK2) != k7_relset_1(sK1,sK0,sK2,k8_relset_1(sK1,sK0,sK2,sK0)) ),
    inference(cnf_transformation,[],[f38])).

fof(f16,axiom,(
    ! [X0,X1,X2,X3] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k10_relat_1(X2,X3) = k8_relset_1(X0,X1,X2,X3) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f34,plain,(
    ! [X0,X1,X2,X3] :
      ( k10_relat_1(X2,X3) = k8_relset_1(X0,X1,X2,X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f16])).

fof(f57,plain,(
    ! [X2,X0,X3,X1] :
      ( k10_relat_1(X2,X3) = k8_relset_1(X0,X1,X2,X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f34])).

fof(f15,axiom,(
    ! [X0,X1,X2,X3] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k9_relat_1(X2,X3) = k7_relset_1(X0,X1,X2,X3) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f33,plain,(
    ! [X0,X1,X2,X3] :
      ( k9_relat_1(X2,X3) = k7_relset_1(X0,X1,X2,X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f15])).

fof(f56,plain,(
    ! [X2,X0,X3,X1] :
      ( k9_relat_1(X2,X3) = k7_relset_1(X0,X1,X2,X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f33])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
     => k3_xboole_0(X0,X1) = X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f19,plain,(
    ! [X0,X1] :
      ( k3_xboole_0(X0,X1) = X0
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f39,plain,(
    ! [X0,X1] :
      ( k3_xboole_0(X0,X1) = X0
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f6,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => k10_relat_1(X1,X0) = k10_relat_1(X1,k3_xboole_0(k2_relat_1(X1),X0)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f23,plain,(
    ! [X0,X1] :
      ( k10_relat_1(X1,X0) = k10_relat_1(X1,k3_xboole_0(k2_relat_1(X1),X0))
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f45,plain,(
    ! [X0,X1] :
      ( k10_relat_1(X1,X0) = k10_relat_1(X1,k3_xboole_0(k2_relat_1(X1),X0))
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f4,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => k2_relat_1(X0) = k9_relat_1(X0,k1_relat_1(X0)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f21,plain,(
    ! [X0] :
      ( k2_relat_1(X0) = k9_relat_1(X0,k1_relat_1(X0))
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f43,plain,(
    ! [X0] :
      ( k2_relat_1(X0) = k9_relat_1(X0,k1_relat_1(X0))
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f21])).

cnf(c_11,plain,
    ( ~ r1_tarski(k2_relat_1(X0),X1)
    | ~ v1_relat_1(X0)
    | k5_relat_1(X0,k6_relat_1(X1)) = X0 ),
    inference(cnf_transformation,[],[f50])).

cnf(c_2,plain,
    ( ~ v5_relat_1(X0,X1)
    | r1_tarski(k2_relat_1(X0),X1)
    | ~ v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f40])).

cnf(c_13,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | v5_relat_1(X0,X2) ),
    inference(cnf_transformation,[],[f53])).

cnf(c_251,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | r1_tarski(k2_relat_1(X3),X4)
    | ~ v1_relat_1(X3)
    | X0 != X3
    | X2 != X4 ),
    inference(resolution_lifted,[status(thm)],[c_2,c_13])).

cnf(c_252,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | r1_tarski(k2_relat_1(X0),X2)
    | ~ v1_relat_1(X0) ),
    inference(unflattening,[status(thm)],[c_251])).

cnf(c_12,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f51])).

cnf(c_256,plain,
    ( r1_tarski(k2_relat_1(X0),X2)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) ),
    inference(global_propositional_subsumption,[status(thm)],[c_252,c_12])).

cnf(c_257,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | r1_tarski(k2_relat_1(X0),X2) ),
    inference(renaming,[status(thm)],[c_256])).

cnf(c_20,negated_conjecture,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) ),
    inference(cnf_transformation,[],[f58])).

cnf(c_308,plain,
    ( r1_tarski(k2_relat_1(X0),X1)
    | k1_zfmisc_1(k2_zfmisc_1(X2,X1)) != k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))
    | sK2 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_257,c_20])).

cnf(c_309,plain,
    ( r1_tarski(k2_relat_1(sK2),X0)
    | k1_zfmisc_1(k2_zfmisc_1(X1,X0)) != k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)) ),
    inference(unflattening,[status(thm)],[c_308])).

cnf(c_402,plain,
    ( ~ v1_relat_1(X0)
    | X1 != X2
    | k5_relat_1(X0,k6_relat_1(X2)) = X0
    | k1_zfmisc_1(k2_zfmisc_1(X3,X1)) != k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))
    | k2_relat_1(X0) != k2_relat_1(sK2) ),
    inference(resolution_lifted,[status(thm)],[c_11,c_309])).

cnf(c_403,plain,
    ( ~ v1_relat_1(X0)
    | k5_relat_1(X0,k6_relat_1(X1)) = X0
    | k1_zfmisc_1(k2_zfmisc_1(X2,X1)) != k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))
    | k2_relat_1(X0) != k2_relat_1(sK2) ),
    inference(unflattening,[status(thm)],[c_402])).

cnf(c_642,plain,
    ( k5_relat_1(X0,k6_relat_1(X1)) = X0
    | k1_zfmisc_1(k2_zfmisc_1(X2,X1)) != k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))
    | k2_relat_1(X0) != k2_relat_1(sK2)
    | v1_relat_1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_403])).

cnf(c_1378,plain,
    ( k5_relat_1(X0,k6_relat_1(sK0)) = X0
    | k2_relat_1(X0) != k2_relat_1(sK2)
    | v1_relat_1(X0) != iProver_top ),
    inference(equality_resolution,[status(thm)],[c_642])).

cnf(c_1777,plain,
    ( k5_relat_1(sK2,k6_relat_1(sK0)) = sK2
    | v1_relat_1(sK2) != iProver_top ),
    inference(equality_resolution,[status(thm)],[c_1378])).

cnf(c_491,plain,
    ( X0 = X0 ),
    theory(equality)).

cnf(c_733,plain,
    ( k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)) = k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)) ),
    inference(instantiation,[status(thm)],[c_491])).

cnf(c_365,plain,
    ( v1_relat_1(X0)
    | k1_zfmisc_1(k2_zfmisc_1(X1,X2)) != k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))
    | sK2 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_12,c_20])).

cnf(c_366,plain,
    ( v1_relat_1(sK2)
    | k1_zfmisc_1(k2_zfmisc_1(X0,X1)) != k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)) ),
    inference(unflattening,[status(thm)],[c_365])).

cnf(c_801,plain,
    ( v1_relat_1(sK2)
    | k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)) != k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)) ),
    inference(instantiation,[status(thm)],[c_366])).

cnf(c_802,plain,
    ( k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)) != k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))
    | v1_relat_1(sK2) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_801])).

cnf(c_2005,plain,
    ( k5_relat_1(sK2,k6_relat_1(sK0)) = sK2 ),
    inference(global_propositional_subsumption,[status(thm)],[c_1777,c_733,c_802])).

cnf(c_3,plain,
    ( v1_relat_1(k6_relat_1(X0)) ),
    inference(cnf_transformation,[],[f42])).

cnf(c_648,plain,
    ( v1_relat_1(k6_relat_1(X0)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3])).

cnf(c_643,plain,
    ( k1_zfmisc_1(k2_zfmisc_1(X0,X1)) != k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))
    | v1_relat_1(sK2) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_366])).

cnf(c_1177,plain,
    ( v1_relat_1(sK2) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_643,c_733,c_802])).

cnf(c_7,plain,
    ( ~ v1_relat_1(X0)
    | ~ v1_relat_1(X1)
    | k10_relat_1(X1,k1_relat_1(X0)) = k1_relat_1(k5_relat_1(X1,X0)) ),
    inference(cnf_transformation,[],[f46])).

cnf(c_644,plain,
    ( k10_relat_1(X0,k1_relat_1(X1)) = k1_relat_1(k5_relat_1(X0,X1))
    | v1_relat_1(X1) != iProver_top
    | v1_relat_1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_7])).

cnf(c_1859,plain,
    ( k10_relat_1(sK2,k1_relat_1(X0)) = k1_relat_1(k5_relat_1(sK2,X0))
    | v1_relat_1(X0) != iProver_top ),
    inference(superposition,[status(thm)],[c_1177,c_644])).

cnf(c_1914,plain,
    ( k10_relat_1(sK2,k1_relat_1(k6_relat_1(X0))) = k1_relat_1(k5_relat_1(sK2,k6_relat_1(X0))) ),
    inference(superposition,[status(thm)],[c_648,c_1859])).

cnf(c_10,plain,
    ( k1_relat_1(k6_relat_1(X0)) = X0 ),
    inference(cnf_transformation,[],[f48])).

cnf(c_1919,plain,
    ( k1_relat_1(k5_relat_1(sK2,k6_relat_1(X0))) = k10_relat_1(sK2,X0) ),
    inference(light_normalisation,[status(thm)],[c_1914,c_10])).

cnf(c_2008,plain,
    ( k10_relat_1(sK2,sK0) = k1_relat_1(sK2) ),
    inference(superposition,[status(thm)],[c_2005,c_1919])).

cnf(c_14,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | v4_relat_1(X0,X1) ),
    inference(cnf_transformation,[],[f52])).

cnf(c_8,plain,
    ( ~ v4_relat_1(X0,X1)
    | ~ v1_relat_1(X0)
    | k7_relat_1(X0,X1) = X0 ),
    inference(cnf_transformation,[],[f47])).

cnf(c_230,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ v1_relat_1(X0)
    | k7_relat_1(X0,X1) = X0 ),
    inference(resolution,[status(thm)],[c_14,c_8])).

cnf(c_234,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k7_relat_1(X0,X1) = X0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_230,c_14,c_12,c_8])).

cnf(c_320,plain,
    ( k7_relat_1(X0,X1) = X0
    | k1_zfmisc_1(k2_zfmisc_1(X1,X2)) != k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))
    | sK2 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_234,c_20])).

cnf(c_321,plain,
    ( k7_relat_1(sK2,X0) = sK2
    | k1_zfmisc_1(k2_zfmisc_1(X0,X1)) != k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)) ),
    inference(unflattening,[status(thm)],[c_320])).

cnf(c_732,plain,
    ( k7_relat_1(sK2,sK1) = sK2 ),
    inference(equality_resolution,[status(thm)],[c_321])).

cnf(c_5,plain,
    ( ~ v1_relat_1(X0)
    | k2_relat_1(k7_relat_1(X0,X1)) = k9_relat_1(X0,X1) ),
    inference(cnf_transformation,[],[f44])).

cnf(c_646,plain,
    ( k2_relat_1(k7_relat_1(X0,X1)) = k9_relat_1(X0,X1)
    | v1_relat_1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_5])).

cnf(c_1447,plain,
    ( k2_relat_1(k7_relat_1(sK2,X0)) = k9_relat_1(sK2,X0) ),
    inference(superposition,[status(thm)],[c_1177,c_646])).

cnf(c_1589,plain,
    ( k9_relat_1(sK2,sK1) = k2_relat_1(sK2) ),
    inference(superposition,[status(thm)],[c_732,c_1447])).

cnf(c_15,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k1_relset_1(X1,X2,X0) = k1_relat_1(X0) ),
    inference(cnf_transformation,[],[f54])).

cnf(c_356,plain,
    ( k1_relset_1(X0,X1,X2) = k1_relat_1(X2)
    | k1_zfmisc_1(k2_zfmisc_1(X0,X1)) != k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))
    | sK2 != X2 ),
    inference(resolution_lifted,[status(thm)],[c_15,c_20])).

cnf(c_357,plain,
    ( k1_relset_1(X0,X1,sK2) = k1_relat_1(sK2)
    | k1_zfmisc_1(k2_zfmisc_1(X0,X1)) != k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)) ),
    inference(unflattening,[status(thm)],[c_356])).

cnf(c_744,plain,
    ( k1_relset_1(sK1,sK0,sK2) = k1_relat_1(sK2) ),
    inference(equality_resolution,[status(thm)],[c_357])).

cnf(c_16,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k2_relset_1(X1,X2,X0) = k2_relat_1(X0) ),
    inference(cnf_transformation,[],[f55])).

cnf(c_347,plain,
    ( k2_relset_1(X0,X1,X2) = k2_relat_1(X2)
    | k1_zfmisc_1(k2_zfmisc_1(X0,X1)) != k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))
    | sK2 != X2 ),
    inference(resolution_lifted,[status(thm)],[c_16,c_20])).

cnf(c_348,plain,
    ( k2_relset_1(X0,X1,sK2) = k2_relat_1(sK2)
    | k1_zfmisc_1(k2_zfmisc_1(X0,X1)) != k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)) ),
    inference(unflattening,[status(thm)],[c_347])).

cnf(c_741,plain,
    ( k2_relset_1(sK1,sK0,sK2) = k2_relat_1(sK2) ),
    inference(equality_resolution,[status(thm)],[c_348])).

cnf(c_19,negated_conjecture,
    ( k2_relset_1(sK1,sK0,sK2) != k7_relset_1(sK1,sK0,sK2,k8_relset_1(sK1,sK0,sK2,sK0))
    | k1_relset_1(sK1,sK0,sK2) != k8_relset_1(sK1,sK0,sK2,k7_relset_1(sK1,sK0,sK2,sK1)) ),
    inference(cnf_transformation,[],[f59])).

cnf(c_845,plain,
    ( k8_relset_1(sK1,sK0,sK2,k7_relset_1(sK1,sK0,sK2,sK1)) != k1_relset_1(sK1,sK0,sK2)
    | k7_relset_1(sK1,sK0,sK2,k8_relset_1(sK1,sK0,sK2,sK0)) != k2_relat_1(sK2) ),
    inference(demodulation,[status(thm)],[c_741,c_19])).

cnf(c_1112,plain,
    ( k8_relset_1(sK1,sK0,sK2,k7_relset_1(sK1,sK0,sK2,sK1)) != k1_relat_1(sK2)
    | k7_relset_1(sK1,sK0,sK2,k8_relset_1(sK1,sK0,sK2,sK0)) != k2_relat_1(sK2) ),
    inference(demodulation,[status(thm)],[c_744,c_845])).

cnf(c_18,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k8_relset_1(X1,X2,X0,X3) = k10_relat_1(X0,X3) ),
    inference(cnf_transformation,[],[f57])).

cnf(c_329,plain,
    ( k8_relset_1(X0,X1,X2,X3) = k10_relat_1(X2,X3)
    | k1_zfmisc_1(k2_zfmisc_1(X0,X1)) != k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))
    | sK2 != X2 ),
    inference(resolution_lifted,[status(thm)],[c_18,c_20])).

cnf(c_330,plain,
    ( k8_relset_1(X0,X1,sK2,X2) = k10_relat_1(sK2,X2)
    | k1_zfmisc_1(k2_zfmisc_1(X0,X1)) != k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)) ),
    inference(unflattening,[status(thm)],[c_329])).

cnf(c_782,plain,
    ( k8_relset_1(sK1,sK0,sK2,X0) = k10_relat_1(sK2,X0) ),
    inference(equality_resolution,[status(thm)],[c_330])).

cnf(c_17,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k7_relset_1(X1,X2,X0,X3) = k9_relat_1(X0,X3) ),
    inference(cnf_transformation,[],[f56])).

cnf(c_338,plain,
    ( k7_relset_1(X0,X1,X2,X3) = k9_relat_1(X2,X3)
    | k1_zfmisc_1(k2_zfmisc_1(X0,X1)) != k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))
    | sK2 != X2 ),
    inference(resolution_lifted,[status(thm)],[c_17,c_20])).

cnf(c_339,plain,
    ( k7_relset_1(X0,X1,sK2,X2) = k9_relat_1(sK2,X2)
    | k1_zfmisc_1(k2_zfmisc_1(X0,X1)) != k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)) ),
    inference(unflattening,[status(thm)],[c_338])).

cnf(c_786,plain,
    ( k7_relset_1(sK1,sK0,sK2,X0) = k9_relat_1(sK2,X0) ),
    inference(equality_resolution,[status(thm)],[c_339])).

cnf(c_1276,plain,
    ( k10_relat_1(sK2,k9_relat_1(sK2,sK1)) != k1_relat_1(sK2)
    | k9_relat_1(sK2,k10_relat_1(sK2,sK0)) != k2_relat_1(sK2) ),
    inference(demodulation,[status(thm)],[c_1112,c_782,c_786])).

cnf(c_1591,plain,
    ( k10_relat_1(sK2,k2_relat_1(sK2)) != k1_relat_1(sK2)
    | k9_relat_1(sK2,k10_relat_1(sK2,sK0)) != k2_relat_1(sK2) ),
    inference(demodulation,[status(thm)],[c_1589,c_1276])).

cnf(c_0,plain,
    ( ~ r1_tarski(X0,X1)
    | k3_xboole_0(X0,X1) = X0 ),
    inference(cnf_transformation,[],[f39])).

cnf(c_393,plain,
    ( X0 != X1
    | k3_xboole_0(X2,X1) = X2
    | k1_zfmisc_1(k2_zfmisc_1(X3,X0)) != k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))
    | k2_relat_1(sK2) != X2 ),
    inference(resolution_lifted,[status(thm)],[c_0,c_309])).

cnf(c_394,plain,
    ( k3_xboole_0(k2_relat_1(sK2),X0) = k2_relat_1(sK2)
    | k1_zfmisc_1(k2_zfmisc_1(X1,X0)) != k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)) ),
    inference(unflattening,[status(thm)],[c_393])).

cnf(c_897,plain,
    ( k3_xboole_0(k2_relat_1(sK2),sK0) = k2_relat_1(sK2) ),
    inference(equality_resolution,[status(thm)],[c_394])).

cnf(c_6,plain,
    ( ~ v1_relat_1(X0)
    | k10_relat_1(X0,k3_xboole_0(k2_relat_1(X0),X1)) = k10_relat_1(X0,X1) ),
    inference(cnf_transformation,[],[f45])).

cnf(c_645,plain,
    ( k10_relat_1(X0,k3_xboole_0(k2_relat_1(X0),X1)) = k10_relat_1(X0,X1)
    | v1_relat_1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_6])).

cnf(c_1493,plain,
    ( k10_relat_1(sK2,k3_xboole_0(k2_relat_1(sK2),X0)) = k10_relat_1(sK2,X0) ),
    inference(superposition,[status(thm)],[c_1177,c_645])).

cnf(c_1605,plain,
    ( k10_relat_1(sK2,k2_relat_1(sK2)) = k10_relat_1(sK2,sK0) ),
    inference(superposition,[status(thm)],[c_897,c_1493])).

cnf(c_1718,plain,
    ( k10_relat_1(sK2,sK0) != k1_relat_1(sK2)
    | k9_relat_1(sK2,k10_relat_1(sK2,sK0)) != k2_relat_1(sK2) ),
    inference(light_normalisation,[status(thm)],[c_1591,c_1605])).

cnf(c_2169,plain,
    ( k9_relat_1(sK2,k1_relat_1(sK2)) != k2_relat_1(sK2)
    | k1_relat_1(sK2) != k1_relat_1(sK2) ),
    inference(demodulation,[status(thm)],[c_2008,c_1718])).

cnf(c_2173,plain,
    ( k9_relat_1(sK2,k1_relat_1(sK2)) != k2_relat_1(sK2) ),
    inference(equality_resolution_simp,[status(thm)],[c_2169])).

cnf(c_4,plain,
    ( ~ v1_relat_1(X0)
    | k9_relat_1(X0,k1_relat_1(X0)) = k2_relat_1(X0) ),
    inference(cnf_transformation,[],[f43])).

cnf(c_647,plain,
    ( k9_relat_1(X0,k1_relat_1(X0)) = k2_relat_1(X0)
    | v1_relat_1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_4])).

cnf(c_1182,plain,
    ( k9_relat_1(sK2,k1_relat_1(sK2)) = k2_relat_1(sK2) ),
    inference(superposition,[status(thm)],[c_1177,c_647])).

cnf(c_2175,plain,
    ( k2_relat_1(sK2) != k2_relat_1(sK2) ),
    inference(light_normalisation,[status(thm)],[c_2173,c_1182])).

cnf(c_2176,plain,
    ( $false ),
    inference(equality_resolution_simp,[status(thm)],[c_2175])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : iproveropt_run.sh %d %s
% 0.14/0.34  % Computer   : n018.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % WCLimit    : 600
% 0.14/0.34  % DateTime   : Tue Dec  1 12:32:12 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.34  % Running in FOF mode
% 2.02/0.98  % SZS status Started for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.02/0.98  
% 2.02/0.98  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 2.02/0.98  
% 2.02/0.98  ------  iProver source info
% 2.02/0.98  
% 2.02/0.98  git: date: 2020-06-30 10:37:57 +0100
% 2.02/0.98  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 2.02/0.98  git: non_committed_changes: false
% 2.02/0.98  git: last_make_outside_of_git: false
% 2.02/0.98  
% 2.02/0.98  ------ 
% 2.02/0.98  
% 2.02/0.98  ------ Input Options
% 2.02/0.98  
% 2.02/0.98  --out_options                           all
% 2.02/0.98  --tptp_safe_out                         true
% 2.02/0.98  --problem_path                          ""
% 2.02/0.98  --include_path                          ""
% 2.02/0.98  --clausifier                            res/vclausify_rel
% 2.02/0.98  --clausifier_options                    --mode clausify
% 2.02/0.98  --stdin                                 false
% 2.02/0.98  --stats_out                             all
% 2.02/0.98  
% 2.02/0.98  ------ General Options
% 2.02/0.98  
% 2.02/0.98  --fof                                   false
% 2.02/0.98  --time_out_real                         305.
% 2.02/0.98  --time_out_virtual                      -1.
% 2.02/0.98  --symbol_type_check                     false
% 2.02/0.98  --clausify_out                          false
% 2.02/0.98  --sig_cnt_out                           false
% 2.02/0.98  --trig_cnt_out                          false
% 2.02/0.98  --trig_cnt_out_tolerance                1.
% 2.02/0.98  --trig_cnt_out_sk_spl                   false
% 2.02/0.98  --abstr_cl_out                          false
% 2.02/0.98  
% 2.02/0.98  ------ Global Options
% 2.02/0.98  
% 2.02/0.98  --schedule                              default
% 2.02/0.98  --add_important_lit                     false
% 2.02/0.98  --prop_solver_per_cl                    1000
% 2.02/0.98  --min_unsat_core                        false
% 2.02/0.98  --soft_assumptions                      false
% 2.02/0.98  --soft_lemma_size                       3
% 2.02/0.98  --prop_impl_unit_size                   0
% 2.02/0.98  --prop_impl_unit                        []
% 2.02/0.98  --share_sel_clauses                     true
% 2.02/0.98  --reset_solvers                         false
% 2.02/0.98  --bc_imp_inh                            [conj_cone]
% 2.02/0.98  --conj_cone_tolerance                   3.
% 2.02/0.98  --extra_neg_conj                        none
% 2.02/0.98  --large_theory_mode                     true
% 2.02/0.98  --prolific_symb_bound                   200
% 2.02/0.98  --lt_threshold                          2000
% 2.02/0.98  --clause_weak_htbl                      true
% 2.02/0.98  --gc_record_bc_elim                     false
% 2.02/0.98  
% 2.02/0.98  ------ Preprocessing Options
% 2.02/0.98  
% 2.02/0.98  --preprocessing_flag                    true
% 2.02/0.98  --time_out_prep_mult                    0.1
% 2.02/0.98  --splitting_mode                        input
% 2.02/0.98  --splitting_grd                         true
% 2.02/0.98  --splitting_cvd                         false
% 2.02/0.98  --splitting_cvd_svl                     false
% 2.02/0.98  --splitting_nvd                         32
% 2.02/0.98  --sub_typing                            true
% 2.02/0.98  --prep_gs_sim                           true
% 2.02/0.98  --prep_unflatten                        true
% 2.02/0.98  --prep_res_sim                          true
% 2.02/0.98  --prep_upred                            true
% 2.02/0.98  --prep_sem_filter                       exhaustive
% 2.02/0.98  --prep_sem_filter_out                   false
% 2.02/0.98  --pred_elim                             true
% 2.02/0.98  --res_sim_input                         true
% 2.02/0.98  --eq_ax_congr_red                       true
% 2.02/0.98  --pure_diseq_elim                       true
% 2.02/0.98  --brand_transform                       false
% 2.02/0.98  --non_eq_to_eq                          false
% 2.02/0.98  --prep_def_merge                        true
% 2.02/0.98  --prep_def_merge_prop_impl              false
% 2.02/0.98  --prep_def_merge_mbd                    true
% 2.02/0.98  --prep_def_merge_tr_red                 false
% 2.02/0.98  --prep_def_merge_tr_cl                  false
% 2.02/0.98  --smt_preprocessing                     true
% 2.02/0.98  --smt_ac_axioms                         fast
% 2.02/0.98  --preprocessed_out                      false
% 2.02/0.98  --preprocessed_stats                    false
% 2.02/0.98  
% 2.02/0.98  ------ Abstraction refinement Options
% 2.02/0.98  
% 2.02/0.98  --abstr_ref                             []
% 2.02/0.98  --abstr_ref_prep                        false
% 2.02/0.98  --abstr_ref_until_sat                   false
% 2.02/0.98  --abstr_ref_sig_restrict                funpre
% 2.02/0.98  --abstr_ref_af_restrict_to_split_sk     false
% 2.02/0.98  --abstr_ref_under                       []
% 2.02/0.98  
% 2.02/0.98  ------ SAT Options
% 2.02/0.98  
% 2.02/0.98  --sat_mode                              false
% 2.02/0.98  --sat_fm_restart_options                ""
% 2.02/0.98  --sat_gr_def                            false
% 2.02/0.98  --sat_epr_types                         true
% 2.02/0.98  --sat_non_cyclic_types                  false
% 2.02/0.98  --sat_finite_models                     false
% 2.02/0.98  --sat_fm_lemmas                         false
% 2.02/0.98  --sat_fm_prep                           false
% 2.02/0.98  --sat_fm_uc_incr                        true
% 2.02/0.98  --sat_out_model                         small
% 2.02/0.98  --sat_out_clauses                       false
% 2.02/0.98  
% 2.02/0.98  ------ QBF Options
% 2.02/0.98  
% 2.02/0.98  --qbf_mode                              false
% 2.02/0.98  --qbf_elim_univ                         false
% 2.02/0.98  --qbf_dom_inst                          none
% 2.02/0.98  --qbf_dom_pre_inst                      false
% 2.02/0.98  --qbf_sk_in                             false
% 2.02/0.98  --qbf_pred_elim                         true
% 2.02/0.98  --qbf_split                             512
% 2.02/0.98  
% 2.02/0.98  ------ BMC1 Options
% 2.02/0.98  
% 2.02/0.98  --bmc1_incremental                      false
% 2.02/0.98  --bmc1_axioms                           reachable_all
% 2.02/0.98  --bmc1_min_bound                        0
% 2.02/0.98  --bmc1_max_bound                        -1
% 2.02/0.98  --bmc1_max_bound_default                -1
% 2.02/0.98  --bmc1_symbol_reachability              true
% 2.02/0.98  --bmc1_property_lemmas                  false
% 2.02/0.98  --bmc1_k_induction                      false
% 2.02/0.98  --bmc1_non_equiv_states                 false
% 2.02/0.98  --bmc1_deadlock                         false
% 2.02/0.98  --bmc1_ucm                              false
% 2.02/0.98  --bmc1_add_unsat_core                   none
% 2.02/0.98  --bmc1_unsat_core_children              false
% 2.02/0.98  --bmc1_unsat_core_extrapolate_axioms    false
% 2.02/0.98  --bmc1_out_stat                         full
% 2.02/0.98  --bmc1_ground_init                      false
% 2.02/0.98  --bmc1_pre_inst_next_state              false
% 2.02/0.98  --bmc1_pre_inst_state                   false
% 2.02/0.98  --bmc1_pre_inst_reach_state             false
% 2.02/0.98  --bmc1_out_unsat_core                   false
% 2.02/0.98  --bmc1_aig_witness_out                  false
% 2.02/0.98  --bmc1_verbose                          false
% 2.02/0.98  --bmc1_dump_clauses_tptp                false
% 2.02/0.98  --bmc1_dump_unsat_core_tptp             false
% 2.02/0.98  --bmc1_dump_file                        -
% 2.02/0.98  --bmc1_ucm_expand_uc_limit              128
% 2.02/0.98  --bmc1_ucm_n_expand_iterations          6
% 2.02/0.98  --bmc1_ucm_extend_mode                  1
% 2.02/0.98  --bmc1_ucm_init_mode                    2
% 2.02/0.98  --bmc1_ucm_cone_mode                    none
% 2.02/0.98  --bmc1_ucm_reduced_relation_type        0
% 2.02/0.98  --bmc1_ucm_relax_model                  4
% 2.02/0.98  --bmc1_ucm_full_tr_after_sat            true
% 2.02/0.98  --bmc1_ucm_expand_neg_assumptions       false
% 2.02/0.98  --bmc1_ucm_layered_model                none
% 2.02/0.98  --bmc1_ucm_max_lemma_size               10
% 2.02/0.98  
% 2.02/0.98  ------ AIG Options
% 2.02/0.98  
% 2.02/0.98  --aig_mode                              false
% 2.02/0.98  
% 2.02/0.98  ------ Instantiation Options
% 2.02/0.98  
% 2.02/0.98  --instantiation_flag                    true
% 2.02/0.98  --inst_sos_flag                         false
% 2.02/0.98  --inst_sos_phase                        true
% 2.02/0.98  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 2.02/0.98  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 2.02/0.98  --inst_lit_sel_side                     num_symb
% 2.02/0.98  --inst_solver_per_active                1400
% 2.02/0.98  --inst_solver_calls_frac                1.
% 2.02/0.98  --inst_passive_queue_type               priority_queues
% 2.02/0.98  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 2.02/0.98  --inst_passive_queues_freq              [25;2]
% 2.02/0.98  --inst_dismatching                      true
% 2.02/0.98  --inst_eager_unprocessed_to_passive     true
% 2.02/0.98  --inst_prop_sim_given                   true
% 2.02/0.98  --inst_prop_sim_new                     false
% 2.02/0.98  --inst_subs_new                         false
% 2.02/0.98  --inst_eq_res_simp                      false
% 2.02/0.98  --inst_subs_given                       false
% 2.02/0.98  --inst_orphan_elimination               true
% 2.02/0.98  --inst_learning_loop_flag               true
% 2.02/0.98  --inst_learning_start                   3000
% 2.02/0.98  --inst_learning_factor                  2
% 2.02/0.98  --inst_start_prop_sim_after_learn       3
% 2.02/0.98  --inst_sel_renew                        solver
% 2.02/0.98  --inst_lit_activity_flag                true
% 2.02/0.98  --inst_restr_to_given                   false
% 2.02/0.98  --inst_activity_threshold               500
% 2.02/0.98  --inst_out_proof                        true
% 2.02/0.98  
% 2.02/0.98  ------ Resolution Options
% 2.02/0.98  
% 2.02/0.98  --resolution_flag                       true
% 2.02/0.98  --res_lit_sel                           adaptive
% 2.02/0.98  --res_lit_sel_side                      none
% 2.02/0.98  --res_ordering                          kbo
% 2.02/0.98  --res_to_prop_solver                    active
% 2.02/0.98  --res_prop_simpl_new                    false
% 2.02/0.98  --res_prop_simpl_given                  true
% 2.02/0.98  --res_passive_queue_type                priority_queues
% 2.02/0.98  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 2.02/0.98  --res_passive_queues_freq               [15;5]
% 2.02/0.98  --res_forward_subs                      full
% 2.02/0.98  --res_backward_subs                     full
% 2.02/0.98  --res_forward_subs_resolution           true
% 2.02/0.98  --res_backward_subs_resolution          true
% 2.02/0.98  --res_orphan_elimination                true
% 2.02/0.98  --res_time_limit                        2.
% 2.02/0.98  --res_out_proof                         true
% 2.02/0.98  
% 2.02/0.98  ------ Superposition Options
% 2.02/0.98  
% 2.02/0.98  --superposition_flag                    true
% 2.02/0.98  --sup_passive_queue_type                priority_queues
% 2.02/0.98  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 2.02/0.98  --sup_passive_queues_freq               [8;1;4]
% 2.02/0.98  --demod_completeness_check              fast
% 2.02/0.98  --demod_use_ground                      true
% 2.02/0.98  --sup_to_prop_solver                    passive
% 2.02/0.98  --sup_prop_simpl_new                    true
% 2.02/0.98  --sup_prop_simpl_given                  true
% 2.02/0.98  --sup_fun_splitting                     false
% 2.02/0.98  --sup_smt_interval                      50000
% 2.02/0.98  
% 2.02/0.98  ------ Superposition Simplification Setup
% 2.02/0.98  
% 2.02/0.98  --sup_indices_passive                   []
% 2.02/0.98  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.02/0.98  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.02/0.98  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.02/0.98  --sup_full_triv                         [TrivRules;PropSubs]
% 2.02/0.98  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.02/0.98  --sup_full_bw                           [BwDemod]
% 2.02/0.98  --sup_immed_triv                        [TrivRules]
% 2.02/0.98  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 2.02/0.98  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.02/0.98  --sup_immed_bw_main                     []
% 2.02/0.98  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.02/0.98  --sup_input_triv                        [Unflattening;TrivRules]
% 2.02/0.98  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.02/0.98  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.02/0.98  
% 2.02/0.98  ------ Combination Options
% 2.02/0.98  
% 2.02/0.98  --comb_res_mult                         3
% 2.02/0.98  --comb_sup_mult                         2
% 2.02/0.98  --comb_inst_mult                        10
% 2.02/0.98  
% 2.02/0.98  ------ Debug Options
% 2.02/0.98  
% 2.02/0.98  --dbg_backtrace                         false
% 2.02/0.98  --dbg_dump_prop_clauses                 false
% 2.02/0.98  --dbg_dump_prop_clauses_file            -
% 2.02/0.98  --dbg_out_stat                          false
% 2.02/0.98  ------ Parsing...
% 2.02/0.98  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 2.02/0.98  
% 2.02/0.98  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe:1:0s pe:2:0s pe:4:0s pe_e  sf_s  rm: 3 0s  sf_e  pe_s  pe_e 
% 2.02/0.98  
% 2.02/0.98  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 2.02/0.98  
% 2.02/0.98  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 2.02/0.98  ------ Proving...
% 2.02/0.98  ------ Problem Properties 
% 2.02/0.98  
% 2.02/0.98  
% 2.02/0.98  clauses                                 16
% 2.02/0.98  conjectures                             1
% 2.02/0.98  EPR                                     0
% 2.02/0.98  Horn                                    16
% 2.02/0.98  unary                                   3
% 2.02/0.98  binary                                  11
% 2.02/0.98  lits                                    32
% 2.02/0.98  lits eq                                 24
% 2.02/0.98  fd_pure                                 0
% 2.02/0.98  fd_pseudo                               0
% 2.02/0.98  fd_cond                                 0
% 2.02/0.98  fd_pseudo_cond                          0
% 2.02/0.98  AC symbols                              0
% 2.02/0.98  
% 2.02/0.98  ------ Schedule dynamic 5 is on 
% 2.02/0.98  
% 2.02/0.98  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" Time Limit: 10.
% 2.02/0.98  
% 2.02/0.98  
% 2.02/0.98  ------ 
% 2.02/0.98  Current options:
% 2.02/0.98  ------ 
% 2.02/0.98  
% 2.02/0.98  ------ Input Options
% 2.02/0.98  
% 2.02/0.98  --out_options                           all
% 2.02/0.98  --tptp_safe_out                         true
% 2.02/0.98  --problem_path                          ""
% 2.02/0.98  --include_path                          ""
% 2.02/0.98  --clausifier                            res/vclausify_rel
% 2.02/0.98  --clausifier_options                    --mode clausify
% 2.02/0.98  --stdin                                 false
% 2.02/0.98  --stats_out                             all
% 2.02/0.98  
% 2.02/0.98  ------ General Options
% 2.02/0.98  
% 2.02/0.98  --fof                                   false
% 2.02/0.98  --time_out_real                         305.
% 2.02/0.98  --time_out_virtual                      -1.
% 2.02/0.98  --symbol_type_check                     false
% 2.02/0.98  --clausify_out                          false
% 2.02/0.98  --sig_cnt_out                           false
% 2.02/0.98  --trig_cnt_out                          false
% 2.02/0.98  --trig_cnt_out_tolerance                1.
% 2.02/0.98  --trig_cnt_out_sk_spl                   false
% 2.02/0.98  --abstr_cl_out                          false
% 2.02/0.98  
% 2.02/0.98  ------ Global Options
% 2.02/0.98  
% 2.02/0.98  --schedule                              default
% 2.02/0.98  --add_important_lit                     false
% 2.02/0.98  --prop_solver_per_cl                    1000
% 2.02/0.98  --min_unsat_core                        false
% 2.02/0.98  --soft_assumptions                      false
% 2.02/0.98  --soft_lemma_size                       3
% 2.02/0.98  --prop_impl_unit_size                   0
% 2.02/0.98  --prop_impl_unit                        []
% 2.02/0.98  --share_sel_clauses                     true
% 2.02/0.98  --reset_solvers                         false
% 2.02/0.98  --bc_imp_inh                            [conj_cone]
% 2.02/0.98  --conj_cone_tolerance                   3.
% 2.02/0.98  --extra_neg_conj                        none
% 2.02/0.98  --large_theory_mode                     true
% 2.02/0.98  --prolific_symb_bound                   200
% 2.02/0.98  --lt_threshold                          2000
% 2.02/0.98  --clause_weak_htbl                      true
% 2.02/0.98  --gc_record_bc_elim                     false
% 2.02/0.98  
% 2.02/0.98  ------ Preprocessing Options
% 2.02/0.98  
% 2.02/0.98  --preprocessing_flag                    true
% 2.02/0.98  --time_out_prep_mult                    0.1
% 2.02/0.98  --splitting_mode                        input
% 2.02/0.98  --splitting_grd                         true
% 2.02/0.98  --splitting_cvd                         false
% 2.02/0.98  --splitting_cvd_svl                     false
% 2.02/0.98  --splitting_nvd                         32
% 2.02/0.98  --sub_typing                            true
% 2.02/0.98  --prep_gs_sim                           true
% 2.02/0.98  --prep_unflatten                        true
% 2.02/0.98  --prep_res_sim                          true
% 2.02/0.98  --prep_upred                            true
% 2.02/0.98  --prep_sem_filter                       exhaustive
% 2.02/0.98  --prep_sem_filter_out                   false
% 2.02/0.98  --pred_elim                             true
% 2.02/0.98  --res_sim_input                         true
% 2.02/0.98  --eq_ax_congr_red                       true
% 2.02/0.98  --pure_diseq_elim                       true
% 2.02/0.98  --brand_transform                       false
% 2.02/0.98  --non_eq_to_eq                          false
% 2.02/0.98  --prep_def_merge                        true
% 2.02/0.98  --prep_def_merge_prop_impl              false
% 2.02/0.98  --prep_def_merge_mbd                    true
% 2.02/0.98  --prep_def_merge_tr_red                 false
% 2.02/0.98  --prep_def_merge_tr_cl                  false
% 2.02/0.98  --smt_preprocessing                     true
% 2.02/0.98  --smt_ac_axioms                         fast
% 2.02/0.98  --preprocessed_out                      false
% 2.02/0.98  --preprocessed_stats                    false
% 2.02/0.98  
% 2.02/0.98  ------ Abstraction refinement Options
% 2.02/0.98  
% 2.02/0.98  --abstr_ref                             []
% 2.02/0.98  --abstr_ref_prep                        false
% 2.02/0.98  --abstr_ref_until_sat                   false
% 2.02/0.98  --abstr_ref_sig_restrict                funpre
% 2.02/0.98  --abstr_ref_af_restrict_to_split_sk     false
% 2.02/0.98  --abstr_ref_under                       []
% 2.02/0.98  
% 2.02/0.98  ------ SAT Options
% 2.02/0.98  
% 2.02/0.98  --sat_mode                              false
% 2.02/0.98  --sat_fm_restart_options                ""
% 2.02/0.98  --sat_gr_def                            false
% 2.02/0.98  --sat_epr_types                         true
% 2.02/0.98  --sat_non_cyclic_types                  false
% 2.02/0.98  --sat_finite_models                     false
% 2.02/0.98  --sat_fm_lemmas                         false
% 2.02/0.98  --sat_fm_prep                           false
% 2.02/0.98  --sat_fm_uc_incr                        true
% 2.02/0.98  --sat_out_model                         small
% 2.02/0.98  --sat_out_clauses                       false
% 2.02/0.98  
% 2.02/0.98  ------ QBF Options
% 2.02/0.98  
% 2.02/0.98  --qbf_mode                              false
% 2.02/0.98  --qbf_elim_univ                         false
% 2.02/0.98  --qbf_dom_inst                          none
% 2.02/0.98  --qbf_dom_pre_inst                      false
% 2.02/0.98  --qbf_sk_in                             false
% 2.02/0.98  --qbf_pred_elim                         true
% 2.02/0.98  --qbf_split                             512
% 2.02/0.98  
% 2.02/0.98  ------ BMC1 Options
% 2.02/0.98  
% 2.02/0.98  --bmc1_incremental                      false
% 2.02/0.98  --bmc1_axioms                           reachable_all
% 2.02/0.98  --bmc1_min_bound                        0
% 2.02/0.98  --bmc1_max_bound                        -1
% 2.02/0.98  --bmc1_max_bound_default                -1
% 2.02/0.98  --bmc1_symbol_reachability              true
% 2.02/0.98  --bmc1_property_lemmas                  false
% 2.02/0.98  --bmc1_k_induction                      false
% 2.02/0.98  --bmc1_non_equiv_states                 false
% 2.02/0.98  --bmc1_deadlock                         false
% 2.02/0.98  --bmc1_ucm                              false
% 2.02/0.98  --bmc1_add_unsat_core                   none
% 2.02/0.98  --bmc1_unsat_core_children              false
% 2.02/0.98  --bmc1_unsat_core_extrapolate_axioms    false
% 2.02/0.98  --bmc1_out_stat                         full
% 2.02/0.98  --bmc1_ground_init                      false
% 2.02/0.98  --bmc1_pre_inst_next_state              false
% 2.02/0.98  --bmc1_pre_inst_state                   false
% 2.02/0.98  --bmc1_pre_inst_reach_state             false
% 2.02/0.98  --bmc1_out_unsat_core                   false
% 2.02/0.98  --bmc1_aig_witness_out                  false
% 2.02/0.98  --bmc1_verbose                          false
% 2.02/0.98  --bmc1_dump_clauses_tptp                false
% 2.02/0.98  --bmc1_dump_unsat_core_tptp             false
% 2.02/0.98  --bmc1_dump_file                        -
% 2.02/0.98  --bmc1_ucm_expand_uc_limit              128
% 2.02/0.98  --bmc1_ucm_n_expand_iterations          6
% 2.02/0.98  --bmc1_ucm_extend_mode                  1
% 2.02/0.98  --bmc1_ucm_init_mode                    2
% 2.02/0.98  --bmc1_ucm_cone_mode                    none
% 2.02/0.98  --bmc1_ucm_reduced_relation_type        0
% 2.02/0.98  --bmc1_ucm_relax_model                  4
% 2.02/0.98  --bmc1_ucm_full_tr_after_sat            true
% 2.02/0.98  --bmc1_ucm_expand_neg_assumptions       false
% 2.02/0.98  --bmc1_ucm_layered_model                none
% 2.02/0.98  --bmc1_ucm_max_lemma_size               10
% 2.02/0.98  
% 2.02/0.98  ------ AIG Options
% 2.02/0.98  
% 2.02/0.98  --aig_mode                              false
% 2.02/0.98  
% 2.02/0.98  ------ Instantiation Options
% 2.02/0.98  
% 2.02/0.98  --instantiation_flag                    true
% 2.02/0.98  --inst_sos_flag                         false
% 2.02/0.98  --inst_sos_phase                        true
% 2.02/0.98  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 2.02/0.98  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 2.02/0.98  --inst_lit_sel_side                     none
% 2.02/0.98  --inst_solver_per_active                1400
% 2.02/0.98  --inst_solver_calls_frac                1.
% 2.02/0.98  --inst_passive_queue_type               priority_queues
% 2.02/0.98  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 2.02/0.98  --inst_passive_queues_freq              [25;2]
% 2.02/0.98  --inst_dismatching                      true
% 2.02/0.98  --inst_eager_unprocessed_to_passive     true
% 2.02/0.98  --inst_prop_sim_given                   true
% 2.02/0.98  --inst_prop_sim_new                     false
% 2.02/0.98  --inst_subs_new                         false
% 2.02/0.98  --inst_eq_res_simp                      false
% 2.02/0.98  --inst_subs_given                       false
% 2.02/0.98  --inst_orphan_elimination               true
% 2.02/0.98  --inst_learning_loop_flag               true
% 2.02/0.98  --inst_learning_start                   3000
% 2.02/0.98  --inst_learning_factor                  2
% 2.02/0.98  --inst_start_prop_sim_after_learn       3
% 2.02/0.98  --inst_sel_renew                        solver
% 2.02/0.98  --inst_lit_activity_flag                true
% 2.02/0.98  --inst_restr_to_given                   false
% 2.02/0.98  --inst_activity_threshold               500
% 2.02/0.98  --inst_out_proof                        true
% 2.02/0.98  
% 2.02/0.98  ------ Resolution Options
% 2.02/0.98  
% 2.02/0.98  --resolution_flag                       false
% 2.02/0.98  --res_lit_sel                           adaptive
% 2.02/0.98  --res_lit_sel_side                      none
% 2.02/0.98  --res_ordering                          kbo
% 2.02/0.98  --res_to_prop_solver                    active
% 2.02/0.98  --res_prop_simpl_new                    false
% 2.02/0.98  --res_prop_simpl_given                  true
% 2.02/0.98  --res_passive_queue_type                priority_queues
% 2.02/0.98  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 2.02/0.98  --res_passive_queues_freq               [15;5]
% 2.02/0.98  --res_forward_subs                      full
% 2.02/0.98  --res_backward_subs                     full
% 2.02/0.98  --res_forward_subs_resolution           true
% 2.02/0.98  --res_backward_subs_resolution          true
% 2.02/0.98  --res_orphan_elimination                true
% 2.02/0.98  --res_time_limit                        2.
% 2.02/0.98  --res_out_proof                         true
% 2.02/0.98  
% 2.02/0.98  ------ Superposition Options
% 2.02/0.98  
% 2.02/0.98  --superposition_flag                    true
% 2.02/0.98  --sup_passive_queue_type                priority_queues
% 2.02/0.98  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 2.02/0.98  --sup_passive_queues_freq               [8;1;4]
% 2.02/0.98  --demod_completeness_check              fast
% 2.02/0.98  --demod_use_ground                      true
% 2.02/0.98  --sup_to_prop_solver                    passive
% 2.02/0.98  --sup_prop_simpl_new                    true
% 2.02/0.98  --sup_prop_simpl_given                  true
% 2.02/0.98  --sup_fun_splitting                     false
% 2.02/0.98  --sup_smt_interval                      50000
% 2.02/0.98  
% 2.02/0.98  ------ Superposition Simplification Setup
% 2.02/0.98  
% 2.02/0.98  --sup_indices_passive                   []
% 2.02/0.98  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.02/0.98  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.02/0.98  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.02/0.98  --sup_full_triv                         [TrivRules;PropSubs]
% 2.02/0.98  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.02/0.98  --sup_full_bw                           [BwDemod]
% 2.02/0.98  --sup_immed_triv                        [TrivRules]
% 2.02/0.98  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 2.02/0.98  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.02/0.98  --sup_immed_bw_main                     []
% 2.02/0.98  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.02/0.98  --sup_input_triv                        [Unflattening;TrivRules]
% 2.02/0.98  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.02/0.98  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.02/0.98  
% 2.02/0.98  ------ Combination Options
% 2.02/0.98  
% 2.02/0.98  --comb_res_mult                         3
% 2.02/0.98  --comb_sup_mult                         2
% 2.02/0.98  --comb_inst_mult                        10
% 2.02/0.98  
% 2.02/0.98  ------ Debug Options
% 2.02/0.98  
% 2.02/0.98  --dbg_backtrace                         false
% 2.02/0.98  --dbg_dump_prop_clauses                 false
% 2.02/0.98  --dbg_dump_prop_clauses_file            -
% 2.02/0.98  --dbg_out_stat                          false
% 2.02/0.98  
% 2.02/0.98  
% 2.02/0.98  
% 2.02/0.98  
% 2.02/0.98  ------ Proving...
% 2.02/0.98  
% 2.02/0.98  
% 2.02/0.98  % SZS status Theorem for theBenchmark.p
% 2.02/0.98  
% 2.02/0.98   Resolution empty clause
% 2.02/0.98  
% 2.02/0.98  % SZS output start CNFRefutation for theBenchmark.p
% 2.02/0.98  
% 2.02/0.98  fof(f10,axiom,(
% 2.02/0.98    ! [X0,X1] : (v1_relat_1(X1) => (r1_tarski(k2_relat_1(X1),X0) => k5_relat_1(X1,k6_relat_1(X0)) = X1))),
% 2.02/0.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.02/0.98  
% 2.02/0.98  fof(f27,plain,(
% 2.02/0.98    ! [X0,X1] : ((k5_relat_1(X1,k6_relat_1(X0)) = X1 | ~r1_tarski(k2_relat_1(X1),X0)) | ~v1_relat_1(X1))),
% 2.02/0.98    inference(ennf_transformation,[],[f10])).
% 2.02/0.98  
% 2.02/0.98  fof(f28,plain,(
% 2.02/0.98    ! [X0,X1] : (k5_relat_1(X1,k6_relat_1(X0)) = X1 | ~r1_tarski(k2_relat_1(X1),X0) | ~v1_relat_1(X1))),
% 2.02/0.98    inference(flattening,[],[f27])).
% 2.02/0.98  
% 2.02/0.98  fof(f50,plain,(
% 2.02/0.98    ( ! [X0,X1] : (k5_relat_1(X1,k6_relat_1(X0)) = X1 | ~r1_tarski(k2_relat_1(X1),X0) | ~v1_relat_1(X1)) )),
% 2.02/0.98    inference(cnf_transformation,[],[f28])).
% 2.02/0.98  
% 2.02/0.98  fof(f2,axiom,(
% 2.02/0.98    ! [X0,X1] : (v1_relat_1(X1) => (v5_relat_1(X1,X0) <=> r1_tarski(k2_relat_1(X1),X0)))),
% 2.02/0.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.02/0.98  
% 2.02/0.98  fof(f20,plain,(
% 2.02/0.98    ! [X0,X1] : ((v5_relat_1(X1,X0) <=> r1_tarski(k2_relat_1(X1),X0)) | ~v1_relat_1(X1))),
% 2.02/0.98    inference(ennf_transformation,[],[f2])).
% 2.02/0.98  
% 2.02/0.98  fof(f36,plain,(
% 2.02/0.98    ! [X0,X1] : (((v5_relat_1(X1,X0) | ~r1_tarski(k2_relat_1(X1),X0)) & (r1_tarski(k2_relat_1(X1),X0) | ~v5_relat_1(X1,X0))) | ~v1_relat_1(X1))),
% 2.02/0.98    inference(nnf_transformation,[],[f20])).
% 2.02/0.98  
% 2.02/0.98  fof(f40,plain,(
% 2.02/0.98    ( ! [X0,X1] : (r1_tarski(k2_relat_1(X1),X0) | ~v5_relat_1(X1,X0) | ~v1_relat_1(X1)) )),
% 2.02/0.98    inference(cnf_transformation,[],[f36])).
% 2.02/0.98  
% 2.02/0.98  fof(f12,axiom,(
% 2.02/0.98    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => (v5_relat_1(X2,X1) & v4_relat_1(X2,X0)))),
% 2.02/0.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.02/0.98  
% 2.02/0.98  fof(f30,plain,(
% 2.02/0.98    ! [X0,X1,X2] : ((v5_relat_1(X2,X1) & v4_relat_1(X2,X0)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 2.02/0.98    inference(ennf_transformation,[],[f12])).
% 2.02/0.98  
% 2.02/0.98  fof(f53,plain,(
% 2.02/0.98    ( ! [X2,X0,X1] : (v5_relat_1(X2,X1) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 2.02/0.98    inference(cnf_transformation,[],[f30])).
% 2.02/0.98  
% 2.02/0.98  fof(f11,axiom,(
% 2.02/0.98    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => v1_relat_1(X2))),
% 2.02/0.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.02/0.98  
% 2.02/0.98  fof(f29,plain,(
% 2.02/0.98    ! [X0,X1,X2] : (v1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 2.02/0.98    inference(ennf_transformation,[],[f11])).
% 2.02/0.98  
% 2.02/0.98  fof(f51,plain,(
% 2.02/0.98    ( ! [X2,X0,X1] : (v1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 2.02/0.98    inference(cnf_transformation,[],[f29])).
% 2.02/0.98  
% 2.02/0.98  fof(f17,conjecture,(
% 2.02/0.98    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) => (k1_relset_1(X1,X0,X2) = k8_relset_1(X1,X0,X2,k7_relset_1(X1,X0,X2,X1)) & k2_relset_1(X1,X0,X2) = k7_relset_1(X1,X0,X2,k8_relset_1(X1,X0,X2,X0))))),
% 2.02/0.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.02/0.98  
% 2.02/0.98  fof(f18,negated_conjecture,(
% 2.02/0.98    ~! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) => (k1_relset_1(X1,X0,X2) = k8_relset_1(X1,X0,X2,k7_relset_1(X1,X0,X2,X1)) & k2_relset_1(X1,X0,X2) = k7_relset_1(X1,X0,X2,k8_relset_1(X1,X0,X2,X0))))),
% 2.02/0.98    inference(negated_conjecture,[],[f17])).
% 2.02/0.98  
% 2.02/0.98  fof(f35,plain,(
% 2.02/0.98    ? [X0,X1,X2] : ((k1_relset_1(X1,X0,X2) != k8_relset_1(X1,X0,X2,k7_relset_1(X1,X0,X2,X1)) | k2_relset_1(X1,X0,X2) != k7_relset_1(X1,X0,X2,k8_relset_1(X1,X0,X2,X0))) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X0))))),
% 2.02/0.98    inference(ennf_transformation,[],[f18])).
% 2.02/0.98  
% 2.02/0.98  fof(f37,plain,(
% 2.02/0.98    ? [X0,X1,X2] : ((k1_relset_1(X1,X0,X2) != k8_relset_1(X1,X0,X2,k7_relset_1(X1,X0,X2,X1)) | k2_relset_1(X1,X0,X2) != k7_relset_1(X1,X0,X2,k8_relset_1(X1,X0,X2,X0))) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X0)))) => ((k1_relset_1(sK1,sK0,sK2) != k8_relset_1(sK1,sK0,sK2,k7_relset_1(sK1,sK0,sK2,sK1)) | k2_relset_1(sK1,sK0,sK2) != k7_relset_1(sK1,sK0,sK2,k8_relset_1(sK1,sK0,sK2,sK0))) & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))))),
% 2.02/0.98    introduced(choice_axiom,[])).
% 2.02/0.98  
% 2.02/0.98  fof(f38,plain,(
% 2.02/0.98    (k1_relset_1(sK1,sK0,sK2) != k8_relset_1(sK1,sK0,sK2,k7_relset_1(sK1,sK0,sK2,sK1)) | k2_relset_1(sK1,sK0,sK2) != k7_relset_1(sK1,sK0,sK2,k8_relset_1(sK1,sK0,sK2,sK0))) & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))),
% 2.02/0.98    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f35,f37])).
% 2.02/0.98  
% 2.02/0.98  fof(f58,plain,(
% 2.02/0.98    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))),
% 2.02/0.98    inference(cnf_transformation,[],[f38])).
% 2.02/0.98  
% 2.02/0.98  fof(f3,axiom,(
% 2.02/0.98    ! [X0] : v1_relat_1(k6_relat_1(X0))),
% 2.02/0.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.02/0.98  
% 2.02/0.98  fof(f42,plain,(
% 2.02/0.98    ( ! [X0] : (v1_relat_1(k6_relat_1(X0))) )),
% 2.02/0.98    inference(cnf_transformation,[],[f3])).
% 2.02/0.98  
% 2.02/0.98  fof(f7,axiom,(
% 2.02/0.98    ! [X0] : (v1_relat_1(X0) => ! [X1] : (v1_relat_1(X1) => k1_relat_1(k5_relat_1(X0,X1)) = k10_relat_1(X0,k1_relat_1(X1))))),
% 2.02/0.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.02/0.98  
% 2.02/0.98  fof(f24,plain,(
% 2.02/0.98    ! [X0] : (! [X1] : (k1_relat_1(k5_relat_1(X0,X1)) = k10_relat_1(X0,k1_relat_1(X1)) | ~v1_relat_1(X1)) | ~v1_relat_1(X0))),
% 2.02/0.98    inference(ennf_transformation,[],[f7])).
% 2.02/0.98  
% 2.02/0.98  fof(f46,plain,(
% 2.02/0.98    ( ! [X0,X1] : (k1_relat_1(k5_relat_1(X0,X1)) = k10_relat_1(X0,k1_relat_1(X1)) | ~v1_relat_1(X1) | ~v1_relat_1(X0)) )),
% 2.02/0.98    inference(cnf_transformation,[],[f24])).
% 2.02/0.98  
% 2.02/0.98  fof(f9,axiom,(
% 2.02/0.98    ! [X0] : (k2_relat_1(k6_relat_1(X0)) = X0 & k1_relat_1(k6_relat_1(X0)) = X0)),
% 2.02/0.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.02/0.98  
% 2.02/0.98  fof(f48,plain,(
% 2.02/0.98    ( ! [X0] : (k1_relat_1(k6_relat_1(X0)) = X0) )),
% 2.02/0.98    inference(cnf_transformation,[],[f9])).
% 2.02/0.98  
% 2.02/0.98  fof(f52,plain,(
% 2.02/0.98    ( ! [X2,X0,X1] : (v4_relat_1(X2,X0) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 2.02/0.98    inference(cnf_transformation,[],[f30])).
% 2.02/0.98  
% 2.02/0.98  fof(f8,axiom,(
% 2.02/0.98    ! [X0,X1] : ((v4_relat_1(X1,X0) & v1_relat_1(X1)) => k7_relat_1(X1,X0) = X1)),
% 2.02/0.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.02/0.98  
% 2.02/0.98  fof(f25,plain,(
% 2.02/0.98    ! [X0,X1] : (k7_relat_1(X1,X0) = X1 | (~v4_relat_1(X1,X0) | ~v1_relat_1(X1)))),
% 2.02/0.98    inference(ennf_transformation,[],[f8])).
% 2.02/0.98  
% 2.02/0.98  fof(f26,plain,(
% 2.02/0.98    ! [X0,X1] : (k7_relat_1(X1,X0) = X1 | ~v4_relat_1(X1,X0) | ~v1_relat_1(X1))),
% 2.02/0.98    inference(flattening,[],[f25])).
% 2.02/0.98  
% 2.02/0.98  fof(f47,plain,(
% 2.02/0.98    ( ! [X0,X1] : (k7_relat_1(X1,X0) = X1 | ~v4_relat_1(X1,X0) | ~v1_relat_1(X1)) )),
% 2.02/0.98    inference(cnf_transformation,[],[f26])).
% 2.02/0.98  
% 2.02/0.98  fof(f5,axiom,(
% 2.02/0.98    ! [X0,X1] : (v1_relat_1(X1) => k2_relat_1(k7_relat_1(X1,X0)) = k9_relat_1(X1,X0))),
% 2.02/0.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.02/0.98  
% 2.02/0.98  fof(f22,plain,(
% 2.02/0.98    ! [X0,X1] : (k2_relat_1(k7_relat_1(X1,X0)) = k9_relat_1(X1,X0) | ~v1_relat_1(X1))),
% 2.02/0.98    inference(ennf_transformation,[],[f5])).
% 2.02/0.98  
% 2.02/0.98  fof(f44,plain,(
% 2.02/0.98    ( ! [X0,X1] : (k2_relat_1(k7_relat_1(X1,X0)) = k9_relat_1(X1,X0) | ~v1_relat_1(X1)) )),
% 2.02/0.98    inference(cnf_transformation,[],[f22])).
% 2.02/0.98  
% 2.02/0.98  fof(f13,axiom,(
% 2.02/0.98    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k1_relat_1(X2) = k1_relset_1(X0,X1,X2))),
% 2.02/0.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.02/0.98  
% 2.02/0.98  fof(f31,plain,(
% 2.02/0.98    ! [X0,X1,X2] : (k1_relat_1(X2) = k1_relset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 2.02/0.98    inference(ennf_transformation,[],[f13])).
% 2.02/0.98  
% 2.02/0.98  fof(f54,plain,(
% 2.02/0.98    ( ! [X2,X0,X1] : (k1_relat_1(X2) = k1_relset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 2.02/0.98    inference(cnf_transformation,[],[f31])).
% 2.02/0.98  
% 2.02/0.98  fof(f14,axiom,(
% 2.02/0.98    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k2_relat_1(X2) = k2_relset_1(X0,X1,X2))),
% 2.02/0.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.02/0.98  
% 2.02/0.98  fof(f32,plain,(
% 2.02/0.98    ! [X0,X1,X2] : (k2_relat_1(X2) = k2_relset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 2.02/0.98    inference(ennf_transformation,[],[f14])).
% 2.02/0.98  
% 2.02/0.98  fof(f55,plain,(
% 2.02/0.98    ( ! [X2,X0,X1] : (k2_relat_1(X2) = k2_relset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 2.02/0.98    inference(cnf_transformation,[],[f32])).
% 2.02/0.98  
% 2.02/0.98  fof(f59,plain,(
% 2.02/0.98    k1_relset_1(sK1,sK0,sK2) != k8_relset_1(sK1,sK0,sK2,k7_relset_1(sK1,sK0,sK2,sK1)) | k2_relset_1(sK1,sK0,sK2) != k7_relset_1(sK1,sK0,sK2,k8_relset_1(sK1,sK0,sK2,sK0))),
% 2.02/0.98    inference(cnf_transformation,[],[f38])).
% 2.02/0.98  
% 2.02/0.98  fof(f16,axiom,(
% 2.02/0.98    ! [X0,X1,X2,X3] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k10_relat_1(X2,X3) = k8_relset_1(X0,X1,X2,X3))),
% 2.02/0.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.02/0.98  
% 2.02/0.98  fof(f34,plain,(
% 2.02/0.98    ! [X0,X1,X2,X3] : (k10_relat_1(X2,X3) = k8_relset_1(X0,X1,X2,X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 2.02/0.98    inference(ennf_transformation,[],[f16])).
% 2.02/0.98  
% 2.02/0.98  fof(f57,plain,(
% 2.02/0.98    ( ! [X2,X0,X3,X1] : (k10_relat_1(X2,X3) = k8_relset_1(X0,X1,X2,X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 2.02/0.98    inference(cnf_transformation,[],[f34])).
% 2.02/0.98  
% 2.02/0.98  fof(f15,axiom,(
% 2.02/0.98    ! [X0,X1,X2,X3] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k9_relat_1(X2,X3) = k7_relset_1(X0,X1,X2,X3))),
% 2.02/0.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.02/0.98  
% 2.02/0.98  fof(f33,plain,(
% 2.02/0.98    ! [X0,X1,X2,X3] : (k9_relat_1(X2,X3) = k7_relset_1(X0,X1,X2,X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 2.02/0.98    inference(ennf_transformation,[],[f15])).
% 2.02/0.98  
% 2.02/0.98  fof(f56,plain,(
% 2.02/0.98    ( ! [X2,X0,X3,X1] : (k9_relat_1(X2,X3) = k7_relset_1(X0,X1,X2,X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 2.02/0.98    inference(cnf_transformation,[],[f33])).
% 2.02/0.98  
% 2.02/0.98  fof(f1,axiom,(
% 2.02/0.98    ! [X0,X1] : (r1_tarski(X0,X1) => k3_xboole_0(X0,X1) = X0)),
% 2.02/0.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.02/0.98  
% 2.02/0.98  fof(f19,plain,(
% 2.02/0.98    ! [X0,X1] : (k3_xboole_0(X0,X1) = X0 | ~r1_tarski(X0,X1))),
% 2.02/0.98    inference(ennf_transformation,[],[f1])).
% 2.02/0.98  
% 2.02/0.98  fof(f39,plain,(
% 2.02/0.98    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = X0 | ~r1_tarski(X0,X1)) )),
% 2.02/0.98    inference(cnf_transformation,[],[f19])).
% 2.02/0.98  
% 2.02/0.98  fof(f6,axiom,(
% 2.02/0.98    ! [X0,X1] : (v1_relat_1(X1) => k10_relat_1(X1,X0) = k10_relat_1(X1,k3_xboole_0(k2_relat_1(X1),X0)))),
% 2.02/0.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.02/0.98  
% 2.02/0.98  fof(f23,plain,(
% 2.02/0.98    ! [X0,X1] : (k10_relat_1(X1,X0) = k10_relat_1(X1,k3_xboole_0(k2_relat_1(X1),X0)) | ~v1_relat_1(X1))),
% 2.02/0.98    inference(ennf_transformation,[],[f6])).
% 2.02/0.98  
% 2.02/0.98  fof(f45,plain,(
% 2.02/0.98    ( ! [X0,X1] : (k10_relat_1(X1,X0) = k10_relat_1(X1,k3_xboole_0(k2_relat_1(X1),X0)) | ~v1_relat_1(X1)) )),
% 2.02/0.98    inference(cnf_transformation,[],[f23])).
% 2.02/0.98  
% 2.02/0.98  fof(f4,axiom,(
% 2.02/0.98    ! [X0] : (v1_relat_1(X0) => k2_relat_1(X0) = k9_relat_1(X0,k1_relat_1(X0)))),
% 2.02/0.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.02/0.98  
% 2.02/0.98  fof(f21,plain,(
% 2.02/0.98    ! [X0] : (k2_relat_1(X0) = k9_relat_1(X0,k1_relat_1(X0)) | ~v1_relat_1(X0))),
% 2.02/0.98    inference(ennf_transformation,[],[f4])).
% 2.02/0.98  
% 2.02/0.98  fof(f43,plain,(
% 2.02/0.98    ( ! [X0] : (k2_relat_1(X0) = k9_relat_1(X0,k1_relat_1(X0)) | ~v1_relat_1(X0)) )),
% 2.02/0.98    inference(cnf_transformation,[],[f21])).
% 2.02/0.98  
% 2.02/0.98  cnf(c_11,plain,
% 2.02/0.98      ( ~ r1_tarski(k2_relat_1(X0),X1)
% 2.02/0.98      | ~ v1_relat_1(X0)
% 2.02/0.98      | k5_relat_1(X0,k6_relat_1(X1)) = X0 ),
% 2.02/0.98      inference(cnf_transformation,[],[f50]) ).
% 2.02/0.98  
% 2.02/0.98  cnf(c_2,plain,
% 2.02/0.98      ( ~ v5_relat_1(X0,X1) | r1_tarski(k2_relat_1(X0),X1) | ~ v1_relat_1(X0) ),
% 2.02/0.98      inference(cnf_transformation,[],[f40]) ).
% 2.02/0.98  
% 2.02/0.98  cnf(c_13,plain,
% 2.02/0.98      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) | v5_relat_1(X0,X2) ),
% 2.02/0.98      inference(cnf_transformation,[],[f53]) ).
% 2.02/0.98  
% 2.02/0.98  cnf(c_251,plain,
% 2.02/0.98      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 2.02/0.98      | r1_tarski(k2_relat_1(X3),X4)
% 2.02/0.98      | ~ v1_relat_1(X3)
% 2.02/0.98      | X0 != X3
% 2.02/0.98      | X2 != X4 ),
% 2.02/0.98      inference(resolution_lifted,[status(thm)],[c_2,c_13]) ).
% 2.02/0.98  
% 2.02/0.98  cnf(c_252,plain,
% 2.02/0.98      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 2.02/0.98      | r1_tarski(k2_relat_1(X0),X2)
% 2.02/0.98      | ~ v1_relat_1(X0) ),
% 2.02/0.98      inference(unflattening,[status(thm)],[c_251]) ).
% 2.02/0.98  
% 2.02/0.98  cnf(c_12,plain,
% 2.02/0.98      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) | v1_relat_1(X0) ),
% 2.02/0.98      inference(cnf_transformation,[],[f51]) ).
% 2.02/0.98  
% 2.02/0.98  cnf(c_256,plain,
% 2.02/0.98      ( r1_tarski(k2_relat_1(X0),X2)
% 2.02/0.98      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) ),
% 2.02/0.98      inference(global_propositional_subsumption,[status(thm)],[c_252,c_12]) ).
% 2.02/0.98  
% 2.02/0.98  cnf(c_257,plain,
% 2.02/0.98      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 2.02/0.98      | r1_tarski(k2_relat_1(X0),X2) ),
% 2.02/0.98      inference(renaming,[status(thm)],[c_256]) ).
% 2.02/0.98  
% 2.02/0.98  cnf(c_20,negated_conjecture,
% 2.02/0.98      ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) ),
% 2.02/0.98      inference(cnf_transformation,[],[f58]) ).
% 2.02/0.98  
% 2.02/0.98  cnf(c_308,plain,
% 2.02/0.98      ( r1_tarski(k2_relat_1(X0),X1)
% 2.02/0.98      | k1_zfmisc_1(k2_zfmisc_1(X2,X1)) != k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))
% 2.02/0.98      | sK2 != X0 ),
% 2.02/0.98      inference(resolution_lifted,[status(thm)],[c_257,c_20]) ).
% 2.02/0.98  
% 2.02/0.98  cnf(c_309,plain,
% 2.02/0.98      ( r1_tarski(k2_relat_1(sK2),X0)
% 2.02/0.98      | k1_zfmisc_1(k2_zfmisc_1(X1,X0)) != k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)) ),
% 2.02/0.98      inference(unflattening,[status(thm)],[c_308]) ).
% 2.02/0.98  
% 2.02/0.98  cnf(c_402,plain,
% 2.02/0.98      ( ~ v1_relat_1(X0)
% 2.02/0.98      | X1 != X2
% 2.02/0.98      | k5_relat_1(X0,k6_relat_1(X2)) = X0
% 2.02/0.98      | k1_zfmisc_1(k2_zfmisc_1(X3,X1)) != k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))
% 2.02/0.98      | k2_relat_1(X0) != k2_relat_1(sK2) ),
% 2.02/0.98      inference(resolution_lifted,[status(thm)],[c_11,c_309]) ).
% 2.02/0.98  
% 2.02/0.98  cnf(c_403,plain,
% 2.02/0.98      ( ~ v1_relat_1(X0)
% 2.02/0.98      | k5_relat_1(X0,k6_relat_1(X1)) = X0
% 2.02/0.98      | k1_zfmisc_1(k2_zfmisc_1(X2,X1)) != k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))
% 2.02/0.98      | k2_relat_1(X0) != k2_relat_1(sK2) ),
% 2.02/0.98      inference(unflattening,[status(thm)],[c_402]) ).
% 2.02/0.98  
% 2.02/0.98  cnf(c_642,plain,
% 2.02/0.98      ( k5_relat_1(X0,k6_relat_1(X1)) = X0
% 2.02/0.98      | k1_zfmisc_1(k2_zfmisc_1(X2,X1)) != k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))
% 2.02/0.98      | k2_relat_1(X0) != k2_relat_1(sK2)
% 2.02/0.98      | v1_relat_1(X0) != iProver_top ),
% 2.02/0.98      inference(predicate_to_equality,[status(thm)],[c_403]) ).
% 2.02/0.98  
% 2.02/0.98  cnf(c_1378,plain,
% 2.02/0.98      ( k5_relat_1(X0,k6_relat_1(sK0)) = X0
% 2.02/0.98      | k2_relat_1(X0) != k2_relat_1(sK2)
% 2.02/0.98      | v1_relat_1(X0) != iProver_top ),
% 2.02/0.98      inference(equality_resolution,[status(thm)],[c_642]) ).
% 2.02/0.98  
% 2.02/0.98  cnf(c_1777,plain,
% 2.02/0.98      ( k5_relat_1(sK2,k6_relat_1(sK0)) = sK2
% 2.02/0.98      | v1_relat_1(sK2) != iProver_top ),
% 2.02/0.98      inference(equality_resolution,[status(thm)],[c_1378]) ).
% 2.02/0.98  
% 2.02/0.98  cnf(c_491,plain,( X0 = X0 ),theory(equality) ).
% 2.02/0.98  
% 2.02/0.98  cnf(c_733,plain,
% 2.02/0.98      ( k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)) = k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)) ),
% 2.02/0.98      inference(instantiation,[status(thm)],[c_491]) ).
% 2.02/0.98  
% 2.02/0.98  cnf(c_365,plain,
% 2.02/0.98      ( v1_relat_1(X0)
% 2.02/0.98      | k1_zfmisc_1(k2_zfmisc_1(X1,X2)) != k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))
% 2.02/0.98      | sK2 != X0 ),
% 2.02/0.98      inference(resolution_lifted,[status(thm)],[c_12,c_20]) ).
% 2.02/0.98  
% 2.02/0.98  cnf(c_366,plain,
% 2.02/0.98      ( v1_relat_1(sK2)
% 2.02/0.98      | k1_zfmisc_1(k2_zfmisc_1(X0,X1)) != k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)) ),
% 2.02/0.98      inference(unflattening,[status(thm)],[c_365]) ).
% 2.02/0.98  
% 2.02/0.98  cnf(c_801,plain,
% 2.02/0.98      ( v1_relat_1(sK2)
% 2.02/0.98      | k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)) != k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)) ),
% 2.02/0.98      inference(instantiation,[status(thm)],[c_366]) ).
% 2.02/0.98  
% 2.02/0.98  cnf(c_802,plain,
% 2.02/0.98      ( k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)) != k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))
% 2.02/0.98      | v1_relat_1(sK2) = iProver_top ),
% 2.02/0.98      inference(predicate_to_equality,[status(thm)],[c_801]) ).
% 2.02/0.98  
% 2.02/0.98  cnf(c_2005,plain,
% 2.02/0.98      ( k5_relat_1(sK2,k6_relat_1(sK0)) = sK2 ),
% 2.02/0.98      inference(global_propositional_subsumption,
% 2.02/0.98                [status(thm)],
% 2.02/0.98                [c_1777,c_733,c_802]) ).
% 2.02/0.98  
% 2.02/0.98  cnf(c_3,plain,
% 2.02/0.98      ( v1_relat_1(k6_relat_1(X0)) ),
% 2.02/0.98      inference(cnf_transformation,[],[f42]) ).
% 2.02/0.98  
% 2.02/0.98  cnf(c_648,plain,
% 2.02/0.98      ( v1_relat_1(k6_relat_1(X0)) = iProver_top ),
% 2.02/0.98      inference(predicate_to_equality,[status(thm)],[c_3]) ).
% 2.02/0.98  
% 2.02/0.98  cnf(c_643,plain,
% 2.02/0.98      ( k1_zfmisc_1(k2_zfmisc_1(X0,X1)) != k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))
% 2.02/0.98      | v1_relat_1(sK2) = iProver_top ),
% 2.02/0.98      inference(predicate_to_equality,[status(thm)],[c_366]) ).
% 2.02/0.98  
% 2.02/0.98  cnf(c_1177,plain,
% 2.02/0.98      ( v1_relat_1(sK2) = iProver_top ),
% 2.02/0.98      inference(global_propositional_subsumption,
% 2.02/0.98                [status(thm)],
% 2.02/0.98                [c_643,c_733,c_802]) ).
% 2.02/0.98  
% 2.02/0.98  cnf(c_7,plain,
% 2.02/0.98      ( ~ v1_relat_1(X0)
% 2.02/0.98      | ~ v1_relat_1(X1)
% 2.02/0.98      | k10_relat_1(X1,k1_relat_1(X0)) = k1_relat_1(k5_relat_1(X1,X0)) ),
% 2.02/0.98      inference(cnf_transformation,[],[f46]) ).
% 2.02/0.98  
% 2.02/0.98  cnf(c_644,plain,
% 2.02/0.98      ( k10_relat_1(X0,k1_relat_1(X1)) = k1_relat_1(k5_relat_1(X0,X1))
% 2.02/0.98      | v1_relat_1(X1) != iProver_top
% 2.02/0.98      | v1_relat_1(X0) != iProver_top ),
% 2.02/0.98      inference(predicate_to_equality,[status(thm)],[c_7]) ).
% 2.02/0.98  
% 2.02/0.98  cnf(c_1859,plain,
% 2.02/0.98      ( k10_relat_1(sK2,k1_relat_1(X0)) = k1_relat_1(k5_relat_1(sK2,X0))
% 2.02/0.98      | v1_relat_1(X0) != iProver_top ),
% 2.02/0.98      inference(superposition,[status(thm)],[c_1177,c_644]) ).
% 2.02/0.98  
% 2.02/0.98  cnf(c_1914,plain,
% 2.02/0.98      ( k10_relat_1(sK2,k1_relat_1(k6_relat_1(X0))) = k1_relat_1(k5_relat_1(sK2,k6_relat_1(X0))) ),
% 2.02/0.98      inference(superposition,[status(thm)],[c_648,c_1859]) ).
% 2.02/0.98  
% 2.02/0.98  cnf(c_10,plain,
% 2.02/0.98      ( k1_relat_1(k6_relat_1(X0)) = X0 ),
% 2.02/0.98      inference(cnf_transformation,[],[f48]) ).
% 2.02/0.98  
% 2.02/0.98  cnf(c_1919,plain,
% 2.02/0.98      ( k1_relat_1(k5_relat_1(sK2,k6_relat_1(X0))) = k10_relat_1(sK2,X0) ),
% 2.02/0.98      inference(light_normalisation,[status(thm)],[c_1914,c_10]) ).
% 2.02/0.98  
% 2.02/0.98  cnf(c_2008,plain,
% 2.02/0.98      ( k10_relat_1(sK2,sK0) = k1_relat_1(sK2) ),
% 2.02/0.98      inference(superposition,[status(thm)],[c_2005,c_1919]) ).
% 2.02/0.98  
% 2.02/0.98  cnf(c_14,plain,
% 2.02/0.98      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) | v4_relat_1(X0,X1) ),
% 2.02/0.98      inference(cnf_transformation,[],[f52]) ).
% 2.02/0.98  
% 2.02/0.98  cnf(c_8,plain,
% 2.02/0.98      ( ~ v4_relat_1(X0,X1) | ~ v1_relat_1(X0) | k7_relat_1(X0,X1) = X0 ),
% 2.02/0.98      inference(cnf_transformation,[],[f47]) ).
% 2.02/0.98  
% 2.02/0.98  cnf(c_230,plain,
% 2.02/0.98      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 2.02/0.98      | ~ v1_relat_1(X0)
% 2.02/0.98      | k7_relat_1(X0,X1) = X0 ),
% 2.02/0.98      inference(resolution,[status(thm)],[c_14,c_8]) ).
% 2.02/0.98  
% 2.02/0.98  cnf(c_234,plain,
% 2.02/0.98      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 2.02/0.98      | k7_relat_1(X0,X1) = X0 ),
% 2.02/0.98      inference(global_propositional_subsumption,
% 2.02/0.98                [status(thm)],
% 2.02/0.98                [c_230,c_14,c_12,c_8]) ).
% 2.02/0.98  
% 2.02/0.98  cnf(c_320,plain,
% 2.02/0.98      ( k7_relat_1(X0,X1) = X0
% 2.02/0.98      | k1_zfmisc_1(k2_zfmisc_1(X1,X2)) != k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))
% 2.02/0.98      | sK2 != X0 ),
% 2.02/0.98      inference(resolution_lifted,[status(thm)],[c_234,c_20]) ).
% 2.02/0.98  
% 2.02/0.98  cnf(c_321,plain,
% 2.02/0.98      ( k7_relat_1(sK2,X0) = sK2
% 2.02/0.98      | k1_zfmisc_1(k2_zfmisc_1(X0,X1)) != k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)) ),
% 2.02/0.98      inference(unflattening,[status(thm)],[c_320]) ).
% 2.02/0.98  
% 2.02/0.98  cnf(c_732,plain,
% 2.02/0.98      ( k7_relat_1(sK2,sK1) = sK2 ),
% 2.02/0.98      inference(equality_resolution,[status(thm)],[c_321]) ).
% 2.02/0.98  
% 2.02/0.98  cnf(c_5,plain,
% 2.02/0.98      ( ~ v1_relat_1(X0) | k2_relat_1(k7_relat_1(X0,X1)) = k9_relat_1(X0,X1) ),
% 2.02/0.98      inference(cnf_transformation,[],[f44]) ).
% 2.02/0.98  
% 2.02/0.98  cnf(c_646,plain,
% 2.02/0.98      ( k2_relat_1(k7_relat_1(X0,X1)) = k9_relat_1(X0,X1)
% 2.02/0.98      | v1_relat_1(X0) != iProver_top ),
% 2.02/0.98      inference(predicate_to_equality,[status(thm)],[c_5]) ).
% 2.02/0.98  
% 2.02/0.98  cnf(c_1447,plain,
% 2.02/0.98      ( k2_relat_1(k7_relat_1(sK2,X0)) = k9_relat_1(sK2,X0) ),
% 2.02/0.98      inference(superposition,[status(thm)],[c_1177,c_646]) ).
% 2.02/0.98  
% 2.02/0.98  cnf(c_1589,plain,
% 2.02/0.98      ( k9_relat_1(sK2,sK1) = k2_relat_1(sK2) ),
% 2.02/0.98      inference(superposition,[status(thm)],[c_732,c_1447]) ).
% 2.02/0.98  
% 2.02/0.98  cnf(c_15,plain,
% 2.02/0.98      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 2.02/0.98      | k1_relset_1(X1,X2,X0) = k1_relat_1(X0) ),
% 2.02/0.98      inference(cnf_transformation,[],[f54]) ).
% 2.02/0.98  
% 2.02/0.98  cnf(c_356,plain,
% 2.02/0.98      ( k1_relset_1(X0,X1,X2) = k1_relat_1(X2)
% 2.02/0.98      | k1_zfmisc_1(k2_zfmisc_1(X0,X1)) != k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))
% 2.02/0.98      | sK2 != X2 ),
% 2.02/0.98      inference(resolution_lifted,[status(thm)],[c_15,c_20]) ).
% 2.02/0.98  
% 2.02/0.98  cnf(c_357,plain,
% 2.02/0.98      ( k1_relset_1(X0,X1,sK2) = k1_relat_1(sK2)
% 2.02/0.98      | k1_zfmisc_1(k2_zfmisc_1(X0,X1)) != k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)) ),
% 2.02/0.98      inference(unflattening,[status(thm)],[c_356]) ).
% 2.02/0.98  
% 2.02/0.98  cnf(c_744,plain,
% 2.02/0.98      ( k1_relset_1(sK1,sK0,sK2) = k1_relat_1(sK2) ),
% 2.02/0.98      inference(equality_resolution,[status(thm)],[c_357]) ).
% 2.02/0.98  
% 2.02/0.98  cnf(c_16,plain,
% 2.02/0.98      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 2.02/0.98      | k2_relset_1(X1,X2,X0) = k2_relat_1(X0) ),
% 2.02/0.98      inference(cnf_transformation,[],[f55]) ).
% 2.02/0.98  
% 2.02/0.98  cnf(c_347,plain,
% 2.02/0.98      ( k2_relset_1(X0,X1,X2) = k2_relat_1(X2)
% 2.02/0.98      | k1_zfmisc_1(k2_zfmisc_1(X0,X1)) != k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))
% 2.02/0.98      | sK2 != X2 ),
% 2.02/0.98      inference(resolution_lifted,[status(thm)],[c_16,c_20]) ).
% 2.02/0.98  
% 2.02/0.98  cnf(c_348,plain,
% 2.02/0.98      ( k2_relset_1(X0,X1,sK2) = k2_relat_1(sK2)
% 2.02/0.98      | k1_zfmisc_1(k2_zfmisc_1(X0,X1)) != k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)) ),
% 2.02/0.98      inference(unflattening,[status(thm)],[c_347]) ).
% 2.02/0.98  
% 2.02/0.98  cnf(c_741,plain,
% 2.02/0.98      ( k2_relset_1(sK1,sK0,sK2) = k2_relat_1(sK2) ),
% 2.02/0.98      inference(equality_resolution,[status(thm)],[c_348]) ).
% 2.02/0.98  
% 2.02/0.98  cnf(c_19,negated_conjecture,
% 2.02/0.98      ( k2_relset_1(sK1,sK0,sK2) != k7_relset_1(sK1,sK0,sK2,k8_relset_1(sK1,sK0,sK2,sK0))
% 2.02/0.98      | k1_relset_1(sK1,sK0,sK2) != k8_relset_1(sK1,sK0,sK2,k7_relset_1(sK1,sK0,sK2,sK1)) ),
% 2.02/0.98      inference(cnf_transformation,[],[f59]) ).
% 2.02/0.98  
% 2.02/0.98  cnf(c_845,plain,
% 2.02/0.98      ( k8_relset_1(sK1,sK0,sK2,k7_relset_1(sK1,sK0,sK2,sK1)) != k1_relset_1(sK1,sK0,sK2)
% 2.02/0.98      | k7_relset_1(sK1,sK0,sK2,k8_relset_1(sK1,sK0,sK2,sK0)) != k2_relat_1(sK2) ),
% 2.02/0.98      inference(demodulation,[status(thm)],[c_741,c_19]) ).
% 2.02/0.98  
% 2.02/0.98  cnf(c_1112,plain,
% 2.02/0.98      ( k8_relset_1(sK1,sK0,sK2,k7_relset_1(sK1,sK0,sK2,sK1)) != k1_relat_1(sK2)
% 2.02/0.98      | k7_relset_1(sK1,sK0,sK2,k8_relset_1(sK1,sK0,sK2,sK0)) != k2_relat_1(sK2) ),
% 2.02/0.98      inference(demodulation,[status(thm)],[c_744,c_845]) ).
% 2.02/0.98  
% 2.02/0.98  cnf(c_18,plain,
% 2.02/0.98      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 2.02/0.98      | k8_relset_1(X1,X2,X0,X3) = k10_relat_1(X0,X3) ),
% 2.02/0.98      inference(cnf_transformation,[],[f57]) ).
% 2.02/0.98  
% 2.02/0.98  cnf(c_329,plain,
% 2.02/0.98      ( k8_relset_1(X0,X1,X2,X3) = k10_relat_1(X2,X3)
% 2.02/0.98      | k1_zfmisc_1(k2_zfmisc_1(X0,X1)) != k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))
% 2.02/0.98      | sK2 != X2 ),
% 2.02/0.98      inference(resolution_lifted,[status(thm)],[c_18,c_20]) ).
% 2.02/0.98  
% 2.02/0.98  cnf(c_330,plain,
% 2.02/0.98      ( k8_relset_1(X0,X1,sK2,X2) = k10_relat_1(sK2,X2)
% 2.02/0.98      | k1_zfmisc_1(k2_zfmisc_1(X0,X1)) != k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)) ),
% 2.02/0.98      inference(unflattening,[status(thm)],[c_329]) ).
% 2.02/0.98  
% 2.02/0.98  cnf(c_782,plain,
% 2.02/0.98      ( k8_relset_1(sK1,sK0,sK2,X0) = k10_relat_1(sK2,X0) ),
% 2.02/0.98      inference(equality_resolution,[status(thm)],[c_330]) ).
% 2.02/0.98  
% 2.02/0.98  cnf(c_17,plain,
% 2.02/0.98      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 2.02/0.98      | k7_relset_1(X1,X2,X0,X3) = k9_relat_1(X0,X3) ),
% 2.02/0.98      inference(cnf_transformation,[],[f56]) ).
% 2.02/0.98  
% 2.02/0.98  cnf(c_338,plain,
% 2.02/0.98      ( k7_relset_1(X0,X1,X2,X3) = k9_relat_1(X2,X3)
% 2.02/0.98      | k1_zfmisc_1(k2_zfmisc_1(X0,X1)) != k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))
% 2.02/0.98      | sK2 != X2 ),
% 2.02/0.98      inference(resolution_lifted,[status(thm)],[c_17,c_20]) ).
% 2.02/0.98  
% 2.02/0.98  cnf(c_339,plain,
% 2.02/0.98      ( k7_relset_1(X0,X1,sK2,X2) = k9_relat_1(sK2,X2)
% 2.02/0.98      | k1_zfmisc_1(k2_zfmisc_1(X0,X1)) != k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)) ),
% 2.02/0.98      inference(unflattening,[status(thm)],[c_338]) ).
% 2.02/0.98  
% 2.02/0.98  cnf(c_786,plain,
% 2.02/0.98      ( k7_relset_1(sK1,sK0,sK2,X0) = k9_relat_1(sK2,X0) ),
% 2.02/0.98      inference(equality_resolution,[status(thm)],[c_339]) ).
% 2.02/0.98  
% 2.02/0.98  cnf(c_1276,plain,
% 2.02/0.98      ( k10_relat_1(sK2,k9_relat_1(sK2,sK1)) != k1_relat_1(sK2)
% 2.02/0.98      | k9_relat_1(sK2,k10_relat_1(sK2,sK0)) != k2_relat_1(sK2) ),
% 2.02/0.98      inference(demodulation,[status(thm)],[c_1112,c_782,c_786]) ).
% 2.02/0.98  
% 2.02/0.98  cnf(c_1591,plain,
% 2.02/0.98      ( k10_relat_1(sK2,k2_relat_1(sK2)) != k1_relat_1(sK2)
% 2.02/0.98      | k9_relat_1(sK2,k10_relat_1(sK2,sK0)) != k2_relat_1(sK2) ),
% 2.02/0.98      inference(demodulation,[status(thm)],[c_1589,c_1276]) ).
% 2.02/0.98  
% 2.02/0.98  cnf(c_0,plain,
% 2.02/0.98      ( ~ r1_tarski(X0,X1) | k3_xboole_0(X0,X1) = X0 ),
% 2.02/0.98      inference(cnf_transformation,[],[f39]) ).
% 2.02/0.98  
% 2.02/0.98  cnf(c_393,plain,
% 2.02/0.98      ( X0 != X1
% 2.02/0.98      | k3_xboole_0(X2,X1) = X2
% 2.02/0.98      | k1_zfmisc_1(k2_zfmisc_1(X3,X0)) != k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))
% 2.02/0.98      | k2_relat_1(sK2) != X2 ),
% 2.02/0.98      inference(resolution_lifted,[status(thm)],[c_0,c_309]) ).
% 2.02/0.98  
% 2.02/0.98  cnf(c_394,plain,
% 2.02/0.98      ( k3_xboole_0(k2_relat_1(sK2),X0) = k2_relat_1(sK2)
% 2.02/0.98      | k1_zfmisc_1(k2_zfmisc_1(X1,X0)) != k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)) ),
% 2.02/0.98      inference(unflattening,[status(thm)],[c_393]) ).
% 2.02/0.98  
% 2.02/0.98  cnf(c_897,plain,
% 2.02/0.98      ( k3_xboole_0(k2_relat_1(sK2),sK0) = k2_relat_1(sK2) ),
% 2.02/0.98      inference(equality_resolution,[status(thm)],[c_394]) ).
% 2.02/0.98  
% 2.02/0.98  cnf(c_6,plain,
% 2.02/0.98      ( ~ v1_relat_1(X0)
% 2.02/0.98      | k10_relat_1(X0,k3_xboole_0(k2_relat_1(X0),X1)) = k10_relat_1(X0,X1) ),
% 2.02/0.98      inference(cnf_transformation,[],[f45]) ).
% 2.02/0.98  
% 2.02/0.98  cnf(c_645,plain,
% 2.02/0.98      ( k10_relat_1(X0,k3_xboole_0(k2_relat_1(X0),X1)) = k10_relat_1(X0,X1)
% 2.02/0.98      | v1_relat_1(X0) != iProver_top ),
% 2.02/0.98      inference(predicate_to_equality,[status(thm)],[c_6]) ).
% 2.02/0.98  
% 2.02/0.98  cnf(c_1493,plain,
% 2.02/0.98      ( k10_relat_1(sK2,k3_xboole_0(k2_relat_1(sK2),X0)) = k10_relat_1(sK2,X0) ),
% 2.02/0.98      inference(superposition,[status(thm)],[c_1177,c_645]) ).
% 2.02/0.98  
% 2.02/0.98  cnf(c_1605,plain,
% 2.02/0.98      ( k10_relat_1(sK2,k2_relat_1(sK2)) = k10_relat_1(sK2,sK0) ),
% 2.02/0.98      inference(superposition,[status(thm)],[c_897,c_1493]) ).
% 2.02/0.98  
% 2.02/0.98  cnf(c_1718,plain,
% 2.02/0.98      ( k10_relat_1(sK2,sK0) != k1_relat_1(sK2)
% 2.02/0.98      | k9_relat_1(sK2,k10_relat_1(sK2,sK0)) != k2_relat_1(sK2) ),
% 2.02/0.98      inference(light_normalisation,[status(thm)],[c_1591,c_1605]) ).
% 2.02/0.98  
% 2.02/0.98  cnf(c_2169,plain,
% 2.02/0.98      ( k9_relat_1(sK2,k1_relat_1(sK2)) != k2_relat_1(sK2)
% 2.02/0.98      | k1_relat_1(sK2) != k1_relat_1(sK2) ),
% 2.02/0.98      inference(demodulation,[status(thm)],[c_2008,c_1718]) ).
% 2.02/0.98  
% 2.02/0.98  cnf(c_2173,plain,
% 2.02/0.98      ( k9_relat_1(sK2,k1_relat_1(sK2)) != k2_relat_1(sK2) ),
% 2.02/0.98      inference(equality_resolution_simp,[status(thm)],[c_2169]) ).
% 2.02/0.98  
% 2.02/0.98  cnf(c_4,plain,
% 2.02/0.98      ( ~ v1_relat_1(X0) | k9_relat_1(X0,k1_relat_1(X0)) = k2_relat_1(X0) ),
% 2.02/0.98      inference(cnf_transformation,[],[f43]) ).
% 2.02/0.98  
% 2.02/0.98  cnf(c_647,plain,
% 2.02/0.98      ( k9_relat_1(X0,k1_relat_1(X0)) = k2_relat_1(X0)
% 2.02/0.98      | v1_relat_1(X0) != iProver_top ),
% 2.02/0.98      inference(predicate_to_equality,[status(thm)],[c_4]) ).
% 2.02/0.98  
% 2.02/0.98  cnf(c_1182,plain,
% 2.02/0.98      ( k9_relat_1(sK2,k1_relat_1(sK2)) = k2_relat_1(sK2) ),
% 2.02/0.98      inference(superposition,[status(thm)],[c_1177,c_647]) ).
% 2.02/0.98  
% 2.02/0.98  cnf(c_2175,plain,
% 2.02/0.98      ( k2_relat_1(sK2) != k2_relat_1(sK2) ),
% 2.02/0.98      inference(light_normalisation,[status(thm)],[c_2173,c_1182]) ).
% 2.02/0.98  
% 2.02/0.98  cnf(c_2176,plain,
% 2.02/0.98      ( $false ),
% 2.02/0.98      inference(equality_resolution_simp,[status(thm)],[c_2175]) ).
% 2.02/0.98  
% 2.02/0.98  
% 2.02/0.98  % SZS output end CNFRefutation for theBenchmark.p
% 2.02/0.98  
% 2.02/0.98  ------                               Statistics
% 2.02/0.98  
% 2.02/0.98  ------ General
% 2.02/0.98  
% 2.02/0.98  abstr_ref_over_cycles:                  0
% 2.02/0.98  abstr_ref_under_cycles:                 0
% 2.02/0.98  gc_basic_clause_elim:                   0
% 2.02/0.98  forced_gc_time:                         0
% 2.02/0.98  parsing_time:                           0.008
% 2.02/0.98  unif_index_cands_time:                  0.
% 2.02/0.98  unif_index_add_time:                    0.
% 2.02/0.98  orderings_time:                         0.
% 2.02/0.98  out_proof_time:                         0.01
% 2.02/0.98  total_time:                             0.123
% 2.02/0.98  num_of_symbols:                         53
% 2.02/0.98  num_of_terms:                           2500
% 2.02/0.98  
% 2.02/0.98  ------ Preprocessing
% 2.02/0.98  
% 2.02/0.98  num_of_splits:                          0
% 2.02/0.98  num_of_split_atoms:                     0
% 2.02/0.98  num_of_reused_defs:                     0
% 2.02/0.98  num_eq_ax_congr_red:                    20
% 2.02/0.98  num_of_sem_filtered_clauses:            1
% 2.02/0.98  num_of_subtypes:                        0
% 2.02/0.98  monotx_restored_types:                  0
% 2.02/0.98  sat_num_of_epr_types:                   0
% 2.02/0.98  sat_num_of_non_cyclic_types:            0
% 2.02/0.98  sat_guarded_non_collapsed_types:        0
% 2.02/0.98  num_pure_diseq_elim:                    0
% 2.02/0.98  simp_replaced_by:                       0
% 2.02/0.98  res_preprocessed:                       102
% 2.02/0.98  prep_upred:                             0
% 2.02/0.98  prep_unflattend:                        15
% 2.02/0.98  smt_new_axioms:                         0
% 2.02/0.98  pred_elim_cands:                        1
% 2.02/0.98  pred_elim:                              4
% 2.02/0.98  pred_elim_cl:                           5
% 2.02/0.98  pred_elim_cycles:                       7
% 2.02/0.98  merged_defs:                            0
% 2.02/0.98  merged_defs_ncl:                        0
% 2.02/0.98  bin_hyper_res:                          0
% 2.02/0.98  prep_cycles:                            4
% 2.02/0.98  pred_elim_time:                         0.004
% 2.02/0.98  splitting_time:                         0.
% 2.02/0.98  sem_filter_time:                        0.
% 2.02/0.98  monotx_time:                            0.
% 2.02/0.98  subtype_inf_time:                       0.
% 2.02/0.98  
% 2.02/0.98  ------ Problem properties
% 2.02/0.98  
% 2.02/0.98  clauses:                                16
% 2.02/0.98  conjectures:                            1
% 2.02/0.98  epr:                                    0
% 2.02/0.98  horn:                                   16
% 2.02/0.98  ground:                                 1
% 2.02/0.98  unary:                                  3
% 2.02/0.98  binary:                                 11
% 2.02/0.98  lits:                                   32
% 2.02/0.98  lits_eq:                                24
% 2.02/0.98  fd_pure:                                0
% 2.02/0.98  fd_pseudo:                              0
% 2.02/0.98  fd_cond:                                0
% 2.02/0.98  fd_pseudo_cond:                         0
% 2.02/0.98  ac_symbols:                             0
% 2.02/0.98  
% 2.02/0.98  ------ Propositional Solver
% 2.02/0.98  
% 2.02/0.98  prop_solver_calls:                      28
% 2.02/0.98  prop_fast_solver_calls:                 582
% 2.02/0.98  smt_solver_calls:                       0
% 2.02/0.98  smt_fast_solver_calls:                  0
% 2.02/0.98  prop_num_of_clauses:                    1029
% 2.02/0.98  prop_preprocess_simplified:             3433
% 2.02/0.98  prop_fo_subsumed:                       5
% 2.02/0.98  prop_solver_time:                       0.
% 2.02/0.98  smt_solver_time:                        0.
% 2.02/0.98  smt_fast_solver_time:                   0.
% 2.02/0.98  prop_fast_solver_time:                  0.
% 2.02/0.98  prop_unsat_core_time:                   0.
% 2.02/0.98  
% 2.02/0.98  ------ QBF
% 2.02/0.98  
% 2.02/0.98  qbf_q_res:                              0
% 2.02/0.98  qbf_num_tautologies:                    0
% 2.02/0.98  qbf_prep_cycles:                        0
% 2.02/0.98  
% 2.02/0.98  ------ BMC1
% 2.02/0.98  
% 2.02/0.98  bmc1_current_bound:                     -1
% 2.02/0.98  bmc1_last_solved_bound:                 -1
% 2.02/0.98  bmc1_unsat_core_size:                   -1
% 2.02/0.98  bmc1_unsat_core_parents_size:           -1
% 2.02/0.98  bmc1_merge_next_fun:                    0
% 2.02/0.98  bmc1_unsat_core_clauses_time:           0.
% 2.02/0.98  
% 2.02/0.98  ------ Instantiation
% 2.02/0.98  
% 2.02/0.98  inst_num_of_clauses:                    435
% 2.02/0.98  inst_num_in_passive:                    68
% 2.02/0.98  inst_num_in_active:                     215
% 2.02/0.98  inst_num_in_unprocessed:                152
% 2.02/0.98  inst_num_of_loops:                      220
% 2.02/0.98  inst_num_of_learning_restarts:          0
% 2.02/0.98  inst_num_moves_active_passive:          2
% 2.02/0.98  inst_lit_activity:                      0
% 2.02/0.98  inst_lit_activity_moves:                0
% 2.02/0.98  inst_num_tautologies:                   0
% 2.02/0.98  inst_num_prop_implied:                  0
% 2.02/0.98  inst_num_existing_simplified:           0
% 2.02/0.98  inst_num_eq_res_simplified:             0
% 2.02/0.98  inst_num_child_elim:                    0
% 2.02/0.98  inst_num_of_dismatching_blockings:      32
% 2.02/0.98  inst_num_of_non_proper_insts:           279
% 2.02/0.98  inst_num_of_duplicates:                 0
% 2.02/0.98  inst_inst_num_from_inst_to_res:         0
% 2.02/0.98  inst_dismatching_checking_time:         0.
% 2.02/0.98  
% 2.02/0.98  ------ Resolution
% 2.02/0.98  
% 2.02/0.98  res_num_of_clauses:                     0
% 2.02/0.98  res_num_in_passive:                     0
% 2.02/0.98  res_num_in_active:                      0
% 2.02/0.98  res_num_of_loops:                       106
% 2.02/0.98  res_forward_subset_subsumed:            33
% 2.02/0.98  res_backward_subset_subsumed:           0
% 2.02/0.98  res_forward_subsumed:                   0
% 2.02/0.98  res_backward_subsumed:                  0
% 2.02/0.98  res_forward_subsumption_resolution:     0
% 2.02/0.98  res_backward_subsumption_resolution:    0
% 2.02/0.98  res_clause_to_clause_subsumption:       58
% 2.02/0.98  res_orphan_elimination:                 0
% 2.02/0.98  res_tautology_del:                      48
% 2.02/0.98  res_num_eq_res_simplified:              0
% 2.02/0.98  res_num_sel_changes:                    0
% 2.02/0.98  res_moves_from_active_to_pass:          0
% 2.02/0.98  
% 2.02/0.98  ------ Superposition
% 2.02/0.98  
% 2.02/0.98  sup_time_total:                         0.
% 2.02/0.98  sup_time_generating:                    0.
% 2.02/0.98  sup_time_sim_full:                      0.
% 2.02/0.98  sup_time_sim_immed:                     0.
% 2.02/0.98  
% 2.02/0.98  sup_num_of_clauses:                     42
% 2.02/0.98  sup_num_in_active:                      38
% 2.02/0.98  sup_num_in_passive:                     4
% 2.02/0.98  sup_num_of_loops:                       43
% 2.02/0.98  sup_fw_superposition:                   17
% 2.02/0.98  sup_bw_superposition:                   3
% 2.02/0.98  sup_immediate_simplified:               4
% 2.02/0.98  sup_given_eliminated:                   0
% 2.02/0.98  comparisons_done:                       0
% 2.02/0.98  comparisons_avoided:                    0
% 2.02/0.98  
% 2.02/0.98  ------ Simplifications
% 2.02/0.98  
% 2.02/0.98  
% 2.02/0.98  sim_fw_subset_subsumed:                 0
% 2.02/0.98  sim_bw_subset_subsumed:                 0
% 2.02/0.98  sim_fw_subsumed:                        0
% 2.02/0.98  sim_bw_subsumed:                        0
% 2.02/0.98  sim_fw_subsumption_res:                 0
% 2.02/0.98  sim_bw_subsumption_res:                 0
% 2.02/0.98  sim_tautology_del:                      0
% 2.02/0.98  sim_eq_tautology_del:                   0
% 2.02/0.98  sim_eq_res_simp:                        1
% 2.02/0.98  sim_fw_demodulated:                     1
% 2.02/0.98  sim_bw_demodulated:                     5
% 2.02/0.98  sim_light_normalised:                   6
% 2.02/0.98  sim_joinable_taut:                      0
% 2.02/0.98  sim_joinable_simp:                      0
% 2.02/0.98  sim_ac_normalised:                      0
% 2.02/0.98  sim_smt_subsumption:                    0
% 2.02/0.98  
%------------------------------------------------------------------------------
