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
% DateTime   : Thu Dec  3 12:07:37 EST 2020

% Result     : Theorem 3.33s
% Output     : CNFRefutation 3.33s
% Verified   : 
% Statistics : Number of formulae       :  200 (2255 expanded)
%              Number of clauses        :  122 ( 691 expanded)
%              Number of leaves         :   19 ( 445 expanded)
%              Depth                    :   25
%              Number of atoms          :  627 (11586 expanded)
%              Number of equality atoms :  270 (3253 expanded)
%              Maximal formula depth    :   10 (   4 average)
%              Maximal clause size      :   14 (   3 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f19,conjecture,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
        & v3_funct_2(X2,X0,X0)
        & v1_funct_2(X2,X0,X0)
        & v1_funct_1(X2) )
     => ( r1_tarski(X1,X0)
       => ( k8_relset_1(X0,X0,X2,k7_relset_1(X0,X0,X2,X1)) = X1
          & k7_relset_1(X0,X0,X2,k8_relset_1(X0,X0,X2,X1)) = X1 ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f20,negated_conjecture,(
    ~ ! [X0,X1,X2] :
        ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
          & v3_funct_2(X2,X0,X0)
          & v1_funct_2(X2,X0,X0)
          & v1_funct_1(X2) )
       => ( r1_tarski(X1,X0)
         => ( k8_relset_1(X0,X0,X2,k7_relset_1(X0,X0,X2,X1)) = X1
            & k7_relset_1(X0,X0,X2,k8_relset_1(X0,X0,X2,X1)) = X1 ) ) ) ),
    inference(negated_conjecture,[],[f19])).

fof(f46,plain,(
    ? [X0,X1,X2] :
      ( ( k8_relset_1(X0,X0,X2,k7_relset_1(X0,X0,X2,X1)) != X1
        | k7_relset_1(X0,X0,X2,k8_relset_1(X0,X0,X2,X1)) != X1 )
      & r1_tarski(X1,X0)
      & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
      & v3_funct_2(X2,X0,X0)
      & v1_funct_2(X2,X0,X0)
      & v1_funct_1(X2) ) ),
    inference(ennf_transformation,[],[f20])).

fof(f47,plain,(
    ? [X0,X1,X2] :
      ( ( k8_relset_1(X0,X0,X2,k7_relset_1(X0,X0,X2,X1)) != X1
        | k7_relset_1(X0,X0,X2,k8_relset_1(X0,X0,X2,X1)) != X1 )
      & r1_tarski(X1,X0)
      & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
      & v3_funct_2(X2,X0,X0)
      & v1_funct_2(X2,X0,X0)
      & v1_funct_1(X2) ) ),
    inference(flattening,[],[f46])).

fof(f52,plain,
    ( ? [X0,X1,X2] :
        ( ( k8_relset_1(X0,X0,X2,k7_relset_1(X0,X0,X2,X1)) != X1
          | k7_relset_1(X0,X0,X2,k8_relset_1(X0,X0,X2,X1)) != X1 )
        & r1_tarski(X1,X0)
        & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
        & v3_funct_2(X2,X0,X0)
        & v1_funct_2(X2,X0,X0)
        & v1_funct_1(X2) )
   => ( ( k8_relset_1(sK0,sK0,sK2,k7_relset_1(sK0,sK0,sK2,sK1)) != sK1
        | k7_relset_1(sK0,sK0,sK2,k8_relset_1(sK0,sK0,sK2,sK1)) != sK1 )
      & r1_tarski(sK1,sK0)
      & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
      & v3_funct_2(sK2,sK0,sK0)
      & v1_funct_2(sK2,sK0,sK0)
      & v1_funct_1(sK2) ) ),
    introduced(choice_axiom,[])).

fof(f53,plain,
    ( ( k8_relset_1(sK0,sK0,sK2,k7_relset_1(sK0,sK0,sK2,sK1)) != sK1
      | k7_relset_1(sK0,sK0,sK2,k8_relset_1(sK0,sK0,sK2,sK1)) != sK1 )
    & r1_tarski(sK1,sK0)
    & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
    & v3_funct_2(sK2,sK0,sK0)
    & v1_funct_2(sK2,sK0,sK0)
    & v1_funct_1(sK2) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f47,f52])).

fof(f86,plain,(
    r1_tarski(sK1,sK0) ),
    inference(cnf_transformation,[],[f53])).

fof(f85,plain,(
    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) ),
    inference(cnf_transformation,[],[f53])).

fof(f12,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => ( v5_relat_1(X2,X1)
        & v4_relat_1(X2,X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f35,plain,(
    ! [X0,X1,X2] :
      ( ( v5_relat_1(X2,X1)
        & v4_relat_1(X2,X0) )
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f68,plain,(
    ! [X2,X0,X1] :
      ( v4_relat_1(X2,X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f35])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ( v4_relat_1(X1,X0)
      <=> r1_tarski(k1_relat_1(X1),X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f22,plain,(
    ! [X0,X1] :
      ( ( v4_relat_1(X1,X0)
      <=> r1_tarski(k1_relat_1(X1),X0) )
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f50,plain,(
    ! [X0,X1] :
      ( ( ( v4_relat_1(X1,X0)
          | ~ r1_tarski(k1_relat_1(X1),X0) )
        & ( r1_tarski(k1_relat_1(X1),X0)
          | ~ v4_relat_1(X1,X0) ) )
      | ~ v1_relat_1(X1) ) ),
    inference(nnf_transformation,[],[f22])).

fof(f58,plain,(
    ! [X0,X1] :
      ( r1_tarski(k1_relat_1(X1),X0)
      | ~ v4_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f50])).

fof(f18,axiom,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
        & v3_funct_2(X1,X0,X0)
        & v1_funct_2(X1,X0,X0)
        & v1_funct_1(X1) )
     => k2_funct_1(X1) = k2_funct_2(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f44,plain,(
    ! [X0,X1] :
      ( k2_funct_1(X1) = k2_funct_2(X0,X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
      | ~ v3_funct_2(X1,X0,X0)
      | ~ v1_funct_2(X1,X0,X0)
      | ~ v1_funct_1(X1) ) ),
    inference(ennf_transformation,[],[f18])).

fof(f45,plain,(
    ! [X0,X1] :
      ( k2_funct_1(X1) = k2_funct_2(X0,X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
      | ~ v3_funct_2(X1,X0,X0)
      | ~ v1_funct_2(X1,X0,X0)
      | ~ v1_funct_1(X1) ) ),
    inference(flattening,[],[f44])).

fof(f81,plain,(
    ! [X0,X1] :
      ( k2_funct_1(X1) = k2_funct_2(X0,X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
      | ~ v3_funct_2(X1,X0,X0)
      | ~ v1_funct_2(X1,X0,X0)
      | ~ v1_funct_1(X1) ) ),
    inference(cnf_transformation,[],[f45])).

fof(f82,plain,(
    v1_funct_1(sK2) ),
    inference(cnf_transformation,[],[f53])).

fof(f83,plain,(
    v1_funct_2(sK2,sK0,sK0) ),
    inference(cnf_transformation,[],[f53])).

fof(f84,plain,(
    v3_funct_2(sK2,sK0,sK0) ),
    inference(cnf_transformation,[],[f53])).

fof(f17,axiom,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
        & v3_funct_2(X1,X0,X0)
        & v1_funct_2(X1,X0,X0)
        & v1_funct_1(X1) )
     => ( m1_subset_1(k2_funct_2(X0,X1),k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
        & v3_funct_2(k2_funct_2(X0,X1),X0,X0)
        & v1_funct_2(k2_funct_2(X0,X1),X0,X0)
        & v1_funct_1(k2_funct_2(X0,X1)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f42,plain,(
    ! [X0,X1] :
      ( ( m1_subset_1(k2_funct_2(X0,X1),k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
        & v3_funct_2(k2_funct_2(X0,X1),X0,X0)
        & v1_funct_2(k2_funct_2(X0,X1),X0,X0)
        & v1_funct_1(k2_funct_2(X0,X1)) )
      | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
      | ~ v3_funct_2(X1,X0,X0)
      | ~ v1_funct_2(X1,X0,X0)
      | ~ v1_funct_1(X1) ) ),
    inference(ennf_transformation,[],[f17])).

fof(f43,plain,(
    ! [X0,X1] :
      ( ( m1_subset_1(k2_funct_2(X0,X1),k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
        & v3_funct_2(k2_funct_2(X0,X1),X0,X0)
        & v1_funct_2(k2_funct_2(X0,X1),X0,X0)
        & v1_funct_1(k2_funct_2(X0,X1)) )
      | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
      | ~ v3_funct_2(X1,X0,X0)
      | ~ v1_funct_2(X1,X0,X0)
      | ~ v1_funct_1(X1) ) ),
    inference(flattening,[],[f42])).

fof(f80,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k2_funct_2(X0,X1),k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
      | ~ v3_funct_2(X1,X0,X0)
      | ~ v1_funct_2(X1,X0,X0)
      | ~ v1_funct_1(X1) ) ),
    inference(cnf_transformation,[],[f43])).

fof(f15,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => ( ( v3_funct_2(X2,X0,X1)
          & v1_funct_1(X2) )
       => ( v2_funct_2(X2,X1)
          & v2_funct_1(X2)
          & v1_funct_1(X2) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f38,plain,(
    ! [X0,X1,X2] :
      ( ( v2_funct_2(X2,X1)
        & v2_funct_1(X2)
        & v1_funct_1(X2) )
      | ~ v3_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f15])).

fof(f39,plain,(
    ! [X0,X1,X2] :
      ( ( v2_funct_2(X2,X1)
        & v2_funct_1(X2)
        & v1_funct_1(X2) )
      | ~ v3_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(flattening,[],[f38])).

fof(f74,plain,(
    ! [X2,X0,X1] :
      ( v2_funct_2(X2,X1)
      | ~ v3_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f39])).

fof(f16,axiom,(
    ! [X0,X1] :
      ( ( v5_relat_1(X1,X0)
        & v1_relat_1(X1) )
     => ( v2_funct_2(X1,X0)
      <=> k2_relat_1(X1) = X0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f40,plain,(
    ! [X0,X1] :
      ( ( v2_funct_2(X1,X0)
      <=> k2_relat_1(X1) = X0 )
      | ~ v5_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f16])).

fof(f41,plain,(
    ! [X0,X1] :
      ( ( v2_funct_2(X1,X0)
      <=> k2_relat_1(X1) = X0 )
      | ~ v5_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f40])).

fof(f51,plain,(
    ! [X0,X1] :
      ( ( ( v2_funct_2(X1,X0)
          | k2_relat_1(X1) != X0 )
        & ( k2_relat_1(X1) = X0
          | ~ v2_funct_2(X1,X0) ) )
      | ~ v5_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(nnf_transformation,[],[f41])).

fof(f75,plain,(
    ! [X0,X1] :
      ( k2_relat_1(X1) = X0
      | ~ v2_funct_2(X1,X0)
      | ~ v5_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f51])).

fof(f69,plain,(
    ! [X2,X0,X1] :
      ( v5_relat_1(X2,X1)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f35])).

fof(f4,axiom,(
    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f60,plain,(
    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1)) ),
    inference(cnf_transformation,[],[f4])).

fof(f77,plain,(
    ! [X0,X1] :
      ( v1_funct_1(k2_funct_2(X0,X1))
      | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
      | ~ v3_funct_2(X1,X0,X0)
      | ~ v1_funct_2(X1,X0,X0)
      | ~ v1_funct_1(X1) ) ),
    inference(cnf_transformation,[],[f43])).

fof(f79,plain,(
    ! [X0,X1] :
      ( v3_funct_2(k2_funct_2(X0,X1),X0,X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
      | ~ v3_funct_2(X1,X0,X0)
      | ~ v1_funct_2(X1,X0,X0)
      | ~ v1_funct_1(X1) ) ),
    inference(cnf_transformation,[],[f43])).

fof(f2,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(X0))
         => v1_relat_1(X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f21,plain,(
    ! [X0] :
      ( ! [X1] :
          ( v1_relat_1(X1)
          | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f57,plain,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f9,axiom,(
    ! [X0,X1] :
      ( ( v1_funct_1(X1)
        & v1_relat_1(X1) )
     => ( r1_tarski(X0,k2_relat_1(X1))
       => k9_relat_1(X1,k10_relat_1(X1,X0)) = X0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f29,plain,(
    ! [X0,X1] :
      ( k9_relat_1(X1,k10_relat_1(X1,X0)) = X0
      | ~ r1_tarski(X0,k2_relat_1(X1))
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f30,plain,(
    ! [X0,X1] :
      ( k9_relat_1(X1,k10_relat_1(X1,X0)) = X0
      | ~ r1_tarski(X0,k2_relat_1(X1))
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f29])).

fof(f65,plain,(
    ! [X0,X1] :
      ( k9_relat_1(X1,k10_relat_1(X1,X0)) = X0
      | ~ r1_tarski(X0,k2_relat_1(X1))
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f73,plain,(
    ! [X2,X0,X1] :
      ( v2_funct_1(X2)
      | ~ v3_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f39])).

fof(f10,axiom,(
    ! [X0,X1] :
      ( ( v1_funct_1(X1)
        & v1_relat_1(X1) )
     => ( v2_funct_1(X1)
       => k9_relat_1(X1,X0) = k10_relat_1(k2_funct_1(X1),X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f31,plain,(
    ! [X0,X1] :
      ( k9_relat_1(X1,X0) = k10_relat_1(k2_funct_1(X1),X0)
      | ~ v2_funct_1(X1)
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f32,plain,(
    ! [X0,X1] :
      ( k9_relat_1(X1,X0) = k10_relat_1(k2_funct_1(X1),X0)
      | ~ v2_funct_1(X1)
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f31])).

fof(f66,plain,(
    ! [X0,X1] :
      ( k9_relat_1(X1,X0) = k10_relat_1(k2_funct_1(X1),X0)
      | ~ v2_funct_1(X1)
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f32])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( X0 = X1
    <=> ( r1_tarski(X1,X0)
        & r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f48,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(nnf_transformation,[],[f1])).

fof(f49,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(flattening,[],[f48])).

fof(f55,plain,(
    ! [X0,X1] :
      ( r1_tarski(X1,X0)
      | X0 != X1 ) ),
    inference(cnf_transformation,[],[f49])).

fof(f88,plain,(
    ! [X1] : r1_tarski(X1,X1) ),
    inference(equality_resolution,[],[f55])).

fof(f6,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => k1_relat_1(X0) = k10_relat_1(X0,k2_relat_1(X0)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f24,plain,(
    ! [X0] :
      ( k1_relat_1(X0) = k10_relat_1(X0,k2_relat_1(X0))
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f62,plain,(
    ! [X0] :
      ( k1_relat_1(X0) = k10_relat_1(X0,k2_relat_1(X0))
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f7,axiom,(
    ! [X0,X1] :
      ( ( v4_relat_1(X1,X0)
        & v1_relat_1(X1) )
     => k7_relat_1(X1,X0) = X1 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f25,plain,(
    ! [X0,X1] :
      ( k7_relat_1(X1,X0) = X1
      | ~ v4_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f26,plain,(
    ! [X0,X1] :
      ( k7_relat_1(X1,X0) = X1
      | ~ v4_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f25])).

fof(f63,plain,(
    ! [X0,X1] :
      ( k7_relat_1(X1,X0) = X1
      | ~ v4_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f5,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => k2_relat_1(k7_relat_1(X1,X0)) = k9_relat_1(X1,X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f23,plain,(
    ! [X0,X1] :
      ( k2_relat_1(k7_relat_1(X1,X0)) = k9_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f61,plain,(
    ! [X0,X1] :
      ( k2_relat_1(k7_relat_1(X1,X0)) = k9_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f11,axiom,(
    ! [X0,X1] :
      ( ( v1_funct_1(X1)
        & v1_relat_1(X1) )
     => ( ( v2_funct_1(X1)
          & r1_tarski(X0,k1_relat_1(X1)) )
       => k10_relat_1(X1,k9_relat_1(X1,X0)) = X0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f33,plain,(
    ! [X0,X1] :
      ( k10_relat_1(X1,k9_relat_1(X1,X0)) = X0
      | ~ v2_funct_1(X1)
      | ~ r1_tarski(X0,k1_relat_1(X1))
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f34,plain,(
    ! [X0,X1] :
      ( k10_relat_1(X1,k9_relat_1(X1,X0)) = X0
      | ~ v2_funct_1(X1)
      | ~ r1_tarski(X0,k1_relat_1(X1))
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f33])).

fof(f67,plain,(
    ! [X0,X1] :
      ( k10_relat_1(X1,k9_relat_1(X1,X0)) = X0
      | ~ v2_funct_1(X1)
      | ~ r1_tarski(X0,k1_relat_1(X1))
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f34])).

fof(f14,axiom,(
    ! [X0,X1,X2,X3] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k10_relat_1(X2,X3) = k8_relset_1(X0,X1,X2,X3) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f37,plain,(
    ! [X0,X1,X2,X3] :
      ( k10_relat_1(X2,X3) = k8_relset_1(X0,X1,X2,X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f71,plain,(
    ! [X2,X0,X3,X1] :
      ( k10_relat_1(X2,X3) = k8_relset_1(X0,X1,X2,X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f37])).

fof(f87,plain,
    ( k8_relset_1(sK0,sK0,sK2,k7_relset_1(sK0,sK0,sK2,sK1)) != sK1
    | k7_relset_1(sK0,sK0,sK2,k8_relset_1(sK0,sK0,sK2,sK1)) != sK1 ),
    inference(cnf_transformation,[],[f53])).

fof(f13,axiom,(
    ! [X0,X1,X2,X3] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k9_relat_1(X2,X3) = k7_relset_1(X0,X1,X2,X3) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f36,plain,(
    ! [X0,X1,X2,X3] :
      ( k9_relat_1(X2,X3) = k7_relset_1(X0,X1,X2,X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f70,plain,(
    ! [X2,X0,X3,X1] :
      ( k9_relat_1(X2,X3) = k7_relset_1(X0,X1,X2,X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f36])).

cnf(c_29,negated_conjecture,
    ( r1_tarski(sK1,sK0) ),
    inference(cnf_transformation,[],[f86])).

cnf(c_1345,plain,
    ( r1_tarski(sK1,sK0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_29])).

cnf(c_30,negated_conjecture,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) ),
    inference(cnf_transformation,[],[f85])).

cnf(c_1344,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_30])).

cnf(c_15,plain,
    ( v4_relat_1(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) ),
    inference(cnf_transformation,[],[f68])).

cnf(c_1354,plain,
    ( v4_relat_1(X0,X1) = iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_15])).

cnf(c_1813,plain,
    ( v4_relat_1(sK2,sK0) = iProver_top ),
    inference(superposition,[status(thm)],[c_1344,c_1354])).

cnf(c_5,plain,
    ( ~ v4_relat_1(X0,X1)
    | r1_tarski(k1_relat_1(X0),X1)
    | ~ v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f58])).

cnf(c_1363,plain,
    ( v4_relat_1(X0,X1) != iProver_top
    | r1_tarski(k1_relat_1(X0),X1) = iProver_top
    | v1_relat_1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_5])).

cnf(c_27,plain,
    ( ~ v1_funct_2(X0,X1,X1)
    | ~ v3_funct_2(X0,X1,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X1)))
    | ~ v1_funct_1(X0)
    | k2_funct_2(X1,X0) = k2_funct_1(X0) ),
    inference(cnf_transformation,[],[f81])).

cnf(c_1346,plain,
    ( k2_funct_2(X0,X1) = k2_funct_1(X1)
    | v1_funct_2(X1,X0,X0) != iProver_top
    | v3_funct_2(X1,X0,X0) != iProver_top
    | m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) != iProver_top
    | v1_funct_1(X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_27])).

cnf(c_2387,plain,
    ( k2_funct_2(sK0,sK2) = k2_funct_1(sK2)
    | v1_funct_2(sK2,sK0,sK0) != iProver_top
    | v3_funct_2(sK2,sK0,sK0) != iProver_top
    | v1_funct_1(sK2) != iProver_top ),
    inference(superposition,[status(thm)],[c_1344,c_1346])).

cnf(c_33,negated_conjecture,
    ( v1_funct_1(sK2) ),
    inference(cnf_transformation,[],[f82])).

cnf(c_32,negated_conjecture,
    ( v1_funct_2(sK2,sK0,sK0) ),
    inference(cnf_transformation,[],[f83])).

cnf(c_31,negated_conjecture,
    ( v3_funct_2(sK2,sK0,sK0) ),
    inference(cnf_transformation,[],[f84])).

cnf(c_1708,plain,
    ( ~ v1_funct_2(sK2,X0,X0)
    | ~ v3_funct_2(sK2,X0,X0)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
    | ~ v1_funct_1(sK2)
    | k2_funct_2(X0,sK2) = k2_funct_1(sK2) ),
    inference(instantiation,[status(thm)],[c_27])).

cnf(c_1710,plain,
    ( ~ v1_funct_2(sK2,sK0,sK0)
    | ~ v3_funct_2(sK2,sK0,sK0)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
    | ~ v1_funct_1(sK2)
    | k2_funct_2(sK0,sK2) = k2_funct_1(sK2) ),
    inference(instantiation,[status(thm)],[c_1708])).

cnf(c_2923,plain,
    ( k2_funct_2(sK0,sK2) = k2_funct_1(sK2) ),
    inference(global_propositional_subsumption,[status(thm)],[c_2387,c_33,c_32,c_31,c_30,c_1710])).

cnf(c_23,plain,
    ( ~ v1_funct_2(X0,X1,X1)
    | ~ v3_funct_2(X0,X1,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X1)))
    | m1_subset_1(k2_funct_2(X1,X0),k1_zfmisc_1(k2_zfmisc_1(X1,X1)))
    | ~ v1_funct_1(X0) ),
    inference(cnf_transformation,[],[f80])).

cnf(c_1350,plain,
    ( v1_funct_2(X0,X1,X1) != iProver_top
    | v3_funct_2(X0,X1,X1) != iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X1))) != iProver_top
    | m1_subset_1(k2_funct_2(X1,X0),k1_zfmisc_1(k2_zfmisc_1(X1,X1))) = iProver_top
    | v1_funct_1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_23])).

cnf(c_4389,plain,
    ( v1_funct_2(sK2,sK0,sK0) != iProver_top
    | v3_funct_2(sK2,sK0,sK0) != iProver_top
    | m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) = iProver_top
    | m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) != iProver_top
    | v1_funct_1(sK2) != iProver_top ),
    inference(superposition,[status(thm)],[c_2923,c_1350])).

cnf(c_34,plain,
    ( v1_funct_1(sK2) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_33])).

cnf(c_35,plain,
    ( v1_funct_2(sK2,sK0,sK0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_32])).

cnf(c_36,plain,
    ( v3_funct_2(sK2,sK0,sK0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_31])).

cnf(c_37,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_30])).

cnf(c_4718,plain,
    ( m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_4389,c_34,c_35,c_36,c_37])).

cnf(c_18,plain,
    ( ~ v3_funct_2(X0,X1,X2)
    | v2_funct_2(X0,X2)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ v1_funct_1(X0) ),
    inference(cnf_transformation,[],[f74])).

cnf(c_22,plain,
    ( ~ v2_funct_2(X0,X1)
    | ~ v5_relat_1(X0,X1)
    | ~ v1_relat_1(X0)
    | k2_relat_1(X0) = X1 ),
    inference(cnf_transformation,[],[f75])).

cnf(c_402,plain,
    ( ~ v3_funct_2(X0,X1,X2)
    | ~ v5_relat_1(X3,X4)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ v1_funct_1(X0)
    | ~ v1_relat_1(X3)
    | X3 != X0
    | X4 != X2
    | k2_relat_1(X3) = X4 ),
    inference(resolution_lifted,[status(thm)],[c_18,c_22])).

cnf(c_403,plain,
    ( ~ v3_funct_2(X0,X1,X2)
    | ~ v5_relat_1(X0,X2)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ v1_funct_1(X0)
    | ~ v1_relat_1(X0)
    | k2_relat_1(X0) = X2 ),
    inference(unflattening,[status(thm)],[c_402])).

cnf(c_14,plain,
    ( v5_relat_1(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) ),
    inference(cnf_transformation,[],[f69])).

cnf(c_419,plain,
    ( ~ v3_funct_2(X0,X1,X2)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ v1_funct_1(X0)
    | ~ v1_relat_1(X0)
    | k2_relat_1(X0) = X2 ),
    inference(forward_subsumption_resolution,[status(thm)],[c_403,c_14])).

cnf(c_1340,plain,
    ( k2_relat_1(X0) = X1
    | v3_funct_2(X0,X2,X1) != iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) != iProver_top
    | v1_funct_1(X0) != iProver_top
    | v1_relat_1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_419])).

cnf(c_4726,plain,
    ( k2_relat_1(k2_funct_1(sK2)) = sK0
    | v3_funct_2(k2_funct_1(sK2),sK0,sK0) != iProver_top
    | v1_funct_1(k2_funct_1(sK2)) != iProver_top
    | v1_relat_1(k2_funct_1(sK2)) != iProver_top ),
    inference(superposition,[status(thm)],[c_4718,c_1340])).

cnf(c_6,plain,
    ( v1_relat_1(k2_zfmisc_1(X0,X1)) ),
    inference(cnf_transformation,[],[f60])).

cnf(c_100,plain,
    ( v1_relat_1(k2_zfmisc_1(X0,X1)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_6])).

cnf(c_102,plain,
    ( v1_relat_1(k2_zfmisc_1(sK0,sK0)) = iProver_top ),
    inference(instantiation,[status(thm)],[c_100])).

cnf(c_26,plain,
    ( ~ v1_funct_2(X0,X1,X1)
    | ~ v3_funct_2(X0,X1,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X1)))
    | ~ v1_funct_1(X0)
    | v1_funct_1(k2_funct_2(X1,X0)) ),
    inference(cnf_transformation,[],[f77])).

cnf(c_1347,plain,
    ( v1_funct_2(X0,X1,X1) != iProver_top
    | v3_funct_2(X0,X1,X1) != iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X1))) != iProver_top
    | v1_funct_1(X0) != iProver_top
    | v1_funct_1(k2_funct_2(X1,X0)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_26])).

cnf(c_3241,plain,
    ( v1_funct_2(sK2,sK0,sK0) != iProver_top
    | v3_funct_2(sK2,sK0,sK0) != iProver_top
    | v1_funct_1(k2_funct_2(sK0,sK2)) = iProver_top
    | v1_funct_1(sK2) != iProver_top ),
    inference(superposition,[status(thm)],[c_1344,c_1347])).

cnf(c_3242,plain,
    ( v1_funct_2(sK2,sK0,sK0) != iProver_top
    | v3_funct_2(sK2,sK0,sK0) != iProver_top
    | v1_funct_1(k2_funct_1(sK2)) = iProver_top
    | v1_funct_1(sK2) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_3241,c_2923])).

cnf(c_24,plain,
    ( ~ v1_funct_2(X0,X1,X1)
    | ~ v3_funct_2(X0,X1,X1)
    | v3_funct_2(k2_funct_2(X1,X0),X1,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X1)))
    | ~ v1_funct_1(X0) ),
    inference(cnf_transformation,[],[f79])).

cnf(c_1349,plain,
    ( v1_funct_2(X0,X1,X1) != iProver_top
    | v3_funct_2(X0,X1,X1) != iProver_top
    | v3_funct_2(k2_funct_2(X1,X0),X1,X1) = iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X1))) != iProver_top
    | v1_funct_1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_24])).

cnf(c_4380,plain,
    ( v1_funct_2(sK2,sK0,sK0) != iProver_top
    | v3_funct_2(k2_funct_2(sK0,sK2),sK0,sK0) = iProver_top
    | v3_funct_2(sK2,sK0,sK0) != iProver_top
    | v1_funct_1(sK2) != iProver_top ),
    inference(superposition,[status(thm)],[c_1344,c_1349])).

cnf(c_4381,plain,
    ( v1_funct_2(sK2,sK0,sK0) != iProver_top
    | v3_funct_2(k2_funct_1(sK2),sK0,sK0) = iProver_top
    | v3_funct_2(sK2,sK0,sK0) != iProver_top
    | v1_funct_1(sK2) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_4380,c_2923])).

cnf(c_3,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | ~ v1_relat_1(X1)
    | v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f57])).

cnf(c_1365,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(X1)) != iProver_top
    | v1_relat_1(X1) != iProver_top
    | v1_relat_1(X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3])).

cnf(c_4723,plain,
    ( v1_relat_1(k2_zfmisc_1(sK0,sK0)) != iProver_top
    | v1_relat_1(k2_funct_1(sK2)) = iProver_top ),
    inference(superposition,[status(thm)],[c_4718,c_1365])).

cnf(c_6657,plain,
    ( k2_relat_1(k2_funct_1(sK2)) = sK0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_4726,c_34,c_35,c_36,c_102,c_3242,c_4381,c_4723])).

cnf(c_11,plain,
    ( ~ r1_tarski(X0,k2_relat_1(X1))
    | ~ v1_funct_1(X1)
    | ~ v1_relat_1(X1)
    | k9_relat_1(X1,k10_relat_1(X1,X0)) = X0 ),
    inference(cnf_transformation,[],[f65])).

cnf(c_1357,plain,
    ( k9_relat_1(X0,k10_relat_1(X0,X1)) = X1
    | r1_tarski(X1,k2_relat_1(X0)) != iProver_top
    | v1_funct_1(X0) != iProver_top
    | v1_relat_1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_11])).

cnf(c_6670,plain,
    ( k9_relat_1(k2_funct_1(sK2),k10_relat_1(k2_funct_1(sK2),X0)) = X0
    | r1_tarski(X0,sK0) != iProver_top
    | v1_funct_1(k2_funct_1(sK2)) != iProver_top
    | v1_relat_1(k2_funct_1(sK2)) != iProver_top ),
    inference(superposition,[status(thm)],[c_6657,c_1357])).

cnf(c_19,plain,
    ( ~ v3_funct_2(X0,X1,X2)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | v2_funct_1(X0)
    | ~ v1_funct_1(X0) ),
    inference(cnf_transformation,[],[f73])).

cnf(c_1351,plain,
    ( v3_funct_2(X0,X1,X2) != iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) != iProver_top
    | v2_funct_1(X0) = iProver_top
    | v1_funct_1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_19])).

cnf(c_3840,plain,
    ( v3_funct_2(sK2,sK0,sK0) != iProver_top
    | v2_funct_1(sK2) = iProver_top
    | v1_funct_1(sK2) != iProver_top ),
    inference(superposition,[status(thm)],[c_1344,c_1351])).

cnf(c_1669,plain,
    ( ~ v3_funct_2(sK2,X0,X1)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
    | v2_funct_1(sK2)
    | ~ v1_funct_1(sK2) ),
    inference(instantiation,[status(thm)],[c_19])).

cnf(c_1670,plain,
    ( v3_funct_2(sK2,X0,X1) != iProver_top
    | m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top
    | v2_funct_1(sK2) = iProver_top
    | v1_funct_1(sK2) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1669])).

cnf(c_1672,plain,
    ( v3_funct_2(sK2,sK0,sK0) != iProver_top
    | m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) != iProver_top
    | v2_funct_1(sK2) = iProver_top
    | v1_funct_1(sK2) != iProver_top ),
    inference(instantiation,[status(thm)],[c_1670])).

cnf(c_3843,plain,
    ( v2_funct_1(sK2) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_3840,c_34,c_36,c_37,c_1672])).

cnf(c_12,plain,
    ( ~ v2_funct_1(X0)
    | ~ v1_funct_1(X0)
    | ~ v1_relat_1(X0)
    | k10_relat_1(k2_funct_1(X0),X1) = k9_relat_1(X0,X1) ),
    inference(cnf_transformation,[],[f66])).

cnf(c_1356,plain,
    ( k10_relat_1(k2_funct_1(X0),X1) = k9_relat_1(X0,X1)
    | v2_funct_1(X0) != iProver_top
    | v1_funct_1(X0) != iProver_top
    | v1_relat_1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_12])).

cnf(c_3848,plain,
    ( k10_relat_1(k2_funct_1(sK2),X0) = k9_relat_1(sK2,X0)
    | v1_funct_1(sK2) != iProver_top
    | v1_relat_1(sK2) != iProver_top ),
    inference(superposition,[status(thm)],[c_3843,c_1356])).

cnf(c_101,plain,
    ( v1_relat_1(k2_zfmisc_1(sK0,sK0)) ),
    inference(instantiation,[status(thm)],[c_6])).

cnf(c_1671,plain,
    ( ~ v3_funct_2(sK2,sK0,sK0)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
    | v2_funct_1(sK2)
    | ~ v1_funct_1(sK2) ),
    inference(instantiation,[status(thm)],[c_1669])).

cnf(c_1598,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | v1_relat_1(X0)
    | ~ v1_relat_1(k2_zfmisc_1(X1,X2)) ),
    inference(instantiation,[status(thm)],[c_3])).

cnf(c_1765,plain,
    ( ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
    | ~ v1_relat_1(k2_zfmisc_1(sK0,sK0))
    | v1_relat_1(sK2) ),
    inference(instantiation,[status(thm)],[c_1598])).

cnf(c_1784,plain,
    ( ~ v2_funct_1(sK2)
    | ~ v1_funct_1(sK2)
    | ~ v1_relat_1(sK2)
    | k10_relat_1(k2_funct_1(sK2),X0) = k9_relat_1(sK2,X0) ),
    inference(instantiation,[status(thm)],[c_12])).

cnf(c_3937,plain,
    ( k10_relat_1(k2_funct_1(sK2),X0) = k9_relat_1(sK2,X0) ),
    inference(global_propositional_subsumption,[status(thm)],[c_3848,c_33,c_31,c_30,c_101,c_1671,c_1765,c_1784])).

cnf(c_6671,plain,
    ( k9_relat_1(k2_funct_1(sK2),k9_relat_1(sK2,X0)) = X0
    | r1_tarski(X0,sK0) != iProver_top
    | v1_funct_1(k2_funct_1(sK2)) != iProver_top
    | v1_relat_1(k2_funct_1(sK2)) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_6670,c_3937])).

cnf(c_6800,plain,
    ( k9_relat_1(k2_funct_1(sK2),k9_relat_1(sK2,X0)) = X0
    | r1_tarski(X0,sK0) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_6671,c_34,c_35,c_36,c_102,c_3242,c_4723])).

cnf(c_6809,plain,
    ( k9_relat_1(k2_funct_1(sK2),k9_relat_1(sK2,k1_relat_1(X0))) = k1_relat_1(X0)
    | v4_relat_1(X0,sK0) != iProver_top
    | v1_relat_1(X0) != iProver_top ),
    inference(superposition,[status(thm)],[c_1363,c_6800])).

cnf(c_8212,plain,
    ( k9_relat_1(k2_funct_1(sK2),k9_relat_1(sK2,k1_relat_1(sK2))) = k1_relat_1(sK2)
    | v1_relat_1(sK2) != iProver_top ),
    inference(superposition,[status(thm)],[c_1813,c_6809])).

cnf(c_1,plain,
    ( r1_tarski(X0,X0) ),
    inference(cnf_transformation,[],[f88])).

cnf(c_1366,plain,
    ( r1_tarski(X0,X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1])).

cnf(c_1758,plain,
    ( k2_relat_1(sK2) = sK0
    | v3_funct_2(sK2,sK0,sK0) != iProver_top
    | v1_funct_1(sK2) != iProver_top
    | v1_relat_1(sK2) != iProver_top ),
    inference(superposition,[status(thm)],[c_1344,c_1340])).

cnf(c_1759,plain,
    ( ~ v3_funct_2(sK2,sK0,sK0)
    | ~ v1_funct_1(sK2)
    | ~ v1_relat_1(sK2)
    | k2_relat_1(sK2) = sK0 ),
    inference(predicate_to_equality_rev,[status(thm)],[c_1758])).

cnf(c_2132,plain,
    ( k2_relat_1(sK2) = sK0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_1758,c_33,c_31,c_30,c_101,c_1759,c_1765])).

cnf(c_3690,plain,
    ( k9_relat_1(sK2,k10_relat_1(sK2,X0)) = X0
    | r1_tarski(X0,sK0) != iProver_top
    | v1_funct_1(sK2) != iProver_top
    | v1_relat_1(sK2) != iProver_top ),
    inference(superposition,[status(thm)],[c_2132,c_1357])).

cnf(c_1766,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) != iProver_top
    | v1_relat_1(k2_zfmisc_1(sK0,sK0)) != iProver_top
    | v1_relat_1(sK2) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1765])).

cnf(c_3946,plain,
    ( k9_relat_1(sK2,k10_relat_1(sK2,X0)) = X0
    | r1_tarski(X0,sK0) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_3690,c_34,c_37,c_102,c_1766])).

cnf(c_3954,plain,
    ( k9_relat_1(sK2,k10_relat_1(sK2,sK0)) = sK0 ),
    inference(superposition,[status(thm)],[c_1366,c_3946])).

cnf(c_2379,plain,
    ( v1_relat_1(k2_zfmisc_1(sK0,sK0)) != iProver_top
    | v1_relat_1(sK2) = iProver_top ),
    inference(superposition,[status(thm)],[c_1344,c_1365])).

cnf(c_2842,plain,
    ( v1_relat_1(sK2) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_2379,c_37,c_102,c_1766])).

cnf(c_8,plain,
    ( ~ v1_relat_1(X0)
    | k10_relat_1(X0,k2_relat_1(X0)) = k1_relat_1(X0) ),
    inference(cnf_transformation,[],[f62])).

cnf(c_1360,plain,
    ( k10_relat_1(X0,k2_relat_1(X0)) = k1_relat_1(X0)
    | v1_relat_1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_8])).

cnf(c_2848,plain,
    ( k10_relat_1(sK2,k2_relat_1(sK2)) = k1_relat_1(sK2) ),
    inference(superposition,[status(thm)],[c_2842,c_1360])).

cnf(c_2850,plain,
    ( k10_relat_1(sK2,sK0) = k1_relat_1(sK2) ),
    inference(light_normalisation,[status(thm)],[c_2848,c_2132])).

cnf(c_3973,plain,
    ( k9_relat_1(sK2,k1_relat_1(sK2)) = sK0 ),
    inference(light_normalisation,[status(thm)],[c_3954,c_2850])).

cnf(c_6808,plain,
    ( k9_relat_1(k2_funct_1(sK2),k9_relat_1(sK2,sK0)) = sK0 ),
    inference(superposition,[status(thm)],[c_1366,c_6800])).

cnf(c_9,plain,
    ( ~ v4_relat_1(X0,X1)
    | ~ v1_relat_1(X0)
    | k7_relat_1(X0,X1) = X0 ),
    inference(cnf_transformation,[],[f63])).

cnf(c_1359,plain,
    ( k7_relat_1(X0,X1) = X0
    | v4_relat_1(X0,X1) != iProver_top
    | v1_relat_1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_9])).

cnf(c_2292,plain,
    ( k7_relat_1(sK2,sK0) = sK2
    | v1_relat_1(sK2) != iProver_top ),
    inference(superposition,[status(thm)],[c_1813,c_1359])).

cnf(c_1632,plain,
    ( v4_relat_1(sK2,sK0)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) ),
    inference(instantiation,[status(thm)],[c_15])).

cnf(c_1885,plain,
    ( ~ v4_relat_1(sK2,X0)
    | ~ v1_relat_1(sK2)
    | k7_relat_1(sK2,X0) = sK2 ),
    inference(instantiation,[status(thm)],[c_9])).

cnf(c_1903,plain,
    ( ~ v4_relat_1(sK2,sK0)
    | ~ v1_relat_1(sK2)
    | k7_relat_1(sK2,sK0) = sK2 ),
    inference(instantiation,[status(thm)],[c_1885])).

cnf(c_2295,plain,
    ( k7_relat_1(sK2,sK0) = sK2 ),
    inference(global_propositional_subsumption,[status(thm)],[c_2292,c_30,c_101,c_1632,c_1765,c_1903])).

cnf(c_7,plain,
    ( ~ v1_relat_1(X0)
    | k2_relat_1(k7_relat_1(X0,X1)) = k9_relat_1(X0,X1) ),
    inference(cnf_transformation,[],[f61])).

cnf(c_1361,plain,
    ( k2_relat_1(k7_relat_1(X0,X1)) = k9_relat_1(X0,X1)
    | v1_relat_1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_7])).

cnf(c_2847,plain,
    ( k2_relat_1(k7_relat_1(sK2,X0)) = k9_relat_1(sK2,X0) ),
    inference(superposition,[status(thm)],[c_2842,c_1361])).

cnf(c_3052,plain,
    ( k9_relat_1(sK2,sK0) = k2_relat_1(sK2) ),
    inference(superposition,[status(thm)],[c_2295,c_2847])).

cnf(c_3053,plain,
    ( k9_relat_1(sK2,sK0) = sK0 ),
    inference(light_normalisation,[status(thm)],[c_3052,c_2132])).

cnf(c_6833,plain,
    ( k9_relat_1(k2_funct_1(sK2),sK0) = sK0 ),
    inference(light_normalisation,[status(thm)],[c_6808,c_3053])).

cnf(c_8224,plain,
    ( k1_relat_1(sK2) = sK0
    | v1_relat_1(sK2) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_8212,c_3973,c_6833])).

cnf(c_8724,plain,
    ( k1_relat_1(sK2) = sK0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_8224,c_37,c_102,c_1766])).

cnf(c_13,plain,
    ( ~ r1_tarski(X0,k1_relat_1(X1))
    | ~ v2_funct_1(X1)
    | ~ v1_funct_1(X1)
    | ~ v1_relat_1(X1)
    | k10_relat_1(X1,k9_relat_1(X1,X0)) = X0 ),
    inference(cnf_transformation,[],[f67])).

cnf(c_1355,plain,
    ( k10_relat_1(X0,k9_relat_1(X0,X1)) = X1
    | r1_tarski(X1,k1_relat_1(X0)) != iProver_top
    | v2_funct_1(X0) != iProver_top
    | v1_funct_1(X0) != iProver_top
    | v1_relat_1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_13])).

cnf(c_8746,plain,
    ( k10_relat_1(sK2,k9_relat_1(sK2,X0)) = X0
    | r1_tarski(X0,sK0) != iProver_top
    | v2_funct_1(sK2) != iProver_top
    | v1_funct_1(sK2) != iProver_top
    | v1_relat_1(sK2) != iProver_top ),
    inference(superposition,[status(thm)],[c_8724,c_1355])).

cnf(c_11223,plain,
    ( r1_tarski(X0,sK0) != iProver_top
    | k10_relat_1(sK2,k9_relat_1(sK2,X0)) = X0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_8746,c_34,c_36,c_37,c_102,c_1672,c_1766])).

cnf(c_11224,plain,
    ( k10_relat_1(sK2,k9_relat_1(sK2,X0)) = X0
    | r1_tarski(X0,sK0) != iProver_top ),
    inference(renaming,[status(thm)],[c_11223])).

cnf(c_11234,plain,
    ( k10_relat_1(sK2,k9_relat_1(sK2,sK1)) = sK1 ),
    inference(superposition,[status(thm)],[c_1345,c_11224])).

cnf(c_3957,plain,
    ( k9_relat_1(sK2,k10_relat_1(sK2,sK1)) = sK1 ),
    inference(superposition,[status(thm)],[c_1345,c_3946])).

cnf(c_17,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k8_relset_1(X1,X2,X0,X3) = k10_relat_1(X0,X3) ),
    inference(cnf_transformation,[],[f71])).

cnf(c_1352,plain,
    ( k8_relset_1(X0,X1,X2,X3) = k10_relat_1(X2,X3)
    | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_17])).

cnf(c_2497,plain,
    ( k8_relset_1(sK0,sK0,sK2,X0) = k10_relat_1(sK2,X0) ),
    inference(superposition,[status(thm)],[c_1344,c_1352])).

cnf(c_28,negated_conjecture,
    ( k8_relset_1(sK0,sK0,sK2,k7_relset_1(sK0,sK0,sK2,sK1)) != sK1
    | k7_relset_1(sK0,sK0,sK2,k8_relset_1(sK0,sK0,sK2,sK1)) != sK1 ),
    inference(cnf_transformation,[],[f87])).

cnf(c_2783,plain,
    ( k7_relset_1(sK0,sK0,sK2,k8_relset_1(sK0,sK0,sK2,sK1)) != sK1
    | k10_relat_1(sK2,k7_relset_1(sK0,sK0,sK2,sK1)) != sK1 ),
    inference(demodulation,[status(thm)],[c_2497,c_28])).

cnf(c_2784,plain,
    ( k7_relset_1(sK0,sK0,sK2,k10_relat_1(sK2,sK1)) != sK1
    | k10_relat_1(sK2,k7_relset_1(sK0,sK0,sK2,sK1)) != sK1 ),
    inference(demodulation,[status(thm)],[c_2783,c_2497])).

cnf(c_16,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k7_relset_1(X1,X2,X0,X3) = k9_relat_1(X0,X3) ),
    inference(cnf_transformation,[],[f70])).

cnf(c_1353,plain,
    ( k7_relset_1(X0,X1,X2,X3) = k9_relat_1(X2,X3)
    | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_16])).

cnf(c_2502,plain,
    ( k7_relset_1(sK0,sK0,sK2,X0) = k9_relat_1(sK2,X0) ),
    inference(superposition,[status(thm)],[c_1344,c_1353])).

cnf(c_2855,plain,
    ( k10_relat_1(sK2,k9_relat_1(sK2,sK1)) != sK1
    | k9_relat_1(sK2,k10_relat_1(sK2,sK1)) != sK1 ),
    inference(demodulation,[status(thm)],[c_2784,c_2502])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_11234,c_3957,c_2855])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : iproveropt_run.sh %d %s
% 0.13/0.34  % Computer   : n021.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 11:20:04 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running in FOF mode
% 3.33/1.01  % SZS status Started for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.33/1.01  
% 3.33/1.01  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 3.33/1.01  
% 3.33/1.01  ------  iProver source info
% 3.33/1.01  
% 3.33/1.01  git: date: 2020-06-30 10:37:57 +0100
% 3.33/1.01  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 3.33/1.01  git: non_committed_changes: false
% 3.33/1.01  git: last_make_outside_of_git: false
% 3.33/1.01  
% 3.33/1.01  ------ 
% 3.33/1.01  
% 3.33/1.01  ------ Input Options
% 3.33/1.01  
% 3.33/1.01  --out_options                           all
% 3.33/1.01  --tptp_safe_out                         true
% 3.33/1.01  --problem_path                          ""
% 3.33/1.01  --include_path                          ""
% 3.33/1.01  --clausifier                            res/vclausify_rel
% 3.33/1.01  --clausifier_options                    --mode clausify
% 3.33/1.01  --stdin                                 false
% 3.33/1.01  --stats_out                             all
% 3.33/1.01  
% 3.33/1.01  ------ General Options
% 3.33/1.01  
% 3.33/1.01  --fof                                   false
% 3.33/1.01  --time_out_real                         305.
% 3.33/1.01  --time_out_virtual                      -1.
% 3.33/1.01  --symbol_type_check                     false
% 3.33/1.01  --clausify_out                          false
% 3.33/1.01  --sig_cnt_out                           false
% 3.33/1.01  --trig_cnt_out                          false
% 3.33/1.01  --trig_cnt_out_tolerance                1.
% 3.33/1.01  --trig_cnt_out_sk_spl                   false
% 3.33/1.01  --abstr_cl_out                          false
% 3.33/1.01  
% 3.33/1.01  ------ Global Options
% 3.33/1.01  
% 3.33/1.01  --schedule                              default
% 3.33/1.01  --add_important_lit                     false
% 3.33/1.01  --prop_solver_per_cl                    1000
% 3.33/1.01  --min_unsat_core                        false
% 3.33/1.01  --soft_assumptions                      false
% 3.33/1.01  --soft_lemma_size                       3
% 3.33/1.01  --prop_impl_unit_size                   0
% 3.33/1.01  --prop_impl_unit                        []
% 3.33/1.01  --share_sel_clauses                     true
% 3.33/1.01  --reset_solvers                         false
% 3.33/1.01  --bc_imp_inh                            [conj_cone]
% 3.33/1.01  --conj_cone_tolerance                   3.
% 3.33/1.01  --extra_neg_conj                        none
% 3.33/1.01  --large_theory_mode                     true
% 3.33/1.01  --prolific_symb_bound                   200
% 3.33/1.01  --lt_threshold                          2000
% 3.33/1.01  --clause_weak_htbl                      true
% 3.33/1.01  --gc_record_bc_elim                     false
% 3.33/1.01  
% 3.33/1.01  ------ Preprocessing Options
% 3.33/1.01  
% 3.33/1.01  --preprocessing_flag                    true
% 3.33/1.01  --time_out_prep_mult                    0.1
% 3.33/1.01  --splitting_mode                        input
% 3.33/1.01  --splitting_grd                         true
% 3.33/1.01  --splitting_cvd                         false
% 3.33/1.01  --splitting_cvd_svl                     false
% 3.33/1.01  --splitting_nvd                         32
% 3.33/1.01  --sub_typing                            true
% 3.33/1.01  --prep_gs_sim                           true
% 3.33/1.01  --prep_unflatten                        true
% 3.33/1.01  --prep_res_sim                          true
% 3.33/1.01  --prep_upred                            true
% 3.33/1.01  --prep_sem_filter                       exhaustive
% 3.33/1.01  --prep_sem_filter_out                   false
% 3.33/1.01  --pred_elim                             true
% 3.33/1.01  --res_sim_input                         true
% 3.33/1.01  --eq_ax_congr_red                       true
% 3.33/1.01  --pure_diseq_elim                       true
% 3.33/1.01  --brand_transform                       false
% 3.33/1.01  --non_eq_to_eq                          false
% 3.33/1.01  --prep_def_merge                        true
% 3.33/1.01  --prep_def_merge_prop_impl              false
% 3.33/1.01  --prep_def_merge_mbd                    true
% 3.33/1.01  --prep_def_merge_tr_red                 false
% 3.33/1.01  --prep_def_merge_tr_cl                  false
% 3.33/1.01  --smt_preprocessing                     true
% 3.33/1.01  --smt_ac_axioms                         fast
% 3.33/1.01  --preprocessed_out                      false
% 3.33/1.01  --preprocessed_stats                    false
% 3.33/1.01  
% 3.33/1.01  ------ Abstraction refinement Options
% 3.33/1.01  
% 3.33/1.01  --abstr_ref                             []
% 3.33/1.01  --abstr_ref_prep                        false
% 3.33/1.01  --abstr_ref_until_sat                   false
% 3.33/1.01  --abstr_ref_sig_restrict                funpre
% 3.33/1.01  --abstr_ref_af_restrict_to_split_sk     false
% 3.33/1.01  --abstr_ref_under                       []
% 3.33/1.01  
% 3.33/1.01  ------ SAT Options
% 3.33/1.01  
% 3.33/1.01  --sat_mode                              false
% 3.33/1.01  --sat_fm_restart_options                ""
% 3.33/1.01  --sat_gr_def                            false
% 3.33/1.01  --sat_epr_types                         true
% 3.33/1.01  --sat_non_cyclic_types                  false
% 3.33/1.01  --sat_finite_models                     false
% 3.33/1.01  --sat_fm_lemmas                         false
% 3.33/1.01  --sat_fm_prep                           false
% 3.33/1.01  --sat_fm_uc_incr                        true
% 3.33/1.01  --sat_out_model                         small
% 3.33/1.01  --sat_out_clauses                       false
% 3.33/1.01  
% 3.33/1.01  ------ QBF Options
% 3.33/1.01  
% 3.33/1.01  --qbf_mode                              false
% 3.33/1.01  --qbf_elim_univ                         false
% 3.33/1.01  --qbf_dom_inst                          none
% 3.33/1.01  --qbf_dom_pre_inst                      false
% 3.33/1.01  --qbf_sk_in                             false
% 3.33/1.01  --qbf_pred_elim                         true
% 3.33/1.01  --qbf_split                             512
% 3.33/1.01  
% 3.33/1.01  ------ BMC1 Options
% 3.33/1.01  
% 3.33/1.01  --bmc1_incremental                      false
% 3.33/1.01  --bmc1_axioms                           reachable_all
% 3.33/1.01  --bmc1_min_bound                        0
% 3.33/1.01  --bmc1_max_bound                        -1
% 3.33/1.01  --bmc1_max_bound_default                -1
% 3.33/1.01  --bmc1_symbol_reachability              true
% 3.33/1.01  --bmc1_property_lemmas                  false
% 3.33/1.01  --bmc1_k_induction                      false
% 3.33/1.01  --bmc1_non_equiv_states                 false
% 3.33/1.01  --bmc1_deadlock                         false
% 3.33/1.01  --bmc1_ucm                              false
% 3.33/1.01  --bmc1_add_unsat_core                   none
% 3.33/1.01  --bmc1_unsat_core_children              false
% 3.33/1.01  --bmc1_unsat_core_extrapolate_axioms    false
% 3.33/1.01  --bmc1_out_stat                         full
% 3.33/1.01  --bmc1_ground_init                      false
% 3.33/1.01  --bmc1_pre_inst_next_state              false
% 3.33/1.01  --bmc1_pre_inst_state                   false
% 3.33/1.01  --bmc1_pre_inst_reach_state             false
% 3.33/1.01  --bmc1_out_unsat_core                   false
% 3.33/1.01  --bmc1_aig_witness_out                  false
% 3.33/1.01  --bmc1_verbose                          false
% 3.33/1.01  --bmc1_dump_clauses_tptp                false
% 3.33/1.01  --bmc1_dump_unsat_core_tptp             false
% 3.33/1.01  --bmc1_dump_file                        -
% 3.33/1.01  --bmc1_ucm_expand_uc_limit              128
% 3.33/1.01  --bmc1_ucm_n_expand_iterations          6
% 3.33/1.01  --bmc1_ucm_extend_mode                  1
% 3.33/1.01  --bmc1_ucm_init_mode                    2
% 3.33/1.01  --bmc1_ucm_cone_mode                    none
% 3.33/1.01  --bmc1_ucm_reduced_relation_type        0
% 3.33/1.01  --bmc1_ucm_relax_model                  4
% 3.33/1.01  --bmc1_ucm_full_tr_after_sat            true
% 3.33/1.01  --bmc1_ucm_expand_neg_assumptions       false
% 3.33/1.01  --bmc1_ucm_layered_model                none
% 3.33/1.01  --bmc1_ucm_max_lemma_size               10
% 3.33/1.01  
% 3.33/1.01  ------ AIG Options
% 3.33/1.01  
% 3.33/1.01  --aig_mode                              false
% 3.33/1.01  
% 3.33/1.01  ------ Instantiation Options
% 3.33/1.01  
% 3.33/1.01  --instantiation_flag                    true
% 3.33/1.01  --inst_sos_flag                         false
% 3.33/1.01  --inst_sos_phase                        true
% 3.33/1.01  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 3.33/1.01  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 3.33/1.01  --inst_lit_sel_side                     num_symb
% 3.33/1.01  --inst_solver_per_active                1400
% 3.33/1.01  --inst_solver_calls_frac                1.
% 3.33/1.01  --inst_passive_queue_type               priority_queues
% 3.33/1.01  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 3.33/1.01  --inst_passive_queues_freq              [25;2]
% 3.33/1.01  --inst_dismatching                      true
% 3.33/1.01  --inst_eager_unprocessed_to_passive     true
% 3.33/1.01  --inst_prop_sim_given                   true
% 3.33/1.01  --inst_prop_sim_new                     false
% 3.33/1.01  --inst_subs_new                         false
% 3.33/1.01  --inst_eq_res_simp                      false
% 3.33/1.01  --inst_subs_given                       false
% 3.33/1.01  --inst_orphan_elimination               true
% 3.33/1.01  --inst_learning_loop_flag               true
% 3.33/1.01  --inst_learning_start                   3000
% 3.33/1.01  --inst_learning_factor                  2
% 3.33/1.01  --inst_start_prop_sim_after_learn       3
% 3.33/1.01  --inst_sel_renew                        solver
% 3.33/1.01  --inst_lit_activity_flag                true
% 3.33/1.01  --inst_restr_to_given                   false
% 3.33/1.01  --inst_activity_threshold               500
% 3.33/1.01  --inst_out_proof                        true
% 3.33/1.01  
% 3.33/1.01  ------ Resolution Options
% 3.33/1.01  
% 3.33/1.01  --resolution_flag                       true
% 3.33/1.01  --res_lit_sel                           adaptive
% 3.33/1.01  --res_lit_sel_side                      none
% 3.33/1.01  --res_ordering                          kbo
% 3.33/1.01  --res_to_prop_solver                    active
% 3.33/1.01  --res_prop_simpl_new                    false
% 3.33/1.01  --res_prop_simpl_given                  true
% 3.33/1.01  --res_passive_queue_type                priority_queues
% 3.33/1.01  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 3.33/1.01  --res_passive_queues_freq               [15;5]
% 3.33/1.01  --res_forward_subs                      full
% 3.33/1.01  --res_backward_subs                     full
% 3.33/1.01  --res_forward_subs_resolution           true
% 3.33/1.01  --res_backward_subs_resolution          true
% 3.33/1.01  --res_orphan_elimination                true
% 3.33/1.01  --res_time_limit                        2.
% 3.33/1.01  --res_out_proof                         true
% 3.33/1.01  
% 3.33/1.01  ------ Superposition Options
% 3.33/1.01  
% 3.33/1.01  --superposition_flag                    true
% 3.33/1.01  --sup_passive_queue_type                priority_queues
% 3.33/1.01  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 3.33/1.01  --sup_passive_queues_freq               [8;1;4]
% 3.33/1.01  --demod_completeness_check              fast
% 3.33/1.01  --demod_use_ground                      true
% 3.33/1.01  --sup_to_prop_solver                    passive
% 3.33/1.01  --sup_prop_simpl_new                    true
% 3.33/1.01  --sup_prop_simpl_given                  true
% 3.33/1.01  --sup_fun_splitting                     false
% 3.33/1.01  --sup_smt_interval                      50000
% 3.33/1.01  
% 3.33/1.01  ------ Superposition Simplification Setup
% 3.33/1.01  
% 3.33/1.01  --sup_indices_passive                   []
% 3.33/1.01  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.33/1.01  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.33/1.01  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.33/1.01  --sup_full_triv                         [TrivRules;PropSubs]
% 3.33/1.01  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.33/1.01  --sup_full_bw                           [BwDemod]
% 3.33/1.01  --sup_immed_triv                        [TrivRules]
% 3.33/1.01  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 3.33/1.01  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.33/1.01  --sup_immed_bw_main                     []
% 3.33/1.01  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 3.33/1.01  --sup_input_triv                        [Unflattening;TrivRules]
% 3.33/1.01  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.33/1.01  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 3.33/1.01  
% 3.33/1.01  ------ Combination Options
% 3.33/1.01  
% 3.33/1.01  --comb_res_mult                         3
% 3.33/1.01  --comb_sup_mult                         2
% 3.33/1.01  --comb_inst_mult                        10
% 3.33/1.01  
% 3.33/1.01  ------ Debug Options
% 3.33/1.01  
% 3.33/1.01  --dbg_backtrace                         false
% 3.33/1.01  --dbg_dump_prop_clauses                 false
% 3.33/1.01  --dbg_dump_prop_clauses_file            -
% 3.33/1.01  --dbg_out_stat                          false
% 3.33/1.01  ------ Parsing...
% 3.33/1.01  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 3.33/1.01  
% 3.33/1.01  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe:1:0s pe:2:0s pe_e  sf_s  rm: 3 0s  sf_e  pe_s  pe_e 
% 3.33/1.01  
% 3.33/1.01  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 3.33/1.01  
% 3.33/1.01  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 3.33/1.01  ------ Proving...
% 3.33/1.01  ------ Problem Properties 
% 3.33/1.01  
% 3.33/1.01  
% 3.33/1.01  clauses                                 29
% 3.33/1.01  conjectures                             6
% 3.33/1.01  EPR                                     6
% 3.33/1.01  Horn                                    29
% 3.33/1.01  unary                                   7
% 3.33/1.01  binary                                  6
% 3.33/1.01  lits                                    84
% 3.33/1.01  lits eq                                 13
% 3.33/1.01  fd_pure                                 0
% 3.33/1.01  fd_pseudo                               0
% 3.33/1.01  fd_cond                                 0
% 3.33/1.01  fd_pseudo_cond                          2
% 3.33/1.01  AC symbols                              0
% 3.33/1.01  
% 3.33/1.01  ------ Schedule dynamic 5 is on 
% 3.33/1.01  
% 3.33/1.01  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" Time Limit: 10.
% 3.33/1.01  
% 3.33/1.01  
% 3.33/1.01  ------ 
% 3.33/1.01  Current options:
% 3.33/1.01  ------ 
% 3.33/1.01  
% 3.33/1.01  ------ Input Options
% 3.33/1.01  
% 3.33/1.01  --out_options                           all
% 3.33/1.01  --tptp_safe_out                         true
% 3.33/1.01  --problem_path                          ""
% 3.33/1.01  --include_path                          ""
% 3.33/1.01  --clausifier                            res/vclausify_rel
% 3.33/1.01  --clausifier_options                    --mode clausify
% 3.33/1.01  --stdin                                 false
% 3.33/1.01  --stats_out                             all
% 3.33/1.01  
% 3.33/1.01  ------ General Options
% 3.33/1.01  
% 3.33/1.01  --fof                                   false
% 3.33/1.01  --time_out_real                         305.
% 3.33/1.01  --time_out_virtual                      -1.
% 3.33/1.01  --symbol_type_check                     false
% 3.33/1.01  --clausify_out                          false
% 3.33/1.01  --sig_cnt_out                           false
% 3.33/1.01  --trig_cnt_out                          false
% 3.33/1.01  --trig_cnt_out_tolerance                1.
% 3.33/1.01  --trig_cnt_out_sk_spl                   false
% 3.33/1.01  --abstr_cl_out                          false
% 3.33/1.01  
% 3.33/1.01  ------ Global Options
% 3.33/1.01  
% 3.33/1.01  --schedule                              default
% 3.33/1.01  --add_important_lit                     false
% 3.33/1.01  --prop_solver_per_cl                    1000
% 3.33/1.01  --min_unsat_core                        false
% 3.33/1.01  --soft_assumptions                      false
% 3.33/1.01  --soft_lemma_size                       3
% 3.33/1.01  --prop_impl_unit_size                   0
% 3.33/1.01  --prop_impl_unit                        []
% 3.33/1.01  --share_sel_clauses                     true
% 3.33/1.01  --reset_solvers                         false
% 3.33/1.01  --bc_imp_inh                            [conj_cone]
% 3.33/1.01  --conj_cone_tolerance                   3.
% 3.33/1.01  --extra_neg_conj                        none
% 3.33/1.01  --large_theory_mode                     true
% 3.33/1.01  --prolific_symb_bound                   200
% 3.33/1.01  --lt_threshold                          2000
% 3.33/1.01  --clause_weak_htbl                      true
% 3.33/1.01  --gc_record_bc_elim                     false
% 3.33/1.01  
% 3.33/1.01  ------ Preprocessing Options
% 3.33/1.01  
% 3.33/1.01  --preprocessing_flag                    true
% 3.33/1.01  --time_out_prep_mult                    0.1
% 3.33/1.01  --splitting_mode                        input
% 3.33/1.01  --splitting_grd                         true
% 3.33/1.01  --splitting_cvd                         false
% 3.33/1.01  --splitting_cvd_svl                     false
% 3.33/1.01  --splitting_nvd                         32
% 3.33/1.01  --sub_typing                            true
% 3.33/1.01  --prep_gs_sim                           true
% 3.33/1.01  --prep_unflatten                        true
% 3.33/1.01  --prep_res_sim                          true
% 3.33/1.01  --prep_upred                            true
% 3.33/1.01  --prep_sem_filter                       exhaustive
% 3.33/1.01  --prep_sem_filter_out                   false
% 3.33/1.01  --pred_elim                             true
% 3.33/1.01  --res_sim_input                         true
% 3.33/1.01  --eq_ax_congr_red                       true
% 3.33/1.01  --pure_diseq_elim                       true
% 3.33/1.01  --brand_transform                       false
% 3.33/1.01  --non_eq_to_eq                          false
% 3.33/1.01  --prep_def_merge                        true
% 3.33/1.01  --prep_def_merge_prop_impl              false
% 3.33/1.01  --prep_def_merge_mbd                    true
% 3.33/1.01  --prep_def_merge_tr_red                 false
% 3.33/1.01  --prep_def_merge_tr_cl                  false
% 3.33/1.01  --smt_preprocessing                     true
% 3.33/1.01  --smt_ac_axioms                         fast
% 3.33/1.01  --preprocessed_out                      false
% 3.33/1.01  --preprocessed_stats                    false
% 3.33/1.01  
% 3.33/1.01  ------ Abstraction refinement Options
% 3.33/1.01  
% 3.33/1.01  --abstr_ref                             []
% 3.33/1.01  --abstr_ref_prep                        false
% 3.33/1.01  --abstr_ref_until_sat                   false
% 3.33/1.01  --abstr_ref_sig_restrict                funpre
% 3.33/1.01  --abstr_ref_af_restrict_to_split_sk     false
% 3.33/1.01  --abstr_ref_under                       []
% 3.33/1.01  
% 3.33/1.01  ------ SAT Options
% 3.33/1.01  
% 3.33/1.01  --sat_mode                              false
% 3.33/1.01  --sat_fm_restart_options                ""
% 3.33/1.01  --sat_gr_def                            false
% 3.33/1.01  --sat_epr_types                         true
% 3.33/1.01  --sat_non_cyclic_types                  false
% 3.33/1.01  --sat_finite_models                     false
% 3.33/1.01  --sat_fm_lemmas                         false
% 3.33/1.01  --sat_fm_prep                           false
% 3.33/1.01  --sat_fm_uc_incr                        true
% 3.33/1.01  --sat_out_model                         small
% 3.33/1.01  --sat_out_clauses                       false
% 3.33/1.01  
% 3.33/1.01  ------ QBF Options
% 3.33/1.01  
% 3.33/1.01  --qbf_mode                              false
% 3.33/1.01  --qbf_elim_univ                         false
% 3.33/1.01  --qbf_dom_inst                          none
% 3.33/1.01  --qbf_dom_pre_inst                      false
% 3.33/1.01  --qbf_sk_in                             false
% 3.33/1.01  --qbf_pred_elim                         true
% 3.33/1.01  --qbf_split                             512
% 3.33/1.01  
% 3.33/1.01  ------ BMC1 Options
% 3.33/1.01  
% 3.33/1.01  --bmc1_incremental                      false
% 3.33/1.01  --bmc1_axioms                           reachable_all
% 3.33/1.01  --bmc1_min_bound                        0
% 3.33/1.01  --bmc1_max_bound                        -1
% 3.33/1.01  --bmc1_max_bound_default                -1
% 3.33/1.01  --bmc1_symbol_reachability              true
% 3.33/1.01  --bmc1_property_lemmas                  false
% 3.33/1.01  --bmc1_k_induction                      false
% 3.33/1.01  --bmc1_non_equiv_states                 false
% 3.33/1.01  --bmc1_deadlock                         false
% 3.33/1.01  --bmc1_ucm                              false
% 3.33/1.01  --bmc1_add_unsat_core                   none
% 3.33/1.01  --bmc1_unsat_core_children              false
% 3.33/1.01  --bmc1_unsat_core_extrapolate_axioms    false
% 3.33/1.01  --bmc1_out_stat                         full
% 3.33/1.01  --bmc1_ground_init                      false
% 3.33/1.01  --bmc1_pre_inst_next_state              false
% 3.33/1.01  --bmc1_pre_inst_state                   false
% 3.33/1.01  --bmc1_pre_inst_reach_state             false
% 3.33/1.01  --bmc1_out_unsat_core                   false
% 3.33/1.01  --bmc1_aig_witness_out                  false
% 3.33/1.01  --bmc1_verbose                          false
% 3.33/1.01  --bmc1_dump_clauses_tptp                false
% 3.33/1.01  --bmc1_dump_unsat_core_tptp             false
% 3.33/1.01  --bmc1_dump_file                        -
% 3.33/1.01  --bmc1_ucm_expand_uc_limit              128
% 3.33/1.01  --bmc1_ucm_n_expand_iterations          6
% 3.33/1.01  --bmc1_ucm_extend_mode                  1
% 3.33/1.01  --bmc1_ucm_init_mode                    2
% 3.33/1.01  --bmc1_ucm_cone_mode                    none
% 3.33/1.01  --bmc1_ucm_reduced_relation_type        0
% 3.33/1.01  --bmc1_ucm_relax_model                  4
% 3.33/1.01  --bmc1_ucm_full_tr_after_sat            true
% 3.33/1.01  --bmc1_ucm_expand_neg_assumptions       false
% 3.33/1.01  --bmc1_ucm_layered_model                none
% 3.33/1.01  --bmc1_ucm_max_lemma_size               10
% 3.33/1.01  
% 3.33/1.01  ------ AIG Options
% 3.33/1.01  
% 3.33/1.01  --aig_mode                              false
% 3.33/1.01  
% 3.33/1.01  ------ Instantiation Options
% 3.33/1.01  
% 3.33/1.01  --instantiation_flag                    true
% 3.33/1.01  --inst_sos_flag                         false
% 3.33/1.01  --inst_sos_phase                        true
% 3.33/1.01  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 3.33/1.01  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 3.33/1.01  --inst_lit_sel_side                     none
% 3.33/1.01  --inst_solver_per_active                1400
% 3.33/1.01  --inst_solver_calls_frac                1.
% 3.33/1.01  --inst_passive_queue_type               priority_queues
% 3.33/1.01  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 3.33/1.01  --inst_passive_queues_freq              [25;2]
% 3.33/1.01  --inst_dismatching                      true
% 3.33/1.01  --inst_eager_unprocessed_to_passive     true
% 3.33/1.01  --inst_prop_sim_given                   true
% 3.33/1.01  --inst_prop_sim_new                     false
% 3.33/1.01  --inst_subs_new                         false
% 3.33/1.01  --inst_eq_res_simp                      false
% 3.33/1.01  --inst_subs_given                       false
% 3.33/1.01  --inst_orphan_elimination               true
% 3.33/1.01  --inst_learning_loop_flag               true
% 3.33/1.01  --inst_learning_start                   3000
% 3.33/1.01  --inst_learning_factor                  2
% 3.33/1.01  --inst_start_prop_sim_after_learn       3
% 3.33/1.01  --inst_sel_renew                        solver
% 3.33/1.01  --inst_lit_activity_flag                true
% 3.33/1.01  --inst_restr_to_given                   false
% 3.33/1.01  --inst_activity_threshold               500
% 3.33/1.01  --inst_out_proof                        true
% 3.33/1.01  
% 3.33/1.01  ------ Resolution Options
% 3.33/1.01  
% 3.33/1.01  --resolution_flag                       false
% 3.33/1.01  --res_lit_sel                           adaptive
% 3.33/1.01  --res_lit_sel_side                      none
% 3.33/1.01  --res_ordering                          kbo
% 3.33/1.01  --res_to_prop_solver                    active
% 3.33/1.01  --res_prop_simpl_new                    false
% 3.33/1.01  --res_prop_simpl_given                  true
% 3.33/1.01  --res_passive_queue_type                priority_queues
% 3.33/1.01  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 3.33/1.01  --res_passive_queues_freq               [15;5]
% 3.33/1.01  --res_forward_subs                      full
% 3.33/1.01  --res_backward_subs                     full
% 3.33/1.01  --res_forward_subs_resolution           true
% 3.33/1.01  --res_backward_subs_resolution          true
% 3.33/1.01  --res_orphan_elimination                true
% 3.33/1.01  --res_time_limit                        2.
% 3.33/1.01  --res_out_proof                         true
% 3.33/1.01  
% 3.33/1.01  ------ Superposition Options
% 3.33/1.01  
% 3.33/1.01  --superposition_flag                    true
% 3.33/1.01  --sup_passive_queue_type                priority_queues
% 3.33/1.01  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 3.33/1.01  --sup_passive_queues_freq               [8;1;4]
% 3.33/1.01  --demod_completeness_check              fast
% 3.33/1.01  --demod_use_ground                      true
% 3.33/1.01  --sup_to_prop_solver                    passive
% 3.33/1.01  --sup_prop_simpl_new                    true
% 3.33/1.01  --sup_prop_simpl_given                  true
% 3.33/1.01  --sup_fun_splitting                     false
% 3.33/1.01  --sup_smt_interval                      50000
% 3.33/1.01  
% 3.33/1.01  ------ Superposition Simplification Setup
% 3.33/1.01  
% 3.33/1.01  --sup_indices_passive                   []
% 3.33/1.01  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.33/1.01  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.33/1.01  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.33/1.01  --sup_full_triv                         [TrivRules;PropSubs]
% 3.33/1.01  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.33/1.01  --sup_full_bw                           [BwDemod]
% 3.33/1.01  --sup_immed_triv                        [TrivRules]
% 3.33/1.01  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 3.33/1.01  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.33/1.01  --sup_immed_bw_main                     []
% 3.33/1.01  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 3.33/1.01  --sup_input_triv                        [Unflattening;TrivRules]
% 3.33/1.01  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.33/1.01  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 3.33/1.01  
% 3.33/1.01  ------ Combination Options
% 3.33/1.01  
% 3.33/1.01  --comb_res_mult                         3
% 3.33/1.01  --comb_sup_mult                         2
% 3.33/1.01  --comb_inst_mult                        10
% 3.33/1.01  
% 3.33/1.01  ------ Debug Options
% 3.33/1.01  
% 3.33/1.01  --dbg_backtrace                         false
% 3.33/1.01  --dbg_dump_prop_clauses                 false
% 3.33/1.01  --dbg_dump_prop_clauses_file            -
% 3.33/1.01  --dbg_out_stat                          false
% 3.33/1.01  
% 3.33/1.01  
% 3.33/1.01  
% 3.33/1.01  
% 3.33/1.01  ------ Proving...
% 3.33/1.01  
% 3.33/1.01  
% 3.33/1.01  % SZS status Theorem for theBenchmark.p
% 3.33/1.01  
% 3.33/1.01  % SZS output start CNFRefutation for theBenchmark.p
% 3.33/1.01  
% 3.33/1.01  fof(f19,conjecture,(
% 3.33/1.01    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v3_funct_2(X2,X0,X0) & v1_funct_2(X2,X0,X0) & v1_funct_1(X2)) => (r1_tarski(X1,X0) => (k8_relset_1(X0,X0,X2,k7_relset_1(X0,X0,X2,X1)) = X1 & k7_relset_1(X0,X0,X2,k8_relset_1(X0,X0,X2,X1)) = X1)))),
% 3.33/1.01    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.33/1.01  
% 3.33/1.01  fof(f20,negated_conjecture,(
% 3.33/1.01    ~! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v3_funct_2(X2,X0,X0) & v1_funct_2(X2,X0,X0) & v1_funct_1(X2)) => (r1_tarski(X1,X0) => (k8_relset_1(X0,X0,X2,k7_relset_1(X0,X0,X2,X1)) = X1 & k7_relset_1(X0,X0,X2,k8_relset_1(X0,X0,X2,X1)) = X1)))),
% 3.33/1.01    inference(negated_conjecture,[],[f19])).
% 3.33/1.01  
% 3.33/1.01  fof(f46,plain,(
% 3.33/1.01    ? [X0,X1,X2] : (((k8_relset_1(X0,X0,X2,k7_relset_1(X0,X0,X2,X1)) != X1 | k7_relset_1(X0,X0,X2,k8_relset_1(X0,X0,X2,X1)) != X1) & r1_tarski(X1,X0)) & (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v3_funct_2(X2,X0,X0) & v1_funct_2(X2,X0,X0) & v1_funct_1(X2)))),
% 3.33/1.01    inference(ennf_transformation,[],[f20])).
% 3.33/1.01  
% 3.33/1.01  fof(f47,plain,(
% 3.33/1.01    ? [X0,X1,X2] : ((k8_relset_1(X0,X0,X2,k7_relset_1(X0,X0,X2,X1)) != X1 | k7_relset_1(X0,X0,X2,k8_relset_1(X0,X0,X2,X1)) != X1) & r1_tarski(X1,X0) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v3_funct_2(X2,X0,X0) & v1_funct_2(X2,X0,X0) & v1_funct_1(X2))),
% 3.33/1.01    inference(flattening,[],[f46])).
% 3.33/1.01  
% 3.33/1.01  fof(f52,plain,(
% 3.33/1.01    ? [X0,X1,X2] : ((k8_relset_1(X0,X0,X2,k7_relset_1(X0,X0,X2,X1)) != X1 | k7_relset_1(X0,X0,X2,k8_relset_1(X0,X0,X2,X1)) != X1) & r1_tarski(X1,X0) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v3_funct_2(X2,X0,X0) & v1_funct_2(X2,X0,X0) & v1_funct_1(X2)) => ((k8_relset_1(sK0,sK0,sK2,k7_relset_1(sK0,sK0,sK2,sK1)) != sK1 | k7_relset_1(sK0,sK0,sK2,k8_relset_1(sK0,sK0,sK2,sK1)) != sK1) & r1_tarski(sK1,sK0) & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) & v3_funct_2(sK2,sK0,sK0) & v1_funct_2(sK2,sK0,sK0) & v1_funct_1(sK2))),
% 3.33/1.01    introduced(choice_axiom,[])).
% 3.33/1.01  
% 3.33/1.01  fof(f53,plain,(
% 3.33/1.01    (k8_relset_1(sK0,sK0,sK2,k7_relset_1(sK0,sK0,sK2,sK1)) != sK1 | k7_relset_1(sK0,sK0,sK2,k8_relset_1(sK0,sK0,sK2,sK1)) != sK1) & r1_tarski(sK1,sK0) & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) & v3_funct_2(sK2,sK0,sK0) & v1_funct_2(sK2,sK0,sK0) & v1_funct_1(sK2)),
% 3.33/1.01    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f47,f52])).
% 3.33/1.01  
% 3.33/1.01  fof(f86,plain,(
% 3.33/1.01    r1_tarski(sK1,sK0)),
% 3.33/1.01    inference(cnf_transformation,[],[f53])).
% 3.33/1.01  
% 3.33/1.01  fof(f85,plain,(
% 3.33/1.01    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))),
% 3.33/1.01    inference(cnf_transformation,[],[f53])).
% 3.33/1.01  
% 3.33/1.01  fof(f12,axiom,(
% 3.33/1.01    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => (v5_relat_1(X2,X1) & v4_relat_1(X2,X0)))),
% 3.33/1.01    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.33/1.01  
% 3.33/1.01  fof(f35,plain,(
% 3.33/1.01    ! [X0,X1,X2] : ((v5_relat_1(X2,X1) & v4_relat_1(X2,X0)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 3.33/1.01    inference(ennf_transformation,[],[f12])).
% 3.33/1.01  
% 3.33/1.01  fof(f68,plain,(
% 3.33/1.01    ( ! [X2,X0,X1] : (v4_relat_1(X2,X0) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 3.33/1.01    inference(cnf_transformation,[],[f35])).
% 3.33/1.01  
% 3.33/1.01  fof(f3,axiom,(
% 3.33/1.01    ! [X0,X1] : (v1_relat_1(X1) => (v4_relat_1(X1,X0) <=> r1_tarski(k1_relat_1(X1),X0)))),
% 3.33/1.01    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.33/1.01  
% 3.33/1.01  fof(f22,plain,(
% 3.33/1.01    ! [X0,X1] : ((v4_relat_1(X1,X0) <=> r1_tarski(k1_relat_1(X1),X0)) | ~v1_relat_1(X1))),
% 3.33/1.01    inference(ennf_transformation,[],[f3])).
% 3.33/1.01  
% 3.33/1.01  fof(f50,plain,(
% 3.33/1.01    ! [X0,X1] : (((v4_relat_1(X1,X0) | ~r1_tarski(k1_relat_1(X1),X0)) & (r1_tarski(k1_relat_1(X1),X0) | ~v4_relat_1(X1,X0))) | ~v1_relat_1(X1))),
% 3.33/1.01    inference(nnf_transformation,[],[f22])).
% 3.33/1.01  
% 3.33/1.01  fof(f58,plain,(
% 3.33/1.01    ( ! [X0,X1] : (r1_tarski(k1_relat_1(X1),X0) | ~v4_relat_1(X1,X0) | ~v1_relat_1(X1)) )),
% 3.33/1.01    inference(cnf_transformation,[],[f50])).
% 3.33/1.01  
% 3.33/1.01  fof(f18,axiom,(
% 3.33/1.01    ! [X0,X1] : ((m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v3_funct_2(X1,X0,X0) & v1_funct_2(X1,X0,X0) & v1_funct_1(X1)) => k2_funct_1(X1) = k2_funct_2(X0,X1))),
% 3.33/1.01    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.33/1.01  
% 3.33/1.01  fof(f44,plain,(
% 3.33/1.01    ! [X0,X1] : (k2_funct_1(X1) = k2_funct_2(X0,X1) | (~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) | ~v3_funct_2(X1,X0,X0) | ~v1_funct_2(X1,X0,X0) | ~v1_funct_1(X1)))),
% 3.33/1.01    inference(ennf_transformation,[],[f18])).
% 3.33/1.01  
% 3.33/1.01  fof(f45,plain,(
% 3.33/1.01    ! [X0,X1] : (k2_funct_1(X1) = k2_funct_2(X0,X1) | ~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) | ~v3_funct_2(X1,X0,X0) | ~v1_funct_2(X1,X0,X0) | ~v1_funct_1(X1))),
% 3.33/1.01    inference(flattening,[],[f44])).
% 3.33/1.01  
% 3.33/1.01  fof(f81,plain,(
% 3.33/1.01    ( ! [X0,X1] : (k2_funct_1(X1) = k2_funct_2(X0,X1) | ~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) | ~v3_funct_2(X1,X0,X0) | ~v1_funct_2(X1,X0,X0) | ~v1_funct_1(X1)) )),
% 3.33/1.01    inference(cnf_transformation,[],[f45])).
% 3.33/1.01  
% 3.33/1.01  fof(f82,plain,(
% 3.33/1.01    v1_funct_1(sK2)),
% 3.33/1.01    inference(cnf_transformation,[],[f53])).
% 3.33/1.01  
% 3.33/1.01  fof(f83,plain,(
% 3.33/1.01    v1_funct_2(sK2,sK0,sK0)),
% 3.33/1.01    inference(cnf_transformation,[],[f53])).
% 3.33/1.01  
% 3.33/1.01  fof(f84,plain,(
% 3.33/1.01    v3_funct_2(sK2,sK0,sK0)),
% 3.33/1.01    inference(cnf_transformation,[],[f53])).
% 3.33/1.01  
% 3.33/1.01  fof(f17,axiom,(
% 3.33/1.01    ! [X0,X1] : ((m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v3_funct_2(X1,X0,X0) & v1_funct_2(X1,X0,X0) & v1_funct_1(X1)) => (m1_subset_1(k2_funct_2(X0,X1),k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v3_funct_2(k2_funct_2(X0,X1),X0,X0) & v1_funct_2(k2_funct_2(X0,X1),X0,X0) & v1_funct_1(k2_funct_2(X0,X1))))),
% 3.33/1.01    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.33/1.01  
% 3.33/1.01  fof(f42,plain,(
% 3.33/1.01    ! [X0,X1] : ((m1_subset_1(k2_funct_2(X0,X1),k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v3_funct_2(k2_funct_2(X0,X1),X0,X0) & v1_funct_2(k2_funct_2(X0,X1),X0,X0) & v1_funct_1(k2_funct_2(X0,X1))) | (~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) | ~v3_funct_2(X1,X0,X0) | ~v1_funct_2(X1,X0,X0) | ~v1_funct_1(X1)))),
% 3.33/1.01    inference(ennf_transformation,[],[f17])).
% 3.33/1.01  
% 3.33/1.01  fof(f43,plain,(
% 3.33/1.01    ! [X0,X1] : ((m1_subset_1(k2_funct_2(X0,X1),k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v3_funct_2(k2_funct_2(X0,X1),X0,X0) & v1_funct_2(k2_funct_2(X0,X1),X0,X0) & v1_funct_1(k2_funct_2(X0,X1))) | ~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) | ~v3_funct_2(X1,X0,X0) | ~v1_funct_2(X1,X0,X0) | ~v1_funct_1(X1))),
% 3.33/1.01    inference(flattening,[],[f42])).
% 3.33/1.01  
% 3.33/1.01  fof(f80,plain,(
% 3.33/1.01    ( ! [X0,X1] : (m1_subset_1(k2_funct_2(X0,X1),k1_zfmisc_1(k2_zfmisc_1(X0,X0))) | ~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) | ~v3_funct_2(X1,X0,X0) | ~v1_funct_2(X1,X0,X0) | ~v1_funct_1(X1)) )),
% 3.33/1.01    inference(cnf_transformation,[],[f43])).
% 3.33/1.01  
% 3.33/1.01  fof(f15,axiom,(
% 3.33/1.01    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => ((v3_funct_2(X2,X0,X1) & v1_funct_1(X2)) => (v2_funct_2(X2,X1) & v2_funct_1(X2) & v1_funct_1(X2))))),
% 3.33/1.01    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.33/1.01  
% 3.33/1.01  fof(f38,plain,(
% 3.33/1.01    ! [X0,X1,X2] : (((v2_funct_2(X2,X1) & v2_funct_1(X2) & v1_funct_1(X2)) | (~v3_funct_2(X2,X0,X1) | ~v1_funct_1(X2))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 3.33/1.01    inference(ennf_transformation,[],[f15])).
% 3.33/1.01  
% 3.33/1.01  fof(f39,plain,(
% 3.33/1.01    ! [X0,X1,X2] : ((v2_funct_2(X2,X1) & v2_funct_1(X2) & v1_funct_1(X2)) | ~v3_funct_2(X2,X0,X1) | ~v1_funct_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 3.33/1.01    inference(flattening,[],[f38])).
% 3.33/1.01  
% 3.33/1.01  fof(f74,plain,(
% 3.33/1.01    ( ! [X2,X0,X1] : (v2_funct_2(X2,X1) | ~v3_funct_2(X2,X0,X1) | ~v1_funct_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 3.33/1.01    inference(cnf_transformation,[],[f39])).
% 3.33/1.01  
% 3.33/1.01  fof(f16,axiom,(
% 3.33/1.01    ! [X0,X1] : ((v5_relat_1(X1,X0) & v1_relat_1(X1)) => (v2_funct_2(X1,X0) <=> k2_relat_1(X1) = X0))),
% 3.33/1.01    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.33/1.01  
% 3.33/1.01  fof(f40,plain,(
% 3.33/1.01    ! [X0,X1] : ((v2_funct_2(X1,X0) <=> k2_relat_1(X1) = X0) | (~v5_relat_1(X1,X0) | ~v1_relat_1(X1)))),
% 3.33/1.01    inference(ennf_transformation,[],[f16])).
% 3.33/1.01  
% 3.33/1.01  fof(f41,plain,(
% 3.33/1.01    ! [X0,X1] : ((v2_funct_2(X1,X0) <=> k2_relat_1(X1) = X0) | ~v5_relat_1(X1,X0) | ~v1_relat_1(X1))),
% 3.33/1.01    inference(flattening,[],[f40])).
% 3.33/1.01  
% 3.33/1.01  fof(f51,plain,(
% 3.33/1.01    ! [X0,X1] : (((v2_funct_2(X1,X0) | k2_relat_1(X1) != X0) & (k2_relat_1(X1) = X0 | ~v2_funct_2(X1,X0))) | ~v5_relat_1(X1,X0) | ~v1_relat_1(X1))),
% 3.33/1.01    inference(nnf_transformation,[],[f41])).
% 3.33/1.01  
% 3.33/1.01  fof(f75,plain,(
% 3.33/1.01    ( ! [X0,X1] : (k2_relat_1(X1) = X0 | ~v2_funct_2(X1,X0) | ~v5_relat_1(X1,X0) | ~v1_relat_1(X1)) )),
% 3.33/1.01    inference(cnf_transformation,[],[f51])).
% 3.33/1.01  
% 3.33/1.01  fof(f69,plain,(
% 3.33/1.01    ( ! [X2,X0,X1] : (v5_relat_1(X2,X1) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 3.33/1.01    inference(cnf_transformation,[],[f35])).
% 3.33/1.01  
% 3.33/1.01  fof(f4,axiom,(
% 3.33/1.01    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1))),
% 3.33/1.01    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.33/1.01  
% 3.33/1.01  fof(f60,plain,(
% 3.33/1.01    ( ! [X0,X1] : (v1_relat_1(k2_zfmisc_1(X0,X1))) )),
% 3.33/1.01    inference(cnf_transformation,[],[f4])).
% 3.33/1.01  
% 3.33/1.01  fof(f77,plain,(
% 3.33/1.01    ( ! [X0,X1] : (v1_funct_1(k2_funct_2(X0,X1)) | ~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) | ~v3_funct_2(X1,X0,X0) | ~v1_funct_2(X1,X0,X0) | ~v1_funct_1(X1)) )),
% 3.33/1.01    inference(cnf_transformation,[],[f43])).
% 3.33/1.01  
% 3.33/1.01  fof(f79,plain,(
% 3.33/1.01    ( ! [X0,X1] : (v3_funct_2(k2_funct_2(X0,X1),X0,X0) | ~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) | ~v3_funct_2(X1,X0,X0) | ~v1_funct_2(X1,X0,X0) | ~v1_funct_1(X1)) )),
% 3.33/1.01    inference(cnf_transformation,[],[f43])).
% 3.33/1.01  
% 3.33/1.01  fof(f2,axiom,(
% 3.33/1.01    ! [X0] : (v1_relat_1(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => v1_relat_1(X1)))),
% 3.33/1.01    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.33/1.01  
% 3.33/1.01  fof(f21,plain,(
% 3.33/1.01    ! [X0] : (! [X1] : (v1_relat_1(X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) | ~v1_relat_1(X0))),
% 3.33/1.01    inference(ennf_transformation,[],[f2])).
% 3.33/1.01  
% 3.33/1.01  fof(f57,plain,(
% 3.33/1.01    ( ! [X0,X1] : (v1_relat_1(X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0)) | ~v1_relat_1(X0)) )),
% 3.33/1.01    inference(cnf_transformation,[],[f21])).
% 3.33/1.01  
% 3.33/1.01  fof(f9,axiom,(
% 3.33/1.01    ! [X0,X1] : ((v1_funct_1(X1) & v1_relat_1(X1)) => (r1_tarski(X0,k2_relat_1(X1)) => k9_relat_1(X1,k10_relat_1(X1,X0)) = X0))),
% 3.33/1.01    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.33/1.01  
% 3.33/1.01  fof(f29,plain,(
% 3.33/1.01    ! [X0,X1] : ((k9_relat_1(X1,k10_relat_1(X1,X0)) = X0 | ~r1_tarski(X0,k2_relat_1(X1))) | (~v1_funct_1(X1) | ~v1_relat_1(X1)))),
% 3.33/1.01    inference(ennf_transformation,[],[f9])).
% 3.33/1.01  
% 3.33/1.01  fof(f30,plain,(
% 3.33/1.01    ! [X0,X1] : (k9_relat_1(X1,k10_relat_1(X1,X0)) = X0 | ~r1_tarski(X0,k2_relat_1(X1)) | ~v1_funct_1(X1) | ~v1_relat_1(X1))),
% 3.33/1.01    inference(flattening,[],[f29])).
% 3.33/1.01  
% 3.33/1.01  fof(f65,plain,(
% 3.33/1.01    ( ! [X0,X1] : (k9_relat_1(X1,k10_relat_1(X1,X0)) = X0 | ~r1_tarski(X0,k2_relat_1(X1)) | ~v1_funct_1(X1) | ~v1_relat_1(X1)) )),
% 3.33/1.01    inference(cnf_transformation,[],[f30])).
% 3.33/1.01  
% 3.33/1.01  fof(f73,plain,(
% 3.33/1.01    ( ! [X2,X0,X1] : (v2_funct_1(X2) | ~v3_funct_2(X2,X0,X1) | ~v1_funct_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 3.33/1.01    inference(cnf_transformation,[],[f39])).
% 3.33/1.01  
% 3.33/1.01  fof(f10,axiom,(
% 3.33/1.01    ! [X0,X1] : ((v1_funct_1(X1) & v1_relat_1(X1)) => (v2_funct_1(X1) => k9_relat_1(X1,X0) = k10_relat_1(k2_funct_1(X1),X0)))),
% 3.33/1.01    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.33/1.01  
% 3.33/1.01  fof(f31,plain,(
% 3.33/1.01    ! [X0,X1] : ((k9_relat_1(X1,X0) = k10_relat_1(k2_funct_1(X1),X0) | ~v2_funct_1(X1)) | (~v1_funct_1(X1) | ~v1_relat_1(X1)))),
% 3.33/1.01    inference(ennf_transformation,[],[f10])).
% 3.33/1.01  
% 3.33/1.01  fof(f32,plain,(
% 3.33/1.01    ! [X0,X1] : (k9_relat_1(X1,X0) = k10_relat_1(k2_funct_1(X1),X0) | ~v2_funct_1(X1) | ~v1_funct_1(X1) | ~v1_relat_1(X1))),
% 3.33/1.01    inference(flattening,[],[f31])).
% 3.33/1.01  
% 3.33/1.01  fof(f66,plain,(
% 3.33/1.01    ( ! [X0,X1] : (k9_relat_1(X1,X0) = k10_relat_1(k2_funct_1(X1),X0) | ~v2_funct_1(X1) | ~v1_funct_1(X1) | ~v1_relat_1(X1)) )),
% 3.33/1.01    inference(cnf_transformation,[],[f32])).
% 3.33/1.01  
% 3.33/1.01  fof(f1,axiom,(
% 3.33/1.01    ! [X0,X1] : (X0 = X1 <=> (r1_tarski(X1,X0) & r1_tarski(X0,X1)))),
% 3.33/1.01    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.33/1.01  
% 3.33/1.01  fof(f48,plain,(
% 3.33/1.01    ! [X0,X1] : ((X0 = X1 | (~r1_tarski(X1,X0) | ~r1_tarski(X0,X1))) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 3.33/1.01    inference(nnf_transformation,[],[f1])).
% 3.33/1.01  
% 3.33/1.01  fof(f49,plain,(
% 3.33/1.01    ! [X0,X1] : ((X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 3.33/1.01    inference(flattening,[],[f48])).
% 3.33/1.01  
% 3.33/1.01  fof(f55,plain,(
% 3.33/1.01    ( ! [X0,X1] : (r1_tarski(X1,X0) | X0 != X1) )),
% 3.33/1.01    inference(cnf_transformation,[],[f49])).
% 3.33/1.01  
% 3.33/1.01  fof(f88,plain,(
% 3.33/1.01    ( ! [X1] : (r1_tarski(X1,X1)) )),
% 3.33/1.01    inference(equality_resolution,[],[f55])).
% 3.33/1.01  
% 3.33/1.01  fof(f6,axiom,(
% 3.33/1.01    ! [X0] : (v1_relat_1(X0) => k1_relat_1(X0) = k10_relat_1(X0,k2_relat_1(X0)))),
% 3.33/1.01    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.33/1.01  
% 3.33/1.01  fof(f24,plain,(
% 3.33/1.01    ! [X0] : (k1_relat_1(X0) = k10_relat_1(X0,k2_relat_1(X0)) | ~v1_relat_1(X0))),
% 3.33/1.01    inference(ennf_transformation,[],[f6])).
% 3.33/1.01  
% 3.33/1.01  fof(f62,plain,(
% 3.33/1.01    ( ! [X0] : (k1_relat_1(X0) = k10_relat_1(X0,k2_relat_1(X0)) | ~v1_relat_1(X0)) )),
% 3.33/1.01    inference(cnf_transformation,[],[f24])).
% 3.33/1.01  
% 3.33/1.01  fof(f7,axiom,(
% 3.33/1.01    ! [X0,X1] : ((v4_relat_1(X1,X0) & v1_relat_1(X1)) => k7_relat_1(X1,X0) = X1)),
% 3.33/1.01    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.33/1.01  
% 3.33/1.01  fof(f25,plain,(
% 3.33/1.01    ! [X0,X1] : (k7_relat_1(X1,X0) = X1 | (~v4_relat_1(X1,X0) | ~v1_relat_1(X1)))),
% 3.33/1.01    inference(ennf_transformation,[],[f7])).
% 3.33/1.01  
% 3.33/1.01  fof(f26,plain,(
% 3.33/1.01    ! [X0,X1] : (k7_relat_1(X1,X0) = X1 | ~v4_relat_1(X1,X0) | ~v1_relat_1(X1))),
% 3.33/1.01    inference(flattening,[],[f25])).
% 3.33/1.01  
% 3.33/1.01  fof(f63,plain,(
% 3.33/1.01    ( ! [X0,X1] : (k7_relat_1(X1,X0) = X1 | ~v4_relat_1(X1,X0) | ~v1_relat_1(X1)) )),
% 3.33/1.01    inference(cnf_transformation,[],[f26])).
% 3.33/1.01  
% 3.33/1.01  fof(f5,axiom,(
% 3.33/1.01    ! [X0,X1] : (v1_relat_1(X1) => k2_relat_1(k7_relat_1(X1,X0)) = k9_relat_1(X1,X0))),
% 3.33/1.01    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.33/1.01  
% 3.33/1.01  fof(f23,plain,(
% 3.33/1.01    ! [X0,X1] : (k2_relat_1(k7_relat_1(X1,X0)) = k9_relat_1(X1,X0) | ~v1_relat_1(X1))),
% 3.33/1.01    inference(ennf_transformation,[],[f5])).
% 3.33/1.01  
% 3.33/1.01  fof(f61,plain,(
% 3.33/1.01    ( ! [X0,X1] : (k2_relat_1(k7_relat_1(X1,X0)) = k9_relat_1(X1,X0) | ~v1_relat_1(X1)) )),
% 3.33/1.01    inference(cnf_transformation,[],[f23])).
% 3.33/1.01  
% 3.33/1.01  fof(f11,axiom,(
% 3.33/1.01    ! [X0,X1] : ((v1_funct_1(X1) & v1_relat_1(X1)) => ((v2_funct_1(X1) & r1_tarski(X0,k1_relat_1(X1))) => k10_relat_1(X1,k9_relat_1(X1,X0)) = X0))),
% 3.33/1.01    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.33/1.01  
% 3.33/1.01  fof(f33,plain,(
% 3.33/1.01    ! [X0,X1] : ((k10_relat_1(X1,k9_relat_1(X1,X0)) = X0 | (~v2_funct_1(X1) | ~r1_tarski(X0,k1_relat_1(X1)))) | (~v1_funct_1(X1) | ~v1_relat_1(X1)))),
% 3.33/1.01    inference(ennf_transformation,[],[f11])).
% 3.33/1.01  
% 3.33/1.01  fof(f34,plain,(
% 3.33/1.01    ! [X0,X1] : (k10_relat_1(X1,k9_relat_1(X1,X0)) = X0 | ~v2_funct_1(X1) | ~r1_tarski(X0,k1_relat_1(X1)) | ~v1_funct_1(X1) | ~v1_relat_1(X1))),
% 3.33/1.01    inference(flattening,[],[f33])).
% 3.33/1.01  
% 3.33/1.01  fof(f67,plain,(
% 3.33/1.01    ( ! [X0,X1] : (k10_relat_1(X1,k9_relat_1(X1,X0)) = X0 | ~v2_funct_1(X1) | ~r1_tarski(X0,k1_relat_1(X1)) | ~v1_funct_1(X1) | ~v1_relat_1(X1)) )),
% 3.33/1.01    inference(cnf_transformation,[],[f34])).
% 3.33/1.01  
% 3.33/1.01  fof(f14,axiom,(
% 3.33/1.01    ! [X0,X1,X2,X3] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k10_relat_1(X2,X3) = k8_relset_1(X0,X1,X2,X3))),
% 3.33/1.01    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.33/1.01  
% 3.33/1.01  fof(f37,plain,(
% 3.33/1.01    ! [X0,X1,X2,X3] : (k10_relat_1(X2,X3) = k8_relset_1(X0,X1,X2,X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 3.33/1.01    inference(ennf_transformation,[],[f14])).
% 3.33/1.01  
% 3.33/1.01  fof(f71,plain,(
% 3.33/1.01    ( ! [X2,X0,X3,X1] : (k10_relat_1(X2,X3) = k8_relset_1(X0,X1,X2,X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 3.33/1.01    inference(cnf_transformation,[],[f37])).
% 3.33/1.01  
% 3.33/1.01  fof(f87,plain,(
% 3.33/1.01    k8_relset_1(sK0,sK0,sK2,k7_relset_1(sK0,sK0,sK2,sK1)) != sK1 | k7_relset_1(sK0,sK0,sK2,k8_relset_1(sK0,sK0,sK2,sK1)) != sK1),
% 3.33/1.01    inference(cnf_transformation,[],[f53])).
% 3.33/1.01  
% 3.33/1.01  fof(f13,axiom,(
% 3.33/1.01    ! [X0,X1,X2,X3] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k9_relat_1(X2,X3) = k7_relset_1(X0,X1,X2,X3))),
% 3.33/1.01    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.33/1.01  
% 3.33/1.01  fof(f36,plain,(
% 3.33/1.01    ! [X0,X1,X2,X3] : (k9_relat_1(X2,X3) = k7_relset_1(X0,X1,X2,X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 3.33/1.01    inference(ennf_transformation,[],[f13])).
% 3.33/1.01  
% 3.33/1.01  fof(f70,plain,(
% 3.33/1.01    ( ! [X2,X0,X3,X1] : (k9_relat_1(X2,X3) = k7_relset_1(X0,X1,X2,X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 3.33/1.01    inference(cnf_transformation,[],[f36])).
% 3.33/1.01  
% 3.33/1.01  cnf(c_29,negated_conjecture,
% 3.33/1.01      ( r1_tarski(sK1,sK0) ),
% 3.33/1.01      inference(cnf_transformation,[],[f86]) ).
% 3.33/1.01  
% 3.33/1.01  cnf(c_1345,plain,
% 3.33/1.01      ( r1_tarski(sK1,sK0) = iProver_top ),
% 3.33/1.01      inference(predicate_to_equality,[status(thm)],[c_29]) ).
% 3.33/1.01  
% 3.33/1.01  cnf(c_30,negated_conjecture,
% 3.33/1.01      ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) ),
% 3.33/1.01      inference(cnf_transformation,[],[f85]) ).
% 3.33/1.01  
% 3.33/1.01  cnf(c_1344,plain,
% 3.33/1.01      ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) = iProver_top ),
% 3.33/1.01      inference(predicate_to_equality,[status(thm)],[c_30]) ).
% 3.33/1.01  
% 3.33/1.01  cnf(c_15,plain,
% 3.33/1.01      ( v4_relat_1(X0,X1)
% 3.33/1.01      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) ),
% 3.33/1.01      inference(cnf_transformation,[],[f68]) ).
% 3.33/1.01  
% 3.33/1.01  cnf(c_1354,plain,
% 3.33/1.01      ( v4_relat_1(X0,X1) = iProver_top
% 3.33/1.01      | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) != iProver_top ),
% 3.33/1.01      inference(predicate_to_equality,[status(thm)],[c_15]) ).
% 3.33/1.01  
% 3.33/1.01  cnf(c_1813,plain,
% 3.33/1.01      ( v4_relat_1(sK2,sK0) = iProver_top ),
% 3.33/1.01      inference(superposition,[status(thm)],[c_1344,c_1354]) ).
% 3.33/1.01  
% 3.33/1.01  cnf(c_5,plain,
% 3.33/1.01      ( ~ v4_relat_1(X0,X1)
% 3.33/1.01      | r1_tarski(k1_relat_1(X0),X1)
% 3.33/1.01      | ~ v1_relat_1(X0) ),
% 3.33/1.01      inference(cnf_transformation,[],[f58]) ).
% 3.33/1.01  
% 3.33/1.01  cnf(c_1363,plain,
% 3.33/1.01      ( v4_relat_1(X0,X1) != iProver_top
% 3.33/1.01      | r1_tarski(k1_relat_1(X0),X1) = iProver_top
% 3.33/1.01      | v1_relat_1(X0) != iProver_top ),
% 3.33/1.01      inference(predicate_to_equality,[status(thm)],[c_5]) ).
% 3.33/1.01  
% 3.33/1.01  cnf(c_27,plain,
% 3.33/1.01      ( ~ v1_funct_2(X0,X1,X1)
% 3.33/1.01      | ~ v3_funct_2(X0,X1,X1)
% 3.33/1.01      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X1)))
% 3.33/1.01      | ~ v1_funct_1(X0)
% 3.33/1.01      | k2_funct_2(X1,X0) = k2_funct_1(X0) ),
% 3.33/1.01      inference(cnf_transformation,[],[f81]) ).
% 3.33/1.01  
% 3.33/1.01  cnf(c_1346,plain,
% 3.33/1.01      ( k2_funct_2(X0,X1) = k2_funct_1(X1)
% 3.33/1.01      | v1_funct_2(X1,X0,X0) != iProver_top
% 3.33/1.01      | v3_funct_2(X1,X0,X0) != iProver_top
% 3.33/1.01      | m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) != iProver_top
% 3.33/1.01      | v1_funct_1(X1) != iProver_top ),
% 3.33/1.01      inference(predicate_to_equality,[status(thm)],[c_27]) ).
% 3.33/1.01  
% 3.33/1.01  cnf(c_2387,plain,
% 3.33/1.01      ( k2_funct_2(sK0,sK2) = k2_funct_1(sK2)
% 3.33/1.01      | v1_funct_2(sK2,sK0,sK0) != iProver_top
% 3.33/1.01      | v3_funct_2(sK2,sK0,sK0) != iProver_top
% 3.33/1.01      | v1_funct_1(sK2) != iProver_top ),
% 3.33/1.01      inference(superposition,[status(thm)],[c_1344,c_1346]) ).
% 3.33/1.01  
% 3.33/1.01  cnf(c_33,negated_conjecture,
% 3.33/1.01      ( v1_funct_1(sK2) ),
% 3.33/1.01      inference(cnf_transformation,[],[f82]) ).
% 3.33/1.01  
% 3.33/1.01  cnf(c_32,negated_conjecture,
% 3.33/1.01      ( v1_funct_2(sK2,sK0,sK0) ),
% 3.33/1.01      inference(cnf_transformation,[],[f83]) ).
% 3.33/1.01  
% 3.33/1.01  cnf(c_31,negated_conjecture,
% 3.33/1.01      ( v3_funct_2(sK2,sK0,sK0) ),
% 3.33/1.01      inference(cnf_transformation,[],[f84]) ).
% 3.33/1.01  
% 3.33/1.01  cnf(c_1708,plain,
% 3.33/1.01      ( ~ v1_funct_2(sK2,X0,X0)
% 3.33/1.01      | ~ v3_funct_2(sK2,X0,X0)
% 3.33/1.01      | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
% 3.33/1.01      | ~ v1_funct_1(sK2)
% 3.33/1.01      | k2_funct_2(X0,sK2) = k2_funct_1(sK2) ),
% 3.33/1.01      inference(instantiation,[status(thm)],[c_27]) ).
% 3.33/1.01  
% 3.33/1.01  cnf(c_1710,plain,
% 3.33/1.01      ( ~ v1_funct_2(sK2,sK0,sK0)
% 3.33/1.01      | ~ v3_funct_2(sK2,sK0,sK0)
% 3.33/1.01      | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
% 3.33/1.01      | ~ v1_funct_1(sK2)
% 3.33/1.01      | k2_funct_2(sK0,sK2) = k2_funct_1(sK2) ),
% 3.33/1.01      inference(instantiation,[status(thm)],[c_1708]) ).
% 3.33/1.01  
% 3.33/1.01  cnf(c_2923,plain,
% 3.33/1.01      ( k2_funct_2(sK0,sK2) = k2_funct_1(sK2) ),
% 3.33/1.01      inference(global_propositional_subsumption,
% 3.33/1.01                [status(thm)],
% 3.33/1.01                [c_2387,c_33,c_32,c_31,c_30,c_1710]) ).
% 3.33/1.01  
% 3.33/1.01  cnf(c_23,plain,
% 3.33/1.01      ( ~ v1_funct_2(X0,X1,X1)
% 3.33/1.01      | ~ v3_funct_2(X0,X1,X1)
% 3.33/1.01      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X1)))
% 3.33/1.01      | m1_subset_1(k2_funct_2(X1,X0),k1_zfmisc_1(k2_zfmisc_1(X1,X1)))
% 3.33/1.01      | ~ v1_funct_1(X0) ),
% 3.33/1.01      inference(cnf_transformation,[],[f80]) ).
% 3.33/1.01  
% 3.33/1.01  cnf(c_1350,plain,
% 3.33/1.01      ( v1_funct_2(X0,X1,X1) != iProver_top
% 3.33/1.01      | v3_funct_2(X0,X1,X1) != iProver_top
% 3.33/1.01      | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X1))) != iProver_top
% 3.33/1.01      | m1_subset_1(k2_funct_2(X1,X0),k1_zfmisc_1(k2_zfmisc_1(X1,X1))) = iProver_top
% 3.33/1.01      | v1_funct_1(X0) != iProver_top ),
% 3.33/1.01      inference(predicate_to_equality,[status(thm)],[c_23]) ).
% 3.33/1.01  
% 3.33/1.01  cnf(c_4389,plain,
% 3.33/1.01      ( v1_funct_2(sK2,sK0,sK0) != iProver_top
% 3.33/1.01      | v3_funct_2(sK2,sK0,sK0) != iProver_top
% 3.33/1.01      | m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) = iProver_top
% 3.33/1.01      | m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) != iProver_top
% 3.33/1.01      | v1_funct_1(sK2) != iProver_top ),
% 3.33/1.01      inference(superposition,[status(thm)],[c_2923,c_1350]) ).
% 3.33/1.01  
% 3.33/1.01  cnf(c_34,plain,
% 3.33/1.01      ( v1_funct_1(sK2) = iProver_top ),
% 3.33/1.01      inference(predicate_to_equality,[status(thm)],[c_33]) ).
% 3.33/1.01  
% 3.33/1.01  cnf(c_35,plain,
% 3.33/1.01      ( v1_funct_2(sK2,sK0,sK0) = iProver_top ),
% 3.33/1.01      inference(predicate_to_equality,[status(thm)],[c_32]) ).
% 3.33/1.01  
% 3.33/1.01  cnf(c_36,plain,
% 3.33/1.01      ( v3_funct_2(sK2,sK0,sK0) = iProver_top ),
% 3.33/1.01      inference(predicate_to_equality,[status(thm)],[c_31]) ).
% 3.33/1.01  
% 3.33/1.01  cnf(c_37,plain,
% 3.33/1.01      ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) = iProver_top ),
% 3.33/1.01      inference(predicate_to_equality,[status(thm)],[c_30]) ).
% 3.33/1.01  
% 3.33/1.01  cnf(c_4718,plain,
% 3.33/1.01      ( m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) = iProver_top ),
% 3.33/1.01      inference(global_propositional_subsumption,
% 3.33/1.01                [status(thm)],
% 3.33/1.01                [c_4389,c_34,c_35,c_36,c_37]) ).
% 3.33/1.01  
% 3.33/1.01  cnf(c_18,plain,
% 3.33/1.01      ( ~ v3_funct_2(X0,X1,X2)
% 3.33/1.01      | v2_funct_2(X0,X2)
% 3.33/1.01      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.33/1.01      | ~ v1_funct_1(X0) ),
% 3.33/1.01      inference(cnf_transformation,[],[f74]) ).
% 3.33/1.01  
% 3.33/1.01  cnf(c_22,plain,
% 3.33/1.01      ( ~ v2_funct_2(X0,X1)
% 3.33/1.01      | ~ v5_relat_1(X0,X1)
% 3.33/1.01      | ~ v1_relat_1(X0)
% 3.33/1.01      | k2_relat_1(X0) = X1 ),
% 3.33/1.01      inference(cnf_transformation,[],[f75]) ).
% 3.33/1.01  
% 3.33/1.01  cnf(c_402,plain,
% 3.33/1.01      ( ~ v3_funct_2(X0,X1,X2)
% 3.33/1.01      | ~ v5_relat_1(X3,X4)
% 3.33/1.01      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.33/1.01      | ~ v1_funct_1(X0)
% 3.33/1.01      | ~ v1_relat_1(X3)
% 3.33/1.01      | X3 != X0
% 3.33/1.01      | X4 != X2
% 3.33/1.01      | k2_relat_1(X3) = X4 ),
% 3.33/1.01      inference(resolution_lifted,[status(thm)],[c_18,c_22]) ).
% 3.33/1.01  
% 3.33/1.01  cnf(c_403,plain,
% 3.33/1.01      ( ~ v3_funct_2(X0,X1,X2)
% 3.33/1.01      | ~ v5_relat_1(X0,X2)
% 3.33/1.01      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.33/1.01      | ~ v1_funct_1(X0)
% 3.33/1.01      | ~ v1_relat_1(X0)
% 3.33/1.01      | k2_relat_1(X0) = X2 ),
% 3.33/1.01      inference(unflattening,[status(thm)],[c_402]) ).
% 3.33/1.01  
% 3.33/1.01  cnf(c_14,plain,
% 3.33/1.01      ( v5_relat_1(X0,X1)
% 3.33/1.01      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) ),
% 3.33/1.01      inference(cnf_transformation,[],[f69]) ).
% 3.33/1.01  
% 3.33/1.01  cnf(c_419,plain,
% 3.33/1.01      ( ~ v3_funct_2(X0,X1,X2)
% 3.33/1.01      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.33/1.01      | ~ v1_funct_1(X0)
% 3.33/1.01      | ~ v1_relat_1(X0)
% 3.33/1.01      | k2_relat_1(X0) = X2 ),
% 3.33/1.01      inference(forward_subsumption_resolution,
% 3.33/1.01                [status(thm)],
% 3.33/1.01                [c_403,c_14]) ).
% 3.33/1.01  
% 3.33/1.01  cnf(c_1340,plain,
% 3.33/1.01      ( k2_relat_1(X0) = X1
% 3.33/1.01      | v3_funct_2(X0,X2,X1) != iProver_top
% 3.33/1.01      | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) != iProver_top
% 3.33/1.01      | v1_funct_1(X0) != iProver_top
% 3.33/1.01      | v1_relat_1(X0) != iProver_top ),
% 3.33/1.01      inference(predicate_to_equality,[status(thm)],[c_419]) ).
% 3.33/1.01  
% 3.33/1.01  cnf(c_4726,plain,
% 3.33/1.01      ( k2_relat_1(k2_funct_1(sK2)) = sK0
% 3.33/1.01      | v3_funct_2(k2_funct_1(sK2),sK0,sK0) != iProver_top
% 3.33/1.01      | v1_funct_1(k2_funct_1(sK2)) != iProver_top
% 3.33/1.01      | v1_relat_1(k2_funct_1(sK2)) != iProver_top ),
% 3.33/1.01      inference(superposition,[status(thm)],[c_4718,c_1340]) ).
% 3.33/1.01  
% 3.33/1.01  cnf(c_6,plain,
% 3.33/1.01      ( v1_relat_1(k2_zfmisc_1(X0,X1)) ),
% 3.33/1.01      inference(cnf_transformation,[],[f60]) ).
% 3.33/1.01  
% 3.33/1.01  cnf(c_100,plain,
% 3.33/1.01      ( v1_relat_1(k2_zfmisc_1(X0,X1)) = iProver_top ),
% 3.33/1.01      inference(predicate_to_equality,[status(thm)],[c_6]) ).
% 3.33/1.01  
% 3.33/1.01  cnf(c_102,plain,
% 3.33/1.01      ( v1_relat_1(k2_zfmisc_1(sK0,sK0)) = iProver_top ),
% 3.33/1.01      inference(instantiation,[status(thm)],[c_100]) ).
% 3.33/1.01  
% 3.33/1.01  cnf(c_26,plain,
% 3.33/1.01      ( ~ v1_funct_2(X0,X1,X1)
% 3.33/1.01      | ~ v3_funct_2(X0,X1,X1)
% 3.33/1.01      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X1)))
% 3.33/1.01      | ~ v1_funct_1(X0)
% 3.33/1.01      | v1_funct_1(k2_funct_2(X1,X0)) ),
% 3.33/1.01      inference(cnf_transformation,[],[f77]) ).
% 3.33/1.01  
% 3.33/1.01  cnf(c_1347,plain,
% 3.33/1.01      ( v1_funct_2(X0,X1,X1) != iProver_top
% 3.33/1.01      | v3_funct_2(X0,X1,X1) != iProver_top
% 3.33/1.01      | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X1))) != iProver_top
% 3.33/1.01      | v1_funct_1(X0) != iProver_top
% 3.33/1.01      | v1_funct_1(k2_funct_2(X1,X0)) = iProver_top ),
% 3.33/1.01      inference(predicate_to_equality,[status(thm)],[c_26]) ).
% 3.33/1.01  
% 3.33/1.01  cnf(c_3241,plain,
% 3.33/1.01      ( v1_funct_2(sK2,sK0,sK0) != iProver_top
% 3.33/1.01      | v3_funct_2(sK2,sK0,sK0) != iProver_top
% 3.33/1.01      | v1_funct_1(k2_funct_2(sK0,sK2)) = iProver_top
% 3.33/1.01      | v1_funct_1(sK2) != iProver_top ),
% 3.33/1.01      inference(superposition,[status(thm)],[c_1344,c_1347]) ).
% 3.33/1.01  
% 3.33/1.01  cnf(c_3242,plain,
% 3.33/1.01      ( v1_funct_2(sK2,sK0,sK0) != iProver_top
% 3.33/1.01      | v3_funct_2(sK2,sK0,sK0) != iProver_top
% 3.33/1.01      | v1_funct_1(k2_funct_1(sK2)) = iProver_top
% 3.33/1.01      | v1_funct_1(sK2) != iProver_top ),
% 3.33/1.01      inference(light_normalisation,[status(thm)],[c_3241,c_2923]) ).
% 3.33/1.01  
% 3.33/1.01  cnf(c_24,plain,
% 3.33/1.01      ( ~ v1_funct_2(X0,X1,X1)
% 3.33/1.01      | ~ v3_funct_2(X0,X1,X1)
% 3.33/1.01      | v3_funct_2(k2_funct_2(X1,X0),X1,X1)
% 3.33/1.01      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X1)))
% 3.33/1.01      | ~ v1_funct_1(X0) ),
% 3.33/1.01      inference(cnf_transformation,[],[f79]) ).
% 3.33/1.01  
% 3.33/1.01  cnf(c_1349,plain,
% 3.33/1.01      ( v1_funct_2(X0,X1,X1) != iProver_top
% 3.33/1.01      | v3_funct_2(X0,X1,X1) != iProver_top
% 3.33/1.01      | v3_funct_2(k2_funct_2(X1,X0),X1,X1) = iProver_top
% 3.33/1.01      | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X1))) != iProver_top
% 3.33/1.01      | v1_funct_1(X0) != iProver_top ),
% 3.33/1.01      inference(predicate_to_equality,[status(thm)],[c_24]) ).
% 3.33/1.01  
% 3.33/1.01  cnf(c_4380,plain,
% 3.33/1.01      ( v1_funct_2(sK2,sK0,sK0) != iProver_top
% 3.33/1.01      | v3_funct_2(k2_funct_2(sK0,sK2),sK0,sK0) = iProver_top
% 3.33/1.01      | v3_funct_2(sK2,sK0,sK0) != iProver_top
% 3.33/1.01      | v1_funct_1(sK2) != iProver_top ),
% 3.33/1.01      inference(superposition,[status(thm)],[c_1344,c_1349]) ).
% 3.33/1.01  
% 3.33/1.01  cnf(c_4381,plain,
% 3.33/1.01      ( v1_funct_2(sK2,sK0,sK0) != iProver_top
% 3.33/1.01      | v3_funct_2(k2_funct_1(sK2),sK0,sK0) = iProver_top
% 3.33/1.01      | v3_funct_2(sK2,sK0,sK0) != iProver_top
% 3.33/1.01      | v1_funct_1(sK2) != iProver_top ),
% 3.33/1.01      inference(light_normalisation,[status(thm)],[c_4380,c_2923]) ).
% 3.33/1.01  
% 3.33/1.01  cnf(c_3,plain,
% 3.33/1.01      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
% 3.33/1.01      | ~ v1_relat_1(X1)
% 3.33/1.01      | v1_relat_1(X0) ),
% 3.33/1.01      inference(cnf_transformation,[],[f57]) ).
% 3.33/1.01  
% 3.33/1.01  cnf(c_1365,plain,
% 3.33/1.01      ( m1_subset_1(X0,k1_zfmisc_1(X1)) != iProver_top
% 3.33/1.01      | v1_relat_1(X1) != iProver_top
% 3.33/1.01      | v1_relat_1(X0) = iProver_top ),
% 3.33/1.01      inference(predicate_to_equality,[status(thm)],[c_3]) ).
% 3.33/1.01  
% 3.33/1.01  cnf(c_4723,plain,
% 3.33/1.01      ( v1_relat_1(k2_zfmisc_1(sK0,sK0)) != iProver_top
% 3.33/1.01      | v1_relat_1(k2_funct_1(sK2)) = iProver_top ),
% 3.33/1.01      inference(superposition,[status(thm)],[c_4718,c_1365]) ).
% 3.33/1.01  
% 3.33/1.01  cnf(c_6657,plain,
% 3.33/1.01      ( k2_relat_1(k2_funct_1(sK2)) = sK0 ),
% 3.33/1.01      inference(global_propositional_subsumption,
% 3.33/1.01                [status(thm)],
% 3.33/1.01                [c_4726,c_34,c_35,c_36,c_102,c_3242,c_4381,c_4723]) ).
% 3.33/1.01  
% 3.33/1.01  cnf(c_11,plain,
% 3.33/1.01      ( ~ r1_tarski(X0,k2_relat_1(X1))
% 3.33/1.01      | ~ v1_funct_1(X1)
% 3.33/1.01      | ~ v1_relat_1(X1)
% 3.33/1.01      | k9_relat_1(X1,k10_relat_1(X1,X0)) = X0 ),
% 3.33/1.01      inference(cnf_transformation,[],[f65]) ).
% 3.33/1.01  
% 3.33/1.01  cnf(c_1357,plain,
% 3.33/1.01      ( k9_relat_1(X0,k10_relat_1(X0,X1)) = X1
% 3.33/1.01      | r1_tarski(X1,k2_relat_1(X0)) != iProver_top
% 3.33/1.01      | v1_funct_1(X0) != iProver_top
% 3.33/1.01      | v1_relat_1(X0) != iProver_top ),
% 3.33/1.01      inference(predicate_to_equality,[status(thm)],[c_11]) ).
% 3.33/1.01  
% 3.33/1.01  cnf(c_6670,plain,
% 3.33/1.01      ( k9_relat_1(k2_funct_1(sK2),k10_relat_1(k2_funct_1(sK2),X0)) = X0
% 3.33/1.01      | r1_tarski(X0,sK0) != iProver_top
% 3.33/1.01      | v1_funct_1(k2_funct_1(sK2)) != iProver_top
% 3.33/1.01      | v1_relat_1(k2_funct_1(sK2)) != iProver_top ),
% 3.33/1.01      inference(superposition,[status(thm)],[c_6657,c_1357]) ).
% 3.33/1.01  
% 3.33/1.01  cnf(c_19,plain,
% 3.33/1.01      ( ~ v3_funct_2(X0,X1,X2)
% 3.33/1.01      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.33/1.01      | v2_funct_1(X0)
% 3.33/1.01      | ~ v1_funct_1(X0) ),
% 3.33/1.01      inference(cnf_transformation,[],[f73]) ).
% 3.33/1.01  
% 3.33/1.01  cnf(c_1351,plain,
% 3.33/1.01      ( v3_funct_2(X0,X1,X2) != iProver_top
% 3.33/1.01      | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) != iProver_top
% 3.33/1.01      | v2_funct_1(X0) = iProver_top
% 3.33/1.01      | v1_funct_1(X0) != iProver_top ),
% 3.33/1.01      inference(predicate_to_equality,[status(thm)],[c_19]) ).
% 3.33/1.01  
% 3.33/1.01  cnf(c_3840,plain,
% 3.33/1.01      ( v3_funct_2(sK2,sK0,sK0) != iProver_top
% 3.33/1.01      | v2_funct_1(sK2) = iProver_top
% 3.33/1.01      | v1_funct_1(sK2) != iProver_top ),
% 3.33/1.01      inference(superposition,[status(thm)],[c_1344,c_1351]) ).
% 3.33/1.01  
% 3.33/1.01  cnf(c_1669,plain,
% 3.33/1.01      ( ~ v3_funct_2(sK2,X0,X1)
% 3.33/1.01      | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
% 3.33/1.01      | v2_funct_1(sK2)
% 3.33/1.01      | ~ v1_funct_1(sK2) ),
% 3.33/1.01      inference(instantiation,[status(thm)],[c_19]) ).
% 3.33/1.01  
% 3.33/1.01  cnf(c_1670,plain,
% 3.33/1.01      ( v3_funct_2(sK2,X0,X1) != iProver_top
% 3.33/1.01      | m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top
% 3.33/1.01      | v2_funct_1(sK2) = iProver_top
% 3.33/1.01      | v1_funct_1(sK2) != iProver_top ),
% 3.33/1.01      inference(predicate_to_equality,[status(thm)],[c_1669]) ).
% 3.33/1.01  
% 3.33/1.01  cnf(c_1672,plain,
% 3.33/1.01      ( v3_funct_2(sK2,sK0,sK0) != iProver_top
% 3.33/1.01      | m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) != iProver_top
% 3.33/1.01      | v2_funct_1(sK2) = iProver_top
% 3.33/1.01      | v1_funct_1(sK2) != iProver_top ),
% 3.33/1.01      inference(instantiation,[status(thm)],[c_1670]) ).
% 3.33/1.01  
% 3.33/1.01  cnf(c_3843,plain,
% 3.33/1.01      ( v2_funct_1(sK2) = iProver_top ),
% 3.33/1.01      inference(global_propositional_subsumption,
% 3.33/1.01                [status(thm)],
% 3.33/1.01                [c_3840,c_34,c_36,c_37,c_1672]) ).
% 3.33/1.01  
% 3.33/1.01  cnf(c_12,plain,
% 3.33/1.01      ( ~ v2_funct_1(X0)
% 3.33/1.01      | ~ v1_funct_1(X0)
% 3.33/1.01      | ~ v1_relat_1(X0)
% 3.33/1.01      | k10_relat_1(k2_funct_1(X0),X1) = k9_relat_1(X0,X1) ),
% 3.33/1.01      inference(cnf_transformation,[],[f66]) ).
% 3.33/1.01  
% 3.33/1.01  cnf(c_1356,plain,
% 3.33/1.01      ( k10_relat_1(k2_funct_1(X0),X1) = k9_relat_1(X0,X1)
% 3.33/1.01      | v2_funct_1(X0) != iProver_top
% 3.33/1.01      | v1_funct_1(X0) != iProver_top
% 3.33/1.01      | v1_relat_1(X0) != iProver_top ),
% 3.33/1.01      inference(predicate_to_equality,[status(thm)],[c_12]) ).
% 3.33/1.01  
% 3.33/1.01  cnf(c_3848,plain,
% 3.33/1.01      ( k10_relat_1(k2_funct_1(sK2),X0) = k9_relat_1(sK2,X0)
% 3.33/1.01      | v1_funct_1(sK2) != iProver_top
% 3.33/1.01      | v1_relat_1(sK2) != iProver_top ),
% 3.33/1.01      inference(superposition,[status(thm)],[c_3843,c_1356]) ).
% 3.33/1.01  
% 3.33/1.01  cnf(c_101,plain,
% 3.33/1.01      ( v1_relat_1(k2_zfmisc_1(sK0,sK0)) ),
% 3.33/1.01      inference(instantiation,[status(thm)],[c_6]) ).
% 3.33/1.01  
% 3.33/1.01  cnf(c_1671,plain,
% 3.33/1.01      ( ~ v3_funct_2(sK2,sK0,sK0)
% 3.33/1.01      | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
% 3.33/1.01      | v2_funct_1(sK2)
% 3.33/1.01      | ~ v1_funct_1(sK2) ),
% 3.33/1.01      inference(instantiation,[status(thm)],[c_1669]) ).
% 3.33/1.01  
% 3.33/1.01  cnf(c_1598,plain,
% 3.33/1.01      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.33/1.01      | v1_relat_1(X0)
% 3.33/1.01      | ~ v1_relat_1(k2_zfmisc_1(X1,X2)) ),
% 3.33/1.01      inference(instantiation,[status(thm)],[c_3]) ).
% 3.33/1.01  
% 3.33/1.01  cnf(c_1765,plain,
% 3.33/1.01      ( ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
% 3.33/1.01      | ~ v1_relat_1(k2_zfmisc_1(sK0,sK0))
% 3.33/1.01      | v1_relat_1(sK2) ),
% 3.33/1.01      inference(instantiation,[status(thm)],[c_1598]) ).
% 3.33/1.01  
% 3.33/1.01  cnf(c_1784,plain,
% 3.33/1.01      ( ~ v2_funct_1(sK2)
% 3.33/1.01      | ~ v1_funct_1(sK2)
% 3.33/1.01      | ~ v1_relat_1(sK2)
% 3.33/1.01      | k10_relat_1(k2_funct_1(sK2),X0) = k9_relat_1(sK2,X0) ),
% 3.33/1.01      inference(instantiation,[status(thm)],[c_12]) ).
% 3.33/1.01  
% 3.33/1.01  cnf(c_3937,plain,
% 3.33/1.01      ( k10_relat_1(k2_funct_1(sK2),X0) = k9_relat_1(sK2,X0) ),
% 3.33/1.01      inference(global_propositional_subsumption,
% 3.33/1.01                [status(thm)],
% 3.33/1.01                [c_3848,c_33,c_31,c_30,c_101,c_1671,c_1765,c_1784]) ).
% 3.33/1.01  
% 3.33/1.01  cnf(c_6671,plain,
% 3.33/1.01      ( k9_relat_1(k2_funct_1(sK2),k9_relat_1(sK2,X0)) = X0
% 3.33/1.01      | r1_tarski(X0,sK0) != iProver_top
% 3.33/1.01      | v1_funct_1(k2_funct_1(sK2)) != iProver_top
% 3.33/1.01      | v1_relat_1(k2_funct_1(sK2)) != iProver_top ),
% 3.33/1.01      inference(light_normalisation,[status(thm)],[c_6670,c_3937]) ).
% 3.33/1.01  
% 3.33/1.01  cnf(c_6800,plain,
% 3.33/1.01      ( k9_relat_1(k2_funct_1(sK2),k9_relat_1(sK2,X0)) = X0
% 3.33/1.01      | r1_tarski(X0,sK0) != iProver_top ),
% 3.33/1.01      inference(global_propositional_subsumption,
% 3.33/1.01                [status(thm)],
% 3.33/1.01                [c_6671,c_34,c_35,c_36,c_102,c_3242,c_4723]) ).
% 3.33/1.01  
% 3.33/1.01  cnf(c_6809,plain,
% 3.33/1.01      ( k9_relat_1(k2_funct_1(sK2),k9_relat_1(sK2,k1_relat_1(X0))) = k1_relat_1(X0)
% 3.33/1.01      | v4_relat_1(X0,sK0) != iProver_top
% 3.33/1.01      | v1_relat_1(X0) != iProver_top ),
% 3.33/1.01      inference(superposition,[status(thm)],[c_1363,c_6800]) ).
% 3.33/1.01  
% 3.33/1.01  cnf(c_8212,plain,
% 3.33/1.01      ( k9_relat_1(k2_funct_1(sK2),k9_relat_1(sK2,k1_relat_1(sK2))) = k1_relat_1(sK2)
% 3.33/1.01      | v1_relat_1(sK2) != iProver_top ),
% 3.33/1.01      inference(superposition,[status(thm)],[c_1813,c_6809]) ).
% 3.33/1.01  
% 3.33/1.01  cnf(c_1,plain,
% 3.33/1.01      ( r1_tarski(X0,X0) ),
% 3.33/1.01      inference(cnf_transformation,[],[f88]) ).
% 3.33/1.01  
% 3.33/1.01  cnf(c_1366,plain,
% 3.33/1.01      ( r1_tarski(X0,X0) = iProver_top ),
% 3.33/1.01      inference(predicate_to_equality,[status(thm)],[c_1]) ).
% 3.33/1.01  
% 3.33/1.01  cnf(c_1758,plain,
% 3.33/1.01      ( k2_relat_1(sK2) = sK0
% 3.33/1.01      | v3_funct_2(sK2,sK0,sK0) != iProver_top
% 3.33/1.01      | v1_funct_1(sK2) != iProver_top
% 3.33/1.01      | v1_relat_1(sK2) != iProver_top ),
% 3.33/1.01      inference(superposition,[status(thm)],[c_1344,c_1340]) ).
% 3.33/1.01  
% 3.33/1.01  cnf(c_1759,plain,
% 3.33/1.01      ( ~ v3_funct_2(sK2,sK0,sK0)
% 3.33/1.01      | ~ v1_funct_1(sK2)
% 3.33/1.01      | ~ v1_relat_1(sK2)
% 3.33/1.01      | k2_relat_1(sK2) = sK0 ),
% 3.33/1.01      inference(predicate_to_equality_rev,[status(thm)],[c_1758]) ).
% 3.33/1.01  
% 3.33/1.01  cnf(c_2132,plain,
% 3.33/1.01      ( k2_relat_1(sK2) = sK0 ),
% 3.33/1.01      inference(global_propositional_subsumption,
% 3.33/1.01                [status(thm)],
% 3.33/1.01                [c_1758,c_33,c_31,c_30,c_101,c_1759,c_1765]) ).
% 3.33/1.01  
% 3.33/1.01  cnf(c_3690,plain,
% 3.33/1.01      ( k9_relat_1(sK2,k10_relat_1(sK2,X0)) = X0
% 3.33/1.01      | r1_tarski(X0,sK0) != iProver_top
% 3.33/1.01      | v1_funct_1(sK2) != iProver_top
% 3.33/1.01      | v1_relat_1(sK2) != iProver_top ),
% 3.33/1.01      inference(superposition,[status(thm)],[c_2132,c_1357]) ).
% 3.33/1.01  
% 3.33/1.01  cnf(c_1766,plain,
% 3.33/1.01      ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) != iProver_top
% 3.33/1.01      | v1_relat_1(k2_zfmisc_1(sK0,sK0)) != iProver_top
% 3.33/1.01      | v1_relat_1(sK2) = iProver_top ),
% 3.33/1.01      inference(predicate_to_equality,[status(thm)],[c_1765]) ).
% 3.33/1.01  
% 3.33/1.01  cnf(c_3946,plain,
% 3.33/1.01      ( k9_relat_1(sK2,k10_relat_1(sK2,X0)) = X0
% 3.33/1.01      | r1_tarski(X0,sK0) != iProver_top ),
% 3.33/1.01      inference(global_propositional_subsumption,
% 3.33/1.01                [status(thm)],
% 3.33/1.01                [c_3690,c_34,c_37,c_102,c_1766]) ).
% 3.33/1.01  
% 3.33/1.01  cnf(c_3954,plain,
% 3.33/1.01      ( k9_relat_1(sK2,k10_relat_1(sK2,sK0)) = sK0 ),
% 3.33/1.01      inference(superposition,[status(thm)],[c_1366,c_3946]) ).
% 3.33/1.01  
% 3.33/1.01  cnf(c_2379,plain,
% 3.33/1.01      ( v1_relat_1(k2_zfmisc_1(sK0,sK0)) != iProver_top
% 3.33/1.01      | v1_relat_1(sK2) = iProver_top ),
% 3.33/1.01      inference(superposition,[status(thm)],[c_1344,c_1365]) ).
% 3.33/1.01  
% 3.33/1.01  cnf(c_2842,plain,
% 3.33/1.01      ( v1_relat_1(sK2) = iProver_top ),
% 3.33/1.01      inference(global_propositional_subsumption,
% 3.33/1.01                [status(thm)],
% 3.33/1.01                [c_2379,c_37,c_102,c_1766]) ).
% 3.33/1.01  
% 3.33/1.01  cnf(c_8,plain,
% 3.33/1.01      ( ~ v1_relat_1(X0)
% 3.33/1.01      | k10_relat_1(X0,k2_relat_1(X0)) = k1_relat_1(X0) ),
% 3.33/1.01      inference(cnf_transformation,[],[f62]) ).
% 3.33/1.01  
% 3.33/1.01  cnf(c_1360,plain,
% 3.33/1.01      ( k10_relat_1(X0,k2_relat_1(X0)) = k1_relat_1(X0)
% 3.33/1.01      | v1_relat_1(X0) != iProver_top ),
% 3.33/1.01      inference(predicate_to_equality,[status(thm)],[c_8]) ).
% 3.33/1.01  
% 3.33/1.01  cnf(c_2848,plain,
% 3.33/1.01      ( k10_relat_1(sK2,k2_relat_1(sK2)) = k1_relat_1(sK2) ),
% 3.33/1.01      inference(superposition,[status(thm)],[c_2842,c_1360]) ).
% 3.33/1.01  
% 3.33/1.01  cnf(c_2850,plain,
% 3.33/1.01      ( k10_relat_1(sK2,sK0) = k1_relat_1(sK2) ),
% 3.33/1.01      inference(light_normalisation,[status(thm)],[c_2848,c_2132]) ).
% 3.33/1.01  
% 3.33/1.01  cnf(c_3973,plain,
% 3.33/1.01      ( k9_relat_1(sK2,k1_relat_1(sK2)) = sK0 ),
% 3.33/1.01      inference(light_normalisation,[status(thm)],[c_3954,c_2850]) ).
% 3.33/1.01  
% 3.33/1.01  cnf(c_6808,plain,
% 3.33/1.01      ( k9_relat_1(k2_funct_1(sK2),k9_relat_1(sK2,sK0)) = sK0 ),
% 3.33/1.01      inference(superposition,[status(thm)],[c_1366,c_6800]) ).
% 3.33/1.01  
% 3.33/1.01  cnf(c_9,plain,
% 3.33/1.01      ( ~ v4_relat_1(X0,X1) | ~ v1_relat_1(X0) | k7_relat_1(X0,X1) = X0 ),
% 3.33/1.01      inference(cnf_transformation,[],[f63]) ).
% 3.33/1.01  
% 3.33/1.01  cnf(c_1359,plain,
% 3.33/1.01      ( k7_relat_1(X0,X1) = X0
% 3.33/1.01      | v4_relat_1(X0,X1) != iProver_top
% 3.33/1.01      | v1_relat_1(X0) != iProver_top ),
% 3.33/1.01      inference(predicate_to_equality,[status(thm)],[c_9]) ).
% 3.33/1.01  
% 3.33/1.01  cnf(c_2292,plain,
% 3.33/1.01      ( k7_relat_1(sK2,sK0) = sK2 | v1_relat_1(sK2) != iProver_top ),
% 3.33/1.01      inference(superposition,[status(thm)],[c_1813,c_1359]) ).
% 3.33/1.01  
% 3.33/1.01  cnf(c_1632,plain,
% 3.33/1.01      ( v4_relat_1(sK2,sK0)
% 3.33/1.01      | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) ),
% 3.33/1.01      inference(instantiation,[status(thm)],[c_15]) ).
% 3.33/1.01  
% 3.33/1.01  cnf(c_1885,plain,
% 3.33/1.01      ( ~ v4_relat_1(sK2,X0)
% 3.33/1.01      | ~ v1_relat_1(sK2)
% 3.33/1.01      | k7_relat_1(sK2,X0) = sK2 ),
% 3.33/1.01      inference(instantiation,[status(thm)],[c_9]) ).
% 3.33/1.01  
% 3.33/1.01  cnf(c_1903,plain,
% 3.33/1.01      ( ~ v4_relat_1(sK2,sK0)
% 3.33/1.01      | ~ v1_relat_1(sK2)
% 3.33/1.01      | k7_relat_1(sK2,sK0) = sK2 ),
% 3.33/1.01      inference(instantiation,[status(thm)],[c_1885]) ).
% 3.33/1.01  
% 3.33/1.01  cnf(c_2295,plain,
% 3.33/1.01      ( k7_relat_1(sK2,sK0) = sK2 ),
% 3.33/1.01      inference(global_propositional_subsumption,
% 3.33/1.01                [status(thm)],
% 3.33/1.01                [c_2292,c_30,c_101,c_1632,c_1765,c_1903]) ).
% 3.33/1.01  
% 3.33/1.01  cnf(c_7,plain,
% 3.33/1.01      ( ~ v1_relat_1(X0)
% 3.33/1.01      | k2_relat_1(k7_relat_1(X0,X1)) = k9_relat_1(X0,X1) ),
% 3.33/1.01      inference(cnf_transformation,[],[f61]) ).
% 3.33/1.01  
% 3.33/1.01  cnf(c_1361,plain,
% 3.33/1.01      ( k2_relat_1(k7_relat_1(X0,X1)) = k9_relat_1(X0,X1)
% 3.33/1.01      | v1_relat_1(X0) != iProver_top ),
% 3.33/1.01      inference(predicate_to_equality,[status(thm)],[c_7]) ).
% 3.33/1.01  
% 3.33/1.01  cnf(c_2847,plain,
% 3.33/1.01      ( k2_relat_1(k7_relat_1(sK2,X0)) = k9_relat_1(sK2,X0) ),
% 3.33/1.01      inference(superposition,[status(thm)],[c_2842,c_1361]) ).
% 3.33/1.01  
% 3.33/1.01  cnf(c_3052,plain,
% 3.33/1.01      ( k9_relat_1(sK2,sK0) = k2_relat_1(sK2) ),
% 3.33/1.01      inference(superposition,[status(thm)],[c_2295,c_2847]) ).
% 3.33/1.01  
% 3.33/1.01  cnf(c_3053,plain,
% 3.33/1.01      ( k9_relat_1(sK2,sK0) = sK0 ),
% 3.33/1.01      inference(light_normalisation,[status(thm)],[c_3052,c_2132]) ).
% 3.33/1.01  
% 3.33/1.01  cnf(c_6833,plain,
% 3.33/1.01      ( k9_relat_1(k2_funct_1(sK2),sK0) = sK0 ),
% 3.33/1.01      inference(light_normalisation,[status(thm)],[c_6808,c_3053]) ).
% 3.33/1.01  
% 3.33/1.01  cnf(c_8224,plain,
% 3.33/1.01      ( k1_relat_1(sK2) = sK0 | v1_relat_1(sK2) != iProver_top ),
% 3.33/1.01      inference(light_normalisation,[status(thm)],[c_8212,c_3973,c_6833]) ).
% 3.33/1.01  
% 3.33/1.01  cnf(c_8724,plain,
% 3.33/1.01      ( k1_relat_1(sK2) = sK0 ),
% 3.33/1.01      inference(global_propositional_subsumption,
% 3.33/1.01                [status(thm)],
% 3.33/1.01                [c_8224,c_37,c_102,c_1766]) ).
% 3.33/1.01  
% 3.33/1.01  cnf(c_13,plain,
% 3.33/1.01      ( ~ r1_tarski(X0,k1_relat_1(X1))
% 3.33/1.01      | ~ v2_funct_1(X1)
% 3.33/1.01      | ~ v1_funct_1(X1)
% 3.33/1.01      | ~ v1_relat_1(X1)
% 3.33/1.01      | k10_relat_1(X1,k9_relat_1(X1,X0)) = X0 ),
% 3.33/1.01      inference(cnf_transformation,[],[f67]) ).
% 3.33/1.01  
% 3.33/1.01  cnf(c_1355,plain,
% 3.33/1.01      ( k10_relat_1(X0,k9_relat_1(X0,X1)) = X1
% 3.33/1.01      | r1_tarski(X1,k1_relat_1(X0)) != iProver_top
% 3.33/1.01      | v2_funct_1(X0) != iProver_top
% 3.33/1.01      | v1_funct_1(X0) != iProver_top
% 3.33/1.01      | v1_relat_1(X0) != iProver_top ),
% 3.33/1.01      inference(predicate_to_equality,[status(thm)],[c_13]) ).
% 3.33/1.01  
% 3.33/1.01  cnf(c_8746,plain,
% 3.33/1.01      ( k10_relat_1(sK2,k9_relat_1(sK2,X0)) = X0
% 3.33/1.01      | r1_tarski(X0,sK0) != iProver_top
% 3.33/1.01      | v2_funct_1(sK2) != iProver_top
% 3.33/1.01      | v1_funct_1(sK2) != iProver_top
% 3.33/1.01      | v1_relat_1(sK2) != iProver_top ),
% 3.33/1.01      inference(superposition,[status(thm)],[c_8724,c_1355]) ).
% 3.33/1.01  
% 3.33/1.01  cnf(c_11223,plain,
% 3.33/1.01      ( r1_tarski(X0,sK0) != iProver_top
% 3.33/1.01      | k10_relat_1(sK2,k9_relat_1(sK2,X0)) = X0 ),
% 3.33/1.01      inference(global_propositional_subsumption,
% 3.33/1.01                [status(thm)],
% 3.33/1.01                [c_8746,c_34,c_36,c_37,c_102,c_1672,c_1766]) ).
% 3.33/1.01  
% 3.33/1.01  cnf(c_11224,plain,
% 3.33/1.01      ( k10_relat_1(sK2,k9_relat_1(sK2,X0)) = X0
% 3.33/1.01      | r1_tarski(X0,sK0) != iProver_top ),
% 3.33/1.01      inference(renaming,[status(thm)],[c_11223]) ).
% 3.33/1.01  
% 3.33/1.01  cnf(c_11234,plain,
% 3.33/1.01      ( k10_relat_1(sK2,k9_relat_1(sK2,sK1)) = sK1 ),
% 3.33/1.01      inference(superposition,[status(thm)],[c_1345,c_11224]) ).
% 3.33/1.01  
% 3.33/1.01  cnf(c_3957,plain,
% 3.33/1.01      ( k9_relat_1(sK2,k10_relat_1(sK2,sK1)) = sK1 ),
% 3.33/1.01      inference(superposition,[status(thm)],[c_1345,c_3946]) ).
% 3.33/1.01  
% 3.33/1.01  cnf(c_17,plain,
% 3.33/1.01      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.33/1.01      | k8_relset_1(X1,X2,X0,X3) = k10_relat_1(X0,X3) ),
% 3.33/1.01      inference(cnf_transformation,[],[f71]) ).
% 3.33/1.01  
% 3.33/1.01  cnf(c_1352,plain,
% 3.33/1.01      ( k8_relset_1(X0,X1,X2,X3) = k10_relat_1(X2,X3)
% 3.33/1.01      | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
% 3.33/1.01      inference(predicate_to_equality,[status(thm)],[c_17]) ).
% 3.33/1.01  
% 3.33/1.01  cnf(c_2497,plain,
% 3.33/1.01      ( k8_relset_1(sK0,sK0,sK2,X0) = k10_relat_1(sK2,X0) ),
% 3.33/1.01      inference(superposition,[status(thm)],[c_1344,c_1352]) ).
% 3.33/1.01  
% 3.33/1.01  cnf(c_28,negated_conjecture,
% 3.33/1.01      ( k8_relset_1(sK0,sK0,sK2,k7_relset_1(sK0,sK0,sK2,sK1)) != sK1
% 3.33/1.01      | k7_relset_1(sK0,sK0,sK2,k8_relset_1(sK0,sK0,sK2,sK1)) != sK1 ),
% 3.33/1.01      inference(cnf_transformation,[],[f87]) ).
% 3.33/1.01  
% 3.33/1.01  cnf(c_2783,plain,
% 3.33/1.01      ( k7_relset_1(sK0,sK0,sK2,k8_relset_1(sK0,sK0,sK2,sK1)) != sK1
% 3.33/1.01      | k10_relat_1(sK2,k7_relset_1(sK0,sK0,sK2,sK1)) != sK1 ),
% 3.33/1.01      inference(demodulation,[status(thm)],[c_2497,c_28]) ).
% 3.33/1.01  
% 3.33/1.01  cnf(c_2784,plain,
% 3.33/1.01      ( k7_relset_1(sK0,sK0,sK2,k10_relat_1(sK2,sK1)) != sK1
% 3.33/1.01      | k10_relat_1(sK2,k7_relset_1(sK0,sK0,sK2,sK1)) != sK1 ),
% 3.33/1.01      inference(demodulation,[status(thm)],[c_2783,c_2497]) ).
% 3.33/1.01  
% 3.33/1.01  cnf(c_16,plain,
% 3.33/1.01      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.33/1.01      | k7_relset_1(X1,X2,X0,X3) = k9_relat_1(X0,X3) ),
% 3.33/1.01      inference(cnf_transformation,[],[f70]) ).
% 3.33/1.01  
% 3.33/1.01  cnf(c_1353,plain,
% 3.33/1.01      ( k7_relset_1(X0,X1,X2,X3) = k9_relat_1(X2,X3)
% 3.33/1.01      | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
% 3.33/1.01      inference(predicate_to_equality,[status(thm)],[c_16]) ).
% 3.33/1.01  
% 3.33/1.01  cnf(c_2502,plain,
% 3.33/1.01      ( k7_relset_1(sK0,sK0,sK2,X0) = k9_relat_1(sK2,X0) ),
% 3.33/1.01      inference(superposition,[status(thm)],[c_1344,c_1353]) ).
% 3.33/1.01  
% 3.33/1.01  cnf(c_2855,plain,
% 3.33/1.01      ( k10_relat_1(sK2,k9_relat_1(sK2,sK1)) != sK1
% 3.33/1.01      | k9_relat_1(sK2,k10_relat_1(sK2,sK1)) != sK1 ),
% 3.33/1.01      inference(demodulation,[status(thm)],[c_2784,c_2502]) ).
% 3.33/1.01  
% 3.33/1.01  cnf(contradiction,plain,
% 3.33/1.01      ( $false ),
% 3.33/1.01      inference(minisat,[status(thm)],[c_11234,c_3957,c_2855]) ).
% 3.33/1.01  
% 3.33/1.01  
% 3.33/1.01  % SZS output end CNFRefutation for theBenchmark.p
% 3.33/1.01  
% 3.33/1.01  ------                               Statistics
% 3.33/1.01  
% 3.33/1.01  ------ General
% 3.33/1.01  
% 3.33/1.01  abstr_ref_over_cycles:                  0
% 3.33/1.01  abstr_ref_under_cycles:                 0
% 3.33/1.01  gc_basic_clause_elim:                   0
% 3.33/1.01  forced_gc_time:                         0
% 3.33/1.01  parsing_time:                           0.016
% 3.33/1.01  unif_index_cands_time:                  0.
% 3.33/1.01  unif_index_add_time:                    0.
% 3.33/1.01  orderings_time:                         0.
% 3.33/1.01  out_proof_time:                         0.012
% 3.33/1.01  total_time:                             0.364
% 3.33/1.01  num_of_symbols:                         55
% 3.33/1.01  num_of_terms:                           15809
% 3.33/1.01  
% 3.33/1.01  ------ Preprocessing
% 3.33/1.01  
% 3.33/1.01  num_of_splits:                          0
% 3.33/1.01  num_of_split_atoms:                     0
% 3.33/1.01  num_of_reused_defs:                     0
% 3.33/1.01  num_eq_ax_congr_red:                    32
% 3.33/1.01  num_of_sem_filtered_clauses:            1
% 3.33/1.01  num_of_subtypes:                        0
% 3.33/1.01  monotx_restored_types:                  0
% 3.33/1.01  sat_num_of_epr_types:                   0
% 3.33/1.01  sat_num_of_non_cyclic_types:            0
% 3.33/1.01  sat_guarded_non_collapsed_types:        0
% 3.33/1.01  num_pure_diseq_elim:                    0
% 3.33/1.01  simp_replaced_by:                       0
% 3.33/1.01  res_preprocessed:                       150
% 3.33/1.01  prep_upred:                             0
% 3.33/1.01  prep_unflattend:                        8
% 3.33/1.01  smt_new_axioms:                         0
% 3.33/1.01  pred_elim_cands:                        8
% 3.33/1.01  pred_elim:                              2
% 3.33/1.01  pred_elim_cl:                           3
% 3.33/1.01  pred_elim_cycles:                       7
% 3.33/1.01  merged_defs:                            0
% 3.33/1.01  merged_defs_ncl:                        0
% 3.33/1.01  bin_hyper_res:                          0
% 3.33/1.01  prep_cycles:                            4
% 3.33/1.01  pred_elim_time:                         0.006
% 3.33/1.01  splitting_time:                         0.
% 3.33/1.01  sem_filter_time:                        0.
% 3.33/1.01  monotx_time:                            0.001
% 3.33/1.01  subtype_inf_time:                       0.
% 3.33/1.01  
% 3.33/1.01  ------ Problem properties
% 3.33/1.01  
% 3.33/1.01  clauses:                                29
% 3.33/1.01  conjectures:                            6
% 3.33/1.01  epr:                                    6
% 3.33/1.01  horn:                                   29
% 3.33/1.01  ground:                                 6
% 3.33/1.01  unary:                                  7
% 3.33/1.01  binary:                                 6
% 3.33/1.01  lits:                                   84
% 3.33/1.01  lits_eq:                                13
% 3.33/1.01  fd_pure:                                0
% 3.33/1.01  fd_pseudo:                              0
% 3.33/1.01  fd_cond:                                0
% 3.33/1.01  fd_pseudo_cond:                         2
% 3.33/1.01  ac_symbols:                             0
% 3.33/1.01  
% 3.33/1.01  ------ Propositional Solver
% 3.33/1.01  
% 3.33/1.01  prop_solver_calls:                      28
% 3.33/1.01  prop_fast_solver_calls:                 1372
% 3.33/1.01  smt_solver_calls:                       0
% 3.33/1.01  smt_fast_solver_calls:                  0
% 3.33/1.01  prop_num_of_clauses:                    5224
% 3.33/1.01  prop_preprocess_simplified:             10585
% 3.33/1.01  prop_fo_subsumed:                       75
% 3.33/1.01  prop_solver_time:                       0.
% 3.33/1.01  smt_solver_time:                        0.
% 3.33/1.01  smt_fast_solver_time:                   0.
% 3.33/1.01  prop_fast_solver_time:                  0.
% 3.33/1.01  prop_unsat_core_time:                   0.
% 3.33/1.01  
% 3.33/1.01  ------ QBF
% 3.33/1.01  
% 3.33/1.01  qbf_q_res:                              0
% 3.33/1.01  qbf_num_tautologies:                    0
% 3.33/1.01  qbf_prep_cycles:                        0
% 3.33/1.01  
% 3.33/1.01  ------ BMC1
% 3.33/1.01  
% 3.33/1.01  bmc1_current_bound:                     -1
% 3.33/1.01  bmc1_last_solved_bound:                 -1
% 3.33/1.01  bmc1_unsat_core_size:                   -1
% 3.33/1.01  bmc1_unsat_core_parents_size:           -1
% 3.33/1.01  bmc1_merge_next_fun:                    0
% 3.33/1.01  bmc1_unsat_core_clauses_time:           0.
% 3.33/1.01  
% 3.33/1.01  ------ Instantiation
% 3.33/1.01  
% 3.33/1.01  inst_num_of_clauses:                    1399
% 3.33/1.01  inst_num_in_passive:                    142
% 3.33/1.01  inst_num_in_active:                     634
% 3.33/1.01  inst_num_in_unprocessed:                623
% 3.33/1.01  inst_num_of_loops:                      650
% 3.33/1.01  inst_num_of_learning_restarts:          0
% 3.33/1.01  inst_num_moves_active_passive:          13
% 3.33/1.01  inst_lit_activity:                      0
% 3.33/1.01  inst_lit_activity_moves:                0
% 3.33/1.01  inst_num_tautologies:                   0
% 3.33/1.01  inst_num_prop_implied:                  0
% 3.33/1.01  inst_num_existing_simplified:           0
% 3.33/1.01  inst_num_eq_res_simplified:             0
% 3.33/1.01  inst_num_child_elim:                    0
% 3.33/1.01  inst_num_of_dismatching_blockings:      275
% 3.33/1.01  inst_num_of_non_proper_insts:           1088
% 3.33/1.01  inst_num_of_duplicates:                 0
% 3.33/1.01  inst_inst_num_from_inst_to_res:         0
% 3.33/1.01  inst_dismatching_checking_time:         0.
% 3.33/1.01  
% 3.33/1.01  ------ Resolution
% 3.33/1.01  
% 3.33/1.01  res_num_of_clauses:                     0
% 3.33/1.01  res_num_in_passive:                     0
% 3.33/1.01  res_num_in_active:                      0
% 3.33/1.01  res_num_of_loops:                       154
% 3.33/1.01  res_forward_subset_subsumed:            52
% 3.33/1.01  res_backward_subset_subsumed:           0
% 3.33/1.01  res_forward_subsumed:                   0
% 3.33/1.01  res_backward_subsumed:                  0
% 3.33/1.01  res_forward_subsumption_resolution:     1
% 3.33/1.01  res_backward_subsumption_resolution:    0
% 3.33/1.01  res_clause_to_clause_subsumption:       351
% 3.33/1.01  res_orphan_elimination:                 0
% 3.33/1.01  res_tautology_del:                      69
% 3.33/1.01  res_num_eq_res_simplified:              0
% 3.33/1.01  res_num_sel_changes:                    0
% 3.33/1.01  res_moves_from_active_to_pass:          0
% 3.33/1.01  
% 3.33/1.01  ------ Superposition
% 3.33/1.01  
% 3.33/1.01  sup_time_total:                         0.
% 3.33/1.01  sup_time_generating:                    0.
% 3.33/1.01  sup_time_sim_full:                      0.
% 3.33/1.01  sup_time_sim_immed:                     0.
% 3.33/1.01  
% 3.33/1.01  sup_num_of_clauses:                     169
% 3.33/1.01  sup_num_in_active:                      115
% 3.33/1.01  sup_num_in_passive:                     54
% 3.33/1.01  sup_num_of_loops:                       129
% 3.33/1.01  sup_fw_superposition:                   141
% 3.33/1.01  sup_bw_superposition:                   100
% 3.33/1.01  sup_immediate_simplified:               100
% 3.33/1.01  sup_given_eliminated:                   0
% 3.33/1.01  comparisons_done:                       0
% 3.33/1.01  comparisons_avoided:                    0
% 3.33/1.01  
% 3.33/1.01  ------ Simplifications
% 3.33/1.01  
% 3.33/1.01  
% 3.33/1.01  sim_fw_subset_subsumed:                 10
% 3.33/1.01  sim_bw_subset_subsumed:                 2
% 3.33/1.01  sim_fw_subsumed:                        19
% 3.33/1.01  sim_bw_subsumed:                        0
% 3.33/1.01  sim_fw_subsumption_res:                 0
% 3.33/1.01  sim_bw_subsumption_res:                 0
% 3.33/1.01  sim_tautology_del:                      2
% 3.33/1.01  sim_eq_tautology_del:                   37
% 3.33/1.01  sim_eq_res_simp:                        1
% 3.33/1.01  sim_fw_demodulated:                     18
% 3.33/1.01  sim_bw_demodulated:                     16
% 3.33/1.01  sim_light_normalised:                   85
% 3.33/1.01  sim_joinable_taut:                      0
% 3.33/1.01  sim_joinable_simp:                      0
% 3.33/1.01  sim_ac_normalised:                      0
% 3.33/1.01  sim_smt_subsumption:                    0
% 3.33/1.01  
%------------------------------------------------------------------------------
