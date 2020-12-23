%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n023.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:07:38 EST 2020

% Result     : Theorem 3.32s
% Output     : CNFRefutation 3.32s
% Verified   : 
% Statistics : Number of formulae       :  194 (1556 expanded)
%              Number of clauses        :  116 ( 482 expanded)
%              Number of leaves         :   19 ( 306 expanded)
%              Depth                    :   24
%              Number of atoms          :  621 (7964 expanded)
%              Number of equality atoms :  264 (2260 expanded)
%              Maximal formula depth    :   10 (   4 average)
%              Maximal clause size      :   14 (   3 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f18,conjecture,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
        & v3_funct_2(X2,X0,X0)
        & v1_funct_2(X2,X0,X0)
        & v1_funct_1(X2) )
     => ( r1_tarski(X1,X0)
       => ( k8_relset_1(X0,X0,X2,k7_relset_1(X0,X0,X2,X1)) = X1
          & k7_relset_1(X0,X0,X2,k8_relset_1(X0,X0,X2,X1)) = X1 ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f19,negated_conjecture,(
    ~ ! [X0,X1,X2] :
        ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
          & v3_funct_2(X2,X0,X0)
          & v1_funct_2(X2,X0,X0)
          & v1_funct_1(X2) )
       => ( r1_tarski(X1,X0)
         => ( k8_relset_1(X0,X0,X2,k7_relset_1(X0,X0,X2,X1)) = X1
            & k7_relset_1(X0,X0,X2,k8_relset_1(X0,X0,X2,X1)) = X1 ) ) ) ),
    inference(negated_conjecture,[],[f18])).

fof(f43,plain,(
    ? [X0,X1,X2] :
      ( ( k8_relset_1(X0,X0,X2,k7_relset_1(X0,X0,X2,X1)) != X1
        | k7_relset_1(X0,X0,X2,k8_relset_1(X0,X0,X2,X1)) != X1 )
      & r1_tarski(X1,X0)
      & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
      & v3_funct_2(X2,X0,X0)
      & v1_funct_2(X2,X0,X0)
      & v1_funct_1(X2) ) ),
    inference(ennf_transformation,[],[f19])).

fof(f44,plain,(
    ? [X0,X1,X2] :
      ( ( k8_relset_1(X0,X0,X2,k7_relset_1(X0,X0,X2,X1)) != X1
        | k7_relset_1(X0,X0,X2,k8_relset_1(X0,X0,X2,X1)) != X1 )
      & r1_tarski(X1,X0)
      & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
      & v3_funct_2(X2,X0,X0)
      & v1_funct_2(X2,X0,X0)
      & v1_funct_1(X2) ) ),
    inference(flattening,[],[f43])).

fof(f49,plain,
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

fof(f50,plain,
    ( ( k8_relset_1(sK0,sK0,sK2,k7_relset_1(sK0,sK0,sK2,sK1)) != sK1
      | k7_relset_1(sK0,sK0,sK2,k8_relset_1(sK0,sK0,sK2,sK1)) != sK1 )
    & r1_tarski(sK1,sK0)
    & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
    & v3_funct_2(sK2,sK0,sK0)
    & v1_funct_2(sK2,sK0,sK0)
    & v1_funct_1(sK2) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f44,f49])).

fof(f82,plain,(
    r1_tarski(sK1,sK0) ),
    inference(cnf_transformation,[],[f50])).

fof(f81,plain,(
    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) ),
    inference(cnf_transformation,[],[f50])).

fof(f17,axiom,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
        & v3_funct_2(X1,X0,X0)
        & v1_funct_2(X1,X0,X0)
        & v1_funct_1(X1) )
     => k2_funct_1(X1) = k2_funct_2(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f41,plain,(
    ! [X0,X1] :
      ( k2_funct_1(X1) = k2_funct_2(X0,X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
      | ~ v3_funct_2(X1,X0,X0)
      | ~ v1_funct_2(X1,X0,X0)
      | ~ v1_funct_1(X1) ) ),
    inference(ennf_transformation,[],[f17])).

fof(f42,plain,(
    ! [X0,X1] :
      ( k2_funct_1(X1) = k2_funct_2(X0,X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
      | ~ v3_funct_2(X1,X0,X0)
      | ~ v1_funct_2(X1,X0,X0)
      | ~ v1_funct_1(X1) ) ),
    inference(flattening,[],[f41])).

fof(f77,plain,(
    ! [X0,X1] :
      ( k2_funct_1(X1) = k2_funct_2(X0,X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
      | ~ v3_funct_2(X1,X0,X0)
      | ~ v1_funct_2(X1,X0,X0)
      | ~ v1_funct_1(X1) ) ),
    inference(cnf_transformation,[],[f42])).

fof(f78,plain,(
    v1_funct_1(sK2) ),
    inference(cnf_transformation,[],[f50])).

fof(f79,plain,(
    v1_funct_2(sK2,sK0,sK0) ),
    inference(cnf_transformation,[],[f50])).

fof(f80,plain,(
    v3_funct_2(sK2,sK0,sK0) ),
    inference(cnf_transformation,[],[f50])).

fof(f16,axiom,(
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

fof(f39,plain,(
    ! [X0,X1] :
      ( ( m1_subset_1(k2_funct_2(X0,X1),k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
        & v3_funct_2(k2_funct_2(X0,X1),X0,X0)
        & v1_funct_2(k2_funct_2(X0,X1),X0,X0)
        & v1_funct_1(k2_funct_2(X0,X1)) )
      | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
      | ~ v3_funct_2(X1,X0,X0)
      | ~ v1_funct_2(X1,X0,X0)
      | ~ v1_funct_1(X1) ) ),
    inference(ennf_transformation,[],[f16])).

fof(f40,plain,(
    ! [X0,X1] :
      ( ( m1_subset_1(k2_funct_2(X0,X1),k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
        & v3_funct_2(k2_funct_2(X0,X1),X0,X0)
        & v1_funct_2(k2_funct_2(X0,X1),X0,X0)
        & v1_funct_1(k2_funct_2(X0,X1)) )
      | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
      | ~ v3_funct_2(X1,X0,X0)
      | ~ v1_funct_2(X1,X0,X0)
      | ~ v1_funct_1(X1) ) ),
    inference(flattening,[],[f39])).

fof(f76,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k2_funct_2(X0,X1),k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
      | ~ v3_funct_2(X1,X0,X0)
      | ~ v1_funct_2(X1,X0,X0)
      | ~ v1_funct_1(X1) ) ),
    inference(cnf_transformation,[],[f40])).

fof(f11,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => ( v5_relat_1(X2,X1)
        & v4_relat_1(X2,X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f32,plain,(
    ! [X0,X1,X2] :
      ( ( v5_relat_1(X2,X1)
        & v4_relat_1(X2,X0) )
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f64,plain,(
    ! [X2,X0,X1] :
      ( v4_relat_1(X2,X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f32])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ( v4_relat_1(X1,X0)
      <=> r1_tarski(k1_relat_1(X1),X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f21,plain,(
    ! [X0,X1] :
      ( ( v4_relat_1(X1,X0)
      <=> r1_tarski(k1_relat_1(X1),X0) )
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f47,plain,(
    ! [X0,X1] :
      ( ( ( v4_relat_1(X1,X0)
          | ~ r1_tarski(k1_relat_1(X1),X0) )
        & ( r1_tarski(k1_relat_1(X1),X0)
          | ~ v4_relat_1(X1,X0) ) )
      | ~ v1_relat_1(X1) ) ),
    inference(nnf_transformation,[],[f21])).

fof(f55,plain,(
    ! [X0,X1] :
      ( r1_tarski(k1_relat_1(X1),X0)
      | ~ v4_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f47])).

fof(f4,axiom,(
    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f57,plain,(
    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1)) ),
    inference(cnf_transformation,[],[f4])).

fof(f2,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(X0))
         => v1_relat_1(X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f20,plain,(
    ! [X0] :
      ( ! [X1] :
          ( v1_relat_1(X1)
          | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f54,plain,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f7,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ( r1_tarski(k1_relat_1(X1),X0)
       => k7_relat_1(X1,X0) = X1 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f24,plain,(
    ! [X0,X1] :
      ( k7_relat_1(X1,X0) = X1
      | ~ r1_tarski(k1_relat_1(X1),X0)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f25,plain,(
    ! [X0,X1] :
      ( k7_relat_1(X1,X0) = X1
      | ~ r1_tarski(k1_relat_1(X1),X0)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f24])).

fof(f60,plain,(
    ! [X0,X1] :
      ( k7_relat_1(X1,X0) = X1
      | ~ r1_tarski(k1_relat_1(X1),X0)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f5,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => k2_relat_1(k7_relat_1(X1,X0)) = k9_relat_1(X1,X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f22,plain,(
    ! [X0,X1] :
      ( k2_relat_1(k7_relat_1(X1,X0)) = k9_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f58,plain,(
    ! [X0,X1] :
      ( k2_relat_1(k7_relat_1(X1,X0)) = k9_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f14,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => ( ( v3_funct_2(X2,X0,X1)
          & v1_funct_1(X2) )
       => ( v2_funct_2(X2,X1)
          & v2_funct_1(X2)
          & v1_funct_1(X2) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f35,plain,(
    ! [X0,X1,X2] :
      ( ( v2_funct_2(X2,X1)
        & v2_funct_1(X2)
        & v1_funct_1(X2) )
      | ~ v3_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f36,plain,(
    ! [X0,X1,X2] :
      ( ( v2_funct_2(X2,X1)
        & v2_funct_1(X2)
        & v1_funct_1(X2) )
      | ~ v3_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(flattening,[],[f35])).

fof(f70,plain,(
    ! [X2,X0,X1] :
      ( v2_funct_2(X2,X1)
      | ~ v3_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f36])).

fof(f15,axiom,(
    ! [X0,X1] :
      ( ( v5_relat_1(X1,X0)
        & v1_relat_1(X1) )
     => ( v2_funct_2(X1,X0)
      <=> k2_relat_1(X1) = X0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f37,plain,(
    ! [X0,X1] :
      ( ( v2_funct_2(X1,X0)
      <=> k2_relat_1(X1) = X0 )
      | ~ v5_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f15])).

fof(f38,plain,(
    ! [X0,X1] :
      ( ( v2_funct_2(X1,X0)
      <=> k2_relat_1(X1) = X0 )
      | ~ v5_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f37])).

fof(f48,plain,(
    ! [X0,X1] :
      ( ( ( v2_funct_2(X1,X0)
          | k2_relat_1(X1) != X0 )
        & ( k2_relat_1(X1) = X0
          | ~ v2_funct_2(X1,X0) ) )
      | ~ v5_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(nnf_transformation,[],[f38])).

fof(f71,plain,(
    ! [X0,X1] :
      ( k2_relat_1(X1) = X0
      | ~ v2_funct_2(X1,X0)
      | ~ v5_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f48])).

fof(f65,plain,(
    ! [X2,X0,X1] :
      ( v5_relat_1(X2,X1)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f32])).

fof(f73,plain,(
    ! [X0,X1] :
      ( v1_funct_1(k2_funct_2(X0,X1))
      | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
      | ~ v3_funct_2(X1,X0,X0)
      | ~ v1_funct_2(X1,X0,X0)
      | ~ v1_funct_1(X1) ) ),
    inference(cnf_transformation,[],[f40])).

fof(f75,plain,(
    ! [X0,X1] :
      ( v3_funct_2(k2_funct_2(X0,X1),X0,X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
      | ~ v3_funct_2(X1,X0,X0)
      | ~ v1_funct_2(X1,X0,X0)
      | ~ v1_funct_1(X1) ) ),
    inference(cnf_transformation,[],[f40])).

fof(f69,plain,(
    ! [X2,X0,X1] :
      ( v2_funct_1(X2)
      | ~ v3_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f36])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( X0 = X1
    <=> ( r1_tarski(X1,X0)
        & r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f45,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(nnf_transformation,[],[f1])).

fof(f46,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(flattening,[],[f45])).

fof(f52,plain,(
    ! [X0,X1] :
      ( r1_tarski(X1,X0)
      | X0 != X1 ) ),
    inference(cnf_transformation,[],[f46])).

fof(f84,plain,(
    ! [X1] : r1_tarski(X1,X1) ),
    inference(equality_resolution,[],[f52])).

fof(f10,axiom,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ! [X1] :
          ( ( r1_tarski(X1,k1_relat_1(X0))
            & v2_funct_1(X0) )
         => k9_relat_1(k2_funct_1(X0),k9_relat_1(X0,X1)) = X1 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f30,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k9_relat_1(k2_funct_1(X0),k9_relat_1(X0,X1)) = X1
          | ~ r1_tarski(X1,k1_relat_1(X0))
          | ~ v2_funct_1(X0) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f31,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k9_relat_1(k2_funct_1(X0),k9_relat_1(X0,X1)) = X1
          | ~ r1_tarski(X1,k1_relat_1(X0))
          | ~ v2_funct_1(X0) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f30])).

fof(f63,plain,(
    ! [X0,X1] :
      ( k9_relat_1(k2_funct_1(X0),k9_relat_1(X0,X1)) = X1
      | ~ r1_tarski(X1,k1_relat_1(X0))
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f8,axiom,(
    ! [X0,X1] :
      ( ( v1_funct_1(X1)
        & v1_relat_1(X1) )
     => ( r1_tarski(X0,k2_relat_1(X1))
       => k9_relat_1(X1,k10_relat_1(X1,X0)) = X0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f26,plain,(
    ! [X0,X1] :
      ( k9_relat_1(X1,k10_relat_1(X1,X0)) = X0
      | ~ r1_tarski(X0,k2_relat_1(X1))
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f27,plain,(
    ! [X0,X1] :
      ( k9_relat_1(X1,k10_relat_1(X1,X0)) = X0
      | ~ r1_tarski(X0,k2_relat_1(X1))
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f26])).

fof(f61,plain,(
    ! [X0,X1] :
      ( k9_relat_1(X1,k10_relat_1(X1,X0)) = X0
      | ~ r1_tarski(X0,k2_relat_1(X1))
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f6,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => k1_relat_1(X0) = k10_relat_1(X0,k2_relat_1(X0)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f23,plain,(
    ! [X0] :
      ( k1_relat_1(X0) = k10_relat_1(X0,k2_relat_1(X0))
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f59,plain,(
    ! [X0] :
      ( k1_relat_1(X0) = k10_relat_1(X0,k2_relat_1(X0))
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f9,axiom,(
    ! [X0,X1] :
      ( ( v1_funct_1(X1)
        & v1_relat_1(X1) )
     => ( ( v2_funct_1(X1)
          & r1_tarski(X0,k1_relat_1(X1)) )
       => k10_relat_1(X1,k9_relat_1(X1,X0)) = X0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f28,plain,(
    ! [X0,X1] :
      ( k10_relat_1(X1,k9_relat_1(X1,X0)) = X0
      | ~ v2_funct_1(X1)
      | ~ r1_tarski(X0,k1_relat_1(X1))
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f29,plain,(
    ! [X0,X1] :
      ( k10_relat_1(X1,k9_relat_1(X1,X0)) = X0
      | ~ v2_funct_1(X1)
      | ~ r1_tarski(X0,k1_relat_1(X1))
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f28])).

fof(f62,plain,(
    ! [X0,X1] :
      ( k10_relat_1(X1,k9_relat_1(X1,X0)) = X0
      | ~ v2_funct_1(X1)
      | ~ r1_tarski(X0,k1_relat_1(X1))
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f13,axiom,(
    ! [X0,X1,X2,X3] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k10_relat_1(X2,X3) = k8_relset_1(X0,X1,X2,X3) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f34,plain,(
    ! [X0,X1,X2,X3] :
      ( k10_relat_1(X2,X3) = k8_relset_1(X0,X1,X2,X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f67,plain,(
    ! [X2,X0,X3,X1] :
      ( k10_relat_1(X2,X3) = k8_relset_1(X0,X1,X2,X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f34])).

fof(f83,plain,
    ( k8_relset_1(sK0,sK0,sK2,k7_relset_1(sK0,sK0,sK2,sK1)) != sK1
    | k7_relset_1(sK0,sK0,sK2,k8_relset_1(sK0,sK0,sK2,sK1)) != sK1 ),
    inference(cnf_transformation,[],[f50])).

fof(f12,axiom,(
    ! [X0,X1,X2,X3] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k9_relat_1(X2,X3) = k7_relset_1(X0,X1,X2,X3) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f33,plain,(
    ! [X0,X1,X2,X3] :
      ( k9_relat_1(X2,X3) = k7_relset_1(X0,X1,X2,X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f66,plain,(
    ! [X2,X0,X3,X1] :
      ( k9_relat_1(X2,X3) = k7_relset_1(X0,X1,X2,X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f33])).

cnf(c_28,negated_conjecture,
    ( r1_tarski(sK1,sK0) ),
    inference(cnf_transformation,[],[f82])).

cnf(c_1203,plain,
    ( r1_tarski(sK1,sK0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_28])).

cnf(c_29,negated_conjecture,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) ),
    inference(cnf_transformation,[],[f81])).

cnf(c_1202,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_29])).

cnf(c_26,plain,
    ( ~ v1_funct_2(X0,X1,X1)
    | ~ v3_funct_2(X0,X1,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X1)))
    | ~ v1_funct_1(X0)
    | k2_funct_2(X1,X0) = k2_funct_1(X0) ),
    inference(cnf_transformation,[],[f77])).

cnf(c_1204,plain,
    ( k2_funct_2(X0,X1) = k2_funct_1(X1)
    | v1_funct_2(X1,X0,X0) != iProver_top
    | v3_funct_2(X1,X0,X0) != iProver_top
    | m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) != iProver_top
    | v1_funct_1(X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_26])).

cnf(c_3167,plain,
    ( k2_funct_2(sK0,sK2) = k2_funct_1(sK2)
    | v1_funct_2(sK2,sK0,sK0) != iProver_top
    | v3_funct_2(sK2,sK0,sK0) != iProver_top
    | v1_funct_1(sK2) != iProver_top ),
    inference(superposition,[status(thm)],[c_1202,c_1204])).

cnf(c_32,negated_conjecture,
    ( v1_funct_1(sK2) ),
    inference(cnf_transformation,[],[f78])).

cnf(c_31,negated_conjecture,
    ( v1_funct_2(sK2,sK0,sK0) ),
    inference(cnf_transformation,[],[f79])).

cnf(c_30,negated_conjecture,
    ( v3_funct_2(sK2,sK0,sK0) ),
    inference(cnf_transformation,[],[f80])).

cnf(c_1529,plain,
    ( ~ v1_funct_2(sK2,X0,X0)
    | ~ v3_funct_2(sK2,X0,X0)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
    | ~ v1_funct_1(sK2)
    | k2_funct_2(X0,sK2) = k2_funct_1(sK2) ),
    inference(instantiation,[status(thm)],[c_26])).

cnf(c_1531,plain,
    ( ~ v1_funct_2(sK2,sK0,sK0)
    | ~ v3_funct_2(sK2,sK0,sK0)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
    | ~ v1_funct_1(sK2)
    | k2_funct_2(sK0,sK2) = k2_funct_1(sK2) ),
    inference(instantiation,[status(thm)],[c_1529])).

cnf(c_3346,plain,
    ( k2_funct_2(sK0,sK2) = k2_funct_1(sK2) ),
    inference(global_propositional_subsumption,[status(thm)],[c_3167,c_32,c_31,c_30,c_29,c_1531])).

cnf(c_22,plain,
    ( ~ v1_funct_2(X0,X1,X1)
    | ~ v3_funct_2(X0,X1,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X1)))
    | m1_subset_1(k2_funct_2(X1,X0),k1_zfmisc_1(k2_zfmisc_1(X1,X1)))
    | ~ v1_funct_1(X0) ),
    inference(cnf_transformation,[],[f76])).

cnf(c_1208,plain,
    ( v1_funct_2(X0,X1,X1) != iProver_top
    | v3_funct_2(X0,X1,X1) != iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X1))) != iProver_top
    | m1_subset_1(k2_funct_2(X1,X0),k1_zfmisc_1(k2_zfmisc_1(X1,X1))) = iProver_top
    | v1_funct_1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_22])).

cnf(c_3833,plain,
    ( v1_funct_2(sK2,sK0,sK0) != iProver_top
    | v3_funct_2(sK2,sK0,sK0) != iProver_top
    | m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) = iProver_top
    | m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) != iProver_top
    | v1_funct_1(sK2) != iProver_top ),
    inference(superposition,[status(thm)],[c_3346,c_1208])).

cnf(c_33,plain,
    ( v1_funct_1(sK2) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_32])).

cnf(c_34,plain,
    ( v1_funct_2(sK2,sK0,sK0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_31])).

cnf(c_35,plain,
    ( v3_funct_2(sK2,sK0,sK0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_30])).

cnf(c_36,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_29])).

cnf(c_4571,plain,
    ( m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_3833,c_33,c_34,c_35,c_36])).

cnf(c_14,plain,
    ( v4_relat_1(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) ),
    inference(cnf_transformation,[],[f64])).

cnf(c_5,plain,
    ( ~ v4_relat_1(X0,X1)
    | r1_tarski(k1_relat_1(X0),X1)
    | ~ v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f55])).

cnf(c_352,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | r1_tarski(k1_relat_1(X0),X1)
    | ~ v1_relat_1(X0) ),
    inference(resolution,[status(thm)],[c_14,c_5])).

cnf(c_1198,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) != iProver_top
    | r1_tarski(k1_relat_1(X0),X1) = iProver_top
    | v1_relat_1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_352])).

cnf(c_4581,plain,
    ( r1_tarski(k1_relat_1(k2_funct_1(sK2)),sK0) = iProver_top
    | v1_relat_1(k2_funct_1(sK2)) != iProver_top ),
    inference(superposition,[status(thm)],[c_4571,c_1198])).

cnf(c_6,plain,
    ( v1_relat_1(k2_zfmisc_1(X0,X1)) ),
    inference(cnf_transformation,[],[f57])).

cnf(c_96,plain,
    ( v1_relat_1(k2_zfmisc_1(X0,X1)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_6])).

cnf(c_98,plain,
    ( v1_relat_1(k2_zfmisc_1(sK0,sK0)) = iProver_top ),
    inference(instantiation,[status(thm)],[c_96])).

cnf(c_3,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | ~ v1_relat_1(X1)
    | v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f54])).

cnf(c_1219,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(X1)) != iProver_top
    | v1_relat_1(X1) != iProver_top
    | v1_relat_1(X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3])).

cnf(c_4576,plain,
    ( v1_relat_1(k2_zfmisc_1(sK0,sK0)) != iProver_top
    | v1_relat_1(k2_funct_1(sK2)) = iProver_top ),
    inference(superposition,[status(thm)],[c_4571,c_1219])).

cnf(c_5012,plain,
    ( r1_tarski(k1_relat_1(k2_funct_1(sK2)),sK0) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_4581,c_98,c_4576])).

cnf(c_9,plain,
    ( ~ r1_tarski(k1_relat_1(X0),X1)
    | ~ v1_relat_1(X0)
    | k7_relat_1(X0,X1) = X0 ),
    inference(cnf_transformation,[],[f60])).

cnf(c_1215,plain,
    ( k7_relat_1(X0,X1) = X0
    | r1_tarski(k1_relat_1(X0),X1) != iProver_top
    | v1_relat_1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_9])).

cnf(c_5018,plain,
    ( k7_relat_1(k2_funct_1(sK2),sK0) = k2_funct_1(sK2)
    | v1_relat_1(k2_funct_1(sK2)) != iProver_top ),
    inference(superposition,[status(thm)],[c_5012,c_1215])).

cnf(c_5446,plain,
    ( k7_relat_1(k2_funct_1(sK2),sK0) = k2_funct_1(sK2) ),
    inference(global_propositional_subsumption,[status(thm)],[c_5018,c_98,c_4576])).

cnf(c_4884,plain,
    ( v1_relat_1(k2_funct_1(sK2)) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_4576,c_98])).

cnf(c_7,plain,
    ( ~ v1_relat_1(X0)
    | k2_relat_1(k7_relat_1(X0,X1)) = k9_relat_1(X0,X1) ),
    inference(cnf_transformation,[],[f58])).

cnf(c_1217,plain,
    ( k2_relat_1(k7_relat_1(X0,X1)) = k9_relat_1(X0,X1)
    | v1_relat_1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_7])).

cnf(c_4890,plain,
    ( k2_relat_1(k7_relat_1(k2_funct_1(sK2),X0)) = k9_relat_1(k2_funct_1(sK2),X0) ),
    inference(superposition,[status(thm)],[c_4884,c_1217])).

cnf(c_5449,plain,
    ( k9_relat_1(k2_funct_1(sK2),sK0) = k2_relat_1(k2_funct_1(sK2)) ),
    inference(superposition,[status(thm)],[c_5446,c_4890])).

cnf(c_17,plain,
    ( ~ v3_funct_2(X0,X1,X2)
    | v2_funct_2(X0,X2)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ v1_funct_1(X0) ),
    inference(cnf_transformation,[],[f70])).

cnf(c_21,plain,
    ( ~ v2_funct_2(X0,X1)
    | ~ v5_relat_1(X0,X1)
    | ~ v1_relat_1(X0)
    | k2_relat_1(X0) = X1 ),
    inference(cnf_transformation,[],[f71])).

cnf(c_410,plain,
    ( ~ v3_funct_2(X0,X1,X2)
    | ~ v5_relat_1(X3,X4)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ v1_funct_1(X0)
    | ~ v1_relat_1(X3)
    | X3 != X0
    | X4 != X2
    | k2_relat_1(X3) = X4 ),
    inference(resolution_lifted,[status(thm)],[c_17,c_21])).

cnf(c_411,plain,
    ( ~ v3_funct_2(X0,X1,X2)
    | ~ v5_relat_1(X0,X2)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ v1_funct_1(X0)
    | ~ v1_relat_1(X0)
    | k2_relat_1(X0) = X2 ),
    inference(unflattening,[status(thm)],[c_410])).

cnf(c_13,plain,
    ( v5_relat_1(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) ),
    inference(cnf_transformation,[],[f65])).

cnf(c_427,plain,
    ( ~ v3_funct_2(X0,X1,X2)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ v1_funct_1(X0)
    | ~ v1_relat_1(X0)
    | k2_relat_1(X0) = X2 ),
    inference(forward_subsumption_resolution,[status(thm)],[c_411,c_13])).

cnf(c_1197,plain,
    ( k2_relat_1(X0) = X1
    | v3_funct_2(X0,X2,X1) != iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) != iProver_top
    | v1_funct_1(X0) != iProver_top
    | v1_relat_1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_427])).

cnf(c_4579,plain,
    ( k2_relat_1(k2_funct_1(sK2)) = sK0
    | v3_funct_2(k2_funct_1(sK2),sK0,sK0) != iProver_top
    | v1_funct_1(k2_funct_1(sK2)) != iProver_top
    | v1_relat_1(k2_funct_1(sK2)) != iProver_top ),
    inference(superposition,[status(thm)],[c_4571,c_1197])).

cnf(c_25,plain,
    ( ~ v1_funct_2(X0,X1,X1)
    | ~ v3_funct_2(X0,X1,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X1)))
    | ~ v1_funct_1(X0)
    | v1_funct_1(k2_funct_2(X1,X0)) ),
    inference(cnf_transformation,[],[f73])).

cnf(c_1205,plain,
    ( v1_funct_2(X0,X1,X1) != iProver_top
    | v3_funct_2(X0,X1,X1) != iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X1))) != iProver_top
    | v1_funct_1(X0) != iProver_top
    | v1_funct_1(k2_funct_2(X1,X0)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_25])).

cnf(c_3293,plain,
    ( v1_funct_2(sK2,sK0,sK0) != iProver_top
    | v3_funct_2(sK2,sK0,sK0) != iProver_top
    | v1_funct_1(k2_funct_2(sK0,sK2)) = iProver_top
    | v1_funct_1(sK2) != iProver_top ),
    inference(superposition,[status(thm)],[c_1202,c_1205])).

cnf(c_1514,plain,
    ( ~ v1_funct_2(sK2,X0,X0)
    | ~ v3_funct_2(sK2,X0,X0)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
    | v1_funct_1(k2_funct_2(X0,sK2))
    | ~ v1_funct_1(sK2) ),
    inference(instantiation,[status(thm)],[c_25])).

cnf(c_1515,plain,
    ( v1_funct_2(sK2,X0,X0) != iProver_top
    | v3_funct_2(sK2,X0,X0) != iProver_top
    | m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) != iProver_top
    | v1_funct_1(k2_funct_2(X0,sK2)) = iProver_top
    | v1_funct_1(sK2) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1514])).

cnf(c_1517,plain,
    ( v1_funct_2(sK2,sK0,sK0) != iProver_top
    | v3_funct_2(sK2,sK0,sK0) != iProver_top
    | m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) != iProver_top
    | v1_funct_1(k2_funct_2(sK0,sK2)) = iProver_top
    | v1_funct_1(sK2) != iProver_top ),
    inference(instantiation,[status(thm)],[c_1515])).

cnf(c_3443,plain,
    ( v1_funct_1(k2_funct_2(sK0,sK2)) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_3293,c_33,c_34,c_35,c_36,c_1517])).

cnf(c_3447,plain,
    ( v1_funct_1(k2_funct_1(sK2)) = iProver_top ),
    inference(light_normalisation,[status(thm)],[c_3443,c_3346])).

cnf(c_23,plain,
    ( ~ v1_funct_2(X0,X1,X1)
    | ~ v3_funct_2(X0,X1,X1)
    | v3_funct_2(k2_funct_2(X1,X0),X1,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X1)))
    | ~ v1_funct_1(X0) ),
    inference(cnf_transformation,[],[f75])).

cnf(c_1207,plain,
    ( v1_funct_2(X0,X1,X1) != iProver_top
    | v3_funct_2(X0,X1,X1) != iProver_top
    | v3_funct_2(k2_funct_2(X1,X0),X1,X1) = iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X1))) != iProver_top
    | v1_funct_1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_23])).

cnf(c_3746,plain,
    ( v1_funct_2(sK2,sK0,sK0) != iProver_top
    | v3_funct_2(k2_funct_2(sK0,sK2),sK0,sK0) = iProver_top
    | v3_funct_2(sK2,sK0,sK0) != iProver_top
    | v1_funct_1(sK2) != iProver_top ),
    inference(superposition,[status(thm)],[c_1202,c_1207])).

cnf(c_3747,plain,
    ( v1_funct_2(sK2,sK0,sK0) != iProver_top
    | v3_funct_2(k2_funct_1(sK2),sK0,sK0) = iProver_top
    | v3_funct_2(sK2,sK0,sK0) != iProver_top
    | v1_funct_1(sK2) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_3746,c_3346])).

cnf(c_5806,plain,
    ( k2_relat_1(k2_funct_1(sK2)) = sK0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_4579,c_33,c_34,c_35,c_98,c_3447,c_3747,c_4576])).

cnf(c_18,plain,
    ( ~ v3_funct_2(X0,X1,X2)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | v2_funct_1(X0)
    | ~ v1_funct_1(X0) ),
    inference(cnf_transformation,[],[f69])).

cnf(c_1209,plain,
    ( v3_funct_2(X0,X1,X2) != iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) != iProver_top
    | v2_funct_1(X0) = iProver_top
    | v1_funct_1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_18])).

cnf(c_2611,plain,
    ( v3_funct_2(sK2,sK0,sK0) != iProver_top
    | v2_funct_1(sK2) = iProver_top
    | v1_funct_1(sK2) != iProver_top ),
    inference(superposition,[status(thm)],[c_1202,c_1209])).

cnf(c_1480,plain,
    ( ~ v3_funct_2(sK2,X0,X1)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
    | v2_funct_1(sK2)
    | ~ v1_funct_1(sK2) ),
    inference(instantiation,[status(thm)],[c_18])).

cnf(c_1481,plain,
    ( v3_funct_2(sK2,X0,X1) != iProver_top
    | m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top
    | v2_funct_1(sK2) = iProver_top
    | v1_funct_1(sK2) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1480])).

cnf(c_1483,plain,
    ( v3_funct_2(sK2,sK0,sK0) != iProver_top
    | m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) != iProver_top
    | v2_funct_1(sK2) = iProver_top
    | v1_funct_1(sK2) != iProver_top ),
    inference(instantiation,[status(thm)],[c_1481])).

cnf(c_2754,plain,
    ( v2_funct_1(sK2) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_2611,c_33,c_35,c_36,c_1483])).

cnf(c_1,plain,
    ( r1_tarski(X0,X0) ),
    inference(cnf_transformation,[],[f84])).

cnf(c_1220,plain,
    ( r1_tarski(X0,X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1])).

cnf(c_12,plain,
    ( ~ r1_tarski(X0,k1_relat_1(X1))
    | ~ v2_funct_1(X1)
    | ~ v1_funct_1(X1)
    | ~ v1_relat_1(X1)
    | k9_relat_1(k2_funct_1(X1),k9_relat_1(X1,X0)) = X0 ),
    inference(cnf_transformation,[],[f63])).

cnf(c_1212,plain,
    ( k9_relat_1(k2_funct_1(X0),k9_relat_1(X0,X1)) = X1
    | r1_tarski(X1,k1_relat_1(X0)) != iProver_top
    | v2_funct_1(X0) != iProver_top
    | v1_funct_1(X0) != iProver_top
    | v1_relat_1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_12])).

cnf(c_3283,plain,
    ( k9_relat_1(k2_funct_1(X0),k9_relat_1(X0,k1_relat_1(X0))) = k1_relat_1(X0)
    | v2_funct_1(X0) != iProver_top
    | v1_funct_1(X0) != iProver_top
    | v1_relat_1(X0) != iProver_top ),
    inference(superposition,[status(thm)],[c_1220,c_1212])).

cnf(c_6594,plain,
    ( k9_relat_1(k2_funct_1(sK2),k9_relat_1(sK2,k1_relat_1(sK2))) = k1_relat_1(sK2)
    | v1_funct_1(sK2) != iProver_top
    | v1_relat_1(sK2) != iProver_top ),
    inference(superposition,[status(thm)],[c_2754,c_3283])).

cnf(c_1597,plain,
    ( k2_relat_1(sK2) = sK0
    | v3_funct_2(sK2,sK0,sK0) != iProver_top
    | v1_funct_1(sK2) != iProver_top
    | v1_relat_1(sK2) != iProver_top ),
    inference(superposition,[status(thm)],[c_1202,c_1197])).

cnf(c_97,plain,
    ( v1_relat_1(k2_zfmisc_1(sK0,sK0)) ),
    inference(instantiation,[status(thm)],[c_6])).

cnf(c_1598,plain,
    ( ~ v3_funct_2(sK2,sK0,sK0)
    | ~ v1_funct_1(sK2)
    | ~ v1_relat_1(sK2)
    | k2_relat_1(sK2) = sK0 ),
    inference(predicate_to_equality_rev,[status(thm)],[c_1597])).

cnf(c_1432,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | v1_relat_1(X0)
    | ~ v1_relat_1(k2_zfmisc_1(X1,X2)) ),
    inference(instantiation,[status(thm)],[c_3])).

cnf(c_1612,plain,
    ( ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
    | ~ v1_relat_1(k2_zfmisc_1(sK0,sK0))
    | v1_relat_1(sK2) ),
    inference(instantiation,[status(thm)],[c_1432])).

cnf(c_1995,plain,
    ( k2_relat_1(sK2) = sK0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_1597,c_32,c_30,c_29,c_97,c_1598,c_1612])).

cnf(c_10,plain,
    ( ~ r1_tarski(X0,k2_relat_1(X1))
    | ~ v1_funct_1(X1)
    | ~ v1_relat_1(X1)
    | k9_relat_1(X1,k10_relat_1(X1,X0)) = X0 ),
    inference(cnf_transformation,[],[f61])).

cnf(c_1214,plain,
    ( k9_relat_1(X0,k10_relat_1(X0,X1)) = X1
    | r1_tarski(X1,k2_relat_1(X0)) != iProver_top
    | v1_funct_1(X0) != iProver_top
    | v1_relat_1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_10])).

cnf(c_2562,plain,
    ( k9_relat_1(sK2,k10_relat_1(sK2,X0)) = X0
    | r1_tarski(X0,sK0) != iProver_top
    | v1_funct_1(sK2) != iProver_top
    | v1_relat_1(sK2) != iProver_top ),
    inference(superposition,[status(thm)],[c_1995,c_1214])).

cnf(c_1613,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) != iProver_top
    | v1_relat_1(k2_zfmisc_1(sK0,sK0)) != iProver_top
    | v1_relat_1(sK2) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1612])).

cnf(c_3588,plain,
    ( k9_relat_1(sK2,k10_relat_1(sK2,X0)) = X0
    | r1_tarski(X0,sK0) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_2562,c_33,c_36,c_98,c_1613])).

cnf(c_3596,plain,
    ( k9_relat_1(sK2,k10_relat_1(sK2,sK0)) = sK0 ),
    inference(superposition,[status(thm)],[c_1220,c_3588])).

cnf(c_1881,plain,
    ( v1_relat_1(k2_zfmisc_1(sK0,sK0)) != iProver_top
    | v1_relat_1(sK2) = iProver_top ),
    inference(superposition,[status(thm)],[c_1202,c_1219])).

cnf(c_1982,plain,
    ( v1_relat_1(sK2) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_1881,c_36,c_98,c_1613])).

cnf(c_8,plain,
    ( ~ v1_relat_1(X0)
    | k10_relat_1(X0,k2_relat_1(X0)) = k1_relat_1(X0) ),
    inference(cnf_transformation,[],[f59])).

cnf(c_1216,plain,
    ( k10_relat_1(X0,k2_relat_1(X0)) = k1_relat_1(X0)
    | v1_relat_1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_8])).

cnf(c_1988,plain,
    ( k10_relat_1(sK2,k2_relat_1(sK2)) = k1_relat_1(sK2) ),
    inference(superposition,[status(thm)],[c_1982,c_1216])).

cnf(c_2062,plain,
    ( k10_relat_1(sK2,sK0) = k1_relat_1(sK2) ),
    inference(light_normalisation,[status(thm)],[c_1988,c_1995])).

cnf(c_3604,plain,
    ( k9_relat_1(sK2,k1_relat_1(sK2)) = sK0 ),
    inference(light_normalisation,[status(thm)],[c_3596,c_2062])).

cnf(c_6605,plain,
    ( k9_relat_1(k2_funct_1(sK2),sK0) = k1_relat_1(sK2)
    | v1_funct_1(sK2) != iProver_top
    | v1_relat_1(sK2) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_6594,c_3604])).

cnf(c_6777,plain,
    ( k9_relat_1(k2_funct_1(sK2),sK0) = k1_relat_1(sK2) ),
    inference(global_propositional_subsumption,[status(thm)],[c_6605,c_33,c_36,c_98,c_1613])).

cnf(c_7986,plain,
    ( k1_relat_1(sK2) = sK0 ),
    inference(light_normalisation,[status(thm)],[c_5449,c_5806,c_6777])).

cnf(c_11,plain,
    ( ~ r1_tarski(X0,k1_relat_1(X1))
    | ~ v2_funct_1(X1)
    | ~ v1_funct_1(X1)
    | ~ v1_relat_1(X1)
    | k10_relat_1(X1,k9_relat_1(X1,X0)) = X0 ),
    inference(cnf_transformation,[],[f62])).

cnf(c_1213,plain,
    ( k10_relat_1(X0,k9_relat_1(X0,X1)) = X1
    | r1_tarski(X1,k1_relat_1(X0)) != iProver_top
    | v2_funct_1(X0) != iProver_top
    | v1_funct_1(X0) != iProver_top
    | v1_relat_1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_11])).

cnf(c_8014,plain,
    ( k10_relat_1(sK2,k9_relat_1(sK2,X0)) = X0
    | r1_tarski(X0,sK0) != iProver_top
    | v2_funct_1(sK2) != iProver_top
    | v1_funct_1(sK2) != iProver_top
    | v1_relat_1(sK2) != iProver_top ),
    inference(superposition,[status(thm)],[c_7986,c_1213])).

cnf(c_9394,plain,
    ( r1_tarski(X0,sK0) != iProver_top
    | k10_relat_1(sK2,k9_relat_1(sK2,X0)) = X0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_8014,c_33,c_35,c_36,c_98,c_1483,c_1613])).

cnf(c_9395,plain,
    ( k10_relat_1(sK2,k9_relat_1(sK2,X0)) = X0
    | r1_tarski(X0,sK0) != iProver_top ),
    inference(renaming,[status(thm)],[c_9394])).

cnf(c_9403,plain,
    ( k10_relat_1(sK2,k9_relat_1(sK2,sK1)) = sK1 ),
    inference(superposition,[status(thm)],[c_1203,c_9395])).

cnf(c_3597,plain,
    ( k9_relat_1(sK2,k10_relat_1(sK2,sK1)) = sK1 ),
    inference(superposition,[status(thm)],[c_1203,c_3588])).

cnf(c_16,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k8_relset_1(X1,X2,X0,X3) = k10_relat_1(X0,X3) ),
    inference(cnf_transformation,[],[f67])).

cnf(c_1210,plain,
    ( k8_relset_1(X0,X1,X2,X3) = k10_relat_1(X2,X3)
    | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_16])).

cnf(c_2341,plain,
    ( k8_relset_1(sK0,sK0,sK2,X0) = k10_relat_1(sK2,X0) ),
    inference(superposition,[status(thm)],[c_1202,c_1210])).

cnf(c_27,negated_conjecture,
    ( k8_relset_1(sK0,sK0,sK2,k7_relset_1(sK0,sK0,sK2,sK1)) != sK1
    | k7_relset_1(sK0,sK0,sK2,k8_relset_1(sK0,sK0,sK2,sK1)) != sK1 ),
    inference(cnf_transformation,[],[f83])).

cnf(c_2661,plain,
    ( k7_relset_1(sK0,sK0,sK2,k8_relset_1(sK0,sK0,sK2,sK1)) != sK1
    | k10_relat_1(sK2,k7_relset_1(sK0,sK0,sK2,sK1)) != sK1 ),
    inference(demodulation,[status(thm)],[c_2341,c_27])).

cnf(c_2662,plain,
    ( k7_relset_1(sK0,sK0,sK2,k10_relat_1(sK2,sK1)) != sK1
    | k10_relat_1(sK2,k7_relset_1(sK0,sK0,sK2,sK1)) != sK1 ),
    inference(demodulation,[status(thm)],[c_2661,c_2341])).

cnf(c_15,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k7_relset_1(X1,X2,X0,X3) = k9_relat_1(X0,X3) ),
    inference(cnf_transformation,[],[f66])).

cnf(c_1211,plain,
    ( k7_relset_1(X0,X1,X2,X3) = k9_relat_1(X2,X3)
    | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_15])).

cnf(c_2437,plain,
    ( k7_relset_1(sK0,sK0,sK2,X0) = k9_relat_1(sK2,X0) ),
    inference(superposition,[status(thm)],[c_1202,c_1211])).

cnf(c_2847,plain,
    ( k10_relat_1(sK2,k9_relat_1(sK2,sK1)) != sK1
    | k9_relat_1(sK2,k10_relat_1(sK2,sK1)) != sK1 ),
    inference(demodulation,[status(thm)],[c_2662,c_2437])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_9403,c_3597,c_2847])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.13/0.13  % Command    : iproveropt_run.sh %d %s
% 0.13/0.34  % Computer   : n023.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 11:16:36 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running in FOF mode
% 3.32/0.99  % SZS status Started for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.32/0.99  
% 3.32/0.99  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 3.32/0.99  
% 3.32/0.99  ------  iProver source info
% 3.32/0.99  
% 3.32/0.99  git: date: 2020-06-30 10:37:57 +0100
% 3.32/0.99  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 3.32/0.99  git: non_committed_changes: false
% 3.32/0.99  git: last_make_outside_of_git: false
% 3.32/0.99  
% 3.32/0.99  ------ 
% 3.32/0.99  
% 3.32/0.99  ------ Input Options
% 3.32/0.99  
% 3.32/0.99  --out_options                           all
% 3.32/0.99  --tptp_safe_out                         true
% 3.32/0.99  --problem_path                          ""
% 3.32/0.99  --include_path                          ""
% 3.32/0.99  --clausifier                            res/vclausify_rel
% 3.32/0.99  --clausifier_options                    --mode clausify
% 3.32/0.99  --stdin                                 false
% 3.32/0.99  --stats_out                             all
% 3.32/0.99  
% 3.32/0.99  ------ General Options
% 3.32/0.99  
% 3.32/0.99  --fof                                   false
% 3.32/0.99  --time_out_real                         305.
% 3.32/0.99  --time_out_virtual                      -1.
% 3.32/0.99  --symbol_type_check                     false
% 3.32/0.99  --clausify_out                          false
% 3.32/0.99  --sig_cnt_out                           false
% 3.32/0.99  --trig_cnt_out                          false
% 3.32/0.99  --trig_cnt_out_tolerance                1.
% 3.32/0.99  --trig_cnt_out_sk_spl                   false
% 3.32/0.99  --abstr_cl_out                          false
% 3.32/0.99  
% 3.32/0.99  ------ Global Options
% 3.32/0.99  
% 3.32/0.99  --schedule                              default
% 3.32/0.99  --add_important_lit                     false
% 3.32/0.99  --prop_solver_per_cl                    1000
% 3.32/0.99  --min_unsat_core                        false
% 3.32/0.99  --soft_assumptions                      false
% 3.32/0.99  --soft_lemma_size                       3
% 3.32/0.99  --prop_impl_unit_size                   0
% 3.32/0.99  --prop_impl_unit                        []
% 3.32/0.99  --share_sel_clauses                     true
% 3.32/0.99  --reset_solvers                         false
% 3.32/0.99  --bc_imp_inh                            [conj_cone]
% 3.32/0.99  --conj_cone_tolerance                   3.
% 3.32/0.99  --extra_neg_conj                        none
% 3.32/0.99  --large_theory_mode                     true
% 3.32/0.99  --prolific_symb_bound                   200
% 3.32/0.99  --lt_threshold                          2000
% 3.32/0.99  --clause_weak_htbl                      true
% 3.32/0.99  --gc_record_bc_elim                     false
% 3.32/0.99  
% 3.32/0.99  ------ Preprocessing Options
% 3.32/0.99  
% 3.32/0.99  --preprocessing_flag                    true
% 3.32/0.99  --time_out_prep_mult                    0.1
% 3.32/0.99  --splitting_mode                        input
% 3.32/0.99  --splitting_grd                         true
% 3.32/0.99  --splitting_cvd                         false
% 3.32/0.99  --splitting_cvd_svl                     false
% 3.32/0.99  --splitting_nvd                         32
% 3.32/0.99  --sub_typing                            true
% 3.32/0.99  --prep_gs_sim                           true
% 3.32/0.99  --prep_unflatten                        true
% 3.32/0.99  --prep_res_sim                          true
% 3.32/0.99  --prep_upred                            true
% 3.32/0.99  --prep_sem_filter                       exhaustive
% 3.32/0.99  --prep_sem_filter_out                   false
% 3.32/0.99  --pred_elim                             true
% 3.32/0.99  --res_sim_input                         true
% 3.32/0.99  --eq_ax_congr_red                       true
% 3.32/0.99  --pure_diseq_elim                       true
% 3.32/0.99  --brand_transform                       false
% 3.32/0.99  --non_eq_to_eq                          false
% 3.32/0.99  --prep_def_merge                        true
% 3.32/0.99  --prep_def_merge_prop_impl              false
% 3.32/0.99  --prep_def_merge_mbd                    true
% 3.32/0.99  --prep_def_merge_tr_red                 false
% 3.32/0.99  --prep_def_merge_tr_cl                  false
% 3.32/0.99  --smt_preprocessing                     true
% 3.32/0.99  --smt_ac_axioms                         fast
% 3.32/0.99  --preprocessed_out                      false
% 3.32/0.99  --preprocessed_stats                    false
% 3.32/0.99  
% 3.32/0.99  ------ Abstraction refinement Options
% 3.32/0.99  
% 3.32/0.99  --abstr_ref                             []
% 3.32/0.99  --abstr_ref_prep                        false
% 3.32/0.99  --abstr_ref_until_sat                   false
% 3.32/0.99  --abstr_ref_sig_restrict                funpre
% 3.32/0.99  --abstr_ref_af_restrict_to_split_sk     false
% 3.32/0.99  --abstr_ref_under                       []
% 3.32/0.99  
% 3.32/0.99  ------ SAT Options
% 3.32/0.99  
% 3.32/0.99  --sat_mode                              false
% 3.32/0.99  --sat_fm_restart_options                ""
% 3.32/0.99  --sat_gr_def                            false
% 3.32/0.99  --sat_epr_types                         true
% 3.32/0.99  --sat_non_cyclic_types                  false
% 3.32/0.99  --sat_finite_models                     false
% 3.32/0.99  --sat_fm_lemmas                         false
% 3.32/0.99  --sat_fm_prep                           false
% 3.32/0.99  --sat_fm_uc_incr                        true
% 3.32/0.99  --sat_out_model                         small
% 3.32/0.99  --sat_out_clauses                       false
% 3.32/0.99  
% 3.32/0.99  ------ QBF Options
% 3.32/0.99  
% 3.32/0.99  --qbf_mode                              false
% 3.32/0.99  --qbf_elim_univ                         false
% 3.32/0.99  --qbf_dom_inst                          none
% 3.32/0.99  --qbf_dom_pre_inst                      false
% 3.32/0.99  --qbf_sk_in                             false
% 3.32/0.99  --qbf_pred_elim                         true
% 3.32/0.99  --qbf_split                             512
% 3.32/0.99  
% 3.32/0.99  ------ BMC1 Options
% 3.32/0.99  
% 3.32/0.99  --bmc1_incremental                      false
% 3.32/0.99  --bmc1_axioms                           reachable_all
% 3.32/0.99  --bmc1_min_bound                        0
% 3.32/0.99  --bmc1_max_bound                        -1
% 3.32/0.99  --bmc1_max_bound_default                -1
% 3.32/0.99  --bmc1_symbol_reachability              true
% 3.32/0.99  --bmc1_property_lemmas                  false
% 3.32/0.99  --bmc1_k_induction                      false
% 3.32/0.99  --bmc1_non_equiv_states                 false
% 3.32/0.99  --bmc1_deadlock                         false
% 3.32/0.99  --bmc1_ucm                              false
% 3.32/0.99  --bmc1_add_unsat_core                   none
% 3.32/0.99  --bmc1_unsat_core_children              false
% 3.32/0.99  --bmc1_unsat_core_extrapolate_axioms    false
% 3.32/0.99  --bmc1_out_stat                         full
% 3.32/0.99  --bmc1_ground_init                      false
% 3.32/0.99  --bmc1_pre_inst_next_state              false
% 3.32/0.99  --bmc1_pre_inst_state                   false
% 3.32/0.99  --bmc1_pre_inst_reach_state             false
% 3.32/0.99  --bmc1_out_unsat_core                   false
% 3.32/0.99  --bmc1_aig_witness_out                  false
% 3.32/0.99  --bmc1_verbose                          false
% 3.32/0.99  --bmc1_dump_clauses_tptp                false
% 3.32/0.99  --bmc1_dump_unsat_core_tptp             false
% 3.32/0.99  --bmc1_dump_file                        -
% 3.32/0.99  --bmc1_ucm_expand_uc_limit              128
% 3.32/0.99  --bmc1_ucm_n_expand_iterations          6
% 3.32/0.99  --bmc1_ucm_extend_mode                  1
% 3.32/0.99  --bmc1_ucm_init_mode                    2
% 3.32/0.99  --bmc1_ucm_cone_mode                    none
% 3.32/0.99  --bmc1_ucm_reduced_relation_type        0
% 3.32/0.99  --bmc1_ucm_relax_model                  4
% 3.32/0.99  --bmc1_ucm_full_tr_after_sat            true
% 3.32/0.99  --bmc1_ucm_expand_neg_assumptions       false
% 3.32/0.99  --bmc1_ucm_layered_model                none
% 3.32/0.99  --bmc1_ucm_max_lemma_size               10
% 3.32/0.99  
% 3.32/0.99  ------ AIG Options
% 3.32/0.99  
% 3.32/0.99  --aig_mode                              false
% 3.32/0.99  
% 3.32/0.99  ------ Instantiation Options
% 3.32/0.99  
% 3.32/0.99  --instantiation_flag                    true
% 3.32/0.99  --inst_sos_flag                         false
% 3.32/0.99  --inst_sos_phase                        true
% 3.32/0.99  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 3.32/0.99  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 3.32/0.99  --inst_lit_sel_side                     num_symb
% 3.32/0.99  --inst_solver_per_active                1400
% 3.32/0.99  --inst_solver_calls_frac                1.
% 3.32/0.99  --inst_passive_queue_type               priority_queues
% 3.32/0.99  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 3.32/0.99  --inst_passive_queues_freq              [25;2]
% 3.32/0.99  --inst_dismatching                      true
% 3.32/0.99  --inst_eager_unprocessed_to_passive     true
% 3.32/0.99  --inst_prop_sim_given                   true
% 3.32/0.99  --inst_prop_sim_new                     false
% 3.32/0.99  --inst_subs_new                         false
% 3.32/0.99  --inst_eq_res_simp                      false
% 3.32/0.99  --inst_subs_given                       false
% 3.32/0.99  --inst_orphan_elimination               true
% 3.32/0.99  --inst_learning_loop_flag               true
% 3.32/0.99  --inst_learning_start                   3000
% 3.32/0.99  --inst_learning_factor                  2
% 3.32/0.99  --inst_start_prop_sim_after_learn       3
% 3.32/0.99  --inst_sel_renew                        solver
% 3.32/0.99  --inst_lit_activity_flag                true
% 3.32/0.99  --inst_restr_to_given                   false
% 3.32/0.99  --inst_activity_threshold               500
% 3.32/0.99  --inst_out_proof                        true
% 3.32/0.99  
% 3.32/0.99  ------ Resolution Options
% 3.32/0.99  
% 3.32/0.99  --resolution_flag                       true
% 3.32/0.99  --res_lit_sel                           adaptive
% 3.32/0.99  --res_lit_sel_side                      none
% 3.32/0.99  --res_ordering                          kbo
% 3.32/0.99  --res_to_prop_solver                    active
% 3.32/0.99  --res_prop_simpl_new                    false
% 3.32/0.99  --res_prop_simpl_given                  true
% 3.32/0.99  --res_passive_queue_type                priority_queues
% 3.32/0.99  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 3.32/0.99  --res_passive_queues_freq               [15;5]
% 3.32/0.99  --res_forward_subs                      full
% 3.32/0.99  --res_backward_subs                     full
% 3.32/0.99  --res_forward_subs_resolution           true
% 3.32/0.99  --res_backward_subs_resolution          true
% 3.32/0.99  --res_orphan_elimination                true
% 3.32/0.99  --res_time_limit                        2.
% 3.32/0.99  --res_out_proof                         true
% 3.32/0.99  
% 3.32/0.99  ------ Superposition Options
% 3.32/0.99  
% 3.32/0.99  --superposition_flag                    true
% 3.32/0.99  --sup_passive_queue_type                priority_queues
% 3.32/0.99  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 3.32/0.99  --sup_passive_queues_freq               [8;1;4]
% 3.32/0.99  --demod_completeness_check              fast
% 3.32/0.99  --demod_use_ground                      true
% 3.32/0.99  --sup_to_prop_solver                    passive
% 3.32/0.99  --sup_prop_simpl_new                    true
% 3.32/0.99  --sup_prop_simpl_given                  true
% 3.32/0.99  --sup_fun_splitting                     false
% 3.32/0.99  --sup_smt_interval                      50000
% 3.32/0.99  
% 3.32/0.99  ------ Superposition Simplification Setup
% 3.32/0.99  
% 3.32/0.99  --sup_indices_passive                   []
% 3.32/0.99  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.32/0.99  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.32/0.99  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.32/0.99  --sup_full_triv                         [TrivRules;PropSubs]
% 3.32/0.99  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.32/0.99  --sup_full_bw                           [BwDemod]
% 3.32/0.99  --sup_immed_triv                        [TrivRules]
% 3.32/0.99  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 3.32/0.99  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.32/0.99  --sup_immed_bw_main                     []
% 3.32/0.99  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 3.32/0.99  --sup_input_triv                        [Unflattening;TrivRules]
% 3.32/0.99  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.32/0.99  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 3.32/0.99  
% 3.32/0.99  ------ Combination Options
% 3.32/0.99  
% 3.32/0.99  --comb_res_mult                         3
% 3.32/0.99  --comb_sup_mult                         2
% 3.32/0.99  --comb_inst_mult                        10
% 3.32/0.99  
% 3.32/0.99  ------ Debug Options
% 3.32/0.99  
% 3.32/0.99  --dbg_backtrace                         false
% 3.32/0.99  --dbg_dump_prop_clauses                 false
% 3.32/0.99  --dbg_dump_prop_clauses_file            -
% 3.32/0.99  --dbg_out_stat                          false
% 3.32/0.99  ------ Parsing...
% 3.32/0.99  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 3.32/0.99  
% 3.32/0.99  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe:1:0s pe:2:0s pe_e  sf_s  rm: 3 0s  sf_e  pe_s  pe_e 
% 3.32/0.99  
% 3.32/0.99  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 3.32/0.99  
% 3.32/0.99  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 3.32/0.99  ------ Proving...
% 3.32/0.99  ------ Problem Properties 
% 3.32/0.99  
% 3.32/0.99  
% 3.32/0.99  clauses                                 26
% 3.32/0.99  conjectures                             6
% 3.32/0.99  EPR                                     6
% 3.32/0.99  Horn                                    26
% 3.32/0.99  unary                                   7
% 3.32/0.99  binary                                  5
% 3.32/0.99  lits                                    77
% 3.32/0.99  lits eq                                 13
% 3.32/0.99  fd_pure                                 0
% 3.32/0.99  fd_pseudo                               0
% 3.32/0.99  fd_cond                                 0
% 3.32/0.99  fd_pseudo_cond                          2
% 3.32/0.99  AC symbols                              0
% 3.32/0.99  
% 3.32/0.99  ------ Schedule dynamic 5 is on 
% 3.32/0.99  
% 3.32/0.99  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" Time Limit: 10.
% 3.32/0.99  
% 3.32/0.99  
% 3.32/0.99  ------ 
% 3.32/0.99  Current options:
% 3.32/0.99  ------ 
% 3.32/0.99  
% 3.32/0.99  ------ Input Options
% 3.32/0.99  
% 3.32/0.99  --out_options                           all
% 3.32/0.99  --tptp_safe_out                         true
% 3.32/0.99  --problem_path                          ""
% 3.32/0.99  --include_path                          ""
% 3.32/0.99  --clausifier                            res/vclausify_rel
% 3.32/0.99  --clausifier_options                    --mode clausify
% 3.32/0.99  --stdin                                 false
% 3.32/0.99  --stats_out                             all
% 3.32/0.99  
% 3.32/0.99  ------ General Options
% 3.32/0.99  
% 3.32/0.99  --fof                                   false
% 3.32/0.99  --time_out_real                         305.
% 3.32/0.99  --time_out_virtual                      -1.
% 3.32/0.99  --symbol_type_check                     false
% 3.32/0.99  --clausify_out                          false
% 3.32/0.99  --sig_cnt_out                           false
% 3.32/0.99  --trig_cnt_out                          false
% 3.32/0.99  --trig_cnt_out_tolerance                1.
% 3.32/0.99  --trig_cnt_out_sk_spl                   false
% 3.32/0.99  --abstr_cl_out                          false
% 3.32/0.99  
% 3.32/0.99  ------ Global Options
% 3.32/0.99  
% 3.32/0.99  --schedule                              default
% 3.32/0.99  --add_important_lit                     false
% 3.32/0.99  --prop_solver_per_cl                    1000
% 3.32/0.99  --min_unsat_core                        false
% 3.32/0.99  --soft_assumptions                      false
% 3.32/0.99  --soft_lemma_size                       3
% 3.32/0.99  --prop_impl_unit_size                   0
% 3.32/0.99  --prop_impl_unit                        []
% 3.32/0.99  --share_sel_clauses                     true
% 3.32/0.99  --reset_solvers                         false
% 3.32/0.99  --bc_imp_inh                            [conj_cone]
% 3.32/0.99  --conj_cone_tolerance                   3.
% 3.32/0.99  --extra_neg_conj                        none
% 3.32/0.99  --large_theory_mode                     true
% 3.32/0.99  --prolific_symb_bound                   200
% 3.32/0.99  --lt_threshold                          2000
% 3.32/0.99  --clause_weak_htbl                      true
% 3.32/0.99  --gc_record_bc_elim                     false
% 3.32/0.99  
% 3.32/0.99  ------ Preprocessing Options
% 3.32/0.99  
% 3.32/0.99  --preprocessing_flag                    true
% 3.32/0.99  --time_out_prep_mult                    0.1
% 3.32/0.99  --splitting_mode                        input
% 3.32/0.99  --splitting_grd                         true
% 3.32/0.99  --splitting_cvd                         false
% 3.32/0.99  --splitting_cvd_svl                     false
% 3.32/0.99  --splitting_nvd                         32
% 3.32/0.99  --sub_typing                            true
% 3.32/0.99  --prep_gs_sim                           true
% 3.32/0.99  --prep_unflatten                        true
% 3.32/0.99  --prep_res_sim                          true
% 3.32/0.99  --prep_upred                            true
% 3.32/0.99  --prep_sem_filter                       exhaustive
% 3.32/0.99  --prep_sem_filter_out                   false
% 3.32/0.99  --pred_elim                             true
% 3.32/0.99  --res_sim_input                         true
% 3.32/0.99  --eq_ax_congr_red                       true
% 3.32/0.99  --pure_diseq_elim                       true
% 3.32/0.99  --brand_transform                       false
% 3.32/0.99  --non_eq_to_eq                          false
% 3.32/0.99  --prep_def_merge                        true
% 3.32/0.99  --prep_def_merge_prop_impl              false
% 3.32/0.99  --prep_def_merge_mbd                    true
% 3.32/0.99  --prep_def_merge_tr_red                 false
% 3.32/0.99  --prep_def_merge_tr_cl                  false
% 3.32/0.99  --smt_preprocessing                     true
% 3.32/0.99  --smt_ac_axioms                         fast
% 3.32/0.99  --preprocessed_out                      false
% 3.32/0.99  --preprocessed_stats                    false
% 3.32/0.99  
% 3.32/0.99  ------ Abstraction refinement Options
% 3.32/0.99  
% 3.32/0.99  --abstr_ref                             []
% 3.32/0.99  --abstr_ref_prep                        false
% 3.32/0.99  --abstr_ref_until_sat                   false
% 3.32/0.99  --abstr_ref_sig_restrict                funpre
% 3.32/0.99  --abstr_ref_af_restrict_to_split_sk     false
% 3.32/0.99  --abstr_ref_under                       []
% 3.32/0.99  
% 3.32/0.99  ------ SAT Options
% 3.32/0.99  
% 3.32/0.99  --sat_mode                              false
% 3.32/0.99  --sat_fm_restart_options                ""
% 3.32/0.99  --sat_gr_def                            false
% 3.32/0.99  --sat_epr_types                         true
% 3.32/0.99  --sat_non_cyclic_types                  false
% 3.32/0.99  --sat_finite_models                     false
% 3.32/0.99  --sat_fm_lemmas                         false
% 3.32/0.99  --sat_fm_prep                           false
% 3.32/0.99  --sat_fm_uc_incr                        true
% 3.32/0.99  --sat_out_model                         small
% 3.32/0.99  --sat_out_clauses                       false
% 3.32/0.99  
% 3.32/0.99  ------ QBF Options
% 3.32/0.99  
% 3.32/0.99  --qbf_mode                              false
% 3.32/0.99  --qbf_elim_univ                         false
% 3.32/0.99  --qbf_dom_inst                          none
% 3.32/0.99  --qbf_dom_pre_inst                      false
% 3.32/0.99  --qbf_sk_in                             false
% 3.32/0.99  --qbf_pred_elim                         true
% 3.32/0.99  --qbf_split                             512
% 3.32/0.99  
% 3.32/0.99  ------ BMC1 Options
% 3.32/0.99  
% 3.32/0.99  --bmc1_incremental                      false
% 3.32/0.99  --bmc1_axioms                           reachable_all
% 3.32/0.99  --bmc1_min_bound                        0
% 3.32/0.99  --bmc1_max_bound                        -1
% 3.32/0.99  --bmc1_max_bound_default                -1
% 3.32/0.99  --bmc1_symbol_reachability              true
% 3.32/0.99  --bmc1_property_lemmas                  false
% 3.32/0.99  --bmc1_k_induction                      false
% 3.32/0.99  --bmc1_non_equiv_states                 false
% 3.32/0.99  --bmc1_deadlock                         false
% 3.32/0.99  --bmc1_ucm                              false
% 3.32/0.99  --bmc1_add_unsat_core                   none
% 3.32/0.99  --bmc1_unsat_core_children              false
% 3.32/0.99  --bmc1_unsat_core_extrapolate_axioms    false
% 3.32/0.99  --bmc1_out_stat                         full
% 3.32/0.99  --bmc1_ground_init                      false
% 3.32/0.99  --bmc1_pre_inst_next_state              false
% 3.32/0.99  --bmc1_pre_inst_state                   false
% 3.32/0.99  --bmc1_pre_inst_reach_state             false
% 3.32/0.99  --bmc1_out_unsat_core                   false
% 3.32/0.99  --bmc1_aig_witness_out                  false
% 3.32/0.99  --bmc1_verbose                          false
% 3.32/0.99  --bmc1_dump_clauses_tptp                false
% 3.32/0.99  --bmc1_dump_unsat_core_tptp             false
% 3.32/0.99  --bmc1_dump_file                        -
% 3.32/0.99  --bmc1_ucm_expand_uc_limit              128
% 3.32/0.99  --bmc1_ucm_n_expand_iterations          6
% 3.32/0.99  --bmc1_ucm_extend_mode                  1
% 3.32/0.99  --bmc1_ucm_init_mode                    2
% 3.32/0.99  --bmc1_ucm_cone_mode                    none
% 3.32/0.99  --bmc1_ucm_reduced_relation_type        0
% 3.32/0.99  --bmc1_ucm_relax_model                  4
% 3.32/0.99  --bmc1_ucm_full_tr_after_sat            true
% 3.32/0.99  --bmc1_ucm_expand_neg_assumptions       false
% 3.32/0.99  --bmc1_ucm_layered_model                none
% 3.32/0.99  --bmc1_ucm_max_lemma_size               10
% 3.32/0.99  
% 3.32/0.99  ------ AIG Options
% 3.32/0.99  
% 3.32/0.99  --aig_mode                              false
% 3.32/0.99  
% 3.32/0.99  ------ Instantiation Options
% 3.32/0.99  
% 3.32/0.99  --instantiation_flag                    true
% 3.32/0.99  --inst_sos_flag                         false
% 3.32/0.99  --inst_sos_phase                        true
% 3.32/0.99  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 3.32/0.99  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 3.32/0.99  --inst_lit_sel_side                     none
% 3.32/0.99  --inst_solver_per_active                1400
% 3.32/0.99  --inst_solver_calls_frac                1.
% 3.32/0.99  --inst_passive_queue_type               priority_queues
% 3.32/0.99  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 3.32/0.99  --inst_passive_queues_freq              [25;2]
% 3.32/0.99  --inst_dismatching                      true
% 3.32/0.99  --inst_eager_unprocessed_to_passive     true
% 3.32/0.99  --inst_prop_sim_given                   true
% 3.32/0.99  --inst_prop_sim_new                     false
% 3.32/0.99  --inst_subs_new                         false
% 3.32/0.99  --inst_eq_res_simp                      false
% 3.32/0.99  --inst_subs_given                       false
% 3.32/0.99  --inst_orphan_elimination               true
% 3.32/0.99  --inst_learning_loop_flag               true
% 3.32/0.99  --inst_learning_start                   3000
% 3.32/0.99  --inst_learning_factor                  2
% 3.32/0.99  --inst_start_prop_sim_after_learn       3
% 3.32/0.99  --inst_sel_renew                        solver
% 3.32/0.99  --inst_lit_activity_flag                true
% 3.32/0.99  --inst_restr_to_given                   false
% 3.32/0.99  --inst_activity_threshold               500
% 3.32/0.99  --inst_out_proof                        true
% 3.32/0.99  
% 3.32/0.99  ------ Resolution Options
% 3.32/0.99  
% 3.32/0.99  --resolution_flag                       false
% 3.32/0.99  --res_lit_sel                           adaptive
% 3.32/0.99  --res_lit_sel_side                      none
% 3.32/0.99  --res_ordering                          kbo
% 3.32/0.99  --res_to_prop_solver                    active
% 3.32/0.99  --res_prop_simpl_new                    false
% 3.32/0.99  --res_prop_simpl_given                  true
% 3.32/0.99  --res_passive_queue_type                priority_queues
% 3.32/0.99  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 3.32/0.99  --res_passive_queues_freq               [15;5]
% 3.32/0.99  --res_forward_subs                      full
% 3.32/0.99  --res_backward_subs                     full
% 3.32/0.99  --res_forward_subs_resolution           true
% 3.32/0.99  --res_backward_subs_resolution          true
% 3.32/0.99  --res_orphan_elimination                true
% 3.32/0.99  --res_time_limit                        2.
% 3.32/0.99  --res_out_proof                         true
% 3.32/0.99  
% 3.32/0.99  ------ Superposition Options
% 3.32/0.99  
% 3.32/0.99  --superposition_flag                    true
% 3.32/0.99  --sup_passive_queue_type                priority_queues
% 3.32/0.99  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 3.32/0.99  --sup_passive_queues_freq               [8;1;4]
% 3.32/0.99  --demod_completeness_check              fast
% 3.32/0.99  --demod_use_ground                      true
% 3.32/0.99  --sup_to_prop_solver                    passive
% 3.32/0.99  --sup_prop_simpl_new                    true
% 3.32/0.99  --sup_prop_simpl_given                  true
% 3.32/0.99  --sup_fun_splitting                     false
% 3.32/0.99  --sup_smt_interval                      50000
% 3.32/0.99  
% 3.32/0.99  ------ Superposition Simplification Setup
% 3.32/0.99  
% 3.32/0.99  --sup_indices_passive                   []
% 3.32/0.99  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.32/0.99  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.32/0.99  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.32/0.99  --sup_full_triv                         [TrivRules;PropSubs]
% 3.32/0.99  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.32/0.99  --sup_full_bw                           [BwDemod]
% 3.32/0.99  --sup_immed_triv                        [TrivRules]
% 3.32/0.99  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 3.32/0.99  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.32/0.99  --sup_immed_bw_main                     []
% 3.32/0.99  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 3.32/0.99  --sup_input_triv                        [Unflattening;TrivRules]
% 3.32/0.99  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.32/0.99  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 3.32/0.99  
% 3.32/0.99  ------ Combination Options
% 3.32/0.99  
% 3.32/0.99  --comb_res_mult                         3
% 3.32/0.99  --comb_sup_mult                         2
% 3.32/0.99  --comb_inst_mult                        10
% 3.32/0.99  
% 3.32/0.99  ------ Debug Options
% 3.32/0.99  
% 3.32/0.99  --dbg_backtrace                         false
% 3.32/0.99  --dbg_dump_prop_clauses                 false
% 3.32/0.99  --dbg_dump_prop_clauses_file            -
% 3.32/0.99  --dbg_out_stat                          false
% 3.32/0.99  
% 3.32/0.99  
% 3.32/0.99  
% 3.32/0.99  
% 3.32/0.99  ------ Proving...
% 3.32/0.99  
% 3.32/0.99  
% 3.32/0.99  % SZS status Theorem for theBenchmark.p
% 3.32/0.99  
% 3.32/0.99  % SZS output start CNFRefutation for theBenchmark.p
% 3.32/0.99  
% 3.32/0.99  fof(f18,conjecture,(
% 3.32/0.99    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v3_funct_2(X2,X0,X0) & v1_funct_2(X2,X0,X0) & v1_funct_1(X2)) => (r1_tarski(X1,X0) => (k8_relset_1(X0,X0,X2,k7_relset_1(X0,X0,X2,X1)) = X1 & k7_relset_1(X0,X0,X2,k8_relset_1(X0,X0,X2,X1)) = X1)))),
% 3.32/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.32/0.99  
% 3.32/0.99  fof(f19,negated_conjecture,(
% 3.32/0.99    ~! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v3_funct_2(X2,X0,X0) & v1_funct_2(X2,X0,X0) & v1_funct_1(X2)) => (r1_tarski(X1,X0) => (k8_relset_1(X0,X0,X2,k7_relset_1(X0,X0,X2,X1)) = X1 & k7_relset_1(X0,X0,X2,k8_relset_1(X0,X0,X2,X1)) = X1)))),
% 3.32/0.99    inference(negated_conjecture,[],[f18])).
% 3.32/0.99  
% 3.32/0.99  fof(f43,plain,(
% 3.32/0.99    ? [X0,X1,X2] : (((k8_relset_1(X0,X0,X2,k7_relset_1(X0,X0,X2,X1)) != X1 | k7_relset_1(X0,X0,X2,k8_relset_1(X0,X0,X2,X1)) != X1) & r1_tarski(X1,X0)) & (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v3_funct_2(X2,X0,X0) & v1_funct_2(X2,X0,X0) & v1_funct_1(X2)))),
% 3.32/0.99    inference(ennf_transformation,[],[f19])).
% 3.32/0.99  
% 3.32/0.99  fof(f44,plain,(
% 3.32/0.99    ? [X0,X1,X2] : ((k8_relset_1(X0,X0,X2,k7_relset_1(X0,X0,X2,X1)) != X1 | k7_relset_1(X0,X0,X2,k8_relset_1(X0,X0,X2,X1)) != X1) & r1_tarski(X1,X0) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v3_funct_2(X2,X0,X0) & v1_funct_2(X2,X0,X0) & v1_funct_1(X2))),
% 3.32/0.99    inference(flattening,[],[f43])).
% 3.32/0.99  
% 3.32/0.99  fof(f49,plain,(
% 3.32/0.99    ? [X0,X1,X2] : ((k8_relset_1(X0,X0,X2,k7_relset_1(X0,X0,X2,X1)) != X1 | k7_relset_1(X0,X0,X2,k8_relset_1(X0,X0,X2,X1)) != X1) & r1_tarski(X1,X0) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v3_funct_2(X2,X0,X0) & v1_funct_2(X2,X0,X0) & v1_funct_1(X2)) => ((k8_relset_1(sK0,sK0,sK2,k7_relset_1(sK0,sK0,sK2,sK1)) != sK1 | k7_relset_1(sK0,sK0,sK2,k8_relset_1(sK0,sK0,sK2,sK1)) != sK1) & r1_tarski(sK1,sK0) & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) & v3_funct_2(sK2,sK0,sK0) & v1_funct_2(sK2,sK0,sK0) & v1_funct_1(sK2))),
% 3.32/0.99    introduced(choice_axiom,[])).
% 3.32/0.99  
% 3.32/0.99  fof(f50,plain,(
% 3.32/0.99    (k8_relset_1(sK0,sK0,sK2,k7_relset_1(sK0,sK0,sK2,sK1)) != sK1 | k7_relset_1(sK0,sK0,sK2,k8_relset_1(sK0,sK0,sK2,sK1)) != sK1) & r1_tarski(sK1,sK0) & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) & v3_funct_2(sK2,sK0,sK0) & v1_funct_2(sK2,sK0,sK0) & v1_funct_1(sK2)),
% 3.32/0.99    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f44,f49])).
% 3.32/0.99  
% 3.32/0.99  fof(f82,plain,(
% 3.32/0.99    r1_tarski(sK1,sK0)),
% 3.32/0.99    inference(cnf_transformation,[],[f50])).
% 3.32/0.99  
% 3.32/0.99  fof(f81,plain,(
% 3.32/0.99    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))),
% 3.32/0.99    inference(cnf_transformation,[],[f50])).
% 3.32/0.99  
% 3.32/0.99  fof(f17,axiom,(
% 3.32/0.99    ! [X0,X1] : ((m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v3_funct_2(X1,X0,X0) & v1_funct_2(X1,X0,X0) & v1_funct_1(X1)) => k2_funct_1(X1) = k2_funct_2(X0,X1))),
% 3.32/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.32/0.99  
% 3.32/0.99  fof(f41,plain,(
% 3.32/0.99    ! [X0,X1] : (k2_funct_1(X1) = k2_funct_2(X0,X1) | (~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) | ~v3_funct_2(X1,X0,X0) | ~v1_funct_2(X1,X0,X0) | ~v1_funct_1(X1)))),
% 3.32/0.99    inference(ennf_transformation,[],[f17])).
% 3.32/0.99  
% 3.32/0.99  fof(f42,plain,(
% 3.32/0.99    ! [X0,X1] : (k2_funct_1(X1) = k2_funct_2(X0,X1) | ~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) | ~v3_funct_2(X1,X0,X0) | ~v1_funct_2(X1,X0,X0) | ~v1_funct_1(X1))),
% 3.32/0.99    inference(flattening,[],[f41])).
% 3.32/0.99  
% 3.32/0.99  fof(f77,plain,(
% 3.32/0.99    ( ! [X0,X1] : (k2_funct_1(X1) = k2_funct_2(X0,X1) | ~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) | ~v3_funct_2(X1,X0,X0) | ~v1_funct_2(X1,X0,X0) | ~v1_funct_1(X1)) )),
% 3.32/0.99    inference(cnf_transformation,[],[f42])).
% 3.32/0.99  
% 3.32/0.99  fof(f78,plain,(
% 3.32/0.99    v1_funct_1(sK2)),
% 3.32/0.99    inference(cnf_transformation,[],[f50])).
% 3.32/0.99  
% 3.32/0.99  fof(f79,plain,(
% 3.32/0.99    v1_funct_2(sK2,sK0,sK0)),
% 3.32/0.99    inference(cnf_transformation,[],[f50])).
% 3.32/0.99  
% 3.32/0.99  fof(f80,plain,(
% 3.32/0.99    v3_funct_2(sK2,sK0,sK0)),
% 3.32/0.99    inference(cnf_transformation,[],[f50])).
% 3.32/0.99  
% 3.32/0.99  fof(f16,axiom,(
% 3.32/0.99    ! [X0,X1] : ((m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v3_funct_2(X1,X0,X0) & v1_funct_2(X1,X0,X0) & v1_funct_1(X1)) => (m1_subset_1(k2_funct_2(X0,X1),k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v3_funct_2(k2_funct_2(X0,X1),X0,X0) & v1_funct_2(k2_funct_2(X0,X1),X0,X0) & v1_funct_1(k2_funct_2(X0,X1))))),
% 3.32/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.32/0.99  
% 3.32/0.99  fof(f39,plain,(
% 3.32/0.99    ! [X0,X1] : ((m1_subset_1(k2_funct_2(X0,X1),k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v3_funct_2(k2_funct_2(X0,X1),X0,X0) & v1_funct_2(k2_funct_2(X0,X1),X0,X0) & v1_funct_1(k2_funct_2(X0,X1))) | (~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) | ~v3_funct_2(X1,X0,X0) | ~v1_funct_2(X1,X0,X0) | ~v1_funct_1(X1)))),
% 3.32/0.99    inference(ennf_transformation,[],[f16])).
% 3.32/0.99  
% 3.32/0.99  fof(f40,plain,(
% 3.32/0.99    ! [X0,X1] : ((m1_subset_1(k2_funct_2(X0,X1),k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v3_funct_2(k2_funct_2(X0,X1),X0,X0) & v1_funct_2(k2_funct_2(X0,X1),X0,X0) & v1_funct_1(k2_funct_2(X0,X1))) | ~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) | ~v3_funct_2(X1,X0,X0) | ~v1_funct_2(X1,X0,X0) | ~v1_funct_1(X1))),
% 3.32/0.99    inference(flattening,[],[f39])).
% 3.32/0.99  
% 3.32/0.99  fof(f76,plain,(
% 3.32/0.99    ( ! [X0,X1] : (m1_subset_1(k2_funct_2(X0,X1),k1_zfmisc_1(k2_zfmisc_1(X0,X0))) | ~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) | ~v3_funct_2(X1,X0,X0) | ~v1_funct_2(X1,X0,X0) | ~v1_funct_1(X1)) )),
% 3.32/0.99    inference(cnf_transformation,[],[f40])).
% 3.32/0.99  
% 3.32/0.99  fof(f11,axiom,(
% 3.32/0.99    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => (v5_relat_1(X2,X1) & v4_relat_1(X2,X0)))),
% 3.32/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.32/0.99  
% 3.32/0.99  fof(f32,plain,(
% 3.32/0.99    ! [X0,X1,X2] : ((v5_relat_1(X2,X1) & v4_relat_1(X2,X0)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 3.32/0.99    inference(ennf_transformation,[],[f11])).
% 3.32/0.99  
% 3.32/0.99  fof(f64,plain,(
% 3.32/0.99    ( ! [X2,X0,X1] : (v4_relat_1(X2,X0) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 3.32/0.99    inference(cnf_transformation,[],[f32])).
% 3.32/0.99  
% 3.32/0.99  fof(f3,axiom,(
% 3.32/0.99    ! [X0,X1] : (v1_relat_1(X1) => (v4_relat_1(X1,X0) <=> r1_tarski(k1_relat_1(X1),X0)))),
% 3.32/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.32/0.99  
% 3.32/0.99  fof(f21,plain,(
% 3.32/0.99    ! [X0,X1] : ((v4_relat_1(X1,X0) <=> r1_tarski(k1_relat_1(X1),X0)) | ~v1_relat_1(X1))),
% 3.32/0.99    inference(ennf_transformation,[],[f3])).
% 3.32/0.99  
% 3.32/0.99  fof(f47,plain,(
% 3.32/0.99    ! [X0,X1] : (((v4_relat_1(X1,X0) | ~r1_tarski(k1_relat_1(X1),X0)) & (r1_tarski(k1_relat_1(X1),X0) | ~v4_relat_1(X1,X0))) | ~v1_relat_1(X1))),
% 3.32/0.99    inference(nnf_transformation,[],[f21])).
% 3.32/0.99  
% 3.32/0.99  fof(f55,plain,(
% 3.32/0.99    ( ! [X0,X1] : (r1_tarski(k1_relat_1(X1),X0) | ~v4_relat_1(X1,X0) | ~v1_relat_1(X1)) )),
% 3.32/0.99    inference(cnf_transformation,[],[f47])).
% 3.32/0.99  
% 3.32/0.99  fof(f4,axiom,(
% 3.32/0.99    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1))),
% 3.32/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.32/0.99  
% 3.32/0.99  fof(f57,plain,(
% 3.32/0.99    ( ! [X0,X1] : (v1_relat_1(k2_zfmisc_1(X0,X1))) )),
% 3.32/0.99    inference(cnf_transformation,[],[f4])).
% 3.32/0.99  
% 3.32/0.99  fof(f2,axiom,(
% 3.32/0.99    ! [X0] : (v1_relat_1(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => v1_relat_1(X1)))),
% 3.32/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.32/0.99  
% 3.32/0.99  fof(f20,plain,(
% 3.32/0.99    ! [X0] : (! [X1] : (v1_relat_1(X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) | ~v1_relat_1(X0))),
% 3.32/0.99    inference(ennf_transformation,[],[f2])).
% 3.32/0.99  
% 3.32/0.99  fof(f54,plain,(
% 3.32/0.99    ( ! [X0,X1] : (v1_relat_1(X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0)) | ~v1_relat_1(X0)) )),
% 3.32/0.99    inference(cnf_transformation,[],[f20])).
% 3.32/0.99  
% 3.32/0.99  fof(f7,axiom,(
% 3.32/0.99    ! [X0,X1] : (v1_relat_1(X1) => (r1_tarski(k1_relat_1(X1),X0) => k7_relat_1(X1,X0) = X1))),
% 3.32/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.32/0.99  
% 3.32/0.99  fof(f24,plain,(
% 3.32/0.99    ! [X0,X1] : ((k7_relat_1(X1,X0) = X1 | ~r1_tarski(k1_relat_1(X1),X0)) | ~v1_relat_1(X1))),
% 3.32/0.99    inference(ennf_transformation,[],[f7])).
% 3.32/0.99  
% 3.32/0.99  fof(f25,plain,(
% 3.32/0.99    ! [X0,X1] : (k7_relat_1(X1,X0) = X1 | ~r1_tarski(k1_relat_1(X1),X0) | ~v1_relat_1(X1))),
% 3.32/0.99    inference(flattening,[],[f24])).
% 3.32/0.99  
% 3.32/0.99  fof(f60,plain,(
% 3.32/0.99    ( ! [X0,X1] : (k7_relat_1(X1,X0) = X1 | ~r1_tarski(k1_relat_1(X1),X0) | ~v1_relat_1(X1)) )),
% 3.32/0.99    inference(cnf_transformation,[],[f25])).
% 3.32/0.99  
% 3.32/0.99  fof(f5,axiom,(
% 3.32/0.99    ! [X0,X1] : (v1_relat_1(X1) => k2_relat_1(k7_relat_1(X1,X0)) = k9_relat_1(X1,X0))),
% 3.32/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.32/0.99  
% 3.32/0.99  fof(f22,plain,(
% 3.32/0.99    ! [X0,X1] : (k2_relat_1(k7_relat_1(X1,X0)) = k9_relat_1(X1,X0) | ~v1_relat_1(X1))),
% 3.32/0.99    inference(ennf_transformation,[],[f5])).
% 3.32/0.99  
% 3.32/0.99  fof(f58,plain,(
% 3.32/0.99    ( ! [X0,X1] : (k2_relat_1(k7_relat_1(X1,X0)) = k9_relat_1(X1,X0) | ~v1_relat_1(X1)) )),
% 3.32/0.99    inference(cnf_transformation,[],[f22])).
% 3.32/0.99  
% 3.32/0.99  fof(f14,axiom,(
% 3.32/0.99    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => ((v3_funct_2(X2,X0,X1) & v1_funct_1(X2)) => (v2_funct_2(X2,X1) & v2_funct_1(X2) & v1_funct_1(X2))))),
% 3.32/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.32/0.99  
% 3.32/0.99  fof(f35,plain,(
% 3.32/0.99    ! [X0,X1,X2] : (((v2_funct_2(X2,X1) & v2_funct_1(X2) & v1_funct_1(X2)) | (~v3_funct_2(X2,X0,X1) | ~v1_funct_1(X2))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 3.32/0.99    inference(ennf_transformation,[],[f14])).
% 3.32/0.99  
% 3.32/0.99  fof(f36,plain,(
% 3.32/0.99    ! [X0,X1,X2] : ((v2_funct_2(X2,X1) & v2_funct_1(X2) & v1_funct_1(X2)) | ~v3_funct_2(X2,X0,X1) | ~v1_funct_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 3.32/0.99    inference(flattening,[],[f35])).
% 3.32/0.99  
% 3.32/0.99  fof(f70,plain,(
% 3.32/0.99    ( ! [X2,X0,X1] : (v2_funct_2(X2,X1) | ~v3_funct_2(X2,X0,X1) | ~v1_funct_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 3.32/0.99    inference(cnf_transformation,[],[f36])).
% 3.32/0.99  
% 3.32/0.99  fof(f15,axiom,(
% 3.32/0.99    ! [X0,X1] : ((v5_relat_1(X1,X0) & v1_relat_1(X1)) => (v2_funct_2(X1,X0) <=> k2_relat_1(X1) = X0))),
% 3.32/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.32/0.99  
% 3.32/0.99  fof(f37,plain,(
% 3.32/0.99    ! [X0,X1] : ((v2_funct_2(X1,X0) <=> k2_relat_1(X1) = X0) | (~v5_relat_1(X1,X0) | ~v1_relat_1(X1)))),
% 3.32/0.99    inference(ennf_transformation,[],[f15])).
% 3.32/0.99  
% 3.32/0.99  fof(f38,plain,(
% 3.32/0.99    ! [X0,X1] : ((v2_funct_2(X1,X0) <=> k2_relat_1(X1) = X0) | ~v5_relat_1(X1,X0) | ~v1_relat_1(X1))),
% 3.32/0.99    inference(flattening,[],[f37])).
% 3.32/0.99  
% 3.32/0.99  fof(f48,plain,(
% 3.32/0.99    ! [X0,X1] : (((v2_funct_2(X1,X0) | k2_relat_1(X1) != X0) & (k2_relat_1(X1) = X0 | ~v2_funct_2(X1,X0))) | ~v5_relat_1(X1,X0) | ~v1_relat_1(X1))),
% 3.32/0.99    inference(nnf_transformation,[],[f38])).
% 3.32/0.99  
% 3.32/0.99  fof(f71,plain,(
% 3.32/0.99    ( ! [X0,X1] : (k2_relat_1(X1) = X0 | ~v2_funct_2(X1,X0) | ~v5_relat_1(X1,X0) | ~v1_relat_1(X1)) )),
% 3.32/0.99    inference(cnf_transformation,[],[f48])).
% 3.32/0.99  
% 3.32/0.99  fof(f65,plain,(
% 3.32/0.99    ( ! [X2,X0,X1] : (v5_relat_1(X2,X1) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 3.32/0.99    inference(cnf_transformation,[],[f32])).
% 3.32/0.99  
% 3.32/0.99  fof(f73,plain,(
% 3.32/0.99    ( ! [X0,X1] : (v1_funct_1(k2_funct_2(X0,X1)) | ~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) | ~v3_funct_2(X1,X0,X0) | ~v1_funct_2(X1,X0,X0) | ~v1_funct_1(X1)) )),
% 3.32/0.99    inference(cnf_transformation,[],[f40])).
% 3.32/0.99  
% 3.32/0.99  fof(f75,plain,(
% 3.32/0.99    ( ! [X0,X1] : (v3_funct_2(k2_funct_2(X0,X1),X0,X0) | ~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) | ~v3_funct_2(X1,X0,X0) | ~v1_funct_2(X1,X0,X0) | ~v1_funct_1(X1)) )),
% 3.32/0.99    inference(cnf_transformation,[],[f40])).
% 3.32/0.99  
% 3.32/0.99  fof(f69,plain,(
% 3.32/0.99    ( ! [X2,X0,X1] : (v2_funct_1(X2) | ~v3_funct_2(X2,X0,X1) | ~v1_funct_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 3.32/0.99    inference(cnf_transformation,[],[f36])).
% 3.32/0.99  
% 3.32/0.99  fof(f1,axiom,(
% 3.32/0.99    ! [X0,X1] : (X0 = X1 <=> (r1_tarski(X1,X0) & r1_tarski(X0,X1)))),
% 3.32/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.32/0.99  
% 3.32/0.99  fof(f45,plain,(
% 3.32/0.99    ! [X0,X1] : ((X0 = X1 | (~r1_tarski(X1,X0) | ~r1_tarski(X0,X1))) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 3.32/0.99    inference(nnf_transformation,[],[f1])).
% 3.32/0.99  
% 3.32/0.99  fof(f46,plain,(
% 3.32/0.99    ! [X0,X1] : ((X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 3.32/0.99    inference(flattening,[],[f45])).
% 3.32/0.99  
% 3.32/0.99  fof(f52,plain,(
% 3.32/0.99    ( ! [X0,X1] : (r1_tarski(X1,X0) | X0 != X1) )),
% 3.32/0.99    inference(cnf_transformation,[],[f46])).
% 3.32/0.99  
% 3.32/0.99  fof(f84,plain,(
% 3.32/0.99    ( ! [X1] : (r1_tarski(X1,X1)) )),
% 3.32/0.99    inference(equality_resolution,[],[f52])).
% 3.32/0.99  
% 3.32/0.99  fof(f10,axiom,(
% 3.32/0.99    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => ! [X1] : ((r1_tarski(X1,k1_relat_1(X0)) & v2_funct_1(X0)) => k9_relat_1(k2_funct_1(X0),k9_relat_1(X0,X1)) = X1))),
% 3.32/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.32/0.99  
% 3.32/0.99  fof(f30,plain,(
% 3.32/0.99    ! [X0] : (! [X1] : (k9_relat_1(k2_funct_1(X0),k9_relat_1(X0,X1)) = X1 | (~r1_tarski(X1,k1_relat_1(X0)) | ~v2_funct_1(X0))) | (~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 3.32/0.99    inference(ennf_transformation,[],[f10])).
% 3.32/0.99  
% 3.32/0.99  fof(f31,plain,(
% 3.32/0.99    ! [X0] : (! [X1] : (k9_relat_1(k2_funct_1(X0),k9_relat_1(X0,X1)) = X1 | ~r1_tarski(X1,k1_relat_1(X0)) | ~v2_funct_1(X0)) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 3.32/0.99    inference(flattening,[],[f30])).
% 3.32/0.99  
% 3.32/0.99  fof(f63,plain,(
% 3.32/0.99    ( ! [X0,X1] : (k9_relat_1(k2_funct_1(X0),k9_relat_1(X0,X1)) = X1 | ~r1_tarski(X1,k1_relat_1(X0)) | ~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 3.32/0.99    inference(cnf_transformation,[],[f31])).
% 3.32/0.99  
% 3.32/0.99  fof(f8,axiom,(
% 3.32/0.99    ! [X0,X1] : ((v1_funct_1(X1) & v1_relat_1(X1)) => (r1_tarski(X0,k2_relat_1(X1)) => k9_relat_1(X1,k10_relat_1(X1,X0)) = X0))),
% 3.32/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.32/0.99  
% 3.32/0.99  fof(f26,plain,(
% 3.32/0.99    ! [X0,X1] : ((k9_relat_1(X1,k10_relat_1(X1,X0)) = X0 | ~r1_tarski(X0,k2_relat_1(X1))) | (~v1_funct_1(X1) | ~v1_relat_1(X1)))),
% 3.32/0.99    inference(ennf_transformation,[],[f8])).
% 3.32/0.99  
% 3.32/0.99  fof(f27,plain,(
% 3.32/0.99    ! [X0,X1] : (k9_relat_1(X1,k10_relat_1(X1,X0)) = X0 | ~r1_tarski(X0,k2_relat_1(X1)) | ~v1_funct_1(X1) | ~v1_relat_1(X1))),
% 3.32/0.99    inference(flattening,[],[f26])).
% 3.32/0.99  
% 3.32/0.99  fof(f61,plain,(
% 3.32/0.99    ( ! [X0,X1] : (k9_relat_1(X1,k10_relat_1(X1,X0)) = X0 | ~r1_tarski(X0,k2_relat_1(X1)) | ~v1_funct_1(X1) | ~v1_relat_1(X1)) )),
% 3.32/0.99    inference(cnf_transformation,[],[f27])).
% 3.32/0.99  
% 3.32/0.99  fof(f6,axiom,(
% 3.32/0.99    ! [X0] : (v1_relat_1(X0) => k1_relat_1(X0) = k10_relat_1(X0,k2_relat_1(X0)))),
% 3.32/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.32/0.99  
% 3.32/0.99  fof(f23,plain,(
% 3.32/0.99    ! [X0] : (k1_relat_1(X0) = k10_relat_1(X0,k2_relat_1(X0)) | ~v1_relat_1(X0))),
% 3.32/0.99    inference(ennf_transformation,[],[f6])).
% 3.32/0.99  
% 3.32/0.99  fof(f59,plain,(
% 3.32/0.99    ( ! [X0] : (k1_relat_1(X0) = k10_relat_1(X0,k2_relat_1(X0)) | ~v1_relat_1(X0)) )),
% 3.32/0.99    inference(cnf_transformation,[],[f23])).
% 3.32/0.99  
% 3.32/0.99  fof(f9,axiom,(
% 3.32/0.99    ! [X0,X1] : ((v1_funct_1(X1) & v1_relat_1(X1)) => ((v2_funct_1(X1) & r1_tarski(X0,k1_relat_1(X1))) => k10_relat_1(X1,k9_relat_1(X1,X0)) = X0))),
% 3.32/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.32/0.99  
% 3.32/0.99  fof(f28,plain,(
% 3.32/0.99    ! [X0,X1] : ((k10_relat_1(X1,k9_relat_1(X1,X0)) = X0 | (~v2_funct_1(X1) | ~r1_tarski(X0,k1_relat_1(X1)))) | (~v1_funct_1(X1) | ~v1_relat_1(X1)))),
% 3.32/0.99    inference(ennf_transformation,[],[f9])).
% 3.32/0.99  
% 3.32/0.99  fof(f29,plain,(
% 3.32/0.99    ! [X0,X1] : (k10_relat_1(X1,k9_relat_1(X1,X0)) = X0 | ~v2_funct_1(X1) | ~r1_tarski(X0,k1_relat_1(X1)) | ~v1_funct_1(X1) | ~v1_relat_1(X1))),
% 3.32/0.99    inference(flattening,[],[f28])).
% 3.32/0.99  
% 3.32/0.99  fof(f62,plain,(
% 3.32/0.99    ( ! [X0,X1] : (k10_relat_1(X1,k9_relat_1(X1,X0)) = X0 | ~v2_funct_1(X1) | ~r1_tarski(X0,k1_relat_1(X1)) | ~v1_funct_1(X1) | ~v1_relat_1(X1)) )),
% 3.32/0.99    inference(cnf_transformation,[],[f29])).
% 3.32/0.99  
% 3.32/0.99  fof(f13,axiom,(
% 3.32/0.99    ! [X0,X1,X2,X3] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k10_relat_1(X2,X3) = k8_relset_1(X0,X1,X2,X3))),
% 3.32/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.32/0.99  
% 3.32/0.99  fof(f34,plain,(
% 3.32/0.99    ! [X0,X1,X2,X3] : (k10_relat_1(X2,X3) = k8_relset_1(X0,X1,X2,X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 3.32/0.99    inference(ennf_transformation,[],[f13])).
% 3.32/0.99  
% 3.32/0.99  fof(f67,plain,(
% 3.32/0.99    ( ! [X2,X0,X3,X1] : (k10_relat_1(X2,X3) = k8_relset_1(X0,X1,X2,X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 3.32/0.99    inference(cnf_transformation,[],[f34])).
% 3.32/0.99  
% 3.32/0.99  fof(f83,plain,(
% 3.32/0.99    k8_relset_1(sK0,sK0,sK2,k7_relset_1(sK0,sK0,sK2,sK1)) != sK1 | k7_relset_1(sK0,sK0,sK2,k8_relset_1(sK0,sK0,sK2,sK1)) != sK1),
% 3.32/0.99    inference(cnf_transformation,[],[f50])).
% 3.32/0.99  
% 3.32/0.99  fof(f12,axiom,(
% 3.32/0.99    ! [X0,X1,X2,X3] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k9_relat_1(X2,X3) = k7_relset_1(X0,X1,X2,X3))),
% 3.32/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.32/0.99  
% 3.32/0.99  fof(f33,plain,(
% 3.32/0.99    ! [X0,X1,X2,X3] : (k9_relat_1(X2,X3) = k7_relset_1(X0,X1,X2,X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 3.32/0.99    inference(ennf_transformation,[],[f12])).
% 3.32/0.99  
% 3.32/0.99  fof(f66,plain,(
% 3.32/0.99    ( ! [X2,X0,X3,X1] : (k9_relat_1(X2,X3) = k7_relset_1(X0,X1,X2,X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 3.32/0.99    inference(cnf_transformation,[],[f33])).
% 3.32/0.99  
% 3.32/0.99  cnf(c_28,negated_conjecture,
% 3.32/0.99      ( r1_tarski(sK1,sK0) ),
% 3.32/0.99      inference(cnf_transformation,[],[f82]) ).
% 3.32/0.99  
% 3.32/0.99  cnf(c_1203,plain,
% 3.32/0.99      ( r1_tarski(sK1,sK0) = iProver_top ),
% 3.32/0.99      inference(predicate_to_equality,[status(thm)],[c_28]) ).
% 3.32/0.99  
% 3.32/0.99  cnf(c_29,negated_conjecture,
% 3.32/0.99      ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) ),
% 3.32/0.99      inference(cnf_transformation,[],[f81]) ).
% 3.32/0.99  
% 3.32/0.99  cnf(c_1202,plain,
% 3.32/0.99      ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) = iProver_top ),
% 3.32/0.99      inference(predicate_to_equality,[status(thm)],[c_29]) ).
% 3.32/0.99  
% 3.32/0.99  cnf(c_26,plain,
% 3.32/0.99      ( ~ v1_funct_2(X0,X1,X1)
% 3.32/0.99      | ~ v3_funct_2(X0,X1,X1)
% 3.32/0.99      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X1)))
% 3.32/0.99      | ~ v1_funct_1(X0)
% 3.32/0.99      | k2_funct_2(X1,X0) = k2_funct_1(X0) ),
% 3.32/0.99      inference(cnf_transformation,[],[f77]) ).
% 3.32/0.99  
% 3.32/0.99  cnf(c_1204,plain,
% 3.32/0.99      ( k2_funct_2(X0,X1) = k2_funct_1(X1)
% 3.32/0.99      | v1_funct_2(X1,X0,X0) != iProver_top
% 3.32/0.99      | v3_funct_2(X1,X0,X0) != iProver_top
% 3.32/0.99      | m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) != iProver_top
% 3.32/0.99      | v1_funct_1(X1) != iProver_top ),
% 3.32/0.99      inference(predicate_to_equality,[status(thm)],[c_26]) ).
% 3.32/0.99  
% 3.32/0.99  cnf(c_3167,plain,
% 3.32/0.99      ( k2_funct_2(sK0,sK2) = k2_funct_1(sK2)
% 3.32/0.99      | v1_funct_2(sK2,sK0,sK0) != iProver_top
% 3.32/0.99      | v3_funct_2(sK2,sK0,sK0) != iProver_top
% 3.32/0.99      | v1_funct_1(sK2) != iProver_top ),
% 3.32/0.99      inference(superposition,[status(thm)],[c_1202,c_1204]) ).
% 3.32/0.99  
% 3.32/0.99  cnf(c_32,negated_conjecture,
% 3.32/0.99      ( v1_funct_1(sK2) ),
% 3.32/0.99      inference(cnf_transformation,[],[f78]) ).
% 3.32/0.99  
% 3.32/0.99  cnf(c_31,negated_conjecture,
% 3.32/0.99      ( v1_funct_2(sK2,sK0,sK0) ),
% 3.32/0.99      inference(cnf_transformation,[],[f79]) ).
% 3.32/0.99  
% 3.32/0.99  cnf(c_30,negated_conjecture,
% 3.32/0.99      ( v3_funct_2(sK2,sK0,sK0) ),
% 3.32/0.99      inference(cnf_transformation,[],[f80]) ).
% 3.32/0.99  
% 3.32/0.99  cnf(c_1529,plain,
% 3.32/0.99      ( ~ v1_funct_2(sK2,X0,X0)
% 3.32/0.99      | ~ v3_funct_2(sK2,X0,X0)
% 3.32/0.99      | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
% 3.32/0.99      | ~ v1_funct_1(sK2)
% 3.32/0.99      | k2_funct_2(X0,sK2) = k2_funct_1(sK2) ),
% 3.32/0.99      inference(instantiation,[status(thm)],[c_26]) ).
% 3.32/0.99  
% 3.32/0.99  cnf(c_1531,plain,
% 3.32/0.99      ( ~ v1_funct_2(sK2,sK0,sK0)
% 3.32/0.99      | ~ v3_funct_2(sK2,sK0,sK0)
% 3.32/0.99      | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
% 3.32/0.99      | ~ v1_funct_1(sK2)
% 3.32/0.99      | k2_funct_2(sK0,sK2) = k2_funct_1(sK2) ),
% 3.32/0.99      inference(instantiation,[status(thm)],[c_1529]) ).
% 3.32/0.99  
% 3.32/0.99  cnf(c_3346,plain,
% 3.32/0.99      ( k2_funct_2(sK0,sK2) = k2_funct_1(sK2) ),
% 3.32/0.99      inference(global_propositional_subsumption,
% 3.32/0.99                [status(thm)],
% 3.32/0.99                [c_3167,c_32,c_31,c_30,c_29,c_1531]) ).
% 3.32/0.99  
% 3.32/0.99  cnf(c_22,plain,
% 3.32/0.99      ( ~ v1_funct_2(X0,X1,X1)
% 3.32/0.99      | ~ v3_funct_2(X0,X1,X1)
% 3.32/0.99      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X1)))
% 3.32/0.99      | m1_subset_1(k2_funct_2(X1,X0),k1_zfmisc_1(k2_zfmisc_1(X1,X1)))
% 3.32/0.99      | ~ v1_funct_1(X0) ),
% 3.32/0.99      inference(cnf_transformation,[],[f76]) ).
% 3.32/0.99  
% 3.32/0.99  cnf(c_1208,plain,
% 3.32/0.99      ( v1_funct_2(X0,X1,X1) != iProver_top
% 3.32/0.99      | v3_funct_2(X0,X1,X1) != iProver_top
% 3.32/0.99      | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X1))) != iProver_top
% 3.32/0.99      | m1_subset_1(k2_funct_2(X1,X0),k1_zfmisc_1(k2_zfmisc_1(X1,X1))) = iProver_top
% 3.32/0.99      | v1_funct_1(X0) != iProver_top ),
% 3.32/0.99      inference(predicate_to_equality,[status(thm)],[c_22]) ).
% 3.32/0.99  
% 3.32/0.99  cnf(c_3833,plain,
% 3.32/0.99      ( v1_funct_2(sK2,sK0,sK0) != iProver_top
% 3.32/0.99      | v3_funct_2(sK2,sK0,sK0) != iProver_top
% 3.32/0.99      | m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) = iProver_top
% 3.32/0.99      | m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) != iProver_top
% 3.32/0.99      | v1_funct_1(sK2) != iProver_top ),
% 3.32/0.99      inference(superposition,[status(thm)],[c_3346,c_1208]) ).
% 3.32/0.99  
% 3.32/0.99  cnf(c_33,plain,
% 3.32/0.99      ( v1_funct_1(sK2) = iProver_top ),
% 3.32/0.99      inference(predicate_to_equality,[status(thm)],[c_32]) ).
% 3.32/0.99  
% 3.32/0.99  cnf(c_34,plain,
% 3.32/0.99      ( v1_funct_2(sK2,sK0,sK0) = iProver_top ),
% 3.32/0.99      inference(predicate_to_equality,[status(thm)],[c_31]) ).
% 3.32/0.99  
% 3.32/0.99  cnf(c_35,plain,
% 3.32/0.99      ( v3_funct_2(sK2,sK0,sK0) = iProver_top ),
% 3.32/0.99      inference(predicate_to_equality,[status(thm)],[c_30]) ).
% 3.32/0.99  
% 3.32/0.99  cnf(c_36,plain,
% 3.32/0.99      ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) = iProver_top ),
% 3.32/0.99      inference(predicate_to_equality,[status(thm)],[c_29]) ).
% 3.32/0.99  
% 3.32/0.99  cnf(c_4571,plain,
% 3.32/0.99      ( m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) = iProver_top ),
% 3.32/0.99      inference(global_propositional_subsumption,
% 3.32/0.99                [status(thm)],
% 3.32/0.99                [c_3833,c_33,c_34,c_35,c_36]) ).
% 3.32/0.99  
% 3.32/0.99  cnf(c_14,plain,
% 3.32/0.99      ( v4_relat_1(X0,X1)
% 3.32/0.99      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) ),
% 3.32/0.99      inference(cnf_transformation,[],[f64]) ).
% 3.32/0.99  
% 3.32/0.99  cnf(c_5,plain,
% 3.32/0.99      ( ~ v4_relat_1(X0,X1)
% 3.32/0.99      | r1_tarski(k1_relat_1(X0),X1)
% 3.32/0.99      | ~ v1_relat_1(X0) ),
% 3.32/0.99      inference(cnf_transformation,[],[f55]) ).
% 3.32/0.99  
% 3.32/0.99  cnf(c_352,plain,
% 3.32/0.99      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.32/0.99      | r1_tarski(k1_relat_1(X0),X1)
% 3.32/0.99      | ~ v1_relat_1(X0) ),
% 3.32/0.99      inference(resolution,[status(thm)],[c_14,c_5]) ).
% 3.32/0.99  
% 3.32/0.99  cnf(c_1198,plain,
% 3.32/0.99      ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) != iProver_top
% 3.32/0.99      | r1_tarski(k1_relat_1(X0),X1) = iProver_top
% 3.32/0.99      | v1_relat_1(X0) != iProver_top ),
% 3.32/0.99      inference(predicate_to_equality,[status(thm)],[c_352]) ).
% 3.32/0.99  
% 3.32/0.99  cnf(c_4581,plain,
% 3.32/0.99      ( r1_tarski(k1_relat_1(k2_funct_1(sK2)),sK0) = iProver_top
% 3.32/0.99      | v1_relat_1(k2_funct_1(sK2)) != iProver_top ),
% 3.32/0.99      inference(superposition,[status(thm)],[c_4571,c_1198]) ).
% 3.32/0.99  
% 3.32/0.99  cnf(c_6,plain,
% 3.32/0.99      ( v1_relat_1(k2_zfmisc_1(X0,X1)) ),
% 3.32/0.99      inference(cnf_transformation,[],[f57]) ).
% 3.32/0.99  
% 3.32/0.99  cnf(c_96,plain,
% 3.32/0.99      ( v1_relat_1(k2_zfmisc_1(X0,X1)) = iProver_top ),
% 3.32/0.99      inference(predicate_to_equality,[status(thm)],[c_6]) ).
% 3.32/0.99  
% 3.32/0.99  cnf(c_98,plain,
% 3.32/0.99      ( v1_relat_1(k2_zfmisc_1(sK0,sK0)) = iProver_top ),
% 3.32/0.99      inference(instantiation,[status(thm)],[c_96]) ).
% 3.32/0.99  
% 3.32/0.99  cnf(c_3,plain,
% 3.32/0.99      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
% 3.32/0.99      | ~ v1_relat_1(X1)
% 3.32/0.99      | v1_relat_1(X0) ),
% 3.32/0.99      inference(cnf_transformation,[],[f54]) ).
% 3.32/0.99  
% 3.32/0.99  cnf(c_1219,plain,
% 3.32/0.99      ( m1_subset_1(X0,k1_zfmisc_1(X1)) != iProver_top
% 3.32/0.99      | v1_relat_1(X1) != iProver_top
% 3.32/0.99      | v1_relat_1(X0) = iProver_top ),
% 3.32/0.99      inference(predicate_to_equality,[status(thm)],[c_3]) ).
% 3.32/0.99  
% 3.32/0.99  cnf(c_4576,plain,
% 3.32/0.99      ( v1_relat_1(k2_zfmisc_1(sK0,sK0)) != iProver_top
% 3.32/0.99      | v1_relat_1(k2_funct_1(sK2)) = iProver_top ),
% 3.32/0.99      inference(superposition,[status(thm)],[c_4571,c_1219]) ).
% 3.32/0.99  
% 3.32/0.99  cnf(c_5012,plain,
% 3.32/0.99      ( r1_tarski(k1_relat_1(k2_funct_1(sK2)),sK0) = iProver_top ),
% 3.32/0.99      inference(global_propositional_subsumption,
% 3.32/0.99                [status(thm)],
% 3.32/0.99                [c_4581,c_98,c_4576]) ).
% 3.32/0.99  
% 3.32/0.99  cnf(c_9,plain,
% 3.32/0.99      ( ~ r1_tarski(k1_relat_1(X0),X1)
% 3.32/0.99      | ~ v1_relat_1(X0)
% 3.32/0.99      | k7_relat_1(X0,X1) = X0 ),
% 3.32/0.99      inference(cnf_transformation,[],[f60]) ).
% 3.32/0.99  
% 3.32/0.99  cnf(c_1215,plain,
% 3.32/0.99      ( k7_relat_1(X0,X1) = X0
% 3.32/0.99      | r1_tarski(k1_relat_1(X0),X1) != iProver_top
% 3.32/0.99      | v1_relat_1(X0) != iProver_top ),
% 3.32/0.99      inference(predicate_to_equality,[status(thm)],[c_9]) ).
% 3.32/0.99  
% 3.32/0.99  cnf(c_5018,plain,
% 3.32/0.99      ( k7_relat_1(k2_funct_1(sK2),sK0) = k2_funct_1(sK2)
% 3.32/0.99      | v1_relat_1(k2_funct_1(sK2)) != iProver_top ),
% 3.32/0.99      inference(superposition,[status(thm)],[c_5012,c_1215]) ).
% 3.32/0.99  
% 3.32/0.99  cnf(c_5446,plain,
% 3.32/0.99      ( k7_relat_1(k2_funct_1(sK2),sK0) = k2_funct_1(sK2) ),
% 3.32/0.99      inference(global_propositional_subsumption,
% 3.32/0.99                [status(thm)],
% 3.32/0.99                [c_5018,c_98,c_4576]) ).
% 3.32/0.99  
% 3.32/0.99  cnf(c_4884,plain,
% 3.32/0.99      ( v1_relat_1(k2_funct_1(sK2)) = iProver_top ),
% 3.32/0.99      inference(global_propositional_subsumption,
% 3.32/0.99                [status(thm)],
% 3.32/0.99                [c_4576,c_98]) ).
% 3.32/0.99  
% 3.32/0.99  cnf(c_7,plain,
% 3.32/0.99      ( ~ v1_relat_1(X0)
% 3.32/0.99      | k2_relat_1(k7_relat_1(X0,X1)) = k9_relat_1(X0,X1) ),
% 3.32/0.99      inference(cnf_transformation,[],[f58]) ).
% 3.32/0.99  
% 3.32/0.99  cnf(c_1217,plain,
% 3.32/0.99      ( k2_relat_1(k7_relat_1(X0,X1)) = k9_relat_1(X0,X1)
% 3.32/0.99      | v1_relat_1(X0) != iProver_top ),
% 3.32/0.99      inference(predicate_to_equality,[status(thm)],[c_7]) ).
% 3.32/0.99  
% 3.32/0.99  cnf(c_4890,plain,
% 3.32/0.99      ( k2_relat_1(k7_relat_1(k2_funct_1(sK2),X0)) = k9_relat_1(k2_funct_1(sK2),X0) ),
% 3.32/0.99      inference(superposition,[status(thm)],[c_4884,c_1217]) ).
% 3.32/0.99  
% 3.32/0.99  cnf(c_5449,plain,
% 3.32/0.99      ( k9_relat_1(k2_funct_1(sK2),sK0) = k2_relat_1(k2_funct_1(sK2)) ),
% 3.32/0.99      inference(superposition,[status(thm)],[c_5446,c_4890]) ).
% 3.32/0.99  
% 3.32/0.99  cnf(c_17,plain,
% 3.32/0.99      ( ~ v3_funct_2(X0,X1,X2)
% 3.32/0.99      | v2_funct_2(X0,X2)
% 3.32/0.99      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.32/0.99      | ~ v1_funct_1(X0) ),
% 3.32/0.99      inference(cnf_transformation,[],[f70]) ).
% 3.32/0.99  
% 3.32/0.99  cnf(c_21,plain,
% 3.32/0.99      ( ~ v2_funct_2(X0,X1)
% 3.32/0.99      | ~ v5_relat_1(X0,X1)
% 3.32/0.99      | ~ v1_relat_1(X0)
% 3.32/0.99      | k2_relat_1(X0) = X1 ),
% 3.32/0.99      inference(cnf_transformation,[],[f71]) ).
% 3.32/0.99  
% 3.32/0.99  cnf(c_410,plain,
% 3.32/0.99      ( ~ v3_funct_2(X0,X1,X2)
% 3.32/0.99      | ~ v5_relat_1(X3,X4)
% 3.32/0.99      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.32/0.99      | ~ v1_funct_1(X0)
% 3.32/0.99      | ~ v1_relat_1(X3)
% 3.32/0.99      | X3 != X0
% 3.32/0.99      | X4 != X2
% 3.32/0.99      | k2_relat_1(X3) = X4 ),
% 3.32/0.99      inference(resolution_lifted,[status(thm)],[c_17,c_21]) ).
% 3.32/0.99  
% 3.32/0.99  cnf(c_411,plain,
% 3.32/0.99      ( ~ v3_funct_2(X0,X1,X2)
% 3.32/0.99      | ~ v5_relat_1(X0,X2)
% 3.32/0.99      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.32/0.99      | ~ v1_funct_1(X0)
% 3.32/0.99      | ~ v1_relat_1(X0)
% 3.32/0.99      | k2_relat_1(X0) = X2 ),
% 3.32/0.99      inference(unflattening,[status(thm)],[c_410]) ).
% 3.32/0.99  
% 3.32/0.99  cnf(c_13,plain,
% 3.32/0.99      ( v5_relat_1(X0,X1)
% 3.32/0.99      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) ),
% 3.32/0.99      inference(cnf_transformation,[],[f65]) ).
% 3.32/0.99  
% 3.32/0.99  cnf(c_427,plain,
% 3.32/0.99      ( ~ v3_funct_2(X0,X1,X2)
% 3.32/0.99      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.32/0.99      | ~ v1_funct_1(X0)
% 3.32/0.99      | ~ v1_relat_1(X0)
% 3.32/0.99      | k2_relat_1(X0) = X2 ),
% 3.32/0.99      inference(forward_subsumption_resolution,
% 3.32/0.99                [status(thm)],
% 3.32/0.99                [c_411,c_13]) ).
% 3.32/0.99  
% 3.32/0.99  cnf(c_1197,plain,
% 3.32/0.99      ( k2_relat_1(X0) = X1
% 3.32/0.99      | v3_funct_2(X0,X2,X1) != iProver_top
% 3.32/0.99      | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) != iProver_top
% 3.32/0.99      | v1_funct_1(X0) != iProver_top
% 3.32/0.99      | v1_relat_1(X0) != iProver_top ),
% 3.32/0.99      inference(predicate_to_equality,[status(thm)],[c_427]) ).
% 3.32/0.99  
% 3.32/0.99  cnf(c_4579,plain,
% 3.32/0.99      ( k2_relat_1(k2_funct_1(sK2)) = sK0
% 3.32/0.99      | v3_funct_2(k2_funct_1(sK2),sK0,sK0) != iProver_top
% 3.32/0.99      | v1_funct_1(k2_funct_1(sK2)) != iProver_top
% 3.32/0.99      | v1_relat_1(k2_funct_1(sK2)) != iProver_top ),
% 3.32/0.99      inference(superposition,[status(thm)],[c_4571,c_1197]) ).
% 3.32/0.99  
% 3.32/0.99  cnf(c_25,plain,
% 3.32/0.99      ( ~ v1_funct_2(X0,X1,X1)
% 3.32/0.99      | ~ v3_funct_2(X0,X1,X1)
% 3.32/0.99      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X1)))
% 3.32/0.99      | ~ v1_funct_1(X0)
% 3.32/0.99      | v1_funct_1(k2_funct_2(X1,X0)) ),
% 3.32/0.99      inference(cnf_transformation,[],[f73]) ).
% 3.32/0.99  
% 3.32/0.99  cnf(c_1205,plain,
% 3.32/0.99      ( v1_funct_2(X0,X1,X1) != iProver_top
% 3.32/0.99      | v3_funct_2(X0,X1,X1) != iProver_top
% 3.32/0.99      | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X1))) != iProver_top
% 3.32/0.99      | v1_funct_1(X0) != iProver_top
% 3.32/0.99      | v1_funct_1(k2_funct_2(X1,X0)) = iProver_top ),
% 3.32/0.99      inference(predicate_to_equality,[status(thm)],[c_25]) ).
% 3.32/0.99  
% 3.32/0.99  cnf(c_3293,plain,
% 3.32/0.99      ( v1_funct_2(sK2,sK0,sK0) != iProver_top
% 3.32/0.99      | v3_funct_2(sK2,sK0,sK0) != iProver_top
% 3.32/0.99      | v1_funct_1(k2_funct_2(sK0,sK2)) = iProver_top
% 3.32/0.99      | v1_funct_1(sK2) != iProver_top ),
% 3.32/0.99      inference(superposition,[status(thm)],[c_1202,c_1205]) ).
% 3.32/0.99  
% 3.32/0.99  cnf(c_1514,plain,
% 3.32/0.99      ( ~ v1_funct_2(sK2,X0,X0)
% 3.32/0.99      | ~ v3_funct_2(sK2,X0,X0)
% 3.32/0.99      | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
% 3.32/0.99      | v1_funct_1(k2_funct_2(X0,sK2))
% 3.32/0.99      | ~ v1_funct_1(sK2) ),
% 3.32/0.99      inference(instantiation,[status(thm)],[c_25]) ).
% 3.32/0.99  
% 3.32/0.99  cnf(c_1515,plain,
% 3.32/0.99      ( v1_funct_2(sK2,X0,X0) != iProver_top
% 3.32/0.99      | v3_funct_2(sK2,X0,X0) != iProver_top
% 3.32/0.99      | m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) != iProver_top
% 3.32/0.99      | v1_funct_1(k2_funct_2(X0,sK2)) = iProver_top
% 3.32/0.99      | v1_funct_1(sK2) != iProver_top ),
% 3.32/0.99      inference(predicate_to_equality,[status(thm)],[c_1514]) ).
% 3.32/0.99  
% 3.32/0.99  cnf(c_1517,plain,
% 3.32/0.99      ( v1_funct_2(sK2,sK0,sK0) != iProver_top
% 3.32/0.99      | v3_funct_2(sK2,sK0,sK0) != iProver_top
% 3.32/0.99      | m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) != iProver_top
% 3.32/0.99      | v1_funct_1(k2_funct_2(sK0,sK2)) = iProver_top
% 3.32/0.99      | v1_funct_1(sK2) != iProver_top ),
% 3.32/0.99      inference(instantiation,[status(thm)],[c_1515]) ).
% 3.32/0.99  
% 3.32/0.99  cnf(c_3443,plain,
% 3.32/0.99      ( v1_funct_1(k2_funct_2(sK0,sK2)) = iProver_top ),
% 3.32/0.99      inference(global_propositional_subsumption,
% 3.32/0.99                [status(thm)],
% 3.32/0.99                [c_3293,c_33,c_34,c_35,c_36,c_1517]) ).
% 3.32/0.99  
% 3.32/0.99  cnf(c_3447,plain,
% 3.32/0.99      ( v1_funct_1(k2_funct_1(sK2)) = iProver_top ),
% 3.32/0.99      inference(light_normalisation,[status(thm)],[c_3443,c_3346]) ).
% 3.32/0.99  
% 3.32/0.99  cnf(c_23,plain,
% 3.32/0.99      ( ~ v1_funct_2(X0,X1,X1)
% 3.32/0.99      | ~ v3_funct_2(X0,X1,X1)
% 3.32/0.99      | v3_funct_2(k2_funct_2(X1,X0),X1,X1)
% 3.32/0.99      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X1)))
% 3.32/0.99      | ~ v1_funct_1(X0) ),
% 3.32/0.99      inference(cnf_transformation,[],[f75]) ).
% 3.32/0.99  
% 3.32/0.99  cnf(c_1207,plain,
% 3.32/0.99      ( v1_funct_2(X0,X1,X1) != iProver_top
% 3.32/0.99      | v3_funct_2(X0,X1,X1) != iProver_top
% 3.32/0.99      | v3_funct_2(k2_funct_2(X1,X0),X1,X1) = iProver_top
% 3.32/0.99      | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X1))) != iProver_top
% 3.32/0.99      | v1_funct_1(X0) != iProver_top ),
% 3.32/0.99      inference(predicate_to_equality,[status(thm)],[c_23]) ).
% 3.32/0.99  
% 3.32/0.99  cnf(c_3746,plain,
% 3.32/0.99      ( v1_funct_2(sK2,sK0,sK0) != iProver_top
% 3.32/0.99      | v3_funct_2(k2_funct_2(sK0,sK2),sK0,sK0) = iProver_top
% 3.32/0.99      | v3_funct_2(sK2,sK0,sK0) != iProver_top
% 3.32/0.99      | v1_funct_1(sK2) != iProver_top ),
% 3.32/0.99      inference(superposition,[status(thm)],[c_1202,c_1207]) ).
% 3.32/0.99  
% 3.32/0.99  cnf(c_3747,plain,
% 3.32/0.99      ( v1_funct_2(sK2,sK0,sK0) != iProver_top
% 3.32/0.99      | v3_funct_2(k2_funct_1(sK2),sK0,sK0) = iProver_top
% 3.32/0.99      | v3_funct_2(sK2,sK0,sK0) != iProver_top
% 3.32/0.99      | v1_funct_1(sK2) != iProver_top ),
% 3.32/0.99      inference(light_normalisation,[status(thm)],[c_3746,c_3346]) ).
% 3.32/0.99  
% 3.32/0.99  cnf(c_5806,plain,
% 3.32/0.99      ( k2_relat_1(k2_funct_1(sK2)) = sK0 ),
% 3.32/0.99      inference(global_propositional_subsumption,
% 3.32/0.99                [status(thm)],
% 3.32/0.99                [c_4579,c_33,c_34,c_35,c_98,c_3447,c_3747,c_4576]) ).
% 3.32/0.99  
% 3.32/0.99  cnf(c_18,plain,
% 3.32/0.99      ( ~ v3_funct_2(X0,X1,X2)
% 3.32/0.99      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.32/0.99      | v2_funct_1(X0)
% 3.32/0.99      | ~ v1_funct_1(X0) ),
% 3.32/0.99      inference(cnf_transformation,[],[f69]) ).
% 3.32/0.99  
% 3.32/0.99  cnf(c_1209,plain,
% 3.32/0.99      ( v3_funct_2(X0,X1,X2) != iProver_top
% 3.32/0.99      | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) != iProver_top
% 3.32/0.99      | v2_funct_1(X0) = iProver_top
% 3.32/0.99      | v1_funct_1(X0) != iProver_top ),
% 3.32/0.99      inference(predicate_to_equality,[status(thm)],[c_18]) ).
% 3.32/0.99  
% 3.32/0.99  cnf(c_2611,plain,
% 3.32/0.99      ( v3_funct_2(sK2,sK0,sK0) != iProver_top
% 3.32/0.99      | v2_funct_1(sK2) = iProver_top
% 3.32/0.99      | v1_funct_1(sK2) != iProver_top ),
% 3.32/0.99      inference(superposition,[status(thm)],[c_1202,c_1209]) ).
% 3.32/0.99  
% 3.32/0.99  cnf(c_1480,plain,
% 3.32/0.99      ( ~ v3_funct_2(sK2,X0,X1)
% 3.32/0.99      | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
% 3.32/0.99      | v2_funct_1(sK2)
% 3.32/0.99      | ~ v1_funct_1(sK2) ),
% 3.32/0.99      inference(instantiation,[status(thm)],[c_18]) ).
% 3.32/0.99  
% 3.32/0.99  cnf(c_1481,plain,
% 3.32/0.99      ( v3_funct_2(sK2,X0,X1) != iProver_top
% 3.32/0.99      | m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top
% 3.32/0.99      | v2_funct_1(sK2) = iProver_top
% 3.32/0.99      | v1_funct_1(sK2) != iProver_top ),
% 3.32/0.99      inference(predicate_to_equality,[status(thm)],[c_1480]) ).
% 3.32/0.99  
% 3.32/0.99  cnf(c_1483,plain,
% 3.32/0.99      ( v3_funct_2(sK2,sK0,sK0) != iProver_top
% 3.32/0.99      | m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) != iProver_top
% 3.32/0.99      | v2_funct_1(sK2) = iProver_top
% 3.32/0.99      | v1_funct_1(sK2) != iProver_top ),
% 3.32/0.99      inference(instantiation,[status(thm)],[c_1481]) ).
% 3.32/0.99  
% 3.32/0.99  cnf(c_2754,plain,
% 3.32/0.99      ( v2_funct_1(sK2) = iProver_top ),
% 3.32/0.99      inference(global_propositional_subsumption,
% 3.32/0.99                [status(thm)],
% 3.32/0.99                [c_2611,c_33,c_35,c_36,c_1483]) ).
% 3.32/0.99  
% 3.32/0.99  cnf(c_1,plain,
% 3.32/0.99      ( r1_tarski(X0,X0) ),
% 3.32/0.99      inference(cnf_transformation,[],[f84]) ).
% 3.32/0.99  
% 3.32/0.99  cnf(c_1220,plain,
% 3.32/0.99      ( r1_tarski(X0,X0) = iProver_top ),
% 3.32/0.99      inference(predicate_to_equality,[status(thm)],[c_1]) ).
% 3.32/0.99  
% 3.32/0.99  cnf(c_12,plain,
% 3.32/0.99      ( ~ r1_tarski(X0,k1_relat_1(X1))
% 3.32/0.99      | ~ v2_funct_1(X1)
% 3.32/0.99      | ~ v1_funct_1(X1)
% 3.32/0.99      | ~ v1_relat_1(X1)
% 3.32/0.99      | k9_relat_1(k2_funct_1(X1),k9_relat_1(X1,X0)) = X0 ),
% 3.32/0.99      inference(cnf_transformation,[],[f63]) ).
% 3.32/0.99  
% 3.32/0.99  cnf(c_1212,plain,
% 3.32/0.99      ( k9_relat_1(k2_funct_1(X0),k9_relat_1(X0,X1)) = X1
% 3.32/0.99      | r1_tarski(X1,k1_relat_1(X0)) != iProver_top
% 3.32/0.99      | v2_funct_1(X0) != iProver_top
% 3.32/0.99      | v1_funct_1(X0) != iProver_top
% 3.32/0.99      | v1_relat_1(X0) != iProver_top ),
% 3.32/0.99      inference(predicate_to_equality,[status(thm)],[c_12]) ).
% 3.32/0.99  
% 3.32/0.99  cnf(c_3283,plain,
% 3.32/0.99      ( k9_relat_1(k2_funct_1(X0),k9_relat_1(X0,k1_relat_1(X0))) = k1_relat_1(X0)
% 3.32/0.99      | v2_funct_1(X0) != iProver_top
% 3.32/0.99      | v1_funct_1(X0) != iProver_top
% 3.32/0.99      | v1_relat_1(X0) != iProver_top ),
% 3.32/0.99      inference(superposition,[status(thm)],[c_1220,c_1212]) ).
% 3.32/0.99  
% 3.32/0.99  cnf(c_6594,plain,
% 3.32/0.99      ( k9_relat_1(k2_funct_1(sK2),k9_relat_1(sK2,k1_relat_1(sK2))) = k1_relat_1(sK2)
% 3.32/0.99      | v1_funct_1(sK2) != iProver_top
% 3.32/0.99      | v1_relat_1(sK2) != iProver_top ),
% 3.32/0.99      inference(superposition,[status(thm)],[c_2754,c_3283]) ).
% 3.32/0.99  
% 3.32/0.99  cnf(c_1597,plain,
% 3.32/0.99      ( k2_relat_1(sK2) = sK0
% 3.32/0.99      | v3_funct_2(sK2,sK0,sK0) != iProver_top
% 3.32/0.99      | v1_funct_1(sK2) != iProver_top
% 3.32/0.99      | v1_relat_1(sK2) != iProver_top ),
% 3.32/0.99      inference(superposition,[status(thm)],[c_1202,c_1197]) ).
% 3.32/0.99  
% 3.32/0.99  cnf(c_97,plain,
% 3.32/0.99      ( v1_relat_1(k2_zfmisc_1(sK0,sK0)) ),
% 3.32/0.99      inference(instantiation,[status(thm)],[c_6]) ).
% 3.32/0.99  
% 3.32/0.99  cnf(c_1598,plain,
% 3.32/0.99      ( ~ v3_funct_2(sK2,sK0,sK0)
% 3.32/0.99      | ~ v1_funct_1(sK2)
% 3.32/0.99      | ~ v1_relat_1(sK2)
% 3.32/0.99      | k2_relat_1(sK2) = sK0 ),
% 3.32/0.99      inference(predicate_to_equality_rev,[status(thm)],[c_1597]) ).
% 3.32/0.99  
% 3.32/0.99  cnf(c_1432,plain,
% 3.32/0.99      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.32/0.99      | v1_relat_1(X0)
% 3.32/0.99      | ~ v1_relat_1(k2_zfmisc_1(X1,X2)) ),
% 3.32/0.99      inference(instantiation,[status(thm)],[c_3]) ).
% 3.32/0.99  
% 3.32/0.99  cnf(c_1612,plain,
% 3.32/0.99      ( ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
% 3.32/0.99      | ~ v1_relat_1(k2_zfmisc_1(sK0,sK0))
% 3.32/0.99      | v1_relat_1(sK2) ),
% 3.32/0.99      inference(instantiation,[status(thm)],[c_1432]) ).
% 3.32/0.99  
% 3.32/0.99  cnf(c_1995,plain,
% 3.32/0.99      ( k2_relat_1(sK2) = sK0 ),
% 3.32/0.99      inference(global_propositional_subsumption,
% 3.32/0.99                [status(thm)],
% 3.32/0.99                [c_1597,c_32,c_30,c_29,c_97,c_1598,c_1612]) ).
% 3.32/0.99  
% 3.32/0.99  cnf(c_10,plain,
% 3.32/0.99      ( ~ r1_tarski(X0,k2_relat_1(X1))
% 3.32/0.99      | ~ v1_funct_1(X1)
% 3.32/0.99      | ~ v1_relat_1(X1)
% 3.32/0.99      | k9_relat_1(X1,k10_relat_1(X1,X0)) = X0 ),
% 3.32/0.99      inference(cnf_transformation,[],[f61]) ).
% 3.32/0.99  
% 3.32/0.99  cnf(c_1214,plain,
% 3.32/0.99      ( k9_relat_1(X0,k10_relat_1(X0,X1)) = X1
% 3.32/0.99      | r1_tarski(X1,k2_relat_1(X0)) != iProver_top
% 3.32/0.99      | v1_funct_1(X0) != iProver_top
% 3.32/0.99      | v1_relat_1(X0) != iProver_top ),
% 3.32/0.99      inference(predicate_to_equality,[status(thm)],[c_10]) ).
% 3.32/0.99  
% 3.32/0.99  cnf(c_2562,plain,
% 3.32/0.99      ( k9_relat_1(sK2,k10_relat_1(sK2,X0)) = X0
% 3.32/0.99      | r1_tarski(X0,sK0) != iProver_top
% 3.32/0.99      | v1_funct_1(sK2) != iProver_top
% 3.32/0.99      | v1_relat_1(sK2) != iProver_top ),
% 3.32/0.99      inference(superposition,[status(thm)],[c_1995,c_1214]) ).
% 3.32/0.99  
% 3.32/0.99  cnf(c_1613,plain,
% 3.32/0.99      ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) != iProver_top
% 3.32/0.99      | v1_relat_1(k2_zfmisc_1(sK0,sK0)) != iProver_top
% 3.32/0.99      | v1_relat_1(sK2) = iProver_top ),
% 3.32/0.99      inference(predicate_to_equality,[status(thm)],[c_1612]) ).
% 3.32/0.99  
% 3.32/0.99  cnf(c_3588,plain,
% 3.32/0.99      ( k9_relat_1(sK2,k10_relat_1(sK2,X0)) = X0
% 3.32/0.99      | r1_tarski(X0,sK0) != iProver_top ),
% 3.32/0.99      inference(global_propositional_subsumption,
% 3.32/0.99                [status(thm)],
% 3.32/0.99                [c_2562,c_33,c_36,c_98,c_1613]) ).
% 3.32/0.99  
% 3.32/0.99  cnf(c_3596,plain,
% 3.32/0.99      ( k9_relat_1(sK2,k10_relat_1(sK2,sK0)) = sK0 ),
% 3.32/0.99      inference(superposition,[status(thm)],[c_1220,c_3588]) ).
% 3.32/0.99  
% 3.32/0.99  cnf(c_1881,plain,
% 3.32/0.99      ( v1_relat_1(k2_zfmisc_1(sK0,sK0)) != iProver_top
% 3.32/0.99      | v1_relat_1(sK2) = iProver_top ),
% 3.32/0.99      inference(superposition,[status(thm)],[c_1202,c_1219]) ).
% 3.32/0.99  
% 3.32/0.99  cnf(c_1982,plain,
% 3.32/0.99      ( v1_relat_1(sK2) = iProver_top ),
% 3.32/0.99      inference(global_propositional_subsumption,
% 3.32/0.99                [status(thm)],
% 3.32/0.99                [c_1881,c_36,c_98,c_1613]) ).
% 3.32/0.99  
% 3.32/0.99  cnf(c_8,plain,
% 3.32/0.99      ( ~ v1_relat_1(X0)
% 3.32/0.99      | k10_relat_1(X0,k2_relat_1(X0)) = k1_relat_1(X0) ),
% 3.32/0.99      inference(cnf_transformation,[],[f59]) ).
% 3.32/0.99  
% 3.32/0.99  cnf(c_1216,plain,
% 3.32/0.99      ( k10_relat_1(X0,k2_relat_1(X0)) = k1_relat_1(X0)
% 3.32/0.99      | v1_relat_1(X0) != iProver_top ),
% 3.32/0.99      inference(predicate_to_equality,[status(thm)],[c_8]) ).
% 3.32/0.99  
% 3.32/0.99  cnf(c_1988,plain,
% 3.32/0.99      ( k10_relat_1(sK2,k2_relat_1(sK2)) = k1_relat_1(sK2) ),
% 3.32/0.99      inference(superposition,[status(thm)],[c_1982,c_1216]) ).
% 3.32/0.99  
% 3.32/0.99  cnf(c_2062,plain,
% 3.32/0.99      ( k10_relat_1(sK2,sK0) = k1_relat_1(sK2) ),
% 3.32/0.99      inference(light_normalisation,[status(thm)],[c_1988,c_1995]) ).
% 3.32/0.99  
% 3.32/0.99  cnf(c_3604,plain,
% 3.32/0.99      ( k9_relat_1(sK2,k1_relat_1(sK2)) = sK0 ),
% 3.32/0.99      inference(light_normalisation,[status(thm)],[c_3596,c_2062]) ).
% 3.32/0.99  
% 3.32/0.99  cnf(c_6605,plain,
% 3.32/0.99      ( k9_relat_1(k2_funct_1(sK2),sK0) = k1_relat_1(sK2)
% 3.32/0.99      | v1_funct_1(sK2) != iProver_top
% 3.32/0.99      | v1_relat_1(sK2) != iProver_top ),
% 3.32/0.99      inference(light_normalisation,[status(thm)],[c_6594,c_3604]) ).
% 3.32/0.99  
% 3.32/0.99  cnf(c_6777,plain,
% 3.32/0.99      ( k9_relat_1(k2_funct_1(sK2),sK0) = k1_relat_1(sK2) ),
% 3.32/0.99      inference(global_propositional_subsumption,
% 3.32/0.99                [status(thm)],
% 3.32/0.99                [c_6605,c_33,c_36,c_98,c_1613]) ).
% 3.32/0.99  
% 3.32/0.99  cnf(c_7986,plain,
% 3.32/0.99      ( k1_relat_1(sK2) = sK0 ),
% 3.32/0.99      inference(light_normalisation,[status(thm)],[c_5449,c_5806,c_6777]) ).
% 3.32/0.99  
% 3.32/0.99  cnf(c_11,plain,
% 3.32/0.99      ( ~ r1_tarski(X0,k1_relat_1(X1))
% 3.32/0.99      | ~ v2_funct_1(X1)
% 3.32/0.99      | ~ v1_funct_1(X1)
% 3.32/0.99      | ~ v1_relat_1(X1)
% 3.32/0.99      | k10_relat_1(X1,k9_relat_1(X1,X0)) = X0 ),
% 3.32/0.99      inference(cnf_transformation,[],[f62]) ).
% 3.32/0.99  
% 3.32/0.99  cnf(c_1213,plain,
% 3.32/0.99      ( k10_relat_1(X0,k9_relat_1(X0,X1)) = X1
% 3.32/0.99      | r1_tarski(X1,k1_relat_1(X0)) != iProver_top
% 3.32/0.99      | v2_funct_1(X0) != iProver_top
% 3.32/0.99      | v1_funct_1(X0) != iProver_top
% 3.32/0.99      | v1_relat_1(X0) != iProver_top ),
% 3.32/0.99      inference(predicate_to_equality,[status(thm)],[c_11]) ).
% 3.32/0.99  
% 3.32/0.99  cnf(c_8014,plain,
% 3.32/0.99      ( k10_relat_1(sK2,k9_relat_1(sK2,X0)) = X0
% 3.32/0.99      | r1_tarski(X0,sK0) != iProver_top
% 3.32/0.99      | v2_funct_1(sK2) != iProver_top
% 3.32/0.99      | v1_funct_1(sK2) != iProver_top
% 3.32/0.99      | v1_relat_1(sK2) != iProver_top ),
% 3.32/0.99      inference(superposition,[status(thm)],[c_7986,c_1213]) ).
% 3.32/0.99  
% 3.32/0.99  cnf(c_9394,plain,
% 3.32/0.99      ( r1_tarski(X0,sK0) != iProver_top
% 3.32/0.99      | k10_relat_1(sK2,k9_relat_1(sK2,X0)) = X0 ),
% 3.32/0.99      inference(global_propositional_subsumption,
% 3.32/0.99                [status(thm)],
% 3.32/0.99                [c_8014,c_33,c_35,c_36,c_98,c_1483,c_1613]) ).
% 3.32/0.99  
% 3.32/0.99  cnf(c_9395,plain,
% 3.32/0.99      ( k10_relat_1(sK2,k9_relat_1(sK2,X0)) = X0
% 3.32/0.99      | r1_tarski(X0,sK0) != iProver_top ),
% 3.32/0.99      inference(renaming,[status(thm)],[c_9394]) ).
% 3.32/0.99  
% 3.32/0.99  cnf(c_9403,plain,
% 3.32/0.99      ( k10_relat_1(sK2,k9_relat_1(sK2,sK1)) = sK1 ),
% 3.32/0.99      inference(superposition,[status(thm)],[c_1203,c_9395]) ).
% 3.32/0.99  
% 3.32/0.99  cnf(c_3597,plain,
% 3.32/0.99      ( k9_relat_1(sK2,k10_relat_1(sK2,sK1)) = sK1 ),
% 3.32/0.99      inference(superposition,[status(thm)],[c_1203,c_3588]) ).
% 3.32/0.99  
% 3.32/0.99  cnf(c_16,plain,
% 3.32/0.99      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.32/0.99      | k8_relset_1(X1,X2,X0,X3) = k10_relat_1(X0,X3) ),
% 3.32/0.99      inference(cnf_transformation,[],[f67]) ).
% 3.32/0.99  
% 3.32/0.99  cnf(c_1210,plain,
% 3.32/0.99      ( k8_relset_1(X0,X1,X2,X3) = k10_relat_1(X2,X3)
% 3.32/0.99      | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
% 3.32/0.99      inference(predicate_to_equality,[status(thm)],[c_16]) ).
% 3.32/0.99  
% 3.32/0.99  cnf(c_2341,plain,
% 3.32/0.99      ( k8_relset_1(sK0,sK0,sK2,X0) = k10_relat_1(sK2,X0) ),
% 3.32/0.99      inference(superposition,[status(thm)],[c_1202,c_1210]) ).
% 3.32/0.99  
% 3.32/0.99  cnf(c_27,negated_conjecture,
% 3.32/0.99      ( k8_relset_1(sK0,sK0,sK2,k7_relset_1(sK0,sK0,sK2,sK1)) != sK1
% 3.32/0.99      | k7_relset_1(sK0,sK0,sK2,k8_relset_1(sK0,sK0,sK2,sK1)) != sK1 ),
% 3.32/0.99      inference(cnf_transformation,[],[f83]) ).
% 3.32/0.99  
% 3.32/0.99  cnf(c_2661,plain,
% 3.32/0.99      ( k7_relset_1(sK0,sK0,sK2,k8_relset_1(sK0,sK0,sK2,sK1)) != sK1
% 3.32/0.99      | k10_relat_1(sK2,k7_relset_1(sK0,sK0,sK2,sK1)) != sK1 ),
% 3.32/0.99      inference(demodulation,[status(thm)],[c_2341,c_27]) ).
% 3.32/0.99  
% 3.32/0.99  cnf(c_2662,plain,
% 3.32/0.99      ( k7_relset_1(sK0,sK0,sK2,k10_relat_1(sK2,sK1)) != sK1
% 3.32/0.99      | k10_relat_1(sK2,k7_relset_1(sK0,sK0,sK2,sK1)) != sK1 ),
% 3.32/0.99      inference(demodulation,[status(thm)],[c_2661,c_2341]) ).
% 3.32/0.99  
% 3.32/0.99  cnf(c_15,plain,
% 3.32/0.99      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.32/0.99      | k7_relset_1(X1,X2,X0,X3) = k9_relat_1(X0,X3) ),
% 3.32/0.99      inference(cnf_transformation,[],[f66]) ).
% 3.32/0.99  
% 3.32/0.99  cnf(c_1211,plain,
% 3.32/0.99      ( k7_relset_1(X0,X1,X2,X3) = k9_relat_1(X2,X3)
% 3.32/0.99      | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
% 3.32/0.99      inference(predicate_to_equality,[status(thm)],[c_15]) ).
% 3.32/0.99  
% 3.32/0.99  cnf(c_2437,plain,
% 3.32/0.99      ( k7_relset_1(sK0,sK0,sK2,X0) = k9_relat_1(sK2,X0) ),
% 3.32/0.99      inference(superposition,[status(thm)],[c_1202,c_1211]) ).
% 3.32/0.99  
% 3.32/0.99  cnf(c_2847,plain,
% 3.32/0.99      ( k10_relat_1(sK2,k9_relat_1(sK2,sK1)) != sK1
% 3.32/0.99      | k9_relat_1(sK2,k10_relat_1(sK2,sK1)) != sK1 ),
% 3.32/0.99      inference(demodulation,[status(thm)],[c_2662,c_2437]) ).
% 3.32/0.99  
% 3.32/0.99  cnf(contradiction,plain,
% 3.32/0.99      ( $false ),
% 3.32/0.99      inference(minisat,[status(thm)],[c_9403,c_3597,c_2847]) ).
% 3.32/0.99  
% 3.32/0.99  
% 3.32/0.99  % SZS output end CNFRefutation for theBenchmark.p
% 3.32/0.99  
% 3.32/0.99  ------                               Statistics
% 3.32/0.99  
% 3.32/0.99  ------ General
% 3.32/0.99  
% 3.32/0.99  abstr_ref_over_cycles:                  0
% 3.32/0.99  abstr_ref_under_cycles:                 0
% 3.32/0.99  gc_basic_clause_elim:                   0
% 3.32/0.99  forced_gc_time:                         0
% 3.32/0.99  parsing_time:                           0.011
% 3.32/0.99  unif_index_cands_time:                  0.
% 3.32/0.99  unif_index_add_time:                    0.
% 3.32/0.99  orderings_time:                         0.
% 3.32/0.99  out_proof_time:                         0.014
% 3.32/0.99  total_time:                             0.293
% 3.32/0.99  num_of_symbols:                         55
% 3.32/0.99  num_of_terms:                           13967
% 3.32/0.99  
% 3.32/0.99  ------ Preprocessing
% 3.32/0.99  
% 3.32/0.99  num_of_splits:                          0
% 3.32/0.99  num_of_split_atoms:                     0
% 3.32/0.99  num_of_reused_defs:                     0
% 3.32/0.99  num_eq_ax_congr_red:                    28
% 3.32/0.99  num_of_sem_filtered_clauses:            1
% 3.32/0.99  num_of_subtypes:                        0
% 3.32/0.99  monotx_restored_types:                  0
% 3.32/0.99  sat_num_of_epr_types:                   0
% 3.32/0.99  sat_num_of_non_cyclic_types:            0
% 3.32/0.99  sat_guarded_non_collapsed_types:        0
% 3.32/0.99  num_pure_diseq_elim:                    0
% 3.32/0.99  simp_replaced_by:                       0
% 3.32/0.99  res_preprocessed:                       140
% 3.32/0.99  prep_upred:                             0
% 3.32/0.99  prep_unflattend:                        10
% 3.32/0.99  smt_new_axioms:                         0
% 3.32/0.99  pred_elim_cands:                        7
% 3.32/0.99  pred_elim:                              3
% 3.32/0.99  pred_elim_cl:                           5
% 3.32/0.99  pred_elim_cycles:                       6
% 3.32/0.99  merged_defs:                            0
% 3.32/0.99  merged_defs_ncl:                        0
% 3.32/0.99  bin_hyper_res:                          0
% 3.32/0.99  prep_cycles:                            4
% 3.32/0.99  pred_elim_time:                         0.003
% 3.32/0.99  splitting_time:                         0.
% 3.32/0.99  sem_filter_time:                        0.
% 3.32/0.99  monotx_time:                            0.
% 3.32/0.99  subtype_inf_time:                       0.
% 3.32/0.99  
% 3.32/0.99  ------ Problem properties
% 3.32/0.99  
% 3.32/0.99  clauses:                                26
% 3.32/0.99  conjectures:                            6
% 3.32/0.99  epr:                                    6
% 3.32/0.99  horn:                                   26
% 3.32/0.99  ground:                                 6
% 3.32/0.99  unary:                                  7
% 3.32/0.99  binary:                                 5
% 3.32/0.99  lits:                                   77
% 3.32/0.99  lits_eq:                                13
% 3.32/0.99  fd_pure:                                0
% 3.32/0.99  fd_pseudo:                              0
% 3.32/0.99  fd_cond:                                0
% 3.32/0.99  fd_pseudo_cond:                         2
% 3.32/0.99  ac_symbols:                             0
% 3.32/0.99  
% 3.32/0.99  ------ Propositional Solver
% 3.32/0.99  
% 3.32/0.99  prop_solver_calls:                      28
% 3.32/0.99  prop_fast_solver_calls:                 1255
% 3.32/0.99  smt_solver_calls:                       0
% 3.32/0.99  smt_fast_solver_calls:                  0
% 3.32/0.99  prop_num_of_clauses:                    4302
% 3.32/0.99  prop_preprocess_simplified:             9857
% 3.32/0.99  prop_fo_subsumed:                       76
% 3.32/0.99  prop_solver_time:                       0.
% 3.32/0.99  smt_solver_time:                        0.
% 3.32/0.99  smt_fast_solver_time:                   0.
% 3.32/0.99  prop_fast_solver_time:                  0.
% 3.32/0.99  prop_unsat_core_time:                   0.
% 3.32/0.99  
% 3.32/0.99  ------ QBF
% 3.32/0.99  
% 3.32/0.99  qbf_q_res:                              0
% 3.32/0.99  qbf_num_tautologies:                    0
% 3.32/0.99  qbf_prep_cycles:                        0
% 3.32/0.99  
% 3.32/0.99  ------ BMC1
% 3.32/0.99  
% 3.32/0.99  bmc1_current_bound:                     -1
% 3.32/0.99  bmc1_last_solved_bound:                 -1
% 3.32/0.99  bmc1_unsat_core_size:                   -1
% 3.32/0.99  bmc1_unsat_core_parents_size:           -1
% 3.32/0.99  bmc1_merge_next_fun:                    0
% 3.32/0.99  bmc1_unsat_core_clauses_time:           0.
% 3.32/0.99  
% 3.32/0.99  ------ Instantiation
% 3.32/0.99  
% 3.32/0.99  inst_num_of_clauses:                    1158
% 3.32/0.99  inst_num_in_passive:                    141
% 3.32/0.99  inst_num_in_active:                     575
% 3.32/0.99  inst_num_in_unprocessed:                442
% 3.32/0.99  inst_num_of_loops:                      590
% 3.32/0.99  inst_num_of_learning_restarts:          0
% 3.32/0.99  inst_num_moves_active_passive:          12
% 3.32/0.99  inst_lit_activity:                      0
% 3.32/0.99  inst_lit_activity_moves:                0
% 3.32/0.99  inst_num_tautologies:                   0
% 3.32/0.99  inst_num_prop_implied:                  0
% 3.32/0.99  inst_num_existing_simplified:           0
% 3.32/0.99  inst_num_eq_res_simplified:             0
% 3.32/1.00  inst_num_child_elim:                    0
% 3.32/1.00  inst_num_of_dismatching_blockings:      320
% 3.32/1.00  inst_num_of_non_proper_insts:           1007
% 3.32/1.00  inst_num_of_duplicates:                 0
% 3.32/1.00  inst_inst_num_from_inst_to_res:         0
% 3.32/1.00  inst_dismatching_checking_time:         0.
% 3.32/1.00  
% 3.32/1.00  ------ Resolution
% 3.32/1.00  
% 3.32/1.00  res_num_of_clauses:                     0
% 3.32/1.00  res_num_in_passive:                     0
% 3.32/1.00  res_num_in_active:                      0
% 3.32/1.00  res_num_of_loops:                       144
% 3.32/1.00  res_forward_subset_subsumed:            58
% 3.32/1.00  res_backward_subset_subsumed:           0
% 3.32/1.00  res_forward_subsumed:                   0
% 3.32/1.00  res_backward_subsumed:                  0
% 3.32/1.00  res_forward_subsumption_resolution:     1
% 3.32/1.00  res_backward_subsumption_resolution:    0
% 3.32/1.00  res_clause_to_clause_subsumption:       240
% 3.32/1.00  res_orphan_elimination:                 0
% 3.32/1.00  res_tautology_del:                      53
% 3.32/1.00  res_num_eq_res_simplified:              0
% 3.32/1.00  res_num_sel_changes:                    0
% 3.32/1.00  res_moves_from_active_to_pass:          0
% 3.32/1.00  
% 3.32/1.00  ------ Superposition
% 3.32/1.00  
% 3.32/1.00  sup_time_total:                         0.
% 3.32/1.00  sup_time_generating:                    0.
% 3.32/1.00  sup_time_sim_full:                      0.
% 3.32/1.00  sup_time_sim_immed:                     0.
% 3.32/1.00  
% 3.32/1.00  sup_num_of_clauses:                     132
% 3.32/1.00  sup_num_in_active:                      101
% 3.32/1.00  sup_num_in_passive:                     31
% 3.32/1.00  sup_num_of_loops:                       117
% 3.32/1.00  sup_fw_superposition:                   70
% 3.32/1.00  sup_bw_superposition:                   71
% 3.32/1.00  sup_immediate_simplified:               32
% 3.32/1.00  sup_given_eliminated:                   0
% 3.32/1.00  comparisons_done:                       0
% 3.32/1.00  comparisons_avoided:                    0
% 3.32/1.00  
% 3.32/1.00  ------ Simplifications
% 3.32/1.00  
% 3.32/1.00  
% 3.32/1.00  sim_fw_subset_subsumed:                 2
% 3.32/1.00  sim_bw_subset_subsumed:                 1
% 3.32/1.00  sim_fw_subsumed:                        2
% 3.32/1.00  sim_bw_subsumed:                        0
% 3.32/1.00  sim_fw_subsumption_res:                 1
% 3.32/1.00  sim_bw_subsumption_res:                 0
% 3.32/1.00  sim_tautology_del:                      0
% 3.32/1.00  sim_eq_tautology_del:                   13
% 3.32/1.00  sim_eq_res_simp:                        1
% 3.32/1.00  sim_fw_demodulated:                     2
% 3.32/1.00  sim_bw_demodulated:                     16
% 3.32/1.00  sim_light_normalised:                   40
% 3.32/1.00  sim_joinable_taut:                      0
% 3.32/1.00  sim_joinable_simp:                      0
% 3.32/1.00  sim_ac_normalised:                      0
% 3.32/1.00  sim_smt_subsumption:                    0
% 3.32/1.00  
%------------------------------------------------------------------------------
