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
% DateTime   : Thu Dec  3 12:07:37 EST 2020

% Result     : Theorem 4.03s
% Output     : CNFRefutation 4.03s
% Verified   : 
% Statistics : Number of formulae       :  219 (1875 expanded)
%              Number of clauses        :  137 ( 643 expanded)
%              Number of leaves         :   21 ( 359 expanded)
%              Depth                    :   22
%              Number of atoms          :  682 (9046 expanded)
%              Number of equality atoms :  288 (2608 expanded)
%              Maximal formula depth    :   10 (   4 average)
%              Maximal clause size      :   14 (   3 average)
%              Maximal term depth       :    6 (   2 average)

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

fof(f45,plain,(
    ? [X0,X1,X2] :
      ( ( k8_relset_1(X0,X0,X2,k7_relset_1(X0,X0,X2,X1)) != X1
        | k7_relset_1(X0,X0,X2,k8_relset_1(X0,X0,X2,X1)) != X1 )
      & r1_tarski(X1,X0)
      & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
      & v3_funct_2(X2,X0,X0)
      & v1_funct_2(X2,X0,X0)
      & v1_funct_1(X2) ) ),
    inference(ennf_transformation,[],[f20])).

fof(f46,plain,(
    ? [X0,X1,X2] :
      ( ( k8_relset_1(X0,X0,X2,k7_relset_1(X0,X0,X2,X1)) != X1
        | k7_relset_1(X0,X0,X2,k8_relset_1(X0,X0,X2,X1)) != X1 )
      & r1_tarski(X1,X0)
      & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
      & v3_funct_2(X2,X0,X0)
      & v1_funct_2(X2,X0,X0)
      & v1_funct_1(X2) ) ),
    inference(flattening,[],[f45])).

fof(f51,plain,
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

fof(f52,plain,
    ( ( k8_relset_1(sK0,sK0,sK2,k7_relset_1(sK0,sK0,sK2,sK1)) != sK1
      | k7_relset_1(sK0,sK0,sK2,k8_relset_1(sK0,sK0,sK2,sK1)) != sK1 )
    & r1_tarski(sK1,sK0)
    & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
    & v3_funct_2(sK2,sK0,sK0)
    & v1_funct_2(sK2,sK0,sK0)
    & v1_funct_1(sK2) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f46,f51])).

fof(f84,plain,(
    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) ),
    inference(cnf_transformation,[],[f52])).

fof(f18,axiom,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
        & v3_funct_2(X1,X0,X0)
        & v1_funct_2(X1,X0,X0)
        & v1_funct_1(X1) )
     => k2_funct_1(X1) = k2_funct_2(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f43,plain,(
    ! [X0,X1] :
      ( k2_funct_1(X1) = k2_funct_2(X0,X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
      | ~ v3_funct_2(X1,X0,X0)
      | ~ v1_funct_2(X1,X0,X0)
      | ~ v1_funct_1(X1) ) ),
    inference(ennf_transformation,[],[f18])).

fof(f44,plain,(
    ! [X0,X1] :
      ( k2_funct_1(X1) = k2_funct_2(X0,X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
      | ~ v3_funct_2(X1,X0,X0)
      | ~ v1_funct_2(X1,X0,X0)
      | ~ v1_funct_1(X1) ) ),
    inference(flattening,[],[f43])).

fof(f80,plain,(
    ! [X0,X1] :
      ( k2_funct_1(X1) = k2_funct_2(X0,X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
      | ~ v3_funct_2(X1,X0,X0)
      | ~ v1_funct_2(X1,X0,X0)
      | ~ v1_funct_1(X1) ) ),
    inference(cnf_transformation,[],[f44])).

fof(f81,plain,(
    v1_funct_1(sK2) ),
    inference(cnf_transformation,[],[f52])).

fof(f82,plain,(
    v1_funct_2(sK2,sK0,sK0) ),
    inference(cnf_transformation,[],[f52])).

fof(f83,plain,(
    v3_funct_2(sK2,sK0,sK0) ),
    inference(cnf_transformation,[],[f52])).

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

fof(f41,plain,(
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
    inference(flattening,[],[f41])).

fof(f79,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k2_funct_2(X0,X1),k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
      | ~ v3_funct_2(X1,X0,X0)
      | ~ v1_funct_2(X1,X0,X0)
      | ~ v1_funct_1(X1) ) ),
    inference(cnf_transformation,[],[f42])).

fof(f12,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => ( v5_relat_1(X2,X1)
        & v4_relat_1(X2,X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f34,plain,(
    ! [X0,X1,X2] :
      ( ( v5_relat_1(X2,X1)
        & v4_relat_1(X2,X0) )
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f67,plain,(
    ! [X2,X0,X1] :
      ( v4_relat_1(X2,X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f34])).

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

fof(f49,plain,(
    ! [X0,X1] :
      ( ( ( v4_relat_1(X1,X0)
          | ~ r1_tarski(k1_relat_1(X1),X0) )
        & ( r1_tarski(k1_relat_1(X1),X0)
          | ~ v4_relat_1(X1,X0) ) )
      | ~ v1_relat_1(X1) ) ),
    inference(nnf_transformation,[],[f22])).

fof(f57,plain,(
    ! [X0,X1] :
      ( r1_tarski(k1_relat_1(X1),X0)
      | ~ v4_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f49])).

fof(f4,axiom,(
    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f59,plain,(
    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1)) ),
    inference(cnf_transformation,[],[f4])).

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

fof(f56,plain,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f8,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => k1_relat_1(X0) = k10_relat_1(X0,k2_relat_1(X0)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f27,plain,(
    ! [X0] :
      ( k1_relat_1(X0) = k10_relat_1(X0,k2_relat_1(X0))
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f63,plain,(
    ! [X0] :
      ( k1_relat_1(X0) = k10_relat_1(X0,k2_relat_1(X0))
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f15,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => ( ( v3_funct_2(X2,X0,X1)
          & v1_funct_1(X2) )
       => ( v2_funct_2(X2,X1)
          & v2_funct_1(X2)
          & v1_funct_1(X2) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f37,plain,(
    ! [X0,X1,X2] :
      ( ( v2_funct_2(X2,X1)
        & v2_funct_1(X2)
        & v1_funct_1(X2) )
      | ~ v3_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f15])).

fof(f38,plain,(
    ! [X0,X1,X2] :
      ( ( v2_funct_2(X2,X1)
        & v2_funct_1(X2)
        & v1_funct_1(X2) )
      | ~ v3_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(flattening,[],[f37])).

fof(f73,plain,(
    ! [X2,X0,X1] :
      ( v2_funct_2(X2,X1)
      | ~ v3_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f38])).

fof(f16,axiom,(
    ! [X0,X1] :
      ( ( v5_relat_1(X1,X0)
        & v1_relat_1(X1) )
     => ( v2_funct_2(X1,X0)
      <=> k2_relat_1(X1) = X0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f39,plain,(
    ! [X0,X1] :
      ( ( v2_funct_2(X1,X0)
      <=> k2_relat_1(X1) = X0 )
      | ~ v5_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f16])).

fof(f40,plain,(
    ! [X0,X1] :
      ( ( v2_funct_2(X1,X0)
      <=> k2_relat_1(X1) = X0 )
      | ~ v5_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f39])).

fof(f50,plain,(
    ! [X0,X1] :
      ( ( ( v2_funct_2(X1,X0)
          | k2_relat_1(X1) != X0 )
        & ( k2_relat_1(X1) = X0
          | ~ v2_funct_2(X1,X0) ) )
      | ~ v5_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(nnf_transformation,[],[f40])).

fof(f74,plain,(
    ! [X0,X1] :
      ( k2_relat_1(X1) = X0
      | ~ v2_funct_2(X1,X0)
      | ~ v5_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f50])).

fof(f68,plain,(
    ! [X2,X0,X1] :
      ( v5_relat_1(X2,X1)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f34])).

fof(f72,plain,(
    ! [X2,X0,X1] :
      ( v2_funct_1(X2)
      | ~ v3_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f38])).

fof(f10,axiom,(
    ! [X0,X1] :
      ( ( v1_funct_1(X1)
        & v1_relat_1(X1) )
     => ( v2_funct_1(X1)
       => k9_relat_1(k2_funct_1(X1),X0) = k10_relat_1(X1,X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f30,plain,(
    ! [X0,X1] :
      ( k9_relat_1(k2_funct_1(X1),X0) = k10_relat_1(X1,X0)
      | ~ v2_funct_1(X1)
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f31,plain,(
    ! [X0,X1] :
      ( k9_relat_1(k2_funct_1(X1),X0) = k10_relat_1(X1,X0)
      | ~ v2_funct_1(X1)
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f30])).

fof(f65,plain,(
    ! [X0,X1] :
      ( k9_relat_1(k2_funct_1(X1),X0) = k10_relat_1(X1,X0)
      | ~ v2_funct_1(X1)
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f7,axiom,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
     => ( r1_tarski(X0,X1)
       => r1_tarski(k9_relat_1(X2,X0),k9_relat_1(X2,X1)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f25,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(k9_relat_1(X2,X0),k9_relat_1(X2,X1))
      | ~ r1_tarski(X0,X1)
      | ~ v1_relat_1(X2) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f26,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(k9_relat_1(X2,X0),k9_relat_1(X2,X1))
      | ~ r1_tarski(X0,X1)
      | ~ v1_relat_1(X2) ) ),
    inference(flattening,[],[f25])).

fof(f62,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(k9_relat_1(X2,X0),k9_relat_1(X2,X1))
      | ~ r1_tarski(X0,X1)
      | ~ v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f11,axiom,(
    ! [X0,X1] :
      ( ( v1_funct_1(X1)
        & v1_relat_1(X1) )
     => ( ( v2_funct_1(X1)
          & r1_tarski(X0,k1_relat_1(X1)) )
       => k10_relat_1(X1,k9_relat_1(X1,X0)) = X0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f32,plain,(
    ! [X0,X1] :
      ( k10_relat_1(X1,k9_relat_1(X1,X0)) = X0
      | ~ v2_funct_1(X1)
      | ~ r1_tarski(X0,k1_relat_1(X1))
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f33,plain,(
    ! [X0,X1] :
      ( k10_relat_1(X1,k9_relat_1(X1,X0)) = X0
      | ~ v2_funct_1(X1)
      | ~ r1_tarski(X0,k1_relat_1(X1))
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f32])).

fof(f66,plain,(
    ! [X0,X1] :
      ( k10_relat_1(X1,k9_relat_1(X1,X0)) = X0
      | ~ v2_funct_1(X1)
      | ~ r1_tarski(X0,k1_relat_1(X1))
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f33])).

fof(f76,plain,(
    ! [X0,X1] :
      ( v1_funct_1(k2_funct_2(X0,X1))
      | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
      | ~ v3_funct_2(X1,X0,X0)
      | ~ v1_funct_2(X1,X0,X0)
      | ~ v1_funct_1(X1) ) ),
    inference(cnf_transformation,[],[f42])).

fof(f78,plain,(
    ! [X0,X1] :
      ( v3_funct_2(k2_funct_2(X0,X1),X0,X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
      | ~ v3_funct_2(X1,X0,X0)
      | ~ v1_funct_2(X1,X0,X0)
      | ~ v1_funct_1(X1) ) ),
    inference(cnf_transformation,[],[f42])).

fof(f6,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => k9_relat_1(X0,k1_relat_1(X0)) = k2_relat_1(X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f24,plain,(
    ! [X0] :
      ( k9_relat_1(X0,k1_relat_1(X0)) = k2_relat_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f61,plain,(
    ! [X0] :
      ( k9_relat_1(X0,k1_relat_1(X0)) = k2_relat_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f5,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => r1_tarski(k9_relat_1(X1,X0),k2_relat_1(X1)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f23,plain,(
    ! [X0,X1] :
      ( r1_tarski(k9_relat_1(X1,X0),k2_relat_1(X1))
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f60,plain,(
    ! [X0,X1] :
      ( r1_tarski(k9_relat_1(X1,X0),k2_relat_1(X1))
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( X0 = X1
    <=> ( r1_tarski(X1,X0)
        & r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f47,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(nnf_transformation,[],[f1])).

fof(f48,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(flattening,[],[f47])).

fof(f55,plain,(
    ! [X0,X1] :
      ( X0 = X1
      | ~ r1_tarski(X1,X0)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f48])).

fof(f14,axiom,(
    ! [X0,X1,X2,X3] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k10_relat_1(X2,X3) = k8_relset_1(X0,X1,X2,X3) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f36,plain,(
    ! [X0,X1,X2,X3] :
      ( k10_relat_1(X2,X3) = k8_relset_1(X0,X1,X2,X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f70,plain,(
    ! [X2,X0,X3,X1] :
      ( k10_relat_1(X2,X3) = k8_relset_1(X0,X1,X2,X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f36])).

fof(f86,plain,
    ( k8_relset_1(sK0,sK0,sK2,k7_relset_1(sK0,sK0,sK2,sK1)) != sK1
    | k7_relset_1(sK0,sK0,sK2,k8_relset_1(sK0,sK0,sK2,sK1)) != sK1 ),
    inference(cnf_transformation,[],[f52])).

fof(f13,axiom,(
    ! [X0,X1,X2,X3] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k9_relat_1(X2,X3) = k7_relset_1(X0,X1,X2,X3) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f35,plain,(
    ! [X0,X1,X2,X3] :
      ( k9_relat_1(X2,X3) = k7_relset_1(X0,X1,X2,X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f69,plain,(
    ! [X2,X0,X3,X1] :
      ( k9_relat_1(X2,X3) = k7_relset_1(X0,X1,X2,X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f35])).

fof(f9,axiom,(
    ! [X0,X1] :
      ( ( v1_funct_1(X1)
        & v1_relat_1(X1) )
     => ( r1_tarski(X0,k2_relat_1(X1))
       => k9_relat_1(X1,k10_relat_1(X1,X0)) = X0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f28,plain,(
    ! [X0,X1] :
      ( k9_relat_1(X1,k10_relat_1(X1,X0)) = X0
      | ~ r1_tarski(X0,k2_relat_1(X1))
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f29,plain,(
    ! [X0,X1] :
      ( k9_relat_1(X1,k10_relat_1(X1,X0)) = X0
      | ~ r1_tarski(X0,k2_relat_1(X1))
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f28])).

fof(f64,plain,(
    ! [X0,X1] :
      ( k9_relat_1(X1,k10_relat_1(X1,X0)) = X0
      | ~ r1_tarski(X0,k2_relat_1(X1))
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f54,plain,(
    ! [X0,X1] :
      ( r1_tarski(X1,X0)
      | X0 != X1 ) ),
    inference(cnf_transformation,[],[f48])).

fof(f87,plain,(
    ! [X1] : r1_tarski(X1,X1) ),
    inference(equality_resolution,[],[f54])).

fof(f85,plain,(
    r1_tarski(sK1,sK0) ),
    inference(cnf_transformation,[],[f52])).

cnf(c_30,negated_conjecture,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) ),
    inference(cnf_transformation,[],[f84])).

cnf(c_1196,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_30])).

cnf(c_27,plain,
    ( ~ v1_funct_2(X0,X1,X1)
    | ~ v3_funct_2(X0,X1,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X1)))
    | ~ v1_funct_1(X0)
    | k2_funct_2(X1,X0) = k2_funct_1(X0) ),
    inference(cnf_transformation,[],[f80])).

cnf(c_1198,plain,
    ( k2_funct_2(X0,X1) = k2_funct_1(X1)
    | v1_funct_2(X1,X0,X0) != iProver_top
    | v3_funct_2(X1,X0,X0) != iProver_top
    | m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) != iProver_top
    | v1_funct_1(X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_27])).

cnf(c_2726,plain,
    ( k2_funct_2(sK0,sK2) = k2_funct_1(sK2)
    | v1_funct_2(sK2,sK0,sK0) != iProver_top
    | v3_funct_2(sK2,sK0,sK0) != iProver_top
    | v1_funct_1(sK2) != iProver_top ),
    inference(superposition,[status(thm)],[c_1196,c_1198])).

cnf(c_33,negated_conjecture,
    ( v1_funct_1(sK2) ),
    inference(cnf_transformation,[],[f81])).

cnf(c_34,plain,
    ( v1_funct_1(sK2) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_33])).

cnf(c_32,negated_conjecture,
    ( v1_funct_2(sK2,sK0,sK0) ),
    inference(cnf_transformation,[],[f82])).

cnf(c_35,plain,
    ( v1_funct_2(sK2,sK0,sK0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_32])).

cnf(c_31,negated_conjecture,
    ( v3_funct_2(sK2,sK0,sK0) ),
    inference(cnf_transformation,[],[f83])).

cnf(c_36,plain,
    ( v3_funct_2(sK2,sK0,sK0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_31])).

cnf(c_2969,plain,
    ( k2_funct_2(sK0,sK2) = k2_funct_1(sK2) ),
    inference(global_propositional_subsumption,[status(thm)],[c_2726,c_34,c_35,c_36])).

cnf(c_23,plain,
    ( ~ v1_funct_2(X0,X1,X1)
    | ~ v3_funct_2(X0,X1,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X1)))
    | m1_subset_1(k2_funct_2(X1,X0),k1_zfmisc_1(k2_zfmisc_1(X1,X1)))
    | ~ v1_funct_1(X0) ),
    inference(cnf_transformation,[],[f79])).

cnf(c_1202,plain,
    ( v1_funct_2(X0,X1,X1) != iProver_top
    | v3_funct_2(X0,X1,X1) != iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X1))) != iProver_top
    | m1_subset_1(k2_funct_2(X1,X0),k1_zfmisc_1(k2_zfmisc_1(X1,X1))) = iProver_top
    | v1_funct_1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_23])).

cnf(c_3376,plain,
    ( v1_funct_2(sK2,sK0,sK0) != iProver_top
    | v3_funct_2(sK2,sK0,sK0) != iProver_top
    | m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) = iProver_top
    | m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) != iProver_top
    | v1_funct_1(sK2) != iProver_top ),
    inference(superposition,[status(thm)],[c_2969,c_1202])).

cnf(c_37,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_30])).

cnf(c_3872,plain,
    ( m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_3376,c_34,c_35,c_36,c_37])).

cnf(c_15,plain,
    ( v4_relat_1(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) ),
    inference(cnf_transformation,[],[f67])).

cnf(c_5,plain,
    ( ~ v4_relat_1(X0,X1)
    | r1_tarski(k1_relat_1(X0),X1)
    | ~ v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f57])).

cnf(c_363,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | r1_tarski(k1_relat_1(X0),X1)
    | ~ v1_relat_1(X0) ),
    inference(resolution,[status(thm)],[c_15,c_5])).

cnf(c_1192,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) != iProver_top
    | r1_tarski(k1_relat_1(X0),X1) = iProver_top
    | v1_relat_1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_363])).

cnf(c_3881,plain,
    ( r1_tarski(k1_relat_1(k2_funct_1(sK2)),sK0) = iProver_top
    | v1_relat_1(k2_funct_1(sK2)) != iProver_top ),
    inference(superposition,[status(thm)],[c_3872,c_1192])).

cnf(c_6,plain,
    ( v1_relat_1(k2_zfmisc_1(X0,X1)) ),
    inference(cnf_transformation,[],[f59])).

cnf(c_100,plain,
    ( v1_relat_1(k2_zfmisc_1(X0,X1)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_6])).

cnf(c_102,plain,
    ( v1_relat_1(k2_zfmisc_1(sK0,sK0)) = iProver_top ),
    inference(instantiation,[status(thm)],[c_100])).

cnf(c_3,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | ~ v1_relat_1(X1)
    | v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f56])).

cnf(c_1214,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(X1)) != iProver_top
    | v1_relat_1(X1) != iProver_top
    | v1_relat_1(X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3])).

cnf(c_3876,plain,
    ( v1_relat_1(k2_zfmisc_1(sK0,sK0)) != iProver_top
    | v1_relat_1(k2_funct_1(sK2)) = iProver_top ),
    inference(superposition,[status(thm)],[c_3872,c_1214])).

cnf(c_4403,plain,
    ( r1_tarski(k1_relat_1(k2_funct_1(sK2)),sK0) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_3881,c_102,c_3876])).

cnf(c_1958,plain,
    ( v1_relat_1(k2_zfmisc_1(sK0,sK0)) != iProver_top
    | v1_relat_1(sK2) = iProver_top ),
    inference(superposition,[status(thm)],[c_1196,c_1214])).

cnf(c_1377,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | v1_relat_1(X0)
    | ~ v1_relat_1(k2_zfmisc_1(X1,X2)) ),
    inference(instantiation,[status(thm)],[c_3])).

cnf(c_1496,plain,
    ( ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
    | ~ v1_relat_1(k2_zfmisc_1(sK0,sK0))
    | v1_relat_1(sK2) ),
    inference(instantiation,[status(thm)],[c_1377])).

cnf(c_1497,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) != iProver_top
    | v1_relat_1(k2_zfmisc_1(sK0,sK0)) != iProver_top
    | v1_relat_1(sK2) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1496])).

cnf(c_2090,plain,
    ( v1_relat_1(sK2) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_1958,c_37,c_102,c_1497])).

cnf(c_10,plain,
    ( ~ v1_relat_1(X0)
    | k10_relat_1(X0,k2_relat_1(X0)) = k1_relat_1(X0) ),
    inference(cnf_transformation,[],[f63])).

cnf(c_1209,plain,
    ( k10_relat_1(X0,k2_relat_1(X0)) = k1_relat_1(X0)
    | v1_relat_1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_10])).

cnf(c_2095,plain,
    ( k10_relat_1(sK2,k2_relat_1(sK2)) = k1_relat_1(sK2) ),
    inference(superposition,[status(thm)],[c_2090,c_1209])).

cnf(c_18,plain,
    ( ~ v3_funct_2(X0,X1,X2)
    | v2_funct_2(X0,X2)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ v1_funct_1(X0) ),
    inference(cnf_transformation,[],[f73])).

cnf(c_22,plain,
    ( ~ v2_funct_2(X0,X1)
    | ~ v5_relat_1(X0,X1)
    | ~ v1_relat_1(X0)
    | k2_relat_1(X0) = X1 ),
    inference(cnf_transformation,[],[f74])).

cnf(c_421,plain,
    ( ~ v3_funct_2(X0,X1,X2)
    | ~ v5_relat_1(X3,X4)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ v1_funct_1(X0)
    | ~ v1_relat_1(X3)
    | X3 != X0
    | X4 != X2
    | k2_relat_1(X3) = X4 ),
    inference(resolution_lifted,[status(thm)],[c_18,c_22])).

cnf(c_422,plain,
    ( ~ v3_funct_2(X0,X1,X2)
    | ~ v5_relat_1(X0,X2)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ v1_funct_1(X0)
    | ~ v1_relat_1(X0)
    | k2_relat_1(X0) = X2 ),
    inference(unflattening,[status(thm)],[c_421])).

cnf(c_14,plain,
    ( v5_relat_1(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) ),
    inference(cnf_transformation,[],[f68])).

cnf(c_438,plain,
    ( ~ v3_funct_2(X0,X1,X2)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ v1_funct_1(X0)
    | ~ v1_relat_1(X0)
    | k2_relat_1(X0) = X2 ),
    inference(forward_subsumption_resolution,[status(thm)],[c_422,c_14])).

cnf(c_1191,plain,
    ( k2_relat_1(X0) = X1
    | v3_funct_2(X0,X2,X1) != iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) != iProver_top
    | v1_funct_1(X0) != iProver_top
    | v1_relat_1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_438])).

cnf(c_1557,plain,
    ( k2_relat_1(sK2) = sK0
    | v3_funct_2(sK2,sK0,sK0) != iProver_top
    | v1_funct_1(sK2) != iProver_top
    | v1_relat_1(sK2) != iProver_top ),
    inference(superposition,[status(thm)],[c_1196,c_1191])).

cnf(c_1774,plain,
    ( k2_relat_1(sK2) = sK0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_1557,c_34,c_36,c_37,c_102,c_1497])).

cnf(c_2096,plain,
    ( k10_relat_1(sK2,sK0) = k1_relat_1(sK2) ),
    inference(light_normalisation,[status(thm)],[c_2095,c_1774])).

cnf(c_19,plain,
    ( ~ v3_funct_2(X0,X1,X2)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | v2_funct_1(X0)
    | ~ v1_funct_1(X0) ),
    inference(cnf_transformation,[],[f72])).

cnf(c_1203,plain,
    ( v3_funct_2(X0,X1,X2) != iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) != iProver_top
    | v2_funct_1(X0) = iProver_top
    | v1_funct_1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_19])).

cnf(c_2817,plain,
    ( v3_funct_2(sK2,sK0,sK0) != iProver_top
    | v2_funct_1(sK2) = iProver_top
    | v1_funct_1(sK2) != iProver_top ),
    inference(superposition,[status(thm)],[c_1196,c_1203])).

cnf(c_1601,plain,
    ( ~ v3_funct_2(sK2,X0,X1)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
    | v2_funct_1(sK2)
    | ~ v1_funct_1(sK2) ),
    inference(instantiation,[status(thm)],[c_19])).

cnf(c_1602,plain,
    ( v3_funct_2(sK2,X0,X1) != iProver_top
    | m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top
    | v2_funct_1(sK2) = iProver_top
    | v1_funct_1(sK2) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1601])).

cnf(c_1604,plain,
    ( v3_funct_2(sK2,sK0,sK0) != iProver_top
    | m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) != iProver_top
    | v2_funct_1(sK2) = iProver_top
    | v1_funct_1(sK2) != iProver_top ),
    inference(instantiation,[status(thm)],[c_1602])).

cnf(c_2901,plain,
    ( v2_funct_1(sK2) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_2817,c_34,c_36,c_37,c_1604])).

cnf(c_12,plain,
    ( ~ v2_funct_1(X0)
    | ~ v1_funct_1(X0)
    | ~ v1_relat_1(X0)
    | k9_relat_1(k2_funct_1(X0),X1) = k10_relat_1(X0,X1) ),
    inference(cnf_transformation,[],[f65])).

cnf(c_1207,plain,
    ( k9_relat_1(k2_funct_1(X0),X1) = k10_relat_1(X0,X1)
    | v2_funct_1(X0) != iProver_top
    | v1_funct_1(X0) != iProver_top
    | v1_relat_1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_12])).

cnf(c_2905,plain,
    ( k9_relat_1(k2_funct_1(sK2),X0) = k10_relat_1(sK2,X0)
    | v1_funct_1(sK2) != iProver_top
    | v1_relat_1(sK2) != iProver_top ),
    inference(superposition,[status(thm)],[c_2901,c_1207])).

cnf(c_3047,plain,
    ( k9_relat_1(k2_funct_1(sK2),X0) = k10_relat_1(sK2,X0) ),
    inference(global_propositional_subsumption,[status(thm)],[c_2905,c_34,c_37,c_102,c_1497])).

cnf(c_9,plain,
    ( ~ r1_tarski(X0,X1)
    | r1_tarski(k9_relat_1(X2,X0),k9_relat_1(X2,X1))
    | ~ v1_relat_1(X2) ),
    inference(cnf_transformation,[],[f62])).

cnf(c_1210,plain,
    ( r1_tarski(X0,X1) != iProver_top
    | r1_tarski(k9_relat_1(X2,X0),k9_relat_1(X2,X1)) = iProver_top
    | v1_relat_1(X2) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_9])).

cnf(c_3052,plain,
    ( r1_tarski(X0,X1) != iProver_top
    | r1_tarski(k9_relat_1(k2_funct_1(sK2),X0),k10_relat_1(sK2,X1)) = iProver_top
    | v1_relat_1(k2_funct_1(sK2)) != iProver_top ),
    inference(superposition,[status(thm)],[c_3047,c_1210])).

cnf(c_3053,plain,
    ( r1_tarski(X0,X1) != iProver_top
    | r1_tarski(k10_relat_1(sK2,X0),k10_relat_1(sK2,X1)) = iProver_top
    | v1_relat_1(k2_funct_1(sK2)) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_3052,c_3047])).

cnf(c_4629,plain,
    ( r1_tarski(k10_relat_1(sK2,X0),k10_relat_1(sK2,X1)) = iProver_top
    | r1_tarski(X0,X1) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_3053,c_102,c_3876])).

cnf(c_4630,plain,
    ( r1_tarski(X0,X1) != iProver_top
    | r1_tarski(k10_relat_1(sK2,X0),k10_relat_1(sK2,X1)) = iProver_top ),
    inference(renaming,[status(thm)],[c_4629])).

cnf(c_4637,plain,
    ( r1_tarski(X0,sK0) != iProver_top
    | r1_tarski(k10_relat_1(sK2,X0),k1_relat_1(sK2)) = iProver_top ),
    inference(superposition,[status(thm)],[c_2096,c_4630])).

cnf(c_13,plain,
    ( ~ r1_tarski(X0,k1_relat_1(X1))
    | ~ v2_funct_1(X1)
    | ~ v1_funct_1(X1)
    | ~ v1_relat_1(X1)
    | k10_relat_1(X1,k9_relat_1(X1,X0)) = X0 ),
    inference(cnf_transformation,[],[f66])).

cnf(c_1206,plain,
    ( k10_relat_1(X0,k9_relat_1(X0,X1)) = X1
    | r1_tarski(X1,k1_relat_1(X0)) != iProver_top
    | v2_funct_1(X0) != iProver_top
    | v1_funct_1(X0) != iProver_top
    | v1_relat_1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_13])).

cnf(c_4952,plain,
    ( k10_relat_1(sK2,k9_relat_1(sK2,k10_relat_1(sK2,X0))) = k10_relat_1(sK2,X0)
    | r1_tarski(X0,sK0) != iProver_top
    | v2_funct_1(sK2) != iProver_top
    | v1_funct_1(sK2) != iProver_top
    | v1_relat_1(sK2) != iProver_top ),
    inference(superposition,[status(thm)],[c_4637,c_1206])).

cnf(c_9224,plain,
    ( r1_tarski(X0,sK0) != iProver_top
    | k10_relat_1(sK2,k9_relat_1(sK2,k10_relat_1(sK2,X0))) = k10_relat_1(sK2,X0) ),
    inference(global_propositional_subsumption,[status(thm)],[c_4952,c_34,c_36,c_37,c_102,c_1497,c_1604])).

cnf(c_9225,plain,
    ( k10_relat_1(sK2,k9_relat_1(sK2,k10_relat_1(sK2,X0))) = k10_relat_1(sK2,X0)
    | r1_tarski(X0,sK0) != iProver_top ),
    inference(renaming,[status(thm)],[c_9224])).

cnf(c_9234,plain,
    ( k10_relat_1(sK2,k9_relat_1(sK2,k10_relat_1(sK2,k1_relat_1(k2_funct_1(sK2))))) = k10_relat_1(sK2,k1_relat_1(k2_funct_1(sK2))) ),
    inference(superposition,[status(thm)],[c_4403,c_9225])).

cnf(c_3879,plain,
    ( k2_relat_1(k2_funct_1(sK2)) = sK0
    | v3_funct_2(k2_funct_1(sK2),sK0,sK0) != iProver_top
    | v1_funct_1(k2_funct_1(sK2)) != iProver_top
    | v1_relat_1(k2_funct_1(sK2)) != iProver_top ),
    inference(superposition,[status(thm)],[c_3872,c_1191])).

cnf(c_26,plain,
    ( ~ v1_funct_2(X0,X1,X1)
    | ~ v3_funct_2(X0,X1,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X1)))
    | ~ v1_funct_1(X0)
    | v1_funct_1(k2_funct_2(X1,X0)) ),
    inference(cnf_transformation,[],[f76])).

cnf(c_1199,plain,
    ( v1_funct_2(X0,X1,X1) != iProver_top
    | v3_funct_2(X0,X1,X1) != iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X1))) != iProver_top
    | v1_funct_1(X0) != iProver_top
    | v1_funct_1(k2_funct_2(X1,X0)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_26])).

cnf(c_2898,plain,
    ( v1_funct_2(sK2,sK0,sK0) != iProver_top
    | v3_funct_2(sK2,sK0,sK0) != iProver_top
    | v1_funct_1(k2_funct_2(sK0,sK2)) = iProver_top
    | v1_funct_1(sK2) != iProver_top ),
    inference(superposition,[status(thm)],[c_1196,c_1199])).

cnf(c_1818,plain,
    ( ~ v1_funct_2(sK2,X0,X0)
    | ~ v3_funct_2(sK2,X0,X0)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
    | v1_funct_1(k2_funct_2(X0,sK2))
    | ~ v1_funct_1(sK2) ),
    inference(instantiation,[status(thm)],[c_26])).

cnf(c_1819,plain,
    ( v1_funct_2(sK2,X0,X0) != iProver_top
    | v3_funct_2(sK2,X0,X0) != iProver_top
    | m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) != iProver_top
    | v1_funct_1(k2_funct_2(X0,sK2)) = iProver_top
    | v1_funct_1(sK2) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1818])).

cnf(c_1821,plain,
    ( v1_funct_2(sK2,sK0,sK0) != iProver_top
    | v3_funct_2(sK2,sK0,sK0) != iProver_top
    | m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) != iProver_top
    | v1_funct_1(k2_funct_2(sK0,sK2)) = iProver_top
    | v1_funct_1(sK2) != iProver_top ),
    inference(instantiation,[status(thm)],[c_1819])).

cnf(c_2972,plain,
    ( v1_funct_1(k2_funct_2(sK0,sK2)) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_2898,c_34,c_35,c_36,c_37,c_1821])).

cnf(c_2976,plain,
    ( v1_funct_1(k2_funct_1(sK2)) = iProver_top ),
    inference(light_normalisation,[status(thm)],[c_2972,c_2969])).

cnf(c_24,plain,
    ( ~ v1_funct_2(X0,X1,X1)
    | ~ v3_funct_2(X0,X1,X1)
    | v3_funct_2(k2_funct_2(X1,X0),X1,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X1)))
    | ~ v1_funct_1(X0) ),
    inference(cnf_transformation,[],[f78])).

cnf(c_1201,plain,
    ( v1_funct_2(X0,X1,X1) != iProver_top
    | v3_funct_2(X0,X1,X1) != iProver_top
    | v3_funct_2(k2_funct_2(X1,X0),X1,X1) = iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X1))) != iProver_top
    | v1_funct_1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_24])).

cnf(c_3372,plain,
    ( v1_funct_2(sK2,sK0,sK0) != iProver_top
    | v3_funct_2(k2_funct_2(sK0,sK2),sK0,sK0) = iProver_top
    | v3_funct_2(sK2,sK0,sK0) != iProver_top
    | v1_funct_1(sK2) != iProver_top ),
    inference(superposition,[status(thm)],[c_1196,c_1201])).

cnf(c_3373,plain,
    ( v1_funct_2(sK2,sK0,sK0) != iProver_top
    | v3_funct_2(k2_funct_1(sK2),sK0,sK0) = iProver_top
    | v3_funct_2(sK2,sK0,sK0) != iProver_top
    | v1_funct_1(sK2) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_3372,c_2969])).

cnf(c_6310,plain,
    ( k2_relat_1(k2_funct_1(sK2)) = sK0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_3879,c_34,c_35,c_36,c_102,c_2976,c_3373,c_3876])).

cnf(c_4137,plain,
    ( v1_relat_1(k2_funct_1(sK2)) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_3876,c_102])).

cnf(c_8,plain,
    ( ~ v1_relat_1(X0)
    | k9_relat_1(X0,k1_relat_1(X0)) = k2_relat_1(X0) ),
    inference(cnf_transformation,[],[f61])).

cnf(c_1211,plain,
    ( k9_relat_1(X0,k1_relat_1(X0)) = k2_relat_1(X0)
    | v1_relat_1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_8])).

cnf(c_4141,plain,
    ( k9_relat_1(k2_funct_1(sK2),k1_relat_1(k2_funct_1(sK2))) = k2_relat_1(k2_funct_1(sK2)) ),
    inference(superposition,[status(thm)],[c_4137,c_1211])).

cnf(c_4225,plain,
    ( k10_relat_1(sK2,k1_relat_1(k2_funct_1(sK2))) = k2_relat_1(k2_funct_1(sK2)) ),
    inference(superposition,[status(thm)],[c_4141,c_3047])).

cnf(c_6314,plain,
    ( k10_relat_1(sK2,k1_relat_1(k2_funct_1(sK2))) = sK0 ),
    inference(demodulation,[status(thm)],[c_6310,c_4225])).

cnf(c_2099,plain,
    ( r1_tarski(k1_relat_1(sK2),sK0) = iProver_top
    | v1_relat_1(sK2) != iProver_top ),
    inference(superposition,[status(thm)],[c_1196,c_1192])).

cnf(c_2422,plain,
    ( r1_tarski(k1_relat_1(sK2),sK0) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_2099,c_37,c_102,c_1497])).

cnf(c_2094,plain,
    ( k9_relat_1(sK2,k1_relat_1(sK2)) = k2_relat_1(sK2) ),
    inference(superposition,[status(thm)],[c_2090,c_1211])).

cnf(c_2097,plain,
    ( k9_relat_1(sK2,k1_relat_1(sK2)) = sK0 ),
    inference(light_normalisation,[status(thm)],[c_2094,c_1774])).

cnf(c_2494,plain,
    ( r1_tarski(k1_relat_1(sK2),X0) != iProver_top
    | r1_tarski(sK0,k9_relat_1(sK2,X0)) = iProver_top
    | v1_relat_1(sK2) != iProver_top ),
    inference(superposition,[status(thm)],[c_2097,c_1210])).

cnf(c_2643,plain,
    ( r1_tarski(sK0,k9_relat_1(sK2,X0)) = iProver_top
    | r1_tarski(k1_relat_1(sK2),X0) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_2494,c_37,c_102,c_1497])).

cnf(c_2644,plain,
    ( r1_tarski(k1_relat_1(sK2),X0) != iProver_top
    | r1_tarski(sK0,k9_relat_1(sK2,X0)) = iProver_top ),
    inference(renaming,[status(thm)],[c_2643])).

cnf(c_7,plain,
    ( r1_tarski(k9_relat_1(X0,X1),k2_relat_1(X0))
    | ~ v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f60])).

cnf(c_1212,plain,
    ( r1_tarski(k9_relat_1(X0,X1),k2_relat_1(X0)) = iProver_top
    | v1_relat_1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_7])).

cnf(c_1776,plain,
    ( r1_tarski(k9_relat_1(sK2,X0),sK0) = iProver_top
    | v1_relat_1(sK2) != iProver_top ),
    inference(superposition,[status(thm)],[c_1774,c_1212])).

cnf(c_1781,plain,
    ( r1_tarski(k9_relat_1(sK2,X0),sK0) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_1776,c_37,c_102,c_1497])).

cnf(c_0,plain,
    ( ~ r1_tarski(X0,X1)
    | ~ r1_tarski(X1,X0)
    | X0 = X1 ),
    inference(cnf_transformation,[],[f55])).

cnf(c_1216,plain,
    ( X0 = X1
    | r1_tarski(X0,X1) != iProver_top
    | r1_tarski(X1,X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_0])).

cnf(c_1787,plain,
    ( k9_relat_1(sK2,X0) = sK0
    | r1_tarski(sK0,k9_relat_1(sK2,X0)) != iProver_top ),
    inference(superposition,[status(thm)],[c_1781,c_1216])).

cnf(c_2651,plain,
    ( k9_relat_1(sK2,X0) = sK0
    | r1_tarski(k1_relat_1(sK2),X0) != iProver_top ),
    inference(superposition,[status(thm)],[c_2644,c_1787])).

cnf(c_6470,plain,
    ( k9_relat_1(sK2,sK0) = sK0 ),
    inference(superposition,[status(thm)],[c_2422,c_2651])).

cnf(c_9235,plain,
    ( k1_relat_1(sK2) = sK0 ),
    inference(light_normalisation,[status(thm)],[c_9234,c_2096,c_6314,c_6470])).

cnf(c_740,plain,
    ( ~ r1_tarski(X0,X1)
    | r1_tarski(X2,X3)
    | X2 != X0
    | X3 != X1 ),
    theory(equality)).

cnf(c_1937,plain,
    ( ~ r1_tarski(X0,X1)
    | r1_tarski(sK1,k1_relat_1(sK2))
    | k1_relat_1(sK2) != X1
    | sK1 != X0 ),
    inference(instantiation,[status(thm)],[c_740])).

cnf(c_2773,plain,
    ( ~ r1_tarski(sK1,X0)
    | r1_tarski(sK1,k1_relat_1(sK2))
    | k1_relat_1(sK2) != X0
    | sK1 != sK1 ),
    inference(instantiation,[status(thm)],[c_1937])).

cnf(c_2775,plain,
    ( r1_tarski(sK1,k1_relat_1(sK2))
    | ~ r1_tarski(sK1,sK0)
    | k1_relat_1(sK2) != sK0
    | sK1 != sK1 ),
    inference(instantiation,[status(thm)],[c_2773])).

cnf(c_17,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k8_relset_1(X1,X2,X0,X3) = k10_relat_1(X0,X3) ),
    inference(cnf_transformation,[],[f70])).

cnf(c_1204,plain,
    ( k8_relset_1(X0,X1,X2,X3) = k10_relat_1(X2,X3)
    | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_17])).

cnf(c_2156,plain,
    ( k8_relset_1(sK0,sK0,sK2,X0) = k10_relat_1(sK2,X0) ),
    inference(superposition,[status(thm)],[c_1196,c_1204])).

cnf(c_28,negated_conjecture,
    ( k8_relset_1(sK0,sK0,sK2,k7_relset_1(sK0,sK0,sK2,sK1)) != sK1
    | k7_relset_1(sK0,sK0,sK2,k8_relset_1(sK0,sK0,sK2,sK1)) != sK1 ),
    inference(cnf_transformation,[],[f86])).

cnf(c_2352,plain,
    ( k7_relset_1(sK0,sK0,sK2,k8_relset_1(sK0,sK0,sK2,sK1)) != sK1
    | k10_relat_1(sK2,k7_relset_1(sK0,sK0,sK2,sK1)) != sK1 ),
    inference(demodulation,[status(thm)],[c_2156,c_28])).

cnf(c_16,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k7_relset_1(X1,X2,X0,X3) = k9_relat_1(X0,X3) ),
    inference(cnf_transformation,[],[f69])).

cnf(c_1205,plain,
    ( k7_relset_1(X0,X1,X2,X3) = k9_relat_1(X2,X3)
    | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_16])).

cnf(c_2159,plain,
    ( k7_relset_1(sK0,sK0,sK2,X0) = k9_relat_1(sK2,X0) ),
    inference(superposition,[status(thm)],[c_1196,c_1205])).

cnf(c_2353,plain,
    ( k10_relat_1(sK2,k9_relat_1(sK2,sK1)) != sK1
    | k9_relat_1(sK2,k10_relat_1(sK2,sK1)) != sK1 ),
    inference(demodulation,[status(thm)],[c_2352,c_2156,c_2159])).

cnf(c_1417,plain,
    ( ~ r1_tarski(sK1,k1_relat_1(X0))
    | ~ v2_funct_1(X0)
    | ~ v1_funct_1(X0)
    | ~ v1_relat_1(X0)
    | k10_relat_1(X0,k9_relat_1(X0,sK1)) = sK1 ),
    inference(instantiation,[status(thm)],[c_13])).

cnf(c_1721,plain,
    ( ~ r1_tarski(sK1,k1_relat_1(sK2))
    | ~ v2_funct_1(sK2)
    | ~ v1_funct_1(sK2)
    | ~ v1_relat_1(sK2)
    | k10_relat_1(sK2,k9_relat_1(sK2,sK1)) = sK1 ),
    inference(instantiation,[status(thm)],[c_1417])).

cnf(c_1603,plain,
    ( ~ v3_funct_2(sK2,sK0,sK0)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
    | v2_funct_1(sK2)
    | ~ v1_funct_1(sK2) ),
    inference(instantiation,[status(thm)],[c_1601])).

cnf(c_1530,plain,
    ( ~ r1_tarski(X0,X1)
    | r1_tarski(sK1,k2_relat_1(sK2))
    | k2_relat_1(sK2) != X1
    | sK1 != X0 ),
    inference(instantiation,[status(thm)],[c_740])).

cnf(c_1571,plain,
    ( ~ r1_tarski(sK1,X0)
    | r1_tarski(sK1,k2_relat_1(sK2))
    | k2_relat_1(sK2) != X0
    | sK1 != sK1 ),
    inference(instantiation,[status(thm)],[c_1530])).

cnf(c_1573,plain,
    ( r1_tarski(sK1,k2_relat_1(sK2))
    | ~ r1_tarski(sK1,sK0)
    | k2_relat_1(sK2) != sK0
    | sK1 != sK1 ),
    inference(instantiation,[status(thm)],[c_1571])).

cnf(c_11,plain,
    ( ~ r1_tarski(X0,k2_relat_1(X1))
    | ~ v1_funct_1(X1)
    | ~ v1_relat_1(X1)
    | k9_relat_1(X1,k10_relat_1(X1,X0)) = X0 ),
    inference(cnf_transformation,[],[f64])).

cnf(c_1410,plain,
    ( ~ r1_tarski(sK1,k2_relat_1(X0))
    | ~ v1_funct_1(X0)
    | ~ v1_relat_1(X0)
    | k9_relat_1(X0,k10_relat_1(X0,sK1)) = sK1 ),
    inference(instantiation,[status(thm)],[c_11])).

cnf(c_1462,plain,
    ( ~ r1_tarski(sK1,k2_relat_1(sK2))
    | ~ v1_funct_1(sK2)
    | ~ v1_relat_1(sK2)
    | k9_relat_1(sK2,k10_relat_1(sK2,sK1)) = sK1 ),
    inference(instantiation,[status(thm)],[c_1410])).

cnf(c_1,plain,
    ( r1_tarski(X0,X0) ),
    inference(cnf_transformation,[],[f87])).

cnf(c_1293,plain,
    ( r1_tarski(sK1,sK1) ),
    inference(instantiation,[status(thm)],[c_1])).

cnf(c_1258,plain,
    ( ~ r1_tarski(X0,sK1)
    | ~ r1_tarski(sK1,X0)
    | sK1 = X0 ),
    inference(instantiation,[status(thm)],[c_0])).

cnf(c_1266,plain,
    ( ~ r1_tarski(sK1,sK1)
    | sK1 = sK1 ),
    inference(instantiation,[status(thm)],[c_1258])).

cnf(c_101,plain,
    ( v1_relat_1(k2_zfmisc_1(sK0,sK0)) ),
    inference(instantiation,[status(thm)],[c_6])).

cnf(c_29,negated_conjecture,
    ( r1_tarski(sK1,sK0) ),
    inference(cnf_transformation,[],[f85])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_9235,c_2775,c_2353,c_1721,c_1603,c_1573,c_1557,c_1497,c_1496,c_1462,c_1293,c_1266,c_102,c_101,c_29,c_37,c_30,c_36,c_31,c_34,c_33])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : iproveropt_run.sh %d %s
% 0.13/0.34  % Computer   : n013.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 12:19:09 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running in FOF mode
% 4.03/0.99  % SZS status Started for /export/starexec/sandbox/benchmark/theBenchmark.p
% 4.03/0.99  
% 4.03/0.99  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 4.03/0.99  
% 4.03/0.99  ------  iProver source info
% 4.03/0.99  
% 4.03/0.99  git: date: 2020-06-30 10:37:57 +0100
% 4.03/0.99  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 4.03/0.99  git: non_committed_changes: false
% 4.03/0.99  git: last_make_outside_of_git: false
% 4.03/0.99  
% 4.03/0.99  ------ 
% 4.03/0.99  
% 4.03/0.99  ------ Input Options
% 4.03/0.99  
% 4.03/0.99  --out_options                           all
% 4.03/0.99  --tptp_safe_out                         true
% 4.03/0.99  --problem_path                          ""
% 4.03/0.99  --include_path                          ""
% 4.03/0.99  --clausifier                            res/vclausify_rel
% 4.03/0.99  --clausifier_options                    ""
% 4.03/0.99  --stdin                                 false
% 4.03/0.99  --stats_out                             all
% 4.03/0.99  
% 4.03/0.99  ------ General Options
% 4.03/0.99  
% 4.03/0.99  --fof                                   false
% 4.03/0.99  --time_out_real                         305.
% 4.03/0.99  --time_out_virtual                      -1.
% 4.03/0.99  --symbol_type_check                     false
% 4.03/0.99  --clausify_out                          false
% 4.03/0.99  --sig_cnt_out                           false
% 4.03/0.99  --trig_cnt_out                          false
% 4.03/0.99  --trig_cnt_out_tolerance                1.
% 4.03/0.99  --trig_cnt_out_sk_spl                   false
% 4.03/0.99  --abstr_cl_out                          false
% 4.03/0.99  
% 4.03/0.99  ------ Global Options
% 4.03/0.99  
% 4.03/0.99  --schedule                              default
% 4.03/0.99  --add_important_lit                     false
% 4.03/0.99  --prop_solver_per_cl                    1000
% 4.03/0.99  --min_unsat_core                        false
% 4.03/0.99  --soft_assumptions                      false
% 4.03/0.99  --soft_lemma_size                       3
% 4.03/0.99  --prop_impl_unit_size                   0
% 4.03/0.99  --prop_impl_unit                        []
% 4.03/0.99  --share_sel_clauses                     true
% 4.03/0.99  --reset_solvers                         false
% 4.03/0.99  --bc_imp_inh                            [conj_cone]
% 4.03/0.99  --conj_cone_tolerance                   3.
% 4.03/0.99  --extra_neg_conj                        none
% 4.03/0.99  --large_theory_mode                     true
% 4.03/0.99  --prolific_symb_bound                   200
% 4.03/0.99  --lt_threshold                          2000
% 4.03/0.99  --clause_weak_htbl                      true
% 4.03/0.99  --gc_record_bc_elim                     false
% 4.03/0.99  
% 4.03/0.99  ------ Preprocessing Options
% 4.03/0.99  
% 4.03/0.99  --preprocessing_flag                    true
% 4.03/0.99  --time_out_prep_mult                    0.1
% 4.03/0.99  --splitting_mode                        input
% 4.03/0.99  --splitting_grd                         true
% 4.03/0.99  --splitting_cvd                         false
% 4.03/0.99  --splitting_cvd_svl                     false
% 4.03/0.99  --splitting_nvd                         32
% 4.03/0.99  --sub_typing                            true
% 4.03/0.99  --prep_gs_sim                           true
% 4.03/0.99  --prep_unflatten                        true
% 4.03/0.99  --prep_res_sim                          true
% 4.03/0.99  --prep_upred                            true
% 4.03/0.99  --prep_sem_filter                       exhaustive
% 4.03/0.99  --prep_sem_filter_out                   false
% 4.03/0.99  --pred_elim                             true
% 4.03/0.99  --res_sim_input                         true
% 4.03/0.99  --eq_ax_congr_red                       true
% 4.03/0.99  --pure_diseq_elim                       true
% 4.03/0.99  --brand_transform                       false
% 4.03/0.99  --non_eq_to_eq                          false
% 4.03/0.99  --prep_def_merge                        true
% 4.03/0.99  --prep_def_merge_prop_impl              false
% 4.03/0.99  --prep_def_merge_mbd                    true
% 4.03/0.99  --prep_def_merge_tr_red                 false
% 4.03/0.99  --prep_def_merge_tr_cl                  false
% 4.03/0.99  --smt_preprocessing                     true
% 4.03/0.99  --smt_ac_axioms                         fast
% 4.03/0.99  --preprocessed_out                      false
% 4.03/0.99  --preprocessed_stats                    false
% 4.03/0.99  
% 4.03/0.99  ------ Abstraction refinement Options
% 4.03/0.99  
% 4.03/0.99  --abstr_ref                             []
% 4.03/0.99  --abstr_ref_prep                        false
% 4.03/0.99  --abstr_ref_until_sat                   false
% 4.03/0.99  --abstr_ref_sig_restrict                funpre
% 4.03/0.99  --abstr_ref_af_restrict_to_split_sk     false
% 4.03/0.99  --abstr_ref_under                       []
% 4.03/0.99  
% 4.03/0.99  ------ SAT Options
% 4.03/0.99  
% 4.03/0.99  --sat_mode                              false
% 4.03/0.99  --sat_fm_restart_options                ""
% 4.03/0.99  --sat_gr_def                            false
% 4.03/0.99  --sat_epr_types                         true
% 4.03/0.99  --sat_non_cyclic_types                  false
% 4.03/0.99  --sat_finite_models                     false
% 4.03/0.99  --sat_fm_lemmas                         false
% 4.03/0.99  --sat_fm_prep                           false
% 4.03/0.99  --sat_fm_uc_incr                        true
% 4.03/1.00  --sat_out_model                         small
% 4.03/1.00  --sat_out_clauses                       false
% 4.03/1.00  
% 4.03/1.00  ------ QBF Options
% 4.03/1.00  
% 4.03/1.00  --qbf_mode                              false
% 4.03/1.00  --qbf_elim_univ                         false
% 4.03/1.00  --qbf_dom_inst                          none
% 4.03/1.00  --qbf_dom_pre_inst                      false
% 4.03/1.00  --qbf_sk_in                             false
% 4.03/1.00  --qbf_pred_elim                         true
% 4.03/1.00  --qbf_split                             512
% 4.03/1.00  
% 4.03/1.00  ------ BMC1 Options
% 4.03/1.00  
% 4.03/1.00  --bmc1_incremental                      false
% 4.03/1.00  --bmc1_axioms                           reachable_all
% 4.03/1.00  --bmc1_min_bound                        0
% 4.03/1.00  --bmc1_max_bound                        -1
% 4.03/1.00  --bmc1_max_bound_default                -1
% 4.03/1.00  --bmc1_symbol_reachability              true
% 4.03/1.00  --bmc1_property_lemmas                  false
% 4.03/1.00  --bmc1_k_induction                      false
% 4.03/1.00  --bmc1_non_equiv_states                 false
% 4.03/1.00  --bmc1_deadlock                         false
% 4.03/1.00  --bmc1_ucm                              false
% 4.03/1.00  --bmc1_add_unsat_core                   none
% 4.03/1.00  --bmc1_unsat_core_children              false
% 4.03/1.00  --bmc1_unsat_core_extrapolate_axioms    false
% 4.03/1.00  --bmc1_out_stat                         full
% 4.03/1.00  --bmc1_ground_init                      false
% 4.03/1.00  --bmc1_pre_inst_next_state              false
% 4.03/1.00  --bmc1_pre_inst_state                   false
% 4.03/1.00  --bmc1_pre_inst_reach_state             false
% 4.03/1.00  --bmc1_out_unsat_core                   false
% 4.03/1.00  --bmc1_aig_witness_out                  false
% 4.03/1.00  --bmc1_verbose                          false
% 4.03/1.00  --bmc1_dump_clauses_tptp                false
% 4.03/1.00  --bmc1_dump_unsat_core_tptp             false
% 4.03/1.00  --bmc1_dump_file                        -
% 4.03/1.00  --bmc1_ucm_expand_uc_limit              128
% 4.03/1.00  --bmc1_ucm_n_expand_iterations          6
% 4.03/1.00  --bmc1_ucm_extend_mode                  1
% 4.03/1.00  --bmc1_ucm_init_mode                    2
% 4.03/1.00  --bmc1_ucm_cone_mode                    none
% 4.03/1.00  --bmc1_ucm_reduced_relation_type        0
% 4.03/1.00  --bmc1_ucm_relax_model                  4
% 4.03/1.00  --bmc1_ucm_full_tr_after_sat            true
% 4.03/1.00  --bmc1_ucm_expand_neg_assumptions       false
% 4.03/1.00  --bmc1_ucm_layered_model                none
% 4.03/1.00  --bmc1_ucm_max_lemma_size               10
% 4.03/1.00  
% 4.03/1.00  ------ AIG Options
% 4.03/1.00  
% 4.03/1.00  --aig_mode                              false
% 4.03/1.00  
% 4.03/1.00  ------ Instantiation Options
% 4.03/1.00  
% 4.03/1.00  --instantiation_flag                    true
% 4.03/1.00  --inst_sos_flag                         true
% 4.03/1.00  --inst_sos_phase                        true
% 4.03/1.00  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 4.03/1.00  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 4.03/1.00  --inst_lit_sel_side                     num_symb
% 4.03/1.00  --inst_solver_per_active                1400
% 4.03/1.00  --inst_solver_calls_frac                1.
% 4.03/1.00  --inst_passive_queue_type               priority_queues
% 4.03/1.00  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 4.03/1.00  --inst_passive_queues_freq              [25;2]
% 4.03/1.00  --inst_dismatching                      true
% 4.03/1.00  --inst_eager_unprocessed_to_passive     true
% 4.03/1.00  --inst_prop_sim_given                   true
% 4.03/1.00  --inst_prop_sim_new                     false
% 4.03/1.00  --inst_subs_new                         false
% 4.03/1.00  --inst_eq_res_simp                      false
% 4.03/1.00  --inst_subs_given                       false
% 4.03/1.00  --inst_orphan_elimination               true
% 4.03/1.00  --inst_learning_loop_flag               true
% 4.03/1.00  --inst_learning_start                   3000
% 4.03/1.00  --inst_learning_factor                  2
% 4.03/1.00  --inst_start_prop_sim_after_learn       3
% 4.03/1.00  --inst_sel_renew                        solver
% 4.03/1.00  --inst_lit_activity_flag                true
% 4.03/1.00  --inst_restr_to_given                   false
% 4.03/1.00  --inst_activity_threshold               500
% 4.03/1.00  --inst_out_proof                        true
% 4.03/1.00  
% 4.03/1.00  ------ Resolution Options
% 4.03/1.00  
% 4.03/1.00  --resolution_flag                       true
% 4.03/1.00  --res_lit_sel                           adaptive
% 4.03/1.00  --res_lit_sel_side                      none
% 4.03/1.00  --res_ordering                          kbo
% 4.03/1.00  --res_to_prop_solver                    active
% 4.03/1.00  --res_prop_simpl_new                    false
% 4.03/1.00  --res_prop_simpl_given                  true
% 4.03/1.00  --res_passive_queue_type                priority_queues
% 4.03/1.00  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 4.03/1.00  --res_passive_queues_freq               [15;5]
% 4.03/1.00  --res_forward_subs                      full
% 4.03/1.00  --res_backward_subs                     full
% 4.03/1.00  --res_forward_subs_resolution           true
% 4.03/1.00  --res_backward_subs_resolution          true
% 4.03/1.00  --res_orphan_elimination                true
% 4.03/1.00  --res_time_limit                        2.
% 4.03/1.00  --res_out_proof                         true
% 4.03/1.00  
% 4.03/1.00  ------ Superposition Options
% 4.03/1.00  
% 4.03/1.00  --superposition_flag                    true
% 4.03/1.00  --sup_passive_queue_type                priority_queues
% 4.03/1.00  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 4.03/1.00  --sup_passive_queues_freq               [8;1;4]
% 4.03/1.00  --demod_completeness_check              fast
% 4.03/1.00  --demod_use_ground                      true
% 4.03/1.00  --sup_to_prop_solver                    passive
% 4.03/1.00  --sup_prop_simpl_new                    true
% 4.03/1.00  --sup_prop_simpl_given                  true
% 4.03/1.00  --sup_fun_splitting                     true
% 4.03/1.00  --sup_smt_interval                      50000
% 4.03/1.00  
% 4.03/1.00  ------ Superposition Simplification Setup
% 4.03/1.00  
% 4.03/1.00  --sup_indices_passive                   [LightNormIndex;FwDemodIndex]
% 4.03/1.00  --sup_indices_active                    [SubsumptionIndex;BwDemodIndex]
% 4.03/1.00  --sup_indices_immed                     [SubsumptionIndex;FwDemodIndex;BwDemodIndex]
% 4.03/1.00  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex]
% 4.03/1.00  --sup_full_triv                         [TrivRules;PropSubs]
% 4.03/1.00  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;Joinability]
% 4.03/1.00  --sup_full_bw                           [BwDemod;BwSubsumption]
% 4.03/1.00  --sup_immed_triv                        [TrivRules]
% 4.03/1.00  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 4.03/1.00  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption]
% 4.03/1.00  --sup_immed_bw_main                     []
% 4.03/1.00  --sup_immed_bw_immed                    [BwDemod;BwSubsumption]
% 4.03/1.00  --sup_input_triv                        [Unflattening;TrivRules]
% 4.03/1.00  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption]
% 4.03/1.00  --sup_input_bw                          []
% 4.03/1.00  
% 4.03/1.00  ------ Combination Options
% 4.03/1.00  
% 4.03/1.00  --comb_res_mult                         3
% 4.03/1.00  --comb_sup_mult                         2
% 4.03/1.00  --comb_inst_mult                        10
% 4.03/1.00  
% 4.03/1.00  ------ Debug Options
% 4.03/1.00  
% 4.03/1.00  --dbg_backtrace                         false
% 4.03/1.00  --dbg_dump_prop_clauses                 false
% 4.03/1.00  --dbg_dump_prop_clauses_file            -
% 4.03/1.00  --dbg_out_stat                          false
% 4.03/1.00  ------ Parsing...
% 4.03/1.00  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 4.03/1.00  
% 4.03/1.00  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe:1:0s pe:2:0s pe_e  sf_s  rm: 3 0s  sf_e  pe_s  pe_e 
% 4.03/1.00  
% 4.03/1.00  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 4.03/1.00  
% 4.03/1.00  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 4.03/1.00  ------ Proving...
% 4.03/1.00  ------ Problem Properties 
% 4.03/1.00  
% 4.03/1.00  
% 4.03/1.00  clauses                                 27
% 4.03/1.00  conjectures                             6
% 4.03/1.00  EPR                                     6
% 4.03/1.00  Horn                                    27
% 4.03/1.00  unary                                   7
% 4.03/1.00  binary                                  6
% 4.03/1.00  lits                                    78
% 4.03/1.00  lits eq                                 12
% 4.03/1.00  fd_pure                                 0
% 4.03/1.00  fd_pseudo                               0
% 4.03/1.00  fd_cond                                 0
% 4.03/1.00  fd_pseudo_cond                          2
% 4.03/1.00  AC symbols                              0
% 4.03/1.00  
% 4.03/1.00  ------ Schedule dynamic 5 is on 
% 4.03/1.00  
% 4.03/1.00  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" Time Limit: 10.
% 4.03/1.00  
% 4.03/1.00  
% 4.03/1.00  ------ 
% 4.03/1.00  Current options:
% 4.03/1.00  ------ 
% 4.03/1.00  
% 4.03/1.00  ------ Input Options
% 4.03/1.00  
% 4.03/1.00  --out_options                           all
% 4.03/1.00  --tptp_safe_out                         true
% 4.03/1.00  --problem_path                          ""
% 4.03/1.00  --include_path                          ""
% 4.03/1.00  --clausifier                            res/vclausify_rel
% 4.03/1.00  --clausifier_options                    ""
% 4.03/1.00  --stdin                                 false
% 4.03/1.00  --stats_out                             all
% 4.03/1.00  
% 4.03/1.00  ------ General Options
% 4.03/1.00  
% 4.03/1.00  --fof                                   false
% 4.03/1.00  --time_out_real                         305.
% 4.03/1.00  --time_out_virtual                      -1.
% 4.03/1.00  --symbol_type_check                     false
% 4.03/1.00  --clausify_out                          false
% 4.03/1.00  --sig_cnt_out                           false
% 4.03/1.00  --trig_cnt_out                          false
% 4.03/1.00  --trig_cnt_out_tolerance                1.
% 4.03/1.00  --trig_cnt_out_sk_spl                   false
% 4.03/1.00  --abstr_cl_out                          false
% 4.03/1.00  
% 4.03/1.00  ------ Global Options
% 4.03/1.00  
% 4.03/1.00  --schedule                              default
% 4.03/1.00  --add_important_lit                     false
% 4.03/1.00  --prop_solver_per_cl                    1000
% 4.03/1.00  --min_unsat_core                        false
% 4.03/1.00  --soft_assumptions                      false
% 4.03/1.00  --soft_lemma_size                       3
% 4.03/1.00  --prop_impl_unit_size                   0
% 4.03/1.00  --prop_impl_unit                        []
% 4.03/1.00  --share_sel_clauses                     true
% 4.03/1.00  --reset_solvers                         false
% 4.03/1.00  --bc_imp_inh                            [conj_cone]
% 4.03/1.00  --conj_cone_tolerance                   3.
% 4.03/1.00  --extra_neg_conj                        none
% 4.03/1.00  --large_theory_mode                     true
% 4.03/1.00  --prolific_symb_bound                   200
% 4.03/1.00  --lt_threshold                          2000
% 4.03/1.00  --clause_weak_htbl                      true
% 4.03/1.00  --gc_record_bc_elim                     false
% 4.03/1.00  
% 4.03/1.00  ------ Preprocessing Options
% 4.03/1.00  
% 4.03/1.00  --preprocessing_flag                    true
% 4.03/1.00  --time_out_prep_mult                    0.1
% 4.03/1.00  --splitting_mode                        input
% 4.03/1.00  --splitting_grd                         true
% 4.03/1.00  --splitting_cvd                         false
% 4.03/1.00  --splitting_cvd_svl                     false
% 4.03/1.00  --splitting_nvd                         32
% 4.03/1.00  --sub_typing                            true
% 4.03/1.00  --prep_gs_sim                           true
% 4.03/1.00  --prep_unflatten                        true
% 4.03/1.00  --prep_res_sim                          true
% 4.03/1.00  --prep_upred                            true
% 4.03/1.00  --prep_sem_filter                       exhaustive
% 4.03/1.00  --prep_sem_filter_out                   false
% 4.03/1.00  --pred_elim                             true
% 4.03/1.00  --res_sim_input                         true
% 4.03/1.00  --eq_ax_congr_red                       true
% 4.03/1.00  --pure_diseq_elim                       true
% 4.03/1.00  --brand_transform                       false
% 4.03/1.00  --non_eq_to_eq                          false
% 4.03/1.00  --prep_def_merge                        true
% 4.03/1.00  --prep_def_merge_prop_impl              false
% 4.03/1.00  --prep_def_merge_mbd                    true
% 4.03/1.00  --prep_def_merge_tr_red                 false
% 4.03/1.00  --prep_def_merge_tr_cl                  false
% 4.03/1.00  --smt_preprocessing                     true
% 4.03/1.00  --smt_ac_axioms                         fast
% 4.03/1.00  --preprocessed_out                      false
% 4.03/1.00  --preprocessed_stats                    false
% 4.03/1.00  
% 4.03/1.00  ------ Abstraction refinement Options
% 4.03/1.00  
% 4.03/1.00  --abstr_ref                             []
% 4.03/1.00  --abstr_ref_prep                        false
% 4.03/1.00  --abstr_ref_until_sat                   false
% 4.03/1.00  --abstr_ref_sig_restrict                funpre
% 4.03/1.00  --abstr_ref_af_restrict_to_split_sk     false
% 4.03/1.00  --abstr_ref_under                       []
% 4.03/1.00  
% 4.03/1.00  ------ SAT Options
% 4.03/1.00  
% 4.03/1.00  --sat_mode                              false
% 4.03/1.00  --sat_fm_restart_options                ""
% 4.03/1.00  --sat_gr_def                            false
% 4.03/1.00  --sat_epr_types                         true
% 4.03/1.00  --sat_non_cyclic_types                  false
% 4.03/1.00  --sat_finite_models                     false
% 4.03/1.00  --sat_fm_lemmas                         false
% 4.03/1.00  --sat_fm_prep                           false
% 4.03/1.00  --sat_fm_uc_incr                        true
% 4.03/1.00  --sat_out_model                         small
% 4.03/1.00  --sat_out_clauses                       false
% 4.03/1.00  
% 4.03/1.00  ------ QBF Options
% 4.03/1.00  
% 4.03/1.00  --qbf_mode                              false
% 4.03/1.00  --qbf_elim_univ                         false
% 4.03/1.00  --qbf_dom_inst                          none
% 4.03/1.00  --qbf_dom_pre_inst                      false
% 4.03/1.00  --qbf_sk_in                             false
% 4.03/1.00  --qbf_pred_elim                         true
% 4.03/1.00  --qbf_split                             512
% 4.03/1.00  
% 4.03/1.00  ------ BMC1 Options
% 4.03/1.00  
% 4.03/1.00  --bmc1_incremental                      false
% 4.03/1.00  --bmc1_axioms                           reachable_all
% 4.03/1.00  --bmc1_min_bound                        0
% 4.03/1.00  --bmc1_max_bound                        -1
% 4.03/1.00  --bmc1_max_bound_default                -1
% 4.03/1.00  --bmc1_symbol_reachability              true
% 4.03/1.00  --bmc1_property_lemmas                  false
% 4.03/1.00  --bmc1_k_induction                      false
% 4.03/1.00  --bmc1_non_equiv_states                 false
% 4.03/1.00  --bmc1_deadlock                         false
% 4.03/1.00  --bmc1_ucm                              false
% 4.03/1.00  --bmc1_add_unsat_core                   none
% 4.03/1.00  --bmc1_unsat_core_children              false
% 4.03/1.00  --bmc1_unsat_core_extrapolate_axioms    false
% 4.03/1.00  --bmc1_out_stat                         full
% 4.03/1.00  --bmc1_ground_init                      false
% 4.03/1.00  --bmc1_pre_inst_next_state              false
% 4.03/1.00  --bmc1_pre_inst_state                   false
% 4.03/1.00  --bmc1_pre_inst_reach_state             false
% 4.03/1.00  --bmc1_out_unsat_core                   false
% 4.03/1.00  --bmc1_aig_witness_out                  false
% 4.03/1.00  --bmc1_verbose                          false
% 4.03/1.00  --bmc1_dump_clauses_tptp                false
% 4.03/1.00  --bmc1_dump_unsat_core_tptp             false
% 4.03/1.00  --bmc1_dump_file                        -
% 4.03/1.00  --bmc1_ucm_expand_uc_limit              128
% 4.03/1.00  --bmc1_ucm_n_expand_iterations          6
% 4.03/1.00  --bmc1_ucm_extend_mode                  1
% 4.03/1.00  --bmc1_ucm_init_mode                    2
% 4.03/1.00  --bmc1_ucm_cone_mode                    none
% 4.03/1.00  --bmc1_ucm_reduced_relation_type        0
% 4.03/1.00  --bmc1_ucm_relax_model                  4
% 4.03/1.00  --bmc1_ucm_full_tr_after_sat            true
% 4.03/1.00  --bmc1_ucm_expand_neg_assumptions       false
% 4.03/1.00  --bmc1_ucm_layered_model                none
% 4.03/1.00  --bmc1_ucm_max_lemma_size               10
% 4.03/1.00  
% 4.03/1.00  ------ AIG Options
% 4.03/1.00  
% 4.03/1.00  --aig_mode                              false
% 4.03/1.00  
% 4.03/1.00  ------ Instantiation Options
% 4.03/1.00  
% 4.03/1.00  --instantiation_flag                    true
% 4.03/1.00  --inst_sos_flag                         true
% 4.03/1.00  --inst_sos_phase                        true
% 4.03/1.00  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 4.03/1.00  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 4.03/1.00  --inst_lit_sel_side                     none
% 4.03/1.00  --inst_solver_per_active                1400
% 4.03/1.00  --inst_solver_calls_frac                1.
% 4.03/1.00  --inst_passive_queue_type               priority_queues
% 4.03/1.00  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 4.03/1.00  --inst_passive_queues_freq              [25;2]
% 4.03/1.00  --inst_dismatching                      true
% 4.03/1.00  --inst_eager_unprocessed_to_passive     true
% 4.03/1.00  --inst_prop_sim_given                   true
% 4.03/1.00  --inst_prop_sim_new                     false
% 4.03/1.00  --inst_subs_new                         false
% 4.03/1.00  --inst_eq_res_simp                      false
% 4.03/1.00  --inst_subs_given                       false
% 4.03/1.00  --inst_orphan_elimination               true
% 4.03/1.00  --inst_learning_loop_flag               true
% 4.03/1.00  --inst_learning_start                   3000
% 4.03/1.00  --inst_learning_factor                  2
% 4.03/1.00  --inst_start_prop_sim_after_learn       3
% 4.03/1.00  --inst_sel_renew                        solver
% 4.03/1.00  --inst_lit_activity_flag                true
% 4.03/1.00  --inst_restr_to_given                   false
% 4.03/1.00  --inst_activity_threshold               500
% 4.03/1.00  --inst_out_proof                        true
% 4.03/1.00  
% 4.03/1.00  ------ Resolution Options
% 4.03/1.00  
% 4.03/1.00  --resolution_flag                       false
% 4.03/1.00  --res_lit_sel                           adaptive
% 4.03/1.00  --res_lit_sel_side                      none
% 4.03/1.00  --res_ordering                          kbo
% 4.03/1.00  --res_to_prop_solver                    active
% 4.03/1.00  --res_prop_simpl_new                    false
% 4.03/1.00  --res_prop_simpl_given                  true
% 4.03/1.00  --res_passive_queue_type                priority_queues
% 4.03/1.00  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 4.03/1.00  --res_passive_queues_freq               [15;5]
% 4.03/1.00  --res_forward_subs                      full
% 4.03/1.00  --res_backward_subs                     full
% 4.03/1.00  --res_forward_subs_resolution           true
% 4.03/1.00  --res_backward_subs_resolution          true
% 4.03/1.00  --res_orphan_elimination                true
% 4.03/1.00  --res_time_limit                        2.
% 4.03/1.00  --res_out_proof                         true
% 4.03/1.00  
% 4.03/1.00  ------ Superposition Options
% 4.03/1.00  
% 4.03/1.00  --superposition_flag                    true
% 4.03/1.00  --sup_passive_queue_type                priority_queues
% 4.03/1.00  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 4.03/1.00  --sup_passive_queues_freq               [8;1;4]
% 4.03/1.00  --demod_completeness_check              fast
% 4.03/1.00  --demod_use_ground                      true
% 4.03/1.00  --sup_to_prop_solver                    passive
% 4.03/1.00  --sup_prop_simpl_new                    true
% 4.03/1.00  --sup_prop_simpl_given                  true
% 4.03/1.00  --sup_fun_splitting                     true
% 4.03/1.00  --sup_smt_interval                      50000
% 4.03/1.00  
% 4.03/1.00  ------ Superposition Simplification Setup
% 4.03/1.00  
% 4.03/1.00  --sup_indices_passive                   [LightNormIndex;FwDemodIndex]
% 4.03/1.00  --sup_indices_active                    [SubsumptionIndex;BwDemodIndex]
% 4.03/1.00  --sup_indices_immed                     [SubsumptionIndex;FwDemodIndex;BwDemodIndex]
% 4.03/1.00  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex]
% 4.03/1.00  --sup_full_triv                         [TrivRules;PropSubs]
% 4.03/1.00  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;Joinability]
% 4.03/1.00  --sup_full_bw                           [BwDemod;BwSubsumption]
% 4.03/1.00  --sup_immed_triv                        [TrivRules]
% 4.03/1.00  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 4.03/1.00  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption]
% 4.03/1.00  --sup_immed_bw_main                     []
% 4.03/1.00  --sup_immed_bw_immed                    [BwDemod;BwSubsumption]
% 4.03/1.00  --sup_input_triv                        [Unflattening;TrivRules]
% 4.03/1.00  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption]
% 4.03/1.00  --sup_input_bw                          []
% 4.03/1.00  
% 4.03/1.00  ------ Combination Options
% 4.03/1.00  
% 4.03/1.00  --comb_res_mult                         3
% 4.03/1.00  --comb_sup_mult                         2
% 4.03/1.00  --comb_inst_mult                        10
% 4.03/1.00  
% 4.03/1.00  ------ Debug Options
% 4.03/1.00  
% 4.03/1.00  --dbg_backtrace                         false
% 4.03/1.00  --dbg_dump_prop_clauses                 false
% 4.03/1.00  --dbg_dump_prop_clauses_file            -
% 4.03/1.00  --dbg_out_stat                          false
% 4.03/1.00  
% 4.03/1.00  
% 4.03/1.00  
% 4.03/1.00  
% 4.03/1.00  ------ Proving...
% 4.03/1.00  
% 4.03/1.00  
% 4.03/1.00  % SZS status Theorem for theBenchmark.p
% 4.03/1.00  
% 4.03/1.00  % SZS output start CNFRefutation for theBenchmark.p
% 4.03/1.00  
% 4.03/1.00  fof(f19,conjecture,(
% 4.03/1.00    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v3_funct_2(X2,X0,X0) & v1_funct_2(X2,X0,X0) & v1_funct_1(X2)) => (r1_tarski(X1,X0) => (k8_relset_1(X0,X0,X2,k7_relset_1(X0,X0,X2,X1)) = X1 & k7_relset_1(X0,X0,X2,k8_relset_1(X0,X0,X2,X1)) = X1)))),
% 4.03/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 4.03/1.00  
% 4.03/1.00  fof(f20,negated_conjecture,(
% 4.03/1.00    ~! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v3_funct_2(X2,X0,X0) & v1_funct_2(X2,X0,X0) & v1_funct_1(X2)) => (r1_tarski(X1,X0) => (k8_relset_1(X0,X0,X2,k7_relset_1(X0,X0,X2,X1)) = X1 & k7_relset_1(X0,X0,X2,k8_relset_1(X0,X0,X2,X1)) = X1)))),
% 4.03/1.00    inference(negated_conjecture,[],[f19])).
% 4.03/1.00  
% 4.03/1.00  fof(f45,plain,(
% 4.03/1.00    ? [X0,X1,X2] : (((k8_relset_1(X0,X0,X2,k7_relset_1(X0,X0,X2,X1)) != X1 | k7_relset_1(X0,X0,X2,k8_relset_1(X0,X0,X2,X1)) != X1) & r1_tarski(X1,X0)) & (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v3_funct_2(X2,X0,X0) & v1_funct_2(X2,X0,X0) & v1_funct_1(X2)))),
% 4.03/1.00    inference(ennf_transformation,[],[f20])).
% 4.03/1.00  
% 4.03/1.00  fof(f46,plain,(
% 4.03/1.00    ? [X0,X1,X2] : ((k8_relset_1(X0,X0,X2,k7_relset_1(X0,X0,X2,X1)) != X1 | k7_relset_1(X0,X0,X2,k8_relset_1(X0,X0,X2,X1)) != X1) & r1_tarski(X1,X0) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v3_funct_2(X2,X0,X0) & v1_funct_2(X2,X0,X0) & v1_funct_1(X2))),
% 4.03/1.00    inference(flattening,[],[f45])).
% 4.03/1.00  
% 4.03/1.00  fof(f51,plain,(
% 4.03/1.00    ? [X0,X1,X2] : ((k8_relset_1(X0,X0,X2,k7_relset_1(X0,X0,X2,X1)) != X1 | k7_relset_1(X0,X0,X2,k8_relset_1(X0,X0,X2,X1)) != X1) & r1_tarski(X1,X0) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v3_funct_2(X2,X0,X0) & v1_funct_2(X2,X0,X0) & v1_funct_1(X2)) => ((k8_relset_1(sK0,sK0,sK2,k7_relset_1(sK0,sK0,sK2,sK1)) != sK1 | k7_relset_1(sK0,sK0,sK2,k8_relset_1(sK0,sK0,sK2,sK1)) != sK1) & r1_tarski(sK1,sK0) & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) & v3_funct_2(sK2,sK0,sK0) & v1_funct_2(sK2,sK0,sK0) & v1_funct_1(sK2))),
% 4.03/1.00    introduced(choice_axiom,[])).
% 4.03/1.00  
% 4.03/1.00  fof(f52,plain,(
% 4.03/1.00    (k8_relset_1(sK0,sK0,sK2,k7_relset_1(sK0,sK0,sK2,sK1)) != sK1 | k7_relset_1(sK0,sK0,sK2,k8_relset_1(sK0,sK0,sK2,sK1)) != sK1) & r1_tarski(sK1,sK0) & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) & v3_funct_2(sK2,sK0,sK0) & v1_funct_2(sK2,sK0,sK0) & v1_funct_1(sK2)),
% 4.03/1.00    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f46,f51])).
% 4.03/1.00  
% 4.03/1.00  fof(f84,plain,(
% 4.03/1.00    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))),
% 4.03/1.00    inference(cnf_transformation,[],[f52])).
% 4.03/1.00  
% 4.03/1.00  fof(f18,axiom,(
% 4.03/1.00    ! [X0,X1] : ((m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v3_funct_2(X1,X0,X0) & v1_funct_2(X1,X0,X0) & v1_funct_1(X1)) => k2_funct_1(X1) = k2_funct_2(X0,X1))),
% 4.03/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 4.03/1.00  
% 4.03/1.00  fof(f43,plain,(
% 4.03/1.00    ! [X0,X1] : (k2_funct_1(X1) = k2_funct_2(X0,X1) | (~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) | ~v3_funct_2(X1,X0,X0) | ~v1_funct_2(X1,X0,X0) | ~v1_funct_1(X1)))),
% 4.03/1.00    inference(ennf_transformation,[],[f18])).
% 4.03/1.00  
% 4.03/1.00  fof(f44,plain,(
% 4.03/1.00    ! [X0,X1] : (k2_funct_1(X1) = k2_funct_2(X0,X1) | ~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) | ~v3_funct_2(X1,X0,X0) | ~v1_funct_2(X1,X0,X0) | ~v1_funct_1(X1))),
% 4.03/1.00    inference(flattening,[],[f43])).
% 4.03/1.00  
% 4.03/1.00  fof(f80,plain,(
% 4.03/1.00    ( ! [X0,X1] : (k2_funct_1(X1) = k2_funct_2(X0,X1) | ~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) | ~v3_funct_2(X1,X0,X0) | ~v1_funct_2(X1,X0,X0) | ~v1_funct_1(X1)) )),
% 4.03/1.00    inference(cnf_transformation,[],[f44])).
% 4.03/1.00  
% 4.03/1.00  fof(f81,plain,(
% 4.03/1.00    v1_funct_1(sK2)),
% 4.03/1.00    inference(cnf_transformation,[],[f52])).
% 4.03/1.00  
% 4.03/1.00  fof(f82,plain,(
% 4.03/1.00    v1_funct_2(sK2,sK0,sK0)),
% 4.03/1.00    inference(cnf_transformation,[],[f52])).
% 4.03/1.00  
% 4.03/1.00  fof(f83,plain,(
% 4.03/1.00    v3_funct_2(sK2,sK0,sK0)),
% 4.03/1.00    inference(cnf_transformation,[],[f52])).
% 4.03/1.00  
% 4.03/1.00  fof(f17,axiom,(
% 4.03/1.00    ! [X0,X1] : ((m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v3_funct_2(X1,X0,X0) & v1_funct_2(X1,X0,X0) & v1_funct_1(X1)) => (m1_subset_1(k2_funct_2(X0,X1),k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v3_funct_2(k2_funct_2(X0,X1),X0,X0) & v1_funct_2(k2_funct_2(X0,X1),X0,X0) & v1_funct_1(k2_funct_2(X0,X1))))),
% 4.03/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 4.03/1.00  
% 4.03/1.00  fof(f41,plain,(
% 4.03/1.00    ! [X0,X1] : ((m1_subset_1(k2_funct_2(X0,X1),k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v3_funct_2(k2_funct_2(X0,X1),X0,X0) & v1_funct_2(k2_funct_2(X0,X1),X0,X0) & v1_funct_1(k2_funct_2(X0,X1))) | (~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) | ~v3_funct_2(X1,X0,X0) | ~v1_funct_2(X1,X0,X0) | ~v1_funct_1(X1)))),
% 4.03/1.00    inference(ennf_transformation,[],[f17])).
% 4.03/1.00  
% 4.03/1.00  fof(f42,plain,(
% 4.03/1.00    ! [X0,X1] : ((m1_subset_1(k2_funct_2(X0,X1),k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v3_funct_2(k2_funct_2(X0,X1),X0,X0) & v1_funct_2(k2_funct_2(X0,X1),X0,X0) & v1_funct_1(k2_funct_2(X0,X1))) | ~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) | ~v3_funct_2(X1,X0,X0) | ~v1_funct_2(X1,X0,X0) | ~v1_funct_1(X1))),
% 4.03/1.00    inference(flattening,[],[f41])).
% 4.03/1.00  
% 4.03/1.00  fof(f79,plain,(
% 4.03/1.00    ( ! [X0,X1] : (m1_subset_1(k2_funct_2(X0,X1),k1_zfmisc_1(k2_zfmisc_1(X0,X0))) | ~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) | ~v3_funct_2(X1,X0,X0) | ~v1_funct_2(X1,X0,X0) | ~v1_funct_1(X1)) )),
% 4.03/1.00    inference(cnf_transformation,[],[f42])).
% 4.03/1.00  
% 4.03/1.00  fof(f12,axiom,(
% 4.03/1.00    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => (v5_relat_1(X2,X1) & v4_relat_1(X2,X0)))),
% 4.03/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 4.03/1.00  
% 4.03/1.00  fof(f34,plain,(
% 4.03/1.00    ! [X0,X1,X2] : ((v5_relat_1(X2,X1) & v4_relat_1(X2,X0)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 4.03/1.00    inference(ennf_transformation,[],[f12])).
% 4.03/1.00  
% 4.03/1.00  fof(f67,plain,(
% 4.03/1.00    ( ! [X2,X0,X1] : (v4_relat_1(X2,X0) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 4.03/1.00    inference(cnf_transformation,[],[f34])).
% 4.03/1.00  
% 4.03/1.00  fof(f3,axiom,(
% 4.03/1.00    ! [X0,X1] : (v1_relat_1(X1) => (v4_relat_1(X1,X0) <=> r1_tarski(k1_relat_1(X1),X0)))),
% 4.03/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 4.03/1.00  
% 4.03/1.00  fof(f22,plain,(
% 4.03/1.00    ! [X0,X1] : ((v4_relat_1(X1,X0) <=> r1_tarski(k1_relat_1(X1),X0)) | ~v1_relat_1(X1))),
% 4.03/1.00    inference(ennf_transformation,[],[f3])).
% 4.03/1.00  
% 4.03/1.00  fof(f49,plain,(
% 4.03/1.00    ! [X0,X1] : (((v4_relat_1(X1,X0) | ~r1_tarski(k1_relat_1(X1),X0)) & (r1_tarski(k1_relat_1(X1),X0) | ~v4_relat_1(X1,X0))) | ~v1_relat_1(X1))),
% 4.03/1.00    inference(nnf_transformation,[],[f22])).
% 4.03/1.00  
% 4.03/1.00  fof(f57,plain,(
% 4.03/1.00    ( ! [X0,X1] : (r1_tarski(k1_relat_1(X1),X0) | ~v4_relat_1(X1,X0) | ~v1_relat_1(X1)) )),
% 4.03/1.00    inference(cnf_transformation,[],[f49])).
% 4.03/1.00  
% 4.03/1.00  fof(f4,axiom,(
% 4.03/1.00    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1))),
% 4.03/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 4.03/1.00  
% 4.03/1.00  fof(f59,plain,(
% 4.03/1.00    ( ! [X0,X1] : (v1_relat_1(k2_zfmisc_1(X0,X1))) )),
% 4.03/1.00    inference(cnf_transformation,[],[f4])).
% 4.03/1.00  
% 4.03/1.00  fof(f2,axiom,(
% 4.03/1.00    ! [X0] : (v1_relat_1(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => v1_relat_1(X1)))),
% 4.03/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 4.03/1.00  
% 4.03/1.00  fof(f21,plain,(
% 4.03/1.00    ! [X0] : (! [X1] : (v1_relat_1(X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) | ~v1_relat_1(X0))),
% 4.03/1.00    inference(ennf_transformation,[],[f2])).
% 4.03/1.00  
% 4.03/1.00  fof(f56,plain,(
% 4.03/1.00    ( ! [X0,X1] : (v1_relat_1(X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0)) | ~v1_relat_1(X0)) )),
% 4.03/1.00    inference(cnf_transformation,[],[f21])).
% 4.03/1.00  
% 4.03/1.00  fof(f8,axiom,(
% 4.03/1.00    ! [X0] : (v1_relat_1(X0) => k1_relat_1(X0) = k10_relat_1(X0,k2_relat_1(X0)))),
% 4.03/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 4.03/1.00  
% 4.03/1.00  fof(f27,plain,(
% 4.03/1.00    ! [X0] : (k1_relat_1(X0) = k10_relat_1(X0,k2_relat_1(X0)) | ~v1_relat_1(X0))),
% 4.03/1.00    inference(ennf_transformation,[],[f8])).
% 4.03/1.00  
% 4.03/1.00  fof(f63,plain,(
% 4.03/1.00    ( ! [X0] : (k1_relat_1(X0) = k10_relat_1(X0,k2_relat_1(X0)) | ~v1_relat_1(X0)) )),
% 4.03/1.00    inference(cnf_transformation,[],[f27])).
% 4.03/1.00  
% 4.03/1.00  fof(f15,axiom,(
% 4.03/1.00    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => ((v3_funct_2(X2,X0,X1) & v1_funct_1(X2)) => (v2_funct_2(X2,X1) & v2_funct_1(X2) & v1_funct_1(X2))))),
% 4.03/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 4.03/1.00  
% 4.03/1.00  fof(f37,plain,(
% 4.03/1.00    ! [X0,X1,X2] : (((v2_funct_2(X2,X1) & v2_funct_1(X2) & v1_funct_1(X2)) | (~v3_funct_2(X2,X0,X1) | ~v1_funct_1(X2))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 4.03/1.00    inference(ennf_transformation,[],[f15])).
% 4.03/1.00  
% 4.03/1.00  fof(f38,plain,(
% 4.03/1.00    ! [X0,X1,X2] : ((v2_funct_2(X2,X1) & v2_funct_1(X2) & v1_funct_1(X2)) | ~v3_funct_2(X2,X0,X1) | ~v1_funct_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 4.03/1.00    inference(flattening,[],[f37])).
% 4.03/1.00  
% 4.03/1.00  fof(f73,plain,(
% 4.03/1.00    ( ! [X2,X0,X1] : (v2_funct_2(X2,X1) | ~v3_funct_2(X2,X0,X1) | ~v1_funct_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 4.03/1.00    inference(cnf_transformation,[],[f38])).
% 4.03/1.00  
% 4.03/1.00  fof(f16,axiom,(
% 4.03/1.00    ! [X0,X1] : ((v5_relat_1(X1,X0) & v1_relat_1(X1)) => (v2_funct_2(X1,X0) <=> k2_relat_1(X1) = X0))),
% 4.03/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 4.03/1.00  
% 4.03/1.00  fof(f39,plain,(
% 4.03/1.00    ! [X0,X1] : ((v2_funct_2(X1,X0) <=> k2_relat_1(X1) = X0) | (~v5_relat_1(X1,X0) | ~v1_relat_1(X1)))),
% 4.03/1.00    inference(ennf_transformation,[],[f16])).
% 4.03/1.00  
% 4.03/1.00  fof(f40,plain,(
% 4.03/1.00    ! [X0,X1] : ((v2_funct_2(X1,X0) <=> k2_relat_1(X1) = X0) | ~v5_relat_1(X1,X0) | ~v1_relat_1(X1))),
% 4.03/1.00    inference(flattening,[],[f39])).
% 4.03/1.00  
% 4.03/1.00  fof(f50,plain,(
% 4.03/1.00    ! [X0,X1] : (((v2_funct_2(X1,X0) | k2_relat_1(X1) != X0) & (k2_relat_1(X1) = X0 | ~v2_funct_2(X1,X0))) | ~v5_relat_1(X1,X0) | ~v1_relat_1(X1))),
% 4.03/1.00    inference(nnf_transformation,[],[f40])).
% 4.03/1.00  
% 4.03/1.00  fof(f74,plain,(
% 4.03/1.00    ( ! [X0,X1] : (k2_relat_1(X1) = X0 | ~v2_funct_2(X1,X0) | ~v5_relat_1(X1,X0) | ~v1_relat_1(X1)) )),
% 4.03/1.00    inference(cnf_transformation,[],[f50])).
% 4.03/1.00  
% 4.03/1.00  fof(f68,plain,(
% 4.03/1.00    ( ! [X2,X0,X1] : (v5_relat_1(X2,X1) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 4.03/1.00    inference(cnf_transformation,[],[f34])).
% 4.03/1.00  
% 4.03/1.00  fof(f72,plain,(
% 4.03/1.00    ( ! [X2,X0,X1] : (v2_funct_1(X2) | ~v3_funct_2(X2,X0,X1) | ~v1_funct_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 4.03/1.00    inference(cnf_transformation,[],[f38])).
% 4.03/1.00  
% 4.03/1.00  fof(f10,axiom,(
% 4.03/1.00    ! [X0,X1] : ((v1_funct_1(X1) & v1_relat_1(X1)) => (v2_funct_1(X1) => k9_relat_1(k2_funct_1(X1),X0) = k10_relat_1(X1,X0)))),
% 4.03/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 4.03/1.00  
% 4.03/1.00  fof(f30,plain,(
% 4.03/1.00    ! [X0,X1] : ((k9_relat_1(k2_funct_1(X1),X0) = k10_relat_1(X1,X0) | ~v2_funct_1(X1)) | (~v1_funct_1(X1) | ~v1_relat_1(X1)))),
% 4.03/1.00    inference(ennf_transformation,[],[f10])).
% 4.03/1.00  
% 4.03/1.00  fof(f31,plain,(
% 4.03/1.00    ! [X0,X1] : (k9_relat_1(k2_funct_1(X1),X0) = k10_relat_1(X1,X0) | ~v2_funct_1(X1) | ~v1_funct_1(X1) | ~v1_relat_1(X1))),
% 4.03/1.00    inference(flattening,[],[f30])).
% 4.03/1.00  
% 4.03/1.00  fof(f65,plain,(
% 4.03/1.00    ( ! [X0,X1] : (k9_relat_1(k2_funct_1(X1),X0) = k10_relat_1(X1,X0) | ~v2_funct_1(X1) | ~v1_funct_1(X1) | ~v1_relat_1(X1)) )),
% 4.03/1.00    inference(cnf_transformation,[],[f31])).
% 4.03/1.00  
% 4.03/1.00  fof(f7,axiom,(
% 4.03/1.00    ! [X0,X1,X2] : (v1_relat_1(X2) => (r1_tarski(X0,X1) => r1_tarski(k9_relat_1(X2,X0),k9_relat_1(X2,X1))))),
% 4.03/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 4.03/1.00  
% 4.03/1.00  fof(f25,plain,(
% 4.03/1.00    ! [X0,X1,X2] : ((r1_tarski(k9_relat_1(X2,X0),k9_relat_1(X2,X1)) | ~r1_tarski(X0,X1)) | ~v1_relat_1(X2))),
% 4.03/1.00    inference(ennf_transformation,[],[f7])).
% 4.03/1.00  
% 4.03/1.00  fof(f26,plain,(
% 4.03/1.00    ! [X0,X1,X2] : (r1_tarski(k9_relat_1(X2,X0),k9_relat_1(X2,X1)) | ~r1_tarski(X0,X1) | ~v1_relat_1(X2))),
% 4.03/1.00    inference(flattening,[],[f25])).
% 4.03/1.00  
% 4.03/1.00  fof(f62,plain,(
% 4.03/1.00    ( ! [X2,X0,X1] : (r1_tarski(k9_relat_1(X2,X0),k9_relat_1(X2,X1)) | ~r1_tarski(X0,X1) | ~v1_relat_1(X2)) )),
% 4.03/1.00    inference(cnf_transformation,[],[f26])).
% 4.03/1.00  
% 4.03/1.00  fof(f11,axiom,(
% 4.03/1.00    ! [X0,X1] : ((v1_funct_1(X1) & v1_relat_1(X1)) => ((v2_funct_1(X1) & r1_tarski(X0,k1_relat_1(X1))) => k10_relat_1(X1,k9_relat_1(X1,X0)) = X0))),
% 4.03/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 4.03/1.00  
% 4.03/1.00  fof(f32,plain,(
% 4.03/1.00    ! [X0,X1] : ((k10_relat_1(X1,k9_relat_1(X1,X0)) = X0 | (~v2_funct_1(X1) | ~r1_tarski(X0,k1_relat_1(X1)))) | (~v1_funct_1(X1) | ~v1_relat_1(X1)))),
% 4.03/1.00    inference(ennf_transformation,[],[f11])).
% 4.03/1.00  
% 4.03/1.00  fof(f33,plain,(
% 4.03/1.00    ! [X0,X1] : (k10_relat_1(X1,k9_relat_1(X1,X0)) = X0 | ~v2_funct_1(X1) | ~r1_tarski(X0,k1_relat_1(X1)) | ~v1_funct_1(X1) | ~v1_relat_1(X1))),
% 4.03/1.00    inference(flattening,[],[f32])).
% 4.03/1.00  
% 4.03/1.00  fof(f66,plain,(
% 4.03/1.00    ( ! [X0,X1] : (k10_relat_1(X1,k9_relat_1(X1,X0)) = X0 | ~v2_funct_1(X1) | ~r1_tarski(X0,k1_relat_1(X1)) | ~v1_funct_1(X1) | ~v1_relat_1(X1)) )),
% 4.03/1.00    inference(cnf_transformation,[],[f33])).
% 4.03/1.00  
% 4.03/1.00  fof(f76,plain,(
% 4.03/1.00    ( ! [X0,X1] : (v1_funct_1(k2_funct_2(X0,X1)) | ~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) | ~v3_funct_2(X1,X0,X0) | ~v1_funct_2(X1,X0,X0) | ~v1_funct_1(X1)) )),
% 4.03/1.00    inference(cnf_transformation,[],[f42])).
% 4.03/1.00  
% 4.03/1.00  fof(f78,plain,(
% 4.03/1.00    ( ! [X0,X1] : (v3_funct_2(k2_funct_2(X0,X1),X0,X0) | ~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) | ~v3_funct_2(X1,X0,X0) | ~v1_funct_2(X1,X0,X0) | ~v1_funct_1(X1)) )),
% 4.03/1.00    inference(cnf_transformation,[],[f42])).
% 4.03/1.00  
% 4.03/1.00  fof(f6,axiom,(
% 4.03/1.00    ! [X0] : (v1_relat_1(X0) => k9_relat_1(X0,k1_relat_1(X0)) = k2_relat_1(X0))),
% 4.03/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 4.03/1.00  
% 4.03/1.00  fof(f24,plain,(
% 4.03/1.00    ! [X0] : (k9_relat_1(X0,k1_relat_1(X0)) = k2_relat_1(X0) | ~v1_relat_1(X0))),
% 4.03/1.00    inference(ennf_transformation,[],[f6])).
% 4.03/1.00  
% 4.03/1.00  fof(f61,plain,(
% 4.03/1.00    ( ! [X0] : (k9_relat_1(X0,k1_relat_1(X0)) = k2_relat_1(X0) | ~v1_relat_1(X0)) )),
% 4.03/1.00    inference(cnf_transformation,[],[f24])).
% 4.03/1.00  
% 4.03/1.00  fof(f5,axiom,(
% 4.03/1.00    ! [X0,X1] : (v1_relat_1(X1) => r1_tarski(k9_relat_1(X1,X0),k2_relat_1(X1)))),
% 4.03/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 4.03/1.00  
% 4.03/1.00  fof(f23,plain,(
% 4.03/1.00    ! [X0,X1] : (r1_tarski(k9_relat_1(X1,X0),k2_relat_1(X1)) | ~v1_relat_1(X1))),
% 4.03/1.00    inference(ennf_transformation,[],[f5])).
% 4.03/1.00  
% 4.03/1.00  fof(f60,plain,(
% 4.03/1.00    ( ! [X0,X1] : (r1_tarski(k9_relat_1(X1,X0),k2_relat_1(X1)) | ~v1_relat_1(X1)) )),
% 4.03/1.00    inference(cnf_transformation,[],[f23])).
% 4.03/1.00  
% 4.03/1.00  fof(f1,axiom,(
% 4.03/1.00    ! [X0,X1] : (X0 = X1 <=> (r1_tarski(X1,X0) & r1_tarski(X0,X1)))),
% 4.03/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 4.03/1.00  
% 4.03/1.00  fof(f47,plain,(
% 4.03/1.00    ! [X0,X1] : ((X0 = X1 | (~r1_tarski(X1,X0) | ~r1_tarski(X0,X1))) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 4.03/1.00    inference(nnf_transformation,[],[f1])).
% 4.03/1.00  
% 4.03/1.00  fof(f48,plain,(
% 4.03/1.00    ! [X0,X1] : ((X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 4.03/1.00    inference(flattening,[],[f47])).
% 4.03/1.00  
% 4.03/1.00  fof(f55,plain,(
% 4.03/1.00    ( ! [X0,X1] : (X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) )),
% 4.03/1.00    inference(cnf_transformation,[],[f48])).
% 4.03/1.00  
% 4.03/1.00  fof(f14,axiom,(
% 4.03/1.00    ! [X0,X1,X2,X3] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k10_relat_1(X2,X3) = k8_relset_1(X0,X1,X2,X3))),
% 4.03/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 4.03/1.00  
% 4.03/1.00  fof(f36,plain,(
% 4.03/1.00    ! [X0,X1,X2,X3] : (k10_relat_1(X2,X3) = k8_relset_1(X0,X1,X2,X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 4.03/1.00    inference(ennf_transformation,[],[f14])).
% 4.03/1.00  
% 4.03/1.00  fof(f70,plain,(
% 4.03/1.00    ( ! [X2,X0,X3,X1] : (k10_relat_1(X2,X3) = k8_relset_1(X0,X1,X2,X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 4.03/1.00    inference(cnf_transformation,[],[f36])).
% 4.03/1.00  
% 4.03/1.00  fof(f86,plain,(
% 4.03/1.00    k8_relset_1(sK0,sK0,sK2,k7_relset_1(sK0,sK0,sK2,sK1)) != sK1 | k7_relset_1(sK0,sK0,sK2,k8_relset_1(sK0,sK0,sK2,sK1)) != sK1),
% 4.03/1.00    inference(cnf_transformation,[],[f52])).
% 4.03/1.00  
% 4.03/1.00  fof(f13,axiom,(
% 4.03/1.00    ! [X0,X1,X2,X3] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k9_relat_1(X2,X3) = k7_relset_1(X0,X1,X2,X3))),
% 4.03/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 4.03/1.00  
% 4.03/1.00  fof(f35,plain,(
% 4.03/1.00    ! [X0,X1,X2,X3] : (k9_relat_1(X2,X3) = k7_relset_1(X0,X1,X2,X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 4.03/1.00    inference(ennf_transformation,[],[f13])).
% 4.03/1.00  
% 4.03/1.00  fof(f69,plain,(
% 4.03/1.00    ( ! [X2,X0,X3,X1] : (k9_relat_1(X2,X3) = k7_relset_1(X0,X1,X2,X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 4.03/1.00    inference(cnf_transformation,[],[f35])).
% 4.03/1.00  
% 4.03/1.00  fof(f9,axiom,(
% 4.03/1.00    ! [X0,X1] : ((v1_funct_1(X1) & v1_relat_1(X1)) => (r1_tarski(X0,k2_relat_1(X1)) => k9_relat_1(X1,k10_relat_1(X1,X0)) = X0))),
% 4.03/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 4.03/1.00  
% 4.03/1.00  fof(f28,plain,(
% 4.03/1.00    ! [X0,X1] : ((k9_relat_1(X1,k10_relat_1(X1,X0)) = X0 | ~r1_tarski(X0,k2_relat_1(X1))) | (~v1_funct_1(X1) | ~v1_relat_1(X1)))),
% 4.03/1.00    inference(ennf_transformation,[],[f9])).
% 4.03/1.00  
% 4.03/1.00  fof(f29,plain,(
% 4.03/1.00    ! [X0,X1] : (k9_relat_1(X1,k10_relat_1(X1,X0)) = X0 | ~r1_tarski(X0,k2_relat_1(X1)) | ~v1_funct_1(X1) | ~v1_relat_1(X1))),
% 4.03/1.00    inference(flattening,[],[f28])).
% 4.03/1.00  
% 4.03/1.00  fof(f64,plain,(
% 4.03/1.00    ( ! [X0,X1] : (k9_relat_1(X1,k10_relat_1(X1,X0)) = X0 | ~r1_tarski(X0,k2_relat_1(X1)) | ~v1_funct_1(X1) | ~v1_relat_1(X1)) )),
% 4.03/1.00    inference(cnf_transformation,[],[f29])).
% 4.03/1.00  
% 4.03/1.00  fof(f54,plain,(
% 4.03/1.00    ( ! [X0,X1] : (r1_tarski(X1,X0) | X0 != X1) )),
% 4.03/1.00    inference(cnf_transformation,[],[f48])).
% 4.03/1.00  
% 4.03/1.00  fof(f87,plain,(
% 4.03/1.00    ( ! [X1] : (r1_tarski(X1,X1)) )),
% 4.03/1.00    inference(equality_resolution,[],[f54])).
% 4.03/1.00  
% 4.03/1.00  fof(f85,plain,(
% 4.03/1.00    r1_tarski(sK1,sK0)),
% 4.03/1.00    inference(cnf_transformation,[],[f52])).
% 4.03/1.00  
% 4.03/1.00  cnf(c_30,negated_conjecture,
% 4.03/1.00      ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) ),
% 4.03/1.00      inference(cnf_transformation,[],[f84]) ).
% 4.03/1.00  
% 4.03/1.00  cnf(c_1196,plain,
% 4.03/1.00      ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) = iProver_top ),
% 4.03/1.00      inference(predicate_to_equality,[status(thm)],[c_30]) ).
% 4.03/1.00  
% 4.03/1.00  cnf(c_27,plain,
% 4.03/1.00      ( ~ v1_funct_2(X0,X1,X1)
% 4.03/1.00      | ~ v3_funct_2(X0,X1,X1)
% 4.03/1.00      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X1)))
% 4.03/1.00      | ~ v1_funct_1(X0)
% 4.03/1.00      | k2_funct_2(X1,X0) = k2_funct_1(X0) ),
% 4.03/1.00      inference(cnf_transformation,[],[f80]) ).
% 4.03/1.00  
% 4.03/1.00  cnf(c_1198,plain,
% 4.03/1.00      ( k2_funct_2(X0,X1) = k2_funct_1(X1)
% 4.03/1.00      | v1_funct_2(X1,X0,X0) != iProver_top
% 4.03/1.00      | v3_funct_2(X1,X0,X0) != iProver_top
% 4.03/1.00      | m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) != iProver_top
% 4.03/1.00      | v1_funct_1(X1) != iProver_top ),
% 4.03/1.00      inference(predicate_to_equality,[status(thm)],[c_27]) ).
% 4.03/1.00  
% 4.03/1.00  cnf(c_2726,plain,
% 4.03/1.00      ( k2_funct_2(sK0,sK2) = k2_funct_1(sK2)
% 4.03/1.00      | v1_funct_2(sK2,sK0,sK0) != iProver_top
% 4.03/1.00      | v3_funct_2(sK2,sK0,sK0) != iProver_top
% 4.03/1.00      | v1_funct_1(sK2) != iProver_top ),
% 4.03/1.00      inference(superposition,[status(thm)],[c_1196,c_1198]) ).
% 4.03/1.00  
% 4.03/1.00  cnf(c_33,negated_conjecture,
% 4.03/1.00      ( v1_funct_1(sK2) ),
% 4.03/1.00      inference(cnf_transformation,[],[f81]) ).
% 4.03/1.00  
% 4.03/1.00  cnf(c_34,plain,
% 4.03/1.00      ( v1_funct_1(sK2) = iProver_top ),
% 4.03/1.00      inference(predicate_to_equality,[status(thm)],[c_33]) ).
% 4.03/1.00  
% 4.03/1.00  cnf(c_32,negated_conjecture,
% 4.03/1.00      ( v1_funct_2(sK2,sK0,sK0) ),
% 4.03/1.00      inference(cnf_transformation,[],[f82]) ).
% 4.03/1.00  
% 4.03/1.00  cnf(c_35,plain,
% 4.03/1.00      ( v1_funct_2(sK2,sK0,sK0) = iProver_top ),
% 4.03/1.00      inference(predicate_to_equality,[status(thm)],[c_32]) ).
% 4.03/1.00  
% 4.03/1.00  cnf(c_31,negated_conjecture,
% 4.03/1.00      ( v3_funct_2(sK2,sK0,sK0) ),
% 4.03/1.00      inference(cnf_transformation,[],[f83]) ).
% 4.03/1.00  
% 4.03/1.00  cnf(c_36,plain,
% 4.03/1.00      ( v3_funct_2(sK2,sK0,sK0) = iProver_top ),
% 4.03/1.00      inference(predicate_to_equality,[status(thm)],[c_31]) ).
% 4.03/1.00  
% 4.03/1.00  cnf(c_2969,plain,
% 4.03/1.00      ( k2_funct_2(sK0,sK2) = k2_funct_1(sK2) ),
% 4.03/1.00      inference(global_propositional_subsumption,
% 4.03/1.00                [status(thm)],
% 4.03/1.00                [c_2726,c_34,c_35,c_36]) ).
% 4.03/1.00  
% 4.03/1.00  cnf(c_23,plain,
% 4.03/1.00      ( ~ v1_funct_2(X0,X1,X1)
% 4.03/1.00      | ~ v3_funct_2(X0,X1,X1)
% 4.03/1.00      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X1)))
% 4.03/1.00      | m1_subset_1(k2_funct_2(X1,X0),k1_zfmisc_1(k2_zfmisc_1(X1,X1)))
% 4.03/1.00      | ~ v1_funct_1(X0) ),
% 4.03/1.00      inference(cnf_transformation,[],[f79]) ).
% 4.03/1.00  
% 4.03/1.00  cnf(c_1202,plain,
% 4.03/1.00      ( v1_funct_2(X0,X1,X1) != iProver_top
% 4.03/1.00      | v3_funct_2(X0,X1,X1) != iProver_top
% 4.03/1.00      | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X1))) != iProver_top
% 4.03/1.00      | m1_subset_1(k2_funct_2(X1,X0),k1_zfmisc_1(k2_zfmisc_1(X1,X1))) = iProver_top
% 4.03/1.00      | v1_funct_1(X0) != iProver_top ),
% 4.03/1.00      inference(predicate_to_equality,[status(thm)],[c_23]) ).
% 4.03/1.00  
% 4.03/1.00  cnf(c_3376,plain,
% 4.03/1.00      ( v1_funct_2(sK2,sK0,sK0) != iProver_top
% 4.03/1.00      | v3_funct_2(sK2,sK0,sK0) != iProver_top
% 4.03/1.00      | m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) = iProver_top
% 4.03/1.00      | m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) != iProver_top
% 4.03/1.00      | v1_funct_1(sK2) != iProver_top ),
% 4.03/1.00      inference(superposition,[status(thm)],[c_2969,c_1202]) ).
% 4.03/1.00  
% 4.03/1.00  cnf(c_37,plain,
% 4.03/1.00      ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) = iProver_top ),
% 4.03/1.00      inference(predicate_to_equality,[status(thm)],[c_30]) ).
% 4.03/1.00  
% 4.03/1.00  cnf(c_3872,plain,
% 4.03/1.00      ( m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) = iProver_top ),
% 4.03/1.00      inference(global_propositional_subsumption,
% 4.03/1.00                [status(thm)],
% 4.03/1.00                [c_3376,c_34,c_35,c_36,c_37]) ).
% 4.03/1.00  
% 4.03/1.00  cnf(c_15,plain,
% 4.03/1.00      ( v4_relat_1(X0,X1)
% 4.03/1.00      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) ),
% 4.03/1.00      inference(cnf_transformation,[],[f67]) ).
% 4.03/1.00  
% 4.03/1.00  cnf(c_5,plain,
% 4.03/1.00      ( ~ v4_relat_1(X0,X1)
% 4.03/1.00      | r1_tarski(k1_relat_1(X0),X1)
% 4.03/1.00      | ~ v1_relat_1(X0) ),
% 4.03/1.00      inference(cnf_transformation,[],[f57]) ).
% 4.03/1.00  
% 4.03/1.00  cnf(c_363,plain,
% 4.03/1.00      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 4.03/1.00      | r1_tarski(k1_relat_1(X0),X1)
% 4.03/1.00      | ~ v1_relat_1(X0) ),
% 4.03/1.00      inference(resolution,[status(thm)],[c_15,c_5]) ).
% 4.03/1.00  
% 4.03/1.00  cnf(c_1192,plain,
% 4.03/1.00      ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) != iProver_top
% 4.03/1.00      | r1_tarski(k1_relat_1(X0),X1) = iProver_top
% 4.03/1.00      | v1_relat_1(X0) != iProver_top ),
% 4.03/1.00      inference(predicate_to_equality,[status(thm)],[c_363]) ).
% 4.03/1.00  
% 4.03/1.00  cnf(c_3881,plain,
% 4.03/1.00      ( r1_tarski(k1_relat_1(k2_funct_1(sK2)),sK0) = iProver_top
% 4.03/1.00      | v1_relat_1(k2_funct_1(sK2)) != iProver_top ),
% 4.03/1.00      inference(superposition,[status(thm)],[c_3872,c_1192]) ).
% 4.03/1.00  
% 4.03/1.00  cnf(c_6,plain,
% 4.03/1.00      ( v1_relat_1(k2_zfmisc_1(X0,X1)) ),
% 4.03/1.00      inference(cnf_transformation,[],[f59]) ).
% 4.03/1.00  
% 4.03/1.00  cnf(c_100,plain,
% 4.03/1.00      ( v1_relat_1(k2_zfmisc_1(X0,X1)) = iProver_top ),
% 4.03/1.00      inference(predicate_to_equality,[status(thm)],[c_6]) ).
% 4.03/1.00  
% 4.03/1.00  cnf(c_102,plain,
% 4.03/1.00      ( v1_relat_1(k2_zfmisc_1(sK0,sK0)) = iProver_top ),
% 4.03/1.00      inference(instantiation,[status(thm)],[c_100]) ).
% 4.03/1.00  
% 4.03/1.00  cnf(c_3,plain,
% 4.03/1.00      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
% 4.03/1.00      | ~ v1_relat_1(X1)
% 4.03/1.00      | v1_relat_1(X0) ),
% 4.03/1.00      inference(cnf_transformation,[],[f56]) ).
% 4.03/1.00  
% 4.03/1.00  cnf(c_1214,plain,
% 4.03/1.00      ( m1_subset_1(X0,k1_zfmisc_1(X1)) != iProver_top
% 4.03/1.00      | v1_relat_1(X1) != iProver_top
% 4.03/1.00      | v1_relat_1(X0) = iProver_top ),
% 4.03/1.00      inference(predicate_to_equality,[status(thm)],[c_3]) ).
% 4.03/1.00  
% 4.03/1.00  cnf(c_3876,plain,
% 4.03/1.00      ( v1_relat_1(k2_zfmisc_1(sK0,sK0)) != iProver_top
% 4.03/1.00      | v1_relat_1(k2_funct_1(sK2)) = iProver_top ),
% 4.03/1.00      inference(superposition,[status(thm)],[c_3872,c_1214]) ).
% 4.03/1.00  
% 4.03/1.00  cnf(c_4403,plain,
% 4.03/1.00      ( r1_tarski(k1_relat_1(k2_funct_1(sK2)),sK0) = iProver_top ),
% 4.03/1.00      inference(global_propositional_subsumption,
% 4.03/1.00                [status(thm)],
% 4.03/1.00                [c_3881,c_102,c_3876]) ).
% 4.03/1.00  
% 4.03/1.00  cnf(c_1958,plain,
% 4.03/1.00      ( v1_relat_1(k2_zfmisc_1(sK0,sK0)) != iProver_top
% 4.03/1.00      | v1_relat_1(sK2) = iProver_top ),
% 4.03/1.00      inference(superposition,[status(thm)],[c_1196,c_1214]) ).
% 4.03/1.00  
% 4.03/1.00  cnf(c_1377,plain,
% 4.03/1.00      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 4.03/1.00      | v1_relat_1(X0)
% 4.03/1.00      | ~ v1_relat_1(k2_zfmisc_1(X1,X2)) ),
% 4.03/1.00      inference(instantiation,[status(thm)],[c_3]) ).
% 4.03/1.00  
% 4.03/1.00  cnf(c_1496,plain,
% 4.03/1.00      ( ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
% 4.03/1.00      | ~ v1_relat_1(k2_zfmisc_1(sK0,sK0))
% 4.03/1.00      | v1_relat_1(sK2) ),
% 4.03/1.00      inference(instantiation,[status(thm)],[c_1377]) ).
% 4.03/1.00  
% 4.03/1.00  cnf(c_1497,plain,
% 4.03/1.00      ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) != iProver_top
% 4.03/1.00      | v1_relat_1(k2_zfmisc_1(sK0,sK0)) != iProver_top
% 4.03/1.00      | v1_relat_1(sK2) = iProver_top ),
% 4.03/1.00      inference(predicate_to_equality,[status(thm)],[c_1496]) ).
% 4.03/1.00  
% 4.03/1.00  cnf(c_2090,plain,
% 4.03/1.00      ( v1_relat_1(sK2) = iProver_top ),
% 4.03/1.00      inference(global_propositional_subsumption,
% 4.03/1.00                [status(thm)],
% 4.03/1.00                [c_1958,c_37,c_102,c_1497]) ).
% 4.03/1.00  
% 4.03/1.00  cnf(c_10,plain,
% 4.03/1.00      ( ~ v1_relat_1(X0)
% 4.03/1.00      | k10_relat_1(X0,k2_relat_1(X0)) = k1_relat_1(X0) ),
% 4.03/1.00      inference(cnf_transformation,[],[f63]) ).
% 4.03/1.00  
% 4.03/1.00  cnf(c_1209,plain,
% 4.03/1.00      ( k10_relat_1(X0,k2_relat_1(X0)) = k1_relat_1(X0)
% 4.03/1.00      | v1_relat_1(X0) != iProver_top ),
% 4.03/1.00      inference(predicate_to_equality,[status(thm)],[c_10]) ).
% 4.03/1.00  
% 4.03/1.00  cnf(c_2095,plain,
% 4.03/1.00      ( k10_relat_1(sK2,k2_relat_1(sK2)) = k1_relat_1(sK2) ),
% 4.03/1.00      inference(superposition,[status(thm)],[c_2090,c_1209]) ).
% 4.03/1.00  
% 4.03/1.00  cnf(c_18,plain,
% 4.03/1.00      ( ~ v3_funct_2(X0,X1,X2)
% 4.03/1.00      | v2_funct_2(X0,X2)
% 4.03/1.00      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 4.03/1.00      | ~ v1_funct_1(X0) ),
% 4.03/1.00      inference(cnf_transformation,[],[f73]) ).
% 4.03/1.00  
% 4.03/1.00  cnf(c_22,plain,
% 4.03/1.00      ( ~ v2_funct_2(X0,X1)
% 4.03/1.00      | ~ v5_relat_1(X0,X1)
% 4.03/1.00      | ~ v1_relat_1(X0)
% 4.03/1.00      | k2_relat_1(X0) = X1 ),
% 4.03/1.00      inference(cnf_transformation,[],[f74]) ).
% 4.03/1.00  
% 4.03/1.00  cnf(c_421,plain,
% 4.03/1.00      ( ~ v3_funct_2(X0,X1,X2)
% 4.03/1.00      | ~ v5_relat_1(X3,X4)
% 4.03/1.00      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 4.03/1.00      | ~ v1_funct_1(X0)
% 4.03/1.00      | ~ v1_relat_1(X3)
% 4.03/1.00      | X3 != X0
% 4.03/1.00      | X4 != X2
% 4.03/1.00      | k2_relat_1(X3) = X4 ),
% 4.03/1.00      inference(resolution_lifted,[status(thm)],[c_18,c_22]) ).
% 4.03/1.00  
% 4.03/1.00  cnf(c_422,plain,
% 4.03/1.00      ( ~ v3_funct_2(X0,X1,X2)
% 4.03/1.00      | ~ v5_relat_1(X0,X2)
% 4.03/1.00      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 4.03/1.00      | ~ v1_funct_1(X0)
% 4.03/1.00      | ~ v1_relat_1(X0)
% 4.03/1.00      | k2_relat_1(X0) = X2 ),
% 4.03/1.00      inference(unflattening,[status(thm)],[c_421]) ).
% 4.03/1.00  
% 4.03/1.00  cnf(c_14,plain,
% 4.03/1.00      ( v5_relat_1(X0,X1)
% 4.03/1.00      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) ),
% 4.03/1.00      inference(cnf_transformation,[],[f68]) ).
% 4.03/1.00  
% 4.03/1.00  cnf(c_438,plain,
% 4.03/1.00      ( ~ v3_funct_2(X0,X1,X2)
% 4.03/1.00      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 4.03/1.00      | ~ v1_funct_1(X0)
% 4.03/1.00      | ~ v1_relat_1(X0)
% 4.03/1.00      | k2_relat_1(X0) = X2 ),
% 4.03/1.00      inference(forward_subsumption_resolution,
% 4.03/1.00                [status(thm)],
% 4.03/1.00                [c_422,c_14]) ).
% 4.03/1.00  
% 4.03/1.00  cnf(c_1191,plain,
% 4.03/1.00      ( k2_relat_1(X0) = X1
% 4.03/1.00      | v3_funct_2(X0,X2,X1) != iProver_top
% 4.03/1.00      | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) != iProver_top
% 4.03/1.00      | v1_funct_1(X0) != iProver_top
% 4.03/1.00      | v1_relat_1(X0) != iProver_top ),
% 4.03/1.00      inference(predicate_to_equality,[status(thm)],[c_438]) ).
% 4.03/1.00  
% 4.03/1.00  cnf(c_1557,plain,
% 4.03/1.00      ( k2_relat_1(sK2) = sK0
% 4.03/1.00      | v3_funct_2(sK2,sK0,sK0) != iProver_top
% 4.03/1.00      | v1_funct_1(sK2) != iProver_top
% 4.03/1.00      | v1_relat_1(sK2) != iProver_top ),
% 4.03/1.00      inference(superposition,[status(thm)],[c_1196,c_1191]) ).
% 4.03/1.00  
% 4.03/1.00  cnf(c_1774,plain,
% 4.03/1.00      ( k2_relat_1(sK2) = sK0 ),
% 4.03/1.00      inference(global_propositional_subsumption,
% 4.03/1.00                [status(thm)],
% 4.03/1.00                [c_1557,c_34,c_36,c_37,c_102,c_1497]) ).
% 4.03/1.00  
% 4.03/1.00  cnf(c_2096,plain,
% 4.03/1.00      ( k10_relat_1(sK2,sK0) = k1_relat_1(sK2) ),
% 4.03/1.00      inference(light_normalisation,[status(thm)],[c_2095,c_1774]) ).
% 4.03/1.00  
% 4.03/1.00  cnf(c_19,plain,
% 4.03/1.00      ( ~ v3_funct_2(X0,X1,X2)
% 4.03/1.00      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 4.03/1.00      | v2_funct_1(X0)
% 4.03/1.00      | ~ v1_funct_1(X0) ),
% 4.03/1.00      inference(cnf_transformation,[],[f72]) ).
% 4.03/1.00  
% 4.03/1.00  cnf(c_1203,plain,
% 4.03/1.00      ( v3_funct_2(X0,X1,X2) != iProver_top
% 4.03/1.00      | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) != iProver_top
% 4.03/1.00      | v2_funct_1(X0) = iProver_top
% 4.03/1.00      | v1_funct_1(X0) != iProver_top ),
% 4.03/1.00      inference(predicate_to_equality,[status(thm)],[c_19]) ).
% 4.03/1.00  
% 4.03/1.00  cnf(c_2817,plain,
% 4.03/1.00      ( v3_funct_2(sK2,sK0,sK0) != iProver_top
% 4.03/1.00      | v2_funct_1(sK2) = iProver_top
% 4.03/1.00      | v1_funct_1(sK2) != iProver_top ),
% 4.03/1.00      inference(superposition,[status(thm)],[c_1196,c_1203]) ).
% 4.03/1.00  
% 4.03/1.00  cnf(c_1601,plain,
% 4.03/1.00      ( ~ v3_funct_2(sK2,X0,X1)
% 4.03/1.00      | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
% 4.03/1.00      | v2_funct_1(sK2)
% 4.03/1.00      | ~ v1_funct_1(sK2) ),
% 4.03/1.00      inference(instantiation,[status(thm)],[c_19]) ).
% 4.03/1.00  
% 4.03/1.00  cnf(c_1602,plain,
% 4.03/1.00      ( v3_funct_2(sK2,X0,X1) != iProver_top
% 4.03/1.00      | m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top
% 4.03/1.00      | v2_funct_1(sK2) = iProver_top
% 4.03/1.00      | v1_funct_1(sK2) != iProver_top ),
% 4.03/1.00      inference(predicate_to_equality,[status(thm)],[c_1601]) ).
% 4.03/1.00  
% 4.03/1.00  cnf(c_1604,plain,
% 4.03/1.00      ( v3_funct_2(sK2,sK0,sK0) != iProver_top
% 4.03/1.00      | m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) != iProver_top
% 4.03/1.00      | v2_funct_1(sK2) = iProver_top
% 4.03/1.00      | v1_funct_1(sK2) != iProver_top ),
% 4.03/1.00      inference(instantiation,[status(thm)],[c_1602]) ).
% 4.03/1.00  
% 4.03/1.00  cnf(c_2901,plain,
% 4.03/1.00      ( v2_funct_1(sK2) = iProver_top ),
% 4.03/1.00      inference(global_propositional_subsumption,
% 4.03/1.00                [status(thm)],
% 4.03/1.00                [c_2817,c_34,c_36,c_37,c_1604]) ).
% 4.03/1.00  
% 4.03/1.00  cnf(c_12,plain,
% 4.03/1.00      ( ~ v2_funct_1(X0)
% 4.03/1.00      | ~ v1_funct_1(X0)
% 4.03/1.00      | ~ v1_relat_1(X0)
% 4.03/1.00      | k9_relat_1(k2_funct_1(X0),X1) = k10_relat_1(X0,X1) ),
% 4.03/1.00      inference(cnf_transformation,[],[f65]) ).
% 4.03/1.00  
% 4.03/1.00  cnf(c_1207,plain,
% 4.03/1.00      ( k9_relat_1(k2_funct_1(X0),X1) = k10_relat_1(X0,X1)
% 4.03/1.00      | v2_funct_1(X0) != iProver_top
% 4.03/1.00      | v1_funct_1(X0) != iProver_top
% 4.03/1.00      | v1_relat_1(X0) != iProver_top ),
% 4.03/1.00      inference(predicate_to_equality,[status(thm)],[c_12]) ).
% 4.03/1.00  
% 4.03/1.00  cnf(c_2905,plain,
% 4.03/1.00      ( k9_relat_1(k2_funct_1(sK2),X0) = k10_relat_1(sK2,X0)
% 4.03/1.00      | v1_funct_1(sK2) != iProver_top
% 4.03/1.00      | v1_relat_1(sK2) != iProver_top ),
% 4.03/1.00      inference(superposition,[status(thm)],[c_2901,c_1207]) ).
% 4.03/1.00  
% 4.03/1.00  cnf(c_3047,plain,
% 4.03/1.00      ( k9_relat_1(k2_funct_1(sK2),X0) = k10_relat_1(sK2,X0) ),
% 4.03/1.00      inference(global_propositional_subsumption,
% 4.03/1.00                [status(thm)],
% 4.03/1.00                [c_2905,c_34,c_37,c_102,c_1497]) ).
% 4.03/1.00  
% 4.03/1.00  cnf(c_9,plain,
% 4.03/1.00      ( ~ r1_tarski(X0,X1)
% 4.03/1.00      | r1_tarski(k9_relat_1(X2,X0),k9_relat_1(X2,X1))
% 4.03/1.00      | ~ v1_relat_1(X2) ),
% 4.03/1.00      inference(cnf_transformation,[],[f62]) ).
% 4.03/1.00  
% 4.03/1.00  cnf(c_1210,plain,
% 4.03/1.00      ( r1_tarski(X0,X1) != iProver_top
% 4.03/1.00      | r1_tarski(k9_relat_1(X2,X0),k9_relat_1(X2,X1)) = iProver_top
% 4.03/1.00      | v1_relat_1(X2) != iProver_top ),
% 4.03/1.00      inference(predicate_to_equality,[status(thm)],[c_9]) ).
% 4.03/1.00  
% 4.03/1.00  cnf(c_3052,plain,
% 4.03/1.00      ( r1_tarski(X0,X1) != iProver_top
% 4.03/1.00      | r1_tarski(k9_relat_1(k2_funct_1(sK2),X0),k10_relat_1(sK2,X1)) = iProver_top
% 4.03/1.00      | v1_relat_1(k2_funct_1(sK2)) != iProver_top ),
% 4.03/1.00      inference(superposition,[status(thm)],[c_3047,c_1210]) ).
% 4.03/1.00  
% 4.03/1.00  cnf(c_3053,plain,
% 4.03/1.00      ( r1_tarski(X0,X1) != iProver_top
% 4.03/1.00      | r1_tarski(k10_relat_1(sK2,X0),k10_relat_1(sK2,X1)) = iProver_top
% 4.03/1.00      | v1_relat_1(k2_funct_1(sK2)) != iProver_top ),
% 4.03/1.00      inference(light_normalisation,[status(thm)],[c_3052,c_3047]) ).
% 4.03/1.00  
% 4.03/1.00  cnf(c_4629,plain,
% 4.03/1.00      ( r1_tarski(k10_relat_1(sK2,X0),k10_relat_1(sK2,X1)) = iProver_top
% 4.03/1.00      | r1_tarski(X0,X1) != iProver_top ),
% 4.03/1.00      inference(global_propositional_subsumption,
% 4.03/1.00                [status(thm)],
% 4.03/1.00                [c_3053,c_102,c_3876]) ).
% 4.03/1.00  
% 4.03/1.00  cnf(c_4630,plain,
% 4.03/1.00      ( r1_tarski(X0,X1) != iProver_top
% 4.03/1.00      | r1_tarski(k10_relat_1(sK2,X0),k10_relat_1(sK2,X1)) = iProver_top ),
% 4.03/1.00      inference(renaming,[status(thm)],[c_4629]) ).
% 4.03/1.00  
% 4.03/1.00  cnf(c_4637,plain,
% 4.03/1.00      ( r1_tarski(X0,sK0) != iProver_top
% 4.03/1.00      | r1_tarski(k10_relat_1(sK2,X0),k1_relat_1(sK2)) = iProver_top ),
% 4.03/1.00      inference(superposition,[status(thm)],[c_2096,c_4630]) ).
% 4.03/1.00  
% 4.03/1.00  cnf(c_13,plain,
% 4.03/1.00      ( ~ r1_tarski(X0,k1_relat_1(X1))
% 4.03/1.00      | ~ v2_funct_1(X1)
% 4.03/1.00      | ~ v1_funct_1(X1)
% 4.03/1.00      | ~ v1_relat_1(X1)
% 4.03/1.00      | k10_relat_1(X1,k9_relat_1(X1,X0)) = X0 ),
% 4.03/1.00      inference(cnf_transformation,[],[f66]) ).
% 4.03/1.00  
% 4.03/1.00  cnf(c_1206,plain,
% 4.03/1.00      ( k10_relat_1(X0,k9_relat_1(X0,X1)) = X1
% 4.03/1.00      | r1_tarski(X1,k1_relat_1(X0)) != iProver_top
% 4.03/1.00      | v2_funct_1(X0) != iProver_top
% 4.03/1.00      | v1_funct_1(X0) != iProver_top
% 4.03/1.00      | v1_relat_1(X0) != iProver_top ),
% 4.03/1.00      inference(predicate_to_equality,[status(thm)],[c_13]) ).
% 4.03/1.00  
% 4.03/1.00  cnf(c_4952,plain,
% 4.03/1.00      ( k10_relat_1(sK2,k9_relat_1(sK2,k10_relat_1(sK2,X0))) = k10_relat_1(sK2,X0)
% 4.03/1.00      | r1_tarski(X0,sK0) != iProver_top
% 4.03/1.00      | v2_funct_1(sK2) != iProver_top
% 4.03/1.00      | v1_funct_1(sK2) != iProver_top
% 4.03/1.00      | v1_relat_1(sK2) != iProver_top ),
% 4.03/1.00      inference(superposition,[status(thm)],[c_4637,c_1206]) ).
% 4.03/1.00  
% 4.03/1.00  cnf(c_9224,plain,
% 4.03/1.00      ( r1_tarski(X0,sK0) != iProver_top
% 4.03/1.00      | k10_relat_1(sK2,k9_relat_1(sK2,k10_relat_1(sK2,X0))) = k10_relat_1(sK2,X0) ),
% 4.03/1.00      inference(global_propositional_subsumption,
% 4.03/1.00                [status(thm)],
% 4.03/1.00                [c_4952,c_34,c_36,c_37,c_102,c_1497,c_1604]) ).
% 4.03/1.00  
% 4.03/1.00  cnf(c_9225,plain,
% 4.03/1.00      ( k10_relat_1(sK2,k9_relat_1(sK2,k10_relat_1(sK2,X0))) = k10_relat_1(sK2,X0)
% 4.03/1.00      | r1_tarski(X0,sK0) != iProver_top ),
% 4.03/1.00      inference(renaming,[status(thm)],[c_9224]) ).
% 4.03/1.00  
% 4.03/1.00  cnf(c_9234,plain,
% 4.03/1.00      ( k10_relat_1(sK2,k9_relat_1(sK2,k10_relat_1(sK2,k1_relat_1(k2_funct_1(sK2))))) = k10_relat_1(sK2,k1_relat_1(k2_funct_1(sK2))) ),
% 4.03/1.00      inference(superposition,[status(thm)],[c_4403,c_9225]) ).
% 4.03/1.00  
% 4.03/1.00  cnf(c_3879,plain,
% 4.03/1.00      ( k2_relat_1(k2_funct_1(sK2)) = sK0
% 4.03/1.00      | v3_funct_2(k2_funct_1(sK2),sK0,sK0) != iProver_top
% 4.03/1.00      | v1_funct_1(k2_funct_1(sK2)) != iProver_top
% 4.03/1.00      | v1_relat_1(k2_funct_1(sK2)) != iProver_top ),
% 4.03/1.00      inference(superposition,[status(thm)],[c_3872,c_1191]) ).
% 4.03/1.00  
% 4.03/1.00  cnf(c_26,plain,
% 4.03/1.00      ( ~ v1_funct_2(X0,X1,X1)
% 4.03/1.00      | ~ v3_funct_2(X0,X1,X1)
% 4.03/1.00      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X1)))
% 4.03/1.00      | ~ v1_funct_1(X0)
% 4.03/1.00      | v1_funct_1(k2_funct_2(X1,X0)) ),
% 4.03/1.00      inference(cnf_transformation,[],[f76]) ).
% 4.03/1.00  
% 4.03/1.00  cnf(c_1199,plain,
% 4.03/1.00      ( v1_funct_2(X0,X1,X1) != iProver_top
% 4.03/1.00      | v3_funct_2(X0,X1,X1) != iProver_top
% 4.03/1.00      | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X1))) != iProver_top
% 4.03/1.00      | v1_funct_1(X0) != iProver_top
% 4.03/1.00      | v1_funct_1(k2_funct_2(X1,X0)) = iProver_top ),
% 4.03/1.00      inference(predicate_to_equality,[status(thm)],[c_26]) ).
% 4.03/1.00  
% 4.03/1.00  cnf(c_2898,plain,
% 4.03/1.00      ( v1_funct_2(sK2,sK0,sK0) != iProver_top
% 4.03/1.00      | v3_funct_2(sK2,sK0,sK0) != iProver_top
% 4.03/1.00      | v1_funct_1(k2_funct_2(sK0,sK2)) = iProver_top
% 4.03/1.00      | v1_funct_1(sK2) != iProver_top ),
% 4.03/1.00      inference(superposition,[status(thm)],[c_1196,c_1199]) ).
% 4.03/1.00  
% 4.03/1.00  cnf(c_1818,plain,
% 4.03/1.00      ( ~ v1_funct_2(sK2,X0,X0)
% 4.03/1.00      | ~ v3_funct_2(sK2,X0,X0)
% 4.03/1.00      | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
% 4.03/1.00      | v1_funct_1(k2_funct_2(X0,sK2))
% 4.03/1.00      | ~ v1_funct_1(sK2) ),
% 4.03/1.00      inference(instantiation,[status(thm)],[c_26]) ).
% 4.03/1.00  
% 4.03/1.00  cnf(c_1819,plain,
% 4.03/1.00      ( v1_funct_2(sK2,X0,X0) != iProver_top
% 4.03/1.00      | v3_funct_2(sK2,X0,X0) != iProver_top
% 4.03/1.00      | m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) != iProver_top
% 4.03/1.00      | v1_funct_1(k2_funct_2(X0,sK2)) = iProver_top
% 4.03/1.00      | v1_funct_1(sK2) != iProver_top ),
% 4.03/1.00      inference(predicate_to_equality,[status(thm)],[c_1818]) ).
% 4.03/1.00  
% 4.03/1.00  cnf(c_1821,plain,
% 4.03/1.00      ( v1_funct_2(sK2,sK0,sK0) != iProver_top
% 4.03/1.00      | v3_funct_2(sK2,sK0,sK0) != iProver_top
% 4.03/1.00      | m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) != iProver_top
% 4.03/1.00      | v1_funct_1(k2_funct_2(sK0,sK2)) = iProver_top
% 4.03/1.00      | v1_funct_1(sK2) != iProver_top ),
% 4.03/1.00      inference(instantiation,[status(thm)],[c_1819]) ).
% 4.03/1.00  
% 4.03/1.00  cnf(c_2972,plain,
% 4.03/1.00      ( v1_funct_1(k2_funct_2(sK0,sK2)) = iProver_top ),
% 4.03/1.00      inference(global_propositional_subsumption,
% 4.03/1.00                [status(thm)],
% 4.03/1.00                [c_2898,c_34,c_35,c_36,c_37,c_1821]) ).
% 4.03/1.00  
% 4.03/1.00  cnf(c_2976,plain,
% 4.03/1.00      ( v1_funct_1(k2_funct_1(sK2)) = iProver_top ),
% 4.03/1.00      inference(light_normalisation,[status(thm)],[c_2972,c_2969]) ).
% 4.03/1.00  
% 4.03/1.00  cnf(c_24,plain,
% 4.03/1.00      ( ~ v1_funct_2(X0,X1,X1)
% 4.03/1.00      | ~ v3_funct_2(X0,X1,X1)
% 4.03/1.00      | v3_funct_2(k2_funct_2(X1,X0),X1,X1)
% 4.03/1.00      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X1)))
% 4.03/1.00      | ~ v1_funct_1(X0) ),
% 4.03/1.00      inference(cnf_transformation,[],[f78]) ).
% 4.03/1.00  
% 4.03/1.00  cnf(c_1201,plain,
% 4.03/1.00      ( v1_funct_2(X0,X1,X1) != iProver_top
% 4.03/1.00      | v3_funct_2(X0,X1,X1) != iProver_top
% 4.03/1.00      | v3_funct_2(k2_funct_2(X1,X0),X1,X1) = iProver_top
% 4.03/1.00      | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X1))) != iProver_top
% 4.03/1.00      | v1_funct_1(X0) != iProver_top ),
% 4.03/1.00      inference(predicate_to_equality,[status(thm)],[c_24]) ).
% 4.03/1.00  
% 4.03/1.00  cnf(c_3372,plain,
% 4.03/1.00      ( v1_funct_2(sK2,sK0,sK0) != iProver_top
% 4.03/1.00      | v3_funct_2(k2_funct_2(sK0,sK2),sK0,sK0) = iProver_top
% 4.03/1.00      | v3_funct_2(sK2,sK0,sK0) != iProver_top
% 4.03/1.00      | v1_funct_1(sK2) != iProver_top ),
% 4.03/1.00      inference(superposition,[status(thm)],[c_1196,c_1201]) ).
% 4.03/1.00  
% 4.03/1.00  cnf(c_3373,plain,
% 4.03/1.00      ( v1_funct_2(sK2,sK0,sK0) != iProver_top
% 4.03/1.00      | v3_funct_2(k2_funct_1(sK2),sK0,sK0) = iProver_top
% 4.03/1.00      | v3_funct_2(sK2,sK0,sK0) != iProver_top
% 4.03/1.00      | v1_funct_1(sK2) != iProver_top ),
% 4.03/1.00      inference(light_normalisation,[status(thm)],[c_3372,c_2969]) ).
% 4.03/1.00  
% 4.03/1.00  cnf(c_6310,plain,
% 4.03/1.00      ( k2_relat_1(k2_funct_1(sK2)) = sK0 ),
% 4.03/1.00      inference(global_propositional_subsumption,
% 4.03/1.00                [status(thm)],
% 4.03/1.00                [c_3879,c_34,c_35,c_36,c_102,c_2976,c_3373,c_3876]) ).
% 4.03/1.00  
% 4.03/1.00  cnf(c_4137,plain,
% 4.03/1.00      ( v1_relat_1(k2_funct_1(sK2)) = iProver_top ),
% 4.03/1.00      inference(global_propositional_subsumption,
% 4.03/1.00                [status(thm)],
% 4.03/1.00                [c_3876,c_102]) ).
% 4.03/1.00  
% 4.03/1.00  cnf(c_8,plain,
% 4.03/1.00      ( ~ v1_relat_1(X0)
% 4.03/1.00      | k9_relat_1(X0,k1_relat_1(X0)) = k2_relat_1(X0) ),
% 4.03/1.00      inference(cnf_transformation,[],[f61]) ).
% 4.03/1.00  
% 4.03/1.00  cnf(c_1211,plain,
% 4.03/1.00      ( k9_relat_1(X0,k1_relat_1(X0)) = k2_relat_1(X0)
% 4.03/1.00      | v1_relat_1(X0) != iProver_top ),
% 4.03/1.00      inference(predicate_to_equality,[status(thm)],[c_8]) ).
% 4.03/1.00  
% 4.03/1.00  cnf(c_4141,plain,
% 4.03/1.00      ( k9_relat_1(k2_funct_1(sK2),k1_relat_1(k2_funct_1(sK2))) = k2_relat_1(k2_funct_1(sK2)) ),
% 4.03/1.00      inference(superposition,[status(thm)],[c_4137,c_1211]) ).
% 4.03/1.00  
% 4.03/1.00  cnf(c_4225,plain,
% 4.03/1.00      ( k10_relat_1(sK2,k1_relat_1(k2_funct_1(sK2))) = k2_relat_1(k2_funct_1(sK2)) ),
% 4.03/1.00      inference(superposition,[status(thm)],[c_4141,c_3047]) ).
% 4.03/1.00  
% 4.03/1.00  cnf(c_6314,plain,
% 4.03/1.00      ( k10_relat_1(sK2,k1_relat_1(k2_funct_1(sK2))) = sK0 ),
% 4.03/1.00      inference(demodulation,[status(thm)],[c_6310,c_4225]) ).
% 4.03/1.00  
% 4.03/1.00  cnf(c_2099,plain,
% 4.03/1.00      ( r1_tarski(k1_relat_1(sK2),sK0) = iProver_top
% 4.03/1.00      | v1_relat_1(sK2) != iProver_top ),
% 4.03/1.00      inference(superposition,[status(thm)],[c_1196,c_1192]) ).
% 4.03/1.00  
% 4.03/1.00  cnf(c_2422,plain,
% 4.03/1.00      ( r1_tarski(k1_relat_1(sK2),sK0) = iProver_top ),
% 4.03/1.00      inference(global_propositional_subsumption,
% 4.03/1.00                [status(thm)],
% 4.03/1.00                [c_2099,c_37,c_102,c_1497]) ).
% 4.03/1.00  
% 4.03/1.00  cnf(c_2094,plain,
% 4.03/1.00      ( k9_relat_1(sK2,k1_relat_1(sK2)) = k2_relat_1(sK2) ),
% 4.03/1.00      inference(superposition,[status(thm)],[c_2090,c_1211]) ).
% 4.03/1.00  
% 4.03/1.00  cnf(c_2097,plain,
% 4.03/1.00      ( k9_relat_1(sK2,k1_relat_1(sK2)) = sK0 ),
% 4.03/1.00      inference(light_normalisation,[status(thm)],[c_2094,c_1774]) ).
% 4.03/1.00  
% 4.03/1.00  cnf(c_2494,plain,
% 4.03/1.00      ( r1_tarski(k1_relat_1(sK2),X0) != iProver_top
% 4.03/1.00      | r1_tarski(sK0,k9_relat_1(sK2,X0)) = iProver_top
% 4.03/1.00      | v1_relat_1(sK2) != iProver_top ),
% 4.03/1.00      inference(superposition,[status(thm)],[c_2097,c_1210]) ).
% 4.03/1.00  
% 4.03/1.00  cnf(c_2643,plain,
% 4.03/1.00      ( r1_tarski(sK0,k9_relat_1(sK2,X0)) = iProver_top
% 4.03/1.00      | r1_tarski(k1_relat_1(sK2),X0) != iProver_top ),
% 4.03/1.00      inference(global_propositional_subsumption,
% 4.03/1.00                [status(thm)],
% 4.03/1.00                [c_2494,c_37,c_102,c_1497]) ).
% 4.03/1.00  
% 4.03/1.00  cnf(c_2644,plain,
% 4.03/1.00      ( r1_tarski(k1_relat_1(sK2),X0) != iProver_top
% 4.03/1.00      | r1_tarski(sK0,k9_relat_1(sK2,X0)) = iProver_top ),
% 4.03/1.00      inference(renaming,[status(thm)],[c_2643]) ).
% 4.03/1.00  
% 4.03/1.00  cnf(c_7,plain,
% 4.03/1.00      ( r1_tarski(k9_relat_1(X0,X1),k2_relat_1(X0)) | ~ v1_relat_1(X0) ),
% 4.03/1.00      inference(cnf_transformation,[],[f60]) ).
% 4.03/1.00  
% 4.03/1.00  cnf(c_1212,plain,
% 4.03/1.00      ( r1_tarski(k9_relat_1(X0,X1),k2_relat_1(X0)) = iProver_top
% 4.03/1.00      | v1_relat_1(X0) != iProver_top ),
% 4.03/1.00      inference(predicate_to_equality,[status(thm)],[c_7]) ).
% 4.03/1.00  
% 4.03/1.00  cnf(c_1776,plain,
% 4.03/1.00      ( r1_tarski(k9_relat_1(sK2,X0),sK0) = iProver_top
% 4.03/1.00      | v1_relat_1(sK2) != iProver_top ),
% 4.03/1.00      inference(superposition,[status(thm)],[c_1774,c_1212]) ).
% 4.03/1.00  
% 4.03/1.00  cnf(c_1781,plain,
% 4.03/1.00      ( r1_tarski(k9_relat_1(sK2,X0),sK0) = iProver_top ),
% 4.03/1.00      inference(global_propositional_subsumption,
% 4.03/1.00                [status(thm)],
% 4.03/1.00                [c_1776,c_37,c_102,c_1497]) ).
% 4.03/1.00  
% 4.03/1.00  cnf(c_0,plain,
% 4.03/1.00      ( ~ r1_tarski(X0,X1) | ~ r1_tarski(X1,X0) | X0 = X1 ),
% 4.03/1.00      inference(cnf_transformation,[],[f55]) ).
% 4.03/1.00  
% 4.03/1.00  cnf(c_1216,plain,
% 4.03/1.00      ( X0 = X1
% 4.03/1.00      | r1_tarski(X0,X1) != iProver_top
% 4.03/1.00      | r1_tarski(X1,X0) != iProver_top ),
% 4.03/1.00      inference(predicate_to_equality,[status(thm)],[c_0]) ).
% 4.03/1.00  
% 4.03/1.00  cnf(c_1787,plain,
% 4.03/1.00      ( k9_relat_1(sK2,X0) = sK0
% 4.03/1.00      | r1_tarski(sK0,k9_relat_1(sK2,X0)) != iProver_top ),
% 4.03/1.00      inference(superposition,[status(thm)],[c_1781,c_1216]) ).
% 4.03/1.00  
% 4.03/1.00  cnf(c_2651,plain,
% 4.03/1.00      ( k9_relat_1(sK2,X0) = sK0
% 4.03/1.00      | r1_tarski(k1_relat_1(sK2),X0) != iProver_top ),
% 4.03/1.00      inference(superposition,[status(thm)],[c_2644,c_1787]) ).
% 4.03/1.00  
% 4.03/1.00  cnf(c_6470,plain,
% 4.03/1.00      ( k9_relat_1(sK2,sK0) = sK0 ),
% 4.03/1.00      inference(superposition,[status(thm)],[c_2422,c_2651]) ).
% 4.03/1.00  
% 4.03/1.00  cnf(c_9235,plain,
% 4.03/1.00      ( k1_relat_1(sK2) = sK0 ),
% 4.03/1.00      inference(light_normalisation,
% 4.03/1.00                [status(thm)],
% 4.03/1.00                [c_9234,c_2096,c_6314,c_6470]) ).
% 4.03/1.00  
% 4.03/1.00  cnf(c_740,plain,
% 4.03/1.00      ( ~ r1_tarski(X0,X1) | r1_tarski(X2,X3) | X2 != X0 | X3 != X1 ),
% 4.03/1.00      theory(equality) ).
% 4.03/1.00  
% 4.03/1.00  cnf(c_1937,plain,
% 4.03/1.00      ( ~ r1_tarski(X0,X1)
% 4.03/1.00      | r1_tarski(sK1,k1_relat_1(sK2))
% 4.03/1.00      | k1_relat_1(sK2) != X1
% 4.03/1.00      | sK1 != X0 ),
% 4.03/1.00      inference(instantiation,[status(thm)],[c_740]) ).
% 4.03/1.00  
% 4.03/1.00  cnf(c_2773,plain,
% 4.03/1.00      ( ~ r1_tarski(sK1,X0)
% 4.03/1.00      | r1_tarski(sK1,k1_relat_1(sK2))
% 4.03/1.00      | k1_relat_1(sK2) != X0
% 4.03/1.00      | sK1 != sK1 ),
% 4.03/1.00      inference(instantiation,[status(thm)],[c_1937]) ).
% 4.03/1.00  
% 4.03/1.00  cnf(c_2775,plain,
% 4.03/1.00      ( r1_tarski(sK1,k1_relat_1(sK2))
% 4.03/1.00      | ~ r1_tarski(sK1,sK0)
% 4.03/1.00      | k1_relat_1(sK2) != sK0
% 4.03/1.00      | sK1 != sK1 ),
% 4.03/1.00      inference(instantiation,[status(thm)],[c_2773]) ).
% 4.03/1.00  
% 4.03/1.00  cnf(c_17,plain,
% 4.03/1.00      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 4.03/1.00      | k8_relset_1(X1,X2,X0,X3) = k10_relat_1(X0,X3) ),
% 4.03/1.00      inference(cnf_transformation,[],[f70]) ).
% 4.03/1.00  
% 4.03/1.00  cnf(c_1204,plain,
% 4.03/1.00      ( k8_relset_1(X0,X1,X2,X3) = k10_relat_1(X2,X3)
% 4.03/1.00      | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
% 4.03/1.00      inference(predicate_to_equality,[status(thm)],[c_17]) ).
% 4.03/1.00  
% 4.03/1.00  cnf(c_2156,plain,
% 4.03/1.00      ( k8_relset_1(sK0,sK0,sK2,X0) = k10_relat_1(sK2,X0) ),
% 4.03/1.00      inference(superposition,[status(thm)],[c_1196,c_1204]) ).
% 4.03/1.00  
% 4.03/1.00  cnf(c_28,negated_conjecture,
% 4.03/1.00      ( k8_relset_1(sK0,sK0,sK2,k7_relset_1(sK0,sK0,sK2,sK1)) != sK1
% 4.03/1.00      | k7_relset_1(sK0,sK0,sK2,k8_relset_1(sK0,sK0,sK2,sK1)) != sK1 ),
% 4.03/1.00      inference(cnf_transformation,[],[f86]) ).
% 4.03/1.00  
% 4.03/1.00  cnf(c_2352,plain,
% 4.03/1.00      ( k7_relset_1(sK0,sK0,sK2,k8_relset_1(sK0,sK0,sK2,sK1)) != sK1
% 4.03/1.00      | k10_relat_1(sK2,k7_relset_1(sK0,sK0,sK2,sK1)) != sK1 ),
% 4.03/1.00      inference(demodulation,[status(thm)],[c_2156,c_28]) ).
% 4.03/1.00  
% 4.03/1.00  cnf(c_16,plain,
% 4.03/1.00      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 4.03/1.00      | k7_relset_1(X1,X2,X0,X3) = k9_relat_1(X0,X3) ),
% 4.03/1.00      inference(cnf_transformation,[],[f69]) ).
% 4.03/1.00  
% 4.03/1.00  cnf(c_1205,plain,
% 4.03/1.00      ( k7_relset_1(X0,X1,X2,X3) = k9_relat_1(X2,X3)
% 4.03/1.00      | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
% 4.03/1.00      inference(predicate_to_equality,[status(thm)],[c_16]) ).
% 4.03/1.00  
% 4.03/1.00  cnf(c_2159,plain,
% 4.03/1.00      ( k7_relset_1(sK0,sK0,sK2,X0) = k9_relat_1(sK2,X0) ),
% 4.03/1.00      inference(superposition,[status(thm)],[c_1196,c_1205]) ).
% 4.03/1.00  
% 4.03/1.00  cnf(c_2353,plain,
% 4.03/1.00      ( k10_relat_1(sK2,k9_relat_1(sK2,sK1)) != sK1
% 4.03/1.00      | k9_relat_1(sK2,k10_relat_1(sK2,sK1)) != sK1 ),
% 4.03/1.00      inference(demodulation,[status(thm)],[c_2352,c_2156,c_2159]) ).
% 4.03/1.00  
% 4.03/1.00  cnf(c_1417,plain,
% 4.03/1.00      ( ~ r1_tarski(sK1,k1_relat_1(X0))
% 4.03/1.00      | ~ v2_funct_1(X0)
% 4.03/1.00      | ~ v1_funct_1(X0)
% 4.03/1.00      | ~ v1_relat_1(X0)
% 4.03/1.00      | k10_relat_1(X0,k9_relat_1(X0,sK1)) = sK1 ),
% 4.03/1.00      inference(instantiation,[status(thm)],[c_13]) ).
% 4.03/1.00  
% 4.03/1.00  cnf(c_1721,plain,
% 4.03/1.00      ( ~ r1_tarski(sK1,k1_relat_1(sK2))
% 4.03/1.00      | ~ v2_funct_1(sK2)
% 4.03/1.00      | ~ v1_funct_1(sK2)
% 4.03/1.00      | ~ v1_relat_1(sK2)
% 4.03/1.00      | k10_relat_1(sK2,k9_relat_1(sK2,sK1)) = sK1 ),
% 4.03/1.00      inference(instantiation,[status(thm)],[c_1417]) ).
% 4.03/1.00  
% 4.03/1.00  cnf(c_1603,plain,
% 4.03/1.00      ( ~ v3_funct_2(sK2,sK0,sK0)
% 4.03/1.00      | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
% 4.03/1.00      | v2_funct_1(sK2)
% 4.03/1.00      | ~ v1_funct_1(sK2) ),
% 4.03/1.00      inference(instantiation,[status(thm)],[c_1601]) ).
% 4.03/1.00  
% 4.03/1.00  cnf(c_1530,plain,
% 4.03/1.00      ( ~ r1_tarski(X0,X1)
% 4.03/1.00      | r1_tarski(sK1,k2_relat_1(sK2))
% 4.03/1.00      | k2_relat_1(sK2) != X1
% 4.03/1.00      | sK1 != X0 ),
% 4.03/1.00      inference(instantiation,[status(thm)],[c_740]) ).
% 4.03/1.00  
% 4.03/1.00  cnf(c_1571,plain,
% 4.03/1.00      ( ~ r1_tarski(sK1,X0)
% 4.03/1.00      | r1_tarski(sK1,k2_relat_1(sK2))
% 4.03/1.00      | k2_relat_1(sK2) != X0
% 4.03/1.00      | sK1 != sK1 ),
% 4.03/1.00      inference(instantiation,[status(thm)],[c_1530]) ).
% 4.03/1.00  
% 4.03/1.00  cnf(c_1573,plain,
% 4.03/1.00      ( r1_tarski(sK1,k2_relat_1(sK2))
% 4.03/1.00      | ~ r1_tarski(sK1,sK0)
% 4.03/1.00      | k2_relat_1(sK2) != sK0
% 4.03/1.00      | sK1 != sK1 ),
% 4.03/1.00      inference(instantiation,[status(thm)],[c_1571]) ).
% 4.03/1.00  
% 4.03/1.00  cnf(c_11,plain,
% 4.03/1.00      ( ~ r1_tarski(X0,k2_relat_1(X1))
% 4.03/1.00      | ~ v1_funct_1(X1)
% 4.03/1.00      | ~ v1_relat_1(X1)
% 4.03/1.00      | k9_relat_1(X1,k10_relat_1(X1,X0)) = X0 ),
% 4.03/1.00      inference(cnf_transformation,[],[f64]) ).
% 4.03/1.00  
% 4.03/1.00  cnf(c_1410,plain,
% 4.03/1.00      ( ~ r1_tarski(sK1,k2_relat_1(X0))
% 4.03/1.00      | ~ v1_funct_1(X0)
% 4.03/1.00      | ~ v1_relat_1(X0)
% 4.03/1.00      | k9_relat_1(X0,k10_relat_1(X0,sK1)) = sK1 ),
% 4.03/1.00      inference(instantiation,[status(thm)],[c_11]) ).
% 4.03/1.00  
% 4.03/1.00  cnf(c_1462,plain,
% 4.03/1.00      ( ~ r1_tarski(sK1,k2_relat_1(sK2))
% 4.03/1.00      | ~ v1_funct_1(sK2)
% 4.03/1.00      | ~ v1_relat_1(sK2)
% 4.03/1.00      | k9_relat_1(sK2,k10_relat_1(sK2,sK1)) = sK1 ),
% 4.03/1.00      inference(instantiation,[status(thm)],[c_1410]) ).
% 4.03/1.00  
% 4.03/1.00  cnf(c_1,plain,
% 4.03/1.00      ( r1_tarski(X0,X0) ),
% 4.03/1.00      inference(cnf_transformation,[],[f87]) ).
% 4.03/1.00  
% 4.03/1.00  cnf(c_1293,plain,
% 4.03/1.00      ( r1_tarski(sK1,sK1) ),
% 4.03/1.00      inference(instantiation,[status(thm)],[c_1]) ).
% 4.03/1.00  
% 4.03/1.00  cnf(c_1258,plain,
% 4.03/1.00      ( ~ r1_tarski(X0,sK1) | ~ r1_tarski(sK1,X0) | sK1 = X0 ),
% 4.03/1.00      inference(instantiation,[status(thm)],[c_0]) ).
% 4.03/1.00  
% 4.03/1.00  cnf(c_1266,plain,
% 4.03/1.00      ( ~ r1_tarski(sK1,sK1) | sK1 = sK1 ),
% 4.03/1.00      inference(instantiation,[status(thm)],[c_1258]) ).
% 4.03/1.00  
% 4.03/1.00  cnf(c_101,plain,
% 4.03/1.00      ( v1_relat_1(k2_zfmisc_1(sK0,sK0)) ),
% 4.03/1.00      inference(instantiation,[status(thm)],[c_6]) ).
% 4.03/1.00  
% 4.03/1.00  cnf(c_29,negated_conjecture,
% 4.03/1.00      ( r1_tarski(sK1,sK0) ),
% 4.03/1.00      inference(cnf_transformation,[],[f85]) ).
% 4.03/1.00  
% 4.03/1.00  cnf(contradiction,plain,
% 4.03/1.00      ( $false ),
% 4.03/1.00      inference(minisat,
% 4.03/1.00                [status(thm)],
% 4.03/1.00                [c_9235,c_2775,c_2353,c_1721,c_1603,c_1573,c_1557,c_1497,
% 4.03/1.00                 c_1496,c_1462,c_1293,c_1266,c_102,c_101,c_29,c_37,c_30,
% 4.03/1.00                 c_36,c_31,c_34,c_33]) ).
% 4.03/1.00  
% 4.03/1.00  
% 4.03/1.00  % SZS output end CNFRefutation for theBenchmark.p
% 4.03/1.00  
% 4.03/1.00  ------                               Statistics
% 4.03/1.00  
% 4.03/1.00  ------ General
% 4.03/1.00  
% 4.03/1.00  abstr_ref_over_cycles:                  0
% 4.03/1.00  abstr_ref_under_cycles:                 0
% 4.03/1.00  gc_basic_clause_elim:                   0
% 4.03/1.00  forced_gc_time:                         0
% 4.03/1.00  parsing_time:                           0.009
% 4.03/1.00  unif_index_cands_time:                  0.
% 4.03/1.00  unif_index_add_time:                    0.
% 4.03/1.00  orderings_time:                         0.
% 4.03/1.00  out_proof_time:                         0.023
% 4.03/1.00  total_time:                             0.445
% 4.03/1.00  num_of_symbols:                         54
% 4.03/1.00  num_of_terms:                           12451
% 4.03/1.00  
% 4.03/1.00  ------ Preprocessing
% 4.03/1.00  
% 4.03/1.00  num_of_splits:                          0
% 4.03/1.00  num_of_split_atoms:                     0
% 4.03/1.00  num_of_reused_defs:                     0
% 4.03/1.00  num_eq_ax_congr_red:                    25
% 4.03/1.00  num_of_sem_filtered_clauses:            1
% 4.03/1.00  num_of_subtypes:                        0
% 4.03/1.00  monotx_restored_types:                  0
% 4.03/1.00  sat_num_of_epr_types:                   0
% 4.03/1.00  sat_num_of_non_cyclic_types:            0
% 4.03/1.00  sat_guarded_non_collapsed_types:        0
% 4.03/1.00  num_pure_diseq_elim:                    0
% 4.03/1.00  simp_replaced_by:                       0
% 4.03/1.00  res_preprocessed:                       142
% 4.03/1.00  prep_upred:                             0
% 4.03/1.00  prep_unflattend:                        8
% 4.03/1.00  smt_new_axioms:                         0
% 4.03/1.00  pred_elim_cands:                        7
% 4.03/1.00  pred_elim:                              3
% 4.03/1.00  pred_elim_cl:                           5
% 4.03/1.00  pred_elim_cycles:                       6
% 4.03/1.00  merged_defs:                            0
% 4.03/1.00  merged_defs_ncl:                        0
% 4.03/1.00  bin_hyper_res:                          0
% 4.03/1.00  prep_cycles:                            4
% 4.03/1.00  pred_elim_time:                         0.009
% 4.03/1.00  splitting_time:                         0.
% 4.03/1.00  sem_filter_time:                        0.
% 4.03/1.00  monotx_time:                            0.001
% 4.03/1.00  subtype_inf_time:                       0.
% 4.03/1.00  
% 4.03/1.00  ------ Problem properties
% 4.03/1.00  
% 4.03/1.00  clauses:                                27
% 4.03/1.00  conjectures:                            6
% 4.03/1.00  epr:                                    6
% 4.03/1.00  horn:                                   27
% 4.03/1.00  ground:                                 6
% 4.03/1.00  unary:                                  7
% 4.03/1.00  binary:                                 6
% 4.03/1.00  lits:                                   78
% 4.03/1.00  lits_eq:                                12
% 4.03/1.00  fd_pure:                                0
% 4.03/1.00  fd_pseudo:                              0
% 4.03/1.00  fd_cond:                                0
% 4.03/1.00  fd_pseudo_cond:                         2
% 4.03/1.00  ac_symbols:                             0
% 4.03/1.00  
% 4.03/1.00  ------ Propositional Solver
% 4.03/1.00  
% 4.03/1.00  prop_solver_calls:                      37
% 4.03/1.00  prop_fast_solver_calls:                 1335
% 4.03/1.00  smt_solver_calls:                       0
% 4.03/1.00  smt_fast_solver_calls:                  0
% 4.03/1.00  prop_num_of_clauses:                    4332
% 4.03/1.00  prop_preprocess_simplified:             8753
% 4.03/1.00  prop_fo_subsumed:                       89
% 4.03/1.00  prop_solver_time:                       0.
% 4.03/1.00  smt_solver_time:                        0.
% 4.03/1.00  smt_fast_solver_time:                   0.
% 4.03/1.00  prop_fast_solver_time:                  0.
% 4.03/1.00  prop_unsat_core_time:                   0.
% 4.03/1.00  
% 4.03/1.00  ------ QBF
% 4.03/1.00  
% 4.03/1.00  qbf_q_res:                              0
% 4.03/1.00  qbf_num_tautologies:                    0
% 4.03/1.00  qbf_prep_cycles:                        0
% 4.03/1.00  
% 4.03/1.00  ------ BMC1
% 4.03/1.00  
% 4.03/1.00  bmc1_current_bound:                     -1
% 4.03/1.00  bmc1_last_solved_bound:                 -1
% 4.03/1.00  bmc1_unsat_core_size:                   -1
% 4.03/1.00  bmc1_unsat_core_parents_size:           -1
% 4.03/1.00  bmc1_merge_next_fun:                    0
% 4.03/1.00  bmc1_unsat_core_clauses_time:           0.
% 4.03/1.00  
% 4.03/1.00  ------ Instantiation
% 4.03/1.00  
% 4.03/1.00  inst_num_of_clauses:                    1129
% 4.03/1.00  inst_num_in_passive:                    456
% 4.03/1.00  inst_num_in_active:                     614
% 4.03/1.00  inst_num_in_unprocessed:                59
% 4.03/1.00  inst_num_of_loops:                      670
% 4.03/1.00  inst_num_of_learning_restarts:          0
% 4.03/1.00  inst_num_moves_active_passive:          47
% 4.03/1.00  inst_lit_activity:                      0
% 4.03/1.00  inst_lit_activity_moves:                0
% 4.03/1.00  inst_num_tautologies:                   0
% 4.03/1.00  inst_num_prop_implied:                  0
% 4.03/1.00  inst_num_existing_simplified:           0
% 4.03/1.00  inst_num_eq_res_simplified:             0
% 4.03/1.00  inst_num_child_elim:                    0
% 4.03/1.00  inst_num_of_dismatching_blockings:      911
% 4.03/1.00  inst_num_of_non_proper_insts:           1770
% 4.03/1.00  inst_num_of_duplicates:                 0
% 4.03/1.00  inst_inst_num_from_inst_to_res:         0
% 4.03/1.00  inst_dismatching_checking_time:         0.
% 4.03/1.00  
% 4.03/1.00  ------ Resolution
% 4.03/1.00  
% 4.03/1.00  res_num_of_clauses:                     0
% 4.03/1.00  res_num_in_passive:                     0
% 4.03/1.00  res_num_in_active:                      0
% 4.03/1.00  res_num_of_loops:                       146
% 4.03/1.00  res_forward_subset_subsumed:            129
% 4.03/1.00  res_backward_subset_subsumed:           0
% 4.03/1.00  res_forward_subsumed:                   0
% 4.03/1.00  res_backward_subsumed:                  0
% 4.03/1.00  res_forward_subsumption_resolution:     1
% 4.03/1.00  res_backward_subsumption_resolution:    0
% 4.03/1.00  res_clause_to_clause_subsumption:       766
% 4.03/1.00  res_orphan_elimination:                 0
% 4.03/1.00  res_tautology_del:                      135
% 4.03/1.00  res_num_eq_res_simplified:              0
% 4.03/1.00  res_num_sel_changes:                    0
% 4.03/1.00  res_moves_from_active_to_pass:          0
% 4.03/1.00  
% 4.03/1.00  ------ Superposition
% 4.03/1.00  
% 4.03/1.00  sup_time_total:                         0.
% 4.03/1.00  sup_time_generating:                    0.
% 4.03/1.00  sup_time_sim_full:                      0.
% 4.03/1.00  sup_time_sim_immed:                     0.
% 4.03/1.00  
% 4.03/1.00  sup_num_of_clauses:                     225
% 4.03/1.00  sup_num_in_active:                      125
% 4.03/1.00  sup_num_in_passive:                     100
% 4.03/1.00  sup_num_of_loops:                       133
% 4.03/1.00  sup_fw_superposition:                   220
% 4.03/1.00  sup_bw_superposition:                   156
% 4.03/1.00  sup_immediate_simplified:               201
% 4.03/1.00  sup_given_eliminated:                   0
% 4.03/1.00  comparisons_done:                       0
% 4.03/1.00  comparisons_avoided:                    0
% 4.03/1.00  
% 4.03/1.00  ------ Simplifications
% 4.03/1.00  
% 4.03/1.00  
% 4.03/1.00  sim_fw_subset_subsumed:                 26
% 4.03/1.00  sim_bw_subset_subsumed:                 5
% 4.03/1.00  sim_fw_subsumed:                        49
% 4.03/1.00  sim_bw_subsumed:                        0
% 4.03/1.00  sim_fw_subsumption_res:                 0
% 4.03/1.00  sim_bw_subsumption_res:                 0
% 4.03/1.00  sim_tautology_del:                      15
% 4.03/1.00  sim_eq_tautology_del:                   28
% 4.03/1.00  sim_eq_res_simp:                        0
% 4.03/1.00  sim_fw_demodulated:                     57
% 4.03/1.00  sim_bw_demodulated:                     8
% 4.03/1.00  sim_light_normalised:                   118
% 4.03/1.00  sim_joinable_taut:                      0
% 4.03/1.00  sim_joinable_simp:                      0
% 4.03/1.00  sim_ac_normalised:                      0
% 4.03/1.00  sim_smt_subsumption:                    0
% 4.03/1.00  
%------------------------------------------------------------------------------
