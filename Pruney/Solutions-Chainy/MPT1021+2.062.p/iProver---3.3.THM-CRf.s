%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n008.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:07:31 EST 2020

% Result     : Theorem 3.42s
% Output     : CNFRefutation 3.42s
% Verified   : 
% Statistics : Number of formulae       :  220 (2366 expanded)
%              Number of clauses        :  137 ( 718 expanded)
%              Number of leaves         :   20 ( 466 expanded)
%              Depth                    :   21
%              Number of atoms          :  706 (11192 expanded)
%              Number of equality atoms :  307 (1131 expanded)
%              Maximal formula depth    :   12 (   4 average)
%              Maximal clause size      :   12 (   3 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f19,conjecture,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
        & v3_funct_2(X1,X0,X0)
        & v1_funct_2(X1,X0,X0)
        & v1_funct_1(X1) )
     => ( r2_relset_1(X0,X0,k1_partfun1(X0,X0,X0,X0,k2_funct_2(X0,X1),X1),k6_partfun1(X0))
        & r2_relset_1(X0,X0,k1_partfun1(X0,X0,X0,X0,X1,k2_funct_2(X0,X1)),k6_partfun1(X0)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f20,negated_conjecture,(
    ~ ! [X0,X1] :
        ( ( m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
          & v3_funct_2(X1,X0,X0)
          & v1_funct_2(X1,X0,X0)
          & v1_funct_1(X1) )
       => ( r2_relset_1(X0,X0,k1_partfun1(X0,X0,X0,X0,k2_funct_2(X0,X1),X1),k6_partfun1(X0))
          & r2_relset_1(X0,X0,k1_partfun1(X0,X0,X0,X0,X1,k2_funct_2(X0,X1)),k6_partfun1(X0)) ) ) ),
    inference(negated_conjecture,[],[f19])).

fof(f46,plain,(
    ? [X0,X1] :
      ( ( ~ r2_relset_1(X0,X0,k1_partfun1(X0,X0,X0,X0,k2_funct_2(X0,X1),X1),k6_partfun1(X0))
        | ~ r2_relset_1(X0,X0,k1_partfun1(X0,X0,X0,X0,X1,k2_funct_2(X0,X1)),k6_partfun1(X0)) )
      & m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
      & v3_funct_2(X1,X0,X0)
      & v1_funct_2(X1,X0,X0)
      & v1_funct_1(X1) ) ),
    inference(ennf_transformation,[],[f20])).

fof(f47,plain,(
    ? [X0,X1] :
      ( ( ~ r2_relset_1(X0,X0,k1_partfun1(X0,X0,X0,X0,k2_funct_2(X0,X1),X1),k6_partfun1(X0))
        | ~ r2_relset_1(X0,X0,k1_partfun1(X0,X0,X0,X0,X1,k2_funct_2(X0,X1)),k6_partfun1(X0)) )
      & m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
      & v3_funct_2(X1,X0,X0)
      & v1_funct_2(X1,X0,X0)
      & v1_funct_1(X1) ) ),
    inference(flattening,[],[f46])).

fof(f51,plain,
    ( ? [X0,X1] :
        ( ( ~ r2_relset_1(X0,X0,k1_partfun1(X0,X0,X0,X0,k2_funct_2(X0,X1),X1),k6_partfun1(X0))
          | ~ r2_relset_1(X0,X0,k1_partfun1(X0,X0,X0,X0,X1,k2_funct_2(X0,X1)),k6_partfun1(X0)) )
        & m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
        & v3_funct_2(X1,X0,X0)
        & v1_funct_2(X1,X0,X0)
        & v1_funct_1(X1) )
   => ( ( ~ r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK0,sK0,sK0,k2_funct_2(sK0,sK1),sK1),k6_partfun1(sK0))
        | ~ r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK0,sK0,sK0,sK1,k2_funct_2(sK0,sK1)),k6_partfun1(sK0)) )
      & m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
      & v3_funct_2(sK1,sK0,sK0)
      & v1_funct_2(sK1,sK0,sK0)
      & v1_funct_1(sK1) ) ),
    introduced(choice_axiom,[])).

fof(f52,plain,
    ( ( ~ r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK0,sK0,sK0,k2_funct_2(sK0,sK1),sK1),k6_partfun1(sK0))
      | ~ r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK0,sK0,sK0,sK1,k2_funct_2(sK0,sK1)),k6_partfun1(sK0)) )
    & m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
    & v3_funct_2(sK1,sK0,sK0)
    & v1_funct_2(sK1,sK0,sK0)
    & v1_funct_1(sK1) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f47,f51])).

fof(f84,plain,(
    m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) ),
    inference(cnf_transformation,[],[f52])).

fof(f12,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => ( ( v3_funct_2(X2,X0,X1)
          & v1_funct_1(X2) )
       => ( v2_funct_2(X2,X1)
          & v2_funct_1(X2)
          & v1_funct_1(X2) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f36,plain,(
    ! [X0,X1,X2] :
      ( ( v2_funct_2(X2,X1)
        & v2_funct_1(X2)
        & v1_funct_1(X2) )
      | ~ v3_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f37,plain,(
    ! [X0,X1,X2] :
      ( ( v2_funct_2(X2,X1)
        & v2_funct_1(X2)
        & v1_funct_1(X2) )
      | ~ v3_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(flattening,[],[f36])).

fof(f69,plain,(
    ! [X2,X0,X1] :
      ( v2_funct_1(X2)
      | ~ v3_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f37])).

fof(f81,plain,(
    v1_funct_1(sK1) ),
    inference(cnf_transformation,[],[f52])).

fof(f83,plain,(
    v3_funct_2(sK1,sK0,sK0) ),
    inference(cnf_transformation,[],[f52])).

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

fof(f53,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | X0 != X1 ) ),
    inference(cnf_transformation,[],[f49])).

fof(f89,plain,(
    ! [X1] : r1_tarski(X1,X1) ),
    inference(equality_resolution,[],[f53])).

fof(f8,axiom,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ! [X1] :
          ( ( r1_tarski(X1,k1_relat_1(X0))
            & v2_funct_1(X0) )
         => k9_relat_1(k2_funct_1(X0),k9_relat_1(X0,X1)) = X1 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f29,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k9_relat_1(k2_funct_1(X0),k9_relat_1(X0,X1)) = X1
          | ~ r1_tarski(X1,k1_relat_1(X0))
          | ~ v2_funct_1(X0) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f30,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k9_relat_1(k2_funct_1(X0),k9_relat_1(X0,X1)) = X1
          | ~ r1_tarski(X1,k1_relat_1(X0))
          | ~ v2_funct_1(X0) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f29])).

fof(f62,plain,(
    ! [X0,X1] :
      ( k9_relat_1(k2_funct_1(X0),k9_relat_1(X0,X1)) = X1
      | ~ r1_tarski(X1,k1_relat_1(X0))
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f70,plain,(
    ! [X2,X0,X1] :
      ( v2_funct_2(X2,X1)
      | ~ v3_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f37])).

fof(f13,axiom,(
    ! [X0,X1] :
      ( ( v5_relat_1(X1,X0)
        & v1_relat_1(X1) )
     => ( v2_funct_2(X1,X0)
      <=> k2_relat_1(X1) = X0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f38,plain,(
    ! [X0,X1] :
      ( ( v2_funct_2(X1,X0)
      <=> k2_relat_1(X1) = X0 )
      | ~ v5_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f39,plain,(
    ! [X0,X1] :
      ( ( v2_funct_2(X1,X0)
      <=> k2_relat_1(X1) = X0 )
      | ~ v5_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f38])).

fof(f50,plain,(
    ! [X0,X1] :
      ( ( ( v2_funct_2(X1,X0)
          | k2_relat_1(X1) != X0 )
        & ( k2_relat_1(X1) = X0
          | ~ v2_funct_2(X1,X0) ) )
      | ~ v5_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(nnf_transformation,[],[f39])).

fof(f71,plain,(
    ! [X0,X1] :
      ( k2_relat_1(X1) = X0
      | ~ v2_funct_2(X1,X0)
      | ~ v5_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f50])).

fof(f10,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => ( v5_relat_1(X2,X1)
        & v4_relat_1(X2,X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f33,plain,(
    ! [X0,X1,X2] :
      ( ( v5_relat_1(X2,X1)
        & v4_relat_1(X2,X0) )
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f66,plain,(
    ! [X2,X0,X1] :
      ( v5_relat_1(X2,X1)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f33])).

fof(f3,axiom,(
    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f57,plain,(
    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1)) ),
    inference(cnf_transformation,[],[f3])).

fof(f2,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(X0))
         => v1_relat_1(X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f22,plain,(
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
    inference(cnf_transformation,[],[f22])).

fof(f7,axiom,(
    ! [X0,X1] :
      ( ( v1_funct_1(X1)
        & v1_relat_1(X1) )
     => ( r1_tarski(X0,k2_relat_1(X1))
       => k9_relat_1(X1,k10_relat_1(X1,X0)) = X0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f27,plain,(
    ! [X0,X1] :
      ( k9_relat_1(X1,k10_relat_1(X1,X0)) = X0
      | ~ r1_tarski(X0,k2_relat_1(X1))
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f28,plain,(
    ! [X0,X1] :
      ( k9_relat_1(X1,k10_relat_1(X1,X0)) = X0
      | ~ r1_tarski(X0,k2_relat_1(X1))
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f27])).

fof(f61,plain,(
    ! [X0,X1] :
      ( k9_relat_1(X1,k10_relat_1(X1,X0)) = X0
      | ~ r1_tarski(X0,k2_relat_1(X1))
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f5,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => k10_relat_1(X0,k2_relat_1(X0)) = k1_relat_1(X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f24,plain,(
    ! [X0] :
      ( k10_relat_1(X0,k2_relat_1(X0)) = k1_relat_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f59,plain,(
    ! [X0] :
      ( k10_relat_1(X0,k2_relat_1(X0)) = k1_relat_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f17,axiom,(
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
    inference(ennf_transformation,[],[f17])).

fof(f45,plain,(
    ! [X0,X1] :
      ( k2_funct_1(X1) = k2_funct_2(X0,X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
      | ~ v3_funct_2(X1,X0,X0)
      | ~ v1_funct_2(X1,X0,X0)
      | ~ v1_funct_1(X1) ) ),
    inference(flattening,[],[f44])).

fof(f79,plain,(
    ! [X0,X1] :
      ( k2_funct_1(X1) = k2_funct_2(X0,X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
      | ~ v3_funct_2(X1,X0,X0)
      | ~ v1_funct_2(X1,X0,X0)
      | ~ v1_funct_1(X1) ) ),
    inference(cnf_transformation,[],[f45])).

fof(f82,plain,(
    v1_funct_2(sK1,sK0,sK0) ),
    inference(cnf_transformation,[],[f52])).

fof(f14,axiom,(
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
    inference(ennf_transformation,[],[f14])).

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
    inference(flattening,[],[f40])).

fof(f76,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k2_funct_2(X0,X1),k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
      | ~ v3_funct_2(X1,X0,X0)
      | ~ v1_funct_2(X1,X0,X0)
      | ~ v1_funct_1(X1) ) ),
    inference(cnf_transformation,[],[f41])).

fof(f65,plain,(
    ! [X2,X0,X1] :
      ( v4_relat_1(X2,X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f33])).

fof(f6,axiom,(
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
    inference(ennf_transformation,[],[f6])).

fof(f26,plain,(
    ! [X0,X1] :
      ( k7_relat_1(X1,X0) = X1
      | ~ v4_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f25])).

fof(f60,plain,(
    ! [X0,X1] :
      ( k7_relat_1(X1,X0) = X1
      | ~ v4_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => k2_relat_1(k7_relat_1(X1,X0)) = k9_relat_1(X1,X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f23,plain,(
    ! [X0,X1] :
      ( k2_relat_1(k7_relat_1(X1,X0)) = k9_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f58,plain,(
    ! [X0,X1] :
      ( k2_relat_1(k7_relat_1(X1,X0)) = k9_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f73,plain,(
    ! [X0,X1] :
      ( v1_funct_1(k2_funct_2(X0,X1))
      | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
      | ~ v3_funct_2(X1,X0,X0)
      | ~ v1_funct_2(X1,X0,X0)
      | ~ v1_funct_1(X1) ) ),
    inference(cnf_transformation,[],[f41])).

fof(f75,plain,(
    ! [X0,X1] :
      ( v3_funct_2(k2_funct_2(X0,X1),X0,X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
      | ~ v3_funct_2(X1,X0,X0)
      | ~ v1_funct_2(X1,X0,X0)
      | ~ v1_funct_1(X1) ) ),
    inference(cnf_transformation,[],[f41])).

fof(f16,axiom,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( ( m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
        & v1_funct_1(X5)
        & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_1(X4) )
     => k5_relat_1(X4,X5) = k1_partfun1(X0,X1,X2,X3,X4,X5) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f42,plain,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( k5_relat_1(X4,X5) = k1_partfun1(X0,X1,X2,X3,X4,X5)
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ v1_funct_1(X5)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X4) ) ),
    inference(ennf_transformation,[],[f16])).

fof(f43,plain,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( k5_relat_1(X4,X5) = k1_partfun1(X0,X1,X2,X3,X4,X5)
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ v1_funct_1(X5)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X4) ) ),
    inference(flattening,[],[f42])).

fof(f78,plain,(
    ! [X4,X2,X0,X5,X3,X1] :
      ( k5_relat_1(X4,X5) = k1_partfun1(X0,X1,X2,X3,X4,X5)
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ v1_funct_1(X5)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X4) ) ),
    inference(cnf_transformation,[],[f43])).

fof(f9,axiom,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ( v2_funct_1(X0)
       => ( k5_relat_1(k2_funct_1(X0),X0) = k6_relat_1(k2_relat_1(X0))
          & k5_relat_1(X0,k2_funct_1(X0)) = k6_relat_1(k1_relat_1(X0)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f31,plain,(
    ! [X0] :
      ( ( k5_relat_1(k2_funct_1(X0),X0) = k6_relat_1(k2_relat_1(X0))
        & k5_relat_1(X0,k2_funct_1(X0)) = k6_relat_1(k1_relat_1(X0)) )
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f32,plain,(
    ! [X0] :
      ( ( k5_relat_1(k2_funct_1(X0),X0) = k6_relat_1(k2_relat_1(X0))
        & k5_relat_1(X0,k2_funct_1(X0)) = k6_relat_1(k1_relat_1(X0)) )
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f31])).

fof(f63,plain,(
    ! [X0] :
      ( k5_relat_1(X0,k2_funct_1(X0)) = k6_relat_1(k1_relat_1(X0))
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f32])).

fof(f18,axiom,(
    ! [X0] : k6_relat_1(X0) = k6_partfun1(X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f80,plain,(
    ! [X0] : k6_relat_1(X0) = k6_partfun1(X0) ),
    inference(cnf_transformation,[],[f18])).

fof(f87,plain,(
    ! [X0] :
      ( k5_relat_1(X0,k2_funct_1(X0)) = k6_partfun1(k1_relat_1(X0))
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(definition_unfolding,[],[f63,f80])).

fof(f64,plain,(
    ! [X0] :
      ( k5_relat_1(k2_funct_1(X0),X0) = k6_relat_1(k2_relat_1(X0))
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f32])).

fof(f86,plain,(
    ! [X0] :
      ( k5_relat_1(k2_funct_1(X0),X0) = k6_partfun1(k2_relat_1(X0))
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(definition_unfolding,[],[f64,f80])).

fof(f85,plain,
    ( ~ r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK0,sK0,sK0,k2_funct_2(sK0,sK1),sK1),k6_partfun1(sK0))
    | ~ r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK0,sK0,sK0,sK1,k2_funct_2(sK0,sK1)),k6_partfun1(sK0)) ),
    inference(cnf_transformation,[],[f52])).

fof(f15,axiom,(
    ! [X0] :
      ( m1_subset_1(k6_partfun1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
      & v1_partfun1(k6_partfun1(X0),X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f21,plain,(
    ! [X0] : m1_subset_1(k6_partfun1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0))) ),
    inference(pure_predicate_removal,[],[f15])).

fof(f77,plain,(
    ! [X0] : m1_subset_1(k6_partfun1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0))) ),
    inference(cnf_transformation,[],[f21])).

fof(f11,axiom,(
    ! [X0,X1,X2,X3] :
      ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) )
     => r2_relset_1(X0,X1,X2,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f34,plain,(
    ! [X0,X1,X2,X3] :
      ( r2_relset_1(X0,X1,X2,X2)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f35,plain,(
    ! [X0,X1,X2,X3] :
      ( r2_relset_1(X0,X1,X2,X2)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(flattening,[],[f34])).

fof(f67,plain,(
    ! [X2,X0,X3,X1] :
      ( r2_relset_1(X0,X1,X2,X2)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f35])).

cnf(c_28,negated_conjecture,
    ( m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) ),
    inference(cnf_transformation,[],[f84])).

cnf(c_1279,plain,
    ( m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_28])).

cnf(c_16,plain,
    ( ~ v3_funct_2(X0,X1,X2)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | v2_funct_1(X0)
    | ~ v1_funct_1(X0) ),
    inference(cnf_transformation,[],[f69])).

cnf(c_1288,plain,
    ( v3_funct_2(X0,X1,X2) != iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) != iProver_top
    | v2_funct_1(X0) = iProver_top
    | v1_funct_1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_16])).

cnf(c_3444,plain,
    ( v3_funct_2(sK1,sK0,sK0) != iProver_top
    | v2_funct_1(sK1) = iProver_top
    | v1_funct_1(sK1) != iProver_top ),
    inference(superposition,[status(thm)],[c_1279,c_1288])).

cnf(c_31,negated_conjecture,
    ( v1_funct_1(sK1) ),
    inference(cnf_transformation,[],[f81])).

cnf(c_32,plain,
    ( v1_funct_1(sK1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_31])).

cnf(c_29,negated_conjecture,
    ( v3_funct_2(sK1,sK0,sK0) ),
    inference(cnf_transformation,[],[f83])).

cnf(c_34,plain,
    ( v3_funct_2(sK1,sK0,sK0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_29])).

cnf(c_35,plain,
    ( m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_28])).

cnf(c_1545,plain,
    ( ~ v3_funct_2(sK1,X0,X1)
    | ~ m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
    | v2_funct_1(sK1)
    | ~ v1_funct_1(sK1) ),
    inference(instantiation,[status(thm)],[c_16])).

cnf(c_1546,plain,
    ( v3_funct_2(sK1,X0,X1) != iProver_top
    | m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top
    | v2_funct_1(sK1) = iProver_top
    | v1_funct_1(sK1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1545])).

cnf(c_1548,plain,
    ( v3_funct_2(sK1,sK0,sK0) != iProver_top
    | m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) != iProver_top
    | v2_funct_1(sK1) = iProver_top
    | v1_funct_1(sK1) != iProver_top ),
    inference(instantiation,[status(thm)],[c_1546])).

cnf(c_4010,plain,
    ( v2_funct_1(sK1) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_3444,c_32,c_34,c_35,c_1548])).

cnf(c_2,plain,
    ( r1_tarski(X0,X0) ),
    inference(cnf_transformation,[],[f89])).

cnf(c_1298,plain,
    ( r1_tarski(X0,X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2])).

cnf(c_9,plain,
    ( ~ r1_tarski(X0,k1_relat_1(X1))
    | ~ v2_funct_1(X1)
    | ~ v1_funct_1(X1)
    | ~ v1_relat_1(X1)
    | k9_relat_1(k2_funct_1(X1),k9_relat_1(X1,X0)) = X0 ),
    inference(cnf_transformation,[],[f62])).

cnf(c_1292,plain,
    ( k9_relat_1(k2_funct_1(X0),k9_relat_1(X0,X1)) = X1
    | r1_tarski(X1,k1_relat_1(X0)) != iProver_top
    | v2_funct_1(X0) != iProver_top
    | v1_funct_1(X0) != iProver_top
    | v1_relat_1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_9])).

cnf(c_3467,plain,
    ( k9_relat_1(k2_funct_1(X0),k9_relat_1(X0,k1_relat_1(X0))) = k1_relat_1(X0)
    | v2_funct_1(X0) != iProver_top
    | v1_funct_1(X0) != iProver_top
    | v1_relat_1(X0) != iProver_top ),
    inference(superposition,[status(thm)],[c_1298,c_1292])).

cnf(c_7333,plain,
    ( k9_relat_1(k2_funct_1(sK1),k9_relat_1(sK1,k1_relat_1(sK1))) = k1_relat_1(sK1)
    | v1_funct_1(sK1) != iProver_top
    | v1_relat_1(sK1) != iProver_top ),
    inference(superposition,[status(thm)],[c_4010,c_3467])).

cnf(c_15,plain,
    ( ~ v3_funct_2(X0,X1,X2)
    | v2_funct_2(X0,X2)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ v1_funct_1(X0) ),
    inference(cnf_transformation,[],[f70])).

cnf(c_19,plain,
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
    inference(resolution_lifted,[status(thm)],[c_15,c_19])).

cnf(c_411,plain,
    ( ~ v3_funct_2(X0,X1,X2)
    | ~ v5_relat_1(X0,X2)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ v1_funct_1(X0)
    | ~ v1_relat_1(X0)
    | k2_relat_1(X0) = X2 ),
    inference(unflattening,[status(thm)],[c_410])).

cnf(c_12,plain,
    ( v5_relat_1(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) ),
    inference(cnf_transformation,[],[f66])).

cnf(c_427,plain,
    ( ~ v3_funct_2(X0,X1,X2)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ v1_funct_1(X0)
    | ~ v1_relat_1(X0)
    | k2_relat_1(X0) = X2 ),
    inference(forward_subsumption_resolution,[status(thm)],[c_411,c_12])).

cnf(c_1274,plain,
    ( k2_relat_1(X0) = X1
    | v3_funct_2(X0,X2,X1) != iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) != iProver_top
    | v1_funct_1(X0) != iProver_top
    | v1_relat_1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_427])).

cnf(c_1682,plain,
    ( k2_relat_1(sK1) = sK0
    | v3_funct_2(sK1,sK0,sK0) != iProver_top
    | v1_funct_1(sK1) != iProver_top
    | v1_relat_1(sK1) != iProver_top ),
    inference(superposition,[status(thm)],[c_1279,c_1274])).

cnf(c_4,plain,
    ( v1_relat_1(k2_zfmisc_1(X0,X1)) ),
    inference(cnf_transformation,[],[f57])).

cnf(c_102,plain,
    ( v1_relat_1(k2_zfmisc_1(sK0,sK0)) ),
    inference(instantiation,[status(thm)],[c_4])).

cnf(c_1702,plain,
    ( ~ v3_funct_2(sK1,sK0,sK0)
    | ~ v1_funct_1(sK1)
    | ~ v1_relat_1(sK1)
    | k2_relat_1(sK1) = sK0 ),
    inference(predicate_to_equality_rev,[status(thm)],[c_1682])).

cnf(c_3,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | ~ v1_relat_1(X1)
    | v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f56])).

cnf(c_1521,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | v1_relat_1(X0)
    | ~ v1_relat_1(k2_zfmisc_1(X1,X2)) ),
    inference(instantiation,[status(thm)],[c_3])).

cnf(c_1721,plain,
    ( ~ m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
    | ~ v1_relat_1(k2_zfmisc_1(sK0,sK0))
    | v1_relat_1(sK1) ),
    inference(instantiation,[status(thm)],[c_1521])).

cnf(c_2187,plain,
    ( k2_relat_1(sK1) = sK0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_1682,c_31,c_29,c_28,c_102,c_1702,c_1721])).

cnf(c_8,plain,
    ( ~ r1_tarski(X0,k2_relat_1(X1))
    | ~ v1_funct_1(X1)
    | ~ v1_relat_1(X1)
    | k9_relat_1(X1,k10_relat_1(X1,X0)) = X0 ),
    inference(cnf_transformation,[],[f61])).

cnf(c_1293,plain,
    ( k9_relat_1(X0,k10_relat_1(X0,X1)) = X1
    | r1_tarski(X1,k2_relat_1(X0)) != iProver_top
    | v1_funct_1(X0) != iProver_top
    | v1_relat_1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_8])).

cnf(c_2751,plain,
    ( k9_relat_1(sK1,k10_relat_1(sK1,X0)) = X0
    | r1_tarski(X0,sK0) != iProver_top
    | v1_funct_1(sK1) != iProver_top
    | v1_relat_1(sK1) != iProver_top ),
    inference(superposition,[status(thm)],[c_2187,c_1293])).

cnf(c_101,plain,
    ( v1_relat_1(k2_zfmisc_1(X0,X1)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_4])).

cnf(c_103,plain,
    ( v1_relat_1(k2_zfmisc_1(sK0,sK0)) = iProver_top ),
    inference(instantiation,[status(thm)],[c_101])).

cnf(c_1722,plain,
    ( m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) != iProver_top
    | v1_relat_1(k2_zfmisc_1(sK0,sK0)) != iProver_top
    | v1_relat_1(sK1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1721])).

cnf(c_2994,plain,
    ( k9_relat_1(sK1,k10_relat_1(sK1,X0)) = X0
    | r1_tarski(X0,sK0) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_2751,c_32,c_35,c_103,c_1722])).

cnf(c_3002,plain,
    ( k9_relat_1(sK1,k10_relat_1(sK1,sK0)) = sK0 ),
    inference(superposition,[status(thm)],[c_1298,c_2994])).

cnf(c_1297,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(X1)) != iProver_top
    | v1_relat_1(X1) != iProver_top
    | v1_relat_1(X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3])).

cnf(c_1974,plain,
    ( v1_relat_1(k2_zfmisc_1(sK0,sK0)) != iProver_top
    | v1_relat_1(sK1) = iProver_top ),
    inference(superposition,[status(thm)],[c_1279,c_1297])).

cnf(c_1988,plain,
    ( v1_relat_1(sK1) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_1974,c_35,c_103,c_1722])).

cnf(c_6,plain,
    ( ~ v1_relat_1(X0)
    | k10_relat_1(X0,k2_relat_1(X0)) = k1_relat_1(X0) ),
    inference(cnf_transformation,[],[f59])).

cnf(c_1294,plain,
    ( k10_relat_1(X0,k2_relat_1(X0)) = k1_relat_1(X0)
    | v1_relat_1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_6])).

cnf(c_1994,plain,
    ( k10_relat_1(sK1,k2_relat_1(sK1)) = k1_relat_1(sK1) ),
    inference(superposition,[status(thm)],[c_1988,c_1294])).

cnf(c_2190,plain,
    ( k10_relat_1(sK1,sK0) = k1_relat_1(sK1) ),
    inference(light_normalisation,[status(thm)],[c_1994,c_2187])).

cnf(c_3003,plain,
    ( k9_relat_1(sK1,k1_relat_1(sK1)) = sK0 ),
    inference(light_normalisation,[status(thm)],[c_3002,c_2190])).

cnf(c_26,plain,
    ( ~ v1_funct_2(X0,X1,X1)
    | ~ v3_funct_2(X0,X1,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X1)))
    | ~ v1_funct_1(X0)
    | k2_funct_2(X1,X0) = k2_funct_1(X0) ),
    inference(cnf_transformation,[],[f79])).

cnf(c_1281,plain,
    ( k2_funct_2(X0,X1) = k2_funct_1(X1)
    | v1_funct_2(X1,X0,X0) != iProver_top
    | v3_funct_2(X1,X0,X0) != iProver_top
    | m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) != iProver_top
    | v1_funct_1(X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_26])).

cnf(c_3250,plain,
    ( k2_funct_2(sK0,sK1) = k2_funct_1(sK1)
    | v1_funct_2(sK1,sK0,sK0) != iProver_top
    | v3_funct_2(sK1,sK0,sK0) != iProver_top
    | v1_funct_1(sK1) != iProver_top ),
    inference(superposition,[status(thm)],[c_1279,c_1281])).

cnf(c_30,negated_conjecture,
    ( v1_funct_2(sK1,sK0,sK0) ),
    inference(cnf_transformation,[],[f82])).

cnf(c_1594,plain,
    ( ~ v1_funct_2(sK1,X0,X0)
    | ~ v3_funct_2(sK1,X0,X0)
    | ~ m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
    | ~ v1_funct_1(sK1)
    | k2_funct_2(X0,sK1) = k2_funct_1(sK1) ),
    inference(instantiation,[status(thm)],[c_26])).

cnf(c_1596,plain,
    ( ~ v1_funct_2(sK1,sK0,sK0)
    | ~ v3_funct_2(sK1,sK0,sK0)
    | ~ m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
    | ~ v1_funct_1(sK1)
    | k2_funct_2(sK0,sK1) = k2_funct_1(sK1) ),
    inference(instantiation,[status(thm)],[c_1594])).

cnf(c_4033,plain,
    ( k2_funct_2(sK0,sK1) = k2_funct_1(sK1) ),
    inference(global_propositional_subsumption,[status(thm)],[c_3250,c_31,c_30,c_29,c_28,c_1596])).

cnf(c_20,plain,
    ( ~ v1_funct_2(X0,X1,X1)
    | ~ v3_funct_2(X0,X1,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X1)))
    | m1_subset_1(k2_funct_2(X1,X0),k1_zfmisc_1(k2_zfmisc_1(X1,X1)))
    | ~ v1_funct_1(X0) ),
    inference(cnf_transformation,[],[f76])).

cnf(c_1287,plain,
    ( v1_funct_2(X0,X1,X1) != iProver_top
    | v3_funct_2(X0,X1,X1) != iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X1))) != iProver_top
    | m1_subset_1(k2_funct_2(X1,X0),k1_zfmisc_1(k2_zfmisc_1(X1,X1))) = iProver_top
    | v1_funct_1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_20])).

cnf(c_4376,plain,
    ( v1_funct_2(sK1,sK0,sK0) != iProver_top
    | v3_funct_2(sK1,sK0,sK0) != iProver_top
    | m1_subset_1(k2_funct_1(sK1),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) = iProver_top
    | m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) != iProver_top
    | v1_funct_1(sK1) != iProver_top ),
    inference(superposition,[status(thm)],[c_4033,c_1287])).

cnf(c_33,plain,
    ( v1_funct_2(sK1,sK0,sK0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_30])).

cnf(c_5058,plain,
    ( m1_subset_1(k2_funct_1(sK1),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_4376,c_32,c_33,c_34,c_35])).

cnf(c_13,plain,
    ( v4_relat_1(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) ),
    inference(cnf_transformation,[],[f65])).

cnf(c_7,plain,
    ( ~ v4_relat_1(X0,X1)
    | ~ v1_relat_1(X0)
    | k7_relat_1(X0,X1) = X0 ),
    inference(cnf_transformation,[],[f60])).

cnf(c_353,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ v1_relat_1(X0)
    | k7_relat_1(X0,X1) = X0 ),
    inference(resolution,[status(thm)],[c_13,c_7])).

cnf(c_1275,plain,
    ( k7_relat_1(X0,X1) = X0
    | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) != iProver_top
    | v1_relat_1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_353])).

cnf(c_5068,plain,
    ( k7_relat_1(k2_funct_1(sK1),sK0) = k2_funct_1(sK1)
    | v1_relat_1(k2_funct_1(sK1)) != iProver_top ),
    inference(superposition,[status(thm)],[c_5058,c_1275])).

cnf(c_5063,plain,
    ( v1_relat_1(k2_zfmisc_1(sK0,sK0)) != iProver_top
    | v1_relat_1(k2_funct_1(sK1)) = iProver_top ),
    inference(superposition,[status(thm)],[c_5058,c_1297])).

cnf(c_5888,plain,
    ( k7_relat_1(k2_funct_1(sK1),sK0) = k2_funct_1(sK1) ),
    inference(global_propositional_subsumption,[status(thm)],[c_5068,c_103,c_5063])).

cnf(c_5538,plain,
    ( v1_relat_1(k2_funct_1(sK1)) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_5063,c_103])).

cnf(c_5,plain,
    ( ~ v1_relat_1(X0)
    | k2_relat_1(k7_relat_1(X0,X1)) = k9_relat_1(X0,X1) ),
    inference(cnf_transformation,[],[f58])).

cnf(c_1295,plain,
    ( k2_relat_1(k7_relat_1(X0,X1)) = k9_relat_1(X0,X1)
    | v1_relat_1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_5])).

cnf(c_5543,plain,
    ( k2_relat_1(k7_relat_1(k2_funct_1(sK1),X0)) = k9_relat_1(k2_funct_1(sK1),X0) ),
    inference(superposition,[status(thm)],[c_5538,c_1295])).

cnf(c_5891,plain,
    ( k9_relat_1(k2_funct_1(sK1),sK0) = k2_relat_1(k2_funct_1(sK1)) ),
    inference(superposition,[status(thm)],[c_5888,c_5543])).

cnf(c_5066,plain,
    ( k2_relat_1(k2_funct_1(sK1)) = sK0
    | v3_funct_2(k2_funct_1(sK1),sK0,sK0) != iProver_top
    | v1_funct_1(k2_funct_1(sK1)) != iProver_top
    | v1_relat_1(k2_funct_1(sK1)) != iProver_top ),
    inference(superposition,[status(thm)],[c_5058,c_1274])).

cnf(c_23,plain,
    ( ~ v1_funct_2(X0,X1,X1)
    | ~ v3_funct_2(X0,X1,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X1)))
    | ~ v1_funct_1(X0)
    | v1_funct_1(k2_funct_2(X1,X0)) ),
    inference(cnf_transformation,[],[f73])).

cnf(c_1284,plain,
    ( v1_funct_2(X0,X1,X1) != iProver_top
    | v3_funct_2(X0,X1,X1) != iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X1))) != iProver_top
    | v1_funct_1(X0) != iProver_top
    | v1_funct_1(k2_funct_2(X1,X0)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_23])).

cnf(c_3867,plain,
    ( v1_funct_2(sK1,sK0,sK0) != iProver_top
    | v3_funct_2(sK1,sK0,sK0) != iProver_top
    | v1_funct_1(k2_funct_2(sK0,sK1)) = iProver_top
    | v1_funct_1(sK1) != iProver_top ),
    inference(superposition,[status(thm)],[c_1279,c_1284])).

cnf(c_1579,plain,
    ( ~ v1_funct_2(sK1,X0,X0)
    | ~ v3_funct_2(sK1,X0,X0)
    | ~ m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
    | v1_funct_1(k2_funct_2(X0,sK1))
    | ~ v1_funct_1(sK1) ),
    inference(instantiation,[status(thm)],[c_23])).

cnf(c_1580,plain,
    ( v1_funct_2(sK1,X0,X0) != iProver_top
    | v3_funct_2(sK1,X0,X0) != iProver_top
    | m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) != iProver_top
    | v1_funct_1(k2_funct_2(X0,sK1)) = iProver_top
    | v1_funct_1(sK1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1579])).

cnf(c_1582,plain,
    ( v1_funct_2(sK1,sK0,sK0) != iProver_top
    | v3_funct_2(sK1,sK0,sK0) != iProver_top
    | m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) != iProver_top
    | v1_funct_1(k2_funct_2(sK0,sK1)) = iProver_top
    | v1_funct_1(sK1) != iProver_top ),
    inference(instantiation,[status(thm)],[c_1580])).

cnf(c_4127,plain,
    ( v1_funct_1(k2_funct_2(sK0,sK1)) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_3867,c_32,c_33,c_34,c_35,c_1582])).

cnf(c_4131,plain,
    ( v1_funct_1(k2_funct_1(sK1)) = iProver_top ),
    inference(light_normalisation,[status(thm)],[c_4127,c_4033])).

cnf(c_21,plain,
    ( ~ v1_funct_2(X0,X1,X1)
    | ~ v3_funct_2(X0,X1,X1)
    | v3_funct_2(k2_funct_2(X1,X0),X1,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X1)))
    | ~ v1_funct_1(X0) ),
    inference(cnf_transformation,[],[f75])).

cnf(c_1286,plain,
    ( v1_funct_2(X0,X1,X1) != iProver_top
    | v3_funct_2(X0,X1,X1) != iProver_top
    | v3_funct_2(k2_funct_2(X1,X0),X1,X1) = iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X1))) != iProver_top
    | v1_funct_1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_21])).

cnf(c_4348,plain,
    ( v1_funct_2(sK1,sK0,sK0) != iProver_top
    | v3_funct_2(k2_funct_2(sK0,sK1),sK0,sK0) = iProver_top
    | v3_funct_2(sK1,sK0,sK0) != iProver_top
    | v1_funct_1(sK1) != iProver_top ),
    inference(superposition,[status(thm)],[c_1279,c_1286])).

cnf(c_4353,plain,
    ( v1_funct_2(sK1,sK0,sK0) != iProver_top
    | v3_funct_2(k2_funct_1(sK1),sK0,sK0) = iProver_top
    | v3_funct_2(sK1,sK0,sK0) != iProver_top
    | v1_funct_1(sK1) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_4348,c_4033])).

cnf(c_5998,plain,
    ( k2_relat_1(k2_funct_1(sK1)) = sK0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_5066,c_32,c_33,c_34,c_103,c_4131,c_4353,c_5063])).

cnf(c_7188,plain,
    ( k9_relat_1(k2_funct_1(sK1),sK0) = sK0 ),
    inference(light_normalisation,[status(thm)],[c_5891,c_5998])).

cnf(c_7344,plain,
    ( k1_relat_1(sK1) = sK0
    | v1_funct_1(sK1) != iProver_top
    | v1_relat_1(sK1) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_7333,c_3003,c_7188])).

cnf(c_7509,plain,
    ( k1_relat_1(sK1) = sK0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_7344,c_32,c_35,c_103,c_1722])).

cnf(c_25,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X4,X5)))
    | ~ v1_funct_1(X0)
    | ~ v1_funct_1(X3)
    | k1_partfun1(X4,X5,X1,X2,X3,X0) = k5_relat_1(X3,X0) ),
    inference(cnf_transformation,[],[f78])).

cnf(c_1282,plain,
    ( k1_partfun1(X0,X1,X2,X3,X4,X5) = k5_relat_1(X4,X5)
    | m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) != iProver_top
    | m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top
    | v1_funct_1(X5) != iProver_top
    | v1_funct_1(X4) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_25])).

cnf(c_5073,plain,
    ( k1_partfun1(X0,X1,sK0,sK0,X2,k2_funct_1(sK1)) = k5_relat_1(X2,k2_funct_1(sK1))
    | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top
    | v1_funct_1(X2) != iProver_top
    | v1_funct_1(k2_funct_1(sK1)) != iProver_top ),
    inference(superposition,[status(thm)],[c_5058,c_1282])).

cnf(c_6823,plain,
    ( v1_funct_1(X2) != iProver_top
    | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top
    | k1_partfun1(X0,X1,sK0,sK0,X2,k2_funct_1(sK1)) = k5_relat_1(X2,k2_funct_1(sK1)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_5073,c_4131])).

cnf(c_6824,plain,
    ( k1_partfun1(X0,X1,sK0,sK0,X2,k2_funct_1(sK1)) = k5_relat_1(X2,k2_funct_1(sK1))
    | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top
    | v1_funct_1(X2) != iProver_top ),
    inference(renaming,[status(thm)],[c_6823])).

cnf(c_6834,plain,
    ( k1_partfun1(sK0,sK0,sK0,sK0,sK1,k2_funct_1(sK1)) = k5_relat_1(sK1,k2_funct_1(sK1))
    | v1_funct_1(sK1) != iProver_top ),
    inference(superposition,[status(thm)],[c_1279,c_6824])).

cnf(c_11,plain,
    ( ~ v2_funct_1(X0)
    | ~ v1_funct_1(X0)
    | ~ v1_relat_1(X0)
    | k5_relat_1(X0,k2_funct_1(X0)) = k6_partfun1(k1_relat_1(X0)) ),
    inference(cnf_transformation,[],[f87])).

cnf(c_1290,plain,
    ( k5_relat_1(X0,k2_funct_1(X0)) = k6_partfun1(k1_relat_1(X0))
    | v2_funct_1(X0) != iProver_top
    | v1_funct_1(X0) != iProver_top
    | v1_relat_1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_11])).

cnf(c_4016,plain,
    ( k5_relat_1(sK1,k2_funct_1(sK1)) = k6_partfun1(k1_relat_1(sK1))
    | v1_funct_1(sK1) != iProver_top
    | v1_relat_1(sK1) != iProver_top ),
    inference(superposition,[status(thm)],[c_4010,c_1290])).

cnf(c_1547,plain,
    ( ~ v3_funct_2(sK1,sK0,sK0)
    | ~ m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
    | v2_funct_1(sK1)
    | ~ v1_funct_1(sK1) ),
    inference(instantiation,[status(thm)],[c_1545])).

cnf(c_1656,plain,
    ( ~ v2_funct_1(sK1)
    | ~ v1_funct_1(sK1)
    | ~ v1_relat_1(sK1)
    | k5_relat_1(sK1,k2_funct_1(sK1)) = k6_partfun1(k1_relat_1(sK1)) ),
    inference(instantiation,[status(thm)],[c_11])).

cnf(c_4290,plain,
    ( k5_relat_1(sK1,k2_funct_1(sK1)) = k6_partfun1(k1_relat_1(sK1)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_4016,c_31,c_29,c_28,c_102,c_1547,c_1656,c_1721])).

cnf(c_6842,plain,
    ( k1_partfun1(sK0,sK0,sK0,sK0,sK1,k2_funct_1(sK1)) = k6_partfun1(k1_relat_1(sK1))
    | v1_funct_1(sK1) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_6834,c_4290])).

cnf(c_6967,plain,
    ( k1_partfun1(sK0,sK0,sK0,sK0,sK1,k2_funct_1(sK1)) = k6_partfun1(k1_relat_1(sK1)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_6842,c_32])).

cnf(c_4643,plain,
    ( k1_partfun1(X0,X1,sK0,sK0,X2,sK1) = k5_relat_1(X2,sK1)
    | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top
    | v1_funct_1(X2) != iProver_top
    | v1_funct_1(sK1) != iProver_top ),
    inference(superposition,[status(thm)],[c_1279,c_1282])).

cnf(c_4774,plain,
    ( v1_funct_1(X2) != iProver_top
    | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top
    | k1_partfun1(X0,X1,sK0,sK0,X2,sK1) = k5_relat_1(X2,sK1) ),
    inference(global_propositional_subsumption,[status(thm)],[c_4643,c_32])).

cnf(c_4775,plain,
    ( k1_partfun1(X0,X1,sK0,sK0,X2,sK1) = k5_relat_1(X2,sK1)
    | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top
    | v1_funct_1(X2) != iProver_top ),
    inference(renaming,[status(thm)],[c_4774])).

cnf(c_4783,plain,
    ( k1_partfun1(X0,X0,sK0,sK0,k2_funct_2(X0,X1),sK1) = k5_relat_1(k2_funct_2(X0,X1),sK1)
    | v1_funct_2(X1,X0,X0) != iProver_top
    | v3_funct_2(X1,X0,X0) != iProver_top
    | m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) != iProver_top
    | v1_funct_1(X1) != iProver_top
    | v1_funct_1(k2_funct_2(X0,X1)) != iProver_top ),
    inference(superposition,[status(thm)],[c_1287,c_4775])).

cnf(c_5275,plain,
    ( k1_partfun1(X0,X0,sK0,sK0,k2_funct_2(X0,X1),sK1) = k5_relat_1(k2_funct_2(X0,X1),sK1)
    | v1_funct_2(X1,X0,X0) != iProver_top
    | v3_funct_2(X1,X0,X0) != iProver_top
    | m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) != iProver_top
    | v1_funct_1(X1) != iProver_top ),
    inference(forward_subsumption_resolution,[status(thm)],[c_4783,c_1284])).

cnf(c_5281,plain,
    ( k1_partfun1(sK0,sK0,sK0,sK0,k2_funct_2(sK0,sK1),sK1) = k5_relat_1(k2_funct_2(sK0,sK1),sK1)
    | v1_funct_2(sK1,sK0,sK0) != iProver_top
    | v3_funct_2(sK1,sK0,sK0) != iProver_top
    | v1_funct_1(sK1) != iProver_top ),
    inference(superposition,[status(thm)],[c_1279,c_5275])).

cnf(c_10,plain,
    ( ~ v2_funct_1(X0)
    | ~ v1_funct_1(X0)
    | ~ v1_relat_1(X0)
    | k5_relat_1(k2_funct_1(X0),X0) = k6_partfun1(k2_relat_1(X0)) ),
    inference(cnf_transformation,[],[f86])).

cnf(c_1291,plain,
    ( k5_relat_1(k2_funct_1(X0),X0) = k6_partfun1(k2_relat_1(X0))
    | v2_funct_1(X0) != iProver_top
    | v1_funct_1(X0) != iProver_top
    | v1_relat_1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_10])).

cnf(c_4015,plain,
    ( k5_relat_1(k2_funct_1(sK1),sK1) = k6_partfun1(k2_relat_1(sK1))
    | v1_funct_1(sK1) != iProver_top
    | v1_relat_1(sK1) != iProver_top ),
    inference(superposition,[status(thm)],[c_4010,c_1291])).

cnf(c_4026,plain,
    ( k5_relat_1(k2_funct_1(sK1),sK1) = k6_partfun1(sK0)
    | v1_funct_1(sK1) != iProver_top
    | v1_relat_1(sK1) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_4015,c_2187])).

cnf(c_4213,plain,
    ( k5_relat_1(k2_funct_1(sK1),sK1) = k6_partfun1(sK0) ),
    inference(global_propositional_subsumption,[status(thm)],[c_4026,c_32,c_35,c_103,c_1722])).

cnf(c_5295,plain,
    ( k1_partfun1(sK0,sK0,sK0,sK0,k2_funct_1(sK1),sK1) = k6_partfun1(sK0)
    | v1_funct_2(sK1,sK0,sK0) != iProver_top
    | v3_funct_2(sK1,sK0,sK0) != iProver_top
    | v1_funct_1(sK1) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_5281,c_4033,c_4213])).

cnf(c_5064,plain,
    ( k1_partfun1(sK0,sK0,sK0,sK0,k2_funct_1(sK1),sK1) = k5_relat_1(k2_funct_1(sK1),sK1)
    | v1_funct_1(k2_funct_1(sK1)) != iProver_top ),
    inference(superposition,[status(thm)],[c_5058,c_4775])).

cnf(c_5138,plain,
    ( k1_partfun1(sK0,sK0,sK0,sK0,k2_funct_1(sK1),sK1) = k6_partfun1(sK0)
    | v1_funct_1(k2_funct_1(sK1)) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_5064,c_4213])).

cnf(c_5333,plain,
    ( k1_partfun1(sK0,sK0,sK0,sK0,k2_funct_1(sK1),sK1) = k6_partfun1(sK0) ),
    inference(global_propositional_subsumption,[status(thm)],[c_5295,c_4131,c_5138])).

cnf(c_27,negated_conjecture,
    ( ~ r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK0,sK0,sK0,k2_funct_2(sK0,sK1),sK1),k6_partfun1(sK0))
    | ~ r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK0,sK0,sK0,sK1,k2_funct_2(sK0,sK1)),k6_partfun1(sK0)) ),
    inference(cnf_transformation,[],[f85])).

cnf(c_1280,plain,
    ( r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK0,sK0,sK0,k2_funct_2(sK0,sK1),sK1),k6_partfun1(sK0)) != iProver_top
    | r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK0,sK0,sK0,sK1,k2_funct_2(sK0,sK1)),k6_partfun1(sK0)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_27])).

cnf(c_4036,plain,
    ( r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK0,sK0,sK0,k2_funct_1(sK1),sK1),k6_partfun1(sK0)) != iProver_top
    | r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK0,sK0,sK0,sK1,k2_funct_1(sK1)),k6_partfun1(sK0)) != iProver_top ),
    inference(demodulation,[status(thm)],[c_4033,c_1280])).

cnf(c_5336,plain,
    ( r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK0,sK0,sK0,sK1,k2_funct_1(sK1)),k6_partfun1(sK0)) != iProver_top
    | r2_relset_1(sK0,sK0,k6_partfun1(sK0),k6_partfun1(sK0)) != iProver_top ),
    inference(demodulation,[status(thm)],[c_5333,c_4036])).

cnf(c_24,plain,
    ( m1_subset_1(k6_partfun1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0))) ),
    inference(cnf_transformation,[],[f77])).

cnf(c_43,plain,
    ( m1_subset_1(k6_partfun1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_24])).

cnf(c_45,plain,
    ( m1_subset_1(k6_partfun1(sK0),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) = iProver_top ),
    inference(instantiation,[status(thm)],[c_43])).

cnf(c_14,plain,
    ( r2_relset_1(X0,X1,X2,X2)
    | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ),
    inference(cnf_transformation,[],[f67])).

cnf(c_1564,plain,
    ( r2_relset_1(X0,X0,k6_partfun1(X0),k6_partfun1(X0))
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
    | ~ m1_subset_1(k6_partfun1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0))) ),
    inference(instantiation,[status(thm)],[c_14])).

cnf(c_2486,plain,
    ( r2_relset_1(X0,X0,k6_partfun1(X0),k6_partfun1(X0))
    | ~ m1_subset_1(k6_partfun1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0))) ),
    inference(instantiation,[status(thm)],[c_1564])).

cnf(c_2487,plain,
    ( r2_relset_1(X0,X0,k6_partfun1(X0),k6_partfun1(X0)) = iProver_top
    | m1_subset_1(k6_partfun1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2486])).

cnf(c_2489,plain,
    ( r2_relset_1(sK0,sK0,k6_partfun1(sK0),k6_partfun1(sK0)) = iProver_top
    | m1_subset_1(k6_partfun1(sK0),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) != iProver_top ),
    inference(instantiation,[status(thm)],[c_2487])).

cnf(c_5454,plain,
    ( r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK0,sK0,sK0,sK1,k2_funct_1(sK1)),k6_partfun1(sK0)) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_5336,c_45,c_2489])).

cnf(c_6970,plain,
    ( r2_relset_1(sK0,sK0,k6_partfun1(k1_relat_1(sK1)),k6_partfun1(sK0)) != iProver_top ),
    inference(demodulation,[status(thm)],[c_6967,c_5454])).

cnf(c_7512,plain,
    ( r2_relset_1(sK0,sK0,k6_partfun1(sK0),k6_partfun1(sK0)) != iProver_top ),
    inference(demodulation,[status(thm)],[c_7509,c_6970])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_7512,c_2489,c_45])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.04/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.04/0.12  % Command    : iproveropt_run.sh %d %s
% 0.12/0.33  % Computer   : n008.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.33  % CPULimit   : 60
% 0.12/0.33  % WCLimit    : 600
% 0.12/0.33  % DateTime   : Tue Dec  1 20:47:30 EST 2020
% 0.12/0.33  % CPUTime    : 
% 0.12/0.34  % Running in FOF mode
% 3.42/0.98  % SZS status Started for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.42/0.98  
% 3.42/0.98  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 3.42/0.98  
% 3.42/0.98  ------  iProver source info
% 3.42/0.98  
% 3.42/0.98  git: date: 2020-06-30 10:37:57 +0100
% 3.42/0.98  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 3.42/0.98  git: non_committed_changes: false
% 3.42/0.98  git: last_make_outside_of_git: false
% 3.42/0.98  
% 3.42/0.98  ------ 
% 3.42/0.98  
% 3.42/0.98  ------ Input Options
% 3.42/0.98  
% 3.42/0.98  --out_options                           all
% 3.42/0.98  --tptp_safe_out                         true
% 3.42/0.98  --problem_path                          ""
% 3.42/0.98  --include_path                          ""
% 3.42/0.98  --clausifier                            res/vclausify_rel
% 3.42/0.98  --clausifier_options                    --mode clausify
% 3.42/0.98  --stdin                                 false
% 3.42/0.98  --stats_out                             all
% 3.42/0.98  
% 3.42/0.98  ------ General Options
% 3.42/0.98  
% 3.42/0.98  --fof                                   false
% 3.42/0.98  --time_out_real                         305.
% 3.42/0.98  --time_out_virtual                      -1.
% 3.42/0.98  --symbol_type_check                     false
% 3.42/0.98  --clausify_out                          false
% 3.42/0.98  --sig_cnt_out                           false
% 3.42/0.98  --trig_cnt_out                          false
% 3.42/0.98  --trig_cnt_out_tolerance                1.
% 3.42/0.98  --trig_cnt_out_sk_spl                   false
% 3.42/0.98  --abstr_cl_out                          false
% 3.42/0.98  
% 3.42/0.98  ------ Global Options
% 3.42/0.98  
% 3.42/0.98  --schedule                              default
% 3.42/0.98  --add_important_lit                     false
% 3.42/0.98  --prop_solver_per_cl                    1000
% 3.42/0.98  --min_unsat_core                        false
% 3.42/0.98  --soft_assumptions                      false
% 3.42/0.98  --soft_lemma_size                       3
% 3.42/0.98  --prop_impl_unit_size                   0
% 3.42/0.98  --prop_impl_unit                        []
% 3.42/0.98  --share_sel_clauses                     true
% 3.42/0.98  --reset_solvers                         false
% 3.42/0.98  --bc_imp_inh                            [conj_cone]
% 3.42/0.98  --conj_cone_tolerance                   3.
% 3.42/0.98  --extra_neg_conj                        none
% 3.42/0.98  --large_theory_mode                     true
% 3.42/0.98  --prolific_symb_bound                   200
% 3.42/0.98  --lt_threshold                          2000
% 3.42/0.98  --clause_weak_htbl                      true
% 3.42/0.98  --gc_record_bc_elim                     false
% 3.42/0.98  
% 3.42/0.98  ------ Preprocessing Options
% 3.42/0.98  
% 3.42/0.98  --preprocessing_flag                    true
% 3.42/0.98  --time_out_prep_mult                    0.1
% 3.42/0.98  --splitting_mode                        input
% 3.42/0.98  --splitting_grd                         true
% 3.42/0.98  --splitting_cvd                         false
% 3.42/0.98  --splitting_cvd_svl                     false
% 3.42/0.98  --splitting_nvd                         32
% 3.42/0.98  --sub_typing                            true
% 3.42/0.98  --prep_gs_sim                           true
% 3.42/0.98  --prep_unflatten                        true
% 3.42/0.98  --prep_res_sim                          true
% 3.42/0.98  --prep_upred                            true
% 3.42/0.98  --prep_sem_filter                       exhaustive
% 3.42/0.98  --prep_sem_filter_out                   false
% 3.42/0.98  --pred_elim                             true
% 3.42/0.98  --res_sim_input                         true
% 3.42/0.98  --eq_ax_congr_red                       true
% 3.42/0.98  --pure_diseq_elim                       true
% 3.42/0.98  --brand_transform                       false
% 3.42/0.98  --non_eq_to_eq                          false
% 3.42/0.98  --prep_def_merge                        true
% 3.42/0.98  --prep_def_merge_prop_impl              false
% 3.42/0.98  --prep_def_merge_mbd                    true
% 3.42/0.98  --prep_def_merge_tr_red                 false
% 3.42/0.98  --prep_def_merge_tr_cl                  false
% 3.42/0.98  --smt_preprocessing                     true
% 3.42/0.98  --smt_ac_axioms                         fast
% 3.42/0.98  --preprocessed_out                      false
% 3.42/0.98  --preprocessed_stats                    false
% 3.42/0.98  
% 3.42/0.98  ------ Abstraction refinement Options
% 3.42/0.98  
% 3.42/0.98  --abstr_ref                             []
% 3.42/0.98  --abstr_ref_prep                        false
% 3.42/0.98  --abstr_ref_until_sat                   false
% 3.42/0.98  --abstr_ref_sig_restrict                funpre
% 3.42/0.98  --abstr_ref_af_restrict_to_split_sk     false
% 3.42/0.98  --abstr_ref_under                       []
% 3.42/0.98  
% 3.42/0.98  ------ SAT Options
% 3.42/0.98  
% 3.42/0.98  --sat_mode                              false
% 3.42/0.98  --sat_fm_restart_options                ""
% 3.42/0.98  --sat_gr_def                            false
% 3.42/0.98  --sat_epr_types                         true
% 3.42/0.98  --sat_non_cyclic_types                  false
% 3.42/0.98  --sat_finite_models                     false
% 3.42/0.98  --sat_fm_lemmas                         false
% 3.42/0.98  --sat_fm_prep                           false
% 3.42/0.98  --sat_fm_uc_incr                        true
% 3.42/0.98  --sat_out_model                         small
% 3.42/0.98  --sat_out_clauses                       false
% 3.42/0.98  
% 3.42/0.98  ------ QBF Options
% 3.42/0.98  
% 3.42/0.98  --qbf_mode                              false
% 3.42/0.98  --qbf_elim_univ                         false
% 3.42/0.98  --qbf_dom_inst                          none
% 3.42/0.98  --qbf_dom_pre_inst                      false
% 3.42/0.98  --qbf_sk_in                             false
% 3.42/0.98  --qbf_pred_elim                         true
% 3.42/0.98  --qbf_split                             512
% 3.42/0.98  
% 3.42/0.98  ------ BMC1 Options
% 3.42/0.98  
% 3.42/0.98  --bmc1_incremental                      false
% 3.42/0.98  --bmc1_axioms                           reachable_all
% 3.42/0.98  --bmc1_min_bound                        0
% 3.42/0.98  --bmc1_max_bound                        -1
% 3.42/0.98  --bmc1_max_bound_default                -1
% 3.42/0.98  --bmc1_symbol_reachability              true
% 3.42/0.98  --bmc1_property_lemmas                  false
% 3.42/0.98  --bmc1_k_induction                      false
% 3.42/0.98  --bmc1_non_equiv_states                 false
% 3.42/0.98  --bmc1_deadlock                         false
% 3.42/0.98  --bmc1_ucm                              false
% 3.42/0.98  --bmc1_add_unsat_core                   none
% 3.42/0.98  --bmc1_unsat_core_children              false
% 3.42/0.98  --bmc1_unsat_core_extrapolate_axioms    false
% 3.42/0.98  --bmc1_out_stat                         full
% 3.42/0.98  --bmc1_ground_init                      false
% 3.42/0.98  --bmc1_pre_inst_next_state              false
% 3.42/0.98  --bmc1_pre_inst_state                   false
% 3.42/0.98  --bmc1_pre_inst_reach_state             false
% 3.42/0.98  --bmc1_out_unsat_core                   false
% 3.42/0.98  --bmc1_aig_witness_out                  false
% 3.42/0.98  --bmc1_verbose                          false
% 3.42/0.98  --bmc1_dump_clauses_tptp                false
% 3.42/0.98  --bmc1_dump_unsat_core_tptp             false
% 3.42/0.98  --bmc1_dump_file                        -
% 3.42/0.98  --bmc1_ucm_expand_uc_limit              128
% 3.42/0.98  --bmc1_ucm_n_expand_iterations          6
% 3.42/0.98  --bmc1_ucm_extend_mode                  1
% 3.42/0.98  --bmc1_ucm_init_mode                    2
% 3.42/0.98  --bmc1_ucm_cone_mode                    none
% 3.42/0.98  --bmc1_ucm_reduced_relation_type        0
% 3.42/0.98  --bmc1_ucm_relax_model                  4
% 3.42/0.98  --bmc1_ucm_full_tr_after_sat            true
% 3.42/0.98  --bmc1_ucm_expand_neg_assumptions       false
% 3.42/0.98  --bmc1_ucm_layered_model                none
% 3.42/0.98  --bmc1_ucm_max_lemma_size               10
% 3.42/0.98  
% 3.42/0.98  ------ AIG Options
% 3.42/0.98  
% 3.42/0.98  --aig_mode                              false
% 3.42/0.98  
% 3.42/0.98  ------ Instantiation Options
% 3.42/0.98  
% 3.42/0.98  --instantiation_flag                    true
% 3.42/0.98  --inst_sos_flag                         false
% 3.42/0.98  --inst_sos_phase                        true
% 3.42/0.98  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 3.42/0.98  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 3.42/0.98  --inst_lit_sel_side                     num_symb
% 3.42/0.98  --inst_solver_per_active                1400
% 3.42/0.98  --inst_solver_calls_frac                1.
% 3.42/0.98  --inst_passive_queue_type               priority_queues
% 3.42/0.98  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 3.42/0.98  --inst_passive_queues_freq              [25;2]
% 3.42/0.98  --inst_dismatching                      true
% 3.42/0.98  --inst_eager_unprocessed_to_passive     true
% 3.42/0.98  --inst_prop_sim_given                   true
% 3.42/0.98  --inst_prop_sim_new                     false
% 3.42/0.98  --inst_subs_new                         false
% 3.42/0.98  --inst_eq_res_simp                      false
% 3.42/0.98  --inst_subs_given                       false
% 3.42/0.98  --inst_orphan_elimination               true
% 3.42/0.98  --inst_learning_loop_flag               true
% 3.42/0.98  --inst_learning_start                   3000
% 3.42/0.98  --inst_learning_factor                  2
% 3.42/0.98  --inst_start_prop_sim_after_learn       3
% 3.42/0.98  --inst_sel_renew                        solver
% 3.42/0.98  --inst_lit_activity_flag                true
% 3.42/0.98  --inst_restr_to_given                   false
% 3.42/0.98  --inst_activity_threshold               500
% 3.42/0.98  --inst_out_proof                        true
% 3.42/0.98  
% 3.42/0.98  ------ Resolution Options
% 3.42/0.98  
% 3.42/0.98  --resolution_flag                       true
% 3.42/0.98  --res_lit_sel                           adaptive
% 3.42/0.98  --res_lit_sel_side                      none
% 3.42/0.98  --res_ordering                          kbo
% 3.42/0.98  --res_to_prop_solver                    active
% 3.42/0.98  --res_prop_simpl_new                    false
% 3.42/0.98  --res_prop_simpl_given                  true
% 3.42/0.98  --res_passive_queue_type                priority_queues
% 3.42/0.98  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 3.42/0.98  --res_passive_queues_freq               [15;5]
% 3.42/0.98  --res_forward_subs                      full
% 3.42/0.98  --res_backward_subs                     full
% 3.42/0.98  --res_forward_subs_resolution           true
% 3.42/0.98  --res_backward_subs_resolution          true
% 3.42/0.98  --res_orphan_elimination                true
% 3.42/0.98  --res_time_limit                        2.
% 3.42/0.98  --res_out_proof                         true
% 3.42/0.98  
% 3.42/0.98  ------ Superposition Options
% 3.42/0.98  
% 3.42/0.98  --superposition_flag                    true
% 3.42/0.98  --sup_passive_queue_type                priority_queues
% 3.42/0.98  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 3.42/0.98  --sup_passive_queues_freq               [8;1;4]
% 3.42/0.98  --demod_completeness_check              fast
% 3.42/0.98  --demod_use_ground                      true
% 3.42/0.98  --sup_to_prop_solver                    passive
% 3.42/0.98  --sup_prop_simpl_new                    true
% 3.42/0.98  --sup_prop_simpl_given                  true
% 3.42/0.98  --sup_fun_splitting                     false
% 3.42/0.98  --sup_smt_interval                      50000
% 3.42/0.98  
% 3.42/0.98  ------ Superposition Simplification Setup
% 3.42/0.98  
% 3.42/0.98  --sup_indices_passive                   []
% 3.42/0.98  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.42/0.98  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.42/0.98  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.42/0.98  --sup_full_triv                         [TrivRules;PropSubs]
% 3.42/0.98  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.42/0.98  --sup_full_bw                           [BwDemod]
% 3.42/0.98  --sup_immed_triv                        [TrivRules]
% 3.42/0.98  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 3.42/0.98  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.42/0.98  --sup_immed_bw_main                     []
% 3.42/0.98  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 3.42/0.98  --sup_input_triv                        [Unflattening;TrivRules]
% 3.42/0.98  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.42/0.98  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 3.42/0.98  
% 3.42/0.98  ------ Combination Options
% 3.42/0.98  
% 3.42/0.98  --comb_res_mult                         3
% 3.42/0.98  --comb_sup_mult                         2
% 3.42/0.98  --comb_inst_mult                        10
% 3.42/0.98  
% 3.42/0.98  ------ Debug Options
% 3.42/0.98  
% 3.42/0.98  --dbg_backtrace                         false
% 3.42/0.98  --dbg_dump_prop_clauses                 false
% 3.42/0.98  --dbg_dump_prop_clauses_file            -
% 3.42/0.98  --dbg_out_stat                          false
% 3.42/0.98  ------ Parsing...
% 3.42/0.98  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 3.42/0.98  
% 3.42/0.98  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe:1:0s pe:2:0s pe_e  sf_s  rm: 3 0s  sf_e  pe_s  pe_e 
% 3.42/0.98  
% 3.42/0.98  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 3.42/0.98  
% 3.42/0.98  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 3.42/0.98  ------ Proving...
% 3.42/0.98  ------ Problem Properties 
% 3.42/0.98  
% 3.42/0.98  
% 3.42/0.98  clauses                                 26
% 3.42/0.98  conjectures                             5
% 3.42/0.98  EPR                                     5
% 3.42/0.98  Horn                                    26
% 3.42/0.98  unary                                   7
% 3.42/0.98  binary                                  3
% 3.42/0.98  lits                                    81
% 3.42/0.98  lits eq                                 11
% 3.42/0.98  fd_pure                                 0
% 3.42/0.98  fd_pseudo                               0
% 3.42/0.98  fd_cond                                 0
% 3.42/0.98  fd_pseudo_cond                          2
% 3.42/0.98  AC symbols                              0
% 3.42/0.98  
% 3.42/0.98  ------ Schedule dynamic 5 is on 
% 3.42/0.98  
% 3.42/0.98  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" Time Limit: 10.
% 3.42/0.98  
% 3.42/0.98  
% 3.42/0.98  ------ 
% 3.42/0.98  Current options:
% 3.42/0.98  ------ 
% 3.42/0.98  
% 3.42/0.98  ------ Input Options
% 3.42/0.98  
% 3.42/0.98  --out_options                           all
% 3.42/0.98  --tptp_safe_out                         true
% 3.42/0.98  --problem_path                          ""
% 3.42/0.98  --include_path                          ""
% 3.42/0.98  --clausifier                            res/vclausify_rel
% 3.42/0.98  --clausifier_options                    --mode clausify
% 3.42/0.98  --stdin                                 false
% 3.42/0.98  --stats_out                             all
% 3.42/0.98  
% 3.42/0.98  ------ General Options
% 3.42/0.98  
% 3.42/0.98  --fof                                   false
% 3.42/0.98  --time_out_real                         305.
% 3.42/0.98  --time_out_virtual                      -1.
% 3.42/0.98  --symbol_type_check                     false
% 3.42/0.98  --clausify_out                          false
% 3.42/0.98  --sig_cnt_out                           false
% 3.42/0.98  --trig_cnt_out                          false
% 3.42/0.98  --trig_cnt_out_tolerance                1.
% 3.42/0.98  --trig_cnt_out_sk_spl                   false
% 3.42/0.98  --abstr_cl_out                          false
% 3.42/0.98  
% 3.42/0.98  ------ Global Options
% 3.42/0.98  
% 3.42/0.98  --schedule                              default
% 3.42/0.98  --add_important_lit                     false
% 3.42/0.98  --prop_solver_per_cl                    1000
% 3.42/0.98  --min_unsat_core                        false
% 3.42/0.98  --soft_assumptions                      false
% 3.42/0.98  --soft_lemma_size                       3
% 3.42/0.98  --prop_impl_unit_size                   0
% 3.42/0.98  --prop_impl_unit                        []
% 3.42/0.98  --share_sel_clauses                     true
% 3.42/0.98  --reset_solvers                         false
% 3.42/0.98  --bc_imp_inh                            [conj_cone]
% 3.42/0.98  --conj_cone_tolerance                   3.
% 3.42/0.98  --extra_neg_conj                        none
% 3.42/0.98  --large_theory_mode                     true
% 3.42/0.98  --prolific_symb_bound                   200
% 3.42/0.98  --lt_threshold                          2000
% 3.42/0.98  --clause_weak_htbl                      true
% 3.42/0.98  --gc_record_bc_elim                     false
% 3.42/0.98  
% 3.42/0.98  ------ Preprocessing Options
% 3.42/0.98  
% 3.42/0.98  --preprocessing_flag                    true
% 3.42/0.98  --time_out_prep_mult                    0.1
% 3.42/0.98  --splitting_mode                        input
% 3.42/0.98  --splitting_grd                         true
% 3.42/0.98  --splitting_cvd                         false
% 3.42/0.98  --splitting_cvd_svl                     false
% 3.42/0.98  --splitting_nvd                         32
% 3.42/0.98  --sub_typing                            true
% 3.42/0.98  --prep_gs_sim                           true
% 3.42/0.98  --prep_unflatten                        true
% 3.42/0.98  --prep_res_sim                          true
% 3.42/0.98  --prep_upred                            true
% 3.42/0.98  --prep_sem_filter                       exhaustive
% 3.42/0.98  --prep_sem_filter_out                   false
% 3.42/0.98  --pred_elim                             true
% 3.42/0.98  --res_sim_input                         true
% 3.42/0.98  --eq_ax_congr_red                       true
% 3.42/0.98  --pure_diseq_elim                       true
% 3.42/0.98  --brand_transform                       false
% 3.42/0.98  --non_eq_to_eq                          false
% 3.42/0.98  --prep_def_merge                        true
% 3.42/0.98  --prep_def_merge_prop_impl              false
% 3.42/0.98  --prep_def_merge_mbd                    true
% 3.42/0.98  --prep_def_merge_tr_red                 false
% 3.42/0.98  --prep_def_merge_tr_cl                  false
% 3.42/0.98  --smt_preprocessing                     true
% 3.42/0.98  --smt_ac_axioms                         fast
% 3.42/0.98  --preprocessed_out                      false
% 3.42/0.98  --preprocessed_stats                    false
% 3.42/0.98  
% 3.42/0.98  ------ Abstraction refinement Options
% 3.42/0.98  
% 3.42/0.98  --abstr_ref                             []
% 3.42/0.98  --abstr_ref_prep                        false
% 3.42/0.98  --abstr_ref_until_sat                   false
% 3.42/0.98  --abstr_ref_sig_restrict                funpre
% 3.42/0.98  --abstr_ref_af_restrict_to_split_sk     false
% 3.42/0.98  --abstr_ref_under                       []
% 3.42/0.98  
% 3.42/0.98  ------ SAT Options
% 3.42/0.98  
% 3.42/0.98  --sat_mode                              false
% 3.42/0.98  --sat_fm_restart_options                ""
% 3.42/0.98  --sat_gr_def                            false
% 3.42/0.98  --sat_epr_types                         true
% 3.42/0.98  --sat_non_cyclic_types                  false
% 3.42/0.98  --sat_finite_models                     false
% 3.42/0.98  --sat_fm_lemmas                         false
% 3.42/0.98  --sat_fm_prep                           false
% 3.42/0.98  --sat_fm_uc_incr                        true
% 3.42/0.98  --sat_out_model                         small
% 3.42/0.98  --sat_out_clauses                       false
% 3.42/0.98  
% 3.42/0.98  ------ QBF Options
% 3.42/0.98  
% 3.42/0.98  --qbf_mode                              false
% 3.42/0.98  --qbf_elim_univ                         false
% 3.42/0.98  --qbf_dom_inst                          none
% 3.42/0.98  --qbf_dom_pre_inst                      false
% 3.42/0.98  --qbf_sk_in                             false
% 3.42/0.98  --qbf_pred_elim                         true
% 3.42/0.98  --qbf_split                             512
% 3.42/0.98  
% 3.42/0.98  ------ BMC1 Options
% 3.42/0.98  
% 3.42/0.98  --bmc1_incremental                      false
% 3.42/0.98  --bmc1_axioms                           reachable_all
% 3.42/0.98  --bmc1_min_bound                        0
% 3.42/0.98  --bmc1_max_bound                        -1
% 3.42/0.98  --bmc1_max_bound_default                -1
% 3.42/0.98  --bmc1_symbol_reachability              true
% 3.42/0.98  --bmc1_property_lemmas                  false
% 3.42/0.98  --bmc1_k_induction                      false
% 3.42/0.98  --bmc1_non_equiv_states                 false
% 3.42/0.98  --bmc1_deadlock                         false
% 3.42/0.98  --bmc1_ucm                              false
% 3.42/0.98  --bmc1_add_unsat_core                   none
% 3.42/0.98  --bmc1_unsat_core_children              false
% 3.42/0.98  --bmc1_unsat_core_extrapolate_axioms    false
% 3.42/0.98  --bmc1_out_stat                         full
% 3.42/0.98  --bmc1_ground_init                      false
% 3.42/0.98  --bmc1_pre_inst_next_state              false
% 3.42/0.98  --bmc1_pre_inst_state                   false
% 3.42/0.98  --bmc1_pre_inst_reach_state             false
% 3.42/0.98  --bmc1_out_unsat_core                   false
% 3.42/0.98  --bmc1_aig_witness_out                  false
% 3.42/0.98  --bmc1_verbose                          false
% 3.42/0.98  --bmc1_dump_clauses_tptp                false
% 3.42/0.98  --bmc1_dump_unsat_core_tptp             false
% 3.42/0.98  --bmc1_dump_file                        -
% 3.42/0.98  --bmc1_ucm_expand_uc_limit              128
% 3.42/0.98  --bmc1_ucm_n_expand_iterations          6
% 3.42/0.98  --bmc1_ucm_extend_mode                  1
% 3.42/0.98  --bmc1_ucm_init_mode                    2
% 3.42/0.98  --bmc1_ucm_cone_mode                    none
% 3.42/0.98  --bmc1_ucm_reduced_relation_type        0
% 3.42/0.98  --bmc1_ucm_relax_model                  4
% 3.42/0.98  --bmc1_ucm_full_tr_after_sat            true
% 3.42/0.98  --bmc1_ucm_expand_neg_assumptions       false
% 3.42/0.98  --bmc1_ucm_layered_model                none
% 3.42/0.98  --bmc1_ucm_max_lemma_size               10
% 3.42/0.98  
% 3.42/0.98  ------ AIG Options
% 3.42/0.98  
% 3.42/0.98  --aig_mode                              false
% 3.42/0.98  
% 3.42/0.98  ------ Instantiation Options
% 3.42/0.98  
% 3.42/0.98  --instantiation_flag                    true
% 3.42/0.98  --inst_sos_flag                         false
% 3.42/0.98  --inst_sos_phase                        true
% 3.42/0.98  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 3.42/0.98  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 3.42/0.98  --inst_lit_sel_side                     none
% 3.42/0.98  --inst_solver_per_active                1400
% 3.42/0.98  --inst_solver_calls_frac                1.
% 3.42/0.98  --inst_passive_queue_type               priority_queues
% 3.42/0.98  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 3.42/0.98  --inst_passive_queues_freq              [25;2]
% 3.42/0.98  --inst_dismatching                      true
% 3.42/0.98  --inst_eager_unprocessed_to_passive     true
% 3.42/0.98  --inst_prop_sim_given                   true
% 3.42/0.98  --inst_prop_sim_new                     false
% 3.42/0.98  --inst_subs_new                         false
% 3.42/0.98  --inst_eq_res_simp                      false
% 3.42/0.98  --inst_subs_given                       false
% 3.42/0.98  --inst_orphan_elimination               true
% 3.42/0.98  --inst_learning_loop_flag               true
% 3.42/0.98  --inst_learning_start                   3000
% 3.42/0.98  --inst_learning_factor                  2
% 3.42/0.98  --inst_start_prop_sim_after_learn       3
% 3.42/0.98  --inst_sel_renew                        solver
% 3.42/0.98  --inst_lit_activity_flag                true
% 3.42/0.98  --inst_restr_to_given                   false
% 3.42/0.98  --inst_activity_threshold               500
% 3.42/0.98  --inst_out_proof                        true
% 3.42/0.98  
% 3.42/0.98  ------ Resolution Options
% 3.42/0.98  
% 3.42/0.98  --resolution_flag                       false
% 3.42/0.98  --res_lit_sel                           adaptive
% 3.42/0.98  --res_lit_sel_side                      none
% 3.42/0.98  --res_ordering                          kbo
% 3.42/0.98  --res_to_prop_solver                    active
% 3.42/0.98  --res_prop_simpl_new                    false
% 3.42/0.98  --res_prop_simpl_given                  true
% 3.42/0.98  --res_passive_queue_type                priority_queues
% 3.42/0.98  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 3.42/0.98  --res_passive_queues_freq               [15;5]
% 3.42/0.98  --res_forward_subs                      full
% 3.42/0.98  --res_backward_subs                     full
% 3.42/0.98  --res_forward_subs_resolution           true
% 3.42/0.98  --res_backward_subs_resolution          true
% 3.42/0.98  --res_orphan_elimination                true
% 3.42/0.98  --res_time_limit                        2.
% 3.42/0.98  --res_out_proof                         true
% 3.42/0.98  
% 3.42/0.98  ------ Superposition Options
% 3.42/0.98  
% 3.42/0.98  --superposition_flag                    true
% 3.42/0.98  --sup_passive_queue_type                priority_queues
% 3.42/0.98  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 3.42/0.98  --sup_passive_queues_freq               [8;1;4]
% 3.42/0.98  --demod_completeness_check              fast
% 3.42/0.98  --demod_use_ground                      true
% 3.42/0.98  --sup_to_prop_solver                    passive
% 3.42/0.98  --sup_prop_simpl_new                    true
% 3.42/0.98  --sup_prop_simpl_given                  true
% 3.42/0.98  --sup_fun_splitting                     false
% 3.42/0.98  --sup_smt_interval                      50000
% 3.42/0.98  
% 3.42/0.98  ------ Superposition Simplification Setup
% 3.42/0.98  
% 3.42/0.98  --sup_indices_passive                   []
% 3.42/0.98  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.42/0.98  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.42/0.98  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.42/0.98  --sup_full_triv                         [TrivRules;PropSubs]
% 3.42/0.98  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.42/0.98  --sup_full_bw                           [BwDemod]
% 3.42/0.98  --sup_immed_triv                        [TrivRules]
% 3.42/0.98  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 3.42/0.98  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.42/0.98  --sup_immed_bw_main                     []
% 3.42/0.98  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 3.42/0.98  --sup_input_triv                        [Unflattening;TrivRules]
% 3.42/0.98  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.42/0.98  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 3.42/0.98  
% 3.42/0.98  ------ Combination Options
% 3.42/0.98  
% 3.42/0.98  --comb_res_mult                         3
% 3.42/0.98  --comb_sup_mult                         2
% 3.42/0.98  --comb_inst_mult                        10
% 3.42/0.98  
% 3.42/0.98  ------ Debug Options
% 3.42/0.98  
% 3.42/0.98  --dbg_backtrace                         false
% 3.42/0.98  --dbg_dump_prop_clauses                 false
% 3.42/0.98  --dbg_dump_prop_clauses_file            -
% 3.42/0.98  --dbg_out_stat                          false
% 3.42/0.98  
% 3.42/0.98  
% 3.42/0.98  
% 3.42/0.98  
% 3.42/0.98  ------ Proving...
% 3.42/0.98  
% 3.42/0.98  
% 3.42/0.98  % SZS status Theorem for theBenchmark.p
% 3.42/0.98  
% 3.42/0.98  % SZS output start CNFRefutation for theBenchmark.p
% 3.42/0.98  
% 3.42/0.98  fof(f19,conjecture,(
% 3.42/0.98    ! [X0,X1] : ((m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v3_funct_2(X1,X0,X0) & v1_funct_2(X1,X0,X0) & v1_funct_1(X1)) => (r2_relset_1(X0,X0,k1_partfun1(X0,X0,X0,X0,k2_funct_2(X0,X1),X1),k6_partfun1(X0)) & r2_relset_1(X0,X0,k1_partfun1(X0,X0,X0,X0,X1,k2_funct_2(X0,X1)),k6_partfun1(X0))))),
% 3.42/0.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.42/0.98  
% 3.42/0.98  fof(f20,negated_conjecture,(
% 3.42/0.98    ~! [X0,X1] : ((m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v3_funct_2(X1,X0,X0) & v1_funct_2(X1,X0,X0) & v1_funct_1(X1)) => (r2_relset_1(X0,X0,k1_partfun1(X0,X0,X0,X0,k2_funct_2(X0,X1),X1),k6_partfun1(X0)) & r2_relset_1(X0,X0,k1_partfun1(X0,X0,X0,X0,X1,k2_funct_2(X0,X1)),k6_partfun1(X0))))),
% 3.42/0.98    inference(negated_conjecture,[],[f19])).
% 3.42/0.98  
% 3.42/0.98  fof(f46,plain,(
% 3.42/0.98    ? [X0,X1] : ((~r2_relset_1(X0,X0,k1_partfun1(X0,X0,X0,X0,k2_funct_2(X0,X1),X1),k6_partfun1(X0)) | ~r2_relset_1(X0,X0,k1_partfun1(X0,X0,X0,X0,X1,k2_funct_2(X0,X1)),k6_partfun1(X0))) & (m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v3_funct_2(X1,X0,X0) & v1_funct_2(X1,X0,X0) & v1_funct_1(X1)))),
% 3.42/0.98    inference(ennf_transformation,[],[f20])).
% 3.42/0.98  
% 3.42/0.98  fof(f47,plain,(
% 3.42/0.98    ? [X0,X1] : ((~r2_relset_1(X0,X0,k1_partfun1(X0,X0,X0,X0,k2_funct_2(X0,X1),X1),k6_partfun1(X0)) | ~r2_relset_1(X0,X0,k1_partfun1(X0,X0,X0,X0,X1,k2_funct_2(X0,X1)),k6_partfun1(X0))) & m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v3_funct_2(X1,X0,X0) & v1_funct_2(X1,X0,X0) & v1_funct_1(X1))),
% 3.42/0.98    inference(flattening,[],[f46])).
% 3.42/0.98  
% 3.42/0.98  fof(f51,plain,(
% 3.42/0.98    ? [X0,X1] : ((~r2_relset_1(X0,X0,k1_partfun1(X0,X0,X0,X0,k2_funct_2(X0,X1),X1),k6_partfun1(X0)) | ~r2_relset_1(X0,X0,k1_partfun1(X0,X0,X0,X0,X1,k2_funct_2(X0,X1)),k6_partfun1(X0))) & m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v3_funct_2(X1,X0,X0) & v1_funct_2(X1,X0,X0) & v1_funct_1(X1)) => ((~r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK0,sK0,sK0,k2_funct_2(sK0,sK1),sK1),k6_partfun1(sK0)) | ~r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK0,sK0,sK0,sK1,k2_funct_2(sK0,sK1)),k6_partfun1(sK0))) & m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) & v3_funct_2(sK1,sK0,sK0) & v1_funct_2(sK1,sK0,sK0) & v1_funct_1(sK1))),
% 3.42/0.98    introduced(choice_axiom,[])).
% 3.42/0.98  
% 3.42/0.98  fof(f52,plain,(
% 3.42/0.98    (~r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK0,sK0,sK0,k2_funct_2(sK0,sK1),sK1),k6_partfun1(sK0)) | ~r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK0,sK0,sK0,sK1,k2_funct_2(sK0,sK1)),k6_partfun1(sK0))) & m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) & v3_funct_2(sK1,sK0,sK0) & v1_funct_2(sK1,sK0,sK0) & v1_funct_1(sK1)),
% 3.42/0.98    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f47,f51])).
% 3.42/0.98  
% 3.42/0.98  fof(f84,plain,(
% 3.42/0.98    m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))),
% 3.42/0.98    inference(cnf_transformation,[],[f52])).
% 3.42/0.98  
% 3.42/0.98  fof(f12,axiom,(
% 3.42/0.98    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => ((v3_funct_2(X2,X0,X1) & v1_funct_1(X2)) => (v2_funct_2(X2,X1) & v2_funct_1(X2) & v1_funct_1(X2))))),
% 3.42/0.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.42/0.98  
% 3.42/0.98  fof(f36,plain,(
% 3.42/0.98    ! [X0,X1,X2] : (((v2_funct_2(X2,X1) & v2_funct_1(X2) & v1_funct_1(X2)) | (~v3_funct_2(X2,X0,X1) | ~v1_funct_1(X2))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 3.42/0.98    inference(ennf_transformation,[],[f12])).
% 3.42/0.98  
% 3.42/0.98  fof(f37,plain,(
% 3.42/0.98    ! [X0,X1,X2] : ((v2_funct_2(X2,X1) & v2_funct_1(X2) & v1_funct_1(X2)) | ~v3_funct_2(X2,X0,X1) | ~v1_funct_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 3.42/0.98    inference(flattening,[],[f36])).
% 3.42/0.98  
% 3.42/0.98  fof(f69,plain,(
% 3.42/0.98    ( ! [X2,X0,X1] : (v2_funct_1(X2) | ~v3_funct_2(X2,X0,X1) | ~v1_funct_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 3.42/0.98    inference(cnf_transformation,[],[f37])).
% 3.42/0.98  
% 3.42/0.98  fof(f81,plain,(
% 3.42/0.98    v1_funct_1(sK1)),
% 3.42/0.98    inference(cnf_transformation,[],[f52])).
% 3.42/0.98  
% 3.42/0.98  fof(f83,plain,(
% 3.42/0.98    v3_funct_2(sK1,sK0,sK0)),
% 3.42/0.98    inference(cnf_transformation,[],[f52])).
% 3.42/0.98  
% 3.42/0.98  fof(f1,axiom,(
% 3.42/0.98    ! [X0,X1] : (X0 = X1 <=> (r1_tarski(X1,X0) & r1_tarski(X0,X1)))),
% 3.42/0.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.42/0.98  
% 3.42/0.98  fof(f48,plain,(
% 3.42/0.98    ! [X0,X1] : ((X0 = X1 | (~r1_tarski(X1,X0) | ~r1_tarski(X0,X1))) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 3.42/0.98    inference(nnf_transformation,[],[f1])).
% 3.42/0.98  
% 3.42/0.98  fof(f49,plain,(
% 3.42/0.98    ! [X0,X1] : ((X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 3.42/0.98    inference(flattening,[],[f48])).
% 3.42/0.98  
% 3.42/0.98  fof(f53,plain,(
% 3.42/0.98    ( ! [X0,X1] : (r1_tarski(X0,X1) | X0 != X1) )),
% 3.42/0.98    inference(cnf_transformation,[],[f49])).
% 3.42/0.98  
% 3.42/0.98  fof(f89,plain,(
% 3.42/0.98    ( ! [X1] : (r1_tarski(X1,X1)) )),
% 3.42/0.98    inference(equality_resolution,[],[f53])).
% 3.42/0.98  
% 3.42/0.98  fof(f8,axiom,(
% 3.42/0.98    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => ! [X1] : ((r1_tarski(X1,k1_relat_1(X0)) & v2_funct_1(X0)) => k9_relat_1(k2_funct_1(X0),k9_relat_1(X0,X1)) = X1))),
% 3.42/0.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.42/0.98  
% 3.42/0.98  fof(f29,plain,(
% 3.42/0.98    ! [X0] : (! [X1] : (k9_relat_1(k2_funct_1(X0),k9_relat_1(X0,X1)) = X1 | (~r1_tarski(X1,k1_relat_1(X0)) | ~v2_funct_1(X0))) | (~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 3.42/0.98    inference(ennf_transformation,[],[f8])).
% 3.42/0.98  
% 3.42/0.98  fof(f30,plain,(
% 3.42/0.98    ! [X0] : (! [X1] : (k9_relat_1(k2_funct_1(X0),k9_relat_1(X0,X1)) = X1 | ~r1_tarski(X1,k1_relat_1(X0)) | ~v2_funct_1(X0)) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 3.42/0.98    inference(flattening,[],[f29])).
% 3.42/0.98  
% 3.42/0.98  fof(f62,plain,(
% 3.42/0.98    ( ! [X0,X1] : (k9_relat_1(k2_funct_1(X0),k9_relat_1(X0,X1)) = X1 | ~r1_tarski(X1,k1_relat_1(X0)) | ~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 3.42/0.98    inference(cnf_transformation,[],[f30])).
% 3.42/0.98  
% 3.42/0.98  fof(f70,plain,(
% 3.42/0.98    ( ! [X2,X0,X1] : (v2_funct_2(X2,X1) | ~v3_funct_2(X2,X0,X1) | ~v1_funct_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 3.42/0.98    inference(cnf_transformation,[],[f37])).
% 3.42/0.98  
% 3.42/0.98  fof(f13,axiom,(
% 3.42/0.98    ! [X0,X1] : ((v5_relat_1(X1,X0) & v1_relat_1(X1)) => (v2_funct_2(X1,X0) <=> k2_relat_1(X1) = X0))),
% 3.42/0.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.42/0.98  
% 3.42/0.98  fof(f38,plain,(
% 3.42/0.98    ! [X0,X1] : ((v2_funct_2(X1,X0) <=> k2_relat_1(X1) = X0) | (~v5_relat_1(X1,X0) | ~v1_relat_1(X1)))),
% 3.42/0.98    inference(ennf_transformation,[],[f13])).
% 3.42/0.98  
% 3.42/0.98  fof(f39,plain,(
% 3.42/0.98    ! [X0,X1] : ((v2_funct_2(X1,X0) <=> k2_relat_1(X1) = X0) | ~v5_relat_1(X1,X0) | ~v1_relat_1(X1))),
% 3.42/0.98    inference(flattening,[],[f38])).
% 3.42/0.98  
% 3.42/0.98  fof(f50,plain,(
% 3.42/0.98    ! [X0,X1] : (((v2_funct_2(X1,X0) | k2_relat_1(X1) != X0) & (k2_relat_1(X1) = X0 | ~v2_funct_2(X1,X0))) | ~v5_relat_1(X1,X0) | ~v1_relat_1(X1))),
% 3.42/0.98    inference(nnf_transformation,[],[f39])).
% 3.42/0.98  
% 3.42/0.98  fof(f71,plain,(
% 3.42/0.98    ( ! [X0,X1] : (k2_relat_1(X1) = X0 | ~v2_funct_2(X1,X0) | ~v5_relat_1(X1,X0) | ~v1_relat_1(X1)) )),
% 3.42/0.98    inference(cnf_transformation,[],[f50])).
% 3.42/0.98  
% 3.42/0.98  fof(f10,axiom,(
% 3.42/0.98    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => (v5_relat_1(X2,X1) & v4_relat_1(X2,X0)))),
% 3.42/0.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.42/0.98  
% 3.42/0.98  fof(f33,plain,(
% 3.42/0.98    ! [X0,X1,X2] : ((v5_relat_1(X2,X1) & v4_relat_1(X2,X0)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 3.42/0.98    inference(ennf_transformation,[],[f10])).
% 3.42/0.98  
% 3.42/0.98  fof(f66,plain,(
% 3.42/0.98    ( ! [X2,X0,X1] : (v5_relat_1(X2,X1) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 3.42/0.98    inference(cnf_transformation,[],[f33])).
% 3.42/0.98  
% 3.42/0.98  fof(f3,axiom,(
% 3.42/0.98    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1))),
% 3.42/0.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.42/0.98  
% 3.42/0.98  fof(f57,plain,(
% 3.42/0.98    ( ! [X0,X1] : (v1_relat_1(k2_zfmisc_1(X0,X1))) )),
% 3.42/0.98    inference(cnf_transformation,[],[f3])).
% 3.42/0.98  
% 3.42/0.98  fof(f2,axiom,(
% 3.42/0.98    ! [X0] : (v1_relat_1(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => v1_relat_1(X1)))),
% 3.42/0.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.42/0.98  
% 3.42/0.98  fof(f22,plain,(
% 3.42/0.98    ! [X0] : (! [X1] : (v1_relat_1(X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) | ~v1_relat_1(X0))),
% 3.42/0.98    inference(ennf_transformation,[],[f2])).
% 3.42/0.98  
% 3.42/0.98  fof(f56,plain,(
% 3.42/0.98    ( ! [X0,X1] : (v1_relat_1(X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0)) | ~v1_relat_1(X0)) )),
% 3.42/0.98    inference(cnf_transformation,[],[f22])).
% 3.42/0.98  
% 3.42/0.98  fof(f7,axiom,(
% 3.42/0.98    ! [X0,X1] : ((v1_funct_1(X1) & v1_relat_1(X1)) => (r1_tarski(X0,k2_relat_1(X1)) => k9_relat_1(X1,k10_relat_1(X1,X0)) = X0))),
% 3.42/0.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.42/0.98  
% 3.42/0.98  fof(f27,plain,(
% 3.42/0.98    ! [X0,X1] : ((k9_relat_1(X1,k10_relat_1(X1,X0)) = X0 | ~r1_tarski(X0,k2_relat_1(X1))) | (~v1_funct_1(X1) | ~v1_relat_1(X1)))),
% 3.42/0.98    inference(ennf_transformation,[],[f7])).
% 3.42/0.98  
% 3.42/0.98  fof(f28,plain,(
% 3.42/0.98    ! [X0,X1] : (k9_relat_1(X1,k10_relat_1(X1,X0)) = X0 | ~r1_tarski(X0,k2_relat_1(X1)) | ~v1_funct_1(X1) | ~v1_relat_1(X1))),
% 3.42/0.98    inference(flattening,[],[f27])).
% 3.42/0.98  
% 3.42/0.98  fof(f61,plain,(
% 3.42/0.98    ( ! [X0,X1] : (k9_relat_1(X1,k10_relat_1(X1,X0)) = X0 | ~r1_tarski(X0,k2_relat_1(X1)) | ~v1_funct_1(X1) | ~v1_relat_1(X1)) )),
% 3.42/0.98    inference(cnf_transformation,[],[f28])).
% 3.42/0.98  
% 3.42/0.98  fof(f5,axiom,(
% 3.42/0.98    ! [X0] : (v1_relat_1(X0) => k10_relat_1(X0,k2_relat_1(X0)) = k1_relat_1(X0))),
% 3.42/0.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.42/0.98  
% 3.42/0.98  fof(f24,plain,(
% 3.42/0.98    ! [X0] : (k10_relat_1(X0,k2_relat_1(X0)) = k1_relat_1(X0) | ~v1_relat_1(X0))),
% 3.42/0.98    inference(ennf_transformation,[],[f5])).
% 3.42/0.98  
% 3.42/0.98  fof(f59,plain,(
% 3.42/0.98    ( ! [X0] : (k10_relat_1(X0,k2_relat_1(X0)) = k1_relat_1(X0) | ~v1_relat_1(X0)) )),
% 3.42/0.98    inference(cnf_transformation,[],[f24])).
% 3.42/0.98  
% 3.42/0.98  fof(f17,axiom,(
% 3.42/0.98    ! [X0,X1] : ((m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v3_funct_2(X1,X0,X0) & v1_funct_2(X1,X0,X0) & v1_funct_1(X1)) => k2_funct_1(X1) = k2_funct_2(X0,X1))),
% 3.42/0.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.42/0.98  
% 3.42/0.98  fof(f44,plain,(
% 3.42/0.98    ! [X0,X1] : (k2_funct_1(X1) = k2_funct_2(X0,X1) | (~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) | ~v3_funct_2(X1,X0,X0) | ~v1_funct_2(X1,X0,X0) | ~v1_funct_1(X1)))),
% 3.42/0.98    inference(ennf_transformation,[],[f17])).
% 3.42/0.98  
% 3.42/0.98  fof(f45,plain,(
% 3.42/0.98    ! [X0,X1] : (k2_funct_1(X1) = k2_funct_2(X0,X1) | ~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) | ~v3_funct_2(X1,X0,X0) | ~v1_funct_2(X1,X0,X0) | ~v1_funct_1(X1))),
% 3.42/0.98    inference(flattening,[],[f44])).
% 3.42/0.98  
% 3.42/0.98  fof(f79,plain,(
% 3.42/0.98    ( ! [X0,X1] : (k2_funct_1(X1) = k2_funct_2(X0,X1) | ~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) | ~v3_funct_2(X1,X0,X0) | ~v1_funct_2(X1,X0,X0) | ~v1_funct_1(X1)) )),
% 3.42/0.98    inference(cnf_transformation,[],[f45])).
% 3.42/0.98  
% 3.42/0.98  fof(f82,plain,(
% 3.42/0.98    v1_funct_2(sK1,sK0,sK0)),
% 3.42/0.98    inference(cnf_transformation,[],[f52])).
% 3.42/0.98  
% 3.42/0.98  fof(f14,axiom,(
% 3.42/0.98    ! [X0,X1] : ((m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v3_funct_2(X1,X0,X0) & v1_funct_2(X1,X0,X0) & v1_funct_1(X1)) => (m1_subset_1(k2_funct_2(X0,X1),k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v3_funct_2(k2_funct_2(X0,X1),X0,X0) & v1_funct_2(k2_funct_2(X0,X1),X0,X0) & v1_funct_1(k2_funct_2(X0,X1))))),
% 3.42/0.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.42/0.98  
% 3.42/0.98  fof(f40,plain,(
% 3.42/0.98    ! [X0,X1] : ((m1_subset_1(k2_funct_2(X0,X1),k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v3_funct_2(k2_funct_2(X0,X1),X0,X0) & v1_funct_2(k2_funct_2(X0,X1),X0,X0) & v1_funct_1(k2_funct_2(X0,X1))) | (~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) | ~v3_funct_2(X1,X0,X0) | ~v1_funct_2(X1,X0,X0) | ~v1_funct_1(X1)))),
% 3.42/0.98    inference(ennf_transformation,[],[f14])).
% 3.42/0.98  
% 3.42/0.98  fof(f41,plain,(
% 3.42/0.98    ! [X0,X1] : ((m1_subset_1(k2_funct_2(X0,X1),k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v3_funct_2(k2_funct_2(X0,X1),X0,X0) & v1_funct_2(k2_funct_2(X0,X1),X0,X0) & v1_funct_1(k2_funct_2(X0,X1))) | ~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) | ~v3_funct_2(X1,X0,X0) | ~v1_funct_2(X1,X0,X0) | ~v1_funct_1(X1))),
% 3.42/0.98    inference(flattening,[],[f40])).
% 3.42/0.98  
% 3.42/0.98  fof(f76,plain,(
% 3.42/0.98    ( ! [X0,X1] : (m1_subset_1(k2_funct_2(X0,X1),k1_zfmisc_1(k2_zfmisc_1(X0,X0))) | ~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) | ~v3_funct_2(X1,X0,X0) | ~v1_funct_2(X1,X0,X0) | ~v1_funct_1(X1)) )),
% 3.42/0.98    inference(cnf_transformation,[],[f41])).
% 3.42/0.98  
% 3.42/0.98  fof(f65,plain,(
% 3.42/0.98    ( ! [X2,X0,X1] : (v4_relat_1(X2,X0) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 3.42/0.98    inference(cnf_transformation,[],[f33])).
% 3.42/0.98  
% 3.42/0.98  fof(f6,axiom,(
% 3.42/0.98    ! [X0,X1] : ((v4_relat_1(X1,X0) & v1_relat_1(X1)) => k7_relat_1(X1,X0) = X1)),
% 3.42/0.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.42/0.98  
% 3.42/0.98  fof(f25,plain,(
% 3.42/0.98    ! [X0,X1] : (k7_relat_1(X1,X0) = X1 | (~v4_relat_1(X1,X0) | ~v1_relat_1(X1)))),
% 3.42/0.98    inference(ennf_transformation,[],[f6])).
% 3.42/0.98  
% 3.42/0.98  fof(f26,plain,(
% 3.42/0.98    ! [X0,X1] : (k7_relat_1(X1,X0) = X1 | ~v4_relat_1(X1,X0) | ~v1_relat_1(X1))),
% 3.42/0.98    inference(flattening,[],[f25])).
% 3.42/0.98  
% 3.42/0.98  fof(f60,plain,(
% 3.42/0.98    ( ! [X0,X1] : (k7_relat_1(X1,X0) = X1 | ~v4_relat_1(X1,X0) | ~v1_relat_1(X1)) )),
% 3.42/0.98    inference(cnf_transformation,[],[f26])).
% 3.42/0.98  
% 3.42/0.98  fof(f4,axiom,(
% 3.42/0.98    ! [X0,X1] : (v1_relat_1(X1) => k2_relat_1(k7_relat_1(X1,X0)) = k9_relat_1(X1,X0))),
% 3.42/0.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.42/0.98  
% 3.42/0.98  fof(f23,plain,(
% 3.42/0.98    ! [X0,X1] : (k2_relat_1(k7_relat_1(X1,X0)) = k9_relat_1(X1,X0) | ~v1_relat_1(X1))),
% 3.42/0.98    inference(ennf_transformation,[],[f4])).
% 3.42/0.98  
% 3.42/0.98  fof(f58,plain,(
% 3.42/0.98    ( ! [X0,X1] : (k2_relat_1(k7_relat_1(X1,X0)) = k9_relat_1(X1,X0) | ~v1_relat_1(X1)) )),
% 3.42/0.98    inference(cnf_transformation,[],[f23])).
% 3.42/0.98  
% 3.42/0.98  fof(f73,plain,(
% 3.42/0.98    ( ! [X0,X1] : (v1_funct_1(k2_funct_2(X0,X1)) | ~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) | ~v3_funct_2(X1,X0,X0) | ~v1_funct_2(X1,X0,X0) | ~v1_funct_1(X1)) )),
% 3.42/0.98    inference(cnf_transformation,[],[f41])).
% 3.42/0.98  
% 3.42/0.98  fof(f75,plain,(
% 3.42/0.98    ( ! [X0,X1] : (v3_funct_2(k2_funct_2(X0,X1),X0,X0) | ~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) | ~v3_funct_2(X1,X0,X0) | ~v1_funct_2(X1,X0,X0) | ~v1_funct_1(X1)) )),
% 3.42/0.98    inference(cnf_transformation,[],[f41])).
% 3.42/0.98  
% 3.42/0.98  fof(f16,axiom,(
% 3.42/0.98    ! [X0,X1,X2,X3,X4,X5] : ((m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) & v1_funct_1(X5) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_1(X4)) => k5_relat_1(X4,X5) = k1_partfun1(X0,X1,X2,X3,X4,X5))),
% 3.42/0.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.42/0.98  
% 3.42/0.98  fof(f42,plain,(
% 3.42/0.98    ! [X0,X1,X2,X3,X4,X5] : (k5_relat_1(X4,X5) = k1_partfun1(X0,X1,X2,X3,X4,X5) | (~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X4)))),
% 3.42/0.98    inference(ennf_transformation,[],[f16])).
% 3.42/0.98  
% 3.42/0.98  fof(f43,plain,(
% 3.42/0.98    ! [X0,X1,X2,X3,X4,X5] : (k5_relat_1(X4,X5) = k1_partfun1(X0,X1,X2,X3,X4,X5) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X4))),
% 3.42/0.98    inference(flattening,[],[f42])).
% 3.42/0.98  
% 3.42/0.98  fof(f78,plain,(
% 3.42/0.98    ( ! [X4,X2,X0,X5,X3,X1] : (k5_relat_1(X4,X5) = k1_partfun1(X0,X1,X2,X3,X4,X5) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X4)) )),
% 3.42/0.98    inference(cnf_transformation,[],[f43])).
% 3.42/0.98  
% 3.42/0.98  fof(f9,axiom,(
% 3.42/0.98    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => (v2_funct_1(X0) => (k5_relat_1(k2_funct_1(X0),X0) = k6_relat_1(k2_relat_1(X0)) & k5_relat_1(X0,k2_funct_1(X0)) = k6_relat_1(k1_relat_1(X0)))))),
% 3.42/0.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.42/0.98  
% 3.42/0.98  fof(f31,plain,(
% 3.42/0.98    ! [X0] : (((k5_relat_1(k2_funct_1(X0),X0) = k6_relat_1(k2_relat_1(X0)) & k5_relat_1(X0,k2_funct_1(X0)) = k6_relat_1(k1_relat_1(X0))) | ~v2_funct_1(X0)) | (~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 3.42/0.98    inference(ennf_transformation,[],[f9])).
% 3.42/0.98  
% 3.42/0.98  fof(f32,plain,(
% 3.42/0.98    ! [X0] : ((k5_relat_1(k2_funct_1(X0),X0) = k6_relat_1(k2_relat_1(X0)) & k5_relat_1(X0,k2_funct_1(X0)) = k6_relat_1(k1_relat_1(X0))) | ~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 3.42/0.98    inference(flattening,[],[f31])).
% 3.42/0.98  
% 3.42/0.98  fof(f63,plain,(
% 3.42/0.98    ( ! [X0] : (k5_relat_1(X0,k2_funct_1(X0)) = k6_relat_1(k1_relat_1(X0)) | ~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 3.42/0.98    inference(cnf_transformation,[],[f32])).
% 3.42/0.98  
% 3.42/0.98  fof(f18,axiom,(
% 3.42/0.98    ! [X0] : k6_relat_1(X0) = k6_partfun1(X0)),
% 3.42/0.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.42/0.98  
% 3.42/0.98  fof(f80,plain,(
% 3.42/0.98    ( ! [X0] : (k6_relat_1(X0) = k6_partfun1(X0)) )),
% 3.42/0.98    inference(cnf_transformation,[],[f18])).
% 3.42/0.98  
% 3.42/0.98  fof(f87,plain,(
% 3.42/0.98    ( ! [X0] : (k5_relat_1(X0,k2_funct_1(X0)) = k6_partfun1(k1_relat_1(X0)) | ~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 3.42/0.98    inference(definition_unfolding,[],[f63,f80])).
% 3.42/0.98  
% 3.42/0.98  fof(f64,plain,(
% 3.42/0.98    ( ! [X0] : (k5_relat_1(k2_funct_1(X0),X0) = k6_relat_1(k2_relat_1(X0)) | ~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 3.42/0.98    inference(cnf_transformation,[],[f32])).
% 3.42/0.98  
% 3.42/0.98  fof(f86,plain,(
% 3.42/0.98    ( ! [X0] : (k5_relat_1(k2_funct_1(X0),X0) = k6_partfun1(k2_relat_1(X0)) | ~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 3.42/0.98    inference(definition_unfolding,[],[f64,f80])).
% 3.42/0.98  
% 3.42/0.98  fof(f85,plain,(
% 3.42/0.98    ~r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK0,sK0,sK0,k2_funct_2(sK0,sK1),sK1),k6_partfun1(sK0)) | ~r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK0,sK0,sK0,sK1,k2_funct_2(sK0,sK1)),k6_partfun1(sK0))),
% 3.42/0.98    inference(cnf_transformation,[],[f52])).
% 3.42/0.98  
% 3.42/0.98  fof(f15,axiom,(
% 3.42/0.98    ! [X0] : (m1_subset_1(k6_partfun1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v1_partfun1(k6_partfun1(X0),X0))),
% 3.42/0.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.42/0.98  
% 3.42/0.98  fof(f21,plain,(
% 3.42/0.98    ! [X0] : m1_subset_1(k6_partfun1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0)))),
% 3.42/0.98    inference(pure_predicate_removal,[],[f15])).
% 3.42/0.98  
% 3.42/0.98  fof(f77,plain,(
% 3.42/0.98    ( ! [X0] : (m1_subset_1(k6_partfun1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0)))) )),
% 3.42/0.98    inference(cnf_transformation,[],[f21])).
% 3.42/0.98  
% 3.42/0.98  fof(f11,axiom,(
% 3.42/0.98    ! [X0,X1,X2,X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) => r2_relset_1(X0,X1,X2,X2))),
% 3.42/0.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.42/0.98  
% 3.42/0.98  fof(f34,plain,(
% 3.42/0.98    ! [X0,X1,X2,X3] : (r2_relset_1(X0,X1,X2,X2) | (~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))))),
% 3.42/0.98    inference(ennf_transformation,[],[f11])).
% 3.42/0.98  
% 3.42/0.98  fof(f35,plain,(
% 3.42/0.98    ! [X0,X1,X2,X3] : (r2_relset_1(X0,X1,X2,X2) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 3.42/0.98    inference(flattening,[],[f34])).
% 3.42/0.98  
% 3.42/0.98  fof(f67,plain,(
% 3.42/0.98    ( ! [X2,X0,X3,X1] : (r2_relset_1(X0,X1,X2,X2) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 3.42/0.98    inference(cnf_transformation,[],[f35])).
% 3.42/0.98  
% 3.42/0.98  cnf(c_28,negated_conjecture,
% 3.42/0.98      ( m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) ),
% 3.42/0.98      inference(cnf_transformation,[],[f84]) ).
% 3.42/0.98  
% 3.42/0.98  cnf(c_1279,plain,
% 3.42/0.98      ( m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) = iProver_top ),
% 3.42/0.98      inference(predicate_to_equality,[status(thm)],[c_28]) ).
% 3.42/0.98  
% 3.42/0.98  cnf(c_16,plain,
% 3.42/0.98      ( ~ v3_funct_2(X0,X1,X2)
% 3.42/0.98      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.42/0.98      | v2_funct_1(X0)
% 3.42/0.98      | ~ v1_funct_1(X0) ),
% 3.42/0.98      inference(cnf_transformation,[],[f69]) ).
% 3.42/0.98  
% 3.42/0.98  cnf(c_1288,plain,
% 3.42/0.98      ( v3_funct_2(X0,X1,X2) != iProver_top
% 3.42/0.98      | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) != iProver_top
% 3.42/0.98      | v2_funct_1(X0) = iProver_top
% 3.42/0.98      | v1_funct_1(X0) != iProver_top ),
% 3.42/0.98      inference(predicate_to_equality,[status(thm)],[c_16]) ).
% 3.42/0.98  
% 3.42/0.98  cnf(c_3444,plain,
% 3.42/0.98      ( v3_funct_2(sK1,sK0,sK0) != iProver_top
% 3.42/0.98      | v2_funct_1(sK1) = iProver_top
% 3.42/0.98      | v1_funct_1(sK1) != iProver_top ),
% 3.42/0.98      inference(superposition,[status(thm)],[c_1279,c_1288]) ).
% 3.42/0.98  
% 3.42/0.98  cnf(c_31,negated_conjecture,
% 3.42/0.98      ( v1_funct_1(sK1) ),
% 3.42/0.98      inference(cnf_transformation,[],[f81]) ).
% 3.42/0.98  
% 3.42/0.98  cnf(c_32,plain,
% 3.42/0.98      ( v1_funct_1(sK1) = iProver_top ),
% 3.42/0.98      inference(predicate_to_equality,[status(thm)],[c_31]) ).
% 3.42/0.98  
% 3.42/0.98  cnf(c_29,negated_conjecture,
% 3.42/0.98      ( v3_funct_2(sK1,sK0,sK0) ),
% 3.42/0.98      inference(cnf_transformation,[],[f83]) ).
% 3.42/0.98  
% 3.42/0.98  cnf(c_34,plain,
% 3.42/0.98      ( v3_funct_2(sK1,sK0,sK0) = iProver_top ),
% 3.42/0.98      inference(predicate_to_equality,[status(thm)],[c_29]) ).
% 3.42/0.98  
% 3.42/0.98  cnf(c_35,plain,
% 3.42/0.98      ( m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) = iProver_top ),
% 3.42/0.98      inference(predicate_to_equality,[status(thm)],[c_28]) ).
% 3.42/0.98  
% 3.42/0.98  cnf(c_1545,plain,
% 3.42/0.98      ( ~ v3_funct_2(sK1,X0,X1)
% 3.42/0.98      | ~ m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
% 3.42/0.98      | v2_funct_1(sK1)
% 3.42/0.98      | ~ v1_funct_1(sK1) ),
% 3.42/0.98      inference(instantiation,[status(thm)],[c_16]) ).
% 3.42/0.98  
% 3.42/0.98  cnf(c_1546,plain,
% 3.42/0.98      ( v3_funct_2(sK1,X0,X1) != iProver_top
% 3.42/0.98      | m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top
% 3.42/0.98      | v2_funct_1(sK1) = iProver_top
% 3.42/0.98      | v1_funct_1(sK1) != iProver_top ),
% 3.42/0.98      inference(predicate_to_equality,[status(thm)],[c_1545]) ).
% 3.42/0.98  
% 3.42/0.98  cnf(c_1548,plain,
% 3.42/0.98      ( v3_funct_2(sK1,sK0,sK0) != iProver_top
% 3.42/0.98      | m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) != iProver_top
% 3.42/0.98      | v2_funct_1(sK1) = iProver_top
% 3.42/0.98      | v1_funct_1(sK1) != iProver_top ),
% 3.42/0.98      inference(instantiation,[status(thm)],[c_1546]) ).
% 3.42/0.98  
% 3.42/0.98  cnf(c_4010,plain,
% 3.42/0.98      ( v2_funct_1(sK1) = iProver_top ),
% 3.42/0.98      inference(global_propositional_subsumption,
% 3.42/0.98                [status(thm)],
% 3.42/0.98                [c_3444,c_32,c_34,c_35,c_1548]) ).
% 3.42/0.98  
% 3.42/0.98  cnf(c_2,plain,
% 3.42/0.98      ( r1_tarski(X0,X0) ),
% 3.42/0.98      inference(cnf_transformation,[],[f89]) ).
% 3.42/0.98  
% 3.42/0.98  cnf(c_1298,plain,
% 3.42/0.98      ( r1_tarski(X0,X0) = iProver_top ),
% 3.42/0.98      inference(predicate_to_equality,[status(thm)],[c_2]) ).
% 3.42/0.98  
% 3.42/0.98  cnf(c_9,plain,
% 3.42/0.98      ( ~ r1_tarski(X0,k1_relat_1(X1))
% 3.42/0.98      | ~ v2_funct_1(X1)
% 3.42/0.98      | ~ v1_funct_1(X1)
% 3.42/0.98      | ~ v1_relat_1(X1)
% 3.42/0.98      | k9_relat_1(k2_funct_1(X1),k9_relat_1(X1,X0)) = X0 ),
% 3.42/0.98      inference(cnf_transformation,[],[f62]) ).
% 3.42/0.98  
% 3.42/0.98  cnf(c_1292,plain,
% 3.42/0.98      ( k9_relat_1(k2_funct_1(X0),k9_relat_1(X0,X1)) = X1
% 3.42/0.98      | r1_tarski(X1,k1_relat_1(X0)) != iProver_top
% 3.42/0.98      | v2_funct_1(X0) != iProver_top
% 3.42/0.98      | v1_funct_1(X0) != iProver_top
% 3.42/0.98      | v1_relat_1(X0) != iProver_top ),
% 3.42/0.98      inference(predicate_to_equality,[status(thm)],[c_9]) ).
% 3.42/0.98  
% 3.42/0.98  cnf(c_3467,plain,
% 3.42/0.98      ( k9_relat_1(k2_funct_1(X0),k9_relat_1(X0,k1_relat_1(X0))) = k1_relat_1(X0)
% 3.42/0.98      | v2_funct_1(X0) != iProver_top
% 3.42/0.98      | v1_funct_1(X0) != iProver_top
% 3.42/0.98      | v1_relat_1(X0) != iProver_top ),
% 3.42/0.98      inference(superposition,[status(thm)],[c_1298,c_1292]) ).
% 3.42/0.98  
% 3.42/0.98  cnf(c_7333,plain,
% 3.42/0.98      ( k9_relat_1(k2_funct_1(sK1),k9_relat_1(sK1,k1_relat_1(sK1))) = k1_relat_1(sK1)
% 3.42/0.98      | v1_funct_1(sK1) != iProver_top
% 3.42/0.98      | v1_relat_1(sK1) != iProver_top ),
% 3.42/0.98      inference(superposition,[status(thm)],[c_4010,c_3467]) ).
% 3.42/0.98  
% 3.42/0.98  cnf(c_15,plain,
% 3.42/0.98      ( ~ v3_funct_2(X0,X1,X2)
% 3.42/0.98      | v2_funct_2(X0,X2)
% 3.42/0.98      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.42/0.98      | ~ v1_funct_1(X0) ),
% 3.42/0.98      inference(cnf_transformation,[],[f70]) ).
% 3.42/0.98  
% 3.42/0.98  cnf(c_19,plain,
% 3.42/0.98      ( ~ v2_funct_2(X0,X1)
% 3.42/0.98      | ~ v5_relat_1(X0,X1)
% 3.42/0.98      | ~ v1_relat_1(X0)
% 3.42/0.98      | k2_relat_1(X0) = X1 ),
% 3.42/0.98      inference(cnf_transformation,[],[f71]) ).
% 3.42/0.98  
% 3.42/0.98  cnf(c_410,plain,
% 3.42/0.98      ( ~ v3_funct_2(X0,X1,X2)
% 3.42/0.98      | ~ v5_relat_1(X3,X4)
% 3.42/0.98      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.42/0.98      | ~ v1_funct_1(X0)
% 3.42/0.98      | ~ v1_relat_1(X3)
% 3.42/0.98      | X3 != X0
% 3.42/0.98      | X4 != X2
% 3.42/0.98      | k2_relat_1(X3) = X4 ),
% 3.42/0.98      inference(resolution_lifted,[status(thm)],[c_15,c_19]) ).
% 3.42/0.98  
% 3.42/0.98  cnf(c_411,plain,
% 3.42/0.98      ( ~ v3_funct_2(X0,X1,X2)
% 3.42/0.98      | ~ v5_relat_1(X0,X2)
% 3.42/0.98      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.42/0.98      | ~ v1_funct_1(X0)
% 3.42/0.98      | ~ v1_relat_1(X0)
% 3.42/0.98      | k2_relat_1(X0) = X2 ),
% 3.42/0.98      inference(unflattening,[status(thm)],[c_410]) ).
% 3.42/0.98  
% 3.42/0.98  cnf(c_12,plain,
% 3.42/0.98      ( v5_relat_1(X0,X1)
% 3.42/0.98      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) ),
% 3.42/0.98      inference(cnf_transformation,[],[f66]) ).
% 3.42/0.98  
% 3.42/0.98  cnf(c_427,plain,
% 3.42/0.98      ( ~ v3_funct_2(X0,X1,X2)
% 3.42/0.98      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.42/0.98      | ~ v1_funct_1(X0)
% 3.42/0.98      | ~ v1_relat_1(X0)
% 3.42/0.98      | k2_relat_1(X0) = X2 ),
% 3.42/0.98      inference(forward_subsumption_resolution,
% 3.42/0.98                [status(thm)],
% 3.42/0.98                [c_411,c_12]) ).
% 3.42/0.98  
% 3.42/0.98  cnf(c_1274,plain,
% 3.42/0.98      ( k2_relat_1(X0) = X1
% 3.42/0.98      | v3_funct_2(X0,X2,X1) != iProver_top
% 3.42/0.98      | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) != iProver_top
% 3.42/0.98      | v1_funct_1(X0) != iProver_top
% 3.42/0.98      | v1_relat_1(X0) != iProver_top ),
% 3.42/0.98      inference(predicate_to_equality,[status(thm)],[c_427]) ).
% 3.42/0.98  
% 3.42/0.98  cnf(c_1682,plain,
% 3.42/0.98      ( k2_relat_1(sK1) = sK0
% 3.42/0.98      | v3_funct_2(sK1,sK0,sK0) != iProver_top
% 3.42/0.98      | v1_funct_1(sK1) != iProver_top
% 3.42/0.98      | v1_relat_1(sK1) != iProver_top ),
% 3.42/0.98      inference(superposition,[status(thm)],[c_1279,c_1274]) ).
% 3.42/0.98  
% 3.42/0.98  cnf(c_4,plain,
% 3.42/0.98      ( v1_relat_1(k2_zfmisc_1(X0,X1)) ),
% 3.42/0.98      inference(cnf_transformation,[],[f57]) ).
% 3.42/0.98  
% 3.42/0.98  cnf(c_102,plain,
% 3.42/0.98      ( v1_relat_1(k2_zfmisc_1(sK0,sK0)) ),
% 3.42/0.98      inference(instantiation,[status(thm)],[c_4]) ).
% 3.42/0.98  
% 3.42/0.98  cnf(c_1702,plain,
% 3.42/0.98      ( ~ v3_funct_2(sK1,sK0,sK0)
% 3.42/0.98      | ~ v1_funct_1(sK1)
% 3.42/0.98      | ~ v1_relat_1(sK1)
% 3.42/0.98      | k2_relat_1(sK1) = sK0 ),
% 3.42/0.98      inference(predicate_to_equality_rev,[status(thm)],[c_1682]) ).
% 3.42/0.98  
% 3.42/0.98  cnf(c_3,plain,
% 3.42/0.98      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
% 3.42/0.98      | ~ v1_relat_1(X1)
% 3.42/0.98      | v1_relat_1(X0) ),
% 3.42/0.98      inference(cnf_transformation,[],[f56]) ).
% 3.42/0.98  
% 3.42/0.98  cnf(c_1521,plain,
% 3.42/0.98      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.42/0.98      | v1_relat_1(X0)
% 3.42/0.98      | ~ v1_relat_1(k2_zfmisc_1(X1,X2)) ),
% 3.42/0.98      inference(instantiation,[status(thm)],[c_3]) ).
% 3.42/0.98  
% 3.42/0.98  cnf(c_1721,plain,
% 3.42/0.98      ( ~ m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
% 3.42/0.98      | ~ v1_relat_1(k2_zfmisc_1(sK0,sK0))
% 3.42/0.98      | v1_relat_1(sK1) ),
% 3.42/0.98      inference(instantiation,[status(thm)],[c_1521]) ).
% 3.42/0.98  
% 3.42/0.98  cnf(c_2187,plain,
% 3.42/0.98      ( k2_relat_1(sK1) = sK0 ),
% 3.42/0.98      inference(global_propositional_subsumption,
% 3.42/0.98                [status(thm)],
% 3.42/0.98                [c_1682,c_31,c_29,c_28,c_102,c_1702,c_1721]) ).
% 3.42/0.98  
% 3.42/0.98  cnf(c_8,plain,
% 3.42/0.98      ( ~ r1_tarski(X0,k2_relat_1(X1))
% 3.42/0.98      | ~ v1_funct_1(X1)
% 3.42/0.98      | ~ v1_relat_1(X1)
% 3.42/0.98      | k9_relat_1(X1,k10_relat_1(X1,X0)) = X0 ),
% 3.42/0.98      inference(cnf_transformation,[],[f61]) ).
% 3.42/0.98  
% 3.42/0.98  cnf(c_1293,plain,
% 3.42/0.98      ( k9_relat_1(X0,k10_relat_1(X0,X1)) = X1
% 3.42/0.98      | r1_tarski(X1,k2_relat_1(X0)) != iProver_top
% 3.42/0.98      | v1_funct_1(X0) != iProver_top
% 3.42/0.98      | v1_relat_1(X0) != iProver_top ),
% 3.42/0.98      inference(predicate_to_equality,[status(thm)],[c_8]) ).
% 3.42/0.98  
% 3.42/0.98  cnf(c_2751,plain,
% 3.42/0.98      ( k9_relat_1(sK1,k10_relat_1(sK1,X0)) = X0
% 3.42/0.98      | r1_tarski(X0,sK0) != iProver_top
% 3.42/0.98      | v1_funct_1(sK1) != iProver_top
% 3.42/0.98      | v1_relat_1(sK1) != iProver_top ),
% 3.42/0.98      inference(superposition,[status(thm)],[c_2187,c_1293]) ).
% 3.42/0.98  
% 3.42/0.98  cnf(c_101,plain,
% 3.42/0.98      ( v1_relat_1(k2_zfmisc_1(X0,X1)) = iProver_top ),
% 3.42/0.98      inference(predicate_to_equality,[status(thm)],[c_4]) ).
% 3.42/0.98  
% 3.42/0.98  cnf(c_103,plain,
% 3.42/0.98      ( v1_relat_1(k2_zfmisc_1(sK0,sK0)) = iProver_top ),
% 3.42/0.98      inference(instantiation,[status(thm)],[c_101]) ).
% 3.42/0.98  
% 3.42/0.98  cnf(c_1722,plain,
% 3.42/0.98      ( m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) != iProver_top
% 3.42/0.98      | v1_relat_1(k2_zfmisc_1(sK0,sK0)) != iProver_top
% 3.42/0.98      | v1_relat_1(sK1) = iProver_top ),
% 3.42/0.98      inference(predicate_to_equality,[status(thm)],[c_1721]) ).
% 3.42/0.98  
% 3.42/0.98  cnf(c_2994,plain,
% 3.42/0.98      ( k9_relat_1(sK1,k10_relat_1(sK1,X0)) = X0
% 3.42/0.98      | r1_tarski(X0,sK0) != iProver_top ),
% 3.42/0.98      inference(global_propositional_subsumption,
% 3.42/0.98                [status(thm)],
% 3.42/0.98                [c_2751,c_32,c_35,c_103,c_1722]) ).
% 3.42/0.98  
% 3.42/0.98  cnf(c_3002,plain,
% 3.42/0.98      ( k9_relat_1(sK1,k10_relat_1(sK1,sK0)) = sK0 ),
% 3.42/0.98      inference(superposition,[status(thm)],[c_1298,c_2994]) ).
% 3.42/0.98  
% 3.42/0.98  cnf(c_1297,plain,
% 3.42/0.98      ( m1_subset_1(X0,k1_zfmisc_1(X1)) != iProver_top
% 3.42/0.98      | v1_relat_1(X1) != iProver_top
% 3.42/0.98      | v1_relat_1(X0) = iProver_top ),
% 3.42/0.98      inference(predicate_to_equality,[status(thm)],[c_3]) ).
% 3.42/0.98  
% 3.42/0.98  cnf(c_1974,plain,
% 3.42/0.98      ( v1_relat_1(k2_zfmisc_1(sK0,sK0)) != iProver_top
% 3.42/0.98      | v1_relat_1(sK1) = iProver_top ),
% 3.42/0.98      inference(superposition,[status(thm)],[c_1279,c_1297]) ).
% 3.42/0.98  
% 3.42/0.98  cnf(c_1988,plain,
% 3.42/0.98      ( v1_relat_1(sK1) = iProver_top ),
% 3.42/0.98      inference(global_propositional_subsumption,
% 3.42/0.98                [status(thm)],
% 3.42/0.98                [c_1974,c_35,c_103,c_1722]) ).
% 3.42/0.98  
% 3.42/0.98  cnf(c_6,plain,
% 3.42/0.98      ( ~ v1_relat_1(X0)
% 3.42/0.98      | k10_relat_1(X0,k2_relat_1(X0)) = k1_relat_1(X0) ),
% 3.42/0.98      inference(cnf_transformation,[],[f59]) ).
% 3.42/0.98  
% 3.42/0.98  cnf(c_1294,plain,
% 3.42/0.98      ( k10_relat_1(X0,k2_relat_1(X0)) = k1_relat_1(X0)
% 3.42/0.98      | v1_relat_1(X0) != iProver_top ),
% 3.42/0.98      inference(predicate_to_equality,[status(thm)],[c_6]) ).
% 3.42/0.98  
% 3.42/0.98  cnf(c_1994,plain,
% 3.42/0.98      ( k10_relat_1(sK1,k2_relat_1(sK1)) = k1_relat_1(sK1) ),
% 3.42/0.98      inference(superposition,[status(thm)],[c_1988,c_1294]) ).
% 3.42/0.98  
% 3.42/0.98  cnf(c_2190,plain,
% 3.42/0.98      ( k10_relat_1(sK1,sK0) = k1_relat_1(sK1) ),
% 3.42/0.98      inference(light_normalisation,[status(thm)],[c_1994,c_2187]) ).
% 3.42/0.98  
% 3.42/0.98  cnf(c_3003,plain,
% 3.42/0.98      ( k9_relat_1(sK1,k1_relat_1(sK1)) = sK0 ),
% 3.42/0.98      inference(light_normalisation,[status(thm)],[c_3002,c_2190]) ).
% 3.42/0.98  
% 3.42/0.98  cnf(c_26,plain,
% 3.42/0.98      ( ~ v1_funct_2(X0,X1,X1)
% 3.42/0.98      | ~ v3_funct_2(X0,X1,X1)
% 3.42/0.98      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X1)))
% 3.42/0.98      | ~ v1_funct_1(X0)
% 3.42/0.98      | k2_funct_2(X1,X0) = k2_funct_1(X0) ),
% 3.42/0.98      inference(cnf_transformation,[],[f79]) ).
% 3.42/0.98  
% 3.42/0.98  cnf(c_1281,plain,
% 3.42/0.98      ( k2_funct_2(X0,X1) = k2_funct_1(X1)
% 3.42/0.98      | v1_funct_2(X1,X0,X0) != iProver_top
% 3.42/0.98      | v3_funct_2(X1,X0,X0) != iProver_top
% 3.42/0.98      | m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) != iProver_top
% 3.42/0.98      | v1_funct_1(X1) != iProver_top ),
% 3.42/0.98      inference(predicate_to_equality,[status(thm)],[c_26]) ).
% 3.42/0.98  
% 3.42/0.98  cnf(c_3250,plain,
% 3.42/0.98      ( k2_funct_2(sK0,sK1) = k2_funct_1(sK1)
% 3.42/0.98      | v1_funct_2(sK1,sK0,sK0) != iProver_top
% 3.42/0.98      | v3_funct_2(sK1,sK0,sK0) != iProver_top
% 3.42/0.98      | v1_funct_1(sK1) != iProver_top ),
% 3.42/0.98      inference(superposition,[status(thm)],[c_1279,c_1281]) ).
% 3.42/0.98  
% 3.42/0.98  cnf(c_30,negated_conjecture,
% 3.42/0.98      ( v1_funct_2(sK1,sK0,sK0) ),
% 3.42/0.98      inference(cnf_transformation,[],[f82]) ).
% 3.42/0.98  
% 3.42/0.98  cnf(c_1594,plain,
% 3.42/0.98      ( ~ v1_funct_2(sK1,X0,X0)
% 3.42/0.98      | ~ v3_funct_2(sK1,X0,X0)
% 3.42/0.98      | ~ m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
% 3.42/0.98      | ~ v1_funct_1(sK1)
% 3.42/0.98      | k2_funct_2(X0,sK1) = k2_funct_1(sK1) ),
% 3.42/0.98      inference(instantiation,[status(thm)],[c_26]) ).
% 3.42/0.98  
% 3.42/0.98  cnf(c_1596,plain,
% 3.42/0.98      ( ~ v1_funct_2(sK1,sK0,sK0)
% 3.42/0.98      | ~ v3_funct_2(sK1,sK0,sK0)
% 3.42/0.98      | ~ m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
% 3.42/0.98      | ~ v1_funct_1(sK1)
% 3.42/0.98      | k2_funct_2(sK0,sK1) = k2_funct_1(sK1) ),
% 3.42/0.98      inference(instantiation,[status(thm)],[c_1594]) ).
% 3.42/0.98  
% 3.42/0.98  cnf(c_4033,plain,
% 3.42/0.98      ( k2_funct_2(sK0,sK1) = k2_funct_1(sK1) ),
% 3.42/0.98      inference(global_propositional_subsumption,
% 3.42/0.98                [status(thm)],
% 3.42/0.98                [c_3250,c_31,c_30,c_29,c_28,c_1596]) ).
% 3.42/0.98  
% 3.42/0.98  cnf(c_20,plain,
% 3.42/0.98      ( ~ v1_funct_2(X0,X1,X1)
% 3.42/0.98      | ~ v3_funct_2(X0,X1,X1)
% 3.42/0.98      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X1)))
% 3.42/0.98      | m1_subset_1(k2_funct_2(X1,X0),k1_zfmisc_1(k2_zfmisc_1(X1,X1)))
% 3.42/0.98      | ~ v1_funct_1(X0) ),
% 3.42/0.98      inference(cnf_transformation,[],[f76]) ).
% 3.42/0.98  
% 3.42/0.98  cnf(c_1287,plain,
% 3.42/0.98      ( v1_funct_2(X0,X1,X1) != iProver_top
% 3.42/0.98      | v3_funct_2(X0,X1,X1) != iProver_top
% 3.42/0.98      | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X1))) != iProver_top
% 3.42/0.98      | m1_subset_1(k2_funct_2(X1,X0),k1_zfmisc_1(k2_zfmisc_1(X1,X1))) = iProver_top
% 3.42/0.98      | v1_funct_1(X0) != iProver_top ),
% 3.42/0.98      inference(predicate_to_equality,[status(thm)],[c_20]) ).
% 3.42/0.98  
% 3.42/0.98  cnf(c_4376,plain,
% 3.42/0.98      ( v1_funct_2(sK1,sK0,sK0) != iProver_top
% 3.42/0.98      | v3_funct_2(sK1,sK0,sK0) != iProver_top
% 3.42/0.98      | m1_subset_1(k2_funct_1(sK1),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) = iProver_top
% 3.42/0.98      | m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) != iProver_top
% 3.42/0.98      | v1_funct_1(sK1) != iProver_top ),
% 3.42/0.98      inference(superposition,[status(thm)],[c_4033,c_1287]) ).
% 3.42/0.98  
% 3.42/0.98  cnf(c_33,plain,
% 3.42/0.98      ( v1_funct_2(sK1,sK0,sK0) = iProver_top ),
% 3.42/0.98      inference(predicate_to_equality,[status(thm)],[c_30]) ).
% 3.42/0.98  
% 3.42/0.98  cnf(c_5058,plain,
% 3.42/0.98      ( m1_subset_1(k2_funct_1(sK1),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) = iProver_top ),
% 3.42/0.98      inference(global_propositional_subsumption,
% 3.42/0.98                [status(thm)],
% 3.42/0.98                [c_4376,c_32,c_33,c_34,c_35]) ).
% 3.42/0.98  
% 3.42/0.98  cnf(c_13,plain,
% 3.42/0.98      ( v4_relat_1(X0,X1)
% 3.42/0.98      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) ),
% 3.42/0.98      inference(cnf_transformation,[],[f65]) ).
% 3.42/0.98  
% 3.42/0.98  cnf(c_7,plain,
% 3.42/0.98      ( ~ v4_relat_1(X0,X1) | ~ v1_relat_1(X0) | k7_relat_1(X0,X1) = X0 ),
% 3.42/0.98      inference(cnf_transformation,[],[f60]) ).
% 3.42/0.98  
% 3.42/0.98  cnf(c_353,plain,
% 3.42/0.98      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.42/0.98      | ~ v1_relat_1(X0)
% 3.42/0.98      | k7_relat_1(X0,X1) = X0 ),
% 3.42/0.98      inference(resolution,[status(thm)],[c_13,c_7]) ).
% 3.42/0.98  
% 3.42/0.98  cnf(c_1275,plain,
% 3.42/0.98      ( k7_relat_1(X0,X1) = X0
% 3.42/0.98      | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) != iProver_top
% 3.42/0.98      | v1_relat_1(X0) != iProver_top ),
% 3.42/0.98      inference(predicate_to_equality,[status(thm)],[c_353]) ).
% 3.42/0.98  
% 3.42/0.98  cnf(c_5068,plain,
% 3.42/0.98      ( k7_relat_1(k2_funct_1(sK1),sK0) = k2_funct_1(sK1)
% 3.42/0.98      | v1_relat_1(k2_funct_1(sK1)) != iProver_top ),
% 3.42/0.98      inference(superposition,[status(thm)],[c_5058,c_1275]) ).
% 3.42/0.98  
% 3.42/0.98  cnf(c_5063,plain,
% 3.42/0.98      ( v1_relat_1(k2_zfmisc_1(sK0,sK0)) != iProver_top
% 3.42/0.98      | v1_relat_1(k2_funct_1(sK1)) = iProver_top ),
% 3.42/0.98      inference(superposition,[status(thm)],[c_5058,c_1297]) ).
% 3.42/0.98  
% 3.42/0.98  cnf(c_5888,plain,
% 3.42/0.98      ( k7_relat_1(k2_funct_1(sK1),sK0) = k2_funct_1(sK1) ),
% 3.42/0.98      inference(global_propositional_subsumption,
% 3.42/0.98                [status(thm)],
% 3.42/0.98                [c_5068,c_103,c_5063]) ).
% 3.42/0.98  
% 3.42/0.98  cnf(c_5538,plain,
% 3.42/0.98      ( v1_relat_1(k2_funct_1(sK1)) = iProver_top ),
% 3.42/0.98      inference(global_propositional_subsumption,
% 3.42/0.98                [status(thm)],
% 3.42/0.98                [c_5063,c_103]) ).
% 3.42/0.98  
% 3.42/0.98  cnf(c_5,plain,
% 3.42/0.98      ( ~ v1_relat_1(X0)
% 3.42/0.98      | k2_relat_1(k7_relat_1(X0,X1)) = k9_relat_1(X0,X1) ),
% 3.42/0.98      inference(cnf_transformation,[],[f58]) ).
% 3.42/0.98  
% 3.42/0.98  cnf(c_1295,plain,
% 3.42/0.98      ( k2_relat_1(k7_relat_1(X0,X1)) = k9_relat_1(X0,X1)
% 3.42/0.98      | v1_relat_1(X0) != iProver_top ),
% 3.42/0.98      inference(predicate_to_equality,[status(thm)],[c_5]) ).
% 3.42/0.98  
% 3.42/0.98  cnf(c_5543,plain,
% 3.42/0.98      ( k2_relat_1(k7_relat_1(k2_funct_1(sK1),X0)) = k9_relat_1(k2_funct_1(sK1),X0) ),
% 3.42/0.98      inference(superposition,[status(thm)],[c_5538,c_1295]) ).
% 3.42/0.98  
% 3.42/0.98  cnf(c_5891,plain,
% 3.42/0.98      ( k9_relat_1(k2_funct_1(sK1),sK0) = k2_relat_1(k2_funct_1(sK1)) ),
% 3.42/0.98      inference(superposition,[status(thm)],[c_5888,c_5543]) ).
% 3.42/0.98  
% 3.42/0.98  cnf(c_5066,plain,
% 3.42/0.98      ( k2_relat_1(k2_funct_1(sK1)) = sK0
% 3.42/0.98      | v3_funct_2(k2_funct_1(sK1),sK0,sK0) != iProver_top
% 3.42/0.98      | v1_funct_1(k2_funct_1(sK1)) != iProver_top
% 3.42/0.98      | v1_relat_1(k2_funct_1(sK1)) != iProver_top ),
% 3.42/0.98      inference(superposition,[status(thm)],[c_5058,c_1274]) ).
% 3.42/0.98  
% 3.42/0.98  cnf(c_23,plain,
% 3.42/0.98      ( ~ v1_funct_2(X0,X1,X1)
% 3.42/0.98      | ~ v3_funct_2(X0,X1,X1)
% 3.42/0.98      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X1)))
% 3.42/0.98      | ~ v1_funct_1(X0)
% 3.42/0.98      | v1_funct_1(k2_funct_2(X1,X0)) ),
% 3.42/0.98      inference(cnf_transformation,[],[f73]) ).
% 3.42/0.98  
% 3.42/0.98  cnf(c_1284,plain,
% 3.42/0.98      ( v1_funct_2(X0,X1,X1) != iProver_top
% 3.42/0.98      | v3_funct_2(X0,X1,X1) != iProver_top
% 3.42/0.98      | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X1))) != iProver_top
% 3.42/0.98      | v1_funct_1(X0) != iProver_top
% 3.42/0.98      | v1_funct_1(k2_funct_2(X1,X0)) = iProver_top ),
% 3.42/0.98      inference(predicate_to_equality,[status(thm)],[c_23]) ).
% 3.42/0.98  
% 3.42/0.98  cnf(c_3867,plain,
% 3.42/0.98      ( v1_funct_2(sK1,sK0,sK0) != iProver_top
% 3.42/0.98      | v3_funct_2(sK1,sK0,sK0) != iProver_top
% 3.42/0.98      | v1_funct_1(k2_funct_2(sK0,sK1)) = iProver_top
% 3.42/0.98      | v1_funct_1(sK1) != iProver_top ),
% 3.42/0.98      inference(superposition,[status(thm)],[c_1279,c_1284]) ).
% 3.42/0.98  
% 3.42/0.98  cnf(c_1579,plain,
% 3.42/0.98      ( ~ v1_funct_2(sK1,X0,X0)
% 3.42/0.98      | ~ v3_funct_2(sK1,X0,X0)
% 3.42/0.98      | ~ m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
% 3.42/0.98      | v1_funct_1(k2_funct_2(X0,sK1))
% 3.42/0.98      | ~ v1_funct_1(sK1) ),
% 3.42/0.98      inference(instantiation,[status(thm)],[c_23]) ).
% 3.42/0.98  
% 3.42/0.98  cnf(c_1580,plain,
% 3.42/0.98      ( v1_funct_2(sK1,X0,X0) != iProver_top
% 3.42/0.98      | v3_funct_2(sK1,X0,X0) != iProver_top
% 3.42/0.98      | m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) != iProver_top
% 3.42/0.98      | v1_funct_1(k2_funct_2(X0,sK1)) = iProver_top
% 3.42/0.98      | v1_funct_1(sK1) != iProver_top ),
% 3.42/0.98      inference(predicate_to_equality,[status(thm)],[c_1579]) ).
% 3.42/0.99  
% 3.42/0.99  cnf(c_1582,plain,
% 3.42/0.99      ( v1_funct_2(sK1,sK0,sK0) != iProver_top
% 3.42/0.99      | v3_funct_2(sK1,sK0,sK0) != iProver_top
% 3.42/0.99      | m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) != iProver_top
% 3.42/0.99      | v1_funct_1(k2_funct_2(sK0,sK1)) = iProver_top
% 3.42/0.99      | v1_funct_1(sK1) != iProver_top ),
% 3.42/0.99      inference(instantiation,[status(thm)],[c_1580]) ).
% 3.42/0.99  
% 3.42/0.99  cnf(c_4127,plain,
% 3.42/0.99      ( v1_funct_1(k2_funct_2(sK0,sK1)) = iProver_top ),
% 3.42/0.99      inference(global_propositional_subsumption,
% 3.42/0.99                [status(thm)],
% 3.42/0.99                [c_3867,c_32,c_33,c_34,c_35,c_1582]) ).
% 3.42/0.99  
% 3.42/0.99  cnf(c_4131,plain,
% 3.42/0.99      ( v1_funct_1(k2_funct_1(sK1)) = iProver_top ),
% 3.42/0.99      inference(light_normalisation,[status(thm)],[c_4127,c_4033]) ).
% 3.42/0.99  
% 3.42/0.99  cnf(c_21,plain,
% 3.42/0.99      ( ~ v1_funct_2(X0,X1,X1)
% 3.42/0.99      | ~ v3_funct_2(X0,X1,X1)
% 3.42/0.99      | v3_funct_2(k2_funct_2(X1,X0),X1,X1)
% 3.42/0.99      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X1)))
% 3.42/0.99      | ~ v1_funct_1(X0) ),
% 3.42/0.99      inference(cnf_transformation,[],[f75]) ).
% 3.42/0.99  
% 3.42/0.99  cnf(c_1286,plain,
% 3.42/0.99      ( v1_funct_2(X0,X1,X1) != iProver_top
% 3.42/0.99      | v3_funct_2(X0,X1,X1) != iProver_top
% 3.42/0.99      | v3_funct_2(k2_funct_2(X1,X0),X1,X1) = iProver_top
% 3.42/0.99      | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X1))) != iProver_top
% 3.42/0.99      | v1_funct_1(X0) != iProver_top ),
% 3.42/0.99      inference(predicate_to_equality,[status(thm)],[c_21]) ).
% 3.42/0.99  
% 3.42/0.99  cnf(c_4348,plain,
% 3.42/0.99      ( v1_funct_2(sK1,sK0,sK0) != iProver_top
% 3.42/0.99      | v3_funct_2(k2_funct_2(sK0,sK1),sK0,sK0) = iProver_top
% 3.42/0.99      | v3_funct_2(sK1,sK0,sK0) != iProver_top
% 3.42/0.99      | v1_funct_1(sK1) != iProver_top ),
% 3.42/0.99      inference(superposition,[status(thm)],[c_1279,c_1286]) ).
% 3.42/0.99  
% 3.42/0.99  cnf(c_4353,plain,
% 3.42/0.99      ( v1_funct_2(sK1,sK0,sK0) != iProver_top
% 3.42/0.99      | v3_funct_2(k2_funct_1(sK1),sK0,sK0) = iProver_top
% 3.42/0.99      | v3_funct_2(sK1,sK0,sK0) != iProver_top
% 3.42/0.99      | v1_funct_1(sK1) != iProver_top ),
% 3.42/0.99      inference(light_normalisation,[status(thm)],[c_4348,c_4033]) ).
% 3.42/0.99  
% 3.42/0.99  cnf(c_5998,plain,
% 3.42/0.99      ( k2_relat_1(k2_funct_1(sK1)) = sK0 ),
% 3.42/0.99      inference(global_propositional_subsumption,
% 3.42/0.99                [status(thm)],
% 3.42/0.99                [c_5066,c_32,c_33,c_34,c_103,c_4131,c_4353,c_5063]) ).
% 3.42/0.99  
% 3.42/0.99  cnf(c_7188,plain,
% 3.42/0.99      ( k9_relat_1(k2_funct_1(sK1),sK0) = sK0 ),
% 3.42/0.99      inference(light_normalisation,[status(thm)],[c_5891,c_5998]) ).
% 3.42/0.99  
% 3.42/0.99  cnf(c_7344,plain,
% 3.42/0.99      ( k1_relat_1(sK1) = sK0
% 3.42/0.99      | v1_funct_1(sK1) != iProver_top
% 3.42/0.99      | v1_relat_1(sK1) != iProver_top ),
% 3.42/0.99      inference(light_normalisation,[status(thm)],[c_7333,c_3003,c_7188]) ).
% 3.42/0.99  
% 3.42/0.99  cnf(c_7509,plain,
% 3.42/0.99      ( k1_relat_1(sK1) = sK0 ),
% 3.42/0.99      inference(global_propositional_subsumption,
% 3.42/0.99                [status(thm)],
% 3.42/0.99                [c_7344,c_32,c_35,c_103,c_1722]) ).
% 3.42/0.99  
% 3.42/0.99  cnf(c_25,plain,
% 3.42/0.99      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.42/0.99      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X4,X5)))
% 3.42/0.99      | ~ v1_funct_1(X0)
% 3.42/0.99      | ~ v1_funct_1(X3)
% 3.42/0.99      | k1_partfun1(X4,X5,X1,X2,X3,X0) = k5_relat_1(X3,X0) ),
% 3.42/0.99      inference(cnf_transformation,[],[f78]) ).
% 3.42/0.99  
% 3.42/0.99  cnf(c_1282,plain,
% 3.42/0.99      ( k1_partfun1(X0,X1,X2,X3,X4,X5) = k5_relat_1(X4,X5)
% 3.42/0.99      | m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) != iProver_top
% 3.42/0.99      | m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top
% 3.42/0.99      | v1_funct_1(X5) != iProver_top
% 3.42/0.99      | v1_funct_1(X4) != iProver_top ),
% 3.42/0.99      inference(predicate_to_equality,[status(thm)],[c_25]) ).
% 3.42/0.99  
% 3.42/0.99  cnf(c_5073,plain,
% 3.42/0.99      ( k1_partfun1(X0,X1,sK0,sK0,X2,k2_funct_1(sK1)) = k5_relat_1(X2,k2_funct_1(sK1))
% 3.42/0.99      | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top
% 3.42/0.99      | v1_funct_1(X2) != iProver_top
% 3.42/0.99      | v1_funct_1(k2_funct_1(sK1)) != iProver_top ),
% 3.42/0.99      inference(superposition,[status(thm)],[c_5058,c_1282]) ).
% 3.42/0.99  
% 3.42/0.99  cnf(c_6823,plain,
% 3.42/0.99      ( v1_funct_1(X2) != iProver_top
% 3.42/0.99      | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top
% 3.42/0.99      | k1_partfun1(X0,X1,sK0,sK0,X2,k2_funct_1(sK1)) = k5_relat_1(X2,k2_funct_1(sK1)) ),
% 3.42/0.99      inference(global_propositional_subsumption,
% 3.42/0.99                [status(thm)],
% 3.42/0.99                [c_5073,c_4131]) ).
% 3.42/0.99  
% 3.42/0.99  cnf(c_6824,plain,
% 3.42/0.99      ( k1_partfun1(X0,X1,sK0,sK0,X2,k2_funct_1(sK1)) = k5_relat_1(X2,k2_funct_1(sK1))
% 3.42/0.99      | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top
% 3.42/0.99      | v1_funct_1(X2) != iProver_top ),
% 3.42/0.99      inference(renaming,[status(thm)],[c_6823]) ).
% 3.42/0.99  
% 3.42/0.99  cnf(c_6834,plain,
% 3.42/0.99      ( k1_partfun1(sK0,sK0,sK0,sK0,sK1,k2_funct_1(sK1)) = k5_relat_1(sK1,k2_funct_1(sK1))
% 3.42/0.99      | v1_funct_1(sK1) != iProver_top ),
% 3.42/0.99      inference(superposition,[status(thm)],[c_1279,c_6824]) ).
% 3.42/0.99  
% 3.42/0.99  cnf(c_11,plain,
% 3.42/0.99      ( ~ v2_funct_1(X0)
% 3.42/0.99      | ~ v1_funct_1(X0)
% 3.42/0.99      | ~ v1_relat_1(X0)
% 3.42/0.99      | k5_relat_1(X0,k2_funct_1(X0)) = k6_partfun1(k1_relat_1(X0)) ),
% 3.42/0.99      inference(cnf_transformation,[],[f87]) ).
% 3.42/0.99  
% 3.42/0.99  cnf(c_1290,plain,
% 3.42/0.99      ( k5_relat_1(X0,k2_funct_1(X0)) = k6_partfun1(k1_relat_1(X0))
% 3.42/0.99      | v2_funct_1(X0) != iProver_top
% 3.42/0.99      | v1_funct_1(X0) != iProver_top
% 3.42/0.99      | v1_relat_1(X0) != iProver_top ),
% 3.42/0.99      inference(predicate_to_equality,[status(thm)],[c_11]) ).
% 3.42/0.99  
% 3.42/0.99  cnf(c_4016,plain,
% 3.42/0.99      ( k5_relat_1(sK1,k2_funct_1(sK1)) = k6_partfun1(k1_relat_1(sK1))
% 3.42/0.99      | v1_funct_1(sK1) != iProver_top
% 3.42/0.99      | v1_relat_1(sK1) != iProver_top ),
% 3.42/0.99      inference(superposition,[status(thm)],[c_4010,c_1290]) ).
% 3.42/0.99  
% 3.42/0.99  cnf(c_1547,plain,
% 3.42/0.99      ( ~ v3_funct_2(sK1,sK0,sK0)
% 3.42/0.99      | ~ m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
% 3.42/0.99      | v2_funct_1(sK1)
% 3.42/0.99      | ~ v1_funct_1(sK1) ),
% 3.42/0.99      inference(instantiation,[status(thm)],[c_1545]) ).
% 3.42/0.99  
% 3.42/0.99  cnf(c_1656,plain,
% 3.42/0.99      ( ~ v2_funct_1(sK1)
% 3.42/0.99      | ~ v1_funct_1(sK1)
% 3.42/0.99      | ~ v1_relat_1(sK1)
% 3.42/0.99      | k5_relat_1(sK1,k2_funct_1(sK1)) = k6_partfun1(k1_relat_1(sK1)) ),
% 3.42/0.99      inference(instantiation,[status(thm)],[c_11]) ).
% 3.42/0.99  
% 3.42/0.99  cnf(c_4290,plain,
% 3.42/0.99      ( k5_relat_1(sK1,k2_funct_1(sK1)) = k6_partfun1(k1_relat_1(sK1)) ),
% 3.42/0.99      inference(global_propositional_subsumption,
% 3.42/0.99                [status(thm)],
% 3.42/0.99                [c_4016,c_31,c_29,c_28,c_102,c_1547,c_1656,c_1721]) ).
% 3.42/0.99  
% 3.42/0.99  cnf(c_6842,plain,
% 3.42/0.99      ( k1_partfun1(sK0,sK0,sK0,sK0,sK1,k2_funct_1(sK1)) = k6_partfun1(k1_relat_1(sK1))
% 3.42/0.99      | v1_funct_1(sK1) != iProver_top ),
% 3.42/0.99      inference(light_normalisation,[status(thm)],[c_6834,c_4290]) ).
% 3.42/0.99  
% 3.42/0.99  cnf(c_6967,plain,
% 3.42/0.99      ( k1_partfun1(sK0,sK0,sK0,sK0,sK1,k2_funct_1(sK1)) = k6_partfun1(k1_relat_1(sK1)) ),
% 3.42/0.99      inference(global_propositional_subsumption,
% 3.42/0.99                [status(thm)],
% 3.42/0.99                [c_6842,c_32]) ).
% 3.42/0.99  
% 3.42/0.99  cnf(c_4643,plain,
% 3.42/0.99      ( k1_partfun1(X0,X1,sK0,sK0,X2,sK1) = k5_relat_1(X2,sK1)
% 3.42/0.99      | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top
% 3.42/0.99      | v1_funct_1(X2) != iProver_top
% 3.42/0.99      | v1_funct_1(sK1) != iProver_top ),
% 3.42/0.99      inference(superposition,[status(thm)],[c_1279,c_1282]) ).
% 3.42/0.99  
% 3.42/0.99  cnf(c_4774,plain,
% 3.42/0.99      ( v1_funct_1(X2) != iProver_top
% 3.42/0.99      | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top
% 3.42/0.99      | k1_partfun1(X0,X1,sK0,sK0,X2,sK1) = k5_relat_1(X2,sK1) ),
% 3.42/0.99      inference(global_propositional_subsumption,
% 3.42/0.99                [status(thm)],
% 3.42/0.99                [c_4643,c_32]) ).
% 3.42/0.99  
% 3.42/0.99  cnf(c_4775,plain,
% 3.42/0.99      ( k1_partfun1(X0,X1,sK0,sK0,X2,sK1) = k5_relat_1(X2,sK1)
% 3.42/0.99      | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top
% 3.42/0.99      | v1_funct_1(X2) != iProver_top ),
% 3.42/0.99      inference(renaming,[status(thm)],[c_4774]) ).
% 3.42/0.99  
% 3.42/0.99  cnf(c_4783,plain,
% 3.42/0.99      ( k1_partfun1(X0,X0,sK0,sK0,k2_funct_2(X0,X1),sK1) = k5_relat_1(k2_funct_2(X0,X1),sK1)
% 3.42/0.99      | v1_funct_2(X1,X0,X0) != iProver_top
% 3.42/0.99      | v3_funct_2(X1,X0,X0) != iProver_top
% 3.42/0.99      | m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) != iProver_top
% 3.42/0.99      | v1_funct_1(X1) != iProver_top
% 3.42/0.99      | v1_funct_1(k2_funct_2(X0,X1)) != iProver_top ),
% 3.42/0.99      inference(superposition,[status(thm)],[c_1287,c_4775]) ).
% 3.42/0.99  
% 3.42/0.99  cnf(c_5275,plain,
% 3.42/0.99      ( k1_partfun1(X0,X0,sK0,sK0,k2_funct_2(X0,X1),sK1) = k5_relat_1(k2_funct_2(X0,X1),sK1)
% 3.42/0.99      | v1_funct_2(X1,X0,X0) != iProver_top
% 3.42/0.99      | v3_funct_2(X1,X0,X0) != iProver_top
% 3.42/0.99      | m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) != iProver_top
% 3.42/0.99      | v1_funct_1(X1) != iProver_top ),
% 3.42/0.99      inference(forward_subsumption_resolution,
% 3.42/0.99                [status(thm)],
% 3.42/0.99                [c_4783,c_1284]) ).
% 3.42/0.99  
% 3.42/0.99  cnf(c_5281,plain,
% 3.42/0.99      ( k1_partfun1(sK0,sK0,sK0,sK0,k2_funct_2(sK0,sK1),sK1) = k5_relat_1(k2_funct_2(sK0,sK1),sK1)
% 3.42/0.99      | v1_funct_2(sK1,sK0,sK0) != iProver_top
% 3.42/0.99      | v3_funct_2(sK1,sK0,sK0) != iProver_top
% 3.42/0.99      | v1_funct_1(sK1) != iProver_top ),
% 3.42/0.99      inference(superposition,[status(thm)],[c_1279,c_5275]) ).
% 3.42/0.99  
% 3.42/0.99  cnf(c_10,plain,
% 3.42/0.99      ( ~ v2_funct_1(X0)
% 3.42/0.99      | ~ v1_funct_1(X0)
% 3.42/0.99      | ~ v1_relat_1(X0)
% 3.42/0.99      | k5_relat_1(k2_funct_1(X0),X0) = k6_partfun1(k2_relat_1(X0)) ),
% 3.42/0.99      inference(cnf_transformation,[],[f86]) ).
% 3.42/0.99  
% 3.42/0.99  cnf(c_1291,plain,
% 3.42/0.99      ( k5_relat_1(k2_funct_1(X0),X0) = k6_partfun1(k2_relat_1(X0))
% 3.42/0.99      | v2_funct_1(X0) != iProver_top
% 3.42/0.99      | v1_funct_1(X0) != iProver_top
% 3.42/0.99      | v1_relat_1(X0) != iProver_top ),
% 3.42/0.99      inference(predicate_to_equality,[status(thm)],[c_10]) ).
% 3.42/0.99  
% 3.42/0.99  cnf(c_4015,plain,
% 3.42/0.99      ( k5_relat_1(k2_funct_1(sK1),sK1) = k6_partfun1(k2_relat_1(sK1))
% 3.42/0.99      | v1_funct_1(sK1) != iProver_top
% 3.42/0.99      | v1_relat_1(sK1) != iProver_top ),
% 3.42/0.99      inference(superposition,[status(thm)],[c_4010,c_1291]) ).
% 3.42/0.99  
% 3.42/0.99  cnf(c_4026,plain,
% 3.42/0.99      ( k5_relat_1(k2_funct_1(sK1),sK1) = k6_partfun1(sK0)
% 3.42/0.99      | v1_funct_1(sK1) != iProver_top
% 3.42/0.99      | v1_relat_1(sK1) != iProver_top ),
% 3.42/0.99      inference(light_normalisation,[status(thm)],[c_4015,c_2187]) ).
% 3.42/0.99  
% 3.42/0.99  cnf(c_4213,plain,
% 3.42/0.99      ( k5_relat_1(k2_funct_1(sK1),sK1) = k6_partfun1(sK0) ),
% 3.42/0.99      inference(global_propositional_subsumption,
% 3.42/0.99                [status(thm)],
% 3.42/0.99                [c_4026,c_32,c_35,c_103,c_1722]) ).
% 3.42/0.99  
% 3.42/0.99  cnf(c_5295,plain,
% 3.42/0.99      ( k1_partfun1(sK0,sK0,sK0,sK0,k2_funct_1(sK1),sK1) = k6_partfun1(sK0)
% 3.42/0.99      | v1_funct_2(sK1,sK0,sK0) != iProver_top
% 3.42/0.99      | v3_funct_2(sK1,sK0,sK0) != iProver_top
% 3.42/0.99      | v1_funct_1(sK1) != iProver_top ),
% 3.42/0.99      inference(light_normalisation,[status(thm)],[c_5281,c_4033,c_4213]) ).
% 3.42/0.99  
% 3.42/0.99  cnf(c_5064,plain,
% 3.42/0.99      ( k1_partfun1(sK0,sK0,sK0,sK0,k2_funct_1(sK1),sK1) = k5_relat_1(k2_funct_1(sK1),sK1)
% 3.42/0.99      | v1_funct_1(k2_funct_1(sK1)) != iProver_top ),
% 3.42/0.99      inference(superposition,[status(thm)],[c_5058,c_4775]) ).
% 3.42/0.99  
% 3.42/0.99  cnf(c_5138,plain,
% 3.42/0.99      ( k1_partfun1(sK0,sK0,sK0,sK0,k2_funct_1(sK1),sK1) = k6_partfun1(sK0)
% 3.42/0.99      | v1_funct_1(k2_funct_1(sK1)) != iProver_top ),
% 3.42/0.99      inference(light_normalisation,[status(thm)],[c_5064,c_4213]) ).
% 3.42/0.99  
% 3.42/0.99  cnf(c_5333,plain,
% 3.42/0.99      ( k1_partfun1(sK0,sK0,sK0,sK0,k2_funct_1(sK1),sK1) = k6_partfun1(sK0) ),
% 3.42/0.99      inference(global_propositional_subsumption,
% 3.42/0.99                [status(thm)],
% 3.42/0.99                [c_5295,c_4131,c_5138]) ).
% 3.42/0.99  
% 3.42/0.99  cnf(c_27,negated_conjecture,
% 3.42/0.99      ( ~ r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK0,sK0,sK0,k2_funct_2(sK0,sK1),sK1),k6_partfun1(sK0))
% 3.42/0.99      | ~ r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK0,sK0,sK0,sK1,k2_funct_2(sK0,sK1)),k6_partfun1(sK0)) ),
% 3.42/0.99      inference(cnf_transformation,[],[f85]) ).
% 3.42/0.99  
% 3.42/0.99  cnf(c_1280,plain,
% 3.42/0.99      ( r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK0,sK0,sK0,k2_funct_2(sK0,sK1),sK1),k6_partfun1(sK0)) != iProver_top
% 3.42/0.99      | r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK0,sK0,sK0,sK1,k2_funct_2(sK0,sK1)),k6_partfun1(sK0)) != iProver_top ),
% 3.42/0.99      inference(predicate_to_equality,[status(thm)],[c_27]) ).
% 3.42/0.99  
% 3.42/0.99  cnf(c_4036,plain,
% 3.42/0.99      ( r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK0,sK0,sK0,k2_funct_1(sK1),sK1),k6_partfun1(sK0)) != iProver_top
% 3.42/0.99      | r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK0,sK0,sK0,sK1,k2_funct_1(sK1)),k6_partfun1(sK0)) != iProver_top ),
% 3.42/0.99      inference(demodulation,[status(thm)],[c_4033,c_1280]) ).
% 3.42/0.99  
% 3.42/0.99  cnf(c_5336,plain,
% 3.42/0.99      ( r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK0,sK0,sK0,sK1,k2_funct_1(sK1)),k6_partfun1(sK0)) != iProver_top
% 3.42/0.99      | r2_relset_1(sK0,sK0,k6_partfun1(sK0),k6_partfun1(sK0)) != iProver_top ),
% 3.42/0.99      inference(demodulation,[status(thm)],[c_5333,c_4036]) ).
% 3.42/0.99  
% 3.42/0.99  cnf(c_24,plain,
% 3.42/0.99      ( m1_subset_1(k6_partfun1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0))) ),
% 3.42/0.99      inference(cnf_transformation,[],[f77]) ).
% 3.42/0.99  
% 3.42/0.99  cnf(c_43,plain,
% 3.42/0.99      ( m1_subset_1(k6_partfun1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0))) = iProver_top ),
% 3.42/0.99      inference(predicate_to_equality,[status(thm)],[c_24]) ).
% 3.42/0.99  
% 3.42/0.99  cnf(c_45,plain,
% 3.42/0.99      ( m1_subset_1(k6_partfun1(sK0),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) = iProver_top ),
% 3.42/0.99      inference(instantiation,[status(thm)],[c_43]) ).
% 3.42/0.99  
% 3.42/0.99  cnf(c_14,plain,
% 3.42/0.99      ( r2_relset_1(X0,X1,X2,X2)
% 3.42/0.99      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
% 3.42/0.99      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ),
% 3.42/0.99      inference(cnf_transformation,[],[f67]) ).
% 3.42/0.99  
% 3.42/0.99  cnf(c_1564,plain,
% 3.42/0.99      ( r2_relset_1(X0,X0,k6_partfun1(X0),k6_partfun1(X0))
% 3.42/0.99      | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
% 3.42/0.99      | ~ m1_subset_1(k6_partfun1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0))) ),
% 3.42/0.99      inference(instantiation,[status(thm)],[c_14]) ).
% 3.42/0.99  
% 3.42/0.99  cnf(c_2486,plain,
% 3.42/0.99      ( r2_relset_1(X0,X0,k6_partfun1(X0),k6_partfun1(X0))
% 3.42/0.99      | ~ m1_subset_1(k6_partfun1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0))) ),
% 3.42/0.99      inference(instantiation,[status(thm)],[c_1564]) ).
% 3.42/0.99  
% 3.42/0.99  cnf(c_2487,plain,
% 3.42/0.99      ( r2_relset_1(X0,X0,k6_partfun1(X0),k6_partfun1(X0)) = iProver_top
% 3.42/0.99      | m1_subset_1(k6_partfun1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0))) != iProver_top ),
% 3.42/0.99      inference(predicate_to_equality,[status(thm)],[c_2486]) ).
% 3.42/0.99  
% 3.42/0.99  cnf(c_2489,plain,
% 3.42/0.99      ( r2_relset_1(sK0,sK0,k6_partfun1(sK0),k6_partfun1(sK0)) = iProver_top
% 3.42/0.99      | m1_subset_1(k6_partfun1(sK0),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) != iProver_top ),
% 3.42/0.99      inference(instantiation,[status(thm)],[c_2487]) ).
% 3.42/0.99  
% 3.42/0.99  cnf(c_5454,plain,
% 3.42/0.99      ( r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK0,sK0,sK0,sK1,k2_funct_1(sK1)),k6_partfun1(sK0)) != iProver_top ),
% 3.42/0.99      inference(global_propositional_subsumption,
% 3.42/0.99                [status(thm)],
% 3.42/0.99                [c_5336,c_45,c_2489]) ).
% 3.42/0.99  
% 3.42/0.99  cnf(c_6970,plain,
% 3.42/0.99      ( r2_relset_1(sK0,sK0,k6_partfun1(k1_relat_1(sK1)),k6_partfun1(sK0)) != iProver_top ),
% 3.42/0.99      inference(demodulation,[status(thm)],[c_6967,c_5454]) ).
% 3.42/0.99  
% 3.42/0.99  cnf(c_7512,plain,
% 3.42/0.99      ( r2_relset_1(sK0,sK0,k6_partfun1(sK0),k6_partfun1(sK0)) != iProver_top ),
% 3.42/0.99      inference(demodulation,[status(thm)],[c_7509,c_6970]) ).
% 3.42/0.99  
% 3.42/0.99  cnf(contradiction,plain,
% 3.42/0.99      ( $false ),
% 3.42/0.99      inference(minisat,[status(thm)],[c_7512,c_2489,c_45]) ).
% 3.42/0.99  
% 3.42/0.99  
% 3.42/0.99  % SZS output end CNFRefutation for theBenchmark.p
% 3.42/0.99  
% 3.42/0.99  ------                               Statistics
% 3.42/0.99  
% 3.42/0.99  ------ General
% 3.42/0.99  
% 3.42/0.99  abstr_ref_over_cycles:                  0
% 3.42/0.99  abstr_ref_under_cycles:                 0
% 3.42/0.99  gc_basic_clause_elim:                   0
% 3.42/0.99  forced_gc_time:                         0
% 3.42/0.99  parsing_time:                           0.01
% 3.42/0.99  unif_index_cands_time:                  0.
% 3.42/0.99  unif_index_add_time:                    0.
% 3.42/0.99  orderings_time:                         0.
% 3.42/0.99  out_proof_time:                         0.017
% 3.42/0.99  total_time:                             0.27
% 3.42/0.99  num_of_symbols:                         56
% 3.42/0.99  num_of_terms:                           11063
% 3.42/0.99  
% 3.42/0.99  ------ Preprocessing
% 3.42/0.99  
% 3.42/0.99  num_of_splits:                          0
% 3.42/0.99  num_of_split_atoms:                     0
% 3.42/0.99  num_of_reused_defs:                     0
% 3.42/0.99  num_eq_ax_congr_red:                    25
% 3.42/0.99  num_of_sem_filtered_clauses:            1
% 3.42/0.99  num_of_subtypes:                        0
% 3.42/0.99  monotx_restored_types:                  0
% 3.42/0.99  sat_num_of_epr_types:                   0
% 3.42/0.99  sat_num_of_non_cyclic_types:            0
% 3.42/0.99  sat_guarded_non_collapsed_types:        0
% 3.42/0.99  num_pure_diseq_elim:                    0
% 3.42/0.99  simp_replaced_by:                       0
% 3.42/0.99  res_preprocessed:                       145
% 3.42/0.99  prep_upred:                             0
% 3.42/0.99  prep_unflattend:                        8
% 3.42/0.99  smt_new_axioms:                         0
% 3.42/0.99  pred_elim_cands:                        8
% 3.42/0.99  pred_elim:                              3
% 3.42/0.99  pred_elim_cl:                           4
% 3.42/0.99  pred_elim_cycles:                       6
% 3.42/0.99  merged_defs:                            0
% 3.42/0.99  merged_defs_ncl:                        0
% 3.42/0.99  bin_hyper_res:                          0
% 3.42/0.99  prep_cycles:                            4
% 3.42/0.99  pred_elim_time:                         0.005
% 3.42/0.99  splitting_time:                         0.
% 3.42/0.99  sem_filter_time:                        0.
% 3.42/0.99  monotx_time:                            0.001
% 3.42/0.99  subtype_inf_time:                       0.
% 3.42/0.99  
% 3.42/0.99  ------ Problem properties
% 3.42/0.99  
% 3.42/0.99  clauses:                                26
% 3.42/0.99  conjectures:                            5
% 3.42/0.99  epr:                                    5
% 3.42/0.99  horn:                                   26
% 3.42/0.99  ground:                                 5
% 3.42/0.99  unary:                                  7
% 3.42/0.99  binary:                                 3
% 3.42/0.99  lits:                                   81
% 3.42/0.99  lits_eq:                                11
% 3.42/0.99  fd_pure:                                0
% 3.42/0.99  fd_pseudo:                              0
% 3.42/0.99  fd_cond:                                0
% 3.42/0.99  fd_pseudo_cond:                         2
% 3.42/0.99  ac_symbols:                             0
% 3.42/0.99  
% 3.42/0.99  ------ Propositional Solver
% 3.42/0.99  
% 3.42/0.99  prop_solver_calls:                      28
% 3.42/0.99  prop_fast_solver_calls:                 1270
% 3.42/0.99  smt_solver_calls:                       0
% 3.42/0.99  smt_fast_solver_calls:                  0
% 3.42/0.99  prop_num_of_clauses:                    2986
% 3.42/0.99  prop_preprocess_simplified:             8303
% 3.42/0.99  prop_fo_subsumed:                       72
% 3.42/0.99  prop_solver_time:                       0.
% 3.42/0.99  smt_solver_time:                        0.
% 3.42/0.99  smt_fast_solver_time:                   0.
% 3.42/0.99  prop_fast_solver_time:                  0.
% 3.42/0.99  prop_unsat_core_time:                   0.
% 3.42/0.99  
% 3.42/0.99  ------ QBF
% 3.42/0.99  
% 3.42/0.99  qbf_q_res:                              0
% 3.42/0.99  qbf_num_tautologies:                    0
% 3.42/0.99  qbf_prep_cycles:                        0
% 3.42/0.99  
% 3.42/0.99  ------ BMC1
% 3.42/0.99  
% 3.42/0.99  bmc1_current_bound:                     -1
% 3.42/0.99  bmc1_last_solved_bound:                 -1
% 3.42/0.99  bmc1_unsat_core_size:                   -1
% 3.42/0.99  bmc1_unsat_core_parents_size:           -1
% 3.42/0.99  bmc1_merge_next_fun:                    0
% 3.42/0.99  bmc1_unsat_core_clauses_time:           0.
% 3.42/0.99  
% 3.42/0.99  ------ Instantiation
% 3.42/0.99  
% 3.42/0.99  inst_num_of_clauses:                    810
% 3.42/0.99  inst_num_in_passive:                    308
% 3.42/0.99  inst_num_in_active:                     441
% 3.42/0.99  inst_num_in_unprocessed:                61
% 3.42/0.99  inst_num_of_loops:                      450
% 3.42/0.99  inst_num_of_learning_restarts:          0
% 3.42/0.99  inst_num_moves_active_passive:          7
% 3.42/0.99  inst_lit_activity:                      0
% 3.42/0.99  inst_lit_activity_moves:                0
% 3.42/0.99  inst_num_tautologies:                   0
% 3.42/0.99  inst_num_prop_implied:                  0
% 3.42/0.99  inst_num_existing_simplified:           0
% 3.42/0.99  inst_num_eq_res_simplified:             0
% 3.42/0.99  inst_num_child_elim:                    0
% 3.42/0.99  inst_num_of_dismatching_blockings:      367
% 3.42/0.99  inst_num_of_non_proper_insts:           831
% 3.42/0.99  inst_num_of_duplicates:                 0
% 3.42/0.99  inst_inst_num_from_inst_to_res:         0
% 3.42/0.99  inst_dismatching_checking_time:         0.
% 3.42/0.99  
% 3.42/0.99  ------ Resolution
% 3.42/0.99  
% 3.42/0.99  res_num_of_clauses:                     0
% 3.42/0.99  res_num_in_passive:                     0
% 3.42/0.99  res_num_in_active:                      0
% 3.42/0.99  res_num_of_loops:                       149
% 3.42/0.99  res_forward_subset_subsumed:            34
% 3.42/0.99  res_backward_subset_subsumed:           2
% 3.42/0.99  res_forward_subsumed:                   0
% 3.42/0.99  res_backward_subsumed:                  0
% 3.42/0.99  res_forward_subsumption_resolution:     1
% 3.42/0.99  res_backward_subsumption_resolution:    0
% 3.42/0.99  res_clause_to_clause_subsumption:       185
% 3.42/0.99  res_orphan_elimination:                 0
% 3.42/0.99  res_tautology_del:                      72
% 3.42/0.99  res_num_eq_res_simplified:              0
% 3.42/0.99  res_num_sel_changes:                    0
% 3.42/0.99  res_moves_from_active_to_pass:          0
% 3.42/0.99  
% 3.42/0.99  ------ Superposition
% 3.42/0.99  
% 3.42/0.99  sup_time_total:                         0.
% 3.42/0.99  sup_time_generating:                    0.
% 3.42/0.99  sup_time_sim_full:                      0.
% 3.42/0.99  sup_time_sim_immed:                     0.
% 3.42/0.99  
% 3.42/0.99  sup_num_of_clauses:                     106
% 3.42/0.99  sup_num_in_active:                      77
% 3.42/0.99  sup_num_in_passive:                     29
% 3.42/0.99  sup_num_of_loops:                       89
% 3.42/0.99  sup_fw_superposition:                   56
% 3.42/0.99  sup_bw_superposition:                   38
% 3.42/0.99  sup_immediate_simplified:               14
% 3.42/0.99  sup_given_eliminated:                   0
% 3.42/0.99  comparisons_done:                       0
% 3.42/0.99  comparisons_avoided:                    0
% 3.42/0.99  
% 3.42/0.99  ------ Simplifications
% 3.42/0.99  
% 3.42/0.99  
% 3.42/0.99  sim_fw_subset_subsumed:                 1
% 3.42/0.99  sim_bw_subset_subsumed:                 4
% 3.42/0.99  sim_fw_subsumed:                        0
% 3.42/0.99  sim_bw_subsumed:                        0
% 3.42/0.99  sim_fw_subsumption_res:                 2
% 3.42/0.99  sim_bw_subsumption_res:                 0
% 3.42/0.99  sim_tautology_del:                      0
% 3.42/0.99  sim_eq_tautology_del:                   3
% 3.42/0.99  sim_eq_res_simp:                        0
% 3.42/0.99  sim_fw_demodulated:                     0
% 3.42/0.99  sim_bw_demodulated:                     11
% 3.42/0.99  sim_light_normalised:                   20
% 3.42/0.99  sim_joinable_taut:                      0
% 3.42/0.99  sim_joinable_simp:                      0
% 3.42/0.99  sim_ac_normalised:                      0
% 3.42/0.99  sim_smt_subsumption:                    0
% 3.42/0.99  
%------------------------------------------------------------------------------
