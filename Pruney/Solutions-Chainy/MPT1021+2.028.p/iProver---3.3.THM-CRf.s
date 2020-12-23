%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n016.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:07:23 EST 2020

% Result     : Theorem 3.06s
% Output     : CNFRefutation 3.06s
% Verified   : 
% Statistics : Number of formulae       :  234 (2883 expanded)
%              Number of clauses        :  163 ( 949 expanded)
%              Number of leaves         :   21 ( 551 expanded)
%              Depth                    :   22
%              Number of atoms          :  800 (13477 expanded)
%              Number of equality atoms :  355 (1490 expanded)
%              Maximal formula depth    :   12 (   5 average)
%              Maximal clause size      :   12 (   3 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f15,conjecture,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
        & v3_funct_2(X1,X0,X0)
        & v1_funct_2(X1,X0,X0)
        & v1_funct_1(X1) )
     => ( r2_relset_1(X0,X0,k1_partfun1(X0,X0,X0,X0,k2_funct_2(X0,X1),X1),k6_partfun1(X0))
        & r2_relset_1(X0,X0,k1_partfun1(X0,X0,X0,X0,X1,k2_funct_2(X0,X1)),k6_partfun1(X0)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f16,negated_conjecture,(
    ~ ! [X0,X1] :
        ( ( m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
          & v3_funct_2(X1,X0,X0)
          & v1_funct_2(X1,X0,X0)
          & v1_funct_1(X1) )
       => ( r2_relset_1(X0,X0,k1_partfun1(X0,X0,X0,X0,k2_funct_2(X0,X1),X1),k6_partfun1(X0))
          & r2_relset_1(X0,X0,k1_partfun1(X0,X0,X0,X0,X1,k2_funct_2(X0,X1)),k6_partfun1(X0)) ) ) ),
    inference(negated_conjecture,[],[f15])).

fof(f41,plain,(
    ? [X0,X1] :
      ( ( ~ r2_relset_1(X0,X0,k1_partfun1(X0,X0,X0,X0,k2_funct_2(X0,X1),X1),k6_partfun1(X0))
        | ~ r2_relset_1(X0,X0,k1_partfun1(X0,X0,X0,X0,X1,k2_funct_2(X0,X1)),k6_partfun1(X0)) )
      & m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
      & v3_funct_2(X1,X0,X0)
      & v1_funct_2(X1,X0,X0)
      & v1_funct_1(X1) ) ),
    inference(ennf_transformation,[],[f16])).

fof(f42,plain,(
    ? [X0,X1] :
      ( ( ~ r2_relset_1(X0,X0,k1_partfun1(X0,X0,X0,X0,k2_funct_2(X0,X1),X1),k6_partfun1(X0))
        | ~ r2_relset_1(X0,X0,k1_partfun1(X0,X0,X0,X0,X1,k2_funct_2(X0,X1)),k6_partfun1(X0)) )
      & m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
      & v3_funct_2(X1,X0,X0)
      & v1_funct_2(X1,X0,X0)
      & v1_funct_1(X1) ) ),
    inference(flattening,[],[f41])).

fof(f44,plain,
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

fof(f45,plain,
    ( ( ~ r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK0,sK0,sK0,k2_funct_2(sK0,sK1),sK1),k6_partfun1(sK0))
      | ~ r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK0,sK0,sK0,sK1,k2_funct_2(sK0,sK1)),k6_partfun1(sK0)) )
    & m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
    & v3_funct_2(sK1,sK0,sK0)
    & v1_funct_2(sK1,sK0,sK0)
    & v1_funct_1(sK1) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f42,f44])).

fof(f71,plain,(
    m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) ),
    inference(cnf_transformation,[],[f45])).

fof(f13,axiom,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
        & v3_funct_2(X1,X0,X0)
        & v1_funct_2(X1,X0,X0)
        & v1_funct_1(X1) )
     => k2_funct_1(X1) = k2_funct_2(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f39,plain,(
    ! [X0,X1] :
      ( k2_funct_1(X1) = k2_funct_2(X0,X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
      | ~ v3_funct_2(X1,X0,X0)
      | ~ v1_funct_2(X1,X0,X0)
      | ~ v1_funct_1(X1) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f40,plain,(
    ! [X0,X1] :
      ( k2_funct_1(X1) = k2_funct_2(X0,X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
      | ~ v3_funct_2(X1,X0,X0)
      | ~ v1_funct_2(X1,X0,X0)
      | ~ v1_funct_1(X1) ) ),
    inference(flattening,[],[f39])).

fof(f66,plain,(
    ! [X0,X1] :
      ( k2_funct_1(X1) = k2_funct_2(X0,X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
      | ~ v3_funct_2(X1,X0,X0)
      | ~ v1_funct_2(X1,X0,X0)
      | ~ v1_funct_1(X1) ) ),
    inference(cnf_transformation,[],[f40])).

fof(f68,plain,(
    v1_funct_1(sK1) ),
    inference(cnf_transformation,[],[f45])).

fof(f69,plain,(
    v1_funct_2(sK1,sK0,sK0) ),
    inference(cnf_transformation,[],[f45])).

fof(f70,plain,(
    v3_funct_2(sK1,sK0,sK0) ),
    inference(cnf_transformation,[],[f45])).

fof(f10,axiom,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
        & v3_funct_2(X1,X0,X0)
        & v1_funct_2(X1,X0,X0)
        & v1_funct_1(X1) )
     => ( m1_subset_1(k2_funct_2(X0,X1),k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
        & v3_funct_2(k2_funct_2(X0,X1),X0,X0)
        & v1_funct_2(k2_funct_2(X0,X1),X0,X0)
        & v1_funct_1(k2_funct_2(X0,X1)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f35,plain,(
    ! [X0,X1] :
      ( ( m1_subset_1(k2_funct_2(X0,X1),k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
        & v3_funct_2(k2_funct_2(X0,X1),X0,X0)
        & v1_funct_2(k2_funct_2(X0,X1),X0,X0)
        & v1_funct_1(k2_funct_2(X0,X1)) )
      | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
      | ~ v3_funct_2(X1,X0,X0)
      | ~ v1_funct_2(X1,X0,X0)
      | ~ v1_funct_1(X1) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f36,plain,(
    ! [X0,X1] :
      ( ( m1_subset_1(k2_funct_2(X0,X1),k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
        & v3_funct_2(k2_funct_2(X0,X1),X0,X0)
        & v1_funct_2(k2_funct_2(X0,X1),X0,X0)
        & v1_funct_1(k2_funct_2(X0,X1)) )
      | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
      | ~ v3_funct_2(X1,X0,X0)
      | ~ v1_funct_2(X1,X0,X0)
      | ~ v1_funct_1(X1) ) ),
    inference(flattening,[],[f35])).

fof(f63,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k2_funct_2(X0,X1),k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
      | ~ v3_funct_2(X1,X0,X0)
      | ~ v1_funct_2(X1,X0,X0)
      | ~ v1_funct_1(X1) ) ),
    inference(cnf_transformation,[],[f36])).

fof(f8,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => ( ( v3_funct_2(X2,X0,X1)
          & v1_funct_1(X2) )
       => ( v2_funct_2(X2,X1)
          & v2_funct_1(X2)
          & v1_funct_1(X2) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f31,plain,(
    ! [X0,X1,X2] :
      ( ( v2_funct_2(X2,X1)
        & v2_funct_1(X2)
        & v1_funct_1(X2) )
      | ~ v3_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f32,plain,(
    ! [X0,X1,X2] :
      ( ( v2_funct_2(X2,X1)
        & v2_funct_1(X2)
        & v1_funct_1(X2) )
      | ~ v3_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(flattening,[],[f31])).

fof(f57,plain,(
    ! [X2,X0,X1] :
      ( v2_funct_2(X2,X1)
      | ~ v3_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f32])).

fof(f6,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => ( v5_relat_1(X2,X1)
        & v4_relat_1(X2,X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f18,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => v5_relat_1(X2,X1) ) ),
    inference(pure_predicate_removal,[],[f6])).

fof(f28,plain,(
    ! [X0,X1,X2] :
      ( v5_relat_1(X2,X1)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f18])).

fof(f53,plain,(
    ! [X2,X0,X1] :
      ( v5_relat_1(X2,X1)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f9,axiom,(
    ! [X0,X1] :
      ( ( v5_relat_1(X1,X0)
        & v1_relat_1(X1) )
     => ( v2_funct_2(X1,X0)
      <=> k2_relat_1(X1) = X0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f33,plain,(
    ! [X0,X1] :
      ( ( v2_funct_2(X1,X0)
      <=> k2_relat_1(X1) = X0 )
      | ~ v5_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f34,plain,(
    ! [X0,X1] :
      ( ( v2_funct_2(X1,X0)
      <=> k2_relat_1(X1) = X0 )
      | ~ v5_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f33])).

fof(f43,plain,(
    ! [X0,X1] :
      ( ( ( v2_funct_2(X1,X0)
          | k2_relat_1(X1) != X0 )
        & ( k2_relat_1(X1) = X0
          | ~ v2_funct_2(X1,X0) ) )
      | ~ v5_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(nnf_transformation,[],[f34])).

fof(f58,plain,(
    ! [X0,X1] :
      ( k2_relat_1(X1) = X0
      | ~ v2_funct_2(X1,X0)
      | ~ v5_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f43])).

fof(f5,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => v1_relat_1(X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f27,plain,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f52,plain,(
    ! [X2,X0,X1] :
      ( v1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f1,axiom,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ( v1_funct_1(k2_funct_1(X0))
        & v1_relat_1(k2_funct_1(X0)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f19,plain,(
    ! [X0] :
      ( ( v1_funct_1(k2_funct_1(X0))
        & v1_relat_1(k2_funct_1(X0)) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f20,plain,(
    ! [X0] :
      ( ( v1_funct_1(k2_funct_1(X0))
        & v1_relat_1(k2_funct_1(X0)) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f19])).

fof(f47,plain,(
    ! [X0] :
      ( v1_funct_1(k2_funct_1(X0))
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f62,plain,(
    ! [X0,X1] :
      ( v3_funct_2(k2_funct_2(X0,X1),X0,X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
      | ~ v3_funct_2(X1,X0,X0)
      | ~ v1_funct_2(X1,X0,X0)
      | ~ v1_funct_1(X1) ) ),
    inference(cnf_transformation,[],[f36])).

fof(f56,plain,(
    ! [X2,X0,X1] :
      ( v2_funct_1(X2)
      | ~ v3_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f32])).

fof(f3,axiom,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ( v2_funct_1(X0)
       => v2_funct_1(k2_funct_1(X0)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f23,plain,(
    ! [X0] :
      ( v2_funct_1(k2_funct_1(X0))
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f24,plain,(
    ! [X0] :
      ( v2_funct_1(k2_funct_1(X0))
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f23])).

fof(f50,plain,(
    ! [X0] :
      ( v2_funct_1(k2_funct_1(X0))
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f2,axiom,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ( v2_funct_1(X0)
       => ( k5_relat_1(k2_funct_1(X0),X0) = k6_relat_1(k2_relat_1(X0))
          & k5_relat_1(X0,k2_funct_1(X0)) = k6_relat_1(k1_relat_1(X0)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f21,plain,(
    ! [X0] :
      ( ( k5_relat_1(k2_funct_1(X0),X0) = k6_relat_1(k2_relat_1(X0))
        & k5_relat_1(X0,k2_funct_1(X0)) = k6_relat_1(k1_relat_1(X0)) )
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f22,plain,(
    ! [X0] :
      ( ( k5_relat_1(k2_funct_1(X0),X0) = k6_relat_1(k2_relat_1(X0))
        & k5_relat_1(X0,k2_funct_1(X0)) = k6_relat_1(k1_relat_1(X0)) )
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f21])).

fof(f49,plain,(
    ! [X0] :
      ( k5_relat_1(k2_funct_1(X0),X0) = k6_relat_1(k2_relat_1(X0))
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f14,axiom,(
    ! [X0] : k6_relat_1(X0) = k6_partfun1(X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f67,plain,(
    ! [X0] : k6_relat_1(X0) = k6_partfun1(X0) ),
    inference(cnf_transformation,[],[f14])).

fof(f73,plain,(
    ! [X0] :
      ( k5_relat_1(k2_funct_1(X0),X0) = k6_partfun1(k2_relat_1(X0))
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(definition_unfolding,[],[f49,f67])).

fof(f4,axiom,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ( v2_funct_1(X0)
       => k2_funct_1(k2_funct_1(X0)) = X0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f25,plain,(
    ! [X0] :
      ( k2_funct_1(k2_funct_1(X0)) = X0
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f26,plain,(
    ! [X0] :
      ( k2_funct_1(k2_funct_1(X0)) = X0
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f25])).

fof(f51,plain,(
    ! [X0] :
      ( k2_funct_1(k2_funct_1(X0)) = X0
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f48,plain,(
    ! [X0] :
      ( k5_relat_1(X0,k2_funct_1(X0)) = k6_relat_1(k1_relat_1(X0))
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f74,plain,(
    ! [X0] :
      ( k5_relat_1(X0,k2_funct_1(X0)) = k6_partfun1(k1_relat_1(X0))
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(definition_unfolding,[],[f48,f67])).

fof(f46,plain,(
    ! [X0] :
      ( v1_relat_1(k2_funct_1(X0))
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f12,axiom,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( ( m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
        & v1_funct_1(X5)
        & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_1(X4) )
     => k5_relat_1(X4,X5) = k1_partfun1(X0,X1,X2,X3,X4,X5) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f37,plain,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( k5_relat_1(X4,X5) = k1_partfun1(X0,X1,X2,X3,X4,X5)
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ v1_funct_1(X5)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X4) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f38,plain,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( k5_relat_1(X4,X5) = k1_partfun1(X0,X1,X2,X3,X4,X5)
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ v1_funct_1(X5)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X4) ) ),
    inference(flattening,[],[f37])).

fof(f65,plain,(
    ! [X4,X2,X0,X5,X3,X1] :
      ( k5_relat_1(X4,X5) = k1_partfun1(X0,X1,X2,X3,X4,X5)
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ v1_funct_1(X5)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X4) ) ),
    inference(cnf_transformation,[],[f38])).

fof(f60,plain,(
    ! [X0,X1] :
      ( v1_funct_1(k2_funct_2(X0,X1))
      | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
      | ~ v3_funct_2(X1,X0,X0)
      | ~ v1_funct_2(X1,X0,X0)
      | ~ v1_funct_1(X1) ) ),
    inference(cnf_transformation,[],[f36])).

fof(f72,plain,
    ( ~ r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK0,sK0,sK0,k2_funct_2(sK0,sK1),sK1),k6_partfun1(sK0))
    | ~ r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK0,sK0,sK0,sK1,k2_funct_2(sK0,sK1)),k6_partfun1(sK0)) ),
    inference(cnf_transformation,[],[f45])).

fof(f11,axiom,(
    ! [X0] :
      ( m1_subset_1(k6_partfun1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
      & v1_partfun1(k6_partfun1(X0),X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f17,plain,(
    ! [X0] : m1_subset_1(k6_partfun1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0))) ),
    inference(pure_predicate_removal,[],[f11])).

fof(f64,plain,(
    ! [X0] : m1_subset_1(k6_partfun1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0))) ),
    inference(cnf_transformation,[],[f17])).

fof(f7,axiom,(
    ! [X0,X1,X2,X3] :
      ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) )
     => r2_relset_1(X0,X1,X2,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f29,plain,(
    ! [X0,X1,X2,X3] :
      ( r2_relset_1(X0,X1,X2,X2)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f30,plain,(
    ! [X0,X1,X2,X3] :
      ( r2_relset_1(X0,X1,X2,X2)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(flattening,[],[f29])).

fof(f54,plain,(
    ! [X2,X0,X3,X1] :
      ( r2_relset_1(X0,X1,X2,X2)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f30])).

cnf(c_22,negated_conjecture,
    ( m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) ),
    inference(cnf_transformation,[],[f71])).

cnf(c_518,negated_conjecture,
    ( m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) ),
    inference(subtyping,[status(esa)],[c_22])).

cnf(c_1028,plain,
    ( m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_518])).

cnf(c_20,plain,
    ( ~ v1_funct_2(X0,X1,X1)
    | ~ v3_funct_2(X0,X1,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X1)))
    | ~ v1_funct_1(X0)
    | k2_funct_2(X1,X0) = k2_funct_1(X0) ),
    inference(cnf_transformation,[],[f66])).

cnf(c_520,plain,
    ( ~ v1_funct_2(X0_48,X0_49,X0_49)
    | ~ v3_funct_2(X0_48,X0_49,X0_49)
    | ~ m1_subset_1(X0_48,k1_zfmisc_1(k2_zfmisc_1(X0_49,X0_49)))
    | ~ v1_funct_1(X0_48)
    | k2_funct_2(X0_49,X0_48) = k2_funct_1(X0_48) ),
    inference(subtyping,[status(esa)],[c_20])).

cnf(c_1026,plain,
    ( k2_funct_2(X0_49,X0_48) = k2_funct_1(X0_48)
    | v1_funct_2(X0_48,X0_49,X0_49) != iProver_top
    | v3_funct_2(X0_48,X0_49,X0_49) != iProver_top
    | m1_subset_1(X0_48,k1_zfmisc_1(k2_zfmisc_1(X0_49,X0_49))) != iProver_top
    | v1_funct_1(X0_48) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_520])).

cnf(c_2093,plain,
    ( k2_funct_2(sK0,sK1) = k2_funct_1(sK1)
    | v1_funct_2(sK1,sK0,sK0) != iProver_top
    | v3_funct_2(sK1,sK0,sK0) != iProver_top
    | v1_funct_1(sK1) != iProver_top ),
    inference(superposition,[status(thm)],[c_1028,c_1026])).

cnf(c_25,negated_conjecture,
    ( v1_funct_1(sK1) ),
    inference(cnf_transformation,[],[f68])).

cnf(c_24,negated_conjecture,
    ( v1_funct_2(sK1,sK0,sK0) ),
    inference(cnf_transformation,[],[f69])).

cnf(c_23,negated_conjecture,
    ( v3_funct_2(sK1,sK0,sK0) ),
    inference(cnf_transformation,[],[f70])).

cnf(c_620,plain,
    ( ~ v1_funct_2(sK1,sK0,sK0)
    | ~ v3_funct_2(sK1,sK0,sK0)
    | ~ m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
    | ~ v1_funct_1(sK1)
    | k2_funct_2(sK0,sK1) = k2_funct_1(sK1) ),
    inference(instantiation,[status(thm)],[c_520])).

cnf(c_2393,plain,
    ( k2_funct_2(sK0,sK1) = k2_funct_1(sK1) ),
    inference(global_propositional_subsumption,[status(thm)],[c_2093,c_25,c_24,c_23,c_22,c_620])).

cnf(c_14,plain,
    ( ~ v1_funct_2(X0,X1,X1)
    | ~ v3_funct_2(X0,X1,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X1)))
    | m1_subset_1(k2_funct_2(X1,X0),k1_zfmisc_1(k2_zfmisc_1(X1,X1)))
    | ~ v1_funct_1(X0) ),
    inference(cnf_transformation,[],[f63])).

cnf(c_526,plain,
    ( ~ v1_funct_2(X0_48,X0_49,X0_49)
    | ~ v3_funct_2(X0_48,X0_49,X0_49)
    | ~ m1_subset_1(X0_48,k1_zfmisc_1(k2_zfmisc_1(X0_49,X0_49)))
    | m1_subset_1(k2_funct_2(X0_49,X0_48),k1_zfmisc_1(k2_zfmisc_1(X0_49,X0_49)))
    | ~ v1_funct_1(X0_48) ),
    inference(subtyping,[status(esa)],[c_14])).

cnf(c_1020,plain,
    ( v1_funct_2(X0_48,X0_49,X0_49) != iProver_top
    | v3_funct_2(X0_48,X0_49,X0_49) != iProver_top
    | m1_subset_1(X0_48,k1_zfmisc_1(k2_zfmisc_1(X0_49,X0_49))) != iProver_top
    | m1_subset_1(k2_funct_2(X0_49,X0_48),k1_zfmisc_1(k2_zfmisc_1(X0_49,X0_49))) = iProver_top
    | v1_funct_1(X0_48) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_526])).

cnf(c_2406,plain,
    ( v1_funct_2(sK1,sK0,sK0) != iProver_top
    | v3_funct_2(sK1,sK0,sK0) != iProver_top
    | m1_subset_1(k2_funct_1(sK1),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) = iProver_top
    | m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) != iProver_top
    | v1_funct_1(sK1) != iProver_top ),
    inference(superposition,[status(thm)],[c_2393,c_1020])).

cnf(c_26,plain,
    ( v1_funct_1(sK1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_25])).

cnf(c_27,plain,
    ( v1_funct_2(sK1,sK0,sK0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_24])).

cnf(c_28,plain,
    ( v3_funct_2(sK1,sK0,sK0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_23])).

cnf(c_29,plain,
    ( m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_22])).

cnf(c_3199,plain,
    ( m1_subset_1(k2_funct_1(sK1),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_2406,c_26,c_27,c_28,c_29])).

cnf(c_9,plain,
    ( ~ v3_funct_2(X0,X1,X2)
    | v2_funct_2(X0,X2)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ v1_funct_1(X0) ),
    inference(cnf_transformation,[],[f57])).

cnf(c_7,plain,
    ( v5_relat_1(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) ),
    inference(cnf_transformation,[],[f53])).

cnf(c_13,plain,
    ( ~ v2_funct_2(X0,X1)
    | ~ v5_relat_1(X0,X1)
    | ~ v1_relat_1(X0)
    | k2_relat_1(X0) = X1 ),
    inference(cnf_transformation,[],[f58])).

cnf(c_291,plain,
    ( ~ v2_funct_2(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X2,X1)))
    | ~ v1_relat_1(X0)
    | k2_relat_1(X0) = X1 ),
    inference(resolution,[status(thm)],[c_7,c_13])).

cnf(c_6,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f52])).

cnf(c_303,plain,
    ( ~ v2_funct_2(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X2,X1)))
    | k2_relat_1(X0) = X1 ),
    inference(forward_subsumption_resolution,[status(thm)],[c_291,c_6])).

cnf(c_334,plain,
    ( ~ v3_funct_2(X0,X1,X2)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X4,X5)))
    | ~ v1_funct_1(X0)
    | X3 != X0
    | X5 != X2
    | k2_relat_1(X3) = X5 ),
    inference(resolution_lifted,[status(thm)],[c_9,c_303])).

cnf(c_335,plain,
    ( ~ v3_funct_2(X0,X1,X2)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X3,X2)))
    | ~ v1_funct_1(X0)
    | k2_relat_1(X0) = X2 ),
    inference(unflattening,[status(thm)],[c_334])).

cnf(c_514,plain,
    ( ~ v3_funct_2(X0_48,X0_49,X1_49)
    | ~ m1_subset_1(X0_48,k1_zfmisc_1(k2_zfmisc_1(X0_49,X1_49)))
    | ~ m1_subset_1(X0_48,k1_zfmisc_1(k2_zfmisc_1(X2_49,X1_49)))
    | ~ v1_funct_1(X0_48)
    | k2_relat_1(X0_48) = X1_49 ),
    inference(subtyping,[status(esa)],[c_335])).

cnf(c_1032,plain,
    ( k2_relat_1(X0_48) = X0_49
    | v3_funct_2(X0_48,X1_49,X0_49) != iProver_top
    | m1_subset_1(X0_48,k1_zfmisc_1(k2_zfmisc_1(X2_49,X0_49))) != iProver_top
    | m1_subset_1(X0_48,k1_zfmisc_1(k2_zfmisc_1(X1_49,X0_49))) != iProver_top
    | v1_funct_1(X0_48) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_514])).

cnf(c_3614,plain,
    ( k2_relat_1(k2_funct_1(sK1)) = sK0
    | v3_funct_2(k2_funct_1(sK1),X0_49,sK0) != iProver_top
    | m1_subset_1(k2_funct_1(sK1),k1_zfmisc_1(k2_zfmisc_1(X0_49,sK0))) != iProver_top
    | v1_funct_1(k2_funct_1(sK1)) != iProver_top ),
    inference(superposition,[status(thm)],[c_3199,c_1032])).

cnf(c_0,plain,
    ( ~ v1_relat_1(X0)
    | ~ v1_funct_1(X0)
    | v1_funct_1(k2_funct_1(X0)) ),
    inference(cnf_transformation,[],[f47])).

cnf(c_535,plain,
    ( ~ v1_relat_1(X0_48)
    | ~ v1_funct_1(X0_48)
    | v1_funct_1(k2_funct_1(X0_48)) ),
    inference(subtyping,[status(esa)],[c_0])).

cnf(c_576,plain,
    ( v1_relat_1(X0_48) != iProver_top
    | v1_funct_1(X0_48) != iProver_top
    | v1_funct_1(k2_funct_1(X0_48)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_535])).

cnf(c_578,plain,
    ( v1_relat_1(sK1) != iProver_top
    | v1_funct_1(k2_funct_1(sK1)) = iProver_top
    | v1_funct_1(sK1) != iProver_top ),
    inference(instantiation,[status(thm)],[c_576])).

cnf(c_529,plain,
    ( ~ m1_subset_1(X0_48,k1_zfmisc_1(k2_zfmisc_1(X0_49,X1_49)))
    | v1_relat_1(X0_48) ),
    inference(subtyping,[status(esa)],[c_6])).

cnf(c_594,plain,
    ( m1_subset_1(X0_48,k1_zfmisc_1(k2_zfmisc_1(X0_49,X1_49))) != iProver_top
    | v1_relat_1(X0_48) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_529])).

cnf(c_596,plain,
    ( m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) != iProver_top
    | v1_relat_1(sK1) = iProver_top ),
    inference(instantiation,[status(thm)],[c_594])).

cnf(c_15,plain,
    ( ~ v1_funct_2(X0,X1,X1)
    | ~ v3_funct_2(X0,X1,X1)
    | v3_funct_2(k2_funct_2(X1,X0),X1,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X1)))
    | ~ v1_funct_1(X0) ),
    inference(cnf_transformation,[],[f62])).

cnf(c_525,plain,
    ( ~ v1_funct_2(X0_48,X0_49,X0_49)
    | ~ v3_funct_2(X0_48,X0_49,X0_49)
    | v3_funct_2(k2_funct_2(X0_49,X0_48),X0_49,X0_49)
    | ~ m1_subset_1(X0_48,k1_zfmisc_1(k2_zfmisc_1(X0_49,X0_49)))
    | ~ v1_funct_1(X0_48) ),
    inference(subtyping,[status(esa)],[c_15])).

cnf(c_1021,plain,
    ( v1_funct_2(X0_48,X0_49,X0_49) != iProver_top
    | v3_funct_2(X0_48,X0_49,X0_49) != iProver_top
    | v3_funct_2(k2_funct_2(X0_49,X0_48),X0_49,X0_49) = iProver_top
    | m1_subset_1(X0_48,k1_zfmisc_1(k2_zfmisc_1(X0_49,X0_49))) != iProver_top
    | v1_funct_1(X0_48) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_525])).

cnf(c_2239,plain,
    ( v1_funct_2(sK1,sK0,sK0) != iProver_top
    | v3_funct_2(k2_funct_2(sK0,sK1),sK0,sK0) = iProver_top
    | v3_funct_2(sK1,sK0,sK0) != iProver_top
    | v1_funct_1(sK1) != iProver_top ),
    inference(superposition,[status(thm)],[c_1028,c_1021])).

cnf(c_606,plain,
    ( v1_funct_2(X0_48,X0_49,X0_49) != iProver_top
    | v3_funct_2(X0_48,X0_49,X0_49) != iProver_top
    | v3_funct_2(k2_funct_2(X0_49,X0_48),X0_49,X0_49) = iProver_top
    | m1_subset_1(X0_48,k1_zfmisc_1(k2_zfmisc_1(X0_49,X0_49))) != iProver_top
    | v1_funct_1(X0_48) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_525])).

cnf(c_608,plain,
    ( v1_funct_2(sK1,sK0,sK0) != iProver_top
    | v3_funct_2(k2_funct_2(sK0,sK1),sK0,sK0) = iProver_top
    | v3_funct_2(sK1,sK0,sK0) != iProver_top
    | m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) != iProver_top
    | v1_funct_1(sK1) != iProver_top ),
    inference(instantiation,[status(thm)],[c_606])).

cnf(c_2459,plain,
    ( v3_funct_2(k2_funct_2(sK0,sK1),sK0,sK0) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_2239,c_26,c_27,c_28,c_29,c_608])).

cnf(c_2463,plain,
    ( v3_funct_2(k2_funct_1(sK1),sK0,sK0) = iProver_top ),
    inference(light_normalisation,[status(thm)],[c_2459,c_2393])).

cnf(c_3663,plain,
    ( k2_relat_1(k2_funct_1(sK1)) = sK0
    | v3_funct_2(k2_funct_1(sK1),sK0,sK0) != iProver_top
    | m1_subset_1(k2_funct_1(sK1),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) != iProver_top
    | v1_funct_1(k2_funct_1(sK1)) != iProver_top ),
    inference(instantiation,[status(thm)],[c_3614])).

cnf(c_5242,plain,
    ( k2_relat_1(k2_funct_1(sK1)) = sK0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_3614,c_26,c_27,c_28,c_29,c_578,c_596,c_2406,c_2463,c_3663])).

cnf(c_10,plain,
    ( ~ v3_funct_2(X0,X1,X2)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | v2_funct_1(X0)
    | ~ v1_funct_1(X0) ),
    inference(cnf_transformation,[],[f56])).

cnf(c_527,plain,
    ( ~ v3_funct_2(X0_48,X0_49,X1_49)
    | ~ m1_subset_1(X0_48,k1_zfmisc_1(k2_zfmisc_1(X0_49,X1_49)))
    | v2_funct_1(X0_48)
    | ~ v1_funct_1(X0_48) ),
    inference(subtyping,[status(esa)],[c_10])).

cnf(c_1019,plain,
    ( v3_funct_2(X0_48,X0_49,X1_49) != iProver_top
    | m1_subset_1(X0_48,k1_zfmisc_1(k2_zfmisc_1(X0_49,X1_49))) != iProver_top
    | v2_funct_1(X0_48) = iProver_top
    | v1_funct_1(X0_48) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_527])).

cnf(c_3206,plain,
    ( v3_funct_2(k2_funct_1(sK1),sK0,sK0) != iProver_top
    | v2_funct_1(k2_funct_1(sK1)) = iProver_top
    | v1_funct_1(k2_funct_1(sK1)) != iProver_top ),
    inference(superposition,[status(thm)],[c_3199,c_1019])).

cnf(c_4,plain,
    ( ~ v2_funct_1(X0)
    | v2_funct_1(k2_funct_1(X0))
    | ~ v1_relat_1(X0)
    | ~ v1_funct_1(X0) ),
    inference(cnf_transformation,[],[f50])).

cnf(c_531,plain,
    ( ~ v2_funct_1(X0_48)
    | v2_funct_1(k2_funct_1(X0_48))
    | ~ v1_relat_1(X0_48)
    | ~ v1_funct_1(X0_48) ),
    inference(subtyping,[status(esa)],[c_4])).

cnf(c_588,plain,
    ( v2_funct_1(X0_48) != iProver_top
    | v2_funct_1(k2_funct_1(X0_48)) = iProver_top
    | v1_relat_1(X0_48) != iProver_top
    | v1_funct_1(X0_48) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_531])).

cnf(c_590,plain,
    ( v2_funct_1(k2_funct_1(sK1)) = iProver_top
    | v2_funct_1(sK1) != iProver_top
    | v1_relat_1(sK1) != iProver_top
    | v1_funct_1(sK1) != iProver_top ),
    inference(instantiation,[status(thm)],[c_588])).

cnf(c_600,plain,
    ( v3_funct_2(X0_48,X0_49,X1_49) != iProver_top
    | m1_subset_1(X0_48,k1_zfmisc_1(k2_zfmisc_1(X0_49,X1_49))) != iProver_top
    | v2_funct_1(X0_48) = iProver_top
    | v1_funct_1(X0_48) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_527])).

cnf(c_602,plain,
    ( v3_funct_2(sK1,sK0,sK0) != iProver_top
    | m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) != iProver_top
    | v2_funct_1(sK1) = iProver_top
    | v1_funct_1(sK1) != iProver_top ),
    inference(instantiation,[status(thm)],[c_600])).

cnf(c_3775,plain,
    ( v2_funct_1(k2_funct_1(sK1)) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_3206,c_26,c_28,c_29,c_590,c_596,c_602])).

cnf(c_2,plain,
    ( ~ v2_funct_1(X0)
    | ~ v1_relat_1(X0)
    | ~ v1_funct_1(X0)
    | k5_relat_1(k2_funct_1(X0),X0) = k6_partfun1(k2_relat_1(X0)) ),
    inference(cnf_transformation,[],[f73])).

cnf(c_533,plain,
    ( ~ v2_funct_1(X0_48)
    | ~ v1_relat_1(X0_48)
    | ~ v1_funct_1(X0_48)
    | k5_relat_1(k2_funct_1(X0_48),X0_48) = k6_partfun1(k2_relat_1(X0_48)) ),
    inference(subtyping,[status(esa)],[c_2])).

cnf(c_1013,plain,
    ( k5_relat_1(k2_funct_1(X0_48),X0_48) = k6_partfun1(k2_relat_1(X0_48))
    | v2_funct_1(X0_48) != iProver_top
    | v1_relat_1(X0_48) != iProver_top
    | v1_funct_1(X0_48) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_533])).

cnf(c_3781,plain,
    ( k5_relat_1(k2_funct_1(k2_funct_1(sK1)),k2_funct_1(sK1)) = k6_partfun1(k2_relat_1(k2_funct_1(sK1)))
    | v1_relat_1(k2_funct_1(sK1)) != iProver_top
    | v1_funct_1(k2_funct_1(sK1)) != iProver_top ),
    inference(superposition,[status(thm)],[c_3775,c_1013])).

cnf(c_1751,plain,
    ( v3_funct_2(sK1,sK0,sK0) != iProver_top
    | v2_funct_1(sK1) = iProver_top
    | v1_funct_1(sK1) != iProver_top ),
    inference(superposition,[status(thm)],[c_1028,c_1019])).

cnf(c_1872,plain,
    ( v2_funct_1(sK1) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_1751,c_26,c_28,c_29,c_602])).

cnf(c_5,plain,
    ( ~ v2_funct_1(X0)
    | ~ v1_relat_1(X0)
    | ~ v1_funct_1(X0)
    | k2_funct_1(k2_funct_1(X0)) = X0 ),
    inference(cnf_transformation,[],[f51])).

cnf(c_530,plain,
    ( ~ v2_funct_1(X0_48)
    | ~ v1_relat_1(X0_48)
    | ~ v1_funct_1(X0_48)
    | k2_funct_1(k2_funct_1(X0_48)) = X0_48 ),
    inference(subtyping,[status(esa)],[c_5])).

cnf(c_1016,plain,
    ( k2_funct_1(k2_funct_1(X0_48)) = X0_48
    | v2_funct_1(X0_48) != iProver_top
    | v1_relat_1(X0_48) != iProver_top
    | v1_funct_1(X0_48) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_530])).

cnf(c_1879,plain,
    ( k2_funct_1(k2_funct_1(sK1)) = sK1
    | v1_relat_1(sK1) != iProver_top
    | v1_funct_1(sK1) != iProver_top ),
    inference(superposition,[status(thm)],[c_1872,c_1016])).

cnf(c_592,plain,
    ( ~ v2_funct_1(sK1)
    | ~ v1_relat_1(sK1)
    | ~ v1_funct_1(sK1)
    | k2_funct_1(k2_funct_1(sK1)) = sK1 ),
    inference(instantiation,[status(thm)],[c_530])).

cnf(c_595,plain,
    ( ~ m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
    | v1_relat_1(sK1) ),
    inference(instantiation,[status(thm)],[c_529])).

cnf(c_601,plain,
    ( ~ v3_funct_2(sK1,sK0,sK0)
    | ~ m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
    | v2_funct_1(sK1)
    | ~ v1_funct_1(sK1) ),
    inference(instantiation,[status(thm)],[c_527])).

cnf(c_2642,plain,
    ( k2_funct_1(k2_funct_1(sK1)) = sK1 ),
    inference(global_propositional_subsumption,[status(thm)],[c_1879,c_25,c_23,c_22,c_592,c_595,c_601])).

cnf(c_3,plain,
    ( ~ v2_funct_1(X0)
    | ~ v1_relat_1(X0)
    | ~ v1_funct_1(X0)
    | k5_relat_1(X0,k2_funct_1(X0)) = k6_partfun1(k1_relat_1(X0)) ),
    inference(cnf_transformation,[],[f74])).

cnf(c_532,plain,
    ( ~ v2_funct_1(X0_48)
    | ~ v1_relat_1(X0_48)
    | ~ v1_funct_1(X0_48)
    | k5_relat_1(X0_48,k2_funct_1(X0_48)) = k6_partfun1(k1_relat_1(X0_48)) ),
    inference(subtyping,[status(esa)],[c_3])).

cnf(c_1014,plain,
    ( k5_relat_1(X0_48,k2_funct_1(X0_48)) = k6_partfun1(k1_relat_1(X0_48))
    | v2_funct_1(X0_48) != iProver_top
    | v1_relat_1(X0_48) != iProver_top
    | v1_funct_1(X0_48) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_532])).

cnf(c_1877,plain,
    ( k5_relat_1(sK1,k2_funct_1(sK1)) = k6_partfun1(k1_relat_1(sK1))
    | v1_relat_1(sK1) != iProver_top
    | v1_funct_1(sK1) != iProver_top ),
    inference(superposition,[status(thm)],[c_1872,c_1014])).

cnf(c_586,plain,
    ( ~ v2_funct_1(sK1)
    | ~ v1_relat_1(sK1)
    | ~ v1_funct_1(sK1)
    | k5_relat_1(sK1,k2_funct_1(sK1)) = k6_partfun1(k1_relat_1(sK1)) ),
    inference(instantiation,[status(thm)],[c_532])).

cnf(c_2649,plain,
    ( k5_relat_1(sK1,k2_funct_1(sK1)) = k6_partfun1(k1_relat_1(sK1)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_1877,c_25,c_23,c_22,c_586,c_595,c_601])).

cnf(c_3790,plain,
    ( k6_partfun1(k2_relat_1(k2_funct_1(sK1))) = k6_partfun1(k1_relat_1(sK1))
    | v1_relat_1(k2_funct_1(sK1)) != iProver_top
    | v1_funct_1(k2_funct_1(sK1)) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_3781,c_2642,c_2649])).

cnf(c_1,plain,
    ( ~ v1_relat_1(X0)
    | v1_relat_1(k2_funct_1(X0))
    | ~ v1_funct_1(X0) ),
    inference(cnf_transformation,[],[f46])).

cnf(c_534,plain,
    ( ~ v1_relat_1(X0_48)
    | v1_relat_1(k2_funct_1(X0_48))
    | ~ v1_funct_1(X0_48) ),
    inference(subtyping,[status(esa)],[c_1])).

cnf(c_579,plain,
    ( v1_relat_1(X0_48) != iProver_top
    | v1_relat_1(k2_funct_1(X0_48)) = iProver_top
    | v1_funct_1(X0_48) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_534])).

cnf(c_581,plain,
    ( v1_relat_1(k2_funct_1(sK1)) = iProver_top
    | v1_relat_1(sK1) != iProver_top
    | v1_funct_1(sK1) != iProver_top ),
    inference(instantiation,[status(thm)],[c_579])).

cnf(c_3972,plain,
    ( k6_partfun1(k2_relat_1(k2_funct_1(sK1))) = k6_partfun1(k1_relat_1(sK1)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_3790,c_26,c_29,c_578,c_581,c_596])).

cnf(c_5246,plain,
    ( k6_partfun1(k1_relat_1(sK1)) = k6_partfun1(sK0) ),
    inference(demodulation,[status(thm)],[c_5242,c_3972])).

cnf(c_19,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X4,X5)))
    | ~ v1_funct_1(X0)
    | ~ v1_funct_1(X3)
    | k1_partfun1(X4,X5,X1,X2,X3,X0) = k5_relat_1(X3,X0) ),
    inference(cnf_transformation,[],[f65])).

cnf(c_521,plain,
    ( ~ m1_subset_1(X0_48,k1_zfmisc_1(k2_zfmisc_1(X0_49,X1_49)))
    | ~ m1_subset_1(X1_48,k1_zfmisc_1(k2_zfmisc_1(X2_49,X3_49)))
    | ~ v1_funct_1(X0_48)
    | ~ v1_funct_1(X1_48)
    | k1_partfun1(X2_49,X3_49,X0_49,X1_49,X1_48,X0_48) = k5_relat_1(X1_48,X0_48) ),
    inference(subtyping,[status(esa)],[c_19])).

cnf(c_1025,plain,
    ( k1_partfun1(X0_49,X1_49,X2_49,X3_49,X0_48,X1_48) = k5_relat_1(X0_48,X1_48)
    | m1_subset_1(X1_48,k1_zfmisc_1(k2_zfmisc_1(X2_49,X3_49))) != iProver_top
    | m1_subset_1(X0_48,k1_zfmisc_1(k2_zfmisc_1(X0_49,X1_49))) != iProver_top
    | v1_funct_1(X0_48) != iProver_top
    | v1_funct_1(X1_48) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_521])).

cnf(c_3205,plain,
    ( k1_partfun1(sK0,sK0,X0_49,X1_49,k2_funct_1(sK1),X0_48) = k5_relat_1(k2_funct_1(sK1),X0_48)
    | m1_subset_1(X0_48,k1_zfmisc_1(k2_zfmisc_1(X0_49,X1_49))) != iProver_top
    | v1_funct_1(X0_48) != iProver_top
    | v1_funct_1(k2_funct_1(sK1)) != iProver_top ),
    inference(superposition,[status(thm)],[c_3199,c_1025])).

cnf(c_5264,plain,
    ( v1_funct_1(X0_48) != iProver_top
    | m1_subset_1(X0_48,k1_zfmisc_1(k2_zfmisc_1(X0_49,X1_49))) != iProver_top
    | k1_partfun1(sK0,sK0,X0_49,X1_49,k2_funct_1(sK1),X0_48) = k5_relat_1(k2_funct_1(sK1),X0_48) ),
    inference(global_propositional_subsumption,[status(thm)],[c_3205,c_26,c_29,c_578,c_596])).

cnf(c_5265,plain,
    ( k1_partfun1(sK0,sK0,X0_49,X1_49,k2_funct_1(sK1),X0_48) = k5_relat_1(k2_funct_1(sK1),X0_48)
    | m1_subset_1(X0_48,k1_zfmisc_1(k2_zfmisc_1(X0_49,X1_49))) != iProver_top
    | v1_funct_1(X0_48) != iProver_top ),
    inference(renaming,[status(thm)],[c_5264])).

cnf(c_5273,plain,
    ( k1_partfun1(sK0,sK0,sK0,sK0,k2_funct_1(sK1),sK1) = k5_relat_1(k2_funct_1(sK1),sK1)
    | v1_funct_1(sK1) != iProver_top ),
    inference(superposition,[status(thm)],[c_1028,c_5265])).

cnf(c_3611,plain,
    ( k2_relat_1(sK1) = sK0
    | v3_funct_2(sK1,X0_49,sK0) != iProver_top
    | m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(X0_49,sK0))) != iProver_top
    | v1_funct_1(sK1) != iProver_top ),
    inference(superposition,[status(thm)],[c_1028,c_1032])).

cnf(c_628,plain,
    ( ~ v3_funct_2(sK1,sK0,sK0)
    | ~ m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
    | ~ v1_funct_1(sK1)
    | k2_relat_1(sK1) = sK0 ),
    inference(instantiation,[status(thm)],[c_514])).

cnf(c_3890,plain,
    ( k2_relat_1(sK1) = sK0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_3611,c_25,c_23,c_22,c_628])).

cnf(c_1878,plain,
    ( k5_relat_1(k2_funct_1(sK1),sK1) = k6_partfun1(k2_relat_1(sK1))
    | v1_relat_1(sK1) != iProver_top
    | v1_funct_1(sK1) != iProver_top ),
    inference(superposition,[status(thm)],[c_1872,c_1013])).

cnf(c_583,plain,
    ( ~ v2_funct_1(sK1)
    | ~ v1_relat_1(sK1)
    | ~ v1_funct_1(sK1)
    | k5_relat_1(k2_funct_1(sK1),sK1) = k6_partfun1(k2_relat_1(sK1)) ),
    inference(instantiation,[status(thm)],[c_533])).

cnf(c_2828,plain,
    ( k5_relat_1(k2_funct_1(sK1),sK1) = k6_partfun1(k2_relat_1(sK1)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_1878,c_25,c_23,c_22,c_583,c_595,c_601])).

cnf(c_3893,plain,
    ( k5_relat_1(k2_funct_1(sK1),sK1) = k6_partfun1(sK0) ),
    inference(demodulation,[status(thm)],[c_3890,c_2828])).

cnf(c_5304,plain,
    ( k1_partfun1(sK0,sK0,sK0,sK0,k2_funct_1(sK1),sK1) = k6_partfun1(sK0)
    | v1_funct_1(sK1) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_5273,c_3893])).

cnf(c_538,plain,
    ( X0_49 = X0_49 ),
    theory(equality)).

cnf(c_573,plain,
    ( sK0 = sK0 ),
    inference(instantiation,[status(thm)],[c_538])).

cnf(c_577,plain,
    ( ~ v1_relat_1(sK1)
    | v1_funct_1(k2_funct_1(sK1))
    | ~ v1_funct_1(sK1) ),
    inference(instantiation,[status(thm)],[c_535])).

cnf(c_541,plain,
    ( X0_48 != X1_48
    | X2_48 != X1_48
    | X2_48 = X0_48 ),
    theory(equality)).

cnf(c_1295,plain,
    ( X0_48 != X1_48
    | k6_partfun1(sK0) != X1_48
    | k6_partfun1(sK0) = X0_48 ),
    inference(instantiation,[status(thm)],[c_541])).

cnf(c_1385,plain,
    ( X0_48 != k6_partfun1(X0_49)
    | k6_partfun1(sK0) = X0_48
    | k6_partfun1(sK0) != k6_partfun1(X0_49) ),
    inference(instantiation,[status(thm)],[c_1295])).

cnf(c_1482,plain,
    ( k5_relat_1(k2_funct_1(X0_48),X0_48) != k6_partfun1(k2_relat_1(X0_48))
    | k6_partfun1(sK0) = k5_relat_1(k2_funct_1(X0_48),X0_48)
    | k6_partfun1(sK0) != k6_partfun1(k2_relat_1(X0_48)) ),
    inference(instantiation,[status(thm)],[c_1385])).

cnf(c_1483,plain,
    ( k5_relat_1(k2_funct_1(sK1),sK1) != k6_partfun1(k2_relat_1(sK1))
    | k6_partfun1(sK0) = k5_relat_1(k2_funct_1(sK1),sK1)
    | k6_partfun1(sK0) != k6_partfun1(k2_relat_1(sK1)) ),
    inference(instantiation,[status(thm)],[c_1482])).

cnf(c_547,plain,
    ( X0_49 != X1_49
    | k6_partfun1(X0_49) = k6_partfun1(X1_49) ),
    theory(equality)).

cnf(c_1297,plain,
    ( sK0 != X0_49
    | k6_partfun1(sK0) = k6_partfun1(X0_49) ),
    inference(instantiation,[status(thm)],[c_547])).

cnf(c_1843,plain,
    ( sK0 != k2_relat_1(X0_48)
    | k6_partfun1(sK0) = k6_partfun1(k2_relat_1(X0_48)) ),
    inference(instantiation,[status(thm)],[c_1297])).

cnf(c_1844,plain,
    ( sK0 != k2_relat_1(sK1)
    | k6_partfun1(sK0) = k6_partfun1(k2_relat_1(sK1)) ),
    inference(instantiation,[status(thm)],[c_1843])).

cnf(c_542,plain,
    ( X0_49 != X1_49
    | X2_49 != X1_49
    | X2_49 = X0_49 ),
    theory(equality)).

cnf(c_2164,plain,
    ( k2_relat_1(X0_48) != X0_49
    | sK0 != X0_49
    | sK0 = k2_relat_1(X0_48) ),
    inference(instantiation,[status(thm)],[c_542])).

cnf(c_2165,plain,
    ( k2_relat_1(sK1) != sK0
    | sK0 = k2_relat_1(sK1)
    | sK0 != sK0 ),
    inference(instantiation,[status(thm)],[c_2164])).

cnf(c_2407,plain,
    ( ~ v1_funct_2(sK1,sK0,sK0)
    | ~ v3_funct_2(sK1,sK0,sK0)
    | m1_subset_1(k2_funct_1(sK1),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
    | ~ m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
    | ~ v1_funct_1(sK1) ),
    inference(predicate_to_equality_rev,[status(thm)],[c_2406])).

cnf(c_3176,plain,
    ( ~ m1_subset_1(X0_48,k1_zfmisc_1(k2_zfmisc_1(X0_49,X1_49)))
    | ~ m1_subset_1(k2_funct_1(sK1),k1_zfmisc_1(k2_zfmisc_1(X2_49,X3_49)))
    | ~ v1_funct_1(X0_48)
    | ~ v1_funct_1(k2_funct_1(sK1))
    | k1_partfun1(X2_49,X3_49,X0_49,X1_49,k2_funct_1(sK1),X0_48) = k5_relat_1(k2_funct_1(sK1),X0_48) ),
    inference(instantiation,[status(thm)],[c_521])).

cnf(c_3179,plain,
    ( ~ m1_subset_1(k2_funct_1(sK1),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
    | ~ m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
    | ~ v1_funct_1(k2_funct_1(sK1))
    | ~ v1_funct_1(sK1)
    | k1_partfun1(sK0,sK0,sK0,sK0,k2_funct_1(sK1),sK1) = k5_relat_1(k2_funct_1(sK1),sK1) ),
    inference(instantiation,[status(thm)],[c_3176])).

cnf(c_1326,plain,
    ( X0_48 != X1_48
    | X0_48 = k6_partfun1(X0_49)
    | k6_partfun1(X0_49) != X1_48 ),
    inference(instantiation,[status(thm)],[c_541])).

cnf(c_2942,plain,
    ( X0_48 != k5_relat_1(k2_funct_1(X1_48),X1_48)
    | X0_48 = k6_partfun1(sK0)
    | k6_partfun1(sK0) != k5_relat_1(k2_funct_1(X1_48),X1_48) ),
    inference(instantiation,[status(thm)],[c_1326])).

cnf(c_4518,plain,
    ( k1_partfun1(X0_49,X1_49,X2_49,X3_49,k2_funct_1(sK1),sK1) != k5_relat_1(k2_funct_1(sK1),sK1)
    | k1_partfun1(X0_49,X1_49,X2_49,X3_49,k2_funct_1(sK1),sK1) = k6_partfun1(sK0)
    | k6_partfun1(sK0) != k5_relat_1(k2_funct_1(sK1),sK1) ),
    inference(instantiation,[status(thm)],[c_2942])).

cnf(c_4522,plain,
    ( k1_partfun1(sK0,sK0,sK0,sK0,k2_funct_1(sK1),sK1) != k5_relat_1(k2_funct_1(sK1),sK1)
    | k1_partfun1(sK0,sK0,sK0,sK0,k2_funct_1(sK1),sK1) = k6_partfun1(sK0)
    | k6_partfun1(sK0) != k5_relat_1(k2_funct_1(sK1),sK1) ),
    inference(instantiation,[status(thm)],[c_4518])).

cnf(c_5497,plain,
    ( k1_partfun1(sK0,sK0,sK0,sK0,k2_funct_1(sK1),sK1) = k6_partfun1(sK0) ),
    inference(global_propositional_subsumption,[status(thm)],[c_5304,c_25,c_24,c_23,c_22,c_573,c_577,c_583,c_595,c_601,c_628,c_1483,c_1844,c_2165,c_2407,c_3179,c_4522])).

cnf(c_2785,plain,
    ( k1_partfun1(sK0,sK0,X0_49,X1_49,sK1,X0_48) = k5_relat_1(sK1,X0_48)
    | m1_subset_1(X0_48,k1_zfmisc_1(k2_zfmisc_1(X0_49,X1_49))) != iProver_top
    | v1_funct_1(X0_48) != iProver_top
    | v1_funct_1(sK1) != iProver_top ),
    inference(superposition,[status(thm)],[c_1028,c_1025])).

cnf(c_2982,plain,
    ( v1_funct_1(X0_48) != iProver_top
    | m1_subset_1(X0_48,k1_zfmisc_1(k2_zfmisc_1(X0_49,X1_49))) != iProver_top
    | k1_partfun1(sK0,sK0,X0_49,X1_49,sK1,X0_48) = k5_relat_1(sK1,X0_48) ),
    inference(global_propositional_subsumption,[status(thm)],[c_2785,c_26])).

cnf(c_2983,plain,
    ( k1_partfun1(sK0,sK0,X0_49,X1_49,sK1,X0_48) = k5_relat_1(sK1,X0_48)
    | m1_subset_1(X0_48,k1_zfmisc_1(k2_zfmisc_1(X0_49,X1_49))) != iProver_top
    | v1_funct_1(X0_48) != iProver_top ),
    inference(renaming,[status(thm)],[c_2982])).

cnf(c_2991,plain,
    ( k1_partfun1(sK0,sK0,X0_49,X0_49,sK1,k2_funct_2(X0_49,X0_48)) = k5_relat_1(sK1,k2_funct_2(X0_49,X0_48))
    | v1_funct_2(X0_48,X0_49,X0_49) != iProver_top
    | v3_funct_2(X0_48,X0_49,X0_49) != iProver_top
    | m1_subset_1(X0_48,k1_zfmisc_1(k2_zfmisc_1(X0_49,X0_49))) != iProver_top
    | v1_funct_1(X0_48) != iProver_top
    | v1_funct_1(k2_funct_2(X0_49,X0_48)) != iProver_top ),
    inference(superposition,[status(thm)],[c_1020,c_2983])).

cnf(c_17,plain,
    ( ~ v1_funct_2(X0,X1,X1)
    | ~ v3_funct_2(X0,X1,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X1)))
    | ~ v1_funct_1(X0)
    | v1_funct_1(k2_funct_2(X1,X0)) ),
    inference(cnf_transformation,[],[f60])).

cnf(c_523,plain,
    ( ~ v1_funct_2(X0_48,X0_49,X0_49)
    | ~ v3_funct_2(X0_48,X0_49,X0_49)
    | ~ m1_subset_1(X0_48,k1_zfmisc_1(k2_zfmisc_1(X0_49,X0_49)))
    | ~ v1_funct_1(X0_48)
    | v1_funct_1(k2_funct_2(X0_49,X0_48)) ),
    inference(subtyping,[status(esa)],[c_17])).

cnf(c_612,plain,
    ( v1_funct_2(X0_48,X0_49,X0_49) != iProver_top
    | v3_funct_2(X0_48,X0_49,X0_49) != iProver_top
    | m1_subset_1(X0_48,k1_zfmisc_1(k2_zfmisc_1(X0_49,X0_49))) != iProver_top
    | v1_funct_1(X0_48) != iProver_top
    | v1_funct_1(k2_funct_2(X0_49,X0_48)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_523])).

cnf(c_3285,plain,
    ( v1_funct_1(X0_48) != iProver_top
    | m1_subset_1(X0_48,k1_zfmisc_1(k2_zfmisc_1(X0_49,X0_49))) != iProver_top
    | v3_funct_2(X0_48,X0_49,X0_49) != iProver_top
    | v1_funct_2(X0_48,X0_49,X0_49) != iProver_top
    | k1_partfun1(sK0,sK0,X0_49,X0_49,sK1,k2_funct_2(X0_49,X0_48)) = k5_relat_1(sK1,k2_funct_2(X0_49,X0_48)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_2991,c_612])).

cnf(c_3286,plain,
    ( k1_partfun1(sK0,sK0,X0_49,X0_49,sK1,k2_funct_2(X0_49,X0_48)) = k5_relat_1(sK1,k2_funct_2(X0_49,X0_48))
    | v1_funct_2(X0_48,X0_49,X0_49) != iProver_top
    | v3_funct_2(X0_48,X0_49,X0_49) != iProver_top
    | m1_subset_1(X0_48,k1_zfmisc_1(k2_zfmisc_1(X0_49,X0_49))) != iProver_top
    | v1_funct_1(X0_48) != iProver_top ),
    inference(renaming,[status(thm)],[c_3285])).

cnf(c_3296,plain,
    ( k1_partfun1(sK0,sK0,sK0,sK0,sK1,k2_funct_2(sK0,sK1)) = k5_relat_1(sK1,k2_funct_2(sK0,sK1))
    | v1_funct_2(sK1,sK0,sK0) != iProver_top
    | v3_funct_2(sK1,sK0,sK0) != iProver_top
    | v1_funct_1(sK1) != iProver_top ),
    inference(superposition,[status(thm)],[c_1028,c_3286])).

cnf(c_3336,plain,
    ( k1_partfun1(sK0,sK0,sK0,sK0,sK1,k2_funct_1(sK1)) = k6_partfun1(k1_relat_1(sK1))
    | v1_funct_2(sK1,sK0,sK0) != iProver_top
    | v3_funct_2(sK1,sK0,sK0) != iProver_top
    | v1_funct_1(sK1) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_3296,c_2393,c_2649])).

cnf(c_3204,plain,
    ( k1_partfun1(sK0,sK0,sK0,sK0,sK1,k2_funct_1(sK1)) = k5_relat_1(sK1,k2_funct_1(sK1))
    | v1_funct_1(k2_funct_1(sK1)) != iProver_top ),
    inference(superposition,[status(thm)],[c_3199,c_2983])).

cnf(c_3268,plain,
    ( k1_partfun1(sK0,sK0,sK0,sK0,sK1,k2_funct_1(sK1)) = k6_partfun1(k1_relat_1(sK1))
    | v1_funct_1(k2_funct_1(sK1)) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_3204,c_2649])).

cnf(c_3455,plain,
    ( k1_partfun1(sK0,sK0,sK0,sK0,sK1,k2_funct_1(sK1)) = k6_partfun1(k1_relat_1(sK1)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_3336,c_26,c_29,c_578,c_596,c_3268])).

cnf(c_21,negated_conjecture,
    ( ~ r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK0,sK0,sK0,k2_funct_2(sK0,sK1),sK1),k6_partfun1(sK0))
    | ~ r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK0,sK0,sK0,sK1,k2_funct_2(sK0,sK1)),k6_partfun1(sK0)) ),
    inference(cnf_transformation,[],[f72])).

cnf(c_519,negated_conjecture,
    ( ~ r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK0,sK0,sK0,k2_funct_2(sK0,sK1),sK1),k6_partfun1(sK0))
    | ~ r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK0,sK0,sK0,sK1,k2_funct_2(sK0,sK1)),k6_partfun1(sK0)) ),
    inference(subtyping,[status(esa)],[c_21])).

cnf(c_1027,plain,
    ( r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK0,sK0,sK0,k2_funct_2(sK0,sK1),sK1),k6_partfun1(sK0)) != iProver_top
    | r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK0,sK0,sK0,sK1,k2_funct_2(sK0,sK1)),k6_partfun1(sK0)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_519])).

cnf(c_2397,plain,
    ( r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK0,sK0,sK0,k2_funct_1(sK1),sK1),k6_partfun1(sK0)) != iProver_top
    | r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK0,sK0,sK0,sK1,k2_funct_1(sK1)),k6_partfun1(sK0)) != iProver_top ),
    inference(demodulation,[status(thm)],[c_2393,c_1027])).

cnf(c_3458,plain,
    ( r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK0,sK0,sK0,k2_funct_1(sK1),sK1),k6_partfun1(sK0)) != iProver_top
    | r2_relset_1(sK0,sK0,k6_partfun1(k1_relat_1(sK1)),k6_partfun1(sK0)) != iProver_top ),
    inference(demodulation,[status(thm)],[c_3455,c_2397])).

cnf(c_5500,plain,
    ( r2_relset_1(sK0,sK0,k6_partfun1(k1_relat_1(sK1)),k6_partfun1(sK0)) != iProver_top
    | r2_relset_1(sK0,sK0,k6_partfun1(sK0),k6_partfun1(sK0)) != iProver_top ),
    inference(demodulation,[status(thm)],[c_5497,c_3458])).

cnf(c_561,plain,
    ( sK0 != sK0
    | k6_partfun1(sK0) = k6_partfun1(sK0) ),
    inference(instantiation,[status(thm)],[c_547])).

cnf(c_18,plain,
    ( m1_subset_1(k6_partfun1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0))) ),
    inference(cnf_transformation,[],[f64])).

cnf(c_522,plain,
    ( m1_subset_1(k6_partfun1(X0_49),k1_zfmisc_1(k2_zfmisc_1(X0_49,X0_49))) ),
    inference(subtyping,[status(esa)],[c_18])).

cnf(c_1024,plain,
    ( m1_subset_1(k6_partfun1(X0_49),k1_zfmisc_1(k2_zfmisc_1(X0_49,X0_49))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_522])).

cnf(c_8,plain,
    ( r2_relset_1(X0,X1,X2,X2)
    | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ),
    inference(cnf_transformation,[],[f54])).

cnf(c_528,plain,
    ( r2_relset_1(X0_49,X1_49,X0_48,X0_48)
    | ~ m1_subset_1(X0_48,k1_zfmisc_1(k2_zfmisc_1(X0_49,X1_49)))
    | ~ m1_subset_1(X1_48,k1_zfmisc_1(k2_zfmisc_1(X0_49,X1_49))) ),
    inference(subtyping,[status(esa)],[c_8])).

cnf(c_1018,plain,
    ( r2_relset_1(X0_49,X1_49,X0_48,X0_48) = iProver_top
    | m1_subset_1(X0_48,k1_zfmisc_1(k2_zfmisc_1(X0_49,X1_49))) != iProver_top
    | m1_subset_1(X1_48,k1_zfmisc_1(k2_zfmisc_1(X0_49,X1_49))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_528])).

cnf(c_1594,plain,
    ( r2_relset_1(X0_49,X0_49,k6_partfun1(X0_49),k6_partfun1(X0_49)) = iProver_top
    | m1_subset_1(X0_48,k1_zfmisc_1(k2_zfmisc_1(X0_49,X0_49))) != iProver_top ),
    inference(superposition,[status(thm)],[c_1024,c_1018])).

cnf(c_1605,plain,
    ( r2_relset_1(sK0,sK0,k6_partfun1(sK0),k6_partfun1(sK0)) = iProver_top
    | m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) != iProver_top ),
    inference(instantiation,[status(thm)],[c_1594])).

cnf(c_552,plain,
    ( ~ r2_relset_1(X0_49,X1_49,X0_48,X1_48)
    | r2_relset_1(X2_49,X3_49,X2_48,X3_48)
    | X2_49 != X0_49
    | X3_49 != X1_49
    | X2_48 != X0_48
    | X3_48 != X1_48 ),
    theory(equality)).

cnf(c_2225,plain,
    ( ~ r2_relset_1(X0_49,X1_49,X0_48,X1_48)
    | r2_relset_1(X2_49,X3_49,k1_partfun1(X4_49,X5_49,X6_49,X7_49,k2_funct_1(sK1),X2_48),k6_partfun1(X8_49))
    | X2_49 != X0_49
    | X3_49 != X1_49
    | k1_partfun1(X4_49,X5_49,X6_49,X7_49,k2_funct_1(sK1),X2_48) != X0_48
    | k6_partfun1(X8_49) != X1_48 ),
    inference(instantiation,[status(thm)],[c_552])).

cnf(c_3066,plain,
    ( ~ r2_relset_1(X0_49,X1_49,X0_48,k6_partfun1(X2_49))
    | r2_relset_1(X3_49,X4_49,k1_partfun1(X5_49,X6_49,X7_49,X8_49,k2_funct_1(sK1),X1_48),k6_partfun1(X9_49))
    | X3_49 != X0_49
    | X4_49 != X1_49
    | k1_partfun1(X5_49,X6_49,X7_49,X8_49,k2_funct_1(sK1),X1_48) != X0_48
    | k6_partfun1(X9_49) != k6_partfun1(X2_49) ),
    inference(instantiation,[status(thm)],[c_2225])).

cnf(c_4035,plain,
    ( r2_relset_1(X0_49,X1_49,k1_partfun1(X2_49,X3_49,X4_49,X5_49,k2_funct_1(sK1),X0_48),k6_partfun1(X6_49))
    | ~ r2_relset_1(X7_49,X8_49,k6_partfun1(X9_49),k6_partfun1(X9_49))
    | X0_49 != X7_49
    | X1_49 != X8_49
    | k1_partfun1(X2_49,X3_49,X4_49,X5_49,k2_funct_1(sK1),X0_48) != k6_partfun1(X9_49)
    | k6_partfun1(X6_49) != k6_partfun1(X9_49) ),
    inference(instantiation,[status(thm)],[c_3066])).

cnf(c_4037,plain,
    ( X0_49 != X1_49
    | X2_49 != X3_49
    | k1_partfun1(X4_49,X5_49,X6_49,X7_49,k2_funct_1(sK1),X0_48) != k6_partfun1(X8_49)
    | k6_partfun1(X9_49) != k6_partfun1(X8_49)
    | r2_relset_1(X0_49,X2_49,k1_partfun1(X4_49,X5_49,X6_49,X7_49,k2_funct_1(sK1),X0_48),k6_partfun1(X9_49)) = iProver_top
    | r2_relset_1(X1_49,X3_49,k6_partfun1(X8_49),k6_partfun1(X8_49)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_4035])).

cnf(c_4039,plain,
    ( sK0 != sK0
    | k1_partfun1(sK0,sK0,sK0,sK0,k2_funct_1(sK1),sK1) != k6_partfun1(sK0)
    | k6_partfun1(sK0) != k6_partfun1(sK0)
    | r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK0,sK0,sK0,k2_funct_1(sK1),sK1),k6_partfun1(sK0)) = iProver_top
    | r2_relset_1(sK0,sK0,k6_partfun1(sK0),k6_partfun1(sK0)) != iProver_top ),
    inference(instantiation,[status(thm)],[c_4037])).

cnf(c_5962,plain,
    ( r2_relset_1(sK0,sK0,k6_partfun1(k1_relat_1(sK1)),k6_partfun1(sK0)) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_5500,c_25,c_24,c_23,c_22,c_29,c_561,c_573,c_577,c_583,c_595,c_601,c_628,c_1483,c_1605,c_1844,c_2165,c_2407,c_3179,c_3458,c_4039,c_4522])).

cnf(c_6830,plain,
    ( r2_relset_1(sK0,sK0,k6_partfun1(sK0),k6_partfun1(sK0)) != iProver_top ),
    inference(demodulation,[status(thm)],[c_5246,c_5962])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_6830,c_1605,c_29])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : iproveropt_run.sh %d %s
% 0.13/0.34  % Computer   : n016.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 10:12:49 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running in FOF mode
% 3.06/1.00  % SZS status Started for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.06/1.00  
% 3.06/1.00  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 3.06/1.00  
% 3.06/1.00  ------  iProver source info
% 3.06/1.00  
% 3.06/1.00  git: date: 2020-06-30 10:37:57 +0100
% 3.06/1.00  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 3.06/1.00  git: non_committed_changes: false
% 3.06/1.00  git: last_make_outside_of_git: false
% 3.06/1.00  
% 3.06/1.00  ------ 
% 3.06/1.00  
% 3.06/1.00  ------ Input Options
% 3.06/1.00  
% 3.06/1.00  --out_options                           all
% 3.06/1.00  --tptp_safe_out                         true
% 3.06/1.00  --problem_path                          ""
% 3.06/1.00  --include_path                          ""
% 3.06/1.00  --clausifier                            res/vclausify_rel
% 3.06/1.00  --clausifier_options                    --mode clausify
% 3.06/1.00  --stdin                                 false
% 3.06/1.00  --stats_out                             all
% 3.06/1.00  
% 3.06/1.00  ------ General Options
% 3.06/1.00  
% 3.06/1.00  --fof                                   false
% 3.06/1.00  --time_out_real                         305.
% 3.06/1.00  --time_out_virtual                      -1.
% 3.06/1.00  --symbol_type_check                     false
% 3.06/1.00  --clausify_out                          false
% 3.06/1.00  --sig_cnt_out                           false
% 3.06/1.00  --trig_cnt_out                          false
% 3.06/1.00  --trig_cnt_out_tolerance                1.
% 3.06/1.00  --trig_cnt_out_sk_spl                   false
% 3.06/1.00  --abstr_cl_out                          false
% 3.06/1.00  
% 3.06/1.00  ------ Global Options
% 3.06/1.00  
% 3.06/1.00  --schedule                              default
% 3.06/1.00  --add_important_lit                     false
% 3.06/1.00  --prop_solver_per_cl                    1000
% 3.06/1.00  --min_unsat_core                        false
% 3.06/1.00  --soft_assumptions                      false
% 3.06/1.00  --soft_lemma_size                       3
% 3.06/1.00  --prop_impl_unit_size                   0
% 3.06/1.00  --prop_impl_unit                        []
% 3.06/1.00  --share_sel_clauses                     true
% 3.06/1.00  --reset_solvers                         false
% 3.06/1.00  --bc_imp_inh                            [conj_cone]
% 3.06/1.00  --conj_cone_tolerance                   3.
% 3.06/1.00  --extra_neg_conj                        none
% 3.06/1.00  --large_theory_mode                     true
% 3.06/1.00  --prolific_symb_bound                   200
% 3.06/1.00  --lt_threshold                          2000
% 3.06/1.00  --clause_weak_htbl                      true
% 3.06/1.00  --gc_record_bc_elim                     false
% 3.06/1.00  
% 3.06/1.00  ------ Preprocessing Options
% 3.06/1.00  
% 3.06/1.00  --preprocessing_flag                    true
% 3.06/1.00  --time_out_prep_mult                    0.1
% 3.06/1.00  --splitting_mode                        input
% 3.06/1.00  --splitting_grd                         true
% 3.06/1.00  --splitting_cvd                         false
% 3.06/1.00  --splitting_cvd_svl                     false
% 3.06/1.00  --splitting_nvd                         32
% 3.06/1.00  --sub_typing                            true
% 3.06/1.00  --prep_gs_sim                           true
% 3.06/1.00  --prep_unflatten                        true
% 3.06/1.00  --prep_res_sim                          true
% 3.06/1.00  --prep_upred                            true
% 3.06/1.00  --prep_sem_filter                       exhaustive
% 3.06/1.00  --prep_sem_filter_out                   false
% 3.06/1.00  --pred_elim                             true
% 3.06/1.00  --res_sim_input                         true
% 3.06/1.00  --eq_ax_congr_red                       true
% 3.06/1.00  --pure_diseq_elim                       true
% 3.06/1.00  --brand_transform                       false
% 3.06/1.00  --non_eq_to_eq                          false
% 3.06/1.00  --prep_def_merge                        true
% 3.06/1.00  --prep_def_merge_prop_impl              false
% 3.06/1.00  --prep_def_merge_mbd                    true
% 3.06/1.00  --prep_def_merge_tr_red                 false
% 3.06/1.00  --prep_def_merge_tr_cl                  false
% 3.06/1.00  --smt_preprocessing                     true
% 3.06/1.00  --smt_ac_axioms                         fast
% 3.06/1.00  --preprocessed_out                      false
% 3.06/1.00  --preprocessed_stats                    false
% 3.06/1.00  
% 3.06/1.00  ------ Abstraction refinement Options
% 3.06/1.00  
% 3.06/1.00  --abstr_ref                             []
% 3.06/1.00  --abstr_ref_prep                        false
% 3.06/1.00  --abstr_ref_until_sat                   false
% 3.06/1.00  --abstr_ref_sig_restrict                funpre
% 3.06/1.00  --abstr_ref_af_restrict_to_split_sk     false
% 3.06/1.00  --abstr_ref_under                       []
% 3.06/1.00  
% 3.06/1.00  ------ SAT Options
% 3.06/1.00  
% 3.06/1.00  --sat_mode                              false
% 3.06/1.00  --sat_fm_restart_options                ""
% 3.06/1.00  --sat_gr_def                            false
% 3.06/1.00  --sat_epr_types                         true
% 3.06/1.00  --sat_non_cyclic_types                  false
% 3.06/1.00  --sat_finite_models                     false
% 3.06/1.00  --sat_fm_lemmas                         false
% 3.06/1.00  --sat_fm_prep                           false
% 3.06/1.00  --sat_fm_uc_incr                        true
% 3.06/1.00  --sat_out_model                         small
% 3.06/1.00  --sat_out_clauses                       false
% 3.06/1.00  
% 3.06/1.00  ------ QBF Options
% 3.06/1.00  
% 3.06/1.00  --qbf_mode                              false
% 3.06/1.00  --qbf_elim_univ                         false
% 3.06/1.00  --qbf_dom_inst                          none
% 3.06/1.00  --qbf_dom_pre_inst                      false
% 3.06/1.00  --qbf_sk_in                             false
% 3.06/1.00  --qbf_pred_elim                         true
% 3.06/1.00  --qbf_split                             512
% 3.06/1.00  
% 3.06/1.00  ------ BMC1 Options
% 3.06/1.00  
% 3.06/1.00  --bmc1_incremental                      false
% 3.06/1.00  --bmc1_axioms                           reachable_all
% 3.06/1.00  --bmc1_min_bound                        0
% 3.06/1.00  --bmc1_max_bound                        -1
% 3.06/1.00  --bmc1_max_bound_default                -1
% 3.06/1.00  --bmc1_symbol_reachability              true
% 3.06/1.00  --bmc1_property_lemmas                  false
% 3.06/1.00  --bmc1_k_induction                      false
% 3.06/1.00  --bmc1_non_equiv_states                 false
% 3.06/1.00  --bmc1_deadlock                         false
% 3.06/1.00  --bmc1_ucm                              false
% 3.06/1.00  --bmc1_add_unsat_core                   none
% 3.06/1.00  --bmc1_unsat_core_children              false
% 3.06/1.00  --bmc1_unsat_core_extrapolate_axioms    false
% 3.06/1.00  --bmc1_out_stat                         full
% 3.06/1.00  --bmc1_ground_init                      false
% 3.06/1.00  --bmc1_pre_inst_next_state              false
% 3.06/1.00  --bmc1_pre_inst_state                   false
% 3.06/1.00  --bmc1_pre_inst_reach_state             false
% 3.06/1.00  --bmc1_out_unsat_core                   false
% 3.06/1.00  --bmc1_aig_witness_out                  false
% 3.06/1.00  --bmc1_verbose                          false
% 3.06/1.00  --bmc1_dump_clauses_tptp                false
% 3.06/1.00  --bmc1_dump_unsat_core_tptp             false
% 3.06/1.00  --bmc1_dump_file                        -
% 3.06/1.00  --bmc1_ucm_expand_uc_limit              128
% 3.06/1.00  --bmc1_ucm_n_expand_iterations          6
% 3.06/1.00  --bmc1_ucm_extend_mode                  1
% 3.06/1.00  --bmc1_ucm_init_mode                    2
% 3.06/1.00  --bmc1_ucm_cone_mode                    none
% 3.06/1.00  --bmc1_ucm_reduced_relation_type        0
% 3.06/1.00  --bmc1_ucm_relax_model                  4
% 3.06/1.00  --bmc1_ucm_full_tr_after_sat            true
% 3.06/1.00  --bmc1_ucm_expand_neg_assumptions       false
% 3.06/1.00  --bmc1_ucm_layered_model                none
% 3.06/1.00  --bmc1_ucm_max_lemma_size               10
% 3.06/1.00  
% 3.06/1.00  ------ AIG Options
% 3.06/1.00  
% 3.06/1.00  --aig_mode                              false
% 3.06/1.00  
% 3.06/1.00  ------ Instantiation Options
% 3.06/1.00  
% 3.06/1.00  --instantiation_flag                    true
% 3.06/1.00  --inst_sos_flag                         false
% 3.06/1.00  --inst_sos_phase                        true
% 3.06/1.00  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 3.06/1.00  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 3.06/1.00  --inst_lit_sel_side                     num_symb
% 3.06/1.00  --inst_solver_per_active                1400
% 3.06/1.00  --inst_solver_calls_frac                1.
% 3.06/1.00  --inst_passive_queue_type               priority_queues
% 3.06/1.00  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 3.06/1.00  --inst_passive_queues_freq              [25;2]
% 3.06/1.00  --inst_dismatching                      true
% 3.06/1.00  --inst_eager_unprocessed_to_passive     true
% 3.06/1.00  --inst_prop_sim_given                   true
% 3.06/1.00  --inst_prop_sim_new                     false
% 3.06/1.00  --inst_subs_new                         false
% 3.06/1.00  --inst_eq_res_simp                      false
% 3.06/1.00  --inst_subs_given                       false
% 3.06/1.00  --inst_orphan_elimination               true
% 3.06/1.00  --inst_learning_loop_flag               true
% 3.06/1.00  --inst_learning_start                   3000
% 3.06/1.00  --inst_learning_factor                  2
% 3.06/1.00  --inst_start_prop_sim_after_learn       3
% 3.06/1.00  --inst_sel_renew                        solver
% 3.06/1.00  --inst_lit_activity_flag                true
% 3.06/1.00  --inst_restr_to_given                   false
% 3.06/1.00  --inst_activity_threshold               500
% 3.06/1.00  --inst_out_proof                        true
% 3.06/1.00  
% 3.06/1.00  ------ Resolution Options
% 3.06/1.00  
% 3.06/1.00  --resolution_flag                       true
% 3.06/1.00  --res_lit_sel                           adaptive
% 3.06/1.00  --res_lit_sel_side                      none
% 3.06/1.00  --res_ordering                          kbo
% 3.06/1.00  --res_to_prop_solver                    active
% 3.06/1.00  --res_prop_simpl_new                    false
% 3.06/1.00  --res_prop_simpl_given                  true
% 3.06/1.00  --res_passive_queue_type                priority_queues
% 3.06/1.00  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 3.06/1.00  --res_passive_queues_freq               [15;5]
% 3.06/1.00  --res_forward_subs                      full
% 3.06/1.00  --res_backward_subs                     full
% 3.06/1.00  --res_forward_subs_resolution           true
% 3.06/1.00  --res_backward_subs_resolution          true
% 3.06/1.00  --res_orphan_elimination                true
% 3.06/1.00  --res_time_limit                        2.
% 3.06/1.00  --res_out_proof                         true
% 3.06/1.00  
% 3.06/1.00  ------ Superposition Options
% 3.06/1.00  
% 3.06/1.00  --superposition_flag                    true
% 3.06/1.00  --sup_passive_queue_type                priority_queues
% 3.06/1.00  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 3.06/1.00  --sup_passive_queues_freq               [8;1;4]
% 3.06/1.00  --demod_completeness_check              fast
% 3.06/1.00  --demod_use_ground                      true
% 3.06/1.00  --sup_to_prop_solver                    passive
% 3.06/1.00  --sup_prop_simpl_new                    true
% 3.06/1.00  --sup_prop_simpl_given                  true
% 3.06/1.00  --sup_fun_splitting                     false
% 3.06/1.00  --sup_smt_interval                      50000
% 3.06/1.00  
% 3.06/1.00  ------ Superposition Simplification Setup
% 3.06/1.00  
% 3.06/1.00  --sup_indices_passive                   []
% 3.06/1.00  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.06/1.00  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.06/1.00  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.06/1.00  --sup_full_triv                         [TrivRules;PropSubs]
% 3.06/1.00  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.06/1.00  --sup_full_bw                           [BwDemod]
% 3.06/1.00  --sup_immed_triv                        [TrivRules]
% 3.06/1.00  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 3.06/1.00  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.06/1.00  --sup_immed_bw_main                     []
% 3.06/1.00  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 3.06/1.00  --sup_input_triv                        [Unflattening;TrivRules]
% 3.06/1.00  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.06/1.00  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 3.06/1.00  
% 3.06/1.00  ------ Combination Options
% 3.06/1.00  
% 3.06/1.00  --comb_res_mult                         3
% 3.06/1.00  --comb_sup_mult                         2
% 3.06/1.00  --comb_inst_mult                        10
% 3.06/1.00  
% 3.06/1.00  ------ Debug Options
% 3.06/1.00  
% 3.06/1.00  --dbg_backtrace                         false
% 3.06/1.00  --dbg_dump_prop_clauses                 false
% 3.06/1.00  --dbg_dump_prop_clauses_file            -
% 3.06/1.00  --dbg_out_stat                          false
% 3.06/1.00  ------ Parsing...
% 3.06/1.00  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 3.06/1.00  
% 3.06/1.00  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe:1:0s pe:2:0s pe_e  sf_s  rm: 3 0s  sf_e  pe_s  pe_e 
% 3.06/1.00  
% 3.06/1.00  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 3.06/1.00  
% 3.06/1.00  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 3.06/1.00  ------ Proving...
% 3.06/1.00  ------ Problem Properties 
% 3.06/1.00  
% 3.06/1.00  
% 3.06/1.00  clauses                                 22
% 3.06/1.00  conjectures                             5
% 3.06/1.00  EPR                                     3
% 3.06/1.00  Horn                                    22
% 3.06/1.00  unary                                   5
% 3.06/1.00  binary                                  2
% 3.06/1.00  lits                                    73
% 3.06/1.00  lits eq                                 6
% 3.06/1.00  fd_pure                                 0
% 3.06/1.00  fd_pseudo                               0
% 3.06/1.00  fd_cond                                 0
% 3.06/1.00  fd_pseudo_cond                          1
% 3.06/1.00  AC symbols                              0
% 3.06/1.00  
% 3.06/1.00  ------ Schedule dynamic 5 is on 
% 3.06/1.00  
% 3.06/1.00  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" Time Limit: 10.
% 3.06/1.00  
% 3.06/1.00  
% 3.06/1.00  ------ 
% 3.06/1.00  Current options:
% 3.06/1.00  ------ 
% 3.06/1.00  
% 3.06/1.00  ------ Input Options
% 3.06/1.00  
% 3.06/1.00  --out_options                           all
% 3.06/1.00  --tptp_safe_out                         true
% 3.06/1.00  --problem_path                          ""
% 3.06/1.00  --include_path                          ""
% 3.06/1.00  --clausifier                            res/vclausify_rel
% 3.06/1.00  --clausifier_options                    --mode clausify
% 3.06/1.00  --stdin                                 false
% 3.06/1.00  --stats_out                             all
% 3.06/1.00  
% 3.06/1.00  ------ General Options
% 3.06/1.00  
% 3.06/1.00  --fof                                   false
% 3.06/1.00  --time_out_real                         305.
% 3.06/1.00  --time_out_virtual                      -1.
% 3.06/1.00  --symbol_type_check                     false
% 3.06/1.00  --clausify_out                          false
% 3.06/1.00  --sig_cnt_out                           false
% 3.06/1.00  --trig_cnt_out                          false
% 3.06/1.00  --trig_cnt_out_tolerance                1.
% 3.06/1.00  --trig_cnt_out_sk_spl                   false
% 3.06/1.00  --abstr_cl_out                          false
% 3.06/1.00  
% 3.06/1.00  ------ Global Options
% 3.06/1.00  
% 3.06/1.00  --schedule                              default
% 3.06/1.00  --add_important_lit                     false
% 3.06/1.00  --prop_solver_per_cl                    1000
% 3.06/1.00  --min_unsat_core                        false
% 3.06/1.00  --soft_assumptions                      false
% 3.06/1.00  --soft_lemma_size                       3
% 3.06/1.00  --prop_impl_unit_size                   0
% 3.06/1.00  --prop_impl_unit                        []
% 3.06/1.00  --share_sel_clauses                     true
% 3.06/1.00  --reset_solvers                         false
% 3.06/1.00  --bc_imp_inh                            [conj_cone]
% 3.06/1.00  --conj_cone_tolerance                   3.
% 3.06/1.00  --extra_neg_conj                        none
% 3.06/1.00  --large_theory_mode                     true
% 3.06/1.00  --prolific_symb_bound                   200
% 3.06/1.00  --lt_threshold                          2000
% 3.06/1.00  --clause_weak_htbl                      true
% 3.06/1.00  --gc_record_bc_elim                     false
% 3.06/1.00  
% 3.06/1.00  ------ Preprocessing Options
% 3.06/1.00  
% 3.06/1.00  --preprocessing_flag                    true
% 3.06/1.00  --time_out_prep_mult                    0.1
% 3.06/1.00  --splitting_mode                        input
% 3.06/1.00  --splitting_grd                         true
% 3.06/1.00  --splitting_cvd                         false
% 3.06/1.00  --splitting_cvd_svl                     false
% 3.06/1.00  --splitting_nvd                         32
% 3.06/1.00  --sub_typing                            true
% 3.06/1.00  --prep_gs_sim                           true
% 3.06/1.00  --prep_unflatten                        true
% 3.06/1.00  --prep_res_sim                          true
% 3.06/1.00  --prep_upred                            true
% 3.06/1.00  --prep_sem_filter                       exhaustive
% 3.06/1.00  --prep_sem_filter_out                   false
% 3.06/1.00  --pred_elim                             true
% 3.06/1.00  --res_sim_input                         true
% 3.06/1.00  --eq_ax_congr_red                       true
% 3.06/1.00  --pure_diseq_elim                       true
% 3.06/1.00  --brand_transform                       false
% 3.06/1.00  --non_eq_to_eq                          false
% 3.06/1.00  --prep_def_merge                        true
% 3.06/1.00  --prep_def_merge_prop_impl              false
% 3.06/1.00  --prep_def_merge_mbd                    true
% 3.06/1.00  --prep_def_merge_tr_red                 false
% 3.06/1.00  --prep_def_merge_tr_cl                  false
% 3.06/1.00  --smt_preprocessing                     true
% 3.06/1.00  --smt_ac_axioms                         fast
% 3.06/1.00  --preprocessed_out                      false
% 3.06/1.00  --preprocessed_stats                    false
% 3.06/1.00  
% 3.06/1.00  ------ Abstraction refinement Options
% 3.06/1.00  
% 3.06/1.00  --abstr_ref                             []
% 3.06/1.00  --abstr_ref_prep                        false
% 3.06/1.00  --abstr_ref_until_sat                   false
% 3.06/1.00  --abstr_ref_sig_restrict                funpre
% 3.06/1.00  --abstr_ref_af_restrict_to_split_sk     false
% 3.06/1.00  --abstr_ref_under                       []
% 3.06/1.00  
% 3.06/1.00  ------ SAT Options
% 3.06/1.00  
% 3.06/1.00  --sat_mode                              false
% 3.06/1.00  --sat_fm_restart_options                ""
% 3.06/1.00  --sat_gr_def                            false
% 3.06/1.00  --sat_epr_types                         true
% 3.06/1.00  --sat_non_cyclic_types                  false
% 3.06/1.00  --sat_finite_models                     false
% 3.06/1.00  --sat_fm_lemmas                         false
% 3.06/1.00  --sat_fm_prep                           false
% 3.06/1.00  --sat_fm_uc_incr                        true
% 3.06/1.00  --sat_out_model                         small
% 3.06/1.00  --sat_out_clauses                       false
% 3.06/1.00  
% 3.06/1.00  ------ QBF Options
% 3.06/1.00  
% 3.06/1.00  --qbf_mode                              false
% 3.06/1.00  --qbf_elim_univ                         false
% 3.06/1.00  --qbf_dom_inst                          none
% 3.06/1.00  --qbf_dom_pre_inst                      false
% 3.06/1.00  --qbf_sk_in                             false
% 3.06/1.00  --qbf_pred_elim                         true
% 3.06/1.00  --qbf_split                             512
% 3.06/1.00  
% 3.06/1.00  ------ BMC1 Options
% 3.06/1.00  
% 3.06/1.00  --bmc1_incremental                      false
% 3.06/1.00  --bmc1_axioms                           reachable_all
% 3.06/1.00  --bmc1_min_bound                        0
% 3.06/1.00  --bmc1_max_bound                        -1
% 3.06/1.00  --bmc1_max_bound_default                -1
% 3.06/1.00  --bmc1_symbol_reachability              true
% 3.06/1.00  --bmc1_property_lemmas                  false
% 3.06/1.00  --bmc1_k_induction                      false
% 3.06/1.00  --bmc1_non_equiv_states                 false
% 3.06/1.00  --bmc1_deadlock                         false
% 3.06/1.00  --bmc1_ucm                              false
% 3.06/1.00  --bmc1_add_unsat_core                   none
% 3.06/1.00  --bmc1_unsat_core_children              false
% 3.06/1.00  --bmc1_unsat_core_extrapolate_axioms    false
% 3.06/1.00  --bmc1_out_stat                         full
% 3.06/1.00  --bmc1_ground_init                      false
% 3.06/1.00  --bmc1_pre_inst_next_state              false
% 3.06/1.00  --bmc1_pre_inst_state                   false
% 3.06/1.00  --bmc1_pre_inst_reach_state             false
% 3.06/1.00  --bmc1_out_unsat_core                   false
% 3.06/1.00  --bmc1_aig_witness_out                  false
% 3.06/1.00  --bmc1_verbose                          false
% 3.06/1.00  --bmc1_dump_clauses_tptp                false
% 3.06/1.00  --bmc1_dump_unsat_core_tptp             false
% 3.06/1.00  --bmc1_dump_file                        -
% 3.06/1.00  --bmc1_ucm_expand_uc_limit              128
% 3.06/1.00  --bmc1_ucm_n_expand_iterations          6
% 3.06/1.00  --bmc1_ucm_extend_mode                  1
% 3.06/1.00  --bmc1_ucm_init_mode                    2
% 3.06/1.00  --bmc1_ucm_cone_mode                    none
% 3.06/1.00  --bmc1_ucm_reduced_relation_type        0
% 3.06/1.00  --bmc1_ucm_relax_model                  4
% 3.06/1.00  --bmc1_ucm_full_tr_after_sat            true
% 3.06/1.00  --bmc1_ucm_expand_neg_assumptions       false
% 3.06/1.00  --bmc1_ucm_layered_model                none
% 3.06/1.00  --bmc1_ucm_max_lemma_size               10
% 3.06/1.00  
% 3.06/1.00  ------ AIG Options
% 3.06/1.00  
% 3.06/1.00  --aig_mode                              false
% 3.06/1.00  
% 3.06/1.00  ------ Instantiation Options
% 3.06/1.00  
% 3.06/1.00  --instantiation_flag                    true
% 3.06/1.00  --inst_sos_flag                         false
% 3.06/1.00  --inst_sos_phase                        true
% 3.06/1.00  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 3.06/1.00  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 3.06/1.00  --inst_lit_sel_side                     none
% 3.06/1.00  --inst_solver_per_active                1400
% 3.06/1.00  --inst_solver_calls_frac                1.
% 3.06/1.00  --inst_passive_queue_type               priority_queues
% 3.06/1.00  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 3.06/1.00  --inst_passive_queues_freq              [25;2]
% 3.06/1.00  --inst_dismatching                      true
% 3.06/1.00  --inst_eager_unprocessed_to_passive     true
% 3.06/1.00  --inst_prop_sim_given                   true
% 3.06/1.00  --inst_prop_sim_new                     false
% 3.06/1.00  --inst_subs_new                         false
% 3.06/1.00  --inst_eq_res_simp                      false
% 3.06/1.00  --inst_subs_given                       false
% 3.06/1.00  --inst_orphan_elimination               true
% 3.06/1.00  --inst_learning_loop_flag               true
% 3.06/1.00  --inst_learning_start                   3000
% 3.06/1.00  --inst_learning_factor                  2
% 3.06/1.00  --inst_start_prop_sim_after_learn       3
% 3.06/1.00  --inst_sel_renew                        solver
% 3.06/1.00  --inst_lit_activity_flag                true
% 3.06/1.00  --inst_restr_to_given                   false
% 3.06/1.00  --inst_activity_threshold               500
% 3.06/1.00  --inst_out_proof                        true
% 3.06/1.00  
% 3.06/1.00  ------ Resolution Options
% 3.06/1.00  
% 3.06/1.00  --resolution_flag                       false
% 3.06/1.00  --res_lit_sel                           adaptive
% 3.06/1.00  --res_lit_sel_side                      none
% 3.06/1.00  --res_ordering                          kbo
% 3.06/1.00  --res_to_prop_solver                    active
% 3.06/1.00  --res_prop_simpl_new                    false
% 3.06/1.00  --res_prop_simpl_given                  true
% 3.06/1.00  --res_passive_queue_type                priority_queues
% 3.06/1.00  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 3.06/1.00  --res_passive_queues_freq               [15;5]
% 3.06/1.00  --res_forward_subs                      full
% 3.06/1.00  --res_backward_subs                     full
% 3.06/1.00  --res_forward_subs_resolution           true
% 3.06/1.00  --res_backward_subs_resolution          true
% 3.06/1.00  --res_orphan_elimination                true
% 3.06/1.00  --res_time_limit                        2.
% 3.06/1.00  --res_out_proof                         true
% 3.06/1.00  
% 3.06/1.00  ------ Superposition Options
% 3.06/1.00  
% 3.06/1.00  --superposition_flag                    true
% 3.06/1.00  --sup_passive_queue_type                priority_queues
% 3.06/1.00  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 3.06/1.00  --sup_passive_queues_freq               [8;1;4]
% 3.06/1.00  --demod_completeness_check              fast
% 3.06/1.00  --demod_use_ground                      true
% 3.06/1.00  --sup_to_prop_solver                    passive
% 3.06/1.00  --sup_prop_simpl_new                    true
% 3.06/1.00  --sup_prop_simpl_given                  true
% 3.06/1.00  --sup_fun_splitting                     false
% 3.06/1.00  --sup_smt_interval                      50000
% 3.06/1.00  
% 3.06/1.00  ------ Superposition Simplification Setup
% 3.06/1.00  
% 3.06/1.00  --sup_indices_passive                   []
% 3.06/1.00  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.06/1.00  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.06/1.00  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.06/1.00  --sup_full_triv                         [TrivRules;PropSubs]
% 3.06/1.00  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.06/1.00  --sup_full_bw                           [BwDemod]
% 3.06/1.00  --sup_immed_triv                        [TrivRules]
% 3.06/1.00  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 3.06/1.00  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.06/1.00  --sup_immed_bw_main                     []
% 3.06/1.00  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 3.06/1.00  --sup_input_triv                        [Unflattening;TrivRules]
% 3.06/1.00  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.06/1.00  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 3.06/1.00  
% 3.06/1.00  ------ Combination Options
% 3.06/1.00  
% 3.06/1.00  --comb_res_mult                         3
% 3.06/1.00  --comb_sup_mult                         2
% 3.06/1.00  --comb_inst_mult                        10
% 3.06/1.00  
% 3.06/1.00  ------ Debug Options
% 3.06/1.00  
% 3.06/1.00  --dbg_backtrace                         false
% 3.06/1.00  --dbg_dump_prop_clauses                 false
% 3.06/1.00  --dbg_dump_prop_clauses_file            -
% 3.06/1.00  --dbg_out_stat                          false
% 3.06/1.00  
% 3.06/1.00  
% 3.06/1.00  
% 3.06/1.00  
% 3.06/1.00  ------ Proving...
% 3.06/1.00  
% 3.06/1.00  
% 3.06/1.00  % SZS status Theorem for theBenchmark.p
% 3.06/1.00  
% 3.06/1.00  % SZS output start CNFRefutation for theBenchmark.p
% 3.06/1.00  
% 3.06/1.00  fof(f15,conjecture,(
% 3.06/1.00    ! [X0,X1] : ((m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v3_funct_2(X1,X0,X0) & v1_funct_2(X1,X0,X0) & v1_funct_1(X1)) => (r2_relset_1(X0,X0,k1_partfun1(X0,X0,X0,X0,k2_funct_2(X0,X1),X1),k6_partfun1(X0)) & r2_relset_1(X0,X0,k1_partfun1(X0,X0,X0,X0,X1,k2_funct_2(X0,X1)),k6_partfun1(X0))))),
% 3.06/1.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.06/1.00  
% 3.06/1.00  fof(f16,negated_conjecture,(
% 3.06/1.00    ~! [X0,X1] : ((m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v3_funct_2(X1,X0,X0) & v1_funct_2(X1,X0,X0) & v1_funct_1(X1)) => (r2_relset_1(X0,X0,k1_partfun1(X0,X0,X0,X0,k2_funct_2(X0,X1),X1),k6_partfun1(X0)) & r2_relset_1(X0,X0,k1_partfun1(X0,X0,X0,X0,X1,k2_funct_2(X0,X1)),k6_partfun1(X0))))),
% 3.06/1.00    inference(negated_conjecture,[],[f15])).
% 3.06/1.00  
% 3.06/1.00  fof(f41,plain,(
% 3.06/1.00    ? [X0,X1] : ((~r2_relset_1(X0,X0,k1_partfun1(X0,X0,X0,X0,k2_funct_2(X0,X1),X1),k6_partfun1(X0)) | ~r2_relset_1(X0,X0,k1_partfun1(X0,X0,X0,X0,X1,k2_funct_2(X0,X1)),k6_partfun1(X0))) & (m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v3_funct_2(X1,X0,X0) & v1_funct_2(X1,X0,X0) & v1_funct_1(X1)))),
% 3.06/1.00    inference(ennf_transformation,[],[f16])).
% 3.06/1.00  
% 3.06/1.00  fof(f42,plain,(
% 3.06/1.00    ? [X0,X1] : ((~r2_relset_1(X0,X0,k1_partfun1(X0,X0,X0,X0,k2_funct_2(X0,X1),X1),k6_partfun1(X0)) | ~r2_relset_1(X0,X0,k1_partfun1(X0,X0,X0,X0,X1,k2_funct_2(X0,X1)),k6_partfun1(X0))) & m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v3_funct_2(X1,X0,X0) & v1_funct_2(X1,X0,X0) & v1_funct_1(X1))),
% 3.06/1.00    inference(flattening,[],[f41])).
% 3.06/1.00  
% 3.06/1.00  fof(f44,plain,(
% 3.06/1.00    ? [X0,X1] : ((~r2_relset_1(X0,X0,k1_partfun1(X0,X0,X0,X0,k2_funct_2(X0,X1),X1),k6_partfun1(X0)) | ~r2_relset_1(X0,X0,k1_partfun1(X0,X0,X0,X0,X1,k2_funct_2(X0,X1)),k6_partfun1(X0))) & m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v3_funct_2(X1,X0,X0) & v1_funct_2(X1,X0,X0) & v1_funct_1(X1)) => ((~r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK0,sK0,sK0,k2_funct_2(sK0,sK1),sK1),k6_partfun1(sK0)) | ~r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK0,sK0,sK0,sK1,k2_funct_2(sK0,sK1)),k6_partfun1(sK0))) & m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) & v3_funct_2(sK1,sK0,sK0) & v1_funct_2(sK1,sK0,sK0) & v1_funct_1(sK1))),
% 3.06/1.00    introduced(choice_axiom,[])).
% 3.06/1.00  
% 3.06/1.00  fof(f45,plain,(
% 3.06/1.00    (~r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK0,sK0,sK0,k2_funct_2(sK0,sK1),sK1),k6_partfun1(sK0)) | ~r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK0,sK0,sK0,sK1,k2_funct_2(sK0,sK1)),k6_partfun1(sK0))) & m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) & v3_funct_2(sK1,sK0,sK0) & v1_funct_2(sK1,sK0,sK0) & v1_funct_1(sK1)),
% 3.06/1.00    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f42,f44])).
% 3.06/1.00  
% 3.06/1.00  fof(f71,plain,(
% 3.06/1.00    m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))),
% 3.06/1.00    inference(cnf_transformation,[],[f45])).
% 3.06/1.00  
% 3.06/1.00  fof(f13,axiom,(
% 3.06/1.00    ! [X0,X1] : ((m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v3_funct_2(X1,X0,X0) & v1_funct_2(X1,X0,X0) & v1_funct_1(X1)) => k2_funct_1(X1) = k2_funct_2(X0,X1))),
% 3.06/1.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.06/1.00  
% 3.06/1.00  fof(f39,plain,(
% 3.06/1.00    ! [X0,X1] : (k2_funct_1(X1) = k2_funct_2(X0,X1) | (~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) | ~v3_funct_2(X1,X0,X0) | ~v1_funct_2(X1,X0,X0) | ~v1_funct_1(X1)))),
% 3.06/1.00    inference(ennf_transformation,[],[f13])).
% 3.06/1.00  
% 3.06/1.00  fof(f40,plain,(
% 3.06/1.00    ! [X0,X1] : (k2_funct_1(X1) = k2_funct_2(X0,X1) | ~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) | ~v3_funct_2(X1,X0,X0) | ~v1_funct_2(X1,X0,X0) | ~v1_funct_1(X1))),
% 3.06/1.00    inference(flattening,[],[f39])).
% 3.06/1.00  
% 3.06/1.00  fof(f66,plain,(
% 3.06/1.00    ( ! [X0,X1] : (k2_funct_1(X1) = k2_funct_2(X0,X1) | ~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) | ~v3_funct_2(X1,X0,X0) | ~v1_funct_2(X1,X0,X0) | ~v1_funct_1(X1)) )),
% 3.06/1.00    inference(cnf_transformation,[],[f40])).
% 3.06/1.00  
% 3.06/1.00  fof(f68,plain,(
% 3.06/1.00    v1_funct_1(sK1)),
% 3.06/1.00    inference(cnf_transformation,[],[f45])).
% 3.06/1.00  
% 3.06/1.00  fof(f69,plain,(
% 3.06/1.00    v1_funct_2(sK1,sK0,sK0)),
% 3.06/1.00    inference(cnf_transformation,[],[f45])).
% 3.06/1.00  
% 3.06/1.00  fof(f70,plain,(
% 3.06/1.00    v3_funct_2(sK1,sK0,sK0)),
% 3.06/1.00    inference(cnf_transformation,[],[f45])).
% 3.06/1.00  
% 3.06/1.00  fof(f10,axiom,(
% 3.06/1.00    ! [X0,X1] : ((m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v3_funct_2(X1,X0,X0) & v1_funct_2(X1,X0,X0) & v1_funct_1(X1)) => (m1_subset_1(k2_funct_2(X0,X1),k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v3_funct_2(k2_funct_2(X0,X1),X0,X0) & v1_funct_2(k2_funct_2(X0,X1),X0,X0) & v1_funct_1(k2_funct_2(X0,X1))))),
% 3.06/1.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.06/1.00  
% 3.06/1.00  fof(f35,plain,(
% 3.06/1.00    ! [X0,X1] : ((m1_subset_1(k2_funct_2(X0,X1),k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v3_funct_2(k2_funct_2(X0,X1),X0,X0) & v1_funct_2(k2_funct_2(X0,X1),X0,X0) & v1_funct_1(k2_funct_2(X0,X1))) | (~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) | ~v3_funct_2(X1,X0,X0) | ~v1_funct_2(X1,X0,X0) | ~v1_funct_1(X1)))),
% 3.06/1.00    inference(ennf_transformation,[],[f10])).
% 3.06/1.00  
% 3.06/1.00  fof(f36,plain,(
% 3.06/1.00    ! [X0,X1] : ((m1_subset_1(k2_funct_2(X0,X1),k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v3_funct_2(k2_funct_2(X0,X1),X0,X0) & v1_funct_2(k2_funct_2(X0,X1),X0,X0) & v1_funct_1(k2_funct_2(X0,X1))) | ~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) | ~v3_funct_2(X1,X0,X0) | ~v1_funct_2(X1,X0,X0) | ~v1_funct_1(X1))),
% 3.06/1.00    inference(flattening,[],[f35])).
% 3.06/1.00  
% 3.06/1.00  fof(f63,plain,(
% 3.06/1.00    ( ! [X0,X1] : (m1_subset_1(k2_funct_2(X0,X1),k1_zfmisc_1(k2_zfmisc_1(X0,X0))) | ~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) | ~v3_funct_2(X1,X0,X0) | ~v1_funct_2(X1,X0,X0) | ~v1_funct_1(X1)) )),
% 3.06/1.00    inference(cnf_transformation,[],[f36])).
% 3.06/1.00  
% 3.06/1.00  fof(f8,axiom,(
% 3.06/1.00    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => ((v3_funct_2(X2,X0,X1) & v1_funct_1(X2)) => (v2_funct_2(X2,X1) & v2_funct_1(X2) & v1_funct_1(X2))))),
% 3.06/1.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.06/1.00  
% 3.06/1.00  fof(f31,plain,(
% 3.06/1.00    ! [X0,X1,X2] : (((v2_funct_2(X2,X1) & v2_funct_1(X2) & v1_funct_1(X2)) | (~v3_funct_2(X2,X0,X1) | ~v1_funct_1(X2))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 3.06/1.00    inference(ennf_transformation,[],[f8])).
% 3.06/1.00  
% 3.06/1.00  fof(f32,plain,(
% 3.06/1.00    ! [X0,X1,X2] : ((v2_funct_2(X2,X1) & v2_funct_1(X2) & v1_funct_1(X2)) | ~v3_funct_2(X2,X0,X1) | ~v1_funct_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 3.06/1.00    inference(flattening,[],[f31])).
% 3.06/1.00  
% 3.06/1.00  fof(f57,plain,(
% 3.06/1.00    ( ! [X2,X0,X1] : (v2_funct_2(X2,X1) | ~v3_funct_2(X2,X0,X1) | ~v1_funct_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 3.06/1.00    inference(cnf_transformation,[],[f32])).
% 3.06/1.00  
% 3.06/1.00  fof(f6,axiom,(
% 3.06/1.00    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => (v5_relat_1(X2,X1) & v4_relat_1(X2,X0)))),
% 3.06/1.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.06/1.00  
% 3.06/1.00  fof(f18,plain,(
% 3.06/1.00    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => v5_relat_1(X2,X1))),
% 3.06/1.00    inference(pure_predicate_removal,[],[f6])).
% 3.06/1.00  
% 3.06/1.00  fof(f28,plain,(
% 3.06/1.00    ! [X0,X1,X2] : (v5_relat_1(X2,X1) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 3.06/1.00    inference(ennf_transformation,[],[f18])).
% 3.06/1.00  
% 3.06/1.00  fof(f53,plain,(
% 3.06/1.00    ( ! [X2,X0,X1] : (v5_relat_1(X2,X1) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 3.06/1.00    inference(cnf_transformation,[],[f28])).
% 3.06/1.00  
% 3.06/1.00  fof(f9,axiom,(
% 3.06/1.00    ! [X0,X1] : ((v5_relat_1(X1,X0) & v1_relat_1(X1)) => (v2_funct_2(X1,X0) <=> k2_relat_1(X1) = X0))),
% 3.06/1.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.06/1.00  
% 3.06/1.00  fof(f33,plain,(
% 3.06/1.00    ! [X0,X1] : ((v2_funct_2(X1,X0) <=> k2_relat_1(X1) = X0) | (~v5_relat_1(X1,X0) | ~v1_relat_1(X1)))),
% 3.06/1.00    inference(ennf_transformation,[],[f9])).
% 3.06/1.00  
% 3.06/1.00  fof(f34,plain,(
% 3.06/1.00    ! [X0,X1] : ((v2_funct_2(X1,X0) <=> k2_relat_1(X1) = X0) | ~v5_relat_1(X1,X0) | ~v1_relat_1(X1))),
% 3.06/1.00    inference(flattening,[],[f33])).
% 3.06/1.00  
% 3.06/1.00  fof(f43,plain,(
% 3.06/1.00    ! [X0,X1] : (((v2_funct_2(X1,X0) | k2_relat_1(X1) != X0) & (k2_relat_1(X1) = X0 | ~v2_funct_2(X1,X0))) | ~v5_relat_1(X1,X0) | ~v1_relat_1(X1))),
% 3.06/1.00    inference(nnf_transformation,[],[f34])).
% 3.06/1.00  
% 3.06/1.00  fof(f58,plain,(
% 3.06/1.00    ( ! [X0,X1] : (k2_relat_1(X1) = X0 | ~v2_funct_2(X1,X0) | ~v5_relat_1(X1,X0) | ~v1_relat_1(X1)) )),
% 3.06/1.00    inference(cnf_transformation,[],[f43])).
% 3.06/1.00  
% 3.06/1.00  fof(f5,axiom,(
% 3.06/1.00    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => v1_relat_1(X2))),
% 3.06/1.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.06/1.00  
% 3.06/1.00  fof(f27,plain,(
% 3.06/1.00    ! [X0,X1,X2] : (v1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 3.06/1.00    inference(ennf_transformation,[],[f5])).
% 3.06/1.00  
% 3.06/1.00  fof(f52,plain,(
% 3.06/1.00    ( ! [X2,X0,X1] : (v1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 3.06/1.00    inference(cnf_transformation,[],[f27])).
% 3.06/1.00  
% 3.06/1.00  fof(f1,axiom,(
% 3.06/1.00    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => (v1_funct_1(k2_funct_1(X0)) & v1_relat_1(k2_funct_1(X0))))),
% 3.06/1.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.06/1.00  
% 3.06/1.00  fof(f19,plain,(
% 3.06/1.00    ! [X0] : ((v1_funct_1(k2_funct_1(X0)) & v1_relat_1(k2_funct_1(X0))) | (~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 3.06/1.00    inference(ennf_transformation,[],[f1])).
% 3.06/1.00  
% 3.06/1.00  fof(f20,plain,(
% 3.06/1.00    ! [X0] : ((v1_funct_1(k2_funct_1(X0)) & v1_relat_1(k2_funct_1(X0))) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 3.06/1.00    inference(flattening,[],[f19])).
% 3.06/1.00  
% 3.06/1.00  fof(f47,plain,(
% 3.06/1.00    ( ! [X0] : (v1_funct_1(k2_funct_1(X0)) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 3.06/1.00    inference(cnf_transformation,[],[f20])).
% 3.06/1.00  
% 3.06/1.00  fof(f62,plain,(
% 3.06/1.00    ( ! [X0,X1] : (v3_funct_2(k2_funct_2(X0,X1),X0,X0) | ~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) | ~v3_funct_2(X1,X0,X0) | ~v1_funct_2(X1,X0,X0) | ~v1_funct_1(X1)) )),
% 3.06/1.00    inference(cnf_transformation,[],[f36])).
% 3.06/1.00  
% 3.06/1.00  fof(f56,plain,(
% 3.06/1.00    ( ! [X2,X0,X1] : (v2_funct_1(X2) | ~v3_funct_2(X2,X0,X1) | ~v1_funct_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 3.06/1.00    inference(cnf_transformation,[],[f32])).
% 3.06/1.00  
% 3.06/1.00  fof(f3,axiom,(
% 3.06/1.00    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => (v2_funct_1(X0) => v2_funct_1(k2_funct_1(X0))))),
% 3.06/1.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.06/1.00  
% 3.06/1.00  fof(f23,plain,(
% 3.06/1.00    ! [X0] : ((v2_funct_1(k2_funct_1(X0)) | ~v2_funct_1(X0)) | (~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 3.06/1.00    inference(ennf_transformation,[],[f3])).
% 3.06/1.00  
% 3.06/1.00  fof(f24,plain,(
% 3.06/1.00    ! [X0] : (v2_funct_1(k2_funct_1(X0)) | ~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 3.06/1.00    inference(flattening,[],[f23])).
% 3.06/1.00  
% 3.06/1.00  fof(f50,plain,(
% 3.06/1.00    ( ! [X0] : (v2_funct_1(k2_funct_1(X0)) | ~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 3.06/1.00    inference(cnf_transformation,[],[f24])).
% 3.06/1.00  
% 3.06/1.00  fof(f2,axiom,(
% 3.06/1.00    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => (v2_funct_1(X0) => (k5_relat_1(k2_funct_1(X0),X0) = k6_relat_1(k2_relat_1(X0)) & k5_relat_1(X0,k2_funct_1(X0)) = k6_relat_1(k1_relat_1(X0)))))),
% 3.06/1.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.06/1.00  
% 3.06/1.00  fof(f21,plain,(
% 3.06/1.00    ! [X0] : (((k5_relat_1(k2_funct_1(X0),X0) = k6_relat_1(k2_relat_1(X0)) & k5_relat_1(X0,k2_funct_1(X0)) = k6_relat_1(k1_relat_1(X0))) | ~v2_funct_1(X0)) | (~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 3.06/1.00    inference(ennf_transformation,[],[f2])).
% 3.06/1.00  
% 3.06/1.00  fof(f22,plain,(
% 3.06/1.00    ! [X0] : ((k5_relat_1(k2_funct_1(X0),X0) = k6_relat_1(k2_relat_1(X0)) & k5_relat_1(X0,k2_funct_1(X0)) = k6_relat_1(k1_relat_1(X0))) | ~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 3.06/1.00    inference(flattening,[],[f21])).
% 3.06/1.00  
% 3.06/1.00  fof(f49,plain,(
% 3.06/1.00    ( ! [X0] : (k5_relat_1(k2_funct_1(X0),X0) = k6_relat_1(k2_relat_1(X0)) | ~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 3.06/1.00    inference(cnf_transformation,[],[f22])).
% 3.06/1.00  
% 3.06/1.00  fof(f14,axiom,(
% 3.06/1.00    ! [X0] : k6_relat_1(X0) = k6_partfun1(X0)),
% 3.06/1.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.06/1.00  
% 3.06/1.00  fof(f67,plain,(
% 3.06/1.00    ( ! [X0] : (k6_relat_1(X0) = k6_partfun1(X0)) )),
% 3.06/1.00    inference(cnf_transformation,[],[f14])).
% 3.06/1.00  
% 3.06/1.00  fof(f73,plain,(
% 3.06/1.00    ( ! [X0] : (k5_relat_1(k2_funct_1(X0),X0) = k6_partfun1(k2_relat_1(X0)) | ~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 3.06/1.00    inference(definition_unfolding,[],[f49,f67])).
% 3.06/1.00  
% 3.06/1.00  fof(f4,axiom,(
% 3.06/1.00    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => (v2_funct_1(X0) => k2_funct_1(k2_funct_1(X0)) = X0))),
% 3.06/1.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.06/1.00  
% 3.06/1.00  fof(f25,plain,(
% 3.06/1.00    ! [X0] : ((k2_funct_1(k2_funct_1(X0)) = X0 | ~v2_funct_1(X0)) | (~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 3.06/1.00    inference(ennf_transformation,[],[f4])).
% 3.06/1.00  
% 3.06/1.00  fof(f26,plain,(
% 3.06/1.00    ! [X0] : (k2_funct_1(k2_funct_1(X0)) = X0 | ~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 3.06/1.00    inference(flattening,[],[f25])).
% 3.06/1.00  
% 3.06/1.00  fof(f51,plain,(
% 3.06/1.00    ( ! [X0] : (k2_funct_1(k2_funct_1(X0)) = X0 | ~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 3.06/1.00    inference(cnf_transformation,[],[f26])).
% 3.06/1.00  
% 3.06/1.00  fof(f48,plain,(
% 3.06/1.00    ( ! [X0] : (k5_relat_1(X0,k2_funct_1(X0)) = k6_relat_1(k1_relat_1(X0)) | ~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 3.06/1.00    inference(cnf_transformation,[],[f22])).
% 3.06/1.00  
% 3.06/1.00  fof(f74,plain,(
% 3.06/1.00    ( ! [X0] : (k5_relat_1(X0,k2_funct_1(X0)) = k6_partfun1(k1_relat_1(X0)) | ~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 3.06/1.00    inference(definition_unfolding,[],[f48,f67])).
% 3.06/1.00  
% 3.06/1.00  fof(f46,plain,(
% 3.06/1.00    ( ! [X0] : (v1_relat_1(k2_funct_1(X0)) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 3.06/1.00    inference(cnf_transformation,[],[f20])).
% 3.06/1.00  
% 3.06/1.00  fof(f12,axiom,(
% 3.06/1.00    ! [X0,X1,X2,X3,X4,X5] : ((m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) & v1_funct_1(X5) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_1(X4)) => k5_relat_1(X4,X5) = k1_partfun1(X0,X1,X2,X3,X4,X5))),
% 3.06/1.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.06/1.00  
% 3.06/1.00  fof(f37,plain,(
% 3.06/1.00    ! [X0,X1,X2,X3,X4,X5] : (k5_relat_1(X4,X5) = k1_partfun1(X0,X1,X2,X3,X4,X5) | (~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X4)))),
% 3.06/1.00    inference(ennf_transformation,[],[f12])).
% 3.06/1.00  
% 3.06/1.00  fof(f38,plain,(
% 3.06/1.00    ! [X0,X1,X2,X3,X4,X5] : (k5_relat_1(X4,X5) = k1_partfun1(X0,X1,X2,X3,X4,X5) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X4))),
% 3.06/1.00    inference(flattening,[],[f37])).
% 3.06/1.00  
% 3.06/1.00  fof(f65,plain,(
% 3.06/1.00    ( ! [X4,X2,X0,X5,X3,X1] : (k5_relat_1(X4,X5) = k1_partfun1(X0,X1,X2,X3,X4,X5) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X4)) )),
% 3.06/1.00    inference(cnf_transformation,[],[f38])).
% 3.06/1.00  
% 3.06/1.00  fof(f60,plain,(
% 3.06/1.00    ( ! [X0,X1] : (v1_funct_1(k2_funct_2(X0,X1)) | ~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) | ~v3_funct_2(X1,X0,X0) | ~v1_funct_2(X1,X0,X0) | ~v1_funct_1(X1)) )),
% 3.06/1.00    inference(cnf_transformation,[],[f36])).
% 3.06/1.00  
% 3.06/1.00  fof(f72,plain,(
% 3.06/1.00    ~r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK0,sK0,sK0,k2_funct_2(sK0,sK1),sK1),k6_partfun1(sK0)) | ~r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK0,sK0,sK0,sK1,k2_funct_2(sK0,sK1)),k6_partfun1(sK0))),
% 3.06/1.00    inference(cnf_transformation,[],[f45])).
% 3.06/1.00  
% 3.06/1.00  fof(f11,axiom,(
% 3.06/1.00    ! [X0] : (m1_subset_1(k6_partfun1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v1_partfun1(k6_partfun1(X0),X0))),
% 3.06/1.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.06/1.00  
% 3.06/1.00  fof(f17,plain,(
% 3.06/1.00    ! [X0] : m1_subset_1(k6_partfun1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0)))),
% 3.06/1.00    inference(pure_predicate_removal,[],[f11])).
% 3.06/1.00  
% 3.06/1.00  fof(f64,plain,(
% 3.06/1.00    ( ! [X0] : (m1_subset_1(k6_partfun1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0)))) )),
% 3.06/1.00    inference(cnf_transformation,[],[f17])).
% 3.06/1.00  
% 3.06/1.00  fof(f7,axiom,(
% 3.06/1.00    ! [X0,X1,X2,X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) => r2_relset_1(X0,X1,X2,X2))),
% 3.06/1.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.06/1.00  
% 3.06/1.00  fof(f29,plain,(
% 3.06/1.00    ! [X0,X1,X2,X3] : (r2_relset_1(X0,X1,X2,X2) | (~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))))),
% 3.06/1.00    inference(ennf_transformation,[],[f7])).
% 3.06/1.00  
% 3.06/1.00  fof(f30,plain,(
% 3.06/1.00    ! [X0,X1,X2,X3] : (r2_relset_1(X0,X1,X2,X2) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 3.06/1.00    inference(flattening,[],[f29])).
% 3.06/1.00  
% 3.06/1.00  fof(f54,plain,(
% 3.06/1.00    ( ! [X2,X0,X3,X1] : (r2_relset_1(X0,X1,X2,X2) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 3.06/1.00    inference(cnf_transformation,[],[f30])).
% 3.06/1.00  
% 3.06/1.00  cnf(c_22,negated_conjecture,
% 3.06/1.00      ( m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) ),
% 3.06/1.00      inference(cnf_transformation,[],[f71]) ).
% 3.06/1.00  
% 3.06/1.00  cnf(c_518,negated_conjecture,
% 3.06/1.00      ( m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) ),
% 3.06/1.00      inference(subtyping,[status(esa)],[c_22]) ).
% 3.06/1.00  
% 3.06/1.00  cnf(c_1028,plain,
% 3.06/1.00      ( m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) = iProver_top ),
% 3.06/1.00      inference(predicate_to_equality,[status(thm)],[c_518]) ).
% 3.06/1.00  
% 3.06/1.00  cnf(c_20,plain,
% 3.06/1.00      ( ~ v1_funct_2(X0,X1,X1)
% 3.06/1.00      | ~ v3_funct_2(X0,X1,X1)
% 3.06/1.00      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X1)))
% 3.06/1.00      | ~ v1_funct_1(X0)
% 3.06/1.00      | k2_funct_2(X1,X0) = k2_funct_1(X0) ),
% 3.06/1.00      inference(cnf_transformation,[],[f66]) ).
% 3.06/1.00  
% 3.06/1.00  cnf(c_520,plain,
% 3.06/1.00      ( ~ v1_funct_2(X0_48,X0_49,X0_49)
% 3.06/1.00      | ~ v3_funct_2(X0_48,X0_49,X0_49)
% 3.06/1.00      | ~ m1_subset_1(X0_48,k1_zfmisc_1(k2_zfmisc_1(X0_49,X0_49)))
% 3.06/1.00      | ~ v1_funct_1(X0_48)
% 3.06/1.00      | k2_funct_2(X0_49,X0_48) = k2_funct_1(X0_48) ),
% 3.06/1.00      inference(subtyping,[status(esa)],[c_20]) ).
% 3.06/1.00  
% 3.06/1.00  cnf(c_1026,plain,
% 3.06/1.00      ( k2_funct_2(X0_49,X0_48) = k2_funct_1(X0_48)
% 3.06/1.00      | v1_funct_2(X0_48,X0_49,X0_49) != iProver_top
% 3.06/1.00      | v3_funct_2(X0_48,X0_49,X0_49) != iProver_top
% 3.06/1.00      | m1_subset_1(X0_48,k1_zfmisc_1(k2_zfmisc_1(X0_49,X0_49))) != iProver_top
% 3.06/1.00      | v1_funct_1(X0_48) != iProver_top ),
% 3.06/1.00      inference(predicate_to_equality,[status(thm)],[c_520]) ).
% 3.06/1.00  
% 3.06/1.00  cnf(c_2093,plain,
% 3.06/1.00      ( k2_funct_2(sK0,sK1) = k2_funct_1(sK1)
% 3.06/1.00      | v1_funct_2(sK1,sK0,sK0) != iProver_top
% 3.06/1.00      | v3_funct_2(sK1,sK0,sK0) != iProver_top
% 3.06/1.00      | v1_funct_1(sK1) != iProver_top ),
% 3.06/1.00      inference(superposition,[status(thm)],[c_1028,c_1026]) ).
% 3.06/1.00  
% 3.06/1.00  cnf(c_25,negated_conjecture,
% 3.06/1.00      ( v1_funct_1(sK1) ),
% 3.06/1.00      inference(cnf_transformation,[],[f68]) ).
% 3.06/1.00  
% 3.06/1.00  cnf(c_24,negated_conjecture,
% 3.06/1.00      ( v1_funct_2(sK1,sK0,sK0) ),
% 3.06/1.00      inference(cnf_transformation,[],[f69]) ).
% 3.06/1.00  
% 3.06/1.00  cnf(c_23,negated_conjecture,
% 3.06/1.00      ( v3_funct_2(sK1,sK0,sK0) ),
% 3.06/1.00      inference(cnf_transformation,[],[f70]) ).
% 3.06/1.00  
% 3.06/1.00  cnf(c_620,plain,
% 3.06/1.00      ( ~ v1_funct_2(sK1,sK0,sK0)
% 3.06/1.00      | ~ v3_funct_2(sK1,sK0,sK0)
% 3.06/1.00      | ~ m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
% 3.06/1.00      | ~ v1_funct_1(sK1)
% 3.06/1.00      | k2_funct_2(sK0,sK1) = k2_funct_1(sK1) ),
% 3.06/1.00      inference(instantiation,[status(thm)],[c_520]) ).
% 3.06/1.00  
% 3.06/1.00  cnf(c_2393,plain,
% 3.06/1.00      ( k2_funct_2(sK0,sK1) = k2_funct_1(sK1) ),
% 3.06/1.00      inference(global_propositional_subsumption,
% 3.06/1.00                [status(thm)],
% 3.06/1.00                [c_2093,c_25,c_24,c_23,c_22,c_620]) ).
% 3.06/1.00  
% 3.06/1.00  cnf(c_14,plain,
% 3.06/1.00      ( ~ v1_funct_2(X0,X1,X1)
% 3.06/1.00      | ~ v3_funct_2(X0,X1,X1)
% 3.06/1.00      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X1)))
% 3.06/1.00      | m1_subset_1(k2_funct_2(X1,X0),k1_zfmisc_1(k2_zfmisc_1(X1,X1)))
% 3.06/1.00      | ~ v1_funct_1(X0) ),
% 3.06/1.00      inference(cnf_transformation,[],[f63]) ).
% 3.06/1.00  
% 3.06/1.00  cnf(c_526,plain,
% 3.06/1.00      ( ~ v1_funct_2(X0_48,X0_49,X0_49)
% 3.06/1.00      | ~ v3_funct_2(X0_48,X0_49,X0_49)
% 3.06/1.00      | ~ m1_subset_1(X0_48,k1_zfmisc_1(k2_zfmisc_1(X0_49,X0_49)))
% 3.06/1.00      | m1_subset_1(k2_funct_2(X0_49,X0_48),k1_zfmisc_1(k2_zfmisc_1(X0_49,X0_49)))
% 3.06/1.00      | ~ v1_funct_1(X0_48) ),
% 3.06/1.00      inference(subtyping,[status(esa)],[c_14]) ).
% 3.06/1.00  
% 3.06/1.00  cnf(c_1020,plain,
% 3.06/1.00      ( v1_funct_2(X0_48,X0_49,X0_49) != iProver_top
% 3.06/1.00      | v3_funct_2(X0_48,X0_49,X0_49) != iProver_top
% 3.06/1.00      | m1_subset_1(X0_48,k1_zfmisc_1(k2_zfmisc_1(X0_49,X0_49))) != iProver_top
% 3.06/1.00      | m1_subset_1(k2_funct_2(X0_49,X0_48),k1_zfmisc_1(k2_zfmisc_1(X0_49,X0_49))) = iProver_top
% 3.06/1.00      | v1_funct_1(X0_48) != iProver_top ),
% 3.06/1.00      inference(predicate_to_equality,[status(thm)],[c_526]) ).
% 3.06/1.00  
% 3.06/1.00  cnf(c_2406,plain,
% 3.06/1.00      ( v1_funct_2(sK1,sK0,sK0) != iProver_top
% 3.06/1.00      | v3_funct_2(sK1,sK0,sK0) != iProver_top
% 3.06/1.00      | m1_subset_1(k2_funct_1(sK1),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) = iProver_top
% 3.06/1.00      | m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) != iProver_top
% 3.06/1.00      | v1_funct_1(sK1) != iProver_top ),
% 3.06/1.00      inference(superposition,[status(thm)],[c_2393,c_1020]) ).
% 3.06/1.00  
% 3.06/1.00  cnf(c_26,plain,
% 3.06/1.00      ( v1_funct_1(sK1) = iProver_top ),
% 3.06/1.00      inference(predicate_to_equality,[status(thm)],[c_25]) ).
% 3.06/1.00  
% 3.06/1.00  cnf(c_27,plain,
% 3.06/1.00      ( v1_funct_2(sK1,sK0,sK0) = iProver_top ),
% 3.06/1.00      inference(predicate_to_equality,[status(thm)],[c_24]) ).
% 3.06/1.00  
% 3.06/1.00  cnf(c_28,plain,
% 3.06/1.00      ( v3_funct_2(sK1,sK0,sK0) = iProver_top ),
% 3.06/1.00      inference(predicate_to_equality,[status(thm)],[c_23]) ).
% 3.06/1.00  
% 3.06/1.00  cnf(c_29,plain,
% 3.06/1.00      ( m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) = iProver_top ),
% 3.06/1.00      inference(predicate_to_equality,[status(thm)],[c_22]) ).
% 3.06/1.00  
% 3.06/1.00  cnf(c_3199,plain,
% 3.06/1.00      ( m1_subset_1(k2_funct_1(sK1),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) = iProver_top ),
% 3.06/1.00      inference(global_propositional_subsumption,
% 3.06/1.00                [status(thm)],
% 3.06/1.00                [c_2406,c_26,c_27,c_28,c_29]) ).
% 3.06/1.00  
% 3.06/1.00  cnf(c_9,plain,
% 3.06/1.00      ( ~ v3_funct_2(X0,X1,X2)
% 3.06/1.00      | v2_funct_2(X0,X2)
% 3.06/1.00      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.06/1.00      | ~ v1_funct_1(X0) ),
% 3.06/1.00      inference(cnf_transformation,[],[f57]) ).
% 3.06/1.00  
% 3.06/1.00  cnf(c_7,plain,
% 3.06/1.00      ( v5_relat_1(X0,X1)
% 3.06/1.00      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) ),
% 3.06/1.00      inference(cnf_transformation,[],[f53]) ).
% 3.06/1.00  
% 3.06/1.00  cnf(c_13,plain,
% 3.06/1.00      ( ~ v2_funct_2(X0,X1)
% 3.06/1.00      | ~ v5_relat_1(X0,X1)
% 3.06/1.00      | ~ v1_relat_1(X0)
% 3.06/1.00      | k2_relat_1(X0) = X1 ),
% 3.06/1.00      inference(cnf_transformation,[],[f58]) ).
% 3.06/1.00  
% 3.06/1.00  cnf(c_291,plain,
% 3.06/1.00      ( ~ v2_funct_2(X0,X1)
% 3.06/1.00      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X2,X1)))
% 3.06/1.00      | ~ v1_relat_1(X0)
% 3.06/1.00      | k2_relat_1(X0) = X1 ),
% 3.06/1.00      inference(resolution,[status(thm)],[c_7,c_13]) ).
% 3.06/1.00  
% 3.06/1.00  cnf(c_6,plain,
% 3.06/1.00      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.06/1.00      | v1_relat_1(X0) ),
% 3.06/1.00      inference(cnf_transformation,[],[f52]) ).
% 3.06/1.00  
% 3.06/1.00  cnf(c_303,plain,
% 3.06/1.00      ( ~ v2_funct_2(X0,X1)
% 3.06/1.00      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X2,X1)))
% 3.06/1.00      | k2_relat_1(X0) = X1 ),
% 3.06/1.00      inference(forward_subsumption_resolution,[status(thm)],[c_291,c_6]) ).
% 3.06/1.00  
% 3.06/1.00  cnf(c_334,plain,
% 3.06/1.00      ( ~ v3_funct_2(X0,X1,X2)
% 3.06/1.00      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.06/1.00      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X4,X5)))
% 3.06/1.00      | ~ v1_funct_1(X0)
% 3.06/1.00      | X3 != X0
% 3.06/1.00      | X5 != X2
% 3.06/1.00      | k2_relat_1(X3) = X5 ),
% 3.06/1.00      inference(resolution_lifted,[status(thm)],[c_9,c_303]) ).
% 3.06/1.00  
% 3.06/1.00  cnf(c_335,plain,
% 3.06/1.00      ( ~ v3_funct_2(X0,X1,X2)
% 3.06/1.00      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.06/1.00      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X3,X2)))
% 3.06/1.00      | ~ v1_funct_1(X0)
% 3.06/1.00      | k2_relat_1(X0) = X2 ),
% 3.06/1.00      inference(unflattening,[status(thm)],[c_334]) ).
% 3.06/1.01  
% 3.06/1.01  cnf(c_514,plain,
% 3.06/1.01      ( ~ v3_funct_2(X0_48,X0_49,X1_49)
% 3.06/1.01      | ~ m1_subset_1(X0_48,k1_zfmisc_1(k2_zfmisc_1(X0_49,X1_49)))
% 3.06/1.01      | ~ m1_subset_1(X0_48,k1_zfmisc_1(k2_zfmisc_1(X2_49,X1_49)))
% 3.06/1.01      | ~ v1_funct_1(X0_48)
% 3.06/1.01      | k2_relat_1(X0_48) = X1_49 ),
% 3.06/1.01      inference(subtyping,[status(esa)],[c_335]) ).
% 3.06/1.01  
% 3.06/1.01  cnf(c_1032,plain,
% 3.06/1.01      ( k2_relat_1(X0_48) = X0_49
% 3.06/1.01      | v3_funct_2(X0_48,X1_49,X0_49) != iProver_top
% 3.06/1.01      | m1_subset_1(X0_48,k1_zfmisc_1(k2_zfmisc_1(X2_49,X0_49))) != iProver_top
% 3.06/1.01      | m1_subset_1(X0_48,k1_zfmisc_1(k2_zfmisc_1(X1_49,X0_49))) != iProver_top
% 3.06/1.01      | v1_funct_1(X0_48) != iProver_top ),
% 3.06/1.01      inference(predicate_to_equality,[status(thm)],[c_514]) ).
% 3.06/1.01  
% 3.06/1.01  cnf(c_3614,plain,
% 3.06/1.01      ( k2_relat_1(k2_funct_1(sK1)) = sK0
% 3.06/1.01      | v3_funct_2(k2_funct_1(sK1),X0_49,sK0) != iProver_top
% 3.06/1.01      | m1_subset_1(k2_funct_1(sK1),k1_zfmisc_1(k2_zfmisc_1(X0_49,sK0))) != iProver_top
% 3.06/1.01      | v1_funct_1(k2_funct_1(sK1)) != iProver_top ),
% 3.06/1.01      inference(superposition,[status(thm)],[c_3199,c_1032]) ).
% 3.06/1.01  
% 3.06/1.01  cnf(c_0,plain,
% 3.06/1.01      ( ~ v1_relat_1(X0)
% 3.06/1.01      | ~ v1_funct_1(X0)
% 3.06/1.01      | v1_funct_1(k2_funct_1(X0)) ),
% 3.06/1.01      inference(cnf_transformation,[],[f47]) ).
% 3.06/1.01  
% 3.06/1.01  cnf(c_535,plain,
% 3.06/1.01      ( ~ v1_relat_1(X0_48)
% 3.06/1.01      | ~ v1_funct_1(X0_48)
% 3.06/1.01      | v1_funct_1(k2_funct_1(X0_48)) ),
% 3.06/1.01      inference(subtyping,[status(esa)],[c_0]) ).
% 3.06/1.01  
% 3.06/1.01  cnf(c_576,plain,
% 3.06/1.01      ( v1_relat_1(X0_48) != iProver_top
% 3.06/1.01      | v1_funct_1(X0_48) != iProver_top
% 3.06/1.01      | v1_funct_1(k2_funct_1(X0_48)) = iProver_top ),
% 3.06/1.01      inference(predicate_to_equality,[status(thm)],[c_535]) ).
% 3.06/1.01  
% 3.06/1.01  cnf(c_578,plain,
% 3.06/1.01      ( v1_relat_1(sK1) != iProver_top
% 3.06/1.01      | v1_funct_1(k2_funct_1(sK1)) = iProver_top
% 3.06/1.01      | v1_funct_1(sK1) != iProver_top ),
% 3.06/1.01      inference(instantiation,[status(thm)],[c_576]) ).
% 3.06/1.01  
% 3.06/1.01  cnf(c_529,plain,
% 3.06/1.01      ( ~ m1_subset_1(X0_48,k1_zfmisc_1(k2_zfmisc_1(X0_49,X1_49)))
% 3.06/1.01      | v1_relat_1(X0_48) ),
% 3.06/1.01      inference(subtyping,[status(esa)],[c_6]) ).
% 3.06/1.01  
% 3.06/1.01  cnf(c_594,plain,
% 3.06/1.01      ( m1_subset_1(X0_48,k1_zfmisc_1(k2_zfmisc_1(X0_49,X1_49))) != iProver_top
% 3.06/1.01      | v1_relat_1(X0_48) = iProver_top ),
% 3.06/1.01      inference(predicate_to_equality,[status(thm)],[c_529]) ).
% 3.06/1.01  
% 3.06/1.01  cnf(c_596,plain,
% 3.06/1.01      ( m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) != iProver_top
% 3.06/1.01      | v1_relat_1(sK1) = iProver_top ),
% 3.06/1.01      inference(instantiation,[status(thm)],[c_594]) ).
% 3.06/1.01  
% 3.06/1.01  cnf(c_15,plain,
% 3.06/1.01      ( ~ v1_funct_2(X0,X1,X1)
% 3.06/1.01      | ~ v3_funct_2(X0,X1,X1)
% 3.06/1.01      | v3_funct_2(k2_funct_2(X1,X0),X1,X1)
% 3.06/1.01      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X1)))
% 3.06/1.01      | ~ v1_funct_1(X0) ),
% 3.06/1.01      inference(cnf_transformation,[],[f62]) ).
% 3.06/1.01  
% 3.06/1.01  cnf(c_525,plain,
% 3.06/1.01      ( ~ v1_funct_2(X0_48,X0_49,X0_49)
% 3.06/1.01      | ~ v3_funct_2(X0_48,X0_49,X0_49)
% 3.06/1.01      | v3_funct_2(k2_funct_2(X0_49,X0_48),X0_49,X0_49)
% 3.06/1.01      | ~ m1_subset_1(X0_48,k1_zfmisc_1(k2_zfmisc_1(X0_49,X0_49)))
% 3.06/1.01      | ~ v1_funct_1(X0_48) ),
% 3.06/1.01      inference(subtyping,[status(esa)],[c_15]) ).
% 3.06/1.01  
% 3.06/1.01  cnf(c_1021,plain,
% 3.06/1.01      ( v1_funct_2(X0_48,X0_49,X0_49) != iProver_top
% 3.06/1.01      | v3_funct_2(X0_48,X0_49,X0_49) != iProver_top
% 3.06/1.01      | v3_funct_2(k2_funct_2(X0_49,X0_48),X0_49,X0_49) = iProver_top
% 3.06/1.01      | m1_subset_1(X0_48,k1_zfmisc_1(k2_zfmisc_1(X0_49,X0_49))) != iProver_top
% 3.06/1.01      | v1_funct_1(X0_48) != iProver_top ),
% 3.06/1.01      inference(predicate_to_equality,[status(thm)],[c_525]) ).
% 3.06/1.01  
% 3.06/1.01  cnf(c_2239,plain,
% 3.06/1.01      ( v1_funct_2(sK1,sK0,sK0) != iProver_top
% 3.06/1.01      | v3_funct_2(k2_funct_2(sK0,sK1),sK0,sK0) = iProver_top
% 3.06/1.01      | v3_funct_2(sK1,sK0,sK0) != iProver_top
% 3.06/1.01      | v1_funct_1(sK1) != iProver_top ),
% 3.06/1.01      inference(superposition,[status(thm)],[c_1028,c_1021]) ).
% 3.06/1.01  
% 3.06/1.01  cnf(c_606,plain,
% 3.06/1.01      ( v1_funct_2(X0_48,X0_49,X0_49) != iProver_top
% 3.06/1.01      | v3_funct_2(X0_48,X0_49,X0_49) != iProver_top
% 3.06/1.01      | v3_funct_2(k2_funct_2(X0_49,X0_48),X0_49,X0_49) = iProver_top
% 3.06/1.01      | m1_subset_1(X0_48,k1_zfmisc_1(k2_zfmisc_1(X0_49,X0_49))) != iProver_top
% 3.06/1.01      | v1_funct_1(X0_48) != iProver_top ),
% 3.06/1.01      inference(predicate_to_equality,[status(thm)],[c_525]) ).
% 3.06/1.01  
% 3.06/1.01  cnf(c_608,plain,
% 3.06/1.01      ( v1_funct_2(sK1,sK0,sK0) != iProver_top
% 3.06/1.01      | v3_funct_2(k2_funct_2(sK0,sK1),sK0,sK0) = iProver_top
% 3.06/1.01      | v3_funct_2(sK1,sK0,sK0) != iProver_top
% 3.06/1.01      | m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) != iProver_top
% 3.06/1.01      | v1_funct_1(sK1) != iProver_top ),
% 3.06/1.01      inference(instantiation,[status(thm)],[c_606]) ).
% 3.06/1.01  
% 3.06/1.01  cnf(c_2459,plain,
% 3.06/1.01      ( v3_funct_2(k2_funct_2(sK0,sK1),sK0,sK0) = iProver_top ),
% 3.06/1.01      inference(global_propositional_subsumption,
% 3.06/1.01                [status(thm)],
% 3.06/1.01                [c_2239,c_26,c_27,c_28,c_29,c_608]) ).
% 3.06/1.01  
% 3.06/1.01  cnf(c_2463,plain,
% 3.06/1.01      ( v3_funct_2(k2_funct_1(sK1),sK0,sK0) = iProver_top ),
% 3.06/1.01      inference(light_normalisation,[status(thm)],[c_2459,c_2393]) ).
% 3.06/1.01  
% 3.06/1.01  cnf(c_3663,plain,
% 3.06/1.01      ( k2_relat_1(k2_funct_1(sK1)) = sK0
% 3.06/1.01      | v3_funct_2(k2_funct_1(sK1),sK0,sK0) != iProver_top
% 3.06/1.01      | m1_subset_1(k2_funct_1(sK1),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) != iProver_top
% 3.06/1.01      | v1_funct_1(k2_funct_1(sK1)) != iProver_top ),
% 3.06/1.01      inference(instantiation,[status(thm)],[c_3614]) ).
% 3.06/1.01  
% 3.06/1.01  cnf(c_5242,plain,
% 3.06/1.01      ( k2_relat_1(k2_funct_1(sK1)) = sK0 ),
% 3.06/1.01      inference(global_propositional_subsumption,
% 3.06/1.01                [status(thm)],
% 3.06/1.01                [c_3614,c_26,c_27,c_28,c_29,c_578,c_596,c_2406,c_2463,
% 3.06/1.01                 c_3663]) ).
% 3.06/1.01  
% 3.06/1.01  cnf(c_10,plain,
% 3.06/1.01      ( ~ v3_funct_2(X0,X1,X2)
% 3.06/1.01      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.06/1.01      | v2_funct_1(X0)
% 3.06/1.01      | ~ v1_funct_1(X0) ),
% 3.06/1.01      inference(cnf_transformation,[],[f56]) ).
% 3.06/1.01  
% 3.06/1.01  cnf(c_527,plain,
% 3.06/1.01      ( ~ v3_funct_2(X0_48,X0_49,X1_49)
% 3.06/1.01      | ~ m1_subset_1(X0_48,k1_zfmisc_1(k2_zfmisc_1(X0_49,X1_49)))
% 3.06/1.01      | v2_funct_1(X0_48)
% 3.06/1.01      | ~ v1_funct_1(X0_48) ),
% 3.06/1.01      inference(subtyping,[status(esa)],[c_10]) ).
% 3.06/1.01  
% 3.06/1.01  cnf(c_1019,plain,
% 3.06/1.01      ( v3_funct_2(X0_48,X0_49,X1_49) != iProver_top
% 3.06/1.01      | m1_subset_1(X0_48,k1_zfmisc_1(k2_zfmisc_1(X0_49,X1_49))) != iProver_top
% 3.06/1.01      | v2_funct_1(X0_48) = iProver_top
% 3.06/1.01      | v1_funct_1(X0_48) != iProver_top ),
% 3.06/1.01      inference(predicate_to_equality,[status(thm)],[c_527]) ).
% 3.06/1.01  
% 3.06/1.01  cnf(c_3206,plain,
% 3.06/1.01      ( v3_funct_2(k2_funct_1(sK1),sK0,sK0) != iProver_top
% 3.06/1.01      | v2_funct_1(k2_funct_1(sK1)) = iProver_top
% 3.06/1.01      | v1_funct_1(k2_funct_1(sK1)) != iProver_top ),
% 3.06/1.01      inference(superposition,[status(thm)],[c_3199,c_1019]) ).
% 3.06/1.01  
% 3.06/1.01  cnf(c_4,plain,
% 3.06/1.01      ( ~ v2_funct_1(X0)
% 3.06/1.01      | v2_funct_1(k2_funct_1(X0))
% 3.06/1.01      | ~ v1_relat_1(X0)
% 3.06/1.01      | ~ v1_funct_1(X0) ),
% 3.06/1.01      inference(cnf_transformation,[],[f50]) ).
% 3.06/1.01  
% 3.06/1.01  cnf(c_531,plain,
% 3.06/1.01      ( ~ v2_funct_1(X0_48)
% 3.06/1.01      | v2_funct_1(k2_funct_1(X0_48))
% 3.06/1.01      | ~ v1_relat_1(X0_48)
% 3.06/1.01      | ~ v1_funct_1(X0_48) ),
% 3.06/1.01      inference(subtyping,[status(esa)],[c_4]) ).
% 3.06/1.01  
% 3.06/1.01  cnf(c_588,plain,
% 3.06/1.01      ( v2_funct_1(X0_48) != iProver_top
% 3.06/1.01      | v2_funct_1(k2_funct_1(X0_48)) = iProver_top
% 3.06/1.01      | v1_relat_1(X0_48) != iProver_top
% 3.06/1.01      | v1_funct_1(X0_48) != iProver_top ),
% 3.06/1.01      inference(predicate_to_equality,[status(thm)],[c_531]) ).
% 3.06/1.01  
% 3.06/1.01  cnf(c_590,plain,
% 3.06/1.01      ( v2_funct_1(k2_funct_1(sK1)) = iProver_top
% 3.06/1.01      | v2_funct_1(sK1) != iProver_top
% 3.06/1.01      | v1_relat_1(sK1) != iProver_top
% 3.06/1.01      | v1_funct_1(sK1) != iProver_top ),
% 3.06/1.01      inference(instantiation,[status(thm)],[c_588]) ).
% 3.06/1.01  
% 3.06/1.01  cnf(c_600,plain,
% 3.06/1.01      ( v3_funct_2(X0_48,X0_49,X1_49) != iProver_top
% 3.06/1.01      | m1_subset_1(X0_48,k1_zfmisc_1(k2_zfmisc_1(X0_49,X1_49))) != iProver_top
% 3.06/1.01      | v2_funct_1(X0_48) = iProver_top
% 3.06/1.01      | v1_funct_1(X0_48) != iProver_top ),
% 3.06/1.01      inference(predicate_to_equality,[status(thm)],[c_527]) ).
% 3.06/1.01  
% 3.06/1.01  cnf(c_602,plain,
% 3.06/1.01      ( v3_funct_2(sK1,sK0,sK0) != iProver_top
% 3.06/1.01      | m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) != iProver_top
% 3.06/1.01      | v2_funct_1(sK1) = iProver_top
% 3.06/1.01      | v1_funct_1(sK1) != iProver_top ),
% 3.06/1.01      inference(instantiation,[status(thm)],[c_600]) ).
% 3.06/1.01  
% 3.06/1.01  cnf(c_3775,plain,
% 3.06/1.01      ( v2_funct_1(k2_funct_1(sK1)) = iProver_top ),
% 3.06/1.01      inference(global_propositional_subsumption,
% 3.06/1.01                [status(thm)],
% 3.06/1.01                [c_3206,c_26,c_28,c_29,c_590,c_596,c_602]) ).
% 3.06/1.01  
% 3.06/1.01  cnf(c_2,plain,
% 3.06/1.01      ( ~ v2_funct_1(X0)
% 3.06/1.01      | ~ v1_relat_1(X0)
% 3.06/1.01      | ~ v1_funct_1(X0)
% 3.06/1.01      | k5_relat_1(k2_funct_1(X0),X0) = k6_partfun1(k2_relat_1(X0)) ),
% 3.06/1.01      inference(cnf_transformation,[],[f73]) ).
% 3.06/1.01  
% 3.06/1.01  cnf(c_533,plain,
% 3.06/1.01      ( ~ v2_funct_1(X0_48)
% 3.06/1.01      | ~ v1_relat_1(X0_48)
% 3.06/1.01      | ~ v1_funct_1(X0_48)
% 3.06/1.01      | k5_relat_1(k2_funct_1(X0_48),X0_48) = k6_partfun1(k2_relat_1(X0_48)) ),
% 3.06/1.01      inference(subtyping,[status(esa)],[c_2]) ).
% 3.06/1.01  
% 3.06/1.01  cnf(c_1013,plain,
% 3.06/1.01      ( k5_relat_1(k2_funct_1(X0_48),X0_48) = k6_partfun1(k2_relat_1(X0_48))
% 3.06/1.01      | v2_funct_1(X0_48) != iProver_top
% 3.06/1.01      | v1_relat_1(X0_48) != iProver_top
% 3.06/1.01      | v1_funct_1(X0_48) != iProver_top ),
% 3.06/1.01      inference(predicate_to_equality,[status(thm)],[c_533]) ).
% 3.06/1.01  
% 3.06/1.01  cnf(c_3781,plain,
% 3.06/1.01      ( k5_relat_1(k2_funct_1(k2_funct_1(sK1)),k2_funct_1(sK1)) = k6_partfun1(k2_relat_1(k2_funct_1(sK1)))
% 3.06/1.01      | v1_relat_1(k2_funct_1(sK1)) != iProver_top
% 3.06/1.01      | v1_funct_1(k2_funct_1(sK1)) != iProver_top ),
% 3.06/1.01      inference(superposition,[status(thm)],[c_3775,c_1013]) ).
% 3.06/1.01  
% 3.06/1.01  cnf(c_1751,plain,
% 3.06/1.01      ( v3_funct_2(sK1,sK0,sK0) != iProver_top
% 3.06/1.01      | v2_funct_1(sK1) = iProver_top
% 3.06/1.01      | v1_funct_1(sK1) != iProver_top ),
% 3.06/1.01      inference(superposition,[status(thm)],[c_1028,c_1019]) ).
% 3.06/1.01  
% 3.06/1.01  cnf(c_1872,plain,
% 3.06/1.01      ( v2_funct_1(sK1) = iProver_top ),
% 3.06/1.01      inference(global_propositional_subsumption,
% 3.06/1.01                [status(thm)],
% 3.06/1.01                [c_1751,c_26,c_28,c_29,c_602]) ).
% 3.06/1.01  
% 3.06/1.01  cnf(c_5,plain,
% 3.06/1.01      ( ~ v2_funct_1(X0)
% 3.06/1.01      | ~ v1_relat_1(X0)
% 3.06/1.01      | ~ v1_funct_1(X0)
% 3.06/1.01      | k2_funct_1(k2_funct_1(X0)) = X0 ),
% 3.06/1.01      inference(cnf_transformation,[],[f51]) ).
% 3.06/1.01  
% 3.06/1.01  cnf(c_530,plain,
% 3.06/1.01      ( ~ v2_funct_1(X0_48)
% 3.06/1.01      | ~ v1_relat_1(X0_48)
% 3.06/1.01      | ~ v1_funct_1(X0_48)
% 3.06/1.01      | k2_funct_1(k2_funct_1(X0_48)) = X0_48 ),
% 3.06/1.01      inference(subtyping,[status(esa)],[c_5]) ).
% 3.06/1.01  
% 3.06/1.01  cnf(c_1016,plain,
% 3.06/1.01      ( k2_funct_1(k2_funct_1(X0_48)) = X0_48
% 3.06/1.01      | v2_funct_1(X0_48) != iProver_top
% 3.06/1.01      | v1_relat_1(X0_48) != iProver_top
% 3.06/1.01      | v1_funct_1(X0_48) != iProver_top ),
% 3.06/1.01      inference(predicate_to_equality,[status(thm)],[c_530]) ).
% 3.06/1.01  
% 3.06/1.01  cnf(c_1879,plain,
% 3.06/1.01      ( k2_funct_1(k2_funct_1(sK1)) = sK1
% 3.06/1.01      | v1_relat_1(sK1) != iProver_top
% 3.06/1.01      | v1_funct_1(sK1) != iProver_top ),
% 3.06/1.01      inference(superposition,[status(thm)],[c_1872,c_1016]) ).
% 3.06/1.01  
% 3.06/1.01  cnf(c_592,plain,
% 3.06/1.01      ( ~ v2_funct_1(sK1)
% 3.06/1.01      | ~ v1_relat_1(sK1)
% 3.06/1.01      | ~ v1_funct_1(sK1)
% 3.06/1.01      | k2_funct_1(k2_funct_1(sK1)) = sK1 ),
% 3.06/1.01      inference(instantiation,[status(thm)],[c_530]) ).
% 3.06/1.01  
% 3.06/1.01  cnf(c_595,plain,
% 3.06/1.01      ( ~ m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
% 3.06/1.01      | v1_relat_1(sK1) ),
% 3.06/1.01      inference(instantiation,[status(thm)],[c_529]) ).
% 3.06/1.01  
% 3.06/1.01  cnf(c_601,plain,
% 3.06/1.01      ( ~ v3_funct_2(sK1,sK0,sK0)
% 3.06/1.01      | ~ m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
% 3.06/1.01      | v2_funct_1(sK1)
% 3.06/1.01      | ~ v1_funct_1(sK1) ),
% 3.06/1.01      inference(instantiation,[status(thm)],[c_527]) ).
% 3.06/1.01  
% 3.06/1.01  cnf(c_2642,plain,
% 3.06/1.01      ( k2_funct_1(k2_funct_1(sK1)) = sK1 ),
% 3.06/1.01      inference(global_propositional_subsumption,
% 3.06/1.01                [status(thm)],
% 3.06/1.01                [c_1879,c_25,c_23,c_22,c_592,c_595,c_601]) ).
% 3.06/1.01  
% 3.06/1.01  cnf(c_3,plain,
% 3.06/1.01      ( ~ v2_funct_1(X0)
% 3.06/1.01      | ~ v1_relat_1(X0)
% 3.06/1.01      | ~ v1_funct_1(X0)
% 3.06/1.01      | k5_relat_1(X0,k2_funct_1(X0)) = k6_partfun1(k1_relat_1(X0)) ),
% 3.06/1.01      inference(cnf_transformation,[],[f74]) ).
% 3.06/1.01  
% 3.06/1.01  cnf(c_532,plain,
% 3.06/1.01      ( ~ v2_funct_1(X0_48)
% 3.06/1.01      | ~ v1_relat_1(X0_48)
% 3.06/1.01      | ~ v1_funct_1(X0_48)
% 3.06/1.01      | k5_relat_1(X0_48,k2_funct_1(X0_48)) = k6_partfun1(k1_relat_1(X0_48)) ),
% 3.06/1.01      inference(subtyping,[status(esa)],[c_3]) ).
% 3.06/1.01  
% 3.06/1.01  cnf(c_1014,plain,
% 3.06/1.01      ( k5_relat_1(X0_48,k2_funct_1(X0_48)) = k6_partfun1(k1_relat_1(X0_48))
% 3.06/1.01      | v2_funct_1(X0_48) != iProver_top
% 3.06/1.01      | v1_relat_1(X0_48) != iProver_top
% 3.06/1.01      | v1_funct_1(X0_48) != iProver_top ),
% 3.06/1.01      inference(predicate_to_equality,[status(thm)],[c_532]) ).
% 3.06/1.01  
% 3.06/1.01  cnf(c_1877,plain,
% 3.06/1.01      ( k5_relat_1(sK1,k2_funct_1(sK1)) = k6_partfun1(k1_relat_1(sK1))
% 3.06/1.01      | v1_relat_1(sK1) != iProver_top
% 3.06/1.01      | v1_funct_1(sK1) != iProver_top ),
% 3.06/1.01      inference(superposition,[status(thm)],[c_1872,c_1014]) ).
% 3.06/1.01  
% 3.06/1.01  cnf(c_586,plain,
% 3.06/1.01      ( ~ v2_funct_1(sK1)
% 3.06/1.01      | ~ v1_relat_1(sK1)
% 3.06/1.01      | ~ v1_funct_1(sK1)
% 3.06/1.01      | k5_relat_1(sK1,k2_funct_1(sK1)) = k6_partfun1(k1_relat_1(sK1)) ),
% 3.06/1.01      inference(instantiation,[status(thm)],[c_532]) ).
% 3.06/1.01  
% 3.06/1.01  cnf(c_2649,plain,
% 3.06/1.01      ( k5_relat_1(sK1,k2_funct_1(sK1)) = k6_partfun1(k1_relat_1(sK1)) ),
% 3.06/1.01      inference(global_propositional_subsumption,
% 3.06/1.01                [status(thm)],
% 3.06/1.01                [c_1877,c_25,c_23,c_22,c_586,c_595,c_601]) ).
% 3.06/1.01  
% 3.06/1.01  cnf(c_3790,plain,
% 3.06/1.01      ( k6_partfun1(k2_relat_1(k2_funct_1(sK1))) = k6_partfun1(k1_relat_1(sK1))
% 3.06/1.01      | v1_relat_1(k2_funct_1(sK1)) != iProver_top
% 3.06/1.01      | v1_funct_1(k2_funct_1(sK1)) != iProver_top ),
% 3.06/1.01      inference(light_normalisation,[status(thm)],[c_3781,c_2642,c_2649]) ).
% 3.06/1.01  
% 3.06/1.01  cnf(c_1,plain,
% 3.06/1.01      ( ~ v1_relat_1(X0)
% 3.06/1.01      | v1_relat_1(k2_funct_1(X0))
% 3.06/1.01      | ~ v1_funct_1(X0) ),
% 3.06/1.01      inference(cnf_transformation,[],[f46]) ).
% 3.06/1.01  
% 3.06/1.01  cnf(c_534,plain,
% 3.06/1.01      ( ~ v1_relat_1(X0_48)
% 3.06/1.01      | v1_relat_1(k2_funct_1(X0_48))
% 3.06/1.01      | ~ v1_funct_1(X0_48) ),
% 3.06/1.01      inference(subtyping,[status(esa)],[c_1]) ).
% 3.06/1.01  
% 3.06/1.01  cnf(c_579,plain,
% 3.06/1.01      ( v1_relat_1(X0_48) != iProver_top
% 3.06/1.01      | v1_relat_1(k2_funct_1(X0_48)) = iProver_top
% 3.06/1.01      | v1_funct_1(X0_48) != iProver_top ),
% 3.06/1.01      inference(predicate_to_equality,[status(thm)],[c_534]) ).
% 3.06/1.01  
% 3.06/1.01  cnf(c_581,plain,
% 3.06/1.01      ( v1_relat_1(k2_funct_1(sK1)) = iProver_top
% 3.06/1.01      | v1_relat_1(sK1) != iProver_top
% 3.06/1.01      | v1_funct_1(sK1) != iProver_top ),
% 3.06/1.01      inference(instantiation,[status(thm)],[c_579]) ).
% 3.06/1.01  
% 3.06/1.01  cnf(c_3972,plain,
% 3.06/1.01      ( k6_partfun1(k2_relat_1(k2_funct_1(sK1))) = k6_partfun1(k1_relat_1(sK1)) ),
% 3.06/1.01      inference(global_propositional_subsumption,
% 3.06/1.01                [status(thm)],
% 3.06/1.01                [c_3790,c_26,c_29,c_578,c_581,c_596]) ).
% 3.06/1.01  
% 3.06/1.01  cnf(c_5246,plain,
% 3.06/1.01      ( k6_partfun1(k1_relat_1(sK1)) = k6_partfun1(sK0) ),
% 3.06/1.01      inference(demodulation,[status(thm)],[c_5242,c_3972]) ).
% 3.06/1.01  
% 3.06/1.01  cnf(c_19,plain,
% 3.06/1.01      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.06/1.01      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X4,X5)))
% 3.06/1.01      | ~ v1_funct_1(X0)
% 3.06/1.01      | ~ v1_funct_1(X3)
% 3.06/1.01      | k1_partfun1(X4,X5,X1,X2,X3,X0) = k5_relat_1(X3,X0) ),
% 3.06/1.01      inference(cnf_transformation,[],[f65]) ).
% 3.06/1.01  
% 3.06/1.01  cnf(c_521,plain,
% 3.06/1.01      ( ~ m1_subset_1(X0_48,k1_zfmisc_1(k2_zfmisc_1(X0_49,X1_49)))
% 3.06/1.01      | ~ m1_subset_1(X1_48,k1_zfmisc_1(k2_zfmisc_1(X2_49,X3_49)))
% 3.06/1.01      | ~ v1_funct_1(X0_48)
% 3.06/1.01      | ~ v1_funct_1(X1_48)
% 3.06/1.01      | k1_partfun1(X2_49,X3_49,X0_49,X1_49,X1_48,X0_48) = k5_relat_1(X1_48,X0_48) ),
% 3.06/1.01      inference(subtyping,[status(esa)],[c_19]) ).
% 3.06/1.01  
% 3.06/1.01  cnf(c_1025,plain,
% 3.06/1.01      ( k1_partfun1(X0_49,X1_49,X2_49,X3_49,X0_48,X1_48) = k5_relat_1(X0_48,X1_48)
% 3.06/1.01      | m1_subset_1(X1_48,k1_zfmisc_1(k2_zfmisc_1(X2_49,X3_49))) != iProver_top
% 3.06/1.01      | m1_subset_1(X0_48,k1_zfmisc_1(k2_zfmisc_1(X0_49,X1_49))) != iProver_top
% 3.06/1.01      | v1_funct_1(X0_48) != iProver_top
% 3.06/1.01      | v1_funct_1(X1_48) != iProver_top ),
% 3.06/1.01      inference(predicate_to_equality,[status(thm)],[c_521]) ).
% 3.06/1.01  
% 3.06/1.01  cnf(c_3205,plain,
% 3.06/1.01      ( k1_partfun1(sK0,sK0,X0_49,X1_49,k2_funct_1(sK1),X0_48) = k5_relat_1(k2_funct_1(sK1),X0_48)
% 3.06/1.01      | m1_subset_1(X0_48,k1_zfmisc_1(k2_zfmisc_1(X0_49,X1_49))) != iProver_top
% 3.06/1.01      | v1_funct_1(X0_48) != iProver_top
% 3.06/1.01      | v1_funct_1(k2_funct_1(sK1)) != iProver_top ),
% 3.06/1.01      inference(superposition,[status(thm)],[c_3199,c_1025]) ).
% 3.06/1.01  
% 3.06/1.01  cnf(c_5264,plain,
% 3.06/1.01      ( v1_funct_1(X0_48) != iProver_top
% 3.06/1.01      | m1_subset_1(X0_48,k1_zfmisc_1(k2_zfmisc_1(X0_49,X1_49))) != iProver_top
% 3.06/1.01      | k1_partfun1(sK0,sK0,X0_49,X1_49,k2_funct_1(sK1),X0_48) = k5_relat_1(k2_funct_1(sK1),X0_48) ),
% 3.06/1.01      inference(global_propositional_subsumption,
% 3.06/1.01                [status(thm)],
% 3.06/1.01                [c_3205,c_26,c_29,c_578,c_596]) ).
% 3.06/1.01  
% 3.06/1.01  cnf(c_5265,plain,
% 3.06/1.01      ( k1_partfun1(sK0,sK0,X0_49,X1_49,k2_funct_1(sK1),X0_48) = k5_relat_1(k2_funct_1(sK1),X0_48)
% 3.06/1.01      | m1_subset_1(X0_48,k1_zfmisc_1(k2_zfmisc_1(X0_49,X1_49))) != iProver_top
% 3.06/1.01      | v1_funct_1(X0_48) != iProver_top ),
% 3.06/1.01      inference(renaming,[status(thm)],[c_5264]) ).
% 3.06/1.01  
% 3.06/1.01  cnf(c_5273,plain,
% 3.06/1.01      ( k1_partfun1(sK0,sK0,sK0,sK0,k2_funct_1(sK1),sK1) = k5_relat_1(k2_funct_1(sK1),sK1)
% 3.06/1.01      | v1_funct_1(sK1) != iProver_top ),
% 3.06/1.01      inference(superposition,[status(thm)],[c_1028,c_5265]) ).
% 3.06/1.01  
% 3.06/1.01  cnf(c_3611,plain,
% 3.06/1.01      ( k2_relat_1(sK1) = sK0
% 3.06/1.01      | v3_funct_2(sK1,X0_49,sK0) != iProver_top
% 3.06/1.01      | m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(X0_49,sK0))) != iProver_top
% 3.06/1.01      | v1_funct_1(sK1) != iProver_top ),
% 3.06/1.01      inference(superposition,[status(thm)],[c_1028,c_1032]) ).
% 3.06/1.01  
% 3.06/1.01  cnf(c_628,plain,
% 3.06/1.01      ( ~ v3_funct_2(sK1,sK0,sK0)
% 3.06/1.01      | ~ m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
% 3.06/1.01      | ~ v1_funct_1(sK1)
% 3.06/1.01      | k2_relat_1(sK1) = sK0 ),
% 3.06/1.01      inference(instantiation,[status(thm)],[c_514]) ).
% 3.06/1.01  
% 3.06/1.01  cnf(c_3890,plain,
% 3.06/1.01      ( k2_relat_1(sK1) = sK0 ),
% 3.06/1.01      inference(global_propositional_subsumption,
% 3.06/1.01                [status(thm)],
% 3.06/1.01                [c_3611,c_25,c_23,c_22,c_628]) ).
% 3.06/1.01  
% 3.06/1.01  cnf(c_1878,plain,
% 3.06/1.01      ( k5_relat_1(k2_funct_1(sK1),sK1) = k6_partfun1(k2_relat_1(sK1))
% 3.06/1.01      | v1_relat_1(sK1) != iProver_top
% 3.06/1.01      | v1_funct_1(sK1) != iProver_top ),
% 3.06/1.01      inference(superposition,[status(thm)],[c_1872,c_1013]) ).
% 3.06/1.01  
% 3.06/1.01  cnf(c_583,plain,
% 3.06/1.01      ( ~ v2_funct_1(sK1)
% 3.06/1.01      | ~ v1_relat_1(sK1)
% 3.06/1.01      | ~ v1_funct_1(sK1)
% 3.06/1.01      | k5_relat_1(k2_funct_1(sK1),sK1) = k6_partfun1(k2_relat_1(sK1)) ),
% 3.06/1.01      inference(instantiation,[status(thm)],[c_533]) ).
% 3.06/1.01  
% 3.06/1.01  cnf(c_2828,plain,
% 3.06/1.01      ( k5_relat_1(k2_funct_1(sK1),sK1) = k6_partfun1(k2_relat_1(sK1)) ),
% 3.06/1.01      inference(global_propositional_subsumption,
% 3.06/1.01                [status(thm)],
% 3.06/1.01                [c_1878,c_25,c_23,c_22,c_583,c_595,c_601]) ).
% 3.06/1.01  
% 3.06/1.01  cnf(c_3893,plain,
% 3.06/1.01      ( k5_relat_1(k2_funct_1(sK1),sK1) = k6_partfun1(sK0) ),
% 3.06/1.01      inference(demodulation,[status(thm)],[c_3890,c_2828]) ).
% 3.06/1.01  
% 3.06/1.01  cnf(c_5304,plain,
% 3.06/1.01      ( k1_partfun1(sK0,sK0,sK0,sK0,k2_funct_1(sK1),sK1) = k6_partfun1(sK0)
% 3.06/1.01      | v1_funct_1(sK1) != iProver_top ),
% 3.06/1.01      inference(light_normalisation,[status(thm)],[c_5273,c_3893]) ).
% 3.06/1.01  
% 3.06/1.01  cnf(c_538,plain,( X0_49 = X0_49 ),theory(equality) ).
% 3.06/1.01  
% 3.06/1.01  cnf(c_573,plain,
% 3.06/1.01      ( sK0 = sK0 ),
% 3.06/1.01      inference(instantiation,[status(thm)],[c_538]) ).
% 3.06/1.01  
% 3.06/1.01  cnf(c_577,plain,
% 3.06/1.01      ( ~ v1_relat_1(sK1)
% 3.06/1.01      | v1_funct_1(k2_funct_1(sK1))
% 3.06/1.01      | ~ v1_funct_1(sK1) ),
% 3.06/1.01      inference(instantiation,[status(thm)],[c_535]) ).
% 3.06/1.01  
% 3.06/1.01  cnf(c_541,plain,
% 3.06/1.01      ( X0_48 != X1_48 | X2_48 != X1_48 | X2_48 = X0_48 ),
% 3.06/1.01      theory(equality) ).
% 3.06/1.01  
% 3.06/1.01  cnf(c_1295,plain,
% 3.06/1.01      ( X0_48 != X1_48
% 3.06/1.01      | k6_partfun1(sK0) != X1_48
% 3.06/1.01      | k6_partfun1(sK0) = X0_48 ),
% 3.06/1.01      inference(instantiation,[status(thm)],[c_541]) ).
% 3.06/1.01  
% 3.06/1.01  cnf(c_1385,plain,
% 3.06/1.01      ( X0_48 != k6_partfun1(X0_49)
% 3.06/1.01      | k6_partfun1(sK0) = X0_48
% 3.06/1.01      | k6_partfun1(sK0) != k6_partfun1(X0_49) ),
% 3.06/1.01      inference(instantiation,[status(thm)],[c_1295]) ).
% 3.06/1.01  
% 3.06/1.01  cnf(c_1482,plain,
% 3.06/1.01      ( k5_relat_1(k2_funct_1(X0_48),X0_48) != k6_partfun1(k2_relat_1(X0_48))
% 3.06/1.01      | k6_partfun1(sK0) = k5_relat_1(k2_funct_1(X0_48),X0_48)
% 3.06/1.01      | k6_partfun1(sK0) != k6_partfun1(k2_relat_1(X0_48)) ),
% 3.06/1.01      inference(instantiation,[status(thm)],[c_1385]) ).
% 3.06/1.01  
% 3.06/1.01  cnf(c_1483,plain,
% 3.06/1.01      ( k5_relat_1(k2_funct_1(sK1),sK1) != k6_partfun1(k2_relat_1(sK1))
% 3.06/1.01      | k6_partfun1(sK0) = k5_relat_1(k2_funct_1(sK1),sK1)
% 3.06/1.01      | k6_partfun1(sK0) != k6_partfun1(k2_relat_1(sK1)) ),
% 3.06/1.01      inference(instantiation,[status(thm)],[c_1482]) ).
% 3.06/1.01  
% 3.06/1.01  cnf(c_547,plain,
% 3.06/1.01      ( X0_49 != X1_49 | k6_partfun1(X0_49) = k6_partfun1(X1_49) ),
% 3.06/1.01      theory(equality) ).
% 3.06/1.01  
% 3.06/1.01  cnf(c_1297,plain,
% 3.06/1.01      ( sK0 != X0_49 | k6_partfun1(sK0) = k6_partfun1(X0_49) ),
% 3.06/1.01      inference(instantiation,[status(thm)],[c_547]) ).
% 3.06/1.01  
% 3.06/1.01  cnf(c_1843,plain,
% 3.06/1.01      ( sK0 != k2_relat_1(X0_48)
% 3.06/1.01      | k6_partfun1(sK0) = k6_partfun1(k2_relat_1(X0_48)) ),
% 3.06/1.01      inference(instantiation,[status(thm)],[c_1297]) ).
% 3.06/1.01  
% 3.06/1.01  cnf(c_1844,plain,
% 3.06/1.01      ( sK0 != k2_relat_1(sK1)
% 3.06/1.01      | k6_partfun1(sK0) = k6_partfun1(k2_relat_1(sK1)) ),
% 3.06/1.01      inference(instantiation,[status(thm)],[c_1843]) ).
% 3.06/1.01  
% 3.06/1.01  cnf(c_542,plain,
% 3.06/1.01      ( X0_49 != X1_49 | X2_49 != X1_49 | X2_49 = X0_49 ),
% 3.06/1.01      theory(equality) ).
% 3.06/1.01  
% 3.06/1.01  cnf(c_2164,plain,
% 3.06/1.01      ( k2_relat_1(X0_48) != X0_49
% 3.06/1.01      | sK0 != X0_49
% 3.06/1.01      | sK0 = k2_relat_1(X0_48) ),
% 3.06/1.01      inference(instantiation,[status(thm)],[c_542]) ).
% 3.06/1.01  
% 3.06/1.01  cnf(c_2165,plain,
% 3.06/1.01      ( k2_relat_1(sK1) != sK0 | sK0 = k2_relat_1(sK1) | sK0 != sK0 ),
% 3.06/1.01      inference(instantiation,[status(thm)],[c_2164]) ).
% 3.06/1.01  
% 3.06/1.01  cnf(c_2407,plain,
% 3.06/1.01      ( ~ v1_funct_2(sK1,sK0,sK0)
% 3.06/1.01      | ~ v3_funct_2(sK1,sK0,sK0)
% 3.06/1.01      | m1_subset_1(k2_funct_1(sK1),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
% 3.06/1.01      | ~ m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
% 3.06/1.01      | ~ v1_funct_1(sK1) ),
% 3.06/1.01      inference(predicate_to_equality_rev,[status(thm)],[c_2406]) ).
% 3.06/1.01  
% 3.06/1.01  cnf(c_3176,plain,
% 3.06/1.01      ( ~ m1_subset_1(X0_48,k1_zfmisc_1(k2_zfmisc_1(X0_49,X1_49)))
% 3.06/1.01      | ~ m1_subset_1(k2_funct_1(sK1),k1_zfmisc_1(k2_zfmisc_1(X2_49,X3_49)))
% 3.06/1.01      | ~ v1_funct_1(X0_48)
% 3.06/1.01      | ~ v1_funct_1(k2_funct_1(sK1))
% 3.06/1.01      | k1_partfun1(X2_49,X3_49,X0_49,X1_49,k2_funct_1(sK1),X0_48) = k5_relat_1(k2_funct_1(sK1),X0_48) ),
% 3.06/1.01      inference(instantiation,[status(thm)],[c_521]) ).
% 3.06/1.01  
% 3.06/1.01  cnf(c_3179,plain,
% 3.06/1.01      ( ~ m1_subset_1(k2_funct_1(sK1),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
% 3.06/1.01      | ~ m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
% 3.06/1.01      | ~ v1_funct_1(k2_funct_1(sK1))
% 3.06/1.01      | ~ v1_funct_1(sK1)
% 3.06/1.01      | k1_partfun1(sK0,sK0,sK0,sK0,k2_funct_1(sK1),sK1) = k5_relat_1(k2_funct_1(sK1),sK1) ),
% 3.06/1.01      inference(instantiation,[status(thm)],[c_3176]) ).
% 3.06/1.01  
% 3.06/1.01  cnf(c_1326,plain,
% 3.06/1.01      ( X0_48 != X1_48
% 3.06/1.01      | X0_48 = k6_partfun1(X0_49)
% 3.06/1.01      | k6_partfun1(X0_49) != X1_48 ),
% 3.06/1.01      inference(instantiation,[status(thm)],[c_541]) ).
% 3.06/1.01  
% 3.06/1.01  cnf(c_2942,plain,
% 3.06/1.01      ( X0_48 != k5_relat_1(k2_funct_1(X1_48),X1_48)
% 3.06/1.01      | X0_48 = k6_partfun1(sK0)
% 3.06/1.01      | k6_partfun1(sK0) != k5_relat_1(k2_funct_1(X1_48),X1_48) ),
% 3.06/1.01      inference(instantiation,[status(thm)],[c_1326]) ).
% 3.06/1.01  
% 3.06/1.01  cnf(c_4518,plain,
% 3.06/1.01      ( k1_partfun1(X0_49,X1_49,X2_49,X3_49,k2_funct_1(sK1),sK1) != k5_relat_1(k2_funct_1(sK1),sK1)
% 3.06/1.01      | k1_partfun1(X0_49,X1_49,X2_49,X3_49,k2_funct_1(sK1),sK1) = k6_partfun1(sK0)
% 3.06/1.01      | k6_partfun1(sK0) != k5_relat_1(k2_funct_1(sK1),sK1) ),
% 3.06/1.01      inference(instantiation,[status(thm)],[c_2942]) ).
% 3.06/1.01  
% 3.06/1.01  cnf(c_4522,plain,
% 3.06/1.01      ( k1_partfun1(sK0,sK0,sK0,sK0,k2_funct_1(sK1),sK1) != k5_relat_1(k2_funct_1(sK1),sK1)
% 3.06/1.01      | k1_partfun1(sK0,sK0,sK0,sK0,k2_funct_1(sK1),sK1) = k6_partfun1(sK0)
% 3.06/1.01      | k6_partfun1(sK0) != k5_relat_1(k2_funct_1(sK1),sK1) ),
% 3.06/1.01      inference(instantiation,[status(thm)],[c_4518]) ).
% 3.06/1.01  
% 3.06/1.01  cnf(c_5497,plain,
% 3.06/1.01      ( k1_partfun1(sK0,sK0,sK0,sK0,k2_funct_1(sK1),sK1) = k6_partfun1(sK0) ),
% 3.06/1.01      inference(global_propositional_subsumption,
% 3.06/1.01                [status(thm)],
% 3.06/1.01                [c_5304,c_25,c_24,c_23,c_22,c_573,c_577,c_583,c_595,
% 3.06/1.01                 c_601,c_628,c_1483,c_1844,c_2165,c_2407,c_3179,c_4522]) ).
% 3.06/1.01  
% 3.06/1.01  cnf(c_2785,plain,
% 3.06/1.01      ( k1_partfun1(sK0,sK0,X0_49,X1_49,sK1,X0_48) = k5_relat_1(sK1,X0_48)
% 3.06/1.01      | m1_subset_1(X0_48,k1_zfmisc_1(k2_zfmisc_1(X0_49,X1_49))) != iProver_top
% 3.06/1.01      | v1_funct_1(X0_48) != iProver_top
% 3.06/1.01      | v1_funct_1(sK1) != iProver_top ),
% 3.06/1.01      inference(superposition,[status(thm)],[c_1028,c_1025]) ).
% 3.06/1.01  
% 3.06/1.01  cnf(c_2982,plain,
% 3.06/1.01      ( v1_funct_1(X0_48) != iProver_top
% 3.06/1.01      | m1_subset_1(X0_48,k1_zfmisc_1(k2_zfmisc_1(X0_49,X1_49))) != iProver_top
% 3.06/1.01      | k1_partfun1(sK0,sK0,X0_49,X1_49,sK1,X0_48) = k5_relat_1(sK1,X0_48) ),
% 3.06/1.01      inference(global_propositional_subsumption,
% 3.06/1.01                [status(thm)],
% 3.06/1.01                [c_2785,c_26]) ).
% 3.06/1.01  
% 3.06/1.01  cnf(c_2983,plain,
% 3.06/1.01      ( k1_partfun1(sK0,sK0,X0_49,X1_49,sK1,X0_48) = k5_relat_1(sK1,X0_48)
% 3.06/1.01      | m1_subset_1(X0_48,k1_zfmisc_1(k2_zfmisc_1(X0_49,X1_49))) != iProver_top
% 3.06/1.01      | v1_funct_1(X0_48) != iProver_top ),
% 3.06/1.01      inference(renaming,[status(thm)],[c_2982]) ).
% 3.06/1.01  
% 3.06/1.01  cnf(c_2991,plain,
% 3.06/1.01      ( k1_partfun1(sK0,sK0,X0_49,X0_49,sK1,k2_funct_2(X0_49,X0_48)) = k5_relat_1(sK1,k2_funct_2(X0_49,X0_48))
% 3.06/1.01      | v1_funct_2(X0_48,X0_49,X0_49) != iProver_top
% 3.06/1.01      | v3_funct_2(X0_48,X0_49,X0_49) != iProver_top
% 3.06/1.01      | m1_subset_1(X0_48,k1_zfmisc_1(k2_zfmisc_1(X0_49,X0_49))) != iProver_top
% 3.06/1.01      | v1_funct_1(X0_48) != iProver_top
% 3.06/1.01      | v1_funct_1(k2_funct_2(X0_49,X0_48)) != iProver_top ),
% 3.06/1.01      inference(superposition,[status(thm)],[c_1020,c_2983]) ).
% 3.06/1.01  
% 3.06/1.01  cnf(c_17,plain,
% 3.06/1.01      ( ~ v1_funct_2(X0,X1,X1)
% 3.06/1.01      | ~ v3_funct_2(X0,X1,X1)
% 3.06/1.01      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X1)))
% 3.06/1.01      | ~ v1_funct_1(X0)
% 3.06/1.01      | v1_funct_1(k2_funct_2(X1,X0)) ),
% 3.06/1.01      inference(cnf_transformation,[],[f60]) ).
% 3.06/1.01  
% 3.06/1.01  cnf(c_523,plain,
% 3.06/1.01      ( ~ v1_funct_2(X0_48,X0_49,X0_49)
% 3.06/1.01      | ~ v3_funct_2(X0_48,X0_49,X0_49)
% 3.06/1.01      | ~ m1_subset_1(X0_48,k1_zfmisc_1(k2_zfmisc_1(X0_49,X0_49)))
% 3.06/1.01      | ~ v1_funct_1(X0_48)
% 3.06/1.01      | v1_funct_1(k2_funct_2(X0_49,X0_48)) ),
% 3.06/1.01      inference(subtyping,[status(esa)],[c_17]) ).
% 3.06/1.01  
% 3.06/1.01  cnf(c_612,plain,
% 3.06/1.01      ( v1_funct_2(X0_48,X0_49,X0_49) != iProver_top
% 3.06/1.01      | v3_funct_2(X0_48,X0_49,X0_49) != iProver_top
% 3.06/1.01      | m1_subset_1(X0_48,k1_zfmisc_1(k2_zfmisc_1(X0_49,X0_49))) != iProver_top
% 3.06/1.01      | v1_funct_1(X0_48) != iProver_top
% 3.06/1.01      | v1_funct_1(k2_funct_2(X0_49,X0_48)) = iProver_top ),
% 3.06/1.01      inference(predicate_to_equality,[status(thm)],[c_523]) ).
% 3.06/1.01  
% 3.06/1.01  cnf(c_3285,plain,
% 3.06/1.01      ( v1_funct_1(X0_48) != iProver_top
% 3.06/1.01      | m1_subset_1(X0_48,k1_zfmisc_1(k2_zfmisc_1(X0_49,X0_49))) != iProver_top
% 3.06/1.01      | v3_funct_2(X0_48,X0_49,X0_49) != iProver_top
% 3.06/1.01      | v1_funct_2(X0_48,X0_49,X0_49) != iProver_top
% 3.06/1.01      | k1_partfun1(sK0,sK0,X0_49,X0_49,sK1,k2_funct_2(X0_49,X0_48)) = k5_relat_1(sK1,k2_funct_2(X0_49,X0_48)) ),
% 3.06/1.01      inference(global_propositional_subsumption,
% 3.06/1.01                [status(thm)],
% 3.06/1.01                [c_2991,c_612]) ).
% 3.06/1.01  
% 3.06/1.01  cnf(c_3286,plain,
% 3.06/1.01      ( k1_partfun1(sK0,sK0,X0_49,X0_49,sK1,k2_funct_2(X0_49,X0_48)) = k5_relat_1(sK1,k2_funct_2(X0_49,X0_48))
% 3.06/1.01      | v1_funct_2(X0_48,X0_49,X0_49) != iProver_top
% 3.06/1.01      | v3_funct_2(X0_48,X0_49,X0_49) != iProver_top
% 3.06/1.01      | m1_subset_1(X0_48,k1_zfmisc_1(k2_zfmisc_1(X0_49,X0_49))) != iProver_top
% 3.06/1.01      | v1_funct_1(X0_48) != iProver_top ),
% 3.06/1.01      inference(renaming,[status(thm)],[c_3285]) ).
% 3.06/1.01  
% 3.06/1.01  cnf(c_3296,plain,
% 3.06/1.01      ( k1_partfun1(sK0,sK0,sK0,sK0,sK1,k2_funct_2(sK0,sK1)) = k5_relat_1(sK1,k2_funct_2(sK0,sK1))
% 3.06/1.01      | v1_funct_2(sK1,sK0,sK0) != iProver_top
% 3.06/1.01      | v3_funct_2(sK1,sK0,sK0) != iProver_top
% 3.06/1.01      | v1_funct_1(sK1) != iProver_top ),
% 3.06/1.01      inference(superposition,[status(thm)],[c_1028,c_3286]) ).
% 3.06/1.01  
% 3.06/1.01  cnf(c_3336,plain,
% 3.06/1.01      ( k1_partfun1(sK0,sK0,sK0,sK0,sK1,k2_funct_1(sK1)) = k6_partfun1(k1_relat_1(sK1))
% 3.06/1.01      | v1_funct_2(sK1,sK0,sK0) != iProver_top
% 3.06/1.01      | v3_funct_2(sK1,sK0,sK0) != iProver_top
% 3.06/1.01      | v1_funct_1(sK1) != iProver_top ),
% 3.06/1.01      inference(light_normalisation,[status(thm)],[c_3296,c_2393,c_2649]) ).
% 3.06/1.01  
% 3.06/1.01  cnf(c_3204,plain,
% 3.06/1.01      ( k1_partfun1(sK0,sK0,sK0,sK0,sK1,k2_funct_1(sK1)) = k5_relat_1(sK1,k2_funct_1(sK1))
% 3.06/1.01      | v1_funct_1(k2_funct_1(sK1)) != iProver_top ),
% 3.06/1.01      inference(superposition,[status(thm)],[c_3199,c_2983]) ).
% 3.06/1.01  
% 3.06/1.01  cnf(c_3268,plain,
% 3.06/1.01      ( k1_partfun1(sK0,sK0,sK0,sK0,sK1,k2_funct_1(sK1)) = k6_partfun1(k1_relat_1(sK1))
% 3.06/1.01      | v1_funct_1(k2_funct_1(sK1)) != iProver_top ),
% 3.06/1.01      inference(light_normalisation,[status(thm)],[c_3204,c_2649]) ).
% 3.06/1.01  
% 3.06/1.01  cnf(c_3455,plain,
% 3.06/1.01      ( k1_partfun1(sK0,sK0,sK0,sK0,sK1,k2_funct_1(sK1)) = k6_partfun1(k1_relat_1(sK1)) ),
% 3.06/1.01      inference(global_propositional_subsumption,
% 3.06/1.01                [status(thm)],
% 3.06/1.01                [c_3336,c_26,c_29,c_578,c_596,c_3268]) ).
% 3.06/1.01  
% 3.06/1.01  cnf(c_21,negated_conjecture,
% 3.06/1.01      ( ~ r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK0,sK0,sK0,k2_funct_2(sK0,sK1),sK1),k6_partfun1(sK0))
% 3.06/1.01      | ~ r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK0,sK0,sK0,sK1,k2_funct_2(sK0,sK1)),k6_partfun1(sK0)) ),
% 3.06/1.01      inference(cnf_transformation,[],[f72]) ).
% 3.06/1.01  
% 3.06/1.01  cnf(c_519,negated_conjecture,
% 3.06/1.01      ( ~ r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK0,sK0,sK0,k2_funct_2(sK0,sK1),sK1),k6_partfun1(sK0))
% 3.06/1.01      | ~ r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK0,sK0,sK0,sK1,k2_funct_2(sK0,sK1)),k6_partfun1(sK0)) ),
% 3.06/1.01      inference(subtyping,[status(esa)],[c_21]) ).
% 3.06/1.01  
% 3.06/1.01  cnf(c_1027,plain,
% 3.06/1.01      ( r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK0,sK0,sK0,k2_funct_2(sK0,sK1),sK1),k6_partfun1(sK0)) != iProver_top
% 3.06/1.01      | r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK0,sK0,sK0,sK1,k2_funct_2(sK0,sK1)),k6_partfun1(sK0)) != iProver_top ),
% 3.06/1.01      inference(predicate_to_equality,[status(thm)],[c_519]) ).
% 3.06/1.01  
% 3.06/1.01  cnf(c_2397,plain,
% 3.06/1.01      ( r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK0,sK0,sK0,k2_funct_1(sK1),sK1),k6_partfun1(sK0)) != iProver_top
% 3.06/1.01      | r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK0,sK0,sK0,sK1,k2_funct_1(sK1)),k6_partfun1(sK0)) != iProver_top ),
% 3.06/1.01      inference(demodulation,[status(thm)],[c_2393,c_1027]) ).
% 3.06/1.01  
% 3.06/1.01  cnf(c_3458,plain,
% 3.06/1.01      ( r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK0,sK0,sK0,k2_funct_1(sK1),sK1),k6_partfun1(sK0)) != iProver_top
% 3.06/1.01      | r2_relset_1(sK0,sK0,k6_partfun1(k1_relat_1(sK1)),k6_partfun1(sK0)) != iProver_top ),
% 3.06/1.01      inference(demodulation,[status(thm)],[c_3455,c_2397]) ).
% 3.06/1.01  
% 3.06/1.01  cnf(c_5500,plain,
% 3.06/1.01      ( r2_relset_1(sK0,sK0,k6_partfun1(k1_relat_1(sK1)),k6_partfun1(sK0)) != iProver_top
% 3.06/1.01      | r2_relset_1(sK0,sK0,k6_partfun1(sK0),k6_partfun1(sK0)) != iProver_top ),
% 3.06/1.01      inference(demodulation,[status(thm)],[c_5497,c_3458]) ).
% 3.06/1.01  
% 3.06/1.01  cnf(c_561,plain,
% 3.06/1.01      ( sK0 != sK0 | k6_partfun1(sK0) = k6_partfun1(sK0) ),
% 3.06/1.01      inference(instantiation,[status(thm)],[c_547]) ).
% 3.06/1.01  
% 3.06/1.01  cnf(c_18,plain,
% 3.06/1.01      ( m1_subset_1(k6_partfun1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0))) ),
% 3.06/1.01      inference(cnf_transformation,[],[f64]) ).
% 3.06/1.01  
% 3.06/1.01  cnf(c_522,plain,
% 3.06/1.01      ( m1_subset_1(k6_partfun1(X0_49),k1_zfmisc_1(k2_zfmisc_1(X0_49,X0_49))) ),
% 3.06/1.01      inference(subtyping,[status(esa)],[c_18]) ).
% 3.06/1.01  
% 3.06/1.01  cnf(c_1024,plain,
% 3.06/1.01      ( m1_subset_1(k6_partfun1(X0_49),k1_zfmisc_1(k2_zfmisc_1(X0_49,X0_49))) = iProver_top ),
% 3.06/1.01      inference(predicate_to_equality,[status(thm)],[c_522]) ).
% 3.06/1.01  
% 3.06/1.01  cnf(c_8,plain,
% 3.06/1.01      ( r2_relset_1(X0,X1,X2,X2)
% 3.06/1.01      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
% 3.06/1.01      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ),
% 3.06/1.01      inference(cnf_transformation,[],[f54]) ).
% 3.06/1.01  
% 3.06/1.01  cnf(c_528,plain,
% 3.06/1.01      ( r2_relset_1(X0_49,X1_49,X0_48,X0_48)
% 3.06/1.01      | ~ m1_subset_1(X0_48,k1_zfmisc_1(k2_zfmisc_1(X0_49,X1_49)))
% 3.06/1.01      | ~ m1_subset_1(X1_48,k1_zfmisc_1(k2_zfmisc_1(X0_49,X1_49))) ),
% 3.06/1.01      inference(subtyping,[status(esa)],[c_8]) ).
% 3.06/1.01  
% 3.06/1.01  cnf(c_1018,plain,
% 3.06/1.01      ( r2_relset_1(X0_49,X1_49,X0_48,X0_48) = iProver_top
% 3.06/1.01      | m1_subset_1(X0_48,k1_zfmisc_1(k2_zfmisc_1(X0_49,X1_49))) != iProver_top
% 3.06/1.01      | m1_subset_1(X1_48,k1_zfmisc_1(k2_zfmisc_1(X0_49,X1_49))) != iProver_top ),
% 3.06/1.01      inference(predicate_to_equality,[status(thm)],[c_528]) ).
% 3.06/1.01  
% 3.06/1.01  cnf(c_1594,plain,
% 3.06/1.01      ( r2_relset_1(X0_49,X0_49,k6_partfun1(X0_49),k6_partfun1(X0_49)) = iProver_top
% 3.06/1.01      | m1_subset_1(X0_48,k1_zfmisc_1(k2_zfmisc_1(X0_49,X0_49))) != iProver_top ),
% 3.06/1.01      inference(superposition,[status(thm)],[c_1024,c_1018]) ).
% 3.06/1.01  
% 3.06/1.01  cnf(c_1605,plain,
% 3.06/1.01      ( r2_relset_1(sK0,sK0,k6_partfun1(sK0),k6_partfun1(sK0)) = iProver_top
% 3.06/1.01      | m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) != iProver_top ),
% 3.06/1.01      inference(instantiation,[status(thm)],[c_1594]) ).
% 3.06/1.01  
% 3.06/1.01  cnf(c_552,plain,
% 3.06/1.01      ( ~ r2_relset_1(X0_49,X1_49,X0_48,X1_48)
% 3.06/1.01      | r2_relset_1(X2_49,X3_49,X2_48,X3_48)
% 3.06/1.01      | X2_49 != X0_49
% 3.06/1.01      | X3_49 != X1_49
% 3.06/1.01      | X2_48 != X0_48
% 3.06/1.01      | X3_48 != X1_48 ),
% 3.06/1.01      theory(equality) ).
% 3.06/1.01  
% 3.06/1.01  cnf(c_2225,plain,
% 3.06/1.01      ( ~ r2_relset_1(X0_49,X1_49,X0_48,X1_48)
% 3.06/1.01      | r2_relset_1(X2_49,X3_49,k1_partfun1(X4_49,X5_49,X6_49,X7_49,k2_funct_1(sK1),X2_48),k6_partfun1(X8_49))
% 3.06/1.01      | X2_49 != X0_49
% 3.06/1.01      | X3_49 != X1_49
% 3.06/1.01      | k1_partfun1(X4_49,X5_49,X6_49,X7_49,k2_funct_1(sK1),X2_48) != X0_48
% 3.06/1.01      | k6_partfun1(X8_49) != X1_48 ),
% 3.06/1.01      inference(instantiation,[status(thm)],[c_552]) ).
% 3.06/1.01  
% 3.06/1.01  cnf(c_3066,plain,
% 3.06/1.01      ( ~ r2_relset_1(X0_49,X1_49,X0_48,k6_partfun1(X2_49))
% 3.06/1.01      | r2_relset_1(X3_49,X4_49,k1_partfun1(X5_49,X6_49,X7_49,X8_49,k2_funct_1(sK1),X1_48),k6_partfun1(X9_49))
% 3.06/1.01      | X3_49 != X0_49
% 3.06/1.01      | X4_49 != X1_49
% 3.06/1.01      | k1_partfun1(X5_49,X6_49,X7_49,X8_49,k2_funct_1(sK1),X1_48) != X0_48
% 3.06/1.01      | k6_partfun1(X9_49) != k6_partfun1(X2_49) ),
% 3.06/1.01      inference(instantiation,[status(thm)],[c_2225]) ).
% 3.06/1.01  
% 3.06/1.01  cnf(c_4035,plain,
% 3.06/1.01      ( r2_relset_1(X0_49,X1_49,k1_partfun1(X2_49,X3_49,X4_49,X5_49,k2_funct_1(sK1),X0_48),k6_partfun1(X6_49))
% 3.06/1.01      | ~ r2_relset_1(X7_49,X8_49,k6_partfun1(X9_49),k6_partfun1(X9_49))
% 3.06/1.01      | X0_49 != X7_49
% 3.06/1.01      | X1_49 != X8_49
% 3.06/1.01      | k1_partfun1(X2_49,X3_49,X4_49,X5_49,k2_funct_1(sK1),X0_48) != k6_partfun1(X9_49)
% 3.06/1.01      | k6_partfun1(X6_49) != k6_partfun1(X9_49) ),
% 3.06/1.01      inference(instantiation,[status(thm)],[c_3066]) ).
% 3.06/1.01  
% 3.06/1.01  cnf(c_4037,plain,
% 3.06/1.01      ( X0_49 != X1_49
% 3.06/1.01      | X2_49 != X3_49
% 3.06/1.01      | k1_partfun1(X4_49,X5_49,X6_49,X7_49,k2_funct_1(sK1),X0_48) != k6_partfun1(X8_49)
% 3.06/1.01      | k6_partfun1(X9_49) != k6_partfun1(X8_49)
% 3.06/1.01      | r2_relset_1(X0_49,X2_49,k1_partfun1(X4_49,X5_49,X6_49,X7_49,k2_funct_1(sK1),X0_48),k6_partfun1(X9_49)) = iProver_top
% 3.06/1.01      | r2_relset_1(X1_49,X3_49,k6_partfun1(X8_49),k6_partfun1(X8_49)) != iProver_top ),
% 3.06/1.01      inference(predicate_to_equality,[status(thm)],[c_4035]) ).
% 3.06/1.01  
% 3.06/1.01  cnf(c_4039,plain,
% 3.06/1.01      ( sK0 != sK0
% 3.06/1.01      | k1_partfun1(sK0,sK0,sK0,sK0,k2_funct_1(sK1),sK1) != k6_partfun1(sK0)
% 3.06/1.01      | k6_partfun1(sK0) != k6_partfun1(sK0)
% 3.06/1.01      | r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK0,sK0,sK0,k2_funct_1(sK1),sK1),k6_partfun1(sK0)) = iProver_top
% 3.06/1.01      | r2_relset_1(sK0,sK0,k6_partfun1(sK0),k6_partfun1(sK0)) != iProver_top ),
% 3.06/1.01      inference(instantiation,[status(thm)],[c_4037]) ).
% 3.06/1.01  
% 3.06/1.01  cnf(c_5962,plain,
% 3.06/1.01      ( r2_relset_1(sK0,sK0,k6_partfun1(k1_relat_1(sK1)),k6_partfun1(sK0)) != iProver_top ),
% 3.06/1.01      inference(global_propositional_subsumption,
% 3.06/1.01                [status(thm)],
% 3.06/1.01                [c_5500,c_25,c_24,c_23,c_22,c_29,c_561,c_573,c_577,c_583,
% 3.06/1.01                 c_595,c_601,c_628,c_1483,c_1605,c_1844,c_2165,c_2407,
% 3.06/1.01                 c_3179,c_3458,c_4039,c_4522]) ).
% 3.06/1.01  
% 3.06/1.01  cnf(c_6830,plain,
% 3.06/1.01      ( r2_relset_1(sK0,sK0,k6_partfun1(sK0),k6_partfun1(sK0)) != iProver_top ),
% 3.06/1.01      inference(demodulation,[status(thm)],[c_5246,c_5962]) ).
% 3.06/1.01  
% 3.06/1.01  cnf(contradiction,plain,
% 3.06/1.01      ( $false ),
% 3.06/1.01      inference(minisat,[status(thm)],[c_6830,c_1605,c_29]) ).
% 3.06/1.01  
% 3.06/1.01  
% 3.06/1.01  % SZS output end CNFRefutation for theBenchmark.p
% 3.06/1.01  
% 3.06/1.01  ------                               Statistics
% 3.06/1.01  
% 3.06/1.01  ------ General
% 3.06/1.01  
% 3.06/1.01  abstr_ref_over_cycles:                  0
% 3.06/1.01  abstr_ref_under_cycles:                 0
% 3.06/1.01  gc_basic_clause_elim:                   0
% 3.06/1.01  forced_gc_time:                         0
% 3.06/1.01  parsing_time:                           0.01
% 3.06/1.01  unif_index_cands_time:                  0.
% 3.06/1.01  unif_index_add_time:                    0.
% 3.06/1.01  orderings_time:                         0.
% 3.06/1.01  out_proof_time:                         0.016
% 3.06/1.01  total_time:                             0.266
% 3.06/1.01  num_of_symbols:                         55
% 3.06/1.01  num_of_terms:                           6597
% 3.06/1.01  
% 3.06/1.01  ------ Preprocessing
% 3.06/1.01  
% 3.06/1.01  num_of_splits:                          0
% 3.06/1.01  num_of_split_atoms:                     0
% 3.06/1.01  num_of_reused_defs:                     0
% 3.06/1.01  num_eq_ax_congr_red:                    8
% 3.06/1.01  num_of_sem_filtered_clauses:            1
% 3.06/1.01  num_of_subtypes:                        4
% 3.06/1.01  monotx_restored_types:                  1
% 3.06/1.01  sat_num_of_epr_types:                   0
% 3.06/1.01  sat_num_of_non_cyclic_types:            0
% 3.06/1.01  sat_guarded_non_collapsed_types:        1
% 3.06/1.01  num_pure_diseq_elim:                    0
% 3.06/1.01  simp_replaced_by:                       0
% 3.06/1.01  res_preprocessed:                       132
% 3.06/1.01  prep_upred:                             0
% 3.06/1.01  prep_unflattend:                        6
% 3.06/1.01  smt_new_axioms:                         0
% 3.06/1.01  pred_elim_cands:                        7
% 3.06/1.01  pred_elim:                              2
% 3.06/1.01  pred_elim_cl:                           3
% 3.06/1.01  pred_elim_cycles:                       4
% 3.06/1.01  merged_defs:                            0
% 3.06/1.01  merged_defs_ncl:                        0
% 3.06/1.01  bin_hyper_res:                          0
% 3.06/1.01  prep_cycles:                            4
% 3.06/1.01  pred_elim_time:                         0.002
% 3.06/1.01  splitting_time:                         0.
% 3.06/1.01  sem_filter_time:                        0.
% 3.06/1.01  monotx_time:                            0.001
% 3.06/1.01  subtype_inf_time:                       0.001
% 3.06/1.01  
% 3.06/1.01  ------ Problem properties
% 3.06/1.01  
% 3.06/1.01  clauses:                                22
% 3.06/1.01  conjectures:                            5
% 3.06/1.01  epr:                                    3
% 3.06/1.01  horn:                                   22
% 3.06/1.01  ground:                                 5
% 3.06/1.01  unary:                                  5
% 3.06/1.01  binary:                                 2
% 3.06/1.01  lits:                                   73
% 3.06/1.01  lits_eq:                                6
% 3.06/1.01  fd_pure:                                0
% 3.06/1.01  fd_pseudo:                              0
% 3.06/1.01  fd_cond:                                0
% 3.06/1.01  fd_pseudo_cond:                         1
% 3.06/1.01  ac_symbols:                             0
% 3.06/1.01  
% 3.06/1.01  ------ Propositional Solver
% 3.06/1.01  
% 3.06/1.01  prop_solver_calls:                      31
% 3.06/1.01  prop_fast_solver_calls:                 1229
% 3.06/1.01  smt_solver_calls:                       0
% 3.06/1.01  smt_fast_solver_calls:                  0
% 3.06/1.01  prop_num_of_clauses:                    2116
% 3.06/1.01  prop_preprocess_simplified:             6626
% 3.06/1.01  prop_fo_subsumed:                       74
% 3.06/1.01  prop_solver_time:                       0.
% 3.06/1.01  smt_solver_time:                        0.
% 3.06/1.01  smt_fast_solver_time:                   0.
% 3.06/1.01  prop_fast_solver_time:                  0.
% 3.06/1.01  prop_unsat_core_time:                   0.
% 3.06/1.01  
% 3.06/1.01  ------ QBF
% 3.06/1.01  
% 3.06/1.01  qbf_q_res:                              0
% 3.06/1.01  qbf_num_tautologies:                    0
% 3.06/1.01  qbf_prep_cycles:                        0
% 3.06/1.01  
% 3.06/1.01  ------ BMC1
% 3.06/1.01  
% 3.06/1.01  bmc1_current_bound:                     -1
% 3.06/1.01  bmc1_last_solved_bound:                 -1
% 3.06/1.01  bmc1_unsat_core_size:                   -1
% 3.06/1.01  bmc1_unsat_core_parents_size:           -1
% 3.06/1.01  bmc1_merge_next_fun:                    0
% 3.06/1.01  bmc1_unsat_core_clauses_time:           0.
% 3.06/1.01  
% 3.06/1.01  ------ Instantiation
% 3.06/1.01  
% 3.06/1.01  inst_num_of_clauses:                    761
% 3.06/1.01  inst_num_in_passive:                    300
% 3.06/1.01  inst_num_in_active:                     415
% 3.06/1.01  inst_num_in_unprocessed:                46
% 3.06/1.01  inst_num_of_loops:                      460
% 3.06/1.01  inst_num_of_learning_restarts:          0
% 3.06/1.01  inst_num_moves_active_passive:          40
% 3.06/1.01  inst_lit_activity:                      0
% 3.06/1.01  inst_lit_activity_moves:                0
% 3.06/1.01  inst_num_tautologies:                   0
% 3.06/1.01  inst_num_prop_implied:                  0
% 3.06/1.01  inst_num_existing_simplified:           0
% 3.06/1.01  inst_num_eq_res_simplified:             0
% 3.06/1.01  inst_num_child_elim:                    0
% 3.06/1.01  inst_num_of_dismatching_blockings:      712
% 3.06/1.01  inst_num_of_non_proper_insts:           1048
% 3.06/1.01  inst_num_of_duplicates:                 0
% 3.06/1.01  inst_inst_num_from_inst_to_res:         0
% 3.06/1.01  inst_dismatching_checking_time:         0.
% 3.06/1.01  
% 3.06/1.01  ------ Resolution
% 3.06/1.01  
% 3.06/1.01  res_num_of_clauses:                     0
% 3.06/1.01  res_num_in_passive:                     0
% 3.06/1.01  res_num_in_active:                      0
% 3.06/1.01  res_num_of_loops:                       136
% 3.06/1.01  res_forward_subset_subsumed:            89
% 3.06/1.01  res_backward_subset_subsumed:           4
% 3.06/1.01  res_forward_subsumed:                   0
% 3.06/1.01  res_backward_subsumed:                  0
% 3.06/1.01  res_forward_subsumption_resolution:     2
% 3.06/1.01  res_backward_subsumption_resolution:    0
% 3.06/1.01  res_clause_to_clause_subsumption:       365
% 3.06/1.01  res_orphan_elimination:                 0
% 3.06/1.01  res_tautology_del:                      112
% 3.06/1.01  res_num_eq_res_simplified:              0
% 3.06/1.01  res_num_sel_changes:                    0
% 3.06/1.01  res_moves_from_active_to_pass:          0
% 3.06/1.01  
% 3.06/1.01  ------ Superposition
% 3.06/1.01  
% 3.06/1.01  sup_time_total:                         0.
% 3.06/1.01  sup_time_generating:                    0.
% 3.06/1.01  sup_time_sim_full:                      0.
% 3.06/1.01  sup_time_sim_immed:                     0.
% 3.06/1.01  
% 3.06/1.01  sup_num_of_clauses:                     115
% 3.06/1.01  sup_num_in_active:                      78
% 3.06/1.01  sup_num_in_passive:                     37
% 3.06/1.01  sup_num_of_loops:                       91
% 3.06/1.01  sup_fw_superposition:                   86
% 3.06/1.01  sup_bw_superposition:                   61
% 3.06/1.01  sup_immediate_simplified:               58
% 3.06/1.01  sup_given_eliminated:                   0
% 3.06/1.01  comparisons_done:                       0
% 3.06/1.01  comparisons_avoided:                    0
% 3.06/1.01  
% 3.06/1.01  ------ Simplifications
% 3.06/1.01  
% 3.06/1.01  
% 3.06/1.01  sim_fw_subset_subsumed:                 9
% 3.06/1.01  sim_bw_subset_subsumed:                 3
% 3.06/1.01  sim_fw_subsumed:                        7
% 3.06/1.01  sim_bw_subsumed:                        0
% 3.06/1.01  sim_fw_subsumption_res:                 3
% 3.06/1.01  sim_bw_subsumption_res:                 0
% 3.06/1.01  sim_tautology_del:                      0
% 3.06/1.01  sim_eq_tautology_del:                   9
% 3.06/1.01  sim_eq_res_simp:                        0
% 3.06/1.01  sim_fw_demodulated:                     0
% 3.06/1.01  sim_bw_demodulated:                     12
% 3.06/1.01  sim_light_normalised:                   47
% 3.06/1.01  sim_joinable_taut:                      0
% 3.06/1.01  sim_joinable_simp:                      0
% 3.06/1.01  sim_ac_normalised:                      0
% 3.06/1.01  sim_smt_subsumption:                    0
% 3.06/1.01  
%------------------------------------------------------------------------------
