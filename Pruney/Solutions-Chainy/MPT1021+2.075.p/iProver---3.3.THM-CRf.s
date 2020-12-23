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
% DateTime   : Thu Dec  3 12:07:34 EST 2020

% Result     : Theorem 3.03s
% Output     : CNFRefutation 3.03s
% Verified   : 
% Statistics : Number of formulae       :  198 (1309 expanded)
%              Number of clauses        :  134 ( 426 expanded)
%              Number of leaves         :   20 ( 255 expanded)
%              Depth                    :   19
%              Number of atoms          :  680 (6267 expanded)
%              Number of equality atoms :  275 ( 639 expanded)
%              Maximal formula depth    :   12 (   5 average)
%              Maximal clause size      :   12 (   3 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f14,conjecture,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
        & v3_funct_2(X1,X0,X0)
        & v1_funct_2(X1,X0,X0)
        & v1_funct_1(X1) )
     => ( r2_relset_1(X0,X0,k1_partfun1(X0,X0,X0,X0,k2_funct_2(X0,X1),X1),k6_partfun1(X0))
        & r2_relset_1(X0,X0,k1_partfun1(X0,X0,X0,X0,X1,k2_funct_2(X0,X1)),k6_partfun1(X0)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f15,negated_conjecture,(
    ~ ! [X0,X1] :
        ( ( m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
          & v3_funct_2(X1,X0,X0)
          & v1_funct_2(X1,X0,X0)
          & v1_funct_1(X1) )
       => ( r2_relset_1(X0,X0,k1_partfun1(X0,X0,X0,X0,k2_funct_2(X0,X1),X1),k6_partfun1(X0))
          & r2_relset_1(X0,X0,k1_partfun1(X0,X0,X0,X0,X1,k2_funct_2(X0,X1)),k6_partfun1(X0)) ) ) ),
    inference(negated_conjecture,[],[f14])).

fof(f36,plain,(
    ? [X0,X1] :
      ( ( ~ r2_relset_1(X0,X0,k1_partfun1(X0,X0,X0,X0,k2_funct_2(X0,X1),X1),k6_partfun1(X0))
        | ~ r2_relset_1(X0,X0,k1_partfun1(X0,X0,X0,X0,X1,k2_funct_2(X0,X1)),k6_partfun1(X0)) )
      & m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
      & v3_funct_2(X1,X0,X0)
      & v1_funct_2(X1,X0,X0)
      & v1_funct_1(X1) ) ),
    inference(ennf_transformation,[],[f15])).

fof(f37,plain,(
    ? [X0,X1] :
      ( ( ~ r2_relset_1(X0,X0,k1_partfun1(X0,X0,X0,X0,k2_funct_2(X0,X1),X1),k6_partfun1(X0))
        | ~ r2_relset_1(X0,X0,k1_partfun1(X0,X0,X0,X0,X1,k2_funct_2(X0,X1)),k6_partfun1(X0)) )
      & m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
      & v3_funct_2(X1,X0,X0)
      & v1_funct_2(X1,X0,X0)
      & v1_funct_1(X1) ) ),
    inference(flattening,[],[f36])).

fof(f39,plain,
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

fof(f40,plain,
    ( ( ~ r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK0,sK0,sK0,k2_funct_2(sK0,sK1),sK1),k6_partfun1(sK0))
      | ~ r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK0,sK0,sK0,sK1,k2_funct_2(sK0,sK1)),k6_partfun1(sK0)) )
    & m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
    & v3_funct_2(sK1,sK0,sK0)
    & v1_funct_2(sK1,sK0,sK0)
    & v1_funct_1(sK1) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f37,f39])).

fof(f65,plain,(
    m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) ),
    inference(cnf_transformation,[],[f40])).

fof(f12,axiom,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
        & v3_funct_2(X1,X0,X0)
        & v1_funct_2(X1,X0,X0)
        & v1_funct_1(X1) )
     => k2_funct_1(X1) = k2_funct_2(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f34,plain,(
    ! [X0,X1] :
      ( k2_funct_1(X1) = k2_funct_2(X0,X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
      | ~ v3_funct_2(X1,X0,X0)
      | ~ v1_funct_2(X1,X0,X0)
      | ~ v1_funct_1(X1) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f35,plain,(
    ! [X0,X1] :
      ( k2_funct_1(X1) = k2_funct_2(X0,X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
      | ~ v3_funct_2(X1,X0,X0)
      | ~ v1_funct_2(X1,X0,X0)
      | ~ v1_funct_1(X1) ) ),
    inference(flattening,[],[f34])).

fof(f60,plain,(
    ! [X0,X1] :
      ( k2_funct_1(X1) = k2_funct_2(X0,X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
      | ~ v3_funct_2(X1,X0,X0)
      | ~ v1_funct_2(X1,X0,X0)
      | ~ v1_funct_1(X1) ) ),
    inference(cnf_transformation,[],[f35])).

fof(f62,plain,(
    v1_funct_1(sK1) ),
    inference(cnf_transformation,[],[f40])).

fof(f63,plain,(
    v1_funct_2(sK1,sK0,sK0) ),
    inference(cnf_transformation,[],[f40])).

fof(f64,plain,(
    v3_funct_2(sK1,sK0,sK0) ),
    inference(cnf_transformation,[],[f40])).

fof(f9,axiom,(
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

fof(f30,plain,(
    ! [X0,X1] :
      ( ( m1_subset_1(k2_funct_2(X0,X1),k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
        & v3_funct_2(k2_funct_2(X0,X1),X0,X0)
        & v1_funct_2(k2_funct_2(X0,X1),X0,X0)
        & v1_funct_1(k2_funct_2(X0,X1)) )
      | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
      | ~ v3_funct_2(X1,X0,X0)
      | ~ v1_funct_2(X1,X0,X0)
      | ~ v1_funct_1(X1) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f31,plain,(
    ! [X0,X1] :
      ( ( m1_subset_1(k2_funct_2(X0,X1),k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
        & v3_funct_2(k2_funct_2(X0,X1),X0,X0)
        & v1_funct_2(k2_funct_2(X0,X1),X0,X0)
        & v1_funct_1(k2_funct_2(X0,X1)) )
      | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
      | ~ v3_funct_2(X1,X0,X0)
      | ~ v1_funct_2(X1,X0,X0)
      | ~ v1_funct_1(X1) ) ),
    inference(flattening,[],[f30])).

fof(f57,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k2_funct_2(X0,X1),k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
      | ~ v3_funct_2(X1,X0,X0)
      | ~ v1_funct_2(X1,X0,X0)
      | ~ v1_funct_1(X1) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f11,axiom,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( ( m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
        & v1_funct_1(X5)
        & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_1(X4) )
     => k5_relat_1(X4,X5) = k1_partfun1(X0,X1,X2,X3,X4,X5) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f32,plain,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( k5_relat_1(X4,X5) = k1_partfun1(X0,X1,X2,X3,X4,X5)
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ v1_funct_1(X5)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X4) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f33,plain,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( k5_relat_1(X4,X5) = k1_partfun1(X0,X1,X2,X3,X4,X5)
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ v1_funct_1(X5)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X4) ) ),
    inference(flattening,[],[f32])).

fof(f59,plain,(
    ! [X4,X2,X0,X5,X3,X1] :
      ( k5_relat_1(X4,X5) = k1_partfun1(X0,X1,X2,X3,X4,X5)
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ v1_funct_1(X5)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X4) ) ),
    inference(cnf_transformation,[],[f33])).

fof(f4,axiom,(
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
    inference(ennf_transformation,[],[f4])).

fof(f22,plain,(
    ! [X0] :
      ( ( k5_relat_1(k2_funct_1(X0),X0) = k6_relat_1(k2_relat_1(X0))
        & k5_relat_1(X0,k2_funct_1(X0)) = k6_relat_1(k1_relat_1(X0)) )
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f21])).

fof(f45,plain,(
    ! [X0] :
      ( k5_relat_1(X0,k2_funct_1(X0)) = k6_relat_1(k1_relat_1(X0))
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f13,axiom,(
    ! [X0] : k6_relat_1(X0) = k6_partfun1(X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f61,plain,(
    ! [X0] : k6_relat_1(X0) = k6_partfun1(X0) ),
    inference(cnf_transformation,[],[f13])).

fof(f68,plain,(
    ! [X0] :
      ( k5_relat_1(X0,k2_funct_1(X0)) = k6_partfun1(k1_relat_1(X0))
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(definition_unfolding,[],[f45,f61])).

fof(f2,axiom,(
    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f42,plain,(
    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1)) ),
    inference(cnf_transformation,[],[f2])).

fof(f7,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => ( ( v3_funct_2(X2,X0,X1)
          & v1_funct_1(X2) )
       => ( v2_funct_2(X2,X1)
          & v2_funct_1(X2)
          & v1_funct_1(X2) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f26,plain,(
    ! [X0,X1,X2] :
      ( ( v2_funct_2(X2,X1)
        & v2_funct_1(X2)
        & v1_funct_1(X2) )
      | ~ v3_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f27,plain,(
    ! [X0,X1,X2] :
      ( ( v2_funct_2(X2,X1)
        & v2_funct_1(X2)
        & v1_funct_1(X2) )
      | ~ v3_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(flattening,[],[f26])).

fof(f50,plain,(
    ! [X2,X0,X1] :
      ( v2_funct_1(X2)
      | ~ v3_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f1,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(X0))
         => v1_relat_1(X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f18,plain,(
    ! [X0] :
      ( ! [X1] :
          ( v1_relat_1(X1)
          | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f41,plain,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f54,plain,(
    ! [X0,X1] :
      ( v1_funct_1(k2_funct_2(X0,X1))
      | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
      | ~ v3_funct_2(X1,X0,X0)
      | ~ v1_funct_2(X1,X0,X0)
      | ~ v1_funct_1(X1) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f66,plain,
    ( ~ r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK0,sK0,sK0,k2_funct_2(sK0,sK1),sK1),k6_partfun1(sK0))
    | ~ r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK0,sK0,sK0,sK1,k2_funct_2(sK0,sK1)),k6_partfun1(sK0)) ),
    inference(cnf_transformation,[],[f40])).

fof(f46,plain,(
    ! [X0] :
      ( k5_relat_1(k2_funct_1(X0),X0) = k6_relat_1(k2_relat_1(X0))
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f67,plain,(
    ! [X0] :
      ( k5_relat_1(k2_funct_1(X0),X0) = k6_partfun1(k2_relat_1(X0))
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(definition_unfolding,[],[f46,f61])).

fof(f51,plain,(
    ! [X2,X0,X1] :
      ( v2_funct_2(X2,X1)
      | ~ v3_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f8,axiom,(
    ! [X0,X1] :
      ( ( v5_relat_1(X1,X0)
        & v1_relat_1(X1) )
     => ( v2_funct_2(X1,X0)
      <=> k2_relat_1(X1) = X0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f28,plain,(
    ! [X0,X1] :
      ( ( v2_funct_2(X1,X0)
      <=> k2_relat_1(X1) = X0 )
      | ~ v5_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f29,plain,(
    ! [X0,X1] :
      ( ( v2_funct_2(X1,X0)
      <=> k2_relat_1(X1) = X0 )
      | ~ v5_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f28])).

fof(f38,plain,(
    ! [X0,X1] :
      ( ( ( v2_funct_2(X1,X0)
          | k2_relat_1(X1) != X0 )
        & ( k2_relat_1(X1) = X0
          | ~ v2_funct_2(X1,X0) ) )
      | ~ v5_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(nnf_transformation,[],[f29])).

fof(f52,plain,(
    ! [X0,X1] :
      ( k2_relat_1(X1) = X0
      | ~ v2_funct_2(X1,X0)
      | ~ v5_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f38])).

fof(f5,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => ( v5_relat_1(X2,X1)
        & v4_relat_1(X2,X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f17,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => v5_relat_1(X2,X1) ) ),
    inference(pure_predicate_removal,[],[f5])).

fof(f23,plain,(
    ! [X0,X1,X2] :
      ( v5_relat_1(X2,X1)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f17])).

fof(f47,plain,(
    ! [X2,X0,X1] :
      ( v5_relat_1(X2,X1)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f10,axiom,(
    ! [X0] :
      ( m1_subset_1(k6_partfun1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
      & v1_partfun1(k6_partfun1(X0),X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f16,plain,(
    ! [X0] : m1_subset_1(k6_partfun1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0))) ),
    inference(pure_predicate_removal,[],[f10])).

fof(f58,plain,(
    ! [X0] : m1_subset_1(k6_partfun1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0))) ),
    inference(cnf_transformation,[],[f16])).

fof(f6,axiom,(
    ! [X0,X1,X2,X3] :
      ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) )
     => r2_relset_1(X0,X1,X2,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f24,plain,(
    ! [X0,X1,X2,X3] :
      ( r2_relset_1(X0,X1,X2,X2)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f25,plain,(
    ! [X0,X1,X2,X3] :
      ( r2_relset_1(X0,X1,X2,X2)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(flattening,[],[f24])).

fof(f48,plain,(
    ! [X2,X0,X3,X1] :
      ( r2_relset_1(X0,X1,X2,X2)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f3,axiom,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ( v2_funct_1(X0)
       => ( k2_relat_1(k2_funct_1(X0)) = k1_relat_1(X0)
          & k2_relat_1(X0) = k1_relat_1(k2_funct_1(X0)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f19,plain,(
    ! [X0] :
      ( ( k2_relat_1(k2_funct_1(X0)) = k1_relat_1(X0)
        & k2_relat_1(X0) = k1_relat_1(k2_funct_1(X0)) )
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f20,plain,(
    ! [X0] :
      ( ( k2_relat_1(k2_funct_1(X0)) = k1_relat_1(X0)
        & k2_relat_1(X0) = k1_relat_1(k2_funct_1(X0)) )
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f19])).

fof(f44,plain,(
    ! [X0] :
      ( k2_relat_1(k2_funct_1(X0)) = k1_relat_1(X0)
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f56,plain,(
    ! [X0,X1] :
      ( v3_funct_2(k2_funct_2(X0,X1),X0,X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
      | ~ v3_funct_2(X1,X0,X0)
      | ~ v1_funct_2(X1,X0,X0)
      | ~ v1_funct_1(X1) ) ),
    inference(cnf_transformation,[],[f31])).

cnf(c_21,negated_conjecture,
    ( m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) ),
    inference(cnf_transformation,[],[f65])).

cnf(c_690,negated_conjecture,
    ( m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) ),
    inference(subtyping,[status(esa)],[c_21])).

cnf(c_1161,plain,
    ( m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_690])).

cnf(c_19,plain,
    ( ~ v1_funct_2(X0,X1,X1)
    | ~ v3_funct_2(X0,X1,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X1)))
    | ~ v1_funct_1(X0)
    | k2_funct_2(X1,X0) = k2_funct_1(X0) ),
    inference(cnf_transformation,[],[f60])).

cnf(c_692,plain,
    ( ~ v1_funct_2(X0_48,X0_49,X0_49)
    | ~ v3_funct_2(X0_48,X0_49,X0_49)
    | ~ m1_subset_1(X0_48,k1_zfmisc_1(k2_zfmisc_1(X0_49,X0_49)))
    | ~ v1_funct_1(X0_48)
    | k2_funct_2(X0_49,X0_48) = k2_funct_1(X0_48) ),
    inference(subtyping,[status(esa)],[c_19])).

cnf(c_1159,plain,
    ( k2_funct_2(X0_49,X0_48) = k2_funct_1(X0_48)
    | v1_funct_2(X0_48,X0_49,X0_49) != iProver_top
    | v3_funct_2(X0_48,X0_49,X0_49) != iProver_top
    | m1_subset_1(X0_48,k1_zfmisc_1(k2_zfmisc_1(X0_49,X0_49))) != iProver_top
    | v1_funct_1(X0_48) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_692])).

cnf(c_1993,plain,
    ( k2_funct_2(sK0,sK1) = k2_funct_1(sK1)
    | v1_funct_2(sK1,sK0,sK0) != iProver_top
    | v3_funct_2(sK1,sK0,sK0) != iProver_top
    | v1_funct_1(sK1) != iProver_top ),
    inference(superposition,[status(thm)],[c_1161,c_1159])).

cnf(c_24,negated_conjecture,
    ( v1_funct_1(sK1) ),
    inference(cnf_transformation,[],[f62])).

cnf(c_23,negated_conjecture,
    ( v1_funct_2(sK1,sK0,sK0) ),
    inference(cnf_transformation,[],[f63])).

cnf(c_22,negated_conjecture,
    ( v3_funct_2(sK1,sK0,sK0) ),
    inference(cnf_transformation,[],[f64])).

cnf(c_782,plain,
    ( ~ v1_funct_2(sK1,sK0,sK0)
    | ~ v3_funct_2(sK1,sK0,sK0)
    | ~ m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
    | ~ v1_funct_1(sK1)
    | k2_funct_2(sK0,sK1) = k2_funct_1(sK1) ),
    inference(instantiation,[status(thm)],[c_692])).

cnf(c_2364,plain,
    ( k2_funct_2(sK0,sK1) = k2_funct_1(sK1) ),
    inference(global_propositional_subsumption,[status(thm)],[c_1993,c_24,c_23,c_22,c_21,c_782])).

cnf(c_13,plain,
    ( ~ v1_funct_2(X0,X1,X1)
    | ~ v3_funct_2(X0,X1,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X1)))
    | m1_subset_1(k2_funct_2(X1,X0),k1_zfmisc_1(k2_zfmisc_1(X1,X1)))
    | ~ v1_funct_1(X0) ),
    inference(cnf_transformation,[],[f57])).

cnf(c_698,plain,
    ( ~ v1_funct_2(X0_48,X0_49,X0_49)
    | ~ v3_funct_2(X0_48,X0_49,X0_49)
    | ~ m1_subset_1(X0_48,k1_zfmisc_1(k2_zfmisc_1(X0_49,X0_49)))
    | m1_subset_1(k2_funct_2(X0_49,X0_48),k1_zfmisc_1(k2_zfmisc_1(X0_49,X0_49)))
    | ~ v1_funct_1(X0_48) ),
    inference(subtyping,[status(esa)],[c_13])).

cnf(c_1153,plain,
    ( v1_funct_2(X0_48,X0_49,X0_49) != iProver_top
    | v3_funct_2(X0_48,X0_49,X0_49) != iProver_top
    | m1_subset_1(X0_48,k1_zfmisc_1(k2_zfmisc_1(X0_49,X0_49))) != iProver_top
    | m1_subset_1(k2_funct_2(X0_49,X0_48),k1_zfmisc_1(k2_zfmisc_1(X0_49,X0_49))) = iProver_top
    | v1_funct_1(X0_48) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_698])).

cnf(c_2701,plain,
    ( v1_funct_2(sK1,sK0,sK0) != iProver_top
    | v3_funct_2(sK1,sK0,sK0) != iProver_top
    | m1_subset_1(k2_funct_1(sK1),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) = iProver_top
    | m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) != iProver_top
    | v1_funct_1(sK1) != iProver_top ),
    inference(superposition,[status(thm)],[c_2364,c_1153])).

cnf(c_25,plain,
    ( v1_funct_1(sK1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_24])).

cnf(c_26,plain,
    ( v1_funct_2(sK1,sK0,sK0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_23])).

cnf(c_27,plain,
    ( v3_funct_2(sK1,sK0,sK0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_22])).

cnf(c_28,plain,
    ( m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_21])).

cnf(c_3965,plain,
    ( m1_subset_1(k2_funct_1(sK1),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_2701,c_25,c_26,c_27,c_28])).

cnf(c_18,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X4,X5)))
    | ~ v1_funct_1(X0)
    | ~ v1_funct_1(X3)
    | k1_partfun1(X4,X5,X1,X2,X3,X0) = k5_relat_1(X3,X0) ),
    inference(cnf_transformation,[],[f59])).

cnf(c_693,plain,
    ( ~ m1_subset_1(X0_48,k1_zfmisc_1(k2_zfmisc_1(X0_49,X1_49)))
    | ~ m1_subset_1(X1_48,k1_zfmisc_1(k2_zfmisc_1(X2_49,X3_49)))
    | ~ v1_funct_1(X0_48)
    | ~ v1_funct_1(X1_48)
    | k1_partfun1(X2_49,X3_49,X0_49,X1_49,X1_48,X0_48) = k5_relat_1(X1_48,X0_48) ),
    inference(subtyping,[status(esa)],[c_18])).

cnf(c_1158,plain,
    ( k1_partfun1(X0_49,X1_49,X2_49,X3_49,X0_48,X1_48) = k5_relat_1(X0_48,X1_48)
    | m1_subset_1(X1_48,k1_zfmisc_1(k2_zfmisc_1(X2_49,X3_49))) != iProver_top
    | m1_subset_1(X0_48,k1_zfmisc_1(k2_zfmisc_1(X0_49,X1_49))) != iProver_top
    | v1_funct_1(X0_48) != iProver_top
    | v1_funct_1(X1_48) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_693])).

cnf(c_2849,plain,
    ( k1_partfun1(sK0,sK0,X0_49,X1_49,sK1,X0_48) = k5_relat_1(sK1,X0_48)
    | m1_subset_1(X0_48,k1_zfmisc_1(k2_zfmisc_1(X0_49,X1_49))) != iProver_top
    | v1_funct_1(X0_48) != iProver_top
    | v1_funct_1(sK1) != iProver_top ),
    inference(superposition,[status(thm)],[c_1161,c_1158])).

cnf(c_3004,plain,
    ( v1_funct_1(X0_48) != iProver_top
    | m1_subset_1(X0_48,k1_zfmisc_1(k2_zfmisc_1(X0_49,X1_49))) != iProver_top
    | k1_partfun1(sK0,sK0,X0_49,X1_49,sK1,X0_48) = k5_relat_1(sK1,X0_48) ),
    inference(global_propositional_subsumption,[status(thm)],[c_2849,c_25])).

cnf(c_3005,plain,
    ( k1_partfun1(sK0,sK0,X0_49,X1_49,sK1,X0_48) = k5_relat_1(sK1,X0_48)
    | m1_subset_1(X0_48,k1_zfmisc_1(k2_zfmisc_1(X0_49,X1_49))) != iProver_top
    | v1_funct_1(X0_48) != iProver_top ),
    inference(renaming,[status(thm)],[c_3004])).

cnf(c_3970,plain,
    ( k1_partfun1(sK0,sK0,sK0,sK0,sK1,k2_funct_1(sK1)) = k5_relat_1(sK1,k2_funct_1(sK1))
    | v1_funct_1(k2_funct_1(sK1)) != iProver_top ),
    inference(superposition,[status(thm)],[c_3965,c_3005])).

cnf(c_687,negated_conjecture,
    ( v1_funct_1(sK1) ),
    inference(subtyping,[status(esa)],[c_24])).

cnf(c_1164,plain,
    ( v1_funct_1(sK1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_687])).

cnf(c_5,plain,
    ( ~ v1_funct_1(X0)
    | ~ v2_funct_1(X0)
    | ~ v1_relat_1(X0)
    | k5_relat_1(X0,k2_funct_1(X0)) = k6_partfun1(k1_relat_1(X0)) ),
    inference(cnf_transformation,[],[f68])).

cnf(c_701,plain,
    ( ~ v1_funct_1(X0_48)
    | ~ v2_funct_1(X0_48)
    | ~ v1_relat_1(X0_48)
    | k5_relat_1(X0_48,k2_funct_1(X0_48)) = k6_partfun1(k1_relat_1(X0_48)) ),
    inference(subtyping,[status(esa)],[c_5])).

cnf(c_1150,plain,
    ( k5_relat_1(X0_48,k2_funct_1(X0_48)) = k6_partfun1(k1_relat_1(X0_48))
    | v1_funct_1(X0_48) != iProver_top
    | v2_funct_1(X0_48) != iProver_top
    | v1_relat_1(X0_48) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_701])).

cnf(c_1530,plain,
    ( k5_relat_1(sK1,k2_funct_1(sK1)) = k6_partfun1(k1_relat_1(sK1))
    | v2_funct_1(sK1) != iProver_top
    | v1_relat_1(sK1) != iProver_top ),
    inference(superposition,[status(thm)],[c_1164,c_1150])).

cnf(c_1,plain,
    ( v1_relat_1(k2_zfmisc_1(X0,X1)) ),
    inference(cnf_transformation,[],[f42])).

cnf(c_83,plain,
    ( v1_relat_1(k2_zfmisc_1(sK0,sK0)) ),
    inference(instantiation,[status(thm)],[c_1])).

cnf(c_757,plain,
    ( ~ v1_funct_1(sK1)
    | ~ v2_funct_1(sK1)
    | ~ v1_relat_1(sK1)
    | k5_relat_1(sK1,k2_funct_1(sK1)) = k6_partfun1(k1_relat_1(sK1)) ),
    inference(instantiation,[status(thm)],[c_701])).

cnf(c_9,plain,
    ( ~ v3_funct_2(X0,X1,X2)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ v1_funct_1(X0)
    | v2_funct_1(X0) ),
    inference(cnf_transformation,[],[f50])).

cnf(c_699,plain,
    ( ~ v3_funct_2(X0_48,X0_49,X1_49)
    | ~ m1_subset_1(X0_48,k1_zfmisc_1(k2_zfmisc_1(X0_49,X1_49)))
    | ~ v1_funct_1(X0_48)
    | v2_funct_1(X0_48) ),
    inference(subtyping,[status(esa)],[c_9])).

cnf(c_763,plain,
    ( ~ v3_funct_2(sK1,sK0,sK0)
    | ~ m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
    | ~ v1_funct_1(sK1)
    | v2_funct_1(sK1) ),
    inference(instantiation,[status(thm)],[c_699])).

cnf(c_0,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | ~ v1_relat_1(X1)
    | v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f41])).

cnf(c_706,plain,
    ( ~ m1_subset_1(X0_48,k1_zfmisc_1(X1_48))
    | ~ v1_relat_1(X1_48)
    | v1_relat_1(X0_48) ),
    inference(subtyping,[status(esa)],[c_0])).

cnf(c_1352,plain,
    ( ~ m1_subset_1(X0_48,k1_zfmisc_1(k2_zfmisc_1(X0_49,X1_49)))
    | v1_relat_1(X0_48)
    | ~ v1_relat_1(k2_zfmisc_1(X0_49,X1_49)) ),
    inference(instantiation,[status(thm)],[c_706])).

cnf(c_1354,plain,
    ( ~ m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
    | ~ v1_relat_1(k2_zfmisc_1(sK0,sK0))
    | v1_relat_1(sK1) ),
    inference(instantiation,[status(thm)],[c_1352])).

cnf(c_1788,plain,
    ( k5_relat_1(sK1,k2_funct_1(sK1)) = k6_partfun1(k1_relat_1(sK1)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_1530,c_24,c_22,c_21,c_83,c_757,c_763,c_1354])).

cnf(c_4045,plain,
    ( k1_partfun1(sK0,sK0,sK0,sK0,sK1,k2_funct_1(sK1)) = k6_partfun1(k1_relat_1(sK1))
    | v1_funct_1(k2_funct_1(sK1)) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_3970,c_1788])).

cnf(c_16,plain,
    ( ~ v1_funct_2(X0,X1,X1)
    | ~ v3_funct_2(X0,X1,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X1)))
    | ~ v1_funct_1(X0)
    | v1_funct_1(k2_funct_2(X1,X0)) ),
    inference(cnf_transformation,[],[f54])).

cnf(c_695,plain,
    ( ~ v1_funct_2(X0_48,X0_49,X0_49)
    | ~ v3_funct_2(X0_48,X0_49,X0_49)
    | ~ m1_subset_1(X0_48,k1_zfmisc_1(k2_zfmisc_1(X0_49,X0_49)))
    | ~ v1_funct_1(X0_48)
    | v1_funct_1(k2_funct_2(X0_49,X0_48)) ),
    inference(subtyping,[status(esa)],[c_16])).

cnf(c_1156,plain,
    ( v1_funct_2(X0_48,X0_49,X0_49) != iProver_top
    | v3_funct_2(X0_48,X0_49,X0_49) != iProver_top
    | m1_subset_1(X0_48,k1_zfmisc_1(k2_zfmisc_1(X0_49,X0_49))) != iProver_top
    | v1_funct_1(X0_48) != iProver_top
    | v1_funct_1(k2_funct_2(X0_49,X0_48)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_695])).

cnf(c_1965,plain,
    ( v1_funct_2(sK1,sK0,sK0) != iProver_top
    | v3_funct_2(sK1,sK0,sK0) != iProver_top
    | v1_funct_1(k2_funct_2(sK0,sK1)) = iProver_top
    | v1_funct_1(sK1) != iProver_top ),
    inference(superposition,[status(thm)],[c_1161,c_1156])).

cnf(c_774,plain,
    ( v1_funct_2(X0_48,X0_49,X0_49) != iProver_top
    | v3_funct_2(X0_48,X0_49,X0_49) != iProver_top
    | m1_subset_1(X0_48,k1_zfmisc_1(k2_zfmisc_1(X0_49,X0_49))) != iProver_top
    | v1_funct_1(X0_48) != iProver_top
    | v1_funct_1(k2_funct_2(X0_49,X0_48)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_695])).

cnf(c_776,plain,
    ( v1_funct_2(sK1,sK0,sK0) != iProver_top
    | v3_funct_2(sK1,sK0,sK0) != iProver_top
    | m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) != iProver_top
    | v1_funct_1(k2_funct_2(sK0,sK1)) = iProver_top
    | v1_funct_1(sK1) != iProver_top ),
    inference(instantiation,[status(thm)],[c_774])).

cnf(c_2274,plain,
    ( v1_funct_1(k2_funct_2(sK0,sK1)) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_1965,c_25,c_26,c_27,c_28,c_776])).

cnf(c_2367,plain,
    ( v1_funct_1(k2_funct_1(sK1)) = iProver_top ),
    inference(demodulation,[status(thm)],[c_2364,c_2274])).

cnf(c_4134,plain,
    ( k1_partfun1(sK0,sK0,sK0,sK0,sK1,k2_funct_1(sK1)) = k6_partfun1(k1_relat_1(sK1)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_4045,c_2367])).

cnf(c_20,negated_conjecture,
    ( ~ r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK0,sK0,sK0,k2_funct_2(sK0,sK1),sK1),k6_partfun1(sK0))
    | ~ r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK0,sK0,sK0,sK1,k2_funct_2(sK0,sK1)),k6_partfun1(sK0)) ),
    inference(cnf_transformation,[],[f66])).

cnf(c_691,negated_conjecture,
    ( ~ r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK0,sK0,sK0,k2_funct_2(sK0,sK1),sK1),k6_partfun1(sK0))
    | ~ r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK0,sK0,sK0,sK1,k2_funct_2(sK0,sK1)),k6_partfun1(sK0)) ),
    inference(subtyping,[status(esa)],[c_20])).

cnf(c_1160,plain,
    ( r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK0,sK0,sK0,k2_funct_2(sK0,sK1),sK1),k6_partfun1(sK0)) != iProver_top
    | r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK0,sK0,sK0,sK1,k2_funct_2(sK0,sK1)),k6_partfun1(sK0)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_691])).

cnf(c_2368,plain,
    ( r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK0,sK0,sK0,k2_funct_1(sK1),sK1),k6_partfun1(sK0)) != iProver_top
    | r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK0,sK0,sK0,sK1,k2_funct_1(sK1)),k6_partfun1(sK0)) != iProver_top ),
    inference(demodulation,[status(thm)],[c_2364,c_1160])).

cnf(c_4137,plain,
    ( r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK0,sK0,sK0,k2_funct_1(sK1),sK1),k6_partfun1(sK0)) != iProver_top
    | r2_relset_1(sK0,sK0,k6_partfun1(k1_relat_1(sK1)),k6_partfun1(sK0)) != iProver_top ),
    inference(demodulation,[status(thm)],[c_4134,c_2368])).

cnf(c_721,plain,
    ( X0_49 != X1_49
    | k6_partfun1(X0_49) = k6_partfun1(X1_49) ),
    theory(equality)).

cnf(c_735,plain,
    ( sK0 != sK0
    | k6_partfun1(sK0) = k6_partfun1(sK0) ),
    inference(instantiation,[status(thm)],[c_721])).

cnf(c_709,plain,
    ( X0_49 = X0_49 ),
    theory(equality)).

cnf(c_743,plain,
    ( sK0 = sK0 ),
    inference(instantiation,[status(thm)],[c_709])).

cnf(c_4,plain,
    ( ~ v1_funct_1(X0)
    | ~ v2_funct_1(X0)
    | ~ v1_relat_1(X0)
    | k5_relat_1(k2_funct_1(X0),X0) = k6_partfun1(k2_relat_1(X0)) ),
    inference(cnf_transformation,[],[f67])).

cnf(c_702,plain,
    ( ~ v1_funct_1(X0_48)
    | ~ v2_funct_1(X0_48)
    | ~ v1_relat_1(X0_48)
    | k5_relat_1(k2_funct_1(X0_48),X0_48) = k6_partfun1(k2_relat_1(X0_48)) ),
    inference(subtyping,[status(esa)],[c_4])).

cnf(c_754,plain,
    ( ~ v1_funct_1(sK1)
    | ~ v2_funct_1(sK1)
    | ~ v1_relat_1(sK1)
    | k5_relat_1(k2_funct_1(sK1),sK1) = k6_partfun1(k2_relat_1(sK1)) ),
    inference(instantiation,[status(thm)],[c_702])).

cnf(c_8,plain,
    ( ~ v3_funct_2(X0,X1,X2)
    | v2_funct_2(X0,X2)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ v1_funct_1(X0) ),
    inference(cnf_transformation,[],[f51])).

cnf(c_12,plain,
    ( ~ v2_funct_2(X0,X1)
    | ~ v5_relat_1(X0,X1)
    | ~ v1_relat_1(X0)
    | k2_relat_1(X0) = X1 ),
    inference(cnf_transformation,[],[f52])).

cnf(c_316,plain,
    ( ~ v3_funct_2(X0,X1,X2)
    | ~ v5_relat_1(X3,X4)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ v1_funct_1(X0)
    | ~ v1_relat_1(X3)
    | X3 != X0
    | X4 != X2
    | k2_relat_1(X3) = X4 ),
    inference(resolution_lifted,[status(thm)],[c_8,c_12])).

cnf(c_317,plain,
    ( ~ v3_funct_2(X0,X1,X2)
    | ~ v5_relat_1(X0,X2)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ v1_funct_1(X0)
    | ~ v1_relat_1(X0)
    | k2_relat_1(X0) = X2 ),
    inference(unflattening,[status(thm)],[c_316])).

cnf(c_6,plain,
    ( v5_relat_1(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) ),
    inference(cnf_transformation,[],[f47])).

cnf(c_333,plain,
    ( ~ v3_funct_2(X0,X1,X2)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ v1_funct_1(X0)
    | ~ v1_relat_1(X0)
    | k2_relat_1(X0) = X2 ),
    inference(forward_subsumption_resolution,[status(thm)],[c_317,c_6])).

cnf(c_686,plain,
    ( ~ v3_funct_2(X0_48,X0_49,X1_49)
    | ~ m1_subset_1(X0_48,k1_zfmisc_1(k2_zfmisc_1(X0_49,X1_49)))
    | ~ v1_funct_1(X0_48)
    | ~ v1_relat_1(X0_48)
    | k2_relat_1(X0_48) = X1_49 ),
    inference(subtyping,[status(esa)],[c_333])).

cnf(c_790,plain,
    ( ~ v3_funct_2(sK1,sK0,sK0)
    | ~ m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
    | ~ v1_funct_1(sK1)
    | ~ v1_relat_1(sK1)
    | k2_relat_1(sK1) = sK0 ),
    inference(instantiation,[status(thm)],[c_686])).

cnf(c_17,plain,
    ( m1_subset_1(k6_partfun1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0))) ),
    inference(cnf_transformation,[],[f58])).

cnf(c_694,plain,
    ( m1_subset_1(k6_partfun1(X0_49),k1_zfmisc_1(k2_zfmisc_1(X0_49,X0_49))) ),
    inference(subtyping,[status(esa)],[c_17])).

cnf(c_1157,plain,
    ( m1_subset_1(k6_partfun1(X0_49),k1_zfmisc_1(k2_zfmisc_1(X0_49,X0_49))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_694])).

cnf(c_7,plain,
    ( r2_relset_1(X0,X1,X2,X2)
    | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ),
    inference(cnf_transformation,[],[f48])).

cnf(c_700,plain,
    ( r2_relset_1(X0_49,X1_49,X0_48,X0_48)
    | ~ m1_subset_1(X0_48,k1_zfmisc_1(k2_zfmisc_1(X0_49,X1_49)))
    | ~ m1_subset_1(X1_48,k1_zfmisc_1(k2_zfmisc_1(X0_49,X1_49))) ),
    inference(subtyping,[status(esa)],[c_7])).

cnf(c_1151,plain,
    ( r2_relset_1(X0_49,X1_49,X0_48,X0_48) = iProver_top
    | m1_subset_1(X0_48,k1_zfmisc_1(k2_zfmisc_1(X0_49,X1_49))) != iProver_top
    | m1_subset_1(X1_48,k1_zfmisc_1(k2_zfmisc_1(X0_49,X1_49))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_700])).

cnf(c_1594,plain,
    ( r2_relset_1(X0_49,X0_49,k6_partfun1(X0_49),k6_partfun1(X0_49)) = iProver_top
    | m1_subset_1(X0_48,k1_zfmisc_1(k2_zfmisc_1(X0_49,X0_49))) != iProver_top ),
    inference(superposition,[status(thm)],[c_1157,c_1151])).

cnf(c_1605,plain,
    ( r2_relset_1(sK0,sK0,k6_partfun1(sK0),k6_partfun1(sK0)) = iProver_top
    | m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) != iProver_top ),
    inference(instantiation,[status(thm)],[c_1594])).

cnf(c_711,plain,
    ( X0_48 != X1_48
    | X2_48 != X1_48
    | X2_48 = X0_48 ),
    theory(equality)).

cnf(c_1457,plain,
    ( X0_48 != X1_48
    | k6_partfun1(sK0) != X1_48
    | k6_partfun1(sK0) = X0_48 ),
    inference(instantiation,[status(thm)],[c_711])).

cnf(c_1556,plain,
    ( X0_48 != k6_partfun1(X0_49)
    | k6_partfun1(sK0) = X0_48
    | k6_partfun1(sK0) != k6_partfun1(X0_49) ),
    inference(instantiation,[status(thm)],[c_1457])).

cnf(c_1640,plain,
    ( k5_relat_1(k2_funct_1(X0_48),X0_48) != k6_partfun1(k2_relat_1(X0_48))
    | k6_partfun1(sK0) = k5_relat_1(k2_funct_1(X0_48),X0_48)
    | k6_partfun1(sK0) != k6_partfun1(k2_relat_1(X0_48)) ),
    inference(instantiation,[status(thm)],[c_1556])).

cnf(c_1641,plain,
    ( k5_relat_1(k2_funct_1(sK1),sK1) != k6_partfun1(k2_relat_1(sK1))
    | k6_partfun1(sK0) = k5_relat_1(k2_funct_1(sK1),sK1)
    | k6_partfun1(sK0) != k6_partfun1(k2_relat_1(sK1)) ),
    inference(instantiation,[status(thm)],[c_1640])).

cnf(c_1459,plain,
    ( sK0 != X0_49
    | k6_partfun1(sK0) = k6_partfun1(X0_49) ),
    inference(instantiation,[status(thm)],[c_721])).

cnf(c_1941,plain,
    ( sK0 != k2_relat_1(X0_48)
    | k6_partfun1(sK0) = k6_partfun1(k2_relat_1(X0_48)) ),
    inference(instantiation,[status(thm)],[c_1459])).

cnf(c_1942,plain,
    ( sK0 != k2_relat_1(sK1)
    | k6_partfun1(sK0) = k6_partfun1(k2_relat_1(sK1)) ),
    inference(instantiation,[status(thm)],[c_1941])).

cnf(c_712,plain,
    ( X0_49 != X1_49
    | X2_49 != X1_49
    | X2_49 = X0_49 ),
    theory(equality)).

cnf(c_2089,plain,
    ( k2_relat_1(X0_48) != X0_49
    | sK0 != X0_49
    | sK0 = k2_relat_1(X0_48) ),
    inference(instantiation,[status(thm)],[c_712])).

cnf(c_2090,plain,
    ( k2_relat_1(sK1) != sK0
    | sK0 = k2_relat_1(sK1)
    | sK0 != sK0 ),
    inference(instantiation,[status(thm)],[c_2089])).

cnf(c_2375,plain,
    ( v1_funct_1(k2_funct_1(sK1)) ),
    inference(predicate_to_equality_rev,[status(thm)],[c_2367])).

cnf(c_2821,plain,
    ( ~ v1_funct_2(sK1,sK0,sK0)
    | ~ v3_funct_2(sK1,sK0,sK0)
    | m1_subset_1(k2_funct_1(sK1),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
    | ~ m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
    | ~ v1_funct_1(sK1) ),
    inference(predicate_to_equality_rev,[status(thm)],[c_2701])).

cnf(c_3220,plain,
    ( ~ m1_subset_1(X0_48,k1_zfmisc_1(k2_zfmisc_1(X0_49,X1_49)))
    | ~ m1_subset_1(k2_funct_1(sK1),k1_zfmisc_1(k2_zfmisc_1(X2_49,X3_49)))
    | ~ v1_funct_1(X0_48)
    | ~ v1_funct_1(k2_funct_1(sK1))
    | k1_partfun1(X2_49,X3_49,X0_49,X1_49,k2_funct_1(sK1),X0_48) = k5_relat_1(k2_funct_1(sK1),X0_48) ),
    inference(instantiation,[status(thm)],[c_693])).

cnf(c_3223,plain,
    ( ~ m1_subset_1(k2_funct_1(sK1),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
    | ~ m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
    | ~ v1_funct_1(k2_funct_1(sK1))
    | ~ v1_funct_1(sK1)
    | k1_partfun1(sK0,sK0,sK0,sK0,k2_funct_1(sK1),sK1) = k5_relat_1(k2_funct_1(sK1),sK1) ),
    inference(instantiation,[status(thm)],[c_3220])).

cnf(c_722,plain,
    ( ~ r2_relset_1(X0_49,X1_49,X0_48,X1_48)
    | r2_relset_1(X2_49,X3_49,X2_48,X3_48)
    | X2_49 != X0_49
    | X3_49 != X1_49
    | X2_48 != X0_48
    | X3_48 != X1_48 ),
    theory(equality)).

cnf(c_2202,plain,
    ( ~ r2_relset_1(X0_49,X1_49,X0_48,X1_48)
    | r2_relset_1(X2_49,X3_49,k1_partfun1(X4_49,X5_49,X6_49,X7_49,k2_funct_1(sK1),X2_48),k6_partfun1(X8_49))
    | X2_49 != X0_49
    | X3_49 != X1_49
    | k1_partfun1(X4_49,X5_49,X6_49,X7_49,k2_funct_1(sK1),X2_48) != X0_48
    | k6_partfun1(X8_49) != X1_48 ),
    inference(instantiation,[status(thm)],[c_722])).

cnf(c_3082,plain,
    ( ~ r2_relset_1(X0_49,X1_49,X0_48,k6_partfun1(X2_49))
    | r2_relset_1(X3_49,X4_49,k1_partfun1(X5_49,X6_49,X7_49,X8_49,k2_funct_1(sK1),X1_48),k6_partfun1(X9_49))
    | X3_49 != X0_49
    | X4_49 != X1_49
    | k1_partfun1(X5_49,X6_49,X7_49,X8_49,k2_funct_1(sK1),X1_48) != X0_48
    | k6_partfun1(X9_49) != k6_partfun1(X2_49) ),
    inference(instantiation,[status(thm)],[c_2202])).

cnf(c_4067,plain,
    ( r2_relset_1(X0_49,X1_49,k1_partfun1(X2_49,X3_49,X4_49,X5_49,k2_funct_1(sK1),X0_48),k6_partfun1(X6_49))
    | ~ r2_relset_1(X7_49,X8_49,k6_partfun1(X9_49),k6_partfun1(X9_49))
    | X0_49 != X7_49
    | X1_49 != X8_49
    | k1_partfun1(X2_49,X3_49,X4_49,X5_49,k2_funct_1(sK1),X0_48) != k6_partfun1(X9_49)
    | k6_partfun1(X6_49) != k6_partfun1(X9_49) ),
    inference(instantiation,[status(thm)],[c_3082])).

cnf(c_4069,plain,
    ( X0_49 != X1_49
    | X2_49 != X3_49
    | k1_partfun1(X4_49,X5_49,X6_49,X7_49,k2_funct_1(sK1),X0_48) != k6_partfun1(X8_49)
    | k6_partfun1(X9_49) != k6_partfun1(X8_49)
    | r2_relset_1(X0_49,X2_49,k1_partfun1(X4_49,X5_49,X6_49,X7_49,k2_funct_1(sK1),X0_48),k6_partfun1(X9_49)) = iProver_top
    | r2_relset_1(X1_49,X3_49,k6_partfun1(X8_49),k6_partfun1(X8_49)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_4067])).

cnf(c_4071,plain,
    ( sK0 != sK0
    | k1_partfun1(sK0,sK0,sK0,sK0,k2_funct_1(sK1),sK1) != k6_partfun1(sK0)
    | k6_partfun1(sK0) != k6_partfun1(sK0)
    | r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK0,sK0,sK0,k2_funct_1(sK1),sK1),k6_partfun1(sK0)) = iProver_top
    | r2_relset_1(sK0,sK0,k6_partfun1(sK0),k6_partfun1(sK0)) != iProver_top ),
    inference(instantiation,[status(thm)],[c_4069])).

cnf(c_1498,plain,
    ( X0_48 != X1_48
    | X0_48 = k6_partfun1(X0_49)
    | k6_partfun1(X0_49) != X1_48 ),
    inference(instantiation,[status(thm)],[c_711])).

cnf(c_2987,plain,
    ( X0_48 != k5_relat_1(k2_funct_1(X1_48),X1_48)
    | X0_48 = k6_partfun1(sK0)
    | k6_partfun1(sK0) != k5_relat_1(k2_funct_1(X1_48),X1_48) ),
    inference(instantiation,[status(thm)],[c_1498])).

cnf(c_4267,plain,
    ( k1_partfun1(X0_49,X1_49,X2_49,X3_49,k2_funct_1(sK1),sK1) != k5_relat_1(k2_funct_1(sK1),sK1)
    | k1_partfun1(X0_49,X1_49,X2_49,X3_49,k2_funct_1(sK1),sK1) = k6_partfun1(sK0)
    | k6_partfun1(sK0) != k5_relat_1(k2_funct_1(sK1),sK1) ),
    inference(instantiation,[status(thm)],[c_2987])).

cnf(c_4271,plain,
    ( k1_partfun1(sK0,sK0,sK0,sK0,k2_funct_1(sK1),sK1) != k5_relat_1(k2_funct_1(sK1),sK1)
    | k1_partfun1(sK0,sK0,sK0,sK0,k2_funct_1(sK1),sK1) = k6_partfun1(sK0)
    | k6_partfun1(sK0) != k5_relat_1(k2_funct_1(sK1),sK1) ),
    inference(instantiation,[status(thm)],[c_4267])).

cnf(c_4644,plain,
    ( r2_relset_1(sK0,sK0,k6_partfun1(k1_relat_1(sK1)),k6_partfun1(sK0)) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_4137,c_24,c_23,c_22,c_21,c_28,c_83,c_735,c_743,c_754,c_763,c_790,c_1354,c_1605,c_1641,c_1942,c_2090,c_2375,c_2821,c_3223,c_4071,c_4271])).

cnf(c_1165,plain,
    ( k2_relat_1(X0_48) = X0_49
    | v3_funct_2(X0_48,X1_49,X0_49) != iProver_top
    | m1_subset_1(X0_48,k1_zfmisc_1(k2_zfmisc_1(X1_49,X0_49))) != iProver_top
    | v1_funct_1(X0_48) != iProver_top
    | v1_relat_1(X0_48) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_686])).

cnf(c_3979,plain,
    ( k2_relat_1(k2_funct_1(sK1)) = sK0
    | v3_funct_2(k2_funct_1(sK1),sK0,sK0) != iProver_top
    | v1_funct_1(k2_funct_1(sK1)) != iProver_top
    | v1_relat_1(k2_funct_1(sK1)) != iProver_top ),
    inference(superposition,[status(thm)],[c_3965,c_1165])).

cnf(c_2,plain,
    ( ~ v1_funct_1(X0)
    | ~ v2_funct_1(X0)
    | ~ v1_relat_1(X0)
    | k2_relat_1(k2_funct_1(X0)) = k1_relat_1(X0) ),
    inference(cnf_transformation,[],[f44])).

cnf(c_704,plain,
    ( ~ v1_funct_1(X0_48)
    | ~ v2_funct_1(X0_48)
    | ~ v1_relat_1(X0_48)
    | k2_relat_1(k2_funct_1(X0_48)) = k1_relat_1(X0_48) ),
    inference(subtyping,[status(esa)],[c_2])).

cnf(c_1147,plain,
    ( k2_relat_1(k2_funct_1(X0_48)) = k1_relat_1(X0_48)
    | v1_funct_1(X0_48) != iProver_top
    | v2_funct_1(X0_48) != iProver_top
    | v1_relat_1(X0_48) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_704])).

cnf(c_1467,plain,
    ( k2_relat_1(k2_funct_1(sK1)) = k1_relat_1(sK1)
    | v2_funct_1(sK1) != iProver_top
    | v1_relat_1(sK1) != iProver_top ),
    inference(superposition,[status(thm)],[c_1164,c_1147])).

cnf(c_748,plain,
    ( ~ v1_funct_1(sK1)
    | ~ v2_funct_1(sK1)
    | ~ v1_relat_1(sK1)
    | k2_relat_1(k2_funct_1(sK1)) = k1_relat_1(sK1) ),
    inference(instantiation,[status(thm)],[c_704])).

cnf(c_1673,plain,
    ( k2_relat_1(k2_funct_1(sK1)) = k1_relat_1(sK1) ),
    inference(global_propositional_subsumption,[status(thm)],[c_1467,c_24,c_22,c_21,c_83,c_748,c_763,c_1354])).

cnf(c_3984,plain,
    ( k1_relat_1(sK1) = sK0
    | v3_funct_2(k2_funct_1(sK1),sK0,sK0) != iProver_top
    | v1_funct_1(k2_funct_1(sK1)) != iProver_top
    | v1_relat_1(k2_funct_1(sK1)) != iProver_top ),
    inference(demodulation,[status(thm)],[c_3979,c_1673])).

cnf(c_82,plain,
    ( v1_relat_1(k2_zfmisc_1(X0,X1)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1])).

cnf(c_84,plain,
    ( v1_relat_1(k2_zfmisc_1(sK0,sK0)) = iProver_top ),
    inference(instantiation,[status(thm)],[c_82])).

cnf(c_14,plain,
    ( ~ v1_funct_2(X0,X1,X1)
    | ~ v3_funct_2(X0,X1,X1)
    | v3_funct_2(k2_funct_2(X1,X0),X1,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X1)))
    | ~ v1_funct_1(X0) ),
    inference(cnf_transformation,[],[f56])).

cnf(c_697,plain,
    ( ~ v1_funct_2(X0_48,X0_49,X0_49)
    | ~ v3_funct_2(X0_48,X0_49,X0_49)
    | v3_funct_2(k2_funct_2(X0_49,X0_48),X0_49,X0_49)
    | ~ m1_subset_1(X0_48,k1_zfmisc_1(k2_zfmisc_1(X0_49,X0_49)))
    | ~ v1_funct_1(X0_48) ),
    inference(subtyping,[status(esa)],[c_14])).

cnf(c_1154,plain,
    ( v1_funct_2(X0_48,X0_49,X0_49) != iProver_top
    | v3_funct_2(X0_48,X0_49,X0_49) != iProver_top
    | v3_funct_2(k2_funct_2(X0_49,X0_48),X0_49,X0_49) = iProver_top
    | m1_subset_1(X0_48,k1_zfmisc_1(k2_zfmisc_1(X0_49,X0_49))) != iProver_top
    | v1_funct_1(X0_48) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_697])).

cnf(c_2133,plain,
    ( v1_funct_2(sK1,sK0,sK0) != iProver_top
    | v3_funct_2(k2_funct_2(sK0,sK1),sK0,sK0) = iProver_top
    | v3_funct_2(sK1,sK0,sK0) != iProver_top
    | v1_funct_1(sK1) != iProver_top ),
    inference(superposition,[status(thm)],[c_1161,c_1154])).

cnf(c_768,plain,
    ( v1_funct_2(X0_48,X0_49,X0_49) != iProver_top
    | v3_funct_2(X0_48,X0_49,X0_49) != iProver_top
    | v3_funct_2(k2_funct_2(X0_49,X0_48),X0_49,X0_49) = iProver_top
    | m1_subset_1(X0_48,k1_zfmisc_1(k2_zfmisc_1(X0_49,X0_49))) != iProver_top
    | v1_funct_1(X0_48) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_697])).

cnf(c_770,plain,
    ( v1_funct_2(sK1,sK0,sK0) != iProver_top
    | v3_funct_2(k2_funct_2(sK0,sK1),sK0,sK0) = iProver_top
    | v3_funct_2(sK1,sK0,sK0) != iProver_top
    | m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) != iProver_top
    | v1_funct_1(sK1) != iProver_top ),
    inference(instantiation,[status(thm)],[c_768])).

cnf(c_2378,plain,
    ( v3_funct_2(k2_funct_2(sK0,sK1),sK0,sK0) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_2133,c_25,c_26,c_27,c_28,c_770])).

cnf(c_2382,plain,
    ( v3_funct_2(k2_funct_1(sK1),sK0,sK0) = iProver_top ),
    inference(light_normalisation,[status(thm)],[c_2378,c_2364])).

cnf(c_1145,plain,
    ( m1_subset_1(X0_48,k1_zfmisc_1(X1_48)) != iProver_top
    | v1_relat_1(X1_48) != iProver_top
    | v1_relat_1(X0_48) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_706])).

cnf(c_3978,plain,
    ( v1_relat_1(k2_zfmisc_1(sK0,sK0)) != iProver_top
    | v1_relat_1(k2_funct_1(sK1)) = iProver_top ),
    inference(superposition,[status(thm)],[c_3965,c_1145])).

cnf(c_4140,plain,
    ( k1_relat_1(sK1) = sK0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_3984,c_84,c_2367,c_2382,c_3978])).

cnf(c_4648,plain,
    ( r2_relset_1(sK0,sK0,k6_partfun1(sK0),k6_partfun1(sK0)) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_4644,c_4140])).

cnf(c_1886,plain,
    ( r2_relset_1(X0_49,X0_49,k6_partfun1(X0_49),k6_partfun1(X0_49)) = iProver_top ),
    inference(superposition,[status(thm)],[c_1157,c_1594])).

cnf(c_4650,plain,
    ( $false ),
    inference(forward_subsumption_resolution,[status(thm)],[c_4648,c_1886])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.01/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : iproveropt_run.sh %d %s
% 0.13/0.34  % Computer   : n018.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 13:15:42 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running in FOF mode
% 3.03/1.01  % SZS status Started for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.03/1.01  
% 3.03/1.01  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 3.03/1.01  
% 3.03/1.01  ------  iProver source info
% 3.03/1.01  
% 3.03/1.01  git: date: 2020-06-30 10:37:57 +0100
% 3.03/1.01  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 3.03/1.01  git: non_committed_changes: false
% 3.03/1.01  git: last_make_outside_of_git: false
% 3.03/1.01  
% 3.03/1.01  ------ 
% 3.03/1.01  
% 3.03/1.01  ------ Input Options
% 3.03/1.01  
% 3.03/1.01  --out_options                           all
% 3.03/1.01  --tptp_safe_out                         true
% 3.03/1.01  --problem_path                          ""
% 3.03/1.01  --include_path                          ""
% 3.03/1.01  --clausifier                            res/vclausify_rel
% 3.03/1.01  --clausifier_options                    --mode clausify
% 3.03/1.01  --stdin                                 false
% 3.03/1.01  --stats_out                             all
% 3.03/1.01  
% 3.03/1.01  ------ General Options
% 3.03/1.01  
% 3.03/1.01  --fof                                   false
% 3.03/1.01  --time_out_real                         305.
% 3.03/1.01  --time_out_virtual                      -1.
% 3.03/1.01  --symbol_type_check                     false
% 3.03/1.01  --clausify_out                          false
% 3.03/1.01  --sig_cnt_out                           false
% 3.03/1.01  --trig_cnt_out                          false
% 3.03/1.01  --trig_cnt_out_tolerance                1.
% 3.03/1.01  --trig_cnt_out_sk_spl                   false
% 3.03/1.01  --abstr_cl_out                          false
% 3.03/1.01  
% 3.03/1.01  ------ Global Options
% 3.03/1.01  
% 3.03/1.01  --schedule                              default
% 3.03/1.01  --add_important_lit                     false
% 3.03/1.01  --prop_solver_per_cl                    1000
% 3.03/1.01  --min_unsat_core                        false
% 3.03/1.01  --soft_assumptions                      false
% 3.03/1.01  --soft_lemma_size                       3
% 3.03/1.01  --prop_impl_unit_size                   0
% 3.03/1.01  --prop_impl_unit                        []
% 3.03/1.01  --share_sel_clauses                     true
% 3.03/1.01  --reset_solvers                         false
% 3.03/1.01  --bc_imp_inh                            [conj_cone]
% 3.03/1.01  --conj_cone_tolerance                   3.
% 3.03/1.01  --extra_neg_conj                        none
% 3.03/1.01  --large_theory_mode                     true
% 3.03/1.01  --prolific_symb_bound                   200
% 3.03/1.01  --lt_threshold                          2000
% 3.03/1.01  --clause_weak_htbl                      true
% 3.03/1.01  --gc_record_bc_elim                     false
% 3.03/1.01  
% 3.03/1.01  ------ Preprocessing Options
% 3.03/1.01  
% 3.03/1.01  --preprocessing_flag                    true
% 3.03/1.01  --time_out_prep_mult                    0.1
% 3.03/1.01  --splitting_mode                        input
% 3.03/1.01  --splitting_grd                         true
% 3.03/1.01  --splitting_cvd                         false
% 3.03/1.01  --splitting_cvd_svl                     false
% 3.03/1.01  --splitting_nvd                         32
% 3.03/1.01  --sub_typing                            true
% 3.03/1.01  --prep_gs_sim                           true
% 3.03/1.01  --prep_unflatten                        true
% 3.03/1.01  --prep_res_sim                          true
% 3.03/1.01  --prep_upred                            true
% 3.03/1.01  --prep_sem_filter                       exhaustive
% 3.03/1.01  --prep_sem_filter_out                   false
% 3.03/1.01  --pred_elim                             true
% 3.03/1.01  --res_sim_input                         true
% 3.03/1.01  --eq_ax_congr_red                       true
% 3.03/1.01  --pure_diseq_elim                       true
% 3.03/1.01  --brand_transform                       false
% 3.03/1.01  --non_eq_to_eq                          false
% 3.03/1.01  --prep_def_merge                        true
% 3.03/1.01  --prep_def_merge_prop_impl              false
% 3.03/1.01  --prep_def_merge_mbd                    true
% 3.03/1.01  --prep_def_merge_tr_red                 false
% 3.03/1.01  --prep_def_merge_tr_cl                  false
% 3.03/1.01  --smt_preprocessing                     true
% 3.03/1.01  --smt_ac_axioms                         fast
% 3.03/1.01  --preprocessed_out                      false
% 3.03/1.01  --preprocessed_stats                    false
% 3.03/1.01  
% 3.03/1.01  ------ Abstraction refinement Options
% 3.03/1.01  
% 3.03/1.01  --abstr_ref                             []
% 3.03/1.01  --abstr_ref_prep                        false
% 3.03/1.01  --abstr_ref_until_sat                   false
% 3.03/1.01  --abstr_ref_sig_restrict                funpre
% 3.03/1.01  --abstr_ref_af_restrict_to_split_sk     false
% 3.03/1.01  --abstr_ref_under                       []
% 3.03/1.01  
% 3.03/1.01  ------ SAT Options
% 3.03/1.01  
% 3.03/1.01  --sat_mode                              false
% 3.03/1.01  --sat_fm_restart_options                ""
% 3.03/1.01  --sat_gr_def                            false
% 3.03/1.01  --sat_epr_types                         true
% 3.03/1.01  --sat_non_cyclic_types                  false
% 3.03/1.01  --sat_finite_models                     false
% 3.03/1.01  --sat_fm_lemmas                         false
% 3.03/1.01  --sat_fm_prep                           false
% 3.03/1.01  --sat_fm_uc_incr                        true
% 3.03/1.01  --sat_out_model                         small
% 3.03/1.01  --sat_out_clauses                       false
% 3.03/1.01  
% 3.03/1.01  ------ QBF Options
% 3.03/1.01  
% 3.03/1.01  --qbf_mode                              false
% 3.03/1.01  --qbf_elim_univ                         false
% 3.03/1.01  --qbf_dom_inst                          none
% 3.03/1.01  --qbf_dom_pre_inst                      false
% 3.03/1.01  --qbf_sk_in                             false
% 3.03/1.01  --qbf_pred_elim                         true
% 3.03/1.01  --qbf_split                             512
% 3.03/1.01  
% 3.03/1.01  ------ BMC1 Options
% 3.03/1.01  
% 3.03/1.01  --bmc1_incremental                      false
% 3.03/1.01  --bmc1_axioms                           reachable_all
% 3.03/1.01  --bmc1_min_bound                        0
% 3.03/1.01  --bmc1_max_bound                        -1
% 3.03/1.01  --bmc1_max_bound_default                -1
% 3.03/1.01  --bmc1_symbol_reachability              true
% 3.03/1.01  --bmc1_property_lemmas                  false
% 3.03/1.01  --bmc1_k_induction                      false
% 3.03/1.01  --bmc1_non_equiv_states                 false
% 3.03/1.01  --bmc1_deadlock                         false
% 3.03/1.01  --bmc1_ucm                              false
% 3.03/1.01  --bmc1_add_unsat_core                   none
% 3.03/1.01  --bmc1_unsat_core_children              false
% 3.03/1.01  --bmc1_unsat_core_extrapolate_axioms    false
% 3.03/1.01  --bmc1_out_stat                         full
% 3.03/1.01  --bmc1_ground_init                      false
% 3.03/1.01  --bmc1_pre_inst_next_state              false
% 3.03/1.01  --bmc1_pre_inst_state                   false
% 3.03/1.01  --bmc1_pre_inst_reach_state             false
% 3.03/1.01  --bmc1_out_unsat_core                   false
% 3.03/1.01  --bmc1_aig_witness_out                  false
% 3.03/1.01  --bmc1_verbose                          false
% 3.03/1.01  --bmc1_dump_clauses_tptp                false
% 3.03/1.01  --bmc1_dump_unsat_core_tptp             false
% 3.03/1.01  --bmc1_dump_file                        -
% 3.03/1.01  --bmc1_ucm_expand_uc_limit              128
% 3.03/1.01  --bmc1_ucm_n_expand_iterations          6
% 3.03/1.01  --bmc1_ucm_extend_mode                  1
% 3.03/1.01  --bmc1_ucm_init_mode                    2
% 3.03/1.01  --bmc1_ucm_cone_mode                    none
% 3.03/1.01  --bmc1_ucm_reduced_relation_type        0
% 3.03/1.01  --bmc1_ucm_relax_model                  4
% 3.03/1.01  --bmc1_ucm_full_tr_after_sat            true
% 3.03/1.01  --bmc1_ucm_expand_neg_assumptions       false
% 3.03/1.01  --bmc1_ucm_layered_model                none
% 3.03/1.01  --bmc1_ucm_max_lemma_size               10
% 3.03/1.01  
% 3.03/1.01  ------ AIG Options
% 3.03/1.01  
% 3.03/1.01  --aig_mode                              false
% 3.03/1.01  
% 3.03/1.01  ------ Instantiation Options
% 3.03/1.01  
% 3.03/1.01  --instantiation_flag                    true
% 3.03/1.01  --inst_sos_flag                         false
% 3.03/1.01  --inst_sos_phase                        true
% 3.03/1.01  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 3.03/1.01  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 3.03/1.01  --inst_lit_sel_side                     num_symb
% 3.03/1.01  --inst_solver_per_active                1400
% 3.03/1.01  --inst_solver_calls_frac                1.
% 3.03/1.01  --inst_passive_queue_type               priority_queues
% 3.03/1.01  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 3.03/1.01  --inst_passive_queues_freq              [25;2]
% 3.03/1.01  --inst_dismatching                      true
% 3.03/1.01  --inst_eager_unprocessed_to_passive     true
% 3.03/1.01  --inst_prop_sim_given                   true
% 3.03/1.01  --inst_prop_sim_new                     false
% 3.03/1.01  --inst_subs_new                         false
% 3.03/1.01  --inst_eq_res_simp                      false
% 3.03/1.01  --inst_subs_given                       false
% 3.03/1.01  --inst_orphan_elimination               true
% 3.03/1.01  --inst_learning_loop_flag               true
% 3.03/1.01  --inst_learning_start                   3000
% 3.03/1.01  --inst_learning_factor                  2
% 3.03/1.01  --inst_start_prop_sim_after_learn       3
% 3.03/1.01  --inst_sel_renew                        solver
% 3.03/1.01  --inst_lit_activity_flag                true
% 3.03/1.01  --inst_restr_to_given                   false
% 3.03/1.01  --inst_activity_threshold               500
% 3.03/1.01  --inst_out_proof                        true
% 3.03/1.01  
% 3.03/1.01  ------ Resolution Options
% 3.03/1.01  
% 3.03/1.01  --resolution_flag                       true
% 3.03/1.01  --res_lit_sel                           adaptive
% 3.03/1.01  --res_lit_sel_side                      none
% 3.03/1.01  --res_ordering                          kbo
% 3.03/1.01  --res_to_prop_solver                    active
% 3.03/1.01  --res_prop_simpl_new                    false
% 3.03/1.01  --res_prop_simpl_given                  true
% 3.03/1.01  --res_passive_queue_type                priority_queues
% 3.03/1.01  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 3.03/1.01  --res_passive_queues_freq               [15;5]
% 3.03/1.01  --res_forward_subs                      full
% 3.03/1.01  --res_backward_subs                     full
% 3.03/1.01  --res_forward_subs_resolution           true
% 3.03/1.01  --res_backward_subs_resolution          true
% 3.03/1.01  --res_orphan_elimination                true
% 3.03/1.01  --res_time_limit                        2.
% 3.03/1.01  --res_out_proof                         true
% 3.03/1.01  
% 3.03/1.01  ------ Superposition Options
% 3.03/1.01  
% 3.03/1.01  --superposition_flag                    true
% 3.03/1.01  --sup_passive_queue_type                priority_queues
% 3.03/1.01  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 3.03/1.01  --sup_passive_queues_freq               [8;1;4]
% 3.03/1.01  --demod_completeness_check              fast
% 3.03/1.01  --demod_use_ground                      true
% 3.03/1.01  --sup_to_prop_solver                    passive
% 3.03/1.01  --sup_prop_simpl_new                    true
% 3.03/1.01  --sup_prop_simpl_given                  true
% 3.03/1.01  --sup_fun_splitting                     false
% 3.03/1.01  --sup_smt_interval                      50000
% 3.03/1.01  
% 3.03/1.01  ------ Superposition Simplification Setup
% 3.03/1.01  
% 3.03/1.01  --sup_indices_passive                   []
% 3.03/1.01  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.03/1.01  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.03/1.01  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.03/1.01  --sup_full_triv                         [TrivRules;PropSubs]
% 3.03/1.01  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.03/1.01  --sup_full_bw                           [BwDemod]
% 3.03/1.01  --sup_immed_triv                        [TrivRules]
% 3.03/1.01  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 3.03/1.01  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.03/1.01  --sup_immed_bw_main                     []
% 3.03/1.01  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 3.03/1.01  --sup_input_triv                        [Unflattening;TrivRules]
% 3.03/1.01  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.03/1.01  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 3.03/1.01  
% 3.03/1.01  ------ Combination Options
% 3.03/1.01  
% 3.03/1.01  --comb_res_mult                         3
% 3.03/1.01  --comb_sup_mult                         2
% 3.03/1.01  --comb_inst_mult                        10
% 3.03/1.01  
% 3.03/1.01  ------ Debug Options
% 3.03/1.01  
% 3.03/1.01  --dbg_backtrace                         false
% 3.03/1.01  --dbg_dump_prop_clauses                 false
% 3.03/1.01  --dbg_dump_prop_clauses_file            -
% 3.03/1.01  --dbg_out_stat                          false
% 3.03/1.01  ------ Parsing...
% 3.03/1.01  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 3.03/1.01  
% 3.03/1.01  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe:1:0s pe:2:0s pe_e  sf_s  rm: 3 0s  sf_e  pe_s  pe_e 
% 3.03/1.01  
% 3.03/1.01  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 3.03/1.01  
% 3.03/1.01  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 3.03/1.01  ------ Proving...
% 3.03/1.01  ------ Problem Properties 
% 3.03/1.01  
% 3.03/1.01  
% 3.03/1.01  clauses                                 21
% 3.03/1.01  conjectures                             5
% 3.03/1.01  EPR                                     3
% 3.03/1.01  Horn                                    21
% 3.03/1.01  unary                                   6
% 3.03/1.01  binary                                  1
% 3.03/1.01  lits                                    69
% 3.03/1.01  lits eq                                 7
% 3.03/1.01  fd_pure                                 0
% 3.03/1.01  fd_pseudo                               0
% 3.03/1.01  fd_cond                                 0
% 3.03/1.01  fd_pseudo_cond                          1
% 3.03/1.01  AC symbols                              0
% 3.03/1.01  
% 3.03/1.01  ------ Schedule dynamic 5 is on 
% 3.03/1.01  
% 3.03/1.01  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" Time Limit: 10.
% 3.03/1.01  
% 3.03/1.01  
% 3.03/1.01  ------ 
% 3.03/1.01  Current options:
% 3.03/1.01  ------ 
% 3.03/1.01  
% 3.03/1.01  ------ Input Options
% 3.03/1.01  
% 3.03/1.01  --out_options                           all
% 3.03/1.01  --tptp_safe_out                         true
% 3.03/1.01  --problem_path                          ""
% 3.03/1.01  --include_path                          ""
% 3.03/1.01  --clausifier                            res/vclausify_rel
% 3.03/1.01  --clausifier_options                    --mode clausify
% 3.03/1.01  --stdin                                 false
% 3.03/1.01  --stats_out                             all
% 3.03/1.01  
% 3.03/1.01  ------ General Options
% 3.03/1.01  
% 3.03/1.01  --fof                                   false
% 3.03/1.01  --time_out_real                         305.
% 3.03/1.01  --time_out_virtual                      -1.
% 3.03/1.01  --symbol_type_check                     false
% 3.03/1.01  --clausify_out                          false
% 3.03/1.01  --sig_cnt_out                           false
% 3.03/1.01  --trig_cnt_out                          false
% 3.03/1.01  --trig_cnt_out_tolerance                1.
% 3.03/1.01  --trig_cnt_out_sk_spl                   false
% 3.03/1.01  --abstr_cl_out                          false
% 3.03/1.01  
% 3.03/1.01  ------ Global Options
% 3.03/1.01  
% 3.03/1.01  --schedule                              default
% 3.03/1.01  --add_important_lit                     false
% 3.03/1.01  --prop_solver_per_cl                    1000
% 3.03/1.01  --min_unsat_core                        false
% 3.03/1.01  --soft_assumptions                      false
% 3.03/1.01  --soft_lemma_size                       3
% 3.03/1.01  --prop_impl_unit_size                   0
% 3.03/1.01  --prop_impl_unit                        []
% 3.03/1.01  --share_sel_clauses                     true
% 3.03/1.01  --reset_solvers                         false
% 3.03/1.01  --bc_imp_inh                            [conj_cone]
% 3.03/1.01  --conj_cone_tolerance                   3.
% 3.03/1.01  --extra_neg_conj                        none
% 3.03/1.01  --large_theory_mode                     true
% 3.03/1.01  --prolific_symb_bound                   200
% 3.03/1.01  --lt_threshold                          2000
% 3.03/1.01  --clause_weak_htbl                      true
% 3.03/1.01  --gc_record_bc_elim                     false
% 3.03/1.01  
% 3.03/1.01  ------ Preprocessing Options
% 3.03/1.01  
% 3.03/1.01  --preprocessing_flag                    true
% 3.03/1.01  --time_out_prep_mult                    0.1
% 3.03/1.01  --splitting_mode                        input
% 3.03/1.01  --splitting_grd                         true
% 3.03/1.01  --splitting_cvd                         false
% 3.03/1.01  --splitting_cvd_svl                     false
% 3.03/1.01  --splitting_nvd                         32
% 3.03/1.01  --sub_typing                            true
% 3.03/1.01  --prep_gs_sim                           true
% 3.03/1.01  --prep_unflatten                        true
% 3.03/1.01  --prep_res_sim                          true
% 3.03/1.01  --prep_upred                            true
% 3.03/1.01  --prep_sem_filter                       exhaustive
% 3.03/1.01  --prep_sem_filter_out                   false
% 3.03/1.01  --pred_elim                             true
% 3.03/1.01  --res_sim_input                         true
% 3.03/1.01  --eq_ax_congr_red                       true
% 3.03/1.01  --pure_diseq_elim                       true
% 3.03/1.01  --brand_transform                       false
% 3.03/1.01  --non_eq_to_eq                          false
% 3.03/1.01  --prep_def_merge                        true
% 3.03/1.01  --prep_def_merge_prop_impl              false
% 3.03/1.01  --prep_def_merge_mbd                    true
% 3.03/1.01  --prep_def_merge_tr_red                 false
% 3.03/1.01  --prep_def_merge_tr_cl                  false
% 3.03/1.01  --smt_preprocessing                     true
% 3.03/1.01  --smt_ac_axioms                         fast
% 3.03/1.01  --preprocessed_out                      false
% 3.03/1.01  --preprocessed_stats                    false
% 3.03/1.01  
% 3.03/1.01  ------ Abstraction refinement Options
% 3.03/1.01  
% 3.03/1.01  --abstr_ref                             []
% 3.03/1.01  --abstr_ref_prep                        false
% 3.03/1.01  --abstr_ref_until_sat                   false
% 3.03/1.01  --abstr_ref_sig_restrict                funpre
% 3.03/1.01  --abstr_ref_af_restrict_to_split_sk     false
% 3.03/1.01  --abstr_ref_under                       []
% 3.03/1.01  
% 3.03/1.01  ------ SAT Options
% 3.03/1.01  
% 3.03/1.01  --sat_mode                              false
% 3.03/1.01  --sat_fm_restart_options                ""
% 3.03/1.01  --sat_gr_def                            false
% 3.03/1.01  --sat_epr_types                         true
% 3.03/1.01  --sat_non_cyclic_types                  false
% 3.03/1.01  --sat_finite_models                     false
% 3.03/1.01  --sat_fm_lemmas                         false
% 3.03/1.01  --sat_fm_prep                           false
% 3.03/1.01  --sat_fm_uc_incr                        true
% 3.03/1.01  --sat_out_model                         small
% 3.03/1.01  --sat_out_clauses                       false
% 3.03/1.01  
% 3.03/1.01  ------ QBF Options
% 3.03/1.01  
% 3.03/1.01  --qbf_mode                              false
% 3.03/1.01  --qbf_elim_univ                         false
% 3.03/1.01  --qbf_dom_inst                          none
% 3.03/1.01  --qbf_dom_pre_inst                      false
% 3.03/1.01  --qbf_sk_in                             false
% 3.03/1.01  --qbf_pred_elim                         true
% 3.03/1.01  --qbf_split                             512
% 3.03/1.01  
% 3.03/1.01  ------ BMC1 Options
% 3.03/1.01  
% 3.03/1.01  --bmc1_incremental                      false
% 3.03/1.01  --bmc1_axioms                           reachable_all
% 3.03/1.01  --bmc1_min_bound                        0
% 3.03/1.01  --bmc1_max_bound                        -1
% 3.03/1.01  --bmc1_max_bound_default                -1
% 3.03/1.01  --bmc1_symbol_reachability              true
% 3.03/1.01  --bmc1_property_lemmas                  false
% 3.03/1.01  --bmc1_k_induction                      false
% 3.03/1.01  --bmc1_non_equiv_states                 false
% 3.03/1.01  --bmc1_deadlock                         false
% 3.03/1.01  --bmc1_ucm                              false
% 3.03/1.01  --bmc1_add_unsat_core                   none
% 3.03/1.01  --bmc1_unsat_core_children              false
% 3.03/1.01  --bmc1_unsat_core_extrapolate_axioms    false
% 3.03/1.01  --bmc1_out_stat                         full
% 3.03/1.01  --bmc1_ground_init                      false
% 3.03/1.01  --bmc1_pre_inst_next_state              false
% 3.03/1.01  --bmc1_pre_inst_state                   false
% 3.03/1.01  --bmc1_pre_inst_reach_state             false
% 3.03/1.01  --bmc1_out_unsat_core                   false
% 3.03/1.01  --bmc1_aig_witness_out                  false
% 3.03/1.01  --bmc1_verbose                          false
% 3.03/1.01  --bmc1_dump_clauses_tptp                false
% 3.03/1.01  --bmc1_dump_unsat_core_tptp             false
% 3.03/1.01  --bmc1_dump_file                        -
% 3.03/1.01  --bmc1_ucm_expand_uc_limit              128
% 3.03/1.01  --bmc1_ucm_n_expand_iterations          6
% 3.03/1.01  --bmc1_ucm_extend_mode                  1
% 3.03/1.01  --bmc1_ucm_init_mode                    2
% 3.03/1.01  --bmc1_ucm_cone_mode                    none
% 3.03/1.01  --bmc1_ucm_reduced_relation_type        0
% 3.03/1.01  --bmc1_ucm_relax_model                  4
% 3.03/1.01  --bmc1_ucm_full_tr_after_sat            true
% 3.03/1.01  --bmc1_ucm_expand_neg_assumptions       false
% 3.03/1.01  --bmc1_ucm_layered_model                none
% 3.03/1.01  --bmc1_ucm_max_lemma_size               10
% 3.03/1.01  
% 3.03/1.01  ------ AIG Options
% 3.03/1.01  
% 3.03/1.01  --aig_mode                              false
% 3.03/1.01  
% 3.03/1.01  ------ Instantiation Options
% 3.03/1.01  
% 3.03/1.01  --instantiation_flag                    true
% 3.03/1.01  --inst_sos_flag                         false
% 3.03/1.01  --inst_sos_phase                        true
% 3.03/1.01  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 3.03/1.01  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 3.03/1.01  --inst_lit_sel_side                     none
% 3.03/1.01  --inst_solver_per_active                1400
% 3.03/1.01  --inst_solver_calls_frac                1.
% 3.03/1.01  --inst_passive_queue_type               priority_queues
% 3.03/1.01  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 3.03/1.01  --inst_passive_queues_freq              [25;2]
% 3.03/1.01  --inst_dismatching                      true
% 3.03/1.01  --inst_eager_unprocessed_to_passive     true
% 3.03/1.01  --inst_prop_sim_given                   true
% 3.03/1.01  --inst_prop_sim_new                     false
% 3.03/1.01  --inst_subs_new                         false
% 3.03/1.01  --inst_eq_res_simp                      false
% 3.03/1.01  --inst_subs_given                       false
% 3.03/1.01  --inst_orphan_elimination               true
% 3.03/1.01  --inst_learning_loop_flag               true
% 3.03/1.01  --inst_learning_start                   3000
% 3.03/1.01  --inst_learning_factor                  2
% 3.03/1.01  --inst_start_prop_sim_after_learn       3
% 3.03/1.01  --inst_sel_renew                        solver
% 3.03/1.01  --inst_lit_activity_flag                true
% 3.03/1.01  --inst_restr_to_given                   false
% 3.03/1.01  --inst_activity_threshold               500
% 3.03/1.01  --inst_out_proof                        true
% 3.03/1.01  
% 3.03/1.01  ------ Resolution Options
% 3.03/1.01  
% 3.03/1.01  --resolution_flag                       false
% 3.03/1.01  --res_lit_sel                           adaptive
% 3.03/1.01  --res_lit_sel_side                      none
% 3.03/1.01  --res_ordering                          kbo
% 3.03/1.01  --res_to_prop_solver                    active
% 3.03/1.01  --res_prop_simpl_new                    false
% 3.03/1.01  --res_prop_simpl_given                  true
% 3.03/1.01  --res_passive_queue_type                priority_queues
% 3.03/1.01  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 3.03/1.01  --res_passive_queues_freq               [15;5]
% 3.03/1.01  --res_forward_subs                      full
% 3.03/1.01  --res_backward_subs                     full
% 3.03/1.01  --res_forward_subs_resolution           true
% 3.03/1.01  --res_backward_subs_resolution          true
% 3.03/1.01  --res_orphan_elimination                true
% 3.03/1.01  --res_time_limit                        2.
% 3.03/1.01  --res_out_proof                         true
% 3.03/1.01  
% 3.03/1.01  ------ Superposition Options
% 3.03/1.01  
% 3.03/1.01  --superposition_flag                    true
% 3.03/1.01  --sup_passive_queue_type                priority_queues
% 3.03/1.01  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 3.03/1.01  --sup_passive_queues_freq               [8;1;4]
% 3.03/1.01  --demod_completeness_check              fast
% 3.03/1.01  --demod_use_ground                      true
% 3.03/1.01  --sup_to_prop_solver                    passive
% 3.03/1.01  --sup_prop_simpl_new                    true
% 3.03/1.01  --sup_prop_simpl_given                  true
% 3.03/1.01  --sup_fun_splitting                     false
% 3.03/1.01  --sup_smt_interval                      50000
% 3.03/1.01  
% 3.03/1.01  ------ Superposition Simplification Setup
% 3.03/1.01  
% 3.03/1.01  --sup_indices_passive                   []
% 3.03/1.01  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.03/1.01  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.03/1.01  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.03/1.01  --sup_full_triv                         [TrivRules;PropSubs]
% 3.03/1.01  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.03/1.01  --sup_full_bw                           [BwDemod]
% 3.03/1.01  --sup_immed_triv                        [TrivRules]
% 3.03/1.01  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 3.03/1.01  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.03/1.01  --sup_immed_bw_main                     []
% 3.03/1.01  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 3.03/1.01  --sup_input_triv                        [Unflattening;TrivRules]
% 3.03/1.01  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.03/1.01  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 3.03/1.01  
% 3.03/1.01  ------ Combination Options
% 3.03/1.01  
% 3.03/1.01  --comb_res_mult                         3
% 3.03/1.01  --comb_sup_mult                         2
% 3.03/1.01  --comb_inst_mult                        10
% 3.03/1.01  
% 3.03/1.01  ------ Debug Options
% 3.03/1.01  
% 3.03/1.01  --dbg_backtrace                         false
% 3.03/1.01  --dbg_dump_prop_clauses                 false
% 3.03/1.01  --dbg_dump_prop_clauses_file            -
% 3.03/1.01  --dbg_out_stat                          false
% 3.03/1.01  
% 3.03/1.01  
% 3.03/1.01  
% 3.03/1.01  
% 3.03/1.01  ------ Proving...
% 3.03/1.01  
% 3.03/1.01  
% 3.03/1.01  % SZS status Theorem for theBenchmark.p
% 3.03/1.01  
% 3.03/1.01   Resolution empty clause
% 3.03/1.01  
% 3.03/1.01  % SZS output start CNFRefutation for theBenchmark.p
% 3.03/1.01  
% 3.03/1.01  fof(f14,conjecture,(
% 3.03/1.01    ! [X0,X1] : ((m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v3_funct_2(X1,X0,X0) & v1_funct_2(X1,X0,X0) & v1_funct_1(X1)) => (r2_relset_1(X0,X0,k1_partfun1(X0,X0,X0,X0,k2_funct_2(X0,X1),X1),k6_partfun1(X0)) & r2_relset_1(X0,X0,k1_partfun1(X0,X0,X0,X0,X1,k2_funct_2(X0,X1)),k6_partfun1(X0))))),
% 3.03/1.01    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.03/1.01  
% 3.03/1.01  fof(f15,negated_conjecture,(
% 3.03/1.01    ~! [X0,X1] : ((m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v3_funct_2(X1,X0,X0) & v1_funct_2(X1,X0,X0) & v1_funct_1(X1)) => (r2_relset_1(X0,X0,k1_partfun1(X0,X0,X0,X0,k2_funct_2(X0,X1),X1),k6_partfun1(X0)) & r2_relset_1(X0,X0,k1_partfun1(X0,X0,X0,X0,X1,k2_funct_2(X0,X1)),k6_partfun1(X0))))),
% 3.03/1.01    inference(negated_conjecture,[],[f14])).
% 3.03/1.01  
% 3.03/1.01  fof(f36,plain,(
% 3.03/1.01    ? [X0,X1] : ((~r2_relset_1(X0,X0,k1_partfun1(X0,X0,X0,X0,k2_funct_2(X0,X1),X1),k6_partfun1(X0)) | ~r2_relset_1(X0,X0,k1_partfun1(X0,X0,X0,X0,X1,k2_funct_2(X0,X1)),k6_partfun1(X0))) & (m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v3_funct_2(X1,X0,X0) & v1_funct_2(X1,X0,X0) & v1_funct_1(X1)))),
% 3.03/1.01    inference(ennf_transformation,[],[f15])).
% 3.03/1.01  
% 3.03/1.01  fof(f37,plain,(
% 3.03/1.01    ? [X0,X1] : ((~r2_relset_1(X0,X0,k1_partfun1(X0,X0,X0,X0,k2_funct_2(X0,X1),X1),k6_partfun1(X0)) | ~r2_relset_1(X0,X0,k1_partfun1(X0,X0,X0,X0,X1,k2_funct_2(X0,X1)),k6_partfun1(X0))) & m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v3_funct_2(X1,X0,X0) & v1_funct_2(X1,X0,X0) & v1_funct_1(X1))),
% 3.03/1.01    inference(flattening,[],[f36])).
% 3.03/1.01  
% 3.03/1.01  fof(f39,plain,(
% 3.03/1.01    ? [X0,X1] : ((~r2_relset_1(X0,X0,k1_partfun1(X0,X0,X0,X0,k2_funct_2(X0,X1),X1),k6_partfun1(X0)) | ~r2_relset_1(X0,X0,k1_partfun1(X0,X0,X0,X0,X1,k2_funct_2(X0,X1)),k6_partfun1(X0))) & m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v3_funct_2(X1,X0,X0) & v1_funct_2(X1,X0,X0) & v1_funct_1(X1)) => ((~r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK0,sK0,sK0,k2_funct_2(sK0,sK1),sK1),k6_partfun1(sK0)) | ~r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK0,sK0,sK0,sK1,k2_funct_2(sK0,sK1)),k6_partfun1(sK0))) & m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) & v3_funct_2(sK1,sK0,sK0) & v1_funct_2(sK1,sK0,sK0) & v1_funct_1(sK1))),
% 3.03/1.01    introduced(choice_axiom,[])).
% 3.03/1.01  
% 3.03/1.01  fof(f40,plain,(
% 3.03/1.01    (~r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK0,sK0,sK0,k2_funct_2(sK0,sK1),sK1),k6_partfun1(sK0)) | ~r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK0,sK0,sK0,sK1,k2_funct_2(sK0,sK1)),k6_partfun1(sK0))) & m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) & v3_funct_2(sK1,sK0,sK0) & v1_funct_2(sK1,sK0,sK0) & v1_funct_1(sK1)),
% 3.03/1.01    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f37,f39])).
% 3.03/1.01  
% 3.03/1.01  fof(f65,plain,(
% 3.03/1.01    m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))),
% 3.03/1.01    inference(cnf_transformation,[],[f40])).
% 3.03/1.01  
% 3.03/1.01  fof(f12,axiom,(
% 3.03/1.01    ! [X0,X1] : ((m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v3_funct_2(X1,X0,X0) & v1_funct_2(X1,X0,X0) & v1_funct_1(X1)) => k2_funct_1(X1) = k2_funct_2(X0,X1))),
% 3.03/1.01    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.03/1.01  
% 3.03/1.01  fof(f34,plain,(
% 3.03/1.01    ! [X0,X1] : (k2_funct_1(X1) = k2_funct_2(X0,X1) | (~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) | ~v3_funct_2(X1,X0,X0) | ~v1_funct_2(X1,X0,X0) | ~v1_funct_1(X1)))),
% 3.03/1.01    inference(ennf_transformation,[],[f12])).
% 3.03/1.01  
% 3.03/1.01  fof(f35,plain,(
% 3.03/1.01    ! [X0,X1] : (k2_funct_1(X1) = k2_funct_2(X0,X1) | ~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) | ~v3_funct_2(X1,X0,X0) | ~v1_funct_2(X1,X0,X0) | ~v1_funct_1(X1))),
% 3.03/1.01    inference(flattening,[],[f34])).
% 3.03/1.01  
% 3.03/1.01  fof(f60,plain,(
% 3.03/1.01    ( ! [X0,X1] : (k2_funct_1(X1) = k2_funct_2(X0,X1) | ~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) | ~v3_funct_2(X1,X0,X0) | ~v1_funct_2(X1,X0,X0) | ~v1_funct_1(X1)) )),
% 3.03/1.01    inference(cnf_transformation,[],[f35])).
% 3.03/1.01  
% 3.03/1.01  fof(f62,plain,(
% 3.03/1.01    v1_funct_1(sK1)),
% 3.03/1.01    inference(cnf_transformation,[],[f40])).
% 3.03/1.01  
% 3.03/1.01  fof(f63,plain,(
% 3.03/1.01    v1_funct_2(sK1,sK0,sK0)),
% 3.03/1.01    inference(cnf_transformation,[],[f40])).
% 3.03/1.01  
% 3.03/1.01  fof(f64,plain,(
% 3.03/1.01    v3_funct_2(sK1,sK0,sK0)),
% 3.03/1.01    inference(cnf_transformation,[],[f40])).
% 3.03/1.01  
% 3.03/1.01  fof(f9,axiom,(
% 3.03/1.01    ! [X0,X1] : ((m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v3_funct_2(X1,X0,X0) & v1_funct_2(X1,X0,X0) & v1_funct_1(X1)) => (m1_subset_1(k2_funct_2(X0,X1),k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v3_funct_2(k2_funct_2(X0,X1),X0,X0) & v1_funct_2(k2_funct_2(X0,X1),X0,X0) & v1_funct_1(k2_funct_2(X0,X1))))),
% 3.03/1.01    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.03/1.01  
% 3.03/1.01  fof(f30,plain,(
% 3.03/1.01    ! [X0,X1] : ((m1_subset_1(k2_funct_2(X0,X1),k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v3_funct_2(k2_funct_2(X0,X1),X0,X0) & v1_funct_2(k2_funct_2(X0,X1),X0,X0) & v1_funct_1(k2_funct_2(X0,X1))) | (~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) | ~v3_funct_2(X1,X0,X0) | ~v1_funct_2(X1,X0,X0) | ~v1_funct_1(X1)))),
% 3.03/1.01    inference(ennf_transformation,[],[f9])).
% 3.03/1.01  
% 3.03/1.01  fof(f31,plain,(
% 3.03/1.01    ! [X0,X1] : ((m1_subset_1(k2_funct_2(X0,X1),k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v3_funct_2(k2_funct_2(X0,X1),X0,X0) & v1_funct_2(k2_funct_2(X0,X1),X0,X0) & v1_funct_1(k2_funct_2(X0,X1))) | ~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) | ~v3_funct_2(X1,X0,X0) | ~v1_funct_2(X1,X0,X0) | ~v1_funct_1(X1))),
% 3.03/1.01    inference(flattening,[],[f30])).
% 3.03/1.01  
% 3.03/1.01  fof(f57,plain,(
% 3.03/1.01    ( ! [X0,X1] : (m1_subset_1(k2_funct_2(X0,X1),k1_zfmisc_1(k2_zfmisc_1(X0,X0))) | ~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) | ~v3_funct_2(X1,X0,X0) | ~v1_funct_2(X1,X0,X0) | ~v1_funct_1(X1)) )),
% 3.03/1.01    inference(cnf_transformation,[],[f31])).
% 3.03/1.01  
% 3.03/1.01  fof(f11,axiom,(
% 3.03/1.01    ! [X0,X1,X2,X3,X4,X5] : ((m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) & v1_funct_1(X5) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_1(X4)) => k5_relat_1(X4,X5) = k1_partfun1(X0,X1,X2,X3,X4,X5))),
% 3.03/1.01    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.03/1.01  
% 3.03/1.01  fof(f32,plain,(
% 3.03/1.01    ! [X0,X1,X2,X3,X4,X5] : (k5_relat_1(X4,X5) = k1_partfun1(X0,X1,X2,X3,X4,X5) | (~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X4)))),
% 3.03/1.01    inference(ennf_transformation,[],[f11])).
% 3.03/1.01  
% 3.03/1.01  fof(f33,plain,(
% 3.03/1.01    ! [X0,X1,X2,X3,X4,X5] : (k5_relat_1(X4,X5) = k1_partfun1(X0,X1,X2,X3,X4,X5) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X4))),
% 3.03/1.01    inference(flattening,[],[f32])).
% 3.03/1.01  
% 3.03/1.01  fof(f59,plain,(
% 3.03/1.01    ( ! [X4,X2,X0,X5,X3,X1] : (k5_relat_1(X4,X5) = k1_partfun1(X0,X1,X2,X3,X4,X5) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X4)) )),
% 3.03/1.01    inference(cnf_transformation,[],[f33])).
% 3.03/1.01  
% 3.03/1.01  fof(f4,axiom,(
% 3.03/1.01    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => (v2_funct_1(X0) => (k5_relat_1(k2_funct_1(X0),X0) = k6_relat_1(k2_relat_1(X0)) & k5_relat_1(X0,k2_funct_1(X0)) = k6_relat_1(k1_relat_1(X0)))))),
% 3.03/1.01    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.03/1.01  
% 3.03/1.01  fof(f21,plain,(
% 3.03/1.01    ! [X0] : (((k5_relat_1(k2_funct_1(X0),X0) = k6_relat_1(k2_relat_1(X0)) & k5_relat_1(X0,k2_funct_1(X0)) = k6_relat_1(k1_relat_1(X0))) | ~v2_funct_1(X0)) | (~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 3.03/1.01    inference(ennf_transformation,[],[f4])).
% 3.03/1.01  
% 3.03/1.01  fof(f22,plain,(
% 3.03/1.01    ! [X0] : ((k5_relat_1(k2_funct_1(X0),X0) = k6_relat_1(k2_relat_1(X0)) & k5_relat_1(X0,k2_funct_1(X0)) = k6_relat_1(k1_relat_1(X0))) | ~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 3.03/1.01    inference(flattening,[],[f21])).
% 3.03/1.01  
% 3.03/1.01  fof(f45,plain,(
% 3.03/1.01    ( ! [X0] : (k5_relat_1(X0,k2_funct_1(X0)) = k6_relat_1(k1_relat_1(X0)) | ~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 3.03/1.01    inference(cnf_transformation,[],[f22])).
% 3.03/1.01  
% 3.03/1.01  fof(f13,axiom,(
% 3.03/1.01    ! [X0] : k6_relat_1(X0) = k6_partfun1(X0)),
% 3.03/1.01    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.03/1.01  
% 3.03/1.01  fof(f61,plain,(
% 3.03/1.01    ( ! [X0] : (k6_relat_1(X0) = k6_partfun1(X0)) )),
% 3.03/1.01    inference(cnf_transformation,[],[f13])).
% 3.03/1.01  
% 3.03/1.01  fof(f68,plain,(
% 3.03/1.01    ( ! [X0] : (k5_relat_1(X0,k2_funct_1(X0)) = k6_partfun1(k1_relat_1(X0)) | ~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 3.03/1.01    inference(definition_unfolding,[],[f45,f61])).
% 3.03/1.01  
% 3.03/1.01  fof(f2,axiom,(
% 3.03/1.01    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1))),
% 3.03/1.01    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.03/1.01  
% 3.03/1.01  fof(f42,plain,(
% 3.03/1.01    ( ! [X0,X1] : (v1_relat_1(k2_zfmisc_1(X0,X1))) )),
% 3.03/1.01    inference(cnf_transformation,[],[f2])).
% 3.03/1.01  
% 3.03/1.01  fof(f7,axiom,(
% 3.03/1.01    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => ((v3_funct_2(X2,X0,X1) & v1_funct_1(X2)) => (v2_funct_2(X2,X1) & v2_funct_1(X2) & v1_funct_1(X2))))),
% 3.03/1.01    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.03/1.01  
% 3.03/1.01  fof(f26,plain,(
% 3.03/1.01    ! [X0,X1,X2] : (((v2_funct_2(X2,X1) & v2_funct_1(X2) & v1_funct_1(X2)) | (~v3_funct_2(X2,X0,X1) | ~v1_funct_1(X2))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 3.03/1.01    inference(ennf_transformation,[],[f7])).
% 3.03/1.01  
% 3.03/1.01  fof(f27,plain,(
% 3.03/1.01    ! [X0,X1,X2] : ((v2_funct_2(X2,X1) & v2_funct_1(X2) & v1_funct_1(X2)) | ~v3_funct_2(X2,X0,X1) | ~v1_funct_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 3.03/1.01    inference(flattening,[],[f26])).
% 3.03/1.01  
% 3.03/1.01  fof(f50,plain,(
% 3.03/1.01    ( ! [X2,X0,X1] : (v2_funct_1(X2) | ~v3_funct_2(X2,X0,X1) | ~v1_funct_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 3.03/1.01    inference(cnf_transformation,[],[f27])).
% 3.03/1.01  
% 3.03/1.01  fof(f1,axiom,(
% 3.03/1.01    ! [X0] : (v1_relat_1(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => v1_relat_1(X1)))),
% 3.03/1.01    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.03/1.01  
% 3.03/1.01  fof(f18,plain,(
% 3.03/1.01    ! [X0] : (! [X1] : (v1_relat_1(X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) | ~v1_relat_1(X0))),
% 3.03/1.01    inference(ennf_transformation,[],[f1])).
% 3.03/1.01  
% 3.03/1.01  fof(f41,plain,(
% 3.03/1.01    ( ! [X0,X1] : (v1_relat_1(X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0)) | ~v1_relat_1(X0)) )),
% 3.03/1.01    inference(cnf_transformation,[],[f18])).
% 3.03/1.01  
% 3.03/1.01  fof(f54,plain,(
% 3.03/1.01    ( ! [X0,X1] : (v1_funct_1(k2_funct_2(X0,X1)) | ~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) | ~v3_funct_2(X1,X0,X0) | ~v1_funct_2(X1,X0,X0) | ~v1_funct_1(X1)) )),
% 3.03/1.01    inference(cnf_transformation,[],[f31])).
% 3.03/1.01  
% 3.03/1.01  fof(f66,plain,(
% 3.03/1.01    ~r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK0,sK0,sK0,k2_funct_2(sK0,sK1),sK1),k6_partfun1(sK0)) | ~r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK0,sK0,sK0,sK1,k2_funct_2(sK0,sK1)),k6_partfun1(sK0))),
% 3.03/1.01    inference(cnf_transformation,[],[f40])).
% 3.03/1.01  
% 3.03/1.01  fof(f46,plain,(
% 3.03/1.01    ( ! [X0] : (k5_relat_1(k2_funct_1(X0),X0) = k6_relat_1(k2_relat_1(X0)) | ~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 3.03/1.01    inference(cnf_transformation,[],[f22])).
% 3.03/1.01  
% 3.03/1.01  fof(f67,plain,(
% 3.03/1.01    ( ! [X0] : (k5_relat_1(k2_funct_1(X0),X0) = k6_partfun1(k2_relat_1(X0)) | ~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 3.03/1.01    inference(definition_unfolding,[],[f46,f61])).
% 3.03/1.01  
% 3.03/1.01  fof(f51,plain,(
% 3.03/1.01    ( ! [X2,X0,X1] : (v2_funct_2(X2,X1) | ~v3_funct_2(X2,X0,X1) | ~v1_funct_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 3.03/1.01    inference(cnf_transformation,[],[f27])).
% 3.03/1.01  
% 3.03/1.01  fof(f8,axiom,(
% 3.03/1.01    ! [X0,X1] : ((v5_relat_1(X1,X0) & v1_relat_1(X1)) => (v2_funct_2(X1,X0) <=> k2_relat_1(X1) = X0))),
% 3.03/1.01    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.03/1.01  
% 3.03/1.01  fof(f28,plain,(
% 3.03/1.01    ! [X0,X1] : ((v2_funct_2(X1,X0) <=> k2_relat_1(X1) = X0) | (~v5_relat_1(X1,X0) | ~v1_relat_1(X1)))),
% 3.03/1.01    inference(ennf_transformation,[],[f8])).
% 3.03/1.01  
% 3.03/1.01  fof(f29,plain,(
% 3.03/1.01    ! [X0,X1] : ((v2_funct_2(X1,X0) <=> k2_relat_1(X1) = X0) | ~v5_relat_1(X1,X0) | ~v1_relat_1(X1))),
% 3.03/1.01    inference(flattening,[],[f28])).
% 3.03/1.01  
% 3.03/1.01  fof(f38,plain,(
% 3.03/1.01    ! [X0,X1] : (((v2_funct_2(X1,X0) | k2_relat_1(X1) != X0) & (k2_relat_1(X1) = X0 | ~v2_funct_2(X1,X0))) | ~v5_relat_1(X1,X0) | ~v1_relat_1(X1))),
% 3.03/1.01    inference(nnf_transformation,[],[f29])).
% 3.03/1.01  
% 3.03/1.01  fof(f52,plain,(
% 3.03/1.01    ( ! [X0,X1] : (k2_relat_1(X1) = X0 | ~v2_funct_2(X1,X0) | ~v5_relat_1(X1,X0) | ~v1_relat_1(X1)) )),
% 3.03/1.02    inference(cnf_transformation,[],[f38])).
% 3.03/1.02  
% 3.03/1.02  fof(f5,axiom,(
% 3.03/1.02    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => (v5_relat_1(X2,X1) & v4_relat_1(X2,X0)))),
% 3.03/1.02    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.03/1.02  
% 3.03/1.02  fof(f17,plain,(
% 3.03/1.02    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => v5_relat_1(X2,X1))),
% 3.03/1.02    inference(pure_predicate_removal,[],[f5])).
% 3.03/1.02  
% 3.03/1.02  fof(f23,plain,(
% 3.03/1.02    ! [X0,X1,X2] : (v5_relat_1(X2,X1) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 3.03/1.02    inference(ennf_transformation,[],[f17])).
% 3.03/1.02  
% 3.03/1.02  fof(f47,plain,(
% 3.03/1.02    ( ! [X2,X0,X1] : (v5_relat_1(X2,X1) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 3.03/1.02    inference(cnf_transformation,[],[f23])).
% 3.03/1.02  
% 3.03/1.02  fof(f10,axiom,(
% 3.03/1.02    ! [X0] : (m1_subset_1(k6_partfun1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v1_partfun1(k6_partfun1(X0),X0))),
% 3.03/1.02    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.03/1.02  
% 3.03/1.02  fof(f16,plain,(
% 3.03/1.02    ! [X0] : m1_subset_1(k6_partfun1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0)))),
% 3.03/1.02    inference(pure_predicate_removal,[],[f10])).
% 3.03/1.02  
% 3.03/1.02  fof(f58,plain,(
% 3.03/1.02    ( ! [X0] : (m1_subset_1(k6_partfun1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0)))) )),
% 3.03/1.02    inference(cnf_transformation,[],[f16])).
% 3.03/1.02  
% 3.03/1.02  fof(f6,axiom,(
% 3.03/1.02    ! [X0,X1,X2,X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) => r2_relset_1(X0,X1,X2,X2))),
% 3.03/1.02    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.03/1.02  
% 3.03/1.02  fof(f24,plain,(
% 3.03/1.02    ! [X0,X1,X2,X3] : (r2_relset_1(X0,X1,X2,X2) | (~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))))),
% 3.03/1.02    inference(ennf_transformation,[],[f6])).
% 3.03/1.02  
% 3.03/1.02  fof(f25,plain,(
% 3.03/1.02    ! [X0,X1,X2,X3] : (r2_relset_1(X0,X1,X2,X2) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 3.03/1.02    inference(flattening,[],[f24])).
% 3.03/1.02  
% 3.03/1.02  fof(f48,plain,(
% 3.03/1.02    ( ! [X2,X0,X3,X1] : (r2_relset_1(X0,X1,X2,X2) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 3.03/1.02    inference(cnf_transformation,[],[f25])).
% 3.03/1.02  
% 3.03/1.02  fof(f3,axiom,(
% 3.03/1.02    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => (v2_funct_1(X0) => (k2_relat_1(k2_funct_1(X0)) = k1_relat_1(X0) & k2_relat_1(X0) = k1_relat_1(k2_funct_1(X0)))))),
% 3.03/1.02    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.03/1.02  
% 3.03/1.02  fof(f19,plain,(
% 3.03/1.02    ! [X0] : (((k2_relat_1(k2_funct_1(X0)) = k1_relat_1(X0) & k2_relat_1(X0) = k1_relat_1(k2_funct_1(X0))) | ~v2_funct_1(X0)) | (~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 3.03/1.02    inference(ennf_transformation,[],[f3])).
% 3.03/1.02  
% 3.03/1.02  fof(f20,plain,(
% 3.03/1.02    ! [X0] : ((k2_relat_1(k2_funct_1(X0)) = k1_relat_1(X0) & k2_relat_1(X0) = k1_relat_1(k2_funct_1(X0))) | ~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 3.03/1.02    inference(flattening,[],[f19])).
% 3.03/1.02  
% 3.03/1.02  fof(f44,plain,(
% 3.03/1.02    ( ! [X0] : (k2_relat_1(k2_funct_1(X0)) = k1_relat_1(X0) | ~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 3.03/1.02    inference(cnf_transformation,[],[f20])).
% 3.03/1.02  
% 3.03/1.02  fof(f56,plain,(
% 3.03/1.02    ( ! [X0,X1] : (v3_funct_2(k2_funct_2(X0,X1),X0,X0) | ~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) | ~v3_funct_2(X1,X0,X0) | ~v1_funct_2(X1,X0,X0) | ~v1_funct_1(X1)) )),
% 3.03/1.02    inference(cnf_transformation,[],[f31])).
% 3.03/1.02  
% 3.03/1.02  cnf(c_21,negated_conjecture,
% 3.03/1.02      ( m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) ),
% 3.03/1.02      inference(cnf_transformation,[],[f65]) ).
% 3.03/1.02  
% 3.03/1.02  cnf(c_690,negated_conjecture,
% 3.03/1.02      ( m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) ),
% 3.03/1.02      inference(subtyping,[status(esa)],[c_21]) ).
% 3.03/1.02  
% 3.03/1.02  cnf(c_1161,plain,
% 3.03/1.02      ( m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) = iProver_top ),
% 3.03/1.02      inference(predicate_to_equality,[status(thm)],[c_690]) ).
% 3.03/1.02  
% 3.03/1.02  cnf(c_19,plain,
% 3.03/1.02      ( ~ v1_funct_2(X0,X1,X1)
% 3.03/1.02      | ~ v3_funct_2(X0,X1,X1)
% 3.03/1.02      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X1)))
% 3.03/1.02      | ~ v1_funct_1(X0)
% 3.03/1.02      | k2_funct_2(X1,X0) = k2_funct_1(X0) ),
% 3.03/1.02      inference(cnf_transformation,[],[f60]) ).
% 3.03/1.02  
% 3.03/1.02  cnf(c_692,plain,
% 3.03/1.02      ( ~ v1_funct_2(X0_48,X0_49,X0_49)
% 3.03/1.02      | ~ v3_funct_2(X0_48,X0_49,X0_49)
% 3.03/1.02      | ~ m1_subset_1(X0_48,k1_zfmisc_1(k2_zfmisc_1(X0_49,X0_49)))
% 3.03/1.02      | ~ v1_funct_1(X0_48)
% 3.03/1.02      | k2_funct_2(X0_49,X0_48) = k2_funct_1(X0_48) ),
% 3.03/1.02      inference(subtyping,[status(esa)],[c_19]) ).
% 3.03/1.02  
% 3.03/1.02  cnf(c_1159,plain,
% 3.03/1.02      ( k2_funct_2(X0_49,X0_48) = k2_funct_1(X0_48)
% 3.03/1.02      | v1_funct_2(X0_48,X0_49,X0_49) != iProver_top
% 3.03/1.02      | v3_funct_2(X0_48,X0_49,X0_49) != iProver_top
% 3.03/1.02      | m1_subset_1(X0_48,k1_zfmisc_1(k2_zfmisc_1(X0_49,X0_49))) != iProver_top
% 3.03/1.02      | v1_funct_1(X0_48) != iProver_top ),
% 3.03/1.02      inference(predicate_to_equality,[status(thm)],[c_692]) ).
% 3.03/1.02  
% 3.03/1.02  cnf(c_1993,plain,
% 3.03/1.02      ( k2_funct_2(sK0,sK1) = k2_funct_1(sK1)
% 3.03/1.02      | v1_funct_2(sK1,sK0,sK0) != iProver_top
% 3.03/1.02      | v3_funct_2(sK1,sK0,sK0) != iProver_top
% 3.03/1.02      | v1_funct_1(sK1) != iProver_top ),
% 3.03/1.02      inference(superposition,[status(thm)],[c_1161,c_1159]) ).
% 3.03/1.02  
% 3.03/1.02  cnf(c_24,negated_conjecture,
% 3.03/1.02      ( v1_funct_1(sK1) ),
% 3.03/1.02      inference(cnf_transformation,[],[f62]) ).
% 3.03/1.02  
% 3.03/1.02  cnf(c_23,negated_conjecture,
% 3.03/1.02      ( v1_funct_2(sK1,sK0,sK0) ),
% 3.03/1.02      inference(cnf_transformation,[],[f63]) ).
% 3.03/1.02  
% 3.03/1.02  cnf(c_22,negated_conjecture,
% 3.03/1.02      ( v3_funct_2(sK1,sK0,sK0) ),
% 3.03/1.02      inference(cnf_transformation,[],[f64]) ).
% 3.03/1.02  
% 3.03/1.02  cnf(c_782,plain,
% 3.03/1.02      ( ~ v1_funct_2(sK1,sK0,sK0)
% 3.03/1.02      | ~ v3_funct_2(sK1,sK0,sK0)
% 3.03/1.02      | ~ m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
% 3.03/1.02      | ~ v1_funct_1(sK1)
% 3.03/1.02      | k2_funct_2(sK0,sK1) = k2_funct_1(sK1) ),
% 3.03/1.02      inference(instantiation,[status(thm)],[c_692]) ).
% 3.03/1.02  
% 3.03/1.02  cnf(c_2364,plain,
% 3.03/1.02      ( k2_funct_2(sK0,sK1) = k2_funct_1(sK1) ),
% 3.03/1.02      inference(global_propositional_subsumption,
% 3.03/1.02                [status(thm)],
% 3.03/1.02                [c_1993,c_24,c_23,c_22,c_21,c_782]) ).
% 3.03/1.02  
% 3.03/1.02  cnf(c_13,plain,
% 3.03/1.02      ( ~ v1_funct_2(X0,X1,X1)
% 3.03/1.02      | ~ v3_funct_2(X0,X1,X1)
% 3.03/1.02      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X1)))
% 3.03/1.02      | m1_subset_1(k2_funct_2(X1,X0),k1_zfmisc_1(k2_zfmisc_1(X1,X1)))
% 3.03/1.02      | ~ v1_funct_1(X0) ),
% 3.03/1.02      inference(cnf_transformation,[],[f57]) ).
% 3.03/1.02  
% 3.03/1.02  cnf(c_698,plain,
% 3.03/1.02      ( ~ v1_funct_2(X0_48,X0_49,X0_49)
% 3.03/1.02      | ~ v3_funct_2(X0_48,X0_49,X0_49)
% 3.03/1.02      | ~ m1_subset_1(X0_48,k1_zfmisc_1(k2_zfmisc_1(X0_49,X0_49)))
% 3.03/1.02      | m1_subset_1(k2_funct_2(X0_49,X0_48),k1_zfmisc_1(k2_zfmisc_1(X0_49,X0_49)))
% 3.03/1.02      | ~ v1_funct_1(X0_48) ),
% 3.03/1.02      inference(subtyping,[status(esa)],[c_13]) ).
% 3.03/1.02  
% 3.03/1.02  cnf(c_1153,plain,
% 3.03/1.02      ( v1_funct_2(X0_48,X0_49,X0_49) != iProver_top
% 3.03/1.02      | v3_funct_2(X0_48,X0_49,X0_49) != iProver_top
% 3.03/1.02      | m1_subset_1(X0_48,k1_zfmisc_1(k2_zfmisc_1(X0_49,X0_49))) != iProver_top
% 3.03/1.02      | m1_subset_1(k2_funct_2(X0_49,X0_48),k1_zfmisc_1(k2_zfmisc_1(X0_49,X0_49))) = iProver_top
% 3.03/1.02      | v1_funct_1(X0_48) != iProver_top ),
% 3.03/1.02      inference(predicate_to_equality,[status(thm)],[c_698]) ).
% 3.03/1.02  
% 3.03/1.02  cnf(c_2701,plain,
% 3.03/1.02      ( v1_funct_2(sK1,sK0,sK0) != iProver_top
% 3.03/1.02      | v3_funct_2(sK1,sK0,sK0) != iProver_top
% 3.03/1.02      | m1_subset_1(k2_funct_1(sK1),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) = iProver_top
% 3.03/1.02      | m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) != iProver_top
% 3.03/1.02      | v1_funct_1(sK1) != iProver_top ),
% 3.03/1.02      inference(superposition,[status(thm)],[c_2364,c_1153]) ).
% 3.03/1.02  
% 3.03/1.02  cnf(c_25,plain,
% 3.03/1.02      ( v1_funct_1(sK1) = iProver_top ),
% 3.03/1.02      inference(predicate_to_equality,[status(thm)],[c_24]) ).
% 3.03/1.02  
% 3.03/1.02  cnf(c_26,plain,
% 3.03/1.02      ( v1_funct_2(sK1,sK0,sK0) = iProver_top ),
% 3.03/1.02      inference(predicate_to_equality,[status(thm)],[c_23]) ).
% 3.03/1.02  
% 3.03/1.02  cnf(c_27,plain,
% 3.03/1.02      ( v3_funct_2(sK1,sK0,sK0) = iProver_top ),
% 3.03/1.02      inference(predicate_to_equality,[status(thm)],[c_22]) ).
% 3.03/1.02  
% 3.03/1.02  cnf(c_28,plain,
% 3.03/1.02      ( m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) = iProver_top ),
% 3.03/1.02      inference(predicate_to_equality,[status(thm)],[c_21]) ).
% 3.03/1.02  
% 3.03/1.02  cnf(c_3965,plain,
% 3.03/1.02      ( m1_subset_1(k2_funct_1(sK1),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) = iProver_top ),
% 3.03/1.02      inference(global_propositional_subsumption,
% 3.03/1.02                [status(thm)],
% 3.03/1.02                [c_2701,c_25,c_26,c_27,c_28]) ).
% 3.03/1.02  
% 3.03/1.02  cnf(c_18,plain,
% 3.03/1.02      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.03/1.02      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X4,X5)))
% 3.03/1.02      | ~ v1_funct_1(X0)
% 3.03/1.02      | ~ v1_funct_1(X3)
% 3.03/1.02      | k1_partfun1(X4,X5,X1,X2,X3,X0) = k5_relat_1(X3,X0) ),
% 3.03/1.02      inference(cnf_transformation,[],[f59]) ).
% 3.03/1.02  
% 3.03/1.02  cnf(c_693,plain,
% 3.03/1.02      ( ~ m1_subset_1(X0_48,k1_zfmisc_1(k2_zfmisc_1(X0_49,X1_49)))
% 3.03/1.02      | ~ m1_subset_1(X1_48,k1_zfmisc_1(k2_zfmisc_1(X2_49,X3_49)))
% 3.03/1.02      | ~ v1_funct_1(X0_48)
% 3.03/1.02      | ~ v1_funct_1(X1_48)
% 3.03/1.02      | k1_partfun1(X2_49,X3_49,X0_49,X1_49,X1_48,X0_48) = k5_relat_1(X1_48,X0_48) ),
% 3.03/1.02      inference(subtyping,[status(esa)],[c_18]) ).
% 3.03/1.02  
% 3.03/1.02  cnf(c_1158,plain,
% 3.03/1.02      ( k1_partfun1(X0_49,X1_49,X2_49,X3_49,X0_48,X1_48) = k5_relat_1(X0_48,X1_48)
% 3.03/1.02      | m1_subset_1(X1_48,k1_zfmisc_1(k2_zfmisc_1(X2_49,X3_49))) != iProver_top
% 3.03/1.02      | m1_subset_1(X0_48,k1_zfmisc_1(k2_zfmisc_1(X0_49,X1_49))) != iProver_top
% 3.03/1.02      | v1_funct_1(X0_48) != iProver_top
% 3.03/1.02      | v1_funct_1(X1_48) != iProver_top ),
% 3.03/1.02      inference(predicate_to_equality,[status(thm)],[c_693]) ).
% 3.03/1.02  
% 3.03/1.02  cnf(c_2849,plain,
% 3.03/1.02      ( k1_partfun1(sK0,sK0,X0_49,X1_49,sK1,X0_48) = k5_relat_1(sK1,X0_48)
% 3.03/1.02      | m1_subset_1(X0_48,k1_zfmisc_1(k2_zfmisc_1(X0_49,X1_49))) != iProver_top
% 3.03/1.02      | v1_funct_1(X0_48) != iProver_top
% 3.03/1.02      | v1_funct_1(sK1) != iProver_top ),
% 3.03/1.02      inference(superposition,[status(thm)],[c_1161,c_1158]) ).
% 3.03/1.02  
% 3.03/1.02  cnf(c_3004,plain,
% 3.03/1.02      ( v1_funct_1(X0_48) != iProver_top
% 3.03/1.02      | m1_subset_1(X0_48,k1_zfmisc_1(k2_zfmisc_1(X0_49,X1_49))) != iProver_top
% 3.03/1.02      | k1_partfun1(sK0,sK0,X0_49,X1_49,sK1,X0_48) = k5_relat_1(sK1,X0_48) ),
% 3.03/1.02      inference(global_propositional_subsumption,[status(thm)],[c_2849,c_25]) ).
% 3.03/1.02  
% 3.03/1.02  cnf(c_3005,plain,
% 3.03/1.02      ( k1_partfun1(sK0,sK0,X0_49,X1_49,sK1,X0_48) = k5_relat_1(sK1,X0_48)
% 3.03/1.02      | m1_subset_1(X0_48,k1_zfmisc_1(k2_zfmisc_1(X0_49,X1_49))) != iProver_top
% 3.03/1.02      | v1_funct_1(X0_48) != iProver_top ),
% 3.03/1.02      inference(renaming,[status(thm)],[c_3004]) ).
% 3.03/1.02  
% 3.03/1.02  cnf(c_3970,plain,
% 3.03/1.02      ( k1_partfun1(sK0,sK0,sK0,sK0,sK1,k2_funct_1(sK1)) = k5_relat_1(sK1,k2_funct_1(sK1))
% 3.03/1.02      | v1_funct_1(k2_funct_1(sK1)) != iProver_top ),
% 3.03/1.02      inference(superposition,[status(thm)],[c_3965,c_3005]) ).
% 3.03/1.02  
% 3.03/1.02  cnf(c_687,negated_conjecture,
% 3.03/1.02      ( v1_funct_1(sK1) ),
% 3.03/1.02      inference(subtyping,[status(esa)],[c_24]) ).
% 3.03/1.02  
% 3.03/1.02  cnf(c_1164,plain,
% 3.03/1.02      ( v1_funct_1(sK1) = iProver_top ),
% 3.03/1.02      inference(predicate_to_equality,[status(thm)],[c_687]) ).
% 3.03/1.02  
% 3.03/1.02  cnf(c_5,plain,
% 3.03/1.02      ( ~ v1_funct_1(X0)
% 3.03/1.02      | ~ v2_funct_1(X0)
% 3.03/1.02      | ~ v1_relat_1(X0)
% 3.03/1.02      | k5_relat_1(X0,k2_funct_1(X0)) = k6_partfun1(k1_relat_1(X0)) ),
% 3.03/1.02      inference(cnf_transformation,[],[f68]) ).
% 3.03/1.02  
% 3.03/1.02  cnf(c_701,plain,
% 3.03/1.02      ( ~ v1_funct_1(X0_48)
% 3.03/1.02      | ~ v2_funct_1(X0_48)
% 3.03/1.02      | ~ v1_relat_1(X0_48)
% 3.03/1.02      | k5_relat_1(X0_48,k2_funct_1(X0_48)) = k6_partfun1(k1_relat_1(X0_48)) ),
% 3.03/1.02      inference(subtyping,[status(esa)],[c_5]) ).
% 3.03/1.02  
% 3.03/1.02  cnf(c_1150,plain,
% 3.03/1.02      ( k5_relat_1(X0_48,k2_funct_1(X0_48)) = k6_partfun1(k1_relat_1(X0_48))
% 3.03/1.02      | v1_funct_1(X0_48) != iProver_top
% 3.03/1.02      | v2_funct_1(X0_48) != iProver_top
% 3.03/1.02      | v1_relat_1(X0_48) != iProver_top ),
% 3.03/1.02      inference(predicate_to_equality,[status(thm)],[c_701]) ).
% 3.03/1.02  
% 3.03/1.02  cnf(c_1530,plain,
% 3.03/1.02      ( k5_relat_1(sK1,k2_funct_1(sK1)) = k6_partfun1(k1_relat_1(sK1))
% 3.03/1.02      | v2_funct_1(sK1) != iProver_top
% 3.03/1.02      | v1_relat_1(sK1) != iProver_top ),
% 3.03/1.02      inference(superposition,[status(thm)],[c_1164,c_1150]) ).
% 3.03/1.02  
% 3.03/1.02  cnf(c_1,plain,
% 3.03/1.02      ( v1_relat_1(k2_zfmisc_1(X0,X1)) ),
% 3.03/1.02      inference(cnf_transformation,[],[f42]) ).
% 3.03/1.02  
% 3.03/1.02  cnf(c_83,plain,
% 3.03/1.02      ( v1_relat_1(k2_zfmisc_1(sK0,sK0)) ),
% 3.03/1.02      inference(instantiation,[status(thm)],[c_1]) ).
% 3.03/1.02  
% 3.03/1.02  cnf(c_757,plain,
% 3.03/1.02      ( ~ v1_funct_1(sK1)
% 3.03/1.02      | ~ v2_funct_1(sK1)
% 3.03/1.02      | ~ v1_relat_1(sK1)
% 3.03/1.02      | k5_relat_1(sK1,k2_funct_1(sK1)) = k6_partfun1(k1_relat_1(sK1)) ),
% 3.03/1.02      inference(instantiation,[status(thm)],[c_701]) ).
% 3.03/1.02  
% 3.03/1.02  cnf(c_9,plain,
% 3.03/1.02      ( ~ v3_funct_2(X0,X1,X2)
% 3.03/1.02      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.03/1.02      | ~ v1_funct_1(X0)
% 3.03/1.02      | v2_funct_1(X0) ),
% 3.03/1.02      inference(cnf_transformation,[],[f50]) ).
% 3.03/1.02  
% 3.03/1.02  cnf(c_699,plain,
% 3.03/1.02      ( ~ v3_funct_2(X0_48,X0_49,X1_49)
% 3.03/1.02      | ~ m1_subset_1(X0_48,k1_zfmisc_1(k2_zfmisc_1(X0_49,X1_49)))
% 3.03/1.02      | ~ v1_funct_1(X0_48)
% 3.03/1.02      | v2_funct_1(X0_48) ),
% 3.03/1.02      inference(subtyping,[status(esa)],[c_9]) ).
% 3.03/1.02  
% 3.03/1.02  cnf(c_763,plain,
% 3.03/1.02      ( ~ v3_funct_2(sK1,sK0,sK0)
% 3.03/1.02      | ~ m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
% 3.03/1.02      | ~ v1_funct_1(sK1)
% 3.03/1.02      | v2_funct_1(sK1) ),
% 3.03/1.02      inference(instantiation,[status(thm)],[c_699]) ).
% 3.03/1.02  
% 3.03/1.02  cnf(c_0,plain,
% 3.03/1.02      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1)) | ~ v1_relat_1(X1) | v1_relat_1(X0) ),
% 3.03/1.02      inference(cnf_transformation,[],[f41]) ).
% 3.03/1.02  
% 3.03/1.02  cnf(c_706,plain,
% 3.03/1.02      ( ~ m1_subset_1(X0_48,k1_zfmisc_1(X1_48))
% 3.03/1.02      | ~ v1_relat_1(X1_48)
% 3.03/1.02      | v1_relat_1(X0_48) ),
% 3.03/1.02      inference(subtyping,[status(esa)],[c_0]) ).
% 3.03/1.02  
% 3.03/1.02  cnf(c_1352,plain,
% 3.03/1.02      ( ~ m1_subset_1(X0_48,k1_zfmisc_1(k2_zfmisc_1(X0_49,X1_49)))
% 3.03/1.02      | v1_relat_1(X0_48)
% 3.03/1.02      | ~ v1_relat_1(k2_zfmisc_1(X0_49,X1_49)) ),
% 3.03/1.02      inference(instantiation,[status(thm)],[c_706]) ).
% 3.03/1.02  
% 3.03/1.02  cnf(c_1354,plain,
% 3.03/1.02      ( ~ m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
% 3.03/1.02      | ~ v1_relat_1(k2_zfmisc_1(sK0,sK0))
% 3.03/1.02      | v1_relat_1(sK1) ),
% 3.03/1.02      inference(instantiation,[status(thm)],[c_1352]) ).
% 3.03/1.02  
% 3.03/1.02  cnf(c_1788,plain,
% 3.03/1.02      ( k5_relat_1(sK1,k2_funct_1(sK1)) = k6_partfun1(k1_relat_1(sK1)) ),
% 3.03/1.02      inference(global_propositional_subsumption,
% 3.03/1.02                [status(thm)],
% 3.03/1.02                [c_1530,c_24,c_22,c_21,c_83,c_757,c_763,c_1354]) ).
% 3.03/1.02  
% 3.03/1.02  cnf(c_4045,plain,
% 3.03/1.02      ( k1_partfun1(sK0,sK0,sK0,sK0,sK1,k2_funct_1(sK1)) = k6_partfun1(k1_relat_1(sK1))
% 3.03/1.02      | v1_funct_1(k2_funct_1(sK1)) != iProver_top ),
% 3.03/1.02      inference(light_normalisation,[status(thm)],[c_3970,c_1788]) ).
% 3.03/1.02  
% 3.03/1.02  cnf(c_16,plain,
% 3.03/1.02      ( ~ v1_funct_2(X0,X1,X1)
% 3.03/1.02      | ~ v3_funct_2(X0,X1,X1)
% 3.03/1.02      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X1)))
% 3.03/1.02      | ~ v1_funct_1(X0)
% 3.03/1.02      | v1_funct_1(k2_funct_2(X1,X0)) ),
% 3.03/1.02      inference(cnf_transformation,[],[f54]) ).
% 3.03/1.02  
% 3.03/1.02  cnf(c_695,plain,
% 3.03/1.02      ( ~ v1_funct_2(X0_48,X0_49,X0_49)
% 3.03/1.02      | ~ v3_funct_2(X0_48,X0_49,X0_49)
% 3.03/1.02      | ~ m1_subset_1(X0_48,k1_zfmisc_1(k2_zfmisc_1(X0_49,X0_49)))
% 3.03/1.02      | ~ v1_funct_1(X0_48)
% 3.03/1.02      | v1_funct_1(k2_funct_2(X0_49,X0_48)) ),
% 3.03/1.02      inference(subtyping,[status(esa)],[c_16]) ).
% 3.03/1.02  
% 3.03/1.02  cnf(c_1156,plain,
% 3.03/1.02      ( v1_funct_2(X0_48,X0_49,X0_49) != iProver_top
% 3.03/1.02      | v3_funct_2(X0_48,X0_49,X0_49) != iProver_top
% 3.03/1.02      | m1_subset_1(X0_48,k1_zfmisc_1(k2_zfmisc_1(X0_49,X0_49))) != iProver_top
% 3.03/1.02      | v1_funct_1(X0_48) != iProver_top
% 3.03/1.02      | v1_funct_1(k2_funct_2(X0_49,X0_48)) = iProver_top ),
% 3.03/1.02      inference(predicate_to_equality,[status(thm)],[c_695]) ).
% 3.03/1.02  
% 3.03/1.02  cnf(c_1965,plain,
% 3.03/1.02      ( v1_funct_2(sK1,sK0,sK0) != iProver_top
% 3.03/1.02      | v3_funct_2(sK1,sK0,sK0) != iProver_top
% 3.03/1.02      | v1_funct_1(k2_funct_2(sK0,sK1)) = iProver_top
% 3.03/1.02      | v1_funct_1(sK1) != iProver_top ),
% 3.03/1.02      inference(superposition,[status(thm)],[c_1161,c_1156]) ).
% 3.03/1.02  
% 3.03/1.02  cnf(c_774,plain,
% 3.03/1.02      ( v1_funct_2(X0_48,X0_49,X0_49) != iProver_top
% 3.03/1.02      | v3_funct_2(X0_48,X0_49,X0_49) != iProver_top
% 3.03/1.02      | m1_subset_1(X0_48,k1_zfmisc_1(k2_zfmisc_1(X0_49,X0_49))) != iProver_top
% 3.03/1.02      | v1_funct_1(X0_48) != iProver_top
% 3.03/1.02      | v1_funct_1(k2_funct_2(X0_49,X0_48)) = iProver_top ),
% 3.03/1.02      inference(predicate_to_equality,[status(thm)],[c_695]) ).
% 3.03/1.02  
% 3.03/1.02  cnf(c_776,plain,
% 3.03/1.02      ( v1_funct_2(sK1,sK0,sK0) != iProver_top
% 3.03/1.02      | v3_funct_2(sK1,sK0,sK0) != iProver_top
% 3.03/1.02      | m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) != iProver_top
% 3.03/1.02      | v1_funct_1(k2_funct_2(sK0,sK1)) = iProver_top
% 3.03/1.02      | v1_funct_1(sK1) != iProver_top ),
% 3.03/1.02      inference(instantiation,[status(thm)],[c_774]) ).
% 3.03/1.02  
% 3.03/1.02  cnf(c_2274,plain,
% 3.03/1.02      ( v1_funct_1(k2_funct_2(sK0,sK1)) = iProver_top ),
% 3.03/1.02      inference(global_propositional_subsumption,
% 3.03/1.02                [status(thm)],
% 3.03/1.02                [c_1965,c_25,c_26,c_27,c_28,c_776]) ).
% 3.03/1.02  
% 3.03/1.02  cnf(c_2367,plain,
% 3.03/1.02      ( v1_funct_1(k2_funct_1(sK1)) = iProver_top ),
% 3.03/1.02      inference(demodulation,[status(thm)],[c_2364,c_2274]) ).
% 3.03/1.02  
% 3.03/1.02  cnf(c_4134,plain,
% 3.03/1.02      ( k1_partfun1(sK0,sK0,sK0,sK0,sK1,k2_funct_1(sK1)) = k6_partfun1(k1_relat_1(sK1)) ),
% 3.03/1.02      inference(global_propositional_subsumption,[status(thm)],[c_4045,c_2367]) ).
% 3.03/1.02  
% 3.03/1.02  cnf(c_20,negated_conjecture,
% 3.03/1.02      ( ~ r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK0,sK0,sK0,k2_funct_2(sK0,sK1),sK1),k6_partfun1(sK0))
% 3.03/1.02      | ~ r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK0,sK0,sK0,sK1,k2_funct_2(sK0,sK1)),k6_partfun1(sK0)) ),
% 3.03/1.02      inference(cnf_transformation,[],[f66]) ).
% 3.03/1.02  
% 3.03/1.02  cnf(c_691,negated_conjecture,
% 3.03/1.02      ( ~ r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK0,sK0,sK0,k2_funct_2(sK0,sK1),sK1),k6_partfun1(sK0))
% 3.03/1.02      | ~ r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK0,sK0,sK0,sK1,k2_funct_2(sK0,sK1)),k6_partfun1(sK0)) ),
% 3.03/1.02      inference(subtyping,[status(esa)],[c_20]) ).
% 3.03/1.02  
% 3.03/1.02  cnf(c_1160,plain,
% 3.03/1.02      ( r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK0,sK0,sK0,k2_funct_2(sK0,sK1),sK1),k6_partfun1(sK0)) != iProver_top
% 3.03/1.02      | r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK0,sK0,sK0,sK1,k2_funct_2(sK0,sK1)),k6_partfun1(sK0)) != iProver_top ),
% 3.03/1.02      inference(predicate_to_equality,[status(thm)],[c_691]) ).
% 3.03/1.02  
% 3.03/1.02  cnf(c_2368,plain,
% 3.03/1.02      ( r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK0,sK0,sK0,k2_funct_1(sK1),sK1),k6_partfun1(sK0)) != iProver_top
% 3.03/1.02      | r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK0,sK0,sK0,sK1,k2_funct_1(sK1)),k6_partfun1(sK0)) != iProver_top ),
% 3.03/1.02      inference(demodulation,[status(thm)],[c_2364,c_1160]) ).
% 3.03/1.02  
% 3.03/1.02  cnf(c_4137,plain,
% 3.03/1.02      ( r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK0,sK0,sK0,k2_funct_1(sK1),sK1),k6_partfun1(sK0)) != iProver_top
% 3.03/1.02      | r2_relset_1(sK0,sK0,k6_partfun1(k1_relat_1(sK1)),k6_partfun1(sK0)) != iProver_top ),
% 3.03/1.02      inference(demodulation,[status(thm)],[c_4134,c_2368]) ).
% 3.03/1.02  
% 3.03/1.02  cnf(c_721,plain,
% 3.03/1.02      ( X0_49 != X1_49 | k6_partfun1(X0_49) = k6_partfun1(X1_49) ),
% 3.03/1.02      theory(equality) ).
% 3.03/1.02  
% 3.03/1.02  cnf(c_735,plain,
% 3.03/1.02      ( sK0 != sK0 | k6_partfun1(sK0) = k6_partfun1(sK0) ),
% 3.03/1.02      inference(instantiation,[status(thm)],[c_721]) ).
% 3.03/1.02  
% 3.03/1.02  cnf(c_709,plain,( X0_49 = X0_49 ),theory(equality) ).
% 3.03/1.02  
% 3.03/1.02  cnf(c_743,plain,
% 3.03/1.02      ( sK0 = sK0 ),
% 3.03/1.02      inference(instantiation,[status(thm)],[c_709]) ).
% 3.03/1.02  
% 3.03/1.02  cnf(c_4,plain,
% 3.03/1.02      ( ~ v1_funct_1(X0)
% 3.03/1.02      | ~ v2_funct_1(X0)
% 3.03/1.02      | ~ v1_relat_1(X0)
% 3.03/1.02      | k5_relat_1(k2_funct_1(X0),X0) = k6_partfun1(k2_relat_1(X0)) ),
% 3.03/1.02      inference(cnf_transformation,[],[f67]) ).
% 3.03/1.02  
% 3.03/1.02  cnf(c_702,plain,
% 3.03/1.02      ( ~ v1_funct_1(X0_48)
% 3.03/1.02      | ~ v2_funct_1(X0_48)
% 3.03/1.02      | ~ v1_relat_1(X0_48)
% 3.03/1.02      | k5_relat_1(k2_funct_1(X0_48),X0_48) = k6_partfun1(k2_relat_1(X0_48)) ),
% 3.03/1.02      inference(subtyping,[status(esa)],[c_4]) ).
% 3.03/1.02  
% 3.03/1.02  cnf(c_754,plain,
% 3.03/1.02      ( ~ v1_funct_1(sK1)
% 3.03/1.02      | ~ v2_funct_1(sK1)
% 3.03/1.02      | ~ v1_relat_1(sK1)
% 3.03/1.02      | k5_relat_1(k2_funct_1(sK1),sK1) = k6_partfun1(k2_relat_1(sK1)) ),
% 3.03/1.02      inference(instantiation,[status(thm)],[c_702]) ).
% 3.03/1.02  
% 3.03/1.02  cnf(c_8,plain,
% 3.03/1.02      ( ~ v3_funct_2(X0,X1,X2)
% 3.03/1.02      | v2_funct_2(X0,X2)
% 3.03/1.02      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.03/1.02      | ~ v1_funct_1(X0) ),
% 3.03/1.02      inference(cnf_transformation,[],[f51]) ).
% 3.03/1.02  
% 3.03/1.02  cnf(c_12,plain,
% 3.03/1.02      ( ~ v2_funct_2(X0,X1)
% 3.03/1.02      | ~ v5_relat_1(X0,X1)
% 3.03/1.02      | ~ v1_relat_1(X0)
% 3.03/1.02      | k2_relat_1(X0) = X1 ),
% 3.03/1.02      inference(cnf_transformation,[],[f52]) ).
% 3.03/1.02  
% 3.03/1.02  cnf(c_316,plain,
% 3.03/1.02      ( ~ v3_funct_2(X0,X1,X2)
% 3.03/1.02      | ~ v5_relat_1(X3,X4)
% 3.03/1.02      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.03/1.02      | ~ v1_funct_1(X0)
% 3.03/1.02      | ~ v1_relat_1(X3)
% 3.03/1.02      | X3 != X0
% 3.03/1.02      | X4 != X2
% 3.03/1.02      | k2_relat_1(X3) = X4 ),
% 3.03/1.02      inference(resolution_lifted,[status(thm)],[c_8,c_12]) ).
% 3.03/1.02  
% 3.03/1.02  cnf(c_317,plain,
% 3.03/1.02      ( ~ v3_funct_2(X0,X1,X2)
% 3.03/1.02      | ~ v5_relat_1(X0,X2)
% 3.03/1.02      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.03/1.02      | ~ v1_funct_1(X0)
% 3.03/1.02      | ~ v1_relat_1(X0)
% 3.03/1.02      | k2_relat_1(X0) = X2 ),
% 3.03/1.02      inference(unflattening,[status(thm)],[c_316]) ).
% 3.03/1.02  
% 3.03/1.02  cnf(c_6,plain,
% 3.03/1.02      ( v5_relat_1(X0,X1) | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) ),
% 3.03/1.02      inference(cnf_transformation,[],[f47]) ).
% 3.03/1.02  
% 3.03/1.02  cnf(c_333,plain,
% 3.03/1.02      ( ~ v3_funct_2(X0,X1,X2)
% 3.03/1.02      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.03/1.02      | ~ v1_funct_1(X0)
% 3.03/1.02      | ~ v1_relat_1(X0)
% 3.03/1.02      | k2_relat_1(X0) = X2 ),
% 3.03/1.02      inference(forward_subsumption_resolution,[status(thm)],[c_317,c_6]) ).
% 3.03/1.02  
% 3.03/1.02  cnf(c_686,plain,
% 3.03/1.02      ( ~ v3_funct_2(X0_48,X0_49,X1_49)
% 3.03/1.02      | ~ m1_subset_1(X0_48,k1_zfmisc_1(k2_zfmisc_1(X0_49,X1_49)))
% 3.03/1.02      | ~ v1_funct_1(X0_48)
% 3.03/1.02      | ~ v1_relat_1(X0_48)
% 3.03/1.02      | k2_relat_1(X0_48) = X1_49 ),
% 3.03/1.02      inference(subtyping,[status(esa)],[c_333]) ).
% 3.03/1.02  
% 3.03/1.02  cnf(c_790,plain,
% 3.03/1.02      ( ~ v3_funct_2(sK1,sK0,sK0)
% 3.03/1.02      | ~ m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
% 3.03/1.02      | ~ v1_funct_1(sK1)
% 3.03/1.02      | ~ v1_relat_1(sK1)
% 3.03/1.02      | k2_relat_1(sK1) = sK0 ),
% 3.03/1.02      inference(instantiation,[status(thm)],[c_686]) ).
% 3.03/1.02  
% 3.03/1.02  cnf(c_17,plain,
% 3.03/1.02      ( m1_subset_1(k6_partfun1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0))) ),
% 3.03/1.02      inference(cnf_transformation,[],[f58]) ).
% 3.03/1.02  
% 3.03/1.02  cnf(c_694,plain,
% 3.03/1.02      ( m1_subset_1(k6_partfun1(X0_49),k1_zfmisc_1(k2_zfmisc_1(X0_49,X0_49))) ),
% 3.03/1.02      inference(subtyping,[status(esa)],[c_17]) ).
% 3.03/1.02  
% 3.03/1.02  cnf(c_1157,plain,
% 3.03/1.02      ( m1_subset_1(k6_partfun1(X0_49),k1_zfmisc_1(k2_zfmisc_1(X0_49,X0_49))) = iProver_top ),
% 3.03/1.02      inference(predicate_to_equality,[status(thm)],[c_694]) ).
% 3.03/1.02  
% 3.03/1.02  cnf(c_7,plain,
% 3.03/1.02      ( r2_relset_1(X0,X1,X2,X2)
% 3.03/1.02      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
% 3.03/1.02      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ),
% 3.03/1.02      inference(cnf_transformation,[],[f48]) ).
% 3.03/1.02  
% 3.03/1.02  cnf(c_700,plain,
% 3.03/1.02      ( r2_relset_1(X0_49,X1_49,X0_48,X0_48)
% 3.03/1.02      | ~ m1_subset_1(X0_48,k1_zfmisc_1(k2_zfmisc_1(X0_49,X1_49)))
% 3.03/1.02      | ~ m1_subset_1(X1_48,k1_zfmisc_1(k2_zfmisc_1(X0_49,X1_49))) ),
% 3.03/1.02      inference(subtyping,[status(esa)],[c_7]) ).
% 3.03/1.02  
% 3.03/1.02  cnf(c_1151,plain,
% 3.03/1.02      ( r2_relset_1(X0_49,X1_49,X0_48,X0_48) = iProver_top
% 3.03/1.02      | m1_subset_1(X0_48,k1_zfmisc_1(k2_zfmisc_1(X0_49,X1_49))) != iProver_top
% 3.03/1.02      | m1_subset_1(X1_48,k1_zfmisc_1(k2_zfmisc_1(X0_49,X1_49))) != iProver_top ),
% 3.03/1.02      inference(predicate_to_equality,[status(thm)],[c_700]) ).
% 3.03/1.02  
% 3.03/1.02  cnf(c_1594,plain,
% 3.03/1.02      ( r2_relset_1(X0_49,X0_49,k6_partfun1(X0_49),k6_partfun1(X0_49)) = iProver_top
% 3.03/1.02      | m1_subset_1(X0_48,k1_zfmisc_1(k2_zfmisc_1(X0_49,X0_49))) != iProver_top ),
% 3.03/1.02      inference(superposition,[status(thm)],[c_1157,c_1151]) ).
% 3.03/1.02  
% 3.03/1.02  cnf(c_1605,plain,
% 3.03/1.02      ( r2_relset_1(sK0,sK0,k6_partfun1(sK0),k6_partfun1(sK0)) = iProver_top
% 3.03/1.02      | m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) != iProver_top ),
% 3.03/1.02      inference(instantiation,[status(thm)],[c_1594]) ).
% 3.03/1.02  
% 3.03/1.02  cnf(c_711,plain,
% 3.03/1.02      ( X0_48 != X1_48 | X2_48 != X1_48 | X2_48 = X0_48 ),
% 3.03/1.02      theory(equality) ).
% 3.03/1.02  
% 3.03/1.02  cnf(c_1457,plain,
% 3.03/1.02      ( X0_48 != X1_48 | k6_partfun1(sK0) != X1_48 | k6_partfun1(sK0) = X0_48 ),
% 3.03/1.02      inference(instantiation,[status(thm)],[c_711]) ).
% 3.03/1.02  
% 3.03/1.02  cnf(c_1556,plain,
% 3.03/1.02      ( X0_48 != k6_partfun1(X0_49)
% 3.03/1.02      | k6_partfun1(sK0) = X0_48
% 3.03/1.02      | k6_partfun1(sK0) != k6_partfun1(X0_49) ),
% 3.03/1.02      inference(instantiation,[status(thm)],[c_1457]) ).
% 3.03/1.02  
% 3.03/1.02  cnf(c_1640,plain,
% 3.03/1.02      ( k5_relat_1(k2_funct_1(X0_48),X0_48) != k6_partfun1(k2_relat_1(X0_48))
% 3.03/1.02      | k6_partfun1(sK0) = k5_relat_1(k2_funct_1(X0_48),X0_48)
% 3.03/1.02      | k6_partfun1(sK0) != k6_partfun1(k2_relat_1(X0_48)) ),
% 3.03/1.02      inference(instantiation,[status(thm)],[c_1556]) ).
% 3.03/1.02  
% 3.03/1.02  cnf(c_1641,plain,
% 3.03/1.02      ( k5_relat_1(k2_funct_1(sK1),sK1) != k6_partfun1(k2_relat_1(sK1))
% 3.03/1.02      | k6_partfun1(sK0) = k5_relat_1(k2_funct_1(sK1),sK1)
% 3.03/1.02      | k6_partfun1(sK0) != k6_partfun1(k2_relat_1(sK1)) ),
% 3.03/1.02      inference(instantiation,[status(thm)],[c_1640]) ).
% 3.03/1.02  
% 3.03/1.02  cnf(c_1459,plain,
% 3.03/1.02      ( sK0 != X0_49 | k6_partfun1(sK0) = k6_partfun1(X0_49) ),
% 3.03/1.02      inference(instantiation,[status(thm)],[c_721]) ).
% 3.03/1.02  
% 3.03/1.02  cnf(c_1941,plain,
% 3.03/1.02      ( sK0 != k2_relat_1(X0_48)
% 3.03/1.02      | k6_partfun1(sK0) = k6_partfun1(k2_relat_1(X0_48)) ),
% 3.03/1.02      inference(instantiation,[status(thm)],[c_1459]) ).
% 3.03/1.02  
% 3.03/1.02  cnf(c_1942,plain,
% 3.03/1.02      ( sK0 != k2_relat_1(sK1)
% 3.03/1.02      | k6_partfun1(sK0) = k6_partfun1(k2_relat_1(sK1)) ),
% 3.03/1.02      inference(instantiation,[status(thm)],[c_1941]) ).
% 3.03/1.02  
% 3.03/1.02  cnf(c_712,plain,
% 3.03/1.02      ( X0_49 != X1_49 | X2_49 != X1_49 | X2_49 = X0_49 ),
% 3.03/1.02      theory(equality) ).
% 3.03/1.02  
% 3.03/1.02  cnf(c_2089,plain,
% 3.03/1.02      ( k2_relat_1(X0_48) != X0_49 | sK0 != X0_49 | sK0 = k2_relat_1(X0_48) ),
% 3.03/1.02      inference(instantiation,[status(thm)],[c_712]) ).
% 3.03/1.02  
% 3.03/1.02  cnf(c_2090,plain,
% 3.03/1.02      ( k2_relat_1(sK1) != sK0 | sK0 = k2_relat_1(sK1) | sK0 != sK0 ),
% 3.03/1.02      inference(instantiation,[status(thm)],[c_2089]) ).
% 3.03/1.02  
% 3.03/1.02  cnf(c_2375,plain,
% 3.03/1.02      ( v1_funct_1(k2_funct_1(sK1)) ),
% 3.03/1.02      inference(predicate_to_equality_rev,[status(thm)],[c_2367]) ).
% 3.03/1.02  
% 3.03/1.02  cnf(c_2821,plain,
% 3.03/1.02      ( ~ v1_funct_2(sK1,sK0,sK0)
% 3.03/1.02      | ~ v3_funct_2(sK1,sK0,sK0)
% 3.03/1.02      | m1_subset_1(k2_funct_1(sK1),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
% 3.03/1.02      | ~ m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
% 3.03/1.02      | ~ v1_funct_1(sK1) ),
% 3.03/1.02      inference(predicate_to_equality_rev,[status(thm)],[c_2701]) ).
% 3.03/1.02  
% 3.03/1.02  cnf(c_3220,plain,
% 3.03/1.02      ( ~ m1_subset_1(X0_48,k1_zfmisc_1(k2_zfmisc_1(X0_49,X1_49)))
% 3.03/1.02      | ~ m1_subset_1(k2_funct_1(sK1),k1_zfmisc_1(k2_zfmisc_1(X2_49,X3_49)))
% 3.03/1.02      | ~ v1_funct_1(X0_48)
% 3.03/1.02      | ~ v1_funct_1(k2_funct_1(sK1))
% 3.03/1.02      | k1_partfun1(X2_49,X3_49,X0_49,X1_49,k2_funct_1(sK1),X0_48) = k5_relat_1(k2_funct_1(sK1),X0_48) ),
% 3.03/1.02      inference(instantiation,[status(thm)],[c_693]) ).
% 3.03/1.02  
% 3.03/1.02  cnf(c_3223,plain,
% 3.03/1.02      ( ~ m1_subset_1(k2_funct_1(sK1),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
% 3.03/1.02      | ~ m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
% 3.03/1.02      | ~ v1_funct_1(k2_funct_1(sK1))
% 3.03/1.02      | ~ v1_funct_1(sK1)
% 3.03/1.02      | k1_partfun1(sK0,sK0,sK0,sK0,k2_funct_1(sK1),sK1) = k5_relat_1(k2_funct_1(sK1),sK1) ),
% 3.03/1.02      inference(instantiation,[status(thm)],[c_3220]) ).
% 3.03/1.02  
% 3.03/1.02  cnf(c_722,plain,
% 3.03/1.02      ( ~ r2_relset_1(X0_49,X1_49,X0_48,X1_48)
% 3.03/1.02      | r2_relset_1(X2_49,X3_49,X2_48,X3_48)
% 3.03/1.02      | X2_49 != X0_49
% 3.03/1.02      | X3_49 != X1_49
% 3.03/1.02      | X2_48 != X0_48
% 3.03/1.02      | X3_48 != X1_48 ),
% 3.03/1.02      theory(equality) ).
% 3.03/1.02  
% 3.03/1.02  cnf(c_2202,plain,
% 3.03/1.02      ( ~ r2_relset_1(X0_49,X1_49,X0_48,X1_48)
% 3.03/1.02      | r2_relset_1(X2_49,X3_49,k1_partfun1(X4_49,X5_49,X6_49,X7_49,k2_funct_1(sK1),X2_48),k6_partfun1(X8_49))
% 3.03/1.02      | X2_49 != X0_49
% 3.03/1.02      | X3_49 != X1_49
% 3.03/1.02      | k1_partfun1(X4_49,X5_49,X6_49,X7_49,k2_funct_1(sK1),X2_48) != X0_48
% 3.03/1.02      | k6_partfun1(X8_49) != X1_48 ),
% 3.03/1.02      inference(instantiation,[status(thm)],[c_722]) ).
% 3.03/1.02  
% 3.03/1.02  cnf(c_3082,plain,
% 3.03/1.02      ( ~ r2_relset_1(X0_49,X1_49,X0_48,k6_partfun1(X2_49))
% 3.03/1.02      | r2_relset_1(X3_49,X4_49,k1_partfun1(X5_49,X6_49,X7_49,X8_49,k2_funct_1(sK1),X1_48),k6_partfun1(X9_49))
% 3.03/1.02      | X3_49 != X0_49
% 3.03/1.02      | X4_49 != X1_49
% 3.03/1.02      | k1_partfun1(X5_49,X6_49,X7_49,X8_49,k2_funct_1(sK1),X1_48) != X0_48
% 3.03/1.02      | k6_partfun1(X9_49) != k6_partfun1(X2_49) ),
% 3.03/1.02      inference(instantiation,[status(thm)],[c_2202]) ).
% 3.03/1.02  
% 3.03/1.02  cnf(c_4067,plain,
% 3.03/1.02      ( r2_relset_1(X0_49,X1_49,k1_partfun1(X2_49,X3_49,X4_49,X5_49,k2_funct_1(sK1),X0_48),k6_partfun1(X6_49))
% 3.03/1.02      | ~ r2_relset_1(X7_49,X8_49,k6_partfun1(X9_49),k6_partfun1(X9_49))
% 3.03/1.02      | X0_49 != X7_49
% 3.03/1.02      | X1_49 != X8_49
% 3.03/1.02      | k1_partfun1(X2_49,X3_49,X4_49,X5_49,k2_funct_1(sK1),X0_48) != k6_partfun1(X9_49)
% 3.03/1.02      | k6_partfun1(X6_49) != k6_partfun1(X9_49) ),
% 3.03/1.02      inference(instantiation,[status(thm)],[c_3082]) ).
% 3.03/1.02  
% 3.03/1.02  cnf(c_4069,plain,
% 3.03/1.02      ( X0_49 != X1_49
% 3.03/1.02      | X2_49 != X3_49
% 3.03/1.02      | k1_partfun1(X4_49,X5_49,X6_49,X7_49,k2_funct_1(sK1),X0_48) != k6_partfun1(X8_49)
% 3.03/1.02      | k6_partfun1(X9_49) != k6_partfun1(X8_49)
% 3.03/1.02      | r2_relset_1(X0_49,X2_49,k1_partfun1(X4_49,X5_49,X6_49,X7_49,k2_funct_1(sK1),X0_48),k6_partfun1(X9_49)) = iProver_top
% 3.03/1.02      | r2_relset_1(X1_49,X3_49,k6_partfun1(X8_49),k6_partfun1(X8_49)) != iProver_top ),
% 3.03/1.02      inference(predicate_to_equality,[status(thm)],[c_4067]) ).
% 3.03/1.02  
% 3.03/1.02  cnf(c_4071,plain,
% 3.03/1.02      ( sK0 != sK0
% 3.03/1.02      | k1_partfun1(sK0,sK0,sK0,sK0,k2_funct_1(sK1),sK1) != k6_partfun1(sK0)
% 3.03/1.02      | k6_partfun1(sK0) != k6_partfun1(sK0)
% 3.03/1.02      | r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK0,sK0,sK0,k2_funct_1(sK1),sK1),k6_partfun1(sK0)) = iProver_top
% 3.03/1.02      | r2_relset_1(sK0,sK0,k6_partfun1(sK0),k6_partfun1(sK0)) != iProver_top ),
% 3.03/1.02      inference(instantiation,[status(thm)],[c_4069]) ).
% 3.03/1.02  
% 3.03/1.02  cnf(c_1498,plain,
% 3.03/1.02      ( X0_48 != X1_48
% 3.03/1.02      | X0_48 = k6_partfun1(X0_49)
% 3.03/1.02      | k6_partfun1(X0_49) != X1_48 ),
% 3.03/1.02      inference(instantiation,[status(thm)],[c_711]) ).
% 3.03/1.02  
% 3.03/1.02  cnf(c_2987,plain,
% 3.03/1.02      ( X0_48 != k5_relat_1(k2_funct_1(X1_48),X1_48)
% 3.03/1.02      | X0_48 = k6_partfun1(sK0)
% 3.03/1.02      | k6_partfun1(sK0) != k5_relat_1(k2_funct_1(X1_48),X1_48) ),
% 3.03/1.02      inference(instantiation,[status(thm)],[c_1498]) ).
% 3.03/1.02  
% 3.03/1.02  cnf(c_4267,plain,
% 3.03/1.02      ( k1_partfun1(X0_49,X1_49,X2_49,X3_49,k2_funct_1(sK1),sK1) != k5_relat_1(k2_funct_1(sK1),sK1)
% 3.03/1.02      | k1_partfun1(X0_49,X1_49,X2_49,X3_49,k2_funct_1(sK1),sK1) = k6_partfun1(sK0)
% 3.03/1.02      | k6_partfun1(sK0) != k5_relat_1(k2_funct_1(sK1),sK1) ),
% 3.03/1.02      inference(instantiation,[status(thm)],[c_2987]) ).
% 3.03/1.02  
% 3.03/1.02  cnf(c_4271,plain,
% 3.03/1.02      ( k1_partfun1(sK0,sK0,sK0,sK0,k2_funct_1(sK1),sK1) != k5_relat_1(k2_funct_1(sK1),sK1)
% 3.03/1.02      | k1_partfun1(sK0,sK0,sK0,sK0,k2_funct_1(sK1),sK1) = k6_partfun1(sK0)
% 3.03/1.02      | k6_partfun1(sK0) != k5_relat_1(k2_funct_1(sK1),sK1) ),
% 3.03/1.02      inference(instantiation,[status(thm)],[c_4267]) ).
% 3.03/1.02  
% 3.03/1.02  cnf(c_4644,plain,
% 3.03/1.02      ( r2_relset_1(sK0,sK0,k6_partfun1(k1_relat_1(sK1)),k6_partfun1(sK0)) != iProver_top ),
% 3.03/1.02      inference(global_propositional_subsumption,
% 3.03/1.02                [status(thm)],
% 3.03/1.02                [c_4137,c_24,c_23,c_22,c_21,c_28,c_83,c_735,c_743,c_754,
% 3.03/1.02                 c_763,c_790,c_1354,c_1605,c_1641,c_1942,c_2090,c_2375,
% 3.03/1.02                 c_2821,c_3223,c_4071,c_4271]) ).
% 3.03/1.02  
% 3.03/1.02  cnf(c_1165,plain,
% 3.03/1.02      ( k2_relat_1(X0_48) = X0_49
% 3.03/1.02      | v3_funct_2(X0_48,X1_49,X0_49) != iProver_top
% 3.03/1.02      | m1_subset_1(X0_48,k1_zfmisc_1(k2_zfmisc_1(X1_49,X0_49))) != iProver_top
% 3.03/1.02      | v1_funct_1(X0_48) != iProver_top
% 3.03/1.02      | v1_relat_1(X0_48) != iProver_top ),
% 3.03/1.02      inference(predicate_to_equality,[status(thm)],[c_686]) ).
% 3.03/1.02  
% 3.03/1.02  cnf(c_3979,plain,
% 3.03/1.02      ( k2_relat_1(k2_funct_1(sK1)) = sK0
% 3.03/1.02      | v3_funct_2(k2_funct_1(sK1),sK0,sK0) != iProver_top
% 3.03/1.02      | v1_funct_1(k2_funct_1(sK1)) != iProver_top
% 3.03/1.02      | v1_relat_1(k2_funct_1(sK1)) != iProver_top ),
% 3.03/1.02      inference(superposition,[status(thm)],[c_3965,c_1165]) ).
% 3.03/1.02  
% 3.03/1.02  cnf(c_2,plain,
% 3.03/1.02      ( ~ v1_funct_1(X0)
% 3.03/1.02      | ~ v2_funct_1(X0)
% 3.03/1.02      | ~ v1_relat_1(X0)
% 3.03/1.02      | k2_relat_1(k2_funct_1(X0)) = k1_relat_1(X0) ),
% 3.03/1.02      inference(cnf_transformation,[],[f44]) ).
% 3.03/1.02  
% 3.03/1.02  cnf(c_704,plain,
% 3.03/1.02      ( ~ v1_funct_1(X0_48)
% 3.03/1.02      | ~ v2_funct_1(X0_48)
% 3.03/1.02      | ~ v1_relat_1(X0_48)
% 3.03/1.02      | k2_relat_1(k2_funct_1(X0_48)) = k1_relat_1(X0_48) ),
% 3.03/1.02      inference(subtyping,[status(esa)],[c_2]) ).
% 3.03/1.02  
% 3.03/1.02  cnf(c_1147,plain,
% 3.03/1.02      ( k2_relat_1(k2_funct_1(X0_48)) = k1_relat_1(X0_48)
% 3.03/1.02      | v1_funct_1(X0_48) != iProver_top
% 3.03/1.02      | v2_funct_1(X0_48) != iProver_top
% 3.03/1.02      | v1_relat_1(X0_48) != iProver_top ),
% 3.03/1.02      inference(predicate_to_equality,[status(thm)],[c_704]) ).
% 3.03/1.02  
% 3.03/1.02  cnf(c_1467,plain,
% 3.03/1.02      ( k2_relat_1(k2_funct_1(sK1)) = k1_relat_1(sK1)
% 3.03/1.02      | v2_funct_1(sK1) != iProver_top
% 3.03/1.02      | v1_relat_1(sK1) != iProver_top ),
% 3.03/1.02      inference(superposition,[status(thm)],[c_1164,c_1147]) ).
% 3.03/1.02  
% 3.03/1.02  cnf(c_748,plain,
% 3.03/1.02      ( ~ v1_funct_1(sK1)
% 3.03/1.02      | ~ v2_funct_1(sK1)
% 3.03/1.02      | ~ v1_relat_1(sK1)
% 3.03/1.02      | k2_relat_1(k2_funct_1(sK1)) = k1_relat_1(sK1) ),
% 3.03/1.02      inference(instantiation,[status(thm)],[c_704]) ).
% 3.03/1.02  
% 3.03/1.02  cnf(c_1673,plain,
% 3.03/1.02      ( k2_relat_1(k2_funct_1(sK1)) = k1_relat_1(sK1) ),
% 3.03/1.02      inference(global_propositional_subsumption,
% 3.03/1.02                [status(thm)],
% 3.03/1.02                [c_1467,c_24,c_22,c_21,c_83,c_748,c_763,c_1354]) ).
% 3.03/1.02  
% 3.03/1.02  cnf(c_3984,plain,
% 3.03/1.02      ( k1_relat_1(sK1) = sK0
% 3.03/1.02      | v3_funct_2(k2_funct_1(sK1),sK0,sK0) != iProver_top
% 3.03/1.02      | v1_funct_1(k2_funct_1(sK1)) != iProver_top
% 3.03/1.02      | v1_relat_1(k2_funct_1(sK1)) != iProver_top ),
% 3.03/1.02      inference(demodulation,[status(thm)],[c_3979,c_1673]) ).
% 3.03/1.02  
% 3.03/1.02  cnf(c_82,plain,
% 3.03/1.02      ( v1_relat_1(k2_zfmisc_1(X0,X1)) = iProver_top ),
% 3.03/1.02      inference(predicate_to_equality,[status(thm)],[c_1]) ).
% 3.03/1.02  
% 3.03/1.02  cnf(c_84,plain,
% 3.03/1.02      ( v1_relat_1(k2_zfmisc_1(sK0,sK0)) = iProver_top ),
% 3.03/1.02      inference(instantiation,[status(thm)],[c_82]) ).
% 3.03/1.02  
% 3.03/1.02  cnf(c_14,plain,
% 3.03/1.02      ( ~ v1_funct_2(X0,X1,X1)
% 3.03/1.02      | ~ v3_funct_2(X0,X1,X1)
% 3.03/1.02      | v3_funct_2(k2_funct_2(X1,X0),X1,X1)
% 3.03/1.02      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X1)))
% 3.03/1.02      | ~ v1_funct_1(X0) ),
% 3.03/1.02      inference(cnf_transformation,[],[f56]) ).
% 3.03/1.02  
% 3.03/1.02  cnf(c_697,plain,
% 3.03/1.02      ( ~ v1_funct_2(X0_48,X0_49,X0_49)
% 3.03/1.02      | ~ v3_funct_2(X0_48,X0_49,X0_49)
% 3.03/1.02      | v3_funct_2(k2_funct_2(X0_49,X0_48),X0_49,X0_49)
% 3.03/1.02      | ~ m1_subset_1(X0_48,k1_zfmisc_1(k2_zfmisc_1(X0_49,X0_49)))
% 3.03/1.02      | ~ v1_funct_1(X0_48) ),
% 3.03/1.02      inference(subtyping,[status(esa)],[c_14]) ).
% 3.03/1.02  
% 3.03/1.02  cnf(c_1154,plain,
% 3.03/1.02      ( v1_funct_2(X0_48,X0_49,X0_49) != iProver_top
% 3.03/1.02      | v3_funct_2(X0_48,X0_49,X0_49) != iProver_top
% 3.03/1.02      | v3_funct_2(k2_funct_2(X0_49,X0_48),X0_49,X0_49) = iProver_top
% 3.03/1.02      | m1_subset_1(X0_48,k1_zfmisc_1(k2_zfmisc_1(X0_49,X0_49))) != iProver_top
% 3.03/1.02      | v1_funct_1(X0_48) != iProver_top ),
% 3.03/1.02      inference(predicate_to_equality,[status(thm)],[c_697]) ).
% 3.03/1.02  
% 3.03/1.02  cnf(c_2133,plain,
% 3.03/1.02      ( v1_funct_2(sK1,sK0,sK0) != iProver_top
% 3.03/1.02      | v3_funct_2(k2_funct_2(sK0,sK1),sK0,sK0) = iProver_top
% 3.03/1.02      | v3_funct_2(sK1,sK0,sK0) != iProver_top
% 3.03/1.02      | v1_funct_1(sK1) != iProver_top ),
% 3.03/1.02      inference(superposition,[status(thm)],[c_1161,c_1154]) ).
% 3.03/1.02  
% 3.03/1.02  cnf(c_768,plain,
% 3.03/1.02      ( v1_funct_2(X0_48,X0_49,X0_49) != iProver_top
% 3.03/1.02      | v3_funct_2(X0_48,X0_49,X0_49) != iProver_top
% 3.03/1.02      | v3_funct_2(k2_funct_2(X0_49,X0_48),X0_49,X0_49) = iProver_top
% 3.03/1.02      | m1_subset_1(X0_48,k1_zfmisc_1(k2_zfmisc_1(X0_49,X0_49))) != iProver_top
% 3.03/1.02      | v1_funct_1(X0_48) != iProver_top ),
% 3.03/1.02      inference(predicate_to_equality,[status(thm)],[c_697]) ).
% 3.03/1.02  
% 3.03/1.02  cnf(c_770,plain,
% 3.03/1.02      ( v1_funct_2(sK1,sK0,sK0) != iProver_top
% 3.03/1.02      | v3_funct_2(k2_funct_2(sK0,sK1),sK0,sK0) = iProver_top
% 3.03/1.02      | v3_funct_2(sK1,sK0,sK0) != iProver_top
% 3.03/1.02      | m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) != iProver_top
% 3.03/1.02      | v1_funct_1(sK1) != iProver_top ),
% 3.03/1.02      inference(instantiation,[status(thm)],[c_768]) ).
% 3.03/1.02  
% 3.03/1.02  cnf(c_2378,plain,
% 3.03/1.02      ( v3_funct_2(k2_funct_2(sK0,sK1),sK0,sK0) = iProver_top ),
% 3.03/1.02      inference(global_propositional_subsumption,
% 3.03/1.02                [status(thm)],
% 3.03/1.02                [c_2133,c_25,c_26,c_27,c_28,c_770]) ).
% 3.03/1.02  
% 3.03/1.02  cnf(c_2382,plain,
% 3.03/1.02      ( v3_funct_2(k2_funct_1(sK1),sK0,sK0) = iProver_top ),
% 3.03/1.02      inference(light_normalisation,[status(thm)],[c_2378,c_2364]) ).
% 3.03/1.02  
% 3.03/1.02  cnf(c_1145,plain,
% 3.03/1.02      ( m1_subset_1(X0_48,k1_zfmisc_1(X1_48)) != iProver_top
% 3.03/1.02      | v1_relat_1(X1_48) != iProver_top
% 3.03/1.02      | v1_relat_1(X0_48) = iProver_top ),
% 3.03/1.02      inference(predicate_to_equality,[status(thm)],[c_706]) ).
% 3.03/1.02  
% 3.03/1.02  cnf(c_3978,plain,
% 3.03/1.02      ( v1_relat_1(k2_zfmisc_1(sK0,sK0)) != iProver_top
% 3.03/1.02      | v1_relat_1(k2_funct_1(sK1)) = iProver_top ),
% 3.03/1.02      inference(superposition,[status(thm)],[c_3965,c_1145]) ).
% 3.03/1.02  
% 3.03/1.02  cnf(c_4140,plain,
% 3.03/1.02      ( k1_relat_1(sK1) = sK0 ),
% 3.03/1.02      inference(global_propositional_subsumption,
% 3.03/1.02                [status(thm)],
% 3.03/1.02                [c_3984,c_84,c_2367,c_2382,c_3978]) ).
% 3.03/1.02  
% 3.03/1.02  cnf(c_4648,plain,
% 3.03/1.02      ( r2_relset_1(sK0,sK0,k6_partfun1(sK0),k6_partfun1(sK0)) != iProver_top ),
% 3.03/1.02      inference(light_normalisation,[status(thm)],[c_4644,c_4140]) ).
% 3.03/1.02  
% 3.03/1.02  cnf(c_1886,plain,
% 3.03/1.02      ( r2_relset_1(X0_49,X0_49,k6_partfun1(X0_49),k6_partfun1(X0_49)) = iProver_top ),
% 3.03/1.02      inference(superposition,[status(thm)],[c_1157,c_1594]) ).
% 3.03/1.02  
% 3.03/1.02  cnf(c_4650,plain,
% 3.03/1.02      ( $false ),
% 3.03/1.02      inference(forward_subsumption_resolution,[status(thm)],[c_4648,c_1886]) ).
% 3.03/1.02  
% 3.03/1.02  
% 3.03/1.02  % SZS output end CNFRefutation for theBenchmark.p
% 3.03/1.02  
% 3.03/1.02  ------                               Statistics
% 3.03/1.02  
% 3.03/1.02  ------ General
% 3.03/1.02  
% 3.03/1.02  abstr_ref_over_cycles:                  0
% 3.03/1.02  abstr_ref_under_cycles:                 0
% 3.03/1.02  gc_basic_clause_elim:                   0
% 3.03/1.02  forced_gc_time:                         0
% 3.03/1.02  parsing_time:                           0.023
% 3.03/1.02  unif_index_cands_time:                  0.
% 3.03/1.02  unif_index_add_time:                    0.
% 3.03/1.02  orderings_time:                         0.
% 3.03/1.02  out_proof_time:                         0.013
% 3.03/1.02  total_time:                             0.2
% 3.03/1.02  num_of_symbols:                         54
% 3.03/1.02  num_of_terms:                           4150
% 3.03/1.02  
% 3.03/1.02  ------ Preprocessing
% 3.03/1.02  
% 3.03/1.02  num_of_splits:                          0
% 3.03/1.02  num_of_split_atoms:                     0
% 3.03/1.02  num_of_reused_defs:                     0
% 3.03/1.02  num_eq_ax_congr_red:                    8
% 3.03/1.02  num_of_sem_filtered_clauses:            1
% 3.03/1.02  num_of_subtypes:                        3
% 3.03/1.02  monotx_restored_types:                  1
% 3.03/1.02  sat_num_of_epr_types:                   0
% 3.03/1.02  sat_num_of_non_cyclic_types:            0
% 3.03/1.02  sat_guarded_non_collapsed_types:        0
% 3.03/1.02  num_pure_diseq_elim:                    0
% 3.03/1.02  simp_replaced_by:                       0
% 3.03/1.02  res_preprocessed:                       126
% 3.03/1.02  prep_upred:                             0
% 3.03/1.02  prep_unflattend:                        6
% 3.03/1.02  smt_new_axioms:                         0
% 3.03/1.02  pred_elim_cands:                        7
% 3.03/1.02  pred_elim:                              2
% 3.03/1.02  pred_elim_cl:                           3
% 3.03/1.02  pred_elim_cycles:                       5
% 3.03/1.02  merged_defs:                            0
% 3.03/1.02  merged_defs_ncl:                        0
% 3.03/1.02  bin_hyper_res:                          0
% 3.03/1.02  prep_cycles:                            4
% 3.03/1.02  pred_elim_time:                         0.005
% 3.03/1.02  splitting_time:                         0.
% 3.03/1.02  sem_filter_time:                        0.
% 3.03/1.02  monotx_time:                            0.001
% 3.03/1.02  subtype_inf_time:                       0.001
% 3.03/1.02  
% 3.03/1.02  ------ Problem properties
% 3.03/1.02  
% 3.03/1.02  clauses:                                21
% 3.03/1.02  conjectures:                            5
% 3.03/1.02  epr:                                    3
% 3.03/1.02  horn:                                   21
% 3.03/1.02  ground:                                 5
% 3.03/1.02  unary:                                  6
% 3.03/1.02  binary:                                 1
% 3.03/1.02  lits:                                   69
% 3.03/1.02  lits_eq:                                7
% 3.03/1.02  fd_pure:                                0
% 3.03/1.02  fd_pseudo:                              0
% 3.03/1.02  fd_cond:                                0
% 3.03/1.02  fd_pseudo_cond:                         1
% 3.03/1.02  ac_symbols:                             0
% 3.03/1.02  
% 3.03/1.02  ------ Propositional Solver
% 3.03/1.02  
% 3.03/1.02  prop_solver_calls:                      29
% 3.03/1.02  prop_fast_solver_calls:                 1087
% 3.03/1.02  smt_solver_calls:                       0
% 3.03/1.02  smt_fast_solver_calls:                  0
% 3.03/1.02  prop_num_of_clauses:                    1264
% 3.03/1.02  prop_preprocess_simplified:             5152
% 3.03/1.02  prop_fo_subsumed:                       54
% 3.03/1.02  prop_solver_time:                       0.
% 3.03/1.02  smt_solver_time:                        0.
% 3.03/1.02  smt_fast_solver_time:                   0.
% 3.03/1.02  prop_fast_solver_time:                  0.
% 3.03/1.02  prop_unsat_core_time:                   0.
% 3.03/1.02  
% 3.03/1.02  ------ QBF
% 3.03/1.02  
% 3.03/1.02  qbf_q_res:                              0
% 3.03/1.02  qbf_num_tautologies:                    0
% 3.03/1.02  qbf_prep_cycles:                        0
% 3.03/1.02  
% 3.03/1.02  ------ BMC1
% 3.03/1.02  
% 3.03/1.02  bmc1_current_bound:                     -1
% 3.03/1.02  bmc1_last_solved_bound:                 -1
% 3.03/1.02  bmc1_unsat_core_size:                   -1
% 3.03/1.02  bmc1_unsat_core_parents_size:           -1
% 3.03/1.02  bmc1_merge_next_fun:                    0
% 3.03/1.02  bmc1_unsat_core_clauses_time:           0.
% 3.03/1.02  
% 3.03/1.02  ------ Instantiation
% 3.03/1.02  
% 3.03/1.02  inst_num_of_clauses:                    486
% 3.03/1.02  inst_num_in_passive:                    30
% 3.03/1.02  inst_num_in_active:                     311
% 3.03/1.02  inst_num_in_unprocessed:                145
% 3.03/1.02  inst_num_of_loops:                      330
% 3.03/1.02  inst_num_of_learning_restarts:          0
% 3.03/1.02  inst_num_moves_active_passive:          15
% 3.03/1.02  inst_lit_activity:                      0
% 3.03/1.02  inst_lit_activity_moves:                0
% 3.03/1.02  inst_num_tautologies:                   0
% 3.03/1.02  inst_num_prop_implied:                  0
% 3.03/1.02  inst_num_existing_simplified:           0
% 3.03/1.02  inst_num_eq_res_simplified:             0
% 3.03/1.02  inst_num_child_elim:                    0
% 3.03/1.02  inst_num_of_dismatching_blockings:      445
% 3.03/1.02  inst_num_of_non_proper_insts:           726
% 3.03/1.02  inst_num_of_duplicates:                 0
% 3.03/1.02  inst_inst_num_from_inst_to_res:         0
% 3.03/1.02  inst_dismatching_checking_time:         0.
% 3.03/1.02  
% 3.03/1.02  ------ Resolution
% 3.03/1.02  
% 3.03/1.02  res_num_of_clauses:                     0
% 3.03/1.02  res_num_in_passive:                     0
% 3.03/1.02  res_num_in_active:                      0
% 3.03/1.02  res_num_of_loops:                       130
% 3.03/1.02  res_forward_subset_subsumed:            122
% 3.03/1.02  res_backward_subset_subsumed:           4
% 3.03/1.02  res_forward_subsumed:                   0
% 3.03/1.02  res_backward_subsumed:                  0
% 3.03/1.02  res_forward_subsumption_resolution:     1
% 3.03/1.02  res_backward_subsumption_resolution:    0
% 3.03/1.02  res_clause_to_clause_subsumption:       148
% 3.03/1.02  res_orphan_elimination:                 0
% 3.03/1.02  res_tautology_del:                      116
% 3.03/1.02  res_num_eq_res_simplified:              0
% 3.03/1.02  res_num_sel_changes:                    0
% 3.03/1.02  res_moves_from_active_to_pass:          0
% 3.03/1.02  
% 3.03/1.02  ------ Superposition
% 3.03/1.02  
% 3.03/1.02  sup_time_total:                         0.
% 3.03/1.02  sup_time_generating:                    0.
% 3.03/1.02  sup_time_sim_full:                      0.
% 3.03/1.02  sup_time_sim_immed:                     0.
% 3.03/1.02  
% 3.03/1.02  sup_num_of_clauses:                     73
% 3.03/1.02  sup_num_in_active:                      49
% 3.03/1.02  sup_num_in_passive:                     24
% 3.03/1.02  sup_num_of_loops:                       65
% 3.03/1.02  sup_fw_superposition:                   30
% 3.03/1.02  sup_bw_superposition:                   29
% 3.03/1.02  sup_immediate_simplified:               8
% 3.03/1.02  sup_given_eliminated:                   0
% 3.03/1.02  comparisons_done:                       0
% 3.03/1.02  comparisons_avoided:                    0
% 3.03/1.02  
% 3.03/1.02  ------ Simplifications
% 3.03/1.02  
% 3.03/1.02  
% 3.03/1.02  sim_fw_subset_subsumed:                 0
% 3.03/1.02  sim_bw_subset_subsumed:                 6
% 3.03/1.02  sim_fw_subsumed:                        1
% 3.03/1.02  sim_bw_subsumed:                        0
% 3.03/1.02  sim_fw_subsumption_res:                 2
% 3.03/1.02  sim_bw_subsumption_res:                 0
% 3.03/1.02  sim_tautology_del:                      0
% 3.03/1.02  sim_eq_tautology_del:                   0
% 3.03/1.02  sim_eq_res_simp:                        0
% 3.03/1.02  sim_fw_demodulated:                     1
% 3.03/1.02  sim_bw_demodulated:                     12
% 3.03/1.02  sim_light_normalised:                   12
% 3.03/1.02  sim_joinable_taut:                      0
% 3.03/1.02  sim_joinable_simp:                      0
% 3.03/1.02  sim_ac_normalised:                      0
% 3.03/1.02  sim_smt_subsumption:                    0
% 3.03/1.02  
%------------------------------------------------------------------------------
