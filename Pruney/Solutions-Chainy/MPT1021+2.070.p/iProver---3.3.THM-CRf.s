%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n011.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:07:32 EST 2020

% Result     : Theorem 2.52s
% Output     : CNFRefutation 2.52s
% Verified   : 
% Statistics : Number of formulae       :  177 (1175 expanded)
%              Number of clauses        :  111 ( 381 expanded)
%              Number of leaves         :   16 ( 224 expanded)
%              Depth                    :   21
%              Number of atoms          :  591 (5479 expanded)
%              Number of equality atoms :  221 ( 567 expanded)
%              Maximal formula depth    :   12 (   5 average)
%              Maximal clause size      :   12 (   3 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f16,conjecture,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
        & v3_funct_2(X1,X0,X0)
        & v1_funct_2(X1,X0,X0)
        & v1_funct_1(X1) )
     => ( r2_relset_1(X0,X0,k1_partfun1(X0,X0,X0,X0,k2_funct_2(X0,X1),X1),k6_partfun1(X0))
        & r2_relset_1(X0,X0,k1_partfun1(X0,X0,X0,X0,X1,k2_funct_2(X0,X1)),k6_partfun1(X0)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f17,negated_conjecture,(
    ~ ! [X0,X1] :
        ( ( m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
          & v3_funct_2(X1,X0,X0)
          & v1_funct_2(X1,X0,X0)
          & v1_funct_1(X1) )
       => ( r2_relset_1(X0,X0,k1_partfun1(X0,X0,X0,X0,k2_funct_2(X0,X1),X1),k6_partfun1(X0))
          & r2_relset_1(X0,X0,k1_partfun1(X0,X0,X0,X0,X1,k2_funct_2(X0,X1)),k6_partfun1(X0)) ) ) ),
    inference(negated_conjecture,[],[f16])).

fof(f40,plain,(
    ? [X0,X1] :
      ( ( ~ r2_relset_1(X0,X0,k1_partfun1(X0,X0,X0,X0,k2_funct_2(X0,X1),X1),k6_partfun1(X0))
        | ~ r2_relset_1(X0,X0,k1_partfun1(X0,X0,X0,X0,X1,k2_funct_2(X0,X1)),k6_partfun1(X0)) )
      & m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
      & v3_funct_2(X1,X0,X0)
      & v1_funct_2(X1,X0,X0)
      & v1_funct_1(X1) ) ),
    inference(ennf_transformation,[],[f17])).

fof(f41,plain,(
    ? [X0,X1] :
      ( ( ~ r2_relset_1(X0,X0,k1_partfun1(X0,X0,X0,X0,k2_funct_2(X0,X1),X1),k6_partfun1(X0))
        | ~ r2_relset_1(X0,X0,k1_partfun1(X0,X0,X0,X0,X1,k2_funct_2(X0,X1)),k6_partfun1(X0)) )
      & m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
      & v3_funct_2(X1,X0,X0)
      & v1_funct_2(X1,X0,X0)
      & v1_funct_1(X1) ) ),
    inference(flattening,[],[f40])).

fof(f45,plain,
    ( ? [X0,X1] :
        ( ( ~ r2_relset_1(X0,X0,k1_partfun1(X0,X0,X0,X0,k2_funct_2(X0,X1),X1),k6_partfun1(X0))
          | ~ r2_relset_1(X0,X0,k1_partfun1(X0,X0,X0,X0,X1,k2_funct_2(X0,X1)),k6_partfun1(X0)) )
        & m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
        & v3_funct_2(X1,X0,X0)
        & v1_funct_2(X1,X0,X0)
        & v1_funct_1(X1) )
   => ( ( ~ r2_relset_1(sK1,sK1,k1_partfun1(sK1,sK1,sK1,sK1,k2_funct_2(sK1,sK2),sK2),k6_partfun1(sK1))
        | ~ r2_relset_1(sK1,sK1,k1_partfun1(sK1,sK1,sK1,sK1,sK2,k2_funct_2(sK1,sK2)),k6_partfun1(sK1)) )
      & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK1,sK1)))
      & v3_funct_2(sK2,sK1,sK1)
      & v1_funct_2(sK2,sK1,sK1)
      & v1_funct_1(sK2) ) ),
    introduced(choice_axiom,[])).

fof(f46,plain,
    ( ( ~ r2_relset_1(sK1,sK1,k1_partfun1(sK1,sK1,sK1,sK1,k2_funct_2(sK1,sK2),sK2),k6_partfun1(sK1))
      | ~ r2_relset_1(sK1,sK1,k1_partfun1(sK1,sK1,sK1,sK1,sK2,k2_funct_2(sK1,sK2)),k6_partfun1(sK1)) )
    & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK1,sK1)))
    & v3_funct_2(sK2,sK1,sK1)
    & v1_funct_2(sK2,sK1,sK1)
    & v1_funct_1(sK2) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1,sK2])],[f41,f45])).

fof(f75,plain,(
    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK1,sK1))) ),
    inference(cnf_transformation,[],[f46])).

fof(f13,axiom,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
        & v3_funct_2(X1,X0,X0)
        & v1_funct_2(X1,X0,X0)
        & v1_funct_1(X1) )
     => k2_funct_1(X1) = k2_funct_2(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f36,plain,(
    ! [X0,X1] :
      ( k2_funct_1(X1) = k2_funct_2(X0,X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
      | ~ v3_funct_2(X1,X0,X0)
      | ~ v1_funct_2(X1,X0,X0)
      | ~ v1_funct_1(X1) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f37,plain,(
    ! [X0,X1] :
      ( k2_funct_1(X1) = k2_funct_2(X0,X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
      | ~ v3_funct_2(X1,X0,X0)
      | ~ v1_funct_2(X1,X0,X0)
      | ~ v1_funct_1(X1) ) ),
    inference(flattening,[],[f36])).

fof(f69,plain,(
    ! [X0,X1] :
      ( k2_funct_1(X1) = k2_funct_2(X0,X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
      | ~ v3_funct_2(X1,X0,X0)
      | ~ v1_funct_2(X1,X0,X0)
      | ~ v1_funct_1(X1) ) ),
    inference(cnf_transformation,[],[f37])).

fof(f72,plain,(
    v1_funct_1(sK2) ),
    inference(cnf_transformation,[],[f46])).

fof(f73,plain,(
    v1_funct_2(sK2,sK1,sK1) ),
    inference(cnf_transformation,[],[f46])).

fof(f74,plain,(
    v3_funct_2(sK2,sK1,sK1) ),
    inference(cnf_transformation,[],[f46])).

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

fof(f32,plain,(
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

fof(f33,plain,(
    ! [X0,X1] :
      ( ( m1_subset_1(k2_funct_2(X0,X1),k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
        & v3_funct_2(k2_funct_2(X0,X1),X0,X0)
        & v1_funct_2(k2_funct_2(X0,X1),X0,X0)
        & v1_funct_1(k2_funct_2(X0,X1)) )
      | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
      | ~ v3_funct_2(X1,X0,X0)
      | ~ v1_funct_2(X1,X0,X0)
      | ~ v1_funct_1(X1) ) ),
    inference(flattening,[],[f32])).

fof(f62,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k2_funct_2(X0,X1),k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
      | ~ v3_funct_2(X1,X0,X0)
      | ~ v1_funct_2(X1,X0,X0)
      | ~ v1_funct_1(X1) ) ),
    inference(cnf_transformation,[],[f33])).

fof(f12,axiom,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( ( m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
        & v1_funct_1(X5)
        & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_1(X4) )
     => k5_relat_1(X4,X5) = k1_partfun1(X0,X1,X2,X3,X4,X5) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f34,plain,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( k5_relat_1(X4,X5) = k1_partfun1(X0,X1,X2,X3,X4,X5)
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ v1_funct_1(X5)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X4) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f35,plain,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( k5_relat_1(X4,X5) = k1_partfun1(X0,X1,X2,X3,X4,X5)
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ v1_funct_1(X5)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X4) ) ),
    inference(flattening,[],[f34])).

fof(f68,plain,(
    ! [X4,X2,X0,X5,X3,X1] :
      ( k5_relat_1(X4,X5) = k1_partfun1(X0,X1,X2,X3,X4,X5)
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ v1_funct_1(X5)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X4) ) ),
    inference(cnf_transformation,[],[f35])).

fof(f59,plain,(
    ! [X0,X1] :
      ( v1_funct_1(k2_funct_2(X0,X1))
      | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
      | ~ v3_funct_2(X1,X0,X0)
      | ~ v1_funct_2(X1,X0,X0)
      | ~ v1_funct_1(X1) ) ),
    inference(cnf_transformation,[],[f33])).

fof(f7,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => ( ( v3_funct_2(X2,X0,X1)
          & v1_funct_1(X2) )
       => ( v2_funct_2(X2,X1)
          & v2_funct_1(X2)
          & v1_funct_1(X2) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f28,plain,(
    ! [X0,X1,X2] :
      ( ( v2_funct_2(X2,X1)
        & v2_funct_1(X2)
        & v1_funct_1(X2) )
      | ~ v3_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f29,plain,(
    ! [X0,X1,X2] :
      ( ( v2_funct_2(X2,X1)
        & v2_funct_1(X2)
        & v1_funct_1(X2) )
      | ~ v3_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(flattening,[],[f28])).

fof(f56,plain,(
    ! [X2,X0,X1] :
      ( v2_funct_2(X2,X1)
      | ~ v3_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f8,axiom,(
    ! [X0,X1] :
      ( ( v5_relat_1(X1,X0)
        & v1_relat_1(X1) )
     => ( v2_funct_2(X1,X0)
      <=> k2_relat_1(X1) = X0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f30,plain,(
    ! [X0,X1] :
      ( ( v2_funct_2(X1,X0)
      <=> k2_relat_1(X1) = X0 )
      | ~ v5_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f31,plain,(
    ! [X0,X1] :
      ( ( v2_funct_2(X1,X0)
      <=> k2_relat_1(X1) = X0 )
      | ~ v5_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f30])).

fof(f42,plain,(
    ! [X0,X1] :
      ( ( ( v2_funct_2(X1,X0)
          | k2_relat_1(X1) != X0 )
        & ( k2_relat_1(X1) = X0
          | ~ v2_funct_2(X1,X0) ) )
      | ~ v5_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(nnf_transformation,[],[f31])).

fof(f57,plain,(
    ! [X0,X1] :
      ( k2_relat_1(X1) = X0
      | ~ v2_funct_2(X1,X0)
      | ~ v5_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f42])).

fof(f4,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => ( v5_relat_1(X2,X1)
        & v4_relat_1(X2,X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f19,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => v5_relat_1(X2,X1) ) ),
    inference(pure_predicate_removal,[],[f4])).

fof(f24,plain,(
    ! [X0,X1,X2] :
      ( v5_relat_1(X2,X1)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f19])).

fof(f51,plain,(
    ! [X2,X0,X1] :
      ( v5_relat_1(X2,X1)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f2,axiom,(
    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f48,plain,(
    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1)) ),
    inference(cnf_transformation,[],[f2])).

fof(f1,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(X0))
         => v1_relat_1(X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f21,plain,(
    ! [X0] :
      ( ! [X1] :
          ( v1_relat_1(X1)
          | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f47,plain,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f3,axiom,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ( v2_funct_1(X0)
       => ( k5_relat_1(k2_funct_1(X0),X0) = k6_relat_1(k2_relat_1(X0))
          & k5_relat_1(X0,k2_funct_1(X0)) = k6_relat_1(k1_relat_1(X0)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f22,plain,(
    ! [X0] :
      ( ( k5_relat_1(k2_funct_1(X0),X0) = k6_relat_1(k2_relat_1(X0))
        & k5_relat_1(X0,k2_funct_1(X0)) = k6_relat_1(k1_relat_1(X0)) )
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f23,plain,(
    ! [X0] :
      ( ( k5_relat_1(k2_funct_1(X0),X0) = k6_relat_1(k2_relat_1(X0))
        & k5_relat_1(X0,k2_funct_1(X0)) = k6_relat_1(k1_relat_1(X0)) )
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f22])).

fof(f50,plain,(
    ! [X0] :
      ( k5_relat_1(k2_funct_1(X0),X0) = k6_relat_1(k2_relat_1(X0))
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f14,axiom,(
    ! [X0] : k6_relat_1(X0) = k6_partfun1(X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f70,plain,(
    ! [X0] : k6_relat_1(X0) = k6_partfun1(X0) ),
    inference(cnf_transformation,[],[f14])).

fof(f77,plain,(
    ! [X0] :
      ( k5_relat_1(k2_funct_1(X0),X0) = k6_partfun1(k2_relat_1(X0))
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(definition_unfolding,[],[f50,f70])).

fof(f55,plain,(
    ! [X2,X0,X1] :
      ( v2_funct_1(X2)
      | ~ v3_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f15,axiom,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
        & v1_funct_2(X1,X0,X0)
        & v1_funct_1(X1) )
     => k1_relset_1(X0,X0,X1) = X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f38,plain,(
    ! [X0,X1] :
      ( k1_relset_1(X0,X0,X1) = X0
      | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
      | ~ v1_funct_2(X1,X0,X0)
      | ~ v1_funct_1(X1) ) ),
    inference(ennf_transformation,[],[f15])).

fof(f39,plain,(
    ! [X0,X1] :
      ( k1_relset_1(X0,X0,X1) = X0
      | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
      | ~ v1_funct_2(X1,X0,X0)
      | ~ v1_funct_1(X1) ) ),
    inference(flattening,[],[f38])).

fof(f71,plain,(
    ! [X0,X1] :
      ( k1_relset_1(X0,X0,X1) = X0
      | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
      | ~ v1_funct_2(X1,X0,X0)
      | ~ v1_funct_1(X1) ) ),
    inference(cnf_transformation,[],[f39])).

fof(f5,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k1_relat_1(X2) = k1_relset_1(X0,X1,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f25,plain,(
    ! [X0,X1,X2] :
      ( k1_relat_1(X2) = k1_relset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f52,plain,(
    ! [X2,X0,X1] :
      ( k1_relat_1(X2) = k1_relset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f49,plain,(
    ! [X0] :
      ( k5_relat_1(X0,k2_funct_1(X0)) = k6_relat_1(k1_relat_1(X0))
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f78,plain,(
    ! [X0] :
      ( k5_relat_1(X0,k2_funct_1(X0)) = k6_partfun1(k1_relat_1(X0))
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(definition_unfolding,[],[f49,f70])).

fof(f76,plain,
    ( ~ r2_relset_1(sK1,sK1,k1_partfun1(sK1,sK1,sK1,sK1,k2_funct_2(sK1,sK2),sK2),k6_partfun1(sK1))
    | ~ r2_relset_1(sK1,sK1,k1_partfun1(sK1,sK1,sK1,sK1,sK2,k2_funct_2(sK1,sK2)),k6_partfun1(sK1)) ),
    inference(cnf_transformation,[],[f46])).

fof(f10,axiom,(
    ! [X0] :
      ( m1_subset_1(k6_partfun1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
      & v1_partfun1(k6_partfun1(X0),X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f18,plain,(
    ! [X0] : m1_subset_1(k6_partfun1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0))) ),
    inference(pure_predicate_removal,[],[f10])).

fof(f63,plain,(
    ! [X0] : m1_subset_1(k6_partfun1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0))) ),
    inference(cnf_transformation,[],[f18])).

fof(f6,axiom,(
    ! [X0,X1,X2,X3] :
      ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) )
     => r2_relset_1(X0,X1,X2,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f26,plain,(
    ! [X0,X1,X2,X3] :
      ( r2_relset_1(X0,X1,X2,X2)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f27,plain,(
    ! [X0,X1,X2,X3] :
      ( r2_relset_1(X0,X1,X2,X2)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(flattening,[],[f26])).

fof(f53,plain,(
    ! [X2,X0,X3,X1] :
      ( r2_relset_1(X0,X1,X2,X2)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f27])).

cnf(c_25,negated_conjecture,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK1,sK1))) ),
    inference(cnf_transformation,[],[f75])).

cnf(c_615,negated_conjecture,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK1,sK1))) ),
    inference(subtyping,[status(esa)],[c_25])).

cnf(c_1132,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK1,sK1))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_615])).

cnf(c_22,plain,
    ( ~ v1_funct_2(X0,X1,X1)
    | ~ v3_funct_2(X0,X1,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X1)))
    | ~ v1_funct_1(X0)
    | k2_funct_2(X1,X0) = k2_funct_1(X0) ),
    inference(cnf_transformation,[],[f69])).

cnf(c_618,plain,
    ( ~ v1_funct_2(X0_50,X0_51,X0_51)
    | ~ v3_funct_2(X0_50,X0_51,X0_51)
    | ~ m1_subset_1(X0_50,k1_zfmisc_1(k2_zfmisc_1(X0_51,X0_51)))
    | ~ v1_funct_1(X0_50)
    | k2_funct_2(X0_51,X0_50) = k2_funct_1(X0_50) ),
    inference(subtyping,[status(esa)],[c_22])).

cnf(c_1129,plain,
    ( k2_funct_2(X0_51,X0_50) = k2_funct_1(X0_50)
    | v1_funct_2(X0_50,X0_51,X0_51) != iProver_top
    | v3_funct_2(X0_50,X0_51,X0_51) != iProver_top
    | m1_subset_1(X0_50,k1_zfmisc_1(k2_zfmisc_1(X0_51,X0_51))) != iProver_top
    | v1_funct_1(X0_50) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_618])).

cnf(c_2092,plain,
    ( k2_funct_2(sK1,sK2) = k2_funct_1(sK2)
    | v1_funct_2(sK2,sK1,sK1) != iProver_top
    | v3_funct_2(sK2,sK1,sK1) != iProver_top
    | v1_funct_1(sK2) != iProver_top ),
    inference(superposition,[status(thm)],[c_1132,c_1129])).

cnf(c_28,negated_conjecture,
    ( v1_funct_1(sK2) ),
    inference(cnf_transformation,[],[f72])).

cnf(c_27,negated_conjecture,
    ( v1_funct_2(sK2,sK1,sK1) ),
    inference(cnf_transformation,[],[f73])).

cnf(c_26,negated_conjecture,
    ( v3_funct_2(sK2,sK1,sK1) ),
    inference(cnf_transformation,[],[f74])).

cnf(c_706,plain,
    ( ~ v1_funct_2(sK2,sK1,sK1)
    | ~ v3_funct_2(sK2,sK1,sK1)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK1,sK1)))
    | ~ v1_funct_1(sK2)
    | k2_funct_2(sK1,sK2) = k2_funct_1(sK2) ),
    inference(instantiation,[status(thm)],[c_618])).

cnf(c_2316,plain,
    ( k2_funct_2(sK1,sK2) = k2_funct_1(sK2) ),
    inference(global_propositional_subsumption,[status(thm)],[c_2092,c_28,c_27,c_26,c_25,c_706])).

cnf(c_12,plain,
    ( ~ v1_funct_2(X0,X1,X1)
    | ~ v3_funct_2(X0,X1,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X1)))
    | m1_subset_1(k2_funct_2(X1,X0),k1_zfmisc_1(k2_zfmisc_1(X1,X1)))
    | ~ v1_funct_1(X0) ),
    inference(cnf_transformation,[],[f62])).

cnf(c_627,plain,
    ( ~ v1_funct_2(X0_50,X0_51,X0_51)
    | ~ v3_funct_2(X0_50,X0_51,X0_51)
    | ~ m1_subset_1(X0_50,k1_zfmisc_1(k2_zfmisc_1(X0_51,X0_51)))
    | m1_subset_1(k2_funct_2(X0_51,X0_50),k1_zfmisc_1(k2_zfmisc_1(X0_51,X0_51)))
    | ~ v1_funct_1(X0_50) ),
    inference(subtyping,[status(esa)],[c_12])).

cnf(c_1120,plain,
    ( v1_funct_2(X0_50,X0_51,X0_51) != iProver_top
    | v3_funct_2(X0_50,X0_51,X0_51) != iProver_top
    | m1_subset_1(X0_50,k1_zfmisc_1(k2_zfmisc_1(X0_51,X0_51))) != iProver_top
    | m1_subset_1(k2_funct_2(X0_51,X0_50),k1_zfmisc_1(k2_zfmisc_1(X0_51,X0_51))) = iProver_top
    | v1_funct_1(X0_50) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_627])).

cnf(c_2650,plain,
    ( v1_funct_2(sK2,sK1,sK1) != iProver_top
    | v3_funct_2(sK2,sK1,sK1) != iProver_top
    | m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK1))) = iProver_top
    | m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK1,sK1))) != iProver_top
    | v1_funct_1(sK2) != iProver_top ),
    inference(superposition,[status(thm)],[c_2316,c_1120])).

cnf(c_29,plain,
    ( v1_funct_1(sK2) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_28])).

cnf(c_30,plain,
    ( v1_funct_2(sK2,sK1,sK1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_27])).

cnf(c_31,plain,
    ( v3_funct_2(sK2,sK1,sK1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_26])).

cnf(c_32,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK1,sK1))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_25])).

cnf(c_4018,plain,
    ( m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK1))) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_2650,c_29,c_30,c_31,c_32])).

cnf(c_21,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X4,X5)))
    | ~ v1_funct_1(X0)
    | ~ v1_funct_1(X3)
    | k1_partfun1(X4,X5,X1,X2,X3,X0) = k5_relat_1(X3,X0) ),
    inference(cnf_transformation,[],[f68])).

cnf(c_619,plain,
    ( ~ m1_subset_1(X0_50,k1_zfmisc_1(k2_zfmisc_1(X0_51,X1_51)))
    | ~ m1_subset_1(X1_50,k1_zfmisc_1(k2_zfmisc_1(X2_51,X3_51)))
    | ~ v1_funct_1(X0_50)
    | ~ v1_funct_1(X1_50)
    | k1_partfun1(X2_51,X3_51,X0_51,X1_51,X1_50,X0_50) = k5_relat_1(X1_50,X0_50) ),
    inference(subtyping,[status(esa)],[c_21])).

cnf(c_1128,plain,
    ( k1_partfun1(X0_51,X1_51,X2_51,X3_51,X0_50,X1_50) = k5_relat_1(X0_50,X1_50)
    | m1_subset_1(X1_50,k1_zfmisc_1(k2_zfmisc_1(X2_51,X3_51))) != iProver_top
    | m1_subset_1(X0_50,k1_zfmisc_1(k2_zfmisc_1(X0_51,X1_51))) != iProver_top
    | v1_funct_1(X0_50) != iProver_top
    | v1_funct_1(X1_50) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_619])).

cnf(c_4024,plain,
    ( k1_partfun1(sK1,sK1,X0_51,X1_51,k2_funct_1(sK2),X0_50) = k5_relat_1(k2_funct_1(sK2),X0_50)
    | m1_subset_1(X0_50,k1_zfmisc_1(k2_zfmisc_1(X0_51,X1_51))) != iProver_top
    | v1_funct_1(X0_50) != iProver_top
    | v1_funct_1(k2_funct_1(sK2)) != iProver_top ),
    inference(superposition,[status(thm)],[c_4018,c_1128])).

cnf(c_15,plain,
    ( ~ v1_funct_2(X0,X1,X1)
    | ~ v3_funct_2(X0,X1,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X1)))
    | ~ v1_funct_1(X0)
    | v1_funct_1(k2_funct_2(X1,X0)) ),
    inference(cnf_transformation,[],[f59])).

cnf(c_624,plain,
    ( ~ v1_funct_2(X0_50,X0_51,X0_51)
    | ~ v3_funct_2(X0_50,X0_51,X0_51)
    | ~ m1_subset_1(X0_50,k1_zfmisc_1(k2_zfmisc_1(X0_51,X0_51)))
    | ~ v1_funct_1(X0_50)
    | v1_funct_1(k2_funct_2(X0_51,X0_50)) ),
    inference(subtyping,[status(esa)],[c_15])).

cnf(c_1123,plain,
    ( v1_funct_2(X0_50,X0_51,X0_51) != iProver_top
    | v3_funct_2(X0_50,X0_51,X0_51) != iProver_top
    | m1_subset_1(X0_50,k1_zfmisc_1(k2_zfmisc_1(X0_51,X0_51))) != iProver_top
    | v1_funct_1(X0_50) != iProver_top
    | v1_funct_1(k2_funct_2(X0_51,X0_50)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_624])).

cnf(c_2052,plain,
    ( v1_funct_2(sK2,sK1,sK1) != iProver_top
    | v3_funct_2(sK2,sK1,sK1) != iProver_top
    | v1_funct_1(k2_funct_2(sK1,sK2)) = iProver_top
    | v1_funct_1(sK2) != iProver_top ),
    inference(superposition,[status(thm)],[c_1132,c_1123])).

cnf(c_695,plain,
    ( v1_funct_2(X0_50,X0_51,X0_51) != iProver_top
    | v3_funct_2(X0_50,X0_51,X0_51) != iProver_top
    | m1_subset_1(X0_50,k1_zfmisc_1(k2_zfmisc_1(X0_51,X0_51))) != iProver_top
    | v1_funct_1(X0_50) != iProver_top
    | v1_funct_1(k2_funct_2(X0_51,X0_50)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_624])).

cnf(c_697,plain,
    ( v1_funct_2(sK2,sK1,sK1) != iProver_top
    | v3_funct_2(sK2,sK1,sK1) != iProver_top
    | m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK1,sK1))) != iProver_top
    | v1_funct_1(k2_funct_2(sK1,sK2)) = iProver_top
    | v1_funct_1(sK2) != iProver_top ),
    inference(instantiation,[status(thm)],[c_695])).

cnf(c_2294,plain,
    ( v1_funct_1(k2_funct_2(sK1,sK2)) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_2052,c_29,c_30,c_31,c_32,c_697])).

cnf(c_2319,plain,
    ( v1_funct_1(k2_funct_1(sK2)) = iProver_top ),
    inference(demodulation,[status(thm)],[c_2316,c_2294])).

cnf(c_5575,plain,
    ( v1_funct_1(X0_50) != iProver_top
    | m1_subset_1(X0_50,k1_zfmisc_1(k2_zfmisc_1(X0_51,X1_51))) != iProver_top
    | k1_partfun1(sK1,sK1,X0_51,X1_51,k2_funct_1(sK2),X0_50) = k5_relat_1(k2_funct_1(sK2),X0_50) ),
    inference(global_propositional_subsumption,[status(thm)],[c_4024,c_2319])).

cnf(c_5576,plain,
    ( k1_partfun1(sK1,sK1,X0_51,X1_51,k2_funct_1(sK2),X0_50) = k5_relat_1(k2_funct_1(sK2),X0_50)
    | m1_subset_1(X0_50,k1_zfmisc_1(k2_zfmisc_1(X0_51,X1_51))) != iProver_top
    | v1_funct_1(X0_50) != iProver_top ),
    inference(renaming,[status(thm)],[c_5575])).

cnf(c_5584,plain,
    ( k1_partfun1(sK1,sK1,sK1,sK1,k2_funct_1(sK2),sK2) = k5_relat_1(k2_funct_1(sK2),sK2)
    | v1_funct_1(sK2) != iProver_top ),
    inference(superposition,[status(thm)],[c_1132,c_5576])).

cnf(c_7,plain,
    ( ~ v3_funct_2(X0,X1,X2)
    | v2_funct_2(X0,X2)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ v1_funct_1(X0) ),
    inference(cnf_transformation,[],[f56])).

cnf(c_11,plain,
    ( ~ v2_funct_2(X0,X1)
    | ~ v5_relat_1(X0,X1)
    | ~ v1_relat_1(X0)
    | k2_relat_1(X0) = X1 ),
    inference(cnf_transformation,[],[f57])).

cnf(c_320,plain,
    ( ~ v3_funct_2(X0,X1,X2)
    | ~ v5_relat_1(X3,X4)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ v1_funct_1(X0)
    | ~ v1_relat_1(X3)
    | X3 != X0
    | X4 != X2
    | k2_relat_1(X3) = X4 ),
    inference(resolution_lifted,[status(thm)],[c_7,c_11])).

cnf(c_321,plain,
    ( ~ v3_funct_2(X0,X1,X2)
    | ~ v5_relat_1(X0,X2)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ v1_funct_1(X0)
    | ~ v1_relat_1(X0)
    | k2_relat_1(X0) = X2 ),
    inference(unflattening,[status(thm)],[c_320])).

cnf(c_4,plain,
    ( v5_relat_1(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) ),
    inference(cnf_transformation,[],[f51])).

cnf(c_337,plain,
    ( ~ v3_funct_2(X0,X1,X2)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ v1_funct_1(X0)
    | ~ v1_relat_1(X0)
    | k2_relat_1(X0) = X2 ),
    inference(forward_subsumption_resolution,[status(thm)],[c_321,c_4])).

cnf(c_611,plain,
    ( ~ v3_funct_2(X0_50,X0_51,X1_51)
    | ~ m1_subset_1(X0_50,k1_zfmisc_1(k2_zfmisc_1(X0_51,X1_51)))
    | ~ v1_funct_1(X0_50)
    | ~ v1_relat_1(X0_50)
    | k2_relat_1(X0_50) = X1_51 ),
    inference(subtyping,[status(esa)],[c_337])).

cnf(c_1136,plain,
    ( k2_relat_1(X0_50) = X0_51
    | v3_funct_2(X0_50,X1_51,X0_51) != iProver_top
    | m1_subset_1(X0_50,k1_zfmisc_1(k2_zfmisc_1(X1_51,X0_51))) != iProver_top
    | v1_funct_1(X0_50) != iProver_top
    | v1_relat_1(X0_50) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_611])).

cnf(c_3508,plain,
    ( k2_relat_1(sK2) = sK1
    | v3_funct_2(sK2,sK1,sK1) != iProver_top
    | v1_funct_1(sK2) != iProver_top
    | v1_relat_1(sK2) != iProver_top ),
    inference(superposition,[status(thm)],[c_1132,c_1136])).

cnf(c_1,plain,
    ( v1_relat_1(k2_zfmisc_1(X0,X1)) ),
    inference(cnf_transformation,[],[f48])).

cnf(c_99,plain,
    ( v1_relat_1(k2_zfmisc_1(sK1,sK1)) ),
    inference(instantiation,[status(thm)],[c_1])).

cnf(c_717,plain,
    ( ~ v3_funct_2(sK2,sK1,sK1)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK1,sK1)))
    | ~ v1_funct_1(sK2)
    | ~ v1_relat_1(sK2)
    | k2_relat_1(sK2) = sK1 ),
    inference(instantiation,[status(thm)],[c_611])).

cnf(c_0,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | ~ v1_relat_1(X1)
    | v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f47])).

cnf(c_634,plain,
    ( ~ m1_subset_1(X0_50,k1_zfmisc_1(X1_50))
    | ~ v1_relat_1(X1_50)
    | v1_relat_1(X0_50) ),
    inference(subtyping,[status(esa)],[c_0])).

cnf(c_1331,plain,
    ( ~ m1_subset_1(X0_50,k1_zfmisc_1(k2_zfmisc_1(X0_51,X1_51)))
    | v1_relat_1(X0_50)
    | ~ v1_relat_1(k2_zfmisc_1(X0_51,X1_51)) ),
    inference(instantiation,[status(thm)],[c_634])).

cnf(c_1333,plain,
    ( ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK1,sK1)))
    | ~ v1_relat_1(k2_zfmisc_1(sK1,sK1))
    | v1_relat_1(sK2) ),
    inference(instantiation,[status(thm)],[c_1331])).

cnf(c_3900,plain,
    ( k2_relat_1(sK2) = sK1 ),
    inference(global_propositional_subsumption,[status(thm)],[c_3508,c_28,c_26,c_25,c_99,c_717,c_1333])).

cnf(c_612,negated_conjecture,
    ( v1_funct_1(sK2) ),
    inference(subtyping,[status(esa)],[c_28])).

cnf(c_1135,plain,
    ( v1_funct_1(sK2) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_612])).

cnf(c_2,plain,
    ( ~ v1_funct_1(X0)
    | ~ v2_funct_1(X0)
    | ~ v1_relat_1(X0)
    | k5_relat_1(k2_funct_1(X0),X0) = k6_partfun1(k2_relat_1(X0)) ),
    inference(cnf_transformation,[],[f77])).

cnf(c_632,plain,
    ( ~ v1_funct_1(X0_50)
    | ~ v2_funct_1(X0_50)
    | ~ v1_relat_1(X0_50)
    | k5_relat_1(k2_funct_1(X0_50),X0_50) = k6_partfun1(k2_relat_1(X0_50)) ),
    inference(subtyping,[status(esa)],[c_2])).

cnf(c_1115,plain,
    ( k5_relat_1(k2_funct_1(X0_50),X0_50) = k6_partfun1(k2_relat_1(X0_50))
    | v1_funct_1(X0_50) != iProver_top
    | v2_funct_1(X0_50) != iProver_top
    | v1_relat_1(X0_50) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_632])).

cnf(c_1556,plain,
    ( k5_relat_1(k2_funct_1(sK2),sK2) = k6_partfun1(k2_relat_1(sK2))
    | v2_funct_1(sK2) != iProver_top
    | v1_relat_1(sK2) != iProver_top ),
    inference(superposition,[status(thm)],[c_1135,c_1115])).

cnf(c_672,plain,
    ( ~ v1_funct_1(sK2)
    | ~ v2_funct_1(sK2)
    | ~ v1_relat_1(sK2)
    | k5_relat_1(k2_funct_1(sK2),sK2) = k6_partfun1(k2_relat_1(sK2)) ),
    inference(instantiation,[status(thm)],[c_632])).

cnf(c_8,plain,
    ( ~ v3_funct_2(X0,X1,X2)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ v1_funct_1(X0)
    | v2_funct_1(X0) ),
    inference(cnf_transformation,[],[f55])).

cnf(c_628,plain,
    ( ~ v3_funct_2(X0_50,X0_51,X1_51)
    | ~ m1_subset_1(X0_50,k1_zfmisc_1(k2_zfmisc_1(X0_51,X1_51)))
    | ~ v1_funct_1(X0_50)
    | v2_funct_1(X0_50) ),
    inference(subtyping,[status(esa)],[c_8])).

cnf(c_684,plain,
    ( ~ v3_funct_2(sK2,sK1,sK1)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK1,sK1)))
    | ~ v1_funct_1(sK2)
    | v2_funct_1(sK2) ),
    inference(instantiation,[status(thm)],[c_628])).

cnf(c_1648,plain,
    ( k5_relat_1(k2_funct_1(sK2),sK2) = k6_partfun1(k2_relat_1(sK2)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_1556,c_28,c_26,c_25,c_99,c_672,c_684,c_1333])).

cnf(c_3903,plain,
    ( k5_relat_1(k2_funct_1(sK2),sK2) = k6_partfun1(sK1) ),
    inference(demodulation,[status(thm)],[c_3900,c_1648])).

cnf(c_5615,plain,
    ( k1_partfun1(sK1,sK1,sK1,sK1,k2_funct_1(sK2),sK2) = k6_partfun1(sK1)
    | v1_funct_1(sK2) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_5584,c_3903])).

cnf(c_5630,plain,
    ( k1_partfun1(sK1,sK1,sK1,sK1,k2_funct_1(sK2),sK2) = k6_partfun1(sK1) ),
    inference(global_propositional_subsumption,[status(thm)],[c_5615,c_29])).

cnf(c_2981,plain,
    ( k1_partfun1(sK1,sK1,X0_51,X1_51,sK2,X0_50) = k5_relat_1(sK2,X0_50)
    | m1_subset_1(X0_50,k1_zfmisc_1(k2_zfmisc_1(X0_51,X1_51))) != iProver_top
    | v1_funct_1(X0_50) != iProver_top
    | v1_funct_1(sK2) != iProver_top ),
    inference(superposition,[status(thm)],[c_1132,c_1128])).

cnf(c_3129,plain,
    ( v1_funct_1(X0_50) != iProver_top
    | m1_subset_1(X0_50,k1_zfmisc_1(k2_zfmisc_1(X0_51,X1_51))) != iProver_top
    | k1_partfun1(sK1,sK1,X0_51,X1_51,sK2,X0_50) = k5_relat_1(sK2,X0_50) ),
    inference(global_propositional_subsumption,[status(thm)],[c_2981,c_29])).

cnf(c_3130,plain,
    ( k1_partfun1(sK1,sK1,X0_51,X1_51,sK2,X0_50) = k5_relat_1(sK2,X0_50)
    | m1_subset_1(X0_50,k1_zfmisc_1(k2_zfmisc_1(X0_51,X1_51))) != iProver_top
    | v1_funct_1(X0_50) != iProver_top ),
    inference(renaming,[status(thm)],[c_3129])).

cnf(c_3139,plain,
    ( k1_partfun1(sK1,sK1,X0_51,X0_51,sK2,k2_funct_2(X0_51,X0_50)) = k5_relat_1(sK2,k2_funct_2(X0_51,X0_50))
    | v1_funct_2(X0_50,X0_51,X0_51) != iProver_top
    | v3_funct_2(X0_50,X0_51,X0_51) != iProver_top
    | m1_subset_1(X0_50,k1_zfmisc_1(k2_zfmisc_1(X0_51,X0_51))) != iProver_top
    | v1_funct_1(X0_50) != iProver_top
    | v1_funct_1(k2_funct_2(X0_51,X0_50)) != iProver_top ),
    inference(superposition,[status(thm)],[c_1120,c_3130])).

cnf(c_4269,plain,
    ( v1_funct_1(X0_50) != iProver_top
    | m1_subset_1(X0_50,k1_zfmisc_1(k2_zfmisc_1(X0_51,X0_51))) != iProver_top
    | v3_funct_2(X0_50,X0_51,X0_51) != iProver_top
    | v1_funct_2(X0_50,X0_51,X0_51) != iProver_top
    | k1_partfun1(sK1,sK1,X0_51,X0_51,sK2,k2_funct_2(X0_51,X0_50)) = k5_relat_1(sK2,k2_funct_2(X0_51,X0_50)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_3139,c_695])).

cnf(c_4270,plain,
    ( k1_partfun1(sK1,sK1,X0_51,X0_51,sK2,k2_funct_2(X0_51,X0_50)) = k5_relat_1(sK2,k2_funct_2(X0_51,X0_50))
    | v1_funct_2(X0_50,X0_51,X0_51) != iProver_top
    | v3_funct_2(X0_50,X0_51,X0_51) != iProver_top
    | m1_subset_1(X0_50,k1_zfmisc_1(k2_zfmisc_1(X0_51,X0_51))) != iProver_top
    | v1_funct_1(X0_50) != iProver_top ),
    inference(renaming,[status(thm)],[c_4269])).

cnf(c_4280,plain,
    ( k1_partfun1(sK1,sK1,sK1,sK1,sK2,k2_funct_2(sK1,sK2)) = k5_relat_1(sK2,k2_funct_2(sK1,sK2))
    | v1_funct_2(sK2,sK1,sK1) != iProver_top
    | v3_funct_2(sK2,sK1,sK1) != iProver_top
    | v1_funct_1(sK2) != iProver_top ),
    inference(superposition,[status(thm)],[c_1132,c_4270])).

cnf(c_23,plain,
    ( ~ v1_funct_2(X0,X1,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X1)))
    | ~ v1_funct_1(X0)
    | k1_relset_1(X1,X1,X0) = X1 ),
    inference(cnf_transformation,[],[f71])).

cnf(c_617,plain,
    ( ~ v1_funct_2(X0_50,X0_51,X0_51)
    | ~ m1_subset_1(X0_50,k1_zfmisc_1(k2_zfmisc_1(X0_51,X0_51)))
    | ~ v1_funct_1(X0_50)
    | k1_relset_1(X0_51,X0_51,X0_50) = X0_51 ),
    inference(subtyping,[status(esa)],[c_23])).

cnf(c_1130,plain,
    ( k1_relset_1(X0_51,X0_51,X0_50) = X0_51
    | v1_funct_2(X0_50,X0_51,X0_51) != iProver_top
    | m1_subset_1(X0_50,k1_zfmisc_1(k2_zfmisc_1(X0_51,X0_51))) != iProver_top
    | v1_funct_1(X0_50) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_617])).

cnf(c_1971,plain,
    ( k1_relset_1(sK1,sK1,sK2) = sK1
    | v1_funct_2(sK2,sK1,sK1) != iProver_top
    | v1_funct_1(sK2) != iProver_top ),
    inference(superposition,[status(thm)],[c_1132,c_1130])).

cnf(c_5,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k1_relset_1(X1,X2,X0) = k1_relat_1(X0) ),
    inference(cnf_transformation,[],[f52])).

cnf(c_630,plain,
    ( ~ m1_subset_1(X0_50,k1_zfmisc_1(k2_zfmisc_1(X0_51,X1_51)))
    | k1_relset_1(X0_51,X1_51,X0_50) = k1_relat_1(X0_50) ),
    inference(subtyping,[status(esa)],[c_5])).

cnf(c_1117,plain,
    ( k1_relset_1(X0_51,X1_51,X0_50) = k1_relat_1(X0_50)
    | m1_subset_1(X0_50,k1_zfmisc_1(k2_zfmisc_1(X0_51,X1_51))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_630])).

cnf(c_1517,plain,
    ( k1_relset_1(sK1,sK1,sK2) = k1_relat_1(sK2) ),
    inference(superposition,[status(thm)],[c_1132,c_1117])).

cnf(c_1991,plain,
    ( k1_relat_1(sK2) = sK1
    | v1_funct_2(sK2,sK1,sK1) != iProver_top
    | v1_funct_1(sK2) != iProver_top ),
    inference(demodulation,[status(thm)],[c_1971,c_1517])).

cnf(c_2513,plain,
    ( k1_relat_1(sK2) = sK1 ),
    inference(global_propositional_subsumption,[status(thm)],[c_1991,c_29,c_30])).

cnf(c_3,plain,
    ( ~ v1_funct_1(X0)
    | ~ v2_funct_1(X0)
    | ~ v1_relat_1(X0)
    | k5_relat_1(X0,k2_funct_1(X0)) = k6_partfun1(k1_relat_1(X0)) ),
    inference(cnf_transformation,[],[f78])).

cnf(c_631,plain,
    ( ~ v1_funct_1(X0_50)
    | ~ v2_funct_1(X0_50)
    | ~ v1_relat_1(X0_50)
    | k5_relat_1(X0_50,k2_funct_1(X0_50)) = k6_partfun1(k1_relat_1(X0_50)) ),
    inference(subtyping,[status(esa)],[c_3])).

cnf(c_1116,plain,
    ( k5_relat_1(X0_50,k2_funct_1(X0_50)) = k6_partfun1(k1_relat_1(X0_50))
    | v1_funct_1(X0_50) != iProver_top
    | v2_funct_1(X0_50) != iProver_top
    | v1_relat_1(X0_50) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_631])).

cnf(c_1774,plain,
    ( k5_relat_1(sK2,k2_funct_1(sK2)) = k6_partfun1(k1_relat_1(sK2))
    | v2_funct_1(sK2) != iProver_top
    | v1_relat_1(sK2) != iProver_top ),
    inference(superposition,[status(thm)],[c_1135,c_1116])).

cnf(c_675,plain,
    ( ~ v1_funct_1(sK2)
    | ~ v2_funct_1(sK2)
    | ~ v1_relat_1(sK2)
    | k5_relat_1(sK2,k2_funct_1(sK2)) = k6_partfun1(k1_relat_1(sK2)) ),
    inference(instantiation,[status(thm)],[c_631])).

cnf(c_1864,plain,
    ( k5_relat_1(sK2,k2_funct_1(sK2)) = k6_partfun1(k1_relat_1(sK2)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_1774,c_28,c_26,c_25,c_99,c_675,c_684,c_1333])).

cnf(c_2516,plain,
    ( k5_relat_1(sK2,k2_funct_1(sK2)) = k6_partfun1(sK1) ),
    inference(demodulation,[status(thm)],[c_2513,c_1864])).

cnf(c_4329,plain,
    ( k1_partfun1(sK1,sK1,sK1,sK1,sK2,k2_funct_1(sK2)) = k6_partfun1(sK1)
    | v1_funct_2(sK2,sK1,sK1) != iProver_top
    | v3_funct_2(sK2,sK1,sK1) != iProver_top
    | v1_funct_1(sK2) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_4280,c_2316,c_2516])).

cnf(c_4023,plain,
    ( k1_partfun1(sK1,sK1,sK1,sK1,sK2,k2_funct_1(sK2)) = k5_relat_1(sK2,k2_funct_1(sK2))
    | v1_funct_1(k2_funct_1(sK2)) != iProver_top ),
    inference(superposition,[status(thm)],[c_4018,c_3130])).

cnf(c_4114,plain,
    ( k1_partfun1(sK1,sK1,sK1,sK1,sK2,k2_funct_1(sK2)) = k6_partfun1(sK1)
    | v1_funct_1(k2_funct_1(sK2)) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_4023,c_2516])).

cnf(c_4346,plain,
    ( k1_partfun1(sK1,sK1,sK1,sK1,sK2,k2_funct_1(sK2)) = k6_partfun1(sK1) ),
    inference(global_propositional_subsumption,[status(thm)],[c_4329,c_2319,c_4114])).

cnf(c_24,negated_conjecture,
    ( ~ r2_relset_1(sK1,sK1,k1_partfun1(sK1,sK1,sK1,sK1,k2_funct_2(sK1,sK2),sK2),k6_partfun1(sK1))
    | ~ r2_relset_1(sK1,sK1,k1_partfun1(sK1,sK1,sK1,sK1,sK2,k2_funct_2(sK1,sK2)),k6_partfun1(sK1)) ),
    inference(cnf_transformation,[],[f76])).

cnf(c_616,negated_conjecture,
    ( ~ r2_relset_1(sK1,sK1,k1_partfun1(sK1,sK1,sK1,sK1,k2_funct_2(sK1,sK2),sK2),k6_partfun1(sK1))
    | ~ r2_relset_1(sK1,sK1,k1_partfun1(sK1,sK1,sK1,sK1,sK2,k2_funct_2(sK1,sK2)),k6_partfun1(sK1)) ),
    inference(subtyping,[status(esa)],[c_24])).

cnf(c_1131,plain,
    ( r2_relset_1(sK1,sK1,k1_partfun1(sK1,sK1,sK1,sK1,k2_funct_2(sK1,sK2),sK2),k6_partfun1(sK1)) != iProver_top
    | r2_relset_1(sK1,sK1,k1_partfun1(sK1,sK1,sK1,sK1,sK2,k2_funct_2(sK1,sK2)),k6_partfun1(sK1)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_616])).

cnf(c_2320,plain,
    ( r2_relset_1(sK1,sK1,k1_partfun1(sK1,sK1,sK1,sK1,k2_funct_1(sK2),sK2),k6_partfun1(sK1)) != iProver_top
    | r2_relset_1(sK1,sK1,k1_partfun1(sK1,sK1,sK1,sK1,sK2,k2_funct_1(sK2)),k6_partfun1(sK1)) != iProver_top ),
    inference(demodulation,[status(thm)],[c_2316,c_1131])).

cnf(c_4349,plain,
    ( r2_relset_1(sK1,sK1,k1_partfun1(sK1,sK1,sK1,sK1,k2_funct_1(sK2),sK2),k6_partfun1(sK1)) != iProver_top
    | r2_relset_1(sK1,sK1,k6_partfun1(sK1),k6_partfun1(sK1)) != iProver_top ),
    inference(demodulation,[status(thm)],[c_4346,c_2320])).

cnf(c_16,plain,
    ( m1_subset_1(k6_partfun1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0))) ),
    inference(cnf_transformation,[],[f63])).

cnf(c_623,plain,
    ( m1_subset_1(k6_partfun1(X0_51),k1_zfmisc_1(k2_zfmisc_1(X0_51,X0_51))) ),
    inference(subtyping,[status(esa)],[c_16])).

cnf(c_1124,plain,
    ( m1_subset_1(k6_partfun1(X0_51),k1_zfmisc_1(k2_zfmisc_1(X0_51,X0_51))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_623])).

cnf(c_6,plain,
    ( r2_relset_1(X0,X1,X2,X2)
    | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ),
    inference(cnf_transformation,[],[f53])).

cnf(c_629,plain,
    ( r2_relset_1(X0_51,X1_51,X0_50,X0_50)
    | ~ m1_subset_1(X0_50,k1_zfmisc_1(k2_zfmisc_1(X0_51,X1_51)))
    | ~ m1_subset_1(X1_50,k1_zfmisc_1(k2_zfmisc_1(X0_51,X1_51))) ),
    inference(subtyping,[status(esa)],[c_6])).

cnf(c_1118,plain,
    ( r2_relset_1(X0_51,X1_51,X0_50,X0_50) = iProver_top
    | m1_subset_1(X0_50,k1_zfmisc_1(k2_zfmisc_1(X0_51,X1_51))) != iProver_top
    | m1_subset_1(X1_50,k1_zfmisc_1(k2_zfmisc_1(X0_51,X1_51))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_629])).

cnf(c_1873,plain,
    ( r2_relset_1(X0_51,X0_51,k6_partfun1(X0_51),k6_partfun1(X0_51)) = iProver_top
    | m1_subset_1(X0_50,k1_zfmisc_1(k2_zfmisc_1(X0_51,X0_51))) != iProver_top ),
    inference(superposition,[status(thm)],[c_1124,c_1118])).

cnf(c_1891,plain,
    ( r2_relset_1(sK1,sK1,k6_partfun1(sK1),k6_partfun1(sK1)) = iProver_top
    | m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK1,sK1))) != iProver_top ),
    inference(instantiation,[status(thm)],[c_1873])).

cnf(c_4439,plain,
    ( r2_relset_1(sK1,sK1,k1_partfun1(sK1,sK1,sK1,sK1,k2_funct_1(sK2),sK2),k6_partfun1(sK1)) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_4349,c_32,c_1891])).

cnf(c_5633,plain,
    ( r2_relset_1(sK1,sK1,k6_partfun1(sK1),k6_partfun1(sK1)) != iProver_top ),
    inference(demodulation,[status(thm)],[c_5630,c_4439])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_5633,c_1891,c_32])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : iproveropt_run.sh %d %s
% 0.13/0.34  % Computer   : n011.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 12:56:42 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.35  % Running in FOF mode
% 2.52/1.01  % SZS status Started for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.52/1.01  
% 2.52/1.01  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 2.52/1.01  
% 2.52/1.01  ------  iProver source info
% 2.52/1.01  
% 2.52/1.01  git: date: 2020-06-30 10:37:57 +0100
% 2.52/1.01  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 2.52/1.01  git: non_committed_changes: false
% 2.52/1.01  git: last_make_outside_of_git: false
% 2.52/1.01  
% 2.52/1.01  ------ 
% 2.52/1.01  
% 2.52/1.01  ------ Input Options
% 2.52/1.01  
% 2.52/1.01  --out_options                           all
% 2.52/1.01  --tptp_safe_out                         true
% 2.52/1.01  --problem_path                          ""
% 2.52/1.01  --include_path                          ""
% 2.52/1.01  --clausifier                            res/vclausify_rel
% 2.52/1.01  --clausifier_options                    --mode clausify
% 2.52/1.01  --stdin                                 false
% 2.52/1.01  --stats_out                             all
% 2.52/1.01  
% 2.52/1.01  ------ General Options
% 2.52/1.01  
% 2.52/1.01  --fof                                   false
% 2.52/1.01  --time_out_real                         305.
% 2.52/1.01  --time_out_virtual                      -1.
% 2.52/1.01  --symbol_type_check                     false
% 2.52/1.01  --clausify_out                          false
% 2.52/1.01  --sig_cnt_out                           false
% 2.52/1.01  --trig_cnt_out                          false
% 2.52/1.01  --trig_cnt_out_tolerance                1.
% 2.52/1.01  --trig_cnt_out_sk_spl                   false
% 2.52/1.01  --abstr_cl_out                          false
% 2.52/1.01  
% 2.52/1.01  ------ Global Options
% 2.52/1.01  
% 2.52/1.01  --schedule                              default
% 2.52/1.01  --add_important_lit                     false
% 2.52/1.01  --prop_solver_per_cl                    1000
% 2.52/1.01  --min_unsat_core                        false
% 2.52/1.01  --soft_assumptions                      false
% 2.52/1.01  --soft_lemma_size                       3
% 2.52/1.01  --prop_impl_unit_size                   0
% 2.52/1.01  --prop_impl_unit                        []
% 2.52/1.01  --share_sel_clauses                     true
% 2.52/1.01  --reset_solvers                         false
% 2.52/1.01  --bc_imp_inh                            [conj_cone]
% 2.52/1.01  --conj_cone_tolerance                   3.
% 2.52/1.01  --extra_neg_conj                        none
% 2.52/1.01  --large_theory_mode                     true
% 2.52/1.01  --prolific_symb_bound                   200
% 2.52/1.01  --lt_threshold                          2000
% 2.52/1.01  --clause_weak_htbl                      true
% 2.52/1.01  --gc_record_bc_elim                     false
% 2.52/1.01  
% 2.52/1.01  ------ Preprocessing Options
% 2.52/1.01  
% 2.52/1.01  --preprocessing_flag                    true
% 2.52/1.01  --time_out_prep_mult                    0.1
% 2.52/1.01  --splitting_mode                        input
% 2.52/1.01  --splitting_grd                         true
% 2.52/1.01  --splitting_cvd                         false
% 2.52/1.01  --splitting_cvd_svl                     false
% 2.52/1.01  --splitting_nvd                         32
% 2.52/1.01  --sub_typing                            true
% 2.52/1.01  --prep_gs_sim                           true
% 2.52/1.01  --prep_unflatten                        true
% 2.52/1.01  --prep_res_sim                          true
% 2.52/1.01  --prep_upred                            true
% 2.52/1.01  --prep_sem_filter                       exhaustive
% 2.52/1.01  --prep_sem_filter_out                   false
% 2.52/1.01  --pred_elim                             true
% 2.52/1.01  --res_sim_input                         true
% 2.52/1.01  --eq_ax_congr_red                       true
% 2.52/1.01  --pure_diseq_elim                       true
% 2.52/1.01  --brand_transform                       false
% 2.52/1.01  --non_eq_to_eq                          false
% 2.52/1.01  --prep_def_merge                        true
% 2.52/1.01  --prep_def_merge_prop_impl              false
% 2.52/1.01  --prep_def_merge_mbd                    true
% 2.52/1.01  --prep_def_merge_tr_red                 false
% 2.52/1.01  --prep_def_merge_tr_cl                  false
% 2.52/1.01  --smt_preprocessing                     true
% 2.52/1.01  --smt_ac_axioms                         fast
% 2.52/1.01  --preprocessed_out                      false
% 2.52/1.01  --preprocessed_stats                    false
% 2.52/1.01  
% 2.52/1.01  ------ Abstraction refinement Options
% 2.52/1.01  
% 2.52/1.01  --abstr_ref                             []
% 2.52/1.01  --abstr_ref_prep                        false
% 2.52/1.01  --abstr_ref_until_sat                   false
% 2.52/1.01  --abstr_ref_sig_restrict                funpre
% 2.52/1.01  --abstr_ref_af_restrict_to_split_sk     false
% 2.52/1.01  --abstr_ref_under                       []
% 2.52/1.01  
% 2.52/1.01  ------ SAT Options
% 2.52/1.01  
% 2.52/1.01  --sat_mode                              false
% 2.52/1.01  --sat_fm_restart_options                ""
% 2.52/1.01  --sat_gr_def                            false
% 2.52/1.01  --sat_epr_types                         true
% 2.52/1.01  --sat_non_cyclic_types                  false
% 2.52/1.01  --sat_finite_models                     false
% 2.52/1.01  --sat_fm_lemmas                         false
% 2.52/1.01  --sat_fm_prep                           false
% 2.52/1.01  --sat_fm_uc_incr                        true
% 2.52/1.01  --sat_out_model                         small
% 2.52/1.01  --sat_out_clauses                       false
% 2.52/1.01  
% 2.52/1.01  ------ QBF Options
% 2.52/1.01  
% 2.52/1.01  --qbf_mode                              false
% 2.52/1.01  --qbf_elim_univ                         false
% 2.52/1.01  --qbf_dom_inst                          none
% 2.52/1.01  --qbf_dom_pre_inst                      false
% 2.52/1.01  --qbf_sk_in                             false
% 2.52/1.01  --qbf_pred_elim                         true
% 2.52/1.01  --qbf_split                             512
% 2.52/1.01  
% 2.52/1.01  ------ BMC1 Options
% 2.52/1.01  
% 2.52/1.01  --bmc1_incremental                      false
% 2.52/1.01  --bmc1_axioms                           reachable_all
% 2.52/1.01  --bmc1_min_bound                        0
% 2.52/1.01  --bmc1_max_bound                        -1
% 2.52/1.01  --bmc1_max_bound_default                -1
% 2.52/1.01  --bmc1_symbol_reachability              true
% 2.52/1.01  --bmc1_property_lemmas                  false
% 2.52/1.01  --bmc1_k_induction                      false
% 2.52/1.01  --bmc1_non_equiv_states                 false
% 2.52/1.01  --bmc1_deadlock                         false
% 2.52/1.01  --bmc1_ucm                              false
% 2.52/1.01  --bmc1_add_unsat_core                   none
% 2.52/1.01  --bmc1_unsat_core_children              false
% 2.52/1.01  --bmc1_unsat_core_extrapolate_axioms    false
% 2.52/1.01  --bmc1_out_stat                         full
% 2.52/1.01  --bmc1_ground_init                      false
% 2.52/1.01  --bmc1_pre_inst_next_state              false
% 2.52/1.01  --bmc1_pre_inst_state                   false
% 2.52/1.01  --bmc1_pre_inst_reach_state             false
% 2.52/1.01  --bmc1_out_unsat_core                   false
% 2.52/1.01  --bmc1_aig_witness_out                  false
% 2.52/1.01  --bmc1_verbose                          false
% 2.52/1.01  --bmc1_dump_clauses_tptp                false
% 2.52/1.01  --bmc1_dump_unsat_core_tptp             false
% 2.52/1.01  --bmc1_dump_file                        -
% 2.52/1.01  --bmc1_ucm_expand_uc_limit              128
% 2.52/1.01  --bmc1_ucm_n_expand_iterations          6
% 2.52/1.01  --bmc1_ucm_extend_mode                  1
% 2.52/1.01  --bmc1_ucm_init_mode                    2
% 2.52/1.01  --bmc1_ucm_cone_mode                    none
% 2.52/1.01  --bmc1_ucm_reduced_relation_type        0
% 2.52/1.01  --bmc1_ucm_relax_model                  4
% 2.52/1.01  --bmc1_ucm_full_tr_after_sat            true
% 2.52/1.01  --bmc1_ucm_expand_neg_assumptions       false
% 2.52/1.01  --bmc1_ucm_layered_model                none
% 2.52/1.01  --bmc1_ucm_max_lemma_size               10
% 2.52/1.01  
% 2.52/1.01  ------ AIG Options
% 2.52/1.01  
% 2.52/1.01  --aig_mode                              false
% 2.52/1.01  
% 2.52/1.01  ------ Instantiation Options
% 2.52/1.01  
% 2.52/1.01  --instantiation_flag                    true
% 2.52/1.01  --inst_sos_flag                         false
% 2.52/1.01  --inst_sos_phase                        true
% 2.52/1.01  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 2.52/1.01  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 2.52/1.01  --inst_lit_sel_side                     num_symb
% 2.52/1.01  --inst_solver_per_active                1400
% 2.52/1.01  --inst_solver_calls_frac                1.
% 2.52/1.01  --inst_passive_queue_type               priority_queues
% 2.52/1.01  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 2.52/1.01  --inst_passive_queues_freq              [25;2]
% 2.52/1.01  --inst_dismatching                      true
% 2.52/1.01  --inst_eager_unprocessed_to_passive     true
% 2.52/1.01  --inst_prop_sim_given                   true
% 2.52/1.01  --inst_prop_sim_new                     false
% 2.52/1.01  --inst_subs_new                         false
% 2.52/1.01  --inst_eq_res_simp                      false
% 2.52/1.01  --inst_subs_given                       false
% 2.52/1.01  --inst_orphan_elimination               true
% 2.52/1.01  --inst_learning_loop_flag               true
% 2.52/1.01  --inst_learning_start                   3000
% 2.52/1.01  --inst_learning_factor                  2
% 2.52/1.01  --inst_start_prop_sim_after_learn       3
% 2.52/1.01  --inst_sel_renew                        solver
% 2.52/1.01  --inst_lit_activity_flag                true
% 2.52/1.01  --inst_restr_to_given                   false
% 2.52/1.01  --inst_activity_threshold               500
% 2.52/1.01  --inst_out_proof                        true
% 2.52/1.01  
% 2.52/1.01  ------ Resolution Options
% 2.52/1.01  
% 2.52/1.01  --resolution_flag                       true
% 2.52/1.01  --res_lit_sel                           adaptive
% 2.52/1.01  --res_lit_sel_side                      none
% 2.52/1.01  --res_ordering                          kbo
% 2.52/1.01  --res_to_prop_solver                    active
% 2.52/1.01  --res_prop_simpl_new                    false
% 2.52/1.01  --res_prop_simpl_given                  true
% 2.52/1.01  --res_passive_queue_type                priority_queues
% 2.52/1.01  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 2.52/1.01  --res_passive_queues_freq               [15;5]
% 2.52/1.01  --res_forward_subs                      full
% 2.52/1.01  --res_backward_subs                     full
% 2.52/1.01  --res_forward_subs_resolution           true
% 2.52/1.01  --res_backward_subs_resolution          true
% 2.52/1.01  --res_orphan_elimination                true
% 2.52/1.01  --res_time_limit                        2.
% 2.52/1.01  --res_out_proof                         true
% 2.52/1.01  
% 2.52/1.01  ------ Superposition Options
% 2.52/1.01  
% 2.52/1.01  --superposition_flag                    true
% 2.52/1.01  --sup_passive_queue_type                priority_queues
% 2.52/1.01  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 2.52/1.01  --sup_passive_queues_freq               [8;1;4]
% 2.52/1.01  --demod_completeness_check              fast
% 2.52/1.01  --demod_use_ground                      true
% 2.52/1.01  --sup_to_prop_solver                    passive
% 2.52/1.01  --sup_prop_simpl_new                    true
% 2.52/1.01  --sup_prop_simpl_given                  true
% 2.52/1.01  --sup_fun_splitting                     false
% 2.52/1.01  --sup_smt_interval                      50000
% 2.52/1.01  
% 2.52/1.01  ------ Superposition Simplification Setup
% 2.52/1.01  
% 2.52/1.01  --sup_indices_passive                   []
% 2.52/1.01  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.52/1.01  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.52/1.01  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.52/1.01  --sup_full_triv                         [TrivRules;PropSubs]
% 2.52/1.01  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.52/1.01  --sup_full_bw                           [BwDemod]
% 2.52/1.01  --sup_immed_triv                        [TrivRules]
% 2.52/1.01  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 2.52/1.01  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.52/1.01  --sup_immed_bw_main                     []
% 2.52/1.01  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.52/1.01  --sup_input_triv                        [Unflattening;TrivRules]
% 2.52/1.01  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.52/1.01  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.52/1.01  
% 2.52/1.01  ------ Combination Options
% 2.52/1.01  
% 2.52/1.01  --comb_res_mult                         3
% 2.52/1.01  --comb_sup_mult                         2
% 2.52/1.01  --comb_inst_mult                        10
% 2.52/1.01  
% 2.52/1.01  ------ Debug Options
% 2.52/1.01  
% 2.52/1.01  --dbg_backtrace                         false
% 2.52/1.01  --dbg_dump_prop_clauses                 false
% 2.52/1.01  --dbg_dump_prop_clauses_file            -
% 2.52/1.01  --dbg_out_stat                          false
% 2.52/1.01  ------ Parsing...
% 2.52/1.01  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 2.52/1.01  
% 2.52/1.01  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe:1:0s pe:2:0s pe_e  sf_s  rm: 3 0s  sf_e  pe_s  pe_e 
% 2.52/1.01  
% 2.52/1.01  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 2.52/1.01  
% 2.52/1.01  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 2.52/1.01  ------ Proving...
% 2.52/1.01  ------ Problem Properties 
% 2.52/1.01  
% 2.52/1.01  
% 2.52/1.01  clauses                                 24
% 2.52/1.01  conjectures                             5
% 2.52/1.01  EPR                                     3
% 2.52/1.01  Horn                                    24
% 2.52/1.01  unary                                   9
% 2.52/1.01  binary                                  2
% 2.52/1.01  lits                                    70
% 2.52/1.01  lits eq                                 7
% 2.52/1.01  fd_pure                                 0
% 2.52/1.01  fd_pseudo                               0
% 2.52/1.01  fd_cond                                 0
% 2.52/1.01  fd_pseudo_cond                          1
% 2.52/1.01  AC symbols                              0
% 2.52/1.01  
% 2.52/1.01  ------ Schedule dynamic 5 is on 
% 2.52/1.01  
% 2.52/1.01  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" Time Limit: 10.
% 2.52/1.01  
% 2.52/1.01  
% 2.52/1.01  ------ 
% 2.52/1.01  Current options:
% 2.52/1.01  ------ 
% 2.52/1.01  
% 2.52/1.01  ------ Input Options
% 2.52/1.01  
% 2.52/1.01  --out_options                           all
% 2.52/1.01  --tptp_safe_out                         true
% 2.52/1.01  --problem_path                          ""
% 2.52/1.01  --include_path                          ""
% 2.52/1.01  --clausifier                            res/vclausify_rel
% 2.52/1.01  --clausifier_options                    --mode clausify
% 2.52/1.01  --stdin                                 false
% 2.52/1.01  --stats_out                             all
% 2.52/1.01  
% 2.52/1.01  ------ General Options
% 2.52/1.01  
% 2.52/1.01  --fof                                   false
% 2.52/1.01  --time_out_real                         305.
% 2.52/1.01  --time_out_virtual                      -1.
% 2.52/1.01  --symbol_type_check                     false
% 2.52/1.01  --clausify_out                          false
% 2.52/1.01  --sig_cnt_out                           false
% 2.52/1.01  --trig_cnt_out                          false
% 2.52/1.01  --trig_cnt_out_tolerance                1.
% 2.52/1.01  --trig_cnt_out_sk_spl                   false
% 2.52/1.01  --abstr_cl_out                          false
% 2.52/1.01  
% 2.52/1.01  ------ Global Options
% 2.52/1.01  
% 2.52/1.01  --schedule                              default
% 2.52/1.01  --add_important_lit                     false
% 2.52/1.01  --prop_solver_per_cl                    1000
% 2.52/1.01  --min_unsat_core                        false
% 2.52/1.01  --soft_assumptions                      false
% 2.52/1.01  --soft_lemma_size                       3
% 2.52/1.01  --prop_impl_unit_size                   0
% 2.52/1.01  --prop_impl_unit                        []
% 2.52/1.01  --share_sel_clauses                     true
% 2.52/1.01  --reset_solvers                         false
% 2.52/1.01  --bc_imp_inh                            [conj_cone]
% 2.52/1.01  --conj_cone_tolerance                   3.
% 2.52/1.01  --extra_neg_conj                        none
% 2.52/1.01  --large_theory_mode                     true
% 2.52/1.01  --prolific_symb_bound                   200
% 2.52/1.01  --lt_threshold                          2000
% 2.52/1.01  --clause_weak_htbl                      true
% 2.52/1.01  --gc_record_bc_elim                     false
% 2.52/1.01  
% 2.52/1.01  ------ Preprocessing Options
% 2.52/1.01  
% 2.52/1.01  --preprocessing_flag                    true
% 2.52/1.01  --time_out_prep_mult                    0.1
% 2.52/1.01  --splitting_mode                        input
% 2.52/1.01  --splitting_grd                         true
% 2.52/1.01  --splitting_cvd                         false
% 2.52/1.01  --splitting_cvd_svl                     false
% 2.52/1.01  --splitting_nvd                         32
% 2.52/1.01  --sub_typing                            true
% 2.52/1.01  --prep_gs_sim                           true
% 2.52/1.01  --prep_unflatten                        true
% 2.52/1.01  --prep_res_sim                          true
% 2.52/1.01  --prep_upred                            true
% 2.52/1.01  --prep_sem_filter                       exhaustive
% 2.52/1.01  --prep_sem_filter_out                   false
% 2.52/1.01  --pred_elim                             true
% 2.52/1.01  --res_sim_input                         true
% 2.52/1.01  --eq_ax_congr_red                       true
% 2.52/1.01  --pure_diseq_elim                       true
% 2.52/1.01  --brand_transform                       false
% 2.52/1.01  --non_eq_to_eq                          false
% 2.52/1.01  --prep_def_merge                        true
% 2.52/1.01  --prep_def_merge_prop_impl              false
% 2.52/1.01  --prep_def_merge_mbd                    true
% 2.52/1.01  --prep_def_merge_tr_red                 false
% 2.52/1.01  --prep_def_merge_tr_cl                  false
% 2.52/1.01  --smt_preprocessing                     true
% 2.52/1.01  --smt_ac_axioms                         fast
% 2.52/1.01  --preprocessed_out                      false
% 2.52/1.01  --preprocessed_stats                    false
% 2.52/1.01  
% 2.52/1.01  ------ Abstraction refinement Options
% 2.52/1.01  
% 2.52/1.01  --abstr_ref                             []
% 2.52/1.01  --abstr_ref_prep                        false
% 2.52/1.01  --abstr_ref_until_sat                   false
% 2.52/1.01  --abstr_ref_sig_restrict                funpre
% 2.52/1.01  --abstr_ref_af_restrict_to_split_sk     false
% 2.52/1.01  --abstr_ref_under                       []
% 2.52/1.01  
% 2.52/1.01  ------ SAT Options
% 2.52/1.01  
% 2.52/1.01  --sat_mode                              false
% 2.52/1.01  --sat_fm_restart_options                ""
% 2.52/1.01  --sat_gr_def                            false
% 2.52/1.01  --sat_epr_types                         true
% 2.52/1.01  --sat_non_cyclic_types                  false
% 2.52/1.01  --sat_finite_models                     false
% 2.52/1.01  --sat_fm_lemmas                         false
% 2.52/1.01  --sat_fm_prep                           false
% 2.52/1.01  --sat_fm_uc_incr                        true
% 2.52/1.01  --sat_out_model                         small
% 2.52/1.01  --sat_out_clauses                       false
% 2.52/1.01  
% 2.52/1.01  ------ QBF Options
% 2.52/1.01  
% 2.52/1.01  --qbf_mode                              false
% 2.52/1.01  --qbf_elim_univ                         false
% 2.52/1.01  --qbf_dom_inst                          none
% 2.52/1.01  --qbf_dom_pre_inst                      false
% 2.52/1.01  --qbf_sk_in                             false
% 2.52/1.01  --qbf_pred_elim                         true
% 2.52/1.01  --qbf_split                             512
% 2.52/1.01  
% 2.52/1.01  ------ BMC1 Options
% 2.52/1.01  
% 2.52/1.01  --bmc1_incremental                      false
% 2.52/1.01  --bmc1_axioms                           reachable_all
% 2.52/1.01  --bmc1_min_bound                        0
% 2.52/1.01  --bmc1_max_bound                        -1
% 2.52/1.01  --bmc1_max_bound_default                -1
% 2.52/1.01  --bmc1_symbol_reachability              true
% 2.52/1.01  --bmc1_property_lemmas                  false
% 2.52/1.01  --bmc1_k_induction                      false
% 2.52/1.01  --bmc1_non_equiv_states                 false
% 2.52/1.01  --bmc1_deadlock                         false
% 2.52/1.01  --bmc1_ucm                              false
% 2.52/1.01  --bmc1_add_unsat_core                   none
% 2.52/1.01  --bmc1_unsat_core_children              false
% 2.52/1.01  --bmc1_unsat_core_extrapolate_axioms    false
% 2.52/1.01  --bmc1_out_stat                         full
% 2.52/1.01  --bmc1_ground_init                      false
% 2.52/1.01  --bmc1_pre_inst_next_state              false
% 2.52/1.01  --bmc1_pre_inst_state                   false
% 2.52/1.01  --bmc1_pre_inst_reach_state             false
% 2.52/1.01  --bmc1_out_unsat_core                   false
% 2.52/1.01  --bmc1_aig_witness_out                  false
% 2.52/1.01  --bmc1_verbose                          false
% 2.52/1.01  --bmc1_dump_clauses_tptp                false
% 2.52/1.01  --bmc1_dump_unsat_core_tptp             false
% 2.52/1.01  --bmc1_dump_file                        -
% 2.52/1.01  --bmc1_ucm_expand_uc_limit              128
% 2.52/1.01  --bmc1_ucm_n_expand_iterations          6
% 2.52/1.01  --bmc1_ucm_extend_mode                  1
% 2.52/1.01  --bmc1_ucm_init_mode                    2
% 2.52/1.01  --bmc1_ucm_cone_mode                    none
% 2.52/1.01  --bmc1_ucm_reduced_relation_type        0
% 2.52/1.01  --bmc1_ucm_relax_model                  4
% 2.52/1.01  --bmc1_ucm_full_tr_after_sat            true
% 2.52/1.01  --bmc1_ucm_expand_neg_assumptions       false
% 2.52/1.01  --bmc1_ucm_layered_model                none
% 2.52/1.01  --bmc1_ucm_max_lemma_size               10
% 2.52/1.01  
% 2.52/1.01  ------ AIG Options
% 2.52/1.01  
% 2.52/1.01  --aig_mode                              false
% 2.52/1.01  
% 2.52/1.01  ------ Instantiation Options
% 2.52/1.01  
% 2.52/1.01  --instantiation_flag                    true
% 2.52/1.01  --inst_sos_flag                         false
% 2.52/1.01  --inst_sos_phase                        true
% 2.52/1.01  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 2.52/1.01  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 2.52/1.01  --inst_lit_sel_side                     none
% 2.52/1.01  --inst_solver_per_active                1400
% 2.52/1.01  --inst_solver_calls_frac                1.
% 2.52/1.01  --inst_passive_queue_type               priority_queues
% 2.52/1.01  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 2.52/1.01  --inst_passive_queues_freq              [25;2]
% 2.52/1.01  --inst_dismatching                      true
% 2.52/1.01  --inst_eager_unprocessed_to_passive     true
% 2.52/1.01  --inst_prop_sim_given                   true
% 2.52/1.01  --inst_prop_sim_new                     false
% 2.52/1.01  --inst_subs_new                         false
% 2.52/1.01  --inst_eq_res_simp                      false
% 2.52/1.01  --inst_subs_given                       false
% 2.52/1.01  --inst_orphan_elimination               true
% 2.52/1.01  --inst_learning_loop_flag               true
% 2.52/1.01  --inst_learning_start                   3000
% 2.52/1.01  --inst_learning_factor                  2
% 2.52/1.01  --inst_start_prop_sim_after_learn       3
% 2.52/1.01  --inst_sel_renew                        solver
% 2.52/1.01  --inst_lit_activity_flag                true
% 2.52/1.01  --inst_restr_to_given                   false
% 2.52/1.01  --inst_activity_threshold               500
% 2.52/1.01  --inst_out_proof                        true
% 2.52/1.01  
% 2.52/1.01  ------ Resolution Options
% 2.52/1.01  
% 2.52/1.01  --resolution_flag                       false
% 2.52/1.01  --res_lit_sel                           adaptive
% 2.52/1.01  --res_lit_sel_side                      none
% 2.52/1.01  --res_ordering                          kbo
% 2.52/1.01  --res_to_prop_solver                    active
% 2.52/1.01  --res_prop_simpl_new                    false
% 2.52/1.01  --res_prop_simpl_given                  true
% 2.52/1.01  --res_passive_queue_type                priority_queues
% 2.52/1.01  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 2.52/1.01  --res_passive_queues_freq               [15;5]
% 2.52/1.01  --res_forward_subs                      full
% 2.52/1.01  --res_backward_subs                     full
% 2.52/1.01  --res_forward_subs_resolution           true
% 2.52/1.01  --res_backward_subs_resolution          true
% 2.52/1.01  --res_orphan_elimination                true
% 2.52/1.01  --res_time_limit                        2.
% 2.52/1.01  --res_out_proof                         true
% 2.52/1.01  
% 2.52/1.01  ------ Superposition Options
% 2.52/1.01  
% 2.52/1.01  --superposition_flag                    true
% 2.52/1.01  --sup_passive_queue_type                priority_queues
% 2.52/1.01  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 2.52/1.01  --sup_passive_queues_freq               [8;1;4]
% 2.52/1.01  --demod_completeness_check              fast
% 2.52/1.01  --demod_use_ground                      true
% 2.52/1.01  --sup_to_prop_solver                    passive
% 2.52/1.01  --sup_prop_simpl_new                    true
% 2.52/1.01  --sup_prop_simpl_given                  true
% 2.52/1.01  --sup_fun_splitting                     false
% 2.52/1.01  --sup_smt_interval                      50000
% 2.52/1.01  
% 2.52/1.01  ------ Superposition Simplification Setup
% 2.52/1.01  
% 2.52/1.01  --sup_indices_passive                   []
% 2.52/1.01  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.52/1.01  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.52/1.01  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.52/1.01  --sup_full_triv                         [TrivRules;PropSubs]
% 2.52/1.01  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.52/1.01  --sup_full_bw                           [BwDemod]
% 2.52/1.01  --sup_immed_triv                        [TrivRules]
% 2.52/1.01  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 2.52/1.01  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.52/1.01  --sup_immed_bw_main                     []
% 2.52/1.01  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.52/1.01  --sup_input_triv                        [Unflattening;TrivRules]
% 2.52/1.01  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.52/1.01  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.52/1.01  
% 2.52/1.01  ------ Combination Options
% 2.52/1.01  
% 2.52/1.01  --comb_res_mult                         3
% 2.52/1.01  --comb_sup_mult                         2
% 2.52/1.01  --comb_inst_mult                        10
% 2.52/1.01  
% 2.52/1.01  ------ Debug Options
% 2.52/1.01  
% 2.52/1.01  --dbg_backtrace                         false
% 2.52/1.01  --dbg_dump_prop_clauses                 false
% 2.52/1.01  --dbg_dump_prop_clauses_file            -
% 2.52/1.01  --dbg_out_stat                          false
% 2.52/1.01  
% 2.52/1.01  
% 2.52/1.01  
% 2.52/1.01  
% 2.52/1.01  ------ Proving...
% 2.52/1.01  
% 2.52/1.01  
% 2.52/1.01  % SZS status Theorem for theBenchmark.p
% 2.52/1.01  
% 2.52/1.01  % SZS output start CNFRefutation for theBenchmark.p
% 2.52/1.01  
% 2.52/1.01  fof(f16,conjecture,(
% 2.52/1.01    ! [X0,X1] : ((m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v3_funct_2(X1,X0,X0) & v1_funct_2(X1,X0,X0) & v1_funct_1(X1)) => (r2_relset_1(X0,X0,k1_partfun1(X0,X0,X0,X0,k2_funct_2(X0,X1),X1),k6_partfun1(X0)) & r2_relset_1(X0,X0,k1_partfun1(X0,X0,X0,X0,X1,k2_funct_2(X0,X1)),k6_partfun1(X0))))),
% 2.52/1.01    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.52/1.01  
% 2.52/1.01  fof(f17,negated_conjecture,(
% 2.52/1.01    ~! [X0,X1] : ((m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v3_funct_2(X1,X0,X0) & v1_funct_2(X1,X0,X0) & v1_funct_1(X1)) => (r2_relset_1(X0,X0,k1_partfun1(X0,X0,X0,X0,k2_funct_2(X0,X1),X1),k6_partfun1(X0)) & r2_relset_1(X0,X0,k1_partfun1(X0,X0,X0,X0,X1,k2_funct_2(X0,X1)),k6_partfun1(X0))))),
% 2.52/1.01    inference(negated_conjecture,[],[f16])).
% 2.52/1.01  
% 2.52/1.01  fof(f40,plain,(
% 2.52/1.01    ? [X0,X1] : ((~r2_relset_1(X0,X0,k1_partfun1(X0,X0,X0,X0,k2_funct_2(X0,X1),X1),k6_partfun1(X0)) | ~r2_relset_1(X0,X0,k1_partfun1(X0,X0,X0,X0,X1,k2_funct_2(X0,X1)),k6_partfun1(X0))) & (m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v3_funct_2(X1,X0,X0) & v1_funct_2(X1,X0,X0) & v1_funct_1(X1)))),
% 2.52/1.01    inference(ennf_transformation,[],[f17])).
% 2.52/1.01  
% 2.52/1.01  fof(f41,plain,(
% 2.52/1.01    ? [X0,X1] : ((~r2_relset_1(X0,X0,k1_partfun1(X0,X0,X0,X0,k2_funct_2(X0,X1),X1),k6_partfun1(X0)) | ~r2_relset_1(X0,X0,k1_partfun1(X0,X0,X0,X0,X1,k2_funct_2(X0,X1)),k6_partfun1(X0))) & m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v3_funct_2(X1,X0,X0) & v1_funct_2(X1,X0,X0) & v1_funct_1(X1))),
% 2.52/1.01    inference(flattening,[],[f40])).
% 2.52/1.01  
% 2.52/1.01  fof(f45,plain,(
% 2.52/1.01    ? [X0,X1] : ((~r2_relset_1(X0,X0,k1_partfun1(X0,X0,X0,X0,k2_funct_2(X0,X1),X1),k6_partfun1(X0)) | ~r2_relset_1(X0,X0,k1_partfun1(X0,X0,X0,X0,X1,k2_funct_2(X0,X1)),k6_partfun1(X0))) & m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v3_funct_2(X1,X0,X0) & v1_funct_2(X1,X0,X0) & v1_funct_1(X1)) => ((~r2_relset_1(sK1,sK1,k1_partfun1(sK1,sK1,sK1,sK1,k2_funct_2(sK1,sK2),sK2),k6_partfun1(sK1)) | ~r2_relset_1(sK1,sK1,k1_partfun1(sK1,sK1,sK1,sK1,sK2,k2_funct_2(sK1,sK2)),k6_partfun1(sK1))) & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK1,sK1))) & v3_funct_2(sK2,sK1,sK1) & v1_funct_2(sK2,sK1,sK1) & v1_funct_1(sK2))),
% 2.52/1.01    introduced(choice_axiom,[])).
% 2.52/1.01  
% 2.52/1.01  fof(f46,plain,(
% 2.52/1.01    (~r2_relset_1(sK1,sK1,k1_partfun1(sK1,sK1,sK1,sK1,k2_funct_2(sK1,sK2),sK2),k6_partfun1(sK1)) | ~r2_relset_1(sK1,sK1,k1_partfun1(sK1,sK1,sK1,sK1,sK2,k2_funct_2(sK1,sK2)),k6_partfun1(sK1))) & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK1,sK1))) & v3_funct_2(sK2,sK1,sK1) & v1_funct_2(sK2,sK1,sK1) & v1_funct_1(sK2)),
% 2.52/1.01    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1,sK2])],[f41,f45])).
% 2.52/1.01  
% 2.52/1.01  fof(f75,plain,(
% 2.52/1.01    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK1,sK1)))),
% 2.52/1.01    inference(cnf_transformation,[],[f46])).
% 2.52/1.01  
% 2.52/1.01  fof(f13,axiom,(
% 2.52/1.01    ! [X0,X1] : ((m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v3_funct_2(X1,X0,X0) & v1_funct_2(X1,X0,X0) & v1_funct_1(X1)) => k2_funct_1(X1) = k2_funct_2(X0,X1))),
% 2.52/1.01    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.52/1.01  
% 2.52/1.01  fof(f36,plain,(
% 2.52/1.01    ! [X0,X1] : (k2_funct_1(X1) = k2_funct_2(X0,X1) | (~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) | ~v3_funct_2(X1,X0,X0) | ~v1_funct_2(X1,X0,X0) | ~v1_funct_1(X1)))),
% 2.52/1.01    inference(ennf_transformation,[],[f13])).
% 2.52/1.01  
% 2.52/1.01  fof(f37,plain,(
% 2.52/1.01    ! [X0,X1] : (k2_funct_1(X1) = k2_funct_2(X0,X1) | ~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) | ~v3_funct_2(X1,X0,X0) | ~v1_funct_2(X1,X0,X0) | ~v1_funct_1(X1))),
% 2.52/1.01    inference(flattening,[],[f36])).
% 2.52/1.01  
% 2.52/1.01  fof(f69,plain,(
% 2.52/1.01    ( ! [X0,X1] : (k2_funct_1(X1) = k2_funct_2(X0,X1) | ~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) | ~v3_funct_2(X1,X0,X0) | ~v1_funct_2(X1,X0,X0) | ~v1_funct_1(X1)) )),
% 2.52/1.01    inference(cnf_transformation,[],[f37])).
% 2.52/1.01  
% 2.52/1.01  fof(f72,plain,(
% 2.52/1.01    v1_funct_1(sK2)),
% 2.52/1.01    inference(cnf_transformation,[],[f46])).
% 2.52/1.01  
% 2.52/1.01  fof(f73,plain,(
% 2.52/1.01    v1_funct_2(sK2,sK1,sK1)),
% 2.52/1.01    inference(cnf_transformation,[],[f46])).
% 2.52/1.01  
% 2.52/1.01  fof(f74,plain,(
% 2.52/1.01    v3_funct_2(sK2,sK1,sK1)),
% 2.52/1.01    inference(cnf_transformation,[],[f46])).
% 2.52/1.01  
% 2.52/1.01  fof(f9,axiom,(
% 2.52/1.01    ! [X0,X1] : ((m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v3_funct_2(X1,X0,X0) & v1_funct_2(X1,X0,X0) & v1_funct_1(X1)) => (m1_subset_1(k2_funct_2(X0,X1),k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v3_funct_2(k2_funct_2(X0,X1),X0,X0) & v1_funct_2(k2_funct_2(X0,X1),X0,X0) & v1_funct_1(k2_funct_2(X0,X1))))),
% 2.52/1.01    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.52/1.01  
% 2.52/1.01  fof(f32,plain,(
% 2.52/1.01    ! [X0,X1] : ((m1_subset_1(k2_funct_2(X0,X1),k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v3_funct_2(k2_funct_2(X0,X1),X0,X0) & v1_funct_2(k2_funct_2(X0,X1),X0,X0) & v1_funct_1(k2_funct_2(X0,X1))) | (~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) | ~v3_funct_2(X1,X0,X0) | ~v1_funct_2(X1,X0,X0) | ~v1_funct_1(X1)))),
% 2.52/1.01    inference(ennf_transformation,[],[f9])).
% 2.52/1.01  
% 2.52/1.01  fof(f33,plain,(
% 2.52/1.01    ! [X0,X1] : ((m1_subset_1(k2_funct_2(X0,X1),k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v3_funct_2(k2_funct_2(X0,X1),X0,X0) & v1_funct_2(k2_funct_2(X0,X1),X0,X0) & v1_funct_1(k2_funct_2(X0,X1))) | ~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) | ~v3_funct_2(X1,X0,X0) | ~v1_funct_2(X1,X0,X0) | ~v1_funct_1(X1))),
% 2.52/1.01    inference(flattening,[],[f32])).
% 2.52/1.01  
% 2.52/1.01  fof(f62,plain,(
% 2.52/1.01    ( ! [X0,X1] : (m1_subset_1(k2_funct_2(X0,X1),k1_zfmisc_1(k2_zfmisc_1(X0,X0))) | ~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) | ~v3_funct_2(X1,X0,X0) | ~v1_funct_2(X1,X0,X0) | ~v1_funct_1(X1)) )),
% 2.52/1.01    inference(cnf_transformation,[],[f33])).
% 2.52/1.01  
% 2.52/1.01  fof(f12,axiom,(
% 2.52/1.01    ! [X0,X1,X2,X3,X4,X5] : ((m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) & v1_funct_1(X5) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_1(X4)) => k5_relat_1(X4,X5) = k1_partfun1(X0,X1,X2,X3,X4,X5))),
% 2.52/1.01    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.52/1.01  
% 2.52/1.01  fof(f34,plain,(
% 2.52/1.01    ! [X0,X1,X2,X3,X4,X5] : (k5_relat_1(X4,X5) = k1_partfun1(X0,X1,X2,X3,X4,X5) | (~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X4)))),
% 2.52/1.01    inference(ennf_transformation,[],[f12])).
% 2.52/1.01  
% 2.52/1.01  fof(f35,plain,(
% 2.52/1.01    ! [X0,X1,X2,X3,X4,X5] : (k5_relat_1(X4,X5) = k1_partfun1(X0,X1,X2,X3,X4,X5) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X4))),
% 2.52/1.01    inference(flattening,[],[f34])).
% 2.52/1.01  
% 2.52/1.01  fof(f68,plain,(
% 2.52/1.01    ( ! [X4,X2,X0,X5,X3,X1] : (k5_relat_1(X4,X5) = k1_partfun1(X0,X1,X2,X3,X4,X5) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X4)) )),
% 2.52/1.01    inference(cnf_transformation,[],[f35])).
% 2.52/1.01  
% 2.52/1.01  fof(f59,plain,(
% 2.52/1.01    ( ! [X0,X1] : (v1_funct_1(k2_funct_2(X0,X1)) | ~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) | ~v3_funct_2(X1,X0,X0) | ~v1_funct_2(X1,X0,X0) | ~v1_funct_1(X1)) )),
% 2.52/1.01    inference(cnf_transformation,[],[f33])).
% 2.52/1.01  
% 2.52/1.01  fof(f7,axiom,(
% 2.52/1.01    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => ((v3_funct_2(X2,X0,X1) & v1_funct_1(X2)) => (v2_funct_2(X2,X1) & v2_funct_1(X2) & v1_funct_1(X2))))),
% 2.52/1.01    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.52/1.01  
% 2.52/1.01  fof(f28,plain,(
% 2.52/1.01    ! [X0,X1,X2] : (((v2_funct_2(X2,X1) & v2_funct_1(X2) & v1_funct_1(X2)) | (~v3_funct_2(X2,X0,X1) | ~v1_funct_1(X2))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 2.52/1.01    inference(ennf_transformation,[],[f7])).
% 2.52/1.01  
% 2.52/1.01  fof(f29,plain,(
% 2.52/1.01    ! [X0,X1,X2] : ((v2_funct_2(X2,X1) & v2_funct_1(X2) & v1_funct_1(X2)) | ~v3_funct_2(X2,X0,X1) | ~v1_funct_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 2.52/1.01    inference(flattening,[],[f28])).
% 2.52/1.01  
% 2.52/1.01  fof(f56,plain,(
% 2.52/1.01    ( ! [X2,X0,X1] : (v2_funct_2(X2,X1) | ~v3_funct_2(X2,X0,X1) | ~v1_funct_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 2.52/1.01    inference(cnf_transformation,[],[f29])).
% 2.52/1.01  
% 2.52/1.01  fof(f8,axiom,(
% 2.52/1.01    ! [X0,X1] : ((v5_relat_1(X1,X0) & v1_relat_1(X1)) => (v2_funct_2(X1,X0) <=> k2_relat_1(X1) = X0))),
% 2.52/1.01    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.52/1.01  
% 2.52/1.01  fof(f30,plain,(
% 2.52/1.01    ! [X0,X1] : ((v2_funct_2(X1,X0) <=> k2_relat_1(X1) = X0) | (~v5_relat_1(X1,X0) | ~v1_relat_1(X1)))),
% 2.52/1.01    inference(ennf_transformation,[],[f8])).
% 2.52/1.01  
% 2.52/1.01  fof(f31,plain,(
% 2.52/1.01    ! [X0,X1] : ((v2_funct_2(X1,X0) <=> k2_relat_1(X1) = X0) | ~v5_relat_1(X1,X0) | ~v1_relat_1(X1))),
% 2.52/1.01    inference(flattening,[],[f30])).
% 2.52/1.01  
% 2.52/1.01  fof(f42,plain,(
% 2.52/1.01    ! [X0,X1] : (((v2_funct_2(X1,X0) | k2_relat_1(X1) != X0) & (k2_relat_1(X1) = X0 | ~v2_funct_2(X1,X0))) | ~v5_relat_1(X1,X0) | ~v1_relat_1(X1))),
% 2.52/1.01    inference(nnf_transformation,[],[f31])).
% 2.52/1.01  
% 2.52/1.01  fof(f57,plain,(
% 2.52/1.01    ( ! [X0,X1] : (k2_relat_1(X1) = X0 | ~v2_funct_2(X1,X0) | ~v5_relat_1(X1,X0) | ~v1_relat_1(X1)) )),
% 2.52/1.01    inference(cnf_transformation,[],[f42])).
% 2.52/1.01  
% 2.52/1.01  fof(f4,axiom,(
% 2.52/1.01    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => (v5_relat_1(X2,X1) & v4_relat_1(X2,X0)))),
% 2.52/1.01    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.52/1.01  
% 2.52/1.01  fof(f19,plain,(
% 2.52/1.01    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => v5_relat_1(X2,X1))),
% 2.52/1.01    inference(pure_predicate_removal,[],[f4])).
% 2.52/1.01  
% 2.52/1.01  fof(f24,plain,(
% 2.52/1.01    ! [X0,X1,X2] : (v5_relat_1(X2,X1) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 2.52/1.01    inference(ennf_transformation,[],[f19])).
% 2.52/1.01  
% 2.52/1.01  fof(f51,plain,(
% 2.52/1.01    ( ! [X2,X0,X1] : (v5_relat_1(X2,X1) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 2.52/1.01    inference(cnf_transformation,[],[f24])).
% 2.52/1.01  
% 2.52/1.01  fof(f2,axiom,(
% 2.52/1.01    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1))),
% 2.52/1.01    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.52/1.01  
% 2.52/1.01  fof(f48,plain,(
% 2.52/1.01    ( ! [X0,X1] : (v1_relat_1(k2_zfmisc_1(X0,X1))) )),
% 2.52/1.01    inference(cnf_transformation,[],[f2])).
% 2.52/1.01  
% 2.52/1.01  fof(f1,axiom,(
% 2.52/1.01    ! [X0] : (v1_relat_1(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => v1_relat_1(X1)))),
% 2.52/1.01    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.52/1.01  
% 2.52/1.01  fof(f21,plain,(
% 2.52/1.01    ! [X0] : (! [X1] : (v1_relat_1(X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) | ~v1_relat_1(X0))),
% 2.52/1.01    inference(ennf_transformation,[],[f1])).
% 2.52/1.01  
% 2.52/1.01  fof(f47,plain,(
% 2.52/1.01    ( ! [X0,X1] : (v1_relat_1(X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0)) | ~v1_relat_1(X0)) )),
% 2.52/1.01    inference(cnf_transformation,[],[f21])).
% 2.52/1.01  
% 2.52/1.01  fof(f3,axiom,(
% 2.52/1.01    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => (v2_funct_1(X0) => (k5_relat_1(k2_funct_1(X0),X0) = k6_relat_1(k2_relat_1(X0)) & k5_relat_1(X0,k2_funct_1(X0)) = k6_relat_1(k1_relat_1(X0)))))),
% 2.52/1.01    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.52/1.01  
% 2.52/1.01  fof(f22,plain,(
% 2.52/1.01    ! [X0] : (((k5_relat_1(k2_funct_1(X0),X0) = k6_relat_1(k2_relat_1(X0)) & k5_relat_1(X0,k2_funct_1(X0)) = k6_relat_1(k1_relat_1(X0))) | ~v2_funct_1(X0)) | (~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 2.52/1.01    inference(ennf_transformation,[],[f3])).
% 2.52/1.01  
% 2.52/1.01  fof(f23,plain,(
% 2.52/1.01    ! [X0] : ((k5_relat_1(k2_funct_1(X0),X0) = k6_relat_1(k2_relat_1(X0)) & k5_relat_1(X0,k2_funct_1(X0)) = k6_relat_1(k1_relat_1(X0))) | ~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 2.52/1.01    inference(flattening,[],[f22])).
% 2.52/1.01  
% 2.52/1.01  fof(f50,plain,(
% 2.52/1.01    ( ! [X0] : (k5_relat_1(k2_funct_1(X0),X0) = k6_relat_1(k2_relat_1(X0)) | ~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 2.52/1.01    inference(cnf_transformation,[],[f23])).
% 2.52/1.01  
% 2.52/1.01  fof(f14,axiom,(
% 2.52/1.01    ! [X0] : k6_relat_1(X0) = k6_partfun1(X0)),
% 2.52/1.01    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.52/1.01  
% 2.52/1.01  fof(f70,plain,(
% 2.52/1.01    ( ! [X0] : (k6_relat_1(X0) = k6_partfun1(X0)) )),
% 2.52/1.01    inference(cnf_transformation,[],[f14])).
% 2.52/1.01  
% 2.52/1.01  fof(f77,plain,(
% 2.52/1.01    ( ! [X0] : (k5_relat_1(k2_funct_1(X0),X0) = k6_partfun1(k2_relat_1(X0)) | ~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 2.52/1.01    inference(definition_unfolding,[],[f50,f70])).
% 2.52/1.01  
% 2.52/1.01  fof(f55,plain,(
% 2.52/1.01    ( ! [X2,X0,X1] : (v2_funct_1(X2) | ~v3_funct_2(X2,X0,X1) | ~v1_funct_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 2.52/1.01    inference(cnf_transformation,[],[f29])).
% 2.52/1.01  
% 2.52/1.01  fof(f15,axiom,(
% 2.52/1.01    ! [X0,X1] : ((m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v1_funct_2(X1,X0,X0) & v1_funct_1(X1)) => k1_relset_1(X0,X0,X1) = X0)),
% 2.52/1.01    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.52/1.01  
% 2.52/1.01  fof(f38,plain,(
% 2.52/1.01    ! [X0,X1] : (k1_relset_1(X0,X0,X1) = X0 | (~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) | ~v1_funct_2(X1,X0,X0) | ~v1_funct_1(X1)))),
% 2.52/1.01    inference(ennf_transformation,[],[f15])).
% 2.52/1.01  
% 2.52/1.01  fof(f39,plain,(
% 2.52/1.01    ! [X0,X1] : (k1_relset_1(X0,X0,X1) = X0 | ~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) | ~v1_funct_2(X1,X0,X0) | ~v1_funct_1(X1))),
% 2.52/1.01    inference(flattening,[],[f38])).
% 2.52/1.01  
% 2.52/1.01  fof(f71,plain,(
% 2.52/1.01    ( ! [X0,X1] : (k1_relset_1(X0,X0,X1) = X0 | ~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) | ~v1_funct_2(X1,X0,X0) | ~v1_funct_1(X1)) )),
% 2.52/1.01    inference(cnf_transformation,[],[f39])).
% 2.52/1.01  
% 2.52/1.01  fof(f5,axiom,(
% 2.52/1.01    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k1_relat_1(X2) = k1_relset_1(X0,X1,X2))),
% 2.52/1.01    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.52/1.01  
% 2.52/1.01  fof(f25,plain,(
% 2.52/1.01    ! [X0,X1,X2] : (k1_relat_1(X2) = k1_relset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 2.52/1.01    inference(ennf_transformation,[],[f5])).
% 2.52/1.01  
% 2.52/1.01  fof(f52,plain,(
% 2.52/1.01    ( ! [X2,X0,X1] : (k1_relat_1(X2) = k1_relset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 2.52/1.01    inference(cnf_transformation,[],[f25])).
% 2.52/1.01  
% 2.52/1.01  fof(f49,plain,(
% 2.52/1.01    ( ! [X0] : (k5_relat_1(X0,k2_funct_1(X0)) = k6_relat_1(k1_relat_1(X0)) | ~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 2.52/1.01    inference(cnf_transformation,[],[f23])).
% 2.52/1.01  
% 2.52/1.01  fof(f78,plain,(
% 2.52/1.01    ( ! [X0] : (k5_relat_1(X0,k2_funct_1(X0)) = k6_partfun1(k1_relat_1(X0)) | ~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 2.52/1.01    inference(definition_unfolding,[],[f49,f70])).
% 2.52/1.01  
% 2.52/1.01  fof(f76,plain,(
% 2.52/1.01    ~r2_relset_1(sK1,sK1,k1_partfun1(sK1,sK1,sK1,sK1,k2_funct_2(sK1,sK2),sK2),k6_partfun1(sK1)) | ~r2_relset_1(sK1,sK1,k1_partfun1(sK1,sK1,sK1,sK1,sK2,k2_funct_2(sK1,sK2)),k6_partfun1(sK1))),
% 2.52/1.01    inference(cnf_transformation,[],[f46])).
% 2.52/1.01  
% 2.52/1.01  fof(f10,axiom,(
% 2.52/1.01    ! [X0] : (m1_subset_1(k6_partfun1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v1_partfun1(k6_partfun1(X0),X0))),
% 2.52/1.01    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.52/1.01  
% 2.52/1.01  fof(f18,plain,(
% 2.52/1.01    ! [X0] : m1_subset_1(k6_partfun1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0)))),
% 2.52/1.01    inference(pure_predicate_removal,[],[f10])).
% 2.52/1.01  
% 2.52/1.01  fof(f63,plain,(
% 2.52/1.01    ( ! [X0] : (m1_subset_1(k6_partfun1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0)))) )),
% 2.52/1.01    inference(cnf_transformation,[],[f18])).
% 2.52/1.01  
% 2.52/1.01  fof(f6,axiom,(
% 2.52/1.01    ! [X0,X1,X2,X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) => r2_relset_1(X0,X1,X2,X2))),
% 2.52/1.01    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.52/1.01  
% 2.52/1.01  fof(f26,plain,(
% 2.52/1.01    ! [X0,X1,X2,X3] : (r2_relset_1(X0,X1,X2,X2) | (~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))))),
% 2.52/1.01    inference(ennf_transformation,[],[f6])).
% 2.52/1.01  
% 2.52/1.01  fof(f27,plain,(
% 2.52/1.01    ! [X0,X1,X2,X3] : (r2_relset_1(X0,X1,X2,X2) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 2.52/1.01    inference(flattening,[],[f26])).
% 2.52/1.01  
% 2.52/1.01  fof(f53,plain,(
% 2.52/1.01    ( ! [X2,X0,X3,X1] : (r2_relset_1(X0,X1,X2,X2) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 2.52/1.01    inference(cnf_transformation,[],[f27])).
% 2.52/1.01  
% 2.52/1.01  cnf(c_25,negated_conjecture,
% 2.52/1.01      ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK1,sK1))) ),
% 2.52/1.01      inference(cnf_transformation,[],[f75]) ).
% 2.52/1.01  
% 2.52/1.01  cnf(c_615,negated_conjecture,
% 2.52/1.01      ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK1,sK1))) ),
% 2.52/1.01      inference(subtyping,[status(esa)],[c_25]) ).
% 2.52/1.01  
% 2.52/1.01  cnf(c_1132,plain,
% 2.52/1.01      ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK1,sK1))) = iProver_top ),
% 2.52/1.01      inference(predicate_to_equality,[status(thm)],[c_615]) ).
% 2.52/1.01  
% 2.52/1.01  cnf(c_22,plain,
% 2.52/1.01      ( ~ v1_funct_2(X0,X1,X1)
% 2.52/1.01      | ~ v3_funct_2(X0,X1,X1)
% 2.52/1.01      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X1)))
% 2.52/1.01      | ~ v1_funct_1(X0)
% 2.52/1.01      | k2_funct_2(X1,X0) = k2_funct_1(X0) ),
% 2.52/1.01      inference(cnf_transformation,[],[f69]) ).
% 2.52/1.01  
% 2.52/1.01  cnf(c_618,plain,
% 2.52/1.01      ( ~ v1_funct_2(X0_50,X0_51,X0_51)
% 2.52/1.01      | ~ v3_funct_2(X0_50,X0_51,X0_51)
% 2.52/1.01      | ~ m1_subset_1(X0_50,k1_zfmisc_1(k2_zfmisc_1(X0_51,X0_51)))
% 2.52/1.01      | ~ v1_funct_1(X0_50)
% 2.52/1.01      | k2_funct_2(X0_51,X0_50) = k2_funct_1(X0_50) ),
% 2.52/1.01      inference(subtyping,[status(esa)],[c_22]) ).
% 2.52/1.01  
% 2.52/1.01  cnf(c_1129,plain,
% 2.52/1.01      ( k2_funct_2(X0_51,X0_50) = k2_funct_1(X0_50)
% 2.52/1.01      | v1_funct_2(X0_50,X0_51,X0_51) != iProver_top
% 2.52/1.01      | v3_funct_2(X0_50,X0_51,X0_51) != iProver_top
% 2.52/1.01      | m1_subset_1(X0_50,k1_zfmisc_1(k2_zfmisc_1(X0_51,X0_51))) != iProver_top
% 2.52/1.01      | v1_funct_1(X0_50) != iProver_top ),
% 2.52/1.01      inference(predicate_to_equality,[status(thm)],[c_618]) ).
% 2.52/1.01  
% 2.52/1.01  cnf(c_2092,plain,
% 2.52/1.01      ( k2_funct_2(sK1,sK2) = k2_funct_1(sK2)
% 2.52/1.01      | v1_funct_2(sK2,sK1,sK1) != iProver_top
% 2.52/1.01      | v3_funct_2(sK2,sK1,sK1) != iProver_top
% 2.52/1.01      | v1_funct_1(sK2) != iProver_top ),
% 2.52/1.01      inference(superposition,[status(thm)],[c_1132,c_1129]) ).
% 2.52/1.01  
% 2.52/1.01  cnf(c_28,negated_conjecture,
% 2.52/1.01      ( v1_funct_1(sK2) ),
% 2.52/1.01      inference(cnf_transformation,[],[f72]) ).
% 2.52/1.01  
% 2.52/1.01  cnf(c_27,negated_conjecture,
% 2.52/1.01      ( v1_funct_2(sK2,sK1,sK1) ),
% 2.52/1.01      inference(cnf_transformation,[],[f73]) ).
% 2.52/1.01  
% 2.52/1.01  cnf(c_26,negated_conjecture,
% 2.52/1.01      ( v3_funct_2(sK2,sK1,sK1) ),
% 2.52/1.01      inference(cnf_transformation,[],[f74]) ).
% 2.52/1.01  
% 2.52/1.01  cnf(c_706,plain,
% 2.52/1.01      ( ~ v1_funct_2(sK2,sK1,sK1)
% 2.52/1.01      | ~ v3_funct_2(sK2,sK1,sK1)
% 2.52/1.01      | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK1,sK1)))
% 2.52/1.01      | ~ v1_funct_1(sK2)
% 2.52/1.01      | k2_funct_2(sK1,sK2) = k2_funct_1(sK2) ),
% 2.52/1.01      inference(instantiation,[status(thm)],[c_618]) ).
% 2.52/1.01  
% 2.52/1.01  cnf(c_2316,plain,
% 2.52/1.01      ( k2_funct_2(sK1,sK2) = k2_funct_1(sK2) ),
% 2.52/1.01      inference(global_propositional_subsumption,
% 2.52/1.01                [status(thm)],
% 2.52/1.01                [c_2092,c_28,c_27,c_26,c_25,c_706]) ).
% 2.52/1.01  
% 2.52/1.01  cnf(c_12,plain,
% 2.52/1.01      ( ~ v1_funct_2(X0,X1,X1)
% 2.52/1.01      | ~ v3_funct_2(X0,X1,X1)
% 2.52/1.01      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X1)))
% 2.52/1.01      | m1_subset_1(k2_funct_2(X1,X0),k1_zfmisc_1(k2_zfmisc_1(X1,X1)))
% 2.52/1.01      | ~ v1_funct_1(X0) ),
% 2.52/1.01      inference(cnf_transformation,[],[f62]) ).
% 2.52/1.01  
% 2.52/1.01  cnf(c_627,plain,
% 2.52/1.01      ( ~ v1_funct_2(X0_50,X0_51,X0_51)
% 2.52/1.01      | ~ v3_funct_2(X0_50,X0_51,X0_51)
% 2.52/1.01      | ~ m1_subset_1(X0_50,k1_zfmisc_1(k2_zfmisc_1(X0_51,X0_51)))
% 2.52/1.01      | m1_subset_1(k2_funct_2(X0_51,X0_50),k1_zfmisc_1(k2_zfmisc_1(X0_51,X0_51)))
% 2.52/1.01      | ~ v1_funct_1(X0_50) ),
% 2.52/1.01      inference(subtyping,[status(esa)],[c_12]) ).
% 2.52/1.01  
% 2.52/1.01  cnf(c_1120,plain,
% 2.52/1.01      ( v1_funct_2(X0_50,X0_51,X0_51) != iProver_top
% 2.52/1.01      | v3_funct_2(X0_50,X0_51,X0_51) != iProver_top
% 2.52/1.01      | m1_subset_1(X0_50,k1_zfmisc_1(k2_zfmisc_1(X0_51,X0_51))) != iProver_top
% 2.52/1.01      | m1_subset_1(k2_funct_2(X0_51,X0_50),k1_zfmisc_1(k2_zfmisc_1(X0_51,X0_51))) = iProver_top
% 2.52/1.01      | v1_funct_1(X0_50) != iProver_top ),
% 2.52/1.01      inference(predicate_to_equality,[status(thm)],[c_627]) ).
% 2.52/1.01  
% 2.52/1.01  cnf(c_2650,plain,
% 2.52/1.01      ( v1_funct_2(sK2,sK1,sK1) != iProver_top
% 2.52/1.01      | v3_funct_2(sK2,sK1,sK1) != iProver_top
% 2.52/1.01      | m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK1))) = iProver_top
% 2.52/1.01      | m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK1,sK1))) != iProver_top
% 2.52/1.01      | v1_funct_1(sK2) != iProver_top ),
% 2.52/1.01      inference(superposition,[status(thm)],[c_2316,c_1120]) ).
% 2.52/1.01  
% 2.52/1.01  cnf(c_29,plain,
% 2.52/1.01      ( v1_funct_1(sK2) = iProver_top ),
% 2.52/1.01      inference(predicate_to_equality,[status(thm)],[c_28]) ).
% 2.52/1.01  
% 2.52/1.01  cnf(c_30,plain,
% 2.52/1.01      ( v1_funct_2(sK2,sK1,sK1) = iProver_top ),
% 2.52/1.01      inference(predicate_to_equality,[status(thm)],[c_27]) ).
% 2.52/1.01  
% 2.52/1.01  cnf(c_31,plain,
% 2.52/1.01      ( v3_funct_2(sK2,sK1,sK1) = iProver_top ),
% 2.52/1.01      inference(predicate_to_equality,[status(thm)],[c_26]) ).
% 2.52/1.01  
% 2.52/1.01  cnf(c_32,plain,
% 2.52/1.01      ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK1,sK1))) = iProver_top ),
% 2.52/1.01      inference(predicate_to_equality,[status(thm)],[c_25]) ).
% 2.52/1.01  
% 2.52/1.01  cnf(c_4018,plain,
% 2.52/1.01      ( m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK1))) = iProver_top ),
% 2.52/1.01      inference(global_propositional_subsumption,
% 2.52/1.01                [status(thm)],
% 2.52/1.01                [c_2650,c_29,c_30,c_31,c_32]) ).
% 2.52/1.01  
% 2.52/1.01  cnf(c_21,plain,
% 2.52/1.01      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 2.52/1.01      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X4,X5)))
% 2.52/1.01      | ~ v1_funct_1(X0)
% 2.52/1.01      | ~ v1_funct_1(X3)
% 2.52/1.01      | k1_partfun1(X4,X5,X1,X2,X3,X0) = k5_relat_1(X3,X0) ),
% 2.52/1.01      inference(cnf_transformation,[],[f68]) ).
% 2.52/1.01  
% 2.52/1.01  cnf(c_619,plain,
% 2.52/1.01      ( ~ m1_subset_1(X0_50,k1_zfmisc_1(k2_zfmisc_1(X0_51,X1_51)))
% 2.52/1.01      | ~ m1_subset_1(X1_50,k1_zfmisc_1(k2_zfmisc_1(X2_51,X3_51)))
% 2.52/1.01      | ~ v1_funct_1(X0_50)
% 2.52/1.01      | ~ v1_funct_1(X1_50)
% 2.52/1.01      | k1_partfun1(X2_51,X3_51,X0_51,X1_51,X1_50,X0_50) = k5_relat_1(X1_50,X0_50) ),
% 2.52/1.01      inference(subtyping,[status(esa)],[c_21]) ).
% 2.52/1.01  
% 2.52/1.01  cnf(c_1128,plain,
% 2.52/1.01      ( k1_partfun1(X0_51,X1_51,X2_51,X3_51,X0_50,X1_50) = k5_relat_1(X0_50,X1_50)
% 2.52/1.01      | m1_subset_1(X1_50,k1_zfmisc_1(k2_zfmisc_1(X2_51,X3_51))) != iProver_top
% 2.52/1.01      | m1_subset_1(X0_50,k1_zfmisc_1(k2_zfmisc_1(X0_51,X1_51))) != iProver_top
% 2.52/1.01      | v1_funct_1(X0_50) != iProver_top
% 2.52/1.01      | v1_funct_1(X1_50) != iProver_top ),
% 2.52/1.01      inference(predicate_to_equality,[status(thm)],[c_619]) ).
% 2.52/1.01  
% 2.52/1.01  cnf(c_4024,plain,
% 2.52/1.01      ( k1_partfun1(sK1,sK1,X0_51,X1_51,k2_funct_1(sK2),X0_50) = k5_relat_1(k2_funct_1(sK2),X0_50)
% 2.52/1.01      | m1_subset_1(X0_50,k1_zfmisc_1(k2_zfmisc_1(X0_51,X1_51))) != iProver_top
% 2.52/1.01      | v1_funct_1(X0_50) != iProver_top
% 2.52/1.01      | v1_funct_1(k2_funct_1(sK2)) != iProver_top ),
% 2.52/1.01      inference(superposition,[status(thm)],[c_4018,c_1128]) ).
% 2.52/1.01  
% 2.52/1.01  cnf(c_15,plain,
% 2.52/1.01      ( ~ v1_funct_2(X0,X1,X1)
% 2.52/1.01      | ~ v3_funct_2(X0,X1,X1)
% 2.52/1.01      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X1)))
% 2.52/1.01      | ~ v1_funct_1(X0)
% 2.52/1.01      | v1_funct_1(k2_funct_2(X1,X0)) ),
% 2.52/1.01      inference(cnf_transformation,[],[f59]) ).
% 2.52/1.01  
% 2.52/1.01  cnf(c_624,plain,
% 2.52/1.01      ( ~ v1_funct_2(X0_50,X0_51,X0_51)
% 2.52/1.01      | ~ v3_funct_2(X0_50,X0_51,X0_51)
% 2.52/1.01      | ~ m1_subset_1(X0_50,k1_zfmisc_1(k2_zfmisc_1(X0_51,X0_51)))
% 2.52/1.01      | ~ v1_funct_1(X0_50)
% 2.52/1.01      | v1_funct_1(k2_funct_2(X0_51,X0_50)) ),
% 2.52/1.01      inference(subtyping,[status(esa)],[c_15]) ).
% 2.52/1.01  
% 2.52/1.01  cnf(c_1123,plain,
% 2.52/1.01      ( v1_funct_2(X0_50,X0_51,X0_51) != iProver_top
% 2.52/1.01      | v3_funct_2(X0_50,X0_51,X0_51) != iProver_top
% 2.52/1.01      | m1_subset_1(X0_50,k1_zfmisc_1(k2_zfmisc_1(X0_51,X0_51))) != iProver_top
% 2.52/1.01      | v1_funct_1(X0_50) != iProver_top
% 2.52/1.01      | v1_funct_1(k2_funct_2(X0_51,X0_50)) = iProver_top ),
% 2.52/1.01      inference(predicate_to_equality,[status(thm)],[c_624]) ).
% 2.52/1.01  
% 2.52/1.01  cnf(c_2052,plain,
% 2.52/1.01      ( v1_funct_2(sK2,sK1,sK1) != iProver_top
% 2.52/1.01      | v3_funct_2(sK2,sK1,sK1) != iProver_top
% 2.52/1.01      | v1_funct_1(k2_funct_2(sK1,sK2)) = iProver_top
% 2.52/1.01      | v1_funct_1(sK2) != iProver_top ),
% 2.52/1.01      inference(superposition,[status(thm)],[c_1132,c_1123]) ).
% 2.52/1.01  
% 2.52/1.01  cnf(c_695,plain,
% 2.52/1.01      ( v1_funct_2(X0_50,X0_51,X0_51) != iProver_top
% 2.52/1.01      | v3_funct_2(X0_50,X0_51,X0_51) != iProver_top
% 2.52/1.01      | m1_subset_1(X0_50,k1_zfmisc_1(k2_zfmisc_1(X0_51,X0_51))) != iProver_top
% 2.52/1.01      | v1_funct_1(X0_50) != iProver_top
% 2.52/1.01      | v1_funct_1(k2_funct_2(X0_51,X0_50)) = iProver_top ),
% 2.52/1.01      inference(predicate_to_equality,[status(thm)],[c_624]) ).
% 2.52/1.01  
% 2.52/1.01  cnf(c_697,plain,
% 2.52/1.01      ( v1_funct_2(sK2,sK1,sK1) != iProver_top
% 2.52/1.01      | v3_funct_2(sK2,sK1,sK1) != iProver_top
% 2.52/1.01      | m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK1,sK1))) != iProver_top
% 2.52/1.01      | v1_funct_1(k2_funct_2(sK1,sK2)) = iProver_top
% 2.52/1.01      | v1_funct_1(sK2) != iProver_top ),
% 2.52/1.01      inference(instantiation,[status(thm)],[c_695]) ).
% 2.52/1.01  
% 2.52/1.01  cnf(c_2294,plain,
% 2.52/1.01      ( v1_funct_1(k2_funct_2(sK1,sK2)) = iProver_top ),
% 2.52/1.01      inference(global_propositional_subsumption,
% 2.52/1.01                [status(thm)],
% 2.52/1.01                [c_2052,c_29,c_30,c_31,c_32,c_697]) ).
% 2.52/1.01  
% 2.52/1.01  cnf(c_2319,plain,
% 2.52/1.01      ( v1_funct_1(k2_funct_1(sK2)) = iProver_top ),
% 2.52/1.01      inference(demodulation,[status(thm)],[c_2316,c_2294]) ).
% 2.52/1.01  
% 2.52/1.01  cnf(c_5575,plain,
% 2.52/1.01      ( v1_funct_1(X0_50) != iProver_top
% 2.52/1.01      | m1_subset_1(X0_50,k1_zfmisc_1(k2_zfmisc_1(X0_51,X1_51))) != iProver_top
% 2.52/1.01      | k1_partfun1(sK1,sK1,X0_51,X1_51,k2_funct_1(sK2),X0_50) = k5_relat_1(k2_funct_1(sK2),X0_50) ),
% 2.52/1.01      inference(global_propositional_subsumption,
% 2.52/1.01                [status(thm)],
% 2.52/1.01                [c_4024,c_2319]) ).
% 2.52/1.01  
% 2.52/1.01  cnf(c_5576,plain,
% 2.52/1.01      ( k1_partfun1(sK1,sK1,X0_51,X1_51,k2_funct_1(sK2),X0_50) = k5_relat_1(k2_funct_1(sK2),X0_50)
% 2.52/1.01      | m1_subset_1(X0_50,k1_zfmisc_1(k2_zfmisc_1(X0_51,X1_51))) != iProver_top
% 2.52/1.01      | v1_funct_1(X0_50) != iProver_top ),
% 2.52/1.01      inference(renaming,[status(thm)],[c_5575]) ).
% 2.52/1.01  
% 2.52/1.01  cnf(c_5584,plain,
% 2.52/1.01      ( k1_partfun1(sK1,sK1,sK1,sK1,k2_funct_1(sK2),sK2) = k5_relat_1(k2_funct_1(sK2),sK2)
% 2.52/1.01      | v1_funct_1(sK2) != iProver_top ),
% 2.52/1.01      inference(superposition,[status(thm)],[c_1132,c_5576]) ).
% 2.52/1.01  
% 2.52/1.01  cnf(c_7,plain,
% 2.52/1.01      ( ~ v3_funct_2(X0,X1,X2)
% 2.52/1.01      | v2_funct_2(X0,X2)
% 2.52/1.01      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 2.52/1.01      | ~ v1_funct_1(X0) ),
% 2.52/1.01      inference(cnf_transformation,[],[f56]) ).
% 2.52/1.01  
% 2.52/1.01  cnf(c_11,plain,
% 2.52/1.01      ( ~ v2_funct_2(X0,X1)
% 2.52/1.01      | ~ v5_relat_1(X0,X1)
% 2.52/1.01      | ~ v1_relat_1(X0)
% 2.52/1.01      | k2_relat_1(X0) = X1 ),
% 2.52/1.01      inference(cnf_transformation,[],[f57]) ).
% 2.52/1.01  
% 2.52/1.01  cnf(c_320,plain,
% 2.52/1.01      ( ~ v3_funct_2(X0,X1,X2)
% 2.52/1.01      | ~ v5_relat_1(X3,X4)
% 2.52/1.01      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 2.52/1.01      | ~ v1_funct_1(X0)
% 2.52/1.01      | ~ v1_relat_1(X3)
% 2.52/1.01      | X3 != X0
% 2.52/1.01      | X4 != X2
% 2.52/1.01      | k2_relat_1(X3) = X4 ),
% 2.52/1.01      inference(resolution_lifted,[status(thm)],[c_7,c_11]) ).
% 2.52/1.01  
% 2.52/1.01  cnf(c_321,plain,
% 2.52/1.01      ( ~ v3_funct_2(X0,X1,X2)
% 2.52/1.01      | ~ v5_relat_1(X0,X2)
% 2.52/1.01      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 2.52/1.01      | ~ v1_funct_1(X0)
% 2.52/1.01      | ~ v1_relat_1(X0)
% 2.52/1.01      | k2_relat_1(X0) = X2 ),
% 2.52/1.01      inference(unflattening,[status(thm)],[c_320]) ).
% 2.52/1.01  
% 2.52/1.01  cnf(c_4,plain,
% 2.52/1.01      ( v5_relat_1(X0,X1)
% 2.52/1.01      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) ),
% 2.52/1.01      inference(cnf_transformation,[],[f51]) ).
% 2.52/1.01  
% 2.52/1.01  cnf(c_337,plain,
% 2.52/1.01      ( ~ v3_funct_2(X0,X1,X2)
% 2.52/1.01      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 2.52/1.01      | ~ v1_funct_1(X0)
% 2.52/1.01      | ~ v1_relat_1(X0)
% 2.52/1.01      | k2_relat_1(X0) = X2 ),
% 2.52/1.01      inference(forward_subsumption_resolution,[status(thm)],[c_321,c_4]) ).
% 2.52/1.01  
% 2.52/1.01  cnf(c_611,plain,
% 2.52/1.01      ( ~ v3_funct_2(X0_50,X0_51,X1_51)
% 2.52/1.01      | ~ m1_subset_1(X0_50,k1_zfmisc_1(k2_zfmisc_1(X0_51,X1_51)))
% 2.52/1.01      | ~ v1_funct_1(X0_50)
% 2.52/1.01      | ~ v1_relat_1(X0_50)
% 2.52/1.01      | k2_relat_1(X0_50) = X1_51 ),
% 2.52/1.01      inference(subtyping,[status(esa)],[c_337]) ).
% 2.52/1.01  
% 2.52/1.01  cnf(c_1136,plain,
% 2.52/1.01      ( k2_relat_1(X0_50) = X0_51
% 2.52/1.01      | v3_funct_2(X0_50,X1_51,X0_51) != iProver_top
% 2.52/1.01      | m1_subset_1(X0_50,k1_zfmisc_1(k2_zfmisc_1(X1_51,X0_51))) != iProver_top
% 2.52/1.01      | v1_funct_1(X0_50) != iProver_top
% 2.52/1.01      | v1_relat_1(X0_50) != iProver_top ),
% 2.52/1.01      inference(predicate_to_equality,[status(thm)],[c_611]) ).
% 2.52/1.01  
% 2.52/1.01  cnf(c_3508,plain,
% 2.52/1.01      ( k2_relat_1(sK2) = sK1
% 2.52/1.01      | v3_funct_2(sK2,sK1,sK1) != iProver_top
% 2.52/1.01      | v1_funct_1(sK2) != iProver_top
% 2.52/1.01      | v1_relat_1(sK2) != iProver_top ),
% 2.52/1.01      inference(superposition,[status(thm)],[c_1132,c_1136]) ).
% 2.52/1.01  
% 2.52/1.01  cnf(c_1,plain,
% 2.52/1.01      ( v1_relat_1(k2_zfmisc_1(X0,X1)) ),
% 2.52/1.01      inference(cnf_transformation,[],[f48]) ).
% 2.52/1.01  
% 2.52/1.01  cnf(c_99,plain,
% 2.52/1.01      ( v1_relat_1(k2_zfmisc_1(sK1,sK1)) ),
% 2.52/1.01      inference(instantiation,[status(thm)],[c_1]) ).
% 2.52/1.01  
% 2.52/1.01  cnf(c_717,plain,
% 2.52/1.01      ( ~ v3_funct_2(sK2,sK1,sK1)
% 2.52/1.01      | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK1,sK1)))
% 2.52/1.01      | ~ v1_funct_1(sK2)
% 2.52/1.01      | ~ v1_relat_1(sK2)
% 2.52/1.01      | k2_relat_1(sK2) = sK1 ),
% 2.52/1.01      inference(instantiation,[status(thm)],[c_611]) ).
% 2.52/1.01  
% 2.52/1.01  cnf(c_0,plain,
% 2.52/1.01      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
% 2.52/1.01      | ~ v1_relat_1(X1)
% 2.52/1.01      | v1_relat_1(X0) ),
% 2.52/1.01      inference(cnf_transformation,[],[f47]) ).
% 2.52/1.01  
% 2.52/1.01  cnf(c_634,plain,
% 2.52/1.01      ( ~ m1_subset_1(X0_50,k1_zfmisc_1(X1_50))
% 2.52/1.01      | ~ v1_relat_1(X1_50)
% 2.52/1.01      | v1_relat_1(X0_50) ),
% 2.52/1.01      inference(subtyping,[status(esa)],[c_0]) ).
% 2.52/1.01  
% 2.52/1.01  cnf(c_1331,plain,
% 2.52/1.01      ( ~ m1_subset_1(X0_50,k1_zfmisc_1(k2_zfmisc_1(X0_51,X1_51)))
% 2.52/1.01      | v1_relat_1(X0_50)
% 2.52/1.01      | ~ v1_relat_1(k2_zfmisc_1(X0_51,X1_51)) ),
% 2.52/1.01      inference(instantiation,[status(thm)],[c_634]) ).
% 2.52/1.01  
% 2.52/1.01  cnf(c_1333,plain,
% 2.52/1.01      ( ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK1,sK1)))
% 2.52/1.01      | ~ v1_relat_1(k2_zfmisc_1(sK1,sK1))
% 2.52/1.01      | v1_relat_1(sK2) ),
% 2.52/1.01      inference(instantiation,[status(thm)],[c_1331]) ).
% 2.52/1.01  
% 2.52/1.01  cnf(c_3900,plain,
% 2.52/1.01      ( k2_relat_1(sK2) = sK1 ),
% 2.52/1.01      inference(global_propositional_subsumption,
% 2.52/1.01                [status(thm)],
% 2.52/1.01                [c_3508,c_28,c_26,c_25,c_99,c_717,c_1333]) ).
% 2.52/1.01  
% 2.52/1.01  cnf(c_612,negated_conjecture,
% 2.52/1.01      ( v1_funct_1(sK2) ),
% 2.52/1.01      inference(subtyping,[status(esa)],[c_28]) ).
% 2.52/1.01  
% 2.52/1.01  cnf(c_1135,plain,
% 2.52/1.01      ( v1_funct_1(sK2) = iProver_top ),
% 2.52/1.01      inference(predicate_to_equality,[status(thm)],[c_612]) ).
% 2.52/1.01  
% 2.52/1.01  cnf(c_2,plain,
% 2.52/1.01      ( ~ v1_funct_1(X0)
% 2.52/1.01      | ~ v2_funct_1(X0)
% 2.52/1.01      | ~ v1_relat_1(X0)
% 2.52/1.01      | k5_relat_1(k2_funct_1(X0),X0) = k6_partfun1(k2_relat_1(X0)) ),
% 2.52/1.01      inference(cnf_transformation,[],[f77]) ).
% 2.52/1.01  
% 2.52/1.01  cnf(c_632,plain,
% 2.52/1.01      ( ~ v1_funct_1(X0_50)
% 2.52/1.01      | ~ v2_funct_1(X0_50)
% 2.52/1.01      | ~ v1_relat_1(X0_50)
% 2.52/1.01      | k5_relat_1(k2_funct_1(X0_50),X0_50) = k6_partfun1(k2_relat_1(X0_50)) ),
% 2.52/1.01      inference(subtyping,[status(esa)],[c_2]) ).
% 2.52/1.01  
% 2.52/1.01  cnf(c_1115,plain,
% 2.52/1.01      ( k5_relat_1(k2_funct_1(X0_50),X0_50) = k6_partfun1(k2_relat_1(X0_50))
% 2.52/1.01      | v1_funct_1(X0_50) != iProver_top
% 2.52/1.01      | v2_funct_1(X0_50) != iProver_top
% 2.52/1.01      | v1_relat_1(X0_50) != iProver_top ),
% 2.52/1.01      inference(predicate_to_equality,[status(thm)],[c_632]) ).
% 2.52/1.01  
% 2.52/1.01  cnf(c_1556,plain,
% 2.52/1.01      ( k5_relat_1(k2_funct_1(sK2),sK2) = k6_partfun1(k2_relat_1(sK2))
% 2.52/1.01      | v2_funct_1(sK2) != iProver_top
% 2.52/1.01      | v1_relat_1(sK2) != iProver_top ),
% 2.52/1.01      inference(superposition,[status(thm)],[c_1135,c_1115]) ).
% 2.52/1.01  
% 2.52/1.01  cnf(c_672,plain,
% 2.52/1.01      ( ~ v1_funct_1(sK2)
% 2.52/1.01      | ~ v2_funct_1(sK2)
% 2.52/1.01      | ~ v1_relat_1(sK2)
% 2.52/1.01      | k5_relat_1(k2_funct_1(sK2),sK2) = k6_partfun1(k2_relat_1(sK2)) ),
% 2.52/1.01      inference(instantiation,[status(thm)],[c_632]) ).
% 2.52/1.01  
% 2.52/1.01  cnf(c_8,plain,
% 2.52/1.01      ( ~ v3_funct_2(X0,X1,X2)
% 2.52/1.01      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 2.52/1.01      | ~ v1_funct_1(X0)
% 2.52/1.01      | v2_funct_1(X0) ),
% 2.52/1.01      inference(cnf_transformation,[],[f55]) ).
% 2.52/1.01  
% 2.52/1.01  cnf(c_628,plain,
% 2.52/1.01      ( ~ v3_funct_2(X0_50,X0_51,X1_51)
% 2.52/1.01      | ~ m1_subset_1(X0_50,k1_zfmisc_1(k2_zfmisc_1(X0_51,X1_51)))
% 2.52/1.01      | ~ v1_funct_1(X0_50)
% 2.52/1.01      | v2_funct_1(X0_50) ),
% 2.52/1.01      inference(subtyping,[status(esa)],[c_8]) ).
% 2.52/1.01  
% 2.52/1.01  cnf(c_684,plain,
% 2.52/1.01      ( ~ v3_funct_2(sK2,sK1,sK1)
% 2.52/1.01      | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK1,sK1)))
% 2.52/1.01      | ~ v1_funct_1(sK2)
% 2.52/1.01      | v2_funct_1(sK2) ),
% 2.52/1.01      inference(instantiation,[status(thm)],[c_628]) ).
% 2.52/1.01  
% 2.52/1.01  cnf(c_1648,plain,
% 2.52/1.01      ( k5_relat_1(k2_funct_1(sK2),sK2) = k6_partfun1(k2_relat_1(sK2)) ),
% 2.52/1.01      inference(global_propositional_subsumption,
% 2.52/1.01                [status(thm)],
% 2.52/1.01                [c_1556,c_28,c_26,c_25,c_99,c_672,c_684,c_1333]) ).
% 2.52/1.01  
% 2.52/1.01  cnf(c_3903,plain,
% 2.52/1.01      ( k5_relat_1(k2_funct_1(sK2),sK2) = k6_partfun1(sK1) ),
% 2.52/1.01      inference(demodulation,[status(thm)],[c_3900,c_1648]) ).
% 2.52/1.01  
% 2.52/1.01  cnf(c_5615,plain,
% 2.52/1.01      ( k1_partfun1(sK1,sK1,sK1,sK1,k2_funct_1(sK2),sK2) = k6_partfun1(sK1)
% 2.52/1.01      | v1_funct_1(sK2) != iProver_top ),
% 2.52/1.01      inference(light_normalisation,[status(thm)],[c_5584,c_3903]) ).
% 2.52/1.01  
% 2.52/1.01  cnf(c_5630,plain,
% 2.52/1.01      ( k1_partfun1(sK1,sK1,sK1,sK1,k2_funct_1(sK2),sK2) = k6_partfun1(sK1) ),
% 2.52/1.01      inference(global_propositional_subsumption,
% 2.52/1.01                [status(thm)],
% 2.52/1.01                [c_5615,c_29]) ).
% 2.52/1.01  
% 2.52/1.01  cnf(c_2981,plain,
% 2.52/1.01      ( k1_partfun1(sK1,sK1,X0_51,X1_51,sK2,X0_50) = k5_relat_1(sK2,X0_50)
% 2.52/1.01      | m1_subset_1(X0_50,k1_zfmisc_1(k2_zfmisc_1(X0_51,X1_51))) != iProver_top
% 2.52/1.01      | v1_funct_1(X0_50) != iProver_top
% 2.52/1.01      | v1_funct_1(sK2) != iProver_top ),
% 2.52/1.01      inference(superposition,[status(thm)],[c_1132,c_1128]) ).
% 2.52/1.01  
% 2.52/1.01  cnf(c_3129,plain,
% 2.52/1.01      ( v1_funct_1(X0_50) != iProver_top
% 2.52/1.01      | m1_subset_1(X0_50,k1_zfmisc_1(k2_zfmisc_1(X0_51,X1_51))) != iProver_top
% 2.52/1.01      | k1_partfun1(sK1,sK1,X0_51,X1_51,sK2,X0_50) = k5_relat_1(sK2,X0_50) ),
% 2.52/1.01      inference(global_propositional_subsumption,
% 2.52/1.01                [status(thm)],
% 2.52/1.01                [c_2981,c_29]) ).
% 2.52/1.01  
% 2.52/1.01  cnf(c_3130,plain,
% 2.52/1.01      ( k1_partfun1(sK1,sK1,X0_51,X1_51,sK2,X0_50) = k5_relat_1(sK2,X0_50)
% 2.52/1.01      | m1_subset_1(X0_50,k1_zfmisc_1(k2_zfmisc_1(X0_51,X1_51))) != iProver_top
% 2.52/1.01      | v1_funct_1(X0_50) != iProver_top ),
% 2.52/1.01      inference(renaming,[status(thm)],[c_3129]) ).
% 2.52/1.01  
% 2.52/1.01  cnf(c_3139,plain,
% 2.52/1.01      ( k1_partfun1(sK1,sK1,X0_51,X0_51,sK2,k2_funct_2(X0_51,X0_50)) = k5_relat_1(sK2,k2_funct_2(X0_51,X0_50))
% 2.52/1.01      | v1_funct_2(X0_50,X0_51,X0_51) != iProver_top
% 2.52/1.01      | v3_funct_2(X0_50,X0_51,X0_51) != iProver_top
% 2.52/1.01      | m1_subset_1(X0_50,k1_zfmisc_1(k2_zfmisc_1(X0_51,X0_51))) != iProver_top
% 2.52/1.01      | v1_funct_1(X0_50) != iProver_top
% 2.52/1.01      | v1_funct_1(k2_funct_2(X0_51,X0_50)) != iProver_top ),
% 2.52/1.01      inference(superposition,[status(thm)],[c_1120,c_3130]) ).
% 2.52/1.01  
% 2.52/1.01  cnf(c_4269,plain,
% 2.52/1.01      ( v1_funct_1(X0_50) != iProver_top
% 2.52/1.01      | m1_subset_1(X0_50,k1_zfmisc_1(k2_zfmisc_1(X0_51,X0_51))) != iProver_top
% 2.52/1.01      | v3_funct_2(X0_50,X0_51,X0_51) != iProver_top
% 2.52/1.01      | v1_funct_2(X0_50,X0_51,X0_51) != iProver_top
% 2.52/1.01      | k1_partfun1(sK1,sK1,X0_51,X0_51,sK2,k2_funct_2(X0_51,X0_50)) = k5_relat_1(sK2,k2_funct_2(X0_51,X0_50)) ),
% 2.52/1.01      inference(global_propositional_subsumption,
% 2.52/1.01                [status(thm)],
% 2.52/1.01                [c_3139,c_695]) ).
% 2.52/1.01  
% 2.52/1.01  cnf(c_4270,plain,
% 2.52/1.01      ( k1_partfun1(sK1,sK1,X0_51,X0_51,sK2,k2_funct_2(X0_51,X0_50)) = k5_relat_1(sK2,k2_funct_2(X0_51,X0_50))
% 2.52/1.01      | v1_funct_2(X0_50,X0_51,X0_51) != iProver_top
% 2.52/1.01      | v3_funct_2(X0_50,X0_51,X0_51) != iProver_top
% 2.52/1.01      | m1_subset_1(X0_50,k1_zfmisc_1(k2_zfmisc_1(X0_51,X0_51))) != iProver_top
% 2.52/1.01      | v1_funct_1(X0_50) != iProver_top ),
% 2.52/1.01      inference(renaming,[status(thm)],[c_4269]) ).
% 2.52/1.01  
% 2.52/1.01  cnf(c_4280,plain,
% 2.52/1.01      ( k1_partfun1(sK1,sK1,sK1,sK1,sK2,k2_funct_2(sK1,sK2)) = k5_relat_1(sK2,k2_funct_2(sK1,sK2))
% 2.52/1.01      | v1_funct_2(sK2,sK1,sK1) != iProver_top
% 2.52/1.01      | v3_funct_2(sK2,sK1,sK1) != iProver_top
% 2.52/1.01      | v1_funct_1(sK2) != iProver_top ),
% 2.52/1.01      inference(superposition,[status(thm)],[c_1132,c_4270]) ).
% 2.52/1.01  
% 2.52/1.01  cnf(c_23,plain,
% 2.52/1.01      ( ~ v1_funct_2(X0,X1,X1)
% 2.52/1.01      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X1)))
% 2.52/1.01      | ~ v1_funct_1(X0)
% 2.52/1.01      | k1_relset_1(X1,X1,X0) = X1 ),
% 2.52/1.01      inference(cnf_transformation,[],[f71]) ).
% 2.52/1.01  
% 2.52/1.01  cnf(c_617,plain,
% 2.52/1.01      ( ~ v1_funct_2(X0_50,X0_51,X0_51)
% 2.52/1.01      | ~ m1_subset_1(X0_50,k1_zfmisc_1(k2_zfmisc_1(X0_51,X0_51)))
% 2.52/1.01      | ~ v1_funct_1(X0_50)
% 2.52/1.01      | k1_relset_1(X0_51,X0_51,X0_50) = X0_51 ),
% 2.52/1.01      inference(subtyping,[status(esa)],[c_23]) ).
% 2.52/1.01  
% 2.52/1.01  cnf(c_1130,plain,
% 2.52/1.01      ( k1_relset_1(X0_51,X0_51,X0_50) = X0_51
% 2.52/1.01      | v1_funct_2(X0_50,X0_51,X0_51) != iProver_top
% 2.52/1.01      | m1_subset_1(X0_50,k1_zfmisc_1(k2_zfmisc_1(X0_51,X0_51))) != iProver_top
% 2.52/1.01      | v1_funct_1(X0_50) != iProver_top ),
% 2.52/1.01      inference(predicate_to_equality,[status(thm)],[c_617]) ).
% 2.52/1.01  
% 2.52/1.01  cnf(c_1971,plain,
% 2.52/1.01      ( k1_relset_1(sK1,sK1,sK2) = sK1
% 2.52/1.01      | v1_funct_2(sK2,sK1,sK1) != iProver_top
% 2.52/1.01      | v1_funct_1(sK2) != iProver_top ),
% 2.52/1.01      inference(superposition,[status(thm)],[c_1132,c_1130]) ).
% 2.52/1.01  
% 2.52/1.01  cnf(c_5,plain,
% 2.52/1.01      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 2.52/1.01      | k1_relset_1(X1,X2,X0) = k1_relat_1(X0) ),
% 2.52/1.01      inference(cnf_transformation,[],[f52]) ).
% 2.52/1.01  
% 2.52/1.01  cnf(c_630,plain,
% 2.52/1.01      ( ~ m1_subset_1(X0_50,k1_zfmisc_1(k2_zfmisc_1(X0_51,X1_51)))
% 2.52/1.01      | k1_relset_1(X0_51,X1_51,X0_50) = k1_relat_1(X0_50) ),
% 2.52/1.01      inference(subtyping,[status(esa)],[c_5]) ).
% 2.52/1.01  
% 2.52/1.01  cnf(c_1117,plain,
% 2.52/1.01      ( k1_relset_1(X0_51,X1_51,X0_50) = k1_relat_1(X0_50)
% 2.52/1.01      | m1_subset_1(X0_50,k1_zfmisc_1(k2_zfmisc_1(X0_51,X1_51))) != iProver_top ),
% 2.52/1.01      inference(predicate_to_equality,[status(thm)],[c_630]) ).
% 2.52/1.01  
% 2.52/1.01  cnf(c_1517,plain,
% 2.52/1.01      ( k1_relset_1(sK1,sK1,sK2) = k1_relat_1(sK2) ),
% 2.52/1.01      inference(superposition,[status(thm)],[c_1132,c_1117]) ).
% 2.52/1.01  
% 2.52/1.01  cnf(c_1991,plain,
% 2.52/1.01      ( k1_relat_1(sK2) = sK1
% 2.52/1.01      | v1_funct_2(sK2,sK1,sK1) != iProver_top
% 2.52/1.01      | v1_funct_1(sK2) != iProver_top ),
% 2.52/1.01      inference(demodulation,[status(thm)],[c_1971,c_1517]) ).
% 2.52/1.01  
% 2.52/1.01  cnf(c_2513,plain,
% 2.52/1.01      ( k1_relat_1(sK2) = sK1 ),
% 2.52/1.01      inference(global_propositional_subsumption,
% 2.52/1.01                [status(thm)],
% 2.52/1.01                [c_1991,c_29,c_30]) ).
% 2.52/1.01  
% 2.52/1.01  cnf(c_3,plain,
% 2.52/1.01      ( ~ v1_funct_1(X0)
% 2.52/1.01      | ~ v2_funct_1(X0)
% 2.52/1.01      | ~ v1_relat_1(X0)
% 2.52/1.01      | k5_relat_1(X0,k2_funct_1(X0)) = k6_partfun1(k1_relat_1(X0)) ),
% 2.52/1.01      inference(cnf_transformation,[],[f78]) ).
% 2.52/1.01  
% 2.52/1.01  cnf(c_631,plain,
% 2.52/1.01      ( ~ v1_funct_1(X0_50)
% 2.52/1.01      | ~ v2_funct_1(X0_50)
% 2.52/1.01      | ~ v1_relat_1(X0_50)
% 2.52/1.01      | k5_relat_1(X0_50,k2_funct_1(X0_50)) = k6_partfun1(k1_relat_1(X0_50)) ),
% 2.52/1.01      inference(subtyping,[status(esa)],[c_3]) ).
% 2.52/1.01  
% 2.52/1.01  cnf(c_1116,plain,
% 2.52/1.01      ( k5_relat_1(X0_50,k2_funct_1(X0_50)) = k6_partfun1(k1_relat_1(X0_50))
% 2.52/1.01      | v1_funct_1(X0_50) != iProver_top
% 2.52/1.01      | v2_funct_1(X0_50) != iProver_top
% 2.52/1.01      | v1_relat_1(X0_50) != iProver_top ),
% 2.52/1.01      inference(predicate_to_equality,[status(thm)],[c_631]) ).
% 2.52/1.01  
% 2.52/1.01  cnf(c_1774,plain,
% 2.52/1.01      ( k5_relat_1(sK2,k2_funct_1(sK2)) = k6_partfun1(k1_relat_1(sK2))
% 2.52/1.01      | v2_funct_1(sK2) != iProver_top
% 2.52/1.01      | v1_relat_1(sK2) != iProver_top ),
% 2.52/1.01      inference(superposition,[status(thm)],[c_1135,c_1116]) ).
% 2.52/1.01  
% 2.52/1.01  cnf(c_675,plain,
% 2.52/1.01      ( ~ v1_funct_1(sK2)
% 2.52/1.01      | ~ v2_funct_1(sK2)
% 2.52/1.01      | ~ v1_relat_1(sK2)
% 2.52/1.01      | k5_relat_1(sK2,k2_funct_1(sK2)) = k6_partfun1(k1_relat_1(sK2)) ),
% 2.52/1.01      inference(instantiation,[status(thm)],[c_631]) ).
% 2.52/1.01  
% 2.52/1.01  cnf(c_1864,plain,
% 2.52/1.01      ( k5_relat_1(sK2,k2_funct_1(sK2)) = k6_partfun1(k1_relat_1(sK2)) ),
% 2.52/1.01      inference(global_propositional_subsumption,
% 2.52/1.01                [status(thm)],
% 2.52/1.01                [c_1774,c_28,c_26,c_25,c_99,c_675,c_684,c_1333]) ).
% 2.52/1.01  
% 2.52/1.01  cnf(c_2516,plain,
% 2.52/1.01      ( k5_relat_1(sK2,k2_funct_1(sK2)) = k6_partfun1(sK1) ),
% 2.52/1.01      inference(demodulation,[status(thm)],[c_2513,c_1864]) ).
% 2.52/1.01  
% 2.52/1.01  cnf(c_4329,plain,
% 2.52/1.01      ( k1_partfun1(sK1,sK1,sK1,sK1,sK2,k2_funct_1(sK2)) = k6_partfun1(sK1)
% 2.52/1.01      | v1_funct_2(sK2,sK1,sK1) != iProver_top
% 2.52/1.01      | v3_funct_2(sK2,sK1,sK1) != iProver_top
% 2.52/1.01      | v1_funct_1(sK2) != iProver_top ),
% 2.52/1.01      inference(light_normalisation,[status(thm)],[c_4280,c_2316,c_2516]) ).
% 2.52/1.01  
% 2.52/1.01  cnf(c_4023,plain,
% 2.52/1.01      ( k1_partfun1(sK1,sK1,sK1,sK1,sK2,k2_funct_1(sK2)) = k5_relat_1(sK2,k2_funct_1(sK2))
% 2.52/1.01      | v1_funct_1(k2_funct_1(sK2)) != iProver_top ),
% 2.52/1.01      inference(superposition,[status(thm)],[c_4018,c_3130]) ).
% 2.52/1.01  
% 2.52/1.01  cnf(c_4114,plain,
% 2.52/1.01      ( k1_partfun1(sK1,sK1,sK1,sK1,sK2,k2_funct_1(sK2)) = k6_partfun1(sK1)
% 2.52/1.01      | v1_funct_1(k2_funct_1(sK2)) != iProver_top ),
% 2.52/1.01      inference(light_normalisation,[status(thm)],[c_4023,c_2516]) ).
% 2.52/1.01  
% 2.52/1.01  cnf(c_4346,plain,
% 2.52/1.01      ( k1_partfun1(sK1,sK1,sK1,sK1,sK2,k2_funct_1(sK2)) = k6_partfun1(sK1) ),
% 2.52/1.01      inference(global_propositional_subsumption,
% 2.52/1.01                [status(thm)],
% 2.52/1.01                [c_4329,c_2319,c_4114]) ).
% 2.52/1.01  
% 2.52/1.01  cnf(c_24,negated_conjecture,
% 2.52/1.01      ( ~ r2_relset_1(sK1,sK1,k1_partfun1(sK1,sK1,sK1,sK1,k2_funct_2(sK1,sK2),sK2),k6_partfun1(sK1))
% 2.52/1.01      | ~ r2_relset_1(sK1,sK1,k1_partfun1(sK1,sK1,sK1,sK1,sK2,k2_funct_2(sK1,sK2)),k6_partfun1(sK1)) ),
% 2.52/1.01      inference(cnf_transformation,[],[f76]) ).
% 2.52/1.01  
% 2.52/1.01  cnf(c_616,negated_conjecture,
% 2.52/1.01      ( ~ r2_relset_1(sK1,sK1,k1_partfun1(sK1,sK1,sK1,sK1,k2_funct_2(sK1,sK2),sK2),k6_partfun1(sK1))
% 2.52/1.01      | ~ r2_relset_1(sK1,sK1,k1_partfun1(sK1,sK1,sK1,sK1,sK2,k2_funct_2(sK1,sK2)),k6_partfun1(sK1)) ),
% 2.52/1.01      inference(subtyping,[status(esa)],[c_24]) ).
% 2.52/1.01  
% 2.52/1.01  cnf(c_1131,plain,
% 2.52/1.01      ( r2_relset_1(sK1,sK1,k1_partfun1(sK1,sK1,sK1,sK1,k2_funct_2(sK1,sK2),sK2),k6_partfun1(sK1)) != iProver_top
% 2.52/1.01      | r2_relset_1(sK1,sK1,k1_partfun1(sK1,sK1,sK1,sK1,sK2,k2_funct_2(sK1,sK2)),k6_partfun1(sK1)) != iProver_top ),
% 2.52/1.01      inference(predicate_to_equality,[status(thm)],[c_616]) ).
% 2.52/1.01  
% 2.52/1.01  cnf(c_2320,plain,
% 2.52/1.01      ( r2_relset_1(sK1,sK1,k1_partfun1(sK1,sK1,sK1,sK1,k2_funct_1(sK2),sK2),k6_partfun1(sK1)) != iProver_top
% 2.52/1.01      | r2_relset_1(sK1,sK1,k1_partfun1(sK1,sK1,sK1,sK1,sK2,k2_funct_1(sK2)),k6_partfun1(sK1)) != iProver_top ),
% 2.52/1.01      inference(demodulation,[status(thm)],[c_2316,c_1131]) ).
% 2.52/1.01  
% 2.52/1.01  cnf(c_4349,plain,
% 2.52/1.01      ( r2_relset_1(sK1,sK1,k1_partfun1(sK1,sK1,sK1,sK1,k2_funct_1(sK2),sK2),k6_partfun1(sK1)) != iProver_top
% 2.52/1.01      | r2_relset_1(sK1,sK1,k6_partfun1(sK1),k6_partfun1(sK1)) != iProver_top ),
% 2.52/1.01      inference(demodulation,[status(thm)],[c_4346,c_2320]) ).
% 2.52/1.01  
% 2.52/1.01  cnf(c_16,plain,
% 2.52/1.01      ( m1_subset_1(k6_partfun1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0))) ),
% 2.52/1.01      inference(cnf_transformation,[],[f63]) ).
% 2.52/1.01  
% 2.52/1.01  cnf(c_623,plain,
% 2.52/1.01      ( m1_subset_1(k6_partfun1(X0_51),k1_zfmisc_1(k2_zfmisc_1(X0_51,X0_51))) ),
% 2.52/1.01      inference(subtyping,[status(esa)],[c_16]) ).
% 2.52/1.01  
% 2.52/1.01  cnf(c_1124,plain,
% 2.52/1.01      ( m1_subset_1(k6_partfun1(X0_51),k1_zfmisc_1(k2_zfmisc_1(X0_51,X0_51))) = iProver_top ),
% 2.52/1.01      inference(predicate_to_equality,[status(thm)],[c_623]) ).
% 2.52/1.01  
% 2.52/1.01  cnf(c_6,plain,
% 2.52/1.01      ( r2_relset_1(X0,X1,X2,X2)
% 2.52/1.01      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
% 2.52/1.01      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ),
% 2.52/1.01      inference(cnf_transformation,[],[f53]) ).
% 2.52/1.01  
% 2.52/1.01  cnf(c_629,plain,
% 2.52/1.01      ( r2_relset_1(X0_51,X1_51,X0_50,X0_50)
% 2.52/1.01      | ~ m1_subset_1(X0_50,k1_zfmisc_1(k2_zfmisc_1(X0_51,X1_51)))
% 2.52/1.01      | ~ m1_subset_1(X1_50,k1_zfmisc_1(k2_zfmisc_1(X0_51,X1_51))) ),
% 2.52/1.01      inference(subtyping,[status(esa)],[c_6]) ).
% 2.52/1.01  
% 2.52/1.01  cnf(c_1118,plain,
% 2.52/1.01      ( r2_relset_1(X0_51,X1_51,X0_50,X0_50) = iProver_top
% 2.52/1.01      | m1_subset_1(X0_50,k1_zfmisc_1(k2_zfmisc_1(X0_51,X1_51))) != iProver_top
% 2.52/1.01      | m1_subset_1(X1_50,k1_zfmisc_1(k2_zfmisc_1(X0_51,X1_51))) != iProver_top ),
% 2.52/1.01      inference(predicate_to_equality,[status(thm)],[c_629]) ).
% 2.52/1.01  
% 2.52/1.01  cnf(c_1873,plain,
% 2.52/1.01      ( r2_relset_1(X0_51,X0_51,k6_partfun1(X0_51),k6_partfun1(X0_51)) = iProver_top
% 2.52/1.01      | m1_subset_1(X0_50,k1_zfmisc_1(k2_zfmisc_1(X0_51,X0_51))) != iProver_top ),
% 2.52/1.01      inference(superposition,[status(thm)],[c_1124,c_1118]) ).
% 2.52/1.01  
% 2.52/1.01  cnf(c_1891,plain,
% 2.52/1.01      ( r2_relset_1(sK1,sK1,k6_partfun1(sK1),k6_partfun1(sK1)) = iProver_top
% 2.52/1.01      | m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK1,sK1))) != iProver_top ),
% 2.52/1.01      inference(instantiation,[status(thm)],[c_1873]) ).
% 2.52/1.01  
% 2.52/1.01  cnf(c_4439,plain,
% 2.52/1.01      ( r2_relset_1(sK1,sK1,k1_partfun1(sK1,sK1,sK1,sK1,k2_funct_1(sK2),sK2),k6_partfun1(sK1)) != iProver_top ),
% 2.52/1.01      inference(global_propositional_subsumption,
% 2.52/1.01                [status(thm)],
% 2.52/1.01                [c_4349,c_32,c_1891]) ).
% 2.52/1.01  
% 2.52/1.01  cnf(c_5633,plain,
% 2.52/1.01      ( r2_relset_1(sK1,sK1,k6_partfun1(sK1),k6_partfun1(sK1)) != iProver_top ),
% 2.52/1.01      inference(demodulation,[status(thm)],[c_5630,c_4439]) ).
% 2.52/1.01  
% 2.52/1.01  cnf(contradiction,plain,
% 2.52/1.01      ( $false ),
% 2.52/1.01      inference(minisat,[status(thm)],[c_5633,c_1891,c_32]) ).
% 2.52/1.01  
% 2.52/1.01  
% 2.52/1.01  % SZS output end CNFRefutation for theBenchmark.p
% 2.52/1.01  
% 2.52/1.01  ------                               Statistics
% 2.52/1.01  
% 2.52/1.01  ------ General
% 2.52/1.01  
% 2.52/1.01  abstr_ref_over_cycles:                  0
% 2.52/1.01  abstr_ref_under_cycles:                 0
% 2.52/1.01  gc_basic_clause_elim:                   0
% 2.52/1.01  forced_gc_time:                         0
% 2.52/1.01  parsing_time:                           0.009
% 2.52/1.01  unif_index_cands_time:                  0.
% 2.52/1.01  unif_index_add_time:                    0.
% 2.52/1.01  orderings_time:                         0.
% 2.52/1.01  out_proof_time:                         0.012
% 2.52/1.01  total_time:                             0.173
% 2.52/1.01  num_of_symbols:                         56
% 2.52/1.01  num_of_terms:                           4949
% 2.52/1.01  
% 2.52/1.01  ------ Preprocessing
% 2.52/1.01  
% 2.52/1.01  num_of_splits:                          0
% 2.52/1.01  num_of_split_atoms:                     0
% 2.52/1.01  num_of_reused_defs:                     0
% 2.52/1.01  num_eq_ax_congr_red:                    28
% 2.52/1.01  num_of_sem_filtered_clauses:            1
% 2.52/1.01  num_of_subtypes:                        3
% 2.52/1.01  monotx_restored_types:                  1
% 2.52/1.01  sat_num_of_epr_types:                   0
% 2.52/1.01  sat_num_of_non_cyclic_types:            0
% 2.52/1.01  sat_guarded_non_collapsed_types:        0
% 2.52/1.01  num_pure_diseq_elim:                    0
% 2.52/1.01  simp_replaced_by:                       0
% 2.52/1.01  res_preprocessed:                       135
% 2.52/1.01  prep_upred:                             0
% 2.52/1.01  prep_unflattend:                        4
% 2.52/1.01  smt_new_axioms:                         0
% 2.52/1.01  pred_elim_cands:                        7
% 2.52/1.01  pred_elim:                              2
% 2.52/1.01  pred_elim_cl:                           4
% 2.52/1.01  pred_elim_cycles:                       4
% 2.52/1.01  merged_defs:                            0
% 2.52/1.01  merged_defs_ncl:                        0
% 2.52/1.01  bin_hyper_res:                          0
% 2.52/1.01  prep_cycles:                            4
% 2.52/1.01  pred_elim_time:                         0.002
% 2.52/1.01  splitting_time:                         0.
% 2.52/1.01  sem_filter_time:                        0.
% 2.52/1.01  monotx_time:                            0.
% 2.52/1.01  subtype_inf_time:                       0.001
% 2.52/1.01  
% 2.52/1.01  ------ Problem properties
% 2.52/1.01  
% 2.52/1.01  clauses:                                24
% 2.52/1.01  conjectures:                            5
% 2.52/1.01  epr:                                    3
% 2.52/1.01  horn:                                   24
% 2.52/1.01  ground:                                 5
% 2.52/1.01  unary:                                  9
% 2.52/1.01  binary:                                 2
% 2.52/1.01  lits:                                   70
% 2.52/1.01  lits_eq:                                7
% 2.52/1.01  fd_pure:                                0
% 2.52/1.01  fd_pseudo:                              0
% 2.52/1.01  fd_cond:                                0
% 2.52/1.01  fd_pseudo_cond:                         1
% 2.52/1.01  ac_symbols:                             0
% 2.52/1.01  
% 2.52/1.01  ------ Propositional Solver
% 2.52/1.01  
% 2.52/1.01  prop_solver_calls:                      31
% 2.52/1.01  prop_fast_solver_calls:                 1099
% 2.52/1.01  smt_solver_calls:                       0
% 2.52/1.01  smt_fast_solver_calls:                  0
% 2.52/1.01  prop_num_of_clauses:                    1594
% 2.52/1.01  prop_preprocess_simplified:             5795
% 2.52/1.01  prop_fo_subsumed:                       68
% 2.52/1.01  prop_solver_time:                       0.
% 2.52/1.01  smt_solver_time:                        0.
% 2.52/1.01  smt_fast_solver_time:                   0.
% 2.52/1.01  prop_fast_solver_time:                  0.
% 2.52/1.01  prop_unsat_core_time:                   0.
% 2.52/1.01  
% 2.52/1.01  ------ QBF
% 2.52/1.01  
% 2.52/1.01  qbf_q_res:                              0
% 2.52/1.01  qbf_num_tautologies:                    0
% 2.52/1.01  qbf_prep_cycles:                        0
% 2.52/1.01  
% 2.52/1.01  ------ BMC1
% 2.52/1.01  
% 2.52/1.01  bmc1_current_bound:                     -1
% 2.52/1.01  bmc1_last_solved_bound:                 -1
% 2.52/1.01  bmc1_unsat_core_size:                   -1
% 2.52/1.01  bmc1_unsat_core_parents_size:           -1
% 2.52/1.01  bmc1_merge_next_fun:                    0
% 2.52/1.01  bmc1_unsat_core_clauses_time:           0.
% 2.52/1.01  
% 2.52/1.01  ------ Instantiation
% 2.52/1.01  
% 2.52/1.01  inst_num_of_clauses:                    554
% 2.52/1.01  inst_num_in_passive:                    159
% 2.52/1.01  inst_num_in_active:                     358
% 2.52/1.01  inst_num_in_unprocessed:                37
% 2.52/1.01  inst_num_of_loops:                      390
% 2.52/1.01  inst_num_of_learning_restarts:          0
% 2.52/1.01  inst_num_moves_active_passive:          26
% 2.52/1.01  inst_lit_activity:                      0
% 2.52/1.01  inst_lit_activity_moves:                0
% 2.52/1.01  inst_num_tautologies:                   0
% 2.52/1.01  inst_num_prop_implied:                  0
% 2.52/1.01  inst_num_existing_simplified:           0
% 2.52/1.01  inst_num_eq_res_simplified:             0
% 2.52/1.01  inst_num_child_elim:                    0
% 2.52/1.01  inst_num_of_dismatching_blockings:      756
% 2.52/1.01  inst_num_of_non_proper_insts:           947
% 2.52/1.01  inst_num_of_duplicates:                 0
% 2.52/1.01  inst_inst_num_from_inst_to_res:         0
% 2.52/1.01  inst_dismatching_checking_time:         0.
% 2.52/1.01  
% 2.52/1.01  ------ Resolution
% 2.52/1.01  
% 2.52/1.01  res_num_of_clauses:                     0
% 2.52/1.01  res_num_in_passive:                     0
% 2.52/1.01  res_num_in_active:                      0
% 2.52/1.01  res_num_of_loops:                       139
% 2.52/1.01  res_forward_subset_subsumed:            145
% 2.52/1.01  res_backward_subset_subsumed:           4
% 2.52/1.01  res_forward_subsumed:                   0
% 2.52/1.01  res_backward_subsumed:                  0
% 2.52/1.01  res_forward_subsumption_resolution:     1
% 2.52/1.01  res_backward_subsumption_resolution:    0
% 2.52/1.01  res_clause_to_clause_subsumption:       200
% 2.52/1.01  res_orphan_elimination:                 0
% 2.52/1.01  res_tautology_del:                      123
% 2.52/1.01  res_num_eq_res_simplified:              0
% 2.52/1.01  res_num_sel_changes:                    0
% 2.52/1.01  res_moves_from_active_to_pass:          0
% 2.52/1.01  
% 2.52/1.01  ------ Superposition
% 2.52/1.01  
% 2.52/1.01  sup_time_total:                         0.
% 2.52/1.01  sup_time_generating:                    0.
% 2.52/1.01  sup_time_sim_full:                      0.
% 2.52/1.01  sup_time_sim_immed:                     0.
% 2.52/1.01  
% 2.52/1.01  sup_num_of_clauses:                     102
% 2.52/1.01  sup_num_in_active:                      66
% 2.52/1.01  sup_num_in_passive:                     36
% 2.52/1.01  sup_num_of_loops:                       77
% 2.52/1.01  sup_fw_superposition:                   62
% 2.52/1.01  sup_bw_superposition:                   28
% 2.52/1.01  sup_immediate_simplified:               19
% 2.52/1.01  sup_given_eliminated:                   0
% 2.52/1.01  comparisons_done:                       0
% 2.52/1.01  comparisons_avoided:                    0
% 2.52/1.01  
% 2.52/1.01  ------ Simplifications
% 2.52/1.01  
% 2.52/1.01  
% 2.52/1.01  sim_fw_subset_subsumed:                 1
% 2.52/1.01  sim_bw_subset_subsumed:                 7
% 2.52/1.01  sim_fw_subsumed:                        4
% 2.52/1.01  sim_bw_subsumed:                        1
% 2.52/1.01  sim_fw_subsumption_res:                 3
% 2.52/1.01  sim_bw_subsumption_res:                 0
% 2.52/1.01  sim_tautology_del:                      0
% 2.52/1.01  sim_eq_tautology_del:                   0
% 2.52/1.01  sim_eq_res_simp:                        0
% 2.52/1.01  sim_fw_demodulated:                     3
% 2.52/1.01  sim_bw_demodulated:                     10
% 2.52/1.01  sim_light_normalised:                   9
% 2.52/1.01  sim_joinable_taut:                      0
% 2.52/1.01  sim_joinable_simp:                      0
% 2.52/1.01  sim_ac_normalised:                      0
% 2.52/1.01  sim_smt_subsumption:                    0
% 2.52/1.01  
%------------------------------------------------------------------------------
