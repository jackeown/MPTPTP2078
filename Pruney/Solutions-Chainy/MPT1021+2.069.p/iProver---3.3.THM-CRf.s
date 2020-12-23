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
% DateTime   : Thu Dec  3 12:07:32 EST 2020

% Result     : Theorem 2.77s
% Output     : CNFRefutation 2.77s
% Verified   : 
% Statistics : Number of formulae       :  165 (1118 expanded)
%              Number of clauses        :   99 ( 336 expanded)
%              Number of leaves         :   16 ( 220 expanded)
%              Depth                    :   20
%              Number of atoms          :  546 (5265 expanded)
%              Number of equality atoms :  214 ( 558 expanded)
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

fof(f76,plain,(
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

fof(f70,plain,(
    ! [X0,X1] :
      ( k2_funct_1(X1) = k2_funct_2(X0,X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
      | ~ v3_funct_2(X1,X0,X0)
      | ~ v1_funct_2(X1,X0,X0)
      | ~ v1_funct_1(X1) ) ),
    inference(cnf_transformation,[],[f37])).

fof(f73,plain,(
    v1_funct_1(sK2) ),
    inference(cnf_transformation,[],[f46])).

fof(f74,plain,(
    v1_funct_2(sK2,sK1,sK1) ),
    inference(cnf_transformation,[],[f46])).

fof(f75,plain,(
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

fof(f69,plain,(
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

fof(f72,plain,(
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

fof(f49,plain,(
    ! [X0] :
      ( k5_relat_1(X0,k2_funct_1(X0)) = k6_relat_1(k1_relat_1(X0))
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f14,axiom,(
    ! [X0] : k6_relat_1(X0) = k6_partfun1(X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f71,plain,(
    ! [X0] : k6_relat_1(X0) = k6_partfun1(X0) ),
    inference(cnf_transformation,[],[f14])).

fof(f79,plain,(
    ! [X0] :
      ( k5_relat_1(X0,k2_funct_1(X0)) = k6_partfun1(k1_relat_1(X0))
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(definition_unfolding,[],[f49,f71])).

fof(f2,axiom,(
    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f48,plain,(
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

fof(f55,plain,(
    ! [X2,X0,X1] :
      ( v2_funct_1(X2)
      | ~ v3_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f29])).

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

fof(f50,plain,(
    ! [X0] :
      ( k5_relat_1(k2_funct_1(X0),X0) = k6_relat_1(k2_relat_1(X0))
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f78,plain,(
    ! [X0] :
      ( k5_relat_1(k2_funct_1(X0),X0) = k6_partfun1(k2_relat_1(X0))
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(definition_unfolding,[],[f50,f71])).

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

fof(f77,plain,
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

cnf(c_26,negated_conjecture,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK1,sK1))) ),
    inference(cnf_transformation,[],[f76])).

cnf(c_1093,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK1,sK1))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_26])).

cnf(c_23,plain,
    ( ~ v1_funct_2(X0,X1,X1)
    | ~ v3_funct_2(X0,X1,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X1)))
    | ~ v1_funct_1(X0)
    | k2_funct_2(X1,X0) = k2_funct_1(X0) ),
    inference(cnf_transformation,[],[f70])).

cnf(c_1096,plain,
    ( k2_funct_2(X0,X1) = k2_funct_1(X1)
    | v1_funct_2(X1,X0,X0) != iProver_top
    | v3_funct_2(X1,X0,X0) != iProver_top
    | m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) != iProver_top
    | v1_funct_1(X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_23])).

cnf(c_2401,plain,
    ( k2_funct_2(sK1,sK2) = k2_funct_1(sK2)
    | v1_funct_2(sK2,sK1,sK1) != iProver_top
    | v3_funct_2(sK2,sK1,sK1) != iProver_top
    | v1_funct_1(sK2) != iProver_top ),
    inference(superposition,[status(thm)],[c_1093,c_1096])).

cnf(c_29,negated_conjecture,
    ( v1_funct_1(sK2) ),
    inference(cnf_transformation,[],[f73])).

cnf(c_28,negated_conjecture,
    ( v1_funct_2(sK2,sK1,sK1) ),
    inference(cnf_transformation,[],[f74])).

cnf(c_27,negated_conjecture,
    ( v3_funct_2(sK2,sK1,sK1) ),
    inference(cnf_transformation,[],[f75])).

cnf(c_1459,plain,
    ( ~ v1_funct_2(sK2,X0,X0)
    | ~ v3_funct_2(sK2,X0,X0)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
    | ~ v1_funct_1(sK2)
    | k2_funct_2(X0,sK2) = k2_funct_1(sK2) ),
    inference(instantiation,[status(thm)],[c_23])).

cnf(c_1461,plain,
    ( ~ v1_funct_2(sK2,sK1,sK1)
    | ~ v3_funct_2(sK2,sK1,sK1)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK1,sK1)))
    | ~ v1_funct_1(sK2)
    | k2_funct_2(sK1,sK2) = k2_funct_1(sK2) ),
    inference(instantiation,[status(thm)],[c_1459])).

cnf(c_2815,plain,
    ( k2_funct_2(sK1,sK2) = k2_funct_1(sK2) ),
    inference(global_propositional_subsumption,[status(thm)],[c_2401,c_29,c_28,c_27,c_26,c_1461])).

cnf(c_12,plain,
    ( ~ v1_funct_2(X0,X1,X1)
    | ~ v3_funct_2(X0,X1,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X1)))
    | m1_subset_1(k2_funct_2(X1,X0),k1_zfmisc_1(k2_zfmisc_1(X1,X1)))
    | ~ v1_funct_1(X0) ),
    inference(cnf_transformation,[],[f62])).

cnf(c_1106,plain,
    ( v1_funct_2(X0,X1,X1) != iProver_top
    | v3_funct_2(X0,X1,X1) != iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X1))) != iProver_top
    | m1_subset_1(k2_funct_2(X1,X0),k1_zfmisc_1(k2_zfmisc_1(X1,X1))) = iProver_top
    | v1_funct_1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_12])).

cnf(c_3418,plain,
    ( v1_funct_2(sK2,sK1,sK1) != iProver_top
    | v3_funct_2(sK2,sK1,sK1) != iProver_top
    | m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK1))) = iProver_top
    | m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK1,sK1))) != iProver_top
    | v1_funct_1(sK2) != iProver_top ),
    inference(superposition,[status(thm)],[c_2815,c_1106])).

cnf(c_30,plain,
    ( v1_funct_1(sK2) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_29])).

cnf(c_31,plain,
    ( v1_funct_2(sK2,sK1,sK1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_28])).

cnf(c_32,plain,
    ( v3_funct_2(sK2,sK1,sK1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_27])).

cnf(c_33,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK1,sK1))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_26])).

cnf(c_4198,plain,
    ( m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK1))) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_3418,c_30,c_31,c_32,c_33])).

cnf(c_22,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X4,X5)))
    | ~ v1_funct_1(X0)
    | ~ v1_funct_1(X3)
    | k1_partfun1(X4,X5,X1,X2,X3,X0) = k5_relat_1(X3,X0) ),
    inference(cnf_transformation,[],[f69])).

cnf(c_1097,plain,
    ( k1_partfun1(X0,X1,X2,X3,X4,X5) = k5_relat_1(X4,X5)
    | m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) != iProver_top
    | m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top
    | v1_funct_1(X5) != iProver_top
    | v1_funct_1(X4) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_22])).

cnf(c_4212,plain,
    ( k1_partfun1(X0,X1,sK1,sK1,X2,k2_funct_1(sK2)) = k5_relat_1(X2,k2_funct_1(sK2))
    | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top
    | v1_funct_1(X2) != iProver_top
    | v1_funct_1(k2_funct_1(sK2)) != iProver_top ),
    inference(superposition,[status(thm)],[c_4198,c_1097])).

cnf(c_15,plain,
    ( ~ v1_funct_2(X0,X1,X1)
    | ~ v3_funct_2(X0,X1,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X1)))
    | ~ v1_funct_1(X0)
    | v1_funct_1(k2_funct_2(X1,X0)) ),
    inference(cnf_transformation,[],[f59])).

cnf(c_1103,plain,
    ( v1_funct_2(X0,X1,X1) != iProver_top
    | v3_funct_2(X0,X1,X1) != iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X1))) != iProver_top
    | v1_funct_1(X0) != iProver_top
    | v1_funct_1(k2_funct_2(X1,X0)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_15])).

cnf(c_3180,plain,
    ( v1_funct_2(sK2,sK1,sK1) != iProver_top
    | v3_funct_2(sK2,sK1,sK1) != iProver_top
    | v1_funct_1(k2_funct_2(sK1,sK2)) = iProver_top
    | v1_funct_1(sK2) != iProver_top ),
    inference(superposition,[status(thm)],[c_1093,c_1103])).

cnf(c_3185,plain,
    ( v1_funct_2(sK2,sK1,sK1) != iProver_top
    | v3_funct_2(sK2,sK1,sK1) != iProver_top
    | v1_funct_1(k2_funct_1(sK2)) = iProver_top
    | v1_funct_1(sK2) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_3180,c_2815])).

cnf(c_5626,plain,
    ( v1_funct_1(X2) != iProver_top
    | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top
    | k1_partfun1(X0,X1,sK1,sK1,X2,k2_funct_1(sK2)) = k5_relat_1(X2,k2_funct_1(sK2)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_4212,c_30,c_31,c_32,c_3185])).

cnf(c_5627,plain,
    ( k1_partfun1(X0,X1,sK1,sK1,X2,k2_funct_1(sK2)) = k5_relat_1(X2,k2_funct_1(sK2))
    | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top
    | v1_funct_1(X2) != iProver_top ),
    inference(renaming,[status(thm)],[c_5626])).

cnf(c_5638,plain,
    ( k1_partfun1(sK1,sK1,sK1,sK1,sK2,k2_funct_1(sK2)) = k5_relat_1(sK2,k2_funct_1(sK2))
    | v1_funct_1(sK2) != iProver_top ),
    inference(superposition,[status(thm)],[c_1093,c_5627])).

cnf(c_24,plain,
    ( ~ v1_funct_2(X0,X1,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X1)))
    | ~ v1_funct_1(X0)
    | k1_relset_1(X1,X1,X0) = X1 ),
    inference(cnf_transformation,[],[f72])).

cnf(c_1095,plain,
    ( k1_relset_1(X0,X0,X1) = X0
    | v1_funct_2(X1,X0,X0) != iProver_top
    | m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) != iProver_top
    | v1_funct_1(X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_24])).

cnf(c_2177,plain,
    ( k1_relset_1(sK1,sK1,sK2) = sK1
    | v1_funct_2(sK2,sK1,sK1) != iProver_top
    | v1_funct_1(sK2) != iProver_top ),
    inference(superposition,[status(thm)],[c_1093,c_1095])).

cnf(c_5,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k1_relset_1(X1,X2,X0) = k1_relat_1(X0) ),
    inference(cnf_transformation,[],[f52])).

cnf(c_1109,plain,
    ( k1_relset_1(X0,X1,X2) = k1_relat_1(X2)
    | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_5])).

cnf(c_1793,plain,
    ( k1_relset_1(sK1,sK1,sK2) = k1_relat_1(sK2) ),
    inference(superposition,[status(thm)],[c_1093,c_1109])).

cnf(c_2181,plain,
    ( k1_relat_1(sK2) = sK1
    | v1_funct_2(sK2,sK1,sK1) != iProver_top
    | v1_funct_1(sK2) != iProver_top ),
    inference(demodulation,[status(thm)],[c_2177,c_1793])).

cnf(c_2959,plain,
    ( k1_relat_1(sK2) = sK1 ),
    inference(global_propositional_subsumption,[status(thm)],[c_2181,c_30,c_31])).

cnf(c_1090,plain,
    ( v1_funct_1(sK2) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_29])).

cnf(c_3,plain,
    ( ~ v1_funct_1(X0)
    | ~ v2_funct_1(X0)
    | ~ v1_relat_1(X0)
    | k5_relat_1(X0,k2_funct_1(X0)) = k6_partfun1(k1_relat_1(X0)) ),
    inference(cnf_transformation,[],[f79])).

cnf(c_1110,plain,
    ( k5_relat_1(X0,k2_funct_1(X0)) = k6_partfun1(k1_relat_1(X0))
    | v1_funct_1(X0) != iProver_top
    | v2_funct_1(X0) != iProver_top
    | v1_relat_1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3])).

cnf(c_2153,plain,
    ( k5_relat_1(sK2,k2_funct_1(sK2)) = k6_partfun1(k1_relat_1(sK2))
    | v2_funct_1(sK2) != iProver_top
    | v1_relat_1(sK2) != iProver_top ),
    inference(superposition,[status(thm)],[c_1090,c_1110])).

cnf(c_1,plain,
    ( v1_relat_1(k2_zfmisc_1(X0,X1)) ),
    inference(cnf_transformation,[],[f48])).

cnf(c_103,plain,
    ( v1_relat_1(k2_zfmisc_1(sK1,sK1)) ),
    inference(instantiation,[status(thm)],[c_1])).

cnf(c_1344,plain,
    ( ~ v1_funct_1(sK2)
    | ~ v2_funct_1(sK2)
    | ~ v1_relat_1(sK2)
    | k5_relat_1(sK2,k2_funct_1(sK2)) = k6_partfun1(k1_relat_1(sK2)) ),
    inference(instantiation,[status(thm)],[c_3])).

cnf(c_8,plain,
    ( ~ v3_funct_2(X0,X1,X2)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ v1_funct_1(X0)
    | v2_funct_1(X0) ),
    inference(cnf_transformation,[],[f55])).

cnf(c_1365,plain,
    ( ~ v3_funct_2(sK2,X0,X1)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
    | ~ v1_funct_1(sK2)
    | v2_funct_1(sK2) ),
    inference(instantiation,[status(thm)],[c_8])).

cnf(c_1367,plain,
    ( ~ v3_funct_2(sK2,sK1,sK1)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK1,sK1)))
    | ~ v1_funct_1(sK2)
    | v2_funct_1(sK2) ),
    inference(instantiation,[status(thm)],[c_1365])).

cnf(c_0,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | ~ v1_relat_1(X1)
    | v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f47])).

cnf(c_1312,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | v1_relat_1(X0)
    | ~ v1_relat_1(k2_zfmisc_1(X1,X2)) ),
    inference(instantiation,[status(thm)],[c_0])).

cnf(c_1642,plain,
    ( ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK1,sK1)))
    | ~ v1_relat_1(k2_zfmisc_1(sK1,sK1))
    | v1_relat_1(sK2) ),
    inference(instantiation,[status(thm)],[c_1312])).

cnf(c_2811,plain,
    ( k5_relat_1(sK2,k2_funct_1(sK2)) = k6_partfun1(k1_relat_1(sK2)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_2153,c_29,c_27,c_26,c_103,c_1344,c_1367,c_1642])).

cnf(c_2962,plain,
    ( k5_relat_1(sK2,k2_funct_1(sK2)) = k6_partfun1(sK1) ),
    inference(demodulation,[status(thm)],[c_2959,c_2811])).

cnf(c_5646,plain,
    ( k1_partfun1(sK1,sK1,sK1,sK1,sK2,k2_funct_1(sK2)) = k6_partfun1(sK1)
    | v1_funct_1(sK2) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_5638,c_2962])).

cnf(c_5792,plain,
    ( k1_partfun1(sK1,sK1,sK1,sK1,sK2,k2_funct_1(sK2)) = k6_partfun1(sK1) ),
    inference(global_propositional_subsumption,[status(thm)],[c_5646,c_30])).

cnf(c_3138,plain,
    ( k1_partfun1(X0,X1,sK1,sK1,X2,sK2) = k5_relat_1(X2,sK2)
    | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top
    | v1_funct_1(X2) != iProver_top
    | v1_funct_1(sK2) != iProver_top ),
    inference(superposition,[status(thm)],[c_1093,c_1097])).

cnf(c_3633,plain,
    ( v1_funct_1(X2) != iProver_top
    | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top
    | k1_partfun1(X0,X1,sK1,sK1,X2,sK2) = k5_relat_1(X2,sK2) ),
    inference(global_propositional_subsumption,[status(thm)],[c_3138,c_30])).

cnf(c_3634,plain,
    ( k1_partfun1(X0,X1,sK1,sK1,X2,sK2) = k5_relat_1(X2,sK2)
    | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top
    | v1_funct_1(X2) != iProver_top ),
    inference(renaming,[status(thm)],[c_3633])).

cnf(c_3642,plain,
    ( k1_partfun1(X0,X0,sK1,sK1,k2_funct_2(X0,X1),sK2) = k5_relat_1(k2_funct_2(X0,X1),sK2)
    | v1_funct_2(X1,X0,X0) != iProver_top
    | v3_funct_2(X1,X0,X0) != iProver_top
    | m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) != iProver_top
    | v1_funct_1(X1) != iProver_top
    | v1_funct_1(k2_funct_2(X0,X1)) != iProver_top ),
    inference(superposition,[status(thm)],[c_1106,c_3634])).

cnf(c_4319,plain,
    ( k1_partfun1(X0,X0,sK1,sK1,k2_funct_2(X0,X1),sK2) = k5_relat_1(k2_funct_2(X0,X1),sK2)
    | v1_funct_2(X1,X0,X0) != iProver_top
    | v3_funct_2(X1,X0,X0) != iProver_top
    | m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) != iProver_top
    | v1_funct_1(X1) != iProver_top ),
    inference(forward_subsumption_resolution,[status(thm)],[c_3642,c_1103])).

cnf(c_4326,plain,
    ( k1_partfun1(sK1,sK1,sK1,sK1,k2_funct_2(sK1,sK2),sK2) = k5_relat_1(k2_funct_2(sK1,sK2),sK2)
    | v1_funct_2(sK2,sK1,sK1) != iProver_top
    | v3_funct_2(sK2,sK1,sK1) != iProver_top
    | v1_funct_1(sK2) != iProver_top ),
    inference(superposition,[status(thm)],[c_1093,c_4319])).

cnf(c_2,plain,
    ( ~ v1_funct_1(X0)
    | ~ v2_funct_1(X0)
    | ~ v1_relat_1(X0)
    | k5_relat_1(k2_funct_1(X0),X0) = k6_partfun1(k2_relat_1(X0)) ),
    inference(cnf_transformation,[],[f78])).

cnf(c_1111,plain,
    ( k5_relat_1(k2_funct_1(X0),X0) = k6_partfun1(k2_relat_1(X0))
    | v1_funct_1(X0) != iProver_top
    | v2_funct_1(X0) != iProver_top
    | v1_relat_1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2])).

cnf(c_2271,plain,
    ( k5_relat_1(k2_funct_1(sK2),sK2) = k6_partfun1(k2_relat_1(sK2))
    | v2_funct_1(sK2) != iProver_top
    | v1_relat_1(sK2) != iProver_top ),
    inference(superposition,[status(thm)],[c_1090,c_1111])).

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

cnf(c_331,plain,
    ( ~ v3_funct_2(X0,X1,X2)
    | ~ v5_relat_1(X3,X4)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ v1_funct_1(X0)
    | ~ v1_relat_1(X3)
    | X3 != X0
    | X4 != X2
    | k2_relat_1(X3) = X4 ),
    inference(resolution_lifted,[status(thm)],[c_7,c_11])).

cnf(c_332,plain,
    ( ~ v3_funct_2(X0,X1,X2)
    | ~ v5_relat_1(X0,X2)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ v1_funct_1(X0)
    | ~ v1_relat_1(X0)
    | k2_relat_1(X0) = X2 ),
    inference(unflattening,[status(thm)],[c_331])).

cnf(c_4,plain,
    ( v5_relat_1(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) ),
    inference(cnf_transformation,[],[f51])).

cnf(c_348,plain,
    ( ~ v3_funct_2(X0,X1,X2)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ v1_funct_1(X0)
    | ~ v1_relat_1(X0)
    | k2_relat_1(X0) = X2 ),
    inference(forward_subsumption_resolution,[status(thm)],[c_332,c_4])).

cnf(c_1089,plain,
    ( k2_relat_1(X0) = X1
    | v3_funct_2(X0,X2,X1) != iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) != iProver_top
    | v1_funct_1(X0) != iProver_top
    | v1_relat_1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_348])).

cnf(c_1551,plain,
    ( k2_relat_1(sK2) = sK1
    | v3_funct_2(sK2,sK1,sK1) != iProver_top
    | v1_funct_1(sK2) != iProver_top
    | v1_relat_1(sK2) != iProver_top ),
    inference(superposition,[status(thm)],[c_1093,c_1089])).

cnf(c_1552,plain,
    ( ~ v3_funct_2(sK2,sK1,sK1)
    | ~ v1_funct_1(sK2)
    | ~ v1_relat_1(sK2)
    | k2_relat_1(sK2) = sK1 ),
    inference(predicate_to_equality_rev,[status(thm)],[c_1551])).

cnf(c_1892,plain,
    ( k2_relat_1(sK2) = sK1 ),
    inference(global_propositional_subsumption,[status(thm)],[c_1551,c_29,c_27,c_26,c_103,c_1552,c_1642])).

cnf(c_2275,plain,
    ( k5_relat_1(k2_funct_1(sK2),sK2) = k6_partfun1(sK1)
    | v2_funct_1(sK2) != iProver_top
    | v1_relat_1(sK2) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_2271,c_1892])).

cnf(c_102,plain,
    ( v1_relat_1(k2_zfmisc_1(X0,X1)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1])).

cnf(c_104,plain,
    ( v1_relat_1(k2_zfmisc_1(sK1,sK1)) = iProver_top ),
    inference(instantiation,[status(thm)],[c_102])).

cnf(c_1366,plain,
    ( v3_funct_2(sK2,X0,X1) != iProver_top
    | m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top
    | v1_funct_1(sK2) != iProver_top
    | v2_funct_1(sK2) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1365])).

cnf(c_1368,plain,
    ( v3_funct_2(sK2,sK1,sK1) != iProver_top
    | m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK1,sK1))) != iProver_top
    | v1_funct_1(sK2) != iProver_top
    | v2_funct_1(sK2) = iProver_top ),
    inference(instantiation,[status(thm)],[c_1366])).

cnf(c_1643,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK1,sK1))) != iProver_top
    | v1_relat_1(k2_zfmisc_1(sK1,sK1)) != iProver_top
    | v1_relat_1(sK2) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1642])).

cnf(c_3722,plain,
    ( k5_relat_1(k2_funct_1(sK2),sK2) = k6_partfun1(sK1) ),
    inference(global_propositional_subsumption,[status(thm)],[c_2275,c_30,c_32,c_33,c_104,c_1368,c_1643])).

cnf(c_4340,plain,
    ( k1_partfun1(sK1,sK1,sK1,sK1,k2_funct_1(sK2),sK2) = k6_partfun1(sK1)
    | v1_funct_2(sK2,sK1,sK1) != iProver_top
    | v3_funct_2(sK2,sK1,sK1) != iProver_top
    | v1_funct_1(sK2) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_4326,c_2815,c_3722])).

cnf(c_4206,plain,
    ( k1_partfun1(sK1,sK1,sK1,sK1,k2_funct_1(sK2),sK2) = k5_relat_1(k2_funct_1(sK2),sK2)
    | v1_funct_1(k2_funct_1(sK2)) != iProver_top ),
    inference(superposition,[status(thm)],[c_4198,c_3634])).

cnf(c_4276,plain,
    ( k1_partfun1(sK1,sK1,sK1,sK1,k2_funct_1(sK2),sK2) = k6_partfun1(sK1)
    | v1_funct_1(k2_funct_1(sK2)) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_4206,c_3722])).

cnf(c_4462,plain,
    ( k1_partfun1(sK1,sK1,sK1,sK1,k2_funct_1(sK2),sK2) = k6_partfun1(sK1) ),
    inference(global_propositional_subsumption,[status(thm)],[c_4340,c_30,c_31,c_32,c_3185,c_4276])).

cnf(c_25,negated_conjecture,
    ( ~ r2_relset_1(sK1,sK1,k1_partfun1(sK1,sK1,sK1,sK1,k2_funct_2(sK1,sK2),sK2),k6_partfun1(sK1))
    | ~ r2_relset_1(sK1,sK1,k1_partfun1(sK1,sK1,sK1,sK1,sK2,k2_funct_2(sK1,sK2)),k6_partfun1(sK1)) ),
    inference(cnf_transformation,[],[f77])).

cnf(c_1094,plain,
    ( r2_relset_1(sK1,sK1,k1_partfun1(sK1,sK1,sK1,sK1,k2_funct_2(sK1,sK2),sK2),k6_partfun1(sK1)) != iProver_top
    | r2_relset_1(sK1,sK1,k1_partfun1(sK1,sK1,sK1,sK1,sK2,k2_funct_2(sK1,sK2)),k6_partfun1(sK1)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_25])).

cnf(c_2818,plain,
    ( r2_relset_1(sK1,sK1,k1_partfun1(sK1,sK1,sK1,sK1,k2_funct_1(sK2),sK2),k6_partfun1(sK1)) != iProver_top
    | r2_relset_1(sK1,sK1,k1_partfun1(sK1,sK1,sK1,sK1,sK2,k2_funct_1(sK2)),k6_partfun1(sK1)) != iProver_top ),
    inference(demodulation,[status(thm)],[c_2815,c_1094])).

cnf(c_4465,plain,
    ( r2_relset_1(sK1,sK1,k1_partfun1(sK1,sK1,sK1,sK1,sK2,k2_funct_1(sK2)),k6_partfun1(sK1)) != iProver_top
    | r2_relset_1(sK1,sK1,k6_partfun1(sK1),k6_partfun1(sK1)) != iProver_top ),
    inference(demodulation,[status(thm)],[c_4462,c_2818])).

cnf(c_16,plain,
    ( m1_subset_1(k6_partfun1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0))) ),
    inference(cnf_transformation,[],[f63])).

cnf(c_59,plain,
    ( m1_subset_1(k6_partfun1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_16])).

cnf(c_61,plain,
    ( m1_subset_1(k6_partfun1(sK1),k1_zfmisc_1(k2_zfmisc_1(sK1,sK1))) = iProver_top ),
    inference(instantiation,[status(thm)],[c_59])).

cnf(c_6,plain,
    ( r2_relset_1(X0,X1,X2,X2)
    | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ),
    inference(cnf_transformation,[],[f53])).

cnf(c_1389,plain,
    ( r2_relset_1(X0,X0,k6_partfun1(X0),k6_partfun1(X0))
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
    | ~ m1_subset_1(k6_partfun1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0))) ),
    inference(instantiation,[status(thm)],[c_6])).

cnf(c_1774,plain,
    ( r2_relset_1(X0,X0,k6_partfun1(X0),k6_partfun1(X0))
    | ~ m1_subset_1(k6_partfun1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0))) ),
    inference(instantiation,[status(thm)],[c_1389])).

cnf(c_1775,plain,
    ( r2_relset_1(X0,X0,k6_partfun1(X0),k6_partfun1(X0)) = iProver_top
    | m1_subset_1(k6_partfun1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1774])).

cnf(c_1777,plain,
    ( r2_relset_1(sK1,sK1,k6_partfun1(sK1),k6_partfun1(sK1)) = iProver_top
    | m1_subset_1(k6_partfun1(sK1),k1_zfmisc_1(k2_zfmisc_1(sK1,sK1))) != iProver_top ),
    inference(instantiation,[status(thm)],[c_1775])).

cnf(c_4468,plain,
    ( r2_relset_1(sK1,sK1,k1_partfun1(sK1,sK1,sK1,sK1,sK2,k2_funct_1(sK2)),k6_partfun1(sK1)) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_4465,c_61,c_1777])).

cnf(c_5795,plain,
    ( r2_relset_1(sK1,sK1,k6_partfun1(sK1),k6_partfun1(sK1)) != iProver_top ),
    inference(demodulation,[status(thm)],[c_5792,c_4468])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_5795,c_1777,c_61])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.13  % Command    : iproveropt_run.sh %d %s
% 0.13/0.34  % Computer   : n008.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 11:46:30 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running in FOF mode
% 2.77/0.98  % SZS status Started for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.77/0.98  
% 2.77/0.98  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 2.77/0.98  
% 2.77/0.98  ------  iProver source info
% 2.77/0.98  
% 2.77/0.98  git: date: 2020-06-30 10:37:57 +0100
% 2.77/0.98  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 2.77/0.98  git: non_committed_changes: false
% 2.77/0.98  git: last_make_outside_of_git: false
% 2.77/0.98  
% 2.77/0.98  ------ 
% 2.77/0.98  
% 2.77/0.98  ------ Input Options
% 2.77/0.98  
% 2.77/0.98  --out_options                           all
% 2.77/0.98  --tptp_safe_out                         true
% 2.77/0.98  --problem_path                          ""
% 2.77/0.98  --include_path                          ""
% 2.77/0.98  --clausifier                            res/vclausify_rel
% 2.77/0.98  --clausifier_options                    --mode clausify
% 2.77/0.98  --stdin                                 false
% 2.77/0.98  --stats_out                             all
% 2.77/0.98  
% 2.77/0.98  ------ General Options
% 2.77/0.98  
% 2.77/0.98  --fof                                   false
% 2.77/0.98  --time_out_real                         305.
% 2.77/0.98  --time_out_virtual                      -1.
% 2.77/0.98  --symbol_type_check                     false
% 2.77/0.98  --clausify_out                          false
% 2.77/0.98  --sig_cnt_out                           false
% 2.77/0.98  --trig_cnt_out                          false
% 2.77/0.98  --trig_cnt_out_tolerance                1.
% 2.77/0.98  --trig_cnt_out_sk_spl                   false
% 2.77/0.98  --abstr_cl_out                          false
% 2.77/0.98  
% 2.77/0.98  ------ Global Options
% 2.77/0.98  
% 2.77/0.98  --schedule                              default
% 2.77/0.98  --add_important_lit                     false
% 2.77/0.98  --prop_solver_per_cl                    1000
% 2.77/0.98  --min_unsat_core                        false
% 2.77/0.98  --soft_assumptions                      false
% 2.77/0.98  --soft_lemma_size                       3
% 2.77/0.98  --prop_impl_unit_size                   0
% 2.77/0.98  --prop_impl_unit                        []
% 2.77/0.98  --share_sel_clauses                     true
% 2.77/0.98  --reset_solvers                         false
% 2.77/0.98  --bc_imp_inh                            [conj_cone]
% 2.77/0.98  --conj_cone_tolerance                   3.
% 2.77/0.98  --extra_neg_conj                        none
% 2.77/0.98  --large_theory_mode                     true
% 2.77/0.98  --prolific_symb_bound                   200
% 2.77/0.98  --lt_threshold                          2000
% 2.77/0.98  --clause_weak_htbl                      true
% 2.77/0.98  --gc_record_bc_elim                     false
% 2.77/0.98  
% 2.77/0.98  ------ Preprocessing Options
% 2.77/0.98  
% 2.77/0.98  --preprocessing_flag                    true
% 2.77/0.98  --time_out_prep_mult                    0.1
% 2.77/0.98  --splitting_mode                        input
% 2.77/0.98  --splitting_grd                         true
% 2.77/0.98  --splitting_cvd                         false
% 2.77/0.98  --splitting_cvd_svl                     false
% 2.77/0.98  --splitting_nvd                         32
% 2.77/0.98  --sub_typing                            true
% 2.77/0.98  --prep_gs_sim                           true
% 2.77/0.98  --prep_unflatten                        true
% 2.77/0.98  --prep_res_sim                          true
% 2.77/0.98  --prep_upred                            true
% 2.77/0.98  --prep_sem_filter                       exhaustive
% 2.77/0.98  --prep_sem_filter_out                   false
% 2.77/0.98  --pred_elim                             true
% 2.77/0.98  --res_sim_input                         true
% 2.77/0.98  --eq_ax_congr_red                       true
% 2.77/0.98  --pure_diseq_elim                       true
% 2.77/0.98  --brand_transform                       false
% 2.77/0.98  --non_eq_to_eq                          false
% 2.77/0.98  --prep_def_merge                        true
% 2.77/0.98  --prep_def_merge_prop_impl              false
% 2.77/0.98  --prep_def_merge_mbd                    true
% 2.77/0.98  --prep_def_merge_tr_red                 false
% 2.77/0.98  --prep_def_merge_tr_cl                  false
% 2.77/0.98  --smt_preprocessing                     true
% 2.77/0.98  --smt_ac_axioms                         fast
% 2.77/0.98  --preprocessed_out                      false
% 2.77/0.98  --preprocessed_stats                    false
% 2.77/0.98  
% 2.77/0.98  ------ Abstraction refinement Options
% 2.77/0.98  
% 2.77/0.98  --abstr_ref                             []
% 2.77/0.98  --abstr_ref_prep                        false
% 2.77/0.98  --abstr_ref_until_sat                   false
% 2.77/0.98  --abstr_ref_sig_restrict                funpre
% 2.77/0.98  --abstr_ref_af_restrict_to_split_sk     false
% 2.77/0.98  --abstr_ref_under                       []
% 2.77/0.98  
% 2.77/0.98  ------ SAT Options
% 2.77/0.98  
% 2.77/0.98  --sat_mode                              false
% 2.77/0.98  --sat_fm_restart_options                ""
% 2.77/0.98  --sat_gr_def                            false
% 2.77/0.98  --sat_epr_types                         true
% 2.77/0.98  --sat_non_cyclic_types                  false
% 2.77/0.98  --sat_finite_models                     false
% 2.77/0.98  --sat_fm_lemmas                         false
% 2.77/0.98  --sat_fm_prep                           false
% 2.77/0.98  --sat_fm_uc_incr                        true
% 2.77/0.98  --sat_out_model                         small
% 2.77/0.98  --sat_out_clauses                       false
% 2.77/0.98  
% 2.77/0.98  ------ QBF Options
% 2.77/0.98  
% 2.77/0.98  --qbf_mode                              false
% 2.77/0.98  --qbf_elim_univ                         false
% 2.77/0.98  --qbf_dom_inst                          none
% 2.77/0.98  --qbf_dom_pre_inst                      false
% 2.77/0.98  --qbf_sk_in                             false
% 2.77/0.98  --qbf_pred_elim                         true
% 2.77/0.98  --qbf_split                             512
% 2.77/0.98  
% 2.77/0.98  ------ BMC1 Options
% 2.77/0.98  
% 2.77/0.98  --bmc1_incremental                      false
% 2.77/0.98  --bmc1_axioms                           reachable_all
% 2.77/0.98  --bmc1_min_bound                        0
% 2.77/0.98  --bmc1_max_bound                        -1
% 2.77/0.98  --bmc1_max_bound_default                -1
% 2.77/0.98  --bmc1_symbol_reachability              true
% 2.77/0.98  --bmc1_property_lemmas                  false
% 2.77/0.98  --bmc1_k_induction                      false
% 2.77/0.98  --bmc1_non_equiv_states                 false
% 2.77/0.98  --bmc1_deadlock                         false
% 2.77/0.98  --bmc1_ucm                              false
% 2.77/0.98  --bmc1_add_unsat_core                   none
% 2.77/0.98  --bmc1_unsat_core_children              false
% 2.77/0.98  --bmc1_unsat_core_extrapolate_axioms    false
% 2.77/0.98  --bmc1_out_stat                         full
% 2.77/0.98  --bmc1_ground_init                      false
% 2.77/0.98  --bmc1_pre_inst_next_state              false
% 2.77/0.98  --bmc1_pre_inst_state                   false
% 2.77/0.98  --bmc1_pre_inst_reach_state             false
% 2.77/0.98  --bmc1_out_unsat_core                   false
% 2.77/0.98  --bmc1_aig_witness_out                  false
% 2.77/0.98  --bmc1_verbose                          false
% 2.77/0.98  --bmc1_dump_clauses_tptp                false
% 2.77/0.98  --bmc1_dump_unsat_core_tptp             false
% 2.77/0.98  --bmc1_dump_file                        -
% 2.77/0.98  --bmc1_ucm_expand_uc_limit              128
% 2.77/0.98  --bmc1_ucm_n_expand_iterations          6
% 2.77/0.98  --bmc1_ucm_extend_mode                  1
% 2.77/0.98  --bmc1_ucm_init_mode                    2
% 2.77/0.98  --bmc1_ucm_cone_mode                    none
% 2.77/0.98  --bmc1_ucm_reduced_relation_type        0
% 2.77/0.98  --bmc1_ucm_relax_model                  4
% 2.77/0.98  --bmc1_ucm_full_tr_after_sat            true
% 2.77/0.98  --bmc1_ucm_expand_neg_assumptions       false
% 2.77/0.98  --bmc1_ucm_layered_model                none
% 2.77/0.98  --bmc1_ucm_max_lemma_size               10
% 2.77/0.98  
% 2.77/0.98  ------ AIG Options
% 2.77/0.98  
% 2.77/0.98  --aig_mode                              false
% 2.77/0.98  
% 2.77/0.98  ------ Instantiation Options
% 2.77/0.98  
% 2.77/0.98  --instantiation_flag                    true
% 2.77/0.98  --inst_sos_flag                         false
% 2.77/0.98  --inst_sos_phase                        true
% 2.77/0.98  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 2.77/0.98  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 2.77/0.98  --inst_lit_sel_side                     num_symb
% 2.77/0.98  --inst_solver_per_active                1400
% 2.77/0.98  --inst_solver_calls_frac                1.
% 2.77/0.98  --inst_passive_queue_type               priority_queues
% 2.77/0.98  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 2.77/0.98  --inst_passive_queues_freq              [25;2]
% 2.77/0.98  --inst_dismatching                      true
% 2.77/0.98  --inst_eager_unprocessed_to_passive     true
% 2.77/0.98  --inst_prop_sim_given                   true
% 2.77/0.98  --inst_prop_sim_new                     false
% 2.77/0.98  --inst_subs_new                         false
% 2.77/0.98  --inst_eq_res_simp                      false
% 2.77/0.98  --inst_subs_given                       false
% 2.77/0.98  --inst_orphan_elimination               true
% 2.77/0.98  --inst_learning_loop_flag               true
% 2.77/0.98  --inst_learning_start                   3000
% 2.77/0.98  --inst_learning_factor                  2
% 2.77/0.98  --inst_start_prop_sim_after_learn       3
% 2.77/0.98  --inst_sel_renew                        solver
% 2.77/0.98  --inst_lit_activity_flag                true
% 2.77/0.98  --inst_restr_to_given                   false
% 2.77/0.98  --inst_activity_threshold               500
% 2.77/0.98  --inst_out_proof                        true
% 2.77/0.98  
% 2.77/0.98  ------ Resolution Options
% 2.77/0.98  
% 2.77/0.98  --resolution_flag                       true
% 2.77/0.98  --res_lit_sel                           adaptive
% 2.77/0.98  --res_lit_sel_side                      none
% 2.77/0.98  --res_ordering                          kbo
% 2.77/0.98  --res_to_prop_solver                    active
% 2.77/0.98  --res_prop_simpl_new                    false
% 2.77/0.98  --res_prop_simpl_given                  true
% 2.77/0.98  --res_passive_queue_type                priority_queues
% 2.77/0.98  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 2.77/0.98  --res_passive_queues_freq               [15;5]
% 2.77/0.98  --res_forward_subs                      full
% 2.77/0.98  --res_backward_subs                     full
% 2.77/0.98  --res_forward_subs_resolution           true
% 2.77/0.98  --res_backward_subs_resolution          true
% 2.77/0.98  --res_orphan_elimination                true
% 2.77/0.98  --res_time_limit                        2.
% 2.77/0.98  --res_out_proof                         true
% 2.77/0.98  
% 2.77/0.98  ------ Superposition Options
% 2.77/0.98  
% 2.77/0.98  --superposition_flag                    true
% 2.77/0.98  --sup_passive_queue_type                priority_queues
% 2.77/0.98  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 2.77/0.98  --sup_passive_queues_freq               [8;1;4]
% 2.77/0.98  --demod_completeness_check              fast
% 2.77/0.98  --demod_use_ground                      true
% 2.77/0.98  --sup_to_prop_solver                    passive
% 2.77/0.98  --sup_prop_simpl_new                    true
% 2.77/0.98  --sup_prop_simpl_given                  true
% 2.77/0.98  --sup_fun_splitting                     false
% 2.77/0.98  --sup_smt_interval                      50000
% 2.77/0.98  
% 2.77/0.98  ------ Superposition Simplification Setup
% 2.77/0.98  
% 2.77/0.98  --sup_indices_passive                   []
% 2.77/0.98  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.77/0.98  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.77/0.98  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.77/0.98  --sup_full_triv                         [TrivRules;PropSubs]
% 2.77/0.98  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.77/0.98  --sup_full_bw                           [BwDemod]
% 2.77/0.98  --sup_immed_triv                        [TrivRules]
% 2.77/0.98  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 2.77/0.98  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.77/0.98  --sup_immed_bw_main                     []
% 2.77/0.98  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.77/0.98  --sup_input_triv                        [Unflattening;TrivRules]
% 2.77/0.98  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.77/0.98  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.77/0.98  
% 2.77/0.98  ------ Combination Options
% 2.77/0.98  
% 2.77/0.98  --comb_res_mult                         3
% 2.77/0.98  --comb_sup_mult                         2
% 2.77/0.98  --comb_inst_mult                        10
% 2.77/0.98  
% 2.77/0.98  ------ Debug Options
% 2.77/0.98  
% 2.77/0.98  --dbg_backtrace                         false
% 2.77/0.98  --dbg_dump_prop_clauses                 false
% 2.77/0.98  --dbg_dump_prop_clauses_file            -
% 2.77/0.98  --dbg_out_stat                          false
% 2.77/0.98  ------ Parsing...
% 2.77/0.98  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 2.77/0.98  
% 2.77/0.98  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe:1:0s pe:2:0s pe_e  sf_s  rm: 3 0s  sf_e  pe_s  pe_e 
% 2.77/0.98  
% 2.77/0.98  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 2.77/0.98  
% 2.77/0.98  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 2.77/0.98  ------ Proving...
% 2.77/0.98  ------ Problem Properties 
% 2.77/0.98  
% 2.77/0.98  
% 2.77/0.98  clauses                                 25
% 2.77/0.98  conjectures                             5
% 2.77/0.98  EPR                                     3
% 2.77/0.98  Horn                                    25
% 2.77/0.98  unary                                   10
% 2.77/0.98  binary                                  2
% 2.77/0.98  lits                                    71
% 2.77/0.98  lits eq                                 7
% 2.77/0.98  fd_pure                                 0
% 2.77/0.98  fd_pseudo                               0
% 2.77/0.98  fd_cond                                 0
% 2.77/0.98  fd_pseudo_cond                          1
% 2.77/0.98  AC symbols                              0
% 2.77/0.98  
% 2.77/0.98  ------ Schedule dynamic 5 is on 
% 2.77/0.98  
% 2.77/0.98  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" Time Limit: 10.
% 2.77/0.98  
% 2.77/0.98  
% 2.77/0.98  ------ 
% 2.77/0.98  Current options:
% 2.77/0.98  ------ 
% 2.77/0.98  
% 2.77/0.98  ------ Input Options
% 2.77/0.98  
% 2.77/0.98  --out_options                           all
% 2.77/0.98  --tptp_safe_out                         true
% 2.77/0.98  --problem_path                          ""
% 2.77/0.98  --include_path                          ""
% 2.77/0.98  --clausifier                            res/vclausify_rel
% 2.77/0.98  --clausifier_options                    --mode clausify
% 2.77/0.98  --stdin                                 false
% 2.77/0.98  --stats_out                             all
% 2.77/0.98  
% 2.77/0.98  ------ General Options
% 2.77/0.98  
% 2.77/0.98  --fof                                   false
% 2.77/0.98  --time_out_real                         305.
% 2.77/0.98  --time_out_virtual                      -1.
% 2.77/0.98  --symbol_type_check                     false
% 2.77/0.98  --clausify_out                          false
% 2.77/0.98  --sig_cnt_out                           false
% 2.77/0.98  --trig_cnt_out                          false
% 2.77/0.98  --trig_cnt_out_tolerance                1.
% 2.77/0.98  --trig_cnt_out_sk_spl                   false
% 2.77/0.98  --abstr_cl_out                          false
% 2.77/0.98  
% 2.77/0.98  ------ Global Options
% 2.77/0.98  
% 2.77/0.98  --schedule                              default
% 2.77/0.98  --add_important_lit                     false
% 2.77/0.98  --prop_solver_per_cl                    1000
% 2.77/0.98  --min_unsat_core                        false
% 2.77/0.98  --soft_assumptions                      false
% 2.77/0.98  --soft_lemma_size                       3
% 2.77/0.98  --prop_impl_unit_size                   0
% 2.77/0.98  --prop_impl_unit                        []
% 2.77/0.98  --share_sel_clauses                     true
% 2.77/0.98  --reset_solvers                         false
% 2.77/0.98  --bc_imp_inh                            [conj_cone]
% 2.77/0.98  --conj_cone_tolerance                   3.
% 2.77/0.98  --extra_neg_conj                        none
% 2.77/0.98  --large_theory_mode                     true
% 2.77/0.98  --prolific_symb_bound                   200
% 2.77/0.98  --lt_threshold                          2000
% 2.77/0.98  --clause_weak_htbl                      true
% 2.77/0.98  --gc_record_bc_elim                     false
% 2.77/0.98  
% 2.77/0.98  ------ Preprocessing Options
% 2.77/0.98  
% 2.77/0.98  --preprocessing_flag                    true
% 2.77/0.98  --time_out_prep_mult                    0.1
% 2.77/0.98  --splitting_mode                        input
% 2.77/0.98  --splitting_grd                         true
% 2.77/0.98  --splitting_cvd                         false
% 2.77/0.98  --splitting_cvd_svl                     false
% 2.77/0.98  --splitting_nvd                         32
% 2.77/0.98  --sub_typing                            true
% 2.77/0.98  --prep_gs_sim                           true
% 2.77/0.98  --prep_unflatten                        true
% 2.77/0.98  --prep_res_sim                          true
% 2.77/0.98  --prep_upred                            true
% 2.77/0.98  --prep_sem_filter                       exhaustive
% 2.77/0.98  --prep_sem_filter_out                   false
% 2.77/0.98  --pred_elim                             true
% 2.77/0.98  --res_sim_input                         true
% 2.77/0.98  --eq_ax_congr_red                       true
% 2.77/0.98  --pure_diseq_elim                       true
% 2.77/0.98  --brand_transform                       false
% 2.77/0.98  --non_eq_to_eq                          false
% 2.77/0.98  --prep_def_merge                        true
% 2.77/0.98  --prep_def_merge_prop_impl              false
% 2.77/0.98  --prep_def_merge_mbd                    true
% 2.77/0.98  --prep_def_merge_tr_red                 false
% 2.77/0.98  --prep_def_merge_tr_cl                  false
% 2.77/0.98  --smt_preprocessing                     true
% 2.77/0.98  --smt_ac_axioms                         fast
% 2.77/0.98  --preprocessed_out                      false
% 2.77/0.98  --preprocessed_stats                    false
% 2.77/0.98  
% 2.77/0.98  ------ Abstraction refinement Options
% 2.77/0.98  
% 2.77/0.98  --abstr_ref                             []
% 2.77/0.98  --abstr_ref_prep                        false
% 2.77/0.98  --abstr_ref_until_sat                   false
% 2.77/0.98  --abstr_ref_sig_restrict                funpre
% 2.77/0.98  --abstr_ref_af_restrict_to_split_sk     false
% 2.77/0.98  --abstr_ref_under                       []
% 2.77/0.98  
% 2.77/0.98  ------ SAT Options
% 2.77/0.98  
% 2.77/0.98  --sat_mode                              false
% 2.77/0.98  --sat_fm_restart_options                ""
% 2.77/0.98  --sat_gr_def                            false
% 2.77/0.98  --sat_epr_types                         true
% 2.77/0.98  --sat_non_cyclic_types                  false
% 2.77/0.98  --sat_finite_models                     false
% 2.77/0.98  --sat_fm_lemmas                         false
% 2.77/0.98  --sat_fm_prep                           false
% 2.77/0.98  --sat_fm_uc_incr                        true
% 2.77/0.98  --sat_out_model                         small
% 2.77/0.98  --sat_out_clauses                       false
% 2.77/0.98  
% 2.77/0.98  ------ QBF Options
% 2.77/0.98  
% 2.77/0.98  --qbf_mode                              false
% 2.77/0.98  --qbf_elim_univ                         false
% 2.77/0.98  --qbf_dom_inst                          none
% 2.77/0.98  --qbf_dom_pre_inst                      false
% 2.77/0.98  --qbf_sk_in                             false
% 2.77/0.98  --qbf_pred_elim                         true
% 2.77/0.98  --qbf_split                             512
% 2.77/0.98  
% 2.77/0.98  ------ BMC1 Options
% 2.77/0.98  
% 2.77/0.98  --bmc1_incremental                      false
% 2.77/0.98  --bmc1_axioms                           reachable_all
% 2.77/0.98  --bmc1_min_bound                        0
% 2.77/0.98  --bmc1_max_bound                        -1
% 2.77/0.98  --bmc1_max_bound_default                -1
% 2.77/0.98  --bmc1_symbol_reachability              true
% 2.77/0.98  --bmc1_property_lemmas                  false
% 2.77/0.98  --bmc1_k_induction                      false
% 2.77/0.98  --bmc1_non_equiv_states                 false
% 2.77/0.98  --bmc1_deadlock                         false
% 2.77/0.98  --bmc1_ucm                              false
% 2.77/0.98  --bmc1_add_unsat_core                   none
% 2.77/0.98  --bmc1_unsat_core_children              false
% 2.77/0.98  --bmc1_unsat_core_extrapolate_axioms    false
% 2.77/0.98  --bmc1_out_stat                         full
% 2.77/0.98  --bmc1_ground_init                      false
% 2.77/0.98  --bmc1_pre_inst_next_state              false
% 2.77/0.98  --bmc1_pre_inst_state                   false
% 2.77/0.98  --bmc1_pre_inst_reach_state             false
% 2.77/0.98  --bmc1_out_unsat_core                   false
% 2.77/0.98  --bmc1_aig_witness_out                  false
% 2.77/0.98  --bmc1_verbose                          false
% 2.77/0.98  --bmc1_dump_clauses_tptp                false
% 2.77/0.98  --bmc1_dump_unsat_core_tptp             false
% 2.77/0.98  --bmc1_dump_file                        -
% 2.77/0.98  --bmc1_ucm_expand_uc_limit              128
% 2.77/0.98  --bmc1_ucm_n_expand_iterations          6
% 2.77/0.98  --bmc1_ucm_extend_mode                  1
% 2.77/0.98  --bmc1_ucm_init_mode                    2
% 2.77/0.98  --bmc1_ucm_cone_mode                    none
% 2.77/0.98  --bmc1_ucm_reduced_relation_type        0
% 2.77/0.98  --bmc1_ucm_relax_model                  4
% 2.77/0.98  --bmc1_ucm_full_tr_after_sat            true
% 2.77/0.98  --bmc1_ucm_expand_neg_assumptions       false
% 2.77/0.98  --bmc1_ucm_layered_model                none
% 2.77/0.98  --bmc1_ucm_max_lemma_size               10
% 2.77/0.98  
% 2.77/0.98  ------ AIG Options
% 2.77/0.98  
% 2.77/0.98  --aig_mode                              false
% 2.77/0.98  
% 2.77/0.98  ------ Instantiation Options
% 2.77/0.98  
% 2.77/0.98  --instantiation_flag                    true
% 2.77/0.98  --inst_sos_flag                         false
% 2.77/0.98  --inst_sos_phase                        true
% 2.77/0.98  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 2.77/0.98  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 2.77/0.98  --inst_lit_sel_side                     none
% 2.77/0.98  --inst_solver_per_active                1400
% 2.77/0.98  --inst_solver_calls_frac                1.
% 2.77/0.98  --inst_passive_queue_type               priority_queues
% 2.77/0.98  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 2.77/0.98  --inst_passive_queues_freq              [25;2]
% 2.77/0.98  --inst_dismatching                      true
% 2.77/0.98  --inst_eager_unprocessed_to_passive     true
% 2.77/0.98  --inst_prop_sim_given                   true
% 2.77/0.98  --inst_prop_sim_new                     false
% 2.77/0.98  --inst_subs_new                         false
% 2.77/0.98  --inst_eq_res_simp                      false
% 2.77/0.98  --inst_subs_given                       false
% 2.77/0.98  --inst_orphan_elimination               true
% 2.77/0.98  --inst_learning_loop_flag               true
% 2.77/0.98  --inst_learning_start                   3000
% 2.77/0.98  --inst_learning_factor                  2
% 2.77/0.98  --inst_start_prop_sim_after_learn       3
% 2.77/0.98  --inst_sel_renew                        solver
% 2.77/0.98  --inst_lit_activity_flag                true
% 2.77/0.98  --inst_restr_to_given                   false
% 2.77/0.98  --inst_activity_threshold               500
% 2.77/0.98  --inst_out_proof                        true
% 2.77/0.98  
% 2.77/0.98  ------ Resolution Options
% 2.77/0.98  
% 2.77/0.98  --resolution_flag                       false
% 2.77/0.98  --res_lit_sel                           adaptive
% 2.77/0.98  --res_lit_sel_side                      none
% 2.77/0.98  --res_ordering                          kbo
% 2.77/0.98  --res_to_prop_solver                    active
% 2.77/0.98  --res_prop_simpl_new                    false
% 2.77/0.98  --res_prop_simpl_given                  true
% 2.77/0.98  --res_passive_queue_type                priority_queues
% 2.77/0.98  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 2.77/0.98  --res_passive_queues_freq               [15;5]
% 2.77/0.98  --res_forward_subs                      full
% 2.77/0.98  --res_backward_subs                     full
% 2.77/0.98  --res_forward_subs_resolution           true
% 2.77/0.98  --res_backward_subs_resolution          true
% 2.77/0.98  --res_orphan_elimination                true
% 2.77/0.98  --res_time_limit                        2.
% 2.77/0.98  --res_out_proof                         true
% 2.77/0.98  
% 2.77/0.98  ------ Superposition Options
% 2.77/0.98  
% 2.77/0.98  --superposition_flag                    true
% 2.77/0.98  --sup_passive_queue_type                priority_queues
% 2.77/0.98  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 2.77/0.98  --sup_passive_queues_freq               [8;1;4]
% 2.77/0.98  --demod_completeness_check              fast
% 2.77/0.99  --demod_use_ground                      true
% 2.77/0.99  --sup_to_prop_solver                    passive
% 2.77/0.99  --sup_prop_simpl_new                    true
% 2.77/0.99  --sup_prop_simpl_given                  true
% 2.77/0.99  --sup_fun_splitting                     false
% 2.77/0.99  --sup_smt_interval                      50000
% 2.77/0.99  
% 2.77/0.99  ------ Superposition Simplification Setup
% 2.77/0.99  
% 2.77/0.99  --sup_indices_passive                   []
% 2.77/0.99  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.77/0.99  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.77/0.99  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.77/0.99  --sup_full_triv                         [TrivRules;PropSubs]
% 2.77/0.99  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.77/0.99  --sup_full_bw                           [BwDemod]
% 2.77/0.99  --sup_immed_triv                        [TrivRules]
% 2.77/0.99  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 2.77/0.99  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.77/0.99  --sup_immed_bw_main                     []
% 2.77/0.99  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.77/0.99  --sup_input_triv                        [Unflattening;TrivRules]
% 2.77/0.99  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.77/0.99  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.77/0.99  
% 2.77/0.99  ------ Combination Options
% 2.77/0.99  
% 2.77/0.99  --comb_res_mult                         3
% 2.77/0.99  --comb_sup_mult                         2
% 2.77/0.99  --comb_inst_mult                        10
% 2.77/0.99  
% 2.77/0.99  ------ Debug Options
% 2.77/0.99  
% 2.77/0.99  --dbg_backtrace                         false
% 2.77/0.99  --dbg_dump_prop_clauses                 false
% 2.77/0.99  --dbg_dump_prop_clauses_file            -
% 2.77/0.99  --dbg_out_stat                          false
% 2.77/0.99  
% 2.77/0.99  
% 2.77/0.99  
% 2.77/0.99  
% 2.77/0.99  ------ Proving...
% 2.77/0.99  
% 2.77/0.99  
% 2.77/0.99  % SZS status Theorem for theBenchmark.p
% 2.77/0.99  
% 2.77/0.99  % SZS output start CNFRefutation for theBenchmark.p
% 2.77/0.99  
% 2.77/0.99  fof(f16,conjecture,(
% 2.77/0.99    ! [X0,X1] : ((m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v3_funct_2(X1,X0,X0) & v1_funct_2(X1,X0,X0) & v1_funct_1(X1)) => (r2_relset_1(X0,X0,k1_partfun1(X0,X0,X0,X0,k2_funct_2(X0,X1),X1),k6_partfun1(X0)) & r2_relset_1(X0,X0,k1_partfun1(X0,X0,X0,X0,X1,k2_funct_2(X0,X1)),k6_partfun1(X0))))),
% 2.77/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.77/0.99  
% 2.77/0.99  fof(f17,negated_conjecture,(
% 2.77/0.99    ~! [X0,X1] : ((m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v3_funct_2(X1,X0,X0) & v1_funct_2(X1,X0,X0) & v1_funct_1(X1)) => (r2_relset_1(X0,X0,k1_partfun1(X0,X0,X0,X0,k2_funct_2(X0,X1),X1),k6_partfun1(X0)) & r2_relset_1(X0,X0,k1_partfun1(X0,X0,X0,X0,X1,k2_funct_2(X0,X1)),k6_partfun1(X0))))),
% 2.77/0.99    inference(negated_conjecture,[],[f16])).
% 2.77/0.99  
% 2.77/0.99  fof(f40,plain,(
% 2.77/0.99    ? [X0,X1] : ((~r2_relset_1(X0,X0,k1_partfun1(X0,X0,X0,X0,k2_funct_2(X0,X1),X1),k6_partfun1(X0)) | ~r2_relset_1(X0,X0,k1_partfun1(X0,X0,X0,X0,X1,k2_funct_2(X0,X1)),k6_partfun1(X0))) & (m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v3_funct_2(X1,X0,X0) & v1_funct_2(X1,X0,X0) & v1_funct_1(X1)))),
% 2.77/0.99    inference(ennf_transformation,[],[f17])).
% 2.77/0.99  
% 2.77/0.99  fof(f41,plain,(
% 2.77/0.99    ? [X0,X1] : ((~r2_relset_1(X0,X0,k1_partfun1(X0,X0,X0,X0,k2_funct_2(X0,X1),X1),k6_partfun1(X0)) | ~r2_relset_1(X0,X0,k1_partfun1(X0,X0,X0,X0,X1,k2_funct_2(X0,X1)),k6_partfun1(X0))) & m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v3_funct_2(X1,X0,X0) & v1_funct_2(X1,X0,X0) & v1_funct_1(X1))),
% 2.77/0.99    inference(flattening,[],[f40])).
% 2.77/0.99  
% 2.77/0.99  fof(f45,plain,(
% 2.77/0.99    ? [X0,X1] : ((~r2_relset_1(X0,X0,k1_partfun1(X0,X0,X0,X0,k2_funct_2(X0,X1),X1),k6_partfun1(X0)) | ~r2_relset_1(X0,X0,k1_partfun1(X0,X0,X0,X0,X1,k2_funct_2(X0,X1)),k6_partfun1(X0))) & m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v3_funct_2(X1,X0,X0) & v1_funct_2(X1,X0,X0) & v1_funct_1(X1)) => ((~r2_relset_1(sK1,sK1,k1_partfun1(sK1,sK1,sK1,sK1,k2_funct_2(sK1,sK2),sK2),k6_partfun1(sK1)) | ~r2_relset_1(sK1,sK1,k1_partfun1(sK1,sK1,sK1,sK1,sK2,k2_funct_2(sK1,sK2)),k6_partfun1(sK1))) & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK1,sK1))) & v3_funct_2(sK2,sK1,sK1) & v1_funct_2(sK2,sK1,sK1) & v1_funct_1(sK2))),
% 2.77/0.99    introduced(choice_axiom,[])).
% 2.77/0.99  
% 2.77/0.99  fof(f46,plain,(
% 2.77/0.99    (~r2_relset_1(sK1,sK1,k1_partfun1(sK1,sK1,sK1,sK1,k2_funct_2(sK1,sK2),sK2),k6_partfun1(sK1)) | ~r2_relset_1(sK1,sK1,k1_partfun1(sK1,sK1,sK1,sK1,sK2,k2_funct_2(sK1,sK2)),k6_partfun1(sK1))) & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK1,sK1))) & v3_funct_2(sK2,sK1,sK1) & v1_funct_2(sK2,sK1,sK1) & v1_funct_1(sK2)),
% 2.77/0.99    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1,sK2])],[f41,f45])).
% 2.77/0.99  
% 2.77/0.99  fof(f76,plain,(
% 2.77/0.99    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK1,sK1)))),
% 2.77/0.99    inference(cnf_transformation,[],[f46])).
% 2.77/0.99  
% 2.77/0.99  fof(f13,axiom,(
% 2.77/0.99    ! [X0,X1] : ((m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v3_funct_2(X1,X0,X0) & v1_funct_2(X1,X0,X0) & v1_funct_1(X1)) => k2_funct_1(X1) = k2_funct_2(X0,X1))),
% 2.77/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.77/0.99  
% 2.77/0.99  fof(f36,plain,(
% 2.77/0.99    ! [X0,X1] : (k2_funct_1(X1) = k2_funct_2(X0,X1) | (~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) | ~v3_funct_2(X1,X0,X0) | ~v1_funct_2(X1,X0,X0) | ~v1_funct_1(X1)))),
% 2.77/0.99    inference(ennf_transformation,[],[f13])).
% 2.77/0.99  
% 2.77/0.99  fof(f37,plain,(
% 2.77/0.99    ! [X0,X1] : (k2_funct_1(X1) = k2_funct_2(X0,X1) | ~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) | ~v3_funct_2(X1,X0,X0) | ~v1_funct_2(X1,X0,X0) | ~v1_funct_1(X1))),
% 2.77/0.99    inference(flattening,[],[f36])).
% 2.77/0.99  
% 2.77/0.99  fof(f70,plain,(
% 2.77/0.99    ( ! [X0,X1] : (k2_funct_1(X1) = k2_funct_2(X0,X1) | ~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) | ~v3_funct_2(X1,X0,X0) | ~v1_funct_2(X1,X0,X0) | ~v1_funct_1(X1)) )),
% 2.77/0.99    inference(cnf_transformation,[],[f37])).
% 2.77/0.99  
% 2.77/0.99  fof(f73,plain,(
% 2.77/0.99    v1_funct_1(sK2)),
% 2.77/0.99    inference(cnf_transformation,[],[f46])).
% 2.77/0.99  
% 2.77/0.99  fof(f74,plain,(
% 2.77/0.99    v1_funct_2(sK2,sK1,sK1)),
% 2.77/0.99    inference(cnf_transformation,[],[f46])).
% 2.77/0.99  
% 2.77/0.99  fof(f75,plain,(
% 2.77/0.99    v3_funct_2(sK2,sK1,sK1)),
% 2.77/0.99    inference(cnf_transformation,[],[f46])).
% 2.77/0.99  
% 2.77/0.99  fof(f9,axiom,(
% 2.77/0.99    ! [X0,X1] : ((m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v3_funct_2(X1,X0,X0) & v1_funct_2(X1,X0,X0) & v1_funct_1(X1)) => (m1_subset_1(k2_funct_2(X0,X1),k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v3_funct_2(k2_funct_2(X0,X1),X0,X0) & v1_funct_2(k2_funct_2(X0,X1),X0,X0) & v1_funct_1(k2_funct_2(X0,X1))))),
% 2.77/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.77/0.99  
% 2.77/0.99  fof(f32,plain,(
% 2.77/0.99    ! [X0,X1] : ((m1_subset_1(k2_funct_2(X0,X1),k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v3_funct_2(k2_funct_2(X0,X1),X0,X0) & v1_funct_2(k2_funct_2(X0,X1),X0,X0) & v1_funct_1(k2_funct_2(X0,X1))) | (~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) | ~v3_funct_2(X1,X0,X0) | ~v1_funct_2(X1,X0,X0) | ~v1_funct_1(X1)))),
% 2.77/0.99    inference(ennf_transformation,[],[f9])).
% 2.77/0.99  
% 2.77/0.99  fof(f33,plain,(
% 2.77/0.99    ! [X0,X1] : ((m1_subset_1(k2_funct_2(X0,X1),k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v3_funct_2(k2_funct_2(X0,X1),X0,X0) & v1_funct_2(k2_funct_2(X0,X1),X0,X0) & v1_funct_1(k2_funct_2(X0,X1))) | ~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) | ~v3_funct_2(X1,X0,X0) | ~v1_funct_2(X1,X0,X0) | ~v1_funct_1(X1))),
% 2.77/0.99    inference(flattening,[],[f32])).
% 2.77/0.99  
% 2.77/0.99  fof(f62,plain,(
% 2.77/0.99    ( ! [X0,X1] : (m1_subset_1(k2_funct_2(X0,X1),k1_zfmisc_1(k2_zfmisc_1(X0,X0))) | ~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) | ~v3_funct_2(X1,X0,X0) | ~v1_funct_2(X1,X0,X0) | ~v1_funct_1(X1)) )),
% 2.77/0.99    inference(cnf_transformation,[],[f33])).
% 2.77/0.99  
% 2.77/0.99  fof(f12,axiom,(
% 2.77/0.99    ! [X0,X1,X2,X3,X4,X5] : ((m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) & v1_funct_1(X5) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_1(X4)) => k5_relat_1(X4,X5) = k1_partfun1(X0,X1,X2,X3,X4,X5))),
% 2.77/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.77/0.99  
% 2.77/0.99  fof(f34,plain,(
% 2.77/0.99    ! [X0,X1,X2,X3,X4,X5] : (k5_relat_1(X4,X5) = k1_partfun1(X0,X1,X2,X3,X4,X5) | (~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X4)))),
% 2.77/0.99    inference(ennf_transformation,[],[f12])).
% 2.77/0.99  
% 2.77/0.99  fof(f35,plain,(
% 2.77/0.99    ! [X0,X1,X2,X3,X4,X5] : (k5_relat_1(X4,X5) = k1_partfun1(X0,X1,X2,X3,X4,X5) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X4))),
% 2.77/0.99    inference(flattening,[],[f34])).
% 2.77/0.99  
% 2.77/0.99  fof(f69,plain,(
% 2.77/0.99    ( ! [X4,X2,X0,X5,X3,X1] : (k5_relat_1(X4,X5) = k1_partfun1(X0,X1,X2,X3,X4,X5) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X4)) )),
% 2.77/0.99    inference(cnf_transformation,[],[f35])).
% 2.77/0.99  
% 2.77/0.99  fof(f59,plain,(
% 2.77/0.99    ( ! [X0,X1] : (v1_funct_1(k2_funct_2(X0,X1)) | ~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) | ~v3_funct_2(X1,X0,X0) | ~v1_funct_2(X1,X0,X0) | ~v1_funct_1(X1)) )),
% 2.77/0.99    inference(cnf_transformation,[],[f33])).
% 2.77/0.99  
% 2.77/0.99  fof(f15,axiom,(
% 2.77/0.99    ! [X0,X1] : ((m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v1_funct_2(X1,X0,X0) & v1_funct_1(X1)) => k1_relset_1(X0,X0,X1) = X0)),
% 2.77/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.77/0.99  
% 2.77/0.99  fof(f38,plain,(
% 2.77/0.99    ! [X0,X1] : (k1_relset_1(X0,X0,X1) = X0 | (~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) | ~v1_funct_2(X1,X0,X0) | ~v1_funct_1(X1)))),
% 2.77/0.99    inference(ennf_transformation,[],[f15])).
% 2.77/0.99  
% 2.77/0.99  fof(f39,plain,(
% 2.77/0.99    ! [X0,X1] : (k1_relset_1(X0,X0,X1) = X0 | ~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) | ~v1_funct_2(X1,X0,X0) | ~v1_funct_1(X1))),
% 2.77/0.99    inference(flattening,[],[f38])).
% 2.77/0.99  
% 2.77/0.99  fof(f72,plain,(
% 2.77/0.99    ( ! [X0,X1] : (k1_relset_1(X0,X0,X1) = X0 | ~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) | ~v1_funct_2(X1,X0,X0) | ~v1_funct_1(X1)) )),
% 2.77/0.99    inference(cnf_transformation,[],[f39])).
% 2.77/0.99  
% 2.77/0.99  fof(f5,axiom,(
% 2.77/0.99    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k1_relat_1(X2) = k1_relset_1(X0,X1,X2))),
% 2.77/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.77/0.99  
% 2.77/0.99  fof(f25,plain,(
% 2.77/0.99    ! [X0,X1,X2] : (k1_relat_1(X2) = k1_relset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 2.77/0.99    inference(ennf_transformation,[],[f5])).
% 2.77/0.99  
% 2.77/0.99  fof(f52,plain,(
% 2.77/0.99    ( ! [X2,X0,X1] : (k1_relat_1(X2) = k1_relset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 2.77/0.99    inference(cnf_transformation,[],[f25])).
% 2.77/0.99  
% 2.77/0.99  fof(f3,axiom,(
% 2.77/0.99    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => (v2_funct_1(X0) => (k5_relat_1(k2_funct_1(X0),X0) = k6_relat_1(k2_relat_1(X0)) & k5_relat_1(X0,k2_funct_1(X0)) = k6_relat_1(k1_relat_1(X0)))))),
% 2.77/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.77/0.99  
% 2.77/0.99  fof(f22,plain,(
% 2.77/0.99    ! [X0] : (((k5_relat_1(k2_funct_1(X0),X0) = k6_relat_1(k2_relat_1(X0)) & k5_relat_1(X0,k2_funct_1(X0)) = k6_relat_1(k1_relat_1(X0))) | ~v2_funct_1(X0)) | (~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 2.77/0.99    inference(ennf_transformation,[],[f3])).
% 2.77/0.99  
% 2.77/0.99  fof(f23,plain,(
% 2.77/0.99    ! [X0] : ((k5_relat_1(k2_funct_1(X0),X0) = k6_relat_1(k2_relat_1(X0)) & k5_relat_1(X0,k2_funct_1(X0)) = k6_relat_1(k1_relat_1(X0))) | ~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 2.77/0.99    inference(flattening,[],[f22])).
% 2.77/0.99  
% 2.77/0.99  fof(f49,plain,(
% 2.77/0.99    ( ! [X0] : (k5_relat_1(X0,k2_funct_1(X0)) = k6_relat_1(k1_relat_1(X0)) | ~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 2.77/0.99    inference(cnf_transformation,[],[f23])).
% 2.77/0.99  
% 2.77/0.99  fof(f14,axiom,(
% 2.77/0.99    ! [X0] : k6_relat_1(X0) = k6_partfun1(X0)),
% 2.77/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.77/0.99  
% 2.77/0.99  fof(f71,plain,(
% 2.77/0.99    ( ! [X0] : (k6_relat_1(X0) = k6_partfun1(X0)) )),
% 2.77/0.99    inference(cnf_transformation,[],[f14])).
% 2.77/0.99  
% 2.77/0.99  fof(f79,plain,(
% 2.77/0.99    ( ! [X0] : (k5_relat_1(X0,k2_funct_1(X0)) = k6_partfun1(k1_relat_1(X0)) | ~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 2.77/0.99    inference(definition_unfolding,[],[f49,f71])).
% 2.77/0.99  
% 2.77/0.99  fof(f2,axiom,(
% 2.77/0.99    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1))),
% 2.77/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.77/0.99  
% 2.77/0.99  fof(f48,plain,(
% 2.77/0.99    ( ! [X0,X1] : (v1_relat_1(k2_zfmisc_1(X0,X1))) )),
% 2.77/0.99    inference(cnf_transformation,[],[f2])).
% 2.77/0.99  
% 2.77/0.99  fof(f7,axiom,(
% 2.77/0.99    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => ((v3_funct_2(X2,X0,X1) & v1_funct_1(X2)) => (v2_funct_2(X2,X1) & v2_funct_1(X2) & v1_funct_1(X2))))),
% 2.77/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.77/0.99  
% 2.77/0.99  fof(f28,plain,(
% 2.77/0.99    ! [X0,X1,X2] : (((v2_funct_2(X2,X1) & v2_funct_1(X2) & v1_funct_1(X2)) | (~v3_funct_2(X2,X0,X1) | ~v1_funct_1(X2))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 2.77/0.99    inference(ennf_transformation,[],[f7])).
% 2.77/0.99  
% 2.77/0.99  fof(f29,plain,(
% 2.77/0.99    ! [X0,X1,X2] : ((v2_funct_2(X2,X1) & v2_funct_1(X2) & v1_funct_1(X2)) | ~v3_funct_2(X2,X0,X1) | ~v1_funct_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 2.77/0.99    inference(flattening,[],[f28])).
% 2.77/0.99  
% 2.77/0.99  fof(f55,plain,(
% 2.77/0.99    ( ! [X2,X0,X1] : (v2_funct_1(X2) | ~v3_funct_2(X2,X0,X1) | ~v1_funct_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 2.77/0.99    inference(cnf_transformation,[],[f29])).
% 2.77/0.99  
% 2.77/0.99  fof(f1,axiom,(
% 2.77/0.99    ! [X0] : (v1_relat_1(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => v1_relat_1(X1)))),
% 2.77/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.77/0.99  
% 2.77/0.99  fof(f21,plain,(
% 2.77/0.99    ! [X0] : (! [X1] : (v1_relat_1(X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) | ~v1_relat_1(X0))),
% 2.77/0.99    inference(ennf_transformation,[],[f1])).
% 2.77/0.99  
% 2.77/0.99  fof(f47,plain,(
% 2.77/0.99    ( ! [X0,X1] : (v1_relat_1(X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0)) | ~v1_relat_1(X0)) )),
% 2.77/0.99    inference(cnf_transformation,[],[f21])).
% 2.77/0.99  
% 2.77/0.99  fof(f50,plain,(
% 2.77/0.99    ( ! [X0] : (k5_relat_1(k2_funct_1(X0),X0) = k6_relat_1(k2_relat_1(X0)) | ~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 2.77/0.99    inference(cnf_transformation,[],[f23])).
% 2.77/0.99  
% 2.77/0.99  fof(f78,plain,(
% 2.77/0.99    ( ! [X0] : (k5_relat_1(k2_funct_1(X0),X0) = k6_partfun1(k2_relat_1(X0)) | ~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 2.77/0.99    inference(definition_unfolding,[],[f50,f71])).
% 2.77/0.99  
% 2.77/0.99  fof(f56,plain,(
% 2.77/0.99    ( ! [X2,X0,X1] : (v2_funct_2(X2,X1) | ~v3_funct_2(X2,X0,X1) | ~v1_funct_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 2.77/0.99    inference(cnf_transformation,[],[f29])).
% 2.77/0.99  
% 2.77/0.99  fof(f8,axiom,(
% 2.77/0.99    ! [X0,X1] : ((v5_relat_1(X1,X0) & v1_relat_1(X1)) => (v2_funct_2(X1,X0) <=> k2_relat_1(X1) = X0))),
% 2.77/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.77/0.99  
% 2.77/0.99  fof(f30,plain,(
% 2.77/0.99    ! [X0,X1] : ((v2_funct_2(X1,X0) <=> k2_relat_1(X1) = X0) | (~v5_relat_1(X1,X0) | ~v1_relat_1(X1)))),
% 2.77/0.99    inference(ennf_transformation,[],[f8])).
% 2.77/0.99  
% 2.77/0.99  fof(f31,plain,(
% 2.77/0.99    ! [X0,X1] : ((v2_funct_2(X1,X0) <=> k2_relat_1(X1) = X0) | ~v5_relat_1(X1,X0) | ~v1_relat_1(X1))),
% 2.77/0.99    inference(flattening,[],[f30])).
% 2.77/0.99  
% 2.77/0.99  fof(f42,plain,(
% 2.77/0.99    ! [X0,X1] : (((v2_funct_2(X1,X0) | k2_relat_1(X1) != X0) & (k2_relat_1(X1) = X0 | ~v2_funct_2(X1,X0))) | ~v5_relat_1(X1,X0) | ~v1_relat_1(X1))),
% 2.77/0.99    inference(nnf_transformation,[],[f31])).
% 2.77/0.99  
% 2.77/0.99  fof(f57,plain,(
% 2.77/0.99    ( ! [X0,X1] : (k2_relat_1(X1) = X0 | ~v2_funct_2(X1,X0) | ~v5_relat_1(X1,X0) | ~v1_relat_1(X1)) )),
% 2.77/0.99    inference(cnf_transformation,[],[f42])).
% 2.77/0.99  
% 2.77/0.99  fof(f4,axiom,(
% 2.77/0.99    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => (v5_relat_1(X2,X1) & v4_relat_1(X2,X0)))),
% 2.77/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.77/0.99  
% 2.77/0.99  fof(f19,plain,(
% 2.77/0.99    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => v5_relat_1(X2,X1))),
% 2.77/0.99    inference(pure_predicate_removal,[],[f4])).
% 2.77/0.99  
% 2.77/0.99  fof(f24,plain,(
% 2.77/0.99    ! [X0,X1,X2] : (v5_relat_1(X2,X1) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 2.77/0.99    inference(ennf_transformation,[],[f19])).
% 2.77/0.99  
% 2.77/0.99  fof(f51,plain,(
% 2.77/0.99    ( ! [X2,X0,X1] : (v5_relat_1(X2,X1) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 2.77/0.99    inference(cnf_transformation,[],[f24])).
% 2.77/0.99  
% 2.77/0.99  fof(f77,plain,(
% 2.77/0.99    ~r2_relset_1(sK1,sK1,k1_partfun1(sK1,sK1,sK1,sK1,k2_funct_2(sK1,sK2),sK2),k6_partfun1(sK1)) | ~r2_relset_1(sK1,sK1,k1_partfun1(sK1,sK1,sK1,sK1,sK2,k2_funct_2(sK1,sK2)),k6_partfun1(sK1))),
% 2.77/0.99    inference(cnf_transformation,[],[f46])).
% 2.77/0.99  
% 2.77/0.99  fof(f10,axiom,(
% 2.77/0.99    ! [X0] : (m1_subset_1(k6_partfun1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v1_partfun1(k6_partfun1(X0),X0))),
% 2.77/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.77/0.99  
% 2.77/0.99  fof(f18,plain,(
% 2.77/0.99    ! [X0] : m1_subset_1(k6_partfun1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0)))),
% 2.77/0.99    inference(pure_predicate_removal,[],[f10])).
% 2.77/0.99  
% 2.77/0.99  fof(f63,plain,(
% 2.77/0.99    ( ! [X0] : (m1_subset_1(k6_partfun1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0)))) )),
% 2.77/0.99    inference(cnf_transformation,[],[f18])).
% 2.77/0.99  
% 2.77/0.99  fof(f6,axiom,(
% 2.77/0.99    ! [X0,X1,X2,X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) => r2_relset_1(X0,X1,X2,X2))),
% 2.77/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.77/0.99  
% 2.77/0.99  fof(f26,plain,(
% 2.77/0.99    ! [X0,X1,X2,X3] : (r2_relset_1(X0,X1,X2,X2) | (~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))))),
% 2.77/0.99    inference(ennf_transformation,[],[f6])).
% 2.77/0.99  
% 2.77/0.99  fof(f27,plain,(
% 2.77/0.99    ! [X0,X1,X2,X3] : (r2_relset_1(X0,X1,X2,X2) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 2.77/0.99    inference(flattening,[],[f26])).
% 2.77/0.99  
% 2.77/0.99  fof(f53,plain,(
% 2.77/0.99    ( ! [X2,X0,X3,X1] : (r2_relset_1(X0,X1,X2,X2) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 2.77/0.99    inference(cnf_transformation,[],[f27])).
% 2.77/0.99  
% 2.77/0.99  cnf(c_26,negated_conjecture,
% 2.77/0.99      ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK1,sK1))) ),
% 2.77/0.99      inference(cnf_transformation,[],[f76]) ).
% 2.77/0.99  
% 2.77/0.99  cnf(c_1093,plain,
% 2.77/0.99      ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK1,sK1))) = iProver_top ),
% 2.77/0.99      inference(predicate_to_equality,[status(thm)],[c_26]) ).
% 2.77/0.99  
% 2.77/0.99  cnf(c_23,plain,
% 2.77/0.99      ( ~ v1_funct_2(X0,X1,X1)
% 2.77/0.99      | ~ v3_funct_2(X0,X1,X1)
% 2.77/0.99      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X1)))
% 2.77/0.99      | ~ v1_funct_1(X0)
% 2.77/0.99      | k2_funct_2(X1,X0) = k2_funct_1(X0) ),
% 2.77/0.99      inference(cnf_transformation,[],[f70]) ).
% 2.77/0.99  
% 2.77/0.99  cnf(c_1096,plain,
% 2.77/0.99      ( k2_funct_2(X0,X1) = k2_funct_1(X1)
% 2.77/0.99      | v1_funct_2(X1,X0,X0) != iProver_top
% 2.77/0.99      | v3_funct_2(X1,X0,X0) != iProver_top
% 2.77/0.99      | m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) != iProver_top
% 2.77/0.99      | v1_funct_1(X1) != iProver_top ),
% 2.77/0.99      inference(predicate_to_equality,[status(thm)],[c_23]) ).
% 2.77/0.99  
% 2.77/0.99  cnf(c_2401,plain,
% 2.77/0.99      ( k2_funct_2(sK1,sK2) = k2_funct_1(sK2)
% 2.77/0.99      | v1_funct_2(sK2,sK1,sK1) != iProver_top
% 2.77/0.99      | v3_funct_2(sK2,sK1,sK1) != iProver_top
% 2.77/0.99      | v1_funct_1(sK2) != iProver_top ),
% 2.77/0.99      inference(superposition,[status(thm)],[c_1093,c_1096]) ).
% 2.77/0.99  
% 2.77/0.99  cnf(c_29,negated_conjecture,
% 2.77/0.99      ( v1_funct_1(sK2) ),
% 2.77/0.99      inference(cnf_transformation,[],[f73]) ).
% 2.77/0.99  
% 2.77/0.99  cnf(c_28,negated_conjecture,
% 2.77/0.99      ( v1_funct_2(sK2,sK1,sK1) ),
% 2.77/0.99      inference(cnf_transformation,[],[f74]) ).
% 2.77/0.99  
% 2.77/0.99  cnf(c_27,negated_conjecture,
% 2.77/0.99      ( v3_funct_2(sK2,sK1,sK1) ),
% 2.77/0.99      inference(cnf_transformation,[],[f75]) ).
% 2.77/0.99  
% 2.77/0.99  cnf(c_1459,plain,
% 2.77/0.99      ( ~ v1_funct_2(sK2,X0,X0)
% 2.77/0.99      | ~ v3_funct_2(sK2,X0,X0)
% 2.77/0.99      | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
% 2.77/0.99      | ~ v1_funct_1(sK2)
% 2.77/0.99      | k2_funct_2(X0,sK2) = k2_funct_1(sK2) ),
% 2.77/0.99      inference(instantiation,[status(thm)],[c_23]) ).
% 2.77/0.99  
% 2.77/0.99  cnf(c_1461,plain,
% 2.77/0.99      ( ~ v1_funct_2(sK2,sK1,sK1)
% 2.77/0.99      | ~ v3_funct_2(sK2,sK1,sK1)
% 2.77/0.99      | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK1,sK1)))
% 2.77/0.99      | ~ v1_funct_1(sK2)
% 2.77/0.99      | k2_funct_2(sK1,sK2) = k2_funct_1(sK2) ),
% 2.77/0.99      inference(instantiation,[status(thm)],[c_1459]) ).
% 2.77/0.99  
% 2.77/0.99  cnf(c_2815,plain,
% 2.77/0.99      ( k2_funct_2(sK1,sK2) = k2_funct_1(sK2) ),
% 2.77/0.99      inference(global_propositional_subsumption,
% 2.77/0.99                [status(thm)],
% 2.77/0.99                [c_2401,c_29,c_28,c_27,c_26,c_1461]) ).
% 2.77/0.99  
% 2.77/0.99  cnf(c_12,plain,
% 2.77/0.99      ( ~ v1_funct_2(X0,X1,X1)
% 2.77/0.99      | ~ v3_funct_2(X0,X1,X1)
% 2.77/0.99      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X1)))
% 2.77/0.99      | m1_subset_1(k2_funct_2(X1,X0),k1_zfmisc_1(k2_zfmisc_1(X1,X1)))
% 2.77/0.99      | ~ v1_funct_1(X0) ),
% 2.77/0.99      inference(cnf_transformation,[],[f62]) ).
% 2.77/0.99  
% 2.77/0.99  cnf(c_1106,plain,
% 2.77/0.99      ( v1_funct_2(X0,X1,X1) != iProver_top
% 2.77/0.99      | v3_funct_2(X0,X1,X1) != iProver_top
% 2.77/0.99      | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X1))) != iProver_top
% 2.77/0.99      | m1_subset_1(k2_funct_2(X1,X0),k1_zfmisc_1(k2_zfmisc_1(X1,X1))) = iProver_top
% 2.77/0.99      | v1_funct_1(X0) != iProver_top ),
% 2.77/0.99      inference(predicate_to_equality,[status(thm)],[c_12]) ).
% 2.77/0.99  
% 2.77/0.99  cnf(c_3418,plain,
% 2.77/0.99      ( v1_funct_2(sK2,sK1,sK1) != iProver_top
% 2.77/0.99      | v3_funct_2(sK2,sK1,sK1) != iProver_top
% 2.77/0.99      | m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK1))) = iProver_top
% 2.77/0.99      | m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK1,sK1))) != iProver_top
% 2.77/0.99      | v1_funct_1(sK2) != iProver_top ),
% 2.77/0.99      inference(superposition,[status(thm)],[c_2815,c_1106]) ).
% 2.77/0.99  
% 2.77/0.99  cnf(c_30,plain,
% 2.77/0.99      ( v1_funct_1(sK2) = iProver_top ),
% 2.77/0.99      inference(predicate_to_equality,[status(thm)],[c_29]) ).
% 2.77/0.99  
% 2.77/0.99  cnf(c_31,plain,
% 2.77/0.99      ( v1_funct_2(sK2,sK1,sK1) = iProver_top ),
% 2.77/0.99      inference(predicate_to_equality,[status(thm)],[c_28]) ).
% 2.77/0.99  
% 2.77/0.99  cnf(c_32,plain,
% 2.77/0.99      ( v3_funct_2(sK2,sK1,sK1) = iProver_top ),
% 2.77/0.99      inference(predicate_to_equality,[status(thm)],[c_27]) ).
% 2.77/0.99  
% 2.77/0.99  cnf(c_33,plain,
% 2.77/0.99      ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK1,sK1))) = iProver_top ),
% 2.77/0.99      inference(predicate_to_equality,[status(thm)],[c_26]) ).
% 2.77/0.99  
% 2.77/0.99  cnf(c_4198,plain,
% 2.77/0.99      ( m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK1))) = iProver_top ),
% 2.77/0.99      inference(global_propositional_subsumption,
% 2.77/0.99                [status(thm)],
% 2.77/0.99                [c_3418,c_30,c_31,c_32,c_33]) ).
% 2.77/0.99  
% 2.77/0.99  cnf(c_22,plain,
% 2.77/0.99      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 2.77/0.99      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X4,X5)))
% 2.77/0.99      | ~ v1_funct_1(X0)
% 2.77/0.99      | ~ v1_funct_1(X3)
% 2.77/0.99      | k1_partfun1(X4,X5,X1,X2,X3,X0) = k5_relat_1(X3,X0) ),
% 2.77/0.99      inference(cnf_transformation,[],[f69]) ).
% 2.77/0.99  
% 2.77/0.99  cnf(c_1097,plain,
% 2.77/0.99      ( k1_partfun1(X0,X1,X2,X3,X4,X5) = k5_relat_1(X4,X5)
% 2.77/0.99      | m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) != iProver_top
% 2.77/0.99      | m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top
% 2.77/0.99      | v1_funct_1(X5) != iProver_top
% 2.77/0.99      | v1_funct_1(X4) != iProver_top ),
% 2.77/0.99      inference(predicate_to_equality,[status(thm)],[c_22]) ).
% 2.77/0.99  
% 2.77/0.99  cnf(c_4212,plain,
% 2.77/0.99      ( k1_partfun1(X0,X1,sK1,sK1,X2,k2_funct_1(sK2)) = k5_relat_1(X2,k2_funct_1(sK2))
% 2.77/0.99      | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top
% 2.77/0.99      | v1_funct_1(X2) != iProver_top
% 2.77/0.99      | v1_funct_1(k2_funct_1(sK2)) != iProver_top ),
% 2.77/0.99      inference(superposition,[status(thm)],[c_4198,c_1097]) ).
% 2.77/0.99  
% 2.77/0.99  cnf(c_15,plain,
% 2.77/0.99      ( ~ v1_funct_2(X0,X1,X1)
% 2.77/0.99      | ~ v3_funct_2(X0,X1,X1)
% 2.77/0.99      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X1)))
% 2.77/0.99      | ~ v1_funct_1(X0)
% 2.77/0.99      | v1_funct_1(k2_funct_2(X1,X0)) ),
% 2.77/0.99      inference(cnf_transformation,[],[f59]) ).
% 2.77/0.99  
% 2.77/0.99  cnf(c_1103,plain,
% 2.77/0.99      ( v1_funct_2(X0,X1,X1) != iProver_top
% 2.77/0.99      | v3_funct_2(X0,X1,X1) != iProver_top
% 2.77/0.99      | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X1))) != iProver_top
% 2.77/0.99      | v1_funct_1(X0) != iProver_top
% 2.77/0.99      | v1_funct_1(k2_funct_2(X1,X0)) = iProver_top ),
% 2.77/0.99      inference(predicate_to_equality,[status(thm)],[c_15]) ).
% 2.77/0.99  
% 2.77/0.99  cnf(c_3180,plain,
% 2.77/0.99      ( v1_funct_2(sK2,sK1,sK1) != iProver_top
% 2.77/0.99      | v3_funct_2(sK2,sK1,sK1) != iProver_top
% 2.77/0.99      | v1_funct_1(k2_funct_2(sK1,sK2)) = iProver_top
% 2.77/0.99      | v1_funct_1(sK2) != iProver_top ),
% 2.77/0.99      inference(superposition,[status(thm)],[c_1093,c_1103]) ).
% 2.77/0.99  
% 2.77/0.99  cnf(c_3185,plain,
% 2.77/0.99      ( v1_funct_2(sK2,sK1,sK1) != iProver_top
% 2.77/0.99      | v3_funct_2(sK2,sK1,sK1) != iProver_top
% 2.77/0.99      | v1_funct_1(k2_funct_1(sK2)) = iProver_top
% 2.77/0.99      | v1_funct_1(sK2) != iProver_top ),
% 2.77/0.99      inference(light_normalisation,[status(thm)],[c_3180,c_2815]) ).
% 2.77/0.99  
% 2.77/0.99  cnf(c_5626,plain,
% 2.77/0.99      ( v1_funct_1(X2) != iProver_top
% 2.77/0.99      | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top
% 2.77/0.99      | k1_partfun1(X0,X1,sK1,sK1,X2,k2_funct_1(sK2)) = k5_relat_1(X2,k2_funct_1(sK2)) ),
% 2.77/0.99      inference(global_propositional_subsumption,
% 2.77/0.99                [status(thm)],
% 2.77/0.99                [c_4212,c_30,c_31,c_32,c_3185]) ).
% 2.77/0.99  
% 2.77/0.99  cnf(c_5627,plain,
% 2.77/0.99      ( k1_partfun1(X0,X1,sK1,sK1,X2,k2_funct_1(sK2)) = k5_relat_1(X2,k2_funct_1(sK2))
% 2.77/0.99      | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top
% 2.77/0.99      | v1_funct_1(X2) != iProver_top ),
% 2.77/0.99      inference(renaming,[status(thm)],[c_5626]) ).
% 2.77/0.99  
% 2.77/0.99  cnf(c_5638,plain,
% 2.77/0.99      ( k1_partfun1(sK1,sK1,sK1,sK1,sK2,k2_funct_1(sK2)) = k5_relat_1(sK2,k2_funct_1(sK2))
% 2.77/0.99      | v1_funct_1(sK2) != iProver_top ),
% 2.77/0.99      inference(superposition,[status(thm)],[c_1093,c_5627]) ).
% 2.77/0.99  
% 2.77/0.99  cnf(c_24,plain,
% 2.77/0.99      ( ~ v1_funct_2(X0,X1,X1)
% 2.77/0.99      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X1)))
% 2.77/0.99      | ~ v1_funct_1(X0)
% 2.77/0.99      | k1_relset_1(X1,X1,X0) = X1 ),
% 2.77/0.99      inference(cnf_transformation,[],[f72]) ).
% 2.77/0.99  
% 2.77/0.99  cnf(c_1095,plain,
% 2.77/0.99      ( k1_relset_1(X0,X0,X1) = X0
% 2.77/0.99      | v1_funct_2(X1,X0,X0) != iProver_top
% 2.77/0.99      | m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) != iProver_top
% 2.77/0.99      | v1_funct_1(X1) != iProver_top ),
% 2.77/0.99      inference(predicate_to_equality,[status(thm)],[c_24]) ).
% 2.77/0.99  
% 2.77/0.99  cnf(c_2177,plain,
% 2.77/0.99      ( k1_relset_1(sK1,sK1,sK2) = sK1
% 2.77/0.99      | v1_funct_2(sK2,sK1,sK1) != iProver_top
% 2.77/0.99      | v1_funct_1(sK2) != iProver_top ),
% 2.77/0.99      inference(superposition,[status(thm)],[c_1093,c_1095]) ).
% 2.77/0.99  
% 2.77/0.99  cnf(c_5,plain,
% 2.77/0.99      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 2.77/0.99      | k1_relset_1(X1,X2,X0) = k1_relat_1(X0) ),
% 2.77/0.99      inference(cnf_transformation,[],[f52]) ).
% 2.77/0.99  
% 2.77/0.99  cnf(c_1109,plain,
% 2.77/0.99      ( k1_relset_1(X0,X1,X2) = k1_relat_1(X2)
% 2.77/0.99      | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
% 2.77/0.99      inference(predicate_to_equality,[status(thm)],[c_5]) ).
% 2.77/0.99  
% 2.77/0.99  cnf(c_1793,plain,
% 2.77/0.99      ( k1_relset_1(sK1,sK1,sK2) = k1_relat_1(sK2) ),
% 2.77/0.99      inference(superposition,[status(thm)],[c_1093,c_1109]) ).
% 2.77/0.99  
% 2.77/0.99  cnf(c_2181,plain,
% 2.77/0.99      ( k1_relat_1(sK2) = sK1
% 2.77/0.99      | v1_funct_2(sK2,sK1,sK1) != iProver_top
% 2.77/0.99      | v1_funct_1(sK2) != iProver_top ),
% 2.77/0.99      inference(demodulation,[status(thm)],[c_2177,c_1793]) ).
% 2.77/0.99  
% 2.77/0.99  cnf(c_2959,plain,
% 2.77/0.99      ( k1_relat_1(sK2) = sK1 ),
% 2.77/0.99      inference(global_propositional_subsumption,
% 2.77/0.99                [status(thm)],
% 2.77/0.99                [c_2181,c_30,c_31]) ).
% 2.77/0.99  
% 2.77/0.99  cnf(c_1090,plain,
% 2.77/0.99      ( v1_funct_1(sK2) = iProver_top ),
% 2.77/0.99      inference(predicate_to_equality,[status(thm)],[c_29]) ).
% 2.77/0.99  
% 2.77/0.99  cnf(c_3,plain,
% 2.77/0.99      ( ~ v1_funct_1(X0)
% 2.77/0.99      | ~ v2_funct_1(X0)
% 2.77/0.99      | ~ v1_relat_1(X0)
% 2.77/0.99      | k5_relat_1(X0,k2_funct_1(X0)) = k6_partfun1(k1_relat_1(X0)) ),
% 2.77/0.99      inference(cnf_transformation,[],[f79]) ).
% 2.77/0.99  
% 2.77/0.99  cnf(c_1110,plain,
% 2.77/0.99      ( k5_relat_1(X0,k2_funct_1(X0)) = k6_partfun1(k1_relat_1(X0))
% 2.77/0.99      | v1_funct_1(X0) != iProver_top
% 2.77/0.99      | v2_funct_1(X0) != iProver_top
% 2.77/0.99      | v1_relat_1(X0) != iProver_top ),
% 2.77/0.99      inference(predicate_to_equality,[status(thm)],[c_3]) ).
% 2.77/0.99  
% 2.77/0.99  cnf(c_2153,plain,
% 2.77/0.99      ( k5_relat_1(sK2,k2_funct_1(sK2)) = k6_partfun1(k1_relat_1(sK2))
% 2.77/0.99      | v2_funct_1(sK2) != iProver_top
% 2.77/0.99      | v1_relat_1(sK2) != iProver_top ),
% 2.77/0.99      inference(superposition,[status(thm)],[c_1090,c_1110]) ).
% 2.77/0.99  
% 2.77/0.99  cnf(c_1,plain,
% 2.77/0.99      ( v1_relat_1(k2_zfmisc_1(X0,X1)) ),
% 2.77/0.99      inference(cnf_transformation,[],[f48]) ).
% 2.77/0.99  
% 2.77/0.99  cnf(c_103,plain,
% 2.77/0.99      ( v1_relat_1(k2_zfmisc_1(sK1,sK1)) ),
% 2.77/0.99      inference(instantiation,[status(thm)],[c_1]) ).
% 2.77/0.99  
% 2.77/0.99  cnf(c_1344,plain,
% 2.77/0.99      ( ~ v1_funct_1(sK2)
% 2.77/0.99      | ~ v2_funct_1(sK2)
% 2.77/0.99      | ~ v1_relat_1(sK2)
% 2.77/0.99      | k5_relat_1(sK2,k2_funct_1(sK2)) = k6_partfun1(k1_relat_1(sK2)) ),
% 2.77/0.99      inference(instantiation,[status(thm)],[c_3]) ).
% 2.77/0.99  
% 2.77/0.99  cnf(c_8,plain,
% 2.77/0.99      ( ~ v3_funct_2(X0,X1,X2)
% 2.77/0.99      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 2.77/0.99      | ~ v1_funct_1(X0)
% 2.77/0.99      | v2_funct_1(X0) ),
% 2.77/0.99      inference(cnf_transformation,[],[f55]) ).
% 2.77/0.99  
% 2.77/0.99  cnf(c_1365,plain,
% 2.77/0.99      ( ~ v3_funct_2(sK2,X0,X1)
% 2.77/0.99      | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
% 2.77/0.99      | ~ v1_funct_1(sK2)
% 2.77/0.99      | v2_funct_1(sK2) ),
% 2.77/0.99      inference(instantiation,[status(thm)],[c_8]) ).
% 2.77/0.99  
% 2.77/0.99  cnf(c_1367,plain,
% 2.77/0.99      ( ~ v3_funct_2(sK2,sK1,sK1)
% 2.77/0.99      | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK1,sK1)))
% 2.77/0.99      | ~ v1_funct_1(sK2)
% 2.77/0.99      | v2_funct_1(sK2) ),
% 2.77/0.99      inference(instantiation,[status(thm)],[c_1365]) ).
% 2.77/0.99  
% 2.77/0.99  cnf(c_0,plain,
% 2.77/0.99      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
% 2.77/0.99      | ~ v1_relat_1(X1)
% 2.77/0.99      | v1_relat_1(X0) ),
% 2.77/0.99      inference(cnf_transformation,[],[f47]) ).
% 2.77/0.99  
% 2.77/0.99  cnf(c_1312,plain,
% 2.77/0.99      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 2.77/0.99      | v1_relat_1(X0)
% 2.77/0.99      | ~ v1_relat_1(k2_zfmisc_1(X1,X2)) ),
% 2.77/0.99      inference(instantiation,[status(thm)],[c_0]) ).
% 2.77/0.99  
% 2.77/0.99  cnf(c_1642,plain,
% 2.77/0.99      ( ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK1,sK1)))
% 2.77/0.99      | ~ v1_relat_1(k2_zfmisc_1(sK1,sK1))
% 2.77/0.99      | v1_relat_1(sK2) ),
% 2.77/0.99      inference(instantiation,[status(thm)],[c_1312]) ).
% 2.77/0.99  
% 2.77/0.99  cnf(c_2811,plain,
% 2.77/0.99      ( k5_relat_1(sK2,k2_funct_1(sK2)) = k6_partfun1(k1_relat_1(sK2)) ),
% 2.77/0.99      inference(global_propositional_subsumption,
% 2.77/0.99                [status(thm)],
% 2.77/0.99                [c_2153,c_29,c_27,c_26,c_103,c_1344,c_1367,c_1642]) ).
% 2.77/0.99  
% 2.77/0.99  cnf(c_2962,plain,
% 2.77/0.99      ( k5_relat_1(sK2,k2_funct_1(sK2)) = k6_partfun1(sK1) ),
% 2.77/0.99      inference(demodulation,[status(thm)],[c_2959,c_2811]) ).
% 2.77/0.99  
% 2.77/0.99  cnf(c_5646,plain,
% 2.77/0.99      ( k1_partfun1(sK1,sK1,sK1,sK1,sK2,k2_funct_1(sK2)) = k6_partfun1(sK1)
% 2.77/0.99      | v1_funct_1(sK2) != iProver_top ),
% 2.77/0.99      inference(light_normalisation,[status(thm)],[c_5638,c_2962]) ).
% 2.77/0.99  
% 2.77/0.99  cnf(c_5792,plain,
% 2.77/0.99      ( k1_partfun1(sK1,sK1,sK1,sK1,sK2,k2_funct_1(sK2)) = k6_partfun1(sK1) ),
% 2.77/0.99      inference(global_propositional_subsumption,
% 2.77/0.99                [status(thm)],
% 2.77/0.99                [c_5646,c_30]) ).
% 2.77/0.99  
% 2.77/0.99  cnf(c_3138,plain,
% 2.77/0.99      ( k1_partfun1(X0,X1,sK1,sK1,X2,sK2) = k5_relat_1(X2,sK2)
% 2.77/0.99      | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top
% 2.77/0.99      | v1_funct_1(X2) != iProver_top
% 2.77/0.99      | v1_funct_1(sK2) != iProver_top ),
% 2.77/0.99      inference(superposition,[status(thm)],[c_1093,c_1097]) ).
% 2.77/0.99  
% 2.77/0.99  cnf(c_3633,plain,
% 2.77/0.99      ( v1_funct_1(X2) != iProver_top
% 2.77/0.99      | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top
% 2.77/0.99      | k1_partfun1(X0,X1,sK1,sK1,X2,sK2) = k5_relat_1(X2,sK2) ),
% 2.77/0.99      inference(global_propositional_subsumption,
% 2.77/0.99                [status(thm)],
% 2.77/0.99                [c_3138,c_30]) ).
% 2.77/0.99  
% 2.77/0.99  cnf(c_3634,plain,
% 2.77/0.99      ( k1_partfun1(X0,X1,sK1,sK1,X2,sK2) = k5_relat_1(X2,sK2)
% 2.77/0.99      | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top
% 2.77/0.99      | v1_funct_1(X2) != iProver_top ),
% 2.77/0.99      inference(renaming,[status(thm)],[c_3633]) ).
% 2.77/0.99  
% 2.77/0.99  cnf(c_3642,plain,
% 2.77/0.99      ( k1_partfun1(X0,X0,sK1,sK1,k2_funct_2(X0,X1),sK2) = k5_relat_1(k2_funct_2(X0,X1),sK2)
% 2.77/0.99      | v1_funct_2(X1,X0,X0) != iProver_top
% 2.77/0.99      | v3_funct_2(X1,X0,X0) != iProver_top
% 2.77/0.99      | m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) != iProver_top
% 2.77/0.99      | v1_funct_1(X1) != iProver_top
% 2.77/0.99      | v1_funct_1(k2_funct_2(X0,X1)) != iProver_top ),
% 2.77/0.99      inference(superposition,[status(thm)],[c_1106,c_3634]) ).
% 2.77/0.99  
% 2.77/0.99  cnf(c_4319,plain,
% 2.77/0.99      ( k1_partfun1(X0,X0,sK1,sK1,k2_funct_2(X0,X1),sK2) = k5_relat_1(k2_funct_2(X0,X1),sK2)
% 2.77/0.99      | v1_funct_2(X1,X0,X0) != iProver_top
% 2.77/0.99      | v3_funct_2(X1,X0,X0) != iProver_top
% 2.77/0.99      | m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) != iProver_top
% 2.77/0.99      | v1_funct_1(X1) != iProver_top ),
% 2.77/0.99      inference(forward_subsumption_resolution,
% 2.77/0.99                [status(thm)],
% 2.77/0.99                [c_3642,c_1103]) ).
% 2.77/0.99  
% 2.77/0.99  cnf(c_4326,plain,
% 2.77/0.99      ( k1_partfun1(sK1,sK1,sK1,sK1,k2_funct_2(sK1,sK2),sK2) = k5_relat_1(k2_funct_2(sK1,sK2),sK2)
% 2.77/0.99      | v1_funct_2(sK2,sK1,sK1) != iProver_top
% 2.77/0.99      | v3_funct_2(sK2,sK1,sK1) != iProver_top
% 2.77/0.99      | v1_funct_1(sK2) != iProver_top ),
% 2.77/0.99      inference(superposition,[status(thm)],[c_1093,c_4319]) ).
% 2.77/0.99  
% 2.77/0.99  cnf(c_2,plain,
% 2.77/0.99      ( ~ v1_funct_1(X0)
% 2.77/0.99      | ~ v2_funct_1(X0)
% 2.77/0.99      | ~ v1_relat_1(X0)
% 2.77/0.99      | k5_relat_1(k2_funct_1(X0),X0) = k6_partfun1(k2_relat_1(X0)) ),
% 2.77/0.99      inference(cnf_transformation,[],[f78]) ).
% 2.77/0.99  
% 2.77/0.99  cnf(c_1111,plain,
% 2.77/0.99      ( k5_relat_1(k2_funct_1(X0),X0) = k6_partfun1(k2_relat_1(X0))
% 2.77/0.99      | v1_funct_1(X0) != iProver_top
% 2.77/0.99      | v2_funct_1(X0) != iProver_top
% 2.77/0.99      | v1_relat_1(X0) != iProver_top ),
% 2.77/0.99      inference(predicate_to_equality,[status(thm)],[c_2]) ).
% 2.77/0.99  
% 2.77/0.99  cnf(c_2271,plain,
% 2.77/0.99      ( k5_relat_1(k2_funct_1(sK2),sK2) = k6_partfun1(k2_relat_1(sK2))
% 2.77/0.99      | v2_funct_1(sK2) != iProver_top
% 2.77/0.99      | v1_relat_1(sK2) != iProver_top ),
% 2.77/0.99      inference(superposition,[status(thm)],[c_1090,c_1111]) ).
% 2.77/0.99  
% 2.77/0.99  cnf(c_7,plain,
% 2.77/0.99      ( ~ v3_funct_2(X0,X1,X2)
% 2.77/0.99      | v2_funct_2(X0,X2)
% 2.77/0.99      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 2.77/0.99      | ~ v1_funct_1(X0) ),
% 2.77/0.99      inference(cnf_transformation,[],[f56]) ).
% 2.77/0.99  
% 2.77/0.99  cnf(c_11,plain,
% 2.77/0.99      ( ~ v2_funct_2(X0,X1)
% 2.77/0.99      | ~ v5_relat_1(X0,X1)
% 2.77/0.99      | ~ v1_relat_1(X0)
% 2.77/0.99      | k2_relat_1(X0) = X1 ),
% 2.77/0.99      inference(cnf_transformation,[],[f57]) ).
% 2.77/0.99  
% 2.77/0.99  cnf(c_331,plain,
% 2.77/0.99      ( ~ v3_funct_2(X0,X1,X2)
% 2.77/0.99      | ~ v5_relat_1(X3,X4)
% 2.77/0.99      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 2.77/0.99      | ~ v1_funct_1(X0)
% 2.77/0.99      | ~ v1_relat_1(X3)
% 2.77/0.99      | X3 != X0
% 2.77/0.99      | X4 != X2
% 2.77/0.99      | k2_relat_1(X3) = X4 ),
% 2.77/0.99      inference(resolution_lifted,[status(thm)],[c_7,c_11]) ).
% 2.77/0.99  
% 2.77/0.99  cnf(c_332,plain,
% 2.77/0.99      ( ~ v3_funct_2(X0,X1,X2)
% 2.77/0.99      | ~ v5_relat_1(X0,X2)
% 2.77/0.99      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 2.77/0.99      | ~ v1_funct_1(X0)
% 2.77/0.99      | ~ v1_relat_1(X0)
% 2.77/0.99      | k2_relat_1(X0) = X2 ),
% 2.77/0.99      inference(unflattening,[status(thm)],[c_331]) ).
% 2.77/0.99  
% 2.77/0.99  cnf(c_4,plain,
% 2.77/0.99      ( v5_relat_1(X0,X1)
% 2.77/0.99      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) ),
% 2.77/0.99      inference(cnf_transformation,[],[f51]) ).
% 2.77/0.99  
% 2.77/0.99  cnf(c_348,plain,
% 2.77/0.99      ( ~ v3_funct_2(X0,X1,X2)
% 2.77/0.99      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 2.77/0.99      | ~ v1_funct_1(X0)
% 2.77/0.99      | ~ v1_relat_1(X0)
% 2.77/0.99      | k2_relat_1(X0) = X2 ),
% 2.77/0.99      inference(forward_subsumption_resolution,[status(thm)],[c_332,c_4]) ).
% 2.77/0.99  
% 2.77/0.99  cnf(c_1089,plain,
% 2.77/0.99      ( k2_relat_1(X0) = X1
% 2.77/0.99      | v3_funct_2(X0,X2,X1) != iProver_top
% 2.77/0.99      | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) != iProver_top
% 2.77/0.99      | v1_funct_1(X0) != iProver_top
% 2.77/0.99      | v1_relat_1(X0) != iProver_top ),
% 2.77/0.99      inference(predicate_to_equality,[status(thm)],[c_348]) ).
% 2.77/0.99  
% 2.77/0.99  cnf(c_1551,plain,
% 2.77/0.99      ( k2_relat_1(sK2) = sK1
% 2.77/0.99      | v3_funct_2(sK2,sK1,sK1) != iProver_top
% 2.77/0.99      | v1_funct_1(sK2) != iProver_top
% 2.77/0.99      | v1_relat_1(sK2) != iProver_top ),
% 2.77/0.99      inference(superposition,[status(thm)],[c_1093,c_1089]) ).
% 2.77/0.99  
% 2.77/0.99  cnf(c_1552,plain,
% 2.77/0.99      ( ~ v3_funct_2(sK2,sK1,sK1)
% 2.77/0.99      | ~ v1_funct_1(sK2)
% 2.77/0.99      | ~ v1_relat_1(sK2)
% 2.77/0.99      | k2_relat_1(sK2) = sK1 ),
% 2.77/0.99      inference(predicate_to_equality_rev,[status(thm)],[c_1551]) ).
% 2.77/0.99  
% 2.77/0.99  cnf(c_1892,plain,
% 2.77/0.99      ( k2_relat_1(sK2) = sK1 ),
% 2.77/0.99      inference(global_propositional_subsumption,
% 2.77/0.99                [status(thm)],
% 2.77/0.99                [c_1551,c_29,c_27,c_26,c_103,c_1552,c_1642]) ).
% 2.77/0.99  
% 2.77/0.99  cnf(c_2275,plain,
% 2.77/0.99      ( k5_relat_1(k2_funct_1(sK2),sK2) = k6_partfun1(sK1)
% 2.77/0.99      | v2_funct_1(sK2) != iProver_top
% 2.77/0.99      | v1_relat_1(sK2) != iProver_top ),
% 2.77/0.99      inference(light_normalisation,[status(thm)],[c_2271,c_1892]) ).
% 2.77/0.99  
% 2.77/0.99  cnf(c_102,plain,
% 2.77/0.99      ( v1_relat_1(k2_zfmisc_1(X0,X1)) = iProver_top ),
% 2.77/0.99      inference(predicate_to_equality,[status(thm)],[c_1]) ).
% 2.77/0.99  
% 2.77/0.99  cnf(c_104,plain,
% 2.77/0.99      ( v1_relat_1(k2_zfmisc_1(sK1,sK1)) = iProver_top ),
% 2.77/0.99      inference(instantiation,[status(thm)],[c_102]) ).
% 2.77/0.99  
% 2.77/0.99  cnf(c_1366,plain,
% 2.77/0.99      ( v3_funct_2(sK2,X0,X1) != iProver_top
% 2.77/0.99      | m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top
% 2.77/0.99      | v1_funct_1(sK2) != iProver_top
% 2.77/0.99      | v2_funct_1(sK2) = iProver_top ),
% 2.77/0.99      inference(predicate_to_equality,[status(thm)],[c_1365]) ).
% 2.77/0.99  
% 2.77/0.99  cnf(c_1368,plain,
% 2.77/0.99      ( v3_funct_2(sK2,sK1,sK1) != iProver_top
% 2.77/0.99      | m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK1,sK1))) != iProver_top
% 2.77/0.99      | v1_funct_1(sK2) != iProver_top
% 2.77/0.99      | v2_funct_1(sK2) = iProver_top ),
% 2.77/0.99      inference(instantiation,[status(thm)],[c_1366]) ).
% 2.77/0.99  
% 2.77/0.99  cnf(c_1643,plain,
% 2.77/0.99      ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK1,sK1))) != iProver_top
% 2.77/0.99      | v1_relat_1(k2_zfmisc_1(sK1,sK1)) != iProver_top
% 2.77/0.99      | v1_relat_1(sK2) = iProver_top ),
% 2.77/0.99      inference(predicate_to_equality,[status(thm)],[c_1642]) ).
% 2.77/0.99  
% 2.77/0.99  cnf(c_3722,plain,
% 2.77/0.99      ( k5_relat_1(k2_funct_1(sK2),sK2) = k6_partfun1(sK1) ),
% 2.77/0.99      inference(global_propositional_subsumption,
% 2.77/0.99                [status(thm)],
% 2.77/0.99                [c_2275,c_30,c_32,c_33,c_104,c_1368,c_1643]) ).
% 2.77/0.99  
% 2.77/0.99  cnf(c_4340,plain,
% 2.77/0.99      ( k1_partfun1(sK1,sK1,sK1,sK1,k2_funct_1(sK2),sK2) = k6_partfun1(sK1)
% 2.77/0.99      | v1_funct_2(sK2,sK1,sK1) != iProver_top
% 2.77/0.99      | v3_funct_2(sK2,sK1,sK1) != iProver_top
% 2.77/0.99      | v1_funct_1(sK2) != iProver_top ),
% 2.77/0.99      inference(light_normalisation,[status(thm)],[c_4326,c_2815,c_3722]) ).
% 2.77/0.99  
% 2.77/0.99  cnf(c_4206,plain,
% 2.77/0.99      ( k1_partfun1(sK1,sK1,sK1,sK1,k2_funct_1(sK2),sK2) = k5_relat_1(k2_funct_1(sK2),sK2)
% 2.77/0.99      | v1_funct_1(k2_funct_1(sK2)) != iProver_top ),
% 2.77/0.99      inference(superposition,[status(thm)],[c_4198,c_3634]) ).
% 2.77/0.99  
% 2.77/0.99  cnf(c_4276,plain,
% 2.77/0.99      ( k1_partfun1(sK1,sK1,sK1,sK1,k2_funct_1(sK2),sK2) = k6_partfun1(sK1)
% 2.77/0.99      | v1_funct_1(k2_funct_1(sK2)) != iProver_top ),
% 2.77/0.99      inference(light_normalisation,[status(thm)],[c_4206,c_3722]) ).
% 2.77/0.99  
% 2.77/0.99  cnf(c_4462,plain,
% 2.77/0.99      ( k1_partfun1(sK1,sK1,sK1,sK1,k2_funct_1(sK2),sK2) = k6_partfun1(sK1) ),
% 2.77/0.99      inference(global_propositional_subsumption,
% 2.77/0.99                [status(thm)],
% 2.77/0.99                [c_4340,c_30,c_31,c_32,c_3185,c_4276]) ).
% 2.77/0.99  
% 2.77/0.99  cnf(c_25,negated_conjecture,
% 2.77/0.99      ( ~ r2_relset_1(sK1,sK1,k1_partfun1(sK1,sK1,sK1,sK1,k2_funct_2(sK1,sK2),sK2),k6_partfun1(sK1))
% 2.77/0.99      | ~ r2_relset_1(sK1,sK1,k1_partfun1(sK1,sK1,sK1,sK1,sK2,k2_funct_2(sK1,sK2)),k6_partfun1(sK1)) ),
% 2.77/0.99      inference(cnf_transformation,[],[f77]) ).
% 2.77/0.99  
% 2.77/0.99  cnf(c_1094,plain,
% 2.77/0.99      ( r2_relset_1(sK1,sK1,k1_partfun1(sK1,sK1,sK1,sK1,k2_funct_2(sK1,sK2),sK2),k6_partfun1(sK1)) != iProver_top
% 2.77/0.99      | r2_relset_1(sK1,sK1,k1_partfun1(sK1,sK1,sK1,sK1,sK2,k2_funct_2(sK1,sK2)),k6_partfun1(sK1)) != iProver_top ),
% 2.77/0.99      inference(predicate_to_equality,[status(thm)],[c_25]) ).
% 2.77/0.99  
% 2.77/0.99  cnf(c_2818,plain,
% 2.77/0.99      ( r2_relset_1(sK1,sK1,k1_partfun1(sK1,sK1,sK1,sK1,k2_funct_1(sK2),sK2),k6_partfun1(sK1)) != iProver_top
% 2.77/0.99      | r2_relset_1(sK1,sK1,k1_partfun1(sK1,sK1,sK1,sK1,sK2,k2_funct_1(sK2)),k6_partfun1(sK1)) != iProver_top ),
% 2.77/0.99      inference(demodulation,[status(thm)],[c_2815,c_1094]) ).
% 2.77/0.99  
% 2.77/0.99  cnf(c_4465,plain,
% 2.77/0.99      ( r2_relset_1(sK1,sK1,k1_partfun1(sK1,sK1,sK1,sK1,sK2,k2_funct_1(sK2)),k6_partfun1(sK1)) != iProver_top
% 2.77/0.99      | r2_relset_1(sK1,sK1,k6_partfun1(sK1),k6_partfun1(sK1)) != iProver_top ),
% 2.77/0.99      inference(demodulation,[status(thm)],[c_4462,c_2818]) ).
% 2.77/0.99  
% 2.77/0.99  cnf(c_16,plain,
% 2.77/0.99      ( m1_subset_1(k6_partfun1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0))) ),
% 2.77/0.99      inference(cnf_transformation,[],[f63]) ).
% 2.77/0.99  
% 2.77/0.99  cnf(c_59,plain,
% 2.77/0.99      ( m1_subset_1(k6_partfun1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0))) = iProver_top ),
% 2.77/0.99      inference(predicate_to_equality,[status(thm)],[c_16]) ).
% 2.77/0.99  
% 2.77/0.99  cnf(c_61,plain,
% 2.77/0.99      ( m1_subset_1(k6_partfun1(sK1),k1_zfmisc_1(k2_zfmisc_1(sK1,sK1))) = iProver_top ),
% 2.77/0.99      inference(instantiation,[status(thm)],[c_59]) ).
% 2.77/0.99  
% 2.77/0.99  cnf(c_6,plain,
% 2.77/0.99      ( r2_relset_1(X0,X1,X2,X2)
% 2.77/0.99      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
% 2.77/0.99      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ),
% 2.77/0.99      inference(cnf_transformation,[],[f53]) ).
% 2.77/0.99  
% 2.77/0.99  cnf(c_1389,plain,
% 2.77/0.99      ( r2_relset_1(X0,X0,k6_partfun1(X0),k6_partfun1(X0))
% 2.77/0.99      | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
% 2.77/0.99      | ~ m1_subset_1(k6_partfun1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0))) ),
% 2.77/0.99      inference(instantiation,[status(thm)],[c_6]) ).
% 2.77/0.99  
% 2.77/0.99  cnf(c_1774,plain,
% 2.77/0.99      ( r2_relset_1(X0,X0,k6_partfun1(X0),k6_partfun1(X0))
% 2.77/0.99      | ~ m1_subset_1(k6_partfun1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0))) ),
% 2.77/0.99      inference(instantiation,[status(thm)],[c_1389]) ).
% 2.77/0.99  
% 2.77/0.99  cnf(c_1775,plain,
% 2.77/0.99      ( r2_relset_1(X0,X0,k6_partfun1(X0),k6_partfun1(X0)) = iProver_top
% 2.77/0.99      | m1_subset_1(k6_partfun1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0))) != iProver_top ),
% 2.77/0.99      inference(predicate_to_equality,[status(thm)],[c_1774]) ).
% 2.77/0.99  
% 2.77/0.99  cnf(c_1777,plain,
% 2.77/0.99      ( r2_relset_1(sK1,sK1,k6_partfun1(sK1),k6_partfun1(sK1)) = iProver_top
% 2.77/0.99      | m1_subset_1(k6_partfun1(sK1),k1_zfmisc_1(k2_zfmisc_1(sK1,sK1))) != iProver_top ),
% 2.77/0.99      inference(instantiation,[status(thm)],[c_1775]) ).
% 2.77/0.99  
% 2.77/0.99  cnf(c_4468,plain,
% 2.77/0.99      ( r2_relset_1(sK1,sK1,k1_partfun1(sK1,sK1,sK1,sK1,sK2,k2_funct_1(sK2)),k6_partfun1(sK1)) != iProver_top ),
% 2.77/0.99      inference(global_propositional_subsumption,
% 2.77/0.99                [status(thm)],
% 2.77/0.99                [c_4465,c_61,c_1777]) ).
% 2.77/0.99  
% 2.77/0.99  cnf(c_5795,plain,
% 2.77/0.99      ( r2_relset_1(sK1,sK1,k6_partfun1(sK1),k6_partfun1(sK1)) != iProver_top ),
% 2.77/0.99      inference(demodulation,[status(thm)],[c_5792,c_4468]) ).
% 2.77/0.99  
% 2.77/0.99  cnf(contradiction,plain,
% 2.77/0.99      ( $false ),
% 2.77/0.99      inference(minisat,[status(thm)],[c_5795,c_1777,c_61]) ).
% 2.77/0.99  
% 2.77/0.99  
% 2.77/0.99  % SZS output end CNFRefutation for theBenchmark.p
% 2.77/0.99  
% 2.77/0.99  ------                               Statistics
% 2.77/0.99  
% 2.77/0.99  ------ General
% 2.77/0.99  
% 2.77/0.99  abstr_ref_over_cycles:                  0
% 2.77/0.99  abstr_ref_under_cycles:                 0
% 2.77/0.99  gc_basic_clause_elim:                   0
% 2.77/0.99  forced_gc_time:                         0
% 2.77/0.99  parsing_time:                           0.008
% 2.77/0.99  unif_index_cands_time:                  0.
% 2.77/0.99  unif_index_add_time:                    0.
% 2.77/0.99  orderings_time:                         0.
% 2.77/0.99  out_proof_time:                         0.011
% 2.77/0.99  total_time:                             0.158
% 2.77/0.99  num_of_symbols:                         53
% 2.77/0.99  num_of_terms:                           8557
% 2.77/0.99  
% 2.77/0.99  ------ Preprocessing
% 2.77/0.99  
% 2.77/0.99  num_of_splits:                          0
% 2.77/0.99  num_of_split_atoms:                     0
% 2.77/0.99  num_of_reused_defs:                     0
% 2.77/0.99  num_eq_ax_congr_red:                    28
% 2.77/0.99  num_of_sem_filtered_clauses:            1
% 2.77/0.99  num_of_subtypes:                        0
% 2.77/0.99  monotx_restored_types:                  0
% 2.77/0.99  sat_num_of_epr_types:                   0
% 2.77/0.99  sat_num_of_non_cyclic_types:            0
% 2.77/0.99  sat_guarded_non_collapsed_types:        0
% 2.77/0.99  num_pure_diseq_elim:                    0
% 2.77/0.99  simp_replaced_by:                       0
% 2.77/0.99  res_preprocessed:                       133
% 2.77/0.99  prep_upred:                             0
% 2.77/0.99  prep_unflattend:                        4
% 2.77/0.99  smt_new_axioms:                         0
% 2.77/0.99  pred_elim_cands:                        7
% 2.77/0.99  pred_elim:                              2
% 2.77/0.99  pred_elim_cl:                           4
% 2.77/0.99  pred_elim_cycles:                       4
% 2.77/0.99  merged_defs:                            0
% 2.77/0.99  merged_defs_ncl:                        0
% 2.77/0.99  bin_hyper_res:                          0
% 2.77/0.99  prep_cycles:                            4
% 2.77/0.99  pred_elim_time:                         0.002
% 2.77/0.99  splitting_time:                         0.
% 2.77/0.99  sem_filter_time:                        0.
% 2.77/0.99  monotx_time:                            0.
% 2.77/0.99  subtype_inf_time:                       0.
% 2.77/0.99  
% 2.77/0.99  ------ Problem properties
% 2.77/0.99  
% 2.77/0.99  clauses:                                25
% 2.77/0.99  conjectures:                            5
% 2.77/0.99  epr:                                    3
% 2.77/0.99  horn:                                   25
% 2.77/0.99  ground:                                 5
% 2.77/0.99  unary:                                  10
% 2.77/0.99  binary:                                 2
% 2.77/0.99  lits:                                   71
% 2.77/0.99  lits_eq:                                7
% 2.77/0.99  fd_pure:                                0
% 2.77/0.99  fd_pseudo:                              0
% 2.77/0.99  fd_cond:                                0
% 2.77/0.99  fd_pseudo_cond:                         1
% 2.77/0.99  ac_symbols:                             0
% 2.77/0.99  
% 2.77/0.99  ------ Propositional Solver
% 2.77/0.99  
% 2.77/0.99  prop_solver_calls:                      27
% 2.77/0.99  prop_fast_solver_calls:                 1065
% 2.77/0.99  smt_solver_calls:                       0
% 2.77/0.99  smt_fast_solver_calls:                  0
% 2.77/0.99  prop_num_of_clauses:                    2268
% 2.77/0.99  prop_preprocess_simplified:             6067
% 2.77/0.99  prop_fo_subsumed:                       66
% 2.77/0.99  prop_solver_time:                       0.
% 2.77/0.99  smt_solver_time:                        0.
% 2.77/0.99  smt_fast_solver_time:                   0.
% 2.77/0.99  prop_fast_solver_time:                  0.
% 2.77/0.99  prop_unsat_core_time:                   0.
% 2.77/0.99  
% 2.77/0.99  ------ QBF
% 2.77/0.99  
% 2.77/0.99  qbf_q_res:                              0
% 2.77/0.99  qbf_num_tautologies:                    0
% 2.77/0.99  qbf_prep_cycles:                        0
% 2.77/0.99  
% 2.77/0.99  ------ BMC1
% 2.77/0.99  
% 2.77/0.99  bmc1_current_bound:                     -1
% 2.77/0.99  bmc1_last_solved_bound:                 -1
% 2.77/0.99  bmc1_unsat_core_size:                   -1
% 2.77/0.99  bmc1_unsat_core_parents_size:           -1
% 2.77/0.99  bmc1_merge_next_fun:                    0
% 2.77/0.99  bmc1_unsat_core_clauses_time:           0.
% 2.77/0.99  
% 2.77/0.99  ------ Instantiation
% 2.77/0.99  
% 2.77/0.99  inst_num_of_clauses:                    600
% 2.77/0.99  inst_num_in_passive:                    253
% 2.77/0.99  inst_num_in_active:                     347
% 2.77/0.99  inst_num_in_unprocessed:                0
% 2.77/0.99  inst_num_of_loops:                      360
% 2.77/0.99  inst_num_of_learning_restarts:          0
% 2.77/0.99  inst_num_moves_active_passive:          9
% 2.77/0.99  inst_lit_activity:                      0
% 2.77/0.99  inst_lit_activity_moves:                0
% 2.77/0.99  inst_num_tautologies:                   0
% 2.77/0.99  inst_num_prop_implied:                  0
% 2.77/0.99  inst_num_existing_simplified:           0
% 2.77/0.99  inst_num_eq_res_simplified:             0
% 2.77/0.99  inst_num_child_elim:                    0
% 2.77/0.99  inst_num_of_dismatching_blockings:      248
% 2.77/0.99  inst_num_of_non_proper_insts:           499
% 2.77/0.99  inst_num_of_duplicates:                 0
% 2.77/0.99  inst_inst_num_from_inst_to_res:         0
% 2.77/0.99  inst_dismatching_checking_time:         0.
% 2.77/0.99  
% 2.77/0.99  ------ Resolution
% 2.77/0.99  
% 2.77/0.99  res_num_of_clauses:                     0
% 2.77/0.99  res_num_in_passive:                     0
% 2.77/0.99  res_num_in_active:                      0
% 2.77/0.99  res_num_of_loops:                       137
% 2.77/0.99  res_forward_subset_subsumed:            21
% 2.77/0.99  res_backward_subset_subsumed:           2
% 2.77/0.99  res_forward_subsumed:                   0
% 2.77/0.99  res_backward_subsumed:                  0
% 2.77/0.99  res_forward_subsumption_resolution:     1
% 2.77/0.99  res_backward_subsumption_resolution:    0
% 2.77/0.99  res_clause_to_clause_subsumption:       165
% 2.77/0.99  res_orphan_elimination:                 0
% 2.77/0.99  res_tautology_del:                      39
% 2.77/0.99  res_num_eq_res_simplified:              0
% 2.77/0.99  res_num_sel_changes:                    0
% 2.77/0.99  res_moves_from_active_to_pass:          0
% 2.77/0.99  
% 2.77/0.99  ------ Superposition
% 2.77/0.99  
% 2.77/0.99  sup_time_total:                         0.
% 2.77/0.99  sup_time_generating:                    0.
% 2.77/0.99  sup_time_sim_full:                      0.
% 2.77/0.99  sup_time_sim_immed:                     0.
% 2.77/0.99  
% 2.77/0.99  sup_num_of_clauses:                     103
% 2.77/0.99  sup_num_in_active:                      62
% 2.77/0.99  sup_num_in_passive:                     41
% 2.77/0.99  sup_num_of_loops:                       70
% 2.77/0.99  sup_fw_superposition:                   55
% 2.77/0.99  sup_bw_superposition:                   30
% 2.77/0.99  sup_immediate_simplified:               14
% 2.77/0.99  sup_given_eliminated:                   0
% 2.77/0.99  comparisons_done:                       0
% 2.77/0.99  comparisons_avoided:                    0
% 2.77/0.99  
% 2.77/0.99  ------ Simplifications
% 2.77/0.99  
% 2.77/0.99  
% 2.77/0.99  sim_fw_subset_subsumed:                 2
% 2.77/0.99  sim_bw_subset_subsumed:                 3
% 2.77/0.99  sim_fw_subsumed:                        0
% 2.77/0.99  sim_bw_subsumed:                        0
% 2.77/0.99  sim_fw_subsumption_res:                 2
% 2.77/0.99  sim_bw_subsumption_res:                 0
% 2.77/0.99  sim_tautology_del:                      0
% 2.77/0.99  sim_eq_tautology_del:                   0
% 2.77/0.99  sim_eq_res_simp:                        0
% 2.77/0.99  sim_fw_demodulated:                     3
% 2.77/0.99  sim_bw_demodulated:                     8
% 2.77/0.99  sim_light_normalised:                   9
% 2.77/0.99  sim_joinable_taut:                      0
% 2.77/0.99  sim_joinable_simp:                      0
% 2.77/0.99  sim_ac_normalised:                      0
% 2.77/0.99  sim_smt_subsumption:                    0
% 2.77/0.99  
%------------------------------------------------------------------------------
