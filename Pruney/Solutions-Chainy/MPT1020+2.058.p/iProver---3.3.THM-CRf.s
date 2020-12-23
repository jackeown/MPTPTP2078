%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n009.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:07:16 EST 2020

% Result     : Theorem 2.18s
% Output     : CNFRefutation 2.18s
% Verified   : 
% Statistics : Number of formulae       :  192 (3657 expanded)
%              Number of clauses        :  124 (1088 expanded)
%              Number of leaves         :   19 ( 887 expanded)
%              Depth                    :   30
%              Number of atoms          :  645 (25079 expanded)
%              Number of equality atoms :  238 (1645 expanded)
%              Maximal formula depth    :   17 (   4 average)
%              Maximal clause size      :   20 (   3 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f15,conjecture,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
        & v3_funct_2(X1,X0,X0)
        & v1_funct_2(X1,X0,X0)
        & v1_funct_1(X1) )
     => ! [X2] :
          ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
            & v3_funct_2(X2,X0,X0)
            & v1_funct_2(X2,X0,X0)
            & v1_funct_1(X2) )
         => ( r2_relset_1(X0,X0,k1_partfun1(X0,X0,X0,X0,X1,X2),k6_partfun1(X0))
           => r2_relset_1(X0,X0,X2,k2_funct_2(X0,X1)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f16,negated_conjecture,(
    ~ ! [X0,X1] :
        ( ( m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
          & v3_funct_2(X1,X0,X0)
          & v1_funct_2(X1,X0,X0)
          & v1_funct_1(X1) )
       => ! [X2] :
            ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
              & v3_funct_2(X2,X0,X0)
              & v1_funct_2(X2,X0,X0)
              & v1_funct_1(X2) )
           => ( r2_relset_1(X0,X0,k1_partfun1(X0,X0,X0,X0,X1,X2),k6_partfun1(X0))
             => r2_relset_1(X0,X0,X2,k2_funct_2(X0,X1)) ) ) ) ),
    inference(negated_conjecture,[],[f15])).

fof(f35,plain,(
    ? [X0,X1] :
      ( ? [X2] :
          ( ~ r2_relset_1(X0,X0,X2,k2_funct_2(X0,X1))
          & r2_relset_1(X0,X0,k1_partfun1(X0,X0,X0,X0,X1,X2),k6_partfun1(X0))
          & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
          & v3_funct_2(X2,X0,X0)
          & v1_funct_2(X2,X0,X0)
          & v1_funct_1(X2) )
      & m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
      & v3_funct_2(X1,X0,X0)
      & v1_funct_2(X1,X0,X0)
      & v1_funct_1(X1) ) ),
    inference(ennf_transformation,[],[f16])).

fof(f36,plain,(
    ? [X0,X1] :
      ( ? [X2] :
          ( ~ r2_relset_1(X0,X0,X2,k2_funct_2(X0,X1))
          & r2_relset_1(X0,X0,k1_partfun1(X0,X0,X0,X0,X1,X2),k6_partfun1(X0))
          & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
          & v3_funct_2(X2,X0,X0)
          & v1_funct_2(X2,X0,X0)
          & v1_funct_1(X2) )
      & m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
      & v3_funct_2(X1,X0,X0)
      & v1_funct_2(X1,X0,X0)
      & v1_funct_1(X1) ) ),
    inference(flattening,[],[f35])).

fof(f40,plain,(
    ! [X0,X1] :
      ( ? [X2] :
          ( ~ r2_relset_1(X0,X0,X2,k2_funct_2(X0,X1))
          & r2_relset_1(X0,X0,k1_partfun1(X0,X0,X0,X0,X1,X2),k6_partfun1(X0))
          & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
          & v3_funct_2(X2,X0,X0)
          & v1_funct_2(X2,X0,X0)
          & v1_funct_1(X2) )
     => ( ~ r2_relset_1(X0,X0,sK2,k2_funct_2(X0,X1))
        & r2_relset_1(X0,X0,k1_partfun1(X0,X0,X0,X0,X1,sK2),k6_partfun1(X0))
        & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
        & v3_funct_2(sK2,X0,X0)
        & v1_funct_2(sK2,X0,X0)
        & v1_funct_1(sK2) ) ) ),
    introduced(choice_axiom,[])).

fof(f39,plain,
    ( ? [X0,X1] :
        ( ? [X2] :
            ( ~ r2_relset_1(X0,X0,X2,k2_funct_2(X0,X1))
            & r2_relset_1(X0,X0,k1_partfun1(X0,X0,X0,X0,X1,X2),k6_partfun1(X0))
            & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
            & v3_funct_2(X2,X0,X0)
            & v1_funct_2(X2,X0,X0)
            & v1_funct_1(X2) )
        & m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
        & v3_funct_2(X1,X0,X0)
        & v1_funct_2(X1,X0,X0)
        & v1_funct_1(X1) )
   => ( ? [X2] :
          ( ~ r2_relset_1(sK0,sK0,X2,k2_funct_2(sK0,sK1))
          & r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK0,sK0,sK0,sK1,X2),k6_partfun1(sK0))
          & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
          & v3_funct_2(X2,sK0,sK0)
          & v1_funct_2(X2,sK0,sK0)
          & v1_funct_1(X2) )
      & m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
      & v3_funct_2(sK1,sK0,sK0)
      & v1_funct_2(sK1,sK0,sK0)
      & v1_funct_1(sK1) ) ),
    introduced(choice_axiom,[])).

fof(f41,plain,
    ( ~ r2_relset_1(sK0,sK0,sK2,k2_funct_2(sK0,sK1))
    & r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK0,sK0,sK0,sK1,sK2),k6_partfun1(sK0))
    & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
    & v3_funct_2(sK2,sK0,sK0)
    & v1_funct_2(sK2,sK0,sK0)
    & v1_funct_1(sK2)
    & m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
    & v3_funct_2(sK1,sK0,sK0)
    & v1_funct_2(sK1,sK0,sK0)
    & v1_funct_1(sK1) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f36,f40,f39])).

fof(f70,plain,(
    r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK0,sK0,sK0,sK1,sK2),k6_partfun1(sK0)) ),
    inference(cnf_transformation,[],[f41])).

fof(f65,plain,(
    m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) ),
    inference(cnf_transformation,[],[f41])).

fof(f7,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k2_relat_1(X2) = k2_relset_1(X0,X1,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f22,plain,(
    ! [X0,X1,X2] :
      ( k2_relat_1(X2) = k2_relset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f49,plain,(
    ! [X2,X0,X1] :
      ( k2_relat_1(X2) = k2_relset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f6,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => ( v5_relat_1(X2,X1)
        & v4_relat_1(X2,X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f17,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => v5_relat_1(X2,X1) ) ),
    inference(pure_predicate_removal,[],[f6])).

fof(f21,plain,(
    ! [X0,X1,X2] :
      ( v5_relat_1(X2,X1)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f17])).

fof(f48,plain,(
    ! [X2,X0,X1] :
      ( v5_relat_1(X2,X1)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f10,axiom,(
    ! [X0,X1] :
      ( ( v5_relat_1(X1,X0)
        & v1_relat_1(X1) )
     => ( v2_funct_2(X1,X0)
      <=> k2_relat_1(X1) = X0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f27,plain,(
    ! [X0,X1] :
      ( ( v2_funct_2(X1,X0)
      <=> k2_relat_1(X1) = X0 )
      | ~ v5_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f28,plain,(
    ! [X0,X1] :
      ( ( v2_funct_2(X1,X0)
      <=> k2_relat_1(X1) = X0 )
      | ~ v5_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f27])).

fof(f38,plain,(
    ! [X0,X1] :
      ( ( ( v2_funct_2(X1,X0)
          | k2_relat_1(X1) != X0 )
        & ( k2_relat_1(X1) = X0
          | ~ v2_funct_2(X1,X0) ) )
      | ~ v5_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(nnf_transformation,[],[f28])).

fof(f55,plain,(
    ! [X0,X1] :
      ( k2_relat_1(X1) = X0
      | ~ v2_funct_2(X1,X0)
      | ~ v5_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f38])).

fof(f9,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => ( ( v3_funct_2(X2,X0,X1)
          & v1_funct_1(X2) )
       => ( v2_funct_2(X2,X1)
          & v2_funct_1(X2)
          & v1_funct_1(X2) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f25,plain,(
    ! [X0,X1,X2] :
      ( ( v2_funct_2(X2,X1)
        & v2_funct_1(X2)
        & v1_funct_1(X2) )
      | ~ v3_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f26,plain,(
    ! [X0,X1,X2] :
      ( ( v2_funct_2(X2,X1)
        & v2_funct_1(X2)
        & v1_funct_1(X2) )
      | ~ v3_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(flattening,[],[f25])).

fof(f54,plain,(
    ! [X2,X0,X1] :
      ( v2_funct_2(X2,X1)
      | ~ v3_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f64,plain,(
    v3_funct_2(sK1,sK0,sK0) ),
    inference(cnf_transformation,[],[f41])).

fof(f62,plain,(
    v1_funct_1(sK1) ),
    inference(cnf_transformation,[],[f41])).

fof(f2,axiom,(
    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f43,plain,(
    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1)) ),
    inference(cnf_transformation,[],[f2])).

fof(f1,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(X0))
         => v1_relat_1(X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f18,plain,(
    ! [X0] :
      ( ! [X1] :
          ( v1_relat_1(X1)
          | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f42,plain,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f14,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_2(X2,X0,X1)
        & v1_funct_1(X2) )
     => ! [X3] :
          ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
            & v1_funct_2(X3,X1,X0)
            & v1_funct_1(X3) )
         => ( ( v2_funct_1(X2)
              & r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0))
              & k2_relset_1(X0,X1,X2) = X1 )
           => ( k2_funct_1(X2) = X3
              | k1_xboole_0 = X1
              | k1_xboole_0 = X0 ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f33,plain,(
    ! [X0,X1,X2] :
      ( ! [X3] :
          ( k2_funct_1(X2) = X3
          | k1_xboole_0 = X1
          | k1_xboole_0 = X0
          | ~ v2_funct_1(X2)
          | ~ r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0))
          | k2_relset_1(X0,X1,X2) != X1
          | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
          | ~ v1_funct_2(X3,X1,X0)
          | ~ v1_funct_1(X3) )
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f34,plain,(
    ! [X0,X1,X2] :
      ( ! [X3] :
          ( k2_funct_1(X2) = X3
          | k1_xboole_0 = X1
          | k1_xboole_0 = X0
          | ~ v2_funct_1(X2)
          | ~ r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0))
          | k2_relset_1(X0,X1,X2) != X1
          | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
          | ~ v1_funct_2(X3,X1,X0)
          | ~ v1_funct_1(X3) )
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(flattening,[],[f33])).

fof(f61,plain,(
    ! [X2,X0,X3,X1] :
      ( k2_funct_1(X2) = X3
      | k1_xboole_0 = X1
      | k1_xboole_0 = X0
      | ~ v2_funct_1(X2)
      | ~ r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0))
      | k2_relset_1(X0,X1,X2) != X1
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
      | ~ v1_funct_2(X3,X1,X0)
      | ~ v1_funct_1(X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(cnf_transformation,[],[f34])).

fof(f13,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_2(X2,X0,X1)
        & v1_funct_1(X2) )
     => ! [X3] :
          ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
            & v1_funct_2(X3,X1,X0)
            & v1_funct_1(X3) )
         => ( r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0))
           => ( v2_funct_2(X3,X0)
              & v2_funct_1(X2) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f31,plain,(
    ! [X0,X1,X2] :
      ( ! [X3] :
          ( ( v2_funct_2(X3,X0)
            & v2_funct_1(X2) )
          | ~ r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0))
          | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
          | ~ v1_funct_2(X3,X1,X0)
          | ~ v1_funct_1(X3) )
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f32,plain,(
    ! [X0,X1,X2] :
      ( ! [X3] :
          ( ( v2_funct_2(X3,X0)
            & v2_funct_1(X2) )
          | ~ r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0))
          | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
          | ~ v1_funct_2(X3,X1,X0)
          | ~ v1_funct_1(X3) )
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(flattening,[],[f31])).

fof(f59,plain,(
    ! [X2,X0,X3,X1] :
      ( v2_funct_1(X2)
      | ~ r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0))
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
      | ~ v1_funct_2(X3,X1,X0)
      | ~ v1_funct_1(X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(cnf_transformation,[],[f32])).

fof(f63,plain,(
    v1_funct_2(sK1,sK0,sK0) ),
    inference(cnf_transformation,[],[f41])).

fof(f66,plain,(
    v1_funct_1(sK2) ),
    inference(cnf_transformation,[],[f41])).

fof(f67,plain,(
    v1_funct_2(sK2,sK0,sK0) ),
    inference(cnf_transformation,[],[f41])).

fof(f69,plain,(
    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) ),
    inference(cnf_transformation,[],[f41])).

fof(f71,plain,(
    ~ r2_relset_1(sK0,sK0,sK2,k2_funct_2(sK0,sK1)) ),
    inference(cnf_transformation,[],[f41])).

fof(f11,axiom,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
        & v3_funct_2(X1,X0,X0)
        & v1_funct_2(X1,X0,X0)
        & v1_funct_1(X1) )
     => k2_funct_1(X1) = k2_funct_2(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f29,plain,(
    ! [X0,X1] :
      ( k2_funct_1(X1) = k2_funct_2(X0,X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
      | ~ v3_funct_2(X1,X0,X0)
      | ~ v1_funct_2(X1,X0,X0)
      | ~ v1_funct_1(X1) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f30,plain,(
    ! [X0,X1] :
      ( k2_funct_1(X1) = k2_funct_2(X0,X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
      | ~ v3_funct_2(X1,X0,X0)
      | ~ v1_funct_2(X1,X0,X0)
      | ~ v1_funct_1(X1) ) ),
    inference(flattening,[],[f29])).

fof(f57,plain,(
    ! [X0,X1] :
      ( k2_funct_1(X1) = k2_funct_2(X0,X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
      | ~ v3_funct_2(X1,X0,X0)
      | ~ v1_funct_2(X1,X0,X0)
      | ~ v1_funct_1(X1) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f8,axiom,(
    ! [X0,X1,X2,X3] :
      ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) )
     => ( r2_relset_1(X0,X1,X2,X3)
      <=> X2 = X3 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f23,plain,(
    ! [X0,X1,X2,X3] :
      ( ( r2_relset_1(X0,X1,X2,X3)
      <=> X2 = X3 )
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f24,plain,(
    ! [X0,X1,X2,X3] :
      ( ( r2_relset_1(X0,X1,X2,X3)
      <=> X2 = X3 )
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(flattening,[],[f23])).

fof(f37,plain,(
    ! [X0,X1,X2,X3] :
      ( ( ( r2_relset_1(X0,X1,X2,X3)
          | X2 != X3 )
        & ( X2 = X3
          | ~ r2_relset_1(X0,X1,X2,X3) ) )
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(nnf_transformation,[],[f24])).

fof(f51,plain,(
    ! [X2,X0,X3,X1] :
      ( r2_relset_1(X0,X1,X2,X3)
      | X2 != X3
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f37])).

fof(f74,plain,(
    ! [X0,X3,X1] :
      ( r2_relset_1(X0,X1,X3,X3)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(equality_resolution,[],[f51])).

fof(f68,plain,(
    v3_funct_2(sK2,sK0,sK0) ),
    inference(cnf_transformation,[],[f41])).

fof(f3,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ( ( k1_xboole_0 = k2_relat_1(X0)
          | k1_relat_1(X0) = k1_xboole_0 )
       => k1_xboole_0 = X0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f19,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | ( k1_xboole_0 != k2_relat_1(X0)
        & k1_relat_1(X0) != k1_xboole_0 )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f20,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | ( k1_xboole_0 != k2_relat_1(X0)
        & k1_relat_1(X0) != k1_xboole_0 )
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f19])).

fof(f45,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | k1_xboole_0 != k2_relat_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f4,axiom,(
    k1_xboole_0 = k6_relat_1(k1_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f46,plain,(
    k1_xboole_0 = k6_relat_1(k1_xboole_0) ),
    inference(cnf_transformation,[],[f4])).

fof(f12,axiom,(
    ! [X0] : k6_relat_1(X0) = k6_partfun1(X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f58,plain,(
    ! [X0] : k6_relat_1(X0) = k6_partfun1(X0) ),
    inference(cnf_transformation,[],[f12])).

fof(f72,plain,(
    k1_xboole_0 = k6_partfun1(k1_xboole_0) ),
    inference(definition_unfolding,[],[f46,f58])).

fof(f5,axiom,(
    ! [X0] : k6_relat_1(X0) = k2_funct_1(k6_relat_1(X0)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f47,plain,(
    ! [X0] : k6_relat_1(X0) = k2_funct_1(k6_relat_1(X0)) ),
    inference(cnf_transformation,[],[f5])).

fof(f73,plain,(
    ! [X0] : k2_funct_1(k6_partfun1(X0)) = k6_partfun1(X0) ),
    inference(definition_unfolding,[],[f47,f58,f58])).

cnf(c_20,negated_conjecture,
    ( r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK0,sK0,sK0,sK1,sK2),k6_partfun1(sK0)) ),
    inference(cnf_transformation,[],[f70])).

cnf(c_1075,negated_conjecture,
    ( r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK0,sK0,sK0,sK1,sK2),k6_partfun1(sK0)) ),
    inference(subtyping,[status(esa)],[c_20])).

cnf(c_1475,plain,
    ( r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK0,sK0,sK0,sK1,sK2),k6_partfun1(sK0)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1075])).

cnf(c_25,negated_conjecture,
    ( m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) ),
    inference(cnf_transformation,[],[f65])).

cnf(c_1071,negated_conjecture,
    ( m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) ),
    inference(subtyping,[status(esa)],[c_25])).

cnf(c_1479,plain,
    ( m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1071])).

cnf(c_7,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k2_relset_1(X1,X2,X0) = k2_relat_1(X0) ),
    inference(cnf_transformation,[],[f49])).

cnf(c_1079,plain,
    ( ~ m1_subset_1(X0_50,k1_zfmisc_1(k2_zfmisc_1(X1_50,X2_50)))
    | k2_relset_1(X1_50,X2_50,X0_50) = k2_relat_1(X0_50) ),
    inference(subtyping,[status(esa)],[c_7])).

cnf(c_1471,plain,
    ( k2_relset_1(X0_50,X1_50,X2_50) = k2_relat_1(X2_50)
    | m1_subset_1(X2_50,k1_zfmisc_1(k2_zfmisc_1(X0_50,X1_50))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1079])).

cnf(c_2484,plain,
    ( k2_relset_1(sK0,sK0,sK1) = k2_relat_1(sK1) ),
    inference(superposition,[status(thm)],[c_1479,c_1471])).

cnf(c_6,plain,
    ( v5_relat_1(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) ),
    inference(cnf_transformation,[],[f48])).

cnf(c_14,plain,
    ( ~ v2_funct_2(X0,X1)
    | ~ v5_relat_1(X0,X1)
    | ~ v1_relat_1(X0)
    | k2_relat_1(X0) = X1 ),
    inference(cnf_transformation,[],[f55])).

cnf(c_10,plain,
    ( ~ v3_funct_2(X0,X1,X2)
    | v2_funct_2(X0,X2)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ v1_funct_1(X0) ),
    inference(cnf_transformation,[],[f54])).

cnf(c_26,negated_conjecture,
    ( v3_funct_2(sK1,sK0,sK0) ),
    inference(cnf_transformation,[],[f64])).

cnf(c_345,plain,
    ( v2_funct_2(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X2,X1)))
    | ~ v1_funct_1(X0)
    | sK1 != X0
    | sK0 != X1
    | sK0 != X2 ),
    inference(resolution_lifted,[status(thm)],[c_10,c_26])).

cnf(c_346,plain,
    ( v2_funct_2(sK1,sK0)
    | ~ m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
    | ~ v1_funct_1(sK1) ),
    inference(unflattening,[status(thm)],[c_345])).

cnf(c_28,negated_conjecture,
    ( v1_funct_1(sK1) ),
    inference(cnf_transformation,[],[f62])).

cnf(c_348,plain,
    ( v2_funct_2(sK1,sK0) ),
    inference(global_propositional_subsumption,[status(thm)],[c_346,c_28,c_25])).

cnf(c_431,plain,
    ( ~ v5_relat_1(X0,X1)
    | ~ v1_relat_1(X0)
    | k2_relat_1(X0) = X1
    | sK1 != X0
    | sK0 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_14,c_348])).

cnf(c_432,plain,
    ( ~ v5_relat_1(sK1,sK0)
    | ~ v1_relat_1(sK1)
    | k2_relat_1(sK1) = sK0 ),
    inference(unflattening,[status(thm)],[c_431])).

cnf(c_478,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ v1_relat_1(sK1)
    | k2_relat_1(sK1) = sK0
    | sK1 != X0
    | sK0 != X2 ),
    inference(resolution_lifted,[status(thm)],[c_6,c_432])).

cnf(c_479,plain,
    ( ~ m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(X0,sK0)))
    | ~ v1_relat_1(sK1)
    | k2_relat_1(sK1) = sK0 ),
    inference(unflattening,[status(thm)],[c_478])).

cnf(c_481,plain,
    ( ~ m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
    | ~ v1_relat_1(sK1)
    | k2_relat_1(sK1) = sK0 ),
    inference(instantiation,[status(thm)],[c_479])).

cnf(c_483,plain,
    ( ~ v1_relat_1(sK1)
    | k2_relat_1(sK1) = sK0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_479,c_25,c_481])).

cnf(c_1063,plain,
    ( ~ v1_relat_1(sK1)
    | k2_relat_1(sK1) = sK0 ),
    inference(subtyping,[status(esa)],[c_483])).

cnf(c_1485,plain,
    ( k2_relat_1(sK1) = sK0
    | v1_relat_1(sK1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1063])).

cnf(c_1,plain,
    ( v1_relat_1(k2_zfmisc_1(X0,X1)) ),
    inference(cnf_transformation,[],[f43])).

cnf(c_84,plain,
    ( v1_relat_1(k2_zfmisc_1(sK0,sK0)) ),
    inference(instantiation,[status(thm)],[c_1])).

cnf(c_0,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | ~ v1_relat_1(X1)
    | v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f42])).

cnf(c_1085,plain,
    ( ~ m1_subset_1(X0_50,k1_zfmisc_1(X1_50))
    | ~ v1_relat_1(X1_50)
    | v1_relat_1(X0_50) ),
    inference(subtyping,[status(esa)],[c_0])).

cnf(c_1642,plain,
    ( ~ m1_subset_1(X0_50,k1_zfmisc_1(k2_zfmisc_1(X1_50,X2_50)))
    | v1_relat_1(X0_50)
    | ~ v1_relat_1(k2_zfmisc_1(X1_50,X2_50)) ),
    inference(instantiation,[status(thm)],[c_1085])).

cnf(c_1845,plain,
    ( ~ m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
    | ~ v1_relat_1(k2_zfmisc_1(sK0,sK0))
    | v1_relat_1(sK1) ),
    inference(instantiation,[status(thm)],[c_1642])).

cnf(c_2008,plain,
    ( k2_relat_1(sK1) = sK0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_1485,c_25,c_84,c_1063,c_1845])).

cnf(c_2486,plain,
    ( k2_relset_1(sK0,sK0,sK1) = sK0 ),
    inference(light_normalisation,[status(thm)],[c_2484,c_2008])).

cnf(c_18,plain,
    ( ~ r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0))
    | ~ v1_funct_2(X3,X1,X0)
    | ~ v1_funct_2(X2,X0,X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
    | ~ v2_funct_1(X2)
    | ~ v1_funct_1(X2)
    | ~ v1_funct_1(X3)
    | k2_relset_1(X0,X1,X2) != X1
    | k2_funct_1(X2) = X3
    | k1_xboole_0 = X0
    | k1_xboole_0 = X1 ),
    inference(cnf_transformation,[],[f61])).

cnf(c_17,plain,
    ( ~ r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0))
    | ~ v1_funct_2(X3,X1,X0)
    | ~ v1_funct_2(X2,X0,X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
    | v2_funct_1(X2)
    | ~ v1_funct_1(X2)
    | ~ v1_funct_1(X3) ),
    inference(cnf_transformation,[],[f59])).

cnf(c_152,plain,
    ( ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
    | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
    | ~ v1_funct_2(X2,X0,X1)
    | ~ v1_funct_2(X3,X1,X0)
    | ~ r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0))
    | ~ v1_funct_1(X2)
    | ~ v1_funct_1(X3)
    | k2_relset_1(X0,X1,X2) != X1
    | k2_funct_1(X2) = X3
    | k1_xboole_0 = X0
    | k1_xboole_0 = X1 ),
    inference(global_propositional_subsumption,[status(thm)],[c_18,c_17])).

cnf(c_153,plain,
    ( ~ r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0))
    | ~ v1_funct_2(X3,X1,X0)
    | ~ v1_funct_2(X2,X0,X1)
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
    | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
    | ~ v1_funct_1(X2)
    | ~ v1_funct_1(X3)
    | k2_relset_1(X0,X1,X2) != X1
    | k2_funct_1(X2) = X3
    | k1_xboole_0 = X1
    | k1_xboole_0 = X0 ),
    inference(renaming,[status(thm)],[c_152])).

cnf(c_1068,plain,
    ( ~ r2_relset_1(X0_50,X0_50,k1_partfun1(X0_50,X1_50,X1_50,X0_50,X2_50,X3_50),k6_partfun1(X0_50))
    | ~ v1_funct_2(X3_50,X1_50,X0_50)
    | ~ v1_funct_2(X2_50,X0_50,X1_50)
    | ~ m1_subset_1(X3_50,k1_zfmisc_1(k2_zfmisc_1(X1_50,X0_50)))
    | ~ m1_subset_1(X2_50,k1_zfmisc_1(k2_zfmisc_1(X0_50,X1_50)))
    | ~ v1_funct_1(X2_50)
    | ~ v1_funct_1(X3_50)
    | k2_relset_1(X0_50,X1_50,X2_50) != X1_50
    | k2_funct_1(X2_50) = X3_50
    | k1_xboole_0 = X1_50
    | k1_xboole_0 = X0_50 ),
    inference(subtyping,[status(esa)],[c_153])).

cnf(c_1482,plain,
    ( k2_relset_1(X0_50,X1_50,X2_50) != X1_50
    | k2_funct_1(X2_50) = X3_50
    | k1_xboole_0 = X1_50
    | k1_xboole_0 = X0_50
    | r2_relset_1(X0_50,X0_50,k1_partfun1(X0_50,X1_50,X1_50,X0_50,X2_50,X3_50),k6_partfun1(X0_50)) != iProver_top
    | v1_funct_2(X3_50,X1_50,X0_50) != iProver_top
    | v1_funct_2(X2_50,X0_50,X1_50) != iProver_top
    | m1_subset_1(X2_50,k1_zfmisc_1(k2_zfmisc_1(X0_50,X1_50))) != iProver_top
    | m1_subset_1(X3_50,k1_zfmisc_1(k2_zfmisc_1(X1_50,X0_50))) != iProver_top
    | v1_funct_1(X2_50) != iProver_top
    | v1_funct_1(X3_50) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1068])).

cnf(c_2973,plain,
    ( k2_funct_1(sK1) = X0_50
    | sK0 = k1_xboole_0
    | r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK0,sK0,sK0,sK1,X0_50),k6_partfun1(sK0)) != iProver_top
    | v1_funct_2(X0_50,sK0,sK0) != iProver_top
    | v1_funct_2(sK1,sK0,sK0) != iProver_top
    | m1_subset_1(X0_50,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) != iProver_top
    | m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) != iProver_top
    | v1_funct_1(X0_50) != iProver_top
    | v1_funct_1(sK1) != iProver_top ),
    inference(superposition,[status(thm)],[c_2486,c_1482])).

cnf(c_29,plain,
    ( v1_funct_1(sK1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_28])).

cnf(c_27,negated_conjecture,
    ( v1_funct_2(sK1,sK0,sK0) ),
    inference(cnf_transformation,[],[f63])).

cnf(c_30,plain,
    ( v1_funct_2(sK1,sK0,sK0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_27])).

cnf(c_32,plain,
    ( m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_25])).

cnf(c_3412,plain,
    ( v1_funct_1(X0_50) != iProver_top
    | v1_funct_2(X0_50,sK0,sK0) != iProver_top
    | r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK0,sK0,sK0,sK1,X0_50),k6_partfun1(sK0)) != iProver_top
    | sK0 = k1_xboole_0
    | k2_funct_1(sK1) = X0_50
    | m1_subset_1(X0_50,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_2973,c_29,c_30,c_32])).

cnf(c_3413,plain,
    ( k2_funct_1(sK1) = X0_50
    | sK0 = k1_xboole_0
    | r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK0,sK0,sK0,sK1,X0_50),k6_partfun1(sK0)) != iProver_top
    | v1_funct_2(X0_50,sK0,sK0) != iProver_top
    | m1_subset_1(X0_50,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) != iProver_top
    | v1_funct_1(X0_50) != iProver_top ),
    inference(renaming,[status(thm)],[c_3412])).

cnf(c_3424,plain,
    ( k2_funct_1(sK1) = sK2
    | sK0 = k1_xboole_0
    | v1_funct_2(sK2,sK0,sK0) != iProver_top
    | m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) != iProver_top
    | v1_funct_1(sK2) != iProver_top ),
    inference(superposition,[status(thm)],[c_1475,c_3413])).

cnf(c_24,negated_conjecture,
    ( v1_funct_1(sK2) ),
    inference(cnf_transformation,[],[f66])).

cnf(c_33,plain,
    ( v1_funct_1(sK2) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_24])).

cnf(c_23,negated_conjecture,
    ( v1_funct_2(sK2,sK0,sK0) ),
    inference(cnf_transformation,[],[f67])).

cnf(c_34,plain,
    ( v1_funct_2(sK2,sK0,sK0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_23])).

cnf(c_21,negated_conjecture,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) ),
    inference(cnf_transformation,[],[f69])).

cnf(c_36,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_21])).

cnf(c_1087,plain,
    ( X0_50 = X0_50 ),
    theory(equality)).

cnf(c_1115,plain,
    ( sK0 = sK0 ),
    inference(instantiation,[status(thm)],[c_1087])).

cnf(c_19,negated_conjecture,
    ( ~ r2_relset_1(sK0,sK0,sK2,k2_funct_2(sK0,sK1)) ),
    inference(cnf_transformation,[],[f71])).

cnf(c_1076,negated_conjecture,
    ( ~ r2_relset_1(sK0,sK0,sK2,k2_funct_2(sK0,sK1)) ),
    inference(subtyping,[status(esa)],[c_19])).

cnf(c_1474,plain,
    ( r2_relset_1(sK0,sK0,sK2,k2_funct_2(sK0,sK1)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1076])).

cnf(c_15,plain,
    ( ~ v1_funct_2(X0,X1,X1)
    | ~ v3_funct_2(X0,X1,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X1)))
    | ~ v1_funct_1(X0)
    | k2_funct_2(X1,X0) = k2_funct_1(X0) ),
    inference(cnf_transformation,[],[f57])).

cnf(c_364,plain,
    ( ~ v1_funct_2(X0,X1,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X1)))
    | ~ v1_funct_1(X0)
    | k2_funct_2(X1,X0) = k2_funct_1(X0)
    | sK1 != X0
    | sK0 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_15,c_26])).

cnf(c_365,plain,
    ( ~ v1_funct_2(sK1,sK0,sK0)
    | ~ m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
    | ~ v1_funct_1(sK1)
    | k2_funct_2(sK0,sK1) = k2_funct_1(sK1) ),
    inference(unflattening,[status(thm)],[c_364])).

cnf(c_367,plain,
    ( k2_funct_2(sK0,sK1) = k2_funct_1(sK1) ),
    inference(global_propositional_subsumption,[status(thm)],[c_365,c_28,c_27,c_25])).

cnf(c_1066,plain,
    ( k2_funct_2(sK0,sK1) = k2_funct_1(sK1) ),
    inference(subtyping,[status(esa)],[c_367])).

cnf(c_1508,plain,
    ( r2_relset_1(sK0,sK0,sK2,k2_funct_1(sK1)) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_1474,c_1066])).

cnf(c_1606,plain,
    ( ~ r2_relset_1(sK0,sK0,sK2,k2_funct_1(sK1)) ),
    inference(predicate_to_equality_rev,[status(thm)],[c_1508])).

cnf(c_8,plain,
    ( r2_relset_1(X0,X1,X2,X2)
    | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ),
    inference(cnf_transformation,[],[f74])).

cnf(c_1078,plain,
    ( r2_relset_1(X0_50,X1_50,X2_50,X2_50)
    | ~ m1_subset_1(X2_50,k1_zfmisc_1(k2_zfmisc_1(X0_50,X1_50))) ),
    inference(subtyping,[status(esa)],[c_8])).

cnf(c_1657,plain,
    ( r2_relset_1(sK0,sK0,sK2,sK2)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) ),
    inference(instantiation,[status(thm)],[c_1078])).

cnf(c_1767,plain,
    ( sK2 = sK2 ),
    inference(instantiation,[status(thm)],[c_1087])).

cnf(c_1097,plain,
    ( ~ r2_relset_1(X0_50,X1_50,X2_50,X3_50)
    | r2_relset_1(X4_50,X5_50,X6_50,X7_50)
    | X4_50 != X0_50
    | X5_50 != X1_50
    | X6_50 != X2_50
    | X7_50 != X3_50 ),
    theory(equality)).

cnf(c_1735,plain,
    ( r2_relset_1(X0_50,X1_50,X2_50,X3_50)
    | ~ r2_relset_1(sK0,sK0,sK2,sK2)
    | X2_50 != sK2
    | X3_50 != sK2
    | X1_50 != sK0
    | X0_50 != sK0 ),
    inference(instantiation,[status(thm)],[c_1097])).

cnf(c_1967,plain,
    ( r2_relset_1(X0_50,X1_50,sK2,X2_50)
    | ~ r2_relset_1(sK0,sK0,sK2,sK2)
    | X2_50 != sK2
    | X1_50 != sK0
    | X0_50 != sK0
    | sK2 != sK2 ),
    inference(instantiation,[status(thm)],[c_1735])).

cnf(c_3226,plain,
    ( r2_relset_1(X0_50,X1_50,sK2,k2_funct_1(sK1))
    | ~ r2_relset_1(sK0,sK0,sK2,sK2)
    | X1_50 != sK0
    | X0_50 != sK0
    | k2_funct_1(sK1) != sK2
    | sK2 != sK2 ),
    inference(instantiation,[status(thm)],[c_1967])).

cnf(c_3233,plain,
    ( r2_relset_1(sK0,sK0,sK2,k2_funct_1(sK1))
    | ~ r2_relset_1(sK0,sK0,sK2,sK2)
    | k2_funct_1(sK1) != sK2
    | sK2 != sK2
    | sK0 != sK0 ),
    inference(instantiation,[status(thm)],[c_3226])).

cnf(c_3427,plain,
    ( sK0 = k1_xboole_0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_3424,c_33,c_34,c_21,c_36,c_1115,c_1606,c_1657,c_1767,c_3233])).

cnf(c_1074,negated_conjecture,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) ),
    inference(subtyping,[status(esa)],[c_21])).

cnf(c_1476,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1074])).

cnf(c_1472,plain,
    ( r2_relset_1(X0_50,X1_50,X2_50,X2_50) = iProver_top
    | m1_subset_1(X2_50,k1_zfmisc_1(k2_zfmisc_1(X0_50,X1_50))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1078])).

cnf(c_2561,plain,
    ( r2_relset_1(sK0,sK0,sK2,sK2) = iProver_top ),
    inference(superposition,[status(thm)],[c_1476,c_1472])).

cnf(c_3439,plain,
    ( r2_relset_1(k1_xboole_0,k1_xboole_0,sK2,sK2) = iProver_top ),
    inference(demodulation,[status(thm)],[c_3427,c_2561])).

cnf(c_22,negated_conjecture,
    ( v3_funct_2(sK2,sK0,sK0) ),
    inference(cnf_transformation,[],[f68])).

cnf(c_334,plain,
    ( v2_funct_2(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X2,X1)))
    | ~ v1_funct_1(X0)
    | sK2 != X0
    | sK0 != X1
    | sK0 != X2 ),
    inference(resolution_lifted,[status(thm)],[c_10,c_22])).

cnf(c_335,plain,
    ( v2_funct_2(sK2,sK0)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
    | ~ v1_funct_1(sK2) ),
    inference(unflattening,[status(thm)],[c_334])).

cnf(c_337,plain,
    ( v2_funct_2(sK2,sK0) ),
    inference(global_propositional_subsumption,[status(thm)],[c_335,c_24,c_21])).

cnf(c_418,plain,
    ( ~ v5_relat_1(X0,X1)
    | ~ v1_relat_1(X0)
    | k2_relat_1(X0) = X1
    | sK2 != X0
    | sK0 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_14,c_337])).

cnf(c_419,plain,
    ( ~ v5_relat_1(sK2,sK0)
    | ~ v1_relat_1(sK2)
    | k2_relat_1(sK2) = sK0 ),
    inference(unflattening,[status(thm)],[c_418])).

cnf(c_462,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ v1_relat_1(sK2)
    | k2_relat_1(sK2) = sK0
    | sK2 != X0
    | sK0 != X2 ),
    inference(resolution_lifted,[status(thm)],[c_6,c_419])).

cnf(c_463,plain,
    ( ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X0,sK0)))
    | ~ v1_relat_1(sK2)
    | k2_relat_1(sK2) = sK0 ),
    inference(unflattening,[status(thm)],[c_462])).

cnf(c_465,plain,
    ( ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
    | ~ v1_relat_1(sK2)
    | k2_relat_1(sK2) = sK0 ),
    inference(instantiation,[status(thm)],[c_463])).

cnf(c_467,plain,
    ( ~ v1_relat_1(sK2)
    | k2_relat_1(sK2) = sK0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_463,c_21,c_465])).

cnf(c_1064,plain,
    ( ~ v1_relat_1(sK2)
    | k2_relat_1(sK2) = sK0 ),
    inference(subtyping,[status(esa)],[c_467])).

cnf(c_1484,plain,
    ( k2_relat_1(sK2) = sK0
    | v1_relat_1(sK2) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1064])).

cnf(c_1842,plain,
    ( ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
    | ~ v1_relat_1(k2_zfmisc_1(sK0,sK0))
    | v1_relat_1(sK2) ),
    inference(instantiation,[status(thm)],[c_1642])).

cnf(c_2004,plain,
    ( k2_relat_1(sK2) = sK0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_1484,c_21,c_84,c_1064,c_1842])).

cnf(c_2,plain,
    ( ~ v1_relat_1(X0)
    | k2_relat_1(X0) != k1_xboole_0
    | k1_xboole_0 = X0 ),
    inference(cnf_transformation,[],[f45])).

cnf(c_1083,plain,
    ( ~ v1_relat_1(X0_50)
    | k2_relat_1(X0_50) != k1_xboole_0
    | k1_xboole_0 = X0_50 ),
    inference(subtyping,[status(esa)],[c_2])).

cnf(c_1469,plain,
    ( k2_relat_1(X0_50) != k1_xboole_0
    | k1_xboole_0 = X0_50
    | v1_relat_1(X0_50) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1083])).

cnf(c_2333,plain,
    ( sK2 = k1_xboole_0
    | sK0 != k1_xboole_0
    | v1_relat_1(sK2) != iProver_top ),
    inference(superposition,[status(thm)],[c_2004,c_1469])).

cnf(c_2347,plain,
    ( ~ v1_relat_1(sK2)
    | sK2 = k1_xboole_0
    | sK0 != k1_xboole_0 ),
    inference(predicate_to_equality_rev,[status(thm)],[c_2333])).

cnf(c_2350,plain,
    ( sK0 != k1_xboole_0
    | sK2 = k1_xboole_0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_2333,c_21,c_84,c_1842,c_2347])).

cnf(c_2351,plain,
    ( sK2 = k1_xboole_0
    | sK0 != k1_xboole_0 ),
    inference(renaming,[status(thm)],[c_2350])).

cnf(c_3441,plain,
    ( sK2 = k1_xboole_0
    | k1_xboole_0 != k1_xboole_0 ),
    inference(demodulation,[status(thm)],[c_3427,c_2351])).

cnf(c_3473,plain,
    ( sK2 = k1_xboole_0 ),
    inference(equality_resolution_simp,[status(thm)],[c_3441])).

cnf(c_3509,plain,
    ( r2_relset_1(k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0) = iProver_top ),
    inference(light_normalisation,[status(thm)],[c_3439,c_3473])).

cnf(c_2334,plain,
    ( sK1 = k1_xboole_0
    | sK0 != k1_xboole_0
    | v1_relat_1(sK1) != iProver_top ),
    inference(superposition,[status(thm)],[c_2008,c_1469])).

cnf(c_83,plain,
    ( v1_relat_1(k2_zfmisc_1(X0,X1)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1])).

cnf(c_85,plain,
    ( v1_relat_1(k2_zfmisc_1(sK0,sK0)) = iProver_top ),
    inference(instantiation,[status(thm)],[c_83])).

cnf(c_1846,plain,
    ( m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) != iProver_top
    | v1_relat_1(k2_zfmisc_1(sK0,sK0)) != iProver_top
    | v1_relat_1(sK1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1845])).

cnf(c_2431,plain,
    ( sK0 != k1_xboole_0
    | sK1 = k1_xboole_0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_2334,c_32,c_85,c_1846])).

cnf(c_2432,plain,
    ( sK1 = k1_xboole_0
    | sK0 != k1_xboole_0 ),
    inference(renaming,[status(thm)],[c_2431])).

cnf(c_3440,plain,
    ( sK1 = k1_xboole_0
    | k1_xboole_0 != k1_xboole_0 ),
    inference(demodulation,[status(thm)],[c_3427,c_2432])).

cnf(c_3495,plain,
    ( sK1 = k1_xboole_0 ),
    inference(equality_resolution_simp,[status(thm)],[c_3440])).

cnf(c_3444,plain,
    ( r2_relset_1(k1_xboole_0,k1_xboole_0,sK2,k2_funct_1(sK1)) != iProver_top ),
    inference(demodulation,[status(thm)],[c_3427,c_1508])).

cnf(c_3476,plain,
    ( r2_relset_1(k1_xboole_0,k1_xboole_0,k1_xboole_0,k2_funct_1(sK1)) != iProver_top ),
    inference(demodulation,[status(thm)],[c_3473,c_3444])).

cnf(c_3497,plain,
    ( r2_relset_1(k1_xboole_0,k1_xboole_0,k1_xboole_0,k2_funct_1(k1_xboole_0)) != iProver_top ),
    inference(demodulation,[status(thm)],[c_3495,c_3476])).

cnf(c_4,plain,
    ( k6_partfun1(k1_xboole_0) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f72])).

cnf(c_1081,plain,
    ( k6_partfun1(k1_xboole_0) = k1_xboole_0 ),
    inference(subtyping,[status(esa)],[c_4])).

cnf(c_5,plain,
    ( k2_funct_1(k6_partfun1(X0)) = k6_partfun1(X0) ),
    inference(cnf_transformation,[],[f73])).

cnf(c_1080,plain,
    ( k2_funct_1(k6_partfun1(X0_50)) = k6_partfun1(X0_50) ),
    inference(subtyping,[status(esa)],[c_5])).

cnf(c_1814,plain,
    ( k2_funct_1(k1_xboole_0) = k6_partfun1(k1_xboole_0) ),
    inference(superposition,[status(thm)],[c_1081,c_1080])).

cnf(c_1815,plain,
    ( k2_funct_1(k1_xboole_0) = k1_xboole_0 ),
    inference(light_normalisation,[status(thm)],[c_1814,c_1081])).

cnf(c_3507,plain,
    ( r2_relset_1(k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_3497,c_1815])).

cnf(c_3511,plain,
    ( $false ),
    inference(forward_subsumption_resolution,[status(thm)],[c_3509,c_3507])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.12/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : iproveropt_run.sh %d %s
% 0.13/0.34  % Computer   : n009.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 16:21:11 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running in FOF mode
% 2.18/0.99  % SZS status Started for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.18/0.99  
% 2.18/0.99  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 2.18/0.99  
% 2.18/0.99  ------  iProver source info
% 2.18/0.99  
% 2.18/0.99  git: date: 2020-06-30 10:37:57 +0100
% 2.18/0.99  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 2.18/0.99  git: non_committed_changes: false
% 2.18/0.99  git: last_make_outside_of_git: false
% 2.18/0.99  
% 2.18/0.99  ------ 
% 2.18/0.99  
% 2.18/0.99  ------ Input Options
% 2.18/0.99  
% 2.18/0.99  --out_options                           all
% 2.18/0.99  --tptp_safe_out                         true
% 2.18/0.99  --problem_path                          ""
% 2.18/0.99  --include_path                          ""
% 2.18/0.99  --clausifier                            res/vclausify_rel
% 2.18/0.99  --clausifier_options                    --mode clausify
% 2.18/0.99  --stdin                                 false
% 2.18/0.99  --stats_out                             all
% 2.18/0.99  
% 2.18/0.99  ------ General Options
% 2.18/0.99  
% 2.18/0.99  --fof                                   false
% 2.18/0.99  --time_out_real                         305.
% 2.18/0.99  --time_out_virtual                      -1.
% 2.18/0.99  --symbol_type_check                     false
% 2.18/0.99  --clausify_out                          false
% 2.18/0.99  --sig_cnt_out                           false
% 2.18/0.99  --trig_cnt_out                          false
% 2.18/0.99  --trig_cnt_out_tolerance                1.
% 2.18/0.99  --trig_cnt_out_sk_spl                   false
% 2.18/0.99  --abstr_cl_out                          false
% 2.18/0.99  
% 2.18/0.99  ------ Global Options
% 2.18/0.99  
% 2.18/0.99  --schedule                              default
% 2.18/0.99  --add_important_lit                     false
% 2.18/0.99  --prop_solver_per_cl                    1000
% 2.18/0.99  --min_unsat_core                        false
% 2.18/0.99  --soft_assumptions                      false
% 2.18/0.99  --soft_lemma_size                       3
% 2.18/0.99  --prop_impl_unit_size                   0
% 2.18/0.99  --prop_impl_unit                        []
% 2.18/0.99  --share_sel_clauses                     true
% 2.18/0.99  --reset_solvers                         false
% 2.18/0.99  --bc_imp_inh                            [conj_cone]
% 2.18/0.99  --conj_cone_tolerance                   3.
% 2.18/0.99  --extra_neg_conj                        none
% 2.18/0.99  --large_theory_mode                     true
% 2.18/0.99  --prolific_symb_bound                   200
% 2.18/0.99  --lt_threshold                          2000
% 2.18/0.99  --clause_weak_htbl                      true
% 2.18/0.99  --gc_record_bc_elim                     false
% 2.18/0.99  
% 2.18/0.99  ------ Preprocessing Options
% 2.18/0.99  
% 2.18/0.99  --preprocessing_flag                    true
% 2.18/0.99  --time_out_prep_mult                    0.1
% 2.18/0.99  --splitting_mode                        input
% 2.18/0.99  --splitting_grd                         true
% 2.18/0.99  --splitting_cvd                         false
% 2.18/0.99  --splitting_cvd_svl                     false
% 2.18/0.99  --splitting_nvd                         32
% 2.18/0.99  --sub_typing                            true
% 2.18/0.99  --prep_gs_sim                           true
% 2.18/0.99  --prep_unflatten                        true
% 2.18/0.99  --prep_res_sim                          true
% 2.18/0.99  --prep_upred                            true
% 2.18/0.99  --prep_sem_filter                       exhaustive
% 2.18/0.99  --prep_sem_filter_out                   false
% 2.18/0.99  --pred_elim                             true
% 2.18/0.99  --res_sim_input                         true
% 2.18/0.99  --eq_ax_congr_red                       true
% 2.18/0.99  --pure_diseq_elim                       true
% 2.18/0.99  --brand_transform                       false
% 2.18/0.99  --non_eq_to_eq                          false
% 2.18/0.99  --prep_def_merge                        true
% 2.18/0.99  --prep_def_merge_prop_impl              false
% 2.18/0.99  --prep_def_merge_mbd                    true
% 2.18/0.99  --prep_def_merge_tr_red                 false
% 2.18/0.99  --prep_def_merge_tr_cl                  false
% 2.18/0.99  --smt_preprocessing                     true
% 2.18/0.99  --smt_ac_axioms                         fast
% 2.18/0.99  --preprocessed_out                      false
% 2.18/0.99  --preprocessed_stats                    false
% 2.18/0.99  
% 2.18/0.99  ------ Abstraction refinement Options
% 2.18/0.99  
% 2.18/0.99  --abstr_ref                             []
% 2.18/0.99  --abstr_ref_prep                        false
% 2.18/0.99  --abstr_ref_until_sat                   false
% 2.18/0.99  --abstr_ref_sig_restrict                funpre
% 2.18/0.99  --abstr_ref_af_restrict_to_split_sk     false
% 2.18/0.99  --abstr_ref_under                       []
% 2.18/0.99  
% 2.18/0.99  ------ SAT Options
% 2.18/0.99  
% 2.18/0.99  --sat_mode                              false
% 2.18/0.99  --sat_fm_restart_options                ""
% 2.18/0.99  --sat_gr_def                            false
% 2.18/0.99  --sat_epr_types                         true
% 2.18/0.99  --sat_non_cyclic_types                  false
% 2.18/0.99  --sat_finite_models                     false
% 2.18/0.99  --sat_fm_lemmas                         false
% 2.18/0.99  --sat_fm_prep                           false
% 2.18/0.99  --sat_fm_uc_incr                        true
% 2.18/0.99  --sat_out_model                         small
% 2.18/0.99  --sat_out_clauses                       false
% 2.18/0.99  
% 2.18/0.99  ------ QBF Options
% 2.18/0.99  
% 2.18/0.99  --qbf_mode                              false
% 2.18/0.99  --qbf_elim_univ                         false
% 2.18/0.99  --qbf_dom_inst                          none
% 2.18/0.99  --qbf_dom_pre_inst                      false
% 2.18/0.99  --qbf_sk_in                             false
% 2.18/0.99  --qbf_pred_elim                         true
% 2.18/0.99  --qbf_split                             512
% 2.18/0.99  
% 2.18/0.99  ------ BMC1 Options
% 2.18/0.99  
% 2.18/0.99  --bmc1_incremental                      false
% 2.18/0.99  --bmc1_axioms                           reachable_all
% 2.18/0.99  --bmc1_min_bound                        0
% 2.18/0.99  --bmc1_max_bound                        -1
% 2.18/0.99  --bmc1_max_bound_default                -1
% 2.18/0.99  --bmc1_symbol_reachability              true
% 2.18/0.99  --bmc1_property_lemmas                  false
% 2.18/0.99  --bmc1_k_induction                      false
% 2.18/0.99  --bmc1_non_equiv_states                 false
% 2.18/0.99  --bmc1_deadlock                         false
% 2.18/0.99  --bmc1_ucm                              false
% 2.18/0.99  --bmc1_add_unsat_core                   none
% 2.18/0.99  --bmc1_unsat_core_children              false
% 2.18/0.99  --bmc1_unsat_core_extrapolate_axioms    false
% 2.18/0.99  --bmc1_out_stat                         full
% 2.18/0.99  --bmc1_ground_init                      false
% 2.18/0.99  --bmc1_pre_inst_next_state              false
% 2.18/0.99  --bmc1_pre_inst_state                   false
% 2.18/0.99  --bmc1_pre_inst_reach_state             false
% 2.18/0.99  --bmc1_out_unsat_core                   false
% 2.18/0.99  --bmc1_aig_witness_out                  false
% 2.18/0.99  --bmc1_verbose                          false
% 2.18/0.99  --bmc1_dump_clauses_tptp                false
% 2.18/0.99  --bmc1_dump_unsat_core_tptp             false
% 2.18/0.99  --bmc1_dump_file                        -
% 2.18/0.99  --bmc1_ucm_expand_uc_limit              128
% 2.18/0.99  --bmc1_ucm_n_expand_iterations          6
% 2.18/0.99  --bmc1_ucm_extend_mode                  1
% 2.18/0.99  --bmc1_ucm_init_mode                    2
% 2.18/0.99  --bmc1_ucm_cone_mode                    none
% 2.18/0.99  --bmc1_ucm_reduced_relation_type        0
% 2.18/0.99  --bmc1_ucm_relax_model                  4
% 2.18/0.99  --bmc1_ucm_full_tr_after_sat            true
% 2.18/0.99  --bmc1_ucm_expand_neg_assumptions       false
% 2.18/0.99  --bmc1_ucm_layered_model                none
% 2.18/0.99  --bmc1_ucm_max_lemma_size               10
% 2.18/0.99  
% 2.18/0.99  ------ AIG Options
% 2.18/0.99  
% 2.18/0.99  --aig_mode                              false
% 2.18/0.99  
% 2.18/0.99  ------ Instantiation Options
% 2.18/0.99  
% 2.18/0.99  --instantiation_flag                    true
% 2.18/0.99  --inst_sos_flag                         false
% 2.18/0.99  --inst_sos_phase                        true
% 2.18/0.99  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 2.18/0.99  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 2.18/0.99  --inst_lit_sel_side                     num_symb
% 2.18/0.99  --inst_solver_per_active                1400
% 2.18/0.99  --inst_solver_calls_frac                1.
% 2.18/0.99  --inst_passive_queue_type               priority_queues
% 2.18/0.99  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 2.18/0.99  --inst_passive_queues_freq              [25;2]
% 2.18/0.99  --inst_dismatching                      true
% 2.18/0.99  --inst_eager_unprocessed_to_passive     true
% 2.18/0.99  --inst_prop_sim_given                   true
% 2.18/0.99  --inst_prop_sim_new                     false
% 2.18/0.99  --inst_subs_new                         false
% 2.18/0.99  --inst_eq_res_simp                      false
% 2.18/0.99  --inst_subs_given                       false
% 2.18/0.99  --inst_orphan_elimination               true
% 2.18/0.99  --inst_learning_loop_flag               true
% 2.18/0.99  --inst_learning_start                   3000
% 2.18/0.99  --inst_learning_factor                  2
% 2.18/0.99  --inst_start_prop_sim_after_learn       3
% 2.18/0.99  --inst_sel_renew                        solver
% 2.18/0.99  --inst_lit_activity_flag                true
% 2.18/0.99  --inst_restr_to_given                   false
% 2.18/0.99  --inst_activity_threshold               500
% 2.18/0.99  --inst_out_proof                        true
% 2.18/0.99  
% 2.18/0.99  ------ Resolution Options
% 2.18/0.99  
% 2.18/0.99  --resolution_flag                       true
% 2.18/0.99  --res_lit_sel                           adaptive
% 2.18/0.99  --res_lit_sel_side                      none
% 2.18/0.99  --res_ordering                          kbo
% 2.18/0.99  --res_to_prop_solver                    active
% 2.18/0.99  --res_prop_simpl_new                    false
% 2.18/0.99  --res_prop_simpl_given                  true
% 2.18/0.99  --res_passive_queue_type                priority_queues
% 2.18/0.99  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 2.18/0.99  --res_passive_queues_freq               [15;5]
% 2.18/0.99  --res_forward_subs                      full
% 2.18/0.99  --res_backward_subs                     full
% 2.18/0.99  --res_forward_subs_resolution           true
% 2.18/0.99  --res_backward_subs_resolution          true
% 2.18/0.99  --res_orphan_elimination                true
% 2.18/0.99  --res_time_limit                        2.
% 2.18/0.99  --res_out_proof                         true
% 2.18/0.99  
% 2.18/0.99  ------ Superposition Options
% 2.18/0.99  
% 2.18/0.99  --superposition_flag                    true
% 2.18/0.99  --sup_passive_queue_type                priority_queues
% 2.18/0.99  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 2.18/0.99  --sup_passive_queues_freq               [8;1;4]
% 2.18/0.99  --demod_completeness_check              fast
% 2.18/0.99  --demod_use_ground                      true
% 2.18/0.99  --sup_to_prop_solver                    passive
% 2.18/0.99  --sup_prop_simpl_new                    true
% 2.18/0.99  --sup_prop_simpl_given                  true
% 2.18/0.99  --sup_fun_splitting                     false
% 2.18/0.99  --sup_smt_interval                      50000
% 2.18/0.99  
% 2.18/0.99  ------ Superposition Simplification Setup
% 2.18/0.99  
% 2.18/0.99  --sup_indices_passive                   []
% 2.18/0.99  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.18/0.99  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.18/0.99  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.18/0.99  --sup_full_triv                         [TrivRules;PropSubs]
% 2.18/0.99  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.18/0.99  --sup_full_bw                           [BwDemod]
% 2.18/0.99  --sup_immed_triv                        [TrivRules]
% 2.18/0.99  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 2.18/0.99  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.18/0.99  --sup_immed_bw_main                     []
% 2.18/0.99  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.18/0.99  --sup_input_triv                        [Unflattening;TrivRules]
% 2.18/0.99  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.18/0.99  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.18/0.99  
% 2.18/0.99  ------ Combination Options
% 2.18/0.99  
% 2.18/0.99  --comb_res_mult                         3
% 2.18/0.99  --comb_sup_mult                         2
% 2.18/0.99  --comb_inst_mult                        10
% 2.18/0.99  
% 2.18/0.99  ------ Debug Options
% 2.18/0.99  
% 2.18/0.99  --dbg_backtrace                         false
% 2.18/0.99  --dbg_dump_prop_clauses                 false
% 2.18/0.99  --dbg_dump_prop_clauses_file            -
% 2.18/0.99  --dbg_out_stat                          false
% 2.18/0.99  ------ Parsing...
% 2.18/0.99  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 2.18/0.99  
% 2.18/0.99  ------ Preprocessing... sf_s  rm: 3 0s  sf_e  pe_s  pe:1:0s pe:2:0s pe_e  sf_s  rm: 4 0s  sf_e  pe_s  pe_e 
% 2.18/0.99  
% 2.18/0.99  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 2.18/0.99  
% 2.18/0.99  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 2.18/0.99  ------ Proving...
% 2.18/0.99  ------ Problem Properties 
% 2.18/0.99  
% 2.18/0.99  
% 2.18/0.99  clauses                                 23
% 2.18/0.99  conjectures                             8
% 2.18/0.99  EPR                                     4
% 2.18/0.99  Horn                                    22
% 2.18/0.99  unary                                   13
% 2.18/0.99  binary                                  4
% 2.18/0.99  lits                                    54
% 2.18/0.99  lits eq                                 17
% 2.18/0.99  fd_pure                                 0
% 2.18/0.99  fd_pseudo                               0
% 2.18/0.99  fd_cond                                 2
% 2.18/0.99  fd_pseudo_cond                          3
% 2.18/0.99  AC symbols                              0
% 2.18/0.99  
% 2.18/0.99  ------ Schedule dynamic 5 is on 
% 2.18/0.99  
% 2.18/0.99  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" Time Limit: 10.
% 2.18/0.99  
% 2.18/0.99  
% 2.18/0.99  ------ 
% 2.18/0.99  Current options:
% 2.18/0.99  ------ 
% 2.18/0.99  
% 2.18/0.99  ------ Input Options
% 2.18/0.99  
% 2.18/0.99  --out_options                           all
% 2.18/0.99  --tptp_safe_out                         true
% 2.18/0.99  --problem_path                          ""
% 2.18/0.99  --include_path                          ""
% 2.18/0.99  --clausifier                            res/vclausify_rel
% 2.18/0.99  --clausifier_options                    --mode clausify
% 2.18/0.99  --stdin                                 false
% 2.18/0.99  --stats_out                             all
% 2.18/0.99  
% 2.18/0.99  ------ General Options
% 2.18/0.99  
% 2.18/0.99  --fof                                   false
% 2.18/0.99  --time_out_real                         305.
% 2.18/0.99  --time_out_virtual                      -1.
% 2.18/0.99  --symbol_type_check                     false
% 2.18/0.99  --clausify_out                          false
% 2.18/0.99  --sig_cnt_out                           false
% 2.18/0.99  --trig_cnt_out                          false
% 2.18/0.99  --trig_cnt_out_tolerance                1.
% 2.18/0.99  --trig_cnt_out_sk_spl                   false
% 2.18/0.99  --abstr_cl_out                          false
% 2.18/0.99  
% 2.18/0.99  ------ Global Options
% 2.18/0.99  
% 2.18/0.99  --schedule                              default
% 2.18/0.99  --add_important_lit                     false
% 2.18/0.99  --prop_solver_per_cl                    1000
% 2.18/0.99  --min_unsat_core                        false
% 2.18/0.99  --soft_assumptions                      false
% 2.18/0.99  --soft_lemma_size                       3
% 2.18/0.99  --prop_impl_unit_size                   0
% 2.18/0.99  --prop_impl_unit                        []
% 2.18/0.99  --share_sel_clauses                     true
% 2.18/0.99  --reset_solvers                         false
% 2.18/0.99  --bc_imp_inh                            [conj_cone]
% 2.18/0.99  --conj_cone_tolerance                   3.
% 2.18/0.99  --extra_neg_conj                        none
% 2.18/0.99  --large_theory_mode                     true
% 2.18/0.99  --prolific_symb_bound                   200
% 2.18/0.99  --lt_threshold                          2000
% 2.18/0.99  --clause_weak_htbl                      true
% 2.18/0.99  --gc_record_bc_elim                     false
% 2.18/0.99  
% 2.18/0.99  ------ Preprocessing Options
% 2.18/0.99  
% 2.18/0.99  --preprocessing_flag                    true
% 2.18/0.99  --time_out_prep_mult                    0.1
% 2.18/0.99  --splitting_mode                        input
% 2.18/0.99  --splitting_grd                         true
% 2.18/0.99  --splitting_cvd                         false
% 2.18/0.99  --splitting_cvd_svl                     false
% 2.18/0.99  --splitting_nvd                         32
% 2.18/0.99  --sub_typing                            true
% 2.18/0.99  --prep_gs_sim                           true
% 2.18/0.99  --prep_unflatten                        true
% 2.18/0.99  --prep_res_sim                          true
% 2.18/0.99  --prep_upred                            true
% 2.18/0.99  --prep_sem_filter                       exhaustive
% 2.18/0.99  --prep_sem_filter_out                   false
% 2.18/0.99  --pred_elim                             true
% 2.18/0.99  --res_sim_input                         true
% 2.18/0.99  --eq_ax_congr_red                       true
% 2.18/0.99  --pure_diseq_elim                       true
% 2.18/0.99  --brand_transform                       false
% 2.18/0.99  --non_eq_to_eq                          false
% 2.18/0.99  --prep_def_merge                        true
% 2.18/0.99  --prep_def_merge_prop_impl              false
% 2.18/0.99  --prep_def_merge_mbd                    true
% 2.18/0.99  --prep_def_merge_tr_red                 false
% 2.18/0.99  --prep_def_merge_tr_cl                  false
% 2.18/0.99  --smt_preprocessing                     true
% 2.18/0.99  --smt_ac_axioms                         fast
% 2.18/0.99  --preprocessed_out                      false
% 2.18/0.99  --preprocessed_stats                    false
% 2.18/0.99  
% 2.18/0.99  ------ Abstraction refinement Options
% 2.18/0.99  
% 2.18/0.99  --abstr_ref                             []
% 2.18/0.99  --abstr_ref_prep                        false
% 2.18/0.99  --abstr_ref_until_sat                   false
% 2.18/0.99  --abstr_ref_sig_restrict                funpre
% 2.18/0.99  --abstr_ref_af_restrict_to_split_sk     false
% 2.18/0.99  --abstr_ref_under                       []
% 2.18/0.99  
% 2.18/0.99  ------ SAT Options
% 2.18/0.99  
% 2.18/0.99  --sat_mode                              false
% 2.18/0.99  --sat_fm_restart_options                ""
% 2.18/0.99  --sat_gr_def                            false
% 2.18/0.99  --sat_epr_types                         true
% 2.18/0.99  --sat_non_cyclic_types                  false
% 2.18/0.99  --sat_finite_models                     false
% 2.18/0.99  --sat_fm_lemmas                         false
% 2.18/0.99  --sat_fm_prep                           false
% 2.18/0.99  --sat_fm_uc_incr                        true
% 2.18/0.99  --sat_out_model                         small
% 2.18/0.99  --sat_out_clauses                       false
% 2.18/0.99  
% 2.18/0.99  ------ QBF Options
% 2.18/0.99  
% 2.18/0.99  --qbf_mode                              false
% 2.18/0.99  --qbf_elim_univ                         false
% 2.18/0.99  --qbf_dom_inst                          none
% 2.18/0.99  --qbf_dom_pre_inst                      false
% 2.18/0.99  --qbf_sk_in                             false
% 2.18/0.99  --qbf_pred_elim                         true
% 2.18/0.99  --qbf_split                             512
% 2.18/0.99  
% 2.18/0.99  ------ BMC1 Options
% 2.18/0.99  
% 2.18/0.99  --bmc1_incremental                      false
% 2.18/0.99  --bmc1_axioms                           reachable_all
% 2.18/0.99  --bmc1_min_bound                        0
% 2.18/0.99  --bmc1_max_bound                        -1
% 2.18/0.99  --bmc1_max_bound_default                -1
% 2.18/0.99  --bmc1_symbol_reachability              true
% 2.18/0.99  --bmc1_property_lemmas                  false
% 2.18/0.99  --bmc1_k_induction                      false
% 2.18/0.99  --bmc1_non_equiv_states                 false
% 2.18/0.99  --bmc1_deadlock                         false
% 2.18/0.99  --bmc1_ucm                              false
% 2.18/0.99  --bmc1_add_unsat_core                   none
% 2.18/0.99  --bmc1_unsat_core_children              false
% 2.18/0.99  --bmc1_unsat_core_extrapolate_axioms    false
% 2.18/0.99  --bmc1_out_stat                         full
% 2.18/0.99  --bmc1_ground_init                      false
% 2.18/0.99  --bmc1_pre_inst_next_state              false
% 2.18/0.99  --bmc1_pre_inst_state                   false
% 2.18/0.99  --bmc1_pre_inst_reach_state             false
% 2.18/0.99  --bmc1_out_unsat_core                   false
% 2.18/0.99  --bmc1_aig_witness_out                  false
% 2.18/0.99  --bmc1_verbose                          false
% 2.18/0.99  --bmc1_dump_clauses_tptp                false
% 2.18/0.99  --bmc1_dump_unsat_core_tptp             false
% 2.18/0.99  --bmc1_dump_file                        -
% 2.18/0.99  --bmc1_ucm_expand_uc_limit              128
% 2.18/0.99  --bmc1_ucm_n_expand_iterations          6
% 2.18/0.99  --bmc1_ucm_extend_mode                  1
% 2.18/0.99  --bmc1_ucm_init_mode                    2
% 2.18/0.99  --bmc1_ucm_cone_mode                    none
% 2.18/0.99  --bmc1_ucm_reduced_relation_type        0
% 2.18/0.99  --bmc1_ucm_relax_model                  4
% 2.18/0.99  --bmc1_ucm_full_tr_after_sat            true
% 2.18/0.99  --bmc1_ucm_expand_neg_assumptions       false
% 2.18/0.99  --bmc1_ucm_layered_model                none
% 2.18/0.99  --bmc1_ucm_max_lemma_size               10
% 2.18/0.99  
% 2.18/0.99  ------ AIG Options
% 2.18/0.99  
% 2.18/0.99  --aig_mode                              false
% 2.18/0.99  
% 2.18/0.99  ------ Instantiation Options
% 2.18/0.99  
% 2.18/0.99  --instantiation_flag                    true
% 2.18/0.99  --inst_sos_flag                         false
% 2.18/0.99  --inst_sos_phase                        true
% 2.18/0.99  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 2.18/0.99  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 2.18/0.99  --inst_lit_sel_side                     none
% 2.18/0.99  --inst_solver_per_active                1400
% 2.18/0.99  --inst_solver_calls_frac                1.
% 2.18/0.99  --inst_passive_queue_type               priority_queues
% 2.18/0.99  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 2.18/0.99  --inst_passive_queues_freq              [25;2]
% 2.18/0.99  --inst_dismatching                      true
% 2.18/0.99  --inst_eager_unprocessed_to_passive     true
% 2.18/0.99  --inst_prop_sim_given                   true
% 2.18/0.99  --inst_prop_sim_new                     false
% 2.18/0.99  --inst_subs_new                         false
% 2.18/0.99  --inst_eq_res_simp                      false
% 2.18/0.99  --inst_subs_given                       false
% 2.18/0.99  --inst_orphan_elimination               true
% 2.18/0.99  --inst_learning_loop_flag               true
% 2.18/0.99  --inst_learning_start                   3000
% 2.18/0.99  --inst_learning_factor                  2
% 2.18/0.99  --inst_start_prop_sim_after_learn       3
% 2.18/0.99  --inst_sel_renew                        solver
% 2.18/0.99  --inst_lit_activity_flag                true
% 2.18/0.99  --inst_restr_to_given                   false
% 2.18/0.99  --inst_activity_threshold               500
% 2.18/0.99  --inst_out_proof                        true
% 2.18/0.99  
% 2.18/0.99  ------ Resolution Options
% 2.18/0.99  
% 2.18/0.99  --resolution_flag                       false
% 2.18/0.99  --res_lit_sel                           adaptive
% 2.18/0.99  --res_lit_sel_side                      none
% 2.18/0.99  --res_ordering                          kbo
% 2.18/0.99  --res_to_prop_solver                    active
% 2.18/0.99  --res_prop_simpl_new                    false
% 2.18/0.99  --res_prop_simpl_given                  true
% 2.18/0.99  --res_passive_queue_type                priority_queues
% 2.18/0.99  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 2.18/0.99  --res_passive_queues_freq               [15;5]
% 2.18/0.99  --res_forward_subs                      full
% 2.18/0.99  --res_backward_subs                     full
% 2.18/0.99  --res_forward_subs_resolution           true
% 2.18/0.99  --res_backward_subs_resolution          true
% 2.18/0.99  --res_orphan_elimination                true
% 2.18/0.99  --res_time_limit                        2.
% 2.18/0.99  --res_out_proof                         true
% 2.18/0.99  
% 2.18/0.99  ------ Superposition Options
% 2.18/0.99  
% 2.18/0.99  --superposition_flag                    true
% 2.18/0.99  --sup_passive_queue_type                priority_queues
% 2.18/0.99  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 2.18/0.99  --sup_passive_queues_freq               [8;1;4]
% 2.18/0.99  --demod_completeness_check              fast
% 2.18/0.99  --demod_use_ground                      true
% 2.18/0.99  --sup_to_prop_solver                    passive
% 2.18/0.99  --sup_prop_simpl_new                    true
% 2.18/0.99  --sup_prop_simpl_given                  true
% 2.18/0.99  --sup_fun_splitting                     false
% 2.18/0.99  --sup_smt_interval                      50000
% 2.18/0.99  
% 2.18/0.99  ------ Superposition Simplification Setup
% 2.18/0.99  
% 2.18/0.99  --sup_indices_passive                   []
% 2.18/0.99  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.18/0.99  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.18/0.99  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.18/0.99  --sup_full_triv                         [TrivRules;PropSubs]
% 2.18/0.99  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.18/0.99  --sup_full_bw                           [BwDemod]
% 2.18/0.99  --sup_immed_triv                        [TrivRules]
% 2.18/0.99  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 2.18/0.99  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.18/0.99  --sup_immed_bw_main                     []
% 2.18/0.99  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.18/0.99  --sup_input_triv                        [Unflattening;TrivRules]
% 2.18/0.99  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.18/0.99  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.18/0.99  
% 2.18/0.99  ------ Combination Options
% 2.18/0.99  
% 2.18/0.99  --comb_res_mult                         3
% 2.18/0.99  --comb_sup_mult                         2
% 2.18/0.99  --comb_inst_mult                        10
% 2.18/0.99  
% 2.18/0.99  ------ Debug Options
% 2.18/0.99  
% 2.18/0.99  --dbg_backtrace                         false
% 2.18/0.99  --dbg_dump_prop_clauses                 false
% 2.18/0.99  --dbg_dump_prop_clauses_file            -
% 2.18/0.99  --dbg_out_stat                          false
% 2.18/0.99  
% 2.18/0.99  
% 2.18/0.99  
% 2.18/0.99  
% 2.18/0.99  ------ Proving...
% 2.18/0.99  
% 2.18/0.99  
% 2.18/0.99  % SZS status Theorem for theBenchmark.p
% 2.18/0.99  
% 2.18/0.99   Resolution empty clause
% 2.18/0.99  
% 2.18/0.99  % SZS output start CNFRefutation for theBenchmark.p
% 2.18/0.99  
% 2.18/0.99  fof(f15,conjecture,(
% 2.18/0.99    ! [X0,X1] : ((m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v3_funct_2(X1,X0,X0) & v1_funct_2(X1,X0,X0) & v1_funct_1(X1)) => ! [X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v3_funct_2(X2,X0,X0) & v1_funct_2(X2,X0,X0) & v1_funct_1(X2)) => (r2_relset_1(X0,X0,k1_partfun1(X0,X0,X0,X0,X1,X2),k6_partfun1(X0)) => r2_relset_1(X0,X0,X2,k2_funct_2(X0,X1)))))),
% 2.18/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.18/0.99  
% 2.18/0.99  fof(f16,negated_conjecture,(
% 2.18/0.99    ~! [X0,X1] : ((m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v3_funct_2(X1,X0,X0) & v1_funct_2(X1,X0,X0) & v1_funct_1(X1)) => ! [X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v3_funct_2(X2,X0,X0) & v1_funct_2(X2,X0,X0) & v1_funct_1(X2)) => (r2_relset_1(X0,X0,k1_partfun1(X0,X0,X0,X0,X1,X2),k6_partfun1(X0)) => r2_relset_1(X0,X0,X2,k2_funct_2(X0,X1)))))),
% 2.18/0.99    inference(negated_conjecture,[],[f15])).
% 2.18/0.99  
% 2.18/0.99  fof(f35,plain,(
% 2.18/0.99    ? [X0,X1] : (? [X2] : ((~r2_relset_1(X0,X0,X2,k2_funct_2(X0,X1)) & r2_relset_1(X0,X0,k1_partfun1(X0,X0,X0,X0,X1,X2),k6_partfun1(X0))) & (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v3_funct_2(X2,X0,X0) & v1_funct_2(X2,X0,X0) & v1_funct_1(X2))) & (m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v3_funct_2(X1,X0,X0) & v1_funct_2(X1,X0,X0) & v1_funct_1(X1)))),
% 2.18/0.99    inference(ennf_transformation,[],[f16])).
% 2.18/0.99  
% 2.18/0.99  fof(f36,plain,(
% 2.18/0.99    ? [X0,X1] : (? [X2] : (~r2_relset_1(X0,X0,X2,k2_funct_2(X0,X1)) & r2_relset_1(X0,X0,k1_partfun1(X0,X0,X0,X0,X1,X2),k6_partfun1(X0)) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v3_funct_2(X2,X0,X0) & v1_funct_2(X2,X0,X0) & v1_funct_1(X2)) & m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v3_funct_2(X1,X0,X0) & v1_funct_2(X1,X0,X0) & v1_funct_1(X1))),
% 2.18/0.99    inference(flattening,[],[f35])).
% 2.18/0.99  
% 2.18/0.99  fof(f40,plain,(
% 2.18/0.99    ( ! [X0,X1] : (? [X2] : (~r2_relset_1(X0,X0,X2,k2_funct_2(X0,X1)) & r2_relset_1(X0,X0,k1_partfun1(X0,X0,X0,X0,X1,X2),k6_partfun1(X0)) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v3_funct_2(X2,X0,X0) & v1_funct_2(X2,X0,X0) & v1_funct_1(X2)) => (~r2_relset_1(X0,X0,sK2,k2_funct_2(X0,X1)) & r2_relset_1(X0,X0,k1_partfun1(X0,X0,X0,X0,X1,sK2),k6_partfun1(X0)) & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v3_funct_2(sK2,X0,X0) & v1_funct_2(sK2,X0,X0) & v1_funct_1(sK2))) )),
% 2.18/0.99    introduced(choice_axiom,[])).
% 2.18/0.99  
% 2.18/0.99  fof(f39,plain,(
% 2.18/0.99    ? [X0,X1] : (? [X2] : (~r2_relset_1(X0,X0,X2,k2_funct_2(X0,X1)) & r2_relset_1(X0,X0,k1_partfun1(X0,X0,X0,X0,X1,X2),k6_partfun1(X0)) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v3_funct_2(X2,X0,X0) & v1_funct_2(X2,X0,X0) & v1_funct_1(X2)) & m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v3_funct_2(X1,X0,X0) & v1_funct_2(X1,X0,X0) & v1_funct_1(X1)) => (? [X2] : (~r2_relset_1(sK0,sK0,X2,k2_funct_2(sK0,sK1)) & r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK0,sK0,sK0,sK1,X2),k6_partfun1(sK0)) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) & v3_funct_2(X2,sK0,sK0) & v1_funct_2(X2,sK0,sK0) & v1_funct_1(X2)) & m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) & v3_funct_2(sK1,sK0,sK0) & v1_funct_2(sK1,sK0,sK0) & v1_funct_1(sK1))),
% 2.18/0.99    introduced(choice_axiom,[])).
% 2.18/0.99  
% 2.18/0.99  fof(f41,plain,(
% 2.18/0.99    (~r2_relset_1(sK0,sK0,sK2,k2_funct_2(sK0,sK1)) & r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK0,sK0,sK0,sK1,sK2),k6_partfun1(sK0)) & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) & v3_funct_2(sK2,sK0,sK0) & v1_funct_2(sK2,sK0,sK0) & v1_funct_1(sK2)) & m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) & v3_funct_2(sK1,sK0,sK0) & v1_funct_2(sK1,sK0,sK0) & v1_funct_1(sK1)),
% 2.18/0.99    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f36,f40,f39])).
% 2.18/0.99  
% 2.18/0.99  fof(f70,plain,(
% 2.18/0.99    r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK0,sK0,sK0,sK1,sK2),k6_partfun1(sK0))),
% 2.18/0.99    inference(cnf_transformation,[],[f41])).
% 2.18/0.99  
% 2.18/0.99  fof(f65,plain,(
% 2.18/0.99    m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))),
% 2.18/0.99    inference(cnf_transformation,[],[f41])).
% 2.18/0.99  
% 2.18/0.99  fof(f7,axiom,(
% 2.18/0.99    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k2_relat_1(X2) = k2_relset_1(X0,X1,X2))),
% 2.18/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.18/0.99  
% 2.18/0.99  fof(f22,plain,(
% 2.18/0.99    ! [X0,X1,X2] : (k2_relat_1(X2) = k2_relset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 2.18/0.99    inference(ennf_transformation,[],[f7])).
% 2.18/0.99  
% 2.18/0.99  fof(f49,plain,(
% 2.18/0.99    ( ! [X2,X0,X1] : (k2_relat_1(X2) = k2_relset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 2.18/0.99    inference(cnf_transformation,[],[f22])).
% 2.18/0.99  
% 2.18/0.99  fof(f6,axiom,(
% 2.18/0.99    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => (v5_relat_1(X2,X1) & v4_relat_1(X2,X0)))),
% 2.18/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.18/0.99  
% 2.18/0.99  fof(f17,plain,(
% 2.18/0.99    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => v5_relat_1(X2,X1))),
% 2.18/0.99    inference(pure_predicate_removal,[],[f6])).
% 2.18/0.99  
% 2.18/0.99  fof(f21,plain,(
% 2.18/0.99    ! [X0,X1,X2] : (v5_relat_1(X2,X1) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 2.18/0.99    inference(ennf_transformation,[],[f17])).
% 2.18/0.99  
% 2.18/0.99  fof(f48,plain,(
% 2.18/0.99    ( ! [X2,X0,X1] : (v5_relat_1(X2,X1) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 2.18/0.99    inference(cnf_transformation,[],[f21])).
% 2.18/0.99  
% 2.18/0.99  fof(f10,axiom,(
% 2.18/0.99    ! [X0,X1] : ((v5_relat_1(X1,X0) & v1_relat_1(X1)) => (v2_funct_2(X1,X0) <=> k2_relat_1(X1) = X0))),
% 2.18/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.18/0.99  
% 2.18/0.99  fof(f27,plain,(
% 2.18/0.99    ! [X0,X1] : ((v2_funct_2(X1,X0) <=> k2_relat_1(X1) = X0) | (~v5_relat_1(X1,X0) | ~v1_relat_1(X1)))),
% 2.18/0.99    inference(ennf_transformation,[],[f10])).
% 2.18/0.99  
% 2.18/0.99  fof(f28,plain,(
% 2.18/0.99    ! [X0,X1] : ((v2_funct_2(X1,X0) <=> k2_relat_1(X1) = X0) | ~v5_relat_1(X1,X0) | ~v1_relat_1(X1))),
% 2.18/0.99    inference(flattening,[],[f27])).
% 2.18/0.99  
% 2.18/0.99  fof(f38,plain,(
% 2.18/0.99    ! [X0,X1] : (((v2_funct_2(X1,X0) | k2_relat_1(X1) != X0) & (k2_relat_1(X1) = X0 | ~v2_funct_2(X1,X0))) | ~v5_relat_1(X1,X0) | ~v1_relat_1(X1))),
% 2.18/0.99    inference(nnf_transformation,[],[f28])).
% 2.18/0.99  
% 2.18/0.99  fof(f55,plain,(
% 2.18/0.99    ( ! [X0,X1] : (k2_relat_1(X1) = X0 | ~v2_funct_2(X1,X0) | ~v5_relat_1(X1,X0) | ~v1_relat_1(X1)) )),
% 2.18/0.99    inference(cnf_transformation,[],[f38])).
% 2.18/0.99  
% 2.18/0.99  fof(f9,axiom,(
% 2.18/0.99    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => ((v3_funct_2(X2,X0,X1) & v1_funct_1(X2)) => (v2_funct_2(X2,X1) & v2_funct_1(X2) & v1_funct_1(X2))))),
% 2.18/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.18/0.99  
% 2.18/0.99  fof(f25,plain,(
% 2.18/0.99    ! [X0,X1,X2] : (((v2_funct_2(X2,X1) & v2_funct_1(X2) & v1_funct_1(X2)) | (~v3_funct_2(X2,X0,X1) | ~v1_funct_1(X2))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 2.18/0.99    inference(ennf_transformation,[],[f9])).
% 2.18/0.99  
% 2.18/0.99  fof(f26,plain,(
% 2.18/0.99    ! [X0,X1,X2] : ((v2_funct_2(X2,X1) & v2_funct_1(X2) & v1_funct_1(X2)) | ~v3_funct_2(X2,X0,X1) | ~v1_funct_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 2.18/0.99    inference(flattening,[],[f25])).
% 2.18/0.99  
% 2.18/0.99  fof(f54,plain,(
% 2.18/0.99    ( ! [X2,X0,X1] : (v2_funct_2(X2,X1) | ~v3_funct_2(X2,X0,X1) | ~v1_funct_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 2.18/0.99    inference(cnf_transformation,[],[f26])).
% 2.18/0.99  
% 2.18/0.99  fof(f64,plain,(
% 2.18/0.99    v3_funct_2(sK1,sK0,sK0)),
% 2.18/0.99    inference(cnf_transformation,[],[f41])).
% 2.18/0.99  
% 2.18/0.99  fof(f62,plain,(
% 2.18/0.99    v1_funct_1(sK1)),
% 2.18/0.99    inference(cnf_transformation,[],[f41])).
% 2.18/0.99  
% 2.18/0.99  fof(f2,axiom,(
% 2.18/0.99    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1))),
% 2.18/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.18/0.99  
% 2.18/0.99  fof(f43,plain,(
% 2.18/0.99    ( ! [X0,X1] : (v1_relat_1(k2_zfmisc_1(X0,X1))) )),
% 2.18/0.99    inference(cnf_transformation,[],[f2])).
% 2.18/0.99  
% 2.18/0.99  fof(f1,axiom,(
% 2.18/0.99    ! [X0] : (v1_relat_1(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => v1_relat_1(X1)))),
% 2.18/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.18/0.99  
% 2.18/0.99  fof(f18,plain,(
% 2.18/0.99    ! [X0] : (! [X1] : (v1_relat_1(X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) | ~v1_relat_1(X0))),
% 2.18/0.99    inference(ennf_transformation,[],[f1])).
% 2.18/0.99  
% 2.18/0.99  fof(f42,plain,(
% 2.18/0.99    ( ! [X0,X1] : (v1_relat_1(X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0)) | ~v1_relat_1(X0)) )),
% 2.18/0.99    inference(cnf_transformation,[],[f18])).
% 2.18/0.99  
% 2.18/0.99  fof(f14,axiom,(
% 2.18/0.99    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => ! [X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(X3,X1,X0) & v1_funct_1(X3)) => ((v2_funct_1(X2) & r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0)) & k2_relset_1(X0,X1,X2) = X1) => (k2_funct_1(X2) = X3 | k1_xboole_0 = X1 | k1_xboole_0 = X0))))),
% 2.18/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.18/0.99  
% 2.18/0.99  fof(f33,plain,(
% 2.18/0.99    ! [X0,X1,X2] : (! [X3] : (((k2_funct_1(X2) = X3 | k1_xboole_0 = X1 | k1_xboole_0 = X0) | (~v2_funct_1(X2) | ~r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0)) | k2_relset_1(X0,X1,X2) != X1)) | (~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) | ~v1_funct_2(X3,X1,X0) | ~v1_funct_1(X3))) | (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2)))),
% 2.18/0.99    inference(ennf_transformation,[],[f14])).
% 2.18/0.99  
% 2.18/0.99  fof(f34,plain,(
% 2.18/0.99    ! [X0,X1,X2] : (! [X3] : (k2_funct_1(X2) = X3 | k1_xboole_0 = X1 | k1_xboole_0 = X0 | ~v2_funct_1(X2) | ~r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0)) | k2_relset_1(X0,X1,X2) != X1 | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) | ~v1_funct_2(X3,X1,X0) | ~v1_funct_1(X3)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2))),
% 2.18/0.99    inference(flattening,[],[f33])).
% 2.18/0.99  
% 2.18/0.99  fof(f61,plain,(
% 2.18/0.99    ( ! [X2,X0,X3,X1] : (k2_funct_1(X2) = X3 | k1_xboole_0 = X1 | k1_xboole_0 = X0 | ~v2_funct_1(X2) | ~r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0)) | k2_relset_1(X0,X1,X2) != X1 | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) | ~v1_funct_2(X3,X1,X0) | ~v1_funct_1(X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2)) )),
% 2.18/0.99    inference(cnf_transformation,[],[f34])).
% 2.18/0.99  
% 2.18/0.99  fof(f13,axiom,(
% 2.18/0.99    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => ! [X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(X3,X1,X0) & v1_funct_1(X3)) => (r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0)) => (v2_funct_2(X3,X0) & v2_funct_1(X2)))))),
% 2.18/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.18/0.99  
% 2.18/0.99  fof(f31,plain,(
% 2.18/0.99    ! [X0,X1,X2] : (! [X3] : (((v2_funct_2(X3,X0) & v2_funct_1(X2)) | ~r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0))) | (~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) | ~v1_funct_2(X3,X1,X0) | ~v1_funct_1(X3))) | (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2)))),
% 2.18/0.99    inference(ennf_transformation,[],[f13])).
% 2.18/0.99  
% 2.18/0.99  fof(f32,plain,(
% 2.18/0.99    ! [X0,X1,X2] : (! [X3] : ((v2_funct_2(X3,X0) & v2_funct_1(X2)) | ~r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0)) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) | ~v1_funct_2(X3,X1,X0) | ~v1_funct_1(X3)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2))),
% 2.18/0.99    inference(flattening,[],[f31])).
% 2.18/0.99  
% 2.18/0.99  fof(f59,plain,(
% 2.18/0.99    ( ! [X2,X0,X3,X1] : (v2_funct_1(X2) | ~r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0)) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) | ~v1_funct_2(X3,X1,X0) | ~v1_funct_1(X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2)) )),
% 2.18/0.99    inference(cnf_transformation,[],[f32])).
% 2.18/0.99  
% 2.18/0.99  fof(f63,plain,(
% 2.18/0.99    v1_funct_2(sK1,sK0,sK0)),
% 2.18/0.99    inference(cnf_transformation,[],[f41])).
% 2.18/0.99  
% 2.18/0.99  fof(f66,plain,(
% 2.18/0.99    v1_funct_1(sK2)),
% 2.18/0.99    inference(cnf_transformation,[],[f41])).
% 2.18/0.99  
% 2.18/0.99  fof(f67,plain,(
% 2.18/0.99    v1_funct_2(sK2,sK0,sK0)),
% 2.18/0.99    inference(cnf_transformation,[],[f41])).
% 2.18/0.99  
% 2.18/0.99  fof(f69,plain,(
% 2.18/0.99    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))),
% 2.18/0.99    inference(cnf_transformation,[],[f41])).
% 2.18/0.99  
% 2.18/0.99  fof(f71,plain,(
% 2.18/0.99    ~r2_relset_1(sK0,sK0,sK2,k2_funct_2(sK0,sK1))),
% 2.18/0.99    inference(cnf_transformation,[],[f41])).
% 2.18/0.99  
% 2.18/0.99  fof(f11,axiom,(
% 2.18/0.99    ! [X0,X1] : ((m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v3_funct_2(X1,X0,X0) & v1_funct_2(X1,X0,X0) & v1_funct_1(X1)) => k2_funct_1(X1) = k2_funct_2(X0,X1))),
% 2.18/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.18/0.99  
% 2.18/0.99  fof(f29,plain,(
% 2.18/0.99    ! [X0,X1] : (k2_funct_1(X1) = k2_funct_2(X0,X1) | (~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) | ~v3_funct_2(X1,X0,X0) | ~v1_funct_2(X1,X0,X0) | ~v1_funct_1(X1)))),
% 2.18/0.99    inference(ennf_transformation,[],[f11])).
% 2.18/0.99  
% 2.18/0.99  fof(f30,plain,(
% 2.18/0.99    ! [X0,X1] : (k2_funct_1(X1) = k2_funct_2(X0,X1) | ~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) | ~v3_funct_2(X1,X0,X0) | ~v1_funct_2(X1,X0,X0) | ~v1_funct_1(X1))),
% 2.18/0.99    inference(flattening,[],[f29])).
% 2.18/0.99  
% 2.18/0.99  fof(f57,plain,(
% 2.18/0.99    ( ! [X0,X1] : (k2_funct_1(X1) = k2_funct_2(X0,X1) | ~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) | ~v3_funct_2(X1,X0,X0) | ~v1_funct_2(X1,X0,X0) | ~v1_funct_1(X1)) )),
% 2.18/0.99    inference(cnf_transformation,[],[f30])).
% 2.18/0.99  
% 2.18/0.99  fof(f8,axiom,(
% 2.18/0.99    ! [X0,X1,X2,X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) => (r2_relset_1(X0,X1,X2,X3) <=> X2 = X3))),
% 2.18/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.18/0.99  
% 2.18/0.99  fof(f23,plain,(
% 2.18/0.99    ! [X0,X1,X2,X3] : ((r2_relset_1(X0,X1,X2,X3) <=> X2 = X3) | (~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))))),
% 2.18/0.99    inference(ennf_transformation,[],[f8])).
% 2.18/0.99  
% 2.18/0.99  fof(f24,plain,(
% 2.18/0.99    ! [X0,X1,X2,X3] : ((r2_relset_1(X0,X1,X2,X3) <=> X2 = X3) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 2.18/0.99    inference(flattening,[],[f23])).
% 2.18/0.99  
% 2.18/0.99  fof(f37,plain,(
% 2.18/0.99    ! [X0,X1,X2,X3] : (((r2_relset_1(X0,X1,X2,X3) | X2 != X3) & (X2 = X3 | ~r2_relset_1(X0,X1,X2,X3))) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 2.18/0.99    inference(nnf_transformation,[],[f24])).
% 2.18/0.99  
% 2.18/0.99  fof(f51,plain,(
% 2.18/0.99    ( ! [X2,X0,X3,X1] : (r2_relset_1(X0,X1,X2,X3) | X2 != X3 | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 2.18/0.99    inference(cnf_transformation,[],[f37])).
% 2.18/0.99  
% 2.18/0.99  fof(f74,plain,(
% 2.18/0.99    ( ! [X0,X3,X1] : (r2_relset_1(X0,X1,X3,X3) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 2.18/0.99    inference(equality_resolution,[],[f51])).
% 2.18/0.99  
% 2.18/0.99  fof(f68,plain,(
% 2.18/0.99    v3_funct_2(sK2,sK0,sK0)),
% 2.18/0.99    inference(cnf_transformation,[],[f41])).
% 2.18/0.99  
% 2.18/0.99  fof(f3,axiom,(
% 2.18/0.99    ! [X0] : (v1_relat_1(X0) => ((k1_xboole_0 = k2_relat_1(X0) | k1_relat_1(X0) = k1_xboole_0) => k1_xboole_0 = X0))),
% 2.18/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.18/0.99  
% 2.18/0.99  fof(f19,plain,(
% 2.18/0.99    ! [X0] : ((k1_xboole_0 = X0 | (k1_xboole_0 != k2_relat_1(X0) & k1_relat_1(X0) != k1_xboole_0)) | ~v1_relat_1(X0))),
% 2.18/0.99    inference(ennf_transformation,[],[f3])).
% 2.18/0.99  
% 2.18/0.99  fof(f20,plain,(
% 2.18/0.99    ! [X0] : (k1_xboole_0 = X0 | (k1_xboole_0 != k2_relat_1(X0) & k1_relat_1(X0) != k1_xboole_0) | ~v1_relat_1(X0))),
% 2.18/0.99    inference(flattening,[],[f19])).
% 2.18/0.99  
% 2.18/0.99  fof(f45,plain,(
% 2.18/0.99    ( ! [X0] : (k1_xboole_0 = X0 | k1_xboole_0 != k2_relat_1(X0) | ~v1_relat_1(X0)) )),
% 2.18/0.99    inference(cnf_transformation,[],[f20])).
% 2.18/0.99  
% 2.18/0.99  fof(f4,axiom,(
% 2.18/0.99    k1_xboole_0 = k6_relat_1(k1_xboole_0)),
% 2.18/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.18/0.99  
% 2.18/0.99  fof(f46,plain,(
% 2.18/0.99    k1_xboole_0 = k6_relat_1(k1_xboole_0)),
% 2.18/0.99    inference(cnf_transformation,[],[f4])).
% 2.18/0.99  
% 2.18/0.99  fof(f12,axiom,(
% 2.18/0.99    ! [X0] : k6_relat_1(X0) = k6_partfun1(X0)),
% 2.18/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.18/0.99  
% 2.18/0.99  fof(f58,plain,(
% 2.18/0.99    ( ! [X0] : (k6_relat_1(X0) = k6_partfun1(X0)) )),
% 2.18/0.99    inference(cnf_transformation,[],[f12])).
% 2.18/0.99  
% 2.18/0.99  fof(f72,plain,(
% 2.18/0.99    k1_xboole_0 = k6_partfun1(k1_xboole_0)),
% 2.18/0.99    inference(definition_unfolding,[],[f46,f58])).
% 2.18/0.99  
% 2.18/0.99  fof(f5,axiom,(
% 2.18/0.99    ! [X0] : k6_relat_1(X0) = k2_funct_1(k6_relat_1(X0))),
% 2.18/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.18/0.99  
% 2.18/0.99  fof(f47,plain,(
% 2.18/0.99    ( ! [X0] : (k6_relat_1(X0) = k2_funct_1(k6_relat_1(X0))) )),
% 2.18/0.99    inference(cnf_transformation,[],[f5])).
% 2.18/0.99  
% 2.18/0.99  fof(f73,plain,(
% 2.18/0.99    ( ! [X0] : (k2_funct_1(k6_partfun1(X0)) = k6_partfun1(X0)) )),
% 2.18/0.99    inference(definition_unfolding,[],[f47,f58,f58])).
% 2.18/0.99  
% 2.18/0.99  cnf(c_20,negated_conjecture,
% 2.18/0.99      ( r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK0,sK0,sK0,sK1,sK2),k6_partfun1(sK0)) ),
% 2.18/0.99      inference(cnf_transformation,[],[f70]) ).
% 2.18/0.99  
% 2.18/0.99  cnf(c_1075,negated_conjecture,
% 2.18/0.99      ( r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK0,sK0,sK0,sK1,sK2),k6_partfun1(sK0)) ),
% 2.18/0.99      inference(subtyping,[status(esa)],[c_20]) ).
% 2.18/0.99  
% 2.18/0.99  cnf(c_1475,plain,
% 2.18/0.99      ( r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK0,sK0,sK0,sK1,sK2),k6_partfun1(sK0)) = iProver_top ),
% 2.18/0.99      inference(predicate_to_equality,[status(thm)],[c_1075]) ).
% 2.18/0.99  
% 2.18/0.99  cnf(c_25,negated_conjecture,
% 2.18/0.99      ( m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) ),
% 2.18/0.99      inference(cnf_transformation,[],[f65]) ).
% 2.18/0.99  
% 2.18/0.99  cnf(c_1071,negated_conjecture,
% 2.18/0.99      ( m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) ),
% 2.18/0.99      inference(subtyping,[status(esa)],[c_25]) ).
% 2.18/0.99  
% 2.18/0.99  cnf(c_1479,plain,
% 2.18/0.99      ( m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) = iProver_top ),
% 2.18/0.99      inference(predicate_to_equality,[status(thm)],[c_1071]) ).
% 2.18/0.99  
% 2.18/0.99  cnf(c_7,plain,
% 2.18/0.99      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 2.18/0.99      | k2_relset_1(X1,X2,X0) = k2_relat_1(X0) ),
% 2.18/0.99      inference(cnf_transformation,[],[f49]) ).
% 2.18/0.99  
% 2.18/0.99  cnf(c_1079,plain,
% 2.18/0.99      ( ~ m1_subset_1(X0_50,k1_zfmisc_1(k2_zfmisc_1(X1_50,X2_50)))
% 2.18/0.99      | k2_relset_1(X1_50,X2_50,X0_50) = k2_relat_1(X0_50) ),
% 2.18/0.99      inference(subtyping,[status(esa)],[c_7]) ).
% 2.18/0.99  
% 2.18/0.99  cnf(c_1471,plain,
% 2.18/0.99      ( k2_relset_1(X0_50,X1_50,X2_50) = k2_relat_1(X2_50)
% 2.18/0.99      | m1_subset_1(X2_50,k1_zfmisc_1(k2_zfmisc_1(X0_50,X1_50))) != iProver_top ),
% 2.18/0.99      inference(predicate_to_equality,[status(thm)],[c_1079]) ).
% 2.18/0.99  
% 2.18/0.99  cnf(c_2484,plain,
% 2.18/0.99      ( k2_relset_1(sK0,sK0,sK1) = k2_relat_1(sK1) ),
% 2.18/0.99      inference(superposition,[status(thm)],[c_1479,c_1471]) ).
% 2.18/0.99  
% 2.18/0.99  cnf(c_6,plain,
% 2.18/0.99      ( v5_relat_1(X0,X1) | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) ),
% 2.18/0.99      inference(cnf_transformation,[],[f48]) ).
% 2.18/0.99  
% 2.18/0.99  cnf(c_14,plain,
% 2.18/0.99      ( ~ v2_funct_2(X0,X1)
% 2.18/0.99      | ~ v5_relat_1(X0,X1)
% 2.18/0.99      | ~ v1_relat_1(X0)
% 2.18/0.99      | k2_relat_1(X0) = X1 ),
% 2.18/0.99      inference(cnf_transformation,[],[f55]) ).
% 2.18/0.99  
% 2.18/0.99  cnf(c_10,plain,
% 2.18/0.99      ( ~ v3_funct_2(X0,X1,X2)
% 2.18/0.99      | v2_funct_2(X0,X2)
% 2.18/0.99      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 2.18/0.99      | ~ v1_funct_1(X0) ),
% 2.18/0.99      inference(cnf_transformation,[],[f54]) ).
% 2.18/0.99  
% 2.18/0.99  cnf(c_26,negated_conjecture,
% 2.18/0.99      ( v3_funct_2(sK1,sK0,sK0) ),
% 2.18/0.99      inference(cnf_transformation,[],[f64]) ).
% 2.18/0.99  
% 2.18/0.99  cnf(c_345,plain,
% 2.18/0.99      ( v2_funct_2(X0,X1)
% 2.18/0.99      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X2,X1)))
% 2.18/0.99      | ~ v1_funct_1(X0)
% 2.18/0.99      | sK1 != X0
% 2.18/0.99      | sK0 != X1
% 2.18/0.99      | sK0 != X2 ),
% 2.18/0.99      inference(resolution_lifted,[status(thm)],[c_10,c_26]) ).
% 2.18/0.99  
% 2.18/0.99  cnf(c_346,plain,
% 2.18/0.99      ( v2_funct_2(sK1,sK0)
% 2.18/0.99      | ~ m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
% 2.18/0.99      | ~ v1_funct_1(sK1) ),
% 2.18/0.99      inference(unflattening,[status(thm)],[c_345]) ).
% 2.18/0.99  
% 2.18/0.99  cnf(c_28,negated_conjecture,
% 2.18/0.99      ( v1_funct_1(sK1) ),
% 2.18/0.99      inference(cnf_transformation,[],[f62]) ).
% 2.18/0.99  
% 2.18/0.99  cnf(c_348,plain,
% 2.18/0.99      ( v2_funct_2(sK1,sK0) ),
% 2.18/0.99      inference(global_propositional_subsumption,
% 2.18/0.99                [status(thm)],
% 2.18/0.99                [c_346,c_28,c_25]) ).
% 2.18/0.99  
% 2.18/0.99  cnf(c_431,plain,
% 2.18/0.99      ( ~ v5_relat_1(X0,X1)
% 2.18/0.99      | ~ v1_relat_1(X0)
% 2.18/0.99      | k2_relat_1(X0) = X1
% 2.18/0.99      | sK1 != X0
% 2.18/0.99      | sK0 != X1 ),
% 2.18/0.99      inference(resolution_lifted,[status(thm)],[c_14,c_348]) ).
% 2.18/0.99  
% 2.18/0.99  cnf(c_432,plain,
% 2.18/0.99      ( ~ v5_relat_1(sK1,sK0) | ~ v1_relat_1(sK1) | k2_relat_1(sK1) = sK0 ),
% 2.18/0.99      inference(unflattening,[status(thm)],[c_431]) ).
% 2.18/0.99  
% 2.18/0.99  cnf(c_478,plain,
% 2.18/0.99      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 2.18/0.99      | ~ v1_relat_1(sK1)
% 2.18/0.99      | k2_relat_1(sK1) = sK0
% 2.18/0.99      | sK1 != X0
% 2.18/0.99      | sK0 != X2 ),
% 2.18/0.99      inference(resolution_lifted,[status(thm)],[c_6,c_432]) ).
% 2.18/0.99  
% 2.18/0.99  cnf(c_479,plain,
% 2.18/0.99      ( ~ m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(X0,sK0)))
% 2.18/0.99      | ~ v1_relat_1(sK1)
% 2.18/0.99      | k2_relat_1(sK1) = sK0 ),
% 2.18/0.99      inference(unflattening,[status(thm)],[c_478]) ).
% 2.18/0.99  
% 2.18/0.99  cnf(c_481,plain,
% 2.18/0.99      ( ~ m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
% 2.18/0.99      | ~ v1_relat_1(sK1)
% 2.18/0.99      | k2_relat_1(sK1) = sK0 ),
% 2.18/0.99      inference(instantiation,[status(thm)],[c_479]) ).
% 2.18/0.99  
% 2.18/0.99  cnf(c_483,plain,
% 2.18/0.99      ( ~ v1_relat_1(sK1) | k2_relat_1(sK1) = sK0 ),
% 2.18/0.99      inference(global_propositional_subsumption,
% 2.18/0.99                [status(thm)],
% 2.18/0.99                [c_479,c_25,c_481]) ).
% 2.18/0.99  
% 2.18/0.99  cnf(c_1063,plain,
% 2.18/0.99      ( ~ v1_relat_1(sK1) | k2_relat_1(sK1) = sK0 ),
% 2.18/0.99      inference(subtyping,[status(esa)],[c_483]) ).
% 2.18/0.99  
% 2.18/0.99  cnf(c_1485,plain,
% 2.18/0.99      ( k2_relat_1(sK1) = sK0 | v1_relat_1(sK1) != iProver_top ),
% 2.18/0.99      inference(predicate_to_equality,[status(thm)],[c_1063]) ).
% 2.18/0.99  
% 2.18/0.99  cnf(c_1,plain,
% 2.18/0.99      ( v1_relat_1(k2_zfmisc_1(X0,X1)) ),
% 2.18/0.99      inference(cnf_transformation,[],[f43]) ).
% 2.18/0.99  
% 2.18/0.99  cnf(c_84,plain,
% 2.18/0.99      ( v1_relat_1(k2_zfmisc_1(sK0,sK0)) ),
% 2.18/0.99      inference(instantiation,[status(thm)],[c_1]) ).
% 2.18/0.99  
% 2.18/0.99  cnf(c_0,plain,
% 2.18/0.99      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1)) | ~ v1_relat_1(X1) | v1_relat_1(X0) ),
% 2.18/0.99      inference(cnf_transformation,[],[f42]) ).
% 2.18/0.99  
% 2.18/0.99  cnf(c_1085,plain,
% 2.18/0.99      ( ~ m1_subset_1(X0_50,k1_zfmisc_1(X1_50))
% 2.18/0.99      | ~ v1_relat_1(X1_50)
% 2.18/0.99      | v1_relat_1(X0_50) ),
% 2.18/0.99      inference(subtyping,[status(esa)],[c_0]) ).
% 2.18/0.99  
% 2.18/0.99  cnf(c_1642,plain,
% 2.18/0.99      ( ~ m1_subset_1(X0_50,k1_zfmisc_1(k2_zfmisc_1(X1_50,X2_50)))
% 2.18/0.99      | v1_relat_1(X0_50)
% 2.18/0.99      | ~ v1_relat_1(k2_zfmisc_1(X1_50,X2_50)) ),
% 2.18/0.99      inference(instantiation,[status(thm)],[c_1085]) ).
% 2.18/0.99  
% 2.18/0.99  cnf(c_1845,plain,
% 2.18/0.99      ( ~ m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
% 2.18/0.99      | ~ v1_relat_1(k2_zfmisc_1(sK0,sK0))
% 2.18/0.99      | v1_relat_1(sK1) ),
% 2.18/0.99      inference(instantiation,[status(thm)],[c_1642]) ).
% 2.18/0.99  
% 2.18/0.99  cnf(c_2008,plain,
% 2.18/0.99      ( k2_relat_1(sK1) = sK0 ),
% 2.18/0.99      inference(global_propositional_subsumption,
% 2.18/0.99                [status(thm)],
% 2.18/0.99                [c_1485,c_25,c_84,c_1063,c_1845]) ).
% 2.18/0.99  
% 2.18/0.99  cnf(c_2486,plain,
% 2.18/0.99      ( k2_relset_1(sK0,sK0,sK1) = sK0 ),
% 2.18/0.99      inference(light_normalisation,[status(thm)],[c_2484,c_2008]) ).
% 2.18/0.99  
% 2.18/0.99  cnf(c_18,plain,
% 2.18/0.99      ( ~ r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0))
% 2.18/0.99      | ~ v1_funct_2(X3,X1,X0)
% 2.18/0.99      | ~ v1_funct_2(X2,X0,X1)
% 2.18/0.99      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
% 2.18/0.99      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
% 2.18/0.99      | ~ v2_funct_1(X2)
% 2.18/0.99      | ~ v1_funct_1(X2)
% 2.18/0.99      | ~ v1_funct_1(X3)
% 2.18/0.99      | k2_relset_1(X0,X1,X2) != X1
% 2.18/0.99      | k2_funct_1(X2) = X3
% 2.18/0.99      | k1_xboole_0 = X0
% 2.18/0.99      | k1_xboole_0 = X1 ),
% 2.18/0.99      inference(cnf_transformation,[],[f61]) ).
% 2.18/0.99  
% 2.18/0.99  cnf(c_17,plain,
% 2.18/0.99      ( ~ r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0))
% 2.18/0.99      | ~ v1_funct_2(X3,X1,X0)
% 2.18/0.99      | ~ v1_funct_2(X2,X0,X1)
% 2.18/0.99      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
% 2.18/0.99      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
% 2.18/0.99      | v2_funct_1(X2)
% 2.18/0.99      | ~ v1_funct_1(X2)
% 2.18/0.99      | ~ v1_funct_1(X3) ),
% 2.18/0.99      inference(cnf_transformation,[],[f59]) ).
% 2.18/0.99  
% 2.18/0.99  cnf(c_152,plain,
% 2.18/0.99      ( ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
% 2.18/0.99      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
% 2.18/0.99      | ~ v1_funct_2(X2,X0,X1)
% 2.18/0.99      | ~ v1_funct_2(X3,X1,X0)
% 2.18/0.99      | ~ r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0))
% 2.18/0.99      | ~ v1_funct_1(X2)
% 2.18/0.99      | ~ v1_funct_1(X3)
% 2.18/0.99      | k2_relset_1(X0,X1,X2) != X1
% 2.18/0.99      | k2_funct_1(X2) = X3
% 2.18/0.99      | k1_xboole_0 = X0
% 2.18/0.99      | k1_xboole_0 = X1 ),
% 2.18/0.99      inference(global_propositional_subsumption,[status(thm)],[c_18,c_17]) ).
% 2.18/0.99  
% 2.18/0.99  cnf(c_153,plain,
% 2.18/0.99      ( ~ r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0))
% 2.18/0.99      | ~ v1_funct_2(X3,X1,X0)
% 2.18/0.99      | ~ v1_funct_2(X2,X0,X1)
% 2.18/0.99      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
% 2.18/0.99      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
% 2.18/0.99      | ~ v1_funct_1(X2)
% 2.18/0.99      | ~ v1_funct_1(X3)
% 2.18/0.99      | k2_relset_1(X0,X1,X2) != X1
% 2.18/0.99      | k2_funct_1(X2) = X3
% 2.18/0.99      | k1_xboole_0 = X1
% 2.18/0.99      | k1_xboole_0 = X0 ),
% 2.18/0.99      inference(renaming,[status(thm)],[c_152]) ).
% 2.18/0.99  
% 2.18/0.99  cnf(c_1068,plain,
% 2.18/0.99      ( ~ r2_relset_1(X0_50,X0_50,k1_partfun1(X0_50,X1_50,X1_50,X0_50,X2_50,X3_50),k6_partfun1(X0_50))
% 2.18/0.99      | ~ v1_funct_2(X3_50,X1_50,X0_50)
% 2.18/0.99      | ~ v1_funct_2(X2_50,X0_50,X1_50)
% 2.18/0.99      | ~ m1_subset_1(X3_50,k1_zfmisc_1(k2_zfmisc_1(X1_50,X0_50)))
% 2.18/0.99      | ~ m1_subset_1(X2_50,k1_zfmisc_1(k2_zfmisc_1(X0_50,X1_50)))
% 2.18/0.99      | ~ v1_funct_1(X2_50)
% 2.18/0.99      | ~ v1_funct_1(X3_50)
% 2.18/0.99      | k2_relset_1(X0_50,X1_50,X2_50) != X1_50
% 2.18/0.99      | k2_funct_1(X2_50) = X3_50
% 2.18/0.99      | k1_xboole_0 = X1_50
% 2.18/0.99      | k1_xboole_0 = X0_50 ),
% 2.18/0.99      inference(subtyping,[status(esa)],[c_153]) ).
% 2.18/0.99  
% 2.18/0.99  cnf(c_1482,plain,
% 2.18/0.99      ( k2_relset_1(X0_50,X1_50,X2_50) != X1_50
% 2.18/0.99      | k2_funct_1(X2_50) = X3_50
% 2.18/0.99      | k1_xboole_0 = X1_50
% 2.18/0.99      | k1_xboole_0 = X0_50
% 2.18/0.99      | r2_relset_1(X0_50,X0_50,k1_partfun1(X0_50,X1_50,X1_50,X0_50,X2_50,X3_50),k6_partfun1(X0_50)) != iProver_top
% 2.18/0.99      | v1_funct_2(X3_50,X1_50,X0_50) != iProver_top
% 2.18/0.99      | v1_funct_2(X2_50,X0_50,X1_50) != iProver_top
% 2.18/0.99      | m1_subset_1(X2_50,k1_zfmisc_1(k2_zfmisc_1(X0_50,X1_50))) != iProver_top
% 2.18/0.99      | m1_subset_1(X3_50,k1_zfmisc_1(k2_zfmisc_1(X1_50,X0_50))) != iProver_top
% 2.18/0.99      | v1_funct_1(X2_50) != iProver_top
% 2.18/0.99      | v1_funct_1(X3_50) != iProver_top ),
% 2.18/0.99      inference(predicate_to_equality,[status(thm)],[c_1068]) ).
% 2.18/0.99  
% 2.18/0.99  cnf(c_2973,plain,
% 2.18/0.99      ( k2_funct_1(sK1) = X0_50
% 2.18/0.99      | sK0 = k1_xboole_0
% 2.18/0.99      | r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK0,sK0,sK0,sK1,X0_50),k6_partfun1(sK0)) != iProver_top
% 2.18/0.99      | v1_funct_2(X0_50,sK0,sK0) != iProver_top
% 2.18/0.99      | v1_funct_2(sK1,sK0,sK0) != iProver_top
% 2.18/0.99      | m1_subset_1(X0_50,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) != iProver_top
% 2.18/0.99      | m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) != iProver_top
% 2.18/0.99      | v1_funct_1(X0_50) != iProver_top
% 2.18/0.99      | v1_funct_1(sK1) != iProver_top ),
% 2.18/0.99      inference(superposition,[status(thm)],[c_2486,c_1482]) ).
% 2.18/0.99  
% 2.18/0.99  cnf(c_29,plain,
% 2.18/0.99      ( v1_funct_1(sK1) = iProver_top ),
% 2.18/0.99      inference(predicate_to_equality,[status(thm)],[c_28]) ).
% 2.18/0.99  
% 2.18/0.99  cnf(c_27,negated_conjecture,
% 2.18/0.99      ( v1_funct_2(sK1,sK0,sK0) ),
% 2.18/0.99      inference(cnf_transformation,[],[f63]) ).
% 2.18/0.99  
% 2.18/0.99  cnf(c_30,plain,
% 2.18/0.99      ( v1_funct_2(sK1,sK0,sK0) = iProver_top ),
% 2.18/0.99      inference(predicate_to_equality,[status(thm)],[c_27]) ).
% 2.18/0.99  
% 2.18/0.99  cnf(c_32,plain,
% 2.18/0.99      ( m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) = iProver_top ),
% 2.18/0.99      inference(predicate_to_equality,[status(thm)],[c_25]) ).
% 2.18/0.99  
% 2.18/0.99  cnf(c_3412,plain,
% 2.18/0.99      ( v1_funct_1(X0_50) != iProver_top
% 2.18/0.99      | v1_funct_2(X0_50,sK0,sK0) != iProver_top
% 2.18/0.99      | r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK0,sK0,sK0,sK1,X0_50),k6_partfun1(sK0)) != iProver_top
% 2.18/0.99      | sK0 = k1_xboole_0
% 2.18/0.99      | k2_funct_1(sK1) = X0_50
% 2.18/0.99      | m1_subset_1(X0_50,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) != iProver_top ),
% 2.18/0.99      inference(global_propositional_subsumption,
% 2.18/0.99                [status(thm)],
% 2.18/0.99                [c_2973,c_29,c_30,c_32]) ).
% 2.18/0.99  
% 2.18/0.99  cnf(c_3413,plain,
% 2.18/0.99      ( k2_funct_1(sK1) = X0_50
% 2.18/0.99      | sK0 = k1_xboole_0
% 2.18/0.99      | r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK0,sK0,sK0,sK1,X0_50),k6_partfun1(sK0)) != iProver_top
% 2.18/0.99      | v1_funct_2(X0_50,sK0,sK0) != iProver_top
% 2.18/0.99      | m1_subset_1(X0_50,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) != iProver_top
% 2.18/0.99      | v1_funct_1(X0_50) != iProver_top ),
% 2.18/0.99      inference(renaming,[status(thm)],[c_3412]) ).
% 2.18/0.99  
% 2.18/0.99  cnf(c_3424,plain,
% 2.18/0.99      ( k2_funct_1(sK1) = sK2
% 2.18/0.99      | sK0 = k1_xboole_0
% 2.18/0.99      | v1_funct_2(sK2,sK0,sK0) != iProver_top
% 2.18/0.99      | m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) != iProver_top
% 2.18/0.99      | v1_funct_1(sK2) != iProver_top ),
% 2.18/0.99      inference(superposition,[status(thm)],[c_1475,c_3413]) ).
% 2.18/0.99  
% 2.18/0.99  cnf(c_24,negated_conjecture,
% 2.18/0.99      ( v1_funct_1(sK2) ),
% 2.18/0.99      inference(cnf_transformation,[],[f66]) ).
% 2.18/0.99  
% 2.18/0.99  cnf(c_33,plain,
% 2.18/0.99      ( v1_funct_1(sK2) = iProver_top ),
% 2.18/0.99      inference(predicate_to_equality,[status(thm)],[c_24]) ).
% 2.18/0.99  
% 2.18/0.99  cnf(c_23,negated_conjecture,
% 2.18/0.99      ( v1_funct_2(sK2,sK0,sK0) ),
% 2.18/0.99      inference(cnf_transformation,[],[f67]) ).
% 2.18/0.99  
% 2.18/0.99  cnf(c_34,plain,
% 2.18/0.99      ( v1_funct_2(sK2,sK0,sK0) = iProver_top ),
% 2.18/0.99      inference(predicate_to_equality,[status(thm)],[c_23]) ).
% 2.18/0.99  
% 2.18/0.99  cnf(c_21,negated_conjecture,
% 2.18/0.99      ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) ),
% 2.18/0.99      inference(cnf_transformation,[],[f69]) ).
% 2.18/0.99  
% 2.18/0.99  cnf(c_36,plain,
% 2.18/0.99      ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) = iProver_top ),
% 2.18/0.99      inference(predicate_to_equality,[status(thm)],[c_21]) ).
% 2.18/0.99  
% 2.18/0.99  cnf(c_1087,plain,( X0_50 = X0_50 ),theory(equality) ).
% 2.18/0.99  
% 2.18/0.99  cnf(c_1115,plain,
% 2.18/0.99      ( sK0 = sK0 ),
% 2.18/0.99      inference(instantiation,[status(thm)],[c_1087]) ).
% 2.18/0.99  
% 2.18/0.99  cnf(c_19,negated_conjecture,
% 2.18/0.99      ( ~ r2_relset_1(sK0,sK0,sK2,k2_funct_2(sK0,sK1)) ),
% 2.18/0.99      inference(cnf_transformation,[],[f71]) ).
% 2.18/0.99  
% 2.18/0.99  cnf(c_1076,negated_conjecture,
% 2.18/0.99      ( ~ r2_relset_1(sK0,sK0,sK2,k2_funct_2(sK0,sK1)) ),
% 2.18/0.99      inference(subtyping,[status(esa)],[c_19]) ).
% 2.18/0.99  
% 2.18/0.99  cnf(c_1474,plain,
% 2.18/0.99      ( r2_relset_1(sK0,sK0,sK2,k2_funct_2(sK0,sK1)) != iProver_top ),
% 2.18/0.99      inference(predicate_to_equality,[status(thm)],[c_1076]) ).
% 2.18/0.99  
% 2.18/0.99  cnf(c_15,plain,
% 2.18/0.99      ( ~ v1_funct_2(X0,X1,X1)
% 2.18/0.99      | ~ v3_funct_2(X0,X1,X1)
% 2.18/0.99      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X1)))
% 2.18/0.99      | ~ v1_funct_1(X0)
% 2.18/0.99      | k2_funct_2(X1,X0) = k2_funct_1(X0) ),
% 2.18/0.99      inference(cnf_transformation,[],[f57]) ).
% 2.18/0.99  
% 2.18/0.99  cnf(c_364,plain,
% 2.18/0.99      ( ~ v1_funct_2(X0,X1,X1)
% 2.18/0.99      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X1)))
% 2.18/0.99      | ~ v1_funct_1(X0)
% 2.18/0.99      | k2_funct_2(X1,X0) = k2_funct_1(X0)
% 2.18/0.99      | sK1 != X0
% 2.18/0.99      | sK0 != X1 ),
% 2.18/0.99      inference(resolution_lifted,[status(thm)],[c_15,c_26]) ).
% 2.18/0.99  
% 2.18/0.99  cnf(c_365,plain,
% 2.18/0.99      ( ~ v1_funct_2(sK1,sK0,sK0)
% 2.18/0.99      | ~ m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
% 2.18/0.99      | ~ v1_funct_1(sK1)
% 2.18/0.99      | k2_funct_2(sK0,sK1) = k2_funct_1(sK1) ),
% 2.18/0.99      inference(unflattening,[status(thm)],[c_364]) ).
% 2.18/0.99  
% 2.18/0.99  cnf(c_367,plain,
% 2.18/0.99      ( k2_funct_2(sK0,sK1) = k2_funct_1(sK1) ),
% 2.18/0.99      inference(global_propositional_subsumption,
% 2.18/0.99                [status(thm)],
% 2.18/0.99                [c_365,c_28,c_27,c_25]) ).
% 2.18/0.99  
% 2.18/0.99  cnf(c_1066,plain,
% 2.18/0.99      ( k2_funct_2(sK0,sK1) = k2_funct_1(sK1) ),
% 2.18/0.99      inference(subtyping,[status(esa)],[c_367]) ).
% 2.18/0.99  
% 2.18/0.99  cnf(c_1508,plain,
% 2.18/0.99      ( r2_relset_1(sK0,sK0,sK2,k2_funct_1(sK1)) != iProver_top ),
% 2.18/0.99      inference(light_normalisation,[status(thm)],[c_1474,c_1066]) ).
% 2.18/0.99  
% 2.18/0.99  cnf(c_1606,plain,
% 2.18/0.99      ( ~ r2_relset_1(sK0,sK0,sK2,k2_funct_1(sK1)) ),
% 2.18/0.99      inference(predicate_to_equality_rev,[status(thm)],[c_1508]) ).
% 2.18/0.99  
% 2.18/0.99  cnf(c_8,plain,
% 2.18/0.99      ( r2_relset_1(X0,X1,X2,X2)
% 2.18/0.99      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ),
% 2.18/0.99      inference(cnf_transformation,[],[f74]) ).
% 2.18/0.99  
% 2.18/0.99  cnf(c_1078,plain,
% 2.18/0.99      ( r2_relset_1(X0_50,X1_50,X2_50,X2_50)
% 2.18/0.99      | ~ m1_subset_1(X2_50,k1_zfmisc_1(k2_zfmisc_1(X0_50,X1_50))) ),
% 2.18/0.99      inference(subtyping,[status(esa)],[c_8]) ).
% 2.18/0.99  
% 2.18/0.99  cnf(c_1657,plain,
% 2.18/0.99      ( r2_relset_1(sK0,sK0,sK2,sK2)
% 2.18/0.99      | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) ),
% 2.18/0.99      inference(instantiation,[status(thm)],[c_1078]) ).
% 2.18/0.99  
% 2.18/0.99  cnf(c_1767,plain,
% 2.18/0.99      ( sK2 = sK2 ),
% 2.18/0.99      inference(instantiation,[status(thm)],[c_1087]) ).
% 2.18/0.99  
% 2.18/0.99  cnf(c_1097,plain,
% 2.18/0.99      ( ~ r2_relset_1(X0_50,X1_50,X2_50,X3_50)
% 2.18/0.99      | r2_relset_1(X4_50,X5_50,X6_50,X7_50)
% 2.18/0.99      | X4_50 != X0_50
% 2.18/0.99      | X5_50 != X1_50
% 2.18/0.99      | X6_50 != X2_50
% 2.18/0.99      | X7_50 != X3_50 ),
% 2.18/0.99      theory(equality) ).
% 2.18/0.99  
% 2.18/0.99  cnf(c_1735,plain,
% 2.18/0.99      ( r2_relset_1(X0_50,X1_50,X2_50,X3_50)
% 2.18/0.99      | ~ r2_relset_1(sK0,sK0,sK2,sK2)
% 2.18/0.99      | X2_50 != sK2
% 2.18/0.99      | X3_50 != sK2
% 2.18/0.99      | X1_50 != sK0
% 2.18/0.99      | X0_50 != sK0 ),
% 2.18/0.99      inference(instantiation,[status(thm)],[c_1097]) ).
% 2.18/0.99  
% 2.18/0.99  cnf(c_1967,plain,
% 2.18/0.99      ( r2_relset_1(X0_50,X1_50,sK2,X2_50)
% 2.18/0.99      | ~ r2_relset_1(sK0,sK0,sK2,sK2)
% 2.18/0.99      | X2_50 != sK2
% 2.18/0.99      | X1_50 != sK0
% 2.18/0.99      | X0_50 != sK0
% 2.18/0.99      | sK2 != sK2 ),
% 2.18/0.99      inference(instantiation,[status(thm)],[c_1735]) ).
% 2.18/0.99  
% 2.18/0.99  cnf(c_3226,plain,
% 2.18/0.99      ( r2_relset_1(X0_50,X1_50,sK2,k2_funct_1(sK1))
% 2.18/0.99      | ~ r2_relset_1(sK0,sK0,sK2,sK2)
% 2.18/0.99      | X1_50 != sK0
% 2.18/0.99      | X0_50 != sK0
% 2.18/0.99      | k2_funct_1(sK1) != sK2
% 2.18/0.99      | sK2 != sK2 ),
% 2.18/0.99      inference(instantiation,[status(thm)],[c_1967]) ).
% 2.18/0.99  
% 2.18/0.99  cnf(c_3233,plain,
% 2.18/0.99      ( r2_relset_1(sK0,sK0,sK2,k2_funct_1(sK1))
% 2.18/0.99      | ~ r2_relset_1(sK0,sK0,sK2,sK2)
% 2.18/0.99      | k2_funct_1(sK1) != sK2
% 2.18/0.99      | sK2 != sK2
% 2.18/0.99      | sK0 != sK0 ),
% 2.18/0.99      inference(instantiation,[status(thm)],[c_3226]) ).
% 2.18/0.99  
% 2.18/0.99  cnf(c_3427,plain,
% 2.18/0.99      ( sK0 = k1_xboole_0 ),
% 2.18/0.99      inference(global_propositional_subsumption,
% 2.18/0.99                [status(thm)],
% 2.18/0.99                [c_3424,c_33,c_34,c_21,c_36,c_1115,c_1606,c_1657,c_1767,c_3233]) ).
% 2.18/0.99  
% 2.18/0.99  cnf(c_1074,negated_conjecture,
% 2.18/0.99      ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) ),
% 2.18/0.99      inference(subtyping,[status(esa)],[c_21]) ).
% 2.18/0.99  
% 2.18/0.99  cnf(c_1476,plain,
% 2.18/0.99      ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) = iProver_top ),
% 2.18/0.99      inference(predicate_to_equality,[status(thm)],[c_1074]) ).
% 2.18/0.99  
% 2.18/0.99  cnf(c_1472,plain,
% 2.18/0.99      ( r2_relset_1(X0_50,X1_50,X2_50,X2_50) = iProver_top
% 2.18/0.99      | m1_subset_1(X2_50,k1_zfmisc_1(k2_zfmisc_1(X0_50,X1_50))) != iProver_top ),
% 2.18/0.99      inference(predicate_to_equality,[status(thm)],[c_1078]) ).
% 2.18/0.99  
% 2.18/0.99  cnf(c_2561,plain,
% 2.18/0.99      ( r2_relset_1(sK0,sK0,sK2,sK2) = iProver_top ),
% 2.18/0.99      inference(superposition,[status(thm)],[c_1476,c_1472]) ).
% 2.18/0.99  
% 2.18/0.99  cnf(c_3439,plain,
% 2.18/0.99      ( r2_relset_1(k1_xboole_0,k1_xboole_0,sK2,sK2) = iProver_top ),
% 2.18/0.99      inference(demodulation,[status(thm)],[c_3427,c_2561]) ).
% 2.18/0.99  
% 2.18/0.99  cnf(c_22,negated_conjecture,
% 2.18/0.99      ( v3_funct_2(sK2,sK0,sK0) ),
% 2.18/0.99      inference(cnf_transformation,[],[f68]) ).
% 2.18/0.99  
% 2.18/0.99  cnf(c_334,plain,
% 2.18/0.99      ( v2_funct_2(X0,X1)
% 2.18/0.99      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X2,X1)))
% 2.18/0.99      | ~ v1_funct_1(X0)
% 2.18/0.99      | sK2 != X0
% 2.18/0.99      | sK0 != X1
% 2.18/0.99      | sK0 != X2 ),
% 2.18/0.99      inference(resolution_lifted,[status(thm)],[c_10,c_22]) ).
% 2.18/0.99  
% 2.18/0.99  cnf(c_335,plain,
% 2.18/0.99      ( v2_funct_2(sK2,sK0)
% 2.18/0.99      | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
% 2.18/0.99      | ~ v1_funct_1(sK2) ),
% 2.18/0.99      inference(unflattening,[status(thm)],[c_334]) ).
% 2.18/0.99  
% 2.18/0.99  cnf(c_337,plain,
% 2.18/0.99      ( v2_funct_2(sK2,sK0) ),
% 2.18/0.99      inference(global_propositional_subsumption,
% 2.18/0.99                [status(thm)],
% 2.18/0.99                [c_335,c_24,c_21]) ).
% 2.18/0.99  
% 2.18/0.99  cnf(c_418,plain,
% 2.18/0.99      ( ~ v5_relat_1(X0,X1)
% 2.18/0.99      | ~ v1_relat_1(X0)
% 2.18/0.99      | k2_relat_1(X0) = X1
% 2.18/0.99      | sK2 != X0
% 2.18/0.99      | sK0 != X1 ),
% 2.18/0.99      inference(resolution_lifted,[status(thm)],[c_14,c_337]) ).
% 2.18/0.99  
% 2.18/0.99  cnf(c_419,plain,
% 2.18/0.99      ( ~ v5_relat_1(sK2,sK0) | ~ v1_relat_1(sK2) | k2_relat_1(sK2) = sK0 ),
% 2.18/0.99      inference(unflattening,[status(thm)],[c_418]) ).
% 2.18/0.99  
% 2.18/0.99  cnf(c_462,plain,
% 2.18/0.99      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 2.18/0.99      | ~ v1_relat_1(sK2)
% 2.18/0.99      | k2_relat_1(sK2) = sK0
% 2.18/0.99      | sK2 != X0
% 2.18/0.99      | sK0 != X2 ),
% 2.18/0.99      inference(resolution_lifted,[status(thm)],[c_6,c_419]) ).
% 2.18/0.99  
% 2.18/0.99  cnf(c_463,plain,
% 2.18/0.99      ( ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X0,sK0)))
% 2.18/0.99      | ~ v1_relat_1(sK2)
% 2.18/0.99      | k2_relat_1(sK2) = sK0 ),
% 2.18/0.99      inference(unflattening,[status(thm)],[c_462]) ).
% 2.18/0.99  
% 2.18/0.99  cnf(c_465,plain,
% 2.18/0.99      ( ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
% 2.18/0.99      | ~ v1_relat_1(sK2)
% 2.18/0.99      | k2_relat_1(sK2) = sK0 ),
% 2.18/0.99      inference(instantiation,[status(thm)],[c_463]) ).
% 2.18/0.99  
% 2.18/0.99  cnf(c_467,plain,
% 2.18/0.99      ( ~ v1_relat_1(sK2) | k2_relat_1(sK2) = sK0 ),
% 2.18/0.99      inference(global_propositional_subsumption,
% 2.18/0.99                [status(thm)],
% 2.18/0.99                [c_463,c_21,c_465]) ).
% 2.18/0.99  
% 2.18/0.99  cnf(c_1064,plain,
% 2.18/0.99      ( ~ v1_relat_1(sK2) | k2_relat_1(sK2) = sK0 ),
% 2.18/0.99      inference(subtyping,[status(esa)],[c_467]) ).
% 2.18/0.99  
% 2.18/0.99  cnf(c_1484,plain,
% 2.18/0.99      ( k2_relat_1(sK2) = sK0 | v1_relat_1(sK2) != iProver_top ),
% 2.18/0.99      inference(predicate_to_equality,[status(thm)],[c_1064]) ).
% 2.18/0.99  
% 2.18/0.99  cnf(c_1842,plain,
% 2.18/0.99      ( ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
% 2.18/0.99      | ~ v1_relat_1(k2_zfmisc_1(sK0,sK0))
% 2.18/0.99      | v1_relat_1(sK2) ),
% 2.18/0.99      inference(instantiation,[status(thm)],[c_1642]) ).
% 2.18/0.99  
% 2.18/0.99  cnf(c_2004,plain,
% 2.18/0.99      ( k2_relat_1(sK2) = sK0 ),
% 2.18/0.99      inference(global_propositional_subsumption,
% 2.18/0.99                [status(thm)],
% 2.18/0.99                [c_1484,c_21,c_84,c_1064,c_1842]) ).
% 2.18/0.99  
% 2.18/0.99  cnf(c_2,plain,
% 2.18/0.99      ( ~ v1_relat_1(X0) | k2_relat_1(X0) != k1_xboole_0 | k1_xboole_0 = X0 ),
% 2.18/0.99      inference(cnf_transformation,[],[f45]) ).
% 2.18/0.99  
% 2.18/0.99  cnf(c_1083,plain,
% 2.18/0.99      ( ~ v1_relat_1(X0_50)
% 2.18/0.99      | k2_relat_1(X0_50) != k1_xboole_0
% 2.18/0.99      | k1_xboole_0 = X0_50 ),
% 2.18/0.99      inference(subtyping,[status(esa)],[c_2]) ).
% 2.18/0.99  
% 2.18/0.99  cnf(c_1469,plain,
% 2.18/0.99      ( k2_relat_1(X0_50) != k1_xboole_0
% 2.18/0.99      | k1_xboole_0 = X0_50
% 2.18/0.99      | v1_relat_1(X0_50) != iProver_top ),
% 2.18/0.99      inference(predicate_to_equality,[status(thm)],[c_1083]) ).
% 2.18/0.99  
% 2.18/0.99  cnf(c_2333,plain,
% 2.18/0.99      ( sK2 = k1_xboole_0
% 2.18/0.99      | sK0 != k1_xboole_0
% 2.18/0.99      | v1_relat_1(sK2) != iProver_top ),
% 2.18/0.99      inference(superposition,[status(thm)],[c_2004,c_1469]) ).
% 2.18/0.99  
% 2.18/0.99  cnf(c_2347,plain,
% 2.18/0.99      ( ~ v1_relat_1(sK2) | sK2 = k1_xboole_0 | sK0 != k1_xboole_0 ),
% 2.18/0.99      inference(predicate_to_equality_rev,[status(thm)],[c_2333]) ).
% 2.18/0.99  
% 2.18/0.99  cnf(c_2350,plain,
% 2.18/0.99      ( sK0 != k1_xboole_0 | sK2 = k1_xboole_0 ),
% 2.18/0.99      inference(global_propositional_subsumption,
% 2.18/0.99                [status(thm)],
% 2.18/0.99                [c_2333,c_21,c_84,c_1842,c_2347]) ).
% 2.18/0.99  
% 2.18/0.99  cnf(c_2351,plain,
% 2.18/0.99      ( sK2 = k1_xboole_0 | sK0 != k1_xboole_0 ),
% 2.18/0.99      inference(renaming,[status(thm)],[c_2350]) ).
% 2.18/0.99  
% 2.18/0.99  cnf(c_3441,plain,
% 2.18/0.99      ( sK2 = k1_xboole_0 | k1_xboole_0 != k1_xboole_0 ),
% 2.18/0.99      inference(demodulation,[status(thm)],[c_3427,c_2351]) ).
% 2.18/0.99  
% 2.18/0.99  cnf(c_3473,plain,
% 2.18/0.99      ( sK2 = k1_xboole_0 ),
% 2.18/0.99      inference(equality_resolution_simp,[status(thm)],[c_3441]) ).
% 2.18/0.99  
% 2.18/0.99  cnf(c_3509,plain,
% 2.18/0.99      ( r2_relset_1(k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0) = iProver_top ),
% 2.18/0.99      inference(light_normalisation,[status(thm)],[c_3439,c_3473]) ).
% 2.18/0.99  
% 2.18/0.99  cnf(c_2334,plain,
% 2.18/0.99      ( sK1 = k1_xboole_0
% 2.18/0.99      | sK0 != k1_xboole_0
% 2.18/0.99      | v1_relat_1(sK1) != iProver_top ),
% 2.18/0.99      inference(superposition,[status(thm)],[c_2008,c_1469]) ).
% 2.18/0.99  
% 2.18/0.99  cnf(c_83,plain,
% 2.18/0.99      ( v1_relat_1(k2_zfmisc_1(X0,X1)) = iProver_top ),
% 2.18/0.99      inference(predicate_to_equality,[status(thm)],[c_1]) ).
% 2.18/0.99  
% 2.18/0.99  cnf(c_85,plain,
% 2.18/0.99      ( v1_relat_1(k2_zfmisc_1(sK0,sK0)) = iProver_top ),
% 2.18/0.99      inference(instantiation,[status(thm)],[c_83]) ).
% 2.18/0.99  
% 2.18/0.99  cnf(c_1846,plain,
% 2.18/0.99      ( m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) != iProver_top
% 2.18/0.99      | v1_relat_1(k2_zfmisc_1(sK0,sK0)) != iProver_top
% 2.18/0.99      | v1_relat_1(sK1) = iProver_top ),
% 2.18/0.99      inference(predicate_to_equality,[status(thm)],[c_1845]) ).
% 2.18/0.99  
% 2.18/0.99  cnf(c_2431,plain,
% 2.18/0.99      ( sK0 != k1_xboole_0 | sK1 = k1_xboole_0 ),
% 2.18/0.99      inference(global_propositional_subsumption,
% 2.18/0.99                [status(thm)],
% 2.18/0.99                [c_2334,c_32,c_85,c_1846]) ).
% 2.18/0.99  
% 2.18/0.99  cnf(c_2432,plain,
% 2.18/0.99      ( sK1 = k1_xboole_0 | sK0 != k1_xboole_0 ),
% 2.18/0.99      inference(renaming,[status(thm)],[c_2431]) ).
% 2.18/0.99  
% 2.18/0.99  cnf(c_3440,plain,
% 2.18/0.99      ( sK1 = k1_xboole_0 | k1_xboole_0 != k1_xboole_0 ),
% 2.18/0.99      inference(demodulation,[status(thm)],[c_3427,c_2432]) ).
% 2.18/0.99  
% 2.18/0.99  cnf(c_3495,plain,
% 2.18/0.99      ( sK1 = k1_xboole_0 ),
% 2.18/0.99      inference(equality_resolution_simp,[status(thm)],[c_3440]) ).
% 2.18/0.99  
% 2.18/0.99  cnf(c_3444,plain,
% 2.18/0.99      ( r2_relset_1(k1_xboole_0,k1_xboole_0,sK2,k2_funct_1(sK1)) != iProver_top ),
% 2.18/0.99      inference(demodulation,[status(thm)],[c_3427,c_1508]) ).
% 2.18/0.99  
% 2.18/0.99  cnf(c_3476,plain,
% 2.18/0.99      ( r2_relset_1(k1_xboole_0,k1_xboole_0,k1_xboole_0,k2_funct_1(sK1)) != iProver_top ),
% 2.18/0.99      inference(demodulation,[status(thm)],[c_3473,c_3444]) ).
% 2.18/0.99  
% 2.18/0.99  cnf(c_3497,plain,
% 2.18/0.99      ( r2_relset_1(k1_xboole_0,k1_xboole_0,k1_xboole_0,k2_funct_1(k1_xboole_0)) != iProver_top ),
% 2.18/0.99      inference(demodulation,[status(thm)],[c_3495,c_3476]) ).
% 2.18/0.99  
% 2.18/0.99  cnf(c_4,plain,
% 2.18/0.99      ( k6_partfun1(k1_xboole_0) = k1_xboole_0 ),
% 2.18/0.99      inference(cnf_transformation,[],[f72]) ).
% 2.18/0.99  
% 2.18/0.99  cnf(c_1081,plain,
% 2.18/0.99      ( k6_partfun1(k1_xboole_0) = k1_xboole_0 ),
% 2.18/0.99      inference(subtyping,[status(esa)],[c_4]) ).
% 2.18/0.99  
% 2.18/0.99  cnf(c_5,plain,
% 2.18/0.99      ( k2_funct_1(k6_partfun1(X0)) = k6_partfun1(X0) ),
% 2.18/0.99      inference(cnf_transformation,[],[f73]) ).
% 2.18/0.99  
% 2.18/0.99  cnf(c_1080,plain,
% 2.18/0.99      ( k2_funct_1(k6_partfun1(X0_50)) = k6_partfun1(X0_50) ),
% 2.18/0.99      inference(subtyping,[status(esa)],[c_5]) ).
% 2.18/0.99  
% 2.18/0.99  cnf(c_1814,plain,
% 2.18/0.99      ( k2_funct_1(k1_xboole_0) = k6_partfun1(k1_xboole_0) ),
% 2.18/0.99      inference(superposition,[status(thm)],[c_1081,c_1080]) ).
% 2.18/0.99  
% 2.18/0.99  cnf(c_1815,plain,
% 2.18/0.99      ( k2_funct_1(k1_xboole_0) = k1_xboole_0 ),
% 2.18/0.99      inference(light_normalisation,[status(thm)],[c_1814,c_1081]) ).
% 2.18/0.99  
% 2.18/0.99  cnf(c_3507,plain,
% 2.18/0.99      ( r2_relset_1(k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0) != iProver_top ),
% 2.18/0.99      inference(light_normalisation,[status(thm)],[c_3497,c_1815]) ).
% 2.18/0.99  
% 2.18/0.99  cnf(c_3511,plain,
% 2.18/0.99      ( $false ),
% 2.18/0.99      inference(forward_subsumption_resolution,[status(thm)],[c_3509,c_3507]) ).
% 2.18/0.99  
% 2.18/0.99  
% 2.18/0.99  % SZS output end CNFRefutation for theBenchmark.p
% 2.18/0.99  
% 2.18/0.99  ------                               Statistics
% 2.18/0.99  
% 2.18/0.99  ------ General
% 2.18/0.99  
% 2.18/0.99  abstr_ref_over_cycles:                  0
% 2.18/0.99  abstr_ref_under_cycles:                 0
% 2.18/0.99  gc_basic_clause_elim:                   0
% 2.18/0.99  forced_gc_time:                         0
% 2.18/0.99  parsing_time:                           0.009
% 2.18/0.99  unif_index_cands_time:                  0.
% 2.18/0.99  unif_index_add_time:                    0.
% 2.18/0.99  orderings_time:                         0.
% 2.18/0.99  out_proof_time:                         0.012
% 2.18/0.99  total_time:                             0.149
% 2.18/0.99  num_of_symbols:                         55
% 2.18/0.99  num_of_terms:                           4503
% 2.18/0.99  
% 2.18/0.99  ------ Preprocessing
% 2.18/0.99  
% 2.18/0.99  num_of_splits:                          0
% 2.18/0.99  num_of_split_atoms:                     0
% 2.18/0.99  num_of_reused_defs:                     0
% 2.18/0.99  num_eq_ax_congr_red:                    16
% 2.18/0.99  num_of_sem_filtered_clauses:            3
% 2.18/0.99  num_of_subtypes:                        2
% 2.18/0.99  monotx_restored_types:                  1
% 2.18/0.99  sat_num_of_epr_types:                   0
% 2.18/0.99  sat_num_of_non_cyclic_types:            0
% 2.18/0.99  sat_guarded_non_collapsed_types:        1
% 2.18/0.99  num_pure_diseq_elim:                    0
% 2.18/0.99  simp_replaced_by:                       0
% 2.18/0.99  res_preprocessed:                       128
% 2.18/0.99  prep_upred:                             0
% 2.18/0.99  prep_unflattend:                        62
% 2.18/0.99  smt_new_axioms:                         0
% 2.18/0.99  pred_elim_cands:                        5
% 2.18/0.99  pred_elim:                              3
% 2.18/0.99  pred_elim_cl:                           3
% 2.18/0.99  pred_elim_cycles:                       6
% 2.18/0.99  merged_defs:                            0
% 2.18/0.99  merged_defs_ncl:                        0
% 2.18/0.99  bin_hyper_res:                          0
% 2.18/0.99  prep_cycles:                            4
% 2.18/0.99  pred_elim_time:                         0.014
% 2.18/0.99  splitting_time:                         0.
% 2.18/0.99  sem_filter_time:                        0.
% 2.18/0.99  monotx_time:                            0.001
% 2.18/0.99  subtype_inf_time:                       0.002
% 2.18/0.99  
% 2.18/0.99  ------ Problem properties
% 2.18/0.99  
% 2.18/0.99  clauses:                                23
% 2.18/0.99  conjectures:                            8
% 2.18/0.99  epr:                                    4
% 2.18/0.99  horn:                                   22
% 2.18/0.99  ground:                                 13
% 2.18/0.99  unary:                                  13
% 2.18/0.99  binary:                                 4
% 2.18/0.99  lits:                                   54
% 2.18/0.99  lits_eq:                                17
% 2.18/0.99  fd_pure:                                0
% 2.18/0.99  fd_pseudo:                              0
% 2.18/0.99  fd_cond:                                2
% 2.18/0.99  fd_pseudo_cond:                         3
% 2.18/0.99  ac_symbols:                             0
% 2.18/0.99  
% 2.18/0.99  ------ Propositional Solver
% 2.18/0.99  
% 2.18/0.99  prop_solver_calls:                      27
% 2.18/0.99  prop_fast_solver_calls:                 971
% 2.18/0.99  smt_solver_calls:                       0
% 2.18/0.99  smt_fast_solver_calls:                  0
% 2.18/0.99  prop_num_of_clauses:                    1122
% 2.18/0.99  prop_preprocess_simplified:             4069
% 2.18/0.99  prop_fo_subsumed:                       29
% 2.18/0.99  prop_solver_time:                       0.
% 2.18/0.99  smt_solver_time:                        0.
% 2.18/0.99  smt_fast_solver_time:                   0.
% 2.18/0.99  prop_fast_solver_time:                  0.
% 2.18/0.99  prop_unsat_core_time:                   0.
% 2.18/0.99  
% 2.18/0.99  ------ QBF
% 2.18/0.99  
% 2.18/0.99  qbf_q_res:                              0
% 2.18/0.99  qbf_num_tautologies:                    0
% 2.18/0.99  qbf_prep_cycles:                        0
% 2.18/0.99  
% 2.18/0.99  ------ BMC1
% 2.18/0.99  
% 2.18/0.99  bmc1_current_bound:                     -1
% 2.18/0.99  bmc1_last_solved_bound:                 -1
% 2.18/0.99  bmc1_unsat_core_size:                   -1
% 2.18/0.99  bmc1_unsat_core_parents_size:           -1
% 2.18/0.99  bmc1_merge_next_fun:                    0
% 2.18/0.99  bmc1_unsat_core_clauses_time:           0.
% 2.18/0.99  
% 2.18/0.99  ------ Instantiation
% 2.18/0.99  
% 2.18/0.99  inst_num_of_clauses:                    321
% 2.18/0.99  inst_num_in_passive:                    46
% 2.18/0.99  inst_num_in_active:                     187
% 2.18/0.99  inst_num_in_unprocessed:                88
% 2.18/0.99  inst_num_of_loops:                      200
% 2.18/0.99  inst_num_of_learning_restarts:          0
% 2.18/0.99  inst_num_moves_active_passive:          10
% 2.18/0.99  inst_lit_activity:                      0
% 2.18/0.99  inst_lit_activity_moves:                0
% 2.18/0.99  inst_num_tautologies:                   0
% 2.18/0.99  inst_num_prop_implied:                  0
% 2.18/0.99  inst_num_existing_simplified:           0
% 2.18/0.99  inst_num_eq_res_simplified:             0
% 2.18/0.99  inst_num_child_elim:                    0
% 2.18/0.99  inst_num_of_dismatching_blockings:      66
% 2.18/0.99  inst_num_of_non_proper_insts:           277
% 2.18/0.99  inst_num_of_duplicates:                 0
% 2.18/0.99  inst_inst_num_from_inst_to_res:         0
% 2.18/0.99  inst_dismatching_checking_time:         0.
% 2.18/0.99  
% 2.18/0.99  ------ Resolution
% 2.18/0.99  
% 2.18/0.99  res_num_of_clauses:                     0
% 2.18/0.99  res_num_in_passive:                     0
% 2.18/0.99  res_num_in_active:                      0
% 2.18/0.99  res_num_of_loops:                       132
% 2.18/0.99  res_forward_subset_subsumed:            16
% 2.18/0.99  res_backward_subset_subsumed:           0
% 2.18/0.99  res_forward_subsumed:                   0
% 2.18/0.99  res_backward_subsumed:                  0
% 2.18/0.99  res_forward_subsumption_resolution:     1
% 2.18/0.99  res_backward_subsumption_resolution:    0
% 2.18/0.99  res_clause_to_clause_subsumption:       125
% 2.18/0.99  res_orphan_elimination:                 0
% 2.18/0.99  res_tautology_del:                      24
% 2.18/0.99  res_num_eq_res_simplified:              0
% 2.18/0.99  res_num_sel_changes:                    0
% 2.18/0.99  res_moves_from_active_to_pass:          0
% 2.18/0.99  
% 2.18/0.99  ------ Superposition
% 2.18/0.99  
% 2.18/0.99  sup_time_total:                         0.
% 2.18/0.99  sup_time_generating:                    0.
% 2.18/0.99  sup_time_sim_full:                      0.
% 2.18/0.99  sup_time_sim_immed:                     0.
% 2.18/0.99  
% 2.18/0.99  sup_num_of_clauses:                     18
% 2.18/0.99  sup_num_in_active:                      17
% 2.18/0.99  sup_num_in_passive:                     1
% 2.18/0.99  sup_num_of_loops:                       39
% 2.18/0.99  sup_fw_superposition:                   19
% 2.18/0.99  sup_bw_superposition:                   1
% 2.18/0.99  sup_immediate_simplified:               4
% 2.18/0.99  sup_given_eliminated:                   0
% 2.18/0.99  comparisons_done:                       0
% 2.18/0.99  comparisons_avoided:                    0
% 2.18/0.99  
% 2.18/0.99  ------ Simplifications
% 2.18/0.99  
% 2.18/0.99  
% 2.18/0.99  sim_fw_subset_subsumed:                 1
% 2.18/0.99  sim_bw_subset_subsumed:                 0
% 2.18/0.99  sim_fw_subsumed:                        0
% 2.18/0.99  sim_bw_subsumed:                        0
% 2.18/0.99  sim_fw_subsumption_res:                 1
% 2.18/0.99  sim_bw_subsumption_res:                 0
% 2.18/0.99  sim_tautology_del:                      0
% 2.18/0.99  sim_eq_tautology_del:                   2
% 2.18/0.99  sim_eq_res_simp:                        2
% 2.18/0.99  sim_fw_demodulated:                     0
% 2.18/0.99  sim_bw_demodulated:                     34
% 2.18/0.99  sim_light_normalised:                   8
% 2.18/0.99  sim_joinable_taut:                      0
% 2.18/0.99  sim_joinable_simp:                      0
% 2.18/0.99  sim_ac_normalised:                      0
% 2.18/0.99  sim_smt_subsumption:                    0
% 2.18/0.99  
%------------------------------------------------------------------------------
