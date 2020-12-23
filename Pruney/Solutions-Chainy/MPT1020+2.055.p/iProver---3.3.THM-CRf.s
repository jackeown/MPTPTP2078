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

% Result     : Theorem 3.47s
% Output     : CNFRefutation 3.47s
% Verified   : 
% Statistics : Number of formulae       :  206 (4068 expanded)
%              Number of clauses        :  143 (1357 expanded)
%              Number of leaves         :   14 ( 929 expanded)
%              Depth                    :   28
%              Number of atoms          :  746 (27794 expanded)
%              Number of equality atoms :  317 (2637 expanded)
%              Maximal formula depth    :   17 (   5 average)
%              Maximal clause size      :   20 (   3 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f12,conjecture,(
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f13,negated_conjecture,(
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
    inference(negated_conjecture,[],[f12])).

fof(f32,plain,(
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
    inference(ennf_transformation,[],[f13])).

fof(f33,plain,(
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
    inference(flattening,[],[f32])).

fof(f37,plain,(
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

fof(f36,plain,
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

fof(f38,plain,
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
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f33,f37,f36])).

fof(f66,plain,(
    r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK0,sK0,sK0,sK1,sK2),k6_partfun1(sK0)) ),
    inference(cnf_transformation,[],[f38])).

fof(f61,plain,(
    m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) ),
    inference(cnf_transformation,[],[f38])).

fof(f5,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k2_relat_1(X2) = k2_relset_1(X0,X1,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f19,plain,(
    ! [X0,X1,X2] :
      ( k2_relat_1(X2) = k2_relset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f44,plain,(
    ! [X2,X0,X1] :
      ( k2_relat_1(X2) = k2_relset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f11,axiom,(
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f30,plain,(
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
    inference(ennf_transformation,[],[f11])).

fof(f31,plain,(
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
    inference(flattening,[],[f30])).

fof(f57,plain,(
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
    inference(cnf_transformation,[],[f31])).

fof(f58,plain,(
    v1_funct_1(sK1) ),
    inference(cnf_transformation,[],[f38])).

fof(f59,plain,(
    v1_funct_2(sK1,sK0,sK0) ),
    inference(cnf_transformation,[],[f38])).

fof(f60,plain,(
    v3_funct_2(sK1,sK0,sK0) ),
    inference(cnf_transformation,[],[f38])).

fof(f7,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => ( ( v3_funct_2(X2,X0,X1)
          & v1_funct_1(X2) )
       => ( v2_funct_2(X2,X1)
          & v2_funct_1(X2)
          & v1_funct_1(X2) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f22,plain,(
    ! [X0,X1,X2] :
      ( ( v2_funct_2(X2,X1)
        & v2_funct_1(X2)
        & v1_funct_1(X2) )
      | ~ v3_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f23,plain,(
    ! [X0,X1,X2] :
      ( ( v2_funct_2(X2,X1)
        & v2_funct_1(X2)
        & v1_funct_1(X2) )
      | ~ v3_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(flattening,[],[f22])).

fof(f48,plain,(
    ! [X2,X0,X1] :
      ( v2_funct_1(X2)
      | ~ v3_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f49,plain,(
    ! [X2,X0,X1] :
      ( v2_funct_2(X2,X1)
      | ~ v3_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f8,axiom,(
    ! [X0,X1] :
      ( ( v5_relat_1(X1,X0)
        & v1_relat_1(X1) )
     => ( v2_funct_2(X1,X0)
      <=> k2_relat_1(X1) = X0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f24,plain,(
    ! [X0,X1] :
      ( ( v2_funct_2(X1,X0)
      <=> k2_relat_1(X1) = X0 )
      | ~ v5_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f25,plain,(
    ! [X0,X1] :
      ( ( v2_funct_2(X1,X0)
      <=> k2_relat_1(X1) = X0 )
      | ~ v5_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f24])).

fof(f35,plain,(
    ! [X0,X1] :
      ( ( ( v2_funct_2(X1,X0)
          | k2_relat_1(X1) != X0 )
        & ( k2_relat_1(X1) = X0
          | ~ v2_funct_2(X1,X0) ) )
      | ~ v5_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(nnf_transformation,[],[f25])).

fof(f50,plain,(
    ! [X0,X1] :
      ( k2_relat_1(X1) = X0
      | ~ v2_funct_2(X1,X0)
      | ~ v5_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f35])).

fof(f4,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => ( v5_relat_1(X2,X1)
        & v4_relat_1(X2,X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f14,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => v5_relat_1(X2,X1) ) ),
    inference(pure_predicate_removal,[],[f4])).

fof(f18,plain,(
    ! [X0,X1,X2] :
      ( v5_relat_1(X2,X1)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f43,plain,(
    ! [X2,X0,X1] :
      ( v5_relat_1(X2,X1)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f2,axiom,(
    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f40,plain,(
    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1)) ),
    inference(cnf_transformation,[],[f2])).

fof(f1,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(X0))
         => v1_relat_1(X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f15,plain,(
    ! [X0] :
      ( ! [X1] :
          ( v1_relat_1(X1)
          | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f39,plain,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f15])).

fof(f62,plain,(
    v1_funct_1(sK2) ),
    inference(cnf_transformation,[],[f38])).

fof(f63,plain,(
    v1_funct_2(sK2,sK0,sK0) ),
    inference(cnf_transformation,[],[f38])).

fof(f65,plain,(
    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) ),
    inference(cnf_transformation,[],[f38])).

fof(f10,axiom,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
        & v3_funct_2(X1,X0,X0)
        & v1_funct_2(X1,X0,X0)
        & v1_funct_1(X1) )
     => k2_funct_2(X0,X1) = k2_funct_1(X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f28,plain,(
    ! [X0,X1] :
      ( k2_funct_2(X0,X1) = k2_funct_1(X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
      | ~ v3_funct_2(X1,X0,X0)
      | ~ v1_funct_2(X1,X0,X0)
      | ~ v1_funct_1(X1) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f29,plain,(
    ! [X0,X1] :
      ( k2_funct_2(X0,X1) = k2_funct_1(X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
      | ~ v3_funct_2(X1,X0,X0)
      | ~ v1_funct_2(X1,X0,X0)
      | ~ v1_funct_1(X1) ) ),
    inference(flattening,[],[f28])).

fof(f56,plain,(
    ! [X0,X1] :
      ( k2_funct_2(X0,X1) = k2_funct_1(X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
      | ~ v3_funct_2(X1,X0,X0)
      | ~ v1_funct_2(X1,X0,X0)
      | ~ v1_funct_1(X1) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f67,plain,(
    ~ r2_relset_1(sK0,sK0,sK2,k2_funct_2(sK0,sK1)) ),
    inference(cnf_transformation,[],[f38])).

fof(f6,axiom,(
    ! [X0,X1,X2,X3] :
      ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) )
     => ( r2_relset_1(X0,X1,X2,X3)
      <=> X2 = X3 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f20,plain,(
    ! [X0,X1,X2,X3] :
      ( ( r2_relset_1(X0,X1,X2,X3)
      <=> X2 = X3 )
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f21,plain,(
    ! [X0,X1,X2,X3] :
      ( ( r2_relset_1(X0,X1,X2,X3)
      <=> X2 = X3 )
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(flattening,[],[f20])).

fof(f34,plain,(
    ! [X0,X1,X2,X3] :
      ( ( ( r2_relset_1(X0,X1,X2,X3)
          | X2 != X3 )
        & ( X2 = X3
          | ~ r2_relset_1(X0,X1,X2,X3) ) )
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(nnf_transformation,[],[f21])).

fof(f46,plain,(
    ! [X2,X0,X3,X1] :
      ( r2_relset_1(X0,X1,X2,X3)
      | X2 != X3
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f34])).

fof(f68,plain,(
    ! [X0,X3,X1] :
      ( r2_relset_1(X0,X1,X3,X3)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(equality_resolution,[],[f46])).

fof(f64,plain,(
    v3_funct_2(sK2,sK0,sK0) ),
    inference(cnf_transformation,[],[f38])).

fof(f3,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ( ( k1_xboole_0 = k2_relat_1(X0)
          | k1_relat_1(X0) = k1_xboole_0 )
       => k1_xboole_0 = X0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f16,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | ( k1_xboole_0 != k2_relat_1(X0)
        & k1_relat_1(X0) != k1_xboole_0 )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f17,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | ( k1_xboole_0 != k2_relat_1(X0)
        & k1_relat_1(X0) != k1_xboole_0 )
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f16])).

fof(f42,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | k1_xboole_0 != k2_relat_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f17])).

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

fof(f26,plain,(
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

fof(f27,plain,(
    ! [X0,X1] :
      ( ( m1_subset_1(k2_funct_2(X0,X1),k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
        & v3_funct_2(k2_funct_2(X0,X1),X0,X0)
        & v1_funct_2(k2_funct_2(X0,X1),X0,X0)
        & v1_funct_1(k2_funct_2(X0,X1)) )
      | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
      | ~ v3_funct_2(X1,X0,X0)
      | ~ v1_funct_2(X1,X0,X0)
      | ~ v1_funct_1(X1) ) ),
    inference(flattening,[],[f26])).

fof(f55,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k2_funct_2(X0,X1),k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
      | ~ v3_funct_2(X1,X0,X0)
      | ~ v1_funct_2(X1,X0,X0)
      | ~ v1_funct_1(X1) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f52,plain,(
    ! [X0,X1] :
      ( v1_funct_1(k2_funct_2(X0,X1))
      | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
      | ~ v3_funct_2(X1,X0,X0)
      | ~ v1_funct_2(X1,X0,X0)
      | ~ v1_funct_1(X1) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f54,plain,(
    ! [X0,X1] :
      ( v3_funct_2(k2_funct_2(X0,X1),X0,X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
      | ~ v3_funct_2(X1,X0,X0)
      | ~ v1_funct_2(X1,X0,X0)
      | ~ v1_funct_1(X1) ) ),
    inference(cnf_transformation,[],[f27])).

cnf(c_20,negated_conjecture,
    ( r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK0,sK0,sK0,sK1,sK2),k6_partfun1(sK0)) ),
    inference(cnf_transformation,[],[f66])).

cnf(c_907,negated_conjecture,
    ( r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK0,sK0,sK0,sK1,sK2),k6_partfun1(sK0)) ),
    inference(subtyping,[status(esa)],[c_20])).

cnf(c_1411,plain,
    ( r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK0,sK0,sK0,sK1,sK2),k6_partfun1(sK0)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_907])).

cnf(c_25,negated_conjecture,
    ( m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) ),
    inference(cnf_transformation,[],[f61])).

cnf(c_902,negated_conjecture,
    ( m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) ),
    inference(subtyping,[status(esa)],[c_25])).

cnf(c_1416,plain,
    ( m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_902])).

cnf(c_5,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k2_relset_1(X1,X2,X0) = k2_relat_1(X0) ),
    inference(cnf_transformation,[],[f44])).

cnf(c_918,plain,
    ( ~ m1_subset_1(X0_50,k1_zfmisc_1(k2_zfmisc_1(X1_50,X2_50)))
    | k2_relset_1(X1_50,X2_50,X0_50) = k2_relat_1(X0_50) ),
    inference(subtyping,[status(esa)],[c_5])).

cnf(c_1400,plain,
    ( k2_relset_1(X0_50,X1_50,X2_50) = k2_relat_1(X2_50)
    | m1_subset_1(X2_50,k1_zfmisc_1(k2_zfmisc_1(X0_50,X1_50))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_918])).

cnf(c_2404,plain,
    ( k2_relset_1(sK0,sK0,sK1) = k2_relat_1(sK1) ),
    inference(superposition,[status(thm)],[c_1416,c_1400])).

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
    inference(cnf_transformation,[],[f57])).

cnf(c_909,plain,
    ( ~ r2_relset_1(X0_50,X0_50,k1_partfun1(X0_50,X1_50,X1_50,X0_50,X2_50,X3_50),k6_partfun1(X0_50))
    | ~ v1_funct_2(X3_50,X1_50,X0_50)
    | ~ v1_funct_2(X2_50,X0_50,X1_50)
    | ~ m1_subset_1(X2_50,k1_zfmisc_1(k2_zfmisc_1(X0_50,X1_50)))
    | ~ m1_subset_1(X3_50,k1_zfmisc_1(k2_zfmisc_1(X1_50,X0_50)))
    | ~ v2_funct_1(X2_50)
    | ~ v1_funct_1(X2_50)
    | ~ v1_funct_1(X3_50)
    | k2_relset_1(X0_50,X1_50,X2_50) != X1_50
    | k2_funct_1(X2_50) = X3_50
    | k1_xboole_0 = X0_50
    | k1_xboole_0 = X1_50 ),
    inference(subtyping,[status(esa)],[c_18])).

cnf(c_1409,plain,
    ( k2_relset_1(X0_50,X1_50,X2_50) != X1_50
    | k2_funct_1(X2_50) = X3_50
    | k1_xboole_0 = X0_50
    | k1_xboole_0 = X1_50
    | r2_relset_1(X0_50,X0_50,k1_partfun1(X0_50,X1_50,X1_50,X0_50,X2_50,X3_50),k6_partfun1(X0_50)) != iProver_top
    | v1_funct_2(X3_50,X1_50,X0_50) != iProver_top
    | v1_funct_2(X2_50,X0_50,X1_50) != iProver_top
    | m1_subset_1(X2_50,k1_zfmisc_1(k2_zfmisc_1(X0_50,X1_50))) != iProver_top
    | m1_subset_1(X3_50,k1_zfmisc_1(k2_zfmisc_1(X1_50,X0_50))) != iProver_top
    | v2_funct_1(X2_50) != iProver_top
    | v1_funct_1(X2_50) != iProver_top
    | v1_funct_1(X3_50) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_909])).

cnf(c_3950,plain,
    ( k2_funct_1(sK1) = X0_50
    | k2_relat_1(sK1) != sK0
    | sK0 = k1_xboole_0
    | r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK0,sK0,sK0,sK1,X0_50),k6_partfun1(sK0)) != iProver_top
    | v1_funct_2(X0_50,sK0,sK0) != iProver_top
    | v1_funct_2(sK1,sK0,sK0) != iProver_top
    | m1_subset_1(X0_50,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) != iProver_top
    | m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) != iProver_top
    | v2_funct_1(sK1) != iProver_top
    | v1_funct_1(X0_50) != iProver_top
    | v1_funct_1(sK1) != iProver_top ),
    inference(superposition,[status(thm)],[c_2404,c_1409])).

cnf(c_28,negated_conjecture,
    ( v1_funct_1(sK1) ),
    inference(cnf_transformation,[],[f58])).

cnf(c_29,plain,
    ( v1_funct_1(sK1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_28])).

cnf(c_27,negated_conjecture,
    ( v1_funct_2(sK1,sK0,sK0) ),
    inference(cnf_transformation,[],[f59])).

cnf(c_30,plain,
    ( v1_funct_2(sK1,sK0,sK0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_27])).

cnf(c_26,negated_conjecture,
    ( v3_funct_2(sK1,sK0,sK0) ),
    inference(cnf_transformation,[],[f60])).

cnf(c_31,plain,
    ( v3_funct_2(sK1,sK0,sK0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_26])).

cnf(c_32,plain,
    ( m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_25])).

cnf(c_9,plain,
    ( ~ v3_funct_2(X0,X1,X2)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | v2_funct_1(X0)
    | ~ v1_funct_1(X0) ),
    inference(cnf_transformation,[],[f48])).

cnf(c_915,plain,
    ( ~ v3_funct_2(X0_50,X1_50,X2_50)
    | ~ m1_subset_1(X0_50,k1_zfmisc_1(k2_zfmisc_1(X1_50,X2_50)))
    | v2_funct_1(X0_50)
    | ~ v1_funct_1(X0_50) ),
    inference(subtyping,[status(esa)],[c_9])).

cnf(c_1661,plain,
    ( ~ v3_funct_2(sK1,X0_50,X1_50)
    | ~ m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(X0_50,X1_50)))
    | v2_funct_1(sK1)
    | ~ v1_funct_1(sK1) ),
    inference(instantiation,[status(thm)],[c_915])).

cnf(c_1662,plain,
    ( v3_funct_2(sK1,X0_50,X1_50) != iProver_top
    | m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(X0_50,X1_50))) != iProver_top
    | v2_funct_1(sK1) = iProver_top
    | v1_funct_1(sK1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1661])).

cnf(c_1664,plain,
    ( v3_funct_2(sK1,sK0,sK0) != iProver_top
    | m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) != iProver_top
    | v2_funct_1(sK1) = iProver_top
    | v1_funct_1(sK1) != iProver_top ),
    inference(instantiation,[status(thm)],[c_1662])).

cnf(c_8,plain,
    ( ~ v3_funct_2(X0,X1,X2)
    | v2_funct_2(X0,X2)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ v1_funct_1(X0) ),
    inference(cnf_transformation,[],[f49])).

cnf(c_12,plain,
    ( ~ v2_funct_2(X0,X1)
    | ~ v5_relat_1(X0,X1)
    | ~ v1_relat_1(X0)
    | k2_relat_1(X0) = X1 ),
    inference(cnf_transformation,[],[f50])).

cnf(c_348,plain,
    ( ~ v3_funct_2(X0,X1,X2)
    | ~ v5_relat_1(X3,X4)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ v1_funct_1(X0)
    | ~ v1_relat_1(X3)
    | X3 != X0
    | X4 != X2
    | k2_relat_1(X3) = X4 ),
    inference(resolution_lifted,[status(thm)],[c_8,c_12])).

cnf(c_349,plain,
    ( ~ v3_funct_2(X0,X1,X2)
    | ~ v5_relat_1(X0,X2)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ v1_funct_1(X0)
    | ~ v1_relat_1(X0)
    | k2_relat_1(X0) = X2 ),
    inference(unflattening,[status(thm)],[c_348])).

cnf(c_4,plain,
    ( v5_relat_1(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) ),
    inference(cnf_transformation,[],[f43])).

cnf(c_365,plain,
    ( ~ v3_funct_2(X0,X1,X2)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ v1_funct_1(X0)
    | ~ v1_relat_1(X0)
    | k2_relat_1(X0) = X2 ),
    inference(forward_subsumption_resolution,[status(thm)],[c_349,c_4])).

cnf(c_898,plain,
    ( ~ v3_funct_2(X0_50,X1_50,X2_50)
    | ~ m1_subset_1(X0_50,k1_zfmisc_1(k2_zfmisc_1(X1_50,X2_50)))
    | ~ v1_funct_1(X0_50)
    | ~ v1_relat_1(X0_50)
    | k2_relat_1(X0_50) = X2_50 ),
    inference(subtyping,[status(esa)],[c_365])).

cnf(c_1420,plain,
    ( k2_relat_1(X0_50) = X1_50
    | v3_funct_2(X0_50,X2_50,X1_50) != iProver_top
    | m1_subset_1(X0_50,k1_zfmisc_1(k2_zfmisc_1(X2_50,X1_50))) != iProver_top
    | v1_funct_1(X0_50) != iProver_top
    | v1_relat_1(X0_50) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_898])).

cnf(c_4345,plain,
    ( k2_relat_1(sK1) = sK0
    | v3_funct_2(sK1,sK0,sK0) != iProver_top
    | v1_funct_1(sK1) != iProver_top
    | v1_relat_1(sK1) != iProver_top ),
    inference(superposition,[status(thm)],[c_1416,c_1420])).

cnf(c_1,plain,
    ( v1_relat_1(k2_zfmisc_1(X0,X1)) ),
    inference(cnf_transformation,[],[f40])).

cnf(c_88,plain,
    ( v1_relat_1(k2_zfmisc_1(X0,X1)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1])).

cnf(c_90,plain,
    ( v1_relat_1(k2_zfmisc_1(sK0,sK0)) = iProver_top ),
    inference(instantiation,[status(thm)],[c_88])).

cnf(c_1685,plain,
    ( ~ v3_funct_2(sK1,X0_50,X1_50)
    | ~ m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(X0_50,X1_50)))
    | ~ v1_funct_1(sK1)
    | ~ v1_relat_1(sK1)
    | k2_relat_1(sK1) = X1_50 ),
    inference(instantiation,[status(thm)],[c_898])).

cnf(c_1686,plain,
    ( k2_relat_1(sK1) = X0_50
    | v3_funct_2(sK1,X1_50,X0_50) != iProver_top
    | m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(X1_50,X0_50))) != iProver_top
    | v1_funct_1(sK1) != iProver_top
    | v1_relat_1(sK1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1685])).

cnf(c_1688,plain,
    ( k2_relat_1(sK1) = sK0
    | v3_funct_2(sK1,sK0,sK0) != iProver_top
    | m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) != iProver_top
    | v1_funct_1(sK1) != iProver_top
    | v1_relat_1(sK1) != iProver_top ),
    inference(instantiation,[status(thm)],[c_1686])).

cnf(c_0,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | ~ v1_relat_1(X1)
    | v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f39])).

cnf(c_922,plain,
    ( ~ m1_subset_1(X0_50,k1_zfmisc_1(X1_50))
    | ~ v1_relat_1(X1_50)
    | v1_relat_1(X0_50) ),
    inference(subtyping,[status(esa)],[c_0])).

cnf(c_1396,plain,
    ( m1_subset_1(X0_50,k1_zfmisc_1(X1_50)) != iProver_top
    | v1_relat_1(X1_50) != iProver_top
    | v1_relat_1(X0_50) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_922])).

cnf(c_1852,plain,
    ( v1_relat_1(k2_zfmisc_1(sK0,sK0)) != iProver_top
    | v1_relat_1(sK1) = iProver_top ),
    inference(superposition,[status(thm)],[c_1416,c_1396])).

cnf(c_4556,plain,
    ( k2_relat_1(sK1) = sK0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_4345,c_29,c_31,c_32,c_90,c_1688,c_1852])).

cnf(c_4559,plain,
    ( k2_relset_1(sK0,sK0,sK1) = sK0 ),
    inference(demodulation,[status(thm)],[c_4556,c_2404])).

cnf(c_4642,plain,
    ( k2_funct_1(sK1) = X0_50
    | sK0 = k1_xboole_0
    | r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK0,sK0,sK0,sK1,X0_50),k6_partfun1(sK0)) != iProver_top
    | v1_funct_2(X0_50,sK0,sK0) != iProver_top
    | v1_funct_2(sK1,sK0,sK0) != iProver_top
    | m1_subset_1(X0_50,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) != iProver_top
    | m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) != iProver_top
    | v2_funct_1(sK1) != iProver_top
    | v1_funct_1(X0_50) != iProver_top
    | v1_funct_1(sK1) != iProver_top ),
    inference(superposition,[status(thm)],[c_4559,c_1409])).

cnf(c_6575,plain,
    ( v1_funct_1(X0_50) != iProver_top
    | m1_subset_1(X0_50,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) != iProver_top
    | k2_funct_1(sK1) = X0_50
    | sK0 = k1_xboole_0
    | r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK0,sK0,sK0,sK1,X0_50),k6_partfun1(sK0)) != iProver_top
    | v1_funct_2(X0_50,sK0,sK0) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_3950,c_29,c_30,c_31,c_32,c_1664,c_4642])).

cnf(c_6576,plain,
    ( k2_funct_1(sK1) = X0_50
    | sK0 = k1_xboole_0
    | r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK0,sK0,sK0,sK1,X0_50),k6_partfun1(sK0)) != iProver_top
    | v1_funct_2(X0_50,sK0,sK0) != iProver_top
    | m1_subset_1(X0_50,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) != iProver_top
    | v1_funct_1(X0_50) != iProver_top ),
    inference(renaming,[status(thm)],[c_6575])).

cnf(c_6587,plain,
    ( k2_funct_1(sK1) = sK2
    | sK0 = k1_xboole_0
    | v1_funct_2(sK2,sK0,sK0) != iProver_top
    | m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) != iProver_top
    | v1_funct_1(sK2) != iProver_top ),
    inference(superposition,[status(thm)],[c_1411,c_6576])).

cnf(c_24,negated_conjecture,
    ( v1_funct_1(sK2) ),
    inference(cnf_transformation,[],[f62])).

cnf(c_23,negated_conjecture,
    ( v1_funct_2(sK2,sK0,sK0) ),
    inference(cnf_transformation,[],[f63])).

cnf(c_21,negated_conjecture,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) ),
    inference(cnf_transformation,[],[f65])).

cnf(c_6588,plain,
    ( ~ v1_funct_2(sK2,sK0,sK0)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
    | ~ v1_funct_1(sK2)
    | k2_funct_1(sK1) = sK2
    | sK0 = k1_xboole_0 ),
    inference(predicate_to_equality_rev,[status(thm)],[c_6587])).

cnf(c_6623,plain,
    ( sK0 = k1_xboole_0
    | k2_funct_1(sK1) = sK2 ),
    inference(global_propositional_subsumption,[status(thm)],[c_6587,c_33,c_34,c_36])).

cnf(c_6624,plain,
    ( k2_funct_1(sK1) = sK2
    | sK0 = k1_xboole_0 ),
    inference(renaming,[status(thm)],[c_6623])).

cnf(c_17,plain,
    ( ~ v1_funct_2(X0,X1,X1)
    | ~ v3_funct_2(X0,X1,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X1)))
    | ~ v1_funct_1(X0)
    | k2_funct_2(X1,X0) = k2_funct_1(X0) ),
    inference(cnf_transformation,[],[f56])).

cnf(c_910,plain,
    ( ~ v1_funct_2(X0_50,X1_50,X1_50)
    | ~ v3_funct_2(X0_50,X1_50,X1_50)
    | ~ m1_subset_1(X0_50,k1_zfmisc_1(k2_zfmisc_1(X1_50,X1_50)))
    | ~ v1_funct_1(X0_50)
    | k2_funct_2(X1_50,X0_50) = k2_funct_1(X0_50) ),
    inference(subtyping,[status(esa)],[c_17])).

cnf(c_1408,plain,
    ( k2_funct_2(X0_50,X1_50) = k2_funct_1(X1_50)
    | v1_funct_2(X1_50,X0_50,X0_50) != iProver_top
    | v3_funct_2(X1_50,X0_50,X0_50) != iProver_top
    | m1_subset_1(X1_50,k1_zfmisc_1(k2_zfmisc_1(X0_50,X0_50))) != iProver_top
    | v1_funct_1(X1_50) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_910])).

cnf(c_2795,plain,
    ( k2_funct_2(sK0,sK1) = k2_funct_1(sK1)
    | v1_funct_2(sK1,sK0,sK0) != iProver_top
    | v3_funct_2(sK1,sK0,sK0) != iProver_top
    | v1_funct_1(sK1) != iProver_top ),
    inference(superposition,[status(thm)],[c_1416,c_1408])).

cnf(c_1725,plain,
    ( ~ v1_funct_2(sK1,X0_50,X0_50)
    | ~ v3_funct_2(sK1,X0_50,X0_50)
    | ~ m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(X0_50,X0_50)))
    | ~ v1_funct_1(sK1)
    | k2_funct_2(X0_50,sK1) = k2_funct_1(sK1) ),
    inference(instantiation,[status(thm)],[c_910])).

cnf(c_1727,plain,
    ( ~ v1_funct_2(sK1,sK0,sK0)
    | ~ v3_funct_2(sK1,sK0,sK0)
    | ~ m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
    | ~ v1_funct_1(sK1)
    | k2_funct_2(sK0,sK1) = k2_funct_1(sK1) ),
    inference(instantiation,[status(thm)],[c_1725])).

cnf(c_4059,plain,
    ( k2_funct_2(sK0,sK1) = k2_funct_1(sK1) ),
    inference(global_propositional_subsumption,[status(thm)],[c_2795,c_28,c_27,c_26,c_25,c_1727])).

cnf(c_19,negated_conjecture,
    ( ~ r2_relset_1(sK0,sK0,sK2,k2_funct_2(sK0,sK1)) ),
    inference(cnf_transformation,[],[f67])).

cnf(c_908,negated_conjecture,
    ( ~ r2_relset_1(sK0,sK0,sK2,k2_funct_2(sK0,sK1)) ),
    inference(subtyping,[status(esa)],[c_19])).

cnf(c_1410,plain,
    ( r2_relset_1(sK0,sK0,sK2,k2_funct_2(sK0,sK1)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_908])).

cnf(c_4063,plain,
    ( r2_relset_1(sK0,sK0,sK2,k2_funct_1(sK1)) != iProver_top ),
    inference(demodulation,[status(thm)],[c_4059,c_1410])).

cnf(c_6636,plain,
    ( sK0 = k1_xboole_0
    | r2_relset_1(sK0,sK0,sK2,sK2) != iProver_top ),
    inference(superposition,[status(thm)],[c_6624,c_4063])).

cnf(c_36,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_21])).

cnf(c_6,plain,
    ( r2_relset_1(X0,X1,X2,X2)
    | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ),
    inference(cnf_transformation,[],[f68])).

cnf(c_917,plain,
    ( r2_relset_1(X0_50,X1_50,X2_50,X2_50)
    | ~ m1_subset_1(X2_50,k1_zfmisc_1(k2_zfmisc_1(X0_50,X1_50))) ),
    inference(subtyping,[status(esa)],[c_6])).

cnf(c_1644,plain,
    ( r2_relset_1(sK0,sK0,sK2,sK2)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) ),
    inference(instantiation,[status(thm)],[c_917])).

cnf(c_1645,plain,
    ( r2_relset_1(sK0,sK0,sK2,sK2) = iProver_top
    | m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1644])).

cnf(c_6655,plain,
    ( sK0 = k1_xboole_0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_6636,c_36,c_1645])).

cnf(c_906,negated_conjecture,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) ),
    inference(subtyping,[status(esa)],[c_21])).

cnf(c_1412,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_906])).

cnf(c_4344,plain,
    ( k2_relat_1(sK2) = sK0
    | v3_funct_2(sK2,sK0,sK0) != iProver_top
    | v1_funct_1(sK2) != iProver_top
    | v1_relat_1(sK2) != iProver_top ),
    inference(superposition,[status(thm)],[c_1412,c_1420])).

cnf(c_33,plain,
    ( v1_funct_1(sK2) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_24])).

cnf(c_22,negated_conjecture,
    ( v3_funct_2(sK2,sK0,sK0) ),
    inference(cnf_transformation,[],[f64])).

cnf(c_35,plain,
    ( v3_funct_2(sK2,sK0,sK0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_22])).

cnf(c_1680,plain,
    ( ~ v3_funct_2(sK2,X0_50,X1_50)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X0_50,X1_50)))
    | ~ v1_funct_1(sK2)
    | ~ v1_relat_1(sK2)
    | k2_relat_1(sK2) = X1_50 ),
    inference(instantiation,[status(thm)],[c_898])).

cnf(c_1681,plain,
    ( k2_relat_1(sK2) = X0_50
    | v3_funct_2(sK2,X1_50,X0_50) != iProver_top
    | m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X1_50,X0_50))) != iProver_top
    | v1_funct_1(sK2) != iProver_top
    | v1_relat_1(sK2) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1680])).

cnf(c_1683,plain,
    ( k2_relat_1(sK2) = sK0
    | v3_funct_2(sK2,sK0,sK0) != iProver_top
    | m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) != iProver_top
    | v1_funct_1(sK2) != iProver_top
    | v1_relat_1(sK2) != iProver_top ),
    inference(instantiation,[status(thm)],[c_1681])).

cnf(c_1851,plain,
    ( v1_relat_1(k2_zfmisc_1(sK0,sK0)) != iProver_top
    | v1_relat_1(sK2) = iProver_top ),
    inference(superposition,[status(thm)],[c_1412,c_1396])).

cnf(c_4488,plain,
    ( k2_relat_1(sK2) = sK0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_4344,c_33,c_35,c_36,c_90,c_1683,c_1851])).

cnf(c_2,plain,
    ( ~ v1_relat_1(X0)
    | k2_relat_1(X0) != k1_xboole_0
    | k1_xboole_0 = X0 ),
    inference(cnf_transformation,[],[f42])).

cnf(c_920,plain,
    ( ~ v1_relat_1(X0_50)
    | k2_relat_1(X0_50) != k1_xboole_0
    | k1_xboole_0 = X0_50 ),
    inference(subtyping,[status(esa)],[c_2])).

cnf(c_1398,plain,
    ( k2_relat_1(X0_50) != k1_xboole_0
    | k1_xboole_0 = X0_50
    | v1_relat_1(X0_50) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_920])).

cnf(c_4492,plain,
    ( sK2 = k1_xboole_0
    | sK0 != k1_xboole_0
    | v1_relat_1(sK2) != iProver_top ),
    inference(superposition,[status(thm)],[c_4488,c_1398])).

cnf(c_4495,plain,
    ( sK0 != k1_xboole_0
    | sK2 = k1_xboole_0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_4492,c_90,c_1851])).

cnf(c_4496,plain,
    ( sK2 = k1_xboole_0
    | sK0 != k1_xboole_0 ),
    inference(renaming,[status(thm)],[c_4495])).

cnf(c_6675,plain,
    ( sK2 = k1_xboole_0
    | k1_xboole_0 != k1_xboole_0 ),
    inference(demodulation,[status(thm)],[c_6655,c_4496])).

cnf(c_6751,plain,
    ( sK2 = k1_xboole_0 ),
    inference(equality_resolution_simp,[status(thm)],[c_6675])).

cnf(c_2794,plain,
    ( k2_funct_2(sK0,sK2) = k2_funct_1(sK2)
    | v1_funct_2(sK2,sK0,sK0) != iProver_top
    | v3_funct_2(sK2,sK0,sK0) != iProver_top
    | v1_funct_1(sK2) != iProver_top ),
    inference(superposition,[status(thm)],[c_1412,c_1408])).

cnf(c_1720,plain,
    ( ~ v1_funct_2(sK2,X0_50,X0_50)
    | ~ v3_funct_2(sK2,X0_50,X0_50)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X0_50,X0_50)))
    | ~ v1_funct_1(sK2)
    | k2_funct_2(X0_50,sK2) = k2_funct_1(sK2) ),
    inference(instantiation,[status(thm)],[c_910])).

cnf(c_1722,plain,
    ( ~ v1_funct_2(sK2,sK0,sK0)
    | ~ v3_funct_2(sK2,sK0,sK0)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
    | ~ v1_funct_1(sK2)
    | k2_funct_2(sK0,sK2) = k2_funct_1(sK2) ),
    inference(instantiation,[status(thm)],[c_1720])).

cnf(c_4051,plain,
    ( k2_funct_2(sK0,sK2) = k2_funct_1(sK2) ),
    inference(global_propositional_subsumption,[status(thm)],[c_2794,c_24,c_23,c_22,c_21,c_1722])).

cnf(c_13,plain,
    ( ~ v1_funct_2(X0,X1,X1)
    | ~ v3_funct_2(X0,X1,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X1)))
    | m1_subset_1(k2_funct_2(X1,X0),k1_zfmisc_1(k2_zfmisc_1(X1,X1)))
    | ~ v1_funct_1(X0) ),
    inference(cnf_transformation,[],[f55])).

cnf(c_914,plain,
    ( ~ v1_funct_2(X0_50,X1_50,X1_50)
    | ~ v3_funct_2(X0_50,X1_50,X1_50)
    | ~ m1_subset_1(X0_50,k1_zfmisc_1(k2_zfmisc_1(X1_50,X1_50)))
    | m1_subset_1(k2_funct_2(X1_50,X0_50),k1_zfmisc_1(k2_zfmisc_1(X1_50,X1_50)))
    | ~ v1_funct_1(X0_50) ),
    inference(subtyping,[status(esa)],[c_13])).

cnf(c_1404,plain,
    ( v1_funct_2(X0_50,X1_50,X1_50) != iProver_top
    | v3_funct_2(X0_50,X1_50,X1_50) != iProver_top
    | m1_subset_1(X0_50,k1_zfmisc_1(k2_zfmisc_1(X1_50,X1_50))) != iProver_top
    | m1_subset_1(k2_funct_2(X1_50,X0_50),k1_zfmisc_1(k2_zfmisc_1(X1_50,X1_50))) = iProver_top
    | v1_funct_1(X0_50) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_914])).

cnf(c_4056,plain,
    ( v1_funct_2(sK2,sK0,sK0) != iProver_top
    | v3_funct_2(sK2,sK0,sK0) != iProver_top
    | m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) = iProver_top
    | m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) != iProver_top
    | v1_funct_1(sK2) != iProver_top ),
    inference(superposition,[status(thm)],[c_4051,c_1404])).

cnf(c_34,plain,
    ( v1_funct_2(sK2,sK0,sK0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_23])).

cnf(c_4790,plain,
    ( m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_4056,c_33,c_34,c_35,c_36])).

cnf(c_4804,plain,
    ( k2_relat_1(k2_funct_1(sK2)) = sK0
    | v3_funct_2(k2_funct_1(sK2),sK0,sK0) != iProver_top
    | v1_funct_1(k2_funct_1(sK2)) != iProver_top
    | v1_relat_1(k2_funct_1(sK2)) != iProver_top ),
    inference(superposition,[status(thm)],[c_4790,c_1420])).

cnf(c_16,plain,
    ( ~ v1_funct_2(X0,X1,X1)
    | ~ v3_funct_2(X0,X1,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X1)))
    | ~ v1_funct_1(X0)
    | v1_funct_1(k2_funct_2(X1,X0)) ),
    inference(cnf_transformation,[],[f52])).

cnf(c_911,plain,
    ( ~ v1_funct_2(X0_50,X1_50,X1_50)
    | ~ v3_funct_2(X0_50,X1_50,X1_50)
    | ~ m1_subset_1(X0_50,k1_zfmisc_1(k2_zfmisc_1(X1_50,X1_50)))
    | ~ v1_funct_1(X0_50)
    | v1_funct_1(k2_funct_2(X1_50,X0_50)) ),
    inference(subtyping,[status(esa)],[c_16])).

cnf(c_1407,plain,
    ( v1_funct_2(X0_50,X1_50,X1_50) != iProver_top
    | v3_funct_2(X0_50,X1_50,X1_50) != iProver_top
    | m1_subset_1(X0_50,k1_zfmisc_1(k2_zfmisc_1(X1_50,X1_50))) != iProver_top
    | v1_funct_1(X0_50) != iProver_top
    | v1_funct_1(k2_funct_2(X1_50,X0_50)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_911])).

cnf(c_2669,plain,
    ( v1_funct_2(sK2,sK0,sK0) != iProver_top
    | v3_funct_2(sK2,sK0,sK0) != iProver_top
    | v1_funct_1(k2_funct_2(sK0,sK2)) = iProver_top
    | v1_funct_1(sK2) != iProver_top ),
    inference(superposition,[status(thm)],[c_1412,c_1407])).

cnf(c_1690,plain,
    ( ~ v1_funct_2(sK2,X0_50,X0_50)
    | ~ v3_funct_2(sK2,X0_50,X0_50)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X0_50,X0_50)))
    | v1_funct_1(k2_funct_2(X0_50,sK2))
    | ~ v1_funct_1(sK2) ),
    inference(instantiation,[status(thm)],[c_911])).

cnf(c_1691,plain,
    ( v1_funct_2(sK2,X0_50,X0_50) != iProver_top
    | v3_funct_2(sK2,X0_50,X0_50) != iProver_top
    | m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X0_50,X0_50))) != iProver_top
    | v1_funct_1(k2_funct_2(X0_50,sK2)) = iProver_top
    | v1_funct_1(sK2) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1690])).

cnf(c_1693,plain,
    ( v1_funct_2(sK2,sK0,sK0) != iProver_top
    | v3_funct_2(sK2,sK0,sK0) != iProver_top
    | m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) != iProver_top
    | v1_funct_1(k2_funct_2(sK0,sK2)) = iProver_top
    | v1_funct_1(sK2) != iProver_top ),
    inference(instantiation,[status(thm)],[c_1691])).

cnf(c_3610,plain,
    ( v1_funct_1(k2_funct_2(sK0,sK2)) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_2669,c_33,c_34,c_35,c_36,c_1693])).

cnf(c_4054,plain,
    ( v1_funct_1(k2_funct_1(sK2)) = iProver_top ),
    inference(demodulation,[status(thm)],[c_4051,c_3610])).

cnf(c_14,plain,
    ( ~ v1_funct_2(X0,X1,X1)
    | ~ v3_funct_2(X0,X1,X1)
    | v3_funct_2(k2_funct_2(X1,X0),X1,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X1)))
    | ~ v1_funct_1(X0) ),
    inference(cnf_transformation,[],[f54])).

cnf(c_913,plain,
    ( ~ v1_funct_2(X0_50,X1_50,X1_50)
    | ~ v3_funct_2(X0_50,X1_50,X1_50)
    | v3_funct_2(k2_funct_2(X1_50,X0_50),X1_50,X1_50)
    | ~ m1_subset_1(X0_50,k1_zfmisc_1(k2_zfmisc_1(X1_50,X1_50)))
    | ~ v1_funct_1(X0_50) ),
    inference(subtyping,[status(esa)],[c_14])).

cnf(c_1405,plain,
    ( v1_funct_2(X0_50,X1_50,X1_50) != iProver_top
    | v3_funct_2(X0_50,X1_50,X1_50) != iProver_top
    | v3_funct_2(k2_funct_2(X1_50,X0_50),X1_50,X1_50) = iProver_top
    | m1_subset_1(X0_50,k1_zfmisc_1(k2_zfmisc_1(X1_50,X1_50))) != iProver_top
    | v1_funct_1(X0_50) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_913])).

cnf(c_2820,plain,
    ( v1_funct_2(sK2,sK0,sK0) != iProver_top
    | v3_funct_2(k2_funct_2(sK0,sK2),sK0,sK0) = iProver_top
    | v3_funct_2(sK2,sK0,sK0) != iProver_top
    | v1_funct_1(sK2) != iProver_top ),
    inference(superposition,[status(thm)],[c_1412,c_1405])).

cnf(c_1744,plain,
    ( ~ v1_funct_2(sK2,X0_50,X0_50)
    | v3_funct_2(k2_funct_2(X0_50,sK2),X0_50,X0_50)
    | ~ v3_funct_2(sK2,X0_50,X0_50)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X0_50,X0_50)))
    | ~ v1_funct_1(sK2) ),
    inference(instantiation,[status(thm)],[c_913])).

cnf(c_1745,plain,
    ( v1_funct_2(sK2,X0_50,X0_50) != iProver_top
    | v3_funct_2(k2_funct_2(X0_50,sK2),X0_50,X0_50) = iProver_top
    | v3_funct_2(sK2,X0_50,X0_50) != iProver_top
    | m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X0_50,X0_50))) != iProver_top
    | v1_funct_1(sK2) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1744])).

cnf(c_1747,plain,
    ( v1_funct_2(sK2,sK0,sK0) != iProver_top
    | v3_funct_2(k2_funct_2(sK0,sK2),sK0,sK0) = iProver_top
    | v3_funct_2(sK2,sK0,sK0) != iProver_top
    | m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) != iProver_top
    | v1_funct_1(sK2) != iProver_top ),
    inference(instantiation,[status(thm)],[c_1745])).

cnf(c_4108,plain,
    ( v3_funct_2(k2_funct_2(sK0,sK2),sK0,sK0) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_2820,c_33,c_34,c_35,c_36,c_1747])).

cnf(c_4112,plain,
    ( v3_funct_2(k2_funct_1(sK2),sK0,sK0) = iProver_top ),
    inference(light_normalisation,[status(thm)],[c_4108,c_4051])).

cnf(c_4801,plain,
    ( v1_relat_1(k2_zfmisc_1(sK0,sK0)) != iProver_top
    | v1_relat_1(k2_funct_1(sK2)) = iProver_top ),
    inference(superposition,[status(thm)],[c_4790,c_1396])).

cnf(c_7968,plain,
    ( k2_relat_1(k2_funct_1(sK2)) = sK0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_4804,c_90,c_4054,c_4112,c_4801])).

cnf(c_7970,plain,
    ( k2_relat_1(k2_funct_1(sK2)) = k1_xboole_0 ),
    inference(light_normalisation,[status(thm)],[c_7968,c_6655])).

cnf(c_7972,plain,
    ( k2_funct_1(sK2) = k1_xboole_0
    | v1_relat_1(k2_funct_1(sK2)) != iProver_top ),
    inference(superposition,[status(thm)],[c_7970,c_1398])).

cnf(c_8102,plain,
    ( k2_funct_1(sK2) = k1_xboole_0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_7972,c_90,c_4801])).

cnf(c_9227,plain,
    ( k2_funct_1(k1_xboole_0) = k1_xboole_0 ),
    inference(demodulation,[status(thm)],[c_6751,c_8102])).

cnf(c_4560,plain,
    ( sK1 = k1_xboole_0
    | sK0 != k1_xboole_0
    | v1_relat_1(sK1) != iProver_top ),
    inference(superposition,[status(thm)],[c_4556,c_1398])).

cnf(c_4563,plain,
    ( sK0 != k1_xboole_0
    | sK1 = k1_xboole_0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_4560,c_90,c_1852])).

cnf(c_4564,plain,
    ( sK1 = k1_xboole_0
    | sK0 != k1_xboole_0 ),
    inference(renaming,[status(thm)],[c_4563])).

cnf(c_6673,plain,
    ( sK1 = k1_xboole_0
    | k1_xboole_0 != k1_xboole_0 ),
    inference(demodulation,[status(thm)],[c_6655,c_4564])).

cnf(c_6803,plain,
    ( sK1 = k1_xboole_0 ),
    inference(equality_resolution_simp,[status(thm)],[c_6673])).

cnf(c_6681,plain,
    ( r2_relset_1(k1_xboole_0,k1_xboole_0,sK2,k2_funct_1(sK1)) != iProver_top ),
    inference(demodulation,[status(thm)],[c_6655,c_4063])).

cnf(c_6756,plain,
    ( r2_relset_1(k1_xboole_0,k1_xboole_0,k1_xboole_0,k2_funct_1(sK1)) != iProver_top ),
    inference(demodulation,[status(thm)],[c_6751,c_6681])).

cnf(c_6806,plain,
    ( r2_relset_1(k1_xboole_0,k1_xboole_0,k1_xboole_0,k2_funct_1(k1_xboole_0)) != iProver_top ),
    inference(demodulation,[status(thm)],[c_6803,c_6756])).

cnf(c_10960,plain,
    ( r2_relset_1(k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0) != iProver_top ),
    inference(demodulation,[status(thm)],[c_9227,c_6806])).

cnf(c_1401,plain,
    ( r2_relset_1(X0_50,X1_50,X2_50,X2_50) = iProver_top
    | m1_subset_1(X2_50,k1_zfmisc_1(k2_zfmisc_1(X0_50,X1_50))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_917])).

cnf(c_2465,plain,
    ( r2_relset_1(sK0,sK0,sK2,sK2) = iProver_top ),
    inference(superposition,[status(thm)],[c_1412,c_1401])).

cnf(c_6689,plain,
    ( r2_relset_1(k1_xboole_0,k1_xboole_0,sK2,sK2) = iProver_top ),
    inference(demodulation,[status(thm)],[c_6655,c_2465])).

cnf(c_6761,plain,
    ( r2_relset_1(k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0) = iProver_top ),
    inference(demodulation,[status(thm)],[c_6751,c_6689])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_10960,c_6761])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.00/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.13/0.13  % Command    : iproveropt_run.sh %d %s
% 0.13/0.34  % Computer   : n009.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 12:56:56 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.21/0.34  % Running in FOF mode
% 3.47/0.98  % SZS status Started for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.47/0.98  
% 3.47/0.98  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 3.47/0.98  
% 3.47/0.98  ------  iProver source info
% 3.47/0.98  
% 3.47/0.98  git: date: 2020-06-30 10:37:57 +0100
% 3.47/0.98  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 3.47/0.98  git: non_committed_changes: false
% 3.47/0.98  git: last_make_outside_of_git: false
% 3.47/0.98  
% 3.47/0.98  ------ 
% 3.47/0.98  
% 3.47/0.98  ------ Input Options
% 3.47/0.98  
% 3.47/0.98  --out_options                           all
% 3.47/0.98  --tptp_safe_out                         true
% 3.47/0.98  --problem_path                          ""
% 3.47/0.98  --include_path                          ""
% 3.47/0.98  --clausifier                            res/vclausify_rel
% 3.47/0.98  --clausifier_options                    --mode clausify
% 3.47/0.98  --stdin                                 false
% 3.47/0.98  --stats_out                             all
% 3.47/0.98  
% 3.47/0.98  ------ General Options
% 3.47/0.98  
% 3.47/0.98  --fof                                   false
% 3.47/0.98  --time_out_real                         305.
% 3.47/0.98  --time_out_virtual                      -1.
% 3.47/0.98  --symbol_type_check                     false
% 3.47/0.98  --clausify_out                          false
% 3.47/0.98  --sig_cnt_out                           false
% 3.47/0.98  --trig_cnt_out                          false
% 3.47/0.98  --trig_cnt_out_tolerance                1.
% 3.47/0.98  --trig_cnt_out_sk_spl                   false
% 3.47/0.98  --abstr_cl_out                          false
% 3.47/0.98  
% 3.47/0.98  ------ Global Options
% 3.47/0.98  
% 3.47/0.98  --schedule                              default
% 3.47/0.98  --add_important_lit                     false
% 3.47/0.98  --prop_solver_per_cl                    1000
% 3.47/0.98  --min_unsat_core                        false
% 3.47/0.98  --soft_assumptions                      false
% 3.47/0.98  --soft_lemma_size                       3
% 3.47/0.98  --prop_impl_unit_size                   0
% 3.47/0.98  --prop_impl_unit                        []
% 3.47/0.98  --share_sel_clauses                     true
% 3.47/0.98  --reset_solvers                         false
% 3.47/0.98  --bc_imp_inh                            [conj_cone]
% 3.47/0.98  --conj_cone_tolerance                   3.
% 3.47/0.98  --extra_neg_conj                        none
% 3.47/0.98  --large_theory_mode                     true
% 3.47/0.98  --prolific_symb_bound                   200
% 3.47/0.98  --lt_threshold                          2000
% 3.47/0.98  --clause_weak_htbl                      true
% 3.47/0.98  --gc_record_bc_elim                     false
% 3.47/0.98  
% 3.47/0.98  ------ Preprocessing Options
% 3.47/0.98  
% 3.47/0.98  --preprocessing_flag                    true
% 3.47/0.98  --time_out_prep_mult                    0.1
% 3.47/0.98  --splitting_mode                        input
% 3.47/0.98  --splitting_grd                         true
% 3.47/0.98  --splitting_cvd                         false
% 3.47/0.98  --splitting_cvd_svl                     false
% 3.47/0.98  --splitting_nvd                         32
% 3.47/0.98  --sub_typing                            true
% 3.47/0.98  --prep_gs_sim                           true
% 3.47/0.98  --prep_unflatten                        true
% 3.47/0.98  --prep_res_sim                          true
% 3.47/0.98  --prep_upred                            true
% 3.47/0.98  --prep_sem_filter                       exhaustive
% 3.47/0.98  --prep_sem_filter_out                   false
% 3.47/0.98  --pred_elim                             true
% 3.47/0.98  --res_sim_input                         true
% 3.47/0.98  --eq_ax_congr_red                       true
% 3.47/0.98  --pure_diseq_elim                       true
% 3.47/0.98  --brand_transform                       false
% 3.47/0.98  --non_eq_to_eq                          false
% 3.47/0.98  --prep_def_merge                        true
% 3.47/0.98  --prep_def_merge_prop_impl              false
% 3.47/0.98  --prep_def_merge_mbd                    true
% 3.47/0.98  --prep_def_merge_tr_red                 false
% 3.47/0.98  --prep_def_merge_tr_cl                  false
% 3.47/0.98  --smt_preprocessing                     true
% 3.47/0.98  --smt_ac_axioms                         fast
% 3.47/0.98  --preprocessed_out                      false
% 3.47/0.98  --preprocessed_stats                    false
% 3.47/0.98  
% 3.47/0.98  ------ Abstraction refinement Options
% 3.47/0.98  
% 3.47/0.98  --abstr_ref                             []
% 3.47/0.98  --abstr_ref_prep                        false
% 3.47/0.98  --abstr_ref_until_sat                   false
% 3.47/0.98  --abstr_ref_sig_restrict                funpre
% 3.47/0.98  --abstr_ref_af_restrict_to_split_sk     false
% 3.47/0.98  --abstr_ref_under                       []
% 3.47/0.98  
% 3.47/0.98  ------ SAT Options
% 3.47/0.98  
% 3.47/0.98  --sat_mode                              false
% 3.47/0.98  --sat_fm_restart_options                ""
% 3.47/0.98  --sat_gr_def                            false
% 3.47/0.98  --sat_epr_types                         true
% 3.47/0.98  --sat_non_cyclic_types                  false
% 3.47/0.98  --sat_finite_models                     false
% 3.47/0.98  --sat_fm_lemmas                         false
% 3.47/0.98  --sat_fm_prep                           false
% 3.47/0.98  --sat_fm_uc_incr                        true
% 3.47/0.98  --sat_out_model                         small
% 3.47/0.98  --sat_out_clauses                       false
% 3.47/0.98  
% 3.47/0.98  ------ QBF Options
% 3.47/0.98  
% 3.47/0.98  --qbf_mode                              false
% 3.47/0.98  --qbf_elim_univ                         false
% 3.47/0.98  --qbf_dom_inst                          none
% 3.47/0.98  --qbf_dom_pre_inst                      false
% 3.47/0.98  --qbf_sk_in                             false
% 3.47/0.98  --qbf_pred_elim                         true
% 3.47/0.98  --qbf_split                             512
% 3.47/0.98  
% 3.47/0.98  ------ BMC1 Options
% 3.47/0.98  
% 3.47/0.98  --bmc1_incremental                      false
% 3.47/0.98  --bmc1_axioms                           reachable_all
% 3.47/0.98  --bmc1_min_bound                        0
% 3.47/0.98  --bmc1_max_bound                        -1
% 3.47/0.98  --bmc1_max_bound_default                -1
% 3.47/0.98  --bmc1_symbol_reachability              true
% 3.47/0.98  --bmc1_property_lemmas                  false
% 3.47/0.98  --bmc1_k_induction                      false
% 3.47/0.98  --bmc1_non_equiv_states                 false
% 3.47/0.98  --bmc1_deadlock                         false
% 3.47/0.98  --bmc1_ucm                              false
% 3.47/0.98  --bmc1_add_unsat_core                   none
% 3.47/0.98  --bmc1_unsat_core_children              false
% 3.47/0.98  --bmc1_unsat_core_extrapolate_axioms    false
% 3.47/0.98  --bmc1_out_stat                         full
% 3.47/0.98  --bmc1_ground_init                      false
% 3.47/0.98  --bmc1_pre_inst_next_state              false
% 3.47/0.98  --bmc1_pre_inst_state                   false
% 3.47/0.98  --bmc1_pre_inst_reach_state             false
% 3.47/0.98  --bmc1_out_unsat_core                   false
% 3.47/0.98  --bmc1_aig_witness_out                  false
% 3.47/0.98  --bmc1_verbose                          false
% 3.47/0.98  --bmc1_dump_clauses_tptp                false
% 3.47/0.98  --bmc1_dump_unsat_core_tptp             false
% 3.47/0.98  --bmc1_dump_file                        -
% 3.47/0.98  --bmc1_ucm_expand_uc_limit              128
% 3.47/0.98  --bmc1_ucm_n_expand_iterations          6
% 3.47/0.98  --bmc1_ucm_extend_mode                  1
% 3.47/0.98  --bmc1_ucm_init_mode                    2
% 3.47/0.98  --bmc1_ucm_cone_mode                    none
% 3.47/0.98  --bmc1_ucm_reduced_relation_type        0
% 3.47/0.98  --bmc1_ucm_relax_model                  4
% 3.47/0.98  --bmc1_ucm_full_tr_after_sat            true
% 3.47/0.98  --bmc1_ucm_expand_neg_assumptions       false
% 3.47/0.98  --bmc1_ucm_layered_model                none
% 3.47/0.98  --bmc1_ucm_max_lemma_size               10
% 3.47/0.98  
% 3.47/0.98  ------ AIG Options
% 3.47/0.98  
% 3.47/0.98  --aig_mode                              false
% 3.47/0.98  
% 3.47/0.98  ------ Instantiation Options
% 3.47/0.98  
% 3.47/0.98  --instantiation_flag                    true
% 3.47/0.98  --inst_sos_flag                         false
% 3.47/0.98  --inst_sos_phase                        true
% 3.47/0.98  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 3.47/0.98  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 3.47/0.98  --inst_lit_sel_side                     num_symb
% 3.47/0.98  --inst_solver_per_active                1400
% 3.47/0.98  --inst_solver_calls_frac                1.
% 3.47/0.98  --inst_passive_queue_type               priority_queues
% 3.47/0.98  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 3.47/0.98  --inst_passive_queues_freq              [25;2]
% 3.47/0.98  --inst_dismatching                      true
% 3.47/0.98  --inst_eager_unprocessed_to_passive     true
% 3.47/0.98  --inst_prop_sim_given                   true
% 3.47/0.98  --inst_prop_sim_new                     false
% 3.47/0.98  --inst_subs_new                         false
% 3.47/0.98  --inst_eq_res_simp                      false
% 3.47/0.98  --inst_subs_given                       false
% 3.47/0.98  --inst_orphan_elimination               true
% 3.47/0.98  --inst_learning_loop_flag               true
% 3.47/0.98  --inst_learning_start                   3000
% 3.47/0.98  --inst_learning_factor                  2
% 3.47/0.98  --inst_start_prop_sim_after_learn       3
% 3.47/0.98  --inst_sel_renew                        solver
% 3.47/0.98  --inst_lit_activity_flag                true
% 3.47/0.98  --inst_restr_to_given                   false
% 3.47/0.98  --inst_activity_threshold               500
% 3.47/0.98  --inst_out_proof                        true
% 3.47/0.98  
% 3.47/0.98  ------ Resolution Options
% 3.47/0.98  
% 3.47/0.98  --resolution_flag                       true
% 3.47/0.98  --res_lit_sel                           adaptive
% 3.47/0.98  --res_lit_sel_side                      none
% 3.47/0.98  --res_ordering                          kbo
% 3.47/0.98  --res_to_prop_solver                    active
% 3.47/0.98  --res_prop_simpl_new                    false
% 3.47/0.98  --res_prop_simpl_given                  true
% 3.47/0.98  --res_passive_queue_type                priority_queues
% 3.47/0.98  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 3.47/0.98  --res_passive_queues_freq               [15;5]
% 3.47/0.98  --res_forward_subs                      full
% 3.47/0.98  --res_backward_subs                     full
% 3.47/0.98  --res_forward_subs_resolution           true
% 3.47/0.98  --res_backward_subs_resolution          true
% 3.47/0.98  --res_orphan_elimination                true
% 3.47/0.98  --res_time_limit                        2.
% 3.47/0.98  --res_out_proof                         true
% 3.47/0.98  
% 3.47/0.98  ------ Superposition Options
% 3.47/0.98  
% 3.47/0.98  --superposition_flag                    true
% 3.47/0.98  --sup_passive_queue_type                priority_queues
% 3.47/0.98  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 3.47/0.98  --sup_passive_queues_freq               [8;1;4]
% 3.47/0.98  --demod_completeness_check              fast
% 3.47/0.98  --demod_use_ground                      true
% 3.47/0.98  --sup_to_prop_solver                    passive
% 3.47/0.98  --sup_prop_simpl_new                    true
% 3.47/0.98  --sup_prop_simpl_given                  true
% 3.47/0.98  --sup_fun_splitting                     false
% 3.47/0.98  --sup_smt_interval                      50000
% 3.47/0.98  
% 3.47/0.98  ------ Superposition Simplification Setup
% 3.47/0.98  
% 3.47/0.98  --sup_indices_passive                   []
% 3.47/0.98  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.47/0.98  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.47/0.98  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.47/0.98  --sup_full_triv                         [TrivRules;PropSubs]
% 3.47/0.98  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.47/0.98  --sup_full_bw                           [BwDemod]
% 3.47/0.98  --sup_immed_triv                        [TrivRules]
% 3.47/0.98  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 3.47/0.98  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.47/0.98  --sup_immed_bw_main                     []
% 3.47/0.98  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 3.47/0.98  --sup_input_triv                        [Unflattening;TrivRules]
% 3.47/0.98  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.47/0.98  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 3.47/0.98  
% 3.47/0.98  ------ Combination Options
% 3.47/0.98  
% 3.47/0.98  --comb_res_mult                         3
% 3.47/0.98  --comb_sup_mult                         2
% 3.47/0.98  --comb_inst_mult                        10
% 3.47/0.98  
% 3.47/0.98  ------ Debug Options
% 3.47/0.98  
% 3.47/0.98  --dbg_backtrace                         false
% 3.47/0.98  --dbg_dump_prop_clauses                 false
% 3.47/0.98  --dbg_dump_prop_clauses_file            -
% 3.47/0.98  --dbg_out_stat                          false
% 3.47/0.98  ------ Parsing...
% 3.47/0.98  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 3.47/0.98  
% 3.47/0.98  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe:1:0s pe:2:0s pe_e  sf_s  rm: 3 0s  sf_e  pe_s  pe_e 
% 3.47/0.98  
% 3.47/0.98  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 3.47/0.98  
% 3.47/0.98  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 3.47/0.98  ------ Proving...
% 3.47/0.98  ------ Problem Properties 
% 3.47/0.98  
% 3.47/0.98  
% 3.47/0.98  clauses                                 25
% 3.47/0.98  conjectures                             10
% 3.47/0.98  EPR                                     6
% 3.47/0.98  Horn                                    24
% 3.47/0.98  unary                                   11
% 3.47/0.98  binary                                  2
% 3.47/0.98  lits                                    74
% 3.47/0.98  lits eq                                 12
% 3.47/0.98  fd_pure                                 0
% 3.47/0.98  fd_pseudo                               0
% 3.47/0.98  fd_cond                                 2
% 3.47/0.98  fd_pseudo_cond                          3
% 3.47/0.98  AC symbols                              0
% 3.47/0.98  
% 3.47/0.98  ------ Schedule dynamic 5 is on 
% 3.47/0.98  
% 3.47/0.98  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" Time Limit: 10.
% 3.47/0.98  
% 3.47/0.98  
% 3.47/0.98  ------ 
% 3.47/0.98  Current options:
% 3.47/0.98  ------ 
% 3.47/0.98  
% 3.47/0.98  ------ Input Options
% 3.47/0.98  
% 3.47/0.98  --out_options                           all
% 3.47/0.98  --tptp_safe_out                         true
% 3.47/0.98  --problem_path                          ""
% 3.47/0.98  --include_path                          ""
% 3.47/0.98  --clausifier                            res/vclausify_rel
% 3.47/0.98  --clausifier_options                    --mode clausify
% 3.47/0.98  --stdin                                 false
% 3.47/0.98  --stats_out                             all
% 3.47/0.98  
% 3.47/0.98  ------ General Options
% 3.47/0.98  
% 3.47/0.98  --fof                                   false
% 3.47/0.98  --time_out_real                         305.
% 3.47/0.98  --time_out_virtual                      -1.
% 3.47/0.98  --symbol_type_check                     false
% 3.47/0.98  --clausify_out                          false
% 3.47/0.98  --sig_cnt_out                           false
% 3.47/0.98  --trig_cnt_out                          false
% 3.47/0.98  --trig_cnt_out_tolerance                1.
% 3.47/0.98  --trig_cnt_out_sk_spl                   false
% 3.47/0.98  --abstr_cl_out                          false
% 3.47/0.98  
% 3.47/0.98  ------ Global Options
% 3.47/0.98  
% 3.47/0.98  --schedule                              default
% 3.47/0.98  --add_important_lit                     false
% 3.47/0.98  --prop_solver_per_cl                    1000
% 3.47/0.98  --min_unsat_core                        false
% 3.47/0.98  --soft_assumptions                      false
% 3.47/0.98  --soft_lemma_size                       3
% 3.47/0.98  --prop_impl_unit_size                   0
% 3.47/0.98  --prop_impl_unit                        []
% 3.47/0.98  --share_sel_clauses                     true
% 3.47/0.98  --reset_solvers                         false
% 3.47/0.98  --bc_imp_inh                            [conj_cone]
% 3.47/0.98  --conj_cone_tolerance                   3.
% 3.47/0.98  --extra_neg_conj                        none
% 3.47/0.98  --large_theory_mode                     true
% 3.47/0.98  --prolific_symb_bound                   200
% 3.47/0.98  --lt_threshold                          2000
% 3.47/0.98  --clause_weak_htbl                      true
% 3.47/0.98  --gc_record_bc_elim                     false
% 3.47/0.98  
% 3.47/0.98  ------ Preprocessing Options
% 3.47/0.98  
% 3.47/0.98  --preprocessing_flag                    true
% 3.47/0.98  --time_out_prep_mult                    0.1
% 3.47/0.98  --splitting_mode                        input
% 3.47/0.98  --splitting_grd                         true
% 3.47/0.98  --splitting_cvd                         false
% 3.47/0.98  --splitting_cvd_svl                     false
% 3.47/0.98  --splitting_nvd                         32
% 3.47/0.98  --sub_typing                            true
% 3.47/0.98  --prep_gs_sim                           true
% 3.47/0.98  --prep_unflatten                        true
% 3.47/0.98  --prep_res_sim                          true
% 3.47/0.98  --prep_upred                            true
% 3.47/0.98  --prep_sem_filter                       exhaustive
% 3.47/0.98  --prep_sem_filter_out                   false
% 3.47/0.98  --pred_elim                             true
% 3.47/0.98  --res_sim_input                         true
% 3.47/0.98  --eq_ax_congr_red                       true
% 3.47/0.98  --pure_diseq_elim                       true
% 3.47/0.98  --brand_transform                       false
% 3.47/0.98  --non_eq_to_eq                          false
% 3.47/0.98  --prep_def_merge                        true
% 3.47/0.98  --prep_def_merge_prop_impl              false
% 3.47/0.98  --prep_def_merge_mbd                    true
% 3.47/0.98  --prep_def_merge_tr_red                 false
% 3.47/0.98  --prep_def_merge_tr_cl                  false
% 3.47/0.98  --smt_preprocessing                     true
% 3.47/0.98  --smt_ac_axioms                         fast
% 3.47/0.98  --preprocessed_out                      false
% 3.47/0.98  --preprocessed_stats                    false
% 3.47/0.98  
% 3.47/0.98  ------ Abstraction refinement Options
% 3.47/0.98  
% 3.47/0.98  --abstr_ref                             []
% 3.47/0.98  --abstr_ref_prep                        false
% 3.47/0.98  --abstr_ref_until_sat                   false
% 3.47/0.98  --abstr_ref_sig_restrict                funpre
% 3.47/0.98  --abstr_ref_af_restrict_to_split_sk     false
% 3.47/0.98  --abstr_ref_under                       []
% 3.47/0.98  
% 3.47/0.98  ------ SAT Options
% 3.47/0.98  
% 3.47/0.98  --sat_mode                              false
% 3.47/0.98  --sat_fm_restart_options                ""
% 3.47/0.98  --sat_gr_def                            false
% 3.47/0.98  --sat_epr_types                         true
% 3.47/0.98  --sat_non_cyclic_types                  false
% 3.47/0.98  --sat_finite_models                     false
% 3.47/0.98  --sat_fm_lemmas                         false
% 3.47/0.98  --sat_fm_prep                           false
% 3.47/0.98  --sat_fm_uc_incr                        true
% 3.47/0.98  --sat_out_model                         small
% 3.47/0.98  --sat_out_clauses                       false
% 3.47/0.98  
% 3.47/0.98  ------ QBF Options
% 3.47/0.98  
% 3.47/0.98  --qbf_mode                              false
% 3.47/0.98  --qbf_elim_univ                         false
% 3.47/0.98  --qbf_dom_inst                          none
% 3.47/0.98  --qbf_dom_pre_inst                      false
% 3.47/0.98  --qbf_sk_in                             false
% 3.47/0.98  --qbf_pred_elim                         true
% 3.47/0.98  --qbf_split                             512
% 3.47/0.98  
% 3.47/0.98  ------ BMC1 Options
% 3.47/0.98  
% 3.47/0.98  --bmc1_incremental                      false
% 3.47/0.98  --bmc1_axioms                           reachable_all
% 3.47/0.98  --bmc1_min_bound                        0
% 3.47/0.98  --bmc1_max_bound                        -1
% 3.47/0.98  --bmc1_max_bound_default                -1
% 3.47/0.98  --bmc1_symbol_reachability              true
% 3.47/0.98  --bmc1_property_lemmas                  false
% 3.47/0.98  --bmc1_k_induction                      false
% 3.47/0.98  --bmc1_non_equiv_states                 false
% 3.47/0.98  --bmc1_deadlock                         false
% 3.47/0.98  --bmc1_ucm                              false
% 3.47/0.98  --bmc1_add_unsat_core                   none
% 3.47/0.98  --bmc1_unsat_core_children              false
% 3.47/0.98  --bmc1_unsat_core_extrapolate_axioms    false
% 3.47/0.98  --bmc1_out_stat                         full
% 3.47/0.98  --bmc1_ground_init                      false
% 3.47/0.98  --bmc1_pre_inst_next_state              false
% 3.47/0.98  --bmc1_pre_inst_state                   false
% 3.47/0.98  --bmc1_pre_inst_reach_state             false
% 3.47/0.98  --bmc1_out_unsat_core                   false
% 3.47/0.98  --bmc1_aig_witness_out                  false
% 3.47/0.98  --bmc1_verbose                          false
% 3.47/0.98  --bmc1_dump_clauses_tptp                false
% 3.47/0.98  --bmc1_dump_unsat_core_tptp             false
% 3.47/0.98  --bmc1_dump_file                        -
% 3.47/0.98  --bmc1_ucm_expand_uc_limit              128
% 3.47/0.98  --bmc1_ucm_n_expand_iterations          6
% 3.47/0.98  --bmc1_ucm_extend_mode                  1
% 3.47/0.98  --bmc1_ucm_init_mode                    2
% 3.47/0.98  --bmc1_ucm_cone_mode                    none
% 3.47/0.98  --bmc1_ucm_reduced_relation_type        0
% 3.47/0.98  --bmc1_ucm_relax_model                  4
% 3.47/0.98  --bmc1_ucm_full_tr_after_sat            true
% 3.47/0.98  --bmc1_ucm_expand_neg_assumptions       false
% 3.47/0.98  --bmc1_ucm_layered_model                none
% 3.47/0.98  --bmc1_ucm_max_lemma_size               10
% 3.47/0.98  
% 3.47/0.98  ------ AIG Options
% 3.47/0.98  
% 3.47/0.98  --aig_mode                              false
% 3.47/0.98  
% 3.47/0.98  ------ Instantiation Options
% 3.47/0.98  
% 3.47/0.98  --instantiation_flag                    true
% 3.47/0.98  --inst_sos_flag                         false
% 3.47/0.98  --inst_sos_phase                        true
% 3.47/0.98  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 3.47/0.98  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 3.47/0.98  --inst_lit_sel_side                     none
% 3.47/0.98  --inst_solver_per_active                1400
% 3.47/0.98  --inst_solver_calls_frac                1.
% 3.47/0.98  --inst_passive_queue_type               priority_queues
% 3.47/0.98  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 3.47/0.98  --inst_passive_queues_freq              [25;2]
% 3.47/0.98  --inst_dismatching                      true
% 3.47/0.98  --inst_eager_unprocessed_to_passive     true
% 3.47/0.98  --inst_prop_sim_given                   true
% 3.47/0.98  --inst_prop_sim_new                     false
% 3.47/0.98  --inst_subs_new                         false
% 3.47/0.98  --inst_eq_res_simp                      false
% 3.47/0.98  --inst_subs_given                       false
% 3.47/0.98  --inst_orphan_elimination               true
% 3.47/0.98  --inst_learning_loop_flag               true
% 3.47/0.98  --inst_learning_start                   3000
% 3.47/0.98  --inst_learning_factor                  2
% 3.47/0.98  --inst_start_prop_sim_after_learn       3
% 3.47/0.98  --inst_sel_renew                        solver
% 3.47/0.98  --inst_lit_activity_flag                true
% 3.47/0.98  --inst_restr_to_given                   false
% 3.47/0.98  --inst_activity_threshold               500
% 3.47/0.98  --inst_out_proof                        true
% 3.47/0.98  
% 3.47/0.98  ------ Resolution Options
% 3.47/0.98  
% 3.47/0.98  --resolution_flag                       false
% 3.47/0.98  --res_lit_sel                           adaptive
% 3.47/0.98  --res_lit_sel_side                      none
% 3.47/0.98  --res_ordering                          kbo
% 3.47/0.98  --res_to_prop_solver                    active
% 3.47/0.98  --res_prop_simpl_new                    false
% 3.47/0.98  --res_prop_simpl_given                  true
% 3.47/0.98  --res_passive_queue_type                priority_queues
% 3.47/0.98  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 3.47/0.98  --res_passive_queues_freq               [15;5]
% 3.47/0.98  --res_forward_subs                      full
% 3.47/0.98  --res_backward_subs                     full
% 3.47/0.98  --res_forward_subs_resolution           true
% 3.47/0.98  --res_backward_subs_resolution          true
% 3.47/0.98  --res_orphan_elimination                true
% 3.47/0.98  --res_time_limit                        2.
% 3.47/0.98  --res_out_proof                         true
% 3.47/0.98  
% 3.47/0.98  ------ Superposition Options
% 3.47/0.98  
% 3.47/0.98  --superposition_flag                    true
% 3.47/0.98  --sup_passive_queue_type                priority_queues
% 3.47/0.98  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 3.47/0.98  --sup_passive_queues_freq               [8;1;4]
% 3.47/0.98  --demod_completeness_check              fast
% 3.47/0.98  --demod_use_ground                      true
% 3.47/0.98  --sup_to_prop_solver                    passive
% 3.47/0.98  --sup_prop_simpl_new                    true
% 3.47/0.98  --sup_prop_simpl_given                  true
% 3.47/0.98  --sup_fun_splitting                     false
% 3.47/0.98  --sup_smt_interval                      50000
% 3.47/0.98  
% 3.47/0.98  ------ Superposition Simplification Setup
% 3.47/0.98  
% 3.47/0.98  --sup_indices_passive                   []
% 3.47/0.98  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.47/0.98  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.47/0.98  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.47/0.98  --sup_full_triv                         [TrivRules;PropSubs]
% 3.47/0.98  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.47/0.98  --sup_full_bw                           [BwDemod]
% 3.47/0.98  --sup_immed_triv                        [TrivRules]
% 3.47/0.98  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 3.47/0.98  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.47/0.98  --sup_immed_bw_main                     []
% 3.47/0.98  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 3.47/0.98  --sup_input_triv                        [Unflattening;TrivRules]
% 3.47/0.98  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.47/0.98  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 3.47/0.98  
% 3.47/0.98  ------ Combination Options
% 3.47/0.98  
% 3.47/0.98  --comb_res_mult                         3
% 3.47/0.98  --comb_sup_mult                         2
% 3.47/0.98  --comb_inst_mult                        10
% 3.47/0.98  
% 3.47/0.98  ------ Debug Options
% 3.47/0.98  
% 3.47/0.98  --dbg_backtrace                         false
% 3.47/0.98  --dbg_dump_prop_clauses                 false
% 3.47/0.98  --dbg_dump_prop_clauses_file            -
% 3.47/0.98  --dbg_out_stat                          false
% 3.47/0.98  
% 3.47/0.98  
% 3.47/0.98  
% 3.47/0.98  
% 3.47/0.98  ------ Proving...
% 3.47/0.98  
% 3.47/0.98  
% 3.47/0.98  % SZS status Theorem for theBenchmark.p
% 3.47/0.98  
% 3.47/0.98  % SZS output start CNFRefutation for theBenchmark.p
% 3.47/0.98  
% 3.47/0.98  fof(f12,conjecture,(
% 3.47/0.98    ! [X0,X1] : ((m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v3_funct_2(X1,X0,X0) & v1_funct_2(X1,X0,X0) & v1_funct_1(X1)) => ! [X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v3_funct_2(X2,X0,X0) & v1_funct_2(X2,X0,X0) & v1_funct_1(X2)) => (r2_relset_1(X0,X0,k1_partfun1(X0,X0,X0,X0,X1,X2),k6_partfun1(X0)) => r2_relset_1(X0,X0,X2,k2_funct_2(X0,X1)))))),
% 3.47/0.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.47/0.98  
% 3.47/0.98  fof(f13,negated_conjecture,(
% 3.47/0.98    ~! [X0,X1] : ((m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v3_funct_2(X1,X0,X0) & v1_funct_2(X1,X0,X0) & v1_funct_1(X1)) => ! [X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v3_funct_2(X2,X0,X0) & v1_funct_2(X2,X0,X0) & v1_funct_1(X2)) => (r2_relset_1(X0,X0,k1_partfun1(X0,X0,X0,X0,X1,X2),k6_partfun1(X0)) => r2_relset_1(X0,X0,X2,k2_funct_2(X0,X1)))))),
% 3.47/0.98    inference(negated_conjecture,[],[f12])).
% 3.47/0.98  
% 3.47/0.98  fof(f32,plain,(
% 3.47/0.98    ? [X0,X1] : (? [X2] : ((~r2_relset_1(X0,X0,X2,k2_funct_2(X0,X1)) & r2_relset_1(X0,X0,k1_partfun1(X0,X0,X0,X0,X1,X2),k6_partfun1(X0))) & (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v3_funct_2(X2,X0,X0) & v1_funct_2(X2,X0,X0) & v1_funct_1(X2))) & (m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v3_funct_2(X1,X0,X0) & v1_funct_2(X1,X0,X0) & v1_funct_1(X1)))),
% 3.47/0.99    inference(ennf_transformation,[],[f13])).
% 3.47/0.99  
% 3.47/0.99  fof(f33,plain,(
% 3.47/0.99    ? [X0,X1] : (? [X2] : (~r2_relset_1(X0,X0,X2,k2_funct_2(X0,X1)) & r2_relset_1(X0,X0,k1_partfun1(X0,X0,X0,X0,X1,X2),k6_partfun1(X0)) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v3_funct_2(X2,X0,X0) & v1_funct_2(X2,X0,X0) & v1_funct_1(X2)) & m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v3_funct_2(X1,X0,X0) & v1_funct_2(X1,X0,X0) & v1_funct_1(X1))),
% 3.47/0.99    inference(flattening,[],[f32])).
% 3.47/0.99  
% 3.47/0.99  fof(f37,plain,(
% 3.47/0.99    ( ! [X0,X1] : (? [X2] : (~r2_relset_1(X0,X0,X2,k2_funct_2(X0,X1)) & r2_relset_1(X0,X0,k1_partfun1(X0,X0,X0,X0,X1,X2),k6_partfun1(X0)) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v3_funct_2(X2,X0,X0) & v1_funct_2(X2,X0,X0) & v1_funct_1(X2)) => (~r2_relset_1(X0,X0,sK2,k2_funct_2(X0,X1)) & r2_relset_1(X0,X0,k1_partfun1(X0,X0,X0,X0,X1,sK2),k6_partfun1(X0)) & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v3_funct_2(sK2,X0,X0) & v1_funct_2(sK2,X0,X0) & v1_funct_1(sK2))) )),
% 3.47/0.99    introduced(choice_axiom,[])).
% 3.47/0.99  
% 3.47/0.99  fof(f36,plain,(
% 3.47/0.99    ? [X0,X1] : (? [X2] : (~r2_relset_1(X0,X0,X2,k2_funct_2(X0,X1)) & r2_relset_1(X0,X0,k1_partfun1(X0,X0,X0,X0,X1,X2),k6_partfun1(X0)) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v3_funct_2(X2,X0,X0) & v1_funct_2(X2,X0,X0) & v1_funct_1(X2)) & m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v3_funct_2(X1,X0,X0) & v1_funct_2(X1,X0,X0) & v1_funct_1(X1)) => (? [X2] : (~r2_relset_1(sK0,sK0,X2,k2_funct_2(sK0,sK1)) & r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK0,sK0,sK0,sK1,X2),k6_partfun1(sK0)) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) & v3_funct_2(X2,sK0,sK0) & v1_funct_2(X2,sK0,sK0) & v1_funct_1(X2)) & m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) & v3_funct_2(sK1,sK0,sK0) & v1_funct_2(sK1,sK0,sK0) & v1_funct_1(sK1))),
% 3.47/0.99    introduced(choice_axiom,[])).
% 3.47/0.99  
% 3.47/0.99  fof(f38,plain,(
% 3.47/0.99    (~r2_relset_1(sK0,sK0,sK2,k2_funct_2(sK0,sK1)) & r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK0,sK0,sK0,sK1,sK2),k6_partfun1(sK0)) & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) & v3_funct_2(sK2,sK0,sK0) & v1_funct_2(sK2,sK0,sK0) & v1_funct_1(sK2)) & m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) & v3_funct_2(sK1,sK0,sK0) & v1_funct_2(sK1,sK0,sK0) & v1_funct_1(sK1)),
% 3.47/0.99    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f33,f37,f36])).
% 3.47/0.99  
% 3.47/0.99  fof(f66,plain,(
% 3.47/0.99    r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK0,sK0,sK0,sK1,sK2),k6_partfun1(sK0))),
% 3.47/0.99    inference(cnf_transformation,[],[f38])).
% 3.47/0.99  
% 3.47/0.99  fof(f61,plain,(
% 3.47/0.99    m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))),
% 3.47/0.99    inference(cnf_transformation,[],[f38])).
% 3.47/0.99  
% 3.47/0.99  fof(f5,axiom,(
% 3.47/0.99    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k2_relat_1(X2) = k2_relset_1(X0,X1,X2))),
% 3.47/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.47/0.99  
% 3.47/0.99  fof(f19,plain,(
% 3.47/0.99    ! [X0,X1,X2] : (k2_relat_1(X2) = k2_relset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 3.47/0.99    inference(ennf_transformation,[],[f5])).
% 3.47/0.99  
% 3.47/0.99  fof(f44,plain,(
% 3.47/0.99    ( ! [X2,X0,X1] : (k2_relat_1(X2) = k2_relset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 3.47/0.99    inference(cnf_transformation,[],[f19])).
% 3.47/0.99  
% 3.47/0.99  fof(f11,axiom,(
% 3.47/0.99    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => ! [X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(X3,X1,X0) & v1_funct_1(X3)) => ((v2_funct_1(X2) & r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0)) & k2_relset_1(X0,X1,X2) = X1) => (k2_funct_1(X2) = X3 | k1_xboole_0 = X1 | k1_xboole_0 = X0))))),
% 3.47/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.47/0.99  
% 3.47/0.99  fof(f30,plain,(
% 3.47/0.99    ! [X0,X1,X2] : (! [X3] : (((k2_funct_1(X2) = X3 | k1_xboole_0 = X1 | k1_xboole_0 = X0) | (~v2_funct_1(X2) | ~r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0)) | k2_relset_1(X0,X1,X2) != X1)) | (~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) | ~v1_funct_2(X3,X1,X0) | ~v1_funct_1(X3))) | (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2)))),
% 3.47/0.99    inference(ennf_transformation,[],[f11])).
% 3.47/0.99  
% 3.47/0.99  fof(f31,plain,(
% 3.47/0.99    ! [X0,X1,X2] : (! [X3] : (k2_funct_1(X2) = X3 | k1_xboole_0 = X1 | k1_xboole_0 = X0 | ~v2_funct_1(X2) | ~r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0)) | k2_relset_1(X0,X1,X2) != X1 | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) | ~v1_funct_2(X3,X1,X0) | ~v1_funct_1(X3)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2))),
% 3.47/0.99    inference(flattening,[],[f30])).
% 3.47/0.99  
% 3.47/0.99  fof(f57,plain,(
% 3.47/0.99    ( ! [X2,X0,X3,X1] : (k2_funct_1(X2) = X3 | k1_xboole_0 = X1 | k1_xboole_0 = X0 | ~v2_funct_1(X2) | ~r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0)) | k2_relset_1(X0,X1,X2) != X1 | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) | ~v1_funct_2(X3,X1,X0) | ~v1_funct_1(X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2)) )),
% 3.47/0.99    inference(cnf_transformation,[],[f31])).
% 3.47/0.99  
% 3.47/0.99  fof(f58,plain,(
% 3.47/0.99    v1_funct_1(sK1)),
% 3.47/0.99    inference(cnf_transformation,[],[f38])).
% 3.47/0.99  
% 3.47/0.99  fof(f59,plain,(
% 3.47/0.99    v1_funct_2(sK1,sK0,sK0)),
% 3.47/0.99    inference(cnf_transformation,[],[f38])).
% 3.47/0.99  
% 3.47/0.99  fof(f60,plain,(
% 3.47/0.99    v3_funct_2(sK1,sK0,sK0)),
% 3.47/0.99    inference(cnf_transformation,[],[f38])).
% 3.47/0.99  
% 3.47/0.99  fof(f7,axiom,(
% 3.47/0.99    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => ((v3_funct_2(X2,X0,X1) & v1_funct_1(X2)) => (v2_funct_2(X2,X1) & v2_funct_1(X2) & v1_funct_1(X2))))),
% 3.47/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.47/0.99  
% 3.47/0.99  fof(f22,plain,(
% 3.47/0.99    ! [X0,X1,X2] : (((v2_funct_2(X2,X1) & v2_funct_1(X2) & v1_funct_1(X2)) | (~v3_funct_2(X2,X0,X1) | ~v1_funct_1(X2))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 3.47/0.99    inference(ennf_transformation,[],[f7])).
% 3.47/0.99  
% 3.47/0.99  fof(f23,plain,(
% 3.47/0.99    ! [X0,X1,X2] : ((v2_funct_2(X2,X1) & v2_funct_1(X2) & v1_funct_1(X2)) | ~v3_funct_2(X2,X0,X1) | ~v1_funct_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 3.47/0.99    inference(flattening,[],[f22])).
% 3.47/0.99  
% 3.47/0.99  fof(f48,plain,(
% 3.47/0.99    ( ! [X2,X0,X1] : (v2_funct_1(X2) | ~v3_funct_2(X2,X0,X1) | ~v1_funct_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 3.47/0.99    inference(cnf_transformation,[],[f23])).
% 3.47/0.99  
% 3.47/0.99  fof(f49,plain,(
% 3.47/0.99    ( ! [X2,X0,X1] : (v2_funct_2(X2,X1) | ~v3_funct_2(X2,X0,X1) | ~v1_funct_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 3.47/0.99    inference(cnf_transformation,[],[f23])).
% 3.47/0.99  
% 3.47/0.99  fof(f8,axiom,(
% 3.47/0.99    ! [X0,X1] : ((v5_relat_1(X1,X0) & v1_relat_1(X1)) => (v2_funct_2(X1,X0) <=> k2_relat_1(X1) = X0))),
% 3.47/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.47/0.99  
% 3.47/0.99  fof(f24,plain,(
% 3.47/0.99    ! [X0,X1] : ((v2_funct_2(X1,X0) <=> k2_relat_1(X1) = X0) | (~v5_relat_1(X1,X0) | ~v1_relat_1(X1)))),
% 3.47/0.99    inference(ennf_transformation,[],[f8])).
% 3.47/0.99  
% 3.47/0.99  fof(f25,plain,(
% 3.47/0.99    ! [X0,X1] : ((v2_funct_2(X1,X0) <=> k2_relat_1(X1) = X0) | ~v5_relat_1(X1,X0) | ~v1_relat_1(X1))),
% 3.47/0.99    inference(flattening,[],[f24])).
% 3.47/0.99  
% 3.47/0.99  fof(f35,plain,(
% 3.47/0.99    ! [X0,X1] : (((v2_funct_2(X1,X0) | k2_relat_1(X1) != X0) & (k2_relat_1(X1) = X0 | ~v2_funct_2(X1,X0))) | ~v5_relat_1(X1,X0) | ~v1_relat_1(X1))),
% 3.47/0.99    inference(nnf_transformation,[],[f25])).
% 3.47/0.99  
% 3.47/0.99  fof(f50,plain,(
% 3.47/0.99    ( ! [X0,X1] : (k2_relat_1(X1) = X0 | ~v2_funct_2(X1,X0) | ~v5_relat_1(X1,X0) | ~v1_relat_1(X1)) )),
% 3.47/0.99    inference(cnf_transformation,[],[f35])).
% 3.47/0.99  
% 3.47/0.99  fof(f4,axiom,(
% 3.47/0.99    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => (v5_relat_1(X2,X1) & v4_relat_1(X2,X0)))),
% 3.47/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.47/0.99  
% 3.47/0.99  fof(f14,plain,(
% 3.47/0.99    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => v5_relat_1(X2,X1))),
% 3.47/0.99    inference(pure_predicate_removal,[],[f4])).
% 3.47/0.99  
% 3.47/0.99  fof(f18,plain,(
% 3.47/0.99    ! [X0,X1,X2] : (v5_relat_1(X2,X1) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 3.47/0.99    inference(ennf_transformation,[],[f14])).
% 3.47/0.99  
% 3.47/0.99  fof(f43,plain,(
% 3.47/0.99    ( ! [X2,X0,X1] : (v5_relat_1(X2,X1) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 3.47/0.99    inference(cnf_transformation,[],[f18])).
% 3.47/0.99  
% 3.47/0.99  fof(f2,axiom,(
% 3.47/0.99    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1))),
% 3.47/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.47/0.99  
% 3.47/0.99  fof(f40,plain,(
% 3.47/0.99    ( ! [X0,X1] : (v1_relat_1(k2_zfmisc_1(X0,X1))) )),
% 3.47/0.99    inference(cnf_transformation,[],[f2])).
% 3.47/0.99  
% 3.47/0.99  fof(f1,axiom,(
% 3.47/0.99    ! [X0] : (v1_relat_1(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => v1_relat_1(X1)))),
% 3.47/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.47/0.99  
% 3.47/0.99  fof(f15,plain,(
% 3.47/0.99    ! [X0] : (! [X1] : (v1_relat_1(X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) | ~v1_relat_1(X0))),
% 3.47/0.99    inference(ennf_transformation,[],[f1])).
% 3.47/0.99  
% 3.47/0.99  fof(f39,plain,(
% 3.47/0.99    ( ! [X0,X1] : (v1_relat_1(X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0)) | ~v1_relat_1(X0)) )),
% 3.47/0.99    inference(cnf_transformation,[],[f15])).
% 3.47/0.99  
% 3.47/0.99  fof(f62,plain,(
% 3.47/0.99    v1_funct_1(sK2)),
% 3.47/0.99    inference(cnf_transformation,[],[f38])).
% 3.47/0.99  
% 3.47/0.99  fof(f63,plain,(
% 3.47/0.99    v1_funct_2(sK2,sK0,sK0)),
% 3.47/0.99    inference(cnf_transformation,[],[f38])).
% 3.47/0.99  
% 3.47/0.99  fof(f65,plain,(
% 3.47/0.99    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))),
% 3.47/0.99    inference(cnf_transformation,[],[f38])).
% 3.47/0.99  
% 3.47/0.99  fof(f10,axiom,(
% 3.47/0.99    ! [X0,X1] : ((m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v3_funct_2(X1,X0,X0) & v1_funct_2(X1,X0,X0) & v1_funct_1(X1)) => k2_funct_2(X0,X1) = k2_funct_1(X1))),
% 3.47/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.47/0.99  
% 3.47/0.99  fof(f28,plain,(
% 3.47/0.99    ! [X0,X1] : (k2_funct_2(X0,X1) = k2_funct_1(X1) | (~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) | ~v3_funct_2(X1,X0,X0) | ~v1_funct_2(X1,X0,X0) | ~v1_funct_1(X1)))),
% 3.47/0.99    inference(ennf_transformation,[],[f10])).
% 3.47/0.99  
% 3.47/0.99  fof(f29,plain,(
% 3.47/0.99    ! [X0,X1] : (k2_funct_2(X0,X1) = k2_funct_1(X1) | ~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) | ~v3_funct_2(X1,X0,X0) | ~v1_funct_2(X1,X0,X0) | ~v1_funct_1(X1))),
% 3.47/0.99    inference(flattening,[],[f28])).
% 3.47/0.99  
% 3.47/0.99  fof(f56,plain,(
% 3.47/0.99    ( ! [X0,X1] : (k2_funct_2(X0,X1) = k2_funct_1(X1) | ~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) | ~v3_funct_2(X1,X0,X0) | ~v1_funct_2(X1,X0,X0) | ~v1_funct_1(X1)) )),
% 3.47/0.99    inference(cnf_transformation,[],[f29])).
% 3.47/0.99  
% 3.47/0.99  fof(f67,plain,(
% 3.47/0.99    ~r2_relset_1(sK0,sK0,sK2,k2_funct_2(sK0,sK1))),
% 3.47/0.99    inference(cnf_transformation,[],[f38])).
% 3.47/0.99  
% 3.47/0.99  fof(f6,axiom,(
% 3.47/0.99    ! [X0,X1,X2,X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) => (r2_relset_1(X0,X1,X2,X3) <=> X2 = X3))),
% 3.47/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.47/0.99  
% 3.47/0.99  fof(f20,plain,(
% 3.47/0.99    ! [X0,X1,X2,X3] : ((r2_relset_1(X0,X1,X2,X3) <=> X2 = X3) | (~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))))),
% 3.47/0.99    inference(ennf_transformation,[],[f6])).
% 3.47/0.99  
% 3.47/0.99  fof(f21,plain,(
% 3.47/0.99    ! [X0,X1,X2,X3] : ((r2_relset_1(X0,X1,X2,X3) <=> X2 = X3) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 3.47/0.99    inference(flattening,[],[f20])).
% 3.47/0.99  
% 3.47/0.99  fof(f34,plain,(
% 3.47/0.99    ! [X0,X1,X2,X3] : (((r2_relset_1(X0,X1,X2,X3) | X2 != X3) & (X2 = X3 | ~r2_relset_1(X0,X1,X2,X3))) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 3.47/0.99    inference(nnf_transformation,[],[f21])).
% 3.47/0.99  
% 3.47/0.99  fof(f46,plain,(
% 3.47/0.99    ( ! [X2,X0,X3,X1] : (r2_relset_1(X0,X1,X2,X3) | X2 != X3 | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 3.47/0.99    inference(cnf_transformation,[],[f34])).
% 3.47/0.99  
% 3.47/0.99  fof(f68,plain,(
% 3.47/0.99    ( ! [X0,X3,X1] : (r2_relset_1(X0,X1,X3,X3) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 3.47/0.99    inference(equality_resolution,[],[f46])).
% 3.47/0.99  
% 3.47/0.99  fof(f64,plain,(
% 3.47/0.99    v3_funct_2(sK2,sK0,sK0)),
% 3.47/0.99    inference(cnf_transformation,[],[f38])).
% 3.47/0.99  
% 3.47/0.99  fof(f3,axiom,(
% 3.47/0.99    ! [X0] : (v1_relat_1(X0) => ((k1_xboole_0 = k2_relat_1(X0) | k1_relat_1(X0) = k1_xboole_0) => k1_xboole_0 = X0))),
% 3.47/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.47/0.99  
% 3.47/0.99  fof(f16,plain,(
% 3.47/0.99    ! [X0] : ((k1_xboole_0 = X0 | (k1_xboole_0 != k2_relat_1(X0) & k1_relat_1(X0) != k1_xboole_0)) | ~v1_relat_1(X0))),
% 3.47/0.99    inference(ennf_transformation,[],[f3])).
% 3.47/0.99  
% 3.47/0.99  fof(f17,plain,(
% 3.47/0.99    ! [X0] : (k1_xboole_0 = X0 | (k1_xboole_0 != k2_relat_1(X0) & k1_relat_1(X0) != k1_xboole_0) | ~v1_relat_1(X0))),
% 3.47/0.99    inference(flattening,[],[f16])).
% 3.47/0.99  
% 3.47/0.99  fof(f42,plain,(
% 3.47/0.99    ( ! [X0] : (k1_xboole_0 = X0 | k1_xboole_0 != k2_relat_1(X0) | ~v1_relat_1(X0)) )),
% 3.47/0.99    inference(cnf_transformation,[],[f17])).
% 3.47/0.99  
% 3.47/0.99  fof(f9,axiom,(
% 3.47/0.99    ! [X0,X1] : ((m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v3_funct_2(X1,X0,X0) & v1_funct_2(X1,X0,X0) & v1_funct_1(X1)) => (m1_subset_1(k2_funct_2(X0,X1),k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v3_funct_2(k2_funct_2(X0,X1),X0,X0) & v1_funct_2(k2_funct_2(X0,X1),X0,X0) & v1_funct_1(k2_funct_2(X0,X1))))),
% 3.47/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.47/0.99  
% 3.47/0.99  fof(f26,plain,(
% 3.47/0.99    ! [X0,X1] : ((m1_subset_1(k2_funct_2(X0,X1),k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v3_funct_2(k2_funct_2(X0,X1),X0,X0) & v1_funct_2(k2_funct_2(X0,X1),X0,X0) & v1_funct_1(k2_funct_2(X0,X1))) | (~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) | ~v3_funct_2(X1,X0,X0) | ~v1_funct_2(X1,X0,X0) | ~v1_funct_1(X1)))),
% 3.47/0.99    inference(ennf_transformation,[],[f9])).
% 3.47/0.99  
% 3.47/0.99  fof(f27,plain,(
% 3.47/0.99    ! [X0,X1] : ((m1_subset_1(k2_funct_2(X0,X1),k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v3_funct_2(k2_funct_2(X0,X1),X0,X0) & v1_funct_2(k2_funct_2(X0,X1),X0,X0) & v1_funct_1(k2_funct_2(X0,X1))) | ~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) | ~v3_funct_2(X1,X0,X0) | ~v1_funct_2(X1,X0,X0) | ~v1_funct_1(X1))),
% 3.47/0.99    inference(flattening,[],[f26])).
% 3.47/0.99  
% 3.47/0.99  fof(f55,plain,(
% 3.47/0.99    ( ! [X0,X1] : (m1_subset_1(k2_funct_2(X0,X1),k1_zfmisc_1(k2_zfmisc_1(X0,X0))) | ~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) | ~v3_funct_2(X1,X0,X0) | ~v1_funct_2(X1,X0,X0) | ~v1_funct_1(X1)) )),
% 3.47/0.99    inference(cnf_transformation,[],[f27])).
% 3.47/0.99  
% 3.47/0.99  fof(f52,plain,(
% 3.47/0.99    ( ! [X0,X1] : (v1_funct_1(k2_funct_2(X0,X1)) | ~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) | ~v3_funct_2(X1,X0,X0) | ~v1_funct_2(X1,X0,X0) | ~v1_funct_1(X1)) )),
% 3.47/0.99    inference(cnf_transformation,[],[f27])).
% 3.47/0.99  
% 3.47/0.99  fof(f54,plain,(
% 3.47/0.99    ( ! [X0,X1] : (v3_funct_2(k2_funct_2(X0,X1),X0,X0) | ~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) | ~v3_funct_2(X1,X0,X0) | ~v1_funct_2(X1,X0,X0) | ~v1_funct_1(X1)) )),
% 3.47/0.99    inference(cnf_transformation,[],[f27])).
% 3.47/0.99  
% 3.47/0.99  cnf(c_20,negated_conjecture,
% 3.47/0.99      ( r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK0,sK0,sK0,sK1,sK2),k6_partfun1(sK0)) ),
% 3.47/0.99      inference(cnf_transformation,[],[f66]) ).
% 3.47/0.99  
% 3.47/0.99  cnf(c_907,negated_conjecture,
% 3.47/0.99      ( r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK0,sK0,sK0,sK1,sK2),k6_partfun1(sK0)) ),
% 3.47/0.99      inference(subtyping,[status(esa)],[c_20]) ).
% 3.47/0.99  
% 3.47/0.99  cnf(c_1411,plain,
% 3.47/0.99      ( r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK0,sK0,sK0,sK1,sK2),k6_partfun1(sK0)) = iProver_top ),
% 3.47/0.99      inference(predicate_to_equality,[status(thm)],[c_907]) ).
% 3.47/0.99  
% 3.47/0.99  cnf(c_25,negated_conjecture,
% 3.47/0.99      ( m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) ),
% 3.47/0.99      inference(cnf_transformation,[],[f61]) ).
% 3.47/0.99  
% 3.47/0.99  cnf(c_902,negated_conjecture,
% 3.47/0.99      ( m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) ),
% 3.47/0.99      inference(subtyping,[status(esa)],[c_25]) ).
% 3.47/0.99  
% 3.47/0.99  cnf(c_1416,plain,
% 3.47/0.99      ( m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) = iProver_top ),
% 3.47/0.99      inference(predicate_to_equality,[status(thm)],[c_902]) ).
% 3.47/0.99  
% 3.47/0.99  cnf(c_5,plain,
% 3.47/0.99      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.47/0.99      | k2_relset_1(X1,X2,X0) = k2_relat_1(X0) ),
% 3.47/0.99      inference(cnf_transformation,[],[f44]) ).
% 3.47/0.99  
% 3.47/0.99  cnf(c_918,plain,
% 3.47/0.99      ( ~ m1_subset_1(X0_50,k1_zfmisc_1(k2_zfmisc_1(X1_50,X2_50)))
% 3.47/0.99      | k2_relset_1(X1_50,X2_50,X0_50) = k2_relat_1(X0_50) ),
% 3.47/0.99      inference(subtyping,[status(esa)],[c_5]) ).
% 3.47/0.99  
% 3.47/0.99  cnf(c_1400,plain,
% 3.47/0.99      ( k2_relset_1(X0_50,X1_50,X2_50) = k2_relat_1(X2_50)
% 3.47/0.99      | m1_subset_1(X2_50,k1_zfmisc_1(k2_zfmisc_1(X0_50,X1_50))) != iProver_top ),
% 3.47/0.99      inference(predicate_to_equality,[status(thm)],[c_918]) ).
% 3.47/0.99  
% 3.47/0.99  cnf(c_2404,plain,
% 3.47/0.99      ( k2_relset_1(sK0,sK0,sK1) = k2_relat_1(sK1) ),
% 3.47/0.99      inference(superposition,[status(thm)],[c_1416,c_1400]) ).
% 3.47/0.99  
% 3.47/0.99  cnf(c_18,plain,
% 3.47/0.99      ( ~ r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0))
% 3.47/0.99      | ~ v1_funct_2(X3,X1,X0)
% 3.47/0.99      | ~ v1_funct_2(X2,X0,X1)
% 3.47/0.99      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
% 3.47/0.99      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
% 3.47/0.99      | ~ v2_funct_1(X2)
% 3.47/0.99      | ~ v1_funct_1(X2)
% 3.47/0.99      | ~ v1_funct_1(X3)
% 3.47/0.99      | k2_relset_1(X0,X1,X2) != X1
% 3.47/0.99      | k2_funct_1(X2) = X3
% 3.47/0.99      | k1_xboole_0 = X0
% 3.47/0.99      | k1_xboole_0 = X1 ),
% 3.47/0.99      inference(cnf_transformation,[],[f57]) ).
% 3.47/0.99  
% 3.47/0.99  cnf(c_909,plain,
% 3.47/0.99      ( ~ r2_relset_1(X0_50,X0_50,k1_partfun1(X0_50,X1_50,X1_50,X0_50,X2_50,X3_50),k6_partfun1(X0_50))
% 3.47/0.99      | ~ v1_funct_2(X3_50,X1_50,X0_50)
% 3.47/0.99      | ~ v1_funct_2(X2_50,X0_50,X1_50)
% 3.47/0.99      | ~ m1_subset_1(X2_50,k1_zfmisc_1(k2_zfmisc_1(X0_50,X1_50)))
% 3.47/0.99      | ~ m1_subset_1(X3_50,k1_zfmisc_1(k2_zfmisc_1(X1_50,X0_50)))
% 3.47/0.99      | ~ v2_funct_1(X2_50)
% 3.47/0.99      | ~ v1_funct_1(X2_50)
% 3.47/0.99      | ~ v1_funct_1(X3_50)
% 3.47/0.99      | k2_relset_1(X0_50,X1_50,X2_50) != X1_50
% 3.47/0.99      | k2_funct_1(X2_50) = X3_50
% 3.47/0.99      | k1_xboole_0 = X0_50
% 3.47/0.99      | k1_xboole_0 = X1_50 ),
% 3.47/0.99      inference(subtyping,[status(esa)],[c_18]) ).
% 3.47/0.99  
% 3.47/0.99  cnf(c_1409,plain,
% 3.47/0.99      ( k2_relset_1(X0_50,X1_50,X2_50) != X1_50
% 3.47/0.99      | k2_funct_1(X2_50) = X3_50
% 3.47/0.99      | k1_xboole_0 = X0_50
% 3.47/0.99      | k1_xboole_0 = X1_50
% 3.47/0.99      | r2_relset_1(X0_50,X0_50,k1_partfun1(X0_50,X1_50,X1_50,X0_50,X2_50,X3_50),k6_partfun1(X0_50)) != iProver_top
% 3.47/0.99      | v1_funct_2(X3_50,X1_50,X0_50) != iProver_top
% 3.47/0.99      | v1_funct_2(X2_50,X0_50,X1_50) != iProver_top
% 3.47/0.99      | m1_subset_1(X2_50,k1_zfmisc_1(k2_zfmisc_1(X0_50,X1_50))) != iProver_top
% 3.47/0.99      | m1_subset_1(X3_50,k1_zfmisc_1(k2_zfmisc_1(X1_50,X0_50))) != iProver_top
% 3.47/0.99      | v2_funct_1(X2_50) != iProver_top
% 3.47/0.99      | v1_funct_1(X2_50) != iProver_top
% 3.47/0.99      | v1_funct_1(X3_50) != iProver_top ),
% 3.47/0.99      inference(predicate_to_equality,[status(thm)],[c_909]) ).
% 3.47/0.99  
% 3.47/0.99  cnf(c_3950,plain,
% 3.47/0.99      ( k2_funct_1(sK1) = X0_50
% 3.47/0.99      | k2_relat_1(sK1) != sK0
% 3.47/0.99      | sK0 = k1_xboole_0
% 3.47/0.99      | r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK0,sK0,sK0,sK1,X0_50),k6_partfun1(sK0)) != iProver_top
% 3.47/0.99      | v1_funct_2(X0_50,sK0,sK0) != iProver_top
% 3.47/0.99      | v1_funct_2(sK1,sK0,sK0) != iProver_top
% 3.47/0.99      | m1_subset_1(X0_50,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) != iProver_top
% 3.47/0.99      | m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) != iProver_top
% 3.47/0.99      | v2_funct_1(sK1) != iProver_top
% 3.47/0.99      | v1_funct_1(X0_50) != iProver_top
% 3.47/0.99      | v1_funct_1(sK1) != iProver_top ),
% 3.47/0.99      inference(superposition,[status(thm)],[c_2404,c_1409]) ).
% 3.47/0.99  
% 3.47/0.99  cnf(c_28,negated_conjecture,
% 3.47/0.99      ( v1_funct_1(sK1) ),
% 3.47/0.99      inference(cnf_transformation,[],[f58]) ).
% 3.47/0.99  
% 3.47/0.99  cnf(c_29,plain,
% 3.47/0.99      ( v1_funct_1(sK1) = iProver_top ),
% 3.47/0.99      inference(predicate_to_equality,[status(thm)],[c_28]) ).
% 3.47/0.99  
% 3.47/0.99  cnf(c_27,negated_conjecture,
% 3.47/0.99      ( v1_funct_2(sK1,sK0,sK0) ),
% 3.47/0.99      inference(cnf_transformation,[],[f59]) ).
% 3.47/0.99  
% 3.47/0.99  cnf(c_30,plain,
% 3.47/0.99      ( v1_funct_2(sK1,sK0,sK0) = iProver_top ),
% 3.47/0.99      inference(predicate_to_equality,[status(thm)],[c_27]) ).
% 3.47/0.99  
% 3.47/0.99  cnf(c_26,negated_conjecture,
% 3.47/0.99      ( v3_funct_2(sK1,sK0,sK0) ),
% 3.47/0.99      inference(cnf_transformation,[],[f60]) ).
% 3.47/0.99  
% 3.47/0.99  cnf(c_31,plain,
% 3.47/0.99      ( v3_funct_2(sK1,sK0,sK0) = iProver_top ),
% 3.47/0.99      inference(predicate_to_equality,[status(thm)],[c_26]) ).
% 3.47/0.99  
% 3.47/0.99  cnf(c_32,plain,
% 3.47/0.99      ( m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) = iProver_top ),
% 3.47/0.99      inference(predicate_to_equality,[status(thm)],[c_25]) ).
% 3.47/0.99  
% 3.47/0.99  cnf(c_9,plain,
% 3.47/0.99      ( ~ v3_funct_2(X0,X1,X2)
% 3.47/0.99      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.47/0.99      | v2_funct_1(X0)
% 3.47/0.99      | ~ v1_funct_1(X0) ),
% 3.47/0.99      inference(cnf_transformation,[],[f48]) ).
% 3.47/0.99  
% 3.47/0.99  cnf(c_915,plain,
% 3.47/0.99      ( ~ v3_funct_2(X0_50,X1_50,X2_50)
% 3.47/0.99      | ~ m1_subset_1(X0_50,k1_zfmisc_1(k2_zfmisc_1(X1_50,X2_50)))
% 3.47/0.99      | v2_funct_1(X0_50)
% 3.47/0.99      | ~ v1_funct_1(X0_50) ),
% 3.47/0.99      inference(subtyping,[status(esa)],[c_9]) ).
% 3.47/0.99  
% 3.47/0.99  cnf(c_1661,plain,
% 3.47/0.99      ( ~ v3_funct_2(sK1,X0_50,X1_50)
% 3.47/0.99      | ~ m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(X0_50,X1_50)))
% 3.47/0.99      | v2_funct_1(sK1)
% 3.47/0.99      | ~ v1_funct_1(sK1) ),
% 3.47/0.99      inference(instantiation,[status(thm)],[c_915]) ).
% 3.47/0.99  
% 3.47/0.99  cnf(c_1662,plain,
% 3.47/0.99      ( v3_funct_2(sK1,X0_50,X1_50) != iProver_top
% 3.47/0.99      | m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(X0_50,X1_50))) != iProver_top
% 3.47/0.99      | v2_funct_1(sK1) = iProver_top
% 3.47/0.99      | v1_funct_1(sK1) != iProver_top ),
% 3.47/0.99      inference(predicate_to_equality,[status(thm)],[c_1661]) ).
% 3.47/0.99  
% 3.47/0.99  cnf(c_1664,plain,
% 3.47/0.99      ( v3_funct_2(sK1,sK0,sK0) != iProver_top
% 3.47/0.99      | m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) != iProver_top
% 3.47/0.99      | v2_funct_1(sK1) = iProver_top
% 3.47/0.99      | v1_funct_1(sK1) != iProver_top ),
% 3.47/0.99      inference(instantiation,[status(thm)],[c_1662]) ).
% 3.47/0.99  
% 3.47/0.99  cnf(c_8,plain,
% 3.47/0.99      ( ~ v3_funct_2(X0,X1,X2)
% 3.47/0.99      | v2_funct_2(X0,X2)
% 3.47/0.99      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.47/0.99      | ~ v1_funct_1(X0) ),
% 3.47/0.99      inference(cnf_transformation,[],[f49]) ).
% 3.47/0.99  
% 3.47/0.99  cnf(c_12,plain,
% 3.47/0.99      ( ~ v2_funct_2(X0,X1)
% 3.47/0.99      | ~ v5_relat_1(X0,X1)
% 3.47/0.99      | ~ v1_relat_1(X0)
% 3.47/0.99      | k2_relat_1(X0) = X1 ),
% 3.47/0.99      inference(cnf_transformation,[],[f50]) ).
% 3.47/0.99  
% 3.47/0.99  cnf(c_348,plain,
% 3.47/0.99      ( ~ v3_funct_2(X0,X1,X2)
% 3.47/0.99      | ~ v5_relat_1(X3,X4)
% 3.47/0.99      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.47/0.99      | ~ v1_funct_1(X0)
% 3.47/0.99      | ~ v1_relat_1(X3)
% 3.47/0.99      | X3 != X0
% 3.47/0.99      | X4 != X2
% 3.47/0.99      | k2_relat_1(X3) = X4 ),
% 3.47/0.99      inference(resolution_lifted,[status(thm)],[c_8,c_12]) ).
% 3.47/0.99  
% 3.47/0.99  cnf(c_349,plain,
% 3.47/0.99      ( ~ v3_funct_2(X0,X1,X2)
% 3.47/0.99      | ~ v5_relat_1(X0,X2)
% 3.47/0.99      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.47/0.99      | ~ v1_funct_1(X0)
% 3.47/0.99      | ~ v1_relat_1(X0)
% 3.47/0.99      | k2_relat_1(X0) = X2 ),
% 3.47/0.99      inference(unflattening,[status(thm)],[c_348]) ).
% 3.47/0.99  
% 3.47/0.99  cnf(c_4,plain,
% 3.47/0.99      ( v5_relat_1(X0,X1)
% 3.47/0.99      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) ),
% 3.47/0.99      inference(cnf_transformation,[],[f43]) ).
% 3.47/0.99  
% 3.47/0.99  cnf(c_365,plain,
% 3.47/0.99      ( ~ v3_funct_2(X0,X1,X2)
% 3.47/0.99      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.47/0.99      | ~ v1_funct_1(X0)
% 3.47/0.99      | ~ v1_relat_1(X0)
% 3.47/0.99      | k2_relat_1(X0) = X2 ),
% 3.47/0.99      inference(forward_subsumption_resolution,[status(thm)],[c_349,c_4]) ).
% 3.47/0.99  
% 3.47/0.99  cnf(c_898,plain,
% 3.47/0.99      ( ~ v3_funct_2(X0_50,X1_50,X2_50)
% 3.47/0.99      | ~ m1_subset_1(X0_50,k1_zfmisc_1(k2_zfmisc_1(X1_50,X2_50)))
% 3.47/0.99      | ~ v1_funct_1(X0_50)
% 3.47/0.99      | ~ v1_relat_1(X0_50)
% 3.47/0.99      | k2_relat_1(X0_50) = X2_50 ),
% 3.47/0.99      inference(subtyping,[status(esa)],[c_365]) ).
% 3.47/0.99  
% 3.47/0.99  cnf(c_1420,plain,
% 3.47/0.99      ( k2_relat_1(X0_50) = X1_50
% 3.47/0.99      | v3_funct_2(X0_50,X2_50,X1_50) != iProver_top
% 3.47/0.99      | m1_subset_1(X0_50,k1_zfmisc_1(k2_zfmisc_1(X2_50,X1_50))) != iProver_top
% 3.47/0.99      | v1_funct_1(X0_50) != iProver_top
% 3.47/0.99      | v1_relat_1(X0_50) != iProver_top ),
% 3.47/0.99      inference(predicate_to_equality,[status(thm)],[c_898]) ).
% 3.47/0.99  
% 3.47/0.99  cnf(c_4345,plain,
% 3.47/0.99      ( k2_relat_1(sK1) = sK0
% 3.47/0.99      | v3_funct_2(sK1,sK0,sK0) != iProver_top
% 3.47/0.99      | v1_funct_1(sK1) != iProver_top
% 3.47/0.99      | v1_relat_1(sK1) != iProver_top ),
% 3.47/0.99      inference(superposition,[status(thm)],[c_1416,c_1420]) ).
% 3.47/0.99  
% 3.47/0.99  cnf(c_1,plain,
% 3.47/0.99      ( v1_relat_1(k2_zfmisc_1(X0,X1)) ),
% 3.47/0.99      inference(cnf_transformation,[],[f40]) ).
% 3.47/0.99  
% 3.47/0.99  cnf(c_88,plain,
% 3.47/0.99      ( v1_relat_1(k2_zfmisc_1(X0,X1)) = iProver_top ),
% 3.47/0.99      inference(predicate_to_equality,[status(thm)],[c_1]) ).
% 3.47/0.99  
% 3.47/0.99  cnf(c_90,plain,
% 3.47/0.99      ( v1_relat_1(k2_zfmisc_1(sK0,sK0)) = iProver_top ),
% 3.47/0.99      inference(instantiation,[status(thm)],[c_88]) ).
% 3.47/0.99  
% 3.47/0.99  cnf(c_1685,plain,
% 3.47/0.99      ( ~ v3_funct_2(sK1,X0_50,X1_50)
% 3.47/0.99      | ~ m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(X0_50,X1_50)))
% 3.47/0.99      | ~ v1_funct_1(sK1)
% 3.47/0.99      | ~ v1_relat_1(sK1)
% 3.47/0.99      | k2_relat_1(sK1) = X1_50 ),
% 3.47/0.99      inference(instantiation,[status(thm)],[c_898]) ).
% 3.47/0.99  
% 3.47/0.99  cnf(c_1686,plain,
% 3.47/0.99      ( k2_relat_1(sK1) = X0_50
% 3.47/0.99      | v3_funct_2(sK1,X1_50,X0_50) != iProver_top
% 3.47/0.99      | m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(X1_50,X0_50))) != iProver_top
% 3.47/0.99      | v1_funct_1(sK1) != iProver_top
% 3.47/0.99      | v1_relat_1(sK1) != iProver_top ),
% 3.47/0.99      inference(predicate_to_equality,[status(thm)],[c_1685]) ).
% 3.47/0.99  
% 3.47/0.99  cnf(c_1688,plain,
% 3.47/0.99      ( k2_relat_1(sK1) = sK0
% 3.47/0.99      | v3_funct_2(sK1,sK0,sK0) != iProver_top
% 3.47/0.99      | m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) != iProver_top
% 3.47/0.99      | v1_funct_1(sK1) != iProver_top
% 3.47/0.99      | v1_relat_1(sK1) != iProver_top ),
% 3.47/0.99      inference(instantiation,[status(thm)],[c_1686]) ).
% 3.47/0.99  
% 3.47/0.99  cnf(c_0,plain,
% 3.47/0.99      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
% 3.47/0.99      | ~ v1_relat_1(X1)
% 3.47/0.99      | v1_relat_1(X0) ),
% 3.47/0.99      inference(cnf_transformation,[],[f39]) ).
% 3.47/0.99  
% 3.47/0.99  cnf(c_922,plain,
% 3.47/0.99      ( ~ m1_subset_1(X0_50,k1_zfmisc_1(X1_50))
% 3.47/0.99      | ~ v1_relat_1(X1_50)
% 3.47/0.99      | v1_relat_1(X0_50) ),
% 3.47/0.99      inference(subtyping,[status(esa)],[c_0]) ).
% 3.47/0.99  
% 3.47/0.99  cnf(c_1396,plain,
% 3.47/0.99      ( m1_subset_1(X0_50,k1_zfmisc_1(X1_50)) != iProver_top
% 3.47/0.99      | v1_relat_1(X1_50) != iProver_top
% 3.47/0.99      | v1_relat_1(X0_50) = iProver_top ),
% 3.47/0.99      inference(predicate_to_equality,[status(thm)],[c_922]) ).
% 3.47/0.99  
% 3.47/0.99  cnf(c_1852,plain,
% 3.47/0.99      ( v1_relat_1(k2_zfmisc_1(sK0,sK0)) != iProver_top
% 3.47/0.99      | v1_relat_1(sK1) = iProver_top ),
% 3.47/0.99      inference(superposition,[status(thm)],[c_1416,c_1396]) ).
% 3.47/0.99  
% 3.47/0.99  cnf(c_4556,plain,
% 3.47/0.99      ( k2_relat_1(sK1) = sK0 ),
% 3.47/0.99      inference(global_propositional_subsumption,
% 3.47/0.99                [status(thm)],
% 3.47/0.99                [c_4345,c_29,c_31,c_32,c_90,c_1688,c_1852]) ).
% 3.47/0.99  
% 3.47/0.99  cnf(c_4559,plain,
% 3.47/0.99      ( k2_relset_1(sK0,sK0,sK1) = sK0 ),
% 3.47/0.99      inference(demodulation,[status(thm)],[c_4556,c_2404]) ).
% 3.47/0.99  
% 3.47/0.99  cnf(c_4642,plain,
% 3.47/0.99      ( k2_funct_1(sK1) = X0_50
% 3.47/0.99      | sK0 = k1_xboole_0
% 3.47/0.99      | r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK0,sK0,sK0,sK1,X0_50),k6_partfun1(sK0)) != iProver_top
% 3.47/0.99      | v1_funct_2(X0_50,sK0,sK0) != iProver_top
% 3.47/0.99      | v1_funct_2(sK1,sK0,sK0) != iProver_top
% 3.47/0.99      | m1_subset_1(X0_50,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) != iProver_top
% 3.47/0.99      | m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) != iProver_top
% 3.47/0.99      | v2_funct_1(sK1) != iProver_top
% 3.47/0.99      | v1_funct_1(X0_50) != iProver_top
% 3.47/0.99      | v1_funct_1(sK1) != iProver_top ),
% 3.47/0.99      inference(superposition,[status(thm)],[c_4559,c_1409]) ).
% 3.47/0.99  
% 3.47/0.99  cnf(c_6575,plain,
% 3.47/0.99      ( v1_funct_1(X0_50) != iProver_top
% 3.47/0.99      | m1_subset_1(X0_50,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) != iProver_top
% 3.47/0.99      | k2_funct_1(sK1) = X0_50
% 3.47/0.99      | sK0 = k1_xboole_0
% 3.47/0.99      | r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK0,sK0,sK0,sK1,X0_50),k6_partfun1(sK0)) != iProver_top
% 3.47/0.99      | v1_funct_2(X0_50,sK0,sK0) != iProver_top ),
% 3.47/0.99      inference(global_propositional_subsumption,
% 3.47/0.99                [status(thm)],
% 3.47/0.99                [c_3950,c_29,c_30,c_31,c_32,c_1664,c_4642]) ).
% 3.47/0.99  
% 3.47/0.99  cnf(c_6576,plain,
% 3.47/0.99      ( k2_funct_1(sK1) = X0_50
% 3.47/0.99      | sK0 = k1_xboole_0
% 3.47/0.99      | r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK0,sK0,sK0,sK1,X0_50),k6_partfun1(sK0)) != iProver_top
% 3.47/0.99      | v1_funct_2(X0_50,sK0,sK0) != iProver_top
% 3.47/0.99      | m1_subset_1(X0_50,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) != iProver_top
% 3.47/0.99      | v1_funct_1(X0_50) != iProver_top ),
% 3.47/0.99      inference(renaming,[status(thm)],[c_6575]) ).
% 3.47/0.99  
% 3.47/0.99  cnf(c_6587,plain,
% 3.47/0.99      ( k2_funct_1(sK1) = sK2
% 3.47/0.99      | sK0 = k1_xboole_0
% 3.47/0.99      | v1_funct_2(sK2,sK0,sK0) != iProver_top
% 3.47/0.99      | m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) != iProver_top
% 3.47/0.99      | v1_funct_1(sK2) != iProver_top ),
% 3.47/0.99      inference(superposition,[status(thm)],[c_1411,c_6576]) ).
% 3.47/0.99  
% 3.47/0.99  cnf(c_24,negated_conjecture,
% 3.47/0.99      ( v1_funct_1(sK2) ),
% 3.47/0.99      inference(cnf_transformation,[],[f62]) ).
% 3.47/0.99  
% 3.47/0.99  cnf(c_23,negated_conjecture,
% 3.47/0.99      ( v1_funct_2(sK2,sK0,sK0) ),
% 3.47/0.99      inference(cnf_transformation,[],[f63]) ).
% 3.47/0.99  
% 3.47/0.99  cnf(c_21,negated_conjecture,
% 3.47/0.99      ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) ),
% 3.47/0.99      inference(cnf_transformation,[],[f65]) ).
% 3.47/0.99  
% 3.47/0.99  cnf(c_6588,plain,
% 3.47/0.99      ( ~ v1_funct_2(sK2,sK0,sK0)
% 3.47/0.99      | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
% 3.47/0.99      | ~ v1_funct_1(sK2)
% 3.47/0.99      | k2_funct_1(sK1) = sK2
% 3.47/0.99      | sK0 = k1_xboole_0 ),
% 3.47/0.99      inference(predicate_to_equality_rev,[status(thm)],[c_6587]) ).
% 3.47/0.99  
% 3.47/0.99  cnf(c_6623,plain,
% 3.47/0.99      ( sK0 = k1_xboole_0 | k2_funct_1(sK1) = sK2 ),
% 3.47/0.99      inference(global_propositional_subsumption,
% 3.47/0.99                [status(thm)],
% 3.47/0.99                [c_6587,c_33,c_34,c_36]) ).
% 3.47/0.99  
% 3.47/0.99  cnf(c_6624,plain,
% 3.47/0.99      ( k2_funct_1(sK1) = sK2 | sK0 = k1_xboole_0 ),
% 3.47/0.99      inference(renaming,[status(thm)],[c_6623]) ).
% 3.47/0.99  
% 3.47/0.99  cnf(c_17,plain,
% 3.47/0.99      ( ~ v1_funct_2(X0,X1,X1)
% 3.47/0.99      | ~ v3_funct_2(X0,X1,X1)
% 3.47/0.99      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X1)))
% 3.47/0.99      | ~ v1_funct_1(X0)
% 3.47/0.99      | k2_funct_2(X1,X0) = k2_funct_1(X0) ),
% 3.47/0.99      inference(cnf_transformation,[],[f56]) ).
% 3.47/0.99  
% 3.47/0.99  cnf(c_910,plain,
% 3.47/0.99      ( ~ v1_funct_2(X0_50,X1_50,X1_50)
% 3.47/0.99      | ~ v3_funct_2(X0_50,X1_50,X1_50)
% 3.47/0.99      | ~ m1_subset_1(X0_50,k1_zfmisc_1(k2_zfmisc_1(X1_50,X1_50)))
% 3.47/0.99      | ~ v1_funct_1(X0_50)
% 3.47/0.99      | k2_funct_2(X1_50,X0_50) = k2_funct_1(X0_50) ),
% 3.47/0.99      inference(subtyping,[status(esa)],[c_17]) ).
% 3.47/0.99  
% 3.47/0.99  cnf(c_1408,plain,
% 3.47/0.99      ( k2_funct_2(X0_50,X1_50) = k2_funct_1(X1_50)
% 3.47/0.99      | v1_funct_2(X1_50,X0_50,X0_50) != iProver_top
% 3.47/0.99      | v3_funct_2(X1_50,X0_50,X0_50) != iProver_top
% 3.47/0.99      | m1_subset_1(X1_50,k1_zfmisc_1(k2_zfmisc_1(X0_50,X0_50))) != iProver_top
% 3.47/0.99      | v1_funct_1(X1_50) != iProver_top ),
% 3.47/0.99      inference(predicate_to_equality,[status(thm)],[c_910]) ).
% 3.47/0.99  
% 3.47/0.99  cnf(c_2795,plain,
% 3.47/0.99      ( k2_funct_2(sK0,sK1) = k2_funct_1(sK1)
% 3.47/0.99      | v1_funct_2(sK1,sK0,sK0) != iProver_top
% 3.47/0.99      | v3_funct_2(sK1,sK0,sK0) != iProver_top
% 3.47/0.99      | v1_funct_1(sK1) != iProver_top ),
% 3.47/0.99      inference(superposition,[status(thm)],[c_1416,c_1408]) ).
% 3.47/0.99  
% 3.47/0.99  cnf(c_1725,plain,
% 3.47/0.99      ( ~ v1_funct_2(sK1,X0_50,X0_50)
% 3.47/0.99      | ~ v3_funct_2(sK1,X0_50,X0_50)
% 3.47/0.99      | ~ m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(X0_50,X0_50)))
% 3.47/0.99      | ~ v1_funct_1(sK1)
% 3.47/0.99      | k2_funct_2(X0_50,sK1) = k2_funct_1(sK1) ),
% 3.47/0.99      inference(instantiation,[status(thm)],[c_910]) ).
% 3.47/0.99  
% 3.47/0.99  cnf(c_1727,plain,
% 3.47/0.99      ( ~ v1_funct_2(sK1,sK0,sK0)
% 3.47/0.99      | ~ v3_funct_2(sK1,sK0,sK0)
% 3.47/0.99      | ~ m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
% 3.47/0.99      | ~ v1_funct_1(sK1)
% 3.47/0.99      | k2_funct_2(sK0,sK1) = k2_funct_1(sK1) ),
% 3.47/0.99      inference(instantiation,[status(thm)],[c_1725]) ).
% 3.47/0.99  
% 3.47/0.99  cnf(c_4059,plain,
% 3.47/0.99      ( k2_funct_2(sK0,sK1) = k2_funct_1(sK1) ),
% 3.47/0.99      inference(global_propositional_subsumption,
% 3.47/0.99                [status(thm)],
% 3.47/0.99                [c_2795,c_28,c_27,c_26,c_25,c_1727]) ).
% 3.47/0.99  
% 3.47/0.99  cnf(c_19,negated_conjecture,
% 3.47/0.99      ( ~ r2_relset_1(sK0,sK0,sK2,k2_funct_2(sK0,sK1)) ),
% 3.47/0.99      inference(cnf_transformation,[],[f67]) ).
% 3.47/0.99  
% 3.47/0.99  cnf(c_908,negated_conjecture,
% 3.47/0.99      ( ~ r2_relset_1(sK0,sK0,sK2,k2_funct_2(sK0,sK1)) ),
% 3.47/0.99      inference(subtyping,[status(esa)],[c_19]) ).
% 3.47/0.99  
% 3.47/0.99  cnf(c_1410,plain,
% 3.47/0.99      ( r2_relset_1(sK0,sK0,sK2,k2_funct_2(sK0,sK1)) != iProver_top ),
% 3.47/0.99      inference(predicate_to_equality,[status(thm)],[c_908]) ).
% 3.47/0.99  
% 3.47/0.99  cnf(c_4063,plain,
% 3.47/0.99      ( r2_relset_1(sK0,sK0,sK2,k2_funct_1(sK1)) != iProver_top ),
% 3.47/0.99      inference(demodulation,[status(thm)],[c_4059,c_1410]) ).
% 3.47/0.99  
% 3.47/0.99  cnf(c_6636,plain,
% 3.47/0.99      ( sK0 = k1_xboole_0 | r2_relset_1(sK0,sK0,sK2,sK2) != iProver_top ),
% 3.47/0.99      inference(superposition,[status(thm)],[c_6624,c_4063]) ).
% 3.47/0.99  
% 3.47/0.99  cnf(c_36,plain,
% 3.47/0.99      ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) = iProver_top ),
% 3.47/0.99      inference(predicate_to_equality,[status(thm)],[c_21]) ).
% 3.47/0.99  
% 3.47/0.99  cnf(c_6,plain,
% 3.47/0.99      ( r2_relset_1(X0,X1,X2,X2)
% 3.47/0.99      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ),
% 3.47/0.99      inference(cnf_transformation,[],[f68]) ).
% 3.47/0.99  
% 3.47/0.99  cnf(c_917,plain,
% 3.47/0.99      ( r2_relset_1(X0_50,X1_50,X2_50,X2_50)
% 3.47/0.99      | ~ m1_subset_1(X2_50,k1_zfmisc_1(k2_zfmisc_1(X0_50,X1_50))) ),
% 3.47/0.99      inference(subtyping,[status(esa)],[c_6]) ).
% 3.47/0.99  
% 3.47/0.99  cnf(c_1644,plain,
% 3.47/0.99      ( r2_relset_1(sK0,sK0,sK2,sK2)
% 3.47/0.99      | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) ),
% 3.47/0.99      inference(instantiation,[status(thm)],[c_917]) ).
% 3.47/0.99  
% 3.47/0.99  cnf(c_1645,plain,
% 3.47/0.99      ( r2_relset_1(sK0,sK0,sK2,sK2) = iProver_top
% 3.47/0.99      | m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) != iProver_top ),
% 3.47/0.99      inference(predicate_to_equality,[status(thm)],[c_1644]) ).
% 3.47/0.99  
% 3.47/0.99  cnf(c_6655,plain,
% 3.47/0.99      ( sK0 = k1_xboole_0 ),
% 3.47/0.99      inference(global_propositional_subsumption,
% 3.47/0.99                [status(thm)],
% 3.47/0.99                [c_6636,c_36,c_1645]) ).
% 3.47/0.99  
% 3.47/0.99  cnf(c_906,negated_conjecture,
% 3.47/0.99      ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) ),
% 3.47/0.99      inference(subtyping,[status(esa)],[c_21]) ).
% 3.47/0.99  
% 3.47/0.99  cnf(c_1412,plain,
% 3.47/0.99      ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) = iProver_top ),
% 3.47/0.99      inference(predicate_to_equality,[status(thm)],[c_906]) ).
% 3.47/0.99  
% 3.47/0.99  cnf(c_4344,plain,
% 3.47/0.99      ( k2_relat_1(sK2) = sK0
% 3.47/0.99      | v3_funct_2(sK2,sK0,sK0) != iProver_top
% 3.47/0.99      | v1_funct_1(sK2) != iProver_top
% 3.47/0.99      | v1_relat_1(sK2) != iProver_top ),
% 3.47/0.99      inference(superposition,[status(thm)],[c_1412,c_1420]) ).
% 3.47/0.99  
% 3.47/0.99  cnf(c_33,plain,
% 3.47/0.99      ( v1_funct_1(sK2) = iProver_top ),
% 3.47/0.99      inference(predicate_to_equality,[status(thm)],[c_24]) ).
% 3.47/0.99  
% 3.47/0.99  cnf(c_22,negated_conjecture,
% 3.47/0.99      ( v3_funct_2(sK2,sK0,sK0) ),
% 3.47/0.99      inference(cnf_transformation,[],[f64]) ).
% 3.47/0.99  
% 3.47/0.99  cnf(c_35,plain,
% 3.47/0.99      ( v3_funct_2(sK2,sK0,sK0) = iProver_top ),
% 3.47/0.99      inference(predicate_to_equality,[status(thm)],[c_22]) ).
% 3.47/0.99  
% 3.47/0.99  cnf(c_1680,plain,
% 3.47/0.99      ( ~ v3_funct_2(sK2,X0_50,X1_50)
% 3.47/0.99      | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X0_50,X1_50)))
% 3.47/0.99      | ~ v1_funct_1(sK2)
% 3.47/0.99      | ~ v1_relat_1(sK2)
% 3.47/0.99      | k2_relat_1(sK2) = X1_50 ),
% 3.47/0.99      inference(instantiation,[status(thm)],[c_898]) ).
% 3.47/0.99  
% 3.47/0.99  cnf(c_1681,plain,
% 3.47/0.99      ( k2_relat_1(sK2) = X0_50
% 3.47/0.99      | v3_funct_2(sK2,X1_50,X0_50) != iProver_top
% 3.47/0.99      | m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X1_50,X0_50))) != iProver_top
% 3.47/0.99      | v1_funct_1(sK2) != iProver_top
% 3.47/0.99      | v1_relat_1(sK2) != iProver_top ),
% 3.47/0.99      inference(predicate_to_equality,[status(thm)],[c_1680]) ).
% 3.47/0.99  
% 3.47/0.99  cnf(c_1683,plain,
% 3.47/0.99      ( k2_relat_1(sK2) = sK0
% 3.47/0.99      | v3_funct_2(sK2,sK0,sK0) != iProver_top
% 3.47/0.99      | m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) != iProver_top
% 3.47/0.99      | v1_funct_1(sK2) != iProver_top
% 3.47/0.99      | v1_relat_1(sK2) != iProver_top ),
% 3.47/0.99      inference(instantiation,[status(thm)],[c_1681]) ).
% 3.47/0.99  
% 3.47/0.99  cnf(c_1851,plain,
% 3.47/0.99      ( v1_relat_1(k2_zfmisc_1(sK0,sK0)) != iProver_top
% 3.47/0.99      | v1_relat_1(sK2) = iProver_top ),
% 3.47/0.99      inference(superposition,[status(thm)],[c_1412,c_1396]) ).
% 3.47/0.99  
% 3.47/0.99  cnf(c_4488,plain,
% 3.47/0.99      ( k2_relat_1(sK2) = sK0 ),
% 3.47/0.99      inference(global_propositional_subsumption,
% 3.47/0.99                [status(thm)],
% 3.47/0.99                [c_4344,c_33,c_35,c_36,c_90,c_1683,c_1851]) ).
% 3.47/0.99  
% 3.47/0.99  cnf(c_2,plain,
% 3.47/0.99      ( ~ v1_relat_1(X0)
% 3.47/0.99      | k2_relat_1(X0) != k1_xboole_0
% 3.47/0.99      | k1_xboole_0 = X0 ),
% 3.47/0.99      inference(cnf_transformation,[],[f42]) ).
% 3.47/0.99  
% 3.47/0.99  cnf(c_920,plain,
% 3.47/0.99      ( ~ v1_relat_1(X0_50)
% 3.47/0.99      | k2_relat_1(X0_50) != k1_xboole_0
% 3.47/0.99      | k1_xboole_0 = X0_50 ),
% 3.47/0.99      inference(subtyping,[status(esa)],[c_2]) ).
% 3.47/0.99  
% 3.47/0.99  cnf(c_1398,plain,
% 3.47/0.99      ( k2_relat_1(X0_50) != k1_xboole_0
% 3.47/0.99      | k1_xboole_0 = X0_50
% 3.47/0.99      | v1_relat_1(X0_50) != iProver_top ),
% 3.47/0.99      inference(predicate_to_equality,[status(thm)],[c_920]) ).
% 3.47/0.99  
% 3.47/0.99  cnf(c_4492,plain,
% 3.47/0.99      ( sK2 = k1_xboole_0
% 3.47/0.99      | sK0 != k1_xboole_0
% 3.47/0.99      | v1_relat_1(sK2) != iProver_top ),
% 3.47/0.99      inference(superposition,[status(thm)],[c_4488,c_1398]) ).
% 3.47/0.99  
% 3.47/0.99  cnf(c_4495,plain,
% 3.47/0.99      ( sK0 != k1_xboole_0 | sK2 = k1_xboole_0 ),
% 3.47/0.99      inference(global_propositional_subsumption,
% 3.47/0.99                [status(thm)],
% 3.47/0.99                [c_4492,c_90,c_1851]) ).
% 3.47/0.99  
% 3.47/0.99  cnf(c_4496,plain,
% 3.47/0.99      ( sK2 = k1_xboole_0 | sK0 != k1_xboole_0 ),
% 3.47/0.99      inference(renaming,[status(thm)],[c_4495]) ).
% 3.47/0.99  
% 3.47/0.99  cnf(c_6675,plain,
% 3.47/0.99      ( sK2 = k1_xboole_0 | k1_xboole_0 != k1_xboole_0 ),
% 3.47/0.99      inference(demodulation,[status(thm)],[c_6655,c_4496]) ).
% 3.47/0.99  
% 3.47/0.99  cnf(c_6751,plain,
% 3.47/0.99      ( sK2 = k1_xboole_0 ),
% 3.47/0.99      inference(equality_resolution_simp,[status(thm)],[c_6675]) ).
% 3.47/0.99  
% 3.47/0.99  cnf(c_2794,plain,
% 3.47/0.99      ( k2_funct_2(sK0,sK2) = k2_funct_1(sK2)
% 3.47/0.99      | v1_funct_2(sK2,sK0,sK0) != iProver_top
% 3.47/0.99      | v3_funct_2(sK2,sK0,sK0) != iProver_top
% 3.47/0.99      | v1_funct_1(sK2) != iProver_top ),
% 3.47/0.99      inference(superposition,[status(thm)],[c_1412,c_1408]) ).
% 3.47/0.99  
% 3.47/0.99  cnf(c_1720,plain,
% 3.47/0.99      ( ~ v1_funct_2(sK2,X0_50,X0_50)
% 3.47/0.99      | ~ v3_funct_2(sK2,X0_50,X0_50)
% 3.47/0.99      | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X0_50,X0_50)))
% 3.47/0.99      | ~ v1_funct_1(sK2)
% 3.47/0.99      | k2_funct_2(X0_50,sK2) = k2_funct_1(sK2) ),
% 3.47/0.99      inference(instantiation,[status(thm)],[c_910]) ).
% 3.47/0.99  
% 3.47/0.99  cnf(c_1722,plain,
% 3.47/0.99      ( ~ v1_funct_2(sK2,sK0,sK0)
% 3.47/0.99      | ~ v3_funct_2(sK2,sK0,sK0)
% 3.47/0.99      | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
% 3.47/0.99      | ~ v1_funct_1(sK2)
% 3.47/0.99      | k2_funct_2(sK0,sK2) = k2_funct_1(sK2) ),
% 3.47/0.99      inference(instantiation,[status(thm)],[c_1720]) ).
% 3.47/0.99  
% 3.47/0.99  cnf(c_4051,plain,
% 3.47/0.99      ( k2_funct_2(sK0,sK2) = k2_funct_1(sK2) ),
% 3.47/0.99      inference(global_propositional_subsumption,
% 3.47/0.99                [status(thm)],
% 3.47/0.99                [c_2794,c_24,c_23,c_22,c_21,c_1722]) ).
% 3.47/0.99  
% 3.47/0.99  cnf(c_13,plain,
% 3.47/0.99      ( ~ v1_funct_2(X0,X1,X1)
% 3.47/0.99      | ~ v3_funct_2(X0,X1,X1)
% 3.47/0.99      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X1)))
% 3.47/0.99      | m1_subset_1(k2_funct_2(X1,X0),k1_zfmisc_1(k2_zfmisc_1(X1,X1)))
% 3.47/0.99      | ~ v1_funct_1(X0) ),
% 3.47/0.99      inference(cnf_transformation,[],[f55]) ).
% 3.47/0.99  
% 3.47/0.99  cnf(c_914,plain,
% 3.47/0.99      ( ~ v1_funct_2(X0_50,X1_50,X1_50)
% 3.47/0.99      | ~ v3_funct_2(X0_50,X1_50,X1_50)
% 3.47/0.99      | ~ m1_subset_1(X0_50,k1_zfmisc_1(k2_zfmisc_1(X1_50,X1_50)))
% 3.47/0.99      | m1_subset_1(k2_funct_2(X1_50,X0_50),k1_zfmisc_1(k2_zfmisc_1(X1_50,X1_50)))
% 3.47/0.99      | ~ v1_funct_1(X0_50) ),
% 3.47/0.99      inference(subtyping,[status(esa)],[c_13]) ).
% 3.47/0.99  
% 3.47/0.99  cnf(c_1404,plain,
% 3.47/0.99      ( v1_funct_2(X0_50,X1_50,X1_50) != iProver_top
% 3.47/0.99      | v3_funct_2(X0_50,X1_50,X1_50) != iProver_top
% 3.47/0.99      | m1_subset_1(X0_50,k1_zfmisc_1(k2_zfmisc_1(X1_50,X1_50))) != iProver_top
% 3.47/0.99      | m1_subset_1(k2_funct_2(X1_50,X0_50),k1_zfmisc_1(k2_zfmisc_1(X1_50,X1_50))) = iProver_top
% 3.47/0.99      | v1_funct_1(X0_50) != iProver_top ),
% 3.47/0.99      inference(predicate_to_equality,[status(thm)],[c_914]) ).
% 3.47/0.99  
% 3.47/0.99  cnf(c_4056,plain,
% 3.47/0.99      ( v1_funct_2(sK2,sK0,sK0) != iProver_top
% 3.47/0.99      | v3_funct_2(sK2,sK0,sK0) != iProver_top
% 3.47/0.99      | m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) = iProver_top
% 3.47/0.99      | m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) != iProver_top
% 3.47/0.99      | v1_funct_1(sK2) != iProver_top ),
% 3.47/0.99      inference(superposition,[status(thm)],[c_4051,c_1404]) ).
% 3.47/0.99  
% 3.47/0.99  cnf(c_34,plain,
% 3.47/0.99      ( v1_funct_2(sK2,sK0,sK0) = iProver_top ),
% 3.47/0.99      inference(predicate_to_equality,[status(thm)],[c_23]) ).
% 3.47/0.99  
% 3.47/0.99  cnf(c_4790,plain,
% 3.47/0.99      ( m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) = iProver_top ),
% 3.47/0.99      inference(global_propositional_subsumption,
% 3.47/0.99                [status(thm)],
% 3.47/0.99                [c_4056,c_33,c_34,c_35,c_36]) ).
% 3.47/0.99  
% 3.47/0.99  cnf(c_4804,plain,
% 3.47/0.99      ( k2_relat_1(k2_funct_1(sK2)) = sK0
% 3.47/0.99      | v3_funct_2(k2_funct_1(sK2),sK0,sK0) != iProver_top
% 3.47/0.99      | v1_funct_1(k2_funct_1(sK2)) != iProver_top
% 3.47/0.99      | v1_relat_1(k2_funct_1(sK2)) != iProver_top ),
% 3.47/0.99      inference(superposition,[status(thm)],[c_4790,c_1420]) ).
% 3.47/0.99  
% 3.47/0.99  cnf(c_16,plain,
% 3.47/0.99      ( ~ v1_funct_2(X0,X1,X1)
% 3.47/0.99      | ~ v3_funct_2(X0,X1,X1)
% 3.47/0.99      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X1)))
% 3.47/0.99      | ~ v1_funct_1(X0)
% 3.47/0.99      | v1_funct_1(k2_funct_2(X1,X0)) ),
% 3.47/0.99      inference(cnf_transformation,[],[f52]) ).
% 3.47/0.99  
% 3.47/0.99  cnf(c_911,plain,
% 3.47/0.99      ( ~ v1_funct_2(X0_50,X1_50,X1_50)
% 3.47/0.99      | ~ v3_funct_2(X0_50,X1_50,X1_50)
% 3.47/0.99      | ~ m1_subset_1(X0_50,k1_zfmisc_1(k2_zfmisc_1(X1_50,X1_50)))
% 3.47/0.99      | ~ v1_funct_1(X0_50)
% 3.47/0.99      | v1_funct_1(k2_funct_2(X1_50,X0_50)) ),
% 3.47/0.99      inference(subtyping,[status(esa)],[c_16]) ).
% 3.47/0.99  
% 3.47/0.99  cnf(c_1407,plain,
% 3.47/0.99      ( v1_funct_2(X0_50,X1_50,X1_50) != iProver_top
% 3.47/0.99      | v3_funct_2(X0_50,X1_50,X1_50) != iProver_top
% 3.47/0.99      | m1_subset_1(X0_50,k1_zfmisc_1(k2_zfmisc_1(X1_50,X1_50))) != iProver_top
% 3.47/0.99      | v1_funct_1(X0_50) != iProver_top
% 3.47/0.99      | v1_funct_1(k2_funct_2(X1_50,X0_50)) = iProver_top ),
% 3.47/0.99      inference(predicate_to_equality,[status(thm)],[c_911]) ).
% 3.47/0.99  
% 3.47/0.99  cnf(c_2669,plain,
% 3.47/0.99      ( v1_funct_2(sK2,sK0,sK0) != iProver_top
% 3.47/0.99      | v3_funct_2(sK2,sK0,sK0) != iProver_top
% 3.47/0.99      | v1_funct_1(k2_funct_2(sK0,sK2)) = iProver_top
% 3.47/0.99      | v1_funct_1(sK2) != iProver_top ),
% 3.47/0.99      inference(superposition,[status(thm)],[c_1412,c_1407]) ).
% 3.47/0.99  
% 3.47/0.99  cnf(c_1690,plain,
% 3.47/0.99      ( ~ v1_funct_2(sK2,X0_50,X0_50)
% 3.47/0.99      | ~ v3_funct_2(sK2,X0_50,X0_50)
% 3.47/0.99      | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X0_50,X0_50)))
% 3.47/0.99      | v1_funct_1(k2_funct_2(X0_50,sK2))
% 3.47/0.99      | ~ v1_funct_1(sK2) ),
% 3.47/0.99      inference(instantiation,[status(thm)],[c_911]) ).
% 3.47/0.99  
% 3.47/0.99  cnf(c_1691,plain,
% 3.47/0.99      ( v1_funct_2(sK2,X0_50,X0_50) != iProver_top
% 3.47/0.99      | v3_funct_2(sK2,X0_50,X0_50) != iProver_top
% 3.47/0.99      | m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X0_50,X0_50))) != iProver_top
% 3.47/0.99      | v1_funct_1(k2_funct_2(X0_50,sK2)) = iProver_top
% 3.47/0.99      | v1_funct_1(sK2) != iProver_top ),
% 3.47/0.99      inference(predicate_to_equality,[status(thm)],[c_1690]) ).
% 3.47/0.99  
% 3.47/0.99  cnf(c_1693,plain,
% 3.47/0.99      ( v1_funct_2(sK2,sK0,sK0) != iProver_top
% 3.47/0.99      | v3_funct_2(sK2,sK0,sK0) != iProver_top
% 3.47/0.99      | m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) != iProver_top
% 3.47/0.99      | v1_funct_1(k2_funct_2(sK0,sK2)) = iProver_top
% 3.47/0.99      | v1_funct_1(sK2) != iProver_top ),
% 3.47/0.99      inference(instantiation,[status(thm)],[c_1691]) ).
% 3.47/0.99  
% 3.47/0.99  cnf(c_3610,plain,
% 3.47/0.99      ( v1_funct_1(k2_funct_2(sK0,sK2)) = iProver_top ),
% 3.47/0.99      inference(global_propositional_subsumption,
% 3.47/0.99                [status(thm)],
% 3.47/0.99                [c_2669,c_33,c_34,c_35,c_36,c_1693]) ).
% 3.47/0.99  
% 3.47/0.99  cnf(c_4054,plain,
% 3.47/0.99      ( v1_funct_1(k2_funct_1(sK2)) = iProver_top ),
% 3.47/0.99      inference(demodulation,[status(thm)],[c_4051,c_3610]) ).
% 3.47/0.99  
% 3.47/0.99  cnf(c_14,plain,
% 3.47/0.99      ( ~ v1_funct_2(X0,X1,X1)
% 3.47/0.99      | ~ v3_funct_2(X0,X1,X1)
% 3.47/0.99      | v3_funct_2(k2_funct_2(X1,X0),X1,X1)
% 3.47/0.99      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X1)))
% 3.47/0.99      | ~ v1_funct_1(X0) ),
% 3.47/0.99      inference(cnf_transformation,[],[f54]) ).
% 3.47/0.99  
% 3.47/0.99  cnf(c_913,plain,
% 3.47/0.99      ( ~ v1_funct_2(X0_50,X1_50,X1_50)
% 3.47/0.99      | ~ v3_funct_2(X0_50,X1_50,X1_50)
% 3.47/0.99      | v3_funct_2(k2_funct_2(X1_50,X0_50),X1_50,X1_50)
% 3.47/0.99      | ~ m1_subset_1(X0_50,k1_zfmisc_1(k2_zfmisc_1(X1_50,X1_50)))
% 3.47/0.99      | ~ v1_funct_1(X0_50) ),
% 3.47/0.99      inference(subtyping,[status(esa)],[c_14]) ).
% 3.47/0.99  
% 3.47/0.99  cnf(c_1405,plain,
% 3.47/0.99      ( v1_funct_2(X0_50,X1_50,X1_50) != iProver_top
% 3.47/0.99      | v3_funct_2(X0_50,X1_50,X1_50) != iProver_top
% 3.47/0.99      | v3_funct_2(k2_funct_2(X1_50,X0_50),X1_50,X1_50) = iProver_top
% 3.47/0.99      | m1_subset_1(X0_50,k1_zfmisc_1(k2_zfmisc_1(X1_50,X1_50))) != iProver_top
% 3.47/0.99      | v1_funct_1(X0_50) != iProver_top ),
% 3.47/0.99      inference(predicate_to_equality,[status(thm)],[c_913]) ).
% 3.47/0.99  
% 3.47/0.99  cnf(c_2820,plain,
% 3.47/0.99      ( v1_funct_2(sK2,sK0,sK0) != iProver_top
% 3.47/0.99      | v3_funct_2(k2_funct_2(sK0,sK2),sK0,sK0) = iProver_top
% 3.47/0.99      | v3_funct_2(sK2,sK0,sK0) != iProver_top
% 3.47/0.99      | v1_funct_1(sK2) != iProver_top ),
% 3.47/0.99      inference(superposition,[status(thm)],[c_1412,c_1405]) ).
% 3.47/0.99  
% 3.47/0.99  cnf(c_1744,plain,
% 3.47/0.99      ( ~ v1_funct_2(sK2,X0_50,X0_50)
% 3.47/0.99      | v3_funct_2(k2_funct_2(X0_50,sK2),X0_50,X0_50)
% 3.47/0.99      | ~ v3_funct_2(sK2,X0_50,X0_50)
% 3.47/0.99      | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X0_50,X0_50)))
% 3.47/0.99      | ~ v1_funct_1(sK2) ),
% 3.47/0.99      inference(instantiation,[status(thm)],[c_913]) ).
% 3.47/0.99  
% 3.47/0.99  cnf(c_1745,plain,
% 3.47/0.99      ( v1_funct_2(sK2,X0_50,X0_50) != iProver_top
% 3.47/0.99      | v3_funct_2(k2_funct_2(X0_50,sK2),X0_50,X0_50) = iProver_top
% 3.47/0.99      | v3_funct_2(sK2,X0_50,X0_50) != iProver_top
% 3.47/0.99      | m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X0_50,X0_50))) != iProver_top
% 3.47/0.99      | v1_funct_1(sK2) != iProver_top ),
% 3.47/0.99      inference(predicate_to_equality,[status(thm)],[c_1744]) ).
% 3.47/0.99  
% 3.47/0.99  cnf(c_1747,plain,
% 3.47/0.99      ( v1_funct_2(sK2,sK0,sK0) != iProver_top
% 3.47/0.99      | v3_funct_2(k2_funct_2(sK0,sK2),sK0,sK0) = iProver_top
% 3.47/0.99      | v3_funct_2(sK2,sK0,sK0) != iProver_top
% 3.47/0.99      | m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) != iProver_top
% 3.47/0.99      | v1_funct_1(sK2) != iProver_top ),
% 3.47/0.99      inference(instantiation,[status(thm)],[c_1745]) ).
% 3.47/0.99  
% 3.47/0.99  cnf(c_4108,plain,
% 3.47/0.99      ( v3_funct_2(k2_funct_2(sK0,sK2),sK0,sK0) = iProver_top ),
% 3.47/0.99      inference(global_propositional_subsumption,
% 3.47/0.99                [status(thm)],
% 3.47/0.99                [c_2820,c_33,c_34,c_35,c_36,c_1747]) ).
% 3.47/0.99  
% 3.47/0.99  cnf(c_4112,plain,
% 3.47/0.99      ( v3_funct_2(k2_funct_1(sK2),sK0,sK0) = iProver_top ),
% 3.47/0.99      inference(light_normalisation,[status(thm)],[c_4108,c_4051]) ).
% 3.47/0.99  
% 3.47/0.99  cnf(c_4801,plain,
% 3.47/0.99      ( v1_relat_1(k2_zfmisc_1(sK0,sK0)) != iProver_top
% 3.47/0.99      | v1_relat_1(k2_funct_1(sK2)) = iProver_top ),
% 3.47/0.99      inference(superposition,[status(thm)],[c_4790,c_1396]) ).
% 3.47/0.99  
% 3.47/0.99  cnf(c_7968,plain,
% 3.47/0.99      ( k2_relat_1(k2_funct_1(sK2)) = sK0 ),
% 3.47/0.99      inference(global_propositional_subsumption,
% 3.47/0.99                [status(thm)],
% 3.47/0.99                [c_4804,c_90,c_4054,c_4112,c_4801]) ).
% 3.47/0.99  
% 3.47/0.99  cnf(c_7970,plain,
% 3.47/0.99      ( k2_relat_1(k2_funct_1(sK2)) = k1_xboole_0 ),
% 3.47/0.99      inference(light_normalisation,[status(thm)],[c_7968,c_6655]) ).
% 3.47/0.99  
% 3.47/0.99  cnf(c_7972,plain,
% 3.47/0.99      ( k2_funct_1(sK2) = k1_xboole_0
% 3.47/0.99      | v1_relat_1(k2_funct_1(sK2)) != iProver_top ),
% 3.47/0.99      inference(superposition,[status(thm)],[c_7970,c_1398]) ).
% 3.47/0.99  
% 3.47/0.99  cnf(c_8102,plain,
% 3.47/0.99      ( k2_funct_1(sK2) = k1_xboole_0 ),
% 3.47/0.99      inference(global_propositional_subsumption,
% 3.47/0.99                [status(thm)],
% 3.47/0.99                [c_7972,c_90,c_4801]) ).
% 3.47/0.99  
% 3.47/0.99  cnf(c_9227,plain,
% 3.47/0.99      ( k2_funct_1(k1_xboole_0) = k1_xboole_0 ),
% 3.47/0.99      inference(demodulation,[status(thm)],[c_6751,c_8102]) ).
% 3.47/0.99  
% 3.47/0.99  cnf(c_4560,plain,
% 3.47/0.99      ( sK1 = k1_xboole_0
% 3.47/0.99      | sK0 != k1_xboole_0
% 3.47/0.99      | v1_relat_1(sK1) != iProver_top ),
% 3.47/0.99      inference(superposition,[status(thm)],[c_4556,c_1398]) ).
% 3.47/0.99  
% 3.47/0.99  cnf(c_4563,plain,
% 3.47/0.99      ( sK0 != k1_xboole_0 | sK1 = k1_xboole_0 ),
% 3.47/0.99      inference(global_propositional_subsumption,
% 3.47/0.99                [status(thm)],
% 3.47/0.99                [c_4560,c_90,c_1852]) ).
% 3.47/0.99  
% 3.47/0.99  cnf(c_4564,plain,
% 3.47/0.99      ( sK1 = k1_xboole_0 | sK0 != k1_xboole_0 ),
% 3.47/0.99      inference(renaming,[status(thm)],[c_4563]) ).
% 3.47/0.99  
% 3.47/0.99  cnf(c_6673,plain,
% 3.47/0.99      ( sK1 = k1_xboole_0 | k1_xboole_0 != k1_xboole_0 ),
% 3.47/0.99      inference(demodulation,[status(thm)],[c_6655,c_4564]) ).
% 3.47/0.99  
% 3.47/0.99  cnf(c_6803,plain,
% 3.47/0.99      ( sK1 = k1_xboole_0 ),
% 3.47/0.99      inference(equality_resolution_simp,[status(thm)],[c_6673]) ).
% 3.47/0.99  
% 3.47/0.99  cnf(c_6681,plain,
% 3.47/0.99      ( r2_relset_1(k1_xboole_0,k1_xboole_0,sK2,k2_funct_1(sK1)) != iProver_top ),
% 3.47/0.99      inference(demodulation,[status(thm)],[c_6655,c_4063]) ).
% 3.47/0.99  
% 3.47/0.99  cnf(c_6756,plain,
% 3.47/0.99      ( r2_relset_1(k1_xboole_0,k1_xboole_0,k1_xboole_0,k2_funct_1(sK1)) != iProver_top ),
% 3.47/0.99      inference(demodulation,[status(thm)],[c_6751,c_6681]) ).
% 3.47/0.99  
% 3.47/0.99  cnf(c_6806,plain,
% 3.47/0.99      ( r2_relset_1(k1_xboole_0,k1_xboole_0,k1_xboole_0,k2_funct_1(k1_xboole_0)) != iProver_top ),
% 3.47/0.99      inference(demodulation,[status(thm)],[c_6803,c_6756]) ).
% 3.47/0.99  
% 3.47/0.99  cnf(c_10960,plain,
% 3.47/0.99      ( r2_relset_1(k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0) != iProver_top ),
% 3.47/0.99      inference(demodulation,[status(thm)],[c_9227,c_6806]) ).
% 3.47/0.99  
% 3.47/0.99  cnf(c_1401,plain,
% 3.47/0.99      ( r2_relset_1(X0_50,X1_50,X2_50,X2_50) = iProver_top
% 3.47/0.99      | m1_subset_1(X2_50,k1_zfmisc_1(k2_zfmisc_1(X0_50,X1_50))) != iProver_top ),
% 3.47/0.99      inference(predicate_to_equality,[status(thm)],[c_917]) ).
% 3.47/0.99  
% 3.47/0.99  cnf(c_2465,plain,
% 3.47/0.99      ( r2_relset_1(sK0,sK0,sK2,sK2) = iProver_top ),
% 3.47/0.99      inference(superposition,[status(thm)],[c_1412,c_1401]) ).
% 3.47/0.99  
% 3.47/0.99  cnf(c_6689,plain,
% 3.47/0.99      ( r2_relset_1(k1_xboole_0,k1_xboole_0,sK2,sK2) = iProver_top ),
% 3.47/0.99      inference(demodulation,[status(thm)],[c_6655,c_2465]) ).
% 3.47/0.99  
% 3.47/0.99  cnf(c_6761,plain,
% 3.47/0.99      ( r2_relset_1(k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0) = iProver_top ),
% 3.47/0.99      inference(demodulation,[status(thm)],[c_6751,c_6689]) ).
% 3.47/0.99  
% 3.47/0.99  cnf(contradiction,plain,
% 3.47/0.99      ( $false ),
% 3.47/0.99      inference(minisat,[status(thm)],[c_10960,c_6761]) ).
% 3.47/0.99  
% 3.47/0.99  
% 3.47/0.99  % SZS output end CNFRefutation for theBenchmark.p
% 3.47/0.99  
% 3.47/0.99  ------                               Statistics
% 3.47/0.99  
% 3.47/0.99  ------ General
% 3.47/0.99  
% 3.47/0.99  abstr_ref_over_cycles:                  0
% 3.47/0.99  abstr_ref_under_cycles:                 0
% 3.47/0.99  gc_basic_clause_elim:                   0
% 3.47/0.99  forced_gc_time:                         0
% 3.47/0.99  parsing_time:                           0.009
% 3.47/0.99  unif_index_cands_time:                  0.
% 3.47/0.99  unif_index_add_time:                    0.
% 3.47/0.99  orderings_time:                         0.
% 3.47/0.99  out_proof_time:                         0.013
% 3.47/0.99  total_time:                             0.394
% 3.47/0.99  num_of_symbols:                         55
% 3.47/0.99  num_of_terms:                           16368
% 3.47/0.99  
% 3.47/0.99  ------ Preprocessing
% 3.47/0.99  
% 3.47/0.99  num_of_splits:                          0
% 3.47/0.99  num_of_split_atoms:                     0
% 3.47/0.99  num_of_reused_defs:                     0
% 3.47/0.99  num_eq_ax_congr_red:                    23
% 3.47/0.99  num_of_sem_filtered_clauses:            1
% 3.47/0.99  num_of_subtypes:                        2
% 3.47/0.99  monotx_restored_types:                  1
% 3.47/0.99  sat_num_of_epr_types:                   0
% 3.47/0.99  sat_num_of_non_cyclic_types:            0
% 3.47/0.99  sat_guarded_non_collapsed_types:        1
% 3.47/0.99  num_pure_diseq_elim:                    0
% 3.47/0.99  simp_replaced_by:                       0
% 3.47/0.99  res_preprocessed:                       132
% 3.47/0.99  prep_upred:                             0
% 3.47/0.99  prep_unflattend:                        38
% 3.47/0.99  smt_new_axioms:                         0
% 3.47/0.99  pred_elim_cands:                        7
% 3.47/0.99  pred_elim:                              2
% 3.47/0.99  pred_elim_cl:                           3
% 3.47/0.99  pred_elim_cycles:                       7
% 3.47/0.99  merged_defs:                            0
% 3.47/0.99  merged_defs_ncl:                        0
% 3.47/0.99  bin_hyper_res:                          0
% 3.47/0.99  prep_cycles:                            4
% 3.47/0.99  pred_elim_time:                         0.011
% 3.47/0.99  splitting_time:                         0.
% 3.47/0.99  sem_filter_time:                        0.
% 3.47/0.99  monotx_time:                            0.001
% 3.47/0.99  subtype_inf_time:                       0.001
% 3.47/0.99  
% 3.47/0.99  ------ Problem properties
% 3.47/0.99  
% 3.47/0.99  clauses:                                25
% 3.47/0.99  conjectures:                            10
% 3.47/0.99  epr:                                    6
% 3.47/0.99  horn:                                   24
% 3.47/0.99  ground:                                 10
% 3.47/0.99  unary:                                  11
% 3.47/0.99  binary:                                 2
% 3.47/0.99  lits:                                   74
% 3.47/0.99  lits_eq:                                12
% 3.47/0.99  fd_pure:                                0
% 3.47/0.99  fd_pseudo:                              0
% 3.47/0.99  fd_cond:                                2
% 3.47/0.99  fd_pseudo_cond:                         3
% 3.47/0.99  ac_symbols:                             0
% 3.47/0.99  
% 3.47/0.99  ------ Propositional Solver
% 3.47/0.99  
% 3.47/0.99  prop_solver_calls:                      28
% 3.47/0.99  prop_fast_solver_calls:                 1541
% 3.47/0.99  smt_solver_calls:                       0
% 3.47/0.99  smt_fast_solver_calls:                  0
% 3.47/0.99  prop_num_of_clauses:                    4557
% 3.47/0.99  prop_preprocess_simplified:             10342
% 3.47/0.99  prop_fo_subsumed:                       197
% 3.47/0.99  prop_solver_time:                       0.
% 3.47/0.99  smt_solver_time:                        0.
% 3.47/0.99  smt_fast_solver_time:                   0.
% 3.47/0.99  prop_fast_solver_time:                  0.
% 3.47/0.99  prop_unsat_core_time:                   0.
% 3.47/0.99  
% 3.47/0.99  ------ QBF
% 3.47/0.99  
% 3.47/0.99  qbf_q_res:                              0
% 3.47/0.99  qbf_num_tautologies:                    0
% 3.47/0.99  qbf_prep_cycles:                        0
% 3.47/0.99  
% 3.47/0.99  ------ BMC1
% 3.47/0.99  
% 3.47/0.99  bmc1_current_bound:                     -1
% 3.47/0.99  bmc1_last_solved_bound:                 -1
% 3.47/0.99  bmc1_unsat_core_size:                   -1
% 3.47/0.99  bmc1_unsat_core_parents_size:           -1
% 3.47/0.99  bmc1_merge_next_fun:                    0
% 3.47/0.99  bmc1_unsat_core_clauses_time:           0.
% 3.47/0.99  
% 3.47/0.99  ------ Instantiation
% 3.47/0.99  
% 3.47/0.99  inst_num_of_clauses:                    1299
% 3.47/0.99  inst_num_in_passive:                    78
% 3.47/0.99  inst_num_in_active:                     602
% 3.47/0.99  inst_num_in_unprocessed:                619
% 3.47/0.99  inst_num_of_loops:                      620
% 3.47/0.99  inst_num_of_learning_restarts:          0
% 3.47/0.99  inst_num_moves_active_passive:          16
% 3.47/0.99  inst_lit_activity:                      0
% 3.47/0.99  inst_lit_activity_moves:                0
% 3.47/0.99  inst_num_tautologies:                   0
% 3.47/0.99  inst_num_prop_implied:                  0
% 3.47/0.99  inst_num_existing_simplified:           0
% 3.47/0.99  inst_num_eq_res_simplified:             0
% 3.47/0.99  inst_num_child_elim:                    0
% 3.47/0.99  inst_num_of_dismatching_blockings:      398
% 3.47/0.99  inst_num_of_non_proper_insts:           1093
% 3.47/0.99  inst_num_of_duplicates:                 0
% 3.47/0.99  inst_inst_num_from_inst_to_res:         0
% 3.47/0.99  inst_dismatching_checking_time:         0.
% 3.47/0.99  
% 3.47/0.99  ------ Resolution
% 3.47/0.99  
% 3.47/0.99  res_num_of_clauses:                     0
% 3.47/0.99  res_num_in_passive:                     0
% 3.47/0.99  res_num_in_active:                      0
% 3.47/0.99  res_num_of_loops:                       136
% 3.47/0.99  res_forward_subset_subsumed:            37
% 3.47/0.99  res_backward_subset_subsumed:           2
% 3.47/0.99  res_forward_subsumed:                   0
% 3.47/0.99  res_backward_subsumed:                  0
% 3.47/0.99  res_forward_subsumption_resolution:     1
% 3.47/0.99  res_backward_subsumption_resolution:    0
% 3.47/0.99  res_clause_to_clause_subsumption:       455
% 3.47/0.99  res_orphan_elimination:                 0
% 3.47/0.99  res_tautology_del:                      82
% 3.47/0.99  res_num_eq_res_simplified:              0
% 3.47/0.99  res_num_sel_changes:                    0
% 3.47/0.99  res_moves_from_active_to_pass:          0
% 3.47/0.99  
% 3.47/0.99  ------ Superposition
% 3.47/0.99  
% 3.47/0.99  sup_time_total:                         0.
% 3.47/0.99  sup_time_generating:                    0.
% 3.47/0.99  sup_time_sim_full:                      0.
% 3.47/0.99  sup_time_sim_immed:                     0.
% 3.47/0.99  
% 3.47/0.99  sup_num_of_clauses:                     69
% 3.47/0.99  sup_num_in_active:                      39
% 3.47/0.99  sup_num_in_passive:                     30
% 3.47/0.99  sup_num_of_loops:                       123
% 3.47/0.99  sup_fw_superposition:                   66
% 3.47/0.99  sup_bw_superposition:                   93
% 3.47/0.99  sup_immediate_simplified:               76
% 3.47/0.99  sup_given_eliminated:                   0
% 3.47/0.99  comparisons_done:                       0
% 3.47/0.99  comparisons_avoided:                    3
% 3.47/0.99  
% 3.47/0.99  ------ Simplifications
% 3.47/0.99  
% 3.47/0.99  
% 3.47/0.99  sim_fw_subset_subsumed:                 22
% 3.47/0.99  sim_bw_subset_subsumed:                 9
% 3.47/0.99  sim_fw_subsumed:                        6
% 3.47/0.99  sim_bw_subsumed:                        0
% 3.47/0.99  sim_fw_subsumption_res:                 6
% 3.47/0.99  sim_bw_subsumption_res:                 0
% 3.47/0.99  sim_tautology_del:                      0
% 3.47/0.99  sim_eq_tautology_del:                   12
% 3.47/0.99  sim_eq_res_simp:                        2
% 3.47/0.99  sim_fw_demodulated:                     7
% 3.47/0.99  sim_bw_demodulated:                     103
% 3.47/0.99  sim_light_normalised:                   45
% 3.47/0.99  sim_joinable_taut:                      0
% 3.47/0.99  sim_joinable_simp:                      0
% 3.47/0.99  sim_ac_normalised:                      0
% 3.47/0.99  sim_smt_subsumption:                    0
% 3.47/0.99  
%------------------------------------------------------------------------------
